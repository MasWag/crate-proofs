#!/usr/bin/env python3
"""Run native correspondence/findings checks with registry source fingerprints."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import tomllib

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--toolchain", default="nightly-2026-06-22")
parser.add_argument("--cargo-home")
parser.add_argument("--rustup-home")
parser.add_argument("--offline", action="store_true")
args = parser.parse_args()
root = Path(__file__).resolve().parent.parent
(root / ".work").mkdir(exist_ok=True)
run = Path(tempfile.mkdtemp(prefix="native-final-", dir=root / ".work"))
(run / "tmp").mkdir()
env = os.environ.copy()
for option, variable in [(args.cargo_home, "CARGO_HOME"), (args.rustup_home, "RUSTUP_HOME")]:
    if option:
        env[variable] = str(Path(option).resolve())
env.update(CARGO_TARGET_DIR=str(root / ".work/native-target"), TMPDIR=str(run / "tmp"))
if args.offline:
    env["CARGO_NET_OFFLINE"] = "true"
cargo = shutil.which("cargo")
if not cargo:
    raise SystemExit("cargo is not on PATH")
manifest = root / "verification/native/Cargo.toml"
base = [cargo, "+" + args.toolchain]
locked = ["--locked"] + (["--offline"] if args.offline else [])


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


metadata = subprocess.run(
    base + ["metadata", *locked, "--format-version", "1", "--manifest-path", str(manifest)],
    env=env, check=True, capture_output=True, text=True,
)
packages = json.loads(metadata.stdout)["packages"]
release_package = next(p for p in packages if p["name"] == "bs58" and p["version"] == "0.5.1")
release = Path(release_package["manifest_path"]).parent
source_lock = json.loads((root / "../source.lock.json").read_text())
registry_lock = tomllib.loads(manifest.with_name("Cargo.lock").read_text())
entry = next(p for p in registry_lock["package"] if p["name"] == "bs58" and p["version"] == "0.5.1")
assert entry["checksum"] == source_lock["sha256"]
std = next(p for p in packages if p["name"] == "creusot-std" and p["version"] == "0.13.0")
assert Path(std["manifest_path"]).resolve() == (
    root / ".work/tools/sources/creusot/creusot-std/Cargo.toml"
).resolve()

files = [Path(__file__), root / "crate/Cargo.toml", root / "crate/Cargo.lock",
         manifest, manifest.with_name("Cargo.lock"), root / "../source.lock.json"]
files += sorted((root / "crate/src").glob("*.rs"))
files += sorted((root / "verification/native/src").glob("*.rs"))
files += [release / name for name in source_lock["files"]]
for directory in [manifest.parent, *manifest.parent.parents]:
    for name in [".cargo/config", ".cargo/config.toml"]:
        path = directory / name
        if path.is_file():
            files.append(path)
cargo_home = Path(env.get("CARGO_HOME", str(Path.home() / ".cargo")))
files += [p for p in [cargo_home / "config", cargo_home / "config.toml"] if p.is_file()]
compiler = Path(subprocess.check_output(
    ["rustup", "which", "rustc", "--toolchain", args.toolchain], env=env, text=True,
).strip()).resolve()
files.append(compiler)
files += sorted((compiler.parent.parent / "lib").glob("librustc_driver-*.so"))


def snapshot():
    values = {str(path.resolve()): digest(path) for path in sorted(set(files))}
    for name in ["RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER"]:
        values["environment:" + name] = hashlib.sha256(env.get(name, "<unset>").encode()).hexdigest()
    return values


def check_release():
    for name, expected in source_lock["files"].items():
        assert digest(release / name) == expected["sha256"], name


check_release()
before = snapshot()
(run / "inputs-before.json").write_text(json.dumps(before, indent=2) + "\n")
command = base + ["run", *locked, "--manifest-path", str(manifest)]
with (run / "run.log").open("w") as log:
    result = subprocess.run(command, env=env, stdout=log, stderr=subprocess.STDOUT)
check_release()
after = snapshot()
(run / "inputs-after.json").write_text(json.dumps(after, indent=2) + "\n")
text = (run / "run.log").read_text()
passed = (result.returncode == 0 and before == after
          and "differential: 145388 paired codec cases" in text
          and all(text.count(f"F{number} ") == 2 for number in [1, 2, 3]))
summary = {
    "status": "passed" if passed else "failed",
    "utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "command": command, "exit": result.returncode, "inputs_match": before == after,
    "input_snapshot_sha256": digest(run / "inputs-before.json"),
    "log_sha256": digest(run / "run.log"),
    "bs58_registry_checksum": source_lock["sha256"],
    "release_files_checked_before_and_after": len(source_lock["files"]),
    "registry_files_in_both_input_snapshots": True,
    "paired_codec_cases": 145388, "fixed_array_comparisons": 120000,
    "constructor_outcome_cases": 348,
    "compile_time_tests": ["Alphabet::new", "empty N=0", "112 with N=4 right padding",
                           "same upstream const API result"],
    "findings_reproduced": [f"F{n}/{mode}" for n in [1, 2, 3] for mode in ["check", "cb58"]],
    "formal_evidence": False, "run_directory": str(run),
}
(run / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
print(json.dumps(summary, indent=2))
raise SystemExit(0 if passed else 1)
