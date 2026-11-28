#!/usr/bin/env python3
"""Record Cargo configuration inputs for the managed version and extraction workspaces."""
import hashlib
import json
import os
from pathlib import Path
import sys


def config_files(cwd):
    # Cargo resolves a relative CARGO_HOME from the invocation directory.
    cargo_home = cwd / os.environ["CARGO_HOME"] if "CARGO_HOME" in os.environ else Path.home() / ".cargo"
    config_dirs = [parent / ".cargo" for parent in (cwd, *cwd.parents)] + [cargo_home]
    for directory in dict.fromkeys(config_dirs):
        for name in ("config", "config.toml"):
            path = directory / name
            yield {
                "path": str(path),
                "resolved": str(path.resolve()) if path.exists() else None,
                "sha256": hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else None,
            }


def main():
    stage, = sys.argv[1:]
    if stage not in ("before", "after"):
        raise SystemExit("Expected before or after")
    root = Path(__file__).resolve().parents[1]
    config = json.loads((root / "aeneas/profiles/default/verification.json").read_text())
    directories = {root, *((root / entry.get("cwd", ".")).resolve() for entry in config["extractions"])}
    records = [{"cwd": str(cwd), "files": list(config_files(cwd))} for cwd in sorted(directories)]
    run = Path(os.environ["AENEAS_RUN_DIR"])
    output = run / f"cargo-context-{stage}.json"
    data = json.dumps(records, indent=2) + "\n"
    output.write_text(data)
    if stage == "after" and (run / "cargo-context-before.json").read_text() != data:
        raise SystemExit("Cargo configuration changed during verification")


if __name__ == "__main__":
    main()
