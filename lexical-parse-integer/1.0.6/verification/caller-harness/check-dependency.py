#!/usr/bin/env python3
"""Check the locked lexical-util archive and every unpacked source file."""
import hashlib
import os
from pathlib import Path, PurePosixPath
import tarfile
import tomllib

ROOT = Path(__file__).resolve().parents[2]
NAME = "lexical-util"
VERSION = "1.0.7"


def checksum(lock: Path) -> str:
    packages = tomllib.loads(lock.read_text())["package"]
    matches = [p for p in packages if p["name"] == NAME and p["version"] == VERSION]
    if len(matches) != 1 or matches[0].get("source") != "registry+https://github.com/rust-lang/crates.io-index":
        raise ValueError(f"expected one crates.io {NAME} {VERSION} in {lock}")
    return matches[0]["checksum"]


def main() -> None:
    expected = checksum(ROOT / "Cargo.lock")
    if checksum(ROOT / "verification/caller-harness/Cargo.lock") != expected:
        raise ValueError("caller and release dependency checksums differ")
    cargo_home = Path(os.environ.get("CARGO_HOME", ROOT / ".work/cargo-home"))
    archives = list((cargo_home / "registry/cache").glob(f"*/{NAME}-{VERSION}.crate"))
    if len(archives) != 1:
        raise ValueError(f"expected one cached {NAME} archive, got {len(archives)}")
    archive = archives[0]
    if hashlib.sha256(archive.read_bytes()).hexdigest() != expected:
        raise ValueError("cached archive does not match Cargo.lock checksum")
    sources = list((cargo_home / "registry/src").glob(f"*/{NAME}-{VERSION}"))
    if len(sources) != 1:
        raise ValueError(f"expected one unpacked {NAME} source, got {len(sources)}")
    source = sources[0]
    checked = 0
    with tarfile.open(archive, "r:gz") as bundle:
        for item in bundle:
            path = PurePosixPath(item.name)
            if path.parts[0] != f"{NAME}-{VERSION}" or ".." in path.parts:
                raise ValueError(f"unsafe archive member: {item.name}")
            if not item.isfile():
                continue
            relative = Path(*path.parts[1:])
            captured = bundle.extractfile(item)
            if captured is None or (source / relative).read_bytes() != captured.read():
                raise ValueError(f"unpacked source differs: {relative}")
            checked += 1
    print(f"checked {NAME} {VERSION}: archive SHA-256 {expected}; {checked} unpacked files identical")


if __name__ == "__main__":
    main()
