#!/usr/bin/env python3
"""Check that the proofs.rs publication package is derived from the managed default profile.

The publication package in this directory is what cargo-proofs records:

* ``release/`` is the crates.io jsonptr 0.8.2 tree. Its file inventory and hashes
  must equal ``../source.lock.json``.
* ``Cargo.toml`` equals ``../Cargo.toml`` except that ``readme`` and ``[lib].path``
  point into ``release/``. ``Cargo.lock`` equals ``../Cargo.lock`` byte for byte.
* ``proofs/`` is a standalone Lake package. ``Jsonptr.lean``, ``Specs.lean``,
  ``Proofs.lean``, ``DerivedSpecs.lean``, ``DerivedProofs.lean`` and
  ``lean-toolchain`` are byte-identical to the managed default profile (the
  generated model comes from ``Generated/aarch64-apple-darwin/Jsonptr.lean``).
  ``lake-manifest.json`` differs only in the package name. ``lakefile.toml``
  requires the official Aeneas Git revision instead of the managed local path.
  ``Publication.lean`` adds per-API projections of bundled default-profile theorems.
* ``proofs.toml`` maps only audited default-profile theorems or projections, uses
  the managed Aeneas revision, and never maps private, refuted or record theorems.

This script checks file identity and metadata only. It does not build Lean, audit
axioms or establish that a theorem states an adequate API contract.
"""
from pathlib import Path
import hashlib
import json
import re
import sys
import tomllib

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
PROFILE = ROOT / 'aeneas/profiles/default'
COPIED = {
    'Jsonptr.lean': 'proofs/Generated/aarch64-apple-darwin/Jsonptr.lean',
    'Specs.lean': 'proofs/Specs.lean',
    'Proofs.lean': 'proofs/Proofs.lean',
    'DerivedSpecs.lean': 'proofs/DerivedSpecs.lean',
    'DerivedProofs.lean': 'proofs/DerivedProofs.lean',
    'lean-toolchain': 'proofs/lean-toolchain',
}
PACKAGE_FILES = set(COPIED) | {'Publication.lean', 'lakefile.toml', 'lake-manifest.json', '.gitignore'}
EXCLUDED_SCOPES = {'private-model', 'refutation-or-record'}
errors = []
LOCAL_PREFIX = b'/' + b'Users/'


def check(condition, message):
    if not condition:
        errors.append(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def release_inventory():
    lock = json.loads((ROOT / 'source.lock.json').read_text())
    release = HERE / 'release'
    actual = {}
    for path in sorted(release.rglob('*')):
        check(not path.is_symlink(), f'symlink in release/: {path}')
        if path.is_file():
            actual[path.relative_to(release).as_posix()] = {
                'sha256': digest(path), 'executable': bool(path.stat().st_mode & 0o111)}
    check(actual == lock['files'], 'release/ differs from ../source.lock.json')


def cargo_files():
    check((HERE / 'Cargo.lock').read_bytes() == (ROOT / 'Cargo.lock').read_bytes(),
          'Cargo.lock differs from ../Cargo.lock')
    expected = (ROOT / 'Cargo.toml').read_text()
    expected = expected.replace('readme = ".work/source/README.md"', 'readme = "release/README.md"', 1)
    expected = expected.replace('path = ".work/source/src/lib.rs"', 'path = "release/src/lib.rs"', 1)
    check((HERE / 'Cargo.toml').read_text() == expected,
          'Cargo.toml differs from ../Cargo.toml beyond the release/ readme and library paths')
    manifest = tomllib.loads((HERE / 'Cargo.toml').read_text())
    check(manifest['lib']['path'] == 'release/src/lib.rs', 'library does not compile release/src/lib.rs')
    check('workspace' in manifest, 'publication manifest must be its own workspace root')


def lean_package(version):
    proofs = HERE / 'proofs'
    present = {p.name for p in proofs.iterdir() if p.name != '.lake'}
    check(present == PACKAGE_FILES, f'unexpected Lean package files: {sorted(present ^ PACKAGE_FILES)}')
    for name, managed in COPIED.items():
        check((proofs / name).read_bytes() == (PROFILE / managed).read_bytes(),
              f'proofs/{name} differs from the managed {managed}')
    published = json.loads((proofs / 'lake-manifest.json').read_text())
    managed = json.loads((PROFILE / 'proofs/lake-manifest.json').read_text())
    check(published.pop('name') == 'jsonptr_publication', 'unexpected Lake package name')
    managed.pop('name')
    check(published == managed, 'lake-manifest.json differs from the managed manifest beyond its name')
    aeneas = [p for p in published['packages'] if p['name'] == 'aeneas']
    check(len(aeneas) == 1 and aeneas[0]['type'] == 'git' and aeneas[0]['rev'] == version
          and aeneas[0]['subDir'] == 'backends/lean', 'Aeneas Lake dependency is not the pinned revision')
    lake = tomllib.loads((proofs / 'lakefile.toml').read_text())
    check(lake['name'] == 'jsonptr_publication', 'lakefile name differs from the manifest')
    require = lake['require']
    check(len(require) == 1 and require[0]['name'] == 'aeneas' and require[0]['rev'] == version
          and require[0]['git'] == {'url': 'https://github.com/AeneasVerif/aeneas', 'subDir': 'backends/lean'},
          'lakefile does not require the official pinned Aeneas revision')
    check(all('srcDir' not in lib for lib in lake['lean_lib']), 'publication package must use root module paths')
    for path in proofs.rglob('*'):
        check('.lake' in path.parts or path.suffix not in ('.olean', '.ilean'), f'compiled Lean artifact: {path}')


def mappings():
    config = tomllib.loads((HERE / 'proofs.toml').read_text())
    tool = config['tool']
    managed = tomllib.loads((PROFILE / 'proofs.toml').read_text())['tool']
    check(tool['name'] == 'aeneas' and tool['version'] == managed['version'], 'Aeneas version differs from the managed profile')
    check(tool.get('lean_dir') == 'proofs', 'lean_dir must be proofs')
    inventory = json.loads((PROFILE / 'theorems.json').read_text())
    scopes = {item['name']: item['scope'] for item in inventory['checked']}
    managed_mapped = {item['theorem'] for item in managed['proofs']}
    projections = set(re.findall(r'^theorem (\w+)', (HERE / 'proofs/Publication.lean').read_text(), re.M))
    theorem_names, apis = set(), set()
    for proof in tool['proofs']:
        name, module, api = proof['theorem'], proof['module'], proof['api']
        check(name not in theorem_names, f'theorem mapped twice: {name}')
        check(api not in apis, f'API mapped twice: {api}')
        theorem_names.add(name)
        apis.add(api)
        check(proof.get('precondition', '').strip() != '', f'missing precondition prose: {name}')
        check('validate_bytes' not in api, f'private API mapped: {api}')
        if module == 'Publication':
            check(name.startswith('JsonptrPublication.') and name.split('.', 1)[1] in projections,
                  f'unknown publication projection: {name}')
        else:
            check(scopes.get(name) not in EXCLUDED_SCOPES and name in scopes,
                  f'{name} is not a public default-profile theorem')
            check(name in managed_mapped, f'{name} is not mapped by the managed default profile')
            expected_module = next(i['module'] for i in inventory['checked'] if i['name'] == name)
            check(module == expected_module, f'{name} module differs from the inventory')
    complete = [p for p in tool['proofs'] if p['api'] == 'ParseError::complete_offset']
    check(len(complete) == 1 and 'usize' in complete[0]['precondition'],
          'complete_offset must keep its usize precondition')
    return tool['version']


def no_local_paths():
    for path in HERE.rglob('*'):
        if path.is_file() and '.lake' not in path.parts and 'release' not in path.relative_to(HERE).parts:
            check(LOCAL_PREFIX not in path.read_bytes(), f'absolute local path in {path.relative_to(HERE)}')


def main():
    release_inventory()
    cargo_files()
    version = mappings()
    lean_package(version)
    no_local_paths()
    if errors:
        for error in errors:
            print('error:', error, file=sys.stderr)
        return 1
    print('publication package derivation and mapping metadata: ok')
    return 0


if __name__ == '__main__':
    sys.exit(main())
