#!/usr/bin/env python3
"""Fingerprint and package real Creusot/Why3find evidence for this workspace."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[2]
sys.path.insert(0, str(REPO / 'scripts'))
from aeneas_management import source


def require(test, message):
    if not test:
        raise ValueError(message)


def digest(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def write(path, data):
    Path(path).write_text(json.dumps(data, indent=2, sort_keys=True) + '\n')


def output(argv):
    return subprocess.check_output(argv, text=True).strip()


def add_tree(paths, root):
    root = Path(root)
    if not root.is_dir():
        return
    for directory, names, files in os.walk(root):
        names[:] = [n for n in names if n not in
                    {'.git', 'target', '.lake', 'verif', '.why3find', '__pycache__'}]
        for name in files:
            if name != '.cargo-ok':
                p = Path(directory) / name
                if p.is_file():
                    paths.add(p.resolve())


def inputs():
    paths = set()
    raw = subprocess.check_output(['git', '-C', str(REPO), 'ls-files', '--cached',
                                   '--others', '--exclude-standard', '-z', str(ROOT)])
    for name in raw.split(b'\0'):
        if not name:
            continue
        p = REPO / os.fsdecode(name)
        relative = p.relative_to(ROOT)
        if ('.work' in relative.parts or relative == Path('verification/results.md')
                or relative.is_relative_to('verification/evidence')):
            continue
        if p.is_file():
            paths.add(p.resolve())
    for relative in ['AGENTS.md', '.agents/skills/creusot-verification/SKILL.md',
                     '.agents/skills/creusot-proof-composition/SKILL.md',
                     'scripts/audit-proof-evidence.py', 'scripts/aeneas_management/source.py']:
        paths.add((REPO / relative).resolve())
    paths.add((ROOT.parent / 'AGENTS.md').resolve())
    paths.add((ROOT.parent / 'source.lock.json').resolve())
    release = ROOT.parent / '.work/source'
    lock = read(ROOT.parent / 'source.lock.json')
    source.check(release, lock)
    add_tree(paths, release)
    metadata = json.loads(output(['cargo', 'metadata', '--locked', '--offline',
                                  '--format-version', '1', '--manifest-path',
                                  str(ROOT / 'Cargo.toml')]))
    for package in metadata['packages']:
        if Path(package['manifest_path']).parent.resolve() != ROOT:
            add_tree(paths, Path(package['manifest_path']).parent)
    data_home = Path(os.environ['XDG_DATA_HOME'])
    add_tree(paths, data_home / 'creusot/share/why3find/packages/creusot')
    why3_data = Path(output(['why3', '--print-datadir']))
    require(why3_data.is_dir(), 'Missing actual Why3 data directory')
    add_tree(paths, why3_data)
    paths.add(Path('/home/lab8/mwaga/proof.rs/toolchain/creusot-env/env.sh'))
    why3_config = Path(os.environ['WHY3CONFIG'])
    require(why3_config.is_file(), 'Missing selected Why3 configuration')
    paths.add(why3_config.resolve())
    for p in [Path(os.environ['CARGO_HOME']) / 'config.toml',
              Path.home() / '.cargo/config.toml',
              Path(os.environ['XDG_CONFIG_HOME']) / 'why3find.json']:
        if p.is_file():
            paths.add(p.resolve())
    return paths, metadata


def tool_inputs():
    tools = {}
    for name in ['cargo', 'rustup', 'cargo-creusot', 'why3find', 'why3', 'z3', 'cvc5', 'alt-ergo']:
        p = shutil.which(name)
        require(p is not None, 'Missing tool: ' + name)
        p = Path(p).resolve()
        tools[name] = {'path': str(p), 'sha256': digest(p)}
    for role, extra in [('native', []), ('extraction', ['--toolchain', 'nightly-2026-06-22'])]:
        for name in ['rustc', 'cargo']:
            p = Path(output(['rustup', 'which', *extra, name])).resolve()
            tools[role + '-' + name] = {'path': str(p), 'sha256': digest(p)}
        compiler = Path(tools[role + '-rustc']['path'])
        for p in (compiler.parent.parent / 'lib').glob('librustc_driver*'):
            if p.is_file():
                tools[role + '-' + p.name] = {'path': str(p), 'sha256': digest(p)}
    p = Path(os.environ['XDG_DATA_HOME']) / 'creusot/toolchains/nightly-2026-06-22/bin/creusot-rustc'
    require(p.is_file(), 'Missing pinned Creusot compiler wrapper')
    tools['creusot-rustc'] = {'path': str(p.resolve()), 'sha256': digest(p)}
    p = Path(output(['why3', '--print-libdir'])) / 'why3server'
    require(p.is_file(), 'Missing actual Why3 solver server')
    tools['why3server'] = {'path': str(p.resolve()), 'sha256': digest(p)}
    return tools


def snapshot(path):
    paths, metadata = inputs()
    tools = tool_inputs()
    hashes = {str(p.relative_to(ROOT) if p.is_relative_to(ROOT) else p): digest(p)
              for p in sorted(paths)}
    for t in tools.values():
        hashes[t['path']] = t['sha256']
    data = {'inputs_sha256': hashes, 'tools_sha256': tools,
            'input_executable': {str(p): bool(p.stat().st_mode & 0o111) for p in paths},
            'resolved_packages': [{'name': p['name'], 'version': p['version'],
                                   'source': p['source'], 'manifest_path': p['manifest_path']}
                                  for p in metadata['packages']]}
    write(path, data)
    return data


def inventory():
    value = read(ROOT / 'verification/target-inventory.json')
    require(bool(value['selected']), 'The selected target inventory must be nonempty')
    require(not value.get('expected_open', {}), 'Final acceptance cannot contain expected-open targets')
    return value


def generated(run):
    return {p.relative_to(run / 'coma/verif/unindent_rlib').as_posix().removesuffix('.coma'): p
            for p in (run / 'coma/verif/unindent_rlib').rglob('*.coma')}


def selected(run):
    inv = inventory()
    files = generated(run)
    require(set(files) == set(inv['selected']) | set(inv['excluded_generated']),
            'Generated target inventory differs from the reviewed selection')
    for required in inv['required_body_targets']:
        require(required in inv['selected'], 'Missing required core body target: ' + required)
    for name in sorted(inv['selected']):
        print(files[name])


def closed(tree):
    if not isinstance(tree, dict) or not tree:
        return False
    if 'prover' in tree:
        return isinstance(tree['prover'], str) and bool(tree['prover'].strip())
    if 'tactic' in tree:
        return bool(tree['tactic']) and bool(tree.get('children')) and all(map(closed, tree['children']))
    return all(isinstance(v, list) and bool(v) and all(map(closed, v)) for v in tree.values())


def package(run):
    before = read(run / 'inputs-before.json')
    after = snapshot(run / 'inputs-after.json')
    require(before == after, 'Proof inputs, dependency sources, modes or tools changed during the run')
    require((run / 'prove.exit').read_text().strip() == '0', 'Why3find exited unsuccessfully')
    require((run / 'native.exit').read_text().strip() == '0', 'Native checks exited unsuccessfully')
    inv = inventory()
    files = generated(run)
    require(set(files) == set(inv['selected']) | set(inv['excluded_generated']),
            'Unclassified or missing generated Coma targets')
    bundle = run / 'bundle'
    bundle.mkdir()
    sessions = {}
    for name, contract in inv['selected'].items():
        p = files[name]
        proof = p.parent / p.stem / 'proof.json'
        require(proof.is_file(), 'Missing fresh proof session: ' + name)
        groups = read(proof).get('proofs')
        require(isinstance(groups, dict) and bool(groups), 'Empty proof session: ' + name)
        goals = {m + '.' + g: t for m, group in groups.items() for g, t in group.items()}
        require(bool(goals) and all(closed(t) for t in goals.values()), 'Open/empty target: ' + name)
        d = bundle / name
        d.mkdir(parents=True)
        shutil.copyfile(p, d / 'target.coma')
        shutil.copyfile(proof, d / 'proof.json')
        sessions[name] = {'goals': len(goals), 'goal_inventory': sorted(goals),
                          'open_goals': [], 'contract': contract,
                          'coma_sha256': digest(d / 'target.coma'),
                          'proof_json_sha256': digest(d / 'proof.json')}
    for name in ['inputs-before.json', 'inputs-after.json', 'versions.txt', 'compile.log',
                 'native.log', 'native.exit', 'prove.log', 'prove.exit']:
        shutil.copyfile(run / name, bundle / name)
    record = {'cache': False, 'identity': 'unindent 0.2.4 verification adaptation; source.lock.json pins release',
              'scope': 'Only the exact selected contracts; source-position semantics and UTF-8 under explicit std models',
              'inputs_sha256': before['inputs_sha256'], 'tools_sha256': before['tools_sha256'],
              'input_executable': before['input_executable'],
              'resolved_packages': before['resolved_packages'], 'targets': sessions,
              'expected_open': {}, 'excluded_generated': inv['excluded_generated'],
              'generated_target_count': len(files),
              'total_session_goals': sum(s['goals'] for s in sessions.values()),
              'application_trusted_assumptions': [],
              'assumption_ledger': 'verification/assumptions.md',
              'source_equivalence': 'Not formally established; see source map and separate finite native comparisons',
              'logs_sha256': {n: digest(bundle / n) for n in ['compile.log', 'native.log', 'prove.log', 'versions.txt']}}
    write(bundle / 'manifest.json', record)
    print('Packaged', len(sessions), 'positive targets and', record['total_session_goals'], 'root goals')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('operation', choices=['snapshot', 'selected', 'package'])
    parser.add_argument('path', type=Path)
    args = parser.parse_args()
    if args.operation == 'snapshot': snapshot(args.path)
    elif args.operation == 'selected': selected(args.path.resolve())
    else: package(args.path.resolve())


if __name__ == '__main__':
    main()
