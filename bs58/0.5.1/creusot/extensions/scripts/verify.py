#!/usr/bin/env python3
"""Fresh proof and complete goal audit for the bs58 extension workspace."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

EXT = Path(__file__).resolve().parent.parent
ROOT = EXT.parent
CRATE = EXT / 'crate'
TOOLS = ROOT / '.work/tools'
CHECKER = EXT / 'scripts/check-run.py'
REVISION = '318615be3b8bbc60d1f6d52469ba5c0bdebed4f1'

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--time', type=int, default=5, help='Why3find per-attempt seconds')
args = parser.parse_args()
out = ROOT / '.work/extensions'
out.mkdir(exist_ok=True, parents=True)
run = Path(tempfile.mkdtemp(prefix='formal-', dir=out))
env = os.environ.copy()
env.update(CARGO_TARGET_DIR=str(run / 'target'), TMPDIR=str(run / 'tmp'),
           XDG_CACHE_HOME=str(run / 'cache'), CARGO_NET_OFFLINE='true')
for name in ('tmp', 'cache'):
    (run / name).mkdir()
print(f'Fresh extension run: {run}', flush=True)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def output(command):
    return subprocess.check_output(command, env=env, text=True).strip()


def clean_tool():
    source = TOOLS / 'sources/creusot'
    assert output(['git', '-C', str(source), 'rev-parse', 'HEAD']) == REVISION
    assert output(['git', '-C', str(source), 'status', '--porcelain']) == ''
    pinned = json.loads((ROOT / 'verification/toolchain.json').read_text())
    for record in pinned['executables'].values():
        assert digest(Path(record['path'])) == record['sha256'], record['path']
    for path, expected in pinned['rustc_driver'].items():
        assert digest(Path(path)) == expected, path
    for name, expected in pinned['prelude'].items():
        path = Path(env['XDG_DATA_HOME']) / 'creusot/share/why3find' / name
        assert digest(path) == expected, str(path)
    assert digest(Path(env['WHY3CONFIG'])) == pinned['why3_configuration']['sha256']


def inputs():
    paths = [ROOT / 'AGENTS.md', ROOT / 'scripts/env.sh', TOOLS / 'env.sh',
             ROOT / 'verification/toolchain.json', ROOT / '../source.lock.json',
             CHECKER, CRATE / 'Cargo.toml', CRATE / 'Cargo.lock',
             EXT / 'targets.json', EXT / 'correspondence.md',
             ROOT / 'verification/extensions/specification.md',
             ROOT / 'verification/extensions/coverage.md',
             ROOT / 'verification/extensions/model-boundaries.md']
    paths += sorted((CRATE / 'src').rglob('*.rs'))
    paths += sorted((EXT / 'scripts').glob('*.py'))
    paths += sorted((EXT / 'scripts').glob('*.sh'))
    model = Path(env['XDG_DATA_HOME']) / 'creusot/share/why3find/packages/creusot'
    paths += sorted(p for p in model.rglob('*') if p.is_file())
    paths += [Path(env['WHY3CONFIG']), Path(env['XDG_DATA_HOME']) / 'creusot/why3find.json']
    for directory in [CRATE, *CRATE.parents]:
        paths += [directory / '.cargo' / n for n in ('config', 'config.toml')
                  if (directory / '.cargo' / n).is_file()]
        if (directory / 'why3find.json').is_file():
            paths.append(directory / 'why3find.json')
    paths += [Path(env['CARGO_HOME']) / n for n in ('config', 'config.toml')
              if (Path(env['CARGO_HOME']) / n).is_file()]
    compiler = Path(output(['rustup', 'which', 'rustc', '--toolchain', env['RUSTUP_TOOLCHAIN']]))
    paths.append(compiler)
    paths += sorted((compiler.parent.parent / 'lib').glob('librustc_driver-*.so'))
    paths.append(Path(env['XDG_DATA_HOME']) / 'creusot/toolchains' /
                 env['RUSTUP_TOOLCHAIN'] / 'bin/creusot-rustc')
    paths += [Path(shutil.which(n)) for n in ('cargo-creusot', 'why3', 'why3find', 'z3', 'cvc5')]
    records = {str(p): digest(p) for p in paths}
    for name, value in env.items():
        if name in {'RUSTFLAGS', 'CARGO_ENCODED_RUSTFLAGS', 'RUSTC', 'RUSTC_WRAPPER',
                    'RUSTC_WORKSPACE_WRAPPER', 'CARGO_BUILD_RUSTC', 'CARGO_BUILD_RUSTFLAGS',
                    'RUSTUP_TOOLCHAIN', 'CARGO_HOME', 'RUSTUP_HOME', 'CARGO_TARGET_DIR'} \
                or name.startswith('CARGO_PROFILE_'):
            records['env:' + name] = hashlib.sha256(value.encode()).hexdigest()
    return ''.join(f'{value}  {key}\n' for key, value in sorted(records.items()))


def execute(command, log, cwd=CRATE):
    with log.open('w') as stream:
        return subprocess.run(command, cwd=cwd, env=env, stdout=stream,
                              stderr=subprocess.STDOUT).returncode


clean_tool()
before = inputs()
(run / 'inputs-before.sha256').write_text(before)
commands = [['cargo', 'creusot', 'version'], ['rustc', '-vV'], ['why3', '--version'],
            ['why3find', '--version'], ['z3', '--version'], ['cvc5', '--version']]
with (run / 'versions.txt').open('w') as log:
    for command in commands:
        subprocess.run(command, env=env, check=True, stdout=log, stderr=subprocess.STDOUT)
command = ['cargo', 'creusot', '--only=coma', '--span-mode', 'absolute',
           '--output-dir', str(run / 'coma'), '--', '--locked', '--offline',
           '--target-dir', str(run / 'target')]
code = execute(command, run / 'compile.log')
(run / 'compile.exit').write_text(str(code) + '\n')
if code:
    clean_tool()
    (run / 'inputs-after.sha256').write_text(inputs())
    raise SystemExit(f'Translation failed ({code}); retained {run}')

targets = sorted((run / 'coma').rglob('*.coma'))
assert targets, 'Zero generated proof targets'
required = json.loads((EXT / 'targets.json').read_text())['required_targets']
relative = {str(p.relative_to(run / 'coma')) for p in targets}
assert required and len(required) == len(set(required)), 'Empty/duplicate required inventory'
assert set(required) == relative, (
    f'Target inventory mismatch: missing={set(required) - relative}; '
    f'unexpected={relative - set(required)}')
(run / 'generated-targets.txt').write_text(''.join(str(p) + '\n' for p in targets))
failed = False
with (run / 'target-exits.tsv').open('w') as exits:
    for target in targets:
        rel = target.relative_to(run / 'coma')
        log = run / 'prover-logs' / rel.with_suffix('.log')
        log.parent.mkdir(parents=True, exist_ok=True)
        proof_command = ['why3find', 'prove', '--no-cache', '-f', '--summary',
                         '--no-autodetect-provers', '-P', 'z3,cvc5', '-j', '2',
                         '--fast', '0.2', '--time', str(args.time), '-d', '4', '-H', '3',
                         '--preprocess', 'compute_specified', str(target)]
        status = execute(proof_command, log)
        exits.write(f'{target}\t{status}\n')
        exits.flush()
        failed |= status != 0
        print(f'{rel}: exit {status}', flush=True)
(run / 'prove.exit').write_text(str(int(failed)) + '\n')
clean_tool()
after = inputs()
(run / 'inputs-after.sha256').write_text(after)
assert before == after, f'Inputs changed during verification; retained {run}'
audit = subprocess.run(['python3', str(CHECKER), str(run)], env=env).returncode
inventory_path = run / 'goal-inventory.json'
try:
    inventory = json.loads(inventory_path.read_text())
except (OSError, ValueError) as error:
    summary = {'status': 'failed', 'run_directory': str(run),
               'compile_exit': code, 'prove_exit': int(failed), 'audit_exit': audit,
               'inputs_match': before == after,
               'audit_error': f'Goal inventory unavailable: {error}'}
    (run / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2), flush=True)
    raise SystemExit(1)
summary = {'status': 'passed' if not failed and audit == 0 else 'failed',
           'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
           'run_directory': str(run), 'compile_exit': code, 'prove_exit': int(failed),
           'audit_exit': audit, 'inputs_match': before == after,
           'input_fingerprint_sha256': digest(run / 'inputs-before.sha256'),
           'goal_inventory_sha256': digest(run / 'goal-inventory.json'),
           'generated_targets': inventory['generated_targets'],
           'root_goals': inventory['root_goals'],
           'computed_root_goals': inventory['computed_root_goals'],
           'solver_leaves': sum(t['proved_leaves'] for t in inventory['targets']),
           'required_targets': required, 'creusot_revision': REVISION}
(run / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps(summary, indent=2), flush=True)
raise SystemExit(0 if summary['status'] == 'passed' else 1)
