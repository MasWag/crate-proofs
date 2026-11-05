#!/usr/bin/env python3
"""Execute the report's CRLF observation against the locked release package."""
import json
from pathlib import Path
import shutil
import subprocess

root = Path(__file__).resolve().parents[1]
harness = root / '.work/crlf-reproduction'
(harness / 'src').mkdir(parents=True, exist_ok=True)
(harness / 'Cargo.toml').write_text(
    '[package]\nname = "unindent-crlf-reproduction"\nversion = "0.0.0"\n'
    'edition = "2021"\n[workspace]\n[dependencies]\n'
    'unindent = { path = ' + json.dumps(str(root)) + ' }\n'
)
shutil.copyfile(root / 'verification/reproductions/crlf.rs', harness / 'src/main.rs')
subprocess.run(['cargo', 'generate-lockfile', '--offline'], cwd=harness, check=True)
subprocess.run(['cargo', 'run', '--locked', '--offline'], cwd=harness, check=True)
