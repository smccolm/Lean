"""Replay unmodified AFE2.py as numerical research, never as proof evidence."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import importlib.metadata
import json
import subprocess
import sys

paper = Path(__file__).resolve().parent.parent
source = paper / 'Sources/DhimanKadiriQuesadaHerrera-v1-source/anc/AFE2.py'
relative = source.relative_to(paper / 'Sources').as_posix()


def main():
    if len(sys.argv) != 1:
        raise ValueError('Usage: python Tools/reproduce_author_code.py')
    expected = [line.split('  ', 1)[0] for line in (paper / 'Sources/SHA256SUMS.txt').read_text().splitlines()
                if line.endswith('  ' + relative)]
    actual_hash = hashlib.sha256(source.read_bytes()).hexdigest()
    if expected != [actual_hash]:
        raise ValueError('The archived AFE2 script does not match its unique source pin.')
    versions = {name: importlib.metadata.version(name) for name in ['numpy', 'scipy']}
    timestamp = datetime.now(timezone.utc)
    output = paper / 'logs' / ('author-code-' + timestamp.strftime('%Y%m%d-%H%M%S-%f'))
    output.mkdir(parents=True)
    result = subprocess.run([sys.executable, '-X', 'utf8', str(source)], cwd=output,
                            capture_output=True, timeout=60, check=False)
    (output / 'stdout.txt').write_bytes(result.stdout)
    (output / 'stderr.txt').write_bytes(result.stderr)
    receipt = dict(observed_on=timestamp.date().isoformat(),executed_utc=timestamp.isoformat(),
                   status='REPLAY ONLY - NOT A PROOF',python=sys.version,versions=versions,
                   source_sha256=actual_hash,exit_code=result.returncode,
                   stdout_sha256=hashlib.sha256(result.stdout).hexdigest(),
                   stderr_sha256=hashlib.sha256(result.stderr).hexdigest(),
                   output_directory=output.relative_to(paper).as_posix(),
                   sage_replay='not run; SageMath 9.5 unavailable during setup')
    (output / 'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    print(result.stdout.decode('utf-8').replace('\r\n', '\n'),end='')
    if result.stderr:
        print(result.stderr.decode('utf-8').replace('\r\n', '\n'),end='',file=sys.stderr)
    print('REPLAY ONLY - NOT A PROOF. Receipt:',output / 'receipt.json')
    return result.returncode


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (ValueError, importlib.metadata.PackageNotFoundError, subprocess.TimeoutExpired) as exc:
        print('REPLAY FAILED:',exc,file=sys.stderr)
        sys.exit(1)
