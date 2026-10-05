"""Verify the inactive research scaffold. Never executes Lean or author code."""
from pathlib import Path
import hashlib
import json
import re
import sys
import tarfile
from urllib.parse import unquote

PAPER = Path(__file__).resolve().parent.parent
PREFIX = 'Dhiman-Kadiri-Quesada-Herrera '


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path):
    return json.loads(path.read_text(encoding='utf-8'))


def validate(paper=PAPER):
    root = paper.parent.parent
    config = read_json(paper / 'Tools/scaffold.json')
    require(config['mode'] == 'planning-only', 'This verifier accepts only planning-only mode.')
    require(config['proofGatesComplete'] == 0 and config['proofGatesTotal'] == 20,
            'Planning mode requires 0/20 proof gates.')
    require(not config['productionModules'] and not config['verificationModules'],
            'No Lean modules are authorized in scaffold mode.')
    actual = sorted(p.relative_to(paper).as_posix() for p in paper.rglob('*')
                    if p.is_file() and not {'logs', '__pycache__'}.intersection(p.relative_to(paper).parts))
    expected = config['requiredFiles']
    require(len(expected) == len(set(expected)), 'Duplicate required scaffold file.')
    require(set(actual) == set(expected),
            f'Inventory mismatch: missing={sorted(set(expected)-set(actual))}; extra={sorted(set(actual)-set(expected))}')
    for relative in actual:
        p = Path(relative)
        require(p.suffix != '.lean' and p.name not in
                {'lakefile.toml', 'lakefile.lean', 'lake-manifest.json', 'lean-toolchain'},
                f'Lean conversion has started unexpectedly: {relative}')
    extension_files = [p.relative_to(paper / 'Extension').as_posix()
                       for p in (paper / 'Extension').rglob('*') if p.is_file()]
    require(extension_files == ['README.md'], 'Extension must contain only its planning README.')
    for name, expected_hash in config['parentFileHashes'].items():
        raw = (root / name).read_bytes()
        require(digest(root / name) == expected_hash or
                hashlib.sha256(raw.replace(b'\r\n', b'\n')).hexdigest() == config['parentTextLfHashes'][name],
                f'Foundation configuration drift: {name}')
    manifest = read_json(root / 'lake-manifest.json')
    pins = {p['name']: p['rev'] for p in manifest['packages']}
    require((root / 'lean-toolchain').read_text().strip() == config['foundation']['toolchain'],
            'Unexpected foundation toolchain.')
    for name in ['mathlib', 'PrimeNumberTheoremAnd']:
        require(pins[name] == config['foundation'][name], f'Foundation package pin mismatch: {name}')
    require(digest(paper / 'push_to_github.bat') == config['ownerSyncSha256'], 'Owner BAT bytes changed.')
    require(hashlib.sha256((paper / config['ownerSyncSource']).read_bytes().replace(b'\r\n', b'\n')).hexdigest()
            == config['ownerSyncSourceLfSha256'],
            'Node-63 reference BAT changed; review source provenance before changing the frozen copy.')
    print(f'INVENTORY/PINS PASS: {len(actual)} retained files; exact node-63 BAT; unchanged parent pins; no Lean package.')

    gates = read_json(paper / 'Tools/proof_gates.json')
    require([g['id'] for g in gates] == [f'DKKH-{i:02}' for i in range(1, 21)], 'Gate IDs/order drift.')
    checklist = (paper / (PREFIX + 'Checklist.md')).read_text(encoding='utf-8')
    architecture = (paper / (PREFIX + 'Architecture.md')).read_text(encoding='utf-8')
    for i, gate in enumerate(gates, 1):
        require(gate['status'] == 'OPEN', f'Planning gate is not OPEN: {gate["id"]}')
        rows = re.findall(r'^\| ' + gate['id'] + r' \| (OPEN|DONE) \|', checklist, re.M)
        require(rows == ['OPEN'], f'Checklist gate status mismatch: {gate["id"]}')
        nodes = re.findall(r'G' + f'{i:02}' + r'\["' + gate['id'] + r'[^\n]*?<br/>OPEN"\]', architecture)
        require(len(nodes) == 1, f'Architecture gate status mismatch: {gate["id"]}')
    for name in ['README.md'] + [PREFIX + role + '.md' for role in
                               ['Checklist', 'Architecture', 'Research Agenda', 'Reproduction Manifest']]:
        require('0/20' in (paper / name).read_text(encoding='utf-8'), f'Missing proof-count disclosure: {name}')
    prompt = (paper / (PREFIX + 'Goal Prompt.md')).read_text(encoding='utf-8')
    for marker in ['GOAL INACTIVE', 'DO NOT START LEAN CONVERSION', 'run_lake_build.bat',
                   'run_dhiman_kadiri_quesada_herrera_build.bat', 'push_to_github.bat', 'Recovery-record']:
        require(marker in prompt, f'Goal prompt lost required boundary: {marker}')
    print('STATUS PASS: inactive goal; twenty OPEN gates agree across JSON, checklist and architecture.')

    index = read_json(paper / 'Tools/source_labels.json')
    source = paper / index['source']
    require(digest(source) == index['sha256'], 'Source label index hash mismatch.')
    tex = source.read_text(encoding='utf-8')
    labels = []
    for match in re.finditer(r'\\label\{([^}]+)\}', tex):
        lead = tex[tex.rfind('\n', 0, match.start()) + 1:match.start()]
        if '%' not in lead:
            labels.append({'label': match[1], 'line': tex.count('\n', 0, match.start()) + 1})
    require(labels == index['labels'], 'Source label index content mismatch.')
    for label in ['thm-VDC', 'thm-AFE1', 'thm-AFE2', 'cor-VDC', 'Explicit_B_estimate',
                  'cor:all_t', 'cor-AFE2', 'cor-k-AFE2', 'cor-thmVDC-partII']:
        require(any(x['label'] == label for x in labels), f'Missing main source anchor: {label}')
    extracted = paper / 'Sources/DhimanKadiriQuesadaHerrera-v1-source'
    archive = paper / 'Sources/dhiman-kadiri-quesada-herrera-2609.00537v1.tar'
    with tarfile.open(archive) as tar:
        members = [m for m in tar.getmembers() if m.isfile()]
        require(sorted(m.name for m in members) == sorted(p.relative_to(extracted).as_posix()
                for p in extracted.rglob('*') if p.is_file()), 'Extracted archive member inventory mismatch.')
        for member in members:
            require(not Path(member.name).is_absolute() and '..' not in Path(member.name).parts,
                    'Unsafe original archive member name.')
            require((extracted / member.name).read_bytes() == tar.extractfile(member).read(),
                    f'Extracted source differs from original archive: {member.name}')
    pdfs = list((paper / 'Sources').glob('*.pdf'))
    for pdf in pdfs:
        require(pdf.read_bytes().startswith(b'%PDF-'), f'Not a PDF: {pdf.name}')
    print(f'SOURCE STRUCTURE PASS: {len(labels)} label anchors; {len(members)} byte-identical archive members; {len(pdfs)} PDFs.')

    links = 0
    for relative in actual:
        if not relative.endswith('.md'):
            continue
        path = paper / relative
        text = path.read_text(encoding='utf-8')
        for match in re.finditer(r'\[[^\]\r\n]*\]\(([^)\r\n]+)\)', text):
            target = match[1].strip('<>')
            if re.match(r'^(https?://|mailto:|#)', target):
                continue
            target = unquote(target.split('#', 1)[0])
            require((path.parent / target).exists(), f'Broken local link in {relative}: {target}')
            links += 1
    print(f'LINKS PASS: {links} existing local Markdown targets.')
    return len(actual)


if __name__ == '__main__':
    try:
        require(len(sys.argv) == 1, 'Usage: python Tools/verify_scaffold.py')
        validate()
    except Exception as exc:
        print(f'SCAFFOLD VALIDATION FAILED: {exc}', file=sys.stderr)
        sys.exit(1)
