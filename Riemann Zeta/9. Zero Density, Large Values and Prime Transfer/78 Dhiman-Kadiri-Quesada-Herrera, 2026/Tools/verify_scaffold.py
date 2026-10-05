"""Validate active project inventory, coverage, pins and status before Lean runs."""
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
    require(config['mode'] in {'active-development', 'project-complete'}, 'Unexpected project mode.')
    require(config['proofGatesTotal'] == 20, 'The twenty acceptance gates are fixed.')
    require(config['verificationModules'] == ['SemanticRegression', 'Audit'],
            'Both semantic regression and exhaustive transitive audit are mandatory.')
    actual = sorted(p.relative_to(paper).as_posix() for p in paper.rglob('*')
                    if p.is_file() and not {'logs', '__pycache__', '.lake'}.intersection(p.relative_to(paper).parts))
    expected = config['requiredFiles']
    require(len(expected) == len(set(expected)), 'Duplicate required scaffold file.')
    require(set(actual) == set(expected),
            f'Inventory mismatch: missing={sorted(set(expected)-set(actual))}; extra={sorted(set(actual)-set(expected))}')
    module_root = 'DhimanKadiriQuesadaHerrera2026'
    modules = config['productionModules'] + config['verificationModules']
    classified = [f'Extension/{module_root}.lean'] + [
        f'Extension/{module_root}/{m.replace(".", "/")}.lean' for m in modules]
    require(len(classified) == len(set(classified)), 'Duplicate Lean classification.')
    require(set(classified) == {p for p in actual if p.endswith('.lean')},
            'Unclassified or missing Lean module.')
    pending, visited = [module_root], set()
    while pending:
        module = pending.pop()
        if module in visited:
            continue
        visited.add(module)
        body = (paper / 'Extension' / (module.replace('.', '/') + '.lean')).read_text(encoding='utf-8')
        pending.extend(re.findall(r'^import (' + module_root + r'(?:\.[A-Za-z0-9_]+)+)\s*$', body, re.M))
    require(visited == {module_root} | {module_root + '.' + m for m in config['productionModules']},
            'Root imports do not cover exactly the production modules.')
    for relative in classified:
        body = (paper / relative).read_text(encoding='utf-8')
        require(not re.search(r'\b(sorry|admit|sorryAx|native_decide|implemented_by|unsafe)\b|^\s*(axiom|constant)\b', body, re.M),
                f'Proof-integrity violation: {relative}')
        require(not re.search(r'set_option\s+linter\S*\s+false', body),
                f'Linter suppression: {relative}')
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
    extension_manifest = read_json(paper / 'Extension/lake-manifest.json')
    require(extension_manifest['name'] == module_root, 'Wrong extension package identity.')
    require((paper / 'Extension/lean-toolchain').read_text().strip() == config['foundation']['toolchain'],
            'Extension toolchain drift.')
    require(len(extension_manifest['packages']) == len(manifest['packages']) + 1, 'Dependency graph size drift.')
    for package in manifest['packages']:
        matches = [p for p in extension_manifest['packages'] if p['name'] == package['name']]
        require(len(matches) == 1 and all(matches[0].get(k) == package.get(k)
                for k in ['type', 'rev', 'url', 'subDir']), f'Dependency drift: {package["name"]}')
    local = [p for p in extension_manifest['packages'] if p['name'] == 'RiemannZeta']
    require(len(local) == 1 and local[0]['type'] == 'path' and
            (paper / 'Extension' / local[0]['dir']).resolve() == root.resolve(), 'Wrong foundation path dependency.')
    print(f'INVENTORY/PINS PASS: {len(actual)} retained files; exact node-63 BAT; unchanged foundation graph.')
    print(f'COVERAGE PASS: {len(config["productionModules"])} production modules; two explicit verification modules.')

    gates = read_json(paper / 'Tools/proof_gates.json')
    require([g['id'] for g in gates] == [f'DKQH-{i:02}' for i in range(1, 21)], 'Gate IDs/order drift.')
    checklist = (paper / (PREFIX + 'Checklist.md')).read_text(encoding='utf-8')
    architecture = (paper / (PREFIX + 'Architecture.md')).read_text(encoding='utf-8')
    for i, gate in enumerate(gates, 1):
        require(gate['status'] in {'OPEN', 'DONE'}, f'Invalid gate status: {gate["id"]}')
        rows = re.findall(r'^\| ' + gate['id'] + r' \| (OPEN|DONE) \|', checklist, re.M)
        require(rows == [gate['status']], f'Checklist gate status mismatch: {gate["id"]}')
        nodes = re.findall(r'G' + f'{i:02}' + r'\["' + gate['id'] + r'[^\n]*?<br/>' + gate['status'] + r'"\]', architecture)
        require(len(nodes) == 1, f'Architecture gate status mismatch: {gate["id"]}')
    complete = sum(g['status'] == 'DONE' for g in gates)
    require(complete == config['proofGatesComplete'], 'Proof-count metadata drift.')
    require((config['mode'] == 'project-complete') == (complete == 20), 'Completion mode/status mismatch.')
    for name in ['README.md'] + [PREFIX + role + '.md' for role in
                               ['Checklist', 'Architecture', 'Research Agenda', 'Reproduction Manifest']]:
        require(f'{complete}/20' in (paper / name).read_text(encoding='utf-8'), f'Missing proof-count disclosure: {name}')
    prompt = (paper / (PREFIX + 'Goal Prompt.md')).read_text(encoding='utf-8')
    for marker in ['ACTIVE GOAL' if complete < 20 else 'GOAL COMPLETE', 'run_lake_build.bat',
                   'run_dhiman_kadiri_quesada_herrera_build.bat', 'push_to_github.bat', 'Recovery-record']:
        require(marker in prompt, f'Goal prompt lost required boundary: {marker}')
    regression = (paper / 'Extension' / module_root / 'SemanticRegression.lean').read_text(encoding='utf-8')
    audit = (paper / 'Extension' / module_root / 'Audit.lean').read_text(encoding='utf-8')
    for name in ['actual_sum_index_discrepancy', 'actual_residual_discrepancy',
                 'literal_functional_equation_counterexample', 'poisson_counterexample_hypotheses',
                 'poisson_counterexample_source_inequality', 'actual_afe_repair_hypotheses',
                 'lemma_one_first_tail', 'lemma_one_second_tail', 'lemma_one_third_tail',
                 'lemma_one_first_plus', 'lemma_one_second_plus', 'lemma_one_third_plus',
                 'lemma_eleven_negative', 'lemma_eleven_positive',
                 'corrected_alternating_identity', 'actual_real_gamma_log_derivative',
                 'lemma_two_geometric_identity', 'lemma_two_geometric_bound',
                 'lemma_two_harmonic_bound', 'lemma_two_half_integer_error',
                 'lemma_two_half_integer_bound', 'lemma_two_integer_cases',
                 'lemma_three_negative', 'lemma_three_positive',
                 'lemma_three_half_integer_negative', 'lemma_three_half_integer_majorant',
                 'lemma_three_half_integer_positive',
                 'lemma_three_negative_convergence', 'lemma_three_positive_convergence',
                 'actual_weighted_wave_derivative',
                 'partI_negative_frequency_integral', 'partI_positive_frequency_integral',
                 'partI_zero_source', 'partI_zero_half_integer_source',
                 'partI_general_source', 'partI_general_half_integer_source',
                 'corollary_zero_one_partI_source', 'theorem_nine_source',
                 'theorem_nine_small_cutoff_source', 'corollary_zero_three_source',
                 'corollary_zero_three_small_decimal', 'corollary_zero_three_large_decimal',
                 'corrected_functional_equation_source',
                 'actual_remainder_reflection',
                 'actual_remainder_conjugation',
                 'lemma_seven_source',
                 'lemma_seven_negative_height', 'lemma_six_source',
                 'lemma_four_source', 'lemma_five_quadratic_sum',
                 'lemma_five_lower_remainder_source', 'lemma_five_lower_sum_source', 'lemma_five_upper_sum_source', 'stationary_point_source',
                 'fresnel_window_source', 'stationary_quadratic_phase_source',
                 'partII_printed_E1_counterexample', 'weighted_integral_gamma_source',
                 'weighted_integral_chi_source', 'afe_integral_sum_source',
                 'stationary_digamma_decimal_source', 'afe_second_derivatives_source', 'afe_positive_second_quotients_source',
                 'partII_negative_second_integral', 'afe_positive_second_integral_source']:
        require(re.search(r'^theorem ' + name + r'\b', regression, re.M) and
                'SemanticRegression.' + name in audit, f'Missing required source regression/audit: {name}')
    print(f'STATUS PASS: active goal; {complete}/20 gates complete; exact source-diagnostic regressions required.')

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
