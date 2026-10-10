"""Validate Dubon inventories, source pins, module coverage and honest proof status."""
from pathlib import Path
from urllib.parse import unquote, urlsplit
import hashlib
import json
import re
import sys

from inspect_source_archive import inspect

PRIMARY = {
    'Sources/dubon-2609.17875v1.pdf': 'a9cac7a820cc2c8b0965eb9caa4eb0eaa6e3159321a90e4e43960cbe764597f2',
    'Sources/dubon-2609.17875v1.tar': '94ffdb0fa9c3b9b77072f3a4f148b0cc924161393aa10d8e40b3ff658ac05d55',
}
STATUS = 'TEMPLATE ONLY — NOT ACTIVATED. 0/20 proof gates complete.'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path):
    return json.loads(path.read_text(encoding='utf-8-sig'))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def retained(project):
    return {p.relative_to(project).as_posix() for p in project.rglob('*')
            if p.is_file() and not any(x in {'logs', '__pycache__', '.lake'}
                                     for x in p.relative_to(project).parts)}


def check_inactive_files(names):
    for name in names:
        p = Path(name)
        require(p.suffix.lower() != '.lean' and p.name not in
                {'lakefile.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain'},
                f'Lean conversion must remain inactive: {p.name}')


def check_state(project, config, registry):
    require(config['mode'] == registry['mode'] and config['mode'] in
            {'template-only', 'active-development', 'project-complete'}, 'Project mode mismatch')
    active = config['mode'] != 'template-only'
    require(config['goalActivated'] is active and registry['goalActivated'] is active,
            'Goal activation mismatch')
    require(registry['namespace'] == 'Dubon2026' and registry['prefix'] == 'DUB',
            'Namespace/prefix mismatch')
    require(registry['total'] == 20, 'Wrong gate total')
    gates = registry['gates']
    ids = [f'DUB-{i:02}' for i in range(1, 21)]
    require([g['id'] for g in gates] == ids, 'Missing, duplicate or reordered gate')
    complete = sum(g['status'] == 'DONE' for g in gates)
    require(registry['completed'] == complete and all(g['status'] in {'OPEN','DONE'} for g in gates),
            'Wrong gate counts/status')
    require(config['proofGatesComplete'] == complete and config['proofGatesTotal'] == 20,
            'Inventory and registry gate counts disagree')
    if not active:
        require(complete == 0 and all(not g['implementationFiles'] and not g['evidence'] for g in gates),
                'Inactive template cannot claim mathematical progress')
    if config['mode'] == 'project-complete':
        require(complete == 20, 'Project completion requires all twenty source gates')
    for i, g in enumerate(gates):
        require(all(d in ids[:i] for d in g['dependsOn']), f'Invalid/cyclic dependency: {g["id"]}')
        require(bool(g['acceptance']) and bool(g['proposedModule']), 'Empty gate contract')
        if g['status'] == 'DONE':
            require(g['implementationFiles'] and g['evidence'], f'Missing gate acceptance evidence: {g["id"]}')
            require(all(next(x for x in gates if x['id'] == d)['status'] == 'DONE'
                        for d in g['dependsOn']), f'Open upstream gate: {g["id"]}')
        for name in g['implementationFiles']:
            require((project / name).is_file(), f'Missing implementation file: {name}')
    actual = retained(project)
    require(len(config['files']) == len({x['path'] for x in config['files']}),
            'Duplicate retained-file classification')
    expected = {x['path'] for x in config['files']}
    require(actual == expected, f'Retained inventory mismatch: missing={sorted(expected-actual)}, extra={sorted(actual-expected)}')
    if active:
        check_active(project,config)
    else:
        check_inactive_files(p for p in project.rglob('*') if p.is_file())
    status = f'GOAL ACTIVE — {complete}/20 proof gates complete.' if active else STATUS
    for name in config['statusDocuments']:
        require(status in (project / name).read_text(encoding='utf-8'), f'Stale status: {name}')
    checklist = (project / 'Dubon Checklist.md').read_text(encoding='utf-8')
    diagram = (project / 'Dubon Architecture.md').read_text(encoding='utf-8')
    require(checklist.count('- [ ] **OPEN**') == 20-complete and
            checklist.count('- [x] **DONE**') == complete, 'Checklist gate counts disagree')
    for i, g in enumerate(gates, 1):
        require(f'## {g["id"]} — {g["title"]}' in checklist and g['acceptance'] in checklist,
                f'Checklist contract mismatch: {g["id"]}')
        require(f'G{i}["{g["id"]} {g["status"]}<br/>{g["title"]}"]' in diagram,
                f'Diagram state mismatch: {g["id"]}')
    expected_edges = {(int(d[-2:]), i) for i, g in enumerate(gates, 1) for d in g['dependsOn']}
    actual_edges = {(int(a), int(b)) for a, b in re.findall(r'G(\d+) --> G(\d+)', diagram)}
    require(actual_edges == expected_edges, 'Diagram dependency mismatch')


def check_active(project, config):
    namespace = 'Dubon2026'
    require(config['verificationModules'] == ['ArithmeticSemanticRegression','SemanticRegression','Audit'],
            'Both semantic regression modules and the audit are mandatory')
    require(config['productionModules'], 'Active package must contain real production modules')
    modules = config['productionModules'] + config['verificationModules']
    classified = {f'Extension/{namespace}.lean'} | {
        f'Extension/{namespace}/{m.replace(".","/")}.lean' for m in modules}
    require(len(classified) == 1+len(modules), 'Duplicate module classification')
    actual = {name for name in retained(project) if name.endswith('.lean')}
    require(classified == actual, 'Unclassified or missing Lean module')
    pending, visited = [namespace],set()
    while pending:
        module = pending.pop()
        if module in visited: continue
        visited.add(module)
        body=(project/'Extension'/(module.replace('.','/')+'.lean')).read_text(encoding='utf-8')
        pending.extend(re.findall(r'^import (Dubon2026(?:\.[A-Za-z0-9_]+)+)\s*$',body,re.M))
    require(visited == {namespace}|{namespace+'.'+m for m in config['productionModules']},
            'Root imports do not cover exactly all production modules')
    for relative in classified:
        body=(project/relative).read_text(encoding='utf-8')
        require(not re.search(r'\b(sorry|admit|sorryAx|native_decide|implemented_by|unsafe)\b|^\s*(axiom|constant)\b',body,re.M),
                f'Proof-integrity violation: {relative}')
        require(not re.search(r'set_option\s+linter\S*\s+false',body),f'Linter suppression: {relative}')
    root=project.parents[1]
    parent=read_json(root/'lake-manifest.json')
    extension=read_json(project/'Extension/lake-manifest.json')
    require(extension['name']==namespace,'Wrong package identity')
    require((project/'Extension/lean-toolchain').read_bytes()==(root/'lean-toolchain').read_bytes(),
            'Extension toolchain differs from selected root')
    check_dependency_graph(project, parent, extension)


def check_dependency_graph(project, parent, extension):
    root=project.parents[1]
    require(len(extension['packages'])==len(parent['packages'])+4,'Dependency graph size drift')
    for package in parent['packages']:
        matches=[p for p in extension['packages'] if p['name']==package['name']]
        require(len(matches)==1 and all(matches[0].get(k)==package.get(k)
                for k in ['type','rev','url','subDir']),f'Dependency drift: {package["name"]}')
    local=[p for p in extension['packages'] if p['name']=='RiemannZeta']
    require(len(local)==1 and local[0]['type']=='path' and
            (project/'Extension'/local[0]['dir']).resolve()==root.resolve(),'Wrong foundation path dependency')
    reused=[p for p in extension['packages'] if p['name']=='GafniTaoNative']
    reused_path=project.parent/'63 Tao-Trudgian-Yang, 2025'/'Dependencies'/'GafniTaoNative'
    require(len(reused)==1 and reused[0]['type']=='path' and
            (project/'Extension'/reused[0]['dir']).resolve()==reused_path.resolve(),
            'Wrong audited node-63 PNT path dependency')
    for name, relative in [('TaoTrudgianYang2025','Extension'),
                           ('ExpdbFrozen','Dependencies/ANTEDBFrozen')]:
        reused=[p for p in extension['packages'] if p['name']==name]
        reused_path=project.parent/'63 Tao-Trudgian-Yang, 2025'/relative
        require(len(reused)==1 and reused[0]['type']=='path' and
                (project/'Extension'/reused[0]['dir']).resolve()==reused_path.resolve(),
                f'Wrong audited node-63 path dependency: {name}')


def check_links(project):
    count = 0
    for p in project.rglob('*.md'):
        rel = p.relative_to(project)
        if 'logs' in rel.parts or ('Sources' in rel.parts and p.name not in {'README.md', 'PINS.md'}):
            continue  # Frozen upstream README links retain their original repository context.
        for target in re.findall(r'(?<!!)\[[^\]\n]+\]\(([^)]+)\)', p.read_text(encoding='utf-8')):
            if urlsplit(target).scheme or target.startswith('#'):
                continue
            target = unquote(target.split('#', 1)[0]).strip('<>')
            require((p.parent / target).exists(), f'Broken local link in {rel}: {target}')
            count += 1
    return count


def main():
    project = Path(__file__).resolve().parents[1]
    root = project.parents[1]
    config = read_json(project / 'Tools/scaffold.json')
    registry = read_json(project / 'Tools/proof_gates.json')
    check_state(project, config, registry)
    for name, expected in PRIMARY.items():
        require(sha(project / name) == expected, f'Frozen primary identity changed: {name}')
    for entry in config['parentConfiguration']:
        require(sha(root / entry['path']) == entry['sha256'], f'Parent pin/config changed: {entry["path"]}')
    owner = root / config['ownerSyncSource']
    require((project / 'push_to_github.bat').read_bytes() == owner.read_bytes(),
            'Synchronization BAT is not the exact Project-63 copy')
    require(sha(owner) == config['ownerSyncSha256'], 'Frozen owner synchronization identity changed')
    for entry in config['copiedVerifierFiles']:
        require(sha(project / entry['path']) == entry['sha256'], f'Original source verifier changed: {entry["path"]}')
    index = read_json(project / 'Tools/source_labels.json')
    source = project / index['source']
    require(sha(source) == index['sha256'], 'Label index source hash mismatch')
    tex = source.read_text(encoding='utf-8')
    labels = [{'label':m.group(1), 'line':tex[:m.start()].count('\n')+1}
              for m in re.finditer(r'\\label\{([^}]+)\}', tex)]
    require(index['labels'] == labels and len(labels) == 139, 'Source label index mismatch')
    bibliography = [{'key':m.group(1), 'line':tex[:m.start()].count('\n')+1, 'tex':m.group(2).strip()}
                    for m in re.finditer(r'\\bibitem\{([^}]+)\}(.*?)(?=\\bibitem|\\end\{thebibliography\})', tex, re.S)]
    require(index['bibliography'] == bibliography and len(bibliography) == 25, 'Bibliography index mismatch')
    labelset = {x['label'] for x in labels}
    for gate in registry['gates']:
        require(set(gate['sourceLabels']) <= labelset, f'Unresolved source anchor: {gate["id"]}')
    inventory = read_json(project / 'Tools/local_reuse_inventory.json')
    for entry in inventory['existingTrackedLeanFiles'] + inventory['selectedFiles']:
        path = root / entry['path']
        require(path.is_file() and sha(path) == entry['sha256'], f'Existing source changed since survey: {entry["path"]}')
    for entry in read_json(project / 'Tools/pnt_reuse.json')['selectedFiles']:
        path = project.parent / entry['pathFromSection']
        require(path.is_file() and sha(path) == entry['sha256'],
                f'Audited PNT reuse source drift: {entry["pathFromSection"]}')
    sturm = read_json(project / 'Tools/sturm_reuse.json')
    require(sturm['revision'] == '53ce31466dc5ff520463249d470119c1e0006e22' and
            sturm['license'] == 'Apache-2.0' and sturm['targetLean'] == '4.30.0',
            'Sturm port provenance drift')
    for entry in sturm['files']:
        path = project / entry['path']
        require(path.is_file() and path.stat().st_size == entry['bytes'] and
                sha(path) == entry['sha256'], f'Sturm source snapshot drift: {entry["path"]}')
    modular = read_json(project / 'Tools/modular_reuse.json')
    require(modular['revision'] == '7c41b9b1747d47298f76bdb51f07031087702198' and
            modular['license'] == 'Apache-2.0' and modular['targetLean'] == '4.30.0',
            'Petersson port provenance drift')
    for entry in modular['files']:
        path = project / entry['path']
        require(path.is_file() and path.stat().st_size == entry['bytes'] and
                sha(path) == entry['sha256'], f'Petersson source snapshot drift: {entry["path"]}')
    for entry in read_json(project / 'Tools/download_receipts.json'):
        path = project / entry['path']
        require(path.stat().st_size == entry['bytes'] and sha(path) == entry['sha256'],
                f'Download receipt differs: {entry["path"]}')
    snapshot = read_json(project / 'Tools/upstream_snapshot.json')
    require(snapshot['asOf'] == '2026-10-06', 'Wrong research cutoff')
    for entry in snapshot['repositories']:
        require(not entry['selectedDependency'] and not entry['treeTruncated'],
                'Unexpected dependency selection or truncated repository survey')
    count = inspect(project)
    links = check_links(project)
    print(f'INVENTORY CHECKS PASS: {len(config["files"])} retained files, {links} local links, '
          f'{len(inventory["existingTrackedLeanFiles"])} unchanged existing Lean files, '
          f'{count} source archive members, 139 labels and 25 bibliography entries.')
    if config['mode']=='template-only':
        print('TEMPLATE ONLY: goal inactive; 0/20 proof gates complete; no Lean proof tested.')
    else:
        print(f'ACTIVE INVENTORY: {registry["completed"]}/20 proof gates complete; Lean build and audit still required.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, OSError, json.JSONDecodeError) as exc:
        print(f'INVENTORY FAIL: {exc}', file=sys.stderr)
        sys.exit(1)
