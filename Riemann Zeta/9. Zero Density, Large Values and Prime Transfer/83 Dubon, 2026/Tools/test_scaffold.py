"""Isolated regression fixtures for template-state/documentation integrity."""
from copy import deepcopy
from datetime import datetime
from pathlib import Path
import shutil
import re

from verify_scaffold import STATUS, check_active, check_dependency_graph, check_inactive_files, check_links, check_state, read_json


def main():
    project = Path(__file__).resolve().parents[1]
    fixtures = project / 'logs' / ('scaffold-tests-' + datetime.now().strftime('%Y%m%d-%H%M%S-%f'))
    fixtures.mkdir(parents=True)
    original_config = read_json(project / 'Tools/scaffold.json')
    original_registry = read_json(project / 'Tools/proof_gates.json')
    # Minimal self-contained documentation fixture; no source archive or Lean proof is copied.
    cases = ['valid', 'active-mode', 'activated-goal', 'done-gate', 'fake-evidence',
             'missing-gate', 'cycle', 'lean-file', 'lake-file', 'extra-file',
             'missing-file', 'stale-status', 'wrong-edge', 'broken-link']
    for case in cases:
        folder = fixtures / case
        folder.mkdir()
        for name in ['Dubon Checklist.md', 'Dubon Architecture.md']:
            shutil.copyfile(project / name, folder / name)
            target=folder/name
            text = target.read_text(encoding='utf-8').replace(
                'GOAL ACTIVE — 0/20 proof gates complete.', STATUS)
            # Fixtures carry status/contracts, not the production dependency tree.
            # Keep their link tests self-contained; the runner separately validates
            # every link in the real project before reaching these regressions.
            text = re.sub(r'\[([^\]\n]+)\]\([^)]+\)', r'\1', text)
            target.write_text(text, encoding='utf-8')
        (folder / 'reference.txt').write_text('Valid local fixture target.', encoding='utf-8')
        with (folder / 'Dubon Architecture.md').open('a', encoding='utf-8') as out:
            out.write('\n[Fixture reference](reference.txt)\n')
        config = deepcopy(original_config)
        config['mode']='template-only'
        config['goalActivated']=False
        config['statusDocuments'] = ['Dubon Checklist.md', 'Dubon Architecture.md']
        config['files'] = [{'path':x} for x in config['statusDocuments'] + ['reference.txt']]
        registry = deepcopy(original_registry)
        registry['mode']='template-only'
        registry['goalActivated']=False
        for gate in registry['gates']:
            gate['implementationFiles']=[]
            gate['evidence']=[]
        if case == 'active-mode': config['mode'] = 'active-development'
        elif case == 'activated-goal': registry['goalActivated'] = True
        elif case == 'done-gate': registry['gates'][0]['status'] = 'DONE'
        elif case == 'fake-evidence': registry['gates'][0]['evidence'] = ['claimed proof']
        elif case == 'missing-gate': registry['gates'].pop()
        elif case == 'cycle': registry['gates'][0]['dependsOn'] = ['DUB-20']
        elif case == 'extra-file':
            (folder / 'extra.txt').write_text('',encoding='utf-8')
        elif case == 'missing-file': config['files'].append({'path':'absent.md'})
        elif case in {'stale-status','wrong-edge','broken-link'}:
            p = folder / 'Dubon Architecture.md'
            text = p.read_text(encoding='utf-8')
            if case == 'stale-status': text = text.replace('0/20','1/20')
            elif case == 'wrong-edge': text = text.replace('G1 --> G2','G20 --> G2')
            else: text += '\n[Missing](missing.md)\n'
            p.write_text(text,encoding='utf-8')
        accepted = True
        try:
            if case in {'lean-file', 'lake-file'}:
                # Validate disallowed names in memory; do not create any Lean/Lake file.
                check_inactive_files(['New.lean' if case == 'lean-file' else 'lakefile.toml'])
            check_state(folder,config,registry)
            check_links(folder)
        except ValueError as exc:
            accepted = False
            rejection = str(exc)
        if accepted != (case == 'valid'):
            raise ValueError(f'Unexpected validation result: {case}, accepted={accepted}: '
                             f'{rejection if not accepted else "unexpected acceptance"}')
        print(f'TEMPLATE TEST PASS: {case} (accepted={accepted})')
    print(f'TEMPLATE TESTS PASS: {len(cases)}; no Lean proof tested. Fixtures: {fixtures}')
    if original_config['mode'] != 'template-only':
        for case in ['valid','missing-audit','missing-production','duplicate-production']:
            config=deepcopy(original_config)
            if case=='missing-audit':config['verificationModules']=['SemanticRegression']
            elif case=='missing-production':config['productionModules']=[]
            elif case=='duplicate-production':config['productionModules']*=2
            accepted=True
            try:check_active(project,config)
            except ValueError:accepted=False
            if accepted!=(case=='valid'):raise ValueError(f'Unexpected active check: {case}')
            print(f'ACTIVE METADATA TEST PASS: {case} (accepted={accepted})')
        parent=read_json(project.parents[1]/'lake-manifest.json')
        selected=read_json(project/'Extension/lake-manifest.json')
        for case in ['valid','wrong-reuse-path','missing-reuse','root-pin-drift']:
            candidate=deepcopy(selected)
            if case=='wrong-reuse-path':
                next(x for x in candidate['packages'] if x['name']=='GafniTaoNative')['dir']='../wrong'
            elif case=='missing-reuse':
                candidate['packages']=[x for x in candidate['packages'] if x['name']!='GafniTaoNative']
            elif case=='root-pin-drift':
                next(x for x in candidate['packages'] if x['name']=='mathlib')['rev']='0'*40
            accepted=True
            try:check_dependency_graph(project,parent,candidate)
            except ValueError:accepted=False
            if accepted!=(case=='valid'):raise ValueError(f'Unexpected dependency check: {case}')
            print(f'DEPENDENCY TEST PASS: {case} (accepted={accepted})')


if __name__ == '__main__':
    main()
