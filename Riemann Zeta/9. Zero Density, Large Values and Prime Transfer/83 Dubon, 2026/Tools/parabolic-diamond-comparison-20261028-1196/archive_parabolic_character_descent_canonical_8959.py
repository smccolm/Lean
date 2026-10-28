from pathlib import Path
import json,hashlib,re
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
cpath=r/'Tools/scaffold.json';c=json.loads(cpath.read_text(encoding='utf-8'))
d=json.loads((r/'Tools/lean-reuse-audit-20261015.json').read_text(encoding='utf-8'))
receipt=d['appliedSourceParabolicCharacterDescent']['receipt8959'];assert receipt['exit']==receipt['diagnostics']==0
archive=r/'Tools/parabolic-character-descent-20261028-1183'
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
assert (p/'paper-verification-8959-console.exit').read_text().strip()=='0'
registered={x['path'] for x in c['files']};files=[]
for f in sorted(p.iterdir()):
 if not f.is_file() or not re.search(r'8959(?:b|c|d)?\.',f.name):continue
 if f.suffix not in ['.py','.ps1','.json','.lean','.log','.exit']:continue
 if f.name.startswith('archive_parabolic_character_descent_canonical_'):continue
 if f.name in ['root-verification-8959-console.log','paper-verification-8959-console.log']:continue
 target=archive/(f.name+('.txt' if f.suffix=='.lean' else ''))
 if target.exists():assert sha(target)==sha(f)
 else:target.write_bytes(f.read_bytes())
 rel=target.relative_to(r).as_posix()
 if rel not in registered:c['files'].append(dict(path=rel,role='Tools'));registered.add(rel)
 files.append(dict(source=str(f),path=rel,sha256=sha(f)))
manifest=archive/'canonical-evidence-8959.json';assert not manifest.exists()
manifest.write_text(json.dumps(dict(status='Canonical PASS of the original parabolic operator congruence away from a fixed integer, actual finite parabolic/Tate word kernels and explicitly conditional transfer descent. Scratch failures and fresh successors are preserved. All mathematical bodies remain identical to their scratch-audited form after import qualification; no verification requirement weakened.',files=files,canonical=receipt,largeCanonicalConsoleEvidence=[dict(path=str(p/n),sha256=sha(p/n)) for n in ['root-verification-8959-console.log','paper-verification-8959-console.log']]),indent=2)+'\n',encoding='utf-8')
c['files'].append(dict(path=manifest.relative_to(r).as_posix(),role='Tools'))
cpath.write_text(json.dumps(c,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(dict(archived=len(files),manifest=str(manifest),sha256=sha(manifest))))
