from pathlib import Path
import hashlib,json,re,sys
from datetime import datetime
now=datetime.now(); verificationDate=f'{now.day} {now.strftime("%B %Y")}'
p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026')
d=Path('E:/Lean/.tmp/dubon83')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
paper,foundation=sys.argv[1:3]
key='coordinateGenerationCotangentImplementation20261009'
implementation_summary=json.loads((p/'Tools/modular_research_20261006.json').read_text(encoding='utf8'))[key]['mathematics'].split('\n\n')[1]
foundation_text=(p/foundation).read_text(encoding='utf-8-sig');assert 'FINAL RESULT: PASS' in foundation_text
observed_commit=re.search(r'^Commit: ([a-f0-9]{40})$',foundation_text,re.M).group(1)
ps=(p/paper).read_text(encoding='utf-8-sig');assert 'DEVELOPMENT PASS - IMPLEMENTED SCOPE VERIFIED; 16/20' in ps
checks=re.findall(r'AUDIT PASS: (\d+) project theorems.*?; (\d+) registered consumers',ps)
lints=re.findall(r'Found 0 errors in (\d+) declarations \(plus (\d+) automatically generated ones\)',ps)
assert len(checks)==2 and checks[0]==checks[1] and checks[0][1]=='6203',checks
assert len(lints)==2 and lints[0]==lints[1],lints
count=int(checks[0][0]);lint,gen=map(int,lints[0])
console=(d/'paper1421-console.log').read_text(encoding='utf-16')
assert Path(paper).name in console and 'DEVELOPMENT PASS - IMPLEMENTED SCOPE VERIFIED; 16/20' in console
inventory=re.search(r'INVENTORY CHECKS PASS: (\d+) retained files, (\d+) local links, (\d+) unchanged existing Lean files',console);assert inventory
files,links,unchanged=map(int,inventory.groups())
c=json.loads((p/'Tools/scaffold.json').read_text(encoding='utf8'));assert len(c['productionModules'])==1421 and c['proofGatesComplete']==16
for name in c['statusDocuments']:
 f=p/name;s=f.read_text(encoding='utf8')
 a='Focused production compilation passed; source-consumer compilation, expanded audit, all sixteen linters and sequential foundation/paper verification are pending.'
 b=f'Focused compilation, all sixteen linters, the expanded dependency audit and sequential foundation/paper verification passed with zero Lean diagnostics ({count:,} exhaustive theorem checks).'
 assert s.count(a)==1,(name,s.count(a));s=s.replace(a,b)
 s=s.replace('The current verified scope has 1417 production modules, 784 exact consumers, 6,189 explicit audit registrations and 11,469 exhaustive theorem dependency checks.',f'The current verified scope has 1421 production modules, 788 exact consumers, 6,203 explicit audit registrations and {count:,} exhaustive theorem dependency checks.')
 f.write_text(s,encoding='utf8')
receipt=f'''
### Original coordinate generation, cotangent and representation point verification — {verificationDate}

Foundation `cmd /c run_lake_build.bat --no-pause` returned **PASS, exit 0**, followed sequentially by paper `cmd /c run_dubon_build.bat --no-pause`, **DEVELOPMENT PASS, exit 0**, with zero Lean diagnostics. Coverage: 1421 production modules, 788 exact consumers, 6,203 explicit registrations and {count:,} exhaustive theorem dependency checks. All sixteen linters passed across {lint:,} declarations plus {gen:,} generated declarations in both paper audit executions. Initial inventory passed with {files:,} retained files, {links:,} local links and {unchanged:,} unchanged existing Lean files; source pins and tooling fixtures passed.

{implementation_summary}

The original coordinate matrix entries generate the actual quotient algebra. Its original multiplication law propagates algebra membership through the genuine multiplicative generators of the original group. A finitely generated abstract group therefore has a finite-type coordinate algebra, Noetherian over a Noetherian base ring. The actual Kähler module of that original algebra supplies linear maps equivalent to the original adjoint cocycles; the proof composes the pinned Kähler universal property with the previously proved original square-zero coordinate derivation correspondence. For an abstract finitely generated group the actual Kähler module is finite over the coordinate algebra. The original representation point evaluation is surjective, its literal kernel quotient is isomorphic to the coefficient algebra with exact coordinate evaluation, and its kernel is maximal when the coefficient ring is a field. No topological finite-generation variant is inferred. Complete local profinite or pseudodeformation representability, Galois association, local p-adic Hodge and Selmer inputs, patching, higher automorphic lifting and analytic continuation remain open. Unconditional Deligne, non-CM Sato–Tate and the final modular application remain open; DUB-01–16 accepted and DUB-17–20 OPEN.

Four exact consumers expose original generator-coordinate algebra generation, Noetherianity for the original finitely generated abstract group, realization of original adjoint cocycles by the genuine Kähler module, and literal original point-quotient evaluation. No finite generation, cotangent universal property, point maximality or residue identification is assumed. No resource budgets or diagnostics are weakened.

The foundation verifier observed dirty checkout `{observed_commit}`; Lean 4.30.0, Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`, PNT+ `4ecb950126c4290293c5662dfe0e884123171df5`. Frozen source and dependency revisions are unchanged. No external Lean code was imported. ELAN_HOME was inferred from the installed Lake command. No staging, commit or push was performed by this agent.

'''
for name in [foundation,foundation[:-4]+'.json',paper,'Tools/verify_scaffold.py','Tools/test_scaffold.py','Tools/run_dubon_verification.ps1','Extension/Dubon2026/Audit.lean','Extension/Dubon2026/SemanticRegression.lean','Extension/Dubon2026.lean','Extension/lakefile.toml','Extension/lake-manifest.json']:
 receipt+=f'- [{Path(name).name}]({name}), SHA-256 `{sha(p/name)}`.\n'
for name in json.loads((d/'modules1421.json').read_text(encoding='utf8')):
 rel=f'Extension/Dubon2026/{name}.lean';receipt+=f'- `{rel}`: SHA-256 `{sha(p/rel)}`.\n'
receipt+='\nOwner BAT SHA-256 `'+sha(p/'push_to_github.bat')+'` (unchanged; not executed).\n'
with (p/'Dubon Reproduction Manifest.md').open('a',encoding='utf8') as out:out.write('\n'+receipt)
f=p/'Tools/modular_research_20261006.json';j=json.loads(f.read_text(encoding='utf8'));v=j[key]
v['status']='Verified actual coordinate generation and finite type for abstract finitely generated groups, Noetherianity over a Noetherian base, genuine Kaehler maps to original adjoint cocycles, finite coordinate Kaehler module, and original point kernel/residue identification. Profinite complete local or pseudodeformation representability, Galois association, local conditions, patching and higher automorphic lifting remain open; DUB-17 remains OPEN.'
v['validation']=f'1421 production modules; 788 exact consumers; 6203 explicit registrations; {count} exhaustive theorem checks; sixteen linters across {lint} declarations plus {gen} generated, in both executions. Logs: {foundation} and {paper}.'
f.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
for q in [p.parent/'README.md',p.parents[1]/'README.md']:
 s=q.read_text(encoding='utf8');s=s.replace('(focused compilation passed; expanded verification pending)', '(focused compilation, expanded audit, all sixteen linters and sequential foundation/paper verification passed with zero diagnostics)');q.write_text(s,encoding='utf8')
print(f'1421-module verification recorded; {count} exhaustive checks; {lint}+{gen} linter declarations; 16/20 accepted.')
