from pathlib import Path
import hashlib,json,re,sys
p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026')
d=Path('E:/Lean/.tmp/dubon83')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
paper,foundation=sys.argv[1:3]
assert 'FINAL RESULT: PASS' in (p/foundation).read_text(encoding='utf-8-sig')
ps=(p/paper).read_text(encoding='utf-8-sig')
assert 'DEVELOPMENT PASS - IMPLEMENTED SCOPE VERIFIED; 16/20' in ps
checks=re.findall(r'AUDIT PASS: (\d+) project theorems.*?; (\d+) registered consumers',ps)
lints=re.findall(r'Found 0 errors in (\d+) declarations \(plus (\d+) automatically generated ones\)',ps)
assert len(checks)==2 and checks[0]==checks[1] and checks[0][1]=='3401',checks
assert len(lints)==2 and lints[0]==lints[1],lints
count=int(checks[0][0]);lint,gen=map(int,lints[0])
console=(d/'paper715-console.log').read_text(encoding='utf-16')
assert Path(paper).name in console and 'DEVELOPMENT PASS - IMPLEMENTED SCOPE VERIFIED; 16/20' in console
inventory=re.search(r'INVENTORY CHECKS PASS: (\d+) retained files, (\d+) local links, (\d+) unchanged existing Lean files',console)
assert inventory
files,links,unchanged=map(int,inventory.groups())
c=json.loads((p/'Tools/scaffold.json').read_text(encoding='utf8'))
assert len(c['productionModules'])==715 and c['proofGatesComplete']==16
for name in c['statusDocuments']:
 f=p/name;s=f.read_text(encoding='utf8')
 a='Focused production compilation passed; source-consumer compilation, expanded audit, all sixteen linters and sequential foundation/paper verification are pending.'
 b=f'Focused compilation, all sixteen linters, the expanded dependency audit and sequential foundation/paper verification passed with zero Lean diagnostics ({count:,} exhaustive theorem checks).'
 assert s.count(a)==1,(name,s.count(a));s=s.replace(a,b)
 s=s.replace('The preceding verified scope had 707 production modules, 291 exact consumers, 3,355 explicit audit registrations and 5,862 exhaustive theorem dependency checks; the current expanded scope is identified above.',f'The current verified scope has 715 production modules, 295 exact consumers, 3,401 explicit audit registrations and {count:,} exhaustive theorem dependency checks.')
 f.write_text(s,encoding='utf8')
receipt=f'''
### True projective arithmetic quotient and faithful unitary realization verification — 7 October 2026

Foundation `cmd /c run_lake_build.bat --no-pause` returned **PASS, exit 0**, followed sequentially by paper `cmd /c run_dubon_build.bat --no-pause`, **DEVELOPMENT PASS, exit 0**, with zero Lean diagnostics. Coverage: 715 production modules, 295 exact consumers, 3,401 explicit registrations and {count:,} exhaustive theorem dependency checks. All sixteen linters passed across {lint:,} declarations plus {gen:,} generated declarations in both paper audit executions. Initial inventory passed with {files:,} retained files, {links:,} local links and {unchanged:,} unchanged existing Lean files; source pins and tooling fixtures passed.

Eight modules and four exact consumers prove the actual central quotient, its proper projection and its left/right Haar measure, with exact hyperbolic orbit pushforward. The original arithmetic action gives a genuine finite-volume projective group fundamental domain. Every vector in the original cyclic span descends continuously and invariantly to an actual L2 function; the linear realization is injective. The quotient pairing has the exact original Petersson normalization. The original right action factors through the true central quotient and preserves the actual L2 inner product.

These are unconditional statements about the original representation and its faithful algebraic unitary realization. Completion and strong continuity, the adelic cuspidal representation and higher symmetric continuation remain unproved. Unconditional Deligne, non-CM Sato–Tate and the final modular application remain open. DUB-01–16 remain accepted; DUB-17–20 remain OPEN.

The foundation verifier observed dirty checkout `a6b9fb6e673f992be69233a9c452d9db2ce9a4e9`; Lean 4.30.0, Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`, PNT+ `4ecb950126c4290293c5662dfe0e884123171df5`. Frozen source and dependency revisions are unchanged. No external Lean code was imported. ELAN_HOME was inferred from the installed Lake command. No staging, commit or push was performed by this agent.

'''
for name in [foundation,foundation[:-4]+'.json',paper,'Tools/verify_scaffold.py','Tools/test_scaffold.py','Tools/run_dubon_verification.ps1','Extension/Dubon2026/Audit.lean','Extension/Dubon2026/SemanticRegression.lean','Extension/Dubon2026.lean','Extension/lakefile.toml','Extension/lake-manifest.json']:
 receipt+=f'- [{Path(name).name}]({name}), SHA-256 `{sha(p/name)}`.\n'
for name in json.loads((d/'modules715.json').read_text(encoding='utf8')):
 rel=f'Extension/Dubon2026/{name}.lean';receipt+=f'- `{rel}`: SHA-256 `{sha(p/rel)}`.\n'
receipt+='\nOwner BAT SHA-256 `'+sha(p/'push_to_github.bat')+'` (unchanged; not executed).\n'
with (p/'Dubon Reproduction Manifest.md').open('a',encoding='utf8') as out:out.write('\n'+receipt)
f=p/'Tools/modular_research_20261006.json';j=json.loads(f.read_text(encoding='utf8'))
v=j['realProjectiveUnitaryImplementation20261007']
v['status']='Verified actual projective arithmetic fundamental domain, Petersson normalization and faithful L2 realization with inner-product-preserving right action: focused production/source consumers, expanded audit, all sixteen linters and sequential foundation/paper verification passed with zero diagnostics. DUB-17 remains OPEN.'
v['validation']=f'715 production modules; 295 exact consumers; 3401 explicit registrations; {count} exhaustive theorem checks; sixteen linters across {lint} declarations plus {gen} generated, in both executions. Logs: {foundation} and {paper}.'
f.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
print(f'715-module verification recorded; {count} exhaustive checks; actual projective L2 realization verified; 16/20 accepted.')
