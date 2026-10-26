from pathlib import Path
import hashlib,json,re,sys
p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026')
d=Path('E:/Lean/.tmp/dubon83')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
foundation='../../logs/foundation_freeze_20261007_140625.log'
paper=sys.argv[1]
assert 'FINAL RESULT: PASS' in (p/foundation).read_text(encoding='utf-8-sig')
ps=(p/paper).read_text(encoding='utf-8-sig')
assert 'DEVELOPMENT PASS - IMPLEMENTED SCOPE VERIFIED; 16/20' in ps
checks=re.findall(r'AUDIT PASS: (\d+) project theorems.*?; (\d+) registered consumers',ps)
lints=re.findall(r'Found 0 errors in (\d+) declarations \(plus (\d+) automatically generated ones\)',ps)
assert len(checks)==2 and checks[0]==checks[1] and checks[0][1]=='2960',checks
assert len(lints)==2 and lints[0]==lints[1],lints
count=int(checks[0][0]);lint,gen=map(int,lints[0])
c=json.loads((p/'Tools/scaffold.json').read_text(encoding='utf8'))
assert len(c['productionModules'])==627 and c['proofGatesComplete']==16
for name in c['statusDocuments']:
 f=p/name;s=f.read_text(encoding='utf8')
 a='Focused production compilation passed; source-consumer compilation, expanded audit, all sixteen linters and sequential foundation/paper verification are pending.'
 b=f'Focused compilation, all sixteen linters, the expanded dependency audit and sequential foundation/paper verification passed with zero Lean diagnostics ({count:,} exhaustive theorem checks).'
 assert s.count(a)==1,(name,s.count(a));s=s.replace(a,b)
 s=s.replace('The preceding verified scope had 622 production modules, 243 exact consumers, 2,930 explicit audit registrations and 5,177 exhaustive theorem dependency checks; the current expanded scope is identified above.',f'The current verified scope has 627 production modules, 246 exact consumers, 2,960 explicit audit registrations and {count:,} exhaustive theorem dependency checks.')
 f.write_text(s,encoding='utf8')
receipt=f'''
### Actual local logarithmic derivatives and higher-prime-power correction verification — 7 October 2026

Foundation `cmd /c run_lake_build.bat --no-pause` returned **PASS, exit 0**, followed sequentially by paper `cmd /c run_dubon_build.bat --no-pause`, **DEVELOPMENT PASS, exit 0**, with zero Lean diagnostics. Coverage: 627 production modules, 246 exact consumers, 2,960 explicit registrations and {count:,} exhaustive theorem dependency checks. All sixteen linters passed across {lint:,} declarations plus {gen:,} generated declarations in both paper audit executions. Initial inventory passed with 734 retained files, 1,164 local links and 4,320 unchanged existing Lean files; source pins and tooling fixtures passed.

Five modules and three exact consumers prove the genuine local spectral Euler logarithmic derivatives, their exact first-prime/higher-power decomposition, and the actual remainder's holomorphy on Re(s)>1/2. A uniform prime majorant log(p)p^(-2a) is summable by actual von Mangoldt convergence. Primitive Hecke roots supply the original symmetric-power trace coefficients and exact local Euler factors, with the finite ramified set explicitly removed. The original prime-character L-series is proved to be the genuine local derivative series minus that analytic remainder. Its boundary continuation therefore follows from continuation of the local derivative series, and the already proved Tauberian/PNT/character chain yields weak Sato--Tate and full H2.

The actual local coefficient bound and boundary continuation of the derivative series remain explicit unproved arithmetic inputs. The genuine global spectral product/logarithmic-derivative identification, automorphic and Galois constructions, Deligne purity and required global continuation/nonvanishing remain open. DUB-17--20 remain OPEN and DUB-01--16 remain accepted. Focused production/source checks and both full verifiers passed with zero diagnostics; no target hypothesis was weakened.

The foundation verifier observed clean checkout `a6b9fb6e673f992be69233a9c452d9db2ce9a4e9` (an externally created `Progress Update` commit detected during ongoing work); Lean 4.30.0, Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`, PNT+ `4ecb950126c4290293c5662dfe0e884123171df5`. The frozen source and dependency revisions are unchanged. No external Lean code was imported. ELAN_HOME was inferred from the installed Lake command. No staging, commit or push was performed by this agent.

'''
for name in [foundation,foundation[:-4]+'.json',paper,'Tools/verify_scaffold.py','Tools/test_scaffold.py','Tools/run_dubon_verification.ps1','Extension/Dubon2026/Audit.lean','Extension/Dubon2026/SemanticRegression.lean','Extension/Dubon2026.lean','Extension/lakefile.toml','Extension/lake-manifest.json']:
 receipt+=f'- [{Path(name).name}]({name}), SHA-256 `{sha(p/name)}`.\n'
for name in json.loads((d/'modules627.json').read_text(encoding='utf8')):
 rel=f'Extension/Dubon2026/{name}.lean';receipt+=f'- `{rel}`: SHA-256 `{sha(p/rel)}`.\n'
receipt+='\nOwner BAT SHA-256 `'+sha(p/'push_to_github.bat')+'` (unchanged; not executed).\n'
with (p/'Dubon Reproduction Manifest.md').open('a',encoding='utf8') as out:out.write('\n'+receipt)
f=p/'Tools/modular_research_20261006.json';j=json.loads(f.read_text(encoding='utf8'))
v=j['spectralTailImplementation20261007']
v['status']='Verified actual higher-prime-power correction and conditional spectral boundary transfer: focused production/source consumers, expanded audit, all sixteen linters and sequential foundation/paper verification passed with zero diagnostics. DUB-17 remains OPEN.'
v['validation']=f'627 production modules; 246 exact consumers; 2960 explicit registrations; {count} exhaustive theorem checks; sixteen linters across {lint} declarations plus {gen} generated, in both executions. Logs: {foundation} and {paper}.'
f.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
print(f'627-module verification recorded; {count} exhaustive checks; higher-prime-power correction verified; 16/20 accepted.')
