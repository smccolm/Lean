from pathlib import Path
import hashlib,json,re,sys
p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026')
d=Path('E:/Lean/.tmp/dubon83')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
foundation='../../logs/foundation_freeze_20261007_132054.log'
paper=sys.argv[1]
assert 'FINAL RESULT: PASS' in (p/foundation).read_text(encoding='utf-8-sig')
ps=(p/paper).read_text(encoding='utf-8-sig')
assert 'DEVELOPMENT PASS - IMPLEMENTED SCOPE VERIFIED; 16/20' in ps
checks=re.findall(r'AUDIT PASS: (\d+) project theorems.*?; (\d+) registered consumers',ps)
lints=re.findall(r'Found 0 errors in (\d+) declarations \(plus (\d+) automatically generated ones\)',ps)
assert len(checks)==2 and checks[0]==checks[1] and checks[0][1]=='2867',checks
assert len(lints)==2 and lints[0]==lints[1],lints
count=int(checks[0][0]);lint,gen=map(int,lints[0])
c=json.loads((p/'Tools/scaffold.json').read_text(encoding='utf8'))
assert len(c['productionModules'])==611 and c['proofGatesComplete']==16
for name in c['statusDocuments']:
 f=p/name;s=f.read_text(encoding='utf8')
 a='Focused production compilation passed; source-consumer compilation, expanded audit, all sixteen linters and sequential foundation/paper verification are pending.'
 b=f'Focused compilation, all sixteen linters, the expanded dependency audit and sequential foundation/paper verification passed with zero Lean diagnostics ({count:,} exhaustive theorem checks).'
 assert a in s,name;s=s.replace(a,b)
 s=s.replace('The preceding verified scope had 604 production modules, 233 exact consumers, 2,838 explicit audit registrations and 5,046 exhaustive theorem dependency checks; the current expanded scope is identified above.',f'The current verified scope has 611 production modules, 236 exact consumers, 2,867 explicit audit registrations and {count:,} exhaustive theorem dependency checks.')
 f.write_text(s,encoding='utf8')
receipt=f"""
### Actual Sato–Tate character and prime-average bridge — 7 October 2026

Foundation `cmd /c run_lake_build.bat --no-pause` returned **PASS, exit 0**, followed sequentially by paper `cmd /c run_dubon_build.bat --no-pause`, **DEVELOPMENT PASS, exit 0**, with zero Lean diagnostics. Coverage: 611 production modules, 236 exact consumers, 2,867 explicit registrations and {count:,} exhaustive theorem dependency checks. All sixteen linters passed across {lint:,} declarations plus {gen:,} generated declarations in both audit executions. Initial inventory passed with 718 retained files, 1,051 local links and 4,320 unchanged existing Lean files; source pins and tooling fixtures passed.

Seven modules establish exact character orthogonality for the genuine Sato–Tate coefficient law, polynomial density and actual weak probability convergence, the normalized primitive prime-power Hecke recurrence, the precise finite empirical integral, and vanishing errors from the actual finite ramified prime set. The final primitive-form consumer takes only two explicitly displayed arithmetic inputs: the good-prime norm bound and vanishing positive-order prime-power averages. It discharges real normalization, all finite ramified terms, weak convergence, positive-density selection and compact-uniform isolated-prime H2. Neither arithmetic premise has yet been proved. This is a verified conditional analytic/normalization bridge; DUB-17–20 remain OPEN. DUB-01–16 remain accepted.

A focused build initially reported a deprecated probability-mass lemma. It was replaced with `probReal_univ`; subsequent focused compilation and both complete verifiers passed with zero diagnostics. Three existing module headers now accurately distinguish the separately proved general-level Rankin–Selberg input from the still-unproved Sato–Tate input. No theorem or source hypothesis was weakened.

Dirty checkout `abbed66648e1ae22078cccafc224dd68e108f54d`; Lean 4.30.0, Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`, PNT+ `4ecb950126c4290293c5662dfe0e884123171df5`. Frozen TeX SHA-256 `605d02ea28f553ae3206cf3e0c176c93840d0a985b654d1b520b638e0a4ec08b`; PDF `a9cac7a820cc2c8b0965eb9caa4eb0eaa6e3159321a90e4e43960cbe764597f2`. The 7 October bounded arithmetic-resource review is recorded separately from the frozen 6 October source inventory. No external code was imported. ELAN_HOME was inferred from the installed Lake command. No staging, commit or push occurred.

"""
for name in [foundation,foundation[:-4]+'.json',paper,'Tools/verify_scaffold.py','Tools/test_scaffold.py','Tools/run_dubon_verification.ps1','Extension/Dubon2026/Audit.lean','Extension/Dubon2026/SemanticRegression.lean','Extension/Dubon2026.lean','Extension/lakefile.toml','Extension/lake-manifest.json']:
 receipt+=f'- [{Path(name).name}]({name}), SHA-256 `{sha(p/name)}`.\n'
for name in json.loads((d/'modules611.json').read_text(encoding='utf8'))+['CuspArithmeticConcentration','PrimitiveArithmeticConcentration','CuspSatoTateConcentration']:
 rel=f'Extension/Dubon2026/{name}.lean';receipt+=f'- `{rel}`: SHA-256 `{sha(p/rel)}`.\n'
receipt+='\nOwner BAT SHA-256 `'+sha(p/'push_to_github.bat')+'` (unchanged; not executed).\n'
with (p/'Dubon Reproduction Manifest.md').open('a',encoding='utf8') as out:out.write('\n'+receipt)
f=p/'Tools/modular_research_20261006.json';j=json.loads(f.read_text(encoding='utf8'))
v=j['satoTateCharacterImplementation20261007']
v['status']='Verified conditional character bridge: focused production/source consumers, expanded audit, all sixteen linters and sequential foundation/paper verification passed with zero diagnostics. DUB-17 remains OPEN.'
v['validation']=f'611 production modules; 236 exact consumers; 2867 explicit registrations; {count} exhaustive theorem checks; sixteen linters across {lint} declarations plus {gen} generated, in both executions. Logs: {foundation} and {paper}.'
f.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
print(f'611-module verification recorded; {count} exhaustive checks; conditional character bridge verified; 16/20 accepted.')
