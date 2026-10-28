from pathlib import Path
import hashlib,json,re,sys
p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026')
d=Path('E:/Lean/.tmp/dubon83')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
paper,foundation=sys.argv[1:3]
key='adelicEveryPlaceIrreducibleCoefficientImplementation20261008'
implementation_summary=json.loads((p/'Tools/modular_research_20261006.json').read_text(encoding='utf8'))[key]['mathematics'].split('\n\n')[1]
foundation_text=(p/foundation).read_text(encoding='utf-8-sig');assert 'FINAL RESULT: PASS' in foundation_text
observed_commit=re.search(r'^Commit: ([a-f0-9]{40})$',foundation_text,re.M).group(1)
ps=(p/paper).read_text(encoding='utf-8-sig');assert 'DEVELOPMENT PASS - IMPLEMENTED SCOPE VERIFIED; 16/20' in ps
checks=re.findall(r'AUDIT PASS: (\d+) project theorems.*?; (\d+) registered consumers',ps)
lints=re.findall(r'Found 0 errors in (\d+) declarations \(plus (\d+) automatically generated ones\)',ps)
assert len(checks)==2 and checks[0]==checks[1] and checks[0][1]=='5447',checks
assert len(lints)==2 and lints[0]==lints[1],lints
count=int(checks[0][0]);lint,gen=map(int,lints[0])
console=(d/'paper1234-console.log').read_text(encoding='utf-16')
assert Path(paper).name in console and 'DEVELOPMENT PASS - IMPLEMENTED SCOPE VERIFIED; 16/20' in console
inventory=re.search(r'INVENTORY CHECKS PASS: (\d+) retained files, (\d+) local links, (\d+) unchanged existing Lean files',console);assert inventory
files,links,unchanged=map(int,inventory.groups())
c=json.loads((p/'Tools/scaffold.json').read_text(encoding='utf8'));assert len(c['productionModules'])==1234 and c['proofGatesComplete']==16
for name in c['statusDocuments']:
 f=p/name;s=f.read_text(encoding='utf8')
 a='Focused production compilation passed; source-consumer compilation, expanded audit, all sixteen linters and sequential foundation/paper verification are pending.'
 b=f'Focused compilation, all sixteen linters, the expanded dependency audit and sequential foundation/paper verification passed with zero Lean diagnostics ({count:,} exhaustive theorem checks).'
 assert s.count(a)==1,(name,s.count(a));s=s.replace(a,b)
 s=s.replace('The current verified scope has 1221 production modules, 581 exact consumers, 5,407 explicit audit registrations and 9,886 exhaustive theorem dependency checks.',f'The current verified scope has 1234 production modules, 594 exact consumers, 5,447 explicit audit registrations and {count:,} exhaustive theorem dependency checks.')
 f.write_text(s,encoding='utf8')
receipt=f'''
### Every-place local irreducibility and coefficient factorization verification — 8 October 2026

Foundation `cmd /c run_lake_build.bat --no-pause` returned **PASS, exit 0**, followed sequentially by paper `cmd /c run_dubon_build.bat --no-pause`, **DEVELOPMENT PASS, exit 0**, with zero Lean diagnostics. Coverage: 1234 production modules, 594 exact consumers, 5,447 explicit registrations and {count:,} exhaustive theorem dependency checks. All sixteen linters passed across {lint:,} declarations plus {gen:,} generated declarations in both paper audit executions. Initial inventory passed with {files:,} retained files, {links:,} local links and {unchanged:,} unchanged existing Lean files; source pins and tooling fixtures passed.

{implementation_summary}

Actual local cyclic level-fixed lines, Hilbert and smooth-core irreducibility, and normalized coefficient/Gram products are now proved at every original finite place. The original full finite Hilbert factor is admissible and its smooth vectors are exactly its genuine algebraic core. The real/finite tensor equivalence and restricted good-place tensor with independent full action remain proved. Individual bad-place tensor factorization of the fixed base, spherical representation/Euler-factor classification, full adelic admissibility across all real compact types, the automorphic non-CM bridge and higher symmetric automorphy/continuation remain open. Unconditional Deligne, non-CM Sato–Tate and the final modular application remain open. DUB-01–16 remain accepted; DUB-17–20 remain OPEN.

Focused elaboration removed an unused level-positivity instance from the scalar normalization identity, factored scalar cancellation into a small genuine module lemma to avoid deep representation instance search, and explicitly included the positive-weight hypothesis where the all-place normalized factorization consumes the bad-place theorem. Default resource budgets and diagnostic checks are unchanged. All thirteen production modules and thirteen exact original-object consumers compiled cleanly before the expanded audit and sequential full verifiers.

The foundation verifier observed dirty checkout `{observed_commit}`; Lean 4.30.0, Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`, PNT+ `4ecb950126c4290293c5662dfe0e884123171df5`. Frozen source and dependency revisions are unchanged. No external Lean code was imported. ELAN_HOME was inferred from the installed Lake command. No staging, commit or push was performed by this agent.

'''
for name in [foundation,foundation[:-4]+'.json',paper,'Tools/verify_scaffold.py','Tools/test_scaffold.py','Tools/run_dubon_verification.ps1','Extension/Dubon2026/Audit.lean','Extension/Dubon2026/SemanticRegression.lean','Extension/Dubon2026.lean','Extension/lakefile.toml','Extension/lake-manifest.json']:
 receipt+=f'- [{Path(name).name}]({name}), SHA-256 `{sha(p/name)}`.\n'
for name in json.loads((d/'modules1234.json').read_text(encoding='utf8')):
 rel=f'Extension/Dubon2026/{name}.lean';receipt+=f'- `{rel}`: SHA-256 `{sha(p/rel)}`.\n'
receipt+='\nOwner BAT SHA-256 `'+sha(p/'push_to_github.bat')+'` (unchanged; not executed).\n'
with (p/'Dubon Reproduction Manifest.md').open('a',encoding='utf8') as out:out.write('\n'+receipt)
f=p/'Tools/modular_research_20261006.json';j=json.loads(f.read_text(encoding='utf8'));v=j[key]
v['status']='Verified original bad-place fixed line via distinct actual local Hecke propagation, faithful classical reconstruction and primitive good-prime multiplicity one. Every original finite place now has the genuine cyclic fixed line, scalar commutants, Hilbert and smooth-core irreducibility, and exact local/full-complement coefficients and Gram products. Actual finite-family products include ramified places, and full finite smooth vectors equal the original algebraic core. Focused production/source consumers, expanded audit, all sixteen linters and sequential foundation/paper verification passed with zero diagnostics. Individual bad tensor factors and full all-real-type admissibility remain open; DUB-17 remains OPEN.'
v['validation']=f'1234 production modules; 594 exact consumers; 5447 explicit registrations; {count} exhaustive theorem checks; sixteen linters across {lint} declarations plus {gen} generated, in both executions. Logs: {foundation} and {paper}.'
f.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
for q in [p.parent/'README.md',p.parents[1]/'README.md']:
 s=q.read_text(encoding='utf8');s=s.replace('(focused compilation passed; expanded verification pending)', '(focused compilation, expanded audit, all sixteen linters and sequential foundation/paper verification passed with zero diagnostics)');q.write_text(s,encoding='utf8')
print(f'1234-module verification recorded; {count} exhaustive checks; {lint}+{gen} linter declarations; 16/20 accepted.')
