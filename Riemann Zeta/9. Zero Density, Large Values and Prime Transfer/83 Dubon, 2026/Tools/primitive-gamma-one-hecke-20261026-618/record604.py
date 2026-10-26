from pathlib import Path
import hashlib,json,re
p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026')
d=Path('E:/Lean/.tmp/dubon83')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
foundation='../../logs/foundation_freeze_20261007_125753.log'
paper='logs/dubon-build-20261007-130116-232.log'
assert 'FINAL RESULT: PASS' in (p/foundation).read_text(encoding='utf-8-sig')
ps=(p/paper).read_text(encoding='utf-8-sig')
assert 'DEVELOPMENT PASS - IMPLEMENTED SCOPE VERIFIED; 15/20' in ps
checks=re.findall(r'AUDIT PASS: (\d+) project theorems.*?; (\d+) registered consumers',ps)
lints=re.findall(r'Found 0 errors in (\d+) declarations \(plus (\d+) automatically generated ones\)',ps)
assert len(checks)==2 and all(x==('5046','2838') for x in checks),checks
assert len(lints)==2 and all(x==('3371','2285') for x in lints),lints
c=json.loads((p/'Tools/scaffold.json').read_text(encoding='utf8'))
g=json.loads((p/'Tools/proof_gates.json').read_text(encoding='utf8'))
gate=next(x for x in g['gates'] if x['id']=='DUB-16')
assert len(c['productionModules'])==604 and c['proofGatesComplete']==15 and gate['status']=='OPEN'
acceptance='DUB-16 is accepted after exact source review and sequential verification on 7 October 2026. DUB-01–16 are DONE; DUB-17–20 remain OPEN.'
for name in c['statusDocuments']:
 f=p/name;s=f.read_text(encoding='utf8')
 a='Focused production compilation passed; source-consumer compilation, expanded audit, all sixteen linters and sequential foundation/paper verification are pending.'
 b='Focused compilation, all sixteen linters, the expanded dependency audit and sequential foundation/paper verification passed with zero Lean diagnostics (5,046 exhaustive theorem checks).'
 assert a in s,name;s=s.replace(a,b)
 s=s.replace('DUB-16 source acceptance is pending those checks; DUB-01–15 remain accepted and DUB-16–20 remain OPEN.',acceptance)
 s=s.replace('DUB-16 acceptance remains pending expanded auditing and sequential verification.',acceptance)
 lines=s.splitlines()
 for i,l in enumerate(lines):
  if l.startswith('**GOAL ACTIVE'):
   l=l.replace('15/20','16/20').replace('DUB-01–15','DUB-01–16').replace('DUB-16–20','DUB-17–20')
   l=l.replace('Seven source gates are accepted, with separate semantic records.','Sixteen source gates are accepted, with separate semantic records.')
   if name=='Dubon Checklist.md':l='**GOAL ACTIVE — 16/20 proof gates complete.** DUB-01–16 are accepted at their exact source contracts. Deligne, non-CM Sato–Tate, the unconditional modular application and final integration/release acceptance remain open.'
   lines[i]=l
 s='\n'.join(lines)+'\n'
 s=s.replace('The preceding verified scope had 590 production modules, 228 exact consumers, 2,784 explicit audit registrations and 4,944 exhaustive theorem dependency checks; the current expanded scope is identified above.', 'The current verified scope has 604 production modules, 233 exact consumers, 2,838 explicit audit registrations and 5,046 exhaustive theorem dependency checks.')
 if name=='Dubon Reproduction Manifest.md':
  s=s.replace('The modular concentration application still requires the true Rankin–Selberg, Deligne, Sato–Tate and automorphic inputs. DUB-01–15 have separate source-acceptance records; DUB-16–20 remain OPEN pending their own complete review and acceptance.', 'The general-level Rankin–Selberg theorem and weighted energy are proved and accepted. The modular concentration application still requires Deligne, Sato–Tate and the automorphic inputs. DUB-01–16 have separate source-acceptance records; DUB-17–20 remain OPEN pending their own complete review and acceptance.')
 if name=='Dubon Architecture.md':s=s.replace('G16["DUB-16 OPEN','G16["DUB-16 DONE')
 if name=='Dubon Checklist.md':
  start=s.index('## DUB-16 —');end=s.index('## DUB-17 —',start)
  section=s[start:end].replace('- [ ] **OPEN**','- [x] **DONE**')
  section=section[:section.index('`WeightedEnergyAbel`')]+('`GeneralRankinSelberg.general_rankin_selberg` proves the genuine positive residue and exact three-fifths square-sum remainder for every nonzero cusp form of weight at least two and every positive level. `ModularEnergy.general_cusp_weighted_rankin_selberg` consumes that proved input for all three weighted regimes; explicit theorems and exact consumers include sigma=0, 3/10 and 1/2. The acceptance record unfolds the actual coefficients, contour/dual-series chain and weighted conclusions. Dependencies: DUB-15. Source anchors: `lem:modular-energy`.\n\n')
  s=s[:start]+section+s[end:]
 f.write_text(s,encoding='utf8')
receipt='''
### General-level Rankin–Selberg and DUB-16 acceptance — 7 October 2026

Foundation `cmd /c run_lake_build.bat --no-pause` returned **PASS, exit 0**, followed sequentially by paper `cmd /c run_dubon_build.bat --no-pause`, **DEVELOPMENT PASS, exit 0**, with zero Lean diagnostics. Coverage: 604 production modules, 233 exact source consumers, 2,838 explicit registrations and 5,046 exhaustive theorem dependency checks. All sixteen linters passed across 3,371 declarations plus 2,285 generated declarations in both audit executions. The initial inventory passed with 711 retained files, 997 local links and 4,320 unchanged existing Lean files; source pins and all tooling fixtures passed.

The exact general-level Rankin–Selberg theorem has the actual positive Petersson residue and uniform three-fifths error for the original normalized cusp coefficients. Five exact consumers expose the signed finite reflected series, the two-pole Riesz identity, the literal original square sum and all weighted energy regimes and transition cases. DUB-16 was accepted after checking these source conclusions against frozen TeX lines 1534–1605, without altering any acceptance clause or source byte. No Lean source, import, dependency, audit or runner changed during this acceptance step. Thus the pre-acceptance log correctly records 15/20 gates at execution; acceptance metadata now records 16/20 and is checked separately by the inventory verifier. DUB-17–20 remain OPEN.

Dirty checkout `abbed66648e1ae22078cccafc224dd68e108f54d`; Lean 4.30.0, Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`, PNT+ `4ecb950126c4290293c5662dfe0e884123171df5`. Frozen TeX SHA-256 `605d02ea28f553ae3206cf3e0c176c93840d0a985b654d1b520b638e0a4ec08b`; PDF `a9cac7a820cc2c8b0965eb9caa4eb0eaa6e3159321a90e4e43960cbe764597f2`. Research cutoff remains 6 October; implementation and verification occurred on 7 October. ELAN_HOME was inferred from the installed Lake command. No staging, commit or push occurred.

'''
shared=[foundation,foundation[:-4]+'.json',paper,'Tools/verify_scaffold.py','Tools/test_scaffold.py','Tools/run_dubon_verification.ps1','Extension/Dubon2026/Audit.lean','Extension/Dubon2026/SemanticRegression.lean','Extension/Dubon2026.lean','Extension/lakefile.toml','Extension/lake-manifest.json','Extension/lean-toolchain']
for name in shared:
 receipt+=f'- [{Path(name).name}]({name}), SHA-256 `{sha(p/name)}`.\n'
for name in json.loads((d/'modules604.json').read_text(encoding='utf8'))+['RankinStripNormalized','RankinStripPhragmenLindelof','RankinPerronContinuation','RankinPerronHorizontal','RankinPerronContourShift']:
 rel=f'Extension/Dubon2026/{name}.lean';receipt+=f'- `{rel}`: SHA-256 `{sha(p/rel)}`.\n'
receipt+='\nOwner BAT SHA-256 `'+sha(p/'push_to_github.bat')+'` (unchanged; not executed).\n'
with (p/'Dubon Reproduction Manifest.md').open('a',encoding='utf8') as out:out.write('\n'+receipt)
semantic='''
## DUB-16 — Actual general-level Rankin–Selberg and weighted energy

**DONE after the 604-module sequential verification on 7 October 2026.** The acceptance clause is unchanged. The frozen source at lines 1534–1605 uses actual normalized Fourier coefficients of a primitive non-CM eigenform of even weight k>=2, positive level and trivial character. The public theorem `general_rankin_selberg` proves a stronger result for every nonzero actual cusp form at every positive level and every integer weight k>=2. It uses the same genuine period-one q-expansion and normalization lambda_f(n)=a_f(n)n^(-(k-1)/2). Primitive normalization implies nonzero; no source form is excluded.

- **Actual input and positive constant.** `cuspRankinResidue` is the proved Petersson-integral residue, not a freely supplied main-term constant. Its positivity follows from nonvanishing of the actual cusp form. `general_rankin_selberg_source` exposes the literal finite sum over 1<=n<=floor(x), a form-dependent uniform constant for all real x>=1, the actual positive residue and the exact O_f(x^(3/5)) assertion.
- **Genuine general-level reflection.** The completed Gamma0 lattice/Petersson integral is unfolded and reflected into its actual finite divisor family. `general_rankin_riesz_reflection_source` expands the signed Mobius amplitudes and positive conductors. The dual coefficients come from actual rescaled q-expansions; their reality, nonnegativity, linear mean and absolute convergence are proved. No scalar general-level functional equation is assumed.
- **Contour and infinite sums.** The numerator is entire with the genuine two pole residues removed. The true reflected coefficients give the left boundary bound; the generalized strip argument controls the whole rectangle and makes both horizontal edges vanish. Finite vertical integrals are identified with actual coefficient-weighted Gamma cutoff series. A uniform summable majorant justifies the infinite-height interchange, and the finite signed divisor sum commutes with that limit. `general_rankin_riesz_dual_source` has the literal original Riesz sum, both residue terms and the actual dual coefficient series. No integral-value premise or formal interchange remains.
- **Sharp error and original coefficients.** Actual low/high coefficient power bounds and Gamma-kernel second differences give C_f x^(3/5), using the same natural floor cutoff at both forward/backward base points. Positivity is applied to the original Rankin convolution sequence; signed dual amplitudes are bounded by their norms. Positive Riesz unsmoothing gives the original convolution estimate. Genuine Mobius deconvolution and its convergent inverse series transfer exactly this error to the original normalized cusp squares and retain the genuine main term.
- **Every weighted source case.** `general_cusp_weighted_rankin_selberg` applies the proved uniform remainder to the exact Abel identity. It proves the asymptotic below 1/2 for every real sigma, bounded additive error at 1/2, and bounded nonnegative energy above 1/2. `general_cusp_weighted_energy_source` unfolds the actual finite norm-square sum. The error theorem retains the literal real integral with coefficient 2|sigma|. `general_cusp_weighted_energy_endpoints_source` explicitly supplies the three-fifths error at sigma=0 and the logarithmic transition at sigma=3/10. Neither the Rankin conclusion nor an energy certificate is a caller premise.

The existing DUB-15 object/normalization theorem supplies the actual source form. Every registered implementation module, all five new source consumers and all transitive theorem dependencies were included in both zero-diagnostic audit executions: 5,046 exhaustive theorems, 2,838 explicit registrations; all sixteen linters passed. The foundation and paper logs and shared source hashes are recorded in the corresponding reproduction receipt. Only documentary/gate metadata changed after verification. Deligne, non-CM Sato–Tate, the classical/automorphic bridge and the final unconditional modular conclusion remain separate DUB-17–20 obligations.

### Implementation hashes at DUB-16 acceptance

'''
for rel in gate['implementationFiles']:semantic+=f'- `{rel}`: SHA-256 `{sha(p/rel)}`.\n'
f=p/'Dubon Semantic Acceptance.md';s=f.read_text(encoding='utf8')
s=s.replace('DUB-16–20 remain OPEN. This file does not certify the complete paper.','DUB-16 is additionally accepted after exact source review and sequential verification on 7 October 2026. DUB-17–20 remain OPEN. This file does not certify the complete paper.',1)
f.write_text(s+'\n'+semantic,encoding='utf8')
gate['status']='DONE';gate['acceptedOn']='2026-10-07'
gate['evidence']=[{'record':'Dubon Semantic Acceptance.md','section':'DUB-16','foundationLog':foundation,'paperLog':paper,'verification':'Both exit 0; zero diagnostics. Exact general-level Rankin–Selberg and weighted energy source review recorded after the unchanged Lean scope passed.'}]
g['completed']=16;c['proofGatesComplete']=16
(p/'Tools/proof_gates.json').write_text(json.dumps(g,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
(p/'Tools/scaffold.json').write_text(json.dumps(c,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
f=p/'Tools/modular_research_20261006.json';j=json.loads(f.read_text(encoding='utf8'))
v=j['generalRankinSelbergImplementation20261007']
v['status']='Verified and source-accepted as DUB-16 on 7 October 2026; 16/20 gates accepted. Deligne, non-CM Sato–Tate and final unconditional modular concentration remain open.'
v['validation']='604 production modules; 233 exact consumers; 2838 explicit registrations; 5046 exhaustive theorem checks; sixteen linters across 3371 declarations plus 2285 generated, in both audit executions. Foundation 125753 and paper 130116-232 logs passed sequentially with zero diagnostics.'
f.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
print('604-module verification recorded; DUB-16 source acceptance recorded; 16/20 accepted.')
