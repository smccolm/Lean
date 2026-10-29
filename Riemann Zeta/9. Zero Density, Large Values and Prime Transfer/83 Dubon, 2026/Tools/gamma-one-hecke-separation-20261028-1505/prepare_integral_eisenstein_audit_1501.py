from pathlib import Path
from datetime import datetime,timezone
import ast,hashlib,json,re
s=Path(__file__).parent;sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
versions=json.loads((s/'gamma-one-integral-eisenstein-versions-1500.json').read_text(encoding='utf-8'))
mods=list(versions);ths=[];defs=[]
for m in mods:
 code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',(s/(m+'.lean')).read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',code,re.M)[1]+'.'
 ths += [ns+x for x in re.findall(r'^theorem\s+([\w.\x27]+)',code,re.M)]
 defs += [ns+x for x in re.findall(r'^def\s+([\w.\x27]+)',code,re.M)]
gn='Dubon2026.SourceFunctionField.GammaOne.';ns=gn+'IntegralEisenstein.'
roots=[ns+n for n in ['ratio_mem_original_field','ratio_separates_signed_identity','normalizedForm_slash']]
separate=[ns+'gammaOneRowSum_coe']
edges=[n for n in ths if n not in separate]+defs+['EisensteinSeries.qExpansion_identity_pnat',
'summable_prod_mul_pow','sigmaAntidiagonalEquivProd','ModularFormClass.qExpansion_coeff_unique',
gn+'div_mem_qExpFunctionFieldC','Dubon2026.SourceFunctionField.qExpansion_E4_eq_map_eisenstein4',
'Dubon2026.SourceFricke.gammaOne_one_mem_strictPeriods']
assert (len(mods),len(ths),len(defs),len(edges))==(9,24,12,42)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=roots,proofEdges=edges,
localModules=mods,separatelyAxiomChecked=separate,compileEvidence={m:m+'-1500' for m in mods})
def write(n,c):
 f=s/n;assert not f.exists(),f;f.write_text(c,encoding='utf-8')
stem='source-gamma-one-integral-eisenstein-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old,new='SourceGammaOneIntegralRatio','SourceGammaOneIntegralEisenstein'
for a,b in [('Audit1','Audit1'),('DependencyAudit1','DependencyAudit1'),('ScratchOwnership1481','ScratchOwnership1501')]:
 c=(s/(old+a+'.lean')).read_text(encoding='utf-8')
 c='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+c[c.index('\nopen Lean'):]
 if a=='Audit1':
  c=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in cfg['queries']),c,count=1)
  for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
  c=re.sub(r'#lint in [^\n]+\n','',c).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
 elif a=='DependencyAudit1':
  for k,v in [('roots',roots),('localModules',mods),('required',edges)]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
  start=c.index(' occur in the ');end=c.index('; DUB17--20 OPEN.',start)
  c=c[:start]+' occur in the proof value closure of actual integral Gamma1 Eisenstein ratios, their slash transformation and all-characteristic separation of the signed identity diamond class. The field action, degree/genus preservation and parabolic transfer remain open'+c[end:]
 else:c=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),c)
 c=c.replace('GAMMA ONE INTEGRAL RATIO','GAMMA ONE INTEGRAL EISENSTEIN')
 write(new+b+'.lean',c)
sources=[]
for d in ['anthropic-integral-slash-depth-1495','anthropic-fricke-integrality-depth-1496','anthropic-peaked-integrality-depth-1498']:
 manifest=s/d/'fetch-manifest.json';rows=json.loads(manifest.read_text(encoding='utf-8'))['files']
 for row in rows:
  f=Path(row['local']);assert sha(f)==row['sha256']
  text=f.read_text(encoding='utf-8');clean=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',text,flags=re.S))
  sources.append(dict(**row,lexicalMatches=re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by)\b',clean),nondefaultOptions=[dict(line=i,text=l) for i,l in enumerate(text.splitlines(),1) if re.search(r'set_option\s+(?:linter\.|maxHeartbeats|synthInstance\.maxHeartbeats|maxRecDepth)',l)]))
assert len(sources)==5
deep='integral-slash-dependency-review-1501.json'
write(deep,json.dumps(dict(recordedUTC=datetime.now(timezone.utc).isoformat(),revision='6e837e75355538c7f80bab5b956861e86c4eacc2',files=sources,externalBuild=False,externalImport=False,scope='Exact five-file upstream slash-integrality chain; supplied source proof bodies inspected, no transitive upstream kernel audit claimed.'),indent=2)+'\n')
report='Dubon Integral Eisenstein Reuse Assessment 2026-10-28.md'
write(report,'''# Integral Eisenstein reuse assessment — 28 October 2026

The exact dependency is DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 → literal higher symmetric-power continuation → automorphy → original all-weight characteristic-zero association → original Gamma1 Tate/Frobenius realization → original coordinate-degree and genus preservation. This scope constructs the integral separating functions needed by the signed-index lower bound. Acceptance remains 16/20; DUB-17–20 OPEN.

The nine versioned native modules compile with zero diagnostics. They construct actual weight-four congruence lattice sums, prove holomorphicity and cusp boundedness, sum the second residue classes to obtain Gamma1 modular forms, and prove their Gamma0 slash transformation. The Fourier argument reuses Mathlib's Lipschitz identity and its absolutely convergent divisor-product series. Summing the second residue class first avoids the external general additive-character expansion. The normalization is the literal nonzero factor (-2πi)^4/3!.

The resulting Fourier coefficients are integers, with constant coefficient zero and first coefficient [1=c]+[1=-c]. Dividing by the original E4 gives actual elements of the original integral-ratio field over every coefficient field. For N>2, the identity signed diamond class has first coefficient one, while each class other than ±1 has coefficient zero. These functions remain distinct after reduction in every characteristic, including two and three. This specializes the general GammaH argument to Gamma1 and avoids its coset averaging. Levels one and two, the field action and index comparison remain separate obligations.

The exact native reuse includes the existing Gamma1 period, original integral-ratio membership theorem, E4 expansion and Mathlib Fourier-coefficient uniqueness. Neither degree nor genus equality is assumed in these new constructions. The separate four-module comparison scope already passes exhaustive scratch, linter, ownership and proof-value audits; it connects the integral-ratio field to the actual native residue field and consumes precisely the still-unproved signed-index lower bound.

The deeper source check qualifies the earlier promising-route assessment: the upstream action on the entire integral-ratio field still requires level-power slash integrality. Its proof passes through Fricke integrality, a trace argument with a peaked auxiliary modular form, and Siegel-unit constructions. Thus the degree route does not eliminate the need to prove or rigorously replace this integrality input. The individual Eisenstein forms have integral slash transforms directly, but that alone does not establish an action on all reduced rational relations. The native diamond action that already assumes degree equality cannot be used here.

Five additional pinned proof texts are recorded in integral-slash-dependency-review-1501.json, supplementing the 29-file targeted review. The relevant primary sources are [all-cusp slash integrality](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_coeff.lean), [Fricke integrality](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_fricke_coeff.lean), and [the peaked auxiliary form](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_gamma1_peaked_auxiliary_form.lean). The unchanged upstream revision is Apache-2.0. These texts remain inert; no upstream build, direct import or transitive audit is claimed. Upstream raised limits and suppressed linters are not adopted.

Canonical scratch checks, proof-value dependency evidence and exact ownership are recorded separately as they finish. This assessment claims no assembled production PASS for the new scope. Degree/genus preservation, finite-modulus integral parabolic transfer, the two-dimensional characteristic-zero realization, remaining local/image/regularity inputs, automorphy and literal higher continuation remain required under the unchanged source contract.
''')
src=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
reuse=[src/(n+'.lean') for n in ['SourceGammaOneFourierLinear','SourceGammaOneFunctionField','SourceGammaOneJCoordinate','SourceGammaOneRationalBoundedDenominators','SourceGammaOneAnalyticIntegrality']]+[s/'targeted-reuse-review-1471.json',s/deep,s/report]
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher continuation -> automorphy -> original all-weight characteristic-zero association -> original Gamma1 Tate/Frobenius arithmetic realization -> exact degree/genus preservation -> signed-index lower bound -> integral Eisenstein diamond separation.',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],shorterRoute='Specialize to weight four and Gamma1. Sum second residue classes before the Fourier calculation, reuse native Lipschitz and divisor-product identities, and separate individual signed diamond classes using E_c/E4. No general additive-character Fourier formula or GammaH coset averaging is needed. The still-open field-action integrality chain is documented explicitly.',assumptionsToDischarge=['Existence of actual holomorphic cusp-bounded weight-four congruence lattice forms.','Exact Gamma0 slash transformation of the actual Gamma1 row-sum forms.','Integral Fourier coefficients for their literal Lipschitz normalization.','Membership of E_c/E4 in the actual integral-ratio field over every field.','Separation of the identity signed diamond class for N>2 after reduction in every characteristic.'],remaining='Level-power slash integrality or a rigorous replacement is still needed for the full reduced field action. Signed-index degree lower bound, degree/genus preservation, finite-modulus parabolic transfer, required two-dimensional characteristic-zero realization, remaining local/image/regularity inputs, automorphy and literal higher continuation remain. Acceptance stays 16/20; DUB-17--20 OPEN.',externalBuild=False,externalImport=False,rootPinsChanged=False,proofLimitsChanged=False)
rf='source-gamma-one-integral-eisenstein-audit-route-1501.json';write(rf,json.dumps(route,indent=2)+'\n')
c=(s/'record_gamma_one_integral_ratio_1481.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-integral-ratio-audit-route-1481',rf[:-5]),('source-gamma-one-integral-ratio-1',stem),(old,new),('ScratchOwnership1481','ScratchOwnership1501'),('GAMMA ONE INTEGRAL RATIO','GAMMA ONE INTEGRAL EISENSTEIN')]:c=c.replace(a,b)
c=c.replace('(4, 7, 20)','(9, 36, 42)').replace('modules=4','modules=9').replace('queries=7','queries=36').replace('linterScopes=4','linterScopes=9').replace("text.count('with 16 linters') == 4","text.count('with 16 linters') == 9").replace('all 20 required','all 42 required').replace('requiredProofValueEdges=20','requiredProofValueEdges=42').replace('proofEdges=20','proofEdges=42')
ast.parse(c);write('record_gamma_one_integral_eisenstein_1501.py',c)
c=(s/'audit_gamma_one_integral_ratio_1481.ps1').read_text(encoding='utf-8-sig')
for a,b in [(old,new),('ScratchOwnership1481','ScratchOwnership1501'),('record_gamma_one_integral_ratio_1481','record_gamma_one_integral_eisenstein_1501')]:c=c.replace(a,b)
write('audit_gamma_one_integral_eisenstein_1501.ps1',c)
print(json.dumps(dict(modules=len(mods),queries=len(cfg['queries']),proofEdges=len(edges),additionalPinnedSources=len(sources))))
