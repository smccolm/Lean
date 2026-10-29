from pathlib import Path
from datetime import datetime,timezone
import ast,hashlib,json,re
s=Path(__file__).parent;sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
versions=json.loads((s/'integral-trace-versions-1531.json').read_text(encoding='utf-8'))
mods=list(versions);ths=[];defs=[]
for m in mods:
 code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',(s/(m+'.lean')).read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',code,re.M)[1]+'.'
 ths += [ns+x for x in re.findall(r'^theorem\s+([\w.\x27]+)',code,re.M)]
 defs += [ns+x for x in re.findall(r'^def\s+([\w.\x27]+)',code,re.M)]
ns='Dubon2026.SourceFunctionField.'
roots=[ns+'IntegralTrace.even_weight_slash_coeff_mem_of_peaked_auxiliary',ns+'GammaOne.exists_even_integral_ratio_of_original_field']
edges=ths+defs+[ns+'GammaOne.mem_qExpFunctionFieldC_iff',ns+'GammaOne.mem_plusMinus_iff',
 ns+'exists_levelOne_j_polynomial',ns+'qExpansion_E4_eq_map_eisenstein4',
 'Dubon2026.SourceFricke.eisensteinQSeries_six_eq_integer_map',
 'Dubon2026.SourceFricke.eisensteinQSeries_map','Dubon2026.SourceFricke.qExpansion_coeff_width',
 'Dubon2026.hasSum_pow_dvd_reindex','UpperHalfPlane.qExpansion_coeff_eq_intervalIntegral',
 'UpperHalfPlane.qExpansion_coeff_unique']
assert len(mods)==21 and len(set(ths))==len(ths) and len(set(edges))==len(edges)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=roots,proofEdges=edges,
 localModules=mods,separatelyAxiomChecked=[],compileEvidence={m:m+'-1531' for m in mods})
def write(n,c):
 f=s/n;assert not f.exists(),f;f.write_text(c,encoding='utf-8')
stem='source-integral-trace-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old,new='SourceGammaOneIntegralEisenstein','SourceIntegralTrace'
for a,b in [('Audit1','Audit1'),('DependencyAudit1','DependencyAudit1'),('ScratchOwnership1501','ScratchOwnership1532')]:
 c=(s/(old+a+'.lean')).read_text(encoding='utf-8')
 c='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+c[c.index('\nopen Lean'):]
 if a=='Audit1':
  c=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in cfg['queries']),c,count=1)
  for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
  c=re.sub(r'#lint in [^\n]+\n','',c).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
 elif a=='DependencyAudit1':
  for k,v in [('roots',roots),('localModules',mods),('required',edges)]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
  start=c.index(' occur in the ');end=c.index('; DUB17--20 OPEN.',start)
  c=c[:start]+' occur in the proof value closure of the actual even-weight peaked-auxiliary trace theorem and the original-field even-ratio reduction. Trace construction, Fourier decomposition, coefficient vanishing and extraction are derived. Peaked auxiliary existence, level-power slash integrality, degree/genus preservation and parabolic transfer remain open'+c[end:]
 else:c=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),c)
 c=c.replace('GAMMA ONE INTEGRAL EISENSTEIN','INTEGRAL TRACE')
 write(new+b+'.lean',c)
sources=[]
for d in ['anthropic-even-integrality-depth-1503','anthropic-series-coefficient-depth-1507','anthropic-trace-dependencies-1510','anthropic-trace-width-1517']:
 rows=json.loads((s/d/'fetch-manifest.json').read_text(encoding='utf-8'))['files']
 for row in rows:
  f=Path(row['local']);assert sha(f)==row['sha256']
  txt=f.read_text(encoding='utf-8');clean=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',txt,flags=re.S))
  sources.append(dict(**row,lexicalMatches=re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by)\b',clean),nondefaultOptions=[dict(line=i,text=l) for i,l in enumerate(txt.splitlines(),1) if re.search(r'set_option\s+(?:linter\.|maxHeartbeats|synthInstance\.maxHeartbeats|maxRecDepth)',l)]))
assert len(sources)==9
deep='integral-trace-dependency-review-1532.json'
write(deep,json.dumps(dict(recordedUTC=datetime.now(timezone.utc).isoformat(),revision='6e837e75355538c7f80bab5b956861e86c4eacc2',files=sources,externalBuild=False,externalImport=False,scope='Nine additional exact source files inspected for the even-weight trace and peaked auxiliary construction. No external import or transitive upstream kernel audit claimed.'),indent=2)+'\n')
report='Dubon Even Weight Integral Trace Assessment 2026-10-28.md'
write(report,'''# Even-weight integral trace assessment — 28 October 2026

The exact dependency is DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 → literal higher symmetric-power continuation → arithmetic automorphy → original all-weight characteristic-zero association → original Gamma1 Tate/Frobenius realization → actual coordinate-degree and genus preservation → the signed-index lower bound → the reduced field action → level-power slash integrality. This scope proves its peaked auxiliary trace argument. Acceptance remains 16/20; DUB-17–20 OPEN.

Every original integral-ratio generator f/g is now proved to equal (f*g)/(g*g), with integral expansions, nonzero denominator and even weight. The existing actual-field membership theorem gives this representation for every element of the original rational Gamma1 field. This proves that the odd-weight auxiliary branch can be omitted for this route; the original field and its elements are unchanged.

For an actual even-weight modular form and a separately specified peaked auxiliary form, the new endpoint derives integrality of each S-slash Fourier coefficient in the chosen subring of C. It constructs a signed coset transversal containing the translation terms and S, constructs the actual level-one trace, proves its three-part Fourier decomposition, derives the remainder's coefficient vanishing from exponential decay, and recovers the requested coefficient using the auxiliary leading unit. The peaked form's existence, its integral expansions, leading unit, order gap and decay are still explicit upstream inputs. The endpoint neither assumes slash integrality nor proves the missing existence input.

The shorter native route reuses the existing j-polynomial representation for the finite coefficient criterion, the proved integral E4 and E6 expansions for weight adjustment, the native signed subgroup, the original width-one Fourier comparison and sparse-series reindexing. A positive base-width extension handles the minimal cusp period. The coincident-cusp case reduces directly to equality with the original even-weight form, avoiding the general upstream odd-weight argument. No new graded-ring classification, Bernoulli calculation, substitute modular field, arbitrary function wrapper, proof-limit increase or linter suppression is introduced.

The pinned primary sources are the [peaked auxiliary trace](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularForm_qExpansion_slash_coeff_mem_of_peaked_auxiliary.lean), [even-weight auxiliary construction](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_SiegelUnit_exists_gamma1_peaked_auxiliary_form_twelve_dvd.lean), and [finite level-one coefficient criterion](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularForm_levelOne_qExpansion_coeff_mem_of_coeff_le_mem.lean). Nine additional inert source texts and their hashes are recorded in integral-trace-dependency-review-1532.json. The unchanged Apache-2.0 revision is inspected source evidence; no external build, direct import or full upstream dependency audit is claimed.

All 21 versioned modules compile without diagnostics. Canonical scratch compilation, exhaustive private/generated axiom checks, sixteen linters per module, proof-value dependency checks and ownership checks are recorded separately as they finish. This report makes no production verification claim for the new scope. Bodies and comments are frozen after canonical scratch preparation; only imports may be qualified on promotion.

The remaining integrality chain needs the actual peaked auxiliary form, the existing bounded-denominator comparison and uniform level-power denominator control, then the complete reduced field action. The signed-index lower bound, actual residue degree equality, genus preservation (including residue characteristics two and three), finite-modulus integral parabolic transfer, the required two-dimensional characteristic-zero realization, remaining local/image/regularity inputs, automorphy and literal higher continuation remain required. No acceptance condition or root pin changes.
''')
src=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
reuse=[src/(n+'.lean') for n in ['SourceGammaOneRatioClosure','SourceGammaOnePlusMinus','SourceLevelOneJPolynomial','SourceIntegralEisensteinSix','SourceQExpansionPeriodWidth','ModularCoefficientOrder']]+[s/'integral-slash-dependency-review-1501.json',s/deep,s/report]
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> original Gamma1 Tate/Frobenius realization -> degree/genus preservation -> signed-index lower bound -> reduced field action -> level-power slash integrality -> even-weight peaked auxiliary trace.',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],shorterRoute='Reduce actual integral ratios to even weight; reuse native j-polynomial, integral E4/E6, signed subgroup and sparse Fourier reindexing. Prove the coincident-cusp case by equality with the original even-weight form. Split the actual trace assembly without increasing proof limits.',assumptionsToDischarge=['Every original field element has an integral even-weight ratio representation.','The first finitely many coefficients determine subring membership of all coefficients of the actual level-one trace.','A prescribed signed cusp transversal exists and constructs an actual level-one trace.','The original expansions imply integral translation-sum coefficients and exact trace decomposition.','Auxiliary exponential decay implies the required vanishing Fourier coefficients.','The separate peaked auxiliary hypotheses imply integrality of the actual even-weight S-slash coefficients.'],remaining='Peaked auxiliary existence and its source hypotheses remain explicit. Level-power slash integrality, the full reduced field action, signed-index lower bound, degree/genus preservation, finite-modulus parabolic transfer, the required two-dimensional characteristic-zero realization, remaining local/image/regularity inputs, automorphy and literal higher continuation remain. Acceptance stays 16/20; DUB-17--20 OPEN.',externalBuild=False,externalImport=False,rootPinsChanged=False,proofLimitsChanged=False)
rf='source-integral-trace-audit-route-1532.json';write(rf,json.dumps(route,indent=2)+'\n')
c=(s/'record_gamma_one_integral_eisenstein_1501.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-integral-eisenstein-audit-route-1501',rf[:-5]),('source-gamma-one-integral-eisenstein-1',stem),(old,new),('ScratchOwnership1501','ScratchOwnership1532'),('GAMMA ONE INTEGRAL EISENSTEIN','INTEGRAL TRACE')]:c=c.replace(a,b)
nm,nq,ne=len(mods),len(cfg['queries']),len(edges)
c=c.replace('(9, 36, 42)',str((nm,nq,ne))).replace('modules=9',f'modules={nm}').replace('queries=36',f'queries={nq}').replace('linterScopes=9',f'linterScopes={nm}').replace("text.count('with 16 linters') == 9",f"text.count('with 16 linters') == {nm}").replace('all 42 required',f'all {ne} required').replace('requiredProofValueEdges=42',f'requiredProofValueEdges={ne}').replace('proofEdges=42',f'proofEdges={ne}')
ast.parse(c);write('record_integral_trace_1532.py',c)
c=(s/'audit_gamma_one_integral_eisenstein_1501.ps1').read_text(encoding='utf-8-sig')
for a,b in [(old,new),('ScratchOwnership1501','ScratchOwnership1532'),('record_gamma_one_integral_eisenstein_1501','record_integral_trace_1532')]:c=c.replace(a,b)
write('audit_integral_trace_1532.ps1',c)
print(json.dumps(dict(modules=nm,theorems=len(ths),constructions=len(defs),queries=nq,proofEdges=ne,additionalPinnedSources=len(sources))))
