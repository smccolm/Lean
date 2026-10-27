from pathlib import Path
import json,re,hashlib,ast
p=Path(r'E:\Lean\.tmp\dubon83')
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
ns='Dubon2026.SourceFunctionField.GammaOne.'
mods=['SourceGammaOneCuspCyclicOrbit','SourceGammaOneCuspCosetPlaces','SourceGammaOneCuspCosetBound','SourceGammaOneCuspPoleDegree','SourceGammaOneCuspPositiveWeight','SourceGammaOneCuspOrbitBijection','SourceGammaOneExactCuspOrbits']
ths=[];defs=[]
for m in mods:
 code=re.sub(r'/\-.*?\-/','',(p/(m+'.lean')).read_text(encoding='utf-8'),flags=re.S)
 for kind,n in re.findall(r'^(theorem|def|abbrev) (\w+)',code,re.M):
  prefix=ns if m in ['SourceGammaOneCuspPoleDegree','SourceGammaOneExactCuspOrbits'] or n=='cuspPlace_mul_left_plusMinus' else ns+'CuspCounting.'
  (ths if kind=='theorem' else defs).append(prefix+n)
queries=ths+defs
required=queries+[ns+'j_pole_order_le_positive_translation',ns+'exists_cusp_place_eq_of_j_pole','Dubon2026.SourceCurve.sum_positive_orders_eq_finrank_adjoin',ns+'finrank_over_j_eq_index','Subgroup.pow_index_mem','MulAction.orbitEquivQuotientStabilizer','MulAction.selfEquivSigmaOrbits']
assert (len(mods),len(ths),len(defs),len(queries),len(required))==(7,24,8,32,39)
closure=mods+['SourceGammaOneRationalCuspOrbit','SourceGammaOneCuspJExactOrder','SourceGammaOneCuspRotationOrder','SourceGammaOneCuspTranslationRamification','SourceGammaOneCuspPlaceLeftInvariance','SourceGammaOneCuspTranslations','SourceGammaOneCuspPlaceRightInvariance','SourceGammaOneRationalCuspPlace','SourceGammaOneCuspPlaceExhaustion','SourceGammaOneCuspBoundedRealization','SourceGammaOneCuspResidues']
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0;assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
def output(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=queries,proofEdges=required,roots=queries,separatelyAxiomChecked=[],scratchImportClosure=closure,separateReason='The actual Gamma1 cyclic coset-orbit map is bijective onto all original j-pole places, and every pole order equals the orbit size. Both elementary subgroup hypotheses are derived for every nonzero level. Real period dimension and arithmetic comparison remain.')
output('source-gamma-one-exact-cusp-orbits-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneExactRamificationAudit1.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b.replace('SOURCE GAMMA ONE EXACT RAMIFICATION','SOURCE GAMMA ONE EXACT CUSP ORBITS').replace('Gamma One Exact Ramification','Gamma One Exact Cusp Orbits')
output('SourceGammaOneExactCuspOrbitsAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in queries)+'\n'+b+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneExactRamificationDependencyAudit1.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,v in [('roots',queries),('localModules',closure),('required',required)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b[:b.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE EXACT CUSP ORBITS DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual Gamma1 cyclic coset-orbit bijection and exact j-pole orders. Only declaration values are traversed. The real period dimension inequality, surjectivity, reciprocity, original arithmetic comparison and higher continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneExactCuspOrbitsDependencyAudit1.lean',imports+b)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
files=[r/'SourceOriginalOrbitFiberBijection.lean',r/'SourceGammaOneExactRamification.lean',r/'SourceCurveTranscendentalDegree.lean',p/'gamma-one-cusp-width-bound-route-766.json',p/'source-gamma-one-cusp-width-bound-1-scratch-receipt.json']
rd=dict(chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> original all-weight arithmetic association -> actual Gamma1 Hecke-character realization -> Picard/H1 and Abel-Jacobi -> real period surjectivity -> matching Manin/genus cusp terms -> actual cusp-orbit bijection and orders.',assumptionsToDischarge='Native cyclic orbit-stabilizer and power-index theorems make each finite orbit cardinality a positive signed stabilizer translation. The proved algebraic cusp pole bound applies. Orbit decomposition sums these sizes to the subgroup index. The original field degree and inverse-coordinate positive-order theorem independently sum all actual j-pole orders to that same index. Surjectivity and positive weights then prove injectivity and exact equality term by term. The exported actual Gamma1 map derives congruence containment and translation membership for every nonzero level; no bijection, count, width or field-degree premise remains.',remaining='Adapt the exact Manin real parabolic dimension bound to the central-sign enlargement of Gamma1 and assemble the actual Hurwitz/genus bound from the proved finite and cusp fiber formulas. Real period surjectivity, reciprocity, Picard/Hecke/diamond/H1, original all-weight characteristic-zero association and higher continuation remain. 16/20; DUB-17--20 OPEN.',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in files],shorterRoute='Use the native cyclic orbit power-index return time instead of developing minimal-period coordinates. Reuse the original positive-weight finite-fiber argument with the already proved upper bound and exact total degree. Original Gamma1 function fields and all nonzero levels are retained.')
output('gamma-one-exact-cusp-orbits-audit-route-774.json',json.dumps(rd,indent=2)+'\n')
s=(p/'record_gamma_one_cusp_width_bound_767b.py').read_text(encoding='utf-8-sig')
for a,b in [('source-gamma-one-cusp-width-bound-1','source-gamma-one-exact-cusp-orbits-1'),('SourceGammaOneCuspWidthBoundAudit1b','SourceGammaOneExactCuspOrbitsAudit1'),('SourceGammaOneCuspWidthBoundDependencyAudit1','SourceGammaOneExactCuspOrbitsDependencyAudit1'),('SOURCE GAMMA ONE CUSP WIDTH BOUND','SOURCE GAMMA ONE EXACT CUSP ORBITS'),('gamma-one-cusp-width-bound-audit-route-767.json','gamma-one-exact-cusp-orbits-audit-route-774.json'),('(4, 21, 29)','(7, 32, 39)'),('all 29 required','all 39 required'),('requiredProofValueEdges=29','requiredProofValueEdges=39'),('modules=4, queries=21','modules=7, queries=32'),('proofEdges=29','proofEdges=39'),('== 4','== 7'),('linterScopes=4','linterScopes=7')]:
 assert a in s,a;s=s.replace(a,b)
ast.parse(s);output('record_gamma_one_exact_cusp_orbits_774.py',s)
s=(p/'SourceGammaOneExactRamificationScratchOwnership731.lean').read_text(encoding='utf-8-sig').replace('import SourceGammaOneExactRamification',''.join('import '+m+'\n' for m in mods).rstrip()).replace('#[`SourceGammaOneExactRamification]',arr(mods))
output('SourceGammaOneExactCuspOrbitsScratchOwnership774.lean',s)
print(json.dumps(dict(modules=7,queries=32,edges=39)))
