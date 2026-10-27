from pathlib import Path
import json,re,hashlib,ast
p=Path(r'E:\Lean\.tmp\dubon83')
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
ns='Dubon2026.SourceFunctionField.GammaOne.'
mods=['SourceGammaOneCuspPlaceLeftInvariance','SourceGammaOneCuspTranslations','SourceGammaOneCuspPlaceRightInvariance','SourceGammaOneRationalCuspPlace']
ths=[ns+x for x in ['cuspRealize_mul_left_eventuallyEq','cuspOrder_mul_left','cuspPlace_mul_left','cuspFunction_vadd_eventuallyEq','cuspRealize_neg','cuspOrder_neg','cuspPlace_neg','translated_modular_T_zpow','cuspRealize_mul_T_zpow_eventuallyEq','cuspOrder_mul_T_zpow','cuspPlace_mul_T_zpow','exists_T_zpow_or_neg_of_lower_left','cuspPlace_eq_of_same_rational_cusp','cuspPlace_eq_of_rational_cusp_orbit']]
defs=[]; queries=ths
required=queries+[ns+x for x in ['functionFieldOver_modular_ratio','eventually_ne_zero_translated_cuspFunction','cuspRealize_eventuallyEq_of_ratio','CuspAuxiliary.natCast_mem_strictPeriods_conj']]+['Dubon2026.SourceParabolic.eq_T_zpow_of_col','Dubon2026.SourceManin.smul_infty_eq_iff']
assert len(queries)==14 and len(required)==20
closure=mods+['SourceGammaOneCuspResidues']
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0;assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
def output(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=queries,proofEdges=required,roots=queries,separatelyAxiomChecked=[],scratchImportClosure=closure,separateReason='Actual cusp places depend only on the rational cusp orbit; cusp widths, bijection and dimension comparison remain.')
output('source-gamma-one-cusp-orbit-invariance-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneExactRamificationAudit1.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b.replace('SOURCE GAMMA ONE EXACT RAMIFICATION','SOURCE GAMMA ONE CUSP ORBIT INVARIANCE').replace('Gamma One Exact Ramification','Gamma One Cusp Orbit Invariance')
output('SourceGammaOneCuspOrbitInvarianceAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in queries)+'\n'+b+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneExactRamificationDependencyAudit1.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,v in [('roots',queries),('localModules',closure),('required',required)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b[:b.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE CUSP ORBIT INVARIANCE DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual cusp-place invariance under subgroup multiplication and signed translations. Only declaration values are traversed. Exact widths, cusp bijection, real period surjectivity, reciprocity, original arithmetic comparison and higher continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneCuspOrbitInvarianceDependencyAudit1.lean',imports+b)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
files=[r/'SourceManinCuspStabilizer.lean',r/'SourceParabolicClassification.lean',r/'SourceGammaOneCuspAuxiliaryForm.lean',r/'CuspSparseLowering.lean',p/'gamma-one-cusp-period-dimension-route-759.json']
rd=dict(chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> original all-weight arithmetic association -> actual Gamma1 Hecke-character realization -> Picard/H1 and Abel-Jacobi -> real period surjectivity -> matching Manin/genus dimension bounds -> actual cusp-orbit/place comparison.',assumptionsToDischarge='Actual modular ratios and their translated cusp germs imply left subgroup invariance. Right integral translation rotates the cusp parameter by a nonzero scalar, preserving its meromorphic order and normalized valuation subring. The central sign fixes the upper half-plane. The existing integral cusp-stabilizer classification proves that the actual normalized place depends only on the rational cusp orbit; representative invariance is not assumed.',remaining='Exact widths and cusp-orbit/place bijection, the reverse dimension inequality, real period surjectivity, reciprocity, Picard/Hecke/diamond/H1 comparisons, full all-weight characteristic-zero association and higher continuation remain. 16/20; DUB-17--20 OPEN.',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in files],shorterRoute='Reuse the existing rational cusp stabilizer, integral parabolic classification, native cusp periodicity and meromorphic-order composition theorem. No new cusp uniformization or full-level Galois field is introduced.')
output('gamma-one-cusp-orbit-invariance-audit-route-762.json',json.dumps(rd,indent=2)+'\n')
s=(p/'record_gamma_one_real_parabolic_periods_758.py').read_text(encoding='utf-8-sig')
for a,b in [('source-gamma-one-real-parabolic-periods-1','source-gamma-one-cusp-orbit-invariance-1'),('SourceGammaOneRealParabolicPeriods','SourceGammaOneCuspOrbitInvariance'),('SOURCE GAMMA ONE REAL PARABOLIC PERIODS','SOURCE GAMMA ONE CUSP ORBIT INVARIANCE'),('gamma-one-real-parabolic-periods-audit-route-758.json','gamma-one-cusp-orbit-invariance-audit-route-762.json'),('(2, 11, 16)','(4, 14, 20)'),('all 16 required','all 20 required'),('requiredProofValueEdges=16','requiredProofValueEdges=20'),('modules=2, queries=11','modules=4, queries=14'),('proofEdges=16','proofEdges=20'),('== 2','== 4'),('linterScopes=2','linterScopes=4')]:
 assert a in s,a;s=s.replace(a,b)
ast.parse(s);output('record_gamma_one_cusp_orbit_invariance_762.py',s)
s=(p/'SourceGammaOneExactRamificationScratchOwnership731.lean').read_text(encoding='utf-8-sig').replace('import SourceGammaOneExactRamification',''.join('import '+m+'\n' for m in mods).rstrip()).replace('#[`SourceGammaOneExactRamification]',arr(mods))
output('SourceGammaOneCuspOrbitInvarianceScratchOwnership762.lean',s)
print(json.dumps(dict(modules=4,queries=14,edges=20)))
