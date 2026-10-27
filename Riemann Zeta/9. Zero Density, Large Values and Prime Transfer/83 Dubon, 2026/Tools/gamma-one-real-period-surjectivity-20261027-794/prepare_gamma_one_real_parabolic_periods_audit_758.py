from pathlib import Path
import json,re,hashlib,ast
p=Path(r'E:\Lean\.tmp\dubon83');r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026');ns='Dubon2026.'
mods=['SourceGammaOneRealPeriodMap','SourceGammaOneRealParabolicPeriods']
ths=[ns+x for x in ['sourceGamma1RealCharacter_finite','sourceGamma1RealPeriodHom_apply','sourceGamma1RealPeriodHom_injective','sourceGamma1CuspForm_finite_real','sourceGamma1_period_eq_zero_of_trace','sourceGamma1RealPeriodHom_parabolic','sourceGamma1RealParabolicPeriodHom_injective','sourceGamma1RealParabolicHoms_finite']]
defs=[ns+x for x in ['sourceGamma1RealPeriodHom','sourceGamma1RealParabolicHoms','sourceGamma1RealParabolicPeriodHom']]
queries=ths+defs
required=queries+[ns+x for x in ['sourceGamma1_real_periods_injective','sourceH1Finite','sourceWeightTwoPrimitive_period','sourceWeightTwoPrimitive_exists_cusp_limit','SourceParabolic.classification']]
assert len(queries)==11 and len(required)==16
closure=mods+['SourceGammaOneRealPeriodInjectivity','SourceGammaOneInvariantRealPart']
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0;assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
def output(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=queries,proofEdges=required,roots=queries,separatelyAxiomChecked=[],scratchImportClosure=closure,separateReason='Actual real Gamma1 periods give an injective map to the finite real parabolic character space. The upper dimension inequality and reciprocity remain.')
output('source-gamma-one-real-parabolic-periods-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneExactRamificationAudit1.lean').read_text(encoding='utf-8');b=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b.replace('SOURCE GAMMA ONE EXACT RAMIFICATION','SOURCE GAMMA ONE REAL PARABOLIC PERIODS').replace('Gamma One Exact Ramification','Gamma One Real Parabolic Periods')
output('SourceGammaOneRealParabolicPeriodsAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in queries)+'\n'+b+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneExactRamificationDependencyAudit1.lean').read_text(encoding='utf-8');b=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,v in [('roots',queries),('localModules',closure),('required',required)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b[:b.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE REAL PARABOLIC PERIODS DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual injective real parabolic period map and its finite target. Only declaration values are traversed. The upper dimension inequality, real period surjectivity, reciprocity, original arithmetic comparison and higher continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneRealParabolicPeriodsDependencyAudit1.lean',imports+b)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
files=[r/'SourceIntegralCohomologyFinite.lean',r/'SourceWeightTwoPeriods.lean',r/'SourceWeightTwoPrimitiveCusps.lean',r/'SourceParabolicClassification.lean',p/'source-gamma-one-real-period-injectivity-1-scratch-receipt.json']
rd=dict(chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> original all-weight arithmetic association -> actual Gamma1 Hecke-character realization -> Picard/H1 and Abel-Jacobi -> real period surjectivity -> actual finite real parabolic period map.',assumptionsToDischarge='Existing finite native H1 proves finiteness of actual real Gamma1 characters. The actual linear real period map is injective, so cusp forms are finite over the reals. Signed translation classification, the primitive shift and finite translated cusp limits prove that every squared-trace-four element has zero period. The resulting exact parabolic character target is finite; none of these properties is assumed.',remaining='The reverse dimension inequality and real period surjectivity, reciprocity, original Picard/Hecke/diamond/H1 comparisons, full all-weight characteristic-zero association and higher continuation remain. 16/20; DUB-17--20 OPEN.',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in files],shorterRoute='Reuse the existing native finite-H1 theorem instead of reproving finite-generator character coordinates. Reuse exact signed-parabolic classification and existing primitive limits to discharge parabolicity. No new representation, reflected period pair or principal-level field is introduced.')
output('gamma-one-real-parabolic-periods-audit-route-758.json',json.dumps(rd,indent=2)+'\n')
s=(p/'record_gamma_one_real_period_injectivity_756.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-real-period-injectivity-1','source-gamma-one-real-parabolic-periods-1'),('SourceGammaOneRealPeriodInjectivityAudit1','SourceGammaOneRealParabolicPeriodsAudit1'),('SourceGammaOneRealPeriodInjectivityDependencyAudit1','SourceGammaOneRealParabolicPeriodsDependencyAudit1'),('SOURCE GAMMA ONE REAL PERIOD INJECTIVITY','SOURCE GAMMA ONE REAL PARABOLIC PERIODS'),('gamma-one-real-period-injectivity-audit-route-756.json','gamma-one-real-parabolic-periods-audit-route-758.json'),('(2, 4, 12)','(2, 11, 16)'),('all 12 required','all 16 required'),('requiredProofValueEdges=12','requiredProofValueEdges=16'),('modules=2, queries=4','modules=2, queries=11'),('proofEdges=12','proofEdges=16')]:
 assert a in s,a;s=s.replace(a,b)
ast.parse(s);output('record_gamma_one_real_parabolic_periods_758.py',s)
s=(p/'SourceGammaOneExactRamificationScratchOwnership731.lean').read_text(encoding='utf-8').replace('import SourceGammaOneExactRamification',''.join('import '+m+'\n' for m in mods).rstrip()).replace('#[`SourceGammaOneExactRamification]',arr(mods))
output('SourceGammaOneRealParabolicPeriodsScratchOwnership758.lean',s)
print(json.dumps(dict(modules=2,queries=11,edges=16)))
