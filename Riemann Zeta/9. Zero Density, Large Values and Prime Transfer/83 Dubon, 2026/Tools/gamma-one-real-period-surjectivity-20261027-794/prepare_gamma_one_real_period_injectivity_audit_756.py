from pathlib import Path
import json,re,hashlib,ast
p=Path(r'E:\Lean\.tmp\dubon83');ns='Dubon2026.'
mods=['SourceGammaOneInvariantRealPart','SourceGammaOneRealPeriodInjectivity']
ths=[ns+x for x in ['sourceGamma1_exists_tile_translate','sourceGamma1_realPart_constant','sourceGamma1_eq_zero_of_real_periods_zero','sourceGamma1_real_periods_injective']]
required=ths+[ns+x for x in ['SourceFunctionField.GammaOne.CuspAuxiliary.conj_T_pow_mem','sourceUpperHalfPlane_re_eq_of_cusp_max','sourceHolomorphic_re_eq_of_isMaxOn','sourceHasDerivAt_comp_smul','sourceWeightTwoPrimitive_period','sourceWeightTwoPrimitive_hasDerivAt','sourceWeightTwoPrimitive_exists_cusp_limit','sourceHolomorphic_re_zero_deriv']]
assert len(required)==12
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0;assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
def output(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
cfg=dict(modules=mods,theorems=ths,constructions=[],queries=ths,proofEdges=required,roots=ths,separatelyAxiomChecked=[],scratchImportClosure=mods,separateReason='Actual Gamma1 real periods determine the cusp form. Surjectivity and reciprocity remain separate obligations.')
output('source-gamma-one-real-period-injectivity-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneExactRamificationAudit1.lean').read_text(encoding='utf-8');b=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,v in [('modules',mods),('theorems',ths),('constructions',[])]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b.replace('SOURCE GAMMA ONE EXACT RAMIFICATION','SOURCE GAMMA ONE REAL PERIOD INJECTIVITY').replace('Gamma One Exact Ramification','Gamma One Real Period Injectivity')
output('SourceGammaOneRealPeriodInjectivityAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in ths)+'\n'+b+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneExactRamificationDependencyAudit1.lean').read_text(encoding='utf-8');b=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,v in [('roots',ths),('localModules',mods),('required',required)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b[:b.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE REAL PERIOD INJECTIVITY DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual Gamma1 real period injectivity proof. Only declaration values are traversed. Real period surjectivity, reciprocity, original Hecke/diamond/Picard/H1 arithmetic comparison, all-weight association and higher continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneRealPeriodInjectivityDependencyAudit1.lean',imports+b)
f=p/'gamma-one-real-period-injectivity-route-756.json';d=json.loads(f.read_text(encoding='utf-8'))
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
rd=dict(chain=d['dependency'],assumptionsToDischarge='The actual real Gamma1 periods determine the cusp form. Primitive derivative normalization and every translated cusp limit are constructed from the original form. The principal-congruence normality theorem supplies the missing cusp translations. No real-period injectivity, reflected-form relation, dimension inequality or surjectivity is assumed.',remaining=d['remaining'],reuseChecked=[dict(path=x['path'],sha256=sha(Path(x['path']))) for x in d['reused']]+[dict(path=str(f),sha256=sha(f))],shorterRoute=d['decision'])
output('gamma-one-real-period-injectivity-audit-route-756.json',json.dumps(rd,indent=2)+'\n')
s=(p/'record_gamma_one_meromorphic_principal_divisor_751.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-meromorphic-principal-divisor-1','source-gamma-one-real-period-injectivity-1'),('SourceGammaOneMeromorphicPrincipalDivisorAudit1','SourceGammaOneRealPeriodInjectivityAudit1'),('SourceGammaOneMeromorphicPrincipalDivisorDependencyAudit1','SourceGammaOneRealPeriodInjectivityDependencyAudit1'),('SOURCE GAMMA ONE MEROMORPHIC PRINCIPAL DIVISOR','SOURCE GAMMA ONE REAL PERIOD INJECTIVITY'),('gamma-one-meromorphic-principal-divisor-audit-route-751.json','gamma-one-real-period-injectivity-audit-route-756.json'),('(2, 6, 15)','(2, 4, 12)'),('all 15 required','all 12 required'),('requiredProofValueEdges=15','requiredProofValueEdges=12'),('modules=2, queries=6','modules=2, queries=4'),('proofEdges=15','proofEdges=12')]:
 assert a in s,a;s=s.replace(a,b)
ast.parse(s);output('record_gamma_one_real_period_injectivity_756.py',s)
s=(p/'SourceGammaOneExactRamificationScratchOwnership731.lean').read_text(encoding='utf-8').replace('import SourceGammaOneExactRamification',''.join('import '+m+'\n' for m in mods).rstrip()).replace('#[`SourceGammaOneExactRamification]',arr(mods))
output('SourceGammaOneRealPeriodInjectivityScratchOwnership756.lean',s)
print(json.dumps(dict(modules=2,queries=4,edges=12)))
