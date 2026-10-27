from pathlib import Path
import json,re,hashlib
p=Path(r'E:\Lean\.tmp\dubon83'); ns='Dubon2026.SourceFunctionField.GammaOne.'; fr='Dubon2026.SourceFricke.'
mods=['SourceGammaOneUniformCuspPole','SourceGammaOneHolomorphicModularQuotient','SourceGammaOneHolomorphicFieldRealization']
ths=[fr+'finite_modular_orbit_of_invariant',fr+'exists_uniform_discriminant_pole_bound']+[ns+x for x in ['exists_holomorphic_modular_quotient','exists_holomorphic_modular_quotient_of_meromorphic_cusps','exists_original_field_of_holomorphic']]
required=ths+['MulAction.orbitEquivQuotientStabilizer']+[fr+x for x in ['IsBoundedAtImInfty.mul_discPow_mono','exists_bounded_mul_discriminant_of_meromorphic','periodic_of_principal_invariant']]+[ns+x for x in ['modular_ratio_mem','realize_eq_div','quotient_cusp_represents','holomorphic_quotient_cusp_eventuallyEq']]
assert len(required)==13
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
closure=mods+['SourceGammaOneCuspBoundedRealization','SourceGammaOneCuspResidues']
def output(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
cfg=dict(modules=mods,theorems=ths,constructions=[],queries=ths,proofEdges=required,roots=ths,separatelyAxiomChecked=[],scratchImportClosure=closure,separateReason='Finite orbit, common discriminant exponent, actual modular quotient and original field membership with literal analytic/cusp realizations. Finite analytic-pole clearing and global periods remain.')
output('source-gamma-one-holomorphic-field-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneExactRamificationAudit1.lean').read_text(encoding='utf-8');b=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,v in [('modules',mods),('theorems',ths),('constructions',[])]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b.replace('SOURCE GAMMA ONE EXACT RAMIFICATION','SOURCE GAMMA ONE HOLOMORPHIC FIELD').replace('Gamma One Exact Ramification','Gamma One Holomorphic Field')
output('SourceGammaOneHolomorphicFieldAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in ths)+'\n'+b+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneExactRamificationDependencyAudit1.lean').read_text(encoding='utf-8');b=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,v in [('roots',ths),('localModules',closure),('required',required)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b[:b.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE HOLOMORPHIC FIELD DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual finite orbit, common cusp-pole exponent, modular quotient and original field realization. Only declaration values are traversed. Finite analytic-pole clearing, global periods, Hecke/diamond/H1 arithmetic comparison, all-weight association and higher continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneHolomorphicFieldDependencyAudit1.lean',imports+b)
rd=json.loads((p/'gamma-one-meromorphic-field-route-744.json').read_text());rd['chain']=rd.pop('dependency');rd['assumptionsToDischarge']='Common exponent for all actual cusp poles, genuine holomorphic modular quotient, membership in the original integral-ratio field, pointwise analytic realization and all translated cusp germs. These are derived from holomorphy, actual Gamma1 invariance and meromorphic cusp germs. Finite analytic-pole clearing is not part of this proved increment.'
root=Path(r'E:\Lean\Riemann Zeta');prod=root/'9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026/Extension/Dubon2026'
files=[prod/(x+'.lean') for x in rd['reuse']]+[p/'source-gamma-one-cusp-residues-1-scratch-receipt.json',p/'source-gamma-one-cusp-exhaustion-1-scratch-receipt.json',root/'.lake/packages/mathlib/Mathlib/GroupTheory/Index.lean',root/'.lake/packages/mathlib/Mathlib/GroupTheory/GroupAction/Quotient.lean']
rd['reuseChecked']=[dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest().upper()) for f in files]
output('gamma-one-holomorphic-field-audit-route-744.json',json.dumps(rd,indent=2)+'\n')
s=(p/'record_gamma_one_cusp_exhaustion_743.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-cusp-exhaustion-1','source-gamma-one-holomorphic-field-1'),('SourceGammaOneCuspExhaustionAudit1','SourceGammaOneHolomorphicFieldAudit1'),('SourceGammaOneCuspExhaustionDependencyAudit1','SourceGammaOneHolomorphicFieldDependencyAudit1'),('SOURCE GAMMA ONE CUSP EXHAUSTION','SOURCE GAMMA ONE HOLOMORPHIC FIELD'),('gamma-one-cusp-exhaustion-audit-route-743.json','gamma-one-holomorphic-field-audit-route-744.json'),('(2, 6, 13)','(3, 5, 13)'),(' == 2',' == 3'),('linterScopes=2','linterScopes=3'),('modules=2, queries=6','modules=3, queries=5')]:
 assert a in s,a;s=s.replace(a,b)
output('record_gamma_one_holomorphic_field_744.py',s)
s=(p/'SourceGammaOneExactRamificationScratchOwnership731.lean').read_text(encoding='utf-8').replace('import SourceGammaOneExactRamification',''.join('import '+m+'\n' for m in mods).rstrip()).replace('#[`SourceGammaOneExactRamification]',arr(mods))
output('SourceGammaOneHolomorphicFieldScratchOwnership744.lean',s)
print(json.dumps(dict(modules=3,queries=5,edges=13)))
