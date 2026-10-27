from pathlib import Path
import re,json,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
mods=['SourceFrickeStableMonic','SourceFrickeModularOrbit']
ns='Dubon2026.SourceFricke.'
ths=[ns+n for n in ['LevelGens.ring_monic_j_relation','mdifferentiable_slFn','exists_fraction_and_monic_j_of_principal_invariant']]
defs=[ns+'modularOrbitGens']
roots=[ths[-1]]
extra=[ns+n for n in ['LevelGens.exists_frac','LevelGens.ring_fixed_eq_aeval_j','LevelGens.finrank_levelField_field','finrank_adjoin_j_levelField']]+['MulSemiringAction.charpoly','MulSemiringAction.monic_charpoly','MulSemiringAction.eval_charpoly','MulSemiringAction.smul_coeff_charpoly','CongruenceSubgroup.Gamma_normal']
required=ths+defs+extra
for m in mods:
 f=p/(m+'.lean')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
closure=set(mods);todo=mods.copy()
while todo:
 f=p/(todo.pop()+'.lean')
 for imp in re.findall(r'(?m)^import (\w+)$',f.read_text(encoding='utf-8')):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
closure=sorted(closure)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=closure,separateReason='All public mathematical declarations are required in actual proof values.')
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-fricke-orbit-monic-2-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,names in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE FRICKE ORBIT MONIC')
output('SourceFrickeOrbitMonicAudit2.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceOriginalPrimitiveTateRestrictionDependencyAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,names in [('roots',roots),('localModules',closure),('required',required)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body[:body.index('  logInfo m!')]+'''  logInfo m!"SOURCE FRICKE ORBIT MONIC DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the original-function fraction and monic-relation consumer. Only declaration values are traversed. The actual modular orbit supplies stability and principal-level invariance. Native finite-action characteristic polynomials supply monicity, the root relation and invariant coefficients, which the proved invariant-j theorem identifies as polynomials in actual j. Rational Fourier spanning, differential realization and arithmetic comparison remain; 16/20; DUB-17--20 OPEN."

#eval runPlanarPairingDependencyAudit
'''
output('SourceFrickeOrbitMonicDependencyAudit2.lean',imports+body)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
primary=p/'fricke-level-structure-reuse-656/P2M/Sol/S_WLight_exists_monicRel_j_of_mdifferentiable_levelFraction.lean.txt'
native=Path(r'E:\Lean\Riemann Zeta\.lake\packages\mathlib\Mathlib\RingTheory\Invariant\Basic.lean')
route=dict(chain='DUB-17/18 -> original all-weight association -> actual finite Gamma1 character realization -> actual Picard/H1 comparison -> cusp differential realization -> rational Fourier structure -> integral base change of Fricke fractions -> actual monic relation over C[j].',selectedRoute='Use native MulSemiringAction.charpoly, monic_charpoly, eval_charpoly and smul_coeff_charpoly in the actual stable family algebra. Reuse the proved invariant polynomial-in-j theorem for its coefficients. This replaces the external orbit-coefficient holomorphy and cusp-bound engine. Build the stable family from the modular orbit of the original function. Existing isIntegral_modular_quotient is a formal Laurent-series result at period one; it does not directly give the required arbitrary-width pointwise relation.',assumptionsToDischarge='Any actual holomorphic principal-level invariant function with finite cusp poles at all modular translates is both an actual Fricke fraction and a root of an actual monic equation with polynomial-in-j coefficients. Neither fraction representation nor monic relation is assumed.',remaining='Cyclotomic integral base change, rational Fourier spanning and descent, actual cusp differential realization and arithmetic comparison; 16/20; DUB-17--20 OPEN.',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in [primary,native,p/'fricke-stable-family-route-659.json']],rootPinsChanged=False,proofLimitsChanged=False)
output('fricke-orbit-monic-local-reuse-route-660.json',json.dumps(route,indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),queries=len(ths+defs),theorems=len(ths),constructions=len(defs),edges=len(required))))
