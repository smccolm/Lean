from pathlib import Path
import json,re,hashlib,ast
p=Path(r'E:\Lean\.tmp\dubon83')
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
ns='Dubon2026.SourceFunctionField.GammaOne.'
mods=['SourceGammaOneRationalCuspOrbit','SourceGammaOneCuspJExactOrder','SourceGammaOneCuspRotationOrder','SourceGammaOneCuspTranslationRamification']
ths=[];defs=[]
for m in mods:
 for kind,n in re.findall(r'^(theorem|def|abbrev) (\w+)',(p/(m+'.lean')).read_text(encoding='utf-8'),re.M):
  (ths if kind=='theorem' else defs).append(ns+n)
queries=ths+defs
required=queries+[ns+x for x in ['exists_cusp_place_eq_of_j_pole','cuspRealize_mul_T_zpow_eventuallyEq','meromorphicAt_cuspRealize','cuspPlace_order']]+['Dubon2026.SourceFunctionField.laurent_order_qExpand','Dubon2026.SourceFunctionField.represents_jqNModC','Complex.exp_eq_one_iff','meromorphicOrderAt_eq_int_iff']
assert (len(mods),len(ths),len(defs),len(queries),len(required))==(4,16,5,21,29)
closure=mods+['SourceGammaOneCuspPlaceLeftInvariance','SourceGammaOneCuspTranslations','SourceGammaOneCuspPlaceRightInvariance','SourceGammaOneRationalCuspPlace','SourceGammaOneCuspPlaceExhaustion','SourceGammaOneCuspBoundedRealization','SourceGammaOneCuspResidues']
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0;assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
def output(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=queries,proofEdges=required,roots=queries,separatelyAxiomChecked=[],scratchImportClosure=closure,separateReason='The actual finite cusp orbit space surjects onto j-pole places. Exact raw order and leading-term rotation bound the normalized j pole by every positive signed stabilizer translation. Exact width and bijection still require finite coset counting.')
output('source-gamma-one-cusp-width-bound-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneExactRamificationAudit1.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b.replace('SOURCE GAMMA ONE EXACT RAMIFICATION','SOURCE GAMMA ONE CUSP WIDTH BOUND').replace('Gamma One Exact Ramification','Gamma One Cusp Width Bound')
output('SourceGammaOneCuspWidthBoundAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in queries)+'\n'+b+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneExactRamificationDependencyAudit1.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,v in [('roots',queries),('localModules',closure),('required',required)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b[:b.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE CUSP WIDTH BOUND DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual finite rational cusp orbit map, exact j-pole order and positive stabilizer translation bound. Only declaration values are traversed. Exact widths, cusp bijection, real period surjectivity, reciprocity, original arithmetic comparison and higher continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneCuspWidthBoundDependencyAudit1.lean',imports+b)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
files=[r/'SourceManinCuspSpace.lean',r/'SourceStabilizerMeromorphicOrder.lean',r/'SourceLaurentExpansionOrders.lean',r/'SourceQExpansionLaurentWidth.lean',r/'SourceGammaOnePlusMinus.lean',p/'gamma-one-cusp-width-bound-route-766.json',p/'source-gamma-one-cusp-orbit-invariance-1-scratch-receipt.json']
rd=dict(chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> original all-weight arithmetic association -> actual Gamma1 Hecke-character realization -> Picard/H1 and Abel-Jacobi -> real period surjectivity -> matching Manin/genus cusp terms -> exact cusp widths.',assumptionsToDischarge='The actual rational cusp orbit space is finite and maps onto every j-pole place, by proved invariance and actual cusp exhaustion. Laurent reindexing gives raw j order minus N. The exact nonzero meromorphic uniformizer and translation invariance force N to divide the product of the signed stabilizer translation and the cusp ramification. Thus the algebraic j-pole order is at most every positive signed stabilizer translation. Finiteness, surjectivity, the raw pole order and this bound are derived, not assumed.',remaining='Identify the least positive signed stabilizer translation with its finite coset-orbit size; sum sizes to the subgroup index and compare with the j-pole degree to prove injectivity and exact widths. Reverse dimension, real period surjectivity, reciprocity, Picard/Hecke/diamond/H1, full all-weight characteristic-zero association and higher continuation remain. 16/20; DUB-17--20 OPEN.',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in files],shorterRoute='Reuse native Laurent-order substitution, actual cusp exhaustion and the existing leading-term stabilizer proof. Direct exponential equality supplies the integer divisibility, avoiding construction of a root-of-unity group or a new width-rescaling analytic chart.')
output('gamma-one-cusp-width-bound-audit-route-767.json',json.dumps(rd,indent=2)+'\n')
s=(p/'record_gamma_one_cusp_orbit_invariance_762.py').read_text(encoding='utf-8-sig')
for a,b in [('source-gamma-one-cusp-orbit-invariance-1','source-gamma-one-cusp-width-bound-1'),('SourceGammaOneCuspOrbitInvariance','SourceGammaOneCuspWidthBound'),('SOURCE GAMMA ONE CUSP ORBIT INVARIANCE','SOURCE GAMMA ONE CUSP WIDTH BOUND'),('gamma-one-cusp-orbit-invariance-audit-route-762.json','gamma-one-cusp-width-bound-audit-route-767.json'),('(4, 14, 20)','(4, 21, 29)'),('all 20 required','all 29 required'),('requiredProofValueEdges=20','requiredProofValueEdges=29'),('modules=4, queries=14','modules=4, queries=21'),('proofEdges=20','proofEdges=29')]:
 assert a in s,a;s=s.replace(a,b)
ast.parse(s);output('record_gamma_one_cusp_width_bound_767.py',s)
s=(p/'SourceGammaOneExactRamificationScratchOwnership731.lean').read_text(encoding='utf-8-sig').replace('import SourceGammaOneExactRamification',''.join('import '+m+'\n' for m in mods).rstrip()).replace('#[`SourceGammaOneExactRamification]',arr(mods))
output('SourceGammaOneCuspWidthBoundScratchOwnership767.lean',s)
print(json.dumps(dict(modules=4,queries=21,edges=29)))
