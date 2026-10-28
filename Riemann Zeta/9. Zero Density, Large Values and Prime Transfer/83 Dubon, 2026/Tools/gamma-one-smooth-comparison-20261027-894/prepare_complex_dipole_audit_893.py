from pathlib import Path
import json,re,ast,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
mods=['SourceComplexDipoleLocalModel','SourceComplexDipoleLogDerivative','SourceComplexDipolePairing','SourceUpperHalfPlaneDipole']
ths=[];defs=[]
for m in mods:
 t=(p/(m+'.lean')).read_text(encoding='utf-8')
 ns=re.search(r'^namespace (\S+)',t,re.M)[1]+'.'
 for kind,n in re.findall(r'^(?:noncomputable )?(theorem|def) (\S+)',t,re.M):
  (ths if kind=='theorem' else defs).append(ns+n)
queries=ths+defs
required=queries+['Dubon2026.SourceComplexReciprocity.Wedge.integral_wedge_residue_identity','Dubon2026.SourceComplexReciprocity.DbarFundamental.D','Dubon2026.SourceComplexReciprocity.DbarFundamental.D_eq_zero_of_notMem_tsupport','exists_contMDiffMap_zero_one_of_isClosed','convex_halfSpace_im_gt']
roots=['Dubon2026.SourceComplexReciprocity.Dipole.exists_localModel_pair']
ev=dict(zip(mods,[m+s for m,s in zip(mods,['891c','891c','891c','891d'])]))
closure=mods+json.loads((p/'source-gamma-one-untwist-wedge-1-audit-config.json').read_text(encoding='utf-8'))['scratchImportClosure']
for m in mods:
 f=p/(m+'.lean')
 assert (p/(ev[m]+'.exit')).read_text().strip()=='0' and (p/(ev[m]+'.log')).stat().st_size==0
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
def output(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=queries,compileEvidence=ev,proofEdges=required,roots=roots,scratchImportClosure=closure,separatelyAxiomChecked=[],separateReason='All new declarations consumed by the actual compact dipole construction. The invariant orbit product will consume these local factors.')
output('source-complex-dipole-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOnePeterssonSmoothLimitAudit1.lean').read_text(encoding='utf-8-sig')
b=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b.replace('SOURCE GAMMA ONE PETERSSON SMOOTH LIMIT','SOURCE COMPLEX DIPOLE').replace('Gamma One Petersson Smooth Limit','Complex Dipole')
output('SourceComplexDipoleAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in queries)+'\n'+b+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOnePeterssonSmoothLimitDependencyAudit1.lean').read_text(encoding='utf-8-sig')
b=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,v in [('roots',roots),('localModules',closure),('required',required)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b[:b.index('  logInfo m!')]+'  logInfo m!"SOURCE COMPLEX DIPOLE DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the declaration-VALUE closure of the actual compact dipole construction. The existing wedge/residue identity, original antiholomorphic derivative, native smooth cutoff and convexity are consumed. The exact +1/-1 orders and integral pi times endpoint difference are proved. Invariant comparison V, analytic reciprocity and full all-weight goal remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceComplexDipoleDependencyAudit1.lean',imports+b)
t=(p/'SourceGammaOnePeterssonSmoothLimitScratchOwnership885.lean').read_text(encoding='utf-8-sig')
b=t[t.index('private def inspectOwnership'):]
b=re.sub(r'let mods : Array Name := #\[[^\n]*',lambda _:'let mods : Array Name := '+arr(mods),b)
output('SourceComplexDipoleScratchOwnership893.lean',imports+b)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
r=Path(r'E:\Lean\Riemann Zeta')
paths=[p/'complex-dipole-reuse-route-891.json',p/'anthropic-flt-residual-closure-20261020/P2M/Sol/S_UpperHalfPlane_exists_localModel_pair_integral_mul_dbarLogDeriv_eq.lean.txt',p/'source-gamma-one-untwist-wedge-1-scratch-receipt.json',r/'.lake/packages/mathlib/Mathlib/Analysis/Complex/Convex.lean',p/'SourceComplexDbarCutoff.lean']
route=dict(chain=json.loads(paths[0].read_text(encoding='utf-8'))['chain'],reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in paths],assumptionsToDischarge=['Construct compact C2 cutoff about the actual segment in the upper half-plane','Actual dipole has exact integer orders +1 at s and -1 at b and equals one outside a compact set','Derive continuous compactly supported antiholomorphic logarithmic derivative','Existing audited wedge/residue identity proves integrability and exact pi times endpoint difference'],remaining='Invariant orbit product V, stabilizer multiplicity and degree-zero cancellation, filled quotient and winding-period comparison, analytic reciprocity, original principal-divisor converse and full all-weight chain remain. 16/20; DUB-17--20 OPEN.')
output('source-complex-dipole-audit-route-893.json',json.dumps(route,indent=2)+'\n')
t=(p/'record_source_gamma_one_petersson_smooth_limit_885.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-petersson-smooth-limit-1','source-complex-dipole-1'),('SourceGammaOnePeterssonSmoothLimit','SourceComplexDipole'),('SOURCE GAMMA ONE PETERSSON SMOOTH LIMIT','SOURCE COMPLEX DIPOLE'),('source-gamma-one-petersson-smooth-limit-audit-route-885.json','source-complex-dipole-audit-route-893.json'),('(6, 26, 41)',str((len(mods),len(queries),len(required)))),('all 41 required',f'all {len(required)} required'),('requiredProofValueEdges=41',f'requiredProofValueEdges={len(required)}'),('modules=6, queries=26',f'modules={len(mods)}, queries={len(queries)}'),('proofEdges=41',f'proofEdges={len(required)}'),('== 6',f'== {len(mods)}'),('linterScopes=6',f'linterScopes={len(mods)}')]:
 assert a in t,a
 t=t.replace(a,b)
ast.parse(t);output('record_source_complex_dipole_893.py',t)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),queries=len(queries),required=len(required))))
