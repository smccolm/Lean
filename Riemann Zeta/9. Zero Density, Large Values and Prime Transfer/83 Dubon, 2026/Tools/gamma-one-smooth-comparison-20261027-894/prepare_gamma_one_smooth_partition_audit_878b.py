from pathlib import Path
import json,re,ast,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
mods=['SourceModularSmoothCutoff','SourceModularSmoothGeometry','SourceModularSmoothCosetSum','SourceModularSmoothCover','SourceModularSmoothedFundamentalSupport','SourceModularSmoothedFundamental','SourceGammaOneSmoothPartition']
ths=[];defs=[]
for m in mods:
 t=(p/(m+'.lean')).read_text(encoding='utf-8')
 ns=re.search(r'^namespace (\S+)',t,re.M)[1]+'.'
 for kind,n in re.findall(r'^(?:noncomputable )?(theorem|def) (\S+)',t,re.M):
  (ths if kind=='theorem' else defs).append(ns+n)
defs.append('Dubon2026.SourceSmoothedFundamental.quotientFintype')
queries=ths+defs
required=queries+['ProperlyDiscontinuousSMul.finite_disjoint_inter_image','UpperHalfPlane.moebius_im','ModularGroup.exists_smul_mem_fd','Real.smoothTransition.contDiff','CongruenceSubgroup.instFiniteIndexGamma1','Dubon2026.modularContinuousConstSMulSL2']
roots=['Dubon2026.sourceGamma1_smooth_partition']
ev={m:m+('878b' if m in mods[-3:] else '877a') for m in mods}
for m in mods:
 f=p/(m+'.lean')
 assert (p/(ev[m]+'.exit')).read_text().strip()=='0' and (p/(ev[m]+'.log')).stat().st_size==0
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
def output(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=queries,compileEvidence=ev,proofEdges=required,roots=roots,scratchImportClosure=mods,separatelyAxiomChecked=[],separateReason='All declarations required in the VALUE closure of the actual original Gamma1 partition; unconsumed convenience lemmas deferred.')
output('source-gamma-one-smooth-partition-1b-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneUntwistWedgeAudit1.lean').read_text(encoding='utf-8-sig')
b=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b.replace('SOURCE GAMMA ONE UNTWIST WEDGE','SOURCE GAMMA ONE SMOOTH PARTITION').replace('Gamma One Untwist Wedge','Gamma One Smooth Partition')
output('SourceGammaOneSmoothPartitionAudit1b.lean',imports+''.join('#print axioms '+n+'\n' for n in queries)+'\n'+b+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneUntwistWedgeDependencyAudit1.lean').read_text(encoding='utf-8-sig')
b=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,v in [('roots',roots),('localModules',mods),('required',required)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b[:b.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE SMOOTH PARTITION DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the declaration-VALUE closure of the actual original Gamma1 compact smooth partition. Native proper discontinuity, Mobius geometry, smooth transition and the existing integral modular continuity instance are consumed. Integral normalization, winding-period comparison and full all-weight goal remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneSmoothPartitionDependencyAudit1b.lean',imports+b)
t=(p/'SourceGammaOneUntwistWedgeScratchOwnership874.lean').read_text(encoding='utf-8-sig')
b=t[t.index('private def inspectOwnership'):]
b=re.sub(r'let mods : Array Name := #\[[^\n]*',lambda _:'let mods : Array Name := '+arr(mods),b)
output('SourceGammaOneSmoothPartitionScratchOwnership878b.lean',imports+b)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
paths=['modular-smooth-partition-route-875.json','modular-smooth-partition-route-876.json','smooth-coset-route-adjustment-876d.json','smooth-partition-minimal-route-877.json']
rows=[dict(path=str(p/n),sha256=sha(p/n)) for n in paths]
rows+=json.loads((p/paths[0]).read_text(encoding='utf-8'))['primary']
route=dict(chain=['DUB-17/18','original all-weight arithmetic association','original Gamma1 coefficient Hecke realization','Picard/H1','Abel-Jacobi converse','analytic reciprocity','winding-period limit','actual compact smooth orbit partition'],reuseChecked=rows,assumptionsToDischarge=['Literal subgroup coset cutoff is smooth with compact support contained in upper half plane','Its actual Gamma1 orbit sum has finite support, is bounded by one and equals one beyond the exact height threshold','Only finitely many modular translates meet its support'],remaining='Invariant integral limit with exact central-sign multiplicity, smooth comparison model, modular winding/period/Petersson comparison, original principal-divisor converse and entire all-weight arithmetic chain remain. No DUB gate closed; 16/20; DUB-17--20 OPEN.')
output('source-gamma-one-smooth-partition-audit-route-878b.json',json.dumps(route,indent=2)+'\n')
t=(p/'record_source_gamma_one_untwist_wedge_874.py').read_text(encoding='utf-8')
replacements=[('source-gamma-one-untwist-wedge-1','source-gamma-one-smooth-partition-1b'),('SourceGammaOneUntwistWedge','SourceGammaOneSmoothPartition'),('SOURCE GAMMA ONE UNTWIST WEDGE','SOURCE GAMMA ONE SMOOTH PARTITION'),('source-gamma-one-untwist-wedge-audit-route-874.json','source-gamma-one-smooth-partition-audit-route-878b.json'),('(5, 27, 35)',str((len(mods),len(queries),len(required)))),('all 35 required',f'all {len(required)} required'),('requiredProofValueEdges=35',f'requiredProofValueEdges={len(required)}'),('modules=5, queries=27',f'modules={len(mods)}, queries={len(queries)}'),('proofEdges=35',f'proofEdges={len(required)}'),('== 5',f'== {len(mods)}'),('linterScopes=5',f'linterScopes={len(mods)}')]
for a,b in replacements:
 assert a in t,a
 t=t.replace(a,b)
t=t.replace('SourceGammaOneSmoothPartitionAudit1.log','SourceGammaOneSmoothPartitionAudit1b.log').replace('SourceGammaOneSmoothPartitionDependencyAudit1.log','SourceGammaOneSmoothPartitionDependencyAudit1b.log')
ast.parse(t);output('record_source_gamma_one_smooth_partition_878b.py',t)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),queries=len(queries),required=len(required))))
