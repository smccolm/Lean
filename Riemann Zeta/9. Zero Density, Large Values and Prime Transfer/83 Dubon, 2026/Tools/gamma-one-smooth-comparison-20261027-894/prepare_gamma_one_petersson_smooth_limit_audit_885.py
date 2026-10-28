from pathlib import Path
import json,re,ast,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
mods=['SourceModularProjectiveFibers','SourceModularSmoothOrbitMass','SourceModularInvariantIntegralUnfolding','SourceModularSmoothIntegralLimit','SourceModularSmoothPlaneIntegral','SourceGammaOnePeterssonSmoothLimit']
ths=[];defs=[]
for m in mods:
 t=(p/(m+'.lean')).read_text(encoding='utf-8')
 ns=re.search(r'^namespace (\S+)',t,re.M)[1]+'.'
 for kind,n in re.findall(r'^(?:noncomputable )?(theorem|def) (\S+)',t,re.M):
  (ths if kind=='theorem' else defs).append(ns+n)
queries=ths+defs
required=queries+['Dubon2026.SourceSmoothedFundamental.contDiff','Dubon2026.SourceSmoothedFundamental.finite_support_smul','Dubon2026.SourceSmoothedFundamental.finsum_smul_le_one','Dubon2026.SourceSmoothedFundamental.finsum_smul_eq_one','Dubon2026.SourceSmoothedFundamental.tsupport_subset','Dubon2026.integralSubgroupDomain_volume_lt_top','Dubon2026.isFundamentalDomain_integralSubgroup','Dubon2026.fd_ae_eq_fdo','Dubon2026.SourceFunctionField.GammaOne.SignedForms.extend','CuspFormClass.petersson_bounded_left',"MeasureTheory.IsFundamentalDomain.lintegral_eq_tsum''","MeasureTheory.IsFundamentalDomain.integral_eq_tsum''",'MeasureTheory.integral_tsum','MeasureTheory.tendsto_integral_filter_of_dominated_convergence','MonoidHom.fiberEquivKerOfSurjective']
roots=['Dubon2026.sourceGamma1_petersson_smoothed_limit']
ev=dict(zip(mods,[m+s for m,s in zip(mods,['879a','880c','881b','882b','883a','884b'])]))
closure=mods+json.loads((p/'source-gamma-one-smooth-partition-1b-audit-config.json').read_text(encoding='utf-8'))['modules']
for m in mods:
 f=p/(m+'.lean')
 assert (p/(ev[m]+'.exit')).read_text().strip()=='0' and (p/(ev[m]+'.log')).stat().st_size==0
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
def output(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=queries,compileEvidence=ev,proofEdges=required,roots=roots,scratchImportClosure=closure,separatelyAxiomChecked=[],separateReason='All new declarations required by the actual original Gamma1 Petersson smooth-limit consumer.')
output('source-gamma-one-petersson-smooth-limit-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneUntwistWedgeAudit1.lean').read_text(encoding='utf-8-sig')
b=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b.replace('SOURCE GAMMA ONE UNTWIST WEDGE','SOURCE GAMMA ONE PETERSSON SMOOTH LIMIT').replace('Gamma One Untwist Wedge','Gamma One Petersson Smooth Limit')
output('SourceGammaOnePeterssonSmoothLimitAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in queries)+'\n'+b+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneUntwistWedgeDependencyAudit1.lean').read_text(encoding='utf-8-sig')
b=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,v in [('roots',roots),('localModules',closure),('required',required)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b[:b.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE PETERSSON SMOOTH LIMIT DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the declaration-VALUE closure of the actual original Gamma1 cusp-form consumer. Native unfolding, fiber equivalence and dominated convergence, existing generic projective domain, finite volume, null boundary and faithful signed cusp forms are consumed. No invariant limit, integrability or central normalization is assumed. Winding-period comparison and full all-weight goal remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOnePeterssonSmoothLimitDependencyAudit1.lean',imports+b)
t=(p/'SourceGammaOneUntwistWedgeScratchOwnership874.lean').read_text(encoding='utf-8-sig')
b=t[t.index('private def inspectOwnership'):]
b=re.sub(r'let mods : Array Name := #\[[^\n]*',lambda _:'let mods : Array Name := '+arr(mods),b)
output('SourceGammaOnePeterssonSmoothLimitScratchOwnership885.lean',imports+b)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
paths=['projective-smooth-unfolding-route-879.json','smooth-native-unfolding-route-883.json','source-gamma-one-smooth-partition-1b-scratch-receipt.json','source-gamma-one-signed-reciprocity-1-scratch-receipt.json']
rows=[dict(path=str(p/n),sha256=sha(p/n)) for n in paths]
rows+=json.loads((p/paths[0]).read_text(encoding='utf-8'))['reuseChecked']
rows+=[json.loads((p/paths[1]).read_text(encoding='utf-8'))['primary']]
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
rows.append(dict(path=str(r/'CuspTraceLatticeIntegral.lean'),sha256=sha(r/'CuspTraceLatticeIntegral.lean'),read='Entire module read; existing generic finite-volume theorem reused.'))
route=dict(chain=['DUB-17/18','original all-weight arithmetic association','original Gamma1 coefficient Hecke realization','Picard/H1','Abel-Jacobi converse','analytic reciprocity','Petersson comparison','actual original cusp-form smooth integral limit'],reuseChecked=rows,assumptionsToDischarge=['Actual projective map has exactly two-element fibers and projective smooth orbit mass tends to one half','Native fundamental-domain unfolding proves both integrability and weighted integral equality','Existing null boundary transfers to the literal source closed domain; planar/hyperbolic measure conversion is exact','Original Gamma1 cusp forms have derived signed invariance, actual Petersson bound and integrability; no analytic limit certificate is supplied'],remaining='Actual smooth comparison local model and winding-period/Petersson reciprocity assembly remain, followed by original principal-divisor converse and entire all-weight arithmetic chain. No DUB gate closed; 16/20; DUB-17--20 OPEN.')
output('source-gamma-one-petersson-smooth-limit-audit-route-885.json',json.dumps(route,indent=2)+'\n')
t=(p/'record_source_gamma_one_untwist_wedge_874.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-untwist-wedge-1','source-gamma-one-petersson-smooth-limit-1'),('SourceGammaOneUntwistWedge','SourceGammaOnePeterssonSmoothLimit'),('SOURCE GAMMA ONE UNTWIST WEDGE','SOURCE GAMMA ONE PETERSSON SMOOTH LIMIT'),('source-gamma-one-untwist-wedge-audit-route-874.json','source-gamma-one-petersson-smooth-limit-audit-route-885.json'),('(5, 27, 35)',str((len(mods),len(queries),len(required)))),('all 35 required',f'all {len(required)} required'),('requiredProofValueEdges=35',f'requiredProofValueEdges={len(required)}'),('modules=5, queries=27',f'modules={len(mods)}, queries={len(queries)}'),('proofEdges=35',f'proofEdges={len(required)}'),('== 5',f'== {len(mods)}'),('linterScopes=5',f'linterScopes={len(mods)}')]:
 assert a in t,a
 t=t.replace(a,b)
ast.parse(t);output('record_source_gamma_one_petersson_smooth_limit_885.py',t)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),queries=len(queries),required=len(required))))
