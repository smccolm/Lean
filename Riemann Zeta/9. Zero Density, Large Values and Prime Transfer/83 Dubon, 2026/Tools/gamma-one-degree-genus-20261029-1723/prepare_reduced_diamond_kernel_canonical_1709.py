from pathlib import Path
from datetime import datetime,timezone
import ast,json,re,hashlib
s=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
versions=json.loads((s/'reduced-diamond-kernel-versions-1705.json').read_text(encoding='utf-8'))
mods=list(versions)
for n in ['SourceReducedDiamondKernelPreflight1705','SourceReducedDiamondKernelValuePreflight1705']:
 f=s/(n+'.log');assert f.with_suffix('.exit').read_text().strip()=='0'
 assert not re.search(r'warning:|error(?:\(|:)|PANIC|Try this:|sorryAx|Found [1-9]',f.read_text(encoding='utf-16'))
def write(n,t):
 f=s/n;assert not f.exists(),f;f.write_text(t,encoding='utf-8')
adjacent=json.loads((s/'reduced-diamond-action-versions-1700.json').read_text(encoding='utf-8'))
for m,v in versions.items():
 f=s/(m+v+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 c=f.read_text(encoding='utf-8')
 for n,ver in {**versions,**adjacent}.items():c=c.replace('import '+n+ver+'\n','import '+n+'\n')
 write(m+'.lean',c)
write('reduced-diamond-kernel-versions-1709.json',json.dumps(versions,indent=2)+'\n')
cfg=json.loads((s/'reduced-diamond-kernel-preflight-config-1705.json').read_text(encoding='utf-8'))
up=[]
for f in ['even-weight-fricke-trace-versions-1643.json','even-weight-fricke-uniform-versions-1653.json','even-weight-full-slash-versions-1661.json','even-weight-integral-diamond-versions-1669.json','reduced-diamond-action-versions-1700.json']:
 up+=list(json.loads((s/f).read_text(encoding='utf-8')))
cfg.update(modules=mods,queries=cfg['theorems']+cfg['constructions'],localModules=mods+up,separatelyAxiomChecked=[],compileEvidence={m:m+'-1709' for m in mods})
stem='source-reduced-diamond-kernel-1';write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
for a,b in [('SourceReducedDiamondKernelPreflight1705','SourceReducedDiamondKernelAudit1'),('SourceReducedDiamondKernelValuePreflight1705','SourceReducedDiamondKernelDependencyAudit1')]:
 c=(s/(a+'.lean')).read_text(encoding='utf-8')
 for n,v in {**versions,**adjacent}.items():c=c.replace(n+v,n)
 for key in ['theorems','constructions','roots','localModules']:
  c=re.sub(r'let '+key+r' : Array Name := #\[[^\n]*\]','let '+key+' : Array Name := '+arr(cfg[key]),c)
 c=re.sub(r'let required : Array Name := #\[[^\n]*\]','let required : Array Name := '+arr(cfg['proofEdges']),c)
 c=c.replace('REDUCED DIAMOND KERNEL PREFLIGHT','REDUCED DIAMOND KERNEL');write(b+'.lean',c)
c=(s/'SourceIntegralTraceScratchOwnership1532.lean').read_text(encoding='utf-8')
c='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+c[c.index('\nopen Lean'):]
c=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),c)
write('SourceReducedDiamondKernelScratchOwnership1709.lean',c)
report='Dubon Reduced Diamond Kernel and Fixed Field Assessment 2026-10-29.md'
chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight characteristic-zero association -> finite homogeneous Gamma1 Hecke-character realization -> original degree/genus preservation -> signed-index lower bound -> actual reduced action, exact kernel and fixed-field degree.'
discharged=['Native degeneracy maps and the original integral j ratio put every divisor j expansion in the Gamma0 field, hence put the actual full modular base field in the original Gamma1 field.',
'Actual even integral Gamma0 ratios are fixed by the constructed diamond pullback. Adjoin extensionality proves fixation of the whole Gamma0 field and therefore of the actual full modular base field.',
'The actual integral Eisenstein separator transforms by the upper-left matrix entry. Its nonzero E4 denominator and first-coefficient separation identify every signed class at levels above two, in every coefficient characteristic. At levels one and two all Gamma0 matrices already lie in signed Gamma1.',
'The exact action kernel is signed Gamma1 inside Gamma0. Its finite index proves finiteness of the actual automorphism image; native Artin fixed-field theory gives its exact degree, equal to that signed relative index. No kernel, finiteness, fixation or degree premise remains in these consumers.']
remaining='The total signed-index lower bound still needs the full-base degree comparison and finite coordinate-degree transfer. Original degree/genus preservation, integral parabolic transfer, removal of the 3<p and fixed exceptional-prime restrictions, the required two-dimensional characteristic-zero realization, original all-weight association, remaining local/image/regularity inputs, automorphy and literal higher continuation remain open. Acceptance stays 16/20; DUB-17--20 OPEN, with every original criterion preserved.'
route='Reuse was checked in native SourceGammaOneHeckeFieldInclusion, SourceGammaOneIntegralJRatio, SourceGammaOneEisensteinSeparation and Mathlib fixed-field theory. The pinned Apache-2.0 source is anthropics/fermats-last-theorem at 6e837e75355538c7f80bab5b956861e86c4eacc2. Specializing its general GammaH argument to Gamma1 avoids coset-averaged forms and uses the already proved integral separators directly. Adjoin extensionality avoids a second construction of the fixed intermediate field.'
write(report,'# Reduced diamond kernel and fixed-field degree — 29 October 2026\n\n'+chain+'\n\n'+'\n\n'.join(discharged)+'\n\n'+route+'\n\nSix versioned modules pass all 17 public axiom queries, exhaustive private/generated theorem checks and sixteen linters each. All 31 required dependencies occur in declaration-value closures of the actual base inclusion/fixation, exact kernel and Artin degree consumers. The first value audit caught three incorrectly qualified Eisenstein declaration names; the corrected fresh audit verifies their actual GammaOne namespace. Mathematical statements and proofs were unchanged. Both audits are retained.\n\n'+remaining+'\n\nThis scope is scratch-audited; production promotion and assembled verification are pending. Frozen source, root pins, proof limits and the owner-only synchronization BAT remain unchanged.\n')
refs=['anthropic-reduced-field-action-1662/manifest.json','source-reduced-diamond-action-1-scratch-receipt.json',report]
routeobj=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain=chain,reuseChecked=[dict(path=str(s/n),sha256=sha(s/n)) for n in refs],shorterRoute=route,assumptionsToDischarge=discharged,remaining=remaining,externalBuild=False,externalImport=False,rootPinsChanged=False,proofLimitsChanged=False)
rf='source-reduced-diamond-kernel-audit-route-1709.json';write(rf,json.dumps(routeobj,indent=2)+'\n')
c=(s/'record_siegel_function_1580.py').read_text(encoding='utf-8')
for a,b in [('source-siegel-function-1',stem),('SourceSiegelFunctionAudit1','SourceReducedDiamondKernelAudit1'),('SourceSiegelFunctionDependencyAudit1','SourceReducedDiamondKernelDependencyAudit1'),('SourceSiegelFunctionScratchOwnership1580','SourceReducedDiamondKernelScratchOwnership1709'),('source-siegel-function-audit-route-1580',rf[:-5]),('SIEGEL FUNCTION','REDUCED DIAMOND KERNEL'),('20261028','20261029'),('2026-10-28','2026-10-29')]:c=c.replace(a,b)
nm,nq,ne=len(mods),len(cfg['queries']),len(cfg['proofEdges']);assert (nm,nq,ne)==(6,17,31)
c=c.replace('(19, 101, 110)',str((nm,nq,ne))).replace('modules=19',f'modules={nm}').replace('queries=101',f'queries={nq}').replace('linterScopes=19',f'linterScopes={nm}').replace("text.count('with 16 linters') == 19",f"text.count('with 16 linters') == {nm}").replace('all 110 required',f'all {ne} required').replace('requiredProofValueEdges=110',f'requiredProofValueEdges={ne}').replace('proofEdges=110',f'proofEdges={ne}')
ast.parse(c);write('record_reduced_diamond_kernel_1709.py',c)
c=(s/'audit_siegel_function_1580.ps1').read_text(encoding='utf-8')
for a,b in [('SourceSiegelFunctionAudit1','SourceReducedDiamondKernelAudit1'),('SourceSiegelFunctionDependencyAudit1','SourceReducedDiamondKernelDependencyAudit1'),('SourceSiegelFunctionScratchOwnership1580','SourceReducedDiamondKernelScratchOwnership1709'),('record_siegel_function_1580','record_reduced_diamond_kernel_1709')]:c=c.replace(a,b)
write('audit_reduced_diamond_kernel_1709.ps1',c)
c=(s/'build_siegel_function_canonical_1580.ps1').read_text(encoding='utf-8')
c=re.sub(r'\$names=@\([^\n]+\)',"$names=@("+','.join(repr(m) for m in mods)+')',c).replace("$ev=$base+'-1580'","$ev=$base+'-1709'").replace('audit_siegel_function_1580','audit_reduced_diamond_kernel_1709')
write('build_reduced_diamond_kernel_canonical_1709.ps1',c)
print(json.dumps(dict(modules=nm,queries=nq,edges=ne,status='Canonical statements, mathematical bodies and comments frozen.')))
