from pathlib import Path
from datetime import datetime,timezone
import ast,json,re,hashlib
s=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
versions=json.loads((s/'gamma-one-degree-versions-1715.json').read_text(encoding='utf-8'))
mods=list(versions)
for n in ['SourceGammaOneDegreePreflight1715','SourceGammaOneDegreeValuePreflight1715']:
 f=s/(n+'.log');assert f.with_suffix('.exit').read_text().strip()=='0'
 assert not re.search(r'warning:|error(?:\(|:)|PANIC|Try this:|sorryAx|Found [1-9]',f.read_text(encoding='utf-16'))
def write(n,t):
 f=s/n;assert not f.exists(),f;f.write_text(t,encoding='utf-8')
adjacent=json.loads((s/'reduced-diamond-kernel-versions-1709.json').read_text(encoding='utf-8'))
for m,v in versions.items():
 f=s/(m+v+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 c=f.read_text(encoding='utf-8')
 for n,ver in {**versions,**adjacent}.items():c=c.replace('import '+n+ver+'\n','import '+n+'\n')
 write(m+'.lean',c)
write('gamma-one-degree-versions-1718.json',json.dumps(versions,indent=2)+'\n')
cfg=json.loads((s/'gamma-one-degree-preflight-config-1715.json').read_text(encoding='utf-8'))
up=[]
for f in ['even-weight-fricke-trace-versions-1643.json','even-weight-fricke-uniform-versions-1653.json','even-weight-full-slash-versions-1661.json','even-weight-integral-diamond-versions-1669.json','reduced-diamond-action-versions-1700.json','reduced-diamond-kernel-versions-1709.json']:
 up+=list(json.loads((s/f).read_text(encoding='utf-8')))
cfg.update(modules=mods,queries=cfg['theorems']+cfg['constructions'],localModules=mods+up,separatelyAxiomChecked=[],compileEvidence={m:m+'-1718' for m in mods})
stem='source-gamma-one-degree-1';write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
for a,b in [('SourceGammaOneDegreePreflight1715','SourceGammaOneDegreeAudit1'),('SourceGammaOneDegreeValuePreflight1715','SourceGammaOneDegreeDependencyAudit1')]:
 c=(s/(a+'.lean')).read_text(encoding='utf-8')
 for n,v in {**versions,**adjacent}.items():c=c.replace(n+v,n)
 for key in ['theorems','constructions','roots','localModules']:
  c=re.sub(r'let '+key+r' : Array Name := #\[[^\n]*\]','let '+key+' : Array Name := '+arr(cfg[key]),c)
 c=re.sub(r'let required : Array Name := #\[[^\n]*\]','let required : Array Name := '+arr(cfg['proofEdges']),c)
 c=c.replace('GAMMA ONE DEGREE PREFLIGHT','GAMMA ONE DEGREE');write(b+'.lean',c)
c=(s/'SourceIntegralTraceScratchOwnership1532.lean').read_text(encoding='utf-8')
c='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+c[c.index('\nopen Lean'):]
c=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),c)
write('SourceGammaOneDegreeScratchOwnership1718.lean',c)
report='Dubon Original Gamma One Degree Preservation Assessment 2026-10-29.md'
chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight characteristic-zero association -> finite homogeneous Gamma1 Hecke-character realization -> original degree/genus preservation -> actual signed-index lower bound and finite coordinate-degree transport.'
discharged=['The actual j-substitution minimal polynomial maps to the algebraic closure. Its already proved degree there gives a lower bound over the original coefficient field. Native finite divisor generation and the simple-extension tower give the required full modular base degree inequality.',
'Full-base fixation, the exact reduced action kernel and Artin degree now give the total signed-index lower bound from positive coordinate degree. No action, kernel, base inclusion or base degree remains a premise.',
'Native Laurent coefficient independence and finite polynomial denominator clearing preserve independent finite families over the actual rational-function coordinate. Rank bounds derive finite degree over the original coefficient field; no independence, finiteness or base-change equality certificate is supplied.',
'The original integral-ratio field maps into the actual coefficient residue field. Native finite residue degree and integral-ratio inclusion give positive degree there, and coefficient transport supplies the prime-field positivity and return inequality.',
'The signed-index bound holds for the actual residue integral-ratio field. The native upper-degree consumer proves original Gamma1 coordinate degree preservation and equality of the actual residue image with the original integral-ratio field at every prime away from the level, including characteristics two and three.']
remaining='Original genus preservation is still required. Integral parabolic transfer, removal of the 3<p and fixed exceptional-prime restrictions, the required two-dimensional characteristic-zero realization, original all-weight association, remaining local/image/regularity inputs, automorphy and literal higher continuation remain open. Acceptance stays 16/20; DUB-17--20 OPEN, with every original criterion preserved.'
route='Reuse was checked against native Laurent coefficient independence, finite-coordinate degree transport, finite divisor generation, the algebraically closed j-substitution degree, actual residue-coordinate finiteness and original degree assembly. The pinned Apache-2.0 source is anthropics/fermats-last-theorem at 6e837e75355538c7f80bab5b956861e86c4eacc2; the two newly selected source files are hash-verified inert references. Only the lower base-degree inequality is needed; full base-change equality and an infinite-dimensional transport theory are deferred. Ambient Laurent independence avoids additional chosen internal coordinate maps.'
write(report,'# Original Gamma1 degree preservation — 29 October 2026\n\n'+chain+'\n\n'+'\n\n'.join(discharged)+'\n\n'+route+'\n\nNine versioned modules pass all 17 public axiom queries, exhaustive private/generated theorem checks and sixteen linters each. All 58 required dependencies occur in declaration-value closures of the original degree-preservation and signed-index consumers. Failed elaboration attempts and fresh compiling successors are retained. Canonical ownership and receipts follow separately.\n\nThe endpoint assumes only a nonzero level, a prime not dividing that level, an actual valuation subring of a characteristic-zero coefficient field and residue characteristic equal to that prime. It assumes no genus or degree-preservation conclusion.\n\n'+remaining+'\n\nThis scope is scratch-audited; production promotion and assembled verification are pending. Frozen source, root pins, proof limits and the owner-only synchronization BAT remain unchanged.\n')
refs=['anthropic-reduced-degree-transport-1706/manifest.json','gamma-one-degree-reuse-review-1714.json','source-reduced-diamond-kernel-1-scratch-receipt.json',report]
routeobj=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain=chain,reuseChecked=[dict(path=str(s/n),sha256=sha(s/n)) for n in refs],shorterRoute=route,assumptionsToDischarge=discharged,remaining=remaining,externalBuild=False,externalImport=False,rootPinsChanged=False,proofLimitsChanged=False)
rf='source-gamma-one-degree-audit-route-1718.json';write(rf,json.dumps(routeobj,indent=2)+'\n')
c=(s/'record_siegel_function_1580.py').read_text(encoding='utf-8')
for a,b in [('source-siegel-function-1',stem),('SourceSiegelFunctionAudit1','SourceGammaOneDegreeAudit1'),('SourceSiegelFunctionDependencyAudit1','SourceGammaOneDegreeDependencyAudit1'),('SourceSiegelFunctionScratchOwnership1580','SourceGammaOneDegreeScratchOwnership1718'),('source-siegel-function-audit-route-1580',rf[:-5]),('SIEGEL FUNCTION','GAMMA ONE DEGREE'),('20261028','20261029'),('2026-10-28','2026-10-29')]:c=c.replace(a,b)
nm,nq,ne=len(mods),len(cfg['queries']),len(cfg['proofEdges']);assert (nm,nq,ne)==(9,17,58)
c=c.replace('(19, 101, 110)',str((nm,nq,ne))).replace('modules=19',f'modules={nm}').replace('queries=101',f'queries={nq}').replace('linterScopes=19',f'linterScopes={nm}').replace("text.count('with 16 linters') == 19",f"text.count('with 16 linters') == {nm}").replace('all 110 required',f'all {ne} required').replace('requiredProofValueEdges=110',f'requiredProofValueEdges={ne}').replace('proofEdges=110',f'proofEdges={ne}')
ast.parse(c);write('record_gamma_one_degree_1718.py',c)
c=(s/'audit_siegel_function_1580.ps1').read_text(encoding='utf-8')
for a,b in [('SourceSiegelFunctionAudit1','SourceGammaOneDegreeAudit1'),('SourceSiegelFunctionDependencyAudit1','SourceGammaOneDegreeDependencyAudit1'),('SourceSiegelFunctionScratchOwnership1580','SourceGammaOneDegreeScratchOwnership1718'),('record_siegel_function_1580','record_gamma_one_degree_1718')]:c=c.replace(a,b)
write('audit_gamma_one_degree_1718.ps1',c)
c=(s/'build_siegel_function_canonical_1580.ps1').read_text(encoding='utf-8')
c=re.sub(r'\$names=@\([^\n]+\)',"$names=@("+','.join(repr(m) for m in mods)+')',c).replace("$ev=$base+'-1580'","$ev=$base+'-1718'").replace('audit_siegel_function_1580','audit_gamma_one_degree_1718')
write('build_gamma_one_degree_canonical_1718.ps1',c)
print(json.dumps(dict(modules=nm,queries=nq,edges=ne,status='Canonical statements, mathematical bodies and comments frozen.')))
