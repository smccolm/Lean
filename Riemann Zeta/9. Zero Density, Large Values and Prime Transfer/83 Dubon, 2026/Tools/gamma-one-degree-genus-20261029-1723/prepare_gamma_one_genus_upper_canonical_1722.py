from pathlib import Path
from datetime import datetime,timezone
import ast,json,re,hashlib
s=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
versions=json.loads((s/'gamma-one-genus-upper-versions-1720.json').read_text(encoding='utf-8'))
mods=list(versions)
for n in ['SourceGammaOneGenusUpperPreflight1720','SourceGammaOneGenusUpperValuePreflight1720']:
 f=s/(n+'.log');assert f.with_suffix('.exit').read_text().strip()=='0'
 assert not re.search(r'warning:|error(?:\(|:)|PANIC|Try this:|sorryAx|Found [1-9]',f.read_text(encoding='utf-16'))
def write(n,t):
 f=s/n;assert not f.exists(),f;f.write_text(t,encoding='utf-8')
adjacent=json.loads((s/'gamma-one-degree-versions-1718.json').read_text(encoding='utf-8'))
for m,v in versions.items():
 f=s/(m+v+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 c=f.read_text(encoding='utf-8')
 for n,ver in {**versions,**adjacent}.items():c=c.replace('import '+n+ver+'\n','import '+n+'\n')
 write(m+'.lean',c)
write('gamma-one-genus-upper-versions-1722.json',json.dumps(versions,indent=2)+'\n')
cfg=json.loads((s/'gamma-one-genus-upper-preflight-config-1720.json').read_text(encoding='utf-8'))
up=[]
for f in ['even-weight-fricke-trace-versions-1643.json','even-weight-fricke-uniform-versions-1653.json','even-weight-full-slash-versions-1661.json','even-weight-integral-diamond-versions-1669.json','reduced-diamond-action-versions-1700.json','reduced-diamond-kernel-versions-1709.json','gamma-one-degree-versions-1718.json']:
 up+=list(json.loads((s/f).read_text(encoding='utf-8')))
cfg.update(modules=mods,queries=cfg['theorems']+cfg['constructions'],localModules=mods+up,separatelyAxiomChecked=[],compileEvidence={m:m+'-1722' for m in mods})
stem='source-gamma-one-genus-upper-1';write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
for a,b in [('SourceGammaOneGenusUpperPreflight1720','SourceGammaOneGenusUpperAudit1'),('SourceGammaOneGenusUpperValuePreflight1720','SourceGammaOneGenusUpperDependencyAudit1')]:
 c=(s/(a+'.lean')).read_text(encoding='utf-8')
 for n,v in {**versions,**adjacent}.items():c=c.replace(n+v,n)
 for key in ['theorems','constructions','roots','localModules']:
  c=re.sub(r'let '+key+r' : Array Name := #\[[^\n]*\]','let '+key+' : Array Name := '+arr(cfg[key]),c)
 c=re.sub(r'let required : Array Name := #\[[^\n]*\]','let required : Array Name := '+arr(cfg['proofEdges']),c)
 c=c.replace('GAMMA ONE GENUS UPPER PREFLIGHT','GAMMA ONE GENUS UPPER');write(b+'.lean',c)
c=(s/'SourceIntegralTraceScratchOwnership1532.lean').read_text(encoding='utf-8')
c='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+c[c.index('\nopen Lean'):]
c=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),c)
write('SourceGammaOneGenusUpperScratchOwnership1722.lean',c)
report='Dubon Original Gamma One Residue Genus Upper Assessment 2026-10-29.md'
chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight characteristic-zero association -> finite homogeneous Gamma1 Hecke-character realization -> original degree/genus preservation -> upper bound on the actual residue genus.'
discharged=['For the actual valuation subring of the algebraic closure of the rationals, original Gamma1 coordinate degree preservation and residue-field identification now supply the degree premise of the native separating-coordinate genus inequality.',
'The actual regular prolongation, proved residue separability and algebraic closure of the residue coefficients give genus(residue image) <= genus(original function field) for every prime not dividing the level, including two and three. No degree, genus or regular-prolongation certificate is assumed.']
remaining='The reverse genus inequality is still required. Integral parabolic transfer, removal of the 3<p and fixed exceptional-prime restrictions, the required two-dimensional characteristic-zero realization, original all-weight association, remaining local/image/regularity inputs, automorphy and literal higher continuation remain open. Acceptance stays 16/20; DUB-17--20 OPEN, with every original criterion preserved.'
route='Reuse was checked against the native separating-residue-coordinate genus inequality, original regular prolongation, residue-coordinate separability and newly proved original Gamma1 degree preservation. A single prolongation (the family indexed by Fin 1) suffices. General Kummer families, new Riemann-Roch infrastructure and unrelated constant-field transport are unnecessary for this half of genus preservation.'
write(report,'# Original Gamma1 residue genus upper bound — 29 October 2026\n\n'+chain+'\n\n'+'\n\n'.join(discharged)+'\n\n'+route+'\n\nThe versioned module passes its public axiom query, exhaustive private/generated theorem checks and sixteen linters. All 62 required dependencies occur in the declaration-value closure of the actual residue-genus consumer. The failed first elaboration and fresh compiling successor are retained. Canonical ownership and receipts follow separately.\n\n'+remaining+'\n\nThis scope is scratch-audited; production promotion and assembled verification are pending. Frozen source, root pins, proof limits and the owner-only synchronization BAT remain unchanged.\n')
refs=['source-gamma-one-degree-1-scratch-receipt.json','gamma-one-genus-upper-preflight-config-1720.json',report]
routeobj=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain=chain,reuseChecked=[dict(path=str(s/n),sha256=sha(s/n)) for n in refs],shorterRoute=route,assumptionsToDischarge=discharged,remaining=remaining,externalBuild=False,externalImport=False,rootPinsChanged=False,proofLimitsChanged=False)
rf='source-gamma-one-genus-upper-audit-route-1722.json';write(rf,json.dumps(routeobj,indent=2)+'\n')
c=(s/'record_siegel_function_1580.py').read_text(encoding='utf-8')
for a,b in [('source-siegel-function-1',stem),('SourceSiegelFunctionAudit1','SourceGammaOneGenusUpperAudit1'),('SourceSiegelFunctionDependencyAudit1','SourceGammaOneGenusUpperDependencyAudit1'),('SourceSiegelFunctionScratchOwnership1580','SourceGammaOneGenusUpperScratchOwnership1722'),('source-siegel-function-audit-route-1580',rf[:-5]),('SIEGEL FUNCTION','GAMMA ONE GENUS UPPER'),('20261028','20261029'),('2026-10-28','2026-10-29')]:c=c.replace(a,b)
nm,nq,ne=len(mods),len(cfg['queries']),len(cfg['proofEdges']);assert (nm,nq,ne)==(1,1,62)
c=c.replace('(19, 101, 110)',str((nm,nq,ne))).replace('modules=19',f'modules={nm}').replace('queries=101',f'queries={nq}').replace('linterScopes=19',f'linterScopes={nm}').replace("text.count('with 16 linters') == 19",f"text.count('with 16 linters') == {nm}").replace('all 110 required',f'all {ne} required').replace('requiredProofValueEdges=110',f'requiredProofValueEdges={ne}').replace('proofEdges=110',f'proofEdges={ne}')
ast.parse(c);write('record_gamma_one_genus_upper_1722.py',c)
c=(s/'audit_siegel_function_1580.ps1').read_text(encoding='utf-8')
for a,b in [('SourceSiegelFunctionAudit1','SourceGammaOneGenusUpperAudit1'),('SourceSiegelFunctionDependencyAudit1','SourceGammaOneGenusUpperDependencyAudit1'),('SourceSiegelFunctionScratchOwnership1580','SourceGammaOneGenusUpperScratchOwnership1722'),('record_siegel_function_1580','record_gamma_one_genus_upper_1722')]:c=c.replace(a,b)
write('audit_gamma_one_genus_upper_1722.ps1',c)
c=(s/'build_siegel_function_canonical_1580.ps1').read_text(encoding='utf-8')
c=re.sub(r'\$names=@\([^\n]+\)',"$names=@("+','.join(repr(m) for m in mods)+')',c).replace("$ev=$base+'-1580'","$ev=$base+'-1722'").replace('audit_siegel_function_1580','audit_gamma_one_genus_upper_1722')
write('build_gamma_one_genus_upper_canonical_1722.ps1',c)
print(json.dumps(dict(modules=nm,queries=nq,edges=ne,status='Canonical statements, mathematical bodies and comments frozen.')))
