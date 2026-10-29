from pathlib import Path
from datetime import datetime,timezone
import ast,json,re,hashlib
s=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
versions=json.loads((s/'reduced-diamond-action-versions-1694.json').read_text(encoding='utf-8'))
mods=list(versions)
for n in ['SourceReducedDiamondActionPreflight1694','SourceReducedDiamondActionValuePreflight1694']:
 f=s/(n+'.log');assert f.with_suffix('.exit').read_text().strip()=='0'
 assert not re.search(r'warning:|error(?:\(|:)|PANIC|Try this:|sorryAx|Found [1-9]',f.read_text(encoding='utf-16'))
def write(n,t):
 f=s/n;assert not f.exists(),f;f.write_text(t,encoding='utf-8')
adjacent=json.loads((s/'even-weight-integral-diamond-versions-1669.json').read_text(encoding='utf-8'))
for m,v in versions.items():
 f=s/(m+v+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 c=f.read_text(encoding='utf-8')
 for n,ver in {**versions,**adjacent}.items():c=c.replace('import '+n+ver+'\n','import '+n+'\n')
 write(m+'.lean',c)
write('reduced-diamond-action-versions-1700.json',json.dumps(versions,indent=2)+'\n')
cfg=json.loads((s/'reduced-diamond-action-preflight-config-1694.json').read_text(encoding='utf-8'))
up=[]
for f in ['even-weight-fricke-trace-versions-1643.json','even-weight-fricke-uniform-versions-1653.json','even-weight-full-slash-versions-1661.json','even-weight-integral-diamond-versions-1669.json']:
 up+=list(json.loads((s/f).read_text(encoding='utf-8')))
cfg.update(modules=mods,queries=cfg['theorems']+cfg['constructions'],localModules=mods+up,separatelyAxiomChecked=[],compileEvidence={m:m+'-1700' for m in mods})
stem='source-reduced-diamond-action-1';write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
for a,b in [('SourceReducedDiamondActionPreflight1694','SourceReducedDiamondActionAudit1'),('SourceReducedDiamondActionValuePreflight1694','SourceReducedDiamondActionDependencyAudit1')]:
 c=(s/(a+'.lean')).read_text(encoding='utf-8')
 for n,v in {**versions,**adjacent}.items():c=c.replace(n+v,n)
 for key in ['theorems','constructions','roots','localModules']:
  c=re.sub(r'let '+key+r' : Array Name := #\[[^\n]*\]','let '+key+' : Array Name := '+arr(cfg[key]),c)
 c=re.sub(r'let required : Array Name := #\[[^\n]*\]','let required : Array Name := '+arr(cfg['proofEdges']),c)
 c=c.replace('REDUCED DIAMOND ACTION PREFLIGHT','REDUCED DIAMOND ACTION');write(b+'.lean',c)
c=(s/'SourceIntegralTraceScratchOwnership1532.lean').read_text(encoding='utf-8')
c='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+c[c.index('\nopen Lean'):]
c=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),c)
write('SourceReducedDiamondActionScratchOwnership1700.lean',c)
report='Dubon Original Reduced Diamond Action Assessment 2026-10-29.md'
chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight characteristic-zero association -> finite homogeneous Gamma1 Hecke-character realization -> original degree/genus preservation -> signed-index lower bound -> actual reduced diamond field action.'
discharged=['The literal reduction kernel consists exactly of integer series divisible by the coefficient prime. Applying the proved integral diamond construction to the divided form proves zero preservation; the inverse matrix proves its converse.',
'Actual integral diamond witnesses have identical normalized reductions, independently of the clearing exponent and integer series. Products and differences respect this reduction.',
'Any two same-weight integral ratios, even of different even weights, give the same transformed quotient. The cross-products f*g\u2032 and g*f\u2032 have the same weight, so the proved difference law and zero equivalence replace weight casts and a separate exponent-clearing argument.',
'The original reduced ratio set is proved closed under field operations and contains all ZMod constants. Thus every element of the original adjoined field has an actual ratio; native even-weight replacement supplies the needed representatives.',
'The actual pullback remains in the original field and preserves zero, one, addition and multiplication. Native field closure handles the level-power scalar without matching the two clearing exponents.',
'Actual slash composition and the proved ring-homomorphism laws establish composition. The inverse matrix supplies an actual inverse, all ZMod scalars are fixed, and matrix inversion supplies a genuine Gamma0 group action by algebra automorphisms.',
'Native even-weight sign invariance proves that the signed Gamma1 subgroup acts trivially. No reduction-relation, denominator, representative-existence, homomorphism, composition or invertibility premise remains.']
remaining='Exact kernel equality, fixation of the full modular base field in this audited scope, signed-index lower bound and original degree/genus preservation remain required. Integral parabolic transfer, removal of the 3<p and fixed exceptional-prime restrictions, the required two-dimensional characteristic-zero realization, original all-weight association, remaining local/image/regularity inputs, automorphy and literal higher continuation remain open. Acceptance stays 16/20; DUB-17--20 OPEN, with every original criterion preserved.'
route='The pinned Apache-2.0 source is anthropics/fermats-last-theorem at 6e837e75355538c7f80bab5b956861e86c4eacc2, P2M/Sol/S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_zmod.lean. The local original ratio field, actual modularDiamond, even-weight representatives, integral slash consumer and sign invariance are reused. Same-weight cross-products avoid source weight casts. Addition follows from differences. Field closure and ring-homomorphism preservation of natural powers avoid two additional common-exponent constructions. General GammaH, odd-weight auxiliary forms and incidental generalizations are deferred because the exact required Gamma1 chain is served without them.'
write(report,'# Original reduced diamond field action — 29 October 2026\n\n'+chain+'\n\n'+'\n\n'.join(discharged)+'\n\n'+route+'\n\nTwenty versioned modules pass 77 public axiom queries, exhaustive private/generated theorem checks and sixteen linters each. All 98 required dependencies occur in the declaration-value closure of the actual action and its explicit quotient, zero and signed-kernel consumers. The first preflight found five missing field documentation strings; fresh successors add them and preserve all mathematical statements and proof bodies. Both the failure and the full corrected preflight are retained. Canonical ownership and receipts follow separately.\n\n'+remaining+'\n\nThis scope is scratch-audited; production promotion and assembled verification are pending. Frozen source, root pins, proof limits and the owner-only synchronization BAT remain unchanged.\n')
refs=['anthropic-reduced-field-action-1662/manifest.json','reduced-diamond-native-reuse-review-1663.json','reduced-ratio-shorter-route-1676.json','reduced-diamond-action-doc-repair-1693.json',report]
routeobj=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain=chain,reuseChecked=[dict(path=str(s/n),sha256=sha(s/n)) for n in refs],shorterRoute=route,assumptionsToDischarge=discharged,remaining=remaining,externalBuild=False,externalImport=False,rootPinsChanged=False,proofLimitsChanged=False)
rf='source-reduced-diamond-action-audit-route-1700.json';write(rf,json.dumps(routeobj,indent=2)+'\n')
c=(s/'record_siegel_function_1580.py').read_text(encoding='utf-8')
for a,b in [('source-siegel-function-1',stem),('SourceSiegelFunctionAudit1','SourceReducedDiamondActionAudit1'),('SourceSiegelFunctionDependencyAudit1','SourceReducedDiamondActionDependencyAudit1'),('SourceSiegelFunctionScratchOwnership1580','SourceReducedDiamondActionScratchOwnership1700'),('source-siegel-function-audit-route-1580',rf[:-5]),('SIEGEL FUNCTION','REDUCED DIAMOND ACTION'),('20261028','20261029'),('2026-10-28','2026-10-29')]:c=c.replace(a,b)
nm,nq,ne=len(mods),len(cfg['queries']),len(cfg['proofEdges']);assert (nm,nq,ne)==(20,77,98)
c=c.replace('(19, 101, 110)',str((nm,nq,ne))).replace('modules=19',f'modules={nm}').replace('queries=101',f'queries={nq}').replace('linterScopes=19',f'linterScopes={nm}').replace("text.count('with 16 linters') == 19",f"text.count('with 16 linters') == {nm}").replace('all 110 required',f'all {ne} required').replace('requiredProofValueEdges=110',f'requiredProofValueEdges={ne}').replace('proofEdges=110',f'proofEdges={ne}')
ast.parse(c);write('record_reduced_diamond_action_1700.py',c)
c=(s/'audit_siegel_function_1580.ps1').read_text(encoding='utf-8')
for a,b in [('SourceSiegelFunctionAudit1','SourceReducedDiamondActionAudit1'),('SourceSiegelFunctionDependencyAudit1','SourceReducedDiamondActionDependencyAudit1'),('SourceSiegelFunctionScratchOwnership1580','SourceReducedDiamondActionScratchOwnership1700'),('record_siegel_function_1580','record_reduced_diamond_action_1700')]:c=c.replace(a,b)
write('audit_reduced_diamond_action_1700.ps1',c)
c=(s/'build_siegel_function_canonical_1580.ps1').read_text(encoding='utf-8')
c=re.sub(r'\$names=@\([^\n]+\)',"$names=@("+','.join(repr(m) for m in mods)+')',c).replace("$ev=$base+'-1580'","$ev=$base+'-1700'").replace('audit_siegel_function_1580','audit_reduced_diamond_action_1700')
write('build_reduced_diamond_action_canonical_1700.ps1',c)
print(json.dumps(dict(modules=nm,queries=nq,edges=ne,status='Canonical statements, mathematical bodies and comments frozen.')))
