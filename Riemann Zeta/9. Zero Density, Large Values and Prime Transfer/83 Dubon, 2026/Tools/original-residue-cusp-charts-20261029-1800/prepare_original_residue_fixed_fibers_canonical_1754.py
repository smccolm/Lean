from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, re
p=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
versions=json.loads((p/'original-residue-fixed-fibers-versions-1749.json').read_text())
for n in ['SourceOriginalResidueFixedFibersPreflight1752','SourceOriginalResidueFixedFibersValuePreflight1752']:
 f=p/(n+'.log');assert f.with_suffix('.exit').read_text().strip()=='0'
 assert not re.search(r'warning:|error(?:\(|:)|PANIC|Try this:|sorryAx|Found [1-9]',f.read_text(encoding='utf-16'))
def write(n,t):
 f=p/n;assert not f.exists(),f;f.write_text(t,encoding='utf-8')
def canonical(s):
 for n,v in versions.items():s=s.replace(n+v,n)
 return s
mods=list(versions)
for n,v in versions.items():
 f=p/(n+v+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0
 s=f.read_text(encoding='utf-8')
 for m,w in versions.items():s=s.replace('import '+m+w+'\n','import '+m+'\n')
 write(n+'.lean',s)
write('original-residue-fixed-fibers-versions-1754.json',json.dumps(versions,indent=2)+'\n')
cfg=json.loads(canonical((p/'original-residue-fixed-fibers-preflight-config-1752.json').read_text()))
cfg['compileEvidence']={m:m+'-1754' for m in mods}
stem='source-original-residue-fixed-fibers-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
for a,b in [('SourceOriginalResidueFixedFibersPreflight1752','SourceOriginalResidueFixedFibersAudit1'),('SourceOriginalResidueFixedFibersValuePreflight1752','SourceOriginalResidueFixedFibersDependencyAudit1')]:
 s=canonical((p/(a+'.lean')).read_text()).replace('FIXED FIBERS PREFLIGHT','FIXED FIBERS')
 write(b+'.lean',s)
arr=lambda xs:'#['+', '.join('`'+x for x in xs)+']'
s=(p/'SourceReducedDiamondScalarScratchOwnership1741.lean').read_text()
s='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+s[s.index('\nopen Lean'):]
s=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),s)
write('SourceOriginalResidueFixedFibersScratchOwnership1754.lean',s)
chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight characteristic-zero association -> finite homogeneous Gamma1 Hecke-character realization -> original genus preservation -> reverse genus inequality -> residue fiber bounds -> actual residue diamond fixed field and full-base fiber transitivity.'
discharged=[
 'The actual original residue coordinate degree is the signed Gamma1 index, by the already proved original degree preservation and residue-field equality.',
 'The diamond fixed field equals the full modular base: its proved Artin degree, original coordinate degree and the native full-base degree force relative degree one. The valuation-residue consumer discharges the coordinate-degree input.',
 'Native Galois place transitivity over that fixed field and Artin automorphism surjectivity produce a literal Gamma0 matrix relating any two actual residue places above the same full-base place. No action, fixed-field identity, Galois transitivity or degree certificate remains a hypothesis in the actual residue consumer.'
]
remaining='The finite elliptic and cusp stabilizer charts, exact residue fiber bounds and reverse genus inequality remain open. Original genus preservation, integral parabolic transfer, exceptional-prime removal, two-dimensional characteristic-zero realization, original all-weight association, local/image/regularity inputs, automorphy and literal higher continuation remain required. Acceptance remains 16/20; DUB-17--20 OPEN under the full original completion contract.'
route='Reuse the already proved original coordinate degree and native full-base degree to identify the fixed field; this avoids the longer external invariant-function construction. Native SourceCurveGaloisFiberTransitivity and Mathlib FixedPoints.toAlgAut_bijective avoid reconstructing the integral-closure prime/place correspondence. Six versioned modules pass public/private/generated axiom checks and sixteen linters each. All 22 required dependencies are checked in the value closures of two actual consumers and the explicitly audited actual action construction; the definitional construction is a separate root because its name reduces away in the consumer values. The failed predecessor audit and fresh refinement are retained; no check was removed.'
report='Dubon Original Residue Fixed Field and Fiber Transitivity Assessment 2026-10-29.md'
write(report,'# Original residue fixed field and fiber transitivity — 29 October 2026\n\n'+chain+'\n\n'+'\n\n'.join(discharged)+'\n\n'+route+'\n\n'+remaining+'\n\nScratch-audited only; production promotion and assembled verification remain pending. Frozen paper, root pins, proof limits and owner-only BAT are unchanged.\n')
refs=['fixed-field-fiber-route-1743.json','original-residue-fixed-fibers-audit-refinement-1752.json','source-reduced-diamond-scalar-1-scratch-receipt.json','anthropic-diamond-place-charts-1746/manifest.json','anthropic-original-residue-charts-1750/manifest.json','anthropic-residue-chart-construction-1751/manifest.json',report]
rf='source-original-residue-fixed-fibers-audit-route-1754'
write(rf+'.json',json.dumps(dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain=chain,reuseChecked=[dict(path=str(p/n),sha256=sha(p/n)) for n in refs],shorterRoute=route,assumptionsToDischarge=discharged,remaining=remaining,externalBuild=False,externalImport=False,rootPinsChanged=False,proofLimitsChanged=False),indent=2)+'\n')
s=(p/'record_reduced_diamond_scalar_1741.py').read_text()
for a,b in [('source-reduced-diamond-scalar-1',stem),('SourceReducedDiamondScalarAudit1','SourceOriginalResidueFixedFibersAudit1'),('SourceReducedDiamondScalarDependencyAudit1','SourceOriginalResidueFixedFibersDependencyAudit1'),('SourceReducedDiamondScalarScratchOwnership1741','SourceOriginalResidueFixedFibersScratchOwnership1754'),('source-reduced-diamond-scalar-audit-route-1741',rf),('REDUCED DIAMOND SCALAR','ORIGINAL RESIDUE FIXED FIBERS')]:s=s.replace(a,b)
for a,b in [('(8, 26, 61)','(6, 7, 22)'),('modules=8','modules=6'),('queries=26','queries=7'),('linterScopes=8','linterScopes=6'),("text.count('with 16 linters') == 8","text.count('with 16 linters') == 6"),('all 61 required','all 22 required'),('requiredProofValueEdges=61','requiredProofValueEdges=22'),('proofEdges=61','proofEdges=22')]:s=s.replace(a,b)
ast.parse(s);write('record_original_residue_fixed_fibers_1754.py',s)
s=(p/'audit_reduced_diamond_scalar_1741.ps1').read_text()
for a,b in [('SourceReducedDiamondScalarAudit1','SourceOriginalResidueFixedFibersAudit1'),('SourceReducedDiamondScalarDependencyAudit1','SourceOriginalResidueFixedFibersDependencyAudit1'),('SourceReducedDiamondScalarScratchOwnership1741','SourceOriginalResidueFixedFibersScratchOwnership1754'),('record_reduced_diamond_scalar_1741','record_original_residue_fixed_fibers_1754')]:s=s.replace(a,b)
write('audit_original_residue_fixed_fibers_1754.ps1',s)
s=(p/'build_reduced_diamond_scalar_canonical_1741.ps1').read_text()
s=re.sub(r'\$names=@\([^\n]+\)',"$names=@("+','.join(repr(m) for m in mods)+')',s).replace("$ev=$base+'-1741'","$ev=$base+'-1754'").replace('audit_reduced_diamond_scalar_1741','audit_original_residue_fixed_fibers_1754')
write('build_original_residue_fixed_fibers_canonical_1754.ps1',s)
print(json.dumps(dict(modules=6,queries=7,valueEdges=22,status='Canonical mathematical bodies and comments frozen; build/audit pending')))
