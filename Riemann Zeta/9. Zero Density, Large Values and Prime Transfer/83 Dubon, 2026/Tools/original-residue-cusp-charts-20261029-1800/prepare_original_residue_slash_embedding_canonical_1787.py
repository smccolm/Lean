from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, re
p=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
versions=json.loads((p/'original-residue-slash-embedding-versions-1783.json').read_text())
for n in ['SourceOriginalResidueSlashEmbeddingPreflight1783','SourceOriginalResidueSlashEmbeddingValuePreflight1783']:
 f=p/(n+'.log');assert f.with_suffix('.exit').read_text().strip()=='0'
 assert not re.search(r'warning:|error(?:\(|:)|PANIC|Try this:|sorryAx|Found [1-9]',f.read_text(encoding='utf-16'))
def write(n,t):
 f=p/n;assert not f.exists(),f;f.write_text(t,encoding='utf-8')
def canonical(s):
 for n,v in versions.items():s=s.replace(n+v,n)
 for n,v in json.loads((p/'integral-slash-chart-relations-versions-1768.json').read_text()).items():s=s.replace(n+v,n)
 return s
kversions=json.loads((p/'integral-slash-chart-relations-versions-1768.json').read_text())
mods=list(versions)
for n,v in versions.items():
 f=p/(n+v+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0
 s=f.read_text(encoding='utf-8')
 for m,w in (versions | kversions).items():s=s.replace('import '+m+w+'\n','import '+m+'\n')
 write(n+'.lean',s)
write('original-residue-slash-embedding-versions-1787.json',json.dumps(versions,indent=2)+'\n')
cfg=json.loads(canonical((p/'original-residue-slash-embedding-preflight-config-1783.json').read_text()))
cfg['compileEvidence']={m:m+'-1787' for m in mods}
stem='source-original-residue-slash-embedding-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
for a,b in [('SourceOriginalResidueSlashEmbeddingPreflight1783','SourceOriginalResidueSlashEmbeddingAudit1'),('SourceOriginalResidueSlashEmbeddingValuePreflight1783','SourceOriginalResidueSlashEmbeddingDependencyAudit1')]:
 s=canonical((p/(a+'.lean')).read_text()).replace('SLASH EMBEDDING PREFLIGHT','SLASH EMBEDDING')
 write(b+'.lean',s)
arr=lambda xs:'#['+', '.join('`'+x for x in xs)+']'
s=(p/'SourceOriginalResidueFixedFibersScratchOwnership1754.lean').read_text()
s='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+s[s.index('\nopen Lean'):]
s=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),s)
write('SourceOriginalResidueSlashEmbeddingScratchOwnership1787.lean',s)
chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight association -> finite homogeneous Gamma1 Hecke-character realization -> original genus preservation -> reverse genus inequality -> cusp residue fiber bounds -> actual original residue cusp field embedding.'
discharged=[
 'The actual discriminant has nonzero reduction at every cusp, including residue characteristics two and three away from the level. Native width change computes every integral level-one chart.',
 'Actual integral forms of weight 12r divided by the original discriminant power generate the whole original integral-ratio function field, including arbitrary integer-weight representatives. Common discriminant powers transfer all finite linear relations, and the actual cusp values preserve multiplication and one.',
 'The original j belongs to the normalized generators and maps exactly to j(q^N), whose transcendence was already proved. Native monoid-algebra evaluation and the kernel quotient construct the algebra map.',
 'Native fraction-ring algebraicity and tower injectivity extend this map to the full original function field. The actual valuation-residue consumer uses the native finite residue-coordinate upper bound and original ratio inclusion to discharge positive degree. Exact signed-index equality is unnecessary for this embedding. No degree, algebraicity, injectivity or field-embedding certificate remains in that consumer.'
]
remaining='The map is constructed for every supplied algebraic-integer reduction homomorphism and every cusp matrix. Prescribed primitive-root reductions are a separate compiling successor, outside this receipt. Stabilizer equivariance, the residue fiber bounds and reverse genus inequality remain open. Original genus preservation, integral parabolic transfer, exceptional-prime removal, two-dimensional characteristic-zero realization, original all-weight association, local/image/regularity inputs, automorphy and literal higher continuation remain required. Acceptance remains 16/20; DUB-17--20 OPEN under the unchanged full completion contract.'
route='Reuse native discriminant expansions, original finite residue-coordinate degree, width substitution and j transcendence. MonoidAlgebra.lift and RingHom.liftOfRightInverse replace the external span and bilinear-map construction; IsFractionRing.comap_isAlgebraic_iff and Algebra.IsAlgebraic.injective_tower_top replace the separate minimal-polynomial denominator argument. These shorter routes have actual original-residue consumers. Every versioned module passes public/private/generated axiom checks, sixteen linters and all sixty required declaration-value dependencies. Failed versions and fresh successors are retained; no proof limit or audit requirement is weakened.'
report='Dubon Original Residue Cusp Field Embedding Assessment 2026-10-29.md'
write(report,'# Original residue cusp field embedding — 29 October 2026\n\n'+chain+'\n\n'+'\n\n'.join(discharged)+'\n\n'+route+'\n\n'+remaining+'\n\nScratch-audited only; production promotion and assembled verification remain pending. Frozen paper, root pins and owner-only BAT remain unchanged.\n')
refs=['original-residue-slash-embedding-route-1783.json','anthropic-residue-chart-construction-1751/manifest.json','anthropic-chart-field-extension-1762/manifest.json','source-integral-slash-chart-relations-1-scratch-receipt.json',report]
rf='source-original-residue-slash-embedding-audit-route-1787'
write(rf+'.json',json.dumps(dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain=chain,reuseChecked=[dict(path=str(p/n),sha256=sha(p/n)) for n in refs],shorterRoute=route,assumptionsToDischarge=discharged,remaining=remaining,externalBuild=False,externalImport=False,rootPinsChanged=False,proofLimitsChanged=False),indent=2)+'\n')
s=(p/'record_original_residue_fixed_fibers_1754.py').read_text()
for a,b in [('source-original-residue-fixed-fibers-1',stem),('SourceOriginalResidueFixedFibersAudit1','SourceOriginalResidueSlashEmbeddingAudit1'),('SourceOriginalResidueFixedFibersDependencyAudit1','SourceOriginalResidueSlashEmbeddingDependencyAudit1'),('SourceOriginalResidueFixedFibersScratchOwnership1754','SourceOriginalResidueSlashEmbeddingScratchOwnership1787'),('source-original-residue-fixed-fibers-audit-route-1754',rf),('ORIGINAL RESIDUE FIXED FIBERS','ORIGINAL RESIDUE SLASH EMBEDDING')]:s=s.replace(a,b)
for a,b in [('(6, 7, 22)','(15, 43, 60)'),('modules=6','modules=15'),('queries=7','queries=43'),('linterScopes=6','linterScopes=15'),("text.count('with 16 linters') == 6","text.count('with 16 linters') == 15"),('all 22 required','all 60 required'),('requiredProofValueEdges=22','requiredProofValueEdges=60'),('proofEdges=22','proofEdges=60')]:s=s.replace(a,b)
ast.parse(s);write('record_original_residue_slash_embedding_1787.py',s)
s=(p/'audit_original_residue_fixed_fibers_1754.ps1').read_text()
for a,b in [('SourceOriginalResidueFixedFibersAudit1','SourceOriginalResidueSlashEmbeddingAudit1'),('SourceOriginalResidueFixedFibersDependencyAudit1','SourceOriginalResidueSlashEmbeddingDependencyAudit1'),('SourceOriginalResidueFixedFibersScratchOwnership1754','SourceOriginalResidueSlashEmbeddingScratchOwnership1787'),('record_original_residue_fixed_fibers_1754','record_original_residue_slash_embedding_1787')]:s=s.replace(a,b)
write('audit_original_residue_slash_embedding_1787.ps1',s)
s=(p/'build_original_residue_fixed_fibers_canonical_1754.ps1').read_text()
s=re.sub(r'\$names=@\([^\n]+\)',"$names=@("+','.join(repr(m) for m in mods)+')',s).replace("$ev=$base+'-1754'","$ev=$base+'-1787'").replace('audit_original_residue_fixed_fibers_1754','audit_original_residue_slash_embedding_1787')
write('build_original_residue_slash_embedding_canonical_1787.ps1',s)
print(json.dumps(dict(modules=15,queries=43,valueEdges=60,status='Canonical mathematical bodies and comments frozen; build/audit pending')))
