from pathlib import Path
import json,re,hashlib
p=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
cfg=json.loads((p/'source-original-primitive-rank-two-17-audit-config.json').read_text(encoding='utf-8'))
excluded={'Dubon2026.characterIdempotentRankTwoEquiv_symm_val':'SourceCharacterIdempotentRankTwo','Dubon2026.rankTwoBaseChangeEquiv_tmul':'SourceRankTwoBaseChange','Dubon2026.intertwinedRangeEquiv_apply':'SourceIntertwinedRangeEquiv'}
old=p/'SourceOriginalPrimitiveRankTwoDependencyAudit17.log'
assert old.with_suffix('.exit').read_text().strip()=='1'
text=old.read_text(encoding='utf-16')
assert set(re.findall(r'Dubon2026\.[A-Za-z0-9_]+',text))==set(excluded)
assert 'Missing original source proof dependencies' in text
for n,m in excluded.items():
 source=(p/(m+'.lean')).read_text(encoding='utf-8')
 found=re.search(r'^theorem '+re.escape(n.rsplit('.',1)[1])+r'\b.*?(?=\n(?:theorem|def|end)\b|\Z)',source,re.M|re.S)
 assert found and found[0].strip().endswith(':= rfl'),n
cfg['proofEdges']=[n for n in cfg['proofEdges'] if n not in excluded]
assert len(cfg['proofEdges'])==45
cfg['separatelyAxiomCheckedDefinitionalLaws']=dict(names=list(excluded),reason='Each of these three public coordinate identities has proof rfl. The terminal proof reduces through their definitions and does not retain a reference to the named theorem. They remain in the full explicit axiom and exhaustive checks; no transitive named-value dependency is claimed for them.')
source=old.with_suffix('.lean').read_text(encoding='utf-8')
source=re.sub(r'let required : Array Name := #\[[^\n]*','let required : Array Name := #['+', '.join('`'+n for n in cfg['proofEdges'])+']',source)
source=source.replace('Only declaration values are traversed.','Only declaration values are traversed. Three public rfl coordinate identities are separately axiom-checked; their names are not claimed as terminal proof dependencies because definitional reduction removes those references.')
lineage=dict(failedAudit=str(old),failedAuditSha256=sha(old),failedAuditSourceSha256=sha(old.with_suffix('.lean')),failure='The axiom/exhaustive/linter audit passed. The first value audit required named dependencies on three rfl coordinate lemmas whose references are eliminated by definitional reduction. All other 45 required value dependencies were present.',correction=cfg['separatelyAxiomCheckedDefinitionalLaws'],sourceOrOleanChanged=False)
route=json.loads((p/'primitive-rank-two-route-562.json').read_text(encoding='utf-8'));route['dependencyAuditLineage']=lineage
for name,value in [('source-original-primitive-rank-two-17-audit-config-562b.json',json.dumps(cfg,indent=2)+'\n'),('SourceOriginalPrimitiveRankTwoDependencyAudit17b.lean',source),('primitive-rank-two-route-562b.json',json.dumps(route,indent=2)+'\n')]:
 f=p/name;assert not f.exists();f.write_text(value,encoding='utf-8')
print(json.dumps(dict(requiredValueEdges=45,separatelyAxiomCheckedDefinitionalLaws=list(excluded))))
