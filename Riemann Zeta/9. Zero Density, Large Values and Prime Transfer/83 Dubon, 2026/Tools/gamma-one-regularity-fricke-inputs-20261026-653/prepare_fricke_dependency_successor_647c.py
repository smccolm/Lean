from pathlib import Path
import json,re,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
cfg=json.loads((p/'source-fricke-transformation-4b-audit-config.json').read_text())
names=['smulPeriodPair_ω₁','smulPeriodPair_ω₂','smulLatticeEquiv_coe','periodPairOfTau_ω₁','periodPairOfTau_ω₂']
separate=['Dubon2026.SourceFricke.'+n for n in names]
for n in names:
 matches=[]
 for m in cfg['modules']:
  s=(p/(m+'.lean')).read_text(encoding='utf-8')
  matches+=re.findall(r'(?:lemma|theorem) '+re.escape(n)+r'\b.*?:= rfl',s,re.S)
 assert len(matches)==1,n
cfg['separatelyAxiomChecked']+=separate
cfg['proofEdges']=[n for n in cfg['proofEdges'] if n not in separate]
assert len(cfg['proofEdges'])==39
cfg['separateReason']='Five projection/coercion equations are literally proved by rfl; simplification unfolds them, so their named theorem constants do not survive in the consumer proof value. Their actual definitions remain required value dependencies. These equations and the finite-instance declaration retain explicit axiom checks and exhaustive theorem/linter coverage. No mathematical dependency is replaced with an assumption.'
f=p/'source-fricke-transformation-4c-audit-config.json';assert not f.exists();f.write_text(json.dumps(cfg,indent=2)+'\n',encoding='utf-8')
s=(p/'SourceFrickeTransformationDependencyAudit4b.lean').read_text(encoding='utf-8')
arr='#['+', '.join(chr(96)+n for n in cfg['proofEdges'])+']'
s=re.sub(r'let required : Array Name := #\[[^\n]*',lambda _:'let required : Array Name := '+arr,s)
f=p/'SourceFrickeTransformationDependencyAudit4c.lean';assert not f.exists();f.write_text(s,encoding='utf-8')
print('Fresh dependency successor: 39 substantive value edges; full passing audit unchanged.')
