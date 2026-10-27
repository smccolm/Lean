from pathlib import Path
import json,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
old=p/'SourceGammaOneCyclotomicConjugationDependencyAudit13.lean'
new=p/'SourceGammaOneCyclotomicConjugationDependencyAudit13V2.lean'
cfgp=p/'source-gamma-one-cyclotomic-conjugation-13-audit-config.json'
cfgnew=p/'source-gamma-one-cyclotomic-conjugation-13-audit-config-v2.json'
oldname='Dubon2026.SourceFunctionField.qExpansion_coeff_width'
newname='Dubon2026.SourceFricke.qExpansion_coeff_width'
assert not new.exists() and not cfgnew.exists()
s=old.read_text(encoding='utf-8');assert s.count(oldname)==1
new.write_text(s.replace(oldname,newname),encoding='utf-8')
cfg=json.loads(cfgp.read_text());assert oldname in cfg['proofEdges']
cfg['proofEdges']=[newname if n==oldname else n for n in cfg['proofEdges']]
cfg['auditCorrection']={'reason':'The required width-change theorem is in SourceFricke, not SourceFunctionField. The original failed VALUE-only audit is retained. Only its incorrectly qualified required name changes; no mathematical source or proof edge is removed.','originalAudit':str(old),'failedLog':str(old.with_suffix('.log')),'failedLogSha256':hashlib.sha256(old.with_suffix('.log').read_bytes()).hexdigest().upper(),'successorAudit':str(new)}
cfgnew.write_text(json.dumps(cfg,indent=2)+'\n',encoding='utf-8')
print('Prepared namespace-corrected dependency audit with all 43 required edges retained')
