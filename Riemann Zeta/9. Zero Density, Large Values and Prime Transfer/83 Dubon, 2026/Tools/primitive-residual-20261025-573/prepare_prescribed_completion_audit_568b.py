from pathlib import Path
import json,hashlib,re
p=Path(__file__).parent
cfg=json.loads((p/'source-original-prescribed-completion-11-audit-config.json').read_text(encoding='utf-8'))
for name in cfg['modules']:
 f=p/(name+'.lean')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,name
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,name
cfg['documentationRepair']=str(p/'prescribed-completion-documentation-successor-568b.json')
f=p/'source-original-prescribed-completion-11-audit-config-568b.json';assert not f.exists();f.write_text(json.dumps(cfg,indent=2)+'\n',encoding='utf-8')
for suffix in ['Audit','DependencyAudit']:
 old=p/('SourceOriginalPrescribedCompletion'+suffix+'11.lean')
 new=p/('SourceOriginalPrescribedCompletion'+suffix+'11b.lean');assert not new.exists()
 new.write_bytes(old.read_bytes())
rd=json.loads((p/'prescribed-completion-route-568.json').read_text(encoding='utf-8'))
rd['documentationRepair']=cfg['documentationRepair']
f=p/'prescribed-completion-route-568b.json';assert not f.exists();f.write_text(json.dumps(rd,indent=2)+'\n',encoding='utf-8')
print('Fresh public and VALUE-only audit sources prepared; original failed audit retained.')
