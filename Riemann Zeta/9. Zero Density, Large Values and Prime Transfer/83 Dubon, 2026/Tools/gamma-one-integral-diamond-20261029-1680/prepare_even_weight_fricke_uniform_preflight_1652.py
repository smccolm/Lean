from pathlib import Path
import json,re
s=Path(__file__).parent
cfg=json.loads((s/'even-weight-fricke-uniform-preflight-config-1651.json').read_text(encoding='utf-8'))
up=list(json.loads((s/'even-weight-fricke-trace-versions-1643.json').read_text(encoding='utf-8')))
cfg['localModules']=cfg['modules']+up
def write(n,c):
 p=s/n; assert not p.exists(),p; p.write_text(c,encoding='utf-8')
arr=lambda xs:'#['+', '.join('`'+x for x in xs)+']'
for kind in ['Preflight','ValuePreflight']:
 old='SourceEvenWeightFrickeUniform'+kind+'1651'
 new='SourceEvenWeightFrickeUniform'+kind+'1652'
 c=(s/(old+'.lean')).read_text(encoding='utf-8')
 if kind=='ValuePreflight':
  c=re.sub(r'let localModules : Array Name := #\[[^\n]*\]','let localModules : Array Name := '+arr(cfg['localModules']),c)
  start=c.index(' occur in the ');end=c.index('; DUB17--20 OPEN.',start)
  c=c[:start]+' occur in the proof value closure of the actual uniform even-weight Fricke integrality consumer. The actual trace constructs coefficient algebraicity; integral cusp-span descent and discriminant cancellation construct a common denominator; proved arithmetic gives one level power for every coefficient. Full slash integrality, reduced field action and degree/genus remain open'+c[end:]
 write(new+'.lean',c)
 c=(s/('audit_'+old+'_1651.ps1')).read_text(encoding='utf-8').replace(old,new)
 write('audit_'+new+'_1652.ps1',c)
write('audit_even_weight_fricke_uniform_preflight_1652.ps1',(s/'audit_even_weight_fricke_uniform_preflight_1651.ps1').read_text(encoding='utf-8').replace('1651','1652'))
write('even-weight-fricke-uniform-preflight-config-1652.json',json.dumps(cfg,indent=2)+'\n')
write('even-weight-fricke-uniform-audit-correction-1652.json',json.dumps(dict(previous='1651',failure='VALUE traversal stopped at already audited canonical scratch Fricke trace modules. Public, exhaustive and sixteen-linter audit passed; the missing dependencies were not traversed.',correction='Add the six actual imported canonical scratch modules to local VALUE traversal. Preserve every required edge and the failed evidence. Correct stale audit message: common denominator is constructed.',requiredEdgesUnchanged=cfg['proofEdges']),indent=2)+'\n')
print('Prepared fresh expanded traversal; all required proof edges preserved.')
