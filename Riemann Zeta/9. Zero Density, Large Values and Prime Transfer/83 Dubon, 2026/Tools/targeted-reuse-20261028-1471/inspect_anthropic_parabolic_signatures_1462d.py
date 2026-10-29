from pathlib import Path
import re
s=Path(__file__).parent
out=[]
for f in sorted((s/'anthropic-parabolic-candidates-1462c').glob('*.lean.txt')):
 c=f.read_text(encoding='utf-8');starts=list(re.finditer(r'^theorem solution\b',c,re.M));assert starts,f
 a=starts[-1].start();b=c.index(':=',a)
 out.append('\nFILE '+f.name+'\n'+'\n'.join(re.findall(r'^import .*$',c,re.M))+'\n'+c[a:b+2]+'\n')
t=s/'anthropic-parabolic-signatures-1462d.txt';assert not t.exists();t.write_text('\n'.join(out),encoding='utf-8')
print(t.read_text(encoding='utf-8'))
