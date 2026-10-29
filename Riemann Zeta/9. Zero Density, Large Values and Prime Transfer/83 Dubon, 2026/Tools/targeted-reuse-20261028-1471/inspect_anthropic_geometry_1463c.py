from pathlib import Path
import re,json
s=Path(__file__).parent
out=[]
for f in sorted((s/'anthropic-gamma-one-geometry-1463b').glob('*.lean.txt')):
 t=f.read_text(encoding='utf-8')
 lines=t.splitlines()
 i=next(i for i,l in enumerate(lines) if l.startswith('theorem solution'))
 text='\n'.join([l for l in lines[:i] if l.startswith('import ')])+ '\n'+'\n'.join(lines[i:])
 out.append('\nFILE '+f.name+'\n'+text)
f=s/'anthropic-geometry-solutions-1463c.txt'
with f.open('x',encoding='utf-8') as h:h.write('\n\n'.join(out)+'\n')
print(f)
for f in sorted((s/'anthropic-gamma-one-geometry-1463b').glob('*.lean.txt')):
 t=f.read_text(encoding='utf-8')
 matches=[(i+1,l[:220]) for i,l in enumerate(t.splitlines()) if re.search(r'\b(sorry|admit|axiom|constant|unsafe|native_decide|implemented_by)\b|sorryAx',l)]
 print(json.dumps(dict(file=f.name,lines=len(t.splitlines()),prohibitedLexicalMatches=matches),ensure_ascii=False))
