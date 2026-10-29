from pathlib import Path
import json,re
s=Path(__file__).parent
t=json.loads((s/'anthropic-parabolic-tree-1462/sol-tree.json').read_text(encoding='utf-8'))
assert not t.get('truncated',False)
paths=[x['path'] for x in t['tree'] if x['path'].endswith('.lean')]
patterns=[r'H1par|coeffParabolic|ParabolicCocycle',r'(coind|corestr|transfer|restrict).*(surject|inject)',r'(surject|inject).*(coind|corestr|transfer|restrict)']
rows={pat:[x for x in paths if re.search(pat,x,re.I)] for pat in patterns}
out=s/'anthropic-parabolic-name-search-1462b.json';assert not out.exists();out.write_text(json.dumps(rows,indent=2)+'\n',encoding='utf-8')
print(json.dumps(rows,indent=2))
