from pathlib import Path
import ast,hashlib,json,re
p=Path(__file__).parent
names=['compare_gamma_one_diamond_quotient_ownership_9161.py','record_source_gamma_one_diamond_quotient_9161.py']
rows=[]
for n in names:
 f=p/n;s=f.read_text(encoding='utf-8');new=re.sub(r'\b26\b','12',s)
 assert new!=s;ast.parse(new);f.write_text(new,encoding='utf-8')
 rows.append(dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest().upper()))
t=p/'gamma-one-diamond-quotient-preexecution-correction-1453b.json';assert not t.exists()
t.write_text(json.dumps(dict(reason='Before any generated script was executed, align the two remaining module-count assertions/receipt fields with all twelve audited modules. No proof, audit scope or executed evidence changed.',files=rows,productionMutation=False),indent=2)+'\n',encoding='utf-8')
print('Corrected unused verifier scope constants; preserved the original preparation and preexecution records.')
