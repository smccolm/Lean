from pathlib import Path
import ast,hashlib,json
p=Path(__file__).parent
s=(p/'record_gamma_one_differential_realization_697.py').read_text(encoding='utf-8')
repl={'source-gamma-one-cusp-differential-realization-6':'source-gamma-one-local-holomorphy-12','SourceGammaOneCuspDifferentialRealizationAudit6':'SourceGammaOneLocalHolomorphyAudit12','SourceGammaOneCuspDifferentialRealizationDependencyAudit6':'SourceGammaOneLocalHolomorphyDependencyAudit12','SOURCE GAMMA ONE CUSP DIFFERENTIAL REALIZATION':'SOURCE GAMMA ONE LOCAL HOLOMORPHY','gamma-one-cusp-differential-realization-audit-route-697.json':'gamma-one-local-holomorphy-audit-route-700.json','(6, 8, 15)':'(12, 35, 46)',' == 6':' == 12','all 15 required proof dependencies':'all 46 required proof dependencies','linterScopes=6':'linterScopes=12','requiredProofValueEdges=15':'requiredProofValueEdges=46','modules=6, queries=8':'modules=12, queries=35','proofEdges=15':'proofEdges=46'}
for a,b in repl.items():assert a in s,a;s=s.replace(a,b)
s=s.replace('.read_text())',".read_text(encoding='utf-8'))")
ast.parse(s)
f=p/'record_gamma_one_local_holomorphy_700.py'
with f.open('x',encoding='utf-8',newline='\n') as out:out.write(s)
print(json.dumps(dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest().upper(),scope='12 modules, 35 queries, 46 proof VALUE edges',productionMutation=False)))