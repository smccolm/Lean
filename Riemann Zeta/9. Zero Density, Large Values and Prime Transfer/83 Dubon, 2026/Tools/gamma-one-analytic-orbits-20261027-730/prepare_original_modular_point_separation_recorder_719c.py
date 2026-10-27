from pathlib import Path
import json, ast
p=Path(__file__).parent
cfg=json.loads((p/'source-original-modular-point-separation-1-audit-config.json').read_text(encoding='utf-8'))
assert (len(cfg['modules']),len(cfg['queries']),len(cfg['proofEdges']))==(1,4,11)
for n in ['SourceOriginalModularPointSeparationAudit1.lean','SourceOriginalModularPointSeparationDependencyAudit1.lean','original-modular-point-separation-audit-route-719.json']:
    assert (p/n).exists()
s=(p/'record_gamma_one_fourier_converse_702.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-fourier-converse-2','source-original-modular-point-separation-1'),('SourceGammaOneFourierConverseAudit2','SourceOriginalModularPointSeparationAudit1'),('SourceGammaOneFourierConverseDependencyAudit2','SourceOriginalModularPointSeparationDependencyAudit1'),('SOURCE GAMMA ONE FOURIER CONVERSE','SOURCE ORIGINAL MODULAR POINT SEPARATION'),('gamma-one-fourier-converse-audit-route-702.json','original-modular-point-separation-audit-route-719.json'),('(2, 2, 10)','(1, 4, 11)'),(' == 2',' == 1'),('all 10 required proof dependencies','all 11 required proof dependencies'),('linterScopes=2','linterScopes=1'),('requiredProofValueEdges=10','requiredProofValueEdges=11'),('modules=2, queries=2','modules=1, queries=4'),('proofEdges=10','proofEdges=11')]:
    assert a in s,a
    s=s.replace(a,b)
ast.parse(s)
with (p/'record_original_modular_point_separation_719.py').open('x',encoding='utf-8',newline='\n') as f:f.write(s)
print('Fresh recorder prepared; existing audits and source untouched.')
