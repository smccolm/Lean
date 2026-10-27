from pathlib import Path
import ast
p=Path(r'E:\Lean\.tmp\dubon83')
s=(p/'record_fricke_cyclotomic_analytic_transport_687.py').read_text(encoding='utf-8')
s=s.replace('source-fricke-cyclotomic-analytic-transport-5','source-gamma-one-cyclotomic-conjugation-13').replace('fricke-cyclotomic-analytic-transport-route-687','gamma-one-cyclotomic-conjugation-route-688').replace('SourceFrickeCyclotomicAnalyticTransportAudit5','SourceGammaOneCyclotomicConjugationAudit13').replace('SourceFrickeCyclotomicAnalyticTransportDependencyAudit5','SourceGammaOneCyclotomicConjugationDependencyAudit13V2').replace('SOURCE FRICKE CYCLOTOMIC ANALYTIC TRANSPORT','SOURCE GAMMA ONE CYCLOTOMIC CONJUGATION')
s=s.replace('source-gamma-one-cyclotomic-conjugation-13-audit-config.json','source-gamma-one-cyclotomic-conjugation-13-audit-config-v2.json')
s=s.replace('==(5,19,27)','==(13,35,43)').replace('==5','==13').replace('all 27 required','all 43 required').replace('linterScopes=5','linterScopes=13').replace('requiredProofValueEdges=27','requiredProofValueEdges=43').replace('modules=5,queries=19','modules=13,queries=35').replace('proofEdges=27','proofEdges=43')
s=s.replace("review=dict(date=", "review=dict(auditCorrection=cfg['auditCorrection'],date=")
ast.parse(s)
f=p/'record_gamma_one_cyclotomic_conjugation_688.py';assert not f.exists();f.write_text(s,encoding='utf-8')
print('Prepared conjugation receipt recorder preserving original failed audit evidence')
