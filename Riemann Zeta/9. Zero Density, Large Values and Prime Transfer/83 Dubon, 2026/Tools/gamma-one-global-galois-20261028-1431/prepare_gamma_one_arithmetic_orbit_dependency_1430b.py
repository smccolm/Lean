from pathlib import Path
import ast,json
p=Path(__file__).parent
old='source-gamma-one-arithmetic-orbit-1'
new='source-gamma-one-arithmetic-orbit-2'
cfg=json.loads((p/(old+'-audit-config.json')).read_text(encoding='utf-8'))
bad='Dubon2026.GaussReduction.residue_charP_of_prime_mem_nonunits'
good='Dubon2026.SourceFunctionField.GaussReduction.residue_charP_of_prime_mem_nonunits'
assert bad in cfg['proofEdges'];cfg['proofEdges']=[good if x==bad else x for x in cfg['proofEdges']]
def write(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
write(new+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
s=(p/'SourceGammaOneArithmeticOrbitDependencyAudit1.lean').read_text(encoding='utf-8');assert bad in s
write('SourceGammaOneArithmeticOrbitDependencyAudit2.lean',s.replace(bad,good))
s=(p/'record_gamma_one_arithmetic_orbit_1430.py').read_text(encoding='utf-8').replace(old,new).replace('SourceGammaOneArithmeticOrbitDependencyAudit1','SourceGammaOneArithmeticOrbitDependencyAudit2')
ast.parse(s);write('record_gamma_one_arithmetic_orbit_1430b.py',s)
s=(p/'audit_gamma_one_arithmetic_orbit_1430.ps1').read_text(encoding='utf-8')
s=s.replace("'SourceGammaOneArithmeticOrbitAudit1',",'').replace('SourceGammaOneArithmeticOrbitDependencyAudit1','SourceGammaOneArithmeticOrbitDependencyAudit2').replace('record_gamma_one_arithmetic_orbit_1430.py','record_gamma_one_arithmetic_orbit_1430b.py')
assert "'SourceGammaOneArithmeticOrbitAudit1'" not in s
write('audit_gamma_one_arithmetic_orbit_1430b.ps1',s)
write('gamma-one-arithmetic-orbit-dependency-correction-1430b.json',json.dumps(dict(reason='Exact declaration lookup found the residue-characteristic theorem under Dubon2026.SourceFunctionField.GaussReduction. Correct the audit name only; the required proof edge and all mathematical sources remain unchanged. Preserve the first audit source/log and use a fresh dependency audit, config and receipt.',old=bad,new=good,proofEdges=21,productionMutation=False),indent=2)+'\n')
