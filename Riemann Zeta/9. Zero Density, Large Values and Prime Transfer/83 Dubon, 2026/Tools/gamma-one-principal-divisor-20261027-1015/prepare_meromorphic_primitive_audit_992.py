from pathlib import Path
import json, re

p = Path(__file__).parent
cfg = json.loads((p/'source-meromorphic-logarithmic-primitive-1-audit-config.json').read_text(encoding='utf-8'))
assert (len(cfg['modules']),len(cfg['queries']),len(cfg['proofEdges'])) == (5,60,60)
def write(n,s):
    f=p/n
    assert not f.exists(), n
    f.write_text(s,encoding='utf-8')
def array(xs): return '#['+', '.join(chr(96)+x for x in xs)+']'
def imports(s):
    return re.sub(r'\A(?:import [^\n]+\n)+', ''.join('import '+x+'\n' for x in cfg['modules'])+'import Mathlib.Tactic\n',s)
def arr(s,name,xs):
    return re.sub(r'let '+name+r' : Array Name := #[^\n]+','let '+name+' : Array Name := '+array(xs),s)
old='SourceOriginalIntegralPeriodDuality'
new='SourceMeromorphicLogarithmicPrimitive'
s=imports((p/(old+'Audit1b.lean')).read_text(encoding='utf-8'))
s=re.sub(r'(?:#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in cfg['queries']),s)
for key in ['modules','theorems','constructions']:s=arr(s,key,cfg[key])
s=re.sub(r'(?:#lint in [^\n]+\n)+',''.join('#lint in '+x+'\n' for x in cfg['modules']),s)
s=s.replace('Original Integral Period Duality','Meromorphic Logarithmic Primitive').replace('ORIGINAL INTEGRAL PERIOD DUALITY','MEROMORPHIC LOGARITHMIC PRIMITIVE')
write(new+'Audit1.lean',s)
s=imports((p/(old+'DependencyAudit1b.lean')).read_text(encoding='utf-8'))
for name,key in [('roots','roots'),('localModules','localModules'),('required','proofEdges')]:s=arr(s,name,cfg[key])
s=re.sub(r'  logInfo m!"SOURCE [^\n]+', '  logInfo m!"SOURCE MEROMORPHIC LOGARITHMIC PRIMITIVE DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the declaration-VALUE closure of the global meromorphic logarithmic primitive. Local integer-residue expansions produce a global meromorphic function with exact orders and the logarithmic derivative off the divisor. Multiplier covariance, cusp limits and the actual differential input remain. DUB17--20 OPEN."',s)
write(new+'DependencyAudit1.lean',s)
s=imports((p/(old+'ScratchOwnership972.lean')).read_text(encoding='utf-8'))
s=arr(s,'mods',cfg['modules'])
write(new+'ScratchOwnership992.lean',s)
s=(p/'record_source_original_integral_period_duality_972.py').read_text(encoding='utf-8')
s=s.replace('source-original-integral-period-duality-1b','source-meromorphic-logarithmic-primitive-1').replace(old+'Audit1b',new+'Audit1').replace(old+'DependencyAudit1b',new+'DependencyAudit1').replace(old+'ScratchOwnership972',new+'ScratchOwnership992')
s=s.replace('source-original-integral-period-duality-audit-route-972','source-meromorphic-logarithmic-primitive-audit-route-992').replace('SOURCE ORIGINAL INTEGRAL PERIOD DUALITY','SOURCE MEROMORPHIC LOGARITHMIC PRIMITIVE')
s=s.replace('(13, 69, 79)','(5, 60, 60)').replace('== 13','== 5').replace('all 79 required','all 60 required').replace('linterScopes=13','linterScopes=5').replace('requiredProofValueEdges=79','requiredProofValueEdges=60').replace('modules=13, queries=69','modules=5, queries=60').replace('proofEdges=79','proofEdges=60')
write('record_source_meromorphic_logarithmic_primitive_992.py',s)
route=json.loads((p/'source-upper-half-plane-meromorphic-primitive-route-984.json').read_text(encoding='utf-8'))
route['remaining']='Actual algebraic differential exists; its analytic residue realization and exponential cusp decay, multiplicative covariance and cusp limit assembly remain, then the general-multiplier principal-divisor consumer. This scratch scope compiles and is being audited, not yet production-promoted. DUB17--20 OPEN.'
write('source-meromorphic-logarithmic-primitive-audit-route-992.json',json.dumps(route,indent=2)+'\n')
s=(p/'audit_original_integral_period_duality_972.ps1').read_text(encoding='utf-8')
s=s.replace(old+'Audit1b',new+'Audit1').replace(old+'DependencyAudit1b',new+'DependencyAudit1').replace(old+'ScratchOwnership972',new+'ScratchOwnership992').replace('record_source_original_integral_period_duality_972','record_source_meromorphic_logarithmic_primitive_992')
write('audit_meromorphic_logarithmic_primitive_992.ps1',s)
print('Prepared 5-module / 60-query / 60-VALUE-edge audit992')
