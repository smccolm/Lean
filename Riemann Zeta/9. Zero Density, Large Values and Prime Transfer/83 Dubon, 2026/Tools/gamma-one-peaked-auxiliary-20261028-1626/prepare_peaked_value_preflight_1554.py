from pathlib import Path
import json,re
s=Path(__file__).parent
cfg=json.loads((s/'peaked-exponent-preflight-config-1552.json').read_text(encoding='utf-8'))
ns='Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.'
roots=[ns+'exists_peaked_exponent_on_actual_cusps']
edges=cfg['theorems']+cfg['constructions']+['hasSum_one_div_nat_pow_mul_cos','DirichletCharacter.LSeries_ne_zero_of_one_lt_re','ZMod.dft_injective','ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq','Dubon2026.SourceFunctionField.GammaOne.mem_plusMinus_iff']
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
c=(s/'SourceIntegralTraceDependencyAudit1.lean').read_text(encoding='utf-8')
c='\n'.join('import '+m for m in cfg['modules'])+'\nimport Mathlib.Tactic\n'+c[c.index('\nopen Lean'):]
for k,v in [('roots',roots),('localModules',cfg['modules']),('required',edges)]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
start=c.index(' occur in the ');end=c.index('; DUB17--20 OPEN.',start)
c=c[:start]+' occur in the proof value closure of the actual Gamma1 cusp exponent construction. Analytic Siegel product construction and expansions remain open'+c[end:]
c=c.replace('INTEGRAL TRACE','PEAKED EXPONENT PREFLIGHT')
def write(n,t):
 f=s/n;assert not f.exists();f.write_text(t,encoding='utf-8')
write('SourcePeakedExponentValuePreflight1554.lean',c)
c=(s/'audit_peaked_exponent_preflight_1552.ps1').read_text(encoding='utf-8').replace('SourcePeakedExponentPreflight1552','SourcePeakedExponentValuePreflight1554')
write('audit_peaked_value_preflight_1554.ps1',c)
