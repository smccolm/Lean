from pathlib import Path
s=Path(__file__).parent;a=s/'fetch_trace_dependencies_1510.py';b=s/'fetch_peaked_core_dependencies_1533.py';assert not b.exists()
t=a.read_text(encoding='utf-8');start=t.index('names=');end=t.index('\nknown=',start)
names=['S_ModularCurve_SiegelUnit_exists_peaked_exponent','S_CongruenceSubgroup_mem_or_neg_mem_Gamma1_iff_and_exists_T_zpow_S_inv_iff','S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow','S_ModularCurve_SiegelUnit_qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow','S_ModularCurve_SiegelUnit_isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow']
t=t[:start]+'names='+repr(names)+t[end:]
b.write_text(t.replace('anthropic-trace-dependencies-1510','anthropic-peaked-core-1533'),encoding='utf-8')
