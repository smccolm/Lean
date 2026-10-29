from pathlib import Path
s=Path(__file__).parent;a=s/'fetch_anthropic_integral_slash_1467.py';b=s/'fetch_peaked_integrality_dependencies_1498.py'
assert not b.exists()
t=a.read_text(encoding='utf-8')
old="names=['S_ModularCurve_exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0', 'S_ModularCurve_two_mul_index_le_sum_ordDiff_D_add_natCard_doubleCoset_of_lt_five', 'S_ModularCurve_card_fibres_jqModC_qExpFunctionFieldC_gammaH_le_natCard_doubleCoset']"
new="names=['S_ModularForm_qExpansion_slash_coeff_mem_of_peaked_auxiliary', 'S_ModularCurve_exists_gamma1_peaked_auxiliary_form', 'S_ModularCurve_exists_ne_zero_isIntegral_mul_qExpansion_slash_fricke_coeff']"
assert old in t
t=t.replace(old,new).replace('anthropic-integral-slash-1467','anthropic-peaked-integrality-depth-1498')
b.write_text(t,encoding='utf-8')
