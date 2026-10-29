from pathlib import Path
s=Path(__file__).parent
t=(s/'fetch_anthropic_gamma_one_geometry_1463b.py').read_text(encoding='utf-8')
start=t.index('names=[');end=t.index('\nknown=',start)
names=['S_ModularCurve_exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0','S_ModularCurve_two_mul_index_le_sum_ordDiff_D_add_natCard_doubleCoset_of_lt_five','S_ModularCurve_card_fibres_jqModC_qExpFunctionFieldC_gammaH_le_natCard_doubleCoset']
t=t[:start]+'names='+repr(names)+t[end:]
t=t.replace('anthropic-gamma-one-geometry-1463b','anthropic-integral-slash-1467')
with (s/'fetch_anthropic_integral_slash_1467.py').open('x',encoding='utf-8') as h:h.write(t)
