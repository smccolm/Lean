from pathlib import Path
s=Path(__file__).parent;a=s/'fetch_eisenstein_degree_dependency_1495.py';b=s/'fetch_series_coefficient_dependency_1507.py'
assert not b.exists()
t=a.read_text(encoding='utf-8').replace('S_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_coeff','S_PowerSeries_coeff_mem_subring_of_coeff_mul_mem').replace('anthropic-integral-slash-depth-1495','anthropic-series-coefficient-depth-1507')
b.write_text(t,encoding='utf-8')
