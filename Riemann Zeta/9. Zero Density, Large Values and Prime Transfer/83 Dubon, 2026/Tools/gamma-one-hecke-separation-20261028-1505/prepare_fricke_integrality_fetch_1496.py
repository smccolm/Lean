from pathlib import Path
s=Path(__file__).parent
a=s/'fetch_eisenstein_degree_dependency_1495.py';b=s/'fetch_fricke_integrality_dependency_1496.py'
assert not b.exists()
t=a.read_text(encoding='utf-8').replace('S_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_coeff','S_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_fricke_coeff').replace('anthropic-integral-slash-depth-1495','anthropic-fricke-integrality-depth-1496')
b.write_text(t,encoding='utf-8')
