from pathlib import Path
s=Path(__file__).parent;a=s/'fetch_peaked_integrality_dependencies_1498.py';b=s/'fetch_even_integrality_dependencies_1503.py'
assert not b.exists()
t=a.read_text(encoding='utf-8')
start=t.index('names=');end=t.index('\nknown=',start)
t=t[:start]+"names=['S_ModularCurve_SiegelUnit_exists_gamma1_peaked_auxiliary_form_twelve_dvd', 'S_ModularForm_levelOne_qExpansion_coeff_mem_of_coeff_le_mem', 'S_ModularForm_exists_levelOne_qExpansion_eq_map_int_constantCoeff_one']"+t[end:]
t=t.replace('anthropic-peaked-integrality-depth-1498','anthropic-even-integrality-depth-1503')
b.write_text(t,encoding='utf-8')
