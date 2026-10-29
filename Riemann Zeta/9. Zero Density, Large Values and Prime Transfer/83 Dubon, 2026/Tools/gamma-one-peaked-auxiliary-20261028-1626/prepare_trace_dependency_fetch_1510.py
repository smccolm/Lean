from pathlib import Path
s=Path(__file__).parent
a=s/'fetch_even_integrality_dependencies_1503.py'
b=s/'fetch_trace_dependencies_1510.py'
assert not b.exists()
t=a.read_text(encoding='utf-8')
start=t.index('names=');end=t.index('\nknown=',start)
t=t[:start]+"names=['S_UpperHalfPlane_qExpansion_coeff_sum_vAdd_eq_mul_coeff', 'S_UpperHalfPlane_qExpansion_coeff_eq_zero_of_isBigO_exp_neg', 'S_ModularForm_exists_levelOne_coe_eq_sum_slash', 'S_CongruenceSubgroup_exists_finset_transversal_adapted_T_S']"+t[end:]
t=t.replace('anthropic-even-integrality-depth-1503','anthropic-trace-dependencies-1510')
b.write_text(t,encoding='utf-8')
