from pathlib import Path
s=Path(__file__).parent
t=(s/'fetch_anthropic_gamma_one_geometry_1463b.py').read_text(encoding='utf-8')
start=t.index('names=[');end=t.index('\nknown=',start)
names=['S_ModularCurve_genusFF_xHFunctionFieldBar_le_genusFF_xHFunctionFieldC_of_not_dvd','S_EisensteinSeries_exists_modularForm_coe_eq_eisensteinG','S_EisensteinSeries_qExpansion_eisensteinG_coeff']
t=t[:start]+'names='+repr(names)+t[end:]
t=t.replace('anthropic-gamma-one-geometry-1463b','anthropic-degree-genus-leaves-1465')
with (s/'fetch_anthropic_degree_genus_leaves_1465.py').open('x',encoding='utf-8') as h:h.write(t)
