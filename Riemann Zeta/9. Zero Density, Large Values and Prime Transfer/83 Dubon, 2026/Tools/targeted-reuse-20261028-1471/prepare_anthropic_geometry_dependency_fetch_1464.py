from pathlib import Path
s=Path(__file__).parent
t=(s/'fetch_anthropic_gamma_one_geometry_1463b.py').read_text(encoding='utf-8')
start=t.index('names=[');end=t.index('\nknown=',start)
names=['S_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd','S_ModularCurve_exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq','S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_zmod','S_ModularCurve_reductionInputsQExpModL_of_finrank_le_of_genusFF_eq']
t=t[:start]+'names='+repr(names)+t[end:]
t=t.replace('anthropic-gamma-one-geometry-1463b','anthropic-geometry-dependencies-1464')
with (s/'fetch_anthropic_geometry_dependencies_1464.py').open('x',encoding='utf-8') as h:h.write(t)
for f in (s/'anthropic-gamma-one-geometry-1463b').glob('*index_gammaH*residueField.lean.txt'):
 text='\n'.join(l for l in f.read_text(encoding='utf-8').splitlines() if not l.startswith('attribute '))+'\n'
 with (s/'anthropic-gamma-one-degree-reading-1464.txt').open('x',encoding='utf-8') as h:h.write(text)
print('Prepared four pinned dependency reads; degree reading copy omits attribute commands only.')
