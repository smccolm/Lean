from pathlib import Path
import ast
s=Path(__file__).parent
c=(s/'prepare_siegel_expansion_preflight_1594.py').read_text(encoding='utf-8')
a=c.index('versions={');b=c.index('\nmods=',a)
c=c[:a]+'''versions={
'SourceSiegelFiniteSeriesProducts':'1596b','SourceSiegelProductCoefficients':'1597b',
'SourceSiegelProductLeadingCoefficient':'1599b','SourceSiegelProductPhases':'1600a',
'SourceSiegelFiniteProductExpansion':'1601b'}'''+c[b:]
c=c.replace("ns='Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.EulerExpansion.'","ns='Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.FiniteExpansion.'")
c=c.replace("roots=[ns+'exists_integral_hasSum_siegelFun']","roots=[ns+'exists_integral_hasSum_prod_siegelFun_pow']")
a=c.index('edges=');b=c.index('\ncfg=',a)
c=c[:a]+'''edges=ths+defs+[
'Dubon2026.SourceFunctionField.Realized.hasSum_qParam_mul',
'Dubon2026.SourceFunctionField.Realized.tendsto_atImInfty',
'Dubon2026.SourceFunctionField.IntegralTrace.coeff_mul_mem',
'Dubon2026.SourceFunctionField.IntegralTrace.coeff_pow_mem',
'Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.EulerExpansion.hasSum_coef',
'Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.EulerExpansion.isIntegral_coef',
'Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.EulerExpansion.coef_zero',
'Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.EulerExpansion.isIntegral_N_mul_inv_coef_zero',
'Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.EulerExpansion.zeta_ne_one']'''+c[b:]
c=c.replace('1594','1602').replace('siegel-expansion','siegel-finite-product').replace('SourceSiegelExpansion','SourceSiegelFiniteProduct').replace('SIEGEL EXPANSION','SIEGEL FINITE PRODUCT')
c=c.replace('literal single Siegel integral expansion, specified leading coefficient, level-cleared inverse and cusp limit. Finite products and peaked auxiliary existence remain open','literal finite Siegel product integral expansion, specified nonzero leading coefficient, level-cleared inverse, phase root of unity and cusp limit. Discriminant adjustment, cusp estimates and peaked auxiliary existence remain open')
ast.parse(c)
f=s/'run_prepare_siegel_finite_product_preflight_1602.py';assert not f.exists();f.write_text(c,encoding='utf-8')
exec(compile(c,str(f),'exec'))
