from pathlib import Path
import ast
s=Path(__file__).parent
c=(s/'run_prepare_peaked_modular_preflight_1609.py').read_text(encoding='utf-8')
a=c.index('versions={');b=c.index('\nmods=',a)
c=c[:a]+'''versions={
'SourcePeakedDiscriminantSeries':'1610b','SourcePeakedSeriesOperations':'1611b',
'SourcePeakedShiftedCoefficients':'1615b','SourcePeakedShiftedSeries':'1613d',
'SourcePeakedWidthOneIdentification':'1617b','SourcePeakedIntegralQExpansion':'1618b',
'SourcePeakedTranslatedIntegralExpansion':'1620a','SourcePeakedScaledOrders':'1621a',
'SourcePeakedOrderGapDecay':'1622a','SourceActualPeakedAuxiliary':'1623a'}'''+c[b:]
c=c.replace("PeakedAuxiliary.Form.'","PeakedAuxiliary.'")
c=c.replace("roots=[ns+'exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow']","roots=[ns+'exists_gamma1_peaked_auxiliary_form_twelve_dvd']")
a=c.index('edges=');b=c.index('\ncfg=',a)
c=c[:a]+'''edges=ths+defs+[
'Dubon2026.SourceFunctionField.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit',
'Dubon2026.hasSum_pow_dvd_reindex',
'Dubon2026.SourceFricke.qParam_one_eq_pow',
'Dubon2026.SourceFricke.gammaOne_one_mem_strictPeriods',
'Dubon2026.SourceFricke.qExpansion_coeff_width',
'Dubon2026.SourceFunctionField.GammaOne.CuspAuxiliary.natCast_mem_strictPeriods_conj',
'ModularFormClass.qExpansion_coeff_unique',
ns+'exists_peaked_exponent_on_actual_cusps',
ns+'Form.exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow',
ns+'Form.uFun_smul',ns+'Form.ord_eq',ns+'Form.thetaFun_slash_apply',
ns+'FiniteExpansion.hasSum_productSeries',ns+'FiniteExpansion.integral_productSeries',
ns+'FiniteExpansion.integral_level_inverse_productSeries_zero',
ns+'FiniteExpansion.productSeries_zero_ne_zero']'''+c[b:]
c=c.replace('1609','1624').replace('peaked-modular-form','actual-peaked-auxiliary').replace('SourcePeakedModularForm','SourceActualPeakedAuxiliary').replace('PEAKED MODULAR FORM','ACTUAL PEAKED AUXILIARY')
c=c.replace('actual discriminant-adjusted Gamma1 modular form and its exact exponential bound at every SL2 cusp, under explicit nonnegative shifted-order hypotheses. Selection of the discriminant power, exact auxiliary q-expansions and peaked auxiliary existence remain open','actual even-weight Gamma1 peaked auxiliary, including proved exponent scaling, discriminant power choice, exact integral coefficients and leading inverse, weight/order gap and separated cusp decay. The auxiliary existence premise is discharged; its trace application, reduced field action and degree/genus preservation remain open')
ast.parse(c)
f=s/'run_prepare_actual_peaked_preflight_1624.py';assert not f.exists();f.write_text(c,encoding='utf-8')
exec(compile(c,str(f),'exec'))
