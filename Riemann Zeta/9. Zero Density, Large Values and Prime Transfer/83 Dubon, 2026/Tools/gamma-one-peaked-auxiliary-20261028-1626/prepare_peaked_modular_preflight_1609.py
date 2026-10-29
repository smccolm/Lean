from pathlib import Path
import ast
s=Path(__file__).parent
c=(s/'run_prepare_siegel_finite_product_preflight_1602.py').read_text(encoding='utf-8')
a=c.index('versions={');b=c.index('\nmods=',a)
c=c[:a]+'''versions={
'SourcePeakedAuxiliaryFunction':'1603a','SourceSiegelCuspPermutation':'1604a',
'SourcePeakedAuxiliaryCuspDecay':'1605a','SourcePeakedAuxiliaryHolomorphic':'1606a',
'SourcePeakedAuxiliaryModularForm':'1607a'}'''+c[b:]
c=c.replace("PeakedAuxiliary.FiniteExpansion.'","PeakedAuxiliary.Form.'")
c=c.replace("roots=[ns+'exists_integral_hasSum_prod_siegelFun_pow']","roots=[ns+'exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow']")
a=c.index('edges=');b=c.index('\ncfg=',a)
c=c[:a]+'''edges=ths+defs+[
'Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Siegel.prod_siegelFun_pow_specialLinearGroup_smul',
'Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Siegel.differentiableOn_siegelFun',
'Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.FiniteExpansion.exists_integral_hasSum_prod_siegelFun_pow',
'CuspFormClass.exp_decay_atImInfty',
'SlashInvariantForm.slash_action_generators_SL2Z']'''+c[b:]
c=c.replace('1602','1609').replace('siegel-finite-product','peaked-modular-form').replace('SourceSiegelFiniteProduct','SourcePeakedModularForm').replace('SIEGEL FINITE PRODUCT','PEAKED MODULAR FORM')
c=c.replace('literal finite Siegel product integral expansion, specified nonzero leading coefficient, level-cleared inverse, phase root of unity and cusp limit. Discriminant adjustment, cusp estimates and peaked auxiliary existence remain open','actual discriminant-adjusted Gamma1 modular form and its exact exponential bound at every SL2 cusp, under explicit nonnegative shifted-order hypotheses. Selection of the discriminant power, exact auxiliary q-expansions and peaked auxiliary existence remain open')
ast.parse(c)
f=s/'run_prepare_peaked_modular_preflight_1609.py';assert not f.exists();f.write_text(c,encoding='utf-8')
exec(compile(c,str(f),'exec'))
