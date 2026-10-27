from pathlib import Path
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
def output(n,s):
    assert not (r/(n+'.lean')).exists()
    with (p/(n+'.lean')).open('x',encoding='utf-8',newline='\n') as f:f.write(s)
group='Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)'
formgroup='(Γ : Subgroup (GL (Fin 2) ℝ))'
s=(r/'SourceModularRatioEvaluation.lean').read_text(encoding='utf-8')
s=s[s.index('namespace Dubon2026.SourceFunctionField'):]
s=s.replace('namespace Dubon2026.SourceFunctionField','namespace Dubon2026.SourceFunctionField.GammaOne').replace('end Dubon2026.SourceFunctionField','end Dubon2026.SourceFunctionField.GammaOne')
s=s.replace('(CongruenceSubgroup.Gamma0 N)',formgroup).replace('CongruenceSubgroup.Gamma0 N :','Γ :')
s=s.replace('def realize (N : ℕ)', 'def realize (Γ : '+group+')')
s=s.replace('theorem realize_eq_div (N : ℕ)', 'theorem realize_eq_div (Γ : '+group+') (hT : ModularGroup.T ∈ Γ)')
s=s.replace('realize N','realize Γ')
s=s.replace('    simp\n  have H', '    exact hper hT\n  have H')
output('SourceGammaOneRatioRealization','import Dubon2026.SourceGammaOneFieldModularRatio\n\n/-! DUB-17/18 -> actual Gamma1 differential/cusp converse -> meromorphic\nrealization of the original integral-ratio field. Adapt the proved local\nSourceModularRatioEvaluation, retaining actual equal-weight modular forms\nand exact q-expansion injectivity. Only translation membership is needed.\nThe local source credits anthropics/fermats-last-theorem, Apache-2.0,\ncommit 6e837e75355538c7f80bab5b956861e86c4eacc2. -/\n'+s)
s=(r/'SourceModularRatioGerms.lean').read_text(encoding='utf-8')
a=s.index('theorem analyticAt_comp_ofComplex');b=s.index('theorem meromorphicOrderAt_comp_ofComplex_ne_top')
s=s[a:b]
s=s.replace('(CongruenceSubgroup.Gamma0 N)',formgroup)
s=s.replace('  eventually_nhdsNE_coe_iff.mpr', '  SourceFunctionField.ModularRatios.eventually_nhdsNE_coe_iff.mpr')
output('SourceGammaOneAnalyticGerms','import SourceGammaOneRatioRealization\nimport Dubon2026.SourceModularRatioGerms\n\n/-! DUB-17/18 -> actual Gamma1 differential/cusp converse -> finite\nmeromorphic germs. The native analytic identity theorem gives punctured\nnonvanishing for actual modular denominators. Reuse the existing coordinate\nfilter identity; no new topology or valuation framework is introduced. -/\nnamespace Dubon2026.SourceFunctionField.GammaOne.ModularRatios\nnoncomputable section\nopen UpperHalfPlane Filter\nopen scoped MatrixGroups Topology Manifold\nvariable {Γ : '+group+'}\n\n'+s+'end\nend Dubon2026.SourceFunctionField.GammaOne.ModularRatios\n')
s=(r/'SourceOriginalMeromorphicRealization.lean').read_text(encoding='utf-8')
s=s[s.index('namespace Dubon2026.SourceFunctionField'):]
s=s.replace('namespace Dubon2026.SourceFunctionField','namespace Dubon2026.SourceFunctionField.GammaOne').replace('end Dubon2026.SourceFunctionField','end Dubon2026.SourceFunctionField.GammaOne')
s=s.replace('{N : ℕ}', '{Γ : '+group+'} (hT : ModularGroup.T ∈ Γ)')
s=s.replace('(N : ℕ) [NeZero N]', '{Γ : '+group+'} (hT : ModularGroup.T ∈ Γ)')
s=s.replace('(CongruenceSubgroup.Gamma0 N)',formgroup)
s=s.replace('modularFunctionFieldOver N ℂ','functionFieldOver Γ ℂ')
s=s.replace('original_field_modular_ratio N','functionFieldOver_modular_ratio hT')
s=s.replace('realize N','realize Γ').replace('realize_eq_div N','realize_eq_div Γ hT')
s=s.replace('meromorphicAt_original_realize','meromorphicAt_realize').replace('meromorphicOrderAt_original_realize_ne_top','meromorphicOrderAt_realize_ne_top')
s=s.replace('meromorphicAt_realize Γ','meromorphicAt_realize hT')
s=s.replace('realize_eventuallyEq_of_ratio g h','realize_eventuallyEq_of_ratio hT g h')
s=s.replace('ModularRatios.qL_ne_zero h hh','ModularRatios.qL_ne_zero hT h hh')
output('SourceGammaOneMeromorphicRealization','import SourceGammaOneAnalyticGerms\n\n/-! DUB-17/18 -> actual Gamma1 differential/cusp converse -> actual\nmeromorphic field realization. Every field element has a proved equal-weight\nmodular quotient; nonzero elements have finite germ order at every point.\nAdapt the proved SourceOriginalMeromorphicRealization to the original\nintegral-ratio field, using translation membership and no Gamma0 place. -/\n'+s)
print('Prepared three selected local analytic realization modules.')
