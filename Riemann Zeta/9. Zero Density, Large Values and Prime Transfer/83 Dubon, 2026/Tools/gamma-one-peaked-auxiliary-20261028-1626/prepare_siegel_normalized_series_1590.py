from pathlib import Path
s=Path(__file__).parent
t=(s/'anthropic-siegel-dependencies-1553/S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_siegelFun.lean.txt').read_text(encoding='utf-8')
ns='Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.EulerExpansion'
body='''theorem polynomial_product_eq_streams (N : ℕ) (hN : 0 < N) (r : ℕ)
    (hr : r < N) (u v : ℂ) {x : ℂ} (hx : ‖x‖ < 1) :
    (if r = 0 then 1 - u else 1) * product (Pc N r u v) x =
      (1 - u * x ^ r) * ∏' n : ℕ,
        ((1 - u * x ^ ((n + 1) * N + r)) * (1 - v * x ^ (n * N + (N - r)))) := by
  unfold product
  simp_rw [Pc_eval]
  exact tprod_Pc_eval N hN r hr u v hx

'''
body+=t[t.index('theorem siegelFun_div_eq (N : ℕ)'):t.index('def coef (N r : ℕ)')]
body=body.replace('ArchSkel.','').replace('ModularCurve.siegelFun_def','siegelFun_def')
header='''/-! DUB-17/18 -> original Gamma1 degree/genus preservation -> level-power
slash integrality -> peaked auxiliary -> exact integral Siegel expansion.
Consume the actual residue reindexing and actual polynomial products to
identify their analytic limit with the normalized literal Siegel function.
The stabilized finite-product coefficients then supply its exact HasSum;
integrality and the level-cleared leading inverse are proved separately.
The native Taylor route replaces the source candidate's formal product W.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_siegelFun. -/
'''
intro='namespace '+ns+'\nnoncomputable section\nopen Complex Polynomial Filter Topology\nopen scoped Real\n\n'
ending='\nend\nend '+ns+'\n'
def write(n,c):
 f=s/n;assert not f.exists();f.write_text(c,encoding='utf-8')
write('SourceSiegelNormalizedProduct1590a.lean','import SourceSiegelResidueProductStreams1588a\nimport SourceSiegelPolynomialFactors1584b\nimport SourceSiegelProductTaylorExpansion1583b\nimport SourceSiegelLeadingUnit1589a\n\n'+header+intro+body+ending)
body=t[t.index('def coef (N r : ℕ)'):t.index('theorem zeta_ne_one ')]
body=body.replace('def coef ', '/-- The actual stabilized finite-product coefficients of the normalized Siegel factor. -/\ndef coef ',1)
body=body.replace('PowerSeries.coeff m (W (Pc N r (zeta N s) (zeta N s)⁻¹))','stableCoeff (Pc N r (zeta N s) (zeta N s)⁻¹) m')
body=body.replace('ArchSkel.','').replace('← tprod_Pc_eval','← polynomial_product_eq_streams')
body=body.replace('''exact (hasSum_coeff_W (Pc_coeff_zero N r _ _) M2_coeff_zero
    (Pc_dom N r (norm_zeta N s).le (norm_zeta_inv N s).le) (norm_qN_lt_one N hN τ)).mul_left _''','''exact (hasSum_stableCoeff (Pc N r (zeta N s) (zeta N s)⁻¹)
    (Pc_coeff_zero N r _ _) 3 (by norm_num)
    (Pc_norm_bound N r (norm_zeta N s).le (norm_zeta_inv N s).le)
    (norm_qN_lt_one N hN τ)).mul_left _''')
body=body.replace('isIntegral_coeff_W','isIntegral_stableCoeff')
body=body.replace('PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_W (Pc_coeff_zero N r _ _),','stableCoeff_zero,')
assert 'hasSum_coeff_W' not in body and 'M2' not in body and ' W ' not in body
body+=t[t.index('theorem isIntegral_N_mul_inv_coef_zero '):t.index('theorem main (N : ℕ)')].replace('ArchSkel.','')
write('SourceSiegelCoefficientSeries1591a.lean','import SourceSiegelNormalizedProduct1590a\n\n'+header+intro+body+ending)
body=t[t.index('theorem main (N : ℕ)'):t.index('\nend Siegel')]
body=body.replace('theorem main ','theorem exists_integral_series_nat ')
body=body.replace('ArchSkel.','')
body=body.replace('exact ModularCurve.tendsto_atImInfty_of_hasSum_qParam (N : ℝ) (by exact_mod_cast hN) _ (coef N r s) h','exact Dubon2026.SourceFunctionField.Realized.tendsto_atImInfty (by exact_mod_cast hN) h')
outer=t[t.index('theorem solution (N : ℕ) (r s : ℤ)'):]
outer=outer.replace('theorem solution ', 'theorem exists_integral_hasSum_siegelFun ').replace('exact main N','exact exists_integral_series_nat N')
write('SourceSiegelIntegralExpansion1592a.lean','import SourceSiegelCoefficientSeries1591a\n\n'+header+intro+body+'\n'+outer+ending)
