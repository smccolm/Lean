import Dubon2026.SourceOriginalAnalyticChartPlaces
import Dubon2026.SourceOriginalAnalyticOrbitSeparation
import Dubon2026.SourceOriginalAnalyticResidueValues

/-! DUB-17/18 -> original Gamma1 global charts -> full orbit separation.
Reuse the proved Gamma0 place/orbit dictionary and actual integral-closure
centers. Discriminant-power modular representations have nowhere-zero
denominators, so equal modular cross products identify all center residues.
This replaces a second simultaneous-invariant lattice construction. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter SourceCurve
open scoped MatrixGroups Topology IntermediateField.algebraAdjoinAdjoin AnalyticChart

theorem originalPlaceEval_eq_modular_ratio (N : ℕ) [NeZero N]
    (x : modularFunctionFieldOver N ℂ) (τ : ℍ)
    (hx : x ∈ (originalAnalyticPlace N τ).toValuationSubring)
    {k : ℤ} (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hh : h ≠ 0)
    (hr : (x : LaurentSeries ℂ) * ModularRatios.qL h = ModularRatios.qL g)
    (hτ : h τ ≠ 0) :
    originalPlaceEval N ℂ (originalAnalyticPlace N τ) x = g τ / h τ := by
  have hq : ContinuousAt (fun z : ℂ => g (ofComplex z) / h (ofComplex z)) (τ : ℂ) :=
    (ModularRatios.analyticAt_comp_ofComplex g τ).continuousAt.div
      (ModularRatios.analyticAt_comp_ofComplex h τ).continuousAt
      (by simpa only [ofComplex_apply] using hτ)
  have he := tendsto_nhds_unique_of_eventuallyEq
    (original_realize_tendsto_residue N τ x hx)
    (hq.tendsto.mono_left nhdsWithin_le_nhds)
    (realize_eventuallyEq_of_ratio g h x hh hr τ)
  simpa only [ofComplex_apply] using he

theorem exists_original_nonvanishing_modular_ratio (N : ℕ) [NeZero N]
    (x : modularFunctionFieldOver N ℂ)
    (hx : ∀ τ : ℍ, x ∈ (originalAnalyticPlace N τ).toValuationSubring) :
    ∃ (k : ℤ) (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k), h ≠ 0 ∧
      (x : LaurentSeries ℂ) * ModularRatios.qL h = ModularRatios.qL g ∧ ∀ τ : ℍ, h τ ≠ 0 := by
  obtain ⟨m, G, hG⟩ := exists_original_discriminant_power N x
    (fun τ => (originalAnalyticPlace_mem_iff_bounded N τ x).mp (hx τ))
  let H : ModularForm (CongruenceSubgroup.Gamma0 N) (12 * (m : ℤ)) :=
    ((QuotientCuspGrowth.Δ₀ N).pow m).mcast (mul_comm (m : ℤ) 12)
  have hH (τ : ℍ) : H τ = ModularForm.discriminant τ ^ m := by
    simp only [H, ModularForm.coe_mcast, ModularForm.coe_pow, Pi.pow_apply,
      QuotientCuspGrowth.coe_Δ₀]
  have hHne (τ : ℍ) : H τ ≠ 0 := by
    rw [hH]
    exact pow_ne_zero _ (ModularForm.discriminant_ne_zero τ)
  have hH0 : H ≠ 0 := fun he => hHne UpperHalfPlane.I (by rw [he]; rfl)
  refine ⟨12 * (m : ℤ), G, H, hH0, ?_, hHne⟩
  have hq : ModularRatios.qL H =
      (qExpansion 1 ModularForm.discriminant : LaurentSeries ℂ) ^ m := by
    have he := congrArg (fun p : PowerSeries ℂ => (p : LaurentSeries ℂ))
      (ModularForm.qExpansion_pow one_pos (ModularRatios.one_mem_strictPeriods N)
        (QuotientCuspGrowth.Δ₀ N) m)
    simpa only [ModularRatios.qL, H, ModularForm.coe_mcast, QuotientCuspGrowth.coe_Δ₀,
      PowerSeries.coe_pow] using he
  rw [hq]
  exact hG

theorem exists_gamma0_smul_eq_of_cross_products (N : ℕ) [NeZero N] (τ τ' : ℍ)
    (hc : ∀ (k : ℤ) (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k),
      g τ * h τ' = g τ' * h τ) :
    ∃ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • τ = τ' := by
  apply (originalAnalyticPlace_eq_iff_gamma0_orbit N τ τ').mp
  have hmem (z : ℍ) := AnalyticChart.chart_mem N (originalAnalyticPlace_j_mem N z)
  apply AnalyticChart.eq_of_center_eq N (hmem τ) (hmem τ')
  ext b
  by_cases hb : b = 0
  · subst b
    exact iff_of_true (Ideal.zero_mem _) (Ideal.zero_mem _)
  let x : AnalyticChart.F N := algebraMap (AnalyticChart.B N) (AnalyticChart.F N) b
  have hx0 : x ≠ 0 := fun hx0 => hb (Subtype.ext hx0)
  have hx (z : ℍ) : x ∈ (originalAnalyticPlace N z).toValuationSubring := hmem z b
  obtain ⟨k, g, h, hh, hr, hne⟩ := exists_original_nonvanishing_modular_ratio N x hx
  have he : originalPlaceEval N ℂ (originalAnalyticPlace N τ) x =
      originalPlaceEval N ℂ (originalAnalyticPlace N τ') x := by
    rw [originalPlaceEval_eq_modular_ratio N x τ (hx τ) g h hh hr (hne τ),
      originalPlaceEval_eq_modular_ratio N x τ' (hx τ') g h hh hr (hne τ')]
    exact (div_eq_div_iff (hne τ) (hne τ')).mpr (hc k g h)
  rw [Place.mem_center_iff_ord_pos _ (hmem τ) hb,
    Place.mem_center_iff_ord_pos _ (hmem τ') hb,
    ← originalPlaceEval_eq_zero_iff_ord_pos N ℂ (originalAnalyticPlace N τ) (hx τ) hx0,
    ← originalPlaceEval_eq_zero_iff_ord_pos N ℂ (originalAnalyticPlace N τ') (hx τ') hx0, he]

theorem exists_original_separating_modular_forms (N : ℕ) [NeZero N]
    (τ τ' : ℍ) (hτ : ∀ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • τ ≠ τ') :
    ∃ (k : ℤ) (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k),
      g τ * h τ' ≠ g τ' * h τ := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨γ, he⟩ := exists_gamma0_smul_eq_of_cross_products N τ τ' hn
  exact hτ γ he

end
end Dubon2026.SourceFunctionField
