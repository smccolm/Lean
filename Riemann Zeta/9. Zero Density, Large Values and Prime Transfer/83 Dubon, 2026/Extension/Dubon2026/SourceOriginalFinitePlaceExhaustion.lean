import Dubon2026.SourceOriginalAnalyticChartPlaces

/-! DUB-17/18 -> numerical genus and regular-differential realization
-> finite analytic-place exhaustion. If an original finite place were
missing from the analytic family, its inverse center ideal would supply
an element outside the integral closure but belonging to every analytic
valuation ring. The proved bounded-function integrality theorem gives
the contradiction. All chart, residue and analytic inputs are derived
for the actual original field.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_ComplexPlaceDictionary_exists_pt_eq_of_mem.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve AnalyticChart UpperHalfPlane
open scoped AnalyticChart IntermediateField.algebraAdjoinAdjoin nonZeroDivisors

theorem exists_original_analytic_place_eq (N : ℕ) [NeZero N]
    (P : Place ℂ (modularFunctionFieldOver N ℂ))
    (hP : jOver N ℂ ∈ P.toValuationSubring) :
    ∃ τ : ℍ, originalAnalyticPlace N τ = P := by
  by_contra hne
  push Not at hne
  have hwP := chart_mem N hP
  have h𝔭0 : Place.center (B N) P hwP ≠ ⊥ := Place.center_ne_bot P hwP
  have h𝔭max : (Place.center (B N) P hwP).IsMaximal :=
    (Place.centerHeightOneSpectrum (B N) P hwP).isPrime.isMaximal h𝔭0
  obtain ⟨x, hx𝔭, hxB⟩ :=
    FractionalIdeal.exists_notMem_one_of_ne_bot (K := F N) h𝔭0 h𝔭max.ne_top
  have hxτ : ∀ τ : ℍ, x ∈ (originalAnalyticPlace N τ).toValuationSubring := by
    intro τ
    have hwτ := chart_mem N (originalAnalyticPlace_j_mem N τ)
    have hneq : ¬ Place.center (B N) P hwP ≤
        Place.center (B N) (originalAnalyticPlace N τ) hwτ := fun hle =>
      hne τ (eq_of_center_eq N hwτ hwP
        (h𝔭max.eq_of_le
          (Place.centerHeightOneSpectrum (B N) (originalAnalyticPlace N τ) hwτ).isPrime.ne_top hle).symm)
    obtain ⟨s, hs𝔭, hsτ⟩ := Set.not_subset.mp hneq
    have hxs : x * algebraMap (B N) (F N) s ∈ (1 : FractionalIdeal (B N)⁰ (F N)) := by
      have hmem : x * algebraMap (B N) (F N) s ∈
          ((Place.center (B N) P hwP : FractionalIdeal (B N)⁰ (F N))⁻¹ *
            (Place.center (B N) P hwP : FractionalIdeal (B N)⁰ (F N))) :=
        FractionalIdeal.mul_mem_mul hx𝔭 (FractionalIdeal.mem_coeIdeal_of_mem _ hs𝔭)
      rwa [inv_mul_cancel₀ (FractionalIdeal.coeIdeal_ne_zero.mpr h𝔭0)] at hmem
    obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).mp hxs
    exact mem_of_mul_eq N hwτ hsτ hb.symm
  have hint := isIntegral_original_of_mem_all_analytic_places N x hxτ
  exact hxB ((FractionalIdeal.mem_one_iff _).mpr ⟨⟨x, hint⟩, rfl⟩)

theorem original_place_cusp_or_analytic (N : ℕ) [NeZero N]
    (P : Place ℂ (modularFunctionFieldOver N ℂ)) :
    P.ord (jOver N ℂ) < 0 ∨ ∃ τ : ℍ, originalAnalyticPlace N τ = P := by
  rcases lt_or_ge (P.ord (jOver N ℂ)) 0 with hc | hf
  · exact Or.inl hc
  · exact Or.inr (exists_original_analytic_place_eq N P (P.mem_of_ord_nonneg hf))

theorem original_finite_fiber_realization (N : ℕ) [NeZero N]
    (P : Place ℂ (modularFunctionFieldOver N ℂ)) (c : ℂ)
    (hc : 0 < P.ord (jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) c)) :
    ∃ τ : ℍ, originalAnalyticPlace N τ = P ∧
      ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ = c := by
  have hP : jOver N ℂ ∈ P.toValuationSubring := by
    have h := add_mem (P.mem_of_ord_nonneg hc.le) (P.algebraMap_mem' c)
    simpa only [sub_add_cancel] using h
  obtain ⟨τ, hτ⟩ := exists_original_analytic_place_eq N P hP
  refine ⟨τ, hτ, ?_⟩
  symm
  apply (originalAnalyticPlace_j_value N τ c).mp
  rwa [hτ]

end
end Dubon2026.SourceFunctionField
