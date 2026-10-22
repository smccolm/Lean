import Dubon2026.SourceOriginalAnalyticJValues
import Dubon2026.SourceOriginalJFiberDegree

/-! DUB-17/18 -> numerical genus and analytic differential realization.
The genuine analytic place lies over the actual finite j-value. Its
coordinate difference has positive normalized order, using continuity of
the literal E4/discriminant quotient and the proved positive normalization.
No finite-fiber location or order hypothesis is supplied.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter
open scoped Topology Manifold

theorem continuous_analytic_j :
    Continuous (fun τ : ℍ => ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) :=
  ((ModularFormClass.holo ModularForm.E₄).continuous.pow 3).div
    (ModularFormClass.holo CuspForm.discriminant).continuous ModularForm.discriminant_ne_zero

theorem originalAnalyticPlace_j_mem (N : ℕ) [NeZero N] (τ : ℍ) :
    jOver N ℂ ∈ (originalAnalyticPlace N τ).toValuationSubring := by
  rw [originalAnalyticPlace_mem_iff_bounded]
  simp only [realize_jOver]
  exact continuous_analytic_j.continuousAt.norm.tendsto.isBoundedUnder_le.mono nhdsWithin_le_nhds

theorem originalAnalyticOrder_j_sub_pos (N : ℕ) [NeZero N] (τ : ℍ) :
    0 < originalAnalyticOrder N τ (jOver N ℂ -
      algebraMap ℂ (modularFunctionFieldOver N ℂ)
        (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)) := by
  let c := ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ
  apply (tendsto_zero_iff_meromorphicOrderAt_pos (meromorphicAt_original_realize N _ τ)).mp
  have hc : Tendsto (fun z : ℂ => realize N (jOver N ℂ : LaurentSeries ℂ) (ofComplex z))
      (𝓝[≠] (τ : ℂ)) (𝓝 c) := by
    simp only [realize_jOver]
    have h := continuous_analytic_j.continuousAt.comp
      (mdifferentiableAt_ofComplex τ.im_pos).continuousAt
    simpa only [Function.comp_def, ofComplex_apply, c] using
      h.tendsto.mono_left (show 𝓝[≠] (τ : ℂ) ≤ 𝓝 (τ : ℂ) from nhdsWithin_le_nhds)
  have hlim : Tendsto
      ((fun z : ℂ => realize N (jOver N ℂ : LaurentSeries ℂ) (ofComplex z)) + fun _ => -c)
      (𝓝[≠] (τ : ℂ)) (𝓝 0) := by
    simpa using hc.add (tendsto_const_nhds (x := -c))
  refine hlim.congr' ?_
  have he : jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) c =
      jOver N ℂ + algebraMap ℂ (modularFunctionFieldOver N ℂ) (-c) := by
    rw [map_neg, sub_eq_add_neg]
  change _ =ᶠ[_] fun z : ℂ => realize N
    ((jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) c : modularFunctionFieldOver N ℂ) : LaurentSeries ℂ)
      (ofComplex z)
  rw [he]
  exact ((original_realize_add_eventuallyEq N (jOver N ℂ)
    (algebraMap ℂ (modularFunctionFieldOver N ℂ) (-c)) τ).trans
      (EventuallyEq.rfl.add (Eventually.of_forall fun z => realize_algebraMap N (-c) (ofComplex z)))).symm

theorem originalAnalyticPlace_j_sub_pos (N : ℕ) [NeZero N] (τ : ℍ) :
    0 < (originalAnalyticPlace N τ).ord (jOver N ℂ -
      algebraMap ℂ (modularFunctionFieldOver N ℂ)
        (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)) := by
  have h := originalAnalyticOrder_j_sub_pos N τ
  have hx : jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ)
      (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) ≠ 0 := by
    intro he
    apply original_j_sub_transcendental N ℂ (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    rw [he]
    exact isAlgebraic_zero
  rw [originalAnalyticPlace_order N τ _ hx,
    ← WithTop.coe_zero, WithTop.coe_lt_coe] at h
  exact (mul_pos_iff_of_pos_left (Int.natCast_pos.mpr (originalAnalyticRamification_pos N τ))).mp h

theorem originalAnalyticPlace_j_value (N : ℕ) [NeZero N] (τ : ℍ) (c : ℂ) :
    0 < (originalAnalyticPlace N τ).ord
      (jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) c) ↔
        c = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ := by
  obtain ⟨c₀, _, hc₀⟩ := (originalAnalyticPlace N τ).exists_unique_coordinate_value
    (original_place_residue_algebraMap_bijective N ℂ (originalAnalyticPlace N τ)).surjective
    (transcendental_jOver N ℂ) (originalAnalyticPlace_j_mem N τ)
  constructor
  · intro hc
    exact (hc₀ c hc).trans (hc₀ _ (originalAnalyticPlace_j_sub_pos N τ)).symm
  · rintro rfl
    exact originalAnalyticPlace_j_sub_pos N τ

end
end Dubon2026.SourceFunctionField
