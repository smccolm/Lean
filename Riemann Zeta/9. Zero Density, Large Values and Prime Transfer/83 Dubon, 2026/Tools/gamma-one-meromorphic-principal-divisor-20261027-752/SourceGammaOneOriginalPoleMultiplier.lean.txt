import Dubon2026.SourceCurveFiniteCoordinateDimensionBounds
import Dubon2026.SourceGammaOneFinitePlaceExhaustion
import Dubon2026.SourceGammaOneCuspPlaces
import Dubon2026.SourceGammaOneAnalyticJOrders

/-! DUB-17/18 -> original all-weight arithmetic association -> actual finite
Gamma1 characters -> Picard/H1 comparison -> modular periods -> meromorphic
field realization. The existing finite-coordinate dimension bound clears
any finite prescribed divisor using a function with its only permitted
pole at an actual cusp. No new polynomial or compact-pole enumeration. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane SourceCurve
open scoped MatrixGroups
variable {Γ : Subgroup SL(2, ℤ)}
  (N : ℕ) [NeZero N] (hΓ : CongruenceSubgroup.Gamma N ≤ Γ)
  (hT : ModularGroup.T ∈ Γ)
include hΓ hT

theorem exists_original_pole_multiplier
    (D : Divisor ℂ (functionFieldOver Γ ℂ)) :
    ∃ a : functionFieldOver Γ ℂ, a ≠ 0 ∧
      ∀ P : Place ℂ (functionFieldOver Γ ℂ), 0 ≤ P.ord (jCoordinateOver Γ ℂ) →
        0 ≤ P.ord a ∧ 0 ≤ P.ord a + D P := by
  classical
  letI : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hΓ
  letI := finiteDimensional_jCoordinateOver hT ℂ
  let E : Divisor ℂ (functionFieldOver Γ ℂ) :=
    D.mapRange (fun z : ℤ => max (-z) 0) (by simp)
  let Q := cuspPlace N hΓ hT (1 : SL(2, ℤ))
  obtain ⟨n, a, ha0, ha⟩ := exists_pole_clearing_function_of_finite_coordinate
    (jCoordinateOver Γ ℂ) (transcendental_jCoordinateOver Γ ℂ) Q E
  have hb := (mem_lSpace_iff_ord.mp ha).resolve_left ha0
  refine ⟨a, ha0, fun P hP => ?_⟩
  have hPQ : P ≠ Q := by
    intro he
    rw [he] at hP
    exact (not_le_of_gt (cuspPlace_j_neg N hΓ hT 1)) hP
  have he : max (-(D P)) 0 ≤ P.ord a := by
    simpa [E, Finsupp.single_apply, Ne.symm hPQ] using hb P
  constructor <;> omega

theorem exists_original_pole_multiplier_at_analytic_places
    (D : Divisor ℂ (functionFieldOver Γ ℂ)) :
    ∃ a : functionFieldOver Γ ℂ, a ≠ 0 ∧
      (∀ τ : ℍ, a ∈ (analyticPlace hT τ).toValuationSubring) ∧
      ∀ τ : ℍ, 0 ≤ (analyticPlace hT τ).ord a + D (analyticPlace hT τ) := by
  obtain ⟨a, ha0, ha⟩ := exists_original_pole_multiplier N hΓ hT D
  have hregular (τ : ℍ) : 0 ≤ (analyticPlace hT τ).ord (jCoordinateOver Γ ℂ) := by
    apply (analyticPlace hT τ).mem_iff_ord_nonneg.mp
    have hm := add_mem ((analyticPlace hT τ).mem_of_ord_nonneg
      (analyticPlace_j_sub_pos hT τ).le)
      ((analyticPlace hT τ).algebraMap_mem' (JMultiplicity.jf τ))
    simpa only [sub_add_cancel] using hm
  exact ⟨a, ha0, fun τ => (analyticPlace hT τ).mem_of_ord_nonneg (ha _ (hregular τ)).1,
    fun τ => (ha _ (hregular τ)).2⟩

end
end Dubon2026.SourceFunctionField.GammaOne
