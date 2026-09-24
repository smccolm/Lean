import TaoTrudgianYang2025.ZetaReflectionValueFamily

/-! The actual weighted common mean and finite value selection combined. -/

noncomputable section
open Complex Filter MeasureTheory Set
open scoped Classical Interval
namespace TaoTrudgianYang2025

theorem exists_reflection_common_value_family (W : Finset ℝ) (S : Finset ℕ)
    (hS : ∀ n ∈ S, n ≠ 0) (hsep : IsOneSeparated W)
    {T L a : ℝ} (hT : 0 < T) (hL : 0 < L) (ha : 0 < a)
    (hW : ∀ t ∈ W, t ∈ Icc T (2*T))
    (hlarge : L ≤ ∑ t ∈ W, zetaReflectionConvolution S T t)
    (hlow : 4*a*(W.card : ℝ)*zetaMomentLogLoss T ≤ L) :
    ∃ u ∈ Icc (-(2*T)) (2*T),
      ∃ j ∈ Finset.range (reflectionBandCount S a), ∃ U : Finset ℝ,
        U.Nonempty ∧ U ⊆ W.image (fun t => t+u) ∧ IsOneSeparated U ∧
        (∀ v ∈ U, v ∈ Icc (T/2) (3*T)) ∧
        (∀ v ∈ U, a*(2 : ℝ)^j ≤ ‖∑ n ∈ S, dirichletPhase n v‖ ∧
          ‖∑ n ∈ S, dirichletPhase n v‖ < 2*(a*(2 : ℝ)^j)) ∧
        L/(8*zetaMomentLogLoss T*(reflectionBandCount S a : ℝ)) ≤
          a*(2 : ℝ)^j*(U.card : ℝ) := by
  obtain ⟨u,hu,hmean⟩ := exists_reflection_common_shift W S hS hT hL hW hlarge
  have hlog := zetaMomentLogLoss_pos T
  have hR : 0 < L/(2*zetaMomentLogLoss T) := by positivity
  have hfloor : 2*a*(W.card : ℝ) ≤ L/(2*zetaMomentLogLoss T) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*zetaMomentLogLoss T)).2
    nlinarith
  obtain ⟨j,hj,U,hne,hUsub,hUsep,hUtime,hUvalues,hUmass⟩ :=
    exists_reflection_shifted_value_family W S hS hsep T u ha hR hfloor hmean
  refine ⟨u,hu,j,hj,U,hne,hUsub,hUsep,hUtime,hUvalues,?_⟩
  convert hUmass using 1
  field_simp
  ring

end TaoTrudgianYang2025
