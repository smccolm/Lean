import Dubon2026.SourceJointChartMonomialDenominators

/-! DUB-17/18 -> Kummer power lifting -> finite localized overlap ->
controlled chart denominators. A polynomial with all roots outside the
coefficient valuation ring is a scalar times a good denominator. Reuses
the existing root-product identity and good-monomial multiplication. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open Polynomial

variable {L : Type*} [Field L] (A : ValuationSubring L)

theorem good_one_sub_C_mul_X {c : L} (hc : A.valuation c < 1) :
    IsGood A (1 - C c * X) := by
  refine ⟨by simp, fun j hj => ?_⟩
  by_cases hj1 : j = 1
  · subst j
    simpa only [coeff_sub, coeff_one, if_neg one_ne_zero, coeff_C_mul_X,
      if_pos rfl, zero_sub, Valuation.map_neg] using hc
  · simp only [coeff_sub, coeff_one, if_neg hj, coeff_C_mul_X, if_neg hj1,
      sub_self, map_zero]
    exact zero_lt_one

theorem good_prod_one_sub (cs : Multiset L)
    (hcs : ∀ c ∈ cs, A.valuation c < 1) :
    IsGood A (cs.map fun c => (1 - C c * X : L[X])).prod := by
  induction cs using Multiset.induction_on with
  | empty => simpa using (IsGoodAt.one (A := A))
  | cons c cs ih =>
    have hc := good_one_sub_C_mul_X A (hcs c (Multiset.mem_cons_self _ _))
    have hs := ih (fun d hd => hcs d (Multiset.mem_cons_of_mem hd))
    simpa using (IsGoodAt.mul (show IsGoodAt A 0 _ from hc)
      (show IsGoodAt A 0 _ from hs))

theorem exists_good_factor_of_roots_outside [IsAlgClosed L] {D : L[X]}
    (hD : D ≠ 0) (hroots : ∀ a ∈ D.roots, 1 < A.valuation a) :
    ∃ (u : L) (t : L[X]), u ≠ 0 ∧ IsGood A t ∧ D = C u * t := by
  classical
  have hsplit : C D.leadingCoeff * (D.roots.map fun a => X - C a).prod = D :=
    C_leadingCoeff_mul_prod_multiset_X_sub_C IsAlgClosed.card_roots_eq_natDegree
  have hroots0 : ∀ a ∈ D.roots, a ≠ 0 := by
    intro a ha h
    have := hroots a ha
    rw [h, map_zero] at this
    exact absurd this (not_lt.mpr zero_le')
  let cs := D.roots.map fun a => a⁻¹
  have hcs : ∀ c ∈ cs, A.valuation c < 1 := by
    intro c hc
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hc
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ (hroots a ha)
  let t : L[X] := (cs.map fun c => 1 - C c * X).prod
  let u := D.leadingCoeff * (D.roots.map fun a => -a).prod
  have hfac : D = C u * t := by
    conv_lhs => rw [← hsplit, prod_X_sub_C_eq_C_mul_prod_one_sub D.roots hroots0]
    rw [C_mul, mul_assoc]
  refine ⟨u, t, ?_, good_prod_one_sub A cs hcs, hfac⟩
  intro hu
  apply hD
  rw [hfac, hu, C_0, zero_mul]

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
