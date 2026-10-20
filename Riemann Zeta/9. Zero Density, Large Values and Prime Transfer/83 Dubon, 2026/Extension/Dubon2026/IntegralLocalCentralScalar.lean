import Dubon2026.GeneralLinearIntegralNumeratorDegree
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.NormNum

/-! Discharging the central-scalar input over the source coefficient ring.
In a characteristic-zero local ring at least one of 2 and 3 is a unit,
and that unit has infinite order. Consequently the exact induced
numerator-degree bound has no separately supplied scalar witness.
-/

namespace Dubon2026
noncomputable section

universe u
variable (R : Type u) [CommRing R] [IsLocalRing R] [CharZero R]

/-- A characteristic-zero local coefficient ring has an actual infinite-order unit, constructed from 2 or 3. -/
theorem integralLocal_exists_infinite_order_unit :
    ∃ u : Rˣ, Function.Injective (fun w : ℤ => u ^ w) := by
  have hunit : IsUnit (2 : R) ∨ IsUnit (3 : R) := by
    have h := IsLocalRing.isUnit_or_isUnit_of_add_one
      (show (-2 : R) + 3 = 1 by norm_num)
    rcases h with h | h
    · exact Or.inl (by simpa only [neg_neg] using h.neg)
    · exact Or.inr h
  obtain ⟨a, ha, u, hu⟩ : ∃ (a : ℕ), 1 < a ∧ ∃ u : Rˣ, (u : R) = (a : R) := by
    rcases hunit with h | h
    · obtain ⟨u, hu⟩ := h
      exact ⟨2, by decide, u, hu⟩
    · obtain ⟨u, hu⟩ := h
      exact ⟨3, by decide, u, hu⟩
  refine ⟨u, injective_zpow_iff_not_isOfFinOrder.mpr ?_⟩
  intro h
  obtain ⟨m, hm, hpow⟩ := h.exists_pow_eq_one
  have hval := congrArg (fun v : Rˣ => (v : R)) hpow
  simp only [Units.val_pow_eq_pow_val, hu, Units.val_one] at hval
  have hnat : a ^ m = 1 := by exact_mod_cast hval
  exact (ne_of_gt (one_lt_pow₀ ha hm.ne')) hnat

variable [IsDomain R]

/-- Over the actual source coefficient ring the exact original numerator degree is bounded by its weight and determinant denominator, with no scalar witness hypothesis. -/
theorem integralLocal_induced_numerator_degree_le {n : ℕ}
    (lam : Fin n → ℤ) (d : ℕ) (P : MvPolynomial (Fin n × Fin n) R)
    (hP : generalLinearRegularFractionMap R n d P ∈
      generalLinearIntegralInducedSubmodule R n lam) :
    P.totalDegree ≤ ((∑ i, lam i) + (n : ℤ) * d).toNat := by
  obtain ⟨u, hu⟩ := integralLocal_exists_infinite_order_unit R
  exact generalLinearIntegralInduced_numerator_degree_le u hu lam d P hP

/-- Every original induced function over the source local domain has a polynomial numerator with the precise source-weight degree bound. IntegralInducedDenominatorBound supplies the uniform denominator separately. -/
theorem integralLocal_induced_exists_degree_bounded_fraction {n : ℕ}
    (lam : Fin n → ℤ) (p : generalLinearIntegralInducedSubmodule R n lam) :
    ∃ (d : ℕ) (P : MvPolynomial (Fin n × Fin n) R),
      generalLinearRegularFractionMap R n d P = p.val ∧
        P.totalDegree ≤ ((∑ i, lam i) + (n : ℤ) * d).toNat := by
  obtain ⟨d, P, hP⟩ := generalLinearRegular_exists_fraction R n p.val
  refine ⟨d, P, hP, integralLocal_induced_numerator_degree_le R lam d P ?_⟩
  rw [hP]
  exact p.property

end
end Dubon2026
