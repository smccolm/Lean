import Dubon2026.SourceIntegralPrimeTwoProduct
import Dubon2026.SourceJPrimePolynomialDegree

/-! Pole bounds for the three explicit rational prime-two conjugate
coefficients imply degree at most three in the integral j-coordinate.
This uses the existing leading-coefficient lemma and native Hahn valuations,
avoiding any assumption of modular-polynomial symmetry. These are the degree
bounds required to identify the integral cubic from finitely many coefficients
and hence identify the actual degree-two cyclic-quotient roots, DUB-17/18. -/
namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
noncomputable section
open Polynomial

theorem coeff_evalAtJ_leading (P : Polynomial ℤ) :
    (evalAtJ P).coeff (-(P.natDegree : ℤ)) = (P.leadingCoeff : ℚ) := by
  have h := PrimeDegreeAux.coeff_aeval_jqModC_neg_natDegree (P.map (Int.castRingHom ℚ))
  rw [jqModC_rat, natDegree_map_eq_of_injective (Int.cast_injective (α := ℚ)),
    coeff_map] at h
  have he : aeval jq (P.map (Int.castRingHom ℚ)) = evalAtJ P := by
    rw [aeval_def, eval₂_map]
    change eval₂ _ jq P = eval₂ _ jq P
    congr 1
    exact Subsingleton.elim _ _
  rw [he] at h
  exact h

theorem natDegree_le_three_of_qExpand_pole_bound (P : Polynomial ℤ)
    (h : (-6 : WithTop ℤ) ≤ (qExpand ℚ 2 (evalAtJ P)).orderTop) :
    P.natDegree ≤ 3 := by
  by_contra! hd
  have hP : P ≠ 0 := by rintro rfl; simp at hd
  have hz : (qExpand ℚ 2 (evalAtJ P)).coeff (2 * -(P.natDegree : ℤ)) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (lt_of_lt_of_le (by
      change ((2 * -(P.natDegree : ℤ) : ℤ) : WithTop ℤ) < ((-6 : ℤ) : WithTop ℤ)
      exact WithTop.coe_lt_coe.mpr (by omega)) h)
  rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, qExpand_coeff_mul,
    coeff_evalAtJ_leading] at hz
  exact (leadingCoeff_ne_zero.mpr hP) (Int.cast_eq_zero.mp hz)

theorem prime_two_conjugate_order_bounds :
    (-4 : WithTop ℤ) ≤ (qExpand ℚ 4 jq).orderTop ∧
    (-1 : WithTop ℤ) ≤ jq.orderTop ∧
    (-1 : WithTop ℤ) ≤ (qTwist (-1 : ℚˣ) jq).orderTop := by
  have hJ : (-1 : WithTop ℤ) ≤ jq.orderTop :=
    HahnSeries.le_orderTop_iff_forall.mpr fun m hm =>
      coeff_jq_of_lt (WithTop.coe_lt_coe.mp hm)
  refine ⟨?_, hJ, ?_⟩
  · apply HahnSeries.le_orderTop_iff_forall.mpr
    intro m hm
    by_cases hdiv : (4 : ℤ) ∣ m
    · obtain ⟨c, rfl⟩ := hdiv
      rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, qExpand_coeff_mul]
      exact coeff_jq_of_lt (by
        have hm' : 4 * c < (-4 : ℤ) := WithTop.coe_lt_coe.mp hm
        omega)
    · exact qExpand_coeff_of_not_dvd 4 jq hdiv
  · apply HahnSeries.le_orderTop_iff_forall.mpr
    intro m hm
    rw [qTwist_coeff, coeff_jq_of_lt (WithTop.coe_lt_coe.mp hm), mul_zero]

theorem modularPolynomial_two_coeff_natDegree_le (k : ℕ) :
    ((modularPolynomial 2).coeff k).natDegree ≤ 3 := by
  obtain ⟨hA, hB, hC⟩ := prime_two_conjugate_order_bounds
  have hsum (a b : LaurentSeries ℚ) (ha : (-6 : WithTop ℤ) ≤ a.orderTop)
      (hb : (-6 : WithTop ℤ) ≤ b.orderTop) : (-6 : WithTop ℤ) ≤ (a + b).orderTop :=
    (le_min ha hb).trans HahnSeries.min_orderTop_le_orderTop_add
  obtain ⟨h₂, h₁, h₀⟩ := modularPolynomial_two_coefficient_identities
  have hAB : (-5 : WithTop ℤ) ≤ (qExpand ℚ 4 jq * jq).orderTop := by
    simpa only [HahnSeries.orderTop_mul] using add_le_add hA hB
  have hAC : (-5 : WithTop ℤ) ≤ (qExpand ℚ 4 jq * qTwist (-1 : ℚˣ) jq).orderTop := by
    simpa only [HahnSeries.orderTop_mul] using add_le_add hA hC
  have hBC : (-2 : WithTop ℤ) ≤ (jq * qTwist (-1 : ℚˣ) jq).orderTop := by
    simpa only [HahnSeries.orderTop_mul] using add_le_add hB hC
  rcases lt_or_ge k 4 with hk | hk
  · interval_cases k
    · apply natDegree_le_three_of_qExpand_pole_bound
      rw [h₀, HahnSeries.orderTop_neg, HahnSeries.orderTop_mul]
      simpa using add_le_add hAB hC
    · apply natDegree_le_three_of_qExpand_pole_bound
      rw [h₁]
      exact hsum _ _ (hsum _ _ ((by decide : (-6 : WithTop ℤ) ≤ -5).trans hAB)
        ((by decide : (-6 : WithTop ℤ) ≤ -5).trans hAC))
        ((by decide : (-6 : WithTop ℤ) ≤ -2).trans hBC)
    · apply natDegree_le_three_of_qExpand_pole_bound
      rw [h₂, HahnSeries.orderTop_neg]
      exact hsum _ _ (hsum _ _ ((by decide : (-6 : WithTop ℤ) ≤ -4).trans hA)
        ((by decide : (-6 : WithTop ℤ) ≤ -1).trans hB))
        ((by decide : (-6 : WithTop ℤ) ≤ -1).trans hC)
    · have hd : (modularPolynomial 2).natDegree = 3 := modularPolynomial_prime_natDegree 2
      rw [← hd, coeff_natDegree, (modularPolynomial_monic 2).leadingCoeff]
      simp
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [modularPolynomial_prime_natDegree]; omega)]
    simp

end
end Dubon2026.SourceFunctionField.IntegralJCoordinate
