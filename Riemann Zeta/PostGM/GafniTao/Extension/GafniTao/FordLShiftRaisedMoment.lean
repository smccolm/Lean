import GafniTao.FordLShiftMaximum

/-!
# Ford Lemma 3.3: the raw shift and the raised system

Ford's raised system deletes coordinates through `d+1`.  The raw finite
difference already vanishes through `d`; at coordinate `d+1` it is a constant.
Consequently the raw one-variable moment is the raised-system moment plus a
fixed phase vector.  This file proves that statement over the integer
polynomial system, including the degree-one endpoint.
-/

open Polynomial

namespace GafniTao

noncomputable section

def fordLDifferencePhase
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (y : ℕ) : Fin k → ℤ :=
  fun j => if (j : ℕ) + 1 ≤ d + 1 then
    (fordIntegerFiniteDifference (y : ℤ) (Ψ.poly j)).eval 0
  else 0

theorem fordIntegerFiniteDifference_eval_constant_below_succ
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (hT : 0 < T) (y : ℕ) (hy : 0 < y)
    (j : Fin k) (hj : (j : ℕ) + 1 ≤ d + 1)
    (x : ℤ) :
    (fordIntegerFiniteDifference (y : ℤ) (Ψ.poly j)).eval x =
      (fordIntegerFiniteDifference (y : ℤ) (Ψ.poly j)).eval 0 := by
  by_cases hjd : (j : ℕ) + 1 ≤ d
  · rw [Ψ.zero_below j hjd]
    simp [fordIntegerFiniteDifference]
  · have hdj : d < (j : ℕ) + 1 := Nat.lt_of_not_ge hjd
    have hdegree : (Ψ.poly j).natDegree = 1 := by
      rw [Ψ.degree_above j hdj]
      omega
    have hdegreeQ :
        ((Ψ.poly j).map (Int.castRingHom ℚ)).natDegree = 0 + 1 := by
      rw [natDegree_map_eq_of_injective Int.cast_injective, hdegree]
    have hleadQ :
        ((Ψ.poly j).map (Int.castRingHom ℚ)).leadingCoeff ≠ 0 := by
      rw [leadingCoeff_map_of_injective Int.cast_injective]
      change ((Ψ.poly j).leadingCoeff : ℚ) ≠ 0
      rw [Ψ.leadingCoeff_above j hdj]
      positivity
    have hyQ : (y : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hy)
    have hdegreeDiffQ :
        (fordFiniteDifference (y : ℚ)
          ((Ψ.poly j).map (Int.castRingHom ℚ))).natDegree = 0 :=
      fordFiniteDifference_natDegree hdegreeQ hleadQ hyQ
    have hdegreeDiffZ :
        (fordIntegerFiniteDifference (y : ℤ) (Ψ.poly j)).natDegree = 0 := by
      rw [← natDegree_map_eq_of_injective
          (f := Int.castRingHom ℚ) Int.cast_injective,
        fordIntegerFiniteDifference_map]
      exact hdegreeDiffQ
    rw [eq_C_of_natDegree_eq_zero hdegreeDiffZ]
    simp

theorem fordLSignedShiftMoment_true_eq_phase_add_raised
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (hT : 0 < T) (m : ℕ) (hm : 0 < m)
    (h : FordPositiveShift P m) (z : Fin P) :
    fordLSignedShiftMoment Ψ m (true, h) z =
      fordLDifferencePhase Ψ (h.1 * m) +
        fordPolynomialSingleMoment
          (fordIntegerDifferenceSystem Ψ hT (h.1 * m)
            (Nat.mul_pos (by
              have hh := h.property
              rw [Finset.mem_Icc] at hh
              omega) hm)) z := by
  funext j
  let x : ℤ := ((((z : ℕ) + 1 : ℕ) : ℤ))
  let y : ℕ := h.1 * m
  have hhpos : 0 < h.1 := by
    have hh := h.property
    rw [Finset.mem_Icc] at hh
    omega
  by_cases hj : (j : ℕ) ≤ d
  · have hlow : (j : ℕ) + 1 ≤ d + 1 := by omega
    have hconst := fordIntegerFiniteDifference_eval_constant_below_succ
      Ψ hT y (Nat.mul_pos hhpos hm) j hlow x
    unfold fordLSignedShiftMoment fordLDifferencePhase
      fordPolynomialSingleMoment fordIntegerDifferenceSystem
    simp only [if_true, Pi.add_apply]
    rw [if_pos hlow, if_pos hlow]
    simp only [Polynomial.eval_zero, add_zero]
    rw [← fordIntegerFiniteDifference_eval]
    simpa [x, y] using hconst
  · have hlow : ¬(j : ℕ) + 1 ≤ d + 1 := by omega
    unfold fordLSignedShiftMoment fordLDifferencePhase
      fordPolynomialSingleMoment fordIntegerDifferenceSystem
    simp only [if_true, Pi.add_apply]
    rw [if_neg hlow, if_neg hlow]
    simp only [zero_add]
    rw [fordIntegerFiniteDifference_eval]

#print axioms fordIntegerFiniteDifference_eval_constant_below_succ
#print axioms fordLSignedShiftMoment_true_eq_phase_add_raised

end

end GafniTao
