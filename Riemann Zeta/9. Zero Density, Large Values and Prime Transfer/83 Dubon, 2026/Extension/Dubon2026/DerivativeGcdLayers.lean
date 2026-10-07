import Dubon2026.PhasePolynomialSigns
import Mathlib.Algebra.Polynomial.FieldDivision

/-! # Successive derivative GCDs remove exactly one copy of each real root -/

namespace Dubon2026

open Polynomial

noncomputable section

theorem polynomial_rootMultiplicity_gcd {P Q : ℝ[X]} (hP : P ≠ 0) (hQ : Q ≠ 0) (t : ℝ) :
    (gcd P Q).rootMultiplicity t = min (P.rootMultiplicity t) (Q.rootMultiplicity t) := by
  apply le_antisymm
  · exact le_min (Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hP (gcd_dvd_left P Q) t)
      (Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hQ (gcd_dvd_right P Q) t)
  · apply (Polynomial.le_rootMultiplicity_iff (gcd_ne_zero_of_left hP)).mpr
    exact dvd_gcd
      ((Polynomial.le_rootMultiplicity_iff hP).mp (min_le_left _ _))
      ((Polynomial.le_rootMultiplicity_iff hQ).mp (min_le_right _ _))

theorem polynomial_rootMultiplicity_le_natDegree (P : ℝ[X]) (t : ℝ) :
    P.rootMultiplicity t ≤ P.natDegree := by
  rw [← Polynomial.count_roots]
  exact (Multiset.count_le_card _ _).trans (Polynomial.card_roots' P)

theorem rootMultiplicity_gcd_derivative {P : ℝ[X]} (hP : P ≠ 0) (t : ℝ) :
    (gcd P P.derivative).rootMultiplicity t = P.rootMultiplicity t - 1 := by
  by_cases hr : P.IsRoot t
  · have hd : P.derivative ≠ 0 := by
      intro hz
      have he := Polynomial.eq_C_of_derivative_eq_zero hz
      have hc : P.coeff 0 = 0 := by
        have hv := hr
        change P.eval t = 0 at hv
        rw [he, Polynomial.eval_C] at hv
        exact hv
      apply hP
      rw [he, hc, Polynomial.C_0]
    rw [polynomial_rootMultiplicity_gcd hP hd,
      Polynomial.derivative_rootMultiplicity_of_root hr, min_eq_right (Nat.sub_le _ _)]
  · have hm := Polynomial.rootMultiplicity_eq_zero hr
    rw [hm, Nat.zero_sub]
    apply Nat.eq_zero_of_le_zero
    simpa only [hm] using
      (Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hP (gcd_dvd_left P P.derivative) t)

/-- The actual iterated polynomial GCD, not a prescribed root-count certificate. -/
def derivativeGcdLayer (P : ℝ[X]) : ℕ → ℝ[X]
  | 0 => P
  | k + 1 => gcd (derivativeGcdLayer P k) (derivativeGcdLayer P k).derivative

theorem derivativeGcdLayer_ne_zero {P : ℝ[X]} (hP : P ≠ 0) (k : ℕ) :
    derivativeGcdLayer P k ≠ 0 := by
  induction k with
  | zero => exact hP
  | succ k ih => exact gcd_ne_zero_of_left ih

theorem derivativeGcdLayer_rootMultiplicity {P : ℝ[X]} (hP : P ≠ 0) (k : ℕ) (t : ℝ) :
    (derivativeGcdLayer P k).rootMultiplicity t = P.rootMultiplicity t - k := by
  induction k with
  | zero => simp only [derivativeGcdLayer, Nat.sub_zero]
  | succ k ih =>
    rw [derivativeGcdLayer, rootMultiplicity_gcd_derivative (derivativeGcdLayer_ne_zero hP k), ih]
    omega

theorem mem_derivativeGcdLayer_roots {P : ℝ[X]} (hP : P ≠ 0) (k : ℕ) (t : ℝ) :
    t ∈ (derivativeGcdLayer P k).roots ↔ k < P.rootMultiplicity t := by
  classical
  rw [← Multiset.count_pos, Polynomial.count_roots, derivativeGcdLayer_rootMultiplicity hP]
  exact Nat.sub_pos_iff_lt

theorem rootMultiplicity_eq_sum_derivativeGcdLayers {P : ℝ[X]} (hP : P ≠ 0) (t : ℝ) :
    P.rootMultiplicity t = ∑ k ∈ Finset.range P.natDegree,
      if t ∈ (derivativeGcdLayer P k).roots then 1 else 0 := by
  classical
  simp only [mem_derivativeGcdLayer_roots hP]
  rw [Finset.sum_boole]
  have hs : (Finset.range P.natDegree).filter (fun k => k < P.rootMultiplicity t) =
      Finset.range (P.rootMultiplicity t) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    exact and_iff_right_of_imp (fun hk => hk.trans_le (polynomial_rootMultiplicity_le_natDegree P t))
  rw [hs, Finset.card_range]
  rfl

end

end Dubon2026
