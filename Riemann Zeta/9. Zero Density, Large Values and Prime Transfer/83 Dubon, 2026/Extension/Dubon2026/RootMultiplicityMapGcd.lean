import Dubon2026.EuclideanSturm
import Mathlib.RingTheory.PrincipalIdealDomain

/-! # Multiplicities of polynomial GCDs after extension of scalars -/

namespace Dubon2026

open Polynomial

noncomputable section

variable {K L : Type*} [Field K] [Field L] [DecidableEq K]

theorem rootMultiplicity_map_gcd (f : K →+* L) {P Q : K[X]}
    (hP : P ≠ 0) (hQ : Q ≠ 0) (t : L) :
    ((gcd P Q).map f).rootMultiplicity t =
      min ((P.map f).rootMultiplicity t) ((Q.map f).rootMultiplicity t) := by
  classical
  apply le_antisymm
  · exact le_min
      (Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd (Polynomial.map_ne_zero hP)
        (Polynomial.map_dvd f (gcd_dvd_left P Q)) t)
      (Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd (Polynomial.map_ne_zero hQ)
        (Polynomial.map_dvd f (gcd_dvd_right P Q)) t)
  · apply (Polynomial.le_rootMultiplicity_iff
      (Polynomial.map_ne_zero (gcd_ne_zero_of_left hP))).mpr
    obtain ⟨a, b, hab⟩ := exists_gcd_eq_mul_add_mul P Q
    rw [hab, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul]
    exact dvd_add
      (dvd_mul_of_dvd_left
        ((Polynomial.le_rootMultiplicity_iff (Polynomial.map_ne_zero hP)).mp (min_le_left _ _)) _)
      (dvd_mul_of_dvd_left
        ((Polynomial.le_rootMultiplicity_iff (Polynomial.map_ne_zero hQ)).mp (min_le_right _ _)) _)

theorem rootMultiplicity_map_gcd_derivative [CharZero L] (f : K →+* L) {P : K[X]}
    (hP : P ≠ 0) (t : L) :
    ((gcd P P.derivative).map f).rootMultiplicity t = (P.map f).rootMultiplicity t - 1 := by
  classical
  by_cases hr : (P.map f).IsRoot t
  · have hd : P.derivative ≠ 0 := by
      intro hz
      have hder : (P.map f).derivative = 0 := by rw [Polynomial.derivative_map, hz]; simp
      have he := Polynomial.eq_C_of_derivative_eq_zero hder
      have hc : (P.map f).coeff 0 = 0 := by
        have hv := hr
        change (P.map f).eval t = 0 at hv
        rw [he, Polynomial.eval_C] at hv
        exact hv
      apply Polynomial.map_ne_zero (f := f) hP
      rw [he, hc, Polynomial.C_0]
    rw [rootMultiplicity_map_gcd f hP hd t, ← Polynomial.derivative_map,
      Polynomial.derivative_rootMultiplicity_of_root hr, min_eq_right (Nat.sub_le _ _)]
  · have hm := Polynomial.rootMultiplicity_eq_zero hr
    rw [hm, Nat.zero_sub]
    apply Nat.eq_zero_of_le_zero
    simpa only [hm] using
      (Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd (Polynomial.map_ne_zero hP)
        (Polynomial.map_dvd f (gcd_dvd_left P P.derivative)) t)

/-- Division by the derivative GCD retains exactly one copy of every root. -/
theorem rootMultiplicity_map_derivativeQuotient [CharZero L] [DecidableEq L]
    (f : K →+* L) {P : K[X]}
    (hP : P ≠ 0) (t : L) :
    ((P / gcd P P.derivative).map f).rootMultiplicity t =
      if (P.map f).IsRoot t then 1 else 0 := by
  classical
  have hg : gcd P P.derivative ≠ 0 := gcd_ne_zero_of_left hP
  have he := EuclideanDomain.mul_div_cancel' hg (gcd_dvd_left P P.derivative)
  have hem := congrArg (Polynomial.map f) he
  simp only [Polynomial.map_mul] at hem
  have hn : (gcd P P.derivative).map f * (P / gcd P P.derivative).map f ≠ 0 := by
    rw [hem]
    exact Polynomial.map_ne_zero hP
  have hm := Polynomial.rootMultiplicity_mul (x := t) hn
  rw [hem, rootMultiplicity_map_gcd_derivative f hP] at hm
  by_cases hr : (P.map f).IsRoot t
  · rw [if_pos hr]
    have hp : 0 < (P.map f).rootMultiplicity t :=
      (Polynomial.rootMultiplicity_pos (Polynomial.map_ne_zero hP)).mpr hr
    omega
  · rw [if_neg hr]
    have hp := Polynomial.rootMultiplicity_eq_zero hr
    omega

end

end Dubon2026
