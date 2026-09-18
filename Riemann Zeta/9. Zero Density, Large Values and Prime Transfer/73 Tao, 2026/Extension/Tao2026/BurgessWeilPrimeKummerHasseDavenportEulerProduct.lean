import Tao2026.BurgessWeilPrimeKummerHasseDavenportRecurrence
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Finite weighted Euler products for Hasse--Davenport

This file proves the formal-power-series identity behind the remaining
closed-point recurrence. For a finite collection of positive degrees `d a`
and weights `w a`, the Euler product

`A(X) = ∏ a, (1 - w(a) X^(d a))⁻¹`

has logarithmic derivative

`A'(X) = (∑ a, d(a) w(a) X^(d(a)-1) / (1-w(a)X^(d(a)))) A(X)`.

The local coefficients are computed exactly: the degree-`m` closed-point
coefficient is `d(a) * w(a)^(m/d(a))` when `d(a) ∣ m`, and zero otherwise.
Taking coefficients gives `HasseDavenportLogDerivativeRecurrence` with no
analytic convergence assumptions. The next layer specializes the finite
alphabet to monic irreducible polynomials of bounded degree.
-/

open scoped BigOperators

noncomputable section

namespace Tao2026

open PowerSeries

/-- The geometric power series with coefficient `w^n` in degree `n`. -/
def weightedGeometricSeries (w : ℂ) : ℂ⟦X⟧ :=
  rescale w (mk 1)

@[simp] theorem coeff_weightedGeometricSeries (w : ℂ) (n : ℕ) :
    coeff n (weightedGeometricSeries w) = w ^ n := by
  simp [weightedGeometricSeries, coeff_rescale]

theorem weightedGeometricSeries_mul (w : ℂ) :
    weightedGeometricSeries w * (1 - C w * X) = 1 := by
  have h := congrArg (fun f : ℂ⟦X⟧ => rescale w f)
    (mk_one_mul_one_sub_eq_one ℂ)
  simpa [weightedGeometricSeries, map_mul, map_sub, rescale_X] using h

/-- The local weighted Euler factor `(1 - w X^d)⁻¹`. -/
def weightedEulerFactor (w : ℂ) (d : ℕ) : ℂ⟦X⟧ :=
  (1 - C w * X ^ d)⁻¹

theorem weightedEulerFactor_eq_subst (w : ℂ) {d : ℕ} (hd : d ≠ 0) :
    weightedEulerFactor w d = subst (X ^ d) (weightedGeometricSeries w) := by
  rw [weightedEulerFactor]
  symm
  apply (PowerSeries.eq_inv_iff_mul_eq_one (by simp [hd])).2
  have hsubst : PowerSeries.HasSubst (X ^ d : ℂ⟦X⟧) :=
    PowerSeries.HasSubst.X_pow hd
  let F := PowerSeries.substAlgHom (R := ℂ) hsubst
  have h := congrArg F
    (weightedGeometricSeries_mul w)
  have hC : F (C w) = C w := F.commutes w
  have hX : F X = (X ^ d : ℂ⟦X⟧) := PowerSeries.substAlgHom_X hsubst
  have hOne : F (1 : ℂ⟦X⟧) = 1 := map_one F
  rw [map_mul F (weightedGeometricSeries w) (1 - C w * X),
    map_sub F 1 (C w * X), map_mul F (C w) X, hC, hX, hOne] at h
  have hF : F (weightedGeometricSeries w) =
      subst (X ^ d) (weightedGeometricSeries w) := by
    exact congrFun (PowerSeries.coe_substAlgHom hsubst)
      (weightedGeometricSeries w)
  rw [hF] at h
  exact h

theorem coeff_weightedEulerFactor (w : ℂ) {d n : ℕ} (hd : d ≠ 0) :
    coeff n (weightedEulerFactor w d) = if d ∣ n then w ^ (n / d) else 0 := by
  rw [weightedEulerFactor_eq_subst w hd, coeff_subst_X_pow hd]
  simp

/-- The unshifted local logarithmic-derivative numerator
`d w X^d / (1-wX^d)`. -/
def weightedEulerLogFactor (w : ℂ) (d : ℕ) : ℂ⟦X⟧ :=
  C (d : ℂ) * C w * X ^ d * weightedEulerFactor w d

theorem weightedEulerLogFactor_eq_subst_sub_one (w : ℂ) {d : ℕ} (hd : d ≠ 0) :
    weightedEulerLogFactor w d =
      C (d : ℂ) * subst (X ^ d) (weightedGeometricSeries w - 1) := by
  have hgeom : C w * X * weightedGeometricSeries w =
      weightedGeometricSeries w - 1 := by
    have h := weightedGeometricSeries_mul w
    linear_combination -h
  have hsubst : PowerSeries.HasSubst (X ^ d : ℂ⟦X⟧) :=
    PowerSeries.HasSubst.X_pow hd
  let F := PowerSeries.substAlgHom (R := ℂ) hsubst
  have h := congrArg F hgeom
  have hC : F (C w) = C w := F.commutes w
  have hX : F X = (X ^ d : ℂ⟦X⟧) := PowerSeries.substAlgHom_X hsubst
  have hOne : F (1 : ℂ⟦X⟧) = 1 := map_one F
  have hG : F (weightedGeometricSeries w) =
      subst (X ^ d) (weightedGeometricSeries w) := by
    exact congrFun (PowerSeries.coe_substAlgHom hsubst)
      (weightedGeometricSeries w)
  have hsub : F (weightedGeometricSeries w - 1) =
      subst (X ^ d) (weightedGeometricSeries w - 1) := by
    exact congrFun (PowerSeries.coe_substAlgHom hsubst)
      (weightedGeometricSeries w - 1)
  have hsubstSub : subst (X ^ d) (weightedGeometricSeries w - 1) =
      subst (X ^ d) (weightedGeometricSeries w) - (1 : ℂ⟦X⟧) := by
    rw [← hsub, map_sub F (weightedGeometricSeries w) 1, hG, hOne]
  rw [map_mul F (C w * X) (weightedGeometricSeries w),
    map_mul F (C w) X, map_sub F, hC, hX, hOne, hG] at h
  rw [weightedEulerLogFactor, weightedEulerFactor_eq_subst w hd]
  rw [hsubstSub, ← h]
  ring

theorem coeff_weightedEulerLogFactor (w : ℂ) {d m : ℕ}
    (hd : d ≠ 0) (hm : 0 < m) :
    coeff m (weightedEulerLogFactor w d) =
      if d ∣ m then (d : ℂ) * w ^ (m / d) else 0 := by
  rw [weightedEulerLogFactor_eq_subst_sub_one w hd, coeff_C_mul,
    coeff_subst_X_pow hd]
  by_cases hdm : d ∣ m
  · rw [if_pos hdm, if_pos hdm]
    have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    have hdle : d ≤ m := Nat.le_of_dvd hm hdm
    have hqpos : 0 < m / d := Nat.div_pos hdle hdpos
    simp [hqpos.ne']
  · rw [if_neg hdm, if_neg hdm, mul_zero]

/-- The shifted local logarithmic derivative
`d w X^(d-1) / (1-wX^d)`. -/
def weightedEulerShiftedLogFactor (w : ℂ) (d : ℕ) : ℂ⟦X⟧ :=
  C (d : ℂ) * C w * X ^ (d - 1) * weightedEulerFactor w d

theorem X_mul_weightedEulerShiftedLogFactor (w : ℂ) {d : ℕ} (hd : d ≠ 0) :
    X * weightedEulerShiftedLogFactor w d = weightedEulerLogFactor w d := by
  rw [weightedEulerShiftedLogFactor, weightedEulerLogFactor]
  conv_rhs =>
    rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hd), pow_add, pow_one]
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hd)]
  ring

theorem coeff_weightedEulerShiftedLogFactor (w : ℂ) {d m : ℕ}
    (hd : d ≠ 0) (hm : 0 < m) :
    coeff (m - 1) (weightedEulerShiftedLogFactor w d) =
      if d ∣ m then (d : ℂ) * w ^ (m / d) else 0 := by
  have h := congrArg (coeff m) (X_mul_weightedEulerShiftedLogFactor w hd)
  have hlhs : coeff m (X * weightedEulerShiftedLogFactor w d) =
      coeff (m - 1) (weightedEulerShiftedLogFactor w d) := by
    simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm.ne')]
      using coeff_succ_X_mul (m - 1) (weightedEulerShiftedLogFactor w d)
  rw [hlhs] at h
  rw [coeff_weightedEulerLogFactor w hd hm] at h
  exact h

theorem derivative_weightedMonomial (w : ℂ) (d : ℕ) :
    d⁄dX ℂ (C w * X ^ d) = C (d : ℂ) * C w * X ^ (d - 1) := by
  rw [Derivation.leibniz]
  simp only [derivative_C, derivative_pow, derivative_X, smul_eq_mul,
    mul_zero, add_zero, mul_one]
  rw [show (d : ℂ⟦X⟧) = C (d : ℂ) by rfl]
  ring

theorem X_mul_derivative_weightedMonomial (w : ℂ) (d : ℕ) :
    X * d⁄dX ℂ (C w * X ^ d) = C (d : ℂ) * (C w * X ^ d) := by
  rw [Derivation.leibniz]
  simp only [derivative_C, derivative_pow, derivative_X, smul_eq_mul,
    mul_zero, add_zero, mul_one]
  rw [show (d : ℂ⟦X⟧) = C (d : ℂ) by rfl]
  by_cases hd : d = 0
  · subst d
    simp
  · conv_rhs =>
      rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hd), pow_add, pow_one]
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hd)]
    ring

theorem X_mul_derivative_weightedEulerFactor (w : ℂ) (d : ℕ) :
    X * d⁄dX ℂ (weightedEulerFactor w d) =
      weightedEulerLogFactor w d * weightedEulerFactor w d := by
  rw [weightedEulerFactor, derivative_inv']
  rw [map_sub, weightedEulerLogFactor]
  rw [show d⁄dX ℂ (1 : ℂ⟦X⟧) = 0 by simp]
  simp only [zero_sub]
  calc
    X * (-((1 - C w * X ^ d)⁻¹ ^ 2) * -(d⁄dX ℂ (C w * X ^ d))) =
        (1 - C w * X ^ d)⁻¹ ^ 2 *
          (X * d⁄dX ℂ (C w * X ^ d)) := by ring
    _ = (1 - C w * X ^ d)⁻¹ ^ 2 *
          (C (d : ℂ) * (C w * X ^ d)) := by
      rw [X_mul_derivative_weightedMonomial]
    _ = C (d : ℂ) * C w * X ^ d * weightedEulerFactor w d *
          (1 - C w * X ^ d)⁻¹ := by
      rw [weightedEulerFactor]
      ring

theorem derivative_weightedEulerFactor (w : ℂ) (d : ℕ) :
    d⁄dX ℂ (weightedEulerFactor w d) =
      weightedEulerShiftedLogFactor w d * weightedEulerFactor w d := by
  rw [weightedEulerFactor, derivative_inv']
  rw [map_sub, weightedEulerShiftedLogFactor]
  rw [show d⁄dX ℂ (1 : ℂ⟦X⟧) = 0 by simp]
  simp only [zero_sub]
  rw [derivative_weightedMonomial]
  rw [weightedEulerFactor]
  ring

/-- The finite product of the local weighted Euler factors. -/
def weightedEulerProduct {α : Type*} (s : Finset α)
    (w : α → ℂ) (d : α → ℕ) : ℂ⟦X⟧ :=
  ∏ a ∈ s, weightedEulerFactor (w a) (d a)

def weightedEulerLogDerivative {α : Type*} (s : Finset α)
    (w : α → ℂ) (d : α → ℕ) : ℂ⟦X⟧ :=
  ∑ a ∈ s, weightedEulerLogFactor (w a) (d a)

/-- The sum of the shifted local logarithmic derivatives. -/
def weightedEulerShiftedLogDerivative {α : Type*} (s : Finset α)
    (w : α → ℂ) (d : α → ℕ) : ℂ⟦X⟧ :=
  ∑ a ∈ s, weightedEulerShiftedLogFactor (w a) (d a)

theorem X_mul_derivative_weightedEulerProduct {α : Type*} (s : Finset α)
    (w : α → ℂ) (d : α → ℕ) :
    X * d⁄dX ℂ (weightedEulerProduct s w d) =
      weightedEulerLogDerivative s w d * weightedEulerProduct s w d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [weightedEulerProduct, weightedEulerLogDerivative]
  | @insert a s ha ih =>
      rw [weightedEulerProduct, weightedEulerLogDerivative]
      simp only [Finset.prod_insert ha, Finset.sum_insert ha]
      rw [Derivation.leibniz]
      simp only [smul_eq_mul]
      change X * (weightedEulerFactor (w a) (d a) *
          d⁄dX ℂ (weightedEulerProduct s w d) +
          weightedEulerProduct s w d * d⁄dX ℂ (weightedEulerFactor (w a) (d a))) = _
      calc
        _ = weightedEulerFactor (w a) (d a) *
              (X * d⁄dX ℂ (weightedEulerProduct s w d)) +
            weightedEulerProduct s w d *
              (X * d⁄dX ℂ (weightedEulerFactor (w a) (d a))) := by ring
        _ = weightedEulerFactor (w a) (d a) *
              (weightedEulerLogDerivative s w d * weightedEulerProduct s w d) +
            weightedEulerProduct s w d *
              (weightedEulerLogFactor (w a) (d a) *
                weightedEulerFactor (w a) (d a)) := by
          rw [ih, X_mul_derivative_weightedEulerFactor]
        _ = (weightedEulerLogFactor (w a) (d a) +
              weightedEulerLogDerivative s w d) *
            (weightedEulerFactor (w a) (d a) * weightedEulerProduct s w d) := by ring

/-- Exact finite Euler-product logarithmic differentiation. -/
theorem derivative_weightedEulerProduct {α : Type*} (s : Finset α)
    (w : α → ℂ) (d : α → ℕ) :
    d⁄dX ℂ (weightedEulerProduct s w d) =
      weightedEulerShiftedLogDerivative s w d * weightedEulerProduct s w d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [weightedEulerProduct, weightedEulerShiftedLogDerivative]
  | @insert a s ha ih =>
      rw [weightedEulerProduct, weightedEulerShiftedLogDerivative]
      simp only [Finset.prod_insert ha, Finset.sum_insert ha]
      rw [Derivation.leibniz]
      simp only [smul_eq_mul]
      change weightedEulerFactor (w a) (d a) *
          d⁄dX ℂ (weightedEulerProduct s w d) +
          weightedEulerProduct s w d * d⁄dX ℂ (weightedEulerFactor (w a) (d a)) =
        (weightedEulerShiftedLogFactor (w a) (d a) +
          weightedEulerShiftedLogDerivative s w d) *
          (weightedEulerFactor (w a) (d a) * weightedEulerProduct s w d)
      rw [ih, derivative_weightedEulerFactor]
      ring

/-- The ordinary coefficient sequence of a finite weighted Euler product. -/
def weightedEulerProductCoefficient {α : Type*} (s : Finset α)
    (w : α → ℂ) (d : α → ℕ) (n : ℕ) : ℂ :=
  coeff n (weightedEulerProduct s w d)

/-- The closed-point coefficient sequence supplied by the logarithmic
derivative, with a harmless zero value in degree zero. -/
def weightedEulerClosedPointCoefficient {α : Type*} (s : Finset α)
    (w : α → ℂ) (d : α → ℕ) : ℕ → ℂ
  | 0 => 0
  | n + 1 => coeff n (weightedEulerShiftedLogDerivative s w d)

theorem coeff_weightedEulerShiftedLogDerivative_sum {α : Type*} (s : Finset α)
    (w : α → ℂ) (d : α → ℕ) (n : ℕ) :
    coeff n (weightedEulerShiftedLogDerivative s w d) =
      ∑ a ∈ s, coeff n (weightedEulerShiftedLogFactor (w a) (d a)) := by
  rw [weightedEulerShiftedLogDerivative]
  rw [map_sum]

theorem weightedEulerClosedPointCoefficient_eq_sum {α : Type*} (s : Finset α)
    (w : α → ℂ) (d : α → ℕ) (hd : ∀ a ∈ s, d a ≠ 0)
    (n : ℕ) :
    weightedEulerClosedPointCoefficient s w d (n + 1) =
      ∑ a ∈ s, if d a ∣ n + 1 then
        (d a : ℂ) * w a ^ ((n + 1) / d a) else 0 := by
  rw [weightedEulerClosedPointCoefficient,
    coeff_weightedEulerShiftedLogDerivative_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hlocal := coeff_weightedEulerShiftedLogFactor (w a)
    (d := d a) (m := n + 1) (hd a ha) (by omega)
  simpa only [Nat.add_sub_cancel] using hlocal

/-- Coefficient extraction from the finite Euler-product identity gives the
exact Hasse--Davenport logarithmic-derivative recurrence. -/
theorem weightedEulerProduct_logDerivativeRecurrence {α : Type*} (s : Finset α)
    (w : α → ℂ) (d : α → ℕ) :
    HasseDavenportLogDerivativeRecurrence
      (weightedEulerProductCoefficient s w d)
      (weightedEulerClosedPointCoefficient s w d) := by
  intro n
  change (n + 1 : ℂ) * coeff (n + 1) (weightedEulerProduct s w d) =
    ∑ k ∈ Finset.range (n + 1),
      coeff k (weightedEulerShiftedLogDerivative s w d) *
        coeff (n - k) (weightedEulerProduct s w d)
  have h := congrArg (coeff n) (derivative_weightedEulerProduct s w d)
  rw [coeff_derivative, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simpa [mul_comm] using h

end Tao2026
