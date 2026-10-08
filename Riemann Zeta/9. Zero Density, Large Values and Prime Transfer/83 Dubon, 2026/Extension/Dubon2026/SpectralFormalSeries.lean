import Dubon2026.MixedSpectralPositivity
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Analysis.Complex.Order

/-! # Actual finite spectral Euler coefficients and their Newton recurrence -/

namespace Dubon2026

noncomputable section
open scoped BigOperators ComplexOrder

/-- The genuine formal geometric series with spectral root `w`. -/
def spectralGeometricSeries (w : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => w ^ n

/-- The actual finite Euler product as a formal power series. -/
def spectralFormalEuler {ι : Type*} (s : Finset ι) (w : ι → ℂ) : PowerSeries ℂ :=
  ∏ i ∈ s, spectralGeometricSeries (w i)

/-- Multiplication by the literal linear Euler denominator cancels its geometric series. -/
theorem spectralGeometricSeries_mul_denominator (w : ℂ) :
    spectralGeometricSeries w * (1 - PowerSeries.C w * PowerSeries.X) = 1 := by
  have h := congrArg (PowerSeries.rescale w)
    (PowerSeries.mk_one_mul_one_sub_eq_one ℂ)
  simpa [spectralGeometricSeries, map_mul, map_sub, PowerSeries.rescale_X,
    PowerSeries.rescale_mk] using h

/-- Formal differentiation of the actual geometric series. -/
theorem derivative_spectralGeometricSeries (w : ℂ) :
    PowerSeries.derivative ℂ (spectralGeometricSeries w) =
      PowerSeries.C w * spectralGeometricSeries w ^ 2 := by
  have h := (PowerSeries.derivative ℂ).leibniz_of_mul_eq_one
    (spectralGeometricSeries_mul_denominator w)
  simpa [map_sub, Derivation.leibniz, smul_eq_mul, mul_comm] using h

/-- The exact formal logarithmic derivative identity for a finite spectral Euler product. -/
theorem derivative_spectralFormalEuler {ι : Type*} (s : Finset ι) (w : ι → ℂ) :
    PowerSeries.derivative ℂ (spectralFormalEuler s w) =
      spectralFormalEuler s w * ∑ i ∈ s, PowerSeries.C (w i) * spectralGeometricSeries (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [spectralFormalEuler]
  | @insert a s ha ih =>
    simp only [spectralFormalEuler, Finset.prod_insert ha, Finset.sum_insert ha] at ih ⊢
    rw [Derivation.leibniz, derivative_spectralGeometricSeries, ih]
    simp only [smul_eq_mul]
    ring

/-- The constant coefficient of the actual finite Euler product is one. -/
theorem coeff_zero_spectralFormalEuler {ι : Type*} (s : Finset ι) (w : ι → ℂ) :
    PowerSeries.coeff 0 (spectralFormalEuler s w) = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff]
  simp [spectralFormalEuler, spectralGeometricSeries, PowerSeries.constantCoeff_mk]

/-- The actual Euler coefficients satisfy Newton's power-trace recurrence. -/
theorem spectralFormalEuler_newton {ι : Type*} (s : Finset ι) (w : ι → ℂ) (n : ℕ) :
    PowerSeries.coeff (n + 1) (spectralFormalEuler s w) * (n + 1 : ℂ) =
      ∑ t ∈ Finset.antidiagonal n, PowerSeries.coeff t.1 (spectralFormalEuler s w) *
        ∑ i ∈ s, w i ^ (t.2 + 1) := by
  rw [← PowerSeries.coeff_derivative, derivative_spectralFormalEuler, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro t ht
  congr 1
  simp only [map_sum, PowerSeries.coeff_C_mul, spectralGeometricSeries,
    PowerSeries.coeff_mk, pow_succ']

/-- Nonnegative real power traces force every coefficient of the genuine finite Euler product
 to be nonnegative real; the coefficients are not postulated. -/
theorem spectralFormalEuler_coeff_nonneg {ι : Type*} (s : Finset ι) (w : ι → ℂ)
    (hw : ∀ r : ℕ, 0 < r → 0 ≤ ∑ i ∈ s, w i ^ r) (n : ℕ) :
    0 ≤ PowerSeries.coeff n (spectralFormalEuler s w) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => rw [coeff_zero_spectralFormalEuler]; exact zero_le_one
    | succ n =>
      have hn : 0 ≤ PowerSeries.coeff (n + 1) (spectralFormalEuler s w) * (n + 1 : ℂ) := by
        rw [spectralFormalEuler_newton]
        apply Finset.sum_nonneg
        intro t ht
        have ht' := Finset.mem_antidiagonal.mp ht
        exact mul_nonneg (ih t.1 (by omega)) (hw (t.2 + 1) (by omega))
      rcases Complex.nonneg_iff.mp hn with ⟨hr, hi⟩
      simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.natCast_re, Complex.natCast_im, Complex.one_re, Complex.one_im,
        add_zero, zero_add, mul_zero, sub_zero] at hr hi
      have hp : 0 < (n : ℝ) + 1 := by positivity
      exact Complex.nonneg_iff.mpr
        ⟨(mul_nonneg_iff_of_pos_right hp).mp hr,
          ((mul_eq_zero.mp hi.symm).resolve_right (ne_of_gt hp)).symm⟩

/-- A geometric bound on actual power traces gives the same geometric bound for the actual
Euler coefficients, by the proved Newton recurrence. -/
theorem norm_spectralFormalEuler_coeff_le {ι : Type*} (s : Finset ι) (w : ι → ℂ)
    {A : ℝ} (hA : 0 ≤ A) (hw : ∀ r : ℕ, 0 < r → ‖∑ i ∈ s, w i ^ r‖ ≤ A ^ r)
    (n : ℕ) : ‖PowerSeries.coeff n (spectralFormalEuler s w)‖ ≤ A ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [coeff_zero_spectralFormalEuler]
    | succ n =>
      have h : ‖PowerSeries.coeff (n + 1) (spectralFormalEuler s w)‖ * (n + 1 : ℝ) ≤
          A ^ (n + 1) * (n + 1 : ℝ) := by
        calc
          _ = ‖PowerSeries.coeff (n + 1) (spectralFormalEuler s w) * (n + 1 : ℂ)‖ := by
            rw [norm_mul]
            congr 1
            norm_cast
          _ = ‖∑ t ∈ Finset.antidiagonal n, PowerSeries.coeff t.1 (spectralFormalEuler s w) *
                ∑ i ∈ s, w i ^ (t.2 + 1)‖ := by rw [spectralFormalEuler_newton]
          _ ≤ ∑ t ∈ Finset.antidiagonal n, ‖PowerSeries.coeff t.1 (spectralFormalEuler s w) *
                ∑ i ∈ s, w i ^ (t.2 + 1)‖ := norm_sum_le _ _
          _ ≤ ∑ _t ∈ Finset.antidiagonal n, A ^ (n + 1) := by
            apply Finset.sum_le_sum
            intro t ht
            have ht' := Finset.mem_antidiagonal.mp ht
            rw [norm_mul]
            calc
              _ ≤ A ^ t.1 * A ^ (t.2 + 1) := mul_le_mul
                (ih t.1 (by omega)) (hw (t.2 + 1) (by omega))
                (norm_nonneg _) (pow_nonneg hA _)
              _ = _ := by rw [← pow_add]; congr 1; omega
          _ = _ := by simp [Finset.Nat.card_antidiagonal, mul_comm]
      exact (mul_le_mul_iff_left₀ (by positivity : 0 < (n : ℝ) + 1)).mp h

end
end Dubon2026
