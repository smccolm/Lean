import Dubon2026.LocalSpectralLogDerivative
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries

/-! # The genuine global finite-rank spectral Euler product on Re(s)>1 -/

namespace Dubon2026

open Filter
open scoped Topology

noncomputable section

/-- The actual global product of all linear spectral denominators. -/
def spectralGlobalDenominator {d : ℕ} (w : Nat.Primes → Fin d → ℂ) (s : ℂ) : ℂ :=
  ∏' v : Nat.Primes × Fin d, (1 - w v.1 v.2 * (((v.1 : ℕ) : ℂ) ^ (-s)))

/-- The genuine reciprocal global spectral Euler product. -/
def spectralGlobalLSeries {d : ℕ} (w : Nat.Primes → Fin d → ℂ) (s : ℂ) : ℂ :=
  (spectralGlobalDenominator w s)⁻¹

/-- The prime power majorant is summable over every actual finite spectral rank. -/
theorem summable_prime_spectral_majorant (d : ℕ) {a : ℝ} (ha : 1 < a) :
    Summable (fun v : Nat.Primes × Fin d => ((v.1 : ℕ) : ℝ) ^ (-a)) := by
  have hp : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-a)) :=
    (Real.summable_nat_rpow.mpr (by linarith : -a < -1)).comp_injective
      (Subtype.val_injective : Function.Injective (fun p : Nat.Primes => (p : ℕ)))
  have hf : Summable (fun v : Fin d × Nat.Primes => ((v.2 : ℕ) : ℝ) ^ (-a)) :=
    (summable_prod_of_nonneg (fun v : Fin d × Nat.Primes => Real.rpow_nonneg (Nat.cast_nonneg (v.2 : ℕ)) (-a))).mpr
      ⟨fun _ => hp, Summable.of_finite⟩
  exact hf.prod_symm

/-- Every true linear spectral perturbation is bounded by the same prime majorant on a smaller half-plane. -/
theorem norm_spectral_prime_perturbation_le {d : ℕ} {w : Nat.Primes → Fin d → ℂ}
    (hw : ∀ p i, ‖w p i‖ ≤ 1) (v : Nat.Primes × Fin d) {a : ℝ} {s : ℂ}
    (hs : a ≤ s.re) :
    ‖-(w v.1 v.2 * (((v.1 : ℕ) : ℂ) ^ (-s)))‖ ≤ ((v.1 : ℕ) : ℝ) ^ (-a) := by
  rw [norm_neg, norm_mul]
  calc
    _ ≤ 1 * ‖((v.1 : ℕ) : ℂ) ^ (-s)‖ := mul_le_mul_of_nonneg_right (hw _ _) (norm_nonneg _)
    _ = ((v.1 : ℕ) : ℝ) ^ (-s.re) := by
      rw [one_mul, Complex.norm_natCast_cpow_of_pos v.1.property.pos, Complex.neg_re]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast v.1.property.one_le) (neg_le_neg hs)

/-- The actual global spectral perturbations are absolutely summable on Re(s)>1. -/
theorem summable_norm_spectral_prime_perturbation {d : ℕ} {w : Nat.Primes → Fin d → ℂ}
    (hw : ∀ p i, ‖w p i‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun v : Nat.Primes × Fin d => ‖-(w v.1 v.2 * (((v.1 : ℕ) : ℂ) ^ (-s)))‖) :=
  (summable_prime_spectral_majorant d hs).of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun v => norm_spectral_prime_perturbation_le hw v le_rfl)

/-- The genuine spectral product converges locally uniformly on each smaller Euler half-plane. -/
theorem spectralGlobalDenominator_multipliableLocallyUniformlyOn {d : ℕ} {w : Nat.Primes → Fin d → ℂ}
    (hw : ∀ p i, ‖w p i‖ ≤ 1) {a : ℝ} (ha : 1 < a) :
    MultipliableLocallyUniformlyOn
      (fun v : Nat.Primes × Fin d => fun s : ℂ => 1 - w v.1 v.2 * (((v.1 : ℕ) : ℂ) ^ (-s)))
      {s : ℂ | a < s.re} := by
  have he := Summable.multipliableLocallyUniformlyOn_one_add
    (f := fun v : Nat.Primes × Fin d => fun s : ℂ => -(w v.1 v.2 * (((v.1 : ℕ) : ℂ) ^ (-s))))
    (isOpen_lt continuous_const Complex.continuous_re) (summable_prime_spectral_majorant d ha)
    (Filter.Eventually.of_forall (fun v s hs => norm_spectral_prime_perturbation_le hw v hs.le))
    (fun v => ((primeDirichletCoordinate_differentiable v.1).const_mul (w v.1 v.2)).neg.continuous.continuousOn)
  simpa only [sub_eq_add_neg] using he

/-- No genuine global spectral denominator vanishes in its absolute Euler half-plane. -/
theorem spectralGlobalDenominator_ne_zero {d : ℕ} {w : Nat.Primes → Fin d → ℂ}
    (hw : ∀ p i, ‖w p i‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) : spectralGlobalDenominator w s ≠ 0 := by
  apply tprod_one_add_ne_zero_of_summable (f := fun v : Nat.Primes × Fin d =>
    -(w v.1 v.2 * (((v.1 : ℕ) : ℂ) ^ (-s))))
  · intro v
    have hz := norm_primeDirichletCoordinate_le v.1 (by linarith : 0 < s.re) le_rfl
    exact spectralEulerDenominator_ne_zero (hw _ _) (hz.1.trans_lt hz.2)
  · exact summable_norm_spectral_prime_perturbation hw hs

/-- Local uniform convergence of the real Euler factors proves differentiability of the actual infinite product. -/
theorem spectralGlobalDenominator_differentiableAt {d : ℕ} {w : Nat.Primes → Fin d → ℂ}
    (hw : ∀ p i, ‖w p i‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ (spectralGlobalDenominator w) s := by
  let a : ℝ := (1 + s.re) / 2
  have ha : 1 < a := by dsimp [a]; linarith
  have hsa : a < s.re := by dsimp [a]; linarith
  have hU : IsOpen {t : ℂ | a < t.re} := isOpen_lt continuous_const Complex.continuous_re
  have hprod := (spectralGlobalDenominator_multipliableLocallyUniformlyOn hw ha).hasProdLocallyUniformlyOn
  have hd := hprod.differentiableOn
    (Filter.Eventually.of_forall (fun t => by
      simpa only [Finset.prod_fn] using
        DifferentiableOn.finsetProd (u := t) (fun v _ =>
          (((primeDirichletCoordinate_differentiable v.1).const_mul (w v.1 v.2)).const_sub 1).differentiableOn))) hU
  exact hd.differentiableAt (hU.mem_nhds hsa)

/-- The genuine spectral Euler L-function is nonzero on Re(s)>1. -/
theorem spectralGlobalLSeries_ne_zero {d : ℕ} {w : Nat.Primes → Fin d → ℂ}
    (hw : ∀ p i, ‖w p i‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) : spectralGlobalLSeries w s ≠ 0 :=
  inv_ne_zero (spectralGlobalDenominator_ne_zero hw hs)

/-- The actual reciprocal global spectral product is holomorphic throughout its Euler half-plane. -/
theorem spectralGlobalLSeries_analyticOnNhd {d : ℕ} {w : Nat.Primes → Fin d → ℂ}
    (hw : ∀ p i, ‖w p i‖ ≤ 1) : AnalyticOnNhd ℂ (spectralGlobalLSeries w) {s : ℂ | 1 < s.re} := by
  have hd : DifferentiableOn ℂ (spectralGlobalLSeries w) {s : ℂ | 1 < s.re} := by
    intro s hs
    exact ((spectralGlobalDenominator_differentiableAt hw hs).inv
      (spectralGlobalDenominator_ne_zero hw hs)).differentiableWithinAt
  exact hd.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

end
end Dubon2026
