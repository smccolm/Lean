import TaoTrudgianYang2025.SargosPrefixMass
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! One prefix-independent fourth-power majorant, before taking a maximum. -/

noncomputable section

open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargos_weighted_sum_pow_four {ι : Type*} (S : Finset ι)
    (b x : ι → ℝ) (hb : ∀ i ∈ S, 0 ≤ b i) :
    (∑ i ∈ S, b i*x i)^4 ≤ (∑ i ∈ S, b i)^3*(∑ i ∈ S, b i*(x i)^4) := by
  have h₂ : (∑ i ∈ S, b i*x i)^2 ≤
      (∑ i ∈ S, b i)*(∑ i ∈ S, b i*(x i)^2) :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S hb
      (fun i hi => mul_nonneg (hb i hi) (sq_nonneg _))
      (fun i hi => by ring_nf; exact le_rfl)
  have h₄ : (∑ i ∈ S, b i*(x i)^2)^2 ≤
      (∑ i ∈ S, b i)*(∑ i ∈ S, b i*(x i)^4) :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S hb
      (fun i hi => mul_nonneg (hb i hi) (by positivity))
      (fun i hi => by ring_nf; exact le_rfl)
  calc
    _ = ((∑ i ∈ S, b i*x i)^2)^2 := by ring
    _ ≤ ((∑ i ∈ S, b i)*(∑ i ∈ S, b i*(x i)^2))^2 :=
      pow_le_pow_left₀ (sq_nonneg _) h₂ 2
    _ = (∑ i ∈ S, b i)^2*(∑ i ∈ S, b i*(x i)^2)^2 := by ring
    _ ≤ (∑ i ∈ S, b i)^2*((∑ i ∈ S, b i)*(∑ i ∈ S, b i*(x i)^4)) :=
      mul_le_mul_of_nonneg_left h₄ (sq_nonneg _)
    _ = _ := by ring

def sargosFourierFourthMajorant {N : ℕ} [NeZero N] (f : ZMod N → ℂ) : ℝ :=
  (∑ k : ZMod N, sargosPrefixMajorant k)^3*
    (∑ k : ZMod N, sargosPrefixMajorant k*‖ZMod.dft f k‖^4)

theorem sargosFourierFourthMajorant_nonneg {N : ℕ} [NeZero N] (f : ZMod N → ℂ) :
    0 ≤ sargosFourierFourthMajorant f := by
  unfold sargosFourierFourthMajorant
  exact mul_nonneg (pow_nonneg
    (Finset.sum_nonneg (fun k hk => sargosPrefixMajorant_nonneg k)) _)
    (Finset.sum_nonneg (fun k hk => mul_nonneg (sargosPrefixMajorant_nonneg k)
      (by positivity)))

theorem norm_sargosFinitePrefix_le_fourierMajorant {N H : ℕ} [NeZero N]
    (f : ZMod N → ℂ) (hH : H ≤ N) :
    ‖sargosFinitePrefix f H‖ ≤ ∑ k : ZMod N, sargosPrefixMajorant k*‖ZMod.dft f k‖ := by
  rw [sargosFinitePrefix_eq_fourier]
  calc
    _ ≤ ∑ k : ZMod N, ‖sargosPrefixKernel H k*ZMod.dft f k‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_sargosPrefixKernel_le_majorant hH k)
        (norm_nonneg _)

theorem norm_sargosFinitePrefix_pow_four_le {N H : ℕ} [NeZero N]
    (f : ZMod N → ℂ) (hH : H ≤ N) :
    ‖sargosFinitePrefix f H‖^4 ≤ sargosFourierFourthMajorant f := by
  calc
    _ ≤ (∑ k : ZMod N, sargosPrefixMajorant k*‖ZMod.dft f k‖)^4 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sargosFinitePrefix_le_fourierMajorant f hH) 4
    _ ≤ _ := sargos_weighted_sum_pow_four Finset.univ sargosPrefixMajorant
      (fun k => ‖ZMod.dft f k‖) (fun k hk => sargosPrefixMajorant_nonneg k)

end TaoTrudgianYang2025
