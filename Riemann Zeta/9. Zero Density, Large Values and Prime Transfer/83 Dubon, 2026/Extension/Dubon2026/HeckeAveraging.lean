/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors

The finite root-of-unity and convergent-series arguments adapt
Modularforms/QExpansionSlash.lean at
7c41b9b1747d47298f76bdb51f07031087702198, generalized to every positive d.
-/
import Dubon2026.ModularDegeneracyCoefficients
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Field.GeomSum

/-! # Actual Hecke averaging and its convergent Fourier expansion -/

namespace Dubon2026

open Complex Finset UpperHalfPlane

noncomputable section

/-- The actual upper-triangular Hecke point (z+b)/d in the upper half-plane. -/
def heckeUpperPoint (d : ℕ) [NeZero d] (b : ℕ) (τ : ℍ) : ℍ :=
  ⟨((τ : ℂ) + b) / d, by
    simp only [Complex.div_natCast_im, Complex.add_im, Complex.natCast_im, add_zero]
    exact div_pos τ.im_pos (Nat.cast_pos.mpr (Nat.pos_of_neZero d))⟩

/-- The classical averaging operator U_d f(z)=(1/d) Σ_{b<d} f((z+b)/d). -/
def heckeAverage (d : ℕ) [NeZero d] (f : ℍ → ℂ) (τ : ℍ) : ℂ :=
  (d : ℂ)⁻¹ * ∑ b ∈ range d, f (heckeUpperPoint d b τ)

/-- Addition of q-parameters is multiplication, for any real period. -/
theorem qParam_add (h : ℝ) (z w : ℂ) :
    Function.Periodic.qParam h (z + w) =
      Function.Periodic.qParam h z * Function.Periodic.qParam h w := by
  simp only [Function.Periodic.qParam, add_div, mul_add, exp_add]

/-- The finite Hecke translates factor into the vertical q-parameter and a root of unity. -/
theorem qParam_heckeUpperPoint_pow (d : ℕ) [NeZero d] (b : ℕ) (τ : ℍ) (n : ℕ) :
    Function.Periodic.qParam 1 (heckeUpperPoint d b τ : ℂ) ^ n =
      Function.Periodic.qParam 1 ((τ : ℂ) / d) ^ n *
        Function.Periodic.qParam 1 (1 / (d : ℂ)) ^ (n * b) := by
  change Function.Periodic.qParam 1 (((τ : ℂ) + b) / d) ^ n = _
  rw [add_div, qParam_add, show (b : ℂ) / d = b * (1 / d) by ring,
    qParam_nat_mul_eq_pow, mul_pow, ← pow_mul, mul_comm b n]

/-- Exact finite root-of-unity cancellation; no limiting interchange is involved. -/
theorem sum_qParam_reciprocal_pow (d : ℕ) [NeZero d] (n : ℕ) :
    ∑ b ∈ range d, Function.Periodic.qParam 1 (1 / (d : ℂ)) ^ (n * b) =
      if d ∣ n then (d : ℂ) else 0 := by
  set ζ := Function.Periodic.qParam (1 : ℝ) (1 / (d : ℂ)) with hζ_def
  have hζ_prim : IsPrimitiveRoot ζ d := by
    rw [hζ_def, Function.Periodic.qParam]
    convert Complex.isPrimitiveRoot_exp d (NeZero.ne d) using 1
    push_cast
    congr 1
    ring
  split_ifs with hdn
  · simp_rw [pow_mul ζ n, (hζ_prim.pow_eq_one_iff_dvd n).mpr hdn, one_pow,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  · have hζn_ne : ζ ^ n ≠ 1 := mt (hζ_prim.pow_eq_one_iff_dvd n).mp hdn
    simp_rw [pow_mul ζ n]
    rw [geom_sum_eq hζn_ne, show (ζ ^ n) ^ d = 1 from by
      rw [← pow_mul, mul_comm, pow_mul, hζ_prim.pow_eq_one, one_pow]]
    simp

/-- Averaging a genuine convergent Fourier expansion extracts its d-multiple coefficients. -/
theorem hasSum_heckeAverage (d : ℕ) [NeZero d] (f : ℍ → ℂ) (a : ℕ → ℂ) (τ : ℍ)
    (hf : ∀ σ : ℍ, HasSum
      (fun n => a n • Function.Periodic.qParam 1 (σ : ℂ) ^ n) (f σ)) :
    HasSum (fun n => a (d * n) • Function.Periodic.qParam 1 (τ : ℂ) ^ n)
      (heckeAverage d f τ) := by
  set q := Function.Periodic.qParam 1 (τ : ℂ)
  have hinj : Function.Injective (d * · : ℕ → ℕ) := mul_right_injective₀ (NeZero.ne d)
  set w := Function.Periodic.qParam 1 ((τ : ℂ) / d) with hw_def
  set ζ := Function.Periodic.qParam 1 (1 / (d : ℂ))
  have hd_ne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hw_pow_d : w ^ d = q := by
    rw [hw_def, ← qParam_nat_mul_eq_pow]
    congr 1
    field_simp
  have h_rewritten : HasSum
      (fun n => a n • w ^ n * ∑ b ∈ range d, ζ ^ (n * b))
      (∑ b ∈ range d, f (heckeUpperPoint d b τ)) := by
    convert hasSum_sum (fun b _ => hf (heckeUpperPoint d b τ)) using 2 with n
    trans (∑ b ∈ range d, a n * (w ^ n * ζ ^ (n * b)))
    · rw [smul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum, mul_assoc]
    · exact Finset.sum_congr rfl fun b _ => by
        rw [qParam_heckeUpperPoint_pow, smul_eq_mul]
  have h_ind : HasSum (fun n => if d ∣ n then a n • w ^ n else 0)
      ((d : ℂ)⁻¹ * ∑ b ∈ range d, f (heckeUpperPoint d b τ)) := by
    have h_scaled := h_rewritten.const_smul (d : ℂ)⁻¹
    unfold HasSum at h_scaled ⊢
    refine h_scaled.congr fun s => ?_
    congr 1
    ext n
    simp only [smul_eq_mul]
    rw [sum_qParam_reciprocal_pow d n]
    split_ifs
    · rw [mul_comm (a n * w ^ n), ← mul_assoc, inv_mul_cancel₀ hd_ne, one_mul]
    · ring
  rw [← hinj.hasSum_iff (fun x hx => by
    simp only [Set.mem_range, not_exists] at hx
    simp [show ¬d ∣ x from fun ⟨j, hj⟩ => hx j (by omega)])] at h_ind
  simp only [Function.comp_def, show ∀ m, d ∣ d * m from dvd_mul_right d, if_true] at h_ind
  convert h_ind using 2 with m
  rw [smul_eq_mul, smul_eq_mul, pow_mul, hw_pow_d]

end
end Dubon2026
