import Dubon2026.SourceToricFourierCharacters
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic.Ring

/-! DUB-17/18 -> original Gamma1 genus preservation -> finite elliptic
fibers -> integral toric coordinates. Finite Fourier transforms of integer
polynomials give integer coefficients and exact inversion at nonzero
characters. Adapted from the Apache-2.0 Anthropic FLT reference pinned at
6e837e75355538c7f80bab5b956861e86c4eacc2; native AddChar orthogonality is used.
The ambient field is kept general because the same identity is required
in the complex field and in every residue field away from the level. -/
namespace Dubon2026.SourceFunctionField.GammaOne.ToricFourier
noncomputable section
open Polynomial
variable {F : Type*} [Field F] {M : ℕ} [NeZero M] {z : F} (hz : IsPrimitiveRoot z M)

/-- Sum of the integer polynomial coefficients at exponents divisible by the level. -/
def avg (M : ℕ) (R : ℤ[X]) : ℤ :=
  ∑ j ∈ Finset.range (R.natDegree + 1), if M ∣ j then R.coeff j else 0

theorem sum_aeval (R : ℤ[X]) : ∑ a : ZMod M, aeval (ψ hz a) R = (M : F) * (avg M R : ℤ) := by
  classical
  simp_rw [aeval_eq_sum_range]
  rw [Finset.sum_comm, avg, Int.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp_rw [zsmul_eq_mul]
  rw [← Finset.mul_sum]
  have h : ∑ a : ZMod M, ψ hz a ^ j = if M ∣ j then (M : F) else 0 := by
    simp_rw [ψ_pow hz _ j]
    have : ∀ a : ZMod M, (j : ZMod M) * a = a * (j : ZMod M) := fun a => mul_comm _ _
    simp_rw [this]
    rw [sum_ψ_mul hz (j : ZMod M)]
    exact if_congr (ZMod.natCast_eq_zero_iff j M) rfl rfl
  rw [h]
  split_ifs <;> simp [mul_comm]

/-- The integer Fourier coefficient of a polynomial evaluated on nonzero level roots. -/
def four (M : ℕ) (c : ZMod M) (R : ℤ[X]) : ℤ := M * avg M (X ^ (-c).val * R) - R.eval 1

theorem filter_ne_zero_eq : (Finset.univ.filter fun a : ZMod M => a ≠ 0) = Finset.univ.erase 0 := by
  classical
  exact Finset.filter_ne' _ _

theorem sum_filter_aeval (c : ZMod M) (R : ℤ[X]) :
    ∑ a ∈ Finset.univ.filter (fun a : ZMod M => a ≠ 0), ψ hz (-(a * c)) * aeval (ψ hz a) R =
      ((four M c R : ℤ) : F) := by
  classical
  have h1 : ∀ a : ZMod M, ψ hz (-(a * c)) * aeval (ψ hz a) R = aeval (ψ hz a) (X ^ (-c).val * R) := by
    intro a
    rw [map_mul, map_pow, aeval_X, ψ_pow hz a (-c).val, ZMod.natCast_zmod_val]
    congr 2
    ring
  simp_rw [h1]
  rw [filter_ne_zero_eq, Finset.sum_erase_eq_sub (Finset.mem_univ _), sum_aeval hz, four,
    Int.cast_sub, Int.cast_mul, Int.cast_natCast, AddChar.map_zero_eq_one]
  congr 1
  rw [aeval_def, eval₂_at_one, eq_intCast, eval_mul, eval_pow, eval_X, one_pow, one_mul]

theorem fourier_inversion (g : ZMod M → F) (s : ZMod M) (hs : s ≠ 0) :
    ∑ c : ZMod M, ψ hz (s * c) *
        ∑ a ∈ Finset.univ.filter (fun a : ZMod M => a ≠ 0), ψ hz (-(a * c)) * g a =
      (M : F) * g s := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ a : ZMod M, ∑ c : ZMod M, ψ hz (s * c) * (ψ hz (-(a * c)) * g a) =
      (if a = s then (M : F) else 0) * g a := by
    intro a
    have : ∀ c : ZMod M, ψ hz (s * c) * (ψ hz (-(a * c)) * g a) = ψ hz (c * (s - a)) * g a := by
      intro c
      rw [← mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    simp_rw [this]
    rw [← Finset.sum_mul, sum_ψ_mul hz (s - a)]
    congr 1
    simp only [sub_eq_zero]
    by_cases h : a = s
    · rw [if_pos h.symm, if_pos h]
    · rw [if_neg (Ne.symm h), if_neg h]
  simp_rw [h, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp [hs]

end
end Dubon2026.SourceFunctionField.GammaOne.ToricFourier
