import Dubon2026.RealExponentialZeroCount
import Dubon2026.DirichletPolynomial

/-! # Uniform real-part zero count on every actual horizontal line -/

namespace Dubon2026

open Set

noncomputable section

/-- The real coefficients of the actual horizontal exponential sum at height t. -/
def horizontalRealCoefficients (a : ℕ → ℂ) (t : ℝ) (n : ℕ) : ℝ :=
  (a n * Complex.exp (-Complex.I * (t : ℂ) * (Real.log n : ℂ))).re

theorem horizontal_dirichletSum_re (a : ℕ → ℂ) (N : ℕ) (t σ : ℝ) :
    (dirichletSum a N ((σ : ℂ) + Complex.I * t)).re =
      realExponentialSum (Finset.Icc 1 N) (horizontalRealCoefficients a t)
        (fun n => -Real.log n) σ := by
  rw [dirichletSum_eq_sum_exp]
  simp only [Complex.re_sum, realExponentialSum]
  apply Finset.sum_congr rfl
  intro n _
  have he : -((σ : ℂ) + Complex.I * t) * (Real.log n : ℂ) =
      -Complex.I * (t : ℂ) * (Real.log n : ℂ) + ((-Real.log n * σ : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he, Complex.exp_add, ← Complex.ofReal_exp, ← mul_assoc]
  simp only [horizontalRealCoefficients, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

theorem horizontalRealCoefficients_one {a : ℕ → ℂ} (ha : a 1 = 1) (t : ℝ) :
    horizontalRealCoefficients a t 1 = 1 := by
  simp only [horizontalRealCoefficients, ha, Nat.cast_one, Real.log_one, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero, mul_one, Complex.one_re]

theorem horizontal_real_zero_finset {a : ℕ → ℂ} {N : ℕ} (hN : 1 ≤ N)
    (ha : a 1 = 1) (t : ℝ) :
    ∃ Z : Finset ℝ, (∀ σ : ℝ, σ ∈ Z ↔
      (dirichletSum a N ((σ : ℂ) + Complex.I * t)).re = 0) ∧ Z.card < N := by
  classical
  let s := (Finset.Icc 1 N).filter (fun n => horizontalRealCoefficients a t n ≠ 0)
  have hs : s.Nonempty := by
    refine ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hN⟩, ?_⟩⟩
    rw [horizontalRealCoefficients_one ha]
    exact one_ne_zero
  have hc : ∀ n ∈ s, horizontalRealCoefficients a t n ≠ 0 :=
    fun _ hn => (Finset.mem_filter.mp hn).2
  have hω : Set.InjOn (fun n : ℕ => -Real.log n) s := by
    intro i hi j hj he
    have hi0 : (0 : ℝ) < i := by
      exact_mod_cast (show 0 < i by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hi).1).1; omega)
    have hj0 : (0 : ℝ) < j := by
      exact_mod_cast (show 0 < j by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).1; omega)
    exact Nat.cast_injective (Real.log_injOn_pos hi0 hj0 (neg_injective he))
  have hfin := finite_realExponentialSum_zeros s (horizontalRealCoefficients a t)
    (fun n => -Real.log n) hs hc hω
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · intro σ
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, realExponentialSum_filter_nonzero,
      horizontal_dirichletSum_re]
  · have hz := realExponentialSum_zero_finset_card_lt s (horizontalRealCoefficients a t)
      (fun n => -Real.log n) hs hc hω hfin.toFinset
      (fun x hx => (hfin.mem_toFinset.mp hx))
    have hsN : s.card ≤ N := by
      calc
        s.card ≤ (Finset.Icc 1 N).card := Finset.card_filter_le _ _
        _ = N := by simp
    exact hz.trans_le hsN

end

end Dubon2026
