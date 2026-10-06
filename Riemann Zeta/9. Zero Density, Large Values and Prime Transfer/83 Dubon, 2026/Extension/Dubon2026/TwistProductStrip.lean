import Dubon2026.TwistProducts
import Mathlib.Analysis.Complex.Hadamard

/-! # Three-lines hypotheses for actual finite products of Dirichlet polynomials -/

namespace Dubon2026

open Set
open scoped BigOperators

noncomputable section

theorem norm_dirichletSum_le_real_majorant (a : ℕ → ℂ) (N : ℕ) {s : ℂ} {l : ℝ}
    (hs : l ≤ s.re) :
    ‖dirichletSum a N s‖ ≤ ∑ n ∈ Finset.Icc 1 N, ‖a n‖ * Real.exp (-l * Real.log n) := by
  rw [dirichletSum_eq_sum_exp]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
    Complex.ofReal_im, mul_zero, sub_zero]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.mp hn).1)
  exact mul_le_mul_of_nonneg_right (neg_le_neg hs) hlog

theorem bddAbove_twistProduct_strip {ι : Type*} [Fintype ι] (a : ℕ → ℂ) (N : ℕ)
    (v : ι → PrimeTorus N) (l u : ℝ) :
    BddAbove ((norm ∘ twistProduct a N v) '' Complex.HadamardThreeLines.verticalClosedStrip l u) := by
  classical
  refine ⟨∏ i, ∑ n ∈ Finset.Icc 1 N,
    ‖twistedCoefficients a N (v i) n‖ * Real.exp (-l * Real.log n), ?_⟩
  rintro y ⟨s, hs, rfl⟩
  change ‖∏ i, dirichletSum (twistedCoefficients a N (v i)) N s‖ ≤ _
  rw [norm_prod]
  apply Finset.prod_le_prod (fun i _ => norm_nonneg _)
  exact fun i _ => norm_dirichletSum_le_real_majorant _ N hs.1

theorem norm_twistProduct_le_three_lines {ι : Type*} [Fintype ι] (a : ℕ → ℂ) (N : ℕ)
    (v : ι → PrimeTorus N) {l u : ℝ} (hlu : l < u) {s : ℂ}
    (hs : s.re ∈ Icc l u) {A B : ℝ}
    (hA : ∀ z : ℂ, z.re = l → ‖twistProduct a N v z‖ ≤ A)
    (hB : ∀ z : ℂ, z.re = u → ‖twistProduct a N v z‖ ≤ B) :
    ‖twistProduct a N v s‖ ≤ A ^ (1 - (s.re - l) / (u - l)) * B ^ ((s.re - l) / (u - l)) := by
  apply Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip' hlu hs
    (Differentiable.diffContOnCl (fun z => (analyticAt_twistProduct a N v z).differentiableAt))
    (bddAbove_twistProduct_strip a N v l u)
  · exact fun z hz => hA z hz
  · exact fun z hz => hB z hz

end

end Dubon2026
