import Dubon2026.LatticeEpsteinPrimitive
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-! # The actual primitive full-level Eisenstein continuation and its residue -/

namespace Dubon2026

open UpperHalfPlane Filter
open scoped Topology

noncomputable section

/-- The exact scalar completing the primitive full-level Eisenstein series. -/
def eisensteinCompletionFactor (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ (-s) * Complex.Gamma s * riemannZeta (2 * s)

/-- The continuation obtained from the actual lattice Mellin transform. -/
def levelOneEisensteinContinuation (z : ℍ) (s : ℂ) : ℂ :=
  latticeCompletedMellin z s / eisensteinCompletionFactor s

/-- The completion factor is nonzero in Re(s)>1/2. -/
theorem eisensteinCompletionFactor_ne_zero {s : ℂ} (hs : 1 / 2 < s.re) :
    eisensteinCompletionFactor s ≠ 0 := by
  have h2 : 1 < (2 * s).re := by simp only [two_mul, Complex.add_re]; linarith
  exact mul_ne_zero (mul_ne_zero
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
    (Complex.Gamma_ne_zero_of_re_pos (by linarith)))
    (riemannZeta_ne_zero_of_one_lt_re h2)

/-- The completion factor is holomorphic throughout Re(s)>1/2. -/
theorem differentiableAt_eisensteinCompletionFactor {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ eisensteinCompletionFactor s := by
  have hG : DifferentiableAt ℂ Complex.Gamma s := Complex.differentiableAt_Gamma s (by
    intro n hn
    have h := congrArg Complex.re hn
    simp only [Complex.neg_re, Complex.natCast_re] at h
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith)
  have h2 : 2 * s ≠ (1 : ℂ) := by
    intro h
    have h' := congrArg Complex.re h
    simp only [two_mul, Complex.add_re, Complex.one_re] at h'
    linarith
  exact (((differentiableAt_id.neg).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).mul hG).mul
      ((differentiableAt_riemannZeta h2).comp s (differentiableAt_id.const_mul 2))

/-- The constructed continuation equals the actual primitive-row series in its defining half-plane. -/
theorem levelOneEisensteinContinuation_eq (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    levelOneEisensteinContinuation z s = gamma0Eisenstein 1 s z := by
  rw [levelOneEisensteinContinuation, latticeCompletedMellin_eq_completed_eisenstein z hs]
  exact mul_div_cancel_left₀ _ (eisensteinCompletionFactor_ne_zero (by linarith))

/-- The actual primitive full-level continuation is holomorphic in Re(s)>1/2 away from s=1. -/
theorem differentiableAt_levelOneEisensteinContinuation (z : ℍ) {s : ℂ}
    (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (levelOneEisensteinContinuation z) s := by
  have hs0 : s ≠ 0 := by
    intro h
    simp only [h, Complex.zero_re] at hs
    linarith
  exact (differentiableAt_latticeCompletedMellin z hs0 hs1).div
    (differentiableAt_eisensteinCompletionFactor hs) (eisensteinCompletionFactor_ne_zero hs)

/-- The exact completing scalar at the pole is π/6. -/
theorem eisensteinCompletionFactor_one : eisensteinCompletionFactor 1 = (Real.pi : ℂ) / 6 := by
  rw [eisensteinCompletionFactor, Complex.cpow_neg_one, Complex.Gamma_one, mul_one,
    mul_one, riemannZeta_two]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-- The genuine primitive-row Eisenstein continuation has residue exactly 3/π at s=1. -/
theorem levelOneEisensteinContinuation_residue_one (z : ℍ) :
    Tendsto (fun s : ℂ => (s - 1) * levelOneEisensteinContinuation z s)
      (𝓝[≠] 1) (𝓝 (3 / (Real.pi : ℂ))) := by
  have hd : Tendsto eisensteinCompletionFactor (𝓝[≠] (1 : ℂ))
      (𝓝 (eisensteinCompletionFactor 1)) := (differentiableAt_eisensteinCompletionFactor
    (s := (1 : ℂ)) (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h := (latticeCompletedMellin_residue_one z).div hd
    (eisensteinCompletionFactor_ne_zero (s := (1 : ℂ)) (by norm_num))
  change Tendsto (fun s : ℂ => ((s - 1) * latticeCompletedMellin z s) /
    eisensteinCompletionFactor s) (𝓝[≠] 1) (𝓝 ((1 / 2 : ℂ) / eisensteinCompletionFactor 1)) at h
  have he : (1 / 2 : ℂ) / eisensteinCompletionFactor 1 = 3 / (Real.pi : ℂ) := by
    rw [eisensteinCompletionFactor_one]
    field_simp
    norm_num
  simpa only [he, levelOneEisensteinContinuation, mul_div_assoc] using h

end
end Dubon2026
