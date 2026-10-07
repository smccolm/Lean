import Dubon2026.Gamma0SievedPrimitive
import Dubon2026.LevelOneEisensteinContinuation
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-! # The actual principal-character factor extracted from congruence lattice rows -/

namespace Dubon2026

open UpperHalfPlane

noncomputable section

/-- The principal character on a natural argument is the literal coprimality indicator. -/
theorem principalCharacter_nat_indicator (Q n : ℕ) :
    (1 : DirichletCharacter ℂ Q) n = if Nat.Coprime n Q then 1 else 0 := by
  classical
  by_cases hn : Nat.Coprime n Q
  · rw [if_pos hn]
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n Q).mpr hn)
  · rw [if_neg hn]
    exact MulChar.map_nonunit _ ((ZMod.isUnit_iff_coprime n Q).not.mpr hn)

/-- The extracted scalar series is exactly the pinned principal-character L-function. -/
theorem coprime_series_eq_LFunctionTrivChar (Q : ℕ) [NeZero Q] {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, if Nat.Coprime n Q then (n : ℂ) ^ (-s) else 0) =
      DirichletCharacter.LFunctionTrivChar Q s := by
  classical
  have hs0 : s ≠ 0 := by
    intro h
    simp only [h, Complex.zero_re] at hs
    linarith
  rw [DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_eq_LSeries _ hs, LSeries]
  apply tsum_congr
  intro n
  rw [LSeries.term_of_ne_zero' hs0, principalCharacter_nat_indicator]
  split_ifs <;> simp [Complex.cpow_neg]

/-- The actual congruence-sieved sum equals L(2s,chi_0) times the primitive Eisenstein series. -/
theorem gamma0SievedSeries_eq_LFunction_eisenstein (Q : ℕ) [NeZero Q]
    {s : ℂ} (hs : 1 < s.re) (z : ℍ) :
    gamma0SievedSeries Q s z =
      DirichletCharacter.LFunctionTrivChar Q (2 * s) * gamma0Eisenstein Q s z := by
  rw [gamma0SievedSeries_eq_coprime_series Q hs z,
    coprime_series_eq_LFunctionTrivChar Q (by
      simp only [two_mul, Complex.add_re]
      linarith)]

/-- The exact scalar completing the primitive Eisenstein series at general positive level. -/
def gamma0CompletionFactor (Q : ℕ) [NeZero Q] (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ (-s) * Complex.Gamma s * DirichletCharacter.LFunctionTrivChar Q (2 * s)

/-- The true general-level completion factor is nonzero in Re(s)>1/2. -/
theorem gamma0CompletionFactor_ne_zero (Q : ℕ) [NeZero Q] {s : ℂ} (hs : 1 / 2 < s.re) :
    gamma0CompletionFactor Q s ≠ 0 := by
  have h2 : 1 < (2 * s).re := by simp only [two_mul, Complex.add_re]; linarith
  have hL : DirichletCharacter.LFunctionTrivChar Q (2 * s) ≠ 0 := by
    rw [DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_eq_LSeries _ h2]
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re _ h2
  exact mul_ne_zero (mul_ne_zero
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
    (Complex.Gamma_ne_zero_of_re_pos (by linarith))) hL

/-- The true general-level completion factor is holomorphic in Re(s)>1/2. -/
theorem differentiableAt_gamma0CompletionFactor (Q : ℕ) [NeZero Q]
    {s : ℂ} (hs : 1 / 2 < s.re) : DifferentiableAt ℂ (gamma0CompletionFactor Q) s := by
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
      ((DirichletCharacter.differentiableAt_LFunction 1 (2 * s) (Or.inl h2)).comp s
        (differentiableAt_id.const_mul 2))

/-- At the pole the completion factor is the principal-character value at two divided by pi. -/
theorem gamma0CompletionFactor_one (Q : ℕ) [NeZero Q] :
    gamma0CompletionFactor Q 1 = DirichletCharacter.LFunctionTrivChar Q 2 / (Real.pi : ℂ) := by
  simp [gamma0CompletionFactor, Complex.cpow_neg_one, div_eq_mul_inv, mul_comm]

end
end Dubon2026
