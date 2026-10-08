import Dubon2026.PrimitiveSecondRankinIdentity
import Dubon2026.CuspRankinPoleNumerator
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-! # Holomorphic continuation of the genuine symmetric-square Euler function -/

namespace Dubon2026

noncomputable section

/-- The actual pole-removed principal-character function is nonzero on the closed right half-plane. -/
theorem principal_pole_numerator_ne_zero (Q : ℕ) [NeZero Q] {s : ℂ} (hs : 1 ≤ s.re) :
    DirichletCharacter.LFunctionTrivChar₁ Q s ≠ 0 := by
  by_cases hs1 : s = 1
  · subst s
    exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero Q
  · rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs1]
    exact mul_ne_zero (sub_ne_zero.mpr hs1)
      (DirichletCharacter.LFunction_ne_zero_of_one_le_re (1 : DirichletCharacter ℂ Q) (.inr hs1) hs)

/-- The exact genuine Rankin numerator divided by the pole-removed principal factor, with the actual finite ramified correction. -/
def primitiveSecondContinuation {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (s : ℂ) : ℂ :=
  cuspRankinPoleNumerator f.toCuspForm s * primitiveRankinBadCorrection f s *
    DirichletCharacter.LFunctionTrivChar Q (2 * s) /
      DirichletCharacter.LFunctionTrivChar₁ Q s

/-- The actual Rankin pole numerator is analytic on the open half-plane Re(s)>1/2. -/
theorem cuspRankinPoleNumerator_analyticOnNhd {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 < k) :
    AnalyticOnNhd ℂ (cuspRankinPoleNumerator f.toCuspForm) {s | 1 / 2 < s.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  exact (differentiableAt_cuspRankinPoleNumerator f.toCuspForm hk hs).differentiableWithinAt

/-- The actual principal-character factor at twice the parameter is holomorphic on Re(s)>1/2. -/
theorem principal_doubled_analyticOnNhd (Q : ℕ) [NeZero Q] :
    AnalyticOnNhd ℂ (fun s : ℂ => DirichletCharacter.LFunctionTrivChar Q (2 * s))
      {s | 1 / 2 < s.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  have hs2 : 2 * s ≠ 1 := by
    intro he
    have hre := congrArg Complex.re he
    norm_num [Complex.mul_re] at hre
    change 1 / 2 < s.re at hs
    linarith
  exact ((DirichletCharacter.differentiableAt_LFunction (1 : DirichletCharacter ℂ Q)
    (2 * s) (.inl hs2)).comp s (differentiableAt_id.const_mul 2)).differentiableWithinAt

/-- The genuine symmetric-square continuation is analytic on a neighborhood of every point of Re(s)≥1, without a Deligne hypothesis. -/
theorem primitiveSecondContinuation_analyticOnNhd {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 < k) :
    AnalyticOnNhd ℂ (primitiveSecondContinuation f) {s | 1 ≤ s.re} := by
  intro s hs
  have hs' : 1 / 2 < s.re := by change 1 ≤ s.re at hs; linarith
  exact (((cuspRankinPoleNumerator_analyticOnNhd f hk s hs').mul
    ((primitiveRankinBadCorrection_differentiable f).analyticAt s)).mul
      (principal_doubled_analyticOnNhd Q s hs')).div
        ((DirichletCharacter.differentiable_LFunctionTrivChar₁ Q).analyticAt s)
        (principal_pole_numerator_ne_zero Q hs)

/-- The holomorphic continuation agrees with the original genuine symmetric-square Euler product throughout its absolute-convergence half-plane. -/
theorem primitiveSecondContinuation_eq_symmetric {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 < k) {s : ℂ} (hs : 1 < s.re) :
    primitiveSecondContinuation f s = primitiveSymmetricLFunction f 2 s := by
  have hs1 : s ≠ 1 := by intro he; simp [he] at hs
  have hn := principal_pole_numerator_ne_zero Q hs.le
  rw [primitiveSecondContinuation, div_eq_iff hn,
    cuspRankinPoleNumerator_eq f.toCuspForm hk (by linarith) hs1,
    cuspRankinContinuation_eq_series f.toCuspForm hk.le hs,
    DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs1]
  calc
    _ = (s - 1) * (cuspRankinSeries f.toCuspForm s * primitiveRankinBadCorrection f s *
        DirichletCharacter.LFunctionTrivChar Q (2 * s)) := by ring
    _ = _ := by rw [← primitive_second_rankin_global_identity f hk.le hs]; ring

/-- The genuine symmetric-square Euler function admits a holomorphic continuation across its full boundary line. Nonvanishing there is a separate theorem. -/
theorem primitive_second_symmetric_holomorphic_continuation {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 < k) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F {s | 1 ≤ s.re} ∧
      Set.EqOn F (primitiveSymmetricLFunction f 2) {s | 1 < s.re} :=
  ⟨primitiveSecondContinuation f, primitiveSecondContinuation_analyticOnNhd f hk,
    fun _ hs => primitiveSecondContinuation_eq_symmetric f hk hs⟩

end
end Dubon2026
