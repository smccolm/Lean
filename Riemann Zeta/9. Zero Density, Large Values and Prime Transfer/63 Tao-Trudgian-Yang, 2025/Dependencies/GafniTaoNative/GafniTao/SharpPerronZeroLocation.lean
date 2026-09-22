import GafniTao.SharpPerronResidues
import GafniTao.CriticalStripReflection

/-!
# Zero location for the `Re s ≥ -1` Perron rectangle

The contour is shifted only to `Re s = -1`, so it encloses no trivial zeta
zero.  The lemmas below prove that fact directly from the functional equation
and then identify every enclosed zeta zero with the project's closed critical
strip zero set.
-/

open Complex Set
open RiemannZeta.GuthMaynard

noncomputable section

namespace GafniTao

/-- Zeta has no real zero in `(-2,0)`.  This is the exact real-axis fragment
needed for the left side of the Perron rectangle. -/
theorem riemannZeta_neg_real_Ioo_two_ne_zero
    {a : ℝ} (ha : 0 < a) (ha2 : a < 2) :
    riemannZeta (((-a : ℝ) : ℂ)) ≠ 0 := by
  let w : ℂ := ((1 + a : ℝ) : ℂ)
  have hwZeta : riemannZeta w ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_lt_re
    simp [w]
    linarith
  have hwNegNat : ∀ n : ℕ, w ≠ -(n : ℂ) := by
    intro n hn
    have hre : w.re = (-(n : ℂ)).re := congrArg Complex.re hn
    simp [w] at hre
    have hnnonneg : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
    linarith
  have hwOne : w ≠ 1 := by
    intro h
    have hre : w.re = (1 : ℂ).re := congrArg Complex.re h
    simp [w] at hre
    linarith
  have hpow : (2 * (Real.pi : ℂ)) ^ (-w) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    left
    norm_num [Complex.ofReal_ne_zero, Real.pi_ne_zero]
  have hGamma : Complex.Gamma w ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    simp [w]
    linarith
  have hcos : Complex.cos ((Real.pi : ℂ) * w / 2) ≠ 0 := by
    rw [Complex.cos_ne_zero_iff]
    intro k hk
    have hre : ((Real.pi : ℂ) * w / 2).re =
        (((2 * (k : ℂ) + 1) * (Real.pi : ℂ) / 2).re) :=
      congrArg Complex.re hk
    have hmain : 1 + a = (2 * k + 1 : ℝ) := by
      have hscaled : Real.pi * (1 + a) / 2 =
          (2 * (k : ℝ) + 1) * Real.pi / 2 := by
        simpa [w, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hre
      nlinarith [Real.pi_pos]
    have haeq : a = (2 * k : ℝ) := by linarith
    cases le_or_gt k 0 with
    | inl hkNonpos =>
        have hkreal : (2 * k : ℝ) ≤ 0 := by
          exact_mod_cast
            (mul_nonpos_of_nonneg_of_nonpos
              (by norm_num : (0 : ℤ) ≤ 2) hkNonpos)
        linarith
    | inr hkPos =>
        have hkOne : (1 : ℤ) ≤ k := by omega
        have hkreal : (2 : ℝ) ≤ 2 * k := by
          exact_mod_cast
            (mul_le_mul_of_nonneg_left hkOne (by norm_num : (0 : ℤ) ≤ 2))
        linarith
  have hfactor : 2 * (2 * (Real.pi : ℂ)) ^ (-w) * Complex.Gamma w *
      Complex.cos ((Real.pi : ℂ) * w / 2) * riemannZeta w ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpow) hGamma) hcos)
      hwZeta
  have hfe := riemannZeta_one_sub (s := w) hwNegNat hwOne
  have hone : 1 - w = (((-a : ℝ) : ℂ)) := by
    dsimp [w]
    apply Complex.ext <;> simp
  rw [hone] at hfe
  rw [hfe]
  exact hfactor

/-- Zeta zeros of positive ordinate lie in the closed critical strip. -/
theorem zeta_zero_re_mem_of_im_pos
    {s : ℂ} (hs : riemannZeta s = 0) (him : 0 < s.im) :
    0 ≤ s.re ∧ s.re ≤ 1 := by
  refine ⟨?_, ?_⟩
  · by_contra hre
    push Not at hre
    set w : ℂ := 1 - s with hw
    have hwre : 1 < w.re := by
      rw [hw]
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hwn : ∀ n : ℕ, w ≠ -(n : ℂ) := by
      intro n h
      have h' := congrArg Complex.re h
      simp only [Complex.neg_re, Complex.natCast_re] at h'
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hw1 : w ≠ 1 := by
      intro h
      have h' := congrArg Complex.re h
      simp only [Complex.one_re] at h'
      linarith
    have hfe := riemannZeta_one_sub hwn hw1
    have h1w : (1 : ℂ) - w = s := by
      rw [hw]
      ring
    rw [h1w, hs] at hfe
    have hzetaw : riemannZeta w ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re hwre.le
    have hGamma : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hwn
    have htwoPi : ((2 : ℂ) * (Real.pi : ℂ)) ^ (-w) ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero (by
        simp only [ne_eq, mul_eq_zero, not_or]
        exact ⟨two_ne_zero, by exact_mod_cast Real.pi_ne_zero⟩)]
      exact Complex.exp_ne_zero _
    have hprod := hfe.symm
    simp only [mul_eq_zero] at hprod
    have hcos : Complex.cos ((Real.pi : ℂ) * w / 2) = 0 := by
      rcases hprod with ((((h | h) | h) | h) | h)
      · norm_num at h
      · exact absurd h htwoPi
      · exact absurd h hGamma
      · exact h
      · exact absurd h hzetaw
    rw [Complex.cos_eq_zero_iff] at hcos
    obtain ⟨k, hk⟩ := hcos
    have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have htwo : (Real.pi : ℂ) * w =
        (Real.pi : ℂ) * (2 * (k : ℂ) + 1) := by
      linear_combination 2 * hk
    have hwk : w = 2 * (k : ℂ) + 1 := mul_left_cancel₀ hpi htwo
    have himw := congrArg Complex.im hwk
    simp [hw] at himw
    linarith
  · by_contra hre
    push Not at hre
    exact riemannZeta_ne_zero_of_one_le_re hre.le hs

/-- Every zeta zero in the closed half-plane `Re s ≥ -1` is in the closed
critical strip.  This includes negative ordinates and the real axis. -/
theorem zeta_zero_re_mem_of_neg_one_le
    {s : ℂ} (hsLeft : -1 ≤ s.re) (hs : riemannZeta s = 0) :
    0 ≤ s.re ∧ s.re ≤ 1 := by
  rcases lt_trichotomy s.im 0 with him | him | him
  · have hs1 : s ≠ 1 := by
      intro h
      subst s
      exact riemannZeta_one_ne_zero hs
    have hstarZero : riemannZeta (star s) = 0 := by
      rw [riemannZeta_conj s hs1, hs]
      simp
    have hpos : 0 < (star s).im := by simp; linarith
    simpa using zeta_zero_re_mem_of_im_pos hstarZero hpos
  · have hsReal : s = (s.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using him
    by_cases hre : 0 ≤ s.re
    · have hupper : s.re ≤ 1 := by
        by_contra hnot
        push Not at hnot
        exact riemannZeta_ne_zero_of_one_le_re hnot.le hs
      exact ⟨hre, hupper⟩
    · have haPos : 0 < -s.re := by linarith
      have haTwo : -s.re < 2 := by linarith
      have hne := riemannZeta_neg_real_Ioo_two_ne_zero haPos haTwo
      apply False.elim
      apply hne
      rw [neg_neg, ← hsReal]
      exact hs
  · exact zeta_zero_re_mem_of_im_pos hs him

end GafniTao
