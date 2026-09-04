import GafniTao.HeathBrownPolynomialPhase
import Mathlib.Analysis.Calculus.Taylor

/-!
# The Lagrange remainder used in Heath-Brown Lemma 1

The source applies Taylor's theorem to `f'` through degree `k-2`.  We expose
that statement on an arbitrary interior segment and retain the exact
factorial.  A later entry bridge supplies these local regularity hypotheses
from the source assumptions after the two endpoint ranges are separated.
-/

open Set

namespace GafniTao

noncomputable section

theorem iteratedDeriv_pred_deriv
    {k : ℕ} (hk : 1 ≤ k) (f : ℝ → ℝ) :
    iteratedDeriv (k - 1) (deriv f) = iteratedDeriv k f := by
  rw [← iteratedDeriv_succ']
  congr 1
  omega

/-- Exact Taylor--Lagrange identity for `f'` on `[n,n+x]`. -/
theorem exists_heathBrown_deriv_taylor_remainder
    {k : ℕ} (hk : 2 ≤ k) {f : ℝ → ℝ} {n x : ℝ}
    (hx : 0 < x)
    (hf : ContDiffOn ℝ (k - 1 : ℕ) (deriv f) (Set.Icc n (n + x))) :
    ∃ ξ ∈ Set.Ioo n (n + x),
      deriv f (n + x) -
          taylorWithinEval (deriv f) (k - 2) (Set.Icc n (n + x)) n (n + x) =
        iteratedDeriv k f ξ * x ^ (k - 1) / (k - 1).factorial := by
  have hne : n ≠ n + x := by linarith
  have huIcc : Set.uIcc n (n + x) = Set.Icc n (n + x) := by
    rw [Set.uIcc_of_le]
    linarith
  have huIoo : Set.uIoo n (n + x) = Set.Ioo n (n + x) := by
    rw [Set.uIoo_of_le]
    linarith
  have horder : k - 2 + 1 = k - 1 := by omega
  have hf' : ContDiffOn ℝ (k - 2 + 1 : ℕ) (deriv f)
      (Set.Icc n (n + x)) := by
    simpa only [horder] using hf
  obtain ⟨ξ, hξ, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := deriv f) (n := k - 2) hne (by simpa only [huIcc] using hf')
  refine ⟨ξ, ?_, ?_⟩
  · simpa [huIoo] using hξ
  · rw [huIcc] at hrem
    rw [hrem]
    have hkOne : 1 ≤ k := by omega
    rw [horder, iteratedDeriv_pred_deriv hkOne f]
    congr 2
    ring

/-- Norm form of the preceding exact remainder identity. -/
theorem norm_heathBrown_deriv_taylor_remainder_le
    {k : ℕ} (hk : 2 ≤ k) {f : ℝ → ℝ} {n x A lambda : ℝ}
    (hx : 0 < x)
    (hf : ContDiffOn ℝ (k - 1 : ℕ) (deriv f) (Set.Icc n (n + x)))
    (hderiv : ∀ ξ ∈ Set.Ioo n (n + x),
      ‖iteratedDeriv k f ξ‖ ≤ A * lambda) :
    ‖deriv f (n + x) -
        taylorWithinEval (deriv f) (k - 2) (Set.Icc n (n + x)) n (n + x)‖ ≤
      A * lambda * x ^ (k - 1) / (k - 1).factorial := by
  obtain ⟨ξ, hξ, hrem⟩ :=
    exists_heathBrown_deriv_taylor_remainder hk hx hf
  have hfac : 0 < ((k - 1).factorial : ℝ) := by positivity
  rw [hrem]
  simp only [norm_div, norm_mul, norm_pow, Real.norm_eq_abs,
    abs_of_pos hx, abs_of_pos hfac]
  have hpow : 0 ≤ x ^ (k - 1) := pow_nonneg hx.le _
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hderiv ξ hξ) hpow) hfac.le

/-- Uniform source form on `0 < x ≤ H`; discarding the positive factorial
only weakens the exact Lagrange bound. -/
theorem norm_heathBrown_deriv_taylor_remainder_le_scale
    {k : ℕ} (hk : 2 ≤ k) {f : ℝ → ℝ} {n x A lambda H : ℝ}
    (hx : 0 < x) (hxH : x ≤ H)
    (hf : ContDiffOn ℝ (k - 1 : ℕ) (deriv f) (Set.Icc n (n + x)))
    (hderiv : ∀ ξ ∈ Set.Ioo n (n + x),
      ‖iteratedDeriv k f ξ‖ ≤ A * lambda) :
    ‖deriv f (n + x) -
        taylorWithinEval (deriv f) (k - 2) (Set.Icc n (n + x)) n (n + x)‖ ≤
      A * lambda * H ^ (k - 1) := by
  have hH : 0 ≤ H := hx.le.trans hxH
  have hmid : n < n + x / 2 := by linarith
  have hmid' : n + x / 2 < n + x := by linarith
  have hAlambda : 0 ≤ A * lambda :=
    (norm_nonneg (iteratedDeriv k f (n + x / 2))).trans
      (hderiv (n + x / 2) ⟨hmid, hmid'⟩)
  have hraw := norm_heathBrown_deriv_taylor_remainder_le
    hk hx hf hderiv
  have hfacOne : (1 : ℝ) ≤ (k - 1).factorial := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hdiv :
      A * lambda * x ^ (k - 1) / (k - 1).factorial ≤
        A * lambda * x ^ (k - 1) := by
    apply div_le_self
    · positivity
    · exact hfacOne
  calc
    ‖deriv f (n + x) -
        taylorWithinEval (deriv f) (k - 2) (Set.Icc n (n + x)) n (n + x)‖ ≤
      A * lambda * x ^ (k - 1) := hraw.trans hdiv
    _ ≤ A * lambda * H ^ (k - 1) := by
      gcongr

#print axioms iteratedDeriv_pred_deriv
#print axioms exists_heathBrown_deriv_taylor_remainder
#print axioms norm_heathBrown_deriv_taylor_remainder_le
#print axioms norm_heathBrown_deriv_taylor_remainder_le_scale

end

end GafniTao
