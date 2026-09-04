import GafniTao.HeathBrownSourceAbel

/-!
# Heath-Brown's source Abel transfer

This is the exact transfer from polynomial partial sums to the translated
source sum.  The error weight is `e(g_n(h))`, with `g_n` defined from the
literal Taylor polynomial; no abstract bounded coefficient replaces it.
-/

open Finset Set
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem heathBrownPhase_taylorError_mul_polynomial
    (k : ℕ) (f : ℝ → ℝ) (n x : ℝ) :
    heathBrownPhase (f (n + x)) =
      heathBrownPhase (heathBrownTaylorError k f n x) *
        heathBrownPhase (heathBrownTaylorPolynomial k f n x) := by
  rw [← heathBrownPhase_add]
  unfold heathBrownTaylorError
  rw [sub_add_cancel]

theorem heathBrown_shifted_source_sum_eq_weighted_polynomial
    (k H : ℕ) (f : ℝ → ℝ) (n : ℝ) :
    (∑ h ∈ Finset.Icc 1 H, heathBrownPhase (f (n + h))) =
      ∑ h ∈ Finset.Icc 1 H,
        heathBrownPhase (heathBrownTaylorError k f n h) *
          heathBrownPhase (heathBrownTaylorPolynomial k f n h) := by
  apply Finset.sum_congr rfl
  intro h hh
  exact heathBrownPhase_taylorError_mul_polynomial k f n h

/-- Exact Abel consumer once the literal weight variation and polynomial
partial sums have been bounded. -/
theorem heathBrown_shifted_source_sum_norm_le_of_variation
    {k H : ℕ} (hH : 1 ≤ H) (f : ℝ → ℝ) (n : ℝ)
    (R D : ℝ) (hR : 0 ≤ R)
    (hpartial : ∀ j ∈ Finset.Icc 1 H,
      ‖∑ h ∈ Finset.Icc 1 j,
        heathBrownPhase (heathBrownTaylorPolynomial k f n h)‖ ≤ R)
    (hvariation :
      (∑ j ∈ Finset.Ico 1 H,
        ‖heathBrownPhase (heathBrownTaylorError k f n ((j + 1 : ℕ) : ℝ)) -
          heathBrownPhase (heathBrownTaylorError k f n j)‖) ≤ D) :
    ‖∑ h ∈ Finset.Icc 1 H, heathBrownPhase (f (n + h))‖ ≤
      (1 + D) * R := by
  rw [heathBrown_shifted_source_sum_eq_weighted_polynomial]
  apply heathBrown_norm_source_weighted_le
    (w := fun h => heathBrownPhase (heathBrownTaylorError k f n h))
    (a := fun h => heathBrownPhase (heathBrownTaylorPolynomial k f n h))
    hH R D hR hpartial
  · exact norm_heathBrownPhase _ |>.le
  · exact hvariation

/-- The fully quantitative source Abel step.  All local differentiability
hypotheses are displayed; the later interval-entry theorem derives them from
the paper's regularity assumption after removing its two endpoint terms. -/
theorem heathBrown_shifted_source_sum_norm_le
    {k H : ℕ} (hk : 2 ≤ k) (hH : 1 ≤ H) {f : ℝ → ℝ}
    {n A lambda R : ℝ}
    (hfat : ContDiffAt ℝ (k - 2 : ℕ) (deriv f) n)
    (hfd : ∀ x ∈ Set.Icc (1 : ℝ) H,
      HasDerivAt f (deriv f (n + x)) (n + x))
    (hfon : ∀ x ∈ Set.Icc (1 : ℝ) H,
      ContDiffOn ℝ (k - 1 : ℕ) (deriv f) (Set.Icc n (n + x)))
    (hderiv : ∀ x ∈ Set.Icc (1 : ℝ) H, ∀ ξ ∈ Set.Ioo n (n + x),
      ‖iteratedDeriv k f ξ‖ ≤ A * lambda)
    (hpartial : ∀ j ∈ Finset.Icc 1 H,
      ‖∑ h ∈ Finset.Icc 1 j,
        heathBrownPhase (heathBrownTaylorPolynomial k f n h)‖ ≤ R)
    (hR : 0 ≤ R) :
    ‖∑ h ∈ Finset.Icc 1 H, heathBrownPhase (f (n + h))‖ ≤
      (1 + (H : ℝ) * (2 * Real.pi * (A * lambda * (H : ℝ) ^ (k - 1)))) * R := by
  apply heathBrown_shifted_source_sum_norm_le_of_variation
    (k := k) (H := H) hH f n R
      ((H : ℝ) * (2 * Real.pi * (A * lambda * (H : ℝ) ^ (k - 1))))
      hR hpartial
  apply sum_norm_heathBrownTaylorError_phase_succ_sub_le
    (k := k) (H := H) (f := f) (n := n)
    (C := A * lambda * (H : ℝ) ^ (k - 1))
  · have hOne : (1 : ℝ) ∈ Set.Icc (1 : ℝ) H := by
      exact ⟨le_rfl, by exact_mod_cast hH⟩
    have hAlambda : 0 ≤ A * lambda :=
      (norm_nonneg (iteratedDeriv k f (n + 1 / 2))).trans
        (hderiv 1 hOne (n + 1 / 2) (by constructor <;> linarith))
    positivity
  · intro j hj
    have hjmem := Finset.mem_Ico.mp hj
    have hjone : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjmem.1
    have hjsucc : j + 1 ≤ H := Nat.succ_le_iff.mpr hjmem.2
    have hjsuccR : (j : ℝ) + 1 ≤ (H : ℝ) := by exact_mod_cast hjsucc
    apply norm_heathBrownTaylorError_phase_succ_sub_le j
    · intro x hx
      have hxSource : x ∈ Set.Icc (1 : ℝ) H := by
        exact ⟨hjone.trans hx.1, hx.2.trans hjsuccR⟩
      have ht := hasDerivAt_heathBrownTaylorError hk (hfd x hxSource)
      rw [ht.deriv]
      exact ht
    · intro x hx
      have hxSource : x ∈ Set.Icc (1 : ℝ) H := by
        exact ⟨hjone.trans hx.1, hx.2.le.trans hjsuccR⟩
      apply norm_deriv_heathBrownTaylorError_le_scale hk
      · exact lt_of_lt_of_le zero_lt_one hxSource.1
      · exact hxSource.2
      · exact hfd x hxSource
      · exact hfat
      · exact hfon x hxSource
      · intro ξ hξ
        exact hderiv x hxSource ξ hξ

/-- Pointwise variation bound on a genuine source edge.  This is separated
from the uniform-maximum form so the subsequent proof can retain each
polynomial partial sum individually. -/
theorem norm_heathBrownTaylorError_weight_succ_sub_le_source
    {k H : ℕ} (hk : 2 ≤ k) {f : ℝ → ℝ}
    {n A lambda : ℝ}
    (hfat : ContDiffAt ℝ (k - 2 : ℕ) (deriv f) n)
    (hfd : ∀ x ∈ Set.Icc (1 : ℝ) H,
      HasDerivAt f (deriv f (n + x)) (n + x))
    (hfon : ∀ x ∈ Set.Icc (1 : ℝ) H,
      ContDiffOn ℝ (k - 1 : ℕ) (deriv f) (Set.Icc n (n + x)))
    (hderiv : ∀ x ∈ Set.Icc (1 : ℝ) H, ∀ ξ ∈ Set.Ioo n (n + x),
      ‖iteratedDeriv k f ξ‖ ≤ A * lambda)
    {j : ℕ} (hj : j ∈ Finset.Ico 1 H) :
    ‖heathBrownPhase (heathBrownTaylorError k f n ((j + 1 : ℕ) : ℝ)) -
        heathBrownPhase (heathBrownTaylorError k f n j)‖ ≤
      2 * Real.pi * (A * lambda * (H : ℝ) ^ (k - 1)) := by
  have hjmem := Finset.mem_Ico.mp hj
  have hjone : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjmem.1
  have hjsucc : j + 1 ≤ H := Nat.succ_le_iff.mpr hjmem.2
  have hjsuccR : (j : ℝ) + 1 ≤ (H : ℝ) := by exact_mod_cast hjsucc
  apply norm_heathBrownTaylorError_phase_succ_sub_le j
  · intro x hx
    have hxSource : x ∈ Set.Icc (1 : ℝ) H := by
      exact ⟨hjone.trans hx.1, hx.2.trans hjsuccR⟩
    have ht := hasDerivAt_heathBrownTaylorError hk (hfd x hxSource)
    rw [ht.deriv]
    exact ht
  · intro x hx
    have hxSource : x ∈ Set.Icc (1 : ℝ) H := by
      exact ⟨hjone.trans hx.1, hx.2.le.trans hjsuccR⟩
    apply norm_deriv_heathBrownTaylorError_le_scale hk
    · exact lt_of_lt_of_le zero_lt_one hxSource.1
    · exact hxSource.2
    · exact hfd x hxSource
    · exact hfat
    · exact hfon x hxSource
    · intro ξ hξ
      exact hderiv x hxSource ξ hξ

/-- Exact partial-sum form of the first Abel transfer in Heath-Brown Lemma 1.
Unlike the convenient uniform-`R` corollary above, this form preserves every
partial sum and hence introduces no spurious factor `H`. -/
theorem heathBrown_shifted_source_sum_norm_le_partial
    {k H : ℕ} (hk : 2 ≤ k) (hH : 1 ≤ H) {f : ℝ → ℝ}
    {n A lambda : ℝ}
    (hfat : ContDiffAt ℝ (k - 2 : ℕ) (deriv f) n)
    (hfd : ∀ x ∈ Set.Icc (1 : ℝ) H,
      HasDerivAt f (deriv f (n + x)) (n + x))
    (hfon : ∀ x ∈ Set.Icc (1 : ℝ) H,
      ContDiffOn ℝ (k - 1 : ℕ) (deriv f) (Set.Icc n (n + x)))
    (hderiv : ∀ x ∈ Set.Icc (1 : ℝ) H, ∀ ξ ∈ Set.Ioo n (n + x),
      ‖iteratedDeriv k f ξ‖ ≤ A * lambda) :
    ‖∑ h ∈ Finset.Icc 1 H, heathBrownPhase (f (n + h))‖ ≤
      ‖heathBrownTaylorPolynomialSum k H f n‖ +
        (2 * Real.pi * (A * lambda * (H : ℝ) ^ (k - 1))) *
          ∑ j ∈ Finset.Ico 1 H,
            ‖heathBrownTaylorPolynomialSum k j f n‖ := by
  rw [heathBrown_shifted_source_sum_eq_weighted_polynomial]
  simpa only [heathBrownTaylorPolynomialSum] using
    (heathBrown_norm_source_weighted_le_partial
      (fun h => heathBrownPhase (heathBrownTaylorError k f n h))
      (fun h => heathBrownPhase (heathBrownTaylorPolynomial k f n h)) hH
      (2 * Real.pi * (A * lambda * (H : ℝ) ^ (k - 1)))
      (by exact norm_heathBrownPhase _ |>.le)
      (by
        intro j hj
        exact norm_heathBrownTaylorError_weight_succ_sub_le_source
          hk hfat hfd hfon hderiv hj))

#print axioms heathBrownPhase_taylorError_mul_polynomial
#print axioms heathBrown_shifted_source_sum_eq_weighted_polynomial
#print axioms heathBrown_shifted_source_sum_norm_le_of_variation
#print axioms heathBrown_shifted_source_sum_norm_le
#print axioms norm_heathBrownTaylorError_weight_succ_sub_le_source
#print axioms heathBrown_shifted_source_sum_norm_le_partial

end

end GafniTao
