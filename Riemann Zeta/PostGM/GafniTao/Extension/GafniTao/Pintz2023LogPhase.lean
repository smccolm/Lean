import GafniTao.WooleyNative
import RiemannZeta.GuthMaynard.HughesYoungDFIProfile

/-!
# Pintz (2023), Section 3: the logarithmic phase

This file identifies the phase in Pintz's partial zeta sums with the phase
used by Heath-Brown's k-th derivative theorem.  It records the complete
positive-order derivative, including its sign and factorial.  The parity
split below is the one needed to feed a positive k-th derivative to
`HeathBrownKthDerivativeTheorem`; negating a real phase only conjugates its
exponential sum and hence preserves its norm.
-/

open Complex Finset Set
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The real phase whose exponential is `n ^ (-I*t)`. -/
noncomputable def pintz2023LogPhase (t x : ℝ) : ℝ :=
  -t / (2 * Real.pi) * Real.log x

/-- Translating the phase to an interval beginning at the positive integer
`N` preserves smoothness to every finite order on the source interval. -/
theorem pintz2023LogPhase_contDiffOn
    (k : ℕ) {N L : ℕ} (t : ℝ) (hN : 0 < N) :
    ContDiffOn ℝ k (fun x : ℝ => pintz2023LogPhase t (N + x))
      (Set.Icc 0 (L : ℝ)) := by
  have hmap : Set.MapsTo (fun x : ℝ => (N : ℝ) + x)
      (Set.Icc 0 (L : ℝ)) ({0} : Set ℝ)ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
    linarith [hx.1]
  have hshift : ContDiffOn ℝ ⊤ (fun x : ℝ => (N : ℝ) + x)
      (Set.Icc 0 (L : ℝ)) :=
    (contDiff_const.add contDiff_id).contDiffOn
  unfold pintz2023LogPhase
  exact (contDiffOn_const.mul
    (Real.contDiffOn_log.comp hshift hmap)).of_le le_top

/-- Exact k-th derivative of the translated logarithmic phase. -/
theorem iteratedDeriv_pintz2023LogPhase
    {k : ℕ} (hk : 1 ≤ k) {N : ℕ} {t x : ℝ}
    (hNx : 0 < (N : ℝ) + x) :
    iteratedDeriv k (fun y : ℝ => pintz2023LogPhase t (N + y)) x =
      (-t / (2 * Real.pi)) * (-1 : ℝ) ^ (k - 1) *
        (k - 1).factorial * ((N : ℝ) + x) ^ (-(k : ℕ) : ℤ) := by
  cases k with
  | zero => omega
  | succ j =>
  simp only [Nat.add_sub_cancel]
  unfold pintz2023LogPhase
  rw [iteratedDeriv_const_mul_field]
  have hcomp := congrFun
    (iteratedDeriv_comp_const_add
      (n := j + 1) (f := Real.log) (s := (N : ℝ))) x
  rw [hcomp, RiemannZeta.GuthMaynard.iteratedDeriv_real_log_succ j hNx]
  ring

/-- The phase exponent is the usual imaginary complex power. -/
theorem heathBrownPhase_pintz2023LogPhase
    {n : ℕ} (hn : 0 < n) (t : ℝ) :
    heathBrownPhase (pintz2023LogPhase t n) =
      (n : ℂ) ^ (-(t : ℂ) * I) := by
  unfold heathBrownPhase pintz2023LogPhase
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne')]
  have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    exact (Complex.ofReal_log hnReal.le).symm
  rw [hlog]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

/-- Negating a real phase conjugates every term of its exponential sum. -/
theorem heathBrownExponentialSum_neg
    (N : ℕ) (f : ℝ → ℝ) :
    heathBrownExponentialSum N (fun x => -f x) =
      star (heathBrownExponentialSum N f) := by
  unfold heathBrownExponentialSum
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro n hn
  unfold heathBrownPhase
  change Complex.exp _ = (starRingEnd ℂ) (Complex.exp _)
  rw [← Complex.exp_conj]
  congr 1
  apply Complex.ext <;> simp

/-- Consequently the k-th derivative theorem can be applied after the
parity-forced sign change without altering the norm of the desired sum. -/
theorem norm_heathBrownExponentialSum_neg
    (N : ℕ) (f : ℝ → ℝ) :
    ‖heathBrownExponentialSum N (fun x => -f x)‖ =
      ‖heathBrownExponentialSum N f‖ := by
  rw [heathBrownExponentialSum_neg, norm_star]

#print axioms pintz2023LogPhase_contDiffOn
#print axioms iteratedDeriv_pintz2023LogPhase
#print axioms heathBrownPhase_pintz2023LogPhase
#print axioms norm_heathBrownExponentialSum_neg

end

end GafniTao
