import DongWangWangZhang2026.XiLogDerivative
import GuthMaynard.ZeroCount

/-!
# Conjugation of the actual zero multiplicity index

The foundation's proved conjugation of zeta's analytic vanishing order
is transported through the xi/zeta analytic-unit bridge. The resulting
permutation preserves every multiplicity label and reindexes the
convergent zero kernel needed by the forcing proposition.
-/

namespace DongWangWangZhang2026
noncomputable section
open Complex Complex.Hadamard Set
open RiemannZeta.GuthMaynard

/-- Conjugation preserves xi divisor multiplicity at every actual indexed zero. -/
theorem xi_divisor_conj_point (p : XiZero) :
    MeromorphicOn.divisor riemannXi univ (star (xiZeroPoint p)) =
      MeromorphicOn.divisor riemannXi univ (xiZeroPoint p) := by
  have hr := xiZeroPoint_re p
  have hn : xiZeroPoint p ≠ 1 := by
    intro h
    simp [h] at hr
  have hcn : star (xiZeroPoint p) ≠ 1 := by
    intro h
    have h' := congrArg star h
    apply hn
    simpa using h'
  have hcr : 0 < (star (xiZeroPoint p)).re := by simpa using hr.1
  simp only [divisor_univ_eq_analyticOrderNatAt_int differentiable_riemannXi]
  congr 1
  simp only [analyticOrderNatAt, xi_analyticOrder_eq_zeta hcr hcn,
    xi_analyticOrder_eq_zeta hr.1 hn]
  exact analyticVanishingOrder_conj (xiZeroPoint p) hn

/-- The genuine conjugation map retains the finite multiplicity label. -/
def xiZeroConj (p : XiZero) : XiZero :=
  ⟨⟨star (xiZeroPoint p), ⟨p.1.2.val, by
      simpa only [xi_divisor_conj_point] using p.1.2.isLt⟩⟩, by
    simp [divisorZeroIndex₀_val_ne_zero p]⟩

/-- Conjugation acts on the actual underlying zero. -/
theorem xiZeroPoint_conj (p : XiZero) :
    xiZeroPoint (xiZeroConj p) = star (xiZeroPoint p) := rfl

/-- Double conjugation preserves the zero and its multiplicity label. -/
theorem xiZeroConj_involutive : Function.Involutive xiZeroConj := by
  intro p
  apply Subtype.ext
  apply Sigma.ext
  · change star (star (xiZeroPoint p)) = xiZeroPoint p
    exact star_star _
  · refine (Fin.heq_ext_iff
      (i := (xiZeroConj (xiZeroConj p)).1.2) (j := p.1.2) ?_).2 ?_
    · change (MeromorphicOn.divisor riemannXi univ (star (star (xiZeroPoint p)))).toNat =
        (MeromorphicOn.divisor riemannXi univ (xiZeroPoint p)).toNat
      rw [star_star]
    · rfl

/-- The full multiplicity-index permutation used in both-sign zero sums. -/
def xiZeroConjEquiv : XiZero ≃ XiZero :=
  Function.Involutive.toPerm xiZeroConj xiZeroConj_involutive

/-- Conjugation reindexes the actual inverse-square kernel without changing its value. -/
theorem tsum_xiZero_kernel_conj (s : ℂ) (a : ℝ) :
    (∑' p : XiZero, a / ‖star s - xiZeroPoint p‖ ^ 2) =
      ∑' p : XiZero, a / ‖s - xiZeroPoint p‖ ^ 2 := by
  have h := xiZeroConjEquiv.tsum_eq (fun p => a / ‖star s - xiZeroPoint p‖ ^ 2)
  change (∑' p : XiZero, a / ‖star s - xiZeroPoint (xiZeroConj p)‖ ^ 2) =
    ∑' p : XiZero, a / ‖star s - xiZeroPoint p‖ ^ 2 at h
  simpa only [xiZeroPoint_conj, ← star_sub, norm_star] using h.symm

/-- The weighted kernel at positive and negative source heights is the same convergent sum. -/
theorem source_zero_kernel_neg_height {a : ℝ} (ha : 0 < a) (v : ℝ) :
    Summable (fun p : XiZero =>
      a / ‖(((1 + a : ℝ) : ℂ) + (v : ℂ) * I) - xiZeroPoint p‖ ^ 2) ∧
    (∑' p : XiZero,
      a / ‖(((1 + a : ℝ) : ℂ) + ((-v : ℝ) : ℂ) * I) - xiZeroPoint p‖ ^ 2) =
      ∑' p : XiZero,
        a / ‖(((1 + a : ℝ) : ℂ) + (v : ℂ) * I) - xiZeroPoint p‖ ^ 2 := by
  have hs : 1 < (((1 + a : ℝ) : ℂ) + (v : ℂ) * I).re := by simp; linarith
  refine ⟨?_, ?_⟩
  · simpa only [mul_one_div] using (summable_xiZero_inverse_square hs).mul_left a
  · simpa [Complex.star_def] using
      tsum_xiZero_kernel_conj (((1 + a : ℝ) : ℂ) + (v : ℂ) * I) a

end
end DongWangWangZhang2026
