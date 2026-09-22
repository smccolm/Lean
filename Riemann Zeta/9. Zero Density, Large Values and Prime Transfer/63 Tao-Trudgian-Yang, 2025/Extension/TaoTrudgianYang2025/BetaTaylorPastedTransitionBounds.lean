import TaoTrudgianYang2025.BetaTaylorPastedExtension
import TaoTrudgianYang2025.BetaTaylorPolynomialBudget

/-!
# Both closed transition bands of the actual pasted extension

Boundary points stay in the transition estimates. Each local formula
uses the genuine Taylor remainder, so no negative power of the width
appears in the final derivative bound.
-/

noncomputable section

open Set
open scoped BigOperators ContDiff

namespace TaoTrudgianYang2025

theorem taylorPastedExtension_left_transition_bound (Q : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (f : ℝ → ℝ) (l r h x M : ℝ),
      0 < h → h ≤ 1 → l+4*h < r →
      (∀ y ∈ Ioo l r, ContDiffAt ℝ ∞ f y) →
      (∀ y ∈ Ioo l r, ∀ j ≤ Q+1, |iteratedDeriv j f y| ≤ M) →
      x ∈ Icc (l+h) (l+2*h) → ∀ n ≤ Q,
        |iteratedDeriv n (taylorPastedExtension f Q l r h) x| ≤ C*M := by
  obtain ⟨B,hB,htr⟩ := smoothTransition_taylor_remainder_uniform_jets Q
  refine ⟨(Q+1 : ℕ)+B,by linarith [Nat.cast_nonneg (α := ℝ) (Q+1)],?_⟩
  intro f l r h x M hh hh₁ hgap hf hb hx n hn
  have ha : l+2*h ∈ Ioo l r := by constructor <;> linarith
  have hxI : x ∈ Ioo l r := by constructor <;> linarith [hx.1,hx.2]
  have hdist : |x-(l+2*h)| ≤ h := by
    rw [abs_le]
    constructor <;> linarith [hx.1,hx.2]
  have hseg : uIcc (l+2*h) x ⊆ Ioo l r := by
    intro y hy
    exact ⟨(lt_min ha.1 hxI.1).trans_le hy.1,hy.2.trans_lt (max_lt ha.2 hxI.2)⟩
  have harg (y : ℝ) : (y-l)/h-1 = 1*y/h+(-l/h-1) := by ring
  have hrem : |iteratedDeriv n (fun y => taylorLeftTransition l h y*
      (f y-finiteTaylorPolynomial f Q (l+2*h) y)) x| ≤ B*M := by
    simpa only [taylorLeftTransition,harg] using
      htr f (l+2*h) x h 1 (-l/h-1) M hh hh₁ (by norm_num) hdist
        (fun y hy => hf y (hseg hy))
        (fun y hy => hb y (hseg hy) (Q+1) le_rfl) n hn
  have hpoly : |iteratedDeriv n (finiteTaylorPolynomial f Q (l+2*h)) x| ≤ (Q+1 : ℕ)*M := by
    simpa only [one_pow,mul_one] using abs_iteratedDeriv_finiteTaylorPolynomial_le hn
      (D := 1) le_rfl (hdist.trans hh₁) (fun j hj => hb _ ha j (by omega))
  have hlocal : x < r-2*h := by linarith [hx.1,hx.2]
  have hN : (n : WithTop ℕ∞) ≤ ∞ :=
    ENat.natCast_le_of_coe_top_le_withTop le_rfl n
  have hp : ContDiffAt ℝ ∞ (finiteTaylorPolynomial f Q (l+2*h)) x :=
    (finiteTaylorPolynomial_contDiff f Q (l+2*h)).contDiffAt
  have ht : ContDiffAt ℝ ∞ (taylorLeftTransition l h) x :=
    (Real.smoothTransition.contDiff.comp (by fun_prop)).contDiffAt
  rw [(taylorPastedExtension_eventuallyEq_left_formula f Q hh hlocal).iteratedDeriv_eq n,
    iteratedDeriv_fun_add (hp.of_le hN) ((ht.mul ((hf x hxI).sub hp)).of_le hN)]
  exact (abs_add_le _ _).trans ((add_le_add hpoly hrem).trans_eq (by ring))

theorem taylorPastedExtension_right_transition_bound (Q : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (f : ℝ → ℝ) (l r h x M : ℝ),
      0 < h → h ≤ 1 → l+4*h < r →
      (∀ y ∈ Ioo l r, ContDiffAt ℝ ∞ f y) →
      (∀ y ∈ Ioo l r, ∀ j ≤ Q+1, |iteratedDeriv j f y| ≤ M) →
      x ∈ Icc (r-2*h) (r-h) → ∀ n ≤ Q,
        |iteratedDeriv n (taylorPastedExtension f Q l r h) x| ≤ C*M := by
  obtain ⟨B,hB,htr⟩ := smoothTransition_taylor_remainder_uniform_jets Q
  refine ⟨(Q+1 : ℕ)+B,by linarith [Nat.cast_nonneg (α := ℝ) (Q+1)],?_⟩
  intro f l r h x M hh hh₁ hgap hf hb hx n hn
  have ha : r-2*h ∈ Ioo l r := by constructor <;> linarith
  have hxI : x ∈ Ioo l r := by constructor <;> linarith [hx.1,hx.2]
  have hdist : |x-(r-2*h)| ≤ h := by
    rw [abs_le]
    constructor <;> linarith [hx.1,hx.2]
  have hseg : uIcc (r-2*h) x ⊆ Ioo l r := by
    intro y hy
    exact ⟨(lt_min ha.1 hxI.1).trans_le hy.1,hy.2.trans_lt (max_lt ha.2 hxI.2)⟩
  have harg (y : ℝ) : (r-y)/h-1 = (-1)*y/h+(r/h-1) := by ring
  have hrem : |iteratedDeriv n (fun y => taylorRightTransition r h y*
      (f y-finiteTaylorPolynomial f Q (r-2*h) y)) x| ≤ B*M := by
    simpa only [taylorRightTransition,harg] using
      htr f (r-2*h) x h (-1) (r/h-1) M hh hh₁ (by norm_num) hdist
        (fun y hy => hf y (hseg hy))
        (fun y hy => hb y (hseg hy) (Q+1) le_rfl) n hn
  have hpoly : |iteratedDeriv n (finiteTaylorPolynomial f Q (r-2*h)) x| ≤ (Q+1 : ℕ)*M := by
    simpa only [one_pow,mul_one] using abs_iteratedDeriv_finiteTaylorPolynomial_le hn
      (D := 1) le_rfl (hdist.trans hh₁) (fun j hj => hb _ ha j (by omega))
  have hlocal : l+2*h < x := by linarith [hx.1,hx.2]
  have hN : (n : WithTop ℕ∞) ≤ ∞ :=
    ENat.natCast_le_of_coe_top_le_withTop le_rfl n
  have hp : ContDiffAt ℝ ∞ (finiteTaylorPolynomial f Q (r-2*h)) x :=
    (finiteTaylorPolynomial_contDiff f Q (r-2*h)).contDiffAt
  have ht : ContDiffAt ℝ ∞ (taylorRightTransition r h) x :=
    (Real.smoothTransition.contDiff.comp (by fun_prop)).contDiffAt
  rw [(taylorPastedExtension_eventuallyEq_right_formula f Q hh hlocal).iteratedDeriv_eq n,
    iteratedDeriv_fun_add (hp.of_le hN) ((ht.mul ((hf x hxI).sub hp)).of_le hN)]
  exact (abs_add_le _ _).trans ((add_le_add hpoly hrem).trans_eq (by ring))

end TaoTrudgianYang2025
