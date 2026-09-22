import TaoTrudgianYang2025.BetaTaylorPastedTransitionBounds

/-!
# Uniform finite jets of the constructed global Taylor extension

The five-region proof keeps every transition boundary. The constant is
chosen before the moving interval, width and original function. Only the
fixed observation distance D and requested finite order Q affect it.
-/

noncomputable section

open Set
open scoped BigOperators ContDiff

namespace TaoTrudgianYang2025

theorem taylorPastedExtension_uniform_jets
    (Q : ℕ) {D : ℝ} (hD : 1 ≤ D) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (f : ℝ → ℝ) (l r h x M : ℝ),
      0 < h → h ≤ 1 → l+4*h < r →
      (∀ y ∈ Ioo l r, ContDiffAt ℝ ∞ f y) →
      (∀ y ∈ Ioo l r, ∀ j ≤ Q+1, |iteratedDeriv j f y| ≤ M) →
      |x-(l+2*h)| ≤ D → |x-(r-2*h)| ≤ D → ∀ n ≤ Q,
        |iteratedDeriv n (taylorPastedExtension f Q l r h) x| ≤ C*M := by
  obtain ⟨L,hL,hleft⟩ := taylorPastedExtension_left_transition_bound Q
  obtain ⟨R,hR,hright⟩ := taylorPastedExtension_right_transition_bound Q
  let G : ℝ := (Q+1 : ℕ)*D^Q
  have hG : 0 ≤ G := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (zero_le_one.trans hD) Q)
  let C := 1+G+L+R
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hGC : G ≤ C := by dsimp [C]; linarith
  have hLC : L ≤ C := by dsimp [C]; linarith
  have hRC : R ≤ C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro f l r h x M hh hh₁ hgap hf hb hdistL hdistR n hn
  have ha : l+2*h ∈ Ioo l r := by constructor <;> linarith
  have haR : r-2*h ∈ Ioo l r := by constructor <;> linarith
  have hM : 0 ≤ M := (abs_nonneg _).trans (hb _ ha 0 (Nat.zero_le _))
  by_cases hx₀ : x < l+h
  · rw [(taylorPastedExtension_eventuallyEq_left_polynomial f Q hh hgap hx₀).iteratedDeriv_eq n]
    exact (abs_iteratedDeriv_finiteTaylorPolynomial_le hn hD hdistL
      (fun j hj => hb _ ha j (by omega))).trans (mul_le_mul_of_nonneg_right hGC hM)
  · have hx₀' : l+h ≤ x := le_of_not_gt hx₀
    by_cases hx₁ : x ≤ l+2*h
    · exact (hleft f l r h x M hh hh₁ hgap hf hb ⟨hx₀',hx₁⟩ n hn).trans
        (mul_le_mul_of_nonneg_right hLC hM)
    · have hx₁' : l+2*h < x := lt_of_not_ge hx₁
      by_cases hx₂ : x < r-2*h
      · rw [(taylorPastedExtension_eventuallyEq_plateau f Q hh ⟨hx₁',hx₂⟩).iteratedDeriv_eq n]
        exact (hb x ⟨by linarith,by linarith⟩ n (by omega)).trans
          (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hC hM)
      · have hx₂' : r-2*h ≤ x := le_of_not_gt hx₂
        by_cases hx₃ : x ≤ r-h
        · exact (hright f l r h x M hh hh₁ hgap hf hb ⟨hx₂',hx₃⟩ n hn).trans
            (mul_le_mul_of_nonneg_right hRC hM)
        · have hx₃' : r-h < x := lt_of_not_ge hx₃
          rw [(taylorPastedExtension_eventuallyEq_right_polynomial f Q hh hgap hx₃').iteratedDeriv_eq n]
          exact (abs_iteratedDeriv_finiteTaylorPolynomial_le hn hD hdistR
            (fun j hj => hb _ haR j (by omega))).trans (mul_le_mul_of_nonneg_right hGC hM)

end TaoTrudgianYang2025
