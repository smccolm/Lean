import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Derivative inequalities across finitely many exceptional points -/

namespace Dubon2026

open Set

theorem image_sub_le_of_derivative_le_off_finset (f f' : ℝ → ℝ) (Z : Finset ℝ) :
    ∀ a b C : ℝ, a ≤ b → ContinuousOn f (Icc a b) →
      (∀ x ∈ Ioo a b, x ∉ Z → HasDerivAt f (f' x) x ∧ f' x ≤ C) →
        f b - f a ≤ C * (b - a) := by
  classical
  induction Z using Finset.induction_on with
  | empty =>
    intro a b C hab hc hd
    rcases hab.eq_or_lt with he | hlt
    · simp [he]
    obtain ⟨x, hx, he⟩ := exists_hasDerivAt_eq_slope f f' hlt hc
      (fun x hx => (hd x hx (by simp)).1)
    have hb := (hd x hx (by simp)).2
    rw [he] at hb
    exact (div_le_iff₀ (sub_pos.mpr hlt)).mp hb
  | @insert c Z _ ih =>
    intro a b C hab hc hd
    by_cases hcin : c ∈ Ioo a b
    · have hsubL : Icc a c ⊆ Icc a b := Icc_subset_Icc le_rfl hcin.2.le
      have hsubR : Icc c b ⊆ Icc a b := Icc_subset_Icc hcin.1.le le_rfl
      have hL := ih a c C hcin.1.le (hc.mono hsubL) (by
        intro x hx hz
        apply hd x ⟨hx.1, hx.2.trans hcin.2⟩
        simpa only [Finset.mem_insert, not_or] using And.intro hx.2.ne hz)
      have hR := ih c b C hcin.2.le (hc.mono hsubR) (by
        intro x hx hz
        apply hd x ⟨hcin.1.trans hx.1, hx.2⟩
        simpa only [Finset.mem_insert, not_or] using And.intro hx.1.ne' hz)
      nlinarith
    · exact ih a b C hab hc (by
        intro x hx hz
        apply hd x hx
        rw [Finset.mem_insert, not_or]
        refine ⟨?_, hz⟩
        intro he
        exact hcin (he ▸ hx))

theorem mul_sub_le_of_le_derivative_off_finset (f f' : ℝ → ℝ) (Z : Finset ℝ)
    (a b C : ℝ) (hab : a ≤ b) (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, x ∉ Z → HasDerivAt f (f' x) x ∧ C ≤ f' x) :
    C * (b - a) ≤ f b - f a := by
  have hh := image_sub_le_of_derivative_le_off_finset (fun x => -f x) (fun x => -f' x)
    Z a b (-C) hab hc.neg (fun x hx hz =>
      ⟨(hd x hx hz).1.neg, neg_le_neg (hd x hx hz).2⟩)
  linarith

end Dubon2026
