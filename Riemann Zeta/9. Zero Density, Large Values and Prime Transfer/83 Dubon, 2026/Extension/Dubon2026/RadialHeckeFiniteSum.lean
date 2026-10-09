import Dubon2026.FinitePlaceHeckeRadialCosets

/-! # Exact p-forward and one-backward count in the original Hecke transversal -/

namespace Dubon2026

noncomputable section

/-- The actual finite sum with one distinguished value retains its exact original cardinality. -/
theorem finite_sum_one_exception {ι : Type*} [Fintype ι]
    (F : ι → ℂ) (j : ι) (a b : ℂ) (hj : F j = a) (hother : ∀ i, i ≠ j → F i = b) :
    ∑ i, F i = a + ((Fintype.card ι : ℂ) - 1) * b := by
  classical
  have he (i : ι) : F i = b + if i = j then a - b else 0 := by
    by_cases h : i = j
    · subst i
      simp only [hj, ↓reduceIte]
      ring
    · simp [h, hother i h]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  ring

/-- The original Option(ZMod p) Hecke transversal has exactly one backward term and p forward terms. -/
theorem hecke_option_sum_one_backward (p : ℕ) [NeZero p] (F : Option (ZMod p) → ℂ)
    (a b : ℂ) (hzero : F (some 0) = a) (hnone : F none = b)
    (hsome : ∀ x : ZMod p, x ≠ 0 → F (some x) = b) :
    ∑ i, F i = a + (p : ℂ) * b := by
  have he := finite_sum_one_exception F (some 0) a b hzero (by
    intro i hi
    cases i with
    | none => exact hnone
    | some x => exact hsome x (by simpa using hi))
  simpa only [Fintype.card_option, ZMod.card, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using he

end
end Dubon2026
