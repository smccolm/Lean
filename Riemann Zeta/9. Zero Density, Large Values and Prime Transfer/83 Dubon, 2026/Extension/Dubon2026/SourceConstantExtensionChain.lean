import Dubon2026.SourceConstantExtensionIntegralAlgebra

/-! DUB-17/18 -> rational Fourier spanning -> Fricke integral base change.
Finite lists of actual complex constants reduce the complex coefficient field
to successive simple extensions. Only the inclusions used by the integral
span induction and finite coefficient capture are retained.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_WLight_frickeFunction_intBaseChange, finite constant chain. -/
namespace Dubon2026.SourceFricke.ConstantDescent
noncomputable section

/-- The original constant field with a finite list of complex constants adjoined. -/
def constantChain (F : IntermediateField ℚ ℂ) : List ℂ → IntermediateField ℚ ℂ
  | [] => F
  | c :: l => (IntermediateField.adjoin (constantChain F l) {c}).restrictScalars ℚ

theorem constantChain_le_cons (F : IntermediateField ℚ ℂ) (c : ℂ) (l : List ℂ) :
    constantChain F l ≤ constantChain F (c :: l) := fun x hx =>
  IntermediateField.algebraMap_mem (IntermediateField.adjoin (constantChain F l) {c})
    (⟨x, hx⟩ : constantChain F l)

theorem le_constantChain (F : IntermediateField ℚ ℂ) : ∀ l : List ℂ, F ≤ constantChain F l
  | [] => le_rfl
  | c :: l => (le_constantChain F l).trans (constantChain_le_cons F c l)

theorem mem_constantChain_of_mem (F : IntermediateField ℚ ℂ) :
    ∀ {l : List ℂ} {c : ℂ}, c ∈ l → c ∈ constantChain F l
  | d :: l, c, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact IntermediateField.mem_adjoin_simple_self (constantChain F l) c
    · exact constantChain_le_cons F d l (mem_constantChain_of_mem F h)

theorem constantChain_le (F : IntermediateField ℚ ℂ) {M : IntermediateField ℚ ℂ}
    (hFM : F ≤ M) : ∀ {l : List ℂ}, (∀ c ∈ l, c ∈ M) → constantChain F l ≤ M
  | [], _ => hFM
  | c :: l, h => by
    intro x hx
    have ih : constantChain F l ≤ M := constantChain_le F hFM fun d hd =>
      h d (List.mem_cons_of_mem c hd)
    change x ∈ IntermediateField.adjoin (constantChain F l) {c} at hx
    rw [← IntermediateField.mem_toSubfield, IntermediateField.adjoin_toSubfield] at hx
    refine Subfield.closure_le (t := M.toSubfield) |>.mpr ?_ hx
    rintro y (⟨z, rfl⟩ | hy)
    · exact ih z.property
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact h _ List.mem_cons_self

theorem constantChain_le_append_left (F : IntermediateField ℚ ℂ) (l₁ l₂ : List ℂ) :
    constantChain F l₁ ≤ constantChain F (l₁ ++ l₂) :=
  constantChain_le F (le_constantChain F _) fun _ hc =>
    mem_constantChain_of_mem F (List.mem_append_left l₂ hc)

theorem constantChain_le_append_right (F : IntermediateField ℚ ℂ) (l₁ l₂ : List ℂ) :
    constantChain F l₂ ≤ constantChain F (l₁ ++ l₂) :=
  constantChain_le F (le_constantChain F _) fun _ hc =>
    mem_constantChain_of_mem F (List.mem_append_right l₁ hc)

end
end Dubon2026.SourceFricke.ConstantDescent