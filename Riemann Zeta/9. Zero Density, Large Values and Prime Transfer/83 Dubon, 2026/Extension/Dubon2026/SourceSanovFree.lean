import Dubon2026.SourceSanovWords
import Mathlib.GroupTheory.FreeGroup.Reduce

/-! Actual free integral matrix words for the required congruence subgroup.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> surjective native H1 coefficient map -> Gamma0 H2 vanishing
after inverting six -> a free subgroup of index dividing 48.

Adapted from anthropics/fermats-last-theorem, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_TW12CD1Dock_subsingleton_H2_gamma0.lean.txt (Apache-2.0;
retained LICENSE and NOTICE). All matrix words use the actual integral
generators; no abstract freeness or faithfulness hypothesis is supplied.
-/

namespace Dubon2026
noncomputable section
open Matrix
open scoped MatrixGroups

/-- A reduced original free-group word has alternating nonzero syllables with the correct initial sign. -/
theorem sourceSanovSyllables_reduced : ∀ L : List (Fin 2 × Bool), FreeGroup.IsReduced L →
    List.IsChain (fun a b => a.1 ≠ b.1) (sourceSanovSyllables L) ∧
    (∀ x ∈ sourceSanovSyllables L, x.2 ≠ 0) ∧
    (∀ g b L', L = (g, b) :: L' →
      ∃ n t, sourceSanovSyllables L = (g, n) :: t ∧ (if b then 0 < n else n < 0)) := by
  intro L
  induction L with
  | nil =>
    intro _
    refine ⟨List.isChain_nil, by simp [sourceSanovSyllables], ?_⟩
    intro g b L' h
    exact absurd h (List.cons_ne_nil _ _).symm
  | cons hd tl ih =>
    intro hred
    obtain ⟨g, b⟩ := hd
    cases tl with
    | nil =>
      refine ⟨?_, ?_, ?_⟩
      · show List.IsChain _ [(g, sourceSanovSign b)]
        exact List.isChain_singleton _
      · intro x hx
        simp only [show sourceSanovSyllables [(g, b)] = [(g, sourceSanovSign b)] from rfl, List.mem_singleton] at hx
        subst hx
        cases b <;> simp [sourceSanovSign]
      · intro g₀ b₀ L' h
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ : (g₀ = g ∧ b₀ = b) ∧ L' = [] := by
          simpa using h.symm
        refine ⟨sourceSanovSign b₀, [], rfl, ?_⟩
        cases b₀ <;> simp [sourceSanovSign]
    | cons hd₂ tl₂ =>
      obtain ⟨g₂, b₂⟩ := hd₂
      have hadj : g = g₂ → b = b₂ := (FreeGroup.isReduced_cons_cons.mp hred).1
      have hred₂ : FreeGroup.IsReduced ((g₂, b₂) :: tl₂) :=
        (FreeGroup.isReduced_cons_cons.mp hred).2
      obtain ⟨ihchain, ihexp, ihhead⟩ := ih hred₂
      obtain ⟨n₂, t₂, hsyl₂, hsgn₂⟩ := ihhead g₂ b₂ tl₂ rfl
      have hunf : sourceSanovSyllables ((g, b) :: (g₂, b₂) :: tl₂)
          = if g = g₂ then (g₂, n₂ + sourceSanovSign b) :: t₂
            else (g, sourceSanovSign b) :: (g₂, n₂) :: t₂ := by
        unfold sourceSanovSyllables
        rw [hsyl₂]
      by_cases hg : g = g₂
      ·
        have hb : b = b₂ := hadj hg
        subst hb
        rw [hunf, if_pos hg]
        have hn : if b then 0 < n₂ + sourceSanovSign b else n₂ + sourceSanovSign b < 0 := by
          cases b <;> simp [sourceSanovSign] at hsgn₂ ⊢ <;> omega
        refine ⟨?_, ?_, ?_⟩
        · rw [hsyl₂] at ihchain
          cases t₂ with
          | nil => exact List.isChain_singleton _
          | cons c t₃ =>
            exact List.isChain_cons_cons.mpr
              ⟨(List.isChain_cons_cons.mp ihchain).1,
               (List.isChain_cons_cons.mp ihchain).2⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx'
          · have : (g₂, n₂ + sourceSanovSign b).2 ≠ 0 := by
              cases b <;> simp [sourceSanovSign] at hn ⊢ <;> omega
            exact this
          · exact ihexp x (by rw [hsyl₂]; exact List.mem_cons_of_mem _ hx')
        · intro g₀ b₀ L' h
          obtain ⟨⟨rfl, rfl⟩, -⟩ : (g₀ = g ∧ b₀ = b) ∧ L' = (g₂, b) :: tl₂ := by
            simpa using h.symm
          refine ⟨n₂ + sourceSanovSign b₀, t₂, ?_, hn⟩
          rw [← hg]
      ·
        rw [hunf, if_neg hg]
        refine ⟨?_, ?_, ?_⟩
        · rw [hsyl₂] at ihchain
          exact List.isChain_cons_cons.mpr ⟨hg, ihchain⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx'
          · cases b <;> simp [sourceSanovSign]
          · exact ihexp x (by rw [hsyl₂]; exact hx')
        · intro g₀ b₀ L' h
          obtain ⟨⟨rfl, rfl⟩, -⟩ : (g₀ = g ∧ b₀ = b) ∧ L' = (g₂, b₂) :: tl₂ := by
            simpa using h.symm
          refine ⟨sourceSanovSign b₀, (g₂, n₂) :: t₂, ?_, ?_⟩
          · rfl
          · cases b₀ <;> simp [sourceSanovSign]

/-- The original two integral unipotent matrices generate a faithfully embedded rank-two free group. -/
theorem sourceSanov_lift_injective :
    Function.Injective (FreeGroup.lift ![sourceSanovA, sourceSanovB] : FreeGroup (Fin 2) →* SL(2, ℤ)) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  by_contra hne
  have hnil : w.toWord ≠ [] := fun h => hne (FreeGroup.toWord_eq_nil_iff.mp h)
  obtain ⟨hchain, hexp, -⟩ := sourceSanovSyllables_reduced w.toWord FreeGroup.isReduced_toWord
  have hprod : FreeGroup.lift ![sourceSanovA, sourceSanovB] w = sourceSanovSyllableProduct (sourceSanovSyllables w.toWord) := by
    conv_lhs => rw [← FreeGroup.mk_toWord (x := w)]
    rw [FreeGroup.lift_mk, sourceSanovSyllables_product]
  exact sourceSanovSyllableProduct_ne_one _ (fun h => hnil (sourceSanovSyllables_eq_nil_iff.mp h)) hchain hexp
    (hprod ▸ hw)

/-- The literal subgroup generated by the original two integral matrices is a free group. -/
theorem sourceSanov_range_free :
    IsFreeGroup ↥(FreeGroup.lift ![sourceSanovA, sourceSanovB] : FreeGroup (Fin 2) →* SL(2, ℤ)).range := by
  have e : FreeGroup (Fin 2) ≃* (FreeGroup.lift ![sourceSanovA, sourceSanovB] :
      FreeGroup (Fin 2) →* SL(2, ℤ)).range := MonoidHom.ofInjective sourceSanov_lift_injective
  exact (FreeGroupBasis.ofFreeGroup (Fin 2)).map e |>.isFreeGroup


end
end Dubon2026
