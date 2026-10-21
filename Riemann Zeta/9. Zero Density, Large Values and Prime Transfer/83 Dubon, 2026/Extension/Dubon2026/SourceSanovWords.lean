import Dubon2026.SourceSanovSyllables

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

/-- The integral exponent of an original free-group letter. -/
def sourceSanovSign (b : Bool) : ℤ := if b then 1 else -1

/-- Group consecutive letters with the same generator into actual integral matrix powers. -/
def sourceSanovSyllables : List (Fin 2 × Bool) → List (Fin 2 × ℤ)
  | [] => []
  | (g, b) :: L =>
    match sourceSanovSyllables L with
    | [] => [(g, sourceSanovSign b)]
    | (g', n) :: t => if g = g' then (g', n + sourceSanovSign b) :: t else (g, sourceSanovSign b) :: (g', n) :: t

/-- The original word has no syllables exactly when it has no letters. -/
theorem sourceSanovSyllables_eq_nil_iff {L : List (Fin 2 × Bool)} : sourceSanovSyllables L = [] ↔ L = [] := by
  constructor
  · intro h
    cases L with
    | nil => rfl
    | cons hd tl =>
      obtain ⟨g, b⟩ := hd
      unfold sourceSanovSyllables at h
      split at h
      · simp_all
      · split at h <;> simp_all
  · rintro rfl; rfl

/-- Grouping the original free-group letters preserves their actual integer matrix product. -/
theorem sourceSanovSyllables_product : ∀ L : List (Fin 2 × Bool),
    sourceSanovSyllableProduct (sourceSanovSyllables L)
      = (L.map fun x => cond x.2 (![sourceSanovA, sourceSanovB] x.1) (![sourceSanovA, sourceSanovB] x.1)⁻¹).prod := by
  intro L
  induction L with
  | nil => simp [sourceSanovSyllables, sourceSanovSyllableProduct]
  | cons hd tl ih =>
    obtain ⟨g, b⟩ := hd
    show sourceSanovSyllableProduct (sourceSanovSyllables ((g, b) :: tl)) = _
    unfold sourceSanovSyllables
    cases htl : sourceSanovSyllables tl with
    | nil =>
      rw [sourceSanovSyllables_eq_nil_iff.mp htl] at ih ⊢
      simp only [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one] at ih ⊢
      rw [show sourceSanovSyllableProduct [(g, sourceSanovSign b)] = (![sourceSanovA, sourceSanovB] g) ^ sourceSanovSign b from by simp [sourceSanovSyllableProduct]]
      cases b <;> simp [sourceSanovSign]
    | cons p t =>
      obtain ⟨g', n⟩ := p
      rw [htl] at ih
      by_cases hg : g = g'
      · subst hg
        simp only [if_true]
        have hL : sourceSanovSyllableProduct ((g, n + sourceSanovSign b) :: t)
            = (![sourceSanovA, sourceSanovB] g) ^ (sourceSanovSign b) * sourceSanovSyllableProduct ((g, n) :: t) := by
          simp only [sourceSanovSyllableProduct, List.map_cons, List.prod_cons]
          rw [← mul_assoc, ← zpow_add, add_comm n (sourceSanovSign b)]
        rw [hL, ih, List.map_cons, List.prod_cons]
        cases b <;> simp [sourceSanovSign]
      · simp only [if_neg hg]
        have hL : sourceSanovSyllableProduct ((g, sourceSanovSign b) :: (g', n) :: t)
            = (![sourceSanovA, sourceSanovB] g) ^ (sourceSanovSign b) * sourceSanovSyllableProduct ((g', n) :: t) := by
          simp [sourceSanovSyllableProduct]
        rw [hL, ih, List.map_cons, List.prod_cons]
        cases b <;> simp [sourceSanovSign]


end
end Dubon2026
