import Dubon2026.SourceSanovMatrices

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

/-- The actual product of alternating powers of the original integral unipotent matrices. -/
def sourceSanovSyllableProduct (L : List (Fin 2 × ℤ)) : SL(2, ℤ) :=
  (L.map fun p => (![sourceSanovA, sourceSanovB] p.1) ^ p.2).prod

/-- The coordinate vector used to detect nontriviality of the original matrix word. -/
def sourceSanovSeed (g : Fin 2) : Fin 2 → ℤ := fun i => if i = g then 0 else 1

/-- The strict coordinate growth property of the actual integer matrix word. -/
def sourceSanovGrowth (g : Fin 2) (u : Fin 2 → ℤ) : Prop := |u (g + 1)| < |u g| ∧ 1 < |u g|

/-- Every nonempty reduced alternating matrix word strictly increases its indicated coordinate. -/
theorem sourceSanovSyllableProduct_growth :
    ∀ (t : List (Fin 2 × ℤ)) (p : Fin 2 × ℤ),
      List.IsChain (fun a b => a.1 ≠ b.1) (p :: t) →
      (∀ x ∈ p :: t, x.2 ≠ 0) →
      sourceSanovGrowth p.1 (((sourceSanovSyllableProduct (p :: t) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).mulVec
        (sourceSanovSeed ((p :: t).getLast (List.cons_ne_nil p t)).1)) := by
  intro t
  induction t with
  | nil =>
    intro p _ hexp
    obtain ⟨g, n⟩ := p
    have hn : n ≠ 0 := hexp _ List.mem_cons_self
    have h2 : (1 : ℤ) < |2 * n| := by
      have h1 : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
      rw [abs_mul]
      norm_num
      linarith
    rcases eq_or_ne g 0 with rfl | hgne
    · rw [show sourceSanovSyllableProduct [((0 : Fin 2), n)] = sourceSanovA ^ n from by simp [sourceSanovSyllableProduct],
        sourceSanovA_zpow_mulVec]
      unfold sourceSanovGrowth sourceSanovSeed
      simp only [List.getLast_singleton']
      constructor <;> simpa using h2
    · have hg1 : g = 1 := by
        fin_cases g
        · exact absurd rfl hgne
        · rfl
      subst hg1
      rw [show sourceSanovSyllableProduct [((1 : Fin 2), n)] = sourceSanovB ^ n from by simp [sourceSanovSyllableProduct],
        sourceSanovB_zpow_mulVec]
      unfold sourceSanovGrowth sourceSanovSeed
      simp only [List.getLast_singleton']
      constructor <;> simpa using h2
  | cons q t' ih =>
    intro p halt hexp
    cases halt with
    | cons_cons hpq hrest =>
    have hIH := ih q hrest (fun x hx => hexp x (List.mem_cons_of_mem _ hx))
    obtain ⟨g, n⟩ := p
    have hn : n ≠ 0 := hexp _ List.mem_cons_self
    rcases eq_or_ne g 0 with rfl | hgne
    ·
      have hq1 : q.1 = 1 := by
        rcases q with ⟨gq, m⟩
        fin_cases gq
        · simp at hpq
        · rfl
      rw [hq1] at hIH
      obtain ⟨hdom, hgrow⟩ := hIH
      rw [show sourceSanovSyllableProduct (((0 : Fin 2), n) :: q :: t') = sourceSanovA ^ n * sourceSanovSyllableProduct (q :: t') from
          by simp [sourceSanovSyllableProduct],
        SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, sourceSanovA_zpow_mulVec]
      unfold sourceSanovGrowth
      have hdom' : |(((sourceSanovSyllableProduct (q :: t') : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).mulVec
          (sourceSanovSeed ((q :: t').getLast (List.cons_ne_nil q t')).1)) 0|
          < |(((sourceSanovSyllableProduct (q :: t') : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).mulVec
          (sourceSanovSeed ((q :: t').getLast (List.cons_ne_nil q t')).1)) 1| := hdom
      have hstep := sourceSanov_abs_growth hn hdom'
      constructor
      · simpa using hstep
      · simpa using lt_trans hgrow hstep
    ·
      have hg1 : g = 1 := by
        fin_cases g
        · exact absurd rfl hgne
        · rfl
      subst hg1
      have hq0 : q.1 = 0 := by
        rcases q with ⟨gq, m⟩
        fin_cases gq
        · rfl
        · simp at hpq
      rw [hq0] at hIH
      obtain ⟨hdom, hgrow⟩ := hIH
      rw [show sourceSanovSyllableProduct (((1 : Fin 2), n) :: q :: t') = sourceSanovB ^ n * sourceSanovSyllableProduct (q :: t') from
          by simp [sourceSanovSyllableProduct],
        SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, sourceSanovB_zpow_mulVec]
      unfold sourceSanovGrowth
      have hdom' : |(((sourceSanovSyllableProduct (q :: t') : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).mulVec
          (sourceSanovSeed ((q :: t').getLast (List.cons_ne_nil q t')).1)) 1|
          < |(((sourceSanovSyllableProduct (q :: t') : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).mulVec
          (sourceSanovSeed ((q :: t').getLast (List.cons_ne_nil q t')).1)) 0| := hdom
      have hstep := sourceSanov_abs_growth hn hdom'
      constructor
      · simpa using hstep
      · simpa using lt_trans hgrow hstep

/-- A nonempty alternating word of nonzero powers of the original matrices is nonidentity. -/
theorem sourceSanovSyllableProduct_ne_one (L : List (Fin 2 × ℤ)) (hne : L ≠ [])
    (halt : List.IsChain (fun a b => a.1 ≠ b.1) L) (hexp : ∀ x ∈ L, x.2 ≠ 0) :
    sourceSanovSyllableProduct L ≠ 1 := by
  obtain ⟨p, t, rfl⟩ : ∃ p t, L = p :: t := by
    cases L with
    | nil => exact absurd rfl hne
    | cons p t => exact ⟨p, t, rfl⟩
  intro h1
  have hinv := sourceSanovSyllableProduct_growth t p halt hexp
  rw [h1] at hinv
  have hseed : ∀ i, ((1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).mulVec
      (sourceSanovSeed ((p :: t).getLast (List.cons_ne_nil p t)).1) i
      = sourceSanovSeed ((p :: t).getLast (List.cons_ne_nil p t)).1 i := by
    intro i
    rw [SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  obtain ⟨-, hgrow⟩ := hinv
  rw [hseed] at hgrow

  unfold sourceSanovSeed at hgrow
  split at hgrow <;> simp at hgrow


end
end Dubon2026
