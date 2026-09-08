import Tao2026.CoefficientSelection
import Tao2026.PowerfulAsymptotics
import Tao2026.PowerfulNumbers

/-!
# Finite powerful-relation reindexing

Exact finite reindexing of the powerful pairs in Tao's Corollary 2.11 by the
unique square-times-squarefree-cube parameters.  Quantitative estimates for
the resulting four-variable equation are developed later.
-/

namespace Tao2026

open Filter Asymptotics

noncomputable def powerfulRelationPairsUpTo
    (a b h x : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.Icc 1 x).product (Finset.Icc 1 (x + h))).filter fun nm =>
    Powerful nm.1 ∧ Powerful nm.2 ∧
      a * nm.1 + h = b * nm.2 ∧ a * nm.1 ≤ x

theorem mem_powerfulRelationPairsUpTo {a b h x : ℕ} {nm : ℕ × ℕ} :
    nm ∈ powerfulRelationPairsUpTo a b h x ↔
      1 ≤ nm.1 ∧ nm.1 ≤ x ∧
      1 ≤ nm.2 ∧ nm.2 ≤ x + h ∧
      Powerful nm.1 ∧ Powerful nm.2 ∧
      a * nm.1 + h = b * nm.2 ∧ a * nm.1 ≤ x := by
  classical
  simp [powerfulRelationPairsUpTo, and_assoc]

noncomputable def powerfulRelationRepresentationsUpTo
    (a b h x : ℕ) :
    Finset ((Σ _cubeBase : ℕ, ℕ) × (Σ _cubeBase : ℕ, ℕ)) := by
  classical
  exact ((powerfulOneTermRepresentations x).product
    (powerfulOneTermRepresentations (x + h))).filter fun rs =>
      a * powerfulOneTermRepresentationValue rs.1 + h =
        b * powerfulOneTermRepresentationValue rs.2 ∧
      a * powerfulOneTermRepresentationValue rs.1 ≤ x

def powerfulRelationRepresentationValue
    (rs : (Σ _cubeBase : ℕ, ℕ) × (Σ _cubeBase : ℕ, ℕ)) :
    ℕ × ℕ :=
  (powerfulOneTermRepresentationValue rs.1,
    powerfulOneTermRepresentationValue rs.2)

theorem mem_powerfulRelationRepresentationsUpTo_iff
    {a b h x : ℕ}
    {rs : (Σ _cubeBase : ℕ, ℕ) × (Σ _cubeBase : ℕ, ℕ)} :
    rs ∈ powerfulRelationRepresentationsUpTo a b h x ↔
      rs.1 ∈ powerfulOneTermRepresentations x ∧
      rs.2 ∈ powerfulOneTermRepresentations (x + h) ∧
      a * powerfulOneTermRepresentationValue rs.1 + h =
        b * powerfulOneTermRepresentationValue rs.2 ∧
      a * powerfulOneTermRepresentationValue rs.1 ≤ x := by
  classical
  simp [powerfulRelationRepresentationsUpTo, and_assoc]

private theorem representationValue_mem_veryBadOneTermNumbersUpTo
    {x : ℕ} {r : Σ _cubeBase : ℕ, ℕ}
    (hr : r ∈ powerfulOneTermRepresentations x) :
    powerfulOneTermRepresentationValue r ∈ veryBadOneTermNumbersUpTo x := by
  rw [← image_powerfulOneTermRepresentations x]
  exact Finset.mem_image.mpr ⟨r, hr, rfl⟩

theorem image_powerfulRelationRepresentationsUpTo
    (a b h x : ℕ) :
    (powerfulRelationRepresentationsUpTo a b h x).image
        powerfulRelationRepresentationValue =
      powerfulRelationPairsUpTo a b h x := by
  classical
  ext nm
  constructor
  · intro hnm
    rw [Finset.mem_image] at hnm
    rcases hnm with ⟨rs, hrs, rfl⟩
    have hrs' := mem_powerfulRelationRepresentationsUpTo_iff.mp hrs
    have hnMem := representationValue_mem_veryBadOneTermNumbersUpTo hrs'.1
    have hmMem := representationValue_mem_veryBadOneTermNumbersUpTo hrs'.2.1
    simp only [veryBadOneTermNumbersUpTo, Finset.mem_filter, Finset.mem_Icc] at hnMem hmMem
    exact mem_powerfulRelationPairsUpTo.mpr
      ⟨hnMem.1.1, hnMem.1.2, hmMem.1.1, hmMem.1.2,
        (mem_veryBadOneTermSet_iff.mp hnMem.2).2,
        (mem_veryBadOneTermSet_iff.mp hmMem.2).2,
        hrs'.2.2.1, hrs'.2.2.2⟩
  · intro hnm
    have hnm' := mem_powerfulRelationPairsUpTo.mp hnm
    have hnVeryBad : nm.1 ∈ veryBadOneTermNumbersUpTo x := by
      simp only [veryBadOneTermNumbersUpTo, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hnm'.1, hnm'.2.1⟩,
        mem_veryBadOneTermSet_iff.mpr ⟨hnm'.1, hnm'.2.2.2.2.1⟩⟩
    have hmVeryBad : nm.2 ∈ veryBadOneTermNumbersUpTo (x + h) := by
      simp only [veryBadOneTermNumbersUpTo, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hnm'.2.2.1, hnm'.2.2.2.1⟩,
        mem_veryBadOneTermSet_iff.mpr
          ⟨hnm'.2.2.1, hnm'.2.2.2.2.2.1⟩⟩
    rw [← image_powerfulOneTermRepresentations x, Finset.mem_image] at hnVeryBad
    rw [← image_powerfulOneTermRepresentations (x + h),
      Finset.mem_image] at hmVeryBad
    rcases hnVeryBad with ⟨r, hr, hrValue⟩
    rcases hmVeryBad with ⟨s, hs, hsValue⟩
    rw [Finset.mem_image]
    refine ⟨(r, s), ?_, ?_⟩
    · apply mem_powerfulRelationRepresentationsUpTo_iff.mpr
      simpa only [hrValue, hsValue] using
        ⟨hr, hs, hnm'.2.2.2.2.2.2.1, hnm'.2.2.2.2.2.2.2⟩
    · exact Prod.ext hrValue hsValue

theorem injOn_powerfulRelationRepresentationValue
    (a b h x : ℕ) :
    Set.InjOn powerfulRelationRepresentationValue
      (powerfulRelationRepresentationsUpTo a b h x) := by
  rintro ⟨r₁, s₁⟩ hrs₁ ⟨r₂, s₂⟩ hrs₂ heq
  have hrs₁' := mem_powerfulRelationRepresentationsUpTo_iff.mp hrs₁
  have hrs₂' := mem_powerfulRelationRepresentationsUpTo_iff.mp hrs₂
  have hfirst : powerfulOneTermRepresentationValue r₁ =
      powerfulOneTermRepresentationValue r₂ := congrArg Prod.fst heq
  have hsecond : powerfulOneTermRepresentationValue s₁ =
      powerfulOneTermRepresentationValue s₂ := congrArg Prod.snd heq
  have hr := injOn_powerfulOneTermRepresentationValue x hrs₁'.1 hrs₂'.1 hfirst
  have hs := injOn_powerfulOneTermRepresentationValue (x + h)
    hrs₁'.2.1 hrs₂'.2.1 hsecond
  exact Prod.ext hr hs

theorem card_powerfulRelationRepresentationsUpTo
    (a b h x : ℕ) :
    (powerfulRelationRepresentationsUpTo a b h x).card =
      (powerfulRelationPairsUpTo a b h x).card := by
  rw [← image_powerfulRelationRepresentationsUpTo a b h x,
    Finset.card_image_iff.mpr
      (injOn_powerfulRelationRepresentationValue a b h x)]

private theorem injOn_fst_powerfulRelationPairsUpTo
    {a b h x : ℕ} (hb : 0 < b) :
    Set.InjOn (fun nm : ℕ × ℕ ↦ nm.1)
      (powerfulRelationPairsUpTo a b h x) := by
  rintro ⟨n₁, m₁⟩ h₁ ⟨n₂, m₂⟩ h₂ hn
  change n₁ = n₂ at hn
  subst n₂
  have h₁' : a * n₁ + h = b * m₁ :=
    (mem_powerfulRelationPairsUpTo.mp h₁).2.2.2.2.2.2.1
  have h₂' : a * n₁ + h = b * m₂ :=
    (mem_powerfulRelationPairsUpTo.mp h₂).2.2.2.2.2.2.1
  have hm : m₁ = m₂ := by
    apply Nat.mul_left_cancel hb
    omega
  subst m₂
  rfl

private theorem injOn_snd_powerfulRelationPairsUpTo
    {a b h x : ℕ} (ha : 0 < a) :
    Set.InjOn (fun nm : ℕ × ℕ ↦ nm.2)
      (powerfulRelationPairsUpTo a b h x) := by
  rintro ⟨n₁, m₁⟩ h₁ ⟨n₂, m₂⟩ h₂ hm
  change m₁ = m₂ at hm
  subst m₂
  have h₁' : a * n₁ + h = b * m₁ :=
    (mem_powerfulRelationPairsUpTo.mp h₁).2.2.2.2.2.2.1
  have h₂' : a * n₂ + h = b * m₁ :=
    (mem_powerfulRelationPairsUpTo.mp h₂).2.2.2.2.2.2.1
  have hn : n₁ = n₂ := by
    apply Nat.mul_left_cancel ha
    omega
  subst n₂
  rfl

theorem card_powerfulRelationPairsUpTo_le_left
    (a b h x : ℕ) (hb : 0 < b) :
    (powerfulRelationPairsUpTo a b h x).card ≤
      veryBadOneTermCount x := by
  have hsubset :
      (powerfulRelationPairsUpTo a b h x).image (fun nm : ℕ × ℕ ↦ nm.1) ⊆
        veryBadOneTermNumbersUpTo x := by
    intro n hn
    rw [Finset.mem_image] at hn
    rcases hn with ⟨nm, hnm, rfl⟩
    have hnm' := mem_powerfulRelationPairsUpTo.mp hnm
    simp only [veryBadOneTermNumbersUpTo, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hnm'.1, hnm'.2.1⟩,
      mem_veryBadOneTermSet_iff.mpr ⟨hnm'.1, hnm'.2.2.2.2.1⟩⟩
  calc
    (powerfulRelationPairsUpTo a b h x).card =
        ((powerfulRelationPairsUpTo a b h x).image
          (fun nm : ℕ × ℕ ↦ nm.1)).card :=
      (Finset.card_image_iff.mpr
        (injOn_fst_powerfulRelationPairsUpTo hb)).symm
    _ ≤ (veryBadOneTermNumbersUpTo x).card := Finset.card_le_card hsubset
    _ = veryBadOneTermCount x := rfl

theorem card_powerfulRelationPairsUpTo_le_right
    (a b h x : ℕ) (ha : 0 < a) :
    (powerfulRelationPairsUpTo a b h x).card ≤
      veryBadOneTermCount (x + h) := by
  have hsubset :
      (powerfulRelationPairsUpTo a b h x).image (fun nm : ℕ × ℕ ↦ nm.2) ⊆
        veryBadOneTermNumbersUpTo (x + h) := by
    intro m hm
    rw [Finset.mem_image] at hm
    rcases hm with ⟨nm, hnm, rfl⟩
    have hnm' := mem_powerfulRelationPairsUpTo.mp hnm
    simp only [veryBadOneTermNumbersUpTo, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hnm'.2.2.1, hnm'.2.2.2.1⟩,
      mem_veryBadOneTermSet_iff.mpr
        ⟨hnm'.2.2.1, hnm'.2.2.2.2.2.1⟩⟩
  calc
    (powerfulRelationPairsUpTo a b h x).card =
        ((powerfulRelationPairsUpTo a b h x).image
          (fun nm : ℕ × ℕ ↦ nm.2)).card :=
      (Finset.card_image_iff.mpr
        (injOn_snd_powerfulRelationPairsUpTo ha)).symm
    _ ≤ (veryBadOneTermNumbersUpTo (x + h)).card :=
      Finset.card_le_card hsubset
    _ = veryBadOneTermCount (x + h) := rfl

/-- Fixing the left powerful number determines the right one when `b > 0`.
This gives the unconditional square-root-scale baseline before the
generalized-Pell improvement in Corollary 2.11. -/
theorem powerfulRelationPairsUpTo_isBigO_veryBadOneTermCount
    (a b h : ℕ) (hb : 0 < b) :
    ((fun x : ℕ ↦ (powerfulRelationPairsUpTo a b h x).card : ℕ → ℝ) =O[atTop]
      fun x : ℕ ↦ (veryBadOneTermCount x : ℝ)) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [] with x
  rw [one_mul,
    Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast card_powerfulRelationPairsUpTo_le_left a b h x hb

/-- The exact finite relation count has the elementary
`x^(1/2+o(1))` upper bound. Tao's Corollary 2.11 sharpens `1/2` to `2/5`
using the third, generalized-Pell fiber estimate. -/
theorem powerfulRelationPairsUpTo_powerUpperBound_half
    (a b h : ℕ) (hb : 0 < b) :
    PowerUpperBound
      (fun x : ℕ ↦ (powerfulRelationPairsUpTo a b h x).card)
      (1 / 2 : ℝ) := by
  intro ε hε
  exact (powerfulRelationPairsUpTo_isBigO_veryBadOneTermCount a b h hb).trans
    (veryBadOneTermCount_powerUpperBound ε hε)

end Tao2026
