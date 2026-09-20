import TaoTrudgianYang2025.EnergyPartition
import TaoTrudgianYang2025.LargeValuePattern
import Mathlib.Data.ZMod.Basic

noncomputable section

namespace TaoTrudgianYang2025

open scoped BigOperators

def unitBinFinset {α : Type*} [Fintype α] [DecidableEq α]
    (W : α → ℝ) (z : ℤ) : Finset α :=
  Finset.univ.filter fun x => ⌊W x⌋ = z

noncomputable def unitBinRank {α : Type*} [Fintype α] [LinearOrder α]
    (W : α → ℝ) (x : α) : ℕ :=
  (Finset.univ.filter fun y => ⌊W y⌋ = ⌊W x⌋ ∧ y < x).card

theorem unitBinRank_lt_card {α : Type*} [Fintype α] [LinearOrder α]
    (W : α → ℝ) (x : α) :
    unitBinRank W x < (unitBinFinset W ⌊W x⌋).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      unitBinFinset] at hy ⊢
    exact hy.1
  · intro heq
    have hxRight : x ∈ unitBinFinset W ⌊W x⌋ := by
      simp [unitBinFinset]
    have hxLeft : x ∉ Finset.univ.filter
        (fun y => ⌊W y⌋ = ⌊W x⌋ ∧ y < x) := by simp
    exact hxLeft (heq ▸ hxRight)

theorem unitBinRank_injective_on_bin {α : Type*} [Fintype α] [LinearOrder α]
    (W : α → ℝ) {x y : α} (hbin : ⌊W x⌋ = ⌊W y⌋)
    (hrank : unitBinRank W x = unitBinRank W y) : x = y := by
  by_contra hxy
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · have hproper :
        (Finset.univ.filter fun z => ⌊W z⌋ = ⌊W x⌋ ∧ z < x) ⊂
          (Finset.univ.filter fun z => ⌊W z⌋ = ⌊W y⌋ ∧ z < y) := by
      rw [Finset.ssubset_iff_subset_ne]
      constructor
      · intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        exact ⟨hz.1.trans hbin, hz.2.trans hlt⟩
      · intro heq
        have hyRight : x ∈ Finset.univ.filter
            (fun z => ⌊W z⌋ = ⌊W y⌋ ∧ z < y) := by
          simp [hbin, hlt]
        have hxLeft : x ∉ Finset.univ.filter
            (fun z => ⌊W z⌋ = ⌊W x⌋ ∧ z < x) := by simp
        exact hxLeft (heq ▸ hyRight)
    have := Finset.card_lt_card hproper
    exact (ne_of_lt this) hrank
  · have hproper :
        (Finset.univ.filter fun z => ⌊W z⌋ = ⌊W y⌋ ∧ z < y) ⊂
          (Finset.univ.filter fun z => ⌊W z⌋ = ⌊W x⌋ ∧ z < x) := by
      rw [Finset.ssubset_iff_subset_ne]
      constructor
      · intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        exact ⟨hz.1.trans hbin.symm, hz.2.trans hgt⟩
      · intro heq
        have hxRight : y ∈ Finset.univ.filter
            (fun z => ⌊W z⌋ = ⌊W x⌋ ∧ z < x) := by
          simp [hbin.symm, hgt]
        have hyLeft : y ∉ Finset.univ.filter
            (fun z => ⌊W z⌋ = ⌊W y⌋ ∧ z < y) := by simp
        exact hyLeft (heq ▸ hxRight)
    have := Finset.card_lt_card hproper
    exact (ne_of_gt this) hrank

noncomputable def boundedMultiplicityColor {α : Type*}
    [Fintype α] [LinearOrder α]
    (W : α → ℝ) (L : ℕ)
    (hlocal : ∀ z : ℤ, (unitBinFinset W z).card ≤ L)
    (x : α) : ZMod 2 × Fin (L + 1) :=
  (((⌊W x⌋ : ℤ) : ZMod 2),
    ⟨unitBinRank W x,
      lt_of_lt_of_le (unitBinRank_lt_card W x)
        ((hlocal ⌊W x⌋).trans (Nat.le_add_right L 1))⟩)

theorem oneSeparated_on_boundedMultiplicityColor {α : Type*}
    [Fintype α] [LinearOrder α]
    (W : α → ℝ) (L : ℕ)
    (hlocal : ∀ z : ℤ, (unitBinFinset W z).card ≤ L)
    (label : ZMod 2 × Fin (L + 1)) :
    ∀ x : EnergyColorFiber (boundedMultiplicityColor W L hlocal) label,
      ∀ y : EnergyColorFiber (boundedMultiplicityColor W L hlocal) label,
        x ≠ y → 1 ≤ |W x.1 - W y.1| := by
  intro x y hxy
  have hcolor : boundedMultiplicityColor W L hlocal x.1 =
      boundedMultiplicityColor W L hlocal y.1 := x.2.trans y.2.symm
  have hparity : ((⌊W x.1⌋ : ℤ) : ZMod 2) =
      ((⌊W y.1⌋ : ℤ) : ZMod 2) := by
    simpa only [boundedMultiplicityColor] using congrArg Prod.fst hcolor
  have hrank : unitBinRank W x.1 = unitBinRank W y.1 := by
    have := congrArg (fun c : ZMod 2 × Fin (L + 1) => c.2.1) hcolor
    simpa only [boundedMultiplicityColor] using this
  have hbin_ne : ⌊W x.1⌋ ≠ ⌊W y.1⌋ := by
    intro hbin
    have hval : x.1 = y.1 := unitBinRank_injective_on_bin W hbin hrank
    apply hxy
    exact Subtype.ext hval
  have hmod : ⌊W x.1⌋ % 2 = ⌊W y.1⌋ % 2 :=
    (ZMod.intCast_eq_intCast_iff' _ _ 2).mp hparity
  have hxl := Int.floor_le (W x.1)
  have hxu := Int.lt_floor_add_one (W x.1)
  have hyl := Int.floor_le (W y.1)
  have hyu := Int.lt_floor_add_one (W y.1)
  rcases lt_or_gt_of_ne hbin_ne with hlt | hgt
  · have hgap : ⌊W x.1⌋ + 2 ≤ ⌊W y.1⌋ := by omega
    have hgapR : (⌊W x.1⌋ : ℝ) + 2 ≤ (⌊W y.1⌋ : ℝ) := by
      exact_mod_cast hgap
    rw [abs_of_nonpos]
    · linarith
    · linarith
  · have hgap : ⌊W y.1⌋ + 2 ≤ ⌊W x.1⌋ := by omega
    have hgapR : (⌊W y.1⌋ : ℝ) + 2 ≤ (⌊W x.1⌋ : ℝ) := by
      exact_mod_cast hgap
    rw [abs_of_nonneg]
    · linarith
    · linarith

/-- Refine any finite base coloring by the explicit unit-bin separation
color. -/
noncomputable def separatedRefinementColor
    {α κ : Type*} [Fintype α] [LinearOrder α]
    (W : α → ℝ) (baseColor : α → κ) (L : ℕ)
    (hlocal : ∀ z : ℤ, (unitBinFinset W z).card ≤ L) (x : α) :
    κ × (ZMod 2 × Fin (L + 1)) :=
  (baseColor x, boundedMultiplicityColor W L hlocal x)

/-- A refined color remembers its original base color. -/
theorem separatedRefinementColor_base
    {α κ : Type*} [Fintype α] [LinearOrder α]
    (W : α → ℝ) (baseColor : α → κ) (L : ℕ)
    (hlocal : ∀ z : ℤ, (unitBinFinset W z).card ≤ L)
    {x : α} {label : κ × (ZMod 2 × Fin (L + 1))}
    (hx : separatedRefinementColor W baseColor L hlocal x = label) :
    baseColor x = label.1 := by
  exact congrArg Prod.fst hx

/-- Every fiber of the refined coloring is one-separated as an indexed
family. -/
theorem separatedRefinementColor_oneSeparated
    {α κ : Type*} [Fintype α] [LinearOrder α]
    (W : α → ℝ) (baseColor : α → κ) (L : ℕ)
    (hlocal : ∀ z : ℤ, (unitBinFinset W z).card ≤ L)
    (label : κ × (ZMod 2 × Fin (L + 1)))
    (x y : EnergyColorFiber
      (separatedRefinementColor W baseColor L hlocal) label)
    (hxy : x ≠ y) :
    1 ≤ |W x.1 - W y.1| := by
  have hsecond : boundedMultiplicityColor W L hlocal x.1 = label.2 :=
    congrArg Prod.snd x.2
  have hsecondY : boundedMultiplicityColor W L hlocal y.1 = label.2 :=
    congrArg Prod.snd y.2
  let x' : EnergyColorFiber (boundedMultiplicityColor W L hlocal) label.2 :=
    ⟨x.1, hsecond⟩
  let y' : EnergyColorFiber (boundedMultiplicityColor W L hlocal) label.2 :=
    ⟨y.1, hsecondY⟩
  have hxy' : x' ≠ y' := by
    intro h
    apply hxy
    have hval : x'.val = y'.val :=
      congrArg (fun z : EnergyColorFiber
        (boundedMultiplicityColor W L hlocal) label.2 => z.val) h
    exact Subtype.ext hval
  exact oneSeparated_on_boundedMultiplicityColor W L hlocal
    label.2 x' y' hxy'

/-- An indexed one-separated family is injective.  Thus passing to its image
does not discard any index or analytic multiplicity. -/
theorem injective_of_indexed_oneSeparated
    {ι : Type*} [Fintype ι] (W : ι → ℝ)
    (hsep : ∀ x y : ι, x ≠ y → 1 ≤ |W x - W y|) :
    Function.Injective W := by
  intro x y hxy
  by_contra hne
  have h := hsep x y hne
  rw [hxy, sub_self, abs_zero] at h
  norm_num at h

/-- The image finset of an indexed one-separated family is one-separated. -/
theorem image_isOneSeparated_of_indexed_oneSeparated
    {ι : Type*} [Fintype ι] [DecidableEq ι] (W : ι → ℝ)
    (hsep : ∀ x y : ι, x ≠ y → 1 ≤ |W x - W y|) :
    IsOneSeparated (Finset.univ.image W) := by
  intro t ht u hu htu
  rw [Finset.mem_image] at ht hu
  obtain ⟨x, _, rfl⟩ := ht
  obtain ⟨y, _, rfl⟩ := hu
  exact hsep x y (fun hxy => htu (congrArg W hxy))

/-- Approximate additive energy is invariant under an equivalence of its
finite index type when the represented values agree. -/
theorem approximateAdditiveEnergyOf_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (r : ℝ) (W : ι → ℝ) (V : κ → ℝ) (e : ι ≃ κ)
    (hvalue : ∀ x, V (e x) = W x) :
    approximateAdditiveEnergyOf r W = approximateAdditiveEnergyOf r V := by
  classical
  unfold approximateAdditiveEnergyOf
  apply Finset.card_bij (fun q _ j => e (q j))
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    simpa only [hvalue] using hq
  · intro q₁ hq₁ q₂ hq₂ heq
    funext j
    exact e.injective (congrFun heq j)
  · intro q hq
    refine ⟨fun j => e.symm (q j), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      have hinverse : ∀ x : κ, W (e.symm x) = V x := by
        intro x
        rw [← hvalue (e.symm x), e.apply_symm_apply]
      simpa only [hinverse] using hq
    · funext j
      exact e.apply_symm_apply (q j)

/-- For a one-separated indexed family, passage to the image finset preserves
unit-tolerance additive energy exactly. -/
theorem finsetAdditiveEnergy_image_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι] (W : ι → ℝ)
    (hsep : ∀ x y : ι, x ≠ y → 1 ≤ |W x - W y|) :
    finsetAdditiveEnergy (Finset.univ.image W) =
      approximateAdditiveEnergyOf 1 W := by
  classical
  have hinj := injective_of_indexed_oneSeparated W hsep
  let e : ι ≃ ↥(Finset.univ.image W) :=
    { toFun := fun x => ⟨W x, Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩⟩
      invFun := fun t => Classical.choose (Finset.mem_image.mp t.2)
      left_inv := by
        intro x
        apply hinj
        exact (Classical.choose_spec (Finset.mem_image.mp
          (show W x ∈ Finset.univ.image W from
            Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩))).2
      right_inv := by
        intro t
        apply Subtype.ext
        exact (Classical.choose_spec (Finset.mem_image.mp t.2)).2 }
  exact (approximateAdditiveEnergyOf_equiv 1 W
    (fun t : ↥(Finset.univ.image W) => (t : ℝ)) e (fun _ => rfl)).symm

end TaoTrudgianYang2025
