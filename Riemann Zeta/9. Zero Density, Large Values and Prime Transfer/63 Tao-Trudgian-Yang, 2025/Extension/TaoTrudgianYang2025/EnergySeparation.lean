import TaoTrudgianYang2025.EnergyPartition
import TaoTrudgianYang2025.LargeValuePattern
import Mathlib.Data.ZMod.Basic

noncomputable section

namespace TaoTrudgianYang2025

open scoped BigOperators

/-- One explicit index for each unit of a natural-valued weight on a finite
set.  This is the generic multiplicity-safe representation used for zero
sets and other weighted detector families. -/
abbrev WeightedCopy {α : Type*} [DecidableEq α]
    (S : Finset α) (weight : α → ℕ) :=
  Σ x : ↥S, Fin (weight x.1)

/-- Expanding a finite weighted set into copies preserves its total weight. -/
theorem weightedCopy_card {α : Type*} [DecidableEq α]
    (S : Finset α) (weight : α → ℕ) :
    Fintype.card (WeightedCopy S weight) = ∑ x ∈ S, weight x := by
  simp only [Fintype.card_sigma, Fintype.card_fin]
  exact Finset.sum_attach S weight

def unitBinFinset {α : Type*} [Fintype α] [DecidableEq α]
    (W : α → ℝ) (z : ℤ) : Finset α :=
  Finset.univ.filter fun x => ⌊W x⌋ = z

/-- A shifted unit-bin count on explicit copies is exactly the weighted sum
over the corresponding attached base points. -/
theorem weightedCopy_unitBin_card
    {α : Type*} [DecidableEq α] (S : Finset α) (weight : α → ℕ)
    (shift : ↥S → ℝ) (z : ℤ) :
    (unitBinFinset
      (fun x : WeightedCopy S weight => shift x.1) z).card =
      ∑ x ∈ S.attach.filter (fun x => ⌊shift x⌋ = z), weight x.1 := by
  classical
  let B := S.attach.filter (fun x => ⌊shift x⌋ = z)
  letI : Fintype ↥B := Fintype.ofFinset B (fun x => Iff.rfl)
  change ((Finset.univ : Finset (WeightedCopy S weight)).filter
    (fun x => ⌊shift x.1⌋ = z)).card = _
  rw [← Fintype.card_subtype]
  let e : {x : WeightedCopy S weight // ⌊shift x.1⌋ = z} ≃
      Σ x : ↥B, Fin (weight x.1.1) :=
    { toFun := fun x => ⟨⟨x.1.1, by
          simp only [B, Finset.mem_filter, Finset.mem_attach]
          exact ⟨trivial, x.2⟩⟩, x.1.2⟩
      invFun := fun x => ⟨⟨x.1.1, x.2⟩, by
          exact (Finset.mem_filter.mp x.1.2).2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact (Finset.sum_subtype B (fun x => Iff.rfl) (fun x : ↥S => weight x.1)).symm

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

/-- A finite base coloring and a unit-bin occupancy bound jointly produce
four one-separated energy classes.  Each refined class remembers its original
branch/scale color, and the complete indexed energy estimate is retained. -/
theorem exists_separated_energy_color_classes
    {α κ : Type*} [Fintype α] [LinearOrder α]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (W : α → ℝ) (baseColor : α → κ) (L : ℕ)
    (hlocal : ∀ z : ℤ, (unitBinFinset W z).card ≤ L) :
    ∃ label : Fin 4 → κ × (ZMod 2 × Fin (L + 1)),
      let color := separatedRefinementColor W baseColor L hlocal
      let Wᵢ := fun i : Fin 4 =>
        fun x : EnergyColorFiber color (label i) => W x.1
      4 * (approximateAdditiveEnergyOf 1 W : ℝ) ≤
          9 * (Fintype.card (κ × (ZMod 2 × Fin (L + 1))) : ℝ) ^ 4 *
            ((approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ)) ∧
        (∀ (i : Fin 4) (x : EnergyColorFiber color (label i)),
          baseColor x.1 = (label i).1) ∧
        (∀ (i : Fin 4) (x y : EnergyColorFiber color (label i)),
          x ≠ y → 1 ≤ |W x.1 - W y.1|) := by
  classical
  let color := separatedRefinementColor W baseColor L hlocal
  obtain ⟨label, henergy⟩ := exists_energy_color_classes W color
  refine ⟨label, henergy, ?_, ?_⟩
  · intro i x
    exact separatedRefinementColor_base W baseColor L hlocal x.2
  · intro i x y hxy
    exact separatedRefinementColor_oneSeparated W baseColor L hlocal
      (label i) x y hxy

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

/-- A bounded perturbation of an indexed one-separated family has an explicit
unit-bin occupancy bound.  This is the quantitative input needed to color the
perturbed family back into one-separated classes without losing indices. -/
theorem unitBinFinset_perturbation_card_le_natCeil
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W W' : ι → ℝ) (d : ℝ) (hd : 0 ≤ d)
    (hsep : ∀ x y : ι, x ≠ y → 1 ≤ |W x - W y|)
    (hpert : ∀ x, |W' x - W x| ≤ d) (z : ℤ) :
    (unitBinFinset W' z).card ≤ Nat.ceil (2 * d + 2) := by
  classical
  let B := unitBinFinset W' z
  let values := B.image W
  have hinj : Function.Injective W :=
    injective_of_indexed_oneSeparated W hsep
  have hcard : values.card = B.card := by
    exact Finset.card_image_iff.mpr hinj.injOn
  have hvaluesSep : ∀ x ∈ values, ∀ y ∈ values,
      x ≠ y → 1 ≤ |x - y| := by
    intro x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    exact hsep i j (fun hij => hxy (congrArg W hij))
  have hvaluesMem : ∀ x ∈ values,
      (z : ℝ) - d ≤ x ∧ x ≤ (z : ℝ) + 1 + d := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hibin : ⌊W' i⌋ = z := by
      simpa only [B, unitBinFinset, Finset.mem_filter,
        Finset.mem_univ, true_and] using hi
    have hilower : (z : ℝ) ≤ W' i := by
      rw [← hibin]
      exact Int.floor_le (W' i)
    have hiupper : W' i < (z : ℝ) + 1 := by
      rw [← hibin]
      exact_mod_cast Int.lt_floor_add_one (W' i)
    have hipert := hpert i
    rw [abs_le] at hipert
    constructor
    · linarith
    · linarith
  have hlength : 0 ≤ ((z : ℝ) + 1 + d) - ((z : ℝ) - d) := by
    linarith
  have hreal : (B.card : ℝ) ≤ 2 * d + 2 := by
    rw [← hcard]
    have hbound := oneSeparated_card_cast_le_interval_length_add_one
      values hvaluesSep hlength hvaluesMem
    convert hbound using 1
    ring
  have hceil : 2 * d + 2 ≤ (Nat.ceil (2 * d + 2) : ℝ) :=
    Nat.le_ceil _
  exact_mod_cast hreal.trans hceil

/-- Complete finite energy bookkeeping for a bounded perturbation of a
one-separated indexed family.  The original energy first transfers to unit
energy of the perturbed family with an explicit tolerance factor, after which
bounded-multiplicity coloring produces four one-separated classes. -/
theorem exists_separated_perturbed_energy_classes
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (W W' : ι → ℝ) (d : ℝ) (hd : 0 ≤ d)
    (hsep : ∀ x y : ι, x ≠ y → 1 ≤ |W x - W y|)
    (hpert : ∀ x, |W' x - W x| ≤ d) :
    let L := Nat.ceil (2 * d + 2)
    let hlocal : ∀ z : ℤ, (unitBinFinset W' z).card ≤ L :=
      fun z => unitBinFinset_perturbation_card_le_natCeil
        W W' d hd hsep hpert z
    ∃ label : Fin 4 → ZMod 2 × Fin (L + 1),
      let color := boundedMultiplicityColor W' L hlocal
      let Wᵢ := fun i : Fin 4 =>
        fun x : EnergyColorFiber color (label i) => W' x.1
      approximateAdditiveEnergyOf 1 W ≤
          (4 * Nat.ceil (1 + 4 * d) + 6) *
            approximateAdditiveEnergyOf 1 W' ∧
        4 * (approximateAdditiveEnergyOf 1 W' : ℝ) ≤
          9 * (Fintype.card (ZMod 2 × Fin (L + 1)) : ℝ) ^ 4 *
            ((approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ)) ∧
        ∀ (i : Fin 4) (x y : EnergyColorFiber color (label i)),
          x ≠ y → 1 ≤ |W' x.1 - W' y.1| := by
  classical
  dsimp only
  let L := Nat.ceil (2 * d + 2)
  let hlocal : ∀ z : ℤ, (unitBinFinset W' z).card ≤ L :=
    fun z => unitBinFinset_perturbation_card_le_natCeil
      W W' d hd hsep hpert z
  let color := boundedMultiplicityColor W' L hlocal
  have htransfer : approximateAdditiveEnergyOf 1 W ≤
      (4 * Nat.ceil (1 + 4 * d) + 6) *
        approximateAdditiveEnergyOf 1 W' := by
    calc
      approximateAdditiveEnergyOf 1 W ≤
          approximateAdditiveEnergyOf (1 + 4 * d) W' :=
        approximateAdditiveEnergyOf_perturbation_le hpert
      _ ≤ (4 * Nat.ceil (1 + 4 * d) + 6) *
            approximateAdditiveEnergyOf 1 W' :=
        approximateAdditiveEnergyOf_le_natCeil_mul_unit _ _
  obtain ⟨label, henergy⟩ := exists_energy_color_classes W' color
  refine ⟨label, htransfer, ?_, ?_⟩
  · simpa only [color] using henergy
  · intro i x y hxy
    exact oneSeparated_on_boundedMultiplicityColor W' L hlocal
      (label i) x y hxy

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
