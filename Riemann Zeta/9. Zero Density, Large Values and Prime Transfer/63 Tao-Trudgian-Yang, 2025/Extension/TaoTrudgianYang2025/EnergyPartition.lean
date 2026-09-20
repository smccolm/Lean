import TaoTrudgianYang2025.ToleranceNormalization
import GuthMaynard.ExtractSeparated

/-!
# Finite partition bounds for indexed additive energy

This module supplies the finite mixed-energy inequality needed when a detector
scale is selected separately at each indexed ordinate.  All constructions use
the original finite index types, so equal real values and analytic
multiplicities are never collapsed into sets.
-/

open scoped BigOperators

namespace TaoTrudgianYang2025

noncomputable section

/-- Ordered mixed quadruples from four finite indexed families. -/
abbrev MixedAdditiveQuadrupleOf
    (ι₀ ι₁ ι₂ ι₃ : Type*) := (ι₀ × ι₁) × (ι₂ × ι₃)

/-- Approximate mixed additive energy of four indexed families. -/
noncomputable def mixedApproximateAdditiveEnergyOf
    {ι₀ ι₁ ι₂ ι₃ : Type*}
    [Fintype ι₀] [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    (r : ℝ) (W₀ : ι₀ → ℝ) (W₁ : ι₁ → ℝ)
    (W₂ : ι₂ → ℝ) (W₃ : ι₃ → ℝ) : ℕ :=
  ((Finset.univ : Finset (MixedAdditiveQuadrupleOf ι₀ ι₁ ι₂ ι₃)).filter
    fun q => |W₀ q.1.1 + W₁ q.1.2 - W₂ q.2.1 - W₃ q.2.2| ≤ r).card

private noncomputable def differenceBinsOf
    {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℤ) (g : β → ℤ) : Finset ℤ :=
  (Finset.univ : Finset (α × β)).image fun p => f p.1 - g p.2

private noncomputable def differenceCountOf
    {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℤ) (g : β → ℤ) (z : ℤ) : ℕ :=
  ((Finset.univ : Finset (α × β)).filter
    fun p => f p.1 - g p.2 = z).card

private noncomputable def differenceSquareSumOf
    {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℤ) (g : β → ℤ) : ℕ :=
  ∑ z ∈ differenceBinsOf f g, differenceCountOf f g z ^ 2

private theorem sum_sq_card_fibers
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (key : α → β) :
    (∑ z ∈ S.image key,
        ((S.filter fun x => key x = z).card : ℕ) ^ 2) =
      ∑ p ∈ S, ∑ q ∈ S, if key p = key q then 1 else 0 := by
  classical
  simpa only [Finset.card_eq_sum_ones, Nat.mul_one, Nat.one_mul] using
    (show
      (∑ z ∈ S.image key,
          (∑ x ∈ S.filter (fun y => key y = z), (1 : ℕ)) ^ 2) =
        ∑ p ∈ S, ∑ q ∈ S,
          if key p = key q then (1 : ℕ) * 1 else 0 by
      simp only [pow_two, Finset.sum_mul_sum, Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hkey : key p = key q
      · rw [Finset.sum_eq_single (key p)]
        · simp [hkey]
        · intro z hz hzne
          have hpne : key p ≠ z := fun hpz => hzne hpz.symm
          simp [hpne]
        · intro hnot
          exact (hnot (Finset.mem_image.mpr ⟨p, hp, rfl⟩)).elim
      · simp [hkey])

private theorem differenceCountOf_eq_zero_of_not_mem
    {α β : Type*} [Fintype α] [Fintype β]
    {f : α → ℤ} {g : β → ℤ} {z : ℤ}
    (hz : z ∉ differenceBinsOf f g) :
    differenceCountOf f g z = 0 := by
  classical
  unfold differenceBinsOf at hz
  unfold differenceCountOf
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp
  exact fun hkey => hz (Finset.mem_image.mpr ⟨p, hp, hkey⟩)

private noncomputable def selfDifferenceCorrelationOf
    {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℤ) (g : β → ℤ) : ℕ :=
  ∑ p : α × α, differenceCountOf g g (-(f p.1 - f p.2))

private noncomputable def crossExactEnergyOf
    {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℤ) (g : β → ℤ) : ℕ :=
  ((Finset.univ : Finset ((α × β) × (α × β))).filter fun q =>
    f q.1.1 + g q.2.2 = f q.2.1 + g q.1.2).card

private theorem selfDifferenceCorrelationOf_eq_crossExactEnergyOf
    {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℤ) (g : β → ℤ) :
    selfDifferenceCorrelationOf f g = crossExactEnergyOf f g := by
  classical
  let reorder : ((α × α) × (β × β)) ≃ ((α × β) × (α × β)) :=
    { toFun := fun q => ((q.1.1, q.2.2), (q.1.2, q.2.1))
      invFun := fun q => ((q.1.1, q.2.1), (q.2.2, q.1.2))
      left_inv := by rintro ⟨⟨a, c⟩, ⟨b, d⟩⟩; rfl
      right_inv := by rintro ⟨⟨a, d⟩, ⟨c, b⟩⟩; rfl }
  let left : Finset ((α × α) × (β × β)) :=
    Finset.univ.filter fun q =>
      g q.2.1 - g q.2.2 = -(f q.1.1 - f q.1.2)
  have hLeft : selfDifferenceCorrelationOf f g = left.card := by
    unfold selfDifferenceCorrelationOf differenceCountOf
    simp only [left, Finset.card_eq_sum_ones, Finset.sum_filter,
      Fintype.sum_prod_type]
  rw [hLeft]
  unfold crossExactEnergyOf
  apply Finset.card_equiv reorder
  intro q
  rcases q with ⟨⟨a, c⟩, ⟨b, d⟩⟩
  simp [left, reorder]
  constructor <;> intro h <;> omega

private theorem selfDifferenceCorrelationOf_eq_sum_counts
    {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℤ) (g : β → ℤ) :
    selfDifferenceCorrelationOf f g =
      ∑ z ∈ differenceBinsOf f f,
        differenceCountOf f f z * differenceCountOf g g (-z) := by
  classical
  unfold selfDifferenceCorrelationOf differenceBinsOf differenceCountOf
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (α × α)))
    (t := (Finset.univ : Finset (α × α)).image
      (fun p => f p.1 - f p.2))
    (g := fun p => f p.1 - f p.2)
    (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩)]
  apply Finset.sum_congr rfl
  intro z hz
  calc
    (∑ i ∈ (Finset.univ : Finset (α × α)) with f i.1 - f i.2 = z,
        ((Finset.univ : Finset (β × β)).filter fun p =>
          g p.1 - g p.2 = -(f i.1 - f i.2)).card) =
        ∑ i : α × α, if f i.1 - f i.2 = z then
          ((Finset.univ : Finset (β × β)).filter fun p =>
            g p.1 - g p.2 = -z).card else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hiz : f i.1 - f i.2 = z
      · simp only [hiz, ↓reduceIte]
      · simp only [hiz, ↓reduceIte]
    _ = ((Finset.univ : Finset (α × α)).filter
          (fun p => f p.1 - f p.2 = z)).card *
        ((Finset.univ : Finset (β × β)).filter fun p =>
          g p.1 - g p.2 = -z).card := by
      rw [← Finset.sum_filter, Finset.sum_const, Nat.nsmul_eq_mul]

private theorem differenceSquareSumOf_eq_crossExactEnergyOf
    {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℤ) (g : β → ℤ) :
    differenceSquareSumOf f g = crossExactEnergyOf f g := by
  classical
  unfold differenceSquareSumOf differenceBinsOf differenceCountOf
    crossExactEnergyOf
  rw [sum_sq_card_fibers]
  let same : ((α × β) × (α × β)) ≃ ((α × β) × (α × β)) :=
    Equiv.refl _
  have hLeft :
      (∑ p : α × β, ∑ q : α × β,
        if f p.1 - g p.2 = f q.1 - g q.2 then 1 else 0) =
      ((Finset.univ : Finset ((α × β) × (α × β))).filter fun q =>
        f q.1.1 - g q.1.2 = f q.2.1 - g q.2.2).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter,
      Fintype.sum_prod_type]
  rw [hLeft]
  apply Finset.card_equiv same
  intro q
  rcases q with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  simp [same]
  constructor <;> intro h <;> omega

private theorem sq_crossExactEnergyOf_le_mul_self
    {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℤ) (g : β → ℤ) :
    (crossExactEnergyOf f g : ℝ) ^ 2 ≤
      (differenceSquareSumOf f f : ℝ) *
        (differenceSquareSumOf g g : ℝ) := by
  classical
  let Sf := differenceBinsOf f f
  let Sg := (differenceBinsOf g g).image fun z => -z
  let U := Sf ∪ Sg
  let F : ℤ → ℝ := fun z => differenceCountOf f f z
  let G : ℤ → ℝ := fun z => differenceCountOf g g (-z)
  have hCorr :
      (crossExactEnergyOf f g : ℝ) = ∑ z ∈ U, F z * G z := by
    rw [← selfDifferenceCorrelationOf_eq_crossExactEnergyOf,
      selfDifferenceCorrelationOf_eq_sum_counts]
    simp only [Nat.cast_sum, Nat.cast_mul]
    change (∑ z ∈ Sf, F z * G z) = ∑ z ∈ U, F z * G z
    apply Finset.sum_subset Finset.subset_union_left
    intro z hzU hzSf
    have hz0 : differenceCountOf f f z = 0 :=
      differenceCountOf_eq_zero_of_not_mem hzSf
    simp [F, hz0]
  have hFSq : ∑ z ∈ U, F z ^ 2 = (differenceSquareSumOf f f : ℝ) := by
    simp only [differenceSquareSumOf, Nat.cast_sum, Nat.cast_pow]
    change (∑ z ∈ U, F z ^ 2) = ∑ z ∈ Sf, F z ^ 2
    symm
    apply Finset.sum_subset Finset.subset_union_left
    intro z hzU hzSf
    have hz0 : differenceCountOf f f z = 0 :=
      differenceCountOf_eq_zero_of_not_mem hzSf
    norm_num [F, hz0]
  have hGSq : ∑ z ∈ U, G z ^ 2 = (differenceSquareSumOf g g : ℝ) := by
    have hImage :
        ∑ z ∈ Sg, G z ^ 2 =
          ∑ z ∈ differenceBinsOf g g,
            (differenceCountOf g g z : ℝ) ^ 2 := by
      dsimp only [Sg]
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro z hz
        simp [G]
      · intro x hx y hy hxy
        exact neg_injective hxy
    calc
      ∑ z ∈ U, G z ^ 2 = ∑ z ∈ Sg, G z ^ 2 := by
        symm
        apply Finset.sum_subset Finset.subset_union_right
        intro z hzU hzSg
        have hzNot : -z ∉ differenceBinsOf g g := by
          intro hz
          apply hzSg
          exact Finset.mem_image.mpr ⟨-z, hz, by simp⟩
        have hz0 : differenceCountOf g g (-z) = 0 :=
          differenceCountOf_eq_zero_of_not_mem hzNot
        norm_num [G, hz0]
      _ = ∑ z ∈ differenceBinsOf g g,
          (differenceCountOf g g z : ℝ) ^ 2 := hImage
      _ = (differenceSquareSumOf g g : ℝ) := by
        simp only [differenceSquareSumOf, Nat.cast_sum, Nat.cast_pow]
  rw [hCorr]
  calc
    (∑ z ∈ U, F z * G z) ^ 2 ≤
        (∑ z ∈ U, F z ^ 2) * (∑ z ∈ U, G z ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq U F G
    _ = (differenceSquareSumOf f f : ℝ) *
        (differenceSquareSumOf g g : ℝ) := by rw [hFSq, hGSq]

private noncomputable def exactMixedShiftCountOf
    {ι₀ ι₁ ι₂ ι₃ : Type*}
    [Fintype ι₀] [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    (j : ℤ) (f₀ : ι₀ → ℤ) (f₁ : ι₁ → ℤ)
    (f₂ : ι₂ → ℤ) (f₃ : ι₃ → ℤ) : ℕ :=
  ((Finset.univ : Finset (MixedAdditiveQuadrupleOf ι₀ ι₁ ι₂ ι₃)).filter
    fun q => f₀ q.1.1 + f₁ q.1.2 - f₂ q.2.1 - f₃ q.2.2 = j).card

private noncomputable def shiftedMixedDifferenceCorrelationOf
    {ι₀ ι₁ ι₂ ι₃ : Type*}
    [Fintype ι₀] [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    (j : ℤ) (f₀ : ι₀ → ℤ) (f₁ : ι₁ → ℤ)
    (f₂ : ι₂ → ℤ) (f₃ : ι₃ → ℤ) : ℕ :=
  ∑ p : ι₀ × ι₂,
    differenceCountOf f₃ f₁ (f₀ p.1 - f₂ p.2 - j)

private theorem shiftedMixedDifferenceCorrelationOf_eq_count
    {ι₀ ι₁ ι₂ ι₃ : Type*}
    [Fintype ι₀] [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    (j : ℤ) (f₀ : ι₀ → ℤ) (f₁ : ι₁ → ℤ)
    (f₂ : ι₂ → ℤ) (f₃ : ι₃ → ℤ) :
    shiftedMixedDifferenceCorrelationOf j f₀ f₁ f₂ f₃ =
      exactMixedShiftCountOf j f₀ f₁ f₂ f₃ := by
  classical
  let reorder : ((ι₀ × ι₂) × (ι₃ × ι₁)) ≃
      MixedAdditiveQuadrupleOf ι₀ ι₁ ι₂ ι₃ :=
    { toFun := fun q => ((q.1.1, q.2.2), (q.1.2, q.2.1))
      invFun := fun q => ((q.1.1, q.2.1), (q.2.2, q.1.2))
      left_inv := by rintro ⟨⟨a, c⟩, ⟨d, b⟩⟩; rfl
      right_inv := by rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl }
  let left : Finset ((ι₀ × ι₂) × (ι₃ × ι₁)) :=
    Finset.univ.filter fun q =>
      f₃ q.2.1 - f₁ q.2.2 = f₀ q.1.1 - f₂ q.1.2 - j
  have hLeft : shiftedMixedDifferenceCorrelationOf j f₀ f₁ f₂ f₃ =
      left.card := by
    unfold shiftedMixedDifferenceCorrelationOf differenceCountOf
    simp only [left, Finset.card_eq_sum_ones, Finset.sum_filter,
      Fintype.sum_prod_type]
  rw [hLeft]
  unfold exactMixedShiftCountOf
  apply Finset.card_equiv reorder
  intro q
  rcases q with ⟨⟨a, c⟩, ⟨d, b⟩⟩
  simp [left, reorder]
  constructor <;> intro h <;> omega

private theorem shiftedMixedDifferenceCorrelationOf_eq_sum_counts
    {ι₀ ι₁ ι₂ ι₃ : Type*}
    [Fintype ι₀] [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    (j : ℤ) (f₀ : ι₀ → ℤ) (f₁ : ι₁ → ℤ)
    (f₂ : ι₂ → ℤ) (f₃ : ι₃ → ℤ) :
    shiftedMixedDifferenceCorrelationOf j f₀ f₁ f₂ f₃ =
      ∑ z ∈ differenceBinsOf f₀ f₂,
        differenceCountOf f₀ f₂ z * differenceCountOf f₃ f₁ (z - j) := by
  classical
  unfold shiftedMixedDifferenceCorrelationOf differenceBinsOf differenceCountOf
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (ι₀ × ι₂)))
    (t := (Finset.univ : Finset (ι₀ × ι₂)).image
      (fun p => f₀ p.1 - f₂ p.2))
    (g := fun p => f₀ p.1 - f₂ p.2)
    (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩)]
  apply Finset.sum_congr rfl
  intro z hz
  calc
    (∑ i ∈ (Finset.univ : Finset (ι₀ × ι₂)) with
        f₀ i.1 - f₂ i.2 = z,
        ((Finset.univ : Finset (ι₃ × ι₁)).filter fun p =>
          f₃ p.1 - f₁ p.2 = f₀ i.1 - f₂ i.2 - j).card) =
        ∑ i : ι₀ × ι₂, if f₀ i.1 - f₂ i.2 = z then
          ((Finset.univ : Finset (ι₃ × ι₁)).filter fun p =>
            f₃ p.1 - f₁ p.2 = z - j).card else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hiz : f₀ i.1 - f₂ i.2 = z
      · simp only [hiz, ↓reduceIte]
      · simp only [hiz, ↓reduceIte]
    _ = ((Finset.univ : Finset (ι₀ × ι₂)).filter
          (fun p => f₀ p.1 - f₂ p.2 = z)).card *
        ((Finset.univ : Finset (ι₃ × ι₁)).filter fun p =>
          f₃ p.1 - f₁ p.2 = z - j).card := by
      rw [← Finset.sum_filter, Finset.sum_const, Nat.nsmul_eq_mul]

private theorem sq_exactMixedShiftCountOf_le_cross
    {ι₀ ι₁ ι₂ ι₃ : Type*}
    [Fintype ι₀] [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    (j : ℤ) (f₀ : ι₀ → ℤ) (f₁ : ι₁ → ℤ)
    (f₂ : ι₂ → ℤ) (f₃ : ι₃ → ℤ) :
    (exactMixedShiftCountOf j f₀ f₁ f₂ f₃ : ℝ) ^ 2 ≤
      (differenceSquareSumOf f₀ f₂ : ℝ) *
        (differenceSquareSumOf f₃ f₁ : ℝ) := by
  classical
  let S₀₂ := differenceBinsOf f₀ f₂
  let S₃₁ := (differenceBinsOf f₃ f₁).image fun z => z + j
  let U := S₀₂ ∪ S₃₁
  let F : ℤ → ℝ := fun z => differenceCountOf f₀ f₂ z
  let G : ℤ → ℝ := fun z => differenceCountOf f₃ f₁ (z - j)
  have hCorr :
      (exactMixedShiftCountOf j f₀ f₁ f₂ f₃ : ℝ) =
        ∑ z ∈ U, F z * G z := by
    rw [← shiftedMixedDifferenceCorrelationOf_eq_count,
      shiftedMixedDifferenceCorrelationOf_eq_sum_counts]
    simp only [Nat.cast_sum, Nat.cast_mul]
    change (∑ z ∈ S₀₂, F z * G z) = ∑ z ∈ U, F z * G z
    apply Finset.sum_subset Finset.subset_union_left
    intro z hzU hzS₀₂
    have hz0 : differenceCountOf f₀ f₂ z = 0 :=
      differenceCountOf_eq_zero_of_not_mem hzS₀₂
    simp [F, hz0]
  have hFSq : ∑ z ∈ U, F z ^ 2 =
      (differenceSquareSumOf f₀ f₂ : ℝ) := by
    simp only [differenceSquareSumOf, Nat.cast_sum, Nat.cast_pow]
    change (∑ z ∈ U, F z ^ 2) = ∑ z ∈ S₀₂, F z ^ 2
    symm
    apply Finset.sum_subset Finset.subset_union_left
    intro z hzU hzS₀₂
    have hz0 : differenceCountOf f₀ f₂ z = 0 :=
      differenceCountOf_eq_zero_of_not_mem hzS₀₂
    norm_num [F, hz0]
  have hGSq : ∑ z ∈ U, G z ^ 2 =
      (differenceSquareSumOf f₃ f₁ : ℝ) := by
    have hImage :
        ∑ z ∈ S₃₁, G z ^ 2 =
          ∑ z ∈ differenceBinsOf f₃ f₁,
            (differenceCountOf f₃ f₁ z : ℝ) ^ 2 := by
      dsimp only [S₃₁]
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro z hz
        simp only [G, add_sub_cancel_right]
      · intro x hx y hy hxy
        exact add_right_cancel hxy
    calc
      ∑ z ∈ U, G z ^ 2 = ∑ z ∈ S₃₁, G z ^ 2 := by
        symm
        apply Finset.sum_subset Finset.subset_union_right
        intro z hzU hzS₃₁
        have hzNot : z - j ∉ differenceBinsOf f₃ f₁ := by
          intro hz
          apply hzS₃₁
          exact Finset.mem_image.mpr ⟨z - j, hz, by omega⟩
        have hz0 : differenceCountOf f₃ f₁ (z - j) = 0 :=
          differenceCountOf_eq_zero_of_not_mem hzNot
        norm_num [G, hz0]
      _ = ∑ z ∈ differenceBinsOf f₃ f₁,
          (differenceCountOf f₃ f₁ z : ℝ) ^ 2 := hImage
      _ = (differenceSquareSumOf f₃ f₁ : ℝ) := by
        simp only [differenceSquareSumOf, Nat.cast_sum, Nat.cast_pow]
  rw [hCorr]
  calc
    (∑ z ∈ U, F z * G z) ^ 2 ≤
        (∑ z ∈ U, F z ^ 2) * (∑ z ∈ U, G z ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq U F G
    _ = (differenceSquareSumOf f₀ f₂ : ℝ) *
        (differenceSquareSumOf f₃ f₁ : ℝ) := by rw [hFSq, hGSq]

private theorem two_mul_le_add_of_sq_le_mul
    {x a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : x ^ 2 ≤ a * b) : 2 * x ≤ a + b := by
  nlinarith [sq_nonneg (a - b)]

private theorem four_mul_exactMixedShiftCountOf_le_sum_self
    {ι₀ ι₁ ι₂ ι₃ : Type*}
    [Fintype ι₀] [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    (j : ℤ) (f₀ : ι₀ → ℤ) (f₁ : ι₁ → ℤ)
    (f₂ : ι₂ → ℤ) (f₃ : ι₃ → ℤ) :
    4 * (exactMixedShiftCountOf j f₀ f₁ f₂ f₃ : ℝ) ≤
      (differenceSquareSumOf f₀ f₀ : ℝ) +
        (differenceSquareSumOf f₁ f₁ : ℝ) +
        (differenceSquareSumOf f₂ f₂ : ℝ) +
        (differenceSquareSumOf f₃ f₃ : ℝ) := by
  have hMixed := sq_exactMixedShiftCountOf_le_cross j f₀ f₁ f₂ f₃
  have h₀₂ := sq_crossExactEnergyOf_le_mul_self f₀ f₂
  have h₃₁ := sq_crossExactEnergyOf_le_mul_self f₃ f₁
  rw [← differenceSquareSumOf_eq_crossExactEnergyOf] at h₀₂ h₃₁
  have hMixedLinear :
      2 * (exactMixedShiftCountOf j f₀ f₁ f₂ f₃ : ℝ) ≤
        (differenceSquareSumOf f₀ f₂ : ℝ) +
          (differenceSquareSumOf f₃ f₁ : ℝ) :=
    two_mul_le_add_of_sq_le_mul (Nat.cast_nonneg _) (Nat.cast_nonneg _) hMixed
  have h₀₂Linear :
      2 * (differenceSquareSumOf f₀ f₂ : ℝ) ≤
        (differenceSquareSumOf f₀ f₀ : ℝ) +
          (differenceSquareSumOf f₂ f₂ : ℝ) :=
    two_mul_le_add_of_sq_le_mul (Nat.cast_nonneg _) (Nat.cast_nonneg _) h₀₂
  have h₃₁Linear :
      2 * (differenceSquareSumOf f₃ f₁ : ℝ) ≤
        (differenceSquareSumOf f₃ f₃ : ℝ) +
          (differenceSquareSumOf f₁ f₁ : ℝ) :=
    two_mul_le_add_of_sq_le_mul (Nat.cast_nonneg _) (Nat.cast_nonneg _) h₃₁
  linarith

private noncomputable def doubleFloorOf
    {ι : Type*} (W : ι → ℝ) (i : ι) : ℤ := ⌊2 * W i⌋

private theorem differenceSquareSumOf_doubleFloor_le_energy
    {ι : Type*} [Fintype ι] (W : ι → ℝ) :
    differenceSquareSumOf (doubleFloorOf W) (doubleFloorOf W) ≤
      approximateAdditiveEnergyOf 1 W := by
  classical
  rw [differenceSquareSumOf_eq_crossExactEnergyOf]
  unfold crossExactEnergyOf approximateAdditiveEnergyOf
  let reorder : ((ι × ι) × (ι × ι)) ≃ AdditiveQuadrupleOf ι :=
    { toFun := fun q => ![q.1.1, q.2.2, q.2.1, q.1.2]
      invFun := fun q => ((q 0, q 3), (q 2, q 1))
      left_inv := by rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl
      right_inv := by intro q; funext i; fin_cases i <;> rfl }
  apply Finset.card_le_card_of_injOn reorder
  · intro q hq
    rcases q with ⟨⟨a, b⟩, ⟨c, d⟩⟩
    have hq' : doubleFloorOf W a + doubleFloorOf W d =
        doubleFloorOf W c + doubleFloorOf W b := by simpa using hq
    have htarget : |W a + W d - W c - W b| ≤ 1 := by
      change ⌊2 * W a⌋ + ⌊2 * W d⌋ =
        ⌊2 * W c⌋ + ⌊2 * W b⌋ at hq'
      have hal := Int.floor_le (2 * W a)
      have hau := Int.lt_floor_add_one (2 * W a)
      have hbl := Int.floor_le (2 * W b)
      have hbu := Int.lt_floor_add_one (2 * W b)
      have hcl := Int.floor_le (2 * W c)
      have hcu := Int.lt_floor_add_one (2 * W c)
      have hdl := Int.floor_le (2 * W d)
      have hdu := Int.lt_floor_add_one (2 * W d)
      have heqReal : (⌊2 * W a⌋ : ℝ) + ⌊2 * W d⌋ =
          ⌊2 * W c⌋ + ⌊2 * W b⌋ := by exact_mod_cast hq'
      rw [abs_le]
      constructor <;> linarith
    simpa [reorder] using htarget
  · intro q hq q' hq' heq
    exact reorder.injective heq

/-- Four-family indexed mixed energy is bounded by the sum of the four
self-energies.  The explicit factor `9` comes from the possible doubled-floor
defects at tolerance one.  No separation or injectivity hypothesis is used. -/
theorem four_mul_mixedApproximateAdditiveEnergyOf_le_nine_mul_sum_self
    {ι₀ ι₁ ι₂ ι₃ : Type*}
    [Fintype ι₀] [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    (W₀ : ι₀ → ℝ) (W₁ : ι₁ → ℝ) (W₂ : ι₂ → ℝ) (W₃ : ι₃ → ℝ) :
    4 * (mixedApproximateAdditiveEnergyOf 1 W₀ W₁ W₂ W₃ : ℝ) ≤
      9 * ((approximateAdditiveEnergyOf 1 W₀ : ℝ) +
        (approximateAdditiveEnergyOf 1 W₁ : ℝ) +
        (approximateAdditiveEnergyOf 1 W₂ : ℝ) +
        (approximateAdditiveEnergyOf 1 W₃ : ℝ)) := by
  classical
  let good : Finset (MixedAdditiveQuadrupleOf ι₀ ι₁ ι₂ ι₃) :=
    (Finset.univ.filter fun q =>
      |W₀ q.1.1 + W₁ q.1.2 - W₂ q.2.1 - W₃ q.2.2| ≤ 1)
  let defect : MixedAdditiveQuadrupleOf ι₀ ι₁ ι₂ ι₃ → ℤ := fun q =>
    doubleFloorOf W₀ q.1.1 + doubleFloorOf W₁ q.1.2 -
      doubleFloorOf W₂ q.2.1 - doubleFloorOf W₃ q.2.2
  let defects : Finset ℤ := good.image defect
  have hdefect_mem (q) (hq : q ∈ good) : defect q ∈ Finset.Icc (-4 : ℤ) 4 := by
    have hgood : |W₀ q.1.1 + W₁ q.1.2 - W₂ q.2.1 - W₃ q.2.2| ≤ 1 := by
      simpa only [good, Finset.mem_filter, Finset.mem_univ, true_and] using hq
    have h0l := Int.floor_le (2 * W₀ q.1.1)
    have h0u := Int.lt_floor_add_one (2 * W₀ q.1.1)
    have h1l := Int.floor_le (2 * W₁ q.1.2)
    have h1u := Int.lt_floor_add_one (2 * W₁ q.1.2)
    have h2l := Int.floor_le (2 * W₂ q.2.1)
    have h2u := Int.lt_floor_add_one (2 * W₂ q.2.1)
    have h3l := Int.floor_le (2 * W₃ q.2.2)
    have h3u := Int.lt_floor_add_one (2 * W₃ q.2.2)
    rw [abs_le] at hgood
    rw [Finset.mem_Icc]
    change (-4 : ℤ) ≤ defect q ∧ defect q ≤ 4
    have hreal : (-4 : ℝ) ≤ (defect q : ℤ) ∧
        ((defect q : ℤ) : ℝ) ≤ 4 := by
      dsimp only [defect, doubleFloorOf]
      push_cast
      change (-4 : ℝ) ≤
          (⌊2 * W₀ q.1.1⌋ : ℝ) + ⌊2 * W₁ q.1.2⌋ -
            ⌊2 * W₂ q.2.1⌋ - ⌊2 * W₃ q.2.2⌋ ∧
        (⌊2 * W₀ q.1.1⌋ : ℝ) + ⌊2 * W₁ q.1.2⌋ -
            ⌊2 * W₂ q.2.1⌋ - ⌊2 * W₃ q.2.2⌋ ≤ 4
      constructor <;> linarith
    exact ⟨by exact_mod_cast hreal.1, by exact_mod_cast hreal.2⟩
  have hdefects : defects ⊆ Finset.Icc (-4 : ℤ) 4 := by
    intro j hj
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
    exact hdefect_mem q hq
  have hcardDefects : defects.card ≤ 9 := by
    calc
      defects.card ≤ (Finset.Icc (-4 : ℤ) 4).card := Finset.card_le_card hdefects
      _ = 9 := by
        rw [Int.card_Icc]
        rfl
  have hfiber (j : ℤ) :
      (good.filter fun q => defect q = j).card ≤
        exactMixedShiftCountOf j (doubleFloorOf W₀) (doubleFloorOf W₁)
          (doubleFloorOf W₂) (doubleFloorOf W₃) := by
    apply Finset.card_le_card
    intro q hq
    rw [Finset.mem_filter] at hq ⊢
    exact ⟨Finset.mem_univ _, hq.2⟩
  have hpartition : good.card =
      ∑ j ∈ defects, (good.filter fun q => defect q = j).card := by
    exact Finset.card_eq_sum_card_fiberwise
      (fun q hq => Finset.mem_image.mpr ⟨q, hq, rfl⟩)
  let S : ℝ :=
    (approximateAdditiveEnergyOf 1 W₀ : ℝ) +
      (approximateAdditiveEnergyOf 1 W₁ : ℝ) +
      (approximateAdditiveEnergyOf 1 W₂ : ℝ) +
      (approximateAdditiveEnergyOf 1 W₃ : ℝ)
  have hEach (j : ℤ) :
      4 * ((good.filter fun q => defect q = j).card : ℝ) ≤ S := by
    have hfiberReal : ((good.filter fun q => defect q = j).card : ℝ) ≤
        exactMixedShiftCountOf j (doubleFloorOf W₀) (doubleFloorOf W₁)
          (doubleFloorOf W₂) (doubleFloorOf W₃) := by
      exact_mod_cast hfiber j
    have hExact := four_mul_exactMixedShiftCountOf_le_sum_self j
      (doubleFloorOf W₀) (doubleFloorOf W₁)
      (doubleFloorOf W₂) (doubleFloorOf W₃)
    have h0 : (differenceSquareSumOf (doubleFloorOf W₀)
        (doubleFloorOf W₀) : ℝ) ≤ approximateAdditiveEnergyOf 1 W₀ := by
      exact_mod_cast differenceSquareSumOf_doubleFloor_le_energy W₀
    have h1 : (differenceSquareSumOf (doubleFloorOf W₁)
        (doubleFloorOf W₁) : ℝ) ≤ approximateAdditiveEnergyOf 1 W₁ := by
      exact_mod_cast differenceSquareSumOf_doubleFloor_le_energy W₁
    have h2 : (differenceSquareSumOf (doubleFloorOf W₂)
        (doubleFloorOf W₂) : ℝ) ≤ approximateAdditiveEnergyOf 1 W₂ := by
      exact_mod_cast differenceSquareSumOf_doubleFloor_le_energy W₂
    have h3 : (differenceSquareSumOf (doubleFloorOf W₃)
        (doubleFloorOf W₃) : ℝ) ≤ approximateAdditiveEnergyOf 1 W₃ := by
      exact_mod_cast differenceSquareSumOf_doubleFloor_le_energy W₃
    dsimp only [S]
    linarith
  change 4 * (good.card : ℝ) ≤ 9 * S
  rw [hpartition, Nat.cast_sum]
  calc
    4 * ∑ j ∈ defects, ((good.filter fun q => defect q = j).card : ℝ) =
        ∑ j ∈ defects,
          4 * ((good.filter fun q => defect q = j).card : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ _j ∈ defects, S := Finset.sum_le_sum fun j _ => hEach j
    _ = (defects.card : ℝ) * S := by simp
    _ ≤ 9 * S := by
      gcongr
      exact_mod_cast hcardDefects

/-- The indexed subfamily of points carrying a specified finite color. -/
abbrev EnergyColorFiber
    {ι κ : Type*} (color : ι → κ) (k : κ) := {i : ι // color i = k}

private theorem colored_quadruple_fiber_card_le_mixed
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (W : ι → ℝ) (color : ι → κ) (label : Fin 4 → κ) :
    ((Finset.univ : Finset (AdditiveQuadrupleOf ι)).filter fun q =>
      |W (q 0) + W (q 1) - W (q 2) - W (q 3)| ≤ 1 ∧
        (fun i => color (q i)) = label).card ≤
      mixedApproximateAdditiveEnergyOf 1
        (fun x : EnergyColorFiber color (label 0) => W x.1)
        (fun x : EnergyColorFiber color (label 1) => W x.1)
        (fun x : EnergyColorFiber color (label 2) => W x.1)
        (fun x : EnergyColorFiber color (label 3) => W x.1) := by
  classical
  let fiber : Finset (AdditiveQuadrupleOf ι) :=
    (Finset.univ.filter fun q =>
      |W (q 0) + W (q 1) - W (q 2) - W (q 3)| ≤ 1 ∧
        (fun i => color (q i)) = label)
  let embed : ↥fiber →
      MixedAdditiveQuadrupleOf
        (EnergyColorFiber color (label 0))
        (EnergyColorFiber color (label 1))
        (EnergyColorFiber color (label 2))
        (EnergyColorFiber color (label 3)) := fun q =>
    let hcolors : ∀ i, color (q.1 i) = label i :=
      fun i => congrFun (Finset.mem_filter.mp q.2).2.2 i
    ((⟨q.1 0, hcolors 0⟩, ⟨q.1 1, hcolors 1⟩),
      (⟨q.1 2, hcolors 2⟩, ⟨q.1 3, hcolors 3⟩))
  have hinj : Function.Injective embed := by
    intro q r hqr
    apply Subtype.ext
    funext i
    fin_cases i
    · exact congrArg (fun z => z.1.1.1) hqr
    · exact congrArg (fun z => z.1.2.1) hqr
    · exact congrArg (fun z => z.2.1.1) hqr
    · exact congrArg (fun z => z.2.2.1) hqr
  let mixedGood : Finset
      (MixedAdditiveQuadrupleOf
        (EnergyColorFiber color (label 0))
        (EnergyColorFiber color (label 1))
        (EnergyColorFiber color (label 2))
        (EnergyColorFiber color (label 3))) :=
    Finset.univ.filter fun q =>
      |W q.1.1.1 + W q.1.2.1 - W q.2.1.1 - W q.2.2.1| ≤ 1
  have hsubset : (Finset.univ.image embed) ⊆ mixedGood := by
    intro z hz
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
    have henergy := (Finset.mem_filter.mp q.2).2.1
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, henergy⟩
  change fiber.card ≤ mixedGood.card
  calc
    fiber.card = (Finset.univ.image embed).card := by
      rw [Finset.card_image_iff.mpr]
      · simp
      · intro q hq r hr hqr
        exact hinj hqr
    _ ≤ mixedGood.card := Finset.card_le_card hsubset

/-- Finite coloring may be performed simultaneously on all four coordinates
of every additive relation.  After the mixed-to-self comparison, the full
indexed energy is controlled by four monochromatic self-energies with only a
fourth-power loss in the number of colors. -/
theorem exists_energy_color_classes
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (W : ι → ℝ) (color : ι → κ) :
    ∃ label : Fin 4 → κ,
      let Wᵢ := fun i : Fin 4 =>
        fun x : EnergyColorFiber color (label i) => W x.1
      4 * (approximateAdditiveEnergyOf 1 W : ℝ) ≤
        9 * (Fintype.card κ : ℝ) ^ 4 *
          ((approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
            (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
            (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
            (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ)) := by
  classical
  let good : Finset (AdditiveQuadrupleOf ι) :=
    Finset.univ.filter fun q =>
      |W (q 0) + W (q 1) - W (q 2) - W (q 3)| ≤ 1
  let colorQ : AdditiveQuadrupleOf ι → Fin 4 → κ :=
    fun q i => color (q i)
  by_cases hgood : good.Nonempty
  · obtain ⟨label, hlabelMem, hlabel⟩ :=
      RiemannZeta.GuthMaynard.weighted_finite_pigeonhole good
        (Finset.univ : Finset (Fin 4 → κ)) (fun _ => 1) colorQ hgood
        (fun q hq => Finset.mem_univ _)
    refine ⟨label, ?_⟩
    let fiber := good.filter fun q => colorQ q = label
    let Wᵢ := fun i : Fin 4 =>
      fun x : EnergyColorFiber color (label i) => W x.1
    have hcolorNat : good.card ≤ (Fintype.card κ) ^ 4 * fiber.card := by
      simpa only [Finset.sum_const_zero, Finset.sum_const, Nat.nsmul_eq_mul,
        Nat.mul_one, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        Nat.reducePow, one_mul, colorQ, fiber] using hlabel
    have hcolor : (good.card : ℝ) ≤
        (Fintype.card κ : ℝ) ^ 4 * (fiber.card : ℝ) := by
      exact_mod_cast hcolorNat
    have hfiberNat : fiber.card ≤
        mixedApproximateAdditiveEnergyOf 1 (Wᵢ 0) (Wᵢ 1) (Wᵢ 2) (Wᵢ 3) := by
      change (good.filter fun q => colorQ q = label).card ≤ _
      simpa only [good, colorQ, Finset.filter_filter, and_assoc] using
        (colored_quadruple_fiber_card_le_mixed W color label)
    have hfiber : (fiber.card : ℝ) ≤
        mixedApproximateAdditiveEnergyOf 1 (Wᵢ 0) (Wᵢ 1) (Wᵢ 2) (Wᵢ 3) := by
      exact_mod_cast hfiberNat
    have hmixed :=
      four_mul_mixedApproximateAdditiveEnergyOf_le_nine_mul_sum_self
        (Wᵢ 0) (Wᵢ 1) (Wᵢ 2) (Wᵢ 3)
    change 4 * (good.card : ℝ) ≤ _
    calc
      4 * (good.card : ℝ) ≤
          4 * ((Fintype.card κ : ℝ) ^ 4 * (fiber.card : ℝ)) := by gcongr
      _ ≤ 4 * ((Fintype.card κ : ℝ) ^ 4 *
          mixedApproximateAdditiveEnergyOf 1
            (Wᵢ 0) (Wᵢ 1) (Wᵢ 2) (Wᵢ 3)) := by gcongr
      _ = (Fintype.card κ : ℝ) ^ 4 *
          (4 * mixedApproximateAdditiveEnergyOf 1
            (Wᵢ 0) (Wᵢ 1) (Wᵢ 2) (Wᵢ 3)) := by ring
      _ ≤ (Fintype.card κ : ℝ) ^ 4 *
          (9 * ((approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
            (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
            (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
            (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ))) := by gcongr
      _ = 9 * (Fintype.card κ : ℝ) ^ 4 *
          ((approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
            (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
            (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
            (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ)) := by ring
  · let label : Fin 4 → κ := fun _ => Classical.choice inferInstance
    refine ⟨label, ?_⟩
    have hempty : good = ∅ := Finset.not_nonempty_iff_eq_empty.mp hgood
    have henergy : approximateAdditiveEnergyOf 1 W = 0 := by
      change good.card = 0
      simp [hempty]
    rw [henergy]
    norm_num
    positivity

end

end TaoTrudgianYang2025
