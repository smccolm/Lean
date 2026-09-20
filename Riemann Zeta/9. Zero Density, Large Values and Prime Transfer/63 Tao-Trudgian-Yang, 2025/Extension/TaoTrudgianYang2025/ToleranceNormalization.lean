import TaoTrudgianYang2025.AdditiveEnergy

/-!
# Tolerance normalization for indexed additive energy

This module compares additive energy at an arbitrary real tolerance with the
paper's unit-tolerance energy.  The proof bins pair sums into unit intervals
and keeps the original finite index type throughout, so repeated values remain
distinct and analytic multiplicity is preserved.
-/

namespace TaoTrudgianYang2025

private noncomputable def closePairCount
    {α : Type*} [Fintype α] (r : ℝ) (f : α → ℝ) : ℕ :=
  ((Finset.univ : Finset (α × α)).filter fun p => |f p.1 - f p.2| ≤ r).card

private noncomputable def energyBin {α : Type*} (f : α → ℝ) (x : α) : ℤ :=
  ⌊f x⌋

private theorem floor_distance_le_natCeil_add_one
    {x y R : ℝ} (hxy : |x - y| ≤ R) :
    |⌊x⌋ - ⌊y⌋| ≤ (Nat.ceil R : ℤ) + 1 := by
  rw [abs_le] at hxy ⊢
  have hceil : R ≤ (Nat.ceil R : ℝ) := Nat.le_ceil R
  have hyFloor : y ≤ (⌊y⌋ : ℝ) + 1 := (Int.lt_floor_add_one y).le
  have hxFloor : x ≤ (⌊x⌋ : ℝ) + 1 := (Int.lt_floor_add_one x).le
  constructor
  · have hreal : -((Nat.ceil R : ℝ) + 1) ≤ (⌊x⌋ : ℝ) - ⌊y⌋ := by
      have hfloorY : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
      linarith
    exact_mod_cast hreal
  · have hreal : (⌊x⌋ : ℝ) - ⌊y⌋ ≤ (Nat.ceil R : ℝ) + 1 := by
      have hfloorX : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
      linarith
    exact_mod_cast hreal

private theorem sameBin_card_eq_sum_mass_sq
    {α : Type*} [Fintype α] (f : α → ℝ) :
    ((Finset.univ : Finset (α × α)).filter fun p =>
        energyBin f p.1 = energyBin f p.2).card =
      ∑ k ∈ (Finset.univ : Finset α).image (energyBin f),
        (((Finset.univ : Finset α).filter fun x =>
          energyBin f x = k).card ^ 2) := by
  classical
  let B : Finset ℤ := (Finset.univ : Finset α).image (energyBin f)
  let mass : ℤ → ℕ := fun k =>
    ((Finset.univ : Finset α).filter fun x => energyBin f x = k).card
  let same : Finset (α × α) :=
    (Finset.univ : Finset (α × α)).filter fun p =>
      energyBin f p.1 = energyBin f p.2
  have hmaps : Set.MapsTo (fun p : α × α => energyBin f p.1)
      (↑same) (↑B) := by
    intro p hp
    exact Finset.mem_image.mpr ⟨p.1, Finset.mem_univ _, rfl⟩
  rw [show ((Finset.univ : Finset (α × α)).filter fun p =>
      energyBin f p.1 = energyBin f p.2) = same by rfl]
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro k hk
  change (same.filter fun p => energyBin f p.1 = k).card = mass k ^ 2
  let fiber : Finset α :=
    (Finset.univ : Finset α).filter fun x => energyBin f x = k
  have heq : same.filter (fun p => energyBin f p.1 = k) =
      fiber ×ˢ fiber := by
    ext p
    simp only [same, fiber, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product]
    constructor
    · rintro ⟨hEq, hFirst⟩
      exact ⟨hFirst, hEq.symm.trans hFirst⟩
    · rintro ⟨hFirst, hSecond⟩
      exact ⟨hFirst.trans hSecond.symm, hFirst⟩
  rw [heq, Finset.card_product]
  simp [fiber, mass, pow_two]

private theorem sum_mass_sq_le_closePairCount_one
    {α : Type*} [Fintype α] (f : α → ℝ) :
    (∑ k ∈ (Finset.univ : Finset α).image (energyBin f),
        (((Finset.univ : Finset α).filter fun x =>
          energyBin f x = k).card ^ 2)) ≤ closePairCount 1 f := by
  classical
  rw [← sameBin_card_eq_sum_mass_sq f]
  apply Finset.card_le_card
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  have hleft : (⌊f p.1⌋ : ℝ) ≤ f p.1 := Int.floor_le _
  have hleft' : f p.1 < (⌊f p.1⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hright : (⌊f p.2⌋ : ℝ) ≤ f p.2 := Int.floor_le _
  have hright' : f p.2 < (⌊f p.2⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  rw [show ⌊f p.1⌋ = ⌊f p.2⌋ from hp.2] at hleft hleft'
  rw [abs_le]
  constructor <;> linarith

private theorem int_neighbor_card_le (k : ℤ) (n : ℕ) (B : Finset ℤ) :
    (B.filter fun l => |k - l| ≤ (n : ℤ)).card ≤ 2 * n + 1 := by
  have hsubset : B.filter (fun l => |k - l| ≤ (n : ℤ)) ⊆
      Finset.Icc (k - n) (k + n) := by
    intro l hl
    rw [Finset.mem_filter] at hl
    rw [Finset.mem_Icc]
    rw [abs_le] at hl
    constructor <;> omega
  calc
    (B.filter fun l => |k - l| ≤ (n : ℤ)).card ≤
        (Finset.Icc (k - n) (k + n)).card := Finset.card_le_card hsubset
    _ = 2 * n + 1 := by
      rw [Int.card_Icc]
      have heq : k + (n : ℤ) + 1 - (k - (n : ℤ)) =
          ((2 * n + 1 : ℕ) : ℤ) := by
        push_cast
        ring
      rw [heq]
      have hn : (0 : ℤ) ≤ 2 * (n : ℤ) + 1 := by positivity
      omega

private theorem mul_le_sq_add_sq (a b : ℕ) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with hab | hba
  · calc
      a * b ≤ b * b := Nat.mul_le_mul_right b hab
      _ ≤ a ^ 2 + b ^ 2 := by simp [pow_two]
  · calc
      a * b ≤ a * a := Nat.mul_le_mul_left a hba
      _ ≤ a ^ 2 + b ^ 2 := by simp [pow_two]

private theorem closePairCount_le_natCeil_mul_closePairCount_one
    {α : Type*} [Fintype α] (R : ℝ) (f : α → ℝ) :
    closePairCount R f ≤ (4 * Nat.ceil R + 6) * closePairCount 1 f := by
  classical
  let B : Finset ℤ := (Finset.univ : Finset α).image (energyBin f)
  let mass : ℤ → ℕ := fun k =>
    ((Finset.univ : Finset α).filter fun x => energyBin f x = k).card
  let L : ℕ := Nat.ceil R + 1
  let good : Finset (α × α) :=
    (Finset.univ : Finset (α × α)).filter fun p => |f p.1 - f p.2| ≤ R
  let tag : α × α → ℤ × ℤ := fun p =>
    (energyBin f p.1, energyBin f p.2)
  let near : Finset (ℤ × ℤ) :=
    (B ×ˢ B).filter fun kl => |kl.1 - kl.2| ≤ (L : ℤ)
  have hmaps : Set.MapsTo tag (↑good) (↑(B ×ˢ B)) := by
    intro p hp
    change tag p ∈ B ×ˢ B
    rw [Finset.mem_product]
    exact ⟨Finset.mem_image.mpr ⟨p.1, Finset.mem_univ _, rfl⟩,
      Finset.mem_image.mpr ⟨p.2, Finset.mem_univ _, rfl⟩⟩
  have hfiber (kl : ℤ × ℤ) (hkl : kl ∈ B ×ˢ B) :
      (good.filter fun p => tag p = kl).card ≤
        if |kl.1 - kl.2| ≤ (L : ℤ) then
          mass kl.1 * mass kl.2 else 0 := by
    split_ifs with hnear
    · have hsubset : good.filter (fun p => tag p = kl) ⊆
          ((Finset.univ : Finset α).filter fun x => energyBin f x = kl.1) ×ˢ
            ((Finset.univ : Finset α).filter fun x =>
              energyBin f x = kl.2) := by
        intro p hp
        rw [Finset.mem_filter] at hp
        have htag := hp.2
        rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
        exact ⟨⟨Finset.mem_univ _, congrArg Prod.fst htag⟩,
          ⟨Finset.mem_univ _, congrArg Prod.snd htag⟩⟩
      calc
        (good.filter fun p => tag p = kl).card ≤
            (((Finset.univ : Finset α).filter fun x =>
                energyBin f x = kl.1) ×ˢ
              ((Finset.univ : Finset α).filter fun x =>
                energyBin f x = kl.2)).card := Finset.card_le_card hsubset
        _ = mass kl.1 * mass kl.2 := by rw [Finset.card_product]
    · have hempty : good.filter (fun p => tag p = kl) = ∅ := by
        ext p
        constructor
        · intro hp
          rw [Finset.mem_filter] at hp
          have hgood := (Finset.mem_filter.mp hp.1).2
          have hdist := floor_distance_le_natCeil_add_one hgood
          have h0 : energyBin f p.1 = kl.1 := congrArg Prod.fst hp.2
          have h1 : energyBin f p.2 = kl.2 := congrArg Prod.snd hp.2
          change ⌊f p.1⌋ = kl.1 at h0
          change ⌊f p.2⌋ = kl.2 at h1
          rw [h0, h1] at hdist
          exact (hnear (by simpa [L] using hdist)).elim
        · intro hp
          simp at hp
      rw [hempty]
      simp
  have hgoodUpper : good.card ≤
      ∑ kl ∈ near, mass kl.1 * mass kl.2 := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    calc
      (∑ kl ∈ B ×ˢ B, (good.filter fun p => tag p = kl).card) ≤
          ∑ kl ∈ B ×ˢ B,
            if |kl.1 - kl.2| ≤ (L : ℤ) then
              mass kl.1 * mass kl.2 else 0 := by
        exact Finset.sum_le_sum fun kl hkl => hfiber kl hkl
      _ = ∑ kl ∈ near, mass kl.1 * mass kl.2 := by
        simp [near, Finset.sum_filter]
  have hmulUpper :
      (∑ kl ∈ near, mass kl.1 * mass kl.2) ≤
        ∑ kl ∈ near, (mass kl.1 ^ 2 + mass kl.2 ^ 2) := by
    exact Finset.sum_le_sum fun kl _ => mul_le_sq_add_sq _ _
  have hswap :
      (∑ kl ∈ near, mass kl.2 ^ 2) =
        ∑ kl ∈ near, mass kl.1 ^ 2 := by
    refine Finset.sum_equiv (Equiv.prodComm ℤ ℤ) ?_ ?_
    · intro kl
      rw [Finset.mem_filter, Finset.mem_filter]
      rw [Finset.mem_product, Finset.mem_product]
      constructor
      · rintro ⟨⟨hk, hl⟩, hdist⟩
        exact ⟨⟨hl, hk⟩, by simpa [abs_sub_comm] using hdist⟩
      · rintro ⟨⟨hl, hk⟩, hdist⟩
        exact ⟨⟨hk, hl⟩, by simpa [abs_sub_comm] using hdist⟩
    · intro kl hkl
      rfl
  have hfirst :
      (∑ kl ∈ near, mass kl.1 ^ 2) ≤
        (2 * L + 1) * ∑ k ∈ B, mass k ^ 2 := by
    calc
      (∑ kl ∈ near, mass kl.1 ^ 2) =
          ∑ k ∈ B, ∑ l ∈ B,
            if |k - l| ≤ (L : ℤ) then mass k ^ 2 else 0 := by
        simp [near, Finset.sum_filter, Finset.sum_product]
      _ = ∑ k ∈ B,
          ∑ l ∈ B.filter (fun l => |k - l| ≤ (L : ℤ)),
            mass k ^ 2 := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.sum_filter]
      _ = ∑ k ∈ B,
          (B.filter (fun l => |k - l| ≤ (L : ℤ))).card *
            mass k ^ 2 := by
        apply Finset.sum_congr rfl
        intro k hk
        simp
      _ ≤ ∑ k ∈ B, (2 * L + 1) * mass k ^ 2 := by
        apply Finset.sum_le_sum
        intro k hk
        gcongr
        exact int_neighbor_card_le k L B
      _ = (2 * L + 1) * ∑ k ∈ B, mass k ^ 2 := by
        rw [Finset.mul_sum]
  have hsquares :
      (∑ kl ∈ near, (mass kl.1 ^ 2 + mass kl.2 ^ 2)) ≤
        (4 * Nat.ceil R + 6) * ∑ k ∈ B, mass k ^ 2 := by
    rw [Finset.sum_add_distrib, hswap]
    calc
      (∑ kl ∈ near, mass kl.1 ^ 2) +
          ∑ kl ∈ near, mass kl.1 ^ 2 ≤
          2 * ((2 * L + 1) * ∑ k ∈ B, mass k ^ 2) := by
        omega
      _ = (4 * Nat.ceil R + 6) * ∑ k ∈ B, mass k ^ 2 := by
        simp [L]
        ring
  calc
    closePairCount R f = good.card := rfl
    _ ≤ ∑ kl ∈ near, mass kl.1 * mass kl.2 := hgoodUpper
    _ ≤ ∑ kl ∈ near, (mass kl.1 ^ 2 + mass kl.2 ^ 2) := hmulUpper
    _ ≤ (4 * Nat.ceil R + 6) * ∑ k ∈ B, mass k ^ 2 := hsquares
    _ ≤ (4 * Nat.ceil R + 6) * closePairCount 1 f := by
      gcongr
      exact sum_mass_sq_le_closePairCount_one f

private def quadEquivPairPair (ι : Type*) :
    AdditiveQuadrupleOf ι ≃ (ι × ι) × (ι × ι) where
  toFun q := ((q 0, q 1), (q 2, q 3))
  invFun p := ![p.1.1, p.1.2, p.2.1, p.2.2]
  left_inv q := by
    funext j
    fin_cases j <;> rfl
  right_inv p := by
    rcases p with ⟨⟨a, b⟩, ⟨c, d⟩⟩
    rfl

private theorem approximateAdditiveEnergyOf_eq_closePairCount
    {ι : Type*} [Fintype ι] (r : ℝ) (W : ι → ℝ) :
    approximateAdditiveEnergyOf r W =
      closePairCount r (fun p : ι × ι => W p.1 + W p.2) := by
  classical
  unfold approximateAdditiveEnergyOf closePairCount
  apply Finset.card_equiv (quadEquivPairPair ι)
  intro q
  simp [quadEquivPairPair]
  ring_nf

/-- Arbitrary-tolerance indexed additive energy is bounded by an explicit
linear factor times unit-tolerance energy.  No separation or injectivity of
the indexed family is required. -/
theorem approximateAdditiveEnergyOf_le_natCeil_mul_unit
    {ι : Type*} [Fintype ι] (R : ℝ) (W : ι → ℝ) :
    approximateAdditiveEnergyOf R W ≤
      (4 * Nat.ceil R + 6) * approximateAdditiveEnergyOf 1 W := by
  rw [approximateAdditiveEnergyOf_eq_closePairCount,
    approximateAdditiveEnergyOf_eq_closePairCount]
  exact closePairCount_le_natCeil_mul_closePairCount_one R _

end TaoTrudgianYang2025
