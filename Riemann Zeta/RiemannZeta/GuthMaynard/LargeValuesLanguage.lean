import Mathlib.Combinatorics.Additive.Energy
import RiemannZeta.GuthMaynard.LargeValuesDefinitions
import RiemannZeta.GuthMaynard.Separated

open Finset
open scoped BigOperators

namespace RiemannZeta.GuthMaynard

/-!
# Reindexing and floor-bin language for approximate additive energy

This file supplies the finite quantitative language used in Guth--Maynard's
affine and energy arguments.  In particular it connects the source's
tolerance-one real energy with Mathlib's exact additive energy.
-/

/-- Apply a reindexing map to all four entries of an additive quadruple. -/
def mapAdditiveQuadruple {α β : Type*} (f : α → β)
    (q : (α × α) × (α × α)) : (β × β) × (β × β) :=
  ((f q.1.1, f q.1.2), (f q.2.1, f q.2.2))

/-- Translation of a finite real set, with the additive convention used by
the large-values energy argument. -/
noncomputable def gmTranslate (c : ℝ) (W : Finset ℝ) : Finset ℝ :=
  W.image (fun x => x + c)

/-- Scaling of a finite real set. -/
noncomputable def gmScale (a : ℝ) (W : Finset ℝ) : Finset ℝ :=
  W.image (fun x => a * x)

/-- Affine image of a finite real set. -/
noncomputable def gmAffineImage (a b : ℝ) (W : Finset ℝ) : Finset ℝ :=
  W.image (fun x => a * x + b)

theorem mapAdditiveQuadruple_translate_mem (η c : ℝ) (W : Finset ℝ)
    (q : (ℝ × ℝ) × (ℝ × ℝ))
    (hq : q ∈ approximateAdditiveQuadruples η W) :
    mapAdditiveQuadruple (fun x => x + c) q ∈
      approximateAdditiveQuadruples η (gmTranslate c W) := by
  simp only [approximateAdditiveQuadruples, Finset.mem_filter,
    Finset.mem_product] at hq ⊢
  rcases hq with ⟨⟨⟨h1, h2⟩, h3, h4⟩, hd⟩
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · exact Finset.mem_image.mpr ⟨q.1.1, h1, rfl⟩
  · exact Finset.mem_image.mpr ⟨q.1.2, h2, rfl⟩
  · exact Finset.mem_image.mpr ⟨q.2.1, h3, rfl⟩
  · exact Finset.mem_image.mpr ⟨q.2.2, h4, rfl⟩
  · rw [show
      (mapAdditiveQuadruple (fun x => x + c) q).1.1 +
        (mapAdditiveQuadruple (fun x => x + c) q).1.2 -
        (mapAdditiveQuadruple (fun x => x + c) q).2.1 -
        (mapAdditiveQuadruple (fun x => x + c) q).2.2 =
          q.1.1 + q.1.2 - q.2.1 - q.2.2 by
        simp only [mapAdditiveQuadruple]
        ring]
    exact hd

theorem mapAdditiveQuadruple_untranslate_mem (η c : ℝ) (W : Finset ℝ)
    (q : (ℝ × ℝ) × (ℝ × ℝ))
    (hq : q ∈ approximateAdditiveQuadruples η (gmTranslate c W)) :
    mapAdditiveQuadruple (fun x => x - c) q ∈
      approximateAdditiveQuadruples η W := by
  simp only [approximateAdditiveQuadruples, Finset.mem_filter,
    Finset.mem_product] at hq ⊢
  rcases hq with ⟨⟨⟨h1, h2⟩, h3, h4⟩, hd⟩
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · rcases Finset.mem_image.mp h1 with ⟨x, hx, hxeq⟩
    have : q.1.1 - c = x := by linarith
    simpa [mapAdditiveQuadruple, this] using hx
  · rcases Finset.mem_image.mp h2 with ⟨x, hx, hxeq⟩
    have : q.1.2 - c = x := by linarith
    simpa [mapAdditiveQuadruple, this] using hx
  · rcases Finset.mem_image.mp h3 with ⟨x, hx, hxeq⟩
    have : q.2.1 - c = x := by linarith
    simpa [mapAdditiveQuadruple, this] using hx
  · rcases Finset.mem_image.mp h4 with ⟨x, hx, hxeq⟩
    have : q.2.2 - c = x := by linarith
    simpa [mapAdditiveQuadruple, this] using hx
  · rw [show
      (mapAdditiveQuadruple (fun x => x - c) q).1.1 +
        (mapAdditiveQuadruple (fun x => x - c) q).1.2 -
        (mapAdditiveQuadruple (fun x => x - c) q).2.1 -
        (mapAdditiveQuadruple (fun x => x - c) q).2.2 =
          q.1.1 + q.1.2 - q.2.1 - q.2.2 by
        simp only [mapAdditiveQuadruple]
        ring]
    exact hd

/-- Approximate additive energy is translation invariant. -/
theorem approxAddEnergy_translate (η c : ℝ) (W : Finset ℝ) :
    ApproxAddEnergy η (gmTranslate c W) = ApproxAddEnergy η W := by
  apply Nat.le_antisymm
  · unfold ApproxAddEnergy
    apply Finset.card_le_card_of_injOn
      (mapAdditiveQuadruple fun x => x - c)
    · exact mapAdditiveQuadruple_untranslate_mem η c W
    · intro q hq q' hq' heq
      rcases q with ⟨⟨a,b⟩,⟨d,e⟩⟩
      rcases q' with ⟨⟨a',b'⟩,⟨d',e'⟩⟩
      simp only [mapAdditiveQuadruple, Prod.mk.injEq] at heq ⊢
      exact ⟨⟨by linarith [heq.1.1], by linarith [heq.1.2]⟩,
        by linarith [heq.2.1], by linarith [heq.2.2]⟩
  · unfold ApproxAddEnergy
    apply Finset.card_le_card_of_injOn
      (mapAdditiveQuadruple fun x => x + c)
    · exact mapAdditiveQuadruple_translate_mem η c W
    · intro q hq q' hq' heq
      rcases q with ⟨⟨a,b⟩,⟨d,e⟩⟩
      rcases q' with ⟨⟨a',b'⟩,⟨d',e'⟩⟩
      simp only [mapAdditiveQuadruple, Prod.mk.injEq] at heq ⊢
      exact ⟨⟨by linarith [heq.1.1], by linarith [heq.1.2]⟩,
        by linarith [heq.2.1], by linarith [heq.2.2]⟩

theorem mapAdditiveQuadruple_scale_mem (η a : ℝ) (W : Finset ℝ)
    (q : (ℝ × ℝ) × (ℝ × ℝ))
    (hq : q ∈ approximateAdditiveQuadruples η W) :
    mapAdditiveQuadruple (fun x => a * x) q ∈
      approximateAdditiveQuadruples (|a| * η) (gmScale a W) := by
  simp only [approximateAdditiveQuadruples, Finset.mem_filter,
    Finset.mem_product] at hq ⊢
  rcases hq with ⟨⟨⟨h1, h2⟩, h3, h4⟩, hd⟩
  refine ⟨⟨⟨Finset.mem_image.mpr ⟨_, h1, rfl⟩,
    Finset.mem_image.mpr ⟨_, h2, rfl⟩⟩,
    Finset.mem_image.mpr ⟨_, h3, rfl⟩,
    Finset.mem_image.mpr ⟨_, h4, rfl⟩⟩, ?_⟩
  rw [show (mapAdditiveQuadruple (fun x => a * x) q).1.1 +
      (mapAdditiveQuadruple (fun x => a * x) q).1.2 -
      (mapAdditiveQuadruple (fun x => a * x) q).2.1 -
      (mapAdditiveQuadruple (fun x => a * x) q).2.2 =
      a * (q.1.1 + q.1.2 - q.2.1 - q.2.2) by
        simp only [mapAdditiveQuadruple]
        ring,
    abs_mul]
  exact mul_le_mul_of_nonneg_left hd (abs_nonneg a)

theorem mapAdditiveQuadruple_unscale_mem (η a : ℝ) (ha : a ≠ 0)
    (W : Finset ℝ) (q : (ℝ × ℝ) × (ℝ × ℝ))
    (hq : q ∈ approximateAdditiveQuadruples (|a| * η) (gmScale a W)) :
    mapAdditiveQuadruple (fun x => x / a) q ∈
      approximateAdditiveQuadruples η W := by
  simp only [approximateAdditiveQuadruples, Finset.mem_filter,
    Finset.mem_product] at hq ⊢
  rcases hq with ⟨⟨⟨h1, h2⟩, h3, h4⟩, hd⟩
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · rcases Finset.mem_image.mp h1 with ⟨x, hx, hxeq⟩
    have : q.1.1 / a = x := by field_simp; linarith
    simpa [mapAdditiveQuadruple, this] using hx
  · rcases Finset.mem_image.mp h2 with ⟨x, hx, hxeq⟩
    have : q.1.2 / a = x := by field_simp; linarith
    simpa [mapAdditiveQuadruple, this] using hx
  · rcases Finset.mem_image.mp h3 with ⟨x, hx, hxeq⟩
    have : q.2.1 / a = x := by field_simp; linarith
    simpa [mapAdditiveQuadruple, this] using hx
  · rcases Finset.mem_image.mp h4 with ⟨x, hx, hxeq⟩
    have : q.2.2 / a = x := by field_simp; linarith
    simpa [mapAdditiveQuadruple, this] using hx
  · rw [show (mapAdditiveQuadruple (fun x => x / a) q).1.1 +
        (mapAdditiveQuadruple (fun x => x / a) q).1.2 -
        (mapAdditiveQuadruple (fun x => x / a) q).2.1 -
        (mapAdditiveQuadruple (fun x => x / a) q).2.2 =
        (q.1.1 + q.1.2 - q.2.1 - q.2.2) / a by
          simp only [mapAdditiveQuadruple]
          ring,
      abs_div]
    exact (div_le_iff₀ (abs_pos.mpr ha)).mpr (by simpa [mul_comm] using hd)

/-- Scaling by a nonzero factor scales the approximation tolerance by its
absolute value and preserves the energy count. -/
theorem approxAddEnergy_scale (η a : ℝ) (ha : a ≠ 0) (W : Finset ℝ) :
    ApproxAddEnergy (|a| * η) (gmScale a W) = ApproxAddEnergy η W := by
  apply Nat.le_antisymm
  · unfold ApproxAddEnergy
    apply Finset.card_le_card_of_injOn
      (mapAdditiveQuadruple fun x => x / a)
    · exact mapAdditiveQuadruple_unscale_mem η a ha W
    · intro q hq q' hq' heq
      rcases q with ⟨⟨b,c⟩,⟨d,e⟩⟩
      rcases q' with ⟨⟨b',c'⟩,⟨d',e'⟩⟩
      simp only [mapAdditiveQuadruple, Prod.mk.injEq] at heq ⊢
      constructor
      · constructor
        · have h := congrArg (fun x : ℝ => x * a) heq.1.1
          field_simp at h
          exact h
        · have h := congrArg (fun x : ℝ => x * a) heq.1.2
          field_simp at h
          exact h
      · constructor
        · have h := congrArg (fun x : ℝ => x * a) heq.2.1
          field_simp at h
          exact h
        · have h := congrArg (fun x : ℝ => x * a) heq.2.2
          field_simp at h
          exact h
  · unfold ApproxAddEnergy
    apply Finset.card_le_card_of_injOn
      (mapAdditiveQuadruple fun x => a * x)
    · exact mapAdditiveQuadruple_scale_mem η a W
    · intro q hq q' hq' heq
      rcases q with ⟨⟨b,c⟩,⟨d,e⟩⟩
      rcases q' with ⟨⟨b',c'⟩,⟨d',e'⟩⟩
      simp only [mapAdditiveQuadruple, Prod.mk.injEq] at heq ⊢
      exact ⟨⟨mul_left_cancel₀ ha heq.1.1, mul_left_cancel₀ ha heq.1.2⟩,
        mul_left_cancel₀ ha heq.2.1, mul_left_cancel₀ ha heq.2.2⟩

theorem gmAffineImage_eq_translate_scale (a b : ℝ) (W : Finset ℝ) :
    gmAffineImage a b W = gmTranslate b (gmScale a W) := by
  ext y
  constructor
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    exact Finset.mem_image.mpr ⟨a * x,
      Finset.mem_image.mpr ⟨x, hx, rfl⟩, rfl⟩
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

/-- Affine reindexing law for approximate additive energy. -/
theorem approxAddEnergy_affine (η a b : ℝ) (ha : a ≠ 0) (W : Finset ℝ) :
    ApproxAddEnergy (|a| * η) (gmAffineImage a b W) = ApproxAddEnergy η W := by
  rw [gmAffineImage_eq_translate_scale]
  rw [approxAddEnergy_translate, approxAddEnergy_scale η a ha W]

/-- Integer additive defect of the floors of a real quadruple. -/
noncomputable def floorAdditiveDefect
    (q : (ℝ × ℝ) × (ℝ × ℝ)) : ℤ :=
  ⌊q.1.1⌋ + ⌊q.1.2⌋ - ⌊q.2.1⌋ - ⌊q.2.2⌋

/-- Tolerance-one energy restricted to one floor-defect bin. -/
noncomputable def ApproxFloorEnergy (k : ℤ) (W : Finset ℝ) : ℕ :=
  ((approximateAdditiveQuadruples 1 W).filter fun q =>
    floorAdditiveDefect q = k).card

/-- Image of the ordinate set under the integer floor map. -/
noncomputable def floorImage (W : Finset ℝ) : Finset ℤ :=
  W.image Int.floor

theorem floorAdditiveDefect_mem_Icc (W : Finset ℝ)
    (q : (ℝ × ℝ) × (ℝ × ℝ))
    (hq : q ∈ approximateAdditiveQuadruples 1 W) :
    floorAdditiveDefect q ∈ Finset.Icc (-3 : ℤ) 3 := by
  simp only [Finset.mem_Icc]
  simp only [approximateAdditiveQuadruples, Finset.mem_filter] at hq
  rw [abs_le] at hq
  have h11 := Int.floor_le q.1.1
  have h12 := Int.lt_floor_add_one q.1.1
  have h21 := Int.floor_le q.1.2
  have h22 := Int.lt_floor_add_one q.1.2
  have h31 := Int.floor_le q.2.1
  have h32 := Int.lt_floor_add_one q.2.1
  have h41 := Int.floor_le q.2.2
  have h42 := Int.lt_floor_add_one q.2.2
  have hlo : (-3 : ℝ) < (floorAdditiveDefect q : ℝ) := by
    simp only [floorAdditiveDefect, Int.cast_sub, Int.cast_add]
    linarith [hq.2.1]
  have hhi : (floorAdditiveDefect q : ℝ) < 3 := by
    simp only [floorAdditiveDefect, Int.cast_sub, Int.cast_add]
    linarith [hq.2.2]
  constructor
  · exact_mod_cast (le_of_lt hlo)
  · exact_mod_cast (le_of_lt hhi)

/-- Exact seven-bin decomposition of tolerance-one real additive energy. -/
theorem approxAddEnergy_one_eq_sum_floorEnergy (W : Finset ℝ) :
    ApproxAddEnergy 1 W =
      ∑ k ∈ Finset.Icc (-3 : ℤ) 3, ApproxFloorEnergy k W := by
  rw [ApproxAddEnergy]
  change #(approximateAdditiveQuadruples 1 W) =
    ∑ k ∈ Finset.Icc (-3 : ℤ) 3,
      #({q ∈ approximateAdditiveQuadruples 1 W |
        floorAdditiveDefect q = k})
  calc
    #(approximateAdditiveQuadruples 1 W) =
        #({q ∈ approximateAdditiveQuadruples 1 W |
          floorAdditiveDefect q ∈ Finset.Icc (-3 : ℤ) 3}) := by
      congr 1
      ext q
      simp only [Finset.mem_filter]
      constructor
      · intro hq
        exact ⟨hq, floorAdditiveDefect_mem_Icc W q hq⟩
      · exact fun hq => hq.1
    _ = ∑ k ∈ Finset.Icc (-3 : ℤ) 3,
        #({q ∈ approximateAdditiveQuadruples 1 W |
          floorAdditiveDefect q = k}) :=
      (Finset.sum_card_fiberwise_eq_card_filter
        (approximateAdditiveQuadruples 1 W) (Finset.Icc (-3 : ℤ) 3)
        floorAdditiveDefect).symm

theorem floor_injective_on_of_separated (W : Finset ℝ)
    (hW : IsSeparated 1 W) :
    ∀ x ∈ W, ∀ y ∈ W, ⌊x⌋ = ⌊y⌋ → x = y := by
  intro x hx y hy hfloor
  by_contra hxy
  have hsep : 1 ≤ |x - y| := by
    simpa [Real.dist_eq] using hW x hx y hy hxy
  have hxfloor := Int.floor_le x
  have hyfloor := Int.floor_le y
  have hxupper := Int.lt_floor_add_one x
  have hyupper := Int.lt_floor_add_one y
  have hxylt : x - y < 1 := by
    rw [hfloor] at hxupper
    linarith
  have hyxlt : -(1 : ℝ) < x - y := by
    rw [← hfloor] at hyupper
    linarith
  exact (not_lt_of_ge hsep) (abs_lt.mpr ⟨hyxlt, hxylt⟩)

noncomputable def floorAdditiveQuadruple
    (q : (ℝ × ℝ) × (ℝ × ℝ)) : (ℤ × ℤ) × (ℤ × ℤ) :=
  mapAdditiveQuadruple Int.floor q

/-- The zero floor-defect bin injects into Mathlib's exact additive energy
when the original real set is one-separated.  Together with the seven-bin
partition, this is the required floor-bin bridge. -/
theorem approxFloorEnergy_zero_le_addEnergy (W : Finset ℝ)
    (hW : IsSeparated 1 W) :
    ApproxFloorEnergy 0 W ≤ Finset.addEnergy (floorImage W) (floorImage W) := by
  rw [Finset.addEnergy_eq_card_filter]
  unfold ApproxFloorEnergy
  apply Finset.card_le_card_of_injOn floorAdditiveQuadruple
  · intro q hq
    change q ∈ ((approximateAdditiveQuadruples 1 W).filter fun q =>
      floorAdditiveDefect q = 0) at hq
    change floorAdditiveQuadruple q ∈
      (((floorImage W ×ˢ floorImage W) ×ˢ
        (floorImage W ×ˢ floorImage W)).filter fun x =>
          x.1.1 + x.1.2 = x.2.1 + x.2.2)
    simp only [Finset.mem_filter, approximateAdditiveQuadruples,
      Finset.mem_product] at hq ⊢
    rcases hq with ⟨⟨⟨⟨h1,h2⟩,h3,h4⟩, hd⟩, hzero⟩
    refine ⟨⟨⟨Finset.mem_image.mpr ⟨_, h1, rfl⟩,
      Finset.mem_image.mpr ⟨_, h2, rfl⟩⟩,
      Finset.mem_image.mpr ⟨_, h3, rfl⟩,
      Finset.mem_image.mpr ⟨_, h4, rfl⟩⟩, ?_⟩
    change ⌊q.1.1⌋ + ⌊q.1.2⌋ - ⌊q.2.1⌋ - ⌊q.2.2⌋ = 0 at hzero
    change ⌊q.1.1⌋ + ⌊q.1.2⌋ = ⌊q.2.1⌋ + ⌊q.2.2⌋
    omega
  · intro q hq q' hq' heq
    change q ∈ ((approximateAdditiveQuadruples 1 W).filter fun q =>
      floorAdditiveDefect q = 0) at hq
    change q' ∈ ((approximateAdditiveQuadruples 1 W).filter fun q =>
      floorAdditiveDefect q = 0) at hq'
    rcases q with ⟨⟨a,b⟩,⟨c,d⟩⟩
    rcases q' with ⟨⟨a',b'⟩,⟨c',d'⟩⟩
    simp only [Finset.mem_filter, approximateAdditiveQuadruples,
      Finset.mem_product] at hq hq'
    rcases hq with ⟨⟨⟨⟨h1,h2⟩,h3,h4⟩, hd⟩, hzero⟩
    rcases hq' with ⟨⟨⟨⟨h1',h2'⟩,h3',h4'⟩, hd'⟩, hzero'⟩
    simp only [floorAdditiveQuadruple, mapAdditiveQuadruple,
      Prod.mk.injEq] at heq ⊢
    exact ⟨⟨floor_injective_on_of_separated W hW _ h1 _ h1' heq.1.1,
      floor_injective_on_of_separated W hW _ h2 _ h2' heq.1.2⟩,
      floor_injective_on_of_separated W hW _ h3 _ h3' heq.2.1,
      floor_injective_on_of_separated W hW _ h4 _ h4' heq.2.2⟩

end RiemannZeta.GuthMaynard
