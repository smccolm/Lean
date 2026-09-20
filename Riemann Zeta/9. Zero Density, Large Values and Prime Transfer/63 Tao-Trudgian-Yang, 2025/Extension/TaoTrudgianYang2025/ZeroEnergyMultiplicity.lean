import TaoTrudgianYang2025.EnergyExponents
import GuthMaynard.ClassicalEndpointSlab

/-!
# Local multiplicity and the cubic zero-energy bound

The paper's zero-energy set uses the symmetric rectangle `|Im ρ| ≤ T`, while
the available Jensen theorem is stated on positive dyadic slabs.  This module
bridges the conventions by treating positive ordinates directly, negative
ordinates by conjugation, and bounded ordinates by a fixed finite rectangle.
-/

open Complex

namespace TaoTrudgianYang2025

open RiemannZeta.GuthMaynard

theorem classicalLocalMultiplicityCap_mono
    {S T : ℝ} (hS : 1 ≤ S) (hST : S ≤ T) :
    classicalLocalMultiplicityCap S ≤ classicalLocalMultiplicityCap T := by
  unfold classicalLocalMultiplicityCap
  apply Nat.ceil_mono
  have hS0 : 0 ≤ S := zero_le_one.trans hS
  have hT : 0 ≤ T := hS0.trans hST
  have hden : 0 ≤ Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) := by
    positivity
  apply div_le_div_of_nonneg_right _ hden
  apply Real.log_le_log
  · positivity
  · apply div_le_div_of_nonneg_right _ (by norm_num)
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hS0 hST (by norm_num)) (by norm_num)

theorem zeroCopy_filter_card_eq_weighted_sum
    (σ T : ℝ) (pred : ℂ → Prop) [DecidablePred pred] :
    ((Finset.univ : Finset (ZeroCopy σ T)).filter fun z => pred z.1).card =
      ∑ ρ ∈ paperZeros σ T,
        if pred ρ then analyticVanishingOrder riemannZeta ρ else 0 := by
  classical
  letI : Fintype {ρ : ℂ // ρ ∈ paperZeros σ T ∧ pred ρ} :=
    Fintype.ofFinset ((paperZeros σ T).filter pred) (by
      intro ρ
      rw [Finset.mem_filter]
      rfl)
  rw [← Fintype.card_subtype]
  let e : {z : ZeroCopy σ T // pred z.1} ≃
      Σ ρ : {ρ : ℂ // ρ ∈ paperZeros σ T ∧ pred ρ},
        Fin (analyticVanishingOrder riemannZeta (ρ : ℂ)) :=
    { toFun := fun z =>
        ⟨⟨z.1.1, z.1.1.property, z.2⟩, z.1.2⟩
      invFun := fun z =>
        ⟨⟨⟨z.1.1, z.1.2.1⟩, z.2⟩, z.1.2.2⟩
      left_inv := by intro z; rfl
      right_inv := by intro z; rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  calc
    (∑ x : {ρ : ℂ // ρ ∈ paperZeros σ T ∧ pred ρ},
        analyticVanishingOrder riemannZeta (x : ℂ)) =
        ∑ ρ ∈ (paperZeros σ T).filter pred,
          analyticVanishingOrder riemannZeta ρ :=
      (Finset.sum_subtype
        ((paperZeros σ T).filter pred)
        (fun ρ => by simp)
        (fun ρ : ℂ => analyticVanishingOrder riemannZeta ρ)).symm
    _ = ∑ ρ ∈ paperZeros σ T,
        if pred ρ then analyticVanishingOrder riemannZeta ρ else 0 := by
      simp only [Finset.sum_filter]

theorem positiveUnitBin_copy_card_le_cap
    {σ T : ℝ} (z : ℤ) (hσ : 1 / 2 ≤ σ) (hz : 8 ≤ (z : ℝ)) :
    ((Finset.univ : Finset (ZeroCopy σ T)).filter fun w =>
      (z : ℝ) ≤ (w.1 : ℂ).im ∧ (w.1 : ℂ).im < (z : ℝ) + 1).card ≤
        classicalLocalMultiplicityCap T := by
  classical
  let pred : ℂ → Prop := fun ρ =>
    (z : ℝ) ≤ ρ.im ∧ ρ.im < (z : ℝ) + 1
  let S := (paperZeros σ T).filter pred
  change ((Finset.univ : Finset (ZeroCopy σ T)).filter fun w =>
    pred w.1).card ≤ _
  by_cases hS : S = ∅
  · rw [zeroCopy_filter_card_eq_weighted_sum σ T pred]
    rw [← Finset.sum_filter, show (paperZeros σ T).filter pred = ∅ from hS]
    simp
  · obtain ⟨ρ₀, hρ₀⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    have hρ₀Data : ρ₀ ∈ paperZeros σ T ∧ pred ρ₀ := by
      simpa only [S, Finset.mem_filter] using hρ₀
    dsimp [pred] at hρ₀Data
    have hρ₀Paper := (mem_paperZeros_iff ρ₀).mp hρ₀Data.1
    have hzT : (z : ℝ) ≤ T := by
      have himT : ρ₀.im ≤ T := le_trans (le_abs_self _) hρ₀Paper.2.2.1
      exact hρ₀Data.2.1.trans himT
    have hsubset : S ⊆ zeroUnitBin σ (z : ℝ) z := by
      intro ρ hρ
      have hρData : ρ ∈ paperZeros σ T ∧ pred ρ := by
        simpa only [S, Finset.mem_filter] using hρ
      dsimp [pred] at hρData
      rw [zeroUnitBin, Finset.mem_filter]
      refine ⟨?_, hρData.2⟩
      rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
        mem_ZeroRectangle]
      have hpaper := (mem_paperZeros_iff ρ).mp hρData.1
      refine ⟨⟨hpaper.1, hpaper.2.1, hρData.2.1, ?_⟩, hpaper.2.2.2⟩
      linarith
    rw [zeroCopy_filter_card_eq_weighted_sum σ T pred]
    change (∑ ρ ∈ paperZeros σ T,
      if pred ρ then analyticVanishingOrder riemannZeta ρ else 0) ≤ _
    rw [← Finset.sum_filter]
    change (∑ ρ ∈ S, analyticVanishingOrder riemannZeta ρ) ≤ _
    calc
      (∑ ρ ∈ S, analyticVanishingOrder riemannZeta ρ) ≤
          ∑ ρ ∈ zeroUnitBin σ (z : ℝ) z,
            analyticVanishingOrder riemannZeta ρ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intro _ _ _
        exact Nat.zero_le _
      _ ≤ classicalLocalMultiplicityCap (z : ℝ) :=
        zeroUnitBin_multiplicity_le_cap σ (z : ℝ) z hσ hz
      _ ≤ classicalLocalMultiplicityCap T := by
        have hzOne : (1 : ℝ) ≤ z := by linarith
        exact classicalLocalMultiplicityCap_mono hzOne hzT

theorem positiveLocal_copy_card_le_three_mul_cap
    {σ T center : ℝ} (hσ : 1 / 2 ≤ σ) (hcenter : 9 ≤ center) :
    ((Finset.univ : Finset (ZeroCopy σ T)).filter fun w =>
      |center - (w.1 : ℂ).im| ≤ 1).card ≤
        3 * classicalLocalMultiplicityCap T := by
  classical
  let localSet : Finset (ZeroCopy σ T) :=
    Finset.univ.filter fun w => |center - (w.1 : ℂ).im| ≤ 1
  let project : ZeroCopy σ T → ℤ := fun w => ⌊(w.1 : ℂ).im⌋
  have hfiber : ∀ z ∈ localSet.image project,
      (localSet.filter fun w => project w = z).card ≤
        classicalLocalMultiplicityCap T := by
    intro z hz
    obtain ⟨w₀, hw₀Local, hw₀Project⟩ := Finset.mem_image.mp hz
    have hw₀Abs : |center - (w₀.1 : ℂ).im| ≤ 1 := by
      simpa only [localSet, Finset.mem_filter, Finset.mem_univ, true_and] using hw₀Local
    have hw₀Lower : center - 1 ≤ (w₀.1 : ℂ).im := by
      rw [abs_le] at hw₀Abs
      linarith
    have hzEight : 8 ≤ (z : ℝ) := by
      have hEightIm : 8 ≤ (w₀.1 : ℂ).im := by linarith
      have hEightFloor : (8 : ℤ) ≤ ⌊(w₀.1 : ℂ).im⌋ :=
        Int.le_floor.mpr (by exact_mod_cast hEightIm)
      change (8 : ℤ) ≤ project w₀ at hEightFloor
      rw [hw₀Project] at hEightFloor
      exact_mod_cast hEightFloor
    have hsubset : (localSet.filter fun w => project w = z) ⊆
        (Finset.univ : Finset (ZeroCopy σ T)).filter fun w =>
          (z : ℝ) ≤ (w.1 : ℂ).im ∧ (w.1 : ℂ).im < (z : ℝ) + 1 := by
      intro w hw
      have hwProject := (Finset.mem_filter.mp hw).2
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hFloorLe : ((⌊(w.1 : ℂ).im⌋ : ℤ) : ℝ) ≤ (w.1 : ℂ).im :=
        Int.floor_le _
      have hLtFloor : (w.1 : ℂ).im <
          ((⌊(w.1 : ℂ).im⌋ : ℤ) : ℝ) + 1 :=
        Int.lt_floor_add_one _
      simpa only [project, hwProject] using And.intro hFloorLe hLtFloor
    exact (Finset.card_le_card hsubset).trans
      (positiveUnitBin_copy_card_le_cap z hσ hzEight)
  have hmain := Finset.card_le_mul_card_image localSet
    (classicalLocalMultiplicityCap T) hfiber
  have himage : (localSet.image project).card ≤ 3 := by
    have hsubset : localSet.image project ⊆
        Finset.Icc ⌊center - 1⌋ ⌊center + 1⌋ := by
      intro z hz
      obtain ⟨w, hwLocal, rfl⟩ := Finset.mem_image.mp hz
      have hwAbs : |center - (w.1 : ℂ).im| ≤ 1 := by
        simpa only [localSet, Finset.mem_filter, Finset.mem_univ, true_and] using hwLocal
      rw [Finset.mem_Icc]
      apply And.intro <;> apply Int.floor_mono
      · linarith [(abs_le.mp hwAbs).2]
      · linarith [(abs_le.mp hwAbs).1]
    calc
      (localSet.image project).card ≤
          (Finset.Icc ⌊center - 1⌋ ⌊center + 1⌋).card :=
        Finset.card_le_card hsubset
      _ = 3 := by
        rw [Int.card_Icc]
        rw [show center - 1 = center + ((-1 : ℤ) : ℝ) by ring,
          Int.floor_add_intCast, Int.floor_add_one]
        have hcalc : ⌊center⌋ + 1 + 1 - (⌊center⌋ + (-1 : ℤ)) = 3 := by
          ring
        rw [hcalc]
        rfl
  change localSet.card ≤ _
  calc
    localSet.card ≤ classicalLocalMultiplicityCap T *
        (localSet.image project).card := hmain
    _ ≤ classicalLocalMultiplicityCap T * 3 := by gcongr
    _ = 3 * classicalLocalMultiplicityCap T := by omega

theorem paperZeros_conj_mem {σ T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ paperZeros σ T) : star ρ ∈ paperZeros σ T := by
  rw [mem_paperZeros_iff]
  have hp := (mem_paperZeros_iff ρ).mp hρ
  have hρNe : ρ ≠ 1 := by
    intro h
    subst ρ
    exact riemannZeta_one_ne_zero hp.2.2.2
  refine ⟨by simpa using hp.1, by simpa using hp.2.1, ?_, ?_⟩
  · simpa using hp.2.2.1
  · rw [riemannZeta_conj ρ hρNe, hp.2.2.2]
    simp

theorem paperZero_ne_one {σ T : ℝ} (ρ : ↥(paperZeros σ T)) :
    (ρ : ℂ) ≠ 1 := by
  intro h
  have hp := (mem_paperZeros_iff (ρ : ℂ)).mp ρ.property
  rw [h] at hp
  exact riemannZeta_one_ne_zero hp.2.2.2

noncomputable def zeroCopyConjEquiv (σ T : ℝ) :
    ZeroCopy σ T ≃ ZeroCopy σ T where
  toFun z :=
    ⟨⟨star (z.1 : ℂ), paperZeros_conj_mem z.1.property⟩,
      Fin.cast (analyticVanishingOrder_conj (z.1 : ℂ)
        (paperZero_ne_one z.1)).symm z.2⟩
  invFun z :=
    ⟨⟨star (z.1 : ℂ), paperZeros_conj_mem z.1.property⟩,
      Fin.cast (analyticVanishingOrder_conj (z.1 : ℂ)
        (paperZero_ne_one z.1)).symm z.2⟩
  left_inv := by
    intro z
    apply Sigma.ext
    · apply Subtype.ext
      simp
    · apply (Fin.heq_ext_iff (by simp)).2
      rfl
  right_inv := by
    intro z
    apply Sigma.ext
    · apply Subtype.ext
      simp
    · apply (Fin.heq_ext_iff (by simp)).2
      rfl

theorem zeroCopy_local_card_conj (σ T center : ℝ) :
    ((Finset.univ : Finset (ZeroCopy σ T)).filter fun w =>
      |center - (w.1 : ℂ).im| ≤ 1).card =
    ((Finset.univ : Finset (ZeroCopy σ T)).filter fun w =>
      |-center - (w.1 : ℂ).im| ≤ 1).card := by
  classical
  let e := zeroCopyConjEquiv σ T
  let leftSet := (Finset.univ : Finset (ZeroCopy σ T)).filter fun w =>
    |center - (w.1 : ℂ).im| ≤ 1
  let rightSet := (Finset.univ : Finset (ZeroCopy σ T)).filter fun w =>
    |-center - (w.1 : ℂ).im| ≤ 1
  let ef : ↥leftSet ≃ ↥rightSet :=
    { toFun := fun w => ⟨e w.1, by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have hw := (Finset.mem_filter.mp w.2).2
        change |-center - (star (w.1.1 : ℂ)).im| ≤ 1
        rw [Complex.star_def, Complex.conj_im]
        rw [show -center - -(w.1.1 : ℂ).im =
          -(center - (w.1.1 : ℂ).im) by ring, abs_neg]
        exact hw⟩
      invFun := fun w => ⟨e.symm w.1, by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have hw := (Finset.mem_filter.mp w.2).2
        change |center - (star (w.1.1 : ℂ)).im| ≤ 1
        rw [Complex.star_def, Complex.conj_im]
        rw [show center - -(w.1.1 : ℂ).im =
          -(-center - (w.1.1 : ℂ).im) by ring, abs_neg]
        exact hw⟩
      left_inv := by intro w; apply Subtype.ext; exact e.left_inv w.1
      right_inv := by intro w; apply Subtype.ext; exact e.right_inv w.1 }
  change leftSet.card = rightSet.card
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr ef

theorem negativeLocal_copy_card_le_three_mul_cap
    {σ T center : ℝ} (hσ : 1 / 2 ≤ σ) (hcenter : center ≤ -9) :
    ((Finset.univ : Finset (ZeroCopy σ T)).filter fun w =>
      |center - (w.1 : ℂ).im| ≤ 1).card ≤
        3 * classicalLocalMultiplicityCap T := by
  rw [zeroCopy_local_card_conj σ T center]
  exact positiveLocal_copy_card_le_three_mul_cap hσ (by linarith)

theorem boundedLocal_copy_card_le_fixed
    {σ T center : ℝ} (hσ : 1 / 2 ≤ σ)
    (hcenterLower : -9 < center) (hcenterUpper : center < 9) :
    ((Finset.univ : Finset (ZeroCopy σ T)).filter fun w =>
      |center - (w.1 : ℂ).im| ≤ 1).card ≤
        paperZeroCount (1 / 2) 10 := by
  classical
  let pred : ℂ → Prop := fun ρ => |center - ρ.im| ≤ 1
  let S := (paperZeros σ T).filter pred
  change ((Finset.univ : Finset (ZeroCopy σ T)).filter fun w =>
    pred w.1).card ≤ _
  rw [zeroCopy_filter_card_eq_weighted_sum σ T pred]
  rw [← Finset.sum_filter]
  change (∑ ρ ∈ S, analyticVanishingOrder riemannZeta ρ) ≤ _
  have hsubset : S ⊆ paperZeros (1 / 2) 10 := by
    intro ρ hρ
    have hρData : ρ ∈ paperZeros σ T ∧ pred ρ := by
      simpa only [S, Finset.mem_filter] using hρ
    have hpaper := (mem_paperZeros_iff ρ).mp hρData.1
    have habs := abs_le.mp hρData.2
    rw [mem_paperZeros_iff]
    refine ⟨hσ.trans hpaper.1, hpaper.2.1, ?_, hpaper.2.2.2⟩
    rw [abs_le]
    constructor <;> linarith
  calc
    (∑ ρ ∈ S, analyticVanishingOrder riemannZeta ρ) ≤
        ∑ ρ ∈ paperZeros (1 / 2) 10,
          analyticVanishingOrder riemannZeta ρ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro _ _ _
      exact Nat.zero_le _
    _ = paperZeroCount (1 / 2) 10 := by
      rfl

theorem zeroCopy_local_card_le_globalCap
    {σ T : ℝ} (hσ : 1 / 2 ≤ σ) (center : ℝ) :
    ((Finset.univ : Finset (ZeroCopy σ T)).filter fun w =>
      |center - (w.1 : ℂ).im| ≤ 1).card ≤
        max (paperZeroCount (1 / 2) 10)
          (3 * classicalLocalMultiplicityCap T) := by
  by_cases hpos : 9 ≤ center
  · exact (positiveLocal_copy_card_le_three_mul_cap hσ hpos).trans
      (le_max_right _ _)
  by_cases hneg : center ≤ -9
  · exact (negativeLocal_copy_card_le_three_mul_cap hσ hneg).trans
      (le_max_right _ _)
  · exact (boundedLocal_copy_card_le_fixed hσ
      (lt_of_not_ge hneg) (lt_of_not_ge hpos)).trans (le_max_left _ _)

theorem zeroAdditiveEnergy_le_globalCap_mul_cube
    {σ T : ℝ} (hσ : 1 / 2 ≤ σ) :
    zeroAdditiveEnergy σ T ≤
      max (paperZeroCount (1 / 2) 10)
        (3 * classicalLocalMultiplicityCap T) * paperZeroCount σ T ^ 3 := by
  unfold zeroAdditiveEnergy
  simpa only [zeroCopy_card] using
    (approximateAdditiveEnergyOf_le_localMass_mul_cube 1
      (fun z : ZeroCopy σ T => ((z.1 : ℂ).im : ℝ)) _
      (zeroCopy_local_card_le_globalCap hσ))

theorem localMultiplicityCap_le_rpow
    {η : ℝ} (hη : 0 < η) :
    ∃ c : ℝ, 0 < c ∧ ∀ T : ℝ, 8 ≤ T →
      (classicalLocalMultiplicityCap T : ℝ) ≤ c * T ^ η := by
  let c : ℝ :=
    (Real.log (500 / 3 : ℝ) + 3 / η) / Real.log (35 / 32 : ℝ) + 1
  have hlogRatio : 0 < Real.log (35 / 32 : ℝ) :=
    Real.log_pos (by norm_num)
  have hlogConst : 0 ≤ Real.log (500 / 3 : ℝ) :=
    Real.log_nonneg (by norm_num)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  refine ⟨c, hc, ?_⟩
  intro T hT
  have hTpos : 0 < T := by linarith
  have hTone : 1 ≤ T := by linarith
  have hTηOne : 1 ≤ T ^ η := Real.one_le_rpow hTone hη.le
  have hlogT : Real.log T ≤ T ^ η / η :=
    Real.log_le_rpow_div hTpos.le hη
  have hraw := localMultiplicityCap_lt_log_majorant T hT
  apply hraw.le.trans
  dsimp [c]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have hInvRatio : 0 ≤ (Real.log (35 / 32 : ℝ))⁻¹ :=
    inv_nonneg.mpr hlogRatio.le
  have hLogScaled : 3 * Real.log T *
      (Real.log (35 / 32 : ℝ))⁻¹ ≤
      3 * (T ^ η / η) * (Real.log (35 / 32 : ℝ))⁻¹ := by
    gcongr
  have hConstScaled : Real.log (500 / 3 : ℝ) *
      (Real.log (35 / 32 : ℝ))⁻¹ ≤
      (Real.log (500 / 3 : ℝ) *
        (Real.log (35 / 32 : ℝ))⁻¹) * T ^ η := by
    calc
      Real.log (500 / 3 : ℝ) * (Real.log (35 / 32 : ℝ))⁻¹ =
          (Real.log (500 / 3 : ℝ) *
            (Real.log (35 / 32 : ℝ))⁻¹) * 1 := by ring
      _ ≤ (Real.log (500 / 3 : ℝ) *
            (Real.log (35 / 32 : ℝ))⁻¹) * T ^ η := by
        gcongr
  calc
    (Real.log (500 / 3 : ℝ) + 3 * Real.log T) *
          (Real.log (35 / 32 : ℝ))⁻¹ + 1 ≤
        (Real.log (500 / 3 : ℝ) *
            (Real.log (35 / 32 : ℝ))⁻¹) * T ^ η +
          3 * (T ^ η / η) *
            (Real.log (35 / 32 : ℝ))⁻¹ + T ^ η := by
      linarith
    _ = ((Real.log (500 / 3 : ℝ) + 3 / η) *
          (Real.log (35 / 32 : ℝ))⁻¹ + 1) * T ^ η := by
      field_simp [hη.ne']

theorem globalMultiplicityCap_le_rpow
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ T : ℝ, C ≤ T →
      (max (paperZeroCount (1 / 2) 10)
        (3 * classicalLocalMultiplicityCap T) : ℕ) ≤ C * T ^ η := by
  obtain ⟨c, hc, hcap⟩ := localMultiplicityCap_le_rpow hη
  let fixed : ℝ := paperZeroCount (1 / 2) 10
  let C : ℝ := max 8 (max fixed (3 * c))
  have hC8 : 8 ≤ C := le_max_left _ _
  have hCfixed : fixed ≤ C :=
    (le_max_left fixed (3 * c)).trans (le_max_right 8 _)
  have hCcap : 3 * c ≤ C :=
    (le_max_right fixed (3 * c)).trans (le_max_right 8 _)
  have hC : 1 ≤ C := by linarith
  refine ⟨C, hC, ?_⟩
  intro T hCT
  have hT8 : 8 ≤ T := hC8.trans hCT
  have hTone : 1 ≤ T := by linarith
  have hpowOne : 1 ≤ T ^ η := Real.one_le_rpow hTone hη.le
  have hcapT := hcap T hT8
  push_cast
  apply max_le
  · change fixed ≤ C * T ^ η
    calc
      fixed ≤ C := hCfixed
      _ ≤ C * T ^ η := by nlinarith
  · calc
      3 * (classicalLocalMultiplicityCap T : ℝ) ≤
          3 * (c * T ^ η) := by gcongr
      _ = (3 * c) * T ^ η := by ring
      _ ≤ C * T ^ η := by gcongr

theorem paperZeroCount_mono_sigma
    {σLow σHigh T : ℝ} (hσ : σLow ≤ σHigh) :
    paperZeroCount σHigh T ≤ paperZeroCount σLow T := by
  rw [paperZeroCount_eq_zeroCountRect, paperZeroCount_eq_zeroCountRect]
  exact zeroCountRect_mono σHigh 1 (-T) T σLow 1 (-T) T hσ
    le_rfl le_rfl le_rfl

theorem IsZeroDensityBound.toEnergyBound_three_mul
    {σ A : ℝ} (h : IsZeroDensityBound σ A) (hσ : 1 / 2 < σ) :
    IsZeroDensityEnergyBound σ (3 * A) := by
  intro ε hε
  obtain ⟨K, hK, δ₀, hδ₀, hcount⟩ := h (ε / 6) (by linarith)
  obtain ⟨D, hD, hcap⟩ :=
    globalMultiplicityCap_le_rpow (show 0 < ε / 2 by linarith)
  let δ : ℝ := min δ₀ ((σ - 1 / 2) / 2)
  have hgap : 0 < (σ - 1 / 2) / 2 := by linarith
  have hδ : 0 < δ := lt_min hδ₀ hgap
  have hδδ₀ : δ ≤ δ₀ := min_le_left _ _
  have hσShift : 1 / 2 ≤ σ - δ := by
    have := min_le_right δ₀ ((σ - 1 / 2) / 2)
    dsimp [δ]
    linarith
  let C : ℝ := max (max K D) (D * K ^ 3)
  have hKC : K ≤ C := (le_max_left K D).trans (le_max_left _ _)
  have hDC : D ≤ C := (le_max_right K D).trans (le_max_left _ _)
  have hprodC : D * K ^ 3 ≤ C := le_max_right _ _
  have hC : 1 ≤ C := hK.trans hKC
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro T hCT
  have hKT : K ≤ T := hKC.trans hCT
  have hDT : D ≤ T := hDC.trans hCT
  have hcountOriginal := hcount T hKT
  have hcountMonoNat : paperZeroCount (σ - δ) T ≤
      paperZeroCount (σ - δ₀) T :=
    paperZeroCount_mono_sigma (by linarith)
  have hcountMono : (paperZeroCount (σ - δ) T : ℝ) ≤
      paperZeroCount (σ - δ₀) T := by
    exact_mod_cast hcountMonoNat
  have hcountBound : (paperZeroCount (σ - δ) T : ℝ) ≤
      K * T ^ (A * (1 - σ) + ε / 6) :=
    hcountMono.trans hcountOriginal
  have henergyNat := zeroCopy_local_card_le_globalCap
    (T := T) hσShift
  have hzeroEnergyNat :=
    (show zeroAdditiveEnergy (σ - δ) T ≤
      max (paperZeroCount (1 / 2) 10)
        (3 * classicalLocalMultiplicityCap T) *
          paperZeroCount (σ - δ) T ^ 3 from by
      unfold zeroAdditiveEnergy
      simpa only [zeroCopy_card] using
        (approximateAdditiveEnergyOf_le_localMass_mul_cube 1
          (fun z : ZeroCopy (σ - δ) T => ((z.1 : ℂ).im : ℝ)) _
          henergyNat))
  have hzeroEnergy : (zeroAdditiveEnergy (σ - δ) T : ℝ) ≤
      (max (paperZeroCount (1 / 2) 10)
        (3 * classicalLocalMultiplicityCap T) : ℝ) *
          (paperZeroCount (σ - δ) T : ℝ) ^ 3 := by
    exact_mod_cast hzeroEnergyNat
  have hcapBound := hcap T hDT
  push_cast at hcapBound
  have hTnonneg : 0 ≤ T := zero_le_one.trans (hC.trans hCT)
  have hpowCube :
      (T ^ (A * (1 - σ) + ε / 6)) ^ 3 =
        T ^ (3 * A * (1 - σ) + ε / 2) := by
    calc
      (T ^ (A * (1 - σ) + ε / 6)) ^ 3 =
          T ^ ((A * (1 - σ) + ε / 6) * (3 : ℝ)) := by
        rw [Real.rpow_mul hTnonneg]
        exact (Real.rpow_natCast
          (T ^ (A * (1 - σ) + ε / 6)) 3).symm
      _ = T ^ (3 * A * (1 - σ) + ε / 2) := by
        congr 1
        ring
  have hpowProduct :
      T ^ (ε / 2) * T ^ (3 * A * (1 - σ) + ε / 2) =
        T ^ ((3 * A) * (1 - σ) + ε) := by
    rw [← Real.rpow_add (zero_lt_one.trans_le (hC.trans hCT))]
    congr 1
    ring
  calc
    (zeroAdditiveEnergy (σ - δ) T : ℝ) ≤
        (max (paperZeroCount (1 / 2) 10)
          (3 * classicalLocalMultiplicityCap T) : ℝ) *
            (paperZeroCount (σ - δ) T : ℝ) ^ 3 := hzeroEnergy
    _ ≤ (D * T ^ (ε / 2)) *
          (K * T ^ (A * (1 - σ) + ε / 6)) ^ 3 := by
      gcongr
    _ = (D * K ^ 3) * T ^ ((3 * A) * (1 - σ) + ε) := by
      rw [mul_pow, hpowCube]
      calc
        D * T ^ (ε / 2) *
            (K ^ 3 * T ^ (3 * A * (1 - σ) + ε / 2)) =
            (D * K ^ 3) *
              (T ^ (ε / 2) * T ^ (3 * A * (1 - σ) + ε / 2)) := by
          ring
        _ = (D * K ^ 3) * T ^ ((3 * A) * (1 - σ) + ε) := by
          rw [hpowProduct]
    _ ≤ C * T ^ ((3 * A) * (1 - σ) + ε) :=
      mul_le_mul_of_nonneg_right hprodC (Real.rpow_nonneg hTnonneg _)

/-- Multiplication by a positive finite extended real is an order
automorphism, including at both infinities. -/
private noncomputable def zeroEnergyScaleOrderIso (c : EReal)
    (hc : 0 < c) (htop : c ≠ ⊤) : EReal ≃o EReal :=
  StrictMono.orderIsoOfSurjective (fun x : EReal => x * c) (by
    intro x y hxy
    have hcancel (z : EReal) : z * c / c = z := by
      rw [mul_comm z c, ← EReal.mul_div c z c,
        EReal.mul_div_cancel (ne_bot_of_gt hc) htop hc.ne']
    have hd : x * c / c < y * c / c := by
      simpa only [hcancel] using hxy
    exact (EReal.strictMono_div_right_of_pos hc htop).lt_iff_lt.mp hd) (by
      intro y
      exact ⟨y / c, EReal.div_mul_cancel (ne_bot_of_gt hc) htop hc.ne'⟩)

private theorem zeroEnergy_sInf_image_mul_three (s : Set EReal) :
    sInf ((fun x : EReal => x * 3) '' s) = sInf s * 3 := by
  let e := zeroEnergyScaleOrderIso 3 (by norm_num) (EReal.natCast_ne_top 3)
  rw [sInf_image]
  change (⨅ a ∈ s, e a) = e (sInf s)
  exact (e.map_sInf s).symm

/-- On the source range `1 / 2 < σ`, the symmetric-rectangle local
multiplicity estimate gives the sharp exponent comparison `A*(σ) ≤ 3 A(σ)`,
including infinite infima. -/
theorem zeroDensityEnergyExponent_le_three_mul_zeroDensityExponent
    (σ : ℝ) (hσ : 1 / 2 < σ) :
    zeroDensityEnergyExponent σ ≤
      (3 : EReal) * zeroDensityExponent σ := by
  let Z : Set EReal :=
    (fun A : ℝ => (A : EReal)) '' zeroDensityBounds σ
  let ZE : Set EReal :=
    (fun Astar : ℝ => (Astar : EReal)) '' zeroDensityEnergyBounds σ
  have hsubset : (fun x : EReal => x * 3) '' Z ⊆ ZE := by
    rintro x ⟨y, ⟨A, hA, rfl⟩, rfl⟩
    refine ⟨3 * A, hA.toEnergyBound_three_mul hσ, ?_⟩
    change (↑(3 * A) : EReal) = (A : EReal) * 3
    calc
      (↑(3 * A) : EReal) = (↑(A * 3) : EReal) := by congr 1; ring
      _ = (A : EReal) * (↑(3 : ℝ) : EReal) := EReal.coe_mul _ _
      _ = (A : EReal) * 3 := by rfl
  have hinf : sInf ZE ≤ sInf ((fun x : EReal => x * 3) '' Z) :=
    sInf_le_sInf hsubset
  rw [zeroEnergy_sInf_image_mul_three] at hinf
  simpa only [zeroDensityExponent, zeroDensityEnergyExponent, Z, ZE,
    mul_comm] using hinf

end TaoTrudgianYang2025
