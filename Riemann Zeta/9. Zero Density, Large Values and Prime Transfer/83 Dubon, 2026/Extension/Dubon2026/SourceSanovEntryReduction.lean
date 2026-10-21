import Dubon2026.SourceSanovMatrices

/-! Original congruence matrices lie in the required actual free subgroup.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> surjective native H1 coefficient map -> Gamma0 H2 vanishing
after inverting six -> the actual free level-four subgroup.

Adapted from anthropics/fermats-last-theorem, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_TW12CD1Dock_subsingleton_H2_gamma0.lean.txt (Apache-2.0;
retained LICENSE and NOTICE). Descent is on the original integer matrix
entry, using the literal previously constructed unipotent generators.
-/

namespace Dubon2026
noncomputable section
open Matrix
open scoped MatrixGroups

/-- The exact integral congruences characterizing the matrices needed for the free subgroup. -/
def sourceSanovEntries (γ : SL(2, ℤ)) : Prop :=
  γ.1 0 0 % 4 = 1 ∧ γ.1 1 1 % 4 = 1 ∧ 2 ∣ γ.1 0 1 ∧ 2 ∣ γ.1 1 0

/-- An original congruence matrix with zero lower-left entry is a power of the actual upper generator. -/
theorem sourceSanov_mem_range_of_lower_zero (γ : SL(2, ℤ)) (h : sourceSanovEntries γ)
    (hc : γ.1 1 0 = 0) :
    γ ∈ (FreeGroup.lift ![sourceSanovA, sourceSanovB] : FreeGroup (Fin 2) →* SL(2, ℤ)).range := by
  obtain ⟨ha, -, ⟨k, hb⟩, -⟩ := h
  have hdet : γ.1.det = 1 := γ.2
  rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
  have ha1 : γ.1 0 0 = 1 := by
    have hu : IsUnit (γ.1 0 0) := IsUnit.of_mul_eq_one (γ.1 1 1) hdet
    rcases Int.isUnit_iff.mp hu with h1 | h1 <;> omega
  have hd1 : γ.1 1 1 = 1 := by rw [ha1] at hdet; omega
  refine ⟨(FreeGroup.of (0 : Fin 2)) ^ k, ?_⟩
  rw [map_zpow, FreeGroup.lift_apply_of]
  apply Subtype.ext
  show (((![sourceSanovA, sourceSanovB] (0 : Fin 2) : SL(2, ℤ)) ^ k : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
    = γ.1
  rw [show (![sourceSanovA, sourceSanovB] (0 : Fin 2)) = sourceSanovA from rfl, sourceSanovA_zpow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha1, hd1, hc, hb]

/-- An even integer shear brings a coordinate within the positive other coordinate's size. -/
theorem sourceSanov_exists_balanced_pos (x y : ℤ) (hy : 0 < y) : ∃ m : ℤ, |x - 2 * m * y| ≤ |y| := by
  refine ⟨if x % (2 * y) ≤ y then x / (2 * y) else x / (2 * y) + 1, ?_⟩
  have hdm : x % (2 * y) + 2 * y * (x / (2 * y)) = x := Int.emod_add_mul_ediv x (2 * y)
  have hr0 : 0 ≤ x % (2 * y) := Int.emod_nonneg x (by positivity)
  have hrlt : x % (2 * y) < 2 * y := Int.emod_lt_of_pos x (by positivity)
  rw [abs_of_pos hy]
  split
  next hle =>
    rw [show x - 2 * (x / (2 * y)) * y = x % (2 * y) from by linarith]
    rw [abs_of_nonneg hr0]
    exact hle
  next hgt =>
    rw [show x - 2 * (x / (2 * y) + 1) * y = x % (2 * y) - 2 * y from by linarith]
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- An even integer shear balances coordinates for either sign of the nonzero other coordinate. -/
theorem sourceSanov_exists_balanced (x y : ℤ) (hy : y ≠ 0) : ∃ m : ℤ, |x - 2 * m * y| ≤ |y| := by
  rcases lt_or_gt_of_ne hy with hneg | hpos
  · obtain ⟨m, hm⟩ := sourceSanov_exists_balanced_pos x (-y) (by linarith)
    refine ⟨-m, ?_⟩
    rw [show x - 2 * -m * y = x - 2 * m * -y from by ring]
    rwa [abs_neg] at hm
  · exact sourceSanov_exists_balanced_pos x y hpos

/-- Opposite coordinate parity makes the actual balancing bound strict. -/
theorem sourceSanov_abs_lt_of_parity {r y : ℤ} (h : |r| ≤ |y|) (hr : r % 2 = 1)
    (hy : y % 2 = 0) : |r| < |y| := by
  rcases lt_or_eq_of_le h with h' | h'
  · exact h'
  · exfalso
    rcases abs_eq_abs.mp h' with rfl | rfl <;> omega

/-- Left multiplication by the actual upper shear has the stated literal matrix entries. -/
theorem sourceSanovA_zpow_mul (m : ℤ) (γ : SL(2, ℤ)) :
    ((sourceSanovA ^ m * γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = !![γ.1 0 0 + 2 * m * γ.1 1 0, γ.1 0 1 + 2 * m * γ.1 1 1;
           γ.1 1 0, γ.1 1 1] := by
  rw [SpecialLinearGroup.coe_mul, sourceSanovA_zpow]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_succ]

/-- Left multiplication by the actual lower shear has the stated literal matrix entries. -/
theorem sourceSanovB_zpow_mul (m : ℤ) (γ : SL(2, ℤ)) :
    ((sourceSanovB ^ m * γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = !![γ.1 0 0, γ.1 0 1;
           γ.1 1 0 + 2 * m * γ.1 0 0, γ.1 1 1 + 2 * m * γ.1 0 1] := by
  rw [SpecialLinearGroup.coe_mul, sourceSanovB_zpow]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals ring

/-- The actual upper shear preserves the required original integer entry congruences. -/
theorem sourceSanovEntries_A_mul (m : ℤ) (γ : SL(2, ℤ)) (h : sourceSanovEntries γ) :
    sourceSanovEntries (sourceSanovA ^ m * γ) := by
  obtain ⟨ha, hd, ⟨kb, hb⟩, ⟨kc, hc⟩⟩ := h
  unfold sourceSanovEntries
  rw [sourceSanovA_zpow_mul]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp
  · rw [hc, show γ.1 0 0 + 2 * m * (2 * kc) = γ.1 0 0 + 4 * (m * kc) from by ring,
      Int.add_mul_emod_self_left]
    exact ha
  · exact hd
  · exact ⟨kb + m * γ.1 1 1, by rw [hb]; ring⟩
  · exact ⟨kc, hc⟩

/-- The actual lower shear preserves the required original integer entry congruences. -/
theorem sourceSanovEntries_B_mul (m : ℤ) (γ : SL(2, ℤ)) (h : sourceSanovEntries γ) :
    sourceSanovEntries (sourceSanovB ^ m * γ) := by
  obtain ⟨ha, hd, ⟨kb, hb⟩, ⟨kc, hc⟩⟩ := h
  unfold sourceSanovEntries
  rw [sourceSanovB_zpow_mul]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp
  · exact ha
  · rw [hb, show γ.1 1 1 + 2 * m * (2 * kb) = γ.1 1 1 + 4 * (m * kb) from by ring,
      Int.add_mul_emod_self_left]
    exact hd
  · exact ⟨kb, hb⟩
  · exact ⟨kc + m * γ.1 0 0, by rw [hc]; ring⟩

/-- The actual upper generator belongs to the literal free-word image. -/
theorem sourceSanovA_mem_range :
    sourceSanovA ∈ (FreeGroup.lift ![sourceSanovA, sourceSanovB] : FreeGroup (Fin 2) →* SL(2, ℤ)).range :=
  ⟨FreeGroup.of 0, by rw [FreeGroup.lift_apply_of]; rfl⟩

/-- The actual lower generator belongs to the literal free-word image. -/
theorem sourceSanovB_mem_range :
    sourceSanovB ∈ (FreeGroup.lift ![sourceSanovA, sourceSanovB] : FreeGroup (Fin 2) →* SL(2, ℤ)).range :=
  ⟨FreeGroup.of 1, by rw [FreeGroup.lift_apply_of]; rfl⟩


end
end Dubon2026
