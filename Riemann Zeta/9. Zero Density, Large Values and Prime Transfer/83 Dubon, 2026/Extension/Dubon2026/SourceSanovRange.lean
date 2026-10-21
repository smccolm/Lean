import Dubon2026.SourceSanovEntryReduction

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

/-- Every original congruence matrix with bounded lower-left entry lies in the actual free-word image. -/
theorem sourceSanov_mem_range_bounded :
    ∀ (n : ℕ) (γ : SL(2, ℤ)), sourceSanovEntries γ → (γ.1 1 0).natAbs ≤ n →
      γ ∈ (FreeGroup.lift ![sourceSanovA, sourceSanovB] : FreeGroup (Fin 2) →* SL(2, ℤ)).range := by
  intro n
  induction n with
  | zero =>
    intro γ h hn
    exact sourceSanov_mem_range_of_lower_zero γ h (Int.natAbs_eq_zero.mp (Nat.le_zero.mp hn))
  | succ n IH =>
    intro γ h hn
    by_cases hc0 : γ.1 1 0 = 0
    · exact sourceSanov_mem_range_of_lower_zero γ h hc0
    · obtain ⟨ha, hd, hb2, hc2⟩ := h

      obtain ⟨m₀, hm₀⟩ := sourceSanov_exists_balanced (γ.1 0 0) (γ.1 1 0) hc0
      have h₁ : sourceSanovEntries (sourceSanovA ^ (-m₀) * γ) :=
        sourceSanovEntries_A_mul (-m₀) γ ⟨ha, hd, hb2, hc2⟩
      have ha₁ : (sourceSanovA ^ (-m₀) * γ : SL(2, ℤ)).1 0 0 = γ.1 0 0 - 2 * m₀ * γ.1 1 0 := by
        rw [sourceSanovA_zpow_mul]
        simp
        ring
      have hc₁ : (sourceSanovA ^ (-m₀) * γ : SL(2, ℤ)).1 1 0 = γ.1 1 0 := by
        rw [sourceSanovA_zpow_mul]
        simp
      have hodd : (γ.1 0 0 - 2 * m₀ * γ.1 1 0) % 2 = 1 := by
        rw [show γ.1 0 0 - 2 * m₀ * γ.1 1 0 = γ.1 0 0 + 2 * -(m₀ * γ.1 1 0) from by ring,
          Int.add_mul_emod_self_left]
        omega
      have hceven : γ.1 1 0 % 2 = 0 := by
        obtain ⟨k, hk⟩ := hc2
        omega
      have hstrict : |γ.1 0 0 - 2 * m₀ * γ.1 1 0| < |γ.1 1 0| :=
        sourceSanov_abs_lt_of_parity hm₀ hodd hceven
      have ha₁0 : γ.1 0 0 - 2 * m₀ * γ.1 1 0 ≠ 0 := by
        intro h0
        rw [h0] at hodd
        omega

      obtain ⟨m₁, hm₁⟩ := sourceSanov_exists_balanced (γ.1 1 0) (γ.1 0 0 - 2 * m₀ * γ.1 1 0) ha₁0
      have h₂ : sourceSanovEntries (sourceSanovB ^ (-m₁) * (sourceSanovA ^ (-m₀) * γ)) :=
        sourceSanovEntries_B_mul (-m₁) _ h₁
      have hc₂ : (sourceSanovB ^ (-m₁) * (sourceSanovA ^ (-m₀) * γ) : SL(2, ℤ)).1 1 0
          = γ.1 1 0 - 2 * m₁ * (γ.1 0 0 - 2 * m₀ * γ.1 1 0) := by
        rw [sourceSanovB_zpow_mul, ha₁, hc₁]
        simp
        ring
      have hmeas : ((sourceSanovB ^ (-m₁) * (sourceSanovA ^ (-m₀) * γ) : SL(2, ℤ)).1 1 0).natAbs ≤ n := by
        have hlt : |γ.1 1 0 - 2 * m₁ * (γ.1 0 0 - 2 * m₀ * γ.1 1 0)| < |γ.1 1 0| :=
          lt_of_le_of_lt hm₁ hstrict
        rw [hc₂]
        rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at hlt
        omega
      have hrec := IH _ h₂ hmeas
      have hre : γ = sourceSanovA ^ m₀ * (sourceSanovB ^ m₁ * (sourceSanovB ^ (-m₁) * (sourceSanovA ^ (-m₀) * γ))) := by
        simp [zpow_neg, mul_inv_cancel_left]
      rw [hre]
      exact mul_mem (Subgroup.zpow_mem _ sourceSanovA_mem_range m₀)
        (mul_mem (Subgroup.zpow_mem _ sourceSanovB_mem_range m₁) hrec)

/-- Every matrix satisfying the required integer congruences lies in the actual free-word image. -/
theorem sourceSanov_mem_range (γ : SL(2, ℤ)) (h : sourceSanovEntries γ) :
    γ ∈ (FreeGroup.lift ![sourceSanovA, sourceSanovB] : FreeGroup (Fin 2) →* SL(2, ℤ)).range :=
  sourceSanov_mem_range_bounded (γ.1 1 0).natAbs γ h le_rfl


end
end Dubon2026
