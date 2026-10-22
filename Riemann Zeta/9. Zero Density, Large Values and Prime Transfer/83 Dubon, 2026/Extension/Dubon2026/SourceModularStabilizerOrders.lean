import Dubon2026.SourceEllipticPointValues

/-! DUB-17/18 -> numerical modular genus -> elliptic ramification ->
the exact analytic multiplicity of j at each upper-half-plane point.
The required derivative identity follows from native level-one dimension
and discriminant division. This avoids adding a general Ramanujan system
or elliptic-curve uniformization. Full modular orbit separation identifies
the two exceptional fibers with the actual elliptic-point stabilizers.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two.
-/
namespace Dubon2026.SourceFunctionField.JMultiplicity
noncomputable section
open UpperHalfPlane ModularForm Complex SlashInvariantForm Derivative Filter ModularGroup
open scoped MatrixGroups Real Topology ModularForm Manifold Derivative Modular
local notation "Δ" => ModularForm.discriminant
theorem natCard_stabilizer_I : Nat.card (MulAction.stabilizer SL(2, ℤ) UpperHalfPlane.I) = 4 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight
    (q := fun g => g ∈ ({1, -1, ModularGroup.S, -ModularGroup.S} : Finset SL(2, ℤ)))
    (fun g => (MulAction.mem_stabilizer_iff).trans ModularGroup.stabilizer_I)),
    Nat.card_eq_finsetCard]
  decide

theorem natCard_stabilizer_ρ : Nat.card (MulAction.stabilizer SL(2, ℤ) ρ) = 6 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight
    (q := fun g => g ∈ ({1, -1, ModularGroup.S * ModularGroup.T, -(ModularGroup.S * ModularGroup.T),
      ModularGroup.T⁻¹ * ModularGroup.S, -(ModularGroup.T⁻¹ * ModularGroup.S)} : Finset SL(2, ℤ)))
    (fun g => (MulAction.mem_stabilizer_iff).trans ModularGroup.stabilizer_ρ)),
    Nat.card_eq_finsetCard]
  decide

theorem natCard_stabilizer_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    Nat.card (MulAction.stabilizer SL(2, ℤ) (γ • τ)) =
      Nat.card (MulAction.stabilizer SL(2, ℤ) τ) :=
  (Nat.card_congr (MulAction.stabilizerEquivStabilizer (rfl : γ • τ = γ • τ)).toEquiv).symm

theorem orbit_trichotomy (τ : ℍ) :
    (∃ γ : SL(2, ℤ), τ = γ • UpperHalfPlane.I) ∨ (∃ γ : SL(2, ℤ), τ = γ • ρ) ∨
      (∀ g : SL(2, ℤ), g • τ = τ → g = 1 ∨ g = -1) := by
  obtain ⟨g₀, hg₀⟩ := ModularGroup.exists_smul_mem_fd τ
  by_cases hI : g₀ • τ = UpperHalfPlane.I
  · exact Or.inl ⟨g₀⁻¹, by rw [← hI, inv_smul_smul]⟩
  by_cases hρ : g₀ • τ = ρ
  · exact Or.inr (Or.inl ⟨g₀⁻¹, by rw [← hρ, inv_smul_smul]⟩)
  by_cases hρ' : g₀ • τ = (1 : ℝ) +ᵥ ρ
  · refine Or.inr (Or.inl ⟨g₀⁻¹ * ModularGroup.T, ?_⟩)
    rw [mul_smul, UpperHalfPlane.modular_T_smul, ← hρ', inv_smul_smul]
  refine Or.inr (Or.inr fun g hg => ?_)
  have h : (g₀ * g * g₀⁻¹) • (g₀ • τ) = g₀ • τ := by
    rw [mul_smul, mul_smul, inv_smul_smul, hg]
  rcases ModularGroup.stabilizer_of_ne hg₀ h hI hρ hρ' with h1 | h1
  · left
    have := congrArg (fun x => g₀⁻¹ * x * g₀) h1
    simpa [mul_assoc] using this
  · right
    have := congrArg (fun x => g₀⁻¹ * x * g₀) h1
    simpa [mul_assoc] using this

theorem natCard_stabilizer_eq_two {τ : ℍ} (h : ∀ g : SL(2, ℤ), g • τ = τ → g = 1 ∨ g = -1) :
    Nat.card (MulAction.stabilizer SL(2, ℤ) τ) = 2 := by
  have hiff : ∀ g : SL(2, ℤ), g ∈ MulAction.stabilizer SL(2, ℤ) τ ↔
      g ∈ ({1, -1} : Finset SL(2, ℤ)) := by
    intro g
    rw [MulAction.mem_stabilizer_iff, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨h g, ?_⟩
    rintro (rfl | rfl)
    · exact one_smul _ _
    · rw [ModularGroup.SL_neg_smul, one_smul]
  rw [Nat.card_congr (Equiv.subtypeEquivRight
    (q := fun g => g ∈ ({1, -1} : Finset SL(2, ℤ))) hiff), Nat.card_eq_finsetCard]
  decide


end
end Dubon2026.SourceFunctionField.JMultiplicity
