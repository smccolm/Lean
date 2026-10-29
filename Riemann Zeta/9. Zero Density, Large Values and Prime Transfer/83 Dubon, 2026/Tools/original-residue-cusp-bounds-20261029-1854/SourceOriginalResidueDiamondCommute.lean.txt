import Dubon2026.SourceOriginalResidueDiamondFixedField

/-! DUB-17/18 -> original Gamma1 genus preservation -> reverse genus inequality
-> cusp residue fiber bounds -> transport stabilizers across an actual fiber.
The native Gamma0 residue homomorphism kills commutators, hence they lie in
Gamma1 and in the already proved exact kernel of the actual diamond action.
No extra abelian-action hypothesis or quotient infrastructure is introduced. -/
namespace Dubon2026.SourceFunctionField.IntegralDiamond
noncomputable section
open CongruenceSubgroup GammaOne
open scoped MatrixGroups
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
  [CharP (IsLocalRing.ResidueField A) ℓ]
local notation "kk" => IsLocalRing.ResidueField A
private local instance : Algebra kk (qExpFunctionFieldC kk (Gamma1 N)) :=
  (qExpFunctionFieldC kk (Gamma1 N)).toSubalgebra.algebra

theorem originalResidueDiamondAction_commute (hℓN : ¬ ℓ ∣ N) (γ δ : Gamma0 N) :
    Commute (originalResidueDiamondAction A N ℓ hℓN γ)
      (originalResidueDiamondAction A N ℓ hℓN δ) := by
  letI : Algebra (ZMod ℓ) kk := (ZMod.castHom (dvd_refl ℓ) kk).toAlgebra
  have hm : Gamma0Map N (γ * δ) = Gamma0Map N (δ * γ) := by
    rw [map_mul, map_mul, mul_comm]
  have hk : Gamma0Map N (γ * δ * (δ * γ)⁻¹) = 1 := by
    rw [map_mul, hm, ← map_mul, mul_inv_cancel, map_one]
  have hg : (γ * δ * (δ * γ)⁻¹).val ∈ Gamma1 N :=
    (Gamma1_mem N _).mpr ((Gamma1_to_Gamma0_mem _).mp ((Gamma1_mem').mpr hk))
  have hρ : originalResidueDiamondAction A N ℓ hℓN (γ * δ * (δ * γ)⁻¹) = 1 :=
    (reducedFieldActionOver_eq_one_iff kk N ℓ hℓN _).mpr (le_plusMinus _ hg)
  rw [map_mul, map_inv, mul_inv_eq_one] at hρ
  simpa only [map_mul] using hρ

end
end Dubon2026.SourceFunctionField.IntegralDiamond
