import Dubon2026.SourceGammaOneIntegralCharacterFactor
import Dubon2026.SourceGammaOneIntegralParabolicLift

/-! DUB17/18 -> original all-weight arithmetic realization -> finite
Gamma1 parabolic H1. Native integral lifting and the proved integer
period-kernel factorization identify modulus characters vanishing on
parabolic and finite-order elements with the dual of the actual period
lattice. The finite-order condition is retained explicitly; no assertion
about all parabolic finite characters is inferred here. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open CongruenceSubgroup
open scoped MatrixGroups
variable (M : ℕ) [NeZero M] (n : ℕ)

/-- Modulus characters trivial on the actual parabolic and elliptic elements. -/
def finiteParabolicHoms : Submodule (ZMod n) (Additive (Gamma1 M) →+ ZMod n) where
  carrier := {φ | (∀ γ : Gamma1 M, γ.val.val.trace ^ 2 = 4 →
      φ (Additive.ofMul γ) = 0) ∧
    ∀ γ : Gamma1 M, IsOfFinOrder γ → φ (Additive.ofMul γ) = 0}
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  add_mem' ha hb := ⟨fun γ hγ => by
    rw [AddMonoidHom.add_apply, ha.1 γ hγ, hb.1 γ hγ, add_zero],
    fun γ hγ => by rw [AddMonoidHom.add_apply, ha.2 γ hγ, hb.2 γ hγ, add_zero]⟩
  smul_mem' c _ h := ⟨fun γ hγ => by rw [AddMonoidHom.smul_apply, h.1 γ hγ, smul_zero],
    fun γ hγ => by rw [AddMonoidHom.smul_apply, h.2 γ hγ, smul_zero]⟩

/-- Pull back a dual lattice character along the original group-period map. -/
def finiteLatticeCharacterMap :
    (sourceWeightTwoIntegralLattice (Gamma1 M) →+ ZMod n) →ₗ[ZMod n]
      finiteParabolicHoms M n where
  toFun ψ := ⟨ψ.comp (latticePeriodHom M), ⟨fun γ hγ => by
    rw [AddMonoidHom.comp_apply, latticePeriodHom_parabolic M γ hγ, map_zero],
    fun γ hγ => by
      rw [AddMonoidHom.comp_apply, latticePeriodHom_finite_order M γ hγ, map_zero]⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finiteLatticeCharacterMap_injective :
    Function.Injective (finiteLatticeCharacterMap M n) := by
  intro ψ χ h
  apply AddMonoidHom.ext
  intro l
  obtain ⟨γ, rfl⟩ := latticePeriodHom_surjective M l
  exact congrArg (fun φ : finiteParabolicHoms M n => φ.val γ) h

theorem finiteLatticeCharacterMap_surjective :
    Function.Surjective (finiteLatticeCharacterMap M n) := by
  intro φ
  obtain ⟨x, hx, hcast⟩ := sourceGamma1_integral_parabolic_character_lift M n
    φ.val φ.property.1 φ.property.2
  obtain ⟨ψ, hψ⟩ := exists_integer_lattice_factor M x hx
  refine ⟨(Int.castAddHom (ZMod n)).comp ψ, Subtype.ext ?_⟩
  change ((Int.castAddHom (ZMod n)).comp ψ).comp (latticePeriodHom M) = φ.val
  rw [AddMonoidHom.comp_assoc, hψ, hcast]

/-- The original period pullback identifies the dual lattice with these actual characters. -/
def finiteLatticeCharacterEquiv :
    (sourceWeightTwoIntegralLattice (Gamma1 M) →+ ZMod n) ≃ₗ[ZMod n]
      finiteParabolicHoms M n :=
  LinearEquiv.ofBijective (finiteLatticeCharacterMap M n)
    ⟨finiteLatticeCharacterMap_injective M n, finiteLatticeCharacterMap_surjective M n⟩

theorem finiteLatticeCharacterEquiv_apply
    (ψ : sourceWeightTwoIntegralLattice (Gamma1 M) →+ ZMod n) (γ : Gamma1 M) :
    (finiteLatticeCharacterEquiv M n ψ).val (Additive.ofMul γ) =
      ψ (latticePeriodHom M (Additive.ofMul γ)) := rfl

end
end Dubon2026.SourceFunctionField.GammaOne
