/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the upstream LICENSE.
Place actions adapted from NYLL ClassFieldTheory, commit
dc55774a7fe03e742f2b4c6114aab5e7d01edfb1,
Nyll/ClassFieldTheory/AlgebraicNumberTheory/SUnit/GaloisAction.lean.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Dubon2026.SUnitFullLogLattice
import Dubon2026.NumberFieldGaloisAbsoluteValues
import Dubon2026.NumberFieldSUnitGaloisAction

/-! # The original actions on the places of the S-unit logarithm

The existing original finite-prime and infinite-place actions combine on
the precise place set used in the proved logarithmic product formula.
The resulting permutation action on coordinates is the representation
needed for DUB-17's S-unit Herbrand quotient.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The actual finite-prime permutation restricted to the specified stable support. -/
@[reducible]
def sUnitStableFinitePlaceAction : MulAction Gal(L/K) S where
  smul σ v := ⟨numberFieldGaloisPlaceEquiv K L σ v.val, (hS σ v.val).mp v.property⟩
  one_smul v := Subtype.ext (numberFieldGaloisPlaceEquiv_one K L v.val)
  mul_smul σ τ v := Subtype.ext (numberFieldGaloisPlaceEquiv_mul K L σ τ v.val)

/-- The actual permutation action on all original logarithmic places. -/
@[reducible]
def sUnitLogPlaceAction : MulAction Gal(L/K) (SUnitLogPlace L S) := by
  letI := sUnitStableFinitePlaceAction K L S hS
  exact {
    smul := fun σ p => match p with
      | Sum.inl w => Sum.inl (σ • w)
      | Sum.inr v => Sum.inr (σ • v)
    one_smul := by
      intro p
      cases p with
      | inl w => exact congrArg Sum.inl (one_smul Gal(L/K) w)
      | inr v => exact congrArg Sum.inr (one_smul Gal(L/K) v)
    mul_smul := by
      intro σ τ p
      cases p with
      | inl w => exact congrArg Sum.inl (mul_smul σ τ w)
      | inr v => exact congrArg Sum.inr (mul_smul σ τ v) }

/-- The actual original S-unit action in additive notation. -/
@[reducible]
def sUnitAdditiveGaloisAction :
    DistribMulAction Gal(L/K) (Additive ((S : Set (HeightOneSpectrum (𝓞 L))).unit L)) := by
  letI := numberFieldSUnitGaloisAction K L S hS
  exact {
    smul := fun σ x => Additive.ofMul (σ • x.toMul)
    one_smul := fun x => congrArg Additive.ofMul (one_smul Gal(L/K) x.toMul)
    mul_smul := fun σ τ x => congrArg Additive.ofMul (mul_smul σ τ x.toMul)
    smul_zero := fun σ => congrArg Additive.ofMul (smul_one σ)
    smul_add := fun σ x y => congrArg Additive.ofMul (smul_mul' σ x.toMul y.toMul) }

/-- Coordinate permutation by the inverse original place action. -/
@[reducible]
def sUnitFullLogSpaceAction : DistribMulAction Gal(L/K) (SUnitFullLogSpace L S) := by
  letI := sUnitLogPlaceAction K L S hS
  exact {
    smul := fun σ z p => z (σ⁻¹ • p)
    one_smul := by
      intro z
      funext p
      change z ((1 : Gal(L/K))⁻¹ • p) = z p
      rw [inv_one, one_smul]
    mul_smul := by
      intro σ τ z
      funext p
      change z ((σ * τ)⁻¹ • p) = z (τ⁻¹ • (σ⁻¹ • p))
      rw [mul_inv_rev, mul_smul]
    smul_zero := fun _ => rfl
    smul_add := fun _ _ _ => rfl }

/-- The original coordinate sum is invariant under the original place permutation. -/
theorem sUnitLogCoordinateSum_galois (σ : Gal(L/K)) (z : SUnitFullLogSpace L S) :
    letI := sUnitFullLogSpaceAction K L S hS
    sUnitLogCoordinateSum L S (σ • z) = sUnitLogCoordinateSum L S z := by
  letI := sUnitLogPlaceAction K L S hS
  change (∑ p : SUnitLogPlace L S, z (σ⁻¹ • p)) = ∑ p, z p
  exact Fintype.sum_equiv (MulAction.toPerm σ⁻¹) _ z (fun _ => rfl)

end
end Dubon2026
