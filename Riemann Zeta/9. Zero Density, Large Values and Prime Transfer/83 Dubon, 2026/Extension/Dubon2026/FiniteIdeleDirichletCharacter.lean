import Dubon2026.FiniteIdeleIntegralNormalization
import Dubon2026.FiniteAdeleResidueRing
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-! # Actual finite-idele characters constructed from original Dirichlet characters

The inverse residue convention makes an unramified local prime uniformizer
have the original Dirichlet value. Continuity and the real sign factor for
the full idèle-class character are separate proof obligations.
-/

namespace Dubon2026

noncomputable section
open IsDedekindDomain

variable {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)

/-- The original Dirichlet character evaluated on the inverse residue of the canonical integral factor of an actual finite idele. -/
def finiteIdeleDirichletCharacter : (FiniteAdeleRing ℤ ℚ)ˣ →* ℂ where
  toFun a := (χ (finiteAdeleResidue D (finiteIdeleIntegralUnitHom a).val))⁻¹
  map_one' := by rw [map_one, Units.val_one, map_one, map_one, inv_one]
  map_mul' a b := by rw [map_mul, Units.val_mul, map_mul, map_mul, mul_inv]

/-- On actual integral units the finite-idele character is the inverse original residue character. -/
theorem finiteIdeleDirichletCharacter_integral (u : finiteAdeleIntegerSubringˣ) :
    finiteIdeleDirichletCharacter χ (Units.map finiteAdeleIntegerSubring.subtype.toMonoidHom u) =
      (χ (finiteAdeleResidue D u.val))⁻¹ := by
  change (χ (finiteAdeleResidue D
    (finiteIdeleIntegralUnitHom (Units.map finiteAdeleIntegerSubring.subtype.toMonoidHom u)).val))⁻¹ = _
  rw [finiteIdeleIntegralUnitHom_integral]

/-- The constructed actual finite character is trivial on every positive principal rational idele. -/
theorem finiteIdeleDirichletCharacter_positive_rational (q : ℚ) (hq : 0 < q) :
    finiteIdeleDirichletCharacter χ
      (Units.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)).toMonoidHom (Units.mk0 q (ne_of_gt hq))) = 1 := by
  change (χ (finiteAdeleResidue D (finiteIdeleIntegralUnitHom _).val))⁻¹ = 1
  rw [finiteIdeleIntegralUnitHom_positive_rational q hq, Units.val_one, map_one, map_one, inv_one]

end
end Dubon2026
