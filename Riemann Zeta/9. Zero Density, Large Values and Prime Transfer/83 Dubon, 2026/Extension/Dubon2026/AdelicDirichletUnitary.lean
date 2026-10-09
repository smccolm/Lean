import Dubon2026.AdelicDirichletPrincipal
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-! # The genuine original Dirichlet idèle character is unitary -/

namespace Dubon2026

noncomputable section
open NumberField IsDedekindDomain

variable {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)

/-- The actual finite-idele character has modulus one at every original finite idele. -/
theorem finiteIdeleDirichletCharacter_norm (a : (FiniteAdeleRing ℤ ℚ)ˣ) :
    ‖finiteIdeleDirichletCharacter χ a‖ = 1 := by
  have he : ‖χ (finiteAdeleResidue D (finiteIdeleIntegralUnitHom a).val)‖ = 1 :=
    χ.unit_norm_eq_one (Units.map (finiteAdeleResidue D).toMonoidHom (finiteIdeleIntegralUnitHom a))
  change ‖(χ (finiteAdeleResidue D (finiteIdeleIntegralUnitHom a).val))⁻¹‖ = 1
  rw [norm_inv, he, inv_one]

omit [NeZero D] in
/-- The original real sign character has modulus one on the actual real unit group. -/
theorem realDirichletSignCharacter_norm (u : ℝˣ) : ‖realDirichletSignCharacter χ u‖ = 1 :=
  χ.unit_norm_eq_one (Units.map (SignType.castHom (α := ZMod D)).toMonoidHom
    (Units.map (signHom (α := ℝ)).toMonoidHom u))

/-- Every value of the constructed original full continuous Dirichlet idèle character has modulus one. -/
theorem adelicDirichletCharacter_norm (a : (AdeleRing ℤ ℚ)ˣ) :
    ‖adelicDirichletCharacter χ a‖ = 1 := by
  rw [adelicDirichletCharacter_apply, norm_mul, realDirichletSignCharacter_norm,
    finiteIdeleDirichletCharacter_norm, mul_one]

end
end Dubon2026
