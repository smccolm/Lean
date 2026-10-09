import Dubon2026.FiniteAdeleResidueChangeLevel
import Dubon2026.AdelicDirichletQuadratic
import Dubon2026.AdelicQuadraticCharacterRigidity

/-! # Primitive descent preserves the actual full quadratic Dirichlet idele character -/

namespace Dubon2026

noncomputable section

/-- Genuine change of Dirichlet modulus preserves quadraticity. -/
theorem dirichlet_changeLevel_quadratic {M D : ℕ} (χ : DirichletCharacter ℂ M)
    (h : M ∣ D) (hχ : χ.IsQuadratic) : (DirichletCharacter.changeLevel h χ).IsQuadratic := by
  apply MulChar.isQuadratic_iff_sq_eq_one.mpr
  rw [← map_pow, hχ.sq_eq_one, map_one]

/-- The genuine primitive inducing character of a quadratic Dirichlet character is quadratic. -/
theorem dirichlet_primitiveCharacter_quadratic {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (hχ : χ.IsQuadratic) : χ.primitiveCharacter.IsQuadratic := by
  apply MulChar.isQuadratic_iff_sq_eq_one.mpr
  apply DirichletCharacter.changeLevel_injective (R := ℂ) χ.conductor_dvd_level
  rw [map_pow, map_one, χ.changeLevel_primitiveCharacter, hχ.sq_eq_one]

/-- Changing a quadratic Dirichlet modulus leaves its character on every original full idele unchanged. -/
theorem adelicDirichletCharacter_changeLevel {M D : ℕ} [NeZero M] [NeZero D]
    (χ : DirichletCharacter ℂ M) (h : M ∣ D) (hχ : χ.IsQuadratic) :
    adelicDirichletCharacter (DirichletCharacter.changeLevel h χ) = adelicDirichletCharacter χ := by
  apply adelicQuadraticCharacter_eq_of_integral
    (adelicDirichletCharacter (DirichletCharacter.changeLevel h χ)) (adelicDirichletCharacter χ)
    (adelicDirichletCharacter_quadratic _ (dirichlet_changeLevel_quadratic χ h hχ))
    (adelicDirichletCharacter_quadratic χ hχ)
    (adelicDirichletCharacter_rational _) (adelicDirichletCharacter_rational χ)
  intro u
  rw [adelicDirichletCharacter_integral, adelicDirichletCharacter_integral,
    dirichlet_changeLevel_integral_residue]

/-- Primitive descent preserves the entire actual idele character, including its genuine real factor. -/
theorem adelicDirichletCharacter_primitive {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (hχ : χ.IsQuadratic) :
    letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    adelicDirichletCharacter χ.primitiveCharacter = adelicDirichletCharacter χ := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have he := adelicDirichletCharacter_changeLevel χ.primitiveCharacter χ.conductor_dvd_level
    (dirichlet_primitiveCharacter_quadratic χ hχ)
  rw [χ.changeLevel_primitiveCharacter] at he
  exact he.symm

/-- The actual trivial Dirichlet character induces the trivial character on all original full ideles. -/
theorem adelicDirichletCharacter_one (D : ℕ) [NeZero D] :
    adelicDirichletCharacter (1 : DirichletCharacter ℂ D) = 1 := by
  have hq : (1 : DirichletCharacter ℂ D).IsQuadratic :=
    MulChar.isQuadratic_iff_sq_eq_one.mpr (one_pow 2)
  apply adelicQuadraticCharacter_eq_of_integral _ _
    (adelicDirichletCharacter_quadratic _ hq) (fun _ => one_pow 2)
    (adelicDirichletCharacter_rational _) (fun _ => rfl)
  intro u
  rw [adelicDirichletCharacter_integral,
    MulChar.one_apply (u.isUnit.map (finiteAdeleResidue D)), inv_one]
  rfl

end
end Dubon2026
