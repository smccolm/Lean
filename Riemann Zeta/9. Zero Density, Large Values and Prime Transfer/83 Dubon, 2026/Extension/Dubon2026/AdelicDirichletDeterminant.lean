import Dubon2026.AdelicDirichletUnitary
import Mathlib.Topology.Algebra.Group.Matrix

/-! # The actual continuous unitary determinant character on the original adelic general-linear group -/

namespace Dubon2026

noncomputable section
open NumberField IsDedekindDomain Matrix

variable {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)

/-- The original full Dirichlet idèle character evaluated on the actual determinant of the original adelic matrix. -/
def adelicDirichletDeterminant : GeneralLinearGroup (Fin 2) (AdeleRing ℤ ℚ) →* ℂ :=
  (adelicDirichletCharacter χ).comp GeneralLinearGroup.det

/-- The determinant character retains the literal original matrix determinant. -/
theorem adelicDirichletDeterminant_apply (g : GeneralLinearGroup (Fin 2) (AdeleRing ℤ ℚ)) :
    adelicDirichletDeterminant χ g = adelicDirichletCharacter χ (GeneralLinearGroup.det g) := rfl

/-- The actual determinant character is continuous in the genuine adelic group topology. -/
theorem adelicDirichletDeterminant_continuous : Continuous (adelicDirichletDeterminant χ) :=
  (adelicDirichletCharacter_continuous χ).comp GeneralLinearGroup.continuous_det

/-- Every value of the original determinant character has modulus one. -/
theorem adelicDirichletDeterminant_norm (g : GeneralLinearGroup (Fin 2) (AdeleRing ℤ ℚ)) :
    ‖adelicDirichletDeterminant χ g‖ = 1 :=
  adelicDirichletCharacter_norm χ (GeneralLinearGroup.det g)

/-- The actual determinant character is trivial on every original principal rational matrix. -/
theorem adelicDirichletDeterminant_rational (g : GeneralLinearGroup (Fin 2) ℚ) :
    adelicDirichletDeterminant χ (GeneralLinearGroup.map (algebraMap ℚ (AdeleRing ℤ ℚ)) g) = 1 := by
  rw [adelicDirichletDeterminant_apply, GeneralLinearGroup.map_det]
  exact adelicDirichletCharacter_rational χ (GeneralLinearGroup.det g)

end
end Dubon2026
