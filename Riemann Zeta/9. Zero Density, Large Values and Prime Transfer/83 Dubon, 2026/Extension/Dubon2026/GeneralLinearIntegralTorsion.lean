import Dubon2026.GeneralLinearIntegralInduction
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.LinearAlgebra.FreeModule.PID

/-! Torsion freeness of the literal integral induced coefficient module.
This removes the torsion-free hypothesis in the PID freeness step on
DUB-17's coefficient-module chain. Finite generation is proved downstream in IntegralInducedFiniteFree.
The generic determinant's nonvanishing and localization-domain arguments
are reused directly from the pinned Mathlib.
-/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable (R : Type u) [CommRing R] [IsDomain R] (n : ℕ)

/-- The original determinant localization inverts only non-zero-divisors. -/
theorem generalLinearRegular_powers_le_nonZeroDivisors :
    Submonoid.powers (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R)) ≤
      nonZeroDivisors (MvPolynomial (Fin n × Fin n) R) := by
  rintro x ⟨m, rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mpr
    (pow_ne_zero m (Matrix.det_mvPolynomialX_ne_zero (Fin n) R))

/-- The original polynomial coordinates embed faithfully into the actual regular-function ring. -/
theorem generalLinearRegularPolynomialMap_injective :
    Function.Injective (generalLinearRegularPolynomialMap R n) :=
  IsLocalization.injective _ (generalLinearRegular_powers_le_nonZeroDivisors R n)

/-- Regular functions on the original general-linear group over a domain form a domain. -/
instance generalLinearRegularIsDomain : IsDomain (GeneralLinearRegularFunctions R n) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors _
    (generalLinearRegular_powers_le_nonZeroDivisors R n)

/-- The coefficient ring embeds faithfully into the original general-linear regular functions. -/
theorem generalLinearRegular_algebraMap_injective :
    Function.Injective (algebraMap R (GeneralLinearRegularFunctions R n)) := by
  rw [IsScalarTower.algebraMap_eq R (MvPolynomial (Fin n × Fin n) R)
    (GeneralLinearRegularFunctions R n)]
  exact (generalLinearRegularPolynomialMap_injective R n).comp
    (MvPolynomial.C_injective (Fin n × Fin n) R)

/-- The original regular functions have no coefficient torsion. -/
instance generalLinearRegularIsTorsionFree :
    Module.IsTorsionFree R (GeneralLinearRegularFunctions R n) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro a p hp
  rw [Algebra.smul_def] at hp
  rcases mul_eq_zero.mp hp with ha | hp
  · exact Or.inl ((generalLinearRegular_algebraMap_injective R n) (by simpa using ha))
  · exact Or.inr hp

/-- The exact source Borel-induced module inherits torsion freeness from its actual regular functions. -/
instance generalLinearIntegralInducedIsTorsionFree (lam : Fin n → ℤ) :
    Module.IsTorsionFree R (generalLinearIntegralInducedSubmodule R n lam) := inferInstance

/-- Over the source PID, finite generation is the only remaining module-theoretic input to freeness of the exact induced module. -/
theorem generalLinearIntegralInduced_free_of_finite [IsPrincipalIdealRing R]
    (lam : Fin n → ℤ) [Module.Finite R (generalLinearIntegralInducedSubmodule R n lam)] :
    Module.Free R (generalLinearIntegralInducedSubmodule R n lam) := inferInstance

end
end Dubon2026
