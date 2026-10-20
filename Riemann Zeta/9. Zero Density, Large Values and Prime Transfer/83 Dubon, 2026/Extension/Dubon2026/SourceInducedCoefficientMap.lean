import Dubon2026.SourceRegularCoefficientMap
import Dubon2026.GeneralLinearIntegralTorsion

/-! The original integral induction inside its changed coefficient ring.
The map preserves the literal covariance over all coefficient algebras.
Its injectivity is reduced to polynomial coefficient injectivity through
the original determinant localization, not an assumed representation model.
-/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] (n : ℕ)

/-- A faithful coefficient embedding induces a faithful map of the original regular functions. -/
theorem sourceRegularCoefficientMap_injective [IsDomain B]
    (h : Function.Injective (algebraMap R B)) :
    Function.Injective (sourceRegularCoefficientMap R B n) := by
  apply IsLocalization.injective_of_map_algebraMap_zero
    (GeneralLinearRegularFunctions R n)
    (M := Submonoid.powers (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R)))
    (sourceRegularCoefficientMap R B n)
  intro P hP
  change sourceRegularCoefficientMap R B n (generalLinearRegularPolynomialMap R n P) = 0 at hP
  rw [sourceRegularCoefficientMap_polynomial] at hP
  have hp : MvPolynomial.map (algebraMap R B) P = 0 :=
    (generalLinearRegularPolynomialMap_injective B n) (by simpa using hP)
  have hz : P = 0 := (MvPolynomial.map_injective (algebraMap R B) h) (by simpa using hp)
  rw [hz, map_zero]

/-- The literal induced covariance is preserved by original coefficient change over every new coefficient algebra. -/
theorem sourceInducedCoefficientMap_mem (lam : Fin n → ℤ)
    {p : GeneralLinearRegularFunctions R n}
    (hp : p ∈ generalLinearIntegralInducedSubmodule R n lam) :
    sourceRegularCoefficientMap R B n p ∈ generalLinearIntegralInducedSubmodule B n lam := by
  intro A _ _ g b
  letI : Algebra R A := Algebra.compHom A (algebraMap R B)
  letI : IsScalarTower R B A := IsScalarTower.of_algebraMap_eq' rfl
  rw [sourceRegularCoefficientMap_eval, sourceRegularCoefficientMap_eval]
  exact hp A g b

/-- The actual linear map from the original integral coefficient module to the same induction over the extended coefficient ring. -/
def sourceInducedCoefficientMap (lam : Fin n → ℤ) :
    generalLinearIntegralInducedSubmodule R n lam →ₗ[R]
      generalLinearIntegralInducedSubmodule B n lam where
  toFun p := ⟨sourceRegularCoefficientMap R B n p.val,
    sourceInducedCoefficientMap_mem R B n lam p.property⟩
  map_add' p q := Subtype.ext (map_add (sourceRegularCoefficientMap R B n) p.val q.val)
  map_smul' r p := Subtype.ext
    ((generalLinearRegularEval (R := R) (generalLinearRegularGeneric B n)).toLinearMap.map_smul r p.val)

/-- The actual coefficient-module map is injective whenever the original coefficient embedding is faithful. -/
theorem sourceInducedCoefficientMap_injective [IsDomain B]
    (h : Function.Injective (algebraMap R B)) (lam : Fin n → ℤ) :
    Function.Injective (sourceInducedCoefficientMap R B n lam) := by
  intro p q he
  apply Subtype.ext
  exact sourceRegularCoefficientMap_injective R B n h (congrArg Subtype.val he)

end
end Dubon2026
