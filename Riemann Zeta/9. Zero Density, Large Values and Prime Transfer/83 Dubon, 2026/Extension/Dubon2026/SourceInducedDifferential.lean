import Dubon2026.SourceRegularDifferentialEvaluation
import Dubon2026.IntegralHighestWeightAction

/-! Preservation of the actual source coefficient module by differentiation.
The original all-algebra Borel covariance is evaluated over dual numbers
and its epsilon coefficient proves the required stability. This removes
the induced-action certificate in the coefficient irreducibility chain.
-/

namespace Dubon2026
noncomputable section
open Matrix TrivSqZeroExt

universe u
variable (R : Type u) [CommRing R] (n : ℕ) (lam : Fin n → ℤ)

/-- Differentiating the original right action preserves the exact source Borel covariance over every coefficient algebra. -/
theorem sourceRegularDifferential_induced_mem
    (X : Matrix (Fin n) (Fin n) R) {p : GeneralLinearRegularFunctions R n}
    (hp : p ∈ generalLinearIntegralInducedSubmodule R n lam) :
    sourceRegularDifferential X p ∈ generalLinearIntegralInducedSubmodule R n lam := by
  intro A _ _ g b
  rw [sourceRegularDifferential_eval, sourceRegularDifferential_eval]
  have hpoint : sourceInfinitesimalPointAt X (b.val * g) =
      (integralWeightBorelBaseChange A (DualNumber A) n b).val *
        sourceInfinitesimalPointAt X g := by
    change GeneralLinearGroup.map (inlAlgHom R A A).toRingHom (b.val * g) *
        sourceInfinitesimalMatrix (X.map (algebraMap R A)) =
      GeneralLinearGroup.map (algebraMap A (DualNumber A)) b.val *
        (GeneralLinearGroup.map (inlAlgHom R A A).toRingHom g *
          sourceInfinitesimalMatrix (X.map (algebraMap R A)))
    rw [map_mul, mul_assoc]
    rfl
  rw [hpoint]
  have hcov := hp (DualNumber A) (sourceInfinitesimalPointAt X g)
    (integralWeightBorelBaseChange A (DualNumber A) n b)
  have hw : (generalLinearBorelWeight lam
      (integralWeightBorelBaseChange A (DualNumber A) n b) : DualNumber A) =
      inl (generalLinearBorelWeight lam b : A) := by
    rw [generalLinearBorelWeight_apply,
      integralWeightBorelBaseChange_character A (DualNumber A) n (fun i => lam i.rev) b]
    rfl
  rw [hcov, hw]
  simp

/-- The differential acts on the original source-induced functions themselves. -/
def sourceInducedDifferential (X : Matrix (Fin n) (Fin n) R) :
    Module.End R (generalLinearIntegralInducedSubmodule R n lam) where
  toFun p := ⟨sourceRegularDifferential X p.val,
    sourceRegularDifferential_induced_mem R n lam X p.property⟩
  map_add' p q := Subtype.ext (map_add (sourceRegularDifferential X) p.val q.val)
  map_smul' r p := Subtype.ext ((sourceRegularDifferential X).toLinearMap.map_smul r p.val)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The original induced module carries the Lie action obtained by differentiating its exact right-translation action. -/
def sourceInducedDifferentialLieHom :
    Matrix (Fin n) (Fin n) R →ₗ⁅R⁆
      Module.End R (generalLinearIntegralInducedSubmodule R n lam) where
  toFun := sourceInducedDifferential R n lam
  map_add' X Y := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    exact congrArg (fun D => D p.val) (sourceRegularDifferential_add X Y)
  map_smul' r X := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    exact congrArg (fun D => D p.val) (sourceRegularDifferential_smul r X)
  map_lie' {X Y} := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    exact congrArg (fun D => D p.val) (sourceRegularDifferential_lie X Y)

end
end Dubon2026
