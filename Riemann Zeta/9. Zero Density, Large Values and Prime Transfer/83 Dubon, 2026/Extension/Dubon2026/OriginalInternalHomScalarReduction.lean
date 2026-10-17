import Dubon2026.OriginalScalarReductionSequence

/-! # The actual reduction map on original internal Hom

Each original linear map descends to the literal scalar reductions of
its source and target. The descended values intertwine the original
internal-Hom actions. This is the actual mod-p comparison map required
to lift the proved mod-p classification to integral projectivity for
DUB-17's fundamental coefficient.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

variable {k G : Type} [CommRing k] [Group G] (A R : Rep.{0} k G) (m : k)

/-- An original linear map respects the actual scalar-image quotients. -/
theorem originalInternalHomReduction_wellDefined (φ : A →ₗ[k] R) :
    originalScalarImage A m ≤ LinearMap.ker ((originalScalarImage R m).mkQ ∘ₗ φ) := by
  rintro x ⟨a, ha⟩
  change (originalScalarMultiplication A m).hom a = x at ha
  rw [originalScalarMultiplication_apply] at ha
  subst x
  change (originalScalarImage R m).mkQ (φ (m • a)) = 0
  rw [map_smul]
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    ⟨φ a, originalScalarMultiplication_apply R m (φ a)⟩

/-- The original linear map reduced on both its actual source and target. -/
def originalInternalHomReductionLinear :
    (A →ₗ[k] R) →ₗ[k] (originalScalarReduction A m →ₗ[k] originalScalarReduction R m) where
  toFun φ := (originalScalarImage A m).liftQ ((originalScalarImage R m).mkQ ∘ₗ φ)
    (originalInternalHomReduction_wellDefined A R m φ)
  map_add' φ ψ := Submodule.linearMap_qext _ (LinearMap.ext fun a => by
    exact (originalScalarImage R m).mkQ.map_add _ _)
  map_smul' r φ := Submodule.linearMap_qext _ (LinearMap.ext fun a => by
    exact (originalScalarImage R m).mkQ.map_smul r _)

/-- The actual internal-Hom reduction retains exactly the original map's reduced value on every original element. -/
theorem originalInternalHomReductionLinear_mk (φ : A →ₗ[k] R) (a : A) :
    originalInternalHomReductionLinear A R m φ ((originalScalarImage A m).mkQ a) =
      (originalScalarImage R m).mkQ (φ a) := rfl

/-- The actual scalar reduction intertwines the original internal-Hom actions. -/
def originalInternalHomReduction : (Rep.ihom A).obj R ⟶
    (Rep.ihom (originalScalarReduction A m)).obj (originalScalarReduction R m) :=
  Rep.ofHom ⟨originalInternalHomReductionLinear A R m, fun g => by
    apply LinearMap.ext
    intro φ
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro a
    rfl⟩

/-- Scalar multiplication of the original map is killed by literal reduction. -/
theorem originalInternalHomReduction_scalar_zero (φ : A →ₗ[k] R) :
    originalInternalHomReductionLinear A R m (m • φ) = 0 := by
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro a
  change (originalScalarImage R m).mkQ (m • φ a) = 0
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    ⟨φ a, originalScalarMultiplication_apply R m (φ a)⟩

end
end Dubon2026
