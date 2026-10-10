import Dubon2026.RelativeMaximalCotangentUniversal
import Dubon2026.OriginalResidueCotangentLinearity

/-! # Actual original residue derivations and relative maximal-ideal cotangent maps -/

namespace Dubon2026

noncomputable section

variable {O R : Type} [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R]

/-- Maps from the genuine relative maximal-ideal quotient to the original residue point's actual epsilon ideal, with its original coefficient action. -/
abbrev OriginalResidueMaximalCotangentMaps
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O) :=
  letI := (originalResidueConstantDualLift eR).toRingHom.toAlgebra
  RelativeMaximalCotangent O R →ₗ[R]
    (TrivSqZeroExt.kerIdeal (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O))

/-- The original residue field acts on genuine maximal-ideal cotangent maps through their actual epsilon coefficients. -/
instance originalResidueMaximalCotangentMapsModule
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O) :
    Module (IsLocalRing.ResidueField O) (OriginalResidueMaximalCotangentMaps eR) := by
  let K := IsLocalRing.ResidueField O
  letI := (originalResidueConstantDualLift eR).toRingHom.toAlgebra
  letI : SMulCommClass R K (TrivSqZeroExt.kerIdeal K K) := by
    refine ⟨?_⟩
    intro r k x
    apply Subtype.ext
    simp only [Submodule.coe_smul_of_tower, Algebra.smul_def]
    exact mul_left_comm _ _ _
  exact inferInstanceAs (Module K
    (RelativeMaximalCotangent O R →ₗ[R] TrivSqZeroExt.kerIdeal K K))

/-- The actual original maximal ideal annihilates the genuine epsilon ideal under the original constant residue coefficient action. -/
theorem originalResidueEpsilon_torsion
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O) :
    (letI := (originalResidueConstantDualLift eR).toRingHom.toAlgebra
     Module.IsTorsionBySet R
       (TrivSqZeroExt.kerIdeal (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O))
       (IsLocalRing.maximalIdeal R)) := by
  letI := (originalResidueConstantDualLift eR).toRingHom.toAlgebra
  intro x r
  apply Subtype.ext
  change originalResidueConstantDualLift eR r.val * x.val = 0
  have hres := (localCoefficientReduction_eq_zero_iff eR r.val).mpr r.property
  have hzero : originalResidueConstantDualLift eR r.val = 0 := by
    change TrivSqZeroExt.inl (localCoefficientReduction eR r.val) = 0
    rw [hres, TrivSqZeroExt.inl_zero]
  rw [hzero, zero_mul]

/-- The genuine relative maximal-ideal cotangent maps classify original relative residue derivations linearly over the original residue field. -/
def originalResidueMaximalCotangentDerivationLinearEquiv
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O) :
    OriginalResidueMaximalCotangentMaps eR ≃ₗ[IsLocalRing.ResidueField O]
      OriginalResidueDerivations eR := by
  let K := IsLocalRing.ResidueField O
  letI := (originalResidueConstantDualLift eR).toRingHom.toAlgebra
  letI : IsScalarTower O R (DualNumber K) :=
    IsScalarTower.of_algHom (originalResidueConstantDualLift eR)
  refine { (relativeMaximalCotangentDerivationEquiv eR
      (originalResidueEpsilon_torsion eR)).toEquiv with
    map_add' := ?_, map_smul' := ?_ }
  · intro f g
    apply Derivation.ext
    intro r
    rfl
  · intro k f
    apply Derivation.ext
    intro r
    rfl

/-- The actual maximal-ideal cotangent comparison retains the universal derivative of every original ring element. -/
theorem originalResidueMaximalCotangentDerivationLinearEquiv_apply
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : OriginalResidueMaximalCotangentMaps eR) (r : R) :
    originalResidueMaximalCotangentDerivationLinearEquiv eR f r =
      f (relativeMaximalCotangentDerivation eR r) := rfl

/-- The universal differential and the literal relative maximal-ideal quotient give the same original residue tangent maps by a genuine residue-field-linear equivalence. -/
def originalResidueMaximalCotangentLinearEquiv
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O) :
    OriginalResidueMaximalCotangentMaps eR ≃ₗ[IsLocalRing.ResidueField O]
      OriginalResidueCotangentMaps eR :=
  (originalResidueMaximalCotangentDerivationLinearEquiv eR).trans
    (originalResidueCotangentDerivationLinearEquiv eR).symm

/-- On each original universal differential, the genuine comparison is evaluation of the original relative maximal-ideal class. -/
theorem originalResidueMaximalCotangentLinearEquiv_apply
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : OriginalResidueMaximalCotangentMaps eR) (r : R) :
    originalResidueMaximalCotangentLinearEquiv eR f (KaehlerDifferential.D O R r) =
      f (relativeMaximalCotangentDerivation eR r) := by
  change originalResidueCotangentDerivationLinearEquiv eR
    ((originalResidueCotangentDerivationLinearEquiv eR).symm
      (originalResidueMaximalCotangentDerivationLinearEquiv eR f)) r = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

end
end Dubon2026
