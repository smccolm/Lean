import Dubon2026.HopfCoordinateAffineGroupScheme
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.LinearAlgebra.FreeModule.PID

/-! # Actual finite free affine coordinates of a finite flat scheme over a PID -/

namespace Dubon2026
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry
universe u

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/-- A finite flat original scheme over the spectrum of the original PID has a genuine
relative affine coordinate presentation with a finite free coordinate module. Coordinates
are the original global sections; the algebra map is recovered from its original structure
morphism by fully faithful spectrum. Finiteness and flatness are transported across the
actual affine isomorphism, and torsion-freeness over the PID gives freeness. -/
theorem finiteFlatScheme_exists_freeAffineCoordinates
    (X : Over (Spec (CommRingCat.of R))) [IsFinite X.hom] [AlgebraicGeometry.Flat X.hom] :
    ∃ A : CommAlgCat.{u} R, Module.Finite R A ∧ Module.Free R A ∧
      Nonempty ((coordinateRelativeSpec (R := R)).obj (op A) ≅ X) := by
  letI : IsAffine X.left := isAffine_of_isAffineHom X.hom
  let A := Scheme.Γ.obj (op X.left)
  let f : CommRingCat.of R ⟶ A := Spec.preimage (X.left.isoSpec.inv ≫ X.hom)
  letI : Algebra R A := f.hom.toAlgebra
  let B := CommAlgCat.of R A
  let e : (coordinateRelativeSpec (R := R)).obj (op B) ≅ X :=
    Over.isoMk X.left.isoSpec.symm (by
      change X.left.isoSpec.inv ≫ X.hom = Spec.map f
      exact (Spec.map_preimage (X.left.isoSpec.inv ≫ X.hom)).symm)
  have hfinite : IsFinite (Spec.map f) := by
    change IsFinite (Spec.map (Spec.preimage (X.left.isoSpec.inv ≫ X.hom)))
    rw [Spec.map_preimage]
    infer_instance
  have hflat : AlgebraicGeometry.Flat (Spec.map f) := by
    change AlgebraicGeometry.Flat (Spec.map (Spec.preimage (X.left.isoSpec.inv ≫ X.hom)))
    rw [Spec.map_preimage]
    infer_instance
  letI : Module.Finite R A :=
    RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff f).mp hfinite)
  letI : Module.Flat R A :=
    RingHom.flat_algebraMap_iff.mp (AlgebraicGeometry.Flat.SpecMap_iff.mp hflat)
  exact ⟨B, inferInstance, inferInstance, ⟨e⟩⟩

end
end Dubon2026
