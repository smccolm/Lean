import Dubon2026.FiniteFlatSchemeAffineCoordinates
import Dubon2026.AffineSchemeCoordinateGroupObject

/-! # Genuine finite free cocommutative Hopf coordinates of the original finite flat group scheme

The equality of base-algebra structures is explicit, so the recovered Hopf coordinates
and their original relative spectrum presentation refer to the same original base map.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry
universe u

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/-- The actual fiber products over the original base. -/
local instance finiteFlatCoordinatesCartesian : CartesianMonoidalCategory (Over (Spec (CommRingCat.of R))) :=
  Over.cartesianMonoidalCategory _

/-- Fix the original fiber-product monoidal structure explicitly. -/
local instance finiteFlatCoordinatesMonoidal : MonoidalCategory (Over (Spec (CommRingCat.of R))) :=
  finiteFlatCoordinatesCartesian.toSemiCartesianMonoidalCategory.toMonoidalCategory

/-- Use the same original fiber-product symmetry. -/
local instance finiteFlatCoordinatesBraided : BraidedCategory (Over (Spec (CommRingCat.of R))) :=
  Over.braidedCategory _

/-- Construct finite free cocommutative Hopf coordinates from the actual original finite flat
commutative group scheme. The Hopf base algebra is exactly its original affine-coordinate base
algebra. The underlying relative spectrum is genuinely isomorphic to the same original scheme;
the separate point comparison must still identify its group and Galois actions. -/
theorem finiteFlatGroupScheme_exists_hopfCoordinates
    (G : CommGrp (Over (Spec (CommRingCat.of R))))
    [IsFinite G.X.hom] [AlgebraicGeometry.Flat G.X.hom] :
    ∃ A : CommAlgCat.{u} R, ∃ h : HopfAlgebra R A,
      h.toAlgebra = (inferInstance : Algebra R A) ∧
      (letI : Algebra R A := h.toAlgebra
       letI := h
       Coalgebra.IsCocomm R A ∧ Module.Finite R A ∧ Module.Free R A ∧
         Nonempty ((coordinateRelativeSpec (R := R)).obj (op A) ≅ G.X)) := by
  obtain ⟨A, hfinite, hfree, ⟨e⟩⟩ := finiteFlatScheme_exists_freeAffineCoordinates G.X
  letI : CommGrpObj (op A) := affineSchemeCoordinateGroupObject G e
  let h : HopfAlgebra R A := coordinateGroupObjectHopfAlgebra (op A)
  refine ⟨A, h, rfl, ?_⟩
  letI : Algebra R A := h.toAlgebra
  letI := h
  exact ⟨coordinateGroupObjectHopfAlgebra_isCocomm (op A), hfinite, hfree, ⟨e⟩⟩

end
end Dubon2026
