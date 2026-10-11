import Dubon2026.FiniteFlatSchemeAffineCoordinates
import Dubon2026.AffineSchemeRecoveredHopfPoints
import Dubon2026.FiniteFreeHopfPointModel

/-! # Construct the actual Hopf point model from the original finite flat scheme realization -/

namespace Dubon2026
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj
universe u

variable {R F K V : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [Field K] [Algebra R F] [Algebra F K] [Algebra R K]
  [IsScalarTower R F K] [CommGroup V] {ρ : (K ≃ₐ[F] K) →* MulAut V}

/-- The original scheme fiber products. -/
local instance schemeModelCartesian : CartesianMonoidalCategory (Over (Spec (CommRingCat.of R))) :=
  Over.cartesianMonoidalCategory _

/-- Retain their actual original monoidal structure explicitly. -/
local instance schemeModelMonoidal : MonoidalCategory (Over (Spec (CommRingCat.of R))) :=
  schemeModelCartesian.toSemiCartesianMonoidalCategory.toMonoidalCategory

/-- The original symmetry of scheme fiber products. -/
local instance schemeModelBraided : BraidedCategory (Over (Spec (CommRingCat.of R))) :=
  Over.braidedCategory _

/-- An actual finite flat commutative group scheme whose original geometric point group
realizes the specified original representation yields a genuine finite free cocommutative
Hopf point model. The target coordinates, Hopf structure and point comparison are constructed
from the same original scheme; its supplied original Galois realization is preserved exactly. -/
theorem finiteFlatSchemePointModel_exists
    (G : CommGrp (Over (Spec (CommRingCat.of R))))
    [IsFinite G.X.hom] [AlgebraicGeometry.Flat G.X.hom]
    (E : ((coordinateRelativeSpec (R := R)).obj (op (CommAlgCat.of R K)) ⟶ G.X) ≃* V)
    (hE : ∀ (g : K ≃ₐ[F] K)
      (p : (coordinateRelativeSpec (R := R)).obj (op (CommAlgCat.of R K)) ⟶ G.X),
      E ((coordinateRelativeSpec (R := R)).map
        (CommAlgCat.ofHom (g.restrictScalars R).toAlgHom).op ≫ p) = ρ g (E p)) :
    Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K V ρ) := by
  obtain ⟨A, hfinite, hfree, ⟨e⟩⟩ := finiteFlatScheme_exists_freeAffineCoordinates G.X
  letI : CommGrpObj (op A) := affineSchemeCoordinateGroupObject G e
  letI := coordinateGroupObjectHopfAlgebra (op A)
  letI := coordinateGroupObjectHopfAlgebra_isCocomm (op A)
  let P := affineSchemeRecoveredHopfPointEquiv G e (CommAlgCat.of R K)
  refine ⟨{
    Coordinates := A
    hopf := coordinateGroupObjectHopfAlgebra (op A)
    cocomm := coordinateGroupObjectHopfAlgebra_isCocomm (op A)
    finite := hfinite
    free := hfree
    pointEquiv := P.trans E
    galois := ?_ }⟩
  intro g p
  change E (P (hopfPointsGaloisAction (R := R) g p)) = ρ g (E (P p))
  have hP := affineSchemeRecoveredHopfPointEquiv_coefficient G e
    (CommAlgCat.of R K) (CommAlgCat.of R K)
    (CommAlgCat.ofHom (g.restrictScalars R).toAlgHom) p
  change P (hopfPointsGaloisAction (R := R) g p) =
    (coordinateRelativeSpec (R := R)).map
      (CommAlgCat.ofHom (g.restrictScalars R).toAlgHom).op ≫ P p at hP
  rw [hP]
  exact hE g (P p)

end
end Dubon2026
