import Dubon2026.FiniteFreeHopfPointModel
import Dubon2026.HopfAffineSchemePointGroup

/-! # Actual finite-flat affine scheme realization of a specified Hopf point model

The original model is an explicit input. This constructs its scheme realization;
it does not assume or prove that a particular arithmetic representation has a model.
This module uses a common universe for the original rings, field, group and coordinates.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry WithConv
open scoped CategoryTheory.MonObj

universe u
variable {R F K V : Type u} [CommRing R] [Field F] [Field K]
  [Algebra R F] [Algebra F K] [Algebra R K] [IsScalarTower R F K]
  [CommGroup V] {ρ : (K ≃ₐ[F] K) →* MulAut V}

/-- The actual fiber products in the scheme category over the original base. -/
local instance modelSchemeCartesian : CartesianMonoidalCategory (Over (Spec (CommRingCat.of R))) :=
  Over.cartesianMonoidalCategory _

/-- The actual symmetry of those original fiber products. -/
local instance modelSchemeBraided : BraidedCategory (Over (Spec (CommRingCat.of R))) :=
  Over.braidedCategory _

/-- Construct the actual affine commutative group scheme of the original given model, using its same original integral coordinate algebra. -/
def finiteFreeHopfPointModelScheme
    (m : FiniteFreeHopfPointModel.{u, u, u, u, u} R F K V ρ) :
    CommGrp (Over (Spec (CommRingCat.of R))) := by
  letI := m.commRing
  letI := m.hopf
  letI := m.cocomm
  exact hopfCoordinateAffineGroupScheme (R := R) (A := m.Coordinates)

/-- The constructed scheme has finite and flat original structure morphism because its actual original coordinate module is finite free. -/
theorem finiteFreeHopfPointModel_scheme_finite_flat
    (m : FiniteFreeHopfPointModel.{u, u, u, u, u} R F K V ρ) :
    IsFinite (finiteFreeHopfPointModelScheme m).X.hom ∧
      AlgebraicGeometry.Flat (finiteFreeHopfPointModelScheme m).X.hom := by
  letI := m.commRing
  letI := m.hopf
  letI := m.cocomm
  letI := m.finite
  letI := m.free
  exact ⟨hopfCoordinateAffineGroupScheme_finite, hopfCoordinateAffineGroupScheme_flat⟩

/-- The original represented group is genuinely the group of points of the actual constructed group scheme in the original point field. -/
def finiteFreeHopfPointModelSchemePoints
    (m : FiniteFreeHopfPointModel.{u, u, u, u, u} R F K V ρ) :
    V ≃* ((coordinateRelativeSpec (R := R)).obj (op (CommAlgCat.of R K)) ⟶
      (finiteFreeHopfPointModelScheme m).X) := by
  letI := m.commRing
  letI := m.hopf
  letI := m.cocomm
  exact m.pointEquiv.symm.trans (hopfAffineSchemePointGroupEquiv (CommAlgCat.of R K))

/-- The genuine scheme point comparison realizes the specified original Galois action through actual precomposition by the original field automorphism's spectrum. -/
theorem finiteFreeHopfPointModel_schemePoints_galois
    (m : FiniteFreeHopfPointModel.{u, u, u, u, u} R F K V ρ)
    (g : K ≃ₐ[F] K) (v : V) :
    finiteFreeHopfPointModelSchemePoints m (ρ g v) =
      (coordinateRelativeSpec (R := R)).map
        (CommAlgCat.ofHom (g.restrictScalars R).toAlgHom).op ≫
          finiteFreeHopfPointModelSchemePoints m v := by
  letI := m.commRing
  letI := m.hopf
  letI := m.cocomm
  let p := m.pointEquiv.symm v
  have hg : m.pointEquiv.symm (ρ g v) = hopfPointsGaloisAction (R := R) g p := by
    apply m.pointEquiv.injective
    rw [m.pointEquiv.apply_symm_apply, m.galois]
    exact congrArg (ρ g) (m.pointEquiv.apply_symm_apply v).symm
  change hopfAffineSchemePointGroupEquiv (CommAlgCat.of R K) (m.pointEquiv.symm (ρ g v)) =
    (coordinateRelativeSpec (R := R)).map
      (CommAlgCat.ofHom (g.restrictScalars R).toAlgHom).op ≫
        hopfAffineSchemePointGroupEquiv (CommAlgCat.of R K) p
  rw [hg]
  exact hopfAffineSchemePointGroupEquiv_coefficient (CommAlgCat.of R K) (CommAlgCat.of R K)
    (CommAlgCat.ofHom (g.restrictScalars R).toAlgHom) p

end
end Dubon2026
