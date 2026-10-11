import Dubon2026.FiniteFlatSchemePointModel
import Dubon2026.FiniteFreeHopfModelSchemeRealization

/-! # The actual finite flat scheme realization and the actual Hopf point model condition -/

namespace Dubon2026
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj
universe u

variable {R F K V : Type u} [CommRing R] [Field F] [Field K]
  [Algebra R F] [Algebra F K] [Algebra R K] [IsScalarTower R F K] [CommGroup V]

/-- The actual original fiber products of schemes over the base. -/
local instance flatRealizationCartesian : CartesianMonoidalCategory (Over (Spec (CommRingCat.of R))) :=
  Over.cartesianMonoidalCategory _

/-- Retain the original fiber-product monoidal structure explicitly. -/
local instance flatRealizationMonoidal : MonoidalCategory (Over (Spec (CommRingCat.of R))) :=
  flatRealizationCartesian.toSemiCartesianMonoidalCategory.toMonoidalCategory

/-- The actual symmetry on those fiber products. -/
local instance flatRealizationBraided : BraidedCategory (Over (Spec (CommRingCat.of R))) :=
  Over.braidedCategory _

/-- The specified original representation is the genuine geometric point representation
of an actual finite flat commutative group scheme over the original base. This is the
scheme-side condition; existence of such a scheme for an arithmetic representation is not assumed. -/
def FiniteFlatSchemePointRealization (ρ : (K ≃ₐ[F] K) →* MulAut V) : Prop :=
  ∃ G : CommGrp (Over (Spec (CommRingCat.of R))),
    IsFinite G.X.hom ∧ AlgebraicGeometry.Flat G.X.hom ∧
    ∃ E : ((coordinateRelativeSpec (R := R)).obj (op (CommAlgCat.of R K)) ⟶ G.X) ≃* V,
      ∀ (g : K ≃ₐ[F] K)
        (p : (coordinateRelativeSpec (R := R)).obj (op (CommAlgCat.of R K)) ⟶ G.X),
        E ((coordinateRelativeSpec (R := R)).map
          (CommAlgCat.ofHom (g.restrictScalars R).toAlgHom).op ≫ p) = ρ g (E p)

/-- Over the actual PID, the original representation has a finite free cocommutative Hopf
point model exactly when it has an actual finite flat commutative scheme realization.
The forward direction constructs the original affine group scheme and its exact point action;
the reverse direction constructs finite/free coordinates and the original Hopf point model. -/
theorem finiteFreeHopfPointModel_iff_schemeRealization [IsDomain R] [IsPrincipalIdealRing R]
    (ρ : (K ≃ₐ[F] K) →* MulAut V) :
    Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K V ρ) ↔
      FiniteFlatSchemePointRealization (R := R) (F := F) (K := K) (V := V) ρ := by
  constructor
  · rintro ⟨m⟩
    let G := finiteFreeHopfPointModelScheme m
    let E := finiteFreeHopfPointModelSchemePoints m
    obtain ⟨hfinite, hflat⟩ := finiteFreeHopfPointModel_scheme_finite_flat m
    refine ⟨G, hfinite, hflat, E.symm, ?_⟩
    intro g p
    apply E.injective
    rw [E.apply_symm_apply]
    have h := finiteFreeHopfPointModel_schemePoints_galois m g (E.symm p)
    change E (ρ g (E.symm p)) = (coordinateRelativeSpec (R := R)).map
      (CommAlgCat.ofHom (g.restrictScalars R).toAlgHom).op ≫ E (E.symm p) at h
    rw [E.apply_symm_apply] at h
    exact h.symm
  · rintro ⟨G, hfinite, hflat, E, hE⟩
    letI := hfinite
    letI := hflat
    exact finiteFlatSchemePointModel_exists G E hE

end
end Dubon2026
