import Dubon2026.ResidualCompletionOriginalDensity
import Dubon2026.LocalizationSubalgebraImage
import Dubon2026.RepresentationCoordinateSubalgebraImage
import Mathlib.Topology.Algebra.Algebra

/-! # The genuine completed residual coefficient image from actual original matrix entries -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι O A : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [CommRing A] [Algebra O A] [TopologicalSpace A]

/-- A genuine continuous completed coefficient map has image in the original closed unit-reflecting subalgebra when its original representation entries do; original coordinate generation, localization fractions and completion density discharge all other coefficients. -/
theorem completedResidual_image_mem_subalgebra
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (S : Subalgebra O A) (hS : IsClosed (S : Set A))
    (hunit : ∀ x : S, IsUnit (x : A) → IsUnit x)
    (f : ResidualRepresentationCompletion ρ →ₐ[O] A) (hf : Continuous f)
    (hentry : ∀ g i j, f ((completedUniversalMatrixRepresentation ρ g).val i j) ∈ S)
    (x : ResidualRepresentationCompletion ρ) : f x ∈ S := by
  let c := Algebra.algHom O (ResidualRepresentationLocalRing ρ) (ResidualRepresentationCompletion ρ)
  let l := Algebra.algHom O (RepresentationCoordinateAlgebra G ι O) (ResidualRepresentationLocalRing ρ)
  have hbase : ∀ r : RepresentationCoordinateAlgebra G ι O,
      (f.comp (c.comp l)) r ∈ S := by
    apply representationCoordinate_image_mem_subalgebra S
    intro g i j
    exact hentry g i j
  have hlocal : ∀ r : ResidualRepresentationLocalRing ρ,
      f (algebraMap (ResidualRepresentationLocalRing ρ) (ResidualRepresentationCompletion ρ) r) ∈ S := by
    intro r
    exact localization_image_mem_subalgebra
      (residualRepresentationCoordinateIdeal ρ).primeCompl S (f.comp c).toRingHom hbase hunit r
  have hs : Set.range (algebraMap (ResidualRepresentationLocalRing ρ)
      (ResidualRepresentationCompletion ρ)) ⊆ f ⁻¹' (S : Set A) := by
    rintro _ ⟨r, rfl⟩
    exact hlocal r
  exact closure_minimal hs (hS.preimage hf) (residualRepresentationCompletion_original_dense ρ x)

end
end Dubon2026
