import Dubon2026.RepresentationOrbitRange
import Dubon2026.SphericalCoefficientRelations
import Mathlib.RepresentationTheory.Intertwining

/-! # The genuine cyclic subquotient supplied by matching original spherical coefficients -/

namespace Dubon2026

noncomputable section

variable {G V W : Type*} [Group G] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (hρ : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (v : V) (w : W) (ℓ : W →ₗ[ℂ] ℂ)
    (hcoeff : ∀ g, ℓ (σ g w) = inner ℂ v (ρ g v))

/-- The proved original coefficient relation map is equivariant on every actual finite cyclic vector. -/
theorem sphericalCoefficientRangeMap_intertwines (g : G) (x : representationOrbitRange σ w) :
    sphericalCoefficientRangeMap ρ σ hρ v w ℓ hcoeff
      (representationOrbitRepresentation σ w g x) =
    ρ g (sphericalCoefficientRangeMap ρ σ hρ v w ℓ hcoeff x) := by
  obtain ⟨x, a, rfl⟩ := x
  have he : representationOrbitRepresentation σ w g
      ⟨Finsupp.linearCombination ℂ (fun h => σ h w) a, ⟨a, rfl⟩⟩ =
      ⟨Finsupp.linearCombination ℂ (fun h => σ h w) (a.mapDomain (fun h => g * h)),
        ⟨a.mapDomain (fun h => g * h), rfl⟩⟩ :=
    Subtype.ext (representation_orbit_linearCombination σ w g a)
  rw [he]
  calc
    _ = Finsupp.linearCombination ℂ (fun h => ρ h v) (a.mapDomain (fun h => g * h)) :=
      sphericalCoefficientRangeMap_linearCombination ρ σ hρ v w ℓ hcoeff _ _
    _ = ρ g (Finsupp.linearCombination ℂ (fun h => ρ h v) a) :=
      (representation_orbit_linearCombination ρ v g a).symm
    _ = _ := congrArg (ρ g)
      (sphericalCoefficientRangeMap_linearCombination ρ σ hρ v w ℓ hcoeff a _).symm

/-- The genuine cyclic relation map is an actual intertwiner into the original unitary representation itself. -/
def sphericalCoefficientIntertwiner :
    Representation.IntertwiningMap (representationOrbitRepresentation σ w) ρ where
  toLinearMap := sphericalCoefficientRangeMap ρ σ hρ v w ℓ hcoeff
  isIntertwining' g := by
    ext x
    exact sphericalCoefficientRangeMap_intertwines ρ σ hρ v w ℓ hcoeff g x

/-- The genuine coefficient intertwiner sends every actual source spherical orbit vector to its original target orbit vector. -/
theorem sphericalCoefficientIntertwiner_orbit (g : G) :
    sphericalCoefficientIntertwiner ρ σ hρ v w ℓ hcoeff
      ⟨σ g w, representationOrbitRange_orbit_mem σ w g⟩ = ρ g v := by
  have he := sphericalCoefficientRangeMap_linearCombination ρ σ hρ v w ℓ hcoeff
    (Finsupp.single g 1) (by exact ⟨Finsupp.single g 1, rfl⟩)
  simpa only [Finsupp.linearCombination_single, one_smul] using he

/-- If the original target vector algebraically generates its actual representation, the genuine induced cyclic intertwiner is surjective onto that entire original representation. -/
theorem sphericalCoefficientIntertwiner_surjective
    (hspan : Submodule.span ℂ (Set.range (fun g => ρ g v)) = ⊤) :
    Function.Surjective (sphericalCoefficientIntertwiner ρ σ hρ v w ℓ hcoeff) := by
  apply LinearMap.range_eq_top.mp
  change (sphericalCoefficientRangeMap ρ σ hρ v w ℓ hcoeff).range = ⊤
  rw [sphericalCoefficientRangeMap_range, Finsupp.range_linearCombination, hspan]

/-- The genuine coefficient quotient map has its image in exactly the original target cyclic range. -/
def sphericalCoefficientCyclicMap :
    representationOrbitRange σ w →ₗ[ℂ] representationOrbitRange ρ v :=
  (sphericalCoefficientRangeMap ρ σ hρ v w ℓ hcoeff).codRestrict _ (fun x => by
    rw [representationOrbitRange, ← sphericalCoefficientRangeMap_range ρ σ hρ v w ℓ hcoeff]
    exact ⟨x, rfl⟩)

/-- The actual cyclic coefficient map is a genuine intertwiner of the original restricted group actions. -/
def sphericalCoefficientCyclicIntertwiner :
    Representation.IntertwiningMap (representationOrbitRepresentation σ w)
      (representationOrbitRepresentation ρ v) where
  toLinearMap := sphericalCoefficientCyclicMap ρ σ hρ v w ℓ hcoeff
  isIntertwining' g := by
    ext x
    exact sphericalCoefficientRangeMap_intertwines ρ σ hρ v w ℓ hcoeff g x

/-- Every original target cyclic vector is the image of its identical finite source orbit combination under the genuine coefficient intertwiner. -/
theorem sphericalCoefficientCyclicIntertwiner_surjective :
    Function.Surjective (sphericalCoefficientCyclicIntertwiner ρ σ hρ v w ℓ hcoeff) := by
  rintro ⟨x, a, rfl⟩
  refine ⟨⟨Finsupp.linearCombination ℂ (fun g => σ g w) a, ⟨a, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  exact sphericalCoefficientRangeMap_linearCombination ρ σ hρ v w ℓ hcoeff a _

/-- The original target cyclic space is the actual quotient of the genuine source cyclic space by the kernel of its proved coefficient intertwiner. -/
def sphericalCoefficientCyclicQuotientEquiv :
    (representationOrbitRange σ w ⧸
      (sphericalCoefficientCyclicMap ρ σ hρ v w ℓ hcoeff).ker) ≃ₗ[ℂ]
      representationOrbitRange ρ v :=
  LinearMap.quotKerEquivOfSurjective (sphericalCoefficientCyclicMap ρ σ hρ v w ℓ hcoeff)
    (sphericalCoefficientCyclicIntertwiner_surjective ρ σ hρ v w ℓ hcoeff)

end
end Dubon2026
