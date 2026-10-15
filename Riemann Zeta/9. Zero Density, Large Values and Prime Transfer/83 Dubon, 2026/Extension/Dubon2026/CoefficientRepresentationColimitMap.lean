import Dubon2026.CoefficientRepresentationColimit

/-! # Actual morphisms between the required coefficient representations

The original equivariant stage maps and their proved transition squares
induce equivariant maps on the source coefficient colimits. This supplies
the original diagonal and quotient maps of the DUB-17 arithmetic sequence.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory

variable {R G ι : Type} [CommRing R] [Group G] [Preorder ι] [DecidableEq ι]
  [Nonempty ι] [IsDirectedOrder ι]
  (A B : ι → Rep R G)
  (f : ∀ i j, i ≤ j → (A i ⟶ A j)) (g : ∀ i j, i ≤ j → (B i ⟶ B j))
  (u : ∀ i, A i ⟶ B i)
  (hu : ∀ i j h, f i j h ≫ u j = u i ≫ g i j h)

private def colimitLinearMap :
    Module.DirectLimit (fun i => A i) (fun i j h => (f i j h).hom.toLinearMap) →ₗ[R]
      Module.DirectLimit (fun i => B i) (fun i j h => (g i j h).hom.toLinearMap) :=
  Module.DirectLimit.map (fun i => (u i).hom.toLinearMap) (by
    intro i j h
    exact congrArg (fun v : A i ⟶ B j => v.hom.toLinearMap) (hu i j h))

omit [Nonempty ι] [IsDirectedOrder ι] in
private theorem colimitLinearMap_of (i : ι) (x : A i) :
    colimitLinearMap A B f g u hu
      (Module.DirectLimit.of R ι (fun i => A i) (fun i j h => (f i j h).hom.toLinearMap) i x) =
        Module.DirectLimit.of R ι (fun i => B i) (fun i j h => (g i j h).hom.toLinearMap) i
          ((u i).hom x) :=
  Module.DirectLimit.map_apply_of
    (R := R) (ι := ι) (G := fun i => A i) (G' := fun i => B i)
    (f := fun i j h => (f i j h).hom.toLinearMap)
    (f' := fun i j h => (g i j h).hom.toLinearMap)
    (fun i => (u i).hom.toLinearMap) (by
      intro i j h
      exact congrArg (fun v : A i ⟶ B j => v.hom.toLinearMap) (hu i j h)) x

/-- Original equivariant stage maps give the genuine equivariant map between their coefficient colimits. -/
def coefficientRepresentationColimitMap :
    coefficientRepresentationColimit A f ⟶ coefficientRepresentationColimit B g :=
  Rep.ofHom {
    toLinearMap := colimitLinearMap A B f g u hu
    isIntertwining' := by
      intro σ
      apply LinearMap.ext
      intro x
      obtain ⟨i, y, rfl⟩ := Module.DirectLimit.exists_of x
      change colimitLinearMap A B f g u hu (coefficientColimitAction A f σ
        (Module.DirectLimit.of R ι (fun i => A i) (fun i j h => (f i j h).hom.toLinearMap) i y)) =
        coefficientColimitAction B g σ (colimitLinearMap A B f g u hu
          (Module.DirectLimit.of R ι (fun i => A i) (fun i j h => (f i j h).hom.toLinearMap) i y))
      rw [coefficientColimitAction_of, colimitLinearMap_of, colimitLinearMap_of,
        coefficientColimitAction_of]
      exact congrArg (Module.DirectLimit.of R ι (fun i => B i)
        (fun i j h => (g i j h).hom.toLinearMap) i) (Rep.hom_comm_apply (u i) σ y) }

/-- The induced equivariant colimit map retains each actual original stage map. -/
theorem coefficientRepresentationColimitMap_of (i : ι) (x : A i) :
    (coefficientRepresentationColimitMap A B f g u hu).hom
      ((coefficientRepresentationColimitOf A f i).hom x) =
        (coefficientRepresentationColimitOf B g i).hom ((u i).hom x) :=
  colimitLinearMap_of A B f g u hu i x

end
end Dubon2026
