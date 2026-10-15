import Dubon2026.ContinuousRepresentationRestriction
import Mathlib.Algebra.Colimit.Module

/-! # Genuine coefficient representations on the required module colimits

This construction supplies the Galois action on the arithmetic S-unit,
source idele and source class colimits. It uses the original stage actions
and equivariant transition maps, without an assumed action on the colimit.
Discrete action continuity follows directly from original stage continuity.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory

variable {R G ι : Type} [CommRing R] [Group G] [Preorder ι] [DecidableEq ι]
  [Nonempty ι] [IsDirectedOrder ι]
  (A : ι → Rep R G) (f : ∀ i j, i ≤ j → (A i ⟶ A j))

/-- The original stage equivariance induces each actual action operator on the module direct limit. -/
def coefficientColimitAction (g : G) :
    Module.DirectLimit (fun i => A i) (fun i j h => (f i j h).hom.toLinearMap) →ₗ[R]
      Module.DirectLimit (fun i => A i) (fun i j h => (f i j h).hom.toLinearMap) :=
  Module.DirectLimit.map (fun i => (A i).ρ g) (by
    intro i j h
    apply LinearMap.ext
    intro x
    exact (Rep.hom_comm_apply (f i j h) g x).symm)

omit [Nonempty ι] [IsDirectedOrder ι] in
/-- The induced operator acts by the same original action on each original stage representative. -/
theorem coefficientColimitAction_of (g : G) (i : ι) (x : A i) :
    coefficientColimitAction A f g
      (Module.DirectLimit.of R ι (fun i => A i) (fun i j h => (f i j h).hom.toLinearMap) i x) =
        Module.DirectLimit.of R ι (fun i => A i) (fun i j h => (f i j h).hom.toLinearMap) i
          ((A i).ρ g x) :=
  Module.DirectLimit.map_apply_of
    (R := R) (ι := ι) (G := fun i => A i) (G' := fun i => A i)
    (f := fun i j h => (f i j h).hom.toLinearMap)
    (f' := fun i j h => (f i j h).hom.toLinearMap)
    (fun i => (A i).ρ g) (by
      intro i j h
      apply LinearMap.ext
      intro y
      exact (Rep.hom_comm_apply (f i j h) g y).symm) x

/-- The literal stage actions give the actual coefficient representation on the original module colimit. -/
def coefficientRepresentationColimit : Rep R G :=
  Rep.of {
    toFun := coefficientColimitAction A f
    map_one' := by
      apply LinearMap.ext
      intro x
      obtain ⟨i, y, rfl⟩ := Module.DirectLimit.exists_of x
      rw [coefficientColimitAction_of]
      change Module.DirectLimit.of R ι (fun i => A i) (fun i j h => (f i j h).hom.toLinearMap) i
        ((A i).ρ 1 y) = _
      rw [map_one]
      rfl
    map_mul' := by
      intro g h
      apply LinearMap.ext
      intro x
      obtain ⟨i, y, rfl⟩ := Module.DirectLimit.exists_of x
      rw [Module.End.mul_apply]
      rw [coefficientColimitAction_of, coefficientColimitAction_of, coefficientColimitAction_of]
      rw [map_mul]
      rfl }

/-- Each original stage includes equivariantly into the constructed coefficient representation. -/
def coefficientRepresentationColimitOf (i : ι) : A i ⟶ coefficientRepresentationColimit A f :=
  Rep.ofHom {
    toLinearMap := Module.DirectLimit.of R ι (fun i => A i) (fun i j h => (f i j h).hom.toLinearMap) i
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro x
      exact (coefficientColimitAction_of A f g i x).symm }

/-- Original continuous stage actions give a continuous action on the discrete coefficient colimit. -/
theorem coefficientRepresentationColimit_continuous
    [TopologicalSpace G] [TopologicalSpace (coefficientRepresentationColimit A f)]
    [DiscreteTopology (coefficientRepresentationColimit A f)]
    [∀ i, TopologicalSpace (A i)] [∀ i, DiscreteTopology (A i)]
    (hA : ∀ i, Continuous (fun z : G × A i => (A i).ρ z.1 z.2)) :
    Continuous (fun z : G × coefficientRepresentationColimit A f =>
      (coefficientRepresentationColimit A f).ρ z.1 z.2) := by
  letI : TopologicalSpace
      (Module.DirectLimit (fun i => A i) (fun i j h => (f i j h).hom.toLinearMap)) :=
    inferInstanceAs (TopologicalSpace (coefficientRepresentationColimit A f))
  rw [continuous_prod_of_discrete_right]
  intro x
  obtain ⟨i, y, rfl⟩ := Module.DirectLimit.exists_of x
  have hc : Continuous (fun g : G => Module.DirectLimit.of R ι (fun i => A i)
      (fun i j h => (f i j h).hom.toLinearMap) i ((A i).ρ g y)) :=
    continuous_of_discreteTopology.comp ((hA i).comp (continuous_id.prodMk continuous_const))
  convert hc using 1
  funext g
  exact coefficientColimitAction_of A f g i y

end
end Dubon2026
