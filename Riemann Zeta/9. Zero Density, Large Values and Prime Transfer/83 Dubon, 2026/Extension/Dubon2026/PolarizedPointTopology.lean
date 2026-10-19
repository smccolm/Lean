import Dubon2026.PolarizedBlockNaturality
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Homeomorph.Defs

/-! The source topology on polarized coefficient-ring points: the product
topology on GL_n, the multiplier and the finite component. This is needed
to compare continuous polarized lifts with the native continuous framed
matrix fibers on DUB-17's CM deformation route. -/

namespace Dubon2026
open Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] [TopologicalSpace R]

/-- Polarized points carry the original coordinate topology and discrete component topology. -/
instance polarizedPointTopologicalSpace : TopologicalSpace (PolarizedGaloisGroup ι R) :=
  TopologicalSpace.induced SemidirectProduct.equivProd inferInstance

/-- The original polarized coordinates are a homeomorphism of the underlying spaces. -/
def polarizedPointHomeomorph : PolarizedGaloisGroup ι R ≃ₜ
    (GeneralLinearGroup ι R × Rˣ) × Multiplicative (ZMod 2) :=
  SemidirectProduct.equivProd.toHomeomorphOfIsInducing ⟨rfl⟩

/-- Continuity in the source target means continuity of its actual matrix,
multiplier and finite component coordinates. -/
theorem continuous_polarized_iff_coordinates {X : Type*} [TopologicalSpace X]
    (f : X → PolarizedGaloisGroup ι R) :
    Continuous f ↔ Continuous (fun x => (f x).left.1) ∧
      Continuous (fun x => (f x).left.2) ∧ Continuous (fun x => (f x).right) := by
  rw [← (polarizedPointHomeomorph (R := R) (ι := ι)).comp_continuous_iff]
  change Continuous (fun x => (((f x).left.1, (f x).left.2), (f x).right)) ↔ _
  rw [continuous_prodMk, continuous_prodMk, and_assoc]

end Dubon2026
