import Dubon2026.ContinuousInvariantConnectingMap
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-! # The invariant connecting map of an actual short exact sequence

Derive the linear exactness data from the original coefficient short
complex. This lets DUB-17's S-unit dual relation sequence supply its actual
continuous connecting map without separately supplied compatibility data.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G]
  (X : ShortComplex (Rep.{0} R G)) (hX : X.ShortExact)
  [TopologicalSpace X.X₁] [IsTopologicalAddGroup X.X₁] [ContinuousSMul R X.X₁]
  [TopologicalSpace X.X₂] [DiscreteTopology X.X₂]
  (hA : Continuous (fun z : G × X.X₁ => X.X₁.ρ z.1 z.2))
  (hB : Continuous (fun z : G × X.X₂ => X.X₂.ρ z.1 z.2))

/-- The actual continuous invariant connecting map of the original short
exact coefficient sequence, with all exactness premises derived. -/
def continuousShortComplexInvariantConnectingMap :
    X.X₃.ρ.invariants →ₗ[R] ContinuousRepresentationH1 X.X₁ hA :=
  continuousCoefficientInvariantConnectingMap X.X₁ X.X₂ X.X₃ X.f.hom.toLinearMap
    ((Rep.mono_iff_injective X.f).mp hX.mono_f) (Rep.hom_comm_apply X.f)
    X.g.hom.toLinearMap ((Rep.epi_iff_surjective X.g).mp hX.epi_g)
    (Rep.hom_comm_apply X.g)
    (hX.exact.map (forget₂ (Rep R G) (ModuleCat R))).moduleCat_range_eq_ker hA hB

end
end Dubon2026
