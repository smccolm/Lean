import Dubon2026.ContinuousShortComplexInvariantConnecting
import Dubon2026.ContinuousInvariantConnectingExactness

/-! An actual invariant lift of a correction does not change its H1
connecting class. This removes the free correction term after localizing
the finite S-unit relation in DUB-17's prescribed local class recovery. -/
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

/-- The actual continuous connecting class is unchanged by a correction
with an invariant lift through the original short exact sequence. -/
theorem continuousInvariantConnecting_eq_of_correction
    (c d : X.X₃.ρ.invariants) (b : X.X₂.ρ.invariants)
    (hb : X.g.hom b.val = c.val - d.val) :
    continuousShortComplexInvariantConnectingMap X hX hA hB c =
      continuousShortComplexInvariantConnectingMap X hX hA hB d := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact (continuousInvariantConnecting_eq_zero_iff X.X₁ X.X₂ X.X₃
    X.f.hom.toLinearMap ((Rep.mono_iff_injective X.f).mp hX.mono_f)
    (Rep.hom_comm_apply X.f) X.g.hom.toLinearMap
    ((Rep.epi_iff_surjective X.g).mp hX.epi_g) (Rep.hom_comm_apply X.g)
    (hX.exact.map (forget₂ (Rep R G) (ModuleCat R))).moduleCat_range_eq_ker
    hA hB (c - d)).mpr ⟨b, hb⟩

end
end Dubon2026
