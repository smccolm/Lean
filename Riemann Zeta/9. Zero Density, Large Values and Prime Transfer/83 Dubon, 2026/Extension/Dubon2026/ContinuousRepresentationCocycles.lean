import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.Topology.ContinuousMap.Algebra

/-! # Genuine continuous low-degree cocycles for the original coefficient representation -/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]

/-- The actual continuous one-cocycles inside the pinned original algebraic
one-cocycle module, with the original inhomogeneous differential. -/
def continuousRepresentationCocyclesOne : Submodule R (groupCohomology.cocycles₁ A) where
  carrier := {c | Continuous (fun g => c g)}
  zero_mem' := continuous_const
  add_mem' hc hd := hc.add hd
  smul_mem' r _ hc := hc.const_smul r

/-- The actual jointly continuous two-cocycles inside the original algebraic
two-cocycle module. Continuity is on the genuine product topology of `G × G`. -/
def continuousRepresentationCocyclesTwo : Submodule R (groupCohomology.cocycles₂ A) where
  carrier := {c | Continuous (fun z => c z)}
  zero_mem' := continuous_const
  add_mem' hc hd := hc.add hd
  smul_mem' r _ hc := hc.const_smul r

/-- The actual continuous one-cocycle submodule has its inherited additive group. -/
instance continuousRepresentationCocyclesOneAddCommGroup :
    AddCommGroup (continuousRepresentationCocyclesOne A) :=
  (continuousRepresentationCocyclesOne A).addCommGroup

/-- The actual continuous two-cocycle submodule has its inherited additive group. -/
instance continuousRepresentationCocyclesTwoAddCommGroup :
    AddCommGroup (continuousRepresentationCocyclesTwo A) :=
  (continuousRepresentationCocyclesTwo A).addCommGroup

omit [TopologicalSpace R] [IsTopologicalGroup G] [ContinuousSMul R A] in
/-- Joint continuity of the original coefficient action makes every original
degree-zero coboundary continuous. -/
theorem representationCoboundary_continuous
    (hA : Continuous (fun z : G × A => A.ρ z.1 z.2)) (x : A) :
    Continuous (fun g => groupCohomology.d₀₁ A x g) := by
  exact (hA.comp (continuous_id.prodMk continuous_const)).sub continuous_const

omit [TopologicalSpace R] [ContinuousSMul R A] in
/-- The original degree-one differential maps actual continuous cochains to
jointly continuous two-cochains, using the same group multiplication and action. -/
theorem representationOneDifferential_continuous
    (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
    (f : G → A) (hf : Continuous f) :
    Continuous (fun z => groupCohomology.d₁₂ A f z) := by
  exact ((hA.comp (continuous_fst.prodMk (hf.comp continuous_snd))).sub
    (hf.comp (continuous_fst.mul continuous_snd))).add (hf.comp continuous_fst)

end
end Dubon2026
