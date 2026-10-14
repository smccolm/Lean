import Dubon2026.CosetCarryProjectionHomotopy
import Dubon2026.ContinuousCohomologyCorestriction
import Mathlib.Topology.Instances.ZMod

/-! # Original continuous carry corestriction and the coset norm

The explicit carry projection homotopy is continuous for an open subgroup.
Consequently genuine continuous corestriction carries the subgroup carry to
the carry of the actual sum of conjugates. The field-norm identification will
apply this to the local reciprocity norm compatibility required by DUB-17's
ramified cyclotomic invariant calculation.
-/
namespace Dubon2026
noncomputable section
open scoped BigOperators
attribute [local instance 1100] Rep.hV2
attribute [-instance] AddCommGroup.toIntModule

variable {G : Type} [Group G] [TopologicalSpace G]
  {n : ℕ} [NeZero n]

/-- The original module action on discrete integer coefficients is continuous. -/
local instance carryCoefficientContinuousSMul (A : Rep ℤ G)
    [TopologicalSpace A] [DiscreteTopology A] :
    @ContinuousSMul ℤ A A.hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ A A.hV2.toSMul inferInstance inferInstance
    continuous_of_discreteTopology

/-- The original representation carry of a continuous finite character is a continuous cocycle. -/
def continuousRepresentationCarryCocycle (A : Rep ℤ G) [TopologicalSpace A] [DiscreteTopology A]
    (χ : G →ₜ* Multiplicative (ZMod n)) (a : A) (ha : ∀ g : G, A.ρ g a = a) :
    continuousRepresentationCocyclesTwo A := by
  let f : Multiplicative (ZMod n) × Multiplicative (ZMod n) → A :=
    fun z => zmodAdditionCarry z.1.toAdd z.2.toAdd • a
  exact ⟨representationCarryCocycle A χ.toMonoidHom a ha,
    (show Continuous f from continuous_of_discreteTopology).comp
      ((χ.continuous.comp continuous_fst).prodMk (χ.continuous.comp continuous_snd))⟩

variable [IsTopologicalGroup G] (S : Subgroup G) (hS : IsOpen (S : Set G))
  (χ : G →ₜ* Multiplicative (ZMod n))

omit [NeZero n] in
include hS in
/-- Openness makes the literal integer carry correction continuous. -/
theorem cosetCarryCorrection_continuous (q : G ⧸ S) :
    Continuous (fun g => cosetCarryCorrection S χ.toMonoidHom g q) := by
  letI : DiscreteTopology (G ⧸ S) := QuotientGroup.discreteTopology hS
  have hout : Continuous (fun t : G ⧸ S => t.out) := continuous_of_discreteTopology
  let f : Multiplicative (ZMod n) × Multiplicative (ZMod n) → ℤ :=
    fun z => zmodAdditionCarry z.1.toAdd z.2.toAdd
  have hc : Continuous (fun z : G × G => f (χ z.1, χ z.2)) :=
    (show Continuous f from continuous_of_discreteTopology).comp
      ((χ.continuous.comp continuous_fst).prodMk (χ.continuous.comp continuous_snd))
  exact (hc.comp (continuous_id.prodMk continuous_const)).sub
    (hc.comp ((hout.comp (continuous_id.smul continuous_const)).prodMk
      (continuous_subtype_val.comp ((cosetTransition_continuous S hS).comp
        (continuous_id.prodMk continuous_const)))))

variable (A : Rep ℤ G) [TopologicalSpace A] [DiscreteTopology A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (a : A) [Fintype (G ⧸ S)]

omit [NeZero n] in
include hS hA in
/-- The constructed weighted carry homotopy is an actual continuous cochain. -/
theorem cosetCarryProjectionHomotopy_continuous :
    Continuous (cosetCarryProjectionHomotopy S χ.toMonoidHom A a) := by
  letI : DiscreteTopology (G ⧸ S) := QuotientGroup.discreteTopology hS
  have hout : Continuous (fun q : G ⧸ S => q.out) := continuous_of_discreteTopology
  apply continuous_finsetSum
  intro q _
  exact (cosetCarryCorrection_continuous S hS χ q).smul
    (hA.comp ((hout.comp (continuous_id.smul continuous_const)).prodMk continuous_const))

/-- The genuine continuous corestriction of the original subgroup carry is the original carry of its actual coset norm coefficient. -/
theorem continuousRepresentationCarryCocycle_corestriction
    (ha : ∀ s : S, A.ρ s a = a) :
    continuousRepresentationH2Corestriction A hA S hS
      (Submodule.Quotient.mk (continuousRepresentationCarryCocycle
        (restrictedCoefficientRep A S.subtype)
        ⟨χ.toMonoidHom.comp S.subtype, χ.continuous.comp continuous_subtype_val⟩ a ha)) =
      (Submodule.Quotient.mk (continuousRepresentationCarryCocycle A χ
        (∑ q : G ⧸ S, A.ρ q.out a) (cosetInvariantCoefficient_sum_fixed S A a ha)) :
        ContinuousRepresentationH2 A hA) := by
  rw [continuousRepresentationH2Corestriction_mk]
  symm
  apply (continuousRepresentationH2_eq_iff A hA _ _).mpr
  refine ⟨⟨cosetCarryProjectionHomotopy S χ.toMonoidHom A a,
    cosetCarryProjectionHomotopy_continuous S hS χ A hA a⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact cosetCarryProjectionHomotopy_differential S χ.toMonoidHom A a ha

end
end Dubon2026
