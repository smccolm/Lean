import Dubon2026.ArithmeticSourceHomContinuity
import Dubon2026.ContinuousInvariantConnectingExactness

/-! # Actual arithmetic source Hom H1 kernel

The original source coefficient sequence and its continuous Hom actions
identify the kernel of the actual S-unit Hom H1 diagonal map. The existing
invariant-connecting lift/coboundary theorem supplies both inclusions, with
no assumed arithmetic cohomology exactness. This serves the actual trace
dual H1 localization route for DUB-17; identifying the source idele H1 with
local terms and the class coefficient comparison remain separate.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (A : Rep.{0} ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K))
  [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (hA : Continuous (fun z : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) × A => A.ρ z.1 z.2))
  [TopologicalSpace (arithmeticSourceSUnitHomRep K Ω a ha A)]
  [DiscreteTopology (arithmeticSourceSUnitHomRep K Ω a ha A)]
  [TopologicalSpace (arithmeticSourceIdeleHomRep K Ω a ha A)]
  [DiscreteTopology (arithmeticSourceIdeleHomRep K Ω a ha A)]

local instance : @ContinuousSMul ℤ (arithmeticSourceSUnitHomRep K Ω a ha A)
    (arithmeticSourceSUnitHomRep K Ω a ha A).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩
local instance : @ContinuousSMul ℤ (arithmeticSourceIdeleHomRep K Ω a ha A)
    (arithmeticSourceIdeleHomRep K Ω a ha A).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

/-- The original arithmetic source diagonal induces its actual continuous S-unit Hom H1 map. -/
def arithmeticSourceHomH1Inclusion :
    ContinuousRepresentationH1 (arithmeticSourceSUnitHomRep K Ω a ha A)
      (arithmeticSourceSUnitHomAction_continuous K Ω a ha A hA) →ₗ[ℤ]
    ContinuousRepresentationH1 (arithmeticSourceIdeleHomRep K Ω a ha A)
      (arithmeticSourceIdeleHomAction_continuous K Ω a ha A hA) :=
  continuousCoefficientH1Map (arithmeticSourceSUnitHomRep K Ω a ha A)
    (arithmeticSourceIdeleHomRep K Ω a ha A)
    (arithmeticSourceHomShortComplex K Ω a ha A).f.hom.toLinearMap
    continuous_of_discreteTopology (Rep.hom_comm_apply (arithmeticSourceHomShortComplex K Ω a ha A).f)
    (arithmeticSourceSUnitHomAction_continuous K Ω a ha A hA)
    (arithmeticSourceIdeleHomAction_continuous K Ω a ha A hA)

variable [IsAlgClosure K Ω] (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 K) ∣ a)
  [Module (ZMod q) A]

/-- Original invariant source-class Hom coefficients give their actual continuous S-unit Hom H1 connecting classes. -/
def arithmeticSourceHomInvariantConnectingMap :
    (arithmeticSourceClassHomRep K Ω a ha A).ρ.invariants →ₗ[ℤ]
      ContinuousRepresentationH1 (arithmeticSourceSUnitHomRep K Ω a ha A)
        (arithmeticSourceSUnitHomAction_continuous K Ω a ha A hA) := by
  have hS := arithmeticSourceHomShortComplex_shortExact K Ω a ha A q hqa
  have hm := hS.map_of_exact
    (forget₂ (Rep ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K)) (ModuleCat ℤ))
  exact continuousCoefficientInvariantConnectingMap
    (arithmeticSourceSUnitHomRep K Ω a ha A)
    (arithmeticSourceIdeleHomRep K Ω a ha A)
    (arithmeticSourceClassHomRep K Ω a ha A)
    (arithmeticSourceHomShortComplex K Ω a ha A).f.hom.toLinearMap
    ((Rep.mono_iff_injective _).mp hS.mono_f)
    (Rep.hom_comm_apply (arithmeticSourceHomShortComplex K Ω a ha A).f)
    (arithmeticSourceHomShortComplex K Ω a ha A).g.hom.toLinearMap
    ((Rep.epi_iff_surjective _).mp hS.epi_g)
    (Rep.hom_comm_apply (arithmeticSourceHomShortComplex K Ω a ha A).g)
    hm.exact.moduleCat_range_eq_ker
    (arithmeticSourceSUnitHomAction_continuous K Ω a ha A hA)
    (arithmeticSourceIdeleHomAction_continuous K Ω a ha A hA)

/-- The original arithmetic S-unit Hom H1 inclusion kernel consists exactly of connecting classes from actual invariant source-class Hom coefficients. -/
theorem arithmeticSourceHomH1_kernel_eq_invariantConnecting_range :
    LinearMap.range (arithmeticSourceHomInvariantConnectingMap K Ω a ha A hA q hqa) =
      LinearMap.ker (arithmeticSourceHomH1Inclusion K Ω a ha A hA) := by
  have hS := arithmeticSourceHomShortComplex_shortExact K Ω a ha A q hqa
  have hm := hS.map_of_exact
    (forget₂ (Rep ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K)) (ModuleCat ℤ))
  ext x
  exact continuousInvariantConnecting_mem_range_iff
    (arithmeticSourceSUnitHomRep K Ω a ha A)
    (arithmeticSourceIdeleHomRep K Ω a ha A)
    (arithmeticSourceClassHomRep K Ω a ha A)
    (arithmeticSourceHomShortComplex K Ω a ha A).f.hom.toLinearMap
    ((Rep.mono_iff_injective _).mp hS.mono_f)
    (Rep.hom_comm_apply (arithmeticSourceHomShortComplex K Ω a ha A).f)
    (arithmeticSourceHomShortComplex K Ω a ha A).g.hom.toLinearMap
    ((Rep.epi_iff_surjective _).mp hS.epi_g)
    (Rep.hom_comm_apply (arithmeticSourceHomShortComplex K Ω a ha A).g)
    hm.exact.moduleCat_range_eq_ker
    (arithmeticSourceSUnitHomAction_continuous K Ω a ha A hA)
    (arithmeticSourceIdeleHomAction_continuous K Ω a ha A hA)
    continuous_of_discreteTopology x

end
end Dubon2026
