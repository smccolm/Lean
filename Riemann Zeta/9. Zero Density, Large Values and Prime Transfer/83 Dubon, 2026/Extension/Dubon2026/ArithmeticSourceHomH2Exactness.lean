import Dubon2026.ArithmeticSourceHomContinuity
import Dubon2026.ContinuousCoefficientH2MiddleExactness

/-! # Actual continuous H2 exactness for the arithmetic source Hom coefficients

The original arithmetic Hom short exact sequence and the proved continuous
actions instantiate the existing continuous cohomology exactness theorem.
The maps remain literal original diagonal/quotient postcomposition on every
continuous cocycle. This is the source sequence input for DUB-17 arithmetic
duality, before the still required local and global class comparisons.
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
  [TopologicalSpace (arithmeticSourceClassHomRep K Ω a ha A)]
  [DiscreteTopology (arithmeticSourceClassHomRep K Ω a ha A)]

local instance : @ContinuousSMul ℤ (arithmeticSourceSUnitHomRep K Ω a ha A)
    (arithmeticSourceSUnitHomRep K Ω a ha A).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩
local instance : @ContinuousSMul ℤ (arithmeticSourceIdeleHomRep K Ω a ha A)
    (arithmeticSourceIdeleHomRep K Ω a ha A).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩
local instance : @ContinuousSMul ℤ (arithmeticSourceClassHomRep K Ω a ha A)
    (arithmeticSourceClassHomRep K Ω a ha A).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

/-- Actual continuous H2 postcomposition with the original arithmetic source diagonal. -/
def arithmeticSourceHomH2Inclusion :
    ContinuousRepresentationH2 (arithmeticSourceSUnitHomRep K Ω a ha A)
      (arithmeticSourceSUnitHomAction_continuous K Ω a ha A hA) →ₗ[ℤ]
    ContinuousRepresentationH2 (arithmeticSourceIdeleHomRep K Ω a ha A)
      (arithmeticSourceIdeleHomAction_continuous K Ω a ha A hA) :=
  continuousCoefficientH2Map (arithmeticSourceSUnitHomRep K Ω a ha A)
    (arithmeticSourceIdeleHomRep K Ω a ha A)
    (arithmeticSourceHomShortComplex K Ω a ha A).f.hom.toLinearMap
    continuous_of_discreteTopology (Rep.hom_comm_apply (arithmeticSourceHomShortComplex K Ω a ha A).f)
    (arithmeticSourceSUnitHomAction_continuous K Ω a ha A hA)
    (arithmeticSourceIdeleHomAction_continuous K Ω a ha A hA)

/-- Actual continuous H2 postcomposition with the original arithmetic source class quotient. -/
def arithmeticSourceHomH2Quotient :
    ContinuousRepresentationH2 (arithmeticSourceIdeleHomRep K Ω a ha A)
      (arithmeticSourceIdeleHomAction_continuous K Ω a ha A hA) →ₗ[ℤ]
    ContinuousRepresentationH2 (arithmeticSourceClassHomRep K Ω a ha A)
      (arithmeticSourceClassHomAction_continuous K Ω a ha A hA) :=
  continuousCoefficientH2Map (arithmeticSourceIdeleHomRep K Ω a ha A)
    (arithmeticSourceClassHomRep K Ω a ha A)
    (arithmeticSourceHomShortComplex K Ω a ha A).g.hom.toLinearMap
    continuous_of_discreteTopology (Rep.hom_comm_apply (arithmeticSourceHomShortComplex K Ω a ha A).g)
    (arithmeticSourceIdeleHomAction_continuous K Ω a ha A hA)
    (arithmeticSourceClassHomAction_continuous K Ω a ha A hA)

variable [IsAlgClosure K Ω] (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 K) ∣ a)
  [Module (ZMod q) A]

include hqa in
/-- The original continuous arithmetic Hom H2 inclusion has exactly the original quotient-map kernel as its image. -/
theorem arithmeticSourceHomH2_range_eq_ker :
    LinearMap.range (arithmeticSourceHomH2Inclusion K Ω a ha A hA) =
      LinearMap.ker (arithmeticSourceHomH2Quotient K Ω a ha A hA) := by
  have hS := arithmeticSourceHomShortComplex_shortExact K Ω a ha A q hqa
  have hm := hS.map_of_exact
    (forget₂ (Rep ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K)) (ModuleCat ℤ))
  exact continuousCoefficientH2_middle_range_eq_ker
    (arithmeticSourceSUnitHomRep K Ω a ha A)
    (arithmeticSourceIdeleHomRep K Ω a ha A)
    (arithmeticSourceClassHomRep K Ω a ha A)
    (arithmeticSourceHomShortComplex K Ω a ha A).f.hom.toLinearMap
    ((Rep.mono_iff_injective _).mp hS.mono_f) continuous_of_discreteTopology
    (Rep.hom_comm_apply (arithmeticSourceHomShortComplex K Ω a ha A).f)
    (arithmeticSourceHomShortComplex K Ω a ha A).g.hom.toLinearMap
    ((Rep.epi_iff_surjective _).mp hS.epi_g)
    (Rep.hom_comm_apply (arithmeticSourceHomShortComplex K Ω a ha A).g)
    hm.exact.moduleCat_range_eq_ker
    (arithmeticSourceSUnitHomAction_continuous K Ω a ha A hA)
    (arithmeticSourceIdeleHomAction_continuous K Ω a ha A hA)
    (arithmeticSourceClassHomAction_continuous K Ω a ha A hA)

end
end Dubon2026
