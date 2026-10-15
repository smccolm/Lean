import Dubon2026.ArithmeticSourceHomH2Exactness
import Dubon2026.ContinuousConnectingH1Exactness

/-! # Original arithmetic Hom connecting sequence

The actual source coefficient maps and the derived Hom exactness supply the
continuous connecting map, with exactness at the original class Hom H1 and
S-unit Hom H2 terms. The existing continuous lift/coboundary proofs perform
the deduction. This serves the source global-duality sequence for DUB-17;
the class-formation and localization comparisons remain separate.
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

/-- Actual continuous H1 postcomposition with the original source class quotient. -/
def arithmeticSourceHomH1Quotient :
    ContinuousRepresentationH1 (arithmeticSourceIdeleHomRep K Ω a ha A)
      (arithmeticSourceIdeleHomAction_continuous K Ω a ha A hA) →ₗ[ℤ]
    ContinuousRepresentationH1 (arithmeticSourceClassHomRep K Ω a ha A)
      (arithmeticSourceClassHomAction_continuous K Ω a ha A hA) :=
  continuousCoefficientH1Map (arithmeticSourceIdeleHomRep K Ω a ha A)
    (arithmeticSourceClassHomRep K Ω a ha A)
    (arithmeticSourceHomShortComplex K Ω a ha A).g.hom.toLinearMap
    continuous_of_discreteTopology (Rep.hom_comm_apply (arithmeticSourceHomShortComplex K Ω a ha A).g)
    (arithmeticSourceIdeleHomAction_continuous K Ω a ha A hA)
    (arithmeticSourceClassHomAction_continuous K Ω a ha A hA)

variable [IsAlgClosure K Ω] (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 K) ∣ a)
  [Module (ZMod q) A]

/-- The original arithmetic Hom sequence supplies its actual continuous H1-to-H2 connecting map. -/
def arithmeticSourceHomConnectingMap :
    ContinuousRepresentationH1 (arithmeticSourceClassHomRep K Ω a ha A)
      (arithmeticSourceClassHomAction_continuous K Ω a ha A hA) →ₗ[ℤ]
    ContinuousRepresentationH2 (arithmeticSourceSUnitHomRep K Ω a ha A)
      (arithmeticSourceSUnitHomAction_continuous K Ω a ha A hA) := by
  have hS := arithmeticSourceHomShortComplex_shortExact K Ω a ha A q hqa
  have hm := hS.map_of_exact
    (forget₂ (Rep ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K)) (ModuleCat ℤ))
  exact continuousCoefficientConnectingMap
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
    (arithmeticSourceClassHomAction_continuous K Ω a ha A hA)

/-- The original arithmetic class Hom H1 quotient image is exactly the connecting-map kernel. -/
theorem arithmeticSourceHomConnecting_H1_range_eq_ker :
    LinearMap.range (arithmeticSourceHomH1Quotient K Ω a ha A hA) =
      LinearMap.ker (arithmeticSourceHomConnectingMap K Ω a ha A hA q hqa) := by
  have hS := arithmeticSourceHomShortComplex_shortExact K Ω a ha A q hqa
  have hm := hS.map_of_exact
    (forget₂ (Rep ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K)) (ModuleCat ℤ))
  exact continuousConnectingH1_range_eq_ker
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

/-- The original arithmetic connecting map has exactly the actual S-unit Hom H2 inclusion kernel as its image. -/
theorem arithmeticSourceHomConnecting_H2_range_eq_ker :
    LinearMap.range (arithmeticSourceHomConnectingMap K Ω a ha A hA q hqa) =
      LinearMap.ker (arithmeticSourceHomH2Inclusion K Ω a ha A hA) := by
  have hS := arithmeticSourceHomShortComplex_shortExact K Ω a ha A q hqa
  have hm := hS.map_of_exact
    (forget₂ (Rep ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K)) (ModuleCat ℤ))
  exact continuousConnectingH2_range_eq_ker
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
