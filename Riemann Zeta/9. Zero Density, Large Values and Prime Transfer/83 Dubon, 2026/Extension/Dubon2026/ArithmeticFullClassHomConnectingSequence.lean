import Dubon2026.ArithmeticClassHomCohomologyComparison
import Dubon2026.ArithmeticSourceHomConnectingSequence

/-! # Original continuous connecting sequence using full classes modulo outside units

The proved prime-field Hom comparison transports the actual source quotient
and connecting maps. Exactness therefore holds at the original full-class
Hom H1 and S-unit Hom H2 terms. The arithmetic class-formation and original
local restriction comparisons remain the missing edges of DUB-17 duality.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  [IsAlgClosure K Ω] (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (A : Rep.{0} ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K))
  [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (hA : Continuous (fun z : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) × A => A.ρ z.1 z.2))
  (q : ℕ) [Fact q.Prime] [Module (ZMod q) A] (hqa : (q : 𝓞 K) ∣ a)
  [TopologicalSpace (arithmeticSourceSUnitHomRep K Ω a ha A)]
  [DiscreteTopology (arithmeticSourceSUnitHomRep K Ω a ha A)]
  [TopologicalSpace (arithmeticSourceIdeleHomRep K Ω a ha A)]
  [DiscreteTopology (arithmeticSourceIdeleHomRep K Ω a ha A)]
  [TopologicalSpace (arithmeticSourceClassHomRep K Ω a ha A)]
  [DiscreteTopology (arithmeticSourceClassHomRep K Ω a ha A)]
  [TopologicalSpace (arithmeticFullClassHomRep K Ω a ha A)]
  [DiscreteTopology (arithmeticFullClassHomRep K Ω a ha A)]

/-- The original coefficient structure used in this comparison. -/
local instance fullClassConnectingUnitSMul : @ContinuousSMul ℤ (arithmeticSourceSUnitHomRep K Ω a ha A)
    (arithmeticSourceSUnitHomRep K Ω a ha A).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩
/-- The original coefficient structure used in this comparison. -/
local instance fullClassConnectingIdeleSMul : @ContinuousSMul ℤ (arithmeticSourceIdeleHomRep K Ω a ha A)
    (arithmeticSourceIdeleHomRep K Ω a ha A).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩
/-- The original coefficient structure used in this comparison. -/
local instance fullClassConnectingSourceSMul : @ContinuousSMul ℤ (arithmeticSourceClassHomRep K Ω a ha A)
    (arithmeticSourceClassHomRep K Ω a ha A).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩
/-- The original coefficient structure used in this comparison. -/
local instance fullClassConnectingTargetSMul : @ContinuousSMul ℤ (arithmeticFullClassHomRep K Ω a ha A)
    (arithmeticFullClassHomRep K Ω a ha A).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

/-- The original source idele H1 map with the proved full-class Hom target identification. -/
def arithmeticFullClassHomH1Quotient :
    ContinuousRepresentationH1 (arithmeticSourceIdeleHomRep K Ω a ha A)
      (arithmeticSourceIdeleHomAction_continuous K Ω a ha A hA) →+
    ContinuousRepresentationH1 (arithmeticFullClassHomRep K Ω a ha A)
      (arithmeticFullClassHomAction_continuous K Ω a ha A hA) :=
  (arithmeticSourceClassHomH1Equiv K Ω a ha A hA q hqa).toAddMonoidHom.comp
    (arithmeticSourceHomH1Quotient K Ω a ha A hA).toAddMonoidHom

/-- The original connecting map with full-class Hom coefficients, obtained through the literal comparison. -/
def arithmeticFullClassHomConnectingMap :
    ContinuousRepresentationH1 (arithmeticFullClassHomRep K Ω a ha A)
      (arithmeticFullClassHomAction_continuous K Ω a ha A hA) →+
    ContinuousRepresentationH2 (arithmeticSourceSUnitHomRep K Ω a ha A)
      (arithmeticSourceSUnitHomAction_continuous K Ω a ha A hA) :=
  (arithmeticSourceHomConnectingMap K Ω a ha A hA q hqa).toAddMonoidHom.comp
    (arithmeticSourceClassHomH1Equiv K Ω a ha A hA q hqa).symm.toAddMonoidHom

/-- The original source quotient has exactly the full-class Hom connecting kernel as its image. -/
theorem arithmeticFullClassHomConnecting_H1_range_eq_ker :
    (arithmeticFullClassHomH1Quotient K Ω a ha A hA q hqa).range =
      (arithmeticFullClassHomConnectingMap K Ω a ha A hA q hqa).ker := by
  ext c
  change (∃ j, arithmeticSourceClassHomH1Equiv K Ω a ha A hA q hqa
    (arithmeticSourceHomH1Quotient K Ω a ha A hA j) = c) ↔
      arithmeticSourceHomConnectingMap K Ω a ha A hA q hqa
        ((arithmeticSourceClassHomH1Equiv K Ω a ha A hA q hqa).symm c) = 0
  constructor
  · rintro ⟨j, rfl⟩
    rw [AddEquiv.symm_apply_apply]
    have h : arithmeticSourceHomH1Quotient K Ω a ha A hA j ∈
        LinearMap.range (arithmeticSourceHomH1Quotient K Ω a ha A hA) := ⟨j, rfl⟩
    rw [arithmeticSourceHomConnecting_H1_range_eq_ker K Ω a ha A hA q hqa] at h
    exact h
  · intro hc
    have h : (arithmeticSourceClassHomH1Equiv K Ω a ha A hA q hqa).symm c ∈
        LinearMap.ker (arithmeticSourceHomConnectingMap K Ω a ha A hA q hqa) := hc
    rw [← arithmeticSourceHomConnecting_H1_range_eq_ker K Ω a ha A hA q hqa] at h
    obtain ⟨j, hj⟩ := h
    exact ⟨j, (congrArg (arithmeticSourceClassHomH1Equiv K Ω a ha A hA q hqa) hj).trans
      ((arithmeticSourceClassHomH1Equiv K Ω a ha A hA q hqa).apply_symm_apply c)⟩

/-- Full-class Hom H1 connecting images are exactly the original S-unit Hom H2 classes killed in source ideles. -/
theorem arithmeticFullClassHomConnecting_H2_range_eq_ker :
    (arithmeticFullClassHomConnectingMap K Ω a ha A hA q hqa).range =
      (arithmeticSourceHomH2Inclusion K Ω a ha A hA).toAddMonoidHom.ker := by
  have he : (arithmeticFullClassHomConnectingMap K Ω a ha A hA q hqa).range =
      (arithmeticSourceHomConnectingMap K Ω a ha A hA q hqa).toAddMonoidHom.range := by
    ext y
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨(arithmeticSourceClassHomH1Equiv K Ω a ha A hA q hqa).symm c, rfl⟩
    · rintro ⟨c, rfl⟩
      refine ⟨arithmeticSourceClassHomH1Equiv K Ω a ha A hA q hqa c, ?_⟩
      change arithmeticSourceHomConnectingMap K Ω a ha A hA q hqa
        ((arithmeticSourceClassHomH1Equiv K Ω a ha A hA q hqa).symm
          (arithmeticSourceClassHomH1Equiv K Ω a ha A hA q hqa c)) = _
      rw [AddEquiv.symm_apply_apply]
      rfl
  exact he.trans (congrArg Submodule.toAddSubgroup
    (arithmeticSourceHomConnecting_H2_range_eq_ker K Ω a ha A hA q hqa))

end
end Dubon2026
