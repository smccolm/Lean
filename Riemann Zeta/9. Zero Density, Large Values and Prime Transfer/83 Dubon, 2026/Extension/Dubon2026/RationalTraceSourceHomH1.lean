import Dubon2026.ArithmeticSourceHomH1Kernel
import Dubon2026.RationalTraceIntegerActionContinuity

/-! # The original arithmetic trace-dual H1 in the source idele sequence

The existing Cartier/trace H1 equivalence enters the newly constructed
original source Hom sequence. Thus the actual global trace-dual classes
killed by its source idele map are exactly the original invariant class-Hom
connecting classes. The comparison with the actual local restriction sum
and class-formation duality remains required for DUB-17 global duality.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (hσ : Continuous σ) (hqa : (q : 𝓞 ℚ) ∣ a)
  (hn : (Fintype.card ι : ZMod q) ≠ 0)

local instance : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
  have hAlg : @AlgebraicClosure.instAlgebra ℚ _ ℚ _ (Algebra.id ℚ) =
      (inferInstance : Algebra ℚ (AlgebraicClosure ℚ)) := Subsingleton.elim _ _
  have h := AlgebraicClosure.instIsAlgClosure ℚ
  rw [hAlg] at h
  exact h

/-- Prime-field scalar multiplication is the original trace-module operation. -/
local instance : Module (ZMod q) (rationalArithmeticTraceZeroIntegerRep a q σ) :=
  inferInstanceAs (Module (ZMod q) (matrixTraceZeroSubmodule ι (ZMod q)))
local instance : Finite (rationalArithmeticTraceZeroIntegerRep a q σ) :=
  inferInstanceAs (Finite (matrixTraceZeroSubmodule ι (ZMod q)))
/-- The original trace-module topology is used in the source Hom comparison. -/
local instance : TopologicalSpace (rationalArithmeticTraceZeroIntegerRep a q σ) :=
  rationalTraceIntegerCoefficientTopology a q σ
local instance : DiscreteTopology (rationalArithmeticTraceZeroIntegerRep a q σ) :=
  rationalTraceIntegerCoefficient_discrete a q σ

variable [TopologicalSpace (rationalArithmeticTraceSUnitHomRep a ha q σ)]
  [DiscreteTopology (rationalArithmeticTraceSUnitHomRep a ha q σ)]
  [TopologicalSpace (arithmeticSourceIdeleHomRep ℚ (AlgebraicClosure ℚ) a ha
    (rationalArithmeticTraceZeroIntegerRep a q σ))]
  [DiscreteTopology (arithmeticSourceIdeleHomRep ℚ (AlgebraicClosure ℚ) a ha
    (rationalArithmeticTraceZeroIntegerRep a q σ))]

/-- The identified source S-unit Hom coefficient inherits its actual trace Hom topology. -/
local instance : TopologicalSpace (arithmeticSourceSUnitHomRep ℚ (AlgebraicClosure ℚ) a ha
    (rationalArithmeticTraceZeroIntegerRep a q σ)) :=
  inferInstanceAs (TopologicalSpace (rationalArithmeticTraceSUnitHomRep a ha q σ))
local instance : DiscreteTopology (arithmeticSourceSUnitHomRep ℚ (AlgebraicClosure ℚ) a ha
    (rationalArithmeticTraceZeroIntegerRep a q σ)) :=
  inferInstanceAs (DiscreteTopology (rationalArithmeticTraceSUnitHomRep a ha q σ))

local instance : @ContinuousSMul ℤ (rationalArithmeticTraceSUnitHomRep a ha q σ)
    (rationalArithmeticTraceSUnitHomRep a ha q σ).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

local instance : @ContinuousSMul ℤ
    (arithmeticSourceIdeleHomRep ℚ (AlgebraicClosure ℚ) a ha (rationalArithmeticTraceZeroIntegerRep a q σ))
    (arithmeticSourceIdeleHomRep ℚ (AlgebraicClosure ℚ) a ha
      (rationalArithmeticTraceZeroIntegerRep a q σ)).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

/-- The actual global trace-dual H1 class maps to original source idele Hom H1 through its proved Cartier identification and original diagonal. -/
def rationalTraceSourceIdeleH1Map :
    RationalArithmeticTraceDualH1 a q hqa σ hσ →+
      ContinuousRepresentationH1
        (arithmeticSourceIdeleHomRep ℚ (AlgebraicClosure ℚ) a ha
          (rationalArithmeticTraceZeroIntegerRep a q σ))
        (arithmeticSourceIdeleHomAction_continuous ℚ (AlgebraicClosure ℚ) a ha
          (rationalArithmeticTraceZeroIntegerRep a q σ) (rationalTraceIntegerAction_continuous a q σ hσ)) :=
  (arithmeticSourceHomH1Inclusion ℚ (AlgebraicClosure ℚ) a ha
    (rationalArithmeticTraceZeroIntegerRep a q σ)
    (rationalTraceIntegerAction_continuous a q σ hσ)).toAddMonoidHom.comp
      (rationalArithmeticTraceSUnitH1Equiv a ha q σ hσ hqa hn).toAddMonoidHom

/-- The actual trace-dual source-idele kernel is exactly the original invariant source-class Hom connecting image, without an assumed cohomology exactness relation. -/
theorem rationalTraceSourceIdeleH1Map_eq_zero_iff
    (x : RationalArithmeticTraceDualH1 a q hqa σ hσ) :
    rationalTraceSourceIdeleH1Map a ha q σ hσ hqa hn x = 0 ↔
      ∃ c : (arithmeticSourceClassHomRep ℚ (AlgebraicClosure ℚ) a ha
          (rationalArithmeticTraceZeroIntegerRep a q σ)).ρ.invariants,
        arithmeticSourceHomInvariantConnectingMap ℚ (AlgebraicClosure ℚ) a ha
          (rationalArithmeticTraceZeroIntegerRep a q σ)
          (rationalTraceIntegerAction_continuous a q σ hσ) q hqa c =
            rationalArithmeticTraceSUnitH1Equiv a ha q σ hσ hqa hn x := by
  have h := arithmeticSourceHomH1_kernel_eq_invariantConnecting_range ℚ (AlgebraicClosure ℚ) a ha
    (rationalArithmeticTraceZeroIntegerRep a q σ)
    (rationalTraceIntegerAction_continuous a q σ hσ) q hqa
  change _ ↔ rationalArithmeticTraceSUnitH1Equiv a ha q σ hσ hqa hn x ∈
    LinearMap.range (arithmeticSourceHomInvariantConnectingMap ℚ (AlgebraicClosure ℚ) a ha
      (rationalArithmeticTraceZeroIntegerRep a q σ)
      (rationalTraceIntegerAction_continuous a q σ hσ) q hqa)
  rw [h]
  rfl

end
end Dubon2026
