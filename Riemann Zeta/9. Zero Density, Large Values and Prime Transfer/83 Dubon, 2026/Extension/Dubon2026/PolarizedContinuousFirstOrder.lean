import Dubon2026.PolarizedDiscreteContinuity
import Dubon2026.PolarizedFirstOrderConjugacy
import Dubon2026.ContinuousAlgebraicH1Injection

/-! The actual continuous fixed-similitude polarized first-order fiber and
its strict classes. Existing continuous cocycles and the faithful H1 map
give the source tangent classification needed in DUB-17's Selmer chain. -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace G] [TopologicalSpace R] [DiscreteTopology R]

/-- Actual continuous dual-number lifts of the original polarized representation with fixed similitude. -/
def ContinuousPolarizedFirstOrderLift (ρ : G →* PolarizedGaloisGroup ι R) :=
  {τ : PolarizedFirstOrderLift ρ // Continuous τ.val}

/-- The original continuous polarized fiber is exactly the existing continuous full-adjoint cocycle module. -/
def continuousPolarizedFirstOrderLiftEquiv (ρ : G →* PolarizedGaloisGroup ι R)
    (hρ : Continuous ρ) :
    ContinuousPolarizedFirstOrderLift ρ ≃ continuousRepresentationCocyclesOne (polarizedAdjointRep ρ) where
  toFun τ := ⟨polarizedFirstOrderCocycle ρ τ.val,
    polarizedFirstOrderCocycle_continuous ρ hρ τ.val τ.property⟩
  invFun c := ⟨polarizedFirstOrderLiftFromCocycle ρ c.val,
    polarizedFirstOrderLiftFromCocycle_continuous ρ hρ c.val c.property⟩
  left_inv τ := Subtype.ext (polarizedFirstOrderLiftFromCocycle_cocycle ρ τ.val)
  right_inv c := Subtype.ext (polarizedFirstOrderCocycle_fromCocycle ρ c.val)

/-- The actual class of the original continuous polarized lift in the existing continuous H1. -/
def continuousPolarizedFirstOrderClass (ρ : G →* PolarizedGaloisGroup ι R) (hρ : Continuous ρ)
    (τ : ContinuousPolarizedFirstOrderLift ρ) :
    ContinuousRepresentationH1 (polarizedAdjointRep ρ) (polarizedAdjointAction_continuous ρ hρ) :=
  Submodule.Quotient.mk (continuousPolarizedFirstOrderLiftEquiv ρ hρ τ)

/-- Equality of original continuous full-adjoint classes is exactly the source strict change of basis. -/
theorem continuousPolarizedFirstOrderClass_eq_iff
    (ρ : G →* PolarizedGaloisGroup ι R) (hρ : Continuous ρ)
    (τ σ : ContinuousPolarizedFirstOrderLift ρ) :
    continuousPolarizedFirstOrderClass ρ hρ τ = continuousPolarizedFirstOrderClass ρ hρ σ ↔
      PolarizedFirstOrderStrictlyConjugate ρ τ.val σ.val := by
  rw [polarizedFirstOrderStrictlyConjugate_iff]
  constructor
  · intro h
    exact congrArg (continuousH1ToAlgebraic (polarizedAdjointRep ρ)
      (polarizedAdjointAction_continuous ρ hρ)) h
  · intro h
    apply continuousH1ToAlgebraic_injective (polarizedAdjointRep ρ)
      (polarizedAdjointAction_continuous ρ hρ)
    exact h

/-- Every original continuous full-adjoint H1 class comes from a genuine continuous fixed-similitude lift. -/
theorem continuousPolarizedFirstOrderClass_surjective
    (ρ : G →* PolarizedGaloisGroup ι R) (hρ : Continuous ρ) :
    Function.Surjective (continuousPolarizedFirstOrderClass ρ hρ) := by
  intro x
  induction x using Quotient.inductionOn' with
  | h c =>
    refine ⟨(continuousPolarizedFirstOrderLiftEquiv ρ hρ).symm c, ?_⟩
    change Submodule.Quotient.mk (continuousPolarizedFirstOrderLiftEquiv ρ hρ
      ((continuousPolarizedFirstOrderLiftEquiv ρ hρ).symm c)) = _
    rw [Equiv.apply_symm_apply]
    rfl

end
end Dubon2026
