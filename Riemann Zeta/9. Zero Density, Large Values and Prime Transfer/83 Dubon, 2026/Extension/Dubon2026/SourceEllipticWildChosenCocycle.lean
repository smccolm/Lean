import Dubon2026.SourceEllipticWildInertiaCocycle
import Dubon2026.SourceEllipticResidueCocycleMultiplication

/-! DUB-17/18 -> characteristic-three modular good reduction -> faithful
prescribed elliptic specialization. Reuse the existing actual field, torsion,
place and point maps, with the newly proved integral inertia cocycle valid
in every residue characteristic. The Legendre field requires only two nonzero.
Wild census and the remaining characteristic-two model branch remain open. -/
namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve IsLocalRing
noncomputable section
variable {F M : Type*} [Field F] [Field M] [Algebra F M] {A : ValuationSubring M}
variable (E : WeierstrassCurve F) (W : WeierstrassCurve A) (κ : VariableChange M)
variable (hκ : κ • E.baseChange M = W.map A.subtype) (hW : IsUnit W.Δ)

/-- The integral lift of the actual generic coordinate cocycle, chosen from its proved existence. -/
def integralInertiaCocycleAll (σ : A.inertiaSubgroup F) : VariableChange A :=
  (exists_integral_inertia_cocycle_all_characteristics E W κ hκ hW σ.val.val σ.val.property).choose

theorem integralInertiaCocycleAll_generic (σ : A.inertiaSubgroup F) :
    (integralInertiaCocycleAll E W κ hκ hW σ).map A.subtype =
      κ * (κ.map (σ.val.val : M →+* M))⁻¹ :=
  (exists_integral_inertia_cocycle_all_characteristics E W κ hκ hW σ.val.val σ.val.property).choose_spec.1

theorem integralInertiaCocycleAll_residue_stabilizes (σ : A.inertiaSubgroup F) :
    (integralInertiaCocycleAll E W κ hκ hW σ).map (residue A) • W.map (residue A) =
      W.map (residue A) :=
  (exists_integral_inertia_cocycle_all_characteristics E W κ hκ hW σ.val.val σ.val.property).choose_spec.2.2
    σ.property

theorem integralInertiaCocycleAll_residue_mul (σ τ : A.inertiaSubgroup F) :
    (integralInertiaCocycleAll E W κ hκ hW (σ * τ)).map (residue A) =
      (integralInertiaCocycleAll E W κ hκ hW σ).map (residue A) *
      (integralInertiaCocycleAll E W κ hκ hW τ).map (residue A) :=
  residue_cocycle_mul κ σ.val.val τ.val.val σ.val.property σ.property
    (integralInertiaCocycleAll E W κ hκ hW σ)
    (integralInertiaCocycleAll E W κ hκ hW τ)
    (integralInertiaCocycleAll E W κ hκ hW (σ * τ))
    (integralInertiaCocycleAll_generic E W κ hκ hW σ)
    (integralInertiaCocycleAll_generic E W κ hκ hW τ)
    (integralInertiaCocycleAll_generic E W κ hκ hW (σ * τ))

end
end Dubon2026.SourceEllipticReduction
