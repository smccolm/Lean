import Dubon2026.SourceEllipticResidueCocycleMultiplication

/-! Choose the proved integral coordinate cocycle on the actual inertia
group and retain its literal generic-fiber identity. Its residue fixes
the actual model and satisfies multiplication. These proved data supply
the inertia homomorphism needed by the DUB-17/18 exceptional-fiber census. -/
namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve IsLocalRing
noncomputable section
variable {F M : Type*} [Field F] [Field M] [Algebra F M] {A : ValuationSubring M}
variable (h2 : IsUnit (2 : A)) (h3 : IsUnit (3 : A))
variable (E : WeierstrassCurve F) (W : WeierstrassCurve A) (κ : VariableChange M)
variable (hκ : κ • E.baseChange M = W.map A.subtype) (hW : IsUnit W.Δ)

/-- The integral lift of the actual generic coordinate cocycle, chosen from its proved existence. -/
def integralInertiaCocycle (σ : A.inertiaSubgroup F) : VariableChange A :=
  (exists_integral_inertia_cocycle h2 h3 E W κ hκ hW σ.val.val σ.val.property).choose

theorem integralInertiaCocycle_generic (σ : A.inertiaSubgroup F) :
    (integralInertiaCocycle h2 h3 E W κ hκ hW σ).map A.subtype =
      κ * (κ.map (σ.val.val : M →+* M))⁻¹ :=
  (exists_integral_inertia_cocycle h2 h3 E W κ hκ hW σ.val.val σ.val.property).choose_spec.1

theorem integralInertiaCocycle_residue_stabilizes (σ : A.inertiaSubgroup F) :
    (integralInertiaCocycle h2 h3 E W κ hκ hW σ).map (residue A) • W.map (residue A) =
      W.map (residue A) :=
  (exists_integral_inertia_cocycle h2 h3 E W κ hκ hW σ.val.val σ.val.property).choose_spec.2.2
    σ.property

theorem integralInertiaCocycle_residue_mul (σ τ : A.inertiaSubgroup F) :
    (integralInertiaCocycle h2 h3 E W κ hκ hW (σ * τ)).map (residue A) =
      (integralInertiaCocycle h2 h3 E W κ hκ hW σ).map (residue A) *
      (integralInertiaCocycle h2 h3 E W κ hκ hW τ).map (residue A) :=
  residue_cocycle_mul κ σ.val.val τ.val.val σ.val.property σ.property
    (integralInertiaCocycle h2 h3 E W κ hκ hW σ)
    (integralInertiaCocycle h2 h3 E W κ hκ hW τ)
    (integralInertiaCocycle h2 h3 E W κ hκ hW (σ * τ))
    (integralInertiaCocycle_generic h2 h3 E W κ hκ hW σ)
    (integralInertiaCocycle_generic h2 h3 E W κ hκ hW τ)
    (integralInertiaCocycle_generic h2 h3 E W κ hκ hW (σ * τ))

end
end Dubon2026.SourceEllipticReduction
