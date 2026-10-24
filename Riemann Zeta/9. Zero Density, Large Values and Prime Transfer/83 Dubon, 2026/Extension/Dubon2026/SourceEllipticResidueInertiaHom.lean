import Dubon2026.SourceEllipticChosenInertiaCocycle
import Dubon2026.SourceEllipticModelTorsionEquivariance

/-! The derived coordinate action is a genuine homomorphism on the actual
inertia group, stabilizes the actual residue curve and intertwines the
original Galois torsion action with literal reduction. This is the action
needed for stabilizer-image and orbit counting in DUB-17/18. -/
namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve IsLocalRing SourceEllipticVariableChange
noncomputable section
variable {F M : Type*} [Field F] [Field M] [Algebra F M] {A : ValuationSubring M}
variable (h2 : IsUnit (2 : A)) (h3 : IsUnit (3 : A))
variable (E : WeierstrassCurve F) (W : WeierstrassCurve A) (κ : VariableChange M)
variable (hκ : κ • E.baseChange M = W.map A.subtype) (hW : IsUnit W.Δ)

/-- The actual residue coordinate changes form a homomorphism on inertia. -/
def residueInertiaHom : A.inertiaSubgroup F →* VariableChange (ResidueField A) :=
  MonoidHom.mk' (fun σ => (integralInertiaCocycle h2 h3 E W κ hκ hW σ).map (residue A))
    (integralInertiaCocycle_residue_mul h2 h3 E W κ hκ hW)

theorem residueInertiaHom_eq_map (σ : A.inertiaSubgroup F) (g : VariableChange A)
    (hg : g.map A.subtype = κ * (κ.map (σ.val.val : M →+* M))⁻¹) :
    residueInertiaHom h2 h3 E W κ hκ hW σ = g.map (residue A) := by
  have h : integralInertiaCocycle h2 h3 E W κ hκ hW σ = g :=
    VariableChange.map_injective Subtype.val_injective
      ((integralInertiaCocycle_generic h2 h3 E W κ hκ hW σ).trans hg.symm)
  change (integralInertiaCocycle h2 h3 E W κ hκ hW σ).map (residue A) = _
  rw [h]

theorem residueInertiaHom_stabilizes (σ : A.inertiaSubgroup F) :
    residueInertiaHom h2 h3 E W κ hκ hW σ • W.map (residue A) = W.map (residue A) :=
  integralInertiaCocycle_residue_stabilizes h2 h3 E W κ hκ hW σ

theorem residueInertiaHom_torsion_equivariance [DecidableEq M] [DecidableEq (ResidueField A)]
    {N : ℕ} (hN : IsUnit (N : A)) (σ : A.inertiaSubgroup F)
    (P : Submodule.torsionBy ℤ (E.baseChange M).toAffine.Point (N : ℤ)) :
    HEq (vcInvFun (residueInertiaHom h2 h3 E W κ hκ hW σ) (W.map (residue A)).toAffine
      (modelTorsionReduction E W κ hκ ((map_residue_Δ_ne_zero_iff W).mpr hW) hN P))
      (modelTorsionReduction E W κ hκ ((map_residue_Δ_ne_zero_iff W).mpr hW) hN
        (galoisTorsionMap E N σ.val.val P)) :=
  modelTorsionReduction_inertia E W κ hκ ((map_residue_Δ_ne_zero_iff W).mpr hW) hN
    (integralInertiaCocycle h2 h3 E W κ hκ hW σ) σ.val.val σ.val.property σ.property
    (integralInertiaCocycle_generic h2 h3 E W κ hκ hW σ)
    (residueInertiaHom_stabilizes h2 h3 E W κ hκ hW σ) P

end
end Dubon2026.SourceEllipticReduction
