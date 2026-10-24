import Dubon2026.SourceEllipticWildChosenCocycle
import Dubon2026.SourceEllipticModelTorsionEquivariance

/-! DUB-17/18 -> characteristic-three modular good reduction -> faithful
prescribed elliptic specialization. Reuse the existing actual field, torsion,
place and point maps, with the newly proved integral inertia cocycle valid
in every residue characteristic. The Legendre field requires only two nonzero.
Wild census and the remaining characteristic-two model branch remain open. -/
namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve IsLocalRing SourceEllipticVariableChange
noncomputable section
variable {F M : Type*} [Field F] [Field M] [Algebra F M] {A : ValuationSubring M}
variable (E : WeierstrassCurve F) (W : WeierstrassCurve A) (κ : VariableChange M)
variable (hκ : κ • E.baseChange M = W.map A.subtype) (hW : IsUnit W.Δ)

/-- The actual residue coordinate changes form a homomorphism on inertia. -/
def residueInertiaHomAll : A.inertiaSubgroup F →* VariableChange (ResidueField A) :=
  MonoidHom.mk' (fun σ => (integralInertiaCocycleAll E W κ hκ hW σ).map (residue A))
    (integralInertiaCocycleAll_residue_mul E W κ hκ hW)

theorem residueInertiaHomAll_eq_map (σ : A.inertiaSubgroup F) (g : VariableChange A)
    (hg : g.map A.subtype = κ * (κ.map (σ.val.val : M →+* M))⁻¹) :
    residueInertiaHomAll E W κ hκ hW σ = g.map (residue A) := by
  have h : integralInertiaCocycleAll E W κ hκ hW σ = g :=
    VariableChange.map_injective Subtype.val_injective
      ((integralInertiaCocycleAll_generic E W κ hκ hW σ).trans hg.symm)
  change (integralInertiaCocycleAll E W κ hκ hW σ).map (residue A) = _
  rw [h]

theorem residueInertiaHomAll_stabilizes (σ : A.inertiaSubgroup F) :
    residueInertiaHomAll E W κ hκ hW σ • W.map (residue A) = W.map (residue A) :=
  integralInertiaCocycleAll_residue_stabilizes E W κ hκ hW σ

theorem residueInertiaHomAll_torsion_equivariance [DecidableEq M] [DecidableEq (ResidueField A)]
    {N : ℕ} (hN : IsUnit (N : A)) (σ : A.inertiaSubgroup F)
    (P : Submodule.torsionBy ℤ (E.baseChange M).toAffine.Point (N : ℤ)) :
    HEq (vcInvFun (residueInertiaHomAll E W κ hκ hW σ) (W.map (residue A)).toAffine
      (modelTorsionReduction E W κ hκ ((map_residue_Δ_ne_zero_iff W).mpr hW) hN P))
      (modelTorsionReduction E W κ hκ ((map_residue_Δ_ne_zero_iff W).mpr hW) hN
        (galoisTorsionMap E N σ.val.val P)) :=
  modelTorsionReduction_inertia E W κ hκ ((map_residue_Δ_ne_zero_iff W).mpr hW) hN
    (integralInertiaCocycleAll E W κ hκ hW σ) σ.val.val σ.val.property σ.property
    (integralInertiaCocycleAll_generic E W κ hκ hW σ)
    (residueInertiaHomAll_stabilizes E W κ hκ hW σ) P

end
end Dubon2026.SourceEllipticReduction
