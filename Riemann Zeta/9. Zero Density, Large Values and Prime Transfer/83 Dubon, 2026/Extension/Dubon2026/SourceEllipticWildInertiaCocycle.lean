import Dubon2026.SourceEllipticWildGoodModelChange
import Dubon2026.SourceEllipticIntegralInertiaCocycle

/-! DUB-17/18 -> wild good reduction -> actual inertia specialization.
The actual coordinate cocycle descends to the valuation ring and its
residue stabilizes the actual good model in every residue characteristic.
No integral lift or residue action is supplied as a certificate. -/
namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve IsLocalRing
noncomputable section
variable {F M : Type*} [Field F] [Field M] [Algebra F M] {A : ValuationSubring M}

theorem exists_integral_inertia_cocycle_all_characteristics
    (E : WeierstrassCurve F) (W : WeierstrassCurve A) (κ : VariableChange M)
    (hκ : κ • E.baseChange M = W.map A.subtype) (hW : IsUnit W.Δ)
    (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F) :
    ∃ g : VariableChange A,
      g.map A.subtype = κ * (κ.map (σ : M →+* M))⁻¹ ∧
      g • conjugateModel W σ hσ = W ∧
      ((⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F →
        g.map (residue A) • W.map (residue A) = W.map (residue A)) := by
  obtain ⟨g, hg⟩ := exists_integral_change_of_good_models_all_characteristics A W (conjugateModel W σ hσ)
    _ (cocycle_smul_conjugate E W κ hκ σ hσ) hW
    (isUnit_conjugateModel_discriminant W σ hσ hW)
  have hgc : g • conjugateModel W σ hσ = W := by
    apply WeierstrassCurve.map_injective (f := A.subtype) Subtype.val_injective
    change (g • conjugateModel W σ hσ).map A.subtype = W.map A.subtype
    rw [← map_variableChange, hg, cocycle_smul_conjugate E W κ hκ σ hσ]
  refine ⟨g, hg, hgc, ?_⟩
  intro hσI
  conv_lhs => rw [← conjugateModel_map_residue W σ hσ hσI]
  rw [map_variableChange, hgc]

end
end Dubon2026.SourceEllipticReduction
