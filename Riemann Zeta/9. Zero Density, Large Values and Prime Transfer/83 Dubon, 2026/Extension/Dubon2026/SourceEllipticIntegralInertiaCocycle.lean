import Dubon2026.SourceEllipticIntegralGoodModelChange
import Dubon2026.SourceEllipticInertiaConjugate

/-! The actual Galois coordinate-change cocycle descends to the valuation
ring and acts on the residue model. This discharges the integral-lift and
residue-stabilizer inputs to the torsion-equivariance step in DUB-17/18.
The unit-two/three hypotheses are supplied by the required characteristic
at least five application; no cocycle lift or residue action is postulated. -/
namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve IsLocalRing
noncomputable section
variable {F M : Type*} [Field F] [Field M] [Algebra F M] {A : ValuationSubring M}

theorem cocycle_smul_conjugate (E : WeierstrassCurve F) (W : WeierstrassCurve A)
    (κ : VariableChange M) (hκ : κ • E.baseChange M = W.map A.subtype)
    (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F) :
    (κ * (κ.map (σ : M →+* M))⁻¹) • (conjugateModel W σ hσ).map A.subtype =
      W.map A.subtype := by
  have h1 : (conjugateModel W σ hσ).map A.subtype =
      κ.map (σ : M →+* M) • E.baseChange M := by
    have hE : (E.baseChange M).map (σ : M →+* M) = E.baseChange M :=
      E.map_baseChange (σ : M →ₐ[F] M)
    rw [conjugateModel_map_subtype, ← hκ, ← map_variableChange, hE]
  rw [h1, ← mul_smul, inv_mul_cancel_right, hκ]

theorem exists_integral_inertia_cocycle (h2 : IsUnit (2 : A)) (h3 : IsUnit (3 : A))
    (E : WeierstrassCurve F) (W : WeierstrassCurve A) (κ : VariableChange M)
    (hκ : κ • E.baseChange M = W.map A.subtype) (hW : IsUnit W.Δ)
    (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F) :
    ∃ g : VariableChange A,
      g.map A.subtype = κ * (κ.map (σ : M →+* M))⁻¹ ∧
      g • conjugateModel W σ hσ = W ∧
      ((⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F →
        g.map (residue A) • W.map (residue A) = W.map (residue A)) := by
  obtain ⟨g, hg⟩ := exists_integral_change_of_good_models A h2 h3 W (conjugateModel W σ hσ)
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
