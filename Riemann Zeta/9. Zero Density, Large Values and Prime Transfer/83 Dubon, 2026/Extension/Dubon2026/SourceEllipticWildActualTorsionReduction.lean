import Dubon2026.SourceEllipticWildInertiaCocycle
import Dubon2026.SourceEllipticModelTorsionEquivariance
import Dubon2026.SourceEllipticPositiveCharacteristicCocycle

/-! DUB-17/18 -> characteristic-three modular good reduction -> faithful
prescribed elliptic specialization. Reuse the existing actual field, torsion,
place and point maps, with the newly proved integral inertia cocycle valid
in every residue characteristic. The Legendre field requires only two nonzero.
Wild census and the remaining characteristic-two model branch remain open. -/
namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve IsLocalRing SourceEllipticVariableChange
noncomputable section

theorem exists_actual_inertia_torsion_reduction_all_characteristics
    {F M : Type*} [Field F] [Field M] [Algebra F M] [DecidableEq M]
    {A : ValuationSubring M} [DecidableEq (ResidueField A)]
    (K : Type*) [Field K] [Algebra K A]
    (E : WeierstrassCurve F) (W : WeierstrassCurve A) (κ : VariableChange M)
    (hκ : κ • E.baseChange M = W.map A.subtype) (hW : IsUnit W.Δ)
    (N : ℕ) (hNK : (N : K) ≠ 0) :
    ∃ θ : Submodule.torsionBy ℤ (E.baseChange M).toAffine.Point (N : ℤ) →+
        (W.map (residue A)).toAffine.Point,
      Function.Injective θ ∧
      (∀ P, θ P = reducePoint ((map_residue_Δ_ne_zero_iff W).mpr hW)
        (modelPointEquiv E W κ hκ P)) ∧
      ∀ (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F),
        (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F →
        ∃ g : VariableChange A,
          g.map A.subtype = κ * (κ.map (σ : M →+* M))⁻¹ ∧
          g.map (residue A) • W.map (residue A) = W.map (residue A) ∧
          ∀ P, HEq (vcInvFun (g.map (residue A)) (W.map (residue A)).toAffine (θ P))
            (θ (galoisTorsionMap E N σ P)) := by
  have hN : IsUnit (N : A) := by
    simpa only [map_natCast] using hNK.isUnit.map (algebraMap K A)
  have hΔ : (W.map (residue A)).Δ ≠ 0 := (map_residue_Δ_ne_zero_iff W).mpr hW
  let θ := modelTorsionReduction E W κ hκ hΔ hN
  refine ⟨θ, modelTorsionReduction_injective E W κ hκ hΔ hN, fun _ => rfl, ?_⟩
  intro σ hσ hσI
  obtain ⟨g, hg, -, hgres⟩ := exists_integral_inertia_cocycle_all_characteristics
    E W κ hκ hW σ hσ
  refine ⟨g, hg, hgres hσI, ?_⟩
  intro P
  exact modelTorsionReduction_inertia E W κ hκ hΔ hN g σ hσ hσI hg (hgres hσI) P

end
end Dubon2026.SourceEllipticReduction
