import Dubon2026.SourceEllipticModelTorsionEquivariance
import Dubon2026.SourceEllipticPositiveCharacteristicCocycle

/-! Assemble actual inertia-equivariant prime-to-characteristic torsion
reduction through a good model. The original point map, integral Galois
cocycle, residue stabilizer action and injectivity are all derived.
The map is restricted to the actual N-torsion needed by the cyclic-subgroup
fiber census, preserving that source consumer without developing full
reduction additivity for arbitrary nonintegral points. This advances
DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 through their finite Galois
specialization, exceptional-fiber count, reverse genus and good reduction. -/
namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve IsLocalRing SourceEllipticVariableChange
noncomputable section

theorem exists_actual_inertia_torsion_reduction
    {F M : Type*} [Field F] [Field M] [Algebra F M] [DecidableEq M]
    {A : ValuationSubring M} [DecidableEq (ResidueField A)]
    (K : Type*) [Field K] [Algebra K A] (p : ℕ) [CharP K p] (hp : 5 ≤ p)
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
  obtain ⟨g, hg, -, hgres⟩ := exists_integral_inertia_cocycle_of_five_le
    K p hp E W κ hκ hW σ hσ
  refine ⟨g, hg, hgres hσI, ?_⟩
  intro P
  exact modelTorsionReduction_inertia E W κ hκ hΔ hN g σ hσ hσI hg (hgres hσI) P

end
end Dubon2026.SourceEllipticReduction
