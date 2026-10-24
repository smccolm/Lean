import Dubon2026.SourceEllipticFaithfulGoodModelField
import Dubon2026.SourceEllipticWildActualTorsionReduction

/-! DUB-17/18 -> characteristic-three modular good reduction -> faithful
prescribed elliptic specialization. Reuse the existing actual field, torsion,
place and point maps, with the newly proved integral inertia cocycle valid
in every residue characteristic. The Legendre field requires only two nonzero.
Wild census and the remaining characteristic-two model branch remain open. -/
namespace Dubon2026.SourceEllipticDivisionField
open WeierstrassCurve IsLocalRing SourceEllipticReduction SourceEllipticVariableChange
noncomputable section

theorem exists_faithful_torsion_model_of_two_ne_zero
    (K : Type*) [Field K] {F Ω : Type*} [Field F] [Field Ω] [Algebra K F]
    [Algebra F Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic F Ω] [DecidableEq Ω]
    (h2K : (2 : K) ≠ 0)
    (E : WeierstrassCurve F) [E.IsElliptic] (N : ℕ) (hNK : (N : K) ≠ 0) :
    ∃ M : IntermediateField F Ω, FiniteDimensional F M ∧ IsGalois F M ∧
      Nat.card {P : (E.baseChange M).toAffine.Point // N • P = 0} = N ^ 2 ∧
      ∀ (A : ValuationSubring M) [Algebra K A] [DecidableEq (ResidueField A)],
        algebraMap F M E.j ∈ A →
      ∃ (W : WeierstrassCurve A) (κ : VariableChange M)
        (hκ : κ • E.baseChange M = W.map A.subtype) (hW : IsUnit W.Δ)
        (θ : Submodule.torsionBy ℤ (E.baseChange M).toAffine.Point (N : ℤ) →+
          (W.map (residue A)).toAffine.Point),
        Function.Injective θ ∧
        (∀ P, θ P = reducePoint ((map_residue_Δ_ne_zero_iff W).mpr hW)
          (modelPointEquiv E W κ hκ P)) ∧
        ∀ (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F),
          (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F →
          ∃ g : VariableChange A,
            g.map A.subtype = κ * (κ.map (σ : M →+* M))⁻¹ ∧
            g.map (residue A) • W.map (residue A) = W.map (residue A) ∧
            (∀ P, HEq (vcInvFun (g.map (residue A)) (W.map (residue A)).toAffine (θ P))
              (θ (galoisTorsionMap E N σ P))) ∧
            (g.map (residue A) = 1 → σ = 1) := by
  have h2F : (2 : F) ≠ 0 := natCast_ne_zero_of_ne_zero h2K
  have hNF : (N : F) ≠ 0 := natCast_ne_zero_of_ne_zero hNK
  obtain ⟨M, hfd, hgal, hcard, hM⟩ := exists_faithful_good_model_field (Ω := Ω) E h2F hNF
  refine ⟨M, hfd, hgal, hcard, ?_⟩
  intro A _ _ hj
  have h2A : IsUnit (2 : A) := by
    simpa only [map_ofNat] using h2K.isUnit.map (algebraMap K A)
  have hNA : IsUnit (N : A) := by
    simpa only [map_natCast] using hNK.isUnit.map (algebraMap K A)
  obtain ⟨W, κ, hκ, hW, hfaith⟩ := hM A h2A hNA hj
  obtain ⟨θ, hinj, hθ, heq⟩ := exists_actual_inertia_torsion_reduction_all_characteristics K E W κ hκ hW N hNK
  refine ⟨W, κ, hκ, hW, θ, hinj, hθ, ?_⟩
  intro σ hσ hI
  obtain ⟨g, hg, hfix, hequiv⟩ := heq σ hσ hI
  exact ⟨g, hg, hfix, hequiv, fun hg1 => hfaith σ hσ hI ⟨g, hg, hg1⟩⟩

end
end Dubon2026.SourceEllipticDivisionField
