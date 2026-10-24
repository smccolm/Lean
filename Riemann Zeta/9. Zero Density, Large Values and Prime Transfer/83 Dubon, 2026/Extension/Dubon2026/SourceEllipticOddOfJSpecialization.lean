import Dubon2026.SourceEllipticOddSpecializationFieldPlace
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ

/-! DUB-17/18 -> characteristic-three modular good reduction -> faithful
prescribed elliptic specialization. Reuse the existing actual field, torsion,
place and point maps, with the newly proved integral inertia cocycle valid
in every residue characteristic. The Legendre field requires only two nonzero.
Wild census and the remaining characteristic-two model branch remain open. -/
namespace Dubon2026.SourceEllipticDivisionField
open WeierstrassCurve IsLocalRing SourceEllipticReduction SourceEllipticVariableChange
open SourceCurve
noncomputable section

theorem exists_faithful_ofJ_specialization_of_two_ne_zero
    (K Ω : Type*) [Field K] [IsAlgClosed K] [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    [Algebra (RatFunc K) Ω] [Algebra K Ω] [IsScalarTower K (RatFunc K) Ω]
    [Algebra.IsAlgebraic (RatFunc K) Ω]
    (h2K : (2 : K) ≠ 0)
    [DecidableEq (RatFunc K)]
    (N : ℕ) (hNK : (N : K) ≠ 0) (E₀ : WeierstrassCurve K) [E₀.IsElliptic] :
    let E : WeierstrassCurve (RatFunc K) := ofJ (RatFunc.X : RatFunc K)
    ∃ M : IntermediateField (RatFunc K) Ω,
      FiniteDimensional (RatFunc K) M ∧ IsGalois (RatFunc K) M ∧
      Nat.card {P : (E.baseChange M).toAffine.Point // N • P = 0} = N ^ 2 ∧
      ∃ (v : Place K M) (_ : DecidableEq v.ResidueField) (e : v.ResidueField ≃ₐ[K] K)
        (W : WeierstrassCurve v.toValuationSubring) (κ : VariableChange M)
        (hκ : κ • E.baseChange M = W.map v.toValuationSubring.subtype) (hW : IsUnit W.Δ)
        (γ : VariableChange K)
        (θ : Submodule.torsionBy ℤ (E.baseChange M).toAffine.Point (N : ℤ) →+
          (W.map (residue v.toValuationSubring)).toAffine.Point),
        0 < v.ord (algebraMap (RatFunc K) M RatFunc.X - algebraMap K M E₀.j) ∧
        γ • W.map (e.toRingHom.comp (residue v.toValuationSubring)) = E₀ ∧
        Function.Injective θ ∧
        (∀ P, θ P = reducePoint ((map_residue_Δ_ne_zero_iff W).mpr hW)
          (modelPointEquiv E W κ hκ P)) ∧
        ∀ (σ : M ≃ₐ[RatFunc K] M)
          (_hσ : σ ∈ v.toValuationSubring.decompositionSubgroup (RatFunc K)),
          ∃ g : VariableChange v.toValuationSubring,
            g.map v.toValuationSubring.subtype = κ * (κ.map (σ : M →+* M))⁻¹ ∧
            g.map (residue v.toValuationSubring) • W.map (residue v.toValuationSubring) =
              W.map (residue v.toValuationSubring) ∧
            (∀ P, HEq (vcInvFun (g.map (residue v.toValuationSubring))
                (W.map (residue v.toValuationSubring)).toAffine (θ P))
              (θ (galoisTorsionMap E N σ P))) ∧
            (g.map (residue v.toValuationSubring) = 1 → σ = 1) := by
  exact exists_faithful_specialization_field_place_of_two_ne_zero K Ω h2K
    (ofJ (RatFunc.X : RatFunc K)) (ofJ_j _) N hNK E₀

end
end Dubon2026.SourceEllipticDivisionField
