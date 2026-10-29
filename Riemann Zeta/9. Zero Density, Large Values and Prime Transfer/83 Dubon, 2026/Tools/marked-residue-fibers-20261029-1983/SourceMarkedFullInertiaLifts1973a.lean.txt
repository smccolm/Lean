import Dubon2026.SourceEllipticGaloisTorsionMap
import Dubon2026.SourceEllipticStabilizerPointAction
import Mathlib.RingTheory.Valuation.RamificationGroup

/-! DUB-17/18 -> reverse genus -> wild residue marked charts.
Use the actual full inertia image to produce the signed point lifts
required by the reduced-chart consumer. Keeping this exact conversion
separate avoids re-elaborating the exceptional specialization witnesses. -/
namespace Dubon2026.SourceFunctionField.MarkedChart
noncomputable section
open WeierstrassCurve SourceEllipticReduction SourceEllipticVariableChange

theorem full_inertia_image_signed_point_lifts
    {F K M : Type*} [Field F] [Field K] [Field M] [Algebra F M]
    [DecidableEq K] [DecidableEq M]
    (E : WeierstrassCurve F) (E₀ : WeierstrassCurve K) (N : ℕ) (w : ValuationSubring M)
    (θ : Submodule.torsionBy ℤ (E.baseChange M).toAffine.Point (N : ℤ) →+ E₀.toAffine.Point)
    (ρ : w.inertiaSubgroup F →* VariableChange K)
    (heq : ∀ σ T, HEq (vcInvFun (ρ σ) E₀.toAffine (θ T)) (θ (galoisTorsionMap E N σ.val.val T)))
    (hfull : ∀ δ : VariableChange K, δ • E₀ = E₀ → ∃ σ : w.inertiaSubgroup F, ρ σ = δ) :
    ∀ δ : VariableChange K, δ • E₀ = E₀ →
      ∃ σ : w.inertiaSubgroup F,
        (∀ T, HEq (vcInvFun δ E₀.toAffine (θ T)) (θ (galoisTorsionMap E N σ.val.val T))) ∨
        (∀ T, HEq (vcInvFun δ E₀.toAffine (θ T)) (-(θ (galoisTorsionMap E N σ.val.val T)))) := by
  intro δ hδ
  obtain ⟨σ, hσ⟩ := hfull δ hδ
  refine ⟨σ, Or.inl ?_⟩
  intro T
  rw [← hσ]
  exact heq σ T

end
end Dubon2026.SourceFunctionField.MarkedChart
