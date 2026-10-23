import Dubon2026.SourceCurveFiniteRankTraceAdd

/-! DUB-17/18 -> global residue vanishing -> residue/trace compatibility.
Changing the local integral projector changes the projected multiplication
operator by a finite-rank operator. The following trace identity is the
precise algebraic comparison needed for that change of projector; it avoids
requiring either projected multiplication operator itself to have finite rank. -/

noncomputable section

namespace Dubon2026.SourceCurve.ResidueTrace

open LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A finite-rank change to one multiplication operator preserves its commutator trace. -/
theorem finrankTrace_commutator_congr (φ ψ γ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range (φ - ψ))]
    [FiniteDimensional K (LinearMap.range (φ ∘ₗ γ - γ ∘ₗ φ))]
    [FiniteDimensional K (LinearMap.range (ψ ∘ₗ γ - γ ∘ₗ ψ))] :
    finrankTrace (φ ∘ₗ γ - γ ∘ₗ φ) = finrankTrace (ψ ∘ₗ γ - γ ∘ₗ ψ) := by
  have he : (φ ∘ₗ γ - γ ∘ₗ φ) - (ψ ∘ₗ γ - γ ∘ₗ ψ) =
      (φ - ψ) ∘ₗ γ - γ ∘ₗ (φ - ψ) := by
    ext x
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
    abel
  have hz := finrankTrace_commutator_eq_zero_left (φ - ψ) γ
  rw [← he, finrankTrace_sub] at hz
  exact sub_eq_zero.mp hz

end Dubon2026.SourceCurve.ResidueTrace
