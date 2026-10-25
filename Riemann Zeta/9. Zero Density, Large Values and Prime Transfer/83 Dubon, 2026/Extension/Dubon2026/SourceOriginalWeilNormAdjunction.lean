import Dubon2026.SourceOriginalWeilPairingDescent
import Dubon2026.SourceOriginalPullbackEvaluation
import Dubon2026.SourceOriginalPushforwardEvaluation
import Dubon2026.SourceCurveCorrespondenceRamification

/-! DUB-17/18 -> Hecke-adjoint original Tate pairing. For compatible
actual divisor/function representatives, finite pullback is adjoint to
the actual norm pushforward. Every evaluation and fiber-regularity input
is discharged by the proved norm formula and disjointness. Construction
of compatible representatives for arbitrary classes is the next step. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
attribute [local instance] originalNormCharZero
variable (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
variable (N M : ℕ) [NeZero N] [NeZero M] {n : ℕ}

theorem originalWeilDatum_norm_adjunction
    (φ : modularFunctionFieldOver N L →ₐ[L] modularFunctionFieldOver M L)
    (d : OriginalWeilDatum N L n) (e : OriginalWeilDatum M L n)
    (hD : e.D₁ = Divisor.finitePullbackAlong φ (original_field_hom_finite L N M φ) d.D₁)
    (hE : d.D₂ = Divisor.geometricPushforwardAlong φ (original_field_hom_finite L N M φ) e.D₂)
    (hf : e.f₁ = φ d.f₁)
    (hg : letI := algebraAlong φ; d.f₂ = Algebra.norm (modularFunctionFieldOver N L) e.f₂) :
    d.pairing = e.pairing := by
  letI := algebraAlong φ
  have hnum : originalDivisorEval N L d.f₁ d.D₂ = originalDivisorEval M L e.f₁ e.D₂ := by
    rw [hE, originalDivisorEval_geometricPushforwardAlong L N M φ e.D₂ d.f₁ d.f₁_ne_zero]
    · rw [hf]
    · intro w hw
      rw [← hf, e.ord_f₁, (e.disjoint w).resolve_right (Finsupp.mem_support_iff.mp hw), mul_zero]
  have hden : originalDivisorEval M L e.f₂ e.D₁ = originalDivisorEval N L d.f₂ d.D₁ := by
    rw [hD, hg]
    apply originalDivisorEval_finitePullbackAlong L N M φ d.D₁ e.f₂
    intro v hv w hw
    have hp : e.D₁ w ≠ 0 := by
      rw [hD, Divisor.finitePullbackAlong_apply, hw]
      exact mul_ne_zero (Finsupp.mem_support_iff.mp hv)
        (ne_of_gt (Place.ramificationAlong_pos φ _ w))
    rw [e.ord_f₂, (e.disjoint w).resolve_left hp, mul_zero]
  change originalDivisorEval N L d.f₁ d.D₂ / originalDivisorEval N L d.f₂ d.D₁ = _
  rw [hnum, ← hden]
  rfl

end
end Dubon2026.SourceFunctionField
