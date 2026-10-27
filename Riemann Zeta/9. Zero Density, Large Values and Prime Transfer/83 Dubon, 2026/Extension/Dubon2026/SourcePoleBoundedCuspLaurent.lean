import Dubon2026.SourceFrickePoleBoundedV3
import Dubon2026.SourceCuspLaurentFunctionIdentity

/-! DUB-17/18 -> actual Gamma1 differential/cusp comparison -> rational
Fourier structure. Actual periodic holomorphic functions with finite cusp
poles have meromorphic Laurent representations: divide the ordinary Fourier
series of a discriminant-cleared function by that of the discriminant.
This discharges existence rather than postulating a Fourier realization. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane ModularForm SlashInvariantFormClass ModularFormClass SourceFunctionField
open scoped Manifold ModularForm MatrixGroups

theorem periodic_discriminant_width (N : ℕ) :
    Function.Periodic ((⇑CuspForm.discriminant : ℍ → ℂ) ∘ ofComplex) N := by
  simpa using (periodic_comp_ofComplex CuspForm.discriminant one_mem_strictPeriods_SL).nat_mul N

theorem represents_discriminant_width (N : ℕ) [NeZero N] :
    CuspTaylor.Represents (qExpansion N (⇑CuspForm.discriminant : ℍ → ℂ) : LaurentSeries ℂ)
      (cuspFunction N (⇑CuspForm.discriminant : ℍ → ℂ)) :=
  CuspTaylor.represents_qExpansion (by exact_mod_cast NeZero.pos N)
    (periodic_discriminant_width N) CuspForm.discriminant.holo'
    (ModularFormClass.bdd_at_infty CuspForm.discriminant)

theorem exists_cusp_represents_of_poleBounded {N : ℕ} [NeZero N] {f : ℍ → ℂ}
    (hf : PoleBounded f) (hper : Function.Periodic (f ∘ ofComplex) N) :
    ∃ A : LaurentSeries ℂ, CuspTaylor.Represents A (cuspFunction N f) := by
  obtain ⟨hhol, m, hbd⟩ := hf
  have hdper := periodic_discriminant_width N
  have hper' : Function.Periodic
      ((f * ⇑CuspForm.discriminant ^ m : ℍ → ℂ) ∘ ofComplex) N := by
    intro z
    simp only [Function.comp_apply, Pi.mul_apply, Pi.pow_apply]
    have hp := hper z
    have hd := hdper z
    simp only [Function.comp_apply] at hp hd
    rw [hp, hd]
  have hrep := CuspTaylor.represents_qExpansion (by exact_mod_cast NeZero.pos N) hper'
    (hhol.mul (CuspForm.discriminant.holo'.pow m)) hbd
  have hquot := hrep.cusp_div ((represents_discriminant_width N).cusp_pow m)
  have he : ((f * ⇑CuspForm.discriminant ^ m) / ⇑CuspForm.discriminant ^ m : ℍ → ℂ) = f := by
    funext τ
    exact mul_div_cancel_right₀ _ (pow_ne_zero m (by
      simpa only [CuspForm.coe_discriminant] using discriminant_ne_zero τ))
  exact ⟨_, he ▸ hquot⟩

end
end Dubon2026.SourceFricke