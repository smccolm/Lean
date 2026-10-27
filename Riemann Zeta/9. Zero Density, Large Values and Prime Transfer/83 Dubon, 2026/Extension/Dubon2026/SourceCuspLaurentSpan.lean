import Dubon2026.SourceCuspLaurentFunctionIdentity
import Dubon2026.SourceLaurentEuler

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational Fourier spanning.
Transfer the Laurent span to actual holomorphic periodic functions. Scalar
multiplication is explicitly the native coefficientwise complex action on
Laurent series, matching the integral constant-descent theorem. -/
namespace Dubon2026.SourceFunctionField.CuspTaylor
noncomputable section
open UpperHalfPlane
open scoped Manifold

theorem Represents.cusp_smul {h : ℝ} {A : LaurentSeries ℂ} {f : ℍ → ℂ}
    (hf : Represents A (cuspFunction h f)) (c : ℂ) :
    Represents (c • A) (cuspFunction h (c • f)) := by
  have hr := (represents_cusp_const h c).cusp_mul hf
  rw [SourceDifferential.algebraMap_laurentSeries_apply_alt,
    HahnSeries.single_zero_mul_eq_smul] at hr
  exact hr

theorem Represents.mem_span_of_laurent_span {h : ℝ} {A : LaurentSeries ℂ} {F : ℍ → ℂ}
    {S : Set (LaurentSeries ℂ)} {T : Set (ℍ → ℂ)}
    (hFA : Represents A (cuspFunction h F)) (hh : 0 < h)
    (hF : MDiff F) (hFper : Function.Periodic (F ∘ ofComplex) h)
    (hT : ∀ f ∈ T, MDiff f ∧ Function.Periodic (f ∘ ofComplex) h)
    (hST : ∀ X ∈ S, ∃ f ∈ T, Represents X (cuspFunction h f))
    (hA : A ∈ Submodule.span ℂ S) : F ∈ Submodule.span ℂ T := by
  have hreal : ∃ g ∈ Submodule.span ℂ T, MDiff g ∧
      Function.Periodic (g ∘ ofComplex) h ∧ Represents A (cuspFunction h g) := by
    clear hFA
    induction hA using Submodule.span_induction with
    | mem X hX =>
      obtain ⟨f, hf, hrep⟩ := hST X hX
      exact ⟨f, Submodule.subset_span hf, (hT f hf).1, (hT f hf).2, hrep⟩
    | zero =>
      refine ⟨0, zero_mem _, mdifferentiable_const, (by intro z; rfl), ?_⟩
      simpa only [map_zero] using represents_cusp_const h 0
    | add X Y _ _ hX hY =>
      obtain ⟨f, hf, hfh, hfp, hfr⟩ := hX
      obtain ⟨g, hg, hgh, hgp, hgr⟩ := hY
      exact ⟨f + g, add_mem hf hg, hfh.add hgh, hfp.add hgp, hfr.cusp_add hgr⟩
    | smul c X _ hX =>
      obtain ⟨f, hf, hfh, hfp, hfr⟩ := hX
      refine ⟨c • f, Submodule.smul_mem _ c hf, mdifferentiable_const.mul hfh, ?_,
        hfr.cusp_smul c⟩
      intro z
      change c * f (ofComplex (z + h)) = c * f (ofComplex z)
      exact congrArg (fun w : ℂ => c * w) (hfp z)
  obtain ⟨g, hg, hgh, hgp, hgr⟩ := hreal
  exact (hFA.eq_upperHalfPlane hgr hh hF hgh hFper hgp).symm ▸ hg

end
end Dubon2026.SourceFunctionField.CuspTaylor