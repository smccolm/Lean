import Dubon2026.SourceGammaOneCuspRatioRealization
import Dubon2026.SourceGammaOneRealizationAlgebra

/-! DUB-17/18 -> actual Gamma1 regular-differential/cusp converse ->
normalized cusp places. Prove the field laws for the actual translated
cusp germs using the original modular quotient identities. The native
slash product and sum laws avoid a separate Laurent-field homomorphism. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane Filter ModularRatios
open scoped MatrixGroups ModularForm Topology
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}

private theorem cusp_translate_mul (N : ℕ) {a b : ℤ}
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) a)
    (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) b) (γ : SL(2, ℤ)) {q : ℂ} (hq : q ≠ 0) :
    cuspFunction N (ModularForm.translate (f.mul g) (γ : GL (Fin 2) ℝ)) q =
      cuspFunction N (ModularForm.translate f (γ : GL (Fin 2) ℝ)) q *
        cuspFunction N (ModularForm.translate g (γ : GL (Fin 2) ℝ)) q := by
  simp only [cuspFunction, Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq,
    Function.comp_apply]
  exact congrFun (ModularForm.mul_slash_SL2 a b γ f g) _

private theorem cusp_translate_add (N : ℕ) {a : ℤ}
    (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) a) (γ : SL(2, ℤ)) {q : ℂ} (hq : q ≠ 0) :
    cuspFunction N (ModularForm.translate (f + g) (γ : GL (Fin 2) ℝ)) q =
      cuspFunction N (ModularForm.translate f (γ : GL (Fin 2) ℝ)) q +
        cuspFunction N (ModularForm.translate g (γ : GL (Fin 2) ℝ)) q := by
  simp only [cuspFunction, Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq,
    Function.comp_apply]
  exact congrFun (SlashAction.add_slash a (γ : GL (Fin 2) ℝ) (f : ℍ → ℂ) (g : ℍ → ℂ)) _

theorem cuspRealize_const_eventuallyEq (N : ℕ) (hT : ModularGroup.T ∈ Γ)
    (γ : SL(2, ℤ)) (c : ℂ) :
    cuspRealize Γ N γ (algebraMap ℂ (LaurentSeries ℂ) c) =ᶠ[𝓝[≠] (0 : ℂ)] fun _ => c := by
  filter_upwards [self_mem_nhdsWithin] with q hq
  simp only [cuspRealize, cuspFunction,
    Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq,
    Function.comp_apply, realize_algebraMap hT]

theorem cuspRealize_mul_eventuallyEq (N : ℕ) [NeZero N]
    (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) (hT : ModularGroup.T ∈ Γ)
    (x y : functionFieldOver Γ ℂ) (γ : SL(2, ℤ)) :
    cuspRealize Γ N γ ((x * y : functionFieldOver Γ ℂ) : LaurentSeries ℂ) =ᶠ[𝓝[≠] (0 : ℂ)]
      cuspRealize Γ N γ (x : LaurentSeries ℂ) * cuspRealize Γ N γ (y : LaurentSeries ℂ) := by
  obtain ⟨a, g, h, hh, hx⟩ := functionFieldOver_modular_ratio hT x
  obtain ⟨b, g', h', hh', hy⟩ := functionFieldOver_modular_ratio hT y
  change (x : LaurentSeries ℂ) * qL h = qL g at hx
  change (y : LaurentSeries ℂ) * qL h' = qL g' at hy
  have he : ((x * y : functionFieldOver Γ ℂ) : LaurentSeries ℂ) * qL (h.mul h') = qL (g.mul g') := by
    change (x : LaurentSeries ℂ) * (y : LaurentSeries ℂ) * qL (h.mul h') = _
    rw [qL_mul hT, qL_mul hT, ← hx, ← hy]
    ring
  filter_upwards [cuspRealize_eventuallyEq_of_ratio N hΓ hT (g.mul g') (h.mul h') _
    (mul_ne_zero' hT h h' hh hh') he γ,
    cuspRealize_eventuallyEq_of_ratio N hΓ hT g h x hh hx γ,
    cuspRealize_eventuallyEq_of_ratio N hΓ hT g' h' y hh' hy γ,
    self_mem_nhdsWithin] with q hxy hxe hye hq
  rw [Pi.mul_apply, hxy, hxe, hye]
  simp only [Pi.div_apply, cusp_translate_mul N _ _ γ hq]
  exact mul_div_mul_comm _ _ _ _

theorem cuspRealize_add_eventuallyEq (N : ℕ) [NeZero N]
    (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) (hT : ModularGroup.T ∈ Γ)
    (x y : functionFieldOver Γ ℂ) (γ : SL(2, ℤ)) :
    cuspRealize Γ N γ ((x + y : functionFieldOver Γ ℂ) : LaurentSeries ℂ) =ᶠ[𝓝[≠] (0 : ℂ)]
      cuspRealize Γ N γ (x : LaurentSeries ℂ) + cuspRealize Γ N γ (y : LaurentSeries ℂ) := by
  obtain ⟨a, g, h, hh, hx⟩ := functionFieldOver_modular_ratio hT x
  obtain ⟨b, g', h', hh', hy⟩ := functionFieldOver_modular_ratio hT y
  change (x : LaurentSeries ℂ) * qL h = qL g at hx
  change (y : LaurentSeries ℂ) * qL h' = qL g' at hy
  have he : ((x + y : functionFieldOver Γ ℂ) : LaurentSeries ℂ) * qL (h.mul h') =
      qL (g.mul h' + h.mul g') := by
    change ((x : LaurentSeries ℂ) + (y : LaurentSeries ℂ)) * qL (h.mul h') = _
    rw [qL_add hT, qL_mul hT, qL_mul hT, qL_mul hT, ← hx, ← hy]
    ring
  filter_upwards [cuspRealize_eventuallyEq_of_ratio N hΓ hT (g.mul h' + h.mul g') (h.mul h') _
    (mul_ne_zero' hT h h' hh hh') he γ,
    cuspRealize_eventuallyEq_of_ratio N hΓ hT g h x hh hx γ,
    cuspRealize_eventuallyEq_of_ratio N hΓ hT g' h' y hh' hy γ,
    eventually_ne_zero_translated_cuspFunction N hΓ h hh γ,
    eventually_ne_zero_translated_cuspFunction N hΓ h' hh' γ,
    self_mem_nhdsWithin] with q hxy hxe hye hz hz' hq
  rw [Pi.add_apply, hxy, hxe, hye]
  simp only [Pi.div_apply, cusp_translate_add N _ _ γ hq, cusp_translate_mul N _ _ γ hq]
  rw [div_add_div _ _ hz hz']

end
end Dubon2026.SourceFunctionField.GammaOne
