import Dubon2026.SourceGammaOneDiamondFieldHom

/-! DUB-17/18 -> original all-weight association -> arithmetic Gamma1
diamond/Picard comparison -> literal analytic place action. Identify the
actual field diamond on every original modular quotient, then reuse the
existing quotient realization to obtain its interior germ. This supplies
the analytic input for place transport and the Picard-period comparison.
-/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open CongruenceSubgroup Matrix.SpecialLinearGroup UpperHalfPlane Filter ModularRatios
open scoped MatrixGroups ModularForm Topology
variable (M : ℕ) [NeZero M] (g : Gamma0 M)

theorem diamondFieldHom_ratio {k : ℤ} (f h : ModularForm (Gamma1 M) k)
    (hh : h ≠ 0) (x : functionFieldOver (Gamma1 M) ℂ)
    (hx : (x : LaurentSeries ℂ) * qL h = qL f) :
    (diamondFieldHom M g x : LaurentSeries ℂ) * qL (modularDiamond M g h) =
      qL (modularDiamond M g f) := by
  have hT : ModularGroup.T ∈ Gamma1 M := by simp [Gamma1_mem, ModularGroup.T]
  have hΓ : Gamma M ≤ Gamma1 M := by
    intro A hA
    rw [Gamma_mem] at hA
    exact (Gamma1_mem M A).mpr ⟨hA.1, hA.2.2.2, hA.2.2.1⟩
  let F := modularDiamond M g f
  let H := modularDiamond M g h
  have hH : H ≠ 0 := modularDiamond_ne_zero M g h hh
  let y : functionFieldOver (Gamma1 M) ℂ :=
    ⟨qL F / qL H, modular_ratio_mem M F H hH⟩
  have hy : (y : LaurentSeries ℂ) * qL H = qL F :=
    div_mul_cancel₀ _ (qL_ne_zero hT H hH)
  have he : diamondFieldHom M g x = y := by
    apply (fieldCuspGerm M 1).injective
    rw [diamondFieldHom_cuspGerm]
    apply Germ.coe_eq.mpr
    filter_upwards [cuspRealize_eventuallyEq_of_ratio M hΓ hT F H y hH hy 1,
      cuspRealize_eventuallyEq_of_ratio M hΓ hT f h x hh hx (g.val * 1)] with q h1 h2
    rw [h1, h2]
    change cuspFunction M (ModularForm.translate f ((g.val * 1 : SL(2, ℤ)) : GL (Fin 2) ℝ)) q /
        cuspFunction M (ModularForm.translate h ((g.val * 1 : SL(2, ℤ)) : GL (Fin 2) ℝ)) q =
      cuspFunction M (ModularForm.translate F ((1 : SL(2, ℤ)) : GL (Fin 2) ℝ)) q /
        cuspFunction M (ModularForm.translate H ((1 : SL(2, ℤ)) : GL (Fin 2) ℝ)) q
    rw [show (ModularForm.translate F ((1 : SL(2, ℤ)) : GL (Fin 2) ℝ) : ℍ → ℂ) =
        (ModularForm.translate f ((g.val * 1 : SL(2, ℤ)) : GL (Fin 2) ℝ) : ℍ → ℂ)
        from modularDiamond_translate_coe M g f 1,
      show (ModularForm.translate H ((1 : SL(2, ℤ)) : GL (Fin 2) ℝ) : ℍ → ℂ) =
        (ModularForm.translate h ((g.val * 1 : SL(2, ℤ)) : GL (Fin 2) ℝ) : ℍ → ℂ)
        from modularDiamond_translate_coe M g h 1]
  rw [he]
  exact hy

theorem realize_diamondFieldHom_eventuallyEq (x : functionFieldOver (Gamma1 M) ℂ) (τ : ℍ) :
    (fun z : ℂ => realize (Gamma1 M) (diamondFieldHom M g x : LaurentSeries ℂ) (ofComplex z))
      =ᶠ[𝓝[≠] (τ : ℂ)]
        fun z : ℂ => realize (Gamma1 M) (x : LaurentSeries ℂ) (g.val • ofComplex z) := by
  have hT : ModularGroup.T ∈ Gamma1 M := by simp [Gamma1_mem, ModularGroup.T]
  obtain ⟨k, f, h, hh, hx⟩ := functionFieldOver_modular_ratio hT x
  have hH := modularDiamond_ne_zero M g h hh
  have hDx := diamondFieldHom_ratio M g f h hh x hx
  filter_upwards [realize_eventuallyEq_of_ratio hT (modularDiamond M g f)
    (modularDiamond M g h) (diamondFieldHom M g x) hH hDx τ,
    eventually_ne_zero_ofComplex (modularDiamond M g h) hH τ] with z he hz
  rw [he, realize_smul_eq_translated_ratio hT f h x hx g.val (ofComplex z) hz]
  rfl

end
end Dubon2026.SourceFunctionField.GammaOne
