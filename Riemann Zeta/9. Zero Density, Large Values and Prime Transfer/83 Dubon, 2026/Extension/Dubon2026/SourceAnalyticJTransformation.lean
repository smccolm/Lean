import Dubon2026.SourceAnalyticJOrbitSeparation
import Dubon2026.SourceAnalyticJInvariant
import Mathlib.NumberTheory.ModularForms.Derivative
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Meromorphic.Order

/-! DUB-17/18 -> numerical modular genus -> elliptic ramification ->
the exact analytic multiplicity of j at each upper-half-plane point.
The required derivative identity follows from native level-one dimension
and discriminant division. This avoids adding a general Ramanujan system
or elliptic-curve uniformization. Full modular orbit separation identifies
the two exceptional fibers with the actual elliptic-point stabilizers.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two.
-/
namespace Dubon2026.SourceFunctionField.JMultiplicity
noncomputable section
open UpperHalfPlane ModularForm Complex SlashInvariantForm Derivative Filter ModularGroup
open scoped MatrixGroups Real Topology ModularForm Manifold Derivative Modular
local notation "Δ" => ModularForm.discriminant
/-- The analytic j-invariant, with its classical zero and 1728 normalization. -/
def jf : ℍ → ℂ := fun τ => (E₄ : ℍ → ℂ) τ ^ 3 / ModularForm.discriminant τ

theorem E₄_smul (γ : SL(2, ℤ)) (τ : ℍ) : E₄ (γ • τ) = denom γ τ ^ (4 : ℤ) * E₄ τ := by
  have h := slash_action_eqn'' (Γ := 𝒮ℒ) (k := (4 : ℤ)) E₄ (γ := (γ : GL (Fin 2) ℝ)) ⟨γ, rfl⟩ τ
  simpa [ModularGroup.sl_moeb] using h

theorem Δ_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    ModularForm.discriminant (γ • τ) = denom γ τ ^ (12 : ℤ) * ModularForm.discriminant τ := by
  have h := slash_action_eqn'' (Γ := 𝒮ℒ) (k := (12 : ℤ)) CuspForm.discriminant
    (γ := (γ : GL (Fin 2) ℝ)) ⟨γ, rfl⟩ τ
  simpa [ModularGroup.sl_moeb, CuspForm.coe_discriminant] using h

theorem jf_smul (γ : SL(2, ℤ)) (τ : ℍ) : jf (γ • τ) = jf τ :=
  E4_cube_div_discriminant_smul γ τ

theorem mdifferentiable_jf : MDiff jf :=
  (E₄.holo'.pow 3).div CuspForm.discriminant.holo' discriminant_ne_zero

theorem D_smul {F : ℍ → ℂ} (hF : MDiff F) (hinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), F (γ • τ) = F τ)
    (γ : SL(2, ℤ)) (τ : ℍ) : D F (γ • τ) = denom γ τ ^ 2 * D F τ := by
  have hdet1 : ((γ : GL (Fin 2) ℝ)).val.det = 1 := Matrix.SpecialLinearGroup.det_coe _
  have hdet : 0 < ((γ : GL (Fin 2) ℝ)).val.det := by rw [hdet1]; exact one_pos

  have h1 : HasDerivAt (fun z : ℂ => (↑((γ : GL (Fin 2) ℝ) • ofComplex z) : ℂ))
      (((γ : GL (Fin 2) ℝ)).val.det / denom (γ : GL (Fin 2) ℝ) τ ^ 2) (τ : ℂ) :=
    (UpperHalfPlane.hasStrictDerivAt_smul hdet τ).hasDerivAt
  have hdiff : DifferentiableAt ℂ (F ∘ ofComplex) (↑(γ • τ) : ℂ) := by
    have := (hF (γ • τ))
    rwa [UpperHalfPlane.mdifferentiableAt_iff] at this
  have h2 : HasDerivAt (F ∘ ofComplex) (deriv (F ∘ ofComplex) (↑(γ • τ) : ℂ)) (↑(γ • τ) : ℂ) :=
    hdiff.hasDerivAt
  have h3 := h2.scomp_of_eq (τ : ℂ) h1 (by simp [ModularGroup.sl_moeb])

  have h4 : (F ∘ ofComplex) ∘ (fun z : ℂ => (↑((γ : GL (Fin 2) ℝ) • ofComplex z) : ℂ))
      =ᶠ[𝓝 (τ : ℂ)] F ∘ ofComplex := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz, UpperHalfPlane.ofComplex_apply]
    rw [← ModularGroup.sl_moeb, hinv]
  have h5 : deriv (F ∘ ofComplex) τ =
      ((((γ : GL (Fin 2) ℝ)).val.det : ℂ) / denom (γ : GL (Fin 2) ℝ) τ ^ 2) •
        deriv (F ∘ ofComplex) (↑(γ • τ) : ℂ) := (h3.congr_of_eventuallyEq h4.symm).deriv
  have hd : denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  simp only [normalizedDerivOfComplex]
  rw [ModularGroup.sl_moeb, h5, hdet1]
  simp only [smul_eq_mul, Complex.ofReal_one]
  field_simp
  rfl

theorem mdiff_E₄ : MDiff (E₄ : ℍ → ℂ) := E₄.holo'
theorem mdiff_E₆ : MDiff (E₆ : ℍ → ℂ) := E₆.holo'
theorem mdiff_Δ : MDiff (ModularForm.discriminant : ℍ → ℂ) := CuspForm.discriminant.holo'

theorem E₆_smul (γ : SL(2, ℤ)) (τ : ℍ) : E₆ (γ • τ) = denom γ τ ^ (6 : ℤ) * E₆ τ := by
  have h := slash_action_eqn'' (Γ := 𝒮ℒ) (k := (6 : ℤ)) E₆ (γ := (γ : GL (Fin 2) ℝ)) ⟨γ, rfl⟩ τ
  simpa [ModularGroup.sl_moeb] using h


end
end Dubon2026.SourceFunctionField.JMultiplicity
