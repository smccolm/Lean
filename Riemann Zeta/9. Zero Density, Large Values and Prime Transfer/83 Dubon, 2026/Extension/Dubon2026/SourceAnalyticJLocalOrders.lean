import Dubon2026.SourceAnalyticJDerivativeIdentity

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
theorem deriv_jf_eventuallyEq {c : ℂ} (hc : ∀ z : ℍ, D jf z * Δ z = c * (E₄ z ^ 2 * E₆ z))
    (τ : ℍ) :
    deriv (jf ∘ ofComplex) =ᶠ[𝓝 (τ : ℂ)]
      (fun _ => 2 * π * Complex.I * c) * ((E₄ : ℍ → ℂ) ∘ ofComplex) ^ 2 *
        ((E₆ : ℍ → ℂ) ∘ ofComplex) * fun w => ((Δ ∘ ofComplex) w)⁻¹ := by
  filter_upwards [isOpen_uhp.mem_nhds τ.im_pos] with w hw
  rw [deriv_jf_eq w hw]
  have hΔ := discriminant_ne_zero (ofComplex w)
  have h := hc (ofComplex w)
  simp only [Pi.mul_apply, Pi.pow_apply, Function.comp_apply]
  rw [eq_div_iff hΔ |>.mpr h |> fun e => (e : D jf (ofComplex w) = _)]
  field_simp

theorem analyticOrderAt_deriv_jf {c : ℂ} (hc0 : c ≠ 0)
    (hc : ∀ z : ℍ, D jf z * Δ z = c * (E₄ z ^ 2 * E₆ z)) (τ : ℍ) :
    analyticOrderAt (deriv (jf ∘ ofComplex)) (τ : ℂ) =
      2 • analyticOrderAt ((E₄ : ℍ → ℂ) ∘ ofComplex) (τ : ℂ) +
        analyticOrderAt ((E₆ : ℍ → ℂ) ∘ ofComplex) (τ : ℂ) := by
  rw [analyticOrderAt_congr (deriv_jf_eventuallyEq hc τ)]
  have hK : AnalyticAt ℂ (fun _ : ℂ => 2 * π * Complex.I * c) (τ : ℂ) := analyticAt_const
  have h4 : AnalyticAt ℂ ((E₄ : ℍ → ℂ) ∘ ofComplex) (τ : ℂ) := analyticAt_comp E₄.holo' τ
  have h6 : AnalyticAt ℂ ((E₆ : ℍ → ℂ) ∘ ofComplex) (τ : ℂ) := analyticAt_comp E₆.holo' τ
  have hΔa : AnalyticAt ℂ (Δ ∘ ofComplex) (τ : ℂ) := analyticAt_comp CuspForm.discriminant.holo' τ
  have hΔi : AnalyticAt ℂ (fun w => ((Δ ∘ ofComplex) w)⁻¹) (τ : ℂ) :=
    hΔa.inv (by simpa using discriminant_ne_zero τ)
  rw [analyticOrderAt_mul ((hK.mul (h4.pow 2)).mul h6) hΔi,
    analyticOrderAt_mul (hK.mul (h4.pow 2)) h6, analyticOrderAt_mul hK (h4.pow 2),
    analyticOrderAt_pow h4,
    hK.analyticOrderAt_eq_zero.mpr (by simp [Real.pi_ne_zero, Complex.I_ne_zero, hc0]),
    hΔi.analyticOrderAt_eq_zero.mpr (by simpa using discriminant_ne_zero τ)]
  simp

theorem E₆_ne_zero_of_E₄_eq_zero {τ : ℍ} (h4 : E₄ τ = 0) : E₆ τ ≠ 0 := by
  intro h6
  have hΔ := discriminant_ne_zero τ
  rw [discriminant_eq_E₄_cube_sub_E₆_sq, h4, h6] at hΔ
  norm_num at hΔ

theorem jf_eq_of_E₆_eq_zero {τ : ℍ} (h6 : E₆ τ = 0) : jf τ = 1728 := by
  have hΔ := discriminant_ne_zero τ
  have hΔ' := discriminant_eq_E₄_cube_sub_E₆_sq τ
  rw [h6] at hΔ'
  have h4 : E₄ τ ^ 3 ≠ 0 := by
    intro h
    rw [h] at hΔ'
    norm_num at hΔ'
    exact hΔ hΔ'
  simp only [jf]
  rw [div_eq_iff hΔ, hΔ']
  ring

theorem order_deriv_add_one (τ : ℍ) :
    analyticOrderAt (deriv (jf ∘ ofComplex)) (τ : ℂ) + 1 =
      analyticOrderAt (fun z : ℂ => jf (ofComplex z) - jf τ) (τ : ℂ) := by
  have h := (analyticAt_comp mdifferentiable_jf τ).analyticOrderAt_deriv_add_one
  rw [comp_apply_coe] at h
  exact h

theorem case_E₄_eq_zero {τ : ℍ} (h4 : E₄ τ = 0) :
    analyticOrderAt (fun z : ℂ => jf (ofComplex z) - jf τ) (τ : ℂ) = (3 : ℕ) ∧
      Nat.card (MulAction.stabilizer SL(2, ℤ) τ) = 6 := by
  obtain ⟨c, hc0, hc⟩ := exists_D_jf_mul_Δ_eq
  have h6 : E₆ τ ≠ 0 := E₆_ne_zero_of_E₄_eq_zero h4
  have hjτ : jf τ = 0 := by simp [jf, h4]

  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (analyticOrderAt_ne_top mdiff_E₄ E₄_I_ne_zero τ)
  have hderiv := analyticOrderAt_deriv_jf hc0 hc τ
  rw [analyticOrderAt_eq_zero_of_ne_zero mdiff_E₆ h6, add_zero, ← hk] at hderiv

  have hF : (fun z : ℂ => jf (ofComplex z) - jf τ) =
      ((E₄ : ℍ → ℂ) ∘ ofComplex) ^ 3 * fun w => ((Δ ∘ ofComplex) w)⁻¹ := by
    funext z
    rw [hjτ, sub_zero]
    simp only [jf, Pi.mul_apply, Pi.pow_apply, Function.comp_apply, div_eq_mul_inv]
  have hE4a : AnalyticAt ℂ ((E₄ : ℍ → ℂ) ∘ ofComplex) (τ : ℂ) := analyticAt_comp mdiff_E₄ τ
  have hΔi : AnalyticAt ℂ (fun w => ((Δ ∘ ofComplex) w)⁻¹) (τ : ℂ) :=
    (analyticAt_comp mdiff_Δ τ).inv (by simpa using discriminant_ne_zero τ)
  have hordF : analyticOrderAt (fun z : ℂ => jf (ofComplex z) - jf τ) (τ : ℂ) = 3 • (k : ℕ∞) := by
    rw [hF, analyticOrderAt_mul (hE4a.pow 3) hΔi, analyticOrderAt_pow hE4a, ← hk,
      hΔi.analyticOrderAt_eq_zero.mpr (by simpa using discriminant_ne_zero τ), add_zero]
  have hrel := order_deriv_add_one τ
  rw [hderiv, hordF] at hrel
  have hk1 : k = 1 := by
    simp only [nsmul_eq_mul] at hrel
    have : ((2 * k + 1 : ℕ) : ℕ∞) = ((3 * k : ℕ) : ℕ∞) := by push_cast; exact_mod_cast hrel
    have := ENat.coe_inj.mp this
    omega
  refine ⟨?_, ?_⟩
  · rw [hordF, hk1]; rfl
  · obtain ⟨γ, hγ⟩ := JOrbitSeparation.exists_smul_eq_of_j_eq ρ τ
      (show jf ρ = jf τ by rw [jf_ρ, hjτ])
    rw [← hγ, natCard_stabilizer_smul, natCard_stabilizer_ρ]

theorem case_E₆_eq_zero {τ : ℍ} (h6 : E₆ τ = 0) :
    analyticOrderAt (fun z : ℂ => jf (ofComplex z) - jf τ) (τ : ℂ) = (2 : ℕ) ∧
      Nat.card (MulAction.stabilizer SL(2, ℤ) τ) = 4 := by
  obtain ⟨c, hc0, hc⟩ := exists_D_jf_mul_Δ_eq
  have h4 : E₄ τ ≠ 0 := fun h4 => E₆_ne_zero_of_E₄_eq_zero h4 h6
  have hjτ : jf τ = 1728 := jf_eq_of_E₆_eq_zero h6
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (analyticOrderAt_ne_top mdiff_E₆ E₆_ρ_ne_zero τ)
  have hderiv := analyticOrderAt_deriv_jf hc0 hc τ
  rw [analyticOrderAt_eq_zero_of_ne_zero mdiff_E₄ h4, smul_zero, zero_add, ← hk] at hderiv

  have hF : (fun z : ℂ => jf (ofComplex z) - jf τ) =
      ((E₆ : ℍ → ℂ) ∘ ofComplex) ^ 2 * fun w => ((Δ ∘ ofComplex) w)⁻¹ := by
    funext z
    have hΔ := discriminant_ne_zero (ofComplex z)
    have hΔ' := discriminant_eq_E₄_cube_sub_E₆_sq (ofComplex z)
    rw [hjτ]
    simp only [jf, Pi.mul_apply, Pi.pow_apply, Function.comp_apply]
    rw [div_sub' hΔ, div_eq_mul_inv]
    congr 1
    rw [hΔ']
    ring
  have hE6a : AnalyticAt ℂ ((E₆ : ℍ → ℂ) ∘ ofComplex) (τ : ℂ) := analyticAt_comp mdiff_E₆ τ
  have hΔi : AnalyticAt ℂ (fun w => ((Δ ∘ ofComplex) w)⁻¹) (τ : ℂ) :=
    (analyticAt_comp mdiff_Δ τ).inv (by simpa using discriminant_ne_zero τ)
  have hordF : analyticOrderAt (fun z : ℂ => jf (ofComplex z) - jf τ) (τ : ℂ) = 2 • (k : ℕ∞) := by
    rw [hF, analyticOrderAt_mul (hE6a.pow 2) hΔi, analyticOrderAt_pow hE6a, ← hk,
      hΔi.analyticOrderAt_eq_zero.mpr (by simpa using discriminant_ne_zero τ), add_zero]
  have hrel := order_deriv_add_one τ
  rw [hderiv, hordF] at hrel
  have hk1 : k = 1 := by
    simp only [nsmul_eq_mul] at hrel
    have : ((k + 1 : ℕ) : ℕ∞) = ((2 * k : ℕ) : ℕ∞) := by push_cast; exact_mod_cast hrel
    have := ENat.coe_inj.mp this
    omega
  refine ⟨?_, ?_⟩
  · rw [hordF, hk1]; rfl
  · have hjI : jf UpperHalfPlane.I = 1728 := jf_eq_of_E₆_eq_zero E₆_I
    obtain ⟨γ, hγ⟩ := JOrbitSeparation.exists_smul_eq_of_j_eq
      UpperHalfPlane.I τ (show jf UpperHalfPlane.I = jf τ by rw [hjI, hjτ])
    rw [← hγ, natCard_stabilizer_smul, natCard_stabilizer_I]

theorem case_generic {τ : ℍ} (h4 : E₄ τ ≠ 0) (h6 : E₆ τ ≠ 0) :
    analyticOrderAt (fun z : ℂ => jf (ofComplex z) - jf τ) (τ : ℂ) = (1 : ℕ) ∧
      Nat.card (MulAction.stabilizer SL(2, ℤ) τ) = 2 := by
  obtain ⟨c, hc0, hc⟩ := exists_D_jf_mul_Δ_eq
  have hD : D jf τ ≠ 0 := by
    intro h
    have := hc τ
    rw [h, zero_mul] at this
    exact mul_ne_zero hc0 (mul_ne_zero (pow_ne_zero _ h4) h6) this.symm
  have hd : deriv (jf ∘ ofComplex) (τ : ℂ) ≠ 0 := by
    rw [deriv_jf_eq _ τ.im_pos, ofComplex_apply]
    exact mul_ne_zero (by simp [Real.pi_ne_zero, Complex.I_ne_zero]) hD
  refine ⟨?_, ?_⟩
  · have h := (analyticAt_comp mdifferentiable_jf τ).analyticOrderAt_sub_eq_one_of_deriv_ne_zero hd
    rw [comp_apply_coe] at h
    exact h
  · rcases orbit_trichotomy τ with ⟨γ, rfl⟩ | ⟨γ, rfl⟩ | h
    · exact absurd ((E₆_smul_eq_zero_iff γ _).mpr E₆_I) h6
    · exact absurd ((E₄_smul_eq_zero_iff γ _).mpr E₄_ρ) h4
    · exact natCard_stabilizer_eq_two h

theorem order_and_card (τ : ℍ) : ∃ m : ℕ,
    analyticOrderAt (fun z : ℂ => jf (ofComplex z) - jf τ) (τ : ℂ) = m ∧
      Nat.card (MulAction.stabilizer SL(2, ℤ) τ) = 2 * m := by
  by_cases h4 : E₄ τ = 0
  · exact ⟨3, case_E₄_eq_zero h4⟩
  by_cases h6 : E₆ τ = 0
  · exact ⟨2, case_E₆_eq_zero h6⟩
  · exact ⟨1, case_generic h4 h6⟩

theorem main (τ : ℍ) :
    meromorphicOrderAt
        (fun z : ℂ => (ModularForm.E₄ : ℍ → ℂ) (ofComplex z) ^ 3 /
            ModularForm.discriminant (ofComplex z)
          - (ModularForm.E₄ : ℍ → ℂ) τ ^ 3 / ModularForm.discriminant τ) (τ : ℂ) =
      ((Nat.card (MulAction.stabilizer SL(2, ℤ) τ) / 2 : ℕ) : ℤ) := by
  obtain ⟨m, hm, hcard⟩ := order_and_card τ
  have hF : AnalyticAt ℂ (fun z : ℂ => jf (ofComplex z) - jf τ) (τ : ℂ) :=
    (analyticAt_comp mdifferentiable_jf τ).sub analyticAt_const
  change meromorphicOrderAt (fun z : ℂ => jf (ofComplex z) - jf τ) (τ : ℂ) = _
  rw [hF.meromorphicOrderAt_eq, hm, hcard, Nat.mul_div_cancel_left _ two_pos]
  rfl


end
end Dubon2026.SourceFunctionField.JMultiplicity
