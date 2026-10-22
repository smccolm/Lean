import Dubon2026.SourceModularStabilizerOrders
import Mathlib.Analysis.Real.Pi.Bounds

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
theorem norm_deriv_le {G : ℍ → ℂ} (hG : MDiff G) {M A : ℝ}
    (hM : ∀ z : ℍ, A ≤ z.im → ‖G z‖ ≤ M) (z : ℍ) (hz : max A 0 + 1 < z.im) :
    ‖deriv (G ∘ ofComplex) z‖ ≤ M := by
  have him : ∀ w : ℂ, dist w (z : ℂ) ≤ 1 → z.im - 1 ≤ w.im := by
    intro w hw
    have h1 : |(w - z).im| ≤ ‖w - (z : ℂ)‖ := Complex.abs_im_le_norm _
    rw [dist_eq_norm] at hw
    rw [Complex.sub_im, UpperHalfPlane.coe_im] at h1
    have := (abs_le.mp (h1.trans hw)).1
    linarith
  have hsub : Metric.closedBall (z : ℂ) 1 ⊆ {w : ℂ | 0 < w.im} := by
    intro w hw
    have := him w (Metric.mem_closedBall.mp hw)
    simp only [Set.mem_setOf_eq]
    have : (0 : ℝ) ≤ max A 0 := le_max_right _ _
    linarith
  have hd : DiffContOnCl ℂ (G ∘ ofComplex) (Metric.ball (z : ℂ) 1) :=
    (UpperHalfPlane.mdifferentiable_iff.mp hG).diffContOnCl_ball hsub
  have hC : ∀ w ∈ Metric.sphere (z : ℂ) 1, ‖(G ∘ ofComplex) w‖ ≤ M := by
    intro w hw
    have h1 := him w (Metric.mem_sphere.mp hw).le
    have hw0 : 0 < w.im := by
      have : (0 : ℝ) ≤ max A 0 := le_max_right _ _
      linarith
    rw [Function.comp_apply, ofComplex_apply_of_im_pos hw0]
    apply hM
    change A ≤ w.im
    have : A ≤ max A 0 := le_max_left _ _
    linarith
  simpa using Complex.norm_deriv_le_of_forall_mem_sphere_norm_le one_pos hd hC

theorem norm_D_le_norm_deriv (G : ℍ → ℂ) (z : ℍ) : ‖D G z‖ ≤ ‖deriv (G ∘ ofComplex) z‖ := by
  rw [normalizedDerivOfComplex, norm_mul]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  rw [norm_inv]
  refine inv_le_one_of_one_le₀ ?_
  simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
  nlinarith [Real.pi_gt_three]

theorem isBoundedAtImInfty_D {G : ℍ → ℂ} (hG : MDiff G) (hb : IsBoundedAtImInfty G) :
    IsBoundedAtImInfty (D G) := by
  rw [isBoundedAtImInfty_iff] at hb ⊢
  obtain ⟨M, A, hM⟩ := hb
  refine ⟨M, max A 0 + 2, fun z hz => (norm_D_le_norm_deriv G z).trans ?_⟩
  exact norm_deriv_le hG hM z (by linarith)

theorem isZeroAtImInfty_D {G : ℍ → ℂ} (hG : MDiff G) (hb : IsZeroAtImInfty G) :
    IsZeroAtImInfty (D G) := by
  rw [isZeroAtImInfty_iff] at hb ⊢
  intro ε hε
  obtain ⟨A, hA⟩ := hb ε hε
  refine ⟨max A 0 + 2, fun z hz => (norm_D_le_norm_deriv G z).trans ?_⟩
  exact norm_deriv_le hG hA z (by linarith)


end
end Dubon2026.SourceFunctionField.JMultiplicity
