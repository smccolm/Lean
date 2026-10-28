import Dubon2026.SourceModularGreenSlicing
/-! DUB-17/18 -> original all-weight arithmetic association -> Gamma1 Picard/H1
-> Abel-Jacobi converse -> analytic reciprocity -> winding-period identity
-> Green's formula on the actual modular fundamental domain.
Adapted from pinned Apache-2.0 anthropics/fermats-last-theorem source.
Native Fubini, one-dimensional FTC and real change-of-variable theorems provide
the shorter rigorous route for the curved boundary; no boundary identity is
assumed. No incidental open-neighborhood assumption is retained. -/
namespace Dubon2026.SourceModularGreen
noncomputable section
open Complex MeasureTheory Set Filter Topology

variable (Φ : ℂ → ℂ) (Φ' : ℂ → ℂ →L[ℝ] ℂ) (U : Set ℂ) (δ : ℝ) (hδ : 0 < δ)
  (hDU : D ⊆ U) (hd : ∀ z ∈ U, HasFDerivAt Φ (Φ' z) z) (hc : ContinuousOn Φ' U)
  (hΦ : ∃ C : ℝ, ∀ z ∈ U, ‖Φ z‖ ≤ C * Real.exp (-δ * z.im))
  (hΦ' : ∃ C : ℝ, ∀ z ∈ U, ‖Φ' z‖ ≤ C * Real.exp (-δ * z.im))

/-- The actual unit-semicircle parametrization. -/
def γ (θ : ℝ) : ℂ := ⟨Real.cos θ, Real.sin θ⟩

lemma exp_mul_I_eq (θ : ℝ) : Complex.exp (θ * I) = γ θ :=
  Complex.ext (Complex.exp_ofReal_mul_I_re θ) (Complex.exp_ofReal_mul_I_im θ)

lemma continuous_γ : Continuous γ :=
  continuous_mk2.comp (Real.continuous_cos.prodMk Real.continuous_sin)

lemma cos_two_pi_div_three : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]

lemma sin_two_pi_div_three : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]

lemma pi_div_three_le : Real.pi / 3 ≤ 2 * Real.pi / 3 := by linarith [Real.pi_pos]

lemma abs_cos_le {θ : ℝ} (hθ : θ ∈ Icc (Real.pi / 3) (2 * Real.pi / 3)) :
    |Real.cos θ| ≤ 1 / 2 := by
  have hπ := Real.pi_pos
  rw [abs_le]
  constructor
  · have := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith) hθ.2
    rw [cos_two_pi_div_three] at this
    exact this
  · have := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith [hθ.2]) hθ.1
    rwa [Real.cos_pi_div_three] at this

lemma sin_nonneg_arc {θ : ℝ} (hθ : θ ∈ Icc (Real.pi / 3) (2 * Real.pi / 3)) : 0 ≤ Real.sin θ :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1, Real.pi_pos])
    (by linarith [hθ.2, Real.pi_pos])

lemma h_cos {θ : ℝ} (hθ : θ ∈ Icc (Real.pi / 3) (2 * Real.pi / 3)) :
    h (Real.cos θ) = Real.sin θ := by
  unfold h
  rw [← Real.sin_sq θ, Real.sqrt_sq (sin_nonneg_arc hθ)]

lemma r_sin (θ : ℝ) : r (Real.sin θ) = |Real.cos θ| := by
  unfold r
  rw [← Real.cos_sq' θ, Real.sqrt_sq_eq_abs]

lemma γ_mem_D {θ : ℝ} (hθ : θ ∈ Icc (Real.pi / 3) (2 * Real.pi / 3)) : γ θ ∈ D :=
  mk_mem_D (abs_cos_le hθ) (h_cos hθ).le

lemma continuousOn_Φ (hd : ∀ z ∈ U, HasFDerivAt Φ (Φ' z) z) : ContinuousOn Φ U :=
  fun z hz => (hd z hz).continuousAt.continuousWithinAt

include hd hDU in
lemma continuousOn_arc : ContinuousOn (fun θ => Φ (γ θ)) (Icc (Real.pi / 3) (2 * Real.pi / 3)) :=
  (continuousOn_Φ Φ Φ' U hd).comp continuous_γ.continuousOn fun _ hθ => hDU (γ_mem_D hθ)

lemma arc_sin :
    ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3), Real.sin θ • Φ (γ θ) =
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2), Φ ⟨x, h x⟩ := by
  have hab := pi_div_three_le
  have key : ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
      (-Real.sin θ) • ((fun x : ℝ => Φ ⟨x, h x⟩) ∘ Real.cos) θ =
        -∫ x in (-(1 / 2 : ℝ))..(1 / 2), Φ ⟨x, h x⟩ := by
    rw [intervalIntegral.integral_deriv_smul_comp_of_deriv_nonpos Real.continuous_cos.continuousOn
      (fun θ _ => Real.hasDerivAt_cos θ) (fun θ hθ => ?_), Real.cos_pi_div_three,
      cos_two_pi_div_three, intervalIntegral.integral_symm]
    rw [min_eq_left hab, max_eq_right hab] at hθ
    exact neg_nonpos.mpr (sin_nonneg_arc (Ioo_subset_Icc_self hθ))
  calc ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3), Real.sin θ • Φ (γ θ)
      = ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
          -((-Real.sin θ) • ((fun x : ℝ => Φ ⟨x, h x⟩) ∘ Real.cos) θ) := by
        refine intervalIntegral.integral_congr fun θ hθ => ?_
        rw [uIcc_of_le hab] at hθ
        simp only [Function.comp_apply, neg_smul, neg_neg, h_cos hθ, γ]
    _ = _ := by rw [intervalIntegral.integral_neg, key, neg_neg]

include hd hDU in

lemma arc_cos :
    ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3), Real.cos θ • Φ (γ θ) =
      -∫ y in (Real.sqrt 3 / 2)..1, corr Φ y := by
  have hπ := Real.pi_pos
  have h1 : Real.pi / 3 ≤ Real.pi / 2 := by linarith
  have h2 : Real.pi / 2 ≤ 2 * Real.pi / 3 := by linarith
  have hΦc := continuousOn_Φ Φ Φ' U hd
  have hcont : ContinuousOn (fun θ => Real.cos θ • Φ (γ θ)) (Icc (Real.pi / 3) (2 * Real.pi / 3)) :=
    Real.continuous_cos.continuousOn.smul (continuousOn_arc Φ Φ' U hDU hd)
  have hi1 : IntervalIntegrable (fun θ => Real.cos θ • Φ (γ θ)) volume (Real.pi / 3) (Real.pi / 2) :=
    (hcont.mono (by rw [uIcc_of_le h1]; exact Icc_subset_Icc_right h2)).intervalIntegrable
  have hi2 : IntervalIntegrable (fun θ => Real.cos θ • Φ (γ θ)) volume (Real.pi / 2)
      (2 * Real.pi / 3) :=
    (hcont.mono (by rw [uIcc_of_le h2]; exact Icc_subset_Icc_left h1)).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]

  have k1 : ∫ θ in (Real.pi / 3)..(Real.pi / 2), Real.cos θ • Φ (γ θ) =
      ∫ y in (Real.sqrt 3 / 2)..1, Φ ⟨r y, y⟩ := by
    rw [← Real.sin_pi_div_three, ← Real.sin_pi_div_two,
      ← intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg (g := fun y : ℝ => Φ ⟨r y, y⟩)
        Real.continuous_sin.continuousOn (fun θ _ => Real.hasDerivAt_sin θ) (fun θ hθ => ?_)]
    · refine intervalIntegral.integral_congr fun θ hθ => ?_
      rw [uIcc_of_le h1] at hθ
      have hc0 : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], hθ.2⟩
      simp only [Function.comp_apply, γ, r_sin, abs_of_nonneg hc0]
    · rw [min_eq_left h1, max_eq_right h1] at hθ
      exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], hθ.2.le⟩

  have k2 : ∫ θ in (Real.pi / 2)..(2 * Real.pi / 3), Real.cos θ • Φ (γ θ) =
      -∫ y in (Real.sqrt 3 / 2)..1, Φ ⟨-r y, y⟩ := by
    rw [← sin_two_pi_div_three, ← Real.sin_pi_div_two,
      ← intervalIntegral.integral_symm (Real.sin (2 * Real.pi / 3)) (Real.sin (Real.pi / 2)),
      ← intervalIntegral.integral_deriv_smul_comp_of_deriv_nonpos (g := fun y : ℝ => Φ ⟨-r y, y⟩)
        Real.continuous_sin.continuousOn (fun θ _ => Real.hasDerivAt_sin θ) (fun θ hθ => ?_)]
    · refine intervalIntegral.integral_congr fun θ hθ => ?_
      rw [uIcc_of_le h2] at hθ
      have hc0 : Real.cos θ ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le hθ.1 (by linarith [hθ.2])
      simp only [Function.comp_apply, γ, r_sin, abs_of_nonpos hc0, neg_neg]
    · rw [min_eq_left h2, max_eq_right h2] at hθ
      exact Real.cos_nonpos_of_pi_div_two_le_of_le hθ.1.le (by linarith [hθ.2])
  have hg1 : IntervalIntegrable (fun y : ℝ => Φ ⟨r y, y⟩) volume (Real.sqrt 3 / 2) 1 := by
    refine (ContinuousOn.mono ?_ (by rw [uIcc_of_le sqrt3_lt_one.le])).intervalIntegrable
    exact hΦc.comp (continuous_mk2.comp (continuous_r.prodMk continuous_id)).continuousOn
      fun y hy => hDU (mem_D_r hy.1 hy.2)
  have hg2 : IntervalIntegrable (fun y : ℝ => Φ ⟨-r y, y⟩) volume (Real.sqrt 3 / 2) 1 := by
    refine (ContinuousOn.mono ?_ (by rw [uIcc_of_le sqrt3_lt_one.le])).intervalIntegrable
    exact hΦc.comp (continuous_mk2.comp (continuous_r.neg.prodMk continuous_id)).continuousOn
      fun y hy => hDU (mem_D_neg_r hy.1 hy.2)
  rw [k1, k2, show (corr Φ) = fun y => Φ ⟨-r y, y⟩ - Φ ⟨r y, y⟩ from rfl,
    intervalIntegral.integral_sub hg2 hg1]
  ring

lemma arc_integrand (θ : ℝ) :
    Φ (Complex.exp (θ * I)) * (I * Complex.exp (θ * I)) =
      -(Real.sin θ • Φ (γ θ)) + I * (Real.cos θ • Φ (γ θ)) := by
  rw [exp_mul_I_eq, Complex.real_smul, Complex.real_smul]
  have e : (γ θ : ℂ) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I := mk_eq _ _
  generalize Φ (γ θ) = w
  rw [e]
  linear_combination ((Real.sin θ : ℂ) * w) * Complex.I_mul_I

include hd hDU in
lemma arc_split :
    ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3), Φ (Complex.exp (θ * I)) * (I * Complex.exp (θ * I)) =
      -(∫ θ in (Real.pi / 3)..(2 * Real.pi / 3), Real.sin θ • Φ (γ θ)) +
        I * ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3), Real.cos θ • Φ (γ θ) := by
  have hab := pi_div_three_le
  have harc := continuousOn_arc Φ Φ' U hDU hd
  have hi1 : IntervalIntegrable (fun θ => Real.sin θ • Φ (γ θ)) volume (Real.pi / 3)
      (2 * Real.pi / 3) := by
    refine (ContinuousOn.mono ?_ (by rw [uIcc_of_le hab])).intervalIntegrable
    exact Real.continuous_sin.continuousOn.smul harc
  have hi2 : IntervalIntegrable (fun θ => Real.cos θ • Φ (γ θ)) volume (Real.pi / 3)
      (2 * Real.pi / 3) := by
    refine (ContinuousOn.mono ?_ (by rw [uIcc_of_le hab])).intervalIntegrable
    exact Real.continuous_cos.continuousOn.smul harc
  have hi1' : IntervalIntegrable (fun θ => -(Real.sin θ • Φ (γ θ))) volume (Real.pi / 3)
      (2 * Real.pi / 3) := hi1.neg
  have hi2' : IntervalIntegrable (fun θ => I * (Real.cos θ • Φ (γ θ))) volume (Real.pi / 3)
      (2 * Real.pi / 3) := hi2.const_mul I
  rw [← intervalIntegral.integral_neg, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add hi1' hi2']
  exact intervalIntegral.integral_congr fun θ _ => arc_integrand Φ θ


end
end Dubon2026.SourceModularGreen
