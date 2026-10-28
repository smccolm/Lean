import Dubon2026.SourceModularSmoothCutoff

/-! Adapted from anthropics/fermats-last-theorem (Apache-2.0), frozen primary
Def_ModularCurve_SmoothedFundamental and
S_ModularCurve_contDiff_and_finsum_smoothedFundamental_eq_one;
exact hashes are recorded in modular-smooth-partition-route-875.json.
DUB-17/18 -> original all-weight arithmetic association -> actual Gamma1
Picard/H1 comparison -> Abel-Jacobi converse -> analytic reciprocity ->
winding/period limit -> smooth modular orbit partition. This constructs the
specific compact smooth family required by the source integral limit.
It assumes neither a period identity nor a principal-divisor realization.
Native proper discontinuity and the Mobius imaginary-part identity are
reused. The exact chosen-representative coset decomposition is proved. The central sign is not quotiented away here. -/
namespace Dubon2026.SourceSmoothedFundamental
noncomputable section
open UpperHalfPlane hiding I coe_smul
open Filter Complex MulAction Set
open scoped MatrixGroups Topology ContDiff Pointwise

theorem denom_eq (γ : SL(2, ℤ)) (z : ℂ) :
    denom γ z = ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) := by
  simp [denom]

theorem analyticAt_mob (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    AnalyticAt ℂ (mob γ) z := by
  unfold mob num denom
  exact ((analyticAt_const.mul analyticAt_id).add analyticAt_const).div
    ((analyticAt_const.mul analyticAt_id).add analyticAt_const)
    (UpperHalfPlane.denom_ne_zero_of_im γ hz.ne')

theorem mob_contDiffAt (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) (n : ℕ∞) :
    ContDiffAt ℝ n (mob γ) z :=
  ((analyticAt_mob γ hz).contDiffAt (n := n)).restrict_scalars ℝ

theorem im_mob (γ : SL(2, ℤ)) (z : ℂ) :
    (mob γ z).im = z.im / Complex.normSq (denom γ z) := by
  simpa [mob] using UpperHalfPlane.moebius_im (γ : GL (Fin 2) ℝ) z

theorem im_pos_of_im_mob_pos (γ : SL(2, ℤ)) {z : ℂ} (h : 0 < (mob γ z).im) : 0 < z.im := by
  rw [im_mob] at h
  by_contra hz
  push Not at hz
  have : z.im / Complex.normSq (denom γ z) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hz (Complex.normSq_nonneg _)
  linarith

theorem finite_moving (K L : Set ℍ) (hK : IsCompact K) (hL : IsCompact L) :
    {γ : SL(2, ℤ) | ((fun τ : ℍ => γ • τ) '' K ∩ L).Nonempty}.Finite := by
  have h := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := 𝒮ℒ) (T := ℍ) hK hL
  set φ : SL(2, ℤ) →* GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ with hφ
  have hinj : Function.Injective φ := by
    intro a b hab
    ext i j
    have := congrArg (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) i j) hab
    simpa [hφ] using this
  refine Finite.of_finite_image ?_ hinj.injOn
  refine (h.image Subtype.val).subset ?_
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨⟨φ g, ⟨g, rfl⟩⟩, hg, rfl⟩

theorem im_smul_le_inv (γ : SL(2, ℤ)) (τ : ℍ) (hc : (γ 1 0 : ℤ) ≠ 0) :
    (γ • τ).im ≤ τ.im⁻¹ := by
  rw [ModularGroup.im_smul_eq_div_normSq]
  have h1 := UpperHalfPlane.c_mul_im_sq_le_normSq_denom (g := (γ : GL (Fin 2) ℝ)) (z := τ)
  have hc' : (1 : ℝ) ≤ ((γ 1 0 : ℤ) : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ (γ 1 0) ^ 2 := by
      have := Int.one_le_abs hc
      nlinarith [sq_abs (γ 1 0)]
    exact_mod_cast this
  have hτ := τ.im_pos
  have hent : ((γ : GL (Fin 2) ℝ) 1 0 : ℝ) = ((γ 1 0 : ℤ) : ℝ) := by simp
  rw [hent] at h1
  have hns : τ.im ^ 2 ≤ Complex.normSq (denom γ τ) := by
    calc τ.im ^ 2 = 1 * τ.im ^ 2 := by ring
      _ ≤ ((γ 1 0 : ℤ) : ℝ) ^ 2 * τ.im ^ 2 := by gcongr
      _ = (((γ 1 0 : ℤ) : ℝ) * τ.im) ^ 2 := by ring
      _ ≤ _ := h1
  have hpos : 0 < Complex.normSq (denom γ τ) := lt_of_lt_of_le (by positivity) hns
  rw [div_le_iff₀ hpos]
  calc τ.im = τ.im⁻¹ * τ.im ^ 2 := by field_simp
    _ ≤ τ.im⁻¹ * Complex.normSq (denom γ τ) := by gcongr

theorem denom_of_c_eq_zero (γ : SL(2, ℤ)) (z : ℂ) (hc : (γ 1 0 : ℤ) = 0) :
    denom γ z = ((γ 1 1 : ℤ) : ℂ) := by
  rw [denom_eq, hc]; simp

theorem d_sq_of_c_eq_zero (γ : SL(2, ℤ)) (hc : (γ 1 0 : ℤ) = 0) :
    (γ 0 0 : ℤ) * γ 1 1 = 1 ∧ (γ 1 1 : ℤ) * γ 1 1 = 1 := by
  have h := γ.det_coe
  rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at h
  refine ⟨h, ?_⟩
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' h with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> norm_num

theorem im_smul_of_c_eq_zero (γ : SL(2, ℤ)) (τ : ℍ) (hc : (γ 1 0 : ℤ) = 0) :
    (γ • τ).im = τ.im := by
  rw [ModularGroup.im_smul_eq_div_normSq, denom_of_c_eq_zero γ _ hc]
  have h2 := (d_sq_of_c_eq_zero γ hc).2
  have : Complex.normSq (((γ 1 1 : ℤ) : ℂ)) = 1 := by
    rw [← Complex.ofReal_intCast, Complex.normSq_ofReal]; exact_mod_cast h2
  rw [this, div_one]

theorem im_smul_le_max (γ : SL(2, ℤ)) (τ : ℍ) : (γ • τ).im ≤ max τ.im τ.im⁻¹ := by
  by_cases hc : (γ 1 0 : ℤ) = 0
  · rw [im_smul_of_c_eq_zero γ τ hc]; exact le_max_left _ _
  · exact (im_smul_le_inv γ τ hc).trans (le_max_right _ _)

theorem exists_smul_nice (τ : ℍ) : ∃ γ : SL(2, ℤ),
    |(γ • τ).re| ≤ 1 / 2 ∧ 3 / 4 ≤ (γ • τ).im ∧ (γ • τ).im ≤ max τ.im τ.im⁻¹ := by
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd τ
  refine ⟨γ, hγ.2, ?_, im_smul_le_max γ τ⟩
  have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hγ
  nlinarith [(γ • τ).im_pos]

end
end Dubon2026.SourceSmoothedFundamental
