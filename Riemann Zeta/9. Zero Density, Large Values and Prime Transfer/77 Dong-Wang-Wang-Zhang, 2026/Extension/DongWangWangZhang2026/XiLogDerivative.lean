import DongWangWangZhang2026.XiZeros

/-!
# The real xi logarithmic derivative

Absolute convergence and multiplicity-preserving reflection cancel the
linear Hadamard factor. The resulting zero sum is for the actual xi function,
with no assumed factorization or prescribed value of its exponential factor.
-/

namespace DongWangWangZhang2026
noncomputable section
open Complex Complex.Hadamard Set
open scoped Topology

/-- The real parts of reciprocal zeros are absolutely summable. -/
theorem summable_xiZero_re_inv :
    Summable (fun p : XiZero => (1 / xiZeroPoint p).re) := by
  apply summable_xiZero_norm_inv_sq.of_norm_bounded
  intro p
  rw [one_div, inv_re, normSq_eq_norm_sq, Real.norm_eq_abs, abs_div,
    abs_of_pos (xiZeroPoint_re p).1, abs_of_nonneg (sq_nonneg _)]
  calc
    (xiZeroPoint p).re / ‖xiZeroPoint p‖ ^ 2 ≤ 1 / ‖xiZeroPoint p‖ ^ 2 :=
      div_le_div_of_nonneg_right (xiZeroPoint_re p).2.le (sq_nonneg _)
    _ = ‖xiZeroPoint p‖⁻¹ ^ (2 : ℕ) := by rw [one_div, inv_pow]

/-- Away from actual zeros, the real resolvent sum is absolutely convergent. -/
theorem summable_xiZero_re_resolvent {s : ℂ}
    (hs : ∀ p : XiZero, s ≠ xiZeroPoint p) :
    Summable (fun p : XiZero => (1 / (s - xiZeroPoint p)).re) := by
  have h := summable_riemannXi_logDerivTerms_divisorZeroIndex₀ hs
  have hr := (Complex.hasSum_re h.hasSum).summable
  simpa only [add_re, add_sub_cancel_right] using hr.sub summable_xiZero_re_inv

/-- Functional-equation reflection negates the actual xi logarithmic derivative. -/
theorem xi_logDeriv_reflect (s : ℂ) :
    logDeriv riemannXi (1 - s) = -logDeriv riemannXi s := by
  have hf : riemannXi ∘ (fun z : ℂ => 1 - z) = riemannXi := by
    funext z
    exact riemannXi_one_sub z
  have h := logDeriv_comp (x := s)
    (differentiable_riemannXi (1 - s))
    (show DifferentiableAt ℂ (fun z : ℂ => 1 - z) s by fun_prop)
  rw [hf] at h
  have hd : deriv (fun z : ℂ => 1 - z) s = -1 := by simp
  change logDeriv riemannXi s =
    logDeriv riemannXi (1 - s) * deriv (fun z : ℂ => 1 - z) s at h
  rw [hd] at h
  linear_combination h

/-- Reflection reindexes all multiplicity labels in the reciprocal zero sum. -/
theorem tsum_xiZero_re_reflected_inv :
    (∑' p : XiZero, (1 / (1 - xiZeroPoint p)).re) =
      ∑' p : XiZero, (1 / xiZeroPoint p).re := by
  exact xiZeroReflectEquiv.tsum_eq (fun p => (1 / xiZeroPoint p).re)

/-- The source real logarithmic-derivative formula, with its convergence proved. -/
theorem re_xi_logDeriv_eq_tsum {s : ℂ}
    (hs : ∀ p : XiZero, s ≠ xiZeroPoint p) :
    (logDeriv riemannXi s).re =
      ∑' p : XiZero, (1 / (s - xiZeroPoint p)).re := by
  obtain ⟨P, hP, hfac⟩ := riemannXi_hadamard_factorization_no_monomial
  have hder (z : ℂ) : P.derivative.eval z = P.coeff 1 := by
    conv_lhs => rw [Polynomial.eq_X_add_C_of_degree_le_one hP]
    simp
  have hlog (z : ℂ) (hz : ∀ p : XiZero, z ≠ xiZeroPoint p) :
      logDeriv riemannXi z = P.coeff 1 +
        ∑' p : XiZero, (1 / (z - xiZeroPoint p) + 1 / xiZeroPoint p) := by
    simpa only [hder] using
      logDeriv_riemannXi_eq_polynomial_derivative_add_tsum hfac hz
  have hzero : ∀ p : XiZero, (0 : ℂ) ≠ xiZeroPoint p :=
    fun p => (divisorZeroIndex₀_val_ne_zero p).symm
  have hone : ∀ p : XiZero, (1 : ℂ) ≠ xiZeroPoint p := by
    intro p he
    have hr := congrArg Complex.re he
    simp only [one_re] at hr
    linarith [(xiZeroPoint_re p).2]
  have h0 := hlog 0 hzero
  simp only [zero_sub, one_div, inv_neg, neg_add_cancel, tsum_zero, add_zero] at h0
  have h1 := congrArg Complex.re (hlog 1 hone)
  have href := xi_logDeriv_reflect 0
  simp only [sub_zero] at href
  rw [href, h0, neg_re, add_re,
    Complex.re_tsum (summable_riemannXi_logDerivTerms_divisorZeroIndex₀ hone)] at h1
  simp only [add_re] at h1
  rw [(summable_xiZero_re_resolvent hone).tsum_add summable_xiZero_re_inv,
    tsum_xiZero_re_reflected_inv] at h1
  have hcancel : (P.coeff 1).re + (∑' p : XiZero, (1 / xiZeroPoint p).re) = 0 := by
    linarith
  rw [hlog s hs, add_re,
    Complex.re_tsum (summable_riemannXi_logDerivTerms_divisorZeroIndex₀ hs)]
  simp only [add_re]
  rw [(summable_xiZero_re_resolvent hs).tsum_add summable_xiZero_re_inv]
  linarith

/-- The source identity on the entire closed right half-plane needs no zero-avoidance premise. -/
theorem re_xi_logDeriv_eq_tsum_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    Summable (fun p : XiZero => (1 / (s - xiZeroPoint p)).re) ∧
      (logDeriv riemannXi s).re =
        ∑' p : XiZero, (1 / (s - xiZeroPoint p)).re := by
  have hz : ∀ p : XiZero, s ≠ xiZeroPoint p := by
    intro p h
    have hr := congrArg Complex.re h
    linarith [(xiZeroPoint_re p).2]
  exact ⟨summable_xiZero_re_resolvent hz, re_xi_logDeriv_eq_tsum hz⟩

/-- Exact logarithmic derivative of the completed-zeta gamma factor. -/
theorem logDeriv_GammaReal {s : ℂ} (hs : 0 < s.re) :
    logDeriv Gammaℝ s =
      -(Complex.log (Real.pi : ℂ)) / 2 + logDeriv Gamma (s / 2) / 2 := by
  have hp : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hg := Gamma_ne_zero_of_re_pos (by simpa using half_pos hs : 0 < (s / 2).re)
  have hdc := (((hasDerivAt_id s).neg).div_const (2 : ℂ)).const_cpow (Or.inl hp)
  have hGamma := differentiableAt_Gamma (s := s / 2) (fun n => by
    intro h
    have hr := congrArg Complex.re h
    simp only [div_ofNat_re, neg_re, natCast_re] at hr
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith)
  have hdg := hGamma.hasDerivAt.comp s ((hasDerivAt_id s).div_const (2 : ℂ))
  dsimp only [Pi.neg_apply, id_eq, Function.comp_def] at hdc hdg
  have hc : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by simp [hp]
  change logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Gamma (z / 2)) s = _
  rw [logDeriv_mul (f := fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
    (g := fun z : ℂ => Gamma (z / 2))
    s hc hg hdc.differentiableAt hdg.differentiableAt]
  rw [logDeriv_apply, hdc.deriv, logDeriv_apply, hdg.deriv, logDeriv_apply]
  field_simp [hc, hg]

/-- The exact xi/zeta/gamma logarithmic-derivative decomposition on the source half-plane. -/
theorem xi_logDeriv_eq_zeta_gamma {s : ℂ} (hs : 1 < s.re) :
    logDeriv riemannXi s = 1 / s + 1 / (s - 1) -
      Complex.log (Real.pi : ℂ) / 2 + logDeriv Gamma (s / 2) / 2 +
      logDeriv riemannZeta s := by
  have hspos : 0 < s.re := lt_trans zero_lt_one hs
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hz := riemannZeta_ne_zero_of_one_le_re hs.le
  have hg := Gammaℝ_ne_zero_of_re_pos hspos
  have hdg : DifferentiableAt ℂ Gammaℝ s := by
    have hd := (differentiable_Gammaℝ_inv s).inv (inv_ne_zero hg)
    have he : (fun z : ℂ => (Gammaℝ z)⁻¹)⁻¹ = Gammaℝ := by
      funext z
      exact inv_inv _
    rwa [he] at hd
  have he : riemannXi =ᶠ[𝓝 s]
      (fun z : ℂ => (z * (z - 1) * Gammaℝ z * riemannZeta z) * (2 : ℂ)⁻¹) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hspos,
      isOpen_ne.mem_nhds hs1] with z hzpos hz1
    rw [xi_eq_factor_mul_zeta hzpos hz1]
    ring
  have hlog :
      logDeriv riemannXi s =
        logDeriv (fun z : ℂ =>
          (z * (z - 1) * Gammaℝ z * riemannZeta z) * (2 : ℂ)⁻¹) s := by
    rw [logDeriv_apply, logDeriv_apply, he.deriv_eq, he.self_of_nhds]
  rw [hlog, logDeriv_mul_const s _ (by norm_num)]
  rw [logDeriv_mul (f := fun z : ℂ => z * (z - 1) * Gammaℝ z) (g := riemannZeta)
    s (mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) hg) hz
    (((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul hdg))
    (differentiableAt_riemannZeta hs1)]
  rw [logDeriv_mul (f := fun z : ℂ => z * (z - 1)) (g := Gammaℝ)
    s (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) hg
    (differentiableAt_id.mul (differentiableAt_id.sub_const 1)) hdg]
  rw [logDeriv_mul (f := fun z : ℂ => z) (g := fun z : ℂ => z - 1)
    s hs0 (sub_ne_zero.mpr hs1)
    differentiableAt_id (differentiableAt_id.sub_const 1), logDeriv_GammaReal hspos]
  simp only [logDeriv_apply, deriv_id'', deriv_sub_const]
  ring

/-- The real zero sum equals the source zeta/gamma expression, with absolute convergence. -/
theorem tsum_xiZero_re_eq_zeta_gamma {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : XiZero => (1 / (s - xiZeroPoint p)).re) ∧
      (∑' p : XiZero, (1 / (s - xiZeroPoint p)).re) =
        (1 / s + 1 / (s - 1) - Complex.log (Real.pi : ℂ) / 2 +
          logDeriv Gamma (s / 2) / 2 + logDeriv riemannZeta s).re := by
  have h := re_xi_logDeriv_eq_tsum_of_one_le_re hs.le
  exact ⟨h.1, h.2.symm.trans (congrArg Complex.re (xi_logDeriv_eq_zeta_gamma hs))⟩

/-- The inverse-square zero kernel used in zero repulsion converges absolutely. -/
theorem summable_xiZero_inverse_square {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : XiZero => 1 / ‖s - xiZeroPoint p‖ ^ 2) := by
  have hr := (re_xi_logDeriv_eq_tsum_of_one_le_re hs.le).1
  apply (hr.div_const (s.re - 1)).of_norm_bounded
  intro p
  have hβ := (xiZeroPoint_re p).2
  have hgap : 0 < s.re - 1 := sub_pos.mpr hs
  have hn : 0 < ‖s - xiZeroPoint p‖ ^ 2 := by
    apply sq_pos_of_pos
    apply norm_pos_iff.mpr
    intro he
    have hz := congrArg Complex.re he
    simp only [sub_re, zero_re] at hz
    linarith
  rw [Real.norm_eq_abs, abs_of_pos (div_pos zero_lt_one hn)]
  simp only [one_div, inv_re, normSq_eq_norm_sq, sub_re]
  rw [le_div_iff₀ hgap]
  have hnum : s.re - 1 ≤ s.re - (xiZeroPoint p).re := by linarith
  calc
    (‖s - xiZeroPoint p‖ ^ 2)⁻¹ * (s.re - 1) =
        (s.re - 1) / ‖s - xiZeroPoint p‖ ^ 2 := by ring
    _ ≤ (s.re - (xiZeroPoint p).re) / ‖s - xiZeroPoint p‖ ^ 2 :=
      div_le_div_of_nonneg_right hnum hn.le

end
end DongWangWangZhang2026
