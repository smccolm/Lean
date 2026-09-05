import GafniTao.PintzZetaAFETermContour

/-!
# Vanishing horizontal edges for individual AFE coefficients

The bound is deliberately termwise.  This permits different contour sides
for coefficients below and above the square-root conductor.
-/

open Complex Filter MeasureTheory Set Topology
open scoped LSeries.notation

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Deligne's real Gamma factor is uniformly bounded on every compact
positive real-part strip, without the offset convention of the frozen helper. -/
theorem exists_uniform_norm_GammaR_positive_strip
    {r₀ r₁ : ℝ} (hr₀ : 0 < r₀) :
    ∃ G : ℝ, 0 < G ∧ ∀ (x y : ℝ), x ∈ Set.Icc r₀ r₁ →
      ‖Complex.Gammaℝ ((x : ℝ) + (y : ℂ) * I)‖ ≤ G := by
  let gammaMajor : ℝ → ℝ := fun x =>
    Real.pi ^ (-x / 2) * Real.Gamma (x / 2)
  have hgammaCont : ContinuousOn (fun x => Real.Gamma (x / 2))
      (Set.Icc r₀ r₁) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.comp
      (by fun_prop : ContinuousOn (fun x : ℝ => x / 2) (Set.Icc r₀ r₁))
      (by
        intro x hx
        change 0 < x / 2
        have := hr₀.trans_le hx.1
        positivity)
  have hpowCont : Continuous (fun x : ℝ => Real.pi ^ (-x / 2)) :=
    (Real.continuous_const_rpow Real.pi_ne_zero).comp (by fun_prop)
  have hmajorCont : ContinuousOn gammaMajor (Set.Icc r₀ r₁) :=
    hpowCont.continuousOn.mul hgammaCont
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hmajorCont
  refine ⟨max 1 C, lt_max_of_lt_left zero_lt_one, ?_⟩
  intro x y hx
  have hsre : (((x : ℝ) : ℂ) + (y : ℂ) * I).re = x := by simp
  have hspos : 0 < (((x : ℝ) : ℂ) + (y : ℂ) * I).re := by
    rw [hsre]
    exact hr₀.trans_le hx.1
  have hbound := norm_GammaR_le_realGamma_re hspos
  have hmajor : gammaMajor x ≤ C := hC ⟨x, hx, rfl⟩
  calc
    _ ≤ gammaMajor x := by simpa [gammaMajor, hsre] using hbound
    _ ≤ C := hmajor
    _ ≤ max 1 C := le_max_right _ _

/-- A positive zeta Dirichlet coefficient has norm at most one in the open
right half-plane. -/
theorem norm_pintzZetaDirichletTerm_le_one
    {z : ℂ} {n : ℕ} (hn : n ≠ 0) (hz : 0 ≤ z.re) :
    ‖pintzZetaDirichletTerm z n‖ ≤ 1 := by
  rw [pintzZetaDirichletTerm, LSeries.norm_term_eq, if_neg hn]
  have hzeta :
      ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) n) = 1 := by
    rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne hn]
    norm_num
  rw [hzeta, norm_one]
  change (1 : ℝ) / (n : ℝ) ^ z.re ≤ 1
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ z.re :=
    Real.one_le_rpow
      (Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hn)) hz
  exact (div_le_one₀ (Real.rpow_pos_of_pos hnpos z.re)).mpr hpow

private theorem mul_six_le_mul_six
    {a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆ : ℝ}
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) (h₃ : a₃ ≤ b₃)
    (h₄ : a₄ ≤ b₄) (h₅ : a₅ ≤ b₅) (h₆ : a₆ ≤ b₆)
    (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃)
    (ha₄ : 0 ≤ a₄) (ha₅ : 0 ≤ a₅) (ha₆ : 0 ≤ a₆)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hb₃ : 0 ≤ b₃)
    (hb₄ : 0 ≤ b₄) (hb₅ : 0 ≤ b₅) :
    (((((a₁ * a₂) * a₃) * a₄) * a₅) * a₆) ≤
      (((((b₁ * b₂) * b₃) * b₄) * b₅) * b₆) := by
  gcongr

private theorem norm_pintzZetaAFETermContourIntegrand_eq
    (s base : ℂ) (n : ℕ) (w : ℂ) :
    ‖pintzZetaAFETermContourIntegrand s base n w‖ =
      ‖Complex.exp (100 * w ^ 2)‖ *
        ‖(base + w) * (1 - (base + w))‖ *
        ‖Complex.Gammaℝ (base + w)‖ *
        ‖(pintzZetaAFENormalization s)⁻¹‖ *
        ‖pintzZetaDirichletTerm (base + w) n‖ * ‖w⁻¹‖ := by
  unfold pintzZetaAFETermContourIntegrand pintzZetaAFETermNumerator
  dsimp only
  rw [norm_div, norm_mul, norm_div, norm_mul, norm_mul]
  simp only [div_eq_mul_inv, norm_mul, norm_inv]

private theorem mul_four_reorder (a b c d : ℝ) :
    a * b * c * d * 1 * 1 = c * d * a * b := by ring

set_option maxHeartbeats 150000 in
/-- Uniform pointwise decay on the upper horizontal side of a termwise
rectangle.  The degree sixteen envelope is shared with the frozen contour
infrastructure and is intentionally generous. -/
theorem exists_pintzZetaAFETerm_horizontal_abs_bound
    (s base : ℂ) {n : ℕ} (hn : n ≠ 0) {q c : ℝ}
    (hq : 0 < q) (hc : 0 < c) (hbase : q < base.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 1 ≤ |y| → ∀ x ∈ Set.uIcc (-q) c,
      ‖pintzZetaAFETermContourIntegrand s base n
          ((x : ℂ) + (y : ℂ) * I)‖ ≤
        C * Real.exp (100 * (max q c) ^ 2 - 100 * y ^ 2) *
          (2 + ‖base‖ + max q c + |y|) ^ 16 := by
  let W : ℝ := max q c
  have hW0 : 0 ≤ W := le_trans hq.le (le_max_left _ _)
  have hr₀ : 0 < base.re - q := sub_pos.mpr hbase
  obtain ⟨G, hG, hgamma⟩ :=
    exists_uniform_norm_GammaR_positive_strip
      (r₀ := base.re - q) (r₁ := base.re + c) hr₀
  let D : ℝ := ‖(pintzZetaAFENormalization s)⁻¹‖ + 1
  let C : ℝ := (G + 1) * D
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro y hy x hx
  let w : ℂ := (x : ℂ) + (y : ℂ) * I
  let z : ℂ := base + w
  change ‖pintzZetaAFETermContourIntegrand s base n w‖ ≤
    C * Real.exp (100 * (max q c) ^ 2 - 100 * y ^ 2) *
      (2 + ‖base‖ + max q c + |y|) ^ 16
  have hqc : -q ≤ c := by linarith
  rw [uIcc_of_le hqc] at hx
  have hxW : |x| ≤ W := by
    rw [abs_le]
    constructor
    · exact (neg_le_neg (le_max_left q c)).trans hx.1
    · exact hx.2.trans (le_max_right q c)
  have hzre : z.re = base.re + x := by simp [z, w]
  have hzmem : base.re + x ∈ Set.Icc (base.re - q) (base.re + c) := by
    constructor <;> linarith [hx.1, hx.2]
  have hgammaBound : ‖Complex.Gammaℝ z‖ ≤ G := by
    have harg :
        (((base.re + x : ℝ) : ℂ) + ((base.im + y : ℝ) : ℂ) * I) =
          z := by
      dsimp only [z, w]
      apply Complex.ext <;> simp
    rw [← harg]
    exact hgamma (base.re + x) (base.im + y) hzmem
  have hzpos : 0 ≤ z.re := by
    rw [hzre]
    linarith [hx.1]
  have hdirichlet := norm_pintzZetaDirichletTerm_le_one hn hzpos
  have hgauss :
      ‖Complex.exp (100 * w ^ 2)‖ ≤
        Real.exp (100 * W ^ 2 - 100 * y ^ 2) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hre : (w ^ 2).re = x ^ 2 - y ^ 2 := by
      simp [w, pow_two, mul_re, mul_im]
    have hxsq : x ^ 2 ≤ W ^ 2 := by
      rw [sq_le_sq]
      exact hxW.trans (le_abs_self W)
    norm_num [mul_re, hre]
    nlinarith
  have hwNorm : 1 ≤ ‖w‖ := by
    have him : w.im = y := by
      dsimp only [w]
      simp
    have habsEq : |y| = |w.im| := (congrArg abs him).symm
    exact hy.trans (habsEq.le.trans (Complex.abs_im_le_norm w))
  have hzNorm : ‖z‖ ≤ ‖base‖ + W + |y| := by
    calc
      _ ≤ ‖base‖ + ‖w‖ := by
        dsimp only [z]
        exact norm_add_le _ _
      _ ≤ ‖base‖ + (|x| + |y|) := by
        gcongr
        dsimp only [w]
        exact (norm_add_le (x : ℂ) ((y : ℂ) * I)).trans_eq (by
          simp [Real.norm_eq_abs])
      _ ≤ ‖base‖ + W + |y| := by linarith
  let B : ℝ := 2 + ‖base‖ + W + |y|
  have hB : 1 ≤ B := by
    dsimp only [B]
    linarith [norm_nonneg base]
  have hpoly : ‖z * (1 - z)‖ ≤ B ^ 2 := by
    rw [norm_mul]
    have hfirst : ‖z‖ ≤ B := by
      dsimp only [B]
      linarith
    have hsecond : ‖1 - z‖ ≤ B := by
      exact (norm_sub_le _ _).trans (by
        norm_num
        dsimp only [B]
        linarith)
    exact (mul_le_mul hfirst hsecond (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hBpow : B ^ 2 ≤ B ^ 16 := by
    exact pow_le_pow_right₀ hB (by omega)
  have hpoly16 : ‖z * (1 - z)‖ ≤ B ^ 16 := hpoly.trans hBpow
  have hgammaPlus : ‖Complex.Gammaℝ z‖ ≤ G + 1 :=
    hgammaBound.trans (by linarith)
  have hnormalizationPlus :
      ‖(pintzZetaAFENormalization s)⁻¹‖ ≤ D := by
    dsimp only [D]
    linarith
  have hwInv : ‖w⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hwNorm
  let E := Real.exp (100 * W ^ 2 - 100 * y ^ 2)
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hB16 : 0 ≤ B ^ 16 := by positivity
  have hPoly0 : 0 ≤ ‖z * (1 - z)‖ := norm_nonneg _
  have hGamma0 : 0 ≤ ‖Complex.Gammaℝ z‖ := norm_nonneg _
  have hNormalization0 : 0 ≤ ‖(pintzZetaAFENormalization s)⁻¹‖ := norm_nonneg _
  have hDirichlet0 : 0 ≤ ‖pintzZetaDirichletTerm z n‖ := norm_nonneg _
  have hWInv0 : 0 ≤ ‖w⁻¹‖ := norm_nonneg _
  have hGPlus0 : 0 ≤ G + 1 := by linarith [hG]
  have hD0 : 0 ≤ D := by dsimp only [D]; positivity
  have hAll :
      ‖Complex.exp (100 * w ^ 2)‖ * ‖z * (1 - z)‖ *
          ‖Complex.Gammaℝ z‖ *
          ‖(pintzZetaAFENormalization s)⁻¹‖ *
          ‖pintzZetaDirichletTerm z n‖ * ‖w⁻¹‖ ≤
        E * B ^ 16 * (G + 1) *
          D * 1 * 1 := by
    exact mul_six_le_mul_six hgauss hpoly16 hgammaPlus hnormalizationPlus
      hdirichlet hwInv hPoly0 hGamma0 hNormalization0 hDirichlet0 hWInv0
      hE hB16 hGPlus0 hD0 zero_le_one
  calc
    _ = ‖Complex.exp (100 * w ^ 2)‖ * ‖z * (1 - z)‖ *
          ‖Complex.Gammaℝ z‖ * ‖(pintzZetaAFENormalization s)⁻¹‖ *
          ‖pintzZetaDirichletTerm z n‖ * ‖w⁻¹‖ := by
      simpa only [z] using norm_pintzZetaAFETermContourIntegrand_eq s base n w
    _ ≤ E * B ^ 16 * (G + 1) *
          D * 1 * 1 := hAll
    _ = C * Real.exp (100 * W ^ 2 - 100 * y ^ 2) * B ^ 16 := by
      change E * B ^ 16 * (G + 1) * D * 1 * 1 = (G + 1) * D * E * B ^ 16
      exact mul_four_reorder E (B ^ 16) (G + 1) D
    _ = C * Real.exp (100 * (max q c) ^ 2 - 100 * y ^ 2) *
          (2 + ‖base‖ + max q c + |y|) ^ 16 := rfl

/-- Upper horizontal specialization of the sign-symmetric displacement
bound. -/
theorem exists_pintzZetaAFETerm_horizontal_bound
    (s base : ℂ) {n : ℕ} (hn : n ≠ 0) {q c : ℝ}
    (hq : 0 < q) (hc : 0 < c) (hbase : q < base.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 1 ≤ H → ∀ x ∈ Set.uIcc (-q) c,
      ‖pintzZetaAFETermContourIntegrand s base n
          ((x : ℂ) + (H : ℂ) * I)‖ ≤
        C * Real.exp (100 * (max q c) ^ 2 - 100 * H ^ 2) *
          (2 + ‖base‖ + max q c + H) ^ 16 := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_pintzZetaAFETerm_horizontal_abs_bound s base hn hq hc hbase
  refine ⟨C, hC, ?_⟩
  intro H hH x hx
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  simpa only [abs_of_nonneg hH0] using hbound H (by simpa [abs_of_nonneg hH0]) x hx

/-- Lower horizontal specialization, with the same constant and envelope as
the upper side. -/
theorem exists_pintzZetaAFETerm_horizontal_neg_bound
    (s base : ℂ) {n : ℕ} (hn : n ≠ 0) {q c : ℝ}
    (hq : 0 < q) (hc : 0 < c) (hbase : q < base.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 1 ≤ H → ∀ x ∈ Set.uIcc (-q) c,
      ‖pintzZetaAFETermContourIntegrand s base n
          ((x : ℂ) - (H : ℂ) * I)‖ ≤
        C * Real.exp (100 * (max q c) ^ 2 - 100 * H ^ 2) *
          (2 + ‖base‖ + max q c + H) ^ 16 := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_pintzZetaAFETerm_horizontal_abs_bound s base hn hq hc hbase
  refine ⟨C, hC, ?_⟩
  intro H hH x hx
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  simpa only [ofReal_neg, neg_mul, sub_eq_add_neg, abs_neg, abs_of_nonneg hH0,
    neg_sq] using hbound (-H) (by simpa [abs_of_nonneg hH0]) x hx

#print axioms exists_uniform_norm_GammaR_positive_strip
#print axioms norm_pintzZetaDirichletTerm_le_one
#print axioms exists_pintzZetaAFETerm_horizontal_abs_bound
#print axioms exists_pintzZetaAFETerm_horizontal_bound
#print axioms exists_pintzZetaAFETerm_horizontal_neg_bound

end

end GafniTao
