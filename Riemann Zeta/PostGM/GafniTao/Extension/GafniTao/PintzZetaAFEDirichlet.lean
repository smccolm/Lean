import GafniTao.PintzZetaAFEAssembly
import RiemannZeta.GuthMaynard.HughesYoungAFE

/-!
# Arithmetic opening of the single-zeta AFE

The two right edges in `PintzZetaAFEAssembly` are opened into the ordinary
zeta Dirichlet series.  All statements here are exact: the finite-height
integrals are interchanged with the series by compact uniform domination,
and the final limit is normalized back to `riemannZeta s`.
-/

open Complex Filter MeasureTheory Set TopologicalSpace Topology
open scoped BigOperators Interval LSeries.notation

noncomputable section

namespace GafniTao

open RiemannZeta.GuthMaynard

/-- One term of the ordinary zeta Dirichlet series. -/
noncomputable def pintzZetaDirichletTerm (s : ℂ) (n : ℕ) : ℂ :=
  LSeries.term
    (fun k : ℕ => (ArithmeticFunction.zeta : ArithmeticFunction ℂ) k) s n

theorem summable_pintzZetaDirichletTerm {s : ℂ} (hs : 1 < s.re) :
    Summable (pintzZetaDirichletTerm s) := by
  exact ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs

theorem tsum_pintzZetaDirichletTerm {s : ℂ} (hs : 1 < s.re) :
    ∑' n : ℕ, pintzZetaDirichletTerm s n = riemannZeta s := by
  simpa only [pintzZetaDirichletTerm] using
    ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs

/-- The completed-zeta right-edge integrand after opening the ordinary zeta
Dirichlet series. -/
noncomputable def pintzZetaAFEOpenedContourIntegrand
    (base : ℂ) (c u : ℝ) : ℂ :=
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  let z : ℂ := base + w
  Complex.exp (100 * w ^ 2) *
    (z * (1 - z)) * Complex.Gammaℝ z *
    LSeries
      (fun k : ℕ => (ArithmeticFunction.zeta : ArithmeticFunction ℂ) k) z /
    w

theorem pintzZetaAFEContourIntegrand_eq_opened
    (base : ℂ) (u : ℝ) {c : ℝ}
    (hc : 1 < base.re + c) :
    pintzZetaAFEContourIntegrand base ((c : ℂ) + (u : ℂ) * I) =
      pintzZetaAFEOpenedContourIntegrand base c u := by
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  let z : ℂ := base + w
  have hzre : 1 < z.re := by
    simpa [z, w] using hc
  have hz0 : z ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hz1 : z ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hL :
      LSeries
          (fun k : ℕ => (ArithmeticFunction.zeta : ArithmeticFunction ℂ) k) z =
        riemannZeta z := by
    simpa only [ArithmeticFunction.natCoe_apply] using
      ArithmeticFunction.LSeries_zeta_eq_riemannZeta hzre
  rw [pintzZetaAFEContourIntegrand, pintzZetaAFEContourNumerator,
    completedXiNumerator_eq z hz0 hz1,
    completedRiemannZeta_eq_zeta_mul_GammaR (by linarith : 0 < z.re),
    ← hL]
  simp only [pintzZetaAFEOpenedContourIntegrand, z, w]
  ring

/-- The pole and Gamma normalization which turns the completed xi numerator
back into the ordinary zeta function. -/
noncomputable def pintzZetaAFENormalization (s : ℂ) : ℂ :=
  s * (1 - s) * Complex.Gammaℝ s

theorem pintzZetaAFENormalization_ne_zero {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    pintzZetaAFENormalization s ≠ 0 := by
  unfold pintzZetaAFENormalization
  have hs : s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have h1s : 1 - s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  exact mul_ne_zero (mul_ne_zero hs h1s)
    (Complex.Gammaℝ_ne_zero_of_re_pos hs0)

theorem completedXiNumerator_div_normalization {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    completedXiNumerator s / pintzZetaAFENormalization s = riemannZeta s := by
  have hs : s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have h1s : s ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  rw [completedXiNumerator_eq s hs h1s,
    completedRiemannZeta_eq_zeta_mul_GammaR hs0]
  unfold pintzZetaAFENormalization
  field_simp [hs, sub_ne_zero.mpr h1s.symm,
    Complex.Gammaℝ_ne_zero_of_re_pos hs0]

/-- The non-arithmetic coefficient of one right-edge series, with both
right edges normalized by the original point `s`. -/
noncomputable def pintzZetaAFERightWeight
    (s base : ℂ) (c u : ℝ) : ℂ :=
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  let z : ℂ := base + w
  Complex.exp (100 * w ^ 2) * (z * (1 - z)) * Complex.Gammaℝ z /
    w / pintzZetaAFENormalization s

/-- One integer-indexed term of a normalized right edge. -/
noncomputable def pintzZetaAFERightTerm
    (s base : ℂ) (c u : ℝ) (n : ℕ) : ℂ :=
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  pintzZetaAFERightWeight s base c u *
    pintzZetaDirichletTerm (base + w) n

theorem pintzZetaAFEOpened_div_normalization_eq_tsum
    (s base : ℂ) (u : ℝ) {c : ℝ}
    (hc : 1 < base.re + c) :
    pintzZetaAFEOpenedContourIntegrand base c u /
        pintzZetaAFENormalization s =
      ∑' n : ℕ, pintzZetaAFERightTerm s base c u n := by
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  have hz : 1 < (base + w).re := by simpa [w] using hc
  have hsum : (∑' n : ℕ, pintzZetaAFERightTerm s base c u n) =
      pintzZetaAFERightWeight s base c u *
        (∑' n : ℕ, pintzZetaDirichletTerm (base + w) n) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    simp only [pintzZetaAFERightTerm, w]
  rw [hsum, tsum_pintzZetaDirichletTerm hz]
  have hL :
      LSeries
          (fun k : ℕ => (ArithmeticFunction.zeta : ArithmeticFunction ℂ) k)
          (base + w) = riemannZeta (base + w) := by
    simpa only [ArithmeticFunction.natCoe_apply] using
      ArithmeticFunction.LSeries_zeta_eq_riemannZeta hz
  unfold pintzZetaAFEOpenedContourIntegrand pintzZetaAFERightWeight
  dsimp only [w]
  rw [hL]
  ring

theorem continuous_pintzZetaDirichletTerm_vertical
    (base : ℂ) (c : ℝ) (n : ℕ) :
    Continuous (fun u : ℝ =>
      pintzZetaDirichletTerm
        (base + ((c : ℂ) + (u : ℂ) * I)) n) := by
  by_cases hn : n = 0
  · subst n
    simpa [pintzZetaDirichletTerm] using
      (continuous_const : Continuous (fun _u : ℝ => (0 : ℂ)))
  · simp only [pintzZetaDirichletTerm, LSeries.term_of_ne_zero hn]
    exact continuous_const.div₀
      (continuous_const_cpow_of_ne_zero (n : ℂ)
        (by exact_mod_cast hn) (by fun_prop))
      (fun _u => Complex.cpow_ne_zero_iff.mpr
        (Or.inl (by exact_mod_cast hn)))

theorem continuous_GammaR_pintz_vertical
    (base : ℂ) {c : ℝ} (hc : 0 < base.re + c) :
    Continuous (fun u : ℝ =>
      Complex.Gammaℝ (base + ((c : ℂ) + (u : ℂ) * I))) := by
  rw [continuous_iff_continuousAt]
  intro u
  unfold Complex.Gammaℝ
  apply ContinuousAt.mul
  · exact (continuousAt_const_cpow
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)).comp (by fun_prop)
  · apply (Complex.continuousAt_Gamma _ ?_).comp
    · fun_prop
    · intro m hm
      have hre := congrArg Complex.re hm
      simp at hre
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith

theorem continuous_pintzZetaAFERightWeight
    (s base : ℂ) {c : ℝ} (hc : 0 < base.re + c)
    (hc0 : c ≠ 0) :
    Continuous (pintzZetaAFERightWeight s base c) := by
  let w : ℝ → ℂ := fun u => (c : ℂ) + (u : ℂ) * I
  let z : ℝ → ℂ := fun u => base + w u
  have hw : Continuous w := by dsimp [w]; fun_prop
  have hz : Continuous z := continuous_const.add hw
  have hwne : ∀ u, w u ≠ 0 := by
    intro u hu
    have hre := congrArg Complex.re hu
    simp [w] at hre
    exact hc0 hre
  have hgamma := continuous_GammaR_pintz_vertical base hc
  have hnum : Continuous (fun u =>
      Complex.exp (100 * (w u) ^ 2) *
        (z u * (1 - z u)) * Complex.Gammaℝ (z u)) := by
    fun_prop
  have h := (hnum.div₀ hw hwne).div_const (pintzZetaAFENormalization s)
  simpa only [pintzZetaAFERightWeight, w, z] using h

theorem continuous_pintzZetaAFERightTerm
    (s base : ℂ) {c : ℝ} (hc : 0 < base.re + c)
    (hc0 : c ≠ 0) (n : ℕ) :
    Continuous (fun u : ℝ => pintzZetaAFERightTerm s base c u n) := by
  unfold pintzZetaAFERightTerm
  exact (continuous_pintzZetaAFERightWeight s base hc hc0).mul
    (continuous_pintzZetaDirichletTerm_vertical base c n)

noncomputable def pintzZetaAFERightContinuousMap
    (s base : ℂ) (c : ℝ) (hc : 0 < base.re + c)
    (hc0 : c ≠ 0) (n : ℕ) : C(ℝ, ℂ) :=
  ⟨fun u => pintzZetaAFERightTerm s base c u n,
    continuous_pintzZetaAFERightTerm s base hc hc0 n⟩

theorem norm_pintzZetaDirichletTerm_vertical
    (base : ℂ) (c u : ℝ) (n : ℕ) :
    ‖pintzZetaDirichletTerm
        (base + ((c : ℂ) + (u : ℂ) * I)) n‖ =
      ‖pintzZetaDirichletTerm (base + (c : ℂ)) n‖ := by
  simp only [pintzZetaDirichletTerm, LSeries.norm_term_eq]
  congr 2
  simp

theorem summable_pintzZetaAFERight_restrict_norm
    (s base : ℂ) (c H : ℝ) (hc : 1 < base.re + c) (hc0 : c ≠ 0) :
    Summable (fun n : ℕ =>
      ‖(pintzZetaAFERightContinuousMap s base c (by linarith)
          hc0 n).restrict
        (⟨Set.uIcc (-H) H, isCompact_uIcc⟩ : Compacts ℝ)‖) := by
  let W : ℝ → ℝ := fun u => ‖pintzZetaAFERightWeight s base c u‖
  have hWcont : Continuous W :=
    (continuous_pintzZetaAFERightWeight s base (by linarith) hc0).norm
  obtain ⟨u₀, hu₀, hmax⟩ := isCompact_uIcc.exists_isMaxOn
    nonempty_uIcc hWcont.continuousOn
  let C : ℝ := 1 + W u₀
  have hC : 0 < C := by dsimp [C]; positivity
  have hseries : Summable (pintzZetaDirichletTerm (base + (c : ℂ))) :=
    summable_pintzZetaDirichletTerm (by simpa using hc)
  have hmajor : Summable (fun n : ℕ =>
      C * ‖pintzZetaDirichletTerm (base + (c : ℂ)) n‖) :=
    (summable_norm_iff.mpr hseries).mul_left C
  apply hmajor.of_nonneg_of_le (fun n => norm_nonneg _)
  intro n
  apply (ContinuousMap.norm_le
    ((pintzZetaAFERightContinuousMap s base c (by linarith)
      hc0 n).restrict
      (⟨Set.uIcc (-H) H, isCompact_uIcc⟩ : Compacts ℝ))
    (by positivity)).2
  intro u
  change ‖pintzZetaAFERightTerm s base c u.1 n‖ ≤ _
  rw [pintzZetaAFERightTerm, norm_mul,
    norm_pintzZetaDirichletTerm_vertical]
  have hWeight : W u.1 ≤ C := (hmax u.2).trans (by dsimp [C]; linarith)
  dsimp only [W] at hWeight
  gcongr

theorem tsum_intervalIntegral_pintzZetaAFERightTerm
    (s base : ℂ) (c H : ℝ) (hc : 1 < base.re + c) (hc0 : c ≠ 0) :
    ∑' n : ℕ, ∫ u in -H..H, pintzZetaAFERightTerm s base c u n =
      ∫ u in -H..H, ∑' n : ℕ, pintzZetaAFERightTerm s base c u n := by
  simpa only [pintzZetaAFERightContinuousMap, ContinuousMap.coe_mk] using
    (intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
      (summable_pintzZetaAFERight_restrict_norm s base c H hc hc0))

theorem vIntegral_pintzZetaAFE_div_normalization_eq_tsum
    (s base : ℂ) (c H : ℝ) (hc : 1 < base.re + c) (hc0 : c ≠ 0) :
    VIntegral' (pintzZetaAFEContourIntegrand base) c (-H) H /
        pintzZetaAFENormalization s =
      (1 / (2 * Real.pi : ℂ)) *
        ∑' n : ℕ, ∫ u in -H..H,
          pintzZetaAFERightTerm s base c u n := by
  have hint :
      (∫ u in -H..H,
          pintzZetaAFEContourIntegrand base
            ((c : ℂ) + (u : ℂ) * I)) =
        ∫ u in -H..H, pintzZetaAFEOpenedContourIntegrand base c u := by
    apply intervalIntegral.integral_congr
    intro u _hu
    exact pintzZetaAFEContourIntegrand_eq_opened base u hc
  calc
    VIntegral' (pintzZetaAFEContourIntegrand base) c (-H) H /
        pintzZetaAFENormalization s =
      (1 / (2 * Real.pi : ℂ)) *
        ∫ u in -H..H,
          pintzZetaAFEOpenedContourIntegrand base c u /
            pintzZetaAFENormalization s := by
      unfold VIntegral' VIntegral
      simp only [smul_eq_mul]
      rw [intervalIntegral.integral_div, hint]
      field_simp [Real.pi_ne_zero]
    _ = (1 / (2 * Real.pi : ℂ)) *
        ∑' n : ℕ, ∫ u in -H..H,
          pintzZetaAFERightTerm s base c u n := by
      rw [tsum_intervalIntegral_pintzZetaAFERightTerm s base c H hc hc0]
      apply congrArg
      apply intervalIntegral.integral_congr
      intro u _hu
      exact pintzZetaAFEOpened_div_normalization_eq_tsum s base u hc

/-- Exact arithmetic form of the single-zeta AFE.  The two series correspond
to the original and functional-equation sides respectively. -/
theorem tendsto_pintzZetaAFERightSeries
    (s : ℂ) {c : ℝ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hc₁ : 1 < s.re + c) (hc₂ : 1 < (1 - s).re + c) :
    Tendsto (fun H : ℝ =>
      (1 / (2 * Real.pi : ℂ)) *
          ∑' n : ℕ, (∫ u in -H..H,
            pintzZetaAFERightTerm s s c u n) +
        (1 / (2 * Real.pi : ℂ)) *
          ∑' n : ℕ, (∫ u in -H..H,
            pintzZetaAFERightTerm s (1 - s) c u n))
      atTop (nhds (riemannZeta s)) := by
  have hc0 : c ≠ 0 := by linarith
  have hafe := pintzZetaAFE_vertical_limit_native s (show 0 < c by linarith)
  have hdiv := hafe.div_const (pintzZetaAFENormalization s)
  rw [completedXiNumerator_div_normalization hs0 hs1] at hdiv
  apply hdiv.congr'
  exact Filter.Eventually.of_forall fun H => by
    change
      (VIntegral' (pintzZetaAFEContourIntegrand s) c (-H) H +
          VIntegral' (pintzZetaAFEContourIntegrand (1 - s)) c (-H) H) /
          pintzZetaAFENormalization s = _
    rw [add_div,
      vIntegral_pintzZetaAFE_div_normalization_eq_tsum s s c H hc₁ hc0,
      vIntegral_pintzZetaAFE_div_normalization_eq_tsum s (1 - s) c H hc₂ hc0]

#print axioms pintzZetaAFEContourIntegrand_eq_opened
#print axioms completedXiNumerator_div_normalization
#print axioms pintzZetaAFEOpened_div_normalization_eq_tsum
#print axioms vIntegral_pintzZetaAFE_div_normalization_eq_tsum
#print axioms tendsto_pintzZetaAFERightSeries

end GafniTao
