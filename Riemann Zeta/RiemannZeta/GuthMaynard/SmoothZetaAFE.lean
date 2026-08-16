import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaHadamard
import RiemannZeta.External.PNT.ResidueCalcOnRectangles
import RiemannZeta.External.PNT.ZetaBoundsUpstream
import RiemannZeta.GuthMaynard.GammaPairBound
import RiemannZeta.GuthMaynard.TwistedDiagonal

open Complex Filter MeasureTheory Set Topology
open ArithmeticFunction
open scoped ArithmeticFunction.zeta ArithmeticFunction.sigma BigOperators Interval
  LSeries.notation

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# The completed-zeta contour for the smooth fourth-moment AFE

This file formalizes the source entry to Hughes--Young Proposition 2.1 in
the unshifted case.  The pole-cancelling completion below is entire, has the
functional-equation symmetry required to reflect the left side of the
contour, and retains the exact zeta factors on the critical line.
-/

/-- The Dirichlet convolution of the arithmetic zeta function with itself is
the ordinary divisor-count function.  This is the small, dependency-clean
part of the newer PNT+ `zeta_mul_zeta` implementation. -/
theorem arithmeticZeta_mul_self_eq_sigma_zero :
    (ζ : ArithmeticFunction ℕ) * ζ = ArithmeticFunction.sigma 0 := by
  ext n
  simp only [ArithmeticFunction.mul_apply, ArithmeticFunction.zeta_apply,
    ArithmeticFunction.sigma_apply, mul_ite,
    mul_zero, mul_one, pow_zero, Finset.sum_const, smul_eq_mul]
  have key : ∀ x ∈ n.divisorsAntidiagonal,
      (if x.2 = 0 then 0 else if x.1 = 0 then 0 else 1) = 1 := by
    intro ⟨a, b⟩ hx
    have h := Nat.mem_divisorsAntidiagonal.mp hx
    simp [mul_ne_zero_iff.mp (h.1 ▸ h.2)]
  simp_rw [Finset.sum_congr rfl key, Finset.card_eq_sum_ones, Finset.sum_const]
  simp only [smul_eq_mul, mul_one, ← Nat.map_div_right_divisors]
  exact Finset.card_map
    { toFun := fun d => (d, n / d), inj' := fun x y h => congrArg Prod.fst h }

/-- The exact divisor-series expansion needed when the right AFE contour is
opened.  It is proved locally so the result does not import unrelated admitted
declarations from the newer PNT+ development. -/
theorem riemannZeta_sq_eq_divisorLSeries {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s ^ 2 =
      LSeries (fun n : ℕ => (n.divisors.card : ℂ)) s := by
  have hNat : LSeries (↗((ζ : ArithmeticFunction ℕ) * ζ)) s =
      LSeries (↗((ζ : ArithmeticFunction ℂ) * ζ)) s := by
    congr 1
    ext n
    simp only [← ArithmeticFunction.natCoe_mul, ArithmeticFunction.natCoe_apply]
  have hMul : LSeries (↗((ζ : ArithmeticFunction ℂ) * ζ)) s =
      LSeries (↗ζ) s * LSeries (↗ζ) s :=
    ArithmeticFunction.LSeries_mul'
      (ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs)
      (ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs)
  calc
    riemannZeta s ^ 2 = LSeries (↗ζ) s * LSeries (↗ζ) s := by
      rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs, pow_two]
    _ = LSeries (↗((ζ : ArithmeticFunction ℂ) * ζ)) s := hMul.symm
    _ = LSeries (↗((ζ : ArithmeticFunction ℕ) * ζ)) s := hNat.symm
    _ = LSeries (↗(ArithmeticFunction.sigma 0)) s := by
      rw [arithmeticZeta_mul_self_eq_sigma_zero]
    _ = LSeries (fun n : ℕ => (n.divisors.card : ℂ)) s := by
      apply congrArg (fun f : ℕ → ℂ => LSeries f s)
      funext n
      simp [ArithmeticFunction.sigma_zero_apply]

/-- Absolute summability of the divisor Dirichlet series on the same right
half-plane on which `riemannZeta_sq_eq_divisorLSeries` opens the zeta square.
This is the convergence datum needed for the Hughes--Young Fubini steps; the
value identity alone is not enough to justify rearranging the two series. -/
theorem divisorLSeries_summable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n : ℕ => (n.divisors.card : ℂ)) s := by
  have hz : LSeriesSummable (⇑(ζ : ArithmeticFunction ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  have hconv : LSeriesSummable (⇑((ζ : ArithmeticFunction ℂ) * ζ)) s :=
    ArithmeticFunction.LSeriesSummable_mul hz hz
  apply (LSeriesSummable_congr s (f := ⇑((ζ : ArithmeticFunction ℂ) * ζ))
    (g := fun n : ℕ => (n.divisors.card : ℂ)) ?_).mp hconv
  intro n hn
  rw [← ArithmeticFunction.natCoe_mul]
  change (((((ζ : ArithmeticFunction ℕ) * ζ) n : ℕ) : ℂ)) = _
  rw [arithmeticZeta_mul_self_eq_sigma_zero]
  simp [ArithmeticFunction.sigma_zero_apply]

/-- The entire Riemann xi numerator, normalized so that away from the two
poles it is `s * (1 - s) * completedRiemannZeta s`. -/
noncomputable def completedXiNumerator (s : ℂ) : ℂ :=
  s * (1 - s) * completedRiemannZeta₀ s - 1

/-- The pole-cancelled numerator is exactly `-2` times Riemann's entire xi
function.  This identifies the local contour normalization with the audited
PNT+ order-one theorem for `riemannXi`. -/
theorem completedXiNumerator_eq_neg_two_mul_riemannXi (s : ℂ) :
    completedXiNumerator s = -2 * riemannXi s := by
  simp [completedXiNumerator, riemannXi]
  ring

/-- Uniform order-`3/2` bound for the pole-cancelled numerator.  The exponent
is deliberately below the quadratic Gaussian exponent used by the AFE. -/
theorem exists_completedXiNumerator_order_three_halves_bound :
    ∃ C > 0, ∀ s : ℂ,
      ‖completedXiNumerator s‖ ≤
        Real.exp (C * (1 + ‖s‖) ^ (3 / 2 : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ :=
    riemannXi_entireOfOrderAtMost_one.exists_bound
      (show (0 : ℝ) < 1 / 2 by norm_num)
  refine ⟨C + 1, by linarith, ?_⟩
  intro s
  rw [completedXiNumerator_eq_neg_two_mul_riemannXi, norm_mul]
  have hbase : 1 ≤ (1 + ‖s‖) ^ (3 / 2 : ℝ) :=
    Real.one_le_rpow (by linarith [norm_nonneg s]) (by norm_num)
  have hlog2 : Real.log 2 ≤ (1 : ℝ) := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    nlinarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    ‖(-2 : ℂ)‖ * ‖riemannXi s‖
        ≤ 2 * Real.exp (C * (1 + ‖s‖) ^ (3 / 2 : ℝ)) := by
          norm_num
          convert hbound s using 1
          norm_num
    _ = Real.exp (Real.log 2 + C * (1 + ‖s‖) ^ (3 / 2 : ℝ)) := by
          rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ Real.exp ((C + 1) * (1 + ‖s‖) ^ (3 / 2 : ℝ)) := by
          apply Real.exp_le_exp.mpr
          nlinarith

/-- A quadratic Gaussian dominates every translated order-`3/2`
exponential.  This real-variable limit is the quantitative engine behind
removing the horizontal sides of the AFE rectangle. -/
theorem tendsto_exp_const_sub_sq_add_three_halves
    (A C D : ℝ) :
    Tendsto
      (fun H : ℝ => Real.exp
        (D - H ^ 2 + C * (A + H) ^ (3 / 2 : ℝ)))
      atTop (𝓝 0) := by
  have hAdiv : Tendsto (fun H : ℝ => A / H) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hratioBase : Tendsto (fun H : ℝ => (A + H) / H) atTop (𝓝 1) := by
    have heq : (fun H : ℝ => A / H + 1) =ᶠ[atTop]
        (fun H : ℝ => (A + H) / H) := by
      filter_upwards [eventually_ne_atTop (0 : ℝ)] with H hH
      field_simp
    simpa using (hAdiv.add_const 1).congr' heq
  have hratioPow : Tendsto
      (fun H : ℝ => ((A + H) / H) ^ (3 / 2 : ℝ)) atTop (𝓝 1) := by
    simpa using hratioBase.rpow_const (Or.inl one_ne_zero)
  have hhalf : Tendsto (fun H : ℝ => H ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
    simpa using tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 2 by norm_num)
  have hsmall : Tendsto
      (fun H : ℝ => ((A + H) / H) ^ (3 / 2 : ℝ) * H ^ (-(1 / 2 : ℝ)))
      atTop (𝓝 0) := by
    simpa using hratioPow.mul hhalf
  have hquot : Tendsto
      (fun H : ℝ => (A + H) ^ (3 / 2 : ℝ) / H ^ 2)
      atTop (𝓝 0) := by
    apply hsmall.congr'
    filter_upwards [eventually_gt_atTop (max 0 (-A))] with H hH
    have hHpos : 0 < H := lt_of_le_of_lt (le_max_left _ _) hH
    have hAHpos : 0 < A + H := by
      have : -A < H := lt_of_le_of_lt (le_max_right _ _) hH
      linarith
    rw [Real.div_rpow hAHpos.le hHpos.le]
    rw [Real.rpow_neg hHpos.le]
    have hpow : H ^ (3 / 2 : ℝ) * H ^ (1 / 2 : ℝ) = H ^ 2 := by
      rw [← Real.rpow_add hHpos]
      norm_num [Real.rpow_two]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hHpos (3 / 2 : ℝ)),
      ne_of_gt (Real.rpow_pos_of_pos hHpos (1 / 2 : ℝ))]
    exact hpow.symm
  have hDquot : Tendsto (fun H : ℝ => D / H ^ 2) atTop (𝓝 0) := by
    have hsq : Tendsto (fun H : ℝ => H ^ 2) atTop atTop := by
      apply (tendsto_rpow_atTop (show (0 : ℝ) < 2 by norm_num)).congr'
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
      rw [Real.rpow_two]
    exact tendsto_const_nhds.div_atTop hsq
  have hbracket : Tendsto
      (fun H : ℝ => -1 +
        C * ((A + H) ^ (3 / 2 : ℝ) / H ^ 2) + D / H ^ 2)
      atTop (𝓝 (-1)) := by
    convert (tendsto_const_nhds.add (tendsto_const_nhds.mul hquot)).add hDquot using 1
    all_goals ring_nf
  have hsq : Tendsto (fun H : ℝ => H ^ 2) atTop atTop := by
    apply (tendsto_rpow_atTop (show (0 : ℝ) < 2 by norm_num)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
    rw [Real.rpow_two]
  have hexponent : Tendsto
      (fun H : ℝ => D - H ^ 2 + C * (A + H) ^ (3 / 2 : ℝ))
      atTop atBot := by
    have hprod := hsq.atTop_mul_neg (show (-1 : ℝ) < 0 by norm_num) hbracket
    apply hprod.congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with H hH
    field_simp
    ring
  exact Real.tendsto_exp_atBot.comp hexponent

theorem completedXiNumerator_eq (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    completedXiNumerator s = s * (1 - s) * completedRiemannZeta s := by
  rw [completedRiemannZeta_eq]
  unfold completedXiNumerator
  have h1m : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  field_simp [hs0, h1m]
  ring

theorem completedXiNumerator_one_sub (s : ℂ) :
    completedXiNumerator (1 - s) = completedXiNumerator s := by
  unfold completedXiNumerator
  rw [completedRiemannZeta₀_one_sub]
  ring

theorem differentiable_completedXiNumerator :
    Differentiable ℂ completedXiNumerator := by
  unfold completedXiNumerator
  have hpoly : Differentiable ℂ (fun s : ℂ => s * (1 - s)) := by fun_prop
  exact (hpoly.mul differentiable_completedZeta₀).sub
    (differentiable_const (c := (1 : ℂ)))

/-- The two critical-line points used in the unshifted fourth moment. -/
noncomputable def afeCriticalPoint (t : ℝ) : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I

@[simp] theorem one_sub_afeCriticalPoint (t : ℝ) :
    1 - afeCriticalPoint t = afeCriticalPoint (-t) := by
  unfold afeCriticalPoint
  push_cast
  ring

theorem afeCriticalPoint_ne_zero (t : ℝ) : afeCriticalPoint t ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  norm_num [afeCriticalPoint] at this

theorem afeCriticalPoint_ne_one (t : ℝ) : afeCriticalPoint t ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  norm_num [afeCriticalPoint] at this

/-- Polynomial normalization which cancels all four completed-zeta poles in
the unshifted Hughes--Young contour. -/
noncomputable def afePoleNormalization (t : ℝ) : ℂ :=
  ((afeCriticalPoint t) * (1 - afeCriticalPoint t) *
    (afeCriticalPoint (-t)) * (1 - afeCriticalPoint (-t))) ^ 2

theorem afePoleNormalization_ne_zero (t : ℝ) : afePoleNormalization t ≠ 0 := by
  unfold afePoleNormalization
  apply pow_ne_zero
  repeat' apply mul_ne_zero
  · exact afeCriticalPoint_ne_zero t
  · exact sub_ne_zero.mpr (afeCriticalPoint_ne_one t).symm
  · exact afeCriticalPoint_ne_zero (-t)
  · exact sub_ne_zero.mpr (afeCriticalPoint_ne_one (-t)).symm

/-- Entire pole-cancelled contour numerator.  The even Gaussian is a
stronger member of the standard Hughes--Young admissible kernel family; its
fixed strength `100` absorbs the uniform paired Gamma growth proved below.
The xi numerators encode the four completed zeta factors without leaving
meromorphic singularities. -/
noncomputable def smoothZetaSqContourNumerator (t : ℝ) (w : ℂ) : ℂ :=
  Complex.exp (100 * w ^ 2) *
    completedXiNumerator (afeCriticalPoint t + w) ^ 2 *
    completedXiNumerator (afeCriticalPoint (-t) + w) ^ 2 /
      afePoleNormalization t

theorem differentiable_smoothZetaSqContourNumerator (t : ℝ) :
    Differentiable ℂ (smoothZetaSqContourNumerator t) := by
  unfold smoothZetaSqContourNumerator
  have hplus : Differentiable ℂ (fun w : ℂ => afeCriticalPoint t + w) := by fun_prop
  have hminus : Differentiable ℂ (fun w : ℂ => afeCriticalPoint (-t) + w) := by fun_prop
  have hxiPlus : Differentiable ℂ
      (fun w : ℂ => completedXiNumerator (afeCriticalPoint t + w)) :=
    fun w => differentiable_completedXiNumerator.differentiableAt.comp w (hplus w)
  have hxiMinus : Differentiable ℂ
      (fun w : ℂ => completedXiNumerator (afeCriticalPoint (-t) + w)) :=
    fun w => differentiable_completedXiNumerator.differentiableAt.comp w (hminus w)
  fun_prop (disch := assumption)

theorem smoothZetaSqContourNumerator_neg (t : ℝ) (w : ℂ) :
    smoothZetaSqContourNumerator t (-w) =
      smoothZetaSqContourNumerator t w := by
  unfold smoothZetaSqContourNumerator
  rw [show afeCriticalPoint t + -w =
      1 - (afeCriticalPoint (-t) + w) by
        unfold afeCriticalPoint
        push_cast
        ring,
    show afeCriticalPoint (-t) + -w =
      1 - (afeCriticalPoint t + w) by
        unfold afeCriticalPoint
        push_cast
        ring,
    completedXiNumerator_one_sub, completedXiNumerator_one_sub]
  simp only [neg_sq]
  ring

/-- At the central point the pole-cancelled numerator is exactly the product
of the four completed zeta factors. -/
theorem smoothZetaSqContourNumerator_zero (t : ℝ) :
    smoothZetaSqContourNumerator t 0 =
      completedRiemannZeta (afeCriticalPoint t) ^ 2 *
        completedRiemannZeta (afeCriticalPoint (-t)) ^ 2 := by
  simp only [smoothZetaSqContourNumerator, zero_pow (by decide : 2 ≠ 0), mul_zero,
    exp_zero, one_mul, add_zero]
  rw [completedXiNumerator_eq _
      (afeCriticalPoint_ne_zero t) (afeCriticalPoint_ne_one t),
    completedXiNumerator_eq _ (afeCriticalPoint_ne_zero (-t))
      (afeCriticalPoint_ne_one (-t))]
  rw [div_eq_iff (afePoleNormalization_ne_zero t)]
  unfold afePoleNormalization
  ring

/-- The odd Cauchy integrand obtained from the even AFE numerator. -/
noncomputable def smoothZetaSqContourIntegrand (t : ℝ) (w : ℂ) : ℂ :=
  smoothZetaSqContourNumerator t w / w

theorem smoothZetaSqContourIntegrand_neg (t : ℝ) (w : ℂ) :
    smoothZetaSqContourIntegrand t (-w) =
      -smoothZetaSqContourIntegrand t w := by
  unfold smoothZetaSqContourIntegrand
  rw [smoothZetaSqContourNumerator_neg]
  by_cases hw : w = 0
  · simp [hw]
  · field_simp

theorem one_add_norm_afeCriticalPoint_add_horizontal_le
    (t c H x : ℝ) (hc : 0 ≤ c) (hH : 0 ≤ H)
    (hx : x ∈ Set.uIcc (-c) c) :
    1 + ‖afeCriticalPoint t + ((x : ℂ) + (H : ℂ) * I)‖ ≤
      2 + |t| + c + H := by
  have hxc : |x| ≤ c := by
    rw [uIcc_of_le (by linarith : -c ≤ c)] at hx
    exact abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
  have hcritical : ‖afeCriticalPoint t‖ ≤ 1 / 2 + |t| := by
    calc
      ‖afeCriticalPoint t‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖(t : ℂ) * I‖ := by
        unfold afeCriticalPoint
        exact norm_add_le _ _
      _ = 1 / 2 + |t| := by simp [Real.norm_eq_abs]
  have hhorizontal : ‖(x : ℂ) + (H : ℂ) * I‖ ≤ c + H := by
    calc
      ‖(x : ℂ) + (H : ℂ) * I‖ ≤ ‖(x : ℂ)‖ + ‖(H : ℂ) * I‖ := norm_add_le _ _
      _ = |x| + H := by simp [Real.norm_eq_abs, abs_of_nonneg hH]
      _ ≤ c + H := by simpa [add_comm] using add_le_add_right hxc H
  calc
    1 + ‖afeCriticalPoint t + ((x : ℂ) + (H : ℂ) * I)‖
        ≤ 1 + (‖afeCriticalPoint t‖ + ‖(x : ℂ) + (H : ℂ) * I‖) := by
          gcongr
          exact norm_add_le _ _
    _ ≤ 1 + ((1 / 2 + |t|) + (c + H)) := by gcongr
    _ ≤ 2 + |t| + c + H := by norm_num; linarith

/-- Uniform pointwise bound on the top horizontal AFE edge. -/
theorem exists_smoothZetaSqContourIntegrand_horizontal_bound
    (t c : ℝ) (hc : 0 ≤ c) :
    ∃ C : ℝ, C > 0 ∧ ∀ H : ℝ, H ≥ 1 → ∀ x ∈ Set.uIcc (-c) c,
      ‖smoothZetaSqContourIntegrand t ((x : ℂ) + (H : ℂ) * I)‖ ≤
        ‖(afePoleNormalization t)⁻¹‖ *
          Real.exp (100 * c ^ 2 - H ^ 2 +
            4 * C * (2 + |t| + c + H) ^ (3 / 2 : ℝ)) := by
  obtain ⟨C, hC, hxi⟩ := exists_completedXiNumerator_order_three_halves_bound
  refine ⟨C, hC, ?_⟩
  intro H hH x hx
  have hH0 : 0 ≤ H := le_trans (by norm_num) hH
  have hargPlus := one_add_norm_afeCriticalPoint_add_horizontal_le
    t c H x hc hH0 hx
  have hargMinus := one_add_norm_afeCriticalPoint_add_horizontal_le
    (-t) c H x hc hH0 hx
  have hpowPlus :
      (1 + ‖afeCriticalPoint t + ((x : ℂ) + (H : ℂ) * I)‖) ^ (3 / 2 : ℝ) ≤
        (2 + |t| + c + H) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hargPlus (by norm_num)
  have hpowMinus :
      (1 + ‖afeCriticalPoint (-t) + ((x : ℂ) + (H : ℂ) * I)‖) ^ (3 / 2 : ℝ) ≤
        (2 + |t| + c + H) ^ (3 / 2 : ℝ) := by
    have hrewrite : 2 + |-t| + c + H = 2 + |t| + c + H := by simp
    rw [hrewrite] at hargMinus
    exact Real.rpow_le_rpow (by positivity) hargMinus (by norm_num)
  have hxiPlus :
      ‖completedXiNumerator
        (afeCriticalPoint t + ((x : ℂ) + (H : ℂ) * I))‖ ≤
        Real.exp (C * (2 + |t| + c + H) ^ (3 / 2 : ℝ)) :=
    (hxi _).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hpowPlus hC.le))
  have hxiMinus :
      ‖completedXiNumerator
        (afeCriticalPoint (-t) + ((x : ℂ) + (H : ℂ) * I))‖ ≤
        Real.exp (C * (2 + |t| + c + H) ^ (3 / 2 : ℝ)) :=
    (hxi _).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hpowMinus hC.le))
  have hxabs : |x| ≤ c := by
    rw [uIcc_of_le (by linarith : -c ≤ c)] at hx
    exact abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
  have hxsq : x ^ 2 ≤ c ^ 2 := by
    have hsquare := mul_self_le_mul_self (abs_nonneg x) hxabs
    calc
      x ^ 2 = |x| ^ 2 := by rw [sq_abs]
      _ ≤ c ^ 2 := by simpa only [pow_two] using hsquare
  have hgauss :
      ‖Complex.exp (100 * (((x : ℂ) + (H : ℂ) * I) ^ 2))‖ ≤
        Real.exp (100 * c ^ 2 - H ^ 2) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hre : ((((x : ℂ) + (H : ℂ) * I) ^ 2).re) = x ^ 2 - H ^ 2 := by
      simp [pow_two, mul_re, mul_im]
    norm_num [mul_re, hre]
    nlinarith [sq_nonneg H]
  have hwNorm : 1 ≤ ‖(x : ℂ) + (H : ℂ) * I‖ := by
    have himle := Complex.abs_im_le_norm ((x : ℂ) + (H : ℂ) * I)
    have himle' : H ≤ ‖(x : ℂ) + (H : ℂ) * I‖ := by
      simpa [abs_of_nonneg hH0] using himle
    linarith
  unfold smoothZetaSqContourIntegrand smoothZetaSqContourNumerator
  rw [norm_div, norm_div, norm_mul, norm_mul, norm_pow, norm_pow]
  have hnum :
      ‖Complex.exp (100 * (((x : ℂ) + (H : ℂ) * I) ^ 2))‖ *
          ‖completedXiNumerator
            (afeCriticalPoint t + ((x : ℂ) + (H : ℂ) * I))‖ ^ 2 *
          ‖completedXiNumerator
            (afeCriticalPoint (-t) + ((x : ℂ) + (H : ℂ) * I))‖ ^ 2 ≤
        Real.exp (100 * c ^ 2 - H ^ 2 +
          4 * C * (2 + |t| + c + H) ^ (3 / 2 : ℝ)) := by
    calc
      _ ≤ Real.exp (100 * c ^ 2 - H ^ 2) *
          Real.exp (C * (2 + |t| + c + H) ^ (3 / 2 : ℝ)) ^ 2 *
          Real.exp (C * (2 + |t| + c + H) ^ (3 / 2 : ℝ)) ^ 2 := by
            gcongr
      _ = _ := by
        let q := C * (2 + |t| + c + H) ^ (3 / 2 : ℝ)
        have hq : Real.exp q ^ 2 = Real.exp (2 * q) := by
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring
        change Real.exp (100 * c ^ 2 - H ^ 2) * Real.exp q ^ 2 * Real.exp q ^ 2 = _
        rw [hq, ← Real.exp_add, ← Real.exp_add]
        congr 1
        dsimp [q]
        ring
  calc
    _ ≤ (Real.exp (100 * c ^ 2 - H ^ 2 +
          4 * C * (2 + |t| + c + H) ^ (3 / 2 : ℝ)) /
        ‖afePoleNormalization t‖) / 1 := by
      gcongr
    _ = ‖(afePoleNormalization t)⁻¹‖ *
          Real.exp (100 * c ^ 2 - H ^ 2 +
            4 * C * (2 + |t| + c + H) ^ (3 / 2 : ℝ)) := by
      rw [norm_inv]
      field_simp [norm_ne_zero_iff.mpr (afePoleNormalization_ne_zero t)]

/-- The Gaussian removes the top horizontal side of the AFE rectangle. -/
theorem tendsto_hIntegral_smoothZetaSq_top_zero
    (t c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun H : ℝ =>
      HIntegral (smoothZetaSqContourIntegrand t) (-c) c H)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_smoothZetaSqContourIntegrand_horizontal_bound t c hc
  let A : ℝ := 2 + |t| + c
  let K : ℝ := ‖(afePoleNormalization t)⁻¹‖
  let envelope : ℝ → ℝ := fun H =>
    K * Real.exp (100 * c ^ 2 - H ^ 2 + 4 * C * (A + H) ^ (3 / 2 : ℝ))
  have henv0 : Tendsto envelope atTop (𝓝 0) := by
    unfold envelope
    have hraw := tendsto_exp_const_sub_sq_add_three_halves A (4 * C) (100 * c ^ 2)
    simpa only [mul_zero] using Tendsto.const_mul K hraw
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (show ∀ᶠ H : ℝ in atTop,
      ‖HIntegral (smoothZetaSqContourIntegrand t) (-c) c H‖ ≤
        envelope H * |c - (-c)| by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
      unfold HIntegral
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      have hx' : x ∈ Set.uIcc (-c) c := Set.uIoc_subset_uIcc hx
      simpa [envelope, A, K, add_assoc] using hbound H hH x hx')
  simpa using henv0.mul_const |c - (-c)|

theorem tendsto_hIntegral'_smoothZetaSq_top_zero
    (t c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun H : ℝ =>
      HIntegral' (smoothZetaSqContourIntegrand t) (-c) c H)
      atTop (𝓝 0) := by
  unfold HIntegral'
  simpa using (tendsto_hIntegral_smoothZetaSq_top_zero t c hc).const_smul
    (1 / (2 * Real.pi * I))

theorem hIntegral_smoothZetaSq_bottom (t : ℝ) (c H : ℝ) :
    HIntegral (smoothZetaSqContourIntegrand t) (-c) c (-H) =
      -HIntegral (smoothZetaSqContourIntegrand t) (-c) c H := by
  let f := smoothZetaSqContourIntegrand t
  have hpoint : ∀ x : ℝ,
      f ((-x : ℝ) + (H : ℂ) * I) = -f ((x : ℂ) + (-H : ℂ) * I) := by
    intro x
    have harg : ((-x : ℝ) : ℂ) + (H : ℂ) * I =
        -((x : ℂ) + (-H : ℂ) * I) := by push_cast; ring
    rw [harg]
    exact smoothZetaSqContourIntegrand_neg t _
  have hcomp := intervalIntegral.integral_comp_neg
    (f := fun x : ℝ => f ((x : ℂ) + (H : ℂ) * I))
    (a := -c) (b := c)
  simp only [neg_neg] at hcomp
  change (∫ x in -c..c, f ((x : ℂ) + ((-H : ℝ) : ℂ) * I)) =
    -(∫ x in -c..c, f ((x : ℂ) + (H : ℂ) * I))
  calc
    (∫ x in -c..c, f ((x : ℂ) + ((-H : ℝ) : ℂ) * I)) =
        -∫ x in -c..c, f (((-x : ℝ) : ℂ) + (H : ℂ) * I) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro x _hx
      simpa only [ofReal_neg, neg_neg] using (congrArg Neg.neg (hpoint x)).symm
    _ = -∫ x in -c..c, f ((x : ℂ) + (H : ℂ) * I) := by rw [hcomp]

theorem vIntegral_smoothZetaSq_left (t : ℝ) (c H : ℝ) :
    VIntegral (smoothZetaSqContourIntegrand t) (-c) (-H) H =
      -VIntegral (smoothZetaSqContourIntegrand t) c (-H) H := by
  let f := smoothZetaSqContourIntegrand t
  have hpoint : ∀ y : ℝ,
      f (((-c : ℝ) : ℂ) + (y : ℂ) * I) =
        -f ((c : ℂ) + ((-y : ℝ) : ℂ) * I) := by
    intro y
    have harg : (((-c : ℝ) : ℂ) + (y : ℂ) * I) =
        -((c : ℂ) + ((-y : ℝ) : ℂ) * I) := by push_cast; ring
    rw [harg]
    exact smoothZetaSqContourIntegrand_neg t _
  have hcomp := intervalIntegral.integral_comp_neg
    (f := fun y : ℝ => f ((c : ℂ) + (y : ℂ) * I))
    (a := -H) (b := H)
  simp only [neg_neg] at hcomp
  have hraw :
    (∫ y in -H..H, f (((-c : ℝ) : ℂ) + (y : ℂ) * I)) =
        -∫ y in -H..H, f ((c : ℂ) + ((-y : ℝ) : ℂ) * I) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro y _hy
      simpa only [ofReal_neg] using hpoint y
  have hraw' :
      (∫ y in -H..H, f (((-c : ℝ) : ℂ) + (y : ℂ) * I)) =
        -(∫ y in -H..H, f ((c : ℂ) + (y : ℂ) * I)) := by
    calc
      _ = -∫ y in -H..H, f ((c : ℂ) + ((-y : ℝ) : ℂ) * I) := hraw
      _ = _ := by rw [hcomp]
  unfold VIntegral
  rw [hraw']
  simp [f]

/-- Finite-rectangle Cauchy identity underlying the smooth AFE.  This is an
exact contour theorem: the only pole is the displayed `1 / w`, and its
residue is the completed fourth moment at height `t`. -/
theorem smoothZetaSq_finiteRectangle (t : ℝ) {c H : ℝ}
    (hc : 0 < c) (hH : 0 < H) :
    RectangleIntegral'
        (fun w : ℂ => smoothZetaSqContourNumerator t w / w)
        ((-c : ℂ) - (H : ℂ) * I) ((c : ℂ) + (H : ℂ) * I) =
      completedRiemannZeta (afeCriticalPoint t) ^ 2 *
        completedRiemannZeta (afeCriticalPoint (-t)) ^ 2 := by
  let F : ℂ → ℂ := smoothZetaSqContourNumerator t
  let z : ℂ := (-c : ℂ) - (H : ℂ) * I
  let w : ℂ := (c : ℂ) + (H : ℂ) * I
  have hF : Differentiable ℂ F := differentiable_smoothZetaSqContourNumerator t
  have hzero : Rectangle z w ∈ 𝓝 (0 : ℂ) := by
    rw [rectangle_mem_nhds_iff, mem_reProdIm,
      uIoo_of_le (by simp [z, w]; linarith : z.re ≤ w.re),
      uIoo_of_le (by simp [z, w]; linarith : z.im ≤ w.im)]
    simp [z, w, hc, hH]
  have hdslope : HolomorphicOn (dslope F 0) (Rectangle z w) := by
    change DifferentiableOn ℂ (dslope F 0) (Rectangle z w)
    rw [differentiableOn_dslope (show Rectangle z w ∈ 𝓝 (0 : ℂ) from hzero)]
    exact hF.differentiableOn
  have hprincipal : Set.EqOn
      ((fun u : ℂ => F u / u) - fun u => F 0 / (u - 0))
      (dslope F 0) (Rectangle z w \ {0}) := by
    intro u hu
    have hu0 : u ≠ 0 := hu.2
    rw [Pi.sub_apply, dslope_of_ne F hu0]
    simp only [slope, sub_zero, smul_eq_mul, vsub_eq_sub]
    field_simp
  have hrect := ResidueTheoremOnRectangleWithSimplePole
    (f := fun u : ℂ => F u / u) (g := dslope F 0)
    (p := 0) (A := F 0)
    (zRe_le_wRe := by simp [z, w]; linarith)
    (zIm_le_wIm := by simp [z, w]; linarith)
    hzero hdslope hprincipal
  simpa [F, z, w, smoothZetaSqContourNumerator_zero] using hrect

/-- Exact finite-height, two-side smooth AFE.  The first term is the right
Dirichlet-series contour; the second is the explicit horizontal remainder.
The next source step is to send `H` to infinity, where the Gaussian forces
the horizontal term to zero. -/
theorem smoothZetaSqAFE_truncated_native (t : ℝ) {c H : ℝ}
    (hc : 0 < c) (hH : 0 < H) :
    completedRiemannZeta (afeCriticalPoint t) ^ 2 *
        completedRiemannZeta (afeCriticalPoint (-t)) ^ 2 =
      2 * (VIntegral' (smoothZetaSqContourIntegrand t) c (-H) H -
        HIntegral' (smoothZetaSqContourIntegrand t) (-c) c H) := by
  have hrect := smoothZetaSq_finiteRectangle t hc hH
  change RectangleIntegral'
      (smoothZetaSqContourIntegrand t)
      ((-c : ℂ) - (H : ℂ) * I) ((c : ℂ) + (H : ℂ) * I) = _ at hrect
  rw [show RectangleIntegral'
        (smoothZetaSqContourIntegrand t)
        ((-c : ℂ) - (H : ℂ) * I) ((c : ℂ) + (H : ℂ) * I) =
      2 * (VIntegral' (smoothZetaSqContourIntegrand t) c (-H) H -
        HIntegral' (smoothZetaSqContourIntegrand t) (-c) c H) by
    unfold RectangleIntegral' RectangleIntegral HIntegral' VIntegral'
    simp [sub_re, sub_im, add_re, add_im, mul_re, mul_im]
    rw [hIntegral_smoothZetaSq_bottom, vIntegral_smoothZetaSq_left]
    ring] at hrect
  exact hrect.symm

/-- Infinite-height smooth AFE in its exact improper-contour form.  The
right vertical integrals converge to one half of the completed fourth
moment; the reflected left vertical is the identical second AFE piece. -/
theorem smoothZetaSqAFE_vertical_limit_native (t : ℝ) {c : ℝ}
    (hc : 0 < c) :
    Tendsto (fun H : ℝ =>
      VIntegral' (smoothZetaSqContourIntegrand t) c (-H) H)
      atTop (𝓝 ((completedRiemannZeta (afeCriticalPoint t) ^ 2 *
        completedRiemannZeta (afeCriticalPoint (-t)) ^ 2) / 2)) := by
  let F : ℂ := completedRiemannZeta (afeCriticalPoint t) ^ 2 *
    completedRiemannZeta (afeCriticalPoint (-t)) ^ 2
  have hhorizontal := tendsto_hIntegral'_smoothZetaSq_top_zero t c hc.le
  have htarget : Tendsto (fun H : ℝ => F / 2 +
      HIntegral' (smoothZetaSqContourIntegrand t) (-c) c H)
      atTop (𝓝 (F / 2)) := by
    simpa using tendsto_const_nhds.add hhorizontal
  apply htarget.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
  have hfinite := smoothZetaSqAFE_truncated_native t hc hH
  change F = 2 * (VIntegral' (smoothZetaSqContourIntegrand t) c (-H) H -
    HIntegral' (smoothZetaSqContourIntegrand t) (-c) c H) at hfinite
  linear_combination hfinite / 2

/-- The exact value assigned to the convergent right vertical contour. -/
noncomputable def smoothZetaSqVerticalAFE (t c : ℝ) : ℂ :=
  limUnder atTop (fun H : ℝ =>
    VIntegral' (smoothZetaSqContourIntegrand t) c (-H) H)

theorem smoothZetaSqAFE_native (t : ℝ) {c : ℝ} (hc : 0 < c) :
    smoothZetaSqVerticalAFE t c =
      (completedRiemannZeta (afeCriticalPoint t) ^ 2 *
        completedRiemannZeta (afeCriticalPoint (-t)) ^ 2) / 2 := by
  exact (smoothZetaSqAFE_vertical_limit_native t hc).limUnder_eq

/-- The right-line integrand after opening both zeta squares into their
ordinary divisor Dirichlet series. -/
noncomputable def smoothZetaSqDivisorContourIntegrand
    (t c u : ℝ) : ℂ :=
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  let s₁ : ℂ := afeCriticalPoint t + w
  let s₂ : ℂ := afeCriticalPoint (-t) + w
  Complex.exp (100 * w ^ 2) *
    (s₁ * (1 - s₁)) ^ 2 * (s₂ * (1 - s₂)) ^ 2 *
    Complex.Gammaℝ s₁ ^ 2 * Complex.Gammaℝ s₂ ^ 2 *
    LSeries (fun n : ℕ => (n.divisors.card : ℂ)) s₁ *
    LSeries (fun n : ℕ => (n.divisors.card : ℂ)) s₂ /
    afePoleNormalization t / w

theorem completedRiemannZeta_eq_zeta_mul_GammaR {s : ℂ}
    (hs : 0 < s.re) :
    completedRiemannZeta s = riemannZeta s * Complex.Gammaℝ s := by
  have hs0 : s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  rw [riemannZeta_def_of_ne_zero hs0]
  field_simp [Complex.Gammaℝ_ne_zero_of_re_pos hs]

/-- The central archimedean factor removed when the completed AFE is turned
back into the ordinary zeta fourth moment. -/
noncomputable def afeGammaNormalization (t : ℝ) : ℂ :=
  Complex.Gammaℝ (afeCriticalPoint t) ^ 2 *
    Complex.Gammaℝ (afeCriticalPoint (-t)) ^ 2

theorem afeGammaNormalization_ne_zero (t : ℝ) :
    afeGammaNormalization t ≠ 0 := by
  unfold afeGammaNormalization
  apply mul_ne_zero <;> apply pow_ne_zero <;>
    apply Complex.Gammaℝ_ne_zero_of_re_pos <;>
    norm_num [afeCriticalPoint]

/-- The polynomial part of the coefficientwise Hughes--Young weight on the
imaginary contour. -/
noncomputable def hughesYoungPolynomialRatio (t u : ℝ) : ℂ :=
  let s₁ := afeCriticalPoint t + (u : ℂ) * I
  let s₂ := afeCriticalPoint (-t) + (u : ℂ) * I
  (s₁ * (1 - s₁)) ^ 2 * (s₂ * (1 - s₂)) ^ 2 /
    afePoleNormalization t

/-- The paired archimedean Gamma quotient in the coefficientwise smooth AFE
weight. -/
noncomputable def hughesYoungGammaRatio (t u : ℝ) : ℂ :=
  let s₁ := afeCriticalPoint t + (u : ℂ) * I
  let s₂ := afeCriticalPoint (-t) + (u : ℂ) * I
  Complex.Gammaℝ s₁ ^ 2 * Complex.Gammaℝ s₂ ^ 2 /
    afeGammaNormalization t

/-- The complete normalized archimedean coefficient on `w = iu`.  The
Dirichlet monomial has norm one and is kept separate. -/
noncomputable def hughesYoungArchimedeanWeight (t u : ℝ) : ℂ :=
  Complex.exp (100 * (((u : ℂ) * I) ^ 2)) *
    hughesYoungPolynomialRatio t u * hughesYoungGammaRatio t u

private theorem norm_criticalPolynomial (y : ℝ) :
    ‖((1 / 2 : ℂ) + (y : ℂ) * I) *
        (1 - ((1 / 2 : ℂ) + (y : ℂ) * I))‖ = 1 / 4 + y ^ 2 := by
  rw [norm_mul]
  have h₁ : ‖(1 / 2 : ℂ) + (y : ℂ) * I‖ = Real.sqrt (1 / 4 + y ^ 2) := by
    rw [Complex.norm_def]
    congr 1
    simp [Complex.normSq, sq]
    ring
  have h₂ : ‖1 - ((1 / 2 : ℂ) + (y : ℂ) * I)‖ =
      Real.sqrt (1 / 4 + y ^ 2) := by
    rw [Complex.norm_def]
    congr 1
    simp [Complex.normSq, sq]
    ring
  rw [h₁, h₂, ← sq]
  exact Real.sq_sqrt (by positivity)

/-- Uniform polynomial control in the normalized Hughes--Young weight. -/
theorem norm_hughesYoungPolynomialRatio_le (t u : ℝ) :
    ‖hughesYoungPolynomialRatio t u‖ ≤ (2 + 8 * u ^ 2) ^ 4 := by
  let A := (1 / 4 : ℝ) + t ^ 2
  let Ap := (1 / 4 : ℝ) + (t + u) ^ 2
  let Am := (1 / 4 : ℝ) + (t - u) ^ 2
  have hA : 0 < A := by dsimp [A]; positivity
  have hAp : 0 ≤ Ap := by dsimp [Ap]; positivity
  have hAm : 0 ≤ Am := by dsimp [Am]; positivity
  have hp : Ap ≤ 2 * A + 2 * u ^ 2 := by
    dsimp [A, Ap]
    nlinarith [sq_nonneg (t - u)]
  have hm : Am ≤ 2 * A + 2 * u ^ 2 := by
    dsimp [A, Am]
    nlinarith [sq_nonneg (t + u)]
  have hB : 0 ≤ 2 * A + 2 * u ^ 2 := by positivity
  have hAquarter : (1 / 4 : ℝ) ≤ A := by
    dsimp [A]
    nlinarith [sq_nonneg t]
  have hprod : Ap * Am ≤ (2 * A + 2 * u ^ 2) ^ 2 := by
    calc
      Ap * Am ≤ (2 * A + 2 * u ^ 2) * Am :=
        mul_le_mul_of_nonneg_right hp hAm
      _ ≤ (2 * A + 2 * u ^ 2) * (2 * A + 2 * u ^ 2) :=
        mul_le_mul_of_nonneg_left hm hB
      _ = (2 * A + 2 * u ^ 2) ^ 2 := by ring
  have hratio : Ap * Am / A ^ 2 ≤ (2 + 8 * u ^ 2) ^ 2 := by
    rw [div_le_iff₀ (sq_pos_of_pos hA)]
    calc
      Ap * Am ≤ (2 * A + 2 * u ^ 2) ^ 2 := hprod
      _ ≤ ((2 + 8 * u ^ 2) * A) ^ 2 := by
        gcongr
        nlinarith
      _ = (2 + 8 * u ^ 2) ^ 2 * A ^ 2 := by ring
  have hratio0 : 0 ≤ Ap * Am / A ^ 2 := by positivity
  unfold hughesYoungPolynomialRatio afePoleNormalization
  dsimp only
  have hs₁ : afeCriticalPoint t + (u : ℂ) * I =
      (1 / 2 : ℂ) + ((t + u : ℝ) : ℂ) * I := by
    unfold afeCriticalPoint
    push_cast
    ring
  have hs₂ : afeCriticalPoint (-t) + (u : ℂ) * I =
      (1 / 2 : ℂ) + ((-(t - u) : ℝ) : ℂ) * I := by
    unfold afeCriticalPoint
    push_cast
    ring
  have hP₁ : ‖(afeCriticalPoint t + (u : ℂ) * I) *
      (1 - (afeCriticalPoint t + (u : ℂ) * I))‖ = Ap := by
    rw [hs₁, norm_criticalPolynomial]
  have hP₂ : ‖(afeCriticalPoint (-t) + (u : ℂ) * I) *
      (1 - (afeCriticalPoint (-t) + (u : ℂ) * I))‖ = Am := by
    rw [hs₂, norm_criticalPolynomial]
    dsimp [Am]
    ring
  have hP0₁ : ‖afeCriticalPoint t * (1 - afeCriticalPoint t)‖ = A := by
    unfold afeCriticalPoint
    rw [norm_criticalPolynomial]
  have hP0₂ : ‖afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t))‖ = A := by
    unfold afeCriticalPoint
    rw [norm_criticalPolynomial]
    dsimp [A]
    ring
  have hden : ‖afeCriticalPoint t * (1 - afeCriticalPoint t) *
      afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t))‖ = A ^ 2 := by
    rw [show afeCriticalPoint t * (1 - afeCriticalPoint t) *
        afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t)) =
      (afeCriticalPoint t * (1 - afeCriticalPoint t)) *
        (afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t))) by ring,
      norm_mul, hP0₁, hP0₂, pow_two]
  rw [norm_div, norm_mul, norm_pow, norm_pow, norm_pow, hP₁, hP₂, hden]
  change (Ap ^ 2 * Am ^ 2) / (A ^ 2) ^ 2 ≤ (2 + 8 * u ^ 2) ^ 4
  have hpow := pow_le_pow_left₀ hratio0 hratio 2
  convert hpow using 1
  all_goals field_simp [hA.ne']

/-- The cancellation-sensitive Gamma ratio is uniformly Gaussian in the
contour ordinate and independent of the height `t`. -/
theorem norm_hughesYoungGammaRatio_le (t u : ℝ) :
    ‖hughesYoungGammaRatio t u‖ ≤ Real.exp (16 * u ^ 2) := by
  have hpair := norm_GammaR_critical_symmetric_le t u
  have hcentral : 0 <
      ‖Complex.Gammaℝ (afeCriticalPoint t)‖ *
        ‖Complex.Gammaℝ (afeCriticalPoint (-t))‖ := by
    apply mul_pos <;> rw [norm_pos_iff]
    · exact Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num [afeCriticalPoint])
    · exact Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num [afeCriticalPoint])
  unfold hughesYoungGammaRatio afeGammaNormalization
  dsimp only
  rw [norm_div, norm_mul, norm_pow, norm_pow, norm_mul, norm_pow, norm_pow]
  have hpairSq := pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hpair 2
  have hexp : Real.exp (8 * u ^ 2) ^ 2 = Real.exp (16 * u ^ 2) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hdenEq :
      ‖Complex.Gammaℝ (afeCriticalPoint t)‖ ^ 2 *
          ‖Complex.Gammaℝ (afeCriticalPoint (-t))‖ ^ 2 =
        (‖Complex.Gammaℝ (afeCriticalPoint t)‖ *
          ‖Complex.Gammaℝ (afeCriticalPoint (-t))‖) ^ 2 := by ring
  rw [hdenEq]
  rw [div_le_iff₀ (sq_pos_of_pos hcentral)]
  unfold afeCriticalPoint at hpairSq ⊢
  have hpArg : (1 / 2 : ℂ) + (t : ℂ) * I + (u : ℂ) * I =
      (1 / 2 : ℂ) + ((t + u : ℝ) : ℂ) * I := by
    push_cast
    ring
  have hmArg : (1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I + (u : ℂ) * I =
      (1 / 2 : ℂ) + ((-t + u : ℝ) : ℂ) * I := by
    push_cast
    ring
  calc
    ‖Complex.Gammaℝ ((1 / 2 : ℂ) + (t : ℂ) * I + (u : ℂ) * I)‖ ^ 2 *
          ‖Complex.Gammaℝ ((1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I + (u : ℂ) * I)‖ ^ 2
        = (‖Complex.Gammaℝ ((1 / 2 : ℂ) + ((t + u : ℝ) : ℂ) * I)‖ *
            ‖Complex.Gammaℝ ((1 / 2 : ℂ) + ((-t + u : ℝ) : ℂ) * I)‖) ^ 2 := by
          rw [hpArg, hmArg, mul_pow]
    _ ≤ (Real.exp (8 * u ^ 2) *
          (‖Complex.Gammaℝ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ *
            ‖Complex.Gammaℝ ((1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I)‖)) ^ 2 := hpairSq
    _ = Real.exp (16 * u ^ 2) *
          (‖Complex.Gammaℝ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ *
            ‖Complex.Gammaℝ ((1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I)‖) ^ 2 := by
          rw [mul_pow, hexp]

/-- The actual normalized archimedean AFE coefficient has uniform Gaussian
decay.  This is the Hughes--Young weight estimate that the finite diagonal
consumer requires; no Stirling or weight hypothesis remains. -/
theorem norm_hughesYoungArchimedeanWeight_le (t u : ℝ) :
    ‖hughesYoungArchimedeanWeight t u‖ ≤
      Real.exp (-84 * u ^ 2) * (2 + 8 * u ^ 2) ^ 4 := by
  unfold hughesYoungArchimedeanWeight
  rw [norm_mul, norm_mul, Complex.norm_exp]
  have hgauss :
      (100 * (((u : ℂ) * I) ^ 2)).re = -100 * u ^ 2 := by
    simp [pow_two, mul_re, mul_im]
  rw [hgauss]
  calc
    Real.exp (-100 * u ^ 2) * ‖hughesYoungPolynomialRatio t u‖ *
          ‖hughesYoungGammaRatio t u‖
        ≤ Real.exp (-100 * u ^ 2) * (2 + 8 * u ^ 2) ^ 4 *
            Real.exp (16 * u ^ 2) := by
          gcongr
          · exact norm_hughesYoungPolynomialRatio_le t u
          · exact norm_hughesYoungGammaRatio_le t u
    _ = Real.exp (-84 * u ^ 2) * (2 + 8 * u ^ 2) ^ 4 := by
      rw [mul_assoc, mul_comm ((2 + 8 * u ^ 2) ^ 4), ← mul_assoc,
        ← Real.exp_add]
      congr 1
      ring_nf

/-- A purely Gaussian envelope for the exact coefficientwise weight.  The
polynomial loss is absorbed while retaining an integrable majorant. -/
theorem norm_hughesYoungArchimedeanWeight_le_gaussian (t u : ℝ) :
    ‖hughesYoungArchimedeanWeight t u‖ ≤ 16 * Real.exp (-68 * u ^ 2) := by
  have hone : 1 + 4 * u ^ 2 ≤ Real.exp (4 * u ^ 2) := by
    simpa [add_comm] using Real.add_one_le_exp (4 * u ^ 2)
  have hpow : (1 + 4 * u ^ 2) ^ 4 ≤ (Real.exp (4 * u ^ 2)) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hone 4
  calc
    ‖hughesYoungArchimedeanWeight t u‖
        ≤ Real.exp (-84 * u ^ 2) * (2 + 8 * u ^ 2) ^ 4 :=
          norm_hughesYoungArchimedeanWeight_le t u
    _ = 16 * Real.exp (-84 * u ^ 2) * (1 + 4 * u ^ 2) ^ 4 := by ring
    _ ≤ 16 * Real.exp (-84 * u ^ 2) * (Real.exp (4 * u ^ 2)) ^ 4 := by
      gcongr
    _ = 16 * Real.exp (-68 * u ^ 2) := by
      have hexp : (Real.exp (4 * u ^ 2)) ^ 4 = Real.exp (16 * u ^ 2) := by
        rw [← Real.exp_nat_mul]
        congr 1
        norm_num
        ring
      rw [hexp, mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- The Gaussian envelope left by the exact Hughes--Young weight is
integrable on the full Mellin line. -/
theorem integrable_hughesYoungWeightEnvelope :
    Integrable (fun u : ℝ => 16 * Real.exp (-68 * u ^ 2)) := by
  exact (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 68)).const_mul 16

/-- At `w = iu`, the normalized analytic factor in the divisor contour is
exactly the coefficientwise Hughes--Young archimedean weight.  This theorem
prevents the weight estimate from floating free of the proved AFE contour. -/
theorem smoothZetaSqDivisorContourIntegrand_zeroLine_eq_weight
    (t u : ℝ) :
    smoothZetaSqDivisorContourIntegrand t 0 u /
        afeGammaNormalization t =
      hughesYoungArchimedeanWeight t u *
        LSeries (fun n : ℕ => (n.divisors.card : ℂ))
          (afeCriticalPoint t + (u : ℂ) * I) *
        LSeries (fun n : ℕ => (n.divisors.card : ℂ))
          (afeCriticalPoint (-t) + (u : ℂ) * I) /
        ((u : ℂ) * I) := by
  unfold smoothZetaSqDivisorContourIntegrand hughesYoungArchimedeanWeight
    hughesYoungPolynomialRatio hughesYoungGammaRatio
  dsimp only [ofReal_zero, zero_add]
  ring_nf

/-- Ordinary-zeta form of the smooth AFE.  Thus the proved contour identity
is not merely an identity for an auxiliary completion: after division by the
nonzero central Gamma factors its limit is exactly half the product of the
two critical-line zeta squares. -/
theorem smoothZetaSqAFE_zeta_vertical_limit_native
    (t : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun H : ℝ =>
      (VIntegral' (fun w => smoothZetaSqContourIntegrand t w) c (-H) H /
        afeGammaNormalization t))
      atTop (𝓝 ((riemannZeta (afeCriticalPoint t) ^ 2 *
        riemannZeta (afeCriticalPoint (-t)) ^ 2) / 2)) := by
  have hafe := (smoothZetaSqAFE_vertical_limit_native t hc).div_const
    (afeGammaNormalization t)
  convert hafe using 1
  have hplus : 0 < (afeCriticalPoint t).re := by norm_num [afeCriticalPoint]
  have hminus : 0 < (afeCriticalPoint (-t)).re := by norm_num [afeCriticalPoint]
  rw [completedRiemannZeta_eq_zeta_mul_GammaR hplus,
    completedRiemannZeta_eq_zeta_mul_GammaR hminus]
  unfold afeGammaNormalization
  field_simp [Complex.Gammaℝ_ne_zero_of_re_pos hplus,
    Complex.Gammaℝ_ne_zero_of_re_pos hminus]

/-- On every right line `c > 1/2`, the AFE contour is literally the product
of two divisor L-series.  This is the exact Dirichlet-series opening used
before Hughes--Young's diagonal/off-diagonal split. -/
theorem smoothZetaSqContourIntegrand_eq_divisorContour
    (t u : ℝ) {c : ℝ} (hc : 1 / 2 < c) :
    smoothZetaSqContourIntegrand t ((c : ℂ) + (u : ℂ) * I) =
      smoothZetaSqDivisorContourIntegrand t c u := by
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  let s₁ : ℂ := afeCriticalPoint t + w
  let s₂ : ℂ := afeCriticalPoint (-t) + w
  have hs₁re : 1 < s₁.re := by
    simp [s₁, w, afeCriticalPoint]
    linarith
  have hs₂re : 1 < s₂.re := by
    simp [s₂, w, afeCriticalPoint]
    linarith
  have hs₁0 : s₁ ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hs₁1 : s₁ ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hs₂0 : s₂ ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hs₂1 : s₂ ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hΛ₁ := completedRiemannZeta_eq_zeta_mul_GammaR
    (show 0 < s₁.re from lt_trans zero_lt_one hs₁re)
  have hΛ₂ := completedRiemannZeta_eq_zeta_mul_GammaR
    (show 0 < s₂.re from lt_trans zero_lt_one hs₂re)
  have hζ₁ := riemannZeta_sq_eq_divisorLSeries hs₁re
  have hζ₂ := riemannZeta_sq_eq_divisorLSeries hs₂re
  unfold smoothZetaSqContourIntegrand smoothZetaSqContourNumerator
    smoothZetaSqDivisorContourIntegrand
  dsimp only
  change (Complex.exp (100 * w ^ 2) * completedXiNumerator s₁ ^ 2 *
      completedXiNumerator s₂ ^ 2 / afePoleNormalization t) / w = _
  rw [completedXiNumerator_eq s₁ hs₁0 hs₁1,
    completedXiNumerator_eq s₂ hs₂0 hs₂1, hΛ₁, hΛ₂]
  simp only [mul_pow]
  rw [hζ₁, hζ₂]
  ring

/-- The smooth AFE with its right side exposed as an improper integral of
the two divisor L-series. -/
theorem smoothZetaSqAFE_divisor_vertical_limit_native
    (t : ℝ) {c : ℝ} (hc : 1 / 2 < c) :
    Tendsto (fun H : ℝ =>
      ((1 / (2 * Real.pi : ℂ)) *
        ∫ u in -H..H, smoothZetaSqDivisorContourIntegrand t c u))
      atTop (𝓝 ((completedRiemannZeta (afeCriticalPoint t) ^ 2 *
        completedRiemannZeta (afeCriticalPoint (-t)) ^ 2) / 2)) := by
  have hafe := smoothZetaSqAFE_vertical_limit_native t
    (show 0 < c by linarith)
  apply hafe.congr'
  filter_upwards with H
  unfold VIntegral' VIntegral
  simp only [smul_eq_mul]
  rw [intervalIntegral.integral_congr]
  · field_simp [Real.pi_ne_zero]
  · intro u _hu
    exact smoothZetaSqContourIntegrand_eq_divisorContour t u hc

/-- Native finite diagonal theorem for the AFE expansion.  It evaluates the
entire `hm = kn` contribution and gives the coefficient-uniform norm bound;
no off-diagonal input is used. -/
theorem twistedFourthMomentDiagonal_native
    (T : ℝ) (hT : 0 ≤ T) (H M K N : Finset ℕ)
    (a : ℕ → ℕ → ℕ → ℕ → ℂ) :
    finiteTwistedFourthMomentDiagonal T H M K N a =
        ((5 * T / 2 : ℝ) : ℂ) *
          finiteTwistedDiagonalCoefficientSum H M K N a ∧
      ‖finiteTwistedFourthMomentDiagonal T H M K N a‖ ≤
        (5 * T / 2) *
          ∑ h ∈ H, ∑ m ∈ M, ∑ k ∈ K, ∑ n ∈ N,
            if h * m = k * n then ‖a h m k n‖ else 0 := by
  constructor
  · exact finiteTwistedFourthMomentDiagonal_eq T H M K N a
  · simpa [abs_of_nonneg (by positivity : 0 ≤ 5 * T / 2)] using
      norm_finiteTwistedFourthMomentDiagonal_le T H M K N a

/-- The positive `h`-fiber over the Hughes--Young diagonal parameter
`q = h * m`.  The restriction `h ≤ L` is the short-twist support condition;
`q / h` is then the corresponding zeta-square index `m`. -/
noncomputable def smoothTwistedDiagonalFiber
    (ell q : ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ h ∈ q.divisors.filter (fun h => h ≤ ell),
    ‖a h‖ * ((q / h).divisors.card : ℝ)

/-- The complete positive majorant of the exact `hm = kn` contribution,
grouped by the common product `q`.  Its factor `q⁻¹` is exactly
`(hmkn)⁻¹/²` on the diagonal. -/
noncomputable def smoothTwistedDiagonalMajorant
    (T : ℝ) (ell cutoff : ℕ) (a : ℕ → ℂ) : ℝ :=
  (5 * T / 2) * ∑ q ∈ Finset.Icc 1 cutoff,
    smoothTwistedDiagonalFiber ell q a ^ 2 * (q : ℝ)⁻¹

/-- A coefficient and divisor power bound controls one diagonal fiber.  This
is the elementary arithmetic step behind the diagonal part of Hughes--Young:
there are at most `d(q)` choices of `h`, and both `h` and `q/h` divide `q`. -/
theorem smoothTwistedDiagonalFiber_le
    {ell q : ℕ} (hq : 0 < q) (a : ℕ → ℂ)
    {delta ca cd : ℝ} (hdelta : 0 ≤ delta) (hca : 0 ≤ ca) (hcd : 0 ≤ cd)
    (ha : ∀ h ∈ Finset.Icc 1 ell, ‖a h‖ ≤ ca * (h : ℝ) ^ delta)
    (hd : ∀ n : ℕ, 0 < n → (n.divisors.card : ℝ) ≤ cd * (n : ℝ) ^ delta) :
    smoothTwistedDiagonalFiber ell q a ≤
      ca * cd ^ 2 * (q : ℝ) ^ (3 * delta) := by
  let S := q.divisors.filter (fun h => h ≤ ell)
  have hterm : ∀ h ∈ S,
      ‖a h‖ * ((q / h).divisors.card : ℝ) ≤
        ca * cd * (q : ℝ) ^ (2 * delta) := by
    intro h hh
    have hhDiv : h ∣ q := (Nat.mem_divisors.mp (Finset.mem_filter.mp hh).1).1
    have hhPos : 0 < h := Nat.pos_of_dvd_of_pos hhDiv hq
    have hhL : h ≤ ell := (Finset.mem_filter.mp hh).2
    have hhq : h ≤ q := Nat.le_of_dvd hq hhDiv
    have hquotPos : 0 < q / h := Nat.div_pos (Nat.le_of_dvd hq hhDiv) hhPos
    have hquotLe : q / h ≤ q := Nat.div_le_self q h
    have ha' := ha h (Finset.mem_Icc.mpr ⟨hhPos, hhL⟩)
    have hd' := hd (q / h) hquotPos
    have hhPow : (h : ℝ) ^ delta ≤ (q : ℝ) ^ delta := by
      exact Real.rpow_le_rpow (Nat.cast_nonneg h) (by exact_mod_cast hhq) hdelta
    have hquotPow : ((q / h : ℕ) : ℝ) ^ delta ≤ (q : ℝ) ^ delta := by
      exact Real.rpow_le_rpow (Nat.cast_nonneg (q / h))
        (by exact_mod_cast hquotLe) hdelta
    calc
      ‖a h‖ * ((q / h).divisors.card : ℝ)
          ≤ (ca * (h : ℝ) ^ delta) * (cd * ((q / h : ℕ) : ℝ) ^ delta) := by
            gcongr
      _ ≤ (ca * (q : ℝ) ^ delta) * (cd * (q : ℝ) ^ delta) := by
            gcongr
      _ = ca * cd * (q : ℝ) ^ (2 * delta) := by
            have hp : (q : ℝ) ^ delta * (q : ℝ) ^ delta =
                (q : ℝ) ^ (2 * delta) := by
              rw [← Real.rpow_add (Nat.cast_pos.mpr hq)]
              ring_nf
            rw [show (ca * (q : ℝ) ^ delta) * (cd * (q : ℝ) ^ delta) =
                ca * cd * ((q : ℝ) ^ delta * (q : ℝ) ^ delta) by ring, hp]
  have hCard : (S.card : ℝ) ≤ cd * (q : ℝ) ^ delta := by
    calc
      (S.card : ℝ) ≤ (q.divisors.card : ℝ) := by
        exact_mod_cast Finset.card_filter_le q.divisors (fun h => h ≤ ell)
      _ ≤ cd * (q : ℝ) ^ delta := hd q hq
  unfold smoothTwistedDiagonalFiber
  change (∑ h ∈ S, ‖a h‖ * ((q / h).divisors.card : ℝ)) ≤ _
  calc
    (∑ h ∈ S, ‖a h‖ * ((q / h).divisors.card : ℝ))
        ≤ ∑ _h ∈ S, ca * cd * (q : ℝ) ^ (2 * delta) := by
          exact Finset.sum_le_sum fun h hh => hterm h hh
    _ = (S.card : ℝ) * (ca * cd * (q : ℝ) ^ (2 * delta)) := by simp
    _ ≤ (cd * (q : ℝ) ^ delta) *
        (ca * cd * (q : ℝ) ^ (2 * delta)) := by
          gcongr
    _ = ca * cd ^ 2 * (q : ℝ) ^ (3 * delta) := by
          have hp : (q : ℝ) ^ delta * (q : ℝ) ^ (2 * delta) =
              (q : ℝ) ^ (3 * delta) := by
            rw [← Real.rpow_add (Nat.cast_pos.mpr hq)]
            ring_nf
          rw [show (cd * (q : ℝ) ^ delta) *
              (ca * cd * (q : ℝ) ^ (2 * delta)) =
                ca * cd ^ 2 * ((q : ℝ) ^ delta *
                  (q : ℝ) ^ (2 * delta)) by ring, hp]

/-- Uniform finite diagonal estimate.  In particular, a short twist whose
coefficients and the divisor function satisfy arbitrarily small power bounds
costs only an arbitrarily small power of the diagonal cutoff.  The harmonic
factor is the genuine sum of `q⁻¹`, rather than a cardinality overestimate. -/
theorem smoothTwistedDiagonalMajorant_le
    {T : ℝ} (hT : 0 ≤ T) {ell cutoff : ℕ} (a : ℕ → ℂ)
    {delta ca cd : ℝ} (hdelta : 0 ≤ delta) (hca : 0 ≤ ca) (hcd : 0 ≤ cd)
    (ha : ∀ h ∈ Finset.Icc 1 ell, ‖a h‖ ≤ ca * (h : ℝ) ^ delta)
    (hd : ∀ n : ℕ, 0 < n → (n.divisors.card : ℝ) ≤ cd * (n : ℝ) ^ delta) :
    smoothTwistedDiagonalMajorant T ell cutoff a ≤
      (5 * T / 2) * ca ^ 2 * cd ^ 4 * (cutoff : ℝ) ^ (6 * delta) *
        (((harmonic cutoff : ℚ) : ℝ)) := by
  have hTerm : ∀ q ∈ Finset.Icc 1 cutoff,
      smoothTwistedDiagonalFiber ell q a ^ 2 * (q : ℝ)⁻¹ ≤
        ca ^ 2 * cd ^ 4 * (cutoff : ℝ) ^ (6 * delta) * (q : ℝ)⁻¹ := by
    intro q hq
    have hqPos : 0 < q := (Finset.mem_Icc.mp hq).1
    have hqCutoff : q ≤ cutoff := (Finset.mem_Icc.mp hq).2
    have hFiber := smoothTwistedDiagonalFiber_le hqPos a hdelta hca hcd ha hd
    have hFiberNonneg : 0 ≤ smoothTwistedDiagonalFiber ell q a := by
      unfold smoothTwistedDiagonalFiber
      positivity
    have hUpperNonneg : 0 ≤ ca * cd ^ 2 * (q : ℝ) ^ (3 * delta) := by
      positivity
    have hSquare : smoothTwistedDiagonalFiber ell q a ^ 2 ≤
        ca ^ 2 * cd ^ 4 * (q : ℝ) ^ (6 * delta) := by
      have hs := (sq_le_sq₀ hFiberNonneg hUpperNonneg).2 hFiber
      calc
        smoothTwistedDiagonalFiber ell q a ^ 2
            ≤ (ca * cd ^ 2 * (q : ℝ) ^ (3 * delta)) ^ 2 := hs
        _ = ca ^ 2 * cd ^ 4 * (q : ℝ) ^ (6 * delta) := by
          have hp : ((q : ℝ) ^ (3 * delta)) ^ 2 =
              (q : ℝ) ^ (6 * delta) := by
            rw [← Real.rpow_natCast]
            rw [← Real.rpow_mul (Nat.cast_nonneg q)]
            congr 1
            ring
          rw [show (ca * cd ^ 2 * (q : ℝ) ^ (3 * delta)) ^ 2 =
              ca ^ 2 * cd ^ 4 * (((q : ℝ) ^ (3 * delta)) ^ 2) by ring, hp]
    have hPow : (q : ℝ) ^ (6 * delta) ≤
        (cutoff : ℝ) ^ (6 * delta) := by
      apply Real.rpow_le_rpow (Nat.cast_nonneg q)
      · exact_mod_cast hqCutoff
      · positivity
    calc
      smoothTwistedDiagonalFiber ell q a ^ 2 * (q : ℝ)⁻¹
          ≤ (ca ^ 2 * cd ^ 4 * (q : ℝ) ^ (6 * delta)) *
              (q : ℝ)⁻¹ := by gcongr
      _ ≤ (ca ^ 2 * cd ^ 4 * (cutoff : ℝ) ^ (6 * delta)) *
              (q : ℝ)⁻¹ := by gcongr
  unfold smoothTwistedDiagonalMajorant
  calc
    (5 * T / 2) * ∑ q ∈ Finset.Icc 1 cutoff,
        smoothTwistedDiagonalFiber ell q a ^ 2 * (q : ℝ)⁻¹
        ≤ (5 * T / 2) * ∑ q ∈ Finset.Icc 1 cutoff,
            ca ^ 2 * cd ^ 4 * (cutoff : ℝ) ^ (6 * delta) *
              (q : ℝ)⁻¹ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Finset.sum_le_sum fun q hq => hTerm q hq
    _ = (5 * T / 2) * ca ^ 2 * cd ^ 4 *
        (cutoff : ℝ) ^ (6 * delta) * (((harmonic cutoff : ℚ) : ℝ)) := by
      have hsum :
          (∑ q ∈ Finset.Icc 1 cutoff,
              ca ^ 2 * cd ^ 4 * (cutoff : ℝ) ^ (6 * delta) * (q : ℝ)⁻¹) =
            ca ^ 2 * cd ^ 4 * (cutoff : ℝ) ^ (6 * delta) *
              ∑ q ∈ Finset.Icc 1 cutoff, (q : ℝ)⁻¹ := by
        rw [Finset.mul_sum]
      rw [hsum]
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      simp only [Rat.cast_inv, Rat.cast_natCast]
      ring

/-- The source-shaped finite weighted diagonal after the change of variables
`q = h*m = k*n`.  The function `weight q h k t` is the smooth AFE weight on
that diagonal.  This definition keeps that weight inside the `t`-integral,
as in Hughes--Young equation (42). -/
noncomputable def smoothTwistedWeightedDiagonal
    (T : ℝ) (ell cutoff : ℕ) (a : ℕ → ℂ)
    (weight : ℕ → ℕ → ℕ → ℝ → ℂ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 cutoff,
    ∑ h ∈ q.divisors.filter (fun h => h ≤ ell),
      ∑ k ∈ q.divisors.filter (fun k => k ≤ ell),
        (a h * star (a k) * ((q / h).divisors.card : ℂ) *
            ((q / k).divisors.card : ℂ) / (q : ℂ)) *
          ∫ t in T / 2..3 * T, weight q h k t

/-- Any pointwise-normalized smooth AFE weight is consumed by exactly the
arithmetic majorant proved above.  This is the missing bridge between the
analytic AFE weight and the regrouped `q = hm = kn` diagonal: no unweighted
phase integral is substituted for a weighted one. -/
theorem norm_smoothTwistedWeightedDiagonal_le_mul
    {T C : ℝ} {ell cutoff : ℕ} (a : ℕ → ℂ)
    (weight : ℕ → ℕ → ℕ → ℝ → ℂ)
    (hWeight : ∀ q ∈ Finset.Icc 1 cutoff,
      ∀ h ∈ q.divisors.filter (fun h => h ≤ ell),
      ∀ k ∈ q.divisors.filter (fun k => k ≤ ell),
        ‖∫ t in T / 2..3 * T, weight q h k t‖ ≤ C * (5 * T / 2)) :
    ‖smoothTwistedWeightedDiagonal T ell cutoff a weight‖ ≤
      C * smoothTwistedDiagonalMajorant T ell cutoff a := by
  unfold smoothTwistedWeightedDiagonal smoothTwistedDiagonalMajorant
  calc
    ‖∑ q ∈ Finset.Icc 1 cutoff,
        ∑ h ∈ q.divisors.filter (fun h => h ≤ ell),
          ∑ k ∈ q.divisors.filter (fun k => k ≤ ell),
            (a h * star (a k) * ((q / h).divisors.card : ℂ) *
                ((q / k).divisors.card : ℂ) / (q : ℂ)) *
              ∫ t in T / 2..3 * T, weight q h k t‖
        ≤ ∑ q ∈ Finset.Icc 1 cutoff,
            ∑ h ∈ q.divisors.filter (fun h => h ≤ ell),
              ∑ k ∈ q.divisors.filter (fun k => k ≤ ell),
                ‖(a h * star (a k) * ((q / h).divisors.card : ℂ) *
                    ((q / k).divisors.card : ℂ) / (q : ℂ)) *
                  ∫ t in T / 2..3 * T, weight q h k t‖ := by
          exact norm_sum_le _ _ |>.trans <| Finset.sum_le_sum fun q _ =>
            norm_sum_le _ _ |>.trans <| Finset.sum_le_sum fun h _ => norm_sum_le _ _
    _ ≤ ∑ q ∈ Finset.Icc 1 cutoff,
          ∑ h ∈ q.divisors.filter (fun h => h ≤ ell),
            ∑ k ∈ q.divisors.filter (fun k => k ≤ ell),
              (‖a h‖ * ((q / h).divisors.card : ℝ)) *
                (‖a k‖ * ((q / k).divisors.card : ℝ)) *
                (q : ℝ)⁻¹ * (C * (5 * T / 2)) := by
          apply Finset.sum_le_sum
          intro q hq
          have hqPos : 0 < q := (Finset.mem_Icc.mp hq).1
          apply Finset.sum_le_sum
          intro h hh
          apply Finset.sum_le_sum
          intro k hk
          rw [norm_mul, norm_div, norm_mul, norm_mul, norm_mul,
            norm_star, Complex.norm_natCast, Complex.norm_natCast,
            Complex.norm_natCast, div_eq_mul_inv]
          have hw := hWeight q hq h hh k hk
          have hcoef : 0 ≤ ‖a h‖ * ‖a k‖ *
              ((q / h).divisors.card : ℝ) * ((q / k).divisors.card : ℝ) *
                (q : ℝ)⁻¹ := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hw hcoef]
    _ = C * ((5 * T / 2) * ∑ q ∈ Finset.Icc 1 cutoff,
          smoothTwistedDiagonalFiber ell q a ^ 2 * (q : ℝ)⁻¹) := by
          rw [show C * ((5 * T / 2) * ∑ q ∈ Finset.Icc 1 cutoff,
              smoothTwistedDiagonalFiber ell q a ^ 2 * (q : ℝ)⁻¹) =
            C * (5 * T / 2) * ∑ q ∈ Finset.Icc 1 cutoff,
              smoothTwistedDiagonalFiber ell q a ^ 2 * (q : ℝ)⁻¹ by ring]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          unfold smoothTwistedDiagonalFiber
          let S := q.divisors.filter (fun h => h ≤ ell)
          let x : ℕ → ℝ := fun h => ‖a h‖ * ((q / h).divisors.card : ℝ)
          have hInner : ∀ h ∈ S,
              (∑ k ∈ S, x h * x k * (q : ℝ)⁻¹ * (C * (5 * T / 2))) =
                x h * (∑ k ∈ S, x k) * (q : ℝ)⁻¹ * (C * (5 * T / 2)) := by
            intro h hh
            calc
              (∑ k ∈ S, x h * x k * (q : ℝ)⁻¹ * (C * (5 * T / 2))) =
                  x h * (q : ℝ)⁻¹ * (C * (5 * T / 2)) * ∑ k ∈ S, x k := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro k hk
                    ring
              _ = x h * (∑ k ∈ S, x k) * (q : ℝ)⁻¹ * (C * (5 * T / 2)) := by ring
          dsimp [S, x] at hInner ⊢
          rw [Finset.sum_congr rfl hInner, pow_two]
          let A := ∑ h ∈ q.divisors.filter (fun h => h ≤ ell),
            ‖a h‖ * ((q / h).divisors.card : ℝ)
          have hOuter :
              (∑ h ∈ q.divisors.filter (fun h => h ≤ ell),
                (‖a h‖ * ((q / h).divisors.card : ℝ) * A) *
                  (q : ℝ)⁻¹ * (C * (5 * T / 2))) =
                A * A * (q : ℝ)⁻¹ * (C * (5 * T / 2)) := by
            calc
              _ = A * (q : ℝ)⁻¹ * (C * (5 * T / 2)) *
                  ∑ h ∈ q.divisors.filter (fun h => h ≤ ell),
                    ‖a h‖ * ((q / h).divisors.card : ℝ) := by
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro h hh
                      ring
              _ = _ := by dsimp [A]; ring
          exact hOuter.trans (by dsimp [A]; ring)

/-- The normalized-weight consumer is the unit-constant specialization of
the quantitative diagonal theorem. -/
theorem norm_smoothTwistedWeightedDiagonal_le
    {T : ℝ} {ell cutoff : ℕ} (a : ℕ → ℂ)
    (weight : ℕ → ℕ → ℕ → ℝ → ℂ)
    (hWeight : ∀ q ∈ Finset.Icc 1 cutoff,
      ∀ h ∈ q.divisors.filter (fun h => h ≤ ell),
      ∀ k ∈ q.divisors.filter (fun k => k ≤ ell),
        ‖∫ t in T / 2..3 * T, weight q h k t‖ ≤ 5 * T / 2) :
    ‖smoothTwistedWeightedDiagonal T ell cutoff a weight‖ ≤
      smoothTwistedDiagonalMajorant T ell cutoff a := by
  simpa using norm_smoothTwistedWeightedDiagonal_le_mul a weight
    (C := 1) (by simpa using hWeight)

/-- The concrete coefficientwise AFE weight satisfies the exact interval
bound required by the weighted diagonal consumer, with its Gaussian decay
retained uniformly in the height interval. -/
theorem norm_integral_hughesYoungArchimedeanWeight_le
    {T : ℝ} (hT : 0 ≤ T) (u : ℝ) :
    ‖∫ t in T / 2..3 * T, hughesYoungArchimedeanWeight t u‖ ≤
      (16 * Real.exp (-68 * u ^ 2)) * (5 * T / 2) := by
  apply (intervalIntegral.norm_integral_le_of_norm_le_const fun t _ =>
    norm_hughesYoungArchimedeanWeight_le_gaussian t u).trans
  have hlen : |3 * T - T / 2| = 5 * T / 2 := by
    rw [abs_of_nonneg]
    · ring
    · linarith
  rw [hlen]

/-- The actual Hughes--Young coefficientwise weight, rather than an abstract
surrogate, is consumed by the diagonal majorant at every Mellin ordinate.
The remaining scalar envelope is integrable by
`integrable_hughesYoungWeightEnvelope`. -/
theorem norm_hughesYoungWeightedDiagonalSlice_le
    {T : ℝ} (hT : 0 ≤ T) {ell cutoff : ℕ} (a : ℕ → ℂ) (u : ℝ) :
    ‖smoothTwistedWeightedDiagonal T ell cutoff a
        (fun _q _h _k t => hughesYoungArchimedeanWeight t u)‖ ≤
      (16 * Real.exp (-68 * u ^ 2)) *
        smoothTwistedDiagonalMajorant T ell cutoff a := by
  apply norm_smoothTwistedWeightedDiagonal_le_mul a _
  intro q hq h hh k hk
  exact norm_integral_hughesYoungArchimedeanWeight_le hT u

end RiemannZeta.GuthMaynard
