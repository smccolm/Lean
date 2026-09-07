import RiemannZeta.GuthMaynard.HughesYoungCompleteCentralContinuation

open Complex Filter Metric Set
open scoped BigOperators Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# The cancellation-preserving Hughes--Young central master jet

The four equation-(84) kernel coefficients pair with the value, the two
first derivatives, and the mixed derivative of the equation-(98) arithmetic
jet.  The reversed kernel polynomial below packages that pairing as one
mixed derivative.  This is the source-faithful object to which the contour
shift and its single moving zeta pole are applied before the auxiliary
shifts are specialized to zero.
-/

/-- The reversed kernel polynomial.  Its value and its first and mixed
Taylor coefficients occur in the reverse order needed by the product rule. -/
noncomputable def hughesYoungCentralReverseKernelPolynomial
    (t : ℝ) (W z w : ℂ) : ℂ :=
  hughesYoungEquation84Kernel11 t W +
    z * hughesYoungEquation84Kernel10 t W +
    w * hughesYoungEquation84Kernel01 t W +
    z * w * hughesYoungEquation84Kernel00 t W

/-- The `hughesYoungCentralReverseKernelPolynomialCore` definition used by the source-facing construction in `HughesYoungCentralMaster`. -/
noncomputable def hughesYoungCentralReverseKernelPolynomialCore
    (t : ℝ) (W z w : ℂ) : ℂ :=
  hughesYoungEquation84KernelCore11 t W +
    z * hughesYoungEquation84KernelCore10 t W +
    w * hughesYoungEquation84KernelCore01 t W +
    z * w * hughesYoungEquation84KernelCore00 t W

theorem hughesYoungCentralReverseKernelPolynomial_eq_auxiliary_mul_core
    (t : ℝ) (W z w : ℂ) :
    hughesYoungCentralReverseKernelPolynomial t W z w =
      hughesYoungAuxiliaryZero W *
        hughesYoungCentralReverseKernelPolynomialCore t W z w := by
  unfold hughesYoungCentralReverseKernelPolynomial
    hughesYoungCentralReverseKernelPolynomialCore
  rw [hughesYoungEquation84Kernel11_eq_auxiliary_mul_core,
    hughesYoungEquation84Kernel10_eq_auxiliary_mul_core,
    hughesYoungEquation84Kernel01_eq_auxiliary_mul_core,
    hughesYoungEquation84Kernel00_eq_auxiliary_mul_core]
  ring

@[simp]
theorem hughesYoungCentralReverseKernelPolynomial_zero_zero
    (t : ℝ) (W : ℂ) :
    hughesYoungCentralReverseKernelPolynomial t W 0 0 =
      hughesYoungEquation84Kernel11 t W := by
  simp [hughesYoungCentralReverseKernelPolynomial]

theorem hasDerivAt_hughesYoungCentralReverseKernelPolynomial_left
    (t : ℝ) (W z w : ℂ) :
    HasDerivAt
      (fun v => hughesYoungCentralReverseKernelPolynomial t W v w)
      (hughesYoungEquation84Kernel10 t W +
        w * hughesYoungEquation84Kernel00 t W) z := by
  unfold hughesYoungCentralReverseKernelPolynomial
  convert (((hasDerivAt_const (x := z)
      (hughesYoungEquation84Kernel11 t W)).add
    ((hasDerivAt_id (x := z)).mul_const
      (hughesYoungEquation84Kernel10 t W))).add
    (hasDerivAt_const (x := z)
      (w * hughesYoungEquation84Kernel01 t W))).add
    (((hasDerivAt_id (x := z)).mul_const w).mul_const
      (hughesYoungEquation84Kernel00 t W)) using 1
  all_goals ring_nf

theorem hasDerivAt_hughesYoungCentralReverseKernelPolynomial_right
    (t : ℝ) (W z w : ℂ) :
    HasDerivAt
      (fun v => hughesYoungCentralReverseKernelPolynomial t W z v)
      (hughesYoungEquation84Kernel01 t W +
        z * hughesYoungEquation84Kernel00 t W) w := by
  unfold hughesYoungCentralReverseKernelPolynomial
  convert (((hasDerivAt_const (x := w)
      (hughesYoungEquation84Kernel11 t W)).add
    (hasDerivAt_const (x := w)
      (z * hughesYoungEquation84Kernel10 t W))).add
    ((hasDerivAt_id (x := w)).mul_const
      (hughesYoungEquation84Kernel01 t W))).add
    (((hasDerivAt_const (x := w) z).mul
      (hasDerivAt_id (x := w))).mul_const
        (hughesYoungEquation84Kernel00 t W)) using 1
  all_goals ring_nf

/-- The undifferentiated master jet whose mixed auxiliary derivative is the
four-term continuation used by equation (84). -/
noncomputable def hughesYoungCentralMasterJet
    (t : ℝ) (a b : ℕ) (W z w : ℂ) : ℂ :=
  hughesYoungEquation96ContinuationJet a b
      (hughesYoungEquation96ContourParameter W) z w *
    hughesYoungCentralReverseKernelPolynomial t W z w

/-- Exact product-rule recovery of the four equation-(84) coefficients from
one mixed derivative.  Keeping `z,w` until after the contour shift preserves
the cancellation at the moving simple pole `2W-z-w=1`. -/
theorem deriv_right_deriv_left_hughesYoungCentralMasterJet_zero
    (t : ℝ) {a b : ℕ} (W : ℂ)
    (hW : (7 / 8 : ℝ) < W.re) :
    deriv (fun w => deriv
      (fun z => hughesYoungCentralMasterJet t a b W z w) 0) 0 =
      hughesYoungEquation96ContinuationCoefficient a b
          (hughesYoungEquation96ContourParameter W) false false *
            hughesYoungEquation84Kernel00 t W +
        hughesYoungEquation96ContinuationCoefficient a b
          (hughesYoungEquation96ContourParameter W) true false *
            hughesYoungEquation84Kernel10 t W +
        hughesYoungEquation96ContinuationCoefficient a b
          (hughesYoungEquation96ContourParameter W) false true *
            hughesYoungEquation84Kernel01 t W +
        hughesYoungEquation96ContinuationCoefficient a b
          (hughesYoungEquation96ContourParameter W) true true *
            hughesYoungEquation84Kernel11 t W := by
  let q := hughesYoungEquation96ContourParameter W
  let J : ℂ × ℂ → ℂ := fun p =>
    hughesYoungEquation96ContinuationJet a b q p.1 p.2
  let P : ℂ × ℂ → ℂ := fun p =>
    hughesYoungCentralReverseKernelPolynomial t W p.1 p.2
  have hq : -(1 / 4 : ℝ) < q.re := by
    dsimp only [q, hughesYoungEquation96ContourParameter]
    norm_num [Complex.mul_re]
    linarith
  have hJ : AnalyticAt ℂ J (0, 0) := by
    have hraw := analyticAt_hughesYoungEquation96ContinuationJet_all
      (h := a) (k := b) (q := q) (z := (0 : ℂ)) (w := (0 : ℂ))
      hq (by norm_num) (by norm_num)
    simpa only [J, q] using hraw.curry_right
  have hleft_eventually :
      (fun w => deriv (fun z => J (z, w) * P (z, w)) 0) =ᶠ[nhds (0 : ℂ)]
        fun w =>
          deriv (fun z => J (z, w)) 0 * P (0, w) +
            J (0, w) *
              (hughesYoungEquation84Kernel10 t W +
                w * hughesYoungEquation84Kernel00 t W) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ)
        (by norm_num : (0 : ℝ) < 1 / 32)] with w hw
    have hwNorm : ‖w‖ < (1 / 8 : ℝ) := by
      have : ‖w‖ < (1 / 32 : ℝ) := by
        simpa [Metric.mem_ball, dist_zero_right] using hw
      linarith
    have hJw : DifferentiableAt ℂ (fun z => J (z, w)) 0 := by
      have hAt : AnalyticAt ℂ J (0, w) := by
        simpa only [J, q] using (analyticAt_hughesYoungEquation96ContinuationJet_all
        (h := a) (k := b) (q := q) (z := (0 : ℂ)) (w := w)
        hq (by norm_num) hwNorm).curry_right
      exact hAt.curry_left.differentiableAt
    have hPw :=
      hasDerivAt_hughesYoungCentralReverseKernelPolynomial_left t W 0 w
    simpa only [P] using (hJw.hasDerivAt.mul hPw).deriv
  change deriv (fun w => deriv (fun z => J (z, w) * P (z, w)) 0) 0 = _
  rw [hleft_eventually.deriv_eq]
  have hJz : DifferentiableAt ℂ (fun w => deriv (fun z => J (z, w)) 0) 0 := by
    have h := hJ.fderiv
    exact (((ContinuousLinearMap.apply ℂ ℂ ((1, 0) : ℂ × ℂ)).analyticAt _).comp'
      (f := fderiv ℂ J) (x := ((0, 0) : ℂ × ℂ)) h).curry_right.differentiableAt.congr_of_eventuallyEq
      (by
        filter_upwards [Metric.ball_mem_nhds (0 : ℂ)
            (by norm_num : (0 : ℝ) < 1 / 32)] with w hw
        have hwNorm : ‖w‖ < (1 / 8 : ℝ) := by
          have : ‖w‖ < (1 / 32 : ℝ) := by
            simpa [Metric.mem_ball, dist_zero_right] using hw
          linarith
        have hslice : HasDerivAt (fun z => J (z, w))
            ((fderiv ℂ J (0, w)) (1, 0)) 0 := by
          have hAt : AnalyticAt ℂ J (0, w) := by
            simpa only [J, q] using
              (analyticAt_hughesYoungEquation96ContinuationJet_all
                (h := a) (k := b) (q := q) (z := (0 : ℂ)) (w := w)
                hq (by norm_num) hwNorm).curry_right
          exact hAt.differentiableAt.hasFDerivAt.comp_hasDerivAt 0
            ((hasDerivAt_id (x := (0 : ℂ))).prodMk
              (hasDerivAt_const (x := (0 : ℂ)) w))
        exact hslice.deriv)
  have hP0 : HasDerivAt (fun w => P (0, w))
      (hughesYoungEquation84Kernel01 t W) 0 := by
    simpa only [P, zero_mul, zero_add, add_zero] using
      (hasDerivAt_hughesYoungCentralReverseKernelPolynomial_right
        t W 0 0)
  have hJ0 : DifferentiableAt ℂ (fun w => J (0, w)) 0 :=
    hJ.curry_right.differentiableAt
  have hlinear : HasDerivAt
      (fun w : ℂ => hughesYoungEquation84Kernel10 t W +
        w * hughesYoungEquation84Kernel00 t W)
      (hughesYoungEquation84Kernel00 t W) 0 := by
    convert (hasDerivAt_const (x := (0 : ℂ))
      (hughesYoungEquation84Kernel10 t W)).add
        ((hasDerivAt_id (x := (0 : ℂ))).mul_const
          (hughesYoungEquation84Kernel00 t W)) using 1
    all_goals ring_nf
  have hout := (hJz.hasDerivAt.mul hP0).add (hJ0.hasDerivAt.mul hlinear)
  have houter :
      deriv (fun w =>
        deriv (fun z => J (z, w)) 0 * P (0, w) +
          J (0, w) * (hughesYoungEquation84Kernel10 t W +
            w * hughesYoungEquation84Kernel00 t W)) 0 =
        deriv (fun w => deriv (fun z => J (z, w)) 0) 0 * P (0, 0) +
          deriv (fun z => J (z, 0)) 0 * hughesYoungEquation84Kernel01 t W +
          (deriv (fun w => J (0, w)) 0 *
              (hughesYoungEquation84Kernel10 t W +
                0 * hughesYoungEquation84Kernel00 t W) +
            J (0, 0) * hughesYoungEquation84Kernel00 t W) := by
    simpa only [Pi.add_apply, Pi.mul_apply] using hout.deriv
  rw [houter]
  unfold hughesYoungEquation96ContinuationCoefficient
  simp only [J, P, hughesYoungCentralReverseKernelPolynomial]
  ring

/-- The full positive central master integrand, including the arithmetic
normalization and the two mollifier coefficients. -/
noncomputable def hughesYoungCompletePositiveCentralMaster
    (T t : ℝ) (h k a b : ℕ) (W z w : ℂ) : ℂ :=
  (((a : ℂ) * b)⁻¹) *
    hughesYoungReducedMellinStaticComplex T t h k W *
      hughesYoungCentralMasterJet t a b W z w

/-- The existing complete positive continuation is exactly the mixed
auxiliary derivative of the full master integrand. -/
theorem deriv_right_deriv_left_hughesYoungCompletePositiveCentralMaster_zero
    (T t : ℝ) (h k : ℕ) {a b : ℕ} (W : ℂ)
    (hW : (7 / 8 : ℝ) < W.re) :
    deriv (fun w => deriv
      (fun z => hughesYoungCompletePositiveCentralMaster
        T t h k a b W z w) 0) 0 =
      hughesYoungCompletePositiveCentralContinuation T t h k a b W := by
  let O : ℂ := (((a : ℂ) * b)⁻¹) *
    hughesYoungReducedMellinStaticComplex T t h k W
  let F : ℂ → ℂ → ℂ := fun z w =>
    hughesYoungCentralMasterJet t a b W z w
  change deriv (fun w => deriv (fun z => O * F z w) 0) 0 = _
  simp_rw [deriv_const_mul_field O]
  rw [deriv_right_deriv_left_hughesYoungCentralMasterJet_zero t W hW]
  unfold hughesYoungCompletePositiveCentralContinuation O
  rfl

/-- The equation-(98) master jet with its unique moving zeta pole removed. -/
noncomputable def hughesYoungEquation96PoleFreeMasterJet
    (h k : ℕ) (W z w : ℂ) : ℂ :=
  Complex.exp
      (z * hughesYoungEquation96LeftConstant h +
        w * hughesYoungEquation96RightConstant k) *
    ((riemannZeta (1 + 2 * W + z + w) /
        riemannZeta (2 + 2 * z + 2 * w)) *
      (hughesYoungC h (-z) z (-w) w W *
        hughesYoungC k (-w) w (-z) z W))

/-- Exact isolation of the single source pole `2W-z-w=1`. -/
theorem hughesYoungEquation96ContinuationJet_contourParameter_eq_pole_mul
    (h k : ℕ) (W z w : ℂ) :
    hughesYoungEquation96ContinuationJet h k
        (hughesYoungEquation96ContourParameter W) z w =
      riemannZeta (2 * W - z - w) *
        hughesYoungEquation96PoleFreeMasterJet h k W z w := by
  unfold hughesYoungEquation96ContinuationJet
    hughesYoungEquation96ContourParameter
    hughesYoungEquation96PoleFreeMasterJet
  ring_nf

/-- The full pole-free numerator multiplying the moving zeta pole. -/
noncomputable def hughesYoungCompletePositiveCentralPoleFree
    (T t : ℝ) (h k a b : ℕ) (W z w : ℂ) : ℂ :=
  (((a : ℂ) * b)⁻¹) *
    hughesYoungReducedMellinStaticComplex T t h k W *
      (hughesYoungEquation96PoleFreeMasterJet a b W z w *
        hughesYoungCentralReverseKernelPolynomial t W z w)

/-- The `hughesYoungCompletePositiveCentralPoleFreeCore` definition used by the source-facing construction in `HughesYoungCentralMaster`. -/
noncomputable def hughesYoungCompletePositiveCentralPoleFreeCore
    (T t : ℝ) (h k a b : ℕ) (W z w : ℂ) : ℂ :=
  (((a : ℂ) * b)⁻¹) *
    hughesYoungReducedMellinStaticComplex T t h k W *
      (hughesYoungEquation96PoleFreeMasterJet a b W z w *
        hughesYoungCentralReverseKernelPolynomialCore t W z w)

theorem hughesYoungCompletePositiveCentralPoleFree_eq_auxiliary_mul_core
    (T t : ℝ) (h k a b : ℕ) (W z w : ℂ) :
    hughesYoungCompletePositiveCentralPoleFree T t h k a b W z w =
      hughesYoungAuxiliaryZero W *
        hughesYoungCompletePositiveCentralPoleFreeCore T t h k a b W z w := by
  unfold hughesYoungCompletePositiveCentralPoleFree
    hughesYoungCompletePositiveCentralPoleFreeCore
  rw [hughesYoungCentralReverseKernelPolynomial_eq_auxiliary_mul_core]
  ring

theorem hughesYoungCompletePositiveCentralMaster_eq_pole_mul
    (T t : ℝ) (h k a b : ℕ) (W z w : ℂ) :
    hughesYoungCompletePositiveCentralMaster T t h k a b W z w =
      riemannZeta (2 * W - z - w) *
        hughesYoungCompletePositiveCentralPoleFree T t h k a b W z w := by
  unfold hughesYoungCompletePositiveCentralMaster
    hughesYoungCentralMasterJet
    hughesYoungCompletePositiveCentralPoleFree
  rw [hughesYoungEquation96ContinuationJet_contourParameter_eq_pole_mul]
  ring

/-- Holomorphy in the central variable of the finite Euler correction on
the full source strip.  The two displayed inequalities are exactly the
nonvanishing conditions for the denominators in equation (100). -/
theorem differentiableAt_hughesYoungC_symmetric_center
    (n : ℕ) {W z w : ℂ}
    (hregular : (-2 - 2 * z - 2 * w : ℂ).re < 0)
    (hcenter : (z - w - 2 * W : ℂ).re < 0) :
    DifferentiableAt ℂ
      (fun V => hughesYoungC n (-z) z (-w) w V) W := by
  unfold hughesYoungC
  apply DifferentiableAt.fun_finsetProd
  intro p hp
  have hp0 : ((p : Nat.Primes) : ℂ) ≠ 0 := by
    exact_mod_cast p.2.ne_zero
  have hpSlit : ((p : Nat.Primes) : ℂ) ∈ Complex.slitPlane := by
    exact Complex.natCast_mem_slitPlane.mpr p.2.ne_zero
  have hreg :
      1 - ((p : Nat.Primes) : ℂ) ^ (-2 - 2 * z - 2 * w) ≠ 0 := by
    apply one_sub_prime_cpow_ne_zero_of_re_neg p
    exact hregular
  have hx :
      1 - ((p : Nat.Primes) : ℂ) ^ (z - w - 2 * W) ≠ 0 := by
    apply one_sub_prime_cpow_ne_zero_of_re_neg p
    exact hcenter
  have hden :
      (1 - (p : ℂ) ^ (-2 + -z - z + -w - w)) *
          (1 - (p : ℂ) ^ (- -z - w - 2 * W)) ≠ 0 := by
    apply mul_ne_zero
    · convert hreg using 1
      ring_nf
    · convert hx using 1
      ring_nf
  unfold hughesYoungCPrimeFactor hughesYoungCPrimeNumerator
    hughesYoungC0 hughesYoungC1 hughesYoungC2
  dsimp only
  fun_prop (disch := first | exact hden | exact Or.inl hp0 | exact hpSlit)

/-- The pole-free equation-(98) master jet is holomorphic in `W` whenever
the zeta denominator and both finite Euler-product denominators stay away
from their poles. -/
theorem differentiableAt_hughesYoungEquation96PoleFreeMasterJet
    (h k : ℕ) {W z w : ℂ}
    (hzeta : 1 < (1 + 2 * W + z + w : ℂ).re)
    (hzetaDen : 1 ≤ (2 + 2 * z + 2 * w : ℂ).re)
    (hregular : (-2 - 2 * z - 2 * w : ℂ).re < 0)
    (hleft : (z - w - 2 * W : ℂ).re < 0)
    (hright : (w - z - 2 * W : ℂ).re < 0) :
    DifferentiableAt ℂ
      (fun V => hughesYoungEquation96PoleFreeMasterJet h k V z w) W := by
  have hzetaNe : (1 + 2 * W + z + w : ℂ) ≠ 1 := by
    intro heq
    rw [heq] at hzeta
    norm_num at hzeta
  have hdenNe : riemannZeta (2 + 2 * z + 2 * w) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re hzetaDen
  have hZ : DifferentiableAt ℂ
      (fun V => riemannZeta (1 + 2 * V + z + w)) W :=
    (differentiableAt_riemannZeta hzetaNe).comp W (by fun_prop)
  have hCh := differentiableAt_hughesYoungC_symmetric_center
    h hregular hleft
  have hregularSwap : (-2 - 2 * w - 2 * z : ℂ).re < 0 := by
    convert hregular using 1
    ring_nf
  have hCk := differentiableAt_hughesYoungC_symmetric_center
    k (z := w) (w := z) hregularSwap (by simpa [sub_eq_add_neg] using hright)
  unfold hughesYoungEquation96PoleFreeMasterJet
  exact (differentiableAt_const (c := Complex.exp
      (z * hughesYoungEquation96LeftConstant h +
        w * hughesYoungEquation96RightConstant k))).mul
    ((hZ.div (differentiableAt_const
      (c := riemannZeta (2 + 2 * z + 2 * w))) hdenNe).mul
      (hCh.mul hCk))

theorem differentiableAt_hughesYoungCentralReverseKernelPolynomial_center
    (t : ℝ) {W z w : ℂ} (hW0 : 0 < W.re)
    (hW3 : W.re < 3 / 2) :
    DifferentiableAt ℂ
      (fun V => hughesYoungCentralReverseKernelPolynomial t V z w) W := by
  unfold hughesYoungCentralReverseKernelPolynomial
  exact (((differentiableAt_hughesYoungEquation84Kernel11 t hW0 hW3).add
    ((differentiableAt_const (c := z)).mul
      (differentiableAt_hughesYoungEquation84Kernel10 t hW0 hW3))).add
    ((differentiableAt_const (c := w)).mul
      (differentiableAt_hughesYoungEquation84Kernel01 t hW0 hW3))).add
    (((differentiableAt_const (c := z)).mul
      (differentiableAt_const (c := w))).mul
      (differentiableAt_hughesYoungEquation84Kernel00 t hW0 hW3))

theorem differentiableAt_hughesYoungCentralReverseKernelPolynomialCore_center
    (t : ℝ) {W z w : ℂ} (hW0 : 0 < W.re)
    (hW3 : W.re < 3 / 2) :
    DifferentiableAt ℂ
      (fun V => hughesYoungCentralReverseKernelPolynomialCore t V z w) W := by
  unfold hughesYoungCentralReverseKernelPolynomialCore
  exact (((differentiableAt_hughesYoungEquation84KernelCore11 t hW0 hW3).add
    ((differentiableAt_const (c := z)).mul
      (differentiableAt_hughesYoungEquation84KernelCore10 t hW0 hW3))).add
    ((differentiableAt_const (c := w)).mul
      (differentiableAt_hughesYoungEquation84KernelCore01 t hW0 hW3))).add
    (((differentiableAt_const (c := z)).mul
      (differentiableAt_const (c := w))).mul
      (differentiableAt_hughesYoungEquation84KernelCore00 t hW0 hW3))

/-- Holomorphy of the complete pole-free numerator on the contour-shift
rectangle. -/
theorem differentiableAt_hughesYoungCompletePositiveCentralPoleFree
    (T t : ℝ) (h k a b : ℕ) {W z w : ℂ}
    (hW0 : 0 < W.re) (hW3 : W.re < 3 / 2)
    (hzeta : 1 < (1 + 2 * W + z + w : ℂ).re)
    (hzetaDen : 1 ≤ (2 + 2 * z + 2 * w : ℂ).re)
    (hregular : (-2 - 2 * z - 2 * w : ℂ).re < 0)
    (hleft : (z - w - 2 * W : ℂ).re < 0)
    (hright : (w - z - 2 * W : ℂ).re < 0) :
    DifferentiableAt ℂ
      (fun V => hughesYoungCompletePositiveCentralPoleFree
        T t h k a b V z w) W := by
  unfold hughesYoungCompletePositiveCentralPoleFree
  convert (differentiableAt_const (c := (((a : ℂ) * b)⁻¹)).mul
    ((differentiableAt_hughesYoungReducedMellinStaticComplex T t h k W).mul
      ((differentiableAt_hughesYoungEquation96PoleFreeMasterJet
          a b hzeta hzetaDen hregular hleft hright).mul
        (differentiableAt_hughesYoungCentralReverseKernelPolynomial_center
          t (z := z) (w := w) hW0 hW3)))) using 1
  funext V
  simp only [Pi.mul_apply]
  ring

end RiemannZeta.GuthMaynard
