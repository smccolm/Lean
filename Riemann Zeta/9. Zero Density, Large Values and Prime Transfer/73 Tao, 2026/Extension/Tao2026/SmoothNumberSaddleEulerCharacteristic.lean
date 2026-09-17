import Tao2026.SmoothNumberSaddleProbability

/-!
# Euler product for the tilted characteristic function

The Fourier series of the tilted logarithmic law is factored here into its
finite prime-local geometric factors.  This is the exact product needed for
the frequency estimates in the Gaussian local-limit argument.
-/

namespace Tao2026

noncomputable section

/-- The unnormalized Fourier weight of a positive integer. -/
noncomputable def smoothFourierWeight (sigma t : ℝ) (n : ℕ) : ℂ :=
  (((n : ℝ) ^ (-sigma) : ℝ) : ℂ) *
    Complex.exp ((t * Real.log (n : ℝ) : ℝ) * Complex.I)

/-- The prime-local ratio in the Fourier Euler product. -/
noncomputable def smoothFourierPrimeRatio
    (p : ℕ) (sigma t : ℝ) : ℂ :=
  smoothFourierWeight sigma t p

/-- The unnormalized Fourier series over positive `k`-smooth integers. -/
noncomputable def smoothFourierDirichletSeries
    (k : ℕ) (sigma t : ℝ) : ℂ :=
  ∑' n : Nat.smoothNumbers k, smoothFourierWeight sigma t n.1

/-- The finite Euler product for the unnormalized Fourier series. -/
noncomputable def smoothFourierEulerProduct
    (k : ℕ) (sigma t : ℝ) : ℂ :=
  ∏ p ∈ k.primesBelow,
    (1 - smoothFourierPrimeRatio p sigma t)⁻¹

/-- The normalized characteristic factor contributed by a single prime. -/
noncomputable def smoothTiltedPrimeCharacteristic
    (p : ℕ) (sigma t : ℝ) : ℂ :=
  (((1 - (p : ℝ) ^ (-sigma) : ℝ) : ℂ) /
    (1 - smoothFourierPrimeRatio p sigma t))

/-- Fourier weights multiply on positive natural inputs. -/
theorem smoothFourierWeight_mul
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (sigma t : ℝ) :
    smoothFourierWeight sigma t (m * n) =
      smoothFourierWeight sigma t m * smoothFourierWeight sigma t n := by
  unfold smoothFourierWeight
  rw [natCast_rpow_neg_mul, Nat.cast_mul,
    Real.log_mul (by exact_mod_cast hm) (by exact_mod_cast hn)]
  rw [mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]
  push_cast
  ring

/-- Fourier weights of prime powers form the expected geometric sequence. -/
theorem smoothFourierWeight_pow
    {p : ℕ} (hp : p ≠ 0) (e : ℕ) (sigma t : ℝ) :
    smoothFourierWeight sigma t (p ^ e) =
      (smoothFourierPrimeRatio p sigma t) ^ e := by
  induction e with
  | zero => simp [smoothFourierWeight, smoothFourierPrimeRatio]
  | succ e ih =>
      rw [pow_succ, smoothFourierWeight_mul (pow_ne_zero _ hp) hp, ih]
      rfl

/-- The norm of a Fourier weight is its underlying positive Rankin weight. -/
theorem norm_smoothFourierWeight
    {n : ℕ} (hn : n ≠ 0) (sigma t : ℝ) :
    ‖smoothFourierWeight sigma t n‖ = (n : ℝ) ^ (-sigma) := by
  unfold smoothFourierWeight
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) _),
    Complex.norm_exp_ofReal_mul_I, mul_one]

/-- The prime-local Fourier ratio has norm strictly below one in the positive
half-plane. -/
theorem norm_smoothFourierPrimeRatio_lt_one
    {p : ℕ} (hp : 1 < p) {sigma : ℝ} (hsigma : 0 < sigma) (t : ℝ) :
    ‖smoothFourierPrimeRatio p sigma t‖ < 1 := by
  rw [smoothFourierPrimeRatio,
    norm_smoothFourierWeight (Nat.ne_zero_of_lt hp)]
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast hp) (neg_neg_of_pos hsigma)

/-- The unnormalized Fourier series is absolutely summable in the positive
half-plane. -/
theorem summable_smoothFourierDirichletSeries
    (k : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) (t : ℝ) :
    Summable fun n : Nat.smoothNumbers k =>
      smoothFourierWeight sigma t n.1 := by
  apply Summable.of_norm
  refine (summable_smoothDirichletSeries_and_eq_eulerProduct k hsigma).1.congr
    (fun n => ?_)
  exact (norm_smoothFourierWeight
    (Nat.ne_zero_of_mem_smoothNumbers n.2) sigma t).symm

/-- Exact finite-prime Euler product for the Fourier Dirichlet series. -/
theorem smoothFourierDirichletSeries_eq_eulerProduct
    (k : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) (t : ℝ) :
    smoothFourierDirichletSeries k sigma t =
      smoothFourierEulerProduct k sigma t := by
  induction k with
  | zero =>
      have hone : Nat.smoothNumbers 0 = ({1} : Set ℕ) :=
        Nat.smoothNumbers_zero
      rw [smoothFourierDirichletSeries, smoothFourierEulerProduct, hone]
      simp [smoothFourierWeight]
  | succ k ih =>
      by_cases hk : k.Prime
      · have hkTwo : 1 < k := hk.one_lt
        let r : ℂ := smoothFourierPrimeRatio k sigma t
        have hr : ‖r‖ < 1 :=
          norm_smoothFourierPrimeRatio_lt_one hkTwo hsigma t
        have hgeom : Summable (fun e : ℕ => r ^ e) :=
          summable_geometric_of_norm_lt_one hr
        have hgeomNorm : Summable (fun e : ℕ => ‖r ^ e‖) :=
          summable_norm_geometric_of_norm_lt_one hr
        have hsmoothNorm : Summable
            (fun n : Nat.smoothNumbers k =>
              ‖smoothFourierWeight sigma t n.1‖) := by
          refine (summable_smoothDirichletSeries_and_eq_eulerProduct
            k hsigma).1.congr (fun n => ?_)
          exact (norm_smoothFourierWeight
            (Nat.ne_zero_of_mem_smoothNumbers n.2) sigma t).symm
        have hprod : Summable
            (fun em : ℕ × Nat.smoothNumbers k =>
              r ^ em.1 * smoothFourierWeight sigma t em.2.1) :=
          summable_mul_of_summable_norm
            (R := ℂ) (f := fun e : ℕ => r ^ e)
            (g := fun n : Nat.smoothNumbers k =>
              smoothFourierWeight sigma t n.1)
            hgeomNorm hsmoothNorm
        have hprimes :
            (k + 1).primesBelow = insert k k.primesBelow := by
          ext p
          simp only [Nat.mem_primesBelow, Finset.mem_insert]
          constructor
          · intro hp
            by_cases hpk : p = k
            · exact Or.inl hpk
            · exact Or.inr ⟨by omega, hp.2⟩
          · rintro (hpk | hp)
            · subst p
              exact ⟨Nat.lt_succ_self k, hk⟩
            · exact ⟨hp.1.trans (Nat.lt_succ_self k), hp.2⟩
        have hknot : k ∉ k.primesBelow := by
          simp [Nat.mem_primesBelow]
        have hweight (em : ℕ × Nat.smoothNumbers k) :
            smoothFourierWeight sigma t (k ^ em.1 * em.2.1) =
              r ^ em.1 * smoothFourierWeight sigma t em.2.1 := by
          rw [smoothFourierWeight_mul
            (pow_ne_zero _ hk.ne_zero)
            (Nat.ne_zero_of_mem_smoothNumbers em.2.2),
            smoothFourierWeight_pow hk.ne_zero]
        rw [smoothFourierDirichletSeries,
          ← (Nat.equivProdNatSmoothNumbers hk).tsum_eq]
        simp_rw [Nat.equivProdNatSmoothNumbers_apply', hweight]
        change (∑' em : ℕ × Nat.smoothNumbers k,
          r ^ em.1 * smoothFourierWeight sigma t em.2.1) = _
        rw [hprod.tsum_prod]
        simp_rw [tsum_mul_left]
        rw [tsum_mul_right,
          hasSum_geom_series_inverse r hr |>.tsum_eq]
        rw [← smoothFourierDirichletSeries, ih]
        unfold smoothFourierEulerProduct
        rw [hprimes, Finset.prod_insert hknot]
        simp only [r, Ring.inverse_eq_inv]
      · have hsmooth :
            Nat.smoothNumbers (k + 1) = Nat.smoothNumbers k :=
          Nat.smoothNumbers_succ hk
        have hprimes : (k + 1).primesBelow = k.primesBelow := by
          ext p
          simp only [Nat.mem_primesBelow]
          constructor
          · intro hp
            refine ⟨?_, hp.2⟩
            by_contra hpk
            have : p = k :=
              Nat.le_antisymm (Nat.le_of_lt_succ hp.1) (Nat.not_lt.mp hpk)
            exact hk (this ▸ hp.2)
          · exact fun hp => ⟨hp.1.trans (Nat.lt_succ_self k), hp.2⟩
        rw [smoothFourierDirichletSeries, hsmooth,
          ← smoothFourierDirichletSeries, ih]
        unfold smoothFourierEulerProduct
        rw [hprimes]

/-- The tilted characteristic function is the twisted Dirichlet series
divided by its untwisted normalizing series. -/
theorem smoothTiltedCharacteristic_eq_fourierDirichletSeries_div
    (y : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) (t : ℝ) :
    smoothTiltedCharacteristic y sigma t =
      smoothFourierDirichletSeries (y + 1) sigma t /
        (smoothDirichletSeries (y + 1) sigma : ℂ) := by
  rw [smoothTiltedCharacteristic_eq_tsum y hsigma t]
  unfold smoothFourierDirichletSeries
  rw [← tsum_div_const]
  apply tsum_congr
  intro n
  unfold smoothTiltedMass smoothFourierWeight
  push_cast
  ring

/-- Euler-product form of the tilted characteristic function before the
source-prime indexing is exposed. -/
theorem smoothTiltedCharacteristic_eq_fourierEulerProduct_div
    (y : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) (t : ℝ) :
    smoothTiltedCharacteristic y sigma t =
      smoothFourierEulerProduct (y + 1) sigma t /
        (smoothEulerProduct (y + 1) sigma : ℂ) := by
  rw [smoothTiltedCharacteristic_eq_fourierDirichletSeries_div y hsigma t,
    smoothFourierDirichletSeries_eq_eulerProduct (y + 1) hsigma t,
    (summable_smoothDirichletSeries_and_eq_eulerProduct
      (y + 1) hsigma).2]

/-- A normalized prime characteristic factor is the quotient of its twisted
and untwisted inverse Euler factors. -/
theorem smoothTiltedPrimeCharacteristic_eq_inv_div_inv
    {p : ℕ} (hp : 1 < p) {sigma : ℝ} (hsigma : 0 < sigma) (t : ℝ) :
    smoothTiltedPrimeCharacteristic p sigma t =
      (1 - smoothFourierPrimeRatio p sigma t)⁻¹ /
        (((1 - (p : ℝ) ^ (-sigma))⁻¹ : ℝ) : ℂ) := by
  have haLt : (p : ℝ) ^ (-sigma) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast hp) (neg_neg_of_pos hsigma)
  have haNe : (1 - (p : ℝ) ^ (-sigma)) ≠ 0 :=
    (sub_pos.mpr haLt).ne'
  have hrNe : 1 - smoothFourierPrimeRatio p sigma t ≠ 0 := by
    apply sub_ne_zero.mpr
    intro heq
    have hnorm := norm_smoothFourierPrimeRatio_lt_one hp hsigma t
    rw [← heq, norm_one] at hnorm
    exact (lt_irrefl 1 hnorm)
  unfold smoothTiltedPrimeCharacteristic
  push_cast
  field_simp [haNe, hrNe]

/-- The tilted characteristic function is the product of its normalized
prime-local characteristic factors. -/
theorem smoothTiltedCharacteristic_eq_primeProduct
    (y : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) (t : ℝ) :
    smoothTiltedCharacteristic y sigma t =
      ∏ p ∈ (y + 1).primesBelow,
        smoothTiltedPrimeCharacteristic p sigma t := by
  rw [smoothTiltedCharacteristic_eq_fourierEulerProduct_div y hsigma t]
  unfold smoothFourierEulerProduct smoothEulerProduct
  have hcast :
      ((∏ p ∈ (y + 1).primesBelow,
          (1 - (p : ℝ) ^ (-sigma))⁻¹ : ℝ) : ℂ) =
        ∏ p ∈ (y + 1).primesBelow,
          (((1 - (p : ℝ) ^ (-sigma))⁻¹ : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  exact (smoothTiltedPrimeCharacteristic_eq_inv_div_inv
    (Nat.mem_primesBelow.mp hp).2.one_lt hsigma t).symm

/-- Source-convention product over the literal primes `p ≤ y`. -/
theorem smoothTiltedCharacteristic_eq_sourcePrimeProduct
    (y : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) (t : ℝ) :
    smoothTiltedCharacteristic y sigma t =
      ∏ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
        smoothTiltedPrimeCharacteristic p sigma t := by
  rw [smoothTiltedCharacteristic_eq_primeProduct y hsigma t]
  congr 1
  ext p
  simp only [Nat.mem_primesBelow, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · exact fun hp => ⟨⟨hp.2.two_le, Nat.lt_succ_iff.mp hp.1⟩, hp.2⟩
  · exact fun hp => ⟨Nat.lt_succ_iff.mpr hp.1.2, hp.2⟩

/-- Each normalized prime-local factor has norm at most one. -/
theorem norm_smoothTiltedPrimeCharacteristic_le_one
    {p : ℕ} (hp : 1 < p) {sigma : ℝ} (hsigma : 0 < sigma) (t : ℝ) :
    ‖smoothTiltedPrimeCharacteristic p sigma t‖ ≤ 1 := by
  have haPos : 0 < (p : ℝ) ^ (-sigma) :=
    Real.rpow_pos_of_pos (by positivity) _
  have haLt : (p : ℝ) ^ (-sigma) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast hp) (neg_neg_of_pos hsigma)
  have hrnorm :
      ‖smoothFourierPrimeRatio p sigma t‖ = (p : ℝ) ^ (-sigma) :=
    norm_smoothFourierWeight (Nat.ne_zero_of_lt hp) sigma t
  have hdenPos :
      0 < ‖(1 : ℂ) - smoothFourierPrimeRatio p sigma t‖ := by
    rw [norm_pos_iff]
    apply sub_ne_zero.mpr
    intro heq
    have hlt := norm_smoothFourierPrimeRatio_lt_one hp hsigma t
    rw [← heq, norm_one] at hlt
    exact (lt_irrefl 1 hlt)
  have hnumDen :
      1 - (p : ℝ) ^ (-sigma) ≤
        ‖(1 : ℂ) - smoothFourierPrimeRatio p sigma t‖ := by
    calc
      1 - (p : ℝ) ^ (-sigma) =
          ‖(1 : ℂ)‖ - ‖smoothFourierPrimeRatio p sigma t‖ := by
            rw [norm_one, hrnorm]
      _ ≤ ‖(1 : ℂ) - smoothFourierPrimeRatio p sigma t‖ :=
        norm_sub_norm_le _ _
  unfold smoothTiltedPrimeCharacteristic
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (sub_pos.mpr haLt)]
  exact (div_le_one hdenPos).2 hnumDen

/-- Exact squared modulus of a prime-local Fourier denominator. -/
theorem norm_sq_one_sub_smoothFourierPrimeRatio
    {p : ℕ} (hp : 1 < p) (sigma t : ℝ) :
    ‖(1 : ℂ) - smoothFourierPrimeRatio p sigma t‖ ^ 2 =
      (1 - (p : ℝ) ^ (-sigma)) ^ 2 +
        2 * (p : ℝ) ^ (-sigma) *
          (1 - Real.cos (t * Real.log (p : ℝ))) := by
  have hrNormSq :
      Complex.normSq (smoothFourierPrimeRatio p sigma t) =
        ((p : ℝ) ^ (-sigma)) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, smoothFourierPrimeRatio,
      norm_smoothFourierWeight (Nat.ne_zero_of_lt hp)]
  have hrRe :
      (smoothFourierPrimeRatio p sigma t).re =
        (p : ℝ) ^ (-sigma) *
          Real.cos (t * Real.log (p : ℝ)) := by
    unfold smoothFourierPrimeRatio smoothFourierWeight
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, Complex.exp_ofReal_mul_I_re]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
  rw [hrNormSq]
  simp only [Complex.normSq_one, one_mul, Complex.conj_re, hrRe]
  ring

/-- Exact prime-local contraction formula.  Its denominator separates the
untwisted mass from the oscillatory loss `1 - cos(t log p)`. -/
theorem norm_smoothTiltedPrimeCharacteristic_sq
    {p : ℕ} (hp : 1 < p) {sigma : ℝ} (hsigma : 0 < sigma) (t : ℝ) :
    ‖smoothTiltedPrimeCharacteristic p sigma t‖ ^ 2 =
      (1 - (p : ℝ) ^ (-sigma)) ^ 2 /
        ((1 - (p : ℝ) ^ (-sigma)) ^ 2 +
          2 * (p : ℝ) ^ (-sigma) *
            (1 - Real.cos (t * Real.log (p : ℝ)))) := by
  have haLt : (p : ℝ) ^ (-sigma) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast hp) (neg_neg_of_pos hsigma)
  unfold smoothTiltedPrimeCharacteristic
  rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (sub_pos.mpr haLt),
    norm_sq_one_sub_smoothFourierPrimeRatio hp]

/-- Exact finite-prime contraction product for the full tilted
characteristic function. -/
theorem norm_smoothTiltedCharacteristic_sq_eq_sourcePrimeProduct
    (y : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) (t : ℝ) :
    ‖smoothTiltedCharacteristic y sigma t‖ ^ 2 =
      ∏ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
        ((1 - (p : ℝ) ^ (-sigma)) ^ 2 /
          ((1 - (p : ℝ) ^ (-sigma)) ^ 2 +
            2 * (p : ℝ) ^ (-sigma) *
              (1 - Real.cos (t * Real.log (p : ℝ))))) := by
  rw [smoothTiltedCharacteristic_eq_sourcePrimeProduct y hsigma t,
    norm_prod, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro p hp
  exact norm_smoothTiltedPrimeCharacteristic_sq
    (Nat.Prime.one_lt (Finset.mem_filter.mp hp).2) hsigma t

/-- Exact contraction product for the centered variance-normalized saddle
characteristic function.  The centering phase disappears from the norm. -/
theorem norm_smoothSaddleNormalizedCharacteristic_sq_eq_sourcePrimeProduct
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) (t : ℝ) :
    ‖smoothSaddleNormalizedCharacteristic X y t‖ ^ 2 =
      ∏ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
        ((1 - (p : ℝ) ^ (-smoothSaddlePoint X y)) ^ 2 /
          ((1 - (p : ℝ) ^ (-smoothSaddlePoint X y)) ^ 2 +
            2 * (p : ℝ) ^ (-smoothSaddlePoint X y) *
              (1 - Real.cos
                ((t / smoothSaddleStandardDeviation X y) *
                  Real.log (p : ℝ))))) := by
  rw [smoothSaddleNormalizedCharacteristic, norm_mul,
    Complex.norm_exp_ofReal_mul_I, one_mul,
    norm_smoothTiltedCharacteristic_sq_eq_sourcePrimeProduct y
      (smoothSaddlePoint_pos hX hy)]

/-- Every prime-local characteristic factor is one at frequency zero. -/
@[simp]
theorem smoothTiltedPrimeCharacteristic_zero
    {p : ℕ} (hp : 1 < p) {sigma : ℝ} (hsigma : 0 < sigma) :
    smoothTiltedPrimeCharacteristic p sigma 0 = 1 := by
  have haLt : (p : ℝ) ^ (-sigma) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast hp) (neg_neg_of_pos hsigma)
  have haNe : (1 - (p : ℝ) ^ (-sigma)) ≠ 0 :=
    (sub_pos.mpr haLt).ne'
  unfold smoothTiltedPrimeCharacteristic smoothFourierPrimeRatio
    smoothFourierWeight
  simp only [zero_mul, Complex.ofReal_zero, Complex.exp_zero, mul_one]
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
  exact div_self (Complex.ofReal_ne_zero.mpr haNe)

/-- At the exact saddle, the normalized characteristic function is a single
centering phase times the literal source-prime product. -/
theorem smoothSaddleNormalizedCharacteristic_eq_sourcePrimeProduct
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) (t : ℝ) :
    smoothSaddleNormalizedCharacteristic X y t =
      Complex.exp
          ((-(t * Real.log X / smoothSaddleStandardDeviation X y) : ℝ) *
            Complex.I) *
        ∏ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
          smoothTiltedPrimeCharacteristic p (smoothSaddlePoint X y)
            (t / smoothSaddleStandardDeviation X y) := by
  rw [smoothSaddleNormalizedCharacteristic,
    smoothTiltedCharacteristic_eq_sourcePrimeProduct y
      (smoothSaddlePoint_pos hX hy)]

end

end Tao2026
