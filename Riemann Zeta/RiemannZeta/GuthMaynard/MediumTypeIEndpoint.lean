import RiemannZeta.GuthMaynard.ClassicalEndpointSlab

open Asymptotics Filter Topology
open Complex Finset MeasureTheory Real Set
open scoped BigOperators ContDiff FourierTransform SchwartzMap

namespace RiemannZeta.GuthMaynard

/-!
# The medium Type-I endpoint consumer

This file closes the one reflected Type-I window left between the direct
endpoint estimate and the finite powering range.  The first lemmas expose
the genuine Bochner-integrability and norm bounds of the common Mellin
integrand.  They are kept separate from the final witness consumer so that
the passage from a source block to a fixed-coefficient reflected polynomial
is visible to the dependency audit.
-/

/-! ## Interval-form reflected polynomials

The endpoint argument cannot use the prefix `1 ≤ m ≤ M`: a dyadic
subblock selected from that prefix could be much shorter than the genuine
dual scale `T / N`.  The following definitions and identity retain an
arbitrary common interval of Fourier modes.  They are the exact Lean
counterpart of first restricting the B-process to its stationary annulus
and only then applying dyadic pigeonholing.
-/

/-- The fixed reflected polynomial on a literal natural interval. -/
noncomputable def typeIReflectedIntervalFixedPolynomial
    (sigma u : ℝ) (L U : ℕ) : ℂ :=
  ∑ m ∈ Finset.Ioc L U,
    ((((m : ℝ) ^ sigma : ℝ) : ℂ) *
      (m : ℂ) ^ ((u : ℂ) * Complex.I))

/-- The Mellin polynomial on the same interval, before removing the
common physical scale and vertical Mellin phase. -/
noncomputable def typeIReflectedIntervalMellinPolynomial
    (sigma t Q : ℝ) (L U : ℕ) (r : ℝ) : ℂ :=
  ∑ m ∈ Finset.Ioc L U,
    typeIReflectionScaleFactor sigma t m *
      ((((m : ℝ) * Q : ℝ) : ℂ) *
        (((m : ℝ) * Q : ℝ) : ℂ) ^ ((r : ℂ) * Complex.I))

/-- The literal negative normalized Poisson modes on `L < m ≤ U`. -/
noncomputable def typeINormalizedNegativeInterval
    (sigma t : ℝ) (Q L U : ℕ) : ℂ :=
  ∑ m ∈ Finset.Ioc L U,
    (Q : ℂ) * typeINormalizedFourier sigma t
      ((Q : ℝ) * (-(m : ℝ)))

/-- The literal positive normalized Poisson modes on `L < m ≤ U`. -/
noncomputable def typeINormalizedPositiveInterval
    (sigma t : ℝ) (Q L U : ℕ) : ℂ :=
  ∑ m ∈ Finset.Ioc L U,
    (Q : ℂ) * typeINormalizedFourier sigma t
      ((Q : ℝ) * (m : ℝ))

/-- The retained negative prefix is the interval with left endpoint zero.
This small identity is used before splitting the Poisson modes into the
low, stationary, and high ranges. -/
theorem typeINormalizedNegativeModes_eq_zero_interval
    (sigma t : ℝ) (Q M : ℕ) :
    typeINormalizedNegativeModes sigma t Q M =
      typeINormalizedNegativeInterval sigma t Q 0 M := by
  unfold typeINormalizedNegativeModes typeINormalizedNegativeInterval
  congr 1

/-- Exact three-way partition of the retained negative Poisson modes.  In
particular the stationary interval is not replaced by a prefix, so every
later dyadic block remains at the physical dual scale. -/
theorem typeINormalizedNegativeModes_eq_three_intervals
    (sigma t : ℝ) (Q L U M : ℕ) (hLU : L ≤ U) (hUM : U ≤ M) :
    typeINormalizedNegativeModes sigma t Q M =
      typeINormalizedNegativeInterval sigma t Q 0 L +
      typeINormalizedNegativeInterval sigma t Q L U +
      typeINormalizedNegativeInterval sigma t Q U M := by
  rw [typeINormalizedNegativeModes_eq_zero_interval]
  unfold typeINormalizedNegativeInterval
  let f : ℕ → ℂ := fun m =>
    (Q : ℂ) * typeINormalizedFourier sigma t
      ((Q : ℝ) * (-(m : ℝ)))
  have hDisj₁ : Disjoint (Finset.Ioc 0 L) (Finset.Ioc L U) := by
    rw [Finset.disjoint_left]
    intro m hm₁ hm₂
    simp only [Finset.mem_Ioc] at hm₁ hm₂
    omega
  have hDisj₂ : Disjoint (Finset.Ioc 0 U) (Finset.Ioc U M) := by
    rw [Finset.disjoint_left]
    intro m hm₁ hm₂
    simp only [Finset.mem_Ioc] at hm₁ hm₂
    omega
  have hUnion₁ :=
    Finset.Ioc_union_Ioc_eq_Ioc (a := 0) (Nat.zero_le L) hLU
  have hUnion₂ :=
    Finset.Ioc_union_Ioc_eq_Ioc (a := 0) (Nat.zero_le U) hUM
  change (∑ m ∈ Finset.Ioc 0 M, f m) =
    (∑ m ∈ Finset.Ioc 0 L, f m) +
      (∑ m ∈ Finset.Ioc L U, f m) +
      ∑ m ∈ Finset.Ioc U M, f m
  rw [← hUnion₂, Finset.sum_union hDisj₂, ← hUnion₁,
    Finset.sum_union hDisj₁]

/-- The Jacobian and phase in the physical mode rescaling have the exact
power norm `m^(sigma-1)`. -/
theorem norm_typeIReflectionScaleFactor
    {sigma t m : ℝ} (hm : 0 < m) :
    ‖typeIReflectionScaleFactor sigma t m‖ = m ^ (sigma - 1) := by
  unfold typeIReflectionScaleFactor
  rw [norm_mul, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hm, Complex.norm_exp,
    Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, sub_self, mul_one]
  rw [Real.exp_zero, mul_one]
  rw [show sigma * Real.log m = Real.log m * sigma by ring]
  rw [← Real.rpow_def_of_pos hm]
  rw [← Real.rpow_neg_one, ← Real.rpow_add hm]
  congr 1
  ring

/-- Exact removal of the ordinate from an interval-form Mellin
polynomial. -/
theorem typeIReflectedIntervalMellinPolynomial_eq_fixed
    (sigma t Q : ℝ) (L U : ℕ) (r : ℝ) (hQ : 0 < Q) :
    typeIReflectedIntervalMellinPolynomial sigma t Q L U r =
      (Q : ℂ) * (Q : ℂ) ^ ((r : ℂ) * Complex.I) *
        typeIReflectedIntervalFixedPolynomial sigma (t + r) L U := by
  unfold typeIReflectedIntervalMellinPolynomial
    typeIReflectedIntervalFixedPolynomial typeIReflectionScaleFactor
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hmPos : 0 < m := lt_of_le_of_lt (Nat.zero_le L)
    (Finset.mem_Ioc.mp hm).1
  have hmReal : (0 : ℝ) < m := by exact_mod_cast hmPos
  have hmComplex : (m : ℂ) ≠ 0 := by exact_mod_cast hmPos.ne'
  have hQComplex : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hmLog : Complex.log (m : ℂ) = (Real.log (m : ℝ) : ℂ) :=
    (Complex.ofReal_log hmReal.le).symm
  have hQLog : Complex.log (Q : ℂ) = (Real.log Q : ℂ) :=
    (Complex.ofReal_log hQ.le).symm
  have hmSigma : ((((m : ℝ) ^ sigma : ℝ) : ℂ)) =
      Complex.exp (((sigma * Real.log (m : ℝ) : ℝ) : ℂ)) := by
    rw [Real.rpow_def_of_pos hmReal, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hMulCast : ((((m : ℝ) * Q : ℝ) : ℂ)) =
      (m : ℂ) * (Q : ℂ) := Complex.ofReal_mul (m : ℝ) Q
  have hMulPow : ((((m : ℝ) * Q : ℝ) : ℂ)) ^ ((r : ℂ) * Complex.I) =
      (m : ℂ) ^ ((r : ℂ) * Complex.I) *
        (Q : ℂ) ^ ((r : ℂ) * Complex.I) := by
    rw [hMulCast]
    exact Complex.mul_cpow_ofReal_nonneg hmReal.le hQ.le _
  rw [hMulPow, hMulCast, hmSigma,
    Complex.cpow_def_of_ne_zero hmComplex,
    Complex.cpow_def_of_ne_zero hQComplex,
    Complex.cpow_def_of_ne_zero hmComplex, hmLog, hQLog]
  field_simp [hmComplex]
  calc
    Complex.exp (((Real.log (m : ℝ) * t : ℝ) : ℂ) * Complex.I) *
          (m : ℂ) *
          Complex.exp (Complex.I * (Real.log (m : ℝ) : ℂ) * (r : ℂ)) =
        (m : ℂ) *
          (Complex.exp (((Real.log (m : ℝ) * t : ℝ) : ℂ) * Complex.I) *
            Complex.exp (Complex.I * (Real.log (m : ℝ) : ℂ) * (r : ℂ))) := by
      ring
    _ = (m : ℂ) * Complex.exp
          ((((Real.log (m : ℝ) * t : ℝ) : ℂ) * Complex.I) +
            Complex.I * (Real.log (m : ℝ) : ℂ) * (r : ℂ)) := by
      rw [Complex.exp_add]
    _ = (m : ℂ) * Complex.exp
          (Complex.I * (Real.log (m : ℝ) : ℂ) * ((t + r : ℝ) : ℂ)) := by
      congr 2
      push_cast
      ring

/-- Exact B-process assembly for a common interval `L < m ≤ U`.  The
common reflection interval is chosen from the extreme supports of the
interval, so every mode has the same oscillatory kernel. -/
theorem sum_typeIDyadicPhysicalIntegral_interval_eq_reflectedMellin
    {sigma t Q : ℝ} {L U : ℕ} (hsigma : 0 ≤ sigma)
    (hQ : 0 < Q) (hLU : L < U) :
    (∑ m ∈ Finset.Ioc L U,
        ∫ x in Q / 2..2 * Q,
          typeIDyadicPhysicalIntegrand sigma t m Q x) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          typeIReflectedIntervalMellinPolynomial sigma t Q L U r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r)
                ((((L + 1 : ℕ) : ℝ) * Q) / 2)
                (2 * (U : ℝ) * Q) := by
  let S := Finset.Ioc L U
  let A : ℝ := (((L + 1 : ℕ) : ℝ) * Q) / 2
  let B : ℝ := 2 * (U : ℝ) * Q
  have hA : 0 < A := by dsimp only [A]; positivity
  have hAB : A ≤ B := by
    dsimp only [A, B]
    have hCast : ((L + 1 : ℕ) : ℝ) ≤ U := by exact_mod_cast hLU
    nlinarith
  have hModeInt : ∀ m ∈ S,
      Integrable (fun r : ℝ =>
        typeIReflectionScaleFactor sigma t m *
          typeICommonMellinMode sigma t ((m : ℝ) * Q) A B r) := by
    intro m hm
    have hmData := Finset.mem_Ioc.mp hm
    have hmPos : (0 : ℝ) < m := by
      exact_mod_cast (lt_of_le_of_lt (Nat.zero_le L) hmData.1)
    exact (integrable_typeICommonMellinMode hsigma (mul_pos hmPos hQ)
      hA hAB).const_mul _
  calc
    (∑ m ∈ Finset.Ioc L U,
        ∫ x in Q / 2..2 * Q,
          typeIDyadicPhysicalIntegrand sigma t m Q x) =
      ∑ m ∈ S,
        (1 / (2 * Real.pi) : ℝ) •
          ∫ r : ℝ,
            typeIReflectionScaleFactor sigma t m *
              typeICommonMellinMode sigma t ((m : ℝ) * Q) A B r := by
        apply Finset.sum_congr rfl
        intro m hm
        have hmData := Finset.mem_Ioc.mp hm
        have hmOne : 1 ≤ m := by omega
        rw [typeIDyadicPhysicalIntegral_rescale
          (by exact_mod_cast (show 0 < m by omega) : (0 : ℝ) < m)
          hQ (by positivity) (by linarith)]
        have hOriginal :
            (∫ v : ℝ,
                typeIDyadicPhysicalIntegrand sigma t 1 ((m : ℝ) * Q) v) =
              ∫ v in (m : ℝ) * (Q / 2)..(m : ℝ) * (2 * Q),
                typeIDyadicPhysicalIntegrand sigma t 1 ((m : ℝ) * Q) v := by
          apply integral_typeIDyadicPhysicalIntegrand_eq_interval
            (mul_pos (by exact_mod_cast (show 0 < m by omega)) hQ)
          · exact le_of_eq (by ring)
          · exact le_of_eq (by ring)
        have hNatural :
            (∫ v : ℝ,
                typeIDyadicPhysicalIntegrand sigma t 1 ((m : ℝ) * Q) v) =
              ∫ v in A..B,
                typeIDyadicPhysicalIntegrand sigma t 1 ((m : ℝ) * Q) v := by
          apply integral_typeIDyadicPhysicalIntegrand_eq_interval
            (mul_pos (by exact_mod_cast (show 0 < m by omega)) hQ)
          · dsimp only [A]
            have hmLower : L + 1 ≤ m := by omega
            have hmLowerReal : ((L + 1 : ℕ) : ℝ) ≤ m := by
              exact_mod_cast hmLower
            nlinarith
          · dsimp only [B]
            have hmUpperReal : (m : ℝ) ≤ U := by exact_mod_cast hmData.2
            nlinarith
        rw [← hOriginal, hNatural]
        have hFun : typeIDyadicPhysicalIntegrand sigma t 1 ((m : ℝ) * Q) =
            fun v : ℝ =>
              (typeIDyadicCutoff (v / ((m : ℝ) * Q)) : ℂ) *
                (gmReflectionPowerWeight sigma v *
                  Complex.exp
                    (-((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))) := by
          funext v
          unfold typeIDyadicPhysicalIntegrand
          congr 3
          ring_nf
        rw [hFun]
        have hmPosReal : (0 : ℝ) < m := by
          exact_mod_cast (show 0 < m by omega)
        have hMellin := typeIDyadicRescaledIntegral_eq_mellinReflection
          (sigma := sigma) (t := t) (q := (m : ℝ) * Q)
          (A := A) (B := B) hsigma (mul_pos hmPosReal hQ) hA hAB
        rw [hMellin]
        unfold typeICommonMellinMode
        simp only [Complex.real_smul]
        rw [MeasureTheory.integral_const_mul]
        ring
    _ = (1 / (2 * Real.pi) : ℝ) •
        ∑ m ∈ S,
          ∫ r : ℝ,
            typeIReflectionScaleFactor sigma t m *
              typeICommonMellinMode sigma t ((m : ℝ) * Q) A B r := by
        rw [Finset.smul_sum]
    _ = (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          ∑ m ∈ S,
            typeIReflectionScaleFactor sigma t m *
              typeICommonMellinMode sigma t ((m : ℝ) * Q) A B r := by
        congr 1
        exact (MeasureTheory.integral_finsetSum S hModeInt).symm
    _ = (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          typeIReflectedIntervalMellinPolynomial sigma t Q L U r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r) A B := by
        congr 1
        apply MeasureTheory.integral_congr_ae
        filter_upwards with r
        unfold typeIReflectedIntervalMellinPolynomial
          typeICommonMellinMode
        rw [Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro m hm
        ring

/-- Exact source-normalized Mellin formula for a literal interval of
negative Poisson modes. -/
theorem sourceScalar_mul_negativeInterval_eq_reflectedMellinIntegral
    {sigma t : ℝ} {Q L U : ℕ} (hsigma : 0 ≤ sigma)
    (hQ : 0 < Q) (hLU : L < U) :
    typeISourceNormalizationScalar sigma t (Q : ℝ) *
        typeINormalizedNegativeInterval sigma t Q L U =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          typeIReflectedIntervalMellinPolynomial sigma t (Q : ℝ) L U r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r)
                ((((L + 1 : ℕ) : ℝ) * Q) / 2)
                (2 * (U : ℝ) * Q) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  rw [typeINormalizedNegativeInterval, Finset.mul_sum]
  calc
    ∑ m ∈ Finset.Ioc L U,
        typeISourceNormalizationScalar sigma t (Q : ℝ) *
          ((Q : ℂ) * typeINormalizedFourier sigma t
            ((Q : ℝ) * (-(m : ℝ)))) =
      ∑ m ∈ Finset.Ioc L U,
        ∫ x in (Q : ℝ) / 2..2 * (Q : ℝ),
          typeIDyadicPhysicalIntegrand sigma t (m : ℝ) (Q : ℝ) x := by
            apply Finset.sum_congr rfl
            intro m _hm
            exact sourceScalar_mul_normalizedFourier_neg_eq_physicalIntegral
              sigma t (Q : ℝ) m hQr
    _ = _ := sum_typeIDyadicPhysicalIntegral_interval_eq_reflectedMellin
      hsigma hQr hLU

/-- Exact positive-mode companion.  It is obtained by conjugating the
negative formula at the reversed ordinate, preserving cancellation within
the entire interval. -/
theorem sourceScalar_mul_positiveInterval_eq_reflectedMellinIntegral
    {sigma t : ℝ} {Q L U : ℕ} (hsigma : 0 ≤ sigma)
    (hQ : 0 < Q) (hLU : L < U) :
    typeISourceNormalizationScalar sigma t (Q : ℝ) *
        typeINormalizedPositiveInterval sigma t Q L U =
      star ((1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          typeIReflectedIntervalMellinPolynomial sigma (-t) (Q : ℝ) L U r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (-t + r)
                ((((L + 1 : ℕ) : ℝ) * Q) / 2)
                (2 * (U : ℝ) * Q)) := by
  rw [typeINormalizedPositiveInterval, Finset.mul_sum]
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  calc
    ∑ m ∈ Finset.Ioc L U,
        typeISourceNormalizationScalar sigma t (Q : ℝ) *
          ((Q : ℂ) * typeINormalizedFourier sigma t
            ((Q : ℝ) * (m : ℝ))) =
      ∑ m ∈ Finset.Ioc L U,
        star (∫ x in (Q : ℝ) / 2..2 * (Q : ℝ),
          typeIDyadicPhysicalIntegrand sigma (-t) (m : ℝ) (Q : ℝ) x) := by
            apply Finset.sum_congr rfl
            intro m _hm
            exact sourceScalar_mul_normalizedFourier_pos_eq_conj_physicalIntegral
              sigma t (Q : ℝ) m hQr
    _ = star (∑ m ∈ Finset.Ioc L U,
        ∫ x in (Q : ℝ) / 2..2 * (Q : ℝ),
          typeIDyadicPhysicalIntegrand sigma (-t) (m : ℝ) (Q : ℝ) x) := by
            simp
    _ = _ := congrArg star
      (sum_typeIDyadicPhysicalIntegral_interval_eq_reflectedMellin
        (t := -t) hsigma hQr hLU)

/-- A dyadic interval-form fixed polynomial is exactly an ordinary
Dirichlet polynomial with coefficients normalized at its right endpoint.
This is the source-entry bridge used by MHH after stationary-annulus
pigeonholing. -/
theorem typeIReflectedIntervalFixedPolynomial_dyadic_normalized
    {sigma u : ℝ} {P : ℕ} (hP : 0 < P) :
    typeIReflectedIntervalFixedPolynomial sigma u P (2 * P) /
        ((((2 * P : ℕ) : ℝ) ^ sigma : ℝ) : ℂ) =
      dirichletPoly P (normalizedTypeIReflectedCoeff sigma (2 * P)) (-u) := by
  have hTwoP : 0 < 2 * P := by omega
  have hTwoPReal : (0 : ℝ) < (2 * P : ℕ) := by exact_mod_cast hTwoP
  unfold typeIReflectedIntervalFixedPolynomial dirichletPoly
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m hm
  have hmData := Finset.mem_Ioc.mp hm
  have hmPos : 0 < m := lt_of_lt_of_le (by omega : 0 < P) hmData.1.le
  have hmReal : (0 : ℝ) < m := by exact_mod_cast hmPos
  rw [normalizedTypeIReflectedCoeff,
    if_pos ⟨hmPos, hmData.2⟩]
  rw [Complex.ofReal_div, Complex.ofReal_cpow hmReal.le,
    Complex.ofReal_cpow hTwoPReal.le]
  have hmComplex : (m : ℂ) ≠ 0 := by exact_mod_cast hmPos.ne'
  rw [Complex.cpow_def_of_ne_zero hmComplex,
    Complex.cpow_def_of_ne_zero hmComplex]
  field_simp
  congr 1
  push_cast
  ring

/-- The coefficients in every normalized reflected dyadic block satisfy
the exact unit bound required by the unrestricted MHH theorem. -/
theorem norm_normalizedTypeIReflectedCoeff_two_mul_le_one
    {sigma : ℝ} (hsigma : 0 ≤ sigma) {P n : ℕ} (hP : 0 < P) :
    ‖normalizedTypeIReflectedCoeff sigma (2 * P) n‖ ≤ 1 :=
  norm_normalizedTypeIReflectedCoeff_le_one hsigma (by omega)

/-- A large fixed interval polynomial gives the corresponding normalized
dyadic Dirichlet polynomial with its exact right-endpoint loss. -/
theorem normalized_reflected_dyadic_large_of_fixed
    {sigma u S : ℝ} {P : ℕ} (hP : 0 < P)
    (hLarge : S <
      ‖typeIReflectedIntervalFixedPolynomial sigma u P (2 * P)‖) :
    S / ((2 * P : ℕ) : ℝ) ^ sigma <
      ‖dirichletPoly P
        (normalizedTypeIReflectedCoeff sigma (2 * P)) (-u)‖ := by
  have hDen : 0 < ((2 * P : ℕ) : ℝ) ^ sigma := by positivity
  rw [← typeIReflectedIntervalFixedPolynomial_dyadic_normalized hP,
    norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hDen]
  exact (div_lt_div_iff_of_pos_right hDen).2 hLarge

/-- Non-strict companion used after finite dyadic pigeonholing. -/
theorem normalized_reflected_dyadic_large_of_fixed_le
    {sigma u S : ℝ} {P : ℕ} (hP : 0 < P)
    (hLarge : S ≤
      ‖typeIReflectedIntervalFixedPolynomial sigma u P (2 * P)‖) :
    S / ((2 * P : ℕ) : ℝ) ^ sigma ≤
      ‖dirichletPoly P
        (normalizedTypeIReflectedCoeff sigma (2 * P)) (-u)‖ := by
  have hDen : 0 < ((2 * P : ℕ) : ℝ) ^ sigma := by positivity
  rw [← typeIReflectedIntervalFixedPolynomial_dyadic_normalized hP,
    norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hDen]
  exact (div_le_div_iff_of_pos_right hDen).2 hLarge

/-- Exact dyadic partition of a reflected interval.  Every block has the
same physical dual scale up to the fixed factor `2^J`; no prefix below the
stationary annulus is introduced. -/
theorem typeIReflectedIntervalFixedPolynomial_eq_sum_dyadic
    (sigma u : ℝ) (P J : ℕ) :
    typeIReflectedIntervalFixedPolynomial sigma u P (2 ^ J * P) =
      ∑ j ∈ Finset.range J,
        typeIReflectedIntervalFixedPolynomial sigma u
          (2 ^ j * P) (2 ^ (j + 1) * P) := by
  induction J with
  | zero => simp [typeIReflectedIntervalFixedPolynomial]
  | succ J ih =>
      rw [Finset.sum_range_succ, ← ih]
      unfold typeIReflectedIntervalFixedPolynomial
      have hPmid : P ≤ 2 ^ J * P :=
        Nat.le_mul_of_pos_left P (pow_pos (by omega : 0 < 2) J)
      have hmidTop : 2 ^ J * P ≤ 2 ^ (J + 1) * P := by
        rw [pow_succ]
        apply Nat.mul_le_mul_right P
        calc
          2 ^ J = 2 ^ J * 1 := by omega
          _ ≤ 2 ^ J * 2 := Nat.mul_le_mul_left _ (by omega)
      rw [← Finset.Ioc_union_Ioc_eq_Ioc hPmid hmidTop,
        Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl)]

/-- One of the `J` dyadic blocks in a stationary reflected annulus carries
at least the average norm. -/
theorem exists_large_reflected_interval_dyadic_block
    {sigma u R : ℝ} {P J : ℕ} (hJ : 0 < J)
    (hLarge : R ≤
      ‖typeIReflectedIntervalFixedPolynomial sigma u P (2 ^ J * P)‖) :
    ∃ j ∈ Finset.range J,
      R / J ≤
        ‖typeIReflectedIntervalFixedPolynomial sigma u
          (2 ^ j * P) (2 ^ (j + 1) * P)‖ := by
  have hTriangle :
      ‖typeIReflectedIntervalFixedPolynomial sigma u P (2 ^ J * P)‖ ≤
        ∑ j ∈ Finset.range J,
          ‖typeIReflectedIntervalFixedPolynomial sigma u
            (2 ^ j * P) (2 ^ (j + 1) * P)‖ := by
    rw [typeIReflectedIntervalFixedPolynomial_eq_sum_dyadic]
    exact norm_sum_le _ _
  exact pigeonhole_real_sum J
    (fun j => ‖typeIReflectedIntervalFixedPolynomial sigma u
      (2 ^ j * P) (2 ^ (j + 1) * P)‖) R
    (hLarge.trans hTriangle) hJ

/-- The preceding stationary-annulus pigeonhole already has the exact
coefficient normalization required by MHH. -/
theorem exists_large_normalized_reflected_interval_dyadic_block
    {sigma u R : ℝ} {P J : ℕ} (hP : 0 < P) (hJ : 0 < J)
    (hLarge : R ≤
      ‖typeIReflectedIntervalFixedPolynomial sigma u P (2 ^ J * P)‖) :
    ∃ j ∈ Finset.range J,
      (R / J) / ((2 ^ (j + 1) * P : ℕ) : ℝ) ^ sigma ≤
        ‖dirichletPoly (2 ^ j * P)
          (normalizedTypeIReflectedCoeff sigma (2 ^ (j + 1) * P)) (-u)‖ := by
  obtain ⟨j, hj, hBlock⟩ :=
    exists_large_reflected_interval_dyadic_block hJ hLarge
  have hPj : 0 < 2 ^ j * P := by positivity
  refine ⟨j, hj, ?_⟩
  have hBlock' : R / J ≤
      ‖typeIReflectedIntervalFixedPolynomial sigma u
        (2 ^ j * P) (2 * (2 ^ j * P))‖ := by
    convert hBlock using 2
    rw [pow_succ]
    ring
  have hNorm := normalized_reflected_dyadic_large_of_fixed_le
    (sigma := sigma) (u := u) hPj hBlock'
  simpa only [pow_succ, Nat.cast_mul, Nat.cast_ofNat, mul_assoc,
    mul_comm, mul_left_comm] using hNorm

/-- Local copy of the multiplicity-preserving displacement selection used
before the later prefix-form reflection lemmas. -/
theorem exists_separated_bounded_shift_image_interval
    (W : Finset ℝ) (shift : ℝ → ℝ) (H : ℝ)
    (_hH : 0 ≤ H) (hSeparated : IsSeparated 1 W)
    (hShift : ∀ t ∈ W, |t - shift t| ≤ H) :
    ∃ U ⊆ W.image shift, IsSeparated 1 U ∧
      W.card ≤ 2 * (2 * ⌈H⌉₊ + 1) * U.card := by
  classical
  let weight : ℝ → ℕ := fun _ => 1
  let shiftedWeight : ℝ → ℕ := fun u =>
    ∑ t ∈ W.filter (fun x => shift x = u), weight t
  have hLocalOriginal : ∀ z : ℤ,
      ∑ t ∈ W.filter
          (fun x => (z : ℝ) ≤ x ∧ x < (z : ℝ) + 1), weight t ≤ 1 := by
    intro z
    have hCard :
        (W.filter (fun x => (z : ℝ) ≤ x ∧ x < (z : ℝ) + 1)).card ≤ 1 := by
      rw [Finset.card_le_one_iff]
      intro x y hx hy
      simp only [Finset.mem_filter] at hx hy
      by_contra hxy
      have hSep := hSeparated x hx.1 y hy.1 hxy
      rw [Real.dist_eq] at hSep
      have hlt : |x - y| < 1 := by
        rw [abs_lt]
        constructor <;> linarith [hx.2.1, hx.2.2, hy.2.1, hy.2.2]
      linarith
    simpa only [weight, Finset.sum_const, nsmul_eq_mul, mul_one] using hCard
  have hLocalShifted : ∀ z : ℤ,
      ∑ u ∈ (W.image shift).filter
          (fun v => (z : ℝ) ≤ v ∧ v < (z : ℝ) + 1), shiftedWeight u ≤
        2 * ⌈H⌉₊ + 1 := by
    intro z
    simpa only [shiftedWeight, weight, mul_one] using
      shifted_bin_weight_le_of_unit_bin_weight W weight id shift H 1
        (by simpa only [id_eq] using hShift) hLocalOriginal z
  obtain ⟨U, hUImage, hUSep, hWeight⟩ :=
    weighted_separated_selection (W.image shift) shiftedWeight
      (2 * ⌈H⌉₊ + 1) hLocalShifted
  have hAll : W.filter (fun t => shift t ∈ W.image shift) = W := by
    apply Finset.filter_eq_self.mpr
    intro t ht
    exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
  have hFiber := Finset.sum_fiberwise_eq_sum_filter W (W.image shift)
    shift weight
  rw [hAll] at hFiber
  have hTotal : ∑ u ∈ W.image shift, shiftedWeight u = W.card := by
    simpa only [shiftedWeight, weight, Finset.sum_const, nsmul_eq_mul,
      mul_one] using hFiber
  refine ⟨U, hUImage, hUSep, ?_⟩
  rw [← hTotal]
  simpa only [mul_assoc] using hWeight

/-- Negative-sign stationary blocks are reflected into one positive base
interval, with all displacement fibres retained. -/
theorem extract_negative_reflected_dyadic_family
    {P : ℕ} {sigma T D H S : ℝ} (W : Finset ℝ)
    (hP : 0 < P) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (hDH : D + H ≤ T / 2)
    (hSeparated : IsSeparated 1 W)
    (hRange : ∀ t ∈ W, T - D ≤ t ∧ t ≤ 2 * T + D)
    (hEach : ∀ t ∈ W, ∃ u ∈ Set.Icc (-H) H,
      S < ‖typeIReflectedIntervalFixedPolynomial sigma (t + u)
        P (2 * P)‖) :
    ∃ U : Finset ℝ,
      IsSeparated 1 U ∧ InBaseInterval (3 * T) U ∧
      W.card ≤ 2 * (2 * ⌈H⌉₊ + 1) * U.card ∧
      ∀ v ∈ U,
        S / ((2 * P : ℕ) : ℝ) ^ sigma <
          ‖dirichletPoly P
            (phaseShiftCoeffs (-3 * T)
              (normalizedTypeIReflectedCoeff sigma (2 * P))) v‖ := by
  classical
  let reflect : ℝ → ℝ := fun t => 3 * T - t
  let Wrev : Finset ℝ := W.image reflect
  have hreflectInj : Function.Injective reflect := by
    intro x y hxy
    dsimp only [reflect] at hxy
    linarith
  have hWrevCard : Wrev.card = W.card := by
    dsimp only [Wrev]
    exact Finset.card_image_iff.mpr fun _ hx _ hy hxy =>
      hreflectInj hxy
  have hWrevSeparated : IsSeparated 1 Wrev := by
    intro x hx y hy hxy
    rcases Finset.mem_image.mp hx with ⟨tx, htx, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨ty, hty, hyEq⟩
    have htxy : tx ≠ ty := by
      intro h
      subst ty
      exact hxy hyEq
    have hsep := hSeparated tx htx ty hty htxy
    subst y
    rw [Real.dist_eq] at hsep ⊢
    dsimp only [reflect]
    rw [show 3 * T - tx - (3 * T - ty) = -(tx - ty) by ring, abs_neg]
    exact hsep
  have hOriginalMem : ∀ x ∈ Wrev, 3 * T - x ∈ W := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨t, ht, rfl⟩
    convert ht using 1
    dsimp only [reflect]
    ring
  let displacement : ℝ → ℝ := fun x =>
    if hx : x ∈ Wrev then Classical.choose (hEach (3 * T - x)
      (hOriginalMem x hx)) else 0
  have hDisplacementMem : ∀ x ∈ Wrev,
      displacement x ∈ Set.Icc (-H) H := by
    intro x hx
    simp only [displacement, dif_pos hx]
    exact (Classical.choose_spec (hEach (3 * T - x)
      (hOriginalMem x hx))).1
  have hDisplacementLarge : ∀ x ∈ Wrev,
      S < ‖typeIReflectedIntervalFixedPolynomial sigma
        ((3 * T - x) + displacement x) P (2 * P)‖ := by
    intro x hx
    simp only [displacement, dif_pos hx]
    exact (Classical.choose_spec (hEach (3 * T - x)
      (hOriginalMem x hx))).2
  let shift : ℝ → ℝ := fun x => x - displacement x
  have hShiftBound : ∀ x ∈ Wrev, |x - shift x| ≤ H := by
    intro x hx
    have hd := hDisplacementMem x hx
    dsimp only [shift]
    rw [show x - (x - displacement x) = displacement x by ring]
    exact abs_le.mpr hd
  obtain ⟨U, hUImage, hUSep, hCard⟩ :=
    exists_separated_bounded_shift_image_interval Wrev shift H hH
      hWrevSeparated hShiftBound
  refine ⟨U, hUSep, ?_, ?_, ?_⟩
  · intro v hv
    rcases Finset.mem_image.mp (hUImage hv) with ⟨x, hx, rfl⟩
    have hxRange := hRange (3 * T - x) (hOriginalMem x hx)
    have hdu := hDisplacementMem x hx
    rw [Set.mem_Icc]
    constructor <;> dsimp only [shift] <;> linarith [hdu.1, hdu.2]
  · rw [← hWrevCard]
    exact hCard
  · intro v hv
    rcases Finset.mem_image.mp (hUImage hv) with ⟨x, hx, rfl⟩
    have hLarge := normalized_reflected_dyadic_large_of_fixed hP
      (hDisplacementLarge x hx)
    have hArg : -((3 * T - x) + displacement x) =
        shift x + (-3 * T) := by
      dsimp only [shift]
      ring
    rw [hArg, dirichletPoly_translate] at hLarge
    exact hLarge

/-- Positive-sign stationary blocks require only the bounded displacement
selection; no reflection of the ordinate is needed. -/
theorem extract_positive_reflected_dyadic_family
    {P : ℕ} {sigma T D H S : ℝ} (W : Finset ℝ)
    (hP : 0 < P) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (hDH : D + H ≤ T / 2)
    (hSeparated : IsSeparated 1 W)
    (hRange : ∀ t ∈ W, T - D ≤ t ∧ t ≤ 2 * T + D)
    (hEach : ∀ t ∈ W, ∃ u ∈ Set.Icc (-H) H,
      S < ‖typeIReflectedIntervalFixedPolynomial sigma (-t + u)
        P (2 * P)‖) :
    ∃ U : Finset ℝ,
      IsSeparated 1 U ∧ InBaseInterval (3 * T) U ∧
      W.card ≤ 2 * (2 * ⌈H⌉₊ + 1) * U.card ∧
      ∀ v ∈ U,
        S / ((2 * P : ℕ) : ℝ) ^ sigma <
          ‖dirichletPoly P
            (normalizedTypeIReflectedCoeff sigma (2 * P)) v‖ := by
  classical
  let displacement : ℝ → ℝ := fun t =>
    if ht : t ∈ W then Classical.choose (hEach t ht) else 0
  have hDisplacementMem : ∀ t ∈ W,
      displacement t ∈ Set.Icc (-H) H := by
    intro t ht
    simp only [displacement, dif_pos ht]
    exact (Classical.choose_spec (hEach t ht)).1
  have hDisplacementLarge : ∀ t ∈ W,
      S < ‖typeIReflectedIntervalFixedPolynomial sigma
        (-t + displacement t) P (2 * P)‖ := by
    intro t ht
    simp only [displacement, dif_pos ht]
    exact (Classical.choose_spec (hEach t ht)).2
  let shift : ℝ → ℝ := fun t => t - displacement t
  have hShiftBound : ∀ t ∈ W, |t - shift t| ≤ H := by
    intro t ht
    have hd := hDisplacementMem t ht
    dsimp only [shift]
    rw [show t - (t - displacement t) = displacement t by ring]
    exact abs_le.mpr hd
  obtain ⟨U, hUImage, hUSep, hCard⟩ :=
    exists_separated_bounded_shift_image_interval W shift H hH
      hSeparated hShiftBound
  refine ⟨U, hUSep, ?_, hCard, ?_⟩
  · intro v hv
    rcases Finset.mem_image.mp (hUImage hv) with ⟨t, ht, rfl⟩
    have htRange := hRange t ht
    have hdu := hDisplacementMem t ht
    rw [Set.mem_Icc]
    constructor <;> dsimp only [shift] <;> linarith [hdu.1, hdu.2]
  · intro v hv
    rcases Finset.mem_image.mp (hUImage hv) with ⟨t, ht, rfl⟩
    have hLarge := normalized_reflected_dyadic_large_of_fixed hP
      (hDisplacementLarge t ht)
    simpa only [shift, neg_add_rev, neg_neg, sub_eq_add_neg,
      add_comm] using hLarge

/-- MHH cardinality for a negative-sign stationary dyadic block. -/
theorem negative_reflected_dyadic_mhh_cardinality
    {P : ℕ} {sigma T D H S : ℝ} (W : Finset ℝ)
    (hP : 0 < P) (hH : 0 ≤ H) (hT : 1 ≤ T)
    (hDH : D + H ≤ T / 2) (hS : 0 < S)
    (hSeparated : IsSeparated 1 W)
    (hRange : ∀ t ∈ W, T - D ≤ t ∧ t ≤ 2 * T + D)
    (hEach : ∀ t ∈ W, ∃ u ∈ Set.Icc (-H) H,
      S < ‖typeIReflectedIntervalFixedPolynomial sigma (t + u)
        P (2 * P)‖)
    (hsigma : 0 ≤ sigma) :
    ∃ K : ℝ, 0 < K ∧ ∃ U : Finset ℝ,
      IsSeparated 1 U ∧ InBaseInterval (3 * T) U ∧
      W.card ≤ 2 * (2 * ⌈H⌉₊ + 1) * U.card ∧
      (U.card : ℝ) ≤
        K * (1 + (((harmonic P : ℚ) : ℝ))) *
          (((P : ℝ) ^ 2 /
              (S / ((2 * P : ℕ) : ℝ) ^ sigma) ^ 2) +
            (3 * T) * min
              ((P : ℝ) /
                (S / ((2 * P : ℕ) : ℝ) ^ sigma) ^ 2)
              ((P : ℝ) ^ 4 /
                (S / ((2 * P : ℕ) : ℝ) ^ sigma) ^ 6)) := by
  obtain ⟨K, hK, hMHH⟩ := classical_large_values_with_harmonic_unrestricted
  obtain ⟨U, hUSep, hUBase, hCard, hLarge⟩ :=
    extract_negative_reflected_dyadic_family W hP hH
      (zero_le_one.trans hT) hDH hSeparated hRange hEach
  have hThreshold : 0 < S / ((2 * P : ℕ) : ℝ) ^ sigma := by positivity
  have hCoeff : ∀ n ∈ dyadicInterval P,
      ‖phaseShiftCoeffs (-3 * T)
        (normalizedTypeIReflectedCoeff sigma (2 * P)) n‖ ≤ 1 := by
    intro n _hn
    rw [norm_phaseShiftCoeffs]
    exact norm_normalizedTypeIReflectedCoeff_two_mul_le_one hsigma hP
  have hAt := hMHH P (3 * T)
    (S / ((2 * P : ℕ) : ℝ) ^ sigma) U
    (phaseShiftCoeffs (-3 * T)
      (normalizedTypeIReflectedCoeff sigma (2 * P)))
    hP (by linarith) hThreshold hCoeff hUSep hUBase
    (fun v hv => (hLarge v hv).le)
  exact ⟨K, hK, U, hUSep, hUBase, hCard, hAt⟩

/-- MHH cardinality for a positive-sign stationary dyadic block. -/
theorem positive_reflected_dyadic_mhh_cardinality
    {P : ℕ} {sigma T D H S : ℝ} (W : Finset ℝ)
    (hP : 0 < P) (hH : 0 ≤ H) (hT : 1 ≤ T)
    (hDH : D + H ≤ T / 2) (hS : 0 < S)
    (hSeparated : IsSeparated 1 W)
    (hRange : ∀ t ∈ W, T - D ≤ t ∧ t ≤ 2 * T + D)
    (hEach : ∀ t ∈ W, ∃ u ∈ Set.Icc (-H) H,
      S < ‖typeIReflectedIntervalFixedPolynomial sigma (-t + u)
        P (2 * P)‖)
    (hsigma : 0 ≤ sigma) :
    ∃ K : ℝ, 0 < K ∧ ∃ U : Finset ℝ,
      IsSeparated 1 U ∧ InBaseInterval (3 * T) U ∧
      W.card ≤ 2 * (2 * ⌈H⌉₊ + 1) * U.card ∧
      (U.card : ℝ) ≤
        K * (1 + (((harmonic P : ℚ) : ℝ))) *
          (((P : ℝ) ^ 2 /
              (S / ((2 * P : ℕ) : ℝ) ^ sigma) ^ 2) +
            (3 * T) * min
              ((P : ℝ) /
                (S / ((2 * P : ℕ) : ℝ) ^ sigma) ^ 2)
              ((P : ℝ) ^ 4 /
                (S / ((2 * P : ℕ) : ℝ) ^ sigma) ^ 6)) := by
  obtain ⟨K, hK, hMHH⟩ := classical_large_values_with_harmonic_unrestricted
  obtain ⟨U, hUSep, hUBase, hCard, hLarge⟩ :=
    extract_positive_reflected_dyadic_family W hP hH
      (zero_le_one.trans hT) hDH hSeparated hRange hEach
  have hThreshold : 0 < S / ((2 * P : ℕ) : ℝ) ^ sigma := by positivity
  have hCoeff : ∀ n ∈ dyadicInterval P,
      ‖normalizedTypeIReflectedCoeff sigma (2 * P) n‖ ≤ 1 := by
    intro n _hn
    exact norm_normalizedTypeIReflectedCoeff_two_mul_le_one hsigma hP
  have hAt := hMHH P (3 * T)
    (S / ((2 * P : ℕ) : ℝ) ^ sigma) U
    (normalizedTypeIReflectedCoeff sigma (2 * P))
    hP (by linarith) hThreshold hCoeff hUSep hUBase
    (fun v hv => (hLarge v hv).le)
  exact ⟨K, hK, U, hUSep, hUBase, hCard, hAt⟩


/-- The common finite reflected Mellin integrand is genuinely Bochner
integrable.  This is the integrand occurring in the exact B-process identity,
not a separately postulated majorant. -/
theorem integrable_typeIReflectedMellinIntegrand
    {sigma t Q : ℝ} {M : ℕ} (hsigma : 0 ≤ sigma)
    (hQ : 0 < Q) (hM : 1 ≤ M) :
    Integrable (fun r : ℝ =>
      typeIReflectedMellinPolynomial sigma t Q M r *
        typeIDyadicCutoffMellin r *
          typeIPowerReflectionIntegral sigma (t + r)
            (Q / 2) (2 * M * Q)) := by
  let S := Finset.Icc 1 M
  let A : ℝ := Q / 2
  let B : ℝ := 2 * M * Q
  have hA : 0 < A := by dsimp only [A]; positivity
  have hAB : A ≤ B := by
    dsimp only [A, B]
    have hMReal : (1 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hMode : ∀ m ∈ S, Integrable (fun r : ℝ =>
      typeIReflectionScaleFactor sigma t m *
        typeICommonMellinMode sigma t ((m : ℝ) * Q) A B r) := by
    intro m hm
    have hmData := Finset.mem_Icc.mp hm
    have hmPos : (0 : ℝ) < m := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hmData.1)
    exact (integrable_typeICommonMellinMode hsigma (mul_pos hmPos hQ)
      hA hAB).const_mul _
  have hSum : Integrable (fun r : ℝ =>
      ∑ m ∈ S, typeIReflectionScaleFactor sigma t m *
        typeICommonMellinMode sigma t ((m : ℝ) * Q) A B r) :=
    MeasureTheory.integrable_finsetSum S hMode
  apply hSum.congr
  filter_upwards with r
  unfold typeIReflectedMellinPolynomial typeICommonMellinMode
  dsimp only [S, A, B]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m _hm
  ring

/-- The interval-form reflected Mellin integrand is Bochner integrable. -/
theorem integrable_typeIReflectedIntervalMellinIntegrand
    {sigma t Q : ℝ} {L U : ℕ} (hsigma : 0 ≤ sigma)
    (hQ : 0 < Q) (hLU : L < U) :
    Integrable (fun r : ℝ =>
      typeIReflectedIntervalMellinPolynomial sigma t Q L U r *
        typeIDyadicCutoffMellin r *
          typeIPowerReflectionIntegral sigma (t + r)
            ((((L + 1 : ℕ) : ℝ) * Q) / 2)
            (2 * (U : ℝ) * Q)) := by
  let S := Finset.Ioc L U
  let A : ℝ := (((L + 1 : ℕ) : ℝ) * Q) / 2
  let B : ℝ := 2 * (U : ℝ) * Q
  have hA : 0 < A := by dsimp only [A]; positivity
  have hAB : A ≤ B := by
    dsimp only [A, B]
    have hCast : ((L + 1 : ℕ) : ℝ) ≤ U := by exact_mod_cast hLU
    nlinarith
  have hMode : ∀ m ∈ S, Integrable (fun r : ℝ =>
      typeIReflectionScaleFactor sigma t m *
        typeICommonMellinMode sigma t ((m : ℝ) * Q) A B r) := by
    intro m hm
    have hmData := Finset.mem_Ioc.mp hm
    have hmPos : (0 : ℝ) < m := by
      exact_mod_cast (lt_of_le_of_lt (Nat.zero_le L) hmData.1)
    exact (integrable_typeICommonMellinMode hsigma (mul_pos hmPos hQ)
      hA hAB).const_mul _
  have hSum : Integrable (fun r : ℝ =>
      ∑ m ∈ S, typeIReflectionScaleFactor sigma t m *
        typeICommonMellinMode sigma t ((m : ℝ) * Q) A B r) :=
    MeasureTheory.integrable_finsetSum S hMode
  apply hSum.congr
  filter_upwards with r
  unfold typeIReflectedIntervalMellinPolynomial typeICommonMellinMode
  dsimp only [S, A, B]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m _hm
  ring

/-- Elementary uniform bound for a literal reflected interval. -/
theorem norm_typeIReflectedIntervalFixedPolynomial_le
    {sigma : ℝ} (hsigma : 0 ≤ sigma) (u : ℝ) (L U : ℕ) :
    ‖typeIReflectedIntervalFixedPolynomial sigma u L U‖ ≤
      (U : ℝ) * (U : ℝ) ^ sigma := by
  rw [typeIReflectedIntervalFixedPolynomial]
  calc
    ‖∑ m ∈ Finset.Ioc L U,
        (((m : ℝ) ^ sigma : ℝ) : ℂ) *
          (m : ℂ) ^ ((u : ℂ) * Complex.I)‖ ≤
      ∑ m ∈ Finset.Ioc L U,
        ‖(((m : ℝ) ^ sigma : ℝ) : ℂ) *
          (m : ℂ) ^ ((u : ℂ) * Complex.I)‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.Ioc L U, (U : ℝ) ^ sigma := by
      apply Finset.sum_le_sum
      intro m hm
      have hmData := Finset.mem_Ioc.mp hm
      have hmPos : 0 < m := lt_of_le_of_lt (Nat.zero_le L) hmData.1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (by positivity) _),
        Complex.norm_natCast_cpow_of_pos hmPos]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re,
        mul_zero, Complex.ofReal_im, Complex.I_im, sub_self, Real.rpow_zero,
        mul_one]
      exact Real.rpow_le_rpow (Nat.cast_nonneg m)
        (by exact_mod_cast hmData.2) hsigma
    _ ≤ (U : ℝ) * (U : ℝ) ^ sigma := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hCard : (Finset.Ioc L U).card ≤ U := by simp
      gcongr

/-- The fixed interval polynomial is the only non-unit factor in its
Mellin polynomial. -/
theorem norm_typeIReflectedIntervalMellinPolynomial_eq_fixed
    (sigma t Q : ℝ) (L U : ℕ) (r : ℝ) (hQ : 0 < Q) :
    ‖typeIReflectedIntervalMellinPolynomial sigma t Q L U r‖ =
      Q * ‖typeIReflectedIntervalFixedPolynomial sigma (t + r) L U‖ := by
  rw [typeIReflectedIntervalMellinPolynomial_eq_fixed sigma t Q L U r hQ,
    norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ,
    Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  simp

/-- Setwise norm bound for the exact interval-form Mellin integral. -/
theorem norm_setIntegral_typeIReflectedIntervalMellinIntegrand_le
    {sigma t Q R K : ℝ} {L U : ℕ} {S : Set ℝ}
    (hS : MeasurableSet S) (hQ : 0 < Q) (hR : 0 ≤ R)
    (hFixed : ∀ r ∈ S,
      ‖typeIReflectedIntervalFixedPolynomial sigma (t + r) L U‖ ≤ R)
    (hKernel : ∀ r ∈ S,
      ‖typeIPowerReflectionIntegral sigma (t + r)
        ((((L + 1 : ℕ) : ℝ) * Q) / 2)
        (2 * (U : ℝ) * Q)‖ ≤ K) :
    ‖∫ r : ℝ in S,
        typeIReflectedIntervalMellinPolynomial sigma t Q L U r *
          typeIDyadicCutoffMellin r *
            typeIPowerReflectionIntegral sigma (t + r)
              ((((L + 1 : ℕ) : ℝ) * Q) / 2)
              (2 * (U : ℝ) * Q)‖ ≤
      Q * R * K * ∫ r : ℝ in S, ‖typeIDyadicCutoffMellin r‖ := by
  have hMellin : Integrable typeIDyadicCutoffMellin := by
    simpa only [typeIDyadicCutoffMellin, VerticalIntegrable] using
      verticalIntegrable_typeIDyadicCutoffMellin
  have hDom : IntegrableOn
      (fun r : ℝ => Q * R * K * ‖typeIDyadicCutoffMellin r‖) S :=
    hMellin.norm.const_mul (Q * R * K) |>.integrableOn
  have hPoint : ∀ᵐ r : ℝ ∂volume.restrict S,
      ‖typeIReflectedIntervalMellinPolynomial sigma t Q L U r *
          typeIDyadicCutoffMellin r *
            typeIPowerReflectionIntegral sigma (t + r)
              ((((L + 1 : ℕ) : ℝ) * Q) / 2)
              (2 * (U : ℝ) * Q)‖ ≤
        Q * R * K * ‖typeIDyadicCutoffMellin r‖ := by
    filter_upwards [ae_restrict_mem hS] with r hr
    rw [norm_mul, norm_mul,
      norm_typeIReflectedIntervalMellinPolynomial_eq_fixed
        sigma t Q L U r hQ]
    have hF := hFixed r hr
    have hP := hKernel r hr
    calc
      Q * ‖typeIReflectedIntervalFixedPolynomial sigma (t + r) L U‖ *
          ‖typeIDyadicCutoffMellin r‖ *
            ‖typeIPowerReflectionIntegral sigma (t + r)
              ((((L + 1 : ℕ) : ℝ) * Q) / 2)
              (2 * (U : ℝ) * Q)‖ ≤
        Q * R * ‖typeIDyadicCutoffMellin r‖ * K := by gcongr
      _ = Q * R * K * ‖typeIDyadicCutoffMellin r‖ := by ring
  simpa only [integral_const_mul] using
    norm_integral_le_of_norm_le hDom hPoint

/-- A setwise norm bound for the exact reflected Mellin integral.  The
coefficient polynomial and the oscillatory kernel are bounded separately,
while the literal Mellin transform retains its full `L¹` mass. -/
theorem norm_setIntegral_typeIReflectedMellinIntegrand_le
    {sigma t Q R K : ℝ} {M : ℕ} {S : Set ℝ}
    (hS : MeasurableSet S) (hQ : 0 < Q) (hR : 0 ≤ R)
    (hFixed : ∀ r ∈ S,
      ‖typeIReflectedFixedPolynomial sigma (t + r) M‖ ≤ R)
    (hKernel : ∀ r ∈ S,
      ‖typeIPowerReflectionIntegral sigma (t + r)
        (Q / 2) (2 * M * Q)‖ ≤ K) :
    ‖∫ r : ℝ in S,
        typeIReflectedMellinPolynomial sigma t Q M r *
          typeIDyadicCutoffMellin r *
            typeIPowerReflectionIntegral sigma (t + r)
              (Q / 2) (2 * M * Q)‖ ≤
      Q * R * K * ∫ r : ℝ in S, ‖typeIDyadicCutoffMellin r‖ := by
  have hMellin : Integrable typeIDyadicCutoffMellin := by
    simpa only [typeIDyadicCutoffMellin, VerticalIntegrable] using
      verticalIntegrable_typeIDyadicCutoffMellin
  have hDom : IntegrableOn
      (fun r : ℝ => Q * R * K * ‖typeIDyadicCutoffMellin r‖) S :=
    hMellin.norm.const_mul (Q * R * K) |>.integrableOn
  have hPoint : ∀ᵐ r : ℝ ∂volume.restrict S,
      ‖typeIReflectedMellinPolynomial sigma t Q M r *
          typeIDyadicCutoffMellin r *
            typeIPowerReflectionIntegral sigma (t + r)
              (Q / 2) (2 * M * Q)‖ ≤
        Q * R * K * ‖typeIDyadicCutoffMellin r‖ := by
    filter_upwards [ae_restrict_mem hS] with r hr
    rw [norm_mul, norm_mul,
      norm_typeIReflectedMellinPolynomial_eq_fixed sigma t Q M r hQ]
    have hF := hFixed r hr
    have hP := hKernel r hr
    calc
      Q * ‖typeIReflectedFixedPolynomial sigma (t + r) M‖ *
          ‖typeIDyadicCutoffMellin r‖ *
            ‖typeIPowerReflectionIntegral sigma (t + r)
              (Q / 2) (2 * M * Q)‖ ≤
        Q * R * ‖typeIDyadicCutoffMellin r‖ * K := by gcongr
      _ = Q * R * K * ‖typeIDyadicCutoffMellin r‖ := by ring
  simpa only [integral_const_mul] using
    norm_integral_le_of_norm_le hDom hPoint

/-! The remaining lemmas specialize the preceding exact estimate to the
bounded Mellin window and its complement. -/

/-- Uniform stationary-window upper bound on the common oscillatory
integral.  Only the proved first/second derivative estimate is used. -/
theorem norm_typeIPowerReflectionIntegral_le_on_symmetric_window
    {sigma t H Q : ℝ} {M : ℕ}
    (hsigma : 0 < sigma) (ht : 2 ≤ t)
    (hHt : 2 * H ≤ t - 2) (hQ : 0 < Q) (hM : 1 ≤ M)
    {r : ℝ} (hr : r ∈ Set.Icc (-H) H) :
    ‖typeIPowerReflectionIntegral sigma (t + r)
        (Q / 2) (2 * M * Q)‖ ≤
      (16 / t) * (Q / 2) ^ (-sigma) +
        (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
          (t / 2) ^ (-sigma - 1 / 2) := by
  have htPos : 0 < t := by linarith
  have hTau : 1 ≤ t + r := by
    have hrLower := hr.1
    linarith
  have hA : 0 < Q / 2 := by positivity
  have hAB : Q / 2 ≤ 2 * M * Q := by
    have hMReal : (1 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hRaw := norm_typeIPowerReflectionIntegral_le_stationary
    hsigma hTau hA hAB
  have hTauLower : t / 2 ≤ t + r := by
    have hrLower := hr.1
    linarith
  have hTauPos : 0 < t + r := zero_lt_one.trans_le hTau
  have hHalfPos : 0 < t / 2 := by positivity
  have hInv : 8 / (t + r) ≤ 16 / t := by
    rw [div_le_div_iff₀ hTauPos htPos]
    nlinarith
  have hExp : -sigma - 1 / 2 ≤ 0 := by linarith
  have hPow : (t + r) ^ (-sigma - 1 / 2) ≤
      (t / 2) ^ (-sigma - 1 / 2) :=
    Real.rpow_le_rpow_of_nonpos hHalfPos hTauLower hExp
  calc
    ‖typeIPowerReflectionIntegral sigma (t + r)
        (Q / 2) (2 * M * Q)‖ ≤
      (8 / (t + r)) * (Q / 2) ^ (-sigma) +
        (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
          (t + r) ^ (-sigma - 1 / 2) := hRaw
    _ ≤ (16 / t) * (Q / 2) ^ (-sigma) +
        (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
          (t / 2) ^ (-sigma - 1 / 2) := by gcongr

/-- The complementary Mellin range is polynomially small to arbitrary
order, with every finite `M` and `Q` dependence displayed. -/
theorem exists_norm_typeIReflectedMellinIntegral_tail_le
    (n : ℕ) (hn : 1 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ {sigma t Q H : ℝ} {M : ℕ},
      0 ≤ sigma → 0 < Q → 1 ≤ M → 1 ≤ H →
      ‖∫ r : ℝ in (Set.Icc (-H) H)ᶜ,
          typeIReflectedMellinPolynomial sigma t Q M r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r)
                (Q / 2) (2 * M * Q)‖ ≤
        Q * ((M : ℝ) * (M : ℝ) ^ sigma) *
          (((2 * M * Q - Q / 2) * ((Q / 2) ^ (-sigma) / (Q / 2))) *
            C * H ^ (1 - (n : ℝ))) := by
  obtain ⟨C, hC, hTail⟩ := exists_typeIDyadicCutoffMellin_tail_bound n hn
  refine ⟨C, hC, ?_⟩
  intro sigma t Q H M hsigma hQ hM hH
  have hA : 0 < Q / 2 := by positivity
  have hAB : Q / 2 ≤ 2 * M * Q := by
    have hMReal : (1 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hBase := norm_setIntegral_typeIReflectedMellinIntegrand_le
    measurableSet_Icc.compl hQ
    (mul_nonneg (Nat.cast_nonneg M) (Real.rpow_nonneg (Nat.cast_nonneg M) _))
    (S := (Set.Icc (-H) H)ᶜ)
    (R := (M : ℝ) * (M : ℝ) ^ sigma)
    (K := (2 * M * Q - Q / 2) * ((Q / 2) ^ (-sigma) / (Q / 2)))
    (fun r _hr => norm_typeIReflectedFixedPolynomial_le hsigma (t + r) M)
    (fun r _hr => norm_typeIPowerReflectionIntegral_le_trivial
      hsigma hA hAB)
  calc
    ‖∫ r : ℝ in (Set.Icc (-H) H)ᶜ,
          typeIReflectedMellinPolynomial sigma t Q M r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r)
                (Q / 2) (2 * M * Q)‖ ≤
        Q * ((M : ℝ) * (M : ℝ) ^ sigma) *
          ((2 * M * Q - Q / 2) * ((Q / 2) ^ (-sigma) / (Q / 2))) *
            ∫ r : ℝ in (Set.Icc (-H) H)ᶜ,
              ‖typeIDyadicCutoffMellin r‖ := hBase
    _ ≤ Q * ((M : ℝ) * (M : ℝ) ^ sigma) *
          (((2 * M * Q - Q / 2) * ((Q / 2) ^ (-sigma) / (Q / 2))) *
            C * H ^ (1 - (n : ℝ))) := by
      have hFront : 0 ≤ Q * ((M : ℝ) * (M : ℝ) ^ sigma) := by
        positivity
      have hKernel : 0 ≤
          (2 * M * Q - Q / 2) * ((Q / 2) ^ (-sigma) / (Q / 2)) := by
        have hMReal : (1 : ℝ) ≤ M := by exact_mod_cast hM
        positivity
      have hMul := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hTail H hH) hKernel) hFront
      simpa only [mul_assoc] using hMul

/-- Complementary Mellin decay for a literal interval of reflected modes.
Unlike the prefix estimate above, this retains both endpoints of the
stationary annulus and is therefore suitable for the exact three-way Poisson
split. -/
theorem exists_norm_typeIReflectedIntervalMellinIntegral_tail_le
    (n : ℕ) (hn : 1 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ {sigma t Q H : ℝ} {L U : ℕ},
      0 ≤ sigma → 0 < Q → L < U → 1 ≤ H →
      ‖∫ r : ℝ in (Set.Icc (-H) H)ᶜ,
          typeIReflectedIntervalMellinPolynomial sigma t Q L U r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r)
                ((((L + 1 : ℕ) : ℝ) * Q) / 2)
                (2 * (U : ℝ) * Q)‖ ≤
        Q * ((U : ℝ) * (U : ℝ) ^ sigma) *
          (((2 * (U : ℝ) * Q - ((((L + 1 : ℕ) : ℝ) * Q) / 2)) *
              ((((((L + 1 : ℕ) : ℝ) * Q) / 2) ^ (-sigma)) /
                ((((L + 1 : ℕ) : ℝ) * Q) / 2))) *
            C * H ^ (1 - (n : ℝ))) := by
  obtain ⟨C, hC, hTail⟩ := exists_typeIDyadicCutoffMellin_tail_bound n hn
  refine ⟨C, hC, ?_⟩
  intro sigma t Q H L U hsigma hQ hLU hH
  let A : ℝ := (((L + 1 : ℕ) : ℝ) * Q) / 2
  let B : ℝ := 2 * (U : ℝ) * Q
  have hA : 0 < A := by dsimp only [A]; positivity
  have hAB : A ≤ B := by
    dsimp only [A, B]
    have hCast : ((L + 1 : ℕ) : ℝ) ≤ U := by exact_mod_cast hLU
    nlinarith
  have hR : 0 ≤ (U : ℝ) * (U : ℝ) ^ sigma := by positivity
  have hBase := norm_setIntegral_typeIReflectedIntervalMellinIntegrand_le
    measurableSet_Icc.compl hQ hR
    (S := (Set.Icc (-H) H)ᶜ)
    (R := (U : ℝ) * (U : ℝ) ^ sigma)
    (K := (B - A) * (A ^ (-sigma) / A))
    (fun r _hr => norm_typeIReflectedIntervalFixedPolynomial_le
      hsigma (t + r) L U)
    (fun r _hr => norm_typeIPowerReflectionIntegral_le_trivial
      hsigma hA hAB)
  calc
    ‖∫ r : ℝ in (Set.Icc (-H) H)ᶜ,
          typeIReflectedIntervalMellinPolynomial sigma t Q L U r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r) A B‖ ≤
        Q * ((U : ℝ) * (U : ℝ) ^ sigma) *
          ((B - A) * (A ^ (-sigma) / A)) *
            ∫ r : ℝ in (Set.Icc (-H) H)ᶜ,
              ‖typeIDyadicCutoffMellin r‖ := hBase
    _ ≤ Q * ((U : ℝ) * (U : ℝ) ^ sigma) *
          (((B - A) * (A ^ (-sigma) / A)) *
            C * H ^ (1 - (n : ℝ))) := by
      have hFront : 0 ≤ Q * ((U : ℝ) * (U : ℝ) ^ sigma) := by positivity
      have hKernel : 0 ≤ (B - A) * (A ^ (-sigma) / A) := by positivity
      have hMul := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hTail H hH) hKernel) hFront
      simpa only [mul_assoc] using hMul
    _ = Q * ((U : ℝ) * (U : ℝ) ^ sigma) *
          (((2 * (U : ℝ) * Q - ((((L + 1 : ℕ) : ℝ) * Q) / 2)) *
              ((((((L + 1 : ℕ) : ℝ) * Q) / 2) ^ (-sigma)) /
                ((((L + 1 : ℕ) : ℝ) * Q) / 2))) *
            C * H ^ (1 - (n : ℝ))) := by rfl

/-- A uniform nonstationary estimate when the entire physical interval lies
to the left of every stationary point on the symmetric Mellin window. -/
theorem norm_typeIPowerReflectionIntegral_le_left_on_symmetric_window
    {sigma t H A B : ℝ} (hsigma : 0 < sigma) (hA : 0 < A)
    (hAB : A ≤ B) (hleft : 2 * Real.pi * B + H < t)
    {r : ℝ} (hr : r ∈ Set.Icc (-H) H) :
    ‖typeIPowerReflectionIntegral sigma (t + r) A B‖ ≤
      (4 / (t - H - 2 * Real.pi * B)) * A ^ (-sigma) := by
  have hphase : 2 * Real.pi * B < t + r := by
    have hrLower := hr.1
    linarith
  have hRaw := norm_powerWeighted_gmReflectionIntegral_le_left
    hsigma hA hAB hphase
  have hDen : 0 < t - H - 2 * Real.pi * B := by linarith
  have hDen' : t - H - 2 * Real.pi * B ≤
      t + r - 2 * Real.pi * B := by linarith [hr.1]
  have hFrac : 4 / (t + r - 2 * Real.pi * B) ≤
      4 / (t - H - 2 * Real.pi * B) := by
    exact div_le_div_of_nonneg_left (by norm_num) hDen
      hDen'
  exact hRaw.trans (mul_le_mul_of_nonneg_right hFrac
    (Real.rpow_nonneg hA.le _))

/-- A uniform nonstationary estimate when the entire physical interval lies
to the right of every stationary point on the symmetric Mellin window. -/
theorem norm_typeIPowerReflectionIntegral_le_right_on_symmetric_window
    {sigma t H A B : ℝ} (hsigma : 0 < sigma) (hA : 0 < A)
    (hAB : A ≤ B) (hright : t + H < 2 * Real.pi * A)
    {r : ℝ} (hr : r ∈ Set.Icc (-H) H) :
    ‖typeIPowerReflectionIntegral sigma (t + r) A B‖ ≤
      (4 / (2 * Real.pi * A - (t + H))) * A ^ (-sigma) := by
  have hphase : t + r < 2 * Real.pi * A := by
    have hrUpper := hr.2
    linarith
  have hRaw := norm_powerWeighted_gmReflectionIntegral_le_right
    hsigma hA hAB hphase
  have hDen : 0 < 2 * Real.pi * A - (t + H) := by linarith
  have hDen' : 2 * Real.pi * A - (t + H) ≤
      2 * Real.pi * A - (t + r) := by linarith [hr.2]
  have hFrac : 4 / (2 * Real.pi * A - (t + r)) ≤
      4 / (2 * Real.pi * A - (t + H)) := by
    exact div_le_div_of_nonneg_left (by norm_num) hDen
      hDen'
  exact hRaw.trans (mul_le_mul_of_nonneg_right hFrac
    (Real.rpow_nonneg hA.le _))

/-- On the same symmetric Mellin window the reversed-ordinate integral is
uniformly nonstationary. -/
theorem norm_typeIPowerReflectionIntegral_neg_le_on_symmetric_window
    {sigma t H Q : ℝ} {M : ℕ}
    (hsigma : 0 < sigma) (ht : 0 < t) (hHt : 2 * H ≤ t)
    (hQ : 0 < Q) (hM : 1 ≤ M)
    {r : ℝ} (hr : r ∈ Set.Icc (-H) H) :
    ‖typeIPowerReflectionIntegral sigma (-t + r)
        (Q / 2) (2 * M * Q)‖ ≤
      (8 / t) * (Q / 2) ^ (-sigma) := by
  have hA : 0 < Q / 2 := by positivity
  have hAB : Q / 2 ≤ 2 * M * Q := by
    have hMReal : (1 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hRight : -t + r < 2 * Real.pi * (Q / 2) := by
    have hrUpper := hr.2
    have hNeg : -t + r ≤ -t / 2 := by linarith
    have hPiQ : 0 < 2 * Real.pi * (Q / 2) := by positivity
    linarith
  have hRaw := norm_powerWeighted_gmReflectionIntegral_le_right
    hsigma hA hAB hRight
  have hDen : t / 2 ≤ 2 * Real.pi * (Q / 2) - (-t + r) := by
    have hrUpper := hr.2
    have hPiQ : 0 ≤ 2 * Real.pi * (Q / 2) := by positivity
    linarith
  have hDenPos : 0 < 2 * Real.pi * (Q / 2) - (-t + r) := by
    linarith
  have hFrac : 4 / (2 * Real.pi * (Q / 2) - (-t + r)) ≤ 8 / t := by
    rw [div_le_div_iff₀ hDenPos ht]
    nlinarith
  exact hRaw.trans (mul_le_mul_of_nonneg_right hFrac
    (Real.rpow_nonneg hA.le _))

/-- Literal `L¹` mass of the fixed dyadic Mellin kernel. -/
noncomputable def typeIDyadicCutoffMellinL1 : ℝ :=
  ∫ r : ℝ, ‖typeIDyadicCutoffMellin r‖

theorem typeIDyadicCutoffMellinL1_nonneg :
    0 ≤ typeIDyadicCutoffMellinL1 := by
  unfold typeIDyadicCutoffMellinL1
  exact integral_nonneg fun _ => norm_nonneg _

/-- Restricting the fixed Mellin kernel cannot increase its total `L¹`
mass. -/
theorem integral_norm_typeIDyadicCutoffMellin_restrict_le
    (S : Set ℝ) :
    ∫ r : ℝ in S, ‖typeIDyadicCutoffMellin r‖ ≤
      typeIDyadicCutoffMellinL1 := by
  have hInt : Integrable (fun r : ℝ => ‖typeIDyadicCutoffMellin r‖) := by
    have hMellin : Integrable typeIDyadicCutoffMellin := by
      simpa only [typeIDyadicCutoffMellin, VerticalIntegrable] using
        verticalIntegrable_typeIDyadicCutoffMellin
    exact hMellin.norm
  unfold typeIDyadicCutoffMellinL1
  exact integral_mono_measure Measure.restrict_le_self
    (Eventually.of_forall fun _ => norm_nonneg _) hInt

/-- Exact norm assembly for one interval of negative Poisson modes.  It is
the reusable bridge from a uniform central-kernel estimate and a genuine
Mellin-tail estimate back to the source-normalized finite interval. -/
theorem norm_sourceScalar_mul_negativeInterval_le_of_kernel_tail
    {sigma t H K E : ℝ} {Q L U : ℕ}
    (hsigma : 0 ≤ sigma) (hQ : 0 < Q) (hLU : L < U)
    (_hH : 0 ≤ H) (_hK : 0 ≤ K)
    (hKernel : ∀ r ∈ Set.Icc (-H) H,
      ‖typeIPowerReflectionIntegral sigma (t + r)
        ((((L + 1 : ℕ) : ℝ) * (Q : ℝ)) / 2)
        (2 * (U : ℝ) * (Q : ℝ))‖ ≤ K)
    (hTail :
      ‖∫ r : ℝ in (Set.Icc (-H) H)ᶜ,
          typeIReflectedIntervalMellinPolynomial sigma t (Q : ℝ) L U r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r)
                ((((L + 1 : ℕ) : ℝ) * (Q : ℝ)) / 2)
                (2 * (U : ℝ) * (Q : ℝ))‖ ≤ E) :
    ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
        typeINormalizedNegativeInterval sigma t Q L U‖ ≤
      (1 / (2 * Real.pi)) *
        ((Q : ℝ) * ((U : ℝ) * (U : ℝ) ^ sigma) * K *
          typeIDyadicCutoffMellinL1 + E) := by
  have hQReal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hR : 0 ≤ (U : ℝ) * (U : ℝ) ^ sigma := by positivity
  have hCentral := norm_setIntegral_typeIReflectedIntervalMellinIntegrand_le
    measurableSet_Icc hQReal hR
    (S := Set.Icc (-H) H)
    (R := (U : ℝ) * (U : ℝ) ^ sigma) (K := K)
    (fun r _hr => norm_typeIReflectedIntervalFixedPolynomial_le
      hsigma (t + r) L U) hKernel
  have hMass := integral_norm_typeIDyadicCutoffMellin_restrict_le
    (Set.Icc (-H) H)
  have hCentral' :
      ‖∫ r : ℝ in Set.Icc (-H) H,
          typeIReflectedIntervalMellinPolynomial sigma t (Q : ℝ) L U r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r)
                ((((L + 1 : ℕ) : ℝ) * (Q : ℝ)) / 2)
                (2 * (U : ℝ) * (Q : ℝ))‖ ≤
        (Q : ℝ) * ((U : ℝ) * (U : ℝ) ^ sigma) * K *
          typeIDyadicCutoffMellinL1 := by
    exact hCentral.trans (mul_le_mul_of_nonneg_left hMass (by positivity))
  have hInt := integrable_typeIReflectedIntervalMellinIntegrand
    (sigma := sigma) (t := t) (Q := (Q : ℝ)) hsigma hQReal hLU
  have hSplit := integral_add_compl
    (s := Set.Icc (-H) H) measurableSet_Icc hInt
  have hWhole :
      ‖∫ r : ℝ,
          typeIReflectedIntervalMellinPolynomial sigma t (Q : ℝ) L U r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r)
                ((((L + 1 : ℕ) : ℝ) * (Q : ℝ)) / 2)
                (2 * (U : ℝ) * (Q : ℝ))‖ ≤
        (Q : ℝ) * ((U : ℝ) * (U : ℝ) ^ sigma) * K *
          typeIDyadicCutoffMellinL1 + E := by
    rw [← hSplit]
    exact (norm_add_le _ _).trans (add_le_add hCentral' hTail)
  have hEq := sourceScalar_mul_negativeInterval_eq_reflectedMellinIntegral
    (t := t) hsigma hQ hLU
  have hNorm := congrArg norm hEq
  simp only [norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))] at hNorm
  rw [hNorm]
  exact mul_le_mul_of_nonneg_left hWhole (by positivity)

/-- A large exact interval-form Mellin integral forces a large fixed
interval polynomial at one bounded ordinate displacement. -/
theorem exists_large_typeIReflectedIntervalFixedPolynomial_of_integral
    {sigma t Q H X R K E : ℝ} {L U : ℕ}
    (hsigma : 0 ≤ sigma) (hQ : 0 < Q) (hLU : L < U)
    (hH : 0 ≤ H) (hR : 0 ≤ R)
    (hKernel : ∀ r ∈ Set.Icc (-H) H,
      ‖typeIPowerReflectionIntegral sigma (t + r)
        ((((L + 1 : ℕ) : ℝ) * Q) / 2)
        (2 * (U : ℝ) * Q)‖ ≤ K)
    (hLarge : X ≤ ‖∫ r : ℝ,
      typeIReflectedIntervalMellinPolynomial sigma t Q L U r *
        typeIDyadicCutoffMellin r *
          typeIPowerReflectionIntegral sigma (t + r)
            ((((L + 1 : ℕ) : ℝ) * Q) / 2)
            (2 * (U : ℝ) * Q)‖)
    (hTail : ‖∫ r : ℝ in (Set.Icc (-H) H)ᶜ,
      typeIReflectedIntervalMellinPolynomial sigma t Q L U r *
        typeIDyadicCutoffMellin r *
          typeIPowerReflectionIntegral sigma (t + r)
            ((((L + 1 : ℕ) : ℝ) * Q) / 2)
            (2 * (U : ℝ) * Q)‖ ≤ E)
    (hGap : Q * R * K * typeIDyadicCutoffMellinL1 + E < X) :
    ∃ r ∈ Set.Icc (-H) H,
      R < ‖typeIReflectedIntervalFixedPolynomial sigma (t + r) L U‖ := by
  by_contra h
  push Not at h
  have hK : 0 ≤ K := by
    have hZeroMem : (0 : ℝ) ∈ Set.Icc (-H) H := by
      constructor <;> linarith
    exact (norm_nonneg _).trans (hKernel 0 hZeroMem)
  have hCentral := norm_setIntegral_typeIReflectedIntervalMellinIntegrand_le
    measurableSet_Icc hQ hR
    (S := Set.Icc (-H) H) (R := R) (K := K) h hKernel
  have hMass := integral_norm_typeIDyadicCutoffMellin_restrict_le
    (Set.Icc (-H) H)
  have hCentral' :
      ‖∫ r : ℝ in Set.Icc (-H) H,
          typeIReflectedIntervalMellinPolynomial sigma t Q L U r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r)
                ((((L + 1 : ℕ) : ℝ) * Q) / 2)
                (2 * (U : ℝ) * Q)‖ ≤
        Q * R * K * typeIDyadicCutoffMellinL1 := by
    exact hCentral.trans (mul_le_mul_of_nonneg_left hMass (by positivity))
  have hInt := integrable_typeIReflectedIntervalMellinIntegrand
    (t := t) hsigma hQ hLU
  have hSplit := integral_add_compl
    (s := Set.Icc (-H) H) measurableSet_Icc hInt
  have hWhole :
      ‖∫ r : ℝ,
          typeIReflectedIntervalMellinPolynomial sigma t Q L U r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r)
                ((((L + 1 : ℕ) : ℝ) * Q) / 2)
                (2 * (U : ℝ) * Q)‖ ≤
        Q * R * K * typeIDyadicCutoffMellinL1 + E := by
    rw [← hSplit]
    exact (norm_add_le _ _).trans (add_le_add hCentral' hTail)
  linarith

/-- A large exact reflected Mellin integral forces a large value of the
fixed reflected polynomial at one bounded ordinate displacement.  The tail
and central-kernel losses are explicit premises, not hidden in a choice. -/
theorem exists_large_typeIReflectedFixedPolynomial_of_integral
    {sigma t Q H L R K E : ℝ} {M : ℕ}
    (hsigma : 0 ≤ sigma) (hQ : 0 < Q) (hM : 1 ≤ M)
    (hH : 0 ≤ H) (hR : 0 ≤ R)
    (hKernel : ∀ r ∈ Set.Icc (-H) H,
      ‖typeIPowerReflectionIntegral sigma (t + r)
        (Q / 2) (2 * M * Q)‖ ≤ K)
    (hLarge : L ≤ ‖∫ r : ℝ,
      typeIReflectedMellinPolynomial sigma t Q M r *
        typeIDyadicCutoffMellin r *
          typeIPowerReflectionIntegral sigma (t + r)
            (Q / 2) (2 * M * Q)‖)
    (hTail : ‖∫ r : ℝ in (Set.Icc (-H) H)ᶜ,
      typeIReflectedMellinPolynomial sigma t Q M r *
        typeIDyadicCutoffMellin r *
          typeIPowerReflectionIntegral sigma (t + r)
            (Q / 2) (2 * M * Q)‖ ≤ E)
    (hGap : Q * R * K * typeIDyadicCutoffMellinL1 + E < L) :
    ∃ r ∈ Set.Icc (-H) H,
      R < ‖typeIReflectedFixedPolynomial sigma (t + r) M‖ := by
  by_contra h
  push Not at h
  have hK : 0 ≤ K := by
    have hZeroMem : (0 : ℝ) ∈ Set.Icc (-H) H := by
      constructor <;> linarith
    exact (norm_nonneg _).trans (hKernel 0 hZeroMem)
  have hCentral := norm_setIntegral_typeIReflectedMellinIntegrand_le
    measurableSet_Icc hQ hR
    (S := Set.Icc (-H) H) (R := R) (K := K) h hKernel
  have hMass := integral_norm_typeIDyadicCutoffMellin_restrict_le
    (Set.Icc (-H) H)
  have hCentral' :
      ‖∫ r : ℝ in Set.Icc (-H) H,
          typeIReflectedMellinPolynomial sigma t Q M r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r)
                (Q / 2) (2 * M * Q)‖ ≤
        Q * R * K * typeIDyadicCutoffMellinL1 := by
    exact hCentral.trans (mul_le_mul_of_nonneg_left hMass (by positivity))
  have hInt := integrable_typeIReflectedMellinIntegrand
    (t := t) hsigma hQ hM
  have hSplit := integral_add_compl
    (s := Set.Icc (-H) H) measurableSet_Icc hInt
  have hWhole :
      ‖∫ r : ℝ,
          typeIReflectedMellinPolynomial sigma t Q M r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r)
                (Q / 2) (2 * M * Q)‖ ≤
        Q * R * K * typeIDyadicCutoffMellinL1 + E := by
    rw [← hSplit]
    exact (norm_add_le _ _).trans (add_le_add hCentral' hTail)
  linarith

/-- Norm form of the exact negative-mode Mellin identity. -/
theorem norm_typeIReflectedMellinIntegral_eq_two_pi_mul_negativeModes
    {sigma t : ℝ} {Q M : ℕ} (hsigma : 0 ≤ sigma)
    (hQ : 0 < Q) (hM : 1 ≤ M) :
    ‖∫ r : ℝ,
        typeIReflectedMellinPolynomial sigma t (Q : ℝ) M r *
          typeIDyadicCutoffMellin r *
            typeIPowerReflectionIntegral sigma (t + r)
              ((Q : ℝ) / 2) (2 * M * Q)‖ =
      2 * Real.pi *
        ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
          typeINormalizedNegativeModes sigma t Q M‖ := by
  have hEq := sourceScalar_mul_negativeModes_eq_reflectedMellinIntegral
    (t := t) hsigma hQ hM
  have hNorm := congrArg norm hEq
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity :
      0 < 1 / (2 * Real.pi))] at hNorm
  have hPi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [hNorm]
  field_simp

/-- Norm form of the exact positive-mode Mellin identity.  Conjugation
changes neither side's norm, so the same `2π` normalization as in the
negative half is retained. -/
theorem norm_typeIReflectedPositiveMellinIntegral_eq_two_pi_mul_positiveModes
    {sigma t : ℝ} {Q M : ℕ} (hsigma : 0 ≤ sigma)
    (hQ : 0 < Q) (hM : 1 ≤ M) :
    ‖∫ r : ℝ,
        typeIReflectedMellinPolynomial sigma (-t) (Q : ℝ) M r *
          typeIDyadicCutoffMellin r *
            typeIPowerReflectionIntegral sigma (-t + r)
              ((Q : ℝ) / 2) (2 * M * Q)‖ =
      2 * Real.pi *
        ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
          typeINormalizedPositiveModes sigma t Q M‖ := by
  have hEq := sourceScalar_mul_positiveModes_eq_reflectedMellinIntegral
    (t := t) hsigma hQ hM
  have hNorm := congrArg norm hEq
  simp only [norm_star, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))] at hNorm
  rw [hNorm]
  field_simp [Real.pi_ne_zero]

/-- A large retained negative half forces a large value of the common
fixed reflected polynomial at a bounded Mellin displacement. -/
theorem exists_large_reflectedFixedPolynomial_of_negativeModes
    {sigma t H L R K E : ℝ} {Q M : ℕ}
    (hsigma : 0 ≤ sigma) (hQ : 0 < Q) (hM : 1 ≤ M)
    (hH : 0 ≤ H) (hR : 0 ≤ R)
    (hLarge : L ≤
      ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
        typeINormalizedNegativeModes sigma t Q M‖)
    (hKernel : ∀ u ∈ Set.Icc (-H) H,
      ‖typeIPowerReflectionIntegral sigma (t + u)
        ((Q : ℝ) / 2) (2 * M * Q)‖ ≤ K)
    (hTail :
      ‖∫ u : ℝ in (Set.Icc (-H) H)ᶜ,
        typeIReflectedMellinPolynomial sigma t (Q : ℝ) M u *
          typeIDyadicCutoffMellin u *
            typeIPowerReflectionIntegral sigma (t + u)
              ((Q : ℝ) / 2) (2 * M * Q)‖ ≤ E)
    (hGap : (Q : ℝ) * R * K * typeIDyadicCutoffMellinL1 + E <
      2 * Real.pi * L) :
    ∃ u ∈ Set.Icc (-H) H,
      R < ‖typeIReflectedFixedPolynomial sigma (t + u) M‖ := by
  have hIntegralEq := norm_typeIReflectedMellinIntegral_eq_two_pi_mul_negativeModes
    (sigma := sigma) (t := t) (Q := Q) (M := M) hsigma hQ hM
  have hIntegralLarge : 2 * Real.pi * L ≤
      ‖∫ u : ℝ,
        typeIReflectedMellinPolynomial sigma t (Q : ℝ) M u *
          typeIDyadicCutoffMellin u *
            typeIPowerReflectionIntegral sigma (t + u)
              ((Q : ℝ) / 2) (2 * M * Q)‖ := by
    rw [hIntegralEq]
    exact mul_le_mul_of_nonneg_left hLarge (by positivity)
  exact exists_large_typeIReflectedFixedPolynomial_of_integral
    hsigma (by exact_mod_cast hQ) hM hH hR hKernel hIntegralLarge hTail hGap

/-- The corresponding extraction for the retained positive half.  Its
fixed polynomial occurs at the reversed source ordinate, exactly as in the
proved conjugation identity. -/
theorem exists_large_reflectedFixedPolynomial_of_positiveModes
    {sigma t H L R K E : ℝ} {Q M : ℕ}
    (hsigma : 0 ≤ sigma) (hQ : 0 < Q) (hM : 1 ≤ M)
    (hH : 0 ≤ H) (hR : 0 ≤ R)
    (hLarge : L ≤
      ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
        typeINormalizedPositiveModes sigma t Q M‖)
    (hKernel : ∀ u ∈ Set.Icc (-H) H,
      ‖typeIPowerReflectionIntegral sigma (-t + u)
        ((Q : ℝ) / 2) (2 * M * Q)‖ ≤ K)
    (hTail :
      ‖∫ u : ℝ in (Set.Icc (-H) H)ᶜ,
        typeIReflectedMellinPolynomial sigma (-t) (Q : ℝ) M u *
          typeIDyadicCutoffMellin u *
            typeIPowerReflectionIntegral sigma (-t + u)
              ((Q : ℝ) / 2) (2 * M * Q)‖ ≤ E)
    (hGap : (Q : ℝ) * R * K * typeIDyadicCutoffMellinL1 + E <
      2 * Real.pi * L) :
    ∃ u ∈ Set.Icc (-H) H,
      R < ‖typeIReflectedFixedPolynomial sigma (-t + u) M‖ := by
  have hIntegralEq :=
    norm_typeIReflectedPositiveMellinIntegral_eq_two_pi_mul_positiveModes
      (sigma := sigma) (t := t) (Q := Q) (M := M) hsigma hQ hM
  have hIntegralLarge : 2 * Real.pi * L ≤
      ‖∫ u : ℝ,
        typeIReflectedMellinPolynomial sigma (-t) (Q : ℝ) M u *
          typeIDyadicCutoffMellin u *
            typeIPowerReflectionIntegral sigma (-t + u)
              ((Q : ℝ) / 2) (2 * M * Q)‖ := by
    rw [hIntegralEq]
    exact mul_le_mul_of_nonneg_left hLarge (by positivity)
  exact exists_large_typeIReflectedFixedPolynomial_of_integral
    hsigma (by exact_mod_cast hQ) hM hH hR hKernel hIntegralLarge hTail hGap

/-- The complete positive-mode block is nonstationary on the bounded
Mellin window; outside that window the arbitrary-order Mellin tail applies.
Every dependence on the dual cutoff is explicit. -/
theorem exists_norm_sourceScalar_mul_positiveModes_le
    (n : ℕ) (hn : 1 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ {sigma t H : ℝ} {Q M : ℕ},
      0 < sigma → 0 < t → 1 ≤ H → 2 * H ≤ t →
      0 < Q → 1 ≤ M →
      ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
          typeINormalizedPositiveModes sigma t Q M‖ ≤
        (1 / (2 * Real.pi)) *
          ((Q : ℝ) * ((M : ℝ) * (M : ℝ) ^ sigma) *
              ((8 / t) * ((Q : ℝ) / 2) ^ (-sigma)) *
                typeIDyadicCutoffMellinL1 +
            (Q : ℝ) * ((M : ℝ) * (M : ℝ) ^ sigma) *
              ((2 * (M : ℝ) * (Q : ℝ) - (Q : ℝ) / 2) *
                  (((Q : ℝ) / 2) ^ (-sigma) / ((Q : ℝ) / 2)) *
                C * H ^ (1 - (n : ℝ)))) := by
  obtain ⟨C, hC, hTail⟩ := exists_norm_typeIReflectedMellinIntegral_tail_le n hn
  refine ⟨C, hC, ?_⟩
  intro sigma t H Q M hsigma ht hH hHt hQ hM
  have hQReal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hR : 0 ≤ (M : ℝ) * (M : ℝ) ^ sigma := by positivity
  have hCentral := norm_setIntegral_typeIReflectedMellinIntegrand_le
    measurableSet_Icc hQReal hR
    (S := Set.Icc (-H) H)
    (t := -t) (R := (M : ℝ) * (M : ℝ) ^ sigma)
    (K := (8 / t) * ((Q : ℝ) / 2) ^ (-sigma))
    (fun r _hr => norm_typeIReflectedFixedPolynomial_le hsigma.le (-t + r) M)
    (fun r hr => norm_typeIPowerReflectionIntegral_neg_le_on_symmetric_window
      hsigma ht hHt hQReal hM hr)
  have hMass := integral_norm_typeIDyadicCutoffMellin_restrict_le
    (Set.Icc (-H) H)
  have hCentral' :
      ‖∫ r : ℝ in Set.Icc (-H) H,
          typeIReflectedMellinPolynomial sigma (-t) (Q : ℝ) M r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (-t + r)
                ((Q : ℝ) / 2) (2 * M * Q)‖ ≤
        (Q : ℝ) * ((M : ℝ) * (M : ℝ) ^ sigma) *
          ((8 / t) * ((Q : ℝ) / 2) ^ (-sigma)) *
            typeIDyadicCutoffMellinL1 := by
    exact hCentral.trans (mul_le_mul_of_nonneg_left hMass (by positivity))
  have hTail' := hTail (sigma := sigma) (t := -t) (Q := (Q : ℝ))
    (H := H) (M := M) hsigma.le hQReal hM hH
  have hInt := integrable_typeIReflectedMellinIntegrand
    (sigma := sigma) (t := -t) (Q := (Q : ℝ)) hsigma.le hQReal hM
  have hSplit := integral_add_compl
    (s := Set.Icc (-H) H) measurableSet_Icc hInt
  have hWhole :
      ‖∫ r : ℝ,
          typeIReflectedMellinPolynomial sigma (-t) (Q : ℝ) M r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (-t + r)
                ((Q : ℝ) / 2) (2 * M * Q)‖ ≤
        (Q : ℝ) * ((M : ℝ) * (M : ℝ) ^ sigma) *
              ((8 / t) * ((Q : ℝ) / 2) ^ (-sigma)) *
                typeIDyadicCutoffMellinL1 +
            (Q : ℝ) * ((M : ℝ) * (M : ℝ) ^ sigma) *
              ((2 * (M : ℝ) * (Q : ℝ) - (Q : ℝ) / 2) *
                  (((Q : ℝ) / 2) ^ (-sigma) / ((Q : ℝ) / 2)) *
                C * H ^ (1 - (n : ℝ))) := by
    rw [← hSplit]
    exact (norm_add_le _ _).trans (add_le_add hCentral' hTail')
  have hEq := sourceScalar_mul_positiveModes_eq_reflectedMellinIntegral
    (t := t) hsigma.le hQ hM
  have hNorm := congrArg norm hEq
  simp only [norm_star, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))] at hNorm
  rw [hNorm]
  exact mul_le_mul_of_nonneg_left hWhole (by positivity)

/-- Zero-mode decay after restoring the exact source normalization. -/
theorem exists_sourceScalar_zeroMode_decay (sigma : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (Q : ℕ), 0 < Q →
      |t| ^ j *
        ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
          ((Q : ℂ) * typeINormalizedFourier sigma t 0)‖ ≤
        (Q : ℝ) ^ (1 - sigma) * C := by
  obtain ⟨C, hC, hDecay⟩ := typeINormalizedFourier_zero_uniform_decay sigma j
  refine ⟨C, hC, ?_⟩
  intro t Q hQ
  have hQReal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hNormQ : ‖(Q : ℂ)‖ = (Q : ℝ) := by
    rw [Complex.norm_natCast]
  have hQP : (Q : ℝ) ^ (-sigma) * (Q : ℝ) =
      (Q : ℝ) ^ (1 - sigma) := by
    calc
      (Q : ℝ) ^ (-sigma) * (Q : ℝ) =
          (Q : ℝ) ^ (-sigma) * (Q : ℝ) ^ (1 : ℝ) := by
            rw [Real.rpow_one]
      _ = (Q : ℝ) ^ (-sigma + 1) := by
            rw [Real.rpow_add hQReal]
      _ = (Q : ℝ) ^ (1 - sigma) := by ring_nf
  rw [norm_mul, norm_mul,
    norm_typeISourceNormalizationScalar sigma t (Q : ℝ) hQReal,
    hNormQ]
  calc
    |t| ^ j * ((Q : ℝ) ^ (-sigma) *
          ((Q : ℝ) * ‖typeINormalizedFourier sigma t 0‖)) =
      (Q : ℝ) ^ (1 - sigma) *
        (|t| ^ j * ‖typeINormalizedFourier sigma t 0‖) := by
          rw [← hQP]
          ring_nf
    _ ≤ (Q : ℝ) ^ (1 - sigma) * C := by
      gcongr
      exact hDecay t

/-- Far-frequency decay after restoring the exact source normalization. -/
theorem exists_sourceScalar_farModes_bound (sigma : ℝ) (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (t : ℝ) (Q M : ℕ),
      0 < Q → 0 < M →
      ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
          typeINormalizedFarTail sigma t Q M‖ ≤
        (Q : ℝ) ^ (-sigma) *
          (K * (1 + |t|) ^ (n + 2) /
            ((Q : ℝ) ^ (n + 1) * (M : ℝ) ^ n)) := by
  obtain ⟨K, hK, hFar⟩ := typeINormalizedFarTail_bound_order sigma n
  refine ⟨K, hK, ?_⟩
  intro t Q M hQ hM
  have hQReal : (0 : ℝ) < Q := by exact_mod_cast hQ
  rw [norm_mul, norm_typeISourceNormalizationScalar sigma t (Q : ℝ) hQReal]
  exact mul_le_mul_of_nonneg_left (hFar t Q M hQ hM)
    (Real.rpow_nonneg hQReal.le _)

/-- Removing the zero, wrong-sign, and far-frequency terms from the exact
Poisson decomposition leaves a genuinely large negative reflected block. -/
theorem sourceSmoothBlock_large_forces_negativeModes
    {Y A r M : ℕ} {sigma t V : ℝ}
    (hY : 0 < Y)
    (hLower : ((Y + 1 : ℕ) : ℝ) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2))
    (hUpper : (2 * (2 ^ r * Y : ℕ) : ℕ) ≤ A)
    (hV : 0 ≤ V)
    (hLarge : V ≤ ‖typeISourceSmoothBlock Y A r sigma t‖)
    (hZero :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        (((2 ^ r * Y : ℕ) : ℂ) *
          typeINormalizedFourier sigma t 0)‖ ≤ V / 8)
    (hPositive :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedPositiveModes sigma t (2 ^ r * Y) M‖ ≤ V / 8)
    (hFar :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedFarTail sigma t (2 ^ r * Y) M‖ ≤ V / 8) :
    V / 2 ≤
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedNegativeModes sigma t (2 ^ r * Y) M‖ := by
  let Q : ℕ := 2 ^ r * Y
  let z : ℂ := ((Q : ℂ) * typeINormalizedFourier sigma t 0)
  let neg : ℂ := typeINormalizedNegativeModes sigma t Q M
  let pos : ℂ := typeINormalizedPositiveModes sigma t Q M
  let far : ℂ := typeINormalizedFarTail sigma t Q M
  let c : ℂ := typeISourceNormalizationScalar sigma t Q
  have hDecomp := typeISourceSmoothBlock_eq_mode_decomposition_of_interior
    hY hLower hUpper (M := M) (sigma := sigma) (t := t)
  have hTriangle : ‖typeISourceSmoothBlock Y A r sigma t‖ ≤
      ‖c * z‖ + ‖c * neg‖ + ‖c * pos‖ + ‖c * far‖ := by
    rw [hDecomp]
    change ‖c * (z + neg + pos + far)‖ ≤
      ‖c * z‖ + ‖c * neg‖ + ‖c * pos‖ + ‖c * far‖
    rw [mul_add, mul_add, mul_add]
    calc
      ‖c * z + c * neg + c * pos + c * far‖ ≤
          ‖c * z + c * neg + c * pos‖ + ‖c * far‖ := norm_add_le _ _
      _ ≤ (‖c * z + c * neg‖ + ‖c * pos‖) + ‖c * far‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ ((‖c * z‖ + ‖c * neg‖) + ‖c * pos‖) + ‖c * far‖ := by
        gcongr
        exact norm_add_le _ _
      _ = ‖c * z‖ + ‖c * neg‖ + ‖c * pos‖ + ‖c * far‖ := by ring
  have hTotal : V ≤ ‖c * z‖ + ‖c * neg‖ + ‖c * pos‖ + ‖c * far‖ :=
    hLarge.trans hTriangle
  have hz : ‖c * z‖ ≤ V / 8 := by simpa only [Q, z, c] using hZero
  have hp : ‖c * pos‖ ≤ V / 8 := by simpa only [Q, pos, c] using hPositive
  have hf : ‖c * far‖ ≤ V / 8 := by simpa only [Q, far, c] using hFar
  have : V / 2 ≤ ‖c * neg‖ := by linarith
  simpa only [Q, neg, c] using this

/-- Once the zero, positive, and genuinely far Poisson terms have been
removed, the negative modes may be restricted further to a literal
stationary annulus.  The low- and high-frequency errors are stated as norms
of the exact interval sums, so the conclusion retains cancellation within
each of the three pieces and does not pass through a pointwise mode bound. -/
theorem sourceSmoothBlock_large_forces_negative_stationary_interval
    {Y A r M P J : ℕ} {sigma t V : ℝ}
    (hY : 0 < Y)
    (hLower : ((Y + 1 : ℕ) : ℝ) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2))
    (hUpper : (2 * (2 ^ r * Y : ℕ) : ℕ) ≤ A)
    (hPJ : P ≤ 2 ^ J * P) (hJM : 2 ^ J * P ≤ M)
    (hV : 0 ≤ V)
    (hLarge : V ≤ ‖typeISourceSmoothBlock Y A r sigma t‖)
    (hZero :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        (((2 ^ r * Y : ℕ) : ℂ) *
          typeINormalizedFourier sigma t 0)‖ ≤ V / 8)
    (hPositive :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedPositiveModes sigma t (2 ^ r * Y) M‖ ≤ V / 8)
    (hFar :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedFarTail sigma t (2 ^ r * Y) M‖ ≤ V / 8)
    (hLow :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedNegativeInterval sigma t (2 ^ r * Y) 0 P‖ ≤ V / 8)
    (hHigh :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedNegativeInterval sigma t (2 ^ r * Y)
          (2 ^ J * P) M‖ ≤ V / 8) :
    V / 4 ≤
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedNegativeInterval sigma t (2 ^ r * Y)
          P (2 ^ J * P)‖ := by
  have hNegative := sourceSmoothBlock_large_forces_negativeModes
    hY hLower hUpper hV hLarge hZero hPositive hFar
  have hSplit := typeINormalizedNegativeModes_eq_three_intervals
    sigma t (2 ^ r * Y) P (2 ^ J * P) M hPJ hJM
  let c : ℂ := typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ)
  let low : ℂ := typeINormalizedNegativeInterval sigma t
    (2 ^ r * Y) 0 P
  let central : ℂ := typeINormalizedNegativeInterval sigma t
    (2 ^ r * Y) P (2 ^ J * P)
  let high : ℂ := typeINormalizedNegativeInterval sigma t
    (2 ^ r * Y) (2 ^ J * P) M
  have hTriangle :
      ‖c * typeINormalizedNegativeModes sigma t (2 ^ r * Y) M‖ ≤
        ‖c * low‖ + ‖c * central‖ + ‖c * high‖ := by
    rw [hSplit]
    change ‖c * (low + central + high)‖ ≤ _
    rw [mul_add, mul_add]
    exact (norm_add_le _ _).trans
      (add_le_add (norm_add_le _ _) le_rfl)
  have hTotal : V / 2 ≤ ‖c * low‖ + ‖c * central‖ + ‖c * high‖ := by
    exact hNegative.trans (by simpa only [c] using hTriangle)
  have hLow' : ‖c * low‖ ≤ V / 8 := by
    simpa only [c, low] using hLow
  have hHigh' : ‖c * high‖ ≤ V / 8 := by
    simpa only [c, high] using hHigh
  have : V / 4 ≤ ‖c * central‖ := by linarith
  simpa only [c, central] using this

/-- The stationary interval isolated above feeds the exact interval Mellin
identity and hence produces one fixed-coefficient reflected polynomial at a
bounded ordinate displacement.  This is the cancellation-preserving source
entry for the later family extraction theorem. -/
theorem exists_large_stationary_reflected_interval_of_source
    {Y A r M P J : ℕ} {sigma t V H R K E : ℝ}
    (hY : 0 < Y)
    (hLower : ((Y + 1 : ℕ) : ℝ) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2))
    (hUpper : (2 * (2 ^ r * Y : ℕ) : ℕ) ≤ A)
    (hP : 0 < P) (hJ : 0 < J) (hJM : 2 ^ J * P ≤ M)
    (hsigma : 0 ≤ sigma) (hV : 0 ≤ V) (hH : 0 ≤ H) (hR : 0 ≤ R)
    (hLarge : V ≤ ‖typeISourceSmoothBlock Y A r sigma t‖)
    (hZero :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        (((2 ^ r * Y : ℕ) : ℂ) *
          typeINormalizedFourier sigma t 0)‖ ≤ V / 8)
    (hPositive :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedPositiveModes sigma t (2 ^ r * Y) M‖ ≤ V / 8)
    (hFar :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedFarTail sigma t (2 ^ r * Y) M‖ ≤ V / 8)
    (hLow :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedNegativeInterval sigma t (2 ^ r * Y) 0 P‖ ≤ V / 8)
    (hHigh :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedNegativeInterval sigma t (2 ^ r * Y)
          (2 ^ J * P) M‖ ≤ V / 8)
    (hKernel : ∀ u ∈ Set.Icc (-H) H,
      ‖typeIPowerReflectionIntegral sigma (t + u)
        ((((P + 1 : ℕ) : ℝ) * (2 ^ r * Y : ℕ)) / 2)
        (2 * ((2 ^ J * P : ℕ) : ℝ) * (2 ^ r * Y : ℕ))‖ ≤ K)
    (hTail :
      ‖∫ u : ℝ in (Set.Icc (-H) H)ᶜ,
        typeIReflectedIntervalMellinPolynomial sigma t
            ((2 ^ r * Y : ℕ) : ℝ) P (2 ^ J * P) u *
          typeIDyadicCutoffMellin u *
            typeIPowerReflectionIntegral sigma (t + u)
              ((((P + 1 : ℕ) : ℝ) * (2 ^ r * Y : ℕ)) / 2)
              (2 * ((2 ^ J * P : ℕ) : ℝ) * (2 ^ r * Y : ℕ))‖ ≤ E)
    (hGap :
      ((2 ^ r * Y : ℕ) : ℝ) * R * K * typeIDyadicCutoffMellinL1 + E <
        Real.pi * V / 2) :
    ∃ u ∈ Set.Icc (-H) H,
      R < ‖typeIReflectedIntervalFixedPolynomial sigma (t + u)
        P (2 ^ J * P)‖ := by
  have hPJ : P ≤ 2 ^ J * P :=
    Nat.le_mul_of_pos_left P (pow_pos (by omega : 0 < 2) J)
  have hStationary := sourceSmoothBlock_large_forces_negative_stationary_interval
    hY hLower hUpper hPJ hJM hV hLarge hZero hPositive hFar hLow hHigh
  have hQ : 0 < 2 ^ r * Y := by positivity
  have hLU : P < 2 ^ J * P := by
    have hTwoPow : 1 < 2 ^ J := one_lt_pow₀ (by omega) (Nat.ne_of_gt hJ)
    nlinarith
  have hIdentity := sourceScalar_mul_negativeInterval_eq_reflectedMellinIntegral
    (sigma := sigma) (t := t) (Q := 2 ^ r * Y)
      (L := P) (U := 2 ^ J * P) hsigma hQ hLU
  have hNorm := congrArg norm hIdentity
  simp only [norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))] at hNorm
  have hIntegralLarge : Real.pi * V / 2 ≤
      ‖∫ u : ℝ,
        typeIReflectedIntervalMellinPolynomial sigma t
            ((2 ^ r * Y : ℕ) : ℝ) P (2 ^ J * P) u *
          typeIDyadicCutoffMellin u *
            typeIPowerReflectionIntegral sigma (t + u)
              ((((P + 1 : ℕ) : ℝ) * (2 ^ r * Y : ℕ)) / 2)
              (2 * ((2 ^ J * P : ℕ) : ℝ) * (2 ^ r * Y : ℕ))‖ := by
    rw [hNorm] at hStationary
    have hTwoPiPos : 0 < 2 * Real.pi := by positivity
    have hScaled := mul_le_mul_of_nonneg_left hStationary hTwoPiPos.le
    field_simp at hScaled
    have hScaled' : 2 * Real.pi * V ≤
        4 * ‖∫ u : ℝ,
          typeIReflectedIntervalMellinPolynomial sigma t
              ((2 ^ r * Y : ℕ) : ℝ) P (2 ^ J * P) u *
            typeIDyadicCutoffMellin u *
              typeIPowerReflectionIntegral sigma (t + u)
                ((((P + 1 : ℕ) : ℝ) * (2 ^ r * Y : ℕ)) / 2)
                (2 * ((2 ^ J * P : ℕ) : ℝ) * (2 ^ r * Y : ℕ))‖ := by
      convert hScaled using 1
      ring
    nlinarith [Real.pi_pos]
  exact exists_large_typeIReflectedIntervalFixedPolynomial_of_integral
    hsigma (by exact_mod_cast hQ) hLU hH hR hKernel hIntegralLarge hTail hGap

/-- If only the zero frequency and the genuinely far frequencies are
discarded, one of the two retained signed Poisson halves carries a fixed
fraction of the original smooth Type-I large value.  This is the
cancellation-safe alternative used in the endpoint proof: the positive
half is not estimated term-by-term and hence no factor depending on the
dual cutoff is introduced. -/
theorem sourceSmoothBlock_large_forces_signedModes
    {Y A r M : ℕ} {sigma t V : ℝ}
    (hY : 0 < Y)
    (hLower : ((Y + 1 : ℕ) : ℝ) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2))
    (hUpper : (2 * (2 ^ r * Y : ℕ) : ℕ) ≤ A)
    (hV : 0 ≤ V)
    (hLarge : V ≤ ‖typeISourceSmoothBlock Y A r sigma t‖)
    (hZero :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        (((2 ^ r * Y : ℕ) : ℂ) *
          typeINormalizedFourier sigma t 0)‖ ≤ V / 8)
    (hFar :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedFarTail sigma t (2 ^ r * Y) M‖ ≤ V / 8) :
    V / 4 ≤
        ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
          typeINormalizedNegativeModes sigma t (2 ^ r * Y) M‖ ∨
      V / 4 ≤
        ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
          typeINormalizedPositiveModes sigma t (2 ^ r * Y) M‖ := by
  let Q : ℕ := 2 ^ r * Y
  let z : ℂ := (Q : ℂ) * typeINormalizedFourier sigma t 0
  let neg : ℂ := typeINormalizedNegativeModes sigma t Q M
  let pos : ℂ := typeINormalizedPositiveModes sigma t Q M
  let far : ℂ := typeINormalizedFarTail sigma t Q M
  let c : ℂ := typeISourceNormalizationScalar sigma t Q
  have hDecomp := typeISourceSmoothBlock_eq_mode_decomposition_of_interior
    hY hLower hUpper (M := M) (sigma := sigma) (t := t)
  have hTriangle : ‖typeISourceSmoothBlock Y A r sigma t‖ ≤
      ‖c * z‖ + ‖c * neg‖ + ‖c * pos‖ + ‖c * far‖ := by
    rw [hDecomp]
    change ‖c * (z + neg + pos + far)‖ ≤
      ‖c * z‖ + ‖c * neg‖ + ‖c * pos‖ + ‖c * far‖
    rw [mul_add, mul_add, mul_add]
    calc
      ‖c * z + c * neg + c * pos + c * far‖ ≤
          ‖c * z + c * neg + c * pos‖ + ‖c * far‖ := norm_add_le _ _
      _ ≤ (‖c * z + c * neg‖ + ‖c * pos‖) + ‖c * far‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ ((‖c * z‖ + ‖c * neg‖) + ‖c * pos‖) + ‖c * far‖ := by
        gcongr
        exact norm_add_le _ _
      _ = ‖c * z‖ + ‖c * neg‖ + ‖c * pos‖ + ‖c * far‖ := by ring
  have hTotal : V ≤ ‖c * z‖ + ‖c * neg‖ + ‖c * pos‖ + ‖c * far‖ :=
    hLarge.trans hTriangle
  have hz : ‖c * z‖ ≤ V / 8 := by simpa only [Q, z, c] using hZero
  have hf : ‖c * far‖ ≤ V / 8 := by simpa only [Q, far, c] using hFar
  by_contra h
  push Not at h
  have hn : ‖c * neg‖ < V / 4 := by simpa only [Q, neg, c] using h.1
  have hp : ‖c * pos‖ < V / 4 := by simpa only [Q, pos, c] using h.2
  linarith

/-! ## Source block to a genuine reflected large value -/

/-- A large interior source block, after the zero, wrong-sign, and far
Poisson modes have been removed quantitatively, produces a large value of
the actual fixed-coefficient reflected polynomial at a bounded ordinate
displacement.  The final hypothesis is the exact normalization needed to
pass from the weighted reflected polynomial to the coefficient-bounded wide
Dirichlet polynomial used by Montgomery--Halasz--Huxley. -/
theorem exists_shift_large_normalized_reflected_wide
    {Y A r M : ℕ} {sigma t V H R K E S : ℝ}
    (hY : 0 < Y)
    (hLower : (((Y + 1 : ℕ) : ℝ)) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2))
    (hUpper : (2 * (2 ^ r * Y : ℕ) : ℕ) ≤ A)
    (hsigma : 0 ≤ sigma) (hM : 1 < M)
    (hV : 0 ≤ V) (hH : 0 ≤ H) (hR : 0 ≤ R)
    (hLarge : V ≤ ‖typeISourceSmoothBlock Y A r sigma t‖)
    (hZero :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        (((2 ^ r * Y : ℕ) : ℂ) *
          typeINormalizedFourier sigma t 0)‖ ≤ V / 8)
    (hPositive :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedPositiveModes sigma t (2 ^ r * Y) M‖ ≤ V / 8)
    (hFar :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedFarTail sigma t (2 ^ r * Y) M‖ ≤ V / 8)
    (hKernel : ∀ u ∈ Set.Icc (-H) H,
      ‖typeIPowerReflectionIntegral sigma (t + u)
        (((2 ^ r * Y : ℕ) : ℝ) / 2)
        (2 * M * (2 ^ r * Y : ℕ))‖ ≤ K)
    (hTail :
      ‖∫ u : ℝ in (Set.Icc (-H) H)ᶜ,
        typeIReflectedMellinPolynomial sigma t
            ((2 ^ r * Y : ℕ) : ℝ) M u *
          typeIDyadicCutoffMellin u *
            typeIPowerReflectionIntegral sigma (t + u)
              (((2 ^ r * Y : ℕ) : ℝ) / 2)
              (2 * M * (2 ^ r * Y : ℕ))‖ ≤ E)
    (hGap :
      ((2 ^ r * Y : ℕ) : ℝ) * R * K *
          typeIDyadicCutoffMellinL1 + E < Real.pi * V)
    (hNormalize :
      S + (M : ℝ) ^ (-sigma) ≤ R / (M : ℝ) ^ sigma) :
    ∃ u ∈ Set.Icc (-H) H,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff sigma M) (-(t + u))‖ := by
  have hQ : 0 < 2 ^ r * Y := by positivity
  have hQReal : (0 : ℝ) < (2 ^ r * Y : ℕ) := by exact_mod_cast hQ
  have hMOne : 1 ≤ M := hM.le
  have hNeg := sourceSmoothBlock_large_forces_negativeModes
    hY hLower hUpper hV hLarge hZero hPositive hFar
  have hIntegralNorm :=
    norm_typeIReflectedMellinIntegral_eq_two_pi_mul_negativeModes
      (t := t) hsigma hQ hMOne
  have hIntegralLarge : Real.pi * V ≤
      ‖∫ u : ℝ,
        typeIReflectedMellinPolynomial sigma t
            ((2 ^ r * Y : ℕ) : ℝ) M u *
          typeIDyadicCutoffMellin u *
            typeIPowerReflectionIntegral sigma (t + u)
              (((2 ^ r * Y : ℕ) : ℝ) / 2)
              (2 * M * (2 ^ r * Y : ℕ))‖ := by
    rw [hIntegralNorm]
    nlinarith [Real.pi_pos]
  obtain ⟨u, hu, huLarge⟩ :=
    exists_large_typeIReflectedFixedPolynomial_of_integral
      hsigma hQReal hMOne hH hR hKernel hIntegralLarge hTail hGap
  refine ⟨u, hu, ?_⟩
  have hMReal : (0 : ℝ) < M := by exact_mod_cast (lt_trans Nat.zero_lt_one hM)
  have hDenom : 0 < (M : ℝ) ^ sigma :=
    Real.rpow_pos_of_pos hMReal sigma
  have hFixedDiv : R / (M : ℝ) ^ sigma <
      ‖typeIReflectedFixedPolynomial sigma (t + u) M /
        (((M : ℝ) ^ sigma : ℝ) : ℂ)‖ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hDenom, div_lt_div_iff₀ hDenom hDenom]
    simpa only [mul_comm] using mul_lt_mul_of_pos_right huLarge hDenom
  have hIdentity := wideDirichletPoly_normalizedTypeIReflectedCoeff
    (sigma := sigma) (u := t + u) hM
  let P : ℂ := wideDirichletPoly 1 (Nat.clog 2 M)
    (normalizedTypeIReflectedCoeff sigma M) (-(t + u))
  let z : ℂ := (((M : ℝ) ^ (-sigma) : ℝ) : ℂ)
  have hRearrange :
      typeIReflectedFixedPolynomial sigma (t + u) M /
          (((M : ℝ) ^ sigma : ℝ) : ℂ) = P + z := by
    dsimp only [P, z]
    calc
      typeIReflectedFixedPolynomial sigma (t + u) M /
            (((M : ℝ) ^ sigma : ℝ) : ℂ) =
          (typeIReflectedFixedPolynomial sigma (t + u) M /
              (((M : ℝ) ^ sigma : ℝ) : ℂ) -
            (((M : ℝ) ^ (-sigma) : ℝ) : ℂ)) +
              (((M : ℝ) ^ (-sigma) : ℝ) : ℂ) := by ring
      _ = wideDirichletPoly 1 (Nat.clog 2 M)
            (normalizedTypeIReflectedCoeff sigma M) (-(t + u)) +
              (((M : ℝ) ^ (-sigma) : ℝ) : ℂ) := by rw [← hIdentity]
  have hTriangle :
      ‖typeIReflectedFixedPolynomial sigma (t + u) M /
          (((M : ℝ) ^ sigma : ℝ) : ℂ)‖ ≤
        ‖P‖ + (M : ℝ) ^ (-sigma) := by
    rw [hRearrange]
    calc
      ‖P + z‖ ≤ ‖P‖ + ‖z‖ := norm_add_le _ _
      _ = ‖P‖ + (M : ℝ) ^ (-sigma) := by
        dsimp only [z]
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg hMReal.le _)]
  dsimp only [P] at hTriangle ⊢
  linarith

/-- Algebraic normalization from a large fixed reflected polynomial to the
coefficient-bounded wide polynomial.  This lemma is sign-neutral: the caller
supplies the actual reflected ordinate. -/
theorem large_normalized_reflected_wide_of_fixed
    {M : ℕ} {sigma u R S : ℝ} (hM : 1 < M)
    (hNormalize : S + (M : ℝ) ^ (-sigma) ≤ R / (M : ℝ) ^ sigma)
    (hLarge : R < ‖typeIReflectedFixedPolynomial sigma u M‖) :
    S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
      (normalizedTypeIReflectedCoeff sigma M) (-u)‖ := by
  have hMReal : (0 : ℝ) < M := by
    exact_mod_cast (lt_trans Nat.zero_lt_one hM)
  have hDenom : 0 < (M : ℝ) ^ sigma :=
    Real.rpow_pos_of_pos hMReal sigma
  have hFixedDiv : R / (M : ℝ) ^ sigma <
      ‖typeIReflectedFixedPolynomial sigma u M /
        (((M : ℝ) ^ sigma : ℝ) : ℂ)‖ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hDenom, div_lt_div_iff₀ hDenom hDenom]
    simpa only [mul_comm] using mul_lt_mul_of_pos_right hLarge hDenom
  have hIdentity := wideDirichletPoly_normalizedTypeIReflectedCoeff
    (sigma := sigma) (u := u) hM
  let P : ℂ := wideDirichletPoly 1 (Nat.clog 2 M)
    (normalizedTypeIReflectedCoeff sigma M) (-u)
  let z : ℂ := (((M : ℝ) ^ (-sigma) : ℝ) : ℂ)
  have hRearrange :
      typeIReflectedFixedPolynomial sigma u M /
          (((M : ℝ) ^ sigma : ℝ) : ℂ) = P + z := by
    dsimp only [P, z]
    calc
      typeIReflectedFixedPolynomial sigma u M /
            (((M : ℝ) ^ sigma : ℝ) : ℂ) =
          (typeIReflectedFixedPolynomial sigma u M /
              (((M : ℝ) ^ sigma : ℝ) : ℂ) -
            (((M : ℝ) ^ (-sigma) : ℝ) : ℂ)) +
              (((M : ℝ) ^ (-sigma) : ℝ) : ℂ) := by ring
      _ = wideDirichletPoly 1 (Nat.clog 2 M)
            (normalizedTypeIReflectedCoeff sigma M) (-u) +
              (((M : ℝ) ^ (-sigma) : ℝ) : ℂ) := by rw [← hIdentity]
  have hTriangle :
      ‖typeIReflectedFixedPolynomial sigma u M /
          (((M : ℝ) ^ sigma : ℝ) : ℂ)‖ ≤
        ‖P‖ + (M : ℝ) ^ (-sigma) := by
    rw [hRearrange]
    calc
      ‖P + z‖ ≤ ‖P‖ + ‖z‖ := norm_add_le _ _
      _ = ‖P‖ + (M : ℝ) ^ (-sigma) := by
        dsimp only [z]
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg hMReal.le _)]
  dsimp only [P] at hTriangle ⊢
  linarith

/-- A large interior source block yields one of the two actual normalized
reflected wide polynomials.  The zero and far modes are removed once, and
the sign is selected only after the exact Poisson identity. -/
theorem exists_signed_shift_large_normalized_reflected_wide
    {Y A r M : ℕ} {sigma t V H R K E S : ℝ}
    (hY : 0 < Y)
    (hLower : (((Y + 1 : ℕ) : ℝ)) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2))
    (hUpper : (2 * (2 ^ r * Y : ℕ) : ℕ) ≤ A)
    (hsigma : 0 ≤ sigma) (hM : 1 < M)
    (hV : 0 ≤ V) (hH : 0 ≤ H) (hR : 0 ≤ R)
    (hLarge : V ≤ ‖typeISourceSmoothBlock Y A r sigma t‖)
    (hZero :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        (((2 ^ r * Y : ℕ) : ℂ) *
          typeINormalizedFourier sigma t 0)‖ ≤ V / 8)
    (hFar :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedFarTail sigma t (2 ^ r * Y) M‖ ≤ V / 8)
    (hKernelNeg : ∀ u ∈ Set.Icc (-H) H,
      ‖typeIPowerReflectionIntegral sigma (t + u)
        (((2 ^ r * Y : ℕ) : ℝ) / 2)
        (2 * M * (2 ^ r * Y : ℕ))‖ ≤ K)
    (hKernelPos : ∀ u ∈ Set.Icc (-H) H,
      ‖typeIPowerReflectionIntegral sigma (-t + u)
        (((2 ^ r * Y : ℕ) : ℝ) / 2)
        (2 * M * (2 ^ r * Y : ℕ))‖ ≤ K)
    (hTailNeg :
      ‖∫ u : ℝ in (Set.Icc (-H) H)ᶜ,
        typeIReflectedMellinPolynomial sigma t
            ((2 ^ r * Y : ℕ) : ℝ) M u *
          typeIDyadicCutoffMellin u *
            typeIPowerReflectionIntegral sigma (t + u)
              (((2 ^ r * Y : ℕ) : ℝ) / 2)
              (2 * M * (2 ^ r * Y : ℕ))‖ ≤ E)
    (hTailPos :
      ‖∫ u : ℝ in (Set.Icc (-H) H)ᶜ,
        typeIReflectedMellinPolynomial sigma (-t)
            ((2 ^ r * Y : ℕ) : ℝ) M u *
          typeIDyadicCutoffMellin u *
            typeIPowerReflectionIntegral sigma (-t + u)
              (((2 ^ r * Y : ℕ) : ℝ) / 2)
              (2 * M * (2 ^ r * Y : ℕ))‖ ≤ E)
    (hGap :
      ((2 ^ r * Y : ℕ) : ℝ) * R * K *
          typeIDyadicCutoffMellinL1 + E < Real.pi * V / 2)
    (hNormalize :
      S + (M : ℝ) ^ (-sigma) ≤ R / (M : ℝ) ^ sigma) :
    (∃ u ∈ Set.Icc (-H) H,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff sigma M) (-(t + u))‖) ∨
    (∃ u ∈ Set.Icc (-H) H,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff sigma M) (t - u)‖) := by
  have hQ : 0 < 2 ^ r * Y := by positivity
  have hMOne : 1 ≤ M := hM.le
  rcases sourceSmoothBlock_large_forces_signedModes
      hY hLower hUpper hV hLarge hZero hFar with hNeg | hPos
  · left
    have hGap' :
        ((2 ^ r * Y : ℕ) : ℝ) * R * K *
            typeIDyadicCutoffMellinL1 + E < 2 * Real.pi * (V / 4) := by
      convert hGap using 1
      ring_nf
    obtain ⟨u, hu, hFixed⟩ :=
      exists_large_reflectedFixedPolynomial_of_negativeModes
        hsigma hQ hMOne hH hR hNeg hKernelNeg hTailNeg hGap'
    exact ⟨u, hu,
      large_normalized_reflected_wide_of_fixed hM hNormalize hFixed⟩
  · right
    have hGap' :
        ((2 ^ r * Y : ℕ) : ℝ) * R * K *
            typeIDyadicCutoffMellinL1 + E < 2 * Real.pi * (V / 4) := by
      convert hGap using 1
      ring_nf
    obtain ⟨u, hu, hFixed⟩ :=
      exists_large_reflectedFixedPolynomial_of_positiveModes
        hsigma hQ hMOne hH hR hPos hKernelPos hTailPos hGap'
    have hWide := large_normalized_reflected_wide_of_fixed
      hM hNormalize hFixed
    refine ⟨u, hu, ?_⟩
    convert hWide using 1
    ring_nf

/-- Translating the ordinate of a wide polynomial is exactly the same
unimodular twist of its coefficients as for an ordinary dyadic block. -/
theorem wideDirichletPoly_translate
    (Q k : ℕ) (a : ℕ → ℂ) (c t : ℝ) :
    wideDirichletPoly Q k a (t + c) =
      wideDirichletPoly Q k (phaseShiftCoeffs c a) t := by
  unfold wideDirichletPoly
  apply Finset.sum_congr rfl
  intro n hn
  have hnPos : 0 < n := by
    exact lt_of_le_of_lt (Nat.zero_le Q) (Finset.mem_Ioc.mp hn).1
  have hnNe : (n : ℂ) ≠ 0 := by exact_mod_cast hnPos.ne'
  rw [phaseShiftCoeffs, if_neg hnPos.ne', mul_assoc,
    ← Complex.cpow_add _ _ hnNe]
  congr 2
  push_cast
  ring

/-- Bounded pointwise displacement followed by unit-bin selection.  The
weight on an image point is its complete fibre cardinality, so collisions
cannot silently discard multiplicity. -/
theorem exists_separated_bounded_shift_image_medium
    (W : Finset ℝ) (shift : ℝ → ℝ) (H : ℝ)
    (_hH : 0 ≤ H) (hSeparated : IsSeparated 1 W)
    (hShift : ∀ t ∈ W, |t - shift t| ≤ H) :
    ∃ U ⊆ W.image shift, IsSeparated 1 U ∧
      W.card ≤ 2 * (2 * ⌈H⌉₊ + 1) * U.card := by
  classical
  let weight : ℝ → ℕ := fun _ => 1
  let shiftedWeight : ℝ → ℕ := fun u =>
    ∑ t ∈ W.filter (fun x => shift x = u), weight t
  have hLocalOriginal : ∀ z : ℤ,
      ∑ t ∈ W.filter
          (fun x => (z : ℝ) ≤ x ∧ x < (z : ℝ) + 1), weight t ≤ 1 := by
    intro z
    have hCard :
        (W.filter (fun x => (z : ℝ) ≤ x ∧ x < (z : ℝ) + 1)).card ≤ 1 := by
      rw [Finset.card_le_one_iff]
      intro x y hx hy
      simp only [Finset.mem_filter] at hx hy
      by_contra hxy
      have hSep := hSeparated x hx.1 y hy.1 hxy
      rw [Real.dist_eq] at hSep
      have hlt : |x - y| < 1 := by
        rw [abs_lt]
        constructor <;> linarith [hx.2.1, hx.2.2, hy.2.1, hy.2.2]
      linarith
    simpa only [weight, Finset.sum_const, nsmul_eq_mul, mul_one] using hCard
  have hLocalShifted : ∀ z : ℤ,
      ∑ u ∈ (W.image shift).filter
          (fun v => (z : ℝ) ≤ v ∧ v < (z : ℝ) + 1), shiftedWeight u ≤
        2 * ⌈H⌉₊ + 1 := by
    intro z
    simpa only [shiftedWeight, weight, mul_one] using
      shifted_bin_weight_le_of_unit_bin_weight W weight id shift H 1
        (by simpa only [id_eq] using hShift) hLocalOriginal z
  obtain ⟨U, hUImage, hUSep, hWeight⟩ :=
    weighted_separated_selection (W.image shift) shiftedWeight
      (2 * ⌈H⌉₊ + 1) hLocalShifted
  have hAll : W.filter (fun t => shift t ∈ W.image shift) = W := by
    apply Finset.filter_eq_self.mpr
    intro t ht
    exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
  have hFiber := Finset.sum_fiberwise_eq_sum_filter W (W.image shift)
    shift weight
  rw [hAll] at hFiber
  have hTotal : ∑ u ∈ W.image shift, shiftedWeight u = W.card := by
    simpa only [shiftedWeight, weight, Finset.sum_const, nsmul_eq_mul,
      mul_one] using hFiber
  refine ⟨U, hUImage, hUSep, ?_⟩
  rw [← hTotal]
  simpa only [mul_assoc] using hWeight

/-- Family extraction from a genuine stationary annulus.  The common dyadic
index is chosen before bounded-displacement reseparation, so both the complete
fibre multiplicity and the fixed `T / N` scale are retained. -/
theorem extract_common_negative_reflected_stationary_block
    {P J : ℕ} {sigma T D H R : ℝ} (W : Finset ℝ)
    (hP : 0 < P) (hJ : 0 < J) (hW : W.Nonempty)
    (hH : 0 ≤ H) (hT : 0 ≤ T) (hDH : D + H ≤ T / 2)
    (hSeparated : IsSeparated 1 W)
    (hRange : ∀ t ∈ W, T - D ≤ t ∧ t ≤ 2 * T + D)
    (hEach : ∀ t ∈ W, ∃ u ∈ Set.Icc (-H) H,
      R ≤ ‖typeIReflectedIntervalFixedPolynomial sigma (t + u)
        P (2 ^ J * P)‖) :
    ∃ j ∈ Finset.range J, ∃ U : Finset ℝ,
      IsSeparated 1 U ∧ InBaseInterval (3 * T) U ∧
      W.card ≤ J * (2 * (2 * ⌈H⌉₊ + 1)) * U.card ∧
      ∀ v ∈ U,
        (R / J) / ((2 ^ (j + 1) * P : ℕ) : ℝ) ^ sigma ≤
          ‖dirichletPoly (2 ^ j * P)
            (phaseShiftCoeffs (-3 * T)
              (normalizedTypeIReflectedCoeff sigma
                (2 ^ (j + 1) * P))) v‖ := by
  classical
  have hEachScale : ∀ t ∈ W, ∃ j ∈ Finset.range J,
      ∃ u ∈ Set.Icc (-H) H,
        (R / J) / ((2 ^ (j + 1) * P : ℕ) : ℝ) ^ sigma ≤
          ‖dirichletPoly (2 ^ j * P)
            (normalizedTypeIReflectedCoeff sigma
              (2 ^ (j + 1) * P)) (-(t + u))‖ := by
    intro t ht
    obtain ⟨u, hu, hLarge⟩ := hEach t ht
    obtain ⟨j, hj, hjLarge⟩ :=
      exists_large_normalized_reflected_interval_dyadic_block hP hJ hLarge
    exact ⟨j, hj, u, hu, hjLarge⟩
  let scale : ℝ → ℕ := fun t =>
    if ht : t ∈ W then Classical.choose (hEachScale t ht) else 0
  have hScaleMem : ∀ t ∈ W, scale t ∈ Finset.range J := by
    intro t ht
    simp only [scale, dif_pos ht]
    exact (Classical.choose_spec (hEachScale t ht)).1
  obtain ⟨j, hj, hScaleCard⟩ := weighted_finite_pigeonhole W
    (Finset.range J) (fun _ => 1) scale hW hScaleMem
  let Wj := W.filter (fun t => scale t = j)
  have hWjSub : Wj ⊆ W := Finset.filter_subset _ _
  have hWjSep : IsSeparated 1 Wj := by
    intro x hx y hy hxy
    exact hSeparated x (hWjSub hx) y (hWjSub hy) hxy
  have hWCard : W.card ≤ J * Wj.card := by
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.card_range, Wj] using hScaleCard
  have hWjEach : ∀ t ∈ Wj, ∃ u ∈ Set.Icc (-H) H,
      (R / J) / ((2 ^ (j + 1) * P : ℕ) : ℝ) ^ sigma ≤
        ‖dirichletPoly (2 ^ j * P)
          (normalizedTypeIReflectedCoeff sigma
            (2 ^ (j + 1) * P)) (-(t + u))‖ := by
    intro t ht
    have htData := Finset.mem_filter.mp ht
    have hChosen := (Classical.choose_spec (hEachScale t htData.1)).2
    have hScaleEq : Classical.choose (hEachScale t htData.1) = j := by
      simpa only [scale, dif_pos htData.1] using htData.2
    simpa only [hScaleEq] using hChosen
  let reflect : ℝ → ℝ := fun t => 3 * T - t
  let Wrev : Finset ℝ := Wj.image reflect
  have hReflectInj : Function.Injective reflect := by
    intro x y hxy
    dsimp only [reflect] at hxy
    linarith
  have hWrevCard : Wrev.card = Wj.card := by
    dsimp only [Wrev]
    exact Finset.card_image_iff.mpr fun _ _ _ _ hxy => hReflectInj hxy
  have hWrevSep : IsSeparated 1 Wrev := by
    intro x hx y hy hxy
    rcases Finset.mem_image.mp hx with ⟨tx, htx, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨ty, hty, hyEq⟩
    have htxy : tx ≠ ty := by
      intro h
      subst ty
      exact hxy hyEq
    have hsep := hWjSep tx htx ty hty htxy
    subst y
    rw [Real.dist_eq] at hsep ⊢
    dsimp only [reflect]
    rw [show 3 * T - tx - (3 * T - ty) = -(tx - ty) by ring, abs_neg]
    exact hsep
  have hOriginalMem : ∀ x ∈ Wrev, 3 * T - x ∈ Wj := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨t, ht, rfl⟩
    convert ht using 1
    dsimp only [reflect]
    ring
  let displacement : ℝ → ℝ := fun x =>
    if hx : x ∈ Wrev then Classical.choose
      (hWjEach (3 * T - x) (hOriginalMem x hx)) else 0
  have hDispMem : ∀ x ∈ Wrev,
      displacement x ∈ Set.Icc (-H) H := by
    intro x hx
    simp only [displacement, dif_pos hx]
    exact (Classical.choose_spec
      (hWjEach (3 * T - x) (hOriginalMem x hx))).1
  let shift : ℝ → ℝ := fun x => x - displacement x
  have hShiftBound : ∀ x ∈ Wrev, |x - shift x| ≤ H := by
    intro x hx
    have hd := hDispMem x hx
    dsimp only [shift]
    rw [show x - (x - displacement x) = displacement x by ring]
    exact abs_le.mpr hd
  obtain ⟨U, hUImage, hUSep, hShiftCard⟩ :=
    exists_separated_bounded_shift_image_medium Wrev shift H hH
      hWrevSep hShiftBound
  refine ⟨j, hj, U, hUSep, ?_, ?_, ?_⟩
  · intro v hv
    rcases Finset.mem_image.mp (hUImage hv) with ⟨x, hx, rfl⟩
    have hxRange := hRange (3 * T - x) (hWjSub (hOriginalMem x hx))
    have hdu := hDispMem x hx
    rw [Set.mem_Icc]
    constructor <;> dsimp only [shift]
    · linarith [hdu.2]
    · linarith [hdu.1]
  · calc
      W.card ≤ J * Wj.card := hWCard
      _ = J * Wrev.card := by rw [hWrevCard]
      _ ≤ J * (2 * (2 * ⌈H⌉₊ + 1) * U.card) := by gcongr
      _ = J * (2 * (2 * ⌈H⌉₊ + 1)) * U.card := by ring
  · intro v hv
    rcases Finset.mem_image.mp (hUImage hv) with ⟨x, hx, rfl⟩
    have hLarge := (Classical.choose_spec
      (hWjEach (3 * T - x) (hOriginalMem x hx))).2
    have hDispEq : displacement x = Classical.choose
        (hWjEach (3 * T - x) (hOriginalMem x hx)) := by
      simp only [displacement, dif_pos hx]
    rw [← hDispEq] at hLarge
    have hArg : -((3 * T - x) + displacement x) = shift x + (-3 * T) := by
      dsimp only [shift]
      ring
    rw [hArg, dirichletPoly_translate] at hLarge
    exact hLarge

/-- Family-level source entry for the stationary B-process.  Every analytic
error estimate is still attached to the ordinate where it is used, while the
physical source scale, stationary annulus, Mellin window, and threshold are
common.  The conclusion performs both nontrivial finite selections: first a
dyadic reflected interval and then a one-separated bounded-displacement
subfamily. -/
theorem extract_common_stationary_reflected_block_of_source
    {Y A r M P J : ℕ} {sigma T D H V R K E : ℝ} (W : Finset ℝ)
    (hY : 0 < Y)
    (hLower : ((Y + 1 : ℕ) : ℝ) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2))
    (hUpper : (2 * (2 ^ r * Y : ℕ) : ℕ) ≤ A)
    (hP : 0 < P) (hJ : 0 < J) (hJM : 2 ^ J * P ≤ M)
    (hsigma : 0 ≤ sigma) (hV : 0 ≤ V) (hH : 0 ≤ H) (hR : 0 ≤ R)
    (hW : W.Nonempty) (hT : 0 ≤ T) (hDH : D + H ≤ T / 2)
    (hSeparated : IsSeparated 1 W)
    (hRange : ∀ t ∈ W, T - D ≤ t ∧ t ≤ 2 * T + D)
    (hLarge : ∀ t ∈ W, V ≤ ‖typeISourceSmoothBlock Y A r sigma t‖)
    (hZero : ∀ t ∈ W,
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        (((2 ^ r * Y : ℕ) : ℂ) *
          typeINormalizedFourier sigma t 0)‖ ≤ V / 8)
    (hPositive : ∀ t ∈ W,
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedPositiveModes sigma t (2 ^ r * Y) M‖ ≤ V / 8)
    (hFar : ∀ t ∈ W,
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedFarTail sigma t (2 ^ r * Y) M‖ ≤ V / 8)
    (hLow : ∀ t ∈ W,
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedNegativeInterval sigma t (2 ^ r * Y) 0 P‖ ≤ V / 8)
    (hHigh : ∀ t ∈ W,
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedNegativeInterval sigma t (2 ^ r * Y)
          (2 ^ J * P) M‖ ≤ V / 8)
    (hKernel : ∀ t ∈ W, ∀ u ∈ Set.Icc (-H) H,
      ‖typeIPowerReflectionIntegral sigma (t + u)
        ((((P + 1 : ℕ) : ℝ) * (2 ^ r * Y : ℕ)) / 2)
        (2 * ((2 ^ J * P : ℕ) : ℝ) * (2 ^ r * Y : ℕ))‖ ≤ K)
    (hTail : ∀ t ∈ W,
      ‖∫ u : ℝ in (Set.Icc (-H) H)ᶜ,
        typeIReflectedIntervalMellinPolynomial sigma t
            ((2 ^ r * Y : ℕ) : ℝ) P (2 ^ J * P) u *
          typeIDyadicCutoffMellin u *
            typeIPowerReflectionIntegral sigma (t + u)
              ((((P + 1 : ℕ) : ℝ) * (2 ^ r * Y : ℕ)) / 2)
              (2 * ((2 ^ J * P : ℕ) : ℝ) * (2 ^ r * Y : ℕ))‖ ≤ E)
    (hGap : ((2 ^ r * Y : ℕ) : ℝ) * R * K *
        typeIDyadicCutoffMellinL1 + E < Real.pi * V / 2) :
    ∃ j ∈ Finset.range J, ∃ U : Finset ℝ,
      IsSeparated 1 U ∧ InBaseInterval (3 * T) U ∧
      W.card ≤ J * (2 * (2 * ⌈H⌉₊ + 1)) * U.card ∧
      ∀ v ∈ U,
        (R / J) / ((2 ^ (j + 1) * P : ℕ) : ℝ) ^ sigma ≤
          ‖dirichletPoly (2 ^ j * P)
            (phaseShiftCoeffs (-3 * T)
              (normalizedTypeIReflectedCoeff sigma
                (2 ^ (j + 1) * P))) v‖ := by
  have hEach : ∀ t ∈ W, ∃ u ∈ Set.Icc (-H) H,
      R ≤ ‖typeIReflectedIntervalFixedPolynomial sigma (t + u)
        P (2 ^ J * P)‖ := by
    intro t ht
    obtain ⟨u, hu, hLargeAt⟩ :=
      exists_large_stationary_reflected_interval_of_source
        hY hLower hUpper hP hJ hJM hsigma hV hH hR
        (hLarge t ht) (hZero t ht) (hPositive t ht) (hFar t ht)
        (hLow t ht) (hHigh t ht) (hKernel t ht) (hTail t ht) hGap
    exact ⟨u, hu, hLargeAt.le⟩
  exact extract_common_negative_reflected_stationary_block
    W hP hJ hW hH hT hDH hSeparated hRange hEach

/-- Family form of the reflected extraction.  Each source ordinate may
choose its own bounded Mellin displacement, but the output is reseparated,
translated to one positive base interval, and pigeonholed onto one common
ordinary dyadic block.  The displayed cardinality loss keeps every fibre of
the displacement map. -/
theorem extract_common_reflected_mhh_block
    {M : ℕ} {sigma T D H S : ℝ} (W : Finset ℝ)
    (hM : 1 < M) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (hDH : D + H ≤ T / 2)
    (hSeparated : IsSeparated 1 W)
    (hRange : ∀ t ∈ W, T - D ≤ t ∧ t ≤ 2 * T + D)
    (hEach : ∀ t ∈ W, ∃ u ∈ Set.Icc (-H) H,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff sigma M) (-(t + u))‖) :
    ∃ j ∈ Finset.range (Nat.clog 2 M), ∃ U : Finset ℝ,
      IsSeparated 1 U ∧ InBaseInterval (3 * T) U ∧
      W.card ≤
        (2 * (2 * ⌈H⌉₊ + 1)) * (Nat.clog 2 M) * U.card ∧
      ∀ v ∈ U,
        S / Nat.clog 2 M ≤
          ‖dirichletPoly (2 ^ j)
            (phaseShiftCoeffs (-3 * T)
              (normalizedTypeIReflectedCoeff sigma M)) v‖ := by
  classical
  let reflect : ℝ → ℝ := fun t => 3 * T - t
  let Wrev : Finset ℝ := W.image reflect
  have hreflectInj : Function.Injective reflect := by
    intro x y hxy
    dsimp only [reflect] at hxy
    linarith
  have hWrevCard : Wrev.card = W.card := by
    dsimp only [Wrev]
    exact Finset.card_image_iff.mpr fun _ hx _ hy hxy =>
      hreflectInj hxy
  have hWrevSeparated : IsSeparated 1 Wrev := by
    intro x hx y hy hxy
    rcases Finset.mem_image.mp hx with ⟨tx, htx, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨ty, hty, hyEq⟩
    have htxy : tx ≠ ty := by
      intro h
      subst ty
      exact hxy hyEq
    have hsep := hSeparated tx htx ty hty htxy
    subst y
    rw [Real.dist_eq] at hsep ⊢
    dsimp only [reflect]
    rw [show 3 * T - tx - (3 * T - ty) = -(tx - ty) by ring, abs_neg]
    exact hsep
  have hOriginalMem : ∀ x ∈ Wrev, 3 * T - x ∈ W := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨t, ht, rfl⟩
    convert ht using 1
    dsimp only [reflect]
    ring
  let displacement : ℝ → ℝ := fun x =>
    if hx : x ∈ Wrev then Classical.choose (hEach (3 * T - x)
      (hOriginalMem x hx)) else 0
  have hDisplacementMem : ∀ x ∈ Wrev,
      displacement x ∈ Set.Icc (-H) H := by
    intro x hx
    simp only [displacement, dif_pos hx]
    exact (Classical.choose_spec (hEach (3 * T - x)
      (hOriginalMem x hx))).1
  have hDisplacementLarge : ∀ x ∈ Wrev,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff sigma M)
          (-((3 * T - x) + displacement x))‖ := by
    intro x hx
    simp only [displacement, dif_pos hx]
    exact (Classical.choose_spec (hEach (3 * T - x)
      (hOriginalMem x hx))).2
  let shift : ℝ → ℝ := fun x => x - displacement x
  have hShiftBound : ∀ x ∈ Wrev, |x - shift x| ≤ H := by
    intro x hx
    have hd := hDisplacementMem x hx
    dsimp only [shift]
    rw [show x - (x - displacement x) = displacement x by ring]
    exact abs_le.mpr hd
  obtain ⟨U₀, hU₀Image, hU₀Sep, hCardShift⟩ :=
    exists_separated_bounded_shift_image_medium Wrev shift H hH
      hWrevSeparated hShiftBound
  have hWide : ∀ v ∈ U₀,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (phaseShiftCoeffs (-3 * T)
          (normalizedTypeIReflectedCoeff sigma M)) v‖ := by
    intro v hv
    have hvImage := hU₀Image hv
    rcases Finset.mem_image.mp hvImage with ⟨x, hx, rfl⟩
    have hLarge := hDisplacementLarge x hx
    have hArg : -((3 * T - x) + displacement x) =
        shift x + (-3 * T) := by
      dsimp only [shift]
      ring
    rw [hArg, wideDirichletPoly_translate] at hLarge
    exact hLarge
  have hClog : 0 < Nat.clog 2 M := Nat.clog_pos Nat.one_lt_two hM
  obtain ⟨j, hj, U, hUsub, hCardDyadic, hLargeDyadic⟩ :=
    exists_dyadic_block_and_subset 1 (Nat.clog 2 M)
      (phaseShiftCoeffs (-3 * T)
        (normalizedTypeIReflectedCoeff sigma M)) U₀ S hClog
      (fun v hv => (hWide v hv).le)
  refine ⟨j, hj, U, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    exact hU₀Sep x (hUsub hx) y (hUsub hy) hxy
  · intro v hv
    have hvU₀ := hUsub hv
    have hvImage := hU₀Image hvU₀
    rcases Finset.mem_image.mp hvImage with ⟨x, hx, rfl⟩
    have hxRange := hRange (3 * T - x) (hOriginalMem x hx)
    have hdu := hDisplacementMem x hx
    rw [Set.mem_Icc]
    constructor <;> dsimp only [shift]
    · have hduUpper : displacement x ≤ H := hdu.2
      linarith
    · have hduLower : -H ≤ displacement x := hdu.1
      linarith
  · rw [← hWrevCard]
    calc
      Wrev.card ≤ 2 * (2 * ⌈H⌉₊ + 1) * U₀.card := hCardShift
      _ ≤ 2 * (2 * ⌈H⌉₊ + 1) *
          ((Nat.clog 2 M) * U.card) := by
            gcongr
            exact_mod_cast hCardDyadic
      _ = (2 * (2 * ⌈H⌉₊ + 1)) * (Nat.clog 2 M) * U.card := by ring
  · intro v hv
    simpa only [mul_one] using hLargeDyadic v hv

/-- Positive-sign companion to `extract_common_reflected_mhh_block`.
The positive Poisson half already lands at the positive ordinate `t - u`,
so no reflection about `3T/2` and no coefficient phase shift are needed. -/
theorem extract_common_positive_reflected_mhh_block
    {M : ℕ} {sigma T D H S : ℝ} (W : Finset ℝ)
    (hM : 1 < M) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (hDH : D + H ≤ T / 2)
    (hSeparated : IsSeparated 1 W)
    (hRange : ∀ t ∈ W, T - D ≤ t ∧ t ≤ 2 * T + D)
    (hEach : ∀ t ∈ W, ∃ u ∈ Set.Icc (-H) H,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff sigma M) (t - u)‖) :
    ∃ j ∈ Finset.range (Nat.clog 2 M), ∃ U : Finset ℝ,
      IsSeparated 1 U ∧ InBaseInterval (3 * T) U ∧
      W.card ≤
        (2 * (2 * ⌈H⌉₊ + 1)) * (Nat.clog 2 M) * U.card ∧
      ∀ v ∈ U,
        S / Nat.clog 2 M ≤
          ‖dirichletPoly (2 ^ j)
            (normalizedTypeIReflectedCoeff sigma M) v‖ := by
  classical
  let displacement : ℝ → ℝ := fun t =>
    if ht : t ∈ W then Classical.choose (hEach t ht) else 0
  have hDisplacementMem : ∀ t ∈ W,
      displacement t ∈ Set.Icc (-H) H := by
    intro t ht
    simp only [displacement, dif_pos ht]
    exact (Classical.choose_spec (hEach t ht)).1
  have hDisplacementLarge : ∀ t ∈ W,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff sigma M)
          (t - displacement t)‖ := by
    intro t ht
    simp only [displacement, dif_pos ht]
    exact (Classical.choose_spec (hEach t ht)).2
  let shift : ℝ → ℝ := fun t => t - displacement t
  have hShiftBound : ∀ t ∈ W, |t - shift t| ≤ H := by
    intro t ht
    have hd := hDisplacementMem t ht
    dsimp only [shift]
    rw [show t - (t - displacement t) = displacement t by ring]
    exact abs_le.mpr hd
  obtain ⟨U₀, hU₀Image, hU₀Sep, hCardShift⟩ :=
    exists_separated_bounded_shift_image_medium W shift H hH
      hSeparated hShiftBound
  have hWide : ∀ v ∈ U₀,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff sigma M) v‖ := by
    intro v hv
    rcases Finset.mem_image.mp (hU₀Image hv) with ⟨t, ht, rfl⟩
    exact hDisplacementLarge t ht
  have hClog : 0 < Nat.clog 2 M := Nat.clog_pos Nat.one_lt_two hM
  obtain ⟨j, hj, U, hUsub, hCardDyadic, hLargeDyadic⟩ :=
    exists_dyadic_block_and_subset 1 (Nat.clog 2 M)
      (normalizedTypeIReflectedCoeff sigma M) U₀ S hClog
      (fun v hv => (hWide v hv).le)
  refine ⟨j, hj, U, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    exact hU₀Sep x (hUsub hx) y (hUsub hy) hxy
  · intro v hv
    have hvU₀ := hUsub hv
    rcases Finset.mem_image.mp (hU₀Image hvU₀) with ⟨t, ht, rfl⟩
    have htRange := hRange t ht
    have hdu := hDisplacementMem t ht
    rw [Set.mem_Icc]
    constructor <;> dsimp only [shift]
    · linarith [hdu.2]
    · linarith [hdu.1]
  · calc
      W.card ≤ 2 * (2 * ⌈H⌉₊ + 1) * U₀.card := hCardShift
      _ ≤ 2 * (2 * ⌈H⌉₊ + 1) *
          ((Nat.clog 2 M) * U.card) := by
            gcongr
            exact_mod_cast hCardDyadic
      _ = (2 * (2 * ⌈H⌉₊ + 1)) * (Nat.clog 2 M) * U.card := by ring
  · intro v hv
    simpa only [mul_one] using hLargeDyadic v hv

/-- The common reflected block is an actual input to the unrestricted
Montgomery--Halasz--Huxley theorem.  This is the cardinality conclusion used
later by the medium witness consumer; in particular, the coefficients in the
MHH call are the normalized reflected coefficients produced by the exact
Poisson/Mellin chain above. -/
theorem reflected_family_mhh_cardinality
    {M : ℕ} {sigma T D H S : ℝ} (W : Finset ℝ)
    (hM : 1 < M) (hH : 0 ≤ H) (hT : 1 ≤ T)
    (hDH : D + H ≤ T / 2) (hS : 0 < S)
    (hSeparated : IsSeparated 1 W)
    (hRange : ∀ t ∈ W, T - D ≤ t ∧ t ≤ 2 * T + D)
    (hEach : ∀ t ∈ W, ∃ u ∈ Set.Icc (-H) H,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff sigma M) (-(t + u))‖)
    (hsigma : 0 ≤ sigma) :
    ∃ K : ℝ, 0 < K ∧
      ∃ j ∈ Finset.range (Nat.clog 2 M), ∃ U : Finset ℝ,
        IsSeparated 1 U ∧ InBaseInterval (3 * T) U ∧
        W.card ≤
          (2 * (2 * ⌈H⌉₊ + 1)) * (Nat.clog 2 M) * U.card ∧
        (U.card : ℝ) ≤
          K * (1 + (((harmonic (2 ^ j) : ℚ) : ℝ))) *
            (((2 ^ j : ℕ) : ℝ) ^ 2 / (S / Nat.clog 2 M) ^ 2 +
              (3 * T) * min
                (((2 ^ j : ℕ) : ℝ) / (S / Nat.clog 2 M) ^ 2)
                (((2 ^ j : ℕ) : ℝ) ^ 4 /
                  (S / Nat.clog 2 M) ^ 6)) := by
  obtain ⟨K, hK, hMHH⟩ := classical_large_values_with_harmonic_unrestricted
  obtain ⟨j, hj, U, hUSep, hUBase, hCard, hLarge⟩ :=
    extract_common_reflected_mhh_block W hM hH (zero_le_one.trans hT) hDH
      hSeparated hRange hEach
  have hClog : 0 < Nat.clog 2 M := Nat.clog_pos Nat.one_lt_two hM
  have hThreshold : 0 < S / Nat.clog 2 M := by positivity
  have hCoeff : ∀ n ∈ dyadicInterval (2 ^ j),
      ‖phaseShiftCoeffs (-3 * T)
        (normalizedTypeIReflectedCoeff sigma M) n‖ ≤ 1 := by
    intro n _hn
    rw [norm_phaseShiftCoeffs]
    exact norm_normalizedTypeIReflectedCoeff_le_one hsigma
      (lt_trans Nat.zero_lt_one hM)
  have hAt := hMHH (2 ^ j) (3 * T) (S / Nat.clog 2 M) U
    (phaseShiftCoeffs (-3 * T)
      (normalizedTypeIReflectedCoeff sigma M))
    (pow_pos (by omega) j) (by linarith) hThreshold hCoeff hUSep hUBase
    (fun v hv => hLarge v hv)
  exact ⟨K, hK, j, hj, U, hUSep, hUBase, hCard, hAt⟩

/-- MHH cardinality conclusion for the retained positive Poisson half. -/
theorem positive_reflected_family_mhh_cardinality
    {M : ℕ} {sigma T D H S : ℝ} (W : Finset ℝ)
    (hM : 1 < M) (hH : 0 ≤ H) (hT : 1 ≤ T)
    (hDH : D + H ≤ T / 2) (hS : 0 < S)
    (hSeparated : IsSeparated 1 W)
    (hRange : ∀ t ∈ W, T - D ≤ t ∧ t ≤ 2 * T + D)
    (hEach : ∀ t ∈ W, ∃ u ∈ Set.Icc (-H) H,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff sigma M) (t - u)‖)
    (hsigma : 0 ≤ sigma) :
    ∃ K : ℝ, 0 < K ∧
      ∃ j ∈ Finset.range (Nat.clog 2 M), ∃ U : Finset ℝ,
        IsSeparated 1 U ∧ InBaseInterval (3 * T) U ∧
        W.card ≤
          (2 * (2 * ⌈H⌉₊ + 1)) * (Nat.clog 2 M) * U.card ∧
        (U.card : ℝ) ≤
          K * (1 + (((harmonic (2 ^ j) : ℚ) : ℝ))) *
            (((2 ^ j : ℕ) : ℝ) ^ 2 / (S / Nat.clog 2 M) ^ 2 +
              (3 * T) * min
                (((2 ^ j : ℕ) : ℝ) / (S / Nat.clog 2 M) ^ 2)
                (((2 ^ j : ℕ) : ℝ) ^ 4 /
                  (S / Nat.clog 2 M) ^ 6)) := by
  obtain ⟨K, hK, hMHH⟩ := classical_large_values_with_harmonic_unrestricted
  obtain ⟨j, hj, U, hUSep, hUBase, hCard, hLarge⟩ :=
    extract_common_positive_reflected_mhh_block W hM hH
      (zero_le_one.trans hT) hDH hSeparated hRange hEach
  have hClog : 0 < Nat.clog 2 M := Nat.clog_pos Nat.one_lt_two hM
  have hThreshold : 0 < S / Nat.clog 2 M := by positivity
  have hCoeff : ∀ n ∈ dyadicInterval (2 ^ j),
      ‖normalizedTypeIReflectedCoeff sigma M n‖ ≤ 1 := by
    intro n _hn
    exact norm_normalizedTypeIReflectedCoeff_le_one hsigma
      (lt_trans Nat.zero_lt_one hM)
  have hAt := hMHH (2 ^ j) (3 * T) (S / Nat.clog 2 M) U
    (normalizedTypeIReflectedCoeff sigma M)
    (pow_pos (by omega) j) (by linarith) hThreshold hCoeff hUSep hUBase
    (fun v hv => hLarge v hv)
  exact ⟨K, hK, j, hj, U, hUSep, hUBase, hCard, hAt⟩

/-- A cancellation-safe family pigeonhole for the two retained Poisson
signs.  No point is discarded before the signed alternative is known; the
only loss is the explicit factor two. -/
theorem select_common_signed_reflected_family
    {M : ℕ} {sigma H S : ℝ} (W : Finset ℝ)
    (hEach : ∀ t ∈ W,
      (∃ u ∈ Set.Icc (-H) H,
        S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
          (normalizedTypeIReflectedCoeff sigma M) (-(t + u))‖) ∨
      (∃ u ∈ Set.Icc (-H) H,
        S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
          (normalizedTypeIReflectedCoeff sigma M) (t - u)‖)) :
    (∃ W' : Finset ℝ, W' ⊆ W ∧ W.card ≤ 2 * W'.card ∧
      ∀ t ∈ W', ∃ u ∈ Set.Icc (-H) H,
        S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
          (normalizedTypeIReflectedCoeff sigma M) (-(t + u))‖) ∨
    (∃ W' : Finset ℝ, W' ⊆ W ∧ W.card ≤ 2 * W'.card ∧
      ∀ t ∈ W', ∃ u ∈ Set.Icc (-H) H,
        S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
          (normalizedTypeIReflectedCoeff sigma M) (t - u)‖) := by
  classical
  let isNegative : ℝ → Prop := fun t =>
    ∃ u ∈ Set.Icc (-H) H,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff sigma M) (-(t + u))‖
  let Wneg := W.filter isNegative
  by_cases hLargeHalf : W.card ≤ 2 * Wneg.card
  · left
    refine ⟨Wneg, Finset.filter_subset _ _, hLargeHalf, ?_⟩
    intro t ht
    exact (Finset.mem_filter.mp ht).2
  · right
    let Wpos := W.filter (fun t => ¬ isNegative t)
    have hPartition : Wneg.card + Wpos.card = W.card := by
      simpa only [Wneg, Wpos, isNegative] using
        W.card_filter_add_card_filter_not isNegative
    have hCard : W.card ≤ 2 * Wpos.card := by omega
    refine ⟨Wpos, Finset.filter_subset _ _, hCard, ?_⟩
    intro t ht
    have htData := Finset.mem_filter.mp ht
    rcases hEach t htData.1 with hNeg | hPos
    · exact False.elim (htData.2 hNeg)
    · exact hPos

/-! ## Dual-scale arithmetic -/

/-- If `T = Q^τ`, the reflected length `T/Q` has logarithmic scale
`τ / (τ - 1)`.  This is the exact scale change used by the B-process;
in particular, no direct MHH exponent at the original medium scale is
silently substituted for the reflected one. -/
theorem reflected_logarithmic_scale_identity
    {T Q M τ : ℝ} (hT : 0 < T) (hQ : 1 < Q)
    (hτ : Q ^ τ = T) (hM : M = T / Q) :
    Real.log T / Real.log M = τ / (τ - 1) := by
  have hlogQ : Real.log Q ≠ 0 := (Real.log_pos hQ).ne'
  have hQpos : 0 < Q := zero_lt_one.trans hQ
  have hlogT : Real.log T = τ * Real.log Q := by
    rw [← hτ, Real.log_rpow hQpos]
  have hlogM : Real.log M = (τ - 1) * Real.log Q := by
    rw [hM, Real.log_div hT.ne' hQpos.ne', hlogT]
    ring
  rw [hlogT, hlogM]
  field_simp [hlogQ]

/-- A medium original scale below two reflects to a genuine zeta-polynomial
scale at least two.  This is the branch point used before applying the
certificate's zeta-window alternative or finite powering. -/
theorem two_le_reflected_scale_of_medium
    {τ : ℝ} (hτOne : 1 < τ) (hτTwo : τ ≤ 2) :
    2 ≤ τ / (τ - 1) := by
  rw [le_div_iff₀ (by linarith : 0 < τ - 1)]
  linarith

/-- The exact alternatives for a reflected medium scale.  Once the
original scale is below two, the B-process scale is at least two.  It is
therefore either in the raised-scale powering range or in the certificate's
exceptional zeta window.  In the latter case the certificate says that the
window is empty or lies in the proved Weyl range.  This lemma is deliberately
stated without any polynomial: it is the real-arithmetic routing bridge used
after the exact Poisson/Mellin extraction. -/
theorem reflected_medium_scale_power_or_weyl
    {σ τ₀ τ : ℝ} (hcert : EndpointScaleCertificate σ τ₀)
    (hτOne : 1 < τ) (hτTwo : τ ≤ 2) :
    4 * τ₀ / 3 ≤ τ / (τ - 1) ∨
      False ∨ τ / (τ - 1) < 6 * σ - 3 := by
  let θ := τ / (τ - 1)
  have hθTwo : 2 ≤ θ := by
    simpa only [θ] using two_le_reflected_scale_of_medium hτOne hτTwo
  by_cases hRaised : 4 * τ₀ / 3 ≤ θ
  · exact Or.inl hRaised
  · exact Or.inr (hcert.zeta_window θ hθTwo (lt_of_not_ge hRaised))

/-- If the exceptional zeta window is nonempty, its entire upper endpoint
lies strictly below the Weyl threshold.  This strengthens the pointwise
strict inequality stored in `EndpointScaleCertificate` to the uniform gap
needed when an epsilon-power estimate is assembled. -/
theorem endpoint_zeta_window_upper_lt_weyl
    {σ τ₀ : ℝ} (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀)
    (hWindow : 2 < 4 * τ₀ / 3) :
    4 * τ₀ / 3 < 6 * σ - 3 := by
  have hAtTwo := hcert.zeta_window 2 (by norm_num) hWindow
  have hSigma : 5 / 6 < σ := by
    rcases hAtTwo with hFalse | hTwo
    · exact False.elim hFalse
    · linarith
  rcases endpointScaleCertificate_tau0_alternative hσUpper hcert with hI | hH
  · have : 4 * τ₀ / 3 < 2 := by
      calc
        4 * τ₀ / 3 ≤ 4 * (2 - σ) / 3 := by gcongr
        _ < 2 := by linarith
    linarith
  · calc
      4 * τ₀ / 3 ≤ 4 * (3 * σ - 1) / 3 := by gcongr
      _ < 6 * σ - 3 := by linarith

/-- Uniform Weyl margin for every scale in the exceptional zeta window.
The right side is positive and depends only on the fixed endpoint data,
not on the height or on the dyadic block selected later. -/
theorem endpoint_zeta_window_uniform_margin
    {σ τ₀ τ : ℝ} (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀)
    (hτLower : 2 ≤ τ) (hτUpper : τ < 4 * τ₀ / 3) :
    0 < (6 * σ - 3 - 4 * τ₀ / 3) / 12 ∧
      τ / 6 + 1 / 2 - σ ≤
        -((6 * σ - 3 - 4 * τ₀ / 3) / 12) := by
  have hWindow : 2 < 4 * τ₀ / 3 := hτLower.trans_lt hτUpper
  have hGap := endpoint_zeta_window_upper_lt_weyl
    hσUpper hcert hWindow
  constructor
  · linarith
  · linarith

/-- Natural-power selection in the exact form used by both the original
Type-II branch and every raised reflected Type-I block.  In particular the
selected power is positive and the physical logarithmic scale divided by
that power belongs to `[2 * τ₀ / 3, τ₀]`; no real-valued surrogate for
the power is introduced. -/
theorem exists_endpoint_natural_power
    {τ₀ τ : ℝ} (hτ₀ : 0 < τ₀) (hRaised : 4 * τ₀ / 3 ≤ τ) :
    ∃ k : ℕ, 0 < k ∧ 2 * τ₀ / 3 ≤ τ / k ∧ τ / k ≤ τ₀ :=
  exists_positive_power_scale_reduction hτ₀ hRaised

/-! ## Dyadic realization of a selected source block -/

/-- The fixed coefficient sequence of a source-smooth Type-I block.  All
ordinate dependence remains in the ordinary Dirichlet phase. -/
noncomputable def typeISourceDirichletCoeff
    (Y A r : ℕ) (σ : ℝ) (n : ℕ) : ℂ :=
  (typeISourceSmoothWeight Y A r n : ℂ) *
    (n : ℂ) ^ (-(σ : ℂ))

/-- A source-smooth block is exactly one finite wide Dirichlet polynomial.
The two apparent endpoint discrepancies are genuine zero terms: the left
endpoint is killed by `typeITailBoundary`, and so is `A + 1`. -/
theorem typeISourceSmoothBlock_eq_wideDirichletPoly
    (Y A r : ℕ) (σ t : ℝ) (hY : 1 ≤ Y) :
    typeISourceSmoothBlock Y A r σ t =
      wideDirichletPoly 1 (Nat.clog 2 (A + 1))
        (typeISourceDirichletCoeff Y A r σ) t := by
  classical
  let k := Nat.clog 2 (A + 1)
  let term : ℕ → ℂ := fun n =>
    typeISourceDirichletCoeff Y A r σ n *
      (n : ℂ) ^ (-(t : ℂ) * I)
  have hSmall : Finset.Ioc 1 (A + 1) ⊆ Finset.Icc 1 (A + 1) := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ioc.mp hn).1.le,
      (Finset.mem_Ioc.mp hn).2⟩
  have hLeftZero : ∀ n ∈ Finset.Icc 1 (A + 1), n ∉ Finset.Ioc 1 (A + 1) →
      term n = 0 := by
    intro n hn hnSmall
    have hnOne : n = 1 := by
      have hnData := Finset.mem_Icc.mp hn
      simp only [Finset.mem_Ioc, not_and_or] at hnSmall
      omega
    subst n
    have hnotTail : 1 ∉ Finset.Ioc Y A := by
      simp only [Finset.mem_Ioc, not_and_or]
      exact Or.inl (by omega)
    simp only [term, typeISourceDirichletCoeff, typeISourceSmoothWeight,
      typeITailBoundary_natCast, if_neg hnotTail, Nat.cast_one, zero_mul,
      Complex.ofReal_zero]
  have hSource :
      (∑ n ∈ Finset.Icc 1 (A + 1), term n) =
        ∑ n ∈ Finset.Ioc 1 (A + 1), term n := by
    symm
    exact Finset.sum_subset hSmall hLeftZero
  have hCover : A + 1 ≤ 2 ^ k := by
    dsimp only [k]
    exact Nat.le_pow_clog (by omega) (A + 1)
  have hTailSubset : Finset.Ioc 1 (A + 1) ⊆ Finset.Ioc 1 (2 ^ k) := by
    intro n hn
    exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1,
      (Finset.mem_Ioc.mp hn).2.trans hCover⟩
  have hRightZero : ∀ n ∈ Finset.Ioc 1 (2 ^ k),
      n ∉ Finset.Ioc 1 (A + 1) → term n = 0 := by
    intro n hn hnSmall
    have hnAbove : A + 1 < n := by
      have hnData := Finset.mem_Ioc.mp hn
      simp only [Finset.mem_Ioc, not_and_or] at hnSmall
      omega
    have hnotTail : n ∉ Finset.Ioc Y A := by
      simp only [Finset.mem_Ioc, not_and_or]
      exact Or.inr (by omega)
    simp only [term, typeISourceDirichletCoeff, typeISourceSmoothWeight,
      typeITailBoundary_natCast, if_neg hnotTail, zero_mul,
      Complex.ofReal_zero]
  have hWide :
      (∑ n ∈ Finset.Ioc 1 (2 ^ k), term n) =
        ∑ n ∈ Finset.Ioc 1 (A + 1), term n := by
    symm
    exact Finset.sum_subset hTailSubset hRightZero
  unfold typeISourceSmoothBlock wideDirichletPoly
  simp only [mul_one]
  change (∑ n ∈ Finset.Icc 1 (A + 1), term n) =
    ∑ n ∈ Finset.Ioc 1 (2 ^ k), term n
  rw [hSource, hWide]

/-! ## Powered reflected-family bridge -/

/-- The zero-real-part convention used by the generic powering theorem is
definitionally the ordinary Dirichlet phase after the elementary complex
ring normalization. -/
theorem sum_zero_real_part_eq_dirichletPoly
    (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    (∑ n ∈ Finset.Ioc N (2 * N),
      a n * (n : ℂ) ^ (-(((0 : ℝ) : ℂ) + I * (t : ℂ)))) =
      dirichletPoly N a t := by
  unfold dirichletPoly
  apply Finset.sum_congr rfl
  intro n _hn
  congr 2
  norm_num
  ring

/-- A cancellation-safe reflected family is passed through every finite
combinatorial operation needed before the endpoint exponent calculation:
sign pigeonholing, bounded-displacement reseparation, dyadic extraction,
exact natural powering, and the unrestricted Montgomery--Halasz--Huxley
estimate.  The output retains the complete cardinality loss from the input
family; in particular no displacement fibre or Poisson-sign alternative is
discarded.

The constants are uniform for all positive powers `k <= B`.  This is the
form needed after the endpoint certificate selects `k` from a physical
logarithmic scale depending on `T`. -/
theorem signed_reflected_family_powered_mhh_cardinality
    (B : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ K : ℝ, 0 < K ∧
      ∀ {M k : ℕ} {sigma T D H S : ℝ} (W : Finset ℝ),
        1 < M → 0 < k → k ≤ B → 0 ≤ sigma →
        0 ≤ H → 1 ≤ T → D + H ≤ T / 2 → 0 < S →
        IsSeparated 1 W →
        (∀ t ∈ W, T - D ≤ t ∧ t ≤ 2 * T + D) →
        (∀ t ∈ W,
          (∃ u ∈ Set.Icc (-H) H,
            S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
              (normalizedTypeIReflectedCoeff sigma M) (-(t + u))‖) ∨
          (∃ u ∈ Set.Icc (-H) H,
            S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
              (normalizedTypeIReflectedCoeff sigma M) (t - u)‖)) →
        ∃ j ∈ Finset.range (Nat.clog 2 M),
          ∃ r ∈ Finset.range k, ∃ U : Finset ℝ,
            let P := 2 ^ j
            let Q := 2 ^ r * P ^ k
            let V := ((S / Nat.clog 2 M) ^ k /
                  (C * ((2 ^ k * P ^ k : ℕ) : ℝ) ^ eta)) / k
            IsSeparated 1 U ∧ InBaseInterval (3 * T) U ∧
              (W.card : ℝ) ≤
                2 * (2 * (2 * ⌈H⌉₊ + 1)) *
                  (Nat.clog 2 M) * k * (U.card : ℝ) ∧
              (U.card : ℝ) ≤
                K * (1 + (((harmonic Q : ℚ) : ℝ))) *
                  ((Q : ℝ) ^ 2 / V ^ 2 +
                    (3 * T) * min ((Q : ℝ) / V ^ 2)
                      ((Q : ℝ) ^ 4 / V ^ 6)) := by
  obtain ⟨C, hC, K, hK, hPowered⟩ :=
    powered_unit_block_large_values_bound_bounded_uniform B eta heta
  refine ⟨C, hC, K, hK, ?_⟩
  intro M k sigma T D H S W hM hk hkB hsigma hH hT hDH hS
    hSeparated hRange hEach
  have hClog : 0 < Nat.clog 2 M := Nat.clog_pos Nat.one_lt_two hM
  have hThreshold : 0 < S / Nat.clog 2 M := by positivity
  rcases select_common_signed_reflected_family W hEach with
    ⟨Wsign, hWsign, hSignCard, hNegative⟩ |
      ⟨Wsign, hWsign, hSignCard, hPositive⟩
  · have hSepSign : IsSeparated 1 Wsign := by
      intro x hx y hy hxy
      exact hSeparated x (hWsign hx) y (hWsign hy) hxy
    have hRangeSign : ∀ t ∈ Wsign,
        T - D ≤ t ∧ t ≤ 2 * T + D := by
      intro t ht
      exact hRange t (hWsign ht)
    obtain ⟨j, hj, U₀, hSep₀, hBase₀, hCard₀, hLarge₀⟩ :=
      extract_common_reflected_mhh_block Wsign hM hH
        (zero_le_one.trans hT) hDH hSepSign hRangeSign hNegative
    let P : ℕ := 2 ^ j
    have hP : 0 < P := by dsimp only [P]; positivity
    have hCoeff : ∀ n ∈ Finset.Ioc P (2 * P),
        ‖phaseShiftCoeffs (-3 * T)
          (normalizedTypeIReflectedCoeff sigma M) n‖ ≤ 1 := by
      intro n _hn
      rw [norm_phaseShiftCoeffs]
      exact norm_normalizedTypeIReflectedCoeff_le_one hsigma
        (lt_trans Nat.zero_lt_one hM)
    obtain ⟨r, hr, U, hUsub, hPowerCard, hSepU, hBaseU,
        hLargeU, hMHHU⟩ :=
      hPowered k P
        (phaseShiftCoeffs (-3 * T)
          (normalizedTypeIReflectedCoeff sigma M))
        0 (3 * T) (S / Nat.clog 2 M) U₀ hk hkB hP (by norm_num)
          (by linarith) hThreshold hCoeff hSep₀ hBase₀
          (by
            intro v hv
            rw [sum_zero_real_part_eq_dirichletPoly]
            simpa only [P] using hLarge₀ v hv)
    refine ⟨j, hj, r, hr, U, ?_, ?_, ?_, ?_⟩
    · exact hSepU
    · exact hBaseU
    · calc
        (W.card : ℝ) ≤ 2 * (Wsign.card : ℝ) := by exact_mod_cast hSignCard
        _ ≤ 2 *
            ((2 * (2 * ⌈H⌉₊ + 1)) * (Nat.clog 2 M) *
              (U₀.card : ℝ)) := by
                gcongr
                exact_mod_cast hCard₀
        _ ≤ 2 *
            ((2 * (2 * ⌈H⌉₊ + 1)) * (Nat.clog 2 M) *
              (k * (U.card : ℝ))) := by gcongr
        _ = 2 * (2 * (2 * ⌈H⌉₊ + 1)) *
              (Nat.clog 2 M) * k * (U.card : ℝ) := by ring
    · simpa only [P, Real.rpow_zero, one_mul] using hMHHU
  · have hSepSign : IsSeparated 1 Wsign := by
      intro x hx y hy hxy
      exact hSeparated x (hWsign hx) y (hWsign hy) hxy
    have hRangeSign : ∀ t ∈ Wsign,
        T - D ≤ t ∧ t ≤ 2 * T + D := by
      intro t ht
      exact hRange t (hWsign ht)
    obtain ⟨j, hj, U₀, hSep₀, hBase₀, hCard₀, hLarge₀⟩ :=
      extract_common_positive_reflected_mhh_block Wsign hM hH
        (zero_le_one.trans hT) hDH hSepSign hRangeSign hPositive
    let P : ℕ := 2 ^ j
    have hP : 0 < P := by dsimp only [P]; positivity
    have hCoeff : ∀ n ∈ Finset.Ioc P (2 * P),
        ‖normalizedTypeIReflectedCoeff sigma M n‖ ≤ 1 := by
      intro n _hn
      exact norm_normalizedTypeIReflectedCoeff_le_one hsigma
        (lt_trans Nat.zero_lt_one hM)
    obtain ⟨r, hr, U, hUsub, hPowerCard, hSepU, hBaseU,
        hLargeU, hMHHU⟩ :=
      hPowered k P
        (normalizedTypeIReflectedCoeff sigma M)
        0 (3 * T) (S / Nat.clog 2 M) U₀ hk hkB hP (by norm_num)
          (by linarith) hThreshold hCoeff hSep₀ hBase₀ (by
            intro v hv
            rw [sum_zero_real_part_eq_dirichletPoly]
            simpa only [P] using hLarge₀ v hv)
    refine ⟨j, hj, r, hr, U, ?_, ?_, ?_, ?_⟩
    · exact hSepU
    · exact hBaseU
    · calc
        (W.card : ℝ) ≤ 2 * (Wsign.card : ℝ) := by exact_mod_cast hSignCard
        _ ≤ 2 *
            ((2 * (2 * ⌈H⌉₊ + 1)) * (Nat.clog 2 M) *
              (U₀.card : ℝ)) := by
                gcongr
                exact_mod_cast hCard₀
        _ ≤ 2 *
            ((2 * (2 * ⌈H⌉₊ + 1)) * (Nat.clog 2 M) *
              (k * (U.card : ℝ))) := by gcongr
        _ = 2 * (2 * (2 * ⌈H⌉₊ + 1)) *
              (Nat.clog 2 M) * k * (U.card : ℝ) := by ring
    · simpa only [P, Real.rpow_zero, one_mul] using hMHHU

/-! ## Source-facing medium witness contract -/

/-- Every selected source-smooth scale is either one of the two lower-edge
blocks, one of the upper-edge blocks meeting the terminal cutoff, or is a
genuine interior block to which the normalized Poisson/B-process identity
applies.  This is the exact finite trichotomy behind the source proof; in
particular no boundary block is silently passed to the interior formula. -/
theorem typeISourceSmoothScale_lower_terminal_or_interior
    {Y A r : ℕ} (hY : 0 < Y) :
    r < 2 ∨ A < 2 * (2 ^ r * Y) ∨
      (((Y + 1 : ℕ) : ℝ) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2) ∧
        2 * (2 ^ r * Y) ≤ A) := by
  by_cases hr : r < 2
  · exact Or.inl hr
  right
  by_cases hUpper : A < 2 * (2 ^ r * Y)
  · exact Or.inl hUpper
  right
  constructor
  · have hrTwo : 2 ≤ r := by omega
    have hpow : 4 ≤ 2 ^ r := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hrTwo
    have hYOne : 1 ≤ Y := hY
    have hNat : 2 * (Y + 1) ≤ 2 ^ r * Y := by
      calc
        2 * (Y + 1) ≤ 4 * Y := by omega
        _ ≤ 2 ^ r * Y := Nat.mul_le_mul_right Y hpow
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by
      have hNatReal : (2 : ℝ) * (Y + 1) ≤ (2 ^ r * Y : ℕ) := by
        exact_mod_cast hNat
      norm_num only [Nat.cast_add, Nat.cast_one]
      nlinarith)
  · omega

/-- The finite dual cutoff used in the medium B-process.  The small positive
power is deliberate: it places every stationary frequency inside the finite
window while leaving an arbitrarily small power loss with which to sum the
far-frequency and Mellin tails. -/
noncomputable def mediumTypeIDualCutoff (T d : ℝ) (Q : ℕ) : ℕ :=
  ⌊T ^ (1 + d) / Q⌋₊

theorem mediumTypeIDualCutoff_cast_le
    {T d : ℝ} {Q : ℕ} (hT : 0 ≤ T) :
    (mediumTypeIDualCutoff T d Q : ℝ) ≤ T ^ (1 + d) / Q := by
  unfold mediumTypeIDualCutoff
  exact Nat.floor_le (div_nonneg (Real.rpow_nonneg hT _)
    (Nat.cast_nonneg Q))

theorem mediumTypeIDualCutoff_lt_add_one
    {T d : ℝ} {Q : ℕ} :
    T ^ (1 + d) / Q < mediumTypeIDualCutoff T d Q + 1 := by
  unfold mediumTypeIDualCutoff
  exact Nat.lt_floor_add_one _

/-- Once the source scale lies below height, the expanded dual cutoff is a
positive natural number.  This discharges the floor edge explicitly rather
than treating the dual length as a positive real surrogate. -/
theorem mediumTypeIDualCutoff_pos
    {T d : ℝ} {Q : ℕ} (hT : 1 ≤ T) (hd : 0 ≤ d)
    (hQ : 0 < Q) (hQT : (Q : ℝ) ≤ T) :
    0 < mediumTypeIDualCutoff T d Q := by
  have hPow : T ≤ T ^ (1 + d) := by
    have hExp : (1 : ℝ) ≤ 1 + d := by linarith
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT hExp
  have hRatio : 1 ≤ T ^ (1 + d) / Q := by
    rw [le_div_iff₀ (by exact_mod_cast hQ)]
    simpa only [one_mul] using hQT.trans hPow
  unfold mediumTypeIDualCutoff
  exact Nat.floor_pos.mpr hRatio

/-- Multiplicity-safe entry from the long-tail lower bound carried by the
actual dichotomy witness.  It selects one common smooth scale on one common
subfamily and immediately records whether that scale is a lower edge, an
upper/terminal edge, or a legal interior B-process scale. -/
theorem extract_common_typeISourceSmoothBlock_classified
    {Y A k : ℕ} {σ V : ℝ} (W : Finset ℝ)
    (hY : 1 ≤ Y) (hA : A ≤ 2 ^ k * Y) (hW : W.Nonempty)
    (hSeparated : IsSeparated 1 W)
    (hLarge : ∀ t ∈ W,
      V ≤ ‖classicalZetaLongTail Y A ((σ : ℂ) + I * (t : ℂ))‖) :
    ∃ r ∈ Finset.range (k + 1), ∃ W' : Finset ℝ,
      W' ⊆ W ∧ IsSeparated 1 W' ∧
      W.card ≤ (k + 1) * W'.card ∧
      (∀ t ∈ W', V / (k + 1 : ℕ) ≤
        ‖typeISourceSmoothBlock Y A r σ t‖) ∧
      (r < 2 ∨ A < 2 * (2 ^ r * Y) ∨
        (((Y + 1 : ℕ) : ℝ) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2) ∧
          2 * (2 ^ r * Y) ≤ A)) := by
  obtain ⟨r, hr, W', hW', hSep', hLarge', hCard'⟩ :=
    exists_common_typeISmoothBlock_large Y A k σ V W
      hY hA hW hSeparated hLarge
  exact ⟨r, hr, W', hW', hSep', hCard', hLarge',
    typeISourceSmoothScale_lower_terminal_or_interior hY⟩

/-- The literal `Nat.clog` cover needed to instantiate the classified source
extraction at the sharp zeta cutoff.  The factor `Y` is retained explicitly,
so this also handles the smallest admissible source scale without a hidden
division or positivity assumption. -/
theorem sharp_source_cutoff_le_clog_cover
    {Y A : ℕ} (hY : 1 ≤ Y) :
    A ≤ 2 ^ (Nat.clog 2 A) * Y := by
  by_cases hA : A = 0
  · simp [hA]
  · calc
      A ≤ 2 ^ (Nat.clog 2 A) := Nat.le_pow_clog (by omega) A
      _ ≤ 2 ^ (Nat.clog 2 A) * Y :=
        Nat.le_mul_of_pos_right _ (by omega)

/-- Concrete source selection from the same long-tail lower bound exported by
the detector dichotomy.  The selected family is a subset of the original
family, and the displayed cardinality factor is the only loss; hence the
analytic-multiplicity inequality attached to that original family remains
available to the final slab consumer. -/
theorem actual_medium_long_tail_selects_classified_source
    {T d σ V : ℝ} (W : Finset ℝ)
    (hT : 1 ≤ T) (hW : W.Nonempty)
    (hSeparated : IsSeparated 1 W)
    (hLarge : ∀ t ∈ W,
      V ≤ ‖classicalZetaLongTail ⌊T ^ (d ^ 2)⌋₊
        ⌊sharpZetaCutoff T⌋₊ ((σ : ℂ) + I * (t : ℂ))‖) :
    let Y := ⌊T ^ (d ^ 2)⌋₊
    let A := ⌊sharpZetaCutoff T⌋₊
    let k := Nat.clog 2 A
    ∃ r ∈ Finset.range (k + 1), ∃ W' : Finset ℝ,
      W' ⊆ W ∧ IsSeparated 1 W' ∧
      W.card ≤ (k + 1) * W'.card ∧
      (∀ t ∈ W', V / (k + 1 : ℕ) ≤
        ‖typeISourceSmoothBlock Y A r σ t‖) ∧
      (r < 2 ∨ A < 2 * (2 ^ r * Y) ∨
        (((Y + 1 : ℕ) : ℝ) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2) ∧
          2 * (2 ^ r * Y) ≤ A)) := by
  dsimp only
  have hPowOne : 1 ≤ T ^ (d ^ 2) :=
    Real.one_le_rpow hT (sq_nonneg d)
  have hY : 1 ≤ ⌊T ^ (d ^ 2)⌋₊ :=
    (Nat.one_le_floor_iff _).mpr hPowOne
  exact extract_common_typeISourceSmoothBlock_classified W hY
    (sharp_source_cutoff_le_clog_cover hY) hW hSeparated hLarge

/-- Exhaustive arithmetic routing of a scale in the endpoint gap.  Scales at
or beyond height are terminal, scales at most square-root height are in the
ordinary zeta/Weyl regime, and only the strict interval `(1,2)` is sent
through the reflected scale `τ/(τ-1)`. -/
theorem endpoint_gap_terminal_zeta_or_reflected
    {σ τ₀ τ : ℝ} (hcert : EndpointScaleCertificate σ τ₀) :
    τ ≤ 1 ∨ 2 ≤ τ ∨
      (1 < τ ∧ τ < 2 ∧
        (4 * τ₀ / 3 ≤ τ / (τ - 1) ∨
          False ∨ τ / (τ - 1) < 6 * σ - 3)) := by
  by_cases hTerminal : τ ≤ 1
  · exact Or.inl hTerminal
  right
  by_cases hZeta : 2 ≤ τ
  · exact Or.inl hZeta
  right
  refine ⟨lt_of_not_ge hTerminal, lt_of_not_ge hZeta, ?_⟩
  exact reflected_medium_scale_power_or_weyl hcert
    (lt_of_not_ge hTerminal) (le_of_not_ge hZeta)

/-! ## Uniform growth on the genuinely reflected branch -/

/-- Once the terminal B-process contradiction does not apply, the physical
source scale is separated from height by a fixed positive power.  The
separation is derived from the same numerical margin used by the detector;
it is not an extra scale hypothesis. -/
theorem medium_complementary_source_scale_bounds
    {sigma d T tau : ℝ} {Q : ℕ}
    (hsigma : 1 / 2 < sigma)
    (hd : 0 < d) (hdGap : d ≤ (sigma - 1 / 2) / 1000)
    (hT : 1 ≤ T) (hQ : 1 < Q)
    (hScale : (Q : ℝ) ^ tau = T)
    (hMargin : -100 * d ≤ tau / 2 - sigma) :
    let a := 2 * sigma - 200 * d
    let gamma := 1 - 1 / a
    1 < a ∧ a ≤ tau ∧ 0 < gamma ∧
      (Q : ℝ) ^ a ≤ T ∧
      (Q : ℝ) ≤ T ^ (1 / a) ∧
      T ^ gamma ≤ T ^ (1 + d) / Q := by
  dsimp only
  let a : ℝ := 2 * sigma - 200 * d
  have haOne : 1 < a := by
    dsimp only [a]
    have hSigmaGap : 0 < sigma - 1 / 2 := sub_pos.mpr hsigma
    have hScaled : 200 * d ≤ (sigma - 1 / 2) / 5 := by
      calc
        200 * d ≤ 200 * ((sigma - 1 / 2) / 1000) := by gcongr
        _ = (sigma - 1 / 2) / 5 := by ring
    linarith [hSigmaGap]
  have haPos : 0 < a := zero_lt_one.trans haOne
  have haTau : a ≤ tau := by
    dsimp only [a]
    linarith
  have hQReal : (1 : ℝ) < Q := by exact_mod_cast hQ
  have hQa : (Q : ℝ) ^ a ≤ T := by
    rw [← hScale]
    exact Real.rpow_le_rpow_of_exponent_le hQReal.le haTau
  have hInvNonneg : 0 ≤ 1 / a := by positivity
  have hQRoot := Real.rpow_le_rpow
    (Real.rpow_nonneg (Nat.cast_nonneg Q) a) hQa hInvNonneg
  have hQPow : ((Q : ℝ) ^ a) ^ (1 / a) = (Q : ℝ) := by
    rw [← Real.rpow_mul (by positivity)]
    field_simp [haPos.ne']
    exact Real.rpow_one (Q : ℝ)
  have hQUpper : (Q : ℝ) ≤ T ^ (1 / a) := by
    simpa only [hQPow] using hQRoot
  let gamma : ℝ := 1 - 1 / a
  have hgamma : 0 < gamma := by
    dsimp only [gamma]
    rw [sub_pos, div_lt_one haPos]
    exact haOne
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have hPowSplit : T ^ gamma * T ^ (1 / a) = T := by
    rw [← Real.rpow_add hTPos]
    dsimp only [gamma]
    calc
      T ^ (1 - 1 / a + 1 / a) = T ^ (1 : ℝ) := by
        congr 1
        field_simp [haPos.ne']
        ring
      _ = T := Real.rpow_one T
  have hRatio : T ^ gamma ≤ T / Q := by
    rw [le_div_iff₀ (by exact_mod_cast (lt_trans Nat.zero_lt_one hQ))]
    calc
      T ^ gamma * (Q : ℝ) ≤ T ^ gamma * T ^ (1 / a) := by gcongr
      _ = T := hPowSplit
  have hPowMono : T ≤ T ^ (1 + d) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT (by linarith : (1 : ℝ) ≤ 1 + d)
  refine ⟨haOne, haTau, hgamma, hQa, hQUpper, ?_⟩
  exact hRatio.trans (div_le_div_of_nonneg_right hPowMono (Nat.cast_nonneg Q))

/-- A real lower bound at least two survives natural flooring with only a
factor two.  This is the exact floor bridge used for the reflected cutoff. -/
theorem half_le_natFloor_of_two_le {x : ℝ} (hx : 2 ≤ x) :
    x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have hFloor : x < (⌊x⌋₊ : ℝ) + 1 := by
    exact_mod_cast Nat.lt_floor_add_one x
  nlinarith

/-- The actual natural dual cutoff therefore grows by the fixed positive
power supplied by `medium_complementary_source_scale_bounds`. -/
theorem mediumTypeIDualCutoff_lower_of_complementary_margin
    {sigma d T tau : ℝ} {Q : ℕ}
    (hsigma : 1 / 2 < sigma)
    (hd : 0 < d) (hdGap : d ≤ (sigma - 1 / 2) / 1000)
    (hT : 1 ≤ T) (hQ : 1 < Q)
    (hScale : (Q : ℝ) ^ tau = T)
    (hMargin : -100 * d ≤ tau / 2 - sigma)
    (hLarge : 2 ≤ T ^ (1 - 1 / (2 * sigma - 200 * d))) :
    T ^ (1 - 1 / (2 * sigma - 200 * d)) / 2 ≤
      (mediumTypeIDualCutoff T d Q : ℝ) := by
  have hBounds := medium_complementary_source_scale_bounds hsigma hd hdGap
    hT hQ hScale hMargin
  dsimp only at hBounds
  have hRatio := hBounds.2.2.2.2.2
  exact (half_le_natFloor_of_two_le
    (hLarge.trans hRatio)).trans' (by
      exact div_le_div_of_nonneg_right hRatio (by norm_num))

/-- The exact medium Type-I branch which remains after the direct and raised
scale consumers.  The long-tail lower bound is part of the same witness
returned by `classical_typeI_typeII_dichotomy_native`; retaining it here is
what permits a common source-smooth block to be selected without changing
the zero family or discarding analytic multiplicity. -/
def ClassicalMediumTypeIWitnessConsumer : Prop :=
  ∀ {σ τ₀ : ℝ}, 1 / 2 < σ → σ < 1 →
    EndpointScaleCertificate σ τ₀ →
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
        let d := classicalEndpointLossParameter σ τ₀ (ε / 100)
        let Y := ⌊T ^ (d ^ 2)⌋₊
        let A := ⌊sharpZetaCutoff T⌋₊
        ∀ r ∈ Finset.range (Nat.clog 2 A), ∀ W : Finset ℝ,
          IsSeparated 1 W →
          (∀ t ∈ W,
            ((3 / 4) * (T ^ (-d ^ 4) / 2)) / Nat.clog 2 A ≤
              ‖dirichletPoly (2 ^ r * Y)
                (classicalZetaLongLineCoeff A σ) t‖) →
          (∀ t ∈ W,
            (3 / 4) * (T ^ (-d ^ 4) / 2) ≤
              ‖classicalZetaLongTail Y A
                ((σ : ℂ) + I * (t : ℂ))‖) →
          (∀ t ∈ W, T - T ^ d ≤ t ∧ t ≤ 2 * T + T ^ d) →
          zeroCountRect σ 1 T (2 * T) ≤
            4 * Nat.clog 2 A *
              ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T) * W.card →
          τ₀ < typeILogarithmicScale T (2 ^ r * Y) →
          typeILogarithmicScale T (2 ^ r * Y) < 4 * τ₀ / 3 →
          (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
            C * T ^ ε * T ^ (3 * (1 - σ) / τ₀)

end RiemannZeta.GuthMaynard
