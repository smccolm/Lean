import RiemannZeta.GuthMaynard.ClassicalEndpointSlab
import RiemannZeta.GuthMaynard.WeylExplicit

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
  ring_nf

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
    ring_nf
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
      ring_nf
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
      (∀ v ∈ U, T / 2 ≤ v ∧ v ≤ 5 * T / 2) ∧
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
  refine ⟨j, hj, U, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro v hv
    have hvU₀ := hUsub hv
    have hvImage := hU₀Image hvU₀
    rcases Finset.mem_image.mp hvImage with ⟨x, hx, rfl⟩
    have hxRange := hRange (3 * T - x) (hOriginalMem x hx)
    have hdu := hDisplacementMem x hx
    dsimp only [shift]
    constructor
    · linarith [hdu.2]
    · linarith [hdu.1]
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
      (∀ v ∈ U, T / 2 ≤ v ∧ v ≤ 5 * T / 2) ∧
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
  refine ⟨j, hj, U, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro v hv
    have hvU₀ := hUsub hv
    rcases Finset.mem_image.mp (hU₀Image hvU₀) with ⟨t, ht, rfl⟩
    have htRange := hRange t ht
    have hdu := hDisplacementMem t ht
    dsimp only [shift]
    constructor
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
  obtain ⟨j, hj, U, hUSep, hUBase, _hURange, hCard, hLarge⟩ :=
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
  obtain ⟨j, hj, U, hUSep, hUBase, _hURange, hCard, hLarge⟩ :=
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

/-
/-- One cancellation-safe interface for the two retained Poisson signs.
The coefficient sequence is existential because the negative sign carries
the fixed translation by `-3T`, whereas the positive sign does not.  The
last field identifies its norm with the same normalized reflected block at
an actual positive ordinate in `[T/2,5T/2]`; this is the bridge needed by
the Weyl alternative after the finite sign and displacement selections. -/
theorem extract_common_signed_reflected_block
    {M : ℕ} {sigma T D H S : ℝ} (W : Finset ℝ)
    (hM : 1 < M) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (hDH : D + H ≤ T / 2)
    (hSeparated : IsSeparated 1 W)
    (hRange : ∀ t ∈ W, T - D ≤ t ∧ t ≤ 2 * T + D)
    (hEach : ∀ t ∈ W,
      (∃ u ∈ Set.Icc (-H) H,
        S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
          (normalizedTypeIReflectedCoeff sigma M) (-(t + u))‖) ∨
      (∃ u ∈ Set.Icc (-H) H,
        S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
          (normalizedTypeIReflectedCoeff sigma M) (t - u)‖)) :
    ∃ j ∈ Finset.range (Nat.clog 2 M), ∃ U : Finset ℝ,
      ∃ a : ℕ → ℂ,
        IsSeparated 1 U ∧ InBaseInterval (3 * T) U ∧
        (∀ v ∈ U, T / 2 ≤ v ∧ v ≤ 5 * T / 2) ∧
        W.card ≤ 2 * (2 * (2 * ⌈H⌉₊ + 1)) *
          (Nat.clog 2 M) * U.card ∧
        (∀ n ∈ dyadicInterval (2 ^ j), ‖a n‖ ≤ 1) ∧
        (∀ v ∈ U, S / Nat.clog 2 M ≤ ‖dirichletPoly (2 ^ j) a v‖) ∧
        (∀ v ∈ U, ∃ w ∈ Set.Icc (T / 2) (5 * T / 2),
          ‖dirichletPoly (2 ^ j) a v‖ =
            ‖dirichletPoly (2 ^ j)
              (normalizedTypeIReflectedCoeff sigma M) w‖) := by
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
    obtain ⟨j, hj, U, hSepU, hBaseU, hURange, hCardU, hLargeU⟩ :=
      extract_common_reflected_mhh_block Wsign hM hH hT hDH
        hSepSign hRangeSign hNegative
    let a : ℕ → ℂ := phaseShiftCoeffs (-3 * T)
      (normalizedTypeIReflectedCoeff sigma M)
    refine ⟨j, hj, U, a, hSepU, hBaseU, hURange, ?_, ?_, ?_, ?_⟩
    · calc
        W.card ≤ 2 * Wsign.card := hSignCard
        _ ≤ 2 * ((2 * (2 * ⌈H⌉₊ + 1)) *
            (Nat.clog 2 M) * U.card) := by gcongr
        _ = 2 * (2 * (2 * ⌈H⌉₊ + 1)) *
            (Nat.clog 2 M) * U.card := by ring
    · intro n hn
      dsimp only [a]
      rw [norm_phaseShiftCoeffs]
      exact norm_normalizedTypeIReflectedCoeff_le_one (by linarith)
        (lt_trans Nat.zero_lt_one hM)
    · exact hLargeU
    · intro v hv
      refine ⟨3 * T - v, ?_, ?_⟩
      · rw [Set.mem_Icc]
        have hvRange := hURange v hv
        constructor <;> linarith
      · dsimp only [a]
        exact norm_phaseShifted_normalized_reflected_eq sigma T v (2 ^ j) M
  · have hSepSign : IsSeparated 1 Wsign := by
      intro x hx y hy hxy
      exact hSeparated x (hWsign hx) y (hWsign hy) hxy
    have hRangeSign : ∀ t ∈ Wsign,
        T - D ≤ t ∧ t ≤ 2 * T + D := by
      intro t ht
      exact hRange t (hWsign ht)
    obtain ⟨j, hj, U, hSepU, hBaseU, hURange, hCardU, hLargeU⟩ :=
      extract_common_positive_reflected_mhh_block Wsign hM hH hT hDH
        hSepSign hRangeSign hPositive
    let a : ℕ → ℂ := normalizedTypeIReflectedCoeff sigma M
    refine ⟨j, hj, U, a, hSepU, hBaseU, hURange, ?_, ?_, ?_, ?_⟩
    · calc
        W.card ≤ 2 * Wsign.card := hSignCard
        _ ≤ 2 * ((2 * (2 * ⌈H⌉₊ + 1)) *
            (Nat.clog 2 M) * U.card) := by gcongr
        _ = 2 * (2 * (2 * ⌈H⌉₊ + 1)) *
            (Nat.clog 2 M) * U.card := by ring
    · intro n hn
      dsimp only [a]
      exact norm_normalizedTypeIReflectedCoeff_le_one (by linarith)
        (lt_trans Nat.zero_lt_one hM)
    · exact hLargeU
    · intro v hv
      refine ⟨v, hURange v hv, ?_⟩
      rfl
-/

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

/-- The small expansion used in the finite Poisson cutoff cannot create an
uncontrolled gap between the reflected scale and the endpoint alternatives.
If an actual dyadic block has scale at least `1 / (1/2+d)`, then it is either
in the exact powered range or in the Weyl range with the explicit `4d`
slack paid later from the epsilon budget.  The two numerical alternatives
in `EndpointScaleCertificate` are handled separately; this is the finite
boundary calculation which replaces an invalid identification of the
expanded cutoff with `T/Q`. -/
theorem reflected_actual_scale_power_or_weyl_with_slack
    {σ τ₀ τ d : ℝ}
    (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀)
    (hd : 0 < d) (hdGap : d ≤ (σ - 1 / 2) / 1000)
    (hτLower : 1 / (1 / 2 + d) ≤ τ) :
    4 * τ₀ / 3 ≤ τ ∨ τ < 6 * σ - 3 + 4 * d := by
  by_cases hRaised : 4 * τ₀ / 3 ≤ τ
  · exact Or.inl hRaised
  right
  have hτUpper : τ < 4 * τ₀ / 3 := lt_of_not_ge hRaised
  have hReciprocal : 2 - 4 * d < 1 / (1 / 2 + d) := by
    rw [lt_div_iff₀ (by linarith : 0 < 1 / 2 + d)]
    nlinarith [sq_pos_of_pos hd]
  have hNearTwo : 2 - 4 * d < τ := hReciprocal.trans_le hτLower
  rcases endpointScaleCertificate_tau0_alternative hσUpper hcert with hI | hH
  · have hUpperI : τ < 4 * (2 - σ) / 3 := by
      exact hτUpper.trans_le (by gcongr)
    have hGapPos : 0 < σ - 1 / 2 := by linarith
    have hScaled : 1000 * d ≤ σ - 1 / 2 := by
      nlinarith
    nlinarith
  · have hUpperH : τ < 4 * (3 * σ - 1) / 3 := by
      exact hτUpper.trans_le (by gcongr)
    nlinarith

/-- Power selection for the finite `4d` transition strip.  It is applied to
the augmented scale `τ+4d`; the selected power is uniformly bounded, its
augmented scale lies in the exact endpoint window, and its actual scale is
at most `4d` below that window. -/
theorem exists_bounded_positive_power_scale_reduction_with_slack
    {τ₀ τ U d : ℝ} (hτ₀ : 0 < τ₀) (hd : 0 ≤ d)
    (hNear : 4 * τ₀ / 3 - 4 * d ≤ τ)
    (hτUpper : τ ≤ U) :
    ∃ k : ℕ, 0 < k ∧ k ≤ ⌈3 * (U + 4 * d) / (2 * τ₀)⌉₊ ∧
      2 * τ₀ / 3 ≤ (τ + 4 * d) / k ∧
      (τ + 4 * d) / k ≤ τ₀ ∧
      τ / k ≤ (τ + 4 * d) / k ∧
      (τ + 4 * d) / k - τ / k ≤ 4 * d := by
  have hRaised : 4 * τ₀ / 3 ≤ τ + 4 * d := by linarith
  have hUpper : τ + 4 * d ≤ U + 4 * d := by linarith
  obtain ⟨k, hk, hkB, hkLower, hkUpper⟩ :=
    exists_bounded_positive_power_scale_reduction hτ₀ hRaised hUpper
  have hkReal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkPos : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨k, hk, hkB, hkLower, hkUpper, ?_, ?_⟩
  · exact div_le_div_of_nonneg_right (by linarith) hkPos.le
  · rw [← sub_div]
    have hFour : 4 * d / (k : ℝ) ≤ 4 * d := by
      exact div_le_self (by positivity) hkReal
    calc
      (τ + 4 * d - τ) / (k : ℝ) = 4 * d / (k : ℝ) := by ring
      _ ≤ 4 * d := hFour

/-- The transition width used in the reflected endpoint argument.  The
factor `σ - 1/2` is the exact gap that degenerates at the left edge of the
critical strip; scaling by its reciprocal gives the Weyl branch a uniform
positive exponent margin.  The dedicated term in
`classicalEndpointLossParameter` makes this width epsilon-small. -/
noncomputable def reflectedEndpointScaleSlack (σ d : ℝ) : ℝ :=
  100 * d / (σ - 1 / 2)

theorem reflectedEndpointScaleSlack_pos
    {σ d : ℝ} (hσ : 1 / 2 < σ) (hd : 0 < d) :
    0 < reflectedEndpointScaleSlack σ d := by
  unfold reflectedEndpointScaleSlack
  positivity

theorem four_mul_le_reflectedEndpointScaleSlack
    {σ d : ℝ} (hσ : 1 / 2 < σ) (hσUpper : σ < 1) (hd : 0 ≤ d) :
    4 * d ≤ reflectedEndpointScaleSlack σ d := by
  unfold reflectedEndpointScaleSlack
  by_cases hdz : d = 0
  · simp [hdz]
  · have hdPos : 0 < d := lt_of_le_of_ne hd (Ne.symm hdz)
    have hgap : 0 < σ - 1 / 2 := by linarith
    rw [le_div_iff₀ hgap]
    nlinarith

/-- Both critical-strip side-gap terms in the global loss parameter make the
reflected transition width smaller than one sixth of the endpoint scale. -/
theorem reflectedEndpointScaleSlack_le_tau0_sixth
    {σ τ₀ d : ℝ} (hσ : 1 / 2 < σ) (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀)
    (hdGap : d ≤ (σ - 1 / 2) / 1000)
    (hdUpperGap : d ≤ (1 - σ) / 1000) :
    reflectedEndpointScaleSlack σ d ≤ τ₀ / 6 := by
  have hgap : 0 < σ - 1 / 2 := by linarith
  have hDensity : 3 * (1 - σ) ≤ τ₀ := by
    nlinarith [hcert.density_base_le_tau0]
  have hSlackCore : reflectedEndpointScaleSlack σ d ≤
      (2 / 5 : ℝ) * (1 - σ) := by
    unfold reflectedEndpointScaleSlack
    by_cases hmid : σ ≤ 3 / 4
    · have hOneSigma : 1 / 4 ≤ 1 - σ := by linarith
      have hdScaled : 100 * d ≤ (σ - 1 / 2) / 10 := by nlinarith
      rw [div_le_iff₀ hgap]
      have hgapUpper : σ - 1 / 2 ≤ 1 / 4 := by linarith
      nlinarith [mul_pos hgap (sub_pos.mpr hσUpper)]
    · have hgapQuarter : 1 / 4 ≤ σ - 1 / 2 := by linarith
      have hdScaled : 100 * d ≤ (1 - σ) / 10 := by nlinarith
      rw [div_le_iff₀ hgap]
      nlinarith
  nlinarith

/-- Natural power selection after augmenting an actual reflected scale by an
arbitrary nonnegative transition width.  The returned `k` is the literal
natural exponent used by finite Dirichlet-polynomial powering. -/
theorem exists_bounded_positive_power_scale_reduction_with_gap
    {τ₀ τ U s : ℝ} (hτ₀ : 0 < τ₀) (hs : 0 ≤ s)
    (hNear : 4 * τ₀ / 3 - s ≤ τ)
    (hτUpper : τ ≤ U) :
    ∃ k : ℕ, 0 < k ∧ k ≤ ⌈3 * (U + s) / (2 * τ₀)⌉₊ ∧
      2 * τ₀ / 3 ≤ (τ + s) / k ∧
      (τ + s) / k ≤ τ₀ ∧
      τ / k ≤ (τ + s) / k ∧
      (τ + s) / k - τ / k ≤ s := by
  have hRaised : 4 * τ₀ / 3 ≤ τ + s := by linarith
  have hUpper : τ + s ≤ U + s := by linarith
  obtain ⟨k, hk, hkB, hkLower, hkUpper⟩ :=
    exists_bounded_positive_power_scale_reduction hτ₀ hRaised hUpper
  have hkReal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkPos : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨k, hk, hkB, hkLower, hkUpper, ?_, ?_⟩
  · exact div_le_div_of_nonneg_right (by linarith) hkPos.le
  · rw [← sub_div]
    have hGap : s / (k : ℝ) ≤ s := div_le_self hs hkReal
    calc
      (τ + s - τ) / (k : ℝ) = s / (k : ℝ) := by ring
      _ ≤ s := hGap

/-- Endpoint form of the preceding selector.  It also records the lower
bound for the actual powered scale and pays exactly for replacing that scale
by the augmented one. -/
theorem exists_bounded_positive_power_augmented_endpoint_with_gap
    {σ τ₀ τ U s d : ℝ}
    (_hσUpper : σ < 1) (hcert : EndpointScaleCertificate σ τ₀)
    (hs : 0 ≤ s) (_hdUpper : d ≤ (1 - σ) / 1000)
    (hSmall : s ≤ τ₀ / 6)
    (hNear : 4 * τ₀ / 3 - s ≤ τ) (hτUpper : τ ≤ U) :
    ∃ k : ℕ, 0 < k ∧
      k ≤ ⌈3 * (U + s) / (2 * τ₀)⌉₊ ∧
      2 * τ₀ / 3 ≤ (τ + s) / k ∧
      (τ + s) / k ≤ τ₀ ∧
      τ / k ≤ (τ + s) / k ∧
      τ₀ / 2 ≤ τ / k ∧
      (3 * (1 - σ) / τ₀) *
          ((τ + s) / k - τ / k) ≤
        (2 * s / τ₀) * (τ / k) := by
  obtain ⟨k, hk, hkB, hkLower, hkUpper, hkActual, hkGap⟩ :=
    exists_bounded_positive_power_scale_reduction_with_gap
      hcert.tau0_pos hs hNear hτUpper
  have hTauDensity : 3 * (1 - σ) ≤ τ₀ := by
    nlinarith [hcert.density_base_le_tau0]
  have hActualLower : τ₀ / 2 ≤ τ / k := by
    have hGapAt : (τ + s) / k - s ≤ τ / k := by linarith
    have hCore : τ₀ / 2 ≤ (τ + s) / k - s := by
      nlinarith [hkLower]
    exact hCore.trans hGapAt
  have hTargetLeOne : 3 * (1 - σ) / τ₀ ≤ 1 := by
    rw [div_le_one hcert.tau0_pos]
    exact hTauDensity
  have hGapNonneg : 0 ≤ (τ + s) / k - τ / k :=
    sub_nonneg.mpr hkActual
  refine ⟨k, hk, hkB, hkLower, hkUpper, hkActual, hActualLower, ?_⟩
  calc
    (3 * (1 - σ) / τ₀) * ((τ + s) / k - τ / k) ≤ 1 * s := by
      gcongr
    _ ≤ (2 * s / τ₀) * (τ / k) := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hcert.tau0_pos).2
      have hActualNonneg : 0 ≤ τ / (k : ℝ) :=
        (div_nonneg hcert.tau0_pos.le (by norm_num)).trans hActualLower
      nlinarith [mul_nonneg hs hActualNonneg]

/-- The augmented-scale power selector already supplies the exact exponent
budget required by the endpoint conversion.  The lower density constraint
in the certificate and the explicit `d ≤ (1-σ)/1000` bound keep the actual
powered scale uniformly positive after the `4d` correction. -/
theorem exists_bounded_positive_power_augmented_endpoint
    {σ τ₀ τ U d : ℝ}
    (hσUpper : σ < 1) (hcert : EndpointScaleCertificate σ τ₀)
    (hd : 0 ≤ d) (hdUpper : d ≤ (1 - σ) / 1000)
    (hNear : 4 * τ₀ / 3 - 4 * d ≤ τ) (hτUpper : τ ≤ U) :
    ∃ k : ℕ, 0 < k ∧
      k ≤ ⌈3 * (U + 4 * d) / (2 * τ₀)⌉₊ ∧
      2 * τ₀ / 3 ≤ (τ + 4 * d) / k ∧
      (τ + 4 * d) / k ≤ τ₀ ∧
      τ / k ≤ (τ + 4 * d) / k ∧
      τ₀ / 2 ≤ τ / k ∧
      (3 * (1 - σ) / τ₀) *
          ((τ + 4 * d) / k - τ / k) ≤
        (8 * d / τ₀) * (τ / k) := by
  obtain ⟨k, hk, hkB, hkLower, hkUpper, hkActual, hkGap⟩ :=
    exists_bounded_positive_power_scale_reduction_with_slack
      hcert.tau0_pos hd hNear hτUpper
  have hkPos : (0 : ℝ) < k := by exact_mod_cast hk
  have hTauDensity : 3 * (1 - σ) ≤ τ₀ := by
    nlinarith [hcert.density_base_le_tau0]
  have hdTau : 4 * d ≤ τ₀ / 750 := by
    nlinarith
  have hActualLower : τ₀ / 2 ≤ τ / k := by
    have hGapAt : (τ + 4 * d) / k - 4 * d ≤ τ / k := by linarith
    have hCore : τ₀ / 2 ≤ (τ + 4 * d) / k - 4 * d := by
      nlinarith [hkLower]
    exact hCore.trans hGapAt
  have hTargetLeOne : 3 * (1 - σ) / τ₀ ≤ 1 := by
    rw [div_le_one hcert.tau0_pos]
    exact hTauDensity
  have hGapNonneg : 0 ≤ (τ + 4 * d) / k - τ / k := by
    exact sub_nonneg.mpr hkActual
  refine ⟨k, hk, hkB, hkLower, hkUpper, hkActual, hActualLower, ?_⟩
  calc
    (3 * (1 - σ) / τ₀) * ((τ + 4 * d) / k - τ / k) ≤
        1 * (4 * d) := by gcongr
    _ ≤ (8 * d / τ₀) * (τ / k) := by
      have hτ₀Pos := hcert.tau0_pos
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hτ₀Pos).2
      have hActualNonneg : 0 ≤ τ / (k : ℝ) :=
        (by positivity : 0 ≤ τ₀ / 2).trans hActualLower
      nlinarith [mul_nonneg hd hActualNonneg]

/-- The single endpoint loss parameter controls every real-power loss that
arises after reflected finite powering.  The natural ceiling is kept
literal: its contribution is bounded from `Nat.ceil_lt_add_one`, while the
factor `1 / (sigma - 1/2)` is paid for by the dedicated half-line-gap term
in `classicalEndpointLossParameter`. -/
theorem reflected_total_power_budget_le
    {sigma tau0 eta d : ℝ}
    (hsigma : 1 / 2 < sigma) (htau0 : 0 < tau0) (heta : 0 < eta)
    (hd : 0 < d) (hdOne : d ≤ 1)
    (hdEta : d ≤ eta / 1000)
    (hdEtaTau : d ≤ eta * tau0 / 1000)
    (hdReflected : d ≤ eta * tau0 * (sigma - 1 / 2) / 1000000) :
    let g := (sigma - 1 / 2) / 2
    let U := 2 / g
    let B := ⌈3 * (U + 4 * d) / (2 * tau0)⌉₊
    24 * d * (B : ℝ) + 8 * d / tau0 + 6 * d ≤ eta / 4 := by
  dsimp only
  let gap : ℝ := sigma - 1 / 2
  have hgap : 0 < gap := by dsimp only [gap]; linarith
  let U : ℝ := 4 / gap
  have hU : 0 < U := by dsimp only [U]; positivity
  let x : ℝ := 3 * (U + 4 * d) / (2 * tau0)
  have hx : 0 ≤ x := by dsimp only [x]; positivity
  let B : ℕ := ⌈x⌉₊
  have hB : (B : ℝ) < x + 1 := by
    simpa only [B] using Nat.ceil_lt_add_one hx
  have hdOverTau : d / tau0 ≤ eta / 1000 := by
    rw [div_le_iff₀ htau0]
    nlinarith
  have hdUOverTau : d * U / tau0 ≤ 4 * eta / 1000000 := by
    have hscaled : d / (tau0 * gap) ≤ eta / 1000000 := by
      rw [div_le_iff₀ (mul_pos htau0 hgap)]
      have hrewrite : eta / 1000000 * (tau0 * gap) =
          eta * tau0 * gap / 1000000 := by ring
      rw [hrewrite]
      simpa only [gap] using hdReflected
    dsimp only [U]
    calc
      d * (4 / gap) / tau0 = 4 * (d / (tau0 * gap)) := by
        field_simp [htau0.ne', hgap.ne']
      _ ≤ 4 * (eta / 1000000) := by gcongr
      _ = 4 * eta / 1000000 := by ring
  have hdSqOverTau : d ^ 2 / tau0 ≤ eta / 1000 := by
    calc
      d ^ 2 / tau0 = d * (d / tau0) := by ring
      _ ≤ 1 * (eta / 1000) := by
        exact mul_le_mul hdOne hdOverTau (by positivity) (by positivity)
      _ = eta / 1000 := by ring
  have hdB : d * (B : ℝ) <
      (3 / 2 : ℝ) * (d * U / tau0) +
        6 * (d ^ 2 / tau0) + d := by
    have hmul := mul_lt_mul_of_pos_left hB hd
    dsimp only [x] at hmul
    have hrewrite : d * (3 * (U + 4 * d) / (2 * tau0) + 1) =
        (3 / 2 : ℝ) * (d * U / tau0) +
          6 * (d ^ 2 / tau0) + d := by
      field_simp [htau0.ne']
      ring
    rwa [hrewrite] at hmul
  have hdB' : d * (B : ℝ) ≤ 8 * eta / 1000 := by
    have hEtaNonneg : 0 ≤ eta := heta.le
    nlinarith [hdUOverTau, hdSqOverTau, hdEta]
  have hFinal :
      24 * d * (B : ℝ) + 8 * d / tau0 + 6 * d ≤ eta / 4 := by
    have hEight : 8 * d / tau0 ≤ 8 * (eta / 1000) := by
      calc
        8 * d / tau0 = 8 * (d / tau0) := by ring
        _ ≤ 8 * (eta / 1000) := by gcongr
    nlinarith [hdB', hEight, hdEta]
  have hUrewrite : 2 / ((sigma - 1 / 2) / 2) = U := by
    dsimp only [U, gap]
    field_simp [show sigma - 1 / 2 ≠ 0 by linarith]
    norm_num
  rw [hUrewrite]
  simpa only [B, x] using hFinal

/-- The dedicated half-line-gap budget controls both the enlarged natural
power ceiling and the endpoint-exponent displacement caused by
`reflectedEndpointScaleSlack`. -/
theorem reflected_total_power_budget_with_gap_le
    {sigma tau0 eta d : ℝ}
    (hsigma : 1 / 2 < sigma) (_hsigmaUpper : sigma < 1)
    (htau0 : 0 < tau0) (_heta : 0 < eta)
    (hd : 0 < d) (hdOne : d ≤ 1)
    (hdEta : d ≤ eta / 1000)
    (hdReflected : d ≤ eta * tau0 * (sigma - 1 / 2) / 1000000) :
    let s := reflectedEndpointScaleSlack sigma d
    let g := (sigma - 1 / 2) / 2
    let U := 2 / g
    let B := ⌈3 * (U + s) / (2 * tau0)⌉₊
    24 * d * (B : ℝ) + 2 * s / tau0 + 6 * d ≤ eta / 4 := by
  dsimp only
  let gap : ℝ := sigma - 1 / 2
  have hgap : 0 < gap := by dsimp only [gap]; linarith
  let s : ℝ := 100 * d / gap
  have hs : 0 < s := by dsimp only [s]; positivity
  let U : ℝ := 4 / gap
  have hU : 0 < U := by dsimp only [U]; positivity
  let x : ℝ := 3 * (U + s) / (2 * tau0)
  have hx : 0 ≤ x := by dsimp only [x]; positivity
  let B : ℕ := ⌈x⌉₊
  have hB : (B : ℝ) < x + 1 := by
    simpa only [B] using Nat.ceil_lt_add_one hx
  have hdGapTau : d / (tau0 * gap) ≤ eta / 1000000 := by
    rw [div_le_iff₀ (mul_pos htau0 hgap)]
    have hrewrite : eta / 1000000 * (tau0 * gap) =
        eta * tau0 * gap / 1000000 := by ring
    rw [hrewrite]
    simpa only [gap] using hdReflected
  have hsTau : s / tau0 ≤ eta / 10000 := by
    dsimp only [s]
    calc
      (100 * d / gap) / tau0 = 100 * (d / (tau0 * gap)) := by
        field_simp [htau0.ne', hgap.ne']
      _ ≤ 100 * (eta / 1000000) := by gcongr
      _ = eta / 10000 := by ring
  have hdUTau : d * U / tau0 ≤ 4 * eta / 1000000 := by
    dsimp only [U]
    calc
      d * (4 / gap) / tau0 = 4 * (d / (tau0 * gap)) := by
        field_simp [htau0.ne', hgap.ne']
      _ ≤ 4 * (eta / 1000000) := by gcongr
      _ = 4 * eta / 1000000 := by ring
  have hdSTau : d * s / tau0 ≤ eta / 10000 := by
    calc
      d * s / tau0 = d * (s / tau0) := by ring
      _ ≤ 1 * (eta / 10000) := by
        exact mul_le_mul hdOne hsTau (div_nonneg hs.le htau0.le) (by norm_num)
      _ = eta / 10000 := by ring
  have hdB : d * (B : ℝ) <
      (3 / 2 : ℝ) * (d * U / tau0) +
        (3 / 2 : ℝ) * (d * s / tau0) + d := by
    have hmul := mul_lt_mul_of_pos_left hB hd
    dsimp only [x] at hmul
    have hrewrite : d * (3 * (U + s) / (2 * tau0) + 1) =
        (3 / 2 : ℝ) * (d * U / tau0) +
          (3 / 2 : ℝ) * (d * s / tau0) + d := by
      field_simp [htau0.ne']
    rwa [hrewrite] at hmul
  have hdB' : d * (B : ℝ) ≤ eta / 100 := by
    nlinarith [hdUTau, hdSTau, hdEta]
  have hFinal :
      24 * d * (B : ℝ) + 2 * s / tau0 + 6 * d ≤ eta / 4 := by
    have hTwo : 2 * s / tau0 ≤ 2 * (eta / 10000) := by
      calc
        2 * s / tau0 = 2 * (s / tau0) := by ring
        _ ≤ 2 * (eta / 10000) := by gcongr
    nlinarith [hdB', hTwo, hdEta]
  have hSrewrite : reflectedEndpointScaleSlack sigma d = s := by
    rfl
  have hUrewrite : 2 / ((sigma - 1 / 2) / 2) = U := by
    dsimp only [U, gap]
    field_simp [show sigma - 1 / 2 ≠ 0 by linarith]
    norm_num
  rw [hSrewrite, hUrewrite]
  simpa only [B, x] using hFinal

/-- A dyadic block selected from the expanded reflected prefix retains a
literal lower bound for its logarithmic height scale.  Floors are kept in
the hypothesis through the natural upper bound on `M`; no equality with the
ideal dual length is asserted. -/
theorem reflected_dyadic_scale_lower_of_expanded_cutoff
    {T τ d : ℝ} {Q P M : ℕ}
    (hT : 1 < T) (hQ : 1 < Q) (hP : 1 < P)
    (hτ : 1 < τ) (hτTwo : τ < 2)
    (hd : 0 ≤ d) (hScale : (Q : ℝ) ^ τ = T)
    (hPM : P ≤ M) (hM : (M : ℝ) ≤ T ^ (1 + d) / Q) :
    1 / (1 / 2 + d) ≤ typeILogarithmicScale T P := by
  have hTPos : 0 < T := by linarith
  have hTOne : 1 ≤ T := hT.le
  have hQReal : (1 : ℝ) < Q := by exact_mod_cast hQ
  have hSqrtQ : T ^ (1 / 2 : ℝ) ≤ (Q : ℝ) := by
    rw [← hScale, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ Q)]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      hQReal.le (by nlinarith : τ * (1 / 2 : ℝ) ≤ 1)
  have hSplit : T ^ (1 + d) = T ^ (1 / 2 + d) * T ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hTPos]
    congr 1
    ring
  have hMUpper : (M : ℝ) ≤ T ^ (1 / 2 + d) := by
    calc
      (M : ℝ) ≤ T ^ (1 + d) / Q := hM
      _ ≤ T ^ (1 + d) / T ^ (1 / 2 : ℝ) := by
        exact div_le_div_of_nonneg_left (Real.rpow_nonneg hTPos.le _)
          (Real.rpow_pos_of_pos hTPos _)
          hSqrtQ
      _ = T ^ (1 / 2 + d) := by
        rw [hSplit]
        field_simp [(Real.rpow_pos_of_pos hTPos (1 / 2 : ℝ)).ne']
  have hPUpper : (P : ℝ) ≤ T ^ (1 / 2 + d) := by
    exact (by exact_mod_cast hPM : (P : ℝ) ≤ M) |>.trans hMUpper
  have ha : 0 < 1 / 2 + d := by linarith
  have hInv : 0 ≤ 1 / (1 / 2 + d) := by positivity
  have hRaised := Real.rpow_le_rpow (Nat.cast_nonneg P) hPUpper hInv
  have hCancel : (T ^ (1 / 2 + d)) ^ (1 / (1 / 2 + d)) = T := by
    rw [← Real.rpow_mul hTPos.le]
    field_simp [ha.ne']
    exact Real.rpow_one T
  apply (Real.le_logb_iff_rpow_le (by exact_mod_cast hP) hTPos).mpr
  exact hRaised.trans_eq hCancel

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

/-- Exhaustive version with a strict Weyl margin.  The `4d` strip directly
below the powered boundary is deliberately retained for a slackened powered
MHH argument.  Outside that strip, the actual dyadic scale lies at least
`4d` below the Weyl threshold. -/
theorem reflected_actual_scale_powered_slack_or_weyl_margin
    {σ τ₀ τ d : ℝ}
    (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀)
    (hd : 0 < d)
    (hτLower : 1 / (1 / 2 + d) ≤ τ) :
    4 * τ₀ / 3 - 4 * d ≤ τ ∨
      τ < 6 * σ - 3 - 4 * d := by
  by_cases hNear : 4 * τ₀ / 3 - 4 * d ≤ τ
  · exact Or.inl hNear
  right
  have hBelow : τ + 4 * d < 4 * τ₀ / 3 := by linarith
  have hReciprocal : 2 - 4 * d < 1 / (1 / 2 + d) := by
    rw [lt_div_iff₀ (by linarith : 0 < 1 / 2 + d)]
    nlinarith [sq_pos_of_pos hd]
  have hNearTwo : 2 - 4 * d < τ := hReciprocal.trans_le hτLower
  have hWindow : 2 < 4 * τ₀ / 3 := by linarith
  have hWeyl := endpoint_zeta_window_upper_lt_weyl hσUpper hcert hWindow
  linarith

/-- Exhaustive reflected split with the gap-scaled transition width.  The
strict complementary alternative now retains a margin large enough to pay
all floored-cutoff and finite-power losses uniformly as `σ ↓ 5/6`. -/
theorem reflected_actual_scale_powered_gap_or_weyl_margin
    {σ τ₀ τ d : ℝ}
    (hσ : 1 / 2 < σ) (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀)
    (hd : 0 < d)
    (hτLower : 1 / (1 / 2 + d) ≤ τ) :
    let s := reflectedEndpointScaleSlack σ d
    4 * τ₀ / 3 - s ≤ τ ∨ τ < 6 * σ - 3 - s := by
  dsimp only
  let s := reflectedEndpointScaleSlack σ d
  have hs : 0 < s := reflectedEndpointScaleSlack_pos hσ hd
  have hFour : 4 * d ≤ s :=
    four_mul_le_reflectedEndpointScaleSlack hσ hσUpper hd.le
  by_cases hNear : 4 * τ₀ / 3 - s ≤ τ
  · exact Or.inl hNear
  right
  have hBelow : τ + s < 4 * τ₀ / 3 := by linarith
  have hReciprocal : 2 - 4 * d < 1 / (1 / 2 + d) := by
    rw [lt_div_iff₀ (by linarith : 0 < 1 / 2 + d)]
    nlinarith [sq_pos_of_pos hd]
  have hNearTwo : 2 - 4 * d < τ := hReciprocal.trans_le hτLower
  have hWindow : 2 < 4 * τ₀ / 3 := by linarith
  have hWeyl := endpoint_zeta_window_upper_lt_weyl hσUpper hcert hWindow
  linarith

/-- The numerical heart of the complementary reflected branch.  The first
inequality is the exact dual-length relation `P < M ≤ T^(1+d-1/τ)` written
in logarithmic coordinates.  Together with the gap-scaled transition it
leaves a fixed `s/24` between the reflected Weyl exponent and the literal
stationary threshold exponent. -/
theorem reflected_weyl_exponent_margin
    {σ τ θ d u s : ℝ}
    (hσ : 1 / 2 < σ) (hσUpper : σ < 1)
    (hd : 0 < d) (huD : u ≤ d)
    (hs : s = reflectedEndpointScaleSlack σ d)
    (hτOne : 1 < τ) (hτTwo : τ < 2)
    (hDual : 1 / θ ≤ 1 + d - 1 / τ)
    (hθLower : 1 / (1 / 2 + d) ≤ θ)
    (hFar : θ < 6 * σ - 3 - s) :
    1 / (2 * θ) + 1 / 6 + 2 * d + s / 24 ≤
      1 / 2 - u - d * σ + (σ - 1) / τ - d := by
  have hgap : 0 < σ - 1 / 2 := by linarith
  have hgapUpper : σ - 1 / 2 < 1 / 2 := by linarith
  have hτPos : 0 < τ := zero_lt_one.trans hτOne
  have hθPos : 0 < θ := by
    have hden : 0 < 1 / 2 + d := by linarith
    exact (div_pos (by norm_num) hden).trans_le hθLower
  have hReciprocal : 2 - 4 * d < 1 / (1 / 2 + d) := by
    rw [lt_div_iff₀ (by linarith : 0 < 1 / 2 + d)]
    nlinarith [sq_pos_of_pos hd]
  have hSigmaMargin : s - 4 * d < 6 * σ - 5 := by
    linarith
  have hScaleSlack : 200 * d ≤ s := by
    subst s
    unfold reflectedEndpointScaleSlack
    rw [le_div_iff₀ hgap]
    nlinarith [mul_pos hd hgap]
  have hTauGap : (σ - 1 / 2) / 2 < (σ - 1 / 2) / τ := by
    exact div_lt_div_of_pos_left hgap hτPos hτTwo
  have hInvTheta : 1 / (2 * θ) ≤ (1 + d - 1 / τ) / 2 := by
    have := div_le_div_of_nonneg_right hDual (by norm_num : (0 : ℝ) ≤ 2)
    calc
      1 / (2 * θ) = (1 / θ) / 2 := by field_simp [hθPos.ne']
      _ ≤ (1 + d - 1 / τ) / 2 := this
  have hdSigma : d * σ < d := by
    simpa only [mul_one] using mul_lt_mul_of_pos_left hσUpper hd
  have hSourceGap : 1 / 6 + s / 12 - d / 3 < (σ - 1 / 2) / 2 := by
    linarith
  have hActualGap : 1 / 6 + s / 12 - d / 3 < (σ - 1 / 2) / τ :=
    hSourceGap.trans hTauGap
  have hLoss :
      u + d * σ + 7 * d / 2 + s / 24 ≤ s / 12 - d / 3 := by
    linarith
  have hDivIdentity :
      (σ - 1) / τ + 1 / (2 * τ) = (σ - 1 / 2) / τ := by
    field_simp [hτPos.ne']
    ring
  calc
    1 / (2 * θ) + 1 / 6 + 2 * d + s / 24 ≤
        (1 + d - 1 / τ) / 2 + 1 / 6 + 2 * d + s / 24 := by
      linarith
    _ ≤ 1 / 2 - u - d * σ + (σ - 1) / τ - d := by
      rw [show (1 + d - 1 / τ) / 2 =
        1 / 2 + d / 2 - 1 / (2 * τ) by ring]
      linarith

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

/-- At integer arguments the complete source weight is between zero and one.
This includes both sharp tail boundaries and is therefore valid for every
source scale, not only the interior Poisson scales. -/
theorem typeISourceSmoothWeight_nat_mem_unitInterval
    (Y A r n : ℕ) :
    0 ≤ typeISourceSmoothWeight Y A r n ∧
      typeISourceSmoothWeight Y A r n ≤ 1 := by
  rw [typeISourceSmoothWeight, typeITailBoundary_natCast]
  split_ifs
  · have hCutNonneg := typeIDyadicCutoff_nonneg
        ((n : ℝ) / (2 ^ r * Y : ℕ))
    have hCutUpper := typeIDyadicCutoff_le_one
        ((n : ℝ) / (2 ^ r * Y : ℕ))
    simpa only [one_mul] using ⟨hCutNonneg, hCutUpper⟩
  · simp

/-- A source coefficient can be nonzero only inside the fixed annulus
`(Q/2,2Q)`, where `Q = 2^r Y`.  The strict inequalities record the zeroes of
the cutoff at both endpoints. -/
theorem typeISourceSmoothWeight_support
    {Y A r n : ℕ}
    (hn : typeISourceSmoothWeight Y A r n ≠ 0) :
    (((2 ^ r * Y : ℕ) : ℝ) / 2) < n ∧
      (n : ℝ) < 2 * (2 ^ r * Y : ℕ) := by
  let Q : ℕ := 2 ^ r * Y
  have hCut : typeIDyadicCutoff ((n : ℝ) / Q) ≠ 0 := by
    intro h
    apply hn
    unfold typeISourceSmoothWeight
    rw [h, mul_zero]
  have hQ : 0 < Q := by
    by_contra hnot
    have hQZero : Q = 0 := Nat.eq_zero_of_not_pos hnot
    apply hCut
    apply typeIDyadicCutoff_eq_zero_of_le_half
    simp [hQZero]
  constructor
  · by_contra hnot
    have hnUpper : (n : ℝ) ≤ (Q : ℝ) / 2 := by
      simpa only [Q] using le_of_not_gt hnot
    have hRatio : (n : ℝ) / Q ≤ 1 / 2 := by
      rw [div_le_iff₀ (by exact_mod_cast hQ)]
      nlinarith
    exact hCut (typeIDyadicCutoff_eq_zero_of_le_half hRatio)
  · by_contra hnot
    have hnLower : 2 * (Q : ℝ) ≤ n := by
      simpa only [Q] using le_of_not_gt hnot
    have hRatio : 2 ≤ (n : ℝ) / Q := by
      rw [le_div_iff₀ (by exact_mod_cast hQ)]
      exact hnLower
    exact hCut (typeIDyadicCutoff_eq_zero_of_two_le hRatio)

/-- Source normalization at the lower edge of its fixed annulus.  This is the
finite analogue of multiplying a smooth zeta block by `Q^σ`; the harmless
factor two makes the coefficient bound literal even at the left edge. -/
noncomputable def normalizedTypeISourceDirichletCoeff
    (Y A r : ℕ) (σ : ℝ) (n : ℕ) : ℂ :=
  ((((((2 ^ r * Y : ℕ) : ℝ) / 2) ^ σ : ℝ) : ℂ)) *
    typeISourceDirichletCoeff Y A r σ n

/-- The normalized coefficients of the actual source-smooth block are bounded
by one on the entire natural line. -/
theorem norm_normalizedTypeISourceDirichletCoeff_le_one
    (Y A r : ℕ) (σ : ℝ) (hσ : 0 ≤ σ) :
    ∀ n : ℕ, ‖normalizedTypeISourceDirichletCoeff Y A r σ n‖ ≤ 1 := by
  intro n
  by_cases hw : typeISourceSmoothWeight Y A r n = 0
  · simp [normalizedTypeISourceDirichletCoeff, typeISourceDirichletCoeff, hw]
  · have hn := typeISourceSmoothWeight_support hw
    have hnPos : 0 < n := by exact_mod_cast (lt_of_le_of_lt
      (by positivity : (0 : ℝ) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2)) hn.1)
    have hWeight := typeISourceSmoothWeight_nat_mem_unitInterval Y A r n
    rw [normalizedTypeISourceDirichletCoeff, typeISourceDirichletCoeff,
      norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by positivity) _),
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hWeight.1,
      Complex.norm_natCast_cpow_of_pos hnPos]
    simp only [Complex.neg_re, Complex.ofReal_re]
    rw [Real.rpow_neg (by exact_mod_cast hnPos.le), ← div_eq_mul_inv]
    have hBaseNonneg : 0 ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2) := by positivity
    have hnNonneg : (0 : ℝ) ≤ n := by exact_mod_cast hnPos.le
    have hRearrange :
        ((((2 ^ r * Y : ℕ) : ℝ) / 2) ^ σ) *
            (typeISourceSmoothWeight Y A r n / (n : ℝ) ^ σ) =
          typeISourceSmoothWeight Y A r n *
            (((((2 ^ r * Y : ℕ) : ℝ) / 2) ^ σ) / (n : ℝ) ^ σ) := by
      ring
    rw [hRearrange]
    rw [← Real.div_rpow hBaseNonneg hnNonneg]
    have hRatio : (((2 ^ r * Y : ℕ) : ℝ) / 2) / n ≤ 1 := by
      rw [div_le_one (by exact_mod_cast hnPos)]
      exact hn.1.le
    calc
      typeISourceSmoothWeight Y A r n *
          ((((2 ^ r * Y : ℕ) : ℝ) / 2) / n) ^ σ ≤
        1 * 1 := by
          exact mul_le_mul hWeight.2
            (Real.rpow_le_one (by positivity) hRatio hσ)
            (Real.rpow_nonneg (by positivity) _) zero_le_one
      _ = 1 := by ring

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

/-- Normalizing the source coefficients scales the complete source block by
the same positive real scalar. -/
theorem wideDirichletPoly_normalizedTypeISourceDirichletCoeff
    (Y A r : ℕ) (σ t : ℝ) (hY : 1 ≤ Y) :
    wideDirichletPoly 1 (Nat.clog 2 (A + 1))
        (normalizedTypeISourceDirichletCoeff Y A r σ) t =
      (((((2 ^ r * Y : ℕ) : ℝ) / 2) ^ σ : ℝ) : ℂ) *
        typeISourceSmoothBlock Y A r σ t := by
  rw [typeISourceSmoothBlock_eq_wideDirichletPoly Y A r σ t hY]
  unfold wideDirichletPoly normalizedTypeISourceDirichletCoeff
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  ring

/-- A large actual source-smooth block yields one common nonzero dyadic
block with unit-bounded coefficients.  The selected dyadic length remains
within a factor four of the physical source scale; these inequalities are
proved from the literal support of the source coefficient rather than
postulated as a scale certificate. -/
theorem extract_normalized_source_dyadic_block
    {Y A r : ℕ} {σ V : ℝ} (W : Finset ℝ)
    (hY : 0 < Y) (hA : 1 < A) (hV : 0 < V)
    (hW : W.Nonempty) (hSeparated : IsSeparated 1 W)
    (hLarge : ∀ t ∈ W, V ≤ ‖typeISourceSmoothBlock Y A r σ t‖) :
    let k := Nat.clog 2 (A + 1)
    ∃ j ∈ Finset.range k, ∃ W' : Finset ℝ,
      W' ⊆ W ∧ IsSeparated 1 W' ∧
      (W.card : ℝ) ≤ k * (W'.card : ℝ) ∧
      (∀ t ∈ W',
        (((((2 ^ r * Y : ℕ) : ℝ) / 2) ^ σ) * V) / k ≤
          ‖dirichletPoly (2 ^ j)
            (normalizedTypeISourceDirichletCoeff Y A r σ) t‖) ∧
      2 ^ j < 2 * (2 ^ r * Y) ∧
      2 ^ r * Y < 4 * 2 ^ j := by
  dsimp only
  let k := Nat.clog 2 (A + 1)
  have hk : 0 < k := by
    dsimp only [k]
    apply Nat.clog_pos Nat.one_lt_two
    omega
  have hQ : 0 < 2 ^ r * Y := by positivity
  have hScalePos : 0 < ((((2 ^ r * Y : ℕ) : ℝ) / 2) ^ σ) := by
    apply Real.rpow_pos_of_pos
    positivity
  have hWide : ∀ t ∈ W,
      ((((2 ^ r * Y : ℕ) : ℝ) / 2) ^ σ) * V ≤
        ‖wideDirichletPoly 1 k
          (normalizedTypeISourceDirichletCoeff Y A r σ) t‖ := by
    intro t ht
    rw [wideDirichletPoly_normalizedTypeISourceDirichletCoeff
      Y A r σ t hY]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hScalePos]
    exact mul_le_mul_of_nonneg_left (hLarge t ht) hScalePos.le
  obtain ⟨j, hj, W', hWsub, hCard, hLarge'⟩ :=
    exists_dyadic_block_and_subset 1 k
      (normalizedTypeISourceDirichletCoeff Y A r σ) W
      (((((2 ^ r * Y : ℕ) : ℝ) / 2) ^ σ) * V) hk hWide
  simp only [mul_one] at hLarge'
  have hSep' : IsSeparated 1 W' := by
    intro x hx y hy hxy
    exact hSeparated x (hWsub hx) y (hWsub hy) hxy
  have hW' : W'.Nonempty := by
    by_contra hnot
    have hCardZero : W'.card = 0 := Finset.card_eq_zero.mpr
      (Finset.not_nonempty_iff_eq_empty.mp hnot)
    rw [hCardZero, Nat.cast_zero, mul_zero] at hCard
    have hWCardPos : (0 : ℝ) < W.card := by exact_mod_cast hW.card_pos
    linarith
  obtain ⟨t, ht⟩ := hW'
  have hThresholdPos : 0 <
      (((((2 ^ r * Y : ℕ) : ℝ) / 2) ^ σ) * V) / k := by
    positivity
  have hPolyNe : dirichletPoly (2 ^ j)
      (normalizedTypeISourceDirichletCoeff Y A r σ) t ≠ 0 := by
    intro hzero
    have hAt := hLarge' t ht
    rw [hzero, norm_zero] at hAt
    linarith
  unfold dirichletPoly at hPolyNe
  obtain ⟨n, hn, hnTerm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hPolyNe
  have hnCoeff : normalizedTypeISourceDirichletCoeff Y A r σ n ≠ 0 := by
    intro hzero
    apply hnTerm
    simp [hzero]
  have hnWeight : typeISourceSmoothWeight Y A r n ≠ 0 := by
    intro hzero
    apply hnCoeff
    simp [normalizedTypeISourceDirichletCoeff,
      typeISourceDirichletCoeff, hzero]
  have hnSource := typeISourceSmoothWeight_support hnWeight
  have hnDyadic := Finset.mem_Ioc.mp hn
  have hLeftReal : ((2 ^ j : ℕ) : ℝ) <
      2 * (2 ^ r * Y : ℕ) := by
    have hPn : ((2 ^ j : ℕ) : ℝ) < n := by exact_mod_cast hnDyadic.1
    exact hPn.trans hnSource.2
  have hRightReal : ((2 ^ r * Y : ℕ) : ℝ) <
      4 * (2 ^ j : ℕ) := by
    have hnUpper : (n : ℝ) ≤ 2 * (2 ^ j : ℕ) := by exact_mod_cast hnDyadic.2
    nlinarith [hnSource.1]
  refine ⟨j, hj, W', hWsub, hSep', hCard, ?_, ?_, ?_⟩
  · simpa only [k] using hLarge'
  · exact_mod_cast hLeftReal
  · exact_mod_cast hRightReal

/-- Complete direct-MHH consumer for one actual source-smooth family.  It
performs the common dyadic selection internally, preserves the source-family
cardinality, and exposes the physical/dyadic scale comparison used by the
later endpoint routing. -/
theorem source_smooth_family_direct_mhh_cardinality :
    ∃ K : ℝ, 0 < K ∧
      ∀ {Y A r : ℕ} {σ T V : ℝ} (W : Finset ℝ),
        0 < Y → 1 < A → 0 ≤ σ → 1 ≤ T → 0 < V →
        W.Nonempty → IsSeparated 1 W → InBaseInterval (3 * T) W →
        (∀ t ∈ W, V ≤ ‖typeISourceSmoothBlock Y A r σ t‖) →
        ∃ j ∈ Finset.range (Nat.clog 2 (A + 1)),
          ∃ W' : Finset ℝ,
            W' ⊆ W ∧ IsSeparated 1 W' ∧ InBaseInterval (3 * T) W' ∧
            (W.card : ℝ) ≤
              (Nat.clog 2 (A + 1) : ℝ) * (W'.card : ℝ) ∧
            let P := 2 ^ j
            let L := (((((2 ^ r * Y : ℕ) : ℝ) / 2) ^ σ) * V) /
              Nat.clog 2 (A + 1)
            (∀ t ∈ W', L ≤
              ‖dirichletPoly P
                (normalizedTypeISourceDirichletCoeff Y A r σ) t‖) ∧
            (W'.card : ℝ) ≤
              K * (1 + (((harmonic P : ℚ) : ℝ))) *
                ((P : ℝ) ^ 2 / L ^ 2 +
                  (3 * T) * min ((P : ℝ) / L ^ 2)
                    ((P : ℝ) ^ 4 / L ^ 6)) ∧
            P < 2 * (2 ^ r * Y) ∧ 2 ^ r * Y < 4 * P := by
  obtain ⟨K, hK, hMHH⟩ := classical_large_values_with_harmonic_unrestricted
  refine ⟨K, hK, ?_⟩
  intro Y A r σ T V W hY hA hσ hT hV hW hSeparated hBase hLarge
  obtain ⟨j, hj, W', hWsub, hSep', hCard, hLarge', hPUpper, hPLower⟩ :=
    extract_normalized_source_dyadic_block W hY hA hV hW hSeparated hLarge
  let P : ℕ := 2 ^ j
  let L : ℝ := (((((2 ^ r * Y : ℕ) : ℝ) / 2) ^ σ) * V) /
    Nat.clog 2 (A + 1)
  have hP : 0 < P := by dsimp only [P]; positivity
  have hL : 0 < L := by
    dsimp only [L]
    have hk : 0 < Nat.clog 2 (A + 1) :=
      Nat.clog_pos Nat.one_lt_two (by omega)
    positivity
  have hCoeff : ∀ n ∈ Finset.Ioc P (2 * P),
      ‖normalizedTypeISourceDirichletCoeff Y A r σ n‖ ≤ 1 := by
    intro n _hn
    exact norm_normalizedTypeISourceDirichletCoeff_le_one Y A r σ hσ n
  have hBase' : InBaseInterval (3 * T) W' := by
    intro t ht
    exact hBase t (hWsub ht)
  have hMHHAt := hMHH P (3 * T) L W'
    (normalizedTypeISourceDirichletCoeff Y A r σ)
    hP (by linarith) hL hCoeff hSep' hBase'
    (by simpa only [P, L] using hLarge')
  refine ⟨j, hj, W', hWsub, hSep', hBase', hCard, ?_⟩
  dsimp only
  refine ⟨by simpa only [P, L] using hLarge', ?_, hPUpper, hPLower⟩
  simpa only [P, L] using hMHHAt

/-- Powered-MHH consumer for an actual source-smooth family.  Both finite
pigeonhole losses are explicit: first the source block is localized to one
dyadic interval, then its exact natural power is localized again. -/
theorem source_smooth_family_powered_mhh_cardinality
    (B : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ K : ℝ, 0 < K ∧
      ∀ {Y A r k : ℕ} {σ T V : ℝ} (W : Finset ℝ),
        0 < Y → 1 < A → 0 ≤ σ → 1 ≤ T → 0 < V →
        0 < k → k ≤ B → W.Nonempty →
        IsSeparated 1 W → InBaseInterval (3 * T) W →
        (∀ t ∈ W, V ≤ ‖typeISourceSmoothBlock Y A r σ t‖) →
        ∃ j ∈ Finset.range (Nat.clog 2 (A + 1)),
          ∃ s ∈ Finset.range k, ∃ W' : Finset ℝ,
            let P := 2 ^ j
            let Q := 2 ^ s * P ^ k
            let L := (((((2 ^ r * Y : ℕ) : ℝ) / 2) ^ σ) * V) /
              Nat.clog 2 (A + 1)
            let Vp := (L ^ k /
              (C * ((2 ^ k * P ^ k : ℕ) : ℝ) ^ eta)) / k
            W' ⊆ W ∧ IsSeparated 1 W' ∧ InBaseInterval (3 * T) W' ∧
            (W.card : ℝ) ≤
              (Nat.clog 2 (A + 1) : ℝ) * k * (W'.card : ℝ) ∧
            (∀ t ∈ W', Vp ≤
              ‖dirichletPoly Q
                (normalizedFinitePoweredCoeffs P k
                  (normalizedTypeISourceDirichletCoeff Y A r σ)
                  0 C eta) t‖) ∧
            (W'.card : ℝ) ≤
              K * (1 + (((harmonic Q : ℚ) : ℝ))) *
                ((Q : ℝ) ^ 2 / Vp ^ 2 +
                  (3 * T) * min ((Q : ℝ) / Vp ^ 2)
                    ((Q : ℝ) ^ 4 / Vp ^ 6)) ∧
            P < 2 * (2 ^ r * Y) ∧ 2 ^ r * Y < 4 * P := by
  obtain ⟨C, hC, K, hK, hPowered⟩ :=
    powered_unit_block_large_values_bound_bounded_uniform B eta heta
  refine ⟨C, hC, K, hK, ?_⟩
  intro Y A r k σ T V W hY hA hσ hT hV hk hkB hW hSeparated hBase hLarge
  obtain ⟨j, hj, W₀, hW₀sub, hSep₀, hCard₀, hLarge₀, hPUpper, hPLower⟩ :=
    extract_normalized_source_dyadic_block W hY hA hV hW hSeparated hLarge
  let P : ℕ := 2 ^ j
  let L : ℝ := (((((2 ^ r * Y : ℕ) : ℝ) / 2) ^ σ) * V) /
    Nat.clog 2 (A + 1)
  have hP : 0 < P := by dsimp only [P]; positivity
  have hL : 0 < L := by
    dsimp only [L]
    have hcover : 0 < Nat.clog 2 (A + 1) :=
      Nat.clog_pos Nat.one_lt_two (by omega)
    positivity
  have hCoeff : ∀ n ∈ Finset.Ioc P (2 * P),
      ‖normalizedTypeISourceDirichletCoeff Y A r σ n‖ ≤ 1 := by
    intro n _hn
    exact norm_normalizedTypeISourceDirichletCoeff_le_one Y A r σ hσ n
  have hBase₀ : InBaseInterval (3 * T) W₀ := by
    intro t ht
    exact hBase t (hW₀sub ht)
  obtain ⟨s, hs, W', hW'sub, hPowerCard, hSep', hBase', hLarge', hMHH'⟩ :=
    hPowered k P (normalizedTypeISourceDirichletCoeff Y A r σ)
      0 (3 * T) L W₀ hk hkB hP (by norm_num) (by linarith) hL
      hCoeff hSep₀ hBase₀ (by
        intro t ht
        have hPhase :
            (∑ n ∈ Finset.Ioc P (2 * P),
              normalizedTypeISourceDirichletCoeff Y A r σ n *
                (n : ℂ) ^ (-(((0 : ℝ) : ℂ) + I * (t : ℂ)))) =
              dirichletPoly P
                (normalizedTypeISourceDirichletCoeff Y A r σ) t := by
          unfold dirichletPoly
          apply Finset.sum_congr rfl
          intro n _hn
          congr 2
          norm_num
          ring
        rw [hPhase]
        simpa only [P, L] using hLarge₀ t ht)
  refine ⟨j, hj, s, hs, W', ?_⟩
  dsimp only
  refine ⟨hW'sub.trans hW₀sub, hSep', hBase', ?_, ?_, ?_,
    hPUpper, hPLower⟩
  calc
    (W.card : ℝ) ≤ (Nat.clog 2 (A + 1) : ℝ) * (W₀.card : ℝ) := hCard₀
    _ ≤ (Nat.clog 2 (A + 1) : ℝ) * (k * (W'.card : ℝ)) := by
      gcongr
    _ = (Nat.clog 2 (A + 1) : ℝ) * k * (W'.card : ℝ) := by ring
  · simpa only [P, L, Real.rpow_zero, one_mul] using hLarge'
  · simpa only [P, L, Real.rpow_zero, one_mul] using hMHH'

/-- A dyadic interval extracted within a fixed factor of a physical source
scale inherits a uniform logarithmic-scale upper bound.  The factor four is
absorbed by the elementary inequality `4P ≤ P²` once the source scale is at
least sixteen. -/
theorem extracted_source_logarithmic_scale_upper
    {T U : ℝ} {Q P : ℕ}
    (hT : 1 ≤ T) (hU : 0 < U) (hQ : 16 ≤ Q)
    (hQP : Q < 4 * P)
    (hScale : typeILogarithmicScale T Q ≤ U) :
    1 < P ∧ typeILogarithmicScale T P ≤ 2 * U := by
  have hPFour : 4 ≤ P := by omega
  have hPOne : 1 < P := by omega
  have hQOne : 1 < Q := by omega
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have hPhysicalQ : T ≤ (Q : ℝ) ^ U :=
    (Real.logb_le_iff_le_rpow (by exact_mod_cast hQOne) hTPos).mp hScale
  have hQP2Nat : Q ≤ P ^ 2 := by
    calc
      Q ≤ 4 * P := hQP.le
      _ ≤ P * P := Nat.mul_le_mul_right P hPFour
      _ = P ^ 2 := by ring
  have hRaised : (Q : ℝ) ^ U ≤ ((P ^ 2 : ℕ) : ℝ) ^ U :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hQP2Nat) hU.le
  have hPower : ((P ^ 2 : ℕ) : ℝ) ^ U = (P : ℝ) ^ (2 * U) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  refine ⟨hPOne, (Real.logb_le_iff_le_rpow
    (by exact_mod_cast hPOne) hTPos).mpr ?_⟩
  calc
    T ≤ (Q : ℝ) ^ U := hPhysicalQ
    _ ≤ ((P ^ 2 : ℕ) : ℝ) ^ U := hRaised
    _ = (P : ℝ) ^ (2 * U) := hPower

/-- The same extracted dyadic interval inherits half of every nonnegative
lower logarithmic-scale bound.  The exact factor-two upper comparison
`P < 2Q` is absorbed by `2Q ≤ Q²`; no asymptotic replacement of either
finite length is used. -/
theorem extracted_source_logarithmic_scale_lower
    {T L : ℝ} {Q P : ℕ}
    (hT : 0 < T) (hL : 0 ≤ L) (hQ : 4 ≤ Q)
    (hQP : Q < 4 * P) (hPQ : P < 2 * Q)
    (hScale : L ≤ typeILogarithmicScale T Q) :
    1 < P ∧ L / 2 ≤ typeILogarithmicScale T P := by
  have hPOne : 1 < P := by omega
  have hQOne : 1 < Q := by omega
  have hPhysicalQ : (Q : ℝ) ^ L ≤ T :=
    (Real.le_logb_iff_rpow_le (by exact_mod_cast hQOne) hT).mp hScale
  have hPQSquareNat : P ≤ Q ^ 2 := by
    calc
      P ≤ 2 * Q := hPQ.le
      _ ≤ Q * Q := Nat.mul_le_mul_right Q (by omega : 2 ≤ Q)
      _ = Q ^ 2 := by ring
  have hRaised : (P : ℝ) ^ (L / 2) ≤ ((Q ^ 2 : ℕ) : ℝ) ^ (L / 2) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hPQSquareNat)
      (by positivity)
  have hPower : ((Q ^ 2 : ℕ) : ℝ) ^ (L / 2) = (Q : ℝ) ^ L := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    ring
  refine ⟨hPOne, (Real.le_logb_iff_rpow_le
    (by exact_mod_cast hPOne) hT).mpr ?_⟩
  exact hRaised.trans_eq hPower |>.trans hPhysicalQ

/-- A dyadic interval within a factor two above its physical source scale
has logarithmic scale within any prescribed positive additive error once
the height is large enough.  This is the quantitative finite bridge needed
to choose the natural power from the extracted polynomial rather than from
an unrelated real surrogate. -/
theorem eventually_extracted_source_logarithmic_scale_lower_additive
    {δ U : ℝ} (hδ : 0 < δ) (hU : 0 < U) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧
      ∀ {T τ : ℝ} {Q P : ℕ}, T₀ ≤ T → 1 < Q → 1 < P →
        P < 2 * Q → τ = typeILogarithmicScale T Q →
        0 < τ → τ ≤ U →
        τ - δ ≤ typeILogarithmicScale T P := by
  let X : ℝ := U ^ 2 * Real.log 2 / δ
  let T₀ : ℝ := max 8 (Real.exp X)
  refine ⟨T₀, le_max_left _ _, ?_⟩
  intro T τ Q P hT hQ hP hPQ hτ hτPos hτUpper
  have hTEight : 8 ≤ T := (le_max_left _ _).trans hT
  have hTExp : Real.exp X ≤ T := (le_max_right _ _).trans hT
  have hTPos : 0 < T := by linarith
  have hTOne : 1 < T := by linarith
  have hLogT : 0 < Real.log T := Real.log_pos hTOne
  have hLogQ : 0 < Real.log (Q : ℝ) := Real.log_pos (by exact_mod_cast hQ)
  have hLogP : 0 < Real.log (P : ℝ) := Real.log_pos (by exact_mod_cast hP)
  have hLogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hXLog : X ≤ Real.log T := by
    have hLogMono := Real.log_le_log (Real.exp_pos X) hTExp
    simpa only [Real.log_exp] using hLogMono
  have hTauLog : τ * Real.log (Q : ℝ) = Real.log T := by
    rw [hτ]
    unfold typeILogarithmicScale Real.logb
    field_simp [hLogQ.ne']
  have hLogPUpper : Real.log (P : ℝ) ≤
      Real.log 2 + Real.log (Q : ℝ) := by
    have hCast : (P : ℝ) ≤ 2 * Q := by exact_mod_cast hPQ.le
    calc
      Real.log (P : ℝ) ≤ Real.log (2 * (Q : ℝ)) :=
        Real.log_le_log (by positivity) hCast
      _ = Real.log 2 + Real.log (Q : ℝ) := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity)]
  have hULog : U * Real.log 2 ≤ δ * Real.log (Q : ℝ) := by
    have hULogQ : Real.log T ≤ U * Real.log (Q : ℝ) := by
      rw [← hTauLog]
      exact mul_le_mul_of_nonneg_right hτUpper hLogQ.le
    have hCore : U ^ 2 * Real.log 2 / δ ≤
        U * Real.log (Q : ℝ) := by
      simpa only [X] using hXLog.trans hULogQ
    rw [div_le_iff₀ hδ] at hCore
    have hUPos : 0 < U := hU
    nlinarith [mul_pos hUPos hLogTwo]
  have hTauLogTwo : τ * Real.log 2 ≤ δ * Real.log (Q : ℝ) :=
    (mul_le_mul_of_nonneg_right hτUpper hLogTwo.le).trans hULog
  rw [hτ]
  unfold typeILogarithmicScale Real.logb
  rw [le_div_iff₀ hLogP]
  by_cases hNonneg : 0 ≤ Real.log T / Real.log (Q : ℝ) - δ
  · calc
      (Real.log T / Real.log (Q : ℝ) - δ) * Real.log (P : ℝ) ≤
          (Real.log T / Real.log (Q : ℝ) - δ) *
            (Real.log 2 + Real.log (Q : ℝ)) :=
        mul_le_mul_of_nonneg_left hLogPUpper hNonneg
      _ ≤ Real.log T := by
        rw [show Real.log T / Real.log (Q : ℝ) = τ by
          rw [hτ]; rfl]
        rw [← hTauLog]
        nlinarith
  · have hNeg : Real.log T / Real.log (Q : ℝ) - δ < 0 :=
      lt_of_not_ge hNonneg
    exact (mul_neg_of_neg_of_pos hNeg hLogP).le.trans hLogT.le

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

/-- A unit-coefficient dyadic polynomial cannot have norm larger than its
literal natural length.  This converts a retained reflected threshold into
a lower bound for the actual block selected by dyadic pigeonholing. -/
theorem unit_coeff_threshold_le_dyadic_length
    {N : ℕ} {V : ℝ} {W : Finset ℝ} {a : ℕ → ℂ}
    (hV : 0 ≤ V) (hW : W.Nonempty)
    (ha : ∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1)
    (hLarge : ∀ t ∈ W, V ≤ ‖dirichletPoly N a t‖) :
    V ≤ (N : ℝ) := by
  have hEnergy := dyadic_energy_le_length N a ha
  have hThreshold := threshold_sq_le_length_mul_energy N V W a hV hW hLarge
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  nlinarith [sq_nonneg (V - (N : ℝ))]

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
    obtain ⟨j, hj, U₀, hSep₀, hBase₀, _hRange₀, hCard₀, hLarge₀⟩ :=
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
    obtain ⟨j, hj, U₀, hSep₀, hBase₀, _hRange₀, hCard₀, hLarge₀⟩ :=
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

/-! ## Finite interval Abel bridges for the source boundary -/

/-- Abel summation for a nonnegative increasing weight.  Unlike the
antitone form used for `n^-sigma`, the endpoint and total variation each
cost one copy of the final weight. -/
theorem norm_weighted_sum_le_of_monotone
    (f : ℕ → ℝ) (g : ℕ → ℂ) (N : ℕ) (B : ℝ)
    (hN : 0 < N)
    (hf : ∀ i, i < N → 0 ≤ f i)
    (hmono : ∀ i, i + 1 < N → f i ≤ f (i + 1))
    (hpartial : ∀ j, j ≤ N → ‖∑ i ∈ Finset.range j, g i‖ ≤ B) :
    ‖∑ i ∈ Finset.range N, f i • g i‖ ≤ 2 * f (N - 1) * B := by
  have hB : 0 ≤ B := by
    simpa using hpartial 0 (Nat.zero_le N)
  have hparts := Finset.sum_Ico_by_parts f g hN
  rw [Finset.range_eq_Ico]
  calc
    ‖∑ i ∈ Finset.Ico 0 N, f i • g i‖ =
        ‖f (N - 1) • (∑ i ∈ Finset.range N, g i) -
          f 0 • (∑ i ∈ Finset.range 0, g i) -
          ∑ i ∈ Finset.Ico 0 (N - 1),
            (f (i + 1) - f i) •
              (∑ j ∈ Finset.range (i + 1), g j)‖ :=
      congrArg norm hparts
    _ = ‖(f (N - 1) : ℂ) * (∑ i ∈ Finset.range N, g i) -
        ∑ i ∈ Finset.Ico 0 (N - 1),
          ((f (i + 1) - f i : ℝ) : ℂ) *
            (∑ j ∈ Finset.range (i + 1), g j)‖ := by
      simp only [Finset.sum_range_zero, Complex.real_smul, mul_zero, sub_zero]
    _ ≤ ‖(f (N - 1) : ℂ) * (∑ i ∈ Finset.range N, g i)‖ +
        ‖∑ i ∈ Finset.Ico 0 (N - 1),
          ((f (i + 1) - f i : ℝ) : ℂ) *
            (∑ j ∈ Finset.range (i + 1), g j)‖ := norm_sub_le _ _
    _ ≤ f (N - 1) * B +
        ∑ i ∈ Finset.Ico 0 (N - 1), (f (i + 1) - f i) * B := by
      apply add_le_add
      · rw [norm_mul, norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hf (N - 1) (by omega))]
        exact mul_le_mul_of_nonneg_left (hpartial N le_rfl)
          (hf (N - 1) (by omega))
      · calc
          ‖∑ i ∈ Finset.Ico 0 (N - 1),
              ((f (i + 1) - f i : ℝ) : ℂ) *
                (∑ j ∈ Finset.range (i + 1), g j)‖ ≤
              ∑ i ∈ Finset.Ico 0 (N - 1),
                ‖((f (i + 1) - f i : ℝ) : ℂ) *
                  (∑ j ∈ Finset.range (i + 1), g j)‖ := norm_sum_le _ _
          _ ≤ ∑ i ∈ Finset.Ico 0 (N - 1),
              (f (i + 1) - f i) * B := by
            apply Finset.sum_le_sum
            intro i hi
            have hi' := Finset.mem_Ico.mp hi
            rw [norm_mul, norm_real, Real.norm_eq_abs,
              abs_of_nonneg (sub_nonneg.mpr (hmono i (by omega)))]
            exact mul_le_mul_of_nonneg_left (hpartial (i + 1) (by omega))
              (sub_nonneg.mpr (hmono i (by omega)))
    _ = (2 * f (N - 1) - f 0) * B := by
      have htel : ∑ i ∈ Finset.Ico 0 (N - 1),
          (f (i + 1) - f i) = f (N - 1) - f 0 := by
        rw [Nat.Ico_zero_eq_range, Finset.sum_range_sub]
      rw [← Finset.sum_mul, htel]
      ring
    _ ≤ 2 * f (N - 1) * B := by
      have hf0 : 0 ≤ f 0 := hf 0 hN
      nlinarith

/-- Exact range form of one dyadic block of the normalized reflected
polynomial.  The `min` records the literal truncation at the natural dual
cutoff `M`; no coefficient beyond that cutoff is retained. -/
theorem dirichletPoly_normalizedTypeIReflectedCoeff_eq_range
    (sigma t : ℝ) (P M : ℕ) (hP : 0 < P) (hPM : P < M) :
    dirichletPoly P (normalizedTypeIReflectedCoeff sigma M) t =
      ∑ i ∈ Finset.range (min P (M - P)),
        (((P + 1 + i : ℕ) : ℝ) ^ sigma / (M : ℝ) ^ sigma) •
          unitaryPhase (logarithmicPhase t (P + 1 + i)) := by
  have hInterval : Finset.Ioc P (2 * P) =
      Finset.Ico (P + 1) (2 * P + 1) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  unfold dirichletPoly dyadicInterval
  rw [hInterval, Finset.sum_Ico_eq_sum_range]
  have hLength : 2 * P + 1 - (P + 1) = P := by omega
  rw [hLength]
  push_cast
  symm
  calc
    ∑ i ∈ Finset.range (min P (M - P)),
        (((P : ℝ) + 1 + (i : ℝ)) ^ sigma / (M : ℝ) ^ sigma) •
          unitaryPhase (logarithmicPhase t (P + 1 + i)) =
      ∑ i ∈ Finset.range (min P (M - P)),
        normalizedTypeIReflectedCoeff sigma M (P + 1 + i) *
          ((P : ℂ) + 1 + (i : ℂ)) ^ (-t * I) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hiL : i < min P (M - P) := Finset.mem_range.mp hi
      have hiDiff : i < M - P := lt_of_lt_of_le hiL (min_le_right _ _)
      have hnPos : 0 < P + 1 + i := by omega
      have hnM : P + 1 + i ≤ M := by omega
      rw [normalizedTypeIReflectedCoeff, if_pos ⟨by omega, hnM⟩,
        Complex.real_smul]
      norm_num only [Nat.cast_add, Nat.cast_one]
      have hPhase :=
        unitaryPhase_logarithmicPhase_eq_cpow t (P + 1 + i) hnPos
      norm_num only [Nat.cast_add, Nat.cast_one] at hPhase
      rw [hPhase]
    _ = ∑ i ∈ Finset.range P,
        normalizedTypeIReflectedCoeff sigma M (P + 1 + i) *
          ((P : ℂ) + 1 + (i : ℂ)) ^ (-t * I) := by
      apply Finset.sum_subset
      · intro i hi
        exact Finset.mem_range.mpr
          ((Finset.mem_range.mp hi).trans_le (min_le_left _ _))
      · intro i hiP hiL
        have hiP' : i < P := Finset.mem_range.mp hiP
        have hiLower : min P (M - P) ≤ i := by
          exact le_of_not_gt (fun h => hiL (Finset.mem_range.mpr h))
        have hMin : min P (M - P) = M - P := by
          apply min_eq_right
          omega
        have hnM : M < P + 1 + i := by
          rw [hMin] at hiLower
          omega
        rw [normalizedTypeIReflectedCoeff,
          if_neg (fun h => (Nat.not_le_of_lt hnM) h.2), zero_mul]

/-- Weyl bound for the actual increasing normalized coefficient on a retained
reflected dyadic interval.  Abel summation is applied in the increasing form,
so the normalization by `M^sigma` is used rather than discarded. -/
theorem norm_dirichletPoly_normalizedTypeIReflectedCoeff_le_weyl
    (sigma t : ℝ) (P M : ℕ)
    (hsigma : 0 ≤ sigma) (hP : 0 < P) (hPM : P < M)
    (htOne : 1 ≤ t)
    (hPt : (((P + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ t)
    (htP : t ≤ (((P + 1 : ℕ) : ℝ) ^ (3 : ℕ))) :
    ‖dirichletPoly P (normalizedTypeIReflectedCoeff sigma M) t‖ ≤
      60 * Real.sqrt (((P + 1 : ℕ) : ℝ) * t ^ (1 / 3 : ℝ)) := by
  let Y : ℝ := t ^ (1 / 3 : ℝ)
  let L : ℕ := min P (M - P)
  let f : ℕ → ℝ := fun i =>
    ((P + 1 + i : ℕ) : ℝ) ^ sigma / (M : ℝ) ^ sigma
  let g : ℕ → ℂ := fun i =>
    unitaryPhase (logarithmicPhase t (P + 1 + i))
  have htPos : 0 < t := zero_lt_one.trans_le htOne
  have hYOne : 1 ≤ Y := Real.one_le_rpow htOne (by norm_num)
  have hYcube : Y ^ (3 : ℕ) = t := by
    dsimp only [Y]
    rw [← Real.rpow_natCast, ← Real.rpow_mul htPos.le]
    norm_num
  have hYUpper : Y ≤ ((P + 1 : ℕ) : ℝ) := by
    have hRoot := Real.rpow_le_rpow htPos.le htP
      (by norm_num : (0 : ℝ) ≤ 1 / 3)
    have hBasePos : (0 : ℝ) < (P + 1 : ℕ) := by positivity
    have hRight :
        ((((P + 1 : ℕ) : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ)) =
          ((P + 1 : ℕ) : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hBasePos.le]
      norm_num
    simpa only [Y, hRight] using hRoot
  have hLPos : 0 < L := by
    dsimp only [L]
    exact lt_min hP (Nat.sub_pos_of_lt hPM)
  have hLUpper : L ≤ P + 1 := by
    dsimp only [L]
    exact (min_le_left _ _).trans (Nat.le_succ _)
  have hPartial : ∀ j, j ≤ L →
      ‖∑ i ∈ Finset.range j, g i‖ ≤
        30 * Real.sqrt (((P + 1 : ℕ) : ℝ) * Y) := by
    intro j hj
    dsimp only [g]
    have hWeyl := logarithmic_weyl_exponent_pair_prefix Y (P + 1) j
      hYOne (by omega) hYUpper (by simpa only [hYcube] using hPt)
      (hj.trans hLUpper)
    rw [logarithmicSum_eq_sum_range] at hWeyl
    norm_num only [Nat.cast_add, Nat.cast_one] at hWeyl
    rw [hYcube] at hWeyl
    simpa only [Nat.cast_add, Nat.cast_one] using hWeyl
  have hFNonneg : ∀ i, i < L → 0 ≤ f i := by
    intro i _hi
    dsimp only [f]
    positivity
  have hFMono : ∀ i, i + 1 < L → f i ≤ f (i + 1) := by
    intro i _hi
    dsimp only [f]
    apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg M) _)
    apply Real.rpow_le_rpow
    · positivity
    · exact_mod_cast (show P + 1 + i ≤ P + 1 + (i + 1) by omega)
    · exact hsigma
  have hAbel := norm_weighted_sum_le_of_monotone f g L
    (30 * Real.sqrt (((P + 1 : ℕ) : ℝ) * Y))
    hLPos hFNonneg hFMono hPartial
  have hLastIndex : P + 1 + (L - 1) ≤ M := by
    have hLToDiff : L ≤ M - P := min_le_right _ _
    omega
  have hFLast : f (L - 1) ≤ 1 := by
    dsimp only [f]
    have hMPos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
    rw [div_le_one (Real.rpow_pos_of_pos hMPos _)]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hLastIndex) hsigma
  rw [dirichletPoly_normalizedTypeIReflectedCoeff_eq_range
    sigma t P M hP hPM]
  change ‖∑ i ∈ Finset.range L, f i • g i‖ ≤ _
  calc
    ‖∑ i ∈ Finset.range L, f i • g i‖ ≤
        2 * f (L - 1) *
          (30 * Real.sqrt (((P + 1 : ℕ) : ℝ) * Y)) := hAbel
    _ ≤ 2 * 1 * (30 * Real.sqrt (((P + 1 : ℕ) : ℝ) * Y)) := by
      gcongr
    _ = 60 * Real.sqrt (((P + 1 : ℕ) : ℝ) * t ^ (1 / 3 : ℝ)) := by
      dsimp only [Y]
      ring

/-- Boundary-slack version of the weighted reflected Weyl estimate.  The
factor `X` is retained explicitly through the A--B process, so the natural
dual cutoff may differ from its ideal real scale by a proved power loss. -/
theorem norm_dirichletPoly_normalizedTypeIReflectedCoeff_le_weyl_with_slack
    (sigma t X : ℝ) (P M : ℕ)
    (hsigma : 0 ≤ sigma) (hP : 0 < P) (hPM : P < M)
    (htOne : 1 ≤ t) (hX : 1 ≤ X)
    (hPt : (((P + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ X * t)
    (htP : t ≤ (((P + 1 : ℕ) : ℝ) ^ (3 : ℕ))) :
    ‖dirichletPoly P (normalizedTypeIReflectedCoeff sigma M) t‖ ≤
      60 * (((2 * (P + 1) : ℕ) : ℝ) ^ sigma / (M : ℝ) ^ sigma) *
        Real.sqrt (X * ((P + 1 : ℕ) : ℝ) * t ^ (1 / 3 : ℝ)) := by
  let Y : ℝ := t ^ (1 / 3 : ℝ)
  let L : ℕ := min P (M - P)
  let f : ℕ → ℝ := fun i =>
    ((P + 1 + i : ℕ) : ℝ) ^ sigma / (M : ℝ) ^ sigma
  let g : ℕ → ℂ := fun i =>
    unitaryPhase (logarithmicPhase t (P + 1 + i))
  have htPos : 0 < t := zero_lt_one.trans_le htOne
  have hYOne : 1 ≤ Y := Real.one_le_rpow htOne (by norm_num)
  have hYcube : Y ^ (3 : ℕ) = t := by
    dsimp only [Y]
    rw [← Real.rpow_natCast, ← Real.rpow_mul htPos.le]
    norm_num
  have hYUpper : Y ≤ ((P + 1 : ℕ) : ℝ) := by
    have hRoot := Real.rpow_le_rpow htPos.le htP
      (by norm_num : (0 : ℝ) ≤ 1 / 3)
    have hBasePos : (0 : ℝ) < (P + 1 : ℕ) := by positivity
    have hRight :
        ((((P + 1 : ℕ) : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ)) =
          ((P + 1 : ℕ) : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hBasePos.le]
      norm_num
    simpa only [Y, hRight] using hRoot
  have hLPos : 0 < L := by
    dsimp only [L]
    exact lt_min hP (Nat.sub_pos_of_lt hPM)
  have hLUpper : L ≤ P + 1 := by
    dsimp only [L]
    exact (min_le_left _ _).trans (Nat.le_succ _)
  have hPartial : ∀ j, j ≤ L →
      ‖∑ i ∈ Finset.range j, g i‖ ≤
        30 * Real.sqrt (X * ((P + 1 : ℕ) : ℝ) * Y) := by
    intro j hj
    dsimp only [g]
    have hWeyl := logarithmic_weyl_exponent_pair_prefix_with_slack
      Y X (P + 1) j hYOne hX (by omega) hYUpper
      (by simpa only [hYcube] using hPt) (hj.trans hLUpper)
    rw [logarithmicSum_eq_sum_range] at hWeyl
    norm_num only [Nat.cast_add, Nat.cast_one] at hWeyl
    rw [hYcube] at hWeyl
    simpa only [Nat.cast_add, Nat.cast_one] using hWeyl
  have hFNonneg : ∀ i, i < L → 0 ≤ f i := by
    intro i _hi
    dsimp only [f]
    positivity
  have hFMono : ∀ i, i + 1 < L → f i ≤ f (i + 1) := by
    intro i _hi
    dsimp only [f]
    apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg M) _)
    apply Real.rpow_le_rpow
    · positivity
    · exact_mod_cast (show P + 1 + i ≤ P + 1 + (i + 1) by omega)
    · exact hsigma
  have hAbel := norm_weighted_sum_le_of_monotone f g L
    (30 * Real.sqrt (X * ((P + 1 : ℕ) : ℝ) * Y))
    hLPos hFNonneg hFMono hPartial
  have hLastTwo : P + 1 + (L - 1) ≤ 2 * (P + 1) := by
    have hLP : L ≤ P := min_le_left _ _
    omega
  have hFLast : f (L - 1) ≤
      (((2 * (P + 1) : ℕ) : ℝ) ^ sigma / (M : ℝ) ^ sigma) := by
    dsimp only [f]
    apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg M) _)
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hLastTwo) hsigma
  rw [dirichletPoly_normalizedTypeIReflectedCoeff_eq_range
    sigma t P M hP hPM]
  change ‖∑ i ∈ Finset.range L, f i • g i‖ ≤ _
  calc
    ‖∑ i ∈ Finset.range L, f i • g i‖ ≤
        2 * f (L - 1) *
          (30 * Real.sqrt (X * ((P + 1 : ℕ) : ℝ) * Y)) := hAbel
    _ ≤ 2 * ((((2 * (P + 1) : ℕ) : ℝ) ^ sigma /
          (M : ℝ) ^ sigma)) *
          (30 * Real.sqrt (X * ((P + 1 : ℕ) : ℝ) * Y)) := by
      gcongr
    _ = 60 * (((2 * (P + 1) : ℕ) : ℝ) ^ sigma / (M : ℝ) ^ sigma) *
        Real.sqrt (X * ((P + 1 : ℕ) : ℝ) * t ^ (1 / 3 : ℝ)) := by
      dsimp only [Y]
      ring

/-- Physical-scale form of the reflected Weyl estimate.  The exact scale
identity eliminates the dyadic length, while the harmless factor `4^sigma`
accounts for the sharp endpoint and normalization. -/
theorem norm_normalizedTypeIReflectedCoeff_le_physical_weyl
    {sigma d T theta w : ℝ} {P M : ℕ}
    (hsigma : 0 ≤ sigma) (hd : 0 ≤ d) (hT : 1 ≤ T)
    (hP : 1 < P) (hPM : P < M)
    (htheta : 0 < theta) (hScale : (P : ℝ) ^ theta = T)
    (hwOne : 1 ≤ w) (hwUpper : w ≤ 3 * T)
    (hPt : (((P + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤
      (2 * T ^ (4 * d)) * w)
    (htP : w ≤ (((P + 1 : ℕ) : ℝ) ^ (3 : ℕ))) :
    ‖dirichletPoly P (normalizedTypeIReflectedCoeff sigma M) w‖ ≤
      (60 * 4 ^ sigma * Real.sqrt 12) *
        T ^ (2 * d + 1 / (2 * theta) + 1 / 6) := by
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have hPReal : (1 : ℝ) < P := by exact_mod_cast hP
  have hMPos : (0 : ℝ) < M := by
    exact_mod_cast (lt_trans Nat.zero_lt_one (lt_trans hP hPM))
  have hXOne : (1 : ℝ) ≤ 2 * T ^ (4 * d) := by
    have hPow : 1 ≤ T ^ (4 * d) := Real.one_le_rpow hT (by positivity)
    nlinarith
  have hRaw := norm_dirichletPoly_normalizedTypeIReflectedCoeff_le_weyl_with_slack
    sigma w (2 * T ^ (4 * d)) P M hsigma (by omega) hPM hwOne hXOne hPt htP
  have hRatio :
      (((2 * (P + 1) : ℕ) : ℝ) ^ sigma / (M : ℝ) ^ sigma) ≤
        4 ^ sigma := by
    have hPMCast : (((2 * (P + 1) : ℕ) : ℝ)) ≤ 4 * (M : ℝ) := by
      exact_mod_cast (show 2 * (P + 1) ≤ 4 * M by omega)
    have hPow := Real.rpow_le_rpow (by positivity) hPMCast hsigma
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hMPos.le] at hPow
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hMPos sigma)).2 (by
      simpa only [mul_assoc] using hPow)
  have hPEq : (P : ℝ) = T ^ (1 / theta) :=
    calc
      (P : ℝ) = ((P : ℝ) ^ theta) ^ (1 / theta) := by
        rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ P)]
        field_simp [htheta.ne']
        exact (Real.rpow_one _).symm
      _ = T ^ (1 / theta) := by rw [hScale]
  have hPSucc : ((P + 1 : ℕ) : ℝ) ≤ 2 * T ^ (1 / theta) := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    rw [← hPEq]
    nlinarith [hPReal.le]
  have hwThird : w ^ (1 / 3 : ℝ) ≤ 3 * T ^ (1 / 3 : ℝ) := by
    have hRpow := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ w) hwUpper
      (by norm_num : (0 : ℝ) ≤ 1 / 3)
    calc
      w ^ (1 / 3 : ℝ) ≤ (3 * T) ^ (1 / 3 : ℝ) := hRpow
      _ = 3 ^ (1 / 3 : ℝ) * T ^ (1 / 3 : ℝ) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hTPos.le]
      _ ≤ 3 * T ^ (1 / 3 : ℝ) := by
        gcongr
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
            (by norm_num : (1 / 3 : ℝ) ≤ 1)
  have hInside :
      (2 * T ^ (4 * d)) * ((P + 1 : ℕ) : ℝ) * w ^ (1 / 3 : ℝ) ≤
        12 * T ^ (4 * d + 1 / theta + 1 / 3) := by
    calc
      (2 * T ^ (4 * d)) * ((P + 1 : ℕ) : ℝ) * w ^ (1 / 3 : ℝ) ≤
          (2 * T ^ (4 * d)) * (2 * T ^ (1 / theta)) *
            (3 * T ^ (1 / 3 : ℝ)) := by gcongr
      _ = 12 * T ^ (4 * d + 1 / theta + 1 / 3) := by
        rw [Real.rpow_add hTPos, Real.rpow_add hTPos]
        ring
  have hSqrt := Real.sqrt_le_sqrt hInside
  have hSqrtRewrite :
      Real.sqrt (12 * T ^ (4 * d + 1 / theta + 1 / 3)) =
        Real.sqrt 12 * T ^ (2 * d + 1 / (2 * theta) + 1 / 6) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 12)]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hTPos.le]
    congr 1
    field_simp [htheta.ne']
    ring
  calc
    ‖dirichletPoly P (normalizedTypeIReflectedCoeff sigma M) w‖ ≤
        60 * (((2 * (P + 1) : ℕ) : ℝ) ^ sigma / (M : ℝ) ^ sigma) *
          Real.sqrt ((2 * T ^ (4 * d)) * ((P + 1 : ℕ) : ℝ) *
            w ^ (1 / 3 : ℝ)) := hRaw
    _ ≤ 60 * 4 ^ sigma *
          Real.sqrt (12 * T ^ (4 * d + 1 / theta + 1 / 3)) := by gcongr
    _ = (60 * 4 ^ sigma * Real.sqrt 12) *
          T ^ (2 * d + 1 / (2 * theta) + 1 / 6) := by
      rw [hSqrtRewrite]
      ring

/-- The normalized reflected coefficients are real, hence fixed by the
coefficientwise conjugation used to reverse the sign of an ordinate. -/
theorem conjugateCoeffs_normalizedTypeIReflectedCoeff
    (sigma : ℝ) (M : ℕ) :
    conjugateCoeffs (normalizedTypeIReflectedCoeff sigma M) =
      normalizedTypeIReflectedCoeff sigma M := by
  funext n
  unfold conjugateCoeffs normalizedTypeIReflectedCoeff
  split_ifs <;> simp

/-- Reversing the ordinate preserves the norm of a normalized reflected
block.  This is the exact bridge for the negative Poisson half. -/
theorem norm_dirichletPoly_normalizedTypeIReflectedCoeff_neg
    (sigma t : ℝ) (P M : ℕ) :
    ‖dirichletPoly P (normalizedTypeIReflectedCoeff sigma M) (-t)‖ =
      ‖dirichletPoly P (normalizedTypeIReflectedCoeff sigma M) t‖ := by
  have hSource :
      sourceDirichletPoly P (normalizedTypeIReflectedCoeff sigma M) t =
        dirichletPoly P (normalizedTypeIReflectedCoeff sigma M) (-t) := by
    unfold sourceDirichletPoly dirichletPoly
    apply Finset.sum_congr rfl
    intro n _hn
    congr 2
    push_cast
    ring
  calc
    ‖dirichletPoly P (normalizedTypeIReflectedCoeff sigma M) (-t)‖ =
        ‖sourceDirichletPoly P (normalizedTypeIReflectedCoeff sigma M) t‖ :=
      congrArg norm hSource.symm
    _ = ‖sourceDirichletPoly P
          (conjugateCoeffs (normalizedTypeIReflectedCoeff sigma M)) t‖ := by
      rw [conjugateCoeffs_normalizedTypeIReflectedCoeff]
    _ = ‖dirichletPoly P (normalizedTypeIReflectedCoeff sigma M) t‖ :=
      norm_sourceDirichletPoly_conjugateCoeffs _ _ _

/-- The translated negative Poisson block has the norm of the same real
coefficient block at the positive reflected ordinate `3T-v`. -/
theorem norm_phaseShifted_normalized_reflected_eq
    (sigma T v : ℝ) (P M : ℕ) :
    ‖dirichletPoly P
        (phaseShiftCoeffs (-3 * T)
          (normalizedTypeIReflectedCoeff sigma M)) v‖ =
      ‖dirichletPoly P (normalizedTypeIReflectedCoeff sigma M) (3 * T - v)‖ := by
  rw [← dirichletPoly_translate]
  convert norm_dirichletPoly_normalizedTypeIReflectedCoeff_neg
    sigma (3 * T - v) P M using 2
  all_goals ring_nf

/-- One cancellation-safe interface for the two retained Poisson signs.
The coefficient sequence is existential because the negative sign carries
the fixed translation by `-3T`, whereas the positive sign does not.  The
last field identifies its norm with the same normalized reflected block at
an actual positive ordinate in `[T/2,5T/2]`; this is the bridge needed by
the Weyl alternative after the finite sign and displacement selections. -/
theorem extract_common_signed_reflected_block
    {M : ℕ} {sigma T D H S : ℝ} (W : Finset ℝ)
    (hM : 1 < M) (hsigma : 0 ≤ sigma) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (hDH : D + H ≤ T / 2)
    (hSeparated : IsSeparated 1 W)
    (hRange : ∀ t ∈ W, T - D ≤ t ∧ t ≤ 2 * T + D)
    (hEach : ∀ t ∈ W,
      (∃ u ∈ Set.Icc (-H) H,
        S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
          (normalizedTypeIReflectedCoeff sigma M) (-(t + u))‖) ∨
      (∃ u ∈ Set.Icc (-H) H,
        S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
          (normalizedTypeIReflectedCoeff sigma M) (t - u)‖)) :
    ∃ j ∈ Finset.range (Nat.clog 2 M), ∃ U : Finset ℝ,
      ∃ a : ℕ → ℂ,
        IsSeparated 1 U ∧ InBaseInterval (3 * T) U ∧
        (∀ v ∈ U, T / 2 ≤ v ∧ v ≤ 5 * T / 2) ∧
        W.card ≤ 2 * (2 * (2 * ⌈H⌉₊ + 1)) *
          (Nat.clog 2 M) * U.card ∧
        (∀ n ∈ dyadicInterval (2 ^ j), ‖a n‖ ≤ 1) ∧
        (∀ v ∈ U, S / Nat.clog 2 M ≤ ‖dirichletPoly (2 ^ j) a v‖) ∧
        (∀ v ∈ U, ∃ w ∈ Set.Icc (T / 2) (5 * T / 2),
          ‖dirichletPoly (2 ^ j) a v‖ =
            ‖dirichletPoly (2 ^ j)
              (normalizedTypeIReflectedCoeff sigma M) w‖) := by
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
    obtain ⟨j, hj, U, hSepU, hBaseU, hURange, hCardU, hLargeU⟩ :=
      extract_common_reflected_mhh_block Wsign hM hH hT hDH
        hSepSign hRangeSign hNegative
    let a : ℕ → ℂ := phaseShiftCoeffs (-3 * T)
      (normalizedTypeIReflectedCoeff sigma M)
    refine ⟨j, hj, U, a, hSepU, hBaseU, hURange, ?_, ?_, ?_, ?_⟩
    · calc
        W.card ≤ 2 * Wsign.card := hSignCard
        _ ≤ 2 * ((2 * (2 * ⌈H⌉₊ + 1)) *
            (Nat.clog 2 M) * U.card) := by gcongr
        _ = 2 * (2 * (2 * ⌈H⌉₊ + 1)) *
            (Nat.clog 2 M) * U.card := by ring
    · intro n hn
      dsimp only [a]
      rw [norm_phaseShiftCoeffs]
      exact norm_normalizedTypeIReflectedCoeff_le_one hsigma
        (lt_trans Nat.zero_lt_one hM)
    · exact hLargeU
    · intro v hv
      refine ⟨3 * T - v, ?_, ?_⟩
      · rw [Set.mem_Icc]
        have hvRange := hURange v hv
        constructor <;> linarith
      · dsimp only [a]
        exact norm_phaseShifted_normalized_reflected_eq sigma T v (2 ^ j) M
  · have hSepSign : IsSeparated 1 Wsign := by
      intro x hx y hy hxy
      exact hSeparated x (hWsign hx) y (hWsign hy) hxy
    have hRangeSign : ∀ t ∈ Wsign,
        T - D ≤ t ∧ t ≤ 2 * T + D := by
      intro t ht
      exact hRange t (hWsign ht)
    obtain ⟨j, hj, U, hSepU, hBaseU, hURange, hCardU, hLargeU⟩ :=
      extract_common_positive_reflected_mhh_block Wsign hM hH hT hDH
        hSepSign hRangeSign hPositive
    let a : ℕ → ℂ := normalizedTypeIReflectedCoeff sigma M
    refine ⟨j, hj, U, a, hSepU, hBaseU, hURange, ?_, ?_, ?_, ?_⟩
    · calc
        W.card ≤ 2 * Wsign.card := hSignCard
        _ ≤ 2 * ((2 * (2 * ⌈H⌉₊ + 1)) *
            (Nat.clog 2 M) * U.card) := by gcongr
        _ = 2 * (2 * (2 * ⌈H⌉₊ + 1)) *
            (Nat.clog 2 M) * U.card := by ring
    · intro n hn
      dsimp only [a]
      exact norm_normalizedTypeIReflectedCoeff_le_one hsigma
        (lt_trans Nat.zero_lt_one hM)
    · exact hLargeU
    · intro v hv
      refine ⟨v, hURange v hv, ?_⟩
      rfl

/-- Abel summation on a literal natural interval.  This is the interval
counterpart of `norm_weighted_sum_le_of_antitone`; keeping the endpoints in
the statement avoids replacing a terminal source block by a prefix beginning
at one. -/
theorem norm_weighted_Ioc_le_of_antitone
    (f : ℕ → ℝ) (g : ℕ → ℂ) (L U : ℕ) (B : ℝ)
    (hLU : L < U)
    (hf : ∀ n ∈ Finset.Ioc L U, 0 ≤ f n)
    (hanti : ∀ n, L < n → n < U → f (n + 1) ≤ f n)
    (hpartial : ∀ j, j ≤ U - L →
      ‖∑ i ∈ Finset.range j, g (L + 1 + i)‖ ≤ B) :
    ‖∑ n ∈ Finset.Ioc L U, f n • g n‖ ≤ f (L + 1) * B := by
  have hLen : 0 < U - L := Nat.sub_pos_of_lt hLU
  let F : ℕ → ℝ := fun i => f (L + 1 + i)
  let G : ℕ → ℂ := fun i => g (L + 1 + i)
  have hF : ∀ i, i < U - L → 0 ≤ F i := by
    intro i hi
    exact hf _ (Finset.mem_Ioc.mpr ⟨by omega, by omega⟩)
  have hAntiF : ∀ i, i + 1 < U - L → F (i + 1) ≤ F i := by
    intro i hi
    simpa only [F, Nat.add_assoc] using
      hanti (L + 1 + i) (by omega) (by omega)
  have hBound := norm_weighted_sum_le_of_antitone F G (U - L) B
    hLen hF hAntiF (by
      intro j hj
      simpa only [G] using hpartial j hj)
  have hIoc : Finset.Ioc L U = Finset.Ico (L + 1) (U + 1) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hIoc, Finset.sum_Ico_eq_sum_range]
  have hLength : U + 1 - (L + 1) = U - L := by omega
  rw [hLength]
  simpa only [F, G, Nat.cast_add, Nat.cast_one] using hBound

/-- The fixed smooth step used by the Type-I partition is decreasing. -/
theorem antitone_typeISmoothStep : Antitone typeISmoothStep := by
  intro x y hxy
  unfold typeISmoothStep
  exact Real.smoothTransition.monotone (by linarith)

theorem typeISmoothStep_nonneg (x : ℝ) : 0 ≤ typeISmoothStep x := by
  unfold typeISmoothStep
  exact Real.smoothTransition.nonneg _

theorem typeISmoothStep_le_one (x : ℝ) : typeISmoothStep x ≤ 1 := by
  unfold typeISmoothStep
  exact Real.smoothTransition.le_one _

theorem typeIDyadicCutoff_eq_one_sub_step_of_le
    {x : ℝ} (hx : x ≤ 1) :
    typeIDyadicCutoff x = 1 - typeISmoothStep (2 * x) := by
  rw [typeIDyadicCutoff, typeISmoothStep_eq_one hx]

theorem typeIDyadicCutoff_eq_step_of_one_le
    {x : ℝ} (hx : 1 ≤ x) :
    typeIDyadicCutoff x = typeISmoothStep x := by
  have hzero : typeISmoothStep (2 * x) = 0 :=
    typeISmoothStep_eq_zero (by linarith)
  rw [typeIDyadicCutoff, hzero]
  ring

/-- Real-power deweighting of one source term into the unitary logarithmic
phase used by all finite Abel estimates. -/
theorem source_weighted_cpow_eq_smul_phase
    (w σ t : ℝ) {n : ℕ} (hn : 0 < n) :
    (w : ℂ) * (n : ℂ) ^ (-(σ : ℂ)) *
        (n : ℂ) ^ (-(t : ℂ) * I) =
      (w * (n : ℝ) ^ (-σ)) •
        unitaryPhase (logarithmicPhase t n) := by
  rw [Complex.real_smul,
    unitaryPhase_logarithmicPhase_eq_cpow t n hn]
  rw [Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg n)]
  simp only [Complex.ofReal_natCast]
  push_cast
  ring

/-- A decreasing smooth cutoff can be inserted into the Abel-summed
second-derivative estimate without changing its square-root majorant. -/
theorem norm_smoothStep_weighted_Ioc_le_sqrt
    (c σ t : ℝ) (Q L U : ℕ)
    (hc : 0 ≤ c) (hσ : 0 ≤ σ) (hQ : 0 < Q)
    (hL : 0 < L) (hLU : L < U) (hLength : U - L ≤ L)
    (hLt : (L : ℝ) ≤ t) (htL : t ≤ (L : ℝ) ^ 2) :
    ‖∑ n ∈ Finset.Ioc L U,
        (typeISmoothStep (c * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)‖ ≤
      (L + 1 : ℝ) ^ (-σ) * (100 * Real.sqrt t) := by
  let f : ℕ → ℝ := fun n =>
    typeISmoothStep (c * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)
  let g : ℕ → ℂ := fun n => unitaryPhase (logarithmicPhase t n)
  have hQReal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hf : ∀ n ∈ Finset.Ioc L U, 0 ≤ f n := by
    intro n _hn
    dsimp only [f]
    exact mul_nonneg (typeISmoothStep_nonneg _) (Real.rpow_nonneg (by positivity) _)
  have hanti : ∀ n, L < n → n < U → f (n + 1) ≤ f n := by
    intro n hnL _hnU
    have hnPos : 0 < n := lt_trans hL hnL
    have harg : c * (n : ℝ) / Q ≤ c * ((n + 1 : ℕ) : ℝ) / Q := by
      apply div_le_div_of_nonneg_right _ hQReal.le
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ n) hc
    have hstep := antitone_typeISmoothStep harg
    have hpow : ((n + 1 : ℕ) : ℝ) ^ (-σ) ≤ (n : ℝ) ^ (-σ) := by
      apply Real.rpow_le_rpow_of_nonpos
      · positivity
      · exact_mod_cast Nat.le_succ n
      · linarith
    dsimp only [f]
    exact mul_le_mul hstep hpow (Real.rpow_nonneg (by positivity) _)
      (typeISmoothStep_nonneg _)
  have hpartial : ∀ j, j ≤ U - L →
      ‖∑ i ∈ Finset.range j, g (L + 1 + i)‖ ≤ 100 * Real.sqrt t := by
    intro j hj
    dsimp only [g]
    simpa only [Nat.cast_add, Nat.cast_one, Nat.add_assoc, add_assoc] using
      norm_logarithmicPhase_prefix_le_sqrt L j t hL
        (hj.trans hLength) hLt htL
  have hBound := norm_weighted_Ioc_le_of_antitone f g L U
    (100 * Real.sqrt t) hLU hf hanti hpartial
  have hStepOne : typeISmoothStep
      (c * (((L + 1 : ℕ) : ℝ)) / Q) ≤ 1 := typeISmoothStep_le_one _
  have hPowNonneg : 0 ≤ ((L + 1 : ℕ) : ℝ) ^ (-σ) :=
    Real.rpow_nonneg (by positivity) _
  calc
    ‖∑ n ∈ Finset.Ioc L U,
        (typeISmoothStep (c * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)‖ =
        ‖∑ n ∈ Finset.Ioc L U, f n • g n‖ := by rfl
    _ ≤ f (L + 1) * (100 * Real.sqrt t) := hBound
    _ ≤ ((L + 1 : ℕ) : ℝ) ^ (-σ) * (100 * Real.sqrt t) := by
      dsimp only [f]
      gcongr
      exact mul_le_of_le_one_left hPowNonneg hStepOne
    _ = (L + 1 : ℝ) ^ (-σ) * (100 * Real.sqrt t) := by norm_num

/-- Weyl A--B-process companion to the preceding smooth-weight Abel bound.
It applies to the exact monotone cutoff occurring in a classified source
block and retains the physical ordinate `t`. -/
theorem norm_smoothStep_weighted_Ioc_le_weyl
    (X c σ t : ℝ) (Q L U : ℕ)
    (hc : 0 ≤ c) (hσ : 0 ≤ σ) (hQ : 0 < Q)
    (hL : 0 < L) (hLU : L < U) (hLength : U - L ≤ L)
    (htOne : 1 ≤ t) (hX : 1 ≤ X)
    (hSquare : (((L + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ X * t)
    (hCube : t ≤ (((L + 1 : ℕ) : ℝ) ^ (3 : ℕ))) :
    ‖∑ n ∈ Finset.Ioc L U,
        (typeISmoothStep (c * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)‖ ≤
      ((L + 1 : ℕ) : ℝ) ^ (-σ) *
        (30 * Real.sqrt (X * ((L + 1 : ℕ) : ℝ) * t ^ (1 / 3 : ℝ))) := by
  let f : ℕ → ℝ := fun n =>
    typeISmoothStep (c * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)
  let g : ℕ → ℂ := fun n => unitaryPhase (logarithmicPhase t n)
  let Y : ℝ := t ^ (1 / 3 : ℝ)
  have htPos : 0 < t := zero_lt_one.trans_le htOne
  have hYOne : 1 ≤ Y := Real.one_le_rpow htOne (by norm_num)
  have hYcube : Y ^ (3 : ℕ) = t := by
    dsimp only [Y]
    rw [← Real.rpow_natCast, ← Real.rpow_mul htPos.le]
    norm_num
  have hYUpper : Y ≤ ((L + 1 : ℕ) : ℝ) := by
    have hRoot := Real.rpow_le_rpow htPos.le hCube
      (by norm_num : (0 : ℝ) ≤ 1 / 3)
    have hBasePos : (0 : ℝ) < (L + 1 : ℕ) := by positivity
    have hRight :
        ((((L + 1 : ℕ) : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ)) =
          ((L + 1 : ℕ) : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hBasePos.le]
      norm_num
    simpa only [Y, hRight] using hRoot
  have hQReal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hf : ∀ n ∈ Finset.Ioc L U, 0 ≤ f n := by
    intro n _hn
    dsimp only [f]
    exact mul_nonneg (typeISmoothStep_nonneg _)
      (Real.rpow_nonneg (by positivity) _)
  have hanti : ∀ n, L < n → n < U → f (n + 1) ≤ f n := by
    intro n hnL _hnU
    have hnPos : 0 < n := lt_trans hL hnL
    have harg : c * (n : ℝ) / Q ≤ c * ((n + 1 : ℕ) : ℝ) / Q := by
      apply div_le_div_of_nonneg_right _ hQReal.le
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ n) hc
    have hstep := antitone_typeISmoothStep harg
    have hpow : ((n + 1 : ℕ) : ℝ) ^ (-σ) ≤ (n : ℝ) ^ (-σ) := by
      apply Real.rpow_le_rpow_of_nonpos
      · positivity
      · exact_mod_cast Nat.le_succ n
      · linarith
    dsimp only [f]
    exact mul_le_mul hstep hpow (Real.rpow_nonneg (by positivity) _)
      (typeISmoothStep_nonneg _)
  have hpartial : ∀ j, j ≤ U - L →
      ‖∑ i ∈ Finset.range j, g (L + 1 + i)‖ ≤
        30 * Real.sqrt (X * ((L + 1 : ℕ) : ℝ) * Y) := by
    intro j hj
    dsimp only [g]
    have hWeyl := logarithmic_weyl_exponent_pair_prefix_with_slack
      Y X (L + 1) j hYOne hX (by omega) hYUpper
      (by simpa only [hYcube] using hSquare)
      (hj.trans hLength |>.trans (Nat.le_succ L))
    rw [logarithmicSum_eq_sum_range] at hWeyl
    rw [hYcube] at hWeyl
    simpa only [Nat.cast_add, Nat.cast_one, Nat.add_assoc, add_assoc] using hWeyl
  have hBound := norm_weighted_Ioc_le_of_antitone f g L U
    (30 * Real.sqrt (X * ((L + 1 : ℕ) : ℝ) * Y)) hLU hf hanti hpartial
  have hStepOne : typeISmoothStep
      (c * (((L + 1 : ℕ) : ℝ)) / Q) ≤ 1 := typeISmoothStep_le_one _
  have hPowNonneg : 0 ≤ ((L + 1 : ℕ) : ℝ) ^ (-σ) :=
    Real.rpow_nonneg (by positivity) _
  calc
    ‖∑ n ∈ Finset.Ioc L U,
        (typeISmoothStep (c * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)‖ =
        ‖∑ n ∈ Finset.Ioc L U, f n • g n‖ := by rfl
    _ ≤ f (L + 1) *
        (30 * Real.sqrt (X * ((L + 1 : ℕ) : ℝ) * Y)) := hBound
    _ ≤ ((L + 1 : ℕ) : ℝ) ^ (-σ) *
        (30 * Real.sqrt (X * ((L + 1 : ℕ) : ℝ) * Y)) := by
      dsimp only [f]
      gcongr
      exact mul_le_of_le_one_left hPowNonneg hStepOne
    _ = ((L + 1 : ℕ) : ℝ) ^ (-σ) *
        (30 * Real.sqrt (X * ((L + 1 : ℕ) : ℝ) * t ^ (1 / 3 : ℝ))) := by
      rfl

/-- Uncut specialization of the smooth Weyl estimate, used for the middle
term in the exact three-sum source expansion. -/
theorem norm_plain_weighted_Ioc_le_weyl
    (X σ t : ℝ) (L U : ℕ)
    (hσ : 0 ≤ σ) (hL : 0 < L) (hLU : L < U)
    (hLength : U - L ≤ L) (htOne : 1 ≤ t) (hX : 1 ≤ X)
    (hSquare : (((L + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ X * t)
    (hCube : t ≤ (((L + 1 : ℕ) : ℝ) ^ (3 : ℕ))) :
    ‖∑ n ∈ Finset.Ioc L U,
        ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)‖ ≤
      ((L + 1 : ℕ) : ℝ) ^ (-σ) *
        (30 * Real.sqrt (X * ((L + 1 : ℕ) : ℝ) * t ^ (1 / 3 : ℝ))) := by
  have h := norm_smoothStep_weighted_Ioc_le_weyl
    X 0 σ t 1 L U (by norm_num) hσ (by omega) hL hLU hLength
      htOne hX hSquare hCube
  have hEq :
      (∑ n ∈ Finset.Ioc L U,
        ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)) =
      ∑ n ∈ Finset.Ioc L U,
        (typeISmoothStep (0 * (n : ℝ) / 1) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [show (0 : ℝ) * (n : ℝ) / 1 = 0 by ring,
      typeISmoothStep_eq_one (by norm_num : (0 : ℝ) ≤ 1), one_mul]
  rw [hEq]
  simpa only [Nat.cast_one] using h

/-- Exact three-sum form of a source block whose upper tail boundary meets
the sharp cutoff.  The rising half of the annular cutoff is written as the
difference of two decreasing weights, and the falling half is already a
decreasing smooth step. -/
theorem typeISourceSmoothBlock_eq_terminal_three_sums
    (Y A r : ℕ) (σ t : ℝ) (hY : 0 < Y)
    (hLower : 2 * (Y + 1) ≤ 2 ^ r * Y) :
    let Q := 2 ^ r * Y
    typeISourceSmoothBlock Y A r σ t =
      (∑ n ∈ Finset.Ioc (Q / 2) (min Q A),
        ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)) -
      (∑ n ∈ Finset.Ioc (Q / 2) (min Q A),
        (typeISmoothStep (2 * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)) +
      (∑ n ∈ Finset.Ioc Q A,
        (typeISmoothStep ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)) := by
  dsimp only
  let Q : ℕ := 2 ^ r * Y
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hYHalf : Y ≤ Q / 2 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mpr
    omega
  have hYQ : Y ≤ Q := hYHalf.trans (Nat.div_le_self Q 2)
  have hLowerSubset : Finset.Ioc (Q / 2) (min Q A) ⊆
      Finset.Ioc Y (min Q A) := by
    intro n hn
    have hndata := Finset.mem_Ioc.mp hn
    exact Finset.mem_Ioc.mpr ⟨hYHalf.trans_lt hndata.1, hndata.2⟩
  have hRestricted :
      (∑ n ∈ Finset.Ioc Y (min Q A),
        (typeIDyadicCutoff ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)) =
      ∑ n ∈ Finset.Ioc (Q / 2) (min Q A),
        (typeIDyadicCutoff ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n) := by
    rw [← Finset.sum_subset hLowerSubset]
    intro n hn hnSmall
    have hnData := Finset.mem_Ioc.mp hn
    have hnHalf : n ≤ Q / 2 := by
      by_contra hnot
      exact hnSmall (Finset.mem_Ioc.mpr ⟨lt_of_not_ge hnot, hnData.2⟩)
    have hRatio : (n : ℝ) / Q ≤ 1 / 2 := by
      rw [div_le_iff₀ (by exact_mod_cast hQ)]
      have hnTwice : 2 * n ≤ Q :=
        by simpa [Nat.mul_comm] using
          (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mp hnHalf
      have hnTwiceReal : (2 : ℝ) * n ≤ Q := by exact_mod_cast hnTwice
      nlinarith
    rw [typeIDyadicCutoff_eq_zero_of_le_half hRatio, zero_mul, zero_smul]
  have hLowerExpand :
      (∑ n ∈ Finset.Ioc (Q / 2) (min Q A),
        (typeIDyadicCutoff ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)) =
      (∑ n ∈ Finset.Ioc (Q / 2) (min Q A),
        ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)) -
      (∑ n ∈ Finset.Ioc (Q / 2) (min Q A),
        (typeISmoothStep (2 * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have hnQ : n ≤ Q :=
      (Finset.mem_Ioc.mp hn).2.trans (min_le_left Q A)
    have hRatio : (n : ℝ) / Q ≤ 1 := by
      rw [div_le_one (by exact_mod_cast hQ)]
      exact_mod_cast hnQ
    rw [typeIDyadicCutoff_eq_one_sub_step_of_le hRatio]
    rw [sub_mul, one_mul, sub_smul]
    simp only [mul_div_assoc]
  have hUpperExpand :
      (∑ n ∈ Finset.Ioc Q A,
        (typeIDyadicCutoff ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)) =
      ∑ n ∈ Finset.Ioc Q A,
        (typeISmoothStep ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnQ : Q < n := (Finset.mem_Ioc.mp hn).1
    have hRatio : 1 ≤ (n : ℝ) / Q := by
      rw [le_div_iff₀ (by exact_mod_cast hQ)]
      norm_num
      exact_mod_cast hnQ.le
    rw [typeIDyadicCutoff_eq_step_of_one_le hRatio]
  rw [typeISourceSmoothBlock_eq_restricted]
  have hCpow :
      (∑ n ∈ Finset.Ioc Y A,
        (typeIDyadicCutoff ((n : ℝ) / Q) : ℂ) *
          (n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-(t : ℂ) * I)) =
      ∑ n ∈ Finset.Ioc Y A,
        (typeIDyadicCutoff ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n) := by
    apply Finset.sum_congr rfl
    intro n hn
    exact source_weighted_cpow_eq_smul_phase _ σ t
      (lt_trans hY (Finset.mem_Ioc.mp hn).1)
  change (∑ n ∈ Finset.Ioc Y A,
      (typeIDyadicCutoff ((n : ℝ) / Q) : ℂ) *
        (n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-(t : ℂ) * I)) = _
  rw [hCpow]
  by_cases hQA : Q ≤ A
  · have hUnion : Finset.Ioc Y Q ∪ Finset.Ioc Q A = Finset.Ioc Y A :=
      Finset.Ioc_union_Ioc_eq_Ioc hYQ hQA
    have hDisjoint : Disjoint (Finset.Ioc Y Q) (Finset.Ioc Q A) :=
      Finset.Ioc_disjoint_Ioc_of_le le_rfl
    rw [← hUnion, Finset.sum_union hDisjoint]
    have hMin : min Q A = Q := min_eq_left hQA
    rw [hMin] at hRestricted hLowerExpand
    rw [hRestricted, hLowerExpand, hUpperExpand]
    rw [min_eq_left hQA]
  · have hAQ : A < Q := lt_of_not_ge hQA
    have hMin : min Q A = A := min_eq_right hAQ.le
    have hUpperEmpty : Finset.Ioc Q A = ∅ := by
      ext n
      simp
      omega
    rw [hMin] at hRestricted hLowerExpand
    rw [hRestricted, hLowerExpand]
    rw [hMin]
    rw [hUpperEmpty, Finset.sum_empty, add_zero]

/-- The coefficient-one member of the three-sum terminal decomposition obeys
the same interval Abel bound as its smooth companions. -/
theorem norm_plain_weighted_Ioc_le_sqrt
    {L U : ℕ} {σ t : ℝ}
    (hσ : 0 ≤ σ) (hLU : L < U) (hL : 0 < L)
    (hLength : U - L ≤ L) (hLt : (L : ℝ) ≤ t)
    (htL : t ≤ (L : ℝ) ^ 2) :
    ‖∑ n ∈ Finset.Ioc L U,
        ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)‖ ≤
      (L + 1 : ℝ) ^ (-σ) * (100 * Real.sqrt t) := by
  let f : ℕ → ℝ := fun n => (n : ℝ) ^ (-σ)
  let g : ℕ → ℂ := fun n => unitaryPhase (logarithmicPhase t n)
  have hf : ∀ n ∈ Finset.Ioc L U, 0 ≤ f n := by
    intro n _hn
    exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hanti : ∀ n, L < n → n < U → f (n + 1) ≤ f n := by
    intro n hnL _hnU
    dsimp only [f]
    exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (lt_trans hL hnL))
      (by exact_mod_cast Nat.le_succ n) (neg_nonpos.mpr hσ)
  have hpartial : ∀ j, j ≤ U - L →
      ‖∑ i ∈ Finset.range j, g (L + 1 + i)‖ ≤ 100 * Real.sqrt t := by
    intro j hj
    dsimp only [g]
    simpa only [Nat.cast_add, Nat.cast_one, Nat.add_assoc, add_assoc] using
      norm_logarithmicPhase_prefix_le_sqrt L j t hL
        (hj.trans hLength) hLt htL
  simpa only [f, g, Nat.cast_add, Nat.cast_one] using
    norm_weighted_Ioc_le_of_antitone f g L U
      (100 * Real.sqrt t) hLU hf hanti hpartial

/-- First-derivative companion to `norm_smoothStep_weighted_Ioc_le_sqrt`.
It covers a terminal interval beginning to the right of the ordinate. -/
theorem norm_smoothStep_weighted_Ioc_le_div
    (c σ t : ℝ) (Q L U : ℕ)
    (hc : 0 ≤ c) (hσ : 0 ≤ σ) (hQ : 0 < Q)
    (hL : 0 < L) (hLU : L < U) (hLength : U - L ≤ L)
    (htOne : 1 ≤ t) (htL : t ≤ (L : ℝ)) :
    ‖∑ n ∈ Finset.Ioc L U,
        (typeISmoothStep (c * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)‖ ≤
      (L + 1 : ℝ) ^ (-σ) * (6 * Real.pi * (L : ℝ) / t) := by
  let f : ℕ → ℝ := fun n =>
    typeISmoothStep (c * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)
  let g : ℕ → ℂ := fun n => unitaryPhase (logarithmicPhase t n)
  have hQReal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hf : ∀ n ∈ Finset.Ioc L U, 0 ≤ f n := by
    intro n _hn
    dsimp only [f]
    exact mul_nonneg (typeISmoothStep_nonneg _) (Real.rpow_nonneg (by positivity) _)
  have hanti : ∀ n, L < n → n < U → f (n + 1) ≤ f n := by
    intro n hnL _hnU
    have hnPos : 0 < n := lt_trans hL hnL
    have harg : c * (n : ℝ) / Q ≤ c * ((n + 1 : ℕ) : ℝ) / Q := by
      apply div_le_div_of_nonneg_right _ hQReal.le
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ n) hc
    have hstep := antitone_typeISmoothStep harg
    have hpow : ((n + 1 : ℕ) : ℝ) ^ (-σ) ≤ (n : ℝ) ^ (-σ) := by
      exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hnPos)
        (by exact_mod_cast Nat.le_succ n) (neg_nonpos.mpr hσ)
    dsimp only [f]
    exact mul_le_mul hstep hpow (Real.rpow_nonneg (by positivity) _)
      (typeISmoothStep_nonneg _)
  have hpartial : ∀ j, j ≤ U - L →
      ‖∑ i ∈ Finset.range j, g (L + 1 + i)‖ ≤
        6 * Real.pi * (L : ℝ) / t := by
    intro j hj
    dsimp only [g]
    simpa only [Nat.cast_add, Nat.cast_one, Nat.add_assoc, add_assoc] using
      norm_logarithmicPhase_prefix_le_div L j t hL
        (hj.trans hLength) htOne htL
  have hBound := norm_weighted_Ioc_le_of_antitone f g L U
    (6 * Real.pi * (L : ℝ) / t) hLU hf hanti hpartial
  have hStepOne : typeISmoothStep
      (c * (((L + 1 : ℕ) : ℝ)) / Q) ≤ 1 := typeISmoothStep_le_one _
  have hPowNonneg : 0 ≤ ((L + 1 : ℕ) : ℝ) ^ (-σ) :=
    Real.rpow_nonneg (by positivity) _
  calc
    ‖∑ n ∈ Finset.Ioc L U,
        (typeISmoothStep (c * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)‖ =
        ‖∑ n ∈ Finset.Ioc L U, f n • g n‖ := by rfl
    _ ≤ f (L + 1) * (6 * Real.pi * (L : ℝ) / t) := hBound
    _ ≤ ((L + 1 : ℕ) : ℝ) ^ (-σ) *
        (6 * Real.pi * (L : ℝ) / t) := by
      dsimp only [f]
      gcongr
      exact mul_le_of_le_one_left hPowNonneg hStepOne
    _ = (L + 1 : ℝ) ^ (-σ) * (6 * Real.pi * (L : ℝ) / t) := by norm_num

/-- First-derivative terminal estimate for the coefficient-one member of the
three-sum source decomposition. -/
theorem norm_plain_weighted_Ioc_le_div
    {L U : ℕ} {σ t : ℝ}
    (hσ : 0 ≤ σ) (hLU : L < U) (hL : 0 < L)
    (hLength : U - L ≤ L) (htOne : 1 ≤ t)
    (htL : t ≤ (L : ℝ)) :
    ‖∑ n ∈ Finset.Ioc L U,
        ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)‖ ≤
      (L + 1 : ℝ) ^ (-σ) * (6 * Real.pi * (L : ℝ) / t) := by
  let f : ℕ → ℝ := fun n => (n : ℝ) ^ (-σ)
  let g : ℕ → ℂ := fun n => unitaryPhase (logarithmicPhase t n)
  have hf : ∀ n ∈ Finset.Ioc L U, 0 ≤ f n := by
    intro n _hn
    exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hanti : ∀ n, L < n → n < U → f (n + 1) ≤ f n := by
    intro n hnL _hnU
    dsimp only [f]
    exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (lt_trans hL hnL))
      (by exact_mod_cast Nat.le_succ n) (neg_nonpos.mpr hσ)
  have hpartial : ∀ j, j ≤ U - L →
      ‖∑ i ∈ Finset.range j, g (L + 1 + i)‖ ≤
        6 * Real.pi * (L : ℝ) / t := by
    intro j hj
    dsimp only [g]
    simpa only [Nat.cast_add, Nat.cast_one, Nat.add_assoc, add_assoc] using
      norm_logarithmicPhase_prefix_le_div L j t hL
        (hj.trans hLength) htOne htL
  simpa only [f, g, Nat.cast_add, Nat.cast_one] using
    norm_weighted_Ioc_le_of_antitone f g L U
      (6 * Real.pi * (L : ℝ) / t) hLU hf hanti hpartial

/-- Uniform interval estimate obtained by routing at the physical comparison
`t ≤ L`.  Keeping both nonnegative majorants makes the later terminal source
assembly independent of that case split. -/
theorem norm_plain_weighted_Ioc_le_sqrt_add_div
    {L U : ℕ} {σ t : ℝ}
    (hσ : 0 ≤ σ) (hL : 0 < L) (hLength : U - L ≤ L)
    (htOne : 1 ≤ t) (htSq : t ≤ (L : ℝ) ^ 2) :
    ‖∑ n ∈ Finset.Ioc L U,
        ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)‖ ≤
      (L + 1 : ℝ) ^ (-σ) *
        (100 * Real.sqrt t + 6 * Real.pi * (L : ℝ) / t) := by
  by_cases hLU : L < U
  · by_cases htL : t ≤ (L : ℝ)
    · exact (norm_plain_weighted_Ioc_le_div hσ hLU hL hLength htOne htL).trans
        (by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
          nlinarith [Real.sqrt_nonneg t])
    · exact (norm_plain_weighted_Ioc_le_sqrt hσ hLU hL hLength
          (le_of_not_ge htL) htSq).trans (by
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
            have hDiv : 0 ≤ 6 * Real.pi * (L : ℝ) / t := by positivity
            linarith)
  · have hEmpty : Finset.Ioc L U = ∅ := by
      ext n
      simp
      omega
    rw [hEmpty, Finset.sum_empty, norm_zero]
    positivity

/-- Smooth-cutoff counterpart of
`norm_plain_weighted_Ioc_le_sqrt_add_div`. -/
theorem norm_smoothStep_weighted_Ioc_le_sqrt_add_div
    (c σ t : ℝ) (Q L U : ℕ)
    (hc : 0 ≤ c) (hσ : 0 ≤ σ) (hQ : 0 < Q)
    (hL : 0 < L) (hLength : U - L ≤ L)
    (htOne : 1 ≤ t) (htSq : t ≤ (L : ℝ) ^ 2) :
    ‖∑ n ∈ Finset.Ioc L U,
        (typeISmoothStep (c * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)‖ ≤
      (L + 1 : ℝ) ^ (-σ) *
        (100 * Real.sqrt t + 6 * Real.pi * (L : ℝ) / t) := by
  by_cases hLU : L < U
  · by_cases htL : t ≤ (L : ℝ)
    · exact (norm_smoothStep_weighted_Ioc_le_div c σ t Q L U hc hσ hQ
          hL hLU hLength htOne htL).trans (by
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
            nlinarith [Real.sqrt_nonneg t])
    · exact (norm_smoothStep_weighted_Ioc_le_sqrt c σ t Q L U hc hσ hQ
          hL hLU hLength (le_of_not_ge htL) htSq).trans
        (by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
          have hDiv : 0 ≤ 6 * Real.pi * (L : ℝ) / t := by positivity
          linarith)
  · have hEmpty : Finset.Ioc L U = ∅ := by
      ext n
      simp
      omega
    rw [hEmpty, Finset.sum_empty, norm_zero]
    positivity

/-- Quantitative elimination bound for a classified upper-edge source block.
The proof uses the exact three-sum identity above and controls all three
pieces without extending the sharp cutoff. -/
theorem norm_typeISourceSmoothBlock_terminal_le
    {Y A r : ℕ} {σ t : ℝ}
    (hY : 0 < Y) (hr : 2 ≤ r)
    (hTerminal : A < 2 * (2 ^ r * Y))
    (hσ : 0 ≤ σ) (htOne : 1 ≤ t)
    (htSq : t ≤ (((2 ^ r * Y) / 2 : ℕ) : ℝ) ^ 2) :
    ‖typeISourceSmoothBlock Y A r σ t‖ ≤
      3 * ((((2 ^ r * Y) / 2 + 1 : ℕ) : ℝ) ^ (-σ)) *
        (100 * Real.sqrt t +
          6 * Real.pi * ((2 ^ r * Y : ℕ) : ℝ) / t) := by
  let Q : ℕ := 2 ^ r * Y
  let L : ℕ := Q / 2
  have hpowFour : 4 ≤ 2 ^ r := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hr
  have hQFour : 4 ≤ Q := by
    dsimp only [Q]
    have hYOne : 1 ≤ Y := hY
    calc
      4 = 4 * 1 := by omega
      _ ≤ 4 * Y := Nat.mul_le_mul_left 4 hYOne
      _ ≤ 2 ^ r * Y := Nat.mul_le_mul_right Y hpowFour
  have hQ : 0 < Q := by omega
  have hL : 0 < L := by dsimp only [L]; omega
  have hEven : 2 ∣ Q := by
    dsimp only [Q]
    exact dvd_mul_of_dvd_left (by
      exact dvd_pow (dvd_refl 2) (by omega : r ≠ 0)) Y
  have hTwiceL : 2 * L = Q := by
    dsimp only [L]
    exact Nat.mul_div_cancel' hEven
  have hLower : 2 * (Y + 1) ≤ Q := by
    calc
      2 * (Y + 1) ≤ 4 * Y := by omega
      _ ≤ Q := by
        dsimp only [Q]
        exact Nat.mul_le_mul_right Y hpowFour
  have hLowerLength : min Q A - L ≤ L := by omega
  have hUpperLength : A - Q ≤ Q := by omega
  have htSqQ : t ≤ (Q : ℝ) ^ 2 := by
    have hLQ : (L : ℝ) ≤ Q := by exact_mod_cast (Nat.div_le_self Q 2)
    have hSq : (L : ℝ) ^ 2 ≤ (Q : ℝ) ^ 2 := by nlinarith
    exact htSq.trans hSq
  let B : ℝ := 100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hPlain := norm_plain_weighted_Ioc_le_sqrt_add_div
    (L := L) (U := min Q A) hσ hL hLowerLength htOne htSq
  have hRise := norm_smoothStep_weighted_Ioc_le_sqrt_add_div
    2 σ t Q L (min Q A) (by norm_num) hσ hQ hL hLowerLength htOne htSq
  have hFall := norm_smoothStep_weighted_Ioc_le_sqrt_add_div
    1 σ t Q Q A (by norm_num) hσ hQ hQ hUpperLength htOne htSqQ
  have hLowerB :
      100 * Real.sqrt t + 6 * Real.pi * (L : ℝ) / t ≤ B := by
    dsimp only [B]
    have hLQ : (L : ℝ) ≤ Q := by exact_mod_cast (Nat.div_le_self Q 2)
    have htPos : 0 < t := by linarith
    gcongr
  have hWeight : ((Q + 1 : ℕ) : ℝ) ^ (-σ) ≤
      ((L + 1 : ℕ) : ℝ) ^ (-σ) := by
    apply Real.rpow_le_rpow_of_nonpos
    · positivity
    · exact_mod_cast Nat.add_le_add_right (Nat.div_le_self Q 2) 1
    · linarith
  have hPlain' :
      ‖∑ n ∈ Finset.Ioc L (min Q A),
          ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)‖ ≤
        ((L + 1 : ℕ) : ℝ) ^ (-σ) * B :=
    by
      simpa only [Nat.cast_add, Nat.cast_one] using
        hPlain.trans (mul_le_mul_of_nonneg_left hLowerB
          (Real.rpow_nonneg (show 0 ≤ (L : ℝ) + 1 by positivity) (-σ)))
  have hRise' :
      ‖∑ n ∈ Finset.Ioc L (min Q A),
          (typeISmoothStep (2 * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
            unitaryPhase (logarithmicPhase t n)‖ ≤
        ((L + 1 : ℕ) : ℝ) ^ (-σ) * B :=
    by
      simpa only [Nat.cast_add, Nat.cast_one] using
        hRise.trans (mul_le_mul_of_nonneg_left hLowerB
          (Real.rpow_nonneg (show 0 ≤ (L : ℝ) + 1 by positivity) (-σ)))
  have hFall' :
      ‖∑ n ∈ Finset.Ioc Q A,
          (typeISmoothStep ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
            unitaryPhase (logarithmicPhase t n)‖ ≤
        ((L + 1 : ℕ) : ℝ) ^ (-σ) * B := by
    calc
      _ ≤ ((Q + 1 : ℕ) : ℝ) ^ (-σ) * B := by
        simpa only [B, Nat.cast_add, Nat.cast_one, one_mul] using hFall
      _ ≤ ((L + 1 : ℕ) : ℝ) ^ (-σ) * B :=
        mul_le_mul_of_nonneg_right hWeight hB
  rw [typeISourceSmoothBlock_eq_terminal_three_sums Y A r σ t hY
    (by simpa only [Q] using hLower)]
  change ‖(∑ n ∈ Finset.Ioc L (min Q A),
        ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)) -
      (∑ n ∈ Finset.Ioc L (min Q A),
        (typeISmoothStep (2 * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)) +
      (∑ n ∈ Finset.Ioc Q A,
        (typeISmoothStep ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n))‖ ≤ _
  calc
    _ ≤ ‖∑ n ∈ Finset.Ioc L (min Q A),
          ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)‖ +
        ‖∑ n ∈ Finset.Ioc L (min Q A),
          (typeISmoothStep (2 * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
            unitaryPhase (logarithmicPhase t n)‖ +
        ‖∑ n ∈ Finset.Ioc Q A,
          (typeISmoothStep ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
            unitaryPhase (logarithmicPhase t n)‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (((L + 1 : ℕ) : ℝ) ^ (-σ) * B) +
        (((L + 1 : ℕ) : ℝ) ^ (-σ) * B) +
        (((L + 1 : ℕ) : ℝ) ^ (-σ) * B) := by linarith
    _ = 3 * ((((2 ^ r * Y) / 2 + 1 : ℕ) : ℝ) ^ (-σ)) *
        (100 * Real.sqrt t + 6 * Real.pi * ((2 ^ r * Y : ℕ) : ℝ) / t) := by
      dsimp only [L, Q, B]
      ring

/-- The falling smooth half of a source block stops exactly at `2Q`, even
when the ambient sharp cutoff is larger. -/
theorem source_upper_smooth_sum_eq_min_two_mul
    (Q A : ℕ) (hQ : 0 < Q) (σ t : ℝ) :
    (∑ n ∈ Finset.Ioc Q A,
        (typeISmoothStep ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)) =
      ∑ n ∈ Finset.Ioc Q (min (2 * Q) A),
        (typeISmoothStep ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n) := by
  have hSub : Finset.Ioc Q (min (2 * Q) A) ⊆ Finset.Ioc Q A := by
    intro n hn
    exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1,
      (Finset.mem_Ioc.mp hn).2.trans (min_le_right _ _)⟩
  rw [← Finset.sum_subset hSub]
  intro n hn hnSmall
  have hnData := Finset.mem_Ioc.mp hn
  have hnTwo : 2 * Q ≤ n := by
    by_contra hnot
    have hnLt : n < 2 * Q := lt_of_not_ge hnot
    exact hnSmall (Finset.mem_Ioc.mpr
      ⟨hnData.1, le_min hnLt.le hnData.2⟩)
  have hRatio : 2 ≤ (n : ℝ) / Q := by
    rw [le_div_iff₀ (by exact_mod_cast hQ)]
    exact_mod_cast hnTwo
  rw [typeISmoothStep_eq_zero hRatio, zero_mul, zero_smul]

/-- Uniform square-root cancellation bound for every classified source
block, with no upper-edge assumption.  The proof uses the exact support at
`2Q`; consequently the ambient sharp cutoff never appears in an interval
length estimate. -/
theorem norm_typeISourceSmoothBlock_le_sqrt
    {Y A r : ℕ} {σ t : ℝ}
    (hY : 0 < Y) (hr : 2 ≤ r) (hσ : 0 ≤ σ)
    (htOne : 1 ≤ t)
    (htSq : t ≤ (((2 ^ r * Y) / 2 : ℕ) : ℝ) ^ 2) :
    ‖typeISourceSmoothBlock Y A r σ t‖ ≤
      3 * ((((2 ^ r * Y) / 2 + 1 : ℕ) : ℝ) ^ (-σ)) *
        (100 * Real.sqrt t +
          6 * Real.pi * ((2 ^ r * Y : ℕ) : ℝ) / t) := by
  let Q : ℕ := 2 ^ r * Y
  let L : ℕ := Q / 2
  let U : ℕ := min (2 * Q) A
  have hpowFour : 4 ≤ 2 ^ r := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hr
  have hQFour : 4 ≤ Q := by
    dsimp only [Q]
    calc
      4 = 4 * 1 := by omega
      _ ≤ 4 * Y := Nat.mul_le_mul_left 4 hY
      _ ≤ 2 ^ r * Y := Nat.mul_le_mul_right Y hpowFour
  have hQ : 0 < Q := by omega
  have hL : 0 < L := by dsimp only [L]; omega
  have hEven : 2 ∣ Q := by
    dsimp only [Q]
    exact dvd_mul_of_dvd_left
      (dvd_pow (dvd_refl 2) (by omega : r ≠ 0)) Y
  have hTwiceL : 2 * L = Q := by
    dsimp only [L]
    exact Nat.mul_div_cancel' hEven
  have hLower : 2 * (Y + 1) ≤ Q := by
    calc
      2 * (Y + 1) ≤ 4 * Y := by omega
      _ ≤ Q := by
        dsimp only [Q]
        exact Nat.mul_le_mul_right Y hpowFour
  have hLowerLength : min Q A - L ≤ L := by omega
  have hUpperLength : U - Q ≤ Q := by
    dsimp only [U]
    omega
  have htSqQ : t ≤ (Q : ℝ) ^ 2 := by
    have hLQ : (L : ℝ) ≤ Q := by exact_mod_cast (Nat.div_le_self Q 2)
    exact htSq.trans (by nlinarith)
  let B : ℝ := 100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hPlain := norm_plain_weighted_Ioc_le_sqrt_add_div
    (L := L) (U := min Q A) hσ hL hLowerLength htOne htSq
  have hRise := norm_smoothStep_weighted_Ioc_le_sqrt_add_div
    2 σ t Q L (min Q A) (by norm_num) hσ hQ hL hLowerLength htOne htSq
  have hFall := norm_smoothStep_weighted_Ioc_le_sqrt_add_div
    1 σ t Q Q U (by norm_num) hσ hQ hQ hUpperLength htOne htSqQ
  have hLowerB :
      100 * Real.sqrt t + 6 * Real.pi * (L : ℝ) / t ≤ B := by
    dsimp only [B]
    have hLQ : (L : ℝ) ≤ Q := by exact_mod_cast (Nat.div_le_self Q 2)
    have htPos : 0 < t := by linarith
    gcongr
  have hWeight : ((Q + 1 : ℕ) : ℝ) ^ (-σ) ≤
      ((L + 1 : ℕ) : ℝ) ^ (-σ) := by
    apply Real.rpow_le_rpow_of_nonpos
    · positivity
    · exact_mod_cast Nat.add_le_add_right (Nat.div_le_self Q 2) 1
    · linarith
  have hPlain' :
      ‖∑ n ∈ Finset.Ioc L (min Q A),
          ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)‖ ≤
        ((L + 1 : ℕ) : ℝ) ^ (-σ) * B := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      hPlain.trans (mul_le_mul_of_nonneg_left hLowerB
        (Real.rpow_nonneg (by positivity) _))
  have hRise' :
      ‖∑ n ∈ Finset.Ioc L (min Q A),
          (typeISmoothStep (2 * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
            unitaryPhase (logarithmicPhase t n)‖ ≤
        ((L + 1 : ℕ) : ℝ) ^ (-σ) * B := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      hRise.trans (mul_le_mul_of_nonneg_left hLowerB
        (Real.rpow_nonneg (by positivity) _))
  have hFall' :
      ‖∑ n ∈ Finset.Ioc Q A,
          (typeISmoothStep ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
            unitaryPhase (logarithmicPhase t n)‖ ≤
        ((L + 1 : ℕ) : ℝ) ^ (-σ) * B := by
    rw [source_upper_smooth_sum_eq_min_two_mul Q A hQ σ t]
    calc
      _ ≤ ((Q + 1 : ℕ) : ℝ) ^ (-σ) *
          (100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t) := by
        simpa only [U, Nat.cast_add, Nat.cast_one, one_mul] using hFall
      _ ≤ ((L + 1 : ℕ) : ℝ) ^ (-σ) * B :=
        mul_le_mul_of_nonneg_right hWeight hB
  rw [typeISourceSmoothBlock_eq_terminal_three_sums Y A r σ t hY
    (by simpa only [Q] using hLower)]
  change ‖(∑ n ∈ Finset.Ioc L (min Q A),
        ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)) -
      (∑ n ∈ Finset.Ioc L (min Q A),
        (typeISmoothStep (2 * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)) +
      (∑ n ∈ Finset.Ioc Q A,
        (typeISmoothStep ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n))‖ ≤ _
  calc
    _ ≤ ‖∑ n ∈ Finset.Ioc L (min Q A),
          ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)‖ +
        ‖∑ n ∈ Finset.Ioc L (min Q A),
          (typeISmoothStep (2 * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
            unitaryPhase (logarithmicPhase t n)‖ +
        ‖∑ n ∈ Finset.Ioc Q A,
          (typeISmoothStep ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
            unitaryPhase (logarithmicPhase t n)‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ ((L + 1 : ℕ) : ℝ) ^ (-σ) * B +
        ((L + 1 : ℕ) : ℝ) ^ (-σ) * B +
        ((L + 1 : ℕ) : ℝ) ^ (-σ) * B := by linarith
    _ = 3 * ((((2 ^ r * Y) / 2 + 1 : ℕ) : ℝ) ^ (-σ)) *
        (100 * Real.sqrt t + 6 * Real.pi * ((2 ^ r * Y : ℕ) : ℝ) / t) := by
      dsimp only [L, Q, B]
      ring

/-- Uniform Weyl bound for a complete source-smooth block in the physical
range `Q^2 \lesssim t \lesssim Q^3`.  This theorem consumes the exact
three-sum expansion of the source block, including both smooth boundary
pieces, rather than replacing it by a coefficient-free model. -/
theorem norm_typeISourceSmoothBlock_le_weyl
    {Y A r : ℕ} {σ t : ℝ}
    (hY : 0 < Y) (hr : 2 ≤ r)
    (hInterior : 2 * (2 ^ r * Y) ≤ A) (hσ : 0 ≤ σ)
    (htOne : 1 ≤ t)
    (hSquare : ((((2 ^ r * Y) + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ 8 * t)
    (hCube : t ≤ ((((2 ^ r * Y) / 2 + 1 : ℕ) : ℝ) ^ (3 : ℕ))) :
    ‖typeISourceSmoothBlock Y A r σ t‖ ≤
      90 * ((((2 ^ r * Y) / 2 + 1 : ℕ) : ℝ) ^ (-σ)) *
        Real.sqrt (8 * (((2 ^ r * Y + 1 : ℕ) : ℝ)) * t ^ (1 / 3 : ℝ)) := by
  let Q : ℕ := 2 ^ r * Y
  let L : ℕ := Q / 2
  let U : ℕ := min (2 * Q) A
  let R : ℝ := Real.sqrt (8 * ((Q + 1 : ℕ) : ℝ) * t ^ (1 / 3 : ℝ))
  have hpowFour : 4 ≤ 2 ^ r := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hr
  have hQFour : 4 ≤ Q := by
    dsimp only [Q]
    calc
      4 = 4 * 1 := by omega
      _ ≤ 4 * Y := Nat.mul_le_mul_left 4 hY
      _ ≤ 2 ^ r * Y := Nat.mul_le_mul_right Y hpowFour
  have hQ : 0 < Q := by omega
  have hL : 0 < L := by dsimp only [L]; omega
  have hEven : 2 ∣ Q := by
    dsimp only [Q]
    exact dvd_mul_of_dvd_left
      (dvd_pow (dvd_refl 2) (by omega : r ≠ 0)) Y
  have hTwiceL : 2 * L = Q := by
    dsimp only [L]
    exact Nat.mul_div_cancel' hEven
  have hLower : 2 * (Y + 1) ≤ Q := by
    calc
      2 * (Y + 1) ≤ 4 * Y := by omega
      _ ≤ Q := by
        dsimp only [Q]
        exact Nat.mul_le_mul_right Y hpowFour
  have hLowerLength : min Q A - L ≤ L := by omega
  have hUpperLength : U - Q ≤ Q := by
    dsimp only [U]
    omega
  have hLQ : L + 1 ≤ Q + 1 := by omega
  have hLQReal : (((L + 1 : ℕ) : ℝ)) ≤ (((Q + 1 : ℕ) : ℝ)) := by
    exact_mod_cast hLQ
  have hSquareL : (((L + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ 8 * t := by
    exact (pow_le_pow_left₀ (by positivity) hLQReal 2).trans
      (by simpa only [Q] using hSquare)
  have hSquareQ : (((Q + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ 8 * t := by
    simpa only [Q] using hSquare
  have hCubeQ : t ≤ (((Q + 1 : ℕ) : ℝ) ^ (3 : ℕ)) :=
    hCube.trans (pow_le_pow_left₀ (by positivity) hLQReal 3)
  have hPlain := norm_plain_weighted_Ioc_le_weyl
    8 σ t L (min Q A) hσ hL (by omega) hLowerLength htOne
      (by norm_num) hSquareL
      (by simpa only [L, Q] using hCube)
  have hRise := norm_smoothStep_weighted_Ioc_le_weyl
    8 2 σ t Q L (min Q A) (by norm_num) hσ hQ hL (by omega)
      hLowerLength htOne (by norm_num) hSquareL
      (by simpa only [L, Q] using hCube)
  have hFall := norm_smoothStep_weighted_Ioc_le_weyl
    8 1 σ t Q Q U (by norm_num) hσ hQ hQ (by omega)
      hUpperLength htOne (by norm_num) hSquareQ hCubeQ
  have hRoot :
      Real.sqrt (8 * ((L + 1 : ℕ) : ℝ) * t ^ (1 / 3 : ℝ)) ≤ R := by
    dsimp only [R]
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hLQReal (by norm_num))
      (Real.rpow_nonneg (by positivity) _)
  have hWeight : (((Q + 1 : ℕ) : ℝ)) ^ (-σ) ≤
      (((L + 1 : ℕ) : ℝ)) ^ (-σ) := by
    apply Real.rpow_le_rpow_of_nonpos
    · positivity
    · exact_mod_cast hLQ
    · linarith
  have hPlain' :
      ‖∑ n ∈ Finset.Ioc L (min Q A),
          ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)‖ ≤
        (((L + 1 : ℕ) : ℝ)) ^ (-σ) * (30 * R) := by
    exact hPlain.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hRoot (by norm_num))
      (Real.rpow_nonneg (by positivity) _))
  have hRise' :
      ‖∑ n ∈ Finset.Ioc L (min Q A),
          (typeISmoothStep (2 * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
            unitaryPhase (logarithmicPhase t n)‖ ≤
        (((L + 1 : ℕ) : ℝ)) ^ (-σ) * (30 * R) := by
    exact hRise.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hRoot (by norm_num))
      (Real.rpow_nonneg (by positivity) _))
  have hFall' :
      ‖∑ n ∈ Finset.Ioc Q A,
          (typeISmoothStep ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
            unitaryPhase (logarithmicPhase t n)‖ ≤
        (((L + 1 : ℕ) : ℝ)) ^ (-σ) * (30 * R) := by
    rw [source_upper_smooth_sum_eq_min_two_mul Q A hQ σ t]
    calc
      _ ≤ (((Q + 1 : ℕ) : ℝ)) ^ (-σ) * (30 * R) := by
        simpa only [U, R, one_mul] using hFall
      _ ≤ (((L + 1 : ℕ) : ℝ)) ^ (-σ) * (30 * R) := by
        exact mul_le_mul_of_nonneg_right hWeight (by positivity)
  rw [typeISourceSmoothBlock_eq_terminal_three_sums Y A r σ t hY
    (by simpa only [Q] using hLower)]
  change ‖(∑ n ∈ Finset.Ioc L (min Q A),
        ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)) -
      (∑ n ∈ Finset.Ioc L (min Q A),
        (typeISmoothStep (2 * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)) +
      (∑ n ∈ Finset.Ioc Q A,
        (typeISmoothStep ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n))‖ ≤ _
  calc
    _ ≤ ‖∑ n ∈ Finset.Ioc L (min Q A),
          ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)‖ +
        ‖∑ n ∈ Finset.Ioc L (min Q A),
          (typeISmoothStep (2 * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
            unitaryPhase (logarithmicPhase t n)‖ +
        ‖∑ n ∈ Finset.Ioc Q A,
          (typeISmoothStep ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
            unitaryPhase (logarithmicPhase t n)‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (((L + 1 : ℕ) : ℝ)) ^ (-σ) * (30 * R) +
        (((L + 1 : ℕ) : ℝ)) ^ (-σ) * (30 * R) +
        (((L + 1 : ℕ) : ℝ)) ^ (-σ) * (30 * R) := by linarith
    _ = 90 * ((((2 ^ r * Y) / 2 + 1 : ℕ) : ℝ) ^ (-σ)) *
        Real.sqrt (8 * (((2 ^ r * Y + 1 : ℕ) : ℝ)) * t ^ (1 / 3 : ℝ)) := by
      dsimp only [L, Q, R]
      ring

/-- Physical form of the preceding source-block Weyl estimate.  The source
length is kept as the actual natural `Q = 2^r Y`, and the identity
`Q^tau = T` is used only at the final exponent conversion. -/
theorem norm_typeISourceSmoothBlock_le_physical_weyl
    {Y A r : ℕ} {σ T t tau : ℝ}
    (hY : 0 < Y) (hr : 2 ≤ r)
    (hInterior : 2 * (2 ^ r * Y) ≤ A)
    (hσ : 0 ≤ σ) (hσUpper : σ ≤ 1)
    (hT : 1 ≤ T) (htOne : 1 ≤ t) (htUpper : t ≤ 3 * T)
    (htau : 0 < tau)
    (hScale : (((2 ^ r * Y : ℕ) : ℝ)) ^ tau = T)
    (hSquare : ((((2 ^ r * Y) + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ 8 * t)
    (hCube : t ≤ ((((2 ^ r * Y) / 2 + 1 : ℕ) : ℝ) ^ (3 : ℕ))) :
    ‖typeISourceSmoothBlock Y A r σ t‖ ≤
      (180 * Real.sqrt 48) *
        T ^ ((1 / 2 - σ) / tau + 1 / 6) := by
  let Q : ℕ := 2 ^ r * Y
  have hQFour : 4 ≤ Q := by
    have hPow : 4 ≤ 2 ^ r := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hr
    dsimp only [Q]
    exact hPow.trans (Nat.le_mul_of_pos_right _ hY)
  have hQPos : (0 : ℝ) < Q := by positivity
  have hQOne : (1 : ℝ) ≤ Q := by exact_mod_cast (by omega : 1 ≤ Q)
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have hEven : 2 ∣ Q := by
    dsimp only [Q]
    exact dvd_mul_of_dvd_left
      (dvd_pow (dvd_refl 2) (by omega : r ≠ 0)) Y
  have hHalfCast : ((Q / 2 : ℕ) : ℝ) = (Q : ℝ) / 2 := by
    have hTwice : 2 * (Q / 2) = Q := Nat.mul_div_cancel' hEven
    have hTwiceReal : (2 : ℝ) * (Q / 2 : ℕ) = Q := by exact_mod_cast hTwice
    linarith
  have hHalfPos : (0 : ℝ) < Q / 2 := by positivity
  have hWeight : (((Q / 2 + 1 : ℕ) : ℝ)) ^ (-σ) ≤
      2 * (Q : ℝ) ^ (-σ) := by
    have hHalfLe : (Q : ℝ) / 2 ≤ ((Q / 2 + 1 : ℕ) : ℝ) := by
      norm_num only [Nat.cast_add, Nat.cast_one, hHalfCast]
      linarith
    have hAnti : (((Q / 2 + 1 : ℕ) : ℝ)) ^ (-σ) ≤
        ((Q : ℝ) / 2) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos hHalfPos hHalfLe (neg_nonpos.mpr hσ)
    have hTwoPow : (2 : ℝ) ^ σ ≤ 2 := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hσUpper
    calc
      (((Q / 2 + 1 : ℕ) : ℝ)) ^ (-σ) ≤ ((Q : ℝ) / 2) ^ (-σ) := by
        simpa only [hHalfCast] using hAnti
      _ = (2 : ℝ) ^ σ * (Q : ℝ) ^ (-σ) := by
        rw [Real.div_rpow hQPos.le (by norm_num : (0 : ℝ) ≤ 2)]
        rw [Real.rpow_neg (by norm_num : (2 : ℝ) ≥ 0)]
        field_simp [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) σ]
      _ ≤ 2 * (Q : ℝ) ^ (-σ) := by gcongr
  have hQSucc : (((Q + 1 : ℕ) : ℝ)) ≤ 2 * Q := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have htThird : t ^ (1 / 3 : ℝ) ≤ 3 * T ^ (1 / 3 : ℝ) := by
    have hPow := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ t) htUpper
      (by norm_num : (0 : ℝ) ≤ 1 / 3)
    calc
      t ^ (1 / 3 : ℝ) ≤ (3 * T) ^ (1 / 3 : ℝ) := hPow
      _ = 3 ^ (1 / 3 : ℝ) * T ^ (1 / 3 : ℝ) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hTPos.le]
      _ ≤ 3 * T ^ (1 / 3 : ℝ) := by
        gcongr
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
            (by norm_num : (1 / 3 : ℝ) ≤ 1)
  have hInside : 8 * (((Q + 1 : ℕ) : ℝ)) * t ^ (1 / 3 : ℝ) ≤
      48 * (Q : ℝ) * T ^ (1 / 3 : ℝ) := by
    calc
      8 * (((Q + 1 : ℕ) : ℝ)) * t ^ (1 / 3 : ℝ) ≤
          8 * (2 * (Q : ℝ)) * (3 * T ^ (1 / 3 : ℝ)) := by gcongr
      _ = 48 * (Q : ℝ) * T ^ (1 / 3 : ℝ) := by ring
  have hSqrt := Real.sqrt_le_sqrt hInside
  have hSqrtRewrite :
      Real.sqrt (48 * (Q : ℝ) * T ^ (1 / 3 : ℝ)) =
        Real.sqrt 48 * (Q : ℝ) ^ (1 / 2 : ℝ) * T ^ (1 / 6 : ℝ) := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 48 * (Q : ℝ)),
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 48)]
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    congr 1
    rw [← Real.rpow_mul hTPos.le]
    congr 1
    ring
  have hQPower : (Q : ℝ) ^ (1 / 2 - σ) =
      T ^ ((1 / 2 - σ) / tau) := by
    rw [← hScale, ← Real.rpow_mul hQPos.le]
    congr 1
    field_simp [htau.ne']
  have hRaw := norm_typeISourceSmoothBlock_le_weyl
    hY hr hInterior hσ htOne hSquare hCube
  calc
    ‖typeISourceSmoothBlock Y A r σ t‖ ≤
        90 * (((Q / 2 + 1 : ℕ) : ℝ) ^ (-σ)) *
          Real.sqrt (8 * (((Q + 1 : ℕ) : ℝ)) * t ^ (1 / 3 : ℝ)) := by
      simpa only [Q] using hRaw
    _ ≤ 90 * (2 * (Q : ℝ) ^ (-σ)) *
          Real.sqrt (48 * (Q : ℝ) * T ^ (1 / 3 : ℝ)) := by gcongr
    _ = (180 * Real.sqrt 48) *
          (((Q : ℝ) ^ (-σ) * (Q : ℝ) ^ (1 / 2 : ℝ)) *
            T ^ (1 / 6 : ℝ)) := by
      rw [hSqrtRewrite]
      ring
    _ = (180 * Real.sqrt 48) *
          ((Q : ℝ) ^ (1 / 2 - σ) * T ^ (1 / 6 : ℝ)) := by
      rw [← Real.rpow_add hQPos]
      congr 3
      ring
    _ = (180 * Real.sqrt 48) *
          T ^ ((1 / 2 - σ) / tau + 1 / 6) := by
      rw [hQPower, Real.rpow_add hTPos]

/-- Uniform physical side conditions for the complete source-block Weyl
estimate.  The factor eight in the quadratic condition is exactly what
absorbs the left displacement of the slab at the boundary `tau = 2`; the
cubic condition uses the fixed positive gap between `tauMax` and `3`. -/
theorem eventually_source_weyl_geometry
    {d tauMax : ℝ} (hTauMaxTwo : 2 ≤ tauMax)
    (hTauMaxThree : tauMax < 3) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧
      ∀ {T t tau : ℝ} {Q : ℕ}, T₀ ≤ T → 1 < Q → 2 ∣ Q →
        2 ≤ tau → tau ≤ tauMax → (Q : ℝ) ^ tau = T →
        T ^ d ≤ T / 2 → T - T ^ d ≤ t → t ≤ 2 * T + T ^ d →
        (((Q + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ 8 * t ∧
          t ≤ ((((Q / 2) + 1 : ℕ) : ℝ) ^ (3 : ℕ)) := by
  let rho : ℝ := 3 / tauMax - 1
  have hTauMaxPos : 0 < tauMax := by linarith
  have hRho : 0 < rho := by
    dsimp only [rho]
    rw [sub_pos, one_lt_div hTauMaxPos]
    exact hTauMaxThree
  have hTop := tendsto_rpow_atTop hRho
  have hEventually := (tendsto_atTop.1 hTop) 24
  rw [eventually_atTop] at hEventually
  obtain ⟨Tpow, hTpow⟩ := hEventually
  let T₀ := max 8 Tpow
  refine ⟨T₀, le_max_left _ _, ?_⟩
  intro T t tau Q hT hQ hEven hTauTwo hTauUpper hScale hDisp htLower htUpper
  have hTEight : 8 ≤ T := (le_max_left _ _).trans hT
  have hTPow : Tpow ≤ T := (le_max_right _ _).trans hT
  have hTOne : 1 ≤ T := by linarith
  have hTPos : 0 < T := by linarith
  have hTauPos : 0 < tau := by linarith
  have hQPos : (0 : ℝ) < Q := by positivity
  have hQOne : (1 : ℝ) ≤ Q := by exact_mod_cast hQ.le
  have htHalf : T / 2 ≤ t := by linarith
  have htThree : t ≤ 3 * T := by linarith
  have hQSquare : (Q : ℝ) ^ (2 : ℕ) ≤ T := by
    calc
      (Q : ℝ) ^ (2 : ℕ) = (Q : ℝ) ^ (2 : ℝ) := by
        exact (Real.rpow_natCast (Q : ℝ) 2).symm
      _ ≤ (Q : ℝ) ^ tau :=
        Real.rpow_le_rpow_of_exponent_le hQOne hTauTwo
      _ = T := hScale
  have hSucc : (((Q + 1 : ℕ) : ℝ)) ≤ 2 * Q := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have hQuadratic : (((Q + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ 8 * t := by
    calc
      (((Q + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ (2 * (Q : ℝ)) ^ (2 : ℕ) := by
        gcongr
      _ = 4 * (Q : ℝ) ^ (2 : ℕ) := by ring
      _ ≤ 4 * T := by gcongr
      _ ≤ 8 * t := by linarith
  have hInv : 3 / tauMax ≤ 3 / tau := by
    exact div_le_div_of_nonneg_left (by norm_num) hTauPos hTauUpper
  have hExp : rho ≤ (3 - tau) / tau := by
    dsimp only [rho]
    rw [sub_div]
    field_simp [hTauPos.ne']
    nlinarith [hInv]
  have hPowerSaving : 24 ≤ (Q : ℝ) ^ (3 - tau) := by
    calc
      (24 : ℝ) ≤ T ^ rho := hTpow T hTPow
      _ ≤ T ^ ((3 - tau) / tau) :=
        Real.rpow_le_rpow_of_exponent_le hTOne hExp
      _ = (Q : ℝ) ^ (3 - tau) := by
        rw [← hScale, ← Real.rpow_mul hQPos.le]
        congr 1
        field_simp [hTauPos.ne']
  have hQCube : 24 * T ≤ (Q : ℝ) ^ (3 : ℕ) := by
    calc
      24 * T = 24 * (Q : ℝ) ^ tau := by rw [hScale]
      _ ≤ (Q : ℝ) ^ (3 - tau) * (Q : ℝ) ^ tau := by
        exact mul_le_mul_of_nonneg_right hPowerSaving
          (Real.rpow_nonneg hQPos.le _)
      _ = (Q : ℝ) ^ (3 : ℕ) := by
        rw [← Real.rpow_add hQPos]
        convert Real.rpow_natCast (Q : ℝ) 3 using 1
        all_goals ring_nf
  have hHalfCast : ((Q / 2 : ℕ) : ℝ) = (Q : ℝ) / 2 := by
    have hTwice : 2 * (Q / 2) = Q := Nat.mul_div_cancel' hEven
    have hTwiceReal : (2 : ℝ) * (Q / 2 : ℕ) = Q := by exact_mod_cast hTwice
    linarith
  refine ⟨hQuadratic, ?_⟩
  calc
    t ≤ 3 * T := htThree
    _ ≤ ((Q : ℝ) / 2) ^ (3 : ℕ) := by
      rw [show ((Q : ℝ) / 2) ^ (3 : ℕ) = (Q : ℝ) ^ (3 : ℕ) / 8 by ring]
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
      nlinarith
    _ = ((Q / 2 : ℕ) : ℝ) ^ (3 : ℕ) := by rw [hHalfCast]
    _ ≤ (((Q / 2 + 1 : ℕ) : ℝ)) ^ (3 : ℕ) := by
      gcongr
      norm_num

/-- The complementary physical source-scale alternative is empty.  This
consumes a nonempty source family and its actual pointwise lower bound; the
`Nat.clog` loss is supplied explicitly and absorbed by the displayed
positive exponent budget. -/
theorem eventually_source_far_family_impossible
    {sigma d u q v Clog : ℝ}
    (hsigmaUpper : sigma < 1)
    (hq : 0 < q) (hTauMaxTwo : 2 ≤ 6 * sigma - 3 - q)
    (hBudget : u + v < q / 18) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧
      ∀ {T tau : ℝ} {Y A r : ℕ} (W : Finset ℝ), T₀ ≤ T →
        A = ⌊sharpZetaCutoff T⌋₊ → 0 < Y → 2 ≤ r →
        2 * (2 ^ r * Y) ≤ A →
        tau = typeILogarithmicScale T (2 ^ r * Y) →
        2 ≤ tau → tau < 6 * sigma - 3 - q →
        T ^ d ≤ T / 2 →
        W.Nonempty →
        (∀ t ∈ W, T - T ^ d ≤ t ∧ t ≤ 2 * T + T ^ d) →
        (((Nat.clog 2 A + 1 : ℕ) : ℝ) ≤ Clog * T ^ v) →
        (∀ t ∈ W,
          ((3 / 4) * (T ^ (-u) / 2)) /
              (Nat.clog 2 A + 1 : ℕ) ≤
            ‖typeISourceSmoothBlock Y A r sigma t‖) →
        False := by
  let tauMax : ℝ := 6 * sigma - 3 - q
  have hTauMaxTwo' : 2 ≤ tauMax := by simpa only [tauMax] using hTauMaxTwo
  have hTauMaxThree : tauMax < 3 := by dsimp only [tauMax]; linarith
  obtain ⟨Tgeo, hTgeo, hGeo⟩ :=
    eventually_source_weyl_geometry hTauMaxTwo' hTauMaxThree
  have hSaving : 0 < q / 18 - u - v := by linarith
  let Cw : ℝ := 180 * Real.sqrt 48
  have hCw : 0 < Cw := by dsimp only [Cw]; positivity
  have hTop := tendsto_rpow_atTop hSaving
  have hEventually := (tendsto_atTop.1 hTop)
    ((8 / 3 : ℝ) * Clog * Cw + 1)
  rw [eventually_atTop] at hEventually
  obtain ⟨Tconst, hTconst⟩ := hEventually
  let T₀ : ℝ := max Tgeo Tconst
  refine ⟨T₀, hTgeo.trans (le_max_left _ _), ?_⟩
  intro T tau Y A r W hT hA hY hr hInterior hTau hTauTwo hFar hDisp
    hW hRange hLog hLarge
  have hTGeo : Tgeo ≤ T := (le_max_left _ _).trans hT
  have hTEight : 8 ≤ T := hTgeo.trans hTGeo
  have hTConst : Tconst ≤ T := (le_max_right _ _).trans hT
  have hTOne : 1 ≤ T := by linarith
  have hTPos : 0 < T := by linarith
  have hTauPos : 0 < tau := by linarith
  have hTauUpper : tau ≤ tauMax := by dsimp only [tauMax]; linarith
  obtain ⟨t, ht⟩ := hW
  let Q : ℕ := 2 ^ r * Y
  have hQFour : 4 ≤ Q := by
    have hPow : 4 ≤ 2 ^ r := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hr
    dsimp only [Q]
    exact hPow.trans (Nat.le_mul_of_pos_right _ hY)
  have hQOne : 1 < Q := by omega
  have hEven : 2 ∣ Q := by
    dsimp only [Q]
    exact dvd_mul_of_dvd_left
      (dvd_pow (dvd_refl 2) (by omega : r ≠ 0)) Y
  have hScale : (Q : ℝ) ^ tau = T := by
    rw [hTau]
    simpa only [Q] using rpow_typeILogarithmicScale_eq hTPos hQOne
  have htLower : T / 2 ≤ t := by linarith [(hRange t ht).1]
  have htOne : 1 ≤ t := by linarith
  have htUpper : t ≤ 3 * T := by linarith [(hRange t ht).2]
  obtain ⟨hSquare, hCube⟩ := hGeo hTGeo hQOne hEven hTauTwo
    hTauUpper hScale hDisp (hRange t ht).1 (hRange t ht).2
  have hWeyl := norm_typeISourceSmoothBlock_le_physical_weyl
    hY hr hInterior (by linarith : 0 ≤ sigma) hsigmaUpper.le hTOne
    htOne htUpper hTauPos hScale hSquare hCube
  let F : ℝ := (1 / 2 - sigma) / tau + 1 / 6
  have hExp : F ≤ -q / 18 := by
    have hCore : F < -q / (6 * tau) := by
      dsimp only [F]
      rw [lt_div_iff₀ (mul_pos (by norm_num) hTauPos)]
      field_simp [hTauPos.ne']
      linarith
    have hUniform : -q / (6 * tau) ≤ -q / 18 := by
      have hDiv : q / 18 ≤ q / (6 * tau) := by
        exact div_le_div_of_nonneg_left hq.le (by positivity) (by linarith)
      simpa only [neg_div] using (neg_le_neg hDiv)
    exact hCore.le.trans hUniform
  have hPow : T ^ F ≤ T ^ (-q / 18) :=
    Real.rpow_le_rpow_of_exponent_le hTOne hExp
  have hNorm : ‖typeISourceSmoothBlock Y A r sigma t‖ ≤
      Cw * T ^ (-q / 18) := by
    exact hWeyl.trans (mul_le_mul_of_nonneg_left
      (by simpa only [F] using hPow) hCw.le)
  have hLogPos : (0 : ℝ) < ((Nat.clog 2 A + 1 : ℕ) : ℝ) := by positivity
  have hLower : (3 / 4 : ℝ) * (T ^ (-u) / 2) ≤
      ((Nat.clog 2 A + 1 : ℕ) : ℝ) *
        ‖typeISourceSmoothBlock Y A r sigma t‖ := by
    simpa only [mul_comm] using (div_le_iff₀ hLogPos).mp (hLarge t ht)
  have hLogNonneg : 0 ≤ Clog * T ^ v := hLogPos.le.trans hLog
  have hThreshold : (3 / 8 : ℝ) * T ^ (-u) ≤
      (Clog * Cw) * T ^ (v - q / 18) := by
    calc
      (3 / 8 : ℝ) * T ^ (-u) =
          (3 / 4) * (T ^ (-u) / 2) := by ring
      _ ≤ ((Nat.clog 2 A + 1 : ℕ) : ℝ) *
          ‖typeISourceSmoothBlock Y A r sigma t‖ := hLower
      _ ≤ (Clog * T ^ v) * (Cw * T ^ (-q / 18)) := by
        exact mul_le_mul hLog hNorm (norm_nonneg _) hLogNonneg
      _ = (Clog * Cw) * (T ^ v * T ^ (-q / 18)) := by ring
      _ = (Clog * Cw) * T ^ (v - q / 18) := by
        rw [← Real.rpow_add hTPos]
        ring_nf
  have hConstRaw := hTconst T hTConst
  change (8 / 3 : ℝ) * Clog * Cw + 1 ≤
    T ^ (q / 18 - u - v) at hConstRaw
  have hConst : (8 / 3 : ℝ) * Clog * Cw <
      T ^ (q / 18 - u - v) := (lt_add_one _).trans_le hConstRaw
  have hScaled := mul_lt_mul_of_pos_right hConst
    (Real.rpow_pos_of_pos hTPos (v - q / 18))
  have hIdentity : T ^ (q / 18 - u - v) * T ^ (v - q / 18) =
      T ^ (-u) := by
    rw [← Real.rpow_add hTPos]
    congr 1
    ring
  have hContradiction : (Clog * Cw) * T ^ (v - q / 18) <
      (3 / 8 : ℝ) * T ^ (-u) := by
    calc
      (Clog * Cw) * T ^ (v - q / 18) =
          (3 / 8 : ℝ) * (((8 / 3 : ℝ) * Clog * Cw) *
            T ^ (v - q / 18)) := by ring
      _ < (3 / 8 : ℝ) *
          (T ^ (q / 18 - u - v) * T ^ (v - q / 18)) := by
        exact mul_lt_mul_of_pos_left hScaled (by norm_num)
      _ = (3 / 8 : ℝ) * T ^ (-u) := by rw [hIdentity]
  linarith

set_option maxHeartbeats 1200000

/-- A genuinely large interior source block must lie on the stationary side
of the B-process margin.  This is proved from the sharp-support square-root
bound above; the margin is not added as a hypothesis to the final consumer. -/
theorem eventually_large_source_forces_complementary_margin
    {σ d u : ℝ} (hσOne : σ < 1)
    (hd : 0 < d) (hdOne : d < 1)
    (hdGap : d ≤ (σ - 1 / 2) / 1000)
    (huD : u ≤ d) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧
      ∀ (T t τ : ℝ) (Y A r : ℕ), T₀ ≤ T →
        A = ⌊sharpZetaCutoff T⌋₊ → 0 < Y → 2 ≤ r →
        2 * (2 ^ r * Y) ≤ A →
        T - T ^ d ≤ t → t ≤ 2 * T + T ^ d →
        T ^ d ≤ T / 2 →
        τ = typeILogarithmicScale T (2 ^ r * Y) →
        ((3 / 4) * (T ^ (-u) / 2)) /
            (Nat.clog 2 A + 1 : ℕ) ≤
          ‖typeISourceSmoothBlock Y A r σ t‖ →
        -100 * d ≤ τ / 2 - σ := by
  let a : ℝ := 2 * σ - 200 * d
  have haOne : 1 < a := by
    dsimp only [a]
    have hScaled : 200 * d ≤ (σ - 1 / 2) / 5 := by
      calc
        200 * d ≤ 200 * ((σ - 1 / 2) / 1000) := by gcongr
        _ = (σ - 1 / 2) / 5 := by ring
    linarith
  have haPos : 0 < a := zero_lt_one.trans haOne
  have haTwo : a < 2 := by dsimp only [a]; linarith
  let δ : ℝ := 2 / a - 1
  have hδ : 0 < δ := by
    dsimp only [δ]
    rw [sub_pos, one_lt_div haPos]
    exact haTwo
  have hPowTop := tendsto_rpow_atTop hδ
  have hEventuallyPow := (tendsto_atTop.1 hPowTop) 48
  rw [eventually_atTop] at hEventuallyPow
  obtain ⟨Tpow, hTpow⟩ := hEventuallyPow
  have hDecay : u + 1 / 2 < σ / a := by
    have hGapEq : σ / a - 1 / 2 = 100 * d / a := by
      field_simp [haPos.ne']
      dsimp only [a]
      ring
    have hFifty : 50 * d < 100 * d / a := by
      rw [lt_div_iff₀ haPos]
      have hMul := mul_lt_mul_of_pos_right haTwo
        (mul_pos (by norm_num : (0 : ℝ) < 50) hd)
      nlinarith
    have huFifty : u < 50 * d := huD.trans_lt (by nlinarith [hd])
    linarith
  have hRatioTop := tendsto_typeI_terminal_ratio (σ / a) (u + 1 / 2) hDecay
  let c : ℝ := 6 * (100 * Real.sqrt 3 + 36 * Real.pi) * 2 ^ σ
  have hc : 0 < c := by dsimp only [c]; positivity
  have hScaled := hRatioTop.const_mul c
  have hEventuallySmall := (tendsto_order.1 hScaled).2 (3 / 8 : ℝ) (by norm_num)
  rw [eventually_atTop] at hEventuallySmall
  obtain ⟨Tsmall, hTsmall⟩ := hEventuallySmall
  obtain ⟨Thalf, hThalf, hHalf⟩ := eventually_rpow_le_half_self d hdOne
  let T₀ : ℝ := max 8 (max Tpow (max Tsmall Thalf))
  refine ⟨T₀, le_max_left _ _, ?_⟩
  intro T t τ Y A r hT hA hY hr hUpper htLower htUpper hDisp hτ hLarge
  have hTEight : 8 ≤ T := (le_max_left _ _).trans hT
  have hRest : max Tpow (max Tsmall Thalf) ≤ T := (le_max_right _ _).trans hT
  have hTPow : Tpow ≤ T := (le_max_left _ _).trans hRest
  have hRest₁ : max Tsmall Thalf ≤ T := (le_max_right _ _).trans hRest
  have hTSmall : Tsmall ≤ T := (le_max_left _ _).trans hRest₁
  have hTHalf : Thalf ≤ T := (le_max_right _ _).trans hRest₁
  have hTPos : 0 < T := by linarith
  have hTOne : 1 ≤ T := by linarith
  by_contra hMargin
  have hτa : τ < a := by
    have : τ / 2 - σ < -100 * d := lt_of_not_ge hMargin
    dsimp only [a]
    linarith
  let Q : ℕ := 2 ^ r * Y
  let L : ℕ := Q / 2
  have hQFour : 4 ≤ Q := by
    dsimp only [Q]
    have hpow : 4 ≤ 2 ^ r := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hr
    calc
      4 = 4 * 1 := by omega
      _ ≤ 4 * Y := Nat.mul_le_mul_left 4 hY
      _ ≤ 2 ^ r * Y := Nat.mul_le_mul_right Y hpow
  have hQOne : 1 < Q := by omega
  have hQ : 0 < Q := by omega
  have hEven : 2 ∣ Q := by
    dsimp only [Q]
    exact dvd_mul_of_dvd_left
      (dvd_pow (dvd_refl 2) (by omega : r ≠ 0)) Y
  have hTwiceL : 2 * L = Q := by
    dsimp only [L]
    exact Nat.mul_div_cancel' hEven
  have hL : 0 < L := by omega
  have hScale : (Q : ℝ) ^ τ = T := by
    subst τ
    simpa only [Q] using rpow_typeILogarithmicScale_eq hTPos hQOne
  have hTa : T ≤ (Q : ℝ) ^ a := by
    rw [← hScale]
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hQOne.le) hτa.le
  have hRoot : T ^ (1 / a) ≤ (Q : ℝ) := by
    have hRaised := Real.rpow_le_rpow hTPos.le hTa
      (by positivity : 0 ≤ 1 / a)
    calc
      T ^ (1 / a) ≤ ((Q : ℝ) ^ a) ^ (1 / a) := hRaised
      _ = (Q : ℝ) := by
        rw [← Real.rpow_mul (by positivity)]
        field_simp [haPos.ne']
        exact Real.rpow_one (Q : ℝ)
  have hPowAt : 48 ≤ T ^ δ := hTpow T hTPow
  have hQSquare : 48 * T ≤ (Q : ℝ) ^ 2 := by
    have hSquare := pow_le_pow_left₀ (Real.rpow_nonneg hTPos.le _) hRoot 2
    have hPowerEq : (T ^ (1 / a)) ^ (2 : ℕ) = T ^ (2 / a) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hTPos.le]
      congr 1
      ring
    have hSplit : T ^ (2 / a) = T * T ^ δ := by
      rw [show 2 / a = 1 + δ by dsimp only [δ]; ring,
        Real.rpow_add hTPos, Real.rpow_one]
    rw [hPowerEq, hSplit] at hSquare
    nlinarith [mul_le_mul_of_nonneg_left hPowAt hTPos.le]
  have htHalf : T / 2 ≤ t := by linarith
  have htThree : t ≤ 3 * T := by linarith
  have htSq : t ≤ (L : ℝ) ^ 2 := by
    have hLReal : (L : ℝ) = (Q : ℝ) / 2 := by
      have hTwiceLReal : (2 : ℝ) * L = Q := by exact_mod_cast hTwiceL
      linarith
    rw [hLReal]
    nlinarith
  have hNorm := norm_typeISourceSmoothBlock_le_sqrt
    (Y := Y) (A := A) (r := r) (σ := σ) (t := t)
    hY hr (by linarith) (by linarith) (by simpa only [Q, L] using htSq)
  subst A
  let A : ℕ := ⌊sharpZetaCutoff T⌋₊
  have hCutNonneg : 0 ≤ sharpZetaCutoff T := by
    linarith [four_mul_lt_sharpZetaCutoff T]
  have hAUpper : (A : ℝ) ≤ 6 * T := by
    dsimp only [A]
    exact (Nat.floor_le hCutNonneg).trans
      (sharpZetaCutoff_le_six_mul (by linarith))
  have hQUpper : (Q : ℝ) ≤ 3 * T := by
    have hUpperReal : (2 : ℝ) * Q ≤ A := by exact_mod_cast hUpper
    linarith
  have hSqrt : Real.sqrt t ≤ Real.sqrt 3 * T ^ (1 / 2 : ℝ) := by
    calc
      Real.sqrt t ≤ Real.sqrt (3 * T) := Real.sqrt_le_sqrt htThree
      _ = Real.sqrt 3 * Real.sqrt T := by rw [Real.sqrt_mul (by norm_num)]
      _ = Real.sqrt 3 * T ^ (1 / 2 : ℝ) := by
        congr 1
        exact Real.sqrt_eq_rpow T
  have hRatio : (Q : ℝ) / t ≤ 6 := by
    have hQt : (Q : ℝ) ≤ 6 * t := by linarith only [hQUpper, htHalf]
    exact (div_le_iff₀ (by linarith only [htHalf, hTPos])).2 hQt
  have hSqrtOne : 1 ≤ T ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow hTOne (by norm_num)
  have hBracket :
      100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t ≤
        (100 * Real.sqrt 3 + 36 * Real.pi) * T ^ (1 / 2 : ℝ) := by
    have hRatioTerm : 6 * Real.pi * (Q : ℝ) / t ≤ 36 * Real.pi := by
      calc
        6 * Real.pi * (Q : ℝ) / t = 6 * Real.pi * ((Q : ℝ) / t) := by ring
        _ ≤ 6 * Real.pi * 6 := by gcongr
        _ = 36 * Real.pi := by ring
    calc
      100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t ≤
          100 * (Real.sqrt 3 * T ^ (1 / 2 : ℝ)) + 36 * Real.pi := by
        gcongr
      _ ≤ 100 * (Real.sqrt 3 * T ^ (1 / 2 : ℝ)) +
          36 * Real.pi * T ^ (1 / 2 : ℝ) := by
        have hPiTerm : 36 * Real.pi ≤ 36 * Real.pi * T ^ (1 / 2 : ℝ) := by
          calc
            36 * Real.pi = 36 * Real.pi * 1 := by ring
            _ ≤ 36 * Real.pi * T ^ (1 / 2 : ℝ) :=
              mul_le_mul_of_nonneg_left hSqrtOne (by positivity)
        exact add_le_add_right hPiTerm _
      _ = (100 * Real.sqrt 3 + 36 * Real.pi) * T ^ (1 / 2 : ℝ) := by ring
  have hWeightQ : (((L + 1 : ℕ) : ℝ)) ^ (-σ) ≤
      ((Q : ℝ) / 2) ^ (-σ) := by
    apply Real.rpow_le_rpow_of_nonpos
    · positivity
    · norm_num only [Nat.cast_add, Nat.cast_one]
      have hLReal : (L : ℝ) = (Q : ℝ) / 2 := by
        have hTwiceLReal : (2 : ℝ) * L = Q := by exact_mod_cast hTwiceL
        linarith
      linarith
    · linarith
  have hWeightT : ((Q : ℝ) / 2) ^ (-σ) ≤
      2 ^ σ * T ^ (-σ / a) := by
    have hQNeg : (Q : ℝ) ^ (-σ) ≤ T ^ (-σ / a) := by
      have hRaised := Real.rpow_le_rpow_of_nonpos
        (Real.rpow_pos_of_pos hTPos (1 / a))
        hRoot (by linarith : -σ ≤ 0)
      have hEq : (T ^ (1 / a)) ^ (-σ) = T ^ (-σ / a) := by
        rw [← Real.rpow_mul hTPos.le]
        congr 1
        ring
      simpa only [hEq] using hRaised
    rw [Real.div_rpow (by positivity : (0 : ℝ) ≤ Q)
      (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      (Q : ℝ) ^ (-σ) / (2 ^ σ)⁻¹ = 2 ^ σ * (Q : ℝ) ^ (-σ) := by
        field_simp
      _ ≤ 2 ^ σ * T ^ (-σ / a) :=
        mul_le_mul_of_nonneg_left hQNeg (Real.rpow_nonneg (by norm_num) _)
  have hNormBound : ‖typeISourceSmoothBlock Y A r σ t‖ ≤
      3 * (100 * Real.sqrt 3 + 36 * Real.pi) * 2 ^ σ *
        T ^ (1 / 2 - σ / a) := by
    calc
      _ ≤ 3 * (((L + 1 : ℕ) : ℝ) ^ (-σ)) *
          (100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t) := by
        simpa only [Q, L, A] using hNorm
      _ ≤ 3 * (2 ^ σ * T ^ (-σ / a)) *
          ((100 * Real.sqrt 3 + 36 * Real.pi) * T ^ (1 / 2 : ℝ)) := by
        calc
          3 * (((L + 1 : ℕ) : ℝ) ^ (-σ)) *
              (100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t) =
            3 * ((((L + 1 : ℕ) : ℝ) ^ (-σ)) *
              (100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t)) := by ring
          _ ≤ 3 * ((2 ^ σ * T ^ (-σ / a)) *
              ((100 * Real.sqrt 3 + 36 * Real.pi) * T ^ (1 / 2 : ℝ))) := by
            have hSourceBracketNonneg :
                0 ≤ 100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t := by
              have htPos : 0 < t := by linarith only [htHalf, hTPos]
              positivity
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul (hWeightQ.trans hWeightT) hBracket
                hSourceBracketNonneg (by positivity)) (by norm_num)
          _ = _ := by ring
      _ = 3 * (100 * Real.sqrt 3 + 36 * Real.pi) * 2 ^ σ *
          T ^ (1 / 2 - σ / a) := by
        calc
          3 * (2 ^ σ * T ^ (-σ / a)) *
              ((100 * Real.sqrt 3 + 36 * Real.pi) * T ^ (1 / 2 : ℝ)) =
            3 * (100 * Real.sqrt 3 + 36 * Real.pi) * 2 ^ σ *
              (T ^ (-σ / a) * T ^ (1 / 2 : ℝ)) := by ring
          _ = _ := by
            rw [← Real.rpow_add hTPos]
            congr 1
            ring_nf
  have hAOne : 1 < A := by
    dsimp only [A]
    apply lt_of_lt_of_le (by omega : 1 < (2 : ℕ))
    apply Nat.le_floor
    exact (show (2 : ℝ) ≤ 4 * T by nlinarith).trans
      (four_mul_lt_sharpZetaCutoff T).le
  have hClog := sharp_cutoff_clog_le_log_majorant T hTEight
  have hkBound : ((Nat.clog 2 A + 1 : ℕ) : ℝ) ≤
      2 * (1 + (Real.log 6 + Real.log T) / Real.log 2) := by
    have hEnvelopeOne : 1 ≤
        1 + (Real.log 6 + Real.log T) / Real.log 2 := by
      have hLogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hLogSix : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
      have hLogT : 0 ≤ Real.log T := Real.log_nonneg hTOne
      have : 0 ≤ (Real.log 6 + Real.log T) / Real.log 2 :=
        div_nonneg (add_nonneg hLogSix hLogT) hLogTwo.le
      linarith
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have hSmallAt :
      c * (1 + (Real.log 6 + Real.log T) / Real.log 2) *
          T ^ (u + 1 / 2 - σ / a) < 3 / 8 := by
    simpa only [mul_assoc] using hTsmall T hTSmall
  have hPowerSplit : T ^ (u + 1 / 2 - σ / a) * T ^ (-u) =
      T ^ (1 / 2 - σ / a) := by
    rw [← Real.rpow_add hTPos]
    congr 1
    ring
  have hNumerator :
      ((Nat.clog 2 A + 1 : ℕ) : ℝ) *
          (3 * (100 * Real.sqrt 3 + 36 * Real.pi) * 2 ^ σ *
            T ^ (1 / 2 - σ / a)) <
        (3 / 4) * (T ^ (-u) / 2) := by
    have hMul := mul_lt_mul_of_pos_right hSmallAt
      (Real.rpow_pos_of_pos hTPos (-u))
    calc
      _ ≤ (2 * (1 + (Real.log 6 + Real.log T) / Real.log 2)) *
          (3 * (100 * Real.sqrt 3 + 36 * Real.pi) * 2 ^ σ *
            T ^ (1 / 2 - σ / a)) := by gcongr
      _ = (c * (1 + (Real.log 6 + Real.log T) / Real.log 2) *
            T ^ (u + 1 / 2 - σ / a)) * T ^ (-u) := by
        rw [show T ^ (1 / 2 - σ / a) =
            T ^ (u + 1 / 2 - σ / a) * T ^ (-u) from hPowerSplit.symm]
        dsimp only [c]
        ring
      _ < (3 / 8) * T ^ (-u) := hMul
      _ = (3 / 4) * (T ^ (-u) / 2) := by ring
  have hkPos : (0 : ℝ) < (Nat.clog 2 A + 1 : ℕ) := by positivity
  have hThresholdLt : ‖typeISourceSmoothBlock Y A r σ t‖ <
      ((3 / 4) * (T ^ (-u) / 2)) / (Nat.clog 2 A + 1 : ℕ) := by
    rw [lt_div_iff₀ hkPos]
    calc
      ‖typeISourceSmoothBlock Y A r σ t‖ * (Nat.clog 2 A + 1 : ℕ) =
          (Nat.clog 2 A + 1 : ℕ) * ‖typeISourceSmoothBlock Y A r σ t‖ := by ring
      _ ≤ (Nat.clog 2 A + 1 : ℕ) *
          (3 * (100 * Real.sqrt 3 + 36 * Real.pi) * 2 ^ σ *
            T ^ (1 / 2 - σ / a)) :=
        mul_le_mul_of_nonneg_left hNormBound hkPos.le
      _ < _ := hNumerator
  exact (not_lt_of_ge (by simpa only [A] using hLarge)) hThresholdLt

/-- Budgeted form of the signed B-process extraction.  The choice of `R`
uses `L¹+1`, so it is valid even if the fixed Mellin mass vanishes; the
strict source gap and the normalization of the reflected polynomial are
then elementary consequences of `R ≥ 2`. -/
theorem exists_signed_shift_large_normalized_reflected_wide_of_budget
    {Y A r M : ℕ} {σ t V H K E : ℝ}
    (hY : 0 < Y)
    (hLower : (((Y + 1 : ℕ) : ℝ)) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2))
    (hUpper : (2 * (2 ^ r * Y : ℕ) : ℕ) ≤ A)
    (hσ : 0 ≤ σ) (hM : 1 < M)
    (hV : 0 < V) (hH : 0 ≤ H) (hK : 0 < K)
    (hLarge : V ≤ ‖typeISourceSmoothBlock Y A r σ t‖)
    (hZero :
      ‖typeISourceNormalizationScalar σ t (2 ^ r * Y : ℕ) *
        (((2 ^ r * Y : ℕ) : ℂ) *
          typeINormalizedFourier σ t 0)‖ ≤ V / 8)
    (hFar :
      ‖typeISourceNormalizationScalar σ t (2 ^ r * Y : ℕ) *
        typeINormalizedFarTail σ t (2 ^ r * Y) M‖ ≤ V / 8)
    (hKernelNeg : ∀ u ∈ Set.Icc (-H) H,
      ‖typeIPowerReflectionIntegral σ (t + u)
        (((2 ^ r * Y : ℕ) : ℝ) / 2)
        (2 * M * (2 ^ r * Y : ℕ))‖ ≤ K)
    (hKernelPos : ∀ u ∈ Set.Icc (-H) H,
      ‖typeIPowerReflectionIntegral σ (-t + u)
        (((2 ^ r * Y : ℕ) : ℝ) / 2)
        (2 * M * (2 ^ r * Y : ℕ))‖ ≤ K)
    (hTailNeg :
      ‖∫ u : ℝ in (Set.Icc (-H) H)ᶜ,
        typeIReflectedMellinPolynomial σ t
            ((2 ^ r * Y : ℕ) : ℝ) M u *
          typeIDyadicCutoffMellin u *
            typeIPowerReflectionIntegral σ (t + u)
              (((2 ^ r * Y : ℕ) : ℝ) / 2)
              (2 * M * (2 ^ r * Y : ℕ))‖ ≤ E)
    (hTailPos :
      ‖∫ u : ℝ in (Set.Icc (-H) H)ᶜ,
        typeIReflectedMellinPolynomial σ (-t)
            ((2 ^ r * Y : ℕ) : ℝ) M u *
          typeIDyadicCutoffMellin u *
            typeIPowerReflectionIntegral σ (-t + u)
              (((2 ^ r * Y : ℕ) : ℝ) / 2)
              (2 * M * (2 ^ r * Y : ℕ))‖ ≤ E)
    (hTailBudget : E ≤ Real.pi * V / 8)
    (hR : 2 ≤ (Real.pi * V) /
      (8 * ((2 ^ r * Y : ℕ) : ℝ) * K *
        (typeIDyadicCutoffMellinL1 + 1))) :
    let R := (Real.pi * V) /
      (8 * ((2 ^ r * Y : ℕ) : ℝ) * K *
        (typeIDyadicCutoffMellinL1 + 1))
    let S := R / (2 * (M : ℝ) ^ σ)
    (∃ u ∈ Set.Icc (-H) H,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff σ M) (-(t + u))‖) ∨
    (∃ u ∈ Set.Icc (-H) H,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff σ M) (t - u)‖) := by
  dsimp only
  let Q : ℕ := 2 ^ r * Y
  let R : ℝ := (Real.pi * V) /
    (8 * (Q : ℝ) * K * (typeIDyadicCutoffMellinL1 + 1))
  let S : ℝ := R / (2 * (M : ℝ) ^ σ)
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hMass : 0 ≤ typeIDyadicCutoffMellinL1 :=
    typeIDyadicCutoffMellinL1_nonneg
  have hDen : 0 < 8 * (Q : ℝ) * K *
      (typeIDyadicCutoffMellinL1 + 1) := by positivity
  have hRPos : 0 < R := by dsimp only [R]; positivity
  have hCentral : (Q : ℝ) * R * K * typeIDyadicCutoffMellinL1 ≤
      Real.pi * V / 8 := by
    dsimp only [R]
    rw [div_eq_mul_inv]
    have hFrac : typeIDyadicCutoffMellinL1 /
        (typeIDyadicCutoffMellinL1 + 1) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    have hQV : 0 ≤ Real.pi * V / 8 := by positivity
    field_simp [hDen.ne']
    nlinarith [mul_le_mul_of_nonneg_left hFrac (mul_nonneg Real.pi_pos.le hV.le)]
  have hGap : (Q : ℝ) * R * K * typeIDyadicCutoffMellinL1 + E <
      Real.pi * V / 2 := by
    have hPiV : 0 < Real.pi * V := mul_pos Real.pi_pos hV
    nlinarith
  have hNormalize : S + (M : ℝ) ^ (-σ) ≤ R / (M : ℝ) ^ σ := by
    have hMPow : 0 < (M : ℝ) ^ σ := by positivity
    have hInv : (M : ℝ) ^ (-σ) = 1 / (M : ℝ) ^ σ := by
      simpa only [one_div] using
        (Real.rpow_neg (by positivity : (0 : ℝ) ≤ M) σ)
    have hRAt : 2 ≤ R := by simpa only [R, Q] using hR
    rw [hInv]
    dsimp only [S]
    have hRewrite : R / (2 * (M : ℝ) ^ σ) + 1 / (M : ℝ) ^ σ =
        (R / 2 + 1) / (M : ℝ) ^ σ := by
      field_simp [hMPow.ne']
    rw [hRewrite]
    exact (div_le_div_iff_of_pos_right hMPow).2 (by nlinarith)
  simpa only [Q, R, S] using
    exists_signed_shift_large_normalized_reflected_wide
      hY hLower hUpper hσ hM hV.le hH hRPos.le hLarge hZero hFar
      hKernelNeg hKernelPos hTailNeg hTailPos hGap hNormalize

/-- The terminal three-sum majorant is eventually smaller than the exact
classified-source threshold.  The statement keeps the additional `clog + 1`
selection loss, rather than silently identifying it with the detector's
original `clog`. -/
theorem eventually_terminal_source_majorant_lt_threshold
    {σ u : ℝ} (hσ : 1 / 2 < σ) (hu : u < σ - 1 / 2) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ (T t : ℝ) (Q L : ℕ), T₀ ≤ T →
      T / 2 ≤ L → (Q : ℝ) ≤ 24 * T →
      T / 2 ≤ t → t ≤ 3 * T →
      3 * (((L + 1 : ℕ) : ℝ) ^ (-σ)) *
          (100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t) <
        ((3 / 4) * (T ^ (-u) / 2)) /
          (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) := by
  have hDecay : u + 1 / 2 < σ := by linarith
  have hTendsto := tendsto_typeI_terminal_ratio σ (u + 1 / 2) hDecay
  let c : ℝ := 6 * (100 * Real.sqrt 3 + 288 * Real.pi) * 2 ^ σ
  have hc : 0 < c := by dsimp only [c]; positivity
  have hScaled := hTendsto.const_mul c
  have hEventually := (tendsto_order.1 hScaled).2 (3 / 8 : ℝ) (by norm_num)
  rw [eventually_atTop] at hEventually
  obtain ⟨Tscale, hTscale⟩ := hEventually
  let T₀ := max 8 Tscale
  refine ⟨T₀, le_max_left _ _, ?_⟩
  intro T t Q L hT hTL hQT htLower htUpper
  have hTEight : 8 ≤ T := (le_max_left _ _).trans hT
  have hTscale' : Tscale ≤ T := (le_max_right _ _).trans hT
  have hTPos : 0 < T := by linarith
  have htPos : 0 < t := by linarith
  have hLPos : (0 : ℝ) < L + 1 := by positivity
  have hWeight : (((L + 1 : ℕ) : ℝ)) ^ (-σ) ≤ (T / 2) ^ (-σ) := by
    apply Real.rpow_le_rpow_of_nonpos
    · positivity
    · norm_num only [Nat.cast_add, Nat.cast_one]
      linarith
    · linarith
  have hSqrt : Real.sqrt t ≤ Real.sqrt 3 * T ^ (1 / 2 : ℝ) := by
    calc
      Real.sqrt t ≤ Real.sqrt (3 * T) := Real.sqrt_le_sqrt htUpper
      _ = Real.sqrt 3 * Real.sqrt T := by rw [Real.sqrt_mul (by norm_num)]
      _ = Real.sqrt 3 * T ^ (1 / 2 : ℝ) := by
        congr 1
        exact Real.sqrt_eq_rpow T
  have hRatio : (Q : ℝ) / t ≤ 48 := by
    rw [div_le_iff₀ htPos]
    nlinarith
  have hSqrtOne : 1 ≤ T ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hRatioTerm : 6 * Real.pi * (Q : ℝ) / t ≤ 6 * Real.pi * 48 := by
    calc
      6 * Real.pi * (Q : ℝ) / t = 6 * Real.pi * ((Q : ℝ) / t) := by ring
      _ ≤ 6 * Real.pi * 48 := mul_le_mul_of_nonneg_left hRatio
        (mul_nonneg (by norm_num) Real.pi_pos.le)
  have hBracket :
      100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t ≤
        (100 * Real.sqrt 3 + 288 * Real.pi) * T ^ (1 / 2 : ℝ) := by
    calc
      100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t ≤
          100 * (Real.sqrt 3 * T ^ (1 / 2 : ℝ)) +
            6 * Real.pi * 48 := add_le_add (mul_le_mul_of_nonneg_left hSqrt
              (by norm_num)) hRatioTerm
      _ ≤ 100 * (Real.sqrt 3 * T ^ (1 / 2 : ℝ)) +
            (6 * Real.pi * 48) * T ^ (1 / 2 : ℝ) := by
        have hCoeff : 0 ≤ 6 * Real.pi * 48 := by positivity
        have hScaledRatio := mul_le_mul_of_nonneg_left hSqrtOne hCoeff
        have hRatioLift : 6 * Real.pi * 48 ≤
            (6 * Real.pi * 48) * T ^ (1 / 2 : ℝ) := by
          simpa only [mul_one] using hScaledRatio
        linarith
      _ = (100 * Real.sqrt 3 + 288 * Real.pi) * T ^ (1 / 2 : ℝ) := by ring
  have hDivPow : (T / 2) ^ (-σ) = 2 ^ σ * T ^ (-σ) := by
    rw [Real.div_rpow hTPos.le (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
  have hPowCombine : T ^ (-σ) * T ^ (1 / 2 : ℝ) =
      T ^ (1 / 2 - σ) := by
    rw [← Real.rpow_add hTPos]
    congr 1
    ring
  have hMajorant :
      3 * (((L + 1 : ℕ) : ℝ) ^ (-σ)) *
          (100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t) ≤
        3 * (100 * Real.sqrt 3 + 288 * Real.pi) * 2 ^ σ *
          T ^ (1 / 2 - σ) := by
    calc
      _ ≤ 3 * (T / 2) ^ (-σ) *
          ((100 * Real.sqrt 3 + 288 * Real.pi) * T ^ (1 / 2 : ℝ)) := by
        gcongr
      _ = 3 * (100 * Real.sqrt 3 + 288 * Real.pi) * 2 ^ σ *
          T ^ (1 / 2 - σ) := by
        rw [hDivPow, ← hPowCombine]
        ring
  let A := ⌊sharpZetaCutoff T⌋₊
  have hAOne : 1 < A := by
    dsimp only [A]
    apply lt_of_lt_of_le (by omega : 1 < (2 : ℕ))
    apply Nat.le_floor
    exact (show (2 : ℝ) ≤ 4 * T by nlinarith).trans
      (four_mul_lt_sharpZetaCutoff T).le
  have hkPos : 0 < (Nat.clog 2 A + 1 : ℕ) := by omega
  have hkRealPos : (0 : ℝ) < (Nat.clog 2 A + 1 : ℕ) := by exact_mod_cast hkPos
  have hClog := sharp_cutoff_clog_le_log_majorant T hTEight
  have hEnvelopeOne : 1 ≤
      1 + (Real.log 6 + Real.log T) / Real.log 2 := by
    have hLogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    have hLogSix : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
    have hLogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hFrac : 0 ≤ (Real.log 6 + Real.log T) / Real.log 2 := by positivity
    linarith
  have hkBound : (Nat.clog 2 A + 1 : ℕ) ≤
      2 * (1 + (Real.log 6 + Real.log T) / Real.log 2) := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have hRatioAt := hTscale T hTscale'
  have hRatioSmall :
      c * (1 + (Real.log 6 + Real.log T) / Real.log 2) *
          T ^ (u + 1 / 2 - σ) < 3 / 8 := by
    simpa only [mul_assoc] using hRatioAt
  have hPowSplit : T ^ (u + 1 / 2 - σ) * T ^ (-u) =
      T ^ (1 / 2 - σ) := by
    rw [← Real.rpow_add hTPos]
    congr 1
    ring
  have hNumerator :
      (Nat.clog 2 A + 1 : ℕ) *
          (3 * (100 * Real.sqrt 3 + 288 * Real.pi) * 2 ^ σ *
            T ^ (1 / 2 - σ)) <
        (3 / 4) * (T ^ (-u) / 2) := by
    have hMul := mul_lt_mul_of_pos_right hRatioSmall
      (Real.rpow_pos_of_pos hTPos (-u))
    calc
      (Nat.clog 2 A + 1 : ℕ) *
          (3 * (100 * Real.sqrt 3 + 288 * Real.pi) * 2 ^ σ *
            T ^ (1 / 2 - σ)) ≤
        (2 * (1 + (Real.log 6 + Real.log T) / Real.log 2)) *
          (3 * (100 * Real.sqrt 3 + 288 * Real.pi) * 2 ^ σ *
            T ^ (1 / 2 - σ)) := by gcongr
      _ = (c * (1 + (Real.log 6 + Real.log T) / Real.log 2) *
            T ^ (u + 1 / 2 - σ)) * T ^ (-u) := by
        calc
          _ = c * (1 + (Real.log 6 + Real.log T) / Real.log 2) *
              T ^ (1 / 2 - σ) := by dsimp only [c]; ring
          _ = c * (1 + (Real.log 6 + Real.log T) / Real.log 2) *
              (T ^ (u + 1 / 2 - σ) * T ^ (-u)) := by rw [hPowSplit]
          _ = _ := by ring
      _ < (3 / 8) * T ^ (-u) := hMul
      _ = (3 / 4) * (T ^ (-u) / 2) := by ring
  change 3 * (((L + 1 : ℕ) : ℝ) ^ (-σ)) *
      (100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t) <
    ((3 / 4) * (T ^ (-u) / 2)) / (Nat.clog 2 A + 1 : ℕ)
  rw [lt_div_iff₀ hkRealPos]
  exact (mul_le_mul_of_nonneg_right hMajorant (Nat.cast_nonneg _)).trans_lt
    (by simpa only [mul_comm] using hNumerator)

/-- The upper-edge alternative returned by the actual common-source
selection is empty for all sufficiently large heights.  Its scale comparison
is derived from a nonzero dyadic coefficient of that same source block. -/
theorem eventually_no_terminal_classified_source
    {σ d u : ℝ} (hσ : 1 / 2 < σ) (hu : u < σ - 1 / 2) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ (T : ℝ) (Y A r : ℕ) (W : Finset ℝ), T₀ ≤ T →
      A = ⌊sharpZetaCutoff T⌋₊ →
      0 < Y → 2 ≤ r → A < 2 * (2 ^ r * Y) →
      W.Nonempty → IsSeparated 1 W →
      (∀ t ∈ W,
        ((3 / 4) * (T ^ (-u) / 2)) / (Nat.clog 2 A + 1 : ℕ) ≤
          ‖typeISourceSmoothBlock Y A r σ t‖) →
      (∀ t ∈ W, T - T ^ d ≤ t ∧ t ≤ 2 * T + T ^ d) →
      T ^ d ≤ T / 2 → False := by
  obtain ⟨Tterminal, hTterminal, hTerminalSmall⟩ :=
    eventually_terminal_source_majorant_lt_threshold hσ hu
  let T₀ := max Tterminal 12
  have hEightTwelve : (8 : ℝ) ≤ 12 := by norm_num
  refine ⟨T₀, hEightTwelve.trans (le_max_right _ _), ?_⟩
  intro T Y A r W hT hA hY hr hTerminal hW hSep hLarge hRange hDisp
  have hTTerminal : Tterminal ≤ T := (le_max_left _ _).trans hT
  have hTTwelve : 12 ≤ T := (le_max_right _ _).trans hT
  have hTEight : 8 ≤ T := by linarith
  have hTPos : 0 < T := by linarith
  subst A
  let A : ℕ := ⌊sharpZetaCutoff T⌋₊
  let Q : ℕ := 2 ^ r * Y
  let L : ℕ := Q / 2
  have hAOne : 1 < A := by
    dsimp only [A]
    apply lt_of_lt_of_le (by omega : 1 < (2 : ℕ))
    apply Nat.le_floor
    exact (show (2 : ℝ) ≤ 4 * T by nlinarith).trans
      (four_mul_lt_sharpZetaCutoff T).le
  have hV : 0 < ((3 / 4) * (T ^ (-u) / 2)) /
      (Nat.clog 2 A + 1 : ℕ) := by positivity
  obtain ⟨j, hj, W', _hWsub, _hSep', _hCard, _hLarge', _hPUpper, hQFourP⟩ :=
    extract_normalized_source_dyadic_block W hY hAOne hV hW hSep hLarge
  have hPA : 2 ^ j ≤ A := by
    have hjClog : j < Nat.clog 2 (A + 1) := Finset.mem_range.mp hj
    have hpow : 2 ^ j < A + 1 := Nat.pow_lt_of_lt_clog hjClog
    omega
  have hCutNonneg : 0 ≤ sharpZetaCutoff T := by
    linarith [four_mul_lt_sharpZetaCutoff T]
  have hAUpper : (A : ℝ) ≤ 6 * T := by
    dsimp only [A]
    exact (Nat.floor_le hCutNonneg).trans
      (sharpZetaCutoff_le_six_mul (by linarith))
  have hQUpperNat : Q < 4 * A := by
    dsimp only [Q] at hQFourP ⊢
    exact hQFourP.trans_le (Nat.mul_le_mul_left 4 hPA)
  have hQUpper : (Q : ℝ) ≤ 24 * T := by
    calc
      (Q : ℝ) ≤ 4 * A := by exact_mod_cast hQUpperNat.le
      _ ≤ 24 * T := by nlinarith
  have hEven : 2 ∣ Q := by
    dsimp only [Q]
    exact dvd_mul_of_dvd_left (dvd_pow (dvd_refl 2) (by omega : r ≠ 0)) Y
  have hTwiceL : 2 * L = Q := by
    dsimp only [L]
    exact Nat.mul_div_cancel' hEven
  obtain ⟨t, htW⟩ := hW
  have hCutLt : sharpZetaCutoff T < (A : ℝ) + 1 := by
    dsimp only [A]
    exact_mod_cast Nat.lt_floor_add_one (sharpZetaCutoff T)
  have hFourTA : 4 * T < (A : ℝ) + 1 :=
    (four_mul_lt_sharpZetaCutoff T).trans hCutLt
  have hAQT : (A : ℝ) + 1 ≤ 2 * Q := by
    have hNat : A + 1 ≤ 2 * Q := by
      dsimp only [Q] at hTerminal ⊢
      omega
    exact_mod_cast hNat
  have hTL : T / 2 ≤ (L : ℝ) := by
    have hQL : (Q : ℝ) = 2 * L := by exact_mod_cast hTwiceL.symm
    rw [hQL] at hAQT
    nlinarith
  have htLower : T / 2 ≤ t := by
    have := (hRange t htW).1
    linarith
  have htUpper : t ≤ 3 * T := by
    have := (hRange t htW).2
    linarith
  have hLThree : (3 : ℝ) ≤ L := by nlinarith
  have htSq : t ≤ (L : ℝ) ^ 2 := by
    have : 3 * T ≤ (L : ℝ) ^ 2 := by nlinarith [sq_nonneg ((L : ℝ) - T / 2)]
    exact htUpper.trans this
  have hBound := norm_typeISourceSmoothBlock_terminal_le
    (Y := Y) (A := A) (r := r) (σ := σ) (t := t) hY hr
    (by simpa only [Q] using hTerminal) (by linarith) (by linarith) (by
      simpa only [L, Q] using htSq)
  have hSmall := hTerminalSmall T t Q L hTTerminal hTL hQUpper
    htLower htUpper
  have hLargeAt := hLarge t htW
  have hThresholdEq :
      ((3 / 4) * (T ^ (-u) / 2)) /
          (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) =
        ((3 / 4) * (T ^ (-u) / 2)) / (Nat.clog 2 A + 1 : ℕ) := by
    rfl
  rw [hThresholdEq] at hSmall
  have hBound' : ‖typeISourceSmoothBlock Y A r σ t‖ ≤
      3 * (((L + 1 : ℕ) : ℝ) ^ (-σ)) *
        (100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t) := by
    simpa only [L, Q] using hBound
  linarith

/-- The two bottom source blocks selected from the long tail have a physical
logarithmic scale comparable with `1 / d`.  Both comparisons retain the
literal natural floor and the factor `2 ^ r`; no real surrogate for the
source length is introduced. -/
theorem eventually_lower_source_logarithmic_scale_bounds
    (d : ℝ) (hd : 0 < d) :
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ (T : ℝ) (r : ℕ), T₀ ≤ T → r < 2 →
      let Y := ⌊T ^ d⌋₊
      let N := 2 ^ r * Y
      1 < N ∧ 1 / (2 * d) ≤ typeILogarithmicScale T N ∧
        typeILogarithmicScale T N ≤ 2 / d := by
  obtain ⟨Tupper, hTupper, hUpper⟩ :=
    eventually_typeI_logarithmic_scale_upper d hd
  let T₀ : ℝ := max Tupper ((2 : ℝ) ^ (1 / d))
  refine ⟨T₀, hTupper.trans (le_max_left _ _), ?_⟩
  intro T r hT hr
  dsimp only
  have hTUpper : Tupper ≤ T := (le_max_left _ _).trans hT
  have hTConst : (2 : ℝ) ^ (1 / d) ≤ T :=
    (le_max_right _ _).trans hT
  have hTTwo : 2 ≤ T := hTupper.trans hTUpper
  have hTPos : 0 < T := by linarith
  let Y := ⌊T ^ d⌋₊
  let N := 2 ^ r * Y
  have hUpperAt := hUpper T r hTUpper
  dsimp only at hUpperAt
  rcases hUpperAt with ⟨hNOne, hTauUpper⟩
  have hPowTwo : 2 ≤ T ^ d := by
    have hRaised := Real.rpow_le_rpow
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      hTConst hd.le
    have hCancel : ((2 : ℝ) ^ (1 / d)) ^ d = 2 := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have hExp : 1 / d * d = 1 := by field_simp [hd.ne']
      rw [hExp, Real.rpow_one]
    simpa only [hCancel] using hRaised
  have hYUpper : (Y : ℝ) ≤ T ^ d := by
    dsimp only [Y]
    exact Nat.floor_le (Real.rpow_nonneg hTPos.le _)
  have hPowR : 2 ^ r ≤ 2 := by
    have hrCases : r = 0 ∨ r = 1 := by omega
    rcases hrCases with rfl | rfl <;> norm_num
  have hNUpper : (N : ℝ) ≤ T ^ (2 * d) := by
    have hFirst : (N : ℝ) ≤ 2 * T ^ d := by
      calc
        (N : ℝ) = (2 ^ r : ℕ) * (Y : ℝ) := by
          dsimp only [N]
          push_cast
          rfl
        _ ≤ 2 * (Y : ℝ) := by
          gcongr
          exact_mod_cast hPowR
        _ ≤ 2 * T ^ d := by gcongr
    have hSecond : 2 * T ^ d ≤ T ^ d * T ^ d := by
      nlinarith [Real.rpow_nonneg hTPos.le d]
    calc
      (N : ℝ) ≤ 2 * T ^ d := hFirst
      _ ≤ T ^ d * T ^ d := hSecond
      _ = T ^ (2 * d) := by
        rw [← Real.rpow_add hTPos]
        congr 1
        ring
  have hNPos : (0 : ℝ) < N := by exact_mod_cast (lt_trans Nat.zero_lt_one hNOne)
  have hLowerPhysical : (N : ℝ) ^ (1 / (2 * d)) ≤ T := by
    have hExp : 0 ≤ 1 / (2 * d) := by positivity
    have hRaised := Real.rpow_le_rpow hNPos.le hNUpper hExp
    calc
      (N : ℝ) ^ (1 / (2 * d)) ≤
          (T ^ (2 * d)) ^ (1 / (2 * d)) := hRaised
      _ = T := by
        rw [← Real.rpow_mul hTPos.le]
        have hCancel : 2 * d * (1 / (2 * d)) = 1 := by
          field_simp [hd.ne']
        rw [hCancel, Real.rpow_one]
  have hTauLower : 1 / (2 * d) ≤ typeILogarithmicScale T N :=
    (Real.le_logb_iff_rpow_le (by exact_mod_cast hNOne) hTPos).mpr
      hLowerPhysical
  exact ⟨hNOne, hTauLower, hTauUpper⟩

/-- The power growth of a dyadic interval extracted from the actual lower
source blocks absorbs both the detector `clog` and the small `T^(d^4)`
threshold loss.  This is the quantitative bridge that allows the existing
Type-II powered-threshold envelope to be reused without changing the source
polynomial. -/
theorem eventually_lower_source_threshold_scale_growth
    (d : ℝ) (hd : 0 < d) (hdOne : d < 1) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧
      ∀ (T : ℝ) (Y A Q P : ℕ), T₀ ≤ T →
        Y = ⌊T ^ (d ^ 2)⌋₊ → A = ⌊sharpZetaCutoff T⌋₊ →
        Y ≤ Q → Q < 4 * P →
        6 * (Nat.clog 2 A + 1 : ℕ) * T ^ (d ^ 4) ≤
          C₀ * ((2 * P : ℕ) : ℝ) ^ d := by
  let γ : ℝ := (d ^ 3 - d ^ 4) / 2
  have hγ : 0 < γ := by
    dsimp only [γ]
    nlinarith [mul_pos (pow_pos hd 3) (sub_pos.mpr hdOne)]
  obtain ⟨Tfloor, hTfloor, hFloor⟩ :=
    eventually_half_rpow_le_natFloor (d ^ 2) (sq_pos_of_pos hd)
  have hLogEventually := eventually_log_nat_power_le_rpow 1 γ hγ
  rw [eventually_atTop] at hLogEventually
  obtain ⟨Tlog, hTlog⟩ := hLogEventually
  let cLog : ℝ := 2 + 2 / Real.log 2
  let C₀ : ℝ := max 1 (6 * cLog * 4 ^ d)
  let T₀ : ℝ := max 8 (max Tfloor Tlog)
  refine ⟨C₀, le_max_left _ _, T₀, le_max_left _ _, ?_⟩
  intro T Y A Q P hT rfl rfl hYQ hQP
  have hTEight : 8 ≤ T := (le_max_left _ _).trans hT
  have hRest : max Tfloor Tlog ≤ T := (le_max_right _ _).trans hT
  have hTFloor : Tfloor ≤ T := (le_max_left _ _).trans hRest
  have hTLog : Tlog ≤ T := (le_max_right _ _).trans hRest
  have hTPos : 0 < T := by linarith
  have hTOne : 1 ≤ T := by linarith
  have hLogPower : Real.log T ≤ T ^ γ := by
    have hAt := hTlog T hTLog
    simpa only [pow_one] using hAt
  have hLogSix : Real.log 6 ≤ Real.log T :=
    Real.log_le_log (by norm_num) (by linarith)
  have hPowOne : 1 ≤ T ^ γ := Real.one_le_rpow hTOne hγ.le
  have hLogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hClogRaw := sharp_cutoff_clog_le_log_majorant T hTEight
  have hClog : (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) ≤
      cLog * T ^ γ := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    calc
      (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ : ℝ) + 1 ≤
          (1 + (Real.log 6 + Real.log T) / Real.log 2) + 1 := by
        linarith
      _ ≤ 2 + (2 * T ^ γ) / Real.log 2 := by
        have hNumerator : Real.log 6 + Real.log T ≤ 2 * T ^ γ := by
          linarith
        have hFrac : (Real.log 6 + Real.log T) / Real.log 2 ≤
            (2 * T ^ γ) / Real.log 2 :=
          div_le_div_of_nonneg_right hNumerator hLogTwo.le
        linarith
      _ = 2 + (2 / Real.log 2) * T ^ γ := by ring
      _ ≤ 2 * T ^ γ + (2 / Real.log 2) * T ^ γ := by
        linarith
      _ = (2 + 2 / Real.log 2) * T ^ γ := by ring
      _ = cLog * T ^ γ := by rfl
  have hYLower : T ^ (d ^ 2) / 2 ≤
      (⌊T ^ (d ^ 2)⌋₊ : ℝ) := (hFloor T hTFloor).1
  have hPPos : 0 < P := by omega
  have hPSource : T ^ (d ^ 2) / 8 ≤ (P : ℝ) := by
    have hYFourP : ⌊T ^ (d ^ 2)⌋₊ < 4 * P := hYQ.trans_lt hQP
    have hYFourPReal : (⌊T ^ (d ^ 2)⌋₊ : ℝ) ≤ 4 * P := by
      exact_mod_cast hYFourP.le
    nlinarith
  have hTwoP : T ^ (d ^ 2) / 4 ≤ ((2 * P : ℕ) : ℝ) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  have hRaised : (T ^ (d ^ 2) / 4) ^ d ≤
      ((2 * P : ℕ) : ℝ) ^ d :=
    Real.rpow_le_rpow (by positivity) hTwoP hd.le
  have hLeftPower : (T ^ (d ^ 2) / 4) ^ d =
      (4 : ℝ) ^ (-d) * T ^ (d ^ 3) := by
    rw [Real.div_rpow (Real.rpow_nonneg hTPos.le _)
      (by norm_num : (0 : ℝ) ≤ 4), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4),
      ← Real.rpow_mul hTPos.le]
    ring_nf
  have hScaleLower : T ^ (d ^ 3) ≤
      4 ^ d * ((2 * P : ℕ) : ℝ) ^ d := by
    have hFourPos : 0 < (4 : ℝ) ^ d := Real.rpow_pos_of_pos (by norm_num) _
    have hFourCancel : (4 : ℝ) ^ d * (4 : ℝ) ^ (-d) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 4)]
      norm_num
    rw [hLeftPower] at hRaised
    calc
      T ^ (d ^ 3) = 4 ^ d * (4 ^ (-d) * T ^ (d ^ 3)) := by
        rw [← mul_assoc, hFourCancel, one_mul]
      _ ≤ 4 ^ d * ((2 * P : ℕ) : ℝ) ^ d :=
        mul_le_mul_of_nonneg_left hRaised hFourPos.le
  have hExponent : d ^ 4 + γ ≤ d ^ 3 := by
    dsimp only [γ]
    nlinarith [mul_pos (pow_pos hd 3) (sub_pos.mpr hdOne)]
  have hTExp : T ^ (d ^ 4 + γ) ≤ T ^ (d ^ 3) :=
    Real.rpow_le_rpow_of_exponent_le hTOne hExponent
  have hClogTerm :
      6 * (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) * T ^ (d ^ 4) ≤
        6 * cLog * T ^ (d ^ 3) := by
    calc
      6 * (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) * T ^ (d ^ 4) ≤
          6 * (cLog * T ^ γ) * T ^ (d ^ 4) := by
        gcongr
      _ = 6 * cLog * T ^ (d ^ 4 + γ) := by
        rw [Real.rpow_add hTPos]
        ring
      _ ≤ 6 * cLog * T ^ (d ^ 3) := by gcongr
  calc
    6 * (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) * T ^ (d ^ 4) ≤
        6 * cLog * T ^ (d ^ 3) := hClogTerm
    _ ≤ (6 * cLog * 4 ^ d) * ((2 * P : ℕ) : ℝ) ^ d := by
      have hcLog : 0 ≤ 6 * cLog := by dsimp only [cLog]; positivity
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hScaleLower hcLog
    _ ≤ C₀ * ((2 * P : ℕ) : ℝ) ^ d := by
      gcongr
      exact le_max_right _ _

/-- The literal threshold of a localized source block dominates the standard
powered threshold after its extra detector logarithm has been absorbed by
`eventually_lower_source_threshold_scale_growth`.  The comparison preserves
the exact dyadic relation `P < 2N`; it does not identify the extracted block
with the physical source scale. -/
theorem lower_source_threshold_ge_typeII_model
    {C₀ u η σ T : ℝ} {A N P : ℕ}
    (hC₀ : 0 < C₀) (hσ : 0 ≤ σ)
    (hT : 0 < T) (hA : 1 < A) (hP : 0 < P)
    (hPN : P < 2 * N)
    (hGrowth :
      (3 / 2 : ℝ) * (Nat.clog 2 A + 1 : ℕ) * T ^ u * 4 ^ σ ≤
        C₀ * ((2 * P : ℕ) : ℝ) ^ η) :
    let V₀ := ((3 / 4 : ℝ) * (T ^ (-u) / 2)) /
      (Nat.clog 2 A + 1 : ℕ)
    let L := ((((N : ℝ) / 2) ^ σ) * V₀) / Nat.clog 2 (A + 1)
    let L₀ := (9 / 16 : ℝ) / Nat.clog 2 (A + 1)
    let D := C₀ * ((2 * P : ℕ) : ℝ) ^ η * (P : ℝ) ^ (-σ)
    L₀ / D ≤ L := by
  dsimp only
  have hPReal : (0 : ℝ) < P := by exact_mod_cast hP
  have hN : 0 < N := by omega
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hAClog : (0 : ℝ) < Nat.clog 2 (A + 1) := by
    exact_mod_cast Nat.clog_pos Nat.one_lt_two (by omega : 1 < A + 1)
  have hLossClog : (0 : ℝ) < Nat.clog 2 A + 1 := by positivity
  have hTwoP : (0 : ℝ) < ((2 * P : ℕ) : ℝ) := by positivity
  have hD : 0 < C₀ * ((2 * P : ℕ) : ℝ) ^ η * (P : ℝ) ^ (-σ) := by
    positivity
  have hPNReal : (P : ℝ) / 4 ≤ (N : ℝ) / 2 := by
    have : (P : ℝ) ≤ 2 * N := by exact_mod_cast hPN.le
    linarith
  have hPowPN : (P : ℝ) ^ σ ≤
      4 ^ σ * ((N : ℝ) / 2) ^ σ := by
    have hRaised := Real.rpow_le_rpow (by positivity) hPNReal hσ
    have hIdentity : (P : ℝ) ^ σ =
        4 ^ σ * ((P : ℝ) / 4) ^ σ := by
      rw [Real.div_rpow hPReal.le (by norm_num : (0 : ℝ) ≤ 4)]
      field_simp [(Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) σ).ne']
    rw [hIdentity]
    exact mul_le_mul_of_nonneg_left hRaised (Real.rpow_nonneg (by norm_num) _)
  have hCore :
      (3 / 2 : ℝ) * (Nat.clog 2 A + 1 : ℕ) * T ^ u * (P : ℝ) ^ σ ≤
        (C₀ * ((2 * P : ℕ) : ℝ) ^ η) * ((N : ℝ) / 2) ^ σ := by
    calc
      (3 / 2 : ℝ) * (Nat.clog 2 A + 1 : ℕ) * T ^ u * (P : ℝ) ^ σ ≤
          ((3 / 2 : ℝ) * (Nat.clog 2 A + 1 : ℕ) * T ^ u) *
            (4 ^ σ * ((N : ℝ) / 2) ^ σ) := by gcongr
      _ = ((3 / 2 : ℝ) * (Nat.clog 2 A + 1 : ℕ) * T ^ u * 4 ^ σ) *
            ((N : ℝ) / 2) ^ σ := by ring
      _ ≤ (C₀ * ((2 * P : ℕ) : ℝ) ^ η) * ((N : ℝ) / 2) ^ σ := by
        gcongr
  have hTpow : 0 < T ^ u := Real.rpow_pos_of_pos hT _
  have hTPowInv : T ^ (-u) = (T ^ u)⁻¹ := Real.rpow_neg hT.le u
  rw [hTPowInv]
  field_simp [hC₀.ne', hTwoP.ne', hTpow.ne', hPReal.ne', hAClog.ne',
    hLossClog.ne']
  have hPcancel : (P : ℝ) ^ σ * (P : ℝ) ^ (-σ) = 1 := by
    rw [← Real.rpow_add hPReal]
    norm_num
  have hScaled :
      3 * (Nat.clog 2 A + 1 : ℕ) * T ^ u ≤
        2 * (C₀ * ((2 * P : ℕ) : ℝ) ^ η * ((N : ℝ) / 2) ^ σ) *
          (P : ℝ) ^ (-σ) := by
    calc
      3 * (Nat.clog 2 A + 1 : ℕ) * T ^ u =
          2 * ((3 / 2 : ℝ) * (Nat.clog 2 A + 1 : ℕ) * T ^ u *
            (P : ℝ) ^ σ) * (P : ℝ) ^ (-σ) := by
        calc
          3 * (Nat.clog 2 A + 1 : ℕ) * T ^ u =
              3 * (Nat.clog 2 A + 1 : ℕ) * T ^ u * 1 := by ring
          _ = 3 * (Nat.clog 2 A + 1 : ℕ) * T ^ u *
              ((P : ℝ) ^ σ * (P : ℝ) ^ (-σ)) := by rw [hPcancel]
          _ = _ := by ring
      _ ≤ 2 * (C₀ * ((2 * P : ℕ) : ℝ) ^ η * ((N : ℝ) / 2) ^ σ) *
          (P : ℝ) ^ (-σ) := by gcongr
  nlinarith

/-- The two literal logarithmic losses from common-source selection and
source-block localization cost an arbitrarily small power of the height.
Both `Nat.clog` arguments are the actual sharp natural cutoff. -/
theorem eventually_source_selection_log_product_le
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) *
          (Nat.clog 2 (⌊sharpZetaCutoff T⌋₊ + 1) : ℝ) ≤ C * T ^ η := by
  have hLogEventually := eventually_log_nat_power_le_rpow 2 η hη
  rw [eventually_atTop] at hLogEventually
  obtain ⟨Tlog, hTlog⟩ := hLogEventually
  let c : ℝ := 2 + 2 / Real.log 2
  let C : ℝ := c ^ (2 : ℕ)
  let T₀ : ℝ := max 8 Tlog
  refine ⟨C, by dsimp only [C, c]; positivity, T₀, le_max_left _ _, ?_⟩
  intro T hT
  have hTEight : 8 ≤ T := (le_max_left _ _).trans hT
  have hTLog : Tlog ≤ T := (le_max_right _ _).trans hT
  have hTPos : 0 < T := by linarith
  have hLogOne : 1 ≤ Real.log T := by
    have hExp : Real.exp 1 ≤ T := by
      calc Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
           _ ≤ 8 := by norm_num
           _ ≤ T := hTEight
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hExp
  have hLogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let A := ⌊sharpZetaCutoff T⌋₊
  have hCutNonneg : 0 ≤ sharpZetaCutoff T := by
    linarith [four_mul_lt_sharpZetaCutoff T]
  have hAUpper : (A : ℝ) ≤ 6 * T := by
    dsimp only [A]
    exact (Nat.floor_le hCutNonneg).trans
      (sharpZetaCutoff_le_six_mul (by linarith))
  have hAOne : 1 ≤ A := by
    dsimp only [A]
    apply (Nat.one_le_floor_iff _).mpr
    exact (show (1 : ℝ) ≤ 4 * T by linarith).trans
      (four_mul_lt_sharpZetaCutoff T).le
  have hALog : Real.log (A + 1 : ℕ) ≤ 2 * Real.log T := by
    have hASeven : ((A + 1 : ℕ) : ℝ) ≤ 7 * T := by
      norm_num only [Nat.cast_add, Nat.cast_one]
      nlinarith
    have hLogMono := Real.log_le_log (by positivity : (0 : ℝ) < (A + 1 : ℕ))
      hASeven
    rw [Real.log_mul (by norm_num : (7 : ℝ) ≠ 0) hTPos.ne'] at hLogMono
    have hLogSeven : Real.log 7 ≤ Real.log T :=
      Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hClogA := sharp_cutoff_clog_le_log_majorant T hTEight
  have hFirst : ((Nat.clog 2 A + 1 : ℕ) : ℝ) ≤ c * Real.log T := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    have hLogSix : Real.log 6 ≤ Real.log T :=
      Real.log_le_log (by norm_num) (by linarith)
    calc
      (Nat.clog 2 A : ℝ) + 1 ≤
          (1 + (Real.log 6 + Real.log T) / Real.log 2) + 1 := by
        linarith
      _ ≤ (2 + 2 / Real.log 2) * Real.log T := by
        have hFrac : (Real.log 6 + Real.log T) / Real.log 2 ≤
            (2 * Real.log T) / Real.log 2 :=
          div_le_div_of_nonneg_right (by linarith) hLogTwo.le
        calc
          _ ≤ 2 + (2 * Real.log T) / Real.log 2 := by linarith
          _ = 2 + (2 / Real.log 2) * Real.log T := by ring
          _ ≤ 2 * Real.log T + (2 / Real.log 2) * Real.log T := by
            linarith
          _ = _ := by ring
      _ = c * Real.log T := by rfl
  have hSecond : (Nat.clog 2 (A + 1) : ℝ) ≤ c * Real.log T := by
    have hRaw := natCast_clog_two_le_one_add_log (A + 1) (by omega)
    calc
      (Nat.clog 2 (A + 1) : ℝ) ≤
          1 + Real.log (A + 1 : ℕ) / Real.log 2 := hRaw
      _ ≤ 1 + (2 * Real.log T) / Real.log 2 := by
        gcongr
      _ ≤ (2 + 2 / Real.log 2) * Real.log T := by
        calc
          _ = 1 + (2 / Real.log 2) * Real.log T := by ring
          _ ≤ 2 * Real.log T + (2 / Real.log 2) * Real.log T := by
            linarith
          _ = _ := by ring
      _ = c * Real.log T := by rfl
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  calc
    ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) *
        (Nat.clog 2 (⌊sharpZetaCutoff T⌋₊ + 1) : ℝ) ≤
      (c * Real.log T) * (c * Real.log T) := by
        simpa only [A] using mul_le_mul hFirst hSecond (by positivity)
          (by positivity)
    _ = C * (Real.log T) ^ (2 : ℕ) := by dsimp only [C]; ring
    _ ≤ C * T ^ η := by
      gcongr
      exact hTlog T hTLog

/-- Replacing the height by `7T` in a powered normalization loss costs only
one bounded-power constant.  This is the exact comparison needed because the
literal source cover uses `A + 1`, while the sharp cutoff only gives
`A + 1 ≤ 7T`. -/
theorem classicalTypeIIPowerLoss_seven_mul_le
    {A e T : ℝ} {k Q B : ℕ}
    (hA : 0 ≤ A) (hT : 8 ≤ T) (hkB : k ≤ B) :
    classicalTypeIIPowerLoss A e (7 * T) k Q ≤
      classicalTypeIIPowerLoss ((2 : ℝ) ^ B * A) e T k Q := by
  have hTPos : 0 < T := by linarith
  have hLogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hLogSeven : Real.log 7 ≤ Real.log T :=
    Real.log_le_log (by norm_num) (by linarith)
  have hLogMul : Real.log (7 * T) ≤ 2 * Real.log T := by
    rw [Real.log_mul (by norm_num : (7 : ℝ) ≠ 0) hTPos.ne']
    linarith
  have hFour : 4 * Real.log (7 * T) ≤ 2 * (4 * Real.log T) := by
    linarith
  have hFourNonneg : 0 ≤ 4 * Real.log (7 * T) := by
    have : 1 ≤ 7 * T := by nlinarith
    exact mul_nonneg (by norm_num) (Real.log_nonneg this)
  have hPow : (4 * Real.log (7 * T)) ^ k ≤
      (2 : ℝ) ^ B * (4 * Real.log T) ^ k := by
    calc
      (4 * Real.log (7 * T)) ^ k ≤
          (2 * (4 * Real.log T)) ^ k :=
        pow_le_pow_left₀ hFourNonneg hFour k
      _ = (2 : ℝ) ^ k * (4 * Real.log T) ^ k := by rw [mul_pow]
      _ ≤ (2 : ℝ) ^ B * (4 * Real.log T) ^ k := by
        gcongr
        norm_num
  unfold classicalTypeIIPowerLoss
  have hScale : 0 ≤ (((2 : ℝ) ^ k) * Q) ^ (2 * e) := by positivity
  have hkNonneg : (0 : ℝ) ≤ k := by positivity
  calc
    A * (((2 : ℝ) ^ k) * Q) ^ (2 * e) * k *
          (4 * Real.log (7 * T)) ^ k ≤
        A * (((2 : ℝ) ^ k) * Q) ^ (2 * e) * k *
          ((2 : ℝ) ^ B * (4 * Real.log T) ^ k) := by gcongr
    _ = ((2 : ℝ) ^ B * A) *
          (((2 : ℝ) ^ k) * Q) ^ (2 * e) * k *
            (4 * Real.log T) ^ k := by ring

/-- Sharp-cutoff specialization of the generic powered-threshold envelope.
All uses of `A + 1`, the natural floor, and the change from `T` to `7T` are
proved here, so downstream source consumers can use the ordinary physical
height in their epsilon budget. -/
theorem source_powered_threshold_loss_le_envelope
    {C₀ C e σ T : ℝ} {A N k B : ℕ}
    (hC₀ : 1 ≤ C₀) (hC : 1 ≤ C)
    (hσOne : σ ≤ 1) (hT : 8 ≤ T)
    (hA : A = ⌊sharpZetaCutoff T⌋₊)
    (hN : 0 < N) (hk : 0 < k) (hkB : k ≤ B) :
    let L := (9 / 16 : ℝ) / Nat.clog 2 (A + 1)
    let D := C₀ * (2 * N : ℝ) ^ e * (N : ℝ) ^ (-σ)
    let aLog := max 1
      (((16 / 9 : ℝ) * (1 + (Real.log 2)⁻¹)) / 4)
    let Aenv := (2 : ℝ) ^ B *
      ((2 : ℝ) ^ B * C₀ ^ B * C * aLog ^ B)
    typeIIPoweredThresholdLoss C L D e σ N k ≤
      1 + classicalTypeIIPowerLoss Aenv e T k (N ^ k) := by
  dsimp only
  subst A
  let A : ℕ := ⌊sharpZetaCutoff T⌋₊
  let aLog : ℝ := max 1
    (((16 / 9 : ℝ) * (1 + (Real.log 2)⁻¹)) / 4)
  let A₀ : ℝ := (2 : ℝ) ^ B * C₀ ^ B * C * aLog ^ B
  let Aenv : ℝ := (2 : ℝ) ^ B * A₀
  have hTPos : 0 < T := by linarith
  have hAOne : 1 < A := by
    dsimp only [A]
    apply lt_of_lt_of_le (by omega : 1 < (2 : ℕ))
    apply Nat.le_floor
    exact (show (2 : ℝ) ≤ 4 * T by nlinarith).trans
      (four_mul_lt_sharpZetaCutoff T).le
  have hCutNonneg : 0 ≤ sharpZetaCutoff T := by
    linarith [four_mul_lt_sharpZetaCutoff T]
  have hAUpper : (A : ℝ) ≤ 6 * T := by
    dsimp only [A]
    exact (Nat.floor_le hCutNonneg).trans
      (sharpZetaCutoff_le_six_mul (by linarith))
  have hASeven : (((A + 1 : ℕ) : ℝ)) ≤ 7 * T := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith
  have hExp : Real.exp 1 ≤ 7 * T := by
    calc
      Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
      _ ≤ 7 * T := by nlinarith
  have hGeneric := typeII_powered_threshold_loss_le_envelope
    (C₀ := C₀) (C := C) (e := e) (dY := 1) (σ := σ)
    (T := 7 * T) (Y := A + 1) (N := N) (k := k)
    hC₀ hC (by norm_num) hσOne hExp (by omega) (by simpa using hASeven)
    hN hk hkB
  dsimp only at hGeneric
  have hA₀ : 0 ≤ A₀ := by dsimp only [A₀, aLog]; positivity
  have hCompare := classicalTypeIIPowerLoss_seven_mul_le
    (A := A₀) (e := e) (T := T) (k := k) (Q := N ^ k) (B := B)
    hA₀ hT hkB
  simpa only [Aenv] using
    hGeneric.trans (add_le_add_right hCompare 1)

set_option maxHeartbeats 1200000

/-- Endpoint consumer for either of the two literal bottom blocks selected
from the source-smooth decomposition.  The proof chooses the natural power
from the physical scale, performs both real finite extractions, and returns
to the multiplicity-weighted zero count. -/
theorem actual_lower_source_family_endpoint_consumer
    {σ τ₀ : ℝ} (hσLower : 1 / 2 < σ) (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
        let d := classicalEndpointLossParameter σ τ₀ (ε / 100)
        let Y := ⌊T ^ (d ^ 2)⌋₊
        let A := ⌊sharpZetaCutoff T⌋₊
        ∀ r : ℕ, r < 2 → ∀ W : Finset ℝ,
          W.Nonempty → IsSeparated 1 W → InBaseInterval (3 * T) W →
          (∀ t ∈ W,
            ((3 / 4) * (T ^ (-d ^ 4) / 2)) /
                (Nat.clog 2 A + 1 : ℕ) ≤
              ‖typeISourceSmoothBlock Y A r σ t‖) →
          zeroCountRect σ 1 T (2 * T) ≤
            (4 * Nat.clog 2 A *
              ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T)) *
                (Nat.clog 2 A + 1) * W.card →
          (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
            C * T ^ ε * T ^ (3 * (1 - σ) / τ₀) := by
  intro ε hε
  have hσ : 0 < σ := by linarith
  let εs : ℝ := ε / 100
  let d := classicalEndpointLossParameter σ τ₀ εs
  let s : ℝ := d ^ 2
  let u : ℝ := d ^ 4
  let U : ℝ := 4 / s
  let B : ℕ := ⌈U / τ₀⌉₊
  have hεs : 0 < εs := by dsimp only [εs]; positivity
  have hdSpec := classicalEndpointLossParameter_spec
    hσLower hσUpper hcert.tau0_pos hεs
  dsimp only at hdSpec
  rcases hdSpec with ⟨hd, hdEpsSmall, hdEpsTauSmall, _hdReflected, _hdHalfGap,
    _hdUpperGap, _hdSigma, hdSmall, _hdHalf, hdOne, _hdSigmaStrict⟩
  have hs : 0 < s := by dsimp only [s]; positivity
  have hu : 0 < u := by dsimp only [u]; positivity
  have hU : 0 < U := by dsimp only [U]; positivity
  have hB : 0 < B := by
    dsimp only [B]
    exact Nat.ceil_pos.mpr (div_pos hU hcert.tau0_pos)
  have hdOneStrict : d < 1 := by
    have hDen : 1 < 1000 * (1 + τ₀) := by nlinarith [hcert.tau0_pos]
    have hInv : 1 / (1000 * (1 + τ₀)) < (1 : ℝ) := by
      simpa only [one_div] using inv_lt_one_of_one_lt₀ hDen
    exact hdSmall.trans_lt hInv
  have hdEps : d ≤ ε / 100000 := by
    dsimp only [εs] at hdEpsSmall
    nlinarith
  have hdEpsTau : d ≤ ε * τ₀ / 100000 := by
    dsimp only [εs] at hdEpsTauSmall
    nlinarith
  obtain ⟨Cpow, hCpow, K, hK, hPowered⟩ :=
    powered_unit_block_large_values_bound_bounded_uniform B d hd
  obtain ⟨Cg, hCg, Tgrowth, hTgrowth, hGrowth⟩ :=
    eventually_lower_source_threshold_scale_growth d hd hdOneStrict
  let C₀ : ℝ := Cg * 4 ^ σ
  have hC₀ : 1 ≤ C₀ := by
    have hFour : 1 ≤ (4 : ℝ) ^ σ :=
      Real.one_le_rpow (by norm_num) hσ.le
    dsimp only [C₀]
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ Cg * 4 ^ σ := mul_le_mul hCg hFour (by norm_num) (by linarith)
  let aLog : ℝ := max 1
    (((16 / 9 : ℝ) * (1 + (Real.log 2)⁻¹)) / 4)
  let Aenv : ℝ := (2 : ℝ) ^ B *
    ((2 : ℝ) ^ B * C₀ ^ B * Cpow * aLog ^ B)
  have hAenv : 0 ≤ Aenv := by dsimp only [Aenv, aLog]; positivity
  obtain ⟨Closs, hCloss, Tloss, hTloss, hLoss⟩ :=
    eventually_endpoint_loss_bundle_le Aenv K d d τ₀ (ε / 4) B
      hAenv hK.le hd hd hcert.tau0_pos (by positivity) hB
      (by nlinarith [hdEps]) (by nlinarith [hdEpsTau])
  obtain ⟨Clog, hClog, Tlog, hTlog, hLogs⟩ :=
    eventually_source_selection_log_product_le (ε / 4) (by positivity)
  obtain ⟨Tscale, hTscale, hScale⟩ :=
    eventually_lower_source_logarithmic_scale_bounds s hs
  have hPowTop := tendsto_rpow_atTop hs
  have hEventuallySixteen := (tendsto_atTop.1 hPowTop) 16
  rw [eventually_atTop] at hEventuallySixteen
  obtain ⟨Tsixteen, hTsixteen⟩ := hEventuallySixteen
  obtain ⟨Twindow, hTwindow, hWindow⟩ :=
    eventually_dyadic_power_scale_in_endpoint_window hcert.tau0_pos hU
  let T₀ : ℝ := max Tloss
    (max Tlog (max Tscale (max Tsixteen (max Twindow Tgrowth))))
  let C : ℝ := Closs * Clog
  refine ⟨C, by dsimp only [C]; positivity, T₀,
    hTloss.trans (le_max_left _ _), ?_⟩
  intro T hT
  dsimp only
  intro r hr W hW hSep hBase hLarge hCount
  have hTLoss : Tloss ≤ T := (le_max_left _ _).trans hT
  have hRest : max Tlog (max Tscale (max Tsixteen (max Twindow Tgrowth))) ≤ T :=
    (le_max_right _ _).trans hT
  have hTLog : Tlog ≤ T := (le_max_left _ _).trans hRest
  have hRest₁ : max Tscale (max Tsixteen (max Twindow Tgrowth)) ≤ T :=
    (le_max_right _ _).trans hRest
  have hTScale : Tscale ≤ T := (le_max_left _ _).trans hRest₁
  have hRest₂ : max Tsixteen (max Twindow Tgrowth) ≤ T :=
    (le_max_right _ _).trans hRest₁
  have hTSixteen : Tsixteen ≤ T := (le_max_left _ _).trans hRest₂
  have hRest₃ : max Twindow Tgrowth ≤ T := (le_max_right _ _).trans hRest₂
  have hTWindow : Twindow ≤ T := (le_max_left _ _).trans hRest₃
  have hTGrowth : Tgrowth ≤ T := (le_max_right _ _).trans hRest₃
  have hTEight : 8 ≤ T := hTloss.trans hTLoss
  have hTPos : 0 < T := by linarith
  have hTOne : 1 ≤ T := by linarith
  let Y : ℕ := ⌊T ^ s⌋₊
  let A : ℕ := ⌊sharpZetaCutoff T⌋₊
  let N : ℕ := 2 ^ r * Y
  have hScaleAt := hScale T r hTScale hr
  dsimp only at hScaleAt
  rcases hScaleAt with ⟨hNOne, hTauLower, hTauUpper⟩
  have hN : 0 < N := lt_trans Nat.zero_lt_one hNOne
  have hTauMargin : 8 * τ₀ ≤ typeILogarithmicScale T N := by
    have hTauSmallProduct : τ₀ * s ≤ 1 / 1000 := by
      have hdTau : τ₀ * d ≤ 1 / 1000 := by
        have hRatio : τ₀ / (1 + τ₀) ≤ 1 := by
          rw [div_le_one (by linarith [hcert.tau0_pos] : 0 < 1 + τ₀)]
          linarith
        have hMul := mul_le_mul_of_nonneg_left hdSmall hcert.tau0_pos.le
        calc
          τ₀ * d ≤ τ₀ * (1 / (1000 * (1 + τ₀))) := hMul
          _ = (1 / 1000 : ℝ) * (τ₀ / (1 + τ₀)) := by
            field_simp [show (1 + τ₀) ≠ 0 by nlinarith [hcert.tau0_pos]]
          _ ≤ 1 / 1000 := by nlinarith
      dsimp only [s]
      calc
        τ₀ * d ^ 2 = (τ₀ * d) * d := by ring
        _ ≤ (1 / 1000 : ℝ) * d :=
          mul_le_mul_of_nonneg_right hdTau hd.le
        _ ≤ 1 / 1000 := by nlinarith
    have hCore : 8 * τ₀ ≤ 1 / (2 * s) := by
      rw [le_div_iff₀ (by positivity : 0 < 2 * s)]
      nlinarith
    exact hCore.trans hTauLower
  have hAOne : 1 < A := by
    dsimp only [A]
    apply lt_of_lt_of_le (by omega : 1 < (2 : ℕ))
    apply Nat.le_floor
    exact (show (2 : ℝ) ≤ 4 * T by nlinarith).trans
      (four_mul_lt_sharpZetaCutoff T).le
  have hY : 0 < Y := by
    dsimp only [Y, s]
    apply Nat.floor_pos.mpr
    have hTOneStrict : 1 < T := by linarith only [hTEight]
    exact (Real.one_lt_rpow hTOneStrict hs).le
  let V₀ : ℝ := ((3 / 4 : ℝ) * (T ^ (-u) / 2)) /
    (Nat.clog 2 A + 1 : ℕ)
  have hV₀ : 0 < V₀ := by dsimp only [V₀]; positivity
  obtain ⟨j, hj, W₀, hW₀sub, hSep₀, hCard₀, hLarge₀,
      hPUpper, hPLower⟩ :=
    extract_normalized_source_dyadic_block W hY hAOne hV₀ hW hSep
      (by simpa only [V₀, u, s, Y, A] using hLarge)
  let P : ℕ := 2 ^ j
  have hN16 : 16 ≤ N := by
    have hPowSixteen : (16 : ℝ) ≤ T ^ s := hTsixteen T hTSixteen
    have hY16 : 16 ≤ Y := by
      dsimp only [Y]
      exact Nat.le_floor hPowSixteen
    dsimp only [N]
    exact hY16.trans (Nat.le_mul_of_pos_left Y (pow_pos (by omega) r))
  have hUHalf : 0 < U / 2 := by positivity
  have hTauUpperHalf : typeILogarithmicScale T N ≤ U / 2 := by
    dsimp only [U]
    convert hTauUpper using 1
    field_simp [hs.ne']
    ring
  have hPScaleUpperData := extracted_source_logarithmic_scale_upper
    hTOne hUHalf hN16 (by simpa only [N, P] using hPLower) hTauUpperHalf
  rcases hPScaleUpperData with ⟨hPOne, hTauPUpperRaw⟩
  have hTauPUpper : typeILogarithmicScale T P ≤ U := by
    convert hTauPUpperRaw using 1
    all_goals dsimp only [P]
    all_goals ring
  have hPScaleLowerData := extracted_source_logarithmic_scale_lower
    hTPos (mul_nonneg (by norm_num) hcert.tau0_pos.le) (by omega : 4 ≤ N)
    (by simpa only [N, P] using hPLower)
    (by simpa only [N, P] using hPUpper) hTauMargin
  have hTauPMargin : 4 * τ₀ ≤ typeILogarithmicScale T P := by
    convert hPScaleLowerData.2 using 1
    all_goals dsimp only [P]
    all_goals ring
  obtain ⟨k, hk, hkB, hTauPowLower, hTauPowUpper⟩ :=
    exists_bounded_power_scale_reduction_with_margin hcert.tau0_pos
      hTauPMargin hTauPUpper
  let L : ℝ := ((((N : ℝ) / 2) ^ σ) * V₀) /
    Nat.clog 2 (A + 1)
  have hP : 0 < P := by dsimp only [P]; positivity
  have hL : 0 < L := by
    dsimp only [L]
    have hCover : 0 < Nat.clog 2 (A + 1) :=
      Nat.clog_pos Nat.one_lt_two (by omega)
    positivity
  have hCoeff : ∀ n ∈ Finset.Ioc P (2 * P),
      ‖normalizedTypeISourceDirichletCoeff Y A r σ n‖ ≤ 1 := by
    intro n _hn
    exact norm_normalizedTypeISourceDirichletCoeff_le_one Y A r σ hσ.le n
  have hBase₀ : InBaseInterval (3 * T) W₀ := by
    intro t ht
    exact hBase t (hW₀sub ht)
  obtain ⟨q, hq, W', hW'sub₀, hPowerCard, hSep', hBase', hLarge', hMHH⟩ :=
    hPowered k P (normalizedTypeISourceDirichletCoeff Y A r σ)
      0 (3 * T) L W₀ hk hkB hP (by norm_num) (by linarith) hL
      hCoeff hSep₀ hBase₀ (by
        intro t ht
        have hPhase := sum_zero_real_part_eq_dirichletPoly P
          (normalizedTypeISourceDirichletCoeff Y A r σ) t
        rw [hPhase]
        simpa only [P, L, V₀, N] using hLarge₀ t ht)
  have hW'sub : W' ⊆ W := hW'sub₀.trans hW₀sub
  have hCard : (W.card : ℝ) ≤
      (Nat.clog 2 (A + 1) : ℝ) * k * (W'.card : ℝ) := by
    calc
      (W.card : ℝ) ≤ (Nat.clog 2 (A + 1) : ℝ) * (W₀.card : ℝ) := hCard₀
      _ ≤ (Nat.clog 2 (A + 1) : ℝ) * (k * (W'.card : ℝ)) := by
        gcongr
      _ = _ := by ring
  let Q : ℕ := 2 ^ q * P ^ k
  let Vp : ℝ := (L ^ k /
    (Cpow * ((2 ^ k * P ^ k : ℕ) : ℝ) ^ d)) / k
  have hqk : q < k := Finset.mem_range.mp hq
  have hQWindow := hWindow T P k q hTWindow hPOne hk hkB hqk
    hTauPUpper hTauPowLower hTauPowUpper
  dsimp only at hQWindow
  rcases hQWindow with ⟨hQOne, hQScaleLower, hQScaleUpper⟩
  have hGrowthAt := hGrowth T Y A N P hTGrowth rfl rfl
    (by dsimp only [N]; exact Nat.le_mul_of_pos_left Y (pow_pos (by omega) r))
    (by simpa only [N, P] using hPLower)
  have hFourNonneg : 0 ≤ (4 : ℝ) ^ σ := Real.rpow_nonneg (by norm_num) _
  have hGrowthModel :
      (3 / 2 : ℝ) * (Nat.clog 2 A + 1 : ℕ) * T ^ u * 4 ^ σ ≤
        C₀ * ((2 * P : ℕ) : ℝ) ^ d := by
    dsimp only [C₀]
    calc
      (3 / 2 : ℝ) * (Nat.clog 2 A + 1 : ℕ) * T ^ u * 4 ^ σ ≤
          (6 * (Nat.clog 2 A + 1 : ℕ) * T ^ u) * 4 ^ σ := by
            gcongr
            norm_num
      _ ≤ (Cg * ((2 * P : ℕ) : ℝ) ^ d) * 4 ^ σ := by
            exact mul_le_mul_of_nonneg_right hGrowthAt hFourNonneg
      _ = (Cg * 4 ^ σ) * ((2 * P : ℕ) : ℝ) ^ d := by ring
  let L₀ : ℝ := (9 / 16 : ℝ) / Nat.clog 2 (A + 1)
  let D : ℝ := C₀ * ((2 * P : ℕ) : ℝ) ^ d * (P : ℝ) ^ (-σ)
  have hL₀ : 0 < L₀ := by
    dsimp only [L₀]
    have : 0 < Nat.clog 2 (A + 1) := Nat.clog_pos Nat.one_lt_two (by omega)
    positivity
  have hD : 0 < D := by dsimp only [D]; positivity
  have hModelBase := lower_source_threshold_ge_typeII_model
    (C₀ := C₀) (u := u) (η := d) (σ := σ) (T := T)
    (A := A) (N := N) (P := P) (by positivity) hσ.le hTPos hAOne hP
    (by simpa only [N, P] using hPUpper) hGrowthModel
  dsimp only at hModelBase
  have hModelBase' : L₀ / D ≤ L := by
    simpa only [L₀, D, L, V₀, N, P] using hModelBase
  let Ploss := typeIIPoweredThresholdLoss Cpow L₀ D d σ P k
  have hThresholdModel := typeII_powered_threshold_lower
    (C := Cpow) (L := L₀) (D := D) (η := d) (σ := σ)
    (N := P) (k := k) (r := q) (by linarith [hCpow]) hL₀ hD hP hk hσ.le hqk
  dsimp only at hThresholdModel
  rcases hThresholdModel with ⟨hPloss, hThresholdModel⟩
  have hModelToActual :
      (((L₀ / D) ^ k /
          (Cpow * ((2 ^ k * P ^ k : ℕ) : ℝ) ^ d)) / k) ≤ Vp := by
    dsimp only [Vp]
    gcongr
  have hThreshold : (Q : ℝ) ^ σ / Ploss ≤ Vp := by
    have hThresholdModel' : (Q : ℝ) ^ σ / Ploss ≤
        (((L₀ / D) ^ k /
          (Cpow * ((2 ^ k * P ^ k : ℕ) : ℝ) ^ d)) / k) := by
      simpa only [Q, Ploss] using hThresholdModel
    exact hThresholdModel'.trans hModelToActual
  have hEnvelope := source_powered_threshold_loss_le_envelope
    (C₀ := C₀) (C := Cpow) (e := d) (σ := σ) (T := T)
    (A := A) (N := P) (k := k) (B := B) hC₀ hCpow hσUpper.le
    hTEight rfl hP hk hkB
  dsimp only at hEnvelope
  have hPEnvelope : Ploss ≤
      1 + classicalTypeIIPowerLoss Aenv d T k (P ^ k) := by
    simpa only [Ploss, L₀, D, Aenv, aLog, Nat.cast_mul, Nat.cast_ofNat] using hEnvelope
  have hFinalLength : P ^ k ≤ Q := by
    dsimp only [Q]
    exact Nat.le_mul_of_pos_left _ (pow_pos (by omega) q)
  have hPFinal : Ploss ≤
      1 + classicalTypeIIPowerLoss Aenv d T k Q :=
    hPEnvelope.trans (add_le_add_right
      (classicalTypeIIPowerLoss_mono_length hAenv hd.le hTOne hFinalLength) 1)
  let base : ℕ := 4 * Nat.clog 2 A *
    ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T)
  let cover₁ : ℕ := Nat.clog 2 A + 1
  let cover₂ : ℕ := Nat.clog 2 (A + 1)
  let multiplicity : ℕ := base * cover₁
  let extraction : ℕ := cover₂ * k
  have hExtractionPos : 0 < extraction := by
    dsimp only [extraction, cover₂]
    exact Nat.mul_pos (Nat.clog_pos Nat.one_lt_two (by omega)) hk
  have hCount' : zeroCountRect σ 1 T (2 * T) ≤ multiplicity * W.card := by
    simpa only [base, cover₁, multiplicity, A] using hCount
  have hExtract : (W.card : ℝ) ≤ extraction * (W'.card : ℝ) := by
    simpa only [extraction, cover₂, Nat.cast_mul, Nat.cast_ofNat,
      mul_assoc, L, Vp, P, Q, N, V₀] using hCard
  have hEndpoint := endpoint_powered_witness_count_le hσUpper hcert hTPos
    (by simpa only [Q] using hQOne) (by exact_mod_cast hExtractionPos)
    hPloss hThreshold (by simpa only [Q] using hQScaleLower)
    (by simpa only [Q] using hQScaleUpper) hCount' hExtract hK.le
    (by simpa only [Q, Vp, P, L, N, V₀, Real.rpow_zero, one_mul] using hMHH)
  have hLossAt := hLoss T Q k hTLoss (by simpa only [Q] using hQOne)
    hk hkB (by simpa only [Q] using hQScaleLower)
  have hLogsAt := hLogs T hTLog
  have hPowLoss : Ploss ^ (6 : ℕ) ≤
      (1 + classicalTypeIIPowerLoss Aenv d T k Q) ^ (6 : ℕ) :=
    pow_le_pow_left₀ (by positivity) hPFinal 6
  have hTargetNonneg : 0 ≤ T ^ (3 * (1 - σ) / τ₀) := by positivity
  have hEpsPow : T ^ (ε / 4) * T ^ (ε / 4) ≤ T ^ ε := by
    rw [← Real.rpow_add hTPos]
    exact Real.rpow_le_rpow_of_exponent_le hTOne (by linarith)
  have hHarmonicNonneg : 0 ≤ (((harmonic Q : ℚ) : ℝ)) := by
    by_cases hQZero : Q = 0
    · simp only [hQZero, harmonic_zero, Rat.cast_zero]
      norm_num
    · exact_mod_cast (harmonic_pos hQZero).le
  have hCoreNonneg : 0 ≤ ((base : ℝ) * (k : ℝ) *
      (K * (1 + (((harmonic Q : ℚ) : ℝ))))) := by
    positivity
  have hEndpoint' : (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
      (((cover₁ : ℕ) : ℝ) * cover₂) *
        (((base : ℕ) : ℝ) * k *
          (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
            (6 * Ploss ^ (6 : ℕ))) *
              T ^ (3 * (1 - σ) / τ₀) := by
    calc
      (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
          ((base * cover₁ : ℕ) : ℝ) * ((cover₂ * k : ℕ) : ℝ) *
            (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
              (6 * Ploss ^ (6 : ℕ) * T ^ (3 * (1 - σ) / τ₀)) := by
            simpa only [multiplicity, extraction, Ploss] using hEndpoint
      _ = (((cover₁ : ℕ) : ℝ) * cover₂) *
          (((base : ℕ) : ℝ) * k *
            (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
              (6 * Ploss ^ (6 : ℕ))) * T ^ (3 * (1 - σ) / τ₀) := by
            norm_num only [Nat.cast_mul]
            ring
  calc
    (zeroCountRect σ 1 T (2 * T) : ℝ) ≤ _ := hEndpoint'
    _ ≤ (((cover₁ : ℕ) : ℝ) * cover₂) *
        (((base : ℕ) : ℝ) * k *
          (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
            (6 * (1 + classicalTypeIIPowerLoss Aenv d T k Q) ^ (6 : ℕ))) *
              T ^ (3 * (1 - σ) / τ₀) := by
      gcongr
    _ ≤ (Clog * T ^ (ε / 4)) * (Closs * T ^ (ε / 4)) *
          T ^ (3 * (1 - σ) / τ₀) := by
      gcongr
    _ ≤ (Closs * Clog) * T ^ ε *
          T ^ (3 * (1 - σ) / τ₀) := by
      calc
        (Clog * T ^ (ε / 4)) * (Closs * T ^ (ε / 4)) *
              T ^ (3 * (1 - σ) / τ₀) =
            (Closs * Clog) * (T ^ (ε / 4) * T ^ (ε / 4)) *
              T ^ (3 * (1 - σ) / τ₀) := by ring
        _ ≤ (Closs * Clog) * T ^ ε *
              T ^ (3 * (1 - σ) / τ₀) := by gcongr
    _ = C * T ^ ε * T ^ (3 * (1 - σ) / τ₀) := by rfl

/-- Powered endpoint consumer for an actual source block whose *extracted*
dyadic scale lies in the small transition strip below the endpoint window.
The natural power is selected after the literal dyadic block is known.  Thus
the scale divided by `k`, the powered coefficients and the final MHH length
all refer to the same finite object. -/
theorem actual_source_near_endpoint_consumer
    {σ τ₀ : ℝ} (hσLower : 1 / 2 < σ) (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
        let d := classicalEndpointLossParameter σ τ₀ (ε / 100)
        let Y := ⌊T ^ (d ^ 2)⌋₊
        let A := ⌊sharpZetaCutoff T⌋₊
        ∀ {r j : ℕ} (W W₀ : Finset ℝ),
          0 < Y → 1 < A → W.Nonempty → IsSeparated 1 W →
          InBaseInterval (3 * T) W → W₀ ⊆ W →
          IsSeparated 1 W₀ →
          (W.card : ℝ) ≤
            (Nat.clog 2 (A + 1) : ℝ) * (W₀.card : ℝ) →
          (∀ t ∈ W₀,
            let N := 2 ^ r * Y
            let V₀ := ((3 / 4 : ℝ) * (T ^ (-(d ^ 4)) / 2)) /
              (Nat.clog 2 A + 1 : ℕ)
            ((((N : ℝ) / 2) ^ σ) * V₀) / Nat.clog 2 (A + 1) ≤
              ‖dirichletPoly (2 ^ j)
                (normalizedTypeISourceDirichletCoeff Y A r σ) t‖) →
          2 ^ j < 2 * (2 ^ r * Y) → 2 ^ r * Y < 4 * 2 ^ j →
          1 < 2 ^ j →
          typeILogarithmicScale T (2 ^ j) ≤ 4 / (d ^ 2) →
          4 * τ₀ / 3 - reflectedEndpointScaleSlack σ d ≤
            typeILogarithmicScale T (2 ^ j) →
          zeroCountRect σ 1 T (2 * T) ≤
            (4 * Nat.clog 2 A *
              ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T)) *
                (Nat.clog 2 A + 1) * W.card →
          (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
            C * T ^ ε * T ^ (3 * (1 - σ) / τ₀) := by
  intro ε hε
  have hσ : 0 < σ := by linarith
  let η : ℝ := ε / 100
  let d := classicalEndpointLossParameter σ τ₀ η
  let s : ℝ := reflectedEndpointScaleSlack σ d
  let Uscale : ℝ := 4 / (d ^ 2)
  let B : ℕ := ⌈3 * (Uscale + s) / (2 * τ₀)⌉₊
  have hη : 0 < η := by dsimp only [η]; positivity
  have hdSpec := classicalEndpointLossParameter_spec
    hσLower hσUpper hcert.tau0_pos hη
  dsimp only at hdSpec
  rcases hdSpec with ⟨hd, hdEta, hdEtaTau, hdReflected, hdGap,
    hdUpper, _hdSigma, _hdSmall, _hdHalf, hdOne, _hdSigmaStrict⟩
  have hs : 0 < s := by
    dsimp only [s]
    exact reflectedEndpointScaleSlack_pos hσLower hd
  have hsSmall : s ≤ τ₀ / 6 := by
    dsimp only [s]
    exact reflectedEndpointScaleSlack_le_tau0_sixth hσLower hσUpper hcert
      hdGap hdUpper
  have hUscale : 0 < Uscale := by dsimp only [Uscale]; positivity
  have hB : 0 < B := by
    dsimp only [B]
    exact Nat.ceil_pos.mpr (div_pos
      (mul_pos (by norm_num) (add_pos hUscale hs))
      (mul_pos (by norm_num) hcert.tau0_pos))
  have hdOneStrict : d < 1 := hdOne.lt_of_ne (by
    intro h
    subst d
    linarith [hdGap, hσUpper])
  have hDisplacementBudget : 2 * s / τ₀ ≤ ε / 400 := by
    have hBudget := reflected_total_power_budget_with_gap_le hσLower hσUpper
      hcert.tau0_pos hη hd hdOne hdEta hdReflected
    dsimp only [s, η] at hBudget
    have hNonneg : 0 ≤ 24 * d *
        (⌈3 * (2 / ((σ - 1 / 2) / 2) + s) / (2 * τ₀)⌉₊ : ℝ) +
        6 * d := by positivity
    linarith
  obtain ⟨Cpow, hCpow, K, hK, hPowered⟩ :=
    powered_unit_block_large_values_bound_bounded_uniform B d hd
  obtain ⟨Cg, hCg, Tgrowth, hTgrowth, hGrowth⟩ :=
    eventually_lower_source_threshold_scale_growth d hd hdOneStrict
  let C₀ : ℝ := Cg * 4 ^ σ
  have hC₀ : 1 ≤ C₀ := by
    have hFour : 1 ≤ (4 : ℝ) ^ σ := Real.one_le_rpow (by norm_num) hσ.le
    dsimp only [C₀]
    nlinarith [mul_nonneg (sub_nonneg.mpr hCg) (sub_nonneg.mpr hFour)]
  let aLog : ℝ := max 1
    (((16 / 9 : ℝ) * (1 + (Real.log 2)⁻¹)) / 4)
  let Aenv : ℝ := (2 : ℝ) ^ B *
    ((2 : ℝ) ^ B * C₀ ^ B * Cpow * aLog ^ B)
  have hAenv : 0 ≤ Aenv := by dsimp only [Aenv, aLog]; positivity
  obtain ⟨Closs, hCloss, Tloss, hTloss, hLoss⟩ :=
    eventually_endpoint_loss_bundle_le Aenv K d d (9 * τ₀ / 16) (ε / 4) B
      hAenv hK.le hd hd (by nlinarith [hcert.tau0_pos]) (by positivity) hB
      (by dsimp only [η] at hdEta; nlinarith)
      (by dsimp only [η] at hdEtaTau; nlinarith)
  obtain ⟨Ccover, hCcover, Tcover, hTcover, hCover⟩ :=
    eventually_source_selection_log_product_le (ε / 4) (by positivity)
  obtain ⟨Tscale, hTscale, hScaleDyadic⟩ :=
    eventually_dyadic_power_scale_lower_half
      (τ₀ := 3 * τ₀ / 4) (U := Uscale)
      (by nlinarith [hcert.tau0_pos]) hUscale
  let C : ℝ := Closs * Ccover * ((2 : ℝ) ^ B) ^ (2 : ℕ)
  let T₀ : ℝ := max Tloss (max Tcover (max Tscale Tgrowth))
  refine ⟨C, by dsimp only [C]; positivity, T₀,
    hTloss.trans (le_max_left _ _), ?_⟩
  intro T hT
  dsimp only
  intro r j W W₀ hY hA hW hSep hBase hW₀sub hSep₀ hCard₀ hLarge₀
    hPUpper hPLower hPOne hTauPUpper hNear hCount
  have hTLoss : Tloss ≤ T := (le_max_left _ _).trans hT
  have hRest : max Tcover (max Tscale Tgrowth) ≤ T :=
    (le_max_right _ _).trans hT
  have hTCover : Tcover ≤ T := (le_max_left _ _).trans hRest
  have hRest' : max Tscale Tgrowth ≤ T := (le_max_right _ _).trans hRest
  have hTScale : Tscale ≤ T := (le_max_left _ _).trans hRest'
  have hTGrowth : Tgrowth ≤ T := (le_max_right _ _).trans hRest'
  have hTEight : 8 ≤ T := hTloss.trans hTLoss
  have hTOne : 1 ≤ T := by linarith
  have hTPos : 0 < T := by linarith
  let Y : ℕ := ⌊T ^ d ^ 2⌋₊
  let A : ℕ := ⌊sharpZetaCutoff T⌋₊
  let N : ℕ := 2 ^ r * Y
  let P : ℕ := 2 ^ j
  let V₀ : ℝ := ((3 / 4 : ℝ) * (T ^ (-(d ^ 4)) / 2)) /
    (Nat.clog 2 A + 1 : ℕ)
  let L : ℝ := ((((N : ℝ) / 2) ^ σ) * V₀) / Nat.clog 2 (A + 1)
  have hP : 0 < P := by dsimp only [P]; positivity
  have hN : 0 < N := by dsimp only [N, Y]; exact Nat.mul_pos (pow_pos (by omega) r) hY
  have hL : 0 < L := by
    dsimp only [L, V₀, N, A]
    have hCover : 0 < Nat.clog 2 (⌊sharpZetaCutoff T⌋₊ + 1) :=
      Nat.clog_pos Nat.one_lt_two (by omega)
    positivity
  have hCoeff : ∀ n ∈ Finset.Ioc P (2 * P),
      ‖normalizedTypeISourceDirichletCoeff Y A r σ n‖ ≤ 1 := by
    intro n _hn
    exact norm_normalizedTypeISourceDirichletCoeff_le_one Y A r σ hσ.le n
  have hBase₀ : InBaseInterval (3 * T) W₀ := by
    intro t ht
    exact hBase t (hW₀sub ht)
  obtain ⟨k, hk, hkB, hkLower, hkUpper, hkScale, hkActualLower, hkGapLoss⟩ :=
    exists_bounded_positive_power_augmented_endpoint_with_gap hσUpper hcert
      hs.le hdUpper hsSmall
      (by simpa only [P] using hNear)
      (by simpa only [P, Uscale] using hTauPUpper)
  obtain ⟨q, hq, W', hW'sub₀, hPowerCard, hSep', hBase', hLarge', hMHH⟩ :=
    hPowered k P (normalizedTypeISourceDirichletCoeff Y A r σ)
      0 (3 * T) L W₀ hk hkB hP (by norm_num) (by linarith) hL
      hCoeff hSep₀ hBase₀ (by
        intro t ht
        rw [sum_zero_real_part_eq_dirichletPoly]
        simpa only [P, L, V₀, N, Y, A] using hLarge₀ t ht)
  let Q : ℕ := 2 ^ q * P ^ k
  let Vp : ℝ := (L ^ k /
    (Cpow * ((2 ^ k * P ^ k : ℕ) : ℝ) ^ d)) / k
  have hqk : q < k := Finset.mem_range.mp hq
  let L₀ : ℝ := (9 / 16 : ℝ) / Nat.clog 2 (A + 1)
  let D : ℝ := C₀ * ((2 * P : ℕ) : ℝ) ^ d * (P : ℝ) ^ (-σ)
  have hL₀ : 0 < L₀ := by
    dsimp only [L₀]
    have : 0 < Nat.clog 2 (A + 1) := Nat.clog_pos Nat.one_lt_two (by omega)
    positivity
  have hD : 0 < D := by dsimp only [D]; positivity
  have hGrowthAt := hGrowth T Y A N P hTGrowth rfl rfl
    (by dsimp only [N]; exact Nat.le_mul_of_pos_left Y (pow_pos (by omega) r))
    (by simpa only [N, P] using hPLower)
  have hGrowthModel :
      (3 / 2 : ℝ) * (Nat.clog 2 A + 1 : ℕ) * T ^ (d ^ 4) * 4 ^ σ ≤
        C₀ * ((2 * P : ℕ) : ℝ) ^ d := by
    dsimp only [C₀]
    calc
      (3 / 2 : ℝ) * (Nat.clog 2 A + 1 : ℕ) * T ^ (d ^ 4) * 4 ^ σ ≤
          (6 * (Nat.clog 2 A + 1 : ℕ) * T ^ (d ^ 4)) * 4 ^ σ := by
            gcongr
            norm_num
      _ ≤ (Cg * ((2 * P : ℕ) : ℝ) ^ d) * 4 ^ σ := by
            exact mul_le_mul_of_nonneg_right hGrowthAt
              (Real.rpow_nonneg (by norm_num) _)
      _ = (Cg * 4 ^ σ) * ((2 * P : ℕ) : ℝ) ^ d := by ring
  have hModelBase := lower_source_threshold_ge_typeII_model
    (C₀ := C₀) (u := d ^ 4) (η := d) (σ := σ) (T := T)
    (A := A) (N := N) (P := P) (by positivity) hσ.le hTPos hA hP
    (by simpa only [N, P] using hPUpper) hGrowthModel
  dsimp only at hModelBase
  have hModelBase' : L₀ / D ≤ L := by
    simpa only [L₀, D, L, V₀, N, P] using hModelBase
  let Ploss := typeIIPoweredThresholdLoss Cpow L₀ D d σ P k
  have hThresholdModel := typeII_powered_threshold_lower
    (C := Cpow) (L := L₀) (D := D) (η := d) (σ := σ)
    (N := P) (k := k) (r := q) (by linarith [hCpow]) hL₀ hD hP hk hσ.le hqk
  dsimp only at hThresholdModel
  rcases hThresholdModel with ⟨hPloss, hThresholdModel⟩
  have hModelToActual :
      (((L₀ / D) ^ k /
          (Cpow * ((2 ^ k * P ^ k : ℕ) : ℝ) ^ d)) / k) ≤ Vp := by
    dsimp only [Vp]
    gcongr
  have hThreshold : (Q : ℝ) ^ σ / Ploss ≤ Vp := by
    have hThresholdModel' : (Q : ℝ) ^ σ / Ploss ≤
        (((L₀ / D) ^ k /
          (Cpow * ((2 ^ k * P ^ k : ℕ) : ℝ) ^ d)) / k) := by
      simpa only [Q, Ploss] using hThresholdModel
    exact hThresholdModel'.trans hModelToActual
  have hEnvelope := source_powered_threshold_loss_le_envelope
    (C₀ := C₀) (C := Cpow) (e := d) (σ := σ) (T := T)
    (A := A) (N := P) (k := k) (B := B) hC₀ hCpow hσUpper.le
    hTEight rfl hP hk hkB
  dsimp only at hEnvelope
  have hPEnvelope : Ploss ≤
      1 + classicalTypeIIPowerLoss Aenv d T k (P ^ k) := by
    simpa only [Ploss, L₀, D, Aenv, aLog, Nat.cast_mul, Nat.cast_ofNat] using hEnvelope
  have hFinalLength : P ^ k ≤ Q := by
    dsimp only [Q]
    exact Nat.le_mul_of_pos_left _ (pow_pos (by omega) q)
  have hPFinal : Ploss ≤
      1 + classicalTypeIIPowerLoss Aenv d T k Q :=
    hPEnvelope.trans (add_le_add_right
      (classicalTypeIIPowerLoss_mono_length hAenv hd.le hTOne hFinalLength) 1)
  have hPower := dyadic_power_mhh_le_endpoint_with_factor_of_augmented_scale
    hσLower hσUpper hcert hTOne (by simpa only [P] using hPOne)
    hk hkB hqk hkScale hkLower hkUpper hkGapLoss
  dsimp only at hPower
  have hFinalScale : 3 * τ₀ / 8 ≤ typeILogarithmicScale T Q := by
    have hScale := hScaleDyadic T P k q hTScale
      (by simpa only [P] using hPOne) hk hqk
      (by simpa only [P, Uscale] using hTauPUpper)
      (by nlinarith [hkActualLower] : 2 * (3 * τ₀ / 4) / 3 ≤
        typeILogarithmicScale T P / k)
    convert hScale using 1
    · ring
  let base : ℕ := 4 * Nat.clog 2 A *
    ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T)
  let cover₁ : ℕ := Nat.clog 2 A + 1
  let cover₂ : ℕ := Nat.clog 2 (A + 1)
  let extraction : ℕ := cover₂ * k
  have hExtractionPos : 0 < extraction := by
    dsimp only [extraction, cover₂]
    exact Nat.mul_pos (Nat.clog_pos Nat.one_lt_two (by omega)) hk
  have hCount' : zeroCountRect σ 1 T (2 * T) ≤ (base * cover₁) * W.card := by
    simpa only [base, cover₁, A] using hCount
  have hExtract : (W.card : ℝ) ≤ extraction * (W'.card : ℝ) := by
    calc
      (W.card : ℝ) ≤ (cover₂ : ℝ) * (W₀.card : ℝ) := by
        simpa only [cover₂] using hCard₀
      _ ≤ (cover₂ : ℝ) * (k * (W'.card : ℝ)) := by gcongr
      _ = extraction * (W'.card : ℝ) := by
        dsimp only [extraction]
        push_cast
        ring
  have hEndpoint := endpoint_witness_count_le_of_mhh_power_factor hTPos
    (by simpa only [Q] using
      (show 1 < 2 ^ q * P ^ k by
        exact (one_lt_pow₀ (by simpa only [P] using hPOne) hk.ne').trans_le
          (Nat.le_mul_of_pos_left _ (pow_pos (by omega) q))))
    (by exact_mod_cast hExtractionPos) hPloss hThreshold
    (R := ((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (2 * s / τ₀))
    (by
      calc
        (Q : ℝ) ^ classicalMHHExponent σ (typeILogarithmicScale T Q) ≤
            ((2 : ℝ) ^ B) ^ (2 : ℕ) *
              T ^ (3 * (1 - σ) / τ₀ + 2 * s / τ₀) := by
                simpa only [Q, P] using hPower
        _ = (((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (2 * s / τ₀)) *
              T ^ (3 * (1 - σ) / τ₀) := by
            rw [Real.rpow_add hTPos]
            ring)
    hCount' hExtract hK.le
    (by simpa only [Q, Vp, P, L, Real.rpow_zero, one_mul] using hMHH)
  have hLossAt := hLoss T Q k hTLoss
    (by dsimp only [Q]; exact (one_lt_pow₀ (by simpa only [P] using hPOne)
      hk.ne').trans_le (Nat.le_mul_of_pos_left _ (pow_pos (by omega) q)))
    hk hkB (by nlinarith [hFinalScale])
  have hCoverAt := hCover T hTCover
  have hPowLoss : Ploss ^ (6 : ℕ) ≤
      (1 + classicalTypeIIPowerLoss Aenv d T k Q) ^ (6 : ℕ) :=
    pow_le_pow_left₀ (by positivity) hPFinal 6
  have hTargetNonneg : 0 ≤ T ^ (3 * (1 - σ) / τ₀) := by positivity
  have hDisp : T ^ (2 * s / τ₀) ≤ T ^ (ε / 400) :=
    Real.rpow_le_rpow_of_exponent_le hTOne hDisplacementBudget
  have hHarmonicNonneg : 0 ≤ (((harmonic Q : ℚ) : ℝ)) := by
    exact_mod_cast (harmonic_pos (by
      dsimp only [Q]
      positivity : Q ≠ 0)).le
  have hCoreNonneg : 0 ≤
      (base : ℝ) * k * (K * (1 + (((harmonic Q : ℚ) : ℝ)))) := by
    positivity
  have hCoreBound :
      (base : ℝ) * k * (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
          (6 * (1 + classicalTypeIIPowerLoss Aenv d T k Q) ^ (6 : ℕ)) ≤
        Closs * T ^ (ε / 4) := by
    simpa only [base, A] using hLossAt
  have hCoverBound : (cover₁ : ℝ) * cover₂ ≤
      Ccover * T ^ (ε / 4) := by
    simpa only [cover₁, cover₂, A] using hCoverAt
  have hCoverNonneg : 0 ≤ (cover₁ : ℝ) * cover₂ := by positivity
  have hCoverTargetNonneg : 0 ≤ Ccover * T ^ (ε / 4) := by positivity
  have hNewCoreNonneg : 0 ≤
      (base : ℝ) * k * (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
        (6 * (1 + classicalTypeIIPowerLoss Aenv d T k Q) ^ (6 : ℕ)) := by
    positivity
  have hDyadicConstantNonneg : 0 ≤ ((2 : ℝ) ^ B) ^ (2 : ℕ) := by
    positivity
  have hSourceDispNonneg : 0 ≤ T ^ (2 * s / τ₀) := by positivity
  have hTargetDispNonneg : 0 ≤ T ^ (ε / 400) := by positivity
  have hSixPow : 6 * Ploss ^ (6 : ℕ) ≤
      6 * (1 + classicalTypeIIPowerLoss Aenv d T k Q) ^ (6 : ℕ) :=
    mul_le_mul_of_nonneg_left hPowLoss (by norm_num)
  have hPoweredCore :
      (base : ℝ) * k * (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
          (6 * Ploss ^ (6 : ℕ)) ≤
        (base : ℝ) * k * (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
          (6 * (1 + classicalTypeIIPowerLoss Aenv d T k Q) ^ (6 : ℕ)) :=
    mul_le_mul_of_nonneg_left hSixPow hCoreNonneg
  have hFirstFront := mul_le_mul_of_nonneg_left hPoweredCore hCoverNonneg
  have hFirstDyadic := mul_le_mul_of_nonneg_right hFirstFront hDyadicConstantNonneg
  have hFirstDisp := mul_le_mul_of_nonneg_right hFirstDyadic hSourceDispNonneg
  have hFirstFinal := mul_le_mul_of_nonneg_right hFirstDisp hTargetNonneg
  have hCoverCore :
      ((cover₁ : ℝ) * cover₂) *
          ((base : ℝ) * k * (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
            (6 * (1 + classicalTypeIIPowerLoss Aenv d T k Q) ^ (6 : ℕ))) ≤
        (Ccover * T ^ (ε / 4)) * (Closs * T ^ (ε / 4)) :=
    mul_le_mul hCoverBound hCoreBound hNewCoreNonneg hCoverTargetNonneg
  have hSecondDyadic := mul_le_mul_of_nonneg_right hCoverCore hDyadicConstantNonneg
  have hSecondDisp := mul_le_mul hSecondDyadic hDisp hSourceDispNonneg (by positivity)
  have hSecondFinal := mul_le_mul_of_nonneg_right hSecondDisp hTargetNonneg
  have hEpsCombine : T ^ (ε / 4) * T ^ (ε / 4) * T ^ (ε / 400) ≤
      T ^ ε := by
    rw [← Real.rpow_add hTPos, ← Real.rpow_add hTPos]
    exact Real.rpow_le_rpow_of_exponent_le hTOne (by linarith)
  have hEndpoint' := hEndpoint
  calc
    (zeroCountRect σ 1 T (2 * T) : ℝ) ≤ _ := hEndpoint'
    _ = ((cover₁ : ℝ) * cover₂) *
        ((base : ℝ) * k * (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
          (6 * Ploss ^ (6 : ℕ))) *
        ((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (2 * s / τ₀) *
          T ^ (3 * (1 - σ) / τ₀) := by
      dsimp only [base, cover₁, cover₂, extraction] at hEndpoint' ⊢
      norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hEndpoint' ⊢
      ring
    _ ≤ ((cover₁ : ℝ) * cover₂) *
        ((base : ℝ) * k * (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
          (6 * (1 + classicalTypeIIPowerLoss Aenv d T k Q) ^ (6 : ℕ))) *
        ((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (2 * s / τ₀) *
          T ^ (3 * (1 - σ) / τ₀) := hFirstFinal
    _ ≤ (Ccover * T ^ (ε / 4)) * (Closs * T ^ (ε / 4)) *
        ((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (ε / 400) *
          T ^ (3 * (1 - σ) / τ₀) := hSecondFinal
    _ ≤ C * T ^ ε * T ^ (3 * (1 - σ) / τ₀) := by
      dsimp only [C]
      calc
        (Ccover * T ^ (ε / 4)) * (Closs * T ^ (ε / 4)) *
            ((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (ε / 400) *
              T ^ (3 * (1 - σ) / τ₀) =
          (Closs * Ccover * ((2 : ℝ) ^ B) ^ (2 : ℕ)) *
            (T ^ (ε / 4) * T ^ (ε / 4) * T ^ (ε / 400)) *
              T ^ (3 * (1 - σ) / τ₀) := by ring
        _ ≤ (Closs * Ccover * ((2 : ℝ) ^ B) ^ (2 : ℕ)) *
            T ^ ε * T ^ (3 * (1 - σ) / τ₀) := by gcongr

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

/-- One common kernel majorant for both signs in the exact B-process on the
physical slab.  The positive sign uses the stationary estimate, while the
reversed sign uses the stronger nonstationary estimate. -/
noncomputable def mediumTypeIStationaryKernel
    (sigma T : ℝ) (Q : ℕ) : ℝ :=
  (32 / T) * ((Q : ℝ) / 2) ^ (-sigma) +
    (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
      (T / 4) ^ (-sigma - 1 / 2)

theorem mediumTypeIStationaryKernel_pos
    {sigma T : ℝ} {Q : ℕ} (hT : 0 < T) (hQ : 0 < Q) :
    0 < mediumTypeIStationaryKernel sigma T Q := by
  unfold mediumTypeIStationaryKernel
  positivity

theorem norm_typeIPowerReflectionIntegral_both_signs_le_mediumKernel
    {sigma T t H : ℝ} {Q M : ℕ}
    (hsigma : 0 < sigma) (hT : 0 < T)
    (htLower : T / 2 ≤ t) (_htUpper : t ≤ 3 * T)
    (hH : 0 ≤ H) (hHt : 2 * H ≤ T / 2 - 2)
    (hQ : 0 < Q) (hM : 1 ≤ M) {u : ℝ}
    (hu : u ∈ Set.Icc (-H) H) :
    ‖typeIPowerReflectionIntegral sigma (t + u)
        ((Q : ℝ) / 2) (2 * M * Q)‖ ≤
        mediumTypeIStationaryKernel sigma T Q ∧
      ‖typeIPowerReflectionIntegral sigma (-t + u)
        ((Q : ℝ) / 2) (2 * M * Q)‖ ≤
        mediumTypeIStationaryKernel sigma T Q := by
  have ht : 2 ≤ t := by linarith
  have hHt' : 2 * H ≤ t - 2 := by linarith
  have hPos := norm_typeIPowerReflectionIntegral_le_on_symmetric_window
    (sigma := sigma) (t := t) (H := H) (Q := (Q : ℝ)) (M := M)
    hsigma ht hHt' (by exact_mod_cast hQ) hM hu
  have htPos : 0 < t := by linarith
  have hTwoH : 2 * H ≤ t := by linarith
  have hNeg := norm_typeIPowerReflectionIntegral_neg_le_on_symmetric_window
    (sigma := sigma) (t := t) (H := H) (Q := (Q : ℝ)) (M := M)
    hsigma htPos hTwoH (by exact_mod_cast hQ) hM hu
  have hInv : 16 / t ≤ 32 / T := by
    rw [div_le_div_iff₀ htPos hT]
    nlinarith
  have hInvNeg : 8 / t ≤ 32 / T :=
    (div_le_div_of_nonneg_right (by norm_num) htPos.le).trans hInv
  have hQuarter : T / 4 ≤ t / 2 := by linarith
  have hExp : -sigma - 1 / 2 ≤ 0 := by linarith
  have hPow := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < T / 4)
    hQuarter hExp
  constructor
  · exact hPos.trans (by
      unfold mediumTypeIStationaryKernel
      gcongr)
  · calc
      ‖typeIPowerReflectionIntegral sigma (-t + u)
          ((Q : ℝ) / 2) (2 * M * Q)‖ ≤
          (8 / t) * ((Q : ℝ) / 2) ^ (-sigma) := hNeg
      _ ≤ (32 / T) * ((Q : ℝ) / 2) ^ (-sigma) := by gcongr
      _ ≤ mediumTypeIStationaryKernel sigma T Q := by
        unfold mediumTypeIStationaryKernel
        exact le_add_of_nonneg_right (by positivity)

/-! ## Reflected endpoint exponent arithmetic -/

/- The direct exponent shortcut below is retained as design work only.  The
source-faithful assembly routes the reflected scale through the certificate's
powered/Weyl alternatives.

/-- The three real powers occurring after the medium B-process is
normalized at the reflected threshold.  This is deliberately expressed in
the original physical scale `tau = log_Q T`; doing so avoids replacing the
finite dual cutoff by an unrelated exact real power. -/
noncomputable def mediumReflectedMHHExponent (sigma tau : ℝ) : ℝ :=
  max (1 - 2 * sigma / tau)
    (min (1 + (1 - 2 * sigma) / tau)
      (2 + (2 - 6 * sigma) / tau))

/-- On the genuinely reflected branch, the loss-free B-process/MHH
exponent is bounded by the endpoint exponent.  The proof uses only the
arithmetic alternatives carried by the actual endpoint certificate. -/
theorem mediumReflectedMHHExponent_le_endpoint
    {sigma tau₀ tau : ℝ}
    (hsigmaLower : 1 / 2 < sigma) (hsigmaUpper : sigma < 1)
    (hcert : EndpointScaleCertificate sigma tau₀)
    (htau₀ : tau₀ < tau) (htauOne : 1 < tau) (htauTwo : tau < 2)
    (htauUpper : tau < 4 * tau₀ / 3)
    (hNotWeyl : 6 * sigma - 3 ≤ tau) :
    mediumReflectedMHHExponent sigma tau ≤
      3 * (1 - sigma) / tau₀ := by
  have htauPos : 0 < tau := by linarith
  have htau₀Pos : 0 < tau₀ := hcert.tau0_pos
  rw [mediumReflectedMHHExponent, max_le_iff]
  constructor
  · rw [le_div_iff₀ htau₀Pos]
    field_simp [htauPos.ne']
    rcases endpointScaleCertificate_tau0_alternative hsigmaUpper hcert with hI | hH
    · by_cases hsign : 0 ≤ tau - 2 * sigma
      · have hmul := mul_le_mul_of_nonneg_left hI hsign
        nlinarith
      · nlinarith
    · by_cases hsign : 0 ≤ tau - 2 * sigma
      · have hmul := mul_le_mul_of_nonneg_left hH hsign
        nlinarith
      · nlinarith
  · rw [min_le_iff]
    by_cases hswitch : tau ≤ 4 * sigma - 1
    · right
      rw [le_div_iff₀ htau₀Pos]
      field_simp [htauPos.ne']
      rcases endpointScaleCertificate_tau0_alternative hsigmaUpper hcert with hI | hH
      · by_cases hsign : 0 ≤ 2 * tau + 2 - 6 * sigma
        · have hmul := mul_le_mul_of_nonneg_left hI hsign
          nlinarith
        · nlinarith
      · by_cases hsign : 0 ≤ 2 * tau + 2 - 6 * sigma
        · have hmul := mul_le_mul_of_nonneg_left hH hsign
          nlinarith
        · nlinarith
    · left
      have hswitch' : 4 * sigma - 1 < tau := lt_of_not_ge hswitch
      rw [le_div_iff₀ htau₀Pos]
      field_simp [htauPos.ne']
      rcases endpointScaleCertificate_tau0_alternative hsigmaUpper hcert with hI | hH
      · by_cases hsign : 0 ≤ tau + 1 - 2 * sigma
        · have hmul := mul_le_mul_of_nonneg_left hI hsign
          nlinarith
        · nlinarith
      · by_cases hsign : 0 ≤ tau + 1 - 2 * sigma
        · have hmul := mul_le_mul_of_nonneg_left hH hsign
          nlinarith
        · nlinarith
-/

/-- Uniform power bound for the common stationary kernel on a genuine
medium scale.  Both summands are put on the same `T^(-sigma-1/2)` scale;
the first uses the exact physical identity `Q^tau=T`. -/
theorem mediumTypeIStationaryKernel_le_rpow
    {sigma T tau : ℝ} {Q : ℕ}
    (hsigmaLower : 1 / 2 < sigma) (hsigmaUpper : sigma < 1)
    (hT : 1 ≤ T) (hQ : 1 < Q) (htauOne : 1 < tau) (htauTwo : tau < 2)
    (hScale : (Q : ℝ) ^ tau = T) :
    mediumTypeIStationaryKernel sigma T Q ≤
      (32 * 2 ^ sigma +
        (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
          4 ^ (sigma + 1 / 2)) * T ^ (-sigma - 1 / 2) := by
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have hQPos : (0 : ℝ) < Q := by positivity
  have htauPos : 0 < tau := by linarith
  have hExp : -1 - sigma / tau ≤ -sigma - 1 / 2 := by
    have hprod : (sigma - 1 / 2) * (2 - tau) > 0 :=
      mul_pos (by linarith) (by linarith)
    field_simp [htauPos.ne']
    nlinarith
  have hQpow : (Q : ℝ) ^ (-sigma) = T ^ (-sigma / tau) := by
    rw [← hScale, ← Real.rpow_mul hQPos.le]
    congr 1
    field_simp [htauPos.ne']
  have hFirstPower : T ^ (-1 - sigma / tau) ≤ T ^ (-sigma - 1 / 2) :=
    Real.rpow_le_rpow_of_exponent_le hT hExp
  have hFirst : (32 / T) * ((Q : ℝ) / 2) ^ (-sigma) ≤
      (32 * 2 ^ sigma) * T ^ (-sigma - 1 / 2) := by
    rw [Real.div_rpow (by positivity : 0 ≤ (Q : ℝ)) (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), hQpow]
    simp only [div_eq_mul_inv, inv_inv]
    rw [← Real.rpow_neg_one]
    have hCombine : T ^ (-1 : ℝ) * T ^ (-sigma / tau) =
        T ^ (-1 - sigma / tau) := by
      rw [← Real.rpow_add hTPos]
      congr 1
      ring
    calc
      32 * T ^ (-1 : ℝ) * (T ^ (-sigma / tau) * 2 ^ sigma) =
          (32 * 2 ^ sigma) *
            (T ^ (-1 : ℝ) * T ^ (-sigma / tau)) := by ring
      _ = (32 * 2 ^ sigma) * T ^ (-1 - sigma / tau) := by rw [hCombine]
      _ ≤ (32 * 2 ^ sigma) * T ^ (-sigma - 1 / 2) := by gcongr
  have hSecondEq : (T / 4) ^ (-sigma - 1 / 2) =
      4 ^ (sigma + 1 / 2) * T ^ (-sigma - 1 / 2) := by
    rw [Real.div_rpow hTPos.le (by norm_num : (0 : ℝ) ≤ 4)]
    have hInv : ((4 : ℝ) ^ (-sigma - 1 / 2))⁻¹ =
        (4 : ℝ) ^ (sigma + 1 / 2) := by
      rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
      congr 1
      ring
    rw [div_eq_mul_inv, hInv]
    ring
  unfold mediumTypeIStationaryKernel
  rw [hSecondEq]
  calc
    (32 / T) * ((Q : ℝ) / 2) ^ (-sigma) +
          (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
            (4 ^ (sigma + 1 / 2) * T ^ (-sigma - 1 / 2)) ≤
        (32 * 2 ^ sigma) * T ^ (-sigma - 1 / 2) +
          (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
            (4 ^ (sigma + 1 / 2) * T ^ (-sigma - 1 / 2)) := by gcongr
    _ = (32 * 2 ^ sigma +
          (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
            4 ^ (sigma + 1 / 2)) * T ^ (-sigma - 1 / 2) := by ring

/- Elementary ratio bridge used three times in the reflected MHH bound.
It keeps the threshold constant and all real powers explicit.
theorem natPow_div_natPow_le_rpow
    {T C X L mu v : ℝ} {n : ℕ}
    (hT : 0 < T) (hC : 0 < C) (hX : 0 ≤ X) (hL : 0 < L)
    (hXUpper : X ≤ T ^ mu) (hLLower : T ^ v / C ≤ L) :
    X ^ n / L ^ n ≤ C ^ n * T ^ ((n : ℝ) * (mu - v)) := by
  have hBasePos : 0 < T ^ v / C := by positivity
  have hNum : X ^ n ≤ (T ^ mu) ^ n := pow_le_pow_left₀ hX hXUpper n
  have hDen : (T ^ v / C) ^ n ≤ L ^ n :=
    pow_le_pow_left₀ hBasePos.le hLLower n
  calc
    X ^ n / L ^ n ≤ (T ^ mu) ^ n / (T ^ v / C) ^ n := by
      exact div_le_div hNum hDen (pow_pos hBasePos n).le (pow_pos hL n)
    _ = C ^ n * T ^ ((n : ℝ) * (mu - v)) := by
      rw [div_pow, div_div, ← mul_div_assoc]
      field_simp [hC.ne']
      rw [← Real.rpow_natCast, ← Real.rpow_natCast,
        ← Real.rpow_mul hT.le, ← Real.rpow_mul hT.le,
        ← Real.rpow_sub hT]
      congr 1
      ring

/-- Exact finite envelope for the three MHH terms after reflection.  The
input `mu` is an upper exponent for the literal floored dual length and `v`
is a lower exponent for its actual normalized threshold. -/
theorem reflected_mhh_terms_le_power_envelope
    {T C L mu v : ℝ} {P M : ℕ}
    (hT : 1 ≤ T) (hC : 1 ≤ C) (hL : 0 < L)
    (hPM : P ≤ M) (hM : (M : ℝ) ≤ T ^ mu)
    (hLLower : T ^ v / C ≤ L) :
    (P : ℝ) ^ 2 / L ^ 2 +
        (3 * T) * min ((P : ℝ) / L ^ 2)
          ((P : ℝ) ^ 4 / L ^ 6) ≤
      C ^ 6 * (T ^ (2 * (mu - v)) +
        3 * min (T ^ (1 + mu - 2 * v))
          (T ^ (1 + 4 * mu - 6 * v))) := by
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have hCPos : 0 < C := zero_lt_one.trans_le hC
  have hPUpper : (P : ℝ) ≤ T ^ mu := by
    exact_mod_cast hPM
    exact_mod_cast hPM
  have hPUpper' : (P : ℝ) ≤ (M : ℝ) := by exact_mod_cast hPM
  have hPToT : (P : ℝ) ≤ T ^ mu := hPUpper'.trans hM
  have hTwo := natPow_div_natPow_le_rpow hTPos hCPos
    (Nat.cast_nonneg P) hL hPToT hLLower (n := 2)
  have hOneNumerator : (P : ℝ) / L ^ 2 ≤
      C ^ 2 * T ^ (mu - 2 * v) := by
    have hDen := natPow_div_natPow_le_rpow hTPos hCPos
      (Nat.cast_nonneg P) hL hPToT hLLower (n := 1)
    have hLInv : 1 / L ≤ C * T ^ (-v) := by
      simpa only [pow_one, one_div] using hDen
    have hLInvNonneg : 0 ≤ 1 / L := by positivity
    have hPNonneg : 0 ≤ (P : ℝ) := Nat.cast_nonneg P
    calc
      (P : ℝ) / L ^ 2 = ((P : ℝ) / L) * (1 / L) := by field_simp
      _ ≤ (C * T ^ (mu - v)) * (C * T ^ (-v)) := by
        gcongr
      _ = C ^ 2 * T ^ (mu - 2 * v) := by
        rw [← Real.rpow_add hTPos]
        ring
  have hFour := natPow_div_natPow_le_rpow hTPos hCPos
    (Nat.cast_nonneg P) hL hPToT hLLower (n := 4)
  have hFourSix : (P : ℝ) ^ 4 / L ^ 6 ≤
      C ^ 6 * T ^ (4 * mu - 6 * v) := by
    have hInvTwo : 1 / L ^ 2 ≤ C ^ 2 * T ^ (-2 * v) := by
      have hZero := natPow_div_natPow_le_rpow hTPos hCPos
        (show (0 : ℝ) ≤ 1 by norm_num) hL
        (show (1 : ℝ) ≤ T ^ (0 : ℝ) by simp) hLLower (n := 2)
      simpa only [one_pow, zero_sub, Nat.cast_ofNat, zero_mul, Real.rpow_zero,
        mul_one] using hZero
    calc
      (P : ℝ) ^ 4 / L ^ 6 =
          ((P : ℝ) ^ 4 / L ^ 4) * (1 / L ^ 2) := by field_simp
      _ ≤ (C ^ 4 * T ^ (4 * (mu - v))) *
          (C ^ 2 * T ^ (-2 * v)) := by gcongr
      _ = C ^ 6 * T ^ (4 * mu - 6 * v) := by
        rw [← Real.rpow_add hTPos]
        ring
  have hCtwoSix : C ^ 2 ≤ C ^ 6 := by nlinarith [sq_nonneg (C ^ 2 - 1)]
  have hTermOne : (P : ℝ) ^ 2 / L ^ 2 ≤
      C ^ 6 * T ^ (2 * (mu - v)) := hTwo.trans (by gcongr)
  have hTermTwo : (3 * T) * min ((P : ℝ) / L ^ 2)
        ((P : ℝ) ^ 4 / L ^ 6) ≤
      C ^ 6 * (3 * min (T ^ (1 + mu - 2 * v))
        (T ^ (1 + 4 * mu - 6 * v))) := by
    have hA : T * ((P : ℝ) / L ^ 2) ≤
        C ^ 6 * T ^ (1 + mu - 2 * v) := by
      calc
        T * ((P : ℝ) / L ^ 2) ≤
            T * (C ^ 2 * T ^ (mu - 2 * v)) := by gcongr
        _ = C ^ 2 * T ^ (1 + mu - 2 * v) := by
          rw [← Real.rpow_one T, ← Real.rpow_add hTPos]
          ring
        _ ≤ C ^ 6 * T ^ (1 + mu - 2 * v) := by gcongr
    have hB : T * ((P : ℝ) ^ 4 / L ^ 6) ≤
        C ^ 6 * T ^ (1 + 4 * mu - 6 * v) := by
      calc
        T * ((P : ℝ) ^ 4 / L ^ 6) ≤
            T * (C ^ 6 * T ^ (4 * mu - 6 * v)) := by gcongr
        _ = C ^ 6 * T ^ (1 + 4 * mu - 6 * v) := by
          rw [← Real.rpow_one T, ← Real.rpow_add hTPos]
          ring
    calc
      (3 * T) * min ((P : ℝ) / L ^ 2)
          ((P : ℝ) ^ 4 / L ^ 6) =
          3 * min (T * ((P : ℝ) / L ^ 2))
            (T * ((P : ℝ) ^ 4 / L ^ 6)) := by
              rw [mul_min_of_nonneg (by positivity : 0 ≤ T)]
              ring
      _ ≤ 3 * min (C ^ 6 * T ^ (1 + mu - 2 * v))
          (C ^ 6 * T ^ (1 + 4 * mu - 6 * v)) := by gcongr
      _ = C ^ 6 * (3 * min (T ^ (1 + mu - 2 * v))
          (T ^ (1 + 4 * mu - 6 * v))) := by
            rw [← mul_min_of_nonneg (by positivity : 0 ≤ C ^ 6)]
            ring
  linarith

/-- The `d`, detector and logarithmic losses introduced by the literal dual
cutoff fit in one explicit exponent budget. -/
theorem reflected_power_envelope_le_endpoint
    {sigma tau₀ tau d u eta T : ℝ}
    (hsigmaLower : 1 / 2 < sigma) (hsigmaUpper : sigma < 1)
    (hcert : EndpointScaleCertificate sigma tau₀)
    (htau₀ : tau₀ < tau) (htauOne : 1 < tau) (htauTwo : tau < 2)
    (htauUpper : tau < 4 * tau₀ / 3)
    (hNotWeyl : 6 * sigma - 3 ≤ tau)
    (hd : 0 ≤ d) (hu : 0 ≤ u) (huD : u ≤ d) (heta : 0 ≤ eta)
    (hT : 1 ≤ T) :
    let mu := 1 + d - 1 / tau
    let v := 1 / 2 - u - d * sigma + (sigma - 1) / tau - eta
    T ^ (2 * (mu - v)) +
        3 * min (T ^ (1 + mu - 2 * v))
          (T ^ (1 + 4 * mu - 6 * v)) ≤
      4 * T ^ (3 * (1 - sigma) / tau₀ + 16 * d + 6 * eta) := by
  dsimp only
  let E := mediumReflectedMHHExponent sigma tau
  have hE := mediumReflectedMHHExponent_le_endpoint hsigmaLower hsigmaUpper
    hcert htau₀ htauOne htauTwo htauUpper hNotWeyl
  have hSigmaNonneg : 0 ≤ sigma := by linarith
  have hLoss₁ :
      2 * ((1 + d - 1 / tau) -
          (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta)) ≤
        (1 - 2 * sigma / tau) + 16 * d + 6 * eta := by
    nlinarith [mul_nonneg hd (sub_nonneg.mpr hsigmaUpper.le)]
  have hLoss₂ :
      1 + (1 + d - 1 / tau) -
          2 * (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta) ≤
        (1 + (1 - 2 * sigma) / tau) + 16 * d + 6 * eta := by
    nlinarith [mul_nonneg hd (sub_nonneg.mpr hsigmaUpper.le)]
  have hLoss₃ :
      1 + 4 * (1 + d - 1 / tau) -
          6 * (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta) ≤
        (2 + (2 - 6 * sigma) / tau) + 16 * d + 6 * eta := by
    nlinarith [mul_nonneg hd (sub_nonneg.mpr hsigmaUpper.le)]
  have hE₁ : 1 - 2 * sigma / tau ≤ E := by
    dsimp only [E, mediumReflectedMHHExponent]
    exact le_max_left _ _
  have hEmin : min (1 + (1 - 2 * sigma) / tau)
      (2 + (2 - 6 * sigma) / tau) ≤ E := by
    dsimp only [E, mediumReflectedMHHExponent]
    exact le_max_right _ _
  have hExp₁ :
      2 * ((1 + d - 1 / tau) -
          (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta)) ≤
        3 * (1 - sigma) / tau₀ + 16 * d + 6 * eta :=
    hLoss₁.trans (add_le_add_right (hE₁.trans hE) _)
  have hMinLoss :
      min
          (1 + (1 + d - 1 / tau) -
            2 * (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta))
          (1 + 4 * (1 + d - 1 / tau) -
            6 * (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta)) ≤
        min (1 + (1 - 2 * sigma) / tau)
            (2 + (2 - 6 * sigma) / tau) + 16 * d + 6 * eta := by
    have hmin := min_le_min hLoss₂ hLoss₃
    simpa only [min_add_add_right] using hmin
  have hExpMin :
      min
          (1 + (1 + d - 1 / tau) -
            2 * (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta))
          (1 + 4 * (1 + d - 1 / tau) -
            6 * (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta)) ≤
        3 * (1 - sigma) / tau₀ + 16 * d + 6 * eta :=
    hMinLoss.trans (add_le_add_right (hEmin.trans hE) _)
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have hPow₁ := Real.rpow_le_rpow_of_exponent_le hT hExp₁
  have hPowMin := Real.rpow_le_rpow_of_exponent_le hT hExpMin
  have hMinPow : min
      (T ^ (1 + (1 + d - 1 / tau) -
        2 * (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta)))
      (T ^ (1 + 4 * (1 + d - 1 / tau) -
        6 * (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta))) ≤
      T ^ (3 * (1 - sigma) / tau₀ + 16 * d + 6 * eta) := by
    rw [← Real.rpow_min hTPos]
    exact hPowMin
  nlinarith [Real.rpow_nonneg hTPos.le
    (3 * (1 - sigma) / tau₀ + 16 * d + 6 * eta)]
-/

/-- Inverting the physical scale identity is legitimate for the positive
natural base and positive logarithmic scale used by the medium branch. -/
theorem natCast_eq_rpow_inv_of_rpow_eq
    {T tau : ℝ} {Q : ℕ} (hQ : 1 < Q) (htau : 0 < tau)
    (hScale : (Q : ℝ) ^ tau = T) :
    (Q : ℝ) = T ^ (1 / tau) := by
  rw [← hScale, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ Q)]
  have hmul : tau * (1 / tau) = 1 := by field_simp [htau.ne']
  rw [hmul, Real.rpow_one]

/-- On a medium scale the expanded dual cutoff is still below the literal
sharp zeta cutoff.  Consequently its `Nat.clog` loss is already covered by
the source-selection logarithmic budget. -/
theorem mediumTypeIDualCutoff_le_sharpZetaCutoff
    {T d tau : ℝ} {Q : ℕ}
    (hT : 8 ≤ T) (_hd : 0 ≤ d) (hdHalf : d ≤ 1 / 2)
    (hQ : 1 < Q) (_htau : 0 < tau) (htauTwo : tau < 2)
    (hScale : (Q : ℝ) ^ tau = T) :
    mediumTypeIDualCutoff T d Q ≤ ⌊sharpZetaCutoff T⌋₊ := by
  have hTPos : 0 < T := by linarith
  have hTOne : 1 ≤ T := by linarith
  have hQReal : (1 : ℝ) < Q := by exact_mod_cast hQ
  have hSqrt : T ^ (1 / 2 : ℝ) ≤ (Q : ℝ) := by
    rw [← hScale, ← Real.rpow_mul (by positivity)]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      hQReal.le (by nlinarith : tau * (1 / 2 : ℝ) ≤ 1)
  have hTd : T ^ d ≤ (Q : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hTOne hdHalf).trans hSqrt
  have hSplit : T ^ (1 + d) = T * T ^ d := by
    rw [Real.rpow_add hTPos, Real.rpow_one]
  have hRatio : T ^ (1 + d) / Q ≤ T := by
    rw [hSplit, div_le_iff₀ (by positivity : (0 : ℝ) < Q)]
    nlinarith
  have hSharp : T ≤ sharpZetaCutoff T :=
    (show T ≤ 4 * T by nlinarith).trans
      (four_mul_lt_sharpZetaCutoff T).le
  unfold mediumTypeIDualCutoff
  exact Nat.floor_mono (hRatio.trans hSharp)

/-- The exact logarithmic product needed by the reflected normalized
threshold.  No new logarithmic estimate is required once the dual cutoff is
proved to lie below the sharp cutoff. -/
theorem medium_reflected_clog_product_le
    {T d tau : ℝ} {Q : ℕ}
    (hT : 8 ≤ T) (hd : 0 ≤ d) (hdHalf : d ≤ 1 / 2)
    (hQ : 1 < Q) (htau : 0 < tau) (htauTwo : tau < 2)
    (hScale : (Q : ℝ) ^ tau = T) :
    ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) *
        (Nat.clog 2 (mediumTypeIDualCutoff T d Q) : ℝ) ≤
      ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) *
        (Nat.clog 2 (⌊sharpZetaCutoff T⌋₊ + 1) : ℝ) := by
  have hM := mediumTypeIDualCutoff_le_sharpZetaCutoff hT hd hdHalf hQ htau
    htauTwo hScale
  have hA : ⌊sharpZetaCutoff T⌋₊ ≤ ⌊sharpZetaCutoff T⌋₊ + 1 := by omega
  have hClog : Nat.clog 2 (mediumTypeIDualCutoff T d Q) ≤
      Nat.clog 2 (⌊sharpZetaCutoff T⌋₊ + 1) :=
    Nat.clog_mono_right 2 (hM.trans hA)
  gcongr

/-- The fixed constant in the normalized reflected-threshold lower bound. -/
noncomputable def mediumReflectedThresholdConstant (Clog CK : ℝ) : ℝ :=
  max 1 ((128 * Clog * CK * (typeIDyadicCutoffMellinL1 + 1)) /
    (3 * Real.pi))

/-- Lower bound for the literal normalized reflected threshold.  It uses
the actual detector threshold, kernel, natural dual cutoff and both `clog`
factors; the displayed exponent is exactly the one used in the reflected
MHH arithmetic above.  The constant is displayed explicitly, making its
uniformity in `T`, the source scale and the selected dyadic block literal. -/
theorem medium_reflected_threshold_explicit_lower
    {sigma T tau d u eta Clog CK : ℝ} {Q M : ℕ}
    (hsigma : 0 ≤ sigma) (hT : 1 ≤ T) (hQ : 1 < Q)
    (hM : 1 < M) (htau : 0 < tau)
    (hScale : (Q : ℝ) ^ tau = T)
    (hMUpper : (M : ℝ) ≤ T ^ (1 + d - 1 / tau))
    (hClog : 0 < Clog)
    (hLogs :
      ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) *
          (Nat.clog 2 M : ℝ) ≤ Clog * T ^ eta)
    (hCK : 0 < CK)
    (hKernel : mediumTypeIStationaryKernel sigma T Q ≤
      CK * T ^ (-sigma - 1 / 2)) :
    let V := ((3 / 4) * (T ^ (-u) / 2)) /
        (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ)
    let R := (Real.pi * V) /
        (8 * (Q : ℝ) * mediumTypeIStationaryKernel sigma T Q *
          (typeIDyadicCutoffMellinL1 + 1))
    let S := R / (2 * (M : ℝ) ^ sigma)
    T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta) /
        mediumReflectedThresholdConstant Clog CK ≤
      S / Nat.clog 2 M := by
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have hQPos : (0 : ℝ) < Q := by positivity
  have hMPos : (0 : ℝ) < M := by positivity
  have hClogMNat : 0 < Nat.clog 2 M := Nat.clog_pos Nat.one_lt_two hM
  have hClogM : (0 : ℝ) < Nat.clog 2 M := by exact_mod_cast hClogMNat
  have hAOne : 1 < ⌊sharpZetaCutoff T⌋₊ := by
    apply lt_of_lt_of_le (by omega : 1 < (2 : ℕ))
    apply Nat.le_floor
    exact (show (2 : ℝ) ≤ 4 * T by nlinarith).trans
      (four_mul_lt_sharpZetaCutoff T).le
  have hClogA : (0 : ℝ) <
      (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) := by positivity
  have hMass : 0 < typeIDyadicCutoffMellinL1 + 1 := by
    linarith [typeIDyadicCutoffMellinL1_nonneg]
  have hKernelPos : 0 < mediumTypeIStationaryKernel sigma T Q :=
    mediumTypeIStationaryKernel_pos hTPos (lt_trans Nat.zero_lt_one hQ)
  have hQEq : (Q : ℝ) = T ^ (1 / tau) :=
    natCast_eq_rpow_inv_of_rpow_eq hQ htau hScale
  have hMPow : (M : ℝ) ^ sigma ≤
      T ^ (sigma * (1 + d - 1 / tau)) := by
    calc
      (M : ℝ) ^ sigma ≤ (T ^ (1 + d - 1 / tau)) ^ sigma :=
        Real.rpow_le_rpow (Nat.cast_nonneg M) hMUpper hsigma
      _ = T ^ (sigma * (1 + d - 1 / tau)) := by
        rw [← Real.rpow_mul hTPos.le]
        ring_nf
  let C₀ : ℝ :=
    (128 * Clog * CK * (typeIDyadicCutoffMellinL1 + 1)) /
      (3 * Real.pi)
  let C : ℝ := max 1 C₀
  have hC₀ : 0 < C₀ := by dsimp only [C₀]; positivity
  have hC : 1 ≤ C := le_max_left _ _
  change T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta) / C ≤ _
  have hDenBound :
      (((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) *
          (Nat.clog 2 M : ℝ)) *
          (Q : ℝ) * mediumTypeIStationaryKernel sigma T Q *
            ((M : ℝ) ^ sigma) ≤
        (Clog * CK) *
          T ^ (eta + 1 / tau - sigma - 1 / 2 +
            sigma * (1 + d - 1 / tau)) := by
    calc
      (((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) *
          (Nat.clog 2 M : ℝ)) *
          (Q : ℝ) * mediumTypeIStationaryKernel sigma T Q *
            ((M : ℝ) ^ sigma) ≤
        (Clog * T ^ eta) * T ^ (1 / tau) *
          (CK * T ^ (-sigma - 1 / 2)) *
            T ^ (sigma * (1 + d - 1 / tau)) := by
              rw [hQEq]
              gcongr
      _ = (Clog * CK) *
          T ^ (eta + 1 / tau - sigma - 1 / 2 +
            sigma * (1 + d - 1 / tau)) := by
            have hPowCombine :
                T ^ eta * T ^ (1 / tau) * T ^ (-sigma - 1 / 2) *
                    T ^ (sigma * (1 + d - 1 / tau)) =
                  T ^ (eta + 1 / tau - sigma - 1 / 2 +
                    sigma * (1 + d - 1 / tau)) := by
              rw [← Real.rpow_add hTPos, ← Real.rpow_add hTPos,
                ← Real.rpow_add hTPos]
              congr 1
              ring
            rw [← hPowCombine]
            ring
  have hCore :
      T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta) / C₀ ≤
        (Real.pi * (((3 / 4) * (T ^ (-u) / 2)) /
          (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ))) /
          (8 * (Q : ℝ) * mediumTypeIStationaryKernel sigma T Q *
            (typeIDyadicCutoffMellinL1 + 1)) /
          (2 * (M : ℝ) ^ sigma) / Nat.clog 2 M := by
    let LA : ℝ := (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ)
    let LM : ℝ := Nat.clog 2 M
    let K₀ : ℝ := mediumTypeIStationaryKernel sigma T Q
    let mass : ℝ := typeIDyadicCutoffMellinL1 + 1
    have hLA : 0 < LA := by simpa only [LA] using hClogA
    have hLM : 0 < LM := by simpa only [LM] using hClogM
    have hK₀ : 0 < K₀ := by simpa only [K₀] using hKernelPos
    have hmass : 0 < mass := by simpa only [mass] using hMass
    let DBig : ℝ := 128 * LA * LM * (Q : ℝ) * K₀ * mass * (M : ℝ) ^ sigma
    have hDBig : 0 < DBig := by dsimp only [DBig]; positivity
    have hRhs :
        (Real.pi * (((3 / 4) * (T ^ (-u) / 2)) /
          (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ))) /
          (8 * (Q : ℝ) * mediumTypeIStationaryKernel sigma T Q *
            (typeIDyadicCutoffMellinL1 + 1)) /
          (2 * (M : ℝ) ^ sigma) / Nat.clog 2 M =
        (3 * Real.pi * T ^ (-u)) / DBig := by
      dsimp only [DBig, LA, LM, K₀, mass]
      field_simp
      ring
    rw [hRhs, div_le_div_iff₀ hC₀ hDBig]
    have hPowEq :
        T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta) *
          T ^ (eta + 1 / tau - sigma - 1 / 2 +
            sigma * (1 + d - 1 / tau)) = T ^ (-u) := by
      rw [← Real.rpow_add hTPos]
      congr 1
      ring
    have hScaled :
        (((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) *
            (Nat.clog 2 M : ℝ) * (Q : ℝ) *
            mediumTypeIStationaryKernel sigma T Q * ((M : ℝ) ^ sigma)) *
            T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta) ≤
          (Clog * CK) * T ^ (-u) := by
      calc
        _ ≤ ((Clog * CK) *
            T ^ (eta + 1 / tau - sigma - 1 / 2 +
              sigma * (1 + d - 1 / tau))) *
              T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta) := by
                gcongr
        _ = (Clog * CK) *
            (T ^ (eta + 1 / tau - sigma - 1 / 2 +
              sigma * (1 + d - 1 / tau)) *
              T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta)) := by
                ring
        _ = (Clog * CK) * T ^ (-u) := by
          rw [mul_comm
            (T ^ (eta + 1 / tau - sigma - 1 / 2 +
              sigma * (1 + d - 1 / tau)))
            (T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta)),
            hPowEq]
    dsimp only [DBig, LA, LM, K₀, mass, C₀]
    calc
      T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta) *
          (128 *
            ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) *
            (Nat.clog 2 M : ℝ) * (Q : ℝ) *
            mediumTypeIStationaryKernel sigma T Q *
            (typeIDyadicCutoffMellinL1 + 1) * (M : ℝ) ^ sigma) =
          (128 * (typeIDyadicCutoffMellinL1 + 1)) *
            ((((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) *
              (Nat.clog 2 M : ℝ) * (Q : ℝ) *
              mediumTypeIStationaryKernel sigma T Q * ((M : ℝ) ^ sigma)) *
              T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta)) := by ring
      _ ≤ (128 * (typeIDyadicCutoffMellinL1 + 1)) *
          ((Clog * CK) * T ^ (-u)) := by gcongr
      _ = 3 * Real.pi * T ^ (-u) *
          (128 * Clog * CK * (typeIDyadicCutoffMellinL1 + 1) /
            (3 * Real.pi)) := by field_simp [Real.pi_ne_zero]
  exact (div_le_div_of_nonneg_left (Real.rpow_nonneg hTPos.le _)
    hC₀ (le_max_right (1 : ℝ) C₀)).trans hCore

/-- Existential compatibility wrapper for callers that only need a named
uniform constant. -/
theorem exists_medium_reflected_threshold_constant
    {sigma T tau d u eta Clog CK : ℝ} {Q M : ℕ}
    (hsigma : 0 ≤ sigma) (hT : 1 ≤ T) (hQ : 1 < Q)
    (hM : 1 < M) (htau : 0 < tau)
    (hScale : (Q : ℝ) ^ tau = T)
    (hMUpper : (M : ℝ) ≤ T ^ (1 + d - 1 / tau))
    (hClog : 0 < Clog)
    (hLogs :
      ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) *
          (Nat.clog 2 M : ℝ) ≤ Clog * T ^ eta)
    (hCK : 0 < CK)
    (hKernel : mediumTypeIStationaryKernel sigma T Q ≤
      CK * T ^ (-sigma - 1 / 2)) :
    ∃ C : ℝ, 1 ≤ C ∧
      let V := ((3 / 4) * (T ^ (-u) / 2)) /
        (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ)
      let R := (Real.pi * V) /
        (8 * (Q : ℝ) * mediumTypeIStationaryKernel sigma T Q *
          (typeIDyadicCutoffMellinL1 + 1))
      let S := R / (2 * (M : ℝ) ^ sigma)
      T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta) / C ≤
        S / Nat.clog 2 M := by
  refine ⟨mediumReflectedThresholdConstant Clog CK, le_max_left _ _, ?_⟩
  exact medium_reflected_threshold_explicit_lower hsigma hT hQ hM htau
    hScale hMUpper hClog hLogs hCK hKernel

/-- On every genuine medium source scale, the exponent in the normalized
reflected threshold has a fixed positive margin.  The estimate uses the
literal `u = d^4` and the later choice `eta = d`; no asymptotic `o(1)` is
inserted. -/
theorem medium_reflected_threshold_exponent_lower
    {sigma tau d u : ℝ}
    (_hsigma : 1 / 2 < sigma) (hsigmaUpper : sigma < 1)
    (htau : 1 < tau) (hd : 0 < d)
    (hdGap : d ≤ (sigma - 1 / 2) / 1000)
    (huD : u ≤ d) :
    (sigma - 1 / 2) / 2 ≤
      1 / 2 - u - d * sigma + (sigma - 1) / tau - d := by
  have htauPos : 0 < tau := by linarith
  have hFrac : sigma - 1 ≤ (sigma - 1) / tau := by
    rw [le_div_iff₀ htauPos]
    have hneg : sigma - 1 < 0 := by linarith
    nlinarith
  have hSmall : 3 * d ≤ (sigma - 1 / 2) / 2 := by
    have hgap : 0 < sigma - 1 / 2 := by linarith
    nlinarith
  have hdSigma : d * sigma ≤ d :=
    mul_le_of_le_one_right hd.le hsigmaUpper.le
  linarith

/-- The normalization loss `P^sigma/L` of a retained reflected dyadic block
costs at most `T^(4d)`, up to the fixed threshold constant.  This is the
finite algebraic cancellation behind the powered reflected route. -/
theorem reflected_normalization_loss_le_four_d
    {sigma tau d u T C L : ℝ} {P M : ℕ}
    (hsigmaHalf : 1 / 2 ≤ sigma) (hsigmaUpper : sigma < 1)
    (htau : 1 < tau) (htauTwo : tau < 2)
    (hd : 0 ≤ d) (huD : u ≤ d)
    (hT : 1 ≤ T) (hC : 1 ≤ C) (hL : 0 < L)
    (hPM : P ≤ M)
    (hM : (M : ℝ) ≤ T ^ (1 + d - 1 / tau))
    (hLLower :
      T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - d) / C ≤ L) :
    max 1 ((P : ℝ) ^ sigma / L) ≤ C * T ^ (4 * d) := by
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have htauPos : 0 < tau := by linarith
  have hPToM : (P : ℝ) ^ sigma ≤ (M : ℝ) ^ sigma :=
    Real.rpow_le_rpow (Nat.cast_nonneg P) (by exact_mod_cast hPM) (by linarith)
  have hMPow : (M : ℝ) ^ sigma ≤
      T ^ (sigma * (1 + d - 1 / tau)) := by
    calc
      (M : ℝ) ^ sigma ≤ (T ^ (1 + d - 1 / tau)) ^ sigma :=
        Real.rpow_le_rpow (Nat.cast_nonneg M) hM (by linarith)
      _ = T ^ (sigma * (1 + d - 1 / tau)) := by
        rw [← Real.rpow_mul hTPos.le]
        ring_nf
  let v : ℝ := 1 / 2 - u - d * sigma + (sigma - 1) / tau - d
  have hBasePos : 0 < T ^ v / C := by dsimp only [v]; positivity
  have hRatio : (P : ℝ) ^ sigma / L ≤
      C * T ^ (sigma * (1 + d - 1 / tau) - v) := by
    calc
      (P : ℝ) ^ sigma / L ≤
          T ^ (sigma * (1 + d - 1 / tau)) / (T ^ v / C) :=
        (div_le_div_of_nonneg_right (hPToM.trans hMPow) hL.le).trans
          (div_le_div_of_nonneg_left (Real.rpow_nonneg hTPos.le _)
            hBasePos hLLower)
      _ = C * T ^ (sigma * (1 + d - 1 / tau) - v) := by
        calc
          T ^ (sigma * (1 + d - 1 / tau)) / (T ^ v / C) =
              C * (T ^ (sigma * (1 + d - 1 / tau)) / T ^ v) := by
                field_simp [show C ≠ 0 by linarith,
                  (Real.rpow_pos_of_pos hTPos v).ne']
          _ = C * T ^ (sigma * (1 + d - 1 / tau) - v) := by
                rw [← Real.rpow_sub hTPos]
  have hCoreNonpos :
      sigma - 1 / 2 + (1 - 2 * sigma) / tau ≤ 0 := by
    have hProd : (2 * sigma - 1) * (tau - 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    have hNum : (sigma - 1 / 2) * tau + (1 - 2 * sigma) ≤ 0 := by
      nlinarith
    rw [show sigma - 1 / 2 + (1 - 2 * sigma) / tau =
      ((sigma - 1 / 2) * tau + (1 - 2 * sigma)) / tau by
        field_simp [htauPos.ne']]
    exact div_nonpos_of_nonpos_of_nonneg hNum htauPos.le
  have hExp : sigma * (1 + d - 1 / tau) - v ≤ 4 * d := by
    have hdSigma : d * sigma ≤ d :=
      mul_le_of_le_one_right hd hsigmaUpper.le
    have hLoss : u + d + 2 * d * sigma ≤ 4 * d := by linarith
    dsimp only [v]
    have hIdentity :
        sigma * (1 + d - 1 / tau) -
            (1 / 2 - u - d * sigma + (sigma - 1) / tau - d) =
          (sigma - 1 / 2 + (1 - 2 * sigma) / tau) +
            (u + d + 2 * d * sigma) := by ring
    rw [hIdentity]
    linarith
  have hRatioFinal : (P : ℝ) ^ sigma / L ≤ C * T ^ (4 * d) :=
    hRatio.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hT hExp) (by linarith : 0 ≤ C))
  have hOne : 1 ≤ C * T ^ (4 * d) := by
    have hPow : 1 ≤ T ^ (4 * d) := Real.one_le_rpow hT (by positivity)
    nlinarith [mul_le_mul hC hPow (by norm_num) (by linarith : 0 ≤ C)]
  exact max_le hOne hRatioFinal

/-- Uniform powered-threshold envelope for a reflected dyadic block.  The
factor `T^(4*d*k)` is exactly the `k`-fold normalization cost established by
`reflected_normalization_loss_le_four_d`; the remaining factors are the same
finite powered MHH loss used by the source-facing consumers. -/
theorem reflected_powered_threshold_loss_le_envelope
    {C₀ C d sigma T D : ℝ} {P k B : ℕ}
    (hC₀ : 1 ≤ C₀) (hC : 1 ≤ C) (hd : 0 ≤ d)
    (hsigmaOne : sigma ≤ 1) (hT : Real.exp 1 ≤ T)
    (hD : 0 < D) (hDUpper : D ≤ C₀ * T ^ (4 * d))
    (hP : 0 < P) (hk : 0 < k) (hkB : k ≤ B) :
    let E := (2 : ℝ) ^ B * C₀ ^ B * C
    typeIIPoweredThresholdLoss C ((P : ℝ) ^ sigma) D d sigma P k ≤
      1 + T ^ (4 * d * k) *
        classicalTypeIIPowerLoss E d T k (P ^ k) := by
  dsimp only
  let E : ℝ := (2 : ℝ) ^ B * C₀ ^ B * C
  have hTOne : 1 ≤ T := by
    calc
      1 = Real.exp 0 := by rw [Real.exp_zero]
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
      _ ≤ T := hT
  have hTPos : 0 < T := zero_lt_one.trans_le hTOne
  have hLogOne : 1 ≤ Real.log T := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hT
  have hLogFactor : 1 ≤ (4 * Real.log T) ^ k := by
    exact one_le_pow₀ (by nlinarith)
  have hDPow : D ^ k ≤ C₀ ^ B * T ^ (4 * d * k) := by
    have hTPow : (T ^ (4 * d)) ^ k = T ^ (4 * d * (k : ℝ)) := by
      calc
        (T ^ (4 * d)) ^ k = (T ^ (4 * d)) ^ (k : ℝ) :=
          (Real.rpow_natCast (T ^ (4 * d)) k).symm
        _ = T ^ ((4 * d) * (k : ℝ)) :=
          (Real.rpow_mul hTPos.le (4 * d) k).symm
    calc
      D ^ k ≤ (C₀ * T ^ (4 * d)) ^ k :=
        pow_le_pow_left₀ hD.le hDUpper k
      _ = C₀ ^ k * (T ^ (4 * d)) ^ k := by rw [mul_pow]
      _ ≤ C₀ ^ B * (T ^ (4 * d)) ^ k := by
        gcongr
      _ = C₀ ^ B * T ^ (4 * d * k) := by rw [hTPow]
  have hPReal : (0 : ℝ) < P := by exact_mod_cast hP
  have hCancel :
      (((2 ^ k * P ^ k : ℕ) : ℝ) ^ sigma) /
          (((P : ℝ) ^ sigma) ^ k) = (((2 : ℝ) ^ k) ^ sigma) := by
    push_cast
    rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k)
      (pow_nonneg hPReal.le k)]
    have hPPow : (((P : ℝ) ^ k) ^ sigma) = ((P : ℝ) ^ sigma) ^ k := by
      calc
        (((P : ℝ) ^ k) ^ sigma) = (((P : ℝ) ^ (k : ℝ)) ^ sigma) := by
          rw [Real.rpow_natCast]
        _ = (P : ℝ) ^ ((k : ℝ) * sigma) :=
          (Real.rpow_mul hPReal.le k sigma).symm
        _ = (P : ℝ) ^ (sigma * (k : ℝ)) := by congr 1; ring
        _ = (((P : ℝ) ^ sigma) ^ (k : ℝ)) :=
          Real.rpow_mul hPReal.le sigma k
        _ = ((P : ℝ) ^ sigma) ^ k := Real.rpow_natCast _ _
    rw [hPPow]
    field_simp [(Real.rpow_pos_of_pos hPReal sigma).ne']
  have hTwoPowSigma : (((2 : ℝ) ^ k) ^ sigma) ≤ (2 : ℝ) ^ B := by
    have hBase : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    calc
      (((2 : ℝ) ^ k) ^ sigma) ≤ (((2 : ℝ) ^ k) ^ (1 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hBase hsigmaOne
      _ = (2 : ℝ) ^ k := by norm_num
      _ ≤ (2 : ℝ) ^ B := pow_le_pow_right₀ (by norm_num) hkB
  have hScale :
      (((2 ^ k * P ^ k : ℕ) : ℝ) ^ d) ≤
        ((((2 : ℝ) ^ k) * ((P ^ k : ℕ) : ℝ)) ^ (2 * d)) := by
    have hCast : ((2 ^ k * P ^ k : ℕ) : ℝ) =
        ((2 : ℝ) ^ k) * ((P ^ k : ℕ) : ℝ) := by norm_num
    rw [hCast]
    have hBaseNat : 1 ≤ 2 ^ k * P ^ k := by
      exact Nat.one_le_iff_ne_zero.mpr
        (mul_ne_zero (pow_ne_zero _ (by omega)) (pow_ne_zero _ hP.ne'))
    have hBaseReal : (1 : ℝ) ≤
        ((2 : ℝ) ^ k) * ((P ^ k : ℕ) : ℝ) := by exact_mod_cast hBaseNat
    exact Real.rpow_le_rpow_of_exponent_le hBaseReal (by linarith)
  have hRaw :
      (((((2 ^ k * P ^ k : ℕ) : ℝ) ^ sigma) * D ^ k *
          (C * (((2 ^ k * P ^ k : ℕ) : ℝ) ^ d)) * k) /
            (((P : ℝ) ^ sigma) ^ k)) ≤
        T ^ (4 * d * k) *
          classicalTypeIIPowerLoss E d T k (P ^ k) := by
    rw [div_eq_mul_inv]
    have hIdentity :
        (((2 ^ k * P ^ k : ℕ) : ℝ) ^ sigma) *
            (((P : ℝ) ^ sigma) ^ k)⁻¹ = (((2 : ℝ) ^ k) ^ sigma) := by
      rw [← div_eq_mul_inv]
      exact hCancel
    dsimp only [classicalTypeIIPowerLoss, E]
    calc
      (((2 ^ k * P ^ k : ℕ) : ℝ) ^ sigma * D ^ k *
            (C * (((2 ^ k * P ^ k : ℕ) : ℝ) ^ d)) * (k : ℝ) *
              (((P : ℝ) ^ sigma) ^ k)⁻¹) =
          ((((2 ^ k * P ^ k : ℕ) : ℝ) ^ sigma *
              (((P : ℝ) ^ sigma) ^ k)⁻¹) * D ^ k *
                (C * ((2 ^ k * P ^ k : ℕ) : ℝ) ^ d) * (k : ℝ)) := by
            push_cast
            ring
      _ = (((2 : ℝ) ^ k) ^ sigma * D ^ k *
            (C * ((2 ^ k * P ^ k : ℕ) : ℝ) ^ d) * (k : ℝ)) := by
          rw [hIdentity]
      _ ≤ (2 : ℝ) ^ B * (C₀ ^ B * T ^ (4 * d * k)) *
            (C * ((((2 : ℝ) ^ k) * ((P ^ k : ℕ) : ℝ)) ^ (2 * d))) *
              (k : ℝ) := by gcongr
      _ ≤ (2 : ℝ) ^ B * (C₀ ^ B * T ^ (4 * d * k)) *
            (C * ((((2 : ℝ) ^ k) * ((P ^ k : ℕ) : ℝ)) ^ (2 * d))) *
              (k : ℝ) * (4 * Real.log T) ^ k := by
          exact le_mul_of_one_le_right (by positivity) hLogFactor
      _ = T ^ (4 * d * k) *
          (((2 : ℝ) ^ B * C₀ ^ B * C) *
            ((((2 : ℝ) ^ k) * ((P ^ k : ℕ) : ℝ)) ^ (2 * d)) *
              (k : ℝ) * (4 * Real.log T) ^ k) := by ring
  unfold typeIIPoweredThresholdLoss
  apply max_le
  · have hLossNonneg : 0 ≤ T ^ (4 * d * k) *
        classicalTypeIIPowerLoss E d T k (P ^ k) := by
      dsimp only [classicalTypeIIPowerLoss, E]
      positivity
    linarith
  · exact hRaw.trans (le_add_of_nonneg_left (by norm_num))

/-- A fixed positive-power threshold forces the dyadic block selected from
a unit-coefficient family to have uniformly bounded logarithmic height
scale.  Both the natural cast and the eventual constant absorption remain
explicit. -/
theorem eventually_threshold_forces_logarithmic_scale_upper
    {g C : ℝ} (hg : 0 < g) (hC : 1 ≤ C) :
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ {T L : ℝ} {P : ℕ}, T₀ ≤ T →
      0 < L → T ^ g / C ≤ L → L ≤ (P : ℝ) →
      1 < P ∧ typeILogarithmicScale T P ≤ 2 / g := by
  have hhalf : 0 < g / 2 := by positivity
  have hTop := tendsto_rpow_atTop hhalf
  have hEventually := (tendsto_atTop.1 hTop) (max 2 C)
  rw [eventually_atTop] at hEventually
  obtain ⟨Tpow, hTpow⟩ := hEventually
  let T₀ : ℝ := max 2 Tpow
  refine ⟨T₀, le_max_left _ _, ?_⟩
  intro T L P hT hL hTL hLP
  have hTTwo : 2 ≤ T := (le_max_left _ _).trans hT
  have hTPow : Tpow ≤ T := (le_max_right _ _).trans hT
  have hTPos : 0 < T := by linarith
  have hRoot : max 2 C ≤ T ^ (g / 2) := hTpow T hTPow
  have hRootTwo : 2 ≤ T ^ (g / 2) := (le_max_left _ _).trans hRoot
  have hRootC : C ≤ T ^ (g / 2) := (le_max_right _ _).trans hRoot
  have hSplit : T ^ g = T ^ (g / 2) * T ^ (g / 2) := by
    rw [← Real.rpow_add hTPos]
    congr 1
    ring
  have hRootToRatio : T ^ (g / 2) ≤ T ^ g / C := by
    rw [hSplit, le_div_iff₀ (by linarith : 0 < C)]
    exact mul_le_mul_of_nonneg_left hRootC (Real.rpow_nonneg hTPos.le _)
  have hRootP : T ^ (g / 2) ≤ (P : ℝ) :=
    hRootToRatio.trans (hTL.trans hLP)
  have hPtwo : 2 ≤ P := by exact_mod_cast hRootTwo.trans hRootP
  have hPOne : 1 < P := by omega
  have hRaise := Real.rpow_le_rpow
    (Real.rpow_nonneg hTPos.le _) hRootP (by positivity : 0 ≤ 2 / g)
  have hCancel : (T ^ (g / 2)) ^ (2 / g) = T := by
    rw [← Real.rpow_mul hTPos.le]
    have : g / 2 * (2 / g) = 1 := by field_simp [hg.ne']
    rw [this, Real.rpow_one]
  refine ⟨hPOne, (Real.logb_le_iff_le_rpow
    (by exact_mod_cast hPOne) hTPos).mpr ?_⟩
  simpa only [hCancel] using hRaise

/-- The source-normalized reflection radius grows by a fixed positive power.
This is the quantitative content of the complementary-margin lemma after
allowing one `T^d` for the source `clog` loss. -/
theorem medium_reflection_radius_exponent_pos
    {sigma d u tau : ℝ}
    (hsigma : 1 / 2 < sigma)
    (hd : 0 < d) (hdGap : d ≤ (sigma - 1 / 2) / 1000)
    (huD : u ≤ d)
    (hMargin : 2 * sigma - 200 * d ≤ tau) :
    0 < sigma + 1 / 2 - 1 / tau - u - d := by
  let a : ℝ := 2 * sigma - 200 * d
  have haOne : 1 < a := by
    dsimp only [a]
    have hScaled : 200 * d ≤ (sigma - 1 / 2) / 5 := by
      calc
        200 * d ≤ 200 * ((sigma - 1 / 2) / 1000) := by gcongr
        _ = (sigma - 1 / 2) / 5 := by ring
    linarith
  have htau : 1 < tau := haOne.trans_le (by simpa only [a] using hMargin)
  have hInv : 1 / tau ≤ 1 / a := by
    exact one_div_le_one_div_of_le (by linarith) (by simpa only [a] using hMargin)
  have hProduct : 1 < (sigma + 1 / 2 - u - d) * a := by
    dsimp only [a]
    have hSigmaGap : 0 < sigma - 1 / 2 := by linarith
    have hTwoD : 2 * d ≤ (sigma - 1 / 2) / 500 := by linarith
    nlinarith [mul_pos hSigmaGap hSigmaGap]
  have hCore : 1 / a < sigma + 1 / 2 - u - d := by
    rw [div_lt_iff₀ (by linarith : 0 < a)]
    simpa only [one_mul] using hProduct
  linarith

/-- Eventual finite form of the preceding radius growth.  The proof keeps
the exact source `clog`, Fourier kernel constant and Mellin mass. -/
theorem eventually_medium_reflection_radius_two
    {sigma d u : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaUpper : sigma < 1)
    (hd : 0 < d) (hdGap : d ≤ (sigma - 1 / 2) / 1000)
    (huD : u ≤ d) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ {T tau : ℝ} {Q : ℕ}, T₀ ≤ T →
      1 < Q → 1 < tau → tau < 2 →
      (Q : ℝ) ^ tau = T →
      2 * sigma - 200 * d ≤ tau →
      2 ≤ (Real.pi *
        (((3 / 4) * (T ^ (-u) / 2)) /
          (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ))) /
        (8 * (Q : ℝ) * mediumTypeIStationaryKernel sigma T Q *
          (typeIDyadicCutoffMellinL1 + 1)) := by
  have hrho : 0 < sigma + 1 / 2 -
      1 / (2 * sigma - 200 * d) - u - d :=
    medium_reflection_radius_exponent_pos hsigma hd hdGap huD le_rfl
  obtain ⟨Clog, hClog, Tlog, hTlog, hLogs⟩ :=
    eventually_source_selection_log_product_le d hd
  let CK : ℝ := 32 * 2 ^ sigma +
    (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
      4 ^ (sigma + 1 / 2)
  have hCK : 0 < CK := by dsimp only [CK]; positivity
  let D : ℝ :=
    (128 * Clog * CK * (typeIDyadicCutoffMellinL1 + 1)) /
      (3 * Real.pi)
  have hD : 0 < D := by
    dsimp only [D]
    exact div_pos
      (mul_pos (mul_pos (mul_pos (by norm_num) hClog) hCK)
        (by linarith [typeIDyadicCutoffMellinL1_nonneg]))
      (mul_pos (by norm_num) Real.pi_pos)
  have hPowTop := tendsto_rpow_atTop hrho
  have hEventually := (tendsto_atTop.1 hPowTop) (2 * D)
  rw [eventually_atTop] at hEventually
  obtain ⟨Tpow, hTpow⟩ := hEventually
  let T₀ : ℝ := max Tlog (max Tpow 8)
  refine ⟨T₀, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro T tau Q hT hQ htauOne htauTwo hScale hMargin
  have hTLog : Tlog ≤ T := (le_max_left _ _).trans hT
  have hRest : max Tpow 8 ≤ T := (le_max_right _ _).trans hT
  have hTPow : Tpow ≤ T := (le_max_left _ _).trans hRest
  have hTEight : 8 ≤ T := (le_max_right _ _).trans hRest
  have hTOne : 1 ≤ T := by linarith
  have hTPos : 0 < T := by linarith
  have hKernel := mediumTypeIStationaryKernel_le_rpow hsigma hsigmaUpper
    hTOne hQ htauOne htauTwo hScale
  have hLogProduct := hLogs T hTLog
  have hSecondClog : (1 : ℝ) ≤
      Nat.clog 2 (⌊sharpZetaCutoff T⌋₊ + 1) := by
    have hAOne : 1 < ⌊sharpZetaCutoff T⌋₊ := by
      apply lt_of_lt_of_le (by omega : 1 < (2 : ℕ))
      apply Nat.le_floor
      exact (show (2 : ℝ) ≤ 4 * T by nlinarith).trans
        (four_mul_lt_sharpZetaCutoff T).le
    have hclog : 0 < Nat.clog 2 (⌊sharpZetaCutoff T⌋₊ + 1) :=
      Nat.clog_pos Nat.one_lt_two (by omega)
    exact_mod_cast hclog
  have hSourceLog :
      ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) ≤
        Clog * T ^ d := by
    have hnonneg : 0 ≤
        ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) := by
      positivity
    nlinarith [mul_le_mul_of_nonneg_left hSecondClog hnonneg]
  have hQEq : (Q : ℝ) = T ^ (1 / tau) :=
    natCast_eq_rpow_inv_of_rpow_eq hQ (by linarith) hScale
  have hDen :
      ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) *
          (Q : ℝ) * mediumTypeIStationaryKernel sigma T Q ≤
        (Clog * CK) * T ^ (d + 1 / tau - sigma - 1 / 2) := by
    calc
      ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) *
          (Q : ℝ) * mediumTypeIStationaryKernel sigma T Q ≤
        (Clog * T ^ d) * T ^ (1 / tau) *
          (CK * T ^ (-sigma - 1 / 2)) := by
            rw [hQEq]
            gcongr
            exact (mediumTypeIStationaryKernel_pos hTPos
              (lt_trans Nat.zero_lt_one hQ)).le
      _ = (Clog * CK) * T ^ (d + 1 / tau - sigma - 1 / 2) := by
        have hPowCombine :
            T ^ d * T ^ (1 / tau) * T ^ (-sigma - 1 / 2) =
              T ^ (d + 1 / tau - sigma - 1 / 2) := by
          rw [← Real.rpow_add hTPos, ← Real.rpow_add hTPos]
          congr 1
          ring
        rw [← hPowCombine]
        ring
  have hExpMono : sigma + 1 / 2 - 1 / (2 * sigma - 200 * d) - u - d ≤
      sigma + 1 / 2 - 1 / tau - u - d := by
    have haPos : 0 < 2 * sigma - 200 * d := by
      have := medium_reflection_radius_exponent_pos hsigma hd hdGap huD le_rfl
      have haOne : 1 < 2 * sigma - 200 * d := by
        have hScaled : 200 * d ≤ (sigma - 1 / 2) / 5 := by
          calc
            200 * d ≤ 200 * ((sigma - 1 / 2) / 1000) := by gcongr
            _ = (sigma - 1 / 2) / 5 := by ring
        linarith
      exact zero_lt_one.trans haOne
    have hInv := one_div_le_one_div_of_le haPos hMargin
    linarith
  have hPowLarge : 2 * D ≤
      T ^ (sigma + 1 / 2 - 1 / tau - u - d) := by
    exact (hTpow T hTPow).trans
      (Real.rpow_le_rpow_of_exponent_le hTOne hExpMono)
  have hPowEq :
      T ^ (sigma + 1 / 2 - 1 / tau - u - d) *
        T ^ (d + 1 / tau - sigma - 1 / 2) = T ^ (-u) := by
    rw [← Real.rpow_add hTPos]
    congr 1
    ring
  have hConst : 16 * (typeIDyadicCutoffMellinL1 + 1) * Clog * CK ≤
      (3 * Real.pi / 8) *
        T ^ (sigma + 1 / 2 - 1 / tau - u - d) := by
    have hThreePi : 0 < 3 * Real.pi := mul_pos (by norm_num) Real.pi_pos
    have hDiv :
        (2 * (128 * Clog * CK * (typeIDyadicCutoffMellinL1 + 1))) /
            (3 * Real.pi) ≤
          T ^ (sigma + 1 / 2 - 1 / tau - u - d) := by
      calc
        _ = 2 * D := by dsimp only [D]; ring
        _ ≤ _ := hPowLarge
    have hCross := (div_le_iff₀ hThreePi).mp hDiv
    have hPowNonneg : 0 ≤
        T ^ (sigma + 1 / 2 - 1 / tau - u - d) := by positivity
    have hMassNonneg : 0 ≤ typeIDyadicCutoffMellinL1 + 1 := by
      linarith [typeIDyadicCutoffMellinL1_nonneg]
    have hXNonneg : 0 ≤
        Clog * CK * (typeIDyadicCutoffMellinL1 + 1) := by positivity
    nlinarith [hCross, mul_nonneg Real.pi_pos.le hPowNonneg]
  have hDenPos : 0 < 8 * (Q : ℝ) *
      mediumTypeIStationaryKernel sigma T Q *
        (typeIDyadicCutoffMellinL1 + 1) := by
    exact mul_pos
      (mul_pos (mul_pos (by norm_num)
          (by exact_mod_cast (lt_trans Nat.zero_lt_one hQ)))
        (mediumTypeIStationaryKernel_pos hTPos
          (lt_trans Nat.zero_lt_one hQ)))
      (by linarith [typeIDyadicCutoffMellinL1_nonneg])
  have hLAPos : 0 <
      ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) := by positivity
  rw [show ((3 / 4 : ℝ) * (T ^ (-u) / 2)) =
    (3 / 8) * T ^ (-u) by ring]
  rw [le_div_iff₀ hDenPos]
  rw [show Real.pi * (((3 / 8 : ℝ) * T ^ (-u)) /
      ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ)) =
    (Real.pi * ((3 / 8 : ℝ) * T ^ (-u))) /
      ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) by ring]
  rw [le_div_iff₀ hLAPos]
  calc
    (2 : ℝ) *
          (8 * Q * mediumTypeIStationaryKernel sigma T Q *
            (typeIDyadicCutoffMellinL1 + 1)) *
        (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) =
      (16 * (typeIDyadicCutoffMellinL1 + 1)) *
        (((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) *
          Q * mediumTypeIStationaryKernel sigma T Q) := by ring
    _ ≤ (16 * (typeIDyadicCutoffMellinL1 + 1)) *
        ((Clog * CK) * T ^ (d + 1 / tau - sigma - 1 / 2)) := by
          exact mul_le_mul_of_nonneg_left hDen
            (mul_nonneg (by norm_num)
              (by linarith [typeIDyadicCutoffMellinL1_nonneg]))
    _ = (16 * (typeIDyadicCutoffMellinL1 + 1) * Clog * CK) *
        T ^ (d + 1 / tau - sigma - 1 / 2) := by ring
    _ ≤ ((3 * Real.pi / 8) *
          T ^ (sigma + 1 / 2 - 1 / tau - u - d)) *
        T ^ (d + 1 / tau - sigma - 1 / 2) := by gcongr
    _ = Real.pi * ((3 / 8 : ℝ) * T ^ (-u)) := by
      calc
        (3 * Real.pi / 8) *
              T ^ (sigma + 1 / 2 - 1 / tau - u - d) *
            T ^ (d + 1 / tau - sigma - 1 / 2) =
          (3 * Real.pi / 8) *
            (T ^ (sigma + 1 / 2 - 1 / tau - u - d) *
              T ^ (d + 1 / tau - sigma - 1 / 2)) := by ring
        _ = (3 * Real.pi / 8) * T ^ (-u) := by rw [hPowEq]
        _ = Real.pi * ((3 / 8 : ℝ) * T ^ (-u)) := by ring

/-- Exact product bounds for the natural dual cutoff.  They are the finite
replacement for the informal notation `M asymp T^(1+d)/Q`. -/
theorem medium_dual_cutoff_product_bounds
    {T d tau : ℝ} {Q : ℕ}
    (hT : 1 ≤ T) (_hd : 0 ≤ d) (hQ : 1 < Q)
    (htau : 1 < tau) (hScale : (Q : ℝ) ^ tau = T)
    (hRatio : 2 ≤ T ^ (1 + d) / Q) :
    let M := mediumTypeIDualCutoff T d Q
    1 < M ∧ (M : ℝ) ≤ T ^ (1 + d) / Q ∧
      T ^ (1 + d) / 2 ≤ (Q : ℝ) * M ∧
      (Q : ℝ) * M ≤ T ^ (1 + d) ∧
      (Q : ℝ) ≤ T := by
  dsimp only
  let M := mediumTypeIDualCutoff T d Q
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have hQPos : (0 : ℝ) < Q := by positivity
  have hMUpper : (M : ℝ) ≤ T ^ (1 + d) / Q := by
    simpa only [M] using mediumTypeIDualCutoff_cast_le (T := T) (d := d)
      (Q := Q) (zero_le_one.trans hT)
  have hMLower : T ^ (1 + d) / Q / 2 ≤ (M : ℝ) := by
    simpa only [M] using half_le_natFloor_of_two_le hRatio
  have hMTwo : (2 : ℕ) ≤ M := by
    dsimp only [M, mediumTypeIDualCutoff]
    exact Nat.le_floor hRatio
  have hMNat : 1 < M := by omega
  have hProdLower : T ^ (1 + d) / 2 ≤ (Q : ℝ) * M := by
    calc
      T ^ (1 + d) / 2 = (Q : ℝ) * (T ^ (1 + d) / Q / 2) := by
        field_simp [hQPos.ne']
      _ ≤ (Q : ℝ) * M := by gcongr
  have hProdUpper : (Q : ℝ) * M ≤ T ^ (1 + d) := by
    calc
      (Q : ℝ) * M ≤ (Q : ℝ) * (T ^ (1 + d) / Q) := by gcongr
      _ = T ^ (1 + d) := by field_simp [hQPos.ne']
  have hQUpper : (Q : ℝ) ≤ T := by
    have hTauPower : (Q : ℝ) ≤ (Q : ℝ) ^ tau := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hQ.le)
          htau.le
    simpa only [hScale] using hTauPower
  exact ⟨hMNat, hMUpper, hProdLower, hProdUpper, hQUpper⟩

/-- A concrete tenth-order envelope for the source-normalized zero mode.
The large fixed order leaves ample room for every detector loss. -/
theorem sourceScalar_zeroMode_le_tenth_order_envelope
    {sigma T t : ℝ} {Q : ℕ}
    (hsigma : sigma ≤ 1) (hT : 1 ≤ T)
    (ht : T / 2 ≤ t) (hQ : 0 < Q) (hQT : (Q : ℝ) ≤ T)
    {C : ℝ}
    (hDecay : |t| ^ (10 : ℕ) *
      ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
        ((Q : ℂ) * typeINormalizedFourier sigma t 0)‖ ≤
      (Q : ℝ) ^ (1 - sigma) * C) :
    ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
        ((Q : ℂ) * typeINormalizedFourier sigma t 0)‖ ≤
      1024 * C * T ^ (1 - sigma - 10) := by
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have htPos : 0 < t := by linarith
  have hExp : 0 ≤ 1 - sigma := by linarith
  have hQPow : (Q : ℝ) ^ (1 - sigma) ≤ T ^ (1 - sigma) :=
    Real.rpow_le_rpow (Nat.cast_nonneg Q) hQT hExp
  have hAbs : T / 2 ≤ |t| := by simpa [abs_of_pos htPos] using ht
  have hAbsPow : (T / 2) ^ (10 : ℕ) ≤ |t| ^ (10 : ℕ) :=
    pow_le_pow_left₀ (by positivity) hAbs 10
  have hScale :
      (1024 * C * T ^ (1 - sigma - 10)) * (T / 2) ^ (10 : ℕ) =
        C * T ^ (1 - sigma) := by
    rw [div_pow, show (2 : ℝ) ^ (10 : ℕ) = 1024 by norm_num,
      ← Real.rpow_natCast]
    have hPow : T ^ (1 - sigma - 10) * T ^ (10 : ℝ) =
        T ^ (1 - sigma) := by
      rw [← Real.rpow_add hTPos]
      congr 1
      ring
    calc
      1024 * C * T ^ (1 - sigma - 10) * (T ^ (10 : ℝ) / 1024) =
          C * (T ^ (1 - sigma - 10) * T ^ (10 : ℝ)) := by ring
      _ = C * T ^ (1 - sigma) := by rw [hPow]
  have hCnonneg : 0 ≤ C := by
    have hLeft : 0 ≤ |t| ^ (10 : ℕ) *
      ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
        ((Q : ℂ) * typeINormalizedFourier sigma t 0)‖ := by positivity
    have hQPowPos : 0 < (Q : ℝ) ^ (1 - sigma) := by positivity
    nlinarith
  have hMajor :
      (Q : ℝ) ^ (1 - sigma) * C ≤
        (1024 * C * T ^ (1 - sigma - 10)) * |t| ^ (10 : ℕ) := by
    calc
      (Q : ℝ) ^ (1 - sigma) * C ≤ T ^ (1 - sigma) * C := by gcongr
      _ = (1024 * C * T ^ (1 - sigma - 10)) *
          (T / 2) ^ (10 : ℕ) := by rw [hScale]; ring
      _ ≤ (1024 * C * T ^ (1 - sigma - 10)) *
          |t| ^ (10 : ℕ) := by gcongr
  have hProduct := hDecay.trans hMajor
  rw [mul_comm] at hProduct
  exact le_of_mul_le_mul_right hProduct (pow_pos (abs_pos.mpr htPos.ne') 10)

/-- The actual zero Fourier mode is eventually at most one eighth of the
literal selected source threshold, uniformly over the medium slab. -/
theorem eventually_sourceScalar_zeroMode_le_detector
    {sigma d u : ℝ} (hsigmaLower : 1 / 2 < sigma)
    (hsigmaUpper : sigma < 1) (hd : 0 < d) (hdOne : d ≤ 1)
    (_hu : 0 ≤ u) (huD : u ≤ d) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ {T t : ℝ} {Q : ℕ}, T₀ ≤ T →
      T / 2 ≤ t → 0 < Q → (Q : ℝ) ≤ T →
      ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
          ((Q : ℂ) * typeINormalizedFourier sigma t 0)‖ ≤
        ((((3 / 4) * (T ^ (-u) / 2)) /
          (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ))) / 8 := by
  obtain ⟨Czero, hCzero, hZeroDecay⟩ :=
    exists_sourceScalar_zeroMode_decay sigma 10
  obtain ⟨Clog, hClog, Tlog, hTlog, hLogs⟩ :=
    eventually_source_selection_log_product_le d hd
  let a : ℝ := 9 + sigma - d - u
  have ha : 0 < a := by dsimp only [a]; linarith
  have hPowTop := tendsto_rpow_atTop ha
  have hEventually := (tendsto_atTop.1 hPowTop)
    ((65536 / 3 : ℝ) * Czero * Clog)
  rw [eventually_atTop] at hEventually
  obtain ⟨Tpow, hTpow⟩ := hEventually
  let T₀ : ℝ := max Tlog (max Tpow 8)
  refine ⟨T₀, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro T t Q hT ht hQ hQT
  have hTLog : Tlog ≤ T := (le_max_left _ _).trans hT
  have hRest : max Tpow 8 ≤ T := (le_max_right _ _).trans hT
  have hTPow : Tpow ≤ T := (le_max_left _ _).trans hRest
  have hTEight : 8 ≤ T := (le_max_right _ _).trans hRest
  have hTOne : 1 ≤ T := by linarith
  have hTPos : 0 < T := by linarith
  have hEnv := sourceScalar_zeroMode_le_tenth_order_envelope
    hsigmaUpper.le hTOne ht hQ hQT (hZeroDecay t Q hQ)
  have hProduct := hLogs T hTLog
  have hSecondClog : (1 : ℝ) ≤
      Nat.clog 2 (⌊sharpZetaCutoff T⌋₊ + 1) := by
    have hAOne : 1 < ⌊sharpZetaCutoff T⌋₊ := by
      apply lt_of_lt_of_le (by omega : 1 < (2 : ℕ))
      apply Nat.le_floor
      exact (show (2 : ℝ) ≤ 4 * T by nlinarith).trans
        (four_mul_lt_sharpZetaCutoff T).le
    have hclog : 0 < Nat.clog 2 (⌊sharpZetaCutoff T⌋₊ + 1) :=
      Nat.clog_pos Nat.one_lt_two (by omega)
    exact_mod_cast hclog
  have hSourceLog :
      ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) ≤
        Clog * T ^ d := by
    have hnonneg : 0 ≤
        ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) := by
      positivity
    nlinarith [mul_le_mul_of_nonneg_left hSecondClog hnonneg]
  have hLarge := hTpow T hTPow
  have hPowerEq :
      T ^ (1 - sigma - 10) * T ^ d * T ^ a = T ^ (-u) := by
    rw [← Real.rpow_add hTPos, ← Real.rpow_add hTPos]
    dsimp only [a]
    congr 1
    ring
  have hScaled :
      1024 * Czero * T ^ (1 - sigma - 10) *
          ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) ≤
        (3 / 64) * T ^ (-u) := by
    calc
      1024 * Czero * T ^ (1 - sigma - 10) *
          ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) ≤
        1024 * Czero * T ^ (1 - sigma - 10) * (Clog * T ^ d) := by
          gcongr
      _ ≤ (3 / 64) * T ^ (-u) := by
        rw [← hPowerEq]
        have hNonneg : 0 ≤
            T ^ (1 - sigma - 10) * T ^ d := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hLarge hNonneg]
  rw [show (((3 / 4 : ℝ) * (T ^ (-u) / 2)) /
      (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ)) / 8 =
    ((3 / 64) * T ^ (-u)) /
      (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) by ring]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) <
    (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ))]
  exact (mul_le_mul_of_nonneg_right hEnv (by positivity)).trans hScaled

/-- Uniform finite envelope for the source-normalized far Poisson modes.
The exact product lower bound for `Q*M` cancels the order-`n` growth in the
ordinate, leaving the decisive factor `T^(-n*d)`. -/
theorem sourceScalar_farModes_le_power_envelope
    {sigma T t d : ℝ} {Q M n : ℕ} {K : ℝ}
    (hsigma : 0 ≤ sigma) (hT : 1 ≤ T)
    (htNonneg : 0 ≤ t) (htUpper : t ≤ 3 * T)
    (hQ : 0 < Q) (hM : 0 < M) (hK : 0 ≤ K)
    (hProd : T ^ (1 + d) / 2 ≤ (Q : ℝ) * M)
    (hRaw :
      ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
          typeINormalizedFarTail sigma t Q M‖ ≤
        (Q : ℝ) ^ (-sigma) *
          (K * (1 + |t|) ^ (n + 2) /
            ((Q : ℝ) ^ (n + 1) * (M : ℝ) ^ n))) :
    ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
        typeINormalizedFarTail sigma t Q M‖ ≤
      K * (4 : ℝ) ^ (n + 2) * 2 ^ n * T ^ (2 - (n : ℝ) * d) := by
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have hQReal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hMReal : (0 : ℝ) < M := by exact_mod_cast hM
  have hQOne : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQWeight : (Q : ℝ) ^ (-sigma) ≤ 1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow_of_nonpos
      (show (0 : ℝ) < 1 by norm_num) hQOne (by linarith)
  have htAbs : |t| = t := abs_of_nonneg htNonneg
  have hOrd : 1 + |t| ≤ 4 * T := by rw [htAbs]; linarith
  have hOrdPow : (1 + |t|) ^ (n + 2) ≤ (4 * T) ^ (n + 2) :=
    pow_le_pow_left₀ (by positivity) hOrd (n + 2)
  have hProdPow : (T ^ (1 + d) / 2) ^ n ≤
      ((Q : ℝ) * M) ^ n := pow_le_pow_left₀ (by positivity) hProd n
  have hDenRewrite : (Q : ℝ) ^ (n + 1) * (M : ℝ) ^ n =
      (Q : ℝ) * (((Q : ℝ) * M) ^ n) := by
    rw [pow_succ']
    ring
  have hDenLower : (T ^ (1 + d) / 2) ^ n ≤
      (Q : ℝ) ^ (n + 1) * (M : ℝ) ^ n := by
    rw [hDenRewrite]
    exact hProdPow.trans (by
      have hQOne : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
      nlinarith [mul_le_mul_of_nonneg_right hQOne
        (pow_nonneg (mul_nonneg (Nat.cast_nonneg Q) (Nat.cast_nonneg M)) n)])
  have hRatio :
      K * (1 + |t|) ^ (n + 2) /
          ((Q : ℝ) ^ (n + 1) * (M : ℝ) ^ n) ≤
        K * (4 * T) ^ (n + 2) / (T ^ (1 + d) / 2) ^ n := by
    exact div_le_div₀ (mul_nonneg hK (pow_nonneg (by positivity) _))
      (mul_le_mul_of_nonneg_left hOrdPow hK)
      (pow_pos (by positivity) _) hDenLower
  have hAlgebra :
      K * (4 * T) ^ (n + 2) / (T ^ (1 + d) / 2) ^ n =
        K * (4 : ℝ) ^ (n + 2) * 2 ^ n *
          T ^ (2 - (n : ℝ) * d) := by
    have hNum : T ^ (n + 2) = T ^ ((n + 2 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
    have hDen : (T ^ (1 + d)) ^ n =
        T ^ ((n : ℝ) * (1 + d)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hTPos.le]
      ring_nf
    have hRatioPower : T ^ (n + 2) / (T ^ (1 + d)) ^ n =
        T ^ (2 - (n : ℝ) * d) := by
      rw [hNum, hDen, div_eq_mul_inv, ← Real.rpow_neg hTPos.le,
        ← Real.rpow_add hTPos]
      congr 1
      push_cast
      ring
    calc
      K * (4 * T) ^ (n + 2) / (T ^ (1 + d) / 2) ^ n =
          K * (4 : ℝ) ^ (n + 2) * 2 ^ n *
            (T ^ (n + 2) / (T ^ (1 + d)) ^ n) := by
              rw [mul_pow, div_pow]
              field_simp [show (T ^ (1 + d)) ^ n ≠ 0 by positivity]
      _ = K * (4 : ℝ) ^ (n + 2) * 2 ^ n *
          T ^ (2 - (n : ℝ) * d) := by rw [hRatioPower]
  calc
    ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
        typeINormalizedFarTail sigma t Q M‖ ≤ _ := hRaw
    _ ≤ 1 * (K * (1 + |t|) ^ (n + 2) /
          ((Q : ℝ) ^ (n + 1) * (M : ℝ) ^ n)) := by gcongr
    _ ≤ K * (4 * T) ^ (n + 2) / (T ^ (1 + d) / 2) ^ n := by
      simpa only [one_mul] using hRatio
    _ = _ := hAlgebra

/-- The complete far-frequency sum is eventually at most one eighth of the
selected source threshold.  The decay order is chosen as a positive natural
number from the physical parameter `d`, rather than assumed. -/
theorem eventually_sourceScalar_farModes_le_detector
    {sigma d u : ℝ} (hsigma : 0 ≤ sigma)
    (hd : 0 < d) (hdOne : d ≤ 1) (hu : 0 ≤ u) (_huD : u ≤ d) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ {T t : ℝ} {Q M : ℕ}, T₀ ≤ T →
      0 ≤ t → t ≤ 3 * T → 0 < Q → 0 < M →
      T ^ (1 + d) / 2 ≤ (Q : ℝ) * M →
      ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
          typeINormalizedFarTail sigma t Q M‖ ≤
        ((((3 / 4) * (T ^ (-u) / 2)) /
          (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ))) / 8 := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((4 + d + u) / d)
  have hnReal : (4 + d + u) / d < (n : ℝ) := by simpa using hn
  have hnTwo : 1 < n := by
    have hRatioFour : 4 < (4 + d + u) / d := by
      rw [lt_div_iff₀ hd]
      nlinarith
    have hnFour : 4 < n := by exact_mod_cast (hRatioFour.trans hnReal)
    omega
  have hnd : 4 + d + u < (n : ℝ) * d := by
    rw [div_lt_iff₀ hd] at hnReal
    simpa only [mul_comm] using hnReal
  obtain ⟨Kfar, hKfar, hFarRaw⟩ := exists_sourceScalar_farModes_bound sigma n
  obtain ⟨Clog, hClog, Tlog, hTlog, hLogs⟩ :=
    eventually_source_selection_log_product_le d hd
  let B : ℝ := Kfar * (4 : ℝ) ^ (n + 2) * 2 ^ n
  have hB : 0 < B := by dsimp only [B]; positivity
  let a : ℝ := (n : ℝ) * d - 2 - d - u
  have ha : 0 < a := by dsimp only [a]; linarith
  have hPowTop := tendsto_rpow_atTop ha
  have hEventually := (tendsto_atTop.1 hPowTop)
    ((64 / 3 : ℝ) * B * Clog)
  rw [eventually_atTop] at hEventually
  obtain ⟨Tpow, hTpow⟩ := hEventually
  let T₀ : ℝ := max Tlog (max Tpow 8)
  refine ⟨T₀, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro T t Q M hT htNonneg htUpper hQ hM hProd
  have hTLog : Tlog ≤ T := (le_max_left _ _).trans hT
  have hRest : max Tpow 8 ≤ T := (le_max_right _ _).trans hT
  have hTPow : Tpow ≤ T := (le_max_left _ _).trans hRest
  have hTEight : 8 ≤ T := (le_max_right _ _).trans hRest
  have hTOne : 1 ≤ T := by linarith
  have hTPos : 0 < T := by linarith
  have hEnv := sourceScalar_farModes_le_power_envelope hsigma hTOne
    htNonneg htUpper hQ hM hKfar.le hProd (hFarRaw t Q M hQ hM)
  have hProduct := hLogs T hTLog
  have hAOne : 1 < ⌊sharpZetaCutoff T⌋₊ := by
    apply lt_of_lt_of_le (by omega : 1 < (2 : ℕ))
    apply Nat.le_floor
    exact (show (2 : ℝ) ≤ 4 * T by nlinarith).trans
      (four_mul_lt_sharpZetaCutoff T).le
  have hSecondClog : (1 : ℝ) ≤
      Nat.clog 2 (⌊sharpZetaCutoff T⌋₊ + 1) := by
    have hclog : 0 < Nat.clog 2 (⌊sharpZetaCutoff T⌋₊ + 1) :=
      Nat.clog_pos Nat.one_lt_two (by omega)
    exact_mod_cast hclog
  have hSourceLog :
      ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) ≤
        Clog * T ^ d := by
    have hnonneg : 0 ≤
        ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) := by
      positivity
    nlinarith [mul_le_mul_of_nonneg_left hSecondClog hnonneg]
  have hLarge := hTpow T hTPow
  have hPowerEq : T ^ (2 - (n : ℝ) * d) * T ^ d * T ^ a =
      T ^ (-u) := by
    rw [← Real.rpow_add hTPos, ← Real.rpow_add hTPos]
    dsimp only [a]
    congr 1
    ring
  have hScaled :
      B * T ^ (2 - (n : ℝ) * d) *
          ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) ≤
        (3 / 64) * T ^ (-u) := by
    calc
      B * T ^ (2 - (n : ℝ) * d) *
          ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) ≤
        B * T ^ (2 - (n : ℝ) * d) * (Clog * T ^ d) := by gcongr
      _ ≤ (3 / 64) * T ^ (-u) := by
        rw [← hPowerEq]
        have hNonneg : 0 ≤ T ^ (2 - (n : ℝ) * d) * T ^ d := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hLarge hNonneg]
  rw [show (((3 / 4 : ℝ) * (T ^ (-u) / 2)) /
      (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ)) / 8 =
    ((3 / 64) * T ^ (-u)) /
      (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) by ring]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) <
    (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ))]
  exact (mul_le_mul_of_nonneg_right hEnv (by positivity)).trans (by
    simpa only [B] using hScaled)

/-- Coarse but uniform power envelope for either complementary Mellin tail.
The exact theorem upstream is retained in `hRaw`; this lemma only performs
the finite support and scale comparisons needed for epsilon absorption. -/
theorem reflectedMellinTail_le_power_envelope
    {sigma T d : ℝ} {Q M n : ℕ} {C E : ℝ}
    (hsigma : 0 ≤ sigma) (hsigmaUpper : sigma ≤ 1)
    (hT : 1 ≤ T) (_hd : 0 ≤ d)
    (hQ : 0 < Q) (hM : 1 ≤ M)
    (hQT : (Q : ℝ) ≤ T)
    (hMT : (M : ℝ) ≤ T ^ (1 + d))
    (hC : 0 ≤ C)
    (hRaw : E ≤
      (Q : ℝ) * ((M : ℝ) * (M : ℝ) ^ sigma) *
        (((2 * M * Q - (Q : ℝ) / 2) *
            (((Q : ℝ) / 2) ^ (-sigma) / ((Q : ℝ) / 2))) *
          C * (T ^ d) ^ (1 - (n : ℝ)))) :
    E ≤ 2 ^ (sigma + 2) * C *
      T ^ (4 + 4 * d - (n : ℝ) * d) := by
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have hQReal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hMReal : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMPos : (0 : ℝ) < M := zero_lt_one.trans_le hMReal
  have hDiffNonneg : 0 ≤ 2 * (M : ℝ) * Q - (Q : ℝ) / 2 := by
    nlinarith
  have hDiff : (2 * M * Q - (Q : ℝ) / 2) ≤
      2 * (M : ℝ) * Q := by norm_num; linarith
  have hQKernel : ((Q : ℝ) / 2) ^ (-sigma) /
      ((Q : ℝ) / 2) =
      2 ^ (sigma + 1) * (Q : ℝ) ^ (-sigma - 1) := by
    have hTwo : (2 : ℝ) ^ sigma * 2 = 2 ^ (sigma + 1) := by
      calc
        (2 : ℝ) ^ sigma * 2 = 2 ^ sigma * 2 ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        _ = 2 ^ (sigma + 1) := by rw [← Real.rpow_add (by norm_num)]
    have hQMul : (Q : ℝ) * (Q : ℝ) ^ (-sigma - 1) =
        (Q : ℝ) ^ (-sigma) := by
      calc
        (Q : ℝ) * (Q : ℝ) ^ (-sigma - 1) =
            (Q : ℝ) ^ (1 : ℝ) * (Q : ℝ) ^ (-sigma - 1) := by
              rw [Real.rpow_one]
        _ = (Q : ℝ) ^ ((1 : ℝ) + (-sigma - 1)) := by
          rw [← Real.rpow_add hQReal]
        _ = (Q : ℝ) ^ (-sigma) := by
          congr 1
          ring
    rw [Real.div_rpow hQReal.le (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp [hQReal.ne']
    calc
      (Q : ℝ) ^ (-sigma) * (2 : ℝ) ^ sigma * 2 =
          (2 : ℝ) ^ (sigma + 1) * (Q : ℝ) ^ (-sigma) := by
            calc
              (Q : ℝ) ^ (-sigma) * (2 : ℝ) ^ sigma * 2 =
                  (Q : ℝ) ^ (-sigma) *
                    ((2 : ℝ) ^ sigma * 2) := by ring
              _ = (Q : ℝ) ^ (-sigma) * 2 ^ (sigma + 1) := by rw [hTwo]
              _ = 2 ^ (sigma + 1) * (Q : ℝ) ^ (-sigma) := by ring
      _ = (Q : ℝ) * (2 : ℝ) ^ (sigma + 1) *
          (Q : ℝ) ^ (-sigma - 1) := by rw [← hQMul]; ring
  have hMWeight : (M : ℝ) ^ sigma ≤ (M : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hMReal hsigmaUpper
  have hQWeight : (Q : ℝ) ^ (1 - sigma) ≤ T := by
    calc
      (Q : ℝ) ^ (1 - sigma) ≤ (Q : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hQ) (by linarith)
      _ = (Q : ℝ) := Real.rpow_one _
      _ ≤ T := hQT
  have hMThree : (M : ℝ) ^ (3 : ℕ) ≤
      T ^ (3 * (1 + d)) := by
    calc
      (M : ℝ) ^ (3 : ℕ) ≤ (T ^ (1 + d)) ^ (3 : ℕ) :=
        pow_le_pow_left₀ (Nat.cast_nonneg M) hMT 3
      _ = T ^ (3 * (1 + d)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hTPos.le]
        congr 1
        ring
  have hQCombine : (Q : ℝ) * Q * (Q : ℝ) ^ (-sigma - 1) =
      (Q : ℝ) ^ (1 - sigma) := by
    calc
      (Q : ℝ) * Q * (Q : ℝ) ^ (-sigma - 1) =
          ((Q : ℝ) ^ (1 : ℝ) * (Q : ℝ) ^ (1 : ℝ)) *
            (Q : ℝ) ^ (-sigma - 1) := by rw [Real.rpow_one]
      _ = (Q : ℝ) ^ ((1 : ℝ) + 1) *
            (Q : ℝ) ^ (-sigma - 1) := by
              rw [← Real.rpow_add hQReal]
      _ = (Q : ℝ) ^ (((1 : ℝ) + 1) + (-sigma - 1)) := by
        rw [← Real.rpow_add hQReal]
      _ = (Q : ℝ) ^ (1 - sigma) := by
        congr 1
        ring
  have hTwoCombine : (2 : ℝ) * 2 ^ (sigma + 1) =
      2 ^ (sigma + 2) := by
    calc
      (2 : ℝ) * 2 ^ (sigma + 1) =
          2 ^ (1 : ℝ) * 2 ^ (sigma + 1) := by rw [Real.rpow_one]
      _ = 2 ^ ((1 : ℝ) + (sigma + 1)) := by
        rw [← Real.rpow_add (by norm_num)]
      _ = 2 ^ (sigma + 2) := by
        congr 1
        ring
  have hMain :
      (Q : ℝ) * ((M : ℝ) * (M : ℝ) ^ sigma) *
          ((2 * M * Q - (Q : ℝ) / 2) *
            (((Q : ℝ) / 2) ^ (-sigma) / ((Q : ℝ) / 2))) ≤
        2 ^ (sigma + 2) * T ^ (4 + 3 * d) := by
    rw [hQKernel]
    calc
      (Q : ℝ) * ((M : ℝ) * (M : ℝ) ^ sigma) *
          ((2 * M * Q - (Q : ℝ) / 2) *
            (2 ^ (sigma + 1) * (Q : ℝ) ^ (-sigma - 1))) ≤
        (Q : ℝ) * ((M : ℝ) * M) *
          ((2 * M * Q) *
            (2 ^ (sigma + 1) * (Q : ℝ) ^ (-sigma - 1))) := by
              gcongr
      _ = 2 ^ (sigma + 2) * ((M : ℝ) ^ (3 : ℕ) *
          (Q : ℝ) ^ (1 - sigma)) := by
        rw [← hQCombine, ← hTwoCombine]
        ring
      _ ≤ 2 ^ (sigma + 2) *
          (T ^ (3 * (1 + d)) * T) := by gcongr
      _ = 2 ^ (sigma + 2) * T ^ (4 + 3 * d) := by
        have hTPow : T ^ (3 * (1 + d)) * T = T ^ (4 + 3 * d) := by
          calc
            T ^ (3 * (1 + d)) * T =
                T ^ (3 * (1 + d)) * T ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = T ^ (3 * (1 + d) + 1) := by
              rw [← Real.rpow_add hTPos]
            _ = T ^ (4 + 3 * d) := by
              congr 1
              ring
        rw [hTPow]
  have hTailPower : (T ^ d) ^ (1 - (n : ℝ)) =
      T ^ (d * (1 - (n : ℝ))) := by
    rw [← Real.rpow_mul hTPos.le]
  have hTailNonneg : 0 ≤ (T ^ d) ^ (1 - (n : ℝ)) := by positivity
  have hPowerCombine : T ^ (4 + 3 * d) *
      T ^ (d * (1 - (n : ℝ))) =
      T ^ (4 + 4 * d - (n : ℝ) * d) := by
    rw [← Real.rpow_add hTPos]
    congr 1
    ring
  calc
    E ≤ _ := hRaw
    _ = ((Q : ℝ) * ((M : ℝ) * (M : ℝ) ^ sigma) *
          ((2 * M * Q - (Q : ℝ) / 2) *
            (((Q : ℝ) / 2) ^ (-sigma) / ((Q : ℝ) / 2)))) *
        (C * (T ^ d) ^ (1 - (n : ℝ))) := by ring
    _ ≤ (2 ^ (sigma + 2) * T ^ (4 + 3 * d)) *
        (C * (T ^ d) ^ (1 - (n : ℝ))) :=
          mul_le_mul_of_nonneg_right hMain (mul_nonneg hC hTailNonneg)
    _ = 2 ^ (sigma + 2) * C *
        T ^ (4 + 4 * d - (n : ℝ) * d) := by
      rw [hTailPower, ← hPowerCombine]
      ring

/-- Both exact complementary Mellin integrals are eventually smaller than
one eighth of the reflected extraction budget.  The decay order is selected
from the physical loss parameter, and the literal source `clog` factor is
absorbed rather than replaced by an asymptotic abbreviation. -/
theorem eventually_reflectedMellinTails_le_detector
    {sigma d u : ℝ} (hsigma : 0 ≤ sigma) (hsigmaUpper : sigma ≤ 1)
    (hd : 0 < d) (hu : 0 ≤ u) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ {T t : ℝ} {Q M : ℕ}, T₀ ≤ T →
      0 < Q → 1 ≤ M → (Q : ℝ) ≤ T →
      (M : ℝ) ≤ T ^ (1 + d) →
      let V := ((3 / 4) * (T ^ (-u) / 2)) /
        (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ)
      let Eneg := ‖∫ r : ℝ in (Set.Icc (-(T ^ d)) (T ^ d)).compl,
        typeIReflectedMellinPolynomial sigma t (Q : ℝ) M r *
          typeIDyadicCutoffMellin r *
            typeIPowerReflectionIntegral sigma (t + r)
              ((Q : ℝ) / 2) (2 * M * Q)‖
      let Epos := ‖∫ r : ℝ in (Set.Icc (-(T ^ d)) (T ^ d)).compl,
        typeIReflectedMellinPolynomial sigma (-t) (Q : ℝ) M r *
          typeIDyadicCutoffMellin r *
            typeIPowerReflectionIntegral sigma (-t + r)
              ((Q : ℝ) / 2) (2 * M * Q)‖
      Eneg ≤ Real.pi * V / 8 ∧ Epos ≤ Real.pi * V / 8 := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((5 + 5 * d + u) / d)
  have hnReal : (5 + 5 * d + u) / d < (n : ℝ) := by simpa using hn
  have hnTwo : 1 < n := by
    have hFive : 5 < (5 + 5 * d + u) / d := by
      rw [lt_div_iff₀ hd]
      nlinarith
    have : 5 < n := by exact_mod_cast (hFive.trans hnReal)
    omega
  have hnd : 5 + 5 * d + u < (n : ℝ) * d := by
    rw [div_lt_iff₀ hd] at hnReal
    simpa only [mul_comm] using hnReal
  obtain ⟨Ctail, hCtail, hTail⟩ :=
    exists_norm_typeIReflectedMellinIntegral_tail_le n hnTwo
  obtain ⟨Clog, hClog, Tlog, hTlog, hLogs⟩ :=
    eventually_source_selection_log_product_le d hd
  let B : ℝ := 2 ^ (sigma + 2) * Ctail
  have hB : 0 < B := by dsimp only [B]; positivity
  let a : ℝ := (n : ℝ) * d - 4 - 5 * d - u
  have ha : 0 < a := by dsimp only [a]; linarith
  have hPowTop := tendsto_rpow_atTop ha
  have hEventually := (tendsto_atTop.1 hPowTop)
    ((64 / (3 * Real.pi) : ℝ) * B * Clog)
  rw [eventually_atTop] at hEventually
  obtain ⟨Tpow, hTpow⟩ := hEventually
  let T₀ : ℝ := max Tlog (max Tpow 8)
  refine ⟨T₀, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro T t Q M hT hQ hM hQT hMT
  dsimp only
  have hTLog : Tlog ≤ T := (le_max_left _ _).trans hT
  have hRest : max Tpow 8 ≤ T := (le_max_right _ _).trans hT
  have hTPow : Tpow ≤ T := (le_max_left _ _).trans hRest
  have hTEight : 8 ≤ T := (le_max_right _ _).trans hRest
  have hTOne : 1 ≤ T := by linarith
  have hTPos : 0 < T := by linarith
  have hHOne : 1 ≤ T ^ d := Real.one_le_rpow hTOne hd.le
  have hQReal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hRawNeg := hTail (sigma := sigma) (t := t) (Q := (Q : ℝ))
    (H := T ^ d) (M := M) hsigma hQReal hM hHOne
  have hRawPos := hTail (sigma := sigma) (t := -t) (Q := (Q : ℝ))
    (H := T ^ d) (M := M) hsigma hQReal hM hHOne
  have hEnvNeg := reflectedMellinTail_le_power_envelope hsigma hsigmaUpper
    hTOne hd.le hQ hM hQT hMT hCtail.le hRawNeg
  have hEnvPos := reflectedMellinTail_le_power_envelope hsigma hsigmaUpper
    hTOne hd.le hQ hM hQT hMT hCtail.le hRawPos
  have hProduct := hLogs T hTLog
  have hSecondClog : (1 : ℝ) ≤
      Nat.clog 2 (⌊sharpZetaCutoff T⌋₊ + 1) := by
    have hAOne : 1 < ⌊sharpZetaCutoff T⌋₊ := by
      apply lt_of_lt_of_le (by omega : 1 < (2 : ℕ))
      apply Nat.le_floor
      exact (show (2 : ℝ) ≤ 4 * T by nlinarith).trans
        (four_mul_lt_sharpZetaCutoff T).le
    have hclog : 0 < Nat.clog 2 (⌊sharpZetaCutoff T⌋₊ + 1) :=
      Nat.clog_pos Nat.one_lt_two (by omega)
    exact_mod_cast hclog
  have hSourceLog :
      ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) ≤
        Clog * T ^ d := by
    have hnonneg : 0 ≤
        ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) := by
      positivity
    nlinarith [mul_le_mul_of_nonneg_left hSecondClog hnonneg]
  have hLarge := hTpow T hTPow
  have hPowerEq : T ^ (4 + 4 * d - (n : ℝ) * d) *
      T ^ d * T ^ a = T ^ (-u) := by
    rw [← Real.rpow_add hTPos, ← Real.rpow_add hTPos]
    dsimp only [a]
    congr 1
    ring
  have hScaled : B * T ^ (4 + 4 * d - (n : ℝ) * d) *
        ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) ≤
      (3 * Real.pi / 64) * T ^ (-u) := by
    calc
      _ ≤ B * T ^ (4 + 4 * d - (n : ℝ) * d) *
          (Clog * T ^ d) := by gcongr
      _ ≤ (3 * Real.pi / 64) * T ^ (-u) := by
        rw [← hPowerEq]
        have hNonneg : 0 ≤
            T ^ (4 + 4 * d - (n : ℝ) * d) * T ^ d := by positivity
        have hConst : B * Clog ≤ (3 * Real.pi / 64) * T ^ a := by
          have hPi : 0 < 3 * Real.pi := mul_pos (by norm_num) Real.pi_pos
          rw [div_mul_eq_mul_div] at hLarge
          field_simp [Real.pi_ne_zero] at hLarge ⊢
          nlinarith [Real.pi_pos]
        calc
          B * T ^ (4 + 4 * d - (n : ℝ) * d) * (Clog * T ^ d) =
              (B * Clog) *
                (T ^ (4 + 4 * d - (n : ℝ) * d) * T ^ d) := by ring
          _ ≤ ((3 * Real.pi / 64) * T ^ a) *
              (T ^ (4 + 4 * d - (n : ℝ) * d) * T ^ d) :=
                mul_le_mul_of_nonneg_right hConst hNonneg
          _ = (3 * Real.pi / 64) *
              (T ^ (4 + 4 * d - (n : ℝ) * d) * T ^ d * T ^ a) := by ring
  have hBudget : B * T ^ (4 + 4 * d - (n : ℝ) * d) ≤
      Real.pi * ((((3 / 4) * (T ^ (-u) / 2)) /
        (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ))) / 8 := by
    rw [show Real.pi * ((((3 / 4 : ℝ) * (T ^ (-u) / 2)) /
        (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ))) / 8 =
      ((3 * Real.pi / 64) * T ^ (-u)) /
        (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) by ring]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) <
      (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ))]
    exact hScaled
  constructor
  · exact hEnvNeg.trans (by simpa only [B] using hBudget)
  · exact hEnvPos.trans (by simpa only [B] using hBudget)

/-- The bounded Mellin-displacement window is eventually small enough for
the uniform two-sign stationary-kernel estimate. -/
theorem eventually_two_mul_rpow_le_half_sub_two
    {d : ℝ} (hd : 0 < d) (hdOne : d < 1) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      2 * T ^ d ≤ T / 2 - 2 := by
  have hgap : 0 < 1 - d := by linarith
  have hPow := tendsto_rpow_neg_atTop hgap
  have hEventually := (tendsto_order.1 hPow).2 (1 / 8 : ℝ) (by norm_num)
  rw [eventually_atTop] at hEventually
  obtain ⟨Tpow, hTpow⟩ := hEventually
  let T₀ : ℝ := max 8 Tpow
  refine ⟨T₀, le_max_left _ _, ?_⟩
  intro T hT
  have hTEight : 8 ≤ T := (le_max_left _ _).trans hT
  have hTPow : Tpow ≤ T := (le_max_right _ _).trans hT
  have hTPos : 0 < T := by linarith
  have hSmall := hTpow T hTPow
  have hRewrite : T ^ (-(1 - d)) = T ^ d / T := by
    rw [show -(1 - d) = d - 1 by ring, Real.rpow_sub hTPos]
    rw [Real.rpow_one]
  rw [hRewrite, div_lt_iff₀ hTPos] at hSmall
  nlinarith

/-- The complementary-margin inequality makes the literal floored dual
cutoff positive and supplies all product comparisons needed by the exact
Poisson formula.  This packages the eventual real-power comparison once,
without replacing the natural floor by an asymptotic surrogate. -/
theorem eventually_medium_dual_cutoff_product_bounds
    {sigma d : ℝ} (hsigma : 1 / 2 < sigma)
    (hd : 0 < d) (hdGap : d ≤ (sigma - 1 / 2) / 1000) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ {T tau : ℝ} {Q : ℕ}, T₀ ≤ T →
      1 < Q → 1 < tau → tau < 2 →
      (Q : ℝ) ^ tau = T → -100 * d ≤ tau / 2 - sigma →
      let M := mediumTypeIDualCutoff T d Q
      1 < M ∧ (M : ℝ) ≤ T ^ (1 + d) / Q ∧
        T ^ (1 + d) / 2 ≤ (Q : ℝ) * M ∧
        (Q : ℝ) * M ≤ T ^ (1 + d) ∧ (Q : ℝ) ≤ T := by
  let a : ℝ := 2 * sigma - 200 * d
  let gamma : ℝ := 1 - 1 / a
  have haOne : 1 < a := by
    dsimp only [a]
    have hScaled : 200 * d ≤ (sigma - 1 / 2) / 5 := by
      calc
        200 * d ≤ 200 * ((sigma - 1 / 2) / 1000) := by gcongr
        _ = (sigma - 1 / 2) / 5 := by ring
    linarith
  have hgamma : 0 < gamma := by
    dsimp only [gamma]
    rw [sub_pos, div_lt_one (by linarith : 0 < a)]
    exact haOne
  have hPowTop := tendsto_rpow_atTop hgamma
  have hEventually := (tendsto_atTop.1 hPowTop) 2
  rw [eventually_atTop] at hEventually
  obtain ⟨Tpow, hTpow⟩ := hEventually
  let T₀ : ℝ := max 8 Tpow
  refine ⟨T₀, le_max_left _ _, ?_⟩
  intro T tau Q hT hQ htauOne htauTwo hScale hMargin
  have hTEight : 8 ≤ T := (le_max_left _ _).trans hT
  have hTPow : Tpow ≤ T := (le_max_right _ _).trans hT
  have hTOne : 1 ≤ T := by linarith
  have hBounds := medium_complementary_source_scale_bounds hsigma hd hdGap
    hTOne hQ hScale hMargin
  dsimp only [a, gamma] at hBounds
  have hRatio : 2 ≤ T ^ (1 + d) / Q :=
    (hTpow T hTPow).trans hBounds.2.2.2.2.2
  simpa only using medium_dual_cutoff_product_bounds hTOne hd.le hQ
    htauOne hScale hRatio

/-- Every genuinely interior source family is converted, point by point,
to one of the two exact normalized reflected wide polynomials.  The same
family, displacement window, natural dual cutoff, detector threshold and
kernel occur in the conclusion; no cardinality or multiplicity is lost at
this analytic stage. -/
theorem eventually_interior_source_family_reflects
    {sigma d u : ℝ} (hsigma : 1 / 2 < sigma) (hsigmaUpper : sigma < 1)
    (hd : 0 < d) (hdOne : d ≤ 1)
    (hdGap : d ≤ (sigma - 1 / 2) / 1000)
    (hu : 0 ≤ u) (huD : u ≤ d) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧
      ∀ {T tau : ℝ} {Y A r : ℕ} (W : Finset ℝ), T₀ ≤ T →
        A = ⌊sharpZetaCutoff T⌋₊ → 0 < Y → 2 ≤ r →
        (((Y + 1 : ℕ) : ℝ) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2)) →
        2 * (2 ^ r * Y) ≤ A →
        tau = typeILogarithmicScale T (2 ^ r * Y) →
        1 < tau → tau < 2 →
        (∀ t ∈ W, T - T ^ d ≤ t ∧ t ≤ 2 * T + T ^ d) →
        (∀ t ∈ W,
          ((3 / 4) * (T ^ (-u) / 2)) /
              (Nat.clog 2 A + 1 : ℕ) ≤
            ‖typeISourceSmoothBlock Y A r sigma t‖) →
        let Q := 2 ^ r * Y
        let M := mediumTypeIDualCutoff T d Q
        let V := ((3 / 4) * (T ^ (-u) / 2)) /
          (Nat.clog 2 A + 1 : ℕ)
        let R := (Real.pi * V) /
          (8 * (Q : ℝ) * mediumTypeIStationaryKernel sigma T Q *
            (typeIDyadicCutoffMellinL1 + 1))
        let S := R / (2 * (M : ℝ) ^ sigma)
        W.Nonempty → 1 < M ∧ ∀ t ∈ W,
          (∃ v ∈ Set.Icc (-(T ^ d)) (T ^ d),
            S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
              (normalizedTypeIReflectedCoeff sigma M) (-(t + v))‖) ∨
          (∃ v ∈ Set.Icc (-(T ^ d)) (T ^ d),
            S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
              (normalizedTypeIReflectedCoeff sigma M) (t - v)‖) := by
  have hdStrict : d < 1 := by
    have hGapPos : 0 < sigma - 1 / 2 := by linarith
    have hSmall : d ≤ (sigma - 1 / 2) / 1000 := hdGap
    nlinarith
  obtain ⟨Tmargin, hTmargin, hMargin⟩ :=
    eventually_large_source_forces_complementary_margin
      (σ := sigma) (d := d) (u := u) hsigmaUpper hd
      hdStrict hdGap huD
  obtain ⟨Tdual, hTdual, hDual⟩ :=
    eventually_medium_dual_cutoff_product_bounds
      (sigma := sigma) (d := d) hsigma hd hdGap
  obtain ⟨Tzero, hTzero, hZero⟩ :=
    eventually_sourceScalar_zeroMode_le_detector
      (sigma := sigma) (d := d) (u := u) hsigma hsigmaUpper hd hdOne hu huD
  obtain ⟨Tfar, hTfar, hFar⟩ :=
    eventually_sourceScalar_farModes_le_detector
      (sigma := sigma) (d := d) (u := u) (by linarith) hd hdOne hu huD
  obtain ⟨Tradius, hTradius, hRadius⟩ :=
    eventually_medium_reflection_radius_two
      (sigma := sigma) (d := d) (u := u) hsigma hsigmaUpper hd hdGap huD
  obtain ⟨Ttail, hTtail, hTail⟩ :=
    eventually_reflectedMellinTails_le_detector
      (sigma := sigma) (d := d) (u := u) (by linarith) hsigmaUpper.le hd hu
  obtain ⟨Thalf, hThalf, hHalf⟩ := eventually_rpow_le_half_self d
    hdStrict
  obtain ⟨Tkernel, hTkernel, hKernelWindow⟩ :=
    eventually_two_mul_rpow_le_half_sub_two hd hdStrict
  let T₀ := max Tmargin
    (max Tdual (max Tzero (max Tfar (max Tradius (max Ttail (max Thalf Tkernel))))))
  refine ⟨T₀, hTmargin.trans (le_max_left _ _), ?_⟩
  intro T tau Y A r W hT hA hY hr hLower hUpper hTau htauOne htauTwo hRange hLarge
  dsimp only
  intro hW
  have hTMargin : Tmargin ≤ T := (le_max_left _ _).trans hT
  have hRest : max Tdual
      (max Tzero (max Tfar (max Tradius (max Ttail (max Thalf Tkernel))))) ≤ T :=
    (le_max_right _ _).trans hT
  have hTDual : Tdual ≤ T := (le_max_left _ _).trans hRest
  have hRest₁ : max Tzero
      (max Tfar (max Tradius (max Ttail (max Thalf Tkernel)))) ≤ T :=
    (le_max_right _ _).trans hRest
  have hTZero : Tzero ≤ T := (le_max_left _ _).trans hRest₁
  have hRest₂ : max Tfar (max Tradius (max Ttail (max Thalf Tkernel))) ≤ T :=
    (le_max_right _ _).trans hRest₁
  have hTFar : Tfar ≤ T := (le_max_left _ _).trans hRest₂
  have hRest₃ : max Tradius (max Ttail (max Thalf Tkernel)) ≤ T :=
    (le_max_right _ _).trans hRest₂
  have hTRadius : Tradius ≤ T := (le_max_left _ _).trans hRest₃
  have hRest₄ : max Ttail (max Thalf Tkernel) ≤ T :=
    (le_max_right _ _).trans hRest₃
  have hTTail : Ttail ≤ T := (le_max_left _ _).trans hRest₄
  have hRest₅ : max Thalf Tkernel ≤ T := (le_max_right _ _).trans hRest₄
  have hTHalf : Thalf ≤ T := (le_max_left _ _).trans hRest₅
  have hTKernel : Tkernel ≤ T := (le_max_right _ _).trans hRest₅
  have hTEight : 8 ≤ T := hTmargin.trans hTMargin
  have hTOne : 1 ≤ T := by linarith
  have hTPos : 0 < T := by linarith
  have hDisp : T ^ d ≤ T / 2 := hHalf T hTHalf
  let Q : ℕ := 2 ^ r * Y
  have hQOne : 1 < Q := by
    have hPow : 4 ≤ 2 ^ r := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hr
    have hProd : 4 ≤ 2 ^ r * Y := by
      calc
        4 ≤ 2 ^ r := hPow
        _ ≤ 2 ^ r * Y := Nat.le_mul_of_pos_right _ hY
    simpa only [Q] using hProd.trans' (by omega : 1 < 4)
  have hScale : (Q : ℝ) ^ tau = T := by
    rw [hTau]
    simpa only [Q] using rpow_typeILogarithmicScale_eq hTPos hQOne
  have hMarginAt : -100 * d ≤ tau / 2 - sigma := by
    obtain ⟨t, ht⟩ := hW
    exact hMargin T t tau Y A r hTMargin hA hY hr hUpper
      (hRange t ht).1 (hRange t ht).2 hDisp hTau (hLarge t ht)
  have hDualAt := hDual (T := T) (tau := tau) (Q := Q) hTDual hQOne
    htauOne htauTwo hScale hMarginAt
  dsimp only at hDualAt
  let M := mediumTypeIDualCutoff T d Q
  have hMOne : 1 < M := by simpa only [M] using hDualAt.1
  refine ⟨hMOne, ?_⟩
  intro t ht
  let V : ℝ := ((3 / 4) * (T ^ (-u) / 2)) / (Nat.clog 2 A + 1 : ℕ)
  let K : ℝ := mediumTypeIStationaryKernel sigma T Q
  let E : ℝ := Real.pi * V / 8
  have htRange := hRange t ht
  have htLower : T / 2 ≤ t := by linarith
  have htUpper : t ≤ 3 * T := by linarith
  have hV : 0 < V := by dsimp only [V]; positivity
  have hK : 0 < K := mediumTypeIStationaryKernel_pos hTPos (by omega)
  have hZeroAt := hZero (T := T) (t := t) (Q := Q) hTZero htLower
    (by omega) hDualAt.2.2.2.2
  have hFarAt := hFar (T := T) (t := t) (Q := Q) (M := M) hTFar
    (by linarith) htUpper (by omega) (by omega) (by simpa only [M] using hDualAt.2.2.1)
  have hKernelAt : ∀ v ∈ Set.Icc (-(T ^ d)) (T ^ d),
      ‖typeIPowerReflectionIntegral sigma (t + v) ((Q : ℝ) / 2) (2 * M * Q)‖ ≤ K ∧
      ‖typeIPowerReflectionIntegral sigma (-t + v) ((Q : ℝ) / 2) (2 * M * Q)‖ ≤ K := by
    intro v hv
    exact norm_typeIPowerReflectionIntegral_both_signs_le_mediumKernel
      (by linarith : 0 < sigma) hTPos htLower htUpper (Real.rpow_nonneg hTPos.le d)
      (hKernelWindow T hTKernel) (by omega) hMOne.le hv
  have hTailAt := hTail (T := T) (t := t) (Q := Q) (M := M) hTTail
    (by omega) hMOne.le hDualAt.2.2.2.2
    (by
      calc
        (M : ℝ) ≤ T ^ (1 + d) / Q := by simpa only [M] using hDualAt.2.1
        _ ≤ T ^ (1 + d) := by
          exact div_le_self (Real.rpow_nonneg hTPos.le _) (by exact_mod_cast hQOne.le))
  have hRadiusAt := hRadius (Q := Q) (T := T) (tau := tau) hTRadius hQOne htauOne
    htauTwo hScale (by linarith [hMarginAt])
  have hReflect := exists_signed_shift_large_normalized_reflected_wide_of_budget
    hY hLower hUpper (by linarith) hMOne hV (Real.rpow_nonneg hTPos.le d) hK
    (by simpa only [V] using hLarge t ht)
    (by simpa only [V, hA, Q] using hZeroAt)
    (by simpa only [V, hA, Q, M] using hFarAt)
    (fun v hv => (hKernelAt v hv).1)
    (fun v hv => (hKernelAt v hv).2)
    (by simpa only [E, V, hA, Q, M] using hTailAt.1)
    (by simpa only [E, V, hA, Q, M] using hTailAt.2)
    (by
      dsimp only [V]
      rw [hA])
    (by simpa only [V, K, hA, Q] using hRadiusAt)
  simpa only [V, K, E, Q, M] using hReflect

/-- Complete finite data exported by an interior source family before the
endpoint power/Weyl split.  It invokes the exact Poisson reflection, makes
the sign and bounded-displacement selections, exposes the literal dyadic
block and proves both of its physical scale bounds from its actual retained
threshold. -/
theorem eventually_interior_source_reflected_dyadic_data
    {sigma d u : ℝ} (hsigma : 1 / 2 < sigma)
    (hsigmaUpper : sigma < 1) (hd : 0 < d) (hdOne : d ≤ 1)
    (hdGap : d ≤ (sigma - 1 / 2) / 1000)
    (hu : 0 ≤ u) (huD : u ≤ d) :
    ∃ Clog : ℝ, 0 < Clog ∧
      let CK := 32 * 2 ^ sigma +
        (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
          4 ^ (sigma + 1 / 2)
      let Cref := mediumReflectedThresholdConstant Clog CK
      let g := (sigma - 1 / 2) / 2
      let Uscale := 2 / g
      1 ≤ Cref ∧ 0 < g ∧ 0 < Uscale ∧
      ∃ T₀ : ℝ, 8 ≤ T₀ ∧
        ∀ {T tau : ℝ} {Y A r : ℕ} (W : Finset ℝ), T₀ ≤ T →
          A = ⌊sharpZetaCutoff T⌋₊ → 0 < Y → 2 ≤ r →
          ((Y + 1 : ℕ) : ℝ) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2) →
          2 * (2 ^ r * Y) ≤ A →
          tau = typeILogarithmicScale T (2 ^ r * Y) →
          1 < tau → tau < 2 →
          W.Nonempty → IsSeparated 1 W →
          (∀ t ∈ W, T - T ^ d ≤ t ∧ t ≤ 2 * T + T ^ d) →
          (∀ t ∈ W,
            ((3 / 4) * (T ^ (-u) / 2)) /
                (Nat.clog 2 A + 1 : ℕ) ≤
              ‖typeISourceSmoothBlock Y A r sigma t‖) →
          let Q := 2 ^ r * Y
          let M := mediumTypeIDualCutoff T d Q
          let V := ((3 / 4) * (T ^ (-u) / 2)) /
            (Nat.clog 2 A + 1 : ℕ)
          let R := (Real.pi * V) /
            (8 * (Q : ℝ) * mediumTypeIStationaryKernel sigma T Q *
              (typeIDyadicCutoffMellinL1 + 1))
          let S := R / (2 * (M : ℝ) ^ sigma)
          let L := S / Nat.clog 2 M
          ∃ j ∈ Finset.range (Nat.clog 2 M), ∃ U : Finset ℝ,
            ∃ a : ℕ → ℂ,
              IsSeparated 1 U ∧ InBaseInterval (3 * T) U ∧
              (∀ v ∈ U, T / 2 ≤ v ∧ v ≤ 5 * T / 2) ∧
              W.card ≤ 2 * (2 * (2 * ⌈T ^ d⌉₊ + 1)) *
                (Nat.clog 2 M) * U.card ∧
              (∀ n ∈ dyadicInterval (2 ^ j), ‖a n‖ ≤ 1) ∧
              (∀ v ∈ U, L ≤ ‖dirichletPoly (2 ^ j) a v‖) ∧
              (∀ v ∈ U, ∃ w ∈ Set.Icc (T / 2) (5 * T / 2),
                ‖dirichletPoly (2 ^ j) a v‖ =
                  ‖dirichletPoly (2 ^ j)
                    (normalizedTypeIReflectedCoeff sigma M) w‖) ∧
              1 < 2 ^ j ∧ 2 ^ j < M ∧
              1 / (1 / 2 + d) ≤ typeILogarithmicScale T (2 ^ j) ∧
              typeILogarithmicScale T (2 ^ j) ≤ Uscale ∧
              T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - d) /
                  Cref ≤ L ∧
              T ^ g / Cref ≤ L := by
  obtain ⟨Clog, hClog, Tlog, hTlog, hLogs⟩ :=
    eventually_source_selection_log_product_le d hd
  let CK : ℝ := 32 * 2 ^ sigma +
    (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
      4 ^ (sigma + 1 / 2)
  have hCK : 0 < CK := by dsimp only [CK]; positivity
  let Cref : ℝ := mediumReflectedThresholdConstant Clog CK
  have hCref : 1 ≤ Cref := by
    dsimp only [Cref, mediumReflectedThresholdConstant]
    exact le_max_left _ _
  let g : ℝ := (sigma - 1 / 2) / 2
  have hg : 0 < g := by dsimp only [g]; linarith
  let Uscale : ℝ := 2 / g
  have hUscale : 0 < Uscale := by dsimp only [Uscale]; positivity
  obtain ⟨Treflect, hTreflect, hReflect⟩ :=
    eventually_interior_source_family_reflects hsigma hsigmaUpper hd hdOne
      hdGap hu huD
  obtain ⟨Tscale, hTscale, hScaleUpper⟩ :=
    eventually_threshold_forces_logarithmic_scale_upper hg hCref
  have hdStrict : d < 1 := by nlinarith [hdGap]
  obtain ⟨Twindow, hTwindow, hWindow⟩ :=
    eventually_two_mul_rpow_le_half_sub_two hd hdStrict
  let T₀ : ℝ := max Tlog (max Treflect (max Tscale Twindow))
  refine ⟨Clog, hClog, hCref, hg, hUscale, T₀,
    hTlog.trans (le_max_left _ _), ?_⟩
  intro T tau Y A r W hT hA hY hr hLower hUpper hTau htauOne htauTwo
    hW hSep hRange hLarge
  dsimp only
  have hTLog : Tlog ≤ T := (le_max_left _ _).trans hT
  have hRest : max Treflect (max Tscale Twindow) ≤ T :=
    (le_max_right _ _).trans hT
  have hTReflect : Treflect ≤ T := (le_max_left _ _).trans hRest
  have hRest₁ : max Tscale Twindow ≤ T := (le_max_right _ _).trans hRest
  have hTScale : Tscale ≤ T := (le_max_left _ _).trans hRest₁
  have hTWindow : Twindow ≤ T := (le_max_right _ _).trans hRest₁
  have hTEight : 8 ≤ T := hTlog.trans hTLog
  have hTOne : 1 ≤ T := by linarith
  have hTPos : 0 < T := by linarith
  let Q : ℕ := 2 ^ r * Y
  have hQOne : 1 < Q := by
    have hPow : 4 ≤ 2 ^ r := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hr
    have : 4 ≤ Q := by
      dsimp only [Q]
      exact hPow.trans (Nat.le_mul_of_pos_right _ hY)
    omega
  have hScale : (Q : ℝ) ^ tau = T := by
    rw [hTau]
    simpa only [Q] using rpow_typeILogarithmicScale_eq hTPos hQOne
  have hReflected := hReflect (T := T) (tau := tau) (Y := Y) (A := A)
    (r := r) W hTReflect hA hY hr hLower hUpper hTau htauOne htauTwo
      hRange hLarge hW
  let M : ℕ := mediumTypeIDualCutoff T d Q
  rcases hReflected with ⟨hMOne, hEach⟩
  have hDH : T ^ d + T ^ d ≤ T / 2 := by
    have := hWindow T hTWindow
    nlinarith
  have hExtract := extract_common_signed_reflected_block W hMOne
    (by linarith : 0 ≤ sigma) (Real.rpow_nonneg hTPos.le d) hTPos.le hDH
    hSep hRange hEach
  obtain ⟨j, hj, U, a, hSepU, hBaseU, hURange, hCardU, hCoeff,
    hLargeU, hOrdinate⟩ := hExtract
  let V : ℝ := ((3 / 4) * (T ^ (-u) / 2)) /
    (Nat.clog 2 A + 1 : ℕ)
  let R : ℝ := (Real.pi * V) /
    (8 * (Q : ℝ) * mediumTypeIStationaryKernel sigma T Q *
      (typeIDyadicCutoffMellinL1 + 1))
  let S : ℝ := R / (2 * (M : ℝ) ^ sigma)
  let L : ℝ := S / Nat.clog 2 M
  have hMOne' : 1 < M := by simpa only [M, Q] using hMOne
  have hClogM : 0 < Nat.clog 2 M :=
    Nat.clog_pos Nat.one_lt_two hMOne'
  have hL : 0 < L := by
    dsimp only [L, S, R, V]
    have hKernelPos := mediumTypeIStationaryKernel_pos (sigma := sigma) hTPos
      (lt_trans Nat.zero_lt_one hQOne)
    have hMass : 0 < typeIDyadicCutoffMellinL1 + 1 := by
      linarith [typeIDyadicCutoffMellinL1_nonneg]
    positivity
  have hLogsAt := hLogs T hTLog
  have hLogProduct := medium_reflected_clog_product_le hTEight hd.le
    (by nlinarith [hdGap, hsigmaUpper] : d ≤ 1 / 2) hQOne (by linarith)
      htauTwo hScale
  have hLogsM :
      ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) *
          (Nat.clog 2 M : ℝ) ≤ Clog * T ^ d := by
    simpa only [M] using hLogProduct.trans hLogsAt
  have hMUpperRaw := mediumTypeIDualCutoff_cast_le
    (T := T) (d := d) (Q := Q) hTPos.le
  have hQEq : (Q : ℝ) = T ^ (1 / tau) :=
    natCast_eq_rpow_inv_of_rpow_eq hQOne (by linarith) hScale
  have hMUpper : (M : ℝ) ≤ T ^ (1 + d - 1 / tau) := by
    calc
      (M : ℝ) ≤ T ^ (1 + d) / Q := by simpa only [M] using hMUpperRaw
      _ = T ^ (1 + d - 1 / tau) := by
        rw [hQEq, ← Real.rpow_sub hTPos]
  have hKernel := mediumTypeIStationaryKernel_le_rpow hsigma hsigmaUpper
    hTOne hQOne htauOne htauTwo hScale
  have hThresholdRaw := medium_reflected_threshold_explicit_lower
    (sigma := sigma) (T := T) (tau := tau) (d := d) (u := u)
    (eta := d) (Clog := Clog) (CK := CK) (Q := Q) (M := M)
    (by linarith) hTOne hQOne hMOne (by linarith) hScale hMUpper hClog
    hLogsM hCK (by simpa only [CK] using hKernel)
  have hThresholdExact :
      T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - d) /
          Cref ≤ L := by
    simpa only [Cref, L, S, R, V, Q, M, hA] using hThresholdRaw
  have hExponent := medium_reflected_threshold_exponent_lower hsigma
    hsigmaUpper htauOne hd hdGap huD
  have hThreshold : T ^ g / Cref ≤ L := by
    have hPow := Real.rpow_le_rpow_of_exponent_le hTOne hExponent
    exact (div_le_div_of_nonneg_right hPow (zero_le_one.trans hCref)).trans (by
      simpa only [g, Cref, L, S, R, V, Q, M, hA] using hThresholdRaw)
  have hUNonempty : U.Nonempty := by
    by_contra hnot
    have hUZero : U.card = 0 := Finset.card_eq_zero.mpr
      (Finset.not_nonempty_iff_eq_empty.mp hnot)
    rw [hUZero, mul_zero] at hCardU
    have hWCard : 0 < W.card := hW.card_pos
    omega
  have hLToP : L ≤ ((2 ^ j : ℕ) : ℝ) :=
    unit_coeff_threshold_le_dyadic_length hL.le hUNonempty hCoeff hLargeU
  have hScaleData := hScaleUpper hTScale hL hThreshold hLToP
  rcases hScaleData with ⟨hPOne, hTauPUpper⟩
  have hPLtM : 2 ^ j < M := by
    exact Nat.pow_lt_of_lt_clog (Finset.mem_range.mp hj)
  have hTauPLower := reflected_dyadic_scale_lower_of_expanded_cutoff
    (T := T) (τ := tau) (d := d) (Q := Q) (P := 2 ^ j) (M := M)
    (by linarith) hQOne hPOne htauOne htauTwo hd.le hScale hPLtM.le
      (by simpa only [M] using hMUpperRaw)
  refine ⟨j, hj, U, a, hSepU, hBaseU, hURange, hCardU, hCoeff,
    ?_, hOrdinate, hPOne, hPLtM, hTauPLower, ?_, hThresholdExact, hThreshold⟩
  · simpa only [L, S, R, V, Q, M] using hLargeU
  · simpa only [Uscale] using hTauPUpper

/-- The literal quadratic and cubic side conditions needed by the reflected
Weyl A--B process hold uniformly on the far dyadic branch. -/
theorem eventually_reflected_weyl_geometry
    {sigma d s U : ℝ} (hsigmaUpper : sigma < 1) (hd : 0 < d)
    (hs : 0 < s) (hU : 0 < U) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ {T theta w : ℝ} {P : ℕ}, T₀ ≤ T →
      1 < P → 0 < theta → (P : ℝ) ^ theta = T →
      1 / (1 / 2 + d) ≤ theta → theta ≤ U →
      theta < 6 * sigma - 3 - s →
      T / 2 ≤ w → w ≤ 5 * T / 2 →
      (((P + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ (2 * T ^ (4 * d)) * w ∧
        w ≤ (((P + 1 : ℕ) : ℝ) ^ (3 : ℕ)) := by
  let delta : ℝ := 6 * (1 - sigma) + s
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  let rho : ℝ := delta / U
  have hrho : 0 < rho := by dsimp only [rho]; positivity
  have hTwoD : 0 < 2 * d := by positivity
  have hTopD := tendsto_rpow_atTop hTwoD
  have hEventuallyFour := (tendsto_atTop.1 hTopD) 4
  rw [eventually_atTop] at hEventuallyFour
  obtain ⟨Td, hTd⟩ := hEventuallyFour
  have hTopRho := tendsto_rpow_atTop hrho
  have hEventuallyThree := (tendsto_atTop.1 hTopRho) 3
  rw [eventually_atTop] at hEventuallyThree
  obtain ⟨Trho, hTrho⟩ := hEventuallyThree
  let T₀ := max 8 (max Td Trho)
  refine ⟨T₀, le_max_left _ _, ?_⟩
  intro T theta w P hT hP htheta hScale hthetaLower hthetaUpper hthetaFar
    hwLower hwUpper
  have hTEight : 8 ≤ T := (le_max_left _ _).trans hT
  have hTRest : max Td Trho ≤ T := (le_max_right _ _).trans hT
  have hTD : Td ≤ T := (le_max_left _ _).trans hTRest
  have hTRho : Trho ≤ T := (le_max_right _ _).trans hTRest
  have hTOne : 1 ≤ T := by linarith
  have hTPos : 0 < T := by linarith
  have ha : 0 < 1 / 2 + d := by linarith
  have hInvTheta : 1 / theta ≤ 1 / 2 + d := by
    rw [div_le_iff₀ htheta]
    have hScaled := mul_le_mul_of_nonneg_left hthetaLower ha.le
    field_simp [ha.ne'] at hScaled
    nlinarith
  have hPEq : (P : ℝ) = T ^ (1 / theta) :=
    natCast_eq_rpow_inv_of_rpow_eq hP htheta hScale
  have hPUpper : (P : ℝ) ≤ T ^ (1 / 2 + d) := by
    rw [hPEq]
    exact Real.rpow_le_rpow_of_exponent_le hTOne hInvTheta
  have hPSucc : ((P + 1 : ℕ) : ℝ) ≤ 2 * T ^ (1 / 2 + d) := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    have hPReal : (1 : ℝ) ≤ P := by exact_mod_cast hP.le
    nlinarith [Real.rpow_nonneg hTPos.le (1 / 2 + d)]
  have hFour : 4 ≤ T ^ (2 * d) := hTd T hTD
  have hSquare : (((P + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤
      T ^ (1 + 4 * d) := by
    calc
      (((P + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤
          (2 * T ^ (1 / 2 + d)) ^ (2 : ℕ) := by gcongr
      _ = 4 * (T ^ (1 / 2 + d)) ^ (2 : ℕ) := by ring
      _ = 4 * T ^ (1 + 2 * d) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hTPos.le]
        congr 1
        ring_nf
      _ ≤ T ^ (2 * d) * T ^ (1 + 2 * d) := by gcongr
      _ = T ^ (1 + 4 * d) := by
        rw [← Real.rpow_add hTPos]
        congr 1
        ring
  have hQuadratic : (((P + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤
      (2 * T ^ (4 * d)) * w := by
    calc
      (((P + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ T ^ (1 + 4 * d) := hSquare
      _ = T ^ (4 * d) * T := by
        rw [Real.rpow_add hTPos, Real.rpow_one]
        ring
      _ ≤ (2 * T ^ (4 * d)) * w := by
        have hPow : 0 ≤ T ^ (4 * d) := Real.rpow_nonneg hTPos.le _
        nlinarith
  have hRhoTheta : rho * theta ≤ delta := by
    dsimp only [rho]
    rw [div_mul_eq_mul_div]
    exact div_le_iff₀ hU |>.2 (by
      have := mul_le_mul_of_nonneg_left hthetaUpper hdelta.le
      nlinarith)
  have hThetaDelta : theta + delta < 3 := by
    dsimp only [delta]
    linarith
  have hRhoExp : 1 + rho ≤ 3 / theta := by
    rw [le_div_iff₀ htheta]
    nlinarith
  have hThree : 3 ≤ T ^ rho := hTrho T hTRho
  have hThreeT : 3 * T ≤ T ^ (1 + rho) := by
    calc
      3 * T ≤ T ^ rho * T := by gcongr
      _ = T ^ (1 + rho) := by
        rw [Real.rpow_add hTPos, Real.rpow_one]
        ring
  have hCubeP : T ^ (1 + rho) ≤ (P : ℝ) ^ (3 : ℕ) := by
    calc
      T ^ (1 + rho) ≤ T ^ (3 / theta) :=
        Real.rpow_le_rpow_of_exponent_le hTOne hRhoExp
      _ = ((P : ℝ) ^ theta) ^ (3 / theta) := by rw [hScale]
      _ = (P : ℝ) ^ (3 : ℕ) := by
        rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ P),
          show theta * (3 / theta) = 3 by field_simp [htheta.ne']]
        exact Real.rpow_natCast (P : ℝ) 3
  refine ⟨hQuadratic, ?_⟩
  calc
    w ≤ 3 * T := by linarith
    _ ≤ T ^ (1 + rho) := hThreeT
    _ ≤ (P : ℝ) ^ (3 : ℕ) := hCubeP
    _ ≤ ((P + 1 : ℕ) : ℝ) ^ (3 : ℕ) := by
      gcongr
      norm_num

/-- The complementary far dyadic alternative exported by the actual
reflection data is impossible.  The proof uses the retained ordinate and
coefficient identity, not merely its cardinality consequence. -/
theorem eventually_reflected_far_dyadic_data_impossible
    {sigma d u s Uscale Cref : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaUpper : sigma < 1)
    (hd : 0 < d) (huD : u ≤ d)
    (hsDef : s = reflectedEndpointScaleSlack sigma d)
    (hUscale : 0 < Uscale) (hCref : 1 ≤ Cref) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧
      ∀ {T tau theta L : ℝ} {P M : ℕ} {U : Finset ℝ} {a : ℕ → ℂ},
        T₀ ≤ T → 1 < tau → tau < 2 →
        1 < P → P < M → theta = typeILogarithmicScale T P →
        theta ≤ Uscale → 1 / (1 / 2 + d) ≤ theta →
        theta < 6 * sigma - 3 - s →
        (M : ℝ) ≤ T ^ (1 + d - 1 / tau) →
        U.Nonempty →
        (∀ v ∈ U, L ≤ ‖dirichletPoly P a v‖) →
        (∀ v ∈ U, ∃ w ∈ Set.Icc (T / 2) (5 * T / 2),
          ‖dirichletPoly P a v‖ =
            ‖dirichletPoly P
              (normalizedTypeIReflectedCoeff sigma M) w‖) →
        T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - d) /
            Cref ≤ L → False := by
  have hs : 0 < s := by
    rw [hsDef]
    exact reflectedEndpointScaleSlack_pos hsigma hd
  obtain ⟨Tgeo, hTgeo, hGeo⟩ :=
    eventually_reflected_weyl_geometry hsigmaUpper hd hs hUscale
  let Cw : ℝ := 60 * 4 ^ sigma * Real.sqrt 12
  have hCw : 0 < Cw := by dsimp only [Cw]; positivity
  have hSaving : 0 < s / 24 := by positivity
  have hTop := tendsto_rpow_atTop hSaving
  have hEventually := (tendsto_atTop.1 hTop) (Cw * Cref + 1)
  rw [eventually_atTop] at hEventually
  obtain ⟨Tconst, hTconst⟩ := hEventually
  let T₀ := max Tgeo Tconst
  refine ⟨T₀, hTgeo.trans (le_max_left _ _), ?_⟩
  intro T tau theta L P M U a hT htauOne htauTwo hP hPM hthetaDef
    hthetaUpper hthetaLower hthetaFar hMUpper hUNonempty hLarge hOrdinate
    hThreshold
  have hTGeo : Tgeo ≤ T := (le_max_left _ _).trans hT
  have hTConst : Tconst ≤ T := (le_max_right _ _).trans hT
  have hTEight : 8 ≤ T := hTgeo.trans hTGeo
  have hTOne : 1 ≤ T := by linarith
  have hTStrict : 1 < T := by linarith
  have hTPos : 0 < T := by linarith
  have htheta : 0 < theta := by
    rw [hthetaDef]
    unfold typeILogarithmicScale
    exact Real.logb_pos (by exact_mod_cast hP) hTStrict
  have hScale : (P : ℝ) ^ theta = T := by
    rw [hthetaDef]
    exact rpow_typeILogarithmicScale_eq hTPos hP
  have hPEq : (P : ℝ) = T ^ (1 / theta) :=
    natCast_eq_rpow_inv_of_rpow_eq hP htheta hScale
  have hPMCast : (P : ℝ) ≤ M := by exact_mod_cast hPM.le
  have hPowerUpper : T ^ (1 / theta) ≤ T ^ (1 + d - 1 / tau) := by
    rw [← hPEq]
    exact hPMCast.trans hMUpper
  have hDual : 1 / theta ≤ 1 + d - 1 / tau :=
    (Real.strictMono_rpow_of_base_gt_one hTStrict).le_iff_le.mp hPowerUpper
  have hMargin := reflected_weyl_exponent_margin hsigma hsigmaUpper hd huD
    hsDef htauOne htauTwo hDual hthetaLower hthetaFar
  obtain ⟨v, hv⟩ := hUNonempty
  obtain ⟨w, hw, hNormEq⟩ := hOrdinate v hv
  have hwOne : 1 ≤ w := by linarith [hw.1]
  have hwThree : w ≤ 3 * T := by linarith [hw.2]
  obtain ⟨hQuadratic, hCubic⟩ := hGeo hTGeo hP htheta hScale
    hthetaLower hthetaUpper hthetaFar hw.1 hw.2
  have hWeyl := norm_normalizedTypeIReflectedCoeff_le_physical_weyl
    (sigma := sigma) (d := d) (T := T) (theta := theta) (w := w)
    (P := P) (M := M) (by linarith) hd.le hTOne hP hPM htheta hScale
      hwOne hwThree hQuadratic hCubic
  let E : ℝ := 1 / 2 - u - d * sigma + (sigma - 1) / tau - d
  let F : ℝ := 2 * d + 1 / (2 * theta) + 1 / 6
  have hExponent : F + s / 24 ≤ E := by
    dsimp only [F, E]
    linarith
  have hPowExponent : T ^ F * T ^ (s / 24) ≤ T ^ E := by
    rw [← Real.rpow_add hTPos]
    exact Real.rpow_le_rpow_of_exponent_le hTOne hExponent
  have hConst : Cw * Cref < T ^ (s / 24) :=
    (show Cw * Cref < Cw * Cref + 1 by linarith).trans_le
      (hTconst T hTConst)
  have hNormUpper : Cref * ‖dirichletPoly P a v‖ < T ^ E := by
    calc
      Cref * ‖dirichletPoly P a v‖ = Cref *
          ‖dirichletPoly P (normalizedTypeIReflectedCoeff sigma M) w‖ := by
            rw [hNormEq]
      _ ≤ Cref * (Cw * T ^ F) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa only [Cw, F] using hWeyl) (zero_le_one.trans hCref)
      _ = (Cw * Cref) * T ^ F := by ring
      _ < T ^ (s / 24) * T ^ F := by
        exact mul_lt_mul_of_pos_right hConst (Real.rpow_pos_of_pos hTPos F)
      _ = T ^ F * T ^ (s / 24) := by ring
      _ ≤ T ^ E := hPowExponent
  have hNormThreshold : ‖dirichletPoly P a v‖ < T ^ E / Cref := by
    rw [lt_div_iff₀ (zero_lt_one.trans_le hCref)]
    simpa only [mul_comm] using hNormUpper
  have hThreshold' : T ^ E / Cref ≤ L := by simpa only [E] using hThreshold
  linarith [hLarge v hv]

set_option maxHeartbeats 4000000

/-- The powered half of the reflected medium branch, from the actual
source-smooth family all the way back to the multiplicity-weighted zero
count.  The selected dyadic block and the selected natural power both occur
inside this proof; no detached cardinality certificate is accepted. -/
theorem actual_interior_reflected_near_endpoint_consumer
    {sigma tau0 : ℝ} (hsigma : 1 / 2 < sigma) (hsigmaUpper : sigma < 1)
    (hcert : EndpointScaleCertificate sigma tau0)
    (Clog : ℝ) :
    ∀ eps : ℝ, 0 < eps →
      ∃ C : ℝ, 0 < C ∧ ∃ T0 : ℝ, 8 ≤ T0 ∧ ∀ T : ℝ, T0 ≤ T →
        let d := classicalEndpointLossParameter sigma tau0 (eps / 100)
        let Y := ⌊T ^ (d ^ 2)⌋₊
        let A := ⌊sharpZetaCutoff T⌋₊
        ∀ {tau : ℝ} {r : ℕ} (W : Finset ℝ),
          A = ⌊sharpZetaCutoff T⌋₊ → 0 < Y → 2 ≤ r →
          ((Y + 1 : ℕ) : ℝ) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2) →
          2 * (2 ^ r * Y) ≤ A →
          tau = typeILogarithmicScale T (2 ^ r * Y) →
          1 < tau → tau < 2 → W.Nonempty → IsSeparated 1 W →
          (∀ t ∈ W, T - T ^ d ≤ t ∧ t ≤ 2 * T + T ^ d) →
          (∀ t ∈ W,
            ((3 / 4) * (T ^ (-(d ^ 4)) / 2)) /
                (Nat.clog 2 A + 1 : ℕ) ≤
              ‖typeISourceSmoothBlock Y A r sigma t‖) →
          zeroCountRect sigma 1 T (2 * T) ≤
            (4 * Nat.clog 2 A *
              ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T)) *
                (Nat.clog 2 A + 1) * W.card →
          let g := (sigma - 1 / 2) / 2
          let Uscale := 2 / g
          ∀ {P : ℕ}, 1 < P →
            typeILogarithmicScale T P ≤ Uscale →
            4 * tau0 / 3 - reflectedEndpointScaleSlack sigma d ≤
              typeILogarithmicScale T P →
            (∃ j U a,
              P = 2 ^ j ∧ j ∈ Finset.range
                (Nat.clog 2 (mediumTypeIDualCutoff T d (2 ^ r * Y))) ∧
              IsSeparated 1 U ∧ InBaseInterval (3 * T) U ∧
              W.card ≤ 2 * (2 * (2 * ⌈T ^ d⌉₊ + 1)) *
                Nat.clog 2 (mediumTypeIDualCutoff T d (2 ^ r * Y)) * U.card ∧
              (∀ n ∈ dyadicInterval P, ‖a n‖ ≤ 1) ∧
              let Q := 2 ^ r * Y
              let M := mediumTypeIDualCutoff T d Q
              let V := ((3 / 4) * (T ^ (-(d ^ 4)) / 2)) /
                (Nat.clog 2 A + 1 : ℕ)
              let R := (Real.pi * V) /
                (8 * (Q : ℝ) * mediumTypeIStationaryKernel sigma T Q *
                  (typeIDyadicCutoffMellinL1 + 1))
              let S := R / (2 * (M : ℝ) ^ sigma)
              let L := S / Nat.clog 2 M
              (∀ v ∈ U, L ≤ ‖dirichletPoly P a v‖) ∧
              P < M ∧
              T ^ (1 / 2 - d ^ 4 - d * sigma +
                    (sigma - 1) / tau - d) /
                  mediumReflectedThresholdConstant
                    Clog
                    (32 * 2 ^ sigma +
                      (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
                        4 ^ (sigma + 1 / 2)) ≤ L) →
            (zeroCountRect sigma 1 T (2 * T) : ℝ) ≤
              C * T ^ eps * T ^ (3 * (1 - sigma) / tau0) := by
  intro eps heps
  let eta : ℝ := eps / 100
  let d := classicalEndpointLossParameter sigma tau0 eta
  let u : ℝ := d ^ 4
  let s : ℝ := reflectedEndpointScaleSlack sigma d
  let g : ℝ := (sigma - 1 / 2) / 2
  let Uscale : ℝ := 2 / g
  let B : ℕ := ⌈3 * (Uscale + s) / (2 * tau0)⌉₊
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have hdSpec := classicalEndpointLossParameter_spec hsigma hsigmaUpper
    hcert.tau0_pos heta
  dsimp only at hdSpec
  rcases hdSpec with ⟨hd, hdEta, hdEtaTau, hdReflected, _hdGap,
    hdUpperGap, _hdSigma, _hdSmall, _hdHalf, hdOne, _hdSigmaStrict⟩
  have hu : 0 < u := by dsimp only [u]; positivity
  have hs : 0 < s := by
    dsimp only [s]
    exact reflectedEndpointScaleSlack_pos hsigma hd
  have huD : u ≤ d := by
    dsimp only [u]
    have hTwo : d ^ 2 ≤ d := by
      nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hdOne)]
    have hTwoOne : d ^ 2 ≤ 1 := hTwo.trans hdOne
    nlinarith [mul_nonneg (sq_nonneg d) (sub_nonneg.mpr hTwoOne)]
  have hg : 0 < g := by dsimp only [g]; linarith
  have hUscale : 0 < Uscale := by dsimp only [Uscale]; positivity
  have hB : 0 < B := by
    dsimp only [B]
    apply Nat.ceil_pos.mpr
    exact div_pos (mul_pos (by norm_num) (add_pos hUscale (by positivity)))
      (mul_pos (by norm_num) hcert.tau0_pos)
  have hsSmall : s ≤ tau0 / 6 := by
    dsimp only [s]
    exact reflectedEndpointScaleSlack_le_tau0_sixth hsigma hsigmaUpper hcert
      _hdGap hdUpperGap
  have hdBudget := reflected_total_power_budget_with_gap_le hsigma hsigmaUpper
    hcert.tau0_pos heta hd hdOne hdEta hdReflected
  dsimp only [s, g, Uscale, B] at hdBudget
  obtain ⟨Cpow, hCpow, K, hK, hPowered⟩ :=
    powered_unit_block_large_values_bound_bounded_uniform B d hd
  let CK : ℝ := 32 * 2 ^ sigma +
    (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
      4 ^ (sigma + 1 / 2)
  let Cref : ℝ := mediumReflectedThresholdConstant Clog CK
  have hCref : 1 ≤ Cref := by
    dsimp only [Cref, mediumReflectedThresholdConstant]
    exact le_max_left _ _
  let E : ℝ := (2 : ℝ) ^ B * Cref ^ B * Cpow
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  obtain ⟨Closs, hCloss, Tloss, hTloss, hLoss⟩ :=
    eventually_endpoint_loss_bundle_le E K d d (9 * tau0 / 16) (eps / 4) B
      hE hK.le hd hd (by nlinarith [hcert.tau0_pos]) (by nlinarith [heps]) hB
      (by dsimp only [eta] at hdEta; nlinarith)
      (by dsimp only [eta] at hdEtaTau; nlinarith)
  obtain ⟨Cmult, hCmult, Tmult, hTmult, hMult⟩ :=
    eventually_dichotomy_multiplicity_factor_bound d d hd.le hd
  obtain ⟨Ccover, hCcover, Tcover, hTcover, hCover⟩ :=
    eventually_source_selection_log_product_le (eps / 4) (by positivity)
  obtain ⟨Tscale, hTscale, hScaleDyadic⟩ :=
    eventually_dyadic_power_scale_lower_half
      (τ₀ := 3 * tau0 / 4) (U := Uscale)
      (by nlinarith [hcert.tau0_pos]) hUscale
  let C : ℝ := Closs * Cmult * Ccover * ((2 : ℝ) ^ B) ^ (2 : ℕ)
  let T0 : ℝ := max Tloss (max Tmult (max Tcover Tscale))
  refine ⟨C, by dsimp only [C]; positivity, T0,
    hTloss.trans (le_max_left _ _), ?_⟩
  intro T hT
  dsimp only
  intro tau r W hA hY hr hLower hUpper hTau htauOne htauTwo hW hSep
    hRange hLarge hCount P hPOne hTauPUpper hNear hData
  rcases hData with ⟨j, U, a, rfl, hj, hSepU, hBaseU, hCardU, hCoeff,
    hLargeU, hPM, hThresholdExact⟩
  have hTLoss : Tloss ≤ T := (le_max_left _ _).trans hT
  have hRest : max Tmult (max Tcover Tscale) ≤ T := (le_max_right _ _).trans hT
  have hTMult : Tmult ≤ T := (le_max_left _ _).trans hRest
  have hRest' : max Tcover Tscale ≤ T := (le_max_right _ _).trans hRest
  have hTCover : Tcover ≤ T := (le_max_left _ _).trans hRest'
  have hTScale : Tscale ≤ T := (le_max_right _ _).trans hRest'
  have hTEight : 8 ≤ T := hTloss.trans hTLoss
  have hTOne : 1 ≤ T := by linarith
  have hTPos : 0 < T := by linarith
  let Y : ℕ := ⌊T ^ d ^ 2⌋₊
  let A : ℕ := ⌊sharpZetaCutoff T⌋₊
  let Qsrc : ℕ := 2 ^ r * Y
  let M : ℕ := mediumTypeIDualCutoff T d Qsrc
  let Vsrc : ℝ := ((3 / 4) * (T ^ (-u) / 2)) /
    (Nat.clog 2 A + 1 : ℕ)
  let Rsrc : ℝ := (Real.pi * Vsrc) /
    (8 * (Qsrc : ℝ) * mediumTypeIStationaryKernel sigma T Qsrc *
      (typeIDyadicCutoffMellinL1 + 1))
  let Ssrc : ℝ := Rsrc / (2 * (M : ℝ) ^ sigma)
  let L : ℝ := Ssrc / Nat.clog 2 M
  have hMOne : 1 < M := by
    simpa only [M, Qsrc, Y] using hPOne.trans hPM
  have hL : 0 < L := by
    have hQsrc : 0 < Qsrc := by
      dsimp only [Qsrc, Y]
      simpa only [d] using Nat.mul_pos (pow_pos (by omega) r) hY
    have hKernelPos := mediumTypeIStationaryKernel_pos (sigma := sigma)
      hTPos hQsrc
    have hMass : 0 < typeIDyadicCutoffMellinL1 + 1 := by
      linarith [typeIDyadicCutoffMellinL1_nonneg]
    have hClogM : 0 < Nat.clog 2 M :=
      Nat.clog_pos Nat.one_lt_two hMOne
    dsimp only [L, Ssrc, Rsrc, Vsrc, A]
    positivity
  have hMUpperRaw := mediumTypeIDualCutoff_cast_le
    (T := T) (d := d) (Q := Qsrc) hTPos.le
  have hQsrcOne : 1 < Qsrc := by
    dsimp only [Qsrc, Y]
    have hpow : 4 ≤ 2 ^ r := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hr
    have : 4 ≤ 2 ^ r * ⌊T ^ d ^ 2⌋₊ :=
      hpow.trans (Nat.le_mul_of_pos_right _ (by simpa only [d] using hY))
    omega
  have hScaleSrc : (Qsrc : ℝ) ^ tau = T := by
    rw [hTau]
    simpa only [Qsrc] using rpow_typeILogarithmicScale_eq hTPos hQsrcOne
  have hQsrcEq : (Qsrc : ℝ) = T ^ (1 / tau) :=
    natCast_eq_rpow_inv_of_rpow_eq hQsrcOne (by linarith) hScaleSrc
  have hMUpper : (M : ℝ) ≤ T ^ (1 + d - 1 / tau) := by
    calc
      (M : ℝ) ≤ T ^ (1 + d) / Qsrc := by
        simpa only [M] using hMUpperRaw
      _ = T ^ (1 + d - 1 / tau) := by
        rw [hQsrcEq, ← Real.rpow_sub hTPos]
  have hD := reflected_normalization_loss_le_four_d hsigma.le hsigmaUpper
    htauOne htauTwo hd.le huD hTOne hCref hL hPM.le hMUpper
    (by simpa only [Cref, L, Ssrc, Rsrc, Vsrc, Qsrc, M, u, Y, A] using
      hThresholdExact)
  let D : ℝ := max 1 (((2 ^ j : ℕ) : ℝ) ^ sigma / L)
  have hDPos : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hDUpper : D ≤ Cref * T ^ (4 * d) := by
    simpa only [D] using hD
  obtain ⟨k, hk, hkB, hkLower, hkUpper, hkScale, hkActualLower, hkLoss⟩ :=
    exists_bounded_positive_power_augmented_endpoint_with_gap hsigmaUpper hcert
      hs.le hdUpperGap hsSmall hNear hTauPUpper
  have hP : 0 < 2 ^ j := pow_pos (by omega) j
  obtain ⟨q, hq, U', hUsub, hPowerCard, hSep', hBase', hLarge', hMHH⟩ :=
    hPowered k (2 ^ j) a 0 (3 * T) L U hk hkB hP (by norm_num)
      (by linarith) hL hCoeff hSepU hBaseU
      (by
        intro v hv
        rw [sum_zero_real_part_eq_dirichletPoly]
        simpa only [L, Ssrc, Rsrc, Vsrc, Qsrc, M, u, Y, A] using hLargeU v hv)
  let Q : ℕ := 2 ^ q * (2 ^ j) ^ k
  let Vp : ℝ := (L ^ k /
    (Cpow * ((2 ^ k * (2 ^ j) ^ k : ℕ) : ℝ) ^ d)) / k
  have hqk : q < k := Finset.mem_range.mp hq
  let Ploss := typeIIPoweredThresholdLoss Cpow
    (((2 ^ j : ℕ) : ℝ) ^ sigma) D d sigma (2 ^ j) k
  have hModel := typeII_powered_threshold_lower
    (C := Cpow) (L := (((2 ^ j : ℕ) : ℝ) ^ sigma)) (D := D)
    (η := d) (σ := sigma) (N := 2 ^ j) (k := k) (r := q)
    (by linarith [hCpow]) (by positivity) hDPos hP hk (by linarith) hqk
  dsimp only at hModel
  rcases hModel with ⟨hPloss, hModel⟩
  have hBaseToL : (((2 ^ j : ℕ) : ℝ) ^ sigma) / D ≤ L := by
    have hRatioLeD : (((2 ^ j : ℕ) : ℝ) ^ sigma) / L ≤ D :=
      le_max_right _ _
    have hCross : (((2 ^ j : ℕ) : ℝ) ^ sigma) ≤ D * L :=
      (div_le_iff₀ hL).mp hRatioLeD
    rw [div_le_iff₀ hDPos]
    calc
      (((2 ^ j : ℕ) : ℝ) ^ sigma) ≤ D * L := hCross
      _ = L * D := mul_comm _ _
  have hModelToActual :
      ((((((2 ^ j : ℕ) : ℝ) ^ sigma) / D) ^ k /
        (Cpow * ((2 ^ k * (2 ^ j) ^ k : ℕ) : ℝ) ^ d)) / k) ≤ Vp := by
    dsimp only [Vp]
    gcongr
  have hThreshold : (Q : ℝ) ^ sigma / Ploss ≤ Vp := by
    have hModel' : (Q : ℝ) ^ sigma / Ploss ≤
        ((((((2 ^ j : ℕ) : ℝ) ^ sigma) / D) ^ k /
          (Cpow * ((2 ^ k * (2 ^ j) ^ k : ℕ) : ℝ) ^ d)) / k) := by
      simpa only [Q, Ploss] using hModel
    exact hModel'.trans hModelToActual
  have hEnvelope := reflected_powered_threshold_loss_le_envelope
    (C₀ := Cref) (C := Cpow) (d := d) (sigma := sigma) (T := T)
    (D := D) (P := 2 ^ j) (k := k) (B := B) hCref hCpow hd.le
    hsigmaUpper.le (by
      calc Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
           _ ≤ T := by linarith) hDPos hDUpper hP hk hkB
  dsimp only at hEnvelope
  have hPlossEnvelope : Ploss ≤
      1 + T ^ (4 * d * k) *
        classicalTypeIIPowerLoss E d T k ((2 ^ j) ^ k) := by
    simpa only [Ploss, E] using hEnvelope
  have hFinalLength : (2 ^ j) ^ k ≤ Q := by
    dsimp only [Q]
    exact Nat.le_mul_of_pos_left _ (pow_pos (by omega) q)
  have hClassMono := classicalTypeIIPowerLoss_mono_length (k := k)
    hE hd.le hTOne hFinalLength
  have hOuter : Ploss ≤ T ^ (4 * d * k) *
      (1 + classicalTypeIIPowerLoss E d T k Q) := by
    calc
      Ploss ≤ 1 + T ^ (4 * d * k) *
          classicalTypeIIPowerLoss E d T k ((2 ^ j) ^ k) := hPlossEnvelope
      _ ≤ T ^ (4 * d * k) *
          (1 + classicalTypeIIPowerLoss E d T k Q) := by
        have hTonePow : 1 ≤ T ^ (4 * d * k) :=
          Real.one_le_rpow hTOne (by positivity)
        have hMonoAdd :
            1 + classicalTypeIIPowerLoss E d T k ((2 ^ j) ^ k) ≤
              1 + classicalTypeIIPowerLoss E d T k Q :=
          by simpa only [add_comm] using add_le_add_left hClassMono 1
        calc
          1 + T ^ (4 * d * k) *
              classicalTypeIIPowerLoss E d T k ((2 ^ j) ^ k) ≤
              T ^ (4 * d * k) + T ^ (4 * d * k) *
                classicalTypeIIPowerLoss E d T k ((2 ^ j) ^ k) := by
            gcongr
          _ = T ^ (4 * d * k) *
              (1 + classicalTypeIIPowerLoss E d T k ((2 ^ j) ^ k)) := by ring
          _ ≤ T ^ (4 * d * k) *
              (1 + classicalTypeIIPowerLoss E d T k Q) :=
            mul_le_mul_of_nonneg_left hMonoAdd
              (Real.rpow_nonneg hTPos.le (4 * d * k))
  have hPower := dyadic_power_mhh_le_endpoint_with_factor_of_augmented_scale
    hsigma hsigmaUpper hcert hTOne hPOne hk hkB hqk hkScale hkLower hkUpper
      hkLoss
  dsimp only at hPower
  have hFinalScale : 3 * tau0 / 8 ≤ typeILogarithmicScale T Q := by
    have hLowerForDyadic : 2 * (3 * tau0 / 4) / 3 ≤
        typeILogarithmicScale T (2 ^ j) / (k : ℝ) := by
      nlinarith [hkActualLower]
    have hScale := hScaleDyadic T (2 ^ j) k q hTScale hPOne hk hqk
      hTauPUpper hLowerForDyadic
    convert hScale using 1
    · ring
  let base : ℕ := 4 * Nat.clog 2 A *
    ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T)
  let cover : ℕ := Nat.clog 2 A + 1
  let extraction : ℕ :=
    (2 * (2 * (2 * ⌈T ^ d⌉₊ + 1)) * Nat.clog 2 M) * k
  have hExtractionPos : 0 < extraction := by
    dsimp only [extraction]
    have hClogMPos : 0 < Nat.clog 2 M :=
      Nat.clog_pos Nat.one_lt_two hMOne
    exact Nat.mul_pos (Nat.mul_pos (by positivity) hClogMPos) hk
  have hCount' : zeroCountRect sigma 1 T (2 * T) ≤
      (base * cover) * W.card := by
    simpa only [base, cover] using hCount
  have hExtract : (W.card : ℝ) ≤ extraction * (U'.card : ℝ) := by
    calc
      (W.card : ℝ) ≤
          (2 * (2 * (2 * ⌈T ^ d⌉₊ + 1)) * Nat.clog 2 M) *
            (U.card : ℝ) := by exact_mod_cast hCardU
      _ ≤ (2 * (2 * (2 * ⌈T ^ d⌉₊ + 1)) * Nat.clog 2 M) *
          (k * (U'.card : ℝ)) := by gcongr
      _ = extraction * (U'.card : ℝ) := by
        dsimp only [extraction]
        push_cast
        ring
  have hEndpoint := endpoint_witness_count_le_of_mhh_power_factor hTPos
    (by simpa only [Q] using
      (show 1 < 2 ^ q * (2 ^ j) ^ k by
        exact (one_lt_pow₀ hPOne hk.ne').trans_le
          (Nat.le_mul_of_pos_left _ (pow_pos (by omega) q))))
    (by exact_mod_cast hExtractionPos) hPloss hThreshold
    (R := ((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (2 * s / tau0))
    (by
      calc
        (Q : ℝ) ^ classicalMHHExponent sigma
            (typeILogarithmicScale T Q) ≤
          ((2 : ℝ) ^ B) ^ (2 : ℕ) *
            T ^ (3 * (1 - sigma) / tau0 + 2 * s / tau0) := by
              simpa only [Q] using hPower
        _ = (((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (2 * s / tau0)) *
            T ^ (3 * (1 - sigma) / tau0) := by
          rw [Real.rpow_add hTPos]
          ring)
    hCount' hExtract hK.le (by
      simpa only [Q, Vp, Real.rpow_zero, one_mul] using hMHH)
  have hBaseAt := hMult T hTMult
  have hCoverAt := hCover T hTCover
  have hClogMLe : Nat.clog 2 M ≤ Nat.clog 2 A := by
    have hMSharp := mediumTypeIDualCutoff_le_sharpZetaCutoff hTEight hd.le
      (by nlinarith [hdUpperGap, hsigmaUpper] : d ≤ 1 / 2)
      hQsrcOne (by linarith) htauTwo hScaleSrc
    exact Nat.clog_mono_right 2 (by simpa only [M, Qsrc, hA] using hMSharp)
  have hExtraLeBase :
      ((2 * (2 * (2 * ⌈T ^ d⌉₊ + 1)) * Nat.clog 2 M : ℕ) : ℝ) ≤
        (base : ℝ) := by
    have hCap : 1 ≤ classicalLocalMultiplicityCap T := by
      unfold classicalLocalMultiplicityCap
      apply Nat.ceil_pos.mpr
      have hDen : 0 < Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) := by
        apply Real.log_pos
        norm_num
      have hArg : 1 < (100 * T ^ (3 : ℝ)) / (0.6 : ℝ) := by
        have hTStrict : (1 : ℝ) < T := by linarith
        have hCube : (1 : ℝ) < T ^ (3 : ℕ) :=
          one_lt_pow₀ hTStrict (by norm_num)
        apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 0.6)).2
        norm_num [Real.rpow_natCast] at hCube ⊢
        linarith
      exact div_pos (Real.log_pos hArg) hDen
    dsimp only [base]
    exact_mod_cast (show
        2 * (2 * (2 * ⌈T ^ d⌉₊ + 1)) * Nat.clog 2 M ≤
          4 * Nat.clog 2 A *
            ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T) by
      have hLogCap : Nat.clog 2 M ≤
          Nat.clog 2 A * classicalLocalMultiplicityCap T :=
        hClogMLe.trans (Nat.le_mul_of_pos_right _ (by omega))
      calc
        2 * (2 * (2 * ⌈T ^ d⌉₊ + 1)) * Nat.clog 2 M =
            4 * (2 * ⌈T ^ d⌉₊ + 1) * Nat.clog 2 M := by ring
        _ ≤ 4 * Nat.clog 2 A *
            ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T) := by
          have := Nat.mul_le_mul_left (4 * (2 * ⌈T ^ d⌉₊ + 1)) hLogCap
          simpa only [mul_assoc, mul_left_comm, mul_comm] using this)
  have hLossAt := hLoss T Q k hTLoss (by
      dsimp only [Q]
      exact (one_lt_pow₀ hPOne hk.ne').trans_le
        (Nat.le_mul_of_pos_left _ (pow_pos (by omega) q))) hk hkB
    (by nlinarith [hFinalScale])
  have hOuterPow : Ploss ^ (6 : ℕ) ≤
      T ^ (24 * d * B) *
        (1 + classicalTypeIIPowerLoss E d T k Q) ^ (6 : ℕ) := by
    have hp := pow_le_pow_left₀ (by positivity) hOuter 6
    have hkReal : (k : ℝ) ≤ B := by exact_mod_cast hkB
    calc
      Ploss ^ (6 : ℕ) ≤
          (T ^ (4 * d * k) *
            (1 + classicalTypeIIPowerLoss E d T k Q)) ^ (6 : ℕ) := hp
      _ = T ^ (24 * d * k) *
          (1 + classicalTypeIIPowerLoss E d T k Q) ^ (6 : ℕ) := by
        rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hTPos.le]
        congr 2
        ring
      _ ≤ T ^ (24 * d * B) *
          (1 + classicalTypeIIPowerLoss E d T k Q) ^ (6 : ℕ) := by
        gcongr
  have hExtraExponent : 3 * d + 24 * d * B + 2 * s / tau0 ≤ eps / 100 := by
    have hEtaQuarter : eta / 4 = eps / 400 := by dsimp only [eta]; ring
    rw [hEtaQuarter] at hdBudget
    have hLeft : 3 * d + 24 * d * B + 2 * s / tau0 ≤
        24 * d * B + 2 * s / tau0 + 6 * d := by linarith [hd.le]
    have hRight : eps / 400 ≤ eps / 100 := by linarith
    exact hLeft.trans (hdBudget.trans hRight)
  have hExtraRpow : T ^ (3 * d) *
      (T ^ (24 * d * B) * T ^ (2 * s / tau0)) ≤ T ^ (eps / 100) := by
    rw [← Real.rpow_add hTPos, ← Real.rpow_add hTPos]
    exact Real.rpow_le_rpow_of_exponent_le hTOne (by linarith)
  have hTargetNonneg : 0 ≤ T ^ (3 * (1 - sigma) / tau0) := by positivity
  have hEndpoint' := hEndpoint
  have hEpsCombine : T ^ (eps / 4) * T ^ (eps / 4) *
      T ^ (eps / 100) ≤ T ^ eps := by
    rw [← Real.rpow_add hTPos, ← Real.rpow_add hTPos]
    exact Real.rpow_le_rpow_of_exponent_le hTOne (by linarith)
  have hExtractionBound : (extraction : ℝ) ≤ (base : ℝ) * k := by
    simpa only [extraction, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using
      mul_le_mul_of_nonneg_right hExtraLeBase
        (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hQOne : 1 < Q := by
    dsimp only [Q]
    exact (one_lt_pow₀ hPOne hk.ne').trans_le
      (Nat.le_mul_of_pos_left _ (pow_pos (by omega) q))
  have hHarmNonneg : 0 ≤ (((harmonic Q : ℚ) : ℝ)) := by
    exact_mod_cast (harmonic_pos (by omega : Q ≠ 0)).le
  have hGNonneg : 0 ≤ K * (1 + (((harmonic Q : ℚ) : ℝ))) :=
    mul_nonneg hK.le (by linarith)
  have hOldNonneg : 0 ≤
      6 * Ploss ^ (6 : ℕ) *
        (((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (2 * s / tau0)) := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (pow_nonneg (by linarith [hPloss]) 6))
      (mul_nonneg (pow_nonneg (by positivity) 2)
        (Real.rpow_nonneg hTPos.le _))
  have hPowerLossBound :
      6 * Ploss ^ (6 : ℕ) *
          (((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (2 * s / tau0)) ≤
        (6 * (1 + classicalTypeIIPowerLoss E d T k Q) ^ (6 : ℕ)) *
          (((2 : ℝ) ^ B) ^ (2 : ℕ) *
            (T ^ (24 * d * B) * T ^ (2 * s / tau0))) := by
    calc
      6 * Ploss ^ (6 : ℕ) *
            (((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (2 * s / tau0)) ≤
          6 * (T ^ (24 * d * B) *
            (1 + classicalTypeIIPowerLoss E d T k Q) ^ (6 : ℕ)) *
            (((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (2 * s / tau0)) := by
        gcongr
      _ = (6 * (1 + classicalTypeIIPowerLoss E d T k Q) ^ (6 : ℕ)) *
          (((2 : ℝ) ^ B) ^ (2 : ℕ) *
            (T ^ (24 * d * B) * T ^ (2 * s / tau0))) := by ring
  have hInnerBound :
      ((extraction : ℝ) * (K * (1 + (((harmonic Q : ℚ) : ℝ))))) *
          (6 * Ploss ^ (6 : ℕ) *
            (((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (2 * s / tau0))) ≤
        (((base : ℝ) * k * (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
            (6 * (1 + classicalTypeIIPowerLoss E d T k Q) ^ (6 : ℕ))) *
          (((2 : ℝ) ^ B) ^ (2 : ℕ) *
            (T ^ (24 * d * B) * T ^ (2 * s / tau0)))) := by
    calc
      ((extraction : ℝ) * (K * (1 + (((harmonic Q : ℚ) : ℝ))))) *
            (6 * Ploss ^ (6 : ℕ) *
              (((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (2 * s / tau0))) ≤
          (((base : ℝ) * k) * (K * (1 + (((harmonic Q : ℚ) : ℝ))))) *
            (6 * Ploss ^ (6 : ℕ) *
              (((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (2 * s / tau0))) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hExtractionBound hGNonneg)
          hOldNonneg
      _ ≤ (((base : ℝ) * k) * (K * (1 + (((harmonic Q : ℚ) : ℝ))))) *
          ((6 * (1 + classicalTypeIIPowerLoss E d T k Q) ^ (6 : ℕ)) *
            (((2 : ℝ) ^ B) ^ (2 : ℕ) *
              (T ^ (24 * d * B) * T ^ (2 * s / tau0)))) := by
        exact mul_le_mul_of_nonneg_left hPowerLossBound
          (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hGNonneg)
      _ = (((base : ℝ) * k * (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
            (6 * (1 + classicalTypeIIPowerLoss E d T k Q) ^ (6 : ℕ))) *
          (((2 : ℝ) ^ B) ^ (2 : ℕ) *
            (T ^ (24 * d * B) * T ^ (2 * s / tau0)))) := by ring
  have hCoverSimple : (cover : ℝ) ≤ Ccover * T ^ (eps / 4) := by
    have hAOne : 1 < ⌊sharpZetaCutoff T⌋₊ := by
      apply lt_of_lt_of_le (by omega : 1 < (2 : ℕ))
      apply Nat.le_floor
      exact (show (2 : ℝ) ≤ 4 * T by
        calc
          (2 : ℝ) ≤ 4 * 8 := by norm_num
          _ ≤ 4 * T := mul_le_mul_of_nonneg_left hTEight (by norm_num)).trans
        (four_mul_lt_sharpZetaCutoff T).le
    have hSecondClog : (1 : ℝ) ≤
        Nat.clog 2 (⌊sharpZetaCutoff T⌋₊ + 1) := by
      have hclog : 0 < Nat.clog 2 (⌊sharpZetaCutoff T⌋₊ + 1) :=
        Nat.clog_pos Nat.one_lt_two (by omega)
      exact_mod_cast hclog
    have hCoverOne : (1 : ℝ) ≤ Nat.clog 2 (A + 1) := by
      simpa only [A] using hSecondClog
    have hnonneg : 0 ≤ (cover : ℝ) := by positivity
    calc
      (cover : ℝ) = (cover : ℝ) * 1 := by ring
      _ ≤ (cover : ℝ) * Nat.clog 2 (A + 1) :=
        mul_le_mul_of_nonneg_left hCoverOne hnonneg
      _ ≤ Ccover * T ^ (eps / 4) := by
        simpa only [cover, A] using hCoverAt
  have hBaseAt' : (base : ℝ) ≤ Cmult * T ^ (3 * d) := by
    calc
      (base : ℝ) ≤ Cmult * T ^ (d + 2 * d) := by
        simpa only [base, A, hA] using hBaseAt
      _ = Cmult * T ^ (3 * d) := by
        congr 1
        ring_nf
  have hLossAt' :
      (base : ℝ) * k * (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
          (6 * (1 + classicalTypeIIPowerLoss E d T k Q) ^ (6 : ℕ)) ≤
        Closs * T ^ (eps / 4) := by
    simpa only [base, A, hA] using hLossAt
  have hMiddleRpow :
      (Cmult * T ^ (3 * d)) * (Closs * T ^ (eps / 4)) *
          (((2 : ℝ) ^ B) ^ (2 : ℕ) *
            (T ^ (24 * d * B) * T ^ (2 * s / tau0))) ≤
        (Cmult * (Closs * T ^ (eps / 4))) *
          (((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (eps / 100)) := by
    calc
      (Cmult * T ^ (3 * d)) * (Closs * T ^ (eps / 4)) *
            (((2 : ℝ) ^ B) ^ (2 : ℕ) *
              (T ^ (24 * d * B) * T ^ (2 * s / tau0))) =
          (Cmult * Closs * T ^ (eps / 4) * (((2 : ℝ) ^ B) ^ (2 : ℕ))) *
            (T ^ (3 * d) *
              (T ^ (24 * d * B) * T ^ (2 * s / tau0))) := by ring
      _ ≤ (Cmult * Closs * T ^ (eps / 4) * (((2 : ℝ) ^ B) ^ (2 : ℕ))) *
          T ^ (eps / 100) :=
        mul_le_mul_of_nonneg_left hExtraRpow (by positivity)
      _ = (Cmult * (Closs * T ^ (eps / 4))) *
          (((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (eps / 100)) := by ring
  calc
    (zeroCountRect sigma 1 T (2 * T) : ℝ) ≤ _ := hEndpoint'
    _ = ((cover : ℝ) * (base : ℝ)) *
        (((extraction : ℝ) * (K * (1 + (((harmonic Q : ℚ) : ℝ))))) *
          (6 * Ploss ^ (6 : ℕ) *
            (((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (2 * s / tau0)))) *
          T ^ (3 * (1 - sigma) / tau0) := by
      dsimp only [base, cover, extraction] at hEndpoint' ⊢
      norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hEndpoint' ⊢
      ring
    _ ≤ ((cover : ℝ) * (base : ℝ)) *
        (((base : ℝ) * k * (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
          (6 * (1 + classicalTypeIIPowerLoss E d T k Q) ^ (6 : ℕ))) *
          (((2 : ℝ) ^ B) ^ (2 : ℕ) *
            (T ^ (24 * d * B) * T ^ (2 * s / tau0)))) *
          T ^ (3 * (1 - sigma) / tau0) := by
      apply mul_le_mul_of_nonneg_right _ hTargetNonneg
      exact mul_le_mul_of_nonneg_left hInnerBound (by positivity)
    _ ≤ (Ccover * T ^ (eps / 4)) *
        ((Cmult * T ^ (3 * d)) * (Closs * T ^ (eps / 4)) *
          (((2 : ℝ) ^ B) ^ (2 : ℕ) *
            (T ^ (24 * d * B) * T ^ (2 * s / tau0)))) *
          T ^ (3 * (1 - sigma) / tau0) := by
      have hFront :
          ((cover : ℝ) * (base : ℝ)) *
              ((base : ℝ) * k *
                (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
                (6 * (1 + classicalTypeIIPowerLoss E d T k Q) ^ (6 : ℕ))) ≤
            (Ccover * T ^ (eps / 4)) *
              ((Cmult * T ^ (3 * d)) * (Closs * T ^ (eps / 4))) := by
        calc
          ((cover : ℝ) * (base : ℝ)) *
                ((base : ℝ) * k *
                  (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
                  (6 * (1 + classicalTypeIIPowerLoss E d T k Q) ^ (6 : ℕ))) ≤
              (Ccover * T ^ (eps / 4)) * (Cmult * T ^ (3 * d)) *
                (Closs * T ^ (eps / 4)) := by gcongr
          _ = (Ccover * T ^ (eps / 4)) *
              ((Cmult * T ^ (3 * d)) * (Closs * T ^ (eps / 4))) := by ring
      apply mul_le_mul_of_nonneg_right _ hTargetNonneg
      have hFactorNonneg : 0 ≤
          (((2 : ℝ) ^ B) ^ (2 : ℕ) *
            (T ^ (24 * d * B) * T ^ (2 * s / tau0))) := by positivity
      have h := mul_le_mul_of_nonneg_right hFront hFactorNonneg
      convert h using 1 <;> ring
    _ ≤ (Ccover * T ^ (eps / 4)) *
        ((Cmult * (Closs * T ^ (eps / 4))) *
          (((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (eps / 100))) *
          T ^ (3 * (1 - sigma) / tau0) := by
      have hOuterNonneg : 0 ≤ Ccover * T ^ (eps / 4) := by positivity
      have h := mul_le_mul_of_nonneg_left hMiddleRpow hOuterNonneg
      have h' := mul_le_mul_of_nonneg_right h hTargetNonneg
      exact h'
    _ ≤ C * T ^ eps * T ^ (3 * (1 - sigma) / tau0) := by
      dsimp only [C]
      calc
        (Ccover * T ^ (eps / 4)) *
            ((Cmult * (Closs * T ^ (eps / 4))) *
              (((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (eps / 100))) *
              T ^ (3 * (1 - sigma) / tau0) =
          (Closs * Cmult * Ccover * ((2 : ℝ) ^ B) ^ (2 : ℕ)) *
            (T ^ (eps / 4) * T ^ (eps / 4) * T ^ (eps / 100)) *
              T ^ (3 * (1 - sigma) / tau0) := by ring
        _ ≤ (Closs * Cmult * Ccover * ((2 : ℝ) ^ B) ^ (2 : ℕ)) *
            T ^ eps * T ^ (3 * (1 - sigma) / tau0) := by gcongr

/-! ## Checked reflected endpoint assembly -/

/-
noncomputable def mediumReflectedMHHExponent (σ τ : ℝ) : ℝ :=
  max (1 - 2 * σ / τ)
    (min (1 + (1 - 2 * σ) / τ)
      (2 + (2 - 6 * σ) / τ))

theorem mediumReflectedMHHExponent_le_endpoint
    {σ τ₀ τ : ℝ}
    (hσLower : 1 / 2 < σ) (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀)
    (hτ₀ : τ₀ < τ) (hτPos : 0 < τ)
    (hτTwo : τ < 2) (hτUpper : τ < 4 * τ₀ / 3)
    (hNotWeyl : 6 * σ - 3 ≤ τ) :
    mediumReflectedMHHExponent σ τ ≤
      3 * (1 - σ) / τ₀ := by
  have hτ₀Pos := hcert.tau0_pos
  rw [mediumReflectedMHHExponent, max_le_iff]
  constructor
  · rw [le_div_iff₀ hτ₀Pos]
    field_simp [hτPos.ne']
    rcases endpointScaleCertificate_tau0_alternative hσUpper hcert with hI | hH
    · by_cases hsign : 0 ≤ τ - 2 * σ
      · have hmul := mul_le_mul_of_nonneg_left hI hsign
        nlinarith
      · nlinarith
    · by_cases hsign : 0 ≤ τ - 2 * σ
      · have hmul := mul_le_mul_of_nonneg_left hH hsign
        nlinarith
      · nlinarith
  · rw [min_le_iff]
    by_cases hswitch : τ ≤ 4 * σ - 1
    · right
      rw [le_div_iff₀ hτ₀Pos]
      field_simp [hτPos.ne']
      rcases endpointScaleCertificate_tau0_alternative hσUpper hcert with hI | hH
      · by_cases hsign : 0 ≤ 2 * τ + 2 - 6 * σ
        · have hmul := mul_le_mul_of_nonneg_left hI hsign
          nlinarith
        · nlinarith
      · by_cases hsign : 0 ≤ 2 * τ + 2 - 6 * σ
        · have hmul := mul_le_mul_of_nonneg_left hH hsign
          nlinarith
        · nlinarith
    · left
      have hswitch' : 4 * σ - 1 < τ := lt_of_not_ge hswitch
      rw [le_div_iff₀ hτ₀Pos]
      field_simp [hτPos.ne']
      rcases endpointScaleCertificate_tau0_alternative hσUpper hcert with hI | hH
      · by_cases hsign : 0 ≤ τ + 1 - 2 * σ
        · have hmul := mul_le_mul_of_nonneg_left hI hsign
          nlinarith
        · nlinarith
      · by_cases hsign : 0 ≤ τ + 1 - 2 * σ
        · have hmul := mul_le_mul_of_nonneg_left hH hsign
          nlinarith
        · nlinarith
-/

/-- A classified interior source block in the endpoint gap cannot have
physical logarithmic scale at least two.  The endpoint certificate first
forces the Huxley alternative and hence `σ > 5/6`; the strengthened common
loss parameter then pays for the detector and source-selection losses in
the physical Weyl estimate. -/
theorem eventually_medium_source_tau_ge_two_impossible
    {σ τ₀ ε : ℝ} (hσ : 1 / 2 < σ) (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀) (hε : 0 < ε) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧
      ∀ {T τ : ℝ} {Y A r : ℕ} (W : Finset ℝ), T₀ ≤ T →
        let d := classicalEndpointLossParameter σ τ₀ (ε / 100)
        A = ⌊sharpZetaCutoff T⌋₊ → 0 < Y → 2 ≤ r →
        2 * (2 ^ r * Y) ≤ A →
        τ = typeILogarithmicScale T (2 ^ r * Y) →
        2 ≤ τ → τ < 4 * τ₀ / 3 →
        T ^ d ≤ T / 2 → W.Nonempty →
        (∀ t ∈ W, T - T ^ d ≤ t ∧ t ≤ 2 * T + T ^ d) →
        (∀ t ∈ W,
          ((3 / 4) * (T ^ (-(d ^ 4)) / 2)) /
              (Nat.clog 2 A + 1 : ℕ) ≤
            ‖typeISourceSmoothBlock Y A r σ t‖) →
        False := by
  let d := classicalEndpointLossParameter σ τ₀ (ε / 100)
  have hεsmall : 0 < ε / 100 := by positivity
  have hdSpec := classicalEndpointLossParameter_spec hσ hσUpper
    hcert.tau0_pos hεsmall
  dsimp only at hdSpec
  rcases hdSpec with ⟨hd, _hdEps, _hdEpsTau, _hdReflected, _hdGap,
    _hdUpper, _hdSigma, _hdSmall, _hdHalf, hdOne, _hdSigmaStrict⟩
  by_cases hσFiveSixths : 5 / 6 < σ
  · let q : ℝ := 2 * σ - 5 / 3
    have hq : 0 < q := by dsimp only [q]; linarith
    have hdFiveSixths : d ≤ (σ - 5 / 6) / 1000 := by
      dsimp only [d]
      exact classicalEndpointLossParameter_le_fiveSixthsGap hσFiveSixths
    let v : ℝ := q / 72
    have hv : 0 < v := by dsimp only [v]; positivity
    have hBudget : d ^ 4 + v < q / 18 := by
      have hdSq : d ^ 2 ≤ d := by
        nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hdOne)]
      have hdSqOne : d ^ 2 ≤ 1 := hdSq.trans hdOne
      have hdFourth : d ^ 4 ≤ d := by
        nlinarith [mul_nonneg (sq_nonneg d) (sub_nonneg.mpr hdSqOne)]
      have hdq : d ≤ q / 2000 := by
        dsimp only [q] at hdFiveSixths ⊢
        linarith
      dsimp only [v]
      nlinarith
    obtain ⟨Clog, _hClog, Tlog, hTlog, hLogs⟩ :=
      eventually_source_selection_log_product_le v hv
    obtain ⟨Tfar, hTfar, hFar⟩ := eventually_source_far_family_impossible
      hσUpper hq (by dsimp only [q]; linarith) hBudget
    let T₀ : ℝ := max Tlog Tfar
    refine ⟨T₀, hTlog.trans (le_max_left _ _), ?_⟩
    intro T τ Y A r W hT
    dsimp only
    intro hA hY hr hInterior hτ hτTwo hτUpper hDisp hW hRange hLarge
    have hTLog : Tlog ≤ T := (le_max_left _ _).trans hT
    have hTFar : Tfar ≤ T := (le_max_right _ _).trans hT
    have hLogProduct := hLogs T hTLog
    have hAOne : 1 < A := by
      rw [hA]
      apply lt_of_lt_of_le (by omega : 1 < (2 : ℕ))
      apply Nat.le_floor
      exact (show (2 : ℝ) ≤ 4 * T by nlinarith [hTlog]).trans
        (four_mul_lt_sharpZetaCutoff T).le
    have hSecond : (1 : ℝ) ≤ Nat.clog 2 (A + 1) := by
      exact_mod_cast Nat.clog_pos Nat.one_lt_two (by omega : 1 < A + 1)
    have hFirstNonneg : (0 : ℝ) ≤ ((Nat.clog 2 A + 1 : ℕ) : ℝ) := by
      positivity
    have hLog : ((Nat.clog 2 A + 1 : ℕ) : ℝ) ≤ Clog * T ^ v := by
      calc
        ((Nat.clog 2 A + 1 : ℕ) : ℝ) =
            ((Nat.clog 2 A + 1 : ℕ) : ℝ) * 1 := by ring
        _ ≤ ((Nat.clog 2 A + 1 : ℕ) : ℝ) * Nat.clog 2 (A + 1) :=
          mul_le_mul_of_nonneg_left hSecond hFirstNonneg
        _ ≤ Clog * T ^ v := by simpa only [hA] using hLogProduct
    have hCertAlternative := endpointScaleCertificate_tau0_alternative hσUpper hcert
    have hTauFar : τ < 6 * σ - 3 - q := by
      rcases hCertAlternative with hI | hH
      · have hBound : 4 * τ₀ / 3 ≤ 4 * (2 - σ) / 3 := by gcongr
        nlinarith
      · have hBound : 4 * τ₀ / 3 ≤ 4 * (3 * σ - 1) / 3 := by gcongr
        dsimp only [q]
        nlinarith
    exact hFar W hTFar hA hY hr hInterior hτ hτTwo hTauFar hDisp hW
      hRange hLog (by simpa only [d] using hLarge)
  · refine ⟨8, le_rfl, ?_⟩
    intro T τ Y A r W hT
    dsimp only
    intro _hA _hY _hr _hInterior _hτ hτTwo hτUpper _hDisp _hW _hRange _hLarge
    have hσLe : σ ≤ 5 / 6 := le_of_not_gt hσFiveSixths
    rcases endpointScaleCertificate_tau0_alternative hσUpper hcert with hI | hH
    · have hBound : 4 * τ₀ / 3 ≤ 4 * (2 - σ) / 3 := by gcongr
      nlinarith
    · have hBound : 4 * τ₀ / 3 ≤ 4 * (3 * σ - 1) / 3 := by gcongr
      nlinarith

/-- Complete consumer for the genuinely reflected source range.  It invokes
the actual pointwise Poisson reflection, selects its common signed dyadic
block, and then dispatches the exhaustive powered/Weyl scale split while
retaining the original multiplicity-weighted count. -/
theorem actual_interior_reflected_endpoint_consumer
    {σ τ₀ : ℝ} (hσ : 1 / 2 < σ) (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
        let d := classicalEndpointLossParameter σ τ₀ (ε / 100)
        let Y := ⌊T ^ (d ^ 2)⌋₊
        let A := ⌊sharpZetaCutoff T⌋₊
        ∀ {τ : ℝ} {r : ℕ} (W : Finset ℝ),
          A = ⌊sharpZetaCutoff T⌋₊ → 0 < Y → 2 ≤ r →
          ((Y + 1 : ℕ) : ℝ) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2) →
          2 * (2 ^ r * Y) ≤ A →
          τ = typeILogarithmicScale T (2 ^ r * Y) →
          1 < τ → τ < 2 → W.Nonempty → IsSeparated 1 W →
          (∀ t ∈ W, T - T ^ d ≤ t ∧ t ≤ 2 * T + T ^ d) →
          (∀ t ∈ W,
            ((3 / 4) * (T ^ (-(d ^ 4)) / 2)) /
                (Nat.clog 2 A + 1 : ℕ) ≤
              ‖typeISourceSmoothBlock Y A r σ t‖) →
          zeroCountRect σ 1 T (2 * T) ≤
            (4 * Nat.clog 2 A *
              ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T)) *
                (Nat.clog 2 A + 1) * W.card →
          (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
            C * T ^ ε * T ^ (3 * (1 - σ) / τ₀) := by
  intro ε hε
  let d := classicalEndpointLossParameter σ τ₀ (ε / 100)
  let u : ℝ := d ^ 4
  have hεsmall : 0 < ε / 100 := by positivity
  have hdSpec := classicalEndpointLossParameter_spec hσ hσUpper
    hcert.tau0_pos hεsmall
  dsimp only at hdSpec
  rcases hdSpec with ⟨hd, _hdEps, _hdEpsTau, _hdReflected, hdGap,
    _hdUpper, _hdSigma, _hdSmall, _hdHalf, hdOne, _hdSigmaStrict⟩
  have hu : 0 < u := by dsimp only [u]; positivity
  have huD : u ≤ d := by
    dsimp only [u]
    have hdSq : d ^ 2 ≤ d := by
      nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hdOne)]
    have hdSqOne : d ^ 2 ≤ 1 := hdSq.trans hdOne
    nlinarith [mul_nonneg (sq_nonneg d) (sub_nonneg.mpr hdSqOne)]
  obtain ⟨Clog, _hClog, hCref, hg, hUscale, Tdata, hTdata, hData⟩ :=
    eventually_interior_source_reflected_dyadic_data hσ hσUpper hd hdOne
      hdGap hu.le huD
  obtain ⟨Cnear, hCnear, Tnear, hTnear, hNear⟩ :=
    actual_interior_reflected_near_endpoint_consumer hσ hσUpper hcert
      Clog ε hε
  let s : ℝ := reflectedEndpointScaleSlack σ d
  obtain ⟨Tfar, hTfar, hFar⟩ := eventually_reflected_far_dyadic_data_impossible
    hσ hσUpper hd huD rfl hUscale hCref
  let T₀ : ℝ := max Tdata (max Tnear Tfar)
  refine ⟨Cnear, hCnear, T₀, hTdata.trans (le_max_left _ _), ?_⟩
  intro T hT
  dsimp only
  intro τ r W hA hY hr hLower hUpper hτ hτOne hτTwo hW hSep hRange
    hLarge hCount
  have hTData : Tdata ≤ T := (le_max_left _ _).trans hT
  have hRest : max Tnear Tfar ≤ T := (le_max_right _ _).trans hT
  have hTNear : Tnear ≤ T := (le_max_left _ _).trans hRest
  have hTFar : Tfar ≤ T := (le_max_right _ _).trans hRest
  have hTPos : 0 < T := by linarith [hTdata]
  let Y : ℕ := ⌊T ^ (d ^ 2)⌋₊
  let A : ℕ := ⌊sharpZetaCutoff T⌋₊
  have hDataAt := hData (T := T) (tau := τ) (Y := Y) (A := A)
    (r := r) W hTData hA hY hr hLower hUpper hτ hτOne hτTwo hW hSep
      hRange (by simpa only [u] using hLarge)
  dsimp only at hDataAt
  rcases hDataAt with ⟨j, hj, U, a, hSepU, hBaseU, hURange, hCardU,
    hCoeff, hLargeU, hOrdinate, hPOne, hPM, hThetaLower, hThetaUpper,
    hThresholdExact, _hThresholdGap⟩
  let P : ℕ := 2 ^ j
  let Q : ℕ := 2 ^ r * Y
  let M : ℕ := mediumTypeIDualCutoff T d Q
  let V : ℝ := ((3 / 4) * (T ^ (-u) / 2)) /
    (Nat.clog 2 A + 1 : ℕ)
  let R : ℝ := (Real.pi * V) /
    (8 * (Q : ℝ) * mediumTypeIStationaryKernel σ T Q *
      (typeIDyadicCutoffMellinL1 + 1))
  let S : ℝ := R / (2 * (M : ℝ) ^ σ)
  let L : ℝ := S / Nat.clog 2 M
  let θ : ℝ := typeILogarithmicScale T P
  have hSplit := reflected_actual_scale_powered_gap_or_weyl_margin
    hσ hσUpper hcert hd (by simpa only [θ] using hThetaLower)
  dsimp only at hSplit
  rcases hSplit with hNearScale | hFarScale
  · apply hNear T hTNear W hA hY hr hLower hUpper hτ hτOne hτTwo hW hSep
      hRange (by simpa only [u] using hLarge) hCount
      (by simpa only [P] using hPOne) (by simpa only [P] using hThetaUpper)
      (by simpa only [P, θ] using hNearScale)
    refine ⟨j, U, a, rfl, hj, hSepU, hBaseU, hCardU, hCoeff, ?_, ?_, ?_⟩
    · simpa only [P, Q, M, V, R, S, L, u] using hLargeU
    · simpa only [P, M] using hPM
    · simpa only [Q, M, V, R, S, L, u] using hThresholdExact
  · have hUNonempty : U.Nonempty := by
      by_contra hnot
      have hUZero : U.card = 0 := Finset.card_eq_zero.mpr
        (Finset.not_nonempty_iff_eq_empty.mp hnot)
      rw [hUZero, mul_zero] at hCardU
      have hWCard : 0 < W.card := hW.card_pos
      omega
    have hQOne : 1 < Q := by
      dsimp only [Q]
      have hPow : 4 ≤ 2 ^ r := by
        simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hr
      have : 4 ≤ 2 ^ r * Y := hPow.trans (Nat.le_mul_of_pos_right _ hY)
      omega
    have hScaleQ : (Q : ℝ) ^ τ = T := by
      rw [hτ]
      simpa only [Q] using rpow_typeILogarithmicScale_eq hTPos hQOne
    have hQEq : (Q : ℝ) = T ^ (1 / τ) :=
      natCast_eq_rpow_inv_of_rpow_eq hQOne (by linarith) hScaleQ
    have hMUpperRaw := mediumTypeIDualCutoff_cast_le
      (T := T) (d := d) (Q := Q) hTPos.le
    have hMUpper : (M : ℝ) ≤ T ^ (1 + d - 1 / τ) := by
      calc
        (M : ℝ) ≤ T ^ (1 + d) / Q := by simpa only [M] using hMUpperRaw
        _ = T ^ (1 + d - 1 / τ) := by
          rw [hQEq, ← Real.rpow_sub hTPos]
    exact (hFar hTFar hτOne hτTwo (by simpa only [P] using hPOne)
      (by simpa only [P, M] using hPM) (by rfl)
      (by simpa only [θ, P] using hThetaUpper)
      (by simpa only [θ, P] using hThetaLower)
      (by simpa only [s, θ, P] using hFarScale) hMUpper hUNonempty
      (by simpa only [P, L] using hLargeU)
      (by simpa only [P, M] using hOrdinate)
      (by simpa only [L, u] using hThresholdExact)).elim

/-- Exhaustive endpoint consumer for the literal smooth source block selected
from the detector's long tail.  Every alternative is discharged on the same
zero family and with the multiplicity factor retained: the lower family uses
direct powering, the terminal family is impossible, a near extracted dyadic
scale uses finite powering, and the remaining interior scale is either ruled
out by Weyl or consumed by the reflected B-process. -/
theorem actual_selected_source_endpoint_consumer
    {σ τ₀ : ℝ} (hσ : 1 / 2 < σ) (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
        let d := classicalEndpointLossParameter σ τ₀ (ε / 100)
        let Y := ⌊T ^ (d ^ 2)⌋₊
        let A := ⌊sharpZetaCutoff T⌋₊
        ∀ r : ℕ, ∀ W : Finset ℝ,
          W.Nonempty → IsSeparated 1 W →
          (∀ t ∈ W, T - T ^ d ≤ t ∧ t ≤ 2 * T + T ^ d) →
          (∀ t ∈ W,
            ((3 / 4) * (T ^ (-(d ^ 4)) / 2)) /
                (Nat.clog 2 A + 1 : ℕ) ≤
              ‖typeISourceSmoothBlock Y A r σ t‖) →
          zeroCountRect σ 1 T (2 * T) ≤
            (4 * Nat.clog 2 A *
              ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T)) *
                (Nat.clog 2 A + 1) * W.card →
          (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
            C * T ^ ε * T ^ (3 * (1 - σ) / τ₀) := by
  intro ε hε
  let d := classicalEndpointLossParameter σ τ₀ (ε / 100)
  let s := reflectedEndpointScaleSlack σ d
  have hεsmall : 0 < ε / 100 := by positivity
  have hdSpec := classicalEndpointLossParameter_spec hσ hσUpper
    hcert.tau0_pos hεsmall
  dsimp only at hdSpec
  rcases hdSpec with ⟨hd, _hdEps, _hdEpsTau, _hdReflected, hdGap,
    _hdUpper, _hdSigma, hdSmall, _hdHalf, hdOne, _hdSigmaStrict⟩
  have hdOneStrict : d < 1 := by
    have hDen : 1 < 1000 * (1 + τ₀) := by nlinarith [hcert.tau0_pos]
    exact hdSmall.trans_lt (by
      simpa only [one_div] using inv_lt_one_of_one_lt₀ hDen)
  have hs : 0 < s := by
    dsimp only [s]
    exact reflectedEndpointScaleSlack_pos hσ hd
  have huD : d ^ 4 ≤ d := by
    have hdSq : d ^ 2 ≤ d := by
      nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hdOne)]
    have hdSqOne : d ^ 2 ≤ 1 := hdSq.trans hdOne
    nlinarith [mul_nonneg (sq_nonneg d) (sub_nonneg.mpr hdSqOne)]
  have huGap : d ^ 4 < σ - 1 / 2 :=
    huD.trans_lt (hdGap.trans_lt (by nlinarith [hσ]))
  obtain ⟨Clower, hClower, Tlower, hTlower, hLower⟩ :=
    actual_lower_source_family_endpoint_consumer hσ hσUpper hcert ε hε
  obtain ⟨Cnear, hCnear, Tnear, hTnear, hNear⟩ :=
    actual_source_near_endpoint_consumer hσ hσUpper hcert ε hε
  obtain ⟨Cref, hCref, Tref, hTref, hRef⟩ :=
    actual_interior_reflected_endpoint_consumer hσ hσUpper hcert ε hε
  obtain ⟨Tterminal, hTterminal, hTerminal⟩ :=
    eventually_no_terminal_classified_source hσ huGap
  obtain ⟨Tmargin, hTmargin, hMargin⟩ :=
    eventually_large_source_forces_complementary_margin hσUpper hd hdOneStrict
      hdGap huD
  obtain ⟨Tdisp, hTdisp, hDisp⟩ := eventually_rpow_le_half_self d hdOneStrict
  obtain ⟨Tscale, hTscale, hScale⟩ :=
    eventually_typeI_logarithmic_scale_upper (d ^ 2) (sq_pos_of_pos hd)
  obtain ⟨Tadd, hTadd, hAdd⟩ :=
    eventually_extracted_source_logarithmic_scale_lower_additive
      (δ := s) (U := 2 / (d ^ 2)) hs
      (div_pos (by norm_num) (sq_pos_of_pos hd))
  obtain ⟨Ttwo, hTtwo, hTwoImpossible⟩ :=
    eventually_medium_source_tau_ge_two_impossible hσ hσUpper hcert hε
  have hPowTop := tendsto_rpow_atTop (sq_pos_of_pos hd)
  have hEventuallyY := (tendsto_atTop.1 hPowTop) 16
  rw [eventually_atTop] at hEventuallyY
  obtain ⟨TY, hTY⟩ := hEventuallyY
  let C : ℝ := max Clower (max Cnear Cref)
  let T₀ : ℝ := max Tlower
    (max Tnear (max Tref (max Tterminal
      (max Tmargin (max Tdisp (max Tscale (max Tadd (max Ttwo (max 8 TY)))))))))
  have hC : 0 < C := hClower.trans_le (le_max_left _ _)
  have hT₀ : 8 ≤ T₀ := hTlower.trans (le_max_left _ _)
  refine ⟨C, hC, T₀, hT₀, ?_⟩
  intro T hT
  dsimp only
  intro r W hW hSep hRange hLarge hCount
  have hTLower : Tlower ≤ T := (le_max_left _ _).trans hT
  have hRest₁ := (le_max_right Tlower _).trans hT
  have hTNear : Tnear ≤ T := (le_max_left _ _).trans hRest₁
  have hRest₂ := (le_max_right Tnear _).trans hRest₁
  have hTRef : Tref ≤ T := (le_max_left _ _).trans hRest₂
  have hRest₃ := (le_max_right Tref _).trans hRest₂
  have hTTerminal : Tterminal ≤ T := (le_max_left _ _).trans hRest₃
  have hRest₄ := (le_max_right Tterminal _).trans hRest₃
  have hTMargin : Tmargin ≤ T := (le_max_left _ _).trans hRest₄
  have hRest₅ := (le_max_right Tmargin _).trans hRest₄
  have hTDisp : Tdisp ≤ T := (le_max_left _ _).trans hRest₅
  have hRest₆ := (le_max_right Tdisp _).trans hRest₅
  have hTScale : Tscale ≤ T := (le_max_left _ _).trans hRest₆
  have hRest₇ := (le_max_right Tscale _).trans hRest₆
  have hTAdd : Tadd ≤ T := (le_max_left _ _).trans hRest₇
  have hRest₈ := (le_max_right Tadd _).trans hRest₇
  have hTTwo : Ttwo ≤ T := (le_max_left _ _).trans hRest₈
  have hRest₉ := (le_max_right Ttwo _).trans hRest₈
  have hTEight : 8 ≤ T := (le_max_left _ _).trans hRest₉
  have hTYAt : TY ≤ T := (le_max_right _ _).trans hRest₉
  have hTOne : 1 ≤ T := by linarith
  have hTPos : 0 < T := by linarith
  let Y : ℕ := ⌊T ^ (d ^ 2)⌋₊
  let A : ℕ := ⌊sharpZetaCutoff T⌋₊
  let Q : ℕ := 2 ^ r * Y
  let τ : ℝ := typeILogarithmicScale T Q
  have hDispAt : T ^ d ≤ T / 2 := hDisp T hTDisp
  have hScaleAt := hScale T r hTScale
  dsimp only at hScaleAt
  have hQOne : 1 < Q := by simpa only [Q, Y] using hScaleAt.1
  have hTauUpper : τ ≤ 2 / (d ^ 2) := by
    simpa only [τ, Q, Y] using hScaleAt.2
  have hY16 : 16 ≤ Y := by
    dsimp only [Y]
    apply Nat.le_floor
    exact hTY T hTYAt
  have hY : 0 < Y := by omega
  have hAOne : 1 < A := by
    dsimp only [A]
    apply lt_of_lt_of_le (by omega : 1 < (2 : ℕ))
    apply Nat.le_floor
    exact (show (2 : ℝ) ≤ 4 * T by nlinarith).trans
      (four_mul_lt_sharpZetaCutoff T).le
  have hBase : InBaseInterval (3 * T) W := by
    intro t ht
    have hAt := hRange t ht
    constructor <;> nlinarith
  have hPromote {C₁ : ℝ} (hC₁ : C₁ ≤ C)
      (hBound : (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
        C₁ * T ^ ε * T ^ (3 * (1 - σ) / τ₀)) :
      (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
        C * T ^ ε * T ^ (3 * (1 - σ) / τ₀) := by
    have hFirst : C₁ * T ^ ε ≤ C * T ^ ε :=
      mul_le_mul_of_nonneg_right hC₁ (Real.rpow_nonneg hTPos.le ε)
    exact hBound.trans (mul_le_mul_of_nonneg_right hFirst
      (Real.rpow_nonneg hTPos.le (3 * (1 - σ) / τ₀)))
  by_cases hrLower : r < 2
  · apply hPromote (le_max_left _ _)
    exact hLower T hTLower r hrLower W hW hSep hBase
      (by simpa only [Y, A, d] using hLarge)
      (by simpa only [Y, A, d] using hCount)
  · have hrTwo : 2 ≤ r := Nat.le_of_not_gt hrLower
    rcases typeISourceSmoothScale_lower_terminal_or_interior
        (Y := Y) (A := A) (r := r) hY with hImpossible | hTerminalOrInterior
    · exact (hrLower hImpossible).elim
    · rcases hTerminalOrInterior with hTerminalScale | hInterior
      · change A < 2 * (2 ^ r * Y) at hTerminalScale
        exact (hTerminal T Y A r W hTTerminal rfl hY hrTwo
          hTerminalScale hW hSep (by simpa only [Y, A, d] using hLarge)
          (by simpa only [d] using hRange) hDispAt).elim
      · change ((((Y + 1 : ℕ) : ℝ) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2)) ∧
          2 * (2 ^ r * Y) ≤ A) at hInterior
        rcases hInterior with ⟨hSourceLower, hSourceUpper⟩
        let t := hW.choose
        have ht : t ∈ W := hW.choose_spec
        have hMarginAt := hMargin T t τ Y A r hTMargin rfl hY hrTwo
          hSourceUpper (hRange t ht).1 (hRange t ht).2 hDispAt rfl
          (by simpa only [Y, A, d] using hLarge t ht)
        have hTauOne : 1 < τ := by
          have hdScaled : 100 * d ≤ (σ - 1 / 2) / 10 := by
            calc
              100 * d ≤ 100 * ((σ - 1 / 2) / 1000) := by gcongr
              _ = (σ - 1 / 2) / 10 := by ring
          nlinarith
        let V : ℝ := ((3 / 4 : ℝ) * (T ^ (-(d ^ 4)) / 2)) /
          (Nat.clog 2 A + 1 : ℕ)
        have hV : 0 < V := by dsimp only [V]; positivity
        obtain ⟨j, hj, W₀, hW₀sub, hSep₀, hCard₀, hLarge₀, hPUpper,
          hPLower⟩ := extract_normalized_source_dyadic_block W hY hAOne hV hW
            hSep (by simpa only [V, Y, A, d] using hLarge)
        let P : ℕ := 2 ^ j
        have hQ16 : 16 ≤ Q := by
          dsimp only [Q]
          exact hY16.trans (Nat.le_mul_of_pos_left Y (pow_pos (by omega) r))
        have hExtractUpper := extracted_source_logarithmic_scale_upper hTOne
          (div_pos (by norm_num) (sq_pos_of_pos hd)) hQ16
          (by simpa only [Q, P] using hPLower) hTauUpper
        have hPOne : 1 < P := hExtractUpper.1
        have hTauPUpper : typeILogarithmicScale T P ≤ 4 / (d ^ 2) := by
          calc
            typeILogarithmicScale T P ≤ 2 * (2 / (d ^ 2)) := hExtractUpper.2
            _ = 4 / (d ^ 2) := by ring
        have hTauPos : 0 < τ := zero_lt_one.trans hTauOne
        have hAddAt := hAdd hTAdd hQOne hPOne (by simpa only [Q, P] using hPUpper)
          rfl hTauPos hTauUpper
        by_cases hNearScale : 4 * τ₀ / 3 - s ≤ typeILogarithmicScale T P
        · apply hPromote ((le_max_left Cnear Cref).trans (le_max_right Clower _))
          exact hNear T hTNear W W₀ hY hAOne hW hSep hBase hW₀sub hSep₀
            (by simpa only [A] using hCard₀)
            (by simpa only [Y, A, Q, P, V, d] using hLarge₀)
            (by simpa only [Q, P] using hPUpper)
            (by simpa only [Q, P] using hPLower) hPOne hTauPUpper
            (by simpa only [s] using hNearScale)
            (by simpa only [Y, A, d] using hCount)
        · have hTauUpperEndpoint : τ < 4 * τ₀ / 3 := by
            have hFar : typeILogarithmicScale T P < 4 * τ₀ / 3 - s :=
              lt_of_not_ge hNearScale
            linarith
          by_cases hTauTwo : 2 ≤ τ
          · exact (hTwoImpossible W hTTwo rfl hY hrTwo hSourceUpper rfl hTauTwo
              hTauUpperEndpoint hDispAt hW (by simpa only [d] using hRange)
              (by simpa only [Y, A, d] using hLarge)).elim
          · apply hPromote ((le_max_right Cnear Cref).trans (le_max_right Clower _))
            exact hRef T hTRef W rfl hY hrTwo hSourceLower hSourceUpper rfl
              hTauOne (lt_of_not_ge hTauTwo) hW hSep
              (by simpa only [d] using hRange)
              (by simpa only [Y, A, d] using hLarge)
              (by simpa only [Y, A, d] using hCount)

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
          11 / 10 < typeILogarithmicScale T (2 ^ r * Y) →
          typeILogarithmicScale T (2 ^ r * Y) < 4 * τ₀ / 3 →
           (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
             C * T ^ ε * T ^ (3 * (1 - σ) / τ₀)

/-- Native implementation of the remaining medium Type-I interface.  It
starts from the actual long-tail component of the detector dichotomy, selects
one common smooth source scale, transfers the original multiplicity-weighted
count through the exact `Nat.clog` cover, and invokes the exhaustive source
consumer above. -/
theorem classical_medium_typeI_witness_consumer_native :
    ClassicalMediumTypeIWitnessConsumer := by
  intro σ τ₀ hσ hσUpper hcert ε hε
  obtain ⟨C, hC, T₀, hT₀, hSelected⟩ :=
    actual_selected_source_endpoint_consumer hσ hσUpper hcert ε hε
  refine ⟨C, hC, T₀, hT₀, ?_⟩
  intro T hT
  dsimp only
  intro r _hr W hSep _hLine hTail hRange hCount _hTauEndpoint _hTauLower
    _hTauUpper
  let d := classicalEndpointLossParameter σ τ₀ (ε / 100)
  let Y : ℕ := ⌊T ^ (d ^ 2)⌋₊
  let A : ℕ := ⌊sharpZetaCutoff T⌋₊
  have hTPos : 0 < T := by linarith [hT₀]
  by_cases hW : W.Nonempty
  · have hWpos : 0 < W.card := hW.card_pos
    obtain ⟨r₀, hr₀, W₀, hW₀sub, hSep₀, hCard₀, hLarge₀, _hClass⟩ :=
      actual_medium_long_tail_selects_classified_source
        (T := T) (d := d) (σ := σ)
        (V := (3 / 4) * (T ^ (-(d ^ 4)) / 2)) W (by linarith [hT₀])
        hW hSep (by simpa only [Y, A, d] using hTail)
    have hW₀ : W₀.Nonempty := by
      by_contra hnot
      have hzero : W₀.card = 0 := Finset.card_eq_zero.mpr
        (Finset.not_nonempty_iff_eq_empty.mp hnot)
      rw [hzero, mul_zero] at hCard₀
      omega
    have hRange₀ : ∀ t ∈ W₀, T - T ^ d ≤ t ∧ t ≤ 2 * T + T ^ d := by
      intro t ht
      exact hRange t (hW₀sub ht)
    let base : ℕ := 4 * Nat.clog 2 A *
      ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T)
    have hCount₀ : zeroCountRect σ 1 T (2 * T) ≤
        base * (Nat.clog 2 A + 1) * W₀.card := by
      calc
        zeroCountRect σ 1 T (2 * T) ≤ base * W.card := by
          simpa only [base, A, d] using hCount
        _ ≤ base * ((Nat.clog 2 A + 1) * W₀.card) :=
          Nat.mul_le_mul_left base hCard₀
        _ = base * (Nat.clog 2 A + 1) * W₀.card := by ring
    exact hSelected T hT r₀ W₀ hW₀ hSep₀
      (by simpa only [d] using hRange₀)
      (by simpa only [Y, A, d] using hLarge₀)
      (by simpa only [base, Y, A, d] using hCount₀)
  · have hWzero : W.card = 0 := Finset.card_eq_zero.mpr
      (Finset.not_nonempty_iff_eq_empty.mp hW)
    have hZeroCount : zeroCountRect σ 1 T (2 * T) = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa only [hWzero, mul_zero] using hCount
    rw [hZeroCount]
    norm_num only [Nat.cast_zero]
    exact mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hTPos.le ε))
      (Real.rpow_nonneg hTPos.le (3 * (1 - σ) / τ₀))

end RiemannZeta.GuthMaynard
