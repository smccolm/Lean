import GafniTao.WooleySection8Ratio
import GafniTao.WooleySection9Product

/-!
# Source specialization of Wooley Lemma 9.1

The results here connect the abstract multigrade product induction to the
literal normalized mixed means.  The common constant from Lemma 7.1 remains
visible, as do the Section-6 conditioned-mean estimate and every scale
hypothesis needed by (8.4)--(8.5).
-/

namespace GafniTao

noncomputable section

/-- A Section-7 multiplier raised to the normalization exponent is bounded
by the multiplier itself. -/
theorem wooley_section7_multiplier_rpow_le
    {k r : ℕ} {D : ℝ} (hr : 1 ≤ r) (hrk : r < k) (hD : 1 ≤ D) :
    D ^ wooleyNormalizationExponent k r ≤ D := by
  exact Real.rpow_le_self_of_one_le hD
    (wooleyNormalizationExponent_le_one hr hrk)

/-- The exact coefficient algebra in the base case of Lemma 9.1. -/
theorem wooley_section9_base_coefficient
    {p k s b nu : ℕ} {C Lambda X : ℝ}
    (hp : 2 ≤ p) (hk : 2 ≤ k) (hC : 1 ≤ C)
    (hs : s ≤ k ^ 2) (hX : 0 ≤ X) :
    (C * (p : ℝ) ^ (((k ^ 2 * nu : ℕ) : ℝ))) *
        X ^ (1 / (k : ℝ)) *
        ((p : ℝ) ^ ((s : ℝ) * (nu : ℝ) - Lambda * (b : ℝ))) ^
          (1 - 1 / (k : ℝ)) ≤
      (C * (p : ℝ) ^ (((k ^ 2 * nu : ℕ) : ℝ))) ^ (2 : ℝ) *
        (p : ℝ) ^ (-(b : ℝ) * (1 - 1 / (k : ℝ)) * Lambda) *
        X ^ wooleyRho k 1 := by
  let A : ℝ := C * (p : ℝ) ^ (((k ^ 2 * nu : ℕ) : ℝ))
  let v : ℝ := 1 - 1 / (k : ℝ)
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hkR : (0 : ℝ) < k := by positivity
  have hv : 0 ≤ v := by
    dsimp [v]
    rw [sub_nonneg, div_le_one hkR]
    exact_mod_cast (show 1 ≤ k by omega)
  have hsR : (s : ℝ) ≤ (k : ℝ) ^ 2 := by
    exact_mod_cast hs
  have hnuR : (0 : ℝ) ≤ nu := Nat.cast_nonneg _
  have hexp :
      ((s : ℝ) * (nu : ℝ) - Lambda * (b : ℝ)) * v ≤
        (((k ^ 2 * nu : ℕ) : ℝ)) -
          (b : ℝ) * v * Lambda := by
    have hsn : (s : ℝ) * (nu : ℝ) ≤ (k : ℝ) ^ 2 * (nu : ℝ) :=
      mul_le_mul_of_nonneg_right hsR hnuR
    calc
      ((s : ℝ) * (nu : ℝ) - Lambda * (b : ℝ)) * v =
          ((s : ℝ) * (nu : ℝ)) * v - (b : ℝ) * v * Lambda := by ring
      _ ≤ (((k : ℝ) ^ 2) * (nu : ℝ)) * v - (b : ℝ) * v * Lambda := by
        exact sub_le_sub_right (mul_le_mul_of_nonneg_right hsn hv) _
      _ ≤ ((k : ℝ) ^ 2) * (nu : ℝ) - (b : ℝ) * v * Lambda := by
        apply sub_le_sub_right
        exact mul_le_of_le_one_right (mul_nonneg (sq_nonneg _) hnuR) (by
          dsimp [v]
          linarith [one_div_nonneg.mpr hkR.le])
      _ = (((k ^ 2 * nu : ℕ) : ℝ)) - (b : ℝ) * v * Lambda := by
        norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hpow :
      ((p : ℝ) ^ ((s : ℝ) * (nu : ℝ) - Lambda * (b : ℝ))) ^ v ≤
        (p : ℝ) ^ ((((k ^ 2 * nu : ℕ) : ℝ)) -
          (b : ℝ) * v * Lambda) := by
    rw [← Real.rpow_mul hpR.le]
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ p by omega)) hexp
  have hA : (p : ℝ) ^ (((k ^ 2 * nu : ℕ) : ℝ)) ≤ A := by
    dsimp [A]
    calc
      (p : ℝ) ^ (((k ^ 2 * nu : ℕ) : ℝ)) =
          1 * (p : ℝ) ^ (((k ^ 2 * nu : ℕ) : ℝ)) := by ring
      _ ≤ C * (p : ℝ) ^ (((k ^ 2 * nu : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hpR.le _)
  have hA0 : 0 ≤ A := by positivity
  have hXpow : 0 ≤ X ^ (1 / (k : ℝ)) := Real.rpow_nonneg hX _
  have htail : 0 ≤ (p : ℝ) ^ (-(b : ℝ) * v * Lambda) :=
    Real.rpow_nonneg hpR.le _
  have hsplit :
      (p : ℝ) ^ ((((k ^ 2 * nu : ℕ) : ℝ)) -
          (b : ℝ) * v * Lambda) =
        (p : ℝ) ^ (((k ^ 2 * nu : ℕ) : ℝ)) *
          (p : ℝ) ^ (-(b : ℝ) * v * Lambda) := by
    rw [show (((k ^ 2 * nu : ℕ) : ℝ)) - (b : ℝ) * v * Lambda =
      (((k ^ 2 * nu : ℕ) : ℝ)) + (-(b : ℝ) * v * Lambda) by ring,
      Real.rpow_add hpR]
  have hcoef :
      A * (p : ℝ) ^ ((((k ^ 2 * nu : ℕ) : ℝ)) -
          (b : ℝ) * v * Lambda) ≤
        A ^ (2 : ℝ) * (p : ℝ) ^ (-(b : ℝ) * v * Lambda) := by
    rw [hsplit, Real.rpow_two]
    calc
      A * ((p : ℝ) ^ (((k ^ 2 * nu : ℕ) : ℝ)) *
          (p : ℝ) ^ (-(b : ℝ) * v * Lambda)) =
          (A * (p : ℝ) ^ (((k ^ 2 * nu : ℕ) : ℝ))) *
            (p : ℝ) ^ (-(b : ℝ) * v * Lambda) := by ring
      _ ≤ (A * A) * (p : ℝ) ^ (-(b : ℝ) * v * Lambda) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hA hA0) htail
      _ = A ^ 2 * (p : ℝ) ^ (-(b : ℝ) * v * Lambda) := by ring
  have hmain := mul_le_mul_of_nonneg_left hpow
    (mul_nonneg hA0 hXpow)
  rw [show wooleyRho k 1 = 1 / (k : ℝ) by
        exact wooleyRho_one (by omega),
    show C * (p : ℝ) ^ (((k ^ 2 * nu : ℕ) : ℝ)) = A by rfl,
    show 1 - 1 / (k : ℝ) = v by rfl]
  calc
    A * X ^ (1 / (k : ℝ)) *
        ((p : ℝ) ^ ((s : ℝ) * (nu : ℝ) - Lambda * (b : ℝ))) ^ v ≤
      A * X ^ (1 / (k : ℝ)) *
        (p : ℝ) ^ ((((k ^ 2 * nu : ℕ) : ℝ)) -
          (b : ℝ) * v * Lambda) := hmain
    _ = (A * (p : ℝ) ^ ((((k ^ 2 * nu : ℕ) : ℝ)) -
          (b : ℝ) * v * Lambda)) * X ^ (1 / (k : ℝ)) := by ring
    _ ≤ (A ^ (2 : ℝ) * (p : ℝ) ^ (-(b : ℝ) * v * Lambda)) *
        X ^ (1 / (k : ℝ)) :=
      mul_le_mul_of_nonneg_right hcoef hXpow
    _ = A ^ (2 : ℝ) * (p : ℝ) ^ (-(b : ℝ) * v * Lambda) *
        X ^ (1 / (k : ℝ)) := by ring

/-- The exponent on the complementary-grade mean in (8.4) is exactly the
multigrade weight `rho_r/r`. -/
theorem wooley_section8_exponent_eq_rho_div
    {k r : ℕ} (hr : 1 ≤ r) :
    1 / ((k - r + 1 : ℕ) : ℝ) = wooleyRho k r / (r : ℝ) := by
  unfold wooleyRho
  have hrR : (r : ℝ) ≠ 0 := by positivity
  field_simp

/-- The first successor scale in Section 9 is literally `k*b`. -/
theorem wooleyNextB_one {k : ℕ} (hk : 1 ≤ k) (b : ℕ) :
    wooleyNextB k 1 b = k * b := by
  rw [wooleyNextB, show k - 1 + 1 = k by omega]
  simp

/-- Wooley Lemma 9.1 with the source normalized mixed means and all constants
visible.  The hypotheses are precisely the uniform Lemma-7.1 estimates and
the source-(6.4) estimate needed by the `r=1` branch; later consumers derive
these hypotheses from the hierarchy before invoking this theorem. -/
theorem wooleySourcePolynomial_lemma_9_1_of_section7
    {k p B H b nu : ℕ} [NeZero p] [NeZero (p ^ B)]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    (Valid : ℕ → ℕ → Prop)
    (C Lambda epsilon : ℝ)
    (hp : 2 ≤ p) (hk : 2 ≤ k) (hC : 1 ≤ C)
    (hnuNext : ∀ r, 1 ≤ r → r < k → nu ≤ wooleyNextB k r b)
    (hnub : nu ≤ b) (hnukb : nu ≤ k * b) (hbH : b ≤ H)
    (hscale : 0 < wooleySourceNormalizationScale
      phi p B H (wooleyTriangular k) Lambda gamma)
    (hsection7 : ∀ r a, 1 ≤ r → r < k → Valid r a →
      wooleySourcePolynomialMixedMean
          phi (wooleyTriangular k) r p B a b nu gamma ≤
        (C * (p : ℝ) ^ (((k ^ 2 * nu : ℕ) : ℝ))) *
          wooleySourcePolynomialMixedMean
            phi (wooleyTriangular k) r p B
            (wooleyNextB k r b) b nu gamma)
    (hvalidPred : ∀ {r a : ℕ}, 2 ≤ r → r < k → Valid r a →
      Valid (r - 1) (wooleyNextB k r b))
    (hupper :
      wooleySourcePolynomialConditionedMean
          (wooleyTriangular k) (p ^ B) (p ^ b) phi gamma ≤
        (p : ℝ) ^ (((H - b : ℕ) : ℝ) * (Lambda + epsilon)) *
          wooleySourcePolynomialConditionedMean
            (wooleyTriangular k) (p ^ B) (p ^ H) phi gamma)
    (hloss : epsilon * ((H - b : ℕ) : ℝ) ≤
      (wooleyTriangular k : ℝ) * (nu : ℝ)) :
    ∀ {r a : ℕ}, 1 ≤ r → r < k → Valid r a →
      wooleySourceNormalizedMixedMean
          phi p B H (wooleyTriangular k) r a b nu Lambda gamma ≤
        (C * (p : ℝ) ^ (((k ^ 2 * nu : ℕ) : ℝ))) ^
            ((r + 1 : ℕ) : ℝ) *
          (p : ℝ) ^
            (-((b : ℝ) * (1 - 1 / (k : ℝ)) * Lambda) / (r : ℝ)) *
          wooleyMonogradeProduct k r (fun j =>
            wooleySourceNormalizedMixedMean
              phi p B H (wooleyTriangular k) (k - j) b
                (wooleyNextB k j b) nu Lambda gamma) := by
  let D : ℝ := C * (p : ℝ) ^ (((k ^ 2 * nu : ℕ) : ℝ))
  let X : ℕ → ℝ := fun j =>
    wooleySourceNormalizedMixedMean
      phi p B H (wooleyTriangular k) (k - j) b
        (wooleyNextB k j b) nu Lambda gamma
  let K : ℕ → ℕ → ℝ := fun r a =>
    wooleySourceNormalizedMixedMean
      phi p B H (wooleyTriangular k) r a b nu Lambda gamma
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hDOne : 1 ≤ D := by
    dsimp [D]
    have hC0 : 0 ≤ C := by linarith
    have hpPow : 1 ≤ (p : ℝ) ^ (((k ^ 2 * nu : ℕ) : ℝ)) :=
      Real.one_le_rpow (by exact_mod_cast (show 1 ≤ p by omega))
        (Nat.cast_nonneg _)
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ C * (p : ℝ) ^ (((k ^ 2 * nu : ℕ) : ℝ)) :=
        mul_le_mul hC hpPow (by norm_num) hC0
  have hX : ∀ j, 1 ≤ j → j < k → 0 ≤ X j := by
    intro j hj hjk
    exact wooleySourceNormalizedMixedMean_nonneg
      phi p B H (wooleyTriangular k) (k - j) b
        (wooleyNextB k j b) nu Lambda gamma
  have hK : ∀ r a, 0 ≤ K r a := by
    intro r a
    exact wooleySourceNormalizedMixedMean_nonneg
      phi p B H (wooleyTriangular k) r a b nu Lambda gamma
  have hbase : ∀ a, Valid 1 a →
      K 1 a ≤ D ^ (2 : ℝ) *
        (p : ℝ) ^ (-((b : ℝ) * (1 - 1 / (k : ℝ)) * Lambda)) *
        (X 1) ^ wooleyRho k 1 := by
    intro a hvalid
    have hsec := hsection7 1 a (by omega) (by omega) hvalid
    rw [wooleyNextB_one (by omega) b] at hsec
    have h85 := wooleySourcePolynomial_equation_8_5
      phi p B H a b nu Lambda epsilon D hk hp hbH hnub hnukb gamma
        hscale (hDOne.trans' (by norm_num)) hsec hupper hloss
    rw [← wooleyNextB_one (by omega) b] at h85
    have htri : wooleyTriangular k ≤ k ^ 2 := by
      exact_mod_cast (show (wooleyTriangular k : ℝ) ≤ (k : ℝ) ^ 2 by
        rw [wooleyTriangular_cast]
        have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
        nlinarith)
    have hcoef := wooley_section9_base_coefficient
      (p := p) (k := k) (s := wooleyTriangular k) (b := b) (nu := nu)
      (C := C) (Lambda := Lambda) (X := X 1)
      hp hk hC htri (hX 1 (by omega) (by omega))
    have hcombined := h85.trans hcoef
    change wooleySourceNormalizedMixedMean
        phi p B H (wooleyTriangular k) 1 a b nu Lambda gamma ≤
      D ^ (2 : ℝ) *
        (p : ℝ) ^ (-((b : ℝ) * (1 - 1 / (k : ℝ)) * Lambda)) *
        (X 1) ^ wooleyRho k 1
    simpa only [D, neg_mul] using hcombined
  have hstep : ∀ {r a : ℕ}, 2 ≤ r → r < k →
      Valid r a →
      K r a ≤ D * (X r) ^ (wooleyRho k r / (r : ℝ)) *
        (K (r - 1) (wooleyNextB k r b)) ^
          (1 - 1 / (r : ℝ)) := by
    intro r a hr hrk hvalid
    have hsec := hsection7 r a (by omega) hrk hvalid
    have h84 := wooleySourcePolynomial_equation_8_4
      phi p B H r a b (wooleyNextB k r b) nu Lambda D hr hrk
        hnub (hnuNext r (by omega) hrk) gamma hscale
        (hDOne.trans' (by norm_num)) hsec
    have hpowD : D ^ wooleyNormalizationExponent k r ≤ D :=
      wooley_section7_multiplier_rpow_le (by omega) hrk hDOne
    have hXnonneg : 0 ≤ (X r) ^ (1 / ((k - r + 1 : ℕ) : ℝ)) := by
      exact Real.rpow_nonneg (hX r (by omega) hrk) _
    have hKnonneg : 0 ≤
        (K (r - 1) (wooleyNextB k r b)) ^
          (1 - 1 / (r : ℝ)) := by
      exact Real.rpow_nonneg (hK (r - 1) (wooleyNextB k r b)) _
    calc
      K r a ≤ D ^ wooleyNormalizationExponent k r *
          (X r) ^ (1 / ((k - r + 1 : ℕ) : ℝ)) *
          (K (r - 1) (wooleyNextB k r b)) ^
            (1 - 1 / (r : ℝ)) := by
        simpa only [D, X, K] using h84
      _ ≤ D * (X r) ^ (1 / ((k - r + 1 : ℕ) : ℝ)) *
          (K (r - 1) (wooleyNextB k r b)) ^
            (1 - 1 / (r : ℝ)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hpowD hXnonneg) hKnonneg
      _ = D * (X r) ^ (wooleyRho k r / (r : ℝ)) *
          (K (r - 1) (wooleyNextB k r b)) ^
            (1 - 1 / (r : ℝ)) := by
        rw [wooley_section8_exponent_eq_rho_div (by omega)]
  intro r a hr hrk hvalid
  simpa only [D, X, K] using
    (wooley_multigrade_to_monograde X K Valid hDOne hpR hX hK hbase hstep
      hvalidPred (r := r) (a := a) hr hrk hvalid)

/-- Exact constant-and-`p` loss absorption used after the finite grade
selection in Lemma 9.2.  Unlike Vinogradov notation, the surviving uniform
constant is displayed. -/
theorem wooley_section9_constant_loss_absorption
    {p k r b nu : ℕ} {C Lambda : ℝ}
    (hp : 2 ≤ p) (hk : 2 ≤ k) (hr : 1 ≤ r) (hrk : r ≤ k - 1)
    (hC : 1 ≤ C) (hLambda : 0 ≤ Lambda)
    (hhierarchy :
      2 * (((r + 1) * k ^ 2 * nu : ℕ) : ℝ) ≤
        (b : ℝ) * Lambda / (k : ℝ)) :
    (C * (p : ℝ) ^ (((k ^ 2 * nu : ℕ) : ℝ))) ^ ((r + 1 : ℕ) : ℝ) *
        (p : ℝ) ^
          (-((b : ℝ) * (1 - 1 / (k : ℝ)) * Lambda) / (r : ℝ)) ≤
      C ^ ((r + 1 : ℕ) : ℝ) *
        (p : ℝ) ^ (-(b : ℝ) * Lambda / (2 * (k : ℝ))) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hC0 : 0 ≤ C := by linarith
  have hpPow0 : 0 ≤ (p : ℝ) ^ (((k ^ 2 * nu : ℕ) : ℝ)) :=
    Real.rpow_nonneg hpR.le _
  rw [Real.mul_rpow hC0 hpPow0]
  have hpexp :
      ((p : ℝ) ^ (((k ^ 2 * nu : ℕ) : ℝ))) ^ ((r + 1 : ℕ) : ℝ) =
        (p : ℝ) ^ ((((r + 1) * k ^ 2 * nu : ℕ) : ℝ)) := by
    rw [← Real.rpow_mul hpR.le]
    apply congrArg (fun z : ℝ => (p : ℝ) ^ z)
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow,
      Nat.cast_ofNat]
    ring_nf
  rw [hpexp]
  have habs := wooley_section9_loss_absorption hp hk hr hrk hLambda hhierarchy
  have hCpow : 0 ≤ C ^ ((r + 1 : ℕ) : ℝ) := Real.rpow_nonneg hC0 _
  calc
    C ^ ((r + 1 : ℕ) : ℝ) *
          (p : ℝ) ^ ((((r + 1) * k ^ 2 * nu : ℕ) : ℝ)) *
          (p : ℝ) ^
            (-((b : ℝ) * (1 - 1 / (k : ℝ)) * Lambda) / (r : ℝ)) =
        C ^ ((r + 1 : ℕ) : ℝ) *
          ((p : ℝ) ^ ((((r + 1) * k ^ 2 * nu : ℕ) : ℝ)) *
            (p : ℝ) ^
              (-(b : ℝ) * ((1 - 1 / (k : ℝ)) * Lambda /
                (r : ℝ)))) := by ring_nf
    _ ≤ C ^ ((r + 1 : ℕ) : ℝ) *
          (p : ℝ) ^ (-(b : ℝ) * Lambda / (2 * (k : ℝ))) :=
      mul_le_mul_of_nonneg_left habs hCpow

/-- Wooley Lemma 9.2 as the exact finite consequence of Lemma 9.1.  It
selects an actual grade and records the constant suppressed by the paper's
Vinogradov notation. -/
theorem wooleySourcePolynomial_lemma_9_2_of_lemma_9_1
    {k p B H r a b nu : ℕ} [NeZero p] [NeZero (p ^ B)]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    (C Lambda : ℝ)
    (hp : 2 ≤ p) (hk : 2 ≤ k) (hr : 1 ≤ r) (hrk : r ≤ k - 1)
    (hC : 1 ≤ C) (hLambda : 0 ≤ Lambda)
    (hhierarchy :
      2 * (((r + 1) * k ^ 2 * nu : ℕ) : ℝ) ≤
        (b : ℝ) * Lambda / (k : ℝ))
    (h91 :
      wooleySourceNormalizedMixedMean
          phi p B H (wooleyTriangular k) r a b nu Lambda gamma ≤
        (C * (p : ℝ) ^ (((k ^ 2 * nu : ℕ) : ℝ))) ^
            ((r + 1 : ℕ) : ℝ) *
          (p : ℝ) ^
            (-((b : ℝ) * (1 - 1 / (k : ℝ)) * Lambda) / (r : ℝ)) *
          wooleyMonogradeProduct k r (fun j =>
            wooleySourceNormalizedMixedMean
              phi p B H (wooleyTriangular k) (k - j) b
                (wooleyNextB k j b) nu Lambda gamma)) :
    ∃ rPrime ∈ wooleyGradeRange r,
      wooleySourceNormalizedMixedMean
          phi p B H (wooleyTriangular k) r a b nu Lambda gamma ≤
        C ^ ((r + 1 : ℕ) : ℝ) *
          (wooleySourceNormalizedMixedMean
            phi p B H (wooleyTriangular k) (k - rPrime) b
              (wooleyNextB k rPrime b) nu Lambda gamma) ^
              wooleyRho k rPrime *
          (p : ℝ) ^ (-(b : ℝ) * Lambda / (2 * (k : ℝ))) := by
  let X : ℕ → ℝ := fun j =>
    wooleySourceNormalizedMixedMean
      phi p B H (wooleyTriangular k) (k - j) b
        (wooleyNextB k j b) nu Lambda gamma
  have hX : ∀ j ∈ wooleyGradeRange r, 0 ≤ X j := by
    intro j hj
    exact wooleySourceNormalizedMixedMean_nonneg
      phi p B H (wooleyTriangular k) (k - j) b
        (wooleyNextB k j b) nu Lambda gamma
  obtain ⟨rPrime, hrPrime, hselect⟩ :=
    exists_wooley_grade_for_weighted_product hr X hX
  refine ⟨rPrime, hrPrime, ?_⟩
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hcoef := wooley_section9_constant_loss_absorption
    hp hk hr hrk hC hLambda hhierarchy
  have htail : 0 ≤ (p : ℝ) ^ (-(b : ℝ) * Lambda / (2 * (k : ℝ))) :=
    Real.rpow_nonneg hpR.le _
  have hselected :
      (C * (p : ℝ) ^ (((k ^ 2 * nu : ℕ) : ℝ))) ^
            ((r + 1 : ℕ) : ℝ) *
          (p : ℝ) ^
            (-((b : ℝ) * (1 - 1 / (k : ℝ)) * Lambda) / (r : ℝ)) *
          wooleyMonogradeProduct k r X ≤
        C ^ ((r + 1 : ℕ) : ℝ) *
          (X rPrime) ^ wooleyRho k rPrime *
          (p : ℝ) ^ (-(b : ℝ) * Lambda / (2 * (k : ℝ))) := by
    have hprod0 : 0 ≤ wooleyMonogradeProduct k r X :=
      wooleyMonogradeProduct_nonneg hX
    have hlead0 : 0 ≤
        (C * (p : ℝ) ^ (((k ^ 2 * nu : ℕ) : ℝ))) ^
            ((r + 1 : ℕ) : ℝ) *
          (p : ℝ) ^
            (-((b : ℝ) * (1 - 1 / (k : ℝ)) * Lambda) / (r : ℝ)) := by
      positivity
    calc
      _ ≤ ((C * (p : ℝ) ^ (((k ^ 2 * nu : ℕ) : ℝ))) ^
              ((r + 1 : ℕ) : ℝ) *
            (p : ℝ) ^
              (-((b : ℝ) * (1 - 1 / (k : ℝ)) * Lambda) / (r : ℝ))) *
          (X rPrime) ^ wooleyRho k rPrime :=
        mul_le_mul_of_nonneg_left hselect hlead0
      _ ≤ (C ^ ((r + 1 : ℕ) : ℝ) *
            (p : ℝ) ^ (-(b : ℝ) * Lambda / (2 * (k : ℝ)))) *
          (X rPrime) ^ wooleyRho k rPrime := by
        exact mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (hX rPrime hrPrime) _)
      _ = C ^ ((r + 1 : ℕ) : ℝ) *
          (X rPrime) ^ wooleyRho k rPrime *
          (p : ℝ) ^ (-(b : ℝ) * Lambda / (2 * (k : ℝ))) := by ring_nf
  exact h91.trans (by simpa only [X] using hselected)

#print axioms wooley_section7_multiplier_rpow_le
#print axioms wooley_section9_base_coefficient
#print axioms wooley_section8_exponent_eq_rho_div
#print axioms wooleyNextB_one
#print axioms wooleySourcePolynomial_lemma_9_1_of_section7
#print axioms wooley_section9_constant_loss_absorption
#print axioms wooleySourcePolynomial_lemma_9_2_of_lemma_9_1

end

end GafniTao
