import Tao2026.BurgessWeilPrimeKummerAffineFiber

/-!
# Affine Kummer traces and multiplicative Fourier inversion

The affine point count from the preceding file is rewritten here as a trace
identity.  For `d = orderOf χ`, the curve `y^d = P(x)` has affine point
count

`p + ∑_{j=1}^{d-1} ∑_x χ^j(P(x))`.

Applying the same identity to every scalar twist `y^d = c P(x)` and taking
the `χ⁻¹` Fourier coefficient recovers the individual `χ`-sum exactly.  This
is the algebraic bridge from projective point-count estimates for all twists
to the sharp complete character-sum estimate.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

/-- The trivial-character correlation plus the number of polynomial zeros
is exactly the cardinality of the prime field. -/
theorem primePolynomialCharacterCorrelation_one_add_zeroFiber
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (P : Polynomial (ZMod p)) :
    primePolynomialCharacterCorrelation p (1 : MulChar (ZMod p) ℂ) P +
        (primePolynomialZeroFiber p P).card = (p : ℂ) := by
  classical
  have hcorr :
      primePolynomialCharacterCorrelation p (1 : MulChar (ZMod p) ℂ) P =
        ∑ x : ZMod p, if P.eval x = 0 then 0 else 1 := by
    unfold primePolynomialCharacterCorrelation
    apply Finset.sum_congr rfl
    intro x _hx
    by_cases hx : P.eval x = 0
    · rw [if_pos hx, hx, MulChar.map_zero]
    · rw [if_neg hx]
      exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)
  rw [hcorr]
  have hnonzero :
      (∑ x : ZMod p, if P.eval x = 0 then (0 : ℂ) else 1) =
        (((Finset.univ : Finset (ZMod p)).filter
          (fun x => ¬P.eval x = 0)).card : ℂ) := by
    calc
      (∑ x : ZMod p, if P.eval x = 0 then (0 : ℂ) else 1) =
          ∑ x : ZMod p, if ¬P.eval x = 0 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro x _hx
        by_cases hx : P.eval x = 0 <;> simp [hx]
      _ = (((Finset.univ : Finset (ZMod p)).filter
          (fun x => ¬P.eval x = 0)).card : ℂ) :=
        Finset.sum_boole (fun x : ZMod p => ¬P.eval x = 0) Finset.univ
  rw [hnonzero]
  have hcard := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (ZMod p))) (fun x => P.eval x = 0)
  have hcard' :
      ((Finset.univ.filter (fun x : ZMod p => ¬P.eval x = 0)).card +
        (primePolynomialZeroFiber p P).card) = p := by
    rw [primePolynomialZeroFiber]
    simpa [add_comm, ZMod.card] using hcard
  exact_mod_cast hcard'

/-- The proper positive powers of `χ`, excluding the terminal trivial
power. -/
def primeKummerProperTraceSum
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) : ℂ :=
  ∑ k ∈ Finset.range (orderOf χ - 1),
    primePolynomialCharacterCorrelation p (χ ^ (k + 1)) P

/-- Exact affine trace formula for the untwisted Kummer cover. -/
theorem card_primeKummerAffineCurvePoints_cast_eq_prime_add_properTrace
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) :
    ((primeKummerAffineCurvePoints p χ P).card : ℂ) =
      (p : ℂ) + primeKummerProperTraceSum p χ P := by
  classical
  have haff := card_primeKummerAffineCurvePoints p χ P
  have hpowers :=
    sum_range_primePolynomialCharacterCorrelation_pow_succ_eq_kernelFiber
      p χ P
  have hsplit :
      (∑ k ∈ Finset.range (orderOf χ),
          primePolynomialCharacterCorrelation p (χ ^ (k + 1)) P) =
        primeKummerProperTraceSum p χ P +
          primePolynomialCharacterCorrelation p
            (1 : MulChar (ZMod p) ℂ) P := by
    unfold primeKummerProperTraceSum
    conv_lhs =>
      rw [← Nat.sub_add_cancel χ.orderOf_pos]
    rw [Finset.sum_range_succ, Nat.sub_add_cancel χ.orderOf_pos,
      pow_orderOf_eq_one]
  have haffCast :
      ((primeKummerAffineCurvePoints p χ P).card : ℂ) =
        ((primePolynomialZeroFiber p P).card : ℂ) +
          (orderOf χ : ℂ) * (primeKummerKernelFiber p χ P).card := by
    exact_mod_cast haff
  rw [← hpowers, hsplit] at haffCast
  calc
    ((primeKummerAffineCurvePoints p χ P).card : ℂ) =
        ((primePolynomialZeroFiber p P).card : ℂ) +
          (primeKummerProperTraceSum p χ P +
            primePolynomialCharacterCorrelation p
              (1 : MulChar (ZMod p) ℂ) P) := haffCast
    _ = primeKummerProperTraceSum p χ P +
          (primePolynomialCharacterCorrelation p
            (1 : MulChar (ZMod p) ℂ) P +
              (primePolynomialZeroFiber p P).card) := by ring
    _ = primeKummerProperTraceSum p χ P + p := by
      rw [primePolynomialCharacterCorrelation_one_add_zeroFiber]
    _ = (p : ℂ) + primeKummerProperTraceSum p χ P := by ring

/-- Pulling a constant scalar out of a polynomial pulls its character value
out of the complete correlation. -/
theorem primePolynomialCharacterCorrelation_C_mul
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (ψ : MulChar (ZMod p) ℂ) (c : ZMod p)
    (P : Polynomial (ZMod p)) :
    primePolynomialCharacterCorrelation p ψ (Polynomial.C c * P) =
      ψ c * primePolynomialCharacterCorrelation p ψ P := by
  classical
  unfold primePolynomialCharacterCorrelation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  simp only [Polynomial.eval_mul, Polynomial.eval_C, map_mul]

/-- The scalar-twisted affine Kummer cover. -/
def primeKummerTwistedAffineCurvePoints
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (c : ZMod p) : Finset (ZMod p × ZMod p) :=
  primeKummerAffineCurvePoints p χ (Polynomial.C c * P)

/-- Exact trace formula for every scalar twist of the affine Kummer cover. -/
theorem card_primeKummerTwistedAffineCurvePoints_cast
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (c : ZMod p) :
    ((primeKummerTwistedAffineCurvePoints p χ P c).card : ℂ) =
      (p : ℂ) +
        ∑ k ∈ Finset.range (orderOf χ - 1),
          (χ ^ (k + 1)) c *
            primePolynomialCharacterCorrelation p (χ ^ (k + 1)) P := by
  classical
  rw [primeKummerTwistedAffineCurvePoints,
    card_primeKummerAffineCurvePoints_cast_eq_prime_add_properTrace]
  unfold primeKummerProperTraceSum
  apply congrArg ((p : ℂ) + ·)
  apply Finset.sum_congr rfl
  intro k _hk
  rw [primePolynomialCharacterCorrelation_C_mul]

/-- The deviation of a twisted affine point count from the prime-field
cardinality. -/
def primeKummerAffineTraceDefect
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (c : ZMod p) : ℂ :=
  ((primeKummerTwistedAffineCurvePoints p χ P c).card : ℂ) - p

/-- The trace defect is the proper character-power trace of the twist. -/
theorem primeKummerAffineTraceDefect_eq_sum
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (c : ZMod p) :
    primeKummerAffineTraceDefect p χ P c =
      ∑ k ∈ Finset.range (orderOf χ - 1),
        (χ ^ (k + 1)) c *
          primePolynomialCharacterCorrelation p (χ ^ (k + 1)) P := by
  rw [primeKummerAffineTraceDefect,
    card_primeKummerTwistedAffineCurvePoints_cast]
  ring

/-- Orthogonality of the Fourier weight `χ⁻¹` against a proper positive
power of `χ`. -/
theorem sum_mulChar_inv_mul_pow_succ
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (k : ℕ) (hk : k < orderOf χ) :
    (∑ c : ZMod p, χ⁻¹ c * (χ ^ (k + 1)) c) =
      if k = 0 then (p - 1 : ℕ) else 0 := by
  classical
  have hchar : χ⁻¹ * χ ^ (k + 1) = χ ^ k := by
    rw [pow_succ']
    group
  calc
    (∑ c : ZMod p, χ⁻¹ c * (χ ^ (k + 1)) c) =
        ∑ c : ZMod p, (χ⁻¹ * χ ^ (k + 1)) c := by rfl
    _ = ∑ c : ZMod p, (χ ^ k) c := by rw [hchar]
    _ = if k = 0 then (p - 1 : ℕ) else 0 := by
      by_cases hk0 : k = 0
      · subst k
        simp [MulChar.sum_one_eq_card_units, Fintype.card_units, ZMod.card]
      · rw [if_neg hk0,
          MulChar.sum_eq_zero_of_ne_one (pow_ne_one_of_lt_orderOf hk0 hk)]
        norm_num

/-- Multiplicative Fourier inversion: the `χ⁻¹` coefficient of the family of
twisted affine point-count defects is exactly `(p-1)` times the individual
complete `χ`-sum. -/
theorem sum_mulChar_inv_mul_primeKummerAffineTraceDefect
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hχ : χ ≠ 1) :
    (∑ c : ZMod p, χ⁻¹ c * primeKummerAffineTraceDefect p χ P c) =
      (p - 1 : ℕ) * primePolynomialCharacterCorrelation p χ P := by
  classical
  have hd : 0 < orderOf χ - 1 := by
    have := mulChar_orderOf_two_le_of_ne_one χ hχ
    omega
  simp_rw [primeKummerAffineTraceDefect_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ x ∈ Finset.range (orderOf χ - 1),
        ∑ i : ZMod p,
          χ⁻¹ i *
              ((χ ^ (x + 1)) i *
                primePolynomialCharacterCorrelation p (χ ^ (x + 1)) P)) =
        ∑ x ∈ Finset.range (orderOf χ - 1),
          (∑ i : ZMod p, χ⁻¹ i * (χ ^ (x + 1)) i) *
            primePolynomialCharacterCorrelation p (χ ^ (x + 1)) P := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c _hc
      ring
    _ = ∑ x ∈ Finset.range (orderOf χ - 1),
          (if x = 0 then (p - 1 : ℕ) else 0) *
            primePolynomialCharacterCorrelation p (χ ^ (x + 1)) P := by
      apply Finset.sum_congr rfl
      intro k hk
      have hklt : k < orderOf χ := by
        have := Finset.mem_range.mp hk
        omega
      rw [sum_mulChar_inv_mul_pow_succ p χ k hklt]
    _ = (p - 1 : ℕ) * primePolynomialCharacterCorrelation p χ P := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro k hk hk0
        simp [hk0]
      · intro hnot
        exact (hnot (Finset.mem_range.mpr hd)).elim

/-- Source-facing point-count formulation of the remaining Kummer input:
every nonzero scalar twist has the sharp affine trace-defect bound. -/
def TaoPrimeKummerAffineTwistWeilBound : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)),
    χ ≠ 1 → P.Splits → ¬IsMulCharOrderScalarPower χ P →
    ∀ c : ZMod p, c ≠ 0 →
      ‖primeKummerAffineTraceDefect p χ P c‖ ≤
        ((P.roots.toFinset.card - 1 : ℕ) : ℝ) * Real.sqrt p

/-- Multiplicative Fourier inversion transfers the uniform sharp point-count
bound for all scalar twists to the individual complete character sum. -/
theorem TaoPrimeKummerAffineTwistWeilBound.toPolynomial
    (hweil : TaoPrimeKummerAffineTwistWeilBound) :
    TaoPrimeKummerPolynomialWeilBound := by
  intro p _ _ χ P hχ hP hpower
  let B : ℝ :=
    ((P.roots.toFinset.card - 1 : ℕ) : ℝ) * Real.sqrt p
  have hB : 0 ≤ B := mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  have hp : p.Prime := Fact.out
  have hp1Nat : 0 < p - 1 := by
    have := hp.two_le
    omega
  have hp1 : 0 < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast hp1Nat
  have hfourier :=
    sum_mulChar_inv_mul_primeKummerAffineTraceDefect p χ P hχ
  have hterm : ∀ c : ZMod p,
      ‖χ⁻¹ c * primeKummerAffineTraceDefect p χ P c‖ ≤
        if c = 0 then 0 else B := by
    intro c
    by_cases hc : c = 0
    · subst c
      simp [MulChar.map_zero]
    · rw [if_neg hc, norm_mul]
      have hroot := (χ⁻¹).apply_mem_rootsOfUnity (Units.mk0 c hc)
      have hnorm : ‖χ⁻¹ c‖ = 1 := by
        simpa using Complex.norm_eq_one_of_mem_rootsOfUnity hroot
      rw [hnorm, one_mul]
      exact hweil p χ P hχ hP hpower c hc
  have hsumIf :
      (∑ c : ZMod p, if c = 0 then (0 : ℝ) else B) =
        ((p - 1 : ℕ) : ℝ) * B := by
    calc
      (∑ c : ZMod p, if c = 0 then (0 : ℝ) else B) =
          ∑ c : ZMod p, B * if c ≠ 0 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro c _hc
        by_cases hc : c = 0 <;> simp [hc]
      _ = B * ∑ c : ZMod p, if c ≠ 0 then 1 else 0 := by
        rw [Finset.mul_sum]
      _ = B *
          (((Finset.univ : Finset (ZMod p)).filter (fun c => c ≠ 0)).card : ℝ) := by
        rw [Finset.sum_boole]
      _ = B * (p - 1 : ℕ) := by
        congr 1
        norm_cast
        rw [← Fintype.card_subtype,
          ← Fintype.card_congr unitsEquivNeZero,
          Fintype.card_units, ZMod.card]
      _ = ((p - 1 : ℕ) : ℝ) * B := by ring
  have hscaled :
      ((p - 1 : ℕ) : ℝ) *
          ‖primePolynomialCharacterCorrelation p χ P‖ ≤
        ((p - 1 : ℕ) : ℝ) * B := by
    calc
      ((p - 1 : ℕ) : ℝ) *
          ‖primePolynomialCharacterCorrelation p χ P‖ =
          ‖((p - 1 : ℕ) : ℂ) *
            primePolynomialCharacterCorrelation p χ P‖ := by
        rw [norm_mul, Complex.norm_natCast]
      _ = ‖∑ c : ZMod p,
          χ⁻¹ c * primeKummerAffineTraceDefect p χ P c‖ := by
        rw [hfourier]
      _ ≤ ∑ c : ZMod p,
          ‖χ⁻¹ c * primeKummerAffineTraceDefect p χ P c‖ :=
        norm_sum_le _ _
      _ ≤ ∑ c : ZMod p, if c = 0 then 0 else B :=
        Finset.sum_le_sum fun c _hc => hterm c
      _ = ((p - 1 : ℕ) : ℝ) * B := hsumIf
  nlinarith

end

end Tao2026
