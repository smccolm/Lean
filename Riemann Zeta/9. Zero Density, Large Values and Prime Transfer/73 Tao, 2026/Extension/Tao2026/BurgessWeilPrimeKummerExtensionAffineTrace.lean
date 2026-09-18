import Tao2026.BurgessWeilPrimeKummerHasseDavenportMinimalPolynomialFibers

/-!
# Extension-field affine Kummer traces

The earlier affine Kummer point-count identity was stated over `ZMod p`.
This file proves the same identity over an arbitrary finite field and then
specializes it to every canonical extension occurring in
`primeKummerExtensionCorrelation`.

For a finite field `F`, a nontrivial multiplicative character `χ`, and a
polynomial `P`, multiplicative Fourier inversion on all scalar twists gives

`∑ c, χ⁻¹(c) (#{(x,y) | y^order(χ) = c P(x)} - #F)
    = (#F - 1) ∑ x, χ(P(x))`.

Thus every positive-degree trace in the genuine Frobenius-system contract is
literally the selected multiplicative Fourier coefficient of affine Kummer
curve point counts over that extension field.  No cancellation or geometric
input is used here.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

/-- Complete polynomial correlation over an arbitrary finite field. -/
def finiteFieldPolynomialCharacterCorrelation
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (P : Polynomial F) : ℂ :=
  ∑ x : F, χ (P.eval x)

/-- Inputs at which a finite-field polynomial vanishes. -/
def finiteFieldPolynomialZeroFiber
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (P : Polynomial F) : Finset F :=
  Finset.univ.filter fun x => P.eval x = 0

/-- Inputs whose nonzero polynomial value lies in the kernel of `χ`. -/
def finiteFieldKummerKernelFiber
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (P : Polynomial F) : Finset F :=
  Finset.univ.filter fun x => χ (P.eval x) = 1

/-- Affine points of the finite-field Kummer cover `y^order(χ) = P(x)`. -/
def finiteFieldKummerAffineCurvePoints
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (P : Polynomial F) : Finset (F × F) :=
  (Finset.univ ×ˢ Finset.univ).filter fun q =>
    q.2 ^ orderOf χ = P.eval q.1

/-- Counting an arbitrary finite-field affine Kummer cover by vertical
fibers. -/
theorem card_finiteFieldKummerAffineCurvePoints_eq_sum_fibers
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (P : Polynomial F) :
    (finiteFieldKummerAffineCurvePoints F χ P).card =
      ∑ x : F, (primeKummerPowerFiber F χ (P.eval x)).card := by
  classical
  rw [finiteFieldKummerAffineCurvePoints]
  simp_rw [primeKummerPowerFiber, Finset.card_filter]
  rw [Finset.sum_product]

/-- Exact affine point count over an arbitrary finite field. -/
theorem card_finiteFieldKummerAffineCurvePoints
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (P : Polynomial F) :
    (finiteFieldKummerAffineCurvePoints F χ P).card =
      (finiteFieldPolynomialZeroFiber F P).card +
        orderOf χ * (finiteFieldKummerKernelFiber F χ P).card := by
  classical
  rw [card_finiteFieldKummerAffineCurvePoints_eq_sum_fibers]
  simp_rw [card_primeKummerPowerFiber]
  have hzeroχ : ∀ x : F, P.eval x = 0 → χ (P.eval x) ≠ 1 := by
    intro x hx
    rw [hx, χ.map_zero]
    exact zero_ne_one
  calc
    (∑ x : F,
        if P.eval x = 0 then 1
        else if χ (P.eval x) = 1 then orderOf χ else 0) =
        ∑ x : F,
          ((if P.eval x = 0 then 1 else 0) +
            orderOf χ * (if χ (P.eval x) = 1 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hx0 : P.eval x = 0
      · have hxχ := hzeroχ x hx0
        simp only [if_pos hx0, if_neg hxχ, mul_zero, add_zero]
      · by_cases hxχ : χ (P.eval x) = 1 <;> simp [hx0, hxχ]
    _ = (∑ x : F, if P.eval x = 0 then 1 else 0) +
          orderOf χ * ∑ x : F, if χ (P.eval x) = 1 then 1 else 0 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = (finiteFieldPolynomialZeroFiber F P).card +
          orderOf χ * (finiteFieldKummerKernelFiber F χ P).card := by
      simp [finiteFieldPolynomialZeroFiber, finiteFieldKummerKernelFiber,
        Finset.sum_boole]

/-- The trivial-character correlation and the zero fiber partition the
finite field. -/
theorem finiteFieldPolynomialCharacterCorrelation_one_add_zeroFiber
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (P : Polynomial F) :
    finiteFieldPolynomialCharacterCorrelation F (1 : MulChar F ℂ) P +
        (finiteFieldPolynomialZeroFiber F P).card = (Fintype.card F : ℂ) := by
  classical
  have hcorr :
      finiteFieldPolynomialCharacterCorrelation F (1 : MulChar F ℂ) P =
        ∑ x : F, if P.eval x = 0 then 0 else 1 := by
    unfold finiteFieldPolynomialCharacterCorrelation
    apply Finset.sum_congr rfl
    intro x _hx
    by_cases hx : P.eval x = 0
    · rw [if_pos hx, hx, MulChar.map_zero]
    · rw [if_neg hx]
      exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)
  rw [hcorr]
  have hnonzero :
      (∑ x : F, if P.eval x = 0 then (0 : ℂ) else 1) =
        (((Finset.univ : Finset F).filter
          (fun x => ¬P.eval x = 0)).card : ℂ) := by
    calc
      (∑ x : F, if P.eval x = 0 then (0 : ℂ) else 1) =
          ∑ x : F, if ¬P.eval x = 0 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro x _hx
        by_cases hx : P.eval x = 0 <;> simp [hx]
      _ = (((Finset.univ : Finset F).filter
          (fun x => ¬P.eval x = 0)).card : ℂ) :=
        Finset.sum_boole (fun x : F => ¬P.eval x = 0) Finset.univ
  rw [hnonzero]
  have hcard := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset F)) (fun x => P.eval x = 0)
  have hcard' :
      ((Finset.univ.filter (fun x : F => ¬P.eval x = 0)).card +
        (finiteFieldPolynomialZeroFiber F P).card) = Fintype.card F := by
    rw [finiteFieldPolynomialZeroFiber]
    simpa [add_comm] using hcard
  exact_mod_cast hcard'

/-- Character-power orthogonality summed over an arbitrary finite-field
polynomial correlation. -/
theorem sum_range_finiteFieldPolynomialCharacterCorrelation_pow_succ
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (P : Polynomial F) :
    (∑ k ∈ Finset.range (orderOf χ),
        finiteFieldPolynomialCharacterCorrelation F (χ ^ (k + 1)) P) =
      (orderOf χ : ℂ) * (finiteFieldKummerKernelFiber F χ P).card := by
  unfold finiteFieldPolynomialCharacterCorrelation
  rw [Finset.sum_comm]
  simp_rw [χ.pow_apply' (Nat.succ_ne_zero _)]
  simp_rw [sum_range_mulChar_apply_pow_succ]
  calc
    (∑ x : F,
        if χ (P.eval x) = 1 then (orderOf χ : ℂ) else 0) =
        ∑ x : F, (orderOf χ : ℂ) *
          if χ (P.eval x) = 1 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      split <;> simp_all
    _ = (orderOf χ : ℂ) *
        ∑ x : F, if χ (P.eval x) = 1 then 1 else 0 := by
      rw [Finset.mul_sum]
    _ = (orderOf χ : ℂ) *
        (finiteFieldKummerKernelFiber F χ P).card := by
      simp [finiteFieldKummerKernelFiber, Finset.sum_boole]

/-- The proper positive character powers, excluding the terminal trivial
power. -/
def finiteFieldKummerProperTraceSum
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (P : Polynomial F) : ℂ :=
  ∑ k ∈ Finset.range (orderOf χ - 1),
    finiteFieldPolynomialCharacterCorrelation F (χ ^ (k + 1)) P

/-- Exact affine trace formula over an arbitrary finite field. -/
theorem card_finiteFieldKummerAffineCurvePoints_cast_eq_card_add_properTrace
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (P : Polynomial F) :
    ((finiteFieldKummerAffineCurvePoints F χ P).card : ℂ) =
      (Fintype.card F : ℂ) + finiteFieldKummerProperTraceSum F χ P := by
  classical
  have haff := card_finiteFieldKummerAffineCurvePoints F χ P
  have hpowers :=
    sum_range_finiteFieldPolynomialCharacterCorrelation_pow_succ F χ P
  have hsplit :
      (∑ k ∈ Finset.range (orderOf χ),
          finiteFieldPolynomialCharacterCorrelation F (χ ^ (k + 1)) P) =
        finiteFieldKummerProperTraceSum F χ P +
          finiteFieldPolynomialCharacterCorrelation F
            (1 : MulChar F ℂ) P := by
    unfold finiteFieldKummerProperTraceSum
    conv_lhs => rw [← Nat.sub_add_cancel χ.orderOf_pos]
    rw [Finset.sum_range_succ, Nat.sub_add_cancel χ.orderOf_pos,
      pow_orderOf_eq_one]
  have haffCast :
      ((finiteFieldKummerAffineCurvePoints F χ P).card : ℂ) =
        ((finiteFieldPolynomialZeroFiber F P).card : ℂ) +
          (orderOf χ : ℂ) * (finiteFieldKummerKernelFiber F χ P).card := by
    exact_mod_cast haff
  rw [← hpowers, hsplit] at haffCast
  calc
    ((finiteFieldKummerAffineCurvePoints F χ P).card : ℂ) =
        ((finiteFieldPolynomialZeroFiber F P).card : ℂ) +
          (finiteFieldKummerProperTraceSum F χ P +
            finiteFieldPolynomialCharacterCorrelation F
              (1 : MulChar F ℂ) P) := haffCast
    _ = finiteFieldKummerProperTraceSum F χ P +
          (finiteFieldPolynomialCharacterCorrelation F
            (1 : MulChar F ℂ) P +
              (finiteFieldPolynomialZeroFiber F P).card) := by ring
    _ = finiteFieldKummerProperTraceSum F χ P + Fintype.card F := by
      rw [finiteFieldPolynomialCharacterCorrelation_one_add_zeroFiber]
    _ = (Fintype.card F : ℂ) +
        finiteFieldKummerProperTraceSum F χ P := by ring

/-- A scalar factor pulls out of an arbitrary finite-field polynomial
correlation. -/
theorem finiteFieldPolynomialCharacterCorrelation_C_mul
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (ψ : MulChar F ℂ) (c : F) (P : Polynomial F) :
    finiteFieldPolynomialCharacterCorrelation F ψ (Polynomial.C c * P) =
      ψ c * finiteFieldPolynomialCharacterCorrelation F ψ P := by
  classical
  unfold finiteFieldPolynomialCharacterCorrelation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  simp only [Polynomial.eval_mul, Polynomial.eval_C, map_mul]

/-- Scalar-twisted affine Kummer points over an arbitrary finite field. -/
def finiteFieldKummerTwistedAffineCurvePoints
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (P : Polynomial F) (c : F) : Finset (F × F) :=
  finiteFieldKummerAffineCurvePoints F χ (Polynomial.C c * P)

/-- Deviation of a twisted affine Kummer point count from the field
cardinality. -/
def finiteFieldKummerAffineTraceDefect
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (P : Polynomial F) (c : F) : ℂ :=
  ((finiteFieldKummerTwistedAffineCurvePoints F χ P c).card : ℂ) -
    Fintype.card F

/-- The finite-field twisted trace defect is the proper character-power
trace. -/
theorem finiteFieldKummerAffineTraceDefect_eq_sum
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (P : Polynomial F) (c : F) :
    finiteFieldKummerAffineTraceDefect F χ P c =
      ∑ k ∈ Finset.range (orderOf χ - 1),
        (χ ^ (k + 1)) c *
          finiteFieldPolynomialCharacterCorrelation F (χ ^ (k + 1)) P := by
  rw [finiteFieldKummerAffineTraceDefect,
    finiteFieldKummerTwistedAffineCurvePoints,
    card_finiteFieldKummerAffineCurvePoints_cast_eq_card_add_properTrace]
  unfold finiteFieldKummerProperTraceSum
  simp_rw [finiteFieldPolynomialCharacterCorrelation_C_mul]
  ring

/-- Orthogonality of `χ⁻¹` against proper positive powers of `χ` over an
arbitrary finite field. -/
theorem sum_finiteField_mulChar_inv_mul_pow_succ
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (k : ℕ) (hk : k < orderOf χ) :
    (∑ c : F, χ⁻¹ c * (χ ^ (k + 1)) c) =
      if k = 0 then (Fintype.card F - 1 : ℕ) else 0 := by
  classical
  have hchar : χ⁻¹ * χ ^ (k + 1) = χ ^ k := by
    rw [pow_succ']
    group
  calc
    (∑ c : F, χ⁻¹ c * (χ ^ (k + 1)) c) =
        ∑ c : F, (χ⁻¹ * χ ^ (k + 1)) c := by rfl
    _ = ∑ c : F, (χ ^ k) c := by rw [hchar]
    _ = if k = 0 then (Fintype.card F - 1 : ℕ) else 0 := by
      by_cases hk0 : k = 0
      · subst k
        simp [MulChar.sum_one_eq_card_units, Fintype.card_units]
      · rw [if_neg hk0,
          MulChar.sum_eq_zero_of_ne_one (pow_ne_one_of_lt_orderOf hk0 hk)]
        norm_num

/-- Multiplicative Fourier inversion for scalar-twisted affine Kummer point
counts over every finite field. -/
theorem sum_mulChar_inv_mul_finiteFieldKummerAffineTraceDefect
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (P : Polynomial F) (hχ : χ ≠ 1) :
    (∑ c : F, χ⁻¹ c * finiteFieldKummerAffineTraceDefect F χ P c) =
      (Fintype.card F - 1 : ℕ) *
        finiteFieldPolynomialCharacterCorrelation F χ P := by
  classical
  have hd : 0 < orderOf χ - 1 := by
    have := mulChar_orderOf_two_le_of_ne_one χ hχ
    omega
  simp_rw [finiteFieldKummerAffineTraceDefect_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ x ∈ Finset.range (orderOf χ - 1),
        ∑ i : F,
          χ⁻¹ i *
            ((χ ^ (x + 1)) i *
              finiteFieldPolynomialCharacterCorrelation F (χ ^ (x + 1)) P)) =
        ∑ x ∈ Finset.range (orderOf χ - 1),
          (∑ i : F, χ⁻¹ i * (χ ^ (x + 1)) i) *
            finiteFieldPolynomialCharacterCorrelation F (χ ^ (x + 1)) P := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c _hc
      ring
    _ = ∑ x ∈ Finset.range (orderOf χ - 1),
          (if x = 0 then (Fintype.card F - 1 : ℕ) else 0) *
            finiteFieldPolynomialCharacterCorrelation F (χ ^ (x + 1)) P := by
      apply Finset.sum_congr rfl
      intro k hk
      have hklt : k < orderOf χ := by
        have := Finset.mem_range.mp hk
        omega
      rw [sum_finiteField_mulChar_inv_mul_pow_succ F χ k hklt]
    _ = (Fintype.card F - 1 : ℕ) *
        finiteFieldPolynomialCharacterCorrelation F χ P := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro k hk hk0
        simp [hk0]
      · intro hnot
        exact (hnot (Finset.mem_range.mpr hd)).elim

/-- The scalar-twisted affine trace defect over the degree-`n+2`
extension used by the positive-successor branch of
`primeKummerExtensionCorrelation`. -/
def primeKummerHigherExtensionAffineTraceDefect
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) (n : ℕ)
    (c : FiniteField.Extension (ZMod p) p (n + 2)) : ℂ := by
  let E := FiniteField.Extension (ZMod p) p (n + 2)
  letI : Fintype E := Fintype.ofFinite E
  letI : DecidableEq E := Classical.decEq E
  exact finiteFieldKummerAffineTraceDefect E
    (finiteFieldNormLiftMulChar (ZMod p) E χ)
    (P.map (algebraMap (ZMod p) E)) c

/-- Every positive-successor Kummer extension correlation is the normalized
`χ⁻¹` Fourier coefficient of scalar-twisted affine Kummer point-count
defects over that same extension field. -/
theorem sum_normLift_inv_mul_primeKummerHigherExtensionAffineTraceDefect
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hχ : χ ≠ 1) (n : ℕ) : by
      let E := FiniteField.Extension (ZMod p) p (n + 2)
      letI : Fintype E := Fintype.ofFinite E
      exact
        (∑ c : E,
          (finiteFieldNormLiftMulChar (ZMod p) E χ)⁻¹ c *
            primeKummerHigherExtensionAffineTraceDefect p χ P n c) =
          (Fintype.card E - 1 : ℕ) *
            primeKummerExtensionCorrelation p χ P (n + 1) := by
  let E := FiniteField.Extension (ZMod p) p (n + 2)
  letI : Fintype E := Fintype.ofFinite E
  letI : DecidableEq E := Classical.decEq E
  let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
  let PE := P.map (algebraMap (ZMod p) E)
  have hχE : χE ≠ 1 := finiteFieldNormLiftMulChar_ne_one
    (ZMod p) E hχ
  have hfourier :=
    sum_mulChar_inv_mul_finiteFieldKummerAffineTraceDefect E χE PE hχE
  have hcorr : primeKummerExtensionCorrelation p χ P (n + 1) =
      finiteFieldPolynomialCharacterCorrelation E χE PE := by
    rw [primeKummerExtensionCorrelation_succ_eq_normLift]
    rfl
  rw [hcorr]
  simpa [primeKummerHigherExtensionAffineTraceDefect, χE, PE] using hfourier

/-- Cardinality-explicit form of the extension-field Fourier identity. -/
theorem sum_normLift_inv_mul_primeKummerHigherExtensionAffineTraceDefect_eq_pow
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hχ : χ ≠ 1) (n : ℕ) : by
      let E := FiniteField.Extension (ZMod p) p (n + 2)
      letI : Fintype E := Fintype.ofFinite E
      exact
        (∑ c : E,
          (finiteFieldNormLiftMulChar (ZMod p) E χ)⁻¹ c *
            primeKummerHigherExtensionAffineTraceDefect p χ P n c) =
          (p ^ (n + 2) - 1 : ℕ) *
            primeKummerExtensionCorrelation p χ P (n + 1) := by
  let E := FiniteField.Extension (ZMod p) p (n + 2)
  letI : Fintype E := Fintype.ofFinite E
  have h :=
    sum_normLift_inv_mul_primeKummerHigherExtensionAffineTraceDefect
      p χ P hχ n
  have hcard : Fintype.card E = p ^ (n + 2) := by
    rw [← Nat.card_eq_fintype_card, FiniteField.natCard_extension,
      Nat.card_zmod]
  simpa [E, hcard] using h

end

end Tao2026
