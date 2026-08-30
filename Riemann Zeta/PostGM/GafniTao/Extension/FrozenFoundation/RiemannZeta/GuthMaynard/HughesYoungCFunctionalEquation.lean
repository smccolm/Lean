import RiemannZeta.GuthMaynard.HughesYoungLemma61

open Complex Finset
open scoped BigOperators

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Hughes--Young equations (125)--(130)

This file starts the Section 6 recombination at its arithmetic core.  The
three local numerators are exactly equations (101)--(103), written using the
single variable `x = p^(-alpha-delta-2s)`.  Equations (128)--(130) are then
proved as rational identities and assembled prime by prime into the finite
Euler-product functional equation (125).
-/

/-- Equation (101), with `x = p^(-alpha-delta-2s)`. -/
def hughesYoungC0 (e : ℕ) (x : ℂ) : ℂ :=
  1 - x ^ (1 + e)

/-- Equation (102), with `u = p^(gamma-delta)`,
`v = p^(alpha-beta)`, and `x = p^(-alpha-delta-2s)`. -/
def hughesYoungC1 (e : ℕ) (u v x : ℂ) : ℂ :=
  (u + v * x) * (1 - x ^ e)

/-- Equation (103), after extracting its nonzero monomial coefficient. -/
def hughesYoungC2 (e : ℕ) (x : ℂ) : ℂ :=
  x - x ^ e

/-- Hughes--Young equation (128). -/
theorem hughesYoungEquation128 {e : ℕ} {x : ℂ}
    (hx : x ≠ 0) (hx1 : 1 - x ≠ 0) :
    hughesYoungC0 e x / (1 - x) =
      x ^ e * (hughesYoungC0 e x⁻¹ / (1 - x⁻¹)) := by
  unfold hughesYoungC0
  have hden : 1 - x⁻¹ = (x - 1) / x := by field_simp [hx]
  have hxm : x - 1 ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hx1))
  have hdiv (A : ℂ) : A / ((x - 1) / x) = A * x / (x - 1) := by
    field_simp [hx]
  rw [hden, hdiv, Nat.one_add]
  simp only [pow_succ, inv_pow]
  field_simp [hx, hx1, hxm, pow_ne_zero]
  ring

/-- Hughes--Young equation (129). -/
theorem hughesYoungEquation129 {e : ℕ} {x u v : ℂ}
    (hx : x ≠ 0) (hx1 : 1 - x ≠ 0) :
    hughesYoungC1 e u v x / (1 - x) =
      x ^ e * (hughesYoungC1 e v u x⁻¹ / (1 - x⁻¹)) := by
  unfold hughesYoungC1
  have hden : 1 - x⁻¹ = (x - 1) / x := by field_simp [hx]
  have hxm : x - 1 ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hx1))
  have hdiv (A : ℂ) : A / ((x - 1) / x) = A * x / (x - 1) := by
    field_simp [hx]
  rw [hden, hdiv]
  simp only [inv_pow]
  field_simp [hx, hx1, hxm, pow_ne_zero]
  ring

/-- Hughes--Young equation (130). -/
theorem hughesYoungEquation130 {e : ℕ} {x : ℂ}
    (hx : x ≠ 0) (hx1 : 1 - x ≠ 0) :
    hughesYoungC2 e x / (1 - x) =
      x ^ e * (hughesYoungC2 e x⁻¹ / (1 - x⁻¹)) := by
  unfold hughesYoungC2
  have hden : 1 - x⁻¹ = (x - 1) / x := by field_simp [hx]
  have hxm : x - 1 ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hx1))
  have hdiv (A : ℂ) : A / ((x - 1) / x) = A * x / (x - 1) := by
    field_simp [hx]
  rw [hden, hdiv]
  simp only [inv_pow]
  field_simp [hx, hx1, hxm, pow_ne_zero]
  ring

/-- The common-denominator combination of equations (128)--(130). -/
theorem hughesYoungEquation127_algebra
    {e : ℕ} {x u v a b r : ℂ}
    (hx : x ≠ 0) (hx1 : 1 - x ≠ 0) (hr : r ≠ 0) :
    (hughesYoungC0 e x - a * hughesYoungC1 e u v x +
        b * hughesYoungC2 e x) / (r * (1 - x)) =
      x ^ e *
        ((hughesYoungC0 e x⁻¹ - a * hughesYoungC1 e v u x⁻¹ +
          b * hughesYoungC2 e x⁻¹) / (r * (1 - x⁻¹))) := by
  have hxm : x - 1 ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hx1))
  unfold hughesYoungC0 hughesYoungC1 hughesYoungC2
  rw [Nat.one_add]
  simp only [pow_succ, inv_pow]
  field_simp [hx, hx1, hxm, hr, pow_ne_zero]
  ring

/-- The three numerator terms in equation (100). -/
def hughesYoungCPrimeNumerator
    (e p : ℕ) (alpha beta gamma delta s : ℂ) : ℂ :=
  let x : ℂ := (p : ℂ) ^ (-alpha - delta - 2 * s)
  hughesYoungC0 e x - (p : ℂ) ^ (-1 : ℂ) *
      hughesYoungC1 e
        ((p : ℂ) ^ (gamma - delta))
        ((p : ℂ) ^ (alpha - beta)) x +
    (p : ℂ) ^ (-2 : ℂ) *
      ((p : ℂ) ^ (alpha - beta + gamma - delta) * hughesYoungC2 e x)

/-- The local factor in equation (100), including both displayed
denominators. -/
def hughesYoungCPrimeFactor
    (e p : ℕ) (alpha beta gamma delta s : ℂ) : ℂ :=
  hughesYoungCPrimeNumerator e p alpha beta gamma delta s /
    ((1 - (p : ℂ) ^ (-2 + alpha - beta + gamma - delta)) *
      (1 - (p : ℂ) ^ (-alpha - delta - 2 * s)))

/-- Equation (100), as a finite Euler product over the primes dividing `h`.
This finite product is the meromorphic continuation of the correction factor
first obtained in the absolute-convergence region of Lemma 6.1. -/
def hughesYoungC
    (h : ℕ) (alpha beta gamma delta s : ℂ) : ℂ :=
  ∏ p ∈ hughesYoungPrimeFactors h,
    hughesYoungCPrimeFactor (h.factorization p) p alpha beta gamma delta s

private theorem cpow_neg_eq_inv {p : ℕ} (z : ℂ) :
    (p : ℂ) ^ (-z) = ((p : ℂ) ^ z)⁻¹ := by
  rw [Complex.cpow_neg]

/-- Primewise form of equation (127), already summed across the three
numerator components. -/
theorem hughesYoungEquation127
    {h : ℕ} {p : Nat.Primes}
    {alpha beta gamma delta s : ℂ}
    (hx1 : 1 - (p : ℂ) ^ (-alpha - delta + 2 * s) ≠ 0)
    (hreg : 1 - (p : ℂ) ^ (-2 + alpha - beta + gamma - delta) ≠ 0) :
    hughesYoungCPrimeFactor (h.factorization p) p
        alpha beta gamma delta (-s) =
      ((p : ℂ) ^ (-alpha - delta + 2 * s)) ^ (h.factorization p) *
        hughesYoungCPrimeFactor (h.factorization p) p
          (-delta) (-gamma) (-beta) (-alpha) s := by
  let x : ℂ := (p : ℂ) ^ (-alpha - delta + 2 * s)
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hx : x ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hp0)
  have hxInv : (p : ℂ) ^ (alpha + delta - 2 * s) = x⁻¹ := by
    rw [show alpha + delta - 2 * s = -(-alpha - delta + 2 * s) by ring]
    exact cpow_neg_eq_inv _
  have halg := hughesYoungEquation127_algebra
    (e := h.factorization p) (x := x)
    (u := (p : ℂ) ^ (gamma - delta))
    (v := (p : ℂ) ^ (alpha - beta))
    (a := (p : ℂ) ^ (-1 : ℂ))
    (b := (p : ℂ) ^ (-2 : ℂ) *
      (p : ℂ) ^ (alpha - beta + gamma - delta))
    (r := 1 - (p : ℂ) ^ (-2 + alpha - beta + gamma - delta))
    hx hx1 hreg
  unfold hughesYoungCPrimeFactor hughesYoungCPrimeNumerator
  dsimp only
  rw [show -alpha - delta - 2 * -s = -alpha - delta + 2 * s by ring]
  rw [show - -delta - -alpha - 2 * s = alpha + delta - 2 * s by ring]
  rw [hxInv]
  rw [show -2 + -delta - -gamma + -beta - -alpha =
      -2 + alpha - beta + gamma - delta by ring]
  rw [show -beta - -alpha = alpha - beta by ring]
  rw [show -delta - -gamma = gamma - delta by ring]
  rw [show gamma - delta + -beta - -alpha =
      alpha - beta + gamma - delta by ring]
  simpa only [x, mul_assoc] using halg

/-- The prime-power factors in a finite factorization multiply back to the
original natural number. -/
theorem prod_hughesYoungPrimeFactors_factorization
    {h : ℕ} (hh : h ≠ 0) :
    ∏ p ∈ hughesYoungPrimeFactors h,
        (p : ℕ) ^ (h.factorization p) = h := by
  unfold hughesYoungPrimeFactors
  rw [prod_map]
  change (∏ x ∈ h.primeFactors.attach, x.1 ^ h.factorization x.1) = h
  simpa [← Nat.prod_factorization_eq_prod_primeFactors] using
    Nat.prod_factorization_pow_eq_self hh

/-- Complex powers of the prime-power factorization multiply to the complex
power of the original positive natural number. -/
theorem prod_hughesYoungPrimeFactors_cpow
    {h : ℕ} (hh : h ≠ 0) (z : ℂ) :
    ∏ p ∈ hughesYoungPrimeFactors h,
        ((p : ℂ) ^ z) ^ (h.factorization p) = (h : ℂ) ^ z := by
  calc
    _ = ∏ p ∈ hughesYoungPrimeFactors h,
        (((p : ℕ) ^ (h.factorization p) : ℕ) : ℂ) ^ z := by
      apply Finset.prod_congr rfl
      intro p _hp
      rw [Nat.cast_pow]
      rw [← Complex.natCast_cpow_natCast_mul]
      exact (Complex.cpow_nat_mul (p : ℂ) (h.factorization p) z).symm
    _ = (((∏ p ∈ hughesYoungPrimeFactors h,
        (p : ℕ) ^ (h.factorization p)) : ℕ) : ℂ) ^ z := by
      induction hughesYoungPrimeFactors h using Finset.induction_on with
      | empty => simp
      | @insert p S hp ih =>
          rw [Finset.prod_insert hp, Finset.prod_insert hp, Nat.cast_mul]
          rw [Complex.natCast_mul_natCast_cpow]
          rw [ih]
    _ = _ := by rw [prod_hughesYoungPrimeFactors_factorization hh]

/-- Hughes--Young equation (125), on the regular locus of the displayed
finite Euler factors.  Since `hughesYoungC` is a finite rational expression,
this is precisely the pointwise form used before meromorphic continuation. -/
theorem hughesYoungEquation125
    {h : ℕ} (hh : 0 < h) {alpha beta gamma delta s : ℂ}
    (hx : ∀ p ∈ hughesYoungPrimeFactors h,
      1 - (p : ℂ) ^ (-alpha - delta + 2 * s) ≠ 0)
    (hreg : ∀ p ∈ hughesYoungPrimeFactors h,
      1 - (p : ℂ) ^ (-2 + alpha - beta + gamma - delta) ≠ 0) :
    (h : ℂ) ^ (-s + alpha) *
        hughesYoungC h alpha beta gamma delta (-s) =
      (h : ℂ) ^ (s - delta) *
        hughesYoungC h (-delta) (-gamma) (-beta) (-alpha) s := by
  have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  rw [hughesYoungC, hughesYoungC]
  calc
    (h : ℂ) ^ (-s + alpha) *
        ∏ p ∈ hughesYoungPrimeFactors h,
          hughesYoungCPrimeFactor (h.factorization p) p
            alpha beta gamma delta (-s) =
      (h : ℂ) ^ (-s + alpha) *
        ∏ p ∈ hughesYoungPrimeFactors h,
          (((p : ℂ) ^ (-alpha - delta + 2 * s)) ^ (h.factorization p) *
            hughesYoungCPrimeFactor (h.factorization p) p
              (-delta) (-gamma) (-beta) (-alpha) s) := by
        congr 1
        apply Finset.prod_congr rfl
        intro p hp
        exact hughesYoungEquation127 (hx p hp) (hreg p hp)
    _ = (h : ℂ) ^ (-s + alpha) *
        ((∏ p ∈ hughesYoungPrimeFactors h,
            ((p : ℂ) ^ (-alpha - delta + 2 * s)) ^ (h.factorization p)) *
          ∏ p ∈ hughesYoungPrimeFactors h,
            hughesYoungCPrimeFactor (h.factorization p) p
              (-delta) (-gamma) (-beta) (-alpha) s) := by
        rw [Finset.prod_mul_distrib]
    _ = (h : ℂ) ^ (-s + alpha) *
        ((h : ℂ) ^ (-alpha - delta + 2 * s) *
          ∏ p ∈ hughesYoungPrimeFactors h,
            hughesYoungCPrimeFactor (h.factorization p) p
              (-delta) (-gamma) (-beta) (-alpha) s) := by
        rw [prod_hughesYoungPrimeFactors_cpow hh.ne']
    _ = (h : ℂ) ^ (s - delta) *
        ∏ p ∈ hughesYoungPrimeFactors h,
          hughesYoungCPrimeFactor (h.factorization p) p
            (-delta) (-gamma) (-beta) (-alpha) s := by
        rw [← mul_assoc, ← Complex.cpow_add _ _ hhC]
        congr 2
        ring

/-- Hughes--Young equation (126), obtained by applying (125) to both twist
variables. -/
theorem hughesYoungEquation126
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {alpha beta gamma delta s : ℂ}
    (hhx : ∀ p ∈ hughesYoungPrimeFactors h,
      1 - (p : ℂ) ^ (-alpha - delta + 2 * s) ≠ 0)
    (hhreg : ∀ p ∈ hughesYoungPrimeFactors h,
      1 - (p : ℂ) ^ (-2 + alpha - beta + gamma - delta) ≠ 0)
    (hkx : ∀ p ∈ hughesYoungPrimeFactors k,
      1 - (p : ℂ) ^ (-gamma - beta + 2 * s) ≠ 0)
    (hkreg : ∀ p ∈ hughesYoungPrimeFactors k,
      1 - (p : ℂ) ^ (-2 + gamma - delta + alpha - beta) ≠ 0) :
    (h * k : ℂ) ^ (-s) * (h : ℂ) ^ alpha * (k : ℂ) ^ gamma *
        (hughesYoungC h alpha beta gamma delta (-s) *
          hughesYoungC k gamma delta alpha beta (-s)) =
      (h * k : ℂ) ^ s * (h : ℂ) ^ (-delta) * (k : ℂ) ^ (-beta) *
        (hughesYoungC h (-delta) (-gamma) (-beta) (-alpha) s *
          hughesYoungC k (-beta) (-alpha) (-delta) (-gamma) s) := by
  have hH := hughesYoungEquation125 hh hhx hhreg
  have hK := hughesYoungEquation125 (h := k) hk hkx hkreg
  have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [Complex.natCast_mul_natCast_cpow]
  rw [Complex.natCast_mul_natCast_cpow]
  calc
    ((h : ℂ) ^ (-s) * (k : ℂ) ^ (-s)) * (h : ℂ) ^ alpha *
          (k : ℂ) ^ gamma *
        (hughesYoungC h alpha beta gamma delta (-s) *
          hughesYoungC k gamma delta alpha beta (-s)) =
      ((h : ℂ) ^ (-s + alpha) *
          hughesYoungC h alpha beta gamma delta (-s)) *
        ((k : ℂ) ^ (-s + gamma) *
          hughesYoungC k gamma delta alpha beta (-s)) := by
        rw [Complex.cpow_add _ _ hhC, Complex.cpow_add _ _ hkC]
        ring
    _ = ((h : ℂ) ^ (s - delta) *
          hughesYoungC h (-delta) (-gamma) (-beta) (-alpha) s) *
        ((k : ℂ) ^ (s - beta) *
          hughesYoungC k (-beta) (-alpha) (-delta) (-gamma) s) := by
        rw [hH, hK]
    _ = ((h : ℂ) ^ s * (k : ℂ) ^ s) * (h : ℂ) ^ (-delta) *
          (k : ℂ) ^ (-beta) *
        (hughesYoungC h (-delta) (-gamma) (-beta) (-alpha) s *
          hughesYoungC k (-beta) (-alpha) (-delta) (-gamma) s) := by
        rw [show s - delta = s + (-delta) by ring]
        rw [show s - beta = s + (-beta) by ring]
        rw [Complex.cpow_add _ _ hhC, Complex.cpow_add _ _ hkC]
        ring

end RiemannZeta.GuthMaynard
