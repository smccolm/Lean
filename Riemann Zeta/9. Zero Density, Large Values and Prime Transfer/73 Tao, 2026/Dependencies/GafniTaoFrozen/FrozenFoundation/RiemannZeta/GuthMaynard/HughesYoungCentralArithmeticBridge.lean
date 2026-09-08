import RiemannZeta.GuthMaynard.HughesYoungMainTerms
import RiemannZeta.GuthMaynard.DFIEquation30

open Complex Finset Filter Set
open scoped BigOperators Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# The DFI central coefficient in Hughes--Young notation

This file begins the exact source bridge from the signed DFI equation-(27)
central series to Hughes--Young equation (96).  The reduced twisting integers
are coprime, so the `gcd (a*b) q` in DFI is literally the product of the two
local gcd factors in Hughes--Young.
-/

/-- For coprime twisting integers, DFI's equation-(27) arithmetic coefficient
is exactly the coefficient of the `(r,q)` term in Hughes--Young equation (96)
at `a=b=1`. -/
theorem dfiEquation27ArithmeticCoefficient_eq_hughesYoung96
    {a b q r : ℕ} [NeZero q] (hab : a.Coprime b) :
    dfiEquation27ArithmeticCoefficient a b r q =
      ramanujanSum q r *
        (((Nat.gcd a q : ℕ) : ℂ) * ((Nat.gcd b q : ℕ) : ℂ)) /
          (q : ℂ) ^ 2 := by
  rw [dfiEquation27ArithmeticCoefficient_eq]
  have hgcd : Nat.gcd (a * b) q = Nat.gcd a q * Nat.gcd b q := by
    simpa [Nat.gcd_comm] using (hab.gcd_mul q)
  rw [hgcd]
  push_cast
  ring

/-- The same coefficient identity with the equation-(96) powers displayed
literally.  This is the termwise bridge used before differentiating the two
Mellin parameters that generate DFI's logarithmic factors. -/
theorem dfiEquation27ArithmeticCoefficient_eq_hughesYoung96_powers
    {a b q r : ℕ} [NeZero q] (hab : a.Coprime b) :
    dfiEquation27ArithmeticCoefficient a b r q =
      ramanujanSum q r *
        ((Nat.gcd a q : ℕ) : ℂ) ^ (1 : ℂ) *
        ((Nat.gcd b q : ℕ) : ℂ) ^ (1 : ℂ) /
          ((q : ℂ) ^ ((1 : ℂ) + 1)) := by
  rw [dfiEquation27ArithmeticCoefficient_eq_hughesYoung96 hab]
  simp only [Complex.cpow_one]
  rw [show (1 : ℂ) + 1 = (2 : ℕ) by norm_num, Complex.cpow_natCast]
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  field_simp [hqC]

/-- With the source sums indexed from one, the DFI arithmetic coefficient is
the zero-`c` summand of Hughes--Young equation (96) at `a=b=1`.  This is an
identity of the actual summands, not only an equality after summation. -/
theorem dfiEquation27ArithmeticCoefficient_eq_hughesYoungEquation96Term
    {a b : ℕ} (hab : a.Coprime b) (r q : ℕ) :
    dfiEquation27ArithmeticCoefficient a b (r + 1) (q + 1) =
      hughesYoungEquation96Term a b 1 1 0 r q := by
  letI : NeZero (q + 1) := ⟨Nat.succ_ne_zero q⟩
  rw [dfiEquation27ArithmeticCoefficient_eq_hughesYoung96 hab]
  unfold hughesYoungEquation96Term
  simp only [Complex.cpow_one, Complex.cpow_zero, mul_one]
  rw [show (1 : ℂ) + 1 = (2 : ℕ) by norm_num, Complex.cpow_natCast]
  have hqC : (((q + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero q
  field_simp [hqC]

/-- General exponent form of the preceding bridge.  The DFI coefficient
times the physical positive-shift Mellin weight is exactly the arbitrary-`c`
summand of Hughes--Young equation (96). -/
theorem dfiEquation27ArithmeticCoefficient_mul_shift_cpow_eq_hughesYoungEquation96Term
    {a b : ℕ} (hab : a.Coprime b) (c : ℂ) (r q : ℕ) :
    dfiEquation27ArithmeticCoefficient a b (r + 1) (q + 1) /
        (((r + 1 : ℕ) : ℂ) ^ c) =
      hughesYoungEquation96Term a b 1 1 c r q := by
  letI : NeZero (q + 1) := ⟨Nat.succ_ne_zero q⟩
  rw [dfiEquation27ArithmeticCoefficient_eq_hughesYoung96 hab]
  unfold hughesYoungEquation96Term
  simp only [Complex.cpow_one]
  rw [show (1 : ℂ) + 1 = (2 : ℕ) by norm_num, Complex.cpow_natCast]
  have hqC : (((q + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero q
  have hrC : (((r + 1 : ℕ) : ℂ) ^ c) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast Nat.succ_ne_zero r))
  field_simp [hqC, hrC]

/-- After the physical substitution `x = a u`, the logarithm in DFI
equation (27) is the Hughes--Young logarithm: the reduced denominator
`q / gcd(a,q)` contributes `log gcd(a,q) - log q`. -/
theorem dfiEquation27LogFactor_reduced_nat_mul
    {a q : ℕ} (ha : 0 < a) (hq : 0 < q) {u : ℝ} (hu : 0 < u) :
    dfiEquation27LogFactor a (dfiReducedDenominator a q) ((a : ℝ) * u) =
      (Real.log u : ℂ) + 2 * Real.eulerMascheroniConstant -
        2 * Complex.log (q : ℂ) + 2 * Complex.log (Nat.gcd a q : ℂ) := by
  letI : NeZero q := ⟨hq.ne'⟩
  let R := dfiReducedModulus a q
  have hg : 0 < R.gcd := R.gcd_pos
  have hd : 0 < R.denominator := R.denominator_pos
  have hrec : R.gcd * R.denominator = q := R.denominator_reconstruct
  have hlogR : Real.log (q : ℝ) =
      Real.log (R.gcd : ℝ) + Real.log (R.denominator : ℝ) := by
    rw [show (q : ℝ) = (R.gcd : ℝ) * (R.denominator : ℝ) by
      exact_mod_cast hrec.symm]
    exact Real.log_mul (by exact_mod_cast hg.ne') (by exact_mod_cast hd.ne')
  have hlogC : Complex.log (q : ℂ) =
      Complex.log (R.gcd : ℂ) + Complex.log (R.denominator : ℂ) := by
    simpa only [Complex.natCast_log, Complex.ofReal_add] using
      congrArg (fun x : ℝ => (x : ℂ)) hlogR
  rw [dfiEquation27LogFactor_nat_mul a (dfiReducedDenominator a q) ha u hu]
  change (Real.log u : ℂ) + 2 * Real.eulerMascheroniConstant -
      2 * Complex.log (R.denominator : ℂ) =
        (Real.log u : ℂ) + 2 * Real.eulerMascheroniConstant -
          2 * Complex.log (q : ℂ) + 2 * Complex.log (R.gcd : ℂ)
  rw [hlogC]
  ring

/-- The entire DFI modulus series for a fixed positive shift is exactly the
inner `l`-series of Hughes--Young equation (96) at `(a,b,c)=(1,1,0)`.
Absolute summability comes from DFI equation (26), so the removal of the
zero modulus and the reindexing are kernel-checked. -/
theorem tsum_dfiEquation27ArithmeticCoefficient_eq_hughesYoung96_inner
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (r : ℕ) :
    (∑' q : ℕ, dfiEquation27ArithmeticCoefficient a b (r + 1) q) =
      ∑' l : ℕ, hughesYoungEquation96Term a b 1 1 0 r l := by
  have hsum : Summable (fun q : ℕ =>
      dfiEquation27ArithmeticCoefficient a b (r + 1) q) :=
    (summable_norm_dfiEquation27ArithmeticCoefficient a b (r + 1)
      ha hb (Nat.succ_pos r)).of_norm
  have hsplit := hsum.sum_add_tsum_nat_add 1
  have hshift :
      (∑' q : ℕ, dfiEquation27ArithmeticCoefficient a b (r + 1) q) =
        ∑' l : ℕ, dfiEquation27ArithmeticCoefficient a b (r + 1) (l + 1) := by
    simpa [dfiEquation27ArithmeticCoefficient_zero] using hsplit.symm
  rw [hshift]
  apply tsum_congr
  intro l
  exact dfiEquation27ArithmeticCoefficient_eq_hughesYoungEquation96Term hab r l

/-- Hughes--Young equation (96), specialized to the two unit gcd exponents,
is literally the double DFI equation-(27) arithmetic series with its positive
shift Mellin weight.  No Euler-product manipulation is used here. -/
theorem hughesYoungEquation96_one_one_eq_dfiArithmeticSeries
    {a b : ℕ} (hab : a.Coprime b) (c : ℂ) :
    hughesYoungEquation96 a b 1 1 c =
      ∑' r : ℕ, ∑' q : ℕ,
        dfiEquation27ArithmeticCoefficient a b (r + 1) (q + 1) /
          (((r + 1 : ℕ) : ℂ) ^ c) := by
  rw [hughesYoungEquation96_eq_tsum_term]
  apply tsum_congr
  intro r
  apply tsum_congr
  intro q
  exact
    (dfiEquation27ArithmeticCoefficient_mul_shift_cpow_eq_hughesYoungEquation96Term
      hab c r q).symm

/-- DFI's equation-(27) arithmetic series evaluated by Hughes--Young
Lemma 6.1.  This composes the termwise source bridge with the already proved
Ramanujan-series Euler product, in its genuine absolute-convergence region. -/
theorem dfiArithmeticSeries_eq_hughesYoungLemma61
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    {c : ℂ} (hc : 0 < c.re) :
    (∑' r : ℕ, ∑' q : ℕ,
        dfiEquation27ArithmeticCoefficient a b (r + 1) (q + 1) /
          (((r + 1 : ℕ) : ℂ) ^ (1 + c))) =
      riemannZeta (1 + c) *
        (riemannZeta (2 + c) / riemannZeta 2) *
        ((∏ p ∈ hughesYoungPrimeFactors a,
            hughesYoungLemma61LeftFactor a 1 1 c p) *
          ∏ p ∈ hughesYoungPrimeFactors b,
            hughesYoungLemma61RightFactor b 1 1 c p) := by
  rw [← hughesYoungEquation96_one_one_eq_dfiArithmeticSeries hab]
  have hpc : 1 < (1 + c).re := by simpa using add_lt_add_left hc 1
  have hleft : ∀ p ∈ hughesYoungPrimeFactors a,
      1 - (p : ℂ) ^ (-((1 : ℂ) + c)) ≠ 0 := by
    intro p _hp
    exact Complex.one_sub_prime_cpow_ne_zero p.prop hpc
  have hright : ∀ p ∈ hughesYoungPrimeFactors b,
      1 - (p : ℂ) ^ (-((1 : ℂ) + c)) ≠ 0 := by
    intro p _hp
    exact Complex.one_sub_prime_cpow_ne_zero p.prop hpc
  convert (hughesYoungLemma61_source ha hb hab
    (a := (1 : ℂ)) (b := (1 : ℂ)) (c := c)
    (by norm_num) hc hleft hright) using 1
  all_goals norm_num

end RiemannZeta.GuthMaynard
