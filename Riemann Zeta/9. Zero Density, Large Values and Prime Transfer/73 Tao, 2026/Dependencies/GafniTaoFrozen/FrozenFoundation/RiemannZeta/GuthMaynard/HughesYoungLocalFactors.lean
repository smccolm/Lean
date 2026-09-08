import RiemannZeta.GuthMaynard.HughesYoungEulerProduct

open Complex Finset
open scoped BigOperators

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Source-facing local Euler factors in Hughes--Young Lemma 6.1

This file applies the algebraic equations (107)--(118) to the actual
prime-power coefficients obtained from equation (106).  Thus the displayed
local factors are not independent rational-function identities: their left
sides are the Euler factors of the convergent arithmetic series.
-/

private theorem primeShiftNormLtOne {p : ℕ} (hp : p.Prime)
    {s : ℂ} (hs : 1 < s.re) : ‖(p : ℂ) ^ (-s)‖ < 1 := by
  have hhalf := Complex.norm_prime_cpow_le_one_half ⟨p, hp⟩ hs
  linarith

private theorem primeCPow_mul_neg_eq {p : ℕ} (hp : p.Prime)
    (u v : ℂ) :
    (p : ℂ) ^ (-u) * (p : ℂ) ^ (-v) = (p : ℂ) ^ (-(u + v)) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [← Complex.cpow_add _ _ hp0]
  congr 1
  ring

private theorem primeCPow_neg_inv {p : ℕ} (c : ℂ) :
    ((p : ℂ) ^ (-c))⁻¹ = (p : ℂ) ^ c := by
  rw [Complex.cpow_neg]
  exact inv_inv _

/-- Equation (108) for the actual prime Euler factor when `p ∤ hk`. -/
theorem hughesYoungEquation108_localFactor
    {h k p : ℕ} (hh : 0 < h) (hk : 0 < k) (hp : p.Prime)
    (hph : ¬ p ∣ h) (hpk : ¬ p ∣ k)
    {a b c : ℂ} (hA : 1 < (a + b).re) (hC : 0 < c.re) :
    (∑' e : ℕ, hughesYoungEquation106Coefficient h k a b c (p ^ e)) =
      (1 - (p : ℂ) ^ (-(a + b))) /
        (1 - (p : ℂ) ^ (-(a + b + c))) := by
  let q : ℂ := (p : ℂ) ^ (-(a + b + c))
  let z : ℂ := (p : ℂ) ^ (-c)
  let v : ℂ := (p : ℂ) ^ (-(a + b))
  have hS : 1 < (a + b + c).re := by
    have hA' : 1 < a.re + b.re := by simpa using hA
    simp only [add_re]
    linarith
  have hq : ‖q‖ < 1 := primeShiftNormLtOne hp hS
  have hq1 : 1 - q ≠ 0 := Complex.one_sub_prime_cpow_ne_zero hp hS
  have hzInv : z⁻¹ = (p : ℂ) ^ c := primeCPow_neg_inv c
  have huq : z⁻¹ * q = v := by
    rw [hzInv]
    unfold q v
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [← Complex.cpow_add _ _ hp0]
    congr 1
    ring
  rw [hughesYoungEquation107_of_not_dvd hh hk hp hph hpk hA hC]
  rw [← hzInv]
  change 1 + (1 - z⁻¹) * hughesYoungEquation107Series q =
    (1 - v) / (1 - q)
  rw [hughesYoungEquation107 hq]
  rw [hughesYoungEquation108 hq1 huq]

/-- Equation (118) for the actual prime Euler factor at a prime dividing
`h`.  The nonvanishing of the second geometric denominator is retained
explicitly; it is later supplied in the initial convergence region before
analytic continuation. -/
theorem hughesYoungEquation118_localFactor_left
    {h k p : ℕ} (hh : 0 < h) (hk : 0 < k) (hp : p.Prime)
    (hhk : Nat.Coprime h k) (hph : p ∣ h)
    {a b c : ℂ} (hA : 1 < (a + b).re) (hC : 0 < c.re)
    (hr1 : 1 - (p : ℂ) ^ (-(b + c)) ≠ 0) :
    (∑' e : ℕ, hughesYoungEquation106Coefficient h k a b c (p ^ e)) =
      (((1 - (p : ℂ) ^ (-b)) *
          (1 - (p : ℂ) ^ (-(a + b + c))) +
        (p : ℂ) ^ (-b) * (1 - (p : ℂ) ^ (-a)) *
          (1 - (p : ℂ) ^ (-c)) *
          ((p : ℂ) ^ (-(b + c))) ^ (h.factorization p)) /
        ((1 - (p : ℂ) ^ (-(b + c))) *
          (1 - (p : ℂ) ^ (-(a + b + c))))) := by
  let x : ℂ := (p : ℂ) ^ (-a)
  let y : ℂ := (p : ℂ) ^ (-b)
  let z : ℂ := (p : ℂ) ^ (-c)
  let q : ℂ := x * y * z
  let r : ℂ := y * z
  have hS : 1 < (a + b + c).re := by
    have hA' : 1 < a.re + b.re := by simpa using hA
    simp only [add_re]
    linarith
  have hqRaw : ‖(p : ℂ) ^ (-(a + b + c))‖ < 1 :=
    primeShiftNormLtOne hp hS
  have hqEq : q = (p : ℂ) ^ (-(a + b + c)) := by
    unfold q x y z
    rw [primeCPow_mul_neg_eq hp a b]
    exact primeCPow_mul_neg_eq hp (a + b) c
  have hrEq : r = (p : ℂ) ^ (-(b + c)) := by
    unfold r y z
    exact primeCPow_mul_neg_eq hp b c
  have hq : ‖q‖ < 1 := by simpa [hqEq] using hqRaw
  have hq1 : 1 - q ≠ 0 := by
    rw [hqEq]
    exact Complex.one_sub_prime_cpow_ne_zero hp hS
  have hr1' : 1 - r ≠ 0 := by simpa [hrEq] using hr1
  have hzInv : z⁻¹ = (p : ℂ) ^ c := primeCPow_neg_inv c
  rw [hughesYoungEquation109_of_dvd_left hh hk hp hhk hph hA hC]
  rw [← hzInv]
  rw [← hqEq, ← hrEq]
  change 1 + (1 - z⁻¹) *
      hughesYoungEquation109Series (h.factorization p) q r =
    (((1 - y) * (1 - q) + y * (1 - x) * (1 - z) *
      r ^ (h.factorization p)) / ((1 - r) * (1 - q)))
  rw [hughesYoungEquation111 hq hr1']
  have hxr : x * r = q := by
    unfold x r q y z
    ring
  rw [hughesYoungEquation112 hq1 hr1' hxr,
    hughesYoungEquation113 hq1 hr1' hxr]
  change hughesYoungEquation114LocalFactor (h.factorization p) x y z = _
  rw [hughesYoungEquation114 hq1 hr1']
  have hz0 : z ≠ 0 := by
    unfold z
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp.ne_zero))
  rw [hughesYoungEquation115 hz0, hughesYoungEquation116 hz0,
    hughesYoungEquation117 hz0, hughesYoungEquation118]

/-- The symmetric equation-(118) local factor at a prime dividing `k`. -/
theorem hughesYoungEquation118_localFactor_right
    {h k p : ℕ} (hh : 0 < h) (hk : 0 < k) (hp : p.Prime)
    (hhk : Nat.Coprime h k) (hpk : p ∣ k)
    {a b c : ℂ} (hA : 1 < (a + b).re) (hC : 0 < c.re)
    (hr1 : 1 - (p : ℂ) ^ (-(a + c)) ≠ 0) :
    (∑' e : ℕ, hughesYoungEquation106Coefficient h k a b c (p ^ e)) =
      (((1 - (p : ℂ) ^ (-a)) *
          (1 - (p : ℂ) ^ (-(a + b + c))) +
        (p : ℂ) ^ (-a) * (1 - (p : ℂ) ^ (-b)) *
          (1 - (p : ℂ) ^ (-c)) *
          ((p : ℂ) ^ (-(a + c))) ^ (k.factorization p)) /
        ((1 - (p : ℂ) ^ (-(a + c))) *
          (1 - (p : ℂ) ^ (-(a + b + c))))) := by
  have hA' : 1 < (b + a).re := by simpa [add_comm] using hA
  calc
    (∑' e : ℕ, hughesYoungEquation106Coefficient h k a b c (p ^ e)) =
        ∑' e : ℕ, hughesYoungEquation106Coefficient k h b a c (p ^ e) := by
      apply tsum_congr
      intro e
      exact hughesYoungEquation106Coefficient_swap h k (p ^ e) a b c
    _ = _ := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (hughesYoungEquation118_localFactor_left hk hh hp hhk.symm hpk hA' hC hr1)

end RiemannZeta.GuthMaynard
