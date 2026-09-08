import RiemannZeta.GuthMaynard.HughesYoungAbsoluteConvergence

open Complex Finset
open scoped BigOperators

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Hughes--Young equations (107)--(118)

This file formalizes the local prime-power calculation in the proof of
Hughes--Young Lemma 6.1.  The variables

* `x = p⁻ᵃ`,
* `y = p⁻ᵇ`,
* `z = p⁻ᶜ`,
* `q = x*y*z = p⁻ᵃ⁻ᵇ⁻ᶜ`, and
* `r = y*z = p⁻ᵇ⁻ᶜ`

are kept algebraic.  This makes every displayed manipulation kernel-checkable
without hiding branch-sensitive complex-power identities.  The later Euler
product theorem supplies these substitutions prime by prime.
-/

/-- The positive-index geometric series in equation (107). -/
noncomputable def hughesYoungEquation107Series (q : ℂ) : ℂ :=
  ∑' j : ℕ, q ^ (j + 1)

/-- Hughes--Young equation (107). -/
theorem hughesYoungEquation107 {q u : ℂ} (hq : ‖q‖ < 1) :
    1 + (1 - u) * hughesYoungEquation107Series q =
      1 + (1 - u) * q / (1 - q) := by
  have hgeom : (∑' j : ℕ, q ^ j) = (1 - q)⁻¹ :=
    tsum_geometric_of_norm_lt_one hq
  unfold hughesYoungEquation107Series
  rw [show (∑' j : ℕ, q ^ (j + 1)) = q * ∑' j : ℕ, q ^ j by
    calc
      (∑' j : ℕ, q ^ (j + 1)) = ∑' j : ℕ, q * q ^ j := by
        apply tsum_congr
        intro j
        rw [pow_succ']
      _ = q * ∑' j : ℕ, q ^ j := tsum_mul_left]
  rw [hgeom]
  simp only [div_eq_mul_inv]
  ring

/-- Hughes--Young equation (108), with `v = u*q = p⁻ᵃ⁻ᵇ`. -/
theorem hughesYoungEquation108 {q u v : ℂ} (hq1 : 1 - q ≠ 0)
    (huq : u * q = v) :
    1 + (1 - u) * q / (1 - q) = (1 - v) / (1 - q) := by
  field_simp
  rw [← huq]
  ring

/-- The equation-(109) prime-power sum.  Its `j`th source term is `r^j`
for `1 ≤ j ≤ hp` and `r^hp*q^(j-hp)` after the valuation of `h` has
been exhausted. -/
noncomputable def hughesYoungEquation109Series
    (hp : ℕ) (q r : ℂ) : ℂ :=
  ∑' n : ℕ,
    if n < hp then r ^ (n + 1) else r ^ hp * q ^ (n + 1 - hp)

/-- The split at the exact prime-adic valuation in equation (110). -/
theorem hughesYoungEquation110 {hp : ℕ} {q r : ℂ}
    (hq : ‖q‖ < 1) :
    hughesYoungEquation109Series hp q r =
      (∑ n ∈ Finset.range hp, r ^ (n + 1)) +
        r ^ hp * (∑' n : ℕ, q ^ (n + 1)) := by
  have htail : Summable (fun n : ℕ => r ^ hp * q ^ (n + 1)) := by
    have hshift : Summable (fun n : ℕ => q ^ (n + 1)) := by
      simpa only [pow_succ'] using
        (summable_geometric_of_norm_lt_one hq).mul_left q
    exact hshift.mul_left (r ^ hp)
  have hall : Summable (fun n : ℕ =>
      if n < hp then r ^ (n + 1) else r ^ hp * q ^ (n + 1 - hp)) := by
    have hshift : Summable (fun n : ℕ =>
        if n + hp < hp then r ^ (n + hp + 1)
          else r ^ hp * q ^ (n + hp + 1 - hp)) := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htail
    exact (summable_nat_add_iff hp).mp hshift
  rw [hughesYoungEquation109Series]
  calc
    (∑' n : ℕ, if n < hp then r ^ (n + 1)
        else r ^ hp * q ^ (n + 1 - hp)) =
        (∑ n ∈ Finset.range hp,
          if n < hp then r ^ (n + 1)
          else r ^ hp * q ^ (n + 1 - hp)) +
        ∑' n : ℕ, if n + hp < hp then r ^ (n + hp + 1)
          else r ^ hp * q ^ (n + hp + 1 - hp) :=
      (hall.sum_add_tsum_nat_add hp).symm
    _ = (∑ n ∈ Finset.range hp, r ^ (n + 1)) +
        ∑' n : ℕ, r ^ hp * q ^ (n + 1) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro n hn
        simp only [mem_range] at hn
        simp [hn]
      · apply tsum_congr
        intro n
        rw [if_neg (by omega)]
        have hsub : n + hp + 1 - hp = n + 1 := by omega
        rw [hsub]
    _ = (∑ n ∈ Finset.range hp, r ^ (n + 1)) +
        r ^ hp * (∑' n : ℕ, q ^ (n + 1)) := by rw [tsum_mul_left]

/-- Finite geometric segment used in equation (111). -/
theorem hughesYoungFiniteGeometricSegment
    {hp : ℕ} {r : ℂ} (hr1 : 1 - r ≠ 0) :
    (∑ n ∈ Finset.range hp, r ^ (n + 1)) =
      r * (1 - r ^ hp) / (1 - r) := by
  rw [show (∑ n ∈ Finset.range hp, r ^ (n + 1)) =
      r * ∑ n ∈ Finset.range hp, r ^ n by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _hn
        rw [pow_succ']]
  rw [geom_sum_eq (Ne.symm (sub_ne_zero.mp hr1)) hp]
  have hrMinus : r - 1 ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hr1))
  have hfrac : (r ^ hp - 1) / (r - 1) =
      (1 - r ^ hp) / (1 - r) := by
    field_simp [hr1, hrMinus]
    ring
  rw [hfrac]
  simp only [div_eq_mul_inv, mul_assoc]

/-- Hughes--Young equation (111). -/
theorem hughesYoungEquation111 {hp : ℕ} {q r : ℂ}
    (hq : ‖q‖ < 1) (hr1 : 1 - r ≠ 0) :
    hughesYoungEquation109Series hp q r =
      r * (1 - r ^ hp) / (1 - r) +
        q * r ^ hp / (1 - q) := by
  rw [hughesYoungEquation110 hq,
    hughesYoungFiniteGeometricSegment hr1]
  have hgeom : (∑' n : ℕ, q ^ n) = (1 - q)⁻¹ :=
    tsum_geometric_of_norm_lt_one hq
  rw [show (∑' n : ℕ, q ^ (n + 1)) = q * ∑' n : ℕ, q ^ n by
    calc
      (∑' n : ℕ, q ^ (n + 1)) = ∑' n : ℕ, q * q ^ n := by
        apply tsum_congr
        intro n
        rw [pow_succ']
      _ = q * ∑' n : ℕ, q ^ n := tsum_mul_left]
  rw [hgeom]
  simp only [div_eq_mul_inv]
  ring

/-- Hughes--Young equation (112), putting the two geometric pieces over a
common denominator. -/
theorem hughesYoungEquation112 {hp : ℕ} {q r : ℂ}
    {x : ℂ} (hq1 : 1 - q ≠ 0) (hr1 : 1 - r ≠ 0) (hxr : x * r = q) :
    r * (1 - r ^ hp) / (1 - r) + q * r ^ hp / (1 - q) =
      (r * ((1 - r ^ hp) * (1 - q) + x * r ^ hp * (1 - r))) /
        ((1 - r) * (1 - q)) := by
  field_simp [hq1, hr1]
  rw [← hxr]
  ring

/-- Hughes--Young equation (113), in the source substitution `q = x*r`. -/
theorem hughesYoungEquation113 {hp : ℕ} {x q r : ℂ}
    (hq1 : 1 - q ≠ 0) (hr1 : 1 - r ≠ 0) (hxr : x * r = q) :
    (r * ((1 - r ^ hp) * (1 - q) + x * r ^ hp * (1 - r))) /
        ((1 - r) * (1 - q)) =
      r * (1 - q - r ^ hp + x * r ^ hp) /
        ((1 - r) * (1 - q)) := by
  field_simp [hq1, hr1]
  rw [← hxr]
  ring

/-- The local factor in equation (114). -/
noncomputable def hughesYoungEquation114LocalFactor
    (hp : ℕ) (x y z : ℂ) : ℂ :=
  let q := x * y * z
  let r := y * z
  1 + (1 - z⁻¹) *
    (r * (1 - q - r ^ hp + x * r ^ hp) / ((1 - r) * (1 - q)))

/-- Hughes--Young equation (114), obtained by inserting equation (113) into
the local factor from equation (109). -/
theorem hughesYoungEquation114 {hp : ℕ} {x y z : ℂ}
    (hq1 : 1 - x * y * z ≠ 0)
    (hr1 : 1 - y * z ≠ 0) :
    hughesYoungEquation114LocalFactor hp x y z =
      (((1 - y * z) * (1 - x * y * z) +
          y * z * (1 - z⁻¹) *
            (1 - x * y * z - (y * z) ^ hp + x * (y * z) ^ hp)) /
        ((1 - y * z) * (1 - x * y * z))) := by
  unfold hughesYoungEquation114LocalFactor
  dsimp only
  let D : ℂ := (1 - y * z) * (1 - x * y * z)
  have hD : D ≠ 0 := mul_ne_zero hr1 hq1
  let A : ℂ := y * z *
    (1 - x * y * z - (y * z) ^ hp + x * (y * z) ^ hp)
  change 1 + (1 - z⁻¹) *
      (A / D) =
    ((1 - y * z) * (1 - x * y * z) +
      y * z * (1 - z⁻¹) *
        (1 - x * y * z - (y * z) ^ hp + x * (y * z) ^ hp)) / D
  rw [eq_div_iff hD]
  rw [add_mul, one_mul, mul_assoc, div_mul_cancel₀ A hD]
  dsimp only [D, A]
  ring

/-- Hughes--Young equation (115). -/
theorem hughesYoungEquation115 {hp : ℕ} {x y z : ℂ}
    (hz : z ≠ 0) :
    (((1 - y * z) * (1 - x * y * z) +
          y * z * (1 - z⁻¹) *
            (1 - x * y * z - (y * z) ^ hp + x * (y * z) ^ hp)) /
        ((1 - y * z) * (1 - x * y * z))) =
      ((1 - x * y * z + y * z *
          (-1 + x * y * z + (1 - z⁻¹) *
            (1 - x * y * z - (y * z) ^ hp + x * (y * z) ^ hp))) /
        ((1 - y * z) * (1 - x * y * z))) := by
  apply congrArg (fun w : ℂ => w / ((1 - y * z) * (1 - x * y * z)))
  field_simp [hz]
  ring

/-- Hughes--Young equation (116). -/
theorem hughesYoungEquation116 {hp : ℕ} {x y z : ℂ}
    (hz : z ≠ 0) :
    ((1 - x * y * z + y * z *
          (-1 + x * y * z + (1 - z⁻¹) *
            (1 - x * y * z - (y * z) ^ hp + x * (y * z) ^ hp))) /
        ((1 - y * z) * (1 - x * y * z))) =
      ((1 - x * y * z + y * z *
          (x * y - z⁻¹ + (1 - z⁻¹) * (y * z) ^ hp * (-1 + x))) /
        ((1 - y * z) * (1 - x * y * z))) := by
  apply congrArg (fun w : ℂ => w / ((1 - y * z) * (1 - x * y * z)))
  field_simp [hz]
  ring

/-- Hughes--Young equation (117). -/
theorem hughesYoungEquation117 {hp : ℕ} {x y z : ℂ}
    (hz : z ≠ 0) :
    ((1 - x * y * z + y * z *
          (x * y - z⁻¹ + (1 - z⁻¹) * (y * z) ^ hp * (-1 + x))) /
        ((1 - y * z) * (1 - x * y * z))) =
      ((1 - y * (1 + x * z - x * y * z) +
          y * (1 - x) * (1 - z) * (y * z) ^ hp) /
        ((1 - y * z) * (1 - x * y * z))) := by
  apply congrArg (fun w : ℂ => w / ((1 - y * z) * (1 - x * y * z)))
  field_simp [hz]
  ring

/-- Hughes--Young equation (118), the final local factor for a prime power
dividing `h`. -/
theorem hughesYoungEquation118 {hp : ℕ} {x y z : ℂ} :
    ((1 - y * (1 + x * z - x * y * z) +
          y * (1 - x) * (1 - z) * (y * z) ^ hp) /
        ((1 - y * z) * (1 - x * y * z))) =
      (((1 - y) * (1 - x * y * z) +
          y * (1 - x) * (1 - z) * (y * z) ^ hp) /
        ((1 - y * z) * (1 - x * y * z))) := by
  apply congrArg (fun w : ℂ => w / ((1 - y * z) * (1 - x * y * z)))
  ring

end RiemannZeta.GuthMaynard
