import GafniTao.WooleySection7Easy

/-!
# Arithmetic ledger for the hard branch of Wooley Lemma 7.1

This file records the exact natural modulus `H' = ceil(B'/r)`, equation
(7.13), and the two strict exponent estimates used after equation (7.24).
The analytic and congruence arguments producing (7.24) are deliberately not
encoded as hypotheses of the final source theorem; they are separate later
obligations.
-/

namespace GafniTao

noncomputable section

/-- The conditioning depth `H' = ceil(B'/r)` in the hard branch of Section 7. -/
def wooleySection7HPrime (k r a b gamma : ℕ) : ℕ :=
  wooleySection7BPrimeNat k r a b gamma ⌈/⌉ r

/-- In the hard branch, the natural representative of `B'` satisfies the
literal rearrangement of equation (7.3). -/
theorem wooley_section7_BPrimeNat_add
    {k r a b gamma nu : ℕ}
    (hBPrime : (nu : ℤ) < wooleySection7BPrimeInt k r a b gamma) :
    wooleySection7BPrimeNat k r a b gamma + r * a + (k - r) * gamma =
      (k - r + 1) * b := by
  have hcast := wooleySection7BPrimeNat_cast hBPrime
  have hInt :
      (wooleySection7BPrimeNat k r a b gamma : ℤ) +
          (r * a : ℕ) + ((k - r) * gamma : ℕ) =
        ((k - r + 1) * b : ℕ) := by
    rw [hcast]
    simp only [wooleySection7BPrimeInt, Nat.cast_add, Nat.cast_mul]
    omega
  exact_mod_cast hInt

theorem wooley_section7_BPrimeNat_pos
    {k r a b gamma nu : ℕ}
    (hBPrime : (nu : ℤ) < wooleySection7BPrimeInt k r a b gamma) :
    0 < wooleySection7BPrimeNat k r a b gamma := by
  have hpos := wooley_section7_BPrimeInt_pos_toNat hBPrime
  have hcast := wooleySection7BPrimeNat_cast hBPrime
  exact_mod_cast (show (0 : ℤ) <
    (wooleySection7BPrimeNat k r a b gamma : ℤ) by simpa [hcast] using hpos)

theorem wooley_section7_BPrimeNat_le_zero
    {k r a b gamma : ℕ} :
    wooleySection7BPrimeNat k r a b gamma ≤
      wooleySection7BPrimeNat k r a b 0 := by
  unfold wooleySection7BPrimeNat wooleySection7BPrimeInt
  apply Int.toNat_le_toNat
  omega

/-- The defining lower ceiling inequality `B' ≤ r H'`. -/
theorem wooley_section7_BPrime_le_mul_HPrime
    {k r a b gamma : ℕ} (hr : 1 ≤ r) :
    wooleySection7BPrimeNat k r a b gamma ≤
      r * wooleySection7HPrime k r a b gamma := by
  exact le_smul_ceilDiv (by omega : 0 < r)

/-- The refinement depth in (7.22) is ordered correctly:
`a + H' ≤ b'`.  This follows from the two literal ceiling definitions and
the signed identity (7.3); no real-valued rounding argument is used. -/
theorem wooley_section7_a_add_HPrime_le_nextB
    {k r a b gamma nu : ℕ}
    (hr : 1 ≤ r)
    (hBPrime : (nu : ℤ) < wooleySection7BPrimeInt k r a b gamma) :
    a + wooleySection7HPrime k r a b gamma ≤
      wooleySection7NextB k r b := by
  let bp := wooleySection7BPrimeNat k r a b gamma
  let hp := wooleySection7HPrime k r a b gamma
  let nb := wooleySection7NextB k r b
  let n := (k - r + 1) * b
  have hid := wooley_section7_BPrimeNat_add hBPrime
  change bp + r * a + (k - r) * gamma = n at hid
  have hncover : n ≤ r * nb := by
    dsimp only [n, nb, wooleySection7NextB]
    exact le_smul_ceilDiv (by omega : 0 < r)
  have hra : r * a ≤ r * nb := by
    omega
  have ha : a ≤ nb := by
    exact Nat.le_of_mul_le_mul_left hra (by omega)
  have hbp : bp ≤ r * (nb - a) := by
    rw [Nat.mul_sub_left_distrib]
    omega
  have hH : hp ≤ nb - a := by
    dsimp only [hp, wooleySection7HPrime]
    exact (ceilDiv_le_iff_le_mul (by omega : 0 < r)).2 hbp
  change a + hp ≤ nb
  omega

/-- Equation (7.13), with all ceiling losses explicit. -/
theorem wooley_equation_7_13
    {k r a b gamma nu : ℕ}
    (hr : 1 ≤ r)
    (hBPrime : (nu : ℤ) < wooleySection7BPrimeInt k r a b gamma) :
    (wooleySection7NextB k r b : ℝ) -
        (wooleySection7HPrime k r a b gamma : ℝ) ≤
      (a : ℝ) + 1 + (k - r : ℕ) * (gamma : ℝ) / (r : ℝ) := by
  let bp := wooleySection7BPrimeNat k r a b gamma
  let hp := wooleySection7HPrime k r a b gamma
  let n := (k - r + 1) * b
  have hceilNat := wooley_section7_nextB_mul_upper
    (k := k) (r := r) (b := b) hr
  have hHNat := wooley_section7_BPrime_le_mul_HPrime
    (k := k) (r := r) (a := a) (b := b) (gamma := gamma) hr
  have hidNat := wooley_section7_BPrimeNat_add hBPrime
  have hceil :
      (r : ℝ) * (wooleySection7NextB k r b : ℝ) ≤
        (n : ℝ) + (r : ℝ) := by
    exact_mod_cast hceilNat
  have hH : (bp : ℝ) ≤ (r : ℝ) * (hp : ℝ) := by
    exact_mod_cast hHNat
  have hid :
      (bp : ℝ) + (r : ℝ) * (a : ℝ) +
          ((k - r : ℕ) : ℝ) * (gamma : ℝ) = (n : ℝ) := by
    exact_mod_cast hidNat
  have hrPos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  dsimp [bp, hp] at hH ⊢
  dsimp [n] at hceil hid
  have hmul :
      (r : ℝ) *
          ((wooleySection7NextB k r b : ℝ) -
            (wooleySection7HPrime k r a b gamma : ℝ) - (a : ℝ) - 1) ≤
        ((k - r : ℕ) : ℝ) * (gamma : ℝ) := by
    nlinarith
  have hdiv :
      (wooleySection7NextB k r b : ℝ) -
          (wooleySection7HPrime k r a b gamma : ℝ) - (a : ℝ) - 1 ≤
        ((k - r : ℕ) : ℝ) * (gamma : ℝ) / (r : ℝ) := by
    apply (le_div_iff₀ hrPos).2
    simpa [mul_comm] using hmul
  linarith

/-- The triangular-number contribution following (7.13) is strictly less
than `k^2 nu / 2`, exactly as in the source. -/
theorem wooley_section7_hard_triangular_loss
    {k r a b gamma nu : ℕ}
    (hr : 1 ≤ r) (hrk : r < k) (hnu : 1 ≤ nu)
    (hgamma : gamma < nu)
    (hBPrime : (nu : ℤ) < wooleySection7BPrimeInt k r a b gamma) :
    (wooleyTriangular r : ℝ) *
        ((wooleySection7NextB k r b : ℝ) - (a : ℝ) -
          (wooleySection7HPrime k r a b gamma : ℝ)) <
      (k : ℝ) ^ 2 * (nu : ℝ) / 2 := by
  have h713 := wooley_equation_7_13 hr hBPrime
  have hRtwoNat : 2 * wooleyTriangular r ≤ r * (r + 1) := by
    simp only [wooleyTriangular]
    exact Nat.mul_div_le _ _
  have hRtwo : 2 * (wooleyTriangular r : ℝ) ≤
      (r : ℝ) * ((r : ℝ) + 1) := by
    exact_mod_cast hRtwoNat
  have hkrPos : 0 < k - r := Nat.sub_pos_of_lt hrk
  have htailStrict : r + (k - r) * gamma < k * nu := by
    have hmul : (k - r) * gamma < (k - r) * nu :=
      Nat.mul_lt_mul_of_pos_left hgamma hkrPos
    have hrnu : r ≤ r * nu := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left r hnu
    calc
      r + (k - r) * gamma < r + (k - r) * nu :=
        Nat.add_lt_add_left hmul r
      _ ≤ r * nu + (k - r) * nu := Nat.add_le_add_right hrnu _
      _ = k * nu := by
        rw [← Nat.add_mul, Nat.add_sub_of_le hrk.le]
  have hprodNat :
      (r + 1) * (r + (k - r) * gamma) < k * (k * nu) := by
    have hr1 : r + 1 ≤ k := by omega
    calc
      (r + 1) * (r + (k - r) * gamma) ≤
          k * (r + (k - r) * gamma) :=
        Nat.mul_le_mul_right _ hr1
      _ < k * (k * nu) :=
        Nat.mul_lt_mul_of_pos_left htailStrict (by omega)
  have hprod :
      ((r : ℝ) + 1) *
          ((r : ℝ) + ((k - r : ℕ) : ℝ) * (gamma : ℝ)) <
        (k : ℝ) * ((k : ℝ) * (nu : ℝ)) := by
    exact_mod_cast hprodNat
  let d : ℝ :=
    (wooleySection7NextB k r b : ℝ) - (a : ℝ) -
      (wooleySection7HPrime k r a b gamma : ℝ)
  have hd : d ≤ 1 + ((k - r : ℕ) : ℝ) * (gamma : ℝ) / (r : ℝ) := by
    dsimp [d]
    linarith
  have hR : (0 : ℝ) ≤ wooleyTriangular r := by positivity
  have hrPos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  change (wooleyTriangular r : ℝ) * d < (k : ℝ) ^ 2 * (nu : ℝ) / 2
  by_cases hdNonneg : 0 ≤ d
  · have hmul := mul_le_mul hRtwo hd hdNonneg
        (by positivity : (0 : ℝ) ≤ (r : ℝ) * ((r : ℝ) + 1))
    have heq :
        (r : ℝ) * ((r : ℝ) + 1) *
            (1 + ((k - r : ℕ) : ℝ) * (gamma : ℝ) / (r : ℝ)) =
          ((r : ℝ) + 1) *
            ((r : ℝ) + ((k - r : ℕ) : ℝ) * (gamma : ℝ)) := by
      field_simp
    rw [heq] at hmul
    nlinarith
  · have hdNeg : d < 0 := lt_of_not_ge hdNonneg
    have hkPos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hnuPos : (0 : ℝ) < nu := by exact_mod_cast (show 0 < nu by omega)
    have : (wooleyTriangular r : ℝ) * d ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hR hdNeg.le
    exact this.trans_lt (by positivity)

/-- The complete numerical exponent ledger after (7.24).  The hypothesis
`B' * epsilon^2 < nu` is the precise output required from the Section 6
parameter hierarchy; no `epsilon` loss is hidden in this lemma. -/
theorem wooley_section7_hard_exponent_loss
    {k r a b gamma nu : ℕ} {epsilon : ℝ}
    (hr : 1 ≤ r) (hrk : r < k) (hnu : 1 ≤ nu)
    (hgamma : gamma < nu)
    (hBPrime : (nu : ℤ) < wooleySection7BPrimeInt k r a b gamma)
    (hEpsilon :
      (wooleySection7BPrimeNat k r a b gamma : ℝ) * epsilon ^ 2 <
        (nu : ℝ)) :
    (wooleySection7BPrimeNat k r a b gamma : ℝ) * epsilon ^ 2 +
        (wooleyTriangular r : ℝ) *
          ((wooleySection7NextB k r b : ℝ) - (a : ℝ) -
            (wooleySection7HPrime k r a b gamma : ℝ)) <
      (k : ℝ) ^ 2 * (nu : ℝ) := by
  have htri := wooley_section7_hard_triangular_loss
    hr hrk hnu hgamma hBPrime
  have hk : 2 ≤ k := by omega
  have hnuPos : (0 : ℝ) < nu := by exact_mod_cast (show 0 < nu by omega)
  have hkSq : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by
    nlinarith [show (2 : ℝ) ≤ k by exact_mod_cast hk]
  nlinarith

#print axioms wooley_section7_BPrimeNat_add
#print axioms wooley_section7_BPrimeNat_pos
#print axioms wooley_section7_BPrimeNat_le_zero
#print axioms wooley_section7_BPrime_le_mul_HPrime
#print axioms wooley_section7_a_add_HPrime_le_nextB
#print axioms wooley_equation_7_13
#print axioms wooley_section7_hard_triangular_loss
#print axioms wooley_section7_hard_exponent_loss

end

end GafniTao
