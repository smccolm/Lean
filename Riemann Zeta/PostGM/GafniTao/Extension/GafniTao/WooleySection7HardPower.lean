import GafniTao.WooleySection7HardArithmetic

/-!
# The power ledger in the hard branch of Wooley Lemma 7.1

This file converts the real exponent inequality following (7.24) into the
literal product of the real and natural powers occurring in the formalized
mean-value estimate.  The implied Corollary 3.2 constant is deliberately not
absorbed here.
-/

namespace GafniTao

noncomputable section

theorem wooley_section7_hard_power_loss
    {k r a b gamma nu p : ℕ} {epsilon : ℝ}
    (hp : 2 ≤ p) (hr : 1 ≤ r) (hrk : r < k) (hnu : 1 ≤ nu)
    (hgamma : gamma < nu)
    (hBPrime : (nu : ℤ) < wooleySection7BPrimeInt k r a b gamma)
    (hEpsilon :
      (wooleySection7BPrimeNat k r a b gamma : ℝ) * epsilon ^ 2 <
        (nu : ℝ)) :
    (p ^ wooleySection7BPrimeNat k r a b gamma : ℝ) ^ (epsilon ^ 2) *
        (p ^ (wooleySection7NextB k r b -
          (a + wooleySection7HPrime k r a b gamma)) : ℝ) ^
            wooleyTriangular r ≤
      (p : ℝ) ^ (k ^ 2 * nu) := by
  let bp := wooleySection7BPrimeNat k r a b gamma
  let d := wooleySection7NextB k r b -
    (a + wooleySection7HPrime k r a b gamma)
  let R := wooleyTriangular r
  change ((p : ℝ) ^ bp) ^ (epsilon ^ 2) * ((p : ℝ) ^ d) ^ R ≤
    (p : ℝ) ^ (k ^ 2 * nu)
  have hpReal : (1 : ℝ) ≤ p := by exact_mod_cast (hp.trans' (by omega))
  have hexp := wooley_section7_hard_exponent_loss
    hr hrk hnu hgamma hBPrime hEpsilon
  have hpow :
      (p : ℝ) ^ ((bp : ℝ) * epsilon ^ 2 + (R : ℝ) * (d : ℝ)) ≤
        (p : ℝ) ^ ((k ^ 2 * nu : ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hpReal (le_of_lt (by
      dsimp only [bp, d, R]
      norm_num [Nat.cast_sub
        (wooley_section7_a_add_HPrime_le_nextB hr hBPrime)] at hexp ⊢
      linarith))
  calc
    ((p : ℝ) ^ bp) ^ (epsilon ^ 2) * ((p : ℝ) ^ d) ^ R =
        (p : ℝ) ^ ((bp : ℝ) * epsilon ^ 2 + (R : ℝ) * (d : ℝ)) := by
      rw [← Real.rpow_natCast (p : ℝ) bp,
        ← Real.rpow_mul (by positivity),
        ← Real.rpow_natCast (p : ℝ) d,
        ← Real.rpow_natCast ((p : ℝ) ^ (d : ℝ)) R,
        ← Real.rpow_mul (by positivity), ← Real.rpow_add (by positivity)]
      ring_nf
    _ ≤ (p : ℝ) ^ ((k ^ 2 * nu : ℕ) : ℝ) := hpow
    _ = (p : ℝ) ^ (k ^ 2 * nu) := Real.rpow_natCast _ _

/-- A single loss independent of the valuation class.  This is the form
needed before summing (7.23) over all separated residue pairs. -/
theorem wooley_section7_hard_power_loss_zero
    {k r a b gamma nu p : ℕ} {epsilon : ℝ}
    (hp : 2 ≤ p) (hr : 1 ≤ r) (hrk : r < k) (hnu : 1 ≤ nu)
    (hgamma : gamma < nu)
    (hBPrime : (nu : ℤ) < wooleySection7BPrimeInt k r a b gamma)
    (hEpsilonZero :
      (wooleySection7BPrimeNat k r a b 0 : ℝ) * epsilon ^ 2 <
        (nu : ℝ)) :
    (p ^ wooleySection7BPrimeNat k r a b 0 : ℝ) ^ (epsilon ^ 2) *
        (p ^ (wooleySection7NextB k r b -
          (a + wooleySection7HPrime k r a b gamma)) : ℝ) ^
            wooleyTriangular r ≤
      (p : ℝ) ^ (k ^ 2 * nu) := by
  let bp0 := wooleySection7BPrimeNat k r a b 0
  let d := wooleySection7NextB k r b -
    (a + wooleySection7HPrime k r a b gamma)
  let R := wooleyTriangular r
  change ((p : ℝ) ^ bp0) ^ (epsilon ^ 2) * ((p : ℝ) ^ d) ^ R ≤
    (p : ℝ) ^ (k ^ 2 * nu)
  have hpReal : (1 : ℝ) ≤ p := by exact_mod_cast (hp.trans' (by omega))
  have htri := wooley_section7_hard_triangular_loss
    hr hrk hnu hgamma hBPrime
  have hk : 2 ≤ k := by omega
  have hkSq : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by
    nlinarith [show (2 : ℝ) ≤ k by exact_mod_cast hk]
  have hnuPos : (0 : ℝ) < nu := by exact_mod_cast (show 0 < nu by omega)
  have hexp :
      (bp0 : ℝ) * epsilon ^ 2 + (R : ℝ) * (d : ℝ) <
        ((k ^ 2 * nu : ℕ) : ℝ) := by
    dsimp only [bp0, d, R]
    norm_num [Nat.cast_sub
      (wooley_section7_a_add_HPrime_le_nextB hr hBPrime)] at htri ⊢
    nlinarith
  have hpow :
      (p : ℝ) ^ ((bp0 : ℝ) * epsilon ^ 2 + (R : ℝ) * (d : ℝ)) ≤
        (p : ℝ) ^ ((k ^ 2 * nu : ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hpReal hexp.le
  calc
    ((p : ℝ) ^ bp0) ^ (epsilon ^ 2) * ((p : ℝ) ^ d) ^ R =
        (p : ℝ) ^ ((bp0 : ℝ) * epsilon ^ 2 + (R : ℝ) * (d : ℝ)) := by
      rw [← Real.rpow_natCast (p : ℝ) bp0,
        ← Real.rpow_mul (by positivity),
        ← Real.rpow_natCast (p : ℝ) d,
        ← Real.rpow_natCast ((p : ℝ) ^ (d : ℝ)) R,
        ← Real.rpow_mul (by positivity), ← Real.rpow_add (by positivity)]
      ring_nf
    _ ≤ (p : ℝ) ^ ((k ^ 2 * nu : ℕ) : ℝ) := hpow
    _ = (p : ℝ) ^ (k ^ 2 * nu) := Real.rpow_natCast _ _

#print axioms wooley_section7_hard_power_loss
#print axioms wooley_section7_hard_power_loss_zero

end

end GafniTao
