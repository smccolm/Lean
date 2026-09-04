import GafniTao.WooleyPolynomialLemma63
import GafniTao.WooleyIterationArithmetic

/-!
# Arithmetic ledger for Wooley Section 7

The source parameter `B'` is signed.  Keeping it in `ℤ` avoids silently
truncating the easy branch at zero.  The natural depth used in the hard branch
is introduced only after positivity has been proved.
-/

namespace GafniTao

noncomputable section

/-- Equation (7.2). -/
def wooleySection7NextB (k r b : ℕ) : ℕ :=
  ((k - r + 1) * b) ⌈/⌉ r

/-- Equation (7.3), as the signed integer occurring in the source. -/
def wooleySection7BPrimeInt (k r a b gamma : ℕ) : ℤ :=
  (((k - r + 1) * b : ℕ) : ℤ) - ((r * a : ℕ) : ℤ) -
    (((k - r) * gamma : ℕ) : ℤ)

theorem wooleySection7NextB_eq_wooleyNextB
    (k r b : ℕ) :
    wooleySection7NextB k r b = wooleyNextB k r b := rfl

theorem wooley_section7_nextB_mul_upper
    {k r b : ℕ} (hr : 1 ≤ r) :
    r * wooleySection7NextB k r b ≤ (k - r + 1) * b + r := by
  have hrPos : 0 < r := by omega
  let n := (k - r + 1) * b
  have hdiv : r * ((n + r - 1) / r) ≤ n + r - 1 := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (n + r - 1) r
  have hle : n + r - 1 ≤ n + r := Nat.sub_le _ _
  simpa [wooleySection7NextB, Nat.ceilDiv_eq_add_pred_div, n] using
    hdiv.trans hle

/-- Equation (7.4), including the ceiling loss, derived from the literal
signed inequality `B' ≤ nu`. -/
theorem wooley_equation_7_4
    {k r a b gamma nu : ℕ}
    (hr : 1 ≤ r) (hrk : r ≤ k)
    (hgamma : gamma < nu)
    (hBPrime : wooleySection7BPrimeInt k r a b gamma ≤ (nu : ℤ)) :
    (wooleySection7NextB k r b : ℝ) - (a : ℝ) ≤
      1 + (k : ℝ) * (nu : ℝ) / (r : ℝ) := by
  let n : ℕ := (k - r + 1) * b
  have hceilNat := wooley_section7_nextB_mul_upper
    (k := k) (r := r) (b := b) hr
  have hceil :
      (r : ℝ) * (wooleySection7NextB k r b : ℝ) ≤
        (n : ℝ) + (r : ℝ) := by
    exact_mod_cast hceilNat
  have hB :
      (n : ℝ) - (r : ℝ) * (a : ℝ) -
          ((k - r : ℕ) : ℝ) * (gamma : ℝ) ≤ (nu : ℝ) := by
    have hBInt :
        (n : ℤ) - (r : ℤ) * (a : ℤ) -
            ((k - r : ℕ) : ℤ) * (gamma : ℤ) ≤ (nu : ℤ) := by
      simpa [wooleySection7BPrimeInt, n, Nat.cast_mul] using hBPrime
    exact_mod_cast hBInt
  have hkr : (k - r : ℕ) ≤ k := Nat.sub_le _ _
  have hgammaLe : gamma ≤ nu := hgamma.le
  have hprodNat : (k - r) * gamma ≤ (k - r) * nu :=
    Nat.mul_le_mul_left _ hgammaLe
  have hkr1 : k - r + 1 ≤ k := by omega
  have htailNat : (k - r) * gamma + nu ≤ k * nu := by
    calc
      (k - r) * gamma + nu ≤ (k - r) * nu + nu :=
        Nat.add_le_add_right hprodNat nu
      _ = (k - r + 1) * nu := by rw [Nat.add_mul, one_mul]
      _ ≤ k * nu := Nat.mul_le_mul_right nu hkr1
  have htail :
      ((k - r : ℕ) : ℝ) * (gamma : ℝ) + (nu : ℝ) ≤
        (k : ℝ) * (nu : ℝ) := by
    exact_mod_cast htailNat
  have hrPos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hcombined :
      (r : ℝ) *
          ((wooleySection7NextB k r b : ℝ) - (a : ℝ)) ≤
        (r : ℝ) + (k : ℝ) * (nu : ℝ) := by
    nlinarith
  have hdivided :
      (wooleySection7NextB k r b : ℝ) - (a : ℝ) ≤
        ((r : ℝ) + (k : ℝ) * (nu : ℝ)) / (r : ℝ) :=
    (le_div_iff₀ hrPos).2 (by simpa [mul_comm] using hcombined)
  calc
    (wooleySection7NextB k r b : ℝ) - (a : ℝ) ≤
        ((r : ℝ) + (k : ℝ) * (nu : ℝ)) / (r : ℝ) := hdivided
    _ = 1 + (k : ℝ) * (nu : ℝ) / (r : ℝ) := by
      field_simp

theorem wooley_section7_BPrimeInt_pos_toNat
    {k r a b gamma nu : ℕ}
    (hBPrime : (nu : ℤ) < wooleySection7BPrimeInt k r a b gamma) :
    0 < wooleySection7BPrimeInt k r a b gamma := by
  exact lt_of_le_of_lt (Int.natCast_nonneg nu) hBPrime

/-- The natural modulus depth used after the hard-branch assumption (7.5). -/
def wooleySection7BPrimeNat (k r a b gamma : ℕ) : ℕ :=
  (wooleySection7BPrimeInt k r a b gamma).toNat

theorem wooleySection7BPrimeNat_cast
    {k r a b gamma nu : ℕ}
    (hBPrime : (nu : ℤ) < wooleySection7BPrimeInt k r a b gamma) :
    (wooleySection7BPrimeNat k r a b gamma : ℤ) =
      wooleySection7BPrimeInt k r a b gamma := by
  exact Int.toNat_of_nonneg
    (wooley_section7_BPrimeInt_pos_toNat hBPrime).le

#print axioms wooley_section7_nextB_mul_upper
#print axioms wooley_equation_7_4
#print axioms wooleySection7BPrimeNat_cast

end

end GafniTao
