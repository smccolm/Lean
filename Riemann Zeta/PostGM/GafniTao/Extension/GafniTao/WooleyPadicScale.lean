import GafniTao.WooleyPadicConcentration
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# The modulus choice in Wooley Section 12

For a fixed prime `p > k`, this file chooses a depth `h` for which the
residue classes modulo `p^h` contain at most one point of `1, ..., Q`, while
the full modulus `p^(k*h)` is larger than every possible degree-`k`
displacement.  The simultaneous upper bound on `p^h` is what turns the
source `p^(B*delta)` loss into `Q^epsilon`.
-/

namespace GafniTao

noncomputable section

theorem fordVinogradovKappa_pos {k : ℕ} (hk : 1 ≤ k) :
    0 < fordVinogradovKappa k := by
  unfold fordVinogradovKappa
  have hdiv : 2 ≤ k * (k + 1) := by nlinarith
  exact Nat.div_pos hdiv (by omega)

theorem fordVinogradovKappa_one_le {k : ℕ} (hk : 1 ≤ k) :
    1 ≤ fordVinogradovKappa k :=
  fordVinogradovKappa_pos hk

/-- Exact scale package needed to pass from the modular concentration
estimate to the integral Vinogradov system. -/
theorem exists_wooleyPadicScale
    {k p Q B0 : ℕ} (hk : 1 ≤ k) (hp : 2 ≤ p) (hQ : 1 ≤ Q) :
    ∃ h : ℕ,
      B0 ≤ k * h ∧
      Q < p ^ h ∧
      fordVinogradovKappa k * Q ^ k < p ^ (k * h) ∧
      p ^ h ≤ p ^ (B0 + 1) * fordVinogradovKappa k * Q := by
  let s := fordVinogradovKappa k
  have hs : 1 ≤ s := fordVinogradovKappa_one_le hk
  have hM : 1 ≤ s * Q := Nat.mul_pos hs hQ
  obtain ⟨b, hbLower, hbUpper⟩ :=
    exists_nat_pow_near hM (by omega : 1 < p)
  let h := b + 1 + B0
  have hpPos : 0 < p := by omega
  have hbaseStrict : s * Q < p ^ (b + 1) := hbUpper
  have hpowMono : p ^ (b + 1) ≤ p ^ h := by
    exact Nat.pow_le_pow_right hpPos (by dsimp [h]; omega)
  have hQph : Q < p ^ h := by
    calc
      Q ≤ s * Q := by nlinarith
      _ < p ^ (b + 1) := hbaseStrict
      _ ≤ p ^ h := hpowMono
  have hsPow : s ≤ s ^ k := le_self_pow₀ hs (by omega : k ≠ 0)
  have hleft : s * Q ^ k ≤ (s * Q) ^ k := by
    rw [mul_pow]
    exact Nat.mul_le_mul_right (Q ^ k) hsPow
  have hright : (s * Q) ^ k < (p ^ h) ^ k :=
    Nat.pow_lt_pow_left
      (hbaseStrict.trans_le hpowMono) (by omega : k ≠ 0)
  have hmodulus : s * Q ^ k < p ^ (k * h) := by
    calc
      s * Q ^ k ≤ (s * Q) ^ k := hleft
      _ < (p ^ h) ^ k := hright
      _ = p ^ (k * h) := by rw [← pow_mul, Nat.mul_comm]
  have hUpperStep : p ^ (b + 1) ≤ s * Q * p := by
    rw [pow_succ]
    exact Nat.mul_le_mul_right p hbLower
  have hUpper : p ^ h ≤ p ^ (B0 + 1) * s * Q := by
    dsimp [h]
    rw [pow_add]
    calc
      p ^ (b + 1) * p ^ B0 ≤ (s * Q * p) * p ^ B0 :=
        Nat.mul_le_mul_right (p ^ B0) hUpperStep
      _ = p ^ (B0 + 1) * s * Q := by
        rw [pow_succ]
        ring
  refine ⟨h, ?_, hQph, hmodulus, hUpper⟩
  calc
    B0 ≤ h := by dsimp [h]; omega
    _ = 1 * h := by simp
    _ ≤ k * h := Nat.mul_le_mul_right h hk

#print axioms fordVinogradovKappa_pos
#print axioms exists_wooleyPadicScale

end

end GafniTao
