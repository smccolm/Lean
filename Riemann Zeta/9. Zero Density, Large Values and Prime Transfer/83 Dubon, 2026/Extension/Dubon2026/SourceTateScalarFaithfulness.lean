import Dubon2026.SourceTateModule

/-! DUB-17/18 -> Frobenius determinant from the original alternating pairing.
Nonzero p-adic scalars cannot annihilate a nonzero Tate sequence. This gives
the cancellation needed by the determinant argument without choosing a basis
for the Tate module of roots of unity. The proof reuses native scalar coordinates. -/
namespace Dubon2026.TateModule
noncomputable section
variable (p : ℕ) [Fact p.Prime] {M : Type*} [AddCommGroup M]

theorem eq_zero_of_prime_smul_eq_zero (x : TateModule p M) (hx : (p : ℤ_[p]) • x = 0) :
    x = 0 := by
  apply Subtype.ext
  funext k
  have h := congrArg (fun z : TateModule p M => (z : ℕ → M) (k + 1)) hx
  dsimp only at h
  rw [natCast_padicInt_smul_apply, compat, coe_zero, Pi.zero_apply] at h
  exact h

theorem eq_zero_of_prime_pow_smul_eq_zero (n : ℕ) (x : TateModule p M)
    (hx : (p : ℤ_[p]) ^ n • x = 0) : x = 0 := by
  induction n with
  | zero => simpa only [pow_zero, one_smul] using hx
  | succ n ih =>
    rw [pow_succ', mul_smul] at hx
    exact ih (eq_zero_of_prime_smul_eq_zero p _ hx)

theorem eq_zero_of_nonzero_scalar_smul_eq_zero (a : ℤ_[p]) (ha : a ≠ 0)
    (x : TateModule p M) (hx : a • x = 0) : x = 0 := by
  rw [PadicInt.unitCoeff_spec ha, mul_smul] at hx
  have h := (PadicInt.unitCoeff ha).isUnit.smul_left_cancel
    (x := (p : ℤ_[p]) ^ a.valuation • x) (y := (0 : TateModule p M))
  rw [smul_zero] at h
  exact eq_zero_of_prime_pow_smul_eq_zero p a.valuation x (h.mp hx)

end
end Dubon2026.TateModule
