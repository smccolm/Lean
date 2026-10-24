import Dubon2026.SourceModularTamePrimeKernel

/-! DUB-17/18 -> prime-to-characteristic Picard torsion injectivity.
Prime-order kernel triviality gives every torsion order invertible in the
actual residue field by strong induction, with no new geometric input. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "kk" => IsLocalRing.ResidueField A
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "Fb" => modularFunctionFieldCoeff N kk
attribute [local instance] residueModularAlgebra residueConstantsClosed

theorem modular_pic0_eq_zero_of_torsion_of_five_le
    (p : ℕ) [CharP kk p] (hp : 5 ≤ p) (hNk : (N : kk) ≠ 0)
    (R : ConstantReduction A FF Fb)
    (hR : R.toRegularProlongation =
      modularRegularProlongation A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk)
    (m : ℕ) (hm : (m : kk) ≠ 0)
    (z : Pic0 Qbar FF) (hmz : m • z = 0) (hz : R.pic0Map z = 0) : z = 0 := by
  induction m using Nat.strong_induction_on generalizing z with
  | h m ih =>
    by_cases hm1 : m = 1
    · simpa only [hm1, one_nsmul] using hmz
    obtain ⟨q, hq, k, rfl⟩ := Nat.exists_prime_and_dvd hm1
    letI : Fact q.Prime := ⟨hq⟩
    have hqk : (q : kk) ≠ 0 := by
      intro he
      exact hm (by rw [Nat.cast_mul, he, zero_mul])
    have hkk : (k : kk) ≠ 0 := by
      intro he
      exact hm (by rw [Nat.cast_mul, he, mul_zero])
    have hkpos : 0 < k := Nat.pos_of_ne_zero (fun he => hkk (by rw [he, Nat.cast_zero]))
    have hklt : k < q * k := by nlinarith [hq.two_le]
    have hkz : k • z = 0 :=
      modular_pic0_eq_zero_of_prime_torsion_of_five_le A N p hp hNk R hR hqk
        (k • z) (by rw [← mul_nsmul, Nat.mul_comm]; exact hmz)
        (by rw [map_nsmul, hz, nsmul_zero])
    exact ih k hklt hkk z hkz hz

end
end Dubon2026.SourceFunctionField.GaussReduction
