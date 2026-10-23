import Dubon2026.SourceModularFunctionFieldCoefficients

/-! DUB-17/18 -> original Frobenius/inertia -> good curve reduction ->
separating j coordinate. The already proved simple pole of the actual j
series rules out every power of exponent at least two, in any characteristic.
This avoids constructing a separate Laurent Frobenius coefficient formula. -/
namespace Dubon2026.SourceFunctionField
noncomputable section

theorem pow_ne_jqModC (K : Type*) [Field K] (n : ℕ) (hn : 2 ≤ n)
    (u : LaurentSeries K) : u ^ n ≠ jqModC K := by
  intro h
  have ho := congrArg HahnSeries.order h
  rw [HahnSeries.order_pow, order_jqModC, nsmul_eq_mul] at ho
  have hd : (n : ℤ) ∣ -1 := ⟨u.order, ho.symm⟩
  have hd1 : (n : ℤ) ∣ 1 := (Int.dvd_neg).mp hd
  have he : (n : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) hd1
  omega

theorem pow_ne_jCoeff (N : ℕ) (K : Type*) [Field K] (n : ℕ) (hn : 2 ≤ n)
    (u : modularFunctionFieldCoeff N K) : u ^ n ≠ jCoeff N K := by
  intro h
  apply pow_ne_jqModC K n hn (u : LaurentSeries K)
  exact congrArg Subtype.val h

end
end Dubon2026.SourceFunctionField
