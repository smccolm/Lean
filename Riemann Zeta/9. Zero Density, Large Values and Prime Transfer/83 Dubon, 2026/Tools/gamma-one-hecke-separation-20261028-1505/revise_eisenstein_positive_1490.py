from pathlib import Path
s=Path(r'E:\Lean\.tmp\dubon83');a=s/'SourceGammaOneEisensteinPositive1488a.lean';b=s/'SourceGammaOneEisensteinPositive1488b.lean'
assert a.exists() and not b.exists() and not a.with_suffix('.lean.txt').exists()
t=a.read_text(encoding='utf-8').replace('π','Real.pi')
t=t.replace('  simp [kappa, Real.pi_ne_zero, Complex.I_ne_zero]', '  unfold kappa\n  apply div_ne_zero\n  · exact pow_ne_zero _ (by norm_num [Real.pi_ne_zero])\n  · exact_mod_cast Nat.factorial_ne_zero 3')
t=t.replace('      ∑\' c : ({c : ℤ | (c : ZMod N) = b} : Set ℤ), F c from rfl, tsum_subtype]\n    rfl', '      ∑\' c : ({c : ℤ | (c : ZMod N) = b} : Set ℤ), F c from rfl, tsum_subtype]\n    exact tsum_congr fun _ => by simp only [Set.indicator_apply, Set.mem_setOf_eq, G]')
t=t.replace('  rw [← neg_mul, ← neg_add, neg_pow, neg_one_pow_eq_one.mpr (by decide : Even (4 : ℕ)), one_mul]', '  congr 1\n  ring')
t=t.replace('    simp only [Int.cast_neg, Int.cast_natCast, neg_eq_iff_eq_neg, integer_row_even]', '    rw [integer_row_even]\n    simp only [Int.cast_neg, Int.cast_natCast, neg_eq_iff_eq_neg]')
b.write_text(t,encoding='utf-8');a.rename(a.with_suffix('.lean.txt'))
