from pathlib import Path
s=Path(__file__).parent
f=s/'SourceGammaOneDiamondQuotientLocal1449b.lean'
c=f.read_text(encoding='utf-8')
marker='variable (Q p n w : ℕ) [NeZero Q] [Fact p.Prime]'
helper='''private theorem coefficient_prime_ne_zero {k : Type*} [Field k]
    (Q p n q : ℕ) (hq : q.Prime) [CharP k q]
    (hcop : q.Coprime (Q * p ^ (n + 1))) : (p : k) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff k q]
  intro h
  exact (hq.coprime_iff_not_dvd.mp hcop)
    (dvd_mul_of_dvd_right (h.trans (dvd_pow_self p (Nat.succ_ne_zero n))) Q)

'''
assert marker in c
c=c.replace(marker,helper+marker)
start=c.index('  have hp : (p : kk) ≠ 0 := by')
stop=c.index('  obtain ⟨φ, hφ⟩',start)
c=c[:start]+'''  have hp : (p : kk) ≠ 0 :=
    coefficient_prime_ne_zero Q p n ell.val ell.property.1 ell.property.2
'''+c[stop:]
t=s/'SourceGammaOneDiamondQuotientLocal1449c.lean';assert not t.exists()
t.write_text(c,encoding='utf-8')
archive=f.with_suffix('.lean.txt');assert not archive.exists()
f.rename(archive)
print('Rejected warning-producing b; isolated residue-prime arithmetic in a narrow proved helper.')
