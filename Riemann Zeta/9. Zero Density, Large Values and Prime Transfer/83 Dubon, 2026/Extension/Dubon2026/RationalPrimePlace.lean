import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-! # The genuine finite place of Q corresponding to an ordinary rational prime -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain

/-- The original height-one prime place corresponding to a genuine rational prime. -/
def rationalPrimePlace (p : ℕ) (hp : p.Prime) : HeightOneSpectrum ℤ :=
  Rat.HeightOneSpectrum.primesEquiv.symm ⟨p, hp⟩

/-- The actual prime-place correspondence recovers exactly the original prime integer. -/
theorem rationalPrimePlace_natGenerator (p : ℕ) (hp : p.Prime) :
    Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp) = p :=
  congrArg Subtype.val (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply ⟨p, hp⟩)

/-- Divisibility by the original rational prime is precisely membership in its actual finite-place ideal. -/
theorem rationalPrimePlace_nat_mem_iff (p : ℕ) (hp : p.Prime) (n : ℕ) :
    (n : ℤ) ∈ (rationalPrimePlace p hp).asIdeal ↔ p ∣ n := by
  have he := Rat.HeightOneSpectrum.natGenerator_dvd_iff (rationalPrimePlace p hp) (n := n)
  rw [rationalPrimePlace_natGenerator] at he
  rw [← map_natCast (Rat.IsIntegralClosure.intEquiv ℤ) n,
    Ideal.apply_mem_of_equiv_iff] at he
  exact he.symm

/-- At every genuine finite place, membership of an ordinary integer means divisibility by its original prime generator. -/
theorem finitePlace_nat_mem_iff (v : HeightOneSpectrum ℤ) (n : ℕ) :
    (n : ℤ) ∈ v.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator v ∣ n := by
  have he := Rat.HeightOneSpectrum.natGenerator_dvd_iff v (n := n)
  rw [← map_natCast (Rat.IsIntegralClosure.intEquiv ℤ) n, Ideal.apply_mem_of_equiv_iff] at he
  exact he.symm

/-- The original prime is a local unit at every distinct genuine finite place. -/
theorem rationalPrimePlace_prime_not_mem (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum ℤ)
    (hv : v ≠ rationalPrimePlace p hp) : (p : ℤ) ∉ v.asIdeal := by
  intro hm
  have hd := (finitePlace_nat_mem_iff v p).mp hm
  have he : Rat.HeightOneSpectrum.natGenerator v = p :=
    (Nat.dvd_prime hp).mp hd |>.resolve_left (Rat.HeightOneSpectrum.prime_natGenerator v).ne_one
  apply hv
  apply Rat.HeightOneSpectrum.primesEquiv.injective
  apply Subtype.ext
  exact he.trans (rationalPrimePlace_natGenerator p hp).symm

/-- Different ordinary primes give different actual finite places. -/
theorem rationalPrimePlace_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    rationalPrimePlace p hp ≠ rationalPrimePlace q hq := by
  intro he
  have hh := congrArg Rat.HeightOneSpectrum.natGenerator he
  rw [rationalPrimePlace_natGenerator, rationalPrimePlace_natGenerator] at hh
  exact hpq hh

end
end Dubon2026
