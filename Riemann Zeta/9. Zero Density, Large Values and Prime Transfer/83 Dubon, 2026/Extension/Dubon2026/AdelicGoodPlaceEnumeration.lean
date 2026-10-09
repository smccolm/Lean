import Dubon2026.AdelicDistinctPlaceCoefficients
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Infinite

/-! # An actual increasing enumeration of all good finite places -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain

variable (N : ℕ) [NeZero N]

/-- There are infinitely many genuine primes coprime to the original positive level. -/
theorem goodAdelicPrimes_infinite : {p : ℕ | p.Prime ∧ p.Coprime N}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨p, hpbound, hp⟩ := Nat.exists_infinite_primes (max a N + 1)
  have hN : N < p := lt_of_lt_of_le (Nat.lt_succ_of_le (le_max_right a N)) hpbound
  have ha : a < p := lt_of_lt_of_le (Nat.lt_succ_of_le (le_max_left a N)) hpbound
  refine ⟨p, ⟨hp, hp.coprime_iff_not_dvd.mpr ?_⟩, ha⟩
  intro hd
  exact (not_le_of_gt hN) (Nat.le_of_dvd (NeZero.pos N) hd)

/-- The actual nth ordinary prime coprime to the original level. -/
def goodAdelicPrime (i : ℕ) : ℕ := Nat.nth (fun p => p.Prime ∧ p.Coprime N) i

/-- Every enumerated integer is genuinely prime and coprime to the original level. -/
theorem goodAdelicPrime_spec (i : ℕ) : (goodAdelicPrime N i).Prime ∧ (goodAdelicPrime N i).Coprime N :=
  Nat.nth_mem_of_infinite (goodAdelicPrimes_infinite N) i

/-- The actual good-prime enumeration is strictly increasing. -/
theorem goodAdelicPrime_strictMono : StrictMono (goodAdelicPrime N) :=
  Nat.nth_strictMono (goodAdelicPrimes_infinite N)

/-- The actual finite place of the nth genuine good prime. -/
def goodAdelicPlace (i : ℕ) : HeightOneSpectrum ℤ :=
  rationalPrimePlace (goodAdelicPrime N i) (goodAdelicPrime_spec N i).1

/-- Every enumerated place is good for the original level. -/
theorem goodAdelicPlace_good (i : ℕ) : IsGoodAdelicPlace N (goodAdelicPlace N i) :=
  ⟨goodAdelicPrime N i, (goodAdelicPrime_spec N i).1, (goodAdelicPrime_spec N i).2, rfl⟩

/-- Distinct indices yield distinct actual finite places. -/
theorem goodAdelicPlace_injective : Function.Injective (goodAdelicPlace N) := by
  intro a b he
  apply (goodAdelicPrime_strictMono N).injective
  have h := congrArg Rat.HeightOneSpectrum.natGenerator he
  simpa only [goodAdelicPlace, rationalPrimePlace_natGenerator] using h

/-- Every actual good finite place occurs in the genuine enumeration. -/
theorem goodAdelicPlace_surjective_good (v : HeightOneSpectrum ℤ) (hv : IsGoodAdelicPlace N v) :
    ∃ i, goodAdelicPlace N i = v := by
  obtain ⟨p, hp, hc, rfl⟩ := hv
  obtain ⟨i, hi⟩ := (Nat.range_nth_of_infinite (goodAdelicPrimes_infinite N)).superset ⟨hp, hc⟩
  refine ⟨i, ?_⟩
  apply Rat.HeightOneSpectrum.primesEquiv.injective
  apply Subtype.ext
  change Rat.HeightOneSpectrum.natGenerator (goodAdelicPlace N i) =
    Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)
  simpa only [goodAdelicPlace, rationalPrimePlace_natGenerator, goodAdelicPrime] using hi

/-- A genuine finite initial family of all good places, retaining its original prime order. -/
def goodAdelicPlaceInitial (n : ℕ) (i : Fin n) : HeightOneSpectrum ℤ := goodAdelicPlace N i.val

/-- Every actual finite initial family has pairwise distinct places. -/
theorem goodAdelicPlaceInitial_injective (n : ℕ) : Function.Injective (goodAdelicPlaceInitial N n) :=
  (goodAdelicPlace_injective N).comp Fin.val_injective

/-- Every actual initial-family coordinate is a genuine good place. -/
theorem goodAdelicPlaceInitial_good (n : ℕ) (i : Fin n) : IsGoodAdelicPlace N (goodAdelicPlaceInitial N n i) :=
  goodAdelicPlace_good N i.val

/-- Extending the genuine initial family retains every earlier place literally. -/
theorem goodAdelicPlaceInitial_castSucc (n : ℕ) (i : Fin n) :
    goodAdelicPlaceInitial N (n + 1) i.castSucc = goodAdelicPlaceInitial N n i := rfl

/-- A genuine initial family contains every good place in any given finite exceptional set. -/
theorem goodAdelicPlaceInitial_covers_finset (S : Finset (HeightOneSpectrum ℤ)) :
    ∃ n, ∀ v ∈ S, IsGoodAdelicPlace N v → ∃ i : Fin n, goodAdelicPlaceInitial N n i = v := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, fun _ h => False.elim (Finset.notMem_empty _ h)⟩
  | @insert w S _ ih =>
    obtain ⟨n, hn⟩ := ih
    by_cases hw : IsGoodAdelicPlace N w
    · obtain ⟨i, hi⟩ := goodAdelicPlace_surjective_good N w hw
      refine ⟨max n (i + 1), ?_⟩
      intro v hv hgood
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact ⟨⟨i, lt_of_lt_of_le (Nat.lt_succ_self i) (le_max_right n (i + 1))⟩, hi⟩
      · obtain ⟨j, hj⟩ := hn v hv hgood
        exact ⟨⟨j.val, lt_of_lt_of_le j.isLt (le_max_left n (i + 1))⟩, hj⟩
    · refine ⟨n, ?_⟩
      intro v hv hgood
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact False.elim (hw hgood)
      · exact hn v hv hgood

end
end Dubon2026
