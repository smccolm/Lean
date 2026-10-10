import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Coset.Card

/-! # The actual degree of a prime cyclotomic extension is coprime to that prime -/

namespace Dubon2026

noncomputable section

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The genuine automorphism power map embeds the actual prime cyclotomic Galois group in the original units modulo p, so its original extension degree divides p minus one. -/
theorem cyclotomic_prime_finrank_dvd (p : ℕ) (hp : p.Prime)
    [IsCyclotomicExtension {p} K L] : Module.finrank K L ∣ p - 1 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact p.Prime := ⟨hp⟩
  letI := IsCyclotomicExtension.finiteDimensional {p} K L
  letI := IsCyclotomicExtension.isGalois {p} K L
  have hζ := IsCyclotomicExtension.zeta_spec p K L
  have hcard := Subgroup.card_dvd_of_injective (hζ.autToPow K) (hζ.autToPow_injective K)
  have ht : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  rw [ht, IsGalois.card_aut_eq_finrank] at hcard
  exact hcard

/-- The actual original prime cyclotomic degree is coprime to the original prime. -/
theorem cyclotomic_prime_finrank_coprime (p : ℕ) (hp : p.Prime)
    [IsCyclotomicExtension {p} K L] : (Module.finrank K L).Coprime p := by
  have hpone : p.Coprime (p - 1) := hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hp.one_lt)
      (Nat.sub_lt hp.pos Nat.one_pos))
  exact hpone.symm.coprime_dvd_left (cyclotomic_prime_finrank_dvd (K := K) (L := L) p hp)

end
end Dubon2026
