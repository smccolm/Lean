import Dubon2026.CyclicParameterFiniteQuotient
import Dubon2026.RationalPrimeAuxiliaryCyclicParameters

/-! The selected congruence condition constructs the finite parameter
character of the original tame quotient. Its prime-power order and
generator compatibility are derived from the literal arithmetic group. -/

namespace Dubon2026
noncomputable section

/-- The same selected prime quotient maps to any prescribed residue-one
parameter in an ideal-power quotient at every smaller level. -/
def rationalPrimeParameterQuotientCharacter
    {R : Type*} [CommRing R] (I : Ideal R)
    (p q level n : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hqI : (q : R) ∈ I) (hlevel : n ≤ level)
    (hmod : p ≡ 1 [MOD q ^ level])
    (g : RationalPrimeTameCoefficientQuotient p q)
    (hg : ∀ d, ∃ j : ℕ, g ^ j = d)
    (x : R) (hx : x - 1 ∈ I) :
    RationalPrimeTameCoefficientQuotient p q →* (R ⧸ I ^ n)ˣ := by
  have hgen : ∀ d, d ∈ Subgroup.zpowers g := by
    intro d
    obtain ⟨j, hj⟩ := hg d
    exact ⟨(j : ℤ), by simpa only [zpow_natCast] using hj⟩
  have htop : Subgroup.zpowers g = ⊤ := top_unique (fun d _ => hgen d)
  have hd : q ^ n ∣ orderOf g := by
    rw [orderOf_eq_card_of_zpowers_eq_top htop]
    exact (pow_dvd_pow q hlevel).trans
      (rationalPrimeTameCoefficientQuotient_card_dvd_of_congruence p q level hmod)
  exact cyclicParameterQuotientCharacter I (Fact.out : q.Prime) hqI g hgen x hx n hd

/-- Generator evaluation of the actual selected-prime character. -/
theorem rationalPrimeParameterQuotientCharacter_generator
    {R : Type*} [CommRing R] (I : Ideal R)
    (p q level n : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hqI : (q : R) ∈ I) (hlevel : n ≤ level)
    (hmod : p ≡ 1 [MOD q ^ level])
    (g : RationalPrimeTameCoefficientQuotient p q)
    (hg : ∀ d, ∃ j : ℕ, g ^ j = d)
    (x : R) (hx : x - 1 ∈ I) :
    (rationalPrimeParameterQuotientCharacter I p q level n hqI hlevel hmod g hg x hx g).val =
      Ideal.Quotient.mk (I ^ n) x := by
  unfold rationalPrimeParameterQuotientCharacter
  exact cyclicParameterQuotientCharacter_generator ..

end
end Dubon2026
