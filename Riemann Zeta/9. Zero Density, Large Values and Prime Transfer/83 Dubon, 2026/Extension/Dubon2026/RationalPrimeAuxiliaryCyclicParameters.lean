import Dubon2026.AuxiliaryFamilyCyclicParameters
import Dubon2026.RationalPrimeTameCoefficientQuotient

/-! The actual coefficient-primary tame quotients are finite cyclic,
so their character augmentation has one generator per coordinate and
per selected prime. These are the literal arithmetic groups used in
the original-support comparison, not replacement cyclic groups. -/

namespace Dubon2026
noncomputable section

/-- The original tame coefficient quotient is cyclic by the actual
quotient map from the multiplicative group of the prime residue field. -/
theorem rationalPrimeTameCoefficientQuotient_isCyclic
    (p q : ℕ) [Fact p.Prime] : IsCyclic (RationalPrimeTameCoefficientQuotient p q) :=
  isCyclic_of_surjective (QuotientGroup.mk' (rationalPrimeTameCoefficientKernel p q))
    (QuotientGroup.mk'_surjective (rationalPrimeTameCoefficientKernel p q))

/-- The augmentation for the genuine selected prime quotients is the
span of precisely one character difference per prime and coordinate.
The required cyclic generators are constructed, not supplied. -/
theorem rationalPrimeAuxiliaryFamily_exists_augmentation_generators
    (O : Type*) [CommRing O] {ι A : Type*}
    [Fintype ι] [CommRing A] [Algebra O A]
    (Q : Finset Nat.Primes) (q : ℕ)
    (κ : ∀ p : Q, RationalPrimeTameCoefficientQuotient p.val.val q →* (ι → A)ˣ) :
    ∃ g : ∀ p : Q, RationalPrimeTameCoefficientQuotient p.val.val q,
      (∀ p d, ∃ n : ℕ, g p ^ n = d) ∧
      auxiliaryFamilyAugmentationIdeal O κ =
        Ideal.span (Set.range fun pi : Q × ι => ((κ pi.1 (g pi.1)).val pi.2) - 1) := by
  letI (p : Q) : Fact p.val.val.Prime := ⟨p.val.property⟩
  letI (p : Q) : IsCyclic (RationalPrimeTameCoefficientQuotient p.val.val q) :=
    rationalPrimeTameCoefficientQuotient_isCyclic p.val.val q
  exact auxiliaryFamilyAugmentationIdeal_exists_cyclic_generators O κ

end
end Dubon2026
