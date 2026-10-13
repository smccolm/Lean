import Dubon2026.OriginalFinitePowerIndex
import Mathlib.NumberTheory.NumberField.ProductFormula

/-! # Product of the original finite-place power indices

The existing original ideal factorization and scalar ideal norm evaluate all
finite-place defects at once. This supplies the finite part of the supported
power-quotient cardinality needed for DUB-17's norm-index upper bound.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K : Type) [Field K] [NumberField K]

/-- A support containing the actual primes dividing the exponent captures
exactly the full scalar ideal norm in the original finite-place product. -/
theorem originalFinitePowerDefect_product (n : ℕ) (hn : n ≠ 0)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    (∏ v ∈ S, Ideal.absNorm (v.maxPowDividing (Ideal.span {(n : 𝓞 K)}))) =
      n ^ Module.finrank ℚ K := by
  let I : Ideal (𝓞 K) := Ideal.span {(n : 𝓞 K)}
  have hI : I ≠ ⊥ := Submodule.span_singleton_eq_bot.mp.mt (Nat.cast_ne_zero.mpr hn)
  have hp : (∏ᶠ v : HeightOneSpectrum (𝓞 K), v.maxPowDividing I) =
      ∏ v ∈ S, v.maxPowDividing I := by
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hv
    apply hS v
    by_contra hnot
    have hd : ¬v.asIdeal ∣ I := by simpa only [I, Ideal.dvd_span_singleton] using hnot
    have he : v.maxPowDividing I = 1 := by
      rw [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity hI,
        multiplicity_eq_zero.mpr hd, pow_zero]
    exact hv he
  rw [← map_prod]
  change Ideal.absNorm (∏ v ∈ S, v.maxPowDividing I) = _
  rw [← hp, Ideal.finprod_heightOneSpectrum_factorization hI,
    Ideal.absNorm_span_natCast, RingOfIntegers.rank]

/-- The actual finite local power indices multiply to the precise exponent
from the support size and the original number-field degree. -/
theorem originalFinitePowerQuotient_product (n : ℕ) (hn : 0 < n)
    (ζ : K) (hζ : IsPrimitiveRoot ζ n) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    (∏ v : S, Nat.card ((v.val.adicCompletion K)ˣ ⧸
      (powMonoidHom n : (v.val.adicCompletion K)ˣ →* (v.val.adicCompletion K)ˣ).range)) =
      n ^ (2 * S.card) * n ^ Module.finrank ℚ K := by
  simp_rw [originalFinitePowerQuotient_card K _ n hn ζ hζ, ← mul_assoc]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_coe, ← pow_two, ← pow_mul]
  rw [Finset.prod_coe_sort (s := S)
    (f := fun v : HeightOneSpectrum (𝓞 K) => Ideal.absNorm (v.maxPowDividing (Ideal.span {(n : 𝓞 K)}))),
    originalFinitePowerDefect_product K n hn.ne' S hS]

end
end Dubon2026
