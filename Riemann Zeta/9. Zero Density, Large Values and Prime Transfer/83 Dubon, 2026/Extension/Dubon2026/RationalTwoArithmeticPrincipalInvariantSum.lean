import Dubon2026.RationalTwoArithmeticActualPrincipalProduct
import Dubon2026.RationalTwoCyclicSubfieldSupport

/-! # The original conductor-two principal character sum and actual support

The proved principal automorphism product is evaluated by every finite
character in the original rational circle. The constructed support covers
all actual finite-place reciprocity factors. DUB-17 uses this equality
with the proved finite and real carry/invariant formulas; the global
cohomology and coherent invariant-support comparisons remain separate.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain HeightOneSpectrum
open scoped BigOperators NumberField

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

variable (a : 𝓞 ℚ) (E : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    [IsCyclic Gal(E/ℚ)] (q : ℚˣ)
    {d : ℕ} [NeZero d] (χ : Gal(E/ℚ) →* Multiplicative (ZMod d))

/-- Evaluate the already proved original principal product by the actual
finite character and its original rational-circle embedding. -/
private theorem twoPrimaryPrincipal_character_sum
    (S : Finset (HeightOneSpectrum ℤ))
    (hprod :
      letI : CommGroup Gal(E/ℚ) := IsCyclic.commGroup
      rationalArithmeticFiniteLocalReciprocityAut a E 2 Nat.prime_two q *
        (rationalRealArithmeticFiniteRestriction a E (if 0 < q.val then 1 else Complex.conjAe) *
          S.attach.prod (fun w => rationalArithmeticFiniteLocalReciprocityAut a E
            (Rat.HeightOneSpectrum.natGenerator w.1)
            (Rat.HeightOneSpectrum.prime_natGenerator w.1) q)) = 1) :
    rationalCyclicInvariant d (χ (rationalArithmeticFiniteLocalReciprocityAut a E 2 Nat.prime_two q)).toAdd +
      rationalCyclicInvariant d (χ (rationalRealArithmeticFiniteRestriction a E
        (if 0 < q.val then 1 else Complex.conjAe))).toAdd +
      ∑ w ∈ S, rationalCyclicInvariant d
        (χ (rationalArithmeticFiniteLocalReciprocityAut a E
          (Rat.HeightOneSpectrum.natGenerator w) (Rat.HeightOneSpectrum.prime_natGenerator w) q)).toAdd = 0 := by
  letI : CommGroup Gal(E/ℚ) := IsCyclic.commGroup
  have hcharacter := congrArg (fun g => rationalCyclicInvariant d (χ g).toAdd) hprod
  rw [← Finset.sum_attach S (fun w => rationalCyclicInvariant d
    (χ (rationalArithmeticFiniteLocalReciprocityAut a E
      (Rat.HeightOneSpectrum.natGenerator w) (Rat.HeightOneSpectrum.prime_natGenerator w) q)).toAdd)]
  simpa only [map_mul, map_one, map_prod, toAdd_mul, toAdd_one, toAdd_prod,
    map_add, map_zero, map_sum, add_assoc] using hcharacter

variable (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (hEF : E.toIntermediateField ≤ F.toIntermediateField)
    (n : ℕ) (hn : 1 ≤ n) [hcycl : IsCyclotomicExtension {2 ^ (n + 1)} ℚ F]
include hn hEF hcycl

/-- Every finite character of the original cyclic subfield satisfies the
principal rational-invariant sum, and every finite-place factor outside
the constructed support and two is the identity. -/
theorem rationalTwoArithmeticCyclicSubfield_exists_principal_invariant_sum :
    ∃ S : Finset (HeightOneSpectrum ℤ),
      (∀ w ∈ S, ¬Rat.HeightOneSpectrum.natGenerator w ∣ 2 ^ (n + 1)) ∧
      (∀ w ∉ S, Rat.HeightOneSpectrum.natGenerator w ≠ 2 →
        rationalArithmeticFiniteLocalReciprocityAut a E (Rat.HeightOneSpectrum.natGenerator w)
          (Rat.HeightOneSpectrum.prime_natGenerator w) q = 1) ∧
      rationalCyclicInvariant d (χ (rationalArithmeticFiniteLocalReciprocityAut a E 2 Nat.prime_two q)).toAdd +
        rationalCyclicInvariant d (χ (rationalRealArithmeticFiniteRestriction a E
          (if 0 < q.val then 1 else Complex.conjAe))).toAdd +
        ∑ w ∈ S, rationalCyclicInvariant d
          (χ (rationalArithmeticFiniteLocalReciprocityAut a E
            (Rat.HeightOneSpectrum.natGenerator w) (Rat.HeightOneSpectrum.prime_natGenerator w) q)).toAdd = 0 :=
  Exists.imp (fun S hs => Exists.elim hs (fun hS hrest =>
    And.intro hS (And.intro
      (fun w hw htwo => rationalTwoArithmeticCyclicSubfield_reciprocity_eq_one_of_residual_valuation
        a E F hEF n w htwo q (hrest.1 w hw))
      (twoPrimaryPrincipal_character_sum a E q χ S hrest.2.2))))
    (rationalTwoArithmeticCyclicSubfield_exists_actual_principal_product a E F hEF n q hn)

end
end Dubon2026
