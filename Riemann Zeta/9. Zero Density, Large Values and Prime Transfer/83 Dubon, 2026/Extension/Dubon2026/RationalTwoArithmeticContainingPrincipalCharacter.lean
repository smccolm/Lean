import Dubon2026.RationalTwoArithmeticContainingCharacter
import Dubon2026.RationalTwoArithmeticPrincipalCharacter

/-! # The conductor-two principal character on the original containing field

The original arithmetic reciprocity value on the cyclic subfield is the
restriction of a global containing-field automorphism. Its power character
cancels the exact signed residual product. The containing field need not be
cyclic. This supplies the ramified factor for DUB-17's principal product;
the actual away-prime and real-place comparisons remain separate obligations.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain HeightOneSpectrum
open scoped BigOperators NumberField ValuativeRel

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

variable (a : 𝓞 ℚ)
    (E F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (hEF : E.toIntermediateField ≤ F.toIntermediateField)
    [IsCyclic Gal(E/ℚ)]
    (n : ℕ) [IsCyclotomicExtension {2 ^ (n + 1)} ℚ F]
    {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ (n + 1))) (q : ℚˣ)

/-- Transfer both proved identities through the same containing-field
restriction, preserving the original reciprocity map on the cyclic subfield. -/
private theorem twoPrimaryContaining_principal_pair
    (t : (ZMod (2 ^ (n + 1)))ˣ)
    (σ : Gal(rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n 1 1
      (by simp only [Units.val_one, Nat.cast_one]) Nat.prime_two.not_dvd_one /
      rationalPrimeLocalField 2 Nat.prime_two))
    (hχ : (rationalPrimeOriginalCyclotomicClosureRoot_isPrimitive
      2 Nat.prime_two n 1 1 (by simp only [Units.val_one, Nat.cast_one])
      Nat.prime_two.not_dvd_one).autToPow (rationalPrimeLocalField 2 Nat.prime_two) σ * t = 1)
    (hrec : rationalArithmeticFiniteLocalReciprocityAut a E 2 Nat.prime_two q =
      rationalTwoArithmeticSubfieldRestriction a E F hEF n σ) :
    hζ.autToPow ℚ (rationalTwoArithmeticContainingRestriction a F n σ) * t = 1 ∧
    rationalArithmeticFiniteLocalReciprocityAut a E 2 Nat.prime_two q =
      embeddedNormalGaloisRestriction (F := ℚ) (IntermediateField.inclusion hEF)
        (rationalTwoArithmeticContainingRestriction a F n σ) := by
  constructor
  · exact (congrArg (fun x => x * t)
      (rationalTwoArithmeticContainingRestriction_autToPow a F n hζ σ)).trans hχ
  · exact hrec.trans
      (rationalTwoArithmeticContainingRestriction_subfield a F n E hEF σ).symm

variable (hn : 1 ≤ n)
include hn

/-- For every rational unit, the conductor-two arithmetic reciprocity value
comes from an actual global containing-field automorphism whose character
cancels the signed finite prime product of the same normalized residual. -/
theorem rationalTwoArithmeticContainingField_exists_principal_character :
    let r := rationalPrimeNormalizedResidual 2 Nat.prime_two q
    ∃ S : Finset (HeightOneSpectrum ℤ),
      ∃ hS : ∀ w ∈ S, ¬Rat.HeightOneSpectrum.natGenerator w ∣ 2 ^ (n + 1),
        (∀ w ∉ S, w.valuation ℚ r.val = 1) ∧
        (if 0 < r.val then (1 : ℚ) else -1) *
          (∏ w ∈ S, (Rat.HeightOneSpectrum.natGenerator w : ℚ) ^
            localFieldUnitOrder
              (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator w)
                (Rat.HeightOneSpectrum.prime_natGenerator w))
              (Additive.ofMul
                (rationalPrimeRationalUnit (Rat.HeightOneSpectrum.natGenerator w)
                  (Rat.HeightOneSpectrum.prime_natGenerator w) r))) = r.val ∧
        ∃ τ : Gal(F/ℚ),
          hζ.autToPow ℚ τ *
            arithmeticCyclotomicSignedAwayProductUnit (2 ^ (n + 1)) S hS r = 1 ∧
          rationalArithmeticFiniteLocalReciprocityAut a E 2 Nat.prime_two q =
            embeddedNormalGaloisRestriction (F := ℚ) (IntermediateField.inclusion hEF) τ :=
  Exists.imp (fun _ => Exists.imp (fun _ hs =>
    And.intro hs.1 (And.intro hs.2.1
      (Exists.elim hs.2.2 (fun σ hσ =>
        ⟨rationalTwoArithmeticContainingRestriction a F n σ,
          twoPrimaryContaining_principal_pair a E F hEF n hζ q _ σ hσ.1 hσ.2⟩)))))
    (rationalTwoArithmeticCyclicSubfield_exists_principal_character a E F hEF n hn q)

end
end Dubon2026
