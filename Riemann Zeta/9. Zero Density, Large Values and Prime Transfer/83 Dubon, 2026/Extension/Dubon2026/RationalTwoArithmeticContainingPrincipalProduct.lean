import Dubon2026.RationalTwoArithmeticContainingPrincipalCharacter
import Dubon2026.ArithmeticCyclotomicContainingSignedProduct

/-! # The conductor-two principal product on the original containing field

Injectivity of the actual cyclotomic power character converts the proved
character cancellation into an identity of original field automorphisms.
Every away-prime factor is original local reciprocity and the real factor
is sign-selected conjugation. DUB-17 still requires the actual real-place
cohomology and carry/invariant comparisons after this automorphism identity.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain HeightOneSpectrum
open scoped BigOperators NumberField

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

variable (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (n : ℕ) [IsCyclotomicExtension {2 ^ (n + 1)} ℚ F]

/-- Injectivity of the actual primitive-root character turns the proved
residue-unit identity into the literal containing-field product identity. -/
private theorem twoPrimaryContaining_product_of_character
    (S : Finset (HeightOneSpectrum ℤ))
    (hS : ∀ w ∈ S, ¬Rat.HeightOneSpectrum.natGenerator w ∣ 2 ^ (n + 1))
    (q : ℚˣ) (τ : Gal(F/ℚ))
    (hχ : (IsCyclotomicExtension.zeta_spec (2 ^ (n + 1)) ℚ F).autToPow ℚ τ *
      arithmeticCyclotomicSignedAwayProductUnit (2 ^ (n + 1)) S hS q = 1) :
    τ * arithmeticCyclotomicContainingSignedAwayProduct a F (2 ^ (n + 1)) S hS q = 1 := by
  let hζ := IsCyclotomicExtension.zeta_spec (2 ^ (n + 1)) ℚ F
  apply IsPrimitiveRoot.autToPow_injective ℚ hζ
  rw [map_mul, map_one, arithmeticCyclotomicContainingSignedAwayProduct_autToPow
    a F (2 ^ (n + 1)) S hS q hζ]
  exact hχ

variable (E : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (hEF : E.toIntermediateField ≤ F.toIntermediateField) [IsCyclic Gal(E/ℚ)]
    (q : ℚˣ) (hn : 1 ≤ n)
include hn

/-- For every rational unit, the conductor-two arithmetic value lifts to
an actual containing-field factor whose product with the signed original
away-prime factors of the same normalized residual is the identity. -/
theorem rationalTwoArithmeticContainingField_exists_principal_product :
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
          τ * arithmeticCyclotomicContainingSignedAwayProduct a F (2 ^ (n + 1)) S hS r = 1 ∧
          rationalArithmeticFiniteLocalReciprocityAut a E 2 Nat.prime_two q =
            embeddedNormalGaloisRestriction (F := ℚ) (IntermediateField.inclusion hEF) τ :=
  Exists.imp (fun _ => Exists.imp (fun _ hs =>
    And.intro hs.1 (And.intro hs.2.1
      (Exists.imp (fun τ hτ => And.intro
        (twoPrimaryContaining_product_of_character a F n _ _ _ τ hτ.1) hτ.2) hs.2.2))))
    (rationalTwoArithmeticContainingField_exists_principal_character a E F hEF n
      (IsCyclotomicExtension.zeta_spec (2 ^ (n + 1)) ℚ F) q hn)

end
end Dubon2026
