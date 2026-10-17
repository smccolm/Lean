import Dubon2026.RationalTwoArithmeticContainingPrincipalProduct
import Dubon2026.ArithmeticContainingNormalizedResidual

/-! # The original conductor-two cyclic-subfield principal product

The containing-field product restricts to the original arithmetic
reciprocity maps of the same rational unit at two and at every selected
away prime. Its real factor is the restriction of sign-selected original
cyclotomic conjugation. DUB-17 still requires its identification with the
actual real-place cohomology contribution and the carry/invariant comparison.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain HeightOneSpectrum
open scoped BigOperators NumberField

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

variable (a : 𝓞 ℚ)
    (E F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (hEF : E.toIntermediateField ≤ F.toIntermediateField) [IsCyclic Gal(E/ℚ)]
    (n : ℕ) [IsCyclotomicExtension {2 ^ (n + 1)} ℚ F] (q : ℚˣ)

/-- Restrict the proved containing-field product and remove its harmless
normalization from the actual away-prime and real factors. -/
private theorem twoPrimaryOriginal_principal_product
    (S : Finset (HeightOneSpectrum ℤ))
    (hS : ∀ w ∈ S, ¬Rat.HeightOneSpectrum.natGenerator w ∣ 2 ^ (n + 1))
    (τ : Gal(F/ℚ))
    (hprod : τ * arithmeticCyclotomicContainingSignedAwayProduct a F (2 ^ (n + 1)) S hS
      (rationalPrimeNormalizedResidual 2 Nat.prime_two q) = 1)
    (hrec : rationalArithmeticFiniteLocalReciprocityAut a E 2 Nat.prime_two q =
      embeddedNormalGaloisRestriction (F := ℚ) (IntermediateField.inclusion hEF) τ) :
    letI : CommGroup Gal(E/ℚ) := IsCyclic.commGroup
    let R : Gal(F/ℚ) →* Gal(E/ℚ) :=
      embeddedNormalGaloisRestriction (F := ℚ) (IntermediateField.inclusion hEF)
    rationalArithmeticFiniteLocalReciprocityAut a E 2 Nat.prime_two q *
      (R (rationalCyclotomicRealSignAut (2 ^ (n + 1)) F q) *
        S.attach.prod (fun w => rationalArithmeticFiniteLocalReciprocityAut a E
          (Rat.HeightOneSpectrum.natGenerator w.1)
          (Rat.HeightOneSpectrum.prime_natGenerator w.1) q)) = 1 := by
  letI : CommGroup Gal(E/ℚ) := IsCyclic.commGroup
  let R : Gal(F/ℚ) →* Gal(E/ℚ) :=
    embeddedNormalGaloisRestriction (F := ℚ) (IntermediateField.inclusion hEF)
  have hnorm : τ * arithmeticCyclotomicContainingSignedAwayProduct a F (2 ^ (n + 1)) S hS q = 1 := by
    rw [← arithmeticCyclotomicContainingSignedAwayProduct_normalizedResidual
      a F 2 Nat.prime_two n S hS q]
    exact hprod
  have hmap : R τ * R (arithmeticCyclotomicContainingSignedAwayProduct a F (2 ^ (n + 1)) S hS q) = 1 := by
    simpa only [map_mul, map_one] using congrArg R hnorm
  have hrest := arithmeticCyclotomicContainingSignedAwayProduct_restrict
    a F (2 ^ (n + 1)) S hS q E hEF
  exact (congrArg₂ (fun x y : Gal(E/ℚ) => x * y) hrec hrest.symm).trans hmap

variable (hn : 1 ≤ n)
include hn

/-- The original reciprocity factors of every rational unit on the
actual cyclic subfield satisfy the principal product with the restricted
sign-selected conjugation, using a constructed finite away-prime support. -/
theorem rationalTwoArithmeticCyclicSubfield_exists_principal_product :
    let r := rationalPrimeNormalizedResidual 2 Nat.prime_two q
    ∃ S : Finset (HeightOneSpectrum ℤ),
      ∃ _hS : ∀ w ∈ S, ¬Rat.HeightOneSpectrum.natGenerator w ∣ 2 ^ (n + 1),
        (∀ w ∉ S, w.valuation ℚ r.val = 1) ∧
        (if 0 < r.val then (1 : ℚ) else -1) *
          (∏ w ∈ S, (Rat.HeightOneSpectrum.natGenerator w : ℚ) ^
            localFieldUnitOrder
              (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator w)
                (Rat.HeightOneSpectrum.prime_natGenerator w))
              (Additive.ofMul
                (rationalPrimeRationalUnit (Rat.HeightOneSpectrum.natGenerator w)
                  (Rat.HeightOneSpectrum.prime_natGenerator w) r))) = r.val ∧
        (letI : CommGroup Gal(E/ℚ) := IsCyclic.commGroup
         let R : Gal(F/ℚ) →* Gal(E/ℚ) :=
           embeddedNormalGaloisRestriction (F := ℚ) (IntermediateField.inclusion hEF)
         rationalArithmeticFiniteLocalReciprocityAut a E 2 Nat.prime_two q *
           (R (rationalCyclotomicRealSignAut (2 ^ (n + 1)) F q) *
             S.attach.prod (fun w => rationalArithmeticFiniteLocalReciprocityAut a E
               (Rat.HeightOneSpectrum.natGenerator w.1)
               (Rat.HeightOneSpectrum.prime_natGenerator w.1) q)) = 1) :=
  Exists.imp (fun _ => Exists.imp (fun _ hs =>
    And.intro hs.1 (And.intro hs.2.1
      (Exists.elim hs.2.2 (fun τ hτ =>
        twoPrimaryOriginal_principal_product a E F hEF n q _ _ τ hτ.1 hτ.2)))))
    (rationalTwoArithmeticContainingField_exists_principal_product a F n E hEF q hn)

end
end Dubon2026
