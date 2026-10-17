import Dubon2026.RationalTwoArithmeticOriginalPrincipalProduct
import Dubon2026.ArithmeticRealSubfieldRestriction

/-! # The principal product with the actual original real arithmetic map

The conductor-two and every away-prime factor are the original finite
reciprocity maps on the same cyclic subfield. The real factor is now the
existing real arithmetic restriction applied to sign-selected complex
conjugation. This closes the field-automorphism comparison for DUB-17;
actual cohomology and carry/invariant comparisons remain necessary.
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

/-- Replace the proved restricted cyclotomic real factor by the same
original real arithmetic automorphism. -/
private theorem twoPrimaryActual_real_factor
    (S : Finset (HeightOneSpectrum ℤ))
    (hprod :
      letI : CommGroup Gal(E/ℚ) := IsCyclic.commGroup
      let R : Gal(F/ℚ) →* Gal(E/ℚ) :=
        embeddedNormalGaloisRestriction (F := ℚ) (IntermediateField.inclusion hEF)
      rationalArithmeticFiniteLocalReciprocityAut a E 2 Nat.prime_two q *
        (R (rationalCyclotomicRealSignAut (2 ^ (n + 1)) F q) *
          S.attach.prod (fun w => rationalArithmeticFiniteLocalReciprocityAut a E
            (Rat.HeightOneSpectrum.natGenerator w.1)
            (Rat.HeightOneSpectrum.prime_natGenerator w.1) q)) = 1) :
    letI : CommGroup Gal(E/ℚ) := IsCyclic.commGroup
    rationalArithmeticFiniteLocalReciprocityAut a E 2 Nat.prime_two q *
      (rationalRealArithmeticFiniteRestriction a E (if 0 < q.val then 1 else Complex.conjAe) *
        S.attach.prod (fun w => rationalArithmeticFiniteLocalReciprocityAut a E
          (Rat.HeightOneSpectrum.natGenerator w.1)
          (Rat.HeightOneSpectrum.prime_natGenerator w.1) q)) = 1 := by
  letI : CommGroup Gal(E/ℚ) := IsCyclic.commGroup
  let R : Gal(F/ℚ) →* Gal(E/ℚ) :=
    embeddedNormalGaloisRestriction (F := ℚ) (IntermediateField.inclusion hEF)
  let W : Gal(E/ℚ) := S.attach.prod (fun w => rationalArithmeticFiniteLocalReciprocityAut a E
    (Rat.HeightOneSpectrum.natGenerator w.1) (Rat.HeightOneSpectrum.prime_natGenerator w.1) q)
  have hreal : R (rationalCyclotomicRealSignAut (2 ^ (n + 1)) F q) =
      rationalRealArithmeticFiniteRestriction a E (if 0 < q.val then 1 else Complex.conjAe) :=
    rationalCyclotomicRealSignAut_restrict_eq_real a E F hEF (2 ^ (n + 1)) q
  exact (congrArg (fun z : Gal(E/ℚ) =>
    rationalArithmeticFiniteLocalReciprocityAut a E 2 Nat.prime_two q * (z * W)) hreal).symm.trans hprod

variable (hn : 1 ≤ n)
include hn hEF

/-- Every rational unit satisfies the original arithmetic principal
product on the actual cyclic subfield, with the existing real restriction
and a constructed finite set of away-prime reciprocity factors. -/
theorem rationalTwoArithmeticCyclicSubfield_exists_actual_principal_product :
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
         rationalArithmeticFiniteLocalReciprocityAut a E 2 Nat.prime_two q *
           (rationalRealArithmeticFiniteRestriction a E (if 0 < q.val then 1 else Complex.conjAe) *
             S.attach.prod (fun w => rationalArithmeticFiniteLocalReciprocityAut a E
               (Rat.HeightOneSpectrum.natGenerator w.1)
               (Rat.HeightOneSpectrum.prime_natGenerator w.1) q)) = 1) :=
  Exists.imp (fun _ => Exists.imp (fun _ hs =>
    And.intro hs.1 (And.intro hs.2.1
      (twoPrimaryActual_real_factor a E F hEF n q _ hs.2.2))))
    (rationalTwoArithmeticCyclicSubfield_exists_principal_product a E F hEF n q hn)

end
end Dubon2026
