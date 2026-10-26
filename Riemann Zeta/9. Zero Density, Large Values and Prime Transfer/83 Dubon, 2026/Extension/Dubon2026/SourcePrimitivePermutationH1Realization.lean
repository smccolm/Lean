import Dubon2026.SourcePrimitivePermutationH1HeckeCharacter
import Dubon2026.SourceBinaryPermutationHeckeFinite
import Dubon2026.SourcePrimitiveFiniteH1OperatorRealization

/-! DUB-17/18 -> original all-weight adic association -> finite geometric
Hecke realization. Consume the actual original primitive form and its
proved compatible local characters to obtain finite permutation Hecke
characters at every precision. No operator relation, finite quotient or
Hecke character is supplied as an extra hypothesis. The arithmetic
geometric correspondence identification and Galois action remain open. -/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel
variable {Q : ℕ} [NeZero Q] {k : ℤ}
variable {E : Type} [Field E] [CharZero E] [ValuativeRel E]

/-- The actual finite permutation Hecke characters, their surjection to
the original finite operator image, and their original Fourier values. -/
def sourcePrimitivePermutationH1CharacterData
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
    (p : ℕ) (hp : p.Prime) (hlarge : 3 < p) [CharP 𝓀[E] p] : Prop :=
  sourcePrimitiveFiniteH1CharacterData f hk τ p hp ∧
  ∀ n : ℕ,
    Finite (sourceBinaryPermutationHeckeAlgebra (ZMod (p ^ (n + 1))) Q (k - 2).toNat) ∧
    Function.Surjective (sourceBinaryPermutationToModulus p n Q (k - 2).toNat hp hlarge) ∧
    (sourcePrimitivePermutationH1HeckeCharacter f hk τ p n hp hlarge).comp
      (FreeAlgebra.lift ℤ
        (sourceBinaryPermutationPrimeOperators (ZMod (p ^ (n + 1))) Q
          (k - 2).toNat)).rangeRestrict.toRingHom =
      (sourcePrimitiveH1AdicQuotientCharacter f hk τ n).comp
        (sourceBinaryH1HeckeWord Q (k - 2).toNat).toRingHom ∧
    ∀ ell : sourceBinaryHeckePrime Q,
      sourcePrimitivePermutationH1HeckeCharacter f hk τ p n hp hlarge
        ((FreeAlgebra.lift ℤ
          (sourceBinaryPermutationPrimeOperators (ZMod (p ^ (n + 1))) Q
            (k - 2).toNat)).rangeRestrict (FreeAlgebra.ι ℤ ell)) =
        Ideal.Quotient.mk ((IsLocalRing.maximalIdeal 𝒪[E]) ^ (n + 1))
          ⟨τ (sourcePrimitiveFieldCoefficient f ell.val),
            sourcePrimitiveCoefficient_valuation_le_one f hk τ ell.val⟩

/-- Every original primitive form of weight at least two supplies actual
finite permutation H1 Hecke characters at all positive powers of each
prime greater than three, retaining the original compatible adic
character and every original good-prime Fourier coefficient. -/
theorem sourcePrimitive_exists_permutationH1HeckeCharacters
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (p : ℕ) (hp : p.Prime)
    (hlarge : 3 < p) :
    letI := sourcePrimitiveCoefficientField_numberField f hk
    letI := rationalPrimeLocalField_charZero p hp
    let F := rationalPrimeLocalField p hp
    let L := commonCoefficientField (sourcePrimitiveCoefficientField f) F
    ∃ (_ : UniformSpace L) (_ : ValuativeRel L),
      IsUniformAddGroup L ∧ IsNonarchimedeanLocalField L ∧
      (ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation L) ∧
      FiniteDimensional F L ∧
      ∃ hchar : CharP 𝓀[L] p, letI := hchar
        Finite 𝓀[L] ∧ ∃ τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] L,
          sourcePrimitivePermutationH1CharacterData f hk τ p hp hlarge := by
  letI := sourcePrimitiveCoefficientField_numberField f hk
  letI := rationalPrimeLocalField_charZero p hp
  let F := rationalPrimeLocalField p hp
  let L := commonCoefficientField (sourcePrimitiveCoefficientField f) F
  have hc := sourcePrimitive_exists_finiteH1OperatorCharacters f hk p hp
  dsimp only at hc
  obtain ⟨u, v, hu, hv, hext, hdim, hchar, hfinite, τ, hdata⟩ := hc
  letI : UniformSpace L := u
  letI : ValuativeRel L := v
  letI : CharP 𝓀[L] p := hchar
  refine ⟨u, v, hu, hv, hext, hdim, hchar, hfinite, τ, hdata, ?_⟩
  intro n
  exact ⟨sourceBinaryPrimePowerPermutationHeckeAlgebra_finite p n Q (k - 2).toNat hp,
    sourceBinaryPermutationToModulus_surjective p n Q (k - 2).toNat hp hlarge,
    sourcePrimitivePermutationH1HeckeCharacter_comp f hk τ p n hp hlarge,
    sourcePrimitivePermutationH1HeckeCharacter_hecke f hk τ p n hp hlarge⟩

end
end Dubon2026
