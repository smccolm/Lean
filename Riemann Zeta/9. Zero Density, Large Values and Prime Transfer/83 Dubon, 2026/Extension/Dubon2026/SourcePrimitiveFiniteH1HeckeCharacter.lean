import Dubon2026.SourceBinaryH1ModulusOperatorAlgebra
import Dubon2026.SourcePrimitiveH1AdicOperatorKernel
import Dubon2026.SourceFiniteOperatorCharacterDescent

/-! DUB-17/18 -> original all-weight adic association -> geometric
finite-precision Hecke realization. Descend the same original adic
character to the actual finite tensor-operator image, using its proved
operator-kernel compatibility and native surjective ring-map descent. -/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel
variable {Q : ℕ} [NeZero Q] {k : ℤ}
variable {E : Type} [Field E] [CharZero E] [ValuativeRel E]

/-- The actual finite operator quotient kernel is killed by the matching
original adic character. -/
theorem sourcePrimitiveH1AdicQuotientCharacter_modulus_kernel
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
    (p n : ℕ) (hp : p.Prime) [CharP 𝓀[E] p] :
    RingHom.ker (sourceBinaryH1ModulusOperatorMap Q (k - 2).toNat
      (p ^ (n + 1))).rangeRestrict.toRingHom ≤
        RingHom.ker (sourcePrimitiveH1AdicQuotientCharacter f hk τ n) := by
  intro T hT
  have he := congrArg Subtype.val (RingHom.mem_ker.mp hT)
  change sourceBinaryH1ModulusOperatorMap Q (k - 2).toNat (p ^ (n + 1)) T = 0 at he
  apply RingHom.mem_ker.mpr
  exact sourcePrimitiveH1AdicQuotientCharacter_zero_of_operator f hk τ p n hp T
    (sourceBinaryH1ModulusOperatorMap_zero_coefficients Q (k - 2).toNat (p ^ (n + 1)) T he)

/-- The original adic character on the literal finite ring of original
coefficient-reduced H1 operators. -/
def sourcePrimitiveFiniteH1HeckeCharacter
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
    (p n : ℕ) (hp : p.Prime) [CharP 𝓀[E] p] :
    sourceBinaryH1ModulusOperatorAlgebra Q (k - 2).toNat (p ^ (n + 1)) →+*
      𝒪[E] ⧸ (IsLocalRing.maximalIdeal 𝒪[E]) ^ (n + 1) := by
  have hker := sourcePrimitiveH1AdicQuotientCharacter_modulus_kernel f hk τ p n hp
  exact sourceFiniteOperatorCharacterDescend
    (A := sourceBinaryH1HeckeAlgebra Q (k - 2).toNat)
    (B := sourceBinaryH1ModulusOperatorAlgebra Q (k - 2).toNat (p ^ (n + 1)))
    (C := 𝒪[E] ⧸ (IsLocalRing.maximalIdeal 𝒪[E]) ^ (n + 1))
    (sourceBinaryH1ModulusOperatorMap Q (k - 2).toNat (p ^ (n + 1))).rangeRestrict.toRingHom
    (sourceBinaryH1ModulusOperatorMap Q (k - 2).toNat (p ^ (n + 1))).rangeRestrict_surjective
    (sourcePrimitiveH1AdicQuotientCharacter f hk τ n) hker

/-- Pullback from the finite operator image is exactly the whole original
adic character, retaining the already proved transition compatibility. -/
theorem sourcePrimitiveFiniteH1HeckeCharacter_comp
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
    (p n : ℕ) (hp : p.Prime) [CharP 𝓀[E] p] :
    (sourcePrimitiveFiniteH1HeckeCharacter f hk τ p n hp).comp
      (sourceBinaryH1ModulusOperatorMap Q (k - 2).toNat (p ^ (n + 1))).rangeRestrict.toRingHom =
        sourcePrimitiveH1AdicQuotientCharacter f hk τ n :=
  sourceFiniteOperatorCharacterDescend_comp _ _ _ _

/-- Each finite-operator character value is the same original Fourier
coefficient in the same prescribed local embedding and adic precision. -/
theorem sourcePrimitiveFiniteH1HeckeCharacter_hecke
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
    (p n : ℕ) (hp : p.Prime) [CharP 𝓀[E] p] (ell : sourceBinaryHeckePrime Q) :
    sourcePrimitiveFiniteH1HeckeCharacter f hk τ p n hp
      ((sourceBinaryH1ModulusOperatorMap Q (k - 2).toNat (p ^ (n + 1))).rangeRestrict
        ⟨sourceBinaryH1PrimeOperators ℤ Q (k - 2).toNat ell,
          Algebra.subset_adjoin ⟨ell, rfl⟩⟩) =
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal 𝒪[E]) ^ (n + 1))
        ⟨τ (sourcePrimitiveFieldCoefficient f ell.val),
          sourcePrimitiveCoefficient_valuation_le_one f hk τ ell.val⟩ := by
  have h := RingHom.congr_fun (sourcePrimitiveFiniteH1HeckeCharacter_comp f hk τ p n hp)
    ⟨sourceBinaryH1PrimeOperators ℤ Q (k - 2).toNat ell, Algebra.subset_adjoin ⟨ell, rfl⟩⟩
  exact h.trans (sourcePrimitiveH1AdicQuotientCharacter_hecke f hk τ n ell)

end
end Dubon2026
