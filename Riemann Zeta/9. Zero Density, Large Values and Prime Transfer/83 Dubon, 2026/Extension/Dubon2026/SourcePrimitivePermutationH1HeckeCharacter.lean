import Dubon2026.SourceBinaryPermutationOperatorDescent
import Dubon2026.SourcePrimitiveFiniteH1HeckeCharacter

/-! DUB-17/18 -> original all-weight adic association -> finite geometric
Hecke realization. The same original finite operator character now acts
on actual permutation H1 Hecke operators through the proved canonical
surjection. Whole-word pullback and original Fourier values are derived. -/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel
variable {Q : ℕ} [NeZero Q] {k : ℤ}
variable {E : Type} [Field E] [CharZero E] [ValuativeRel E]

/-- The original primitive form's adic character on the actual
prime-power permutation H1 Hecke operator image. -/
def sourcePrimitivePermutationH1HeckeCharacter
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
    (p n : ℕ) (hp : p.Prime) (hlarge : 3 < p) [CharP 𝓀[E] p] :
    sourceBinaryPermutationHeckeAlgebra (ZMod (p ^ (n + 1))) Q (k - 2).toNat →+*
      𝒪[E] ⧸ (IsLocalRing.maximalIdeal 𝒪[E]) ^ (n + 1) :=
  (sourcePrimitiveFiniteH1HeckeCharacter f hk τ p n hp).comp
    (sourceBinaryPermutationToModulus p n Q (k - 2).toNat hp hlarge)

/-- Pullback from actual permutation Hecke words is the same entire
original compatible adic H1 character. -/
theorem sourcePrimitivePermutationH1HeckeCharacter_comp
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
    (p n : ℕ) (hp : p.Prime) (hlarge : 3 < p) [CharP 𝓀[E] p] :
    (sourcePrimitivePermutationH1HeckeCharacter f hk τ p n hp hlarge).comp
      (FreeAlgebra.lift ℤ
        (sourceBinaryPermutationPrimeOperators (ZMod (p ^ (n + 1))) Q
          (k - 2).toNat)).rangeRestrict.toRingHom =
      (sourcePrimitiveH1AdicQuotientCharacter f hk τ n).comp
        (sourceBinaryH1HeckeWord Q (k - 2).toNat).toRingHom := by
  apply RingHom.ext
  intro a
  have h := congrArg (sourcePrimitiveFiniteH1HeckeCharacter f hk τ p n hp)
    (RingHom.congr_fun
      (sourceBinaryPermutationToModulus_comp p n Q (k - 2).toNat hp hlarge) a)
  exact h.trans (RingHom.congr_fun
    (sourcePrimitiveFiniteH1HeckeCharacter_comp f hk τ p n hp)
      (sourceBinaryH1HeckeWord Q (k - 2).toNat a))

/-- Every original good-prime Fourier coefficient is retained on the
actual full permutation Hecke correspondence at the same adic precision. -/
theorem sourcePrimitivePermutationH1HeckeCharacter_hecke
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
    (p n : ℕ) (hp : p.Prime) (hlarge : 3 < p) [CharP 𝓀[E] p]
    (ell : sourceBinaryHeckePrime Q) :
    sourcePrimitivePermutationH1HeckeCharacter f hk τ p n hp hlarge
      ((FreeAlgebra.lift ℤ
        (sourceBinaryPermutationPrimeOperators (ZMod (p ^ (n + 1))) Q
          (k - 2).toNat)).rangeRestrict (FreeAlgebra.ι ℤ ell)) =
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal 𝒪[E]) ^ (n + 1))
        ⟨τ (sourcePrimitiveFieldCoefficient f ell.val),
          sourcePrimitiveCoefficient_valuation_le_one f hk τ ell.val⟩ := by
  have h := RingHom.congr_fun
    (sourcePrimitivePermutationH1HeckeCharacter_comp f hk τ p n hp hlarge)
      (FreeAlgebra.ι ℤ ell)
  have hw : sourceBinaryH1HeckeWord Q (k - 2).toNat (FreeAlgebra.ι ℤ ell) =
      ⟨sourceBinaryH1PrimeOperators ℤ Q (k - 2).toNat ell,
        Algebra.subset_adjoin ⟨ell, rfl⟩⟩ :=
    Subtype.ext (FreeAlgebra.lift_ι_apply _ ell)
  change sourcePrimitivePermutationH1HeckeCharacter f hk τ p n hp hlarge _ =
    sourcePrimitiveH1AdicQuotientCharacter f hk τ n
      (sourceBinaryH1HeckeWord Q (k - 2).toNat (FreeAlgebra.ι ℤ ell)) at h
  rw [hw] at h
  exact h.trans (sourcePrimitiveH1AdicQuotientCharacter_hecke f hk τ n ell)

end
end Dubon2026
