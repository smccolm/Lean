import Dubon2026.SourcePrimitiveFiniteH1HeckeCharacter
import Dubon2026.SourcePrimitiveCongruentH1AdicRealization

/-! DUB-17/18 -> original all-weight adic association -> geometric
finite-precision Hecke realization. The original primitive form and prime
supply their actual local completion and finite operator characters at
every precision. Each pulls back to the same compatible original H1
character and retains the exact original Fourier coefficients. No finite
operator quotient or character factorization is supplied as a premise. -/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel
variable {Q : ℕ} [NeZero Q] {k : ℤ}
variable {E : Type} [Field E] [CharZero E] [ValuativeRel E]

/-- The actual finite operator characters with their whole original
pullback and exact good-prime Fourier values at every precision. -/
def sourcePrimitiveFiniteH1CharacterData
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
    (p : ℕ) (hp : p.Prime) [CharP 𝓀[E] p] : Prop :=
  sourcePrimitiveH1AdicCongruenceData f hk τ p ∧
  ∀ n : ℕ,
    Finite (sourceBinaryH1ModulusOperatorAlgebra Q (k - 2).toNat (p ^ (n + 1))) ∧
    (sourcePrimitiveFiniteH1HeckeCharacter f hk τ p n hp).comp
      (sourceBinaryH1ModulusOperatorMap Q (k - 2).toNat (p ^ (n + 1))).rangeRestrict.toRingHom =
        sourcePrimitiveH1AdicQuotientCharacter f hk τ n ∧
    ∀ ell : sourceBinaryHeckePrime Q,
      sourcePrimitiveFiniteH1HeckeCharacter f hk τ p n hp
        ((sourceBinaryH1ModulusOperatorMap Q (k - 2).toNat (p ^ (n + 1))).rangeRestrict
          ⟨sourceBinaryH1PrimeOperators ℤ Q (k - 2).toNat ell,
            Algebra.subset_adjoin ⟨ell, rfl⟩⟩) =
        Ideal.Quotient.mk ((IsLocalRing.maximalIdeal 𝒪[E]) ^ (n + 1))
          ⟨τ (sourcePrimitiveFieldCoefficient f ell.val),
            sourcePrimitiveCoefficient_valuation_le_one f hk τ ell.val⟩

/-- Every original primitive form of weight at least two supplies, at every
prescribed prime, actual finite coefficient-reduced H1 operator characters
with the same compatible adic pullback and exact original Fourier values. -/
theorem sourcePrimitive_exists_finiteH1OperatorCharacters
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (p : ℕ) (hp : p.Prime) :
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
          sourcePrimitiveFiniteH1CharacterData f hk τ p hp := by
  letI := sourcePrimitiveCoefficientField_numberField f hk
  letI := rationalPrimeLocalField_charZero p hp
  let F := rationalPrimeLocalField p hp
  let L := commonCoefficientField (sourcePrimitiveCoefficientField f) F
  have hc := sourcePrimitive_exists_congruentH1AdicRealization f hk p hp
  dsimp only at hc
  obtain ⟨u, v, hu, hv, hext, hdim, hchar, hfinite, τ, hdata⟩ := hc
  letI : UniformSpace L := u
  letI : ValuativeRel L := v
  letI : CharP 𝓀[L] p := hchar
  refine ⟨u, v, hu, hv, hext, hdim, hchar, hfinite, τ, hdata, ?_⟩
  intro n
  letI : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  exact ⟨sourceBinaryH1ModulusOperatorAlgebra_finite Q (k - 2).toNat (p ^ (n + 1)),
    sourcePrimitiveFiniteH1HeckeCharacter_comp f hk τ p n hp,
    sourcePrimitiveFiniteH1HeckeCharacter_hecke f hk τ p n hp⟩

end
end Dubon2026
