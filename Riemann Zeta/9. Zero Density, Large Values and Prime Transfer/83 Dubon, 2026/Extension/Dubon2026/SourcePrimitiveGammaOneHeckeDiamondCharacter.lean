import Dubon2026.SourceGammaOneHeckeDiamondDescent
import Dubon2026.SourcePrimitiveFiniteH1HeckeCharacter

/-! DUB-17/18 -> original all-weight association -> actual finite Gamma1
arithmetic character -> original diamond value one. Compose the original
finite Fourier-valued character with the proved native prime-and-diamond
operator descent. The resulting character retains every original prime
Fourier value and sends every original homogeneous normalizer diamond to
one, at every prime-power precision with p > 3. This is a character on
full H1; parabolic and arithmetic two-dimensional realization remain open. -/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel
variable {Q : ℕ} [NeZero Q] {k : ℤ}
variable {E : Type} [Field E] [CharZero E] [ValuativeRel E]

/-- The original primitive form's character on the actual finite Gamma1
good-prime Hecke and original diamond operator ring at the prescribed prime-power precision. -/
def sourcePrimitiveGammaOneHeckeDiamondCharacter
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
    (p n : ℕ) [NeZero p] (hp : p.Prime) (hlarge : 3 < p) [CharP 𝓀[E] p] :
    sourceGammaOneHeckeDiamondAlgebra Q (p ^ (n + 1)) (k - 2).toNat →+*
      𝒪[E] ⧸ (IsLocalRing.maximalIdeal 𝒪[E]) ^ (n + 1) :=
  (sourcePrimitiveFiniteH1HeckeCharacter f hk τ p n hp).comp
    (sourceGammaOneDiamondToModulus Q (p ^ (n + 1)) (k - 2).toNat
      (sourcePrimePower_six_isUnit p n hp hlarge))

/-- The entire Gamma1 word character pulls back to the same original
adic H1 character on the matching restricted prime words with every diamond acting as one. -/
theorem sourcePrimitiveGammaOneHeckeDiamondCharacter_comp
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
    (p n : ℕ) [NeZero p] (hp : p.Prime) (hlarge : 3 < p) [CharP 𝓀[E] p] :
    (sourcePrimitiveGammaOneHeckeDiamondCharacter f hk τ p n hp hlarge).comp
      (FreeAlgebra.lift ℤ
        (sourceGammaOneHeckeDiamondOperators Q (p ^ (n + 1)) (k - 2).toNat)).rangeRestrict.toRingHom =
      (sourcePrimitiveH1AdicQuotientCharacter f hk τ n).comp
        (sourceGammaOneOriginalHeckeDiamondWord Q (p ^ (n + 1)) (k - 2).toNat).toRingHom := by
  apply RingHom.ext
  intro a
  have h := congrArg (sourcePrimitiveFiniteH1HeckeCharacter f hk τ p n hp)
    (RingHom.congr_fun
      (sourceGammaOneDiamondToModulus_comp Q (p ^ (n + 1)) (k - 2).toNat
        (sourcePrimePower_six_isUnit p n hp hlarge)) a)
  exact h.trans (RingHom.congr_fun
    (sourcePrimitiveFiniteH1HeckeCharacter_comp f hk τ p n hp)
      (sourceGammaOneOriginalHeckeDiamondWord Q (p ^ (n + 1)) (k - 2).toNat a))

/-- Each genuine Gamma1 prime correspondence retains the original Fourier
coefficient in the same prescribed local embedding and adic quotient. -/
theorem sourcePrimitiveGammaOneHeckeDiamondCharacter_hecke
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
    (p n : ℕ) [NeZero p] (hp : p.Prime) (hlarge : 3 < p) [CharP 𝓀[E] p]
    (ell : sourceBinaryHeckePrime (Q * p ^ (n + 1))) :
    sourcePrimitiveGammaOneHeckeDiamondCharacter f hk τ p n hp hlarge
      ((FreeAlgebra.lift ℤ
        (sourceGammaOneHeckeDiamondOperators Q (p ^ (n + 1)) (k - 2).toNat)).rangeRestrict
          (FreeAlgebra.ι ℤ (Sum.inl ell))) =
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal 𝒪[E]) ^ (n + 1))
        ⟨τ (sourcePrimitiveFieldCoefficient f ell.val),
          sourcePrimitiveCoefficient_valuation_le_one f hk τ ell.val⟩ := by
  have h := RingHom.congr_fun
    (sourcePrimitiveGammaOneHeckeDiamondCharacter_comp f hk τ p n hp hlarge)
      (FreeAlgebra.ι ℤ (Sum.inl ell))
  have hw : sourceGammaOneOriginalHeckeDiamondWord Q (p ^ (n + 1)) (k - 2).toNat
      (FreeAlgebra.ι ℤ (Sum.inl ell)) =
      ⟨sourceBinaryH1PrimeOperators ℤ Q (k - 2).toNat
        (sourceGammaOneHeckePrimeForget Q (p ^ (n + 1)) ell),
        Algebra.subset_adjoin ⟨sourceGammaOneHeckePrimeForget Q (p ^ (n + 1)) ell, rfl⟩⟩ :=
    FreeAlgebra.lift_ι_apply _ (Sum.inl ell)
  change sourcePrimitiveGammaOneHeckeDiamondCharacter f hk τ p n hp hlarge _ =
    sourcePrimitiveH1AdicQuotientCharacter f hk τ n
      (sourceGammaOneOriginalHeckeDiamondWord Q (p ^ (n + 1)) (k - 2).toNat
        (FreeAlgebra.ι ℤ (Sum.inl ell))) at h
  rw [hw] at h
  exact h.trans (sourcePrimitiveH1AdicQuotientCharacter_hecke f hk τ n
    (sourceGammaOneHeckePrimeForget Q (p ^ (n + 1)) ell))


/-- Every actual original homogeneous normalizer diamond has value one
in the same primitive form's finite character, at every retained precision. -/
theorem sourcePrimitiveGammaOneHeckeDiamondCharacter_diamond
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
    (p n : ℕ) [NeZero p] (hp : p.Prime) (hlarge : 3 < p) [CharP 𝓀[E] p]
    (g : CongruenceSubgroup.Gamma0 (Q * (p ^ (n + 1)) ^ 2)) :
    sourcePrimitiveGammaOneHeckeDiamondCharacter f hk τ p n hp hlarge
      ((FreeAlgebra.lift ℤ
        (sourceGammaOneHeckeDiamondOperators Q (p ^ (n + 1)) (k - 2).toNat)).rangeRestrict
          (FreeAlgebra.ι ℤ (Sum.inr g))) = 1 := by
  have h := RingHom.congr_fun
    (sourcePrimitiveGammaOneHeckeDiamondCharacter_comp f hk τ p n hp hlarge)
      (FreeAlgebra.ι ℤ (Sum.inr g))
  change sourcePrimitiveGammaOneHeckeDiamondCharacter f hk τ p n hp hlarge _ =
    sourcePrimitiveH1AdicQuotientCharacter f hk τ n
      (sourceGammaOneOriginalHeckeDiamondWord Q (p ^ (n + 1)) (k - 2).toNat
        (FreeAlgebra.ι ℤ (Sum.inr g))) at h
  simpa only [sourceGammaOneOriginalHeckeDiamondWord, FreeAlgebra.lift_ι_apply,
    Sum.elim_inr, map_one] using h

end
end Dubon2026
