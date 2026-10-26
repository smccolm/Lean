import Dubon2026.SourcePrimitiveIntegralH1Character
import Dubon2026.SourcePrimitiveFieldHeckeCharacter

/-! DUB-17/18 -> original all-weight adic association -> compatible
prime-power Hecke realizations -> the original integral H1 character
over its actual Fourier coefficient field. Restrict the already proved
complex character using its original prime generators. This avoids an
algebraic-closure specialization when constructing local adic quotients.
An arithmetic Galois realization is still required.
-/
namespace Dubon2026
noncomputable section

variable {Q : ℕ} [NeZero Q] {k : ℤ}

/-- All values of the original integral H1 Hecke character belong to the
same literal Fourier coefficient ring as the original primitive form. -/
theorem sourcePrimitiveH1HeckeCharacter_mem_coefficientRing
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (T : sourceBinaryH1HeckeAlgebra Q (k - 2).toNat) :
    sourcePrimitiveH1HeckeCharacter f hk T ∈ sourcePrimitiveCoefficientRing f := by
  have h : ∀ t (ht : t ∈ sourceBinaryH1HeckeAlgebra Q (k - 2).toNat),
      sourcePrimitiveH1HeckeCharacter f hk ⟨t, ht⟩ ∈ sourcePrimitiveCoefficientRing f := by
    intro t ht
    induction ht using Algebra.adjoin_induction with
    | mem t ht =>
      obtain ⟨ell, rfl⟩ := ht
      rw [sourcePrimitiveH1HeckeCharacter_hecke]
      exact Algebra.subset_adjoin ⟨ell.val, rfl⟩
    | algebraMap z =>
      change sourcePrimitiveH1HeckeCharacter f hk (algebraMap ℤ _ z) ∈ _
      rw [AlgHom.commutes]
      exact (sourcePrimitiveCoefficientRing f).algebraMap_mem z
    | add a b ha hb hfa hfb =>
      change sourcePrimitiveH1HeckeCharacter f hk (⟨a, ha⟩ + ⟨b, hb⟩) ∈ _
      rw [map_add]
      exact (sourcePrimitiveCoefficientRing f).add_mem hfa hfb
    | mul a b ha hb hfa hfb =>
      change sourcePrimitiveH1HeckeCharacter f hk (⟨a, ha⟩ * ⟨b, hb⟩) ∈ _
      rw [map_mul]
      exact (sourcePrimitiveCoefficientRing f).mul_mem hfa hfb
  exact h T.val T.property

/-- The original H1 character, valued in the original Fourier coefficient field. -/
def sourcePrimitiveFieldH1HeckeCharacter (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) :
    sourceBinaryH1HeckeAlgebra Q (k - 2).toNat →ₐ[ℤ] sourcePrimitiveCoefficientField f :=
  (sourcePrimitiveH1HeckeCharacter f hk).codRestrict
    ((sourcePrimitiveCoefficientField f).toSubalgebra.restrictScalars ℤ)
    (fun T => sourcePrimitiveCoefficientRing_le_field f
      (sourcePrimitiveH1HeckeCharacter_mem_coefficientRing f hk T))

/-- The field-valued H1 character has exactly the original good-prime Fourier values. -/
theorem sourcePrimitiveFieldH1HeckeCharacter_hecke
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (ell : sourceBinaryHeckePrime Q) :
    sourcePrimitiveFieldH1HeckeCharacter f hk
      ⟨sourceBinaryH1PrimeOperators ℤ Q (k - 2).toNat ell,
        Algebra.subset_adjoin ⟨ell, rfl⟩⟩ = sourcePrimitiveFieldCoefficient f ell.val := by
  apply Subtype.ext
  exact sourcePrimitiveH1HeckeCharacter_hecke f hk ell

/-- Finiteness of the actual integral H1 Hecke algebra makes every field-valued character value integral. -/
theorem sourcePrimitiveFieldH1HeckeCharacter_isIntegral
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (T : sourceBinaryH1HeckeAlgebra Q (k - 2).toNat) :
    IsIntegral ℤ (sourcePrimitiveFieldH1HeckeCharacter f hk T) := by
  letI := sourceBinaryH1HeckeAlgebra_finite Q (k - 2).toNat
  exact (IsIntegral.of_finite ℤ T).map (sourcePrimitiveFieldH1HeckeCharacter f hk)

end
end Dubon2026
