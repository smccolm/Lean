import Dubon2026.SourcePrimitiveH1CoefficientField
import Dubon2026.SourcePrimitiveResidualHeckeCharacter

/-! DUB-17/18 -> original all-weight adic association -> compatible
prime-power Hecke realizations. The original integral binary H1 character
lands in the valuation ring of the same original local coefficient
embedding. Integrality follows from the finite integral H1 Hecke algebra;
no algebraic-closure specialization or new eigenvalue choice is used.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel

variable {Q : ℕ} [NeZero Q] {k : ℤ}
variable {E : Type} [Field E] [CharZero E] [ValuativeRel E]

/-- The original integral H1 character in the valuation ring of the same Fourier coefficient embedding. -/
def sourcePrimitiveLocalH1HeckeCharacter (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E) :
    sourceBinaryH1HeckeAlgebra Q (k - 2).toNat →+* 𝒪[E] :=
  (τ.toRingHom.comp (sourcePrimitiveFieldH1HeckeCharacter f hk).toRingHom).codRestrict
    (ValuativeRel.valuation E).integer (fun T => by
      have hi := (sourcePrimitiveFieldH1HeckeCharacter_isIntegral f hk T).map
        (τ.restrictScalars ℤ)
      exact (Valuation.integer.integers (ValuativeRel.valuation E)).isIntegral_iff_v_le_one.mp
        hi.tower_top)

/-- The local H1 character retains the exact original field-valued character under the prescribed embedding. -/
theorem sourcePrimitiveLocalH1HeckeCharacter_coe
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
    (T : sourceBinaryH1HeckeAlgebra Q (k - 2).toNat) :
    (sourcePrimitiveLocalH1HeckeCharacter f hk τ T : E) =
      τ (sourcePrimitiveFieldH1HeckeCharacter f hk T) := rfl

/-- Every original good-prime H1 value is the original Fourier coefficient in the same valuation ring. -/
theorem sourcePrimitiveLocalH1HeckeCharacter_hecke
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E) (ell : sourceBinaryHeckePrime Q) :
    sourcePrimitiveLocalH1HeckeCharacter f hk τ
      ⟨sourceBinaryH1PrimeOperators ℤ Q (k - 2).toNat ell,
        Algebra.subset_adjoin ⟨ell, rfl⟩⟩ =
      ⟨τ (sourcePrimitiveFieldCoefficient f ell.val),
        sourcePrimitiveCoefficient_valuation_le_one f hk τ ell.val⟩ := by
  apply Subtype.ext
  rw [sourcePrimitiveLocalH1HeckeCharacter_coe, sourcePrimitiveFieldH1HeckeCharacter_hecke]

/-- Reduction of the local H1 character agrees with the existing original analytic residual character on each good prime. -/
theorem sourcePrimitiveLocalH1HeckeCharacter_residue
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E) (ell : sourceBinaryHeckePrime Q) :
    IsLocalRing.residue 𝒪[E] (sourcePrimitiveLocalH1HeckeCharacter f hk τ
      ⟨sourceBinaryH1PrimeOperators ℤ Q (k - 2).toNat ell,
        Algebra.subset_adjoin ⟨ell, rfl⟩⟩) =
      sourcePrimitiveResidualHeckeCharacter f hk τ
        ⟨cuspHeckeLinear Q k ell.val, Algebra.subset_adjoin
          ⟨(⟨ell.val, ell.property.1.pos⟩ : ℕ+), rfl⟩⟩ := by
  rw [sourcePrimitiveLocalH1HeckeCharacter_hecke]
  exact (sourcePrimitiveResidualHeckeCharacter_hecke f hk τ ⟨ell.val, ell.property.1.pos⟩).symm

end
end Dubon2026
