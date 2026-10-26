import Dubon2026.SourcePrimitiveAdicH1Quotients

/-! DUB-17/18 -> original all-weight characteristic-zero Galois association
-> compatible finite-level Hecke realizations. Assemble exact reductions of
the original integral H1 character with its original Fourier values and the
existing analytic residual character. This records coefficient compatibility;
an actual geometric Galois realization is still required.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel

variable {Q : ℕ} [NeZero Q] {k : ℤ}
variable {E : Type} [Field E] [CharZero E] [ValuativeRel E]

/-- Exact compatible finite adic reductions of the same original H1 character. -/
def sourcePrimitiveCompatibleH1AdicData
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E) : Prop :=
  IsNoetherianRing 𝒪[E] ∧ Finite 𝓀[E] ∧
  (∀ n : ℕ, Finite (𝒪[E] ⧸ (IsLocalRing.maximalIdeal 𝒪[E]) ^ (n + 1))) ∧
  (∀ ell : sourceBinaryHeckePrime Q,
    IsLocalRing.residue 𝒪[E] (sourcePrimitiveLocalH1HeckeCharacter f hk τ
      ⟨sourceBinaryH1PrimeOperators ℤ Q (k - 2).toNat ell,
        Algebra.subset_adjoin ⟨ell, rfl⟩⟩) =
      sourcePrimitiveResidualHeckeCharacter f hk τ
        ⟨cuspHeckeLinear Q k ell.val, Algebra.subset_adjoin
          ⟨(⟨ell.val, ell.property.1.pos⟩ : ℕ+), rfl⟩⟩) ∧
  (∀ (n : ℕ) (ell : sourceBinaryHeckePrime Q),
    sourcePrimitiveH1AdicQuotientCharacter f hk τ n
      ⟨sourceBinaryH1PrimeOperators ℤ Q (k - 2).toNat ell,
        Algebra.subset_adjoin ⟨ell, rfl⟩⟩ =
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal 𝒪[E]) ^ (n + 1))
        ⟨τ (sourcePrimitiveFieldCoefficient f ell.val),
          sourcePrimitiveCoefficient_valuation_le_one f hk τ ell.val⟩) ∧
  ∀ (m n : ℕ) (h : m ≤ n),
    (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal 𝒪[E])
      (Nat.add_le_add_right h 1)).comp (sourcePrimitiveH1AdicQuotientCharacter f hk τ n) =
        sourcePrimitiveH1AdicQuotientCharacter f hk τ m

/-- Noetherianity and finite residue imply the assembled coefficient data;
the exact character and all compatibility identities are derived. -/
theorem sourcePrimitiveCompatibleH1AdicData_of_local
    [IsNoetherianRing 𝒪[E]] [Finite 𝓀[E]]
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E) :
    sourcePrimitiveCompatibleH1AdicData f hk τ :=
  ⟨inferInstance, inferInstance, sourceLocalH1AdicQuotient_finite,
    sourcePrimitiveLocalH1HeckeCharacter_residue f hk τ,
    sourcePrimitiveH1AdicQuotientCharacter_hecke f hk τ,
    fun _ _ h => sourcePrimitiveH1AdicQuotientCharacter_compatible f hk τ h⟩

end
end Dubon2026
