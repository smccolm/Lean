import Dubon2026.SourcePrimitiveResidualHeckeCharacter
import Dubon2026.RationalPrimeOriginalResidueCard
import Mathlib.Algebra.CharP.CharAndCard

/-! The residual eigensystem has the actual original prime characteristic.
DUB-17/18 -> modular Galois association -> reduction of the original Hecke
eigensystem modulo the original rational prime. Reuse the proved cardinality
of the genuine prime-completion residue field and native valuation-extension
residue algebras. No new completion or residue-field construction is needed.
-/

namespace Dubon2026
noncomputable section
open scoped ValuativeRel
variable {Q : ℕ} [NeZero Q] {k : ℤ}

/-- The residue field of the genuine original rational prime completion has that prime characteristic. -/
theorem sourceRationalPrimeLocalResidue_charP (ell : ℕ) (hell : ell.Prime) :
    CharP 𝓀[rationalPrimeLocalField ell hell] ell := by
  letI : Fact ell.Prime := ⟨hell⟩
  letI : Fintype 𝓀[rationalPrimeLocalField ell hell] := Fintype.ofFinite _
  apply charP_of_card_eq_prime
  rw [← Nat.card_eq_fintype_card]
  exact rationalPrimeLocalField_residue_card ell hell

/-- An actual valuation extension of the original prime completion preserves its residue characteristic. -/
theorem sourceRationalPrimeExtensionResidue_charP (ell : ℕ) (hell : ell.Prime)
    (E : Type) [Field E] [Algebra (rationalPrimeLocalField ell hell) E]
    [ValuativeRel E]
    [(ValuativeRel.valuation (rationalPrimeLocalField ell hell)).HasExtension
      (ValuativeRel.valuation E)] : CharP 𝓀[E] ell := by
  letI := sourceRationalPrimeLocalResidue_charP ell hell
  exact (Algebra.charP_iff 𝓀[rationalPrimeLocalField ell hell] 𝓀[E] ell).mp inferInstance

/-- The original primitive residual Hecke eigensystem is realized over an actual finite residue field of the prescribed prime characteristic, with maximal kernel and exact original Fourier values. -/
theorem sourcePrimitive_exists_residualHeckeCharacter_charP
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (ell : ℕ) (hell : ell.Prime) :
    letI := sourcePrimitiveCoefficientField_numberField f hk
    letI := rationalPrimeLocalField_charZero ell hell
    let F := rationalPrimeLocalField ell hell
    let L := commonCoefficientField (sourcePrimitiveCoefficientField f) F
    ∃ (_ : UniformSpace L) (_ : ValuativeRel L),
      IsUniformAddGroup L ∧ IsNonarchimedeanLocalField L ∧
      (ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation L) ∧
      FiniteDimensional F L ∧ CharP 𝓀[L] ell ∧ Finite 𝓀[L] ∧
      ∃ τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] L,
        (RingHom.ker (sourcePrimitiveResidualHeckeCharacter f hk τ)).IsMaximal ∧
        ∀ n : ℕ+, sourcePrimitiveResidualHeckeCharacter f hk τ
          ⟨cuspHeckeLinear Q k n, Algebra.subset_adjoin ⟨n, rfl⟩⟩ =
            IsLocalRing.residue 𝒪[L]
              ⟨τ (sourcePrimitiveFieldCoefficient f n),
                sourcePrimitiveCoefficient_valuation_le_one f hk τ n⟩ := by
  letI := sourcePrimitiveCoefficientField_numberField f hk
  letI := rationalPrimeLocalField_charZero ell hell
  let F := rationalPrimeLocalField ell hell
  let L := commonCoefficientField (sourcePrimitiveCoefficientField f) F
  have hc := sourcePrimitive_exists_residualHeckeCharacter f hk ell hell
  dsimp only at hc
  obtain ⟨u, v, hu, hv, hext, hfin, τ, hmax, heigen⟩ := hc
  letI : UniformSpace L := u
  letI : ValuativeRel L := v
  letI : IsNonarchimedeanLocalField L := hv
  letI : (ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation L) := hext
  exact ⟨u, v, hu, hv, hext, hfin,
    sourceRationalPrimeExtensionResidue_charP ell hell L, inferInstance, τ, hmax, heigen⟩

end
end Dubon2026
