import Dubon2026.SourcePrimitiveFieldHeckeCharacter
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Actual reduction of the original primitive Hecke eigensystem.
DUB-17/18 -> modular Galois association -> prescribed integral and residual
Hecke eigenvalues. The constructed coefficient number field supplies these
values in an actual local valuation ring; its finite residue field makes
the original residual eigencharacter kernel maximal. This is an eigensystem,
not a Galois action or nonzero prescribed unitary Hecke localization.
-/

namespace Dubon2026
noncomputable section
open scoped ValuativeRel
variable {Q : ℕ} [NeZero Q] {k : ℤ}
variable {E : Type} [Field E] [CharZero E] [ValuativeRel E]

/-- All original integral Hecke eigenvalues land in the actual local valuation ring. -/
def sourcePrimitiveLocalHeckeCharacter (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E) :
    sourceOriginalIntegralHeckeAlgebra Q k →+* 𝒪[E] :=
  (τ.toRingHom.comp (sourcePrimitiveFieldHeckeCharacter f).toRingHom).codRestrict
    (ValuativeRel.valuation E).integer (fun T => by
      have hi := (sourcePrimitiveFieldHeckeCharacter_isIntegral f hk T).map
        (τ.restrictScalars ℤ)
      exact (Valuation.integer.integers (ValuativeRel.valuation E)).isIntegral_iff_v_le_one.mp
        hi.tower_top)

/-- Original local Hecke values recover the given embedding of the exact field-valued eigensystem. -/
theorem sourcePrimitiveLocalHeckeCharacter_coe (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
    (T : sourceOriginalIntegralHeckeAlgebra Q k) :
    (sourcePrimitiveLocalHeckeCharacter f hk τ T : E) =
      τ (sourcePrimitiveFieldHeckeCharacter f T) := rfl

/-- The actual primitive Hecke character reduced in the original local residue field. -/
def sourcePrimitiveResidualHeckeCharacter (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E) :
    sourceOriginalIntegralHeckeAlgebra Q k →+* 𝓀[E] :=
  (IsLocalRing.residue 𝒪[E]).comp (sourcePrimitiveLocalHeckeCharacter f hk τ)

/-- At each positive original Hecke index the residue character is the reduction of the actual original Fourier coefficient. -/
theorem sourcePrimitiveResidualHeckeCharacter_hecke (f : PrimitiveCuspForm Q k)
    (hk : 2 ≤ k) (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E) (n : ℕ+) :
    sourcePrimitiveResidualHeckeCharacter f hk τ
      ⟨cuspHeckeLinear Q k n, Algebra.subset_adjoin ⟨n, rfl⟩⟩ =
        IsLocalRing.residue 𝒪[E]
          ⟨τ (sourcePrimitiveFieldCoefficient f n),
            sourcePrimitiveCoefficient_valuation_le_one f hk τ n⟩ := by
  apply congrArg (IsLocalRing.residue 𝒪[E])
  apply Subtype.ext
  change τ (sourcePrimitiveFieldHeckeCharacter f
    ⟨cuspHeckeLinear Q k n, Algebra.subset_adjoin ⟨n, rfl⟩⟩) = _
  rw [sourcePrimitiveFieldHeckeCharacter_hecke]

/-- The actual residual eigensystem has finite image in every genuine local coefficient field. -/
theorem sourcePrimitiveResidualHeckeCharacter_range_finite
    [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E) :
    Finite (sourcePrimitiveResidualHeckeCharacter f hk τ).range := inferInstance

/-- The exact residual primitive Hecke eigencharacter defines a maximal ideal of the original integral Hecke algebra. -/
theorem sourcePrimitiveResidualHeckeCharacter_ker_isMaximal
    [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E) :
    (RingHom.ker (sourcePrimitiveResidualHeckeCharacter f hk τ)).IsMaximal := by
  let χ := sourcePrimitiveResidualHeckeCharacter f hk τ
  letI := sourcePrimitiveResidualHeckeCharacter_range_finite f hk τ
  letI : Field χ.range := (Finite.isField_of_domain χ.range).toField
  rw [← RingHom.ker_rangeRestrict χ]
  exact RingHom.ker_isMaximal_of_surjective χ.rangeRestrict χ.rangeRestrict_surjective

/-- At every original rational prime the original primitive form has a realized residual Hecke eigensystem in a finite genuine local coefficient extension, with its exact Fourier values and maximal kernel. -/
theorem sourcePrimitive_exists_residualHeckeCharacter
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (ell : ℕ) (hell : ell.Prime) :
    letI := sourcePrimitiveCoefficientField_numberField f hk
    letI := rationalPrimeLocalField_charZero ell hell
    let F := rationalPrimeLocalField ell hell
    let L := commonCoefficientField (sourcePrimitiveCoefficientField f) F
    ∃ (_ : UniformSpace L) (_ : ValuativeRel L),
      IsUniformAddGroup L ∧ IsNonarchimedeanLocalField L ∧
      (ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation L) ∧
      FiniteDimensional F L ∧
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
  have hc := sourcePrimitiveCoefficient_exists_local_structure f hk ell hell
  dsimp only at hc
  obtain ⟨u, v, hu, hv, hext, hfin, _⟩ := hc
  letI : UniformSpace L := u
  letI : ValuativeRel L := v
  letI : IsNonarchimedeanLocalField L := hv
  let σ : sourcePrimitiveCoefficientField f →ₐ[ℚ] AlgebraicClosure F := IsAlgClosed.lift
  let τ := commonCoefficientEmbedding (sourcePrimitiveCoefficientField f) F σ
  exact ⟨u, v, hu, hv, hext, hfin, τ,
    sourcePrimitiveResidualHeckeCharacter_ker_isMaximal f hk τ,
    sourcePrimitiveResidualHeckeCharacter_hecke f hk τ⟩

end
end Dubon2026
