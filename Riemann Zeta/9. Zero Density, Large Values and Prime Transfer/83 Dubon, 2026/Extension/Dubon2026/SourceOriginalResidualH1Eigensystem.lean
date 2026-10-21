import Dubon2026.SourceBinaryH1HeckeCommute
import Dubon2026.SourcePrimitiveResidualH1Eigensystem

/-! The original primitive residual binary H1 eigensystem with Hecke commutativity proved.
DUB-17/18 -> residual modular Galois association -> finite-characteristic weight/level
reduction -> the actual nonzero residual H1 eigenclass. Every source primitive
form of weight at least two and every prescribed rational prime are retained.
This proves the required residual cohomological input, not yet the geometric
Galois association, purity, crystallinity or higher symmetric-power continuation.
-/

namespace Dubon2026
noncomputable section
open scoped ValuativeRel
variable {Q : ℕ} [NeZero Q] {k : ℤ}

/-- The original primitive form and local coefficient embedding supply a nonzero residual H1 eigenclass with all original good-prime eigenvalues. Integral Hecke commutativity, character realization, tensor nonvanishing and injective coefficient change are all proved. -/
theorem sourcePrimitive_exists_residualH1Eigensystem
    {E : Type} [Field E] [CharZero E] [ValuativeRel E]
    {K : Type} [Field K] [IsAlgClosed K] [Algebra 𝓀[E] K]
    (ell : ℕ) (hell : ell.Prime) [CharP K ell]
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E) :
    ∃ x : groupCohomology.H1 (sourceBinaryCoefficientRep K Q (k - 2).toNat),
      x ≠ 0 ∧ ∀ p : sourceBinaryHeckePrime Q,
        sourceBinaryH1PrimeOperators K Q (k - 2).toNat p x =
          algebraMap 𝓀[E] K (sourcePrimitiveResidualHeckeCharacter f hk τ
            ⟨cuspHeckeLinear Q k p.val, Algebra.subset_adjoin
              ⟨(⟨p.val, p.property.1.pos⟩ : ℕ+), rfl⟩⟩) • x := by
  exact sourcePrimitive_exists_residualH1Eigensystem_of_commute ell hell f hk
    (sourceBinaryH1PrimeOperators_commute ℤ Q (k - 2).toNat) τ

/-- At every prescribed rational prime, every original primitive form of weight at least two supplies its genuine local coefficient field and a nonzero residual native binary H1 eigensystem with the original Fourier reductions. No commutativity or residual eigenclass hypothesis remains. -/
theorem sourcePrimitive_exists_residualH1Eigensystem_charP
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (ell : ℕ) (hell : ell.Prime) :
    letI := sourcePrimitiveCoefficientField_numberField f hk
    letI := rationalPrimeLocalField_charZero ell hell
    let F := rationalPrimeLocalField ell hell
    let L := commonCoefficientField (sourcePrimitiveCoefficientField f) F
    ∃ (_ : UniformSpace L) (_ : ValuativeRel L),
      letI : Algebra 𝓀[L] (AlgebraicClosure 𝓀[L]) :=
        @AlgebraicClosure.instAlgebra 𝓀[L] _ 𝓀[L] _ (Algebra.id 𝓀[L])
      IsUniformAddGroup L ∧ IsNonarchimedeanLocalField L ∧
      (ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation L) ∧
      FiniteDimensional F L ∧ Finite 𝓀[L] ∧
      CharP (AlgebraicClosure 𝓀[L]) ell ∧
      ∃ (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] L)
        (x : groupCohomology.H1
          (sourceBinaryCoefficientRep (AlgebraicClosure 𝓀[L]) Q (k - 2).toNat)),
        x ≠ 0 ∧ ∀ p : sourceBinaryHeckePrime Q,
          sourceBinaryH1PrimeOperators (AlgebraicClosure 𝓀[L]) Q (k - 2).toNat p x =
            algebraMap 𝓀[L] (AlgebraicClosure 𝓀[L])
              (sourcePrimitiveResidualHeckeCharacter f hk τ
                ⟨cuspHeckeLinear Q k p.val, Algebra.subset_adjoin
                  ⟨(⟨p.val, p.property.1.pos⟩ : ℕ+), rfl⟩⟩) • x := by
  exact sourcePrimitive_exists_residualH1Eigensystem_charP_of_commute f hk ell hell
    (sourceBinaryH1PrimeOperators_commute ℤ Q (k - 2).toNat)

end
end Dubon2026
