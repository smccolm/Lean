import Dubon2026.SourceGammaOneOriginalLocalTrace
import Dubon2026.SourceOriginalLocalDeterminant
import Dubon2026.SourcePrimitiveWeightParity

/-! DUB-17/18 -> actual rank-two realization -> actual source oddness.
The original primitive form supplies even weight, and the proved original
norm-Frobenius comparison supplies the full cyclotomic determinant value.
Thus oddness at actual complex conjugation is discharged from the source. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open scoped ValuativeRel
attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField
local notation "Qbar" => AlgebraicClosure ℚ
private local instance : IsGalois ℚ Qbar := sourceRationalAlgebraicClosure_isGalois
variable (Q p : ℕ) [NeZero Q] [Fact p.Prime] {k : ℤ}

/-- The original primitive form and its exact good-prime determinant values
force oddness at actual complex conjugation in the actual local ring. -/
theorem originalPrimitiveLocalDeterminant_odd
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    {E : Type} [Field E] [CharZero E] [ValuativeRel E] [UniformSpace E]
    [IsUniformAddGroup E] [IsNonarchimedeanLocalField E] [CharP 𝓀[E] p]
    (D : (Qbar ≃ₐ[ℚ] Qbar) →* 𝒪[E]) (hD : Continuous D)
    (hFrob : ∀ (q : ℕ) (hq : q.Prime), ¬q ∣ Q * p →
      ∀ (e : Qbar →ₐ[ℚ] rationalPrimeLocalClosure q hq)
        (φ : Gal(rationalPrimeLocalClosure q hq/rationalPrimeLocalField q hq)),
        (∀ z : IsLocalRing.ResidueField (algebraicLocalIntegerRing
          (rationalPrimeLocalClosure q hq)), φ • z = z ^ q) →
        D (embeddedNormalGaloisRestriction e φ) = (q : 𝒪[E]) ^ Int.toNat (k - 1))
    (e : Qbar →ₐ[ℚ] ℂ) : D (sourceAbsoluteComplexConjugation e) = -1 := by
  rw [originalLocalDeterminant_conjugation Q p (k - 1).toNat
    compactSeparatedLocalRing_isAdic D hD hFrob e]
  have hodd : Odd (k - 1).toNat := by
    obtain ⟨n, hn⟩ := sourcePrimitive_binaryDegree_even f hk
    exact ⟨n, by omega⟩
  exact hodd.neg_one_pow

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
