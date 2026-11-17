import Dubon2026.SourceOriginalAdicDeterminant
import Dubon2026.SourceAdicQuotientContinuity

/-! DUB-17/18 -> actual rank-two realization -> original odd determinant.
The actual complete coefficient-ring determinant is compared at every
positive precision with the original cyclotomic character, then native
adic separation proves its exact value at actual complex conjugation. -/
namespace Dubon2026
noncomputable section
attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField
local notation "Qbar" => AlgebraicClosure ℚ
private local instance : IsGalois ℚ Qbar := sourceRationalAlgebraicClosure_isGalois
variable {R : Type} [CommRing R] [IsLocalRing R]
  [TopologicalSpace R] [IsTopologicalRing R]
variable (Q p w : ℕ) [NeZero Q] [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p]

/-- The original good-prime determinant values force the exact complex
conjugation value in the actual separated adic coefficient ring. -/
theorem originalLocalDeterminant_conjugation
    [IsHausdorff (IsLocalRing.maximalIdeal R) R]
    (hI : IsAdic (IsLocalRing.maximalIdeal R))
    (D : (Qbar ≃ₐ[ℚ] Qbar) →* R) (hD : Continuous D)
    (hFrob : ∀ (q : ℕ) (hq : q.Prime), ¬q ∣ Q * p →
      ∀ (e : Qbar →ₐ[ℚ] rationalPrimeLocalClosure q hq)
        (φ : Gal(rationalPrimeLocalClosure q hq/rationalPrimeLocalField q hq)),
        (∀ z : IsLocalRing.ResidueField (algebraicLocalIntegerRing
          (rationalPrimeLocalClosure q hq)), φ • z = z ^ q) →
        D (embeddedNormalGaloisRestriction e φ) = (q : R) ^ w)
    (e : Qbar →ₐ[ℚ] ℂ) :
    D (sourceAbsoluteComplexConjugation e) = (-1 : R) ^ w := by
  apply positiveAdic_ext (IsLocalRing.maximalIdeal R)
  intro n
  let π := Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R) ^ (n + 1))
  let Dn := π.toMonoidHom.comp D
  letI : TopologicalSpace (R ⧸ (IsLocalRing.maximalIdeal R) ^ (n + 1)) := ⊥
  have hDn : @Continuous _ _ _ ⊥ Dn :=
    (continuous_positive_adic_quotient (IsLocalRing.maximalIdeal R) hI n).comp hD
  have hFn : ∀ (q : ℕ) (hq : q.Prime), ¬q ∣ Q * p →
      ∀ (i : Qbar →ₐ[ℚ] rationalPrimeLocalClosure q hq)
        (φ : Gal(rationalPrimeLocalClosure q hq/rationalPrimeLocalField q hq)),
        (∀ z : IsLocalRing.ResidueField (algebraicLocalIntegerRing
          (rationalPrimeLocalClosure q hq)), φ • z = z ^ q) →
        Dn (embeddedNormalGaloisRestriction i φ) =
          (q : R ⧸ (IsLocalRing.maximalIdeal R) ^ (n + 1)) ^ w := by
    intro q hq ha i φ hφ
    change π (D _) = _
    rw [hFrob q hq ha i φ hφ, map_pow, map_natCast]
  have he := originalAdicDeterminant_eq_cyclotomic Q p n w Dn hDn hFn
  have hc := congrArg (fun d => d (sourceAbsoluteComplexConjugation e)) he
  dsimp only at hc
  rw [sourceAdicCyclotomicDeterminant_conjugation] at hc
  change π (D (sourceAbsoluteComplexConjugation e)) = (-1) ^ w at hc
  simpa only [map_pow, map_neg, map_one] using hc

end
end Dubon2026
