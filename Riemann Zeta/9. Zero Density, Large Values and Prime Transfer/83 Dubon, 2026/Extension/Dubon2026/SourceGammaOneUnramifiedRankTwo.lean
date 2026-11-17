import Dubon2026.SourceGammaOneLocalUnramifiedRankTwo
import Dubon2026.SourcePrimitiveResidualCharacteristic

/-! DUB-17/18 -> original all-weight association -> actual rank-two realization.
The original primitive form constructs a genuine finite local coefficient
field and a continuous two-dimensional representation with its exact
Fourier traces and weight determinants at every original good-prime norm
Frobenius. Actual conjugation is odd. No trace, algebra, matrix action,
basis or continuity certificate is supplied. Its norm-inertia action outside Q*p is trivial. Further local conditions,
exceptional primes and the higher continuation chain remain separate. -/
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

/-- The original primitive cusp form constructs its actual continuous rank-two
representation over a genuine finite local coefficient field, with exact
original norm-Frobenius trace and determinant actual complex oddness and trivial norm-inertia action outside Q*p. -/
theorem exists_gammaOne_original_unramified_rankTwo
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (hlarge : 3 < p) :
    letI := sourcePrimitiveCoefficientField_numberField f hk
    letI := rationalPrimeLocalField_charZero p (Fact.out : p.Prime)
    let F := rationalPrimeLocalField p (Fact.out : p.Prime)
    let L := commonCoefficientField (sourcePrimitiveCoefficientField f) F
    ∃ (u : UniformSpace L) (_ : ValuativeRel L),
      letI : TopologicalSpace L := u.toTopologicalSpace
      IsUniformAddGroup L ∧ IsNonarchimedeanLocalField L ∧
      (ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation L) ∧
      FiniteDimensional F L ∧ CharP 𝓀[L] p ∧
      ∃ τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] L,
      ∃ ρ : (Qbar ≃ₐ[ℚ] Qbar) →* Matrix.GeneralLinearGroup (Fin 2) L,
        Continuous ρ ∧
        (∀ (q : ℕ) (hq : q.Prime), ¬q ∣ Q * p →
          ∀ (e : Qbar →ₐ[ℚ] rationalPrimeLocalClosure q hq)
            (φ : Gal(rationalPrimeLocalClosure q hq/rationalPrimeLocalField q hq)),
            (∀ z : IsLocalRing.ResidueField (algebraicLocalIntegerRing
              (rationalPrimeLocalClosure q hq)), φ • z = z ^ q) →
            Matrix.trace (ρ (embeddedNormalGaloisRestriction e φ)).val =
              τ (sourcePrimitiveFieldCoefficient f q) ∧
            (ρ (embeddedNormalGaloisRestriction e φ)).val.det = (q : L) ^ Int.toNat (k - 1)) ∧
        (∀ e : Qbar →ₐ[ℚ] ℂ,
          (ρ (sourceAbsoluteComplexConjugation e)).val.det = -1 ∧
          Matrix.trace (ρ (sourceAbsoluteComplexConjugation e)).val = 0) ∧
        ∀ (q : ℕ) (hq : q.Prime), ¬q ∣ Q * p →
          ∀ (e : Qbar →ₐ[ℚ] rationalPrimeLocalClosure q hq)
            (g : Gal(rationalPrimeLocalClosure q hq/rationalPrimeLocalField q hq)),
            g ∈ rationalPrimeNormInertia q hq → ρ (embeddedNormalGaloisRestriction e g) = 1 := by
  letI := sourcePrimitiveCoefficientField_numberField f hk
  letI := rationalPrimeLocalField_charZero p (Fact.out : p.Prime)
  let F := rationalPrimeLocalField p (Fact.out : p.Prime)
  let L := commonCoefficientField (sourcePrimitiveCoefficientField f) F
  have hc := sourcePrimitiveCoefficient_exists_local_structure f hk p (Fact.out : p.Prime)
  dsimp only at hc
  obtain ⟨u, v, hu, hv, hext, hfin, _⟩ := hc
  letI : UniformSpace L := u
  letI : TopologicalSpace L := u.toTopologicalSpace
  letI : ValuativeRel L := v
  letI : IsUniformAddGroup L := hu
  letI : IsNonarchimedeanLocalField L := hv
  letI : (ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation L) := hext
  letI : CharP 𝓀[L] p := sourceRationalPrimeExtensionResidue_charP p (Fact.out : p.Prime) L
  let σ : sourcePrimitiveCoefficientField f →ₐ[ℚ] AlgebraicClosure F := IsAlgClosed.lift
  let τ := commonCoefficientEmbedding (sourcePrimitiveCoefficientField f) F σ
  exact ⟨u, v, hu, hv, hext, hfin, inferInstance, τ,
    exists_gammaOne_original_local_unramified_rankTwo Q p f hk hlarge τ⟩

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
