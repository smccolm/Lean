import Dubon2026.SourceGammaOneLocalArithmeticRankTwo
import Dubon2026.SourcePrimitiveResidualCharacteristic

/-! DUB-17/18 -> original all-weight association -> actual arithmetic rank-two realization.
The original primitive form constructs its genuine finite local coefficient
field and a continuous representation of the prescribed arithmetic group.
Original norm Frobenius values and complex oddness are retained. All trace,
algebra, matrix, kernel and continuity inputs are derived. The remaining
local/image/regularity and higher continuation obligations stay separate. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open scoped ValuativeRel NumberField
attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField
local notation "Qbar" => AlgebraicClosure ℚ
private local instance : IsGalois ℚ Qbar := sourceRationalAlgebraicClosure_isGalois
variable (Q p : ℕ) [NeZero Q] [Fact p.Prime] {k : ℤ}

/-- The original primitive form constructs the local coefficient field and
its continuous arithmetic rank-two representation, with exact original
Fourier traces, weight determinants and complex oddness. -/
theorem exists_gammaOne_original_arithmetic_rankTwo
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
      ∃ η : rationalArithmeticGaloisGroup ((Q * p : ℕ) : 𝓞 ℚ) →ₜ*
        Matrix.GeneralLinearGroup (Fin 2) L,
        (∀ (q : ℕ) (hq : q.Prime), ¬q ∣ Q * p →
          ∀ (e : Qbar →ₐ[ℚ] rationalPrimeLocalClosure q hq)
            (φ : Gal(rationalPrimeLocalClosure q hq/rationalPrimeLocalField q hq)),
            (∀ z : IsLocalRing.ResidueField (algebraicLocalIntegerRing
              (rationalPrimeLocalClosure q hq)), φ • z = z ^ q) →
            Matrix.trace (η (sourceAbsoluteArithmeticRestriction ((Q * p : ℕ) : 𝓞 ℚ)
                (embeddedNormalGaloisRestriction e φ))).val =
              τ (sourcePrimitiveFieldCoefficient f q) ∧
            (η (sourceAbsoluteArithmeticRestriction ((Q * p : ℕ) : 𝓞 ℚ)
                (embeddedNormalGaloisRestriction e φ))).val.det = (q : L) ^ Int.toNat (k - 1)) ∧
        (∀ e : Qbar →ₐ[ℚ] ℂ,
          (η (sourceAbsoluteArithmeticRestriction ((Q * p : ℕ) : 𝓞 ℚ)
            (sourceAbsoluteComplexConjugation e))).val.det = -1 ∧
          Matrix.trace (η (sourceAbsoluteArithmeticRestriction ((Q * p : ℕ) : 𝓞 ℚ)
            (sourceAbsoluteComplexConjugation e))).val = 0) := by
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
    exists_gammaOne_original_local_arithmetic_rankTwo Q p f hk hlarge τ⟩

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
