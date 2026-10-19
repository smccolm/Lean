import Dubon2026.OriginalAlgebraicCoefficientFiber
import Dubon2026.ArithmeticFixedDeterminantRepresentation

/-! Algebraic coefficient maps into a complete local ring retain the
actual fixed-determinant framed classification and matrix evaluation.
Automatic continuity discharges the original source-topology condition. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField

variable {ι O A : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (ResidueField O)] [TopologicalSpace (ResidueField O)] [DiscreteTopology (ResidueField O)]
  [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [Algebra O A] [WithIdeal A] [IsAdicComplete (maximalIdeal A) A]
  (hA : (WithIdeal.i : Ideal A) = maximalIdeal A)
  (eA : ResidueField A ≃ₐ[O] ResidueField O)
  (a : 𝓞 ℚ) (ha : a ≠ 0) (q : ℕ) (hq : q.Prime) (hqa : (q : 𝓞 ℚ) ∣ a)
  [CharP (ResidueField O) q]
  (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (ResidueField O))
  (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
  (hδ : ∀ g, GeneralLinearGroup.det (σ g) = Units.map (algebraMap O (ResidueField O)) (δ g))

/-- All actual residue-preserving algebraic maps from the original
fixed-determinant ring classify exactly the original framed lifts. -/
def arithmeticFixedDeterminantAlgebraicFiberEquiv :
    (letI := arithmeticFixedDeterminantRing_isLocal a ha q hq hqa σ hσ δ hδ
     {f : ArithmeticFixedDeterminantRing a ha q hq hqa σ hσ δ →ₐ[O] A //
       (localCoefficientReduction eA).comp f = localCoefficientReduction
         (arithmeticFixedDeterminantResidueEquiv a ha q hq hqa σ hσ δ hδ)} ≃
       {f : OriginalContinuousFramedFiber eA (rationalArithmeticGaloisGroup a) σ //
         ∀ g, GeneralLinearGroup.det (f.val g) = Units.map (algebraMap O A) (δ g)}) := by
  letI := arithmeticFixedDeterminantRing_isLocal a ha q hq hqa σ hσ δ hδ
  have htopA : (inferInstance : TopologicalSpace A) = (maximalIdeal A).adicTopology :=
    congrArg Ideal.adicTopology hA
  exact (originalAlgebraicContinuousCoefficientFiberEquiv
    (arithmeticFixedDeterminantRing_localData a ha q hq hqa σ hσ δ hδ).2.2 htopA
    (arithmeticFixedDeterminantResidueEquiv a ha q hq hqa σ hσ δ hδ) eA).trans
      (arithmeticFixedDeterminantFramedFiberEquiv hA eA a ha q hq hqa σ hσ δ hδ)

/-- The algebraic classification evaluates the same entire actual
universal representation, with no change of coefficients or frames. -/
theorem arithmeticFixedDeterminantAlgebraicFiberEquiv_evaluation :
    (letI := arithmeticFixedDeterminantRing_isLocal a ha q hq hqa σ hσ δ hδ
     ∀ f g, (arithmeticFixedDeterminantAlgebraicFiberEquiv hA eA a ha q hq hqa σ hσ δ hδ f).val.val g =
       GeneralLinearGroup.map f.val.toRingHom
         (arithmeticFixedDeterminantRepresentation a ha q hq hqa σ hσ δ g)) := by
  intro f g
  rfl

end
end Dubon2026
