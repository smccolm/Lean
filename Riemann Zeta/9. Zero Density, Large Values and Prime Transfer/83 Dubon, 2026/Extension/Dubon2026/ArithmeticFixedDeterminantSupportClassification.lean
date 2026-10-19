import Dubon2026.ArithmeticFixedDeterminantAlgebraicFiber
import Dubon2026.ArithmeticSupportRestriction
import Dubon2026.FramedCoefficientClassification

/-! The original fixed-determinant classification retains its
universal-matrix evaluation along actual arithmetic support restriction.
It supplies the two original-ring coefficient targets in the actual
auxiliary quotient ring isomorphism. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField

/-- Construct the original coefficient classification and its full
matrix evaluation along the actual support map as one checked output. -/
def arithmeticFixedDeterminantSupportAlgebraicClassification
    {ι O A : Type} [Fintype ι] [DecidableEq ι]
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
    (b : 𝓞 ℚ) (hab : a ∣ b) :
    (letI := arithmeticFixedDeterminantRing_isLocal a ha q hq hqa σ hσ δ hδ
     FramedCoefficientClassification
       (arithmeticFixedDeterminantResidueEquiv a ha q hq hqa σ hσ δ hδ) eA
       (rationalArithmeticGaloisGroup a) σ δ (rationalArithmeticSupportRestriction a b hab)
       (fun g => arithmeticFixedDeterminantRepresentation a ha q hq hqa σ hσ δ
         (rationalArithmeticSupportRestriction a b hab g))) := by
  letI := arithmeticFixedDeterminantRing_isLocal a ha q hq hqa σ hσ δ hδ
  refine ⟨arithmeticFixedDeterminantAlgebraicFiberEquiv hA eA a ha q hq hqa σ hσ δ hδ, ?_⟩
  intro f g
  exact arithmeticFixedDeterminantAlgebraicFiberEquiv_evaluation hA eA
    a ha q hq hqa σ hσ δ hδ f (rationalArithmeticSupportRestriction a b hab g)

end
end Dubon2026
