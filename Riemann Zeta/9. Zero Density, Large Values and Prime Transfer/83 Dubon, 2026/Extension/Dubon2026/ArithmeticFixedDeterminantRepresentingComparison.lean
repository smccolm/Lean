import Dubon2026.ArithmeticFixedDeterminantSupportClassification
import Dubon2026.FramedCoefficientUniversalRingComparison

/-! Specialize the proved inverse-map construction to the actual base
ring first. The second representing ring remains abstract here and is
supplied by the actual auxiliary quotient in the arithmetic consumer. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField

/-- The genuine original-support ring is identified with any complete
local ring carrying the proved same framed classification and matrix
evaluation. The arithmetic consumer constructs that classification. -/
def arithmeticFixedDeterminantRepresentingComparison
    {ι O S : Type} [Fintype ι] [DecidableEq ι]
    [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [Finite (ResidueField O)] [TopologicalSpace (ResidueField O)] [DiscreteTopology (ResidueField O)]
    [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [Algebra O S]
    [WithIdeal S] [IsAdicComplete (maximalIdeal S) S]
    (hS : (WithIdeal.i : Ideal S) = maximalIdeal S)
    (eS : ResidueField S ≃ₐ[O] ResidueField O)
    (a : 𝓞 ℚ) (ha : a ≠ 0) (q : ℕ) (hq : q.Prime) (hqa : (q : 𝓞 ℚ) ∣ a)
    [CharP (ResidueField O) q]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) = Units.map (algebraMap O (ResidueField O)) (δ g))
    (b : 𝓞 ℚ) (hab : a ∣ b)
    (τS : rationalArithmeticGaloisGroup b → GeneralLinearGroup ι S)
    (FS : ∀ {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      [Algebra O A] [WithIdeal A] [IsAdicComplete (maximalIdeal A) A]
      (_hA : (WithIdeal.i : Ideal A) = maximalIdeal A)
      (eA : ResidueField A ≃ₐ[O] ResidueField O),
      FramedCoefficientClassification eS eA (rationalArithmeticGaloisGroup a) σ δ
        (rationalArithmeticSupportRestriction a b hab) τS) :
    (letI := arithmeticFixedDeterminantRing_isLocal a ha q hq hqa σ hσ δ hδ
     ResidueMatrixRingComparison
       (arithmeticFixedDeterminantResidueEquiv a ha q hq hqa σ hσ δ hδ) eS
       (fun g => arithmeticFixedDeterminantRepresentation a ha q hq hqa σ hσ δ
         (rationalArithmeticSupportRestriction a b hab g)) τS) := by
  let R := ArithmeticFixedDeterminantRing a ha q hq hqa σ hσ δ
  letI := arithmeticFixedDeterminantRing_isLocal a ha q hq hqa σ hσ δ hδ
  have hR := arithmeticFixedDeterminantRing_localData a ha q hq hqa σ hσ δ hδ
  letI := hR.1
  letI := hR.2.1
  letI : WithIdeal R := ⟨maximalIdeal R⟩
  exact framedCoefficientUniversalRingComparison (O := O) (R := R) (S := S)
    rfl hS (arithmeticFixedDeterminantResidueEquiv a ha q hq hqa σ hσ δ hδ) eS
    (rationalArithmeticGaloisGroup a) (rationalArithmeticSupportRestriction a b hab)
    (rationalArithmeticSupportRestriction_surjective a b hab) σ δ
    (fun g => arithmeticFixedDeterminantRepresentation a ha q hq hqa σ hσ δ
      (rationalArithmeticSupportRestriction a b hab g)) τS
    (fun {A} _ _ _ _ _ _ hA eA =>
      arithmeticFixedDeterminantSupportAlgebraicClassification (O := O) (A := A)
        hA eA a ha q hq hqa σ hσ δ hδ b hab) FS

end
end Dubon2026
