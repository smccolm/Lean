import Dubon2026.ArithmeticUniversalAuxiliaryLocalData
import Dubon2026.ArithmeticUniversalAuxiliaryEvaluation
import Dubon2026.ArithmeticOriginalSupportFramedEvaluation
import Dubon2026.OriginalAlgebraicCoefficientFiber
import Dubon2026.FramedCoefficientClassification

/-! The constructed original-support algebraic classification retains
the actual quotient universal matrices as part of the same output.
Both fields are assembled directly from native automatic continuity,
the actual auxiliary quotient classification and proved support descent. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField BigOperators

variable {ι O A : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (ResidueField O)] [TopologicalSpace (ResidueField O)] [DiscreteTopology (ResidueField O)]
  [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [Algebra O A] [WithIdeal A] [IsAdicComplete (maximalIdeal A) A]

/-- The literal quotient of the actual auxiliary-support universal
ring represents all original-support continuous framed lifts with the
specified determinant. No local compatibility, field-unramifiedness,
kernel-containment, lift or classification certificate is supplied. -/
def arithmeticUniversalOriginalSupportAlgebraicClassification
    (hA : (WithIdeal.i : Ideal A) = maximalIdeal A)
    (eA : ResidueField A ≃ₐ[O] ResidueField O)
    (a b : 𝓞 ℚ) (hb : b ≠ 0) (q : ℕ) (hq : q.Prime) (hqb : (q : 𝓞 ℚ) ∣ b)
    [CharP (ResidueField O) q]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) = Units.map (algebraMap O (ResidueField O)) (δ g))
    (Q : Finset Nat.Primes) (hba : b = a * ∏ p ∈ Q, (p.val : 𝓞 ℚ))
    (hab : a ∣ b) (haway : ∀ p : Q, ¬(p.val.val : 𝓞 ℚ) ∣ a) :
    (let π := rationalArithmeticSupportRestriction a b hab
     let σb := σ.comp π.toMonoidHom
     let hσb : Continuous σb := hσ.comp π.continuous
     let δb := δ.comp π.toMonoidHom
     let hδb : ∀ g, GeneralLinearGroup.det (σb g) =
       Units.map (algebraMap O (ResidueField O)) (δb g) := fun g => hδ (π g)
     let hIb : ∀ (p : Q) g, g ∈ rationalPrimeNormInertia p.val.val p.val.property →
       σb (rationalPrimeArithmeticRestriction b p.val.val p.val.property g) = 1 :=
       fun p g hg => rationalArithmeticSupportCharacter_inertia_eq_one a b hab σ
         p.val.val p.val.property (haway p) g hg
     letI := arithmeticAuxiliaryUniversalRing_isLocal b hb q hq hqb σb hσb δb hδb Q hIb
     FramedCoefficientClassification
       (arithmeticAuxiliaryUniversalResidueEquiv b hb q hq hqb σb hσb δb hδb Q hIb) eA
       (rationalArithmeticGaloisGroup a) σ δ π
       (arithmeticAuxiliaryUniversalRepresentation b hb q hq hqb σb hσb δb Q)) := by
  let π := rationalArithmeticSupportRestriction a b hab
  let σb := σ.comp π.toMonoidHom
  let hσb : Continuous σb := hσ.comp π.continuous
  let δb := δ.comp π.toMonoidHom
  let hδb : ∀ g, GeneralLinearGroup.det (σb g) =
      Units.map (algebraMap O (ResidueField O)) (δb g) := fun g => hδ (π g)
  let hIb : ∀ (p : Q) g, g ∈ rationalPrimeNormInertia p.val.val p.val.property →
      σb (rationalPrimeArithmeticRestriction b p.val.val p.val.property g) = 1 :=
    fun p g hg => rationalArithmeticSupportCharacter_inertia_eq_one a b hab σ
      p.val.val p.val.property (haway p) g hg
  letI := arithmeticAuxiliaryUniversalRing_isLocal b hb q hq hqb σb hσb δb hδb Q hIb
  letI : IsHausdorff (WithIdeal.i : Ideal A) A := hA.symm ▸ inferInstance
  letI : T2Space A := (IsAdic.isHausdorff_iff (I := (WithIdeal.i : Ideal A)) rfl).mp inferInstance
  have htopA : (inferInstance : TopologicalSpace A) = (maximalIdeal A).adicTopology :=
    congrArg Ideal.adicTopology hA
  let C := originalAlgebraicContinuousCoefficientFiberEquiv
    (arithmeticAuxiliaryUniversalRing_localData b hb q hq hqb σb hσb δb hδb Q hIb).2.2 htopA
    (arithmeticAuxiliaryUniversalResidueEquiv b hb q hq hqb σb hσb δb hδb Q hIb) eA
  let Eaux := arithmeticUniversalAuxiliaryFramedFiberEquiv hA eA b hb q hq hqb σb hσb δb hδb Q hIb
  let Edes := arithmeticOriginalSupportFramedFiberEquiv eA a b hb Q hba hab haway σ δ
  refine ⟨(C.trans Eaux).trans Edes.symm, ?_⟩
  intro f g
  exact (arithmeticOriginalSupportFramedFiberEquiv_symm_apply eA a b hb Q hba hab haway σ δ
    (Eaux (C f)) g).trans
    (arithmeticUniversalAuxiliaryFramedFiberEquiv_evaluation hA eA b hb q hq hqb σb hσb δb hδb Q hIb (C f) g)

end
end Dubon2026
