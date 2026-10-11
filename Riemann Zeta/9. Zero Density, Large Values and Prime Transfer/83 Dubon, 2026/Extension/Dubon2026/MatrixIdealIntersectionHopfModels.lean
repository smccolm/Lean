import Dubon2026.MatrixIdealQuotientHopfModels
import Dubon2026.FiniteFreeHopfPointModelProduct

/-! # Genuine model closure under intersections of original coefficient ideals -/

namespace Dubon2026
noncomputable section

universe uC uD
open Matrix

variable {A ι : Type*} [CommRing A]

/-- The two genuine quotient transitions embed the original intersection quotient into the original quotient pair. -/
private theorem idealIntersectionQuotientPair_injective (I J : Ideal A) :
    Function.Injective (fun x : A ⧸ (I ⊓ J) =>
      (Ideal.Quotient.factor (show I ⊓ J ≤ I from inf_le_left) x,
       Ideal.Quotient.factor (show I ⊓ J ≤ J from inf_le_right) x)) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h a =>
    induction y using Quotient.inductionOn with
    | h b =>
      intro h
      apply Ideal.Quotient.eq.mpr
      exact ⟨Ideal.Quotient.eq.mp (congrArg Prod.fst h),
        Ideal.Quotient.eq.mp (congrArg Prod.snd h)⟩

/-- The original intersection-quotient vector group maps to the two original quotient vector groups through its actual quotient transitions. -/
def matrixIdealIntersectionVectorMap (I J : Ideal A) :
    Multiplicative (ι → A ⧸ (I ⊓ J)) →*
      Multiplicative (ι → A ⧸ I) × Multiplicative (ι → A ⧸ J) :=
  (matrixCoefficientVectorMap (Ideal.Quotient.factor (show I ⊓ J ≤ I from inf_le_left))).prod
    (matrixCoefficientVectorMap (Ideal.Quotient.factor (show I ⊓ J ≤ J from inf_le_right)))

/-- The actual two quotient projections determine every original intersection-quotient vector. -/
theorem matrixIdealIntersectionVectorMap_injective (I J : Ideal A) :
    Function.Injective (matrixIdealIntersectionVectorMap (ι := ι) I J) := by
  intro v w h
  change Multiplicative.toAdd v = Multiplicative.toAdd w
  funext i
  apply idealIntersectionQuotientPair_injective I J
  exact Prod.ext
    (congrArg (fun x : Multiplicative (ι → A ⧸ I) × Multiplicative (ι → A ⧸ J) =>
      Multiplicative.toAdd x.1 i) h)
    (congrArg (fun x : Multiplicative (ι → A ⧸ I) × Multiplicative (ι → A ⧸ J) =>
      Multiplicative.toAdd x.2 i) h)

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype ι] [DecidableEq ι]

/-- The literal original quotient transitions intertwine the entire same original representation with the product of its two reductions. -/
theorem matrixIdealIntersectionVectorMap_equivariant (I J : Ideal A)
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (g : K ≃ₐ[F] K) (v : Multiplicative (ι → A ⧸ (I ⊓ J))) :
    matrixIdealIntersectionVectorMap I J
        (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation (I ⊓ J) ρ) g v) =
      galoisModuleProductAction
        (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation I ρ))
        (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation J ρ)) g
        (matrixIdealIntersectionVectorMap I J v) := by
  apply Prod.ext
  · have h := matrixCoefficientVectorMap_equivariant
      (Ideal.Quotient.factor (show I ⊓ J ≤ I from inf_le_left))
      (matrixIdealQuotientRepresentation (I ⊓ J) ρ) g v
    rw [matrixIdealQuotientRepresentation_transition] at h
    exact h
  · have h := matrixCoefficientVectorMap_equivariant
      (Ideal.Quotient.factor (show I ⊓ J ≤ J from inf_le_right))
      (matrixIdealQuotientRepresentation (I ⊓ J) ρ) g v
    rw [matrixIdealQuotientRepresentation_transition] at h
    exact h

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [PerfectField F] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]

/-- Models of the two actual reductions construct a model modulo their actual ideal intersection: form their genuine tensor-coordinate product and use the proved equivariant injection of the original intersection quotient. -/
theorem matrixIdealIntersectionHopfModel_exists (I J : Ideal A)
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (mI : FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative (ι → A ⧸ I))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation I ρ)))
    (mJ : FiniteFreeHopfPointModel.{_, _, _, _, uD} R F K (Multiplicative (ι → A ⧸ J))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation J ρ))) :
    Nonempty (FiniteFreeHopfPointModel.{_, _, _, _, max uC uD} R F K (Multiplicative (ι → A ⧸ (I ⊓ J)))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation (I ⊓ J) ρ))) := by
  exact finiteFreeHopfPointModel_of_injective_exists (finiteFreeHopfPointModelProduct mI mJ)
    (matrixIdealIntersectionVectorMap I J) (matrixIdealIntersectionVectorMap_injective I J)
    (matrixIdealIntersectionVectorMap_equivariant I J ρ)

end
end Dubon2026
