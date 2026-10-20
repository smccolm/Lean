import Dubon2026.PolarizedContinuousFirstOrder
import Dubon2026.PolarizedFramedMatrixFiber
import Dubon2026.RelativeDualNumberResidue
import Dubon2026.DualNumberAdicTopology

/-! The original polarized coefficient fiber over residual dual numbers
is the actual continuous fixed-similitude first-order fiber. The source
residue, base character and topology are compared explicitly; this is the
entry bridge from the already-proved coefficient quotient to the source
full-adjoint tangent classification required by DUB-17. -/

namespace Dubon2026
noncomputable section
open Matrix

/-- The source product and original maximal-adic topologies give the same polarized continuity. -/
theorem dualNumberPolarized_continuous_iff
    (K : Type) [Field K] [TopologicalSpace K] [DiscreteTopology K]
    {X ι : Type} [TopologicalSpace X] [Fintype ι] [DecidableEq ι]
    (f : X → PolarizedGaloisGroup ι (DualNumber K)) :
    (letI : TopologicalSpace (DualNumber K) := (IsLocalRing.maximalIdeal (DualNumber K)).adicTopology
     Continuous f) ↔ Continuous f := by
  rw [dualNumber_maximal_adicTopology_eq K]

variable {O ι : Type} [CommRing O] [IsLocalRing O] [Fintype ι] [DecidableEq ι]

/-- Reduction through the true source residue equivalence is exactly the original polarized first-coordinate reduction. -/
theorem polarizedDual_sourceReduction :
    polarizedCoefficientMap (ι := ι)
      (localCoefficientReduction (relativeDualNumberResidueEquiv O)).toRingHom =
      polarizedDualReduction (R := IsLocalRing.ResidueField O) := by
  apply congrArg (polarizedCoefficientMap (ι := ι))
  apply RingHom.ext
  intro x
  exact relativeDualNumberResidueEquiv_reduction O x

variable (H : ProfiniteGrp) (σ : H →* PolarizedGaloisGroup ι (IsLocalRing.ResidueField O))
  (ν : H →* Oˣ)
  (hν : ∀ g, polarizedSimilitude (σ g) =
    Units.map (algebraMap O (IsLocalRing.ResidueField O)) (ν g))

include hν in
/-- The source base similitude on dual numbers is the actual constant lift of the original residual similitude. -/
theorem polarizedDual_sourceSimilitude :
    (Units.map (algebraMap O (DualNumber (IsLocalRing.ResidueField O)))).comp ν =
      (Units.map (TrivSqZeroExt.inlHom (IsLocalRing.ResidueField O)
        (IsLocalRing.ResidueField O)).toMonoidHom).comp (polarizedSimilitude.comp σ) := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  change algebraMap O (DualNumber (IsLocalRing.ResidueField O)) (ν g).val =
    TrivSqZeroExt.inl (polarizedSimilitude (σ g)).val
  rw [hν g]
  rfl

variable [TopologicalSpace (IsLocalRing.ResidueField O)] [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- The original continuous polarized coefficient fiber is the exact continuous full-adjoint first-order fiber. -/
def originalPolarizedDualFiberEquiv :
    (letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
      ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
     OriginalContinuousPolarizedFiber (relativeDualNumberResidueEquiv O) H σ ν) ≃
      ContinuousPolarizedFirstOrderLift σ where
  toFun τ := by
    letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
      ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
    letI : TopologicalSpace (DualNumber (IsLocalRing.ResidueField O)) :=
      (IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))).adicTopology
    have hr : polarizedDualReduction.comp τ.val.toMonoidHom = σ := by
      simpa only [polarizedDual_sourceReduction] using τ.property.1
    have hm : polarizedSimilitude.comp τ.val.toMonoidHom =
        (Units.map (TrivSqZeroExt.inlHom (IsLocalRing.ResidueField O)
          (IsLocalRing.ResidueField O)).toMonoidHom).comp (polarizedSimilitude.comp σ) := by
      simpa only [polarizedDual_sourceSimilitude H σ ν hν] using τ.property.2
    exact ⟨⟨τ.val.toMonoidHom, hr, hm⟩,
      (dualNumberPolarized_continuous_iff (IsLocalRing.ResidueField O) τ.val.toMonoidHom).mp
        τ.val.continuous⟩
  invFun τ := by
    letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
      ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
    letI : TopologicalSpace (DualNumber (IsLocalRing.ResidueField O)) :=
      (IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))).adicTopology
    refine ⟨⟨τ.val.val,
      (dualNumberPolarized_continuous_iff (IsLocalRing.ResidueField O) τ.val.val).mpr τ.property⟩, ?_, ?_⟩
    · rw [polarizedDual_sourceReduction]
      exact τ.val.property.1
    · rw [polarizedDual_sourceSimilitude H σ ν hν]
      exact τ.val.property.2
  left_inv τ := by
    apply Subtype.ext
    rfl
  right_inv τ := by
    apply Subtype.ext
    rfl

end
end Dubon2026
