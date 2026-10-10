import Dubon2026.OriginalResidualFramedFibers
import Dubon2026.DualNumberOriginalResidue
import Dubon2026.DualNumberAdicTopology
import Dubon2026.ContinuousFirstOrderDeformation

/-! # The original dual-number framed fiber and genuine continuous first-order lifts -/

namespace Dubon2026

noncomputable section
open Matrix

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [TopologicalSpace K] [DiscreteTopology K]

/-- The true dual-number residue field and original maximal-adic topology identify the entire original framed fiber with the genuine continuous first-order lifts in the original product topology. -/
def originalDualNumberFramedFiberEquiv
    (H : ProfiniteGrp) (ρ : H →* GeneralLinearGroup ι K) :
    {τ : MatrixFirstOrderLift ρ // Continuous τ.val} ≃
      (letI : WithIdeal (DualNumber K) := ⟨IsLocalRing.maximalIdeal (DualNumber K)⟩
       OriginalContinuousFramedFiber (dualNumberOriginalResidueEquiv K) H
         ((GeneralLinearGroup.map (n := ι) (IsLocalRing.residue K)).comp ρ)) where
  toFun τ := by
    letI : WithIdeal (DualNumber K) := ⟨IsLocalRing.maximalIdeal (DualNumber K)⟩
    letI : TopologicalSpace (DualNumber K) :=
      (IsLocalRing.maximalIdeal (DualNumber K)).adicTopology
    refine ⟨⟨τ.val.val, (dualNumberGL_continuous_iff K τ.val.val).mpr τ.property⟩, ?_⟩
    apply MonoidHom.ext
    intro g
    apply Units.ext
    apply Matrix.ext
    intro i j
    have hτ := congrArg (fun v : GeneralLinearGroup ι K => v.val i j)
      (DFunLike.congr_fun τ.val.property g)
    exact (dualNumberOriginalResidueEquiv_reduction K ((τ.val.val g).val i j)).trans
      (congrArg (IsLocalRing.residue K) hτ)
  invFun f := by
    letI : WithIdeal (DualNumber K) := ⟨IsLocalRing.maximalIdeal (DualNumber K)⟩
    letI : TopologicalSpace (DualNumber K) :=
      (IsLocalRing.maximalIdeal (DualNumber K)).adicTopology
    refine ⟨⟨f.val.toMonoidHom, ?_⟩, (dualNumberGL_continuous_iff K f.val).mp f.val.continuous⟩
    apply MonoidHom.ext
    intro g
    apply Units.ext
    apply Matrix.ext
    intro i j
    apply (IsLocalRing.residue K).injective
    have hf := congrArg (fun v : GeneralLinearGroup ι (IsLocalRing.ResidueField K) => v.val i j)
      (DFunLike.congr_fun f.property g)
    exact (dualNumberOriginalResidueEquiv_reduction K ((f.val g).val i j)).symm.trans hf
  left_inv τ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv f := by
    apply Subtype.ext
    apply DFunLike.ext
    intro g
    rfl

/-- The original dual-number framed comparison is bijective on the whole genuine continuous first-order fiber. -/
theorem originalDualNumberFramedFiberEquiv_bijective
    (H : ProfiniteGrp) (ρ : H →* GeneralLinearGroup ι K) :
    Function.Bijective (originalDualNumberFramedFiberEquiv H ρ) :=
  (originalDualNumberFramedFiberEquiv H ρ).bijective

/-- The true residue and topology comparison preserves every matrix of the original first-order representation. -/
theorem originalDualNumberFramedFiberEquiv_evaluation
    (H : ProfiniteGrp) (ρ : H →* GeneralLinearGroup ι K)
    (τ : {τ : MatrixFirstOrderLift ρ // Continuous τ.val}) (g : H) :
    (originalDualNumberFramedFiberEquiv H ρ τ).val g = τ.val.val g := rfl

end
end Dubon2026
