import Dubon2026.OriginalResidualFramedFibers
import Dubon2026.RelativeDualNumberResidue
import Dubon2026.DualNumberAdicTopology
import Dubon2026.ContinuousFirstOrderDeformation

/-! # Relative dual-number framed fibers over the original coefficient ring -/

namespace Dubon2026

noncomputable section
open Matrix

variable {ι O : Type} [Fintype ι] [DecidableEq ι] [CommRing O] [IsLocalRing O]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- The true dual-number residue field and original maximal-adic topology identify the entire original framed fiber with the genuine continuous first-order lifts in the original product topology. -/
def relativeDualNumberFramedFiberEquiv
    (H : ProfiniteGrp) (ρ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    {τ : MatrixFirstOrderLift ρ // Continuous τ.val} ≃
      (letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) := ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
       OriginalContinuousFramedFiber (relativeDualNumberResidueEquiv O) H
         ρ) where
  toFun τ := by
    letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) := ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
    letI : TopologicalSpace (DualNumber (IsLocalRing.ResidueField O)) :=
      (IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))).adicTopology
    refine ⟨⟨τ.val.val, (dualNumberGL_continuous_iff (IsLocalRing.ResidueField O) τ.val.val).mpr τ.property⟩, ?_⟩
    apply MonoidHom.ext
    intro g
    apply Units.ext
    apply Matrix.ext
    intro i j
    have hτ := congrArg (fun v : GeneralLinearGroup ι (IsLocalRing.ResidueField O) => v.val i j)
      (DFunLike.congr_fun τ.val.property g)
    exact (relativeDualNumberResidueEquiv_reduction O ((τ.val.val g).val i j)).trans hτ
  invFun f := by
    letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) := ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
    letI : TopologicalSpace (DualNumber (IsLocalRing.ResidueField O)) :=
      (IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))).adicTopology
    refine ⟨⟨f.val.toMonoidHom, ?_⟩, (dualNumberGL_continuous_iff (IsLocalRing.ResidueField O) f.val).mp f.val.continuous⟩
    apply MonoidHom.ext
    intro g
    apply Units.ext
    apply Matrix.ext
    intro i j
    have hf := congrArg (fun v : GeneralLinearGroup ι (IsLocalRing.ResidueField O) => v.val i j)
      (DFunLike.congr_fun f.property g)
    exact (relativeDualNumberResidueEquiv_reduction O ((f.val g).val i j)).symm.trans hf
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
theorem relativeDualNumberFramedFiberEquiv_bijective
    (H : ProfiniteGrp) (ρ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    Function.Bijective (relativeDualNumberFramedFiberEquiv H ρ) :=
  (relativeDualNumberFramedFiberEquiv H ρ).bijective

/-- The true residue and topology comparison preserves every matrix of the original first-order representation. -/
theorem relativeDualNumberFramedFiberEquiv_evaluation
    (H : ProfiniteGrp) (ρ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (τ : {τ : MatrixFirstOrderLift ρ // Continuous τ.val}) (g : H) :
    (relativeDualNumberFramedFiberEquiv H ρ τ).val g = τ.val.val g := rfl

end
end Dubon2026
