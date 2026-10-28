import Dubon2026.SourceGammaOneConstantHecke
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-! DUB17/18 -> original all-weight arithmetic realization -> original
homogeneous-coefficient Gamma1 H1/Hecke comparison. Evaluate the existing
native correspondence on its native character, retaining the explicit
coefficient endomorphism b. The original application supplies its
homogeneousMatrixAction, so no scalar replacement is made. -/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology
variable (R V : Type) [CommRing R] [AddCommGroup V] [Module R V]
  (M d : ℕ) [NeZero d] (b : Module.End R V)

private local instance : Fintype (Gamma1 M ⧸ sourceGammaOneHeckeUpper M d) := by
  letI := sourceGammaOneHeckeUpper_finiteIndex M d
  exact Fintype.ofFinite _

theorem sourceGammaOneConstantHeckeH1_coefficient_hom_apply
    (x : H1 (Rep.trivial R (Gamma1 M) V)) (γ : Gamma1 M) :
    (H1IsoOfIsTrivial (Rep.trivial R (Gamma1 M) V)).hom
        (sourceGammaOneConstantHeckeH1 R V M d b x) (Additive.ofMul γ) =
      ∑ q : Gamma1 M ⧸ sourceGammaOneHeckeUpper M d,
        b ((H1IsoOfIsTrivial (Rep.trivial R (Gamma1 M) V)).hom x
          (Additive.ofMul (sourceGammaOneHeckeConjugation M d
            (cosetTransition (sourceGammaOneHeckeUpper M d) γ q)))) := by
  induction x using H1_induction_on with
  | h z =>
    rw [sourceGammaOneConstantHeckeH1_cocycle, H1IsoOfIsTrivial_H1π_apply_apply]
    rw [sourceGammaOneConstantHeckeCocycles_apply]
    apply Finset.sum_congr rfl
    intro q _
    exact congrArg b ((H1IsoOfIsTrivial_H1π_apply_apply z
      (Additive.ofMul (sourceGammaOneHeckeConjugation M d
        (cosetTransition (sourceGammaOneHeckeUpper M d) γ q)))).symm)

end
end Dubon2026
