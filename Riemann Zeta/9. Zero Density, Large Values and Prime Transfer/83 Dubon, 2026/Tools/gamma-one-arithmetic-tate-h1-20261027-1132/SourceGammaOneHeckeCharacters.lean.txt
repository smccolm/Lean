import Dubon2026.SourceGammaOneConstantHecke
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-! DUB17/18 -> original all-weight arithmetic association -> actual
Gamma1 Picard/H1 comparison. Evaluate the existing native H1 correspondence
through the native trivial-coefficient character isomorphism. This is the
full original coset trace, over both integer and complex coefficients. -/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology

variable (R : Type) [CommRing R] (M d : ℕ) [NeZero d]
private local instance : Fintype (Gamma1 M ⧸ sourceGammaOneHeckeUpper M d) := by
  letI := sourceGammaOneHeckeUpper_finiteIndex M d
  exact Fintype.ofFinite _

theorem sourceGammaOneConstantHeckeH1_hom_apply
    (x : H1 (Rep.trivial R (Gamma1 M) R)) (γ : Gamma1 M) :
    (H1IsoOfIsTrivial (Rep.trivial R (Gamma1 M) R)).hom
        (sourceGammaOneConstantHeckeH1 R R M d LinearMap.id x) (Additive.ofMul γ) =
      ∑ q : Gamma1 M ⧸ sourceGammaOneHeckeUpper M d,
        (H1IsoOfIsTrivial (Rep.trivial R (Gamma1 M) R)).hom x
          (Additive.ofMul (sourceGammaOneHeckeConjugation M d
            (cosetTransition (sourceGammaOneHeckeUpper M d) γ q))) := by
  induction x using H1_induction_on with
  | h z =>
    rw [sourceGammaOneConstantHeckeH1_cocycle, H1IsoOfIsTrivial_H1π_apply_apply]
    rw [sourceGammaOneConstantHeckeCocycles_apply]
    apply Finset.sum_congr rfl
    intro q _
    exact (H1IsoOfIsTrivial_H1π_apply_apply z
      (Additive.ofMul (sourceGammaOneHeckeConjugation M d
        (cosetTransition (sourceGammaOneHeckeUpper M d) γ q)))).symm

end
end Dubon2026
