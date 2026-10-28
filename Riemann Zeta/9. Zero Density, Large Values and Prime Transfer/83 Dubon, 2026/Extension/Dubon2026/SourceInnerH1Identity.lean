import Dubon2026.SourceSemilinearCohomology
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! DUB-17/18 -> original all-weight association -> finite Gamma1
arithmetic realization -> trivial diamond on the original Gamma0 character.
The native transfer base-change theorem reduces normalizer invariance to
this exact inner-conjugation action on the original first cohomology.
-/
namespace Dubon2026
noncomputable section
open groupCohomology CategoryTheory
variable {R G : Type} [CommRing R] [Group G] (A : Rep R G) (g : G)

/-- The original inverse coefficient action accompanying inner conjugation. -/
def sourceInnerCoefficientMorphism : Rep.res (MulAut.conj g).toMonoidHom A ⟶ A :=
  Rep.ofHom {
    toLinearMap := A.ρ g⁻¹
    isIntertwining' := by
      intro h
      apply LinearMap.ext
      intro x
      change A.ρ g⁻¹ (A.ρ (g * h * g⁻¹) x) = A.ρ h (A.ρ g⁻¹ x)
      simp only [← Module.End.mul_apply, ← map_mul]
      congr 1
      group }

theorem sourceInnerH1_identity (x : H1 A) :
    groupCohomology.map (MulAut.conj g).toMonoidHom
      (sourceInnerCoefficientMorphism A g) 1 x = x := by
  induction x using H1_induction_on with
  | h c =>
    rw [H1π_comp_map_apply]
    apply (H1π_eq_iff _ _).mpr
    refine ⟨- A.ρ g⁻¹ (c g), ?_⟩
    funext h
    change A.ρ h (- A.ρ g⁻¹ (c g)) - (- A.ρ g⁻¹ (c g)) =
      A.ρ g⁻¹ (c (g * h * g⁻¹)) - c h
    have hm := (mem_cocycles₁_iff c).mp c.property
    have hi := congrArg (A.ρ g⁻¹) (cocycles₁_map_inv c g)
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply, map_neg] at hi
    rw [hm, hm, hi]
    simp only [map_add, map_neg, ← Module.End.mul_apply, ← map_mul,
      mul_assoc, inv_mul_cancel_left, inv_mul_cancel, map_one, Module.End.one_apply]
    abel

end
end Dubon2026
