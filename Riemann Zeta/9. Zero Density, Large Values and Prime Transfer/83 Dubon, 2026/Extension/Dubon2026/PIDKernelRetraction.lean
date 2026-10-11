import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Finiteness.Basic

/-! # Actual kernel retractions over the original principal ideal domain -/

namespace Dubon2026
noncomputable section

variable {R M N : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [AddCommGroup M] [Module R M] [Module.Finite R M]
  [AddCommGroup N] [Module R N] [Module.IsTorsionFree R N]

/-- The kernel of an actual map into a torsion-free module over a PID is a direct summand of its finite original source. The finite torsion-free image is free, so its genuine range surjection admits a section. -/
theorem pidKernel_exists_retraction (f : M →ₗ[R] N) :
    ∃ p : M →ₗ[R] LinearMap.ker f,
      p.comp (LinearMap.ker f).subtype = LinearMap.id := by
  letI : Module.Free R (LinearMap.range f) := inferInstance
  obtain ⟨s, hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  let e : M →ₗ[R] M := LinearMap.id - s.comp f.rangeRestrict
  have he (x : M) : f (e x) = 0 := by
    have hx : f (s (f.rangeRestrict x)) = f x :=
      congrArg Subtype.val (LinearMap.congr_fun hs (f.rangeRestrict x))
    change f (x - s (f.rangeRestrict x)) = 0
    rw [map_sub, hx, sub_self]
  let p : M →ₗ[R] LinearMap.ker f := e.codRestrict _ (fun x => he x)
  refine ⟨p, ?_⟩
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have hx : f.rangeRestrict x.val = 0 := Subtype.ext x.property
  change x.val - s (f.rangeRestrict x.val) = x.val
  rw [hx, map_zero, sub_zero]

end
end Dubon2026
