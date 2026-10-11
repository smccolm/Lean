import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Pi

/-! # The actual coordinate invariant line is a free rank-one direct summand -/

namespace Dubon2026
noncomputable section

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- If an actual submodule is the first axis in a genuine original linear coordinate system, it is linearly equivalent to the original coefficient ring and is an actual direct summand of the whole original module. -/
theorem submodule_rankOne_split_of_coordinates (S : Submodule R V)
    (e : V ≃ₗ[R] R × R) (hS : ∀ v, v ∈ S ↔ (e v).2 = 0) :
    Nonempty (S ≃ₗ[R] R) ∧ ∃ N : Submodule R V, IsCompl S N := by
  let f : S →ₗ[R] R := (LinearMap.fst R R R).comp (e.toLinearMap.comp S.subtype)
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply e.injective
      apply Prod.ext
      · exact hxy
      · exact (hS x.val).mp x.property |>.trans ((hS y.val).mp y.property).symm
    · intro a
      have hm : e.symm (a, 0) ∈ S := (hS _).mpr (by simp)
      refine ⟨⟨e.symm (a, 0), hm⟩, ?_⟩
      change (e (e.symm (a, 0))).1 = a
      simp only [e.apply_symm_apply]
  let lineEquiv : S ≃ₗ[R] R := LinearEquiv.ofBijective f hf
  let projection : V →ₗ[R] S := lineEquiv.symm.toLinearMap.comp
    ((LinearMap.fst R R R).comp e.toLinearMap)
  have hp (x : S) : projection x = x := by
    change lineEquiv.symm (lineEquiv x) = x
    exact lineEquiv.symm_apply_apply x
  exact ⟨⟨lineEquiv⟩, ⟨projection.ker, LinearMap.isCompl_of_proj hp⟩⟩

end
end Dubon2026
