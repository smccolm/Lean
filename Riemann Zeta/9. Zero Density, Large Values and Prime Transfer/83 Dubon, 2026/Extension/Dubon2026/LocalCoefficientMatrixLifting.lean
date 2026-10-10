import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Lifting actual invertible matrices along genuine local coefficient surjections -/

namespace Dubon2026
noncomputable section
open Matrix

variable {ι A B : Type} [Fintype ι] [DecidableEq ι] [CommRing A] [CommRing B]

/-- A genuine surjective coefficient homomorphism reflecting units lifts every actual invertible matrix, by lifting its original entries and reflecting the original determinant-unit condition. -/
theorem generalLinearGroup_map_surjective (f : A →+* B) (hf : Function.Surjective f)
    [IsLocalHom f] : Function.Surjective (GeneralLinearGroup.map (n := ι) f) := by
  intro U
  choose X hX using fun i j => hf (U.val i j)
  have hmap : (RingHom.mapMatrix f) X = U.val := Matrix.ext hX
  have hdet : IsUnit (Matrix.det X) := by
    apply isUnit_of_map_unit f
    rw [RingHom.map_det, hmap]
    exact Matrix.isUnits_det_units U
  refine ⟨GeneralLinearGroup.mk'' X hdet, ?_⟩
  apply Units.ext
  exact hmap

/-- A genuine original matrix reducing to the identity lifts through a surjective local coefficient map to a matrix reducing to the same identity, for the actual compatible residue maps. -/
theorem generalLinearGroup_strict_lift {K : Type} [CommRing K]
    (f : A →+* B) (hf : Function.Surjective f) [IsLocalHom f]
    (rA : A →+* K) (rB : B →+* K) (hr : rB.comp f = rA)
    (U : GeneralLinearGroup ι B) (hU : GeneralLinearGroup.map rB U = 1) :
    ∃ V : GeneralLinearGroup ι A,
      GeneralLinearGroup.map f V = U ∧ GeneralLinearGroup.map rA V = 1 := by
  obtain ⟨V, hV⟩ := generalLinearGroup_map_surjective f hf U
  refine ⟨V, hV, ?_⟩
  rw [← hr, GeneralLinearGroup.map_comp, MonoidHom.comp_apply, hV]
  exact hU

end
end Dubon2026
