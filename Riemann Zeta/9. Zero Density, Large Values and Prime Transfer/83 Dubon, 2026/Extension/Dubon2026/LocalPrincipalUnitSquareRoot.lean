import Dubon2026.AdicCompleteSimpleRoot
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! The scalar correction needed for DUB-17 polarized strict descent.
The existing complete-local simple-root theorem supplies the square root;
no new completeness or Newton iteration infrastructure is introduced. -/

namespace Dubon2026
open Polynomial IsLocalRing
noncomputable section

/-- In the original complete local ring with residual characteristic not
two, every residue-one unit has a residue-one unit square root. -/
theorem localPrincipalUnit_squareRoot
    {R : Type} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (h2 : (2 : ResidueField R) ≠ 0) (u : Rˣ)
    (hu : Units.map (residue R).toMonoidHom u = 1) :
    ∃ v : Rˣ, Units.map (residue R).toMonoidHom v = 1 ∧ v ^ 2 = u := by
  have hur : residue R (u : R) = 1 := congrArg Units.val hu
  let f : R[X] := X ^ 2 - C (u : R)
  have hf : f.eval 1 ∈ maximalIdeal R := by
    apply (residue_eq_zero_iff _).mp
    simp only [f, eval_sub, eval_pow, eval_X, one_pow, eval_C, map_sub, map_one, hur, sub_self]
  have hdf : IsUnit (Ideal.Quotient.mk (maximalIdeal R) (f.derivative.eval 1)) := by
    change IsUnit (residue R (f.derivative.eval 1))
    have hd : f.derivative.eval 1 = (2 : R) := by simp [f, one_add_one_eq_two]
    rw [hd, map_ofNat]
    exact isUnit_iff_ne_zero.mpr h2
  obtain ⟨x, hx, hxr⟩ := adicComplete_polynomial_simple_root (maximalIdeal R) f 1 hf hdf
  have hxres : residue R x = 1 := by
    have he := (residue_eq_zero_iff _).mpr hxr
    simpa only [map_sub, map_one, sub_eq_zero] using he
  have hxunit : IsUnit x := (residue_ne_zero_iff_isUnit x).mp (hxres ▸ one_ne_zero)
  refine ⟨hxunit.unit, ?_, ?_⟩
  · apply Units.ext
    change residue R (hxunit.unit : R) = 1
    simpa only [IsUnit.unit_spec] using hxres
  · apply Units.ext
    change (hxunit.unit : R) ^ 2 = (u : R)
    rw [IsUnit.unit_spec]
    simpa only [f, IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] using hx

end
end Dubon2026
