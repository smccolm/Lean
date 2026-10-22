import Dubon2026.SourceCurveFiberDegreeSum
import Dubon2026.SourceCurvePicardGroup
import Dubon2026.SourceCurveDivisorDegree

/-! DUB-17/18 -> original Picard Hecke correspondence -> divisor pullback
along its finite function-field maps. The existing finite place fibers and
exact order-restriction law give the actual ramification-weighted finite
divisor and preserve principal divisors. Degree preservation on degree-zero
classes is proved separately from the existing fiber-degree identity.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_AlgebraicCurve_DivisorPushPull.lean, Pullback section.
-/
namespace Dubon2026.SourceCurve
noncomputable section
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
variable [FiniteDimensional F E] [Algebra.IsSeparable F E]

namespace Place
variable (E) in
/-- The actual finite set of places restricting to the given place. -/
def restrictionFiber (v : Place K F) : Finset (Place K E) :=
  (@Set.toFinite (Place K E) {w : Place K E | w.restrict F = v}
    (finite_placeFiber (E := E) v)).toFinset

@[simp] theorem mem_restrictionFiber {v : Place K F} {w : Place K E} :
    w ∈ restrictionFiber E v ↔ w.restrict F = v := by
  simp only [restrictionFiber, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

end Place
namespace Divisor
variable (E)

/-- Pull back a single-place divisor with its actual ramification orders. -/
def finitePullbackSingle (v : Place K F) : ℤ →+ Divisor K E where
  toFun n := ∑ w ∈ v.restrictionFiber E,
    Finsupp.single w (n * w.ord (algebraMap F E (w.restrict F).uniformizer))
  map_zero' := by simp
  map_add' m n := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ => by rw [add_mul, Finsupp.single_add]

/-- The ramification-weighted pullback along the actual finite extension. -/
def finitePullback : Divisor K F →+ Divisor K E :=
  Finsupp.liftAddHom (finitePullbackSingle E)

theorem finitePullback_single (v : Place K F) (n : ℤ) :
    finitePullback E (Finsupp.single v n) = ∑ w ∈ v.restrictionFiber E,
      Finsupp.single w (n * w.ord (algebraMap F E (w.restrict F).uniformizer)) :=
  Finsupp.liftAddHom_apply_single _ _ _

theorem finitePullback_single_apply_of_eq {v : Place K F} {w : Place K E}
    (hw : w.restrict F = v) (n : ℤ) :
    finitePullback E (Finsupp.single v n) w =
      n * w.ord (algebraMap F E (w.restrict F).uniformizer) := by
  classical
  rw [finitePullback_single, Finset.sum_apply']
  trans (Finsupp.single w (n * w.ord (algebraMap F E (w.restrict F).uniformizer))) w
  · refine Finset.sum_eq_single_of_mem w (Place.mem_restrictionFiber.mpr hw) ?_
    intro b _ hb
    exact Finsupp.single_eq_of_ne' hb
  · exact Finsupp.single_eq_same

theorem finitePullback_single_apply_of_ne {v : Place K F} {w : Place K E}
    (hw : w.restrict F ≠ v) (n : ℤ) :
    finitePullback E (Finsupp.single v n) w = 0 := by
  classical
  rw [finitePullback_single, Finset.sum_apply']
  exact Finset.sum_eq_zero fun b hb =>
    Finsupp.single_eq_of_ne fun h => hw (h ▸ Place.mem_restrictionFiber.mp hb)

theorem finitePullback_apply (D : Divisor K F) (w : Place K E) :
    finitePullback E D w = D (w.restrict F) *
      w.ord (algebraMap F E (w.restrict F).uniformizer) := by
  classical
  induction D using Finsupp.induction with
  | zero => simp
  | single_add v n D _ _ ih =>
    rw [map_add, Finsupp.add_apply, ih, Finsupp.add_apply, add_mul]
    congr 1
    by_cases hw : w.restrict F = v
    · rw [finitePullback_single_apply_of_eq E hw, hw, Finsupp.single_eq_same]
    · rw [finitePullback_single_apply_of_ne E hw, Finsupp.single_eq_of_ne hw, zero_mul]

theorem isPrincipal_finitePullback {D : Divisor K F} (hD : IsPrincipal D) :
    IsPrincipal (finitePullback E D) := by
  obtain ⟨f, hf, hD⟩ := hD
  refine ⟨algebraMap F E f, (map_ne_zero _).mpr hf, fun w => ?_⟩
  rw [finitePullback_apply, hD]
  exact (w.ord_algebraMap_restrict f).symm

end Divisor
end
end Dubon2026.SourceCurve
