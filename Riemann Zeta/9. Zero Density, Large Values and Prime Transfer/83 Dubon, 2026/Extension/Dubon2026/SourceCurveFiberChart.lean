import Dubon2026.SourceCurveCoordinateSupport
import Dubon2026.SourceCurveRestrictionOrders
import Dubon2026.SourceCurveRamificationOrders

/-! DUB-17/18 -> original global residue identity -> descent from the actual
finite Galois closure. The integral closure of a genuine place ring is the
Dedekind chart for its extension places. Existing integral-closedness and
center theorems identify those places with actual prime centers.
Selected from Def_AlgebraicCurve_PlacesOverDVR, anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2. Already proved
order, center and integral-containment lemmas are reused, not duplicated.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open IsDedekindDomain IsLocalRing
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
variable [FiniteDimensional F E] [Algebra.IsSeparable F E]

variable (E) in
/-- The literal integral closure of a base place ring in the extension field. -/
abbrev integralClosureAt (v : Place K F) : Type _ := integralClosure v.toValuationSubring E

instance instIsDedekindDomainIntegralClosureAt (v : Place K F) :
    IsDedekindDomain (integralClosureAt E v) :=
  integralClosure.isDedekindDomain v.toValuationSubring F E

instance instIsFractionRingIntegralClosureAt (v : Place K F) :
    IsFractionRing (integralClosureAt E v) E :=
  integralClosure.isFractionRing_of_finite_extension (A := v.toValuationSubring) F E

instance instFiniteIntegralClosureAt (v : Place K F) :
    Module.Finite v.toValuationSubring (integralClosureAt E v) :=
  IsIntegralClosure.finite v.toValuationSubring F E _

omit [Algebra K E] [IsScalarTower K F E] [FiniteDimensional F E]
    [Algebra.IsSeparable F E] in
theorem algebraMap_integralClosureAt_injective (v : Place K F) :
    Function.Injective (algebraMap v.toValuationSubring (integralClosureAt E v)) := by
  intro a b hab
  have h := congrArg (algebraMap (integralClosureAt E v) E) hab
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h
  exact ((algebraMap F E).injective.comp (IsFractionRing.injective v.toValuationSubring F)) h

instance instTorsionFreeIntegralClosureAt (v : Place K F) :
    Module.IsTorsionFree v.toValuationSubring (integralClosureAt E v) := by
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro r c hrc
  rw [Algebra.smul_def] at hrc
  rcases mul_eq_zero.mp hrc with h | h
  · exact Or.inl (algebraMap_integralClosureAt_injective v (by rw [h, map_zero]))
  · exact Or.inr h

omit [Algebra K E] [Algebra F E] [IsScalarTower K F E] [FiniteDimensional F E]
    [Algebra.IsSeparable F E] in
theorem maximalIdeal_ne_bot (v : Place K F) :
    maximalIdeal v.toValuationSubring ≠ ⊥ := by
  intro h
  exact valuationSubring_not_isField_of_ne_top F v.ne_top'
    (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)

omit [FiniteDimensional F E] in
theorem integralClosureAt_mem_of_restrict_eq {v : Place K F} {w : Place K E}
    (hw : w.restrict F = v) (c : integralClosureAt E v) :
    algebraMap (integralClosureAt E v) E c ∈ w.toValuationSubring := by
  apply integralClosure_mem_of_base_mem w (fun r : v.toValuationSubring => ?_) c
  rw [IsScalarTower.algebraMap_apply v.toValuationSubring F E]
  apply (w.mem_restrict_iff).mp
  rw [hw]
  exact r.2

variable (E) in
/-- The actual prime center of an extension place on the integral-closure chart. -/
def fiberCenter {v : Place K F} {w : Place K E} (hw : w.restrict F = v) :
    HeightOneSpectrum (integralClosureAt E v) :=
  centerHeightOneSpectrum (integralClosureAt E v) w (integralClosureAt_mem_of_restrict_eq hw)

theorem fiberCenter_liesOver {v : Place K F} {w : Place K E} (hw : w.restrict F = v) :
    (fiberCenter E hw).asIdeal.LiesOver (maximalIdeal v.toValuationSubring) := by
  refine ⟨?_⟩
  rw [Ideal.under_def]
  ext r
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  have hrR : algebraMap v.toValuationSubring (integralClosureAt E v) r ≠ 0 := by
    simpa only [map_zero] using (algebraMap_integralClosureAt_injective v).ne hr
  have hrF : (r : F) ≠ 0 := by exact_mod_cast hr
  have hepos := w.ord_restricted_uniformizer_pos (F := F)
  rw [hw] at hepos
  change r ∈ maximalIdeal v.toValuationSubring ↔
    algebraMap v.toValuationSubring (integralClosureAt E v) r ∈
      center (integralClosureAt E v) w (integralClosureAt_mem_of_restrict_eq hw)
  rw [w.mem_center_iff_ord_pos _ hrR,
    ← IsScalarTower.algebraMap_apply v.toValuationSubring (integralClosureAt E v) E,
    IsScalarTower.algebraMap_apply v.toValuationSubring F E,
    w.ord_algebraMap_restrict, hw, v.mem_maximalIdeal_iff_ord_pos hrF r.2]
  exact (mul_pos_iff_of_pos_right hepos).symm

end
end Dubon2026.SourceCurve.Place
