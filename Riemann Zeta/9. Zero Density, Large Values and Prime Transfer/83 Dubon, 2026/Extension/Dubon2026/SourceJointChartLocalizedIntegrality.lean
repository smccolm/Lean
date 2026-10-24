import Dubon2026.SourceJointChartLocalizations
import Dubon2026.SourceJointChartValuationUnits

/-! DUB-17/18 -> original-field Kummer power lifting -> genus inequality ->
common residue-chart constants. These localizations use denominators whose
reduction is a nonzero monomial. They provide the two charts and overlap
needed by the already proved idempotent gluing theorem. Adapted from
Apache-2.0 FLT commit 6e837e75355538c7f80bab5b956861e86c4eacc2;
native integral-closure algebras replace the external chart predicate. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open Polynomial IsLocalRing

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {ι : Type*} {Fb : ι → Type*} [∀ i, Field (Fb i)]
  [∀ i, Algebra (ResidueField A) (Fb i)]
variable (R : ∀ i, RegularProlongation A F (Fb i))

theorem mem_integers_of_mem_Pg {g : F} (hg : ∀ i, g ∈ (R i).integers) {x : F} (hx : x ∈ Pg R g hg)
    (i : ι) : x ∈ (R i).integers := by
  obtain ⟨t, ht, hxt⟩ := hx
  have h1 : (R i).integers.valuation (x * aeval g t) ≤ 1 := (mem_iff_le _ _).mp (hxt.1 i)
  rw [map_mul, valuation_aeval_eq_one (R i) (hg i) ht, mul_one] at h1
  exact (mem_iff_le _ _).mpr h1

theorem valuation_lt_of_mem_map {g : F} (hg : ∀ i, g ∈ (R i).integers) {x : Pg R g hg}
    (hx : x ∈ (maximalIdeal A).map (algebraMap A (Pg R g hg))) (i : ι) :
    (R i).integers.valuation (x : F) < 1 := by
  have hx' : x ∈ Submodule.span (Pg R g hg)
      ((algebraMap A (Pg R g hg)) '' (maximalIdeal A : Set A)) := hx
  refine Submodule.span_induction (p := fun (y : Pg R g hg) _ => (R i).integers.valuation (y : F) < 1)
    ?_ ?_ ?_ ?_ hx'
  · rintro y ⟨m, hm, rfl⟩
    exact valuation_algebraMap_lt (R i) ((A.valuation_lt_one_iff _).mp hm)
  · simp
  · intro y y' _ _ hy hy'
    exact Valuation.map_add_lt _ hy hy'
  · intro p y _ hy
    show (R i).integers.valuation ((p : F) * y) < 1
    rw [map_mul]
    calc (R i).integers.valuation (p : F) * (R i).integers.valuation (y : F)
        ≤ 1 * (R i).integers.valuation (y : F) :=
          by gcongr; exact (mem_iff_le _ _).mp (mem_integers_of_mem_Pg R hg p.2 i)
      _ < 1 := by rwa [one_mul]

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
