import Dubon2026.NumberFieldInfiniteAdeleGaloisAction
import Mathlib.Topology.MetricSpace.Completion

/-! # Original base change on infinite adeles

The actual restriction of infinite places gives isometries of the original
completed fields. Their original product is a closed isometric embedding,
which permits a direct trace-and-density proof of infinite-adele descent
in DUB-17's native idele norm-quotient dependency chain.
-/

namespace Dubon2026
noncomputable section
open NumberField UniformSpace Topology
variable (K L : Type) [Field K] [Field L] [Algebra K L]

/-- Original field base change at an original infinite place is isometric. -/
theorem originalInfiniteWithAbsBaseChange_isometry (w : InfinitePlace L) :
    Isometry (WithAbs.map (w.comap (algebraMap K L)).val w.val (algebraMap K L)) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  rfl

/-- The original base field map completed at an actual infinite place. -/
def originalInfiniteCompletionBaseChange (w : InfinitePlace L) :
    (w.comap (algebraMap K L)).Completion →+* w.Completion :=
  (originalInfiniteWithAbsBaseChange_isometry K L w).mapRingHom

/-- The original completed infinite-place map is an isometry. -/
theorem originalInfiniteCompletionBaseChange_isometry (w : InfinitePlace L) :
    Isometry (originalInfiniteCompletionBaseChange K L w) :=
  (originalInfiniteWithAbsBaseChange_isometry K L w).isometry_mapRingHom

/-- The completed infinite-place map retains the actual original field embedding. -/
theorem originalInfiniteCompletionBaseChange_algebraMap (w : InfinitePlace L) (x : K) :
    originalInfiniteCompletionBaseChange K L w
      (algebraMap K (w.comap (algebraMap K L)).Completion x) =
        algebraMap L w.Completion (algebraMap K L x) := by
  change (originalInfiniteWithAbsBaseChange_isometry K L w).mapRingHom
    (↑(WithAbs.toAbs (w.comap (algebraMap K L)).val x) : (w.comap (algebraMap K L)).Completion) = _
  rw [Isometry.mapRingHom_coe]
  rfl

/-- Actual base change on the original infinite adele ring. -/
def originalInfiniteAdeleBaseChangeMap : InfiniteAdeleRing K →+* InfiniteAdeleRing L where
  toFun a w := originalInfiniteCompletionBaseChange K L w (a (w.comap (algebraMap K L)))
  map_one' := funext fun _ => map_one _
  map_zero' := funext fun _ => map_zero _
  map_mul' _ _ := funext fun _ => map_mul _ _ _
  map_add' _ _ := funext fun _ => map_add _ _ _

/-- The original infinite-adele base-change map extends the actual diagonal field embedding. -/
theorem originalInfiniteAdeleBaseChangeMap_algebraMap (x : K) :
    originalInfiniteAdeleBaseChangeMap K L (algebraMap K (InfiniteAdeleRing K) x) =
      algebraMap L (InfiniteAdeleRing L) (algebraMap K L x) := by
  funext w
  exact originalInfiniteCompletionBaseChange_algebraMap K L w x

variable [NumberField K] [NumberField L]

/-- The original base infinite adeles form a closed embedded subring of the original upper infinite adeles. -/
theorem originalInfiniteAdeleBaseChangeMap_isClosedEmbedding :
    IsClosedEmbedding (originalInfiniteAdeleBaseChangeMap K L) := by
  change IsClosedEmbedding (fun a : (v : InfinitePlace K) → v.Completion =>
    fun w : InfinitePlace L => originalInfiniteCompletionBaseChange K L w (a (w.comap (algebraMap K L))))
  have hi : Isometry (fun a : (v : InfinitePlace K) → v.Completion =>
      fun w : InfinitePlace L => originalInfiniteCompletionBaseChange K L w (a (w.comap (algebraMap K L)))) := by
    intro a b
    simp only [edist_pi_def, Finset.sup_univ_eq_iSup]
    simp_rw [(originalInfiniteCompletionBaseChange_isometry K L _).edist_eq]
    exact (InfinitePlace.comap_surjective (k := K) (K := L)).iSup_comp (fun v => edist (a v) (b v))
  exact hi.isClosedEmbedding

end
end Dubon2026
