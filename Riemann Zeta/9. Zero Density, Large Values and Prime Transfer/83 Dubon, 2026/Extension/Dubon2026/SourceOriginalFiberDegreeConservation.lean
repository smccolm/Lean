import Dubon2026.SourceOriginalFiberOrderSupport

/-! DUB-17/18 -> original torsion cardinality -> compact original curve.
The finite positive-order fibers of an original function all have the same
total multiplicity. This consumes its actual principal divisor and the
proved invariance of pole orders under subtraction of a constant.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_Place_exists_finset_forall_exists_localParam_eq_complex.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) [NeZero N]

/-- The actual finite positive-order fiber of an original function. -/
def originalPositiveFiber (g : modularFunctionFieldOver N ℂ) (a : ℂ) :
    Finset (Place ℂ (modularFunctionFieldOver N ℂ)) :=
  (originalPrincipalDivisor N ℂ (g - algebraMap ℂ (modularFunctionFieldOver N ℂ) a)).support.filter
    (fun v => 0 < v.ord (g - algebraMap ℂ (modularFunctionFieldOver N ℂ) a))

theorem mem_originalPositiveFiber (g : modularFunctionFieldOver N ℂ) (a : ℂ)
    (v : Place ℂ (modularFunctionFieldOver N ℂ)) :
    v ∈ originalPositiveFiber N g a ↔
      0 < v.ord (g - algebraMap ℂ (modularFunctionFieldOver N ℂ) a) := by
  simp only [originalPositiveFiber, Finset.mem_filter, Finsupp.mem_support_iff,
    originalPrincipalDivisor_apply]
  exact ⟨And.right, fun h => ⟨h.ne', h⟩⟩

theorem original_fiber_total_order_constant (g : modularFunctionFieldOver N ℂ) (a : ℂ) :
    (∑ v ∈ originalPositiveFiber N g a,
      v.ord (g - algebraMap ℂ (modularFunctionFieldOver N ℂ) a)) =
    ∑ v ∈ originalPositiveFiber N g 0, v.ord g := by
  classical
  let D := fun a : ℂ => originalPrincipalDivisor N ℂ
    (g - algebraMap ℂ (modularFunctionFieldOver N ℂ) a)
  let Pl := fun a : ℂ => (D a).support.filter (fun v => D a v < 0)
  have hD : ∀ a v, D a v = v.ord (g - algebraMap ℂ (modularFunctionFieldOver N ℂ) a) :=
    fun _ _ => rfl
  have hmem : ∀ a v, v ∈ Pl a ↔ g ∉ v.toValuationSubring := by
    intro a v
    simp only [Pl, Finset.mem_filter, Finsupp.mem_support_iff, hD]
    have hneg : v.ord (g - algebraMap ℂ (modularFunctionFieldOver N ℂ) a) < 0 ↔
        g ∉ v.toValuationSubring := by
      rw [← original_sub_const_mem_iff N v g a]
      exact ⟨fun h hm => not_le_of_gt h (v.ord_nonneg_of_mem hm),
        fun h => lt_of_not_ge (fun hn => h (v.mem_of_ord_nonneg hn))⟩
    exact ⟨fun h => hneg.mp h.2, fun h => ⟨(hneg.mpr h).ne, hneg.mpr h⟩⟩
  have hsumPl : ∀ a, (∑ v ∈ Pl a, D a v) = ∑ v ∈ Pl 0, D 0 v := by
    intro a
    have hset : Pl a = Pl 0 := by ext v; rw [hmem, hmem]
    rw [hset]
    refine Finset.sum_congr rfl fun v hv => ?_
    have hp := (hmem 0 v).mp hv
    rw [hD, hD, original_ord_sub_const_of_pole N v hp,
      original_ord_sub_const_of_pole N v hp]
  have hsplit : ∀ a, (∑ v ∈ originalPositiveFiber N g a, D a v) +
      (∑ v ∈ Pl a, D a v) = 0 := by
    intro a
    have hz : (∑ v ∈ (D a).support, D a v) = 0 :=
      (original_divisor_sum_support N (D a)).trans (degree_originalPrincipalDivisor N ℂ _)
    rw [← hz]
    change (∑ v ∈ (D a).support.filter (fun v => 0 < D a v), D a v) +
      (∑ v ∈ (D a).support.filter (fun v => D a v < 0), D a v) = _
    rw [← Finset.sum_filter_add_sum_filter_not (D a).support (fun v => 0 < D a v)]
    congr 1
    apply Finset.sum_congr
    · ext v
      simp only [Finset.mem_filter, Finsupp.mem_support_iff, not_lt]
      exact ⟨fun h => ⟨h.1, h.2.le⟩, fun h => ⟨h.1, lt_of_le_of_ne h.2 h.1⟩⟩
    · intro v _
      rfl
  have h1 := hsplit a
  have h2 := hsplit 0
  rw [hsumPl a] at h1
  have he : (∑ v ∈ originalPositiveFiber N g a, D a v) =
      ∑ v ∈ originalPositiveFiber N g 0, D 0 v := by omega
  simpa only [hD, map_zero, sub_zero] using he

end
end Dubon2026.SourceFunctionField
