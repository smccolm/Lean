import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> principal
divisor kernel. A locally constant coset-valued fiber sum is constant on
the connected parameter plane. Native quotient equality and constancy of
locally constant functions replace a separate clopen-set argument. No
topology or discreteness on the period subgroup is assumed.
-/
namespace Dubon2026.SourceFunctionField.PeriodCoset
open scoped Topology

theorem sub_mem_of_eventually_sub_mem {X M : Type*}
    [TopologicalSpace X] [PreconnectedSpace X] [AddCommGroup M]
    (L : AddSubgroup M) (φ : X → M)
    (h : ∀ x₀ : X, ∀ᶠ x in 𝓝 x₀, φ x - φ x₀ ∈ L) (x y : X) : φ x - φ y ∈ L := by
  have hl : IsLocallyConstant (fun z => (QuotientAddGroup.mk (φ z) : M ⧸ L)) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro z
    exact (h z).mono fun w hw => QuotientAddGroup.eq_iff_sub_mem.mpr hw
  exact QuotientAddGroup.eq_iff_sub_mem.mp (hl.apply_eq_of_preconnectedSpace x y)

end Dubon2026.SourceFunctionField.PeriodCoset
