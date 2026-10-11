import Dubon2026.ScaledLatticeProducts
import Dubon2026.LocalFieldIntegerAlgebraFinite
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.GroupWithZero

/-! # Openness of the original lattice from its genuine integer-ring bound -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel Topology

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)] in
/-- A genuine original lattice containing a nonzero base scalar power of
the actual extension integer ring is open in the original field topology. -/
theorem localField_lattice_isOpen_of_integer_power_bound
    (A : Submodule 𝒪[K] L) (π : 𝒪[K]) (hπ : π ≠ 0) (n : ℕ)
    (hbound : ∀ x : 𝒪[L], π ^ n • (x : L) ∈ A) : IsOpen (A : Set L) := by
  let c : L := algebraMap 𝒪[K] L (π ^ n)
  have hc : c ≠ 0 := by
    intro he
    apply pow_ne_zero n hπ
    exact (FaithfulSMul.algebraMap_injective 𝒪[K] L) (he.trans (map_zero _).symm)
  let S : Set L := (fun x : L => c * x) '' ((ValuativeRel.valuation L).integer : Set L)
  have hS : IsOpen S :=
    (Homeomorph.mulLeft₀ c hc).isOpenMap _ (Valuation.isOpen_integer (v := ValuativeRel.valuation L))
  have hz : (0 : L) ∈ S := ⟨0, (ValuativeRel.valuation L).integer.zero_mem, mul_zero c⟩
  apply A.toAddSubgroup.isOpen_of_mem_nhds (g := (0 : L))
  apply Filter.mem_of_superset (hS.mem_nhds hz)
  rintro x ⟨a, ha, rfl⟩
  simpa only [Algebra.smul_def] using hbound ⟨a, ha⟩

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)] in
/-- The original small scalar lattice is open because it still contains
an explicitly computed nonzero scalar power of the actual integer ring. -/
theorem localField_scaled_lattice_isOpen
    (A : Submodule 𝒪[K] L) (π : 𝒪[K]) (hπ : π ≠ 0) (n : ℕ)
    (hbound : ∀ x : 𝒪[L], π ^ n • (x : L) ∈ A) :
    IsOpen (scalarLatticeImage A (π ^ (n + 1)) : Set L) := by
  apply localField_lattice_isOpen_of_integer_power_bound K L _ π hπ (n + 1 + n)
  intro x
  refine (mem_scalarLatticeImage A _ _).mpr ⟨π ^ n • (x : L), hbound x, ?_⟩
  rw [smul_smul, ← pow_add]

end
end Dubon2026
