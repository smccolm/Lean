import Dubon2026.AdelicCompactFiniteConverse
import Dubon2026.AdelicRealCyclicClosure

/-! # Exact identification of original real K-finite vectors with the actual raising module -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The actual smooth raising module has exactly the original algebraic Hilbert raising span as its genuine image. -/
theorem adelicRaisingSpan_hilbert_image :
    (adelicRaisingSpan f).map (adelicRealSmoothSubmodule f).subtype =
      Submodule.span ℂ (Set.range (fun n : ℕ => (adelicRaisingJet f n).val)) := by
  rw [adelicRaisingSpan, Submodule.map_span, ← Set.range_comp]
  rfl

/-- In the original real cyclic Hilbert representation, genuine K-finiteness is exactly finite original raising expansion. -/
theorem adelicRealCyclic_KFinite_iff (hf : f ≠ 0) (hk : 0 < k)
    (v : AdelicCyclicHilbert f) (hv : v ∈ adelicRealCyclicClosedSpan f) :
    FiniteDimensional ℂ (adelicCompactOrbitSpan f v) ↔
      v ∈ Submodule.span ℂ (Set.range (fun n : ℕ => (adelicRaisingJet f n).val)) := by
  constructor
  · intro hfin
    letI := hfin
    apply adelicCompactFinite_mem_raisingSpan f hf hk v
    exact (adelicRaisingClosedSpan_eq_realCyclicClosedSpan f hf).symm ▸ hv
  · exact adelicRaisingSpan_compact_finite f hf v

/-- Every actual K-finite vector of the original real component is the literal image of an original smooth raising-module vector. -/
theorem adelicRealKFinite_raising_lift (hf : f ≠ 0) (hk : 0 < k)
    (v : AdelicCyclicHilbert f) (hv : v ∈ adelicRealCyclicClosedSpan f)
    [FiniteDimensional ℂ (adelicCompactOrbitSpan f v)] :
    ∃ w : adelicRealSmoothSubmodule f, w.val = v ∧ w ∈ adelicRaisingSpan f := by
  have hs := (adelicRealCyclic_KFinite_iff f hf hk v hv).mp inferInstance
  have hm : v ∈ (adelicRaisingSpan f).map (adelicRealSmoothSubmodule f).subtype :=
    (adelicRaisingSpan_hilbert_image f).symm ▸ hs
  obtain ⟨w, hw, he⟩ := Submodule.mem_map.mp hm
  exact ⟨w, he, hw⟩

/-- Smoothness of actual K-finite vectors in the original real component follows from their proved exact raising expansion. -/
theorem adelicRealKFinite_mem_smooth (hf : f ≠ 0) (hk : 0 < k)
    (v : AdelicCyclicHilbert f) (hv : v ∈ adelicRealCyclicClosedSpan f)
    [FiniteDimensional ℂ (adelicCompactOrbitSpan f v)] : v ∈ adelicRealSmoothSubmodule f := by
  obtain ⟨w, hw, _⟩ := adelicRealKFinite_raising_lift f hf hk v hv
  exact hw ▸ w.property

/-- A genuine smooth K-finite vector in the original real component lies in the original smooth raising module itself. -/
theorem adelicSmoothKFinite_mem_raisingSpan (hf : f ≠ 0) (hk : 0 < k)
    (v : adelicRealSmoothSubmodule f) (hv : v.val ∈ adelicRealCyclicClosedSpan f)
    [FiniteDimensional ℂ (adelicCompactOrbitSpan f v.val)] : v ∈ adelicRaisingSpan f := by
  have h := @adelicRealKFinite_raising_lift N inferInstance k f hf hk v.val hv inferInstance
  obtain ⟨w, hw, hs⟩ := h
  have he : w = v := Subtype.ext hw
  exact he ▸ hs

end
end Dubon2026
