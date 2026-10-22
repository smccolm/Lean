import Dubon2026.SourceOriginalFinitePuncturePaths

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
global meromorphic exponential. Every actual finite divisor admits an
original base point outside its support, and any two such points can be
joined by an actual continuous path avoiding that support.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Set
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_original_divisor_base_point (D : Divisor ℂ F) :
    ∃ P : Place ℂ F, D P = 0 := by
  obtain ⟨P, hP⟩ := exists_original_place_outside_finite N D.support.finite_toSet
  exact ⟨P, Finsupp.notMem_support_iff.mp hP⟩

theorem exists_original_path_avoiding_divisor (D : Divisor ℂ F)
    (P Q : Place ℂ F) (hP : D P = 0) (hQ : D Q = 0) :
    letI := placeTopology N
    ∃ γ : Path P Q, ∀ t, D (γ t) = 0 := by
  letI := placeTopology N
  have h := original_isPathConnected_compl_finite N D.support.finite_toSet
  have hP' : P ∈ (D.support : Set (Place ℂ F))ᶜ := Finsupp.notMem_support_iff.mpr hP
  have hQ' : Q ∈ (D.support : Set (Place ℂ F))ᶜ := Finsupp.notMem_support_iff.mpr hQ
  have hj := h.joinedIn P hP' Q hQ'
  exact ⟨hj.somePath, fun t => Finsupp.notMem_support_iff.mp (hj.somePath_mem t)⟩

end
end Dubon2026.SourceFunctionField.OriginalChart
