import Dubon2026.SourceOriginalWeilCoverFinitePuncturePaths

/-! DUB-17/18 -> auxiliary point division -> cover Abel converse -> global meromorphic exponential. Reuse the native logarithmic-model and finite-puncture arguments with proved cover geometry and actual residue values. The global period correction remains open. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n] (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * A v)
include A hRadicand hOrders
local notation "CoverPath" => @Path (Place ℂ EE) (placeTopology N n radicand A hRadicand hOrders)

theorem exists_cover_divisor_base_point (D : Divisor ℂ EE) :
    ∃ P : Place ℂ EE, D P = 0 := by
  obtain ⟨P, hP⟩ := exists_cover_place_outside_finite N n radicand A hRadicand hOrders D.support.finite_toSet
  exact ⟨P, Finsupp.notMem_support_iff.mp hP⟩

theorem exists_cover_path_avoiding_divisor (D : Divisor ℂ EE)
    (P Q : Place ℂ EE) (hP : D P = 0) (hQ : D Q = 0) :
    letI := placeTopology N n radicand A hRadicand hOrders
    ∃ γ : Path P Q, ∀ t, D (γ t) = 0 := by
  letI := placeTopology N n radicand A hRadicand hOrders
  have h := cover_isPathConnected_compl_finite N n radicand A hRadicand hOrders D.support.finite_toSet
  have hP' : P ∈ (D.support : Set (Place ℂ EE))ᶜ := Finsupp.notMem_support_iff.mpr hP
  have hQ' : Q ∈ (D.support : Set (Place ℂ EE))ᶜ := Finsupp.notMem_support_iff.mpr hQ
  have hj := h.joinedIn P hP' Q hQ'
  exact ⟨hj.somePath, fun t => Finsupp.notMem_support_iff.mp (hj.somePath_mem t)⟩


end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
