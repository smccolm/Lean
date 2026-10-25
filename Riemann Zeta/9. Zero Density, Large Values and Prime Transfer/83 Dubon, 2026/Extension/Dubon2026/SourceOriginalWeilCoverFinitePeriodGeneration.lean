import Dubon2026.SourceOriginalWeilCoverAbelJacobiPeriods

/-! DUB-17/18 -> auxiliary point division -> cover Abel converse -> raw reciprocity period correction. Reuse the native actual Abel potential and compact maximum-principle argument; only the exact linear and integer-coordinate consumers required for correction are retained. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n] (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders
local notation "CoverPath" => @Path (Place ℂ EE) (placeTopology N n radicand baseDivisor hRadicand hOrders)

theorem exists_cover_period_coordinates {kDim : ℕ} {ι : Type*} [Fintype ι]
    (b : Fin kDim → Ω[EE⁄ℂ]) (Pz : ι → Place ℂ EE) (Z : ∀ k, CoverPath (Pz k) (Pz k))
    (hgen : ∀ (P : Place ℂ EE) (γ : CoverPath P P), ∃ κ : ι → ℤ,
      ∀ i, pathIntegral N n radicand baseDivisor hRadicand hOrders (b i) γ = ∑ k, (κ k : ℂ) * pathIntegral N n radicand baseDivisor hRadicand hOrders (b i) (Z k))
    {u : Fin kDim → ℂ} (hu : u ∈ pathPeriodLattice N n radicand baseDivisor hRadicand hOrders b) :
    ∃ κ : ι → ℤ, u = fun i => ∑ k, (κ k : ℂ) * pathIntegral N n radicand baseDivisor hRadicand hOrders (b i) (Z k) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  classical
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨P, γ, rfl⟩ := hu
    obtain ⟨κ, hκ⟩ := hgen P γ
    exact ⟨κ, funext hκ⟩
  | zero => exact ⟨0, by ext i; simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨κ, rfl⟩ := hu
    obtain ⟨μ, rfl⟩ := hv
    exact ⟨κ + μ, by ext i; simp [add_mul, Finset.sum_add_distrib]⟩
  | smul a u _ hu =>
    obtain ⟨κ, rfl⟩ := hu
    refine ⟨a • κ, ?_⟩
    ext i
    simp [zsmul_eq_mul, Finset.mul_sum, mul_assoc]


end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
