import Dubon2026.SourceOriginalWeilCoverPeriodExponential

/-! DUB-17/18 -> auxiliary point division -> cover Abel converse -> integral-period principality. The native exponential argument is applied to the actual cover with constructed residue data, paths and local models. Integral loop periods remain an explicit upstream hypothesis; their correction and the full Abel converse are not asserted here. -/
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


theorem exists_cover_period_exponential (D : Divisor ℂ EE) (η : Ω[EE⁄ℂ])
    (hη : ∀ v : Place ℂ EE, -1 ≤ v.ordDifferential η)
    (hres : ∀ v, v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v) (v.uniformizer * v.differentialCoeff η) = (D v : ℂ))
    (hper : ∀ (P : Place ℂ EE) (α : CoverPath P P), (∀ t, D (α t) = 0) →
      ∃ m : ℤ, pathIntegral N n radicand A hRadicand hOrders η α = 2 * Real.pi * Complex.I * m) :
    ∃ g : Place ℂ EE → ℂ, (∀ P, D P = 0 → g P ≠ 0) ∧
      ∀ (P Q : Place ℂ EE) (σ : CoverPath P Q), D P = 0 → D Q = 0 →
        (∀ t, D (σ t) = 0) → g Q = g P * Complex.exp (pathIntegral N n radicand A hRadicand hOrders η σ) := by
  letI := placeTopology N n radicand A hRadicand hOrders
  obtain ⟨P₀, hP₀⟩ := exists_cover_divisor_base_point N n radicand A hRadicand hOrders D
  refine ⟨coverPeriodExponential N n radicand A hRadicand hOrders D η P₀ hP₀,
    coverPeriodExponential_ne_zero N n radicand A hRadicand hOrders D η P₀ hP₀, ?_⟩
  intro P Q σ hP hQ hσ
  exact coverPeriodExponential_transport N n radicand A hRadicand hOrders D η hη hres hper P₀ hP₀ P Q hP hQ σ hσ


end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
