import Dubon2026.SourceOriginalWeilCoverExponentialMeromorphicOrders
import Dubon2026.SourceOriginalWeilCoverMeromorphicPrincipalDivisor

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


theorem exists_cover_meromorphic_orders_of_integral_periods
    (D : Divisor ℂ EE) (η : Ω[EE⁄ℂ])
    (hη : ∀ v : Place ℂ EE, -1 ≤ v.ordDifferential η)
    (hres : ∀ v, v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v) (v.uniformizer * v.differentialCoeff η) = (D v : ℂ))
    (hper : ∀ (P : Place ℂ EE) (α : CoverPath P P), (∀ t, D (α t) = 0) →
      ∃ m : ℤ, pathIntegral N n radicand A hRadicand hOrders η α = 2 * Real.pi * Complex.I * m) :
    ∃ g : Place ℂ EE → ℂ, ∀ v, MeromorphicAt (fun z => g (placeFamily N n radicand A hRadicand hOrders v z)) 0 ∧
      meromorphicOrderAt (fun z => g (placeFamily N n radicand A hRadicand hOrders v z)) 0 = (D v : WithTop ℤ) := by
  letI := placeTopology N n radicand A hRadicand hOrders
  obtain ⟨g, hgn, ht⟩ := exists_cover_period_exponential N n radicand A hRadicand hOrders D η hη hres hper
  exact ⟨g, cover_meromorphic_orders_of_exponential_transport N n radicand A hRadicand hOrders D η hη hres g hgn ht⟩

theorem cover_isPrincipal_of_integral_periods
    (D : Divisor ℂ EE) (η : Ω[EE⁄ℂ])
    (hη : ∀ v : Place ℂ EE, -1 ≤ v.ordDifferential η)
    (hres : ∀ v, v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v) (v.uniformizer * v.differentialCoeff η) = (D v : ℂ))
    (hper : ∀ (P : Place ℂ EE) (α : CoverPath P P), (∀ t, D (α t) = 0) →
      ∃ m : ℤ, pathIntegral N n radicand A hRadicand hOrders η α = 2 * Real.pi * Complex.I * m) :
    Divisor.IsPrincipal D := by
  letI := placeTopology N n radicand A hRadicand hOrders
  obtain ⟨g, hg⟩ := exists_cover_meromorphic_orders_of_integral_periods N n radicand A hRadicand hOrders D η hη hres hper
  exact cover_isPrincipal_of_meromorphic_orders N n radicand A hRadicand hOrders D g (fun v => (hg v).1) (fun v => (hg v).2)


end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
