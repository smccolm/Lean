import Dubon2026.SourceOriginalWeilCoverIntegralPeriodsPrincipal
import Dubon2026.SourceOriginalWeilCoverRegularDifferentialSubtraction

/-! DUB-17/18 -> auxiliary point division -> cover Abel converse. The native integer-period correction and actual cover integral-period principality consume the geometric loop-generation and bilinear/third-kind reciprocity clauses explicitly. These raw geometric clauses remain open, so this is a conditional Abel converse. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential Matrix
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n] (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders
local notation "CoverPath" => @Path (Place ℂ EE) (placeTopology N n radicand baseDivisor hRadicand hOrders)

theorem cover_integral_periods_of_generators {ι : Type*} [Fintype ι]
    (D : Divisor ℂ EE) (θ : Ω[EE⁄ℂ])
    (hθ : ∀ v : Place ℂ EE, -1 ≤ v.ordDifferential θ)
    (hres : ∀ v, v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v) (v.uniformizer * v.differentialCoeff θ) = (D v : ℂ))
    (Pz : ι → Place ℂ EE) (Z : ∀ k, CoverPath (Pz k) (Pz k))
    (m : ι → ℤ) (hm : ∀ k, pathIntegral N n radicand baseDivisor hRadicand hOrders θ (Z k) = 2 * Real.pi * Complex.I * (m k : ℂ))
    (hgen : ∀ (P : Place ℂ EE) (γ : CoverPath P P), (∀ t, D (γ t) = 0) →
      ∃ (κ : ι → ℤ) (w : Place ℂ EE → ℤ), ∀ η : Ω[EE⁄ℂ],
        (∀ v : Place ℂ EE, -1 ≤ v.ordDifferential η) →
        (∀ v : Place ℂ EE, D v = 0 → 0 ≤ v.ordDifferential η) →
        pathIntegral N n radicand baseDivisor hRadicand hOrders η γ = ∑ k, (κ k : ℂ) * pathIntegral N n radicand baseDivisor hRadicand hOrders η (Z k) +
          2 * Real.pi * Complex.I * ∑ v ∈ D.support,
            (w v : ℂ) * v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v) (v.uniformizer * v.differentialCoeff η)) :
    ∀ (P : Place ℂ EE) (γ : CoverPath P P), (∀ t, D (γ t) = 0) →
      ∃ a : ℤ, pathIntegral N n radicand baseDivisor hRadicand hOrders θ γ = 2 * Real.pi * Complex.I * a := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  classical
  intro P γ hγ
  obtain ⟨κ, w, h⟩ := hgen P γ hγ
  have hreg : ∀ v : Place ℂ EE, D v = 0 → 0 ≤ v.ordDifferential θ := by
    intro v hv
    exact v.ord_nonneg_of_mem (cover_coeff_regular_off_divisor N n radicand D θ hθ hres v hv)
  rw [h θ hθ hreg]
  refine ⟨(∑ k, κ k * m k) + ∑ v ∈ D.support, w v * D v, ?_⟩
  simp only [hm, hres, Int.cast_add, Int.cast_sum, Int.cast_mul, mul_add, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring


end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
