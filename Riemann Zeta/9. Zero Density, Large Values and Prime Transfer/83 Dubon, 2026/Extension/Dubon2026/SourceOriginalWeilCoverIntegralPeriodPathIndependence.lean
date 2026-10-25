import Dubon2026.SourceOriginalWeilCoverRegularPathIntegralLaws
import Dubon2026.SourceOriginalWeilCoverSimplePoleRegularPart

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


omit A hRadicand hOrders [NeZero n] in
theorem cover_coeff_regular_off_divisor (D : Divisor ℂ EE) (η : Ω[EE⁄ℂ])
    (hη : ∀ v : Place ℂ EE, -1 ≤ v.ordDifferential η)
    (hres : ∀ v, v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v) (v.uniformizer * v.differentialCoeff η) = (D v : ℂ))
    (v : Place ℂ EE) (hv : D v = 0) : v.differentialCoeff η ∈ v.toValuationSubring := by
  have hz : v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v) (v.uniformizer * v.differentialCoeff η) = 0 := by
    rw [hres, hv, Int.cast_zero]
  simpa only [map_zero, zero_mul, sub_zero] using
    cover_simple_pole_regular_part N n radicand v η (hη v) 0 hz

theorem exp_pathIntegral_eq_of_integral_periods (D : Divisor ℂ EE) (η : Ω[EE⁄ℂ])
    (hη : ∀ v : Place ℂ EE, -1 ≤ v.ordDifferential η)
    (hres : ∀ v, v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v) (v.uniformizer * v.differentialCoeff η) = (D v : ℂ))
    (hper : ∀ (P : Place ℂ EE) (α : CoverPath P P), (∀ t, D (α t) = 0) →
      ∃ m : ℤ, pathIntegral N n radicand A hRadicand hOrders η α = 2 * Real.pi * Complex.I * m)
    {P Q : Place ℂ EE} (γ δ : CoverPath P Q)
    (hγ : ∀ t, D (γ t) = 0) (hδ : ∀ t, D (δ t) = 0) :
    Complex.exp (pathIntegral N n radicand A hRadicand hOrders η γ) = Complex.exp (pathIntegral N n radicand A hRadicand hOrders η δ) := by
  letI := placeTopology N n radicand A hRadicand hOrders
  have hγreg := fun t => cover_coeff_regular_off_divisor N n radicand D η hη hres (γ t) (hγ t)
  have hδreg := fun t => cover_coeff_regular_off_divisor N n radicand D η hη hres (δ t) (hδ t)
  have hδsymm : ∀ t, (δ.symm t).differentialCoeff η ∈ (δ.symm t).toValuationSubring :=
    fun t => hδreg (unitInterval.symm t)
  have hloop : ∀ t, D ((γ.trans δ.symm) t) = 0 := by
    intro t
    rw [Path.trans_apply]
    split_ifs
    · exact hγ _
    · exact hδ _
  obtain ⟨m, hm⟩ := hper P (γ.trans δ.symm) hloop
  rw [pathIntegral_trans_of_coeff_mem N n radicand A hRadicand hOrders γ δ.symm hγreg hδsymm,
    pathIntegral_symm_of_coeff_mem N n radicand A hRadicand hOrders δ hδreg] at hm
  have he : pathIntegral N n radicand A hRadicand hOrders η γ = pathIntegral N n radicand A hRadicand hOrders η δ + (m : ℂ) * (2 * Real.pi * Complex.I) := by
    linear_combination hm
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]


end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
