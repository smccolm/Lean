import Dubon2026.SourceOriginalWeilCoverIntegralPeriodPathIndependence
import Dubon2026.SourceOriginalWeilCoverDivisorAvoidingPaths

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


/-- A chosen actual continuous path avoiding the actual divisor support. -/
def coverDivisorAvoidingPath (D : Divisor ℂ EE) (P Q : Place ℂ EE)
    (hP : D P = 0) (hQ : D Q = 0) : CoverPath P Q :=
  Classical.choose (exists_cover_path_avoiding_divisor N n radicand A hRadicand hOrders D P Q hP hQ)

theorem coverDivisorAvoidingPath_avoids (D : Divisor ℂ EE) (P Q : Place ℂ EE)
    (hP : D P = 0) (hQ : D Q = 0) (t : unitInterval) :
    D (coverDivisorAvoidingPath N n radicand A hRadicand hOrders D P Q hP hQ t) = 0 :=
  Classical.choose_spec (exists_cover_path_avoiding_divisor N n radicand A hRadicand hOrders D P Q hP hQ) t

/-- Exponentiation of an actual original integral from a fixed point outside
the divisor support; the value at a support point is set to zero. -/
def coverPeriodExponential (D : Divisor ℂ EE) (η : Ω[EE⁄ℂ])
    (P₀ : Place ℂ EE) (hP₀ : D P₀ = 0) (P : Place ℂ EE) : ℂ := by
  letI := placeTopology N n radicand A hRadicand hOrders
  classical
  exact if hP : D P = 0 then
    Complex.exp (pathIntegral N n radicand A hRadicand hOrders η (coverDivisorAvoidingPath N n radicand A hRadicand hOrders D P₀ P hP₀ hP)) else 0

theorem coverPeriodExponential_ne_zero (D : Divisor ℂ EE) (η : Ω[EE⁄ℂ])
    (P₀ : Place ℂ EE) (hP₀ : D P₀ = 0) (P : Place ℂ EE) (hP : D P = 0) :
    coverPeriodExponential N n radicand A hRadicand hOrders D η P₀ hP₀ P ≠ 0 := by
  letI := placeTopology N n radicand A hRadicand hOrders
  rw [coverPeriodExponential, dif_pos hP]
  exact Complex.exp_ne_zero _

theorem coverPeriodExponential_eq_path (D : Divisor ℂ EE) (η : Ω[EE⁄ℂ])
    (hη : ∀ v : Place ℂ EE, -1 ≤ v.ordDifferential η)
    (hres : ∀ v, v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v) (v.uniformizer * v.differentialCoeff η) = (D v : ℂ))
    (hper : ∀ (P : Place ℂ EE) (α : CoverPath P P), (∀ t, D (α t) = 0) →
      ∃ m : ℤ, pathIntegral N n radicand A hRadicand hOrders η α = 2 * Real.pi * Complex.I * m)
    (P₀ : Place ℂ EE) (hP₀ : D P₀ = 0) (P : Place ℂ EE) (hP : D P = 0)
    (γ : CoverPath P₀ P) (hγ : ∀ t, D (γ t) = 0) :
    coverPeriodExponential N n radicand A hRadicand hOrders D η P₀ hP₀ P = Complex.exp (pathIntegral N n radicand A hRadicand hOrders η γ) := by
  letI := placeTopology N n radicand A hRadicand hOrders
  rw [coverPeriodExponential, dif_pos hP]
  exact exp_pathIntegral_eq_of_integral_periods N n radicand A hRadicand hOrders D η hη hres hper _ γ
    (coverDivisorAvoidingPath_avoids N n radicand A hRadicand hOrders D P₀ P hP₀ hP) hγ

theorem coverPeriodExponential_transport (D : Divisor ℂ EE) (η : Ω[EE⁄ℂ])
    (hη : ∀ v : Place ℂ EE, -1 ≤ v.ordDifferential η)
    (hres : ∀ v, v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v) (v.uniformizer * v.differentialCoeff η) = (D v : ℂ))
    (hper : ∀ (P : Place ℂ EE) (α : CoverPath P P), (∀ t, D (α t) = 0) →
      ∃ m : ℤ, pathIntegral N n radicand A hRadicand hOrders η α = 2 * Real.pi * Complex.I * m)
    (P₀ : Place ℂ EE) (hP₀ : D P₀ = 0) (P Q : Place ℂ EE)
    (hP : D P = 0) (hQ : D Q = 0) (σ : CoverPath P Q) (hσ : ∀ t, D (σ t) = 0) :
    coverPeriodExponential N n radicand A hRadicand hOrders D η P₀ hP₀ Q =
      coverPeriodExponential N n radicand A hRadicand hOrders D η P₀ hP₀ P * Complex.exp (pathIntegral N n radicand A hRadicand hOrders η σ) := by
  letI := placeTopology N n radicand A hRadicand hOrders
  let γ := coverDivisorAvoidingPath N n radicand A hRadicand hOrders D P₀ P hP₀ hP
  have hγ : ∀ t, D (γ t) = 0 := coverDivisorAvoidingPath_avoids N n radicand A hRadicand hOrders D P₀ P hP₀ hP
  have hconcat : ∀ t, D ((γ.trans σ) t) = 0 := by
    intro t
    rw [Path.trans_apply]
    split_ifs
    · exact hγ _
    · exact hσ _
  rw [coverPeriodExponential_eq_path N n radicand A hRadicand hOrders D η hη hres hper P₀ hP₀ Q hQ (γ.trans σ) hconcat,
    coverPeriodExponential_eq_path N n radicand A hRadicand hOrders D η hη hres hper P₀ hP₀ P hP γ hγ,
    pathIntegral_trans_of_coeff_mem N n radicand A hRadicand hOrders γ σ
      (fun t => cover_coeff_regular_off_divisor N n radicand D η hη hres (γ t) (hγ t))
      (fun t => cover_coeff_regular_off_divisor N n radicand D η hη hres (σ t) (hσ t)),
    Complex.exp_add]


end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
