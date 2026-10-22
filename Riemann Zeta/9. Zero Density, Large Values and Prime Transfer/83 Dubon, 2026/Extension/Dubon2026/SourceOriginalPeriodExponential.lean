import Dubon2026.SourceOriginalIntegralPeriodPathIndependence
import Dubon2026.SourceOriginalDivisorAvoidingPaths

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
global meromorphic exponential. Actual divisor-avoiding paths define the
exponential of the original differential integral. Integral loop periods
prove independence of the chosen path and transport along every avoiding
path. The period-correction theorem and local meromorphic gluing remain open.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology
local notation "F" => modularFunctionFieldOver N ℂ

/-- A chosen actual continuous path avoiding the actual divisor support. -/
def originalDivisorAvoidingPath (D : Divisor ℂ F) (P Q : Place ℂ F)
    (hP : D P = 0) (hQ : D Q = 0) : Path P Q :=
  Classical.choose (exists_original_path_avoiding_divisor N D P Q hP hQ)

theorem originalDivisorAvoidingPath_avoids (D : Divisor ℂ F) (P Q : Place ℂ F)
    (hP : D P = 0) (hQ : D Q = 0) (t : unitInterval) :
    D (originalDivisorAvoidingPath N D P Q hP hQ t) = 0 :=
  Classical.choose_spec (exists_original_path_avoiding_divisor N D P Q hP hQ) t

/-- Exponentiation of an actual original integral from a fixed point outside
the divisor support; the value at a support point is set to zero. -/
def originalPeriodExponential (D : Divisor ℂ F) (η : Ω[F⁄ℂ])
    (P₀ : Place ℂ F) (hP₀ : D P₀ = 0) (P : Place ℂ F) : ℂ := by
  classical
  exact if hP : D P = 0 then
    Complex.exp (pathIntegral N η (originalDivisorAvoidingPath N D P₀ P hP₀ hP)) else 0

theorem originalPeriodExponential_ne_zero (D : Divisor ℂ F) (η : Ω[F⁄ℂ])
    (P₀ : Place ℂ F) (hP₀ : D P₀ = 0) (P : Place ℂ F) (hP : D P = 0) :
    originalPeriodExponential N D η P₀ hP₀ P ≠ 0 := by
  rw [originalPeriodExponential, dif_pos hP]
  exact Complex.exp_ne_zero _

theorem originalPeriodExponential_eq_path (D : Divisor ℂ F) (η : Ω[F⁄ℂ])
    (hη : ∀ v : Place ℂ F, -1 ≤ v.ordDifferential η)
    (hres : ∀ v, originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff η) = (D v : ℂ))
    (hper : ∀ (P : Place ℂ F) (α : Path P P), (∀ t, D (α t) = 0) →
      ∃ m : ℤ, pathIntegral N η α = 2 * Real.pi * Complex.I * m)
    (P₀ : Place ℂ F) (hP₀ : D P₀ = 0) (P : Place ℂ F) (hP : D P = 0)
    (γ : Path P₀ P) (hγ : ∀ t, D (γ t) = 0) :
    originalPeriodExponential N D η P₀ hP₀ P = Complex.exp (pathIntegral N η γ) := by
  rw [originalPeriodExponential, dif_pos hP]
  exact exp_pathIntegral_eq_of_integral_periods N D η hη hres hper _ γ
    (originalDivisorAvoidingPath_avoids N D P₀ P hP₀ hP) hγ

theorem originalPeriodExponential_transport (D : Divisor ℂ F) (η : Ω[F⁄ℂ])
    (hη : ∀ v : Place ℂ F, -1 ≤ v.ordDifferential η)
    (hres : ∀ v, originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff η) = (D v : ℂ))
    (hper : ∀ (P : Place ℂ F) (α : Path P P), (∀ t, D (α t) = 0) →
      ∃ m : ℤ, pathIntegral N η α = 2 * Real.pi * Complex.I * m)
    (P₀ : Place ℂ F) (hP₀ : D P₀ = 0) (P Q : Place ℂ F)
    (hP : D P = 0) (hQ : D Q = 0) (σ : Path P Q) (hσ : ∀ t, D (σ t) = 0) :
    originalPeriodExponential N D η P₀ hP₀ Q =
      originalPeriodExponential N D η P₀ hP₀ P * Complex.exp (pathIntegral N η σ) := by
  let γ := originalDivisorAvoidingPath N D P₀ P hP₀ hP
  have hγ : ∀ t, D (γ t) = 0 := originalDivisorAvoidingPath_avoids N D P₀ P hP₀ hP
  have hconcat : ∀ t, D ((γ.trans σ) t) = 0 := by
    intro t
    rw [Path.trans_apply]
    split_ifs
    · exact hγ _
    · exact hσ _
  rw [originalPeriodExponential_eq_path N D η hη hres hper P₀ hP₀ Q hQ (γ.trans σ) hconcat,
    originalPeriodExponential_eq_path N D η hη hres hper P₀ hP₀ P hP γ hγ,
    pathIntegral_trans_of_coeff_mem N γ σ
      (fun t => original_coeff_regular_off_divisor N D η hη hres (γ t) (hγ t))
      (fun t => original_coeff_regular_off_divisor N D η hη hres (σ t) (hσ t)),
    Complex.exp_add]

end
end Dubon2026.SourceFunctionField.OriginalChart
