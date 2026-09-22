import TaoTrudgianYang2025.JutilaWindowBound
import TaoTrudgianYang2025.ClassicalMeanSquareBound

/-!
# The exact source Jutila optimization

The optimized local height is the minimum of the two source exponents.
Below the allowed local range the proved mean-square bound is sufficient.
-/

noncomputable section

namespace TaoTrudgianYang2025

def jutilaLocalExponent (k : ℕ) (σ : ℝ) : ℝ :=
  min ((4-2/(k : ℝ))*σ-(2-2/(k : ℝ))) ((8*(k : ℝ)-2)*σ-6*k+2)

def jutilaLargeValueExponent (k : ℕ) (σ τ : ℝ) : ℝ :=
  max (2-2*σ) (max (τ+4-2/(k : ℝ)-(6-2/(k : ℝ))*σ) (τ+(6-8*σ)*k))

/-- The optimized subdivision exponent is exactly the paper's displayed
three-piece maximum, with the original integer parameter. -/
theorem jutila_optimization_identity (k : ℕ) (σ τ : ℝ) :
    2-2*σ+max 0 (τ-jutilaLocalExponent k σ) = jutilaLargeValueExponent k σ τ := by
  unfold jutilaLocalExponent jutilaLargeValueExponent
  simp only [min_def, max_def]
  split_ifs <;> nlinarith

/-- Both actual local terms lie below the diagonal exponent at the
chosen local height. -/
theorem jutila_local_exponent_constraints (k : ℕ) (hk : 0 < k) (σ : ℝ) :
    (k : ℝ)*jutilaLocalExponent k σ+2*k-4*k*σ ≤ 2-2*σ ∧
    jutilaLocalExponent k σ+6*k-8*k*σ ≤ 2-2*σ := by
  have hkp : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 := min_le_left ((4-2/(k : ℝ))*σ-(2-2/(k : ℝ)))
    ((8*(k : ℝ)-2)*σ-6*k+2)
  have h2 := min_le_right ((4-2/(k : ℝ))*σ-(2-2/(k : ℝ)))
    ((8*(k : ℝ)-2)*σ-6*k+2)
  have hm := mul_le_mul_of_nonneg_left h1 hkp.le
  have he : (k : ℝ)*((4-2/(k : ℝ))*σ-(2-2/(k : ℝ)))+2*k-4*k*σ =
      2-2*σ := by field_simp; ring
  change (k : ℝ)*jutilaLocalExponent k σ+2*k-4*k*σ ≤ 2-2*σ ∧ _
  dsimp [jutilaLocalExponent]
  constructor <;> nlinarith

/-- The complete source Jutila bound, for every positive integer k.
The domain is the paper's fixed 1/2 ≤ σ ≤ 1 and τ ≥ 0. -/
theorem jutila_largeValueBound (k : ℕ) (hk : 0 < k) {σ τ : ℝ}
    (hσLower : 1/2 ≤ σ) (_hσUpper : σ ≤ 1) (hτ : 0 ≤ τ) :
    IsLargeValueBound σ τ (jutilaLargeValueExponent k σ τ) := by
  by_cases hσ : σ ≤ 3/4
  · apply (obvious_largeValueBound σ hτ).mono
    have hh : 0 ≤ (6-8*σ)*(k : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg _)
    exact (show τ ≤ τ+(6-8*σ)*k by linarith).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  have hσp : 3/4 < σ := lt_of_not_ge hσ
  by_cases hlocal : 1 ≤ jutilaLocalExponent k σ
  · have hc := jutila_local_exponent_constraints k hk σ
    simpa only [jutila_optimization_identity] using
      (jutila_largeValueBound_of_local_exponent k hk hσp hlocal hc.1 hc.2 (τ := τ))
  · apply (meanSquare_largeValueBound (τ := τ)
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/2) hσLower)).mono
    rw [← jutila_optimization_identity]
    apply max_le
    · have hh := le_max_left (0 : ℝ) (τ-jutilaLocalExponent k σ)
      linarith
    · have hh := le_max_right (0 : ℝ) (τ-jutilaLocalExponent k σ)
      have hl : jutilaLocalExponent k σ ≤ 1 := le_of_not_ge hlocal
      linarith

theorem largeValueExponent_le_jutila (k : ℕ) (hk : 0 < k) {σ τ : ℝ}
    (hσLower : 1/2 ≤ σ) (hσUpper : σ ≤ 1) (hτ : 0 ≤ τ) :
    largeValueExponent σ τ ≤ (jutilaLargeValueExponent k σ τ : EReal) :=
  largeValueExponent_le_of_bound (jutila_largeValueBound k hk hσLower hσUpper hτ)

theorem zetaLargeValueExponent_le_jutila (k : ℕ) (hk : 0 < k) {σ τ : ℝ}
    (hσLower : 1/2 ≤ σ) (hσUpper : σ ≤ 1) (hτ : 0 ≤ τ) :
    zetaLargeValueExponent σ τ ≤ (jutilaLargeValueExponent k σ τ : EReal) :=
  zetaLargeValueExponent_le_of_bound (jutila_largeValueBound k hk hσLower hσUpper hτ).toZeta

end TaoTrudgianYang2025
