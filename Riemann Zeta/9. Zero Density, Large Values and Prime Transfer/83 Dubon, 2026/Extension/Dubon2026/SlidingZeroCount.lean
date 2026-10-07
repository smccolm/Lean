import Dubon2026.TwistCountBound
import Dubon2026.VerticalZeroTranslation

/-! # Sliding windows of the actual zero set

The count along the prime torus orbit is exactly the count of original zeros in
a vertically translated window. On a bounded range of translations, one fixed
finite zero set supplies an indicator-sum formula with the actual multiplicities.
-/

namespace Dubon2026

open Set Complex
open scoped BigOperators

noncomputable section

/-- Original zeros in a translated open rectangle, obtained by exact translation. -/
def slidingZerosFinset (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (ha : a 1 ≠ 0)
    (l u H τ : ℝ) : Finset ℂ :=
  (zerosInOpenRectangleFinset (twistedCoefficients a N (primeTorusFlow N τ)) N hN
    (by rwa [twistedCoefficients_one]) l u H).image (fun s => s + I * τ)

theorem mem_slidingZerosFinset (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (ha : a 1 ≠ 0)
    (l u H τ : ℝ) (s : ℂ) :
    s ∈ slidingZerosFinset a N hN ha l u H τ ↔
      l < s.re ∧ s.re < u ∧ |s.im - τ| < H ∧ dirichletSum a N s = 0 := by
  classical
  unfold slidingZerosFinset
  constructor
  · intro hs
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hs
    rw [mem_zerosInOpenRectangleFinset, dirichletSum_twist_height] at hw
    simpa using hw
  · intro hs
    apply Finset.mem_image.mpr
    refine ⟨s - I * τ, ?_, sub_add_cancel _ _⟩
    rw [mem_zerosInOpenRectangleFinset, dirichletSum_twist_height, sub_add_cancel]
    simpa using hs

/-- The literal multiplicity-weighted count in a translated open rectangle. -/
def slidingZeroCount (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (ha : a 1 ≠ 0)
    (l u H τ : ℝ) : ℕ :=
  ∑ s ∈ slidingZerosFinset a N hN ha l u H τ, zeroMultiplicity a N s

theorem slidingZeroCount_eq_twistZeroCount (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u H τ : ℝ) :
    slidingZeroCount a N hN ha l u H τ =
      twistZeroCount a N hN ha l u H (primeTorusFlow N τ) := by
  classical
  unfold slidingZeroCount slidingZerosFinset
  rw [Finset.sum_image]
  · simp only [← zeroMultiplicity_twist_height, twistZeroCount, verticalZeroCount]
  · intro s _ w _ he
    exact add_right_cancel he

theorem slidingZerosFinset_eq_filter (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u H : ℝ) {T τ : ℝ} (hτ : |τ| ≤ T) :
    slidingZerosFinset a N hN ha l u H τ =
      (zerosInOpenRectangleFinset a N hN ha l u (T + H)).filter
        (fun s => |s.im - τ| < H) := by
  classical
  ext s
  rw [mem_slidingZerosFinset, Finset.mem_filter, mem_zerosInOpenRectangleFinset]
  constructor
  · rintro ⟨hl, hu, ht, hz⟩
    refine ⟨⟨hl, hu, ?_, hz⟩, ht⟩
    have hb : |s.im| ≤ |s.im - τ| + |τ| := by
      simpa only [sub_add_cancel] using abs_add_le (s.im - τ) τ
    linarith
  · rintro ⟨⟨hl, hu, _, hz⟩, ht⟩
    exact ⟨hl, hu, ht, hz⟩

theorem slidingZeroCount_eq_sum_indicators (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u H : ℝ) {T τ : ℝ} (hτ : |τ| ≤ T) :
    (slidingZeroCount a N hN ha l u H τ : ℝ) =
      ∑ s ∈ zerosInOpenRectangleFinset a N hN ha l u (T + H),
        (Ioo (s.im - H) (s.im + H)).indicator
          (fun _ => (zeroMultiplicity a N s : ℝ)) τ := by
  classical
  rw [slidingZeroCount, slidingZerosFinset_eq_filter a N hN ha l u H hτ,
    Nat.cast_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s _
  have he : |s.im - τ| < H ↔ τ ∈ Ioo (s.im - H) (s.im + H) := by
    rw [abs_lt, mem_Ioo]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  simp only [he, Set.indicator_apply]

end

end Dubon2026
