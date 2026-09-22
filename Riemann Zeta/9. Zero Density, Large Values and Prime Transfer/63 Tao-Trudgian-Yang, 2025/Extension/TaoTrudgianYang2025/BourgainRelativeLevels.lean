import TaoTrudgianYang2025.BourgainCommonBand

/-!
# Shared grids for relative difference multiplicities

The integer level j alone is not a common relative multiplicity when the
component cardinalities differ. Regridding 2^j/|W| on a shared physical
floor retains a factor four count band and its exact ceiling-log loss.
-/

open RiemannZeta.GuthMaynard
open scoped Classical

noncomputable section

namespace TaoTrudgianYang2025

def bourgainRelativeLevel (N τ : ℝ) (p : ℕ) : ℝ :=
  N^(-(|τ|+2))*(2 : ℝ)^p

def bourgainRelativeLevelCount (N τ : ℝ) : ℕ :=
  bourgainZetaBandCount 1 0 (N^(-(|τ|+2)))

theorem bourgainRelativeLevelCount_pos (N τ : ℝ) :
    0 < bourgainRelativeLevelCount N τ := by
  exact bourgainZetaBandCount_pos _ _ _

/-- The finite relative grid has logarithmic length independent of the
component and its selected absolute integer difference level. -/
theorem bourgainRelativeLevelCount_log_bound {N τ : ℝ} (hN : 1 ≤ N) :
    (bourgainRelativeLevelCount N τ : ℝ) ≤
      2+(Real.log 5+(|τ|+2)*Real.log N)/Real.log 2 := by
  have hh := bourgainZetaBandCount_power_log_bound
    (B := 1) (N := N) (U := 0) (A := |τ|+2) (u := 0)
    (by norm_num) hN (by norm_num) (by positivity) (by norm_num) (by norm_num)
  simpa only [bourgainRelativeLevelCount, mul_one, mul_zero, add_zero, zero_add,
    show (4 : ℝ)+1 = 5 by norm_num] using hh

/-- Polynomially bounded positive cardinality gives a common lower
floor for every normalized dyadic difference count. -/
theorem bourgain_relative_difference_floor {N τ : ℝ} {R j : ℕ}
    (hN : 2 ≤ N) (hR : 0 < R) (hsize : (R : ℝ) ≤ 2*N^(|τ|+1))
    (hj : 2^j ≤ R) :
    N^(-(|τ|+2)) ≤ (2 : ℝ)^j/(R : ℝ) ∧ (2 : ℝ)^j/(R : ℝ) ≤ 1 := by
  have hNp : 0 < N := by linarith
  have hRp : (0 : ℝ) < R := by exact_mod_cast hR
  have hcap : (R : ℝ) ≤ N^(|τ|+2) := by
    apply hsize.trans
    calc
      2*N^(|τ|+1) ≤ N*N^(|τ|+1) := by gcongr
      _ = N^(|τ|+2) := by
        rw [show |τ|+2 = (|τ|+1)+1 by ring, Real.rpow_add hNp (|τ|+1) 1, Real.rpow_one]
        ring
  constructor
  · calc
      N^(-(|τ|+2)) = 1/N^(|τ|+2) := by rw [Real.rpow_neg hNp.le, one_div]
      _ ≤ 1/(R : ℝ) := one_div_le_one_div_of_le hRp hcap
      _ ≤ (2 : ℝ)^j/(R : ℝ) := by
        apply div_le_div_of_nonneg_right _ hRp.le
        exact one_le_pow₀ (by norm_num)
  · apply (div_le_one hRp).mpr
    exact_mod_cast hj

/-- Regrid the actual retained heavy level. The same floor and finite
index range apply to every localized component in the physical window. -/
theorem bourgain_retained_relative_level (P : LargeValuePattern)
    {W : Finset ℝ} (hsub : W ⊆ P.reflectedOrdinates) (j : ℕ)
    (hj : 2^j ≤ W.card) {τ δ : ℝ} (hN : 2 ≤ P.N)
    (hδ : δ ≤ 1) (hT : P.T ≤ P.N^(τ+δ)) :
    ∃ p ∈ Finset.range (bourgainRelativeLevelCount P.N τ),
      let d := bourgainRelativeLevel P.N τ p
      0 < d ∧ d ≤ 1 ∧
      d*(W.card : ℝ) ≤ (2 : ℝ)^j ∧ (2 : ℝ)^j < 2*d*(W.card : ℝ) ∧
      (∀ ℓ ∈ bourgainDifferenceLevel W j,
        d*(W.card : ℝ) ≤ (bourgainDifferenceCount W ℓ : ℝ) ∧
        (bourgainDifferenceCount W ℓ : ℝ) < 4*d*(W.card : ℝ)) ∧
      d*((bourgainDifferenceLevel W j).card : ℝ) ≤ 2*(W.card : ℝ) := by
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hW : 0 < W.card := (Nat.pow_pos (by norm_num : 0 < (2 : ℕ))).trans_le hj
  have hWp : (0 : ℝ) < W.card := by exact_mod_cast hW
  have hsize := bourgain_retained_card_le_shared_power P hsub hδ hT
  obtain ⟨hfloor, hupper⟩ := bourgain_relative_difference_floor hN hW hsize hj
  have ha : 0 < P.N^(-(|τ|+2)) := Real.rpow_pos_of_pos hNp _
  have hterminal : (1 : ℝ) <
      P.N^(-(|τ|+2))*(2 : ℝ)^(bourgainRelativeLevelCount P.N τ) := by
    simpa only [bourgainRelativeLevelCount, add_zero, mul_one] using
      (bourgainZetaBandCount_terminal (B := 1) (T := 0) ha)
  obtain ⟨p, hp, hlo, hhi⟩ :=
    exists_bourgain_dyadic_amplitude hfloor (hupper.trans_lt hterminal)
  let d := bourgainRelativeLevel P.N τ p
  have hd : 0 < d := mul_pos ha (by positivity)
  have hd1 : d ≤ 1 := hlo.trans hupper
  have hl : d*(W.card : ℝ) ≤ (2 : ℝ)^j := (le_div_iff₀ hWp).mp hlo
  have hu : (2 : ℝ)^j < 2*d*(W.card : ℝ) := (div_lt_iff₀ hWp).mp hhi
  refine ⟨p, hp, hd, hd1, hl, hu, ?_, ?_⟩
  · intro ℓ hℓ
    have hb := bourgainDifferenceLevel_bounds hℓ
    have hb₁ : (2 : ℝ)^j ≤ (bourgainDifferenceCount W ℓ : ℝ) := by exact_mod_cast hb.1
    have hb₂ : (bourgainDifferenceCount W ℓ : ℝ) < (2 : ℝ)^(j+1) := by exact_mod_cast hb.2
    rw [pow_succ] at hb₂
    exact ⟨hl.trans hb₁, by nlinarith⟩
  · have hc : (2 : ℝ)^j*((bourgainDifferenceLevel W j).card : ℝ) ≤
        2*(W.card : ℝ)^2 := by exact_mod_cast bourgainDifferenceLevel_card_le W j
    have hm := mul_le_mul_of_nonneg_right hl
      (by positivity : (0 : ℝ) ≤ (bourgainDifferenceLevel W j).card)
    have hh : (W.card : ℝ)*(d*((bourgainDifferenceLevel W j).card : ℝ)) ≤
        (W.card : ℝ)*(2*(W.card : ℝ)) := by nlinarith
    exact (mul_le_mul_iff_of_pos_left hWp).mp hh

end TaoTrudgianYang2025
