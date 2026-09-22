import TaoTrudgianYang2025.BourgainBandOccupancy

/-!
# Finite dyadic amplitude selection with an actual terminal bound

The low-amplitude contribution is kept. The number of amplitude bands is
a concrete ceiling logarithm; the actual zeta growth theorem supplies its
terminal majorant.
-/

open MeasureTheory Set
open scoped Interval Classical

noncomputable section

namespace TaoTrudgianYang2025

/-- Every value between a positive floor and a finite dyadic terminal
bound lies in an actual left-closed, right-open band. -/
theorem exists_bourgain_dyadic_amplitude {a x : ℝ} (hx : a ≤ x)
    {J : ℕ} (hupper : x < a*(2 : ℝ)^J) :
    ∃ j ∈ Finset.range J, a*(2 : ℝ)^j ≤ x ∧ x < 2*(a*(2 : ℝ)^j) := by
  induction J with
  | zero => simp only [pow_zero, mul_one] at hupper; exact False.elim (not_lt_of_ge hx hupper)
  | succ J ih =>
    by_cases h : x < a*(2 : ℝ)^J
    · obtain ⟨j, hj, hlo, hhi⟩ := ih h
      exact ⟨j, Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp hj) (Nat.lt_succ_self J)),
        hlo, hhi⟩
    · refine ⟨J, Finset.mem_range.mpr (Nat.lt_succ_self J), le_of_not_gt h, ?_⟩
      convert hupper using 1
      rw [pow_succ]
      ring

/-- A ceiling-logarithmic number of amplitude bands; the extra final band
makes the terminal bound strict even at exact powers of two. -/
def bourgainZetaBandCount (B T a : ℝ) : ℕ :=
  Nat.clog 2 (Nat.ceil (B*(1+T)/a)) + 1

theorem bourgainZetaBandCount_pos (B T a : ℝ) :
    0 < bourgainZetaBandCount B T a := by
  exact Nat.succ_pos _

theorem bourgainZetaBandCount_terminal {B T a : ℝ} (ha : 0 < a) :
    B*(1+T) < a*(2 : ℝ)^(bourgainZetaBandCount B T a) := by
  have hc : B*(1+T)/a ≤ (Nat.ceil (B*(1+T)/a) : ℝ) := Nat.le_ceil _
  have hp : (Nat.ceil (B*(1+T)/a) : ℝ) ≤
      (2 : ℝ)^(Nat.clog 2 (Nat.ceil (B*(1+T)/a))) := by
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < (2 : ℕ)) (Nat.ceil (B*(1+T)/a))
  have hbase : B*(1+T) ≤ a*(2 : ℝ)^(Nat.clog 2 (Nat.ceil (B*(1+T)/a))) := by
    have h := (div_le_iff₀ ha).mp (hc.trans hp)
    simpa only [mul_comm] using h
  dsimp only [bourgainZetaBandCount]
  rw [pow_succ]
  have hpositive : 0 < a*(2 : ℝ)^(Nat.clog 2 (Nat.ceil (B*(1+T)/a))) := by positivity
  nlinarith

/-- The terminal majorant is derived from the actual critical-line zeta
function, uniformly in the floor and spatial radius. -/
theorem exists_bourgainZetaBand_terminal :
    ∃ B : ℝ, 0 < B ∧ ∀ T a : ℝ, 0 < a → ∀ t ∈ Icc (-T) T,
      zetaMomentCriticalNorm t < a*(2 : ℝ)^(bourgainZetaBandCount B T a) := by
  obtain ⟨B, hB, hgrowth⟩ := exists_zetaMomentCriticalNorm_le_linear
  refine ⟨B, hB, ?_⟩
  intro T a ha t ht
  have hat : |t| ≤ T := abs_le.mpr ht
  exact ((hgrowth t).trans (by gcongr)).trans_lt (bourgainZetaBandCount_terminal ha)

/-- The actual squared zeta norm is dominated by a low floor plus a finite
sum of actual band indicators. -/
theorem bourgainZetaBand_square_partition {T a t : ℝ}
    (ht : t ∈ Icc (-T) T) {J : ℕ}
    (hterminal : zetaMomentCriticalNorm t < a*(2 : ℝ)^J) :
    zetaMomentCriticalNorm t^2 ≤ a^2 +
      ∑ j ∈ Finset.range J, (2*(a*(2 : ℝ)^j))^2 *
        (bourgainZetaBand T (a*(2 : ℝ)^j)).indicator (fun _ => (1 : ℝ)) t := by
  have hnonneg (j : ℕ) (_hj : j ∈ Finset.range J) : 0 ≤
      (2*(a*(2 : ℝ)^j))^2 *
        (bourgainZetaBand T (a*(2 : ℝ)^j)).indicator (fun _ => (1 : ℝ)) t := by
    by_cases h : t ∈ bourgainZetaBand T (a*(2 : ℝ)^j) <;> simp [h, sq_nonneg]
  by_cases hlow : zetaMomentCriticalNorm t < a
  · have hsq := pow_le_pow_left₀ (show 0 ≤ zetaMomentCriticalNorm t from norm_nonneg _)
      hlow.le 2
    have hsum := Finset.sum_nonneg hnonneg
    linarith
  · obtain ⟨j, hj, hlo, hhi⟩ :=
      exists_bourgain_dyadic_amplitude (le_of_not_gt hlow) hterminal
    have hmem : t ∈ bourgainZetaBand T (a*(2 : ℝ)^j) :=
      (mem_bourgainZetaBand _ _ _).mpr ⟨ht.1, ht.2, hlo, hhi⟩
    have hsingle := Finset.single_le_sum hnonneg hj
    rw [Set.indicator_of_mem hmem, mul_one] at hsingle
    have hsq := pow_le_pow_left₀ (show 0 ≤ zetaMomentCriticalNorm t from norm_nonneg _)
      hhi.le 2
    linarith [sq_nonneg a]

end TaoTrudgianYang2025
