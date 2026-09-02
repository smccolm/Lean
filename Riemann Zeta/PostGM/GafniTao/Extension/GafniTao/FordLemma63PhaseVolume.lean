import GafniTao.FordLemma63MomentIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Ford Lemma 6.3: exact phase-box volume
-/

open Finset Set MeasureTheory
open scoped BigOperators

namespace GafniTao

noncomputable section

def fordLemma63OmegaLower
    (k M n : ℕ) (u t : ℝ) (j : Fin k) : ℝ :=
  fordTaylorGamma t ((n : ℝ) + u) j - fordLemma63Radius k M j

def fordLemma63OmegaUpper
    (k M n : ℕ) (u t : ℝ) (j : Fin k) : ℝ :=
  fordTaylorGamma t ((n : ℝ) + u) j + fordLemma63Radius k M j

theorem fordLemma63Omega_eq_Icc
    (k M n : ℕ) (u t : ℝ) :
    fordLemma63Omega k M n u t =
      Set.Icc (fordLemma63OmegaLower k M n u t)
        (fordLemma63OmegaUpper k M n u t) := by
  ext β
  simp only [fordLemma63Omega, Set.mem_setOf_eq, Set.mem_Icc, Pi.le_def,
    fordLemma63OmegaLower, fordLemma63OmegaUpper]
  constructor
  · intro h
    constructor
    · intro j
      have hj := h j
      rw [abs_le] at hj
      linarith
    · intro j
      have hj := h j
      rw [abs_le] at hj
      linarith
  · rintro ⟨hl, hu⟩ j
    rw [abs_le]
    constructor
    · have := hl j
      linarith
    · have := hu j
      linarith

theorem fordLemma63OmegaUpper_sub_lower
    (k M n : ℕ) (u t : ℝ) (j : Fin k) :
    fordLemma63OmegaUpper k M n u t j -
        fordLemma63OmegaLower k M n u t j =
      2 * fordLemma63Radius k M j := by
  unfold fordLemma63OmegaUpper fordLemma63OmegaLower
  ring

theorem fordLemma63Radius_nonneg
    (k M : ℕ) (j : Fin k) : 0 ≤ fordLemma63Radius k M j := by
  unfold fordLemma63Radius
  positivity

theorem fordLemma63Omega_volume_toReal
    (k M n : ℕ) (u t : ℝ) :
    (volume (fordLemma63Omega k M n u t)).toReal =
      ∏ j : Fin k, 2 * fordLemma63Radius k M j := by
  rw [fordLemma63Omega_eq_Icc]
  rw [Real.volume_Icc_pi_toReal]
  · apply Finset.prod_congr rfl
    intro j hj
    exact fordLemma63OmegaUpper_sub_lower k M n u t j
  · intro j
    unfold fordLemma63OmegaUpper fordLemma63OmegaLower
    have hj := fordLemma63Radius_nonneg k M j
    linarith

theorem fordLemma63_prod_successor_cast (k : ℕ) :
    (∏ j : Fin k, ((((j : ℕ) + 1 : ℕ) : ℝ))) = (k.factorial : ℝ) := by
  have hnat : (∏ j : Fin k, ((j : ℕ) + 1)) = k.factorial := by
    calc
      (∏ j : Fin k, ((j : ℕ) + 1)) =
          ∏ i ∈ Finset.range k, (i + 1) :=
        (Finset.prod_range (fun i : ℕ => i + 1)).symm
      _ = k.factorial := Finset.prod_range_add_one_eq_factorial k
  exact_mod_cast hnat

theorem fordLemma63_prod_scale_powers (k M : ℕ) :
    (∏ j : Fin k, (M : ℝ) ^ ((j : ℕ) + 1)) =
      (M : ℝ) ^ fordVinogradovKappa k := by
  rw [Finset.prod_pow_eq_pow_sum, sum_fin_degrees]
  rfl

theorem fordLemma63_two_mul_radius
    {k M : ℕ} (hk : 1 ≤ k) (hM : 1 ≤ M) (j : Fin k) :
    2 * fordLemma63Radius k M j =
      1 / (Real.pi * (((j : ℕ) + 1 : ℕ) : ℝ) * (k : ℝ) *
        (M : ℝ) ^ ((j : ℕ) + 1)) := by
  unfold fordLemma63Radius
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  have hj0 : ((((j : ℕ) + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  norm_num only [Nat.cast_add, Nat.cast_one]
  field_simp [Real.pi_ne_zero, hk0, hM0, hj0]

theorem fordLemma63_prod_two_mul_radius
    {k M : ℕ} (hk : 1 ≤ k) (hM : 1 ≤ M) :
    (∏ j : Fin k, 2 * fordLemma63Radius k M j) =
      1 / (Real.pi ^ k * (k.factorial : ℝ) * (k : ℝ) ^ k *
        (M : ℝ) ^ fordVinogradovKappa k) := by
  calc
    (∏ j : Fin k, 2 * fordLemma63Radius k M j) =
        ∏ j : Fin k,
          1 / (Real.pi * (((j : ℕ) + 1 : ℕ) : ℝ) * (k : ℝ) *
            (M : ℝ) ^ ((j : ℕ) + 1)) := by
      apply Finset.prod_congr rfl
      intro j _hj
      exact fordLemma63_two_mul_radius hk hM j
    _ = 1 / ∏ j : Fin k,
          (Real.pi * (((j : ℕ) + 1 : ℕ) : ℝ) * (k : ℝ) *
            (M : ℝ) ^ ((j : ℕ) + 1)) := by
      rw [Finset.prod_div_distrib]
      simp
    _ = 1 / (Real.pi ^ k * (k.factorial : ℝ) * (k : ℝ) ^ k *
          (M : ℝ) ^ fordVinogradovKappa k) := by
      congr 1
      simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
      rw [fordLemma63_prod_successor_cast, fordLemma63_prod_scale_powers]

theorem fordLemma63Omega_volume_exact
    {k M n : ℕ} {u t : ℝ} (hk : 1 ≤ k) (hM : 1 ≤ M) :
    (volume (fordLemma63Omega k M n u t)).toReal =
      1 / (Real.pi ^ k * (k.factorial : ℝ) * (k : ℝ) ^ k *
        (M : ℝ) ^ fordVinogradovKappa k) := by
  rw [fordLemma63Omega_volume_toReal,
    fordLemma63_prod_two_mul_radius hk hM]

#print axioms fordLemma63Omega_eq_Icc
#print axioms fordLemma63Omega_volume_toReal
#print axioms fordLemma63Omega_volume_exact

end

end GafniTao
