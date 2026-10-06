import Dubon2026.IsolatedTorusSplit

/-! # Uniform lower bound from the actual isolated-prime conditional Haar integral -/

namespace Dubon2026

open MeasureTheory

noncomputable section

theorem exists_uniform_isolated_haar_lower {K : ℝ} (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℕ → ℂ) (N : ℕ) (σ : ℝ)
      (S : Finset (PrimeCoordinate N)) [Nonempty ↥S],
      (∀ p ∈ S, N < 2 * p.val) → 5 ≤ Fintype.card ↥S →
      (∀ p : ↥S, a p.val.val ≠ 0) →
      steinhausMaxCoefficient (fun p : ↥S => ‖a p.val.val‖ * (p.val.val : ℝ) ^ (-σ)) /
        steinhausMinCoefficient (fun p : ↥S => ‖a p.val.val‖ * (p.val.val : ℝ) ^ (-σ)) ≤ K →
      (1 / 2 : ℝ) * Real.log (∑ p : ↥S, ‖a p.val.val‖ ^ 2 * (p.val.val : ℝ) ^ (-2 * σ)) - C ≤
        haarLogPotential a N σ := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_complex_steinhaus_log hK
  refine ⟨C, hC, ?_⟩
  intro a N σ S _ hS hm ha hcomp
  let d : ↥S → ℂ := fun p => a p.val.val * (p.val.val : ℂ) ^ (-(σ : ℂ))
  have hd : ∀ p, d p ≠ 0 := by
    intro p
    apply norm_pos_iff.mp
    dsimp only [d]
    rw [norm_mul, norm_nat_cpow_neg_real]
    exact mul_pos (norm_pos_iff.mpr (ha p))
      (Real.rpow_pos_of_pos (by exact_mod_cast (mem_primesUpTo.mp p.val.property).1.pos) _)
  have hcomp' : steinhausMaxCoefficient (fun p => ‖d p‖) /
      steinhausMinCoefficient (fun p => ‖d p‖) ≤ K := by
    simpa only [d, norm_mul, norm_nat_cpow_neg_real] using hcomp
  let A : ℝ := Real.log (Real.sqrt (∑ p, ‖d p‖ ^ 2)) - C
  have hinner (w : ComplementaryPrimeCoordinates S → UnitAddCircle) :
      A ≤ ∫ z : ↥S → UnitAddCircle,
        Real.log ‖bohrOnTorus a N σ ((primeTorusSplit N S).symm (z, w))‖ ∂steinhausHaar ↥S := by
    have hh := (hbound ↥S d hd hm hcomp' (isolatedBohrRemainder a N σ S w)).2
    simpa only [bohrOnTorus_conditioned a N σ S hS, d] using hh
  have hi := integrable_split_bohr_log a N σ S
  have hl : A ≤ haarLogPotential a N σ := by
    calc
      A = ∫ _w : ComplementaryPrimeCoordinates S → UnitAddCircle, A
          ∂steinhausHaar (ComplementaryPrimeCoordinates S) := by simp
      _ ≤ ∫ w : ComplementaryPrimeCoordinates S → UnitAddCircle,
          (∫ z : ↥S → UnitAddCircle,
            Real.log ‖bohrOnTorus a N σ ((primeTorusSplit N S).symm (z, w))‖ ∂steinhausHaar ↥S)
            ∂steinhausHaar (ComplementaryPrimeCoordinates S) :=
        integral_mono (integrable_const _) hi.integral_prod_right hinner
      _ = ∫ p, Real.log ‖bohrOnTorus a N σ ((primeTorusSplit N S).symm p)‖
          ∂(steinhausHaar ↥S).prod (steinhausHaar (ComplementaryPrimeCoordinates S)) :=
        (integral_prod_symm _ hi).symm
      _ = haarLogPotential a N σ := integral_split_bohr_log a N σ S
  have henergy : (∑ p, ‖d p‖ ^ 2) =
      ∑ p : ↥S, ‖a p.val.val‖ ^ 2 * (p.val.val : ℝ) ^ (-2 * σ) := by
    simp only [d, norm_coefficient_sq]
  have he : A = (1 / 2 : ℝ) * Real.log
      (∑ p : ↥S, ‖a p.val.val‖ ^ 2 * (p.val.val : ℝ) ^ (-2 * σ)) - C := by
    dsimp only [A]
    rw [Real.log_sqrt (Finset.sum_nonneg (fun p _ => sq_nonneg ‖d p‖)), henergy]
    ring
  rwa [he] at hl

theorem exists_uniform_isolated_jessen_lower {K : ℝ} (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℕ → ℂ) (N : ℕ), 1 ≤ N → a 1 ≠ 0 →
      ∀ (σ : ℝ) (S : Finset (PrimeCoordinate N)) [Nonempty ↥S],
      (∀ p ∈ S, N < 2 * p.val) → 5 ≤ Fintype.card ↥S →
      (∀ p : ↥S, a p.val.val ≠ 0) →
      steinhausMaxCoefficient (fun p : ↥S => ‖a p.val.val‖ * (p.val.val : ℝ) ^ (-σ)) /
        steinhausMinCoefficient (fun p : ↥S => ‖a p.val.val‖ * (p.val.val : ℝ) ^ (-σ)) ≤ K →
      (1 / 2 : ℝ) * Real.log (∑ p : ↥S, ‖a p.val.val‖ ^ 2 * (p.val.val : ℝ) ^ (-2 * σ)) - C ≤
        jessenFunction a N σ := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_isolated_haar_lower hK
  refine ⟨C, hC, ?_⟩
  intro a N hN ha σ S _ hS hm hap hcomp
  rw [jessenFunction_eq_haar hN ha]
  exact hbound a N σ S hS hm hap hcomp

end

end Dubon2026
