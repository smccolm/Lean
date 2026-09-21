import TaoTrudgianYang2025.AtkinsonCoefficientEnergy

/-!
# Dyadic phase maxima and their finite Gram budget

Discarding Gaussian damping gives a proved upper bound, while the source
cutoff remains explicit. Cauchy--Schwarz over the dyadic indices consumes
the actual height-dependent-prefix Gram theorem on each block.
-/

noncomputable section

open Complex

namespace TaoTrudgianYang2025

def atkinsonUndampedDyadicPhaseBound (T : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (Nat.clog 2 N),
    ((2^j:ℕ):ℝ)^(-(1/4:ℝ))*atkinsonPhaseBlockMax T (2^j) (2^j)

theorem atkinsonUndampedDyadicPhaseBound_nonneg (T : ℝ) (N : ℕ) :
    0 ≤ atkinsonUndampedDyadicPhaseBound T N := by
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (atkinsonPhaseBlockMax_nonneg _ _ _))

theorem atkinsonUndampedDyadicPhaseBound_mono (T : ℝ) {N K : ℕ} (hNK : N ≤ K) :
    atkinsonUndampedDyadicPhaseBound T N ≤ atkinsonUndampedDyadicPhaseBound T K := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.clog_mono_right 2 hNK))
  intro j _ _
  exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (atkinsonPhaseBlockMax_nonneg _ _ _)

theorem atkinsonFullDyadicPhaseBound_le_undamped {T : ℝ} (hT : 0 < T) (G : ℝ) (N : ℕ) :
    atkinsonFullDyadicPhaseBound T G N ≤ atkinsonUndampedDyadicPhaseBound T N := by
  apply Finset.sum_le_sum
  intro j _
  have he : Real.exp (-(G^2*((2^j:ℕ):ℝ))/(12*T)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg (sq_nonneg G) (Nat.cast_nonneg _)))
      (by positivity)
  calc
    _ ≤ (((2^j:ℕ):ℝ)^(-(1/4:ℝ))*1)*atkinsonPhaseBlockMax T (2^j) (2^j) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (atkinsonPhaseBlockMax_nonneg _ _ _)
    _ = _ := by rw [mul_one]

def atkinsonDyadicGramBudget (N : ℕ) (W : Finset ℝ) : ℝ :=
  (Nat.clog 2 N : ℝ)*∑ j ∈ Finset.range (Nat.clog 2 N),
    (((2^j:ℕ):ℝ)^(-(1/4:ℝ)))^2*atkinsonBlockCoefficientEnergy (2^j) (2^j)*
      ∑ t ∈ W, ∑ u ∈ W, atkinsonPrefixGramMax (2^j) (2^j) t u

theorem atkinsonDyadicGramBudget_nonneg (N : ℕ) (W : Finset ℝ) :
    0 ≤ atkinsonDyadicGramBudget N W := by
  apply mul_nonneg (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg (mul_nonneg (sq_nonneg _) (atkinsonBlockCoefficientEnergy_nonneg _ _))
  exact Finset.sum_nonneg (fun t _ => Finset.sum_nonneg (fun u _ =>
    atkinsonPrefixGramMax_nonneg _ _ t u))

theorem sum_atkinsonUndampedDyadicPhaseBound_sq_le_budget (N : ℕ) (W : Finset ℝ) :
    (∑ t ∈ W, atkinsonUndampedDyadicPhaseBound t N)^2 ≤ atkinsonDyadicGramBudget N W := by
  let S : ℕ → ℝ := fun j => ∑ t ∈ W, atkinsonPhaseBlockMax t (2^j) (2^j)
  let w : ℕ → ℝ := fun j => ((2^j:ℕ):ℝ)^(-(1/4:ℝ))
  have he : (∑ t ∈ W, atkinsonUndampedDyadicPhaseBound t N) =
      ∑ j ∈ Finset.range (Nat.clog 2 N), w j*S j := by
    unfold atkinsonUndampedDyadicPhaseBound
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact (Finset.mul_sum _ _ _).symm
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (Nat.clog 2 N))
    (fun _ => (1:ℝ)) (fun j => w j*S j)
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one] at hcs
  rw [he]
  apply hcs.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro j _
  rw [mul_pow]
  apply (mul_le_mul_of_nonneg_left (sum_atkinsonPhaseBlockMax_sq_le_gramMax (2^j) (2^j) W)
    (sq_nonneg (w j))).trans_eq
  dsimp [w]
  ring

end TaoTrudgianYang2025
