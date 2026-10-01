import TaoTrudgianYang2025.HuxleyLinearForms
open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped BigOperators Classical ContDiff
namespace HuxleySourceCompletionErrorScratch
private theorem cubic_completion_point_error
    {σ c N R A μ : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hN : 1 ≤ N) (hR : 0 < R)
    (hAlow : N ≤ A) (hAhigh : A ≤ 3*N)
    (hμ : c/(12*σ*N*R^2) ≤ μ) :
    Real.sqrt A*Real.log (2*A)+1/(μ*A^2) ≤
      Real.sqrt (3*N)*Real.log (6*N)+12*σ*R^2/(c*N) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hAp : 0 < A := hNp.trans_le hAlow
  have hμp : 0 < μ := (div_pos hc (by positivity)).trans_le hμ
  have hlog : Real.sqrt A*Real.log (2*A) ≤ Real.sqrt (3*N)*Real.log (6*N) := by
    apply mul_le_mul (Real.sqrt_le_sqrt hAhigh)
      (Real.log_le_log (by positivity) (by linarith only [hAhigh]))
      (Real.log_nonneg (by linarith only [hAlow,hN])) (Real.sqrt_nonneg _)
  have hden : c*N/(12*σ*R^2) ≤ μ*A^2 := by
    calc
      _ = (c/(12*σ*N*R^2))*N^2 := by field_simp
      _ ≤ _ := mul_le_mul hμ (pow_le_pow_left₀ hNp.le hAlow 2) (sq_nonneg _) hμp.le
  have hrecip := one_div_le_one_div_of_le (show 0 < c*N/(12*σ*R^2) by positivity) hden
  have he : 1/(c*N/(12*σ*R^2))=12*σ*R^2/(c*N) := by field_simp
  rw [he] at hrecip
  exact add_le_add hlog hrecip

private theorem actual_source_grid_completion_error
    (S : Finset (ℝ × ℤ)) (Y : Finset ℝ) (F : ℝ → ℝ)
    (z : ℝ × ℤ → ℝ) (A : ℝ × ℤ → ℕ)
    {σ c J η T M R s : ℝ} {N : ℕ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hN : 1 ≤ N) (hM : 2 ≤ M) (hR : 0 < R)
    (hphase : T*(N:ℝ)*R^2=M^3)
    (hy : ∀ y∈Y, y∈Icc (1:ℝ) 2)
    (hlabels : ∀ i∈S, i.1∈Y)
    (hgrid : ∀ i∈S, M ≤ s+(N:ℝ)*i.2 ∧ s+(N:ℝ)*i.2 ≤ 2*M)
    (hz : ∀ i∈S, z i∈Icc M (2*M))
    (hA : ∀ i∈S, N ≤ A i ∧ A i ≤ 3*N)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) :
    let f := fun i w => T*(F (w/M)-F (w/M+η*i.1))/(σ*η)
    let μ := fun i => iteratedDeriv 3 (f i) (round (z i))/6
    (S.card:ℝ) ≤ (Y.card:ℝ)*(M/(N:ℝ)+1) ∧
    (∑ i∈S, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) ≤
      (Y.card:ℝ)*(M/(N:ℝ)+1)*
        (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σ*R^2/(c*(N:ℝ))) := by
  classical
  intro f μ
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNreal : (1:ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨I,hI,_hIlow,hIhigh⟩ := physical_grid_interval_card (N:=(N:ℝ)) (Z:=s)
    (x:=M) (z:=2*M) hNp (by linarith only [hM])
  have hsub : S⊆Y ×ˢ I := by
    intro i hi
    refine Finset.mem_product.mpr ⟨hlabels i hi,(hI i.2).mpr ?_⟩
    simpa only [mul_comm (i.2:ℝ) (N:ℝ)] using hgrid i hi
  have hcardRaw : (S.card:ℝ) ≤ (Y.card:ℝ)*(I.card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_product Y I)
  have hcard : (S.card:ℝ) ≤ (Y.card:ℝ)*(M/(N:ℝ)+1) := by
    have hIbound : (I.card:ℝ) ≤ M/(N:ℝ)+1 := by
      convert hIhigh using 1
      ring
    exact hcardRaw.trans (mul_le_mul_of_nonneg_left hIbound (Nat.cast_nonneg _))
  refine ⟨hcard,?_⟩
  let ErrorBound := Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σ*R^2/(c*(N:ℝ))
  have hError : 0 ≤ ErrorBound := add_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by linarith only [hNreal])))
    (by positivity)
  have hpoint i (hi : i∈S) :
      Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2) ≤ ErrorBound := by
    have hcubic := positive_difference_rounded_cubic_scales F hσ hc hJ hη hηmax
      (hy i.1 (hlabels i hi)) hf hbound hnegative hM hNp hR (hz i hi) hphase
    exact cubic_completion_point_error hσ hc hNreal hR
      (by exact_mod_cast (hA i hi).1) (by exact_mod_cast (hA i hi).2) hcubic.1
  calc
    _ ≤ ∑ _i∈S,ErrorBound := Finset.sum_le_sum hpoint
    _ = (S.card:ℝ)*ErrorBound := by rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hError

example
    {σ c N R A μ : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hN : 1 ≤ N) (hR : 0 < R)
    (hAlow : N ≤ A) (hAhigh : A ≤ 3*N)
    (hμ : c/(12*σ*N*R^2) ≤ μ) :
    Real.sqrt A*Real.log (2*A)+1/(μ*A^2) ≤
      Real.sqrt (3*N)*Real.log (6*N)+12*σ*R^2/(c*N) :=
  HuxleySourceCompletionErrorScratch.cubic_completion_point_error (σ:=σ) (c:=c) (N:=N) (R:=R) (A:=A) (μ:=μ) hσ hc hN hR hAlow hAhigh hμ

example
    (S : Finset (ℝ × ℤ)) (Y : Finset ℝ) (F : ℝ → ℝ)
    (z : ℝ × ℤ → ℝ) (A : ℝ × ℤ → ℕ)
    {σ c J η T M R s : ℝ} {N : ℕ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hN : 1 ≤ N) (hM : 2 ≤ M) (hR : 0 < R)
    (hphase : T*(N:ℝ)*R^2=M^3)
    (hy : ∀ y∈Y, y∈Icc (1:ℝ) 2)
    (hlabels : ∀ i∈S, i.1∈Y)
    (hgrid : ∀ i∈S, M ≤ s+(N:ℝ)*i.2 ∧ s+(N:ℝ)*i.2 ≤ 2*M)
    (hz : ∀ i∈S, z i∈Icc M (2*M))
    (hA : ∀ i∈S, N ≤ A i ∧ A i ≤ 3*N)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) :
    let f := fun i w => T*(F (w/M)-F (w/M+η*i.1))/(σ*η)
    let μ := fun i => iteratedDeriv 3 (f i) (round (z i))/6
    (S.card:ℝ) ≤ (Y.card:ℝ)*(M/(N:ℝ)+1) ∧
    (∑ i∈S, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) ≤
      (Y.card:ℝ)*(M/(N:ℝ)+1)*
        (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σ*R^2/(c*(N:ℝ))) :=
  HuxleySourceCompletionErrorScratch.actual_source_grid_completion_error S Y F z A (σ:=σ) (c:=c) (J:=J) (η:=η) (T:=T) (M:=M) (R:=R) (s:=s) (N:=N) hσ hc hJ hη hηmax hN hM hR hphase hy hlabels hgrid hz hA hf hbound hnegative


#print axioms cubic_completion_point_error
#print axioms actual_source_grid_completion_error
end HuxleySourceCompletionErrorScratch
