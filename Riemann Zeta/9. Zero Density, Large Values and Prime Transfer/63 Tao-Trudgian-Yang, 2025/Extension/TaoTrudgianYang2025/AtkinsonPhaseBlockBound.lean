import TaoTrudgianYang2025.AtkinsonMainVariation

/-!
# Actual phase-block consumers of uniform weight variation

Each block keeps its source indices and both original signs. A finite maximum
of the literal raw phase partial sums controls the complete stationary block.
Global dyadic assembly and the Gram estimate are not assumed here.
-/

noncomputable section

open Complex

namespace TaoTrudgianYang2025

def atkinsonPhaseBlockSum (T : ℝ) (m N : ℕ) : ℂ :=
  ∑ i ∈ Finset.range N, atkinsonPositivePhaseTerm T (m+i)

def atkinsonPhaseBlockMax (T : ℝ) (m N : ℕ) : ℝ :=
  (Finset.range (N+1)).sup' (by simp) (fun j => ‖atkinsonPhaseBlockSum T m j‖)

def atkinsonStationaryBlock (T G L : ℝ) (m N : ℕ) : ℂ :=
  ∑ i ∈ Finset.range N, atkinsonStationaryLeadingTerm T G L (m+i)

theorem norm_atkinsonPhaseBlockSum_le_max (T : ℝ) (m N j : ℕ) (hj : j ≤ N) :
    ‖atkinsonPhaseBlockSum T m j‖ ≤ atkinsonPhaseBlockMax T m N := by
  unfold atkinsonPhaseBlockMax
  exact Finset.le_sup' (fun k => ‖atkinsonPhaseBlockSum T m k‖)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

theorem atkinsonPhaseBlockMax_nonneg (T : ℝ) (m N : ℕ) :
    0 ≤ atkinsonPhaseBlockMax T m N := by
  have h := norm_atkinsonPhaseBlockSum_le_max T m N 0 (Nat.zero_le N)
  simpa only [atkinsonPhaseBlockSum,Finset.sum_range_zero,norm_zero] using h

theorem norm_atkinsonNegativePhaseBlockSum (T : ℝ) (m N : ℕ) :
    ‖∑ i ∈ Finset.range N, atkinsonNegativePhaseTerm T (m+i)‖ =
      ‖atkinsonPhaseBlockSum T m N‖ := by
  simp only [atkinsonNegativePhaseTerm_eq_conj,← map_sum,Complex.norm_conj]
  rfl

theorem FiniteVariationBound.norm_sum_mul_le {w a : ℕ → ℂ} {N : ℕ} {M A : ℝ}
    (hw : FiniteVariationBound w N M) (hA : 0 ≤ A)
    (ha : ∀ j ≤ N, ‖∑ i ∈ Finset.range j, a i‖ ≤ A) :
    ‖∑ i ∈ Finset.range N, w i*a i‖ ≤ 2*M*A := by
  have hv : (∑ i ∈ Finset.range (N-1), ‖w (i+1)-w i‖) ≤ M := by
    apply le_trans _ hw.variation_le
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le N 1))
    intro i _ _
    exact norm_nonneg _
  apply (norm_sum_mul_le_discrete_parts w a N).trans
  have he := mul_le_mul (hw.norm_le (N-1) (Nat.sub_le N 1)) (ha N le_rfl)
    (norm_nonneg _) hw.nonneg
  have hs : (∑ i ∈ Finset.range (N-1),
      ‖w (i+1)-w i‖*‖∑ k ∈ Finset.range (i+1), a k‖) ≤ A*M := by
    calc
      _ ≤ ∑ i ∈ Finset.range (N-1), ‖w (i+1)-w i‖*A := by
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_left (ha (i+1) (by
          have h := Finset.mem_range.mp hi
          omega)) (norm_nonneg _)
      _ = A*(∑ i ∈ Finset.range (N-1), ‖w (i+1)-w i‖) := by
        rw [← Finset.sum_mul]
        ring
      _ ≤ A*M := mul_le_mul_of_nonneg_left hv hA
  nlinarith

theorem atkinsonStationaryBlock_eq_signed {T G : ℝ} (hT : 0 < T)
    (hG : G ≠ 0) (L : ℝ) (m N : ℕ) :
    atkinsonStationaryBlock T G L m N = atkinsonCommonMainPhase T *
      ((∑ i ∈ Finset.range N, atkinsonPositiveMainWeight T G L (m+i)*atkinsonPositivePhaseTerm T (m+i))-
        ∑ i ∈ Finset.range N, atkinsonNegativeMainWeight T G L (m+i)*atkinsonNegativePhaseTerm T (m+i)) := by
  unfold atkinsonStationaryBlock
  simp_rw [atkinsonStationaryLeadingTerm_eq_signed hT hG L]
  rw [← Finset.mul_sum,Finset.sum_sub_distrib]

theorem exists_norm_atkinsonStationaryBlock_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 0 < T → 0 < G → G^2 ≤ 2*T → 0 < L →
      ∀ m N : ℕ, 0 < m → 10000*((m+N:ℕ):ℝ) ≤ T →
      ‖atkinsonStationaryBlock T G L m N‖ ≤
        C*G*T^(-(1/4:ℝ))*(m:ℝ)^(-(1/4:ℝ))*Real.exp (-(G^2*(m:ℝ))/(12*T))*
          atkinsonPhaseBlockMax T m N := by
  obtain ⟨C,hC,hvar⟩ := exists_finiteVariationBound_atkinsonMainWeights
  refine ⟨8*C,by positivity,?_⟩
  intro T G L hT hG hGT hL m N hm hN
  obtain ⟨hp,hn⟩ := hvar T G L hT hG hGT hL m N hm hN
  have hmax := atkinsonPhaseBlockMax_nonneg T m N
  have hpb := hp.norm_sum_mul_le hmax (fun j hj => norm_atkinsonPhaseBlockSum_le_max T m N j hj)
  have hnb := hn.norm_sum_mul_le hmax (fun j hj => by
    rw [norm_atkinsonNegativePhaseBlockSum]
    exact norm_atkinsonPhaseBlockSum_le_max T m N j hj)
  rw [atkinsonStationaryBlock_eq_signed hT hG.ne',norm_mul]
  apply (mul_le_mul (norm_atkinsonCommonMainPhase_le T) (norm_sub_le _ _)
    (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)).trans
  nlinarith

theorem exists_atkinsonSourceCutoff_block_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) →
      ∀ m N : ℕ, 0 < m → m+N ≤ atkinsonSourceCutoff T G (Real.log T) →
      ‖atkinsonStationaryBlock T G (Real.log T) m N‖ ≤
        C*G*T^(-(1/4:ℝ))*(m:ℝ)^(-(1/4:ℝ))*Real.exp (-(G^2*(m:ℝ))/(12*T))*
          atkinsonPhaseBlockMax T m N := by
  obtain ⟨C,hC,hblock⟩ := exists_norm_atkinsonStationaryBlock_le
  obtain ⟨B,hB⟩ := Filter.eventually_atTop.mp (eventually_atkinsonSourceCutoff_small hδ)
  refine ⟨C,hC,max 40000 B,le_max_left _ _,?_⟩
  intro T G hT hlower hupper m N hm hcut
  have hTlarge : 40000 ≤ T := (le_max_left _ _).trans hT
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hG : 0 < G := (Real.rpow_pos_of_pos hT0 δ).trans_le hlower
  have hGhi : G ≤ Real.sqrt T := by
    rw [Real.sqrt_eq_rpow]
    exact hupper.trans (Real.rpow_le_rpow_of_exponent_le hT1 (by linarith))
  have hGT : G^2 ≤ 2*T := by
    have h := pow_le_pow_left₀ hG.le hGhi 2
    rw [Real.sq_sqrt hT0.le] at h
    linarith
  have hsmall := hB T ((le_max_right _ _).trans hT) G hlower
  have hcutR : ((m+N:ℕ):ℝ) ≤ atkinsonSourceCutoff T G (Real.log T) := by exact_mod_cast hcut
  exact hblock T G (Real.log T) hT0 hG hGT (Real.log_pos (by linarith)) m N hm (by linarith)

end TaoTrudgianYang2025
