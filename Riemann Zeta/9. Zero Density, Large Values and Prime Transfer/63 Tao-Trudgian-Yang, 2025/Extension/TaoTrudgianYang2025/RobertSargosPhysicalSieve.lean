import TaoTrudgianYang2025.RobertSargosPolynomialSieve
import TaoTrudgianYang2025.ExponentPairEpsilonBudget
import TaoTrudgianYang2025.RobertSargosPhysicalInitialReduction

/-! Source-connected physical sieve assembly and explicit scale budgets.
The global differencing scale is separate from the selected symmetric block. -/

noncomputable section
open GafniTao Set
open scoped BigOperators ContDiff
namespace TaoTrudgianYang2025

theorem robertSargos_physical_shift_half_height (H : ℕ) {lam : ℝ}
    (hlam : 0 < lam) (hsmall : lam ≤ 1/8192)
    (hHmin : lam^(-(1:ℝ)/7) ≤ H) :
    (⌊lam^(-(1:ℝ)/13)⌋₊:ℝ) ≤ (H:ℝ)/2 := by
  let T := lam^(-(1:ℝ)/13)
  let R := ⌊T⌋₊
  have hT : 2 ≤ T := (thirteenth_root_physical_scale hlam hsmall).1
  have hR : 2 ≤ R := Nat.le_floor hT
  have hRcast : (2:ℝ) ≤ R := by exact_mod_cast hR
  have hRhi : (R:ℝ) ≤ T := Nat.floor_le (by linarith)
  have hT13 : T^13 = lam⁻¹ := by
    dsimp only [T]
    rw [thirteenth_root_nat_pow hlam]
    norm_num [Real.rpow_neg_one]
  have hHpow := pow_le_pow_left₀ (Real.rpow_nonneg hlam.le (-(1:ℝ)/7)) hHmin 7
  have he : (lam^(-(1:ℝ)/7))^7 = lam⁻¹ := by
    rw [← Real.rpow_mul_natCast hlam.le]
    norm_num [Real.rpow_neg_one]
  rw [he,← hT13] at hHpow
  have hRHpow : (R:ℝ)^13 ≤ (H:ℝ)^7 :=
    (pow_le_pow_left₀ (Nat.cast_nonneg R) hRhi 13).trans hHpow
  by_contra hnot
  have hnot' : (H:ℝ) < 2*(R:ℝ) := by change ¬ (R:ℝ) ≤ (H:ℝ)/2 at hnot; linarith
  have hnat : H < 2*R := by exact_mod_cast hnot'
  have hHle : (H:ℝ) ≤ 2*(R:ℝ)-1 := by
    have h : H+1 ≤ 2*R := by omega
    have h' : (H:ℝ)+1 ≤ 2*(R:ℝ) := by exact_mod_cast h
    linarith
  have hH7 := pow_le_pow_left₀ (Nat.cast_nonneg H) hHle 7
  let u := (R:ℝ)-2
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hpoly : 0 < (u+2)^13-(2*(u+2)-1)^7 := by
    ring_nf
    positivity
  have huR : u+2 = (R:ℝ) := by dsimp [u]; ring
  rw [huR] at hpoly
  linarith

/-- The complete source symmetric sum now has a numerical sieve bound.
All sieve, sample-spacing, arithmetic-count and prefix inputs are derived. -/
theorem exists_robertSargos_physical_sieve_reduction (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : ℝ → ℝ) (M H : ℕ) (C lam : ℝ),
    1 ≤ C → 0 < lam → lam ≤ 1/8192 →
    lam^(-(8:ℝ)/13) ≤ M → lam^(-(1:ℝ)/7) ≤ H →
    (H:ℝ) ≤ lam^(-(2:ℝ)/13)/2 →
    (∀ t ∈ Icc (1:ℝ) M, ContDiffAt ℝ 4 f t) →
    (∀ t ∈ Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f t) →
    (∀ t ∈ Icc (1:ℝ) M, iteratedDeriv 4 f t ≤ C*lam) →
    let Q := ⌊lam^(-(3:ℝ)/13)⌋₊
    let R := ⌊lam^(-(1:ℝ)/13)⌋₊
    let A := lam^(-(2:ℝ)/13)
    ‖robertSargosSymmetricSum f M H‖^2 ≤
      3140*C*(1+2*Real.pi*C)*(M:ℝ)^2+
        (256*(1+648*Real.pi*C)^3*(M:ℝ)*H/((Q:ℝ)*R*Q))*
        Real.sqrt (K*C*M*(1+Real.log M)*(Nat.clog 2 Q:ℝ)^2*
          (((Finset.Ioo (-(R:ℤ)) R).erase 0).card:ℝ)*
          (1+3*A*Q)*(1+(C*lam*M)*(13*A*(Q:ℝ)^2))*
          ((R:ℝ)*Q*H*Q)^(1+ε)*
          (1+(1/(C*lam*M)+12*R*(H:ℝ)^2)/((H:ℝ)*Q))) := by
  classical
  obtain ⟨K,hK,hcount⟩ := exists_robertSargos_counted_polynomial_sieve ε hε
  refine ⟨32*K,by positivity,?_⟩
  intro f M H C lam hC hlam hsmall hM hHmin hHmax hf hlo hhi
  dsimp only
  let Q := ⌊lam^(-(3:ℝ)/13)⌋₊
  let R := ⌊lam^(-(1:ℝ)/13)⌋₊
  let A := lam^(-(2:ℝ)/13)
  let T := lam^(-(1:ℝ)/13)
  have hT : 2 ≤ T := (thirteenth_root_physical_scale hlam hsmall).1
  have hT1 : 1 ≤ T := by linarith
  have h2 : T^2 = A := by
    simpa only [Nat.cast_ofNat] using thirteenth_root_nat_pow hlam 2
  have h3 : T^3 = lam^(-(3:ℝ)/13) := by
    simpa only [Nat.cast_ofNat] using thirteenth_root_nat_pow hlam 3
  have h8 : T^8 = lam^(-(8:ℝ)/13) := by
    simpa only [Nat.cast_ofNat] using thirteenth_root_nat_pow hlam 8
  have hQlo : T^3/2 ≤ (Q:ℝ) := by
    have h := (positive_floor_half_bounds
      (show 1 ≤ T^3 by exact one_le_pow₀ hT1)).2.1
    simpa only [h3,Q] using h
  have hA : 0 < A := Real.rpow_pos_of_pos hlam _
  have hAQ : A ≤ Q := by
    rw [← h2]
    nlinarith [mul_le_mul_of_nonneg_right hT (sq_nonneg T)]
  have hRA : (R:ℝ) ≤ A := by
    have hr : (R:ℝ) ≤ T := Nat.floor_le (Real.rpow_nonneg hlam.le _)
    rw [← h2]
    nlinarith
  have hHA : (H:ℝ) ≤ A := by change (H:ℝ) ≤ A/2 at hHmax; linarith
  obtain ⟨hH0,hQ0,hR0,_,_⟩ :=
    robertSargos_physical_a_times_a_ranges M H hlam hsmall hM hHmin hHmax
  have hRH := robertSargos_physical_shift_half_height H hlam hsmall hHmin
  have hM1 : 1 ≤ M := by
    have h := (one_le_pow₀ hT1 : 1 ≤ T^8)
    rw [h8] at h
    exact_mod_cast h.trans hM
  have hCpos : 0 < C := by linarith
  obtain ⟨positive,X,Y,N,hprefix,hbase⟩ :=
    robertSargos_physical_polynomial_reduction f M H hC hlam hsmall hM hHmin hHmax hf hlo hhi
  have hb := hcount f M R H Q positive X Y N A C lam
    hM1 hR0 hH0 hQ0 hA hCpos hlam hAQ hHA hRA hRH
    (fun r => (hprefix r).1) (fun r => (hprefix r).2.1) (fun r => (hprefix r).2.2)
    hf hlo hhi
  have hs := robertSargos_physical_sample_spacing f M hC hlam hsmall hM hf hlo hhi
  have hnonneg : 0 ≤
      K*(Nat.clog 2 Q:ℝ)^2*(((Finset.Ioo (-(R:ℤ)) R).erase 0).card:ℝ)*
        (1+3*A*Q)*(1+(C*lam*M)*(13*A*(Q:ℝ)^2))*
        ((R:ℝ)*Q*H*Q)^(1+ε)*
        (1+(1/(C*lam*M)+12*R*(H:ℝ)^2)/((H:ℝ)*Q)) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hs hnonneg
  have hbound :
      (∑ r ∈ (Finset.Ioo (-(R:ℤ)) R).erase 0, ∑ m ∈ Finset.Icc (1:ℤ) M,
        ‖robertSargosSignedPolynomialPrefix f H Q r m (positive r) (X r) (Y r) (N r)‖)^2 ≤
      (32*K)*C*M*(1+Real.log M)*(Nat.clog 2 Q:ℝ)^2*
        (((Finset.Ioo (-(R:ℤ)) R).erase 0).card:ℝ)*
        (1+3*A*Q)*(1+(C*lam*M)*(13*A*(Q:ℝ)^2))*
        ((R:ℝ)*Q*H*Q)^(1+ε)*
        (1+(1/(C*lam*M)+12*R*(H:ℝ)^2)/((H:ℝ)*Q)) := by
    apply hb.trans
    convert hmul using 1 <;> dsimp only [Q,A] <;> ring
  have hcommon : robertSargosCommonMInterval M H Q Q ⊆ Finset.Icc (1:ℤ) M := by
    intro m hm
    simp only [robertSargosCommonMInterval,Finset.mem_Icc] at hm
    apply Finset.mem_Icc.mpr
    omega
  have hsum :
      (∑ r ∈ (Finset.Ioo (-(R:ℤ)) R).erase 0,
        ∑ m ∈ robertSargosCommonMInterval M H Q Q,
          ‖robertSargosSignedPolynomialPrefix f H Q r m (positive r) (X r) (Y r) (N r)‖) ≤
      ∑ r ∈ (Finset.Ioo (-(R:ℤ)) R).erase 0, ∑ m ∈ Finset.Icc (1:ℤ) M,
        ‖robertSargosSignedPolynomialPrefix f H Q r m (positive r) (X r) (Y r) (N r)‖ := by
    exact Finset.sum_le_sum (fun r _ => Finset.sum_le_sum_of_subset_of_nonneg
      hcommon (fun m _ _ => norm_nonneg _))
  have hroot := hsum.trans (Real.le_sqrt_of_sq_le hbound)
  exact hbase.trans (add_le_add_right (mul_le_mul_of_nonneg_left hroot
    (show 0 ≤ 256*(1+648*Real.pi*C)^3*(M:ℝ)*H/((Q:ℝ)*R*Q) by positivity)) _)



theorem robertSargos_taylor_factor_budget {T lam M C R H Q ε : ℝ}
    (hT : 1 ≤ T) (hlam : 0 < lam) (hnorm : T^13*lam = 1)
    (hM : T^8 ≤ M) (hC : 1 ≤ C) (hR : 0 < R) (hRhi : R ≤ T)
    (hH : 0 < H) (hHhi : H ≤ T^2) (hQ : 0 < Q) (hQhi : Q ≤ T^3)
    (hε : 0 ≤ ε) :
    (R*Q*H*Q)^(1+ε)*(1+(1/(C*lam*M)+12*R*H^2)/(H*Q)) ≤
      14*(T^9)^ε*T^9 := by
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hMp : 0 < M := (by positivity : 0 < T^8).trans_le hM
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hbase : R*Q*H*Q ≤ T^9 := by
    calc
      _ ≤ T*T^3*T^2*T^3 := by gcongr
      _ = _ := by ring
  have hE : 1/(C*lam*M) ≤ T^5 := by
    have hCM : T^8 ≤ C*M := by
      have h := mul_le_mul_of_nonneg_right hC hMp.le
      linarith
    have h := mul_le_mul_of_nonneg_left hCM (show 0 ≤ T^5*lam by positivity)
    apply (div_le_iff₀ (by positivity : 0 < C*lam*M)).mpr
    nlinarith only [h,hnorm]
  have hsecond : R*Q*(1/(C*lam*M)) ≤ T^9 := by
    calc
      _ ≤ T*T^3*T^5 := by gcongr
      _ = _ := by ring
  have hthird : 12*R^2*Q*H^2 ≤ 12*T^9 := by
    calc
      _ ≤ 12*T^2*T^3*(T^2)^2 := by gcongr
      _ = _ := by ring
  have hexpand :
      (R*Q*H*Q)^(1+ε)*(1+(1/(C*lam*M)+12*R*H^2)/(H*Q)) =
      (R*Q*H*Q)^ε*(R*Q*H*Q+R*Q*(1/(C*lam*M))+12*R^2*Q*H^2) := by
    rw [add_comm 1 ε,Real.rpow_add_one (by positivity : R*Q*H*Q ≠ 0)]
    field_simp; ring
  rw [hexpand]
  calc
    _ ≤ (T^9)^ε*(14*T^9) := by
      apply mul_le_mul
      · exact Real.rpow_le_rpow (by positivity) hbase hε
      · linarith
      · positivity
      · positivity
    _ = _ := by ring

theorem robertSargos_frequency_factor_budget {T lam M C Q : ℝ}
    (hT : 1 ≤ T) (hlam : 0 < lam) (hnorm : T^13*lam = 1)
    (hM : T^8 ≤ M) (hC : 1 ≤ C) (hQ : 0 ≤ Q) (hQhi : Q ≤ T^3) :
    (1+3*T^2*Q)*(1+(C*lam*M)*(13*T^2*Q^2)) ≤ 56*C*M := by
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hMp : 0 < M := (by positivity : 0 < T^8).trans_le hM
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hCM : T^8 ≤ C*M := by
    have h := mul_le_mul_of_nonneg_right hC hMp.le
    linarith
  have hn16 : T^16*lam = T^3 := by
    calc
      _ = T^3*(T^13*lam) := by ring
      _ = _ := by rw [hnorm,mul_one]
  have hunit : 1 ≤ C*lam*M*T^8 := by
    have h := mul_le_mul_of_nonneg_left hCM (show 0 ≤ lam*T^8 by positivity)
    have h3 : 1 ≤ T^3 := one_le_pow₀ hT
    nlinarith only [h,hn16,h3]
  have hfirst : 1+3*T^2*Q ≤ 4*T^5 := by
    have h := mul_le_mul_of_nonneg_left hQhi (show 0 ≤ 3*T^2 by positivity)
    have h5 : 1 ≤ T^5 := one_le_pow₀ hT
    nlinarith only [h,h5]
  have hsecond : 1+(C*lam*M)*(13*T^2*Q^2) ≤ 14*C*lam*M*T^8 := by
    have hq2 := pow_le_pow_left₀ hQ hQhi 2
    have h := mul_le_mul_of_nonneg_left hq2 (show 0 ≤ 13*C*lam*M*T^2 by positivity)
    nlinarith only [h,hunit]
  have hprod := mul_le_mul hfirst hsecond (by positivity) (by positivity)
  have he : (4*T^5)*(14*C*lam*M*T^8) = 56*C*M := by
    calc
      _ = 56*C*M*(T^13*lam) := by ring
      _ = _ := by rw [hnorm,mul_one]
  rwa [he] at hprod


theorem robertSargos_sieve_coefficient_budget {T M H Q R : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M) (hHhi : H ≤ T^2/2)
    (hQlo : T^3/2 ≤ Q) (hRlo : T/2 ≤ R) :
    M*H/(Q*R*Q) ≤ 4*M/T^5 := by
  have hQ : 0 < Q := (by positivity : 0 < T^3/2).trans_le hQlo
  have hR : 0 < R := (by positivity : 0 < T/2).trans_le hRlo
  have hd : T^7/8 ≤ Q*R*Q := by
    calc
      _ = (T^3/2)*(T/2)*(T^3/2) := by ring
      _ ≤ _ := by gcongr
  calc
    _ ≤ M*(T^2/2)/(T^7/8) := by gcongr
    _ = _ := by field_simp; ring

theorem robertSargos_root_power_budget {T M ε : ℝ}
    (hT : 1 ≤ T) (hM : T^8 ≤ M) (hε : 0 ≤ ε) :
    (T^9)^ε ≤ (M^ε)^2 := by
  have hMp : 0 < M := (by positivity : 0 < T^8).trans_le hM
  have hp : T^9 ≤ M^2 := by
    have h₁ : T^9 ≤ T^16 := pow_le_pow_right₀ hT (by norm_num)
    have h₂ := pow_le_pow_left₀ (show 0 ≤ T^8 by positivity) hM 2
    nlinarith only [h₁,h₂]
  have h := Real.rpow_le_rpow (by positivity : 0 ≤ T^9) hp hε
  have he : (M^2)^ε = (M^ε)^2 := by
    rw [← Real.rpow_natCast M 2,← Real.rpow_mul hMp.le]
    norm_num only [Nat.cast_ofNat]
    rw [mul_comm (2:ℝ) ε,Real.rpow_mul hMp.le]
    norm_num only [Real.rpow_two]
  rwa [he] at h


theorem robertSargos_sieve_radicand_budget {T lam M C R H Q K J L W ε : ℝ}
    (hT : 1 ≤ T) (hlam : 0 < lam) (hnorm : T^13*lam = 1)
    (hM : T^8 ≤ M) (hC : 1 ≤ C) (hR : 0 < R) (hRhi : R ≤ T)
    (hH : 0 < H) (hHhi : H ≤ T^2) (hQ : 0 < Q) (hQhi : Q ≤ T^3)
    (hK : 0 ≤ K) (hL : 1 ≤ L) (hW : 0 ≤ W) (hWhi : W ≤ 2*T)
    (hε : 0 ≤ ε) :
    K*C*M*L*J^2*W*(1+3*T^2*Q)*(1+(C*lam*M)*(13*T^2*Q^2))*
      (R*Q*H*Q)^(1+ε)*(1+(1/(C*lam*M)+12*R*H^2)/(H*Q)) ≤
      (Real.sqrt (1568*K)*C*M*L*J*T^5*M^ε)^2 := by
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hMp : 0 < M := (by positivity : 0 < T^8).trans_le hM
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hLL : L ≤ L^2 := by nlinarith
  have hf := robertSargos_frequency_factor_budget hT hlam hnorm hM hC hQ.le hQhi
  have ht := robertSargos_taylor_factor_budget hT hlam hnorm hM hC hR hRhi
    hH hHhi hQ hQhi hε
  have hp := robertSargos_root_power_budget hT hM hε
  have hP : (K*C*M*L*J^2)*W ≤ (K*C*M*L^2*J^2)*(2*T) := by gcongr
  have hPF := mul_le_mul hP hf (by positivity) (by positivity)
  have hCT : (R*Q*H*Q)^(1+ε)*(1+(1/(C*lam*M)+12*R*H^2)/(H*Q)) ≤
      14*(M^ε)^2*T^9 := ht.trans (by gcongr)
  calc
    _ = (K*C*M*L*J^2)*W*((1+3*T^2*Q)*(1+(C*lam*M)*(13*T^2*Q^2)))*
        ((R*Q*H*Q)^(1+ε)*(1+(1/(C*lam*M)+12*R*H^2)/(H*Q))) := by ring
    _ ≤ (K*C*M*L^2*J^2)*(2*T)*(56*C*M)*(14*(M^ε)^2*T^9) := by
      exact mul_le_mul hPF hCT (by positivity) (by positivity)
    _ = _ := by
      simp only [mul_pow,Real.sq_sqrt (show 0 ≤ 1568*K by positivity)]
      ring

theorem exists_robertSargos_large_block_log_bound (ε : ℝ) (hε : 0 < ε)
    (C : ℝ) (hC : 1 ≤ C) :
    ∃ D : ℝ, 0 < D ∧ ∀ (f : ℝ → ℝ) (M H : ℕ) (lam : ℝ),
    0 < lam → lam ≤ 1/8192 → lam^(-(8:ℝ)/13) ≤ M →
    lam^(-(1:ℝ)/7) ≤ H → (H:ℝ) ≤ lam^(-(2:ℝ)/13)/2 →
    (∀ t ∈ Icc (1:ℝ) M, ContDiffAt ℝ 4 f t) →
    (∀ t ∈ Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f t) →
    (∀ t ∈ Icc (1:ℝ) M, iteratedDeriv 4 f t ≤ C*lam) →
    ‖robertSargosSymmetricSum f M H‖^2 ≤
      D*(M:ℝ)^2*(1+Real.log M)^2*(M:ℝ)^ε := by
  classical
  obtain ⟨K,hK,hsrc⟩ := exists_robertSargos_physical_sieve_reduction ε hε
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let D₀ := 3140*C*(1+2*Real.pi*C)
  let D₁ := 1024*(1+648*Real.pi*C)^3*Real.sqrt (1568*K)*C*(2/Real.log 2)
  refine ⟨D₀+D₁,by dsimp [D₀,D₁]; positivity,?_⟩
  intro f M H lam hlam hsmall hM hHmin hHmax hf hlo hhi
  let T := lam^(-(1:ℝ)/13)
  let Q := ⌊lam^(-(3:ℝ)/13)⌋₊
  let R := ⌊lam^(-(1:ℝ)/13)⌋₊
  let J : ℝ := Nat.clog 2 Q
  let L : ℝ := 1+Real.log M
  let W : ℝ := ((Finset.Ioo (-(R:ℤ)) R).erase 0).card
  have hT : 2 ≤ T := (thirteenth_root_physical_scale hlam hsmall).1
  have hT1 : 1 ≤ T := by linarith
  have hTp : 0 < T := by linarith
  have hn : T^13*lam = 1 := (thirteenth_root_physical_scale hlam hsmall).2
  have h2 : T^2 = lam^(-(2:ℝ)/13) := by
    simpa only [Nat.cast_ofNat] using thirteenth_root_nat_pow hlam 2
  have h3 : T^3 = lam^(-(3:ℝ)/13) := by
    simpa only [Nat.cast_ofNat] using thirteenth_root_nat_pow hlam 3
  have h8 : T^8 = lam^(-(8:ℝ)/13) := by
    simpa only [Nat.cast_ofNat] using thirteenth_root_nat_pow hlam 8
  have hM' : T^8 ≤ M := by rwa [h8]
  have hM1 : (1:ℝ) ≤ M := (one_le_pow₀ hT1).trans hM'
  have hMp : (0:ℝ) < M := zero_lt_one.trans_le hM1
  have hL : 1 ≤ L := by
    have h := Real.log_nonneg hM1
    dsimp only [L]
    linarith
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hJ0 : 0 ≤ J := Nat.cast_nonneg _
  have hW0 : 0 ≤ W := Nat.cast_nonneg _
  have hQfloor := positive_floor_half_bounds (one_le_pow₀ hT1 : 1 ≤ T^3)
  have hQlo : T^3/2 ≤ (Q:ℝ) := by simpa only [h3,Q] using hQfloor.2.1
  have hQhi : (Q:ℝ) ≤ T^3 := by simpa only [h3,Q] using hQfloor.2.2
  have hRfloor := positive_floor_half_bounds hT1
  have hRlo : T/2 ≤ (R:ℝ) := hRfloor.2.1
  have hRhi : (R:ℝ) ≤ T := hRfloor.2.2
  obtain ⟨hH0,hQ0,hR0,hQM,_⟩ :=
    robertSargos_physical_a_times_a_ranges M H hlam hsmall hM hHmin hHmax
  have hHp : (0:ℝ) < H := by exact_mod_cast hH0
  have hQp : (0:ℝ) < Q := by dsimp only [Q]; exact_mod_cast hQ0
  have hRp : (0:ℝ) < R := by dsimp only [R]; exact_mod_cast hR0
  have hHhalf : (H:ℝ) ≤ T^2/2 := by rwa [h2]
  have hHhi : (H:ℝ) ≤ T^2 := by linarith [sq_nonneg T]
  have hWhi : W ≤ 2*T := by
    have hc : ((Finset.Ioo (-(R:ℤ)) R).erase 0).card ≤ 2*R := by
      apply (Finset.card_le_card (Finset.erase_subset _ _)).trans
      rw [Int.card_Ioo]
      omega
    have hc' : W ≤ 2*(R:ℝ) := by dsimp only [W]; exact_mod_cast hc
    linarith
  have hQ2 : 2 ≤ Q := by
    have hpow := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hT 3
    have h : (2:ℝ) ≤ Q := by nlinarith only [hpow,hQlo]
    exact_mod_cast h
  have hJ : J ≤ (2/Real.log 2)*L := by
    have hqm : (Q:ℝ) ≤ M := by dsimp only [Q]; exact_mod_cast hQM
    have hlog := Real.log_le_log hQp hqm
    calc
      J ≤ 2*(Real.log Q/Real.log 2) := nat_clog_two_le_twice_log Q hQ2
      _ ≤ 2*(Real.log M/Real.log 2) := by gcongr
      _ ≤ 2*((1+Real.log M)/Real.log 2) := by gcongr; linarith
      _ = _ := by dsimp only [L]; ring
  have hrad := robertSargos_sieve_radicand_budget
    (K := K) (J := J) (L := L) (W := W) hT1 hlam hn hM' hC hRp hRhi
    hHp hHhi hQp hQhi hK.le hL hW0 hWhi hε.le
  rw [h2] at hrad
  have hroot := Real.sqrt_le_sqrt hrad
  rw [Real.sqrt_sq (show 0 ≤ Real.sqrt (1568*K)*C*(M:ℝ)*L*J*T^5*(M:ℝ)^ε
    by positivity)] at hroot
  have hcb := robertSargos_sieve_coefficient_budget hTp hMp.le hHhalf hQlo hRlo
  have hcoef :
      256*(1+648*Real.pi*C)^3*(M:ℝ)*H/((Q:ℝ)*R*Q) ≤
      1024*(1+648*Real.pi*C)^3*(M:ℝ)/T^5 := by
    have h := mul_le_mul_of_nonneg_left hcb
      (show 0 ≤ 256*(1+648*Real.pi*C)^3 by positivity)
    convert h using 1 <;> ring
  have hm := mul_le_mul hcoef hroot (Real.sqrt_nonneg _) (by positivity)
  have he :
      (1024*(1+648*Real.pi*C)^3*(M:ℝ)/T^5)*
        (Real.sqrt (1568*K)*C*M*L*J*T^5*(M:ℝ)^ε) =
      1024*(1+648*Real.pi*C)^3*Real.sqrt (1568*K)*C*(M:ℝ)^2*L*J*(M:ℝ)^ε := by
    field_simp
  rw [he] at hm
  have hjmul := mul_le_mul_of_nonneg_left hJ (show 0 ≤
      1024*(1+648*Real.pi*C)^3*Real.sqrt (1568*K)*C*(M:ℝ)^2*L*(M:ℝ)^ε by positivity)
  have hmain := hm.trans (show
      1024*(1+648*Real.pi*C)^3*Real.sqrt (1568*K)*C*(M:ℝ)^2*L*J*(M:ℝ)^ε ≤
      D₁*(M:ℝ)^2*L^2*(M:ℝ)^ε by
    dsimp only [D₁]
    convert hjmul using 1 <;> ring)
  have hpow : 1 ≤ (M:ℝ)^ε := Real.one_le_rpow hM1 hε.le
  have hLsq : 1 ≤ L^2 := one_le_pow₀ hL
  have herror : D₀*(M:ℝ)^2 ≤ D₀*(M:ℝ)^2*L^2*(M:ℝ)^ε := by
    have h₁ := le_mul_of_one_le_right (show 0 ≤ D₀*(M:ℝ)^2 by dsimp [D₀]; positivity) hLsq
    have h₂ := le_mul_of_one_le_right
      (show 0 ≤ D₀*(M:ℝ)^2*L^2 by dsimp [D₀]; positivity) hpow
    exact h₁.trans h₂
  have hs := hsrc f M H C lam hC hlam hsmall hM hHmin hHmax hf hlo hhi
  have htotal := hs.trans (add_le_add herror hmain)
  change _ ≤ (D₀+D₁)*(M:ℝ)^2*L^2*(M:ℝ)^ε
  convert htotal using 1; ring

theorem exists_robertSargos_large_block_bound (ε : ℝ) (hε : 0 < ε)
    (C : ℝ) (hC : 1 ≤ C) :
    ∃ D : ℝ, 0 < D ∧ ∀ (f : ℝ → ℝ) (M H : ℕ) (lam : ℝ),
    0 < lam → lam ≤ 1/8192 → lam^(-(8:ℝ)/13) ≤ M →
    lam^(-(1:ℝ)/7) ≤ H → (H:ℝ) ≤ lam^(-(2:ℝ)/13)/2 →
    (∀ t ∈ Icc (1:ℝ) M, ContDiffAt ℝ 4 f t) →
    (∀ t ∈ Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f t) →
    (∀ t ∈ Icc (1:ℝ) M, iteratedDeriv 4 f t ≤ C*lam) →
    ‖robertSargosSymmetricSum f M H‖ ≤ D*(M:ℝ)^(1+ε) := by
  obtain ⟨D,hD,hblock⟩ := exists_robertSargos_large_block_log_bound ε hε C hC
  refine ⟨Real.sqrt D*(1+2/ε),by positivity,?_⟩
  intro f M H lam hlam hsmall hM hHmin hHmax hf hlo hhi
  have hM1 : (1:ℝ) ≤ M :=
    (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hlam
      (by linarith : lam ≤ 1) (by norm_num : -(8:ℝ)/13 ≤ 0)).trans hM
  have hMp : (0:ℝ) < M := zero_lt_one.trans_le hM1
  have hL : 0 ≤ 1+Real.log (M:ℝ) := by
    have h := Real.log_nonneg hM1
    linarith
  have hlog : 1+Real.log (M:ℝ) ≤ (1+2/ε)*(M:ℝ)^(ε/2) := by
    convert one_add_log_le_rpow_budget hM1 (show 0 < ε/2 by positivity) using 1; ring
  have hb := hblock f M H lam hlam hsmall hM hHmin hHmax hf hlo hhi
  have hp := pow_le_pow_left₀ hL hlog 2
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (show 0 ≤ D*(M:ℝ)^2 by positivity))
    (show 0 ≤ (M:ℝ)^ε by positivity)
  have hehalf : ((M:ℝ)^(ε/2))^2 = (M:ℝ)^ε := by
    rw [← Real.rpow_mul_natCast hMp.le]
    congr 1
    norm_num
  have he :
      D*(M:ℝ)^2*((1+2/ε)*(M:ℝ)^(ε/2))^2*(M:ℝ)^ε =
      (Real.sqrt D*(1+2/ε)*(M:ℝ)^(1+ε))^2 := by
    simp only [mul_pow,hehalf,Real.rpow_add hMp,Real.rpow_one,Real.sq_sqrt hD.le]
    ring
  have hs := hb.trans hmul
  rw [he] at hs
  have hn := norm_nonneg (robertSargosSymmetricSum f M H)
  have ht : 0 ≤ Real.sqrt D*(1+2/ε)*(M:ℝ)^(1+ε) := by positivity
  nlinarith only [hs,hn,ht]

theorem exists_robertSargos_fourth_derivative_long_range_small (ε : ℝ) (hε : 0 < ε)
    (C : ℝ) (hC : 1 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : ℝ → ℝ) (M : ℕ) (lam : ℝ),
    0 < lam → lam ≤ 1/8192 → lam^(-(8:ℝ)/13) ≤ M →
    (∀ t ∈ Icc (1:ℝ) M, ContDiffAt ℝ 4 f t) →
    (∀ t ∈ Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f t) →
    (∀ t ∈ Icc (1:ℝ) M, iteratedDeriv 4 f t ≤ C*lam) →
    ‖∑ m ∈ Finset.Icc (1:ℤ) M, fordAdditiveCharacter (f m)‖ ≤
      K*(M:ℝ)^(1+ε)*lam^((1:ℝ)/13) := by
  obtain ⟨D,hD,hblock⟩ := exists_robertSargos_large_block_bound ε hε C hC
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let B := 1860*C+30*(1+D)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨Real.sqrt (B*(1+1/ε)/Real.log 2),by positivity,?_⟩
  intro f M lam hlam hsmall hM hf hlo hhi
  have hM1 : (1:ℝ) ≤ M :=
    (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hlam
      (by linarith : lam ≤ 1) (by norm_num : -(8:ℝ)/13 ≤ 0)).trans hM
  have hMp : (0:ℝ) < M := zero_lt_one.trans_le hM1
  have hpow : 1 ≤ (M:ℝ)^ε := Real.one_le_rpow hM1 hε.le
  have hlogM : 0 ≤ Real.log (M:ℝ) := Real.log_nonneg hM1
  let S := ∑ m ∈ Finset.Icc (1:ℤ) M, fordAdditiveCharacter (f m)
  have hcoarse : ‖S‖^2 ≤ B*(Real.log M/Real.log 2)*(M:ℝ)^2*lam^((2:ℝ)/13)*(M:ℝ)^ε := by
    rcases robertSargos_physical_initial_reduction f M hC hlam hsmall hM hf hlo hhi
      with hs | ⟨k,hk,_,hkmin,hkmax,hs⟩
    · have h₁ : 1860*C ≤ B := by dsimp [B]; linarith
      have h₂ := mul_le_mul_of_nonneg_right h₁ (show 0 ≤
        (Real.log M/Real.log 2)*(M:ℝ)^2*lam^((2:ℝ)/13) by positivity)
      have h₃ := le_mul_of_one_le_right (show 0 ≤
        B*(Real.log M/Real.log 2)*(M:ℝ)^2*lam^((2:ℝ)/13) by positivity) hpow
      apply hs.trans
      apply (show 1860*C*(Real.log M/Real.log 2)*(M:ℝ)^2*lam^((2:ℝ)/13) ≤
        B*(Real.log M/Real.log 2)*(M:ℝ)^2*lam^((2:ℝ)/13) by
          convert h₂ using 1 <;> ring).trans h₃
    · let H := ⌊lam^(-(2:ℝ)/13)⌋₊
      obtain ⟨hH,_,_,_⟩ := robertSargos_physical_floor_shift M hlam hsmall hM
      have hHp : (0:ℝ) < H := by dsimp only [H]; exact_mod_cast (show
        0 < ⌊lam^(-(2:ℝ)/13)⌋₊ by omega)
      have hlogH : 0 ≤ Real.log (H:ℝ) := Real.log_nonneg (by
        dsimp only [H]
        exact_mod_cast (show 1 ≤ ⌊lam^(-(2:ℝ)/13)⌋₊ by omega))
      have hb := hblock f M k lam hlam hsmall hM hkmin.le hkmax hf hlo hhi
      have hterm := mul_le_mul_of_nonneg_left hb (show 0 ≤ (M:ℝ)/H by positivity)
      have hmain : (M:ℝ)^2/H+((M:ℝ)/H)*‖robertSargosSymmetricSum f M k‖ ≤
          (1+D)*((M:ℝ)^2/H)*(M:ℝ)^ε := by
        have hfirst := le_mul_of_one_le_right (show 0 ≤ (M:ℝ)^2/H by positivity) hpow
        rw [Real.rpow_add hMp,Real.rpow_one] at hterm
        simp only [div_eq_mul_inv] at hterm hfirst ⊢
        nlinarith only [hterm,hfirst]
      have hscaled := mul_le_mul_of_nonneg_left hmain
        (show 0 ≤ 15*(Real.log H/Real.log 2) by positivity)
      have hfloor := robertSargos_initial_floor_budget M
        (C := (1+D)/62) (by positivity) hlam hsmall hM
      have hfloor' :
          15*(1+D)*(Real.log H/Real.log 2)*((M:ℝ)^2/H) ≤
          30*(1+D)*(Real.log M/Real.log 2)*(M:ℝ)^2*lam^((2:ℝ)/13) := by
        convert hfloor using 1 <;> dsimp only [H] <;> ring
      have hfloormul := mul_le_mul_of_nonneg_right hfloor' (show 0 ≤ (M:ℝ)^ε by positivity)
      have hB' : 30*(1+D) ≤ B := by dsimp [B]; linarith
      have hlast := mul_le_mul_of_nonneg_right hB' (show 0 ≤
        (Real.log M/Real.log 2)*(M:ℝ)^2*lam^((2:ℝ)/13)*(M:ℝ)^ε by positivity)
      have hfirst := hs.trans hscaled
      have hsecond := hfirst.trans (show
          15*(Real.log H/Real.log 2)*((1+D)*((M:ℝ)^2/H)*(M:ℝ)^ε) ≤
          30*(1+D)*(Real.log M/Real.log 2)*(M:ℝ)^2*lam^((2:ℝ)/13)*(M:ℝ)^ε by
        convert hfloormul using 1; ring)
      apply hsecond.trans
      convert hlast using 1 <;> ring
  have hlog : Real.log (M:ℝ)/Real.log 2 ≤ ((1+1/ε)/Real.log 2)*(M:ℝ)^ε := by
    have h := one_add_log_le_rpow_budget hM1 hε
    have h' : Real.log (M:ℝ) ≤ (1+1/ε)*(M:ℝ)^ε := by linarith
    have hd := div_le_div_of_nonneg_right h' hlog2.le
    convert hd using 1; ring
  have hmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤
      B*(M:ℝ)^2*lam^((2:ℝ)/13)*(M:ℝ)^ε by positivity)
  have hsq :
      ‖S‖^2 ≤ (Real.sqrt (B*(1+1/ε)/Real.log 2)*(M:ℝ)^(1+ε)*lam^((1:ℝ)/13))^2 := by
    apply hcoarse.trans
    have hlam2 : (lam^((1:ℝ)/13))^2 = lam^((2:ℝ)/13) := by
      rw [← Real.rpow_mul_natCast hlam.le]
      congr 1
      norm_num
    simp only [mul_pow,hlam2,Real.rpow_add hMp,Real.rpow_one,
      Real.sq_sqrt (show 0 ≤ B*(1+1/ε)/Real.log 2 by positivity)]
    convert hmul using 1 <;> ring
  have hn := norm_nonneg S
  have ht : 0 ≤ Real.sqrt (B*(1+1/ε)/Real.log 2)*(M:ℝ)^(1+ε)*lam^((1:ℝ)/13) := by positivity
  change ‖S‖ ≤ _
  nlinarith only [hsq,hn,ht]

/-- Long-range fourth-derivative estimate, with no small-lambda restriction. -/
theorem exists_robertSargos_fourth_derivative_long_range (ε : ℝ) (hε : 0 < ε)
    (C : ℝ) (hC : 1 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : ℝ → ℝ) (M : ℕ) (lam : ℝ),
    0 < lam → lam^(-(8:ℝ)/13) ≤ M →
    (∀ t ∈ Icc (1:ℝ) M, ContDiffAt ℝ 4 f t) →
    (∀ t ∈ Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f t) →
    (∀ t ∈ Icc (1:ℝ) M, iteratedDeriv 4 f t ≤ C*lam) →
    ‖∑ m ∈ Finset.Icc (1:ℤ) M, fordAdditiveCharacter (f m)‖ ≤
      K*(M:ℝ)^(1+ε)*lam^((1:ℝ)/13) := by
  obtain ⟨K,hK,hsmallRange⟩ := exists_robertSargos_fourth_derivative_long_range_small ε hε C hC
  refine ⟨K+2,by positivity,?_⟩
  intro f M lam hlam hM hf hlo hhi
  by_cases hsmall : lam ≤ 1/8192
  · apply (hsmallRange f M lam hlam hsmall hM hf hlo hhi).trans
    gcongr
    linarith
  have hMp : (0:ℝ) < M := (Real.rpow_pos_of_pos hlam (-(8:ℝ)/13)).trans_le hM
  have hM1 : (1:ℝ) ≤ M := by
    have hm : 0 < M := by exact_mod_cast hMp
    exact_mod_cast (show 1 ≤ M by omega)
  have hphase :
      ‖∑ m ∈ Finset.Icc (1:ℤ) M, fordAdditiveCharacter (f m)‖ ≤ M := by
    apply (norm_sum_le _ _).trans
    simp [sargos_character_norm,Int.card_Icc]
  have hlower : (1/2:ℝ) ≤ lam^((1:ℝ)/13) := by
    have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1/8192)
      (le_of_lt (lt_of_not_ge hsmall)) (by norm_num : (0:ℝ) ≤ 1/13)
    have he : (1/8192:ℝ)^((1:ℝ)/13) = 1/2 := by
      rw [show (1/8192:ℝ) = (2:ℝ)^(-(13:ℝ)) by norm_num,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    rwa [he] at h
  have hpower : (M:ℝ) ≤ (M:ℝ)^(1+ε) := by
    rw [Real.rpow_add hMp,Real.rpow_one]
    exact le_mul_of_one_le_right hMp.le (Real.one_le_rpow hM1 hε.le)
  have hprod := mul_le_mul_of_nonneg_left hlower
    (show 0 ≤ 2*(M:ℝ)^(1+ε) by positivity)
  calc
    _ ≤ (M:ℝ) := hphase
    _ ≤ (M:ℝ)^(1+ε) := hpower
    _ ≤ 2*(M:ℝ)^(1+ε)*lam^((1:ℝ)/13) := by nlinarith only [hprod]
    _ ≤ _ := by gcongr; linarith

end TaoTrudgianYang2025
