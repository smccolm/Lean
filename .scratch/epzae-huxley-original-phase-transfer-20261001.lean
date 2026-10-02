import TaoTrudgianYang2025.HuxleyLinearForms
import TaoTrudgianYang2025.ExponentPairSourceWeyl
import TaoTrudgianYang2025.DoubledBlockPrefixes
import TaoTrudgianYang2025.RobertSargosInitialDyadicLog
import TaoTrudgianYang2025.PointMeanLemmaThreeEdges

open scoped BigOperators FourierTransform Classical ContDiff NNReal
open Set Filter TaoTrudgianYang2025

namespace HuxleyOriginalPhaseScratch

private theorem nonnegative_doubled_block_selection
    (f : ℕ → ℝ) (H : ℕ) (hH : 2 ≤ H) (hf₀ : f 0=0)
    (hf : ∀ n, 0 ≤ f n) {A : ℝ} (hA : 0 ≤ A)
    (hcap : ∀ n < H, f n ≤ A) :
    ∃ k : ℕ, 0 < k ∧ 2*k ≤ H ∧
      (∑ n∈Finset.range H,f n) ≤
        (Nat.clog 2 H:ℝ)*(A+∑ j∈Finset.range k,f (k+j)) := by
  classical
  obtain ⟨k,hk,hmax⟩ := (Finset.Icc 1 (H/2)).exists_max_image
    (fun k => ∑ j∈Finset.range k,f (k+j))
    (by exact ⟨1,Finset.mem_Icc.mpr ⟨le_rfl,by omega⟩⟩)
  have hk' := Finset.mem_Icc.mp hk
  have hnorm (s : Finset ℕ) (g : ℕ → ℕ) :
      ‖∑ j∈s,(f (g j):ℂ)‖=∑ j∈s,f (g j) := by
    rw [←Complex.ofReal_sum]
    exact Complex.norm_of_nonneg (Finset.sum_nonneg (fun j _ => hf (g j)))
  have hbound := norm_prefix_le_doubled_blocks
    (fun n => (f n:ℂ)) H (Nat.clog 2 H) H
    (congrArg (fun x : ℝ => (x:ℂ)) hf₀) le_rfl (Nat.le_pow_clog (by norm_num) H)
    A (∑ j∈Finset.range k,f (k+j)) hA
    (Finset.sum_nonneg (fun j _ => hf (k+j)))
    (fun n hn => (Complex.norm_of_nonneg (hf n)).le.trans (hcap n hn))
    (fun l hl hlH => by
      rw [hnorm (Finset.range l) (fun j => l+j)]
      exact hmax l (Finset.mem_Icc.mpr ⟨by omega,by omega⟩))
  have he : ‖∑ n∈Finset.range H,(f n:ℂ)‖ = ∑ n∈Finset.range H,f n :=
    hnorm (Finset.range H) id
  rw [he] at hbound
  exact ⟨k,by omega,by omega,hbound⟩

private theorem norm_sourceShiftCorrelation_le_length
    (F : ℝ → ℝ) (X M : ℝ) (a L r : ℕ) :
    ‖sourceShiftCorrelation F X M a L r‖ ≤ (L:ℝ)+1 := by
  unfold sourceShiftCorrelation
  calc
    _ ≤ ∑ j∈Finset.range (L+1-r),
        ‖star (Expdb.oscillatory F X M ((a:ℝ)+j))*
          Expdb.oscillatory F X M ((a:ℝ)+j+r)‖ := norm_sum_le _ _
    _ = (L+1-r:ℕ) := by simp
    _ ≤ (L:ℝ)+1 := by exact_mod_cast (Nat.sub_le (L+1) r)


private theorem weyl_prefix_twenty_fourth_power
    {S All B M H L C : ℝ} (hM : 0 < M) (hH : 0 < H)
    (hAll : 0 ≤ All) (hB : 0 ≤ B) (hL : 0 ≤ L) (hC : 1 ≤ C)
    (hLM : L ≤ 2*M) (hHM : H ≤ M)
    (hWeyl : H^2*S^2 ≤ (L+H)*(H*L+2*H*All))
    (hPrefix : All ≤ C*(L+B)) :
    S^24 ≤ (18:ℝ)^12*(2:ℝ)^11*C^12*
      ((M^2/H)^12+(M/H)^12*B^12) := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hRight : 0 ≤ H*L+2*H*All := by positivity
  have hAllBound : All ≤ C*(2*M+B) :=
    hPrefix.trans (mul_le_mul_of_nonneg_left (add_le_add hLM le_rfl) hC0)
  have hraw : H^2*S^2 ≤ 18*H*C*(M^2+M*B) := by
    calc
      _ ≤ (L+H)*(H*L+2*H*All) := hWeyl
      _ ≤ (3*M)*(H*L+2*H*All) :=
        mul_le_mul_of_nonneg_right (by linarith only [hLM,hHM]) hRight
      _ ≤ (3*M)*(2*H*M+2*H*C*(2*M+B)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc
          _ ≤ H*(2*M)+2*H*(C*(2*M+B)) :=
            add_le_add (mul_le_mul_of_nonneg_left hLM hH.le)
              (mul_le_mul_of_nonneg_left hAllBound (by positivity))
          _ = _ := by ring
      _ ≤ _ := by
        nlinarith only [
          mul_nonneg (show 0 ≤ H*M^2 by positivity) (sub_nonneg.mpr hC),
          mul_nonneg (show 0 ≤ H*C*M by positivity) hB]
  have hSquare : S^2 ≤ 18*C*(M^2/H+(M/H)*B) := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hH)).mp
    calc
      _ ≤ 18*H*C*(M^2+M*B) := hraw
      _ = _ := by field_simp
  calc
    _ = (S^2)^12 := by ring
    _ ≤ (18*C*(M^2/H+(M/H)*B))^12 := pow_le_pow_left₀ (sq_nonneg S) hSquare 12
    _ = (18:ℝ)^12*C^12*(M^2/H+(M/H)*B)^12 := by ring
    _ ≤ (18:ℝ)^12*C^12*(2^11*((M^2/H)^12+((M/H)*B)^12)) :=
      mul_le_mul_of_nonneg_left (add_pow_le (by positivity) (by positivity) 12) (by positivity)
    _ = _ := by ring


private theorem source_correlation_doubled_block
    (F : ℝ → ℝ) (X M : ℝ) (a L H : ℕ) (hH : 2 ≤ H) :
    ∃ k : ℕ, 0 < k ∧ 2*k ≤ H ∧
      (∑ r∈Finset.Icc 1 (H-1),‖sourceShiftCorrelation F X M a L r‖) ≤
        (Nat.clog 2 H:ℝ)*((L:ℝ)+1+
          ∑ j∈Finset.range k,‖sourceShiftCorrelation F X M a L (k+j)‖) := by
  classical
  let f := fun r : ℕ => if r=0 then 0 else ‖sourceShiftCorrelation F X M a L r‖
  have hf₀ : f 0=0 := by simp only [f,if_pos rfl]
  have hf (r : ℕ) : 0 ≤ f r := by
    dsimp only [f]
    split_ifs
    · exact le_rfl
    · exact norm_nonneg _
  have hcap (r : ℕ) : f r ≤ (L:ℝ)+1 := by
    dsimp only [f]
    split_ifs
    · positivity
    · exact norm_sourceShiftCorrelation_le_length F X M a L r
  obtain ⟨k,hk,hkH,hs⟩ := nonnegative_doubled_block_selection f H hH hf₀ hf
    (show 0 ≤ (L:ℝ)+1 by positivity) (fun r _ => hcap r)
  have hfilt : (∑ r∈(Finset.range H).filter (fun r => 0<r),f r) =
      ∑ r∈Finset.range H,f r := by
    apply Finset.sum_filter_of_ne
    intro r _ hne
    by_contra hn
    have hr : r=0 := by omega
    subst r
    exact hne hf₀
  have hset : (Finset.range H).filter (fun r => 0<r) = Finset.Icc 1 (H-1) := by
    ext r
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Icc]
    omega
  have hall : (∑ r∈Finset.range H,f r) =
      ∑ r∈Finset.Icc 1 (H-1),‖sourceShiftCorrelation F X M a L r‖ := by
    rw [←hfilt,hset]
    apply Finset.sum_congr rfl
    intro r hr
    exact if_neg (by have := (Finset.mem_Icc.mp hr).1; omega)
  have hblock : (∑ j∈Finset.range k,f (k+j)) =
      ∑ j∈Finset.range k,‖sourceShiftCorrelation F X M a L (k+j)‖ := by
    apply Finset.sum_congr rfl
    intro j _
    exact if_neg (by omega)
  rw [hall,hblock] at hs
  exact ⟨k,hk,hkH,hs⟩

private theorem exists_source_dyadic_twenty_fourth_power
    (F : ℝ → ℝ) (X M : ℝ) (a L H : ℕ) (hM : 0 < M)
    (hH : 2 ≤ H) (hHM : (H:ℝ) ≤ M) (hLM : (L:ℝ)+1 ≤ 2*M) :
    ∃ k : ℕ, 0 < k ∧ 2*k ≤ H ∧
      ‖Expdb.exponentialSumAt F X M a (a+L)‖^24 ≤
        (18:ℝ)^12*(2:ℝ)^11*(Nat.clog 2 H:ℝ)^12*
          ((M^2/(H:ℝ))^12+(M/(H:ℝ))^12*
            (∑ j∈Finset.range k,‖sourceShiftCorrelation F X M a L (k+j)‖)^12) := by
  obtain ⟨k,hk,hkH,hs⟩ := source_correlation_doubled_block F X M a L H hH
  have hHpos : (0:ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hclog : 1 ≤ Nat.clog 2 H := by
    have hh := Nat.le_pow_clog (by norm_num : 1<2) H
    by_contra hn
    have hz : Nat.clog 2 H=0 := by omega
    rw [hz,pow_zero] at hh
    omega
  have hC : (1:ℝ) ≤ Nat.clog 2 H := by exact_mod_cast hclog
  have hw := source_exponentialSum_weyl F X M a L H
  simp only [Nat.cast_add,Nat.cast_one] at hw
  exact ⟨k,hk,hkH,weyl_prefix_twenty_fourth_power hM hHpos
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    (by positivity) hC hLM hHM hw hs⟩

example
    (f : ℕ → ℝ) (H : ℕ) (hH : 2 ≤ H) (hf₀ : f 0=0)
    (hf : ∀ n, 0 ≤ f n) {A : ℝ} (hA : 0 ≤ A)
    (hcap : ∀ n < H, f n ≤ A) :
    ∃ k : ℕ, 0 < k ∧ 2*k ≤ H ∧
      (∑ n∈Finset.range H,f n) ≤
        (Nat.clog 2 H:ℝ)*(A+∑ j∈Finset.range k,f (k+j)) :=
  HuxleyOriginalPhaseScratch.nonnegative_doubled_block_selection f H hH hf₀ hf (A:=A) hA hcap

example
    (F : ℝ → ℝ) (X M : ℝ) (a L r : ℕ) :
    ‖sourceShiftCorrelation F X M a L r‖ ≤ (L:ℝ)+1 :=
  HuxleyOriginalPhaseScratch.norm_sourceShiftCorrelation_le_length F X M a L r

example
    {S All B M H L C : ℝ} (hM : 0 < M) (hH : 0 < H)
    (hAll : 0 ≤ All) (hB : 0 ≤ B) (hL : 0 ≤ L) (hC : 1 ≤ C)
    (hLM : L ≤ 2*M) (hHM : H ≤ M)
    (hWeyl : H^2*S^2 ≤ (L+H)*(H*L+2*H*All))
    (hPrefix : All ≤ C*(L+B)) :
    S^24 ≤ (18:ℝ)^12*(2:ℝ)^11*C^12*
      ((M^2/H)^12+(M/H)^12*B^12) :=
  HuxleyOriginalPhaseScratch.weyl_prefix_twenty_fourth_power (S:=S) (All:=All) (B:=B) (M:=M) (H:=H) (L:=L) (C:=C) hM hH hAll hB hL hC hLM hHM hWeyl hPrefix

example
    (F : ℝ → ℝ) (X M : ℝ) (a L H : ℕ) (hH : 2 ≤ H) :
    ∃ k : ℕ, 0 < k ∧ 2*k ≤ H ∧
      (∑ r∈Finset.Icc 1 (H-1),‖sourceShiftCorrelation F X M a L r‖) ≤
        (Nat.clog 2 H:ℝ)*((L:ℝ)+1+
          ∑ j∈Finset.range k,‖sourceShiftCorrelation F X M a L (k+j)‖) :=
  HuxleyOriginalPhaseScratch.source_correlation_doubled_block F X M a L H hH

example
    (F : ℝ → ℝ) (X M : ℝ) (a L H : ℕ) (hM : 0 < M)
    (hH : 2 ≤ H) (hHM : (H:ℝ) ≤ M) (hLM : (L:ℝ)+1 ≤ 2*M) :
    ∃ k : ℕ, 0 < k ∧ 2*k ≤ H ∧
      ‖Expdb.exponentialSumAt F X M a (a+L)‖^24 ≤
        (18:ℝ)^12*(2:ℝ)^11*(Nat.clog 2 H:ℝ)^12*
          ((M^2/(H:ℝ))^12+(M/(H:ℝ))^12*
            (∑ j∈Finset.range k,‖sourceShiftCorrelation F X M a L (k+j)‖)^12) :=
  HuxleyOriginalPhaseScratch.exists_source_dyadic_twenty_fourth_power F X M a L H hM hH hHM hLM


#print axioms HuxleyOriginalPhaseScratch.nonnegative_doubled_block_selection
#print axioms HuxleyOriginalPhaseScratch.norm_sourceShiftCorrelation_le_length
#print axioms HuxleyOriginalPhaseScratch.weyl_prefix_twenty_fourth_power
#print axioms HuxleyOriginalPhaseScratch.source_correlation_doubled_block
#print axioms HuxleyOriginalPhaseScratch.exists_source_dyadic_twenty_fourth_power


private theorem exponentialSumAt_eq_int_Icc
    (F : ℝ → ℝ) (X M : ℝ) (a b : ℕ) :
    Expdb.exponentialSumAt F X M a b =
      ∑ j∈Finset.Icc (a:ℤ) (b:ℤ),Expdb.oscillatory F X M j := by
  unfold Expdb.exponentialSumAt
  apply Finset.sum_bij (fun (n:ℕ) _ => (n:ℤ))
  case hi =>
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hn'.1,by exact_mod_cast hn'.2⟩
  case i_inj =>
    intro n _ m _ hnm
    exact_mod_cast hnm
  case i_surj =>
    intro z hz
    have hz' := Finset.mem_Icc.mp hz
    have hz0 : 0≤z := (Int.natCast_nonneg a).trans hz'.1
    refine ⟨z.toNat,Finset.mem_Icc.mpr ⟨?_,?_⟩,Int.toNat_of_nonneg hz0⟩
    · omega
    · omega
  case h =>
    intro n _
    simp only [Int.cast_natCast]

private theorem norm_exponentialSumAt_le_int_Ioc
    (F : ℝ → ℝ) (X M : ℝ) (a b : ℕ) (hab : a≤b) :
    ‖Expdb.exponentialSumAt F X M a b‖ ≤
      1+‖∑ j∈Finset.Ioc (a:ℤ) (b:ℤ),Expdb.oscillatory F X M j‖ := by
  rw [exponentialSumAt_eq_int_Icc,
    Finset.Icc_eq_cons_Ioc (by exact_mod_cast hab : (a:ℤ)≤b),Finset.sum_cons]
  simpa only [Expdb.norm_oscillatory] using
    norm_add_le (Expdb.oscillatory F X M (a:ℤ))
      (∑ j∈Finset.Ioc (a:ℤ) (b:ℤ),Expdb.oscillatory F X M j)

private theorem norm_sourceShiftCorrelation_le_difference_Ioc
    (F : ℝ → ℝ) (X : ℝ) {M : ℝ} (hM : M≠0)
    (a L r k : ℕ) (hk : 0<k) (hrL : r≤L) :
    ‖sourceShiftCorrelation F X M a L r‖ ≤
      1+‖∑ j∈Finset.Ioc (a:ℤ) ((a+(L-r):ℕ):ℤ),
        Expdb.oscillatory
          (fun u => (F u-F (u+((k:ℝ)/M)*((r:ℝ)/k)))/((k:ℝ)/M))
          (X*k/M) M j‖ := by
  have hkR : (k:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hc := HuxleyRationalPhase.sourceShiftCorrelation_difference_family_sum
    F (σ:=1) (T:=X) (N:=M) (H:=(k:ℝ)) (by norm_num) hM hkR a L r hrL
  dsimp only at hc
  rw [hc]
  simpa only [one_mul,sub_add_cancel,Complex.norm_conj] using
    norm_exponentialSumAt_le_int_Ioc
      (fun u => (F u-F (u+((k:ℝ)/M)*((r:ℝ)/k-1+1)))/(1*((k:ℝ)/M)))
      (1*X*k/M) M a (a+(L-r)) (Nat.le_add_right _ _)

example
    (F : ℝ → ℝ) (X M : ℝ) (a b : ℕ) :
    Expdb.exponentialSumAt F X M a b =
      ∑ j∈Finset.Icc (a:ℤ) (b:ℤ),Expdb.oscillatory F X M j :=
  HuxleyOriginalPhaseScratch.exponentialSumAt_eq_int_Icc F X M a b

example
    (F : ℝ → ℝ) (X M : ℝ) (a b : ℕ) (hab : a≤b) :
    ‖Expdb.exponentialSumAt F X M a b‖ ≤
      1+‖∑ j∈Finset.Ioc (a:ℤ) (b:ℤ),Expdb.oscillatory F X M j‖ :=
  HuxleyOriginalPhaseScratch.norm_exponentialSumAt_le_int_Ioc F X M a b hab

example
    (F : ℝ → ℝ) (X : ℝ) {M : ℝ} (hM : M≠0)
    (a L r k : ℕ) (hk : 0<k) (hrL : r≤L) :
    ‖sourceShiftCorrelation F X M a L r‖ ≤
      1+‖∑ j∈Finset.Ioc (a:ℤ) ((a+(L-r):ℕ):ℤ),
        Expdb.oscillatory
          (fun u => (F u-F (u+((k:ℝ)/M)*((r:ℝ)/k)))/((k:ℝ)/M))
          (X*k/M) M j‖ :=
  HuxleyOriginalPhaseScratch.norm_sourceShiftCorrelation_le_difference_Ioc F X (M:=M) hM a L r k hk hrL


#print axioms HuxleyOriginalPhaseScratch.exponentialSumAt_eq_int_Icc
#print axioms HuxleyOriginalPhaseScratch.norm_exponentialSumAt_le_int_Ioc
#print axioms HuxleyOriginalPhaseScratch.norm_sourceShiftCorrelation_le_difference_Ioc


private theorem comparable_radius_powers
    {N R S D : ℝ} (hN : 0<N) (hR : 0<R) (hS : 0<S) (hD : 1≤D)
    (hSR : S≤D*R) (hRS : R≤D*S) :
    S^2≤D^2*R^2 ∧ 1/S^2≤D^2/R^2 ∧
      (N/S)^((2:ℝ)/3)≤D*(N/R)^((2:ℝ)/3) ∧
      (S/N)^((2:ℝ)/3)≤D*(R/N)^((2:ℝ)/3) := by
  have hD0 : 0≤D := zero_le_one.trans hD
  have hDs : D^((2:ℝ)/3)≤D := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hD (by norm_num : (2:ℝ)/3≤1)
  have hpow {x y : ℝ} (hx : 0≤x) (hy : 0≤y) (hxy : x≤D*y) :
      x^((2:ℝ)/3)≤D*y^((2:ℝ)/3) := by
    calc
      _ ≤ (D*y)^((2:ℝ)/3) := Real.rpow_le_rpow hx hxy (by norm_num)
      _ = D^((2:ℝ)/3)*y^((2:ℝ)/3) := Real.mul_rpow hD0 hy
      _ ≤ _ := mul_le_mul_of_nonneg_right hDs (Real.rpow_nonneg hy _)
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [mul_pow] using pow_le_pow_left₀ hS.le hSR 2
  · apply (div_le_div_iff₀ (sq_pos_of_pos hS) (sq_pos_of_pos hR)).mpr
    simpa only [one_mul,mul_pow] using pow_le_pow_left₀ hR.le hRS 2
  · apply hpow (div_nonneg hN.le hS.le) (div_nonneg hN.le hR.le)
    calc
      _ ≤ (D*N)/R := (div_le_div_iff₀ hS hR).mpr (by
        nlinarith only [mul_le_mul_of_nonneg_left hRS hN.le])
      _ = _ := by ring
  · apply hpow (div_nonneg hS.le hN.le) (div_nonneg hR.le hN.le)
    calc
      _ ≤ (D*R)/N := div_le_div_of_nonneg_right hSR hN.le
      _ = _ := by ring

example
    {N R S D : ℝ} (hN : 0<N) (hR : 0<R) (hS : 0<S) (hD : 1≤D)
    (hSR : S≤D*R) (hRS : R≤D*S) :
    S^2≤D^2*R^2 ∧ 1/S^2≤D^2/R^2 ∧
      (N/S)^((2:ℝ)/3)≤D*(N/R)^((2:ℝ)/3) ∧
      (S/N)^((2:ℝ)/3)≤D*(R/N)^((2:ℝ)/3) :=
  HuxleyOriginalPhaseScratch.comparable_radius_powers (N:=N) (R:=R) (S:=S) (D:=D) hN hR hS hD hSR hRS


#print axioms HuxleyOriginalPhaseScratch.comparable_radius_powers


private theorem upper_radius_error_bound
    {Ysmall Y M N R S D : ℝ}
    (hYsmall : 0≤Ysmall) (hY : Ysmall≤Y) (hM : 0<M) (hN : 0<N)
    (hR : 0<R) (hS : 0<S) (hD : 1≤D) (hSR : S≤D*R) (hRS : R≤D*S) :
    Ysmall*M/Real.sqrt N+Ysmall*M*S^2/N^2+Ysmall*N*(N/S)^((2:ℝ)/3) ≤
      D^2*(Y*M/Real.sqrt N+Y*M*R^2/N^2+Y*N*(N/R)^((2:ℝ)/3)) := by
  have hY0 := hYsmall.trans hY
  have hD0 := zero_le_one.trans hD
  have hD2 : 1≤D^2 := by nlinarith only [hD,sq_nonneg (D-1)]
  have hDD2 : D≤D^2 := by nlinarith only [hD,sq_nonneg (D-1)]
  obtain ⟨hSq,_,hInv,_⟩ := comparable_radius_powers hN hR hS hD hSR hRS
  have h₁ : Ysmall*M/Real.sqrt N≤D^2*(Y*M/Real.sqrt N) := by
    calc
      _ ≤ Y*M/Real.sqrt N := by gcongr
      _ ≤ _ := le_mul_of_one_le_left (by positivity) hD2
  have h₂ : Ysmall*M*S^2/N^2≤D^2*(Y*M*R^2/N^2) := by
    calc
      _ ≤ Y*M*(D^2*R^2)/N^2 := by gcongr
      _ = _ := by ring
  have h₃ : Ysmall*N*(N/S)^((2:ℝ)/3)≤D^2*(Y*N*(N/R)^((2:ℝ)/3)) := by
    calc
      _ ≤ Y*N*(D*(N/R)^((2:ℝ)/3)) := by gcongr
      _ = D*(Y*N*(N/R)^((2:ℝ)/3)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hDD2 (by positivity)
  calc
    _ ≤ D^2*(Y*M/Real.sqrt N)+D^2*(Y*M*R^2/N^2)+
        D^2*(Y*N*(N/R)^((2:ℝ)/3)) := add_le_add (add_le_add h₁ h₂) h₃
    _ = _ := by ring

private theorem upper_radius_main_bound
    {Ysmall Y M N R S D J : ℝ}
    (hYsmall : 0≤Ysmall) (hY : Ysmall≤Y) (hM : 0<M) (hN : 0<N)
    (hR : 0<R) (hS : 0<S) (hD : 1≤D) (hJ : 0≤J)
    (hSR : S≤D*R) (hRS : R≤D*S) :
    Ysmall^11*M^11/(N*S^2)+Ysmall^11*J*M^11/N^3+
      Ysmall^12*M^12/(N^4*S^2)*(S/N)^((2:ℝ)/3) ≤
    D^4*(Y^11*M^11/(N*R^2)+Y^11*J*M^11/N^3+
      Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) := by
  have hY0 := hYsmall.trans hY
  have hD0 := zero_le_one.trans hD
  have hD4 : 1≤D^4 := one_le_pow₀ hD
  have hD24 : D^2≤D^4 := pow_le_pow_right₀ hD (by norm_num)
  have hD34 : D^3≤D^4 := pow_le_pow_right₀ hD (by norm_num)
  obtain ⟨_,hInv,_,hFor⟩ := comparable_radius_powers hN hR hS hD hSR hRS
  have h₁ : Ysmall^11*M^11/(N*S^2)≤D^4*(Y^11*M^11/(N*R^2)) := by
    calc
      _ = (Ysmall^11*M^11/N)*(1/S^2) := by ring
      _ ≤ (Y^11*M^11/N)*(D^2/R^2) := by gcongr
      _ = D^2*(Y^11*M^11/(N*R^2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD24 (by positivity)
  have h₂ : Ysmall^11*J*M^11/N^3≤D^4*(Y^11*J*M^11/N^3) := by
    calc
      _ ≤ Y^11*J*M^11/N^3 := by gcongr
      _ ≤ _ := le_mul_of_one_le_left (by positivity) hD4
  have h₃ : Ysmall^12*M^12/(N^4*S^2)*(S/N)^((2:ℝ)/3)≤
      D^4*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) := by
    calc
      _ = (Ysmall^12*M^12/N^4)*(1/S^2)*(S/N)^((2:ℝ)/3) := by ring
      _ ≤ (Y^12*M^12/N^4)*(D^2/R^2)*(D*(R/N)^((2:ℝ)/3)) := by gcongr
      _ = D^3*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD34 (by positivity)
  calc
    _ ≤ D^4*(Y^11*M^11/(N*R^2))+D^4*(Y^11*J*M^11/N^3)+
        D^4*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) :=
          add_le_add (add_le_add h₁ h₂) h₃
    _ = _ := by ring

example
    {Ysmall Y M N R S D : ℝ}
    (hYsmall : 0≤Ysmall) (hY : Ysmall≤Y) (hM : 0<M) (hN : 0<N)
    (hR : 0<R) (hS : 0<S) (hD : 1≤D) (hSR : S≤D*R) (hRS : R≤D*S) :
    Ysmall*M/Real.sqrt N+Ysmall*M*S^2/N^2+Ysmall*N*(N/S)^((2:ℝ)/3) ≤
      D^2*(Y*M/Real.sqrt N+Y*M*R^2/N^2+Y*N*(N/R)^((2:ℝ)/3)) :=
  HuxleyOriginalPhaseScratch.upper_radius_error_bound (Ysmall:=Ysmall) (Y:=Y) (M:=M) (N:=N) (R:=R) (S:=S) (D:=D) hYsmall hY hM hN hR hS hD hSR hRS

example
    {Ysmall Y M N R S D J : ℝ}
    (hYsmall : 0≤Ysmall) (hY : Ysmall≤Y) (hM : 0<M) (hN : 0<N)
    (hR : 0<R) (hS : 0<S) (hD : 1≤D) (hJ : 0≤J)
    (hSR : S≤D*R) (hRS : R≤D*S) :
    Ysmall^11*M^11/(N*S^2)+Ysmall^11*J*M^11/N^3+
      Ysmall^12*M^12/(N^4*S^2)*(S/N)^((2:ℝ)/3) ≤
    D^4*(Y^11*M^11/(N*R^2)+Y^11*J*M^11/N^3+
      Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) :=
  HuxleyOriginalPhaseScratch.upper_radius_main_bound (Ysmall:=Ysmall) (Y:=Y) (M:=M) (N:=N) (R:=R) (S:=S) (D:=D) (J:=J) hYsmall hY hM hN hR hS hD hJ hSR hRS


#print axioms HuxleyOriginalPhaseScratch.upper_radius_error_bound
#print axioms HuxleyOriginalPhaseScratch.upper_radius_main_bound


private theorem normalized_radius_comparable
    {γ R S D : ℝ} (hR : 0<R) (hS : 0<S) (hD : 1≤D)
    (hγD : γ≤D) (hDγ : 1≤D*γ) (hlink : γ*S^2=R^2) :
    S≤D*R ∧ R≤D*S := by
  have hD0 := zero_le_one.trans hD
  have hDD2 : D≤D^2 := by nlinarith only [hD,sq_nonneg (D-1)]
  constructor
  · apply (sq_le_sq₀ hS.le (mul_nonneg hD0 hR.le)).mp
    calc
      _ ≤ (D*γ)*S^2 := le_mul_of_one_le_left (sq_nonneg S) hDγ
      _ = D*R^2 := by rw [mul_assoc,hlink]
      _ ≤ D^2*R^2 := mul_le_mul_of_nonneg_right hDD2 (sq_nonneg R)
      _ = _ := (mul_pow D R 2).symm
  · apply (sq_le_sq₀ hR.le (mul_nonneg hD0 hS.le)).mp
    calc
      _ = γ*S^2 := hlink.symm
      _ ≤ D*S^2 := mul_le_mul_of_nonneg_right hγD (sq_nonneg S)
      _ ≤ D^2*S^2 := mul_le_mul_of_nonneg_right hDD2 (sq_nonneg S)
      _ = _ := (mul_pow D S 2).symm

private theorem comparable_radius_source_budgets
    {M N R S D C : ℝ} (hM : 0<M) (hN : 0<N)
    (hR : 0<R) (hD : 1≤D) (hC : 1≤C)
    (hSR : S≤D*R) (hRS : R≤D*S)
    (hRlow : C*D^7≤R) (hRN : (C*D^7)*R≤N)
    (hNR : (C*D^7)*N≤R^2) (hNM : (C*D^7)*N^2≤M)
    (hFour : (C*D^7)*N^4≤M*R^3)
    (hTen : (C*D^7)*N^10≤M^3*R^7) :
    1≤S ∧ C*S≤N ∧ C*N≤S^2 ∧ C*N^2≤M ∧
      N^4≤M*S^3 ∧ N^10≤M^3*S^7 := by
  have hDpos := zero_lt_one.trans_le hD
  have hCpos := zero_lt_one.trans_le hC
  have hpow (i : ℕ) (hi : i≤7) : C*D^i≤C*D^7 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hi) hCpos.le
  have hplain (i : ℕ) (hi : i≤7) : D^i≤C*D^7 :=
    (le_mul_of_one_le_left (pow_nonneg hDpos.le i) hC).trans (hpow i hi)
  have hB : C≤C*D^7 := by simpa only [pow_zero,mul_one] using hpow 0 (by omega)
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · have hDb : D≤C*D^7 := by simpa only [pow_one] using hplain 1 (by omega)
    have hh := hDb.trans (hRlow.trans hRS)
    nlinarith only [hh,hDpos]
  · calc
      _ ≤ C*(D*R) := mul_le_mul_of_nonneg_left hSR hCpos.le
      _ = (C*D^1)*R := by ring
      _ ≤ (C*D^7)*R := mul_le_mul_of_nonneg_right (hpow 1 (by omega)) hR.le
      _ ≤ N := hRN
  · apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hDpos)).mp
    calc
      _ = (C*D^2)*N := by ring
      _ ≤ (C*D^7)*N := mul_le_mul_of_nonneg_right (hpow 2 (by omega)) hN.le
      _ ≤ R^2 := hNR
      _ ≤ (D*S)^2 := pow_le_pow_left₀ hR.le hRS 2
      _ = _ := by ring
  · exact (mul_le_mul_of_nonneg_right hB (sq_nonneg N)).trans hNM
  · apply (mul_le_mul_iff_right₀ (pow_pos hDpos 3)).mp
    calc
      _ ≤ (C*D^7)*N^4 :=
        mul_le_mul_of_nonneg_right (hplain 3 (by omega)) (pow_nonneg hN.le 4)
      _ ≤ M*R^3 := hFour
      _ ≤ M*(D*S)^3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR.le hRS 3) hM.le
      _ = _ := by ring
  · apply (mul_le_mul_iff_right₀ (pow_pos hDpos 7)).mp
    calc
      _ ≤ (C*D^7)*N^10 :=
        mul_le_mul_of_nonneg_right (hplain 7 le_rfl) (pow_nonneg hN.le 10)
      _ ≤ M^3*R^7 := hTen
      _ ≤ M^3*(D*S)^7 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR.le hRS 7) (pow_nonneg hM.le 3)
      _ = _ := by ring

example
    {γ R S D : ℝ} (hR : 0<R) (hS : 0<S) (hD : 1≤D)
    (hγD : γ≤D) (hDγ : 1≤D*γ) (hlink : γ*S^2=R^2) :
    S≤D*R ∧ R≤D*S :=
  HuxleyOriginalPhaseScratch.normalized_radius_comparable (γ:=γ) (R:=R) (S:=S) (D:=D) hR hS hD hγD hDγ hlink

example
    {M N R S D C : ℝ} (hM : 0<M) (hN : 0<N)
    (hR : 0<R) (hD : 1≤D) (hC : 1≤C)
    (hSR : S≤D*R) (hRS : R≤D*S)
    (hRlow : C*D^7≤R) (hRN : (C*D^7)*R≤N)
    (hNR : (C*D^7)*N≤R^2) (hNM : (C*D^7)*N^2≤M)
    (hFour : (C*D^7)*N^4≤M*R^3)
    (hTen : (C*D^7)*N^10≤M^3*R^7) :
    1≤S ∧ C*S≤N ∧ C*N≤S^2 ∧ C*N^2≤M ∧
      N^4≤M*S^3 ∧ N^10≤M^3*S^7 :=
  HuxleyOriginalPhaseScratch.comparable_radius_source_budgets (M:=M) (N:=N) (R:=R) (S:=S) (D:=D) (C:=C) hM hN hR hD hC hSR hRS hRlow hRN hNR hNM hFour hTen


#print axioms HuxleyOriginalPhaseScratch.normalized_radius_comparable
#print axioms HuxleyOriginalPhaseScratch.comparable_radius_source_budgets



private theorem upper_expression_nonnegative
    {Y M N R J : ℝ} (hY : 0≤Y) (hM : 0≤M) (hN : 0≤N)
    (hR : 0≤R) (hJ : 0≤J) :
    0≤Y*M/Real.sqrt N+Y*M*R^2/N^2+Y*N*(N/R)^((2:ℝ)/3) ∧
    0≤Y^11*M^11/(N*R^2)+Y^11*J*M^11/N^3+
      Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3) := by
  constructor <;> positivity

example
    {Y M N R J : ℝ} (hY : 0≤Y) (hM : 0≤M) (hN : 0≤N)
    (hR : 0≤R) (hJ : 0≤J) :
    0≤Y*M/Real.sqrt N+Y*M*R^2/N^2+Y*N*(N/R)^((2:ℝ)/3) ∧
    0≤Y^11*M^11/(N*R^2)+Y^11*J*M^11/N^3+
      Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3) :=
  HuxleyOriginalPhaseScratch.upper_expression_nonnegative (Y:=Y) (M:=M) (N:=N) (R:=R) (J:=J) hY hM hN hR hJ


#print axioms HuxleyOriginalPhaseScratch.upper_expression_nonnegative

private theorem approximateModelPhase_enlarged_quantitative_upper
    {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ δ η₀ B C : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 1 ≤ B ∧ 1 ≤ C ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1 ≤ M →
        Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
        ∃ Fext : ℝ → ℝ,
          (∀ (X : ℝ) (a b : ℕ), M ≤ (a:ℝ) → (b:ℝ) ≤ 2*M →
            ‖Expdb.exponentialSumAt F X M a b-
              Expdb.exponentialSumAt Fext X M a b‖ ≤ 6) ∧
          ∀ (T : ℝ) (Y : Finset ℝ) (n N : ℕ) (R Jsep η : ℝ),
            C ≤ T → N=8*n → 2 ≤ N → B ≤ R →
            0 < η → η ≤ η₀ → 0 < Jsep → Jsep ≤ M →
            (∀ y∈Y, y∈Icc (1:ℝ) 2) →
            (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
            T*(N:ℝ)*R^2=M^3 →
            B*R ≤ N → B*(N:ℝ) ≤ R^2 → B*(N:ℝ)^2 ≤ M →
            B*(N:ℝ)^4 ≤ M*R^3 → B*(N:ℝ)^10 ≤ M^3*R^7 →
            ∀ A Bint : ℝ → ℤ, (∀ y∈Y, ⌈M⌉ ≤ A y) →
              (∀ y∈Y, A y ≤ Bint y) → (∀ y∈Y, Bint y ≤ ⌊2*M⌋) →
              let Yc := (Y.card:ℝ)
              let ErrorTotal := Yc*M/Real.sqrt (N:ℝ)+Yc*M*R^2/(N:ℝ)^2+
                Yc*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
              let Main := Yc^11*M^11/((N:ℝ)*R^2)+
                Yc^11*Jsep*M^11/(N:ℝ)^3+
                Yc^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
              (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y),
                (𝐞 (T*(Fext ((j:ℝ)/M)-Fext ((j:ℝ)/M+η*y))/η):ℂ)‖)^12 ≤
                  C*T^ε*(ErrorTotal^12+Main) := by
  classical
  have hσone : 0<σ+1 := by linarith only [hσ]
  let δmodel := min (modelPhaseThirdLower (σ+1)) 1/2
  have hmin : 0 < min (modelPhaseThirdLower (σ+1)) 1 :=
    lt_min (modelPhaseThirdLower_pos hσone) zero_lt_one
  have hδmodel : 0<δmodel := half_pos hmin
  have hδmodelCap : δmodel ≤ min (modelPhaseThirdLower (σ+1)) 1 := by
    dsimp only [δmodel]
    linarith only [hmin]
  obtain ⟨δ,ηsrc,a,c,J,hδ,hηsrc,hηsrcCap,ha,hc,hJ,hanchor,hsource⟩ :=
    HuxleyRationalPhase.approximateModelPhase_enlarged_colored_common_scale_source
      hσ hδmodel (by norm_num : (0:ℝ)<1) 5 le_rfl
  have hanchor' : c≤4*modelPhaseThirdLower (σ+1)*1/((σ+1)*((σ+1)+1)+3) := by
    simpa only [add_assoc,show (1:ℝ)+1=2 by norm_num] using hanchor
  obtain ⟨Cbudget,ηquant,hCbudget,hηquant,_,hquant⟩ :=
    HuxleyRationalPhase.eventually_upper_quantitative_phase_subinterval_bound
      (by norm_num : (0:ℝ)<1) hc hJ hσone hδmodel.le hδmodelCap hε hanchor'
  obtain ⟨Tcut,hTcut⟩ := Filter.eventually_atTop.mp hquant
  let D := 2+2*σ+1/σ
  have hD : 1≤D := by
    dsimp only [D]
    have hi : 0<1/σ := div_pos zero_lt_one hσ
    linarith only [hσ,hi]
  have hDpos := zero_lt_one.trans_le hD
  have hDσ : 1≤D*σ := by
    have hi : (1/σ)*σ=1 := div_mul_cancel₀ 1 hσ.ne'
    dsimp only [D]
    nlinarith only [hi,hσ,sq_nonneg σ]
  have hσD : 2*σ≤D := by
    dsimp only [D]
    have hi : 0<1/σ := by positivity
    linarith only [hi]
  let B := Cbudget*D^7
  have hB : 1≤B := by
    calc
      _ = (1:ℝ)*1 := by norm_num
      _ ≤ Cbudget*D^7 := mul_le_mul hCbudget (one_le_pow₀ hD)
        zero_le_one (zero_le_one.trans hCbudget)
  let Cap := 4/a+3
  have hCap : 1≤Cap := by
    dsimp only [Cap]
    have hh : 0<4/a := by positivity
    linarith only [hh]
  let K := (2*σ)^ε*D^24
  have hK : 0≤K := mul_nonneg
    (Real.rpow_nonneg (mul_nonneg (by norm_num) hσ.le) ε) (pow_nonneg hDpos.le 24)
  let C := max 1 (max (Tcut/σ) (Cap^12*K))
  have hC : 1≤C := le_max_left _ _
  have hCcut : Tcut/σ≤C := (le_max_left _ _).trans (le_max_right _ _)
  have hCK : Cap^12*K≤C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨δ,min ηsrc ηquant,B,C,hδ,lt_min hηsrc hηquant,
    (min_le_left _ _).trans hηsrcCap,hB,hC,?_⟩
  intro M F hM hF
  obtain ⟨Fext,_,_,hsharp,hcolors⟩ := hsource M F hM hF
  refine ⟨Fext,hsharp,?_⟩
  intro T Y n N R Jsep η hT hN8 hN2 hRlow hη hηcap hJsep hJsepM
    hY hsep hphase hRN hNR hNM hFour hTen A Bint hA hAB hBint Yc ErrorTotal Main
  have hMp : 0<M := zero_lt_one.trans_le hM
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hRp : 0<R := zero_lt_one.trans_le (hB.trans hRlow)
  have hTp : 0<T := zero_lt_one.trans_le (hC.trans hT)
  have hYc : 0≤Yc := Nat.cast_nonneg _
  have hSigns := upper_expression_nonnegative hYc hMp.le hNp.le hRp.le hJsep.le
  have hError : 0≤ErrorTotal := hSigns.1
  have hMain : 0≤Main := hSigns.2
  have hMass : 0≤ErrorTotal^12+Main := add_nonneg (pow_nonneg hError 12) hMain
  let color := fun y : ℝ => ⌊y/a⌋
  let z := fun y : ℝ => (‖∑ j∈Finset.Ioc (A y) (Bint y),
    (𝐞 (T*(Fext ((j:ℝ)/M)-Fext ((j:ℝ)/M+η*y))/η):ℂ)‖:ℂ)
  have hzNorm (U : Finset ℝ) :
      ‖∑ y∈U,z y‖ = ∑ y∈U,‖∑ j∈Finset.Ioc (A y) (Bint y),
        (𝐞 (T*(Fext ((j:ℝ)/M)-Fext ((j:ℝ)/M+η*y))/η):ℂ)‖ := by
    dsimp only [z]
    rw [←Complex.ofReal_sum]
    exact Complex.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  obtain ⟨hcard,hmoment,hclasses⟩ :=
    hcolors Y id η hY hη (hηcap.trans (min_le_left _ _))
  have hlocal (j : ℤ) (hj : j∈Y.image color) :
      ‖∑ y∈Y.filter (fun y => color y=j),z y‖^12 ≤
        K*T^ε*(ErrorTotal^12+Main) := by
    obtain ⟨y₀,hy₀,_,hreg,hjets,htests,hnegative,hscaled⟩ := hclasses j hj
    let γ := σ*y₀
    have hy₀range := hY y₀ hy₀
    have hy₀p : 0<y₀ := zero_lt_one.trans_le hy₀range.1
    have hγ : 0<γ := mul_pos hσ hy₀p
    have hγlo : σ≤γ := le_mul_of_one_le_right hσ.le hy₀range.1
    have hγhi : γ≤2*σ := by dsimp only [γ]; nlinarith only [hy₀range.2,hσ]
    have hγD := hγhi.trans hσD
    have hDγ : 1≤D*γ := hDσ.trans (mul_le_mul_of_nonneg_left hγlo hDpos.le)
    let Fsrc := fun w => (1/(σ*y₀))*Fext w
    let Tnew := T*σ*y₀/1
    let Rnew := R*Real.sqrt (1/(σ*y₀))
    obtain ⟨hTnew,hRnew,hRsq,hnewphase,hmodels⟩ :=
      hscaled T (N:ℝ) R hTp hRp hphase
    have hTnewEq : Tnew=T*γ := by dsimp only [Tnew,γ]; rw [div_one,mul_assoc]
    have hRnewSq : Rnew^2=R^2/γ := by
      simpa only [mul_one] using hRsq
    have hRg : γ*Rnew^2=R^2 := by rw [hRnewSq]; field_simp
    obtain ⟨hSle,hRle⟩ := normalized_radius_comparable hRp hRnew hD hγD hDγ hRg
    obtain ⟨hRnew1,hnewRN,hnewNR,hnewNM,hnewFour,hnewTen⟩ :=
      comparable_radius_source_budgets hMp hNp hRp hD hCbudget hSle hRle
        hRlow hRN hNR hNM hFour hTen
    have hTnewCut : Tcut≤Tnew := by
      rw [hTnewEq]
      exact ((div_le_iff₀ hσ).mp (hCcut.trans hT)).trans
        (mul_le_mul_of_nonneg_left hγlo hTp.le)
    let Yj := Y.filter (fun y => color y=j)
    have hYj (y : ℝ) (hy : y∈Yj) : y∈Y :=
      (Finset.mem_filter.mp hy).1
    have hYjColor (y : ℝ) (hy : y∈Yj) : color y=j :=
      (Finset.mem_filter.mp hy).2
    have hmod (y : ℝ) (hy : y∈Yj) :
        Expdb.IsApproximateModelPhaseFunction
          (fun u => (Fsrc u-Fsrc (u+η*y))/(1*η)) (σ+1) 4 δmodel :=
      approximateModelPhase_mono (hmodels y (hYj y hy) (hYjColor y hy)).1
        (by norm_num) le_rfl
    have hq := hTcut Tnew hTnewCut Fsrc Yj n N Rnew Jsep hN8 hN2 hRnew1
      hη (hηcap.trans (min_le_right _ _)) hJsep hJsepM
      (fun y hy => hY y (hYj y hy))
      (fun y hy v hv hne => hsep y (hYj y hy) v (hYj v hv) hne)
      hreg hjets htests hnegative hmod hnewphase hnewRN hnewNR hnewNM
      hnewFour hnewTen A Bint (fun y hy => hA y (hYj y hy))
      (fun y hy => hAB y (hYj y hy)) (fun y hy => hBint y (hYj y hy))
    have hYj0 : (0:ℝ)≤Yj.card := Nat.cast_nonneg _
    have hYjCard : (Yj.card:ℝ)≤Yc := by
      change ((Y.filter (fun y => color y=j)).card:ℝ)≤(Y.card:ℝ)
      exact_mod_cast (Finset.card_filter_le Y (fun y => color y=j))
    let Enew := (Yj.card:ℝ)*M/Real.sqrt (N:ℝ)+
      (Yj.card:ℝ)*M*Rnew^2/(N:ℝ)^2+
      (Yj.card:ℝ)*(N:ℝ)*((N:ℝ)/Rnew)^((2:ℝ)/3)
    let MainNew := (Yj.card:ℝ)^11*M^11/((N:ℝ)*Rnew^2)+
      (Yj.card:ℝ)^11*Jsep*M^11/(N:ℝ)^3+
      (Yj.card:ℝ)^12*M^12/((N:ℝ)^4*Rnew^2)*(Rnew/(N:ℝ))^((2:ℝ)/3)
    have hEnew : Enew≤D^2*ErrorTotal :=
      upper_radius_error_bound hYj0 hYjCard hMp hNp hRp hRnew hD hSle hRle
    have hMainNew : MainNew≤D^4*Main :=
      upper_radius_main_bound hYj0 hYjCard hMp hNp hRp hRnew hD hJsep.le hSle hRle
    have hNewSigns := upper_expression_nonnegative hYj0 hMp.le hNp.le hRnew.le hJsep.le
    have hEnew0 : 0≤Enew := hNewSigns.1
    have hMainNew0 : 0≤MainNew := hNewSigns.2
    have hEpow : Enew^12≤D^24*ErrorTotal^12 := by
      calc
        _ ≤ (D^2*ErrorTotal)^12 := pow_le_pow_left₀ hEnew0 hEnew 12
        _ = _ := by rw [mul_pow,←pow_mul]
    have hMainPow : MainNew≤D^24*Main :=
      hMainNew.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hD (by norm_num : 4≤24)) hMain)
    have hTotal : Enew^12+MainNew≤D^24*(ErrorTotal^12+Main) := by
      calc
        _ ≤ D^24*ErrorTotal^12+D^24*Main := add_le_add hEpow hMainPow
        _ = _ := (mul_add _ _ _).symm
    have hTpow : Tnew^ε≤(2*σ)^ε*T^ε := by
      rw [hTnewEq,Real.mul_rpow hTp.le hγ.le]
      calc
        _ ≤ T^ε*(2*σ)^ε :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hγ.le hγhi hε.le)
            (Real.rpow_nonneg hTp.le _)
        _ = _ := mul_comm _ _
    rw [hzNorm]
    calc
      _ = (∑ y∈Yj,‖∑ l∈Finset.Ioc (A y) (Bint y),
          (𝐞 (Tnew*(Fsrc ((l:ℝ)/M)-Fsrc ((l:ℝ)/M+η*y))/(1*η)):ℂ)‖)^12 := by
        congr 1
        apply Finset.sum_congr rfl
        intro y hy
        congr 1
        apply Finset.sum_congr rfl
        intro l _
        apply congrArg (fun x : ℝ => (𝐞 x:ℂ))
        simpa only [one_mul] using ((hmodels y (hYj y hy) (hYjColor y hy)).2.1 (l:ℝ)).symm
      _ ≤ Tnew^ε*(Enew^12+MainNew) := hq
      _ ≤ ((2*σ)^ε*T^ε)*(D^24*(ErrorTotal^12+Main)) :=
        mul_le_mul hTpow hTotal (add_nonneg (pow_nonneg hEnew0 12) hMainNew0)
          (mul_nonneg (Real.rpow_nonneg (mul_nonneg (by norm_num) hσ.le) ε)
            (Real.rpow_nonneg hTp.le ε))
      _ = _ := by dsimp only [K]; ac_rfl
  have hKmass : 0≤K*T^ε*(ErrorTotal^12+Main) :=
    mul_nonneg (mul_nonneg hK (Real.rpow_nonneg hTp.le ε)) hMass
  have hcolorSum :
      (∑ j∈Y.image color,‖∑ y∈Y.filter (fun y => color y=j),z y‖^12) ≤
        Cap*(K*T^ε*(ErrorTotal^12+Main)) := by
    calc
      _ ≤ ∑ _j∈Y.image color,K*T^ε*(ErrorTotal^12+Main) :=
        Finset.sum_le_sum hlocal
      _ = ((Y.image color).card:ℝ)*(K*T^ε*(ErrorTotal^12+Main)) := by
        rw [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard hKmass
  calc
    _ = ‖∑ y∈Y,z y‖^12 := congrArg (fun x : ℝ => x^12) (hzNorm Y).symm
    _ ≤ Cap^11*∑ j∈Y.image color,‖∑ y∈Y.filter (fun y => color y=j),z y‖^12 :=
      hmoment z
    _ ≤ Cap^11*(Cap*(K*T^ε*(ErrorTotal^12+Main))) :=
      mul_le_mul_of_nonneg_left hcolorSum (pow_nonneg (zero_le_one.trans hCap) 11)
    _ = (Cap^12*K)*(T^ε*(ErrorTotal^12+Main)) := by
      rw [show Cap^12=Cap^11*Cap from pow_succ Cap 11]
      ac_rfl
    _ ≤ C*(T^ε*(ErrorTotal^12+Main)) :=
      mul_le_mul_of_nonneg_right hCK (mul_nonneg (Real.rpow_nonneg hTp.le ε) hMass)
    _ = _ := (mul_assoc _ _ _).symm

example
    {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ δ η₀ B C : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 1 ≤ B ∧ 1 ≤ C ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1 ≤ M →
        Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
        ∃ Fext : ℝ → ℝ,
          (∀ (X : ℝ) (a b : ℕ), M ≤ (a:ℝ) → (b:ℝ) ≤ 2*M →
            ‖Expdb.exponentialSumAt F X M a b-
              Expdb.exponentialSumAt Fext X M a b‖ ≤ 6) ∧
          ∀ (T : ℝ) (Y : Finset ℝ) (n N : ℕ) (R Jsep η : ℝ),
            C ≤ T → N=8*n → 2 ≤ N → B ≤ R →
            0 < η → η ≤ η₀ → 0 < Jsep → Jsep ≤ M →
            (∀ y∈Y, y∈Icc (1:ℝ) 2) →
            (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
            T*(N:ℝ)*R^2=M^3 →
            B*R ≤ N → B*(N:ℝ) ≤ R^2 → B*(N:ℝ)^2 ≤ M →
            B*(N:ℝ)^4 ≤ M*R^3 → B*(N:ℝ)^10 ≤ M^3*R^7 →
            ∀ A Bint : ℝ → ℤ, (∀ y∈Y, ⌈M⌉ ≤ A y) →
              (∀ y∈Y, A y ≤ Bint y) → (∀ y∈Y, Bint y ≤ ⌊2*M⌋) →
              let Yc := (Y.card:ℝ)
              let ErrorTotal := Yc*M/Real.sqrt (N:ℝ)+Yc*M*R^2/(N:ℝ)^2+
                Yc*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
              let Main := Yc^11*M^11/((N:ℝ)*R^2)+
                Yc^11*Jsep*M^11/(N:ℝ)^3+
                Yc^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
              (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y),
                (𝐞 (T*(Fext ((j:ℝ)/M)-Fext ((j:ℝ)/M+η*y))/η):ℂ)‖)^12 ≤
                  C*T^ε*(ErrorTotal^12+Main) :=
  HuxleyOriginalPhaseScratch.approximateModelPhase_enlarged_quantitative_upper (σ:=σ) (ε:=ε) hσ hε


#print axioms HuxleyOriginalPhaseScratch.approximateModelPhase_enlarged_quantitative_upper


private theorem dyadic_shift_actual_family
    (F : ℝ → ℝ) (X : ℝ) {M : ℝ} (hM : 0<M)
    (a L k : ℕ) (hk : 0<k) (ha : M≤(a:ℝ)) (hb : ((a+L:ℕ):ℝ)≤2*M) :
    let S := (Finset.Ico k (2*k)).filter (fun r => r≤L)
    let Y := S.image (fun (r:ℕ) => (r:ℝ)/(k:ℝ))
    let Bint := fun y : ℝ => ((a+(L-⌊(k:ℝ)*y⌋₊):ℕ):ℤ)
    Y.card≤k ∧
      (∀ y∈Y, y∈Icc (1:ℝ) 2) ∧
      (∀ y∈Y, ∀ z∈Y, y≠z → 1≤(k:ℝ)*|y-z|) ∧
      ⌈M⌉≤(a:ℤ) ∧ (∀ y∈Y, (a:ℤ)≤Bint y) ∧
      (∀ y∈Y, Bint y≤⌊2*M⌋) ∧
      (∑ j∈Finset.range k,‖sourceShiftCorrelation F X M a L (k+j)‖) ≤
        (Y.card:ℝ)+∑ y∈Y,‖∑ l∈Finset.Ioc (a:ℤ) (Bint y),
          (𝐞 ((X*k/M)*(F ((l:ℝ)/M)-F ((l:ℝ)/M+((k:ℝ)/M)*y))/
            ((k:ℝ)/M)):ℂ)‖ := by
  classical
  intro S Y Bint
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  have hinj : Function.Injective (fun r : ℕ => (r:ℝ)/(k:ℝ)) := by
    intro r s hrs
    have hh := (div_left_inj' hkR.ne').mp hrs
    exact_mod_cast hh
  have hcard : Y.card=S.card := Finset.card_image_of_injOn hinj.injOn
  have hSk : S.card≤k := by
    calc
      _ ≤ (Finset.Ico k (2*k)).card := Finset.card_filter_le _ _
      _ = k := by rw [Nat.card_Ico]; omega
  have hfloor (r : ℕ) : ⌊(k:ℝ)*((r:ℝ)/(k:ℝ))⌋₊=r := by
    rw [show (k:ℝ)*((r:ℝ)/(k:ℝ))=(r:ℝ) by field_simp]
    exact Nat.floor_natCast r
  have hgeom := HuxleyRationalPhase.difference_family_dyadic_parameter_geometry hkR
  refine ⟨hcard.trans_le hSk,?_,?_,?_,?_,?_,?_⟩
  · intro y hy
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hy
    have hr' := Finset.mem_Ico.mp (Finset.mem_filter.mp hr).1
    have hh := hgeom.1 r (by exact_mod_cast hr'.1)
      (by exact_mod_cast hr'.2.le)
    constructor <;> linarith only [hh.1,hh.2]
  · intro y hy z hz hyz
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hz
    have hrs : r≠s := fun he => hyz (congrArg (fun n : ℕ => (n:ℝ)/(k:ℝ)) he)
    have hh := hgeom.2 r s hrs
    rw [show (r:ℝ)/(k:ℝ)-1-((s:ℝ)/(k:ℝ)-1)=
      (r:ℝ)/(k:ℝ)-(s:ℝ)/(k:ℝ) by ring] at hh
    exact hh
  · apply Int.ceil_le.mpr
    simpa only [Int.cast_natCast] using ha
  · intro y _
    dsimp only [Bint]
    exact_mod_cast (Nat.le_add_right a (L-⌊(k:ℝ)*y⌋₊))
  · intro y _
    apply Int.le_floor.mpr
    have hh : ((a+(L-⌊(k:ℝ)*y⌋₊):ℕ):ℝ)≤((a+L:ℕ):ℝ) := by
      exact_mod_cast (show a+(L-⌊(k:ℝ)*y⌋₊)≤a+L by omega)
    exact hh.trans hb
  · let f := fun r => ‖sourceShiftCorrelation F X M a L r‖
    have hRange : (∑ j∈Finset.range k,f (k+j))=∑ r∈Finset.Ico k (2*k),f r := by
      apply Finset.sum_bij (fun (j:ℕ) _ => k+j)
      case hi =>
        intro j hj
        have hj' := Finset.mem_range.mp hj
        exact Finset.mem_Ico.mpr ⟨by omega,by omega⟩
      case i_inj =>
        intro j _ l _ hjl
        omega
      case i_surj =>
        intro r hr
        have hr' := Finset.mem_Ico.mp hr
        exact ⟨r-k,Finset.mem_range.mpr (by omega),by omega⟩
      case h =>
        intro j _
        rfl
    have hFilter : (∑ r∈S,f r)=∑ r∈Finset.Ico k (2*k),f r := by
      apply Finset.sum_filter_of_ne
      intro r _ hne
      by_contra hn
      exact hne (by
        dsimp only [f]
        rw [sourceShiftCorrelation_empty F X M a L r (by omega),norm_zero])
    rw [hRange,←hFilter,hcard]
    rw [Finset.sum_image hinj.injOn]
    calc
      _ ≤ ∑ r∈S,(1+‖∑ l∈Finset.Ioc (a:ℤ) (Bint ((r:ℝ)/(k:ℝ))),
          (𝐞 ((X*k/M)*(F ((l:ℝ)/M)-F ((l:ℝ)/M+((k:ℝ)/M)*((r:ℝ)/(k:ℝ))))/
            ((k:ℝ)/M)):ℂ)‖) := by
        apply Finset.sum_le_sum
        intro r hr
        have hh := norm_sourceShiftCorrelation_le_difference_Ioc
          F X hM.ne' a L r k hk (Finset.mem_filter.mp hr).2
        dsimp only [Bint]
        rw [hfloor]
        simpa only [Expdb.oscillatory,←mul_div_assoc] using hh
      _ = _ := by rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one]

example
    (F : ℝ → ℝ) (X : ℝ) {M : ℝ} (hM : 0<M)
    (a L k : ℕ) (hk : 0<k) (ha : M≤(a:ℝ)) (hb : ((a+L:ℕ):ℝ)≤2*M) :
    let S := (Finset.Ico k (2*k)).filter (fun r => r≤L)
    let Y := S.image (fun (r:ℕ) => (r:ℝ)/(k:ℝ))
    let Bint := fun y : ℝ => ((a+(L-⌊(k:ℝ)*y⌋₊):ℕ):ℤ)
    Y.card≤k ∧
      (∀ y∈Y, y∈Icc (1:ℝ) 2) ∧
      (∀ y∈Y, ∀ z∈Y, y≠z → 1≤(k:ℝ)*|y-z|) ∧
      ⌈M⌉≤(a:ℤ) ∧ (∀ y∈Y, (a:ℤ)≤Bint y) ∧
      (∀ y∈Y, Bint y≤⌊2*M⌋) ∧
      (∑ j∈Finset.range k,‖sourceShiftCorrelation F X M a L (k+j)‖) ≤
        (Y.card:ℝ)+∑ y∈Y,‖∑ l∈Finset.Ioc (a:ℤ) (Bint y),
          (𝐞 ((X*k/M)*(F ((l:ℝ)/M)-F ((l:ℝ)/M+((k:ℝ)/M)*y))/
            ((k:ℝ)/M)):ℂ)‖ :=
  HuxleyOriginalPhaseScratch.dyadic_shift_actual_family F X (M:=M) hM a L k hk ha hb


#print axioms HuxleyOriginalPhaseScratch.dyadic_shift_actual_family


private theorem upper_endpoint_error_absorption
    {Y M N R : ℝ} (hY : 0≤Y) (hM : 0≤M) (hN : 1≤N)
    (hR : 0<R) (hRN : R≤N) :
    Y≤Y*M/Real.sqrt N+Y*M*R^2/N^2+Y*N*(N/R)^((2:ℝ)/3) := by
  have hNp := zero_lt_one.trans_le hN
  have hratio : 1≤N/R := (one_le_div hR).mpr hRN
  have hpow : 1≤(N/R)^((2:ℝ)/3) := Real.one_le_rpow hratio (by norm_num)
  have hunit : 1≤N*(N/R)^((2:ℝ)/3) := by
    calc
      _ = (1:ℝ)*1 := by norm_num
      _ ≤ _ := mul_le_mul hN hpow zero_le_one hNp.le
  have hh : Y≤Y*N*(N/R)^((2:ℝ)/3) := by
    calc
      _ ≤ Y*(N*(N/R)^((2:ℝ)/3)) := le_mul_of_one_le_right hY hunit
      _ = _ := (mul_assoc _ _ _).symm
  have hfirst : 0≤Y*M/Real.sqrt N+Y*M*R^2/N^2 := by positivity
  exact hh.trans (le_add_of_nonneg_left hfirst)

example
    {Y M N R : ℝ} (hY : 0≤Y) (hM : 0≤M) (hN : 1≤N)
    (hR : 0<R) (hRN : R≤N) :
    Y≤Y*M/Real.sqrt N+Y*M*R^2/N^2+Y*N*(N/R)^((2:ℝ)/3) :=
  HuxleyOriginalPhaseScratch.upper_endpoint_error_absorption (Y:=Y) (M:=M) (N:=N) (R:=R) hY hM hN hR hRN


#print axioms HuxleyOriginalPhaseScratch.upper_endpoint_error_absorption


private theorem approximateModelPhase_enlarged_upper_correlation_moment
    {σ ε : ℝ} (hσ : 0<σ) (hε : 0<ε) :
    ∃ δ η₀ B C : ℝ, 0<δ ∧ 0<η₀ ∧ η₀≤1/8 ∧ 1≤B ∧ 1≤C ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1≤M →
        Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
        ∃ Fext : ℝ → ℝ,
          (∀ (X : ℝ) (a b : ℕ), M≤(a:ℝ) → (b:ℝ)≤2*M →
            ‖Expdb.exponentialSumAt F X M a b-
              Expdb.exponentialSumAt Fext X M a b‖≤6) ∧
          ∀ (X : ℝ) (n N a L k : ℕ) (R : ℝ),
            C≤X*k/M → N=8*n → 2≤N → B≤R →
            0<k → (k:ℝ)/M≤η₀ → (k:ℝ)≤M →
            M≤(a:ℝ) → ((a+L:ℕ):ℝ)≤2*M →
            (X*k/M)*(N:ℝ)*R^2=M^3 →
            B*R≤N → B*(N:ℝ)≤R^2 → B*(N:ℝ)^2≤M →
            B*(N:ℝ)^4≤M*R^3 → B*(N:ℝ)^10≤M^3*R^7 →
            let K := (k:ℝ)
            let E := K*M/Real.sqrt (N:ℝ)+K*M*R^2/(N:ℝ)^2+
              K*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
            let Main := K^11*M^11/((N:ℝ)*R^2)+
              K^11*K*M^11/(N:ℝ)^3+
              K^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
            (∑ j∈Finset.range k,‖sourceShiftCorrelation Fext X M a L (k+j)‖)^12 ≤
              C*(X*k/M)^ε*(E^12+Main) := by
  classical
  obtain ⟨δ,η₀,B,C₀,hδ,hη₀,hηcap,hB,hC₀,hsource⟩ :=
    approximateModelPhase_enlarged_quantitative_upper hσ hε
  let C := (2:ℝ)^12*C₀
  have hCC₀ : C₀≤C := le_mul_of_one_le_left (zero_le_one.trans hC₀) (by norm_num)
  have hC : 1≤C := hC₀.trans hCC₀
  refine ⟨δ,η₀,B,C,hδ,hη₀,hηcap,hB,hC,?_⟩
  intro M F hM hF
  obtain ⟨Fext,hsharp,hupper⟩ := hsource M F hM hF
  refine ⟨Fext,hsharp,?_⟩
  intro X n N a L k R hT hN8 hN2 hR hk hη hKM ha hb hphase hRN hNR hNM
    hFour hTen K E Main
  have hMp := zero_lt_one.trans_le hM
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hN1 : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hRp := zero_lt_one.trans_le (hB.trans hR)
  have hKp : 0<K := by
    change (0:ℝ)<k
    exact_mod_cast hk
  have hT1 : 1≤X*k/M := hC.trans hT
  have hTp := zero_lt_one.trans_le hT1
  let S := (Finset.Ico k (2*k)).filter (fun r => r≤L)
  let Y := S.image (fun (r:ℕ) => (r:ℝ)/(k:ℝ))
  let Bint := fun y : ℝ => ((a+(L-⌊(k:ℝ)*y⌋₊):ℕ):ℤ)
  obtain ⟨hcard,hY,hsep,hA,hAB,hBint,hcorr⟩ :=
    dyadic_shift_actual_family Fext X hMp a L k hk ha hb
  have hY0 : (0:ℝ)≤Y.card := Nat.cast_nonneg _
  have hYK : (Y.card:ℝ)≤K := by
    change (Y.card:ℝ)≤(k:ℝ)
    exact_mod_cast hcard
  let EY := (Y.card:ℝ)*M/Real.sqrt (N:ℝ)+(Y.card:ℝ)*M*R^2/(N:ℝ)^2+
    (Y.card:ℝ)*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
  let MainY := (Y.card:ℝ)^11*M^11/((N:ℝ)*R^2)+
    (Y.card:ℝ)^11*(k:ℝ)*M^11/(N:ℝ)^3+
    (Y.card:ℝ)^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
  have hEY : EY≤E := by
    have hh := upper_radius_error_bound hY0 hYK hMp hNp hRp hRp
      (show (1:ℝ)≤1 from le_rfl) (by rw [one_mul]) (by rw [one_mul])
    simpa only [one_pow,one_mul] using hh
  have hMY : MainY≤Main := by
    have hh := upper_radius_main_bound hY0 hYK hMp hNp hRp hRp
      (show (1:ℝ)≤1 from le_rfl) hKp.le (by rw [one_mul]) (by rw [one_mul])
    simpa only [one_pow,one_mul] using hh
  have hYSigns := upper_expression_nonnegative hY0 hMp.le hNp.le hRp.le hKp.le
  have hSigns := upper_expression_nonnegative hKp.le hMp.le hNp.le hRp.le hKp.le
  have hEY0 : 0≤EY := hYSigns.1
  have hE0 : 0≤E := hSigns.1
  have hMain0 : 0≤Main := hSigns.2
  have hMass0 : 0≤E^12+Main := add_nonneg (pow_nonneg hE0 12) hMain0
  have hMass : EY^12+MainY≤E^12+Main :=
    add_le_add (pow_le_pow_left₀ hEY0 hEY 12) hMY
  let Z := ∑ y∈Y,‖∑ l∈Finset.Ioc (a:ℤ) (Bint y),
    (𝐞 ((X*k/M)*(Fext ((l:ℝ)/M)-Fext ((l:ℝ)/M+((k:ℝ)/M)*y))/
      ((k:ℝ)/M)):ℂ)‖
  have hZ0 : 0≤Z := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hZ : Z^12≤C₀*(X*k/M)^ε*(E^12+Main) := by
    have hu := hupper (X*k/M) Y n N R k ((k:ℝ)/M)
      (hCC₀.trans hT) hN8 hN2 hR (div_pos hKp hMp) hη hKp hKM hY hsep hphase
      hRN hNR hNM hFour hTen (fun _ => (a:ℤ)) Bint (fun _ _ => hA) hAB hBint
    exact hu.trans (mul_le_mul_of_nonneg_left hMass
      (mul_nonneg (zero_le_one.trans hC₀) (Real.rpow_nonneg hTp.le ε)))
  have hQ : 1≤C₀*(X*k/M)^ε := by
    calc
      _ = (1:ℝ)*1 := by norm_num
      _ ≤ _ := mul_le_mul hC₀ (Real.one_le_rpow hT1 hε.le)
        zero_le_one (zero_le_one.trans hC₀)
  have hRleN : R≤(N:ℝ) :=
    (le_mul_of_one_le_left hRp.le hB).trans hRN
  have hKE : K≤E := upper_endpoint_error_absorption hKp.le hMp.le hN1 hRp hRleN
  have hKpow : K^12≤C₀*(X*k/M)^ε*(E^12+Main) :=
    ((pow_le_pow_left₀ hKp.le hKE 12).trans (le_add_of_nonneg_right hMain0)).trans
      (le_mul_of_one_le_left hMass0 hQ)
  have hCorr : (∑ j∈Finset.range k,‖sourceShiftCorrelation Fext X M a L (k+j)‖)≤K+Z :=
    hcorr.trans (add_le_add hYK le_rfl)
  calc
    _ ≤ (K+Z)^12 :=
      pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hCorr 12
    _ ≤ (2:ℝ)^11*(K^12+Z^12) := add_pow_le hKp.le hZ0 12
    _ ≤ (2:ℝ)^11*(C₀*(X*k/M)^ε*(E^12+Main)+C₀*(X*k/M)^ε*(E^12+Main)) :=
      mul_le_mul_of_nonneg_left (add_le_add hKpow hZ) (by norm_num)
    _ = _ := by
      rw [←two_mul]
      dsimp only [C]
      rw [show (2:ℝ)^12=2^11*2 from pow_succ 2 11]
      ac_rfl

example
    {σ ε : ℝ} (hσ : 0<σ) (hε : 0<ε) :
    ∃ δ η₀ B C : ℝ, 0<δ ∧ 0<η₀ ∧ η₀≤1/8 ∧ 1≤B ∧ 1≤C ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1≤M →
        Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
        ∃ Fext : ℝ → ℝ,
          (∀ (X : ℝ) (a b : ℕ), M≤(a:ℝ) → (b:ℝ)≤2*M →
            ‖Expdb.exponentialSumAt F X M a b-
              Expdb.exponentialSumAt Fext X M a b‖≤6) ∧
          ∀ (X : ℝ) (n N a L k : ℕ) (R : ℝ),
            C≤X*k/M → N=8*n → 2≤N → B≤R →
            0<k → (k:ℝ)/M≤η₀ → (k:ℝ)≤M →
            M≤(a:ℝ) → ((a+L:ℕ):ℝ)≤2*M →
            (X*k/M)*(N:ℝ)*R^2=M^3 →
            B*R≤N → B*(N:ℝ)≤R^2 → B*(N:ℝ)^2≤M →
            B*(N:ℝ)^4≤M*R^3 → B*(N:ℝ)^10≤M^3*R^7 →
            let K := (k:ℝ)
            let E := K*M/Real.sqrt (N:ℝ)+K*M*R^2/(N:ℝ)^2+
              K*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
            let Main := K^11*M^11/((N:ℝ)*R^2)+
              K^11*K*M^11/(N:ℝ)^3+
              K^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
            (∑ j∈Finset.range k,‖sourceShiftCorrelation Fext X M a L (k+j)‖)^12 ≤
              C*(X*k/M)^ε*(E^12+Main) :=
  HuxleyOriginalPhaseScratch.approximateModelPhase_enlarged_upper_correlation_moment (σ:=σ) (ε:=ε) hσ hε


#print axioms HuxleyOriginalPhaseScratch.approximateModelPhase_enlarged_upper_correlation_moment


private theorem upper_correlation_integer_moments
    {X M N K R : ℝ} (hX : 0<X) (hM : 0<M) (hN : 0<N) (hK : 0<K) (hR : 0<R)
    (hscale : (X*K/M)*N*R^2=M^3) :
    (K*M/Real.sqrt N)^36=K^36*M^36/N^18 ∧
    (K*M*R^2/N^2)^36=M^180/(X^36*N^108) ∧
    (K*N*(N/R)^((2:ℝ)/3))^36=X^12*K^48*N^72/M^48 ∧
    (K^11*M^11/(N*R^2))^3=X^3*K^36*M^21 ∧
    (K^11*K*M^11/N^3)^3=K^36*M^33/N^9 ∧
    (K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))^3=
      X^2*K^38*M^28/N^12 := by
  have hR2 : R^2=M^4/(X*K*N) := by
    apply (eq_div_iff (mul_ne_zero (mul_ne_zero hX.ne' hK.ne') hN.ne')).mpr
    have hs := hscale
    field_simp at hs
    nlinarith only [hs]
  have hCubic : K*M*R^2/N^2=M^5/(X*N^3) := by
    rw [hR2]
    field_simp
  have hTypeOne : K^11*M^11/(N*R^2)=X*K^12*M^7 := by
    rw [hR2]
    field_simp
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · have hsqrt : (Real.sqrt N)^36=N^18 := by
      calc
        _ = ((Real.sqrt N)^2)^18 := by rw [←pow_mul]
        _ = N^18 := by rw [Real.sq_sqrt hN.le]
    rw [div_pow,mul_pow,hsqrt]
  · rw [hCubic]
    simp only [div_pow,mul_pow,←pow_mul]
  · rw [mul_pow,mul_pow,←Real.rpow_mul_natCast (div_nonneg hN.le hR.le),
      show ((2:ℝ)/3)*((36:ℕ):ℝ)=((24:ℕ):ℝ) by norm_num,
      Real.rpow_natCast,div_pow]
    rw [show R^24=(R^2)^12 by rw [←pow_mul],hR2]
    field_simp
  · rw [hTypeOne]
    simp only [mul_pow,←pow_mul]
  · simp only [mul_pow,div_pow,←pow_mul]
    ring
  · rw [mul_pow,←Real.rpow_mul_natCast (div_nonneg hR.le hN.le),
      show ((2:ℝ)/3)*((3:ℕ):ℝ)=((2:ℕ):ℝ) by norm_num,
      Real.rpow_natCast,div_pow,
      hR2]
    field_simp
    nlinarith only [(eq_div_iff (mul_ne_zero (mul_ne_zero hX.ne' hK.ne') hN.ne')).mp hR2]

example
    {X M N K R : ℝ} (hX : 0<X) (hM : 0<M) (hN : 0<N) (hK : 0<K) (hR : 0<R)
    (hscale : (X*K/M)*N*R^2=M^3) :
    (K*M/Real.sqrt N)^36=K^36*M^36/N^18 ∧
    (K*M*R^2/N^2)^36=M^180/(X^36*N^108) ∧
    (K*N*(N/R)^((2:ℝ)/3))^36=X^12*K^48*N^72/M^48 ∧
    (K^11*M^11/(N*R^2))^3=X^3*K^36*M^21 ∧
    (K^11*K*M^11/N^3)^3=K^36*M^33/N^9 ∧
    (K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))^3=
      X^2*K^38*M^28/N^12 :=
  HuxleyOriginalPhaseScratch.upper_correlation_integer_moments (X:=X) (M:=M) (N:=N) (K:=K) (R:=R) hX hM hN hK hR hscale


#print axioms HuxleyOriginalPhaseScratch.upper_correlation_integer_moments


private theorem upper_integer_moments_all_shifts
    {X M N K H R : ℝ}
    (hX : 0<X) (hM : 0<M) (hN : 0<N) (hK : 0<K) (hH : 0<H) (hR : 0<R)
    (hKH : K≤H) (hscale : (X*K/M)*N*R^2=M^3) :
    (M/H)^36*(K*M/Real.sqrt N)^36≤M^72/N^18 ∧
    (M/H)^36*(K*M*R^2/N^2)^36≤M^216/(H^36*X^36*N^108) ∧
    (M/H)^36*(K*N*(N/R)^((2:ℝ)/3))^36≤X^12*H^12*N^72/M^12 ∧
    (M/H)^36*(K^11*M^11/(N*R^2))^3≤X^3*M^57 ∧
    (M/H)^36*(K^11*K*M^11/N^3)^3≤M^69/N^9 ∧
    (M/H)^36*(K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))^3≤
      X^2*H^2*M^64/N^12 := by
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ :=
    upper_correlation_integer_moments hX hM hN hK hR hscale
  rw [h₁,h₂,h₃,h₄,h₅,h₆]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · calc
      _ ≤ (M/H)^36*(H^36*M^36/N^18) := by gcongr
      _ = _ := by field_simp
  · exact le_of_eq (by field_simp)
  · calc
      _ ≤ (M/H)^36*(X^12*H^48*N^72/M^48) := by gcongr
      _ = _ := by field_simp
  · calc
      _ ≤ (M/H)^36*(X^3*H^36*M^21) := by gcongr
      _ = _ := by field_simp
  · calc
      _ ≤ (M/H)^36*(H^36*M^33/N^9) := by gcongr
      _ = _ := by field_simp
  · calc
      _ ≤ (M/H)^36*(X^2*H^38*M^28/N^12) := by gcongr
      _ = _ := by field_simp

private theorem three_term_power_bound
    {a b c : ℝ} (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (n : ℕ) :
    (a+b+c)^n≤(2:ℝ)^(2*n)*(a^n+b^n+c^n) := by
  let D := (2:ℝ)^(n-1)
  have hD : 1≤D := one_le_pow₀ (by norm_num)
  have hD0 := zero_le_one.trans hD
  have hDpow : D^2≤(2:ℝ)^(2*n) := by
    dsimp only [D]
    rw [←pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    _ ≤ D*((a+b)^n+c^n) := add_pow_le (add_nonneg ha hb) hc n
    _ ≤ D*(D*(a^n+b^n)+D*c^n) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (add_pow_le ha hb n)
          (le_mul_of_one_le_left (pow_nonneg hc n) hD)) hD0
    _ = D^2*(a^n+b^n+c^n) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hDpow
      (add_nonneg (add_nonneg (pow_nonneg ha n) (pow_nonneg hb n)) (pow_nonneg hc n))

example
    {X M N K H R : ℝ}
    (hX : 0<X) (hM : 0<M) (hN : 0<N) (hK : 0<K) (hH : 0<H) (hR : 0<R)
    (hKH : K≤H) (hscale : (X*K/M)*N*R^2=M^3) :
    (M/H)^36*(K*M/Real.sqrt N)^36≤M^72/N^18 ∧
    (M/H)^36*(K*M*R^2/N^2)^36≤M^216/(H^36*X^36*N^108) ∧
    (M/H)^36*(K*N*(N/R)^((2:ℝ)/3))^36≤X^12*H^12*N^72/M^12 ∧
    (M/H)^36*(K^11*M^11/(N*R^2))^3≤X^3*M^57 ∧
    (M/H)^36*(K^11*K*M^11/N^3)^3≤M^69/N^9 ∧
    (M/H)^36*(K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))^3≤
      X^2*H^2*M^64/N^12 :=
  HuxleyOriginalPhaseScratch.upper_integer_moments_all_shifts (X:=X) (M:=M) (N:=N) (K:=K) (H:=H) (R:=R) hX hM hN hK hH hR hKH hscale

example
    {a b c : ℝ} (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (n : ℕ) :
    (a+b+c)^n≤(2:ℝ)^(2*n)*(a^n+b^n+c^n) :=
  HuxleyOriginalPhaseScratch.three_term_power_bound (a:=a) (b:=b) (c:=c) ha hb hc n


#print axioms HuxleyOriginalPhaseScratch.upper_integer_moments_all_shifts
#print axioms HuxleyOriginalPhaseScratch.three_term_power_bound


private theorem weighted_upper_integer_moment_bound
    {X M N K H R : ℝ}
    (hX : 0<X) (hM : 0<M) (hN : 0<N) (hK : 0<K) (hH : 0<H) (hR : 0<R)
    (hKH : K≤H) (hscale : (X*K/M)*N*R^2=M^3) :
    let E := K*M/Real.sqrt N+K*M*R^2/N^2+K*N*(N/R)^((2:ℝ)/3)
    let Main := K^11*M^11/(N*R^2)+K^11*K*M^11/N^3+
      K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)
    (M/H)^36*(E^36+Main^3)≤(2:ℝ)^72*
      ((M^72/N^18+M^216/(H^36*X^36*N^108)+X^12*H^12*N^72/M^12)+
        (X^3*M^57+M^69/N^9+X^2*H^2*M^64/N^12)) := by
  intro E Main
  let e₁ := K*M/Real.sqrt N
  let e₂ := K*M*R^2/N^2
  let e₃ := K*N*(N/R)^((2:ℝ)/3)
  let a₁ := K^11*M^11/(N*R^2)
  let a₂ := K^11*K*M^11/N^3
  let a₃ := K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)
  have he₁ : 0≤e₁ := by dsimp only [e₁]; positivity
  have he₂ : 0≤e₂ := by dsimp only [e₂]; positivity
  have he₃ : 0≤e₃ := by dsimp only [e₃]; positivity
  have ha₁ : 0≤a₁ := by dsimp only [a₁]; positivity
  have ha₂ : 0≤a₂ := by dsimp only [a₂]; positivity
  have ha₃ : 0≤a₃ := by dsimp only [a₃]; positivity
  have hE : E^36≤(2:ℝ)^72*(e₁^36+e₂^36+e₃^36) :=
    three_term_power_bound he₁ he₂ he₃ 36
  have hMain : Main^3≤(2:ℝ)^72*(a₁^3+a₂^3+a₃^3) :=
    (three_term_power_bound ha₁ ha₂ ha₃ 3).trans
      (mul_le_mul_of_nonneg_right (by norm_num)
        (add_nonneg (add_nonneg (pow_nonneg ha₁ 3) (pow_nonneg ha₂ 3)) (pow_nonneg ha₃ 3)))
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ :=
    upper_integer_moments_all_shifts hX hM hN hK hH hR hKH hscale
  have hW : 0≤(M/H)^36 := pow_nonneg (div_nonneg hM.le hH.le) 36
  calc
    _ ≤ (M/H)^36*((2:ℝ)^72*(e₁^36+e₂^36+e₃^36)+
        (2:ℝ)^72*(a₁^3+a₂^3+a₃^3)) :=
      mul_le_mul_of_nonneg_left (add_le_add hE hMain) hW
    _ = (2:ℝ)^72*(((M/H)^36*e₁^36+(M/H)^36*e₂^36+(M/H)^36*e₃^36)+
        ((M/H)^36*a₁^3+(M/H)^36*a₂^3+(M/H)^36*a₃^3)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (add_le_add h₁ h₂) h₃)
        (add_le_add (add_le_add h₄ h₅) h₆)) (by norm_num)

example
    {X M N K H R : ℝ}
    (hX : 0<X) (hM : 0<M) (hN : 0<N) (hK : 0<K) (hH : 0<H) (hR : 0<R)
    (hKH : K≤H) (hscale : (X*K/M)*N*R^2=M^3) :
    let E := K*M/Real.sqrt N+K*M*R^2/N^2+K*N*(N/R)^((2:ℝ)/3)
    let Main := K^11*M^11/(N*R^2)+K^11*K*M^11/N^3+
      K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)
    (M/H)^36*(E^36+Main^3)≤(2:ℝ)^72*
      ((M^72/N^18+M^216/(H^36*X^36*N^108)+X^12*H^12*N^72/M^12)+
        (X^3*M^57+M^69/N^9+X^2*H^2*M^64/N^12)) :=
  HuxleyOriginalPhaseScratch.weighted_upper_integer_moment_bound (X:=X) (M:=M) (N:=N) (K:=K) (H:=H) (R:=R) hX hM hN hK hH hR hKH hscale


#print axioms HuxleyOriginalPhaseScratch.weighted_upper_integer_moment_bound


private theorem upper_weyl_seventy_second_bound
    {S Z A C L X M N K H R ε : ℝ}
    (hS : 0≤S) (hZ : 0≤Z) (hA : 0≤A) (hC : 1≤C) (hL : 0≤L)
    (hX : 1≤X) (hM : 0<M) (hN : 0<N) (hK : 0<K) (hH : 0<H) (hR : 0<R)
    (hε : 0≤ε) (hKH : K≤H) (hscale : (X*K/M)*N*R^2=M^3) :
    let E := K*M/Real.sqrt N+K*M*R^2/N^2+K*N*(N/R)^((2:ℝ)/3)
    let Main := K^11*M^11/(N*R^2)+K^11*K*M^11/N^3+
      K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)
    Z^12≤C*X^ε*(E^12+Main) →
    S^24≤A*L^12*((M^2/H)^12+(M/H)^12*Z^12) →
    S^72≤(2:ℝ)^76*A^3*C^3*L^36*X^(3*ε)*
      (M^72/H^36+
        ((M^72/N^18+M^216/(H^36*X^36*N^108)+X^12*H^12*N^72/M^12)+
          (X^3*M^57+M^69/N^9+X^2*H^2*M^64/N^12))) := by
  intro E Main hCorr hWeyl
  have hXp := zero_lt_one.trans_le hX
  have hC0 := zero_le_one.trans hC
  have hSigns := upper_expression_nonnegative hK.le hM.le hN.le hR.le hK.le
  have hE0 : 0≤E := hSigns.1
  have hMain0 : 0≤Main := hSigns.2
  let V := (M^72/N^18+M^216/(H^36*X^36*N^108)+X^12*H^12*N^72/M^12)+
    (X^3*M^57+M^69/N^9+X^2*H^2*M^64/N^12)
  have hV0 : 0≤V := by dsimp only [V]; positivity
  have hW0 : 0≤(M/H)^36 := pow_nonneg (div_nonneg hM.le hH.le) 36
  have hTpow : 0≤X^(3*ε) := Real.rpow_nonneg hXp.le _
  have hTpowOne : 1≤X^(3*ε) := Real.one_le_rpow hX (mul_nonneg (by norm_num) hε)
  have hXpCube : (X^ε)^3=X^(3*ε) := by
    rw [←Real.rpow_mul_natCast hXp.le]
    congr 1
    norm_num [mul_comm]
  have hCube : S^72≤A^3*L^36*((M^2/H)^12+(M/H)^12*Z^12)^3 := by
    simpa only [mul_pow,←pow_mul] using
      pow_le_pow_left₀ (pow_nonneg hS 24) hWeyl 3
  have hAdd : ((M^2/H)^12+(M/H)^12*Z^12)^3≤
      4*(M^72/H^36+(M/H)^36*Z^36) := by
    simpa only [div_pow,mul_pow,←pow_mul,show (2:ℝ)^(3-1)=4 by norm_num] using
      add_pow_le (by positivity : 0≤(M^2/H)^12)
        (by positivity : 0≤(M/H)^12*Z^12) 3
  have hSmain : S^72≤4*A^3*L^36*(M^72/H^36+(M/H)^36*Z^36) := by
    calc
      _ ≤ A^3*L^36*((M^2/H)^12+(M/H)^12*Z^12)^3 := hCube
      _ ≤ A^3*L^36*(4*(M^72/H^36+(M/H)^36*Z^36)) :=
        mul_le_mul_of_nonneg_left hAdd (mul_nonneg (pow_nonneg hA 3) (pow_nonneg hL 36))
      _ = _ := by ac_rfl
  have hZCube : Z^36≤C^3*X^(3*ε)*(E^12+Main)^3 := by
    have hh := pow_le_pow_left₀ (pow_nonneg hZ 12) hCorr 3
    simpa only [mul_pow,←pow_mul,hXpCube] using hh
  have hEM : (E^12+Main)^3≤4*(E^36+Main^3) := by
    simpa only [←pow_mul,show (2:ℝ)^(3-1)=4 by norm_num] using
      add_pow_le (pow_nonneg hE0 12) hMain0 3
  have hZMoment : Z^36≤4*C^3*X^(3*ε)*(E^36+Main^3) := by
    calc
      _ ≤ C^3*X^(3*ε)*(E^12+Main)^3 := hZCube
      _ ≤ C^3*X^(3*ε)*(4*(E^36+Main^3)) :=
        mul_le_mul_of_nonneg_left hEM (mul_nonneg (pow_nonneg hC0 3) hTpow)
      _ = _ := by ac_rfl
  have hWeighted : (M/H)^36*(E^36+Main^3)≤(2:ℝ)^72*V :=
    weighted_upper_integer_moment_bound hXp hM hN hK hH hR hKH hscale
  let Q := (2:ℝ)^74*C^3*X^(3*ε)
  have hQ : 1≤Q := by
    calc
      _ ≤ C^3 := one_le_pow₀ hC
      _ ≤ C^3*X^(3*ε) := le_mul_of_one_le_right (pow_nonneg hC0 3) hTpowOne
      _ ≤ (2:ℝ)^74*(C^3*X^(3*ε)) :=
        le_mul_of_one_le_left (mul_nonneg (pow_nonneg hC0 3) hTpow) (by norm_num)
      _ = Q := (mul_assoc _ _ _).symm
  have hScaledZ : (M/H)^36*Z^36≤Q*V := by
    calc
      _ ≤ (M/H)^36*(4*C^3*X^(3*ε)*(E^36+Main^3)) :=
        mul_le_mul_of_nonneg_left hZMoment hW0
      _ = (4*C^3*X^(3*ε))*((M/H)^36*(E^36+Main^3)) := by ac_rfl
      _ ≤ (4*C^3*X^(3*ε))*((2:ℝ)^72*V) :=
        mul_le_mul_of_nonneg_left hWeighted
          (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hC0 3)) hTpow)
      _ = Q*V := by
        dsimp only [Q]
        rw [show (2:ℝ)^74=4*2^72 by norm_num]
        ac_rfl
  have hDiag : M^72/H^36≤Q*(M^72/H^36) :=
    le_mul_of_one_le_left (by positivity) hQ
  calc
    _ ≤ 4*A^3*L^36*(M^72/H^36+(M/H)^36*Z^36) := hSmain
    _ ≤ 4*A^3*L^36*(Q*(M^72/H^36)+Q*V) :=
      mul_le_mul_of_nonneg_left (add_le_add hDiag hScaledZ)
        (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hA 3)) (pow_nonneg hL 36))
    _ = _ := by
      rw [←mul_add]
      dsimp only [Q,V]
      rw [show (2:ℝ)^76=4*2^74 by norm_num]
      ring

example
    {S Z A C L X M N K H R ε : ℝ}
    (hS : 0≤S) (hZ : 0≤Z) (hA : 0≤A) (hC : 1≤C) (hL : 0≤L)
    (hX : 1≤X) (hM : 0<M) (hN : 0<N) (hK : 0<K) (hH : 0<H) (hR : 0<R)
    (hε : 0≤ε) (hKH : K≤H) (hscale : (X*K/M)*N*R^2=M^3) :
    let E := K*M/Real.sqrt N+K*M*R^2/N^2+K*N*(N/R)^((2:ℝ)/3)
    let Main := K^11*M^11/(N*R^2)+K^11*K*M^11/N^3+
      K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)
    Z^12≤C*X^ε*(E^12+Main) →
    S^24≤A*L^12*((M^2/H)^12+(M/H)^12*Z^12) →
    S^72≤(2:ℝ)^76*A^3*C^3*L^36*X^(3*ε)*
      (M^72/H^36+
        ((M^72/N^18+M^216/(H^36*X^36*N^108)+X^12*H^12*N^72/M^12)+
          (X^3*M^57+M^69/N^9+X^2*H^2*M^64/N^12))) :=
  HuxleyOriginalPhaseScratch.upper_weyl_seventy_second_bound (S:=S) (Z:=Z) (A:=A) (C:=C) (L:=L) (X:=X) (M:=M) (N:=N) (K:=K) (H:=H) (R:=R) (ε:=ε) hS hZ hA hC hL hX hM hN hK hH hR hε hKH hscale


#print axioms HuxleyOriginalPhaseScratch.upper_weyl_seventy_second_bound


private theorem upper_all_shift_polynomial_budgets
    {X M N K H R B : ℝ}
    (hX : 0<X) (hM : 0<M) (hN : 0<N) (hK : 1≤K) (hR : 0<R)
    (hB : 1≤B) (hKH : K≤H) (hBN : B≤N)
    (hscale : (X*K/M)*N*R^2=M^3)
    (hRN : B^2*M^4≤X*N^3) (hNR : B*X*H*N^2≤M^4)
    (hNM : B*N^2≤M)
    (hFour : B^2*X^3*H^3*N^11≤M^14)
    (hTen : B^2*X^7*H^7*N^27≤M^34) :
    B≤R ∧ B*R≤N ∧ B*N≤R^2 ∧ B*N^2≤M ∧
      B*N^4≤M*R^3 ∧ B*N^10≤M^3*R^7 := by
  have hKp := zero_lt_one.trans_le hK
  have hHp := hKp.trans_le hKH
  have hBp := zero_lt_one.trans_le hB
  have hDen : 0<X*K*N := mul_pos (mul_pos hX hKp) hN
  have hR2 : R^2=M^4/(X*K*N) := by
    apply (eq_div_iff hDen.ne').mpr
    have hs := hscale
    field_simp at hs
    nlinarith only [hs]
  have hNR' : B*N≤R^2 := by
    rw [hR2]
    apply (le_div_iff₀ hDen).mpr
    calc
      _ = B*X*K*N^2 := by ring
      _ ≤ B*X*H*N^2 := by gcongr
      _ ≤ M^4 := hNR
  refine ⟨?_,?_,hNR',hNM,?_,?_⟩
  · apply (sq_le_sq₀ hBp.le hR.le).mp
    calc
      B^2 = B*B := pow_two B
      _ ≤ B*N := mul_le_mul_of_nonneg_left hBN hBp.le
      _ ≤ R^2 := hNR'
  · apply (sq_le_sq₀ (mul_nonneg hBp.le hR.le) hN.le).mp
    rw [mul_pow,hR2,←mul_div_assoc]
    apply (div_le_iff₀ hDen).mpr
    calc
      _ ≤ X*N^3 := hRN
      _ ≤ K*(X*N^3) := le_mul_of_one_le_left (by positivity) hK
      _ = _ := by ring
  · apply (sq_le_sq₀ (mul_nonneg hBp.le (pow_nonneg hN.le 4))
      (mul_nonneg hM.le (pow_nonneg hR.le 3))).mp
    simp only [mul_pow,←pow_mul]
    rw [show R^6=(R^2)^3 by rw [←pow_mul],hR2,div_pow,←mul_div_assoc]
    apply (le_div_iff₀ (pow_pos hDen 3)).mpr
    calc
      _ = B^2*X^3*K^3*N^11 := by ring
      _ ≤ B^2*X^3*H^3*N^11 := by gcongr
      _ ≤ M^14 := hFour
      _ = _ := by ring
  · apply (sq_le_sq₀ (mul_nonneg hBp.le (pow_nonneg hN.le 10))
      (mul_nonneg (pow_nonneg hM.le 3) (pow_nonneg hR.le 7))).mp
    simp only [mul_pow,←pow_mul]
    rw [show R^14=(R^2)^7 by rw [←pow_mul],hR2,div_pow,←mul_div_assoc]
    apply (le_div_iff₀ (pow_pos hDen 7)).mpr
    calc
      _ = B^2*X^7*K^7*N^27 := by ring
      _ ≤ B^2*X^7*H^7*N^27 := by gcongr
      _ ≤ M^34 := hTen
      _ = _ := by ring

example
    {X M N K H R B : ℝ}
    (hX : 0<X) (hM : 0<M) (hN : 0<N) (hK : 1≤K) (hR : 0<R)
    (hB : 1≤B) (hKH : K≤H) (hBN : B≤N)
    (hscale : (X*K/M)*N*R^2=M^3)
    (hRN : B^2*M^4≤X*N^3) (hNR : B*X*H*N^2≤M^4)
    (hNM : B*N^2≤M)
    (hFour : B^2*X^3*H^3*N^11≤M^14)
    (hTen : B^2*X^7*H^7*N^27≤M^34) :
    B≤R ∧ B*R≤N ∧ B*N≤R^2 ∧ B*N^2≤M ∧
      B*N^4≤M*R^3 ∧ B*N^10≤M^3*R^7 :=
  HuxleyOriginalPhaseScratch.upper_all_shift_polynomial_budgets (X:=X) (M:=M) (N:=N) (K:=K) (H:=H) (R:=R) (B:=B) hX hM hN hK hR hB hKH hBN hscale hRN hNR hNM hFour hTen


#print axioms HuxleyOriginalPhaseScratch.upper_all_shift_polynomial_budgets


private theorem sharp_extension_power_bound
    {u v : ℂ} {D W P E : ℝ} (hD : 0≤D) (hW : 1≤W) (hP : 0≤P) (hE : 0≤E)
    (hsharp : ‖u-v‖≤E) (hv : ‖v‖^72≤D*W*P) :
    ‖u‖^72≤(2:ℝ)^71*(D+E^72)*W*(1+P) := by
  have hW0 := zero_le_one.trans hW
  have hu : ‖u‖≤‖v‖+E := by
    calc
      _ = ‖v+(u-v)‖ := by congr 1; abel
      _ ≤ ‖v‖+‖u-v‖ := norm_add_le _ _
      _ ≤ _ := add_le_add le_rfl hsharp
  have hErr : E^72≤E^72*W :=
    le_mul_of_one_le_right (pow_nonneg hE 72) hW
  have hFold : D*W*P+E^72*W≤(D+E^72)*W*(1+P) := by
    nlinarith only [mul_nonneg hD hW0,
      mul_nonneg (mul_nonneg (pow_nonneg hE 72) hW0) hP]
  calc
    _ ≤ (‖v‖+E)^72 := pow_le_pow_left₀ (norm_nonneg _) hu 72
    _ ≤ (2:ℝ)^71*(‖v‖^72+E^72) := add_pow_le (norm_nonneg _) hE 72
    _ ≤ (2:ℝ)^71*(D*W*P+E^72*W) :=
      mul_le_mul_of_nonneg_left (add_le_add hv hErr) (by norm_num)
    _ ≤ (2:ℝ)^71*((D+E^72)*W*(1+P)) :=
      mul_le_mul_of_nonneg_left hFold (by norm_num)
    _ = _ := by ac_rfl

example
    {u v : ℂ} {D W P E : ℝ} (hD : 0≤D) (hW : 1≤W) (hP : 0≤P) (hE : 0≤E)
    (hsharp : ‖u-v‖≤E) (hv : ‖v‖^72≤D*W*P) :
    ‖u‖^72≤(2:ℝ)^71*(D+E^72)*W*(1+P) :=
  HuxleyOriginalPhaseScratch.sharp_extension_power_bound (u:=u) (v:=v) (D:=D) (W:=W) (P:=P) (E:=E) hD hW hP hE hsharp hv


#print axioms HuxleyOriginalPhaseScratch.sharp_extension_power_bound


private theorem approximateModelPhase_upper_original_seventy_second
    {σ ε : ℝ} (hσ : 0<σ) (hε : 0<ε) :
    ∃ δ η₀ B C : ℝ, 0<δ ∧ 0<η₀ ∧ η₀≤1/8 ∧ 1≤B ∧ 1≤C ∧
      ∀ (X M : ℝ) (F : ℝ → ℝ) (n N H a L : ℕ),
        1≤X → 1≤M → Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
        N=8*n → 2≤N → 2≤H → (H:ℝ)≤η₀*M → C≤X/M →
        B≤N → B^2*M^4≤X*(N:ℝ)^3 → B*X*(H:ℝ)*(N:ℝ)^2≤M^4 →
        B*(N:ℝ)^2≤M → B^2*X^3*(H:ℝ)^3*(N:ℝ)^11≤M^14 →
        B^2*X^7*(H:ℝ)^7*(N:ℝ)^27≤M^34 →
        M≤(a:ℝ) → ((a+L:ℕ):ℝ)≤2*M →
        ‖Expdb.exponentialSumAt F X M a (a+L)‖^72 ≤
          C*(1+(Nat.clog 2 H:ℝ))^36*X^(3*ε)*
            (1+(M^72/(H:ℝ)^36+
              ((M^72/(N:ℝ)^18+M^216/((H:ℝ)^36*X^36*(N:ℝ)^108)+
                  X^12*(H:ℝ)^12*(N:ℝ)^72/M^12)+
                (X^3*M^57+M^69/(N:ℝ)^9+X^2*(H:ℝ)^2*M^64/(N:ℝ)^12)))) := by
  classical
  obtain ⟨δ,η₀,B,C₀,hδ,hη₀,hηcap,hB,hC₀,hsource⟩ :=
    approximateModelPhase_enlarged_upper_correlation_moment hσ hε
  let A₀ := (18:ℝ)^12*(2:ℝ)^11
  have hA₀ : 0≤A₀ := by dsimp only [A₀]; norm_num
  let D := (2:ℝ)^76*A₀^3*C₀^3
  have hD : 0≤D := mul_nonneg
    (mul_nonneg (by norm_num) (pow_nonneg hA₀ 3)) (pow_nonneg (zero_le_one.trans hC₀) 3)
  let C := max C₀ ((2:ℝ)^71*(D+6^72))
  have hCC₀ : C₀≤C := le_max_left _ _
  have hCoeff : (2:ℝ)^71*(D+6^72)≤C := le_max_right _ _
  have hC : 1≤C := hC₀.trans hCC₀
  refine ⟨δ,η₀,B,C,hδ,hη₀,hηcap,hB,hC,?_⟩
  intro X M F n N H a L hX hM hF hN8 hN2 hH2 hHeta hThreshold
    hBN hRN hNR hNM hFour hTen ha hb
  have hXp := zero_lt_one.trans_le hX
  have hMp := zero_lt_one.trans_le hM
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hHp : (0:ℝ)<H := by exact_mod_cast (show 0<H by omega)
  have hHM : (H:ℝ)≤M := by
    calc
      _ ≤ η₀*M := hHeta
      _ ≤ (1:ℝ)*M := mul_le_mul_of_nonneg_right
        (hηcap.trans (by norm_num : (1:ℝ)/8≤1)) hMp.le
      _ = M := one_mul M
  have hLM : (L:ℝ)+1≤2*M := by
    have hb' : (a:ℝ)+(L:ℝ)≤2*M := by simpa only [Nat.cast_add] using hb
    linarith only [hb',ha,hM]
  obtain ⟨Fext,hsharp,hcorr⟩ := hsource M F hM hF
  obtain ⟨k,hk,hkH,hweyl⟩ := exists_source_dyadic_twenty_fourth_power
    Fext X M a L H hMp hH2 hHM hLM
  have hKp : (0:ℝ)<k := by exact_mod_cast hk
  have hK1 : (1:ℝ)≤k := by exact_mod_cast (show 1≤k by omega)
  have hKH : (k:ℝ)≤H := by exact_mod_cast (show k≤H by omega)
  have hKM : (k:ℝ)≤M := hKH.trans hHM
  let R := Real.sqrt (M^4/(X*(k:ℝ)*(N:ℝ)))
  have hRadicand : 0<M^4/(X*(k:ℝ)*(N:ℝ)) :=
    div_pos (pow_pos hMp 4) (mul_pos (mul_pos hXp hKp) hNp)
  have hRp : 0<R := Real.sqrt_pos.mpr hRadicand
  have hR2 : R^2=M^4/(X*(k:ℝ)*(N:ℝ)) := Real.sq_sqrt hRadicand.le
  have hphase : (X*k/M)*(N:ℝ)*R^2=M^3 := by
    rw [hR2]
    field_simp
  obtain ⟨hBR,hRNN,hNRR,hNMM,hFourR,hTenR⟩ :=
    upper_all_shift_polynomial_budgets hXp hMp hNp hK1 hRp hB hKH hBN
      hphase hRN hNR hNM hFour hTen
  have hTbase : C₀≤X*k/M := by
    calc
      _ ≤ X/M := hCC₀.trans hThreshold
      _ ≤ (X/M)*(k:ℝ) := le_mul_of_one_le_right (div_nonneg hXp.le hMp.le) hK1
      _ = _ := by ring
  have hTbasePos := zero_lt_one.trans_le (hC₀.trans hTbase)
  have hTbaseUpper : X*k/M≤X :=
    (div_le_iff₀ hMp).mpr (mul_le_mul_of_nonneg_left hKM hXp.le)
  have hEtaK : (k:ℝ)/M≤η₀ := (div_le_iff₀ hMp).mpr (hKH.trans hHeta)
  let E := (k:ℝ)*M/Real.sqrt (N:ℝ)+(k:ℝ)*M*R^2/(N:ℝ)^2+
    (k:ℝ)*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
  let Main := (k:ℝ)^11*M^11/((N:ℝ)*R^2)+(k:ℝ)^11*(k:ℝ)*M^11/(N:ℝ)^3+
    (k:ℝ)^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
  let Z := ∑ j∈Finset.range k,‖sourceShiftCorrelation Fext X M a L (k+j)‖
  have hZ0 : 0≤Z := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hZbase : Z^12≤C₀*(X*k/M)^ε*(E^12+Main) :=
    hcorr X n N a L k R hTbase hN8 hN2 hBR hk hEtaK hKM ha hb hphase
      hRNN hNRR hNMM hFourR hTenR
  have hSigns := upper_expression_nonnegative hKp.le hMp.le hNp.le hRp.le hKp.le
  have hE0 : 0≤E := hSigns.1
  have hMain0 : 0≤Main := hSigns.2
  have hZ : Z^12≤C₀*X^ε*(E^12+Main) :=
    hZbase.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hTbasePos.le hTbaseUpper hε.le)
        (zero_le_one.trans hC₀)) (add_nonneg (pow_nonneg hE0 12) hMain0))
  let Poly := M^72/(H:ℝ)^36+
    ((M^72/(N:ℝ)^18+M^216/((H:ℝ)^36*X^36*(N:ℝ)^108)+
        X^12*(H:ℝ)^12*(N:ℝ)^72/M^12)+
      (X^3*M^57+M^69/(N:ℝ)^9+X^2*(H:ℝ)^2*M^64/(N:ℝ)^12))
  have hPoly : 0≤Poly := by dsimp only [Poly]; positivity
  have hClog : (0:ℝ)≤Nat.clog 2 H := Nat.cast_nonneg _
  have hClogPlus : (1:ℝ)≤1+(Nat.clog 2 H:ℝ) := le_add_of_nonneg_right hClog
  have hClogPlus0 := zero_le_one.trans hClogPlus
  have hXpow0 : 0≤X^(3*ε) := Real.rpow_nonneg hXp.le _
  have hSext : ‖Expdb.exponentialSumAt Fext X M a (a+L)‖^72≤
      D*(Nat.clog 2 H:ℝ)^36*X^(3*ε)*Poly :=
    upper_weyl_seventy_second_bound (norm_nonneg _) hZ0 hA₀ hC₀ hClog hX hMp hNp
      hKp hHp hRp hε.le hKH hphase hZ hweyl
  let W := (1+(Nat.clog 2 H:ℝ))^36*X^(3*ε)
  have hW : 1≤W := by
    calc
      _ ≤ (1+(Nat.clog 2 H:ℝ))^36 := one_le_pow₀ hClogPlus
      _ ≤ _ := le_mul_of_one_le_right (pow_nonneg hClogPlus0 36)
        (Real.one_le_rpow hX (mul_nonneg (by norm_num) hε.le))
  have hLog : (Nat.clog 2 H:ℝ)^36≤(1+(Nat.clog 2 H:ℝ))^36 :=
    pow_le_pow_left₀ hClog (by linarith only) 36
  have hSext' : ‖Expdb.exponentialSumAt Fext X M a (a+L)‖^72≤D*W*Poly := by
    calc
      _ ≤ D*(Nat.clog 2 H:ℝ)^36*X^(3*ε)*Poly := hSext
      _ ≤ D*(1+(Nat.clog 2 H:ℝ))^36*X^(3*ε)*Poly :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLog hD) hXpow0) hPoly
      _ = _ := by dsimp only [W]; simp only [mul_assoc]
  have hOriginal := sharp_extension_power_bound hD hW hPoly (by norm_num : (0:ℝ)≤6)
    (hsharp X a (a+L) ha hb) hSext'
  calc
    _ ≤ (2:ℝ)^71*(D+6^72)*W*(1+Poly) := hOriginal
    _ ≤ C*W*(1+Poly) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCoeff (zero_le_one.trans hW))
        (add_nonneg zero_le_one hPoly)
    _ = _ := by dsimp only [W,Poly]; simp only [mul_assoc]

example
    {σ ε : ℝ} (hσ : 0<σ) (hε : 0<ε) :
    ∃ δ η₀ B C : ℝ, 0<δ ∧ 0<η₀ ∧ η₀≤1/8 ∧ 1≤B ∧ 1≤C ∧
      ∀ (X M : ℝ) (F : ℝ → ℝ) (n N H a L : ℕ),
        1≤X → 1≤M → Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
        N=8*n → 2≤N → 2≤H → (H:ℝ)≤η₀*M → C≤X/M →
        B≤N → B^2*M^4≤X*(N:ℝ)^3 → B*X*(H:ℝ)*(N:ℝ)^2≤M^4 →
        B*(N:ℝ)^2≤M → B^2*X^3*(H:ℝ)^3*(N:ℝ)^11≤M^14 →
        B^2*X^7*(H:ℝ)^7*(N:ℝ)^27≤M^34 →
        M≤(a:ℝ) → ((a+L:ℕ):ℝ)≤2*M →
        ‖Expdb.exponentialSumAt F X M a (a+L)‖^72 ≤
          C*(1+(Nat.clog 2 H:ℝ))^36*X^(3*ε)*
            (1+(M^72/(H:ℝ)^36+
              ((M^72/(N:ℝ)^18+M^216/((H:ℝ)^36*X^36*(N:ℝ)^108)+
                  X^12*(H:ℝ)^12*(N:ℝ)^72/M^12)+
                (X^3*M^57+M^69/(N:ℝ)^9+X^2*(H:ℝ)^2*M^64/(N:ℝ)^12)))) :=
  HuxleyOriginalPhaseScratch.approximateModelPhase_upper_original_seventy_second (σ:=σ) (ε:=ε) hσ hε


#print axioms HuxleyOriginalPhaseScratch.approximateModelPhase_upper_original_seventy_second


private theorem floor_power_scales
    {U V : ℝ} (hU : 32≤U) (hV : 4≤V) :
    let n := ⌊U/8⌋₊
    let N := 8*n
    let H := ⌊V⌋₊
    2≤N ∧ 2≤H ∧ U/2≤(N:ℝ) ∧ (N:ℝ)≤U ∧
      V/2≤(H:ℝ) ∧ (H:ℝ)≤V := by
  intro n N H
  have hn4 : 4≤n := Nat.le_floor (by linarith only [hU] : (4:ℝ)≤U/8)
  have hH4 : 4≤H := Nat.le_floor hV
  have hNcast : (N:ℝ)=8*(n:ℝ) := by simp only [N,Nat.cast_mul,Nat.cast_ofNat]
  have hnlo : U/8<(n:ℝ)+1 := Nat.lt_floor_add_one (U/8)
  have hnhi : (n:ℝ)≤U/8 := Nat.floor_le (by linarith only [hU])
  have hHlo : V<(H:ℝ)+1 := Nat.lt_floor_add_one V
  have hHhi : (H:ℝ)≤V := Nat.floor_le (by linarith only [hV])
  refine ⟨by dsimp only [N]; omega,by omega,?_,?_,?_,hHhi⟩
  · rw [hNcast]
    linarith only [hnlo,hU]
  · rw [hNcast]
    linarith only [hnhi]
  · linarith only [hHlo,hV]

example
    {U V : ℝ} (hU : 32≤U) (hV : 4≤V) :
    let n := ⌊U/8⌋₊
    let N := 8*n
    let H := ⌊V⌋₊
    2≤N ∧ 2≤H ∧ U/2≤(N:ℝ) ∧ (N:ℝ)≤U ∧
      V/2≤(H:ℝ) ∧ (H:ℝ)≤V :=
  HuxleyOriginalPhaseScratch.floor_power_scales (U:=U) (V:=V) hU hV


#print axioms HuxleyOriginalPhaseScratch.floor_power_scales


private theorem eventually_uniform_clog_power_loss
    {C ζ : ℝ} (hC : 0≤C) (hζ : 0<ζ) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ H : ℕ, 2≤H → (H:ℝ)≤X →
      C*(1+(Nat.clog 2 H:ℝ))^36≤X^ζ := by
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  let D := 1+2/Real.log 2
  have hD : 0≤D := by dsimp only [D]; positivity
  have hLoss := eventually_const_log_pow_le_rpow
    (C*D^36) (mul_nonneg hC (pow_nonneg hD 36)) 36 hζ
  filter_upwards [hLoss,Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Filter.eventually_ge_atTop (1:ℝ)] with X hLossX hlogX hX
  intro H hH hHX
  have hHp : (0:ℝ)<H := by exact_mod_cast (show 0<H by omega)
  have hlogHX := Real.log_le_log hHp hHX
  have hc : (Nat.clog 2 H:ℝ)≤(2/Real.log 2)*Real.log X := by
    calc
      _ ≤ 2*(Real.log H/Real.log 2) := nat_clog_two_le_twice_log H hH
      _ ≤ 2*(Real.log X/Real.log 2) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hlogHX hlog2.le) (by norm_num)
      _ = _ := by ring
  have hplus : 1+(Nat.clog 2 H:ℝ)≤D*Real.log X := by
    dsimp only [D]
    nlinarith only [hc,hlogX]
  calc
    _ ≤ C*(D*Real.log X)^36 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hplus 36) hC
    _ = (C*D^36)*(Real.log X)^36 := by rw [mul_pow,mul_assoc]
    _ ≤ X^ζ := hLossX

example
    {C ζ : ℝ} (hC : 0≤C) (hζ : 0<ζ) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ H : ℕ, 2≤H → (H:ℝ)≤X →
      C*(1+(Nat.clog 2 H:ℝ))^36≤X^ζ :=
  HuxleyOriginalPhaseScratch.eventually_uniform_clog_power_loss (C:=C) (ζ:=ζ) hC hζ


#print axioms HuxleyOriginalPhaseScratch.eventually_uniform_clog_power_loss


private theorem upper_seven_monomials_power_window
    {X M N H ℓ u ν h ξ : ℝ}
    (hX : 1≤X) (hξ : 0≤ξ)
    (hMl : X^ℓ≤M) (hMu : M≤X^u)
    (hNl : X^ν/2≤N) (hNu : N≤X^ν)
    (hHl : X^h/2≤H) (hHu : H≤X^h)
    (hDiag : 72*u-36*h≤ξ) (hSqrt : 72*u-18*ν≤ξ)
    (hCubic : 216*u-36*h-36-108*ν≤ξ)
    (hEndpoint : 12+12*h+72*ν-12*ℓ≤ξ)
    (hType1 : 3+57*u≤ξ) (hType2 : 69*u-9*ν≤ξ)
    (hPair : 2+2*h+64*u-12*ν≤ξ) :
    1+(M^72/H^36+
      ((M^72/N^18+M^216/(H^36*X^36*N^108)+X^12*H^12*N^72/M^12)+
        (X^3*M^57+M^69/N^9+X^2*H^2*M^64/N^12))) ≤
      (8*(2:ℝ)^144)*X^ξ := by
  have hXp := zero_lt_one.trans_le hX
  have hMp : 0<M := (Real.rpow_pos_of_pos hXp ℓ).trans_le hMl
  have hNp : 0<N := (div_pos (Real.rpow_pos_of_pos hXp ν) (by norm_num)).trans_le hNl
  have hHp : 0<H := (div_pos (Real.rpow_pos_of_pos hXp h) (by norm_num)).trans_le hHl
  have hconst {b : ℝ} {j : ℕ} (hj : j≤144) (hb : b≤ξ) :
      (2:ℝ)^j*X^b≤(2:ℝ)^144*X^ξ :=
    mul_le_mul (pow_le_pow_right₀ (by norm_num) hj)
      (Real.rpow_le_rpow_of_exponent_le hX hb) (Real.rpow_nonneg hXp.le _) (by positivity)
  have h₀ : 1≤(2:ℝ)^144*X^ξ :=
    (Real.one_le_rpow hX hξ).trans
      (le_mul_of_one_le_left (Real.rpow_nonneg hXp.le _) (by norm_num))
  have h₁ : M^72/H^36≤(2:ℝ)^144*X^ξ := by
    calc
      _ ≤ (X^u)^72/(X^h/2)^36 := by gcongr
      _ = (2:ℝ)^36*((X^u)^72/(X^h)^36) := by field_simp
      _ = (2:ℝ)^36*X^(72*u-36*h) := by
        rw [←Real.rpow_mul_natCast hXp.le,←Real.rpow_mul_natCast hXp.le,
          ←Real.rpow_sub hXp]
        apply congrArg (fun y : ℝ => (2:ℝ)^36*X^y)
        push_cast
        ring
      _ ≤ _ := hconst (by norm_num) hDiag
  have h₂ : M^72/N^18≤(2:ℝ)^144*X^ξ := by
    calc
      _ ≤ (X^u)^72/(X^ν/2)^18 := by gcongr
      _ = (2:ℝ)^18*((X^u)^72/(X^ν)^18) := by field_simp
      _ = (2:ℝ)^18*X^(72*u-18*ν) := by
        rw [←Real.rpow_mul_natCast hXp.le,←Real.rpow_mul_natCast hXp.le,
          ←Real.rpow_sub hXp]
        apply congrArg (fun y : ℝ => (2:ℝ)^18*X^y)
        push_cast
        ring
      _ ≤ _ := hconst (by norm_num) hSqrt
  have h₃ : M^216/(H^36*X^36*N^108)≤(2:ℝ)^144*X^ξ := by
    calc
      _ ≤ (X^u)^216/((X^h/2)^36*X^36*(X^ν/2)^108) := by gcongr
      _ = (2:ℝ)^144*((X^u)^216/((X^h)^36*X^36*(X^ν)^108)) := by field_simp
      _ = (2:ℝ)^144*X^(216*u-36*h-36-108*ν) := by
        simp only [←Real.rpow_mul_natCast hXp.le]
        rw [←Real.rpow_natCast X 36]
        simp only [←Real.rpow_add hXp,←Real.rpow_sub hXp]
        apply congrArg (fun y : ℝ => (2:ℝ)^144*X^y)
        push_cast
        ring
      _ ≤ _ := hconst le_rfl hCubic
  have h₄ : X^12*H^12*N^72/M^12≤(2:ℝ)^144*X^ξ := by
    calc
      _ ≤ X^12*(X^h)^12*(X^ν)^72/(X^ℓ)^12 := by gcongr
      _ = X^(12+12*h+72*ν-12*ℓ) := by
        simp only [←Real.rpow_mul_natCast hXp.le]
        rw [←Real.rpow_natCast X 12]
        simp only [←Real.rpow_add hXp,←Real.rpow_sub hXp]
        apply congrArg (fun y : ℝ => X^y)
        push_cast
        ring
      _ ≤ _ := by simpa only [pow_zero,one_mul] using hconst (j:=0) (by omega) hEndpoint
  have h₅ : X^3*M^57≤(2:ℝ)^144*X^ξ := by
    calc
      _ ≤ X^3*(X^u)^57 := by gcongr
      _ = X^(3+57*u) := by
        rw [←Real.rpow_mul_natCast hXp.le,←Real.rpow_natCast X 3,←Real.rpow_add hXp]
        apply congrArg (fun y : ℝ => X^y)
        push_cast
        ring
      _ ≤ _ := by simpa only [pow_zero,one_mul] using hconst (j:=0) (by omega) hType1
  have h₆ : M^69/N^9≤(2:ℝ)^144*X^ξ := by
    calc
      _ ≤ (X^u)^69/(X^ν/2)^9 := by gcongr
      _ = (2:ℝ)^9*((X^u)^69/(X^ν)^9) := by field_simp
      _ = (2:ℝ)^9*X^(69*u-9*ν) := by
        rw [←Real.rpow_mul_natCast hXp.le,←Real.rpow_mul_natCast hXp.le,
          ←Real.rpow_sub hXp]
        apply congrArg (fun y : ℝ => (2:ℝ)^9*X^y)
        push_cast
        ring
      _ ≤ _ := hconst (by norm_num) hType2
  have h₇ : X^2*H^2*M^64/N^12≤(2:ℝ)^144*X^ξ := by
    calc
      _ ≤ X^2*(X^h)^2*(X^u)^64/(X^ν/2)^12 := by gcongr
      _ = (2:ℝ)^12*(X^2*(X^h)^2*(X^u)^64/(X^ν)^12) := by field_simp
      _ = (2:ℝ)^12*X^(2+2*h+64*u-12*ν) := by
        simp only [←Real.rpow_mul_natCast hXp.le]
        rw [←Real.rpow_natCast X 2]
        simp only [←Real.rpow_add hXp,←Real.rpow_sub hXp]
        apply congrArg (fun y : ℝ => (2:ℝ)^12*X^y)
        push_cast
        ring
      _ ≤ _ := hconst (by norm_num) hPair
  linarith only [h₀,h₁,h₂,h₃,h₄,h₅,h₆,h₇]

example
    {X M N H ℓ u ν h ξ : ℝ}
    (hX : 1≤X) (hξ : 0≤ξ)
    (hMl : X^ℓ≤M) (hMu : M≤X^u)
    (hNl : X^ν/2≤N) (hNu : N≤X^ν)
    (hHl : X^h/2≤H) (hHu : H≤X^h)
    (hDiag : 72*u-36*h≤ξ) (hSqrt : 72*u-18*ν≤ξ)
    (hCubic : 216*u-36*h-36-108*ν≤ξ)
    (hEndpoint : 12+12*h+72*ν-12*ℓ≤ξ)
    (hType1 : 3+57*u≤ξ) (hType2 : 69*u-9*ν≤ξ)
    (hPair : 2+2*h+64*u-12*ν≤ξ) :
    1+(M^72/H^36+
      ((M^72/N^18+M^216/(H^36*X^36*N^108)+X^12*H^12*N^72/M^12)+
        (X^3*M^57+M^69/N^9+X^2*H^2*M^64/N^12))) ≤
      (8*(2:ℝ)^144)*X^ξ :=
  HuxleyOriginalPhaseScratch.upper_seven_monomials_power_window (X:=X) (M:=M) (N:=N) (H:=H) (ℓ:=ℓ) (u:=u) (ν:=ν) (h:=h) (ξ:=ξ) hX hξ hMl hMu hNl hNu hHl hHu hDiag hSqrt hCubic hEndpoint hType1 hType2 hPair


#print axioms HuxleyOriginalPhaseScratch.upper_seven_monomials_power_window


private theorem eventually_upper_polynomial_power_window
    {B C η ℓ u ν h : ℝ}
    (hB : 1≤B) (hC : 1≤C) (hη : 0<η)
    (hℓ : 0<ℓ) (hν : 0<ν) (hh : 0<h)
    (hu : u<1) (hhℓ : h<ℓ) (hRN : 4*u<1+3*ν)
    (hNR : 1+h+2*ν<4*ℓ) (hNM : 2*ν<ℓ)
    (hFour : 3+3*h+11*ν<14*ℓ) (hTen : 7+7*h+27*ν<34*ℓ) :
    ∀ᶠ X : ℝ in Filter.atTop, 1≤X ∧
      ∀ M : ℝ, X^ℓ≤M → M≤X^u →
        let n := ⌊X^ν/8⌋₊
        let N := 8*n
        let H := ⌊X^h⌋₊
        1≤M ∧ 2≤N ∧ 2≤H ∧
        X^ν/2≤(N:ℝ) ∧ (N:ℝ)≤X^ν ∧ X^h/2≤(H:ℝ) ∧ (H:ℝ)≤X^h ∧
        (H:ℝ)≤η*M ∧ C≤X/M ∧ B≤N ∧
        B^2*M^4≤X*(N:ℝ)^3 ∧ B*X*(H:ℝ)*(N:ℝ)^2≤M^4 ∧
        B*(N:ℝ)^2≤M ∧ B^2*X^3*(H:ℝ)^3*(N:ℝ)^11≤M^14 ∧
        B^2*X^7*(H:ℝ)^7*(N:ℝ)^27≤M^34 := by
  have hB0 := zero_le_one.trans hB
  have hC0 := zero_le_one.trans hC
  have hNpow : ∀ᶠ X : ℝ in Filter.atTop, 32≤X^ν :=
    (tendsto_rpow_atTop hν).eventually_ge_atTop 32
  have hHpow : ∀ᶠ X : ℝ in Filter.atTop, 4≤X^h :=
    (tendsto_rpow_atTop hh).eventually_ge_atTop 4
  have hBNdom := eventually_const_mul_rpow_le_rpow (D:=2*B) (a:=0) hν
  have hRNdom := eventually_const_mul_rpow_le_rpow (D:=8*B^2) hRN
  have hNRdom := eventually_const_mul_rpow_le_rpow (D:=B) hNR
  have hNMdom := eventually_const_mul_rpow_le_rpow (D:=B) hNM
  have hFourdom := eventually_const_mul_rpow_le_rpow (D:=B^2) hFour
  have hTendom := eventually_const_mul_rpow_le_rpow (D:=B^2) hTen
  have hEtadom := eventually_const_mul_rpow_le_rpow (D:=1/η) hhℓ
  have hThreshold := eventually_const_mul_rpow_le_rpow (D:=C) hu
  filter_upwards [hNpow,hHpow,hBNdom,hRNdom,hNRdom,hNMdom,hFourdom,hTendom,
    hEtadom,hThreshold,Filter.eventually_ge_atTop (1:ℝ)] with
    X hNU hHU hBNX hRNX hNRX hNMX hFourX hTenX hEtaX hThresholdX hX
  refine ⟨hX,?_⟩
  intro M hMl hMu n N H
  have hXp := zero_lt_one.trans_le hX
  have hM1 : 1≤M := (Real.one_le_rpow hX hℓ.le).trans hMl
  have hMp := zero_lt_one.trans_le hM1
  obtain ⟨hN2,hH2,hNl,hNu,hHl,hHu⟩ := floor_power_scales hNU hHU
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hHp : (0:ℝ)<H := by exact_mod_cast (show 0<H by omega)
  have hp (q : ℝ) (m : ℕ) : (X^q)^m=X^((m:ℝ)*q) := by
    simpa only [mul_comm] using (Real.rpow_mul_natCast hXp.le q m).symm
  refine ⟨hM1,hN2,hH2,hNl,hNu,hHl,hHu,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have he : X^h≤η*X^ℓ := by
      have hh' := mul_le_mul_of_nonneg_left hEtaX hη.le
      simpa [one_div,←mul_assoc,hη.ne'] using hh'
    exact hHu.trans (he.trans (mul_le_mul_of_nonneg_left hMl hη.le))
  · apply (le_div_iff₀ hMp).mpr
    calc
      _ ≤ C*X^u := mul_le_mul_of_nonneg_left hMu hC0
      _ ≤ X^1 := hThresholdX
      _ = X := Real.rpow_one X
  · have he : 2*B≤X^ν := by simpa only [Real.rpow_zero,mul_one] using hBNX
    change B≤(N:ℝ)
    linarith only [he,hNl]
  · have hlow : B^2*(X^u)^4≤X*(X^ν/2)^3 := by
      apply (mul_le_mul_iff_right₀ (by norm_num : (0:ℝ)<8)).mp
      calc
        _ = (8*B^2)*X^(4*u) := by rw [hp]; norm_num only [Nat.cast_ofNat]; ring
        _ ≤ X^(1+3*ν) := hRNX
        _ = _ := by
          rw [div_pow,hp,Real.rpow_add hXp,Real.rpow_one]
          norm_num only [Nat.cast_ofNat]
          field_simp
    calc
      _ ≤ B^2*(X^u)^4 := by gcongr
      _ ≤ X*(X^ν/2)^3 := hlow
      _ ≤ _ := by gcongr
  · calc
      _ ≤ B*X*(X^h)*(X^ν)^2 := by gcongr
      _ = B*(X^(1:ℝ)*(X^h)*(X^ν)^2) := by rw [Real.rpow_one]; ring
      _ = B*X^(1+h+2*ν) := by
        rw [hp]
        norm_num only [Nat.cast_ofNat]
        rw [←Real.rpow_add hXp,←Real.rpow_add hXp]
      _ ≤ X^(4*ℓ) := hNRX
      _ = (X^ℓ)^4 := by simpa only [Nat.cast_ofNat] using (hp ℓ 4).symm
      _ ≤ _ := by gcongr
  · calc
      _ ≤ B*(X^ν)^2 := by gcongr
      _ = B*X^(2*ν) := by rw [hp]; norm_num only [Nat.cast_ofNat]
      _ ≤ X^ℓ := hNMX
      _ ≤ M := hMl
  · calc
      _ ≤ B^2*X^3*(X^h)^3*(X^ν)^11 := by gcongr
      _ = B^2*X^(3+3*h+11*ν) := by
        rw [hp,hp,←Real.rpow_natCast X 3]
        norm_num only [Nat.cast_ofNat]
        simp only [mul_assoc,←Real.rpow_add hXp]
      _ ≤ X^(14*ℓ) := hFourX
      _ = (X^ℓ)^14 := by simpa only [Nat.cast_ofNat] using (hp ℓ 14).symm
      _ ≤ _ := by gcongr
  · calc
      _ ≤ B^2*X^7*(X^h)^7*(X^ν)^27 := by gcongr
      _ = B^2*X^(7+7*h+27*ν) := by
        rw [hp,hp,←Real.rpow_natCast X 7]
        norm_num only [Nat.cast_ofNat]
        simp only [mul_assoc,←Real.rpow_add hXp]
      _ ≤ X^(34*ℓ) := hTenX
      _ = (X^ℓ)^34 := by simpa only [Nat.cast_ofNat] using (hp ℓ 34).symm
      _ ≤ _ := by gcongr

example
    {B C η ℓ u ν h : ℝ}
    (hB : 1≤B) (hC : 1≤C) (hη : 0<η)
    (hℓ : 0<ℓ) (hν : 0<ν) (hh : 0<h)
    (hu : u<1) (hhℓ : h<ℓ) (hRN : 4*u<1+3*ν)
    (hNR : 1+h+2*ν<4*ℓ) (hNM : 2*ν<ℓ)
    (hFour : 3+3*h+11*ν<14*ℓ) (hTen : 7+7*h+27*ν<34*ℓ) :
    ∀ᶠ X : ℝ in Filter.atTop, 1≤X ∧
      ∀ M : ℝ, X^ℓ≤M → M≤X^u →
        let n := ⌊X^ν/8⌋₊
        let N := 8*n
        let H := ⌊X^h⌋₊
        1≤M ∧ 2≤N ∧ 2≤H ∧
        X^ν/2≤(N:ℝ) ∧ (N:ℝ)≤X^ν ∧ X^h/2≤(H:ℝ) ∧ (H:ℝ)≤X^h ∧
        (H:ℝ)≤η*M ∧ C≤X/M ∧ B≤N ∧
        B^2*M^4≤X*(N:ℝ)^3 ∧ B*X*(H:ℝ)*(N:ℝ)^2≤M^4 ∧
        B*(N:ℝ)^2≤M ∧ B^2*X^3*(H:ℝ)^3*(N:ℝ)^11≤M^14 ∧
        B^2*X^7*(H:ℝ)^7*(N:ℝ)^27≤M^34 :=
  HuxleyOriginalPhaseScratch.eventually_upper_polynomial_power_window (B:=B) (C:=C) (η:=η) (ℓ:=ℓ) (u:=u) (ν:=ν) (h:=h) hB hC hη hℓ hν hh hu hhℓ hRN hNR hNM hFour hTen


#print axioms HuxleyOriginalPhaseScratch.eventually_upper_polynomial_power_window


private theorem upper_beta_of_power_window
    {α : ℝ≥0} {β δw ν h εs ζ : ℝ}
    (hδw : 0<δw) (hν : 0<ν) (hh : 0<h) (hεs : 0<εs) (hζ : 0<ζ)
    (hℓ : 0<(α:ℝ)-δw) (hu : (α:ℝ)+δw<1)
    (hhℓ : h<(α:ℝ)-δw) (hRN : 4*((α:ℝ)+δw)<1+3*ν)
    (hNR : 1+h+2*ν<4*((α:ℝ)-δw)) (hNM : 2*ν<(α:ℝ)-δw)
    (hFour : 3+3*h+11*ν<14*((α:ℝ)-δw))
    (hTen : 7+7*h+27*ν<34*((α:ℝ)-δw))
    (hBase : 3*εs+ζ≤72*β)
    (hDiag : 72*((α:ℝ)+δw)-36*h+3*εs+ζ≤72*β)
    (hSqrt : 72*((α:ℝ)+δw)-18*ν+3*εs+ζ≤72*β)
    (hCubic : 216*((α:ℝ)+δw)-36*h-36-108*ν+3*εs+ζ≤72*β)
    (hEndpoint : 12+12*h+72*ν-12*((α:ℝ)-δw)+3*εs+ζ≤72*β)
    (hType1 : 3+57*((α:ℝ)+δw)+3*εs+ζ≤72*β)
    (hType2 : 69*((α:ℝ)+δw)-9*ν+3*εs+ζ≤72*β)
    (hPair : 2+2*h+64*((α:ℝ)+δw)-12*ν+3*εs+ζ≤72*β) :
    Expdb.IsExponentSumBoundNonAsymptotic α β := by
  intro ε hε σ hσ
  obtain ⟨δsrc,η,B,Csrc,hδsrc,hη,hηcap,hB,hCsrc,hSource⟩ :=
    approximateModelPhase_upper_original_seventy_second hσ hεs
  have hPhys := eventually_upper_polynomial_power_window
    hB hCsrc hη hℓ hν hh hu hhℓ hRN hNR hNM hFour hTen
  have hLog := eventually_uniform_clog_power_loss
    (C:=Csrc*(8*(2:ℝ)^144))
    (mul_nonneg (zero_le_one.trans hCsrc) (by norm_num)) hζ
  obtain ⟨T₀,hT₀⟩ := Filter.eventually_atTop.mp (hPhys.and hLog)
  let δ := min δsrc δw
  let C := max 1 T₀
  have hC : 1≤C := le_max_left _ _
  refine ⟨δ,lt_min hδsrc hδw,7,by norm_num,C,hC,?_⟩
  intro T M F a b setup
  have hT : 1≤T := hC.trans setup.threshold_le_param
  have hTp := zero_lt_one.trans_le hT
  have hTogether := hT₀ T ((le_max_right 1 T₀).trans setup.threshold_le_param)
  by_cases hba : b<a
  · rw [Expdb.exponentialSumAt_of_lt hba,norm_zero]
    exact mul_nonneg (zero_le_one.trans hC) (Real.rpow_nonneg hTp.le _)
  have hab : a≤b := Nat.le_of_not_gt hba
  let L := b-a
  have hEnd : a+L=b := Nat.add_sub_of_le hab
  have hδwle : δ≤δw := min_le_right _ _
  have hδsrcle : δ≤δsrc := min_le_left _ _
  have hMl : T^((α:ℝ)-δw)≤M :=
    (Real.rpow_le_rpow_of_exponent_le hT (sub_le_sub_left hδwle _)).trans
      setup.rpow_sub_le_scale
  have hMu : M≤T^((α:ℝ)+δw) := setup.scale_le_rpow_add.trans
    (Real.rpow_le_rpow_of_exponent_le hT (add_le_add le_rfl hδwle))
  have hF := approximateModelPhase_mono setup.isApproximateModelPhase le_rfl hδsrcle
  let n := ⌊T^ν/8⌋₊
  let N := 8*n
  let H := ⌊T^h⌋₊
  obtain ⟨hM,hN2,hH2,hNl,hNu,hHl,hHu,hHη,hThreshold,hBN,hRNM,hNRM,
      hNMM,hFourM,hTenM⟩ := hTogether.1.2 M hMl hMu
  have hStart := setup.scale_le_start
  have hStop : ((a+L:ℕ):ℝ)≤2*M := by rw [hEnd]; exact setup.end_le_two_mul_scale
  have hActual := hSource T M F n N H a L hT hM hF rfl hN2 hH2 hHη
    hThreshold hBN hRNM hNRM hNMM hFourM hTenM hStart hStop
  let ξ := 72*β-3*εs-ζ
  have hξ : 0≤ξ := by dsimp only [ξ]; linarith only [hBase]
  have hPoly := upper_seven_monomials_power_window hT hξ hMl hMu hNl hNu hHl hHu
    (by dsimp only [ξ]; linarith only [hDiag])
    (by dsimp only [ξ]; linarith only [hSqrt])
    (by dsimp only [ξ]; linarith only [hCubic])
    (by dsimp only [ξ]; linarith only [hEndpoint])
    (by dsimp only [ξ]; linarith only [hType1])
    (by dsimp only [ξ]; linarith only [hType2])
    (by dsimp only [ξ]; linarith only [hPair])
  have hh1 : h≤1 := by linarith only [hhℓ,hu,hδw]
  have hHT : (H:ℝ)≤T := hHu.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT hh1)
  have hLoss := hTogether.2 H hH2 hHT
  have hCsrc0 := zero_le_one.trans hCsrc
  have hLog0 : 0≤(1+(Nat.clog 2 H:ℝ))^36 := pow_nonneg (by positivity) _
  have hXpow0 := Real.rpow_nonneg hTp.le (3*εs)
  have hPower : ‖Expdb.exponentialSumAt F T M a b‖^72≤T^(72*β) := by
    rw [←hEnd]
    calc
      _ ≤ Csrc*(1+(Nat.clog 2 H:ℝ))^36*T^(3*εs)*
          (1+ (M^72/(H:ℝ)^36+
            ((M^72/(N:ℝ)^18+M^216/((H:ℝ)^36*T^36*(N:ℝ)^108)+
                T^12*(H:ℝ)^12*(N:ℝ)^72/M^12)+
              (T^3*M^57+M^69/(N:ℝ)^9+T^2*(H:ℝ)^2*M^64/(N:ℝ)^12)))) := hActual
      _ ≤ Csrc*(1+(Nat.clog 2 H:ℝ))^36*T^(3*εs)*((8*(2:ℝ)^144)*T^ξ) :=
        mul_le_mul_of_nonneg_left hPoly (mul_nonneg (mul_nonneg hCsrc0 hLog0) hXpow0)
      _ = (Csrc*(8*(2:ℝ)^144)*(1+(Nat.clog 2 H:ℝ))^36)*T^(3*εs)*T^ξ := by ac_rfl
      _ ≤ T^ζ*T^(3*εs)*T^ξ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hLoss hXpow0) (Real.rpow_nonneg hTp.le _)
      _ = T^(72*β) := by
        rw [←Real.rpow_add hTp,←Real.rpow_add hTp]
        apply congrArg (fun x : ℝ => T^x)
        dsimp only [ξ]
        ring
  have hRootPower : (T^β)^72=T^(72*β) := by
    simpa only [Nat.cast_ofNat,mul_comm] using (Real.rpow_mul_natCast hTp.le β 72).symm
  have hRoot : ‖Expdb.exponentialSumAt F T M a b‖≤T^β :=
    le_of_pow_le_pow_left₀ (by norm_num : (72:ℕ)≠0)
      (Real.rpow_nonneg hTp.le _) (hPower.trans_eq hRootPower.symm)
  calc
    _ ≤ T^β := hRoot
    _ ≤ T^(β+ε) := Real.rpow_le_rpow_of_exponent_le hT (le_add_of_nonneg_right hε.le)
    _ ≤ C*T^(β+ε) := le_mul_of_one_le_left (Real.rpow_nonneg hTp.le _) hC

example
    {α : ℝ≥0} {β δw ν h εs ζ : ℝ}
    (hδw : 0<δw) (hν : 0<ν) (hh : 0<h) (hεs : 0<εs) (hζ : 0<ζ)
    (hℓ : 0<(α:ℝ)-δw) (hu : (α:ℝ)+δw<1)
    (hhℓ : h<(α:ℝ)-δw) (hRN : 4*((α:ℝ)+δw)<1+3*ν)
    (hNR : 1+h+2*ν<4*((α:ℝ)-δw)) (hNM : 2*ν<(α:ℝ)-δw)
    (hFour : 3+3*h+11*ν<14*((α:ℝ)-δw))
    (hTen : 7+7*h+27*ν<34*((α:ℝ)-δw))
    (hBase : 3*εs+ζ≤72*β)
    (hDiag : 72*((α:ℝ)+δw)-36*h+3*εs+ζ≤72*β)
    (hSqrt : 72*((α:ℝ)+δw)-18*ν+3*εs+ζ≤72*β)
    (hCubic : 216*((α:ℝ)+δw)-36*h-36-108*ν+3*εs+ζ≤72*β)
    (hEndpoint : 12+12*h+72*ν-12*((α:ℝ)-δw)+3*εs+ζ≤72*β)
    (hType1 : 3+57*((α:ℝ)+δw)+3*εs+ζ≤72*β)
    (hType2 : 69*((α:ℝ)+δw)-9*ν+3*εs+ζ≤72*β)
    (hPair : 2+2*h+64*((α:ℝ)+δw)-12*ν+3*εs+ζ≤72*β) :
    Expdb.IsExponentSumBoundNonAsymptotic α β :=
  HuxleyOriginalPhaseScratch.upper_beta_of_power_window (α:=α) (β:=β) (δw:=δw) (ν:=ν) (h:=h) (εs:=εs) (ζ:=ζ) hδw hν hh hεs hζ hℓ hu hhℓ hRN hNR hNM hFour hTen hBase hDiag hSqrt hCubic hEndpoint hType1 hType2 hPair


#print axioms HuxleyOriginalPhaseScratch.upper_beta_of_power_window


private theorem upper_seventh_row_nonAsymptotic
    {α : ℝ≥0} (hα : 861996/2811205≤(α:ℝ)) (hα₁ : (α:ℝ)≤87/275) :
    Expdb.IsExponentSumBoundNonAsymptotic α ((13+94*(α:ℝ))/146) := by
  let t : ℝ := ((α:ℝ)-861996/2811205)/(87/275-861996/2811205)
  let ν : ℝ := (1-t)*(92661/1000000)+t*(108591/1000000)
  let h : ℝ := (1-t)*(41183/1000000)+t*(48263/1000000)
  apply upper_beta_of_power_window
    (δw:=1/1000000000000) (ν:=ν) (h:=h) (εs:=1/100000000) (ζ:=1/100000000)
  all_goals norm_num [ν,h,t]
  all_goals linarith only [hα,hα₁]

private theorem exponentSumGrowthExponent_le_huxley_seventhRow
    {α : ℝ≥0} (hα : 861996/2811205≤(α:ℝ)) (hα₁ : (α:ℝ)≤87/275) :
    Expdb.exponentSumGrowthExponent α ≤ (13+94*(α:ℝ))/146 := by
  exact Expdb.exponentSumGrowthExponent_le_iff_nonAsymptotic.mpr
    (upper_seventh_row_nonAsymptotic hα hα₁)

private theorem upper_eighth_row_nonAsymptotic
    {α : ℝ≥0} (hα : 87/275≤(α:ℝ)) (hα₁ : (α:ℝ)≤423/1295) :
    Expdb.IsExponentSumBoundNonAsymptotic α ((11+191*(α:ℝ))/244) := by
  let t : ℝ := ((α:ℝ)-87/275)/(423/1295-87/275)
  let ν : ℝ := (1-t)*(108591/1000000)+t*(116002/1000000)
  let h : ℝ := (1-t)*(48263/1000000)+t*(52767/1000000)
  apply upper_beta_of_power_window
    (δw:=1/1000000000000) (ν:=ν) (h:=h) (εs:=1/100000000) (ζ:=1/100000000)
  all_goals norm_num [ν,h,t]
  all_goals linarith only [hα,hα₁]

private theorem exponentSumGrowthExponent_le_huxley_eighthRow
    {α : ℝ≥0} (hα : 87/275≤(α:ℝ)) (hα₁ : (α:ℝ)≤423/1295) :
    Expdb.exponentSumGrowthExponent α ≤ (11+191*(α:ℝ))/244 := by
  exact Expdb.exponentSumGrowthExponent_le_iff_nonAsymptotic.mpr
    (upper_eighth_row_nonAsymptotic hα hα₁)

example
    {α : ℝ≥0} (hα : 861996/2811205≤(α:ℝ)) (hα₁ : (α:ℝ)≤87/275) :
    Expdb.IsExponentSumBoundNonAsymptotic α ((13+94*(α:ℝ))/146) :=
  HuxleyOriginalPhaseScratch.upper_seventh_row_nonAsymptotic (α:=α) hα hα₁

example
    {α : ℝ≥0} (hα : 861996/2811205≤(α:ℝ)) (hα₁ : (α:ℝ)≤87/275) :
    Expdb.exponentSumGrowthExponent α ≤ (13+94*(α:ℝ))/146 :=
  HuxleyOriginalPhaseScratch.exponentSumGrowthExponent_le_huxley_seventhRow (α:=α) hα hα₁

example
    {α : ℝ≥0} (hα : 87/275≤(α:ℝ)) (hα₁ : (α:ℝ)≤423/1295) :
    Expdb.IsExponentSumBoundNonAsymptotic α ((11+191*(α:ℝ))/244) :=
  HuxleyOriginalPhaseScratch.upper_eighth_row_nonAsymptotic (α:=α) hα hα₁

example
    {α : ℝ≥0} (hα : 87/275≤(α:ℝ)) (hα₁ : (α:ℝ)≤423/1295) :
    Expdb.exponentSumGrowthExponent α ≤ (11+191*(α:ℝ))/244 :=
  HuxleyOriginalPhaseScratch.exponentSumGrowthExponent_le_huxley_eighthRow (α:=α) hα hα₁


#print axioms HuxleyOriginalPhaseScratch.upper_seventh_row_nonAsymptotic
#print axioms HuxleyOriginalPhaseScratch.exponentSumGrowthExponent_le_huxley_seventhRow
#print axioms HuxleyOriginalPhaseScratch.upper_eighth_row_nonAsymptotic
#print axioms HuxleyOriginalPhaseScratch.exponentSumGrowthExponent_le_huxley_eighthRow

end HuxleyOriginalPhaseScratch
