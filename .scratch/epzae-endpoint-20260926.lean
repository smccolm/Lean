import TaoTrudgianYang2025.ParabolaBilinearLocalization
import TaoTrudgianYang2025.ExponentPairShiftJets
import TaoTrudgianYang2025.SargosLocalAffineJets

noncomputable section
open Set Filter Expdb
open scoped ContDiff Topology
namespace TaoTrudgianYang2025.EndpointPrototype

private theorem compression_power_error {η : ℝ} (hη : 0 ≤ η) (hη₁ : η ≤ 1)
    (p : ℕ) : |(1-η)^p-1| ≤ (p : ℝ)*η := by
  have hc : 0 ≤ 1-η := by linarith
  have hp : (1-η)^p ≤ 1 := pow_le_one₀ hc (by linarith)
  rw [abs_of_nonpos (sub_nonpos.mpr hp)]
  have h := one_add_mul_le_pow (a := -η) (by linarith : -2 ≤ -η) p
  rw [← sub_eq_add_neg] at h
  linarith

private theorem compression_jet_error
    {σ δ η : ℝ} {Q p : ℕ} {G : ℝ → ℝ}
    (hσ : 0 ≤ σ) (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hη₁ : η < 1)
    (hG : IsApproximateModelPhaseFunction G σ Q δ) (hp : p ≤ Q)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) :
    |iteratedDeriv (p+1) (fun v => G (aProcessShiftPoint η 0 v)) u -
        iteratedDeriv p (modelPhase σ) u| ≤
      δ+(modelPhaseJetCoefficient σ (p+1)+(p+1)*modelPhaseJetCoefficient σ p)*η := by
  have hv := aProcessShiftPoint_mem_Ioo hη hη₁ (by norm_num : (0:ℝ) ∈ Icc 0 1) hu
  have hc : 0 ≤ 1-η := by linarith
  have hcp : 0 ≤ (1-η)^(p+1) := pow_nonneg hc _
  have hc1 : (1-η)^(p+1) ≤ 1 := pow_le_one₀ hc (by linarith)
  have hd := sargos_iteratedDeriv_comp_affine_local
    (c := 1-η) (d := (1+0)*η)
    (fun y hy => approximateModelPhase_contDiffAt hG
      (aProcessShiftPoint_mem_Ioo hη hη₁ (by norm_num : (0:ℝ) ∈ Icc 0 1) hy))
    hu (p+1)
  change iteratedDeriv (p+1) (fun v => G (aProcessShiftPoint η 0 v)) u = _ at hd
  rw [hd]
  have herr := approximateModelPhase_iteratedDeriv_error hG hv p hp
  have hlip := iteratedDeriv_modelPhase_lipschitz hσ hv hu p
  have hdist := aProcessShiftPoint_distance hη (by norm_num : (0:ℝ) ∈ Icc 0 1)
    (Ioo_subset_Icc_self hu)
  have hb := iteratedDeriv_modelPhase_abs_le hσ hu p
  have hpow := compression_power_error hη hη₁.le (p+1)
  have h1 : |(1-η)^(p+1) *
      (iteratedDeriv (p+1) G (aProcessShiftPoint η 0 u) -
        iteratedDeriv p (modelPhase σ) (aProcessShiftPoint η 0 u))| ≤ δ := by
    rw [abs_mul,abs_of_nonneg hcp]
    exact (mul_le_mul_of_nonneg_left herr hcp).trans (mul_le_of_le_one_left hδ hc1)
  have h2 : |(1-η)^(p+1) *
      (iteratedDeriv p (modelPhase σ) (aProcessShiftPoint η 0 u) -
        iteratedDeriv p (modelPhase σ) u)| ≤ modelPhaseJetCoefficient σ (p+1)*η := by
    rw [abs_mul,abs_of_nonneg hcp]
    exact (mul_le_mul_of_nonneg_left
      (hlip.trans (mul_le_mul_of_nonneg_left hdist (modelPhaseJetCoefficient_nonneg σ _))) hcp).trans
        (mul_le_of_le_one_left (mul_nonneg (modelPhaseJetCoefficient_nonneg σ _) hη) hc1)
  have h3 : |((1-η)^(p+1)-1)*iteratedDeriv p (modelPhase σ) u| ≤
      (p+1)*modelPhaseJetCoefficient σ p*η := by
    rw [abs_mul]
    have hh := mul_le_mul hpow hb (abs_nonneg _) (by positivity : 0 ≤ ((p+1:ℕ):ℝ)*η)
    push_cast at hh
    nlinarith only [hh]
  calc
    _ = |(1-η)^(p+1) *
        (iteratedDeriv (p+1) G (aProcessShiftPoint η 0 u) -
          iteratedDeriv p (modelPhase σ) (aProcessShiftPoint η 0 u)) +
        (1-η)^(p+1) * (iteratedDeriv p (modelPhase σ) (aProcessShiftPoint η 0 u) -
          iteratedDeriv p (modelPhase σ) u) +
        ((1-η)^(p+1)-1)*iteratedDeriv p (modelPhase σ) u| := by
      congr 1
      change (1-η)^(p+1)*iteratedDeriv (p+1) G (aProcessShiftPoint η 0 u)-_ = _
      ring
    _ ≤ _ := by
      exact (abs_add_le _ _).trans
        (add_le_add ((abs_add_le _ _).trans (add_le_add h1 h2)) h3) |>.trans_eq (by ring)

private theorem compression_model_phase {σ : ℝ} (hσ : 0 ≤ σ) (Q : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (G : ℝ → ℝ) (δ η : ℝ),
      0 ≤ δ → 0 ≤ η → η < 1 →
      IsApproximateModelPhaseFunction G σ Q δ →
      IsApproximateModelPhaseFunction (fun v => G (aProcessShiftPoint η 0 v)) σ Q (δ+K*η) := by
  let B : ℕ → ℝ := fun p =>
    modelPhaseJetCoefficient σ (p+1)+(p+1)*modelPhaseJetCoefficient σ p
  have hB (p : ℕ) : 0 ≤ B p := by
    dsimp [B]
    exact add_nonneg (modelPhaseJetCoefficient_nonneg σ _) (mul_nonneg
      (by positivity) (modelPhaseJetCoefficient_nonneg σ _))
  refine ⟨1+∑ p ∈ Finset.range (Q+1), B p, ?_, ?_⟩
  · have hh := Finset.sum_nonneg (s := Finset.range (Q+1)) (fun p _ => hB p)
    linarith
  intro G δ η hδ hη hη₁ hG
  apply approximateModelPhase_of_interior_bounds
  · apply hG.1.comp (by unfold aProcessShiftPoint; fun_prop)
    intro u hu
    exact aProcessShiftPoint_mem_Icc hη hη₁.le (by norm_num : (0:ℝ) ∈ Icc 0 1) hu
  · intro u hu p hp
    have hb : B p ≤ 1+∑ j ∈ Finset.range (Q+1), B j := by
      have hh := Finset.single_le_sum (s := Finset.range (Q+1)) (f := B)
        (fun j _ => hB j) (Finset.mem_range.mpr (by omega : p < Q+1))
      linarith
    exact (compression_jet_error hσ hδ hη hη₁ hG hp hu).trans
      (add_le_add_right (mul_le_mul_of_nonneg_right hb hη) δ)

#print axioms compression_power_error
#print axioms compression_jet_error
#print axioms compression_model_phase

private theorem residue_core_bound {h r a b : ℕ} {P B : ℝ} {f : ℕ → ℂ}
    (hh : 0 < h) (hr : r < h) (hB : 0 ≤ B)
    (ha : P ≤ (a : ℝ))
    (hbound : ∀ c d : ℕ, (P-r)/(h:ℝ) ≤ c → (d:ℝ) ≤ 2*((P-r)/(h:ℝ)) →
      ‖∑ m ∈ Finset.Icc c d, f (h*m+r)‖ ≤ B) :
    ‖∑ n ∈ (Finset.Icc a b).filter (fun n => n%h=r ∧ (n:ℝ) ≤ 2*P-r), f n‖ ≤ B := by
  classical
  let S := (Finset.Icc a b).filter (fun n => n%h=r ∧ (n:ℝ) ≤ 2*P-r)
  change ‖∑ n ∈ S, f n‖ ≤ B
  by_cases hS : S.Nonempty
  · let l := S.min' hS
    let u := S.max' hS
    have hl : l ∈ S := Finset.min'_mem _ _
    have hu : u ∈ S := Finset.max'_mem _ _
    have hlp := Finset.mem_filter.mp hl
    have hup := Finset.mem_filter.mp hu
    have hid {n : ℕ} (hn : n ∈ S) : h*(n/h)+r=n := by
      have hm := (Finset.mem_filter.mp hn).2.1
      have hd := Nat.mod_add_div n h
      omega
    have hlid := hid hl
    have huid := hid hu
    have hreal : (0:ℝ) < h := by exact_mod_cast hh
    have hcl : (P-r)/(h:ℝ) ≤ (l/h:ℕ) := by
      apply (div_le_iff₀ hreal).mpr
      have hal : (a:ℝ) ≤ l := by exact_mod_cast (Finset.mem_Icc.mp hlp.1).1
      have hi : (h:ℝ)*(l/h:ℕ)+r=l := by exact_mod_cast hlid
      nlinarith
    have hdu : ((u/h:ℕ):ℝ) ≤ 2*((P-r)/(h:ℝ)) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hreal).mpr
      have hi : (h:ℝ)*(u/h:ℕ)+r=u := by exact_mod_cast huid
      nlinarith [hup.2.2]
    have he : (∑ m ∈ Finset.Icc (l/h) (u/h), f (h*m+r)) = ∑ n ∈ S, f n := by
      apply Finset.sum_bij (fun m _ => h*m+r)
      · intro m hm
        have hm' := Finset.mem_Icc.mp hm
        have hlo := Nat.mul_le_mul_left h hm'.1
        have hhi := Nat.mul_le_mul_left h hm'.2
        have hlm : l ≤ h*m+r := by omega
        have hmu : h*m+r ≤ u := by omega
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hlp.1).1.trans hlm,
          hmu.trans (Finset.mem_Icc.mp hup.1).2⟩, ?_, ?_⟩
        · simp [Nat.add_mod,Nat.mod_eq_of_lt hr]
        · have hn : ((h*m+r:ℕ):ℝ) ≤ u := by exact_mod_cast hmu
          exact hn.trans hup.2.2
      · intro m hm k hk heq
        exact Nat.eq_of_mul_eq_mul_left hh (Nat.add_right_cancel heq)
      · intro n hn
        refine ⟨n/h,Finset.mem_Icc.mpr ⟨?_,?_⟩,hid hn⟩
        · exact Nat.div_le_div_right (Finset.min'_le _ _ hn)
        · exact Nat.div_le_div_right (Finset.le_max' _ _ hn)
      · intro m hm
        rfl
    rw [← he]
    exact hbound _ _ hcl hdu
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simpa only [he,Finset.sum_empty,norm_zero] using hB

private theorem residue_upper_tail_card {h r a b : ℕ} {P : ℝ}
    (hh : 0 < h) (hr : r < h) (hb : (b:ℝ) ≤ 2*P) :
    ((Finset.Icc a b).filter (fun n => n%h=r ∧ ¬ (n:ℝ) ≤ 2*P-r)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro n hn m hm
  have hnp := Finset.mem_filter.mp hn
  have hmp := Finset.mem_filter.mp hm
  have hnup : (n:ℝ) ≤ 2*P :=
    (by exact_mod_cast (Finset.mem_Icc.mp hnp.1).2 : (n:ℝ) ≤ b).trans hb
  have hmup : (m:ℝ) ≤ 2*P :=
    (by exact_mod_cast (Finset.mem_Icc.mp hmp.1).2 : (m:ℝ) ≤ b).trans hb
  have hnd : h*(n/h)+r=n := by
    have he := Nat.mod_add_div n h
    omega
  have hmd : h*(m/h)+r=m := by
    have he := Nat.mod_add_div m h
    omega
  have hnr : (h:ℝ)*(n/h:ℕ)+r=n := by exact_mod_cast hnd
  have hmr : (h:ℝ)*(m/h:ℕ)+r=m := by exact_mod_cast hmd
  have hrr : (r:ℝ) < h := by exact_mod_cast hr
  have hpos : (0:ℝ) < h := by exact_mod_cast hh
  have heq : n/h=m/h := by
    apply le_antisymm
    · by_contra hnle
      have hi : ((m/h:ℕ):ℝ)+1 ≤ (n/h:ℕ) := by exact_mod_cast (by omega : m/h+1 ≤ n/h)
      have hnlo := lt_of_not_ge hnp.2.2
      have hmlo := lt_of_not_ge hmp.2.2
      nlinarith
    · by_contra hmle
      have hi : ((n/h:ℕ):ℝ)+1 ≤ (m/h:ℕ) := by exact_mod_cast (by omega : n/h+1 ≤ m/h)
      have hnlo := lt_of_not_ge hnp.2.2
      have hmlo := lt_of_not_ge hmp.2.2
      nlinarith
  rw [heq] at hnd
  omega

private theorem residue_interval_sum_bound {h a b : ℕ} {P B : ℝ} {f : ℕ → ℂ}
    (hh : 0 < h) (hB : 0 ≤ B) (ha : P ≤ (a:ℝ)) (hb : (b:ℝ) ≤ 2*P)
    (hf : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (hbound : ∀ r < h, ∀ c d : ℕ, (P-r)/(h:ℝ) ≤ c →
      (d:ℝ) ≤ 2*((P-r)/(h:ℝ)) →
      ‖∑ m ∈ Finset.Icc c d, f (h*m+r)‖ ≤ B) :
    ‖∑ n ∈ Finset.Icc a b, f n‖ ≤ (h:ℝ)*(B+1) := by
  classical
  have hpart := Finset.sum_fiberwise_of_maps_to
    (s := Finset.Icc a b) (t := Finset.range h) (g := fun n => n%h)
    (fun n _ => Finset.mem_range.mpr (Nat.mod_lt n hh)) f
  rw [← hpart]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ r ∈ Finset.range h, (B+1) := by
      apply Finset.sum_le_sum
      intro r hr
      have hrc : r < h := Finset.mem_range.mp hr
      have hcore := residue_core_bound (b := b) hh hrc hB ha (hbound r hrc)
      have hcard := residue_upper_tail_card hh hrc hb (a := a)
      let S : Finset ℕ := (Finset.Icc a b).filter (fun n => n%h=r)
      have he := Finset.sum_filter_add_sum_filter_not S (fun n : ℕ => (n:ℝ) ≤ 2*P-r) f
      have htail : ‖∑ n ∈ S.filter (fun n : ℕ => ¬ (n:ℝ) ≤ 2*P-r), f n‖ ≤ 1 := by
        refine (norm_sum_le _ _).trans ?_
        calc
          _ ≤ ∑ n ∈ S.filter (fun n : ℕ => ¬ (n:ℝ) ≤ 2*P-r), (1:ℝ) :=
            Finset.sum_le_sum (fun n _ => hf n)
          _ = ((S.filter (fun n : ℕ => ¬ (n:ℝ) ≤ 2*P-r)).card:ℝ) := by simp
          _ ≤ 1 := by
            have hc : (S.filter (fun n : ℕ => ¬ (n:ℝ) ≤ 2*P-r)).card ≤ 1 := by
              simpa only [S,Finset.filter_filter] using hcard
            exact_mod_cast hc
      have hc : ‖∑ n ∈ S.filter (fun n : ℕ => (n:ℝ) ≤ 2*P-r), f n‖ ≤ B := by
        simpa only [S,Finset.filter_filter] using hcore
      change ‖∑ n ∈ S, f n‖ ≤ B+1
      rw [← he]
      exact (norm_add_le _ _).trans (add_le_add hc htail)
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]

#print axioms residue_core_bound
#print axioms residue_upper_tail_card
#print axioms residue_interval_sum_bound


private theorem endpoint_residue_scales
    {T P q δ δs K : ℝ} (hT : 1 ≤ T) (hq : 0 ≤ q)
    (hδs : 0 < δs) (hδ : δ ≤ δs/2) (hK : 1 ≤ K)
    (hPlo : T^((1:ℝ)/2-δ) ≤ P) (hPhi : P ≤ T^((1:ℝ)/2+δ))
    (hsize : 8*T^q ≤ T^((1:ℝ)/2-δ))
    (habsorb : 4*T^((1:ℝ)/2-δs) ≤ T^((1:ℝ)/2-δ))
    (hjet : (4*K/δs)*T^q ≤ T^((1:ℝ)/2-δ)) :
    1 ≤ ⌈T^q⌉₊ ∧ (⌈T^q⌉₊:ℝ) ≤ 2*T^q ∧ ∀ r < ⌈T^q⌉₊,
      0 ≤ (r:ℝ)/P ∧ (r:ℝ)/P < 1 ∧
      T^((1:ℝ)/2-q-δs) ≤ (P-r)/(⌈T^q⌉₊:ℝ) ∧
      (P-r)/(⌈T^q⌉₊:ℝ) ≤ T^((1:ℝ)/2-q+δs) ∧
      δ+K*((r:ℝ)/P) ≤ δs := by
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hz : 1 ≤ T^q := Real.one_le_rpow hT hq
  have hzp : 0 < T^q := zero_lt_one.trans_le hz
  have hMlo : T^q ≤ (⌈T^q⌉₊:ℝ) := Nat.le_ceil _
  have hMhi : (⌈T^q⌉₊:ℝ) ≤ 2*T^q := by
    have hh := Nat.ceil_lt_add_one hzp.le
    linarith
  have hMpos : (0:ℝ) < ⌈T^q⌉₊ := hzp.trans_le hMlo
  have hPp : 0 < P := (Real.rpow_pos_of_pos hTp _).trans_le hPlo
  refine ⟨Nat.one_le_ceil_iff.mpr hzp,hMhi,?_⟩
  intro r hr
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg _
  have hrM : (r:ℝ) < ⌈T^q⌉₊ := by exact_mod_cast hr
  have hrP : (r:ℝ) < P := by linarith
  have hrhalf : (r:ℝ) ≤ P/2 := by linarith
  refine ⟨div_nonneg hr0 hPp.le,(div_lt_one hPp).mpr hrP,?_,?_,?_⟩
  · apply (le_div_iff₀ hMpos).mpr
    have he : T^((1:ℝ)/2-q-δs)*T^q = T^((1:ℝ)/2-δs) := by
      rw [← Real.rpow_add hTp]
      congr 1
      ring
    have hh := mul_le_mul_of_nonneg_left hMhi (Real.rpow_nonneg hTp.le ((1:ℝ)/2-q-δs))
    have he' : T^((1:ℝ)/2-q-δs)*(2*T^q) = 2*T^((1:ℝ)/2-δs) := by
      calc
        _ = 2*(T^((1:ℝ)/2-q-δs)*T^q) := by ring
        _ = _ := by rw [he]
    rw [he'] at hh
    linarith
  · apply (div_le_iff₀ hMpos).mpr
    have hdd : δ ≤ δs := by linarith
    have hphi : P ≤ T^((1:ℝ)/2+δs) :=
      hPhi.trans (Real.rpow_le_rpow_of_exponent_le hT (by linarith))
    have he : T^((1:ℝ)/2-q+δs)*T^q = T^((1:ℝ)/2+δs) := by
      rw [← Real.rpow_add hTp]
      congr 1
      ring
    have hh := mul_le_mul_of_nonneg_left hMlo (Real.rpow_nonneg hTp.le ((1:ℝ)/2-q+δs))
    rw [he] at hh
    linarith
  · have hj : 4*K*T^q ≤ δs*P := by
      have h := hjet.trans hPlo
      have hx : 4*K/δs*T^q = (4*K*T^q)/δs := by ring
      rw [hx] at h
      have hh := (div_le_iff₀ hδs).mp h
      nlinarith only [hh]
    have hm : K*(r:ℝ) ≤ K*(2*T^q) :=
      mul_le_mul_of_nonneg_left (hrM.le.trans hMhi) (zero_le_one.trans hK)
    have hh : K*(r:ℝ)/P ≤ δs/2 := by
      apply (div_le_iff₀ hPp).mpr
      nlinarith only [hj,hm]
    rw [mul_div_assoc] at hh
    linarith

private theorem endpoint_affine_sample {P : ℝ} {h r m : ℕ}
    (hP : P ≠ 0) (hr : P-(r:ℝ) ≠ 0) :
    aProcessShiftPoint ((r:ℝ)/P) 0 ((m:ℝ)/((P-r)/(h:ℝ))) =
      ((h*m+r:ℕ):ℝ)/P := by
  unfold aProcessShiftPoint
  push_cast
  field_simp
  ring

#print axioms endpoint_residue_scales
#print axioms endpoint_affine_sample


private theorem endpoint_beta_contract :
    IsExponentSumBoundNonAsymptotic (1/2) ((17:ℝ)/42) := by
  intro ε hε σ hσ
  let q : ℝ := min ((1:ℝ)/100) (ε/4)
  have hq : 0 < q := lt_min (by norm_num) (by positivity)
  have hqsmall : q ≤ (1:ℝ)/100 := min_le_left _ _
  have hqε : q ≤ ε/4 := min_le_right _ _
  let α : NNReal := ⟨(1:ℝ)/2-q,by linarith⟩
  have hαlo : (3:ℝ)/7 ≤ (α:ℝ) := by change (3:ℝ)/7 ≤ 1/2-q; linarith
  have hαhi : (α:ℝ) < (1:ℝ)/2 := by change (1:ℝ)/2-q < 1/2; linarith
  obtain ⟨δs,hδs,Q,hQ,C₀,hC₀,hsource⟩ :=
    isExponentSumBoundNonAsymptotic_bourgain_baseline_interior
      hαlo hαhi (ε/4) (by positivity) σ hσ
  obtain ⟨K,hK,hcompression⟩ := compression_model_phase hσ.le Q
  let δ : ℝ := min (δs/4) (q/4)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδs4 : δ ≤ δs/4 := min_le_left _ _
  have hδq : δ ≤ q/4 := min_le_right _ _
  have hgap : q < (1:ℝ)/2-δ := by linarith
  have hsize := eventually_const_mul_rpow_le_rpow (D := 8) hgap
  have habsorb := eventually_const_mul_rpow_le_rpow
    (D := 4) (a := (1:ℝ)/2-δs) (b := (1:ℝ)/2-δ) (by linarith)
  have hjet := eventually_const_mul_rpow_le_rpow (D := 4*K/δs) hgap
  obtain ⟨U,hU⟩ := eventually_atTop.mp (hsize.and (habsorb.and hjet))
  let C : ℝ := max 1 (max (4*C₀) U)
  have hC : 1 ≤ C := le_max_left _ _
  have hCC : 4*C₀ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hUC : U ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨δ,hδ,Q,hQ,C,hC,?_⟩
  intro T P G a b hs
  have hT : 1 ≤ T := hC.trans hs.threshold_le_param
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hPlo : T^((1:ℝ)/2-δ) ≤ P := by simpa using hs.rpow_sub_le_scale
  have hPhi : P ≤ T^((1:ℝ)/2+δ) := by simpa using hs.scale_le_rpow_add
  have hPp : 0 < P := (Real.rpow_pos_of_pos hTp _).trans_le hPlo
  obtain ⟨hsizeT,habsorbT,hjetT⟩ := hU T (hUC.trans hs.threshold_le_param)
  obtain ⟨hM1,hMhi,hscales⟩ := endpoint_residue_scales hT hq.le hδs
    (by linarith : δ ≤ δs/2) hK hPlo hPhi hsizeT habsorbT hjetT
  let M : ℕ := ⌈T^q⌉₊
  let B : ℝ := C₀*T^((13:ℝ)/84+(α:ℝ)/2+ε/4)
  have hB : 1 ≤ B := by
    exact one_le_mul_of_one_le_of_one_le hC₀ (Real.one_le_rpow hT (by positivity))
  have hC₀T : C₀ ≤ T := by linarith [hs.threshold_le_param]
  have hresidue (r : ℕ) (hr : r < M) (c d : ℕ)
      (hc : (P-r)/(M:ℝ) ≤ c) (hd : (d:ℝ) ≤ 2*((P-r)/(M:ℝ))) :
      ‖∑ m ∈ Finset.Icc c d, oscillatory G T P ((M*m+r:ℕ):ℝ)‖ ≤ B := by
    obtain ⟨hη,hη₁,hPrlo,hPrhi,hjetR⟩ := hscales r hr
    let Gr : ℝ → ℝ := fun v => G (aProcessShiftPoint ((r:ℝ)/P) 0 v)
    have hGr := hcompression G δ ((r:ℝ)/P) hδ.le hη hη₁ hs.isApproximateModelPhase
    have hGr' : IsApproximateModelPhaseFunction Gr σ Q δs :=
      approximateModelPhase_mono hGr le_rfl hjetR
    have hPrlo' : T^((α:ℝ)-δs) ≤ (P-r)/(M:ℝ) := hPrlo
    have hPrhi' : (P-r)/(M:ℝ) ≤ T^((α:ℝ)+δs) := hPrhi
    have hsetup : IsModelPhaseSumSetupAt (α:ℝ) σ δs Q C₀ T
        ((P-r)/(M:ℝ)) Gr c d :=
      ⟨hC₀T,hPrlo',hPrhi',hGr',hc,hd⟩
    have hh := hsource T ((P-r)/(M:ℝ)) Gr c d hsetup
    have hrP : (r:ℝ) < P := (div_lt_one hPp).mp hη₁
    have he : exponentialSumAt Gr T ((P-r)/(M:ℝ)) c d =
        ∑ m ∈ Finset.Icc c d, oscillatory G T P ((M*m+r:ℕ):ℝ) := by
      unfold exponentialSumAt
      apply Finset.sum_congr rfl
      intro m hm
      unfold oscillatory
      dsimp only [Gr]
      rw [endpoint_affine_sample hPp.ne' (sub_ne_zero.mpr hrP.ne')]
    rw [he] at hh
    exact hh
  have hsum := residue_interval_sum_bound (h := M)
    (by omega : 0 < M) (zero_le_one.trans hB) hs.scale_le_start hs.end_le_two_mul_scale
    (f := fun n => oscillatory G T P n) (fun n => by simp) hresidue
  change ‖exponentialSumAt G T P a b‖ ≤ _ at hsum
  have hexp : q+((13:ℝ)/84+(α:ℝ)/2+ε/4) ≤ (17:ℝ)/42+ε := by
    change q+((13:ℝ)/84+((1:ℝ)/2-q)/2+ε/4) ≤ (17:ℝ)/42+ε
    linarith
  calc
    ‖exponentialSumAt G T P a b‖ ≤ (M:ℝ)*(B+1) := hsum
    _ ≤ (2*T^q)*(2*B) := mul_le_mul hMhi (by linarith) (by linarith) (by positivity)
    _ = 4*C₀*T^(q+((13:ℝ)/84+(α:ℝ)/2+ε/4)) := by
      rw [Real.rpow_add hTp]
      dsimp only [B]
      ring
    _ ≤ C*T^((17:ℝ)/42+ε) :=
      mul_le_mul hCC (Real.rpow_le_rpow_of_exponent_le hT hexp)
        (Real.rpow_nonneg hTp.le _) (zero_le_one.trans hC)

#print axioms endpoint_beta_contract


/-- The baseline Bourgain supporting line includes the square-root endpoint. -/
private theorem closed_baseline_beta {α : NNReal}
    (hα : (3:ℝ)/7 ≤ (α:ℝ)) (hαupper : (α:ℝ) ≤ 1/2) :
    exponentSumGrowthExponent α ≤ (13:ℝ)/84+(α:ℝ)/2 := by
  rcases lt_or_eq_of_le hαupper with hlt|heq
  · exact exponentSumGrowthExponent_le_bourgain_baseline_interior hα hlt
  · have ha : α = (1/2:NNReal) := by
      ext
      simpa using heq
    subst α
    have hh := exponentSumGrowthExponent_le_iff_nonAsymptotic.mpr endpoint_beta_contract
    norm_num at hh ⊢
    exact hh

example : IsExponentSumBoundNonAsymptotic (1/2) ((17:ℝ)/42) := endpoint_beta_contract

example {α : NNReal} (hα : (3:ℝ)/7 ≤ (α:ℝ)) (hαupper : (α:ℝ) ≤ 1/2) :
    exponentSumGrowthExponent α ≤ (13:ℝ)/84+(α:ℝ)/2 :=
  closed_baseline_beta hα hαupper

example : exponentSumGrowthExponent (1/2) ≤ (17:ℝ)/42 := by
  have hh := closed_baseline_beta (α := 1/2) (by norm_num) (by norm_num)
  norm_num at hh ⊢
  exact hh

example : exponentSumGrowthExponent (3/7) ≤ (31:ℝ)/84 := by
  have hh := closed_baseline_beta (α := 3/7) (by norm_num) (by norm_num)
  norm_num at hh ⊢
  exact hh

#print axioms closed_baseline_beta

end TaoTrudgianYang2025.EndpointPrototype
