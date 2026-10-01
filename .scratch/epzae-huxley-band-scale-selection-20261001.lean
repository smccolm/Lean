import TaoTrudgianYang2025.HuxleyLinearForms

open scoped BigOperators
open Set Filter
open TaoTrudgianYang2025.HuxleyRationalPhase

namespace HuxleyBandScaleScratch

private theorem reference_floor_physical_budgets
    {N R Q B L : ℝ} (hR : 1 ≤ R) (hRQ : R ≤ Q) (hQN : Q ≤ N)
    (hNR : N ≤ R^2) (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hlarge : 2*B*L ≤ (N/Q)^((2:ℝ)/3)) :
    let U : ℕ := ⌊(N/Q)^((2:ℝ)/3)/B⌋₊
    1 ≤ U ∧ L ≤ (U:ℝ) ∧
      (N/Q)^((2:ℝ)/3)/(2*B) ≤ (U:ℝ) ∧
      (U:ℝ) ≤ (N/Q)^((2:ℝ)/3)/B ∧
      B^2*(U:ℝ)^3*R^2 ≤ N^2 ∧
      (U:ℝ) ≤ R^2 := by
  intro U
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hQ : 0 < Q := hRp.trans_le hRQ
  have hN : 0 < N := hQ.trans_le hQN
  have hBp : 0 < B := zero_lt_one.trans_le hB
  let scale := (N/Q)^((2:ℝ)/3)/B
  have hX2L : 2*L ≤ scale := (le_div_iff₀ hBp).mpr (by nlinarith only [hlarge])
  have hX2 : 2 ≤ scale := by linarith only [hX2L,hL]
  have hU : 1 ≤ U := (Nat.one_le_floor_iff scale).mpr (by linarith only [hX2])
  have hUle : (U:ℝ) ≤ scale := Nat.floor_le (by linarith only [hX2])
  have hUlower : scale/2 ≤ (U:ℝ) := by
    have hh := Nat.lt_floor_add_one scale
    change scale < (U:ℝ)+1 at hh
    linarith only [hh,hX2]
  have hUL : L ≤ (U:ℝ) := by linarith only [hX2L,hUlower]
  have hpow : ((N/Q)^((2:ℝ)/3))^3=(N/Q)^2 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (div_pos hN hQ).le]
    norm_num
  have hcube : B^3*(U:ℝ)^3*Q^2 ≤ N^2 := by
    have hh := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Nat.cast_nonneg U) hUle 3)
      (show 0 ≤ B^3*Q^2 by positivity)
    have he : (B^3*Q^2)*scale^3=N^2 := by
      dsimp only [scale]
      rw [div_pow,hpow,div_pow]
      field_simp
    rw [he] at hh
    nlinarith only [hh]
  have hlinear : B*(U:ℝ)*Q ≤ N := by
    have hratio : 1 ≤ N/Q := (one_le_div hQ).mpr hQN
    have hp := Real.rpow_le_self_of_one_le hratio (by norm_num : (2:ℝ)/3 ≤ 1)
    have hh := mul_le_mul_of_nonneg_left hUle hBp.le
    have he : B*scale=(N/Q)^((2:ℝ)/3) := by dsimp only [scale]; field_simp
    rw [he] at hh
    exact (le_div_iff₀ hQ).mp (hh.trans hp)
  have hnowrap : B^2*(U:ℝ)^3*R^2 ≤ N^2 := by
    have hBpow : B^2 ≤ B^3 := by
      have hh := mul_le_mul_of_nonneg_left hB (sq_nonneg B)
      nlinarith only [hh]
    calc
      _ ≤ B^3*(U:ℝ)^3*Q^2 := by gcongr
      _ ≤ _ := hcube
  have hUN : (U:ℝ) ≤ N := by
    calc
      (U:ℝ) = 1*(U:ℝ)*1 := by ring
      _ ≤ B*(U:ℝ)*Q := by gcongr; exact hR.trans hRQ
      _ ≤ N := hlinear
  refine ⟨hU,hUL,?_,hUle,hnowrap,hUN.trans hNR⟩
  convert hUlower using 1
  dsimp only [scale]
  ring

private theorem dyadic_band_integer_physical_selection
    (N : ℕ) {σ J R B L Cbase qcap Dcap : ℝ}
    (hσ : 0 < σ) (hR : 1 ≤ R) (hRN : R ≤ N) (hNR : (N:ℝ) ≤ R^2)
    (hB : 1 ≤ B) (hL : 1 ≤ L) (hCbase : 768 ≤ Cbase)
    (hcap : 0 < qcap) (hcapOne : qcap ≤ 1)
    (hlarge : qcap*(2*B*L)^((3:ℝ)/2) ≤ 1)
    (hDcap : 0 ≤ Dcap) (hsmall : 4*Dcap*qcap ≤ 1)
    (hroom : 2*Cbase*R ≤ qcap*(N:ℝ)) :
    ∃ (Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ),
      let Q := fun k : ℕ => Qbase*2^k
      Cbase*R ≤ Qbase ∧ (Qbase:ℝ) ≤ 2*Cbase*R ∧
      qcap*(N:ℝ)/2 ≤ Q kmax ∧ (Q kmax:ℝ) ≤ qcap*(N:ℝ) ∧
      (kmax:ℝ) ≤ Real.log N/Real.log 2 ∧
      (∀ k, 0 < Kmesh k) ∧
      (∀ k ≤ kmax,
        L ≤ (Usel k:ℝ) ∧
        63*(J/(2*σ*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
        (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
        (Kmesh k:ℝ) ≤ 2*(max 1 (63*J/(2*σ)))*(Q k:ℝ)*(N:ℝ)/R^2 ∧
        1 ≤ Usel k ∧
        B^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
        (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/B ∧
        ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*B) ≤ (Usel k:ℝ) ∧
        Q k ≤ N ∧ (Usel k:ℝ) ≤ R^2 ∧
        768*R ≤ (Q k:ℝ) ∧ 2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧
        Dcap*(Q k:ℝ)/(N:ℝ) ≤ 1/4) ∧
      (∀ k, Usel k ≤ Usel 0) := by
  classical
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hNp : (0:ℝ) < N := hRp.trans_le hRN
  have hCp : 0 < Cbase := by linarith only [hCbase]
  have hCR : 1 ≤ Cbase*R := by nlinarith only [hCbase,hR]
  let Qbase : ℕ := ⌈Cbase*R⌉₊
  have hQlo : Cbase*R ≤ (Qbase:ℝ) := Nat.le_ceil _
  have hQhi : (Qbase:ℝ) ≤ 2*Cbase*R := by
    have hh := Nat.ceil_lt_add_one (mul_pos hCp hRp).le
    change (Qbase:ℝ) < Cbase*R+1 at hh
    linarith only [hh,hCR]
  have hQp : (0:ℝ) < Qbase := (mul_pos hCp hRp).trans_le hQlo
  have hratio : 1 ≤ qcap*(N:ℝ)/(Qbase:ℝ) :=
    (le_div_iff₀ hQp).mpr (by simpa only [one_mul] using hQhi.trans hroom)
  obtain ⟨kmax,hklo,hkhi⟩ := exists_nat_pow_near hratio (by norm_num : (1:ℝ) < 2)
  let Q := fun k : ℕ => Qbase*2^k
  have hQcast k : (Q k:ℝ)=(Qbase:ℝ)*(2:ℝ)^k := by simp only [Q,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  have hQbase k : (Qbase:ℝ) ≤ Q k := by
    rw [hQcast]
    exact le_mul_of_one_le_right hQp.le (one_le_pow₀ (by norm_num))
  have hQpos k : (0:ℝ) < Q k := hQp.trans_le (hQbase k)
  have hQupper : (Q kmax:ℝ) ≤ qcap*(N:ℝ) := by
    rw [hQcast]
    have hh := (le_div_iff₀ hQp).mp hklo
    simpa only [mul_comm] using hh
  have hQlower : qcap*(N:ℝ)/2 ≤ Q kmax := by
    have hh := (div_lt_iff₀ hQp).mp hkhi
    rw [pow_succ] at hh
    rw [hQcast]
    nlinarith only [hh]
  have hQmono k (hk : k ≤ kmax) : Q k ≤ Q kmax := by
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hk)
  have hQN k (hk : k ≤ kmax) : Q k ≤ N := by
    have hh : (Q k:ℝ) ≤ N :=
      (by exact_mod_cast hQmono k hk : (Q k:ℝ) ≤ Q kmax).trans (hQupper.trans (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hcapOne hNp.le))
    exact_mod_cast hh
  have hstrong k : 768*R ≤ (Q k:ℝ) :=
    (mul_le_mul_of_nonneg_right hCbase hRp.le).trans (hQlo.trans (hQbase k))
  have hRQ k : R ≤ (Q k:ℝ) := by
    have hh := hstrong k
    linarith only [hh,hRp]
  have hminscale k : 2*R^2 ≤ (Q k:ℝ)*(N:ℝ) := by
    have hh := mul_le_mul (hstrong k) hRN hRp.le (hQpos k).le
    nlinarith only [hh,sq_nonneg R]
  have hmesh k := exists_positive_difference_source_fourier_mesh
    (J:=J) hσ hNp hRp (hQpos k) (by
      have hh := hminscale k
      linarith only [hh,sq_nonneg R])
  choose Kmesh hK hSource hMesh hMeshUpper using hmesh
  let Usel := fun k => ⌊((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/B⌋₊
  have hUdata k (hk : k ≤ kmax) :=
    reference_floor_physical_budgets (N:=(N:ℝ)) (B:=B) (L:=L)
      hR (hRQ k) (by exact_mod_cast hQN k hk) hNR hB hL (by
        have hqcap : (Q k:ℝ) ≤ qcap*(N:ℝ) :=
          (by exact_mod_cast hQmono k hk : (Q k:ℝ) ≤ Q kmax).trans hQupper
        have hratioLower : 1/qcap ≤ (N:ℝ)/(Q k:ℝ) := by
          apply (div_le_div_iff₀ hcap (hQpos k)).mpr
          nlinarith only [hqcap]
        have hpowle : (2*B*L)^((3:ℝ)/2) ≤ (N:ℝ)/(Q k:ℝ) :=
          ((le_div_iff₀ hcap).mpr (by nlinarith only [hlarge])).trans hratioLower
        have hh := (Real.le_rpow_inv_iff_of_pos
          (by positivity : (0:ℝ) ≤ 2*B*L)
          (div_pos hNp (hQpos k)).le (by norm_num : (0:ℝ) < 3/2)).mpr hpowle
        norm_num only [show ((3:ℝ)/2)⁻¹=2/3 by norm_num] at hh
        exact hh)
  have hUmono k : Usel k ≤ Usel 0 := by
    apply Nat.floor_mono
    apply div_le_div_of_nonneg_right _ (zero_le_one.trans hB)
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    apply div_le_div_of_nonneg_left hNp.le (hQpos 0)
    simpa only [Q,pow_zero,mul_one] using hQbase k
  have hklog : (kmax:ℝ) ≤ Real.log N/Real.log 2 := by
    have hQone : (1:ℝ) ≤ Qbase := hCR.trans hQlo
    have hpowN : (2:ℝ)^kmax ≤ N := by
      have hh : (2:ℝ)^kmax ≤ (Q kmax:ℝ) := by
        rw [hQcast]
        exact le_mul_of_one_le_left (by positivity) hQone
      exact hh.trans (by exact_mod_cast hQN kmax le_rfl)
    have hh := Real.log_le_log (by positivity : (0:ℝ) < (2:ℝ)^kmax) hpowN
    rw [Real.log_pow] at hh
    exact (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mpr hh
  refine ⟨Qbase,kmax,Kmesh,Usel,hQlo,hQhi,hQlower,hQupper,hklog,hK,?_,hUmono⟩
  intro k hk
  obtain ⟨hU,hUL,hUlower,hUupper,hwrap,hUR⟩ := hUdata k hk
  refine ⟨hUL,hSource k,hMesh k,hMeshUpper k,hU,hwrap,hUupper,hUlower,
    hQN k hk,hUR,hstrong k,hminscale k,?_⟩
  have hqcap : (Q k:ℝ) ≤ qcap*(N:ℝ) :=
    (by exact_mod_cast hQmono k hk : (Q k:ℝ) ≤ Q kmax).trans hQupper
  apply (div_le_iff₀ hNp).mpr
  have hh := mul_le_mul_of_nonneg_left hqcap hDcap
  have hs := mul_le_mul_of_nonneg_right hsmall hNp.le
  nlinarith only [hh,hs]

example
    {N R Q B L : ℝ} (hR : 1 ≤ R) (hRQ : R ≤ Q) (hQN : Q ≤ N)
    (hNR : N ≤ R^2) (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hlarge : 2*B*L ≤ (N/Q)^((2:ℝ)/3)) :
    let U : ℕ := ⌊(N/Q)^((2:ℝ)/3)/B⌋₊
    1 ≤ U ∧ L ≤ (U:ℝ) ∧
      (N/Q)^((2:ℝ)/3)/(2*B) ≤ (U:ℝ) ∧
      (U:ℝ) ≤ (N/Q)^((2:ℝ)/3)/B ∧
      B^2*(U:ℝ)^3*R^2 ≤ N^2 ∧
      (U:ℝ) ≤ R^2 :=
  HuxleyBandScaleScratch.reference_floor_physical_budgets (N:=N) (R:=R) (Q:=Q) (B:=B) (L:=L) hR hRQ hQN hNR hB hL hlarge

example
    (N : ℕ) {σ J R B L Cbase qcap Dcap : ℝ}
    (hσ : 0 < σ) (hR : 1 ≤ R) (hRN : R ≤ N) (hNR : (N:ℝ) ≤ R^2)
    (hB : 1 ≤ B) (hL : 1 ≤ L) (hCbase : 768 ≤ Cbase)
    (hcap : 0 < qcap) (hcapOne : qcap ≤ 1)
    (hlarge : qcap*(2*B*L)^((3:ℝ)/2) ≤ 1)
    (hDcap : 0 ≤ Dcap) (hsmall : 4*Dcap*qcap ≤ 1)
    (hroom : 2*Cbase*R ≤ qcap*(N:ℝ)) :
    ∃ (Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ),
      let Q := fun k : ℕ => Qbase*2^k
      Cbase*R ≤ Qbase ∧ (Qbase:ℝ) ≤ 2*Cbase*R ∧
      qcap*(N:ℝ)/2 ≤ Q kmax ∧ (Q kmax:ℝ) ≤ qcap*(N:ℝ) ∧
      (kmax:ℝ) ≤ Real.log N/Real.log 2 ∧
      (∀ k, 0 < Kmesh k) ∧
      (∀ k ≤ kmax,
        L ≤ (Usel k:ℝ) ∧
        63*(J/(2*σ*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
        (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
        (Kmesh k:ℝ) ≤ 2*(max 1 (63*J/(2*σ)))*(Q k:ℝ)*(N:ℝ)/R^2 ∧
        1 ≤ Usel k ∧
        B^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
        (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/B ∧
        ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*B) ≤ (Usel k:ℝ) ∧
        Q k ≤ N ∧ (Usel k:ℝ) ≤ R^2 ∧
        768*R ≤ (Q k:ℝ) ∧ 2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧
        Dcap*(Q k:ℝ)/(N:ℝ) ≤ 1/4) ∧
      (∀ k, Usel k ≤ Usel 0) :=
  HuxleyBandScaleScratch.dyadic_band_integer_physical_selection N (σ:=σ) (J:=J) (R:=R) (B:=B) (L:=L) (Cbase:=Cbase) (qcap:=qcap) (Dcap:=Dcap) hσ hR hRN hNR hB hL hCbase hcap hcapOne hlarge hDcap hsmall hroom

#print axioms HuxleyBandScaleScratch.reference_floor_physical_budgets
#print axioms HuxleyBandScaleScratch.dyadic_band_integer_physical_selection

private theorem exists_uniform_dyadic_band_integer_scales
    {σ J B D₀ D₁ : ℝ} (hσ : 0 < σ)
    (hB : 1 ≤ B) (hD₀ : 0 ≤ D₀) (hD₁ : 0 ≤ D₁) :
    ∃ Csep : ℝ, 1 ≤ Csep ∧
      ∀ (N : ℕ) (R : ℝ), 1 ≤ R → (N:ℝ) ≤ R^2 → Csep*R ≤ N →
      ∃ (Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ),
        let Q := fun k : ℕ => Qbase*2^k
        (768:ℝ)*R ≤ Qbase ∧ (Qbase:ℝ) ≤ 1536*R ∧
        (N:ℝ)/Csep ≤ Q kmax ∧ (Q kmax:ℝ) ≤ N ∧
        (kmax:ℝ) ≤ Real.log N/Real.log 2 ∧
        (∀ k, 0 < Kmesh k) ∧
        (∀ k ≤ kmax,
          12*J ≤ σ*(Usel k:ℝ) ∧
          63*(J/(2*σ*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
          (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
          (Kmesh k:ℝ) ≤ 2*(max 1 (63*J/(2*σ)))*(Q k:ℝ)*(N:ℝ)/R^2 ∧
          1 ≤ Usel k ∧
          B^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
          (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/B ∧
          ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*B) ≤ (Usel k:ℝ) ∧
          Q k ≤ N ∧ (Usel k:ℝ) ≤ R^2 ∧
          768*R ≤ (Q k:ℝ) ∧ 2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧
          D₀*(Q k:ℝ)/(N:ℝ)+D₁*(2*(Q k:ℝ))/(N:ℝ) ≤ 1/2 ∧
          D₀*(Q k:ℝ)/(N:ℝ) < 1/2) ∧
        (∀ k, Usel k ≤ Usel 0) := by
  let L := max 1 (12*J/σ)
  let Dcap := D₀+2*D₁
  let qcap := 1/(4*Dcap+(2*B*L)^((3:ℝ)/2)+1)
  let Csep := 1536/qcap
  have hL : 1 ≤ L := le_max_left _ _
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hDc : 0 ≤ Dcap := by dsimp only [Dcap]; positivity
  have hpow : 0 < (2*B*L)^((3:ℝ)/2) := by positivity
  have hden : 0 < 4*Dcap+(2*B*L)^((3:ℝ)/2)+1 := by positivity
  have hcap : 0 < qcap := by dsimp only [qcap]; positivity
  have hcapOne : qcap ≤ 1 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hDc,hpow]
  have hlarge : qcap*(2*B*L)^((3:ℝ)/2) ≤ 1 := by
    dsimp only [qcap]
    rw [one_div,mul_comm,←div_eq_mul_inv]
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hDc]
  have hsmall : 4*Dcap*qcap ≤ 1 := by
    dsimp only [qcap]
    rw [one_div,←div_eq_mul_inv]
    apply (div_le_iff₀ hden).mpr
    linarith only [hpow]
  have hCsep : 1 ≤ Csep := by
    apply (le_div_iff₀ hcap).mpr
    linarith only [hcapOne]
  refine ⟨Csep,hCsep,?_⟩
  intro N R hR hNR hroom
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hRN : R ≤ N :=
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hCsep hRp.le : R ≤ Csep*R).trans hroom
  have hNp : (0:ℝ) < N := hRp.trans_le hRN
  have hroom' : 2*(768:ℝ)*R ≤ qcap*(N:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hroom hcap.le
    have he : qcap*(Csep*R)=1536*R := by dsimp only [Csep]; field_simp
    rw [he] at hh
    nlinarith only [hh]
  obtain ⟨Qbase,kmax,Kmesh,Usel,hQlo,hQhi,hQlast,hQlastHi,hlog,hK,hvalid,hmono⟩ :=
    dyadic_band_integer_physical_selection N (J:=J) hσ hR hRN hNR hB hL
      (by norm_num : (768:ℝ) ≤ 768) hcap hcapOne hlarge hDc hsmall hroom'
  refine ⟨Qbase,kmax,Kmesh,Usel,hQlo,by simpa only [show (2:ℝ)*768=1536 by norm_num] using hQhi,
    ?_,?_,hlog,hK,?_,hmono⟩
  · have hh : (N:ℝ)/Csep ≤ qcap*(N:ℝ)/2 := by
      have he : (N:ℝ)/Csep=qcap*(N:ℝ)/1536 := by
        dsimp only [Csep]
        field_simp
      rw [he]
      exact div_le_div_of_nonneg_left (mul_pos hcap hNp).le
        (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≤ 1536)
    exact hh.trans hQlast
  · exact hQlastHi.trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hcapOne hNp.le)
  · intro k hk
    obtain ⟨hUL,hSource,hMesh,hMeshUpper,hU,hwrap,hUupper,hUlower,hQN,hUR,hStrong,hMin,hD⟩ :=
      hvalid k hk
    have hULarge : 12*J ≤ σ*(Usel k:ℝ) := by
      have hh := (le_max_right (1:ℝ) (12*J/σ)).trans hUL
      have hh' := (div_le_iff₀ hσ).mp hh
      simpa only [mul_comm] using hh'
    have hDsum : D₀*(Qbase*2^k:ℕ)/(N:ℝ)+
        D₁*(2*(Qbase*2^k:ℕ))/(N:ℝ) ≤ 1/4 := by
      convert hD using 1
      dsimp only [Dcap]
      ring
    have hDlow : 0 ≤ D₁*(2*(Qbase*2^k:ℕ))/(N:ℝ) := by positivity
    refine ⟨hULarge,hSource,hMesh,hMeshUpper,hU,hwrap,hUupper,hUlower,
      hQN,hUR,hStrong,hMin,?_,?_⟩ <;> linarith only [hDsum,hDlow]


example
    {σ J B D₀ D₁ : ℝ} (hσ : 0 < σ)
    (hB : 1 ≤ B) (hD₀ : 0 ≤ D₀) (hD₁ : 0 ≤ D₁) :
    ∃ Csep : ℝ, 1 ≤ Csep ∧
      ∀ (N : ℕ) (R : ℝ), 1 ≤ R → (N:ℝ) ≤ R^2 → Csep*R ≤ N →
      ∃ (Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ),
        let Q := fun k : ℕ => Qbase*2^k
        (768:ℝ)*R ≤ Qbase ∧ (Qbase:ℝ) ≤ 1536*R ∧
        (N:ℝ)/Csep ≤ Q kmax ∧ (Q kmax:ℝ) ≤ N ∧
        (kmax:ℝ) ≤ Real.log N/Real.log 2 ∧
        (∀ k, 0 < Kmesh k) ∧
        (∀ k ≤ kmax,
          12*J ≤ σ*(Usel k:ℝ) ∧
          63*(J/(2*σ*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
          (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
          (Kmesh k:ℝ) ≤ 2*(max 1 (63*J/(2*σ)))*(Q k:ℝ)*(N:ℝ)/R^2 ∧
          1 ≤ Usel k ∧
          B^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
          (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/B ∧
          ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*B) ≤ (Usel k:ℝ) ∧
          Q k ≤ N ∧ (Usel k:ℝ) ≤ R^2 ∧
          768*R ≤ (Q k:ℝ) ∧ 2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧
          D₀*(Q k:ℝ)/(N:ℝ)+D₁*(2*(Q k:ℝ))/(N:ℝ) ≤ 1/2 ∧
          D₀*(Q k:ℝ)/(N:ℝ) < 1/2) ∧
        (∀ k, Usel k ≤ Usel 0) :=
  HuxleyBandScaleScratch.exists_uniform_dyadic_band_integer_scales (σ:=σ) (J:=J) (B:=B) (D₀:=D₀) (D₁:=D₁) hσ hB hD₀ hD₁

#print axioms HuxleyBandScaleScratch.exists_uniform_dyadic_band_integer_scales

private theorem selected_band_prefactor_identity
    {R Q N M Cmesh Ccard Y : ℝ}
    (hR : R ≠ 0) (hQ : Q ≠ 0) (hN : N ≠ 0) :
    (R^2/Q)^6*(Cmesh*Q*N/R^2)^12*(Ccard*Y*M*R^2/(N*Q^2))^10 =
      Cmesh^12*Ccard^10*Y^10*M^10*N^2*R^8/Q^14 := by
  field_simp


example
    {R Q N M Cmesh Ccard Y : ℝ}
    (hR : R ≠ 0) (hQ : Q ≠ 0) (hN : N ≠ 0) :
    (R^2/Q)^6*(Cmesh*Q*N/R^2)^12*(Ccard*Y*M*R^2/(N*Q^2))^10 =
      Cmesh^12*Ccard^10*Y^10*M^10*N^2*R^8/Q^14 :=
  HuxleyBandScaleScratch.selected_band_prefactor_identity (R:=R) (Q:=Q) (N:=N) (M:=M) (Cmesh:=Cmesh) (Ccard:=Ccard) (Y:=Y) hR hQ hN

#print axioms HuxleyBandScaleScratch.selected_band_prefactor_identity


private theorem physical_mesh_type_spacing_bound
    {α Cmesh N R Q K : ℝ}
    (hα : 0 ≤ α) (hC : 0 ≤ Cmesh) (hN : 0 < N)
    (hR : 0 < R) (hQ : 0 < Q) (hK : 0 < K)
    (hmesh : Q*N ≤ K*R^2)
    (hupper : K ≤ Cmesh*Q*N/R^2) :
    Real.sqrt ((α/(N*R^2))*Q^3)*Real.sqrt K/K^2 ≤
      Real.sqrt (α*Cmesh)*R^2/N^2 := by
  have hprod : (α/(N*R^2))*Q^3*K ≤ α*Cmesh*(Q^2/R^2)^2 := by
    calc
      _ ≤ (α/(N*R^2))*Q^3*(Cmesh*Q*N/R^2) :=
        mul_le_mul_of_nonneg_left hupper (by positivity)
      _ = _ := by field_simp
  have hroot :
      Real.sqrt ((α/(N*R^2))*Q^3)*Real.sqrt K ≤
        Real.sqrt (α*Cmesh)*(Q^2/R^2) := by
    rw [←Real.sqrt_mul (by positivity : 0 ≤ (α/(N*R^2))*Q^3)]
    calc
      _ ≤ Real.sqrt (α*Cmesh*(Q^2/R^2)^2) := Real.sqrt_le_sqrt hprod
      _ = _ := by
        rw [Real.sqrt_mul (mul_nonneg hα hC),
          Real.sqrt_sq (by positivity : 0 ≤ Q^2/R^2)]
  have hsq := pow_le_pow_left₀ (mul_pos hQ hN).le hmesh 2
  have hquot : Q^2/R^2/K^2 ≤ R^2/N^2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hK) (sq_pos_of_pos hN)).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (sq_pos_of_pos hR)).mpr
    convert hsq using 1 <;> ring
  calc
    _ ≤ (Real.sqrt (α*Cmesh)*(Q^2/R^2))/K^2 :=
      div_le_div_of_nonneg_right hroot (sq_nonneg K)
    _ = Real.sqrt (α*Cmesh)*(Q^2/R^2/K^2) := by ring
    _ ≤ Real.sqrt (α*Cmesh)*(R^2/N^2) :=
      mul_le_mul_of_nonneg_left hquot (Real.sqrt_nonneg _)
    _ = _ := by ring

private theorem physical_band_logarithmic_bounds
    {Carg Cmesh T N R Q K kmax : ℝ}
    (hCarg : 0 ≤ Carg) (hCmesh : 1 ≤ Cmesh)
    (hT : 1 ≤ T) (hR : 1 ≤ R) (hRQ : R ≤ Q)
    (hQN : Q ≤ N) (hNR : N ≤ R^2) (hNT : N ≤ T)
    (hK : 0 < K) (hKupper : K ≤ Cmesh*Q*N/R^2)
    (hkmax : kmax ≤ Real.log N/Real.log 2) :
    2+Real.log (Carg*R^2/Q+1) ≤ (3+Real.log (Carg+1))*(1+Real.log T) ∧
    1+Real.log K ≤ (3+Real.log (Cmesh+1))*(1+Real.log T) ∧
    kmax+2 ≤ (2+1/Real.log 2)*(1+Real.log T) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hQ : 0 < Q := hRp.trans_le hRQ
  have hN : 0 < N := hQ.trans_le hQN
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hlinear (C z : ℝ) (hC : 0 ≤ C) (hz : 0 ≤ z) (hzT : z ≤ C*T) :
      2+Real.log (z+1) ≤ (3+Real.log (C+1))*(1+Real.log T) := by
    have hCp : 0 < C+1 := by linarith only [hC]
    have hbound : z+1 ≤ (C+1)*T := by nlinarith only [hzT,hT]
    have hh := Real.log_le_log (by linarith only [hz] : 0 < z+1) hbound
    rw [Real.log_mul hCp.ne' hTp.ne'] at hh
    have hlogC : 0 ≤ Real.log (C+1) := Real.log_nonneg (by linarith only [hC])
    nlinarith only [hh,hlogC,hlogT,mul_nonneg hlogC hlogT]
  have hRT : R ≤ T := hRQ.trans (hQN.trans hNT)
  have hRquot : R^2/Q ≤ R := (div_le_iff₀ hQ).mpr (by
    nlinarith only [mul_le_mul_of_nonneg_left hRQ hRp.le])
  have harg : Carg*R^2/Q ≤ Carg*T := by
    calc
      _ = Carg*(R^2/Q) := by ring
      _ ≤ Carg*T := mul_le_mul_of_nonneg_left (hRquot.trans hRT) hCarg
  have hKT : K ≤ Cmesh*T := by
    calc
      _ ≤ Cmesh*Q*N/R^2 := hKupper
      _ ≤ Cmesh*Q := (div_le_iff₀ (sq_pos_of_pos hRp)).mpr
        (mul_le_mul_of_nonneg_left hNR (by positivity))
      _ ≤ Cmesh*T := mul_le_mul_of_nonneg_left (hQN.trans hNT) (by positivity)
  refine ⟨hlinear Carg _ hCarg (by positivity) harg,?_,?_⟩
  · have hh := hlinear Cmesh K (by positivity) hK.le hKT
    have hlogK := Real.log_le_log hK (by linarith : K ≤ K+1)
    linarith only [hh,hlogK]
  · have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogN := Real.log_le_log hN hNT
    have hq := div_le_div_of_nonneg_right hlogN hlog2.le
    have hh := hkmax.trans hq
    have he : (2+1/Real.log 2)*(1+Real.log T) =
        2+Real.log T/Real.log 2+2*Real.log T+1/Real.log 2 := by ring
    rw [he]
    nlinarith only [hh,hlogT,one_div_pos.mpr hlog2]

example
    {α Cmesh N R Q K : ℝ}
    (hα : 0 ≤ α) (hC : 0 ≤ Cmesh) (hN : 0 < N)
    (hR : 0 < R) (hQ : 0 < Q) (hK : 0 < K)
    (hmesh : Q*N ≤ K*R^2)
    (hupper : K ≤ Cmesh*Q*N/R^2) :
    Real.sqrt ((α/(N*R^2))*Q^3)*Real.sqrt K/K^2 ≤
      Real.sqrt (α*Cmesh)*R^2/N^2 :=
  HuxleyBandScaleScratch.physical_mesh_type_spacing_bound (α:=α) (Cmesh:=Cmesh) (N:=N) (R:=R) (Q:=Q) (K:=K) hα hC hN hR hQ hK hmesh hupper

example
    {Carg Cmesh T N R Q K kmax : ℝ}
    (hCarg : 0 ≤ Carg) (hCmesh : 1 ≤ Cmesh)
    (hT : 1 ≤ T) (hR : 1 ≤ R) (hRQ : R ≤ Q)
    (hQN : Q ≤ N) (hNR : N ≤ R^2) (hNT : N ≤ T)
    (hK : 0 < K) (hKupper : K ≤ Cmesh*Q*N/R^2)
    (hkmax : kmax ≤ Real.log N/Real.log 2) :
    2+Real.log (Carg*R^2/Q+1) ≤ (3+Real.log (Carg+1))*(1+Real.log T) ∧
    1+Real.log K ≤ (3+Real.log (Cmesh+1))*(1+Real.log T) ∧
    kmax+2 ≤ (2+1/Real.log 2)*(1+Real.log T) :=
  HuxleyBandScaleScratch.physical_band_logarithmic_bounds (Carg:=Carg) (Cmesh:=Cmesh) (T:=T) (N:=N) (R:=R) (Q:=Q) (K:=K) (kmax:=kmax) hCarg hCmesh hT hR hRQ hQN hNR hNT hK hKupper hkmax


#print axioms HuxleyBandScaleScratch.physical_mesh_type_spacing_bound
#print axioms HuxleyBandScaleScratch.physical_band_logarithmic_bounds


private theorem positive_difference_source_type_spacing_bound
    {σ c J T M N R Q K Cmesh : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 ≤ J)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N)
    (hR : 0 < R) (hQ : 0 < Q) (hK : 0 < K) (hC : 0 ≤ Cmesh)
    (hscale : T*N*R^2=M^3)
    (hmesh : Q*N ≤ K*R^2) (hupper : K ≤ Cmesh*Q*N/R^2) :
    let μ₀ := c*T/(12*σ*M^3)
    let U₀ := J*T/(2*σ*M^3)
    (16*U₀/μ₀)*Real.sqrt (U₀*Q^3)*Real.sqrt K/(6*K^2) ≤
      (16*J/c)*Real.sqrt ((J/(2*σ))*Cmesh)*R^2/N^2 := by
  intro μ₀ U₀
  have hU : U₀=(J/(2*σ))/(N*R^2) := by
    dsimp only [U₀]
    rw [←hscale]
    field_simp
  have hratio : 16*U₀/μ₀=96*J/c := by
    dsimp only [U₀,μ₀]
    field_simp
    ring
  have hh := physical_mesh_type_spacing_bound
    (show 0 ≤ J/(2*σ) by positivity) hC hN hR hQ hK hmesh hupper
  calc
    _ = (16*J/c)*(Real.sqrt (((J/(2*σ))/(N*R^2))*Q^3)*Real.sqrt K/K^2) := by
      rw [hratio,hU]
      ring
    _ ≤ (16*J/c)*(Real.sqrt ((J/(2*σ))*Cmesh)*R^2/N^2) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

private theorem physical_denominator_rpow_decay
    {R Q N s : ℝ} (p : ℕ)
    (hR : 0 < R) (hRQ : R ≤ Q) (hN : 0 < N) (hs : s ≤ p) :
    (Q/N)^s/Q^p ≤ (R/N)^s/R^p := by
  have hQ : 0 < Q := hR.trans_le hRQ
  have hh := Real.rpow_le_rpow_of_nonpos hR hRQ (sub_nonpos.mpr hs)
  rw [Real.rpow_sub_natCast hQ.ne',Real.rpow_sub_natCast hR.ne'] at hh
  calc
    _ = (Q^s/Q^p)/N^s := by
      rw [Real.div_rpow hQ.le hN.le]
      ring
    _ ≤ (R^s/R^p)/N^s :=
      div_le_div_of_nonneg_right hh (Real.rpow_nonneg hN.le _)
    _ = _ := by
      rw [Real.div_rpow hR.le hN.le]
      ring

private theorem physical_reference_reciprocal_bound
    {N Q B U : ℝ} (hN : 0 < N) (hQ : 0 < Q) (hB : 0 < B)
    (hU : (N/Q)^((2:ℝ)/3)/(2*B) ≤ U) :
    0 < U ∧ 1/U ≤ 2*B*(Q/N)^((2:ℝ)/3) := by
  have hlow : 0 < (N/Q)^((2:ℝ)/3)/(2*B) := by positivity
  refine ⟨hlow.trans_le hU,?_⟩
  calc
    _ ≤ 1/((N/Q)^((2:ℝ)/3)/(2*B)) :=
      one_div_le_one_div_of_le hlow hU
    _ = _ := by
      rw [Real.div_rpow hN.le hQ.le,Real.div_rpow hQ.le hN.le]
      field_simp

example
    {σ c J T M N R Q K Cmesh : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 ≤ J)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N)
    (hR : 0 < R) (hQ : 0 < Q) (hK : 0 < K) (hC : 0 ≤ Cmesh)
    (hscale : T*N*R^2=M^3)
    (hmesh : Q*N ≤ K*R^2) (hupper : K ≤ Cmesh*Q*N/R^2) :
    let μ₀ := c*T/(12*σ*M^3)
    let U₀ := J*T/(2*σ*M^3)
    (16*U₀/μ₀)*Real.sqrt (U₀*Q^3)*Real.sqrt K/(6*K^2) ≤
      (16*J/c)*Real.sqrt ((J/(2*σ))*Cmesh)*R^2/N^2 :=
  HuxleyBandScaleScratch.positive_difference_source_type_spacing_bound (σ:=σ) (c:=c) (J:=J) (T:=T) (M:=M) (N:=N) (R:=R) (Q:=Q) (K:=K) (Cmesh:=Cmesh) hσ hc hJ hT hM hN hR hQ hK hC hscale hmesh hupper

example
    {R Q N s : ℝ} (p : ℕ)
    (hR : 0 < R) (hRQ : R ≤ Q) (hN : 0 < N) (hs : s ≤ p) :
    (Q/N)^s/Q^p ≤ (R/N)^s/R^p :=
  HuxleyBandScaleScratch.physical_denominator_rpow_decay (R:=R) (Q:=Q) (N:=N) (s:=s) p hR hRQ hN hs

example
    {N Q B U : ℝ} (hN : 0 < N) (hQ : 0 < Q) (hB : 0 < B)
    (hU : (N/Q)^((2:ℝ)/3)/(2*B) ≤ U) :
    0 < U ∧ 1/U ≤ 2*B*(Q/N)^((2:ℝ)/3) :=
  HuxleyBandScaleScratch.physical_reference_reciprocal_bound (N:=N) (Q:=Q) (B:=B) (U:=U) hN hQ hB hU


#print axioms HuxleyBandScaleScratch.positive_difference_source_type_spacing_bound
#print axioms HuxleyBandScaleScratch.physical_denominator_rpow_decay
#print axioms HuxleyBandScaleScratch.physical_reference_reciprocal_bound


private theorem upper_physical_family_monomial_bound
    {Y M N R Q U V Jsep D Cdelta Cupper Cv B delta : ℝ}
    (hY : 0 ≤ Y) (hM : 0 ≤ M) (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q)
    (hJ : 0 ≤ Jsep) (hD : 0 ≤ D) (hCd : 0 ≤ Cdelta)
    (hCu : 0 ≤ Cupper) (hCv : 0 ≤ Cv) (hB : 0 < B) (hd : 0 ≤ delta)
    (hVupper : V ≤ Cv*R^4/N^2) (hdelta : delta ≤ Cdelta*R^2/N^2)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B) ≤ U) :
    (Y^10*M^10*N^2*R^8/Q^14)*
        (V*D*Y*(M/N)*(1+delta*Jsep)+Y^2*V*(Cupper*M^2/(N^4*U))) ≤
      Cv*(D*(Y^11*M^11/(N*R^2))+
        D*Cdelta*(Y^11*Jsep*M^11/N^3)+
        2*B*Cupper*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))) := by
  have hQ : 0 < Q := hR.trans_le hRQ
  obtain ⟨hU,hUinv⟩ := physical_reference_reciprocal_bound hN hQ hB hUlower
  have hcost : Cupper*M^2/(N^4*U) ≤
      (Cupper*M^2/N^4)*(2*B*(Q/N)^((2:ℝ)/3)) := by
    calc
      _ = (Cupper*M^2/N^4)*(1/U) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hUinv (by positivity)
  have hQpow := pow_le_pow_left₀ hR.le hRQ 14
  have hI0 : R^12/Q^14 ≤ 1/R^2 := by
    calc
      _ ≤ R^12/R^14 := div_le_div_of_nonneg_left (by positivity) (by positivity) hQpow
      _ = _ := by field_simp
  have hI1 : R^14/Q^14 ≤ 1 := (div_le_one (by positivity)).mpr hQpow
  have hII : R^12*(Q/N)^((2:ℝ)/3)/Q^14 ≤ (R/N)^((2:ℝ)/3)/R^2 := by
    calc
      _ = R^12*((Q/N)^((2:ℝ)/3)/Q^14) := by ring
      _ ≤ R^12*((R/N)^((2:ℝ)/3)/R^14) :=
        mul_le_mul_of_nonneg_left
          (physical_denominator_rpow_decay 14 hR hRQ hN (by norm_num)) (by positivity)
      _ = _ := by field_simp
  let A₀ := Cv*D*Y^11*M^11/N
  let A₁ := Cv*D*Cdelta*Y^11*Jsep*M^11/N^3
  let A₂ := Cv*2*B*Cupper*Y^12*M^12/N^4
  have hA₀ : 0 ≤ A₀ := by dsimp only [A₀]; positivity
  have hA₁ : 0 ≤ A₁ := by dsimp only [A₁]; positivity
  have hA₂ : 0 ≤ A₂ := by dsimp only [A₂]; positivity
  calc
    _ ≤ (Y^10*M^10*N^2*R^8/Q^14)*
        ((Cv*R^4/N^2)*D*Y*(M/N)*(1+(Cdelta*R^2/N^2)*Jsep)+
          Y^2*(Cv*R^4/N^2)*((Cupper*M^2/N^4)*(2*B*(Q/N)^((2:ℝ)/3)))) := by
      gcongr
    _ = A₀*(R^12/Q^14)+A₁*(R^14/Q^14)+A₂*(R^12*(Q/N)^((2:ℝ)/3)/Q^14) := by
      dsimp only [A₀,A₁,A₂]
      field_simp
    _ ≤ A₀*(1/R^2)+A₁*1+A₂*((R/N)^((2:ℝ)/3)/R^2) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hI0 hA₀)
        (mul_le_mul_of_nonneg_left hI1 hA₁)) (mul_le_mul_of_nonneg_left hII hA₂)
    _ = _ := by
      dsimp only [A₀,A₁,A₂]
      ring

example
    {Y M N R Q U V Jsep D Cdelta Cupper Cv B delta : ℝ}
    (hY : 0 ≤ Y) (hM : 0 ≤ M) (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q)
    (hJ : 0 ≤ Jsep) (hD : 0 ≤ D) (hCd : 0 ≤ Cdelta)
    (hCu : 0 ≤ Cupper) (hCv : 0 ≤ Cv) (hB : 0 < B) (hd : 0 ≤ delta)
    (hVupper : V ≤ Cv*R^4/N^2) (hdelta : delta ≤ Cdelta*R^2/N^2)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B) ≤ U) :
    (Y^10*M^10*N^2*R^8/Q^14)*
        (V*D*Y*(M/N)*(1+delta*Jsep)+Y^2*V*(Cupper*M^2/(N^4*U))) ≤
      Cv*(D*(Y^11*M^11/(N*R^2))+
        D*Cdelta*(Y^11*Jsep*M^11/N^3)+
        2*B*Cupper*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))) :=
  HuxleyBandScaleScratch.upper_physical_family_monomial_bound (Y:=Y) (M:=M) (N:=N) (R:=R) (Q:=Q) (U:=U) (V:=V) (Jsep:=Jsep) (D:=D) (Cdelta:=Cdelta) (Cupper:=Cupper) (Cv:=Cv) (B:=B) (delta:=delta) hY hM hN hR hRQ hJ hD hCd hCu hCv hB hd hVupper hdelta hUlower


#print axioms HuxleyBandScaleScratch.upper_physical_family_monomial_bound


private theorem lower_physical_family_monomial_bound
    {Y M N R Q U V Jsep D Cdelta Clower Cv B delta : ℝ}
    (hY : 0 ≤ Y) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q)
    (hJ : 0 ≤ Jsep) (hD : 0 ≤ D) (hCd : 0 ≤ Cdelta)
    (hCl : 0 ≤ Clower) (hCv : 0 ≤ Cv) (hB : 0 < B) (hd : 0 ≤ delta)
    (hVlower : V ≤ Cv*M^2/N^4) (hdelta : delta ≤ Cdelta*R^2/N^2)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B) ≤ U) :
    (Y^10*M^10*N^2*R^8/Q^14)*
        (V*D*Y*(M/N)*(1+delta*Jsep)+Y^2*V*(Clower*R^4/(N^2*U))) ≤
      Cv*(D*(Y^11*M^13/(N^3*R^6))+
        D*Cdelta*(Y^11*Jsep*M^13/(N^5*R^4))+
        2*B*Clower*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))) := by
  have hQ : 0 < Q := hR.trans_le hRQ
  have hU := (physical_reference_reciprocal_bound hN hQ hB hUlower).1
  let Cv' := Cv*M^2/(N^2*R^4)
  let Cu' := Clower*R^4*N^2/M^2
  have hCv' : 0 ≤ Cv' := by dsimp only [Cv']; positivity
  have hCu' : 0 ≤ Cu' := by dsimp only [Cu']; positivity
  have hVupper : V ≤ Cv'*R^4/N^2 := by
    convert hVlower using 1
    dsimp only [Cv']
    field_simp
  have hh := upper_physical_family_monomial_bound hY hM.le hN hR hRQ
    hJ hD hCd hCu' hCv' hB hd hVupper hdelta hUlower
  calc
    _ = (Y^10*M^10*N^2*R^8/Q^14)*
        (V*D*Y*(M/N)*(1+delta*Jsep)+Y^2*V*(Cu'*M^2/(N^4*U))) := by
      dsimp only [Cu']
      field_simp
    _ ≤ Cv'*(D*(Y^11*M^11/(N*R^2))+
        D*Cdelta*(Y^11*Jsep*M^11/N^3)+
        2*B*Cu'*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))) := hh
    _ = _ := by
      dsimp only [Cv',Cu']
      field_simp

private theorem physical_large_pair_monomial_bound
    {Y M N R Q C : ℝ}
    (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q) (hC : 0 ≤ C) :
    (Y^10*M^10*N^2*R^8/Q^14)*
        (Y^2*(C*M^2*R^4/N^6*(Q/N)^((2:ℝ)/3))) ≤
      C*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) := by
  have hQ : 0 < Q := hR.trans_le hRQ
  have hmono := physical_denominator_rpow_decay 14 hR hRQ hN (by norm_num : (2:ℝ)/3 ≤ 14)
  calc
    _ = (C*Y^12*M^12*R^12/N^4)*((Q/N)^((2:ℝ)/3)/Q^14) := by field_simp
    _ ≤ (C*Y^12*M^12*R^12/N^4)*((R/N)^((2:ℝ)/3)/R^14) :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = _ := by field_simp

example
    {Y M N R Q U V Jsep D Cdelta Clower Cv B delta : ℝ}
    (hY : 0 ≤ Y) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q)
    (hJ : 0 ≤ Jsep) (hD : 0 ≤ D) (hCd : 0 ≤ Cdelta)
    (hCl : 0 ≤ Clower) (hCv : 0 ≤ Cv) (hB : 0 < B) (hd : 0 ≤ delta)
    (hVlower : V ≤ Cv*M^2/N^4) (hdelta : delta ≤ Cdelta*R^2/N^2)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B) ≤ U) :
    (Y^10*M^10*N^2*R^8/Q^14)*
        (V*D*Y*(M/N)*(1+delta*Jsep)+Y^2*V*(Clower*R^4/(N^2*U))) ≤
      Cv*(D*(Y^11*M^13/(N^3*R^6))+
        D*Cdelta*(Y^11*Jsep*M^13/(N^5*R^4))+
        2*B*Clower*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))) :=
  HuxleyBandScaleScratch.lower_physical_family_monomial_bound (Y:=Y) (M:=M) (N:=N) (R:=R) (Q:=Q) (U:=U) (V:=V) (Jsep:=Jsep) (D:=D) (Cdelta:=Cdelta) (Clower:=Clower) (Cv:=Cv) (B:=B) (delta:=delta) hY hM hN hR hRQ hJ hD hCd hCl hCv hB hd hVlower hdelta hUlower

example
    {Y M N R Q C : ℝ}
    (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q) (hC : 0 ≤ C) :
    (Y^10*M^10*N^2*R^8/Q^14)*
        (Y^2*(C*M^2*R^4/N^6*(Q/N)^((2:ℝ)/3))) ≤
      C*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) :=
  HuxleyBandScaleScratch.physical_large_pair_monomial_bound (Y:=Y) (M:=M) (N:=N) (R:=R) (Q:=Q) (C:=C) hN hR hRQ hC


#print axioms HuxleyBandScaleScratch.lower_physical_family_monomial_bound
#print axioms HuxleyBandScaleScratch.physical_large_pair_monomial_bound


private theorem general_physical_family_monomial_bound
    {Y M N R Q U Jsep D Cdelta Cupper Clower Clarge B delta : ℝ}
    (hY : 0 ≤ Y) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q)
    (hJ : 0 ≤ Jsep) (hD : 0 ≤ D) (hCd : 0 ≤ Cdelta)
    (hCu : 0 ≤ Cupper) (hCl : 0 ≤ Clower) (hCb : 0 ≤ Clarge)
    (hB : 1 ≤ B) (hd : 0 ≤ delta)
    (hdelta : delta ≤ Cdelta*R^2/N^2)
    (hUupper : U ≤ (N/Q)^((2:ℝ)/3)/B)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B) ≤ U) :
    let V := U^((3:ℝ)/2)
    (Y^10*M^10*N^2*R^8/Q^14)*
        (V*D*Y*(M/N)*(1+delta*Jsep)+
          Y^2*(V*(Cupper*M^2/(N^4*U)+Clower*R^4/(N^2*U))+
            Clarge*M^2*R^4/N^6*(Q/N)^((2:ℝ)/3))) ≤
      D*(Y^11*M^11*N^2/R^7)+
        D*Cdelta*(Y^11*Jsep*M^11/R^5)+
        2*B*Cupper*(Y^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3))+
        2*B*Clower*(Y^12*M^10*N/R^3*(R/N)^((2:ℝ)/3))+
        Clarge*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) := by
  intro V
  have hQ : 0 < Q := hR.trans_le hRQ
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hU := (physical_reference_reciprocal_bound hN hQ hBp hUlower).1
  have hUbound : U ≤ (N/R)^((2:ℝ)/3) := by
    calc
      _ ≤ (N/Q)^((2:ℝ)/3)/B := hUupper
      _ ≤ (N/Q)^((2:ℝ)/3) := div_le_self (by positivity) hB
      _ ≤ (N/R)^((2:ℝ)/3) :=
        Real.rpow_le_rpow (by positivity)
          (div_le_div_of_nonneg_left hN.le hR hRQ) (by norm_num)
  have hVbound : V ≤ N/R := by
    have hh := Real.rpow_le_rpow hU.le hUbound (by norm_num : (0:ℝ) ≤ 3/2)
    have he : ((N/R)^((2:ℝ)/3))^((3:ℝ)/2)=N/R := by
      rw [←Real.rpow_mul (div_pos hN hR).le]
      norm_num
    exact hh.trans_eq he
  let Cvu := N^3/R^5
  let Cvl := N^5/(M^2*R)
  have hCvu : 0 ≤ Cvu := by dsimp only [Cvu]; positivity
  have hCvl : 0 ≤ Cvl := by dsimp only [Cvl]; positivity
  have hVu : V ≤ Cvu*R^4/N^2 := by
    convert hVbound using 1
    dsimp only [Cvu]
    field_simp
  have hVl : V ≤ Cvl*M^2/N^4 := by
    convert hVbound using 1
    dsimp only [Cvl]
    field_simp
  have hu := upper_physical_family_monomial_bound hY hM.le hN hR hRQ
    hJ hD hCd hCu hCvu hBp hd hVu hdelta hUlower
  have hl := lower_physical_family_monomial_bound hY hM hN hR hRQ
    hJ (show (0:ℝ) ≤ 0 by rfl) hCd hCl hCvl hBp hd hVl hdelta hUlower
  have hb := physical_large_pair_monomial_bound (Y:=Y) (M:=M) hN hR hRQ hCb
  convert add_le_add (add_le_add hu hl) hb using 1
  · ring
  · dsimp only [Cvu,Cvl]
    field_simp
    ring

example
    {Y M N R Q U Jsep D Cdelta Cupper Clower Clarge B delta : ℝ}
    (hY : 0 ≤ Y) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q)
    (hJ : 0 ≤ Jsep) (hD : 0 ≤ D) (hCd : 0 ≤ Cdelta)
    (hCu : 0 ≤ Cupper) (hCl : 0 ≤ Clower) (hCb : 0 ≤ Clarge)
    (hB : 1 ≤ B) (hd : 0 ≤ delta)
    (hdelta : delta ≤ Cdelta*R^2/N^2)
    (hUupper : U ≤ (N/Q)^((2:ℝ)/3)/B)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B) ≤ U) :
    let V := U^((3:ℝ)/2)
    (Y^10*M^10*N^2*R^8/Q^14)*
        (V*D*Y*(M/N)*(1+delta*Jsep)+
          Y^2*(V*(Cupper*M^2/(N^4*U)+Clower*R^4/(N^2*U))+
            Clarge*M^2*R^4/N^6*(Q/N)^((2:ℝ)/3))) ≤
      D*(Y^11*M^11*N^2/R^7)+
        D*Cdelta*(Y^11*Jsep*M^11/R^5)+
        2*B*Cupper*(Y^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3))+
        2*B*Clower*(Y^12*M^10*N/R^3*(R/N)^((2:ℝ)/3))+
        Clarge*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) :=
  HuxleyBandScaleScratch.general_physical_family_monomial_bound (Y:=Y) (M:=M) (N:=N) (R:=R) (Q:=Q) (U:=U) (Jsep:=Jsep) (D:=D) (Cdelta:=Cdelta) (Cupper:=Cupper) (Clower:=Clower) (Clarge:=Clarge) (B:=B) (delta:=delta) hY hM hN hR hRQ hJ hD hCd hCu hCl hCb hB hd hdelta hUupper hUlower


#print axioms HuxleyBandScaleScratch.general_physical_family_monomial_bound


private theorem selected_band_grid_cardinality_bound
    (Chunks : Finset (ℝ × ℤ)) (band : (ℝ × ℤ) → Option ℕ)
    (Grid : ℕ → ℤ → Finset (ℝ × ℤ)) (Qbase kmax : ℕ)
    {Y M N R Cbase Cdensity L : ℝ}
    (hQbase : 0 < Qbase) (hY : 0 ≤ Y) (hM : 0 ≤ M) (hN : 0 < N)
    (hCd : 0 ≤ Cdensity) (hL : 1 ≤ L)
    (hbase : (Qbase:ℝ) ≤ Cbase*R)
    (hchunks : (Chunks.card:ℝ) ≤ Y*(8*M/N)) :
    let Q := fun k : ℕ => Qbase*2^k
    (∀ j ≤ kmax, ((Chunks.filter (fun p => band p=some (j+1))).card:ℝ) ≤
      Y*(Cdensity*M*R^2/(N*(Q j:ℝ)^2)*L)) →
    (∀ k ≤ kmax, ∀ r : ℤ,
      (Grid k r).card ≤ 2*(Chunks.filter (fun p => band p=some k)).card) →
    ∀ k ≤ kmax, ∀ r : ℤ,
      ((Grid k r).card:ℝ) ≤
        (16*Cbase^2+8*Cdensity)*Y*M*R^2/(N*(Q k:ℝ)^2)*L := by
  classical
  intro Q hbands hgrids k hk r
  have hQpos (j : ℕ) : (0:ℝ) < Q j := by
    exact_mod_cast Nat.mul_pos hQbase (by positivity : 0 < 2^j)
  have hLp : 0 ≤ L := zero_le_one.trans hL
  have hgrid : ((Grid k r).card:ℝ) ≤
      2*((Chunks.filter (fun p => band p=some k)).card:ℝ) := by
    exact_mod_cast hgrids k hk r
  cases k with
  | zero =>
    have hsub : ((Chunks.filter (fun p => band p=some 0)).card:ℝ) ≤ Chunks.card := by
      exact_mod_cast Finset.card_filter_le (s:=Chunks) (p:=fun p => band p=some 0)
    have hQsq : (Q 0:ℝ)^2 ≤ Cbase^2*R^2 := by
      simpa only [Q,pow_zero,Nat.mul_one,mul_pow] using
        pow_le_pow_left₀ (Nat.cast_nonneg Qbase) hbase 2
    have hcoef : 16*Cbase^2 ≤ (16*Cbase^2+8*Cdensity)*L := by
      calc
        _ ≤ 16*Cbase^2+8*Cdensity := by linarith only [hCd]
        _ ≤ _ := le_mul_of_one_le_right (by positivity) hL
    calc
      _ ≤ 2*((Chunks.filter (fun p => band p=some 0)).card:ℝ) := hgrid
      _ ≤ 2*(Y*(8*M/N)) :=
        mul_le_mul_of_nonneg_left (hsub.trans hchunks) (by norm_num)
      _ = (16*Y*M/(N*(Q 0:ℝ)^2))*(Q 0:ℝ)^2 := by
        field_simp [(hQpos 0).ne']
        ring
      _ ≤ (16*Y*M/(N*(Q 0:ℝ)^2))*(Cbase^2*R^2) :=
        mul_le_mul_of_nonneg_left hQsq (by positivity)
      _ = (16*Cbase^2)*(Y*M*R^2/(N*(Q 0:ℝ)^2)) := by ring
      _ ≤ ((16*Cbase^2+8*Cdensity)*L)*(Y*M*R^2/(N*(Q 0:ℝ)^2)) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = _ := by ring
  | succ j =>
    have hj : j ≤ kmax := (Nat.le_succ j).trans hk
    have hstep : (Q (j+1):ℝ)=2*(Q j:ℝ) := by
      simp only [Q,pow_succ,Nat.cast_mul,Nat.cast_ofNat]
      ring
    have hcoef : 8*Cdensity ≤ 16*Cbase^2+8*Cdensity := by
      nlinarith only [sq_nonneg Cbase]
    calc
      _ ≤ 2*((Chunks.filter (fun p => band p=some (j+1))).card:ℝ) := hgrid
      _ ≤ 2*(Y*(Cdensity*M*R^2/(N*(Q j:ℝ)^2)*L)) :=
        mul_le_mul_of_nonneg_left (hbands j hj) (by norm_num)
      _ = (8*Cdensity)*(Y*M*R^2/(N*(Q (j+1):ℝ)^2))*L := by
        rw [hstep]
        field_simp
        ring
      _ ≤ (16*Cbase^2+8*Cdensity)*(Y*M*R^2/(N*(Q (j+1):ℝ)^2))*L :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoef (by positivity)) hLp
      _ = _ := by ring

private theorem selected_terminal_density_bound
    {n N M R Q Y Cdensity Csep L : ℝ}
    (hN : 0 < N) (hM : 0 ≤ M) (hY : 0 ≤ Y)
    (hCd : 0 ≤ Cdensity) (hC : 0 < Csep) (hL : 0 ≤ L)
    (hscale : N=8*n) (hQlower : N/Csep ≤ Q) :
    n*Y*(Cdensity*M*R^2/(N*Q^2)*L) ≤
      (Cdensity*Csep^2/8)*(Y*M*R^2/N^2)*L := by
  have hQ : 0 < Q := (div_pos hN hC).trans_le hQlower
  have hn : n=N/8 := by linarith only [hscale]
  calc
    _ = (Cdensity*Y*M*R^2/8)/Q^2*L := by rw [hn]; field_simp
    _ ≤ (Cdensity*Y*M*R^2/8)/(N/Csep)^2*L := by
      apply mul_le_mul_of_nonneg_right _ hL
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ (div_pos hN hC).le hQlower 2)
    _ = _ := by field_simp

example
    (Chunks : Finset (ℝ × ℤ)) (band : (ℝ × ℤ) → Option ℕ)
    (Grid : ℕ → ℤ → Finset (ℝ × ℤ)) (Qbase kmax : ℕ)
    {Y M N R Cbase Cdensity L : ℝ}
    (hQbase : 0 < Qbase) (hY : 0 ≤ Y) (hM : 0 ≤ M) (hN : 0 < N)
    (hCd : 0 ≤ Cdensity) (hL : 1 ≤ L)
    (hbase : (Qbase:ℝ) ≤ Cbase*R)
    (hchunks : (Chunks.card:ℝ) ≤ Y*(8*M/N)) :
    let Q := fun k : ℕ => Qbase*2^k
    (∀ j ≤ kmax, ((Chunks.filter (fun p => band p=some (j+1))).card:ℝ) ≤
      Y*(Cdensity*M*R^2/(N*(Q j:ℝ)^2)*L)) →
    (∀ k ≤ kmax, ∀ r : ℤ,
      (Grid k r).card ≤ 2*(Chunks.filter (fun p => band p=some k)).card) →
    ∀ k ≤ kmax, ∀ r : ℤ,
      ((Grid k r).card:ℝ) ≤
        (16*Cbase^2+8*Cdensity)*Y*M*R^2/(N*(Q k:ℝ)^2)*L :=
  HuxleyBandScaleScratch.selected_band_grid_cardinality_bound Chunks band Grid Qbase kmax (Y:=Y) (M:=M) (N:=N) (R:=R) (Cbase:=Cbase) (Cdensity:=Cdensity) (L:=L) hQbase hY hM hN hCd hL hbase hchunks

example
    {n N M R Q Y Cdensity Csep L : ℝ}
    (hN : 0 < N) (hM : 0 ≤ M) (hY : 0 ≤ Y)
    (hCd : 0 ≤ Cdensity) (hC : 0 < Csep) (hL : 0 ≤ L)
    (hscale : N=8*n) (hQlower : N/Csep ≤ Q) :
    n*Y*(Cdensity*M*R^2/(N*Q^2)*L) ≤
      (Cdensity*Csep^2/8)*(Y*M*R^2/N^2)*L :=
  HuxleyBandScaleScratch.selected_terminal_density_bound (n:=n) (N:=N) (M:=M) (R:=R) (Q:=Q) (Y:=Y) (Cdensity:=Cdensity) (Csep:=Csep) (L:=L) hN hM hY hCd hC hL hscale hQlower


#print axioms HuxleyBandScaleScratch.selected_band_grid_cardinality_bound
#print axioms HuxleyBandScaleScratch.selected_terminal_density_bound


private theorem selected_band_mesh_cardinality_prefactor_bound
    {Y M N R Q K P Cmesh Ccard L T ε : ℝ}
    (hY : 0 ≤ Y) (hM : 0 ≤ M) (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hK : 0 < K) (hP : 0 ≤ P)
    (hCm : 0 < Cmesh) (hCc : 0 ≤ Ccard) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hQN : Q ≤ N) (hNR : N ≤ R^2) (hNT : N ≤ T)
    (hmesh : K ≤ Cmesh*Q*N/R^2)
    (hcard : P ≤ Ccard*Y*M*R^2/(N*Q^2)*L) :
    (R^2/Q)^6*K^((12:ℝ)+ε)*(2*P)^10 ≤
      (Cmesh^12*Cmesh^ε*(2*Ccard)^10)*T^ε*L^10*
        (Y^10*M^10*N^2*R^8/Q^14) := by
  have hT : 0 < T := hN.trans_le hNT
  have hKT : K ≤ Cmesh*T := by
    calc
      _ ≤ Cmesh*Q*N/R^2 := hmesh
      _ ≤ Cmesh*Q := (div_le_iff₀ (sq_pos_of_pos hR)).mpr
        (mul_le_mul_of_nonneg_left hNR (by positivity))
      _ ≤ Cmesh*T := mul_le_mul_of_nonneg_left (hQN.trans hNT) hCm.le
  have hKpow : K^((12:ℝ)+ε) ≤
      (Cmesh*Q*N/R^2)^12*Cmesh^ε*T^ε := by
    calc
      _ = K^12*K^ε := by norm_num [Real.rpow_add hK]
      _ ≤ (Cmesh*Q*N/R^2)^12*(Cmesh*T)^ε := by gcongr
      _ = _ := by rw [Real.mul_rpow hCm.le hT.le]; ring
  have hPbound : 2*P ≤ (2*Ccard)*Y*M*R^2/(N*Q^2)*L := by
    calc
      _ ≤ 2*(Ccard*Y*M*R^2/(N*Q^2)*L) :=
        mul_le_mul_of_nonneg_left hcard (by norm_num)
      _ = _ := by ring
  calc
    _ ≤ (R^2/Q)^6*((Cmesh*Q*N/R^2)^12*Cmesh^ε*T^ε)*
        ((2*Ccard)*Y*M*R^2/(N*Q^2)*L)^10 := by gcongr
    _ = (Cmesh^ε*T^ε*L^10)*
        ((R^2/Q)^6*(Cmesh*Q*N/R^2)^12*((2*Ccard)*Y*M*R^2/(N*Q^2))^10) := by
      rw [mul_pow]
      ring
    _ = _ := by
      rw [selected_band_prefactor_identity hR.ne' hQ.ne' hN.ne']
      ring

example
    {Y M N R Q K P Cmesh Ccard L T ε : ℝ}
    (hY : 0 ≤ Y) (hM : 0 ≤ M) (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hK : 0 < K) (hP : 0 ≤ P)
    (hCm : 0 < Cmesh) (hCc : 0 ≤ Ccard) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hQN : Q ≤ N) (hNR : N ≤ R^2) (hNT : N ≤ T)
    (hmesh : K ≤ Cmesh*Q*N/R^2)
    (hcard : P ≤ Ccard*Y*M*R^2/(N*Q^2)*L) :
    (R^2/Q)^6*K^((12:ℝ)+ε)*(2*P)^10 ≤
      (Cmesh^12*Cmesh^ε*(2*Ccard)^10)*T^ε*L^10*
        (Y^10*M^10*N^2*R^8/Q^14) :=
  HuxleyBandScaleScratch.selected_band_mesh_cardinality_prefactor_bound (Y:=Y) (M:=M) (N:=N) (R:=R) (Q:=Q) (K:=K) (P:=P) (Cmesh:=Cmesh) (Ccard:=Ccard) (L:=L) (T:=T) (ε:=ε) hY hM hN hR hQ hK hP hCm hCc hL hε hQN hNR hNT hmesh hcard


#print axioms HuxleyBandScaleScratch.selected_band_mesh_cardinality_prefactor_bound

end HuxleyBandScaleScratch
