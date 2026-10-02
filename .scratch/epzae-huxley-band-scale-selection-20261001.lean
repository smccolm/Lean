import TaoTrudgianYang2025.HuxleyLinearForms

open scoped BigOperators
open Set Filter
open TaoTrudgianYang2025
open scoped Classical ContDiff FourierTransform
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
    (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hK : 0 < K) (hP : 0 ≤ P)
    (hCm : 0 < Cmesh) (hε : 0 ≤ ε)
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
    (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hK : 0 < K) (hP : 0 ≤ P)
    (hCm : 0 < Cmesh) (hε : 0 ≤ ε)
    (hQN : Q ≤ N) (hNR : N ≤ R^2) (hNT : N ≤ T)
    (hmesh : K ≤ Cmesh*Q*N/R^2)
    (hcard : P ≤ Ccard*Y*M*R^2/(N*Q^2)*L) :
    (R^2/Q)^6*K^((12:ℝ)+ε)*(2*P)^10 ≤
      (Cmesh^12*Cmesh^ε*(2*Ccard)^10)*T^ε*L^10*
        (Y^10*M^10*N^2*R^8/Q^14) :=
  HuxleyBandScaleScratch.selected_band_mesh_cardinality_prefactor_bound (Y:=Y) (M:=M) (N:=N) (R:=R) (Q:=Q) (K:=K) (P:=P) (Cmesh:=Cmesh) (Ccard:=Ccard) (L:=L) (T:=T) (ε:=ε) hN hR hQ hK hP hCm hε hQN hNR hNT hmesh hcard


#print axioms HuxleyBandScaleScratch.selected_band_mesh_cardinality_prefactor_bound


private theorem positive_difference_completion_error_physical_bound
    {Y M N R T C : ℝ} (hY : 0 ≤ Y) (hN : 1 ≤ N)
    (hNM : N ≤ M) (hMT : M ≤ T) (hC : 0 ≤ C) :
    Y*(M/N+1)*(Real.sqrt (3*N)*Real.log (6*N)+C*R^2/N) ≤
      (2*Real.sqrt 3*(1+Real.log 6)+2*C)*
        (Y*M/Real.sqrt N+Y*M*R^2/N^2)*(1+Real.log T) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hMp : 0 < M := hNp.trans_le hNM
  have hT : 1 ≤ T := hN.trans (hNM.trans hMT)
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hlog6 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have hlogN := Real.log_le_log hNp (hNM.trans hMT)
  have hlog : Real.log (6*N) ≤ (1+Real.log 6)*(1+Real.log T) := by
    rw [Real.log_mul (by norm_num : (6:ℝ) ≠ 0) hNp.ne']
    nlinarith only [hlogN,hlog6,hlogT,mul_nonneg hlog6 hlogT]
  have hlogPos : 0 ≤ Real.log (6*N) := Real.log_nonneg (by linarith only [hN])
  have hL : 1 ≤ 1+Real.log T := by linarith only [hlogT]
  have hratio : 1 ≤ M/N := (le_div_iff₀ hNp).mpr (by simpa only [one_mul] using hNM)
  have hfront : M/N+1 ≤ 2*M/N := by
    calc
      _ ≤ M/N+M/N := add_le_add le_rfl hratio
      _ = _ := by ring
  have hsum : Real.sqrt (3*N)*Real.log (6*N)+C*R^2/N ≤
      (Real.sqrt 3*Real.sqrt N*(1+Real.log 6)+C*R^2/N)*(1+Real.log T) := by
    have hc := le_mul_of_one_le_right (by positivity : 0 ≤ C*R^2/N) hL
    calc
      _ = Real.sqrt 3*Real.sqrt N*Real.log (6*N)+C*R^2/N := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
      _ ≤ Real.sqrt 3*Real.sqrt N*((1+Real.log 6)*(1+Real.log T))+
          (C*R^2/N)*(1+Real.log T) :=
        add_le_add (mul_le_mul_of_nonneg_left hlog (by positivity)) hc
      _ = _ := by ring
  have hcancel : M/N*Real.sqrt N=M/Real.sqrt N := by
    calc
      _ = M*(Real.sqrt N/N) := by ring
      _ = _ := by rw [Real.sqrt_div_self']; ring
  let A := 2*Real.sqrt 3*(1+Real.log 6)
  let E₁ := Y*M/Real.sqrt N
  let E₂ := Y*M*R^2/N^2
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hE₁ : 0 ≤ E₁ := by dsimp only [E₁]; positivity
  have hE₂ : 0 ≤ E₂ := by dsimp only [E₂]; positivity
  calc
    _ ≤ Y*(2*M/N)*
        ((Real.sqrt 3*Real.sqrt N*(1+Real.log 6)+C*R^2/N)*(1+Real.log T)) := by
      gcongr
    _ = (A*(Y*(M/N*Real.sqrt N))+2*C*E₂)*(1+Real.log T) := by
      dsimp only [A,E₂]
      ring
    _ = (A*E₁+2*C*E₂)*(1+Real.log T) := by
      rw [hcancel]
      dsimp only [E₁]
      ring
    _ ≤ ((A+2*C)*(E₁+E₂))*(1+Real.log T) := by
      apply mul_le_mul_of_nonneg_right _ (by linarith only [hlogT])
      nlinarith only [mul_nonneg hA hE₂,mul_nonneg hC hE₁]
    _ = _ := rfl

example
    {Y M N R T C : ℝ} (hY : 0 ≤ Y) (hN : 1 ≤ N)
    (hNM : N ≤ M) (hMT : M ≤ T) (hC : 0 ≤ C) :
    Y*(M/N+1)*(Real.sqrt (3*N)*Real.log (6*N)+C*R^2/N) ≤
      (2*Real.sqrt 3*(1+Real.log 6)+2*C)*
        (Y*M/Real.sqrt N+Y*M*R^2/N^2)*(1+Real.log T) :=
  HuxleyBandScaleScratch.positive_difference_completion_error_physical_bound (Y:=Y) (M:=M) (N:=N) (R:=R) (T:=T) (C:=C) hY hN hNM hMT hC


#print axioms HuxleyBandScaleScratch.positive_difference_completion_error_physical_bound


private theorem positive_difference_endpoint_error_physical_bound
    {Y N n R Q U κ σ c Cphys B : ℝ}
    (hY : 0 ≤ Y) (hN : 1 ≤ N) (hR : 0 < R) (hRQ : R ≤ Q) (hQN : Q ≤ N)
    (hκ : 0 < κ) (hσ : 0 ≤ σ) (hc : 0 < c) (hCphys : 0 ≤ Cphys)
    (hB : 1 ≤ B) (hscale : N=8*n)
    (hUupper : U ≤ (N/Q)^((2:ℝ)/3)/B) :
    Y*(2*((56*U/κ)*N+N/(Cphys+2)+2)+
        2*((14*σ/c)*U*N)+6*N+2*n) ≤
      (112/κ+28*σ/c+2/(Cphys+2)+41/4)*
        (Y*N*(N/R)^((2:ℝ)/3)) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hQ : 0 < Q := hR.trans_le hRQ
  let X := (N/R)^((2:ℝ)/3)
  let A := 112/κ+28*σ/c
  let E := 2/(Cphys+2)+25/4
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hn : n=N/8 := by linarith only [hscale]
  have hUX : U ≤ X := by
    calc
      _ ≤ (N/Q)^((2:ℝ)/3)/B := hUupper
      _ ≤ (N/Q)^((2:ℝ)/3) := div_le_self (by positivity) hB
      _ ≤ (N/R)^((2:ℝ)/3) := Real.rpow_le_rpow (by positivity)
        (div_le_div_of_nonneg_left hNp.le hR hRQ) (by norm_num)
  have hX : 1 ≤ X := Real.one_le_rpow
    ((le_div_iff₀ hR).mpr (by simpa only [one_mul] using hRQ.trans hQN)) (by norm_num)
  have hNX : N ≤ X*N := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hX hNp.le
  have hXN : 1 ≤ X*N := hN.trans hNX
  calc
    _ = Y*(A*(U*N)+E*N+4) := by
      dsimp only [A,E]
      rw [hn]
      ring
    _ ≤ Y*(A*(X*N)+E*(X*N)+4*(X*N)) := by
      apply mul_le_mul_of_nonneg_left _ hY
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hUX hNp.le) hA)
          (mul_le_mul_of_nonneg_left hNX hE))
        (by nlinarith only [hXN])
    _ = _ := by
      dsimp only [A,E,X]
      ring

example
    {Y N n R Q U κ σ c Cphys B : ℝ}
    (hY : 0 ≤ Y) (hN : 1 ≤ N) (hR : 0 < R) (hRQ : R ≤ Q) (hQN : Q ≤ N)
    (hκ : 0 < κ) (hσ : 0 ≤ σ) (hc : 0 < c) (hCphys : 0 ≤ Cphys)
    (hB : 1 ≤ B) (hscale : N=8*n)
    (hUupper : U ≤ (N/Q)^((2:ℝ)/3)/B) :
    Y*(2*((56*U/κ)*N+N/(Cphys+2)+2)+
        2*((14*σ/c)*U*N)+6*N+2*n) ≤
      (112/κ+28*σ/c+2/(Cphys+2)+41/4)*
        (Y*N*(N/R)^((2:ℝ)/3)) :=
  HuxleyBandScaleScratch.positive_difference_endpoint_error_physical_bound (Y:=Y) (N:=N) (n:=n) (R:=R) (Q:=Q) (U:=U) (κ:=κ) (σ:=σ) (c:=c) (Cphys:=Cphys) (B:=B) hY hN hR hRQ hQN hκ hσ hc hCphys hB hscale hUupper


#print axioms HuxleyBandScaleScratch.positive_difference_endpoint_error_physical_bound


private theorem eventually_selected_band_logarithmic_absorption
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in Filter.atTop, 0 < T ∧ 1 ≤ Real.log T ∧
      C*T^(ε/2)*(1+Real.log T)^36 ≤ T^ε := by
  filter_upwards [
    TaoTrudgianYang2025.eventually_const_log_pow_le_rpow (C*2^36) (by positivity) 36
      (show 0 < ε/2 by linarith only [hε]),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Filter.eventually_ge_atTop (1:ℝ)] with T hsmall hlog hT
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hpoly : C*(1+Real.log T)^36 ≤ T^(ε/2) := by
    calc
      _ ≤ C*(2*Real.log T)^36 := by gcongr; linarith only [hlog]
      _ = (C*2^36)*(Real.log T)^36 := by rw [mul_pow]; ring
      _ ≤ _ := hsmall
  refine ⟨hTp,hlog,?_⟩
  calc
    _ = (C*(1+Real.log T)^36)*T^(ε/2) := by ring
    _ ≤ T^(ε/2)*T^(ε/2) := mul_le_mul_of_nonneg_right hpoly (by positivity)
    _ = _ := by rw [←Real.rpow_add hTp]; congr 1; ring

example
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in Filter.atTop, 0 < T ∧ 1 ≤ Real.log T ∧
      C*T^(ε/2)*(1+Real.log T)^36 ≤ T^ε :=
  HuxleyBandScaleScratch.eventually_selected_band_logarithmic_absorption (C:=C) (ε:=ε) hC hε


#print axioms HuxleyBandScaleScratch.eventually_selected_band_logarithmic_absorption


private theorem exists_uniform_source_physical_budget
    {Csep A₄ A₂ B Cbuffer Clinear Cwidth : ℝ}
    (hSep : 0 ≤ Csep) (hA₄ : 0 ≤ A₄) (hA₂ : 0 ≤ A₂)
    (hB : 0 ≤ B) (hBuffer : 0 ≤ Cbuffer) (hLinear : 0 ≤ Clinear)
    (hWidth : 0 ≤ Cwidth) :
    ∃ Cbudget : ℝ, 1 ≤ Cbudget ∧ Csep ≤ Cbudget ∧
      ∀ (N R M U : ℝ), 2 ≤ N → 1 ≤ R →
      Cbudget*R ≤ N → Cbudget*N ≤ R^2 → Cbudget*N^2 ≤ M → U ≤ N →
      0 < M ∧ R ≤ N ∧ N ≤ R^2 ∧ N^2 ≤ M ∧ N*R ≤ M ∧ N^3 ≤ M*R^2 ∧ R ≤ M ∧
      7*N+2 ≤ M/4 ∧
      A₄*(6*N+1)^4 ≤ M*N*R^2 ∧
      A₂*(6*N+1)^2 ≤ N*R^2 ∧
      B*R^2/N^2 ≤ 1/2 ∧
      2*((Cbuffer*U)*N+Clinear*N+2+(Cwidth*U)*N)+6*N ≤ M ∧
      (∀ T : ℝ, 0 < T → T*N*R^2=M^3 → M ≤ T) := by
  let Cbudget := 43+Csep+2401*A₄+49*A₂+2*B+2*Cbuffer+2*Cwidth+2*Clinear
  have hbounds : 1 ≤ Cbudget ∧ Csep ≤ Cbudget ∧ 32 ≤ Cbudget ∧
      2401*A₄ ≤ Cbudget ∧ 49*A₂ ≤ Cbudget ∧ 2*B ≤ Cbudget ∧
      2*(Cbuffer+Cwidth)+2*Clinear+10 ≤ Cbudget := by
    dsimp only [Cbudget]
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;>
      linarith only [hSep,hA₄,hA₂,hB,hBuffer,hLinear,hWidth]
  obtain ⟨hC,hSepC,h32,hC₄,hC₂,hCB,hCend⟩ := hbounds
  refine ⟨Cbudget,hC,hSepC,?_⟩
  intro N R M U hN hR hRNbudget hNRbudget hMbudget hUN
  have hNp : 0 < N := by linarith only [hN]
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hRN : R ≤ N :=
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hC hRp.le : R ≤ Cbudget*R).trans hRNbudget
  have hNR : N ≤ R^2 :=
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hC hNp.le : N ≤ Cbudget*N).trans hNRbudget
  have hNM₂ : N^2 ≤ M :=
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hC (sq_nonneg N) : N^2 ≤ Cbudget*N^2).trans hMbudget
  have hNsq : N ≤ N^2 := by nlinarith only [hN]
  have hNsqOne : 1 ≤ N^2 := by nlinarith only [hN]
  have hNM : N ≤ M := hNsq.trans hNM₂
  have hMp : 0 < M := hNp.trans_le hNM
  have hNRM : N*R ≤ M := by
    calc
      _ ≤ N*N := mul_le_mul_of_nonneg_left hRN hNp.le
      _ = N^2 := (pow_two N).symm
      _ ≤ M := hNM₂
  have hN₃ : N^3 ≤ M*R^2 := by
    calc
      _ = N^2*N := by ring
      _ ≤ _ := mul_le_mul hNM₂ hNR hNp.le hMp.le
  have hpad : 7*N+2 ≤ M/4 := by
    have hh := (mul_le_mul_of_nonneg_right h32 (sq_nonneg N)).trans hMbudget
    have hn := mul_le_mul_of_nonneg_left hNsq (by norm_num : (0:ℝ) ≤ 32)
    nlinarith only [hh,hn,hN]
  have hshort : 6*N+1 ≤ 7*N := by linarith only [hN]
  have hquartic : A₄*(6*N+1)^4 ≤ M*N*R^2 := by
    calc
      _ ≤ A₄*(7*N)^4 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hshort 4) hA₄
      _ = (2401*A₄)*N^4 := by ring
      _ ≤ Cbudget*N^4 := mul_le_mul_of_nonneg_right hC₄ (by positivity)
      _ = (Cbudget*N^2)*N^2 := by ring
      _ ≤ M*N^2 := mul_le_mul_of_nonneg_right hMbudget (sq_nonneg N)
      _ = M*N*N := by ring
      _ ≤ M*N*R^2 := mul_le_mul_of_nonneg_left hNR (by positivity)
  have hquadratic : A₂*(6*N+1)^2 ≤ N*R^2 := by
    calc
      _ ≤ A₂*(7*N)^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hshort 2) hA₂
      _ = (49*A₂)*N^2 := by ring
      _ ≤ Cbudget*N^2 := mul_le_mul_of_nonneg_right hC₂ (sq_nonneg N)
      _ = (Cbudget*N)*N := by ring
      _ ≤ R^2*N := mul_le_mul_of_nonneg_right hNRbudget hNp.le
      _ = _ := by ring
  have hsmall : B*R^2/N^2 ≤ 1/2 := by
    have hCsq : Cbudget ≤ Cbudget^2 := by nlinarith only [hC]
    have hmul := mul_le_mul_of_nonneg_right (hCB.trans hCsq) (sq_nonneg R)
    have hsq : Cbudget^2*R^2 ≤ N^2 := by
      simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) hRNbudget 2
    apply (div_le_iff₀ (sq_pos_of_pos hNp)).mpr
    nlinarith only [hmul,hsq]
  have hroom : 2*((Cbuffer*U)*N+Clinear*N+2+(Cwidth*U)*N)+6*N ≤ M := by
    have hUN' : U*N ≤ N^2 := by
      simpa only [pow_two] using mul_le_mul_of_nonneg_right hUN hNp.le
    have hb := mul_le_mul_of_nonneg_left hUN' hBuffer
    have hw := mul_le_mul_of_nonneg_left hUN' hWidth
    have hl := mul_le_mul_of_nonneg_left hNsq hLinear
    calc
      _ ≤ (2*(Cbuffer+Cwidth)+2*Clinear+10)*N^2 := by
        nlinarith only [hb,hw,hl,hNsq,hNsqOne]
      _ ≤ Cbudget*N^2 := mul_le_mul_of_nonneg_right hCend (sq_nonneg N)
      _ ≤ M := hMbudget
  refine ⟨hMp,hRN,hNR,hNM₂,hNRM,hN₃,hRN.trans hNM,hpad,hquartic,hquadratic,hsmall,hroom,?_⟩
  intro T hT hscale
  have hRM₂ : R^2 ≤ M :=
    (pow_le_pow_left₀ hRp.le hRN 2).trans hNM₂
  have hprod : N*R^2 ≤ M^2 := by
    calc
      _ ≤ M*M := mul_le_mul hNM hRM₂ (sq_nonneg R) hMp.le
      _ = _ := (pow_two M).symm
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hMp)).mp
  calc
    M^2*M = M^3 := by ring
    _ = T*(N*R^2) := by nlinarith only [hscale]
    _ ≤ T*M^2 := mul_le_mul_of_nonneg_left hprod hT.le
    _ = M^2*T := by ring

example
    {Csep A₄ A₂ B Cbuffer Clinear Cwidth : ℝ}
    (hSep : 0 ≤ Csep) (hA₄ : 0 ≤ A₄) (hA₂ : 0 ≤ A₂)
    (hB : 0 ≤ B) (hBuffer : 0 ≤ Cbuffer) (hLinear : 0 ≤ Clinear)
    (hWidth : 0 ≤ Cwidth) :
    ∃ Cbudget : ℝ, 1 ≤ Cbudget ∧ Csep ≤ Cbudget ∧
      ∀ (N R M U : ℝ), 2 ≤ N → 1 ≤ R →
      Cbudget*R ≤ N → Cbudget*N ≤ R^2 → Cbudget*N^2 ≤ M → U ≤ N →
      0 < M ∧ R ≤ N ∧ N ≤ R^2 ∧ N^2 ≤ M ∧ N*R ≤ M ∧ N^3 ≤ M*R^2 ∧ R ≤ M ∧
      7*N+2 ≤ M/4 ∧
      A₄*(6*N+1)^4 ≤ M*N*R^2 ∧
      A₂*(6*N+1)^2 ≤ N*R^2 ∧
      B*R^2/N^2 ≤ 1/2 ∧
      2*((Cbuffer*U)*N+Clinear*N+2+(Cwidth*U)*N)+6*N ≤ M ∧
      (∀ T : ℝ, 0 < T → T*N*R^2=M^3 → M ≤ T) :=
  HuxleyBandScaleScratch.exists_uniform_source_physical_budget (Csep:=Csep) (A₄:=A₄) (A₂:=A₂) (B:=B) (Cbuffer:=Cbuffer) (Clinear:=Clinear) (Cwidth:=Cwidth) hSep hA₄ hA₂ hB hBuffer hLinear hWidth


#print axioms HuxleyBandScaleScratch.exists_uniform_source_physical_budget


private theorem selected_band_finite_power_cleanup
    (kmax : ℕ) (G : ℕ → ℤ → ℝ)
    {S Terminal Endpoint E Main L Tpow Cband Cerror Cgrid : ℝ}
    (hTerminal : 0 ≤ Terminal) (hEndpoint : 0 ≤ Endpoint)
    (hMain : 0 ≤ Main) (hL : 1 ≤ L) (hTpow : 1 ≤ Tpow)
    (hCb : 0 ≤ Cband) (hCg : 0 ≤ Cgrid)
    (hband : (kmax:ℝ)+2 ≤ Cband*L)
    (hterminal : Terminal ≤ Cerror*E*L) (hendpoint : Endpoint ≤ Cerror*E*L)
    (hgrid : ∀ k∈Finset.range (kmax+1), ∀ r∈Finset.Ico (0:ℤ) 8,
      G k r ≤ Cgrid*Tpow*L^22*(E^12+Main))
    (hsource : S ≤ 2^11*(((kmax:ℝ)+2)^11*
      (Terminal^12+(4:ℝ)^12*(8:ℝ)^11*
        ∑ k∈Finset.range (kmax+1),∑ r∈Finset.Ico (0:ℤ) 8,G k r)+Endpoint^12)) :
    S ≤ (2:ℝ)^11*(Cband^11*Cerror^12+
      (4:ℝ)^12*(8:ℝ)^12*Cband^12*Cgrid+Cerror^12)*
        Tpow*L^36*(E^12+Main) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hT0 : 0 ≤ Tpow := zero_le_one.trans hTpow
  have hTotal : 0 ≤ E^12+Main := by positivity
  have hEtotal : E^12 ≤ E^12+Main := by linarith only [hMain]
  have hLpow (m : ℕ) (hm : m ≤ 36) : L^m ≤ L^36 :=
    pow_le_pow_right₀ hL hm
  have herror (m : ℕ) (hm : m ≤ 36) :
      E^12*L^m ≤ Tpow*L^36*(E^12+Main) := by
    calc
      _ ≤ (E^12+Main)*L^36 := mul_le_mul hEtotal (hLpow m hm) (by positivity) hTotal
      _ ≤ Tpow*((E^12+Main)*L^36) :=
        le_mul_of_one_le_left (by positivity) hTpow
      _ = _ := by ring
  have hsum : (∑ k∈Finset.range (kmax+1),∑ r∈Finset.Ico (0:ℤ) 8,G k r) ≤
      ((kmax:ℝ)+1)*8*(Cgrid*Tpow*L^22*(E^12+Main)) := by
    calc
      _ ≤ ∑ k∈Finset.range (kmax+1),∑ r∈Finset.Ico (0:ℤ) 8,
          Cgrid*Tpow*L^22*(E^12+Main) := by
        apply Finset.sum_le_sum
        intro k hk
        exact Finset.sum_le_sum (hgrid k hk)
      _ = _ := by
        have hcard8 : (Finset.Ico (0:ℤ) 8).card=8 := by decide
        simp only [Finset.sum_const,hcard8,Finset.card_range,nsmul_eq_mul,
          Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
        ring
  have hk : (kmax:ℝ)+1 ≤ Cband*L := by linarith only [hband]
  have hsumMajor : (∑ k∈Finset.range (kmax+1),∑ r∈Finset.Ico (0:ℤ) 8,G k r) ≤
      (Cband*L)*8*(Cgrid*Tpow*L^22*(E^12+Main)) := by
    apply hsum.trans
    gcongr
  have hterm :
      ((kmax:ℝ)+2)^11*Terminal^12 ≤
        (Cband^11*Cerror^12)*Tpow*L^36*(E^12+Main) := by
    calc
      _ ≤ (Cband*L)^11*(Cerror*E*L)^12 := by gcongr
      _ = (Cband^11*Cerror^12)*(E^12*L^23) := by ring
      _ ≤ (Cband^11*Cerror^12)*(Tpow*L^36*(E^12+Main)) :=
        mul_le_mul_of_nonneg_left (herror 23 (by norm_num)) (by positivity)
      _ = _ := by ring
  have hgridCost :
      ((kmax:ℝ)+2)^11*((4:ℝ)^12*(8:ℝ)^11*
        ∑ k∈Finset.range (kmax+1),∑ r∈Finset.Ico (0:ℤ) 8,G k r) ≤
      ((4:ℝ)^12*(8:ℝ)^12*Cband^12*Cgrid)*Tpow*L^36*(E^12+Main) := by
    have hkpow : ((kmax:ℝ)+2)^11 ≤ (Cband*L)^11 :=
      pow_le_pow_left₀ (by positivity) hband 11
    have hL34 : L^34 ≤ L^36 := hLpow 34 (by norm_num)
    calc
      _ ≤ ((kmax:ℝ)+2)^11*((4:ℝ)^12*(8:ℝ)^11*
          ((Cband*L)*8*(Cgrid*Tpow*L^22*(E^12+Main)))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsumMajor (by positivity)) (by positivity)
      _ ≤ (Cband*L)^11*((4:ℝ)^12*(8:ℝ)^11*
          ((Cband*L)*8*(Cgrid*Tpow*L^22*(E^12+Main)))) :=
        mul_le_mul_of_nonneg_right hkpow (by positivity)
      _ = ((4:ℝ)^12*(8:ℝ)^12*Cband^12*Cgrid)*Tpow*L^34*(E^12+Main) := by ring
      _ ≤ _ := by gcongr
  have hend : Endpoint^12 ≤ Cerror^12*Tpow*L^36*(E^12+Main) := by
    calc
      _ ≤ (Cerror*E*L)^12 := pow_le_pow_left₀ hEndpoint hendpoint 12
      _ = Cerror^12*(E^12*L^12) := by ring
      _ ≤ Cerror^12*(Tpow*L^36*(E^12+Main)) :=
        mul_le_mul_of_nonneg_left (herror 12 (by norm_num)) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ 2^11*(((kmax:ℝ)+2)^11*
        (Terminal^12+(4:ℝ)^12*(8:ℝ)^11*
          ∑ k∈Finset.range (kmax+1),∑ r∈Finset.Ico (0:ℤ) 8,G k r)+Endpoint^12) := hsource
    _ = 2^11*(((kmax:ℝ)+2)^11*Terminal^12+
        ((kmax:ℝ)+2)^11*((4:ℝ)^12*(8:ℝ)^11*
          ∑ k∈Finset.range (kmax+1),∑ r∈Finset.Ico (0:ℤ) 8,G k r)+Endpoint^12) := by ring
    _ ≤ 2^11*((Cband^11*Cerror^12)*Tpow*L^36*(E^12+Main)+
        ((4:ℝ)^12*(8:ℝ)^12*Cband^12*Cgrid)*Tpow*L^36*(E^12+Main)+
        Cerror^12*Tpow*L^36*(E^12+Main)) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add hterm hgridCost) hend) (by positivity)
    _ = _ := by ring

example
    (kmax : ℕ) (G : ℕ → ℤ → ℝ)
    {S Terminal Endpoint E Main L Tpow Cband Cerror Cgrid : ℝ}
    (hTerminal : 0 ≤ Terminal) (hEndpoint : 0 ≤ Endpoint)
    (hMain : 0 ≤ Main) (hL : 1 ≤ L) (hTpow : 1 ≤ Tpow)
    (hCb : 0 ≤ Cband) (hCg : 0 ≤ Cgrid)
    (hband : (kmax:ℝ)+2 ≤ Cband*L)
    (hterminal : Terminal ≤ Cerror*E*L) (hendpoint : Endpoint ≤ Cerror*E*L)
    (hgrid : ∀ k∈Finset.range (kmax+1), ∀ r∈Finset.Ico (0:ℤ) 8,
      G k r ≤ Cgrid*Tpow*L^22*(E^12+Main))
    (hsource : S ≤ 2^11*(((kmax:ℝ)+2)^11*
      (Terminal^12+(4:ℝ)^12*(8:ℝ)^11*
        ∑ k∈Finset.range (kmax+1),∑ r∈Finset.Ico (0:ℤ) 8,G k r)+Endpoint^12)) :
    S ≤ (2:ℝ)^11*(Cband^11*Cerror^12+
      (4:ℝ)^12*(8:ℝ)^12*Cband^12*Cgrid+Cerror^12)*
        Tpow*L^36*(E^12+Main) :=
  HuxleyBandScaleScratch.selected_band_finite_power_cleanup kmax G (S:=S) (Terminal:=Terminal) (Endpoint:=Endpoint) (E:=E) (Main:=Main) (L:=L) (Tpow:=Tpow) (Cband:=Cband) (Cerror:=Cerror) (Cgrid:=Cgrid) hTerminal hEndpoint hMain hL hTpow hCb hCg hband hterminal hendpoint hgrid hsource


#print axioms HuxleyBandScaleScratch.selected_band_finite_power_cleanup


private theorem positive_difference_source_physical_regime_coefficients
    {σ c J κ T M N R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) (hκ : 0 < κ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2=M^3) (hNR : N ≤ R^2) (hNM : N^2 ≤ M) :
    let lambda := c*κ*T/(12*J*M^2)
    let Uband := (3*J/σ)*T/(2*M^2)
    Uband/lambda=18*J^2/(σ*c*κ) ∧
      Uband^2*(R^8/N^4)=(3*J/(2*σ))^2*M^2*R^4/N^6 ∧
      1+R^4/(6*N^2) ≤ (7/6:ℝ)*R^4/N^2 ∧
      1+R^4*Uband^2/N^2 ≤ (1+(3*J/(2*σ))^2)*M^2/N^4 := by
  intro lambda Uband
  have hTscale : T=M^3/(N*R^2) := (eq_div_iff (by positivity)).mpr (by
    nlinarith only [hscale])
  have hUscale : Uband=(3*J/(2*σ))*M/(N*R^2) := by
    dsimp only [Uband]
    rw [hTscale]
    field_simp
  have hratio : Uband/lambda=18*J^2/(σ*c*κ) := by
    dsimp only [Uband,lambda]
    field_simp
    ring
  have hupper : 1 ≤ R^4/N^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hN)).mpr
    have hh := pow_le_pow_left₀ hN.le hNR 2
    nlinarith only [hh]
  have hlower : 1 ≤ M^2/N^4 := by
    apply (le_div_iff₀ (pow_pos hN 4)).mpr
    have hh := pow_le_pow_left₀ (sq_nonneg N) hNM 2
    nlinarith only [hh]
  refine ⟨hratio,?_,?_,?_⟩
  · rw [hUscale]
    field_simp
  · have he : R^4/(6*N^2)=(R^4/N^2)/6 := by ring
    rw [he]
    calc
      _ ≤ R^4/N^2+(R^4/N^2)/6 := add_le_add hupper le_rfl
      _ = _ := by ring
  · have he : R^4*Uband^2/N^2=(3*J/(2*σ))^2*(M^2/N^4) := by
      rw [hUscale]
      field_simp
    rw [he]
    calc
      _ ≤ M^2/N^4+(3*J/(2*σ))^2*(M^2/N^4) := add_le_add hlower le_rfl
      _ = _ := by ring

example
    {σ c J κ T M N R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) (hκ : 0 < κ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2=M^3) (hNR : N ≤ R^2) (hNM : N^2 ≤ M) :
    let lambda := c*κ*T/(12*J*M^2)
    let Uband := (3*J/σ)*T/(2*M^2)
    Uband/lambda=18*J^2/(σ*c*κ) ∧
      Uband^2*(R^8/N^4)=(3*J/(2*σ))^2*M^2*R^4/N^6 ∧
      1+R^4/(6*N^2) ≤ (7/6:ℝ)*R^4/N^2 ∧
      1+R^4*Uband^2/N^2 ≤ (1+(3*J/(2*σ))^2)*M^2/N^4 :=
  HuxleyBandScaleScratch.positive_difference_source_physical_regime_coefficients (σ:=σ) (c:=c) (J:=J) (κ:=κ) (T:=T) (M:=M) (N:=N) (R:=R) hσ hc hJ hκ hT hM hN hR hscale hNR hNM


#print axioms HuxleyBandScaleScratch.positive_difference_source_physical_regime_coefficients


private theorem upper_selected_grid_family_bound
    {Y Z P M N R Q U K V Jsep D Cdelta Cupper Cv B delta Cmesh Ccard L T ε : ℝ}
    (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hZY : Z ≤ Y) (hP : 0 ≤ P)
    (hM : 0 ≤ M) (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q) (hK : 0 < K)
    (hV : 0 ≤ V) (hJ : 0 ≤ Jsep) (hD : 0 ≤ D) (hCd : 0 ≤ Cdelta)
    (hCu : 0 ≤ Cupper) (hCv : 0 ≤ Cv) (hB : 0 < B) (hd : 0 ≤ delta)
    (hCm : 0 < Cmesh) (hT : 1 ≤ T) (hε : 0 ≤ ε)
    (hQN : Q ≤ N) (hNR : N ≤ R^2) (hNT : N ≤ T)
    (hmesh : K ≤ Cmesh*Q*N/R^2)
    (hcard : P ≤ Ccard*Y*M*R^2/(N*Q^2)*L)
    (hVupper : V ≤ Cv*R^4/N^2) (hdelta : delta ≤ Cdelta*R^2/N^2)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B) ≤ U) :
    (R^2/Q)^6*K^((12:ℝ)+ε)*(2*P)^10*
      (V*D*Z*(M/N)*(1+delta*Jsep)+Z^2*V*(Cupper*M^2/(N^4*U))*T^ε) ≤
      (Cmesh^12*Cmesh^ε*(2*Ccard)^10)*T^(2*ε)*L^10*Cv*
        (D*(Y^11*M^11/(N*R^2))+
          D*Cdelta*(Y^11*Jsep*M^11/N^3)+
          2*B*Cupper*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))) := by
  have hQ : 0 < Q := hR.trans_le hRQ
  have hU := (physical_reference_reciprocal_bound hN hQ hB hUlower).1
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hTpow : 1 ≤ T^ε := Real.one_le_rpow hT hε
  let TypeI := V*D*Y*(M/N)*(1+delta*Jsep)
  let Pair := Y^2*V*(Cupper*M^2/(N^4*U))
  let Cpref := Cmesh^12*Cmesh^ε*(2*Ccard)^10
  let Physical := Y^10*M^10*N^2*R^8/Q^14
  have hTypeI : 0 ≤ TypeI := by dsimp only [TypeI]; positivity
  have hPair : 0 ≤ Pair := by dsimp only [Pair]; positivity
  have hCpref : 0 ≤ Cpref := by dsimp only [Cpref]; positivity
  have hPhysical : 0 ≤ Physical := by dsimp only [Physical]; positivity
  have hmass : V*D*Z*(M/N)*(1+delta*Jsep)+
      Z^2*V*(Cupper*M^2/(N^4*U))*T^ε ≤ (TypeI+Pair)*T^ε := by
    calc
      _ ≤ TypeI+Pair*T^ε := by dsimp only [TypeI,Pair]; gcongr
      _ ≤ TypeI*T^ε+Pair*T^ε :=
        add_le_add (le_mul_of_one_le_right hTypeI hTpow) le_rfl
      _ = _ := by ring
  have hpref := selected_band_mesh_cardinality_prefactor_bound
    hN hR hQ hK hP hCm hε hQN hNR hNT hmesh hcard
  have hmonomial := upper_physical_family_monomial_bound
    hY hM hN hR hRQ hJ hD hCd hCu hCv hB hd hVupper hdelta hUlower
  have hTproduct : T^ε*T^ε=T^(2*ε) := by
    rw [←Real.rpow_add hTp]
    congr 1
    ring
  calc
    _ ≤ (Cpref*T^ε*L^10*Physical)*((TypeI+Pair)*T^ε) := by
      exact mul_le_mul hpref hmass (by positivity) (by positivity)
    _ = Cpref*T^(2*ε)*L^10*(Physical*(TypeI+Pair)) := by
      calc
        _ = Cpref*(T^ε*T^ε)*L^10*(Physical*(TypeI+Pair)) := by ring
        _ = _ := by rw [hTproduct]
    _ ≤ Cpref*T^(2*ε)*L^10*
        (Cv*(D*(Y^11*M^11/(N*R^2))+
          D*Cdelta*(Y^11*Jsep*M^11/N^3)+
          2*B*Cupper*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)))) :=
      mul_le_mul_of_nonneg_left hmonomial (by positivity)
    _ = _ := by dsimp only [Cpref]; ring

example
    {Y Z P M N R Q U K V Jsep D Cdelta Cupper Cv B delta Cmesh Ccard L T ε : ℝ}
    (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hZY : Z ≤ Y) (hP : 0 ≤ P)
    (hM : 0 ≤ M) (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q) (hK : 0 < K)
    (hV : 0 ≤ V) (hJ : 0 ≤ Jsep) (hD : 0 ≤ D) (hCd : 0 ≤ Cdelta)
    (hCu : 0 ≤ Cupper) (hCv : 0 ≤ Cv) (hB : 0 < B) (hd : 0 ≤ delta)
    (hCm : 0 < Cmesh) (hT : 1 ≤ T) (hε : 0 ≤ ε)
    (hQN : Q ≤ N) (hNR : N ≤ R^2) (hNT : N ≤ T)
    (hmesh : K ≤ Cmesh*Q*N/R^2)
    (hcard : P ≤ Ccard*Y*M*R^2/(N*Q^2)*L)
    (hVupper : V ≤ Cv*R^4/N^2) (hdelta : delta ≤ Cdelta*R^2/N^2)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B) ≤ U) :
    (R^2/Q)^6*K^((12:ℝ)+ε)*(2*P)^10*
      (V*D*Z*(M/N)*(1+delta*Jsep)+Z^2*V*(Cupper*M^2/(N^4*U))*T^ε) ≤
      (Cmesh^12*Cmesh^ε*(2*Ccard)^10)*T^(2*ε)*L^10*Cv*
        (D*(Y^11*M^11/(N*R^2))+
          D*Cdelta*(Y^11*Jsep*M^11/N^3)+
          2*B*Cupper*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))) :=
  HuxleyBandScaleScratch.upper_selected_grid_family_bound (Y:=Y) (Z:=Z) (P:=P) (M:=M) (N:=N) (R:=R) (Q:=Q) (U:=U) (K:=K) (V:=V) (Jsep:=Jsep) (D:=D) (Cdelta:=Cdelta) (Cupper:=Cupper) (Cv:=Cv) (B:=B) (delta:=delta) (Cmesh:=Cmesh) (Ccard:=Ccard) (L:=L) (T:=T) (ε:=ε) hY hZ hZY hP hM hN hR hRQ hK hV hJ hD hCd hCu hCv hB hd hCm hT hε hQN hNR hNT hmesh hcard hVupper hdelta hUlower


#print axioms HuxleyBandScaleScratch.upper_selected_grid_family_bound



private theorem exists_source_cutoff_margins
    {κ Ccurv Cphys Sector Esize : ℝ}
    (hκ : 0 < κ) (hCcurv : 0 ≤ Ccurv) (hCphys : 0 ≤ Cphys)
    (hEsize : 0 < Esize) :
    ∃ Bcut Bselect : ℝ, 0 < Bcut ∧ 1 ≤ Bselect ∧
      2+168/κ ≤ Bselect ∧ 7*Bcut ≤ κ*Bselect ∧
      Sector ≤ Bselect*Esize ∧ 61*Ccurv*Cphys ≤ Bcut := by
  let Bcut := 1+61*Ccurv*Cphys
  let Bselect := max 1 (max (2+168/κ) (max (7*Bcut/κ) (Sector/Esize)))
  have hBcut : 0 < Bcut := by dsimp only [Bcut]; positivity
  have hBs : 1 ≤ Bselect := le_max_left _ _
  have hSize : 2+168/κ ≤ Bselect := (le_max_left _ _).trans (le_max_right _ _)
  have hCut : 7*Bcut/κ ≤ Bselect :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hSec : Sector/Esize ≤ Bselect :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨Bcut,Bselect,hBcut,hBs,hSize,?_,(div_le_iff₀ hEsize).mp hSec,?_⟩
  · calc
      7*Bcut ≤ Bselect*κ := (div_le_iff₀ hκ).mp hCut
      _ = κ*Bselect := mul_comm _ _
  · dsimp only [Bcut]
    linarith

example
    {κ Ccurv Cphys Sector Esize : ℝ}
    (hκ : 0 < κ) (hCcurv : 0 ≤ Ccurv) (hCphys : 0 ≤ Cphys)
    (hEsize : 0 < Esize) :
    ∃ Bcut Bselect : ℝ, 0 < Bcut ∧ 1 ≤ Bselect ∧
      2+168/κ ≤ Bselect ∧ 7*Bcut ≤ κ*Bselect ∧
      Sector ≤ Bselect*Esize ∧ 61*Ccurv*Cphys ≤ Bcut :=
  HuxleyBandScaleScratch.exists_source_cutoff_margins (κ:=κ) (Ccurv:=Ccurv) (Cphys:=Cphys) (Sector:=Sector) (Esize:=Esize) hκ hCcurv hCphys hEsize


#print axioms HuxleyBandScaleScratch.exists_source_cutoff_margins


private theorem upper_numerical_constants_nonnegative
    {σsrc csrc Usrc κ Cphys Csrc Couter CUP Dtype Bselect Csep ε : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) (hκ : 0 < κ)
    (hCphys : 0 ≤ Cphys) (hCsrcZero : 0 ≤ Csrc) (hCouter : 0 ≤ Couter)
    (hCUP : 0 ≤ CUP) (hDtype : 0 ≤ Dtype) (hBsOne : 1 ≤ Bselect)
    (hCsep : 1 ≤ Csep) :
    let εloss := ε/4
    let Cmesh := 2*max 1 (63*Usrc/(2*σsrc))
    let CtailBand := (6*Usrc/σsrc)*(64*σsrc/csrc)^2+192*σsrc/csrc
    let ClowBand := (3*Usrc/σsrc+csrc/(32*σsrc))*((3072*σsrc)/csrc)^2+(3072*σsrc)/csrc
    let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
    let Carg := 512*768*σsrc/csrc
    let DensityLog := 3+Real.log (Carg+1)
    let Cdensity := 128*CerrorBand*DensityLog
    let Ccard := 16*(1536:ℝ)^2+8*Cdensity
    let CKlog := 3+Real.log (Cmesh+1)
    let Cband := 2+1/Real.log 2
    let Cdelta := (16*Usrc/csrc)*Real.sqrt ((Usrc/(2*σsrc))*Cmesh)
    let Cmass := Dtype+Dtype*Cdelta+2*Bselect*CUP
    let Cfamily := Couter*
      (Cmesh^12*Cmesh^εloss*(2*Ccard)^10)*(7/6:ℝ)*Cmass
    let CE₀ := 2*Real.sqrt 3*(1+Real.log 6)+24*σsrc/csrc
    let Cterminal := Cdensity*Csep^2/8
    let Cendpoint := 112/κ+28*σsrc/csrc+2/(Cphys+2)+41/4
    let Cerror := 1+Csrc*CE₀+Cterminal+Cendpoint
    let Cgrid := (2:ℝ)^11*(Cerror^12+(Csrc*CKlog)^12*Cfamily)
    let Ctotal := (2:ℝ)^11*(Cband^11*Cerror^12+
      (4:ℝ)^12*(8:ℝ)^12*Cband^12*Cgrid+Cerror^12)
    0 ≤ CtailBand ∧
    0 ≤ ClowBand ∧
    0 ≤ CerrorBand ∧
    1 ≤ Cmesh ∧
    0 ≤ Carg ∧
    0 ≤ DensityLog ∧
    0 ≤ Cdensity ∧
    0 ≤ Ccard ∧
    0 ≤ CKlog ∧
    0 ≤ Cband ∧
    0 ≤ Cdelta ∧
    0 ≤ Cmass ∧
    0 ≤ Cfamily ∧
    0 ≤ CE₀ ∧
    0 ≤ Cterminal ∧
    0 ≤ Cendpoint ∧
    0 ≤ Cerror ∧
    Csrc*CE₀ ≤ Cerror ∧
    Cterminal ≤ Cerror ∧
    Cendpoint ≤ Cerror ∧
    0 ≤ Cgrid ∧
    0 ≤ Ctotal := by
  classical
  intro εloss Cmesh CtailBand ClowBand CerrorBand Carg DensityLog Cdensity Ccard CKlog Cband Cdelta Cmass Cfamily CE₀ Cterminal Cendpoint Cerror Cgrid Ctotal
  have hBs : 0 < Bselect := zero_lt_one.trans_le hBsOne
  have hCtailBand : 0 ≤ CtailBand := by dsimp only [CtailBand]; positivity
  have hClowBand : 0 ≤ ClowBand := by dsimp only [ClowBand]; positivity
  have hCerrorBand : 0 ≤ CerrorBand := by dsimp only [CerrorBand]; positivity
  have hCmeshOne : 1 ≤ Cmesh := by
    have hh := le_max_left (1:ℝ) (63*Usrc/(2*σsrc))
    dsimp only [Cmesh]
    linarith only [hh]
  have hCmesh : 0 < Cmesh := zero_lt_one.trans_le hCmeshOne
  have hCarg : 0 ≤ Carg := by dsimp only [Carg]; positivity
  have hDensityLog : 0 ≤ DensityLog := by
    have hh := Real.log_nonneg (show (1:ℝ) ≤ Carg+1 by linarith only [hCarg])
    dsimp only [DensityLog]
    linarith only [hh]
  have hCdensity : 0 ≤ Cdensity := by dsimp only [Cdensity]; positivity
  have hCcard : 0 ≤ Ccard := by dsimp only [Ccard]; positivity
  have hCKlog : 0 ≤ CKlog := by
    have hh := Real.log_nonneg (show (1:ℝ) ≤ Cmesh+1 by linarith only [hCmeshOne])
    dsimp only [CKlog]
    linarith only [hh]
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCband : 0 ≤ Cband := by dsimp only [Cband]; positivity
  have hCdelta : 0 ≤ Cdelta := by dsimp only [Cdelta]; positivity
  have hCmass : 0 ≤ Cmass := by dsimp only [Cmass]; positivity
  have hCfamily : 0 ≤ Cfamily := by dsimp only [Cfamily]; positivity
  have hlogSix : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have hCE₀ : 0 ≤ CE₀ := by dsimp only [CE₀]; positivity
  have hCterminal : 0 ≤ Cterminal := by dsimp only [Cterminal]; positivity
  have hCendpoint : 0 ≤ Cendpoint := by dsimp only [Cendpoint]; positivity
  have hCerror : 0 ≤ Cerror := by dsimp only [Cerror]; positivity
  have hErrorCompletion : Csrc*CE₀ ≤ Cerror := by
    dsimp only [Cerror]
    linarith only [hCterminal,hCendpoint]
  have hErrorTerminal : Cterminal ≤ Cerror := by
    dsimp only [Cerror]
    nlinarith only [mul_nonneg hCsrcZero hCE₀,hCendpoint]
  have hErrorEndpoint : Cendpoint ≤ Cerror := by
    dsimp only [Cerror]
    nlinarith only [mul_nonneg hCsrcZero hCE₀,hCterminal]
  have hCgrid : 0 ≤ Cgrid := by dsimp only [Cgrid]; positivity
  have hCtotal : 0 ≤ Ctotal := by dsimp only [Ctotal]; positivity

  exact ⟨hCtailBand,hClowBand,hCerrorBand,hCmeshOne,hCarg,hDensityLog,hCdensity,hCcard,hCKlog,hCband,hCdelta,hCmass,hCfamily,hCE₀,hCterminal,hCendpoint,hCerror,hErrorCompletion,hErrorTerminal,hErrorEndpoint,hCgrid,hCtotal⟩

example
    {σsrc csrc Usrc κ Cphys Csrc Couter CUP Dtype Bselect Csep ε : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) (hκ : 0 < κ)
    (hCphys : 0 ≤ Cphys) (hCsrcZero : 0 ≤ Csrc) (hCouter : 0 ≤ Couter)
    (hCUP : 0 ≤ CUP) (hDtype : 0 ≤ Dtype) (hBsOne : 1 ≤ Bselect)
    (hCsep : 1 ≤ Csep) :
    let εloss := ε/4
    let Cmesh := 2*max 1 (63*Usrc/(2*σsrc))
    let CtailBand := (6*Usrc/σsrc)*(64*σsrc/csrc)^2+192*σsrc/csrc
    let ClowBand := (3*Usrc/σsrc+csrc/(32*σsrc))*((3072*σsrc)/csrc)^2+(3072*σsrc)/csrc
    let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
    let Carg := 512*768*σsrc/csrc
    let DensityLog := 3+Real.log (Carg+1)
    let Cdensity := 128*CerrorBand*DensityLog
    let Ccard := 16*(1536:ℝ)^2+8*Cdensity
    let CKlog := 3+Real.log (Cmesh+1)
    let Cband := 2+1/Real.log 2
    let Cdelta := (16*Usrc/csrc)*Real.sqrt ((Usrc/(2*σsrc))*Cmesh)
    let Cmass := Dtype+Dtype*Cdelta+2*Bselect*CUP
    let Cfamily := Couter*
      (Cmesh^12*Cmesh^εloss*(2*Ccard)^10)*(7/6:ℝ)*Cmass
    let CE₀ := 2*Real.sqrt 3*(1+Real.log 6)+24*σsrc/csrc
    let Cterminal := Cdensity*Csep^2/8
    let Cendpoint := 112/κ+28*σsrc/csrc+2/(Cphys+2)+41/4
    let Cerror := 1+Csrc*CE₀+Cterminal+Cendpoint
    let Cgrid := (2:ℝ)^11*(Cerror^12+(Csrc*CKlog)^12*Cfamily)
    let Ctotal := (2:ℝ)^11*(Cband^11*Cerror^12+
      (4:ℝ)^12*(8:ℝ)^12*Cband^12*Cgrid+Cerror^12)
    0 ≤ CtailBand ∧
    0 ≤ ClowBand ∧
    0 ≤ CerrorBand ∧
    1 ≤ Cmesh ∧
    0 ≤ Carg ∧
    0 ≤ DensityLog ∧
    0 ≤ Cdensity ∧
    0 ≤ Ccard ∧
    0 ≤ CKlog ∧
    0 ≤ Cband ∧
    0 ≤ Cdelta ∧
    0 ≤ Cmass ∧
    0 ≤ Cfamily ∧
    0 ≤ CE₀ ∧
    0 ≤ Cterminal ∧
    0 ≤ Cendpoint ∧
    0 ≤ Cerror ∧
    Csrc*CE₀ ≤ Cerror ∧
    Cterminal ≤ Cerror ∧
    Cendpoint ≤ Cerror ∧
    0 ≤ Cgrid ∧
    0 ≤ Ctotal :=
  HuxleyBandScaleScratch.upper_numerical_constants_nonnegative (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) (κ:=κ) (Cphys:=Cphys) (Csrc:=Csrc) (Couter:=Couter) (CUP:=CUP) (Dtype:=Dtype) (Bselect:=Bselect) (Csep:=Csep) (ε:=ε) hσsrc hcsrc hUsrc hκ hCphys hCsrcZero hCouter hCUP hDtype hBsOne hCsep


#print axioms HuxleyBandScaleScratch.upper_numerical_constants_nonnegative


private theorem selected_grid_completion_bound
    {a b F E Main L W Cerror Clog Cfamily : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hMain : 0 ≤ Main) (hCf : 0 ≤ Cfamily)
    (hL : 1 ≤ L) (hW : 1 ≤ W)
    (haBound : a ≤ Cerror*E*L) (hbBound : b ≤ Clog*L)
    (hFBound : F ≤ Cfamily*W*L^10*Main) :
    (2:ℝ)^11*(a^12+b^12*F) ≤
      (2:ℝ)^11*(Cerror^12+Clog^12*Cfamily)*W*L^22*(E^12+Main) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hL12 : L^12 ≤ L^22 := pow_le_pow_right₀ hL (by norm_num)
  have hFirst : a^12 ≤ Cerror^12*W*L^22*E^12 := by
    calc
      _ ≤ (Cerror*E*L)^12 := pow_le_pow_left₀ ha haBound 12
      _ = Cerror^12*E^12*L^12 := by ring
      _ ≤ Cerror^12*E^12*L^22 := mul_le_mul_of_nonneg_left hL12 (by positivity)
      _ ≤ (Cerror^12*E^12*L^22)*W := le_mul_of_one_le_right (by positivity) hW
      _ = _ := by ring
  have hSecond : b^12*F ≤ (Clog^12*Cfamily)*W*L^22*Main := by
    calc
      _ ≤ b^12*(Cfamily*W*L^10*Main) :=
        mul_le_mul_of_nonneg_left hFBound (by positivity)
      _ ≤ (Clog*L)^12*(Cfamily*W*L^10*Main) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hb hbBound 12) (by positivity)
      _ = _ := by ring
  have hCross : Cerror^12*E^12+(Clog^12*Cfamily)*Main ≤
      (Cerror^12+Clog^12*Cfamily)*(E^12+Main) := by
    nlinarith only [
      mul_nonneg (show 0 ≤ Cerror^12 by positivity) hMain,
      mul_nonneg (show 0 ≤ Clog^12*Cfamily by positivity) (show 0 ≤ E^12 by positivity)]
  calc
    _ ≤ (2:ℝ)^11*(Cerror^12*W*L^22*E^12+(Clog^12*Cfamily)*W*L^22*Main) :=
      mul_le_mul_of_nonneg_left (add_le_add hFirst hSecond) (by positivity)
    _ = ((2:ℝ)^11*W*L^22)*(Cerror^12*E^12+(Clog^12*Cfamily)*Main) := by ring
    _ ≤ ((2:ℝ)^11*W*L^22)*((Cerror^12+Clog^12*Cfamily)*(E^12+Main)) :=
      mul_le_mul_of_nonneg_left hCross (by positivity)
    _ = _ := by ring

example
    {a b F E Main L W Cerror Clog Cfamily : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hMain : 0 ≤ Main) (hCf : 0 ≤ Cfamily)
    (hL : 1 ≤ L) (hW : 1 ≤ W)
    (haBound : a ≤ Cerror*E*L) (hbBound : b ≤ Clog*L)
    (hFBound : F ≤ Cfamily*W*L^10*Main) :
    (2:ℝ)^11*(a^12+b^12*F) ≤
      (2:ℝ)^11*(Cerror^12+Clog^12*Cfamily)*W*L^22*(E^12+Main) :=
  HuxleyBandScaleScratch.selected_grid_completion_bound (a:=a) (b:=b) (F:=F) (E:=E) (Main:=Main) (L:=L) (W:=W) (Cerror:=Cerror) (Clog:=Clog) (Cfamily:=Cfamily) ha hb hMain hCf hL hW haBound hbBound hFBound


#print axioms HuxleyBandScaleScratch.selected_grid_completion_bound



private theorem upper_selected_grid_family_total_bound
    {Y Z P M N R Q U K V Jsep D Cdelta Cupper Cv B delta Cmesh Ccard L T ε Couter : ℝ}
    (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hZY : Z ≤ Y) (hP : 0 ≤ P)
    (hM : 0 ≤ M) (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q) (hK : 0 < K)
    (hV : 0 ≤ V) (hJ : 0 ≤ Jsep) (hD : 0 ≤ D) (hCd : 0 ≤ Cdelta)
    (hCu : 0 ≤ Cupper) (hCv : 0 ≤ Cv) (hB : 0 < B) (hd : 0 ≤ delta)
    (hCm : 0 < Cmesh) (hT : 1 ≤ T) (hε : 0 ≤ ε) (hCo : 0 ≤ Couter)
    (hQN : Q ≤ N) (hNR : N ≤ R^2) (hNT : N ≤ T)
    (hmesh : K ≤ Cmesh*Q*N/R^2)
    (hcard : P ≤ Ccard*Y*M*R^2/(N*Q^2)*L)
    (hVupper : V ≤ Cv*R^4/N^2) (hdelta : delta ≤ Cdelta*R^2/N^2)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B) ≤ U) :
    Couter*(R^2/Q)^6*K^((12:ℝ)+ε)*(2*P)^10*
      (V*D*Z*(M/N)*(1+delta*Jsep)+Z^2*V*(Cupper*M^2/(N^4*U))*T^ε) ≤
      (Couter*(Cmesh^12*Cmesh^ε*(2*Ccard)^10)*Cv*(D+D*Cdelta+2*B*Cupper))*
        T^(2*ε)*L^10*
        (Y^11*M^11/(N*R^2)+Y^11*Jsep*M^11/N^3+
          Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) := by
  let m₁ := Y^11*M^11/(N*R^2)
  let m₂ := Y^11*Jsep*M^11/N^3
  let m₃ := Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)
  let Cmass := D+D*Cdelta+2*B*Cupper
  let Cpref := Cmesh^12*Cmesh^ε*(2*Ccard)^10
  have hm₁ : 0 ≤ m₁ := by dsimp only [m₁]; positivity
  have hm₂ : 0 ≤ m₂ := by dsimp only [m₂]; positivity
  have hm₃ : 0 ≤ m₃ := by dsimp only [m₃]; positivity
  have hDc := mul_nonneg hD hCd
  have hUc : 0 ≤ 2*B*Cupper := by positivity
  have hDmass : D ≤ Cmass :=
    (le_add_of_nonneg_right hDc).trans (le_add_of_nonneg_right hUc)
  have hDcmass : D*Cdelta ≤ Cmass :=
    (le_add_of_nonneg_left hD).trans (le_add_of_nonneg_right hUc)
  have hUcmass : 2*B*Cupper ≤ Cmass := le_add_of_nonneg_left (add_nonneg hD hDc)
  have hWeighted : D*m₁+D*Cdelta*m₂+2*B*Cupper*m₃ ≤ Cmass*(m₁+m₂+m₃) := by
    calc
      _ ≤ Cmass*m₁+Cmass*m₂+Cmass*m₃ :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_right hDmass hm₁)
          (mul_le_mul_of_nonneg_right hDcmass hm₂)) (mul_le_mul_of_nonneg_right hUcmass hm₃)
      _ = _ := by rw [mul_add, mul_add]
  have hCpref : 0 ≤ Cpref := by dsimp only [Cpref]; positivity
  have hraw := upper_selected_grid_family_bound
    hY hZ hZY hP hM hN hR hRQ hK hV hJ hD hCd hCu hCv hB hd hCm hT hε
    hQN hNR hNT hmesh hcard hVupper hdelta hUlower
  have hpref : 0 ≤ Cpref*T^(2*ε)*L^10*Cv :=
    mul_nonneg (mul_nonneg (mul_nonneg hCpref (Real.rpow_nonneg (zero_le_one.trans hT) _))
      (by positivity)) hCv
  calc
    _ = Couter*((R^2/Q)^6*K^((12:ℝ)+ε)*(2*P)^10*
        (V*D*Z*(M/N)*(1+delta*Jsep)+Z^2*V*(Cupper*M^2/(N^4*U))*T^ε)) := by
      simp only [mul_assoc]
    _ ≤ Couter*(Cpref*T^(2*ε)*L^10*Cv*(D*m₁+D*Cdelta*m₂+2*B*Cupper*m₃)) :=
      mul_le_mul_of_nonneg_left hraw hCo
    _ ≤ Couter*(Cpref*T^(2*ε)*L^10*Cv*(Cmass*(m₁+m₂+m₃))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hWeighted hpref) hCo
    _ = _ := by
      change Couter*(Cpref*T^(2*ε)*L^10*Cv*(Cmass*(m₁+m₂+m₃))) =
        (Couter*Cpref*Cv*Cmass)*T^(2*ε)*L^10*(m₁+m₂+m₃)
      ac_rfl

example
    {Y Z P M N R Q U K V Jsep D Cdelta Cupper Cv B delta Cmesh Ccard L T ε Couter : ℝ}
    (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hZY : Z ≤ Y) (hP : 0 ≤ P)
    (hM : 0 ≤ M) (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q) (hK : 0 < K)
    (hV : 0 ≤ V) (hJ : 0 ≤ Jsep) (hD : 0 ≤ D) (hCd : 0 ≤ Cdelta)
    (hCu : 0 ≤ Cupper) (hCv : 0 ≤ Cv) (hB : 0 < B) (hd : 0 ≤ delta)
    (hCm : 0 < Cmesh) (hT : 1 ≤ T) (hε : 0 ≤ ε) (hCo : 0 ≤ Couter)
    (hQN : Q ≤ N) (hNR : N ≤ R^2) (hNT : N ≤ T)
    (hmesh : K ≤ Cmesh*Q*N/R^2)
    (hcard : P ≤ Ccard*Y*M*R^2/(N*Q^2)*L)
    (hVupper : V ≤ Cv*R^4/N^2) (hdelta : delta ≤ Cdelta*R^2/N^2)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B) ≤ U) :
    Couter*(R^2/Q)^6*K^((12:ℝ)+ε)*(2*P)^10*
      (V*D*Z*(M/N)*(1+delta*Jsep)+Z^2*V*(Cupper*M^2/(N^4*U))*T^ε) ≤
      (Couter*(Cmesh^12*Cmesh^ε*(2*Ccard)^10)*Cv*(D+D*Cdelta+2*B*Cupper))*
        T^(2*ε)*L^10*
        (Y^11*M^11/(N*R^2)+Y^11*Jsep*M^11/N^3+
          Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) :=
  HuxleyBandScaleScratch.upper_selected_grid_family_total_bound (Y:=Y) (Z:=Z) (P:=P) (M:=M) (N:=N) (R:=R) (Q:=Q) (U:=U) (K:=K) (V:=V) (Jsep:=Jsep) (D:=D) (Cdelta:=Cdelta) (Cupper:=Cupper) (Cv:=Cv) (B:=B) (delta:=delta) (Cmesh:=Cmesh) (Ccard:=Ccard) (L:=L) (T:=T) (ε:=ε) (Couter:=Couter) hY hZ hZY hP hM hN hR hRQ hK hV hJ hD hCd hCu hCv hB hd hCm hT hε hCo hQN hNR hNT hmesh hcard hVupper hdelta hUlower


#print axioms upper_selected_grid_family_total_bound

private theorem eventually_upper_finite_numerical_consequence
    {σsrc csrc Usrc κ Cphys Csrc Couter CUP Dtype Bselect Csep ε : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) (hκ : 0 < κ)
    (hCphys : 0 ≤ Cphys) (hCsrcZero : 0 ≤ Csrc) (hCouter : 0 ≤ Couter)
    (hCUP : 0 ≤ CUP) (hDtype : 0 ≤ Dtype) (hBsOne : 1 ≤ Bselect)
    (hCsep : 1 ≤ Csep) (hε : 0 < ε) :
    let εloss := ε/4
    let Cmesh := 2*max 1 (63*Usrc/(2*σsrc))
    let CtailBand := (6*Usrc/σsrc)*(64*σsrc/csrc)^2+192*σsrc/csrc
    let ClowBand := (3*Usrc/σsrc+csrc/(32*σsrc))*((3072*σsrc)/csrc)^2+(3072*σsrc)/csrc
    let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Y : Finset ℝ)
      (n N Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ) (R M Jsep : ℝ)
      (Chunks : Finset (ℝ × ℤ)) (band : (ℝ × ℤ) → Option ℕ)
      (Dcover : ℕ → Finset (ℝ × ℤ)) {S : ℝ},
      N=8*n → 2 ≤ N → 1 ≤ R → (N:ℝ) ≤ R^2 → (N:ℝ)^2 ≤ M →
      M ≤ T → 0 ≤ Jsep → T*(N:ℝ)*R^2=M^3 →
      0 < Qbase → (Qbase:ℝ) ≤ 1536*R → (N:ℝ)/Csep ≤ (Qbase*2^kmax:ℕ) →
      (kmax:ℝ) ≤ Real.log N/Real.log 2 → (∀ k, 0 < Kmesh k) →
      let Q := fun k : ℕ => Qbase*2^k
      (∀ k ≤ kmax,
        R ≤ (Q k:ℝ) ∧ Q k ≤ N ∧
        (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
        (Kmesh k:ℝ) ≤ Cmesh*(Q k:ℝ)*(N:ℝ)/R^2 ∧
        (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
        ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Usel k:ℝ)) →
      let Yc := (Y.card:ℝ)
      let μ₀ := csrc*T/(12*σsrc*M^3)
      let U₀ := Usrc*T/(2*σsrc*M^3)
      let Vscale := 1+R^4/(6*(N:ℝ)^2)
      let Error := Yc*(M/(N:ℝ)+1)*
        (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
      let Δtype := fun k : ℕ =>
        (16*U₀/μ₀)*Real.sqrt (U₀*(Q k:ℝ)^3)*Real.sqrt (Kmesh k)/(6*(Kmesh k:ℝ)^2)
      let Buffer := fun k : ℕ =>
        (56*(Usel k:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
      let Width := fun k : ℕ => (14*σsrc/csrc)*(Usel k:ℝ)*(N:ℝ)
      let FamilyBound := fun (k : ℕ) (P : Finset (ℝ × ℤ)) =>
        Couter*(R^2/(Q k:ℝ))^6*(Kmesh k:ℝ)^((12:ℝ)+εloss)*(2*(P.card:ℝ))^10*
          (Vscale*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+(Δtype k)*Jsep)+
            ((P.image Prod.fst).card:ℝ)^2*Vscale*
              (CUP*M^2/((N:ℝ)^4*(Usel k:ℝ)))*T^εloss)
      let Density := fun k => 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
        (2+Real.log (512*σsrc*R^2/(csrc*((Q k:ℝ)/768))+1))
      let Endpoint := Yc*(2*Buffer 0+2*Width 0+6*(N:ℝ)+2*(n:ℝ))
      let Selected := fun k => Chunks.filter (fun p => band p=some k)
      let Grid := fun (k : ℕ) (r : ℤ) =>
        ((Dcover k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
      (Chunks.card:ℝ) ≤ Yc*(8*M/(N:ℝ)) →
      (∀ k ≤ kmax, ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤ Yc*Density k) →
      (∀ k ≤ kmax, ∀ r : ℤ, (Grid k r).card ≤ 2*(Selected k).card) →
      (∀ k ≤ kmax, ∀ r : ℤ, (Grid k r).image Prod.fst ⊆ Y) →
      S ≤ 2^11*(((kmax:ℝ)+2)^11*
        (((n:ℝ)*Yc*Density kmax)^12+
          (4:ℝ)^12*(8:ℝ)^11*∑ k∈Finset.range (kmax+1),∑ r∈Finset.Ico (0:ℤ) 8,
            (2^11*((Csrc*Error)^12+
              (Csrc*(1+Real.log (Kmesh k)))^12*FamilyBound k (Grid k r))))+Endpoint^12) →
      let ErrorTotal := Yc*M/Real.sqrt (N:ℝ)+Yc*M*R^2/(N:ℝ)^2+
        Yc*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
      let Main := Yc^11*M^11/((N:ℝ)*R^2)+Yc^11*Jsep*M^11/(N:ℝ)^3+
        Yc^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
      S ≤ T^ε*(ErrorTotal^12+Main) := by

  classical
  intro εloss Cmesh CtailBand ClowBand CerrorBand
  have hεloss : 0 < εloss := by dsimp only [εloss]; linarith only [hε]
  have hBs : 0 < Bselect := zero_lt_one.trans_le hBsOne
  let Carg := 512*768*σsrc/csrc
  let DensityLog := 3+Real.log (Carg+1)
  let Cdensity := 128*CerrorBand*DensityLog
  let Ccard := 16*(1536:ℝ)^2+8*Cdensity
  let CKlog := 3+Real.log (Cmesh+1)
  let Cband := 2+1/Real.log 2
  let Cdelta := (16*Usrc/csrc)*Real.sqrt ((Usrc/(2*σsrc))*Cmesh)
  let Cmass := Dtype+Dtype*Cdelta+2*Bselect*CUP
  let Cfamily := Couter*
    (Cmesh^12*Cmesh^εloss*(2*Ccard)^10)*(7/6:ℝ)*Cmass
  let CE₀ := 2*Real.sqrt 3*(1+Real.log 6)+24*σsrc/csrc
  let Cterminal := Cdensity*Csep^2/8
  let Cendpoint := 112/κ+28*σsrc/csrc+2/(Cphys+2)+41/4
  let Cerror := 1+Csrc*CE₀+Cterminal+Cendpoint
  let Cgrid := (2:ℝ)^11*(Cerror^12+(Csrc*CKlog)^12*Cfamily)
  let Ctotal := (2:ℝ)^11*(Cband^11*Cerror^12+
    (4:ℝ)^12*(8:ℝ)^12*Cband^12*Cgrid+Cerror^12)
  have hConstants :
      0 ≤ CtailBand ∧ 0 ≤ ClowBand ∧ 0 ≤ CerrorBand ∧ 1 ≤ Cmesh ∧
      0 ≤ Carg ∧ 0 ≤ DensityLog ∧ 0 ≤ Cdensity ∧ 0 ≤ Ccard ∧
      0 ≤ CKlog ∧ 0 ≤ Cband ∧ 0 ≤ Cdelta ∧ 0 ≤ Cmass ∧
      0 ≤ Cfamily ∧ 0 ≤ CE₀ ∧ 0 ≤ Cterminal ∧ 0 ≤ Cendpoint ∧
      0 ≤ Cerror ∧ Csrc*CE₀ ≤ Cerror ∧ Cterminal ≤ Cerror ∧
      Cendpoint ≤ Cerror ∧ 0 ≤ Cgrid ∧ 0 ≤ Ctotal :=
    upper_numerical_constants_nonnegative (ε:=ε) hσsrc hcsrc hUsrc hκ hCphys hCsrcZero
      hCouter hCUP hDtype hBsOne hCsep
  obtain ⟨hCtailBand,hClowBand,hCerrorBand,hCmeshOne,hCarg,hDensityLog,hCdensity,hCcard,hCKlog,hCband,hCdelta,hCmass,hCfamily,hCE₀,hCterminal,hCendpoint,hCerror,hErrorCompletion,hErrorTerminal,hErrorEndpoint,hCgrid,hCtotal⟩ :=
    hConstants
  have hCmesh : 0 < Cmesh := zero_lt_one.trans_le hCmeshOne
  filter_upwards [eventually_selected_band_logarithmic_absorption hCtotal hε,
    Filter.eventually_ge_atTop (1:ℝ)] with T hAbs hTone
  intro Y n N Qbase kmax Kmesh Usel R M Jsep Chunks band Dcover S
    hNlink hNtwo hR hNR' hNsqM hMT hJsep hscale hQbase hBaseHi hEndLo hkmax hKpos
    Q hvalid Yc μ₀ U₀ Vscale Error Δtype Buffer Width FamilyBound Density Endpoint Selected Grid
    hChunks hBands hGridCount hGridImage hNorm ErrorTotal Main
  have hT : 0 < T := hAbs.1
  have hLogOne : 1 ≤ Real.log T := hAbs.2.1
  have hNreal : (2:ℝ) ≤ N := by exact_mod_cast hNtwo
  have hNp : (0:ℝ) < N := by linarith only [hNreal]
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hNOne : (1:ℝ) ≤ N := by linarith only [hNreal]
  have hM : 0 < M := (sq_pos_of_pos hNp).trans_le hNsqM
  have hNM : (N:ℝ) ≤ M :=
    (by nlinarith only [hNreal] : (N:ℝ) ≤ (N:ℝ)^2).trans hNsqM
  have hNT : (N:ℝ) ≤ T := hNM.trans hMT
  have hVscale : 1 ≤ Vscale := by
    have hh : 0 ≤ R^4/(6*(N:ℝ)^2) := by positivity
    dsimp only [Vscale]
    linarith only [hh]
  let L := 1+Real.log T
  have hL : 1 ≤ L := by dsimp only [L]; linarith only [hLogOne]
  have hLzero : 0 ≤ L := zero_le_one.trans hL
  have hYc : 0 ≤ Yc := Nat.cast_nonneg _
  have hMain : 0 ≤ Main :=
    add_nonneg
      (add_nonneg
        (div_nonneg (mul_nonneg (pow_nonneg hYc 11) (pow_nonneg hM.le 11))
          (mul_nonneg hNp.le (sq_nonneg R)))
        (div_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hYc 11) hJsep)
          (pow_nonneg hM.le 11)) (pow_nonneg hNp.le 3)))
      (mul_nonneg
        (div_nonneg (mul_nonneg (pow_nonneg hYc 12) (pow_nonneg hM.le 12))
          (mul_nonneg (pow_nonneg hNp.le 4) (sq_nonneg R)))
        (Real.rpow_pos_of_pos (div_pos hRp hNp) _).le)
  have hErrorTotal : 0 ≤ ErrorTotal :=
    add_nonneg
      (add_nonneg (div_nonneg (mul_nonneg hYc hM.le) (Real.sqrt_nonneg _))
        (div_nonneg (mul_nonneg (mul_nonneg hYc hM.le) (sq_nonneg R))
          (sq_nonneg (N:ℝ))))
      (mul_nonneg (mul_nonneg hYc hNp.le)
        (Real.rpow_pos_of_pos (div_pos hNp hRp) _).le)
  have hQpos (k : ℕ) : (0:ℝ) < Q k := by
    exact_mod_cast Nat.mul_pos hQbase (by positivity : 0 < 2^k)
  have hKreal (k : ℕ) : (0:ℝ) < Kmesh k := by exact_mod_cast hKpos k
  have hlogs (k : ℕ) (hk : k ≤ kmax) :
      2+Real.log (Carg*R^2/(Q k:ℝ)+1) ≤ DensityLog*L ∧
      1+Real.log (Kmesh k) ≤ CKlog*L ∧
      (kmax:ℝ)+2 ≤ Cband*L := by
    obtain ⟨hRQ,hQN,_,hKU,_,_⟩ := hvalid k hk
    have hQNreal : (Q k:ℝ) ≤ N := by exact_mod_cast hQN
    exact physical_band_logarithmic_bounds hCarg hCmeshOne hTone hR hRQ
      hQNreal hNR' hNT (hKreal k) hKU hkmax
  have hDensity (k : ℕ) (hk : k ≤ kmax) :
      Density k ≤ Cdensity*M*R^2/((N:ℝ)*(Q k:ℝ)^2)*L := by
    have harg : 512*σsrc*R^2/(csrc*((Q k:ℝ)/768))=Carg*R^2/(Q k:ℝ) := by
      dsimp only [Carg]
      field_simp [(hQpos k).ne']
    calc
      _ = 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
          (2+Real.log (Carg*R^2/(Q k:ℝ)+1)) := by
        dsimp only [Density]
        rw [harg]
      _ ≤ 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*(DensityLog*L) :=
        mul_le_mul_of_nonneg_left (hlogs k hk).1 (by positivity)
      _ = _ := by dsimp only [Cdensity]; ring
  have hBandCounts (k : ℕ) (hk : k ≤ kmax) :
      ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤
        Yc*(Cdensity*M*R^2/((N:ℝ)*(Q k:ℝ)^2)*L) :=
    (hBands k hk).trans (mul_le_mul_of_nonneg_left (hDensity k hk) hYc)
  have hGridCard (k : ℕ) (hk : k ≤ kmax) (r : ℤ) :
      ((Grid k r).card:ℝ) ≤ Ccard*Yc*M*R^2/((N:ℝ)*(Q k:ℝ)^2)*L := by
    exact selected_band_grid_cardinality_bound Chunks band Grid Qbase kmax hQbase
      hYc hM.le hNp hCdensity hL hBaseHi hChunks hBandCounts
      hGridCount k hk r
  have hGridPhase (k : ℕ) (hk : k ≤ kmax) (r : ℤ) :
      (((Grid k r).image Prod.fst).card:ℝ) ≤ Yc := by
    change (((Grid k r).image Prod.fst).card:ℝ) ≤ (Y.card:ℝ)
    exact_mod_cast Finset.card_le_card (hGridImage k hk r)
  have hDeltaType (k : ℕ) (hk : k ≤ kmax) :
      Δtype k ≤ Cdelta*R^2/(N:ℝ)^2 := by
    obtain ⟨_,_,hMesh,hKU,_,_⟩ := hvalid k hk
    exact positive_difference_source_type_spacing_bound hσsrc hcsrc hUsrc.le
      hT hM hNp hRp (hQpos k) (hKreal k) hCmesh.le hscale hMesh hKU
  have hVupper : Vscale ≤ (7/6:ℝ)*R^4/(N:ℝ)^2 := by
    obtain ⟨_,_,hv,_⟩ := positive_difference_source_physical_regime_coefficients
      hσsrc hcsrc hUsrc hκ hT hM hNp hRp hscale hNR' hNsqM
    exact hv

  have hFamily (k : ℕ) (hk : k ≤ kmax) (r : ℤ) :
      FamilyBound k (Grid k r) ≤ Cfamily*T^(2*εloss)*L^10*Main := by
    obtain ⟨hRQ,hQN,_,hKU,_,hUlower⟩ := hvalid k hk
    have hQNreal : (Q k:ℝ) ≤ N := by exact_mod_cast hQN
    have hdeltazero : 0 ≤ Δtype k := by dsimp only [Δtype,U₀,μ₀]; positivity
    exact upper_selected_grid_family_total_bound
      hYc (Nat.cast_nonneg ((Grid k r).image Prod.fst).card) (hGridPhase k hk r)
      (Nat.cast_nonneg (Grid k r).card) hM.le hNp hRp hRQ (hKreal k)
      (zero_le_one.trans hVscale) hJsep hDtype hCdelta hCUP
      (show (0:ℝ) ≤ 7/6 by norm_num) hBs hdeltazero hCmesh hTone hεloss.le hCouter
      hQNreal hNR' hNT hKU (hGridCard k hk r) hVupper (hDeltaType k hk) hUlower
  let E₁ := Yc*M/Real.sqrt (N:ℝ)
  let E₂ := Yc*M*R^2/(N:ℝ)^2
  let E₃ := Yc*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
  have hE₁ : 0 ≤ E₁ := div_nonneg (mul_nonneg hYc hM.le) (Real.sqrt_nonneg _)
  have hE₂ : 0 ≤ E₂ := div_nonneg (mul_nonneg (mul_nonneg hYc hM.le) (sq_nonneg R))
    (sq_nonneg (N:ℝ))
  have hE₃ : 0 ≤ E₃ := mul_nonneg (mul_nonneg hYc hNp.le)
    (Real.rpow_pos_of_pos (div_pos hNp hRp) _).le
  have hE₁₂Total : E₁+E₂ ≤ ErrorTotal := le_add_of_nonneg_right hE₃
  have hE₂Total : E₂ ≤ ErrorTotal := (le_add_of_nonneg_left hE₁).trans hE₁₂Total
  have hE₃Total : E₃ ≤ ErrorTotal := le_add_of_nonneg_left (add_nonneg hE₁ hE₂)
  have hCompletion : Csrc*Error ≤ Cerror*ErrorTotal*L := by
    have hraw := positive_difference_completion_error_physical_bound
      (R:=R) hYc hNOne hNM hMT (show 0 ≤ 12*σsrc/csrc by positivity)
    have he : Error ≤ CE₀*(E₁+E₂)*L := by
      convert hraw using 1
      · dsimp only [Error]
        ring
      · dsimp only [CE₀,E₁,E₂,L]
        ring
    calc
      _ ≤ Csrc*(CE₀*(E₁+E₂)*L) := mul_le_mul_of_nonneg_left he hCsrcZero
      _ = (Csrc*CE₀)*(E₁+E₂)*L := by simp only [mul_assoc]
      _ ≤ Cerror*ErrorTotal*L :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hErrorCompletion hE₁₂Total (add_nonneg hE₁ hE₂) hCerror) hLzero
  have hNlinkReal : (N:ℝ)=8*(n:ℝ) := by exact_mod_cast hNlink
  have hTerminalBound : (n:ℝ)*Yc*Density kmax ≤ Cerror*ErrorTotal*L := by
    have hnzero : 0 ≤ (n:ℝ)*Yc := mul_nonneg (Nat.cast_nonneg n) hYc
    have hcore := selected_terminal_density_bound (R:=R) hNp hM.le hYc hCdensity
      (zero_lt_one.trans_le hCsep) hLzero hNlinkReal hEndLo
    calc
      _ ≤ (n:ℝ)*Yc*(Cdensity*M*R^2/((N:ℝ)*(Q kmax:ℝ)^2)*L) :=
        mul_le_mul_of_nonneg_left (hDensity kmax le_rfl) hnzero
      _ ≤ Cterminal*E₂*L := hcore
      _ ≤ Cerror*ErrorTotal*L :=
        mul_le_mul_of_nonneg_right (mul_le_mul hErrorTerminal hE₂Total hE₂ hCerror) hLzero
  have hEndpointBound : Endpoint ≤ Cerror*ErrorTotal*L := by
    obtain ⟨hRQ,hQN,_,_,hUupper,_⟩ := hvalid 0 (Nat.zero_le _)
    have hQNreal : (Q 0:ℝ) ≤ N := by exact_mod_cast hQN
    have hraw := positive_difference_endpoint_error_physical_bound
      hYc hNOne hRp hRQ hQNreal hκ hσsrc.le hcsrc hCphys hBsOne hNlinkReal hUupper
    have he : Endpoint ≤ Cendpoint*E₃ := by
      exact hraw
    calc
      _ ≤ Cendpoint*E₃ := he
      _ ≤ Cerror*ErrorTotal := mul_le_mul hErrorEndpoint hE₃Total hE₃ hCerror
      _ ≤ Cerror*ErrorTotal*L := le_mul_of_one_le_right (mul_nonneg hCerror hErrorTotal) hL

  have hLogN : 0 ≤ Real.log (6*(N:ℝ)) :=
    Real.log_nonneg (by linarith only [hNreal])
  have hCompletionZero : 0 ≤ Csrc*Error := by dsimp only [Error]; positivity
  have hDensityZero (k : ℕ) : 0 ≤ Density k := by
    have harg : 1 ≤ 512*σsrc*R^2/(csrc*((Q k:ℝ)/768))+1 := by
      have hh : 0 ≤ 512*σsrc*R^2/(csrc*((Q k:ℝ)/768)) := by positivity
      linarith only [hh]
    have hh := Real.log_nonneg harg
    dsimp only [Density]
    positivity
  have hTerminalZero : 0 ≤ (n:ℝ)*Yc*Density kmax :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hYc) (hDensityZero kmax)
  have hEndpointZero : 0 ≤ Endpoint := by dsimp only [Endpoint,Buffer,Width]; positivity
  have hTpowOne : 1 ≤ T^(2*εloss) :=
    Real.one_le_rpow hTone (mul_nonneg (by norm_num) hεloss.le)
  let G := fun k r => 2^11*((Csrc*Error)^12+
    (Csrc*(1+Real.log (Kmesh k)))^12*FamilyBound k (Grid k r))
  have hG (k : ℕ) (hk : k ≤ kmax) (r : ℤ) :
      G k r ≤ Cgrid*T^(2*εloss)*L^22*(ErrorTotal^12+Main) := by
    have hKone : (1:ℝ) ≤ Kmesh k := by
      have hh : 1 ≤ Kmesh k := Nat.succ_le_iff.mpr (hKpos k)
      exact_mod_cast hh
    have hlogK := Real.log_nonneg hKone
    have hLogZero : 0 ≤ Csrc*(1+Real.log (Kmesh k)) :=
      mul_nonneg hCsrcZero (add_nonneg zero_le_one hlogK)
    have hLogBound : Csrc*(1+Real.log (Kmesh k)) ≤ (Csrc*CKlog)*L := by
      calc
        _ ≤ Csrc*(CKlog*L) := mul_le_mul_of_nonneg_left (hlogs k hk).2.1 hCsrcZero
        _ = _ := by simp only [mul_assoc]
    exact selected_grid_completion_bound hCompletionZero hLogZero hMain hCfamily hL hTpowOne
      hCompletion hLogBound (hFamily k hk r)
  have hClean := selected_band_finite_power_cleanup kmax G
    hTerminalZero hEndpointZero hMain hL hTpowOne hCband hCgrid
    (hlogs 0 (Nat.zero_le _)).2.2 hTerminalBound hEndpointBound
    (fun k hk r _ => hG k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) r) hNorm
  have hExp : 2*εloss=ε/2 := by dsimp only [εloss]; ring
  have hFactor : Ctotal*T^(2*εloss)*L^36 ≤ T^ε := by
    simpa only [hExp,L] using hAbs.2.2
  exact hClean.trans (mul_le_mul_of_nonneg_right hFactor
    (add_nonneg (pow_nonneg hErrorTotal 12) hMain))

example
    {σsrc csrc Usrc κ Cphys Csrc Couter CUP Dtype Bselect Csep ε : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) (hκ : 0 < κ)
    (hCphys : 0 ≤ Cphys) (hCsrcZero : 0 ≤ Csrc) (hCouter : 0 ≤ Couter)
    (hCUP : 0 ≤ CUP) (hDtype : 0 ≤ Dtype) (hBsOne : 1 ≤ Bselect)
    (hCsep : 1 ≤ Csep) (hε : 0 < ε) :
    let εloss := ε/4
    let Cmesh := 2*max 1 (63*Usrc/(2*σsrc))
    let CtailBand := (6*Usrc/σsrc)*(64*σsrc/csrc)^2+192*σsrc/csrc
    let ClowBand := (3*Usrc/σsrc+csrc/(32*σsrc))*((3072*σsrc)/csrc)^2+(3072*σsrc)/csrc
    let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Y : Finset ℝ)
      (n N Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ) (R M Jsep : ℝ)
      (Chunks : Finset (ℝ × ℤ)) (band : (ℝ × ℤ) → Option ℕ)
      (Dcover : ℕ → Finset (ℝ × ℤ)) {S : ℝ},
      N=8*n → 2 ≤ N → 1 ≤ R → (N:ℝ) ≤ R^2 → (N:ℝ)^2 ≤ M →
      M ≤ T → 0 ≤ Jsep → T*(N:ℝ)*R^2=M^3 →
      0 < Qbase → (Qbase:ℝ) ≤ 1536*R → (N:ℝ)/Csep ≤ (Qbase*2^kmax:ℕ) →
      (kmax:ℝ) ≤ Real.log N/Real.log 2 → (∀ k, 0 < Kmesh k) →
      let Q := fun k : ℕ => Qbase*2^k
      (∀ k ≤ kmax,
        R ≤ (Q k:ℝ) ∧ Q k ≤ N ∧
        (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
        (Kmesh k:ℝ) ≤ Cmesh*(Q k:ℝ)*(N:ℝ)/R^2 ∧
        (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
        ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Usel k:ℝ)) →
      let Yc := (Y.card:ℝ)
      let μ₀ := csrc*T/(12*σsrc*M^3)
      let U₀ := Usrc*T/(2*σsrc*M^3)
      let Vscale := 1+R^4/(6*(N:ℝ)^2)
      let Error := Yc*(M/(N:ℝ)+1)*
        (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
      let Δtype := fun k : ℕ =>
        (16*U₀/μ₀)*Real.sqrt (U₀*(Q k:ℝ)^3)*Real.sqrt (Kmesh k)/(6*(Kmesh k:ℝ)^2)
      let Buffer := fun k : ℕ =>
        (56*(Usel k:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
      let Width := fun k : ℕ => (14*σsrc/csrc)*(Usel k:ℝ)*(N:ℝ)
      let FamilyBound := fun (k : ℕ) (P : Finset (ℝ × ℤ)) =>
        Couter*(R^2/(Q k:ℝ))^6*(Kmesh k:ℝ)^((12:ℝ)+εloss)*(2*(P.card:ℝ))^10*
          (Vscale*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+(Δtype k)*Jsep)+
            ((P.image Prod.fst).card:ℝ)^2*Vscale*
              (CUP*M^2/((N:ℝ)^4*(Usel k:ℝ)))*T^εloss)
      let Density := fun k => 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
        (2+Real.log (512*σsrc*R^2/(csrc*((Q k:ℝ)/768))+1))
      let Endpoint := Yc*(2*Buffer 0+2*Width 0+6*(N:ℝ)+2*(n:ℝ))
      let Selected := fun k => Chunks.filter (fun p => band p=some k)
      let Grid := fun (k : ℕ) (r : ℤ) =>
        ((Dcover k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
      (Chunks.card:ℝ) ≤ Yc*(8*M/(N:ℝ)) →
      (∀ k ≤ kmax, ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤ Yc*Density k) →
      (∀ k ≤ kmax, ∀ r : ℤ, (Grid k r).card ≤ 2*(Selected k).card) →
      (∀ k ≤ kmax, ∀ r : ℤ, (Grid k r).image Prod.fst ⊆ Y) →
      S ≤ 2^11*(((kmax:ℝ)+2)^11*
        (((n:ℝ)*Yc*Density kmax)^12+
          (4:ℝ)^12*(8:ℝ)^11*∑ k∈Finset.range (kmax+1),∑ r∈Finset.Ico (0:ℤ) 8,
            (2^11*((Csrc*Error)^12+
              (Csrc*(1+Real.log (Kmesh k)))^12*FamilyBound k (Grid k r))))+Endpoint^12) →
      let ErrorTotal := Yc*M/Real.sqrt (N:ℝ)+Yc*M*R^2/(N:ℝ)^2+
        Yc*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
      let Main := Yc^11*M^11/((N:ℝ)*R^2)+Yc^11*Jsep*M^11/(N:ℝ)^3+
        Yc^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
      S ≤ T^ε*(ErrorTotal^12+Main) :=
  HuxleyBandScaleScratch.eventually_upper_finite_numerical_consequence (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) (κ:=κ) (Cphys:=Cphys) (Csrc:=Csrc) (Couter:=Couter) (CUP:=CUP) (Dtype:=Dtype) (Bselect:=Bselect) (Csep:=Csep) (ε:=ε) hσsrc hcsrc hUsrc hκ hCphys hCsrcZero hCouter hCUP hDtype hBsOne hCsep hε


#print axioms HuxleyBandScaleScratch.eventually_upper_finite_numerical_consequence

private theorem eventually_upper_quantitative_phase_subinterval_bound
    {σsrc csrc Usrc σ δ ε : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hδzero : 0 ≤ δ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hε : 0 < ε)
    (hanchorBudget : csrc ≤ 4*modelPhaseThirdLower σ*σsrc/(σ*(σ+1)+3)) :
    ∃ Cbudget η₀ : ℝ, 1 ≤ Cbudget ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (Y : Finset ℝ)
      (n N : ℕ) (R Jsep : ℝ) {η M : ℝ},
      N=8*n → 2 ≤ N → 1 ≤ R → 0 < η → η ≤ η₀ →
      0 < Jsep → Jsep ≤ M →
      (∀ y∈Y, y∈Icc (1:ℝ) 2) →
      (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j ≤ 6, |iteratedDeriv (j+1) Fsrc w| ≤ Usrc) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
      (∀ y∈Y, Expdb.IsApproximateModelPhaseFunction
        (fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)) σ 4 δ) →
      T*(N:ℝ)*R^2=M^3 →
      Cbudget*R ≤ N → Cbudget*(N:ℝ) ≤ R^2 → Cbudget*(N:ℝ)^2 ≤ M →
      (N:ℝ)^4 ≤ M*R^3 → (N:ℝ)^10 ≤ M^3*R^7 →
      ∀ A Bint : ℝ → ℤ, (∀ y∈Y, ⌈M⌉ ≤ A y) →
      (∀ y∈Y, A y ≤ Bint y) → (∀ y∈Y, Bint y ≤ ⌊2*M⌋) →
      let Yc := (Y.card:ℝ)
      let ErrorTotal := Yc*M/Real.sqrt (N:ℝ)+Yc*M*R^2/(N:ℝ)^2+
        Yc*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
      let Main := Yc^11*M^11/((N:ℝ)*R^2)+
        Yc^11*Jsep*M^11/(N:ℝ)^3+
        Yc^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
      (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y),
        (𝐞 (T*(Fsrc ((j:ℝ)/M)-Fsrc ((j:ℝ)/M+η*y))/(σsrc*η)):ℂ)‖)^12 ≤
        T^ε*(ErrorTotal^12+Main) := by

  classical
  let εloss := ε/4
  have hεloss : 0 < εloss := by dsimp only [εloss]; linarith only [hε]
  let κ := modelPhaseThirdLower σ
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  let Ratio := 18*Usrc^2/(σsrc*csrc*κ)
  let Lsource := max (8*Ratio^2)
    (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)/κ^2)
  have hLsource : 0 ≤ Lsource :=
    (by positivity : (0:ℝ) ≤ 8*Ratio^2).trans (le_max_left _ _)
  let θ := min (1/48:ℝ) (1/(16*(Lsource+3)))
  have hθ : 0 < θ := lt_min (by norm_num) (by positivity)
  have hθmax : θ ≤ 1/24 := (min_le_left _ _).trans (by norm_num)
  have hθaction : θ ≤ 1/(8*(Lsource+3)) := by
    apply (min_le_right _ _).trans
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (by nlinarith only [hLsource])
  obtain ⟨Csrc,η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
    hCsrc,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,hfinite⟩ :=
    eventually_positive_difference_triangular_selected_band_phase_subinterval_physical_sieve
      hσsrc hcsrc hUsrc hσ hεloss hanchorBudget
  let Cphys := σ*(σ+1)+1
  let c := κ/6
  let J := Cphys/6
  let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hc : 0 < c := by dsimp only [c]; positivity
  have hJ : 0 < J := by dsimp only [J]; positivity
  have hB : 1 ≤ B := le_max_left _ _
  have hBzero : 0 ≤ B := zero_le_one.trans hB
  let C₂ := modelPhaseJetCoefficient σ 2+δ
  let C₃ := modelPhaseJetCoefficient σ 3+δ
  let Ct := C₂/2+5*C₃/12
  let Cc := C₂/κ+C₃/(2*κ)
  have hC₂ : 0 ≤ C₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδzero
  have hC₃ : 0 ≤ C₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδzero
  have hC₄ : 0 ≤ modelPhaseJetCoefficient σ 4+δ :=
    add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδzero
  have hCR : 0 ≤ quarticReciprocalConstant σ δ := by
    dsimp only [quarticReciprocalConstant]
    positivity
  have hCN : 0 ≤ quarticNonlinearResidualConstant σ δ := by
    dsimp only [quarticNonlinearResidualConstant]
    positivity
  have hCt : 0 ≤ Ct := by dsimp only [Ct]; positivity
  have hCc : 0 ≤ Cc := by dsimp only [Cc]; positivity
  let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
  let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
    2*quarticNonlinearResidualConstant σ δ)/κ
  let Esize := κ/(16*(Cphys+2))
  let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
  let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
  let Lunit := 2*κ/Cphys
  let Gamma := Cphys/κ
  let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
  have hCcurv : 0 ≤ Ccurv := by dsimp only [Ccurv]; positivity
  have hKres : 0 ≤ Kres := by dsimp only [Kres]; positivity
  have hEsize : 0 < Esize := by dsimp only [Esize]; positivity
  have hDbase : 0 ≤ Dbase := by dsimp only [Dbase]; positivity
  have hTbase : 0 ≤ Tbase := by dsimp only [Tbase]; positivity
  have hLunit : 0 < Lunit := by dsimp only [Lunit]; positivity
  have hGamma : 0 < Gamma := by dsimp only [Gamma]; positivity
  have hCthird : 0 ≤ Cthird := by dsimp only [Cthird]; positivity
  let AupperConst := 2*Cupper*(Cthird+1)*1^2/(κ*Lunit^3)
  let BupperConst := Cupper*(Cthird+1)*1^2/Lunit^2+Dupper*(B+1)*1^2/4
  let DupperConst := θ*(3*Usrc/σsrc)*1/2
  have hAupper : 0 ≤ AupperConst := by dsimp only [AupperConst]; positivity
  have hBupper : 0 ≤ BupperConst := by dsimp only [BupperConst]; positivity
  have hDupper : 0 ≤ DupperConst := by dsimp only [DupperConst]; positivity
  let Sector := 2*3840*128^2*105*(Dbase+64*Tbase*Esize^2)
  obtain ⟨Bcut,Bselect,hBcut,hBsOne,hBsSize,hcutMargin,hsize,hBsize⟩ :=
    exists_source_cutoff_margins (Sector:=Sector) hκ hCcurv hCphys.le hEsize
  have hBs : 0 < Bselect := zero_lt_one.trans_le hBsOne
  let D₀ := 37*B/2+16*B*Cc+2*Ct+2*Cc
  have hD₀ : 0 ≤ D₀ := by dsimp only [D₀]; positivity
  obtain ⟨Csep,hCsep,hselect⟩ :=
    exists_uniform_dyadic_band_integer_scales (J:=Usrc) hσsrc hBsOne hD₀ hCN
  obtain ⟨Cbudget,hCbudget,hCsepBudget,hbudget⟩ :=
    exists_uniform_source_physical_budget (zero_le_one.trans hCsep)
      (show 0 ≤ 3*Usrc/σsrc by positivity)
      (show 0 ≤ 3*Usrc/(4*σsrc) by positivity) hBzero
      (show 0 ≤ 56/κ by positivity)
      (show 0 ≤ 1/(Cphys+2) by positivity)
      (show 0 ≤ 14*σsrc/csrc by positivity)

  let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
  let NarrowCap := (4/θ+3)*(72*Usrc^2/(σsrc*csrc*κ*θ)+3)
  let Cap := 3*ChartCap*NarrowCap
  have hChartCap : 0 ≤ ChartCap := by dsimp only [ChartCap]; positivity
  have hNarrowCap : 0 ≤ NarrowCap := by dsimp only [NarrowCap]; positivity
  have hCap : 0 ≤ Cap := by dsimp only [Cap]; positivity
  let CUP := 240*(9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+
    2*BupperConst+(3/2:ℝ)*DupperConst)
  have hCUP : 0 ≤ CUP := by dsimp only [CUP]; positivity
  let Couter := (48*σsrc/csrc)^6*C*Cap^11
  have hCouter : 0 ≤ Couter := by dsimp only [Couter]; positivity
  let CtailBand := (6*Usrc/σsrc)*(64*σsrc/csrc)^2+192*σsrc/csrc
  let ClowBand := (3*Usrc/σsrc+csrc/(32*σsrc))*((3072*σsrc)/csrc)^2+(3072*σsrc)/csrc
  let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
  have hNumeric := eventually_upper_finite_numerical_consequence
    hσsrc hcsrc hUsrc hκ hCphys.le (zero_le_one.trans hCsrc)
    hCouter hCUP hDtype.le hBsOne hCsep hε
  have hLog : ∀ᶠ T : ℝ in Filter.atTop, 1 ≤ Real.log T :=
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop 1)
  refine ⟨Cbudget,η₀,hCbudget,hη₀,hηcap,?_⟩
  filter_upwards [hfinite hθ hθmax hθaction,hNumeric,
    Filter.eventually_ge_atTop (1:ℝ),hLog] with T hfiniteT hNumericT hTone hLogOne
  intro Fsrc Y n N R Jsep η M hNlink hNtwo hR hη hηsmall hJsep hJM
    hy hsepY hreg hjets htests hnegative hmodels hscale
    hSepBudget hRadiusBudget hSquareBudget hNfour hNten A Bint hA hAB hBint
    Yc ErrorTotal Main
  have hT : 0 < T := zero_lt_one.trans_le hTone
  have hNreal : (2:ℝ) ≤ N := by exact_mod_cast hNtwo
  have hNp : (0:ℝ) < N := by linarith only [hNreal]
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hNOne : (1:ℝ) ≤ N := by linarith only [hNreal]
  have hNR : (N:ℝ) ≤ R^2 :=
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hCbudget hNp.le :
      (N:ℝ) ≤ Cbudget*N).trans hRadiusBudget
  have hCsepRoom : Csep*R ≤ N :=
    (mul_le_mul_of_nonneg_right hCsepBudget hRp.le).trans hSepBudget
  obtain ⟨Qbase,kmax,Kmesh,Usel,hBaseLo,hBaseHi,hEndLo,hEndHi,hkmax,hKpos,hvalid,hUmono⟩ :=
    hselect N R hR hNR hCsepRoom
  let Q := fun k : ℕ => Qbase*2^k
  have hUzero : (Usel 0:ℝ) ≤ N := by
    obtain ⟨_,_,_,_,_,_,hUupper,_,_,_,hQstrong,_,_,_⟩ := hvalid 0 (Nat.zero_le _)
    have hQone : (1:ℝ) ≤ Q 0 := by nlinarith only [hQstrong,hR]
    have hQzero : (0:ℝ) < Q 0 := zero_lt_one.trans_le hQone
    calc
      _ ≤ ((N:ℝ)/(Q 0:ℝ))^((2:ℝ)/3)/Bselect := hUupper
      _ ≤ ((N:ℝ)/(Q 0:ℝ))^((2:ℝ)/3) := div_le_self (by positivity) hBsOne
      _ ≤ (N:ℝ)^((2:ℝ)/3) := Real.rpow_le_rpow (by positivity)
        (div_le_self hNp.le hQone) (by norm_num)
      _ ≤ N := Real.rpow_le_self_of_one_le hNOne (by norm_num)
  obtain ⟨hM,hRN,hNR',hNsqM,hNRM,hNcube,hRM,hpad,hquartic,hquadratic,hsmall,hroom,hMTall⟩ :=
    hbudget (N:ℝ) R M (Usel 0:ℝ) hNreal hR hSepBudget hRadiusBudget hSquareBudget hUzero
  have hMT : M ≤ T := hMTall T hT hscale
  have hNM : (N:ℝ) ≤ M :=
    (by nlinarith only [hNreal] : (N:ℝ) ≤ (N:ℝ)^2).trans hNsqM
  have hNT : (N:ℝ) ≤ T := hNM.trans hMT
  have hRegimeLog : (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) :=
    hNfour.trans (le_mul_of_one_le_right (by positivity)
      (Real.one_le_rpow hLogOne (by norm_num)))
  let Vscale := 1+R^4/(6*(N:ℝ)^2)
  have hVscale : 1 ≤ Vscale := by
    have hh : 0 ≤ R^4/(6*(N:ℝ)^2) := by positivity
    dsimp only [Vscale]
    linarith only [hh]

  let μ₀ := csrc*T/(12*σsrc*M^3)
  let U₀ := Usrc*T/(2*σsrc*M^3)
  let Error := Yc*(M/(N:ℝ)+1)*
    (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
  let f := fun y w => T*(Fsrc (w/M)-Fsrc (w/M+η*y))/(σsrc*η)
  let Δtype := fun k : ℕ =>
    (16*U₀/μ₀)*Real.sqrt (U₀*(Q k:ℝ)^3)*Real.sqrt (Kmesh k)/(6*(Kmesh k:ℝ)^2)
  let Δ := fun k : ℕ => D₀*(Q k:ℝ)/(N:ℝ)
  let D := fun k : ℕ =>
    Δ k+quarticNonlinearResidualConstant σ δ*(2*(Q k:ℝ))/(N:ℝ)
  let Kupper := fun k : ℕ =>
    240*(M^2/((N:ℝ)^4*(Usel k:ℝ)))*
      (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
  let Buffer := fun k : ℕ =>
    (56*(Usel k:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
  let Width := fun k : ℕ => (14*σsrc/csrc)*(Usel k:ℝ)*(N:ℝ)
  let FamilyBound := fun (k : ℕ) (P : Finset (ℝ × ℤ)) =>
    (48*σsrc/csrc)^6*(R^2/(Q k:ℝ))^6*
      C*(Kmesh k:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(P.card:ℝ))^10*
        (Vscale*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+(Δtype k)*Jsep)+
          ((P.image Prod.fst).card:ℝ)^2*Vscale*(Kupper k)*T^εloss)
  let Density := fun k => 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
    (2+Real.log (512*σsrc*R^2/(csrc*((Q k:ℝ)/768))+1))
  let Endpoint := Yc*(2*Buffer 0+2*Width 0+6*(N:ℝ)+2*(n:ℝ))
  have hvalidTri : ∀ k ≤ kmax,
      12*Usrc ≤ σsrc*(Usel k:ℝ) ∧
      63*(Usrc/(2*σsrc*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
      (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
      1 ≤ Usel k ∧ Bselect^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
      (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
      Q k ≤ N ∧ (Usel k:ℝ) ≤ R^2 ∧
      768*R ≤ (Q k:ℝ) ∧ 2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧
      D k ≤ 1/2 ∧ Δ k < 1/2 := by
    intro k hk
    obtain ⟨hUL,hSource,hMesh,_,hU,hWrap,hUpper,_,hQN,hUR,hStrong,hMin,hD,hDelta⟩ :=
      hvalid k hk
    exact ⟨hUL,hSource,hMesh,hU,hWrap,hUpper,hQN,hUR,hStrong,hMin,hD,hDelta⟩
  have hRoom : 2*(Buffer 0+Width 0)+6*(N:ℝ) ≤ M := by
    convert hroom using 1
    dsimp only [Buffer,Width]
    ring
  obtain ⟨Chunks,band,Dcover,hChunks,hBands,hTerminal,hGrids,hNorm⟩ :=
    hfiniteT Fsrc Y n N Qbase kmax Kmesh Usel R Jsep Vscale true
      (η:=η) (M:=M) (δ:=δ) (Bcut:=Bcut) (Bselect:=Bselect)
      hKpos hNlink hη hηsmall hT hNtwo hR hRM hVscale hδzero hδ hJsep hJM
      hy hsepY hreg hjets htests hnegative hmodels hscale hpad hquartic hquadratic
      hRegimeLog hBcut hBsSize hcutMargin hNten hNsqM hNRM
      (by rfl) hsmall hNR' hRN hNcube hsize hBsize hvalidTri
      (fun k _ => hUmono k) hRoom A Bint hA hAB hBint
  let Selected := fun k => Chunks.filter (fun p => band p=some k)
  let Grid := fun (k : ℕ) (r : ℤ) =>
    ((Dcover k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
  let NumericFamily := fun (k : ℕ) (P : Finset (ℝ × ℤ)) =>
    Couter*(R^2/(Q k:ℝ))^6*(Kmesh k:ℝ)^((12:ℝ)+εloss)*(2*(P.card:ℝ))^10*
      (Vscale*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+(Δtype k)*Jsep)+
        ((P.image Prod.fst).card:ℝ)^2*Vscale*
          (CUP*M^2/((N:ℝ)^4*(Usel k:ℝ)))*T^εloss)
  have hQbaseReal : (0:ℝ) < Qbase := by nlinarith only [hBaseLo,hRp]
  have hQbase : 0 < Qbase := by exact_mod_cast hQbaseReal
  have hvalidNumeric : ∀ k ≤ kmax,
      R ≤ (Q k:ℝ) ∧ Q k ≤ N ∧
      (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
      (Kmesh k:ℝ) ≤ (2*max 1 (63*Usrc/(2*σsrc)))*(Q k:ℝ)*(N:ℝ)/R^2 ∧
      (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
      ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Usel k:ℝ) := by
    intro k hk
    obtain ⟨_,_,hMesh,hKU,_,_,hUpper,hLower,hQN,_,hStrong,_,_,_⟩ := hvalid k hk
    exact ⟨by nlinarith only [hStrong,hRp],hQN,hMesh,hKU,hUpper,hLower⟩
  have hKupper (k : ℕ) : Kupper k=CUP*M^2/((N:ℝ)^4*(Usel k:ℝ)) := by
    dsimp only [Kupper,CUP]
    simp only [div_eq_mul_inv]
    ac_rfl
  have hFamilyEq (k : ℕ) (P : Finset (ℝ × ℤ)) :
      FamilyBound k P=NumericFamily k P := by
    dsimp only [FamilyBound,NumericFamily]
    rw [hKupper]
    dsimp only [Couter]
    ac_rfl
  let S := (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y), (𝐞 (f y j):ℂ)‖)^12
  change S ≤ 2^11*(((kmax:ℝ)+2)^11*
    (((n:ℝ)*Yc*Density kmax)^12+
      (4:ℝ)^12*(8:ℝ)^11*∑ k∈Finset.range (kmax+1),∑ r∈Finset.Ico (0:ℤ) 8,
        (2^11*((Csrc*Error)^12+
          (Csrc*(1+Real.log (Kmesh k)))^12*FamilyBound k (Grid k r))))+Endpoint^12) at hNorm
  simp only [hFamilyEq] at hNorm
  exact hNumericT Y n N Qbase kmax Kmesh Usel R M Jsep Chunks band Dcover
    hNlink hNtwo hR hNR' hNsqM hMT hJsep.le hscale hQbase hBaseHi hEndLo hkmax hKpos
    hvalidNumeric hChunks hBands
    (fun k hk r => (hGrids k hk).2.2.1 r)
    (fun k hk r => (hGrids k hk).2.2.2 r) hNorm

example
    {σsrc csrc Usrc σ δ ε : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hδzero : 0 ≤ δ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hε : 0 < ε)
    (hanchorBudget : csrc ≤ 4*modelPhaseThirdLower σ*σsrc/(σ*(σ+1)+3)) :
    ∃ Cbudget η₀ : ℝ, 1 ≤ Cbudget ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (Y : Finset ℝ)
      (n N : ℕ) (R Jsep : ℝ) {η M : ℝ},
      N=8*n → 2 ≤ N → 1 ≤ R → 0 < η → η ≤ η₀ →
      0 < Jsep → Jsep ≤ M →
      (∀ y∈Y, y∈Icc (1:ℝ) 2) →
      (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j ≤ 6, |iteratedDeriv (j+1) Fsrc w| ≤ Usrc) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
      (∀ y∈Y, Expdb.IsApproximateModelPhaseFunction
        (fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)) σ 4 δ) →
      T*(N:ℝ)*R^2=M^3 →
      Cbudget*R ≤ N → Cbudget*(N:ℝ) ≤ R^2 → Cbudget*(N:ℝ)^2 ≤ M →
      (N:ℝ)^4 ≤ M*R^3 → (N:ℝ)^10 ≤ M^3*R^7 →
      ∀ A Bint : ℝ → ℤ, (∀ y∈Y, ⌈M⌉ ≤ A y) →
      (∀ y∈Y, A y ≤ Bint y) → (∀ y∈Y, Bint y ≤ ⌊2*M⌋) →
      let Yc := (Y.card:ℝ)
      let ErrorTotal := Yc*M/Real.sqrt (N:ℝ)+Yc*M*R^2/(N:ℝ)^2+
        Yc*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
      let Main := Yc^11*M^11/((N:ℝ)*R^2)+
        Yc^11*Jsep*M^11/(N:ℝ)^3+
        Yc^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
      (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y),
        (𝐞 (T*(Fsrc ((j:ℝ)/M)-Fsrc ((j:ℝ)/M+η*y))/(σsrc*η)):ℂ)‖)^12 ≤
        T^ε*(ErrorTotal^12+Main) :=
  HuxleyBandScaleScratch.eventually_upper_quantitative_phase_subinterval_bound (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) (σ:=σ) (δ:=δ) (ε:=ε) hσsrc hcsrc hUsrc hσ hδzero hδ hε hanchorBudget


#print axioms HuxleyBandScaleScratch.eventually_upper_quantitative_phase_subinterval_bound

end HuxleyBandScaleScratch
