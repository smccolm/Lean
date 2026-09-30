import TaoTrudgianYang2025.IntegerIntervalCount
import TaoTrudgianYang2025.HuxleyLinearForms
open scoped ContDiff BigOperators FourierTransform Classical
open Set Polynomial
open TaoTrudgianYang2025
open TaoTrudgianYang2025.HuxleyRationalPhase
namespace HuxleyTaggedComplementScratch

private theorem tagged_filtered_sum
    {ι : Type*} [DecidableEq ι] (Y : Finset ι) (S : ι → Finset ℤ)
    (P : ι × ℤ → Prop) [DecidablePred P] (H : ι → ℤ → ℝ) :
    (∑ p∈(Y.biUnion (fun i => (S i).image (fun k => (i,k)))).filter P,H p.1 p.2)=
      ∑ i∈Y,∑ k∈(S i).filter (fun k => P (i,k)),H i k := by
  classical
  rw [Finset.filter_biUnion]
  simp_rw [Finset.filter_image]
  have hd : Set.PairwiseDisjoint (↑Y)
      (fun i => ((S i).filter (fun k => P (i,k))).image (fun k => (i,k))) := by
    intro i _hi j _hj hij
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨k,_hk,hke⟩ := Finset.mem_image.mp hp
    obtain ⟨l,_hl,hle⟩ := Finset.mem_image.mp hq
    exact hij (congrArg Prod.fst (hke.trans hle.symm))
  rw [Finset.sum_biUnion hd]
  apply Finset.sum_congr rfl
  intro i _hi
  exact Finset.sum_image (fun k _hk l _hl hkl => Prod.mk.inj hkl |>.2)

private theorem huxley_sharp_tail_source_scale
    {σ c J M N R Q : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hQ : 0 < Q)
    (hRQ : R ≤ Q) (hNR : N*R ≤ M) :
    let Vcurv := 3*J*M/(2*σ*N*R^2)
    let D := 64*σ*R^2/(c*Q)
    let C := (6*J/σ)*(64*σ/c)^2+192*σ/c
    4*Vcurv*D^2+3*D*(2+Real.log (D+1)) ≤
      C*(M*R/(N*Q))*(2+Real.log (D+1)) := by
  intro Vcurv D C
  let A := 64*σ/c
  let K := M*R/(N*Q)
  let L := 2+Real.log (D+1)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hL : 1 ≤ L := by
    have hh := Real.log_nonneg (show 1 ≤ D+1 by linarith only [hD])
    dsimp only [L]
    linarith only [hh]
  have hratio : R/Q ≤ 1 := (div_le_one₀ hQ).mpr hRQ
  have hbase : R^2/Q ≤ K := by
    apply (div_le_div_iff₀ hQ (mul_pos hN hQ)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hNR (mul_nonneg hR.le hQ.le)]
  have hfirst : 4*Vcurv*D^2 ≤ (6*J/σ)*A^2*K*L := by
    have he : 4*Vcurv*D^2=((6*J/σ)*A^2*K)*(R/Q) := by
      dsimp only [Vcurv,D,A,K]
      field_simp
      ring
    rw [he]
    exact (mul_le_mul_of_nonneg_left hratio (by positivity)).trans
      (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hL (show 0 ≤ (6*J/σ)*A^2*K by positivity))
  have hsecond : 3*D*L ≤ 3*A*K*L := by
    have he : D=A*(R^2/Q) := by dsimp only [D,A]; ring
    rw [he,←mul_assoc (3:ℝ) A]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hbase (by positivity)) (by linarith only [hL])
  have hh := add_le_add hfirst hsecond
  convert hh using 1
  dsimp only [C,A]
  ring


private theorem huxley_low_anchor_source_scale
    {σ c J M N R Q B : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hQ : 1 ≤ Q) (hB : 0 ≤ B) (hRQ : R ≤ Q) (hNR : N*R ≤ M) :
    let Vcurv := 3*J*M/(2*σ*N*R^2)
    let delta := c/(64*σ*R^2)
    let D := B*R^2/(c*Q)
    let C := (3*J/σ+c/(32*σ))*(B/c)^2+B/c
    D*(2*(Vcurv+delta)*D+1) ≤ C*(M*R/(N*Q)) := by
  intro Vcurv delta D C
  let E := B/c
  let K := M*R/(N*Q)
  have hQp : 0 < Q := by linarith only [hQ]
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hratio : R/Q ≤ 1 := (div_le_one₀ hQp).mpr hRQ
  have hbase : R^2/Q ≤ K := by
    apply (div_le_div_iff₀ hQp (mul_pos hN hQp)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hNR (mul_nonneg hR.le hQp.le)]
  have hsquare : R^2/Q^2 ≤ K := by
    have he : R^2/Q^2=(R^2/Q)*(1/Q) := by ring
    rw [he]
    exact (mul_le_mul_of_nonneg_left ((div_le_one₀ hQp).mpr hQ)
      (by positivity)).trans (by simpa only [mul_one] using hbase)
  have hfirst : ((3*J/σ)*E^2*K)*(R/Q) ≤ (3*J/σ)*E^2*K := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hratio
      (show 0 ≤ (3*J/σ)*E^2*K by positivity)
  have hsecond : ((c/(32*σ))*E^2)*(R^2/Q^2) ≤ ((c/(32*σ))*E^2)*K :=
    mul_le_mul_of_nonneg_left hsquare (by positivity)
  have hthird : E*(R^2/Q) ≤ E*K := mul_le_mul_of_nonneg_left hbase hE
  calc
    _ = ((3*J/σ)*E^2*K)*(R/Q)+((c/(32*σ))*E^2)*(R^2/Q^2)+E*(R^2/Q) := by
      dsimp only [Vcurv,delta,D,E,K]
      field_simp
      ring
    _ ≤ ((3*J/σ)*E^2*K)+((c/(32*σ))*E^2)*K+E*K := add_le_add (add_le_add hfirst hsecond) hthird
    _ = _ := by dsimp only [C,E]; ring


theorem huxley_anchor_complement_source_scale
    (Q Acut : ℕ) {σ c J M N R B : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hA : 2 ≤ Acut) (hAQ : Acut ≤ Q) (hB : 0 ≤ B)
    (hRQ : (Acut:ℝ)*R ≤ Q) (hNR : N*R ≤ M) :
    let Vcurv := 3*J*M/(2*σ*N*R^2)
    let delta := c/(64*σ*R^2)
    let Dlow := B*R^2/(c*(Q:ℝ))
    let Dhigh := 64*σ*R^2/(c*((Q/Acut+1:ℕ):ℝ))
    let Dupper := 64*σ*R^2/(c*((Q:ℝ)/Acut))
    let Ctail := (6*J/σ)*(64*σ/c)^2+192*σ/c
    let Clow := (3*J/σ+c/(32*σ))*(B/c)^2+B/c
    (4*Vcurv*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1)))+
      Dlow*(2*(Vcurv+delta)*Dlow+1) ≤
        ((Acut:ℝ)*Ctail+Clow)*(M*R/(N*Q))*(2+Real.log (Dupper+1)) := by
  intro Vcurv delta Dlow Dhigh Dupper Ctail Clow
  have hAp : 0 < Acut := by omega
  have hQp : 0 < Q := by omega
  have hAr : (0:ℝ) < Acut := Nat.cast_pos.mpr hAp
  have hQr : (0:ℝ) < Q := Nat.cast_pos.mpr hQp
  have hA1 : (1:ℝ) ≤ Acut := by exact_mod_cast (show 1 ≤ Acut by omega)
  have hQ1 : (1:ℝ) ≤ Q := by exact_mod_cast hQp
  have hthreshold : (Q:ℝ)/Acut ≤ (Q/Acut+1:ℕ) := by
    apply (div_le_iff₀ hAr).mpr
    have hh : Q < Acut*(Q/Acut+1) := Nat.lt_mul_div_succ Q hAp
    have hr : (Q:ℝ) < (Acut:ℝ)*((Q/Acut+1:ℕ):ℝ) := by exact_mod_cast hh
    simpa only [mul_comm] using hr.le
  have hRQeff : R ≤ (Q:ℝ)/Acut := (le_div_iff₀ hAr).mpr (by nlinarith only [hRQ])
  have hRQfull : R ≤ (Q:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hA1 hR.le
    nlinarith only [hh,hRQ]
  have hDhigh : 0 ≤ Dhigh := by dsimp only [Dhigh]; positivity
  have hDupper : 0 ≤ Dupper := by dsimp only [Dupper]; positivity
  have hDle : Dhigh ≤ Dupper := by
    exact div_le_div_of_nonneg_left (by positivity)
      (mul_pos hc (div_pos hQr hAr)) (mul_le_mul_of_nonneg_left hthreshold hc.le)
  have hlog : 1 ≤ 2+Real.log (Dupper+1) := by
    have hh := Real.log_nonneg (show 1 ≤ Dupper+1 by linarith only [hDupper])
    linarith only [hh]
  have hhigh :
      4*Vcurv*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1)) ≤
        (Acut:ℝ)*Ctail*(M*R/(N*Q))*(2+Real.log (Dupper+1)) := by
    have hmono :
        4*Vcurv*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1)) ≤
          4*Vcurv*Dupper^2+3*Dupper*(2+Real.log (Dupper+1)) := by
      have hX : 0 ≤ Vcurv := by dsimp only [Vcurv]; positivity
      have hlogHigh : 0 ≤ Real.log (Dhigh+1) :=
        Real.log_nonneg (by linarith only [hDhigh])
      gcongr
    have hh := hmono.trans
      (huxley_sharp_tail_source_scale hσ hc hJ hM hN hR (div_pos hQr hAr) hRQeff hNR)
    change _ ≤ Ctail*(M*R/(N*((Q:ℝ)/Acut)))*(2+Real.log (Dupper+1)) at hh
    convert hh using 1
    field_simp
  have hlow : Dlow*(2*(Vcurv+delta)*Dlow+1) ≤
      Clow*(M*R/(N*Q))*(2+Real.log (Dupper+1)) := by
    have hh := huxley_low_anchor_source_scale hσ hc hJ hM hN hR hQ1 hB hRQfull hNR
    apply hh.trans
    have hp : 0 ≤ Clow*(M*R/(N*Q)) := by dsimp only [Clow]; positivity
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hlog hp
  convert add_le_add hhigh hlow using 1
  ring


example
    (Q Acut : ℕ) {σ c J M N R B : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hA : 2 ≤ Acut) (hAQ : Acut ≤ Q) (hB : 0 ≤ B)
    (hRQ : (Acut:ℝ)*R ≤ Q) (hNR : N*R ≤ M) :
    let Vcurv := 3*J*M/(2*σ*N*R^2)
    let delta := c/(64*σ*R^2)
    let Dlow := B*R^2/(c*(Q:ℝ))
    let Dhigh := 64*σ*R^2/(c*((Q/Acut+1:ℕ):ℝ))
    let Dupper := 64*σ*R^2/(c*((Q:ℝ)/Acut))
    let Ctail := (6*J/σ)*(64*σ/c)^2+192*σ/c
    let Clow := (3*J/σ+c/(32*σ))*(B/c)^2+B/c
    (4*Vcurv*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1)))+
      Dlow*(2*(Vcurv+delta)*Dlow+1) ≤
        ((Acut:ℝ)*Ctail+Clow)*(M*R/(N*Q))*(2+Real.log (Dupper+1)) :=
  HuxleyTaggedComplementScratch.huxley_anchor_complement_source_scale Q Acut (σ:=σ) (c:=c) (J:=J) (M:=M) (N:=N) (R:=R) (B:=B) hσ hc hJ hM hN hR hA hAQ hB hRQ hNR

private theorem tagged_cost_source_scale
    {a N C D Q L cost : ℝ}
    (ha : 0 ≤ a) (hN : 0 < N) (hQ : 0 < Q)
    (hcost : cost ≤ C*(D/(N*Q))*L) :
    a*N*cost ≤ a*C*(D/Q)*L := by
  calc
    _ ≤ a*N*(C*(D/(N*Q))*L) :=
      mul_le_mul_of_nonneg_left hcost (mul_nonneg ha hN.le)
    _ = _ := by field_simp

private theorem tagged_anchor_complement_grouped_count
    {ι : Type*} [DecidableEq ι] (Y : Finset ι) (S : ι → Finset ℤ)
    (F : ℝ → ℝ) (y : ι → ℝ) (anchor : ι → ℤ → ℚ)
    (N : ℕ) (s : ℝ) {σ c J η T M R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : ∀ i∈Y, y i∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hphase : T*(N:ℝ)*R^2=M^3)
    (hpoints : ∀ i∈Y, ∀ k∈S i, s+(N:ℝ)*k∈Icc M (2*M))
    (hdisjoint : ∀ i∈Y, ∀ j∈Y, i≠j → y i=y j → Disjoint (S i) (S j)) :
    let f := fun u w => T*(F (w/M)-F (w/M+η*u))/(σ*η)
    let h := fun u w => iteratedDeriv 2 (f u) w/2
    let t := fun k : ℤ => s+(N:ℝ)*k
    let delta := c/(64*σ*R^2)
    let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
    (∀ i∈Y, ∀ k∈S i,
      (anchor i k:ℝ)∈Ioo (h (y i) (t k)-delta) (h (y i) (t k)+delta) ∧
      ∀ a : ℚ, (a:ℝ)∈Ioo (h (y i) (t k)-delta) (h (y i) (t k)+delta) →
        (anchor i k).den ≤ a.den) →
    ∀ (Q Acut : ℕ) (Bmajor : ℝ), 2 ≤ Acut → Acut ≤ Q → 0 ≤ Bmajor →
      let Sall := Y.biUnion (fun i => (S i).image (fun k => (i,k)))
      let Good : ι × ℤ → Prop := fun p => Acut*(anchor p.1 p.2).den ≤ Q ∧
        Bmajor*R^2 ≤ c*(Q:ℝ)*(anchor p.1 p.2).den
      let Dlow := Bmajor*R^2/(c*(Q:ℝ))
      let Dhigh := 64*σ*R^2/(c*((Q/Acut+1:ℕ):ℝ))
      let Cost := 4*Vbound*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1))+
        Dlow*(2*(Vbound+delta)*Dlow+1)
      ((Sall.filter (fun p => ¬ Good p)).card:ℝ) ≤ ((Y.image y).card:ℝ)*Cost ∧
      ∀ H : ι → ℤ → ℕ, (∀ i∈Y, ∀ k∈S i, H i k ≤ N) →
        (∑ p∈Sall.filter (fun p => ¬ Good p),(H p.1 p.2:ℝ)) ≤
          ((Y.image y).card:ℝ)*(N:ℝ)*Cost := by
  classical
  intro f h t delta Vbound hanchors Q Acut Bmajor hA hAQ hB Sall Good Dlow Dhigh Cost
  let Phases := Y.image y
  let P := Sall.filter (fun p => ¬ Good p)
  let Grid := fun u => (Y.filter (fun i => y i=u)).biUnion S
  have hgrid u k : k∈Grid u ↔ ∃ i∈Y, y i=u ∧ k∈S i := by
    constructor
    · intro hk
      obtain ⟨i,hi,hk⟩ := Finset.mem_biUnion.mp hk
      exact ⟨i,(Finset.mem_filter.mp hi).1,(Finset.mem_filter.mp hi).2,hk⟩
    · rintro ⟨i,hi,hu,hk⟩
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,hu⟩,hk⟩
  let ag := fun u k => if hh : ∃ i∈Y, y i=u ∧ k∈S i then
    anchor (Classical.choose hh) k else (0:ℚ)
  have hag i (hi : i∈Y) k (hk : k∈S i) : ag (y i) k=anchor i k := by
    have hex : ∃ j∈Y, y j=y i ∧ k∈S j := ⟨i,hi,rfl,hk⟩
    dsimp only [ag]
    rw [dif_pos hex]
    have hh := Classical.choose_spec hex
    have he : Classical.choose hex=i := by
      by_contra hne
      exact Finset.disjoint_left.mp
        (hdisjoint _ hh.1 i hi hne hh.2.1) hh.2.2 hk
    rw [he]
  have hmem p : p∈Sall ↔ p.1∈Y ∧ p.2∈S p.1 := by
    constructor
    · intro hp
      obtain ⟨i,hi,hp⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨k,hk,he⟩ := Finset.mem_image.mp hp
      subst p
      exact ⟨hi,hk⟩
    · rintro ⟨hi,hk⟩
      exact Finset.mem_biUnion.mpr ⟨p.1,hi,Finset.mem_image.mpr ⟨p.2,hk,rfl⟩⟩
  have hGcount u (hu : u∈Phases) :
      ((Grid u).filter (fun k => ¬ (Acut*(ag u k).den ≤ Q ∧
        Bmajor*R^2 ≤ c*(Q:ℝ)*(ag u k).den))).card ≤ (Cost:ℝ) := by
    have hyp : u∈Icc (1:ℝ) 2 := by
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
      exact hy i hi
    have hpts k (hk : k∈Grid u) : t k∈Icc M (2*M) := by
      obtain ⟨i,hi,_hui,hk⟩ := (hgrid u k).mp hk
      exact hpoints i hi k hk
    have hanc k (hk : k∈Grid u) :
        (ag u k:ℝ)∈Ioo (h u (t k)-delta) (h u (t k)+delta) ∧
        ∀ a : ℚ, (a:ℝ)∈Ioo (h u (t k)-delta) (h u (t k)+delta) →
          (ag u k).den ≤ a.den := by
      obtain ⟨i,hi,hui,hk⟩ := (hgrid u k).mp hk
      rw [←hui,hag i hi k hk]
      exact hanchors i hi k hk
    exact (positive_difference_minimal_anchor_complement_count (Grid u) F (ag u) N s
      hσ hc hJ hη hηmax hyp hf hbound htests hnegative hT hM hN hR hphase
      hpts hanc Q Acut Bmajor hA hAQ hB).1
  have hfiber u (hu : u∈Phases) :
      ((P.filter (fun p => y p.1=u)).card:ℝ) ≤ Cost := by
    let V := P.filter (fun p => y p.1=u)
    have hdata p (hp : p∈V) : p.1∈Y ∧ p.2∈S p.1 ∧ ¬ Good p ∧ y p.1=u := by
      have hh := Finset.mem_filter.mp hp
      have hpP := Finset.mem_filter.mp hh.1
      have hm := (hmem p).mp hpP.1
      exact ⟨hm.1,hm.2,hpP.2,hh.2⟩
    have hinj : Set.InjOn Prod.snd (V:Set (ι × ℤ)) := by
      intro p hp q hq he
      have hpS := hdata p hp
      have hqS := hdata q hq
      have hij : p.1=q.1 := by
        by_contra hne
        exact Finset.disjoint_left.mp
          (hdisjoint p.1 hpS.1 q.1 hqS.1 hne (hpS.2.2.2.trans hqS.2.2.2.symm))
          hpS.2.1 (by rw [he]; exact hqS.2.1)
      exact Prod.ext hij he
    have hsub : V.image Prod.snd ⊆ (Grid u).filter (fun k =>
        ¬ (Acut*(ag u k).den ≤ Q ∧ Bmajor*R^2 ≤ c*(Q:ℝ)*(ag u k).den)) := by
      intro k hk
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hk
      have hh := hdata p hp
      refine Finset.mem_filter.mpr ⟨(hgrid u p.2).mpr ⟨p.1,hh.1,hh.2.2.2,hh.2.1⟩,?_⟩
      rw [←hh.2.2.2,hag p.1 hh.1 p.2 hh.2.1]
      exact hh.2.2.1
    have hh := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hGcount u hu)
    rwa [Finset.card_image_of_injOn hinj] at hh
  have hcard : (P.card:ℝ) ≤ (Phases.card:ℝ)*Cost := by
    have he : (P.card:ℝ)=∑ u∈Phases,((P.filter (fun p => y p.1=u)).card:ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_fiberwise
        (fun p hp => Finset.mem_image_of_mem y ((hmem p).mp (Finset.mem_filter.mp hp).1).1)
    calc
      _ = _ := he
      _ ≤ ∑ _u∈Phases,Cost := Finset.sum_le_sum hfiber
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]
  refine ⟨hcard,?_⟩
  intro H hH
  have hNp : (0:ℝ) ≤ N := Nat.cast_nonneg _
  calc
    (∑ p∈P,(H p.1 p.2:ℝ)) ≤ ∑ _p∈P,(N:ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hh := (hmem p).mp (Finset.mem_filter.mp hp).1
      exact Nat.cast_le.mpr (hH p.1 hh.1 p.2 hh.2)
    _ = (N:ℝ)*(P.card:ℝ) := by simp only [Finset.sum_const,nsmul_eq_mul,mul_comm]
    _ ≤ (N:ℝ)*((Phases.card:ℝ)*Cost) := mul_le_mul_of_nonneg_left hcard hNp
    _ = _ := by ring

/-- Disjoint physical gaps of the same phase are combined before charging
the anchor error. The original tagged family retains one common Fourier
mode, with the number of DISTINCT phases, not the number of gap tags,
multiplying the explicit and MR/Q source-scale errors. -/
theorem positive_difference_tagged_gap_controlled_complement_fourier
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) (Y : Finset ι) (F : ℝ → ℝ)
      (N : ℕ) (s : ℤ) (H : ι → ℤ → ℕ)
      (η T M R U : ℝ) (y x₁ x₂ : ι → ℝ),
      1 ≤ N → (∀ i∈Y, ∀ k, H i k ≤ N) →
      0 < η → η ≤ 1/8 → (∀ i∈Y, y i∈Icc (1:ℝ) 2) →
      0 < T → 0 < M → 0 < R → 0 < U →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 → 7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      3*J ≤ σ*U →
      (∀ i∈Y, x₁ i∈Icc M (2*M)) → (∀ i∈Y, x₂ i∈Icc M (2*M)) →
      (∀ i∈Y, ∀ j∈Y, i≠j → y i=y j → x₂ i ≤ x₁ j ∨ x₂ j ≤ x₁ i) →
      let f := fun i w => T*(F (w/M)-F (w/M+η*y i))/(σ*η)
      let h := fun i w => iteratedDeriv 2 (f i) w/2
      let t := fun k : ℤ => (s:ℝ)+(N:ℝ)*k
      let L := fun k : ℤ => s+(N:ℤ)*k+2*(N:ℤ)
      let delta := c/(64*σ*R^2)
      let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
      (∀ i∈Y, U/(4*R^2) ≤ h i (x₂ i)-h i (x₁ i) ∧
        h i (x₂ i)-h i (x₁ i) ≤ 7*U/(2*R^2)) →
      ∃ (S : ι → Finset ℤ) (anchor : ι → ℤ → ℚ) (za : ι → ℤ → ℝ),
        (∀ i∈Y,
          (∀ k : ℤ, k∈(S i) ↔ (x₁ i)+(N:ℝ)/4 ≤ t k ∧ t k ≤ (x₂ i)-(N:ℝ)/4) ∧
        (∀ k∈(S i), (za i) k∈Ioo (x₁ i) (x₂ i) ∧ (h i) ((za i) k)=((anchor i) k:ℝ) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i) (x₁ i)) ((h i) (x₂ i)) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i) (t k)-delta) ((h i) (t k)+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo ((h i) (t k)-delta) ((h i) (t k)+delta) → ((anchor i) k).den ≤ a.den) ∧
        (∀ k∈(S i), |(za i) k-t k| ≤ (N:ℝ)/16) ∧
        (σ/(6*J))*U-3/2 ≤ ((S i).card:ℝ) ∧ ((S i).card:ℝ) ≤ (56*σ/c)*U+1/2 ∧
        (∀ Q : ℕ, 2 ≤ Q →
          let D := 64*σ*R^2/(c*(Q:ℝ))
          (((S i).filter (fun k => Q ≤ ((anchor i) k).den)).card:ℝ) ≤
            4*(Vbound+1)*D^2+D*(2+Real.log (D+1)))) ∧
      ∀ Q : ℕ, 2 ≤ Q → Q ≤ N →
      let Sall := Y.biUnion (fun i => (S i).image (fun k => (i,k)))
      let Good := fun i => 2*(anchor i.1 i.2).den ≤ Q ∧
        128*σ*R^2 ≤ c*(Q:ℝ)*(anchor i.1 i.2).den
      let G := Sall.filter Good
      let Dlow := 128*σ*R^2/(c*(Q:ℝ))
      let Khigh := Q/2+1
      let Dhigh := 64*σ*R^2/(c*(Khigh:ℝ))
      let Cost := 4*Vbound*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1))+
        Dlow*(2*(Vbound+delta)*Dlow+1)
      ∃ (r : ι × ℤ → ℚ) (z : ι × ℤ → ℝ),
      (∀ i∈G, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i.1 i.2:ℝ) < r i ∧ |(r i:ℝ)-(anchor i.1 i.2:ℝ)| ≤ c/(64*σ*R^2) ∧
        z i∈Icc (za i.1 i.2) (za i.1 i.2+(N:ℝ)/16) ∧
        iteratedDeriv 2 (f i.1) (z i)/2=(r i:ℝ)) ∧
      (∀ i∈G, z i∈Ioo (x₁ i.1) (x₂ i.1)) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i.2-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i.1) (m i)/6
      let ℓ := fun i => deriv (f i.1) (m i)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      (∀ i∈G, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i.2) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : ι × ℤ → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
      let FourierCost :=
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))
      let Cerror := 2*((6*J/σ)*(64*σ/c)^2+192*σ/c)+
        ((3*J/σ+c/(32*σ))*(128*σ/c)^2+128*σ/c)
      (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1 i.2),(𝐞 (f i.1 n):ℂ)‖) ≤ C*(((Y.image y).card:ℝ)*(N:ℝ)*Cost+FourierCost) ∧
      (2*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
        (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1 i.2),(𝐞 (f i.1 n):ℂ)‖) ≤
          C*(((Y.image y).card:ℝ)*Cerror*(M*R/Q)*(2+Real.log (Dlow+1))+FourierCost)) := by
  classical
  obtain ⟨C,hC,hentry⟩ := positive_difference_tagged_gap_dyadic_source_fourier hσ hc hJ
  refine ⟨C,hC,?_⟩
  intro ι Y F N s H η T M R U y x₁ x₂ hN hH hη hηmax hy hT hM hR hU
    hf hbound htests hnegative hphase hbuffer hfourBudget hquadBudget hUlarge hx₁ hx₂
    hGapSep f h t L delta Vbound hgap
  obtain ⟨S,anchor,za,hinfo,hfourier⟩ :=
    hentry ι Y F N s H η T M R U y x₁ x₂ hN hH hη hηmax hy hT hM hR hU
      hf hbound hnegative hphase hbuffer hfourBudget hquadBudget hUlarge hx₁ hx₂ hgap
  refine ⟨S,anchor,za,hinfo,?_⟩
  intro Q hQ hQN Sall Good G Dlow Khigh Dhigh Cost
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpoints i (hi : i∈Y) k (hk : k∈S i) : t k∈Icc M (2*M) := by
    have hh := ((hinfo i hi).1 k).mp hk
    constructor <;> linarith only [hh.1,hh.2,(hx₁ i hi).1,(hx₂ i hi).2,hNp]
  have hanchors i (hi : i∈Y) k (hk : k∈S i) := ((hinfo i hi).2.1 k hk).2.2.2
  have hdisjoint i (hi : i∈Y) j (hj : j∈Y) (hne : i≠j) (hye : y i=y j) :
      Disjoint (S i) (S j) := by
    apply Finset.disjoint_left.mpr
    intro k hki hkj
    have hai := ((hinfo i hi).1 k).mp hki
    have haj := ((hinfo j hj).1 k).mp hkj
    rcases hGapSep i hi j hj hne hye with hij | hji
    · linarith only [hai.1,hai.2,haj.1,haj.2,hij,hNp]
    · linarith only [hai.1,hai.2,haj.1,haj.2,hji,hNp]
  have hgroup := tagged_anchor_complement_grouped_count Y S F y anchor N (s:ℝ)
    hσ hc hJ hη hηmax hy hf hbound htests hnegative hT hM
    (show 0 < N by omega) hR hphase hpoints hdisjoint hanchors
    Q 2 (128*σ) (by norm_num) hQ (by positivity)
  have hweight : (∑ i∈Sall.filter (fun i => ¬ Good i),(H i.1 i.2:ℝ)) ≤
      ((Y.image y).card:ℝ)*(N:ℝ)*Cost :=
    hgroup.2 H (fun i hi k _ => hH i hi k)
  obtain ⟨r,z,hr,hzg,hcenter,hcompletion⟩ := hfourier Q hQN
  refine ⟨r,z,hr,hzg,hcenter,?_⟩
  dsimp only
  intro K₀ _ hK₀
  obtain ⟨v,hv,k,hfour⟩ := hcompletion K₀ hK₀
  refine ⟨v,hv,k,?_⟩
  let m := fun i => round (z i)
  let A := fun i => (L i.2-m i).toNat
  let q := fun i => (r i).den
  let μ := fun i => iteratedDeriv 3 (f i.1) (m i)/6
  let ℓ := fun i => deriv (f i.1) (m i)
  let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
  let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
  let stretch := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
  let K := fun i => -2*μ i*(stretch i)^3
  let x := fun i p =>
    (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
  let FourierCost :=
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))
  let Cerror := 2*((6*J/σ)*(64*σ/c)^2+192*σ/c)+
        ((3*J/σ+c/(32*σ))*(128*σ/c)^2+128*σ/c)
  have hbase : (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1 i.2),(𝐞 (f i.1 n):ℂ)‖) ≤ C*(((Y.image y).card:ℝ)*(N:ℝ)*Cost+FourierCost) := by
    apply hfour.trans
    dsimp only [FourierCost]
    rw [←add_assoc (((Y.image y).card:ℝ)*(N:ℝ)*Cost)]
    gcongr
  refine ⟨hbase,?_⟩
  intro hRQ hNR
  have hh := huxley_anchor_complement_source_scale Q 2
    hσ hc hJ hM hNp hR (by norm_num) hQ (show 0 ≤ 128*σ by positivity)
    (by simpa only [Nat.cast_ofNat] using hRQ) hNR
  have hDupper : 64*σ*R^2/(c*((Q:ℝ)/2))=Dlow := by dsimp only [Dlow]; ring
  have hcost : Cost ≤ Cerror*(M*R/((N:ℝ)*Q))*(2+Real.log (Dlow+1)) := by
    simpa only [Nat.cast_ofNat,hDupper] using hh
  have hscaled : ((Y.image y).card:ℝ)*(N:ℝ)*Cost ≤
      ((Y.image y).card:ℝ)*Cerror*(M*R/Q)*(2+Real.log (Dlow+1)) :=
    tagged_cost_source_scale (Nat.cast_nonneg _) hNp
      (by exact_mod_cast (show 0 < Q by omega)) hcost
  apply hbase.trans
  apply mul_le_mul_of_nonneg_left _ (by linarith only [hC])
  exact add_le_add hscaled (le_refl FourierCost)

example
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) (Y : Finset ι) (F : ℝ → ℝ)
      (N : ℕ) (s : ℤ) (H : ι → ℤ → ℕ)
      (η T M R U : ℝ) (y x₁ x₂ : ι → ℝ),
      1 ≤ N → (∀ i∈Y, ∀ k, H i k ≤ N) →
      0 < η → η ≤ 1/8 → (∀ i∈Y, y i∈Icc (1:ℝ) 2) →
      0 < T → 0 < M → 0 < R → 0 < U →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 → 7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      3*J ≤ σ*U →
      (∀ i∈Y, x₁ i∈Icc M (2*M)) → (∀ i∈Y, x₂ i∈Icc M (2*M)) →
      (∀ i∈Y, ∀ j∈Y, i≠j → y i=y j → x₂ i ≤ x₁ j ∨ x₂ j ≤ x₁ i) →
      let f := fun i w => T*(F (w/M)-F (w/M+η*y i))/(σ*η)
      let h := fun i w => iteratedDeriv 2 (f i) w/2
      let t := fun k : ℤ => (s:ℝ)+(N:ℝ)*k
      let L := fun k : ℤ => s+(N:ℤ)*k+2*(N:ℤ)
      let delta := c/(64*σ*R^2)
      let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
      (∀ i∈Y, U/(4*R^2) ≤ h i (x₂ i)-h i (x₁ i) ∧
        h i (x₂ i)-h i (x₁ i) ≤ 7*U/(2*R^2)) →
      ∃ (S : ι → Finset ℤ) (anchor : ι → ℤ → ℚ) (za : ι → ℤ → ℝ),
        (∀ i∈Y,
          (∀ k : ℤ, k∈(S i) ↔ (x₁ i)+(N:ℝ)/4 ≤ t k ∧ t k ≤ (x₂ i)-(N:ℝ)/4) ∧
        (∀ k∈(S i), (za i) k∈Ioo (x₁ i) (x₂ i) ∧ (h i) ((za i) k)=((anchor i) k:ℝ) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i) (x₁ i)) ((h i) (x₂ i)) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i) (t k)-delta) ((h i) (t k)+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo ((h i) (t k)-delta) ((h i) (t k)+delta) → ((anchor i) k).den ≤ a.den) ∧
        (∀ k∈(S i), |(za i) k-t k| ≤ (N:ℝ)/16) ∧
        (σ/(6*J))*U-3/2 ≤ ((S i).card:ℝ) ∧ ((S i).card:ℝ) ≤ (56*σ/c)*U+1/2 ∧
        (∀ Q : ℕ, 2 ≤ Q →
          let D := 64*σ*R^2/(c*(Q:ℝ))
          (((S i).filter (fun k => Q ≤ ((anchor i) k).den)).card:ℝ) ≤
            4*(Vbound+1)*D^2+D*(2+Real.log (D+1)))) ∧
      ∀ Q : ℕ, 2 ≤ Q → Q ≤ N →
      let Sall := Y.biUnion (fun i => (S i).image (fun k => (i,k)))
      let Good := fun i => 2*(anchor i.1 i.2).den ≤ Q ∧
        128*σ*R^2 ≤ c*(Q:ℝ)*(anchor i.1 i.2).den
      let G := Sall.filter Good
      let Dlow := 128*σ*R^2/(c*(Q:ℝ))
      let Khigh := Q/2+1
      let Dhigh := 64*σ*R^2/(c*(Khigh:ℝ))
      let Cost := 4*Vbound*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1))+
        Dlow*(2*(Vbound+delta)*Dlow+1)
      ∃ (r : ι × ℤ → ℚ) (z : ι × ℤ → ℝ),
      (∀ i∈G, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i.1 i.2:ℝ) < r i ∧ |(r i:ℝ)-(anchor i.1 i.2:ℝ)| ≤ c/(64*σ*R^2) ∧
        z i∈Icc (za i.1 i.2) (za i.1 i.2+(N:ℝ)/16) ∧
        iteratedDeriv 2 (f i.1) (z i)/2=(r i:ℝ)) ∧
      (∀ i∈G, z i∈Ioo (x₁ i.1) (x₂ i.1)) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i.2-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i.1) (m i)/6
      let ℓ := fun i => deriv (f i.1) (m i)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      (∀ i∈G, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i.2) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : ι × ℤ → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
      let FourierCost :=
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))
      let Cerror := 2*((6*J/σ)*(64*σ/c)^2+192*σ/c)+
        ((3*J/σ+c/(32*σ))*(128*σ/c)^2+128*σ/c)
      (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1 i.2),(𝐞 (f i.1 n):ℂ)‖) ≤ C*(((Y.image y).card:ℝ)*(N:ℝ)*Cost+FourierCost) ∧
      (2*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
        (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1 i.2),(𝐞 (f i.1 n):ℂ)‖) ≤
          C*(((Y.image y).card:ℝ)*Cerror*(M*R/Q)*(2+Real.log (Dlow+1))+FourierCost)) :=
  HuxleyTaggedComplementScratch.positive_difference_tagged_gap_controlled_complement_fourier (σ:=σ) (c:=c) (J:=J) hσ hc hJ

#print axioms positive_difference_tagged_gap_controlled_complement_fourier
#print axioms tagged_anchor_complement_grouped_count
#print axioms huxley_anchor_complement_source_scale
#print axioms tagged_filtered_sum
end HuxleyTaggedComplementScratch
