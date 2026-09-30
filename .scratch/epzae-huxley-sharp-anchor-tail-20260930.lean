import TaoTrudgianYang2025.IntegerIntervalCount
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import TaoTrudgianYang2025.HuxleyLinearForms
open scoped ContDiff BigOperators FourierTransform Classical
open Set Polynomial
open TaoTrudgianYang2025
open TaoTrudgianYang2025.HuxleyRationalPhase

namespace HuxleySharpAnchorTailScratch

private theorem bourgain_minimal_arc_dirichlet_compression
    {xi delta : ℝ} (hdelta : 0 < delta) (Q : ℕ) (hQ : 2 ≤ Q)
    (r : ℚ)
    (hminimal : ∀ t : ℚ, (t:ℝ)∈Ioo (xi-delta) (xi+delta) → r.den ≤ t.den)
    (hrQ : Q ≤ r.den) :
    ∃ a : ℚ, 0 < a.den ∧ a.den < Q ∧
      (a.den:ℝ) ≤ 1/(delta*(Q:ℝ)) ∧
      |xi-(a:ℝ)| ≤ 1/((Q:ℝ)*a.den) := by
  obtain ⟨a,ha,haden⟩ := Real.exists_rat_abs_sub_le_and_den_le xi
    (n:=Q-1) (by omega)
  have hQpred : ((Q-1:ℕ):ℝ)+1=Q := by
    have hh : Q-1+1=Q := by omega
    exact_mod_cast hh
  rw [hQpred] at ha
  have haQ : a.den < Q := by omega
  have hfar : delta ≤ |xi-(a:ℝ)| := by
    by_contra! hh
    have ht := abs_lt.mp hh
    have hinside : (a:ℝ)∈Ioo (xi-delta) (xi+delta) := by
      constructor <;> linarith only [ht.1,ht.2]
    have hm := hminimal a hinside
    omega
  have hQp : (0:ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hadp : (0:ℝ) < a.den := Nat.cast_pos.mpr a.pos
  refine ⟨a,a.pos,haQ,?_,ha⟩
  have hh := (le_div_iff₀ (mul_pos hQp hadp)).mp (hfar.trans ha)
  apply (le_div_iff₀ (mul_pos hdelta hQp)).mpr
  nlinarith only [hh]

private theorem bourgain_separated_level_band_count
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (k : ι → ℤ) (v : ι → ℝ)
    (B : ℕ) {eta a w : ℝ} (heta : 0 < eta) (hw : 0 ≤ w)
    (hmul : ∀ n : ℤ, (S.filter (fun i => k i=n)).card ≤ B)
    (hsep : ∀ i∈S, ∀ j∈S, eta*|(k i:ℝ)-k j| ≤ |v i-v j|) :
    ((S.filter (fun i => |v i-a| ≤ w)).card:ℝ) ≤
      B*(4*w/eta+1) := by
  classical
  let T := S.filter (fun i => |v i-a| ≤ w)
  by_cases hempty : T=∅
  · change (T.card:ℝ) ≤ _
    rw [hempty,Finset.card_empty,Nat.cast_zero]
    positivity
  obtain ⟨i₀,hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hTsub : T ⊆ S := Finset.filter_subset _ _
  have hnear i (hi : i∈T) : |(k i:ℝ)-k i₀| ≤ 2*w/eta := by
    have hpair := hsep i (hTsub hi) i₀ (hTsub hi₀)
    have hdist : |v i-v i₀| ≤ 2*w := by
      have hh := abs_sub_le (v i) a (v i₀)
      rw [abs_sub_comm a (v i₀)] at hh
      linarith only [hh,(Finset.mem_filter.mp hi).2,(Finset.mem_filter.mp hi₀).2]
    apply (le_div_iff₀ heta).mpr
    nlinarith only [hpair,hdist]
  have himage : ((T.image k).card:ℝ) ≤ 4*w/eta+1 := by
    have hb := integer_card_le_of_abs_sub_le (T.image k) (a:=(k i₀:ℝ))
      (B:=2*w/eta) (by positivity) (by
        intro n hn
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hn
        exact hnear i hi)
    convert hb using 1
    ring
  have hcard : T.card ≤ (T.image k).card*B := by
    calc
      _ = ∑ n∈T.image k,(T.filter (fun i => k i=n)).card :=
        Finset.card_eq_sum_card_image k T
      _ ≤ ∑ _n∈T.image k,B := by
        apply Finset.sum_le_sum
        intro n hn
        exact (Finset.card_le_card (Finset.filter_subset_filter _ hTsub)).trans (hmul n)
      _ = _ := by simp
  change (T.card:ℝ) ≤ _
  calc
    _ ≤ ((T.image k).card:ℝ)*B := by exact_mod_cast hcard
    _ ≤ (4*w/eta+1)*B := mul_le_mul_of_nonneg_right himage (Nat.cast_nonneg _)
    _ = _ := mul_comm _ _

private theorem bourgain_rational_neighborhood_block_count_sharp
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (k : ι → ℤ)
    (v : ι → ℝ) (a : ι → ℚ) (J Q B : ℕ) {eta Vcurv : ℝ}
    (heta : 0 < eta) (hQ : 0 < Q) (hX : 0 ≤ Vcurv)
    (hmul : ∀ n : ℤ, (S.filter (fun i => k i=n)).card ≤ B)
    (hsep : ∀ i∈S, ∀ j∈S, eta*|(k i:ℝ)-k j| ≤ |v i-v j|)
    (hv : ∀ i∈S, |v i| ≤ Vcurv)
    (hden : ∀ i∈S, (a i).den ≤ J)
    (hnear : ∀ i∈S, |v i-(a i:ℝ)| ≤ 1/((Q:ℝ)*(a i).den)) :
    (S.card:ℝ) ≤ B*∑ q∈Finset.Icc 1 J,
      (2*Vcurv*(q:ℝ)+3)*(4/(eta*(Q:ℝ)*q)+1) := by
  classical
  have hQr : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hQ1 : (1:ℝ) ≤ Q := by exact_mod_cast hQ
  have hnum i (hi : i∈S) : |((a i).num:ℝ)| ≤ Vcurv*(a i).den+1 := by
    have hd : (0:ℝ) < (a i).den := Nat.cast_pos.mpr (a i).pos
    have hval : |(a i:ℝ)| ≤ Vcurv+1/((Q:ℝ)*(a i).den) := by
      have hh := abs_add_le (v i) ((a i:ℝ)-v i)
      rw [add_sub_cancel,abs_sub_comm (a i:ℝ) (v i)] at hh
      linarith only [hh,hv i hi,hnear i hi]
    rw [Rat.cast_def,abs_div,abs_of_pos hd] at hval
    have hh := (div_le_iff₀ hd).mp hval
    have he : (Vcurv+1/((Q:ℝ)*(a i).den))*(a i).den=Vcurv*(a i).den+1/(Q:ℝ) := by
      field_simp
    rw [he] at hh
    have hinv : 1/(Q:ℝ) ≤ 1 := (div_le_one₀ hQr).mpr hQ1
    linarith only [hh,hinv]
  have hfiber (q : ℕ) (hq : q∈Finset.Icc 1 J) :
      ((S.filter (fun i => (a i).den=q)).card:ℝ) ≤
        (2*Vcurv*(q:ℝ)+3)*(B*(4/(eta*(Q:ℝ)*q)+1)) := by
    let T := S.filter (fun i => (a i).den=q)
    let W := T.image (fun i => (a i).num)
    have hqpos : 0 < q := by have hh := Finset.mem_Icc.mp hq; omega
    have hqr : (0:ℝ) < q := Nat.cast_pos.mpr hqpos
    have hW : (W.card:ℝ) ≤ 2*Vcurv*(q:ℝ)+3 := by
      have hh := integer_card_le_of_abs_sub_le W (a:=0) (B:=Vcurv*(q:ℝ)+1)
        (by positivity) (by
          intro p hp
          obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
          obtain ⟨hiS,he⟩ := Finset.mem_filter.mp hi
          simpa only [sub_zero,he] using hnum i hiS)
      convert hh using 1
      ring
    have hpcount p (hp : p∈W) :
        ((T.filter (fun i => (a i).num=p)).card:ℝ) ≤
          B*(4/(eta*(Q:ℝ)*q)+1) := by
      have hsub : T.filter (fun i => (a i).num=p) ⊆
          S.filter (fun i => |v i-(p:ℝ)/q| ≤ 1/((Q:ℝ)*q)) := by
        intro i hi
        obtain ⟨hiT,he⟩ := Finset.mem_filter.mp hi
        obtain ⟨hiS,hd⟩ := Finset.mem_filter.mp hiT
        refine Finset.mem_filter.mpr ⟨hiS,?_⟩
        simpa only [Rat.cast_def,he,hd] using hnear i hiS
      have hb := bourgain_separated_level_band_count S k v B heta
        (w:=1/((Q:ℝ)*q)) (a:=(p:ℝ)/q) (by positivity) hmul hsep
      have hc := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hb
      convert hc using 1
      ring
    calc
      _ = ∑ p∈W,((T.filter (fun i => (a i).num=p)).card:ℝ) := by
        exact_mod_cast Finset.card_eq_sum_card_image (fun i => (a i).num) T
      _ ≤ ∑ _p∈W,B*(4/(eta*(Q:ℝ)*q)+1) :=
        Finset.sum_le_sum (fun p hp => hpcount p hp)
      _ = (W.card:ℝ)*(B*(4/(eta*(Q:ℝ)*q)+1)) := by
        simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hW (by positivity)
  have hcard : S.card=∑ q∈Finset.Icc 1 J,(S.filter (fun i => (a i).den=q)).card :=
    Finset.card_eq_sum_card_fiberwise (fun i hi =>
      Finset.mem_Icc.mpr ⟨(a i).pos,hden i hi⟩)
  calc
    _ = ∑ q∈Finset.Icc 1 J,((S.filter (fun i => (a i).den=q)).card:ℝ) := by
      exact_mod_cast hcard
    _ ≤ ∑ q∈Finset.Icc 1 J,
        (2*Vcurv*(q:ℝ)+3)*(B*(4/(eta*(Q:ℝ)*q)+1)) :=
      Finset.sum_le_sum hfiber
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q hq; ring

private theorem bourgain_rational_neighborhood_block_count
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (k : ι → ℤ)
    (v : ι → ℝ) (a : ι → ℚ) (J Q B : ℕ) {eta Vcurv : ℝ}
    (heta : 0 < eta) (hQ : 0 < Q) (hX : 0 ≤ Vcurv)
    (hmul : ∀ n : ℤ, (S.filter (fun i => k i=n)).card ≤ B)
    (hsep : ∀ i∈S, ∀ j∈S, eta*|(k i:ℝ)-k j| ≤ |v i-v j|)
    (hv : ∀ i∈S, |v i| ≤ Vcurv)
    (hden : ∀ i∈S, (a i).den ≤ J)
    (hnear : ∀ i∈S, |v i-(a i:ℝ)| ≤ 1/((Q:ℝ)*(a i).den)) :
    (S.card:ℝ) ≤ B*∑ q∈Finset.Icc 1 J,
      (2*(Vcurv+1)*(q:ℝ)+1)*(4/(eta*(Q:ℝ)*q)+1) := by
  classical
  have hh := bourgain_rational_neighborhood_block_count_sharp S k v a J Q B
    heta hQ hX hmul hsep hv hden hnear
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg B)
  apply Finset.sum_le_sum
  intro q hq
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
  nlinarith only [hq1]

/-- Minimum-denominator tails without the spurious constant part of
the quadratic height cost. This consumes the supplied anchors themselves,
not newly selected rational values. -/
theorem bourgain_actual_minimal_arc_sharp_tail
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (k : ι → ℤ)
    (v : ι → ℝ) (r : ι → ℚ) (B : ℕ) {eta delta Vcurv : ℝ}
    (heta : 0 < eta) (hdelta : 0 < delta) (hX : 0 ≤ Vcurv)
    (hwidth : 4*delta ≤ eta)
    (hmul : ∀ n : ℤ, (S.filter (fun i => k i=n)).card ≤ B)
    (hsep : ∀ i∈S, ∀ j∈S, eta*|(k i:ℝ)-k j| ≤ |v i-v j|)
    (hv : ∀ i∈S, |v i| ≤ Vcurv)
    (hminimal : ∀ i∈S, ∀ a : ℚ,
      (a:ℝ)∈Ioo (v i-delta) (v i+delta) → (r i).den ≤ a.den) :
    ∀ Q : ℕ, 2 ≤ Q →
      let D := 1/(delta*(Q:ℝ))
      ((S.filter (fun i => Q ≤ (r i).den)).card:ℝ) ≤
        B*(4*Vcurv*D^2+3*D*(2+Real.log (D+1))) := by
  classical
  intro Q hQ D
  let G := S.filter (fun i => Q ≤ (r i).den)
  let J := ⌊D⌋₊
  have hGsub : G ⊆ S := Finset.filter_subset _ _
  have hQp : 0 < Q := by omega
  have hQr : (0:ℝ) < Q := Nat.cast_pos.mpr hQp
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hJ : (J:ℝ) ≤ D := Nat.floor_le hD
  have hex i : ∃ a : ℚ, i∈G →
      0 < a.den ∧ a.den < Q ∧ (a.den:ℝ) ≤ D ∧
        |v i-(a:ℝ)| ≤ 1/((Q:ℝ)*a.den) := by
    by_cases hi : i∈G
    · obtain ⟨a,ha⟩ := bourgain_minimal_arc_dirichlet_compression hdelta Q hQ
        (r i) (hminimal i (hGsub hi)) (Finset.mem_filter.mp hi).2
      exact ⟨a,fun _ => ha⟩
    · exact ⟨0,fun hh => False.elim (hi hh)⟩
  choose a ha using hex
  have hden i (hi : i∈G) : (a i).den ≤ J :=
    (Nat.le_floor_iff' (a i).pos.ne').mpr (ha i hi).2.2.1
  have hmulG n : (G.filter (fun i => k i=n)).card ≤ B :=
    (Finset.card_le_card (Finset.filter_subset_filter _ hGsub)).trans (hmul n)
  have hb := bourgain_rational_neighborhood_block_count_sharp G k v a J Q B
    heta hQp hX hmulG
    (fun i hi j hj => hsep i (hGsub hi) j (hGsub hj))
    (fun i hi => hv i (hGsub hi)) hden
    (fun i hi => (ha i hi).2.2.2)
  have hE : 4/(eta*(Q:ℝ)) ≤ D := by
    apply (div_le_div_iff₀ (mul_pos heta hQr) (mul_pos hdelta hQr)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hwidth hQr.le]
  have hlog : Real.log (J:ℝ) ≤ Real.log (D+1) := by
    by_cases hzero : J=0
    · rw [hzero,Nat.cast_zero,Real.log_zero]
      exact Real.log_nonneg (by linarith only [hD])
    · exact Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hzero))
        (by linarith only [hJ])
  have hharm : (∑ q∈Finset.Icc 1 J,1/(q:ℝ)) ≤ 1+Real.log (D+1) := by
    have hh : (∑ q∈Finset.Icc 1 J,1/(q:ℝ)) ≤ 1+Real.log J := by
      simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,
        Rat.cast_natCast,one_div] using harmonic_le_one_add_log J
    linarith only [hh,hlog]
  have hcard : (Finset.Icc 1 J).card=J := by simp
  have hlinear : (∑ q∈Finset.Icc 1 J,(2*Vcurv*(q:ℝ)+3)) ≤ (2*Vcurv*D+3)*D := by
    calc
      _ ≤ ∑ _q∈Finset.Icc 1 J,(2*Vcurv*D+3) := by
        apply Finset.sum_le_sum
        intro q hq
        have hqD : (q:ℝ) ≤ D := (Nat.cast_le.mpr (Finset.mem_Icc.mp hq).2).trans hJ
        nlinarith only [mul_nonneg hX (sub_nonneg.mpr hqD)]
      _ = (2*Vcurv*D+3)*(J:ℝ) := by simp only [Finset.sum_const,nsmul_eq_mul,hcard,mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left hJ (by positivity)
  have heq q (hq : q∈Finset.Icc 1 J) :
      (2*Vcurv*(q:ℝ)+3)*(4/(eta*(Q:ℝ)*q)+1)=
        (2*Vcurv*(q:ℝ)+3)+(4/(eta*(Q:ℝ)))*(2*Vcurv+3/(q:ℝ)) := by
    have hqp : (0:ℝ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
    field_simp
    ring
  have hsum :
      (∑ q∈Finset.Icc 1 J,(2*Vcurv*(q:ℝ)+3)*(4/(eta*(Q:ℝ)*q)+1)) ≤
        4*Vcurv*D^2+3*D*(2+Real.log (D+1)) := by
    calc
      _ = (∑ q∈Finset.Icc 1 J,(2*Vcurv*(q:ℝ)+3))+
          (4/(eta*(Q:ℝ)))*(2*Vcurv*J+3*∑ q∈Finset.Icc 1 J,1/(q:ℝ)) := by
        rw [Finset.sum_congr rfl heq]
        simp only [Finset.sum_add_distrib,div_eq_mul_inv,←Finset.mul_sum,
          Finset.sum_const,nsmul_eq_mul,hcard]
        ring
      _ ≤ (2*Vcurv*D+3)*D+D*(2*Vcurv*D+3*(1+Real.log (D+1))) := by
        apply add_le_add hlinear
        apply (mul_le_mul_of_nonneg_right hE (by positivity)).trans
        apply mul_le_mul_of_nonneg_left _ hD
        nlinarith only [hharm,mul_nonneg hX (sub_nonneg.mpr hJ)]
      _ = _ := by ring
  exact hb.trans (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg B))

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

/-- The actual physical minimum-denominator anchors satisfy the source-scale
large-denominator tail, including the original exponential sums. The
extra standalone quadratic cost in the previous tail is absent. -/
theorem positive_difference_actual_minimal_anchor_sharp_tail
    (S : Finset ℤ) (F : ℝ → ℝ) (anchor : ℤ → ℚ)
    (N : ℕ) (s : ℝ) {σ c J η y T M R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hphase : T*(N:ℝ)*R^2=M^3)
    (hpoints : ∀ i∈S, s+(N:ℝ)*i∈Icc M (2*M)) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun w => iteratedDeriv 2 f w/2
    let t := fun i : ℤ => s+(N:ℝ)*i
    let delta := c/(64*σ*R^2)
    let Vcurv := 3*J*M/(2*σ*(N:ℝ)*R^2)
    let C := (6*J/σ)*(64*σ/c)^2+192*σ/c
    (∀ i∈S, ∀ a : ℚ, (a:ℝ)∈Ioo (h (t i)-delta) (h (t i)+delta) →
      (anchor i).den ≤ a.den) →
    ∀ Q : ℕ, 2 ≤ Q →
      let High := S.filter (fun i => Q ≤ (anchor i).den)
      let D := 64*σ*R^2/(c*(Q:ℝ))
      (High.card:ℝ) ≤ 4*Vcurv*D^2+3*D*(2+Real.log (D+1)) ∧
      ((R ≤ (Q:ℝ)) → (N:ℝ)*R ≤ M →
        (High.card:ℝ) ≤ C*(M*R/((N:ℝ)*Q))*(2+Real.log (D+1)) ∧
        ∀ (L : ℤ → ℤ) (H : ℤ → ℕ), (∀ i∈S, H i ≤ N) →
          (∑ i∈High, ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f n):ℂ)‖) ≤
            C*(M*R/Q)*(2+Real.log (D+1))) := by
  classical
  intro f h t delta Vcurv C hanchors Q hQ High D
  have hNp : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hQp : (0:ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  let eta := c/(4*σ*R^2)
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  have hX : 0 ≤ Vcurv := by dsimp only [Vcurv]; positivity
  have hwidth : 4*delta ≤ eta := by
    have he : 4*delta=eta/4 := by dsimp only [delta,eta]; ring
    rw [he]
    linarith only [heta]
  have hsep i (hi : i∈S) j (hj : j∈S) :
      eta*|((id i:ℤ):ℝ)-(id j:ℤ)| ≤ |h (t i)-h (t j)| := by
    let V := |h (t i)-h (t j)|
    have he : 7*(2*R^2*V/7)/(2*R^2)=V := by field_simp
    have hnear : |h (t j)-h (t i)| ≤ 7*(2*R^2*V/7)/(2*R^2) := by
      rw [he,abs_sub_comm]
    have hw := positive_difference_reference_preimage_width F
      hσ hc hη hηmax hy hf hnegative hT hM hNp hR hphase
      (hpoints i hi) (hpoints j hj) hnear
    have hgrid : |t j-t i|=(N:ℝ)*|(i:ℝ)-j| := by
      rw [abs_sub_comm (t j) (t i),←abs_of_pos hNp,←abs_mul]
      congr 1
      dsimp only [t]
      ring
    rw [hgrid] at hw
    have hmul : (N:ℝ)*|(i:ℝ)-j| ≤ (N:ℝ)*((4*σ*R^2/c)*V) := by
      convert hw using 1
      ring
    have hh := (mul_le_mul_iff_right₀ hNp).mp hmul
    calc
      _ ≤ eta*((4*σ*R^2/c)*V) := mul_le_mul_of_nonneg_left hh heta.le
      _ = _ := by dsimp only [eta,V]; field_simp
  have hscale : T/M^2=M/((N:ℝ)*R^2) := by
    apply (div_eq_div_iff (by positivity) (by positivity)).mpr
    nlinarith only [hphase]
  have hv i (hi : i∈S) : |h (t i)| ≤ Vcurv := by
    have hh := (positive_difference_half_curvature_source_bounds F
      hσ hc hJ hη hηmax hT hM hy (hpoints i hi) hf hbound htests).2
    convert hh using 1
    calc
      Vcurv = (3*J/(2*σ))*(M/((N:ℝ)*R^2)) := by dsimp only [Vcurv]; ring
      _ = (3*J/σ)*T/(2*M^2) := by rw [←hscale]; ring
  have hmul n : (S.filter (fun i => id i=n)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    exact ((Finset.mem_filter.mp hi).2).trans ((Finset.mem_filter.mp hj).2).symm
  have hraw := bourgain_actual_minimal_arc_sharp_tail S id (fun i => h (t i))
    anchor 1 heta hdelta hX hwidth hmul hsep hv hanchors Q hQ
  have hD : 1/(delta*(Q:ℝ))=D := by dsimp only [delta,D]; field_simp
  rw [hD] at hraw
  simp only [Nat.cast_one,one_mul] at hraw
  refine ⟨hraw,?_⟩
  intro hRQ hNR
  have hcount := hraw.trans
    (huxley_sharp_tail_source_scale hσ hc hJ hM hNp hR hQp hRQ hNR)
  refine ⟨hcount,?_⟩
  intro L H hH
  calc
    (∑ i∈High, ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f n):ℂ)‖) ≤
        ∑ _i∈High,(N:ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hn : ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f n):ℂ)‖ ≤ H i := by
        apply (norm_sum_le _ _).trans_eq
        simp
      exact hn.trans (Nat.cast_le.mpr (hH i (Finset.mem_filter.mp hi).1))
    _ = (N:ℝ)*(High.card:ℝ) := by simp only [Finset.sum_const,nsmul_eq_mul,mul_comm]
    _ ≤ (N:ℝ)*(C*(M*R/((N:ℝ)*Q))*(2+Real.log (D+1))) :=
      mul_le_mul_of_nonneg_left hcount hNp.le
    _ = _ := by field_simp

private theorem positive_difference_near_anchor_injective
    (S : Finset ℤ) (F : ℝ → ℝ) (anchor : ℤ → ℚ)
    (N : ℕ) (s : ℝ) {σ c η y T M R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hphase : T*(N:ℝ)*R^2=M^3)
    (hpoints : ∀ i∈S, s+(N:ℝ)*i∈Icc M (2*M)) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun w => iteratedDeriv 2 f w/2
    let t := fun i : ℤ => s+(N:ℝ)*i
    (∀ i∈S, |(anchor i:ℝ)-h (t i)| ≤ c/(64*σ*R^2)) →
    Set.InjOn anchor (S : Set ℤ) := by
  intro f h t hnear i hi j hj he
  have hNp : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hcurv : |h (t i)-h (t j)| ≤ 7*(c/(112*σ))/(2*R^2) := by
    calc
      _ = |(h (t i)-(anchor i:ℝ))+((anchor j:ℝ)-h (t j))| := by rw [he]; congr 1; ring
      _ ≤ |h (t i)-(anchor i:ℝ)|+|(anchor j:ℝ)-h (t j)| := abs_add_le _ _
      _ ≤ c/(64*σ*R^2)+c/(64*σ*R^2) := by
        rw [abs_sub_comm (h (t i)) (anchor i:ℝ)]
        exact add_le_add (hnear i hi) (hnear j hj)
      _ = _ := by ring
  have hwidth := positive_difference_reference_preimage_width F
    hσ hc hη hηmax hy hf hnegative hT hM hNp hR hphase
    (hpoints i hi) (hpoints j hj) (by simpa only [abs_sub_comm] using hcurv)
  have hw : |t j-t i| ≤ (N:ℝ)/8 := by
    convert hwidth using 1
    field_simp
    ring
  have heq : |t j-t i|=(N:ℝ)*|((j-i:ℤ):ℝ)| := by
    rw [←abs_of_pos hNp,←abs_mul]
    congr 1
    dsimp only [t]
    push_cast
    ring
  rw [heq] at hw
  have hdiff : |((j-i:ℤ):ℝ)| < 1 := by nlinarith only [hw,hNp]
  have hz : j-i=0 := Int.abs_lt_one_iff.mp (by exact_mod_cast hdiff)
  exact (sub_eq_zero.mp hz).symm



/-- Both failures of the source anchor regime have derived counts.
The sharpened sparse tail consumes the actual supplied minimum-denominator
anchors. Neither a complement-cardinality nor a rational-fiber bound
is assumed. -/
theorem positive_difference_minimal_anchor_complement_count
    (S : Finset ℤ) (F : ℝ → ℝ) (anchor : ℤ → ℚ)
    (N : ℕ) (s : ℝ) {σ c J η y T M R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hphase : T*(N:ℝ)*R^2=M^3)
    (hpoints : ∀ i∈S, s+(N:ℝ)*i∈Icc M (2*M)) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun w => iteratedDeriv 2 f w/2
    let t := fun i : ℤ => s+(N:ℝ)*i
    let delta := c/(64*σ*R^2)
    let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
    (∀ i∈S, (anchor i:ℝ)∈Ioo (h (t i)-delta) (h (t i)+delta) ∧
      ∀ a : ℚ, (a:ℝ)∈Ioo (h (t i)-delta) (h (t i)+delta) → (anchor i).den ≤ a.den) →
    ∀ (Q Acut : ℕ) (Bmajor : ℝ), 2 ≤ Acut → Acut ≤ Q → 0 ≤ Bmajor →
    let Bad := S.filter (fun i => ¬ (Acut*(anchor i).den ≤ Q ∧
      Bmajor*R^2 ≤ c*(Q:ℝ)*(anchor i).den))
    let Dlow := Bmajor*R^2/(c*(Q:ℝ))
    let Khigh := Q/Acut+1
    let Dhigh := 64*σ*R^2/(c*(Khigh:ℝ))
    let Cost := 4*Vbound*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1))+
      Dlow*(2*(Vbound+delta)*Dlow+1)
    (Bad.card:ℝ) ≤ Cost ∧
      ∀ H : ℤ → ℕ, (∀ i∈S, H i ≤ N) →
        (∑ i∈Bad,(H i:ℝ)) ≤ (N:ℝ)*Cost := by
  classical
  intro f h t delta Vbound hanchors Q Acut Bmajor hAcut hAQ hBmajor
    Bad Dlow Khigh Dhigh Cost
  have hNp : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hQ : 0 < Q := by omega
  have hQr : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hApos : 0 < Acut := by omega
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  have hV : 0 ≤ Vbound := by dsimp only [Vbound]; positivity
  have hDlow : 0 ≤ Dlow := by dsimp only [Dlow]; positivity
  have hnear i (hi : i∈S) : |(anchor i:ℝ)-h (t i)| ≤ delta := by
    have hh := (hanchors i hi).1
    exact abs_le.mpr ⟨by linarith only [hh.1],by linarith only [hh.2]⟩
  have hinj := positive_difference_near_anchor_injective S F anchor N s
    hσ hc hη hηmax hy hf hnegative hT hM hN hR hphase hpoints hnear
  have hK : 2 ≤ Khigh := by
    have hh : 1 ≤ Q/Acut := (Nat.le_div_iff_mul_le hApos).mpr (by simpa only [one_mul] using hAQ)
    dsimp only [Khigh]
    omega
  let High := S.filter (fun i => Khigh ≤ (anchor i).den)
  have hhigh : (High.card:ℝ) ≤ 4*Vbound*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1)) := by
    exact (positive_difference_actual_minimal_anchor_sharp_tail S F anchor N s
      hσ hc hJ hη hηmax hy hf hbound htests hnegative hT hM hN hR hphase hpoints
      (fun i hi => (hanchors i hi).2) Khigh hK).1
  have hscale2 : T/M^2=M/((N:ℝ)*R^2) := by
    apply (div_eq_div_iff (by positivity) (by positivity)).mpr
    nlinarith only [hphase]
  have hvalues i (hi : i∈S) : |(anchor i:ℝ)| ≤ Vbound+delta := by
    have hh := (positive_difference_half_curvature_source_bounds F
      hσ hc hJ hη hηmax hT hM hy (hpoints i hi) hf hbound htests).2
    have he : (3*J/σ)*T/(2*M^2)=Vbound := by
      calc
        _ = (3*J/(2*σ))*(T/M^2) := by ring
        _ = Vbound := by rw [hscale2]; dsimp only [Vbound]; ring
    rw [he] at hh
    calc
      |(anchor i:ℝ)| = |((anchor i:ℝ)-h (t i))+h (t i)| := by rw [sub_add_cancel]
      _ ≤ |(anchor i:ℝ)-h (t i)|+|h (t i)| := abs_add_le _ _
      _ ≤ delta+Vbound := add_le_add (hnear i hi) hh
      _ = Vbound+delta := by ring
  let Low := S.filter (fun i => c*(Q:ℝ)*(anchor i).den < Bmajor*R^2)
  have hlowden i (hi : i∈Low) : (anchor i).den ≤ ⌊Dlow⌋₊ := by
    apply Nat.le_floor
    apply (le_div_iff₀ (mul_pos hc hQr)).mpr
    have hh := (Finset.mem_filter.mp hi).2
    nlinarith only [hh]
  have hlow : (Low.card:ℝ) ≤ Dlow*(2*(Vbound+delta)*Dlow+1) := by
    have hcount := bourgain_bounded_denominator_count Low anchor ⌊Dlow⌋₊ 1
      (add_nonneg hV hdelta.le) (fun i hi => hvalues i (Finset.mem_filter.mp hi).1) hlowden
      (by
        intro a
        apply Finset.card_le_one.mpr
        intro i hi j hj
        obtain ⟨hiL,hia⟩ := Finset.mem_filter.mp hi
        obtain ⟨hjL,hja⟩ := Finset.mem_filter.mp hj
        exact hinj (Finset.mem_filter.mp hiL).1 (Finset.mem_filter.mp hjL).1 (hia.trans hja.symm))
    simp only [Nat.cast_one,one_mul] at hcount
    apply hcount.trans
    have hfloor : (⌊Dlow⌋₊:ℝ) ≤ Dlow := Nat.floor_le hDlow
    gcongr
  have hsub : Bad⊆High∪Low := by
    intro i hi
    obtain ⟨hiS,hbad⟩ := Finset.mem_filter.mp hi
    rcases not_and_or.mp hbad with hlarge | hsmall
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨hiS,?_⟩
      have hh : Q/Acut < (anchor i).den :=
        (Nat.div_lt_iff_lt_mul hApos).mpr (by simpa only [mul_comm] using lt_of_not_ge hlarge)
      exact Nat.succ_le_of_lt hh
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hiS,lt_of_not_ge hsmall⟩)
  have hcard : (Bad.card:ℝ) ≤ Cost := by
    have hh : (Bad.card:ℝ) ≤ (High.card:ℝ)+(Low.card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    exact hh.trans (add_le_add hhigh hlow)
  refine ⟨hcard,?_⟩
  intro H hH
  calc
    (∑ i∈Bad,(H i:ℝ)) ≤ ∑ _i∈Bad,(N:ℝ) := Finset.sum_le_sum (fun i hi =>
      Nat.cast_le.mpr (hH i (Finset.mem_filter.mp hi).1))
    _ = (N:ℝ)*(Bad.card:ℝ) := by simp only [Finset.sum_const,nsmul_eq_mul,mul_comm]
    _ ≤ (N:ℝ)*Cost := mul_le_mul_of_nonneg_left hcard hNp.le




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

private theorem huxley_anchor_complement_source_scale
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

/-- The original interior-gap Fourier witnesses now carry a derived,
explicit bound for the entire rejected-anchor contribution. The source
sum, rational roots and single common Fourier mode are unchanged. -/
theorem positive_difference_interior_gap_controlled_complement_fourier
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (F : ℝ → ℝ) (N : ℕ) (s : ℤ) (H : ℤ → ℕ)
      (η y T M R U x₁ x₂ : ℝ),
      1 ≤ N → (∀ k, H k ≤ N) →
      0 < η → η ≤ 1/8 → y∈Icc (1:ℝ) 2 → 0 < T → 0 < M → 0 < R → 0 < U →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 → 7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      3*J ≤ σ*U → x₁∈Icc M (2*M) → x₂∈Icc M (2*M) →
      let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun w => iteratedDeriv 2 f w/2
      let t := fun k : ℤ => (s:ℝ)+(N:ℝ)*k
      let L := fun k : ℤ => s+(N:ℤ)*k+2*(N:ℤ)
      let delta := c/(64*σ*R^2)
      let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
      U/(4*R^2) ≤ h x₂-h x₁ → h x₂-h x₁ ≤ 7*U/(2*R^2) →
      ∃ S : Finset ℤ, ∃ (anchor : ℤ → ℚ) (za : ℤ → ℝ),
        (∀ k : ℤ, k∈S ↔ x₁+(N:ℝ)/4 ≤ t k ∧ t k ≤ x₂-(N:ℝ)/4) ∧
        (∀ k∈S, za k∈Ioo x₁ x₂ ∧ h (za k)=(anchor k:ℝ) ∧
          (anchor k:ℝ)∈Ioo (h x₁) (h x₂) ∧
          (anchor k:ℝ)∈Ioo (h (t k)-delta) (h (t k)+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo (h (t k)-delta) (h (t k)+delta) → (anchor k).den ≤ a.den) ∧
        (∀ k∈S, |za k-t k| ≤ (N:ℝ)/16) ∧
        (σ/(6*J))*U-3/2 ≤ (S.card:ℝ) ∧ (S.card:ℝ) ≤ (56*σ/c)*U+1/2 ∧
        (∀ Q : ℕ, 2 ≤ Q →
          let D := 64*σ*R^2/(c*(Q:ℝ))
          ((S.filter (fun k => Q ≤ (anchor k).den)).card:ℝ) ≤
            4*(Vbound+1)*D^2+D*(2+Real.log (D+1))) ∧
      ∀ Q : ℕ, 2 ≤ Q → Q ≤ N →
      let Good := fun i => 2*(anchor i).den ≤ Q ∧
        128*σ*R^2 ≤ c*(Q:ℝ)*(anchor i).den
      let G := S.filter Good
      let Dlow := 128*σ*R^2/(c*(Q:ℝ))
      let Khigh := Q/2+1
      let Dhigh := 64*σ*R^2/(c*(Khigh:ℝ))
      let Cost := 4*Vbound*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1))+
        Dlow*(2*(Vbound+delta)*Dlow+1)
      ((S.filter (fun i => ¬ Good i)).card:ℝ) ≤ Cost ∧
      ∃ (r : ℤ → ℚ) (z : ℤ → ℝ),
      (∀ i∈G, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i:ℝ) < r i ∧ |(r i:ℝ)-(anchor i:ℝ)| ≤ c/(64*σ*R^2) ∧
        z i∈Icc (za i) (za i+(N:ℝ)/16) ∧
        iteratedDeriv 2 f (z i)/2=(r i:ℝ)) ∧
      (∀ i∈G, z i∈Ioo x₁ x₂) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 f (m i)/6
      let ℓ := fun i => deriv f (m i)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      (∀ i∈G, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : ℤ → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
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
      (∑ i∈S, ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f n):ℂ)‖) ≤ C*((N:ℝ)*Cost+FourierCost) ∧
      (2*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
        (∑ i∈S, ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f n):ℂ)‖) ≤
          C*(Cerror*(M*R/Q)*(2+Real.log (Dlow+1))+FourierCost)) := by
  classical
  obtain ⟨C,hC,hentry⟩ := positive_difference_interior_gap_dyadic_source_fourier hσ hc hJ
  refine ⟨C,hC,?_⟩
  intro F N s H η y T M R U x₁ x₂ hN hH hη hηmax hy hT hM hR hU
    hf hbound htests hnegative hphase hbuffer hfourBudget hquadBudget hUlarge hx₁ hx₂
    f h t L delta Vbound hgaplow hgapup
  obtain ⟨S,anchor,za,hmem,hdata,hdist,hcardlow,hcardup,htail,hfourier⟩ :=
    hentry F N s H η y T M R U x₁ x₂ hN hH hη hηmax hy hT hM hR hU
      hf hbound hnegative hphase hbuffer hfourBudget hquadBudget hUlarge hx₁ hx₂
      hgaplow hgapup
  refine ⟨S,anchor,za,hmem,hdata,hdist,hcardlow,hcardup,htail,?_⟩
  intro Q hQ hQN Good G Dlow Khigh Dhigh Cost
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpoints i (hi : i∈S) : t i∈Icc M (2*M) := by
    have hh := (hmem i).mp hi
    constructor <;> linarith only [hh.1,hh.2,hx₁.1,hx₂.2,hNp]
  have hanchors i (hi : i∈S) := (hdata i hi).2.2.2
  have hb := positive_difference_minimal_anchor_complement_count S F anchor N (s:ℝ)
    hσ hc hJ hη hηmax hy hf hbound htests hnegative hT hM
    (show 0 < N by omega) hR hphase hpoints hanchors
    Q 2 (128*σ) (by norm_num) hQ (by positivity)
  obtain ⟨r,z,hr,hzg,hcenter,hcompletion⟩ := hfourier Q hQN
  refine ⟨hb.1,r,z,hr,hzg,hcenter,?_⟩
  dsimp only
  intro K₀ _ hK₀
  obtain ⟨v,hv,k,hfour⟩ := hcompletion K₀ hK₀
  refine ⟨v,hv,k,?_⟩
  let m := fun i => round (z i)
  let A := fun i => (L i-m i).toNat
  let q := fun i => (r i).den
  let μ := fun i => iteratedDeriv 3 f (m i)/6
  let ℓ := fun i => deriv f (m i)
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
  have hbase : (∑ i∈S, ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f n):ℂ)‖) ≤ C*((N:ℝ)*Cost+FourierCost) := by
    apply hfour.trans
    have hweight := hb.2 H (fun i _ => hH i)
    dsimp only [FourierCost]
    rw [←add_assoc ((N:ℝ)*Cost)]
    gcongr
  refine ⟨hbase,?_⟩
  intro hRQ hNR
  have hh := huxley_anchor_complement_source_scale Q 2
    hσ hc hJ hM hNp hR (by norm_num) hQ (show 0 ≤ 128*σ by positivity)
    (by simpa only [Nat.cast_ofNat] using hRQ) hNR
  have hDupper : 64*σ*R^2/(c*((Q:ℝ)/2))=Dlow := by dsimp only [Dlow]; ring
  have hcost : Cost ≤ Cerror*(M*R/((N:ℝ)*Q))*(2+Real.log (Dlow+1)) := by
    simpa only [Nat.cast_ofNat,hDupper] using hh
  have hscaled : (N:ℝ)*Cost ≤ Cerror*(M*R/Q)*(2+Real.log (Dlow+1)) := by
    have hh := mul_le_mul_of_nonneg_left hcost hNp.le
    convert hh using 1
    field_simp
  apply hbase.trans
  apply mul_le_mul_of_nonneg_left _ (by linarith only [hC])
  exact add_le_add hscaled (le_refl FourierCost)

example
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (k : ι → ℤ)
    (v : ι → ℝ) (r : ι → ℚ) (B : ℕ) {eta delta Vcurv : ℝ}
    (heta : 0 < eta) (hdelta : 0 < delta) (hX : 0 ≤ Vcurv)
    (hwidth : 4*delta ≤ eta)
    (hmul : ∀ n : ℤ, (S.filter (fun i => k i=n)).card ≤ B)
    (hsep : ∀ i∈S, ∀ j∈S, eta*|(k i:ℝ)-k j| ≤ |v i-v j|)
    (hv : ∀ i∈S, |v i| ≤ Vcurv)
    (hminimal : ∀ i∈S, ∀ a : ℚ,
      (a:ℝ)∈Ioo (v i-delta) (v i+delta) → (r i).den ≤ a.den) :
    ∀ Q : ℕ, 2 ≤ Q →
      let D := 1/(delta*(Q:ℝ))
      ((S.filter (fun i => Q ≤ (r i).den)).card:ℝ) ≤
        B*(4*Vcurv*D^2+3*D*(2+Real.log (D+1))) :=
  HuxleySharpAnchorTailScratch.bourgain_actual_minimal_arc_sharp_tail (ι:=ι) S k v r B (eta:=eta) (delta:=delta) (Vcurv:=Vcurv) heta hdelta hX hwidth hmul hsep hv hminimal

example
    (S : Finset ℤ) (F : ℝ → ℝ) (anchor : ℤ → ℚ)
    (N : ℕ) (s : ℝ) {σ c J η y T M R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hphase : T*(N:ℝ)*R^2=M^3)
    (hpoints : ∀ i∈S, s+(N:ℝ)*i∈Icc M (2*M)) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun w => iteratedDeriv 2 f w/2
    let t := fun i : ℤ => s+(N:ℝ)*i
    let delta := c/(64*σ*R^2)
    let Vcurv := 3*J*M/(2*σ*(N:ℝ)*R^2)
    let C := (6*J/σ)*(64*σ/c)^2+192*σ/c
    (∀ i∈S, ∀ a : ℚ, (a:ℝ)∈Ioo (h (t i)-delta) (h (t i)+delta) →
      (anchor i).den ≤ a.den) →
    ∀ Q : ℕ, 2 ≤ Q →
      let High := S.filter (fun i => Q ≤ (anchor i).den)
      let D := 64*σ*R^2/(c*(Q:ℝ))
      (High.card:ℝ) ≤ 4*Vcurv*D^2+3*D*(2+Real.log (D+1)) ∧
      ((R ≤ (Q:ℝ)) → (N:ℝ)*R ≤ M →
        (High.card:ℝ) ≤ C*(M*R/((N:ℝ)*Q))*(2+Real.log (D+1)) ∧
        ∀ (L : ℤ → ℤ) (H : ℤ → ℕ), (∀ i∈S, H i ≤ N) →
          (∑ i∈High, ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f n):ℂ)‖) ≤
            C*(M*R/Q)*(2+Real.log (D+1))) :=
  HuxleySharpAnchorTailScratch.positive_difference_actual_minimal_anchor_sharp_tail S F anchor N s (σ:=σ) (c:=c) (J:=J) (η:=η) (y:=y) (T:=T) (M:=M) (R:=R) hσ hc hJ hη hηmax hy hf hbound htests hnegative hT hM hN hR hphase hpoints

example
    (S : Finset ℤ) (F : ℝ → ℝ) (anchor : ℤ → ℚ)
    (N : ℕ) (s : ℝ) {σ c J η y T M R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hphase : T*(N:ℝ)*R^2=M^3)
    (hpoints : ∀ i∈S, s+(N:ℝ)*i∈Icc M (2*M)) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun w => iteratedDeriv 2 f w/2
    let t := fun i : ℤ => s+(N:ℝ)*i
    let delta := c/(64*σ*R^2)
    let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
    (∀ i∈S, (anchor i:ℝ)∈Ioo (h (t i)-delta) (h (t i)+delta) ∧
      ∀ a : ℚ, (a:ℝ)∈Ioo (h (t i)-delta) (h (t i)+delta) → (anchor i).den ≤ a.den) →
    ∀ (Q Acut : ℕ) (Bmajor : ℝ), 2 ≤ Acut → Acut ≤ Q → 0 ≤ Bmajor →
    let Bad := S.filter (fun i => ¬ (Acut*(anchor i).den ≤ Q ∧
      Bmajor*R^2 ≤ c*(Q:ℝ)*(anchor i).den))
    let Dlow := Bmajor*R^2/(c*(Q:ℝ))
    let Khigh := Q/Acut+1
    let Dhigh := 64*σ*R^2/(c*(Khigh:ℝ))
    let Cost := 4*Vbound*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1))+
      Dlow*(2*(Vbound+delta)*Dlow+1)
    (Bad.card:ℝ) ≤ Cost ∧
      ∀ H : ℤ → ℕ, (∀ i∈S, H i ≤ N) →
        (∑ i∈Bad,(H i:ℝ)) ≤ (N:ℝ)*Cost :=
  HuxleySharpAnchorTailScratch.positive_difference_minimal_anchor_complement_count S F anchor N s (σ:=σ) (c:=c) (J:=J) (η:=η) (y:=y) (T:=T) (M:=M) (R:=R) hσ hc hJ hη hηmax hy hf hbound htests hnegative hT hM hN hR hphase hpoints

example
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (F : ℝ → ℝ) (N : ℕ) (s : ℤ) (H : ℤ → ℕ)
      (η y T M R U x₁ x₂ : ℝ),
      1 ≤ N → (∀ k, H k ≤ N) →
      0 < η → η ≤ 1/8 → y∈Icc (1:ℝ) 2 → 0 < T → 0 < M → 0 < R → 0 < U →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 → 7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      3*J ≤ σ*U → x₁∈Icc M (2*M) → x₂∈Icc M (2*M) →
      let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun w => iteratedDeriv 2 f w/2
      let t := fun k : ℤ => (s:ℝ)+(N:ℝ)*k
      let L := fun k : ℤ => s+(N:ℤ)*k+2*(N:ℤ)
      let delta := c/(64*σ*R^2)
      let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
      U/(4*R^2) ≤ h x₂-h x₁ → h x₂-h x₁ ≤ 7*U/(2*R^2) →
      ∃ S : Finset ℤ, ∃ (anchor : ℤ → ℚ) (za : ℤ → ℝ),
        (∀ k : ℤ, k∈S ↔ x₁+(N:ℝ)/4 ≤ t k ∧ t k ≤ x₂-(N:ℝ)/4) ∧
        (∀ k∈S, za k∈Ioo x₁ x₂ ∧ h (za k)=(anchor k:ℝ) ∧
          (anchor k:ℝ)∈Ioo (h x₁) (h x₂) ∧
          (anchor k:ℝ)∈Ioo (h (t k)-delta) (h (t k)+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo (h (t k)-delta) (h (t k)+delta) → (anchor k).den ≤ a.den) ∧
        (∀ k∈S, |za k-t k| ≤ (N:ℝ)/16) ∧
        (σ/(6*J))*U-3/2 ≤ (S.card:ℝ) ∧ (S.card:ℝ) ≤ (56*σ/c)*U+1/2 ∧
        (∀ Q : ℕ, 2 ≤ Q →
          let D := 64*σ*R^2/(c*(Q:ℝ))
          ((S.filter (fun k => Q ≤ (anchor k).den)).card:ℝ) ≤
            4*(Vbound+1)*D^2+D*(2+Real.log (D+1))) ∧
      ∀ Q : ℕ, 2 ≤ Q → Q ≤ N →
      let Good := fun i => 2*(anchor i).den ≤ Q ∧
        128*σ*R^2 ≤ c*(Q:ℝ)*(anchor i).den
      let G := S.filter Good
      let Dlow := 128*σ*R^2/(c*(Q:ℝ))
      let Khigh := Q/2+1
      let Dhigh := 64*σ*R^2/(c*(Khigh:ℝ))
      let Cost := 4*Vbound*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1))+
        Dlow*(2*(Vbound+delta)*Dlow+1)
      ((S.filter (fun i => ¬ Good i)).card:ℝ) ≤ Cost ∧
      ∃ (r : ℤ → ℚ) (z : ℤ → ℝ),
      (∀ i∈G, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i:ℝ) < r i ∧ |(r i:ℝ)-(anchor i:ℝ)| ≤ c/(64*σ*R^2) ∧
        z i∈Icc (za i) (za i+(N:ℝ)/16) ∧
        iteratedDeriv 2 f (z i)/2=(r i:ℝ)) ∧
      (∀ i∈G, z i∈Ioo x₁ x₂) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 f (m i)/6
      let ℓ := fun i => deriv f (m i)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      (∀ i∈G, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : ℤ → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
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
      (∑ i∈S, ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f n):ℂ)‖) ≤ C*((N:ℝ)*Cost+FourierCost) ∧
      (2*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
        (∑ i∈S, ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f n):ℂ)‖) ≤
          C*(Cerror*(M*R/Q)*(2+Real.log (Dlow+1))+FourierCost)) :=
  HuxleySharpAnchorTailScratch.positive_difference_interior_gap_controlled_complement_fourier (σ:=σ) (c:=c) (J:=J) hσ hc hJ

#print axioms huxley_anchor_complement_source_scale
#print axioms huxley_low_anchor_source_scale
#print axioms positive_difference_minimal_anchor_complement_count
#print axioms positive_difference_interior_gap_controlled_complement_fourier
#print axioms positive_difference_actual_minimal_anchor_sharp_tail
#print axioms huxley_sharp_tail_source_scale
#print axioms bourgain_actual_minimal_arc_sharp_tail
#print axioms bourgain_rational_neighborhood_block_count
#print axioms bourgain_rational_neighborhood_block_count_sharp

end HuxleySharpAnchorTailScratch
