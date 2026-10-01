import TaoTrudgianYang2025.HuxleyLinearForms

open Set MeasureTheory Filter Asymptotics
open scoped BigOperators Topology
open TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase

namespace HuxleyChartedMassScratch

private theorem physical_source_quartic_constants_nonneg
    {σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 ≤ δ) :
    0 ≤ quarticReciprocalConstant σ δ ∧ 0 ≤ quarticNonlinearResidualConstant σ δ := by
  have hκ := modelPhaseThirdLower_pos hσ
  have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ
  have hC₄ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδ
  constructor
  · dsimp only [quarticReciprocalConstant]
    positivity
  · dsimp only [quarticNonlinearResidualConstant]
    positivity

private theorem reciprocal_square_prefix (J : ℕ) :
    (∑ m∈Finset.range J, 1/((m:ℝ)+1)^2) ≤ 2-2/((J:ℝ)+1) := by
  induction J with
  | zero => norm_num
  | succ J ih =>
    rw [Finset.sum_range_succ,Nat.cast_add,Nat.cast_one]
    have hJ : (0:ℝ) ≤ J := Nat.cast_nonneg J
    have hstep : 1/((J:ℝ)+1)^2 ≤ 2/((J:ℝ)+1)-2/((J:ℝ)+1+1) := by
      have h₁ : (J:ℝ)+1 ≠ 0 := by positivity
      have h₂ : (J:ℝ)+1+1 ≠ 0 := by positivity
      have he : 2/((J:ℝ)+1)-2/((J:ℝ)+1+1)=2/(((J:ℝ)+1)*((J:ℝ)+1+1)) := by
        field_simp
        ring
      rw [he]
      apply (div_le_div_iff₀ (by positivity : 0 < ((J:ℝ)+1)^2)
        (by positivity : 0 < ((J:ℝ)+1)*((J:ℝ)+1+1))).mpr
      nlinarith
    linarith only [ih,hstep]

private theorem finite_occupied_tail_sum
    {ι : Type*} (S : Finset ι) (n : ι → ℕ) (J : ℕ)
    {A B : ℝ} (hB : 0 ≤ B) (hcap : ∀ i∈S, n i ≤ J)
    (htail : ∀ m∈Finset.range J,
      ((S.filter (fun i => m < n i)).card:ℝ) ≤ A+B/((m:ℝ)+1)^2) :
    (∑ i∈S, (n i:ℝ)) ≤ A*(J:ℝ)+2*B := by
  classical
  have hrepr :
      (∑ m∈Finset.range J, ((S.filter (fun i => m < n i)).card:ℝ)) =
        ∑ i∈S, (n i:ℝ) := by
    calc
      _ = ∑ m∈Finset.range J, ∑ i∈S, if m < n i then (1:ℝ) else 0 := by
        simp
      _ = ∑ i∈S, ∑ m∈Finset.range J, if m < n i then (1:ℝ) else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        have hfilter : (Finset.range J).filter (fun m => m < n i)=Finset.range (n i) := by
          ext m
          simp only [Finset.mem_filter,Finset.mem_range]
          have hiCap := hcap i hi
          omega
        rw [← Finset.sum_filter,hfilter]
        simp
  rw [← hrepr]
  calc
    _ ≤ ∑ m∈Finset.range J, (A+B/((m:ℝ)+1)^2) := Finset.sum_le_sum htail
    _ = A*(J:ℝ)+B*(∑ m∈Finset.range J,1/((m:ℝ)+1)^2) := by
      simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,
        nsmul_eq_mul,div_eq_mul_inv,one_mul,Finset.mul_sum]
      ring
    _ ≤ A*(J:ℝ)+2*B := by
      have hh : (∑ m∈Finset.range J,1/((m:ℝ)+1)^2) ≤ 2 :=
        (reciprocal_square_prefix J).trans (sub_le_self _ (by positivity))
      nlinarith only [mul_le_mul_of_nonneg_left hh hB]

private theorem finite_occupied_cubic_tail_sum
    {ι : Type*} (S : Finset ι) (n : ι → ℕ)
    {A B K c : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K) (hc : 0 < c)
    (hcap : ∀ i∈S, (n i:ℝ)^3*c ≤ K)
    (htail : ∀ m : ℕ, 0 < m →
      ((S.filter (fun i => m ≤ n i)).card:ℝ) ≤ A+B/(m:ℝ)^2) :
    (∑ i∈S, (n i:ℝ)) ≤ A*(K/c)^((3:ℝ)⁻¹)+2*B := by
  classical
  let J := S.sup n
  let root := (K/c)^((3:ℝ)⁻¹)
  have hroot : 0 ≤ root := Real.rpow_nonneg (div_nonneg hK hc.le) _
  have hrootcube : root^3=K/c :=
    Real.rpow_inv_natCast_pow (div_nonneg hK hc.le) (by norm_num : (3:ℕ) ≠ 0)
  have hJcube : (J:ℝ)^3 ≤ K/c := by
    by_cases hs : S.Nonempty
    · obtain ⟨i,hi,he⟩ := Finset.sup_mem_of_nonempty (f:=n) hs
      change n i=J at he
      rw [← he]
      exact (le_div_iff₀ hc).mpr (hcap i hi)
    · have hJzero : J=0 := by simp [J,Finset.not_nonempty_iff_eq_empty.mp hs]
      rw [hJzero]
      simpa using div_nonneg hK hc.le
  have hJ : (J:ℝ) ≤ root := (pow_le_pow_iff_left₀ (Nat.cast_nonneg J)
    hroot (by decide : (3:ℕ) ≠ 0)).mp (by rw [hrootcube]; exact hJcube)
  have hh := finite_occupied_tail_sum S n J hB (fun i hi => Finset.le_sup hi)
    (fun m _ => by
      simpa only [Nat.lt_iff_add_one_le,Nat.cast_add,Nat.cast_one] using htail (m+1) (by omega))
  exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left hJ hA) le_rfl)


private theorem quotient_block_mass (a b : ℕ) (hb : 0 < b) (hba : b ≤ a) :
    0 < a/b ∧ b*(a/b) ≤ a ∧ a ≤ 2*b*(a/b) := by
  have hpos := Nat.div_pos hba hb
  have hrem := Nat.mod_lt a hb
  have he := Nat.div_add_mod a b
  have hmul : b ≤ b*(a/b) := Nat.le_mul_of_pos_right b hpos
  refine ⟨hpos,Nat.mul_div_le a b,?_⟩
  nlinarith only [hrem,he,hmul]

private theorem two_term_first_cubic_cap
    {C A B N scale length n : ℝ}
    (hC : 0 ≤ C) (hN : 0 < N) (hs : 0 < scale)
    (hl : 0 < length) (hn : 0 ≤ n) (hshort : scale*n ≤ length)
    (hfirst : C ≤ A/(length^3*N^2)+B) (hsmall : 2*B ≤ C) :
    n^3*C ≤ 2*A/(scale^3*N^2) := by
  have hden : 0 < length^3*N^2 := by positivity
  have hhalf : C/2 ≤ A/(length^3*N^2) := by linarith only [hfirst,hsmall]
  have hm := (le_div_iff₀ hden).mp hhalf
  have hp := pow_le_pow_left₀ (mul_nonneg hs.le hn) hshort 3
  have hh := mul_le_mul_of_nonneg_right hp (mul_nonneg (sq_nonneg N) hC)
  apply (le_div_iff₀ (by positivity : 0 < scale^3*N^2)).mpr
  nlinarith only [hm,hh]



theorem physicalModelPhase_actual_fourier_charted_reference_sample_mass
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (Bmajor Cmajor : ℕ)
    (S : ℝ × ℝ → Finset ℕ) (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℝ × ℝ → ℕ → Fin 2 → ℚ) (vinv : ℝ × ℝ → ℕ → Fin 2 → ℤ)
    (parity : ℝ × ℝ → ℕ → Fin 2 → Fin 2) (anchor : ℝ × ℝ → ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ℝ × ℝ → ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T)
    (hM : 0 < M)
    (hN : 0 < N)
    (hR : 1 ≤ R)
    (hRM : R ≤ M)
    (hQ : 0 < Q)
    (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i)
    (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ ab∈Gaps, ∀ j∈(S ab), (x ab) j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hden : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, ((rat ab) j i).den ≤ Q ∧ Q ≤ 2*((rat ab) j i).den)
    (hlambda : 0 < lambda)
    (hUband : 0 ≤ Uband)
    (hθ : 0 < θ)
    (hθmax : θ ≤ 1/24)
    (hcurv : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, lambda ≤ |((rat ab) j i:ℝ)| ∧ |((rat ab) j i:ℝ)| ≤ Uband)
    (hinv : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (((rat ab) j i).den:ℤ) ∣ ((rat ab) j i).num*(vinv ab) j i-1)
    (hchart : ∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1)
    (horientation : ∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2))
    (hBcut : 0 < Bcut)
    (hs : ∀ ab∈Gaps, (s ab) ≠ 0)
    (hrefSet : ∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs)
    (hparentSet : ∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|)
    (hwideL : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hUref : 1 ≤ Uref)
    (hBselectSize : 2+168/modelPhaseThirdLower σ ≤ Bselect)
    (hcutMargin : 7*Bcut ≤ modelPhaseThirdLower σ*Bselect)
    (hselectedWrap : Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2)
    (hreferenceDen : ∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ))
    (hgapWidth : ∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2))
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : N^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ ab∈Gaps, ∀ j∈(S ab), ((rat ab) j 0:ℝ)∈Icc ab.1 ab.2)
    (hc : Mat 2 ≠ 0)
    (hlarge : 64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (ab : ℝ × ℝ) => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (ab : ℝ × ℝ) => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun (ab : ℝ × ℝ) => fun j i => (⌊(((rat ab) j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊(((rat ab) j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ab∈Gaps, ∀ j∈(S ab), (sourceColor ab) j 0=(sourceColor ab) j 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, iteratedDeriv 2 (f i) ((x ab) j i)/2=((rat ab) j i:ℝ)) →
    let q := fun (ab : ℝ × ℝ) => fun j i => ((rat ab) j i).den
    let mu := fun (ab : ℝ × ℝ) => fun j i => iteratedDeriv 3 (f i) (round ((x ab) j i))/6
    let ell := fun (ab : ℝ × ℝ) => fun j i => deriv (f i) (round ((x ab) j i))
    let b := fun (ab : ℝ × ℝ) => fun j i => (⌊((q ab) j i:ℝ)*(ell ab) j i⌋+((parity ab) j i:ℕ) : ℤ)
    let cround := fun (ab : ℝ × ℝ) => fun j i => round (((q ab) j i:ℝ)*(ell ab) j i)
    let tau := fun (ab : ℝ × ℝ) => fun j i => (((b ab) j i:ℝ)-((q ab) j i:ℝ)*(ell ab) j i)/2
    let dual := fun (ab : ℝ × ℝ) => fun j i => -2*(mu ab) j i*(Real.sqrt (2/(3*(mu ab) j i*((q ab) j i:ℝ))))^3
    let cloud := fun (ab : ℝ × ℝ) => fun j i => (![Int.fract (-((vinv ab) j i:ℝ)*(b ab) j i/(q ab) j i),
      Int.fract (-((vinv ab) j i:ℝ)/(q ab) j i),(dual ab) j i/Real.sqrt K₀,
      (3*(dual ab) j i*(tau ab) j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ab∈Gaps, ∀ j∈(S ab), (b ab) j 0-(cround ab) j 0=(b ab) j 1-(cround ab) j 1) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ a, |(cloud ab) j 0 a-(cloud ab) j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 →
    N ≤ R^2 →
    R ≤ N →
    N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (∀ ab∈Gaps, ∀ j∈(S ab), (Mat 2:ℝ)*((rat ab) j 0:ℝ)+Mat 3=((q ab) j 1:ℝ)/(q ab) j 0) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ((Mat 0:ℝ)*((rat ab) j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*((rat ab) j 0:ℝ)+Mat 3)=((rat ab) j 1:ℝ)) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), |((anchor ab) j:ℝ)-((rat ab) j 0:ℝ)| ≤ ε) →
    (∀ ab∈Gaps, ∀ j∈(S ab), 256*(((anchor ab) j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ab∈Gaps, ∀ j∈(S ab), 256 ≤ (2*ε)*((Q:ℝ)/3)*((anchor ab) j).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Blabels := fun ab => 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ ab∈Gaps, Blabels ab ≤ Bmajor) →
    (∀ ab∈Gaps, Ccharts ab ≤ Cmajor) →
    (∀ ab∈Gaps, m0 ≤ (S ab).card) →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    (∑ ab∈Gaps, ((S ab).card:ℝ)) ≤
      4*(m0:ℝ)*((2*Cfirst*R^4/(Lunit^3*N^2)/|(Mat 2:ℝ)|)^((3:ℝ)⁻¹)+
        Cpack*R^4/(Lunit^2*N^2*|(Mat 2:ℝ)| *(Uref:ℝ))) := by
  classical
  intro Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor f hlevel
    q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Blabels m0 hBmajor hCmajor hS Lunit Gamma Cthird Cpack Cfirst
  let Csecond := 32*(modelPhaseJetCoefficient σ 3+δ)/κ^2
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hunit : 0 < Lunit := div_pos (mul_pos (by norm_num) hκ) hCphys
  have hm0 : 0 < m0 := by dsimp only [m0]; omega
  have hUp : (0:ℝ) < Uref := by exact_mod_cast (show 0 < Uref by omega)
  have hδ0 := approximateModelPhase_tolerance_nonneg (hF 0)
  have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  obtain ⟨hCR,hCN⟩ := physical_source_quartic_constants_nonneg hσ hδ0
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hCt : 0 ≤ Ct := by dsimp only [Ct]; positivity
  have hCc : 0 ≤ Cc := by dsimp only [Cc]; positivity
  have hK : 0 ≤ Kres := by dsimp only [Kres]; positivity
  have hΓ : 0 ≤ Gamma := div_nonneg hCphys.le hκ.le
  have hCthird : 0 ≤ Cthird :=
    mul_nonneg hΓ (add_nonneg (mul_nonneg (by norm_num) hK)
      (mul_nonneg (by norm_num) hCR))
  have hcore : 0 ≤ Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ :=
    add_nonneg (mul_nonneg (sq_nonneg Gamma) hCthird)
      (div_nonneg (mul_nonneg hΓ hC₃) hκ.le)
  have hCpack : 0 ≤ Cpack :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCphys.le) hcore) hκ.le
  have hCfirst : 0 ≤ Cfirst :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCphys.le) hcore) (sq_nonneg κ)
  have hCmat : 0 < |(Mat 2:ℝ)| := abs_pos.mpr (by exact_mod_cast hc)
  have hlarge32 : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *κ^2*T := by
    have hn := mul_nonneg hC₃ (sq_nonneg M)
    nlinarith only [hlarge,hn]
  have habsorb : 2*(Csecond*N*R^2/M) ≤ |(Mat 2:ℝ)| := by
    have hs : 64*(modelPhaseJetCoefficient σ 3+δ)*N*R^2 ≤ |(Mat 2:ℝ)| *κ^2*M := by
      apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hM)).mp
      calc
        _ = (64*(modelPhaseJetCoefficient σ 3+δ)*M^2)*(N*R^2) := by ring
        _ ≤ (|(Mat 2:ℝ)| *κ^2*T)*(N*R^2) :=
          mul_le_mul_of_nonneg_right hlarge (by positivity)
        _ = (|(Mat 2:ℝ)| *κ^2)*(T*N*R^2) := by ring
        _ = _ := by rw [hscale]; ring
    calc
      _ = (64*(modelPhaseJetCoefficient σ 3+δ)*N*R^2)/(κ^2*M) := by
        dsimp only [Csecond]
        ring
      _ ≤ _ := (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hs])
  let n := fun ab => (S ab).card/m0
  have hn ab (hab : ab∈Gaps) := quotient_block_mass (S ab).card m0 hm0 (hS ab hab)
  have hfamily (G : Finset (ℝ × ℝ)) (hsub : G ⊆ Gaps) (m : ℕ) (hm : 0 < m)
      (hblocks : ∀ ab∈G, m0*m ≤ (S ab).card) :
      (G.Nonempty → |(Mat 2:ℝ)| ≤
        Cfirst*R^4/((Lunit*(m:ℝ))^3*N^2)+Csecond*N*R^2/M) ∧
      (G.card:ℝ) ≤ Cpack*R^4/((Lunit*(m:ℝ))^2*N^2*|(Mat 2:ℝ)| *(Uref:ℝ))+2 := by
    exact physicalModelPhase_actual_fourier_charted_long_gap_packing
      Uref Refs G (Bselect:=Bselect) Bmajor Cmajor m hm
      S Q K₀ rat vinv parity anchor Mat e r v s
      hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW (fun ab hab => hx ab (hsub hab)) (fun ab hab => hwindow ab (hsub hab)) (fun ab hab => hden ab (hsub hab)) hlambda hUband hθ hθmax (fun ab hab => hcurv ab (hsub hab)) (fun ab hab => hinv ab (hsub hab)) (fun ab hab => hchart ab (hsub hab)) (fun ab hab => horientation ab (hsub hab)) hBcut (fun ab hab => hs ab (hsub hab)) (fun ab hab => hrefSet ab (hsub hab)) (fun ab hab => hparentSet ab (hsub hab)) hsep (fun ab hab => hwideL ab (hsub hab)) (fun ab hab => hwideU ab (hsub hab)) hUref hBselectSize hcutMargin hselectedWrap (fun ab hab => hreferenceDen ab (hsub hab)) (fun ab hab => hgapWidth ab (hsub hab)) hRQ hselectedUpper hscaleTen (fun ab hab => hfamilyGap ab (hsub hab))
      hc hlarge32 (fun ab hab => hgap ab (hsub hab))
      (fun ab hab => hsourceColor ab (hsub hab)) (fun ab hab => hlevel ab (hsub hab)) (fun ab hab => hcolor ab (hsub hab)) (fun ab hab => hnear ab (hsub hab)) hsmall hNR hRN hNcube hminscale hMatdet (fun ab hab => hMatt ab (hsub hab)) (fun ab hab => hMatmap ab (hsub hab)) hMatgamma hNtwo (fun ab hab => hL ab (hsub hab)) (fun ab hab => hU ab (hsub hab)) (fun ab hab => hanchor ab (hsub hab)) (fun ab hab => hcut ab (hsub hab)) (fun ab hab => hcount ab (hsub hab))
      hsize hD hΔ hBsize
      (fun ab hab => hBmajor ab (hsub hab))
      (fun ab hab => hCmajor ab (hsub hab)) hblocks
  have hfirst ab (hab : ab∈Gaps) :
      |(Mat 2:ℝ)| ≤ Cfirst*R^4/((Lunit*(n ab:ℝ))^3*N^2)+Csecond*N*R^2/M := by
    have hs : ({ab} : Finset (ℝ × ℝ)) ⊆ Gaps := Finset.singleton_subset_iff.mpr hab
    have hb : ∀ t∈({ab} : Finset (ℝ × ℝ)), m0*n ab ≤ (S t).card := by
      intro t ht
      have he : t=ab := Finset.mem_singleton.mp ht
      subst t
      exact (hn ab hab).2.1
    exact (hfamily {ab} hs (n ab) (hn ab hab).1 hb).1 (Finset.singleton_nonempty ab)
  have hcap ab (hab : ab∈Gaps) :
      (n ab:ℝ)^3*|(Mat 2:ℝ)| ≤ 2*(Cfirst*R^4)/(Lunit^3*N^2) :=
    two_term_first_cubic_cap hCmat.le hN hunit
      (mul_pos hunit (by exact_mod_cast (hn ab hab).1))
      (Nat.cast_nonneg _) le_rfl (hfirst ab hab) habsorb
  let Cost := Cpack*R^4/(Lunit^2*N^2*|(Mat 2:ℝ)| *(Uref:ℝ))
  have htail (m : ℕ) (hm : 0 < m) :
      ((Gaps.filter (fun ab => m ≤ n ab)).card:ℝ) ≤ 2+Cost/(m:ℝ)^2 := by
    let Long := Gaps.filter (fun ab => m ≤ n ab)
    have hin : Long ⊆ Gaps := Finset.filter_subset _ _
    have hb ab (hab : ab∈Long) : m0*m ≤ (S ab).card :=
      (Nat.mul_le_mul_left m0 (Finset.mem_filter.mp hab).2).trans (hn ab (hin hab)).2.1
    exact (hfamily Long hin m hm hb).2.trans_eq (by dsimp only [Cost]; ring)
  have hsum := finite_occupied_cubic_tail_sum Gaps n (by norm_num : (0:ℝ) ≤ 2)
    (show 0 ≤ Cost by dsimp only [Cost]; positivity)
    (show 0 ≤ 2*(Cfirst*R^4)/(Lunit^3*N^2) by positivity) hCmat hcap htail
  have hmass : (∑ ab∈Gaps, ((S ab).card:ℝ)) ≤ 2*(m0:ℝ)*(∑ ab∈Gaps, (n ab:ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ab hab
    exact_mod_cast (hn ab hab).2.2
  calc
    _ ≤ 2*(m0:ℝ)*(∑ ab∈Gaps, (n ab:ℝ)) := hmass
    _ ≤ 2*(m0:ℝ)*(2*(2*(Cfirst*R^4)/(Lunit^3*N^2)/|(Mat 2:ℝ)|)^((3:ℝ)⁻¹)+2*Cost) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by dsimp only [Cost]; ring_nf


example
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (Bmajor Cmajor : ℕ)
    (S : ℝ × ℝ → Finset ℕ) (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℝ × ℝ → ℕ → Fin 2 → ℚ) (vinv : ℝ × ℝ → ℕ → Fin 2 → ℤ)
    (parity : ℝ × ℝ → ℕ → Fin 2 → Fin 2) (anchor : ℝ × ℝ → ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ℝ × ℝ → ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T)
    (hM : 0 < M)
    (hN : 0 < N)
    (hR : 1 ≤ R)
    (hRM : R ≤ M)
    (hQ : 0 < Q)
    (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i)
    (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ ab∈Gaps, ∀ j∈(S ab), (x ab) j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hden : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, ((rat ab) j i).den ≤ Q ∧ Q ≤ 2*((rat ab) j i).den)
    (hlambda : 0 < lambda)
    (hUband : 0 ≤ Uband)
    (hθ : 0 < θ)
    (hθmax : θ ≤ 1/24)
    (hcurv : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, lambda ≤ |((rat ab) j i:ℝ)| ∧ |((rat ab) j i:ℝ)| ≤ Uband)
    (hinv : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (((rat ab) j i).den:ℤ) ∣ ((rat ab) j i).num*(vinv ab) j i-1)
    (hchart : ∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1)
    (horientation : ∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2))
    (hBcut : 0 < Bcut)
    (hs : ∀ ab∈Gaps, (s ab) ≠ 0)
    (hrefSet : ∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs)
    (hparentSet : ∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|)
    (hwideL : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hUref : 1 ≤ Uref)
    (hBselectSize : 2+168/modelPhaseThirdLower σ ≤ Bselect)
    (hcutMargin : 7*Bcut ≤ modelPhaseThirdLower σ*Bselect)
    (hselectedWrap : Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2)
    (hreferenceDen : ∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ))
    (hgapWidth : ∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2))
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : N^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ ab∈Gaps, ∀ j∈(S ab), ((rat ab) j 0:ℝ)∈Icc ab.1 ab.2)
    (hc : Mat 2 ≠ 0)
    (hlarge : 64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (ab : ℝ × ℝ) => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (ab : ℝ × ℝ) => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun (ab : ℝ × ℝ) => fun j i => (⌊(((rat ab) j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊(((rat ab) j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ab∈Gaps, ∀ j∈(S ab), (sourceColor ab) j 0=(sourceColor ab) j 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, iteratedDeriv 2 (f i) ((x ab) j i)/2=((rat ab) j i:ℝ)) →
    let q := fun (ab : ℝ × ℝ) => fun j i => ((rat ab) j i).den
    let mu := fun (ab : ℝ × ℝ) => fun j i => iteratedDeriv 3 (f i) (round ((x ab) j i))/6
    let ell := fun (ab : ℝ × ℝ) => fun j i => deriv (f i) (round ((x ab) j i))
    let b := fun (ab : ℝ × ℝ) => fun j i => (⌊((q ab) j i:ℝ)*(ell ab) j i⌋+((parity ab) j i:ℕ) : ℤ)
    let cround := fun (ab : ℝ × ℝ) => fun j i => round (((q ab) j i:ℝ)*(ell ab) j i)
    let tau := fun (ab : ℝ × ℝ) => fun j i => (((b ab) j i:ℝ)-((q ab) j i:ℝ)*(ell ab) j i)/2
    let dual := fun (ab : ℝ × ℝ) => fun j i => -2*(mu ab) j i*(Real.sqrt (2/(3*(mu ab) j i*((q ab) j i:ℝ))))^3
    let cloud := fun (ab : ℝ × ℝ) => fun j i => (![Int.fract (-((vinv ab) j i:ℝ)*(b ab) j i/(q ab) j i),
      Int.fract (-((vinv ab) j i:ℝ)/(q ab) j i),(dual ab) j i/Real.sqrt K₀,
      (3*(dual ab) j i*(tau ab) j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ab∈Gaps, ∀ j∈(S ab), (b ab) j 0-(cround ab) j 0=(b ab) j 1-(cround ab) j 1) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ a, |(cloud ab) j 0 a-(cloud ab) j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 →
    N ≤ R^2 →
    R ≤ N →
    N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (∀ ab∈Gaps, ∀ j∈(S ab), (Mat 2:ℝ)*((rat ab) j 0:ℝ)+Mat 3=((q ab) j 1:ℝ)/(q ab) j 0) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ((Mat 0:ℝ)*((rat ab) j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*((rat ab) j 0:ℝ)+Mat 3)=((rat ab) j 1:ℝ)) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), |((anchor ab) j:ℝ)-((rat ab) j 0:ℝ)| ≤ ε) →
    (∀ ab∈Gaps, ∀ j∈(S ab), 256*(((anchor ab) j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ab∈Gaps, ∀ j∈(S ab), 256 ≤ (2*ε)*((Q:ℝ)/3)*((anchor ab) j).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Blabels := fun ab => 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ ab∈Gaps, Blabels ab ≤ Bmajor) →
    (∀ ab∈Gaps, Ccharts ab ≤ Cmajor) →
    (∀ ab∈Gaps, m0 ≤ (S ab).card) →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    (∑ ab∈Gaps, ((S ab).card:ℝ)) ≤
      4*(m0:ℝ)*((2*Cfirst*R^4/(Lunit^3*N^2)/|(Mat 2:ℝ)|)^((3:ℝ)⁻¹)+
        Cpack*R^4/(Lunit^2*N^2*|(Mat 2:ℝ)| *(Uref:ℝ))) :=
  HuxleyChartedMassScratch.physicalModelPhase_actual_fourier_charted_reference_sample_mass Uref Refs Gaps (Bselect:=Bselect) Bmajor Cmajor S Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (Bcut:=Bcut) (lambda:=lambda) (Uband:=Uband) (θ:=θ) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hc hlarge hgap



#print axioms reciprocal_square_prefix
#print axioms finite_occupied_tail_sum
#print axioms finite_occupied_cubic_tail_sum
#print axioms quotient_block_mass
#print axioms two_term_first_cubic_cap

private theorem adjacent_reference_gap_card_closed
    (S : Finset ℝ) (G : Finset (ℝ × ℝ)) {lo hi d : ℝ}
    (hd : 0 < d) (hlohi : lo ≤ hi)
    (hsep : ∀ x∈S, ∀ y∈S, x≠y → d ≤ |x-y|)
    (hgap : ∀ ab∈G, ab.1∈S ∧ ab.2∈S ∧ ab.1<ab.2 ∧
      ∀ t∈S, ¬(ab.1<t ∧ t<ab.2))
    (hmeet : ∀ ab∈G, ab.1 ≤ hi ∧ lo ≤ ab.2) :
    (G.card:ℝ) ≤ (hi-lo)/d+2 := by
  classical
  have hinj : Set.InjOn Prod.fst (G : Set (ℝ × ℝ)) := by
    intro ab hab cd hcd he
    apply Prod.ext he
    rcases lt_trichotomy ab.2 cd.2 with hlt | heq | hgt
    · exact False.elim ((hgap cd hcd).2.2.2 _ (hgap ab hab).2.1
        ⟨by rw [←he]; exact (hgap ab hab).2.2.1,hlt⟩)
    · exact heq
    · exact False.elim ((hgap ab hab).2.2.2 _ (hgap cd hcd).2.1
        ⟨by rw [he]; exact (hgap cd hcd).2.2.1,hgt⟩)
  let G₀ := G.filter (fun ab => ab.1<lo)
  let G₁ := G.filter (fun ab => ¬ab.1<lo)
  have hsmall : G₀.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro ab hab cd hcd
    have ha := Finset.mem_filter.mp hab
    have hc := Finset.mem_filter.mp hcd
    apply hinj ha.1 hc.1
    rcases lt_trichotomy ab.1 cd.1 with hlt | heq | hgt
    · exact False.elim ((hgap ab ha.1).2.2.2 _ (hgap cd hc.1).1
        ⟨hlt,hc.2.trans_le (hmeet ab ha.1).2⟩)
    · exact heq
    · exact False.elim ((hgap cd hc.1).2.2.2 _ (hgap ab ha.1).1
        ⟨hgt,ha.2.trans_le (hmeet cd hc.1).2⟩)
  have hlarge := separated_reference_interval_card (G₁.image Prod.fst) hd hlohi
    (by
      intro x hx y hy hne
      obtain ⟨ab,hab,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp hy
      exact hsep _ (hgap ab (Finset.mem_filter.mp hab).1).1
        _ (hgap cd (Finset.mem_filter.mp hcd).1).1 hne)
    (by
      intro x hx
      obtain ⟨ab,hab,rfl⟩ := Finset.mem_image.mp hx
      have ha := Finset.mem_filter.mp hab
      exact ⟨le_of_not_gt ha.2,(hmeet ab ha.1).1⟩)
  have he : (G₁.image Prod.fst).card=G₁.card :=
    Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _))
  rw [he] at hlarge
  have hcard : G.card=G₀.card+G₁.card :=
    (Finset.card_filter_add_card_filter_not (s:=G) (fun ab => ab.1<lo)).symm
  have hcardR : (G.card:ℝ)=(G₀.card:ℝ)+(G₁.card:ℝ) := by exact_mod_cast hcard
  have hsmallR : (G₀.card:ℝ) ≤ 1 := by exact_mod_cast hsmall
  linarith only [hcardR,hsmallR,hlarge]


private theorem reference_gap_count_of_closed_profile_width
    (S : Finset ℝ) (G : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ)
    {d D : ℝ} (hd : 0 < d) (hD : 0 ≤ D)
    (hsep : ∀ x∈S, ∀ y∈S, x≠y → d ≤ |x-y|)
    (hgap : ∀ ab∈G, ab.1∈S ∧ ab.2∈S ∧ ab.1 < ab.2 ∧
      ∀ t∈S, ¬(ab.1 < t ∧ t < ab.2))
    (hpoint : ∀ ab∈G, p ab∈Icc ab.1 ab.2)
    (hwidth : ∀ ab∈G, ∀ cd∈G, |p cd-p ab| ≤ D) :
    (G.card:ℝ) ≤ D/d+2 := by
  classical
  by_cases hG : G.Nonempty
  · let Values := G.image p
    have hv : Values.Nonempty := Finset.Nonempty.image hG p
    let lo := Values.min' hv
    let hi := Values.max' hv
    obtain ⟨ab,hab,hablo⟩ := Finset.mem_image.mp (Finset.min'_mem Values hv)
    obtain ⟨cd,hcd,hcdhi⟩ := Finset.mem_image.mp (Finset.max'_mem Values hv)
    have hbounds g (hg : g∈G) : lo ≤ p g ∧ p g ≤ hi :=
      ⟨Finset.min'_le Values _ (Finset.mem_image.mpr ⟨g,hg,rfl⟩),
        Finset.le_max' Values _ (Finset.mem_image.mpr ⟨g,hg,rfl⟩)⟩
    have hlohi : lo ≤ hi := (hbounds ab hab).1.trans (hbounds ab hab).2
    have hspan : hi-lo ≤ D := by
      change Values.max' hv-Values.min' hv ≤ D
      rw [←hablo,←hcdhi]
      exact (abs_le.mp (hwidth ab hab cd hcd)).2
    have hc := adjacent_reference_gap_card_closed S G hd hlohi hsep hgap (by
      intro g hg
      exact ⟨(hpoint g hg).1.trans (hbounds g hg).2,
        (hbounds g hg).1.trans (hpoint g hg).2⟩)
    exact hc.trans (add_le_add (div_le_div_of_nonneg_right hspan hd.le) le_rfl)
  · have he : G=∅ := Finset.not_nonempty_iff_eq_empty.mp hG
    rw [he]
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity


private theorem paired_large_entry_closed_reference_gap_packing
    (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ))
    (x y : ℝ × ℝ → ℝ) (Mat : Fin 4 → ℤ)
    {σ δ T M R U Δ : ℝ} {τ A W : Fin 2 → ℝ} {F : Fin 2 → ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hτ : ∀ i, T ≤ τ i ∧ τ i ≤ 2*T)
    (hM : 0 < M) (hR : 0 < R) (hU : 0 < U) (hΔ : 0 ≤ Δ)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hMat : Mat 0*Mat 3-Mat 1*Mat 2=1) (hc : Mat 2≠0)
    (hlarge : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a≠b → U/(4*R^2) ≤ |a-b|)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ z∈Refs, ¬(ab.1 < z ∧ z < ab.2))
    (hx : ∀ ab∈Gaps, x ab∈Ioo (1/2:ℝ) (W 0-1/2))
    (hy : ∀ ab∈Gaps, y ab∈Ioo (1/2:ℝ) (W 1-1/2)) :
    let f := fun i => heathBrownPhysicalPhase (F i) (τ i) M (A i) 1
    let p := fun ab => iteratedDeriv 2 (f 0) (x ab)/2
    let mu := fun i z => iteratedDeriv 3 (f i) (round z)/6
    let t := fun ab => (Mat 2:ℝ)*p ab+Mat 3
    (∀ ab∈Gaps, p ab∈Icc ab.1 ab.2) →
    (∀ ab∈Gaps, ((Mat 0:ℝ)*p ab+Mat 1)/t ab=iteratedDeriv 2 (f 1) (y ab)/2) →
    (∀ ab∈Gaps, t ab∈Icc (1/2:ℝ) 2) →
    (∀ ab∈Gaps, |mu 1 (y ab)*(t ab)^3/mu 0 (x ab)-1| ≤ Δ) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let Gamma := Cphys/κ
    let eta := (modelPhaseJetCoefficient σ 3+δ)/(2*κ*M)
    (Gaps.card:ℝ) ≤ 64*Cphys*(Gamma^2*Δ+2*Gamma*eta)*R^2/
      (κ*|(Mat 2:ℝ)| *U)+2 := by
  classical
  intro f p mu t hpoint hmap ht hthird κ Cphys Gamma eta
  have hδ0 : 0 ≤ δ := approximateModelPhase_tolerance_nonneg (hF 0)
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCp : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hGamma : 0 < Gamma := div_pos hCp hκ
  have hC₃ : 0 ≤ modelPhaseJetCoefficient σ 3+δ :=
    add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have heta : 0 ≤ eta := by dsimp only [eta]; positivity
  have hcpos : 0 < |(Mat 2:ℝ)| := abs_pos.mpr (by exact_mod_cast hc)
  let Width := 16*Cphys*(Gamma^2*Δ+2*Gamma*eta)/(κ*|(Mat 2:ℝ)|)
  have hw0 : 0 ≤ Width := by dsimp only [Width]; positivity
  have hordered ab (hab : ab∈Gaps) cd (hcd : cd∈Gaps) (horder : p ab ≤ p cd) :
      p cd-p ab ≤ Width := by
    exact physicalModelPhase_paired_large_entry_curvature_diameter
      ![x ab,x cd] ![y ab,y cd] (Mat 0) (Mat 1) (Mat 2) (Mat 3)
      hσ hδ hδ0 hF hT hτ hM hA hW hΔ hMat hc hlarge
      (by intro i; fin_cases i; exact hx ab hab; exact hx cd hcd)
      (by intro i; fin_cases i; exact hy ab hab; exact hy cd hcd)
      horder
      (by intro i; fin_cases i; exact hmap ab hab; exact hmap cd hcd)
      (by intro i; fin_cases i; exact ht ab hab; exact ht cd hcd)
      (by intro i; fin_cases i; exact hthird ab hab; exact hthird cd hcd)
  have hwidth ab (hab : ab∈Gaps) cd (hcd : cd∈Gaps) : |p cd-p ab| ≤ Width := by
    by_cases hle : p ab ≤ p cd
    · rw [abs_of_nonneg (sub_nonneg.mpr hle)]
      exact hordered ab hab cd hcd hle
    · rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hle))]
      exact hordered cd hcd ab hab (le_of_not_ge hle)
  have hp := reference_gap_count_of_closed_profile_width Refs Gaps p
    (show 0 < U/(4*R^2) by positivity) hw0 hsep hgap hpoint hwidth
  apply hp.trans_eq
  dsimp only [Width]
  field_simp
  ring_nf




/-- Ordinary Third Conditions are derived from the literal Fourier clouds.
For one actual representative in each occupied reference gap, this proves the
large-entry gap count used for short families, without a Third certificate. -/
private theorem physicalModelPhase_actual_fourier_large_entry_closed_reference_gap_count
    (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) (Mat : Fin 4 → ℤ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℝ × ℝ → Fin 2 → ℚ) (vinv : ℝ × ℝ → Fin 2 → ℤ)
    (parity : ℝ × ℝ → Fin 2 → Fin 2) (x : ℝ × ℝ → Fin 2 → ℝ)
    {σ δ T M N R U : ℝ} {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hU : 0 < U)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2) (hNscale : N^2 ≤ M*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hMat : Mat 0*Mat 3-Mat 1*Mat 2=1) (hc : Mat 2≠0)
    (hlarge : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a≠b → U/(4*R^2) ≤ |a-b|)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2))
    (hx : ∀ ab∈Gaps, ∀ i, x ab i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ ab∈Gaps, ∀ i, (rat ab i).den ≤ Q ∧ Q ≤ 2*(rat ab i).den)
    (hinv : ∀ ab∈Gaps, ∀ i, ((rat ab i).den:ℤ) ∣ (rat ab i).num*vinv ab i-1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ab∈Gaps, ∀ i, iteratedDeriv 2 (f i) (x ab i)/2=(rat ab i:ℝ)) →
    let q := fun ab i => (rat ab i).den
    let mu := fun ab i => iteratedDeriv 3 (f i) (round (x ab i))/6
    let ell := fun ab i => deriv (f i) (round (x ab i))
    let b := fun ab i => (⌊(q ab i:ℝ)*ell ab i⌋+(parity ab i:ℕ) : ℤ)
    let cround := fun ab i => round ((q ab i:ℝ)*ell ab i)
    let tau := fun ab i => ((b ab i:ℝ)-(q ab i:ℝ)*ell ab i)/2
    let dual := fun ab i => -2*mu ab i*(Real.sqrt (2/(3*mu ab i*(q ab i:ℝ))))^3
    let cloud := fun ab i => (![Int.fract (-(vinv ab i:ℝ)*b ab i/q ab i),
      Int.fract (-(vinv ab i:ℝ)/q ab i),dual ab i/Real.sqrt K₀,
      (3*dual ab i*tau ab i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ab∈Gaps, b ab 0-cround ab 0=b ab 1-cround ab 1) →
    (∀ ab∈Gaps, ∀ a, |cloud ab 0 a-cloud ab 1 a| ≤ 2*radius a) →
    (∀ ab∈Gaps, (Mat 2:ℝ)*(rat ab 0:ℝ)+Mat 3=(q ab 1:ℝ)/q ab 0) →
    (∀ ab∈Gaps, ((Mat 0:ℝ)*(rat ab 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat ab 0:ℝ)+Mat 3)=(rat ab 1:ℝ)) →
    (∀ ab∈Gaps, (rat ab 0:ℝ)∈Icc ab.1 ab.2) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    let Gamma := Cphys/κ
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    (Gaps.card:ℝ) ≤ 2+Cgap*R^4/(N^2*|(Mat 2:ℝ)| *U) := by
  classical
  intro f hlevel q mu ell b cround tau dual cloud radius hcolor hnear hMatt hMatmap
    hsourceGap κ Cphys c J B Gamma Cgap
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hGamma : 0 < Gamma := div_pos hCphys hκ
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hδ0 := approximateModelPhase_tolerance_nonneg (hF 0)
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hratio ab (hab : ab∈Gaps) : (q ab 1:ℝ)/q ab 0∈Icc (1/2:ℝ) 2 := by
    have hq : (0:ℝ) < q ab 0 := by exact_mod_cast (rat ab 0).den_pos
    have hlo₀ : ((q ab 0):ℝ) ≤ Q := by exact_mod_cast (hden ab hab 0).1
    have hhi₀ : (Q:ℝ) ≤ 2*q ab 0 := by exact_mod_cast (hden ab hab 0).2
    have hlo₁ : ((q ab 1):ℝ) ≤ Q := by exact_mod_cast (hden ab hab 1).1
    have hhi₁ : (Q:ℝ) ≤ 2*q ab 1 := by exact_mod_cast (hden ab hab 1).2
    constructor
    · apply (le_div_iff₀ hq).mpr
      linarith only [hlo₀,hhi₁]
    · apply (div_le_iff₀ hq).mpr
      linarith only [hlo₁,hhi₀]
  have hthird ab (hab : ab∈Gaps) :
      |mu ab 1*((Mat 2:ℝ)*(iteratedDeriv 2 (f 0) (x ab 0)/2)+Mat 3)^3/mu ab 0-1| ≤ B*R^2/N^2 := by
    obtain ⟨_v,_hv,hh,_hrest⟩ := physicalModelPhase_actual_fourier_conditions
      Q K₀ (rat ab) (vinv ab) (parity ab)
      hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW
      (hx ab hab) (hden ab hab) (hinv ab hab) (hlevel ab hab)
      (hcolor ab hab) (hnear ab hab)
    rw [hlevel ab hab 0,hMatt ab hab]
    have he : mu ab 1*((q ab 1:ℝ)/q ab 0)^3/mu ab 0-1=
        mu ab 1*(q ab 1:ℝ)^3/(mu ab 0*(q ab 0:ℝ)^3)-1 := by
      rw [div_pow]
      ring_nf
    rw [he]
    exact hh
  have hp := paired_large_entry_closed_reference_gap_packing (τ:=fun _ => T)
    Refs Gaps (fun ab => x ab 0) (fun ab => x ab 1) Mat
    hσ hδ hF hT (fun _ => ⟨le_rfl,by linarith only [hT]⟩) hM hR hU
    (show 0 ≤ B*R^2/N^2 by positivity) hA hW hMat hc hlarge hsep hgap
    (fun ab hab => hx ab hab 0) (fun ab hab => hx ab hab 1)
    (fun ab hab => by
      change iteratedDeriv 2 (f 0) (x ab 0)/2∈Icc ab.1 ab.2
      rw [hlevel ab hab 0]
      exact hsourceGap ab hab)
    (fun ab hab => by
      change ((Mat 0:ℝ)*(iteratedDeriv 2 (f 0) (x ab 0)/2)+Mat 1)/
        ((Mat 2:ℝ)*(iteratedDeriv 2 (f 0) (x ab 0)/2)+Mat 3)=iteratedDeriv 2 (f 1) (x ab 1)/2
      rw [hlevel ab hab 0,hlevel ab hab 1]
      exact hMatmap ab hab)
    (fun ab hab => by
      change (Mat 2:ℝ)*(iteratedDeriv 2 (f 0) (x ab 0)/2)+Mat 3∈Icc (1/2:ℝ) 2
      rw [hlevel ab hab 0,hMatt ab hab]
      exact hratio ab hab)
    hthird
  have hInv : 1/M ≤ R^2/N^2 := (div_le_div_iff₀ hM (sq_pos_of_pos hN)).mpr
    (by simpa only [one_mul,mul_one,mul_comm] using hNscale)
  have heta : 2*Gamma*((modelPhaseJetCoefficient σ 3+δ)/(2*κ*M)) ≤
      (Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)*(R^2/N^2) := by
    calc
      _ = (Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)*(1/M) := by ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left hInv (by positivity)
  apply hp.trans
  calc
    _ ≤ 64*Cphys*(Gamma^2*(B*R^2/N^2)+
        (Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)*(R^2/N^2))*R^2/
        (κ*|(Mat 2:ℝ)| *U)+2 := by
      apply add_le_add _ le_rfl
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg R)
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 64*Cphys)
      exact add_le_add le_rfl heta
    _ = _ := by dsimp only [Cgap]; ring_nf


theorem physicalModelPhase_actual_fourier_charted_all_reference_sample_mass
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (Bmajor Cmajor : ℕ)
    (S : ℝ × ℝ → Finset ℕ) (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℝ × ℝ → ℕ → Fin 2 → ℚ) (vinv : ℝ × ℝ → ℕ → Fin 2 → ℤ)
    (parity : ℝ × ℝ → ℕ → Fin 2 → Fin 2) (anchor : ℝ × ℝ → ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ℝ × ℝ → ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T)
    (hM : 0 < M)
    (hN : 0 < N)
    (hR : 1 ≤ R)
    (hRM : R ≤ M)
    (hQ : 0 < Q)
    (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i)
    (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ ab∈Gaps, ∀ j∈(S ab), (x ab) j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hden : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, ((rat ab) j i).den ≤ Q ∧ Q ≤ 2*((rat ab) j i).den)
    (hlambda : 0 < lambda)
    (hUband : 0 ≤ Uband)
    (hθ : 0 < θ)
    (hθmax : θ ≤ 1/24)
    (hcurv : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, lambda ≤ |((rat ab) j i:ℝ)| ∧ |((rat ab) j i:ℝ)| ≤ Uband)
    (hinv : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (((rat ab) j i).den:ℤ) ∣ ((rat ab) j i).num*(vinv ab) j i-1)
    (hchart : ∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1)
    (horientation : ∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2))
    (hBcut : 0 < Bcut)
    (hs : ∀ ab∈Gaps, (s ab) ≠ 0)
    (hrefSet : ∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs)
    (hparentSet : ∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|)
    (hwideL : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hUref : 1 ≤ Uref)
    (hBselectSize : 2+168/modelPhaseThirdLower σ ≤ Bselect)
    (hcutMargin : 7*Bcut ≤ modelPhaseThirdLower σ*Bselect)
    (hselectedWrap : Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2)
    (hreferenceDen : ∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ))
    (hgapWidth : ∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2))
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : N^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ ab∈Gaps, ∀ j∈(S ab), ((rat ab) j 0:ℝ)∈Icc ab.1 ab.2)
    (hc : Mat 2 ≠ 0)
    (hlarge : 64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (ab : ℝ × ℝ) => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (ab : ℝ × ℝ) => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun (ab : ℝ × ℝ) => fun j i => (⌊(((rat ab) j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊(((rat ab) j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ab∈Gaps, ∀ j∈(S ab), (sourceColor ab) j 0=(sourceColor ab) j 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, iteratedDeriv 2 (f i) ((x ab) j i)/2=((rat ab) j i:ℝ)) →
    let q := fun (ab : ℝ × ℝ) => fun j i => ((rat ab) j i).den
    let mu := fun (ab : ℝ × ℝ) => fun j i => iteratedDeriv 3 (f i) (round ((x ab) j i))/6
    let ell := fun (ab : ℝ × ℝ) => fun j i => deriv (f i) (round ((x ab) j i))
    let b := fun (ab : ℝ × ℝ) => fun j i => (⌊((q ab) j i:ℝ)*(ell ab) j i⌋+((parity ab) j i:ℕ) : ℤ)
    let cround := fun (ab : ℝ × ℝ) => fun j i => round (((q ab) j i:ℝ)*(ell ab) j i)
    let tau := fun (ab : ℝ × ℝ) => fun j i => (((b ab) j i:ℝ)-((q ab) j i:ℝ)*(ell ab) j i)/2
    let dual := fun (ab : ℝ × ℝ) => fun j i => -2*(mu ab) j i*(Real.sqrt (2/(3*(mu ab) j i*((q ab) j i:ℝ))))^3
    let cloud := fun (ab : ℝ × ℝ) => fun j i => (![Int.fract (-((vinv ab) j i:ℝ)*(b ab) j i/(q ab) j i),
      Int.fract (-((vinv ab) j i:ℝ)/(q ab) j i),(dual ab) j i/Real.sqrt K₀,
      (3*(dual ab) j i*(tau ab) j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ab∈Gaps, ∀ j∈(S ab), (b ab) j 0-(cround ab) j 0=(b ab) j 1-(cround ab) j 1) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ a, |(cloud ab) j 0 a-(cloud ab) j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 →
    N ≤ R^2 →
    R ≤ N →
    N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (∀ ab∈Gaps, ∀ j∈(S ab), (Mat 2:ℝ)*((rat ab) j 0:ℝ)+Mat 3=((q ab) j 1:ℝ)/(q ab) j 0) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ((Mat 0:ℝ)*((rat ab) j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*((rat ab) j 0:ℝ)+Mat 3)=((rat ab) j 1:ℝ)) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), |((anchor ab) j:ℝ)-((rat ab) j 0:ℝ)| ≤ ε) →
    (∀ ab∈Gaps, ∀ j∈(S ab), 256*(((anchor ab) j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ab∈Gaps, ∀ j∈(S ab), 256 ≤ (2*ε)*((Q:ℝ)/3)*((anchor ab) j).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Blabels := fun ab => 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ ab∈Gaps, Blabels ab ≤ Bmajor) →
    (∀ ab∈Gaps, Ccharts ab ≤ Cmajor) →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    (∑ ab∈Gaps, ((S ab).card:ℝ)) ≤
      4*(m0:ℝ)*((2*Cfirst*R^4/(Lunit^3*N^2)/|(Mat 2:ℝ)|)^((3:ℝ)⁻¹)+
        Cpack*R^4/(Lunit^2*N^2*|(Mat 2:ℝ)| *(Uref:ℝ)))+
      (m0:ℝ)*(2+Cgap*R^4/(N^2*|(Mat 2:ℝ)| *(Uref:ℝ))) := by
  classical
  intro Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor f hlevel
    q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Blabels m0 hBmajor hCmajor Lunit Gamma Cthird Cpack Cfirst Cgap
  let Long := Gaps.filter (fun ab => m0 ≤ (S ab).card)
  let Short := Gaps.filter (fun ab => (S ab).Nonempty ∧ (S ab).card < m0)
  have hinLong : Long ⊆ Gaps := Finset.filter_subset _ _
  have hinShort : Short ⊆ Gaps := Finset.filter_subset _ _
  have hlong := physicalModelPhase_actual_fourier_charted_reference_sample_mass
    Uref Refs Long (Bselect:=Bselect) Bmajor Cmajor S Q K₀ rat vinv parity anchor Mat e r v s
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW (fun ab hab => hx ab (hinLong hab)) (fun ab hab => hwindow ab (hinLong hab)) (fun ab hab => hden ab (hinLong hab)) hlambda hUband hθ hθmax (fun ab hab => hcurv ab (hinLong hab)) (fun ab hab => hinv ab (hinLong hab)) (fun ab hab => hchart ab (hinLong hab)) (fun ab hab => horientation ab (hinLong hab)) hBcut (fun ab hab => hs ab (hinLong hab)) (fun ab hab => hrefSet ab (hinLong hab)) (fun ab hab => hparentSet ab (hinLong hab)) hsep (fun ab hab => hwideL ab (hinLong hab)) (fun ab hab => hwideU ab (hinLong hab)) hUref hBselectSize hcutMargin hselectedWrap (fun ab hab => hreferenceDen ab (hinLong hab)) (fun ab hab => hgapWidth ab (hinLong hab)) hRQ hselectedUpper hscaleTen (fun ab hab => hfamilyGap ab (hinLong hab))
    hc hlarge (fun ab hab => hgap ab (hinLong hab))
    (fun ab hab => hsourceColor ab (hinLong hab)) (fun ab hab => hlevel ab (hinLong hab)) (fun ab hab => hcolor ab (hinLong hab)) (fun ab hab => hnear ab (hinLong hab)) hsmall hNR hRN hNcube hminscale hMatdet (fun ab hab => hMatt ab (hinLong hab)) (fun ab hab => hMatmap ab (hinLong hab)) hMatgamma hNtwo (fun ab hab => hL ab (hinLong hab)) (fun ab hab => hU ab (hinLong hab)) (fun ab hab => hanchor ab (hinLong hab)) (fun ab hab => hcut ab (hinLong hab)) (fun ab hab => hcount ab (hinLong hab))
    hsize hD hΔ hBsize
    (fun ab hab => hBmajor ab (hinLong hab))
    (fun ab hab => hCmajor ab (hinLong hab))
    (fun _ hab => (Finset.mem_filter.mp hab).2)
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hδ0 := approximateModelPhase_tolerance_nonneg (hF 0)
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hlarge32 : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *κ^2*T := by
    have hn := mul_nonneg hC₃ (sq_nonneg M)
    nlinarith only [hlarge,hn]
  have hUp : (0:ℝ) < Uref := by exact_mod_cast (show 0 < Uref by omega)
  have hF₃ i := approximateModelPhase_mono (hF i) (by norm_num : 3 ≤ 4) le_rfl
  have hNscale : N^2 ≤ M*R^2 := by
    have hm := mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ N by linarith only [hNtwo])
      (sq_nonneg N)
    nlinarith only [hm,hNcube]
  have hchoose ab (hab : ab∈Short) : ∃ j, j∈S ab :=
    (Finset.mem_filter.mp hab).2.1
  choose! j hj using hchoose
  have hshortcount :
      (Short.card:ℝ) ≤ 2+Cgap*R^4/(N^2*|(Mat 2:ℝ)| *(Uref:ℝ)) := by
    exact physicalModelPhase_actual_fourier_large_entry_closed_reference_gap_count
      Refs Short Mat Q K₀ (fun ab => rat ab (j ab)) (fun ab => vinv ab (j ab))
      (fun ab => parity ab (j ab)) (fun ab => x ab (j ab))
      hσ hδ hF₃ hT hM hN (zero_lt_one.trans_le hR) hUp hQ hscale hmesh hNscale
      hA hW hMatdet hc hlarge32
      (by
        intro a ha b hb hne
        calc
          (Uref:ℝ)/(4*R^2)=((Uref:ℝ)/R^2)/4 := by ring
          _ ≤ |a-b| := (hsep a ha b hb hne).le)
      (fun ab hab => hgap ab (hinShort hab))
      (fun ab hab => hx ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hden ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hinv ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hlevel ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hcolor ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hnear ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hMatt ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hMatmap ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hfamilyGap ab (hinShort hab) _ (hj ab hab))
  have hshortmass : (∑ ab∈Short, ((S ab).card:ℝ)) ≤
      (m0:ℝ)*(2+Cgap*R^4/(N^2*|(Mat 2:ℝ)| *(Uref:ℝ))) := by
    calc
      _ ≤ ∑ _ab∈Short, (m0:ℝ) := by
        apply Finset.sum_le_sum
        intro ab hab
        exact_mod_cast (Finset.mem_filter.mp hab).2.2.le
      _ = (m0:ℝ)*(Short.card:ℝ) := by simp [mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left hshortcount (Nat.cast_nonneg _)
  have hpartition : (∑ ab∈Gaps, ((S ab).card:ℝ)) =
      (∑ ab∈Long, ((S ab).card:ℝ))+(∑ ab∈Short, ((S ab).card:ℝ)) := by
    simp only [Long,Short,Finset.sum_filter,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ab _
    by_cases hh : m0 ≤ (S ab).card
    · simp [hh,not_lt.mpr hh]
    · have hlt : (S ab).card < m0 := lt_of_not_ge hh
      by_cases he : (S ab).Nonempty
      · simp [hh,he,hlt]
      · have hz : (S ab).card=0 := by simp [Finset.not_nonempty_iff_eq_empty.mp he]
        simp [he,hz]
  rw [hpartition]
  exact add_le_add hlong hshortmass

example
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (Bmajor Cmajor : ℕ)
    (S : ℝ × ℝ → Finset ℕ) (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℝ × ℝ → ℕ → Fin 2 → ℚ) (vinv : ℝ × ℝ → ℕ → Fin 2 → ℤ)
    (parity : ℝ × ℝ → ℕ → Fin 2 → Fin 2) (anchor : ℝ × ℝ → ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ℝ × ℝ → ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T)
    (hM : 0 < M)
    (hN : 0 < N)
    (hR : 1 ≤ R)
    (hRM : R ≤ M)
    (hQ : 0 < Q)
    (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i)
    (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ ab∈Gaps, ∀ j∈(S ab), (x ab) j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hden : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, ((rat ab) j i).den ≤ Q ∧ Q ≤ 2*((rat ab) j i).den)
    (hlambda : 0 < lambda)
    (hUband : 0 ≤ Uband)
    (hθ : 0 < θ)
    (hθmax : θ ≤ 1/24)
    (hcurv : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, lambda ≤ |((rat ab) j i:ℝ)| ∧ |((rat ab) j i:ℝ)| ≤ Uband)
    (hinv : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (((rat ab) j i).den:ℤ) ∣ ((rat ab) j i).num*(vinv ab) j i-1)
    (hchart : ∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1)
    (horientation : ∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2))
    (hBcut : 0 < Bcut)
    (hs : ∀ ab∈Gaps, (s ab) ≠ 0)
    (hrefSet : ∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs)
    (hparentSet : ∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|)
    (hwideL : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hUref : 1 ≤ Uref)
    (hBselectSize : 2+168/modelPhaseThirdLower σ ≤ Bselect)
    (hcutMargin : 7*Bcut ≤ modelPhaseThirdLower σ*Bselect)
    (hselectedWrap : Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2)
    (hreferenceDen : ∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ))
    (hgapWidth : ∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2))
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : N^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ ab∈Gaps, ∀ j∈(S ab), ((rat ab) j 0:ℝ)∈Icc ab.1 ab.2)
    (hc : Mat 2 ≠ 0)
    (hlarge : 64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (ab : ℝ × ℝ) => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (ab : ℝ × ℝ) => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun (ab : ℝ × ℝ) => fun j i => (⌊(((rat ab) j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊(((rat ab) j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ab∈Gaps, ∀ j∈(S ab), (sourceColor ab) j 0=(sourceColor ab) j 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, iteratedDeriv 2 (f i) ((x ab) j i)/2=((rat ab) j i:ℝ)) →
    let q := fun (ab : ℝ × ℝ) => fun j i => ((rat ab) j i).den
    let mu := fun (ab : ℝ × ℝ) => fun j i => iteratedDeriv 3 (f i) (round ((x ab) j i))/6
    let ell := fun (ab : ℝ × ℝ) => fun j i => deriv (f i) (round ((x ab) j i))
    let b := fun (ab : ℝ × ℝ) => fun j i => (⌊((q ab) j i:ℝ)*(ell ab) j i⌋+((parity ab) j i:ℕ) : ℤ)
    let cround := fun (ab : ℝ × ℝ) => fun j i => round (((q ab) j i:ℝ)*(ell ab) j i)
    let tau := fun (ab : ℝ × ℝ) => fun j i => (((b ab) j i:ℝ)-((q ab) j i:ℝ)*(ell ab) j i)/2
    let dual := fun (ab : ℝ × ℝ) => fun j i => -2*(mu ab) j i*(Real.sqrt (2/(3*(mu ab) j i*((q ab) j i:ℝ))))^3
    let cloud := fun (ab : ℝ × ℝ) => fun j i => (![Int.fract (-((vinv ab) j i:ℝ)*(b ab) j i/(q ab) j i),
      Int.fract (-((vinv ab) j i:ℝ)/(q ab) j i),(dual ab) j i/Real.sqrt K₀,
      (3*(dual ab) j i*(tau ab) j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ab∈Gaps, ∀ j∈(S ab), (b ab) j 0-(cround ab) j 0=(b ab) j 1-(cround ab) j 1) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ a, |(cloud ab) j 0 a-(cloud ab) j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 →
    N ≤ R^2 →
    R ≤ N →
    N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (∀ ab∈Gaps, ∀ j∈(S ab), (Mat 2:ℝ)*((rat ab) j 0:ℝ)+Mat 3=((q ab) j 1:ℝ)/(q ab) j 0) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ((Mat 0:ℝ)*((rat ab) j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*((rat ab) j 0:ℝ)+Mat 3)=((rat ab) j 1:ℝ)) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), |((anchor ab) j:ℝ)-((rat ab) j 0:ℝ)| ≤ ε) →
    (∀ ab∈Gaps, ∀ j∈(S ab), 256*(((anchor ab) j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ab∈Gaps, ∀ j∈(S ab), 256 ≤ (2*ε)*((Q:ℝ)/3)*((anchor ab) j).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Blabels := fun ab => 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ ab∈Gaps, Blabels ab ≤ Bmajor) →
    (∀ ab∈Gaps, Ccharts ab ≤ Cmajor) →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    (∑ ab∈Gaps, ((S ab).card:ℝ)) ≤
      4*(m0:ℝ)*((2*Cfirst*R^4/(Lunit^3*N^2)/|(Mat 2:ℝ)|)^((3:ℝ)⁻¹)+
        Cpack*R^4/(Lunit^2*N^2*|(Mat 2:ℝ)| *(Uref:ℝ)))+
      (m0:ℝ)*(2+Cgap*R^4/(N^2*|(Mat 2:ℝ)| *(Uref:ℝ))) :=
  HuxleyChartedMassScratch.physicalModelPhase_actual_fourier_charted_all_reference_sample_mass Uref Refs Gaps (Bselect:=Bselect) Bmajor Cmajor S Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (Bcut:=Bcut) (lambda:=lambda) (Uband:=Uband) (θ:=θ) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hc hlarge hgap



/-- Ordinary Third Conditions are derived from the literal Fourier clouds.
For one actual representative in each occupied reference gap, this proves the
large-entry gap count used for short families, without a Third certificate. -/
theorem physicalModelPhase_actual_fourier_large_entry_reference_gap_count
    (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) (Mat : Fin 4 → ℤ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℝ × ℝ → Fin 2 → ℚ) (vinv : ℝ × ℝ → Fin 2 → ℤ)
    (parity : ℝ × ℝ → Fin 2 → Fin 2) (x : ℝ × ℝ → Fin 2 → ℝ)
    {σ δ T M N R U : ℝ} {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hU : 0 < U)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2) (hNscale : N^2 ≤ M*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hMat : Mat 0*Mat 3-Mat 1*Mat 2=1) (hc : Mat 2≠0)
    (hlarge : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a≠b → U/(4*R^2) ≤ |a-b|)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2))
    (hx : ∀ ab∈Gaps, ∀ i, x ab i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ ab∈Gaps, ∀ i, (rat ab i).den ≤ Q ∧ Q ≤ 2*(rat ab i).den)
    (hinv : ∀ ab∈Gaps, ∀ i, ((rat ab i).den:ℤ) ∣ (rat ab i).num*vinv ab i-1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ab∈Gaps, ∀ i, iteratedDeriv 2 (f i) (x ab i)/2=(rat ab i:ℝ)) →
    let q := fun ab i => (rat ab i).den
    let mu := fun ab i => iteratedDeriv 3 (f i) (round (x ab i))/6
    let ell := fun ab i => deriv (f i) (round (x ab i))
    let b := fun ab i => (⌊(q ab i:ℝ)*ell ab i⌋+(parity ab i:ℕ) : ℤ)
    let cround := fun ab i => round ((q ab i:ℝ)*ell ab i)
    let tau := fun ab i => ((b ab i:ℝ)-(q ab i:ℝ)*ell ab i)/2
    let dual := fun ab i => -2*mu ab i*(Real.sqrt (2/(3*mu ab i*(q ab i:ℝ))))^3
    let cloud := fun ab i => (![Int.fract (-(vinv ab i:ℝ)*b ab i/q ab i),
      Int.fract (-(vinv ab i:ℝ)/q ab i),dual ab i/Real.sqrt K₀,
      (3*dual ab i*tau ab i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ab∈Gaps, b ab 0-cround ab 0=b ab 1-cround ab 1) →
    (∀ ab∈Gaps, ∀ a, |cloud ab 0 a-cloud ab 1 a| ≤ 2*radius a) →
    (∀ ab∈Gaps, (Mat 2:ℝ)*(rat ab 0:ℝ)+Mat 3=(q ab 1:ℝ)/q ab 0) →
    (∀ ab∈Gaps, ((Mat 0:ℝ)*(rat ab 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat ab 0:ℝ)+Mat 3)=(rat ab 1:ℝ)) →
    (∀ ab∈Gaps, (rat ab 0:ℝ)∈Ioo ab.1 ab.2) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    let Gamma := Cphys/κ
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    (Gaps.card:ℝ) ≤ 2+Cgap*R^4/(N^2*|(Mat 2:ℝ)| *U) := by
  intro f hlevel q mu ell b cround tau dual cloud radius hcolor hnear hMatt hMatmap
    hsourceGap κ Cphys c J B Gamma Cgap
  exact physicalModelPhase_actual_fourier_large_entry_closed_reference_gap_count
    Refs Gaps Mat Q K₀ rat vinv parity x
    hσ hδ hF hT hM hN hR hU hQ hscale hmesh hNscale hA hW hMat hc hlarge
    hsep hgap hx hden hinv hlevel hcolor hnear hMatt hMatmap
    (fun ab hab => ⟨(hsourceGap ab hab).1.le,(hsourceGap ab hab).2.le⟩)


example
    (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) (Mat : Fin 4 → ℤ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℝ × ℝ → Fin 2 → ℚ) (vinv : ℝ × ℝ → Fin 2 → ℤ)
    (parity : ℝ × ℝ → Fin 2 → Fin 2) (x : ℝ × ℝ → Fin 2 → ℝ)
    {σ δ T M N R U : ℝ} {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hU : 0 < U)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2) (hNscale : N^2 ≤ M*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hMat : Mat 0*Mat 3-Mat 1*Mat 2=1) (hc : Mat 2≠0)
    (hlarge : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a≠b → U/(4*R^2) ≤ |a-b|)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2))
    (hx : ∀ ab∈Gaps, ∀ i, x ab i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ ab∈Gaps, ∀ i, (rat ab i).den ≤ Q ∧ Q ≤ 2*(rat ab i).den)
    (hinv : ∀ ab∈Gaps, ∀ i, ((rat ab i).den:ℤ) ∣ (rat ab i).num*vinv ab i-1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ab∈Gaps, ∀ i, iteratedDeriv 2 (f i) (x ab i)/2=(rat ab i:ℝ)) →
    let q := fun ab i => (rat ab i).den
    let mu := fun ab i => iteratedDeriv 3 (f i) (round (x ab i))/6
    let ell := fun ab i => deriv (f i) (round (x ab i))
    let b := fun ab i => (⌊(q ab i:ℝ)*ell ab i⌋+(parity ab i:ℕ) : ℤ)
    let cround := fun ab i => round ((q ab i:ℝ)*ell ab i)
    let tau := fun ab i => ((b ab i:ℝ)-(q ab i:ℝ)*ell ab i)/2
    let dual := fun ab i => -2*mu ab i*(Real.sqrt (2/(3*mu ab i*(q ab i:ℝ))))^3
    let cloud := fun ab i => (![Int.fract (-(vinv ab i:ℝ)*b ab i/q ab i),
      Int.fract (-(vinv ab i:ℝ)/q ab i),dual ab i/Real.sqrt K₀,
      (3*dual ab i*tau ab i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ab∈Gaps, b ab 0-cround ab 0=b ab 1-cround ab 1) →
    (∀ ab∈Gaps, ∀ a, |cloud ab 0 a-cloud ab 1 a| ≤ 2*radius a) →
    (∀ ab∈Gaps, (Mat 2:ℝ)*(rat ab 0:ℝ)+Mat 3=(q ab 1:ℝ)/q ab 0) →
    (∀ ab∈Gaps, ((Mat 0:ℝ)*(rat ab 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat ab 0:ℝ)+Mat 3)=(rat ab 1:ℝ)) →
    (∀ ab∈Gaps, (rat ab 0:ℝ)∈Ioo ab.1 ab.2) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    let Gamma := Cphys/κ
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    (Gaps.card:ℝ) ≤ 2+Cgap*R^4/(N^2*|(Mat 2:ℝ)| *U) :=
  HuxleyChartedMassScratch.physicalModelPhase_actual_fourier_large_entry_reference_gap_count Refs Gaps Mat Q K₀ rat vinv parity x (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (U:=U) (F:=F) (A:=A) (W:=W) hσ hδ hF hT hM hN hR hU hQ hscale hmesh hNscale hA hW hMat hc hlarge hsep hgap hx hden hinv



#print axioms physicalModelPhase_actual_fourier_large_entry_reference_gap_count

private theorem reference_gap_count_of_profile_width
    (S : Finset ℝ) (G : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ)
    {d D : ℝ} (hd : 0 < d) (hD : 0 ≤ D)
    (hsep : ∀ x∈S, ∀ y∈S, x≠y → d ≤ |x-y|)
    (hgap : ∀ ab∈G, ab.1∈S ∧ ab.2∈S ∧ ab.1 < ab.2 ∧
      ∀ t∈S, ¬(ab.1 < t ∧ t < ab.2))
    (hpoint : ∀ ab∈G, p ab∈Ioo ab.1 ab.2)
    (hwidth : ∀ ab∈G, ∀ cd∈G, |p cd-p ab| ≤ D) :
    (G.card:ℝ) ≤ D/d+2 := by
  exact reference_gap_count_of_closed_profile_width S G p hd hD hsep hgap
    (fun ab hab => ⟨(hpoint ab hab).1.le,(hpoint ab hab).2.le⟩) hwidth


private theorem paired_large_entry_reference_gap_packing
    (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ))
    (x y : ℝ × ℝ → ℝ) (Mat : Fin 4 → ℤ)
    {σ δ T M R U Δ : ℝ} {τ A W : Fin 2 → ℝ} {F : Fin 2 → ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hτ : ∀ i, T ≤ τ i ∧ τ i ≤ 2*T)
    (hM : 0 < M) (hR : 0 < R) (hU : 0 < U) (hΔ : 0 ≤ Δ)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hMat : Mat 0*Mat 3-Mat 1*Mat 2=1) (hc : Mat 2≠0)
    (hlarge : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a≠b → U/(4*R^2) ≤ |a-b|)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ z∈Refs, ¬(ab.1 < z ∧ z < ab.2))
    (hx : ∀ ab∈Gaps, x ab∈Ioo (1/2:ℝ) (W 0-1/2))
    (hy : ∀ ab∈Gaps, y ab∈Ioo (1/2:ℝ) (W 1-1/2)) :
    let f := fun i => heathBrownPhysicalPhase (F i) (τ i) M (A i) 1
    let p := fun ab => iteratedDeriv 2 (f 0) (x ab)/2
    let mu := fun i z => iteratedDeriv 3 (f i) (round z)/6
    let t := fun ab => (Mat 2:ℝ)*p ab+Mat 3
    (∀ ab∈Gaps, p ab∈Ioo ab.1 ab.2) →
    (∀ ab∈Gaps, ((Mat 0:ℝ)*p ab+Mat 1)/t ab=iteratedDeriv 2 (f 1) (y ab)/2) →
    (∀ ab∈Gaps, t ab∈Icc (1/2:ℝ) 2) →
    (∀ ab∈Gaps, |mu 1 (y ab)*(t ab)^3/mu 0 (x ab)-1| ≤ Δ) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let Gamma := Cphys/κ
    let eta := (modelPhaseJetCoefficient σ 3+δ)/(2*κ*M)
    (Gaps.card:ℝ) ≤ 64*Cphys*(Gamma^2*Δ+2*Gamma*eta)*R^2/
      (κ*|(Mat 2:ℝ)| *U)+2 := by
  intro f p mu t hpoint hmap ht hthird κ Cphys Gamma eta
  exact paired_large_entry_closed_reference_gap_packing Refs Gaps x y Mat
    hσ hδ hF hT hτ hM hR hU hΔ hA hW hMat hc hlarge hsep hgap hx hy
    (fun ab hab => ⟨(hpoint ab hab).1.le,(hpoint ab hab).2.le⟩) hmap ht hthird


example
    (S : Finset ℝ) (G : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ)
    {d D : ℝ} (hd : 0 < d) (hD : 0 ≤ D)
    (hsep : ∀ x∈S, ∀ y∈S, x≠y → d ≤ |x-y|)
    (hgap : ∀ ab∈G, ab.1∈S ∧ ab.2∈S ∧ ab.1 < ab.2 ∧
      ∀ t∈S, ¬(ab.1 < t ∧ t < ab.2))
    (hpoint : ∀ ab∈G, p ab∈Ioo ab.1 ab.2)
    (hwidth : ∀ ab∈G, ∀ cd∈G, |p cd-p ab| ≤ D) :
    (G.card:ℝ) ≤ D/d+2 :=
  HuxleyChartedMassScratch.reference_gap_count_of_profile_width S G p (d:=d) (D:=D) hd hD hsep hgap hpoint hwidth

example
    (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ))
    (x y : ℝ × ℝ → ℝ) (Mat : Fin 4 → ℤ)
    {σ δ T M R U Δ : ℝ} {τ A W : Fin 2 → ℝ} {F : Fin 2 → ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hτ : ∀ i, T ≤ τ i ∧ τ i ≤ 2*T)
    (hM : 0 < M) (hR : 0 < R) (hU : 0 < U) (hΔ : 0 ≤ Δ)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hMat : Mat 0*Mat 3-Mat 1*Mat 2=1) (hc : Mat 2≠0)
    (hlarge : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a≠b → U/(4*R^2) ≤ |a-b|)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ z∈Refs, ¬(ab.1 < z ∧ z < ab.2))
    (hx : ∀ ab∈Gaps, x ab∈Ioo (1/2:ℝ) (W 0-1/2))
    (hy : ∀ ab∈Gaps, y ab∈Ioo (1/2:ℝ) (W 1-1/2)) :
    let f := fun i => heathBrownPhysicalPhase (F i) (τ i) M (A i) 1
    let p := fun ab => iteratedDeriv 2 (f 0) (x ab)/2
    let mu := fun i z => iteratedDeriv 3 (f i) (round z)/6
    let t := fun ab => (Mat 2:ℝ)*p ab+Mat 3
    (∀ ab∈Gaps, p ab∈Ioo ab.1 ab.2) →
    (∀ ab∈Gaps, ((Mat 0:ℝ)*p ab+Mat 1)/t ab=iteratedDeriv 2 (f 1) (y ab)/2) →
    (∀ ab∈Gaps, t ab∈Icc (1/2:ℝ) 2) →
    (∀ ab∈Gaps, |mu 1 (y ab)*(t ab)^3/mu 0 (x ab)-1| ≤ Δ) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let Gamma := Cphys/κ
    let eta := (modelPhaseJetCoefficient σ 3+δ)/(2*κ*M)
    (Gaps.card:ℝ) ≤ 64*Cphys*(Gamma^2*Δ+2*Gamma*eta)*R^2/
      (κ*|(Mat 2:ℝ)| *U)+2 :=
  HuxleyChartedMassScratch.paired_large_entry_reference_gap_packing Refs Gaps x y Mat (σ:=σ) (δ:=δ) (T:=T) (M:=M) (R:=R) (U:=U) (Δ:=Δ) (τ:=τ) (A:=A) (W:=W) (F:=F) hσ hδ hF hT hτ hM hR hU hΔ hA hW hMat hc hlarge hsep hgap hx hy



#print axioms reference_gap_count_of_profile_width
#print axioms paired_large_entry_reference_gap_packing

#print axioms adjacent_reference_gap_card_closed
#print axioms reference_gap_count_of_closed_profile_width
#print axioms paired_large_entry_closed_reference_gap_packing
#print axioms physicalModelPhase_actual_fourier_large_entry_closed_reference_gap_count
#print axioms physicalModelPhase_actual_fourier_charted_all_reference_sample_mass
#print axioms physicalModelPhase_actual_fourier_charted_reference_sample_mass
end HuxleyChartedMassScratch
