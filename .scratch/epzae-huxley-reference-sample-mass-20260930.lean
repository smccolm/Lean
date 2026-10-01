import TaoTrudgianYang2025.HuxleyLinearForms
open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped ContDiff FourierTransform BigOperators
namespace HuxleyReferenceMassScratch
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

/-- The actual signed-height source samples are summed across ALL long
reference gaps for a fixed large-entry matrix. The proof combines the genuine
two-term First Condition with improved-Third gap packing and a convergent
occupied-tail sum, with no extra full-interval packing factor. -/
theorem physicalModelPhase_signed_height_reference_sample_mass
    {Kcoord : ℕ}
    (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) (Mat : Fin 4 → ℤ)
    (S : ℝ × ℝ → Finset ℕ) (p : ℝ × ℝ → ℕ → ℤ × ℤ)
    (x : ℝ × ℝ → ℕ → Fin 2 → ℝ)
    (xref e r v s H : ℝ × ℝ → Fin 2 → ℝ)
    (d nSpan base l w y₀ ac bc : ℝ × ℝ → ℝ) (k : ℝ × ℝ → Fin 17)
    {σ δ T M N R U Cres Q D Ccurv Bcut P₁ P₂ : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R)
    (hU : 0 < U) (hCres : 0 ≤ Cres)
    (hD₀ : 0 ≤ D) (hD : D ≤ 1/2) (hDupper : D ≤ Cres*Q/N)
    (hscale : T*N*R^2=M^3)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hP₂ : 0 < P₂) (hCcurv : 0 ≤ Ccurv) (hBcut : 0 < Bcut)
    (hBsize : ((2*Kcoord+1:ℕ):ℝ)*Ccurv*(σ*(σ+1)+1) ≤ Bcut)
    (hMat : Mat 0*Mat 3-Mat 1*Mat 2=1) (hc : Mat 2≠0)
    (hlarge : 64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a≠b → U/(4*R^2) ≤ |a-b|)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2))
    (hd : ∀ ab∈Gaps, 0 < d ab)
    (href : ∀ ab∈Gaps, ∀ i, xref ab i∈Ioo (1/2:ℝ) (W i-1/2))
    (hheight : ∀ ab∈Gaps, ∀ j∈S ab, |((p ab j).1:ℝ)| ≤ P₁ ∧ ((p ab j).2:ℝ) ≤ P₂)
    (hpt : ∀ ab∈Gaps, ∀ j∈S ab, 0 < (p ab j).2)
    (hQband : ∀ ab∈Gaps, ∀ j∈S ab, Q ≤ 2*(r ab 0*(p ab j).1+s ab 0*(p ab j).2))
    (hx : ∀ ab∈Gaps, ∀ j∈S ab, ∀ i, x ab j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ ab∈Gaps, ∀ j∈S ab,
      x ab j 0∈Icc (base ab+N*(j:ℝ)) (base ab+N*((j:ℝ)+1)))
    (hdisplacement : ∀ ab∈Gaps, ∀ j∈S ab, ∀ i, |x ab j i-xref ab i| ≤ H ab i)
    (hspan : ∀ ab∈Gaps, ∀ i, 2*H ab i+1 ≤ nSpan ab)
    (hnsquare : ∀ ab∈Gaps, (nSpan ab)^2 ≤ M*R)
    (hr : ∀ ab∈Gaps, ∀ i, r ab i≠0)
    (hdet : ∀ ab∈Gaps, ∀ i, v ab i*r ab i-e ab i*s ab i=1)
    (hden : ∀ ab∈Gaps, ∀ t∈Icc (l ab) (w ab), ∀ i,
      d ab ≤ r ab i*t+s ab i ∧ r ab i*t+s ab i ≤ 2*d ab)
    (hcoord : ∀ ab∈Gaps, |r ab 0| * max |l ab| |w ab| ≤ (Kcoord:ℝ)*d ab)
    (htransport : ∀ ab∈Gaps,
      e ab 1=(Mat 0:ℝ)*e ab 0+Mat 1*r ab 0 ∧
      v ab 1=(Mat 0:ℝ)*v ab 0+Mat 1*s ab 0 ∧
      r ab 1=(Mat 2:ℝ)*e ab 0+Mat 3*r ab 0 ∧
      s ab 1=(Mat 2:ℝ)*v ab 0+Mat 3*s ab 0) :
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let mu := fun ab i => iteratedDeriv 3 (f i) (round (xref ab i))/6
    let nu := fun ab i => iteratedDeriv 4 (f i) (round (xref ab i))/24
    let y := fun ab j => ((p ab j).1:ℝ)/(p ab j).2
    let g := fun ab => rationalPhase (mu ab 0) (r ab 0) (s ab 0) (mu ab 1) (r ab 1) (s ab 1)
    let h := fun ab => quarticPhase (mu ab 0) (nu ab 0) (r ab 0) (s ab 0)
      (mu ab 1) (nu ab 1) (r ab 1) (s ab 1)
    let phi := fun ab t => g ab t-h ab t
    let Gcoord := fun ab => minorArcCoordinate (mu ab 0) (r ab 0) (s ab 0)
    let Vcurv := fun ab => Ccurv*R^4/(N*(d ab)^3)
    let Z := fun ab => quarticCurvatureBoundaryRoots (mu ab 0) (nu ab 0) (r ab 0) (s ab 0)
      (mu ab 1) (nu ab 1) (r ab 1) (s ab 1) (Vcurv ab)
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let K := 4*Cres/κ
    let Gamma := Cphys/κ
    (∀ ab∈Gaps, 32*Blabels ≤ (S ab).card) →
    (∀ ab∈Gaps, |Gcoord ab (l ab)| ≤ |r ab 0| *N^2/(Bcut*R^2)) →
    (∀ ab∈Gaps, ∀ i, iteratedDeriv 2 (f i) (xref ab i)/2=e ab i/r ab i) →
    (∀ ab∈Gaps, ∀ j∈S ab, ∀ i, iteratedDeriv 2 (f i) (x ab j i)/2=
      (e ab i*(p ab j).1+v ab i*(p ab j).2)/(r ab i*(p ab j).1+s ab i*(p ab j).2)) →
    (∀ ab∈Gaps, ∀ j∈S ab, iteratedDeriv 2 (f 0) (x ab j 0)/2∈Ioo ab.1 ab.2) →
    (∀ ab∈Gaps, y₀ ab∈finiteBoundaryCell (Z ab) (l ab) (w ab) (k ab)) →
    (∀ ab∈Gaps, ∀ j∈S ab, y ab j∈finiteBoundaryCell (Z ab) (l ab) (w ab) (k ab)) →
    (∀ ab∈Gaps, |iteratedDeriv 2 (g ab) (y₀ ab)-iteratedDeriv 2 (h ab) (y₀ ab)| ≤ Vcurv ab) →
    (∀ ab∈Gaps, ∀ j∈S ab,
      |(ac ab-round (ac ab-deriv (phi ab) (y ab j)))*y ab j+
        (bc ab-round (bc ab-phi ab (y ab j)+y ab j*deriv (phi ab) (y ab j)))-
        g ab (y ab j)+h ab (y ab j)| ≤ D/(p ab j).2) →
    let Cthird := Gamma*(32*K+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let m0 := 32*Blabels
    let Lunit := 2*κ/Cphys
    (∑ ab∈Gaps, ((S ab).card:ℝ)) ≤
      4*(m0:ℝ)*((2*Cfirst*R^4/(Lunit^3*N^2)/|(Mat 2:ℝ)|)^((3:ℝ)⁻¹)+
        Cpack*R^4/(Lunit^2*N^2*|(Mat 2:ℝ)| *U)) := by
  classical
  intro Blabels f mu nu y g h phi Gcoord Vcurv Z κ Cphys K Gamma
    hS hGcut hbase hpoint hsourceGap hy₀ hy hcurv hres Cthird Cpack Cfirst m0 Lunit
  let Lsource := fun ab => κ/(16*(Blabels:ℝ)*Cphys)*((S ab).card:ℝ)
  let Csecond := 32*(modelPhaseJetCoefficient σ 3+δ)/κ^2
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hB : (0:ℝ) < Blabels := by dsimp only [Blabels]; positivity
  have hm0 : 0 < m0 := by dsimp only [m0,Blabels]; omega
  have hm0R : (0:ℝ) < m0 := by exact_mod_cast hm0
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hlambda : 0 < κ/(16*(Blabels:ℝ)*Cphys) := by positivity
  have hunit : 0 < Lunit := by dsimp only [Lunit]; positivity
  have hunitEq : Lunit=κ/(16*(Blabels:ℝ)*Cphys)*(m0:ℝ) := by
    dsimp only [Lunit,m0]
    push_cast
    field_simp; ring
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hδ0 := approximateModelPhase_tolerance_nonneg (hF 0)
  have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hC₄ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδ0
  have hCR : 0 ≤ quarticReciprocalConstant σ δ := by
    dsimp only [quarticReciprocalConstant]
    positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hGamma : 0 < Gamma := div_pos hCphys hκ
  have hCt : 0 ≤ Cthird := by dsimp only [Cthird]; positivity
  have hCp : 0 ≤ Cpack := by dsimp only [Cpack]; positivity
  have hCf : 0 ≤ Cfirst := by dsimp only [Cfirst]; positivity
  have hCmat : 0 < |(Mat 2:ℝ)| := abs_pos.mpr (by exact_mod_cast hc)
  have hlarge32 : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *κ^2*T := by
    have hn := mul_nonneg hC₃ (sq_nonneg M)
    nlinarith only [hlarge,hn]
  have hsmall : 2*(Csecond*N*R^2/M) ≤ |(Mat 2:ℝ)| := by
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
  have hLsrc ab (hab : ab∈Gaps) : 0 < Lsource ab := by
    have hcount : (0:ℝ) < (S ab).card := by exact_mod_cast (hm0.trans_le (hS ab hab))
    exact mul_pos hlambda hcount
  have hblock ab (hab : ab∈Gaps) : Lunit*(n ab:ℝ) ≤ Lsource ab := by
    have hh : (m0:ℝ)*(n ab:ℝ) ≤ (S ab).card := by exact_mod_cast (hn ab hab).2.1
    have hh' := mul_le_mul_of_nonneg_left hh hlambda.le
    rw [hunitEq]
    convert hh' using 1
    ring
  have hfirst ab (hab : ab∈Gaps) :
      |(Mat 2:ℝ)| ≤ Cfirst*R^4/((Lsource ab)^3*N^2)+Csecond*N*R^2/M := by
    exact physicalModelPhase_signed_height_square_span_first_condition
      (ac:=ac ab) (bc:=bc ab) (y₀:=y₀ ab)
      (S ab) (p ab) (x ab) Mat
      (hS ab hab) hσ hδ hF hT hM hN hR (hd ab hab) hCres hD₀ hD hDupper hscale
      hA hW (href ab hab) (hheight ab hab) (hpt ab hab) (hQband ab hab)
      (hx ab hab) (hwindow ab hab) (hdisplacement ab hab) (hspan ab hab)
      (hnsquare ab hab) (hr ab hab) (hdet ab hab) (hden ab hab) (hcoord ab hab)
      hP₂ hCcurv hBcut hBsize hMat (htransport ab hab) (hGcut ab hab)
      (hbase ab hab) (hpoint ab hab) (hy₀ ab hab) (hy ab hab) (hcurv ab hab) (hres ab hab)
  have hcap ab (hab : ab∈Gaps) : (n ab:ℝ)^3*|(Mat 2:ℝ)| ≤ 2*(Cfirst*R^4)/(Lunit^3*N^2) :=
    two_term_first_cubic_cap hCmat.le hN hunit (hLsrc ab hab) (Nat.cast_nonneg _)
      (hblock ab hab) (hfirst ab hab) hsmall
  let Cost := Cpack*R^4/(Lunit^2*N^2*|(Mat 2:ℝ)| *U)
  have htail (m : ℕ) (hm : 0 < m) :
      ((Gaps.filter (fun ab => m ≤ n ab)).card:ℝ) ≤ 2+Cost/(m:ℝ)^2 := by
    let Long := Gaps.filter (fun ab => m ≤ n ab)
    have hin ab (hab : ab∈Long) := (Finset.mem_filter.mp hab).1
    have hmR : (0:ℝ) < m := by exact_mod_cast hm
    have hlong ab (hab : ab∈Long) : Lunit*(m:ℝ) ≤ Lsource ab :=
      (mul_le_mul_of_nonneg_left
        (show (m:ℝ) ≤ n ab by exact_mod_cast (Finset.mem_filter.mp hab).2) hunit.le).trans
          (hblock ab (hin ab hab))
    have hp := physicalModelPhase_signed_height_long_reference_gap_packing
      Refs Long Mat S p x xref e r v s H d nSpan base l w y₀ ac bc k
      hσ hδ hF hT hM hN hR hU (mul_pos hunit hmR) hCres hD₀ hD hDupper hscale
      hA hW hP₂ hCcurv hBcut hBsize hMat hc hlarge32 hsep
      (fun ab hab => hgap ab (hin ab hab)) (fun ab hab => hd ab (hin ab hab))
      (fun ab hab => href ab (hin ab hab)) (fun ab hab => hheight ab (hin ab hab))
      (fun ab hab => hpt ab (hin ab hab)) (fun ab hab => hQband ab (hin ab hab))
      (fun ab hab => hx ab (hin ab hab)) (fun ab hab => hwindow ab (hin ab hab))
      (fun ab hab => hdisplacement ab (hin ab hab)) (fun ab hab => hspan ab (hin ab hab))
      (fun ab hab => hnsquare ab (hin ab hab)) (fun ab hab => hr ab (hin ab hab))
      (fun ab hab => hdet ab (hin ab hab)) (fun ab hab => hden ab (hin ab hab))
      (fun ab hab => hcoord ab (hin ab hab)) (fun ab hab => htransport ab (hin ab hab))
      (fun ab hab => hS ab (hin ab hab)) hlong
      (fun ab hab => hGcut ab (hin ab hab)) (fun ab hab => hbase ab (hin ab hab))
      (fun ab hab => hpoint ab (hin ab hab)) (fun ab hab => hsourceGap ab (hin ab hab))
      (fun ab hab => hy₀ ab (hin ab hab)) (fun ab hab => hy ab (hin ab hab))
      (fun ab hab => hcurv ab (hin ab hab)) (fun ab hab => hres ab (hin ab hab))
    exact hp.trans_eq (by dsimp only [Cost]; ring)
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

#print axioms physicalModelPhase_signed_height_reference_sample_mass
#print axioms finite_occupied_cubic_tail_sum
#print axioms quotient_block_mass
#print axioms two_term_first_cubic_cap
example
    {Kcoord : ℕ}
    (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) (Mat : Fin 4 → ℤ)
    (S : ℝ × ℝ → Finset ℕ) (p : ℝ × ℝ → ℕ → ℤ × ℤ)
    (x : ℝ × ℝ → ℕ → Fin 2 → ℝ)
    (xref e r v s H : ℝ × ℝ → Fin 2 → ℝ)
    (d nSpan base l w y₀ ac bc : ℝ × ℝ → ℝ) (k : ℝ × ℝ → Fin 17)
    {σ δ T M N R U Cres Q D Ccurv Bcut P₁ P₂ : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R)
    (hU : 0 < U) (hCres : 0 ≤ Cres)
    (hD₀ : 0 ≤ D) (hD : D ≤ 1/2) (hDupper : D ≤ Cres*Q/N)
    (hscale : T*N*R^2=M^3)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hP₂ : 0 < P₂) (hCcurv : 0 ≤ Ccurv) (hBcut : 0 < Bcut)
    (hBsize : ((2*Kcoord+1:ℕ):ℝ)*Ccurv*(σ*(σ+1)+1) ≤ Bcut)
    (hMat : Mat 0*Mat 3-Mat 1*Mat 2=1) (hc : Mat 2≠0)
    (hlarge : 64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a≠b → U/(4*R^2) ≤ |a-b|)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2))
    (hd : ∀ ab∈Gaps, 0 < d ab)
    (href : ∀ ab∈Gaps, ∀ i, xref ab i∈Ioo (1/2:ℝ) (W i-1/2))
    (hheight : ∀ ab∈Gaps, ∀ j∈S ab, |((p ab j).1:ℝ)| ≤ P₁ ∧ ((p ab j).2:ℝ) ≤ P₂)
    (hpt : ∀ ab∈Gaps, ∀ j∈S ab, 0 < (p ab j).2)
    (hQband : ∀ ab∈Gaps, ∀ j∈S ab, Q ≤ 2*(r ab 0*(p ab j).1+s ab 0*(p ab j).2))
    (hx : ∀ ab∈Gaps, ∀ j∈S ab, ∀ i, x ab j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ ab∈Gaps, ∀ j∈S ab,
      x ab j 0∈Icc (base ab+N*(j:ℝ)) (base ab+N*((j:ℝ)+1)))
    (hdisplacement : ∀ ab∈Gaps, ∀ j∈S ab, ∀ i, |x ab j i-xref ab i| ≤ H ab i)
    (hspan : ∀ ab∈Gaps, ∀ i, 2*H ab i+1 ≤ nSpan ab)
    (hnsquare : ∀ ab∈Gaps, (nSpan ab)^2 ≤ M*R)
    (hr : ∀ ab∈Gaps, ∀ i, r ab i≠0)
    (hdet : ∀ ab∈Gaps, ∀ i, v ab i*r ab i-e ab i*s ab i=1)
    (hden : ∀ ab∈Gaps, ∀ t∈Icc (l ab) (w ab), ∀ i,
      d ab ≤ r ab i*t+s ab i ∧ r ab i*t+s ab i ≤ 2*d ab)
    (hcoord : ∀ ab∈Gaps, |r ab 0| * max |l ab| |w ab| ≤ (Kcoord:ℝ)*d ab)
    (htransport : ∀ ab∈Gaps,
      e ab 1=(Mat 0:ℝ)*e ab 0+Mat 1*r ab 0 ∧
      v ab 1=(Mat 0:ℝ)*v ab 0+Mat 1*s ab 0 ∧
      r ab 1=(Mat 2:ℝ)*e ab 0+Mat 3*r ab 0 ∧
      s ab 1=(Mat 2:ℝ)*v ab 0+Mat 3*s ab 0) :
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let mu := fun ab i => iteratedDeriv 3 (f i) (round (xref ab i))/6
    let nu := fun ab i => iteratedDeriv 4 (f i) (round (xref ab i))/24
    let y := fun ab j => ((p ab j).1:ℝ)/(p ab j).2
    let g := fun ab => rationalPhase (mu ab 0) (r ab 0) (s ab 0) (mu ab 1) (r ab 1) (s ab 1)
    let h := fun ab => quarticPhase (mu ab 0) (nu ab 0) (r ab 0) (s ab 0)
      (mu ab 1) (nu ab 1) (r ab 1) (s ab 1)
    let phi := fun ab t => g ab t-h ab t
    let Gcoord := fun ab => minorArcCoordinate (mu ab 0) (r ab 0) (s ab 0)
    let Vcurv := fun ab => Ccurv*R^4/(N*(d ab)^3)
    let Z := fun ab => quarticCurvatureBoundaryRoots (mu ab 0) (nu ab 0) (r ab 0) (s ab 0)
      (mu ab 1) (nu ab 1) (r ab 1) (s ab 1) (Vcurv ab)
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let K := 4*Cres/κ
    let Gamma := Cphys/κ
    (∀ ab∈Gaps, 32*Blabels ≤ (S ab).card) →
    (∀ ab∈Gaps, |Gcoord ab (l ab)| ≤ |r ab 0| *N^2/(Bcut*R^2)) →
    (∀ ab∈Gaps, ∀ i, iteratedDeriv 2 (f i) (xref ab i)/2=e ab i/r ab i) →
    (∀ ab∈Gaps, ∀ j∈S ab, ∀ i, iteratedDeriv 2 (f i) (x ab j i)/2=
      (e ab i*(p ab j).1+v ab i*(p ab j).2)/(r ab i*(p ab j).1+s ab i*(p ab j).2)) →
    (∀ ab∈Gaps, ∀ j∈S ab, iteratedDeriv 2 (f 0) (x ab j 0)/2∈Ioo ab.1 ab.2) →
    (∀ ab∈Gaps, y₀ ab∈finiteBoundaryCell (Z ab) (l ab) (w ab) (k ab)) →
    (∀ ab∈Gaps, ∀ j∈S ab, y ab j∈finiteBoundaryCell (Z ab) (l ab) (w ab) (k ab)) →
    (∀ ab∈Gaps, |iteratedDeriv 2 (g ab) (y₀ ab)-iteratedDeriv 2 (h ab) (y₀ ab)| ≤ Vcurv ab) →
    (∀ ab∈Gaps, ∀ j∈S ab,
      |(ac ab-round (ac ab-deriv (phi ab) (y ab j)))*y ab j+
        (bc ab-round (bc ab-phi ab (y ab j)+y ab j*deriv (phi ab) (y ab j)))-
        g ab (y ab j)+h ab (y ab j)| ≤ D/(p ab j).2) →
    let Cthird := Gamma*(32*K+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let m0 := 32*Blabels
    let Lunit := 2*κ/Cphys
    (∑ ab∈Gaps, ((S ab).card:ℝ)) ≤
      4*(m0:ℝ)*((2*Cfirst*R^4/(Lunit^3*N^2)/|(Mat 2:ℝ)|)^((3:ℝ)⁻¹)+
        Cpack*R^4/(Lunit^2*N^2*|(Mat 2:ℝ)| *U)) :=
  HuxleyReferenceMassScratch.physicalModelPhase_signed_height_reference_sample_mass (Kcoord:=Kcoord) Refs Gaps Mat S p x xref e r v s H d nSpan base l w y₀ ac bc k (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (U:=U) (Cres:=Cres) (Q:=Q) (D:=D) (Ccurv:=Ccurv) (Bcut:=Bcut) (P₁:=P₁) (P₂:=P₂) (F:=F) (A:=A) (W:=W) hσ hδ hF hT hM hN hR hU hCres hD₀ hD hDupper hscale hA hW hP₂ hCcurv hBcut hBsize hMat hc hlarge hsep hgap hd href hheight hpt hQband hx hwindow hdisplacement hspan hnsquare hr hdet hden hcoord htransport


#print axioms reciprocal_square_prefix
#print axioms finite_occupied_tail_sum
private theorem resonance_matrix_reciprocal_sum
    (S : Finset (Fin 4 → ℤ)) {X Gamma : ℝ}
    (hX : 0 ≤ X) (hGamma : 0 ≤ Gamma)
    (hdet : ∀ M∈S, M 0*M 3-M 1*M 2=1)
    (hc : ∀ M∈S, M 2 ≠ 0 ∧ |(M 2:ℝ)| ≤ Gamma)
    (ha : ∀ M∈S, |(M 0:ℝ)| ≤ |(M 2:ℝ)| *X+2)
    (hd : ∀ M∈S, |(M 3:ℝ)| ≤ |(M 2:ℝ)| *X+2) :
    ∑ M∈S,1/|(M 2:ℝ)| ≤ (2*Gamma+1)*(2*X+5)^2 := by
  let Z := ∑ M∈S,1/|(M 2:ℝ)|
  let K := (2*Gamma+1)*(2*X+5)^2
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  by_contra! hbad
  have hgap : 0 < Z-K := sub_pos.mpr hbad
  let W := (K*Gamma+1)/(Z-K)
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hh := bourgain_resonance_matrix_weight_sum S hX hGamma hW hdet hc ha hd
  have he : (∑ M∈S,(1+W/|(M 2:ℝ)|))=(S.card:ℝ)+W*Z := by
    dsimp only [Z]
    simp only [Finset.sum_add_distrib,div_eq_mul_inv,←Finset.mul_sum,
      Finset.sum_const,nsmul_eq_mul,mul_one,one_mul]
  rw [he] at hh
  have hw : W*(Z-K)=K*Gamma+1 := by dsimp only [W]; field_simp
  change (S.card:ℝ)+W*Z ≤ K*(Gamma+W) at hh
  nlinarith only [hh,hw,(show (0:ℝ) ≤ S.card from Nat.cast_nonneg _)]

private theorem cubic_reciprocal_majorant {K c Gamma : ℝ}
    (hK : 0 ≤ K) (hc : 0 < c) (hcap : c ≤ Gamma) :
    (K/c)^((3:ℝ)⁻¹) ≤ K^((3:ℝ)⁻¹)*Gamma^((2:ℝ)/3)/c := by
  apply (le_div_iff₀ hc).mpr
  calc
    _ = K^((3:ℝ)⁻¹)*c^(1-(3:ℝ)⁻¹) := by
      rw [Real.div_rpow hK hc.le,Real.rpow_sub hc,Real.rpow_one]
      ring
    _ ≤ K^((3:ℝ)⁻¹)*Gamma^(1-(3:ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hc.le hcap (by norm_num))
        (Real.rpow_nonneg hK _)
    _ = _ := by norm_num

private theorem resonance_matrix_cubic_weight_sum
    (S : Finset (Fin 4 → ℤ)) {Vbound Gamma A K B : ℝ}
    (hV : 0 ≤ Vbound) (hGamma : 0 ≤ Gamma)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hdet : ∀ Mat∈S, Mat 0*Mat 3-Mat 1*Mat 2=1)
    (hc : ∀ Mat∈S, Mat 2 ≠ 0 ∧ |(Mat 2:ℝ)| ≤ Gamma)
    (ha : ∀ Mat∈S, |(Mat 0:ℝ)| ≤ |(Mat 2:ℝ)| *Vbound+2)
    (hd : ∀ Mat∈S, |(Mat 3:ℝ)| ≤ |(Mat 2:ℝ)| *Vbound+2) :
    ∑ Mat∈S,(A*(K/|(Mat 2:ℝ)|)^((3:ℝ)⁻¹)+B/|(Mat 2:ℝ)|) ≤
      ((2*Gamma+1)*(2*Vbound+5)^2)*(A*K^((3:ℝ)⁻¹)*Gamma^((2:ℝ)/3)+B) := by
  have hw := resonance_matrix_reciprocal_sum S hV hGamma hdet hc ha hd
  have hp Mat (hMat : Mat∈S) : 0 < |(Mat 2:ℝ)| :=
    abs_pos.mpr (by exact_mod_cast (hc Mat hMat).1)
  let C := A*K^((3:ℝ)⁻¹)*Gamma^((2:ℝ)/3)+B
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact add_nonneg (mul_nonneg (mul_nonneg hA (Real.rpow_nonneg hK _))
      (Real.rpow_nonneg hGamma _)) hB
  calc
    _ ≤ ∑ Mat∈S,C*(1/|(Mat 2:ℝ)|) := by
      apply Finset.sum_le_sum
      intro Mat hMat
      have hh := mul_le_mul_of_nonneg_left
        (cubic_reciprocal_majorant hK (hp Mat hMat) (hc Mat hMat).2) hA
      dsimp only [C]
      calc
        _ ≤ A*(K^((3:ℝ)⁻¹)*Gamma^((2:ℝ)/3)/|(Mat 2:ℝ)|)+B/|(Mat 2:ℝ)| :=
          add_le_add hh le_rfl
        _ = _ := by ring
    _ = C*(∑ Mat∈S,1/|(Mat 2:ℝ)|) := (Finset.mul_sum S _ _).symm
    _ ≤ C*((2*Gamma+1)*(2*Vbound+5)^2) := mul_le_mul_of_nonneg_left hw hC
    _ = _ := by dsimp only [C]; ring

#print axioms cubic_reciprocal_majorant
#print axioms resonance_matrix_cubic_weight_sum
#print axioms resonance_matrix_reciprocal_sum
end HuxleyReferenceMassScratch
