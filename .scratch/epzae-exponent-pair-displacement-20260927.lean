import TaoTrudgianYang2025.SquareProductCount
noncomputable section
open Set MeasureTheory GafniTao Expdb
open scoped BigOperators FourierTransform Topology ContDiff
namespace TaoTrudgianYang2025.CubicJointCount


theorem original_joint_level_displacement_count
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 2 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (T N d D a b R B lam δ₁ δ₂ W : ℝ)
          (K : ℤ) (S : Finset (ℤ × ℕ)),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 2 ≤ d → 0 < D → 0 < R → 0 ≤ B → 0 < lam →
          N < a-R → b+R+2*D < 2*N →
          δ₂ ≤ lam*d*R/2 → δ₁+2*B*D*R^2 ≤ W/2 →
          0 < K → 2*(K:ℝ)*N^2/(σ*T) ≤ κ₀ → 0 < W → W ≤ 1/2 →
          let f := fun z => T*F (z/N)
          (∀ t∈Icc (a-R) (b+R+2*D),
            -B ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam) →
          (∀ p∈S, (p.1:ℝ)∈Icc a b ∧ (p.2:ℝ)∈Icc d (2*D)) →
          (∀ p∈S, |(iteratedDeriv 2 f ((p.1:ℝ)+(p.2:ℝ))-
            iteratedDeriv 2 f p.1)/2-(K:ℝ)| ≤ δ₂) →
          (∀ p∈S, ∃ e : ℤ, |iteratedDeriv 1 f ((p.1:ℝ)+(p.2:ℝ))-
            iteratedDeriv 1 f p.1-(e:ℝ)| ≤ δ₁) →
            ((S.image Prod.snd).card:ℝ) ≤
              C*(W*D+(T/N^2)^(k₀+ε)*D^(l₀+ε)*W^(-(k₀+ε))+N^2/T) := by
  classical
  obtain ⟨δ,κ₀,hδ,hκ₀,Q,hQ,C,hC,hcount⟩ :=
    original_second_level_near_curve_count hσ hpair hε hp
  refine ⟨δ,κ₀,hδ,hκ₀,Q,hQ,C,hC,?_⟩
  intro F T N d D a b R B lam δ₁ δ₂ W K S hF hT hN hd hDpos hR hB hlam
    hleft hright hbuffer hwidth hK hκle hW hWhalf f hfour hbox hsecond hfirst
  have hdpos : 0 < d := by linarith
  let J := S.image Prod.snd
  have hmem (q : ℕ) (hq : q∈J) : d ≤ (q:ℝ) ∧ (q:ℝ) ≤ 2*D := by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    exact (hbox p hp).2
  have hnorm (t : ℝ) (ht : t∈Icc (a-R) (b+R+2*D)) :
      t/N∈Ioo (1:ℝ) 2 := by
    constructor
    · apply (one_lt_div hN).mpr
      linarith [ht.1]
    · apply (div_lt_iff₀ hN).mpr
      linarith [ht.2]
  have hf (t : ℝ) (ht : t∈Icc (a-R) (b+R+2*D)) : ContDiffAt ℝ 4 f t := by
    have hc := (approximateModelPhase_contDiffAt hF (hnorm t ht)).comp t
      (show ContDiffAt ℝ ∞ (fun z : ℝ => z/N) t by fun_prop)
    exact (contDiffAt_const.mul hc).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4)
  have hex (q : ℕ) (hq : q∈J) :
      ∃ x : ℝ, x/N∈Ioo (1:ℝ) 2 ∧ (x+(q:ℝ))/N∈Ioo (1:ℝ) 2 ∧
        (iteratedDeriv 2 f (x+(q:ℝ))-iteratedDeriv 2 f x)/2=(K:ℝ) ∧
        ∃ e : ℤ, |iteratedDeriv 1 f (x+(q:ℝ))-iteratedDeriv 1 f x-
          2*(K:ℝ)*x-(e:ℝ)| ≤ W/2 := by
    obtain ⟨p,hps,hpq⟩ := Finset.mem_image.mp hq
    have hpos : 0 < (q:ℝ) := hdpos.trans_le (hmem q hq).1
    have hpab : (p.1:ℝ)∈Icc a b := (hbox p hps).1
    have hsub : Icc ((p.1:ℝ)-R) ((p.1:ℝ)+R+(q:ℝ)) ⊆ Icc (a-R) (b+R+2*D) := by
      intro t ht
      constructor <;> linarith [ht.1,ht.2,hpab.1,hpab.2,(hmem q hq).2]
    have hbudget : δ₂ ≤ lam*(q:ℝ)*R/2 := hbuffer.trans (by gcongr; exact (hmem q hq).1)
    have hnear₂ : |(iteratedDeriv 2 f ((p.1:ℝ)+(q:ℝ))-iteratedDeriv 2 f p.1)/2-(K:ℝ)| ≤ δ₂ := by
      simpa only [hpq] using hsecond p hps
    obtain ⟨x,hx,hlevel,_hdist⟩ := cubic_exact_second_difference_level
      f hpos hR hbudget (fun t ht => hf t (hsub ht))
      (fun t ht => hfour t (hsub ht)) hnear₂
    obtain ⟨e,he⟩ := hfirst p hps
    rw [hpq] at he
    have hnear := cubic_stationary_curve_near_integer
      f p.1 K e hpos hlam hR.le hx (fun t ht => hf t (hsub ht))
      (fun t ht => hfour t (hsub ht)) hlevel he
    have hxx : x∈Icc (a-R) (b+R+2*D) := hsub ⟨hx.1,by linarith [hx.2]⟩
    have hxxq : x+(q:ℝ)∈Icc (a-R) (b+R+2*D) :=
      hsub ⟨by linarith [hx.1],by linarith [hx.2]⟩
    refine ⟨x,hnorm x hxx,hnorm (x+q) hxxq,hlevel,e-2*K*p.1,?_⟩
    exact hnear.trans ((show δ₁+B*(q:ℝ)*R^2 ≤ δ₁+2*B*D*R^2 by
      nlinarith [mul_le_mul_of_nonneg_left (hmem q hq).2
        (mul_nonneg hB (sq_nonneg R))]).trans hwidth)
  let x := fun q => if hq : q∈J then Classical.choose (hex q hq) else 0
  have hx (q : ℕ) (hq : q∈J) :
      x q/N∈Ioo (1:ℝ) 2 ∧ (x q+(q:ℝ))/N∈Ioo (1:ℝ) 2 ∧
        (iteratedDeriv 2 f (x q+(q:ℝ))-iteratedDeriv 2 f (x q))/2=(K:ℝ) ∧
        ∃ e : ℤ, |iteratedDeriv 1 f (x q+(q:ℝ))-iteratedDeriv 1 f (x q)-
          2*(K:ℝ)*x q-(e:ℝ)| ≤ W/2 := by
    simp only [x,dif_pos hq]
    exact Classical.choose_spec (hex q hq)
  have hcountJ := hcount F T N D K J x hF hT hN hDpos hK hκle
    (fun q hq => (hx q hq).1) (fun q hq => (hx q hq).2.1)
    (fun q hq => ⟨hd.trans (hmem q hq).1,(hmem q hq).2⟩)
    (fun q hq => (hx q hq).2.2.1) W hW hWhalf (fun q hq => (hx q hq).2.2.2)
  exact hcountJ

/-- The original-model near-curve estimate applied to a labelled block source.
No cardinality estimate is an input; both the displacement image and its
source multiplicities are derived. -/
theorem original_model_block_source_pair_count
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 2 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ {ι : Type*} [DecidableEq ι] (S : Finset ι) (V : Finset (ι × ι))
          (center block : ι → ℤ) (H Bmul : ℕ) (s K : ℤ)
          (F : ℝ → ℝ) (T N d D a b R B lam δ₁ δ₂ W : ℝ),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 2 ≤ d → 0 < D → 0 < R → 0 ≤ B →
          0 < lam → 0 ≤ δ₂ → 0 < H →
          N < a-R → b+R+2*D < 2*N →
          δ₂ ≤ lam*d*R/2 → δ₁+2*B*D*R^2 ≤ W/2 →
          0 < K → 2*(K:ℝ)*N^2/(σ*T) ≤ κ₀ → 0 < W → W ≤ 1/2 →
          (∀ i∈S, (H:ℤ) ≤ s+(H:ℤ)*block i-center i ∧
            s+(H:ℤ)*block i-center i ≤ 3*(H:ℤ)) →
          (∀ j : ℤ, (S.filter (fun i => block i=j)).card ≤ Bmul) →
          (∀ i∈S, (center i:ℝ)∈Icc a b) →
          V ⊆ S ×ˢ S →
          (∀ p∈V, (center p.2:ℝ)-center p.1∈Icc d (2*D)) →
          let f := fun z => T*F (z/N)
          (∀ t∈Icc (a-R) (b+R+2*D),
            -B ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam) →
          (∀ p∈V, |(iteratedDeriv 2 f (center p.2)-
            iteratedDeriv 2 f (center p.1))/2-(K:ℝ)| ≤ δ₂) →
          (∀ p∈V, ∃ e : ℤ, |iteratedDeriv 1 f (center p.2)-
            iteratedDeriv 1 f (center p.1)-(e:ℝ)| ≤ δ₁) →
            (V.card:ℝ) ≤ (3*(Bmul:ℝ)^2*(3+8*δ₂/(lam*d*H)))*
              (C*(W*D+(T/N^2)^(k₀+ε)*D^(l₀+ε)*W^(-(k₀+ε))+N^2/T)) := by
  classical
  obtain ⟨δ,κ₀,hδ,hκ₀,Q,hQ,C,hC,hcount⟩ :=
    original_joint_level_displacement_count hσ hpair hε hp
  refine ⟨δ,κ₀,hδ,hκ₀,Q,hQ,C,hC,?_⟩
  intro ι _ S V center block H Bmul s K F T N d D a b R B lam δ₁ δ₂ W
    hF hT hN hd hD hR hB hlam hδ₂ hH hleft hright hbuffer hwidth hK hκle hW hWhalf
    hspan hmul hcenter hVS hdisp f hfour hsecond hfirst
  have hdp : 0 < d := by linarith
  have hHr : (0:ℝ) < H := by exact_mod_cast hH
  let n := fun p : ι × ι => (center p.2-center p.1).toNat
  let E := V.image (fun p => (center p.1,n p))
  let J := E.image Prod.snd
  have hn p (hp : p∈V) : (n p:ℝ)=(center p.2:ℝ)-center p.1 := by
    have hnn : 0 ≤ center p.2-center p.1 := by
      exact_mod_cast (hdp.le.trans (hdisp p hp).1)
    have he := Int.toNat_of_nonneg hnn
    exact_mod_cast he
  have hpoints p (hp : p∈V) : (center p.1:ℝ)+(n p:ℝ)=center p.2 := by
    rw [hn p hp]
    ring
  have hcountJ : (J.card:ℝ) ≤
      C*(W*D+(T/N^2)^(k₀+ε)*D^(l₀+ε)*W^(-(k₀+ε))+N^2/T) := by
    apply hcount F T N d D a b R B lam δ₁ δ₂ W K E hF hT hN hd hD hR hB hlam
      hleft hright hbuffer hwidth hK hκle hW hWhalf hfour
    · intro p hp
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hp
      exact ⟨hcenter _ (Finset.mem_product.mp (hVS hv)).1, by
        simpa only [hn v hv] using hdisp v hv⟩
    · intro p hp
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hp
      simpa only [hpoints v hv] using hsecond v hv
    · intro p hp
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hp
      simpa only [hpoints v hv] using hfirst v hv
  have hf t (ht : t∈Ioo (a-R) (b+R+2*D)) : ContDiffAt ℝ 4 f t := by
    have hnrm : t/N∈Ioo (1:ℝ) 2 := by
      constructor
      · apply (one_lt_div hN).mpr
        linarith [ht.1]
      · apply (div_lt_iff₀ hN).mpr
        linarith [ht.2]
    have hc := (approximateModelPhase_contDiffAt hF hnrm).comp t
      (show ContDiffAt ℝ ∞ (fun z : ℝ => z/N) t by fun_prop)
    exact (contDiffAt_const.mul hc).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4)
  have hcent i (hi : i∈S) : (center i:ℝ)∈Ioo (a-R) (b+R+2*D) := by
    constructor <;> linarith [(hcenter i hi).1,(hcenter i hi).2]
  let M := 3*(Bmul:ℝ)^2*(3+8*δ₂/(lam*d*H))
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hfiber q : ((V.filter (fun p => n p=q)).card:ℝ) ≤ M := by
    let Vq := V.filter (fun p => n p=q)
    by_cases hvq : Vq.Nonempty
    · obtain ⟨v,hv⟩ := hvq
      obtain ⟨hv,he⟩ := Finset.mem_filter.mp hv
      have hqd : d ≤ (q:ℝ) := by rw [←he,hn v hv]; exact (hdisp v hv).1
      have hqp : (0:ℝ)<q := hdp.trans_le hqd
      have hb := fixed_displacement_source_pair_fibers S Vq center block H Bmul s f
        hH hlam hqp hδ₂ hspan hmul hf
        (fun t ht => (hfour t ⟨ht.1.le,ht.2.le⟩).2) hcent
        (fun p hp => hVS (Finset.mem_filter.mp hp).1)
        (fun p hp => by
          rw [←hn p (Finset.mem_filter.mp hp).1,(Finset.mem_filter.mp hp).2])
        (fun p hp => hsecond p (Finset.mem_filter.mp hp).1)
      have hfrac : 8*δ₂/(lam*(q:ℝ)*H) ≤ 8*δ₂/(lam*d*H) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqd hlam.le) hHr.le)
      exact hb.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hfrac) (by positivity))
    · change (Vq.card:ℝ) ≤ M
      rw [Finset.not_nonempty_iff_eq_empty.mp hvq,Finset.card_empty,Nat.cast_zero]
      exact hM
  have hmap p (hp : p∈V) : n p∈J :=
    Finset.mem_image.mpr ⟨(center p.1,n p),Finset.mem_image_of_mem _ hp,rfl⟩
  have hc : (V.card:ℝ)=∑ q∈J,((V.filter (fun p => n p=q)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmap
  calc
    _ = _ := hc
    _ ≤ ∑ _q∈J,M := Finset.sum_le_sum (fun q _ => hfiber q)
    _ = M*J.card := by simp [mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left hcountJ hM

/-- A positive curvature shift in the actual model, with the rounded source
multiplicity retained and all derivative assumptions derived from the model. -/
theorem original_model_rounded_shift_count
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 3 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ {ι : Type*} [DecidableEq ι] (S : Finset ι) (V : Finset (ι × ι))
          (center block : ι → ℤ) (z : ι → ℝ) (H Bmul : ℕ) (s K : ℤ)
          (F : ℝ → ℝ) (T N a b R δ₁ W : ℝ),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 0 < R → 0 < H → 0 < K →
          let L := modelPhaseJetLower σ 2*T/N^3
          let U := (modelPhaseJetCoefficient σ 2+1)*T/N^3
          let lam := modelPhaseJetLower σ 3*T/N^4
          let B := (modelPhaseJetCoefficient σ 3+1)*T/N^4
          let d := (K:ℝ)/(6*U)
          let D := (K:ℝ)/L+1
          12*U ≤ 1 → N < a-R → b+R+2*D < 2*N →
          3*U ≤ lam*d*R/2 → δ₁+2*B*D*R^2 ≤ W/2 →
          2*(K:ℝ)*N^2/(σ*T) ≤ κ₀ → 0 < W → W ≤ 1/2 →
          (∀ i∈S, (H:ℤ) ≤ s+(H:ℤ)*block i-center i ∧
            s+(H:ℤ)*block i-center i ≤ 3*(H:ℤ)) →
          (∀ j : ℤ, (S.filter (fun i => block i=j)).card ≤ Bmul) →
          (∀ i∈S, (center i:ℝ)∈Icc a b) →
          (∀ i∈S, z i∈Ioo N (2*N)) →
          (∀ i∈S, |(center i:ℝ)-z i| ≤ 1/2) →
          V ⊆ S ×ˢ S →
          let f := fun t => T*F (t/N)
          (∀ p∈V, iteratedDeriv 2 f (z p.2)/2-
            iteratedDeriv 2 f (z p.1)/2=(K:ℝ)) →
          (∀ p∈V, ∃ e : ℤ, |iteratedDeriv 1 f (center p.2)-
            iteratedDeriv 1 f (center p.1)-(e:ℝ)| ≤ δ₁) →
            (V.card:ℝ) ≤ (3*(Bmul:ℝ)^2*(3+144*U^2/(lam*(K:ℝ)*H)))*
              (C*(W*D+(T/N^2)^(k₀+ε)*D^(l₀+ε)*W^(-(k₀+ε))+N^2/T)) := by
  classical
  obtain ⟨δ₀,κ₀,hδ₀,hκ₀,Q₀,hQ₀,C,hC,hcount⟩ :=
    original_model_block_source_pair_count hσ hpair hε hp
  obtain ⟨δd,hδd,hdata⟩ := model_displacement_derivative_data hσ
  let δ := min δ₀ δd
  let Q := max Q₀ 3
  refine ⟨δ,κ₀,lt_min hδ₀ hδd,hκ₀,Q,le_max_right _ _,C,hC,?_⟩
  intro ι _ S V center block z H Bmul s K F T N a b R δ₁ W
    hF hT hN hR hH hK L U lam B d D hUsmall hleft hright hbuffer hwidth
    hκle hW hWhalf hspan hmul hcenter hz hround hVS f hlevel hfirst
  have hF₀ := approximateModelPhase_mono hF (le_max_left _ _) (min_le_left _ _)
  have hFd := approximateModelPhase_mono hF (le_max_right _ _) (min_le_right _ _)
  obtain ⟨hreg,hthree,hfour,_⟩ := hdata F T N hT hN hFd
  have hlam : 0 < lam := by dsimp only [lam]; positivity [modelPhaseJetLower_pos hσ 3]
  have hL : 0 < L := by dsimp only [L]; positivity [modelPhaseJetLower_pos hσ 2]
  have hU : 0 < U := by dsimp only [U]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  have hB : 0 ≤ B := by dsimp only [B]; positivity [modelPhaseJetCoefficient_pos hσ 3]
  have hKr : (1:ℝ) ≤ K := by exact_mod_cast (show (1:ℤ) ≤ K by omega)
  have hKp : (0:ℝ) < K := zero_lt_one.trans_le hKr
  have hd : 2 ≤ d := by
    apply (le_div_iff₀ (by positivity : 0 < 6*U)).mpr
    linarith
  have hD : 0 < D := by dsimp only [D]; positivity
  have hsegment : Icc (a-R) (b+R+2*D) ⊆ Ioo N (2*N) := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  have hcent i (hi : i∈S) : (center i:ℝ)∈Ioo N (2*N) := by
    apply hsegment
    constructor <;> linarith [(hcenter i hi).1,(hcenter i hi).2]
  have hthree' t (ht : t∈Ioo N (2*N)) :
      L ≤ iteratedDeriv 3 f t ∧ iteratedDeriv 3 f t ≤ 6*U := by
    have hh := hthree t ht
    exact ⟨hh.1,by linarith [hh.2]⟩
  have hdisp p (hp : p∈V) : (center p.2:ℝ)-center p.1∈Icc d (2*D) := by
    have hpp := Finset.mem_product.mp (hVS hp)
    have hb := rounded_positive_curvature_shift_bounds f hL hU
      (by linarith only [hUsmall,hKr,hU] : 6*U ≤ (K:ℝ))
      (fun t ht => (hreg t ht).of_le (by norm_num)) hthree'
      (hz _ hpp.1) (hz _ hpp.2) (hround _ hpp.1) (hround _ hpp.2) (hlevel p hp)
    refine ⟨hb.1,?_⟩
    dsimp only [D]
    have hbhi : (center p.2:ℝ)-center p.1 ≤ 2*((K:ℝ)/L)+1 := by
      simpa only [mul_div_assoc] using hb.2
    linarith only [hbhi]
  have hsecond p (hp : p∈V) :
      |(iteratedDeriv 2 f (center p.2)-iteratedDeriv 2 f (center p.1))/2-(K:ℝ)| ≤ 3*U := by
    have hpp := Finset.mem_product.mp (hVS hp)
    have hseg : uIcc (z p.1) (center p.1:ℝ) ∪ uIcc (z p.2) (center p.2:ℝ) ⊆ Ioo N (2*N) :=
      union_subset ((convex_Ioo N (2*N)).ordConnected.uIcc_subset (hz _ hpp.1) (hcent _ hpp.1))
        ((convex_Ioo N (2*N)).ordConnected.uIcc_subset (hz _ hpp.2) (hcent _ hpp.2))
    apply rounded_curvature_difference_error f
      (fun t ht => (hreg t (hseg ht)).of_le (by norm_num)) ?_
      (hround _ hpp.1) (hround _ hpp.2) (hlevel p hp)
    intro t ht
    rw [abs_of_pos (hL.trans_le (hthree' t (hseg ht)).1)]
    exact (hthree' t (hseg ht)).2
  have hb := hcount S V center block H Bmul s K F T N d D a b R B lam δ₁ (3*U) W
    hF₀ hT hN hd hD hR hB hlam (by positivity) hH hleft hright hbuffer hwidth
    hK hκle hW hWhalf hspan hmul hcenter hVS hdisp
    (fun t ht => hfour t (hsegment ht)) hsecond hfirst
  have he : 8*(3*U)/(lam*d*H)=144*U^2/(lam*(K:ℝ)*H) := by
    dsimp only [d]
    field_simp
    ring
  rwa [he] at hb

/-- A free Fourier width absorbs the rounded-center lifting error uniformly
over positive curvature shifts, without changing the displacement multiplicity. -/
theorem rounded_shift_free_width
    {L U lam B K η w : ℝ}
    (hL : 0 < L) (hU : 0 < U) (hlam : 0 < lam) (hB : 0 ≤ B)
    (hK : 1 ≤ K) (hLK : L ≤ K) (hη : 0 ≤ η) (hw : 0 < w) (hwhalf : w ≤ 1/2)
    (hsmall : 2*η+10368*B*U^4/(lam^2*L) ≤ 1/2) :
    let d := K/(6*U)
    let D := K/L+1
    let R := 36*U^2/(lam*K)
    let W := max (2*η+4*B*D*R^2) w
    0 < R ∧ 0 < W ∧ W ≤ 1/2 ∧
      3*U=lam*d*R/2 ∧ η+2*B*D*R^2 ≤ W/2 ∧
      W*D ≤ (2*η+w)*D+20736*B*U^4/(lam^2*L^2) ∧
      ∀ p : ℝ, 0 ≤ p → W^(-p) ≤ w^(-p) := by
  intro d D R W
  have hKp : 0 < K := zero_lt_one.trans_le hK
  have hD : 0 < D := by dsimp only [D]; positivity
  have hR : 0 < R := by dsimp only [R]; positivity
  have hDup : D ≤ 2*K/L := by
    have h1 : 1 ≤ K/L := (one_le_div hL).mpr hLK
    dsimp only [D]
    rw [mul_div_assoc]
    linarith
  have hraw : 4*B*D*R^2 ≤ 10368*B*U^4/(lam^2*L) := by
    calc
      _ ≤ 4*B*(2*K/L)*R^2 := by gcongr
      _ = 10368*B*U^4/(lam^2*L*K) := by dsimp only [R]; field_simp; ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (by nlinarith [mul_le_mul_of_nonneg_left hK (show 0 ≤ lam^2*L by positivity)])
  have hW : 0 < W := hw.trans_le (le_max_right _ _)
  have hwidth : η+2*B*D*R^2 ≤ W/2 := by
    have hh : 2*η+4*B*D*R^2 ≤ W := le_max_left _ _
    linarith
  have hbudget : 4*B*D^2*R^2 ≤ 20736*B*U^4/(lam^2*L^2) := by
    calc
      _ ≤ 4*B*(2*K/L)^2*R^2 := by gcongr
      _ = _ := by dsimp only [R]; field_simp; ring
  have hWD : W*D ≤ (2*η+w)*D+20736*B*U^4/(lam^2*L^2) := by
    have hsum : W ≤ 2*η+4*B*D*R^2+w := by
      apply max_le
      · linarith
      · have hh : 0 ≤ 2*η+4*B*D*R^2 := by positivity
        linarith
    calc
      _ ≤ (2*η+4*B*D*R^2+w)*D := mul_le_mul_of_nonneg_right hsum hD.le
      _ = (2*η+w)*D+4*B*D^2*R^2 := by ring
      _ ≤ _ := add_le_add le_rfl hbudget
  refine ⟨hR,hW,max_le (by linarith only [hraw,hsmall]) hwhalf,?_,hwidth,hWD,?_⟩
  · dsimp only [d,R]
    field_simp
    ring
  · intro p hp
    exact Real.rpow_le_rpow_of_nonpos hw (le_max_right _ _) (neg_nonpos.mpr hp)

/-- Uniform positive-shift estimate. The Fourier width is chosen inside the
proof, including the rounded-center lifting error; the shift weight is retained
for the subsequent harmonic sum. -/
theorem original_model_uniform_positive_shift_count
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 3 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ {ι : Type*} [DecidableEq ι] (S : Finset ι) (V : Finset (ι × ι))
          (center block : ι → ℤ) (z : ι → ℝ) (H Bmul : ℕ) (s K : ℤ)
          (F : ℝ → ℝ) (T N a b Kmax η w : ℝ),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 0 < H → 0 < K → (K:ℝ) ≤ Kmax →
          0 ≤ η → 0 < w → w ≤ 1/2 →
          let L := modelPhaseJetLower σ 2*T/N^3
          let U := (modelPhaseJetCoefficient σ 2+1)*T/N^3
          let lam := modelPhaseJetLower σ 3*T/N^4
          let B := (modelPhaseJetCoefficient σ 3+1)*T/N^4
          let Rmax := 36*U^2/lam
          let Dmax := Kmax/L+1
          12*U ≤ 1 → L ≤ 1 →
          2*η+10368*B*U^4/(lam^2*L) ≤ 1/2 →
          N < a-Rmax → b+Rmax+2*Dmax < 2*N →
          2*Kmax*N^2/(σ*T) ≤ κ₀ →
          (∀ i∈S, (H:ℤ) ≤ s+(H:ℤ)*block i-center i ∧
            s+(H:ℤ)*block i-center i ≤ 3*(H:ℤ)) →
          (∀ j : ℤ, (S.filter (fun i => block i=j)).card ≤ Bmul) →
          (∀ i∈S, (center i:ℝ)∈Icc a b) →
          (∀ i∈S, z i∈Ioo N (2*N)) →
          (∀ i∈S, |(center i:ℝ)-z i| ≤ 1/2) →
          V ⊆ S ×ˢ S →
          let f := fun t => T*F (t/N)
          (∀ p∈V, iteratedDeriv 2 f (z p.2)/2-
            iteratedDeriv 2 f (z p.1)/2=(K:ℝ)) →
          (∀ p∈V, ∃ e : ℤ, |iteratedDeriv 1 f (center p.2)-
            iteratedDeriv 1 f (center p.1)-(e:ℝ)| ≤ η) →
            (V.card:ℝ) ≤ (3*(Bmul:ℝ)^2*(3+144*U^2/(lam*(K:ℝ)*H)))*
              (C*((2*η+w)*Dmax+20736*B*U^4/(lam^2*L^2)+
                (T/N^2)^(k₀+ε)*Dmax^(l₀+ε)*w^(-(k₀+ε))+N^2/T)) := by
  classical
  obtain ⟨δ,κ₀,hδ,hκ₀,Q,hQ,C,hC,hcount⟩ :=
    original_model_rounded_shift_count hσ hpair hε hp
  refine ⟨δ,κ₀,hδ,hκ₀,Q,hQ,C,hC,?_⟩
  intro ι _ S V center block z H Bmul s K F T N a b Kmax η w
    hF hT hN hH hK hKmax hη hw hwhalf L U lam B Rmax Dmax hUsmall hLsmall
    hsmall hleft hright hκle hspan hmul hcenter hz hround hVS f hlevel hfirst
  have hlam : 0 < lam := by dsimp only [lam]; positivity [modelPhaseJetLower_pos hσ 3]
  have hL : 0 < L := by dsimp only [L]; positivity [modelPhaseJetLower_pos hσ 2]
  have hU : 0 < U := by dsimp only [U]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  have hB : 0 ≤ B := by dsimp only [B]; positivity [modelPhaseJetCoefficient_pos hσ 3]
  have hKr : (1:ℝ) ≤ K := by exact_mod_cast (show (1:ℤ) ≤ K by omega)
  have hKp : (0:ℝ) < K := zero_lt_one.trans_le hKr
  let R := 36*U^2/(lam*(K:ℝ))
  let D := (K:ℝ)/L+1
  let W := max (2*η+4*B*D*R^2) w
  have hwidth := rounded_shift_free_width hL hU hlam hB hKr (hLsmall.trans hKr)
    hη hw hwhalf hsmall
  change 0 < R ∧ 0 < W ∧ W ≤ 1/2 ∧
    3*U=lam*((K:ℝ)/(6*U))*R/2 ∧ η+2*B*D*R^2 ≤ W/2 ∧
    W*D ≤ (2*η+w)*D+20736*B*U^4/(lam^2*L^2) ∧
    ∀ p : ℝ, 0 ≤ p → W^(-p) ≤ w^(-p) at hwidth
  have hRmax : R ≤ Rmax := by
    apply div_le_div_of_nonneg_left (by positivity) hlam
    nlinarith only [mul_le_mul_of_nonneg_left hKr hlam.le]
  have hDD : D ≤ Dmax := add_le_add
    (div_le_div_of_nonneg_right hKmax hL.le) le_rfl
  have hDp : 0 < D := by dsimp only [D]; positivity
  have hDmax : 0 < Dmax := hDp.trans_le hDD
  have hκ : 2*(K:ℝ)*N^2/(σ*T) ≤ κ₀ := le_trans
    (by gcongr) hκle
  have hb := hcount S V center block z H Bmul s K F T N a b R η W
    hF hT hN hwidth.1 hH hK hUsmall
    (by linarith only [hleft,hRmax])
    (by change b+R+2*D < 2*N; linarith only [hright,hRmax,hDD])
    hwidth.2.2.2.1.le hwidth.2.2.2.2.1 hκ hwidth.2.1 hwidth.2.2.1
    hspan hmul hcenter hz hround hVS hlevel hfirst
  have hp0 : 0 ≤ k₀+ε := by linarith [hpair.inTriangle.1]
  have hl0 : 0 ≤ l₀+ε := by linarith [hpair.inTriangle.2.2.1]
  have hfirstTerm : W*D ≤ (2*η+w)*Dmax+20736*B*U^4/(lam^2*L^2) :=
    hwidth.2.2.2.2.2.1.trans (add_le_add
      (mul_le_mul_of_nonneg_left hDD (by positivity)) le_rfl)
  have hosc : (T/N^2)^(k₀+ε)*D^(l₀+ε)*W^(-(k₀+ε)) ≤
      (T/N^2)^(k₀+ε)*Dmax^(l₀+ε)*w^(-(k₀+ε)) :=
    mul_le_mul
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hDp.le hDD hl0) (by positivity))
      (hwidth.2.2.2.2.2.2 _ hp0) (by positivity) (by positivity)
  exact hb.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hfirstTerm hosc) le_rfl)
      (zero_le_one.trans hC)) (by positivity))

/-- Both signs and the zero curvature shift for the actual model source.
The positive fibers use the analytic exponent-pair near-curve estimate. -/
theorem original_model_all_shifts_count
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 3 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ {ι : Type*} [DecidableEq ι] (S : Finset ι) (R : Finset (ι × ι))
          (center block : ι → ℤ) (z : ι → ℝ) (H Bmul Kcut : ℕ) (s : ℤ)
          (F : ℝ → ℝ) (T N a b η w : ℝ),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 0 < H → 0 ≤ η → 0 < w → w ≤ 1/2 →
          let L := modelPhaseJetLower σ 2*T/N^3
          let U := (modelPhaseJetCoefficient σ 2+1)*T/N^3
          let lam := modelPhaseJetLower σ 3*T/N^4
          let B := (modelPhaseJetCoefficient σ 3+1)*T/N^4
          let Rmax := 36*U^2/lam
          let Dmax := (Kcut:ℝ)/L+1
          12*U ≤ 1 → L ≤ 1 →
          2*η+10368*B*U^4/(lam^2*L) ≤ 1/2 →
          N < a-Rmax → b+Rmax+2*Dmax < 2*N →
          2*(Kcut:ℝ)*N^2/(σ*T) ≤ κ₀ →
          (∀ i∈S, (H:ℤ) ≤ s+(H:ℤ)*block i-center i ∧
            s+(H:ℤ)*block i-center i ≤ 3*(H:ℤ)) →
          (∀ j : ℤ, (S.filter (fun i => block i=j)).card ≤ Bmul) →
          (∀ i∈S, (center i:ℝ)∈Icc a b) →
          (∀ i∈S, z i∈Ioo N (2*N)) →
          (∀ i∈S, |(center i:ℝ)-z i| ≤ 1/2) →
          R ⊆ S ×ˢ S → (∀ p∈R, p.swap∈R) →
          let f := fun t => T*F (t/N)
          (∀ p∈R, ∃ k : ℤ, iteratedDeriv 2 f (z p.2)/2-
            iteratedDeriv 2 f (z p.1)/2=(k:ℝ) ∧ |(k:ℝ)| ≤ Kcut) →
          (∀ p∈R, ∃ e : ℤ, |iteratedDeriv 1 f (center p.2)-
            iteratedDeriv 1 f (center p.1)-(e:ℝ)| ≤ η) →
          let Count := C*((2*η+w)*Dmax+20736*B*U^4/(lam^2*L^2)+
                (T/N^2)^(k₀+ε)*Dmax^(l₀+ε)*w^(-(k₀+ε))+N^2/T)
          let Dweight := 144*U^2/(lam*H)
          (R.card:ℝ) ≤ 4*(Bmul:ℝ)*S.card+
            6*(Bmul:ℝ)^2*Count*(3*(Kcut:ℝ)+Dweight*(harmonic Kcut:ℝ)) := by
  classical
  obtain ⟨δ₀,κ₀,hδ₀,hκ₀,Q,hQ,C,hC,hcount⟩ :=
    original_model_uniform_positive_shift_count hσ hpair hε hp
  obtain ⟨δd,hδd,hdata⟩ := model_displacement_derivative_data hσ
  refine ⟨min δ₀ δd,κ₀,lt_min hδ₀ hδd,hκ₀,Q,hQ,C,hC,?_⟩
  intro ι _ S R center block z H Bmul Kcut s F T N a b η w
    hF hT hN hH hη hw hwhalf L U lam B Rmax Dmax hUsmall hLsmall
    hsmall hleft hright hκle hspan hmul hcenter hz hround hRS hsym f hshift hnear Count D
  have hF₀ := approximateModelPhase_mono hF le_rfl (min_le_left _ _)
  have hFd := approximateModelPhase_mono hF hQ (min_le_right _ _)
  obtain ⟨hreg,hthree,_,_⟩ := hdata F T N hT hN hFd
  have hlam : 0 < lam := by dsimp only [lam]; positivity [modelPhaseJetLower_pos hσ 3]
  have hL : 0 < L := by dsimp only [L]; positivity [modelPhaseJetLower_pos hσ 2]
  have hU : 0 < U := by dsimp only [U]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  have hB : 0 ≤ B := by dsimp only [B]; positivity [modelPhaseJetCoefficient_pos hσ 3]
  have hDmax : 0 < Dmax := by dsimp only [Dmax]; positivity
  have hCount : 0 ≤ Count := by dsimp only [Count]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  let h := fun x => iteratedDeriv 2 f x/2
  let Z := R.filter (fun p => h (z p.1)=h (z p.2))
  let Rp := R.filter (fun p => h (z p.1)<h (z p.2))
  have hRmem p (hp : p∈R) : p.1∈S ∧ p.2∈S := Finset.mem_product.mp (hRS hp)
  have hpmem p (hp : p∈Rp) : p∈R ∧ h (z p.1)<h (z p.2) := Finset.mem_filter.mp hp
  have hRsplit : R ⊆ Z ∪ (Rp ∪ Rp.image Prod.swap) := by
    intro p hp
    rcases lt_trichotomy (h (z p.1)) (h (z p.2)) with hh | hh | hh
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp,hh⟩))
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp,hh⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨p.swap,Finset.mem_filter.mpr ⟨hsym p hp,hh⟩,Prod.swap_swap p⟩
  have hsplit : R.card ≤ Z.card+2*Rp.card := by
    have hh := (Finset.card_le_card hRsplit).trans (Finset.card_union_le _ _)
    have hh' := Finset.card_union_le Rp (Rp.image Prod.swap)
    have he : (Rp.image Prod.swap).card=Rp.card := Finset.card_image_of_injective _ Prod.swap_injective
    omega
  have hmulLevel := bourgain_curvature_level_block_multiplicity S f z center block H Bmul s
    hH hL (fun t ht => (hreg t ht).of_le (by norm_num)) (fun t ht => (hthree t ht).1)
    hz (fun i hi => by simpa only [abs_sub_comm] using hround i hi) hspan hmul
  have hZfiber i : (Z.filter (fun p => p.1=i)).card ≤ 4*Bmul := by
    have hsub : Z.filter (fun p => p.1=i) ⊆ {i} ×ˢ (S.filter (fun j => h (z j)=h (z i))) := by
      intro p hp
      obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
      obtain ⟨hp,hh⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr he,
        Finset.mem_filter.mpr ⟨(hRmem p hp).2,by rw [←he]; exact hh.symm⟩⟩
    calc
      _ ≤ _ := Finset.card_le_card hsub
      _ = (S.filter (fun j => h (z j)=h (z i))).card := by simp only [Finset.card_product,Finset.card_singleton,one_mul]
      _ ≤ _ := hmulLevel _
  have hZ : (Z.card:ℝ) ≤ 4*(Bmul:ℝ)*S.card := by
    have he : (Z.card:ℝ)=∑ i∈S,((Z.filter (fun p => p.1=i)).card:ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_fiberwise
        (fun (p : ι × ι) hp => (hRmem p (Finset.mem_filter.mp hp).1).1)
    rw [he]
    calc
      _ ≤ ∑ _i∈S,4*(Bmul:ℝ) := Finset.sum_le_sum (fun i _ => by exact_mod_cast hZfiber i)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
  have hex (p : ι × ι) : ∃ d : ℕ, p∈Rp →
      0 < d ∧ h (z p.2)-h (z p.1)=(d:ℝ) ∧ d ≤ Kcut := by
    by_cases hp : p∈Rp
    · obtain ⟨d,he,hd⟩ := hshift p (hpmem p hp).1
      change h (z p.2)-h (z p.1)=(d:ℝ) at he
      have hdr : 0 < (d:ℝ) := by linarith only [he,(hpmem p hp).2]
      have hdi : 0 < d := by exact_mod_cast hdr
      have hdcast : (d.toNat:ℝ)=(d:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hdi.le
      refine ⟨d.toNat,fun _ => ⟨by omega,by rw [hdcast]; exact he,?_⟩⟩
      have hh : (d.toNat:ℝ) ≤ Kcut := by rw [hdcast]; exact (le_abs_self _).trans hd
      exact_mod_cast hh
    · exact ⟨0,fun hh => False.elim (hp hh)⟩
  choose shift hshiftNat using hex
  let J := Finset.Icc 1 Kcut
  have hindex p (hp : p∈Rp) : shift p∈J :=
    Finset.mem_Icc.mpr ⟨(hshiftNat p hp).1,(hshiftNat p hp).2.2⟩
  have hfiber n (hn : n∈J) :
      ((Rp.filter (fun p => shift p=n)).card:ℝ) ≤
        3*(Bmul:ℝ)^2*Count*(3+D/n) := by
    let E := Rp.filter (fun p => shift p=n)
    have hnmem := Finset.mem_Icc.mp hn
    have hEmem p (hp : p∈E) : p∈Rp ∧ shift p=n := Finset.mem_filter.mp hp
    have hb := hcount S E center block z H Bmul s (n:ℤ) F T N a b Kcut η w
      hF₀ hT hN hH (by exact_mod_cast hnmem.1) (by exact_mod_cast hnmem.2)
      hη hw hwhalf hUsmall hLsmall hsmall hleft hright hκle hspan hmul hcenter hz hround
      (fun p hp => hRS (hpmem p (hEmem p hp).1).1)
      (by
        intro p hp
        have he := (hshiftNat p (hEmem p hp).1).2.1
        rw [(hEmem p hp).2] at he
        simpa only [Int.cast_natCast] using he)
      (fun p hp => hnear p (hpmem p (hEmem p hp).1).1)
    change (E.card:ℝ) ≤
      (3*(Bmul:ℝ)^2*(3+144*U^2/(lam*((n:ℤ):ℝ)*H)))*Count at hb
    have hDeq : 144*U^2/(lam*((n:ℤ):ℝ)*H)=D/n := by
      simp only [Int.cast_natCast]
      dsimp only [D]
      ring
    rw [hDeq] at hb
    exact hb.trans_eq (by ring)
  have hsum : (∑ n∈J,(3+D/(n:ℝ))) ≤ 3*(Kcut:ℝ)+D*(harmonic Kcut:ℝ) := by
    have hh := sum_positive_displacement_weight_le_harmonic (η:=0) (N:=Kcut) le_rfl
      (by positivity : 0 ≤ D/3)
    simp only [Real.rpow_zero,one_mul] at hh
    calc
      _ = 3*∑ n∈J,(1+(D/3)/(n:ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ ≤ 3*((Kcut:ℝ)+(D/3)*(harmonic Kcut:ℝ)) :=
        mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = _ := by ring
  have hRp : (Rp.card:ℝ) ≤ 3*(Bmul:ℝ)^2*Count*(3*(Kcut:ℝ)+D*(harmonic Kcut:ℝ)) := by
    have hc : (Rp.card:ℝ)=∑ n∈J,((Rp.filter (fun p => shift p=n)).card:ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_fiberwise hindex
    calc
      _ = _ := hc
      _ ≤ ∑ n∈J,3*(Bmul:ℝ)^2*Count*(3+D/(n:ℝ)) := Finset.sum_le_sum hfiber
      _ = (3*(Bmul:ℝ)^2*Count)*∑ n∈J,(3+D/(n:ℝ)) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)
  have hsplitR : (R.card:ℝ) ≤ (Z.card:ℝ)+2*(Rp.card:ℝ) := by exact_mod_cast hsplit
  calc
    _ ≤ _ := hsplitR
    _ ≤ 4*(Bmul:ℝ)*S.card+2*(3*(Bmul:ℝ)^2*Count*(3*(Kcut:ℝ)+D*(harmonic Kcut:ℝ))) :=
      add_le_add hZ (mul_le_mul_of_nonneg_left hRp (by norm_num))
    _ = _ := by ring

/-- The literal four-coordinate second-spacing window, counted by an analytic
exponent pair. All rational labels, both parities, both shift signs, the
zero shift and the block multiplicities are preserved. -/
theorem original_model_four_coordinate_count
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 3 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ {ι : Type*} [DecidableEq ι] (S : Finset ι)
          (center block label inverse : ι → ℤ) (z : ι → ℝ) (q : ι → ℕ)
          (parity : ι → Fin 2) (H Bmul M Qden : ℕ) [NeZero M] (s : ℤ)
          (F : ℝ → ℝ) (T N a₀ b₀ w : ℝ),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 0 < H → 0 < Qden → 0 < w → w ≤ 1/2 →
          (Qden:ℝ)^2 < 6*(M:ℝ)^2 →
          let L := modelPhaseJetLower σ 2*T/N^3
          let U := (modelPhaseJetCoefficient σ 2+1)*T/N^3
          let lam := modelPhaseJetLower σ 3*T/N^4
          let B := (modelPhaseJetCoefficient σ 3+1)*T/N^4
          let f := fun t => T*F (t/N)
    let mu := fun i => iteratedDeriv 3 f (center i)/6
    let ell := fun i => iteratedDeriv 1 f (center i)
    let b := fun i => (⌊(q i:ℝ)*ell i⌋:ℤ)+(parity i:ℕ)
    let tau := fun i => ((b i:ℝ)-(q i:ℝ)*ell i)/2
    let coeff := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let Y := fun i => (![Int.fract (-(inverse i:ℝ)*b i/q i),Int.fract (-(inverse i:ℝ)/q i),
      coeff i/Real.sqrt M,(3*coeff i*tau i/2)/Real.sqrt M] : Fin 4 → ℝ)
    let window : Fin 4 → ℝ :=
      ![1/(12*(M:ℝ)),1/(12*(M:ℝ)^2),(1/(M:ℝ)^2)/12,(1/(M:ℝ))/12]
    let R := (S ×ˢ S).filter (fun ij => ∀ j, |Y ij.1 j-Y ij.2 j| ≤ 2*window j)
    let D₀ : ℝ := (Real.sqrt M/(9*(M:ℝ))+Real.sqrt M/(12*(M:ℝ)^2))*
      Real.sqrt (U*(Qden:ℝ)^3)
    let η : ℝ := 4*D₀/(Qden:ℝ)
    let rho := (12*U*Real.sqrt (U*(Qden:ℝ)^3)/lam)*(Real.sqrt M/(6*(M:ℝ)^2))
    let Kcut := ⌈3*U*(rho+1)⌉₊
    let Rmax := 36*U^2/lam
    let Dmax := (Kcut:ℝ)/L+1
    12*U ≤ 1 → L ≤ 1 →
    2*η+10368*B*U^4/(lam^2*L) ≤ 1/2 →
    N < a₀-Rmax → b₀+Rmax+2*Dmax < 2*N →
    2*(Kcut:ℝ)*N^2/(σ*T) ≤ κ₀ →
    (∀ i∈S, (H:ℤ) ≤ s+(H:ℤ)*block i-center i ∧
      s+(H:ℤ)*block i-center i ≤ 3*(H:ℤ)) →
    (∀ j : ℤ, (S.filter (fun i => block i=j)).card ≤ Bmul) →
    (∀ i∈S, (center i:ℝ)∈Icc a₀ b₀) →
    (∀ i∈S, z i∈Ioo N (2*N)) →
    (∀ i∈S, |(center i:ℝ)-z i| ≤ 1/2) →
    (∀ i∈S, 0 < q i ∧ q i ≤ Qden ∧ Qden ≤ 2*q i) →
    (∀ i∈S, (q i:ℤ) ∣ label i*inverse i-1) →
    (∀ i∈S, iteratedDeriv 2 f (z i)/2=(label i:ℝ)/q i) →
    let Count := C*((2*η+w)*Dmax+20736*B*U^4/(lam^2*L^2)+
      (T/N^2)^(k₀+ε)*Dmax^(l₀+ε)*w^(-(k₀+ε))+N^2/T)
    let Dweight := 144*U^2/(lam*H)
    (R.card:ℝ) ≤ 4*(Bmul:ℝ)*S.card+
      6*(Bmul:ℝ)^2*Count*(3*(Kcut:ℝ)+Dweight*(harmonic Kcut:ℝ)) := by
  classical
  obtain ⟨δ₀,κ₀,hδ₀,hκ₀,Q,hQ,C,hC,hcount⟩ :=
    original_model_all_shifts_count hσ hpair hε hp
  obtain ⟨δd,hδd,hdata⟩ := model_displacement_derivative_data hσ
  refine ⟨min δ₀ δd,κ₀,lt_min hδ₀ hδd,hκ₀,Q,hQ,C,hC,?_⟩
  intro ι _ S center block label inverse z q parity H Bmul M Qden _ s F T N a₀ b₀ w
    hF hT hN hH hQden hw hwhalf hthin L U lam B f
    mu ell b tau coeff Y window R D₀ η rho Kcut Rmax Dmax hUsmall hLsmall
    hsmall hleft hright hκle hspan hmul hcenter hz hround hq hinverse hlevel Count Dweight
  have hF₀ := approximateModelPhase_mono hF le_rfl (min_le_left _ _)
  have hFd := approximateModelPhase_mono hF hQ (min_le_right _ _)
  obtain ⟨hreg,hthree,hfour,_⟩ := hdata F T N hT hN hFd
  have hlam : 0 < lam := by dsimp only [lam]; positivity [modelPhaseJetLower_pos hσ 3]
  have hL : 0 < L := by dsimp only [L]; positivity [modelPhaseJetLower_pos hσ 2]
  have hU : 0 < U := by dsimp only [U]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  have hRmax : 0 < Rmax := by dsimp only [Rmax]; positivity
  have hDmax : 0 < Dmax := by dsimp only [Dmax]; positivity
  have hcent i (hi : i∈S) : (center i:ℝ)∈Ioo N (2*N) := by
    have hh := hcenter i hi
    constructor <;> linarith [hh.1,hh.2]
  have hthreeUpper t (ht : t∈Ioo N (2*N)) :
      L ≤ iteratedDeriv 3 f t ∧ iteratedDeriv 3 f t ≤ 6*U := by
    have hh := hthree t ht
    exact ⟨hh.1,by linarith [hh.2]⟩
  have hQr : (0:ℝ) < Qden := by exact_mod_cast hQden
  have hD₀ : 0 ≤ D₀ := by dsimp only [D₀]; positivity
  have hη : 0 ≤ η := by dsimp only [η]; positivity
  have hRmem p (hp : p∈R) : p.1∈S ∧ p.2∈S :=
    Finset.mem_product.mp (Finset.mem_filter.mp hp).1
  have hRnear p (hp : p∈R) : ∀ j, |Y p.1 j-Y p.2 j| ≤ 2*window j :=
    (Finset.mem_filter.mp hp).2
  have hRsym p (hp : p∈R) : p.swap∈R := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨(hRmem p hp).2,(hRmem p hp).1⟩,?_⟩
    intro j
    change |Y p.2 j-Y p.1 j| ≤ 2*window j
    rw [abs_sub_comm]
    exact hRnear p hp j
  have hshift p (hp : p∈R) : ∃ k : ℤ,
      iteratedDeriv 2 f (z p.2)/2-iteratedDeriv 2 f (z p.1)/2=(k:ℝ) ∧ |(k:ℝ)| ≤ Kcut := by
    have hi := (hRmem p hp).1
    have hj := (hRmem p hp).2
    have hh := source_four_coordinate_integer_shift_bound f M (q p.1) (q p.2) Qden
      (label p.1) (label p.2) (inverse p.1) (inverse p.2) (center p.1) (center p.2)
      (hq _ hi).1 (hq _ hj).1 (hq _ hi).2.1 (hq _ hj).2.1 hthin hlam hU
      (fun t ht => (hreg t ht).of_le (by norm_num))
      (fun t ht => ⟨hL.trans_le (hthreeUpper t ht).1,(hthreeUpper t ht).2⟩)
      (fun t ht => by
        have hb := (hfour t ht).2
        rw [abs_of_neg (by linarith only [hb,hlam])]
        linarith only [hb])
      (hz _ hi) (hz _ hj) (hcent _ hi) (hcent _ hj)
      (by simpa only [abs_sub_comm] using hround _ hi)
      (by simpa only [abs_sub_comm] using hround _ hj)
      (hinverse _ hi) (hinverse _ hj) (hlevel _ hi) (hlevel _ hj)
      (by
        have hb := hRnear p hp 1
        change _ ≤ 2*(1/(12*(M:ℝ)^2)) at hb
        convert hb using 1
        ring)
      (by
        have hb := hRnear p hp 2
        change _ ≤ 2*((1/(M:ℝ)^2)/12) at hb
        convert hb using 1
        ring)
    obtain ⟨_,k,hk,hb⟩ := hh
    exact ⟨k,hk,hb.trans (Nat.le_ceil _)⟩
  have hnear p (hp : p∈R) : ∃ e : ℤ, |ell p.2-ell p.1-(e:ℝ)| ≤ η := by
    have hi := (hRmem p hp).1
    have hj := (hRmem p hp).2
    have hmui : 0 < mu p.1 := by
      dsimp only [mu]
      positivity [hL.trans_le (hthreeUpper _ (hcent _ hi)).1]
    have hmuj : 0 < mu p.2 := by
      dsimp only [mu]
      positivity [hL.trans_le (hthreeUpper _ (hcent _ hj)).1]
    have hmuiU : mu p.1 ≤ U := by
      dsimp only [mu]
      linarith only [(hthreeUpper _ (hcent _ hi)).2]
    obtain ⟨_,k,e,_hk,he⟩ := actual_source_triangular_derivative_resonance M (q p.1) (q p.2) Qden
      (label p.1) (label p.2) (inverse p.1) (inverse p.2)
      (hq _ hi).1 (hq _ hj).1 (hq _ hi).2.1 (hq _ hj).2.1 hthin
      (hinverse _ hi) (hinverse _ hj) hmui hmuj hmuiU (parity p.1) (parity p.2)
      (hRnear p hp)
    have hqr : (0:ℝ) < q p.1 := by exact_mod_cast (hq _ hi).1
    have hQq : (Qden:ℝ) ≤ 2*(q p.1:ℝ) := by exact_mod_cast (hq _ hi).2.2
    refine ⟨e,he.trans ?_⟩
    change 2*D₀/(q p.1:ℝ) ≤ 4*D₀/Qden
    apply (div_le_div_iff₀ hqr hQr).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hQq hD₀]
  exact hcount S R center block z H Bmul Kcut s F T N a₀ b₀ η w
    hF₀ hT hN hH hη hw hwhalf hUsmall hLsmall hsmall hleft hright hκle
    hspan hmul hcenter hz hround (fun _ hp => (Finset.mem_filter.mp hp).1)
    hRsym hshift hnear

/-- The actual frozen C4 source sum with the refined exponent-pair spacing
count. The original model supplies all derivative data, and the real source
labels/parities are passed to the literal four-coordinate count. -/
theorem exists_model_refined_frozen_source
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Qphase : ℕ, 3 ≤ Qphase ∧ ∃ C > (0:ℝ), ∃ Cp : ℝ, 1 ≤ Cp ∧
      ∀ (ι : Type*) [DecidableEq ι] (S : Finset ι)
      (G : ℝ → ℝ) (T P : ℝ) (r : ι → ℚ) (z : ι → ℝ) (m k : ι → ℤ)
      (H : ι → ℕ) (N Q Bmul : ℕ) (s : ℤ) (A B w : ℝ),
      IsApproximateModelPhaseFunction G σ Qphase δ →
      0 < T → 0 < P → 0 < N → 0 < Q → 0 < w → w ≤ 1/2 →
      let f := fun t => T*G (t/P)
      let L := modelPhaseJetLower σ 2*T/P^3
      let U := (modelPhaseJetCoefficient σ 2+1)*T/P^3
      let lam := modelPhaseJetLower σ 3*T/P^4
      let F := (modelPhaseJetCoefficient σ 3+1)*T/P^4
      12*U ≤ 1 → L ≤ 1 →
      F*(6*(N:ℝ)+1)^4 ≤ 1 → (3*U/2)*(6*(N:ℝ)+1)^2 ≤ 1 →
      (∀ i∈S, z i∈Ioo A B) →
      (∀ i∈S, Icc ((m i:ℝ)-(6*(N:ℝ)+1)) ((m i:ℝ)+(6*(N:ℝ)+1)) ⊆ Icc A B) →
      (∀ i∈S, |z i-m i| ≤ 1/2) →
      (∀ i∈S, (N:ℤ) ≤ s+(N:ℤ)*k i-m i ∧ s+(N:ℤ)*k i-m i ≤ 3*(N:ℤ)) →
      (∀ n : ℤ, (S.filter (fun i => k i=n)).card ≤ Bmul) →
      (∀ i∈S, H i ≤ N) →
      (∀ i∈S, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧ (r i).den ≤ N) →
      (∀ i∈S, iteratedDeriv 2 f (z i)/2=(r i:ℝ)) →
      12 ≤ L*(Q:ℝ)*(N:ℝ)^2 → 384 ≤ L^2*(Q:ℝ)^3*(N:ℝ)^3 →
      let Z := (S.card:ℝ)
      let M : ℕ := ⌈63*U*(Q:ℝ)*(N:ℝ)^2⌉₊+1
      let V := 756*U/L
      let Wloss := 1+32/(L*(Q:ℝ)^2*N)
      let d := L*(Q:ℝ)*N/12
      let D₀ := (Real.sqrt M/(9*(M:ℝ))+Real.sqrt M/(12*(M:ℝ)^2))*Real.sqrt (U*(Q:ℝ)^3)
      let η : ℝ := 4*D₀/(Q:ℝ)
      let rho := (12*U*Real.sqrt (U*(Q:ℝ)^3)/lam)*(Real.sqrt M/(6*(M:ℝ)^2))
      let K := ⌈3*U*(rho+1)⌉₊
      let Rmax := 36*U^2/lam
      let Dmax := (K:ℝ)/L+1
      let Dweight := 144*U^2/(lam*N)
      let Count := Cp*((2*η+w)*Dmax+20736*F*U^4/(lam^2*L^2)+
        (T/P^2)^(k₀+ε)*Dmax^(l₀+ε)*w^(-(k₀+ε))+P^2/T)
      let Pair := 4*(Bmul:ℝ)*Z+6*(Bmul:ℝ)^2*Count*(3*(K:ℝ)+Dweight*(harmonic K:ℝ))
      let Loss := (5*Wloss)^11*Wloss^2*(6*(3+8*Real.pi*V)*(1+Real.log M))^12*
        (2/d)^6*(M:ℝ)^((12:ℝ)+ε)
      let Err := Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+6/(L*(N:ℝ)^2)+
        Real.sqrt (12/(L*(N:ℝ)*Q))
      (Q:ℝ)^2 < 6*(M:ℝ)^2 →
      2*η+10368*F*U^4/(lam^2*L) ≤ 1/2 →
      P < A-Rmax → B+Rmax+2*Dmax < 2*P →
      2*(K:ℝ)*P^2/(σ*T) ≤ κ₀ →
      (∑ i∈S, ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖)^12 ≤
        C*(Loss*(2*Z)^10*Pair+(Z*Err)^12) := by
  classical
  obtain ⟨δ₀,κ₀,hδ₀,hκ₀,Qphase,hQphase,Cp,hCp,hcount⟩ :=
    original_model_four_coordinate_count hσ hpair hε hp
  obtain ⟨δd,hδd,hdata⟩ := model_displacement_derivative_data hσ
  obtain ⟨C,hC,hsource⟩ := exists_bourgain_C4_frozen_source_second_spacing_reduction hε
  refine ⟨min δ₀ δd,κ₀,lt_min hδ₀ hδd,hκ₀,Qphase,hQphase,4*C,by positivity,Cp,hCp,?_⟩
  intro ι instι S G T P r z m k H N Q Bmul s A B w
    hG hT hP hN hQ hw hwhalf f L U lam F hUsmall hLsmall hfourSmall hquadSmall
    hz hbuffer hround hspan hmul hH hq hlevel hdual hfrozen
    Z M V Wloss d D₀ η rho K Rmax Dmax Dweight Count Pair Loss Err hthin
    hliftSmall hleft hright hκle
  have hG₀ := approximateModelPhase_mono hG le_rfl (min_le_left _ _)
  have hGd := approximateModelPhase_mono hG hQphase (min_le_right _ _)
  obtain ⟨hreg,hthreeModel,hfourModel,_⟩ := hdata G T P hT hP hGd
  have hlam : 0 < lam := by dsimp only [lam]; positivity [modelPhaseJetLower_pos hσ 3]
  have hL : 0 < L := by dsimp only [L]; positivity [modelPhaseJetLower_pos hσ 2]
  have hU : 0 < U := by dsimp only [U]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  have hF : 0 < F := by dsimp only [F]; positivity [modelPhaseJetCoefficient_pos hσ 3]
  have hRmax : 0 < Rmax := by dsimp only [Rmax]; positivity
  have hDmax : 0 < Dmax := by dsimp only [Dmax]; positivity
  have hdomain : Icc A B ⊆ Ioo P (2*P) := by
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  have hf x (hx : x∈Icc A B) : ContDiffAt ℝ 5 f x := hreg x (hdomain hx)
  have hthree x (hx : x∈Icc A B) :
      L ≤ iteratedDeriv 3 f x ∧ iteratedDeriv 3 f x ≤ 6*U := by
    have hh := hthreeModel x (hdomain hx)
    exact ⟨hh.1,by linarith [hh.2]⟩
  have hfour x (hx : x∈Icc A B) :
      -F ≤ iteratedDeriv 4 f x ∧ iteratedDeriv 4 f x ≤ -lam := hfourModel x (hdomain hx)
  have hf₄ x (hx : x∈Icc A B) : ContDiffAt ℝ 4 f x := (hf x hx).of_le (by norm_num)
  have hfourAbs x (hx : x∈Icc A B) : lam ≤ |iteratedDeriv 4 f x| ∧ |iteratedDeriv 4 f x| ≤ F := by
    have hh := hfour x hx
    rw [abs_of_neg (by linarith only [hh.2,hlam])]
    constructor <;> linarith only [hh.1,hh.2]
  let H₀ := L*(Q:ℝ)*(N:ℝ)^2/12
  have hNr : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hQr : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hcard : (S.card:ℝ) ≤ Z := le_rfl
  let W := fun i => (s+(N:ℤ)*k i-m i).toNat
  let mu := fun i => iteratedDeriv 3 f (m i)/6
  have hW i (hi : i∈S) : N ≤ W i ∧ W i ≤ 3*N ∧ m i+(W i:ℤ)=s+(N:ℤ)*k i := by
    have hh := hspan i hi
    dsimp only [W]
    constructor
    · omega
    · constructor <;> omega
  have hWp i (hi : i∈S) : 1 ≤ W i := (Nat.succ_le_iff.mpr hN).trans (hW i hi).1
  have hWr i (hi : i∈S) : (N:ℝ) ≤ W i ∧ (W i:ℝ) ≤ 3*(N:ℝ) := by
    constructor <;> exact_mod_cast (by first | exact (hW i hi).1 | exact (hW i hi).2.1)
  have hm i (hi : i∈S) : (m i:ℝ)∈Ioo A B := by
    have hrad : 0 < 6*(N:ℝ)+1 := by positivity
    have hlo := (hbuffer i hi (left_mem_Icc.mpr (by linarith only [hrad]))).1
    have hhi := (hbuffer i hi (right_mem_Icc.mpr (by linarith only [hrad]))).2
    constructor <;> linarith only [hlo,hhi,hrad]
  have hmu i (hi : i∈S) : 0 < mu i ∧ L/6 ≤ mu i ∧ mu i ≤ U := by
    have hh := hthree (m i) ⟨(hm i hi).1.le,(hm i hi).2.le⟩
    dsimp only [mu]
    constructor
    · linarith only [hh.1,hL]
    · constructor <;> linarith only [hh.1,hh.2]
  have hbuf i (hi : i∈S) :
      Icc ((m i:ℝ)-(2*(W i:ℝ)+1)) ((m i:ℝ)+(2*(W i:ℝ)+1)) ⊆ Icc A B := by
    intro x hx
    apply hbuffer i hi
    have hw := (hWr i hi).2
    constructor <;> linarith only [hx.1,hx.2,hw]
  have hsmall i (hi : i∈S) :
      F*(2*(W i:ℝ)+1)^4 ≤ 1 ∧ (3*U/2)*(2*(W i:ℝ)+1)^2 ≤ 1 := by
    have hw : 2*(W i:ℝ)+1 ≤ 6*(N:ℝ)+1 := by linarith only [(hWr i hi).2]
    constructor
    · exact (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hw 4) hF.le).trans hfourSmall
    · exact (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hw 2) (by positivity)).trans hquadSmall
  have hcurv i (hi : i∈S) :
      |iteratedDeriv 2 f (m i)/2-((r i).num:ℝ)/(r i).den| ≤ 3*U/2 := by
    have hh := bourgain_curvature_level_difference f hf₄
      (fun x hx => ⟨hL.le.trans (hthree x hx).1,(hthree x hx).2⟩)
      ⟨(hm i hi).1.le,(hm i hi).2.le⟩ ⟨(hz i hi).1.le,(hz i hi).2.le⟩
    rw [hlevel i hi,Rat.cast_def,abs_sub_comm (m i:ℝ) (z i)] at hh
    have hr := mul_le_mul_of_nonneg_left (hround i hi) (show 0 ≤ 3*U by positivity)
    exact hh.trans (by linarith only [hr])
  have hscale i (hi : i∈S) : mu i*(W i:ℝ)^2 ≤ 1 := by
    have ha : (W i:ℝ)^2 ≤ (2*(W i:ℝ)+1)^2 := by
      nlinarith only [show (0:ℝ) ≤ W i from Nat.cast_nonneg _]
    calc
      _ ≤ U*(2*(W i:ℝ)+1)^2 :=
        mul_le_mul (hmu i hi).2.2 ha (sq_nonneg _) hU.le
      _ ≤ (3*U/2)*(2*(W i:ℝ)+1)^2 := by gcongr; linarith only [hU]
      _ ≤ _ := (hsmall i hi).2

  letI : NeZero M := ⟨by dsimp only [M]; omega⟩
  have hM : 63*U*(Q:ℝ)*(N:ℝ)^2≤(M:ℝ) := by
    have hh := Nat.le_ceil (63*U*(Q:ℝ)*(N:ℝ)^2)
    dsimp only [M]
    push_cast
    linarith only [hh]
  have hV : 0≤V := by dsimp only [V]; positivity
  have hWloss : 1≤Wloss := by
    have hp : 0≤32/(L*(Q:ℝ)^2*N) := by positivity
    dsimp only [Wloss]
    linarith only [hp]
  have hd : 0<d := by dsimp only [d]; positivity
  have hphysical i (hi : i∈S) :
      1≤H₀ ∧ H₀≤ mu i*((r i).den:ℝ)*(W i:ℝ)^2 ∧
        7*(mu i*((r i).den:ℝ)*(W i:ℝ)^2)≤63*U*(Q:ℝ)*(N:ℝ)^2 ∧
        7*(mu i*((r i).den:ℝ)*(W i:ℝ)^2)≤V*H₀ ∧
        |-2*mu i*(Real.sqrt (2/(3*mu i*((r i).den:ℝ))))^3|≤H₀*Real.sqrt H₀ ∧
        |-2*mu i*(Real.sqrt (2/(3*mu i*((r i).den:ℝ))))^3|/Real.sqrt H₀≤Wloss := by
    have hQq : (Q:ℝ)/2≤(r i).den := by
      have hh : (Q:ℝ)≤2*((r i).den:ℝ) := by exact_mod_cast (hq i hi).2.1
      linarith only [hh]
    exact bourgain_frozen_physical_dual_scales hL hU hNr hQr (hmu i hi).2
      ⟨hQq,Nat.cast_le.mpr (hq i hi).1⟩ (hWr i hi) hdual hfrozen
  have hdscale i (hi : i∈S) : d≤ mu i*((r i).den:ℝ)*W i := by
    have hqr : (Q:ℝ)≤2*((r i).den:ℝ) := by exact_mod_cast (hq i hi).2.1
    calc
      d = (L/6)*((Q:ℝ)/2)*N := by dsimp only [d]; ring
      _ ≤ mu i*((r i).den:ℝ)*W i :=
        mul_le_mul (mul_le_mul (hmu i hi).2.1 (by linarith only [hqr])
          (by positivity) (hmu i hi).1.le)
          (hWr i hi).1 hNr.le (mul_nonneg (hmu i hi).1.le (Nat.cast_nonneg _))
  by_cases hS : S.Nonempty
  · obtain ⟨i₀,hi₀⟩ := hS
    have hH₀ := (hphysical i₀ hi₀).1
    have hH₀M : H₀≤(M:ℝ) := by
      have hlow := (hphysical i₀ hi₀).2.1
      have hhigh := (hphysical i₀ hi₀).2.2.1.trans hM
      linarith only [hlow,hhigh,hH₀]
    obtain ⟨rinv,hinv,hbound⟩ := hsource ι S (fun _ => f) (fun i => (m i:ℝ))
      (fun i => (r i).num) (fun i => (r i).den) W H hWp
      (fun i hi => (hH i hi).trans (hW i hi).1) F (3*U/2) hF.le (by positivity)
      (fun i hi => (hsmall i hi).1) (fun i hi => (hsmall i hi).2)
      (fun i hi x hx => hf₄ x (hbuf i hi hx))
      (fun i hi x hx => (hfourAbs x (hbuf i hi hx)).2) hcurv
      (fun i hi => ⟨(r i).pos,((hq i hi).2.2.trans (hW i hi).1),
        (r i).isCoprime_num_den,(hmu i hi).1,hscale i hi⟩)
      M H₀ V Wloss d hH₀ hH₀M hV hWloss hd
      (fun i hi => (hphysical i hi).2.1)
      (fun i hi => (hphysical i hi).2.2.2.2.1)
      (fun i hi => (hphysical i hi).2.2.2.2.2)
      (fun i hi => (hphysical i hi).2.2.1.trans hM)
      (fun i hi => (hphysical i hi).2.2.2.1) hdscale

    let S₂ := S ×ˢ (Finset.univ : Finset (Fin 2))
    have hmul₂ n : (S₂.filter (fun p => k p.1=n)).card ≤ 2*Bmul := by
      have he : S₂.filter (fun p => k p.1=n)=
          (S.filter (fun i => k i=n)) ×ˢ (Finset.univ : Finset (Fin 2)) := by
        ext p
        simp only [S₂,Finset.mem_filter,Finset.mem_product,Finset.mem_univ,and_true]
      rw [he,Finset.card_product,Finset.card_univ,Fintype.card_fin]
      have hh := hmul n
      omega
    have hc₀ := hcount S₂
      (fun p => m p.1) (fun p => k p.1) (fun p => (r p.1).num) (fun p => rinv p.1)
      (fun p => z p.1) (fun p => (r p.1).den) Prod.snd N (2*Bmul) M Q s G T P A B w
      hG₀ hT hP hN hQ hw hwhalf hthin hUsmall hLsmall hliftSmall hleft hright hκle
      (fun p hp => hspan _ (Finset.mem_product.mp hp).1) hmul₂
      (fun p hp => ⟨(hm _ (Finset.mem_product.mp hp).1).1.le,(hm _ (Finset.mem_product.mp hp).1).2.le⟩)
      (fun p hp => hdomain ⟨(hz _ (Finset.mem_product.mp hp).1).1.le,(hz _ (Finset.mem_product.mp hp).1).2.le⟩)
      (fun p hp => by simpa only [abs_sub_comm] using hround _ (Finset.mem_product.mp hp).1)
      (fun p hp => ⟨(r p.1).pos,(hq _ (Finset.mem_product.mp hp).1).1,
        (hq _ (Finset.mem_product.mp hp).1).2.1⟩)
      (fun p hp => hinv _ (Finset.mem_product.mp hp).1)
      (fun p hp => by simpa only [Rat.cast_def] using hlevel _ (Finset.mem_product.mp hp).1)
    dsimp only at hc₀
    have hPairRewrite : 4*((2*Bmul:ℕ):ℝ)*S₂.card+
        6*((2*Bmul:ℕ):ℝ)^2*Count*(3*(K:ℝ)+Dweight*(harmonic K:ℝ))=4*Pair := by
      dsimp only [Pair,Z,S₂]
      rw [Finset.card_product,Finset.card_univ,Fintype.card_fin]
      push_cast
      ring
    have hc := hc₀
    change _ ≤ 4*((2*Bmul:ℕ):ℝ)*S₂.card+
      6*((2*Bmul:ℕ):ℝ)^2*Count*(3*(K:ℝ)+Dweight*(harmonic K:ℝ)) at hc
    rw [hPairRewrite] at hc
    simp only [iteratedDeriv_one] at hc

    have hErr i (hi : i∈S) :
        Real.sqrt (W i)*Real.log (2*(W i:ℝ))+1/(mu i*(W i:ℝ)^2)+
          1/(Real.sqrt (mu i*(W i:ℝ))*Real.sqrt (r i).den) ≤ Err := by
      have hQq : (Q:ℝ)/2 ≤ (r i).den := by
        have hh : (Q:ℝ) ≤ 2*((r i).den:ℝ) := by exact_mod_cast (hq i hi).2.1
        linarith only [hh]
      exact displacement_prescribed_source_error hN hQ (r i).pos hL
        (hW i hi).1 (hW i hi).2.1 (hmu i hi).2.1 hQq

    have hlog : 0≤Real.log (6*(N:ℝ)) := by
      have hn : (1:ℝ)≤N := by exact_mod_cast hN
      exact Real.log_nonneg (by linarith only [hn])
    have hErr0 : 0≤Err := by dsimp only [Err]; positivity
    let ErrorSum := ∑ i∈S,(Real.sqrt (W i)*Real.log (2*(W i:ℝ))+1/(mu i*(W i:ℝ)^2)+
      1/(Real.sqrt (mu i*(W i:ℝ))*Real.sqrt (r i).den))
    have hErrorSum0 : 0≤ErrorSum := by
      apply Finset.sum_nonneg
      intro i hi
      have hw1 : (1:ℝ)≤W i := by exact_mod_cast hWp i hi
      have hl := Real.log_nonneg (by linarith only [hw1] : 1≤2*(W i:ℝ))
      have hmup := (hmu i hi).1
      positivity
    have herrorSum : ErrorSum≤Z*Err := by
      calc
        _ ≤ ∑ _i∈S,Err := Finset.sum_le_sum hErr
        _ = S.card*Err := by simp only [Finset.sum_const,nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right hcard hErr0
    have hLoss : 0≤Loss := by dsimp only [Loss]; positivity
    have hsrc :
        (∑ i∈S, ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖)=
        ∑ i∈S, ‖∑ n∈Finset.Ioc (W i:ℤ) ((W i:ℤ)+H i),(𝐞 (f ((m i:ℝ)+n)):ℂ)‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [←(hW i hi).2.2,bourgain_integer_source_translation]
    dsimp only at hbound hc
    rw [←hsrc] at hbound
    exact displacement_frozen_cardinality_absorption S hC.le hLoss hErr0
      hErrorSum0 herrorSum hc hbound
  · have hempty : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hZ : Z=0 := by simp only [Z,hempty,Finset.card_empty,Nat.cast_zero]
    have hsrcempty :
        (∑ i∈S, ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖)^12=0 := by
      rw [hempty]
      simp only [Finset.sum_empty,zero_pow (by norm_num : (12:ℕ)≠0)]
    rw [hsrcempty]
    exact displacement_empty_source_bound C Loss Pair Err Z hZ


/-- Exact balance for the exponent-pair replacement of the second-spacing
term. This is algebra only; the analytic beta consumer is a separate obligation. -/
theorem refined_spacing_exponent_balance {k l a : ℝ} (hk : 0 ≤ k) :
    let u := 1-3*a
    let z := a+u/2
    let v := a+u
    let w := (k*v+(l-1)*z)/(1+k)
    let c := (7*k+l+4)/(24*(1+k))
    let d := (5*k-l+10)/(24*(1+k))
    w+z=k*v+l*z-k*w ∧
      w+z=((2*k+l)/(1+k))*a+((3*k+l)/(2*(1+k)))*u ∧
      10*a+u/2+(a+3*u/2)+(w+z)=12*(c+d*a) := by
  intro u z v w c d
  have hd : (1+k) ≠ 0 := by positivity
  dsimp only [u,z,v,w,c,d]
  field_simp
  constructor
  · ring
  constructor <;> ring

/-- Physical strict inequalities for the prospective Bourgain-input refinement;
this statement does not assert the beta bound. -/
theorem refined_bourgain_scale_domain {a : ℝ} (ha : 2/5 < a) (hb : a < 3/7) :
    let u := 1-3*a
    let z := a+u/2
    let w := -(3+23*a)/194
    let β := max (1/12+2*a/3) (241/1164+425*a/1164)
    u<0 ∧ w<0 ∧ 2-5*a<0 ∧ 0<a+3*u/2 ∧ z<a ∧ z<β ∧
      2*a-1<0 ∧ 1/4+a/4≤β ∧
      ((13/84:ℝ)*(a+u)+(55/84-1)*z)/(1+13/84)=w ∧
      w+z=(47-60*a)/97 := by
  intro u z w β
  have hβ : 1/12+2*a/3 ≤ β := le_max_left _ _
  dsimp only [u,z,w] at *
  refine ⟨by linarith,by linarith,by linarith,by linarith,by linarith,
    by linarith,by linarith,by linarith,?_,?_⟩ <;> ring

end TaoTrudgianYang2025.CubicJointCount
#print axioms TaoTrudgianYang2025.CubicJointCount.original_joint_level_displacement_count
#print axioms TaoTrudgianYang2025.CubicJointCount.original_model_block_source_pair_count
#print axioms TaoTrudgianYang2025.CubicJointCount.original_model_rounded_shift_count
#print axioms TaoTrudgianYang2025.CubicJointCount.rounded_shift_free_width
#print axioms TaoTrudgianYang2025.CubicJointCount.original_model_uniform_positive_shift_count
#print axioms TaoTrudgianYang2025.CubicJointCount.original_model_all_shifts_count
#print axioms TaoTrudgianYang2025.CubicJointCount.original_model_four_coordinate_count
#print axioms TaoTrudgianYang2025.CubicJointCount.exists_model_refined_frozen_source
#print axioms TaoTrudgianYang2025.CubicJointCount.refined_spacing_exponent_balance
#print axioms TaoTrudgianYang2025.CubicJointCount.refined_bourgain_scale_domain
