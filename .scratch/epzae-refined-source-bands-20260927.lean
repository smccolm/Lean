import TaoTrudgianYang2025.SquareProductCount
noncomputable section
open Set MeasureTheory Expdb Filter GafniTao
open scoped Topology ContDiff BigOperators NNReal FourierTransform
namespace TaoTrudgianYang2025.CubicJointCount

/-- Minimal curvature arcs are constructed from the actual model and retained
through both the low-denominator source estimate and the refined frozen sieve.
No rational family, cardinality estimate or source bound is an input. -/
theorem exists_model_refined_source_bands
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Qphase : ℕ, 3 ≤ Qphase ∧ ∃ Cd ≥ (1:ℝ), ∃ Cf > (0:ℝ),
      ∃ Cp : ℝ, 1 ≤ Cp ∧ ∀ (ι : Type*) [DecidableEq ι]
      (S : Finset ι) (F : ℝ → ℝ) (T P : ℝ) (k : ι → ℤ) (H : ι → ℕ)
      (N : ℕ) (s : ℤ) (A B w : ℝ),
      IsApproximateModelPhaseFunction F σ Qphase δ →
      0<T → 0<P → 0<N → 0<w → w≤1/2 → P<A → B<2*P →
      let f := fun t => T*F (t/P)
      let L := modelPhaseJetLower σ 2*T/P^3
      let U := (modelPhaseJetCoefficient σ 2+1)*T/P^3
      let lam := modelPhaseJetLower σ 3*T/P^4
      let F4 := (modelPhaseJetCoefficient σ 3+1)*T/P^4
      let X := (modelPhaseJetCoefficient σ 1+1)*T/P^2/2
      12*U≤1 → L≤1 →
      F4*(6*(N:ℝ)+1)^4≤1 → (3*U/2)*(6*(N:ℝ)+1)^2≤1 →
      (∀ j : ℤ, (S.filter (fun i => k i=j)).card ≤ 1) →
      (∀ i∈S, H i ≤ N) →
      let base := fun i => (s:ℝ)-2*(N:ℝ)+(N:ℝ)*(k i:ℝ)
      (∀ i∈S, Icc (base i-(7*(N:ℝ)+2)) (base i+(7*(N:ℝ)+2)) ⊆ Icc A B) →
      ∃ r : ι → ℚ,
        (∀ Q₀ : ℕ, 2 ≤ Q₀ →
          let D₀ := 8/(L*(N:ℝ)*(Q₀:ℝ))
          ((S.filter (fun i => Q₀ ≤ (r i).den)).card:ℝ) ≤
            4*(X+1)*D₀^2+D₀*(2+Real.log (D₀+1))) ∧
        (∀ j : ℕ,
          let Q : ℕ := 2^(j+1)
          let G := (S.filter (fun i => (r i).den ≤ N)).filter (fun i => Nat.log 2 (r i).den=j)
          let Z := (G.card:ℝ)
          let Zd := 4*(Q:ℝ)*(2*X*Q+1)
          let D := 16/(L*(N:ℝ)*(Q:ℝ))
          let Err := Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+6/(L*(N:ℝ)^2)+
            Real.sqrt (12/(L*(N:ℝ)*Q))
          Z ≤ Zd ∧
          (1 ≤ j → Z ≤ 4*(X+1)*D^2+D*(2+Real.log (D+1))) ∧
          (∑ i∈G, ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖) ≤
            Cd*Zd*(3*(N:ℝ)*Real.sqrt (3*U*(Q:ℝ)*N)+Err) ∧
          (12 ≤ L*(Q:ℝ)*(N:ℝ)^2 → 384 ≤ L^2*(Q:ℝ)^3*(N:ℝ)^3 →
            let M : ℕ := ⌈63*U*(Q:ℝ)*(N:ℝ)^2⌉₊+1
            let V := 756*U/L
            let W := 1+32/(L*(Q:ℝ)^2*N)
            let d := L*(Q:ℝ)*N/12
            let Loss := (5*W)^11*W^2*(6*(3+8*Real.pi*V)*(1+Real.log M))^12*
              (2/d)^6*(M:ℝ)^((12:ℝ)+ε)
            let D₀ := (Real.sqrt M/(9*(M:ℝ))+Real.sqrt M/(12*(M:ℝ)^2))*
              Real.sqrt (U*(Q:ℝ)^3)
            let η := 4*D₀/(Q:ℝ)
            let rho := (12*U*Real.sqrt (U*(Q:ℝ)^3)/lam)*(Real.sqrt M/(6*(M:ℝ)^2))
            let K := ⌈3*U*(rho+1)⌉₊
            let Rmax := 36*U^2/lam
            let Dmax := (K:ℝ)/L+1
            let Dweight := 144*U^2/(lam*N)
            let Count := Cp*((2*η+w)*Dmax+20736*F4*U^4/(lam^2*L^2)+
              (T/P^2)^(k₀+ε)*Dmax^(l₀+ε)*w^(-(k₀+ε))+P^2/T)
            let Pair := 4*Z+6*Count*(3*(K:ℝ)+Dweight*(harmonic K:ℝ))
            (Q:ℝ)^2 < 6*(M:ℝ)^2 →
            2*η+10368*F4*U^4/(lam^2*L) ≤ 1/2 →
            P < A-Rmax → B+Rmax+2*Dmax < 2*P →
            2*(K:ℝ)*P^2/(σ*T) ≤ κ₀ →
            (∑ i∈G, ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖)^12 ≤
              Cf*(Loss*(2*Z)^10*Pair+(Z*Err)^12))) := by
  classical
  obtain ⟨δ₀,κ₀,hδ₀,hκ₀,Qphase,hQphase,Cf,hCf,Cp,hCp,hfrozenSource⟩ :=
    exists_model_refined_frozen_source hσ hpair hε hp
  obtain ⟨δd,hδd,hdata⟩ := model_displacement_derivative_data hσ
  obtain ⟨Cd,hCd,hdirect⟩ := exists_bourgain_C4_low_denominator_source
  refine ⟨min δ₀ δd,κ₀,lt_min hδ₀ hδd,hκ₀,Qphase,hQphase,Cd,hCd,Cf,hCf,Cp,hCp,?_⟩
  intro ι _ S F T P k H N s A B w hF hT hP hN hw hwhalf hA hB
    f L U lam F4 X hUsmall hLsmall hfourSmall hquadSmall hmul hH base hbuffer
  have hF₀ := approximateModelPhase_mono hF le_rfl (min_le_left _ _)
  have hFd := approximateModelPhase_mono hF hQphase (min_le_right _ _)
  obtain ⟨hreg,hthreeModel,hfourModel,hcurvModel⟩ := hdata F T P hT hP hFd
  have hlam : 0 < lam := by dsimp only [lam]; positivity [modelPhaseJetLower_pos hσ 3]
  have hL : 0 < L := by dsimp only [L]; positivity [modelPhaseJetLower_pos hσ 2]
  have hU : 0 < U := by dsimp only [U]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  have hF4 : 0 ≤ F4 := by dsimp only [F4]; positivity [modelPhaseJetCoefficient_pos hσ 3]
  have hX : 0 ≤ X := by dsimp only [X]; positivity [modelPhaseJetCoefficient_pos hσ 1]
  have hdomain : Icc A B ⊆ Ioo P (2*P) := by
    intro t ht
    exact ⟨hA.trans_le ht.1,ht.2.trans_lt hB⟩
  have hf₄ t (ht : t∈Icc A B) : ContDiffAt ℝ 4 f t :=
    (hreg t (hdomain ht)).of_le (by norm_num)
  have hthree t (ht : t∈Icc A B) :
      L ≤ iteratedDeriv 3 f t ∧ iteratedDeriv 3 f t ≤ 6*U := by
    have hh := hthreeModel t (hdomain ht)
    exact ⟨hh.1,by linarith [hh.2]⟩
  have hfourAbs t (ht : t∈Icc A B) : |iteratedDeriv 4 f t| ≤ F4 := by
    have hh := hfourModel t (hdomain ht)
    rw [abs_of_neg (by linarith only [hh.2,hlam])]
    linarith only [hh.1]
  have hcurv t (ht : t∈Icc A B) : |iteratedDeriv 2 f t/2| ≤ X :=
    hcurvModel t (hdomain ht)
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have ht i (hi : i∈S) : base i∈Icc A B :=
    hbuffer i hi ⟨by linarith only [hNr],by linarith only [hNr]⟩
  obtain ⟨r,z,hr,htail₀⟩ := exists_bourgain_C3_minimal_curvature_arc_count S f k N 1
    ((s:ℝ)-2*(N:ℝ)) hN hL hX
    (fun t ht => (hf₄ t ht).of_le (by norm_num)) (fun t ht => (hthree t ht).1) hmul
    (by
      intro i hi x hx
      apply hbuffer i hi
      change base i-(N:ℝ)/4 ≤ x ∧ x ≤ base i+(N:ℝ)/4 at hx
      constructor <;> linarith only [hx.1,hx.2,hNr])
    (fun i hi => hcurv _ (ht i hi))
  have hgeo i (hi : i∈S) : z i∈Ioo A B ∧ |z i-(round (z i):ℝ)| ≤ 1/2 ∧
      ((N:ℤ) ≤ s+(N:ℤ)*k i-round (z i) ∧
        s+(N:ℤ)*k i-round (z i) ≤ 3*(N:ℤ)) ∧
      Icc ((round (z i):ℝ)-(6*(N:ℝ)+1)) ((round (z i):ℝ)+(6*(N:ℝ)+1)) ⊆ Icc A B := by
    have hz := (hr i hi).1
    change z i∈Ioo (base i-(N:ℝ)/4) (base i+(N:ℝ)/4) at hz
    have hround : |z i-(round (z i):ℝ)| ≤ 1/2 := abs_sub_round (z i)
    have hround' := abs_le.mp hround
    have hlo := (hbuffer i hi (left_mem_Icc.mpr (by linarith only [hNr]))).1
    have hhi := (hbuffer i hi (right_mem_Icc.mpr (by linarith only [hNr]))).2
    have hstart : ((s+(N:ℤ)*k i:ℤ):ℝ)=base i+2*(N:ℝ) := by
      dsimp only [base]; push_cast; ring
    refine ⟨⟨by linarith only [hlo,hz.1,hNr],by linarith only [hhi,hz.2,hNr]⟩,hround,?_,?_⟩
    · have hlow : (N:ℝ) ≤ ((s+(N:ℤ)*k i:ℤ):ℝ)-(round (z i):ℝ) := by
        linarith only [hz.1,hz.2,hround'.1,hround'.2,hstart,hNr]
      have hhigh : ((s+(N:ℤ)*k i:ℤ):ℝ)-(round (z i):ℝ) ≤ 3*(N:ℝ) := by
        linarith only [hz.1,hz.2,hround'.1,hround'.2,hstart,hNr]
      constructor
      · exact_mod_cast hlow
      · exact_mod_cast hhigh
    · intro x hx
      apply hbuffer i hi
      constructor <;> linarith only [hx.1,hx.2,hz.1,hz.2,hround'.1,hround'.2,hNr]
  have hlevel i (hi : i∈S) : iteratedDeriv 2 f (z i)/2=(r i:ℝ) := (hr i hi).2.1
  have htail (Q₀ : ℕ) (hQ₀ : 2≤Q₀) :
      let D₀ := 8/(L*(N:ℝ)*(Q₀:ℝ))
      ((S.filter (fun i => Q₀ ≤ (r i).den)).card:ℝ) ≤
        4*(X+1)*D₀^2+D₀*(2+Real.log (D₀+1)) := by
    simpa only [Nat.cast_one,one_mul] using htail₀ Q₀ hQ₀
  refine ⟨r,htail,?_⟩
  intro j Q G Z Zd D Err
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hGS : G ⊆ S := fun i hi =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
  have hmulG n : (G.filter (fun i => k i=n)).card ≤ 1 :=
    (Finset.card_le_card (Finset.filter_subset_filter _ hGS)).trans (hmul n)
  have hqdata i (hi : i∈G) :
      (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧ (r i).den ≤ N := by
    obtain ⟨hi',hj⟩ := Finset.mem_filter.mp hi
    have hlo := Nat.pow_log_le_self 2 (r i).pos.ne'
    have hhi := Nat.lt_pow_succ_log_self (by norm_num : 1<(2:ℕ)) (r i).den
    rw [hj] at hlo hhi
    refine ⟨hhi.le,?_,(Finset.mem_filter.mp hi').2⟩
    calc
      Q=2*2^j := by dsimp only [Q]; rw [pow_succ,Nat.mul_comm]
      _ ≤ _ := Nat.mul_le_mul_left _ hlo
  have hdir := hdirect ι G f r z (fun i => round (z i)) k H N Q 1 s A B L F4 U X
    hN hQ hL hF4 hU hX hfourSmall hquadSmall hf₄ hthree hfourAbs
    (fun i hi => (hgeo i (hGS hi)).1)
    (fun i hi => (hgeo i (hGS hi)).2.2.2)
    (fun i hi => (hgeo i (hGS hi)).2.1)
    (fun i hi => (hgeo i (hGS hi)).2.2.1)
    hmulG (fun i hi => hH i (hGS hi)) hqdata
    (fun i hi => hlevel i (hGS hi))
    (fun i hi => hcurv _ ⟨(hgeo i (hGS hi)).1.1.le,(hgeo i (hGS hi)).1.2.le⟩)
  dsimp only at hdir
  simp only [Nat.cast_one,mul_one] at hdir
  refine ⟨hdir.1,?_,?_,?_⟩
  · intro hj
    have htwo : 2 ≤ 2^j := by simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:ℕ)) hj
    have hsubset : G ⊆ S.filter (fun i => 2^j ≤ (r i).den) := by
      intro i hi
      apply Finset.mem_filter.mpr
      refine ⟨hGS hi,?_⟩
      have hh := Nat.pow_log_le_self 2 (r i).pos.ne'
      rw [(Finset.mem_filter.mp hi).2] at hh
      exact hh
    have hh := (Nat.cast_le.mpr (Finset.card_le_card hsubset)).trans (htail (2^j) htwo)
    have he : 8/(L*(N:ℝ)*(2^j:ℕ))=D := by
      dsimp only [D,Q]
      rw [pow_succ,Nat.cast_mul,Nat.cast_ofNat]
      ring
    simpa only [he] using hh
  · dsimp only [Err,Zd]
    convert hdir.2 using 1
    ring
  · intro hdual hfrozen M V Wloss d Loss D₀ η rho K Rmax Dmax Dweight Count Pair
      hthin hliftSmall hleft hright hκle
    have hs := hfrozenSource ι G F T P r z (fun i => round (z i)) k H N Q 1 s A B w
      hF₀ hT hP hN hQ hw hwhalf hUsmall hLsmall hfourSmall hquadSmall
      (fun i hi => (hgeo i (hGS hi)).1)
      (fun i hi => (hgeo i (hGS hi)).2.2.2)
      (fun i hi => (hgeo i (hGS hi)).2.1)
      (fun i hi => (hgeo i (hGS hi)).2.2.1)
      hmulG (fun i hi => hH i (hGS hi)) hqdata
      (fun i hi => hlevel i (hGS hi)) hdual hfrozen hthin hliftSmall hleft hright hκle
    simpa only [Nat.cast_one,mul_one,one_pow] using hs
end TaoTrudgianYang2025.CubicJointCount

