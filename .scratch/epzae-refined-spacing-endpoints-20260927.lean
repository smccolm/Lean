import TaoTrudgianYang2025.SquareProductCount
noncomputable section
open Set Expdb
open scoped Topology ContDiff BigOperators NNReal FourierTransform
namespace TaoTrudgianYang2025.CubicJointCount

/-- Closed-source trimming preserves both endpoints and charges every removed term. -/
theorem refined_integer_source_trim
    (g : ℤ→ℂ) (hg : ∀ n, ‖g n‖≤1) {a b : ℤ} {K : ℕ}
    (hab : a+2*(K:ℤ)≤b) :
    ‖∑ n∈Finset.Icc a b,g n‖≤
      ‖∑ n∈Finset.Ioc (a+K) (b-K),g n‖+2*(K:ℝ)+1 := by
  have hlo : a≤a+K := by omega
  have hmid : a+(K:ℤ)≤b-K := by omega
  have hhi : b-(K:ℤ)≤b := by omega
  rw [←Finset.add_sum_Ioc_eq_sum_Icc (show a≤b by omega)]
  rw [sargos_integer_Ioc_sum_split g hlo (hmid.trans hhi),
    sargos_integer_Ioc_sum_split g hmid hhi]
  have hleft := norm_sum_integer_Ioc_le g hg hlo
  have hright := norm_sum_integer_Ioc_le g hg hhi
  have hnorm₁ := norm_add_le (g a)
    ((∑ n∈Finset.Ioc a (a+K),g n)+
      ((∑ n∈Finset.Ioc (a+K) (b-K),g n)+(∑ n∈Finset.Ioc (b-K) b,g n)))
  have hnorm₂ := norm_add_le (∑ n∈Finset.Ioc a (a+K),g n)
    ((∑ n∈Finset.Ioc (a+K) (b-K),g n)+(∑ n∈Finset.Ioc (b-K) b,g n))
  have hnorm₃ := norm_add_le (∑ n∈Finset.Ioc (a+K) (b-K),g n)
    (∑ n∈Finset.Ioc (b-K) b,g n)
  push_cast at hleft hright
  linarith only [hnorm₁,hnorm₂,hnorm₃,hleft,hright,hg a]

/-- The refined estimate reaches the literal closed original source sum.
Short intervals and the two removed endpoint strips are included. -/
theorem exists_model_refined_global_bound
    {σ k₀ l₀ ε : ℝ} (hσ : 0<σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0<ε) (hp : k₀+ε<1) :
    let u := modelPhaseJetCoefficient σ 2+1
    let l := modelPhaseJetLower σ 2/u
    let a := modelPhaseJetLower σ 3/u
    let b := (modelPhaseJetCoefficient σ 3+1)/u
    let n := 2+48/a
    ∃ δ κ₀ : ℝ, 0<δ ∧ 0<κ₀ ∧
      ∃ Qphase : ℕ, 3≤Qphase ∧ ∃ C > (0:ℝ),
      ∀ (F : ℝ→ℝ) (T P : ℝ) (aa bb : ℕ) (w : ℝ),
      IsApproximateModelPhaseFunction F σ Qphase δ →
      0<T → 0<P → P≤aa → (bb:ℝ)≤2*P → 0<w → w≤1/2 →
      let U := u*T/P^3
      U≤1/3600 → 1≤P*U*Real.sqrt U → b≤P*U → l*U≤1 →
      P*U^2≤1 → 8*Real.sqrt U+(10368*b/(a^2*l))*(P*U^2)≤1/2 →
      (2*n*u/σ)*Real.sqrt U≤κ₀ →
      ‖exponentialSumAt F T P aa bb‖^12 ≤
        C*P^ε*(1+Real.log P)^36*
          (P^11*U+w*P^12*U^((5:ℝ)/2)+
            P^(11+(k₀+ε)+(l₀+ε))*U^(2+(k₀+ε)+(l₀+ε)/2)*w^(-(k₀+ε))) := by
  classical
  intro u l a b n
  let m := 36/a+2*(n/l+1)+1
  have hu : 0<u := by dsimp only [u]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  have hl : 0<l := by dsimp only [l]; positivity [modelPhaseJetLower_pos hσ 2]
  have ha : 0<a := by dsimp only [a]; positivity [modelPhaseJetLower_pos hσ 3]
  have hn : 0<n := by dsimp only [n]; positivity
  have hm : 0 < m := by dsimp only [m]; positivity
  obtain ⟨δ,κ₀,hδ,hκ₀,Qphase,hQphase,Cf,hCf,hsource⟩ :=
    exists_model_refined_source_global hσ hpair hε hp
  let Ctrim := 2*m+3
  have hCtrim : 0<Ctrim := by dsimp only [Ctrim]; positivity
  let C := 2^11*(Cf+Ctrim^12)
  have hC : 0<C := by dsimp only [C]; positivity
  refine ⟨δ,κ₀,hδ,hκ₀,Qphase,hQphase,C,hC,?_⟩
  intro F T P aa bb w hF hT hP haa hbb hw hwhalf U
    hUsmall hKscale hbPU hLsmall hsmall hlift hκ
  have hU : 0<U := by dsimp only [U]; positivity
  have hU1 : U≤1 := by linarith only [hUsmall]
  have hscale := displacement_block_physical_scale hP hU hUsmall hKscale
  let N := ⌊1/(10*Real.sqrt U)⌋₊
  have hN : 0<N := (displacement_block_scale hU hUsmall).1
  let K := ⌈m*(P*Real.sqrt U)⌉₊
  let E := P^11*U+w*P^12*U^((5:ℝ)/2)+
    P^(11+(k₀+ε)+(l₀+ε))*U^(2+(k₀+ε)+(l₀+ε)/2)*w^(-(k₀+ε))
  let Log := 1+Real.log P
  let Budget := P^ε*Log^36*E
  have hLog1 : 1≤Log := by
    have hh := Real.log_nonneg hscale.2.1
    dsimp only [Log]
    linarith only [hh]
  have hLog : 0<Log := zero_lt_one.trans_le hLog1
  have hE : 0≤E := by dsimp only [E]; positivity
  have hBudget : 0≤Budget := by dsimp only [Budget]; positivity
  have hFirst : P^11*U≤E := by
    have hmid : 0≤w*P^12*U^((5:ℝ)/2) := by positivity
    have hlast : 0≤P^(11+(k₀+ε)+(l₀+ε))*U^(2+(k₀+ε)+(l₀+ε)/2)*w^(-(k₀+ε)) := by positivity
    dsimp only [E]
    linarith only [hmid,hlast]
  have hPS : 1≤P*Real.sqrt U := hKscale.trans (by
    calc
      _ ≤ P*1*Real.sqrt U := by gcongr
      _ = _ := by ring)
  have hKlo : m*(P*Real.sqrt U)≤(K:ℝ) := Nat.le_ceil _
  have hKhi : (K:ℝ) ≤ m*(P*Real.sqrt U)+1 :=
    (Nat.ceil_lt_add_one (show 0 ≤ m*(P*Real.sqrt U) by positivity)).le
  have htrimBound : 2*(K:ℝ)+1≤Ctrim*P*Real.sqrt U := by
    dsimp only [Ctrim]
    nlinarith only [hKhi,hPS]
  have htrimMoment : (2*(K:ℝ)+1)^12≤Ctrim^12*Budget := by
    have hh : 2*(K:ℝ)+1≤Ctrim*P*U^((1:ℝ)/2)*Log^2 := by
      rw [←Real.sqrt_eq_rpow]
      exact htrimBound.trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hLog1))
    have he := refined_elementary_twelfth hscale.2.1 hU hU1 (by positivity)
      hCtrim.le hLog1 hε.le (by norm_num : (1:ℝ)/4≤1/2) hsmall hh
    calc
      _ ≤ Ctrim^12*P^ε*Log^24*(P^11*U) := he
      _ ≤ Ctrim^12*P^ε*Log^36*E := by gcongr; norm_num
      _ = _ := by simp only [Budget,mul_assoc]
  by_cases hlong : aa+2*K≤bb
  · let A : ℤ := (aa:ℤ)+K
    let B : ℤ := (bb:ℤ)-K
    let g := fun t : ℤ => (𝐞 (T*F ((t:ℝ)/P)):ℂ)
    have hg (t : ℤ) : ‖g t‖≤1 := by dsimp only [g]; simp
    have hAB : A≤B := by dsimp only [A,B]; omega
    obtain ⟨S,hbuffer,_,hblocks⟩ := exists_buffered_integer_source_blocks_interval g hg
      hAB (le_refl (A:ℝ)) (le_refl (B:ℝ)) N hN
    have hmul (j : ℤ) : (S.filter (fun k : ℕ => (k:ℤ)=j)).card≤1 := by
      apply Finset.card_le_one.mpr
      intro v hv z hz
      have hv' := (Finset.mem_filter.mp hv).2
      have hz' := (Finset.mem_filter.mp hz).2
      exact_mod_cast hv'.trans hz'.symm
    have hA : P+m*(P*Real.sqrt U)<(A:ℝ)+1/2 := by
      dsimp only [A]
      push_cast
      linarith only [haa,hKlo]
    have hB : (B:ℝ)-1/2+m*(P*Real.sqrt U)<2*P := by
      dsimp only [B]
      push_cast
      linarith only [hbb,hKlo]
    have hs := hsource ℕ S F T P (fun k => (k:ℤ)) (fun _ => N) A
      ((A:ℝ)+1/2) ((B:ℝ)-1/2) w hF hT hP hw hwhalf
      hUsmall hKscale hbPU hLsmall hsmall hlift hκ hA hB hmul (fun _ _ => le_rfl)
      (by simpa only [Int.cast_natCast] using hbuffer)
    let Core := 1+23*(N:ℝ)+∑ k∈S, ‖∑ t∈Finset.Ioc (A+(N:ℤ)*k) (A+(N:ℤ)*k+N),g t‖
    have hCore : 0≤Core := by dsimp only [Core]; positivity
    change Core^12≤Cf*P^ε*Log^36*E at hs
    have hs' : Core^12≤Cf*Budget := by simpa only [Budget,mul_assoc] using hs
    have ht := refined_integer_source_trim g hg (a:=(aa:ℤ)) (b:=(bb:ℤ)) (K:=K)
      (by exact_mod_cast hlong)
    have hnorm : ‖exponentialSumAt F T P aa bb‖≤Core+(2*(K:ℝ)+1) := by
      rw [exponentialSumAt_eq_int_sum]
      change ‖∑ t∈Finset.Icc (aa:ℤ) (bb:ℤ),g t‖≤_
      change ‖∑ t∈Finset.Icc (aa:ℤ) (bb:ℤ),g t‖≤‖∑ t∈Finset.Ioc A B,g t‖+2*(K:ℝ)+1 at ht
      dsimp only [Core]
      linarith only [ht,hblocks]
    have hp₀ := (pow_le_pow_left₀ (norm_nonneg _) hnorm 12).trans
      (add_pow_le hCore (by positivity : 0≤2*(K:ℝ)+1) 12)
    have hm := mul_le_mul_of_nonneg_left (add_le_add hs' htrimMoment)
      (show (0:ℝ)≤2^(12-1) by positivity)
    exact hp₀.trans (by
      rw [←add_mul,←mul_assoc] at hm
      simpa only [C,Budget,Log,E,mul_assoc,Nat.reduceSub] using hm)
  · have hnorm : ‖exponentialSumAt F T P aa bb‖≤2*(K:ℝ)+1 := by
      have hc : ((Finset.Icc aa bb).card:ℝ)≤2*(K:ℝ)+1 := by
        have hh : (Finset.Icc aa bb).card≤2*K+1 := by rw [Nat.card_Icc]; omega
        exact_mod_cast hh
      exact (norm_exponentialSumAt_le_card F T P aa bb).trans hc
    have hCtrimC : Ctrim^12≤C := by
      exact (le_add_of_nonneg_left hCf.le).trans
        (le_mul_of_one_le_left (by positivity) (by norm_num : (1:ℝ)≤2^11))
    exact ((pow_le_pow_left₀ (norm_nonneg _) hnorm 12).trans htrimMoment).trans
      (by
        simpa only [Budget,Log,E,mul_assoc] using mul_le_mul_of_nonneg_right hCtrimC hBudget)

end TaoTrudgianYang2025.CubicJointCount
