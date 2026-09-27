import TaoTrudgianYang2025.SquareProductCount
import TaoTrudgianYang2025.BetaStationaryMain
import TaoTrudgianYang2025.DyadicMomentCutoff

noncomputable section
open Set Expdb GafniTao Filter Topology
open scoped BigOperators FourierTransform NNReal
namespace TaoTrudgianYang2025.CubicScalePrototype
open TaoTrudgianYang2025.CubicJointCount

/-- Original-model eighth-power estimate from the literal C4 reduction
and the proved joint derivative count. Every C4/third-derivative hypothesis
is derived from the same original model phase. -/
theorem exists_original_cubic_eighth_estimate
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 3 ≤ Q ∧ ∃ C : ℝ, 0 < C ∧
        ∀ (F : ℝ → ℝ) (T N Y : ℝ) (A : ℤ) (M H J : ℕ),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 2 ≤ H → 2 ≤ Y →
          let lam := modelPhaseJetLower σ 3*T/N^4
          let B := (modelPhaseJetCoefficient σ 3+1)*T/N^4
          let L := modelPhaseJetLower σ 2*T/N^3
          let U := (modelPhaseJetCoefficient σ 2+1)*T/N^3
          let Qcut := 3/(2*lam*(H:ℝ)^3)
          1 ≤ Qcut → Qcut ≤ (2:ℝ)^J →
          N < (A:ℝ)+1-(H:ℝ)^2 → (A:ℝ)+M+(H:ℝ)^2+2*Qcut < 2*N →
          1/(4*(H:ℝ)^2) ≤ L/4 → 4*U*Qcut*N^2/(σ*T) ≤ κ₀ →
          B*((H:ℝ)+1)^4 ≤ 1 →
          let E := ((J:ℝ)+2)*(U/(lam*(H:ℝ)^2))*
            (1+B/(lam^2*(H:ℝ)^4)+Qcut/(H:ℝ)+Qcut/Y+
              (T/N^2)^(k₀+ε)*Qcut^(l₀+ε)*Y^(k₀+ε)+N^2/T)
          ‖∑ m∈Finset.range M,
            fordAdditiveCharacter (T*F (((A:ℝ)+(m:ℝ)+1)/N))‖^8 ≤
              C*((M:ℝ)^6*((M:ℝ)+E)*(1+U*(H:ℝ)^2)*(H:ℝ)^ε+(H:ℝ)^8) := by
  obtain ⟨δ₀,κ₀,hδ₀,hκ₀,Q₀,hQ₀,C₀,hC₀,hcount⟩ :=
    original_cubicDerivativePairs_count hσ hpair hε hp
  obtain ⟨δd,hδd,hdata⟩ := model_displacement_derivative_data hσ
  obtain ⟨C₁,hC₁,hsource⟩ := SquareProductCount.CubicSource.exists_C4_source_eighth_reduction hε
  let δ := min δ₀ δd
  let Q := max Q₀ 3
  let C := C₁*(1+2*C₀)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨δ,κ₀,lt_min hδ₀ hδd,hκ₀,Q,le_max_right _ _,C,hC,?_⟩
  intro F T N Y A M H J hF hT hN hH hY lam B L U Qcut hQcut hQpow hleft hright hδL hshift hTaylor E
  have hF₀ := approximateModelPhase_mono hF (le_max_left _ _) (min_le_left _ _)
  have hFd := approximateModelPhase_mono hF (le_max_right _ _) (min_le_right _ _)
  obtain ⟨hreg,hthree,hfour,_hsecondabs⟩ := hdata F T N hT hN hFd
  let f := fun x => T*F (x/N)
  let g := fun x => f ((A:ℝ)+x)
  have hHr : (2:ℝ) ≤ H := by exact_mod_cast hH
  have hHpos : (0:ℝ) < H := by linarith only [hHr]
  have hlam : 0 < lam := by dsimp [lam]; positivity [modelPhaseJetLower_pos hσ 3]
  have hL : 0 < L := by dsimp [L]; positivity [modelPhaseJetLower_pos hσ 2]
  have hU : 0 < U := by dsimp [U]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  have hB : 0 < B := by dsimp [B]; positivity [modelPhaseJetCoefficient_pos hσ 3]
  have hQpos : 0 < Qcut := zero_lt_one.trans_le hQcut
  have hder (j : ℕ) (x : ℝ) : iteratedDeriv j g x=iteratedDeriv j f ((A:ℝ)+x) :=
    congrFun (iteratedDeriv_comp_const_add j f (A:ℝ)) x
  have hHbuf : (H:ℝ)+1 ≤ (H:ℝ)^2 := by nlinarith only [hHr]
  have hpoint (m : ℕ) (hm : m∈Finset.range M) (y : ℝ)
      (hy : y∈Icc ((m:ℝ)-H) ((m:ℝ)+H+2)) : (A:ℝ)+y∈Ioo N (2*N) := by
    have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg _
    have hmM : (m:ℝ)+1 ≤ M := by
      exact_mod_cast (show m+1≤M by have := Finset.mem_range.mp hm; omega)
    constructor <;> linarith only [hy.1,hy.2,hm0,hmM,hHbuf,hleft,hright,hQpos]
  have hg (m : ℕ) (hm : m∈Finset.range M) (y : ℝ)
      (hy : y∈Icc ((m:ℝ)-H) ((m:ℝ)+H+2)) : ContDiffAt ℝ 4 g y := by
    exact ((hreg ((A:ℝ)+y) (hpoint m hm y hy)).comp y
      (show ContDiffAt ℝ 5 (fun z : ℝ => (A:ℝ)+z) y by fun_prop)).of_le (by norm_num)
  have hfour' (m : ℕ) (hm : m∈Finset.range M) (y : ℝ)
      (hy : y∈Icc ((m:ℝ)-H) ((m:ℝ)+H+2)) : |iteratedDeriv 4 g y| ≤ B := by
    rw [hder]
    have hh := hfour ((A:ℝ)+y) (hpoint m hm y hy)
    apply abs_le.mpr
    exact ⟨hh.1,by linarith only [hh.2,hlam,hB]⟩
  have hthree' (m : ℕ) (hm : m∈Finset.range M) :
      iteratedDeriv 3 g ((m:ℝ)+1)/6∈Icc (0:ℝ) (0+U/6) := by
    rw [hder]
    have hcenter : (m:ℝ)+1∈Icc ((m:ℝ)-H) ((m:ℝ)+H+2) := by
      constructor <;> linarith only [hHpos]
    have hh := hthree ((A:ℝ)+((m:ℝ)+1)) (hpoint m hm ((m:ℝ)+1) hcenter)
    constructor <;> linarith only [hh.1,hh.2,hL]
  have hnear := hcount F T N Y A M H J hF₀ hT hN hH hY hQcut hQpow hleft hright hδL hshift
  have hsum := hsource g M H (by omega) B 0 (U/6) hB.le (by positivity)
    hTaylor hg hfour' hthree'
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hnear' : ((SquareProductCount.CubicSource.cubicDerivativePairs g M H).card:ℝ) ≤
      (1+2*C₀)*((M:ℝ)+E) := by
    have hh : ((SquareProductCount.CubicSource.cubicDerivativePairs g M H).card:ℝ) ≤
        (M:ℝ)+2*C₀*E := by
      convert hnear using 1
      dsimp [E]
      ring
    have hm : (0:ℝ) ≤ M := Nat.cast_nonneg _
    have hx : 0 ≤ 2*C₀*(M:ℝ) := by positivity
    nlinarith only [hh,hE,hx]
  have hUwidth : 1+(U/6)*(H:ℝ)^2 ≤ 1+U*(H:ℝ)^2 := by
    nlinarith only [mul_nonneg hU.le (sq_nonneg (H:ℝ))]
  have hb : ‖∑ m∈Finset.range M, fordAdditiveCharacter (g ((m:ℝ)+1))‖^8 ≤
      C*((M:ℝ)^6*((M:ℝ)+E)*(1+U*(H:ℝ)^2)*(H:ℝ)^ε+(H:ℝ)^8) := by
    calc
      _ ≤ C₁*((M:ℝ)^6*(SquareProductCount.CubicSource.cubicDerivativePairs g M H).card*
          (1+(U/6)*(H:ℝ)^2)*(H:ℝ)^ε+(H:ℝ)^8) := hsum
      _ ≤ C₁*((M:ℝ)^6*((1+2*C₀)*((M:ℝ)+E))*(1+U*(H:ℝ)^2)*(H:ℝ)^ε+(H:ℝ)^8) := by gcongr
      _ ≤ C₁*((1+2*C₀)*((M:ℝ)^6*((M:ℝ)+E)*(1+U*(H:ℝ)^2)*(H:ℝ)^ε+(H:ℝ)^8)) := by
        apply mul_le_mul_of_nonneg_left _ hC₁.le
        nlinarith only [mul_nonneg (show 0 ≤ 2*C₀ by positivity) (pow_nonneg hHpos.le 8)]
      _ = _ := by dsimp [C]; ring
  simpa only [g,f,add_assoc] using hb

#print axioms exists_original_cubic_eighth_estimate


/-- Trimming both ends of a literal source interval loses only its removed
unit-modulus terms, including the original closed left endpoint. -/
theorem cubic_source_trim
    (z : ℕ → ℂ) (hz : ∀ n, ‖z n‖ ≤ 1) (a b K : ℕ)
    (hab : a+2*K ≤ b) :
    ‖∑ n∈Finset.Icc a b, z n‖ ≤
      ‖∑ m∈Finset.range (b-a-2*K), z (a+K+m+1)‖+2*(K:ℝ)+1 := by
  let M := b-a-2*K
  have he : b-a+1=((K+1)+M)+K := by dsimp [M]; omega
  rw [RiemannZeta.GuthMaynard.sum_Icc_eq_shifted_range z a b (by omega),he,
    Finset.sum_range_add,Finset.sum_range_add]
  have hleft : ‖∑ i∈Finset.range (K+1), z (a+i)‖ ≤ (K:ℝ)+1 := by
    calc
      _ ≤ ∑ i∈Finset.range (K+1), ‖z (a+i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i∈Finset.range (K+1), (1:ℝ) := Finset.sum_le_sum (fun i _ => hz (a+i))
      _ = _ := by simp
  have hright : ‖∑ i∈Finset.range K, z (a+((K+1)+M+i))‖ ≤ (K:ℝ) := by
    calc
      _ ≤ ∑ i∈Finset.range K, ‖z (a+((K+1)+M+i))‖ := norm_sum_le _ _
      _ ≤ ∑ _i∈Finset.range K, (1:ℝ) := Finset.sum_le_sum (fun i _ => hz _)
      _ = _ := by simp
  have hmid : (∑ i∈Finset.range M, z (a+(K+1+i))) =
      ∑ i∈Finset.range M, z (a+K+i+1) := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    omega
  rw [hmid]
  have htriangle := norm_add_le
    ((∑ i∈Finset.range (K+1), z (a+i))+
      ∑ i∈Finset.range M, z (a+K+i+1))
    (∑ i∈Finset.range K, z (a+((K+1)+M+i)))
  have htriangle₂ := norm_add_le (∑ i∈Finset.range (K+1), z (a+i))
    (∑ i∈Finset.range M, z (a+K+i+1))
  dsimp [M] at htriangle
  dsimp [M] at htriangle₂
  linarith only [htriangle,htriangle₂,hleft,hright]

#print axioms exists_original_cubic_eighth_estimate
#print axioms cubic_source_trim

/-- The physical eighth-power bound for the complete closed source sum.
The discarded endpoints are chosen here, not supplied as an assumption. -/
theorem exists_complete_cubic_eighth_estimate
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 3 ≤ Q ∧ ∃ C : ℝ, 0 < C ∧
        ∀ (F : ℝ → ℝ) (T N Y : ℝ) (a b H J : ℕ),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 2 ≤ H → 2 ≤ Y →
          N ≤ a → (b:ℝ) ≤ 2*N →
          let lam := modelPhaseJetLower σ 3*T/N^4
          let B := (modelPhaseJetCoefficient σ 3+1)*T/N^4
          let L := modelPhaseJetLower σ 2*T/N^3
          let U := (modelPhaseJetCoefficient σ 2+1)*T/N^3
          let Qcut := 3/(2*lam*(H:ℝ)^3)
          1 ≤ Qcut → Qcut ≤ (2:ℝ)^J →
          1/(4*(H:ℝ)^2) ≤ L/4 → 4*U*Qcut*N^2/(σ*T) ≤ κ₀ →
          B*((H:ℝ)+1)^4 ≤ 1 →
          let E := ((J:ℝ)+2)*(U/(lam*(H:ℝ)^2))*
            (1+B/(lam^2*(H:ℝ)^4)+Qcut/(H:ℝ)+Qcut/Y+
              (T/N^2)^(k₀+ε)*Qcut^(l₀+ε)*Y^(k₀+ε)+N^2/T)
          ‖exponentialSumAt F T N a b‖^8 ≤
            C*(N^6*(N+E)*(1+U*(H:ℝ)^2)*(H:ℝ)^ε+
              (H:ℝ)^8+((H:ℝ)^2+Qcut+1)^8) := by
  classical
  obtain ⟨δ,κ₀,hδ,hκ₀,Q,hQ,C₀,hC₀,hsource⟩ :=
    exists_original_cubic_eighth_estimate hσ hpair hε hp
  let C := 128*(C₀+5^8+1)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨δ,κ₀,hδ,hκ₀,Q,hQ,C,hC,?_⟩
  intro F T N Y a b H J hF hT hN hH hY ha hb lam B L U Qcut hQcut hQpow hδL hshift hTaylor E
  let R := (H:ℝ)^2+Qcut+1
  let K : ℕ := ⌈(H:ℝ)^2+2*Qcut+1⌉₊
  have hKlo : (H:ℝ)^2+2*Qcut+1 ≤ K := Nat.le_ceil _
  have hQpos : 0 < Qcut := zero_lt_one.trans_le hQcut
  have hKhi : (K:ℝ) < (H:ℝ)^2+2*Qcut+2 := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ (H:ℝ)^2+2*Qcut+1 by positivity)
    convert hh using 1
    ring
  have hR : 0 < R := by dsimp [R]; positivity
  have hboundary : 2*(K:ℝ)+1 ≤ 5*R := by
    dsimp [R]
    nlinarith only [hKhi,sq_nonneg (H:ℝ),hQpos]
  have hE : 0 ≤ E := by dsimp [E,U,lam,B]; positivity [modelPhaseJetLower_pos hσ 3,
    modelPhaseJetCoefficient_pos hσ 2,modelPhaseJetCoefficient_pos hσ 3]
  have hU : 0 < U := by dsimp [U]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  let Z := N^6*(N+E)*(1+U*(H:ℝ)^2)*(H:ℝ)^ε+(H:ℝ)^8
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hmajor : 128*(C₀*Z+5^8*R^8) ≤ C*(Z+R^8) := by
    dsimp [C]
    nlinarith only [hZ,pow_nonneg hR.le 8,
      mul_nonneg hC₀.le (pow_nonneg hR.le 8)]
  by_cases hab : a+2*K ≤ b
  · let M := b-a-2*K
    let A : ℤ := (a:ℤ)+(K:ℤ)
    have hAr : (A:ℝ)=(a:ℝ)+(K:ℝ) := by dsimp [A]; push_cast; rfl
    have hM : (M:ℝ)=(b:ℝ)-(a:ℝ)-2*(K:ℝ) := by
      dsimp [M]
      push_cast [Nat.cast_sub (show 2*K≤b-a by omega),Nat.cast_sub (show a≤b by omega)]
      ring
    have hMN : (M:ℝ) ≤ N := by
      rw [hM]
      linarith only [ha,hb,(Nat.cast_nonneg K : (0:ℝ) ≤ K)]
    have hleft : N < (A:ℝ)+1-(H:ℝ)^2 := by
      rw [hAr]
      linarith only [ha,hKlo,hQpos]
    have hright : (A:ℝ)+M+(H:ℝ)^2+2*Qcut < 2*N := by
      rw [hAr,hM]
      linarith only [hb,hKlo]
    have hc := hsource F T N Y A M H J hF hT hN hH hY hQcut hQpow
      hleft hright hδL hshift hTaylor
    let S := ∑ m∈Finset.range M, fordAdditiveCharacter (T*F (((A:ℝ)+(m:ℝ)+1)/N))
    have hc' : ‖S‖^8 ≤ C₀*Z := by
      refine hc.trans ?_
      dsimp [Z]
      gcongr
    have htrim := cubic_source_trim (fun n => oscillatory F T N n)
      (fun n => (norm_oscillatory F T N n).le) a b K hab
    have hmid : (∑ m∈Finset.range (b-a-2*K), oscillatory F T N ((a+K+m+1:ℕ):ℝ))=S := by
      apply Finset.sum_congr rfl
      intro m _
      simp only [sargos_ford_character_eq_fourier,oscillatory,Nat.cast_add,Nat.cast_one,hAr]
    have hnorm : ‖exponentialSumAt F T N a b‖ ≤ ‖S‖+5*R := by
      rw [hmid] at htrim
      change ‖exponentialSumAt F T N a b‖ ≤ _ at htrim
      linarith only [htrim,hboundary]
    have hpow := (pow_le_pow_left₀ (norm_nonneg _) hnorm 8).trans
      (add_pow_le (norm_nonneg S) (by positivity : 0 ≤ 5*R) 8)
    rw [mul_pow] at hpow
    change ‖exponentialSumAt F T N a b‖^8 ≤ C*(Z+R^8)
    exact (hpow.trans (by norm_num; gcongr)).trans hmajor
  · have hnorm : ‖exponentialSumAt F T N a b‖ ≤ 5*R := by
      have hh := norm_exponentialSumAt_le_card F T N a b
      have hcard : ((Finset.Icc a b).card:ℝ) ≤ 2*(K:ℝ)+1 := by
        have hn : (Finset.Icc a b).card ≤ 2*K+1 := by rw [Nat.card_Icc]; omega
        exact_mod_cast hn
      exact (hh.trans hcard).trans hboundary
    have hp := pow_le_pow_left₀ (norm_nonneg _) hnorm 8
    rw [mul_pow] at hp
    change ‖exponentialSumAt F T N a b‖^8 ≤ C*(Z+R^8)
    exact hp.trans ((by nlinarith only [mul_nonneg hC₀.le hZ,pow_nonneg hR.le 8] :
      5^8*R^8 ≤ 128*(C₀*Z+5^8*R^8)).trans hmajor)

#print axioms exists_complete_cubic_eighth_estimate

/-- Fixed real powers preserve the already-proved ANTEDB scale semantics. -/
private theorem cubic_power_rpow
    {X T : VariableObject ℝ} {a : ℝ}
    (hX : IsPowerAsymptotic X T a) (hT : ∀ i, 1 ≤ T i) (p : ℝ) :
    IsPowerAsymptotic (fun i => (X i)^p) T (a*p) := by
  obtain ⟨e,he,hXe⟩ := hX
  refine ⟨fun i => e i*p,?_,?_⟩
  · convert he.const_smul p using 1
    · funext i
      exact mul_comm (e i) p
    · funext i
      exact mul_comm a p
  · filter_upwards [hXe] with i hi
    rw [hi,← Real.rpow_mul (zero_le_one.trans (hT i))]

private theorem cubic_power_natpow
    {X T : VariableObject ℝ} {a : ℝ}
    (hX : IsPowerAsymptotic X T a) (hT : ∀ i, 1 ≤ T i) (n : ℕ) :
    IsPowerAsymptotic (fun i => (X i)^n) T (a*(n:ℝ)) := by
  simpa only [Real.rpow_natCast] using cubic_power_rpow hX hT (n:ℝ)

private theorem cubic_power_const
    {T : VariableObject ℝ} (hT : ∀ i, 1 ≤ T i) (hTunbounded : T.IsUnbounded)
    {c : ℝ} (hc : 0 < c) :
    IsPowerAsymptotic (fun _ => c) T 0 := by
  have hTtop : Tendsto T atTop atTop :=
    (VariableObject.isUnbounded_iff_tendsto_atTop
      (fun i => zero_le_one.trans (hT i))).mp hTunbounded
  apply isPowerAsymptotic_of_logb_tendsto
    (hTtop.eventually (eventually_gt_atTop 1)) (Filter.Eventually.of_forall (fun _ => hc))
  simpa only [Real.logb] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => Real.log c) atTop (𝓝 (Real.log c))).div_atTop
      (Real.tendsto_log_atTop.comp hTtop)

private theorem cubic_power_eventually_le
    {X T : VariableObject ℝ} {a b : ℝ}
    (hX : IsPowerAsymptotic X T a) (hT : ∀ i, 1 ≤ T i) (hab : a < b) :
    ∀ᶠ i in atTop, X i ≤ (T i)^b := by
  have hh := hX.eventually_between (Filter.Eventually.of_forall hT)
    (sub_pos.mpr hab)
  filter_upwards [hh] with i hi
  convert hi.2 using 1
  congr 1
  ring

/-- The existing dyadic cutoff has subpower block-count cost; its actual
integer index remains linked to the physical cutoff. -/
private theorem cubic_dyadic_index_bound
    {T X : VariableObject ℝ} (hT : ∀ i, 1 ≤ T i) (hTunbounded : T.IsUnbounded)
    {q η : ℝ} (hq : 0 < q) (hη : 0 < η)
    (hX : ∀ᶠ i in atTop, 1 ≤ X i ∧ X i ≤ (T i)^q) :
    ∀ᶠ i in atTop, ∃ J : ℕ, X i ≤ (2:ℝ)^J ∧ (J:ℝ)+2 ≤ (T i)^η := by
  let γ := η/(2*q)
  have hγ : 0 < γ := by dsimp [γ]; positivity
  obtain ⟨D,hD,hcount⟩ := exists_dyadic_count_sq_le_rpow hγ
  have hTtop : Tendsto T atTop atTop :=
    (VariableObject.isUnbounded_iff_tendsto_atTop
      (fun i => zero_le_one.trans (hT i))).mp hTunbounded
  have hconstant := hTtop.eventually (eventually_const_mul_rpow_le_rpow
    (D := 2*D*(2:ℝ)^γ) (a := η/2) (b := η) (by linarith))
  filter_upwards [hX,hconstant] with i hi hconst
  obtain ⟨J,hJlo,hJhi⟩ := exists_dyadic_cutoff hi.1
  refine ⟨J,hJlo,?_⟩
  have hJ := hcount J
  have hj : (J:ℝ)+2 ≤ 2*((J:ℝ)+1)^2 := by
    nlinarith only [(Nat.cast_nonneg J : (0:ℝ) ≤ J),sq_nonneg (J:ℝ)]
  have hTp : 0 < T i := zero_lt_one.trans_le (hT i)
  calc
    _ ≤ 2*(D*((2:ℝ)^J)^γ) := hj.trans (by gcongr)
    _ ≤ 2*(D*(2*(T i)^q)^γ) := by gcongr; exact hJhi.trans (by gcongr; exact hi.2)
    _ = (2*D*2^γ)*(T i)^(η/2) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity),
        ← Real.rpow_mul hTp.le]
      have he : q*γ=η/2 := by dsimp [γ]; field_simp
      rw [he]
      ring
    _ ≤ _ := hconst

/-- Actual integer Taylor scales and physical Fourier scales satisfy every
remaining analytic side condition throughout the missing Bourgain interval. -/
theorem eventually_cubic_bourgain_parameters
    {T N : VariableObject ℝ} {α σ κ₀ η : ℝ}
    (hlo : 140/391 ≤ α) (hhi : α < 16/39) (hσ : 0 < σ)
    (hκ₀ : 0 < κ₀) (hη : 0 < η)
    (hT : ∀ i, 1 ≤ T i) (hTunbounded : T.IsUnbounded)
    (hNT : IsPowerAsymptotic N T α) :
    let h := (246*α-55)/398
    let r := (362*α-123)/398
    let H := floorRpow T h
    let Y := fun i => (T i)^r
    let lam := fun i => modelPhaseJetLower σ 3*T i/(N i)^4
    let B := fun i => (modelPhaseJetCoefficient σ 3+1)*T i/(N i)^4
    let L := fun i => modelPhaseJetLower σ 2*T i/(N i)^3
    let U := fun i => (modelPhaseJetCoefficient σ 2+1)*T i/(N i)^3
    let Qcut := fun i => 3/(2*lam i*(H i:ℝ)^3)
    ∀ᶠ i in atTop, 0 < N i ∧ 2 ≤ H i ∧ 2 ≤ Y i ∧
      ∃ J : ℕ, 1 ≤ Qcut i ∧ Qcut i ≤ (2:ℝ)^J ∧ (J:ℝ)+2 ≤ (T i)^η ∧
        1/(4*(H i:ℝ)^2) ≤ L i/4 ∧
        4*U i*Qcut i*(N i)^2/(σ*T i) ≤ κ₀ ∧
        B i*((H i:ℝ)+1)^4 ≤ 1 := by
  intro h r H Y lam B L U Qcut
  let q := 4*α-1-3*h
  have hh : 0 < h := by dsimp [h]; linarith only [hlo]
  have hr : 0 < r := by dsimp [r]; linarith only [hlo]
  have hq : 0 < q := by dsimp [q,h]; linarith only [hlo]
  have hTscale := isPowerAsymptotic_self T
  have hH : IsPowerAsymptotic (fun i => (H i:ℝ)) T h :=
    isPowerAsymptotic_floorRpow hh hT hTunbounded
  have hY : IsPowerAsymptotic Y T r := by
    simpa using cubic_power_rpow hTscale hT r
  have hc (c : ℝ) (hc : 0 < c) := cubic_power_const hT hTunbounded hc
  have hlam : IsPowerAsymptotic lam T (1-4*α) := by
    convert ((hc _ (modelPhaseJetLower_pos hσ 3)).mul hTscale hT).div
      (cubic_power_natpow hNT hT 4) hT using 1
    ring
  have hB : IsPowerAsymptotic B T (1-4*α) := by
    convert ((hc (modelPhaseJetCoefficient σ 3+1) (by positivity [modelPhaseJetCoefficient_pos hσ 3])).mul hTscale hT).div
      (cubic_power_natpow hNT hT 4) hT using 1
    ring
  have hL : IsPowerAsymptotic L T (1-3*α) := by
    convert ((hc _ (modelPhaseJetLower_pos hσ 2)).mul hTscale hT).div
      (cubic_power_natpow hNT hT 3) hT using 1
    ring
  have hU : IsPowerAsymptotic U T (1-3*α) := by
    convert ((hc (modelPhaseJetCoefficient σ 2+1) (by positivity [modelPhaseJetCoefficient_pos hσ 2])).mul hTscale hT).div
      (cubic_power_natpow hNT hT 3) hT using 1
    ring
  have hQ : IsPowerAsymptotic Qcut T q := by
    convert (hc 3 (by norm_num)).div
      (((hc 2 (by norm_num)).mul hlam hT).mul (cubic_power_natpow hH hT 3) hT) hT using 1
    dsimp [q]
    ring
  have hLH : IsPowerAsymptotic (fun i => L i*(H i:ℝ)^2) T (1-3*α+2*h) := by
    convert hL.mul (cubic_power_natpow hH hT 2) hT using 1
    ring
  have hshift : IsPowerAsymptotic (fun i => 4*U i*Qcut i*(N i)^2/(σ*T i)) T (q-α) := by
    convert ((((hc 4 (by norm_num)).mul hU hT).mul hQ hT).mul
      (cubic_power_natpow hNT hT 2) hT).div ((hc σ hσ).mul hTscale hT) hT using 1
    ring
  have htaylor : IsPowerAsymptotic (fun i => 16*B i*(H i:ℝ)^4) T (1-4*α+4*h) := by
    convert ((hc 16 (by norm_num)).mul hB hT).mul
      (cubic_power_natpow hH hT 4) hT using 1
    ring
  have hNlarge := (hNT.tendsto_atTop_of_pos
    (by linarith only [hlo] : 0 < α) hT hTunbounded).eventually (eventually_gt_atTop 0)
  have hHlarge := (hH.tendsto_atTop_of_pos hh hT hTunbounded).eventually
    (eventually_ge_atTop 2)
  have hYlarge := (hY.tendsto_atTop_of_pos hr hT hTunbounded).eventually
    (eventually_ge_atTop 2)
  have hQlarge := (hQ.tendsto_atTop_of_pos hq hT hTunbounded).eventually
    (eventually_ge_atTop 1)
  have hLHlarge := (hLH.tendsto_atTop_of_pos
    (by dsimp [h]; linarith only [hhi] : 0 < 1-3*α+2*h) hT hTunbounded).eventually
    (eventually_ge_atTop 1)
  have hshiftsmall := (hshift.tendsto_zero_of_neg
    (by dsimp [q,h]; linarith only [hhi] : q-α < 0) hT hTunbounded).eventually
    (eventually_lt_nhds hκ₀)
  have htaylorsmall := (htaylor.tendsto_zero_of_neg
    (by dsimp [h]; linarith only [hlo] : 1-4*α+4*h < 0) hT hTunbounded).eventually
    (eventually_lt_nhds (by norm_num : (0:ℝ) < 1))
  have hindex := cubic_dyadic_index_bound hT hTunbounded
    (by linarith only [hq] : 0 < q+1) hη
    (hQlarge.and (cubic_power_eventually_le hQ hT (by linarith : q<q+1)))
  filter_upwards [hNlarge,hHlarge,hYlarge,hLHlarge,hshiftsmall,htaylorsmall,hindex,hQlarge]
    with i hNi hHi hYi hLHi hsi hti hJi hQi
  obtain ⟨J,hJq,hJcount⟩ := hJi
  refine ⟨hNi,by exact_mod_cast hHi,hYi,J,hQi,hJq,hJcount,?_,hsi.le,?_⟩
  · have hHp : (0:ℝ) < H i := by linarith only [hHi]
    apply (div_le_iff₀ (by positivity : 0 < 4*(H i:ℝ)^2)).mpr
    nlinarith only [hLHi]
  · have hBp : 0 < B i := by
      dsimp [B]
      positivity [modelPhaseJetCoefficient_pos hσ 3,zero_lt_one.trans_le (hT i)]
    have hsum : (H i:ℝ)+1 ≤ 2*(H i:ℝ) := by linarith only [hHi]
    have hp := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (H i:ℝ)+1) hsum 4
    have hm := mul_le_mul_of_nonneg_left hp hBp.le
    nlinarith only [hm,hti]

#print axioms eventually_cubic_bourgain_parameters

/-- The actual closed-source majorant has the D(Bourgain) exponent.
Both independent scales and the complete dyadic cost remain explicit. -/
theorem eventually_cubic_bourgain_cost
    {T N : VariableObject ℝ} {α σ η : ℝ}
    (hlo : 140/391 ≤ α) (hhi : α < 16/39) (hσ : 0 < σ) (hη : 0 < η)
    (hT : ∀ i, 1 ≤ T i) (hTunbounded : T.IsUnbounded)
    (hNT : IsPowerAsymptotic N T α) :
    let h := (246*α-55)/398
    let r := (362*α-123)/398
    let β := 18/199+(521/796)*α
    let H := floorRpow T h
    let Y := fun i => (T i)^r
    let lam := fun i => modelPhaseJetLower σ 3*T i/(N i)^4
    let B := fun i => (modelPhaseJetCoefficient σ 3+1)*T i/(N i)^4
    let U := fun i => (modelPhaseJetCoefficient σ 2+1)*T i/(N i)^3
    let Qcut := fun i => 3/(2*lam i*(H i:ℝ)^3)
    ∀ᶠ i in atTop, ∀ J : ℕ, (J:ℝ)+2 ≤ (T i)^η →
      let E := ((J:ℝ)+2)*(U i/(lam i*(H i:ℝ)^2))*
        (1+B i/((lam i)^2*(H i:ℝ)^4)+Qcut i/(H i:ℝ)+Qcut i/Y i+
          (T i/(N i)^2)^(13/84+η)*(Qcut i)^(55/84+η)*(Y i)^(13/84+η)+(N i)^2/T i)
      (N i)^6*(N i+E)*(1+U i*(H i:ℝ)^2)*(H i:ℝ)^η+
          (H i:ℝ)^8+((H i:ℝ)^2+Qcut i+1)^8 ≤
        (15+3^8)*(T i)^(8*β+5*η) := by
  intro h r β H Y lam B U Qcut
  let q := 4*α-1-3*h
  let V := fun i => U i/(lam i*(H i:ℝ)^2)
  let f₁ := fun i => V i/N i
  let f₂ := fun i => V i*(B i/((lam i)^2*(H i:ℝ)^4))/N i
  let f₃ := fun i => V i*(Qcut i/(H i:ℝ))/N i
  let f₄ := fun i => V i*(Qcut i/Y i)/N i
  let f₅ := fun i => V i*((T i/(N i)^2)^(13/84+η)*(Qcut i)^(55/84+η)*(Y i)^(13/84+η))/N i
  let f₆ := fun i => V i*((N i)^2/T i)/N i
  have hh : 0 < h := by dsimp [h]; linarith only [hlo]
  have hTscale := isPowerAsymptotic_self T
  have hH : IsPowerAsymptotic (fun i => (H i:ℝ)) T h :=
    isPowerAsymptotic_floorRpow hh hT hTunbounded
  have hY : IsPowerAsymptotic Y T r := by simpa using cubic_power_rpow hTscale hT r
  have hc (c : ℝ) (hc : 0 < c) := cubic_power_const hT hTunbounded hc
  have hlam : IsPowerAsymptotic lam T (1-4*α) := by
    convert ((hc _ (modelPhaseJetLower_pos hσ 3)).mul hTscale hT).div
      (cubic_power_natpow hNT hT 4) hT using 1
    ring
  have hB : IsPowerAsymptotic B T (1-4*α) := by
    convert ((hc (modelPhaseJetCoefficient σ 3+1)
      (by positivity [modelPhaseJetCoefficient_pos hσ 3])).mul hTscale hT).div
      (cubic_power_natpow hNT hT 4) hT using 1
    ring
  have hU : IsPowerAsymptotic U T (1-3*α) := by
    convert ((hc (modelPhaseJetCoefficient σ 2+1)
      (by positivity [modelPhaseJetCoefficient_pos hσ 2])).mul hTscale hT).div
      (cubic_power_natpow hNT hT 3) hT using 1
    ring
  have hQ : IsPowerAsymptotic Qcut T q := by
    convert (hc 3 (by norm_num)).div
      (((hc 2 (by norm_num)).mul hlam hT).mul (cubic_power_natpow hH hT 3) hT) hT using 1
    dsimp [q]
    ring
  have hV : IsPowerAsymptotic V T (α-2*h) := by
    convert hU.div (hlam.mul (cubic_power_natpow hH hT 2) hT) hT using 1
    ring
  have hf₁ : IsPowerAsymptotic f₁ T (-2*h) := by
    convert hV.div hNT hT using 1
    ring
  have hf₂ : IsPowerAsymptotic f₂ T (4*α-1-6*h) := by
    convert (hV.mul (hB.div ((cubic_power_natpow hlam hT 2).mul
      (cubic_power_natpow hH hT 4) hT) hT) hT).div hNT hT using 1
    ring
  have hf₃ : IsPowerAsymptotic f₃ T (4*α-1-6*h) := by
    convert (hV.mul (hQ.div hH hT) hT).div hNT hT using 1
    dsimp [q]
    ring
  have hf₄ : IsPowerAsymptotic f₄ T 0 := by
    convert (hV.mul (hQ.div hY hT) hT).div hNT hT using 1
    dsimp [q,h,r]
    ring
  have hf₅ : IsPowerAsymptotic f₅ T (η*(1-2*α+q+r)) := by
    convert (hV.mul (((cubic_power_rpow (hTscale.div
      (cubic_power_natpow hNT hT 2) hT) hT (13/84+η)).mul
        (cubic_power_rpow hQ hT (55/84+η)) hT).mul
          (cubic_power_rpow hY hT (13/84+η)) hT) hT).div hNT hT using 1
    dsimp [q,h,r]
    ring
  have hf₆ : IsPowerAsymptotic f₆ T (2*α-1-2*h) := by
    convert (hV.mul ((cubic_power_natpow hNT hT 2).div hTscale hT) hT).div hNT hT using 1
    ring
  have hmain : IsPowerAsymptotic
      (fun i => (N i)^7*U i*(H i:ℝ)^2*(H i:ℝ)^η) T (8*β+h*η) := by
    convert (((cubic_power_natpow hNT hT 7).mul hU hT).mul
      (cubic_power_natpow hH hT 2) hT).mul (cubic_power_rpow hH hT η) hT using 1
    dsimp [β,h]
    ring
  have hwidth : IsPowerAsymptotic (fun i => U i*(H i:ℝ)^2) T (1-3*α+2*h) := by
    convert hU.mul (cubic_power_natpow hH hT 2) hT using 1
    ring
  have hqβ : q < β := by dsimp [q,h,β]; linarith only [hlo,hhi]
  have h2hβ : 2*h < β := by dsimp [h,β]; linarith only [hlo,hhi]
  have hhβ : h < β := by linarith only [hh,h2hβ]
  have hβ : 0 < β := by linarith only [hh,hhβ]
  have he₂ : 4*α-1-6*h ≤ 0 := by dsimp [h]; linarith only [hhi]
  have he₆ : 2*α-1-2*h < 0 := by dsimp [h]; linarith only [hhi]
  have he₅ : 1-2*α+q+r < 1 := by dsimp [q,h,r]; linarith only [hhi]
  have hh1 : h < 1 := by dsimp [h]; linarith only [hhi]
  have hb₁ := cubic_power_eventually_le hf₁ hT (by linarith only [hh,hη] : -2*h<2*η)
  have hb₂ := cubic_power_eventually_le hf₂ hT (by linarith only [he₂,hη] : 4*α-1-6*h<2*η)
  have hb₃ := cubic_power_eventually_le hf₃ hT (by linarith only [he₂,hη] : 4*α-1-6*h<2*η)
  have hb₄ := cubic_power_eventually_le hf₄ hT (by linarith only [hη] : 0<2*η)
  have hb₅ := cubic_power_eventually_le hf₅ hT
    (by nlinarith only [he₅,hη] : η*(1-2*α+q+r)<2*η)
  have hb₆ := cubic_power_eventually_le hf₆ hT (by linarith only [he₆,hη] : 2*α-1-2*h<2*η)
  have hbmain := cubic_power_eventually_le hmain hT
    (by nlinarith only [hh1,hη] : 8*β+h*η<8*β+2*η)
  have hbH := cubic_power_eventually_le hH hT hhβ
  have hbH₂ := cubic_power_eventually_le (cubic_power_natpow hH hT 2) hT
    (by linarith only [h2hβ] : h*2<β)
  have hbQ := cubic_power_eventually_le hQ hT hqβ
  have hbwidth := (hwidth.tendsto_atTop_of_pos
    (by dsimp [h]; linarith only [hhi] : 0 < 1-3*α+2*h) hT hTunbounded).eventually
      (eventually_ge_atTop 1)
  have hNlarge := (hNT.tendsto_atTop_of_pos
    (by linarith only [hlo] : 0 < α) hT hTunbounded).eventually (eventually_gt_atTop 0)
  filter_upwards [hb₁,hb₂,hb₃,hb₄,hb₅,hb₆,hbmain,hbH,hbH₂,hbQ,hbwidth,hNlarge]
    with i h₁ h₂ h₃ h₄ h₅ h₆ hm hHi hH₂i hQi hwi hNi
  intro J hJ E
  have hTi : 0 < T i := zero_lt_one.trans_le (hT i)
  have hHp : (0:ℝ) < H i := by exact_mod_cast floorRpow_pos T h i
  have hUp : 0 < U i := by dsimp [U]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  have hlampos : 0 < lam i := by dsimp [lam]; positivity [modelPhaseJetLower_pos hσ 3]
  have hQp : 0 < Qcut i := by dsimp [Qcut]; positivity
  have hVp : 0 < V i := by dsimp [V]; positivity
  have hsum : f₁ i+f₂ i+f₃ i+f₄ i+f₅ i+f₆ i ≤ 6*(T i)^(2*η) := by
    linarith only [h₁,h₂,h₃,h₄,h₅,h₆]
  have heq : E=((J:ℝ)+2)*N i*(f₁ i+f₂ i+f₃ i+f₄ i+f₅ i+f₆ i) := by
    dsimp [E,f₁,f₂,f₃,f₄,f₅,f₆,V]
    field_simp
  have hE : E ≤ 6*N i*(T i)^(3*η) := by
    rw [heq]
    calc
      _ ≤ ((J:ℝ)+2)*N i*(6*(T i)^(2*η)) := by gcongr
      _ ≤ (T i)^η*N i*(6*(T i)^(2*η)) := by gcongr
      _ = _ := by
        rw [show (T i)^η*N i*(6*(T i)^(2*η)) =
          6*N i*((T i)^η*(T i)^(2*η)) by ring,← Real.rpow_add hTi]
        congr 2
        ring
  have hone₃ : 1 ≤ (T i)^(3*η) := Real.one_le_rpow (hT i) (by positivity)
  have hNE : N i+E ≤ 7*N i*(T i)^(3*η) := by
    have hn := mul_le_mul_of_nonneg_left hone₃ hNi.le
    nlinarith only [hE,hn]
  have hUW : 1+U i*(H i:ℝ)^2 ≤ 2*U i*(H i:ℝ)^2 := by linarith only [hwi]
  have hcost : (N i)^6*(N i+E)*(1+U i*(H i:ℝ)^2)*(H i:ℝ)^η ≤
      14*(T i)^(8*β+5*η) := by
    calc
      _ ≤ (N i)^6*(7*N i*(T i)^(3*η))*(2*U i*(H i:ℝ)^2)*(H i:ℝ)^η := by gcongr
      _ = 14*((N i)^7*U i*(H i:ℝ)^2*(H i:ℝ)^η)*(T i)^(3*η) := by ring
      _ ≤ 14*(T i)^(8*β+2*η)*(T i)^(3*η) := by gcongr
      _ = _ := by rw [mul_assoc,← Real.rpow_add hTi]; congr 2; ring
  have honeβ : 1 ≤ (T i)^β := Real.one_le_rpow (hT i) hβ.le
  have hR : (H i:ℝ)^2+Qcut i+1 ≤ 3*(T i)^β := by
    linarith only [hH₂i,hQi,honeβ]
  have hH8 : (H i:ℝ)^8 ≤ (T i)^(8*β+5*η) := by
    calc
      _ ≤ ((T i)^β)^8 := pow_le_pow_left₀ hHp.le hHi 8
      _ = (T i)^(8*β) := by rw [← Real.rpow_mul_natCast hTi.le]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (hT i) (by linarith only [hη])
  have hR8 : ((H i:ℝ)^2+Qcut i+1)^8 ≤ 3^8*(T i)^(8*β+5*η) := by
    calc
      _ ≤ (3*(T i)^β)^8 := pow_le_pow_left₀ (by positivity) hR 8
      _ = 3^8*(T i)^(8*β) := by
        rw [mul_pow,← Real.rpow_mul_natCast hTi.le]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (hT i) (by linarith only [hη])) (by norm_num)
  linarith only [hcost,hH8,hR8]

#print axioms eventually_cubic_bourgain_cost

/-- Analytic closure of the missing D(Bourgain) interval. This consumes the
literal original sum, the proved Bourgain pair, and the linked physical
scales; no derivative-count or sum estimate is an input. -/
theorem isExponentSumBound_cubic_bourgain_gap
    {α : ℝ≥0} (hlo : 140/391 ≤ (α:ℝ)) (hhi : (α:ℝ) < 16/39) :
    IsExponentSumBound α (18/199+(521/796)*(α:ℝ)) := by
  intro N T F a b _hN hT hTunbounded hNT hF hab
  apply (isPowerBounded_iff_forall_pos
    (exponentialSum F T N a b) T (18/199+(521/796)*(α:ℝ)) hT hTunbounded).mpr
  intro ε hε
  let η := min ((1:ℝ)/100) ε
  have hη : 0 < η := lt_min (by norm_num) hε
  have hηε : η ≤ ε := min_le_right _ _
  have hηsmall : (13/84:ℝ)+η < 1 := by
    have hh : η ≤ (1:ℝ)/100 := min_le_left _ _
    linarith only [hh]
  obtain ⟨hphase,σ,hσ,herror⟩ := hF
  obtain ⟨δ,κ₀,hδ,hκ₀,Q,_hQ,C₀,hC₀,hsource⟩ :=
    TaoTrudgianYang2025.CubicJointCount.exists_complete_cubic_eighth_estimate
      hσ exponentPair_bourgain hη hηsmall
  have happrox := (IsModelPhaseFunctionWith.mk hphase herror).eventually_isApproximate Q hδ
  have hparameters := eventually_cubic_bourgain_parameters hlo hhi hσ hκ₀ hη hT hTunbounded hNT
  have hcost := eventually_cubic_bourgain_cost hlo hhi hσ hη hT hTunbounded hNT
  let β := 18/199+(521/796)*(α:ℝ)
  let C := max 1 (C₀*(15+3^8))
  have hC : 1 ≤ C := le_max_left _ _
  have hC₀C : C₀*(15+3^8) ≤ C := le_max_right _ _
  have hCpow : C ≤ C^8 := by
    calc
      C = C*1 := (mul_one C).symm
      _ ≤ C*C^7 := mul_le_mul_of_nonneg_left (one_le_pow₀ hC) (zero_le_one.trans hC)
      _ = _ := by ring
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [happrox,hparameters,hcost] with i hFi hpi hci
  obtain ⟨hNi,hHi,hYi,J,hQi,hQJ,hJ,hcurv,hshift,hTaylor⟩ := hpi
  have hTi : 0 < T i := zero_lt_one.trans_le (hT i)
  have hs := hsource (F i) (T i) (N i)
    ((T i)^((362*(α:ℝ)-123)/398)) (a i) (b i)
    (floorRpow T ((246*(α:ℝ)-55)/398) i) J
    hFi hTi hNi hHi hYi (hab i).1 (hab i).2
    hQi hQJ hcurv hshift hTaylor
  have hmajor := mul_le_mul_of_nonneg_left (hci J hJ) hC₀.le
  have hbound : ‖exponentialSumAt (F i) (T i) (N i) (a i) (b i)‖^8 ≤
      C₀*(15+3^8)*(T i)^(8*β+5*η) := by
    exact hs.trans (by convert hmajor using 1; ring)
  have hexp : 8*β+5*η ≤ (β+ε)*8 := by linarith only [hηε,hε]
  have hp : ‖exponentialSumAt (F i) (T i) (N i) (a i) (b i)‖^8 ≤
      (C*(T i)^(β+ε))^8 := by
    calc
      _ ≤ C₀*(15+3^8)*(T i)^(8*β+5*η) := hbound
      _ ≤ C^8*(T i)^((β+ε)*8) :=
        mul_le_mul (hC₀C.trans hCpow) (Real.rpow_le_rpow_of_exponent_le (hT i) hexp)
          (Real.rpow_nonneg hTi.le _) (by positivity)
      _ = _ := by rw [mul_pow,← Real.rpow_mul_natCast hTi.le]; norm_num
  have hh := (pow_le_pow_iff_left₀ (norm_nonneg _)
    (by positivity : 0 ≤ C*(T i)^(β+ε)) (by norm_num : (8:ℕ)≠0)).mp hp
  simpa only [exponentialSum_apply,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hTi.le _)] using hh

theorem exponentSumGrowthExponent_le_cubic_bourgain_gap
    {α : ℝ≥0} (hlo : 140/391 ≤ (α:ℝ)) (hhi : (α:ℝ) < 16/39) :
    exponentSumGrowthExponent α ≤ 18/199+(521/796)*(α:ℝ) :=
  exponentSumGrowthExponent_le_iff.mpr (isExponentSumBound_cubic_bourgain_gap hlo hhi)

#print axioms isExponentSumBound_cubic_bourgain_gap
#print axioms exponentSumGrowthExponent_le_cubic_bourgain_gap
/-- The already proved analytic inputs cover the D(Bourgain) target outside
one exact open interval. No estimate on that remaining interval is assumed. -/
theorem bourgain_d_target_outside_gap
    {α : NNReal} (hhalf : (α:ℝ) ≤ 1/2)
    (hgap : (α:ℝ) ≤ 140/391 ∨ 16/39 ≤ (α:ℝ)) :
    exponentSumGrowthExponent α ≤ (18:ℝ)/199+521/796*(α:ℝ) := by
  rcases hgap with hlo | hhi
  · have h := exponentSumGrowthExponent_le_exponentPairLine_closed
      exponentPair_robertSargos α (by linarith only [hhalf])
    unfold exponentPairLine at h
    linarith only [h,hlo]
  · by_cases hfirst : (α:ℝ) ≤ 5/12
    · have h := TaoTrudgianYang2025.exponentSumGrowthExponent_le_bourgain_table_first
        (α:=α) (by linarith only [hhi]) hfirst
      linarith only [h,hhi]
    · by_cases hsecond : (α:ℝ) ≤ 3/7
      · have h := TaoTrudgianYang2025.exponentSumGrowthExponent_le_bourgain_table_second
          (α:=α) (le_of_not_ge hfirst) hsecond
        linarith only [h,hhalf]
      · have h := exponentSumGrowthExponent_le_bourgain_baseline
          (α:=α) (le_of_not_ge hsecond) hhalf
        have hα : (3:ℝ)/7 ≤ (α:ℝ) := le_of_not_ge hsecond
        linarith only [h,hα]

theorem exponentPair_sargosD_bourgain : ExponentPair (18/199) (593/796) := by
  apply exponentPair_of_beta_bound_half (by norm_num [InExponentPairTriangle]) (by norm_num)
  intro α hhalf
  have hbound : exponentSumGrowthExponent α ≤ 18/199+(521/796)*(α:ℝ) := by
    by_cases hlo : (α:ℝ) ≤ 140/391
    · exact bourgain_d_target_outside_gap hhalf (Or.inl hlo)
    · by_cases hhi : (α:ℝ) < 16/39
      · exact exponentSumGrowthExponent_le_cubic_bourgain_gap (le_of_not_ge hlo) hhi
      · exact bourgain_d_target_outside_gap hhalf (Or.inr (le_of_not_gt hhi))
  convert hbound using 1
  unfold exponentPairLine
  ring

example : exponentSumGrowthExponent (2/5) ≤ (701:ℝ)/1990 := by
  have h := exponentSumGrowthExponent_le_cubic_bourgain_gap (α:=2/5) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

example : exponentSumGrowthExponent (140/391) ≤ (127:ℝ)/391 := by
  have h := exponentSumGrowthExponent_le_cubic_bourgain_gap (α:=140/391) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

example : exponentSumGrowthExponent (16/39) ≤ (14:ℝ)/39 := by
  have h := bourgain_d_target_outside_gap (α:=16/39) (by norm_num) (Or.inr (by norm_num))
  norm_num at h ⊢
  exact h

#print axioms bourgain_d_target_outside_gap
#print axioms exponentPair_sargosD_bourgain

theorem exponentPair_sargosAD_bourgain : ExponentPair (9/217) (1461/1736) := by
  have h := exponentPair_sargosD_bourgain.aProcess
  norm_num at h
  exact h

theorem exponentSumGrowthExponent_le_sargosD_bourgain
    {α : ℝ≥0} (hα : (α:ℝ) ≤ 1) :
    exponentSumGrowthExponent α ≤ 18/199+(521/796)*(α:ℝ) := by
  have h := exponentSumGrowthExponent_le_exponentPairLine_closed exponentPair_sargosD_bourgain α hα
  convert h using 1
  unfold exponentPairLine
  ring

theorem exponentSumGrowthExponent_le_sargosAD_bourgain
    {α : ℝ≥0} (hα : (α:ℝ) ≤ 1) :
    exponentSumGrowthExponent α ≤ 9/217+(1389/1736)*(α:ℝ) := by
  have h := exponentSumGrowthExponent_le_exponentPairLine_closed exponentPair_sargosAD_bourgain α hα
  convert h using 1
  unfold exponentPairLine
  ring

#print axioms exponentPair_sargosAD_bourgain
#print axioms exponentSumGrowthExponent_le_sargosD_bourgain
#print axioms exponentSumGrowthExponent_le_sargosAD_bourgain
end TaoTrudgianYang2025.CubicScalePrototype
