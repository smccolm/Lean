import TaoTrudgianYang2025.BetaUniformity
import TaoTrudgianYang2025.ExponentPairShiftUniformity
import TaoTrudgianYang2025.ExponentPairSourceCorrelation
import TaoTrudgianYang2025.ExponentPairDifferencingBound
import TaoTrudgianYang2025.HuxleyLinearForms
import TaoTrudgianYang2025.SquareProductCount

/-! Local beta uniformity for the short-range A-process. The input is a
proved beta bound on a compact interval, not an assumed transformed pair. -/

noncomputable section
open Set Expdb TaoTrudgianYang2025
open scoped NNReal
namespace LocalBetaAProcessScratch

private theorem uniform_model_sum_of_beta_interval
    {lo hi b c : ℝ} (hlo : 0≤lo) (hlohi : lo≤hi) (hc : 0≤c) (hc₁ : c≤4)
    (hβ : ∀ α : ℝ≥0, (α:ℝ)∈Icc lo hi →
      exponentSumGrowthExponent α≤b+c*(α:ℝ))
    {σ ε : ℝ} (hσ : 0<σ) (hε : 0<ε) :
    ∃ δ : ℝ, 0<δ ∧ ∃ P : ℕ, 1≤P ∧ ∃ C : ℝ, 1≤C ∧
      ∀ (T N : ℝ) (F : ℝ→ℝ) (a z : ℕ),
        C≤T → 0<N → Real.logb T N∈Icc lo hi →
        IsApproximateModelPhaseFunction F σ P δ →
        N≤(a:ℝ) → (z:ℝ)≤2*N →
        ‖exponentialSumAt F T N a z‖≤C*T^(b+c*Real.logb T N+ε) := by
  classical
  have hlocal (α : Icc lo hi) :
      ∃ δ : ℝ, 0<δ ∧ ∃ P : ℕ, 1≤P ∧ ∃ C : ℝ, 1≤C ∧
        ∀ (T N : ℝ) (F : ℝ→ℝ) (a z : ℕ),
          IsModelPhaseSumSetupAt α σ δ P C T N F a z →
          ‖exponentialSumAt F T N a z‖≤C*T^(b+c*α+ε/2) :=
    (exponentSumGrowthExponent_le_iff_nonAsymptotic.mp
      (hβ ⟨α,hlo.trans α.property.1⟩ α.property))
        (ε/2) (by linarith only [hε]) σ hσ
  choose δ hδ P hP C hC hbound using hlocal
  let radius (α : Icc lo hi) := min (δ α) (ε/16)
  have hrad (α : Icc lo hi) : 0<radius α :=
    lt_min (hδ α) (by positivity)
  let U (α : Icc lo hi) : Set ℝ := Ioo (α-radius α) (α+radius α)
  have hcover : Icc lo hi⊆⋃ α,U α := by
    intro x hx
    refine mem_iUnion.mpr ⟨⟨x,hx⟩,?_⟩
    have hh := hrad ⟨x,hx⟩
    change x-radius ⟨x,hx⟩<x ∧ x<x+radius ⟨x,hx⟩
    constructor <;> linarith only [hh]
  obtain ⟨s,hs⟩ := isCompact_Icc.elim_finite_subcover U (fun _ => isOpen_Ioo) hcover
  have hsne : s.Nonempty := by
    have hz := hs (show lo∈Icc lo hi from ⟨le_rfl,hlohi⟩)
    obtain ⟨α,hα,_⟩ := mem_iUnion₂.mp hz
    exact ⟨α,hα⟩
  let δall : ℝ := s.inf' hsne δ
  let Pall : ℕ := max 1 (s.sup P)
  let Call : ℝ := max 2 (s.sup' hsne C)
  have hδall : 0<δall :=
    (Finset.lt_inf'_iff hsne).2 (fun α _ => hδ α)
  have hPall : 1≤Pall := le_max_left _ _
  have hCall : 1≤Call := le_trans (by norm_num) (le_max_left _ _)
  refine ⟨δall,hδall,Pall,hPall,Call,hCall,?_⟩
  intro T N F a z hCT hN hz hF ha hzend
  have hT : 1<T := lt_of_lt_of_le
    (lt_of_lt_of_le (by norm_num : (1:ℝ)<2) (le_max_left _ _)) hCT
  obtain ⟨α,hα,hu⟩ := mem_iUnion₂.mp (hs hz)
  change (α:ℝ)-radius α<Real.logb T N ∧
    Real.logb T N<(α:ℝ)+radius α at hu
  have hδle : δall≤δ α := Finset.inf'_le δ hα
  have hPle : P α≤Pall := (Finset.le_sup hα).trans (le_max_right _ _)
  have hCle : C α≤Call := (Finset.le_sup' C hα).trans (le_max_right _ _)
  have hrδ : radius α≤δ α := min_le_left _ _
  have hrε : radius α≤ε/16 := min_le_right _ _
  have hpoint := hbound α T N F a z
    ⟨hCle.trans hCT,
      (Real.le_logb_iff_rpow_le hT hN).mp (by linarith only [hu.1,hrδ]),
      (Real.logb_le_iff_le_rpow hT hN).mp (by linarith only [hu.2,hrδ]),
      approximateModelPhase_mono hF hPle hδle,ha,hzend⟩
  have hexp : b+c*α+ε/2≤b+c*Real.logb T N+ε := by
    nlinarith only [hc,hc₁,hε,hu.1,hrε,
      mul_nonneg hc (show 0≤Real.logb T N+ε/16-(α:ℝ) by
        linarith only [hu.1,hrε])]
  exact hpoint.trans (mul_le_mul hCle
    (Real.rpow_le_rpow_of_exponent_le hT.le hexp)
    (Real.rpow_nonneg (zero_lt_one.trans hT).le _) (zero_le_one.trans hCall))

example
    {lo hi b c : ℝ} (hlo : 0≤lo) (hlohi : lo≤hi) (hc : 0≤c) (hc₁ : c≤4)
    (hβ : ∀ α : ℝ≥0, (α:ℝ)∈Icc lo hi →
      exponentSumGrowthExponent α≤b+c*(α:ℝ))
    {σ ε : ℝ} (hσ : 0<σ) (hε : 0<ε) :
    ∃ δ : ℝ, 0<δ ∧ ∃ P : ℕ, 1≤P ∧ ∃ C : ℝ, 1≤C ∧
      ∀ (T N : ℝ) (F : ℝ→ℝ) (a z : ℕ),
        C≤T → 0<N → Real.logb T N∈Icc lo hi →
        IsApproximateModelPhaseFunction F σ P δ →
        N≤(a:ℝ) → (z:ℝ)≤2*N →
        ‖exponentialSumAt F T N a z‖≤C*T^(b+c*Real.logb T N+ε) := by
  exact uniform_model_sum_of_beta_interval hlo hlohi hc hc₁ hβ hσ hε

#print axioms uniform_model_sum_of_beta_interval

/-- Physical form of an affine beta bound. -/
private theorem local_beta_power_identity {T N : ℝ}
    (hT : 1<T) (hN : 0<N) (b c ε : ℝ) :
    T^(b+c*Real.logb T N+ε)=T^(b+ε)*N^c := by
  have hTp := zero_lt_one.trans hT
  rw [show b+c*Real.logb T N+ε=(b+ε)+Real.logb T N*c by ring,
    Real.rpow_add hTp,Real.rpow_mul hTp.le,Real.rpow_logb hTp hT.ne' hN]

example {T N : ℝ} (hT : 1<T) (hN : 0<N) (b c ε : ℝ) :
    T^(b+c*Real.logb T N+ε)=T^(b+ε)*N^c := by
  exact local_beta_power_identity hT hN b c ε

#print axioms local_beta_power_identity

/-- A local beta bound applied to the literal compressed A-process
correlation. The physical logarithmic scale and both endpoints are checked. -/
private theorem source_correlation_of_local_beta
    {lo hi b c : ℝ} (hlo : 0≤lo) (hlohi : lo≤hi) (hc : 0≤c) (hc₁ : c≤4)
    (hβ : ∀ α : ℝ≥0, (α:ℝ)∈Icc lo hi →
      exponentSumGrowthExponent α≤b+c*(α:ℝ))
    {σ ε : ℝ} (hσ : 0<σ) (hε : 0<ε) :
    ∃ δ : ℝ, 0<δ ∧ ∃ P : ℕ, 2≤P ∧
      ∃ η₀ : ℝ, 0<η₀ ∧ η₀≤1/2 ∧ ∃ C : ℝ, 1≤C ∧
        ∀ (F : ℝ→ℝ) (T N : ℝ) (a L r : ℕ),
          2≤N → 0<r → (r:ℝ)≤η₀*N →
          N≤(a:ℝ) → ((a+L:ℕ):ℝ)≤2*N →
          IsApproximateModelPhaseFunction F σ P δ →
          C≤σ*T*r/N → Real.logb (σ*T*r/N) (N-r)∈Icc lo hi →
          ‖sourceShiftCorrelation F T N a L r‖≤
            C*(σ*T*r/N)^(b+ε)*(N-r)^c := by
  obtain ⟨d,hd,Q,hQ,C₀,hC₀,hbound⟩ :=
    uniform_model_sum_of_beta_interval hlo hlohi hc hc₁ hβ
      (show 0<σ+1 by linarith only [hσ]) hε
  obtain ⟨δ,η₀,hδ,hη₀,hηhalf,hmodel⟩ := aProcessShiftPhase_uniform_model hσ Q hd
  let C := C₀+2
  have hC : 1≤C := by dsimp only [C]; linarith only [hC₀]
  have hC₀C : C₀≤C := by dsimp only [C]; linarith
  refine ⟨δ,hδ,Q+1,by omega,η₀,hη₀,hηhalf,C,hC,?_⟩
  intro F T N a L r hN hr hrN ha hb hF hTC hLog
  have hNpos : 0<N := by linarith only [hN]
  have hrhalf : (r:ℝ)≤N/2 := hrN.trans (by nlinarith only [hηhalf,hN])
  have hNr : 1≤N-(r:ℝ) := by linarith only [hN,hrhalf]
  have hNrp := zero_lt_one.trans_le hNr
  have hrlt : (r:ℝ)<N := by linarith only [hrhalf,hNpos]
  have hra : r≤a := by exact_mod_cast (hrlt.le.trans ha)
  have hTgt : 1<σ*T*r/N := by
    have hCC : C₀+2≤σ*T*r/N := hTC
    linarith only [hCC,hC₀]
  have hTp := zero_lt_one.trans hTgt
  by_cases hrL : r≤L
  · have hηpos : 0<(r:ℝ)/N := div_pos (Nat.cast_pos.mpr hr) hNpos
    have hηcap : (r:ℝ)/N≤η₀ := (div_le_iff₀ hNpos).mpr hrN
    have hphase := hmodel F ((r:ℝ)/N) hF hηpos hηcap
    have hend := sourceShiftCorrelation_compressed_endpoints ha hb hrlt hrL
    have hsum := hbound (σ*T*r/N) (N-r) (aProcessShiftPhase F σ ((r:ℝ)/N))
      (a-r) ((a-r)+(L-r)) (hC₀C.trans hTC) hNrp hLog hphase hend.1 hend.2
    rw [norm_sourceShiftCorrelation_compressed_sum hNpos.ne' hNrp.ne' hσ.ne' hr hra hrL]
    calc
      _ ≤ C₀*(σ*T*r/N)^(b+c*Real.logb (σ*T*r/N) (N-r)+ε) := hsum
      _ = C₀*(σ*T*r/N)^(b+ε)*(N-r)^c := by
        rw [local_beta_power_identity hTgt hNrp]
        ring
      _ ≤ C*(σ*T*r/N)^(b+ε)*(N-r)^c := by gcongr
  · rw [sourceShiftCorrelation_empty _ _ _ _ _ _ (by omega),norm_zero]
    exact mul_nonneg
      (mul_nonneg (zero_le_one.trans hC) (Real.rpow_nonneg hTp.le _))
      (Real.rpow_nonneg hNrp.le _)

example
    {lo hi b c : ℝ} (hlo : 0≤lo) (hlohi : lo≤hi) (hc : 0≤c) (hc₁ : c≤4)
    (hβ : ∀ α : ℝ≥0, (α:ℝ)∈Icc lo hi →
      exponentSumGrowthExponent α≤b+c*(α:ℝ))
    {σ ε : ℝ} (hσ : 0<σ) (hε : 0<ε) :
    ∃ δ : ℝ, 0<δ ∧ ∃ P : ℕ, 2≤P ∧
      ∃ η₀ : ℝ, 0<η₀ ∧ η₀≤1/2 ∧ ∃ C : ℝ, 1≤C ∧
        ∀ (F : ℝ→ℝ) (T N : ℝ) (a L r : ℕ),
          2≤N → 0<r → (r:ℝ)≤η₀*N →
          N≤(a:ℝ) → ((a+L:ℕ):ℝ)≤2*N →
          IsApproximateModelPhaseFunction F σ P δ →
          C≤σ*T*r/N → Real.logb (σ*T*r/N) (N-r)∈Icc lo hi →
          ‖sourceShiftCorrelation F T N a L r‖≤
            C*(σ*T*r/N)^(b+ε)*(N-r)^c := by
  exact source_correlation_of_local_beta hlo hlohi hc hc₁ hβ hσ hε

#print axioms source_correlation_of_local_beta

/-- The installed tenth/eleventh rows and D(Bourgain) give a one-sided
Lipschitz majorant on the entire upper source interval. -/
private theorem middle_source_beta_tail
    {ρ B : ℝ} (hρlo : (227:ℝ)/601≤ρ) (hρhi : ρ≤(1508:ℝ)/3825)
    (hfirst : ρ≤12/31 → (29+173*ρ)/280≤B)
    (hsecond : 12/31≤ρ → (4+103*ρ)/128≤B)
    {μ : ℝ≥0} (hρμ : ρ≤(μ:ℝ)) (hμ : (μ:ℝ)≤1) :
    exponentSumGrowthExponent μ≤B+(μ:ℝ)-ρ := by
  by_cases h10 : (μ:ℝ)≤12/31
  · have hh := HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_tenthRow
      (hρlo.trans hρμ) h10
    have hB := hfirst (hρμ.trans h10)
    linarith only [hh,hB,hρμ]
  by_cases h11 : (μ:ℝ)≤1508/3825
  · have hh := HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_eleventhRow
      (le_of_not_ge h10) h11
    by_cases hρ : ρ≤12/31
    · have hB := hfirst hρ
      linarith only [hh,hB,hρ,lt_of_not_ge h10]
    · have hB := hsecond (le_of_not_ge hρ)
      linarith only [hh,hB,hρμ]
  have hh := CubicJointCount.exponentSumGrowthExponent_le_sargosD_bourgain (α:=μ) hμ
  unfold exponentPairLine at hh
  by_cases hρ : ρ≤12/31
  · have hB := hfirst hρ
    linarith only [hh,hB,hρ,lt_of_not_ge h11]
  · have hB := hsecond (le_of_not_ge hρ)
    linarith only [hh,hB,hρhi,lt_of_not_ge h11]

example
    {ρ B : ℝ} (hρlo : (227:ℝ)/601≤ρ) (hρhi : ρ≤(1508:ℝ)/3825)
    (hfirst : ρ≤12/31 → (29+173*ρ)/280≤B)
    (hsecond : 12/31≤ρ → (4+103*ρ)/128≤B)
    {μ : ℝ≥0} (hρμ : ρ≤(μ:ℝ)) (hμ : (μ:ℝ)≤1) :
    exponentSumGrowthExponent μ≤B+(μ:ℝ)-ρ := by
  exact middle_source_beta_tail hρlo hρhi hfirst hsecond hρμ hμ

#print axioms middle_source_beta_tail

/-- Exact parent-scale geometry for the remaining third-pair A-process
interval. These are rational scalar consequences, not analytic assumptions. -/
private theorem third_pair_parent_geometry
    {α : ℝ} (hα : (391838:ℝ)/1377271≤α) (hα₁ : α≤(754:ℝ)/2579) :
    let β := 10769/351096+(587779/702192)*α
    let η := 2*(α-β)
    let ρ := α/(1+α-2*β)
    0<α ∧ α<1/2 ∧ 0<η ∧ η<α ∧
      0<ρ ∧ (227:ℝ)/601≤ρ ∧ ρ≤(1508:ℝ)/3825 ∧
      0≤1/α ∧ 1/α≤4 ∧
      (29+173*ρ)/280≤ρ/α-1 ∧ (4+103*ρ)/128≤ρ/α-1 := by
  intro β η ρ
  have hαp : 0<α := by linarith only [hα]
  have hαhalf : α<1/2 := by linarith only [hα₁]
  have hαquarter : 1/4≤α := by linarith only [hα]
  have hηp : 0<η := by dsimp only [η,β]; linarith only [hα]
  have hηα : η<α := by dsimp only [η,β]; linarith only [hα,hα₁]
  let den := 1+α-2*β
  have hden : 0<den := by dsimp only [den,β]; linarith only [hα₁]
  have hρp : 0<ρ := div_pos hαp hden
  have hρlo : (227:ℝ)/601≤ρ := by
    apply (le_div_iff₀ hden).mpr
    dsimp only [den,β]
    linarith only [hα]
  have hρhi : ρ≤(1508:ℝ)/3825 := by
    apply (div_le_iff₀ hden).mpr
    dsimp only [den,β]
    linarith only [hα₁]
  have hρden : ρ*den=α := div_mul_cancel₀ α hden.ne'
  have hρdiv : ρ/α=1/den := by
    dsimp only [ρ,den]
    field_simp
  have hfirst : (29+173*ρ)/280≤ρ/α-1 := by
    rw [hρdiv]
    apply (le_sub_iff_add_le).mpr
    apply (le_div_iff₀ hden).mpr
    have he : den=1+α-2*(10769/351096+(587779/702192)*α) := rfl
    nlinarith only [hρden,he,hα]
  have hsecond : (4+103*ρ)/128≤ρ/α-1 := by
    rw [hρdiv]
    apply (le_sub_iff_add_le).mpr
    apply (le_div_iff₀ hden).mpr
    have he : den=1+α-2*(10769/351096+(587779/702192)*α) := rfl
    nlinarith only [hρden,he,hα₁]
  exact ⟨hαp,hαhalf,hηp,hηα,hρp,hρlo,hρhi,
    (div_pos zero_lt_one hαp).le,
    (div_le_iff₀ hαp).mpr (by linarith only [hαquarter]),hfirst,hsecond⟩

example
    {α : ℝ} (hα : (391838:ℝ)/1377271≤α) (hα₁ : α≤(754:ℝ)/2579) :
    let β := 10769/351096+(587779/702192)*α
    let η := 2*(α-β)
    let ρ := α/(1+α-2*β)
    0<α ∧ α<1/2 ∧ 0<η ∧ η<α ∧
      0<ρ ∧ (227:ℝ)/601≤ρ ∧ ρ≤(1508:ℝ)/3825 ∧
      0≤1/α ∧ 1/α≤4 ∧
      (29+173*ρ)/280≤ρ/α-1 ∧ (4+103*ρ)/128≤ρ/α-1 := by
  exact third_pair_parent_geometry hα hα₁

#print axioms third_pair_parent_geometry

/-- The actual installed beta rows supply the full source interval needed
for every compressed A-process shift, including the small-shift end. -/
private theorem third_pair_parent_beta
    {α : ℝ} (hα : (391838:ℝ)/1377271≤α) (hα₁ : α≤(754:ℝ)/2579) :
    let β := 10769/351096+(587779/702192)*α
    let ρ := α/(1+α-2*β)
    ∀ μ : ℝ≥0, (μ:ℝ)∈Icc ρ 1 →
      exponentSumGrowthExponent μ≤-1+(1/α)*(μ:ℝ) := by
  intro β ρ μ hμ
  obtain ⟨hαp,hαhalf,_,_,_,hρlo,hρhi,_,_,hfirst,hsecond⟩ :=
    third_pair_parent_geometry hα hα₁
  have hh := middle_source_beta_tail hρlo hρhi
    (fun _ => hfirst) (fun _ => hsecond) hμ.1 hμ.2
  have hdifference : (μ:ℝ)-ρ≤((μ:ℝ)-ρ)/α := by
    apply (le_div_iff₀ hαp).mpr
    exact mul_le_of_le_one_right (sub_nonneg.mpr hμ.1)
      (by linarith only [hαhalf] : α≤1)
  rw [sub_div] at hdifference
  have hm : (1/α)*(μ:ℝ)=(μ:ℝ)/α := by ring
  rw [hm]
  linarith only [hh,hdifference]

example
    {α : ℝ} (hα : (391838:ℝ)/1377271≤α) (hα₁ : α≤(754:ℝ)/2579) :
    let β := 10769/351096+(587779/702192)*α
    let ρ := α/(1+α-2*β)
    ∀ μ : ℝ≥0, (μ:ℝ)∈Icc ρ 1 →
      exponentSumGrowthExponent μ≤-1+(1/α)*(μ:ℝ) := by
  exact third_pair_parent_beta hα hα₁

#print axioms third_pair_parent_beta

/-- Exact closed two-sided scale margins for the lower third-pair interval.
The numerical discovery is replaced here by rational kernel-checked algebra. -/
private theorem third_pair_capped_lower_full_window_margins
    {t u : ℝ} (ht : t∈Icc (0:ℝ) 1) (hu : u∈Icc (0:ℝ) 1) :
    let α := (1-t)*(890/3277)+t*(391838/1377271)
    let h := ((1-t)*2719220+t*3138145)/100000000
    let g₀ := ((1-t)*478287+t*206648)/100000000
    let ν₀ := ((1-t)*11931645+t*14083866)/100000000
    let ν₁ := ((1-t)*11788823+t*14087152)/100000000
    let g := (1-u)*g₀+u*(3*h)
    let ν := (1-u)*ν₀+u*ν₁
    let β := 10769/351096+(587779/702192)*α
    let ℓ := α-1/10000000000
    let v := α+1/10000000000
    let μ := (1:ℝ)/1000000
    μ≤ℓ ∧
      v+μ≤1 ∧
      μ≤h ∧
      μ≤ν ∧
      μ≤g₀ ∧
      5*h+μ≤ℓ ∧
      g₀+μ≤3*h ∧
      ν+μ≤ℓ ∧
      5*v-1-g+μ≤3*ν ∧
      1+g+2*ν+μ≤5*ℓ ∧
      4*ν+1+g+μ≤6*ℓ ∧
      ν+3*v+μ≤1+g ∧
      1+g+μ≤4*ℓ ∧
      3*v+μ≤1+g ∧
      7*v+μ≤2+2*g+ν ∧
      7+7*g+27*ν+μ≤41*ℓ ∧
      2*h+μ≤β ∧
      4*v+g₀-3*h+μ≤4*β ∧
      288*v-144*h+μ≤288*β ∧
      288*v-36*ν+72*g-216*h+μ≤288*β ∧
      648*v-72-216*h-216*ν+μ≤288*β ∧
      24+96*g-216*h+96*v+144*ν+μ≤288*β ∧
      21+87*g-216*h+177*v+33*ν+μ≤288*β ∧
      15+87*g-216*h+207*v+15*ν+μ≤288*β ∧
      12+78*g-216*h+216*v+24*ν+μ≤288*β ∧
      6+78*g-216*h+246*v+6*ν+μ≤288*β ∧
      72*g-216*h+284*v-24*ν+μ≤288*β ∧
      504*v-72-216*h+72*ν+μ≤288*β := by
  intro α h g₀ ν₀ ν₁ g ν β ℓ v μ
  have ht0 := ht.1
  have ht1 := ht.2
  have hu0 := hu.1
  have hu1 := hu.2
  have h00 := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hu1)
  have h01 := mul_nonneg (sub_nonneg.mpr ht1) hu0
  have h10 := mul_nonneg ht0 (sub_nonneg.mpr hu1)
  have h11 := mul_nonneg ht0 hu0
  dsimp only [α,h,g₀,ν₀,ν₁,g,ν,β,ℓ,v,μ]
  repeat' constructor
  all_goals nlinarith only [ht0,ht1,hu0,hu1,h00,h01,h10,h11]

example
    {t u : ℝ} (ht : t∈Icc (0:ℝ) 1) (hu : u∈Icc (0:ℝ) 1) :
    let α := (1-t)*(890/3277)+t*(391838/1377271)
    let h := ((1-t)*2719220+t*3138145)/100000000
    let g₀ := ((1-t)*478287+t*206648)/100000000
    let ν₀ := ((1-t)*11931645+t*14083866)/100000000
    let ν₁ := ((1-t)*11788823+t*14087152)/100000000
    let g := (1-u)*g₀+u*(3*h)
    let ν := (1-u)*ν₀+u*ν₁
    let β := 10769/351096+(587779/702192)*α
    let ℓ := α-1/10000000000
    let v := α+1/10000000000
    let μ := (1:ℝ)/1000000
    μ≤ℓ ∧
      v+μ≤1 ∧
      μ≤h ∧
      μ≤ν ∧
      μ≤g₀ ∧
      5*h+μ≤ℓ ∧
      g₀+μ≤3*h ∧
      ν+μ≤ℓ ∧
      5*v-1-g+μ≤3*ν ∧
      1+g+2*ν+μ≤5*ℓ ∧
      4*ν+1+g+μ≤6*ℓ ∧
      ν+3*v+μ≤1+g ∧
      1+g+μ≤4*ℓ ∧
      3*v+μ≤1+g ∧
      7*v+μ≤2+2*g+ν ∧
      7+7*g+27*ν+μ≤41*ℓ ∧
      2*h+μ≤β ∧
      4*v+g₀-3*h+μ≤4*β ∧
      288*v-144*h+μ≤288*β ∧
      288*v-36*ν+72*g-216*h+μ≤288*β ∧
      648*v-72-216*h-216*ν+μ≤288*β ∧
      24+96*g-216*h+96*v+144*ν+μ≤288*β ∧
      21+87*g-216*h+177*v+33*ν+μ≤288*β ∧
      15+87*g-216*h+207*v+15*ν+μ≤288*β ∧
      12+78*g-216*h+216*v+24*ν+μ≤288*β ∧
      6+78*g-216*h+246*v+6*ν+μ≤288*β ∧
      72*g-216*h+284*v-24*ν+μ≤288*β ∧
      504*v-72-216*h+72*ν+μ≤288*β := by
  exact third_pair_capped_lower_full_window_margins ht hu

#print axioms third_pair_capped_lower_full_window_margins

open Filter

private theorem eventually_local_A_physical_window
    {ℓ v h d ρ η σ C : ℝ}
    (hℓv : ℓ≤v) (hh : 0<h) (hhℓ : h<ℓ) (hv : 2*v<1)
    (hd : 0<d) (hρ : 0≤ρ) (hη : 0<η) (hηhalf : η≤1/2)
    (hσ : 0<σ)
    (hq : 1+h-ℓ+d≤2) (hρq : ρ*(1+h-ℓ+d)≤ℓ-d) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ M : ℝ, X^ℓ≤M → M≤X^v →
      let H := ⌊X^h⌋₊
      2≤X ∧ 2≤M ∧ 2≤H ∧ X^h/2≤(H:ℝ) ∧ (H:ℝ)≤X^h ∧
      (H:ℝ)≤η*M ∧ (H:ℝ)≤X ∧
      ∀ r : ℕ, 0<r → r≤H →
        C≤σ*X*r/M ∧ 1<σ*X*r/M ∧ 0<M-r ∧
        Real.logb (σ*X*r/M) (M-r)∈Icc ρ 1 ∧ σ*X*r/M≤X^2 := by
  have hℓ : 0<ℓ := hh.trans hhℓ
  have hE := eventually_const_mul_rpow_le_rpow (D:=1/η) hhℓ
  have hSq := eventually_const_mul_rpow_le_rpow (D:=1/σ) hv
  have hHalf := eventually_const_mul_rpow_le_rpow (D:=2)
    (show ℓ-d<ℓ by linarith only [hd])
  have hBase := (tendsto_rpow_atTop hℓ).eventually_ge_atTop (max 2 C)
  have hHBase := (tendsto_rpow_atTop hh).eventually_ge_atTop 4
  have hSig := (tendsto_rpow_atTop hd).eventually_ge_atTop σ
  filter_upwards [hE,hSq,hHalf,hBase,hHBase,hSig,Filter.eventually_ge_atTop (2:ℝ)]
    with X hEX hSqX hHalfX hBaseX hHBaseX hSigX hX
  intro M hMl hMv H
  have hXp : 0<X := by linarith only [hX]
  have hXone : 1≤X := by linarith only [hX]
  have hM : 2≤M := (le_max_left 2 C).trans (hBaseX.trans hMl)
  have hMp : 0<M := by linarith only [hM]
  have hCM : C≤M := (le_max_right 2 C).trans (hBaseX.trans hMl)
  have hH2 : 2≤H := Nat.le_floor (by linarith only [hHBaseX] : (2:ℝ)≤X^h)
  have hHup : (H:ℝ)≤X^h := Nat.floor_le (Real.rpow_nonneg hXp.le h)
  have hHlo : X^h/2≤(H:ℝ) := by
    have hz := Nat.lt_floor_add_one (X^h)
    change X^h<(H:ℝ)+1 at hz
    linarith only [hz,hHBaseX]
  have hHE : (H:ℝ)≤η*M := by
    have he : X^h≤X^ℓ*η := (div_le_iff₀ hη).mp
      (by simpa only [div_eq_mul_inv,one_mul,mul_one,mul_comm] using hEX)
    exact hHup.trans (he.trans (by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hMl hη.le))
  have hHMhalf : (H:ℝ)≤M/2 := hHE.trans (by nlinarith only [hηhalf,hMp])
  have hHX : (H:ℝ)≤X := by
    calc
      _ ≤ X^h := hHup
      _ ≤ X^1 := Real.rpow_le_rpow_of_exponent_le hXone
        (by linarith only [hhℓ,hℓv,hv])
      _ = X := Real.rpow_one X
  have hMsq : M^2≤σ*X := by
    calc
      _ ≤ (X^v)^2 := pow_le_pow_left₀ hMp.le hMv 2
      _ = X^(2*v) := by
        simpa only [Nat.cast_ofNat,mul_comm] using
          (Real.rpow_mul_natCast hXp.le v 2).symm
      _ ≤ X*σ := (div_le_iff₀ hσ).mp
        (by simpa only [Real.rpow_one,div_eq_mul_inv,one_mul,mul_one,mul_comm] using hSqX)
      _ = _ := mul_comm _ _
  refine ⟨hX,hM,hH2,hHlo,hHup,hHE,hHX,?_⟩
  intro r hr hrH
  have hrp : 0<(r:ℝ) := Nat.cast_pos.mpr hr
  have hrone : (1:ℝ)≤r := by exact_mod_cast hr
  have hrHreal : (r:ℝ)≤H := by exact_mod_cast hrH
  have hrhalf : (r:ℝ)≤M/2 := hrHreal.trans hHMhalf
  have hNr : 0<M-(r:ℝ) := by linarith only [hrhalf,hMp]
  have hMY : M≤σ*X*r/M := by
    apply (le_div_iff₀ hMp).mpr
    calc
      _ = M^2 := by ring
      _ ≤ σ*X := hMsq
      _ ≤ σ*X*r := le_mul_of_one_le_right (mul_nonneg hσ.le hXp.le) hrone
  have hYgt : 1<σ*X*r/M := lt_of_lt_of_le (by linarith only [hM] : 1<M) hMY
  have hNrLower : X^(ℓ-d)≤M-(r:ℝ) := by
    linarith only [hHalfX,hMl,hrhalf]
  have hYupper : σ*X*r/M≤X^(1+h-ℓ+d) := by
    calc
      _ ≤ X^d*X*X^h/X^ℓ := by
        apply div_le_div₀ (by positivity) _ (Real.rpow_pos_of_pos hXp ℓ) hMl
        exact mul_le_mul (mul_le_mul_of_nonneg_right hSigX hXp.le)
          (hrHreal.trans hHup) hrp.le (by positivity)
      _ = X^(1+h-ℓ+d) := by
        have he : X^d*X*X^h=X^(d+1+h) := by
          rw [Real.rpow_add hXp,Real.rpow_add hXp,Real.rpow_one]
        rw [he,← Real.rpow_sub hXp]
        congr 1
        ring
  have hLogLo : ρ≤Real.logb (σ*X*r/M) (M-r) := by
    apply (Real.le_logb_iff_rpow_le hYgt hNr).mpr
    calc
      _ ≤ (X^(1+h-ℓ+d))^ρ :=
        Real.rpow_le_rpow (zero_lt_one.trans hYgt).le hYupper hρ
      _ = X^((1+h-ℓ+d)*ρ) := (Real.rpow_mul hXp.le _ _).symm
      _ ≤ X^(ℓ-d) := Real.rpow_le_rpow_of_exponent_le hXone (by
        simpa only [mul_comm] using hρq)
      _ ≤ M-r := hNrLower
  have hLogHi : Real.logb (σ*X*r/M) (M-r)≤1 := by
    apply (Real.logb_le_iff_le_rpow hYgt hNr).mpr
    rw [Real.rpow_one]
    exact (sub_le_self M hrp.le).trans hMY
  exact ⟨hCM.trans hMY,hYgt,hNr,⟨hLogLo,hLogHi⟩,
    hYupper.trans (by simpa only [Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_le hXone hq)⟩

example
    {ℓ v h d ρ η σ C : ℝ}
    (hℓv : ℓ≤v) (hh : 0<h) (hhℓ : h<ℓ) (hv : 2*v<1)
    (hd : 0<d) (hρ : 0≤ρ) (hη : 0<η) (hηhalf : η≤1/2)
    (hσ : 0<σ)
    (hq : 1+h-ℓ+d≤2) (hρq : ρ*(1+h-ℓ+d)≤ℓ-d) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ M : ℝ, X^ℓ≤M → M≤X^v →
      let H := ⌊X^h⌋₊
      2≤X ∧ 2≤M ∧ 2≤H ∧ X^h/2≤(H:ℝ) ∧ (H:ℝ)≤X^h ∧
      (H:ℝ)≤η*M ∧ (H:ℝ)≤X ∧
      ∀ r : ℕ, 0<r → r≤H →
        C≤σ*X*r/M ∧ 1<σ*X*r/M ∧ 0<M-r ∧
        Real.logb (σ*X*r/M) (M-r)∈Icc ρ 1 ∧ σ*X*r/M≤X^2 := by
  exact eventually_local_A_physical_window hℓv hh hhℓ hv hd hρ hη hηhalf hσ hq hρq

#print axioms eventually_local_A_physical_window

private theorem local_beta_correlation_harmonic_majorant
    {X M σ C c ε : ℝ} {r : ℕ}
    (hX : 0<X) (hM : 0<M) (hσ : 0<σ) (hC : 0≤C)
    (hc : 0≤c) (hε : 0≤ε) (hr : 0<r)
    (hNr : 0<M-r) (hY : σ*X*r/M≤X^2) :
    C*(σ*X*r/M)^(-1+ε)*(M-r)^c ≤
      (C/σ)*X^(2*ε-1)*M^(c+1)*(r:ℝ)⁻¹ := by
  have hrp : 0<(r:ℝ) := Nat.cast_pos.mpr hr
  have hYp : 0<σ*X*r/M := div_pos (mul_pos (mul_pos hσ hX) hrp) hM
  have hscale : (X^2)^ε=X^(2*ε) := by
    simpa only [Nat.cast_ofNat] using (Real.rpow_natCast_mul hX.le 2 ε).symm
  calc
    _ = C*(σ*X*r/M)⁻¹*((σ*X*r/M)^ε*(M-r)^c) := by
      rw [Real.rpow_add hYp,Real.rpow_neg_one]
      ring
    _ ≤ C*(σ*X*r/M)⁻¹*((X^2)^ε*M^c) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC (inv_nonneg.mpr hYp.le))
      exact mul_le_mul (Real.rpow_le_rpow hYp.le hY hε)
        (Real.rpow_le_rpow hNr.le (sub_le_self M hrp.le) hc)
        (Real.rpow_nonneg hNr.le _) (Real.rpow_nonneg (sq_nonneg X) _)
    _ = _ := by
      rw [hscale,Real.rpow_sub hX,Real.rpow_one,
        Real.rpow_add hM,Real.rpow_one]
      field_simp

example
    {X M σ C c ε : ℝ} {r : ℕ}
    (hX : 0<X) (hM : 0<M) (hσ : 0<σ) (hC : 0≤C)
    (hc : 0≤c) (hε : 0≤ε) (hr : 0<r)
    (hNr : 0<M-r) (hY : σ*X*r/M≤X^2) :
    C*(σ*X*r/M)^(-1+ε)*(M-r)^c ≤
      (C/σ)*X^(2*ε-1)*M^(c+1)*(r:ℝ)⁻¹ := by
  exact local_beta_correlation_harmonic_majorant hX hM hσ hC hc hε hr hNr hY

#print axioms local_beta_correlation_harmonic_majorant

private theorem source_weyl_harmonic_bound
    (F : ℝ→ℝ) {X M A : ℝ} {a L H : ℕ}
    (hM : 2≤M) (hH : 1≤H) (hHM : (H:ℝ)≤M) (hHX : (H:ℝ)≤X)
    (hA : 0≤A) (ha : M≤(a:ℝ)) (hb : ((a+L:ℕ):ℝ)≤2*M)
    (hCorr : ∀ r∈Finset.Icc 1 (H-1),
      ‖sourceShiftCorrelation F X M a L r‖≤A*(r:ℝ)⁻¹) :
    ‖exponentialSumAt F X M a (a+L)‖^2 ≤
      12*(M^2/(H:ℝ)+M*A*(1+Real.log X)/(H:ℝ)) := by
  have hMp : 0<M := by linarith only [hM]
  have hHp : (0:ℝ)<H := by exact_mod_cast (show 0<H by omega)
  have hHone : (1:ℝ)≤H := by exact_mod_cast hH
  have hXone : 1≤X := hHone.trans hHX
  have hB : 0≤1+Real.log X := by have := Real.log_nonneg hXone; linarith
  let S := ∑ r∈Finset.Icc 1 (H-1), ‖sourceShiftCorrelation F X M a L r‖
  have hS : 0≤S := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hsum : S≤A*(1+Real.log X) := by
    calc
      _ ≤ ∑ r∈Finset.Icc 1 (H-1), A*(r:ℝ)⁻¹ := Finset.sum_le_sum hCorr
      _ = A*∑ r∈Finset.Icc 1 (H-1), (r:ℝ)⁻¹ := (Finset.mul_sum _ _ _).symm
      _ ≤ A*(1+Real.log H) := mul_le_mul_of_nonneg_left (sum_shift_inv_le H) hA
      _ ≤ A*(1+Real.log X) := mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (Real.log_le_log hHp hHX)) hA
  have hL : (L:ℝ)+1≤2*M := by
    push_cast at hb
    linarith only [ha,hb,hM]
  have hw := source_exponentialSum_weyl F X M a L H
  simp only [Nat.cast_add,Nat.cast_one] at hw
  have hmajor : S≤1*((H:ℝ)*(A*(1+Real.log X)/(H:ℝ))+(M^2/M)*1) := by
    have he : (H:ℝ)*(A*(1+Real.log X)/(H:ℝ))=A*(1+Real.log X) := by field_simp
    rw [one_mul,he,mul_one]
    exact hsum.trans (le_add_of_nonneg_right (div_nonneg (sq_nonneg M) hMp.le))
  have hm := weyl_correlation_sum_majorant hS
    (div_nonneg (mul_nonneg hA hB) hHp.le) hMp hHp
    (by positivity : 0≤(L:ℝ)+1) hL hHM (le_refl M) (le_refl (1:ℝ))
    (le_refl (1:ℝ)) hw hmajor
  convert hm using 1
  ring

example
    (F : ℝ→ℝ) {X M A : ℝ} {a L H : ℕ}
    (hM : 2≤M) (hH : 1≤H) (hHM : (H:ℝ)≤M) (hHX : (H:ℝ)≤X)
    (hA : 0≤A) (ha : M≤(a:ℝ)) (hb : ((a+L:ℕ):ℝ)≤2*M)
    (hCorr : ∀ r∈Finset.Icc 1 (H-1),
      ‖sourceShiftCorrelation F X M a L r‖≤A*(r:ℝ)⁻¹) :
    ‖exponentialSumAt F X M a (a+L)‖^2 ≤
      12*(M^2/(H:ℝ)+M*A*(1+Real.log X)/(H:ℝ)) := by
  exact source_weyl_harmonic_bound F hM hH hHM hHX hA ha hb hCorr

#print axioms source_weyl_harmonic_bound

private theorem local_A_power_ratio
    {X M H p v h : ℝ} (hX : 0<X) (hM : 0≤M) (hp : 0≤p)
    (hMu : M≤X^v) (hHl : X^h/2≤H) :
    M^p/H≤2*X^(v*p-h) := by
  calc
    _ ≤ (X^v)^p/(X^h/2) := div_le_div₀
      (Real.rpow_nonneg (Real.rpow_nonneg hX.le _) _)
      (Real.rpow_le_rpow hM hMu hp) (by positivity) hHl
    _ = 2*X^(v*p-h) := by
      rw [←Real.rpow_mul hX.le,Real.rpow_sub hX]
      ring

example
    {X M H p v h : ℝ} (hX : 0<X) (hM : 0≤M) (hp : 0≤p)
    (hMu : M≤X^v) (hHl : X^h/2≤H) :
    M^p/H≤2*X^(v*p-h) := by
  exact local_A_power_ratio hX hM hp hMu hHl

#print axioms local_A_power_ratio

private theorem third_pair_local_A_nonAsymptotic
    {α : ℝ≥0} (hα : (391838:ℝ)/1377271≤(α:ℝ))
    (hα₁ : (α:ℝ)≤(754:ℝ)/2579) :
    IsExponentSumBoundNonAsymptotic α
      (10769/351096+(587779/702192)*(α:ℝ)) := by
  let β := 10769/351096+(587779/702192)*(α:ℝ)
  let η₀ := 2*((α:ℝ)-β)
  let ρ := (α:ℝ)/(1+(α:ℝ)-2*β)
  let c := 1/(α:ℝ)
  obtain ⟨hαp,hαhalf,hη₀p,hη₀α,hρp,hρlo,hρhi,hc,hc₁,_,_⟩ :=
    third_pair_parent_geometry hα hα₁
  change 0<η₀ at hη₀p
  change η₀<(α:ℝ) at hη₀α
  change 0<ρ at hρp
  change (227:ℝ)/601≤ρ at hρlo
  change ρ≤(1508:ℝ)/3825 at hρhi
  change 0≤c at hc
  change c≤4 at hc₁
  have hρquarter : 1/4≤ρ := by linarith only [hρlo]
  have hρone : ρ≤1 := by linarith only [hρhi]
  have hαc : (α:ℝ)*c=1 := by dsimp only [c]; field_simp
  have hρbase : ρ*(1+η₀-(α:ℝ))=(α:ℝ) := by
    have hden : 0<1+(α:ℝ)-2*β := by
      dsimp only [β]
      linarith only [hα₁]
    dsimp only [ρ,η₀]
    convert div_mul_cancel₀ (α:ℝ) hden.ne' using 1; ring
  intro ε hε σ hσ
  let d := min (η₀/2) (ε/4)
  let w := min (d/100) ((1-2*(α:ℝ))/100)
  let h := η₀-d
  let ℓ := (α:ℝ)-w
  let v := (α:ℝ)+w
  let εs := d/100
  let E := 2*β+d+w*(c+2)+2*εs
  have hd : 0<d := lt_min (by positivity) (by positivity)
  have hdη : d≤η₀/2 := min_le_left _ _
  have hdε : d≤ε/4 := min_le_right _ _
  have hw : 0<w := lt_min (by positivity) (by
    apply div_pos _ (by norm_num)
    linarith only [hαhalf])
  have hwd : w≤d/100 := min_le_left _ _
  have hwα : w≤(1-2*(α:ℝ))/100 := min_le_right _ _
  have hεs : 0<εs := div_pos hd (by norm_num)
  have hh : 0<h := by dsimp only [h]; linarith only [hdη,hη₀p]
  have hhℓ : h<ℓ := by dsimp only [h,ℓ]; linarith only [hη₀α,hwd,hd]
  have hℓv : ℓ≤v := by dsimp only [ℓ,v]; linarith only [hw]
  have hv : 2*v<1 := by dsimp only [v]; linarith only [hwα,hαhalf]
  have hq : 1+h-ℓ+w≤2 := by
    dsimp only [h,ℓ]
    linarith only [hη₀α,hwd,hd]
  have hρq : ρ*(1+h-ℓ+w)≤ℓ-w := by
    have hρd : d/4≤ρ*d := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hρquarter) hd.le]
    have hρw : ρ*w≤w := mul_le_of_le_one_left hw.le hρone
    dsimp only [h,ℓ]
    nlinarith only [hρbase,hρd,hρw,hwd]
  have hDiagExp : 2*v-h≤E := by
    dsimp only [E,v,h,η₀,εs]
    nlinarith only [mul_nonneg hw.le hc,hd.le]
  have hCrossExp : v*(c+2)-h-1+2*εs=E := by
    dsimp only [E,v,h,η₀]
    nlinarith only [hαc]
  have hFinalExp : E+ε/4≤2*(β+ε) := by
    have hwc : w*(c+2)≤6*w := by nlinarith only [mul_nonneg hw.le (sub_nonneg.mpr hc₁)]
    dsimp only [E,εs]
    linarith only [hwc,hwd,hdε,hε]
  obtain ⟨δsrc,hδsrc,P,hP,η,hη,hηhalf,Csrc,hCsrc,hSource⟩ :=
    source_correlation_of_local_beta hρp.le hρone hc hc₁
      (third_pair_parent_beta hα hα₁) hσ hεs
  let D := 24+24*(Csrc/σ)
  have hK : 0≤Csrc/σ := div_nonneg (zero_le_one.trans hCsrc) hσ.le
  have hD : 0≤D := by dsimp only [D]; positivity
  have hPhys := eventually_local_A_physical_window
    (C:=Csrc) hℓv hh hhℓ hv hw hρp.le hη hηhalf hσ hq hρq
  have hLog := eventually_const_log_pow_le_rpow (2*D)
    (mul_nonneg (by norm_num) hD) 1 (show 0<ε/4 by positivity)
  have hLogOne : ∀ᶠ X : ℝ in atTop, 1≤Real.log X :=
    Real.tendsto_log_atTop.eventually_ge_atTop 1
  obtain ⟨X₀,hX₀⟩ := eventually_atTop.mp
    (hPhys.and (hLog.and (hLogOne.and (eventually_ge_atTop (2:ℝ)))))
  let δ := min δsrc w
  let C := max 1 X₀
  have hC : 1≤C := le_max_left _ _
  refine ⟨δ,lt_min hδsrc hw,P,by omega,C,hC,?_⟩
  intro X M F a b setup
  have hTogether := hX₀ X ((le_max_right 1 X₀).trans setup.threshold_le_param)
  have hX2 := hTogether.2.2.2
  have hX : 1≤X := (by norm_num : (1:ℝ)≤2).trans hX2
  have hXp := zero_lt_one.trans_le hX
  have hMl : X^ℓ≤M :=
    (Real.rpow_le_rpow_of_exponent_le hX
      (sub_le_sub_left (min_le_right δsrc w) _)).trans setup.rpow_sub_le_scale
  have hMu : M≤X^v := setup.scale_le_rpow_add.trans
    (Real.rpow_le_rpow_of_exponent_le hX (add_le_add le_rfl (min_le_right δsrc w)))
  have hF := approximateModelPhase_mono setup.isApproximateModelPhase
    le_rfl (min_le_left δsrc w)
  let H := ⌊X^h⌋₊
  obtain ⟨_,hM,hH2,hHl,_,hHE,hHX,hAll⟩ := hTogether.1 M hMl hMu
  have hMp : 0<M := by linarith only [hM]
  have hHp : (0:ℝ)<H := by exact_mod_cast (show 0<H by omega)
  have hHM : (H:ℝ)≤M := hHE.trans (by nlinarith only [hηhalf,hMp])
  have hB : 0≤1+Real.log X := by linarith only [hTogether.2.2.1]
  suffices hResult : ‖exponentialSumAt F X M a b‖≤X^(β+ε) from
    hResult.trans (le_mul_of_one_le_left (Real.rpow_nonneg hXp.le _) hC)
  by_cases hba : b<a
  · rw [exponentialSumAt_of_lt hba,norm_zero]
    exact Real.rpow_nonneg hXp.le _
  have hab : a≤b := Nat.le_of_not_gt hba
  let L := b-a
  have hEnd : a+L=b := Nat.add_sub_of_le hab
  have ha := setup.scale_le_start
  have hb : ((a+L:ℕ):ℝ)≤2*M := by rw [hEnd]; exact setup.end_le_two_mul_scale
  let A := (Csrc/σ)*X^(2*εs-1)*M^(c+1)
  have hA : 0≤A := mul_nonneg (mul_nonneg hK (Real.rpow_nonneg hXp.le _))
    (Real.rpow_nonneg hMp.le _)
  have hCorr (r : ℕ) (hr : r∈Finset.Icc 1 (H-1)) :
      ‖sourceShiftCorrelation F X M a L r‖≤A*(r:ℝ)⁻¹ := by
    have hrI := Finset.mem_Icc.mp hr
    have hrp : 0<r := by omega
    have hrH : r≤H := by omega
    obtain ⟨hCY,_,hNr,hLogY,hYcap⟩ := hAll r hrp hrH
    have hrHE : (r:ℝ)≤η*M :=
      (show (r:ℝ)≤H by exact_mod_cast hrH).trans hHE
    exact (hSource F X M a L r hM hrp hrHE ha hb hF hCY hLogY).trans
      (local_beta_correlation_harmonic_majorant hXp hMp hσ
        (zero_le_one.trans hCsrc) hc hεs.le hrp hNr hYcap)
  have hWeyl := source_weyl_harmonic_bound F hM (by omega : 1≤H)
    hHM hHX hA ha hb hCorr
  have hDiag : M^2/(H:ℝ)≤2*X^E := by
    have hr := local_A_power_ratio (p:=2) hXp hMp.le (by norm_num) hMu hHl
    rw [Real.rpow_two] at hr
    exact hr.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hX (by simpa only [mul_comm] using hDiagExp))
      (by norm_num))
  have hCross : M*A*(1+Real.log X)/(H:ℝ)≤
      2*(Csrc/σ)*(1+Real.log X)*X^E := by
    have hr := local_A_power_ratio (p:=c+2) hXp hMp.le (by linarith only [hc]) hMu hHl
    have he : M^(c+2)=M*M^(c+1) := by
      rw [show c+2=1+(c+1) by ring,Real.rpow_add hMp,Real.rpow_one]
    calc
      _ = (Csrc/σ)*X^(2*εs-1)*(1+Real.log X)*(M^(c+2)/(H:ℝ)) := by
        rw [he]
        dsimp only [A]
        ring
      _ ≤ (Csrc/σ)*X^(2*εs-1)*(1+Real.log X)*(2*X^(v*(c+2)-h)) :=
        mul_le_mul_of_nonneg_left hr (mul_nonneg (mul_nonneg hK
          (Real.rpow_nonneg hXp.le _)) hB)
      _ = 2*(Csrc/σ)*(1+Real.log X)*X^E := by
        have he' : (2*εs-1)+(v*(c+2)-h)=E := by linarith only [hCrossExp]
        rw [←he',Real.rpow_add hXp]
        ring
  have hSqr : ‖exponentialSumAt F X M a b‖^2≤D*(1+Real.log X)*X^E := by
    rw [←hEnd]
    calc
      _ ≤ 12*(M^2/(H:ℝ)+M*A*(1+Real.log X)/(H:ℝ)) := hWeyl
      _ ≤ 12*(2*X^E+2*(Csrc/σ)*(1+Real.log X)*X^E) :=
        mul_le_mul_of_nonneg_left (add_le_add hDiag hCross) (by norm_num)
      _ ≤ D*(1+Real.log X)*X^E := by
        have hLog0 : 0≤Real.log X := Real.log_nonneg hX
        have hExtra := mul_nonneg hLog0 (Real.rpow_nonneg hXp.le E)
        dsimp only [D]
        nlinarith only [hExtra]
  have hLoss : D*(1+Real.log X)≤X^(ε/4) := by
    have hhLog := hTogether.2.1
    rw [pow_one] at hhLog
    have hExtra := mul_nonneg hD (sub_nonneg.mpr hTogether.2.2.1)
    have hLong : D*(1+Real.log X)≤2*D*Real.log X := by
      nlinarith only [hExtra]
    exact hLong.trans hhLog
  have hFinal : ‖exponentialSumAt F X M a b‖^2≤(X^(β+ε))^2 := by
    calc
      _ ≤ D*(1+Real.log X)*X^E := hSqr
      _ ≤ X^(ε/4)*X^E := mul_le_mul_of_nonneg_right hLoss (Real.rpow_nonneg hXp.le E)
      _ = X^(E+ε/4) := by rw [←Real.rpow_add hXp]; congr 1; ring
      _ ≤ X^(2*(β+ε)) := Real.rpow_le_rpow_of_exponent_le hX hFinalExp
      _ = (X^(β+ε))^2 := by
        simpa only [Nat.cast_ofNat,mul_comm] using Real.rpow_mul_natCast hXp.le (β+ε) 2
  exact (sq_le_sq₀ (norm_nonneg _) (Real.rpow_nonneg hXp.le _)).mp hFinal

example
    {α : ℝ≥0} (hα : (391838:ℝ)/1377271≤(α:ℝ))
    (hα₁ : (α:ℝ)≤(754:ℝ)/2579) :
    IsExponentSumBoundNonAsymptotic α
      (10769/351096+(587779/702192)*(α:ℝ)) := by
  exact third_pair_local_A_nonAsymptotic hα hα₁

#print axioms third_pair_local_A_nonAsymptotic

private theorem exponentSumGrowthExponent_le_huxley_thirdPair_upperRange
    {α : ℝ≥0} (hα : (391838:ℝ)/1377271≤(α:ℝ))
    (hα₁ : (α:ℝ)≤(754:ℝ)/2579) :
    exponentSumGrowthExponent α≤10769/351096+(587779/702192)*(α:ℝ) := by
  exact exponentSumGrowthExponent_le_iff_nonAsymptotic.mpr
    (third_pair_local_A_nonAsymptotic hα hα₁)

example
    {α : ℝ≥0} (hα : (391838:ℝ)/1377271≤(α:ℝ))
    (hα₁ : (α:ℝ)≤(754:ℝ)/2579) :
    exponentSumGrowthExponent α≤10769/351096+(587779/702192)*(α:ℝ) := by
  exact exponentSumGrowthExponent_le_huxley_thirdPair_upperRange hα hα₁

#print axioms exponentSumGrowthExponent_le_huxley_thirdPair_upperRange

end LocalBetaAProcessScratch
