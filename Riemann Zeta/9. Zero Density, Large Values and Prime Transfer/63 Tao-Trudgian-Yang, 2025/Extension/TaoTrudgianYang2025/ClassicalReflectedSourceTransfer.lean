import TaoTrudgianYang2025.ClassicalReflectedPhysicalWindows

/-!
# Actual interior source consumers of compact zeta bounds

The common zeta constants precede source perturbation parameters, heights,
lengths and indexed families. All normalization, size, height-window and
occupied-color hypotheses are derived from the actual smooth source.
The explicit finite logarithmic/ceiling loss is retained in the conclusion;
its final epsilon absorption and other source branches are separate work.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem classicalReflected_interior_source_cardinality_transfer
    (sigma B : ℝ) (hsigma : 1/2 < sigma) (hsigmaUpper : sigma < 1)
    (hB : 0 ≤ B)
    (hLV : ∀ tau ∈ Set.Icc (2 : ℝ) (2/((sigma-1/2)/2)),
      IsZetaLargeValueBound sigma tau (B*tau)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 1 ≤ C ∧ ∃ delta : ℝ, 0 < delta ∧
        ∀ d u : ℝ, 0 < d → d ≤ (sigma-1/2)/1000 →
          0 ≤ u → u ≤ d → d ≤ delta/8 →
          (2/((sigma-1/2)/2))*(u+3*d) ≤ delta/2 →
          ∃ T₀ : ℝ, 8 ≤ T₀ ∧
            ∀ {ι : Type*} [Fintype ι] [LinearOrder ι]
              {T tau : ℝ} {Y A r : ℕ} (W : ι → ℝ), T₀ ≤ T →
              A = ⌊sharpZetaCutoff T⌋₊ → 0 < Y → 2 ≤ r →
              ((Y+1 : ℕ) : ℝ) ≤ (((2^r*Y : ℕ) : ℝ)/2) →
              2*(2^r*Y) ≤ A →
              tau = typeILogarithmicScale T (2^r*Y) → 1 < tau → tau < 2 →
              (∀ x, T-T^d ≤ W x ∧ W x ≤ 2*T+T^d) →
              (∀ x, ((3/4)*(T^(-u)/2))/(Nat.clog 2 A+1 : ℕ) ≤
                ‖typeISourceSmoothBlock Y A r sigma (W x)‖) →
              (∀ x y : ι, x ≠ y → 1 ≤ |W x-W y|) →
              let M := mediumTypeIDualCutoff T d (2^r*Y)
              let D := T^d+2*Real.pi*T^d
              let L := Nat.ceil (2*D+2)
              let K := (Fintype.card (Fin (Nat.clog 2 M) ×
                (ZMod 2 × Fin (L+1))) : ℝ)
              (Fintype.card ι : ℝ) ≤ K*(4*(C*(2*T)^B*T^ε)) := by
  intro ε hε
  let U : ℝ := 2/((sigma-1/2)/2)
  have hg : 0 < (sigma-1/2)/2 := by linarith
  have hU : 2 ≤ U := by
    apply (le_div_iff₀ hg).mpr
    linarith
  obtain ⟨C,hC,delta,hdelta,hfinite⟩ :=
    classicalReflected_uniform_colored_cardinality_bound
      sigma B U hB hU hLV ε hε
  refine ⟨C,hC,delta,hdelta,?_⟩
  intro d u hd hdGap hu huD hdWindow hLoss
  have hdOne : d ≤ 1 := by nlinarith [hdGap]
  have hdHalf : d ≤ 1/2 := by nlinarith [hdGap]
  have hdStrict : d < 1 := by nlinarith [hdGap]
  obtain ⟨Clog,_hClog,_hCref,_hg,_hUscale,k,_hk,Tsource,hTsource,hsource⟩ :=
    eventually_interior_source_normalized_indexed_fourier_data hsigma hsigmaUpper
      hd hdOne hdGap hu huD hd hdelta hLoss
  have hPhysical := eventually_classicalReflected_compact_scale_conditions
    C U delta d (by linarith) hdelta hd.le hdHalf hdWindow
  have hRoom := eventually_classicalReflected_fourier_displacement_fits d hdStrict
  obtain ⟨Tabs,habs⟩ := Filter.eventually_atTop.mp (hPhysical.and hRoom)
  refine ⟨max Tsource Tabs,hTsource.trans (le_max_left _ _),?_⟩
  intro ι _ _ T tau Y A r W hT hA hY hr hLower hUpper hTau htauOne htauTwo
    hRange hLarge hsep
  dsimp only
  have hTpos : 0 < T := by
    have he := hTsource.trans ((le_max_left _ _).trans hT)
    linarith
  have hCnonneg : 0 ≤ C := zero_le_one.trans hC
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
    rw [Fintype.card_of_isEmpty, Nat.cast_zero]
    positivity
  | inr hnonempty =>
    obtain ⟨W',label,hpert,hPositive,hNormalized,_hValues,_hEnergy,
      _hExact,_hGrowth,hGeometry⟩ :=
      hsource W ((le_max_left _ _).trans hT) hA hY hr hLower hUpper hTau
        htauOne htauTwo hRange hLarge
    obtain ⟨hPhysAt,hRoomAt⟩ := habs T ((le_max_right _ _).trans hT)
    let M := mediumTypeIDualCutoff T d (2^r*Y)
    let D := T^d+2*Real.pi*T^d
    have hFinalRange : ∀ x, T/4 ≤ W' x ∧ W' x ≤ 4*T := by
      intro x
      have hx := hPositive x
      constructor <;> linarith
    apply hfinite M (fun j : Fin (Nat.clog 2 M) => 2^j.val) label T D W W'
      hTpos (by dsimp [D]; positivity) hsep hpert hFinalRange _ hNormalized
    intro x
    have hgx := hGeometry x
    exact ⟨hgx.1,hPhysAt (2^(label x).val) hgx.1 hgx.2.2.1 hgx.2.2.2.1⟩

theorem classicalReflected_interior_source_energy_transfer
    (sigma B : ℝ) (hsigma : 1/2 < sigma) (hsigmaUpper : sigma < 1)
    (hB : 0 ≤ B)
    (hLV : ∀ tau ∈ Set.Icc (2 : ℝ) (2/((sigma-1/2)/2)),
      IsZetaLargeValueEnergyBound sigma tau (B*tau)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 1 ≤ C ∧ ∃ delta : ℝ, 0 < delta ∧
        ∀ d u : ℝ, 0 < d → d ≤ (sigma-1/2)/1000 →
          0 ≤ u → u ≤ d → d ≤ delta/8 →
          (2/((sigma-1/2)/2))*(u+3*d) ≤ delta/2 →
          ∃ T₀ : ℝ, 8 ≤ T₀ ∧
            ∀ {ι : Type*} [Fintype ι] [LinearOrder ι]
              {T tau : ℝ} {Y A r : ℕ} (W : ι → ℝ), T₀ ≤ T →
              A = ⌊sharpZetaCutoff T⌋₊ → 0 < Y → 2 ≤ r →
              ((Y+1 : ℕ) : ℝ) ≤ (((2^r*Y : ℕ) : ℝ)/2) →
              2*(2^r*Y) ≤ A →
              tau = typeILogarithmicScale T (2^r*Y) → 1 < tau → tau < 2 →
              (∀ x, T-T^d ≤ W x ∧ W x ≤ 2*T+T^d) →
              (∀ x, ((3/4)*(T^(-u)/2))/(Nat.clog 2 A+1 : ℕ) ≤
                ‖typeISourceSmoothBlock Y A r sigma (W x)‖) →
              (∀ x y : ι, x ≠ y → 1 ≤ |W x-W y|) →
              let M := mediumTypeIDualCutoff T d (2^r*Y)
              let D := T^d+2*Real.pi*T^d
              let L := Nat.ceil (2*D+2)
              let K := (Fintype.card (Fin (Nat.clog 2 M) ×
                (ZMod 2 × Fin (L+1))) : ℝ)
              (approximateAdditiveEnergyOf 1 W : ℝ) ≤ (4*Nat.ceil (1+4*D)+6)*(9*K^4*(2304*(C*(2*T)^B*T^ε))) := by
  intro ε hε
  let U : ℝ := 2/((sigma-1/2)/2)
  have hg : 0 < (sigma-1/2)/2 := by linarith
  have hU : 2 ≤ U := by
    apply (le_div_iff₀ hg).mpr
    linarith
  obtain ⟨C,hC,delta,hdelta,hfinite⟩ :=
    classicalReflected_uniform_colored_energy_bound
      sigma B U hB hU hLV ε hε
  refine ⟨C,hC,delta,hdelta,?_⟩
  intro d u hd hdGap hu huD hdWindow hLoss
  have hdOne : d ≤ 1 := by nlinarith [hdGap]
  have hdHalf : d ≤ 1/2 := by nlinarith [hdGap]
  have hdStrict : d < 1 := by nlinarith [hdGap]
  obtain ⟨Clog,_hClog,_hCref,_hg,_hUscale,k,_hk,Tsource,hTsource,hsource⟩ :=
    eventually_interior_source_normalized_indexed_fourier_data hsigma hsigmaUpper
      hd hdOne hdGap hu huD hd hdelta hLoss
  have hPhysical := eventually_classicalReflected_compact_scale_conditions
    C U delta d (by linarith) hdelta hd.le hdHalf hdWindow
  have hRoom := eventually_classicalReflected_fourier_displacement_fits d hdStrict
  obtain ⟨Tabs,habs⟩ := Filter.eventually_atTop.mp (hPhysical.and hRoom)
  refine ⟨max Tsource Tabs,hTsource.trans (le_max_left _ _),?_⟩
  intro ι _ _ T tau Y A r W hT hA hY hr hLower hUpper hTau htauOne htauTwo
    hRange hLarge hsep
  dsimp only
  have hTpos : 0 < T := by
    have he := hTsource.trans ((le_max_left _ _).trans hT)
    linarith
  have hCnonneg : 0 ≤ C := zero_le_one.trans hC
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
    have hz : approximateAdditiveEnergyOf 1 W = 0 := by
      simp [approximateAdditiveEnergyOf, AdditiveQuadrupleOf]
    rw [hz, Nat.cast_zero]
    positivity
  | inr hnonempty =>
    obtain ⟨W',label,hpert,hPositive,hNormalized,_hValues,_hEnergy,
      _hExact,_hGrowth,hGeometry⟩ :=
      hsource W ((le_max_left _ _).trans hT) hA hY hr hLower hUpper hTau
        htauOne htauTwo hRange hLarge
    obtain ⟨hPhysAt,hRoomAt⟩ := habs T ((le_max_right _ _).trans hT)
    let M := mediumTypeIDualCutoff T d (2^r*Y)
    let D := T^d+2*Real.pi*T^d
    have hFinalRange : ∀ x, T/4 ≤ W' x ∧ W' x ≤ 4*T := by
      intro x
      have hx := hPositive x
      constructor <;> linarith
    apply hfinite M (fun j : Fin (Nat.clog 2 M) => 2^j.val) label T D W W'
      hTpos (by dsimp [D]; positivity) hsep hpert hFinalRange _ hNormalized
    intro x
    have hgx := hGeometry x
    exact ⟨hgx.1,hPhysAt (2^(label x).val) hgx.1 hgx.2.2.1 hgx.2.2.2.1⟩


end TaoTrudgianYang2025

