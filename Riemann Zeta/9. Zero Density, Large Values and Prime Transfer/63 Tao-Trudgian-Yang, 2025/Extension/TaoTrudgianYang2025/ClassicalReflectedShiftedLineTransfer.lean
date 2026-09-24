import TaoTrudgianYang2025.ClassicalGlobalSourceEntry

/-!
# Reflected interior source transfer at a nearby fixed real-part line

The zeta exponent and compact range are fixed before the source line.
The normalized source uses half of the exponent window, leaving the
other half for the target/source line difference. Every physical family
and its complete color count is still supplied by the actual factory.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem classicalReflected_shifted_line_source_cardinality_transfer
    (sigma B U : ℝ) (hB : 0 ≤ B) (hU : 2 ≤ U)
    (hLV : ∀ tau ∈ Set.Icc (2 : ℝ) U,
      IsZetaLargeValueBound sigma tau (B*tau)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 1 ≤ C ∧ ∃ delta : ℝ, 0 < delta ∧
        ∀ s d u : ℝ, 1/2 < s → s < 1 →
          2/((s-1/2)/2) ≤ U → sigma-delta/2 ≤ s →
          0 < d → d ≤ (s-1/2)/1000 →
          0 ≤ u → u ≤ d → d ≤ delta/8 →
          U*(u+3*d) ≤ delta/4 →
          ∃ T₀ : ℝ, 8 ≤ T₀ ∧
            ∀ {ι : Type*} [Fintype ι] [LinearOrder ι]
              {T tau : ℝ} {Y A r : ℕ} (W : ι → ℝ), T₀ ≤ T →
              A = ⌊sharpZetaCutoff T⌋₊ → 0 < Y → 2 ≤ r →
              ((Y+1 : ℕ) : ℝ) ≤ (((2^r*Y : ℕ) : ℝ)/2) →
              2*(2^r*Y) ≤ A →
              tau = typeILogarithmicScale T (2^r*Y) → 1 < tau → tau < 2 →
              (∀ x, T-T^d ≤ W x ∧ W x ≤ 2*T+T^d) →
              (∀ x, ((3/4)*(T^(-u)/2))/(Nat.clog 2 A+1 : ℕ) ≤
                ‖typeISourceSmoothBlock Y A r s (W x)‖) →
              (∀ x y : ι, x ≠ y → 1 ≤ |W x-W y|) →
              let M := mediumTypeIDualCutoff T d (2^r*Y)
              let D := T^d+2*Real.pi*T^d
              let L := Nat.ceil (2*D+2)
              let K := (Fintype.card (Fin (Nat.clog 2 M) ×
                (ZMod 2 × Fin (L+1))) : ℝ)
              (Fintype.card ι : ℝ) ≤ K*(4*(C*(2*T)^B*T^ε)) := by
  intro ε hε
  obtain ⟨C,hC,delta,hdelta,hfinite⟩ :=
    classicalReflected_uniform_colored_cardinality_bound
      sigma B U hB hU hLV ε hε
  refine ⟨C,hC,delta,hdelta,?_⟩
  intro s d u hs hsUpper hSU hLine hd hdGap hu huD hdWindow hLoss
  have hdOne : d ≤ 1 := by nlinarith [hdGap]
  have hdHalf : d ≤ 1/2 := by nlinarith [hdGap]
  have hdStrict : d < 1 := by nlinarith [hdGap]
  obtain ⟨Clog,_hClog,_hCref,_hg,_hUscale,k,_hk,Tsource,hTsource,hsource⟩ :=
    eventually_interior_source_normalized_indexed_fourier_data hs hsUpper
      hd hdOne hdGap hu huD hd (by linarith : 0 < delta/2)
      (show (2/((s-1/2)/2))*(u+3*d) ≤ (delta/2)/2 by
        have hmul := mul_le_mul_of_nonneg_right hSU (by positivity : 0 ≤ u+3*d)
        linarith)
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
    have hTarget : ∀ x, ((2^(label x).val : ℕ) : ℝ)^(sigma-delta) ≤
        ‖∑ n ∈ Finset.Ioc (2^(label x).val) (min (2*2^(label x).val) M),
          dirichletPhase n (W' x)‖ := by
      intro x
      have hNreal : (1 : ℝ) ≤ (2^(label x).val : ℕ) := by
        exact_mod_cast (hGeometry x).1.le
      exact (Real.rpow_le_rpow_of_exponent_le hNreal (by linarith)).trans (hNormalized x)
    apply hfinite M (fun j : Fin (Nat.clog 2 M) => 2^j.val) label T D W W'
      hTpos (by dsimp [D]; positivity) hsep hpert hFinalRange _ hTarget
    intro x
    have hgx := hGeometry x
    exact ⟨hgx.1,hPhysAt (2^(label x).val) hgx.1 hgx.2.2.1
      (hgx.2.2.2.1.trans hSU)⟩

theorem classicalReflected_shifted_line_source_energy_transfer
    (sigma B U : ℝ) (hB : 0 ≤ B) (hU : 2 ≤ U)
    (hLV : ∀ tau ∈ Set.Icc (2 : ℝ) U,
      IsZetaLargeValueEnergyBound sigma tau (B*tau)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 1 ≤ C ∧ ∃ delta : ℝ, 0 < delta ∧
        ∀ s d u : ℝ, 1/2 < s → s < 1 →
          2/((s-1/2)/2) ≤ U → sigma-delta/2 ≤ s →
          0 < d → d ≤ (s-1/2)/1000 →
          0 ≤ u → u ≤ d → d ≤ delta/8 →
          U*(u+3*d) ≤ delta/4 →
          ∃ T₀ : ℝ, 8 ≤ T₀ ∧
            ∀ {ι : Type*} [Fintype ι] [LinearOrder ι]
              {T tau : ℝ} {Y A r : ℕ} (W : ι → ℝ), T₀ ≤ T →
              A = ⌊sharpZetaCutoff T⌋₊ → 0 < Y → 2 ≤ r →
              ((Y+1 : ℕ) : ℝ) ≤ (((2^r*Y : ℕ) : ℝ)/2) →
              2*(2^r*Y) ≤ A →
              tau = typeILogarithmicScale T (2^r*Y) → 1 < tau → tau < 2 →
              (∀ x, T-T^d ≤ W x ∧ W x ≤ 2*T+T^d) →
              (∀ x, ((3/4)*(T^(-u)/2))/(Nat.clog 2 A+1 : ℕ) ≤
                ‖typeISourceSmoothBlock Y A r s (W x)‖) →
              (∀ x y : ι, x ≠ y → 1 ≤ |W x-W y|) →
              let M := mediumTypeIDualCutoff T d (2^r*Y)
              let D := T^d+2*Real.pi*T^d
              let L := Nat.ceil (2*D+2)
              let K := (Fintype.card (Fin (Nat.clog 2 M) ×
                (ZMod 2 × Fin (L+1))) : ℝ)
              (approximateAdditiveEnergyOf 1 W : ℝ) ≤ (4*Nat.ceil (1+4*D)+6)*(9*K^4*(2304*(C*(2*T)^B*T^ε))) := by
  intro ε hε
  obtain ⟨C,hC,delta,hdelta,hfinite⟩ :=
    classicalReflected_uniform_colored_energy_bound
      sigma B U hB hU hLV ε hε
  refine ⟨C,hC,delta,hdelta,?_⟩
  intro s d u hs hsUpper hSU hLine hd hdGap hu huD hdWindow hLoss
  have hdOne : d ≤ 1 := by nlinarith [hdGap]
  have hdHalf : d ≤ 1/2 := by nlinarith [hdGap]
  have hdStrict : d < 1 := by nlinarith [hdGap]
  obtain ⟨Clog,_hClog,_hCref,_hg,_hUscale,k,_hk,Tsource,hTsource,hsource⟩ :=
    eventually_interior_source_normalized_indexed_fourier_data hs hsUpper
      hd hdOne hdGap hu huD hd (by linarith : 0 < delta/2)
      (show (2/((s-1/2)/2))*(u+3*d) ≤ (delta/2)/2 by
        have hmul := mul_le_mul_of_nonneg_right hSU (by positivity : 0 ≤ u+3*d)
        linarith)
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
    have hTarget : ∀ x, ((2^(label x).val : ℕ) : ℝ)^(sigma-delta) ≤
        ‖∑ n ∈ Finset.Ioc (2^(label x).val) (min (2*2^(label x).val) M),
          dirichletPhase n (W' x)‖ := by
      intro x
      have hNreal : (1 : ℝ) ≤ (2^(label x).val : ℕ) := by
        exact_mod_cast (hGeometry x).1.le
      exact (Real.rpow_le_rpow_of_exponent_le hNreal (by linarith)).trans (hNormalized x)
    apply hfinite M (fun j : Fin (Nat.clog 2 M) => 2^j.val) label T D W W'
      hTpos (by dsimp [D]; positivity) hsep hpert hFinalRange _ hTarget
    intro x
    have hgx := hGeometry x
    exact ⟨hgx.1,hPhysAt (2^(label x).val) hgx.1 hgx.2.2.1
      (hgx.2.2.2.1.trans hSU)⟩


end TaoTrudgianYang2025

