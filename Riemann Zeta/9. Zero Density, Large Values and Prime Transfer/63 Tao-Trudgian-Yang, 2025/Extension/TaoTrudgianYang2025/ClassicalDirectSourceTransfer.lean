import TaoTrudgianYang2025.ClassicalDirectSourceNormalized

/-!
# Compact zeta transfer for the actual direct interior source

Constants precede the source line and displacement choices. The two
literal physical lengths, normalized thresholds, positive height windows
and every separation color are derived from the original smooth source.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem classicalDirect_shifted_line_source_cardinality_transfer
    (sigma B a : ℝ) (hB : 0 ≤ B) (ha : 0 < a) (haHalf : a ≤ 1/2)
    (hLV : ∀ tau ∈ Set.Icc (2 : ℝ) (1/a),
      IsZetaLargeValueBound sigma tau (B*tau)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 1 ≤ C ∧ ∃ delta : ℝ, 0 < delta ∧
        ∀ s d u : ℝ, 0 ≤ s → sigma-delta/2 ≤ s →
          0 < d → d < 1 → u ≤ 1 → u ≤ a*delta/4 →
          ∀ᶠ T : ℝ in Filter.atTop,
            let Y := ⌊T^a⌋₊
            let A := ⌊sharpZetaCutoff T⌋₊
            ∀ {ι : Type*} [Fintype ι] [LinearOrder ι] (r : ℕ) (W : ι → ℝ),
              let Q := 2^r*Y
              2 ≤ r → ((Y+1 : ℕ) : ℝ) ≤ (Q : ℝ)/2 → 2*Q ≤ A →
              2 ≤ typeILogarithmicScale T Q →
              (∀ x, T-T^d ≤ W x ∧ W x ≤ 2*T+T^d) →
              (∀ x, ((3/4)*(T^(-u)/2))/(Nat.clog 2 A+1 : ℕ) ≤
                ‖typeISourceSmoothBlock Y A r s (W x)‖) →
              (∀ x y : ι, x ≠ y → 1 ≤ |W x-W y|) →
              let D := 2*Real.pi*T^d
              let L := Nat.ceil (2*D+2)
              let K := (Fintype.card (Fin 2 × (ZMod 2 × Fin (L+1))) : ℝ)
              (Fintype.card ι : ℝ) ≤ K*(4*(C*(2*T)^B*T^ε)) := by
  intro ε hε
  have hU : 2 ≤ 1/a := by
    apply (le_div_iff₀ ha).mpr
    linarith
  obtain ⟨C,hC,delta,hdelta,hfinite⟩ :=
    classicalReflected_uniform_colored_cardinality_bound
      sigma B (1/a) hB hU hLV ε hε
  refine ⟨C,hC,delta,hdelta,?_⟩
  intro s d u hs hLine hd hdOne huOne huLoss
  obtain ⟨k,_hk,hSource⟩ :=
    exists_order_eventually_interior_source_normalized_two_dyadic_family
      a d (delta/2) ha hd (by linarith)
  have hSourceAt := hSource s u hs huOne (by nlinarith)
  have hPhysical := eventually_classicalReflected_compact_scale_conditions
    C (1/a) delta 0 (by positivity) hdelta (by norm_num) (by norm_num) (by linarith)
  have hFourierRoom := eventually_classicalReflected_fourier_displacement_fits d hdOne
  obtain ⟨Tdisp,_hTdisp,hDisp⟩ := eventually_rpow_le_half_self d hdOne
  filter_upwards [hSourceAt,hPhysical,hFourierRoom,
    Filter.eventually_ge_atTop Tdisp,Filter.eventually_ge_atTop (8 : ℝ)] with
      T hSourceT hPhysicalT hFourierT hDispT hT
  dsimp only
  intro ι _ _ r W hr hLower hUpper hScale hRange hLarge hSep
  let Y := ⌊T^a⌋₊
  let Q := 2^r*Y
  let D := 2*Real.pi*T^d
  have hTPos : 0 < T := by linarith
  obtain ⟨W',label,hPert,hGeometry,_hEnergy⟩ :=
    hSourceT r W hr hLower hUpper hScale hLarge
  have hFinalRange : ∀ x, T/4 ≤ W' x ∧ W' x ≤ 4*T := by
    intro x
    have hx := hRange x
    have hp := abs_le.mp (hPert x)
    have hb := hDisp T hDispT
    constructor <;> linarith
  apply hfinite (2*Q) (classicalDirectDyadicLength Q) label T D W W'
    hTPos (by dsimp [D]; positivity) hSep hPert hFinalRange
  · intro x
    have hx := hGeometry x
    refine ⟨hx.1,?_⟩
    apply hPhysicalT (classicalDirectDyadicLength Q (label x)) hx.1
    · norm_num
      exact hx.2.2.2.1
    · exact hx.2.2.2.2.1
  · intro x
    have hx := hGeometry x
    have hNReal : (1 : ℝ) ≤ classicalDirectDyadicLength Q (label x) := by
      exact_mod_cast hx.1.le
    have hThreshold := (Real.rpow_le_rpow_of_exponent_le hNReal
      (show sigma-delta ≤ s-delta/2 by linarith)).trans hx.2.2.2.2.2
    rw [min_eq_left (Nat.mul_le_mul_left 2
      (classicalDirectDyadicLength_bounds Q (label x)).2)]
    exact hThreshold

theorem classicalDirect_shifted_line_source_energy_transfer
    (sigma B a : ℝ) (hB : 0 ≤ B) (ha : 0 < a) (haHalf : a ≤ 1/2)
    (hLV : ∀ tau ∈ Set.Icc (2 : ℝ) (1/a),
      IsZetaLargeValueEnergyBound sigma tau (B*tau)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 1 ≤ C ∧ ∃ delta : ℝ, 0 < delta ∧
        ∀ s d u : ℝ, 0 ≤ s → sigma-delta/2 ≤ s →
          0 < d → d < 1 → u ≤ 1 → u ≤ a*delta/4 →
          ∀ᶠ T : ℝ in Filter.atTop,
            let Y := ⌊T^a⌋₊
            let A := ⌊sharpZetaCutoff T⌋₊
            ∀ {ι : Type*} [Fintype ι] [LinearOrder ι] (r : ℕ) (W : ι → ℝ),
              let Q := 2^r*Y
              2 ≤ r → ((Y+1 : ℕ) : ℝ) ≤ (Q : ℝ)/2 → 2*Q ≤ A →
              2 ≤ typeILogarithmicScale T Q →
              (∀ x, T-T^d ≤ W x ∧ W x ≤ 2*T+T^d) →
              (∀ x, ((3/4)*(T^(-u)/2))/(Nat.clog 2 A+1 : ℕ) ≤
                ‖typeISourceSmoothBlock Y A r s (W x)‖) →
              (∀ x y : ι, x ≠ y → 1 ≤ |W x-W y|) →
              let D := 2*Real.pi*T^d
              let L := Nat.ceil (2*D+2)
              let K := (Fintype.card (Fin 2 × (ZMod 2 × Fin (L+1))) : ℝ)
              (approximateAdditiveEnergyOf 1 W : ℝ) ≤ (4*Nat.ceil (1+4*D)+6)*(9*K^4*(2304*(C*(2*T)^B*T^ε))) := by
  intro ε hε
  have hU : 2 ≤ 1/a := by
    apply (le_div_iff₀ ha).mpr
    linarith
  obtain ⟨C,hC,delta,hdelta,hfinite⟩ :=
    classicalReflected_uniform_colored_energy_bound
      sigma B (1/a) hB hU hLV ε hε
  refine ⟨C,hC,delta,hdelta,?_⟩
  intro s d u hs hLine hd hdOne huOne huLoss
  obtain ⟨k,_hk,hSource⟩ :=
    exists_order_eventually_interior_source_normalized_two_dyadic_family
      a d (delta/2) ha hd (by linarith)
  have hSourceAt := hSource s u hs huOne (by nlinarith)
  have hPhysical := eventually_classicalReflected_compact_scale_conditions
    C (1/a) delta 0 (by positivity) hdelta (by norm_num) (by norm_num) (by linarith)
  have hFourierRoom := eventually_classicalReflected_fourier_displacement_fits d hdOne
  obtain ⟨Tdisp,_hTdisp,hDisp⟩ := eventually_rpow_le_half_self d hdOne
  filter_upwards [hSourceAt,hPhysical,hFourierRoom,
    Filter.eventually_ge_atTop Tdisp,Filter.eventually_ge_atTop (8 : ℝ)] with
      T hSourceT hPhysicalT hFourierT hDispT hT
  dsimp only
  intro ι _ _ r W hr hLower hUpper hScale hRange hLarge hSep
  let Y := ⌊T^a⌋₊
  let Q := 2^r*Y
  let D := 2*Real.pi*T^d
  have hTPos : 0 < T := by linarith
  obtain ⟨W',label,hPert,hGeometry,_hEnergy⟩ :=
    hSourceT r W hr hLower hUpper hScale hLarge
  have hFinalRange : ∀ x, T/4 ≤ W' x ∧ W' x ≤ 4*T := by
    intro x
    have hx := hRange x
    have hp := abs_le.mp (hPert x)
    have hb := hDisp T hDispT
    constructor <;> linarith
  apply hfinite (2*Q) (classicalDirectDyadicLength Q) label T D W W'
    hTPos (by dsimp [D]; positivity) hSep hPert hFinalRange
  · intro x
    have hx := hGeometry x
    refine ⟨hx.1,?_⟩
    apply hPhysicalT (classicalDirectDyadicLength Q (label x)) hx.1
    · norm_num
      exact hx.2.2.2.1
    · exact hx.2.2.2.2.1
  · intro x
    have hx := hGeometry x
    have hNReal : (1 : ℝ) ≤ classicalDirectDyadicLength Q (label x) := by
      exact_mod_cast hx.1.le
    have hThreshold := (Real.rpow_le_rpow_of_exponent_le hNReal
      (show sigma-delta ≤ s-delta/2 by linarith)).trans hx.2.2.2.2.2
    rw [min_eq_left (Nat.mul_le_mul_left 2
      (classicalDirectDyadicLength_bounds Q (label x)).2)]
    exact hThreshold

end TaoTrudgianYang2025
