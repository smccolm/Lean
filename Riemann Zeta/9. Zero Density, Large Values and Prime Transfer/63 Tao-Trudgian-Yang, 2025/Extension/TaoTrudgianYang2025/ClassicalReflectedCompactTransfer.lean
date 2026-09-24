import TaoTrudgianYang2025.ClassicalReflectedHeightWindows
import TaoTrudgianYang2025.ClassicalTypeICardinalityUniformity

/-!
# Compact zeta bounds on reflected positive height windows

The constants and exponent window are chosen before every physical family.
Actual sharp coefficient-one patterns consume all four positive height
colors. Cardinality counts every fiber; energy uses the proved four-fiber
selection inequality rather than a cardinality-selected subset.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem classicalReflected_uniform_expanded_slab_cardinality_bound
    (σ B U : ℝ) (hB : 0 ≤ B) (hU : 2 ≤ U)
    (hLV : ∀ τ ∈ Set.Icc (2 : ℝ) U, IsZetaLargeValueBound σ τ (B*τ)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
        ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
          (A N : ℕ) (V T : ℝ) (W : ι → ℝ),
          1 < N → 0 < T → C ≤ (N : ℝ) →
          4 ≤ (N : ℝ)^(δ/2) →
          2-δ/2 ≤ typeILogarithmicScale T N →
          typeILogarithmicScale T N ≤ U+δ/2 →
          (∀ x, T/4 ≤ W x ∧ W x ≤ 4*T) →
          (∀ x y : ι, x ≠ y → 1 ≤ |W x-W y|) →
          (∀ x, V ≤ ‖∑ n ∈ Finset.Ioc N (min (2*N) A),
            dirichletPhase n (W x)‖) →
          (N : ℝ)^(σ-δ) ≤ V →
          (Fintype.card ι : ℝ) ≤ 4*(C*(2*T)^B*(N : ℝ)^ε) := by
  intro ε hε
  obtain ⟨C,hC,δ,hδ,hbound⟩ :=
    zetaLargeValueBound_uniform_near_logScale_interval σ B 2 U hB hU hLV ε hε
  refine ⟨C,hC,δ,hδ,?_⟩
  intro ι _ _ A N V T W hN hTpos hCN hPower hNL hNU hW hsep hlarge hVL
  classical
  have hNreal : 1 < (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hNreal
  have hVpos : 0 < (N : ℝ) ^ (σ - δ) := Real.rpow_pos_of_pos hNpos _
  let color : ι → Fin 4 := fun x => classicalReflectedHeightColor T (W x)
  let Wᵢ := fun i : Fin 4 =>
    fun x : EnergyColorFiber color i => W x.1
  have hclass (i : Fin 4) :
      (Fintype.card (EnergyColorFiber color i) : ℝ) ≤
        C * (2 * T) ^ B * (N : ℝ) ^ ε := by
    let H := classicalReflectedHeight T i
    have hH := classicalReflectedHeight_bounds T hTpos i
    have hWi : ∀ x : EnergyColorFiber color i,
        H ≤ Wᵢ i x ∧ Wᵢ i x ≤ 2 * H := by
      intro x
      have hx := classicalReflectedHeightColor_mem T (W x.1) (hW x.1)
      change classicalReflectedHeight T (color x.1) ≤ Wᵢ i x ∧
        Wᵢ i x ≤ 2 * classicalReflectedHeight T (color x.1) at hx
      simpa only [x.2] using hx
    have hsepi : ∀ x y : EnergyColorFiber color i,
        x ≠ y → 1 ≤ |Wᵢ i x - Wᵢ i y| := by
      intro x y hxy
      exact hsep x.1 y.1 (fun h => hxy (Subtype.ext h))
    have hlargei : ∀ x : EnergyColorFiber color i,
        (N : ℝ) ^ (σ - δ) ≤
          ‖∑ n ∈ Finset.Ioc N (min (2 * N) A), dirichletPhase n (Wᵢ i x)‖ :=
      fun x => hVL.trans (hlarge x.1)
    let P := indexedClassicalTypeIZetaPattern
      A N ((N : ℝ) ^ (σ - δ)) H (Wᵢ i) hN hVpos hH.1 hWi hsepi hlargei
    have hPN : P.N = N := rfl
    have hPT : P.T = H := by change 2 * H - H = H; ring
    have hpscale : ∃ α ∈ Set.Icc (2 : ℝ) U,
        |Real.logb P.N P.T - α| ≤ δ := by
      rw [hPN, hPT]
      exact classicalReflected_logScale_near_interval U δ T H N hU hδ.le
        hTpos hN hNL hNU hPower hH.2.1 hH.2.2
    have hp := hbound P hCN hpscale (by rfl : P.N ^ (σ - δ) ≤ P.V)
    have heq := indexedClassicalTypeIZetaPattern_card
      A N ((N : ℝ) ^ (σ - δ)) H (Wᵢ i) hN hVpos hH.1 hWi hsepi hlargei
    rw [show P.ordinates.card = Fintype.card (EnergyColorFiber color i) from heq,
      hPN, hPT] at hp
    exact hp.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hH.1.le hH.2.2 hB)
        (zero_le_one.trans hC)) (Real.rpow_nonneg hNpos.le _))
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using
    cardinality_le_color_count_mul color (C * (2 * T) ^ B * (N : ℝ) ^ ε) hclass


theorem classicalReflected_uniform_expanded_slab_energy_bound
    (σ B U : ℝ) (hB : 0 ≤ B) (hU : 2 ≤ U)
    (hLV : ∀ τ ∈ Set.Icc (2 : ℝ) U, IsZetaLargeValueEnergyBound σ τ (B*τ)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
        ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
          (A N : ℕ) (V T : ℝ) (W : ι → ℝ),
          1 < N → 0 < T → C ≤ (N : ℝ) →
          4 ≤ (N : ℝ)^(δ/2) →
          2-δ/2 ≤ typeILogarithmicScale T N →
          typeILogarithmicScale T N ≤ U+δ/2 →
          (∀ x, T/4 ≤ W x ∧ W x ≤ 4*T) →
          (∀ x y : ι, x ≠ y → 1 ≤ |W x-W y|) →
          (∀ x, V ≤ ‖∑ n ∈ Finset.Ioc N (min (2*N) A),
            dirichletPhase n (W x)‖) →
          (N : ℝ)^(σ-δ) ≤ V →
          (approximateAdditiveEnergyOf 1 W : ℝ) ≤ 2304*(C*(2*T)^B*(N : ℝ)^ε) := by
  intro ε hε
  obtain ⟨C,hC,δ,hδ,hbound⟩ :=
    zetaEnergyBound_uniform_near_logScale_interval σ B 2 U hB hU hLV ε hε
  refine ⟨C,hC,δ,hδ,?_⟩
  intro ι _ _ A N V T W hN hTpos hCN hPower hNL hNU hW hsep hlarge hVL
  classical
  have hNreal : 1 < (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hNreal
  have hVpos : 0 < (N : ℝ) ^ (σ - δ) := Real.rpow_pos_of_pos hNpos _
  let color : ι → Fin 4 := fun x => classicalReflectedHeightColor T (W x)
  obtain ⟨label, henergy⟩ := exists_energy_color_classes W color
  let Wᵢ := fun i : Fin 4 =>
    fun x : EnergyColorFiber color (label i) => W x.1
  have hclass (i : Fin 4) :
      (approximateAdditiveEnergyOf 1 (Wᵢ i) : ℝ) ≤
        C * (2 * T) ^ B * (N : ℝ) ^ ε := by
    let H := classicalReflectedHeight T (label i)
    have hH := classicalReflectedHeight_bounds T hTpos (label i)
    have hWi : ∀ x : EnergyColorFiber color (label i),
        H ≤ Wᵢ i x ∧ Wᵢ i x ≤ 2 * H := by
      intro x
      have hx := classicalReflectedHeightColor_mem T (W x.1) (hW x.1)
      change classicalReflectedHeight T (color x.1) ≤ Wᵢ i x ∧
        Wᵢ i x ≤ 2 * classicalReflectedHeight T (color x.1) at hx
      simpa only [x.2] using hx
    have hsepi : ∀ x y : EnergyColorFiber color (label i),
        x ≠ y → 1 ≤ |Wᵢ i x - Wᵢ i y| := by
      intro x y hxy
      exact hsep x.1 y.1 (fun h => hxy (Subtype.ext h))
    have hlargei : ∀ x : EnergyColorFiber color (label i),
        (N : ℝ) ^ (σ - δ) ≤
          ‖∑ n ∈ Finset.Ioc N (min (2 * N) A), dirichletPhase n (Wᵢ i x)‖ :=
      fun x => hVL.trans (hlarge x.1)
    let P := indexedClassicalTypeIZetaPattern
      A N ((N : ℝ) ^ (σ - δ)) H (Wᵢ i) hN hVpos hH.1 hWi hsepi hlargei
    have hPN : P.N = N := rfl
    have hPT : P.T = H := by change 2 * H - H = H; ring
    have hpscale : ∃ α ∈ Set.Icc (2 : ℝ) U,
        |Real.logb P.N P.T - α| ≤ δ := by
      rw [hPN, hPT]
      exact classicalReflected_logScale_near_interval U δ T H N hU hδ.le
        hTpos hN hNL hNU hPower hH.2.1 hH.2.2
    have hp := hbound P hCN hpscale (by rfl : P.N ^ (σ - δ) ≤ P.V)
    have heq := indexedClassicalTypeIZetaPattern_energy_eq
      A N ((N : ℝ) ^ (σ - δ)) H (Wᵢ i) hN hVpos hH.1 hWi hsepi hlargei
    rw [show finsetAdditiveEnergy P.ordinates =
      approximateAdditiveEnergyOf 1 (Wᵢ i) from heq, hPN, hPT] at hp
    exact hp.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hH.1.le hH.2.2 hB)
        (zero_le_one.trans hC)) (Real.rpow_nonneg hNpos.le _))
  have henergy' :
      4 * (approximateAdditiveEnergyOf 1 W : ℝ) ≤
        2304 * ((approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
          (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
          (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
          (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ)) := by
    simpa only [Fintype.card_fin, Nat.cast_ofNat, show (9 : ℝ) * 4 ^ 4 = 2304 by
      norm_num] using henergy
  linarith [hclass 0, hclass 1, hclass 2, hclass 3]


end TaoTrudgianYang2025

