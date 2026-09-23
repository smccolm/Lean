import TaoTrudgianYang2025.ClassicalTypeIUniformity
import TaoTrudgianYang2025.ClassicalTypeICardinalityLoss
import TaoTrudgianYang2025.LargeValueUniformity

/-!
# Uniform Type-I cardinality transfer

The source scales and all three positive slabs have logarithmic height near
the closed interval [1,1/a]. Constants and threshold windows are chosen
before the physical source scale.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem classicalTypeI_uniform_expanded_slab_cardinality_bound
    (σ B a : ℝ) (hB : 0 ≤ B) (ha : 0 < a) (haone : a ≤ 1)
    (hLV : ∀ τ ∈ Set.Icc (1 : ℝ) (1 / a),
      IsZetaLargeValueBound σ τ (B * τ)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
        ∀ᶠ T : ℝ in Filter.atTop,
          ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
            (A N : ℕ) (V : ℝ) (W : ι → ℝ),
            T ^ a ≤ (N : ℝ) → (N : ℝ) ≤ 6 * T →
            (∀ x, T / 2 ≤ W x ∧ W x ≤ 4 * T) →
            (∀ x y : ι, x ≠ y → 1 ≤ |W x - W y|) →
            (∀ x, V ≤ ‖∑ n ∈ Finset.Ioc N (min (2 * N) A),
              dirichletPhase n (W x)‖) →
            (N : ℝ) ^ (σ - δ) ≤ V →
            (Fintype.card ι : ℝ) ≤
              3 * (C * (2 * T) ^ B * (N : ℝ) ^ ε) := by
  intro ε hε
  obtain ⟨C, hC, δ, hδ, hbound⟩ :=
    zetaLargeValueBound_uniform_near_logScale_interval σ B 1 (1 / a) hB
      ((le_div_iff₀ ha).mpr (by simpa using haone)) hLV ε hε
  refine ⟨C, hC, δ, hδ, ?_⟩
  have hCevent := (tendsto_rpow_atTop ha).eventually (Filter.eventually_ge_atTop C)
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ), hCevent,
    eventually_classicalTypeI_logScale_near_interval a δ ha haone hδ] with
      T hT hTC hscale
  intro ι _ _ A N V W hNL hNU hW hsep hlarge hVL
  classical
  have hTpos : 0 < T := by linarith
  have hNreal : 1 < (N : ℝ) :=
    (Real.one_lt_rpow (by linarith : 1 < T) ha).trans_le hNL
  have hN : 1 < N := by exact_mod_cast hNreal
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hNreal
  have hVpos : 0 < (N : ℝ) ^ (σ - δ) := Real.rpow_pos_of_pos hNpos _
  let color : ι → Fin 3 := fun x => classicalTypeIHeightColor T (W x)
  let Wᵢ := fun i : Fin 3 =>
    fun x : EnergyColorFiber color i => W x.1
  have hclass (i : Fin 3) :
      (Fintype.card (EnergyColorFiber color i) : ℝ) ≤
        C * (2 * T) ^ B * (N : ℝ) ^ ε := by
    let H := classicalTypeIHeight T i
    have hH := classicalTypeIHeight_bounds T hTpos i
    have hWi : ∀ x : EnergyColorFiber color i,
        H ≤ Wᵢ i x ∧ Wᵢ i x ≤ 2 * H := by
      intro x
      have hx := classicalTypeIHeightColor_mem T (W x.1) (hW x.1)
      change classicalTypeIHeight T (color x.1) ≤ Wᵢ i x ∧
        Wᵢ i x ≤ 2 * classicalTypeIHeight T (color x.1) at hx
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
    have hpscale : ∃ α ∈ Set.Icc (1 : ℝ) (1 / a),
        |Real.logb P.N P.T - α| ≤ δ := by
      rw [hPN, hPT]
      exact hscale N H hNL hNU hH.2.1 hH.2.2
    have hp := hbound P (hTC.trans hNL) hpscale (by rfl : P.N ^ (σ - δ) ≤ P.V)
    have heq := indexedClassicalTypeIZetaPattern_card
      A N ((N : ℝ) ^ (σ - δ)) H (Wᵢ i) hN hVpos hH.1 hWi hsepi hlargei
    rw [show P.ordinates.card = Fintype.card (EnergyColorFiber color i) from heq,
      hPN, hPT] at hp
    exact hp.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hH.1.le hH.2.2 hB)
        (zero_le_one.trans hC)) (Real.rpow_nonneg hNpos.le _))
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using
    cardinality_le_color_count_mul color (C * (2 * T) ^ B * (N : ℝ) ^ ε) hclass


theorem classicalTypeI_uniform_fourier_cardinality_transfer
    (σ B a : ℝ) (hB : 0 ≤ B) (ha : 0 < a) (haone : a ≤ 1)
    (hLV : ∀ τ ∈ Set.Icc (1 : ℝ) (1 / a),
      IsZetaLargeValueBound σ τ (B * τ)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
        ∀ᶠ T : ℝ in Filter.atTop,
          ∀ {ι : Type*} [Fintype ι] [LinearOrder ι]
            (A N k : ℕ) (s V u : ℝ) (W : ι → ℝ),
            let d := 2 * Real.pi * classicalTypeIFourierRadius A N k s V
            let Q := V / (4 * (N : ℝ) ^ (-s) * classicalTypeIFourierL1 s)
            1 < N → 0 < V → 1 < k → 0 < T →
            T ^ a ≤ (N : ℝ) → (N : ℝ) ≤ 6 * T →
            u + d ≤ T / 2 →
            (∀ x, T - u ≤ W x ∧ W x ≤ 2 * T + u) →
            (∀ x, V ≤
              ‖dirichletPoly N (classicalZetaLongLineCoeff A s) (W x)‖) →
            (∀ x y : ι, x ≠ y → 1 ≤ |W x - W y|) →
            (N : ℝ) ^ (σ - δ) ≤ Q →
            (Fintype.card ι : ℝ) ≤
              classicalTypeIFourierCardinalityLoss d *
                (C * (2 * T) ^ B * (N : ℝ) ^ ε) := by
  intro ε hε
  obtain ⟨C, hC, δ, hδ, hfinite⟩ :=
    classicalTypeI_uniform_expanded_slab_cardinality_bound σ B a hB ha haone hLV ε hε
  refine ⟨C, hC, δ, hδ, ?_⟩
  filter_upwards [hfinite] with T hZeta
  intro ι _ _ A N k s V u W
  dsimp only
  let d := 2 * Real.pi * classicalTypeIFourierRadius A N k s V
  let L := Nat.ceil (2 * d + 2)
  let Q := V / (4 * (N : ℝ) ^ (-s) * classicalTypeIFourierL1 s)
  intro hN hV hk hT hNL hNU hroom hW hlarge hsep hQL
  have hd : 0 ≤ d :=
    mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
      (classicalTypeIFourierRadius_pos A N k s V hV hk).le
  classical
  obtain ⟨W', hpert, hlarge', _henergy⟩ :=
    exists_classicalTypeI_explicitBoundedOrdinate_family
      A N k s V W (by omega) hV hk hlarge
  let hlocal : ∀ z : ℤ, (unitBinFinset W' z).card ≤ L := fun z =>
    unitBinFinset_perturbation_card_le_natCeil W W' d hd hsep hpert z
  let color := boundedMultiplicityColor W' L hlocal
  let Wᵢ := fun c : ZMod 2 × Fin (L + 1) =>
    fun x : EnergyColorFiber color c => W' x.1
  have hclass (c : ZMod 2 × Fin (L + 1)) :
      (Fintype.card (EnergyColorFiber color c) : ℝ) ≤
        3 * (C * (2 * T) ^ B * (N : ℝ) ^ ε) := by
    apply hZeta A N Q (Wᵢ c) hNL hNU
      _ (oneSeparated_on_boundedMultiplicityColor W' L hlocal c)
      (fun x => hlarge' x.1) hQL
    intro x
    have hx := hW x.1
    have hp := abs_le.mp (hpert x.1)
    change T / 2 ≤ W' x.1 ∧ W' x.1 ≤ 4 * T
    constructor <;> linarith
  have hc := cardinality_le_color_count_mul color
    (3 * (C * (2 * T) ^ B * (N : ℝ) ^ ε)) hclass
  simpa only [classicalTypeIFourierCardinalityLoss, mul_assoc, L, d] using hc


end TaoTrudgianYang2025
