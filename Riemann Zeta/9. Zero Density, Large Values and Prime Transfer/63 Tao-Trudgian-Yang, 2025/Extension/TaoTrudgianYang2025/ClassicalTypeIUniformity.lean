import TaoTrudgianYang2025.ClassicalTypeIEnergyTransfer
import TaoTrudgianYang2025.EnergyUniformity

/-!
# Uniform Type I energy transfer

The physical source scale and its three positive height slabs approach the
closed exponent interval `[1,1/a]` uniformly. Compact-range zeta estimates
therefore choose the threshold window before the source cutoff parameters.
-/

noncomputable section

namespace TaoTrudgianYang2025

open RiemannZeta.GuthMaynard

/-- Every point in a thickened closed interval is within the thickening
distance of a point in the original interval. -/
theorem exists_mem_Icc_abs_sub_le_of_bounds
    (l u x δ : ℝ) (hlu : l ≤ u) (hδ : 0 ≤ δ)
    (hxL : l - δ ≤ x) (hxU : x ≤ u + δ) :
    ∃ y ∈ Set.Icc l u, |x - y| ≤ δ := by
  by_cases hxl : x < l
  · exact ⟨l, ⟨le_rfl, hlu⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  by_cases hxu : u < x
  · exact ⟨u, ⟨hlu, le_rfl⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  exact ⟨x, ⟨le_of_not_gt hxl, le_of_not_gt hxu⟩, by simpa using hδ⟩

/-- Source block lengths `T^a ≤ N ≤ 6T` place every positive height slab
`T/2 ≤ H ≤ 2T` in an arbitrarily small neighborhood of `[1,1/a]`.
The estimate is uniform in both `N` and `H`. -/
theorem eventually_classicalTypeI_logScale_near_interval
    (a δ : ℝ) (ha : 0 < a) (haone : a ≤ 1) (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ N H : ℝ,
      T ^ a ≤ N → N ≤ 6 * T → T / 2 ≤ H → H ≤ 2 * T →
      ∃ τ ∈ Set.Icc (1 : ℝ) (1 / a), |Real.logb N H - τ| ≤ δ := by
  have hpow := (tendsto_rpow_atTop (mul_pos ha hδ)).eventually
    (Filter.eventually_ge_atTop (12 : ℝ))
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ), hpow] with T hT hpower
  intro N H hNL hNU hHL hHU
  have hTpos : 0 < T := by linarith
  have hNone : 1 < N :=
    (Real.one_lt_rpow (by linarith : 1 < T) ha).trans_le hNL
  have hNpos : 0 < N := zero_lt_one.trans hNone
  have hHpos : 0 < H := by linarith
  have hNpower : 12 ≤ N ^ δ := by
    calc
      12 ≤ T ^ (a * δ) := hpower
      _ = (T ^ a) ^ δ := Real.rpow_mul hTpos.le a δ
      _ ≤ N ^ δ := Real.rpow_le_rpow (Real.rpow_nonneg hTpos.le _) hNL hδ.le
  have hNpowerpos : 0 < N ^ δ := Real.rpow_pos_of_pos hNpos _
  have hTupper : T ≤ N ^ (1 / a) := by
    calc
      T = (T ^ a) ^ (1 / a) := by
        rw [← Real.rpow_mul hTpos.le, mul_one_div_cancel ha.ne', Real.rpow_one]
      _ ≤ N ^ (1 / a) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hTpos.le _) hNL (by positivity)
  have hlogL : 1 - δ ≤ Real.logb N H := by
    apply (Real.le_logb_iff_rpow_le hNone hHpos).mpr
    rw [Real.rpow_sub hNpos, Real.rpow_one]
    apply (div_le_iff₀ hNpowerpos).mpr
    nlinarith
  have hlogU : Real.logb N H ≤ 1 / a + δ := by
    apply (Real.logb_le_iff_le_rpow hNone hHpos).mpr
    rw [Real.rpow_add hNpos]
    nlinarith [Real.rpow_pos_of_pos hNpos (1 / a)]
  exact exists_mem_Icc_abs_sub_le_of_bounds 1 (1 / a) (Real.logb N H) δ
    ((le_div_iff₀ ha).mpr (by simpa using haone)) hδ.le hlogL hlogU

/-- Uniform coefficient-one energy control on the full expanded source slab.
The same threshold window works for all actual physical source scales. -/
theorem classicalTypeI_uniform_expanded_slab_bound
    (σ B a : ℝ) (hB : 0 ≤ B) (ha : 0 < a) (haone : a ≤ 1)
    (hLV : ∀ τ ∈ Set.Icc (1 : ℝ) (1 / a),
      IsZetaLargeValueEnergyBound σ τ (B * τ)) :
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
            (approximateAdditiveEnergyOf 1 W : ℝ) ≤
              729 * (C * (2 * T) ^ B * (N : ℝ) ^ ε) := by
  intro ε hε
  obtain ⟨C, hC, δ, hδ, hbound⟩ :=
    zetaEnergyBound_uniform_near_logScale_interval σ B 1 (1 / a) hB
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
  obtain ⟨label, henergy⟩ := exists_energy_color_classes W color
  let Wᵢ := fun i : Fin 4 =>
    fun x : EnergyColorFiber color (label i) => W x.1
  have hclass (i : Fin 4) :
      (approximateAdditiveEnergyOf 1 (Wᵢ i) : ℝ) ≤
        C * (2 * T) ^ B * (N : ℝ) ^ ε := by
    let H := classicalTypeIHeight T (label i)
    have hH := classicalTypeIHeight_bounds T hTpos (label i)
    have hWi : ∀ x : EnergyColorFiber color (label i),
        H ≤ Wᵢ i x ∧ Wᵢ i x ≤ 2 * H := by
      intro x
      have hx := classicalTypeIHeightColor_mem T (W x.1) (hW x.1)
      change classicalTypeIHeight T (color x.1) ≤ Wᵢ i x ∧
        Wᵢ i x ≤ 2 * classicalTypeIHeight T (color x.1) at hx
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
    have hpscale : ∃ α ∈ Set.Icc (1 : ℝ) (1 / a),
        |Real.logb P.N P.T - α| ≤ δ := by
      rw [hPN, hPT]
      exact hscale N H hNL hNU hH.2.1 hH.2.2
    have hp := hbound P (hTC.trans hNL) hpscale (by rfl : P.N ^ (σ - δ) ≤ P.V)
    have heq := indexedClassicalTypeIZetaPattern_energy_eq
      A N ((N : ℝ) ^ (σ - δ)) H (Wᵢ i) hN hVpos hH.1 hWi hsepi hlargei
    rw [show finsetAdditiveEnergy P.ordinates =
      approximateAdditiveEnergyOf 1 (Wᵢ i) from heq, hPN, hPT] at hp
    exact hp.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hH.1.le hH.2.2 hB)
        (zero_le_one.trans hC)) (Real.rpow_nonneg hNpos.le _))
  have henergy' :
      4 * (approximateAdditiveEnergyOf 1 W : ℝ) ≤
        729 * ((approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
          (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
          (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
          (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ)) := by
    simpa only [Fintype.card_fin, Nat.cast_ofNat, show (9 : ℝ) * 3 ^ 4 = 729 by
      norm_num] using henergy
  linarith [hclass 0, hclass 1, hclass 2, hclass 3]

/-- The uniform zeta bound consumes the Fourier-deweighted source classes.
The source real-part parameter is independent of the zeta exponent parameter;
their relation is expressed only through the actual normalized threshold. -/
theorem classicalTypeI_uniform_fourier_energy_transfer
    (σ B a : ℝ) (hB : 0 ≤ B) (ha : 0 < a) (haone : a ≤ 1)
    (hLV : ∀ τ ∈ Set.Icc (1 : ℝ) (1 / a),
      IsZetaLargeValueEnergyBound σ τ (B * τ)) :
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
            (approximateAdditiveEnergyOf 1 W : ℝ) ≤
              classicalTypeIFourierEnergyLoss d *
                (C * (2 * T) ^ B * (N : ℝ) ^ ε) := by
  intro ε hε
  obtain ⟨C, hC, δ, hδ, hfinite⟩ :=
    classicalTypeI_uniform_expanded_slab_bound σ B a hB ha haone hLV ε hε
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
  obtain ⟨W', hpert, label, htransfer, henergy, hlarge', hseparated⟩ :=
    exists_separated_classicalTypeI_explicitFourier_energy_classes
      A N k s V W (by omega) hV hk hlarge hsep
  let hlocal : ∀ z : ℤ, (unitBinFinset W' z).card ≤ L := fun z =>
    unitBinFinset_perturbation_card_le_natCeil W W' d hd hsep hpert z
  let color := boundedMultiplicityColor W' L hlocal
  let Wᵢ := fun i : Fin 4 =>
    fun x : EnergyColorFiber color (label i) => W' x.1
  let E := 729 * (C * (2 * T) ^ B * (N : ℝ) ^ ε)
  have hclass (i : Fin 4) :
      (approximateAdditiveEnergyOf 1 (Wᵢ i) : ℝ) ≤ E := by
    apply hZeta A N Q (Wᵢ i) hNL hNU _ (hseparated i) (hlarge' i) hQL
    intro x
    have hx := hW x.1
    have hp := abs_le.mp (hpert x.1)
    change T / 2 ≤ W' x.1 ∧ W' x.1 ≤ 4 * T
    constructor <;> linarith
  have hSum :
      (approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
          (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
          (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
          (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ) ≤ 4 * E := by
    linarith [hclass 0, hclass 1, hclass 2, hclass 3]
  let K : ℝ := 9 * (Fintype.card (ZMod 2 × Fin (L + 1)) : ℝ) ^ 4
  have hK : 0 ≤ K := by positivity
  have hshifted : (approximateAdditiveEnergyOf 1 W' : ℝ) ≤ K * E := by
    have hprod := mul_le_mul_of_nonneg_left hSum hK
    change 4 * (approximateAdditiveEnergyOf 1 W' : ℝ) ≤
      K * ((approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
        (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
        (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
        (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ)) at henergy
    nlinarith
  have htransferReal :
      (approximateAdditiveEnergyOf 1 W : ℝ) ≤
        (4 * Nat.ceil (1 + 4 * d) + 6) *
          (approximateAdditiveEnergyOf 1 W' : ℝ) := by
    exact_mod_cast htransfer
  calc
    (approximateAdditiveEnergyOf 1 W : ℝ) ≤
        (4 * Nat.ceil (1 + 4 * d) + 6) *
          (approximateAdditiveEnergyOf 1 W' : ℝ) := htransferReal
    _ ≤ (4 * Nat.ceil (1 + 4 * d) + 6) * (K * E) :=
      mul_le_mul_of_nonneg_left hshifted (by positivity)
    _ = classicalTypeIFourierEnergyLoss d *
        (C * (2 * T) ^ B * (N : ℝ) ^ ε) := by
      simp only [classicalTypeIFourierEnergyLoss, K, E, L]
      ring

/-- Uniform source Type I energy estimate in the physical height. The zeta
hypotheses choose `δ` before the source line `s` and threshold power `D`.
In particular a slightly left-shifted real-part line is permitted. The
Fourier order, all coloring losses, and the physical scale window are
discharged from the actual sharp source polynomial. -/
theorem classicalTypeI_uniform_source_energy_bound
    (σ B a : ℝ) (hB : 0 ≤ B) (ha : 0 < a) (haone : a ≤ 1)
    (hLV : ∀ τ ∈ Set.Icc (1 : ℝ) (1 / a),
      IsZetaLargeValueEnergyBound σ τ (B * τ)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
        ∀ s D : ℝ, 0 ≤ s → σ - δ / 2 ≤ s → 0 ≤ D + 1 → D ≤ a * δ / 4 →
          ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ θ ≤ ε / 40 ∧
            ∀ᶠ T : ℝ in Filter.atTop,
              ∀ {ι : Type*} [Fintype ι] [LinearOrder ι]
                (N : ℕ) (W : ι → ℝ),
                T ^ a ≤ (N : ℝ) →
                (∀ x, T - T ^ θ ≤ W x ∧ W x ≤ 2 * T + T ^ θ) →
                (∀ x,
                  ((3 / 4 : ℝ) * (T ^ (-D) / 2)) /
                      Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ ≤
                    ‖dirichletPoly N
                      (classicalZetaLongLineCoeff ⌊sharpZetaCutoff T⌋₊ s) (W x)‖) →
                (∀ x y : ι, x ≠ y → 1 ≤ |W x - W y|) →
                (approximateAdditiveEnergyOf 1 W : ℝ) ≤ C * T ^ (B + ε) := by
  intro ε hε
  obtain ⟨C, hC, δ, hδ, hfinite⟩ :=
    classicalTypeI_uniform_fourier_energy_transfer σ B a hB ha haone hLV
      (ε / 2) (by linarith)
  let Cfinal : ℝ := max 1 (C * (2 : ℝ) ^ B * (6 : ℝ) ^ (ε / 2))
  refine ⟨Cfinal, le_max_left _ _, δ, hδ, ?_⟩
  intro s D hs hsσ hD hDloss
  let θ : ℝ := min (1 / 4) (ε / 40)
  have hθ : 0 < θ := lt_min (by norm_num) (by positivity)
  have hθone : θ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hgap : 5 * θ < ε / 2 := by
    have hsmall : θ ≤ ε / 40 := min_le_right _ _
    linarith
  obtain ⟨k, hk, hradius⟩ :=
    exists_order_eventually_classicalTypeIFourierRadius_sharpCutoff_le_rpow
      s D θ hs hD hθ
  have hthreshold := eventually_classicalTypeI_normalized_sourceThreshold_lower
    s a (δ / 2) D ha (by linarith) (by linarith)
  have hroom := eventually_classicalTypeI_displacements_fit θ hθone
  have hloss := eventually_classicalTypeIFourierEnergyLoss_le_rpow
    θ (ε / 2) hθ.le hgap
  refine ⟨θ, hθ, hθone, min_le_right _ _, ?_⟩
  filter_upwards [hfinite, hradius, hthreshold, hroom, hloss,
    Filter.eventually_ge_atTop (8 : ℝ)] with
      T hfinite hradius hthreshold hroom hloss hT
  intro ι _ _ N W hscale hW hlarge hsep
  have hTpos : 0 < T := by linarith
  have hNreal : 1 < (N : ℝ) :=
    (Real.one_lt_rpow (by linarith : 1 < T) ha).trans_le hscale
  have hN : 1 < N := by exact_mod_cast hNreal
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hNreal
  have hCnonneg : 0 ≤ C := zero_le_one.trans hC
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
    have he : approximateAdditiveEnergyOf 1 W = 0 := by
      simp [approximateAdditiveEnergyOf]
    rw [he, Nat.cast_zero]
    exact mul_nonneg (zero_le_one.trans (le_max_left _ _))
      (Real.rpow_nonneg hTpos.le _)
  | inr hnonempty =>
    let A := ⌊sharpZetaCutoff T⌋₊
    let V := ((3 / 4 : ℝ) * (T ^ (-D) / 2)) / Nat.clog 2 A
    let R := classicalTypeIFourierRadius A N k s V
    let d := 2 * Real.pi * R
    have hA : 1 < A := by
      apply lt_of_lt_of_le (by omega : 1 < (2 : ℕ))
      apply Nat.le_floor
      exact (show (2 : ℝ) ≤ 4 * T by linarith).trans
        (four_mul_lt_sharpZetaCutoff T).le
    have hV : 0 < V := by
      have hc : 0 < Nat.clog 2 A := Nat.clog_pos Nat.one_lt_two hA
      dsimp only [V]
      positivity
    have hR : R ≤ T ^ θ := hradius N (W (Classical.choice hnonempty))
      (by omega) (hlarge (Classical.choice hnonempty))
    have hd : 0 ≤ d := mul_nonneg (show 0 ≤ 2 * Real.pi by positivity)
      (classicalTypeIFourierRadius_pos A N k s V hV hk).le
    have hdBound : d ≤ 2 * Real.pi * T ^ θ :=
      mul_le_mul_of_nonneg_left hR (by positivity)
    have hNU : (N : ℝ) ≤ 6 * T :=
      classicalTypeI_source_large_scale_le_six_mul N s T D
        (W (Classical.choice hnonempty)) hT (hlarge (Classical.choice hnonempty))
    have hQL : (N : ℝ) ^ (σ - δ) ≤
        V / (4 * (N : ℝ) ^ (-s) * classicalTypeIFourierL1 s) :=
      (Real.rpow_le_rpow_of_exponent_le hNreal.le (by linarith)).trans
        (hthreshold N hscale)
    have henergy := hfinite A N k s V (T ^ θ) W
      hN hV hk hTpos hscale hNU (hroom R hR) hW hlarge hsep hQL
    calc
      (approximateAdditiveEnergyOf 1 W : ℝ) ≤
          classicalTypeIFourierEnergyLoss d *
            (C * (2 * T) ^ B * (N : ℝ) ^ (ε / 2)) := henergy
      _ ≤ T ^ (ε / 2) * (C * (2 * T) ^ B * (N : ℝ) ^ (ε / 2)) :=
        mul_le_mul_of_nonneg_right (hloss d hd hdBound) (by positivity)
      _ ≤ T ^ (ε / 2) * (C * (2 * T) ^ B * (6 * T) ^ (ε / 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hNpos.le hNU (by linarith))
            (by positivity)) (Real.rpow_nonneg hTpos.le _)
      _ = (C * (2 : ℝ) ^ B * (6 : ℝ) ^ (ε / 2)) * T ^ (B + ε) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hTpos.le,
          Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6) hTpos.le]
        have hp : T ^ (ε / 2) * T ^ B * T ^ (ε / 2) = T ^ (B + ε) := by
          rw [← Real.rpow_add hTpos, ← Real.rpow_add hTpos]
          congr 1
          ring
        calc
          _ = (C * (2 : ℝ) ^ B * (6 : ℝ) ^ (ε / 2)) *
              (T ^ (ε / 2) * T ^ B * T ^ (ε / 2)) := by ring
          _ = _ := by rw [hp]
      _ ≤ Cfinal * T ^ (B + ε) := mul_le_mul_of_nonneg_right
        (le_max_right _ _) (Real.rpow_nonneg hTpos.le _)

/-- The uniform physical-height estimate consumes an actual Type I color
fiber of the shifted zero multiset. The floor loss is included, and no
separately supplied height window, polynomial, or separation certificate
remains on this fiber. -/
theorem classicalTypeI_uniform_source_class_energy_bound
    (σ B a : ℝ) (hB : 0 ≤ B) (ha : 0 < a) (hatwo : a ≤ 2)
    (hLV : ∀ τ ∈ Set.Icc (1 : ℝ) (2 / a),
      IsZetaLargeValueEnergyBound σ τ (B * τ)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
        ∀ s D : ℝ, 0 ≤ s → σ - δ / 2 ≤ s → 0 ≤ D + 1 → D ≤ a * δ / 8 →
          ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ θ ≤ ε / 40 ∧
            ∀ᶠ T : ℝ in Filter.atTop,
              let Y := ⌊T ^ a⌋₊
              ∀ (X L : ℕ)
                (shiftedZero : ↥(zerosInRect s 1 T (2 * T)) → ℝ)
                (baseColor : ↥(zerosInRect s 1 T (2 * T)) →
                  ClassicalBranchScaleColor T Y)
                (hlocal : ∀ z : ℤ,
                  (unitBinFinset (fun x : ClassicalSlabZeroCopy s T =>
                    shiftedZero x.1) z).card ≤ L)
                (label : ClassicalSeparatedBranchScaleColor T Y L)
                (r : Fin (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊)),
                label.1 = some (Sum.inl r) →
                (∀ ρ, T - T ^ θ ≤ shiftedZero ρ ∧
                  shiftedZero ρ ≤ 2 * T + T ^ θ) →
                (∀ x : EnergyColorFiber
                  (classicalSeparatedBranchScaleColor s T Y
                    shiftedZero baseColor L hlocal) label,
                  ClassicalBranchScaleLarge s T D Y X label.1 (shiftedZero x.1.1)) →
                (approximateAdditiveEnergyOf 1
                    (fun x : EnergyColorFiber
                      (classicalSeparatedBranchScaleColor s T Y
                        shiftedZero baseColor L hlocal) label =>
                      shiftedZero x.1.1) : ℝ) ≤ C * T ^ (B + ε) := by
  intro ε hε
  have hinterval : 1 / (a / 2) = 2 / a := by rw [div_div_eq_mul_div]; ring
  have hLV' : ∀ τ ∈ Set.Icc (1 : ℝ) (1 / (a / 2)),
      IsZetaLargeValueEnergyBound σ τ (B * τ) := by
    simpa only [hinterval] using hLV
  obtain ⟨C, hC, δ, hδ, hsource⟩ :=
    classicalTypeI_uniform_source_energy_bound σ B (a / 2)
      hB (by linarith) (by linarith) hLV' ε hε
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro s D hs hsσ hD hDloss
  obtain ⟨θ, hθ, hθone, hθε, hbound⟩ := hsource s D hs hsσ hD (by linarith)
  refine ⟨θ, hθ, hθone, hθε, ?_⟩
  filter_upwards [hbound, eventually_classicalTypeI_sourceScale_lower a ha] with
    T hbound hscale
  dsimp only
  intro X L shiftedZero baseColor hlocal label r hlabel hW hlarge
  let Y := ⌊T ^ a⌋₊
  let N := 2 ^ (r : ℕ) * Y
  let color := classicalSeparatedBranchScaleColor s T Y shiftedZero baseColor L hlocal
  let W := fun x : EnergyColorFiber color label => shiftedZero x.1.1
  apply hbound N W (hscale r)
  · intro x
    exact hW x.1.1
  · intro x
    have hx := hlarge x
    rw [hlabel] at hx
    exact hx.1
  · intro x y hxy
    exact separatedRefinementColor_oneSeparated
      (fun z : ClassicalSlabZeroCopy s T => shiftedZero z.1)
      (fun z => baseColor z.1) L hlocal label x y hxy

end TaoTrudgianYang2025
