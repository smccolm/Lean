import TaoTrudgianYang2025.ZeroEnergyDichotomy
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Source Type-I thresholds and zeta energy patterns

The sharp Type-I Fourier extraction has an explicit threshold and preserves
an indexed family of ordinates. This module matches that threshold to powers
of the actual dyadic scale and retains the coefficient-one interval needed
by the zeta-specific energy bound.
-/

noncomputable section

namespace TaoTrudgianYang2025

open RiemannZeta.GuthMaynard

/-- The sharp-cutoff dyadic count grows at most logarithmically in the
physical height, with a constant independent of the extracted scale. -/
theorem classicalTypeI_sharpCutoff_clog_le_const_mul_log
    (T : ℝ) (hT : 8 ≤ T) :
    (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ : ℝ) ≤
      (1 + 2 / Real.log 2) * Real.log T := by
  have hLogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLogSixT : Real.log 6 ≤ Real.log T :=
    Real.log_le_log (by norm_num) (by linarith)
  have hLogOne : 1 ≤ Real.log T := by
    have hExpT : Real.exp 1 ≤ T :=
      (Real.exp_one_lt_three.le.trans (by norm_num : (3 : ℝ) ≤ 8)).trans hT
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hExpT
  calc
    (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ : ℝ) ≤
        1 + (Real.log 6 + Real.log T) / Real.log 2 :=
      sharp_cutoff_clog_le_log_majorant T hT
    _ ≤ Real.log T + (2 * Real.log T) / Real.log 2 := by
      have hfrac := div_le_div_of_nonneg_right
        (show Real.log 6 + Real.log T ≤ 2 * Real.log T by linarith)
        hLogTwo.le
      linarith
    _ = (1 + 2 / Real.log 2) * Real.log T := by ring

/-- Any fixed nonnegative multiple of the source dyadic-count loss is
eventually absorbed by any positive power of the physical height. -/
theorem eventually_const_mul_classicalTypeI_clog_le_rpow
    (C η : ℝ) (hC : 0 ≤ C) (hη : 0 < η) :
    ∀ᶠ T : ℝ in Filter.atTop,
      C * Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ ≤ T ^ η := by
  filter_upwards [eventually_one_add_const_mul_log_le_rpow
    (C * (1 + 2 / Real.log 2)) η hη,
    Filter.eventually_ge_atTop (8 : ℝ)] with T hbound hT
  have hclog := mul_le_mul_of_nonneg_left
    (classicalTypeI_sharpCutoff_clog_le_const_mul_log T hT) hC
  nlinarith

/-- Exact normalized threshold returned by the sharp Fourier extraction,
with its scale power separated from the height and logarithmic losses. -/
theorem classicalTypeI_normalized_sourceThreshold_eq
    (A N : ℕ) (σ T D : ℝ) (hA : 1 < A) (hN : 0 < N) (hT : 0 < T) :
    (((3 / 4 : ℝ) * (T ^ (-D) / 2)) / Nat.clog 2 A) /
        (4 * (N : ℝ) ^ (-σ) * classicalTypeIFourierL1 σ) =
      (N : ℝ) ^ σ /
        ((32 / 3 : ℝ) * classicalTypeIFourierL1 σ *
          Nat.clog 2 A * T ^ D) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hclog : (0 : ℝ) < Nat.clog 2 A := by
    exact_mod_cast Nat.clog_pos Nat.one_lt_two hA
  have hL := classicalTypeIFourierL1_pos σ
  have hTD := Real.rpow_pos_of_pos hT D
  have hNS := Real.rpow_pos_of_pos hNpos σ
  rw [Real.rpow_neg hT.le, Real.rpow_neg hNpos.le]
  field_simp
  ring

/-- Source threshold matching, uniform in every extracted scale satisfying
the physical lower bound. The source threshold exponent spends at most half
of the prescribed scale exponent loss; the fixed Fourier norm and dyadic
count are absorbed by the other half. -/
theorem eventually_classicalTypeI_normalized_sourceThreshold_lower
    (σ a ε D : ℝ) (ha : 0 < a) (hε : 0 < ε)
    (hD : D ≤ a * ε / 2) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ N : ℕ, T ^ a ≤ (N : ℝ) →
      (N : ℝ) ^ (σ - ε) ≤
        (((3 / 4 : ℝ) * (T ^ (-D) / 2)) /
            Nat.clog 2 ⌊sharpZetaCutoff T⌋₊) /
          (4 * (N : ℝ) ^ (-σ) * classicalTypeIFourierL1 σ) := by
  let K : ℝ := (32 / 3) * classicalTypeIFourierL1 σ
  have hK : 0 < K := mul_pos (by norm_num) (classicalTypeIFourierL1_pos σ)
  have hη : 0 < a * ε / 2 := by positivity
  filter_upwards [eventually_const_mul_classicalTypeI_clog_le_rpow
    K (a * ε / 2) hK.le hη,
    Filter.eventually_ge_atTop (8 : ℝ)] with T hclog hT
  intro N hscale
  have hTpos : 0 < T := by linarith
  have hTone : 1 ≤ T := by linarith
  have hNpos : (0 : ℝ) < N :=
    (Real.rpow_pos_of_pos hTpos a).trans_le hscale
  have hNnat : 0 < N := by exact_mod_cast hNpos
  have hA : 1 < ⌊sharpZetaCutoff T⌋₊ := by
    apply lt_of_lt_of_le (by omega : 1 < (2 : ℕ))
    apply Nat.le_floor
    exact (show (2 : ℝ) ≤ 4 * T by linarith).trans
      (four_mul_lt_sharpZetaCutoff T).le
  have hclogPos : (0 : ℝ) < Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ := by
    exact_mod_cast Nat.clog_pos Nat.one_lt_two hA
  have hdenPos : 0 <
      K * Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ * T ^ D := by positivity
  have hden : K * Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ * T ^ D ≤
      (N : ℝ) ^ ε := by
    calc
      K * Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ * T ^ D ≤
          T ^ (a * ε / 2) * T ^ D :=
        mul_le_mul_of_nonneg_right hclog (Real.rpow_nonneg hTpos.le _)
      _ = T ^ (a * ε / 2 + D) := (Real.rpow_add hTpos _ _).symm
      _ ≤ T ^ (a * ε) :=
        Real.rpow_le_rpow_of_exponent_le hTone (by linarith)
      _ = (T ^ a) ^ ε := Real.rpow_mul hTpos.le _ _
      _ ≤ (N : ℝ) ^ ε :=
        Real.rpow_le_rpow (Real.rpow_nonneg hTpos.le _) hscale hε.le
  rw [classicalTypeI_normalized_sourceThreshold_eq
    _ N σ T D hA hNnat hTpos, Real.rpow_sub hNpos]
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hNpos.le _) hdenPos hden

/-- The coefficient-one sharp block on a genuine positive dyadic height
interval is a zeta large-value pattern. The excluded left support endpoint
is recorded by the active integer interval starting at `N+1`. -/
def indexedClassicalTypeIZetaPattern
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A N : ℕ) (V H : ℝ) (W : ι → ℝ)
    (hN : 1 < N) (hV : 0 < V) (hH : 0 < H)
    (hW : ∀ x, H ≤ W x ∧ W x ≤ 2 * H)
    (hsep : ∀ x y : ι, x ≠ y → 1 ≤ |W x - W y|)
    (hlarge : ∀ x, V ≤
      ‖∑ n ∈ Finset.Ioc N (min (2 * N) A), dirichletPhase n (W x)‖) :
    ZetaLargeValuePattern where
  toLargeValuePattern :=
    indexedClassicalTypeICoefficientOnePattern A N V H (2 * H) W
      hN hV (by linarith) hW hsep hlarge
  active := Finset.Ioc N (min (2 * N) A)
  active_isInterval := by
    refine ⟨N + 1, min (2 * N) A, ?_⟩
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  active_subset := by
    intro n hn
    change n ∈ Finset.Icc N (2 * N)
    simp only [Finset.mem_Ioc] at hn
    simp only [Finset.mem_Icc]
    omega
  coeff_eq_indicator := by
    intro n hn
    change n ∈ Finset.Icc N (2 * N) at hn
    change closedDyadicCoeff N (classicalTypeICoefficientOneCoeff A) n =
      if n ∈ Finset.Ioc N (min (2 * N) A) then 1 else 0
    simp only [closedDyadicCoeff, classicalTypeICoefficientOneCoeff,
      Finset.mem_Ioc, Finset.mem_Icc] at *
    split_ifs <;> first | rfl | omega
  intervalLeft_eq := by change H = 2 * H - H; ring
  intervalRight_eq := by change 2 * H = 2 * (2 * H - H); ring

/-- Zeta pattern conversion retains the complete indexed energy. -/
theorem indexedClassicalTypeIZetaPattern_energy_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A N : ℕ) (V H : ℝ) (W : ι → ℝ)
    (hN : 1 < N) (hV : 0 < V) (hH : 0 < H)
    (hW : ∀ x, H ≤ W x ∧ W x ≤ 2 * H)
    (hsep : ∀ x y : ι, x ≠ y → 1 ≤ |W x - W y|)
    (hlarge : ∀ x, V ≤
      ‖∑ n ∈ Finset.Ioc N (min (2 * N) A), dirichletPhase n (W x)‖) :
    finsetAdditiveEnergy
        (indexedClassicalTypeIZetaPattern A N V H W hN hV hH hW hsep hlarge).ordinates =
      approximateAdditiveEnergyOf 1 W :=
  indexedClassicalTypeICoefficientOnePattern_energy_eq
    A N V H (2 * H) W hN hV (by linarith) hW hsep hlarge

/-- Three positive dyadic height slabs cover the perturbed source interval. -/
def classicalTypeIHeightColor (T t : ℝ) : Fin 3 :=
  if t < T then 0 else if t < 2 * T then 1 else 2

def classicalTypeIHeight (T : ℝ) (c : Fin 3) : ℝ :=
  if c = 0 then T / 2 else if c = 1 then T else 2 * T

theorem classicalTypeIHeight_bounds (T : ℝ) (hT : 0 < T) (c : Fin 3) :
    0 < classicalTypeIHeight T c ∧
      T / 2 ≤ classicalTypeIHeight T c ∧ classicalTypeIHeight T c ≤ 2 * T := by
  unfold classicalTypeIHeight
  split_ifs <;> exact ⟨by linarith, by linarith, by linarith⟩

theorem classicalTypeIHeightColor_mem (T t : ℝ)
    (ht : T / 2 ≤ t ∧ t ≤ 4 * T) :
    classicalTypeIHeight T (classicalTypeIHeightColor T t) ≤ t ∧
      t ≤ 2 * classicalTypeIHeight T (classicalTypeIHeightColor T t) := by
  unfold classicalTypeIHeightColor
  split_ifs with hfirst hsecond <;>
    simp only [classicalTypeIHeight, Fin.reduceEq, ↓reduceIte] <;>
      constructor <;> linarith [ht.1, ht.2]

/-- A zeta energy bound controls a sharp coefficient-one family throughout
the expanded positive slab. Three height colors preserve the coefficient
indicator and the ordinate values, so the source zeta hypothesis applies
without translating the polynomial. Only a lower threshold bound is needed:
the pattern is assigned the exact lower edge of the exponent window. -/
theorem IsZetaLargeValueEnergyBound.classicalTypeI_expanded_slab_bound
    {σ τ ρstar : ℝ} (hLV : IsZetaLargeValueEnergyBound σ τ ρstar) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
        ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
          (A N : ℕ) (V T : ℝ) (W : ι → ℝ),
          1 < N → 0 < T →
          (∀ x, T / 2 ≤ W x ∧ W x ≤ 4 * T) →
          (∀ x y : ι, x ≠ y → 1 ≤ |W x - W y|) →
          (∀ x, V ≤ ‖∑ n ∈ Finset.Ioc N (min (2 * N) A),
            dirichletPhase n (W x)‖) →
          C ≤ (N : ℝ) →
          (N : ℝ) ^ (τ - δ) ≤ T / 2 →
          2 * T ≤ (N : ℝ) ^ (τ + δ) →
          (N : ℝ) ^ (σ - δ) ≤ V →
          (approximateAdditiveEnergyOf 1 W : ℝ) ≤
            729 * (C * (N : ℝ) ^ (ρstar + ε)) := by
  intro ε hε
  obtain ⟨C, hC, δ, hδ, hbound⟩ := hLV ε hε
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro ι _ _ A N V T W hN hT hW hsep hlarge hCN hTL hTU hVL
  classical
  let color : ι → Fin 3 := fun x => classicalTypeIHeightColor T (W x)
  obtain ⟨label, henergy⟩ := exists_energy_color_classes W color
  let Wᵢ := fun i : Fin 4 =>
    fun x : EnergyColorFiber color (label i) => W x.1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hVpos : 0 < (N : ℝ) ^ (σ - δ) := Real.rpow_pos_of_pos hNpos _
  have hclass (i : Fin 4) :
      (approximateAdditiveEnergyOf 1 (Wᵢ i) : ℝ) ≤
        C * (N : ℝ) ^ (ρstar + ε) := by
    let H := classicalTypeIHeight T (label i)
    have hH := classicalTypeIHeight_bounds T hT (label i)
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
    have hPV : P.V = (N : ℝ) ^ (σ - δ) := rfl
    have hlow : P.N ^ (τ - δ) ≤ P.T := by
      rw [hPN, hPT]
      exact hTL.trans hH.2.1
    have hupp : P.T ≤ P.N ^ (τ + δ) := by
      rw [hPN, hPT]
      exact hH.2.2.trans hTU
    have hvupp : P.V ≤ P.N ^ (σ + δ) := by
      rw [hPV, hPN]
      exact Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast hN.le) (by linarith)
    have heq := indexedClassicalTypeIZetaPattern_energy_eq
      A N ((N : ℝ) ^ (σ - δ)) H (Wᵢ i) hN hVpos hH.1 hWi hsepi hlargei
    have hp := hbound P hCN hlow hupp (by rw [hPN, hPV]) hvupp
    rw [show finsetAdditiveEnergy P.ordinates =
      approximateAdditiveEnergyOf 1 (Wᵢ i) from heq, hPN] at hp
    exact hp
  have henergy' :
      4 * (approximateAdditiveEnergyOf 1 W : ℝ) ≤
        729 * ((approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
          (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
          (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
          (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ)) := by
    simpa only [Fintype.card_fin, Nat.cast_ofNat, show (9 : ℝ) * 3 ^ 4 = 729 by
      norm_num] using henergy
  linarith [hclass 0, hclass 1, hclass 2, hclass 3]

/-- Source-faithful finite Type-I energy transfer using the zeta-specific
bound. The beta-removal expansion and Fourier displacement must together fit
inside half the physical height; the exact coefficient-one sums are then
partitioned into three genuine zeta slabs. All indexing and losses remain
explicit through the original weighted family. -/
theorem IsZetaLargeValueEnergyBound.classicalTypeI_fourier_energy_transfer
    {σLV τ ρstar : ℝ} (hLV : IsZetaLargeValueEnergyBound σLV τ ρstar) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
        ∀ {ι : Type*} [Fintype ι] [LinearOrder ι]
          (A N k : ℕ) (σ V T u : ℝ) (W : ι → ℝ),
          let d := 2 * Real.pi * classicalTypeIFourierRadius A N k σ V
          let L := Nat.ceil (2 * d + 2)
          let Q := V / (4 * (N : ℝ) ^ (-σ) * classicalTypeIFourierL1 σ)
          1 < N → 0 < V → 1 < k → 0 < T →
          u + d ≤ T / 2 →
          (∀ x, T - u ≤ W x ∧ W x ≤ 2 * T + u) →
          (∀ x, V ≤
            ‖dirichletPoly N (classicalZetaLongLineCoeff A σ) (W x)‖) →
          (∀ x y : ι, x ≠ y → 1 ≤ |W x - W y|) →
          C ≤ (N : ℝ) →
          (N : ℝ) ^ (τ - δ) ≤ T / 2 →
          2 * T ≤ (N : ℝ) ^ (τ + δ) →
          (N : ℝ) ^ (σLV - δ) ≤ Q →
          (approximateAdditiveEnergyOf 1 W : ℝ) ≤
            (4 * Nat.ceil (1 + 4 * d) + 6) *
              (9 * (Fintype.card (ZMod 2 × Fin (L + 1)) : ℝ) ^ 4) *
                (729 * (C * (N : ℝ) ^ (ρstar + ε))) := by
  intro ε hε
  obtain ⟨C, hC, δ, hδ, hZeta⟩ :=
    hLV.classicalTypeI_expanded_slab_bound ε hε
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro ι _ _ A N k σ V T u W
  dsimp only
  let d := 2 * Real.pi * classicalTypeIFourierRadius A N k σ V
  let L := Nat.ceil (2 * d + 2)
  let Q := V / (4 * (N : ℝ) ^ (-σ) * classicalTypeIFourierL1 σ)
  intro hN hV hk hT hroom hW hlarge hsep hCN hTL hTU hQL
  have hd : 0 ≤ d :=
    mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
      (classicalTypeIFourierRadius_pos A N k σ V hV hk).le
  obtain ⟨W', hpert, label, htransfer, henergy, hlarge', hseparated⟩ :=
    exists_separated_classicalTypeI_explicitFourier_energy_classes
      A N k σ V W (by omega) hV hk hlarge hsep
  let hlocal : ∀ z : ℤ, (unitBinFinset W' z).card ≤ L := fun z =>
    unitBinFinset_perturbation_card_le_natCeil W W' d hd hsep hpert z
  let color := boundedMultiplicityColor W' L hlocal
  let Wᵢ := fun i : Fin 4 =>
    fun x : EnergyColorFiber color (label i) => W' x.1
  let B := 729 * (C * (N : ℝ) ^ (ρstar + ε))
  have hclass (i : Fin 4) :
      (approximateAdditiveEnergyOf 1 (Wᵢ i) : ℝ) ≤ B := by
    apply hZeta A N Q T (Wᵢ i) hN hT _ (hseparated i) (hlarge' i)
      hCN hTL hTU hQL
    intro x
    have hx := hW x.1
    have hp := abs_le.mp (hpert x.1)
    change T / 2 ≤ W' x.1 ∧ W' x.1 ≤ 4 * T
    constructor <;> linarith
  have hSum :
      (approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
          (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
          (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
          (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ) ≤ 4 * B := by
    linarith [hclass 0, hclass 1, hclass 2, hclass 3]
  let K : ℝ := 9 * (Fintype.card (ZMod 2 × Fin (L + 1)) : ℝ) ^ 4
  have hK : 0 ≤ K := by positivity
  have hshifted : (approximateAdditiveEnergyOf 1 W' : ℝ) ≤ K * B := by
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
    _ ≤ (4 * Nat.ceil (1 + 4 * d) + 6) * (K * B) :=
      mul_le_mul_of_nonneg_left hshifted (by positivity)
    _ = (4 * Nat.ceil (1 + 4 * d) + 6) * K * B := by ring

/-- All explicit perturbation, separation, and zeta-slab coloring losses in
the preceding finite transfer, as a function of the Fourier displacement. -/
def classicalTypeIFourierEnergyLoss (d : ℝ) : ℝ :=
  (4 * Nat.ceil (1 + 4 * d) + 6) *
    (9 * (Fintype.card (ZMod 2 × Fin (Nat.ceil (2 * d + 2) + 1)) : ℝ) ^ 4) * 729

/-- The complete finite loss has degree at most five in the displacement. -/
theorem classicalTypeIFourierEnergyLoss_le (d : ℝ) (hd : 0 ≤ d) :
    classicalTypeIFourierEnergyLoss d ≤ 429981696 * (1 + d) ^ 5 := by
  have hfirst : (4 * Nat.ceil (1 + 4 * d) + 6 : ℝ) ≤ 16 * (1 + d) := by
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ 1 + 4 * d by linarith)
    linarith
  have hcolors :
      (Fintype.card (ZMod 2 × Fin (Nat.ceil (2 * d + 2) + 1)) : ℝ) ≤
        8 * (1 + d) := by
    simp only [Fintype.card_prod, ZMod.card, Fintype.card_fin, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ 2 * d + 2 by linarith)
    linarith
  unfold classicalTypeIFourierEnergyLoss
  calc
    (4 * Nat.ceil (1 + 4 * d) + 6) *
        (9 * (Fintype.card (ZMod 2 × Fin (Nat.ceil (2 * d + 2) + 1)) : ℝ) ^ 4) *
        729 ≤
      (16 * (1 + d)) * (9 * (8 * (1 + d)) ^ 4) * 729 := by
        gcongr
    _ = 429981696 * (1 + d) ^ 5 := by ring

/-- A sufficiently small subpower displacement makes the complete finite
energy loss smaller than any prescribed height power. -/
theorem eventually_classicalTypeIFourierEnergyLoss_le_rpow
    (θ η : ℝ) (hθ : 0 ≤ θ) (hgap : 5 * θ < η) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ d : ℝ, 0 ≤ d →
      d ≤ 2 * Real.pi * T ^ θ →
      classicalTypeIFourierEnergyLoss d ≤ T ^ η := by
  let K : ℝ := 429981696 * (1 + 2 * Real.pi) ^ 5
  have hconst : ∀ᶠ T : ℝ in Filter.atTop, K ≤ T ^ (η - 5 * θ) :=
    (tendsto_rpow_atTop (by linarith : 0 < η - 5 * θ)).eventually
      (Filter.eventually_ge_atTop K)
  filter_upwards [hconst, Filter.eventually_ge_atTop (1 : ℝ)] with T hconst hT
  intro d hd hdT
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hpowOne : 1 ≤ T ^ θ := Real.one_le_rpow hT hθ
  have hbase : 1 + d ≤ (1 + 2 * Real.pi) * T ^ θ := by nlinarith
  calc
    classicalTypeIFourierEnergyLoss d ≤ 429981696 * (1 + d) ^ 5 :=
      classicalTypeIFourierEnergyLoss_le d hd
    _ ≤ 429981696 * ((1 + 2 * Real.pi) * T ^ θ) ^ 5 := by gcongr
    _ = K * T ^ (5 * θ) := by
      rw [mul_pow, ← Real.rpow_natCast (T ^ θ) 5, ← Real.rpow_mul hTpos.le]
      dsimp only [K]
      rw [show θ * (5 : ℕ) = 5 * θ by push_cast; ring]
      ring
    _ ≤ T ^ (η - 5 * θ) * T ^ (5 * θ) :=
      mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hTpos.le _)
    _ = T ^ η := by rw [← Real.rpow_add hTpos]; congr 1; ring

/-- The two source ordinate expansions fit inside half the physical height
eventually, uniformly for every Fourier radius bounded by the same subpower. -/
theorem eventually_classicalTypeI_displacements_fit
    (θ : ℝ) (hθ : θ < 1) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ R : ℝ, R ≤ T ^ θ →
      T ^ θ + 2 * Real.pi * R ≤ T / 2 := by
  have hconst : ∀ᶠ T : ℝ in Filter.atTop,
      2 * (1 + 2 * Real.pi) ≤ T ^ (1 - θ) :=
    (tendsto_rpow_atTop (by linarith : 0 < 1 - θ)).eventually
      (Filter.eventually_ge_atTop _)
  filter_upwards [hconst, Filter.eventually_gt_atTop (0 : ℝ)] with T hc hT
  intro R hR
  have hmult := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hT.le θ)
  have hid : T ^ (1 - θ) * T ^ θ = T := by
    rw [← Real.rpow_add hT, sub_add_cancel, Real.rpow_one]
  rw [hid] at hmult
  have hR' := mul_le_mul_of_nonneg_left hR
    (show 0 ≤ 2 * Real.pi by positivity)
  nlinarith

/-- The sharp source Type-I family satisfies the zeta energy estimate with
any prescribed scale epsilon loss. The Fourier order, source displacement,
threshold normalization, three height slabs, and all coloring factors are
chosen and discharged here. The remaining physical inputs are the source
lower scale bound and the height exponent window supplied by scale selection. -/
theorem IsZetaLargeValueEnergyBound.classicalTypeI_source_energy_bound
    {σ τ ρstar : ℝ} (hLV : IsZetaLargeValueEnergyBound σ τ ρstar)
    (hσ : 0 ≤ σ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
        ∀ a D : ℝ, 0 < a → 0 ≤ D + 1 → D ≤ a * δ / 2 →
          ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
            ∀ᶠ T : ℝ in Filter.atTop,
              ∀ {ι : Type*} [Fintype ι] [LinearOrder ι]
                (N : ℕ) (W : ι → ℝ),
                T ^ a ≤ (N : ℝ) →
                (N : ℝ) ^ (τ - δ) ≤ T / 2 →
                2 * T ≤ (N : ℝ) ^ (τ + δ) →
                (∀ x, T - T ^ θ ≤ W x ∧ W x ≤ 2 * T + T ^ θ) →
                (∀ x,
                  ((3 / 4 : ℝ) * (T ^ (-D) / 2)) /
                      Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ ≤
                    ‖dirichletPoly N
                      (classicalZetaLongLineCoeff ⌊sharpZetaCutoff T⌋₊ σ) (W x)‖) →
                (∀ x y : ι, x ≠ y → 1 ≤ |W x - W y|) →
                (approximateAdditiveEnergyOf 1 W : ℝ) ≤
                  C * (N : ℝ) ^ (ρstar + ε) := by
  intro ε hε
  obtain ⟨C, hC, δ, hδ, hfinite⟩ :=
    hLV.classicalTypeI_fourier_energy_transfer (ε / 2) (by linarith)
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro a D ha hD hDloss
  let θ : ℝ := min (1 / 4) (a * ε / 40)
  have hθ : 0 < θ := lt_min (by norm_num) (by positivity)
  have hθone : θ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hgap : 5 * θ < a * ε / 2 := by
    have hsmall : θ ≤ a * ε / 40 := min_le_right _ _
    have hae : 0 < a * ε := mul_pos ha hε
    linarith
  obtain ⟨k, hk, hradius⟩ :=
    exists_order_eventually_classicalTypeIFourierRadius_sharpCutoff_le_rpow
      σ D θ hσ hD hθ
  have hthreshold := eventually_classicalTypeI_normalized_sourceThreshold_lower
    σ a δ D ha hδ hDloss
  have hroom := eventually_classicalTypeI_displacements_fit θ hθone
  have hloss := eventually_classicalTypeIFourierEnergyLoss_le_rpow
    θ (a * ε / 2) hθ.le hgap
  have hscaleLarge : ∀ᶠ T : ℝ in Filter.atTop, max C 2 ≤ T ^ a :=
    (tendsto_rpow_atTop ha).eventually (Filter.eventually_ge_atTop (max C 2))
  refine ⟨θ, hθ, hθone, ?_⟩
  filter_upwards [hradius, hthreshold, hroom, hloss, hscaleLarge,
    Filter.eventually_ge_atTop (8 : ℝ)] with
      T hradius hthreshold hroom hloss hscaleLarge hT
  intro ι _ _ N W hscale hTL hTU hW hlarge hsep
  have hTpos : 0 < T := by linarith
  have hCN : C ≤ (N : ℝ) := (le_max_left C 2).trans (hscaleLarge.trans hscale)
  have hNtwo : (2 : ℝ) ≤ N := (le_max_right C 2).trans (hscaleLarge.trans hscale)
  have hN : 1 < N := by exact_mod_cast (show (1 : ℝ) < N by linarith)
  have hNpos : (0 : ℝ) < N := by linarith
  have hCnonneg : 0 ≤ C := zero_le_one.trans hC
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
    have he : approximateAdditiveEnergyOf 1 W = 0 := by
      simp [approximateAdditiveEnergyOf]
    rw [he, Nat.cast_zero]
    positivity
  | inr hnonempty =>
    let A := ⌊sharpZetaCutoff T⌋₊
    let V := ((3 / 4 : ℝ) * (T ^ (-D) / 2)) / Nat.clog 2 A
    let R := classicalTypeIFourierRadius A N k σ V
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
    have hd : 0 ≤ d := by
      exact mul_nonneg (show 0 ≤ 2 * Real.pi by positivity)
        (classicalTypeIFourierRadius_pos A N k σ V hV hk).le
    have hdBound : d ≤ 2 * Real.pi * T ^ θ :=
      mul_le_mul_of_nonneg_left hR (by positivity)
    have henergy := hfinite A N k σ V T (T ^ θ) W
      hN hV hk hTpos (hroom R hR) hW hlarge hsep hCN hTL hTU
        (hthreshold N hscale)
    have henergy' : (approximateAdditiveEnergyOf 1 W : ℝ) ≤
        classicalTypeIFourierEnergyLoss d *
          (C * (N : ℝ) ^ (ρstar + ε / 2)) := by
      simpa only [classicalTypeIFourierEnergyLoss, mul_assoc, d, R] using henergy
    have hlossN : classicalTypeIFourierEnergyLoss d ≤ (N : ℝ) ^ (ε / 2) := by
      apply (hloss d hd hdBound).trans
      calc
        T ^ (a * ε / 2) = (T ^ a) ^ (ε / 2) := by
          rw [← Real.rpow_mul hTpos.le]
          congr 1
          ring
        _ ≤ (N : ℝ) ^ (ε / 2) :=
          Real.rpow_le_rpow (Real.rpow_nonneg hTpos.le _) hscale (by linarith)
    calc
      (approximateAdditiveEnergyOf 1 W : ℝ) ≤
          classicalTypeIFourierEnergyLoss d *
            (C * (N : ℝ) ^ (ρstar + ε / 2)) := henergy'
      _ ≤ (N : ℝ) ^ (ε / 2) * (C * (N : ℝ) ^ (ρstar + ε / 2)) :=
        mul_le_mul_of_nonneg_right hlossN (by positivity)
      _ = C * ((N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ρstar + ε / 2)) := by ring
      _ = C * (N : ℝ) ^ (ρstar + ε) := by
        rw [← Real.rpow_add hNpos]
        congr 2
        ring

/-- Every actual dyadic block above the source floor cutoff has a uniform
positive-power lower scale bound. The estimate includes the floor loss. -/
theorem eventually_classicalTypeI_sourceScale_lower (a : ℝ) (ha : 0 < a) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ r : ℕ,
      T ^ (a / 2) ≤ ((2 ^ r * ⌊T ^ a⌋₊ : ℕ) : ℝ) := by
  obtain ⟨T₀, hT₀, hfloor⟩ := eventually_half_rpow_le_natFloor a ha
  have hpow : ∀ᶠ T : ℝ in Filter.atTop, 2 ≤ T ^ (a / 2) :=
    (tendsto_rpow_atTop (by linarith : 0 < a / 2)).eventually
      (Filter.eventually_ge_atTop 2)
  filter_upwards [Filter.eventually_ge_atTop T₀, hpow] with T hT hpow
  intro r
  have hTpos : 0 < T := by linarith
  have hid : T ^ a = T ^ (a / 2) * T ^ (a / 2) := by
    rw [← Real.rpow_add hTpos]
    congr 1
    ring
  calc
    T ^ (a / 2) ≤ T ^ a / 2 := by rw [hid]; nlinarith
    _ ≤ (⌊T ^ a⌋₊ : ℝ) := (hfloor T hT).1
    _ ≤ ((2 ^ r * ⌊T ^ a⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_mul_of_pos_left ⌊T ^ a⌋₊ (pow_pos (by omega) r)

/-- Consumer for an actual classical Type-I branch/scale fiber of the
multiplicity-preserving slab extraction. Its scale is the selected dyadic
block over the source floor cutoff. Largeness and separation are recovered
from the genuine branch label and refined color, rather than supplied anew
as hypotheses on a detached polynomial family. -/
theorem IsZetaLargeValueEnergyBound.classicalTypeI_source_class_energy_bound
    {σ τ ρstar : ℝ} (hLV : IsZetaLargeValueEnergyBound σ τ ρstar)
    (hσ : 0 ≤ σ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
        ∀ a D : ℝ, 0 < a → 0 ≤ D + 1 → D ≤ a * δ / 4 →
          ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
            ∀ᶠ T : ℝ in Filter.atTop,
              let Y := ⌊T ^ a⌋₊
              ∀ (X L : ℕ)
                (shiftedZero : ↥(zerosInRect σ 1 T (2 * T)) → ℝ)
                (baseColor : ↥(zerosInRect σ 1 T (2 * T)) →
                  ClassicalBranchScaleColor T Y)
                (hlocal : ∀ z : ℤ,
                  (unitBinFinset (fun x : ClassicalSlabZeroCopy σ T =>
                    shiftedZero x.1) z).card ≤ L)
                (label : ClassicalSeparatedBranchScaleColor T Y L)
                (r : Fin (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊)),
                label.1 = some (Sum.inl r) →
                (∀ ρ, T - T ^ θ ≤ shiftedZero ρ ∧
                  shiftedZero ρ ≤ 2 * T + T ^ θ) →
                (∀ ρ, ClassicalBranchScaleLarge σ T D Y X
                  (baseColor ρ) (shiftedZero ρ)) →
                ((2 ^ (r : ℕ) * Y : ℕ) : ℝ) ^ (τ - δ) ≤ T / 2 →
                2 * T ≤ ((2 ^ (r : ℕ) * Y : ℕ) : ℝ) ^ (τ + δ) →
                (approximateAdditiveEnergyOf 1
                    (fun x : EnergyColorFiber
                      (classicalSeparatedBranchScaleColor σ T Y
                        shiftedZero baseColor L hlocal) label =>
                      shiftedZero x.1.1) : ℝ) ≤
                  C * ((2 ^ (r : ℕ) * Y : ℕ) : ℝ) ^ (ρstar + ε) := by
  intro ε hε
  obtain ⟨C, hC, δ, hδ, hsource⟩ := hLV.classicalTypeI_source_energy_bound hσ ε hε
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro a D ha hD hDloss
  obtain ⟨θ, hθ, hθone, hbound⟩ :=
    hsource (a / 2) D (by linarith) hD (by linarith)
  refine ⟨θ, hθ, hθone, ?_⟩
  filter_upwards [hbound, eventually_classicalTypeI_sourceScale_lower a ha] with
    T hbound hscale
  dsimp only
  intro X L shiftedZero baseColor hlocal label r hlabel hinterval hlarge hTL hTU
  let Y := ⌊T ^ a⌋₊
  let N := 2 ^ (r : ℕ) * Y
  let color := classicalSeparatedBranchScaleColor σ T Y shiftedZero baseColor L hlocal
  let W := fun x : EnergyColorFiber color label => shiftedZero x.1.1
  apply hbound N W (hscale r) hTL hTU
  · intro x
    exact hinterval x.1.1
  · intro x
    have hx := hlarge x.1.1
    have hb : baseColor x.1.1 = label.1 :=
      separatedRefinementColor_base
        (fun z : ClassicalSlabZeroCopy σ T => shiftedZero z.1)
        (fun z => baseColor z.1) L hlocal x.2
    rw [hb, hlabel] at hx
    exact hx.1
  · intro x y hxy
    exact separatedRefinementColor_oneSeparated
      (fun z : ClassicalSlabZeroCopy σ T => shiftedZero z.1)
      (fun z => baseColor z.1) L hlocal label x y hxy

/-- Convergence of the physical logarithmic scale supplies precisely the
two height inequalities consumed by the three-slab zeta energy transfer,
including its factors of two. -/
theorem eventually_classicalTypeI_height_window_of_logb_tendsto
    (N : ℕ → ℕ) (T : ℕ → ℝ) (τ : ℝ)
    (hN : ∀ n, 1 < (N n : ℝ)) (hT : ∀ n, 0 < T n)
    (hNtop : Filter.Tendsto (fun n => (N n : ℝ)) Filter.atTop Filter.atTop)
    (hscale : Filter.Tendsto (fun n => Real.logb (N n : ℝ) (T n))
      Filter.atTop (nhds τ)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n in Filter.atTop,
      (N n : ℝ) ^ (τ - δ) ≤ T n / 2 ∧
        2 * T n ≤ (N n : ℝ) ^ (τ + δ) := by
  intro δ hδ
  have hlo := (tendsto_order.1 hscale).1 (τ - δ / 2) (by linarith)
  have hup := (tendsto_order.1 hscale).2 (τ + δ / 2) (by linarith)
  have htwo : ∀ᶠ n in Filter.atTop, 2 ≤ (N n : ℝ) ^ (δ / 2) :=
    ((tendsto_rpow_atTop (by linarith : 0 < δ / 2)).comp hNtop).eventually
      (Filter.eventually_ge_atTop 2)
  filter_upwards [hlo, hup, htwo] with n hlo hup htwo
  have hNpos : (0 : ℝ) < N n := zero_lt_one.trans (hN n)
  have hlower : (N n : ℝ) ^ (τ - δ / 2) ≤ T n :=
    (Real.le_logb_iff_rpow_le (hN n) (hT n)).mp hlo.le
  have hupper : T n ≤ (N n : ℝ) ^ (τ + δ / 2) :=
    (Real.logb_le_iff_le_rpow (hN n) (hT n)).mp hup.le
  constructor
  · have hprod := mul_le_mul_of_nonneg_right htwo
      (Real.rpow_nonneg hNpos.le (τ - δ))
    have hid : (N n : ℝ) ^ (δ / 2) * (N n : ℝ) ^ (τ - δ) =
        (N n : ℝ) ^ (τ - δ / 2) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring
    rw [hid] at hprod
    linarith
  · calc
      2 * T n ≤ (N n : ℝ) ^ (δ / 2) * (N n : ℝ) ^ (τ + δ / 2) :=
        mul_le_mul htwo hupper (hT n).le (Real.rpow_nonneg hNpos.le _)
      _ = (N n : ℝ) ^ (τ + δ) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring

/-- Compactness selects the source exponent from the actual physical scale
bounds. The upper cutoff `N ≤ 6T` forces the limiting exponent to be at
least one, while `T^a ≤ N` bounds it by `1/a`. The same subsequence gives
every height window needed by the zeta energy estimate. -/
theorem exists_classicalTypeI_scale_subsequence
    (a : ℝ) (ha : 0 < a) (N : ℕ → ℕ) (T : ℕ → ℝ)
    (hT : ∀ n, 1 < T n)
    (hTtop : Filter.Tendsto T Filter.atTop Filter.atTop)
    (hlower : ∀ n, (T n) ^ a ≤ (N n : ℝ))
    (hupper : ∀ n, (N n : ℝ) ≤ 6 * T n) :
    ∃ τ : ℝ, 1 ≤ τ ∧ τ ≤ 1 / a ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Filter.Tendsto (fun n => T (φ n)) Filter.atTop Filter.atTop ∧
        Filter.Tendsto (fun n => (N (φ n) : ℝ)) Filter.atTop Filter.atTop ∧
        Filter.Tendsto (fun n => Real.logb (N (φ n) : ℝ) (T (φ n)))
          Filter.atTop (nhds τ) ∧
        ∀ δ : ℝ, 0 < δ → ∀ᶠ n in Filter.atTop,
          (N (φ n) : ℝ) ^ (τ - δ) ≤ T (φ n) / 2 ∧
            2 * T (φ n) ≤ (N (φ n) : ℝ) ^ (τ + δ) := by
  have hN (n : ℕ) : 1 < (N n : ℝ) :=
    (Real.one_lt_rpow (hT n) ha).trans_le (hlower n)
  have hNtop : Filter.Tendsto (fun n => (N n : ℝ)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono hlower ((tendsto_rpow_atTop ha).comp hTtop)
  have hbox (n : ℕ) : Real.logb (N n : ℝ) (T n) ∈ Set.Icc 0 (1 / a) := by
    refine ⟨Real.logb_nonneg (hN n) (hT n).le, ?_⟩
    apply (Real.logb_le_iff_le_rpow (hN n) (zero_lt_one.trans (hT n))).mpr
    calc
      T n = ((T n) ^ a) ^ (1 / a) := by
        rw [← Real.rpow_mul (zero_lt_one.trans (hT n)).le]
        rw [mul_one_div_cancel ha.ne', Real.rpow_one]
      _ ≤ (N n : ℝ) ^ (1 / a) :=
        Real.rpow_le_rpow
          (Real.rpow_nonneg (zero_lt_one.trans (hT n)).le _) (hlower n) (by positivity)
  obtain ⟨τ, hτ, φ, hφ, hlimit⟩ := isCompact_Icc.tendsto_subseq hbox
  have hφtop : Filter.Tendsto φ Filter.atTop Filter.atTop := hφ.tendsto_atTop
  have hNsub := hNtop.comp hφtop
  have hTsub := hTtop.comp hφtop
  have hlogTop := Real.tendsto_log_atTop.comp hNsub
  have hlowerLimit :
      Filter.Tendsto (fun n => 1 - Real.log 6 / Real.log (N (φ n) : ℝ))
        Filter.atTop (nhds (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub (hlogTop.const_div_atTop (Real.log 6))
  have hτone : 1 ≤ τ := by
    apply le_of_tendsto_of_tendsto' hlowerLimit hlimit
    intro n
    have hNp : (0 : ℝ) < N (φ n) := zero_lt_one.trans (hN (φ n))
    have hTp : 0 < T (φ n) := zero_lt_one.trans (hT (φ n))
    have hlogN : 0 < Real.log (N (φ n) : ℝ) := Real.log_pos (hN (φ n))
    have hlogUpper := Real.log_le_log hNp (hupper (φ n))
    rw [Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) hTp.ne'] at hlogUpper
    change 1 - Real.log 6 / Real.log (N (φ n) : ℝ) ≤
      Real.logb (N (φ n) : ℝ) (T (φ n))
    rw [Real.logb, le_div_iff₀ hlogN]
    have hcancel := div_mul_cancel₀ (Real.log 6) hlogN.ne'
    nlinarith
  refine ⟨τ, hτone, hτ.2, φ, hφ, hTsub, hNsub, hlimit, ?_⟩
  exact eventually_classicalTypeI_height_window_of_logb_tendsto
    (fun n => N (φ n)) (fun n => T (φ n)) τ
      (fun n => hN (φ n)) (fun n => zero_lt_one.trans (hT (φ n))) hNsub hlimit

/-- A genuinely large sharp source block must start before the sharp cutoff.
Thus the source polynomial itself supplies the physical upper scale bound
used in compactness. -/
theorem classicalTypeI_source_large_scale_le_six_mul
    (N : ℕ) (σ T D t : ℝ) (hT : 8 ≤ T)
    (hlarge :
      ((3 / 4 : ℝ) * (T ^ (-D) / 2)) / Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ ≤
        ‖dirichletPoly N (classicalZetaLongLineCoeff ⌊sharpZetaCutoff T⌋₊ σ) t‖) :
    (N : ℝ) ≤ 6 * T := by
  have hTpos : 0 < T := by linarith
  have hA : 1 < ⌊sharpZetaCutoff T⌋₊ := by
    apply lt_of_lt_of_le (by omega : 1 < (2 : ℕ))
    apply Nat.le_floor
    exact (show (2 : ℝ) ≤ 4 * T by linarith).trans
      (four_mul_lt_sharpZetaCutoff T).le
  have hV : 0 <
      ((3 / 4 : ℝ) * (T ^ (-D) / 2)) / Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ := by
    have hc := Nat.clog_pos Nat.one_lt_two hA
    positivity
  have hNA := typeI_start_lt_cutoff_of_positive_large_value
    ⌊sharpZetaCutoff T⌋₊ N σ t _ hV hlarge
  calc
    (N : ℝ) ≤ (⌊sharpZetaCutoff T⌋₊ : ℝ) := by exact_mod_cast hNA.le
    _ ≤ sharpZetaCutoff T :=
      Nat.floor_le ((show 0 ≤ 4 * T by positivity).trans (four_mul_lt_sharpZetaCutoff T).le)
    _ ≤ 6 * T := sharpZetaCutoff_le_six_mul (by linarith)

/-- Source large-value witnesses select a physical exponent and all its
eventual zeta height windows. The upper scale estimate is derived from the
actual sharp polynomial, not assumed as unrelated numerical data. -/
theorem exists_classicalTypeI_source_scale_subsequence
    (σ a D : ℝ) (ha : 0 < a)
    (N : ℕ → ℕ) (T t : ℕ → ℝ)
    (hT : ∀ n, 8 ≤ T n)
    (hTtop : Filter.Tendsto T Filter.atTop Filter.atTop)
    (hlower : ∀ n, (T n) ^ a ≤ (N n : ℝ))
    (hlarge : ∀ n,
      ((3 / 4 : ℝ) * ((T n) ^ (-D) / 2)) /
          Nat.clog 2 ⌊sharpZetaCutoff (T n)⌋₊ ≤
        ‖dirichletPoly (N n)
          (classicalZetaLongLineCoeff ⌊sharpZetaCutoff (T n)⌋₊ σ) (t n)‖) :
    ∃ τ : ℝ, 1 ≤ τ ∧ τ ≤ 1 / a ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Filter.Tendsto (fun n => T (φ n)) Filter.atTop Filter.atTop ∧
        Filter.Tendsto (fun n => (N (φ n) : ℝ)) Filter.atTop Filter.atTop ∧
        Filter.Tendsto (fun n => Real.logb (N (φ n) : ℝ) (T (φ n)))
          Filter.atTop (nhds τ) ∧
        ∀ δ : ℝ, 0 < δ → ∀ᶠ n in Filter.atTop,
          (N (φ n) : ℝ) ^ (τ - δ) ≤ T (φ n) / 2 ∧
            2 * T (φ n) ≤ (N (φ n) : ℝ) ^ (τ + δ) :=
  exists_classicalTypeI_scale_subsequence a ha N T
    (fun n => by linarith [hT n]) hTtop hlower
    (fun n => classicalTypeI_source_large_scale_le_six_mul
      (N n) σ (T n) D (t n) (hT n) (hlarge n))

end TaoTrudgianYang2025
