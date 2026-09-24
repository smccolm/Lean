import TaoTrudgianYang2025.ClassicalBottomSourceThreshold
import TaoTrudgianYang2025.ClassicalPatternCardinality
import TaoTrudgianYang2025.LargeValueUniformity

/-!
# General large-value transfer on a linked physical scale interval

A genuine separated Dirichlet family is packaged at its expanded source
height. The scale window is linked to N and T, with constants chosen before
the family and height-displacement exponent. Cardinality and energy are
preserved exactly by the packaging.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem classicalGeneral_uniform_physical_cardinality_bound
    (σ B a b : ℝ) (hB : 0 ≤ B) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a)
    (hLV : ∀ τ ∈ Set.Icc (1/a) (1/b), IsLargeValueBound σ τ (B*τ)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
        ∀ θ : ℝ, θ ≤ 1 →
          ∀ᶠ T : ℝ in Filter.atTop,
            ∀ {ι : Type*} [Fintype ι] (N : ℕ) (V : ℝ)
              (coeff : ℕ → ℂ) (W : ι → ℝ),
              T^b ≤ (N : ℝ) → (N : ℝ) ≤ T^a →
              (N : ℝ)^(σ-δ) ≤ V →
              (∀ n ∈ dyadicInterval N, ‖coeff n‖ ≤ 1) →
              (∀ x, T-T^θ ≤ W x ∧ W x ≤ 2*T+T^θ) →
              (∀ x y : ι, x ≠ y → 1 ≤ |W x-W y|) →
              (∀ x, V ≤ ‖dirichletPoly N coeff (W x)‖) →
              (Fintype.card ι : ℝ) ≤ C*T^(B+ε) := by
  intro ε hε
  obtain ⟨C,hC,δ,hδ,hBound⟩ :=
    largeValueBound_uniform_near_logScale_interval σ B (1/a) (1/b)
      hB (one_div_le_one_div_of_le hb hba) hLV (ε/a) (div_pos hε ha)
  let Cfinal := max 1 (C*(3 : ℝ)^B)
  refine ⟨Cfinal,le_max_left _ _,δ,hδ,?_⟩
  intro θ hθ
  filter_upwards [eventually_classicalTypeII_logScale_near_interval a b δ ha hb hba hδ,
    (tendsto_rpow_atTop hb).eventually (Filter.eventually_ge_atTop C),
    Filter.eventually_ge_atTop (2 : ℝ)] with T hNear hCEvent hT
  intro ι _ N V coeff W hNL hNU hThreshold hCoeff hW hSep hLarge
  classical
  have hTPos : 0 < T := by linarith
  have hTOne : 1 ≤ T := by linarith
  have hNReal : 1 < (N : ℝ) :=
    (Real.one_lt_rpow (by linarith : 1 < T) hb).trans_le hNL
  have hN : 1 < N := by exact_mod_cast hNReal
  have hNPos : (0 : ℝ) < N := zero_lt_one.trans hNReal
  have hV : 0 < V := (Real.rpow_pos_of_pos hNPos _).trans_le hThreshold
  have hHeight : T ≤ (2*T+T^θ)-(T-T^θ) ∧ (2*T+T^θ)-(T-T^θ) ≤ 3*T := by
    have hp : T^θ ≤ T := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hTOne hθ
    constructor <;> linarith [Real.rpow_pos_of_pos hTPos θ]
  have hab : T-T^θ < 2*T+T^θ := by linarith [hHeight.1]
  let P := indexedDirichletLargeValuePattern N V (T-T^θ) (2*T+T^θ)
    coeff W hN hV hab hCoeff hW hSep hLarge
  have hPC : C ≤ P.N := hCEvent.trans hNL
  have hPNear : ∃ τ ∈ Set.Icc (1/a) (1/b), |Real.logb P.N P.T-τ| ≤ δ :=
    hNear N P.T hNL hNU hHeight.1 hHeight.2
  have hp : (P.ordinates.card : ℝ) ≤ C*P.T^B*(N : ℝ)^(ε/a) :=
    hBound P hPC hPNear hThreshold
  have hIdentity := indexedDirichletLargeValuePattern_card N V (T-T^θ) (2*T+T^θ)
    coeff W hN hV hab hCoeff hW hSep hLarge
  change P.ordinates.card = Fintype.card ι at hIdentity
  rw [hIdentity] at hp
  have hCNonneg : 0 ≤ C := zero_le_one.trans hC
  calc
    (Fintype.card ι : ℝ) ≤ C*P.T^B*(N : ℝ)^(ε/a) := hp
    _ ≤ C*(3*T)^B*(T^a)^(ε/a) :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow P.T_pos.le hHeight.2 hB) hCNonneg)
        (Real.rpow_le_rpow hNPos.le hNU (div_pos hε ha).le)
        (Real.rpow_nonneg hNPos.le _) (by positivity)
    _ = (C*(3 : ℝ)^B)*T^(B+ε) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hTPos.le,
        ← Real.rpow_mul hTPos.le,mul_div_cancel₀ ε ha.ne',Real.rpow_add hTPos]
      ring
    _ ≤ Cfinal*T^(B+ε) := mul_le_mul_of_nonneg_right
      (le_max_right _ _) (Real.rpow_nonneg hTPos.le _)

theorem classicalGeneral_uniform_physical_energy_bound
    (σ B a b : ℝ) (hB : 0 ≤ B) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a)
    (hLV : ∀ τ ∈ Set.Icc (1/a) (1/b), IsLargeValueEnergyBound σ τ (B*τ)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
        ∀ θ : ℝ, θ ≤ 1 →
          ∀ᶠ T : ℝ in Filter.atTop,
            ∀ {ι : Type*} [Fintype ι] (N : ℕ) (V : ℝ)
              (coeff : ℕ → ℂ) (W : ι → ℝ),
              T^b ≤ (N : ℝ) → (N : ℝ) ≤ T^a →
              (N : ℝ)^(σ-δ) ≤ V →
              (∀ n ∈ dyadicInterval N, ‖coeff n‖ ≤ 1) →
              (∀ x, T-T^θ ≤ W x ∧ W x ≤ 2*T+T^θ) →
              (∀ x y : ι, x ≠ y → 1 ≤ |W x-W y|) →
              (∀ x, V ≤ ‖dirichletPoly N coeff (W x)‖) →
              (approximateAdditiveEnergyOf 1 W : ℝ) ≤ C*T^(B+ε) := by
  intro ε hε
  obtain ⟨C,hC,δ,hδ,hBound⟩ :=
    largeValueEnergyBound_uniform_near_logScale_interval σ B (1/a) (1/b)
      hB (one_div_le_one_div_of_le hb hba) hLV (ε/a) (div_pos hε ha)
  let Cfinal := max 1 (C*(3 : ℝ)^B)
  refine ⟨Cfinal,le_max_left _ _,δ,hδ,?_⟩
  intro θ hθ
  filter_upwards [eventually_classicalTypeII_logScale_near_interval a b δ ha hb hba hδ,
    (tendsto_rpow_atTop hb).eventually (Filter.eventually_ge_atTop C),
    Filter.eventually_ge_atTop (2 : ℝ)] with T hNear hCEvent hT
  intro ι _ N V coeff W hNL hNU hThreshold hCoeff hW hSep hLarge
  classical
  have hTPos : 0 < T := by linarith
  have hTOne : 1 ≤ T := by linarith
  have hNReal : 1 < (N : ℝ) :=
    (Real.one_lt_rpow (by linarith : 1 < T) hb).trans_le hNL
  have hN : 1 < N := by exact_mod_cast hNReal
  have hNPos : (0 : ℝ) < N := zero_lt_one.trans hNReal
  have hV : 0 < V := (Real.rpow_pos_of_pos hNPos _).trans_le hThreshold
  have hHeight : T ≤ (2*T+T^θ)-(T-T^θ) ∧ (2*T+T^θ)-(T-T^θ) ≤ 3*T := by
    have hp : T^θ ≤ T := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hTOne hθ
    constructor <;> linarith [Real.rpow_pos_of_pos hTPos θ]
  have hab : T-T^θ < 2*T+T^θ := by linarith [hHeight.1]
  let P := indexedDirichletLargeValuePattern N V (T-T^θ) (2*T+T^θ)
    coeff W hN hV hab hCoeff hW hSep hLarge
  have hPC : C ≤ P.N := hCEvent.trans hNL
  have hPNear : ∃ τ ∈ Set.Icc (1/a) (1/b), |Real.logb P.N P.T-τ| ≤ δ :=
    hNear N P.T hNL hNU hHeight.1 hHeight.2
  have hp : (finsetAdditiveEnergy P.ordinates : ℝ) ≤ C*P.T^B*(N : ℝ)^(ε/a) :=
    hBound P hPC hPNear hThreshold
  have hIdentity := indexedDirichletLargeValuePattern_energy_eq N V (T-T^θ) (2*T+T^θ)
    coeff W hN hV hab hCoeff hW hSep hLarge
  change finsetAdditiveEnergy P.ordinates = approximateAdditiveEnergyOf 1 W at hIdentity
  rw [hIdentity] at hp
  have hCNonneg : 0 ≤ C := zero_le_one.trans hC
  calc
    (approximateAdditiveEnergyOf 1 W : ℝ) ≤ C*P.T^B*(N : ℝ)^(ε/a) := hp
    _ ≤ C*(3*T)^B*(T^a)^(ε/a) :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow P.T_pos.le hHeight.2 hB) hCNonneg)
        (Real.rpow_le_rpow hNPos.le hNU (div_pos hε ha).le)
        (Real.rpow_nonneg hNPos.le _) (by positivity)
    _ = (C*(3 : ℝ)^B)*T^(B+ε) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hTPos.le,
        ← Real.rpow_mul hTPos.le,mul_div_cancel₀ ε ha.ne',Real.rpow_add hTPos]
      ring
    _ ≤ Cfinal*T^(B+ε) := mul_le_mul_of_nonneg_right
      (le_max_right _ _) (Real.rpow_nonneg hTPos.le _)

end TaoTrudgianYang2025
