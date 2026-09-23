import TaoTrudgianYang2025.ClassicalTypeICardinalityUniformity

/-!
# Uniform physical Type-I cardinality bound

The actual sharp source polynomial supplies its own upper scale bound.
Fourier order, normalized threshold and all separation losses are discharged
before the source family is selected.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem classicalTypeI_uniform_source_cardinality_bound
    (σ B a : ℝ) (hB : 0 ≤ B) (ha : 0 < a) (haone : a ≤ 1)
    (hLV : ∀ τ ∈ Set.Icc (1 : ℝ) (1 / a),
      IsZetaLargeValueBound σ τ (B * τ)) :
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
                (Fintype.card ι : ℝ) ≤ C * T ^ (B + ε) := by
  intro ε hε
  obtain ⟨C, hC, δ, hδ, hfinite⟩ :=
    classicalTypeI_uniform_fourier_cardinality_transfer σ B a hB ha haone hLV
      (ε / 2) (by linarith)
  let Cfinal : ℝ := max 1 (C * (2 : ℝ) ^ B * (6 : ℝ) ^ (ε / 2))
  refine ⟨Cfinal, le_max_left _ _, δ, hδ, ?_⟩
  intro s D hs hsσ hD hDloss
  let θ : ℝ := min (1 / 4) (ε / 40)
  have hθ : 0 < θ := lt_min (by norm_num) (by positivity)
  have hθone : θ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hgap : θ < ε / 2 := by
    have hsmall : θ ≤ ε / 40 := min_le_right _ _
    linarith
  obtain ⟨k, hk, hradius⟩ :=
    exists_order_eventually_classicalTypeIFourierRadius_sharpCutoff_le_rpow
      s D θ hs hD hθ
  have hthreshold := eventually_classicalTypeI_normalized_sourceThreshold_lower
    s a (δ / 2) D ha (by linarith) (by linarith)
  have hroom := eventually_classicalTypeI_displacements_fit θ hθone
  have hloss := eventually_classicalTypeIFourierCardinalityLoss_le_rpow
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
    rw [Fintype.card_of_isEmpty, Nat.cast_zero]
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
    have hcard := hfinite A N k s V (T ^ θ) W
      hN hV hk hTpos hscale hNU (hroom R hR) hW hlarge hsep hQL
    calc
      (Fintype.card ι : ℝ) ≤
          classicalTypeIFourierCardinalityLoss d *
            (C * (2 * T) ^ B * (N : ℝ) ^ (ε / 2)) := hcard
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


end TaoTrudgianYang2025
