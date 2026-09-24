import TaoTrudgianYang2025.ClassicalReflectedFourier

/-!
# Fourier deweighting of the actual reflected source factory

This theorem unpacks the source reflection output and applies the literal
coefficient-one extraction to that same selected block and finite family.
All physical scales, source thresholds, displacement radii, cardinality
losses and the retained energy displacement estimate remain visible.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem eventually_interior_source_positive_reflected_fourier_data
    {sigma d u : ℝ} (hsigma : 1 / 2 < sigma)
    (hsigmaUpper : sigma < 1) (hd : 0 < d) (hdOne : d ≤ 1)
    (hdGap : d ≤ (sigma - 1 / 2) / 1000)
    (hu : 0 ≤ u) (huD : u ≤ d) :
    ∃ Clog : ℝ, 0 < Clog ∧
      let CK := 32 * 2 ^ sigma +
        (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
          4 ^ (sigma + 1 / 2)
      let Cref := mediumReflectedThresholdConstant Clog CK
      let g := (sigma - 1 / 2) / 2
      let Uscale := 2 / g
      1 ≤ Cref ∧ 0 < g ∧ 0 < Uscale ∧
      ∃ T₀ : ℝ, 8 ≤ T₀ ∧
        ∀ {T tau : ℝ} {Y A r : ℕ} (W : Finset ℝ), T₀ ≤ T →
          A = ⌊sharpZetaCutoff T⌋₊ → 0 < Y → 2 ≤ r →
          ((Y + 1 : ℕ) : ℝ) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2) →
          2 * (2 ^ r * Y) ≤ A →
          tau = typeILogarithmicScale T (2 ^ r * Y) →
          1 < tau → tau < 2 →
          W.Nonempty → IsSeparated 1 W →
          (∀ t ∈ W, T - T ^ d ≤ t ∧ t ≤ 2 * T + T ^ d) →
          (∀ t ∈ W,
            ((3 / 4) * (T ^ (-u) / 2)) /
                (Nat.clog 2 A + 1 : ℕ) ≤
              ‖typeISourceSmoothBlock Y A r sigma t‖) →
          let Q := 2 ^ r * Y
          let M := mediumTypeIDualCutoff T d Q
          let V := ((3 / 4) * (T ^ (-u) / 2)) /
            (Nat.clog 2 A + 1 : ℕ)
          let R := (Real.pi * V) /
            (8 * (Q : ℝ) * mediumTypeIStationaryKernel sigma T Q *
              (typeIDyadicCutoffMellinL1 + 1))
          let S := R / (2 * (M : ℝ) ^ sigma)
          let L := S / Nat.clog 2 M
          ∃ j ∈ Finset.range (Nat.clog 2 M), ∃ U : Finset ℝ,
              IsSeparated 1 U ∧
              (∀ v ∈ U, T / 2 ≤ v ∧ v ≤ 5 * T / 2) ∧
              W.card ≤ 2 * (2 * (2 * ⌈T ^ d⌉₊ + 1)) *
                (Nat.clog 2 M) * U.card ∧
              (∀ n ∈ dyadicInterval (2 ^ j),
                ‖normalizedTypeIReflectedCoeff sigma M n‖ ≤ 1) ∧
              (∀ v ∈ U, L ≤ ‖dirichletPoly (2 ^ j)
                (normalizedTypeIReflectedCoeff sigma M) v‖) ∧
              1 < 2 ^ j ∧ 2 ^ j < M ∧
              1 / (1 / 2 + d) ≤ typeILogarithmicScale T (2 ^ j) ∧
              typeILogarithmicScale T (2 ^ j) ≤ Uscale ∧
              T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - d) /
                  Cref ≤ L ∧
              T ^ g / Cref ≤ L ∧
              ∀ k : ℕ, 1 < k →
                let sourceV := (M : ℝ) ^ sigma * L
                let radius := classicalTypeIFourierRadius M (2 ^ j) k (-sigma) sourceV
                ∃ W' : {v : ℝ // v ∈ U} → ℝ,
                  (∀ x, |W' x - x.1| ≤ 2 * Real.pi * radius) ∧
                  (∀ x,
                    sourceV /
                        (4 * ((2 ^ j : ℕ) : ℝ) ^ sigma * classicalTypeIFourierL1 (-sigma)) ≤
                      ‖∑ n ∈ Finset.Ioc (2 ^ j) (min (2 * 2 ^ j) M),
                        dirichletPhase n (W' x)‖) ∧
                  approximateAdditiveEnergyOf 1 (fun x : {v : ℝ // v ∈ U} => x.1) ≤
                    (4 * Nat.ceil (1 + 4 * (2 * Real.pi * radius)) + 6) *
                      approximateAdditiveEnergyOf 1 W' := by
  classical
  obtain ⟨Clog, hClog, hCref, hg, hUscale, T₀, hT₀, hdata⟩ :=
    eventually_interior_source_positive_reflected_data hsigma hsigmaUpper
      hd hdOne hdGap hu huD
  refine ⟨Clog, hClog, hCref, hg, hUscale, T₀, hT₀, ?_⟩
  intro T tau Y A r W hT hA hY hr hLower hUpper hTau htauOne htauTwo
    hW hSep hRange hLarge
  dsimp only
  obtain ⟨j, hj, U, hSepU, hRangeU, hCardU, hCoeff, hLargeU,
    hN, hNM, hScaleL, hScaleU, hLexp, hLlower⟩ :=
      hdata W hT hA hY hr hLower hUpper hTau htauOne htauTwo
        hW hSep hRange hLarge
  refine ⟨j, hj, U, hSepU, hRangeU, hCardU, hCoeff, hLargeU,
    hN, hNM, hScaleL, hScaleU, hLexp, hLlower, ?_⟩
  intro k hk
  dsimp only
  let Q := 2 ^ r * Y
  let M := mediumTypeIDualCutoff T d Q
  let V : ℝ := ((3 / 4) * (T ^ (-u) / 2)) / (Nat.clog 2 A + 1 : ℕ)
  let R := (Real.pi * V) /
    (8 * (Q : ℝ) * mediumTypeIStationaryKernel sigma T Q *
      (typeIDyadicCutoffMellinL1 + 1))
  let L := (R / (2 * (M : ℝ) ^ sigma)) / Nat.clog 2 M
  have hM : 0 < M := (Nat.zero_lt_one.trans hN).trans hNM
  have hTpos : 0 < T := by linarith [hT₀]
  have hL : 0 < L :=
    (div_pos (Real.rpow_pos_of_pos hTpos _) (zero_lt_one.trans_le hCref)).trans_le hLlower
  exact exists_classicalReflected_explicitBoundedOrdinate_family
    M (2 ^ j) k sigma L (fun x : {v : ℝ // v ∈ U} => x.1)
      hM (Nat.zero_lt_one.trans hN) hL hk (fun x => hLargeU x.1 x.2)

end TaoTrudgianYang2025
