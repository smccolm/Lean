import TaoTrudgianYang2025.AtkinsonPrintedSource

/-! Retained focused production audit and exact source-contract regressions.
The development proofs are installed in AtkinsonPrintedSource.lean. -/

open scoped NNReal FourierTransform
open TaoTrudgianYang2025 RiemannZeta.GuthMaynard

#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.abs_saddleRoot_sub_le
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.sqrt_succ_sub_le
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.abs_saddleRoot_sqrt_succ_sub_le
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.abs_saddleRoot_neg_sqrt_succ_sub_le
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.zetaDivisorBandCutoff_width_ratio
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.exists_intervalC2Bound_cutoff_width_ratio
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.exists_norm_saddleCutoff_increment_le
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.exists_norm_saddleCutoff_source_increment_le
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.exists_norm_saddleMellin_increment_le
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.exists_norm_saddleResidual_source_increment_le
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.abs_arsinh_sub_le
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.arsinh_sq_sub_le
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.saddleFrequency_sq_succ_sub_le
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.exp_neg_sub_le
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.norm_saddleGaussian_increment_le
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.norm_saddleGaussian_fourWidth_le
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.norm_saddleGaussian_fourWidth_increment_le
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.abs_rpow_succ_sub_le
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.norm_fourthRootCoefficient_increment_le
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.exists_norm_mainWeights_fourWidth_increment_le
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.floor_step_ae
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.integral_floor_step_unit
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.integral_floor_step_nat
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.norm_sum_mul_le_endpoint_integral
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.printedAtkinsonPhase_eq
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.sum_Ioc_nat_eq_range
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.norm_printedAtkinsonPrefix
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.exists_mainWeights_fourWidth_block_bounds
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.exists_stationary_printed_block_bound
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.sum_divisorCard_le_log
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.sum_mul_le_of_prefix_le
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.sum_shift_quarter_rpow_le
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.sum_Ioc_real_eq_range
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.sum_divisorCard_quarter_le_log
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.sum_divisorCard_quarter_le_three
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.exists_stationaryTerm_norm_le_divisor
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.exists_stationarySmallPrefix_le_log
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.sum_Ioc_pow_two_dyadic
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.pow_clog_two_le_double
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.ceil_support_dyadic_le_cutoff
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.stationaryTerm_eq_zero_of_support
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.stationarySum_eq_dyadic_support
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.stationarySupport_dyadic_le_cutoff
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.printedAtkinsonBlockBound_nonneg
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.exists_stationarySum_le_printed_dyadic
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.pow_clog_ceil_bounds
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.sum_Ioc_pow_two_split
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.exists_stationarySum_le_largePrinted_dyadic
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.norm_printedPrefix_le_square
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.integral_printedPrefix_eq_sum
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.printedBlockBound_le_damped_square
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.printedCutoff_damping_lower
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.exists_logPower_exponential_tail
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.sum_printedBlocks_tail_le
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.mem_printedAtkinsonDyadicIndices
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.exists_stationarySum_le_exactPrinted
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.eventually_printedAtkinson_geometry
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.exists_zetaSquareLocalMean_le_exactPrinted
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.printedBlockBound_eq_source
#print axioms TaoTrudgianYang2025.AtkinsonPrintedSource.exists_zetaSquareLocalMean_le_printedAtkinson

-- EPZAE-21: literal Ivić source-form conventions and full-width consumer.
namespace AtkinsonPrintedSourceRegression

open MeasureTheory Set TaoTrudgianYang2025.AtkinsonPrintedSource

example (T : ℝ) (n : ℕ) :
    printedAtkinsonPhase T n = atkinsonSourcePhase T n+Real.pi/4 :=
  printedAtkinsonPhase_eq T n

example (T : ℝ) (K : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ‖printedAtkinsonPrefix T K x‖ =
      ‖∑ i ∈ Finset.range ⌊x⌋₊, atkinsonPositivePhaseTerm T (K+1+i)‖ :=
  norm_printedAtkinsonPrefix T K hx

example (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, (n.divisors.card:ℝ)*(n:ℝ)^(-(1/4:ℝ))) ≤
      3*(N:ℝ)^(3/4:ℝ)*(1+Real.log N) :=
  sum_divisorCard_quarter_le_three N

example :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 40000 ≤ T → 0 < G → 16*G^2 ≤ T →
      1 ≤ L → 1200*L ≤ 4*G → ∀ K : ℕ, 0 < K → 2*K ≤ atkinsonSourceCutoff T (4*G) L →
      ‖∑ n ∈ Finset.Ioc K (2*K), atkinsonStationaryLeadingTerm T (4*G) L n‖ ≤
        C*printedBlockScale T G K*(‖printedAtkinsonPrefix T K (K:ℝ)‖+
          (1/(K:ℝ))*(∫ x in (0:ℝ)..(K:ℝ), ‖printedAtkinsonPrefix T K x‖)) :=
  exists_stationary_printed_block_bound

example {x : ℝ} (hx : 1 ≤ x) :
    x ≤ ((2^Nat.clog 2 ⌈x⌉₊:ℕ):ℝ) ∧ ((2^Nat.clog 2 ⌈x⌉₊:ℕ):ℝ) ≤ 2*x :=
  pow_clog_ceil_bounds hx

example {T G η : ℝ}
    (hN : 0 ≤ printedAtkinsonCutoff T G η) (j : ℕ) :
    j ∈ printedAtkinsonDyadicIndices T G η ↔
      T^(1/3:ℝ) ≤ ((2^j:ℕ):ℝ) ∧ ((2^j:ℕ):ℝ) ≤ printedAtkinsonCutoff T G η :=
  mem_printedAtkinsonDyadicIndices hN j

example {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G L : ℝ,
      T₀ ≤ T → 1 ≤ Real.log T → 0 < G → 16*G^2 ≤ T → 1 ≤ L → 1200*L ≤ 4*G →
      printedAtkinsonB T G η < T/(2*Real.pi) →
      ‖atkinsonStationaryLeadingSum T (4*G) L‖ ≤ C*(G*Real.log T+
        ∑ j ∈ printedAtkinsonDyadicIndices T G η, printedAtkinsonBlockBound T G (2^j)) :=
  exists_stationarySum_le_exactPrinted hη

example {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) →
      (∫ t in T-G..T+G, zetaMomentCriticalNorm t^2) ≤ C*(G*Real.log T+
        G*∑ j ∈ printedAtkinsonDyadicIndices T G η,
          (T*((2^j:ℕ):ℝ))^(-(1/4:ℝ))*
            (‖printedAtkinsonPrefix T (2^j) ((2^j:ℕ):ℝ)‖+
              (((2^j:ℕ):ℝ))⁻¹*(∫ x in (0:ℝ)..((2^j:ℕ):ℝ), ‖printedAtkinsonPrefix T (2^j) x‖))*
            Real.exp (-(G^2*((2^j:ℕ):ℝ))/T)) :=
  exists_zetaSquareLocalMean_le_printedAtkinson hδ hη

example (T : ℝ) (K : ℕ) : printedAtkinsonPrefix T K 0 = 0 := by
  simp [printedAtkinsonPrefix]

-- A genuine sub-fourth-root source width, with the original printed cutoff.
example :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^(1/10:ℝ) ≤ G → G ≤ T^(1/2-(1/10:ℝ)) →
      (∫ t in T-G..T+G, zetaMomentCriticalNorm t^2) ≤ C*(G*Real.log T+
        ∑ j ∈ printedAtkinsonDyadicIndices T G (1/10),
          printedAtkinsonBlockBound T G (2^j)) :=
  exists_zetaSquareLocalMean_le_exactPrinted
    (by norm_num : (0:ℝ) < 1/10) (by norm_num : (0:ℝ) < 1/10)

end AtkinsonPrintedSourceRegression
