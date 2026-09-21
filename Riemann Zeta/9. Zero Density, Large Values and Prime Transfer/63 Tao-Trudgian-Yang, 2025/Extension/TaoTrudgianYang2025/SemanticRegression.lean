import TaoTrudgianYang2025

open scoped NNReal FourierTransform
open TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

/-! Exact-type compatibility checks for the bootstrap dependency graph. -/

example (α : ℝ≥0) :
    Expdb.IsExponentSumBound α (Expdb.exponentSumGrowthExponent α) :=
  Expdb.isExponentSumBound_exponentSumGrowthExponent α

example : RiemannZeta.GuthMaynard.PublishedGuthMaynardLargeValues :=
  RiemannZeta.GuthMaynard.guthMaynardLargeValues_published_native

example : RiemannZeta.GuthMaynard.PublishedGuthMaynardZeroDensity
    (fun sigma T => RiemannZeta.GuthMaynard.N sigma T) :=
  RiemannZeta.GuthMaynard.guthMaynardZeroDensity_published_native

example : 0 < 2493 * (14 / 15 + 1 / 1000 : ℝ) - 2014 := by
  apply optimizedBourgainPieceTwo_denominator_pos
  · norm_num
  · norm_num

example {k l : ℝ} :
    IsExponentPairEstimate k l ↔
      IsExponentPairEstimateNonAsymptotic k l :=
  isExponentPairEstimate_iff_nonAsymptotic

example {k₀ l₀ k₁ l₁ θ : ℝ}
    (h₀ : ExponentPair k₀ l₀) (h₁ : ExponentPair k₁ l₁)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    ExponentPair ((1 - θ) * k₀ + θ * k₁)
      ((1 - θ) * l₀ + θ * l₁) :=
  h₀.convexCombination h₁ hθ₀ hθ₁

example {k l : ℝ} (h : ExponentPair k l) :
    Expdb.exponentSumGrowthExponent 0 ≤ exponentPairLine k l 0 := by
  apply exponentSumGrowthExponent_le_exponentPairLine h
  norm_num

/-- Two equal values remain two indexed multiset elements, so all sixteen
ordered quadruples contribute. -/
example : additiveEnergy (fun _ : Fin 2 ↦ (0 : ℝ)) = 16 := by
  norm_num [additiveEnergy, approximateAdditiveEnergy,
    approximateAdditiveEnergyOf, AdditiveQuadruple]

example (W : Finset ℝ)
    (hW : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → 1 ≤ |x - y|) :
    W.card ^ 2 ≤ finsetAdditiveEnergy W ∧
      finsetAdditiveEnergy W ≤ 3 * W.card ^ 3 :=
  ⟨finset_card_square_le_additiveEnergy W,
    finset_additiveEnergy_le_three_mul_cube W hW⟩

example (σ T : ℝ) :
    paperZeroCount σ T =
      RiemannZeta.GuthMaynard.zeroCountRect σ 1 (-T) T :=
  paperZeroCount_eq_zeroCountRect σ T

example {σ T : ℝ} (ρ : ℂ) :
    ρ ∈ paperZeros σ T ↔
      σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T ∧ riemannZeta ρ = 0 :=
  mem_paperZeros_iff ρ

example (σ A : ℝ) : IsZeroDensityBound σ A ↔
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 1 ≤ C ∧
        ∃ δ : ℝ, 0 < δ ∧
          ∀ T : ℝ, C ≤ T →
            (paperZeroCount (σ - δ) T : ℝ) ≤
              C * T ^ (A * (1 - σ) + ε) :=
  Iff.rfl

example : IsZeroDensityBound (3 / 4 : ℝ)
    (3 / (3 * (3 / 4 : ℝ) - 1)) :=
  huxley_isZeroDensityBound_inclusive (by norm_num) (by norm_num)

example : IsZeroDensityBound (7 / 10 : ℝ)
    (15 / (3 + 5 * (7 / 10 : ℝ))) :=
  guthMaynard_isZeroDensityBound_inclusive (by norm_num) (by norm_num)

example : IsZeroDensityBound (1 : ℝ) (3 / (3 * (1 : ℝ) - 1)) :=
  huxley_isZeroDensityBound_inclusive (by norm_num) (by norm_num)

example (n : ℕ) (t : ℝ) :
    dirichletPhase n t =
      Complex.cpow (n : ℂ) (-(Complex.I * (t : ℂ))) :=
  rfl

example (P : LargeValuePattern) (n : ℕ) :
    n ∈ P.indices ↔ P.N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * P.N :=
  P.mem_indices_iff n

example (σ τ ρ : ℝ) : IsLargeValueBound σ τ ρ ↔
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 1 ≤ C ∧
        ∃ δ : ℝ, 0 < δ ∧
          ∀ P : LargeValuePattern,
            C ≤ P.N →
            P.N ^ (τ - δ) ≤ P.T →
            P.T ≤ P.N ^ (τ + δ) →
            P.N ^ (σ - δ) ≤ P.V →
            P.V ≤ P.N ^ (σ + δ) →
            (P.ordinates.card : ℝ) ≤ C * P.N ^ (ρ + ε) :=
  Iff.rfl

example {σ τ : ℝ} (hσLower : 1 / 2 ≤ σ) (hσUpper : σ ≤ 1)
    (hτ : 0 ≤ τ) :
    IsLargeValueBound σ τ
      (max (2 - 2 * σ)
        (max (18 / 5 - 4 * σ) (τ + 12 / 5 - 4 * σ))) := by
  simpa [guthMaynardLargeValueExponent] using
    guthMaynard_largeValueBound hσLower hσUpper hτ

example (σ Astar : ℝ) : IsZeroDensityEnergyBound σ Astar ↔
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 1 ≤ C ∧
        ∃ δ : ℝ, 0 < δ ∧
          ∀ T : ℝ, C ≤ T →
            (zeroAdditiveEnergy (σ - δ) T : ℝ) ≤
              C * T ^ (Astar * (1 - σ) + ε) :=
  Iff.rfl

example (σ T : ℝ) : Fintype.card (ZeroCopy σ T) = paperZeroCount σ T :=
  zeroCopy_card σ T

example (σ T center : ℝ) :
    ((Finset.univ : Finset (ZeroCopy σ T)).filter fun z =>
      |center - (z.1 : ℂ).im| ≤ 1).card =
      ∑ ρ ∈ paperZeros σ T,
        if |center - ρ.im| ≤ 1 then
          analyticVanishingOrder riemannZeta ρ else 0 :=
  zeroCopy_local_card_eq_weighted_sum σ T center

example {σ τ ρstar : ℝ} (h : IsLargeValueEnergyBound σ τ ρstar) :
    IsZetaLargeValueEnergyBound σ τ ρstar :=
  h.toZeta

example (σ τ : ℝ) :
    (2 : EReal) * largeValueExponent σ τ ≤ largeValueEnergyExponent σ τ ∧
      largeValueEnergyExponent σ τ ≤
        (3 : EReal) * largeValueExponent σ τ :=
  ⟨two_mul_largeValueExponent_le_largeValueEnergyExponent σ τ,
    largeValueEnergyExponent_le_three_mul_largeValueExponent σ τ⟩

example (σ τ : ℝ) :
    (2 : EReal) * zetaLargeValueExponent σ τ ≤
        zetaLargeValueEnergyExponent σ τ ∧
      zetaLargeValueEnergyExponent σ τ ≤
        (3 : EReal) * zetaLargeValueExponent σ τ :=
  ⟨two_mul_zetaLargeValueExponent_le_zetaLargeValueEnergyExponent σ τ,
    zetaLargeValueEnergyExponent_le_three_mul_zetaLargeValueExponent σ τ⟩

example (σ : ℝ) :
    (2 : EReal) * zeroDensityExponent σ ≤
        zeroDensityEnergyExponent σ ∧
      zeroDensityEnergyExponent σ ≤
        (4 : EReal) * zeroDensityExponent σ :=
  ⟨two_mul_zeroDensityExponent_le_zeroDensityEnergyExponent σ,
    zeroDensityEnergyExponent_le_four_mul_zeroDensityExponent σ⟩

example (σ : ℝ) (hσ : 1 / 2 < σ) :
    (2 : EReal) * zeroDensityExponent σ ≤
        zeroDensityEnergyExponent σ ∧
      zeroDensityEnergyExponent σ ≤
        (3 : EReal) * zeroDensityExponent σ :=
  ⟨two_mul_zeroDensityExponent_le_zeroDensityEnergyExponent σ,
    zeroDensityEnergyExponent_le_three_mul_zeroDensityExponent σ hσ⟩

example {σ T : ℝ} (hσ : 1 / 2 ≤ σ) :
    zeroAdditiveEnergy σ T ≤
      max (paperZeroCount (1 / 2) 10)
        (3 * classicalLocalMultiplicityCap T) * paperZeroCount σ T ^ 3 :=
  zeroAdditiveEnergy_le_globalCap_mul_cube hσ

example (σ T d : ℝ) (shifted : ZeroCopy σ T → ℝ)
    (hshift : ∀ z, |shifted z - (z.1 : ℂ).im| ≤ d) :
    zeroAdditiveEnergy σ T ≤
      approximateAdditiveEnergyOf (1 + 4 * d) shifted :=
  zeroAdditiveEnergy_le_perturbed σ T d shifted hshift

example (σ T d : ℝ) (shifted : ZeroCopy σ T → ℝ)
    (hshift : ∀ z, |shifted z - (z.1 : ℂ).im| ≤ d) :
    zeroAdditiveEnergy σ T ≤
      (4 * Nat.ceil (1 + 4 * d) + 6) *
        approximateAdditiveEnergyOf 1 shifted :=
  zeroAdditiveEnergy_le_mul_perturbed_unit σ T d shifted hshift

example (δ : ℝ) (hδ : 0 < δ) :
    ∃ T₀ : ℝ, Real.exp 2 ≤ T₀ ∧
      ∀ (σ T : ℝ), 7 / 10 ≤ σ → σ ≤ 4 / 5 → T₀ ≤ T →
        ∃ shifted : TypeIZeroCopy σ T → ℝ,
          (∀ z, |(z.1.1 : ℂ).im - shifted z| ≤ T ^ δ) ∧
          (∀ z, 1 / (4 * Real.log T) ≤
            ‖RiemannZeta.GuthMaynard.detectPoly
              (2 ^ RiemannZeta.GuthMaynard.chosenTypeIScale z.1.1 T)
              (σ + Complex.I * shifted z) T‖) :=
  typeIZeroCopy_exists_shifted_detector δ hδ

example {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (W : ι → ℝ) (color : ι → κ) :
    ∃ label : Fin 4 → κ,
      let Wᵢ := fun i : Fin 4 =>
        fun x : EnergyColorFiber color (label i) => W x.1
      4 * (approximateAdditiveEnergyOf 1 W : ℝ) ≤
        9 * (Fintype.card κ : ℝ) ^ 4 *
          ((approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
            (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
            (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
            (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ)) :=
  exists_energy_color_classes W color

example {ι κ : Type*} [Fintype ι] [LinearOrder ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (W : ι → ℝ) (color : ι → κ) (L : ℕ)
    (hlocal : ∀ z : ℤ, (unitBinFinset W z).card ≤ L) :=
  exists_separated_energy_color_classes W color L hlocal

example (δ : ℝ) (hδ : 0 < δ) :=
  typeIZeroAdditiveEnergy_le_detector_scale_class_energies δ hδ

example (δ : ℝ) (hδ : 0 < δ) :=
  typeIZeroAdditiveEnergy_le_separated_detector_scale_class_energies δ hδ

example (σ T : ℝ) (shift : ↥(typeIZeroSet σ T) → ℝ) (z : ℤ) :=
  typeIZeroCopy_shifted_unitBin_card σ T shift z

example {ι : Type*} [Fintype ι] [DecidableEq ι] (W : ι → ℝ)
    (hsep : ∀ x y : ι, x ≠ y → 1 ≤ |W x - W y|) :
    finsetAdditiveEnergy (Finset.univ.image W) =
      approximateAdditiveEnergyOf 1 W :=
  finsetAdditiveEnergy_image_eq W hsep

example (σ ε : ℝ) (hσ : 0 ≤ σ) (hε : 0 < ε) :=
  exists_detectorPatternNormalization_le_const_mul_rpow σ ε hσ hε

example (δ σ T : ℝ) (hT : Real.exp 2 ≤ T)
    (shifted : TypeIZeroCopy σ T → ℝ) (L : ℕ)
    (hlocal : ∀ z : ℤ, (unitBinFinset shifted z).card ≤ L)
    (label : TypeISeparatedScaleColor T L)
    (x₀ : EnergyColorFiber
      (typeISeparatedScaleColor σ T shifted L hlocal) label)
    (hshift : ∀ x : TypeIZeroCopy σ T,
      |(x.1.1 : ℂ).im - shifted x| ≤ T ^ δ)
    (hlarge : ∀ x : EnergyColorFiber
      (typeISeparatedScaleColor σ T shifted L hlocal) label,
      1 / (4 * Real.log T) ≤
        ‖detectPoly (2 ^ typeIScaleColorIndex label.1)
          (σ + Complex.I * shifted x.1) T‖)
    (hsep : ∀ x y : EnergyColorFiber
      (typeISeparatedScaleColor σ T shifted L hlocal) label,
      x ≠ y → 1 ≤ |shifted x.1 - shifted y.1|) :=
  exists_typeIDetectorClassPattern δ σ T hT shifted L hlocal label x₀
    hshift hlarge hsep

example (σ T : ℝ) :
    Fintype.card (ClassicalSlabZeroCopy σ T) =
      zeroCountRect σ 1 T (2 * T) :=
  classicalSlabZeroCopy_card σ T

example (σ T H : ℝ) (L₀ : ℕ)
    (shift : ↥(zerosInRect σ 1 T (2 * T)) → ℝ)
    (hshift : ∀ ρ : ↥(zerosInRect σ 1 T (2 * T)),
      |(ρ : ℂ).im - shift ρ| ≤ H)
    (hlocal : ∀ z : ℤ,
      ∑ ρ ∈ (zerosInRect σ 1 T (2 * T)).filter
        (fun ρ => (z : ℝ) ≤ ρ.im ∧ ρ.im < (z : ℝ) + 1),
        analyticVanishingOrder riemannZeta ρ ≤ L₀)
    (z : ℤ) :
    (unitBinFinset
      (fun x : ClassicalSlabZeroCopy σ T => shift x.1) z).card ≤
        (2 * Nat.ceil H + 1) * L₀ :=
  classicalSlabZeroCopy_shifted_unitBin_card_le σ T H L₀
    shift hshift hlocal z

example (σ T d : ℝ) (shifted : ClassicalSlabZeroCopy σ T → ℝ)
    (hshift : ∀ z, |shifted z - (z.1.1 : ℂ).im| ≤ d) :=
  classicalSlabZeroEnergy_le_shifted_unit σ T d shifted hshift

example (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    (∑ n ∈ Finset.Icc N (2 * N),
      closedDyadicCoeff N a n * dirichletPhase n t) =
        dirichletPoly N a t :=
  sum_closedDyadicCoeff_eq_dirichletPoly N a t

example (A N : ℕ) (σ t : ℝ) :
    dirichletPoly N (normalizedClassicalZetaLongLineCoeff A N σ) t =
      (((N : ℝ) ^ σ : ℝ) : ℂ) *
        dirichletPoly N (classicalZetaLongLineCoeff A σ) t :=
  dirichletPoly_normalizedClassicalZetaLongLineCoeff A N σ t

example (A N : ℕ) (σ V t : ℝ) (hN : 0 < N)
    (hlarge : V ≤
      ‖dirichletPoly N (classicalZetaLongLineCoeff A σ) t‖) :
    ∃ r : Fin 2, V / 2 ≤
      ‖typeISourceSmoothBlock N (min (2 * N) A) r σ t‖ :=
  exists_large_typeISourceSmoothBlock_of_sharp_large A N σ V t hN hlarge

example (A N : ℕ) (σ t : ℝ) (hN : 0 < N) :
    dirichletPoly N (classicalZetaLongLineCoeff A σ) t =
      ((((N : ℝ) ^ (-σ) : ℝ) : ℂ) *
        ∫ ξ : ℝ, 𝓕 (classicalTypeILogProfileSchwartz σ) ξ *
          Complex.exp
            (-(((2 * Real.pi * ξ * Real.log (N : ℝ) : ℝ) : ℂ) * Complex.I)) *
          ∑ n ∈ Finset.Ioc N (min (2 * N) A),
            (n : ℂ) ^
              (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * Complex.I)) :=
  dirichletPoly_classicalZetaLongLineCoeff_fourierDeweight
    A N σ t hN

example (A N : ℕ) (t : ℝ) :
    dirichletPoly N (classicalTypeICoefficientOneCoeff A) t =
      ∑ n ∈ Finset.Ioc N (min (2 * N) A), dirichletPhase n t :=
  dirichletPoly_classicalTypeICoefficientOneCoeff_eq_active_sum A N t

example (A N : ℕ) (σ V t : ℝ) (hN : 0 < N) (hV : 0 < V)
    (hlarge : V ≤
      ‖dirichletPoly N (classicalZetaLongLineCoeff A σ) t‖) :
    ∃ ξ : ℝ,
      V / (2 * (N : ℝ) ^ (-σ) * classicalTypeIFourierL1 σ) ≤
        ‖∑ n ∈ Finset.Ioc N (min (2 * N) A),
          (n : ℂ) ^
            (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * Complex.I)‖ :=
  exists_large_coefficientOne_shift_of_classicalTypeI
    A N σ V t hN hV hlarge

example (A N k : ℕ) (σ V t R : ℝ) (hN : 0 < N) (hV : 0 < V)
    (hk : 1 < k) (hR : 0 < R)
    (hlarge : V ≤
      ‖dirichletPoly N (classicalZetaLongLineCoeff A σ) t‖)
    (htail :
      (N : ℝ) ^ (-σ) * (Finset.Ioc N (min (2 * N) A)).card *
        ((2 * SchwartzMap.seminorm ℝ k 0
            (𝓕 (classicalTypeILogProfileSchwartz σ)) / ((k : ℝ) - 1)) *
          R ^ (1 - (k : ℝ))) ≤ V / 2) :
    ∃ ξ ∈ Set.Icc (-R) R,
      V / (4 * (N : ℝ) ^ (-σ) * classicalTypeIFourierL1 σ) ≤
        ‖∑ n ∈ Finset.Ioc N (min (2 * N) A),
          (n : ℂ) ^
            (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * Complex.I)‖ :=
  exists_bounded_coefficientOne_shift_of_classicalTypeI
    A N k σ V t R hN hV hk hR hlarge htail

example (A N k : ℕ) (σ V : ℝ) (hV : 0 < V) (hk : 1 < k) :
    let R := classicalTypeIFourierRadius A N k σ V
    (N : ℝ) ^ (-σ) * (Finset.Ioc N (min (2 * N) A)).card *
        ((2 * SchwartzMap.seminorm ℝ k 0
            (𝓕 (classicalTypeILogProfileSchwartz σ)) / ((k : ℝ) - 1)) *
          R ^ (1 - (k : ℝ))) ≤ V / 2 :=
  classicalTypeIFourierRadius_tail_numeric A N k σ V hV hk

example (A N k : ℕ) (σ V T α δ : ℝ) (hV : 0 < V) (hk : 1 < k)
    (hT : 1 ≤ T) (horder : α ≤ δ * ((k : ℝ) - 1))
    (hbase :
      1 +
          4 * ((N : ℝ) ^ (-σ) * (Finset.Ioc N (min (2 * N) A)).card) *
            SchwartzMap.seminorm ℝ k 0
              (𝓕 (classicalTypeILogProfileSchwartz σ)) /
            (((k : ℝ) - 1) * V) ≤
        T ^ α) :
    classicalTypeIFourierRadius A N k σ V ≤ T ^ δ :=
  classicalTypeIFourierRadius_le_rpow_of_base_growth
    A N k σ V T α δ hV hk hT horder hbase

example (D δ : ℝ) (hδ : 0 < δ) :
    ∃ k : ℕ, 1 < k ∧
      D + 1 + δ / 2 ≤ δ * ((k : ℝ) - 1) :=
  exists_classicalTypeIFourier_order D δ hδ

example (A N k : ℕ) (σ V t : ℝ) (hN : 0 < N) (hV : 0 < V)
    (hk : 1 < k)
    (hlarge : V ≤
      ‖dirichletPoly N (classicalZetaLongLineCoeff A σ) t‖) :
    let R := classicalTypeIFourierRadius A N k σ V
    ∃ ξ ∈ Set.Icc (-R) R,
      V / (4 * (N : ℝ) ^ (-σ) * classicalTypeIFourierL1 σ) ≤
        ‖∑ n ∈ Finset.Ioc N (min (2 * N) A),
          (n : ℂ) ^
            (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * Complex.I)‖ :=
  exists_explicitly_bounded_coefficientOne_shift_of_classicalTypeI
    A N k σ V t hN hV hk hlarge

example (Y A r : ℕ) (σ V t : ℝ) (hY : 0 < Y) (hV : 0 < V)
    (hlarge : V ≤ ‖typeISourceSmoothBlock Y A r σ t‖) :
    ∃ ξ : ℝ,
      V / (2 * typeISourceSmoothBlockFourierL1 Y A r σ hY) ≤
        ‖∑ n ∈ Finset.Ioc Y A,
          (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * Complex.I)‖ :=
  exists_large_coefficientOne_shift_of_typeISourceSmoothBlock
    Y A r σ V t hY hV hlarge

example (Y A r : ℕ) (σ t : ℝ) (hY : 0 < Y) :
    typeISourceSmoothBlock Y A r σ t =
      ∫ ξ : ℝ, 𝓕 (typeILogWeightSchwartz Y A r σ hY) ξ *
        ∑ n ∈ Finset.Ioc Y A,
          (n : ℂ) ^
            (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * Complex.I) :=
  typeISourceSmoothBlock_fourierDeweight_restricted Y A r σ t hY

example (Y A r : ℕ) (σ V t : ℝ) (hY : 0 < Y) (hV : 0 < V) :
    let R := typeISourceFourierRadius Y A r σ V hY
    ‖∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ,
        𝓕 (typeILogWeightSchwartz Y A r σ hY) ξ *
          ∑ n ∈ Finset.Ioc Y A,
            (n : ℂ) ^
              (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * Complex.I)‖ ≤
      V / 2 :=
  norm_typeILogWeight_fourier_tail_integral_le_half
    Y A r σ V t hY hV

example (Y A r : ℕ) (σ V t : ℝ) (hY : 0 < Y) (hV : 0 < V)
    (hlarge : V ≤ ‖typeISourceSmoothBlock Y A r σ t‖) :
    let R := typeISourceFourierRadius Y A r σ V hY
    ∃ ξ ∈ Set.Icc (-R) R,
      V / (4 * typeISourceSmoothBlockFourierL1 Y A r σ hY) ≤
        ‖∑ n ∈ Finset.Ioc Y A,
          (n : ℂ) ^
            (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * Complex.I)‖ :=
  exists_explicitly_bounded_coefficientOne_shift_of_typeISourceSmoothBlock
    Y A r σ V t hY hV hlarge

example {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W W' : ι → ℝ) (d : ℝ) (hd : 0 ≤ d)
    (hsep : ∀ x y : ι, x ≠ y → 1 ≤ |W x - W y|)
    (hpert : ∀ x, |W' x - W x| ≤ d) (z : ℤ) :
    (unitBinFinset W' z).card ≤ Nat.ceil (2 * d + 2) :=
  unitBinFinset_perturbation_card_le_natCeil
    W W' d hd hsep hpert z

example (N : ℕ) (T u d tau delta : ℝ)
    (hN : 1 ≤ (N : ℝ)) (hdelta : 0 < delta)
    (hu : 0 ≤ u) (huT : u ≤ T) (hd : 0 ≤ d) (hdT : d ≤ T)
    (hTLower : (N : ℝ) ^ (tau - delta / 2) ≤ T)
    (hTUpper : T ≤ (N : ℝ) ^ (tau + delta / 2))
    (hFive : 5 ≤ (N : ℝ) ^ (delta / 2)) :
    (N : ℝ) ^ (tau - delta) ≤
        (2 * T + u + d) - (T - u - d) ∧
      (2 * T + u + d) - (T - u - d) ≤
        (N : ℝ) ^ (tau + delta) :=
  classicalSlab_expanded_height_in_rpow_window
    N T u d tau delta hN hdelta hu huT hd hdT
      hTLower hTUpper hFive

example {σ τ ρ ρstar s : ℝ}
    (h : InLargeValueEnergyRegion σ τ ρ ρstar s) :
    ρ ≤ τ ∧ 2 * ρ ≤ ρstar ∧ ρstar ≤ 3 * ρ ∧
      ρ + 2 ≤ s ∧ s ≤ 2 * ρ + 2 :=
  ⟨h.rho_le_tau, h.two_mul_rho_le_rhoStar,
    h.rhoStar_le_three_mul_rho, h.rho_add_two_le_s,
    h.s_le_two_mul_rho_add_two⟩

-- All shared endpoints have one deterministic height color. The upper
-- endpoint of the last slab remains in that slab.
example :
    (classicalTypeIHeightColor 10 5, classicalTypeIHeightColor 10 10,
      classicalTypeIHeightColor 10 20, classicalTypeIHeightColor 10 40) =
      ((0 : Fin 3), (1 : Fin 3), (2 : Fin 3), (2 : Fin 3)) := by
  norm_num [classicalTypeIHeightColor]

example :
    classicalTypeIHeight 10 0 = 5 ∧
      classicalTypeIHeight 10 1 = 10 ∧ classicalTypeIHeight 10 2 = 20 := by
  norm_num [classicalTypeIHeight, Fin.ext_iff]

-- Closed support includes N, but its coefficient is zero. The active
-- integer interval includes its right cutoff and excludes the next integer.
example :
    closedDyadicCoeff 2 (classicalTypeICoefficientOneCoeff 3) 2 = 0 ∧
      closedDyadicCoeff 2 (classicalTypeICoefficientOneCoeff 3) 3 = 1 ∧
      closedDyadicCoeff 2 (classicalTypeICoefficientOneCoeff 3) 4 = 0 := by
  norm_num [closedDyadicCoeff, classicalTypeICoefficientOneCoeff]

example : Finset.Ioc 2 (min (2 * 2) 3) = ({3} : Finset ℕ) := by decide

example : Finset.Ioc 4 (min (2 * 4) 3) = (∅ : Finset ℕ) := by decide

example (σ τ : ℝ) :
    largeValueEnergyRegionSupremum σ τ ≤
        largeValueEnergyExponent σ τ ∧
      zetaLargeValueEnergyRegionSupremum σ τ ≤
        zetaLargeValueEnergyExponent σ τ :=
  ⟨largeValueEnergyRegionSupremum_le_largeValueEnergyExponent σ τ,
    zetaLargeValueEnergyRegionSupremum_le_zetaLargeValueEnergyExponent σ τ⟩

example {σ τ : ℝ} (hσLower : 1 / 2 ≤ σ) (hσUpper : σ ≤ 1)
    (hτ : 0 ≤ τ) :
    largeValueEnergyExponent σ τ =
        largeValueEnergyRegionSupremum σ τ ∧
      zetaLargeValueEnergyExponent σ τ =
        zetaLargeValueEnergyRegionSupremum σ τ :=
  ⟨largeValueEnergyExponent_eq_regionSupremum hσLower hσUpper hτ,
    zetaLargeValueEnergyExponent_eq_regionSupremum hσLower hσUpper hτ⟩

example {σ τ ρ ρstar s : ℝ} :
    InLargeValueEnergyRegionAsymptotic σ τ ρ ρstar s ↔
      InLargeValueEnergyRegion σ τ ρ ρstar s :=
  inLargeValueEnergyRegionAsymptotic_iff

example {σ τ ρ ρstar s : ℝ} :
    InZetaLargeValueEnergyRegionAsymptotic σ τ ρ ρstar s ↔
      InZetaLargeValueEnergyRegion σ τ ρ ρstar s :=
  inZetaLargeValueEnergyRegionAsymptotic_iff

example {σ τ ρstar : ℝ} :
    IsLargeValueEnergyBoundAsymptotic σ τ ρstar ↔
      IsLargeValueEnergyBound σ τ ρstar :=
  isLargeValueEnergyBoundAsymptotic_iff

example {σ τ ρstar : ℝ} :
    IsZetaLargeValueEnergyBoundAsymptotic σ τ ρstar ↔
      IsZetaLargeValueEnergyBound σ τ ρstar :=
  isZetaLargeValueEnergyBoundAsymptotic_iff

example {σ Astar : ℝ} :
    IsZeroDensityEnergyBoundAsymptotic σ Astar ↔
      IsZeroDensityEnergyBound σ Astar :=
  isZeroDensityEnergyBoundAsymptotic_iff

example :
    InExponentPairTriangle (89 / 1282 : ℝ) (997 / 1282 : ℝ) :=
  publishedExponentPairs_mem_triangle.1

example : generatedExponentPairCoordinates = [
    (89 / 1282, 997 / 1282),
    (652397 / 9713986, 7599781 / 9713986),
    (10769 / 351096, 609317 / 702192),
    (89 / 3478, 15327 / 17390)] := by
  rfl

example : generatedEnergyClauses.map
    (fun clause => (clause.lower, clause.upper, clause.bounds.length)) = [
      (3 / 4, 5 / 6, 2),
      (7 / 10, 3 / 4, 2),
      (173 / 229, 443 / 586, 3),
      (443 / 586, 373 / 493, 2),
      (373 / 493, 103 / 136, 3),
      (103 / 136, 42 / 55, 2),
      (42 / 55, 79 / 103, 2),
      (79 / 103, 84 / 109, 2),
      (84 / 109, 5 / 6, 2)] := by
  rfl

example : ∀ clause ∈ generatedEnergyClauses,
    EnergyClauseDenominatorsPositive clause :=
  generatedEnergyClauses_denominatorsPositive

example := optimizedBourgain_endpoint_agreement

-- Type II normalization retains both the dyadic count and divisor power.
example :
    ((((3 / 4 : ℝ) * (3 / 4)) / Nat.clog 2 2) /
      ((1 : ℝ) * (2 * 2 : ℝ) ^ (0 : ℝ) * (2 : ℝ) ^ (-(1 : ℝ)))) = 9 / 8 := by
  norm_num [Real.rpow_neg_one, Nat.clog]

example :
    ((((3 / 4 : ℝ) * (3 / 4)) / Nat.clog 2 2) /
      ((1 : ℝ) * (2 * 2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-(1 : ℝ)))) = 9 / 32 := by
  norm_num [Real.rpow_neg_one, Nat.clog]

example (s T D t : ℝ) (Y X : ℕ) :
    ¬ ClassicalBranchScaleLarge s T D Y X none t := by
  simp only [ClassicalBranchScaleLarge, not_false_eq_true]

-- Signed slabs have closed endpoints; the low-height color includes its edge.
example (σ : ℝ) (hσ : 1 / 2 < σ) (hσUpper : σ < 1) :
    zeroDensityEnergyExponent σ * ((1 - σ : ℝ) : EReal) ≤
      max (sSup ((fun τ : ℝ => zetaLargeValueEnergyExponent σ τ / (τ : EReal)) '' Set.Ici 1))
        (Filter.limsup (fun τ : ℝ => largeValueEnergyExponent σ τ / (τ : EReal)) Filter.atTop) :=
  zeroDensityEnergyExponent_le_sup_limsup σ hσ hσUpper

example : finsetAdditiveEnergy
    (singletonLargeValuePattern 2 1 0 (by norm_num) (by norm_num)).ordinates = 1 :=
  singletonLargeValuePattern_energy 2 1 0 (by norm_num) (by norm_num)

example : ZeroDyadicColorCondition 2 8 (-4) (some (true, ⟨0, by omega⟩)) := by
  norm_num [ZeroDyadicColorCondition]

example : ZeroDyadicColorCondition 2 8 4 (some (false, ⟨0, by omega⟩)) := by
  norm_num [ZeroDyadicColorCondition]

example : ZeroDyadicColorCondition 2 8 (-2) none := by
  norm_num [ZeroDyadicColorCondition]

example : approximateAdditiveEnergyOf 1 (fun _ : Fin 2 => (0 : ℝ)) = 16 := by
  norm_num [approximateAdditiveEnergyOf, AdditiveQuadrupleOf]

-- The uniform scale neighborhood includes excursions past either endpoint.
example : ∃ y ∈ Set.Icc (1 : ℝ) 2, |(9 / 10 : ℝ) - y| ≤ 1 / 10 :=
  exists_mem_Icc_abs_sub_le_of_bounds 1 2 (9 / 10) (1 / 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : ∃ y ∈ Set.Icc (1 : ℝ) 2, |(21 / 10 : ℝ) - y| ≤ 1 / 10 :=
  exists_mem_Icc_abs_sub_le_of_bounds 1 2 (21 / 10) (1 / 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : ∃ y ∈ Set.Icc (1 : ℝ) 1, |(1 : ℝ) - y| ≤ 0 :=
  exists_mem_Icc_abs_sub_le_of_bounds 1 1 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example := optimizedBourgain_interval_cover

-- The pinned five-coordinate powering clause contradicts actual region membership.
example : InLargeValueEnergyRegion (3 / 4) 2 0 0 2 :=
  energyPowering_source_counterexample.1

-- The repair keeps actual region membership and leaves the fifth exponent free.
example : CardinalityEnergyPoweringWitnesses (3 / 4) 2 0 0 2 :=
  singleton_cardinalityEnergyPoweringWitnesses _ _ _
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : CardinalityEnergyPoweringWitnesses (1 / 2) 0 0 0 3 :=
  singleton_cardinalityEnergyPoweringWitnesses _ _ _
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : CardinalityEnergyPoweringWitnesses 1 2 0 0 4 :=
  singleton_cardinalityEnergyPoweringWitnesses _ _ _
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

-- The compact powered-height interval includes both endpoints.
example : ∃ k : ℕ, 1 ≤ k ∧ (2 : ℝ) / k ∈ Set.Icc (2 : ℝ) 4 := by
  simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using
    exists_power_height_in_Icc (τ₀ := 2) (τ := 2) (by norm_num) (by norm_num)

example : ∃ k : ℕ, 1 ≤ k ∧ (4 : ℝ) / k ∈ Set.Icc (2 : ℝ) 4 := by
  simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using
    exists_power_height_in_Icc (τ₀ := 2) (τ := 4) (by norm_num) (by norm_num)

-- This signature intentionally retains endpoint one, not the unproved two.
example (σ B τ₀ : ℝ) (hσ : 1 / 2 < σ) (hσUpper : σ < 1)
    (hB : 0 ≤ B) (hτ₀ : 0 < τ₀)
    (hZeta : ∀ τ ∈ Set.Ico (1 : ℝ) τ₀, IsZetaLargeValueEnergyBound σ τ (B * τ))
    (hGeneral : ∀ τ ∈ Set.Icc τ₀ (2 * τ₀), IsLargeValueEnergyBound σ τ (B * τ)) :
    IsZeroDensityEnergyBound σ (B / (1 - σ)) :=
  isZeroDensityEnergyBound_of_bounded_energy_ranges σ B τ₀ hσ hσUpper hB hτ₀ hZeta hGeneral

-- The full theorem, not just the singleton helper, recovers this witness.
example : CardinalityEnergyPoweringWitnesses (3 / 4) 2 0 0 2 :=
  correctedCardinalityEnergyPowering _ _ _ _ _ (by norm_num)
    ⟨2, energyPowering_source_counterexample.1⟩

-- Every positive integer power and both sigma endpoints use the full proof.
example (k : ℕ) (hk : 1 ≤ k) :
    CardinalityEnergyPoweringWitnesses (1 / 2) 0 0 0 k :=
  correctedCardinalityEnergyPowering _ _ _ _ k hk
    ⟨2, singleton_mem_largeValueEnergyRegion _ _
      (by norm_num) (by norm_num) (by norm_num)⟩

example (k : ℕ) (hk : 1 ≤ k) : CardinalityEnergyPoweringWitnesses 1 2 0 0 k :=
  correctedCardinalityEnergyPowering _ _ _ _ k hk
    ⟨2, singleton_mem_largeValueEnergyRegion _ _
      (by norm_num) (by norm_num) (by norm_num)⟩

-- Exact expanded interface: two witnesses, two independent fifth coordinates.
example (σ τ ρ energy s : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (h : InLargeValueEnergyRegion σ τ ρ energy s) :
    (∃ eCard sCard : ℝ,
      InLargeValueEnergyRegion σ (τ / k) (ρ / k) eCard sCard ∧ eCard ≤ energy / k) ∧
    (∃ rEnergy sEnergy : ℝ,
      InLargeValueEnergyRegion σ (τ / k) rEnergy (energy / k) sEnergy ∧ rEnergy ≤ ρ / k) :=
  h.corrected_powering k hk

example (σ τ ρ energy : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (h : InCardinalityEnergyRegion σ τ ρ energy)
    (hHeathBrown : ∀ card e : ℝ,
      InCardinalityEnergyRegion σ (τ / k) card e →
        e ≤ heathBrownEnergyRHS σ (τ / k) card e) :
    energy / k ≤ heathBrownEnergyRHS σ (τ / k) (ρ / k) (energy / k) :=
  h.powered_heathBrown_relation k hk hHeathBrown

example (σ τ ρ energy : ℝ) (k : ℕ)
    (h : CardinalityEnergyPoweringWitnesses σ τ ρ energy k)
    (hHeathBrown : ∀ card e : ℝ,
      InCardinalityEnergyRegion σ (τ / k) card e →
        e ≤ heathBrownEnergyRHS σ (τ / k) card e) :
    energy / k ≤ heathBrownEnergyRHS σ (τ / k) (ρ / k) (energy / k) :=
  h.heathBrown_relation hHeathBrown

example : ¬ ∃ ρ' ρstar' s' : ℝ,
    InLargeValueEnergyRegion (3 / 4) 1 ρ' ρstar' s' ∧ s' ≤ 1 := by
  rintro ⟨ρ', ρstar', s', hregion, hs⟩
  have hlower := hregion.two_le_s
  linarith

example : doubleZetaSum (singletonLargeValuePattern 2 (3 / 4) 2
    (by norm_num) (by norm_num)) = 9 := by
  rw [singletonLargeValuePattern_doubleZetaSum]
  norm_num

-- Actual five-coordinate source interface, with no separate analytic premise.
example (σ τ ρ e s : ℝ) (h : InLargeValueEnergyRegion σ τ ρ e s) :
    e ≤ 1 - 2 * σ +
      1 / 2 * max (max (ρ + 1) (2 * ρ)) (5 / 4 * ρ + τ / 2) +
      1 / 2 * max (max (e + 1) (4 * ρ)) (3 / 4 * e + ρ + τ / 2) :=
  h.heathBrown_relation

example (σ τ ρ e : ℝ) (h : InCardinalityEnergyRegion σ τ ρ e)
    (k : ℕ) (hk : 1 ≤ k) :
    e / k ≤ heathBrownEnergyRHS σ (τ / k) (ρ / k) (e / k) :=
  h.heathBrown_powered k hk

-- The preserved obstruction is also a valid input to the repaired HB chain.
example : 0 ≤ heathBrownEnergyRHS (3 / 4) 1 0 0 := by
  have h : InCardinalityEnergyRegion (3 / 4) 2 0 0 :=
    ⟨2, energyPowering_source_counterexample.1⟩
  simpa using h.heathBrown_powered 2 (by norm_num)

-- Low-height and sigma endpoint coverage consumes actual source patterns.
example : 0 ≤ heathBrownEnergyRHS 1 0 0 0 :=
  (singleton_mem_largeValueEnergyRegion 1 0
    (by norm_num) (by norm_num) (by norm_num)).heathBrown_relation

example (σ ρ e s : ℝ) (h : InLargeValueEnergyRegion σ (3 / 2) ρ e s) :
    e ≤ max (max (3 * ρ + 1 - 2 * σ) (ρ + 4 - 4 * σ))
      (5 / 2 * ρ + (3 - 4 * σ) / 2) :=
  h.heathBrown_small_height le_rfl

example (W : Finset ℝ) : finsetAdditiveEnergy W =
    RiemannZeta.GuthMaynard.ApproxAddEnergy 1 W := finsetAdditiveEnergy_eq_native W

-- Classical cardinality powering consumes its own corrected witness.
example (σ τ ρ e : ℝ) (h : InCardinalityEnergyRegion σ τ ρ e)
    (k : ℕ) (hk : 1 ≤ k) :
    ρ / k ≤ max (2 - 2 * σ) (4 + τ / k - 6 * σ) :=
  h.huxley_cardinality_powered k hk

example (σ : ℝ) : classicalLargeValueExponent σ 0 = 2 - 2 * σ := by
  unfold classicalLargeValueExponent
  have := min_le_left (1 - 2 * σ) (4 - 6 * σ)
  rw [max_eq_left (by linarith)]

-- The compact interval and both sigma-piece endpoints use actual bounds.
example : IsLargeValueEnergyBound (3 / 4) 2 3 := by
  convert energyClauseOneGeneral_uniform_bound (σ := 3 / 4) (τ := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) using 1
  norm_num [energyClauseOneGeneralRate]

example : IsLargeValueEnergyBound (3 / 4) 4 6 := by
  convert energyClauseOneGeneral_uniform_bound (σ := 3 / 4) (τ := 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) using 1
  norm_num [energyClauseOneGeneralRate]

example : energyClauseOneGeneralRate (4 / 5) = 1 := by
  norm_num [energyClauseOneGeneralRate]

example : IsLargeValueEnergyBound (5 / 6) (16 / 3) (112 / 27) := by
  convert energyClauseOneGeneral_uniform_bound (σ := 5 / 6) (τ := 16 / 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) using 1
  norm_num [energyClauseOneGeneralRate]

example (σ τ ρ e s : ℝ) (h : InLargeValueEnergyRegion σ τ ρ e s)
    (hlo : 3 / 4 ≤ σ) (hhi : σ ≤ 4 / 5)
    (htlo : 8 * σ - 4 ≤ τ) (hthi : τ ≤ 2 * (8 * σ - 4)) :
    e / τ ≤ (18 - 19 * σ) / (2 * (3 * σ - 1)) :=
  h.energyClauseOneGeneral_lower_piece hlo hhi htlo hthi

-- Final assembly remains conditional only on the displayed zeta range;
-- endpoint one must not silently become the source's unproved endpoint two.
example (σ : ℝ) (hlo : 3 / 4 ≤ σ) (hhi : σ ≤ 5 / 6)
    (hZeta : ∀ τ ∈ Set.Ico (1 : ℝ) (8 * σ - 4),
      IsZetaLargeValueEnergyBound σ τ (energyClauseOnePublicRate σ * τ)) :
    IsZeroDensityEnergyBound σ (energyClauseOnePublicRate σ / (1 - σ)) :=
  energyClauseOne_of_zeta_range hlo hhi hZeta

-- Exact zeta-envelope endpoints and the rational crossover are certified.
example : energyClauseOneZetaRate (3 / 4) = 21 / 16 := by
  norm_num [energyClauseOneZetaRate]

example : energyClauseOneZetaRate (5 / 6) = 6 / 7 := by
  norm_num [energyClauseOneZetaRate]

example : energyClauseOneZetaRate (65 / 86) = 110 / 87 := by
  norm_num [energyClauseOneZetaRate]

-- Both low/high cardinality caps agree at the closed height transition.
example (σ : ℝ) : 2 * (4 * σ - 1) - 12 * (σ - 1 / 2) = 4 - 4 * σ := by
  ring

example (i : Fin 6) : heathBrownEnergyBranch (4 / 5) (11 / 5) (4 / 5) i ≤ 56 / 25 := by
  have h := energyClauseOneZeta_branch_bound (σ := 4 / 5) (t := 11 / 5) (r := 4 / 5)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) i
  norm_num [energyClauseOneZetaRate] at h
  exact h

-- Actual-region Huxley cap has no twelfth-moment premise.
example (ρ e s : ℝ) (h : InZetaLargeValueEnergyRegion (4 / 5) (12 / 5) ρ e s) :
    ρ ≤ 4 / 5 := by
  have hc := (show InCardinalityEnergyRegion (4 / 5) (12 / 5) ρ e from
    ⟨s, h.toGeneral⟩).energyClauseOneZeta_cardinality_cap (by norm_num)
  norm_num at hc
  exact hc

-- The closed upper source height is supported, but the LV premise stays visible.
example (hTwelfth : IsZetaLargeValueBound (5 / 6) (8 / 3) (4 / 3)) :
    IsZetaLargeValueEnergyBound (5 / 6) (8 / 3) (16 / 7) := by
  have h := energyClauseOneZeta_uniform_bound_of_twelfth (σ := 5 / 6) (τ := 8 / 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by convert hTwelfth using 1; norm_num)
  norm_num [energyClauseOneZetaRate] at h
  exact h

-- End-to-end assembly retains both unfinished analytic inputs literally.
example (σ : ℝ) (hlo : 3 / 4 ≤ σ) (hhi : σ ≤ 5 / 6)
    (hShort : ∀ τ ∈ Set.Ico (1 : ℝ) 2,
      IsZetaLargeValueEnergyBound σ τ (energyClauseOnePublicRate σ * τ))
    (hTwelfth : ∀ τ ∈ Set.Ico (2 : ℝ) (8 * σ - 4),
      IsZetaLargeValueBound σ τ (2 * τ - 12 * (σ - 1 / 2))) :
    IsZeroDensityEnergyBound σ (energyClauseOnePublicRate σ / (1 - σ)) :=
  energyClauseOne_of_twelfth_and_short_zeta hlo hhi hShort hTwelfth

-- The central kernel contribution and a separated neighboring point are retained.
example : zetaMomentKernel 0 0 = 1 := by norm_num [zetaMomentKernel]

example : (∑ t ∈ ({0, 1} : Finset ℝ), zetaMomentKernel t 0) = 3 / 2 := by
  norm_num [zetaMomentKernel]

-- Exact source-window mass, including the closed center and both endpoints.
example : (∫ u in (1 / 2 : ℝ)..3, zetaMomentKernel 1 u) =
    Real.log (3 / 2) + Real.log 3 := by
  convert integral_zetaMomentKernel (a := 1 / 2) (t := 1) (b := 3)
    (by norm_num) (by norm_num) using 1; norm_num

example (a x : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x) :
    12 * a ^ 11 * x ≤ x ^ 12 + 11 * a ^ 12 := twelfth_tangent_bound ha hx

-- The final analytic estimate is on the real zeta function, not a proxy.
example (T : ℝ) (W : Finset ℝ) (hT : 0 < T)
    (hSep : RiemannZeta.GuthMaynard.IsSeparated 1 W)
    (hW : ∀ t ∈ W, t ∈ Set.Icc T (2 * T)) :
    (∑ t ∈ W, (∫ u in T / 2..3 * T,
      (1 / (1 + |u - t|)) *
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * Complex.I)‖) ^ 12) ≤
      zetaMomentLogLoss T ^ 12 *
        ∫ u in T / 2..3 * T,
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * Complex.I)‖ ^ 12 :=
  sum_zetaMomentConvolution_twelfth W hT hSep hW

-- The modular entry premise remains visible; the later Perron consumer discharges it.
example (P : ZetaLargeValuePattern) (C : ℝ) (hC : 0 < C)
    (hEntry : ∀ t ∈ P.ordinates,
      P.V ≤ C * Real.sqrt P.N * zetaMomentConvolution P.T t) :
    (P.ordinates.card : ℝ) * P.V ^ 12 ≤
      C ^ 12 * P.N ^ 6 * zetaMomentLogLoss P.T ^ 12 * zetaTwelfthMoment P.T :=
  P.twelfth_cardinality_of_convolution hC hEntry

example :
    (RationalAffineFraction.mk 270 (-173) 125 (-93)).normalizeSign.eval
        (173 / 229 : ℝ) =
      (RationalAffineFraction.mk 270 (-173) 125 (-93)).eval
        (173 / 229 : ℝ) :=
  RationalAffineFraction.eval_normalizeSign _ _

-- Every fixed logarithmic loss, including the zeroth power, has a uniform threshold.
example (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in Filter.atTop, zetaMomentLogLoss T ^ n ≤ T ^ ε :=
  eventually_zetaMomentLogLoss_pow_le_rpow n hε

-- Source-window enlargement keeps the actual critical-line moment integrals.
example (T : ℝ) (hT : 0 < T) :
    zetaTwelfthMoment T ≤
      (∫ u in T / 2..T, zetaMomentCriticalNorm u ^ 12) +
      (∫ u in T..2 * T, zetaMomentCriticalNorm u ^ 12) +
      (∫ u in 2 * T..4 * T, zetaMomentCriticalNorm u ^ 12) :=
  zetaTwelfthMoment_le_three_dyadic hT

-- Dyadic normalization still exposes the genuine, unproved analytic input.
example
    (hDyadic : ∀ η : ℝ, 0 < η → ∃ C T₀ : ℝ, 0 ≤ C ∧
      ∀ H : ℝ, T₀ ≤ H → 0 < H →
        (∫ u in H..2 * H, zetaMomentCriticalNorm u ^ 12) ≤ C * H ^ (2 + η))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in Filter.atTop,
      zetaMomentLogLoss T ^ 12 * zetaTwelfthMoment T ≤ T ^ (2 + ε) :=
  eventually_zetaMomentLoss_twelfth_of_dyadic hDyadic hε

-- Uniform physical-height consumption of both explicit analytic inputs.
example
    (hDyadic : ∀ η : ℝ, 0 < η → ∃ C T₀ : ℝ, 0 ≤ C ∧
      ∀ H : ℝ, T₀ ≤ H → 0 < H →
        (∫ u in H..2 * H, zetaMomentCriticalNorm u ^ 12) ≤ C * H ^ (2 + η))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ P : ZetaLargeValuePattern, T₀ ≤ P.T →
      ∀ C : ℝ, 0 < C →
        (∀ t ∈ P.ordinates, P.V ≤ C * Real.sqrt P.N * zetaMomentConvolution P.T t) →
        (P.ordinates.card : ℝ) * P.V ^ 12 ≤ C ^ 12 * P.N ^ 6 * P.T ^ (2 + ε) :=
  zetaPattern_twelfth_cardinality_of_dyadic_and_convolution hDyadic hε

-- Integer endpoints are retained exactly, including a singleton interval.
example : zetaIntervalCutoff 3 7 3 = 1 :=
  zetaIntervalCutoff_eq_one (by norm_num) (by norm_num)

example : zetaIntervalCutoff 3 7 7 = 1 :=
  zetaIntervalCutoff_eq_one (by norm_num) (by norm_num)

example : zetaIntervalCutoff 3 3 3 = 1 :=
  zetaIntervalCutoff_eq_one (by norm_num) (by norm_num)

-- The outer half-integer endpoints vanish, not the integer endpoints.
example : zetaIntervalCutoff 3 7 (5 / 2) = 0 :=
  zetaIntervalCutoff_eq_zero_left (by norm_num)

example : zetaIntervalCutoff 3 7 (15 / 2) = 0 :=
  zetaIntervalCutoff_eq_zero_right (by norm_num)

example (n : ℕ) : zetaIntervalCutoff 4 3 n = 0 := by
  rw [zetaIntervalCutoff_nat]
  have hn : n ∉ Finset.Icc 4 3 := by simp
  simp only [hn, ↓reduceIte]

-- No endpoint or sign correction is hidden in the source polynomial.
example (P : ZetaLargeValuePattern) {a b : ℕ}
    (hactive : P.active = Finset.Icc a b) (t : ℝ) :
    (∑ n ∈ P.indices, P.coeff n * dirichletPhase n t) =
      ∑' n : ℕ, (zetaIntervalCutoff a b n : ℂ) * dirichletPhase n t :=
  P.polynomial_eq_cutoff_tsum hactive t

-- Physical support is derived from the actual nonempty large-value set.
example (P : ZetaLargeValuePattern) {a b : ℕ}
    (hactive : P.active = Finset.Icc a b) {t : ℝ} (ht : t ∈ P.ordinates) :
    Function.support (zetaIntervalCutoff a b) ⊆ Set.Icc (P.N / 2) (3 * P.N) :=
  P.cutoff_support_in_scale hactive (P.active_nonempty_of_mem_ordinates ht)

-- The moving pole has the negative ordinate, and its residue is retained.
example (g : ℝ → ℂ) (t : ℝ) :
    zetaMellinNumerator g t (1 - (t : ℂ) * Complex.I) =
      mellin g (1 - (t : ℂ) * Complex.I) :=
  zetaMellinNumerator_at_pole g t

-- The actual sharp polynomial equals the whole critical integral PLUS residue.
-- The localized norm estimate is checked separately below, with physical hypotheses.
example (P : ZetaLargeValuePattern) {a b : ℕ}
    (hactive : P.active = Finset.Icc a b) (t : ℝ) :
    (∑ n ∈ P.indices, P.coeff n * dirichletPhase n t) =
      mellin (fun x => (zetaIntervalCutoff a b x : ℂ)) (1 - (t : ℂ) * Complex.I) +
        (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ,
          riemannZeta (((1 / 2 : ℝ) : ℂ) + ((u + t : ℝ) : ℂ) * Complex.I) *
            mellin (fun x => (zetaIntervalCutoff a b x : ℂ))
              (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * Complex.I) :=
  P.polynomial_eq_critical_zeta_mellin hactive t

-- Every positive derivative order has one endpoint-independent mass bound.
example (a b j : ℕ) (hab : a ≤ b) (hj : 0 < j) :
    (∫ x : ℝ, ‖iteratedDeriv j (zetaIntervalCutoff a b) x‖) ≤ zetaCutoffDerivativeMass j :=
  integral_norm_iteratedDeriv_zetaIntervalCutoff_le hab hj

-- The flat interior of the actual sharp-interval interpolation has zero derivative.
example : deriv (zetaIntervalCutoff 2 4) 3 = 0 := by
  have heq : zetaIntervalCutoff 2 4 =ᶠ[nhds (3 : ℝ)] fun _ => (1 : ℝ) := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (2 : ℝ) < 3) (by norm_num : (3 : ℝ) < 4)] with x hx
    exact zetaIntervalCutoff_eq_one hx.1.le hx.2.le
  rw [heq.deriv_eq, deriv_const]

example (a b : ℕ) (hab : a ≤ b) :
    (∫ x : ℝ, ‖iteratedDeriv 4 (fun y => (zetaIntervalCutoff a b y : ℂ)) x‖) ≤
      zetaCutoffDerivativeMass 4 :=
  integral_norm_complex_cutoff_deriv_le hab (by norm_num)

-- Exact physical square-root normalization, including frequency zero.
example (P : ZetaLargeValuePattern) {a b : ℕ}
    (hactive : P.active = Finset.Icc a b) (hne : P.active.Nonempty) (u : ℝ) :
    ‖mellin (fun x => (zetaIntervalCutoff a b x : ℂ))
      (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * Complex.I)‖ ≤
        zetaCutoffMellinConstant 1 (1 / 2) * Real.sqrt P.N / (1 + |u|) :=
  P.cutoff_critical_mellin_kernel hactive hne u

-- The residue is bounded, not silently removed even at ordinate zero.
example (P : ZetaLargeValuePattern) {a b : ℕ}
    (hactive : P.active = Finset.Icc a b) (hne : P.active.Nonempty) :
    ‖mellin (fun x => (zetaIntervalCutoff a b x : ℂ)) 1‖ ≤
      zetaCutoffMellinConstant 4 1 * P.N ^ 4 := by
  simpa using P.cutoff_mellin_residue_bound hactive hne (j := 4) (by norm_num) 0

-- Both closed source height endpoints translate to the correct Mellin window.
example (T : ℝ) : zetaMellinSourceWindow T T = Set.Icc (-T / 2) (2 * T) := by
  unfold zetaMellinSourceWindow
  congr 1 <;> ring

example (T : ℝ) : zetaMellinSourceWindow T (2 * T) = Set.Icc (-3 * T / 2) T := by
  unfold zetaMellinSourceWindow
  congr 1 <;> ring

example (P : ZetaLargeValuePattern) {a b : ℕ}
    (hactive : P.active = Finset.Icc a b) (hne : P.active.Nonempty)
    {t : ℝ} (ht : t ∈ Set.Icc P.T (2 * P.T)) :
    ‖∫ u : ℝ in (zetaMellinSourceWindow P.T t)ᶜ, zetaCutoffCriticalIntegrand a b t u‖ ≤
      120 * zetaCutoffMellinConstant 4 (1 / 2) * P.N ^ (7 / 2 : ℝ) / P.T ^ 2 :=
  P.cutoff_critical_far_integral hactive hne ht

-- No supplied pointwise analytic estimate remains in this actual-pattern consumer.
example (P : ZetaLargeValuePattern) (hscale : P.N ^ (7 / 4 : ℝ) ≤ P.T)
    (hvalue : 2 * zetaPerronError ≤ P.V) {t : ℝ} (ht : t ∈ P.ordinates) :
    P.V ≤ zetaPerronConstant * Real.sqrt P.N * zetaMomentConvolution P.T t :=
  P.perron_entry hscale hvalue ht

example (P : ZetaLargeValuePattern) (hscale : P.N ^ (7 / 4 : ℝ) ≤ P.T)
    (hvalue : 2 * zetaPerronError ≤ P.V) :
    (P.ordinates.card : ℝ) * P.V ^ 12 ≤
      zetaPerronConstant ^ 12 * P.N ^ 6 * zetaMomentLogLoss P.T ^ 12 * zetaTwelfthMoment P.T :=
  P.twelfth_cardinality_of_perron hscale hvalue

-- Closed sigma=1/2, tau=2 and delta=1/4 are covered by a common threshold.
example : ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ P : ZetaLargeValuePattern, N₀ ≤ P.N →
    P.N ^ (7 / 4 : ℝ) ≤ P.T → P.N ^ (1 / 4 : ℝ) ≤ P.V →
      ∀ t ∈ P.ordinates,
        P.V ≤ zetaPerronConstant * Real.sqrt P.N * zetaMomentConvolution P.T t := by
  obtain ⟨N₀, hN₀, h⟩ := exists_zetaPerron_uniform_threshold
  refine ⟨N₀, hN₀, ?_⟩
  intro P hN hT hV
  have hentry := h P hN (1 / 2) 2 (1 / 4) (by norm_num) le_rfl le_rfl
  norm_num at hentry
  exact hentry hT hV

-- The genuine dyadic moment is now the only analytic input to the uniform LV bound.
example
    (hDyadic : ∀ η : ℝ, 0 < η → ∃ C T₀ : ℝ, 0 ≤ C ∧
      ∀ H : ℝ, T₀ ≤ H → 0 < H →
        (∫ u in H..2 * H, zetaMomentCriticalNorm u ^ 12) ≤ C * H ^ (2 + η)) :
    IsZetaLargeValueBound (5 / 6) (8 / 3) (4 / 3) := by
  convert zetaTwelfth_largeValueBound_of_dyadic hDyadic
    (σ := 5 / 6) (τ := 8 / 3) (by norm_num) (by norm_num) using 1
  norm_num

example
    (hDyadic : ∀ η : ℝ, 0 < η → ∃ C T₀ : ℝ, 0 ≤ C ∧
      ∀ H : ℝ, T₀ ≤ H → 0 < H →
        (∫ u in H..2 * H, zetaMomentCriticalNorm u ^ 12) ≤ C * H ^ (2 + η)) :
    IsZetaLargeValueEnergyBound (5 / 6) (8 / 3) (16 / 7) := by
  have h := energyClauseOneZeta_uniform_bound_of_twelfth (σ := 5 / 6) (τ := 8 / 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (zetaTwelfth_largeValueBound_of_dyadic hDyadic (by norm_num) (by norm_num))
  norm_num [energyClauseOneZetaRate] at h
  exact h

-- The preserved modular interface exposes both inputs; the later consumer derives short zeta.
example
    (hDyadic : ∀ η : ℝ, 0 < η → ∃ C T₀ : ℝ, 0 ≤ C ∧
      ∀ H : ℝ, T₀ ≤ H → 0 < H →
        (∫ u in H..2 * H, zetaMomentCriticalNorm u ^ 12) ≤ C * H ^ (2 + η))
    {σ : ℝ} (hlo : 3 / 4 ≤ σ) (hhi : σ ≤ 5 / 6)
    (hShort : ∀ τ ∈ Set.Ico (1 : ℝ) 2,
      IsZetaLargeValueEnergyBound σ τ (energyClauseOnePublicRate σ * τ)) :
    IsZeroDensityEnergyBound σ (energyClauseOnePublicRate σ / (1 - σ)) :=
  energyClauseOne_of_dyadic_moment_and_short_zeta hDyadic hlo hhi hShort

-- Threshold-relative absorption keeps the actual error scale visible.
example (P : ZetaLargeValuePattern) (hscale : P.N ^ (23 / 16 : ℝ) ≤ P.T)
    (hvalue : 2 * zetaPerronError * P.N ^ (5 / 8 : ℝ) ≤ P.V)
    {t : ℝ} (ht : t ∈ P.ordinates) :
    P.V ≤ zetaPerronConstant * Real.sqrt P.N * zetaMomentConvolution P.T t :=
  P.perron_entry_with_scaled_error hscale hvalue ht

-- Closed sigma=3/4, tau=3/2, delta=1/16 windows have a common threshold.
example : ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ P : ZetaLargeValuePattern, N₀ ≤ P.N →
    P.N ^ (23 / 16 : ℝ) ≤ P.T → P.N ^ (11 / 16 : ℝ) ≤ P.V →
      ∀ t ∈ P.ordinates,
        P.V ≤ zetaPerronConstant * Real.sqrt P.N * zetaMomentConvolution P.T t := by
  obtain ⟨N₀, hN₀, h⟩ := exists_zetaPerron_short_uniform_threshold
  refine ⟨N₀, hN₀, ?_⟩
  intro P hN hT hV
  have hentry := h P hN (3 / 4) (3 / 2) (1 / 16) le_rfl le_rfl le_rfl
  norm_num at hentry
  exact hentry hT hV

-- The transition between first- and second-derivative ranges is included.
example (P : ZetaLargeValuePattern) :
    ‖∑ n ∈ P.indices, P.coeff n * dirichletPhase n P.N‖ ≤
      2 + 200 * Real.sqrt P.N + 12 * Real.pi := by
  have h := P.polynomial_norm_le_short_majorant P.one_lt_N.le
    (show P.N ≤ P.N ^ 2 by nlinarith [P.one_lt_N])
  simpa only [mul_div_cancel_right₀ _ (zero_lt_one.trans P.one_lt_N).ne'] using h

-- Genuine cancellation gives minus infinity at the closed lower source height.
example : zetaLargeValueExponent (3 / 4) 1 = ⊥ :=
  zetaShort_largeValueExponent_eq_bot le_rfl le_rfl (by norm_num)

-- The short-height twelfth-moment bridge includes its boundary exponent zero.
example
    (hDyadic : ∀ η : ℝ, 0 < η → ∃ C T₀ : ℝ, 0 ≤ C ∧
      ∀ H : ℝ, T₀ ≤ H → 0 < H →
        (∫ u in H..2 * H, zetaMomentCriticalNorm u ^ 12) ≤ C * H ^ (2 + η)) :
    IsZetaLargeValueBound (3 / 4) (3 / 2) 0 := by
  convert zetaTwelfth_short_largeValueBound_of_dyadic hDyadic
    (σ := 3 / 4) (τ := 3 / 2) le_rfl le_rfl using 1
  norm_num

example : energyClauseOnePublicRate (3 / 4) * 2 = 3 := by
  norm_num [energyClauseOnePublicRate]

-- No separate short-zeta premise remains, including the upper sigma endpoint.
example
    (hDyadic : ∀ η : ℝ, 0 < η → ∃ C T₀ : ℝ, 0 ≤ C ∧
      ∀ H : ℝ, T₀ ≤ H → 0 < H →
        (∫ u in H..2 * H, zetaMomentCriticalNorm u ^ 12) ≤ C * H ^ (2 + η)) :
    IsZeroDensityEnergyBound (5 / 6) (36 / 7) := by
  convert energyClauseOne_of_dyadic_moment hDyadic
    (σ := 5 / 6) (by norm_num) le_rfl using 1
  norm_num [energyClauseOnePublicRate]

example
    (hDyadic : ∀ η : ℝ, 0 < η → ∃ C T₀ : ℝ, 0 ≤ C ∧
      ∀ H : ℝ, T₀ ≤ H → 0 < H →
        (∫ u in H..2 * H, zetaMomentCriticalNorm u ^ 12) ≤ C * H ^ (2 + η))
    {σ : ℝ} (hlo : 3 / 4 ≤ σ) (hhi : σ ≤ 5 / 6) :
    IsZeroDensityEnergyBound σ (energyClauseOnePublicRate σ / (1 - σ)) :=
  energyClauseOne_of_dyadic_moment hDyadic hlo hhi

-- Infimum semantics recover the exact uniform statement, including exponent zero.
example (σ τ : ℝ) :
    zetaLargeValueExponent σ τ ≤ 0 ↔ IsZetaLargeValueBound σ τ 0 :=
  zetaLargeValueExponent_le_iff

-- Negative rates collapse through actual finite cardinalities, for every target rate.
example {σ τ : ℝ} (h : IsZetaLargeValueBound σ τ (-1 / 10)) :
    IsZetaLargeValueBound σ τ (-100) :=
  h.any_of_neg (by norm_num) (-100)

example (σ τ : ℝ) :
    zetaLargeValueExponent σ τ = ⊥ ↔ zetaLargeValueExponent σ τ < 0 :=
  zetaLargeValueExponent_eq_bot_iff_neg σ τ

-- Negative branch: the maximum is -1, but discreteness gives the stronger -2.
example {σ τ : ℝ} (h : zetaLargeValueExponent σ τ ≤ (-1 : ℝ)) :
    zetaLargeValueExponent σ τ ≤ (-2 : ℝ) := by
  have hm : zetaLargeValueExponent σ τ ≤ ((max (-1) (2 * (-1)) : ℝ) : EReal) := by
    norm_num
    exact h
  simpa using zetaLargeValueExponent_le_double_of_le_max hm

-- The same numerical implication would be false for unrestricted real numbers.
example : ¬ ((-1 : ℝ) ≤ 2 * (-1)) := by norm_num

-- Zero is not treated as negative infinity at the maximum's branch boundary.
example : (0 : EReal) ≤ ((max (0 : ℝ) (2 * 0) : ℝ) : EReal) ∧ (0 : EReal) ≠ ⊥ := by
  norm_num

example {σ τ : ℝ} (h : zetaLargeValueExponent σ τ ≤ (2 : ℝ)) :
    zetaLargeValueExponent σ τ ≤ ((2 * (1 : ℝ) : ℝ) : EReal) := by
  apply zetaLargeValueExponent_le_double_of_le_max
  simpa using h

-- Unconditional actual sharp-interval consumer at the closed short-height endpoint.
example : ∃ C δ : ℝ, 1 ≤ C ∧ 0 < δ ∧ ∀ (N : ℕ) (I : Finset ℕ) (t : ℝ),
    C ≤ (N : ℝ) → IsIntegerInterval I → I ⊆ Finset.Icc N (2 * N) →
    (N : ℝ) ^ (1 - δ) ≤ t → t ≤ (N : ℝ) ^ (1 + δ) →
    ‖∑ n ∈ I, dirichletPhase n t‖ < (N : ℝ) ^ (3 / 4 - δ) :=
  zetaShort_pointwise_powerSaving le_rfl le_rfl (by norm_num)

-- The one-sided square remains nonsingular at central height zero.
example : zetaSquarePoleNormalization 0 = (1 / 16 : ℂ) := by
  norm_num [zetaSquarePoleNormalization_eq]

example (t : ℝ) : zetaSquareGammaNormalization (-t) = zetaSquareGammaNormalization t :=
  zetaSquareGammaNormalization_neg t

-- Actual ordinary-divisor coefficients, including the empty zero term.
example (t u : ℝ) : zetaSquareDivisorTerm t 0 u = 0 := by
  simp [zetaSquareDivisorTerm, divisorDirichletTerm, LSeries.term]

example (t u : ℝ) : zetaSquareDivisorTerm t 1 u = zetaSquareRightKernel t u := by
  simp [zetaSquareDivisorTerm, divisorDirichletTerm, LSeries.term]

-- One Gaussian constant works for all central and contour heights.
example : ∃ C : ℝ, 0 < C ∧ ∀ t u : ℝ,
    ‖zetaSquareRightKernel t u‖ ≤
      C * Real.exp (100 - 100 * u ^ 2) * (3 + |t| + |u|) ^ 12 :=
  exists_zetaSquareRightKernel_uniform_gaussian_bound

example (t : ℝ) :
    Summable (fun n : ℕ => ∫ u : ℝ, ‖zetaSquareDivisorTerm t n u‖) :=
  summable_integral_norm_zetaSquareDivisorTerm t

-- Source entry has no analytic input or positive-height exclusion.
example : HasSum (zetaSquareNormalizedContribution 0)
    ((zetaMomentCriticalNorm 0 ^ 2 : ℝ) : ℂ) :=
  hasSum_zetaSquareNormalizedContribution 0

-- The local second-moment identity uses actual zeta, with a convergent series.
example {T G : ℝ} (hG : 0 ≤ G) :
    HasSum (fun n : ℕ => ∫ t in T - G..T + G, zetaSquareNormalizedContribution t n)
      ((∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2 : ℝ) : ℂ) :=
  hasSum_zetaSquareLocalMean (by linarith)

example (T : ℝ) :
    (∫ t in T..T, zetaMomentCriticalNorm t ^ 2) =
      (∑' n : ℕ, ∫ t in T..T, zetaSquareNormalizedContribution t n).re :=
  zetaSquareLocalMean_eq_divisor_series le_rfl

-- The physical Gaussian is centered at T, without an unintended 1/G factor.
example (T G : ℝ) : zetaGaussianWeight T G T = 1 := by simp [zetaGaussianWeight]

example (T : ℝ) {G : ℝ} (hG : 0 < G) :
    1 ≤ Real.exp 1 * zetaGaussianWeight T G (T + G) :=
  zetaGaussianWeight_local_lower hG ⟨by linarith, le_rfl⟩

-- Weighted convergence is not restricted to positive test functions.
example {a b : ℝ} (hab : a ≤ b) :
    HasSum (fun n : ℕ => ∫ t in a..b, ((-1 : ℝ) : ℂ) * zetaSquareNormalizedContribution t n)
      ((∫ t in a..b, (-1 : ℝ) * zetaMomentCriticalNorm t ^ 2 : ℝ) : ℂ) :=
  hasSum_zetaSquareWeightedLocalMean _ continuous_const hab

example {T G : ℝ} (hG : 0 < G) :
    (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
      Real.exp 1 * zetaSquareGaussianWindow T G 1 :=
  zetaSquareLocalMean_le_gaussian_window hG le_rfl

example (T : ℝ) {G : ℝ} (hG : 0 < G) :
    zetaSquareGaussianMean T G =
      ∫ t : ℝ, zetaGaussianWeight T G t * zetaMomentCriticalNorm t ^ 2 :=
  zetaSquareGaussianMean_eq_physical T hG

-- The same threshold works for all positive widths up to T.
example : ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T G : ℝ, T₀ ≤ T → 0 < G → G ≤ T →
    0 ≤ zetaSquareGaussianMean T G - zetaSquareGaussianWindow T G (Real.log T) ∧
    zetaSquareGaussianMean T G - zetaSquareGaussianWindow T G (Real.log T) ≤ G * T ^ (-10 : ℝ) :=
  exists_zetaSquareGaussian_log_tail_bound 10

-- Quadratic transform includes zero frequency and the closed G^2=2T boundary.
example : ‖zetaGaussianQuadraticIntegral 2 2 0‖ ≤ Real.sqrt Real.pi * 2 := by
  simpa using norm_zetaGaussianQuadraticIntegral_le
    (T := 2) (G := 2) (by norm_num) (by norm_num) (by norm_num) 0

example : ‖zetaGaussianQuadraticIntegral 2 2 (-1)‖ ≤
    Real.sqrt Real.pi * 2 * Real.exp (-(2 : ℝ) ^ 2 / 8) :=
  norm_zetaGaussianQuadraticIntegral_tail (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

-- The negative quadratic phase retains the actual T-dependent imaginary part.
example : (zetaGaussianQuadraticCoefficient 2 2).im = 1 / 4 := by
  rw [zetaGaussianQuadraticCoefficient_im]
  norm_num

-- The actual digamma estimate includes both closed height boundaries.
section GammaPhaseRegression

open Complex MeasureTheory

example : ‖Complex.digamma (1 + I) - Complex.log (1 + I)‖ ≤ 4 := by
  simpa using norm_digamma_sub_log_le (z := 1 + I) (by norm_num) (by norm_num)

example : ‖Complex.digamma (1 - I) - Complex.log (1 - I)‖ ≤ 4 := by
  simpa using norm_digamma_sub_log_le (z := 1 - I) (by norm_num) (by norm_num)

example {z : ℂ} (hz : 0 < z.re) (hy : 1 ≤ |z.im|) :
    ‖(∑ n ∈ Finset.range 0, (z + n)⁻¹) -
      (Complex.log (z + (0 : ℕ)) - Complex.log z)‖ ≤ 4 / |z.im| :=
  norm_sum_reciprocal_sub_log_le hz hy 0

example : zetaSquareReflectedGammaPhase 0 = 1 := zetaSquareReflectedGammaPhase_zero

-- Genuine functional-equation source, not an independent unit-phase parameter.
example (t : ℝ) : zetaSquareReflectedGammaPhase t *
    riemannZeta (afeCriticalPoint (-t)) = riemannZeta (afeCriticalPoint t) :=
  zetaSquareReflectedGammaPhase_mul_zeta t

example : |zetaSquareGammaFrequency 2 + Real.log (2 / (2 * Real.pi))| ≤ 9 / 2 :=
  abs_zetaSquareGammaFrequency_add_log_le le_rfl

-- The negative endpoint is included at the smallest permitted central height.
example : ‖zetaSquareReflectedGammaPhase (4 + (-2 : ℝ)) -
    zetaSquareReflectedGammaPhase 4 * Complex.exp (-I * (zetaSquareGammaQuadraticAngle 4 (-2) : ℂ))‖ ≤
    (18 / 4 + 2 * (2 : ℝ) ^ 2 / 4 ^ 2) * |(-2 : ℝ)| :=
  norm_zetaSquareReflectedGammaPhase_sub_quadratic_le
    (r := 2) (by norm_num) (by norm_num) (by norm_num)

example : ‖zetaSquareReflectedGammaPhase (4 + (2 : ℝ)) -
    zetaSquareReflectedGammaPhase 4 * Complex.exp (-I * (zetaSquareGammaQuadraticAngle 4 2 : ℂ))‖ ≤
    (18 / 4 + 2 * (2 : ℝ) ^ 2 / 4 ^ 2) * |(2 : ℝ)| :=
  norm_zetaSquareReflectedGammaPhase_sub_quadratic_le
    (r := 2) (by norm_num) (by norm_num) (by norm_num)

example (T G v : ℝ) :
    Complex.exp (-I * (zetaSquareGammaQuadraticAngle T 0 : ℂ)) *
      Complex.exp (I * (v : ℂ) * (0 : ℂ)) * ((Real.exp (-(0 / G) ^ 2) : ℝ) : ℂ) =
      Complex.exp (I * ((v - Real.log (T / (2 * Real.pi)) : ℝ) : ℂ) * (0 : ℂ)) *
        Complex.exp (-zetaGaussianQuadraticCoefficient T G * (0 : ℂ) ^ 2) :=
  zetaSquareGammaQuadratic_gaussian_identity T G v 0

example : Integrable (zetaSquareGammaGaussianIntegrand 4 2 (-1)) :=
  integrable_zetaSquareGammaGaussianIntegrand 4 (-1) (by norm_num)

-- Tail bound includes radius zero and retains the physical width.
example {G : ℝ} (hG : 0 < G) :
    (∫ x in (Set.Ioc (0 : ℝ) 0)ᶜ, Real.exp (-(x / G) ^ 2)) ≤ Real.sqrt (2 * Real.pi) * G := by
  simpa using physical_gaussian_tail_le (r := 0) hG le_rfl

-- The complete true-phase transform consumes quadratic damping, not just its formula.
example : ‖zetaSquareGammaGaussianTransform 4 2 (-1)‖ ≤
    Real.sqrt Real.pi * 2 * Real.exp (-(2 * ((-1 : ℝ) - Real.log (4 / (2 * Real.pi)))) ^ 2 / 8) +
    2 * (2 : ℝ) ^ 2 * (18 / 4 + 2 * 2 ^ 2 / 4 ^ 2) +
      2 * Real.sqrt (2 * Real.pi) * 2 * Real.exp (-(2 / 2 : ℝ) ^ 2 / 2) :=
  norm_zetaSquareGammaGaussianTransform_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (-1)

end GammaPhaseRegression

section GammaAmplitudeRegression

open Complex MeasureTheory

example (t : ℝ) (w : ℂ) : zetaGammaShiftAmplitude t w 0 = 1 :=
  zetaGammaShiftAmplitude_zero t w

example : Complex.log (-(2 : ℂ) * I) = zetaGammaLeadingLog 4 + Complex.log (Real.pi : ℂ) := by
  convert log_negative_height_eq (t := 4) (by norm_num) using 1
  norm_num

-- The closed shift boundary and the path endpoint are both included.
example : ‖Complex.digamma (zetaGammaHalfShift 4 (2 * I) 1) -
    (zetaGammaLeadingLog 4 + Complex.log (Real.pi : ℂ))‖ ≤ 21 / 4 := by
  convert norm_zetaGammaHalfShift_digamma_sub_le (t := 4) (w := 2 * I)
    (v := 1) (by norm_num) (by norm_num) (by norm_num) (by constructor <;> norm_num)
    using 1
  norm_num

example : ‖Complex.digamma (zetaGammaHalfShift 4 (-2 * I) 1) -
    (zetaGammaLeadingLog 4 + Complex.log (Real.pi : ℂ))‖ ≤ 21 / 4 := by
  convert norm_zetaGammaHalfShift_digamma_sub_le (t := 4) (w := -2 * I)
    (v := 1) (by norm_num) (by norm_num) (by norm_num) (by constructor <;> norm_num)
    using 1
  norm_num

-- The signed contour growth is not replaced by a symmetric phase.
example (t : ℝ) : ((1 + I) * zetaGammaLeadingLog t).re =
    Real.log (t / (2 * Real.pi)) + Real.pi / 2 := by
  simpa using zetaGammaLeadingLog_mul_re t (1 + I)

example (t : ℝ) : ((1 - I) * zetaGammaLeadingLog t).re =
    Real.log (t / (2 * Real.pi)) - Real.pi / 2 := by
  simpa [sub_eq_add_neg] using zetaGammaLeadingLog_mul_re t (1 - I)

example (t : ℝ) : zetaSquarePoleShift t 0 = 1 := by
  have hne : afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t)) ≠ 0 := by
    rw [criticalPoint_pole_product]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
  simp only [zetaSquarePoleShift, add_zero, div_self hne, one_pow]

example : ‖zetaSquareRightKernel (-4) 1 / zetaSquareGammaNormalization 4 -
    zetaSquareLeadingRightKernel 4 1‖ ≤
    114375 * Real.exp 120 * Real.exp (-90 * (1 : ℝ) ^ 2) * (1 + |(1 : ℝ)|) ^ 10 :=
  norm_zetaSquareRightKernel_sub_leading_near_le (by norm_num) (by norm_num)

example : ‖zetaSquareRightKernel (-4) (-1) / zetaSquareGammaNormalization 4 -
    zetaSquareLeadingRightKernel 4 (-1)‖ ≤
    114375 * Real.exp 120 * Real.exp (-90 * (-1 : ℝ) ^ 2) * (1 + |(-1 : ℝ)|) ^ 10 :=
  norm_zetaSquareRightKernel_sub_leading_near_le (by norm_num) (by norm_num)

-- The inverse bound covers height zero as well as arbitrarily large heights.
example : ∃ C : ℝ, 0 < C ∧ ‖(zetaSquareGammaNormalization 0)⁻¹‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_inv_zetaSquareGammaNormalization_le
  exact ⟨C, hC, by simpa using hbound 0⟩

example : Integrable (zetaSquareLeadingRightKernel 4) :=
  integrable_zetaSquareLeadingRightKernel le_rfl

example : HasSum (zetaSquareLeadingDivisorContribution 4) (zetaSquareLeadingDivisorIntegral 4) :=
  hasSum_zetaSquareLeadingDivisorContribution le_rfl

example (t u : ℝ) : ‖zetaSquareLeadingDivisorTerm t 0 u‖ = 0 := by
  rw [norm_zetaSquareLeadingDivisorTerm]
  simp [divisorDirichletTerm, LSeries.term]

-- One source remainder constant, not a separately chosen constant for each height.
example : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 4 ≤ t →
    ‖zetaSquareDivisorIntegral (-t) / zetaSquareGammaNormalization t -
      zetaSquareLeadingDivisorIntegral t‖ ≤ C :=
  exists_norm_zetaSquareDivisorIntegral_sub_leading_le

end GammaAmplitudeRegression

section DivisorWeightRegression

open Complex MeasureTheory
open scoped ComplexConjugate

example : zetaDivisorWeight 0 = 1 / 2 := zetaDivisorWeight_zero

example (q : ℂ) : zetaDivisorWeight q + zetaDivisorWeight (-q) = 1 :=
  zetaDivisorWeight_add_neg q

-- The logarithmic source argument retains its signed imaginary part,
-- even at the zero coefficient (whose Dirichlet term is separately zero).
example (T : ℝ) : (zetaDivisorWeightArgument T 0).im = Real.pi / 2 :=
  zetaDivisorWeightArgument_im T 0

example : Real.exp (-(zetaDivisorWeightArgument (2 * Real.pi) 1).re) = 1 := by
  rw [exp_neg_zetaDivisorWeightArgument_re (by positivity) (by norm_num)]
  field_simp
  norm_num

example : |Real.log (8 + (-4 : ℝ)) - Real.log 8| ≤ 2 * |(-4 : ℝ)| / 8 :=
  abs_log_height_shift_le (by norm_num) (by norm_num)

example : |Real.log (8 + (4 : ℝ)) - Real.log 8| ≤ 2 * |(4 : ℝ)| / 8 :=
  abs_log_height_shift_le (by norm_num) (by norm_num)

example : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → ∀ x : ℝ, |x| ≤ T / 2 →
    ∀ n : ℕ, 0 < n →
    ‖zetaDivisorWeight (zetaDivisorWeightArgument (T + x) n) -
      zetaDivisorWeight (zetaDivisorWeightArgument T n)‖ ≤
      C * (|x| / T) * min (T / (2 * Real.pi * (n : ℝ))) (2 * Real.pi * (n : ℝ) / T) :=
  exists_norm_source_zetaDivisorWeight_height_sub_le

example (t : ℝ) : Summable (fun n : ℕ => ‖divisorDirichletTerm (afeCriticalPoint t) n‖ *
    ‖zetaDivisorWeight (zetaDivisorWeightArgument 1 n)‖) :=
  summable_norm_source_divisor_weight (by norm_num) t

example : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ t : ℝ,
    (∑' n : ℕ, ‖divisorDirichletTerm (afeCriticalPoint t) n‖ *
      ‖zetaDivisorWeight (zetaDivisorWeightArgument T n)‖) ≤ C * T ^ (1 / 2 + (1 / 4 : ℝ)) :=
  exists_tsum_norm_source_divisor_weight_le (1 / 4) (by norm_num)

example (T : ℝ) (n : ℕ) : ‖zetaSquareLeadingDivisorContribution T n -
    zetaSquareFrozenDivisorContribution T 0 n‖ = 0 := by
  simpa only [add_zero, sub_self, norm_zero, mul_zero] using norm_zetaSquareDivisor_freezing_error T 0 n

-- Both closed half-height boundaries are covered by one constant.
example : ∃ C : ℝ, 0 < C ∧ ∀ x ∈ ({-4, 4} : Set ℝ),
    ‖zetaSquareLeadingDivisorIntegral (8 + x) - zetaSquareFrozenDivisorIntegral 8 x‖ ≤
      C * |x| * (8 : ℝ) ^ (-1 / 2 + (1 / 4 : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_zetaSquareLeadingDivisor_sub_frozen_le (1 / 4) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro x hx
  apply hbound 8 (by norm_num)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl <;> norm_num

example : HasSum (fun n : ℕ => zetaFrozenDivisorCoefficient 8 n *
    zetaSquareGammaGaussianTransform 8 4 (Real.log (n : ℝ))) (zetaFrozenDivisorGaussianMean 8 4) :=
  hasSum_zetaFrozenDivisorGaussianMean (by norm_num) (by norm_num)

example (T : ℝ) : zetaFrozenDivisorCoefficient T 0 = 0 := by
  simp [zetaFrozenDivisorCoefficient, divisorDirichletTerm, LSeries.term]

example (T x : ℝ) : zetaSquareFrozenDivisorContribution T x 1 =
    zetaFrozenDivisorCoefficient T 1 * zetaSquareReflectedGammaPhase (T + x) := by
  simpa using zetaSquareFrozenDivisorContribution_eq_phase T x 1

example : zetaMomentCriticalNorm 0 ^ 2 =
    2 * (zetaSquareDivisorIntegral 0 / zetaSquareGammaNormalization 0).re := by
  simpa using zetaSquareNorm_eq_reflected_source 0

example : zetaSquareRightKernel (-4) (-1) = conj (zetaSquareRightKernel 4 1) :=
  zetaSquareRightKernel_conj 4 1

example : zetaSquareGaussianWindow 8 4 1 =
    ∫ x in (-4 : ℝ)..4, Real.exp (-(x / 4) ^ 2) * zetaMomentCriticalNorm (8 + x) ^ 2 := by
  convert zetaSquareGaussianWindow_eq_height_shift 8 4 (G := 4) (by norm_num) using 1
  norm_num

example : Integrable (fun x : ℝ => zetaSquareFrozenDivisorIntegral 1 x *
    (Real.exp (-(x / 1) ^ 2) : ℂ)) :=
  integrable_zetaSquareFrozenDivisor_gaussian (by norm_num) (by norm_num)

-- The closed Gaussian scale boundary still uses the actual coefficient series.
example : Summable (fun n : ℕ => zetaFrozenDivisorCoefficient 8 n * zetaSquareReflectedGammaPhase 8 *
    zetaGaussianQuadraticIntegral 8 4 (Real.log (n : ℝ) - Real.log (8 / (2 * Real.pi)))) :=
  summable_zetaFrozenDivisorQuadraticTerm (by norm_num) (by norm_num) (by norm_num)

example (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G r : ℝ, 8 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      0 ≤ r → r ≤ T / 2 →
      |zetaSquareGaussianWindow T G (r / G) - 2 * (zetaFrozenDivisorQuadraticSum T G).re| ≤
        C * r * (1 + r * T ^ (-1 / 2 + ε)) +
          (∑' n : ℕ, ‖zetaFrozenDivisorCoefficient T n‖) *
            (4 * r ^ 2 * (18 / T + 2 * r ^ 2 / T ^ 2) +
              6 * Real.sqrt (2 * Real.pi) * G * Real.exp (-(r / G) ^ 2 / 2)) :=
  exists_abs_zetaSquareGaussianWindow_sub_quadratic_le ε hε

end DivisorWeightRegression

section ShortDivisorRegression

open Complex Filter MeasureTheory

example (T G L : ℝ) : 0 ∉ zetaQuadraticDivisorBand T G L :=
  zero_not_mem_zetaQuadraticDivisorBand T G L

-- Closed zero-frequency centre; no positive-width cutoff assumption.
example : 1 ∈ zetaQuadraticDivisorBand (2 * Real.pi) 1 0 := by
  rw [mem_zetaQuadraticDivisorBand_iff (by positivity) (by norm_num)]
  norm_num [Real.pi_ne_zero]

-- The upper and lower logarithmic band boundaries are included.
example : 2 ∈ zetaQuadraticDivisorBand (2 * Real.pi) 1 (Real.log 2) := by
  rw [mem_zetaQuadraticDivisorBand_iff (by positivity) (by norm_num)]
  norm_num [Real.pi_ne_zero, abs_of_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))]

example : 1 ∈ zetaQuadraticDivisorBand (4 * Real.pi) 1 (Real.log 2) := by
  have hc : 4 * Real.pi / (2 * Real.pi) = 2 := by
    field_simp
    norm_num
  rw [mem_zetaQuadraticDivisorBand_iff (by positivity) (by norm_num), hc]
  norm_num [abs_of_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))]

example (T : ℝ) : zetaFrozenDivisorCoefficient T 0 = 0 :=
  zetaFrozenDivisorCoefficient_zero T

example : ‖zetaFrozenDivisorQuadraticSum 8 4 - zetaShortQuadraticDivisorSum 8 4 0‖ ≤
    (∑' n : ℕ, ‖zetaFrozenDivisorCoefficient 8 n‖) * (Real.sqrt Real.pi * 4) := by
  simpa using norm_zetaFrozenDivisorQuadraticSum_sub_short_le
    (T := 8) (G := 4) (L := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T G : ℝ, T₀ ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
    ‖zetaFrozenDivisorQuadraticSum T G - zetaShortQuadraticDivisorSum T G (Real.log T)‖ ≤
      G * T ^ (-(3 : ℝ)) :=
  exists_zetaQuadraticDivisor_log_tail_bound 3

example : (2 : ℝ) ^ 2 ≤ 4 :=
  gaussian_width_sq_le_height (G := 2) (T := 4) (δ := 0) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [Real.rpow_div_two_eq_sqrt])

example : ∀ᶠ T : ℝ in atTop, 8 ≤ T ∧ 1 ≤ Real.log T ∧
    ∀ G : ℝ, 0 < G → G ≤ T ^ (1 / 2 - (1 / 4 : ℝ)) →
      G ^ 2 ≤ 2 * T ∧ G * Real.log T ≤ T / 2 ∧ G ≤ T :=
  eventually_zeta_source_log_window_scales (by norm_num)

example (T G δ : ℝ) (hT : 1 ≤ T) (hδ : 0 < δ) (hG : G ≤ T ^ (1 / 2 - δ))
    (hlog : 1 ≤ Real.log T) (hlog4 : (Real.log T) ^ 4 ≤ T ^ (δ / 2)) :
    G * (Real.log T) ^ 0 * T ^ (-1 / 2 + δ / 4) ≤ 1 :=
  source_log_monomial_le_one hT hδ hG hlog hlog4 (by norm_num)

example : ∀ᶠ T : ℝ in atTop, 4 * (Real.log T) ^ 4 ≤ T ^ (1 / 4 : ℝ) :=
  eventually_const_log_pow_le_rpow 4 (by norm_num) 4 (by norm_num)

example : Real.exp 1 - 1 ≤ 2 * (1 : ℝ) :=
  exp_sub_one_le_two_mul (by norm_num) le_rfl

example : ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T G : ℝ,
    T₀ ≤ T → 0 < G → G ≤ T ^ (1 / 2 - (1 / 4 : ℝ)) →
    |(∫ t : ℝ, zetaGaussianWeight T G t * zetaMomentCriticalNorm t ^ 2) -
      2 * (zetaShortQuadraticDivisorSum T G (Real.log T)).re| ≤ C * G * Real.log T :=
  exists_zetaSquarePhysicalGaussian_short_approximation (by norm_num)

example : ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T G : ℝ,
    T₀ ≤ T → 0 < G → G ≤ T ^ (1 / 2 - (1 / 4 : ℝ)) →
    (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
      2 * Real.exp 1 * (zetaShortQuadraticDivisorSum T G (Real.log T)).re + C * G * Real.log T :=
  exists_zetaSquareLocalMean_le_short_divisor (by norm_num)

example : ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T G : ℝ, T₀ ≤ T → T ^ (1 / 4 : ℝ) ≤ G →
    ∀ n ∈ zetaQuadraticDivisorBand T G (Real.log T),
      |(n : ℝ) - T / (2 * Real.pi)| ≤ T * Real.log T / (Real.pi * G) ∧
        T / (4 * Real.pi) ≤ (n : ℝ) ∧ (n : ℝ) ≤ T / Real.pi :=
  exists_zetaQuadraticDivisorBand_physical_bounds (by norm_num)

example (T G L : ℝ) : zetaShortQuadraticDivisorSum T G L =
    ∑ n ∈ zetaQuadraticDivisorBand T G L, divisorWeight n * zetaShortDivisorTestFunction T G n :=
  zetaShortQuadraticDivisorSum_eq_divisor_test T G L

example (T G : ℝ) : zetaFrozenDivisorCoefficient T 0 * zetaSquareReflectedGammaPhase T *
    zetaGaussianQuadraticIntegral T G (Real.log (0 : ℝ) - Real.log (T / (2 * Real.pi))) =
      divisorWeight 0 * zetaShortDivisorTestFunction T G 0 :=
  by simpa only [Nat.cast_zero] using zetaQuadraticDivisorTerm_eq_testFunction T G 0

-- A single tail constant is allowed to be negative; the uniform
-- Gaussian-power absorption remains true without a positivity postulate.
example : ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
    (-1 : ℝ) * T ^ (1 : ℝ) * Real.exp (-(1 / 8) * (Real.log T) ^ 2) ≤ T ^ (-(2 : ℝ)) :=
  exists_logGaussian_power_tail_bound (-1) 1 2 (by norm_num)

end ShortDivisorRegression

section SmoothVoronoiRegression

open Complex Filter MeasureTheory
open scoped ContDiff

-- Smoothness concerns the actual entire contour weight, including its
-- complex logarithmic argument rather than only the real axis.
example : ContDiff ℝ ∞ zetaDivisorWeight := contDiff_zetaDivisorWeight

example : DifferentiableAt ℂ zetaDivisorWeight (Complex.I * Real.pi / 2) :=
  differentiable_zetaDivisorWeight _

example : ContDiffAt ℝ ∞ (zetaShortDivisorTestFunction 8 4) 1 :=
  contDiffAt_zetaShortDivisorTestFunction 8 (by norm_num) (by norm_num)

-- Both ends of both smooth transitions have their exact values.
example : zetaBandCutoff 1 2 3 4 1 = 0 :=
  zetaBandCutoff_eq_zero_left (by norm_num) le_rfl

example : zetaBandCutoff 1 2 3 4 2 = 1 :=
  zetaBandCutoff_eq_one (by norm_num) (by norm_num) le_rfl (by norm_num)

example : zetaBandCutoff 1 2 3 4 3 = 1 :=
  zetaBandCutoff_eq_one (by norm_num) (by norm_num) (by norm_num) le_rfl

example : zetaBandCutoff 1 2 3 4 4 = 0 :=
  zetaBandCutoff_eq_zero_right (by norm_num) le_rfl

example : zetaSmoothDivisorTest 8 4 1 0 = 0 :=
  zetaSmoothDivisorTest_eq_zero_left (by norm_num) (by norm_num) (by norm_num)
    (zetaDivisorBandEdge_pos (by norm_num) 4 (-2 * 1)).le

example : ContDiff ℝ ∞ (zetaSmoothDivisorTest 8 4 1) :=
  contDiff_zetaSmoothDivisorTest (by norm_num) (by norm_num) (by norm_num)

noncomputable example : DFIVoronoiTestFunction (zetaSmoothDivisorTest 8 4 1) :=
  zetaSmoothDivisorVoronoiTest (by norm_num) (by norm_num) (by norm_num)

example : Summable (fun n : ℕ => divisorWeight n * zetaSmoothDivisorTest 8 4 1 n) :=
  summable_zetaSmoothDivisorTerm (by norm_num) (by norm_num) (by norm_num) 1

example : ‖zetaSmoothDivisorSum 8 4 1 - zetaShortQuadraticDivisorSum 8 4 1‖ ≤
    (∑' n : ℕ, ‖zetaFrozenDivisorCoefficient 8 n‖) *
      (Real.sqrt Real.pi * 4 * Real.exp (-(1 : ℝ) ^ 2 / 8)) :=
  norm_zetaSmoothDivisorSum_sub_short_le (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ T G : ℝ, T₀ ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
    ‖zetaSmoothDivisorSum T G (Real.log T) - zetaShortQuadraticDivisorSum T G (Real.log T)‖ ≤
      G * T ^ (-(3 : ℝ)) := exists_zetaSmoothDivisor_log_tail_bound 3

example : zetaSmoothDivisorSum 8 4 1 = zetaDivisorVoronoiMain 8 4 1 +
    zetaDivisorVoronoiMinus 8 4 1 + zetaDivisorVoronoiPlus 8 4 1 :=
  zetaSmoothDivisorSum_eq_voronoi (by norm_num) (by norm_num) (by norm_num)

example : zetaDivisorVoronoiMinus 8 4 1 = zetaDivisorBesselMinus 8 4 1 :=
  zetaDivisorVoronoiMinus_eq_bessel (by norm_num) (by norm_num) (by norm_num)

example : zetaDivisorVoronoiPlus 8 4 1 = zetaDivisorBesselPlus 8 4 1 :=
  zetaDivisorVoronoiPlus_eq_bessel (by norm_num) (by norm_num) (by norm_num)

example : ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T G : ℝ,
    T₀ ≤ T → 0 < G → G ≤ T ^ (1 / 2 - (1 / 4 : ℝ)) →
    |(∫ t : ℝ, zetaGaussianWeight T G t * zetaMomentCriticalNorm t ^ 2) -
      2 * (zetaDivisorVoronoiMain T G (Real.log T) + zetaDivisorBesselMinus T G (Real.log T) +
        zetaDivisorBesselPlus T G (Real.log T)).re| ≤ C * G * Real.log T :=
  exists_zetaSquarePhysicalGaussian_bessel_approximation (by norm_num)

example : ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T G : ℝ,
    T₀ ≤ T → 0 < G → G ≤ T ^ (1 / 2 - (1 / 4 : ℝ)) →
    (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
      2 * Real.exp 1 * (zetaDivisorVoronoiMain T G (Real.log T) +
        zetaDivisorBesselMinus T G (Real.log T) + zetaDivisorBesselPlus T G (Real.log T)).re +
          C * G * Real.log T := exists_zetaSquareLocalMean_le_bessel (by norm_num)

end SmoothVoronoiRegression

section BesselK0Regression

open Complex Filter MeasureTheory Set

example : |dfiBesselK0 2| ≤ 2 * Real.exp (-1) := by
  simpa using abs_dfiBesselK0_exp_le (x := 2) le_rfl

example : Real.exp (-(1 : ℝ)) ≤ 1 := by
  calc
    _ ≤ (Nat.factorial 0 : ℝ) / (1 : ℝ) ^ 0 := exp_neg_le_factorial_div_pow (by norm_num) 0
    _ = 1 := by norm_num

example : 0 < zetaBesselK0PowerConstant 0 := zetaBesselK0PowerConstant_pos 0

example : |dfiBesselK0 (4 * Real.pi)| ≤ zetaBesselK0PowerConstant 2 / (16 : ℝ) ^ 2 := by
  simpa using abs_dfiBesselK0_source_le (T := 16) (x := 1) (n := 1)
    (by norm_num) (by norm_num) (by norm_num) 2

example : (32 : ℝ) / (4 * Real.pi) ≤ zetaDivisorBandEdge 32 8 (-2 * 1) ∧
    zetaDivisorBandEdge 32 8 (2 * 1) ≤ 32 / Real.pi :=
  zetaDivisorBandEdge_outer_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num)

-- The complete smooth transitions, not just the retained integer band.
example : Function.support (zetaSmoothDivisorTest 32 8 1) ⊆ Icc 2 32 := by
  simpa only [show (32 : ℝ) / 16 = 2 by norm_num] using
    support_zetaSmoothDivisorTest_physical (T := 32) (G := 8) (L := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, ‖zetaSmoothDivisorTest 32 8 1 x‖ ≤ C * 8 := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_zetaSmoothDivisorTest_le
  exact ⟨C, hC, hbound 32 8 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩

example : Integrable (zetaBesselK0SourceIntegrand 32 8 1 1) :=
  integrable_zetaBesselK0SourceIntegrand (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : (∫ x : ℝ in Ioi 0, ‖zetaSmoothDivisorTest 32 8 1 x‖) =
    ∫ x : ℝ in Icc 2 32, ‖zetaSmoothDivisorTest 32 8 1 x‖ := by
  simpa only [show (32 : ℝ) / 16 = 2 by norm_num] using
    zetaSmoothDivisorTest_integral_norm_eq_physical (T := 32) (G := 8) (L := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example (T G L : ℝ) : zetaBesselK0SourceTerm T G L 0 = 0 := by
  simp [zetaBesselK0SourceTerm, divisorWeight]

example : ‖divisorDirichletTerm 2 0‖ = 0 := by
  simpa using norm_divisorDirichletTerm_two 0

-- Both the Gaussian-square and smooth-cutoff width boundaries are closed.
example : HasSum (zetaBesselK0SourceTerm 32 8 1) (zetaDivisorBesselPlus 32 8 1) :=
  hasSum_zetaBesselK0SourceTerm (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : (-1 : ℝ) * 4 / (4 : ℝ) ^ (2 : ℕ) ≤ (4 : ℝ) ^ (-(0 : ℝ)) :=
  besselK0_source_power_absorb (by norm_num) (by norm_num) (by norm_num)

example : ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ, T₀ ≤ T →
    T ^ (1 / 8 : ℝ) ≤ G → G ≤ T ^ (1 / 2 - (1 / 8 : ℝ)) →
    ‖zetaDivisorBesselPlus T G (Real.log T)‖ ≤ G * T ^ (-(3 : ℝ)) :=
  exists_zetaDivisorBesselPlus_powerSaving (by norm_num) 3

example : ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
    T₀ ≤ T → T ^ (1 / 8 : ℝ) ≤ G → G ≤ T ^ (1 / 2 - (1 / 8 : ℝ)) →
    |(∫ t : ℝ, zetaGaussianWeight T G t * zetaMomentCriticalNorm t ^ 2) -
      2 * (zetaDivisorVoronoiMain T G (Real.log T) +
        zetaDivisorBesselMinus T G (Real.log T)).re| ≤ C * G * Real.log T :=
  exists_zetaSquarePhysicalGaussian_main_minus_approximation (by norm_num)

example : ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
    T₀ ≤ T → T ^ (1 / 4 : ℝ) ≤ G → G ≤ T ^ (1 / 2 - (1 / 4 : ℝ)) →
    (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
      2 * Real.exp 1 * (zetaDivisorVoronoiMain T G (Real.log T) +
        zetaDivisorBesselMinus T G (Real.log T)).re + C * G * Real.log T :=
  exists_zetaSquareLocalMean_le_main_minus (by norm_num)

end BesselK0Regression

section AtkinsonSourceRegression

open Complex Filter MeasureTheory Set
open scoped ContDiff

example : zetaDivisorLatticePhase 0 = 1 := by
  simpa only [Nat.cast_zero] using zetaDivisorLatticePhase_nat 0

example : zetaDivisorLatticePhase 2 = 1 := zetaDivisorLatticePhase_nat 2

example : ‖zetaDivisorLatticePhase (1 / 2)‖ = 1 := norm_zetaDivisorLatticePhase _

example (T G L : ℝ) : zetaAtkinsonDivisorTest T G L 1 = zetaSmoothDivisorTest T G L 1 := by
  simpa only [Nat.cast_one] using zetaAtkinsonDivisorTest_nat T G L 1

example (T G L x : ℝ) :
    ‖zetaAtkinsonDivisorTest T G L x‖ = ‖zetaSmoothDivisorTest T G L x‖ :=
  norm_zetaAtkinsonDivisorTest T G L x

example : Function.support (zetaAtkinsonDivisorTest 32 8 1) ⊆ Icc 2 32 := by
  rw [support_zetaAtkinsonDivisorTest]
  simpa only [show (32 : ℝ) / 16 = 2 by norm_num] using
    support_zetaSmoothDivisorTest_physical (T := 32) (G := 8) (L := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

noncomputable example : DFIVoronoiTestFunction (zetaAtkinsonDivisorTest 32 8 1) :=
  zetaAtkinsonDivisorVoronoiTest (by norm_num) (by norm_num) (by norm_num)

example : zetaSmoothDivisorSum 32 8 1 = zetaAtkinsonVoronoiMain 32 8 1 +
    zetaAtkinsonBesselMinus 32 8 1 + zetaAtkinsonBesselPlus 32 8 1 :=
  zetaSmoothDivisorSum_eq_atkinson_bessel (by norm_num) (by norm_num) (by norm_num)

example : Integrable (fun x : ℝ => zetaAtkinsonDivisorTest 32 8 1 x *
    (dfiBesselK0 (4 * Real.pi * Real.sqrt (x * (1 : ℕ))) : ℂ)) :=
  integrable_zetaAtkinsonK0_integrand (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example (T G L : ℝ) : zetaAtkinsonBesselPlusTerm T G L 0 = 0 := by
  simp [zetaAtkinsonBesselPlusTerm, divisorWeight]

example : HasSum (zetaAtkinsonBesselPlusTerm 32 8 1) (zetaAtkinsonBesselPlus 32 8 1) :=
  hasSum_zetaAtkinsonBesselPlusTerm (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ, T₀ ≤ T →
    T ^ (1 / 8 : ℝ) ≤ G → G ≤ T ^ (1 / 2 - (1 / 8 : ℝ)) →
    ‖zetaAtkinsonBesselPlus T G (Real.log T)‖ ≤ G * T ^ (-(3 : ℝ)) :=
  exists_zetaAtkinsonBesselPlus_powerSaving (by norm_num) 3

example : ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
    T₀ ≤ T → T ^ (1 / 8 : ℝ) ≤ G → G ≤ T ^ (1 / 2 - (1 / 8 : ℝ)) →
    |(∫ t : ℝ, zetaGaussianWeight T G t * zetaMomentCriticalNorm t ^ 2) -
      2 * (zetaAtkinsonVoronoiMain T G (Real.log T) +
        zetaAtkinsonBesselMinus T G (Real.log T)).re| ≤ C * G * Real.log T :=
  exists_zetaSquarePhysicalGaussian_atkinson_reduced (by norm_num)

example : ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
    T₀ ≤ T → T ^ (1 / 4 : ℝ) ≤ G → G ≤ T ^ (1 / 2 - (1 / 4 : ℝ)) →
    (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
      2 * Real.exp 1 * (zetaAtkinsonVoronoiMain T G (Real.log T) +
        zetaAtkinsonBesselMinus T G (Real.log T)).re + C * G * Real.log T :=
  exists_zetaSquareLocalMean_le_atkinson_reduced (by norm_num)

end AtkinsonSourceRegression

section AtkinsonSaddleRegression

open Complex

example (T G L : ℝ) :
    zetaAtkinsonDivisorTest T G L 1 =
      zetaAtkinsonAmplitude T G L 1 * Complex.exp ((zetaAtkinsonPhase T 0 1 : ℝ) * I) :=
  zetaAtkinsonDivisorTest_eq_amplitude_phase T G L (by norm_num)

example : zetaAtkinsonSaddle (4 * Real.pi) 1 = 4 := by
  have hA : 4 * Real.pi / (2 * Real.pi) = (2 : ℝ) := by field_simp; ring
  norm_num [zetaAtkinsonSaddle, atkinsonSaddleRoot, hA]

example : zetaAtkinsonSaddle (4 * Real.pi) (-1) = 1 := by
  have hA : 4 * Real.pi / (2 * Real.pi) = (2 : ℝ) := by field_simp; ring
  norm_num [zetaAtkinsonSaddle, atkinsonSaddleRoot, hA]

example (T : ℝ) (hT : 0 < T) : zetaAtkinsonSaddle T 0 = T / (2 * Real.pi) :=
  zetaAtkinsonSaddle_zero hT

example (T x : ℝ) (hT : 0 < T) (hx : 0 < x) :
    deriv (zetaAtkinsonPhase T 1) x = 0 ↔ x = zetaAtkinsonSaddle T 1 :=
  zetaAtkinsonPhase_stationary_iff hT hx 1

example (T : ℝ) (hT : 0 < T) :
    deriv (zetaAtkinsonPhase T (-1)) (zetaAtkinsonSaddle T (-1)) = 0 :=
  zetaAtkinsonPhase_stationary hT (-1)

example (T : ℝ) (hT : 0 < T) :
    deriv (deriv (zetaAtkinsonPhase T 1)) (zetaAtkinsonSaddle T 1) < 0 :=
  zetaAtkinsonPhase_secondDeriv_saddle_neg hT 1

example (T : ℝ) (hT : 0 < T) :
    deriv (deriv (zetaAtkinsonPhase T (-1))) (zetaAtkinsonSaddle T (-1)) < 0 :=
  zetaAtkinsonPhase_secondDeriv_saddle_neg hT (-1)

end AtkinsonSaddleRegression

section AtkinsonMainRegression

open Complex MeasureTheory Set

example : IntervalC1Bound (fun x => (zetaBandCutoff 1 2 3 4 x : ℂ)) (-1) 5 2 :=
  intervalC1Bound_zetaBandCutoff (by norm_num) (by norm_num) (by norm_num)

example (T : ℝ) (hT : 0 < T) :
    IntervalC1Bound (fun x : ℝ => (Real.sqrt x : ℂ)) (T / 16) T (Real.sqrt T) :=
  intervalC1Bound_source_sqrt hT

example (T : ℝ) (hT : 16 ≤ T) :
    IntervalC1Bound (fun x : ℝ => ((Real.log x + 2 * Real.eulerMascheroniConstant : ℝ) : ℂ))
      (T / 16) T (Real.log T + 2 * Real.eulerMascheroniConstant) :=
  intervalC1Bound_source_log hT

example (T : ℝ) (hT : 0 < T) :
    zetaDivisorWeight ((Real.log T : ℂ) - zetaGammaLeadingLog T) = zetaMainMellinProfile 1 := by
  simpa only [div_self hT.ne'] using zetaDivisorWeight_source_eq_profile hT hT

example : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T →
    IntervalC1Bound (fun x => zetaMainMellinProfile (x / T)) (T / 16) T C :=
  exists_intervalC1Bound_zetaMainMellinProfile

example : zetaLogGaussianEnvelope 4 8 4 = 1 := by
  simp only [zetaLogGaussianEnvelope, sub_self, mul_zero, zero_pow (by decide : 2 ≠ 0),
    neg_zero, zero_div, Real.exp_zero]

example : IntervalC1Bound (fun x : ℝ => (zetaLogGaussianEnvelope 2 0 x : ℂ)) 1 4 2 :=
  intervalC1Bound_zetaLogGaussianEnvelope (by norm_num) (by norm_num) (by norm_num) 0

example : HasDerivAt (zetaLogGaussianEnvelope 2 8) 0 2 := by
  simpa only [sub_self, zero_div, mul_zero, zero_mul] using
    hasDerivAt_zetaLogGaussianEnvelope 2 8 (x := 2) (by norm_num)

example : 1 / ‖zetaGaussianQuadraticCoefficient 8 4‖ ≤ 16 := by
  simpa only [show (4 : ℝ) ^ 2 = 16 by norm_num] using
    inverse_norm_zetaGaussianQuadraticCoefficient_le 8 (G := 4) (by norm_num)

example : HasDerivAt (zetaGaussianQuadraticIntegral 8 4) 0 0 := by
  simpa only [Complex.ofReal_zero, neg_zero, zero_div, zero_mul] using
    hasDerivAt_zetaGaussianQuadraticIntegral 8 (G := 4) (by norm_num) 0

example : ‖deriv (zetaGaussianQuadraticIntegral 32 8) 1‖ ≤
    (Real.sqrt Real.pi * (8 : ℝ) ^ 3 / 2) * |(1 : ℝ)| * Real.exp (-((8 : ℝ) * 1) ^ 2 / 8) :=
  norm_deriv_zetaGaussianQuadraticIntegral_le (by norm_num) (by norm_num) (by norm_num) 1

example : IntervalC1Bound
    (fun x => zetaGaussianQuadraticIntegral 32 8 (Real.log x - Real.log (32 / (2 * Real.pi))))
    (32 / 16) 32 (4 * Real.sqrt Real.pi * 8) :=
  intervalC1Bound_zetaQuadraticLogGaussian (by norm_num) (by norm_num) (by norm_num)

example (T G L : ℝ) (hT : 0 < T) :
    zetaAtkinsonMainWeight T G L 1 * ((1 : ℂ)⁻¹ *
      Complex.exp (((T * Real.log 1 - 2 * Real.pi * 1 : ℝ) : ℂ) * I)) =
        ((Real.log 1 : ℂ) + 2 * Real.eulerMascheroniConstant) * zetaAtkinsonDivisorTest T G L 1 :=
  zetaAtkinsonMainWeight_carrier hT (by norm_num) G L

example : ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 16 ≤ T → 1 ≤ Real.log T →
    0 < G → G ^ 2 ≤ 2 * T → 0 < L →
    IntervalC1Bound (zetaAtkinsonMainWeight T G L) (T / 16) T
      (C * G * Real.sqrt T * Real.log T) := exists_intervalC1Bound_zetaAtkinsonMainWeight

example : Integrable (zetaAtkinsonMainIntegrand 32 8 1) :=
  integrable_zetaAtkinsonMainIntegrand (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : zetaAtkinsonVoronoiMain 32 8 1 =
    ∫ x in (32 / 16)..32, zetaAtkinsonMainWeight 32 8 1 x * ((x : ℂ)⁻¹ *
      Complex.exp (((32 * Real.log x - 2 * Real.pi * x : ℝ) : ℂ) * I)) :=
  zetaAtkinsonVoronoiMain_eq_reflection (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 16 ≤ T → 1 ≤ Real.log T →
    0 < G → G ^ 2 ≤ 2 * T → 0 < L → 8 * L ≤ G →
    ‖zetaAtkinsonVoronoiMain T G L‖ ≤ C * G * Real.log T :=
  exists_norm_zetaAtkinsonVoronoiMain_le

example : ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
    T₀ ≤ T → T ^ (1 / 8 : ℝ) ≤ G → G ≤ T ^ (1 / 2 - (1 / 8 : ℝ)) →
    ‖zetaAtkinsonVoronoiMain T G (Real.log T)‖ ≤ C * G * Real.log T :=
  exists_zetaAtkinsonVoronoiMain_log_bound (by norm_num)

example : ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
    T₀ ≤ T → T ^ (1 / 8 : ℝ) ≤ G → G ≤ T ^ (1 / 2 - (1 / 8 : ℝ)) →
    |(∫ t : ℝ, zetaGaussianWeight T G t * zetaMomentCriticalNorm t ^ 2) -
      2 * (zetaAtkinsonBesselMinus T G (Real.log T)).re| ≤ C * G * Real.log T :=
  exists_zetaSquarePhysicalGaussian_atkinson_minus_approximation (by norm_num)

example : ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
    T₀ ≤ T → T ^ (1 / 4 : ℝ) ≤ G → G ≤ T ^ (1 / 2 - (1 / 4 : ℝ)) →
    (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
      2 * Real.exp 1 * (zetaAtkinsonBesselMinus T G (Real.log T)).re +
        C * G * Real.log T := exists_zetaSquareLocalMean_le_atkinson_minus (by norm_num)

end AtkinsonMainRegression

section NeumannSourceRegression

open Complex Filter MeasureTheory Set Topology

-- The branch signs and the limiting ray through one are essential.
example : neumannRayCoefficient = (1 + I) / 2 := neumannRayCoefficient_eq

example : neumannLaplaceAmplitude 0 = 1 := neumannLaplaceAmplitude_zero

example : ‖neumannLaplaceAmplitude (-3)‖ ≤ 1 := norm_neumannLaplaceAmplitude_le_one (-3)

example : ‖neumannLaplaceAmplitude (-2) - 1 + I * (-2 : ℝ) / 2‖ ≤
    (3 / 8 : ℝ) * (-2 : ℝ) ^ 2 := by
  simpa only [mul_comm I] using norm_neumannLaplaceAmplitude_sub_linear_le (-2)

example : IntegrableOn (fun t : ℝ => neumannContourKernel 1 ((1 : ℂ) + t * I)) (Ioi 0) :=
  integrableOn_neumannContourKernel_vertical (by norm_num) (by norm_num)

example : ContinuousAt (neumannVerticalIntegral 1) 1 :=
  continuousAt_neumannVerticalIntegral (by norm_num) (by norm_num)

example : neumannVerticalIntegral 1 0 = (dfiBesselY0Tail 1 : ℂ) :=
  neumannVerticalIntegral_zero_eq_tail 1

example : dfiBesselY0 (1 / 2) = -(2 / Real.pi) * (neumannVerticalIntegral (1 / 2) 1).re :=
  dfiBesselY0_eq_neumannVerticalIntegral (by norm_num)

example : neumannLaplaceMoment 1 0 = Real.sqrt Real.pi := by
  simpa using neumannLaplaceMoment_zero (x := 1) (by norm_num)

example : neumannLaplaceMoment 1 1 = Real.sqrt Real.pi / 2 := by
  simpa using neumannLaplaceMoment_one (x := 1) (by norm_num)

example : neumannLaplaceMoment 1 2 = 3 * Real.sqrt Real.pi / 4 := by
  simpa using neumannLaplaceMoment_two (x := 1) (by norm_num)

-- Includes small positive arguments, not just an unspecified asymptotic range.
example : |dfiBesselY0 (1 / 2) - neumannTwoTerm (1 / 2)| ≤
    neumannTwoTermErrorConstant * (1 / 2 : ℝ) ^ (-(5 / 2 : ℝ)) :=
  abs_dfiBesselY0_sub_neumannTwoTerm_le (by norm_num)

example : Measurable dfiBesselY0 := measurable_dfiBesselY0

example (n : ℕ) (hn : 0 < n) :
    16 * n ≤ (4 * Real.pi * Real.sqrt (1 * n)) ^ 2 ∧
      1 ≤ 4 * Real.pi * Real.sqrt (1 * n) :=
  neumann_source_argument_bounds (by norm_num) (by norm_num) hn

example (n : ℕ) (hn : 0 < n) :
    |dfiBesselY0 (4 * Real.pi * Real.sqrt (2 * n)) -
      neumannTwoTerm (4 * Real.pi * Real.sqrt (2 * n))| ≤
        neumannTwoTermErrorConstant * (32 : ℝ) ^ (-(5 / 4 : ℝ)) *
          (n : ℝ) ^ (-(5 / 4 : ℝ)) :=
  abs_neumann_source_remainder_le (by norm_num) (by norm_num) hn

-- Physical support and the closed G-squared endpoint are both exercised.
example : Integrable (zetaAtkinsonTwoTermIntegrand 32 8 1 1) :=
  integrable_zetaAtkinsonTwoTermIntegrand
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example (T G L : ℝ) : zetaNeumannRemainderTerm T G L 0 = 0 := by
  simp [zetaNeumannRemainderTerm, divisorWeight]

example (T G L : ℝ) : zetaAtkinsonTwoTerm T G L 0 = 0 := by
  simp [zetaAtkinsonTwoTerm, divisorWeight]

example : ‖divisorDirichletTerm (5 / 4) 0‖ = ‖divisorWeight 0‖ * (0 : ℝ) ^ (-(5 / 4 : ℝ)) := by
  simpa only [Complex.ofReal_div, Complex.ofReal_ofNat, Nat.cast_zero] using
    norm_divisorDirichletTerm_real (5 / 4) 0

example : Summable (zetaNeumannRemainderTerm 32 8 1) :=
  summable_zetaNeumannRemainderTerm
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : Summable (zetaAtkinsonTwoTerm 32 8 1) :=
  summable_zetaAtkinsonTwoTerm
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : zetaAtkinsonBesselMinus 32 8 1 - zetaAtkinsonTwoTermSum 32 8 1 =
    ∑' n : ℕ, zetaNeumannRemainderTerm 32 8 1 n :=
  zetaAtkinsonBesselMinus_sub_twoTerm
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 16 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
    0 < L → 8 * L ≤ G →
      ‖zetaAtkinsonBesselMinus T G L - zetaAtkinsonTwoTermSum T G L‖ ≤ C * G :=
  exists_norm_zetaAtkinsonBesselMinus_sub_twoTerm_le

example : ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
    T₀ ≤ T → T ^ (1 / 8 : ℝ) ≤ G → G ≤ T ^ (1 / 2 - (1 / 8 : ℝ)) →
    |(∫ t : ℝ, zetaGaussianWeight T G t * zetaMomentCriticalNorm t ^ 2) -
      2 * (zetaAtkinsonTwoTermSum T G (Real.log T)).re| ≤ C * G * Real.log T :=
  exists_zetaSquarePhysicalGaussian_atkinson_twoTerm_approximation (by norm_num)

example : ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
    T₀ ≤ T → T ^ (1 / 4 : ℝ) ≤ G → G ≤ T ^ (1 / 2 - (1 / 4 : ℝ)) →
    (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
      2 * Real.exp 1 * (zetaAtkinsonTwoTermSum T G (Real.log T)).re +
        C * G * Real.log T := exists_zetaSquareLocalMean_le_atkinson_twoTerm (by norm_num)

end NeumannSourceRegression

section AtkinsonCarrierRegression

open Complex Filter MeasureTheory Set

example (T b : ℝ) : zetaAtkinsonPhase T b (2 ^ 2) = 2 * Real.pi * atkinsonRootPhase T b 2 :=
  zetaAtkinsonPhase_sq T b (by norm_num)

example (T b : ℝ) : HasDerivAt (atkinsonRootPhase T b) (atkinsonRootSlope T b 1) 1 :=
  hasDerivAt_atkinsonRootPhase T b (by norm_num)

example (b : ℝ) : HasDerivAt (atkinsonRootSlope Real.pi b) (-3) 1 := by
  simpa only [one_pow, mul_one, neg_div, div_self Real.pi_ne_zero,
    show -(1 : ℝ) - 2 = -3 by norm_num] using
      hasDerivAt_atkinsonRootSlope Real.pi b (y := 1) (by norm_num)

example : StrictAntiOn (atkinsonRootSlope 0 (-3)) (Ioi 0) :=
  atkinsonRootSlope_strictAnti (by norm_num) (-3)

example (T : ℝ) (hT : 0 < T) (b : ℝ) :
    atkinsonRootSlope T b (atkinsonSaddleRoot (T / (2 * Real.pi)) b + 1) ≤ -2 :=
  atkinsonRootSlope_le_neg_two hT
    (by linarith [atkinsonSaddleRoot_pos (by positivity : 0 < T / (2 * Real.pi)) b]) le_rfl

example (T : ℝ) (hT : 0 < T) (b : ℝ)
    (hr : 1 < atkinsonSaddleRoot (T / (2 * Real.pi)) b) :
    2 ≤ atkinsonRootSlope T b (atkinsonSaddleRoot (T / (2 * Real.pi)) b - 1) :=
  two_le_atkinsonRootSlope hT (by linarith) le_rfl

example : ‖∫ y in (1 : ℝ)..4, atkinsonRootKernel 8 3 y‖ ≤ 4 :=
  norm_atkinsonRootKernel_integral_le_four (by norm_num) 3 (by norm_num) (by norm_num)

example : ‖∫ y in (1 : ℝ)..4, atkinsonRootKernel 8 (-3) y‖ ≤ 4 :=
  norm_atkinsonRootKernel_integral_le_four (by norm_num) (-3) (by norm_num) (by norm_num)

example : ‖∫ y in (1 : ℝ)..1, atkinsonRootKernel 8 0 y‖ ≤ 4 :=
  norm_atkinsonRootKernel_integral_le_four (by norm_num) 0 (by norm_num) le_rfl

example {f : ℝ → ℂ} {M : ℝ} (hf : IntervalC1Bound f (1 ^ 2) (2 ^ 2) M) :
    IntervalC1Bound (fun y => f (y ^ 2)) 1 2 M :=
  hf.comp_sq (by norm_num) (by norm_num)

example : ‖∫ y in (1 : ℝ)..4, (2 : ℂ) * atkinsonRootKernel 8 (-3) y‖ ≤ 16 := by
  have h := (intervalC1Bound_const 2 1 4).atkinsonRoot (T := 8)
    (by norm_num) (-3) (by norm_num) (by norm_num)
  simpa only [norm_ofNat, show (8 : ℝ) * 2 = 16 by norm_num] using h

example : Real.sqrt (1 : ℝ) * Real.exp (-Real.log 1 / 2) = 1 :=
  sqrt_mul_exp_neg_half_log (by norm_num)

example : ∃ C : ℝ, 0 < C ∧ ∀ T G L b : ℝ, 0 < T → 0 < G → G ^ 2 ≤ 2 * T →
    0 < L → 8 * L ≤ G →
    ‖atkinsonPowerIntegral T G L (1 / 4) b‖ ≤ C * G * T ^ (-(1 / 4 : ℝ)) :=
  exists_norm_atkinsonPowerIntegral_le (1 / 4)

example : ∃ C : ℝ, 0 < C ∧ ∀ T G L b : ℝ, 0 < T → 0 < G → G ^ 2 ≤ 2 * T →
    0 < L → 8 * L ≤ G →
    ‖atkinsonPowerIntegral T G L (3 / 4) b‖ ≤ C * G * T ^ (-(3 / 4 : ℝ)) :=
  exists_norm_atkinsonPowerIntegral_le (3 / 4)

example : Integrable (atkinsonPowerIntegrand 32 8 1 (1 / 4) (Real.sqrt 2)) :=
  integrable_atkinsonPowerIntegrand (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (1 / 4) (Real.sqrt 2)

example : Integrable (atkinsonPowerIntegrand 32 8 1 (3 / 4) (-Real.sqrt 2)) :=
  integrable_atkinsonPowerIntegrand (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (3 / 4) (-Real.sqrt 2)

example : (4 * Real.pi * Real.sqrt (2 * (1 : ℕ))) ^ (-2 * (3 / 4 : ℝ)) =
    atkinsonBesselScale (3 / 4) 1 * (2 : ℝ) ^ (-(3 / 4 : ℝ)) :=
  atkinson_bessel_argument_rpow (by norm_num) (by norm_num) (3 / 4)

example (T G L : ℝ) : zetaAtkinsonTwoTerm T G L 0 = 0 := by
  simp [zetaAtkinsonTwoTerm, divisorWeight]

example : zetaAtkinsonTwoTerm 32 8 1 1 =
    divisorWeight 1 * (-(2 * Real.pi) : ℂ) * atkinsonTwoTermCarrierIntegral 32 8 1 1 :=
  zetaAtkinsonTwoTerm_eq_carrierIntegral (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1

example : Summable (fun n : ℕ => divisorWeight n * (-(2 * Real.pi) : ℂ) *
    atkinsonTwoTermCarrierIntegral 32 8 1 n) :=
  summable_atkinsonTwoTermCarrierIntegrals
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : zetaAtkinsonTwoTermSum 32 8 1 = atkinsonTwoTermCarrierSum 32 8 1 :=
  zetaAtkinsonTwoTermSum_eq_carrierIntegrals (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ T G L : ℝ, 0 < T → 0 < G → G ^ 2 ≤ 2 * T →
    0 < L → 8 * L ≤ G → ∀ n : ℕ,
    ‖zetaAtkinsonTwoTerm T G L n‖ ≤ ‖divisorWeight n‖ *
      (C * G * T ^ (-(1 / 4 : ℝ)) * (n : ℝ) ^ (-(1 / 4 : ℝ)) +
       D * G * T ^ (-(3 / 4 : ℝ)) * (n : ℝ) ^ (-(3 / 4 : ℝ))) :=
  exists_norm_zetaAtkinsonTwoTerm_le

example : ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
    T₀ ≤ T → T ^ (1 / 8 : ℝ) ≤ G → G ≤ T ^ (1 / 2 - (1 / 8 : ℝ)) →
    |(∫ t : ℝ, zetaGaussianWeight T G t * zetaMomentCriticalNorm t ^ 2) -
      2 * (atkinsonTwoTermCarrierSum T G (Real.log T)).re| ≤ C * G * Real.log T :=
  exists_zetaSquarePhysicalGaussian_carrier_approximation (by norm_num)

example : ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
    T₀ ≤ T → T ^ (1 / 4 : ℝ) ≤ G → G ≤ T ^ (1 / 2 - (1 / 4 : ℝ)) →
    (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
      2 * Real.exp 1 * (atkinsonTwoTermCarrierSum T G (Real.log T)).re +
        C * G * Real.log T := exists_zetaSquareLocalMean_le_carriers (by norm_num)

end AtkinsonCarrierRegression

section AtkinsonCorrectionRegression

open Complex MeasureTheory Set
open RiemannZeta.GuthMaynard

example : (32 : ℝ) ≤ atkinsonRootSlope 16 32 1 := by
  apply atkinsonRootSlope_far_positive (by norm_num)
  · norm_num
  · norm_num

example : atkinsonRootSlope 16 (-32) 4 ≤ (-32 : ℝ) := by
  apply atkinsonRootSlope_far_negative (by norm_num)
  · norm_num
  · norm_num

example : ‖∫ y in (1 : ℝ)..4, atkinsonRootKernel 16 32 y‖ ≤ 1 / (32 * Real.pi) ∧
    ‖∫ y in (1 : ℝ)..4, atkinsonRootKernel 16 (-32) y‖ ≤ 1 / (32 * Real.pi) := by
  have h := norm_atkinsonRootKernel_integral_far (T := 16) (b := 32) (c := 4)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

example : ∃ C : ℝ, 0 < C ∧ ∀ T G L b : ℝ, 0 < T → 0 < G → G ^ 2 ≤ 2 * T →
    0 < L → 8 * L ≤ G → 8 * Real.sqrt T ≤ b →
    ‖atkinsonPowerIntegral T G L (1 / 4) b‖ ≤ C * G * T ^ (-(1 / 4 : ℝ)) / b ∧
    ‖atkinsonPowerIntegral T G L (1 / 4) (-b)‖ ≤ C * G * T ^ (-(1 / 4 : ℝ)) / b :=
  exists_norm_atkinsonPowerIntegral_far_le (1 / 4)

example : (1 : ℝ) ^ (-(3 / 4 : ℝ)) * Real.sqrt 1 ≤ 1 :=
  atkinson_correction_height_absorb le_rfl

example : ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 1 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
    0 < L → 8 * L ≤ G → ∀ n : ℕ, 0 < n →
    ‖neumannCorrectionPlus * atkinsonPowerIntegral T G L (3 / 4) (Real.sqrt n) +
      neumannCorrectionMinus * atkinsonPowerIntegral T G L (3 / 4) (-Real.sqrt n)‖ ≤
        C * G / Real.sqrt n := exists_norm_atkinsonCorrectionPair_le

example (T G L : ℝ) : atkinsonCorrectionTerm T G L 0 = 0 := by
  simp [atkinsonCorrectionTerm, divisorWeight]

example (T G L : ℝ) : atkinsonLeadingTerm T G L 0 = 0 := by
  simp [atkinsonLeadingTerm, divisorWeight]

example (T G L : ℝ) : atkinsonTwoTermCarrierIntegral T G L 1 =
    atkinsonLeadingIntegral T G L 1 - atkinsonCorrectionIntegral T G L 1 :=
  atkinsonTwoTermCarrierIntegral_eq_leading_sub_correction T G L 1

example : zetaAtkinsonTwoTerm 32 8 1 1 =
    atkinsonLeadingTerm 32 8 1 1 - atkinsonCorrectionTerm 32 8 1 1 :=
  zetaAtkinsonTwoTerm_eq_leading_sub_correction (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) 1

example : Summable (atkinsonCorrectionTerm 32 8 1) :=
  summable_atkinsonCorrectionTerm (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : Summable (atkinsonLeadingTerm 32 8 1) :=
  summable_atkinsonLeadingTerm (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : zetaAtkinsonTwoTermSum 32 8 1 =
    atkinsonLeadingSum 32 8 1 - atkinsonCorrectionSum 32 8 1 :=
  zetaAtkinsonTwoTermSum_eq_leading_sub_correction (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

example : ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 16 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
    0 < L → 8 * L ≤ G → ‖zetaAtkinsonTwoTermSum T G L - atkinsonLeadingSum T G L‖ ≤ C * G :=
  exists_norm_zetaAtkinsonTwoTermSum_sub_leading_le

example : ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
    T₀ ≤ T → T ^ (1 / 8 : ℝ) ≤ G → G ≤ T ^ (1 / 2 - (1 / 8 : ℝ)) →
    |(∫ t : ℝ, zetaGaussianWeight T G t * zetaMomentCriticalNorm t ^ 2) -
      2 * (atkinsonLeadingSum T G (Real.log T)).re| ≤ C * G * Real.log T :=
  exists_zetaSquarePhysicalGaussian_atkinson_leading_approximation (by norm_num)

example : ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
    T₀ ≤ T → T ^ (1 / 4 : ℝ) ≤ G → G ≤ T ^ (1 / 2 - (1 / 4 : ℝ)) →
    (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
      2 * Real.exp 1 * (atkinsonLeadingSum T G (Real.log T)).re +
        C * G * Real.log T := exists_zetaSquareLocalMean_le_atkinson_leading (by norm_num)

end AtkinsonCorrectionRegression

section AtkinsonFourierRegression

open Complex MeasureTheory Set
open scoped ContDiff

example : IntervalC2Bound (fun _ : ℝ => (1 : ℂ)) (1 / 4) 1 1 1 := by
  simpa only [norm_one] using intervalC2Bound_const (1 : ℂ) (1 / 4) 1 (by norm_num : (0 : ℝ) ≤ 1)

example : Function.support (zetaDivisorBandCutoff 32 8 1) ⊆ Icc 2 32 := by
  have h := support_zetaDivisorBandCutoff_physical (T := 32) (G := 8) (L := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

example (α : ℝ) : Function.support (atkinsonRootFourierAmplitude 32 8 1 α) ⊆ Icc (1 / 4) 1 :=
  support_atkinsonRootFourierAmplitude (by norm_num) (by norm_num) (by norm_num) (by norm_num) α

example (T G L α : ℝ) : atkinsonRootFourierAmplitude T G L α 0 = 0 := by
  simp [atkinsonRootFourierAmplitude]

example (T G L α : ℝ) : atkinsonRootFourierAmplitude T G L α (-1) = 0 := by
  simp [atkinsonRootFourierAmplitude]

example (α : ℝ) : ContDiff ℝ ∞ (atkinsonRootFourierAmplitude 32 8 1 α) :=
  contDiff_atkinsonRootFourierAmplitude (by norm_num) (by norm_num) (by norm_num) (by norm_num) α

example (α : ℝ) : HasCompactSupport (atkinsonRootFourierAmplitude 32 8 1 α) :=
  hasCompactSupport_atkinsonRootFourierAmplitude (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) α

example (α : ℝ) : Function.support (iteratedDeriv 2 (atkinsonRootFourierAmplitude 32 8 1 α)) ⊆
    Icc (1 / 4) 1 :=
  support_iteratedDeriv_atkinsonRootFourierAmplitude (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) α 2

example : ∃ C : ℝ, 0 < C ∧ ∀ T G L ξ : ℝ, 1 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
    1 ≤ L → 8 * L ≤ G →
    (1 + |ξ|) ^ 2 * ‖𝓕 (atkinsonRootFourierAmplitude T G L (1 / 4)) ξ‖ ≤
      C * G * T ^ (-(1 / 4 : ℝ)) * T ^ 2 :=
  exists_norm_fourier_atkinsonRootFourierAmplitude_le (1 / 4)

example (α : ℝ) : atkinsonPowerIntegral 32 8 1 α 1 =
    (2 * Real.sqrt 32 : ℝ) • (atkinsonPhaseExponential 32 (Real.log 32) *
      𝓕 (atkinsonRootFourierAmplitude 32 8 1 α) (-2 * 1 * Real.sqrt 32)) :=
  atkinsonPowerIntegral_eq_fourier (by norm_num) (by norm_num) (by norm_num) (by norm_num) α 1

example (α : ℝ) : atkinsonPowerIntegral 32 8 1 α (-1) =
    (2 * Real.sqrt 32 : ℝ) • (atkinsonPhaseExponential 32 (Real.log 32) *
      𝓕 (atkinsonRootFourierAmplitude 32 8 1 α) (-2 * (-1) * Real.sqrt 32)) :=
  atkinsonPowerIntegral_eq_fourier (by norm_num) (by norm_num) (by norm_num) (by norm_num) α (-1)

example : ∃ C : ℝ, 0 < C ∧ ∀ T G L b : ℝ, 1 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
    1 ≤ L → 8 * L ≤ G → b ^ 2 * ‖atkinsonPowerIntegral T G L (1 / 4) b‖ ≤
      C * G * T ^ (-(1 / 4 : ℝ)) * T * Real.sqrt T :=
  exists_sq_mul_norm_atkinsonPowerIntegral_le (1 / 4)

example : ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 1 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
    1 ≤ L → 8 * L ≤ G → ∀ n : ℕ,
    ‖atkinsonLeadingTerm T G L n‖ ≤ C * G * T ^ (5 / 4 : ℝ) *
      ‖divisorDirichletTerm (5 / 4) n‖ := exists_norm_atkinsonLeadingTerm_le

example : Summable (atkinsonLeadingTerm 32 8 1) :=
  summable_atkinsonLeadingTerm_of_secondOrder (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example (T G L : ℝ) : atkinsonLeadingFiniteSum T G L 0 = 0 := by
  simp [atkinsonLeadingFiniteSum]

example (T G L : ℝ) : atkinsonLeadingFiniteSum T G L 1 = 0 := by
  simp [atkinsonLeadingFiniteSum, atkinsonLeadingTerm, divisorWeight]

example : ‖divisorDirichletTerm (5 / 4) 1‖ ≤ (1 : ℝ) ^ (-(1 / 8 : ℝ)) *
    ‖divisorDirichletTerm (9 / 8) 1‖ := by
  simpa only [Nat.cast_one] using
    norm_divisorDirichletTerm_fiveQuarters_le_tail (N := 1) (by norm_num) le_rfl

example : ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 1 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
    1 ≤ L → 8 * L ≤ G → ∀ N : ℕ, T ^ (10 : ℝ) ≤ N →
    ‖atkinsonLeadingSum T G L - atkinsonLeadingFiniteSum T G L N‖ ≤ C * G :=
  exists_norm_atkinsonLeadingSum_sub_polynomial_le

example : ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
    T₀ ≤ T → T ^ (1 / 8 : ℝ) ≤ G → G ≤ T ^ (1 / 2 - (1 / 8 : ℝ)) →
    ∀ N : ℕ, T ^ (10 : ℝ) ≤ N →
    |(∫ t : ℝ, zetaGaussianWeight T G t * zetaMomentCriticalNorm t ^ 2) -
      2 * (atkinsonLeadingFiniteSum T G (Real.log T) N).re| ≤ C * G * Real.log T :=
  exists_zetaSquarePhysicalGaussian_atkinson_finite_approximation (by norm_num)

example : ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
    T₀ ≤ T → T ^ (1 / 8 : ℝ) ≤ G → G ≤ T ^ (1 / 2 - (1 / 8 : ℝ)) →
    ∀ N : ℕ, T ^ (10 : ℝ) ≤ N →
    (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
      2 * Real.exp 1 * (atkinsonLeadingFiniteSum T G (Real.log T) N).re +
        C * G * Real.log T :=
  exists_zetaSquareLocalMean_le_atkinson_finite (by norm_num)

end AtkinsonFourierRegression

namespace AtkinsonStationaryRegression

open TaoTrudgianYang2025 Complex MeasureTheory Set

example (T : ℝ) : atkinsonSourcePhase T 0 = -Real.pi / 4 := by
  simp [atkinsonSourcePhase, neg_div]

example : Complex.exp (((Real.pi * (0 : ℝ) : ℝ) : ℂ) * I) = 1 := by
  simpa only [pow_zero, Nat.cast_zero] using exp_atkinson_natural_pi 0

example : Complex.exp (((Real.pi * (1 : ℝ) : ℝ) : ℂ) * I) = -1 := by
  simpa only [pow_one, Nat.cast_one] using exp_atkinson_natural_pi 1

example : Complex.exp (((Real.pi * (2 : ℝ) : ℝ) : ℂ) * I) = 1 := by
  simpa using exp_atkinson_natural_pi 2

example {T : ℝ} (hT : 0 < T) (n : ℕ) :
    atkinsonSaddleRoot (T / (2 * Real.pi)) (Real.sqrt n) *
      atkinsonSaddleRoot (T / (2 * Real.pi)) (-Real.sqrt n) = T / (2 * Real.pi) :=
  atkinsonSaddleRoot_mul_neg (by positivity) (Real.sqrt n)

example (n : ℕ) : zetaGaussianQuadraticIntegral 32 8
    (Real.log (zetaAtkinsonSaddle 32 (Real.sqrt n)) - Real.log (32 / (2 * Real.pi))) =
      atkinsonSaddleGaussian 32 8 n :=
  zetaGaussianQuadraticIntegral_at_saddle (by norm_num) 8 n

example (n : ℕ) : zetaGaussianQuadraticIntegral 32 8
    (Real.log (zetaAtkinsonSaddle 32 (-Real.sqrt n)) - Real.log (32 / (2 * Real.pi))) =
      atkinsonSaddleGaussian 32 8 n :=
  zetaGaussianQuadraticIntegral_at_neg_saddle (by norm_num) (by norm_num) n

example : ‖atkinsonSaddleGaussian 32 8 32‖ ≤ Real.sqrt Real.pi * 8 *
    Real.exp (-(8 : ℝ) ^ 2 * 32 / (12 * 32)) := by
  simpa only [Nat.cast_ofNat, neg_mul] using
    norm_atkinsonSaddleGaussian_le_physical (T := 32) (G := 8)
      (by norm_num) (by norm_num) (by norm_num) 32 (by norm_num)

example : |Real.log (1 + (1 / 2 : ℝ)) - 1 / 2 + (1 / 2 : ℝ) ^ 2 / 2| ≤
    2 * |(1 / 2 : ℝ)| ^ 3 := abs_log_one_add_sub_quadratic_le (by norm_num)

example : |Real.log (1 + (-(1 / 2 : ℝ))) - (-(1 / 2 : ℝ)) + (-(1 / 2 : ℝ)) ^ 2 / 2| ≤
    2 * |(-(1 / 2 : ℝ))| ^ 3 := abs_log_one_add_sub_quadratic_le (by norm_num)

example (v : ℝ) : ‖deriv (zetaGaussianQuadraticIntegral 32 8) v‖ ≤
    5 * Real.sqrt Real.pi * 8 ^ 2 :=
  norm_deriv_zetaGaussianQuadraticIntegral_le_natural (by norm_num) (by norm_num) (by norm_num) v

example (v : ℝ) : ‖iteratedDeriv 2 (zetaGaussianQuadraticIntegral 32 8) v‖ ≤
    3 * Real.sqrt Real.pi * 8 ^ 3 :=
  norm_iteratedDeriv_two_zetaGaussianQuadraticIntegral_le_natural
    (by norm_num) (by norm_num) (by norm_num) v

example : ∃ C : ℝ, 0 < C ∧
    IntervalC2Bound (fun y => atkinsonPowerWeight 32 8 1 (1 / 4) (y ^ 2))
      (Real.sqrt 32 / 4) (Real.sqrt 32)
        (C * 8 * (32 : ℝ) ^ (-(1 / 4 : ℝ))) (8 / Real.sqrt 32) := by
  obtain ⟨C, hC, h⟩ := exists_intervalC2Bound_atkinsonPowerWeight_root_natural (1 / 4)
  exact ⟨C, hC, h 32 8 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩

example (c : ℝ) : atkinsonQuadraticWindow c 0 = 0 := by
  simp [atkinsonQuadraticWindow]

example (T G L α b : ℝ) : atkinsonFiniteStationaryMain T G L α b 0 = 0 := by
  simp [atkinsonFiniteStationaryMain, atkinsonQuadraticWindow]

example {T : ℝ} (hT : 0 < T) (b : ℝ) : 1 < atkinsonSaddleCurvature T b :=
  one_lt_atkinsonSaddleCurvature hT b

example {T : ℝ} (hT : 0 < T) (b : ℝ) :
    Real.sqrt (atkinsonSaddleCurvature T b) *
      Real.sqrt (atkinsonSaddleRoot (T / (2 * Real.pi)) b) =
    Real.sqrt (atkinsonSaddleCurvature T (-b)) *
      Real.sqrt (atkinsonSaddleRoot (T / (2 * Real.pi)) (-b)) := by
  rw [atkinsonSaddle_squareRoot_normalization hT b,
    atkinsonSaddle_squareRoot_normalization hT (-b), neg_sq]

example (n : ℕ) (H : ℝ) : atkinsonFiniteStationaryMain 32 8 1 (1 / 4) (Real.sqrt n) H =
    2 * atkinsonSaddleProfile 32 8 1 (1 / 4) (Real.sqrt n) * atkinsonSaddleGaussian 32 8 n *
      Complex.exp ((atkinsonCentralPhase 32 : ℂ) * I) * (-1 : ℂ) ^ n *
        Complex.exp (((atkinsonSourcePhase 32 n + Real.pi / 4 : ℝ) : ℂ) * I) *
          atkinsonQuadraticWindow (atkinsonSaddleCurvature 32 (Real.sqrt n)) H :=
  atkinsonFiniteStationaryMain_sqrt (by norm_num) 8 1 (1 / 4) H n

example (n : ℕ) (H : ℝ) : atkinsonFiniteStationaryMain 32 8 1 (1 / 4) (-Real.sqrt n) H =
    2 * atkinsonSaddleProfile 32 8 1 (1 / 4) (-Real.sqrt n) * atkinsonSaddleGaussian 32 8 n *
      Complex.exp ((atkinsonCentralPhase 32 : ℂ) * I) * (-1 : ℂ) ^ n *
        Complex.exp (((-atkinsonSourcePhase 32 n - Real.pi / 4 : ℝ) : ℂ) * I) *
          atkinsonQuadraticWindow (atkinsonSaddleCurvature 32 (-Real.sqrt n)) H :=
  atkinsonFiniteStationaryMain_neg_sqrt (by norm_num) (by norm_num) 1 (1 / 4) H n

example : ∃ C : ℝ, 0 < C ∧ ∀ T G L b H : ℝ, 0 < T → 1 ≤ G → G ^ 2 ≤ 2 * T →
    1 ≤ L → 8 * L ≤ G → 0 < H →
    Real.sqrt T / 4 ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b - H →
    atkinsonSaddleRoot (T / (2 * Real.pi)) b + H ≤ Real.sqrt T →
    H ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b / 2 →
    ‖atkinsonPowerIntegral T G L (1 / 4) b - atkinsonFiniteStationaryMain T G L (1 / 4) b H‖ ≤
      C * G * T ^ (-(1 / 4 : ℝ)) * (4 / (H * Real.pi) + 4 * (G / Real.sqrt T) * H ^ 2 +
        16 * T * H ^ 4 / (atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 3) :=
  exists_atkinsonPowerIntegral_finite_stationary_approximation (1 / 4)

example : |Real.sqrt (1 : ℝ)| ≤ Real.sqrt 10000 / 100 := by
  simpa only [Nat.cast_one] using
    sqrt_nat_small_frequency (T := 10000) (by norm_num) 1 (by norm_num)

example : ∃ C : ℝ, 0 < C ∧ ∀ T G L H : ℝ, 0 < T → 1 ≤ G → G ^ 2 ≤ 2 * T →
    1 ≤ L → 8 * L ≤ G → 0 < H → H ≤ Real.sqrt T / 12 →
    ∀ n : ℕ, 10000 * (n : ℝ) ≤ T →
    ‖atkinsonPowerIntegral T G L (1 / 4) (Real.sqrt n) -
      atkinsonFiniteStationaryMain T G L (1 / 4) (Real.sqrt n) H‖ ≤
        C * G * T ^ (-(1 / 4 : ℝ)) *
          (4 / (H * Real.pi) + 4 * (G / Real.sqrt T) * H ^ 2 + 432 * H ^ 4 / Real.sqrt T) ∧
    ‖atkinsonPowerIntegral T G L (1 / 4) (-Real.sqrt n) -
      atkinsonFiniteStationaryMain T G L (1 / 4) (-Real.sqrt n) H‖ ≤
        C * G * T ^ (-(1 / 4 : ℝ)) *
          (4 / (H * Real.pi) + 4 * (G / Real.sqrt T) * H ^ 2 + 432 * H ^ 4 / Real.sqrt T) :=
  exists_atkinsonPowerIntegral_small_n_pair_approximation (1 / 4)

end AtkinsonStationaryRegression

section FresnelStationaryRegression

open TaoTrudgianYang2025 Complex MeasureTheory Set Filter
open scoped Topology

example (c x : ℝ) : fresnelDampedKernel 0 c x =
    Complex.exp (((-2 * Real.pi * c * x ^ 2 : ℝ) : ℂ) * I) :=
  fresnelDampedKernel_zero c x

example (ε c x : ℝ) : fresnelDampedKernel ε c (-x) = fresnelDampedKernel ε c x :=
  fresnelDampedKernel_neg ε c x

example (x : ℝ) : ‖fresnelDampedKernel 0 1 x‖ ≤ 1 :=
  norm_fresnelDampedKernel (by norm_num) 1 x

example : ‖∫ x in (1 : ℝ)..2, fresnelDampedKernel 0 1 x‖ ≤ 1 / Real.pi := by
  simpa only [one_mul] using norm_integral_fresnelDampedKernel_le
    (ε := 0) (c := 1) (a := 1) (b := 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example (c H : ℝ) : Continuous
    (fun ε : ℝ => ∫ x in (-H)..H, fresnelDampedKernel ε c x) :=
  continuous_fresnelDampedWindow c H

example : fresnelGaussianValue 1 = (1 - I) / 2 := by
  simpa using fresnelGaussianValue_eq_cartesian (c := 1) (by norm_num)

example : ‖fresnelGaussianValue 1‖ = 1 / Real.sqrt 2 := by
  simpa only [mul_one] using norm_fresnelGaussianValue (c := 1) (by norm_num)

example : ‖atkinsonQuadraticWindow 1 1 - fresnelGaussianValue 1‖ ≤ 2 / Real.pi := by
  simpa only [one_mul] using norm_atkinsonQuadraticWindow_sub_gaussianValue_le
    (c := 1) (H := 1) (by norm_num) (by norm_num)

example : Tendsto (atkinsonQuadraticWindow 1) atTop
    (𝓝 (Complex.exp (((-Real.pi / 4 : ℝ) : ℂ) * I) / (Real.sqrt 2 : ℂ))) := by
  simpa only [mul_one] using tendsto_atkinsonQuadraticWindow (c := 1) (by norm_num)

example : Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * I) *
    Complex.exp (((-Real.pi / 4 : ℝ) : ℂ) * I) = 1 := by
  simpa using exp_positive_saddle_mul_fresnel 0

example : Complex.exp (((-Real.pi / 4 : ℝ) : ℂ) * I) *
    Complex.exp (((-Real.pi / 4 : ℝ) : ℂ) * I) = -I := by
  simpa only [neg_zero, zero_sub, neg_div, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, mul_one] using exp_negative_saddle_mul_fresnel 0

example (n : ℕ) : atkinsonStationaryMain 32 8 1 (1 / 4) (Real.sqrt n) =
    (2 * atkinsonSaddleProfile 32 8 1 (1 / 4) (Real.sqrt n) * atkinsonSaddleGaussian 32 8 n *
      Complex.exp ((atkinsonCentralPhase 32 : ℂ) * I) * (-1 : ℂ) ^ n *
        Complex.exp ((atkinsonSourcePhase 32 n : ℂ) * I)) /
          (Real.sqrt (2 * atkinsonSaddleCurvature 32 (Real.sqrt n)) : ℂ) :=
  atkinsonStationaryMain_sqrt (by norm_num) 8 1 (1 / 4) n

example (n : ℕ) : atkinsonStationaryMain 32 8 1 (1 / 4) (-Real.sqrt n) =
    ((-I) * 2 * atkinsonSaddleProfile 32 8 1 (1 / 4) (-Real.sqrt n) * atkinsonSaddleGaussian 32 8 n *
      Complex.exp ((atkinsonCentralPhase 32 : ℂ) * I) * (-1 : ℂ) ^ n *
        Complex.exp ((-atkinsonSourcePhase 32 n : ℂ) * I)) /
          (Real.sqrt (2 * atkinsonSaddleCurvature 32 (-Real.sqrt n)) : ℂ) :=
  atkinsonStationaryMain_neg_sqrt (by norm_num) (by norm_num) 1 (1 / 4) n

example : (4 : ℝ) / ((1 / 12) * Real.pi) + 4 * (1 / 1) * (1 / 12) ^ 2 +
    432 * (1 / 12) ^ 4 / 1 ≤ 20 / 1 :=
  atkinsonStationary_error_le_of_power_balance (S := 1) (G := 1) (X := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : ∃ C : ℝ, 0 < C ∧ ∀ T G L b : ℝ, 1 ≤ T → 1 ≤ G →
    G ≤ T ^ (1 / 2 - 3 * (1 / 10 : ℝ)) → 1 ≤ L → 8 * L ≤ G →
    |b| ≤ Real.sqrt T / 100 →
    ‖atkinsonPowerIntegral T G L (1 / 4) b - atkinsonStationaryMain T G L (1 / 4) b‖ ≤
      C * G * T ^ (-(1 / 4 : ℝ)) * T ^ (-(1 / 10 : ℝ)) := by
  obtain ⟨C, hC, h⟩ := exists_atkinsonPowerIntegral_small_frequency_power_saving (1 / 4)
  exact ⟨C, hC, fun T G L b => h (1 / 10) T G L b (by norm_num) le_rfl⟩

example {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) → ∀ n : ℕ, 10000 * (n : ℝ) ≤ T →
      ‖atkinsonPowerIntegral T G (Real.log T) (1 / 4) (Real.sqrt n) -
        atkinsonStationaryMain T G (Real.log T) (1 / 4) (Real.sqrt n)‖ ≤
          C * G * T ^ (-(1 / 4 : ℝ)) * T ^ (-min (δ / 3) (1 / 10)) ∧
      ‖atkinsonPowerIntegral T G (Real.log T) (1 / 4) (-Real.sqrt n) -
        atkinsonStationaryMain T G (Real.log T) (1 / 4) (-Real.sqrt n)‖ ≤
          C * G * T ^ (-(1 / 4 : ℝ)) * T ^ (-min (δ / 3) (1 / 10)) :=
  exists_atkinsonPowerIntegral_source_power_saving (1 / 4) hδ

end FresnelStationaryRegression

section AtkinsonSourceBandRegression

open TaoTrudgianYang2025 Complex MeasureTheory Set Filter

example (x : ℝ) : Real.arsinh |x| = |Real.arsinh x| := arsinh_abs x

example : Real.log (zetaDivisorBandEdge 32 8 0) = Real.log (32 / (2 * Real.pi)) := by
  simpa using log_zetaDivisorBandEdge (by norm_num : (0 : ℝ) < 32) 8 0

example :
    zetaDivisorBandCutoff 32 8 1 (zetaDivisorBandEdge 32 8 (-2 * 1)) = 0 ∧
    zetaDivisorBandCutoff 32 8 1 (zetaDivisorBandEdge 32 8 (2 * 1)) = 0 :=
  zetaDivisorBandCutoff_endpoints (by norm_num) (by norm_num) (by norm_num)

example : atkinsonPowerWeight 32 8 1 (1 / 4) (atkinsonRootBandLower 32 8 1 ^ 2) = 0 ∧
    atkinsonPowerWeight 32 8 1 (1 / 4) (atkinsonRootBandUpper 32 8 1 ^ 2) = 0 :=
  atkinsonPowerWeight_rootBand_endpoints (by norm_num) (by norm_num) (by norm_num) (1 / 4)

example : atkinsonRootBandLower 32 8 1 ≤ atkinsonRootBandUpper 32 8 1 :=
  atkinsonRootBand_order (by norm_num) (by norm_num) (by norm_num)

example : atkinsonRootBandUpper 32 8 1 - atkinsonRootBandLower 32 8 1 ≤
    4 * Real.sqrt 32 * (1 / 8) :=
  atkinsonRootBand_length_le (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example (b : ℝ) : atkinsonPowerIntegral 32 8 1 (1 / 4) b =
    2 * ∫ y in atkinsonRootBandLower 32 8 1..atkinsonRootBandUpper 32 8 1,
      atkinsonPowerWeight 32 8 1 (1 / 4) (y ^ 2) * atkinsonRootKernel 32 b y :=
  atkinsonPowerIntegral_eq_root_band (by norm_num) (by norm_num) (by norm_num) (1 / 4) b

example : atkinsonStationaryMain 32 8 1 (1 / 4) (Real.sqrt 5) = 0 ∧
    atkinsonStationaryMain 32 8 1 (1 / 4) (-Real.sqrt 5) = 0 :=
  atkinsonStationaryMain_pair_eq_zero_of_index (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (1 / 4) 5 (by norm_num)

example {y : ℝ} (hy : y ∈ Icc (atkinsonRootBandLower 32 8 1) (atkinsonRootBandUpper 32 8 1)) :
    6 * Real.sqrt 32 * (1 / 8) ≤ atkinsonRootSlope 32 (6 * Real.sqrt 32 * (1 / 8)) y ∧
      atkinsonRootSlope 32 (-(6 * Real.sqrt 32 * (1 / 8))) y ≤ -(6 * Real.sqrt 32 * (1 / 8)) :=
  atkinsonRootSlope_outside_band (by norm_num) (by norm_num) (by norm_num) (by norm_num) hy le_rfl

example (b : ℝ) : |deriv (atkinsonRootSlope 32 b) (Real.sqrt 32 / 4)| ≤ 8 ∧
    |iteratedDeriv 2 (atkinsonRootSlope 32 b) (Real.sqrt 32 / 4)| ≤ 64 / Real.sqrt 32 :=
  atkinsonRootSlope_derivative_bounds (by norm_num) le_rfl b

example : 32 * (8 / Real.sqrt 32) +
    (atkinsonRootBandUpper 32 8 1 - atkinsonRootBandLower 32 8 1) *
      (32 * (8 / Real.sqrt 32)) ^ 2 ≤ 4128 * 1 * (8 / Real.sqrt 32) :=
  atkinsonRootBand_derivative_bracket (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : ∃ C : ℝ, 0 < C ∧
    ‖atkinsonPowerIntegral 32 8 1 (1 / 4) (Real.sqrt 18)‖ ≤
      C * 8 ^ 2 * (32 : ℝ) ^ (-(1 / 4 : ℝ)) * 1 / (Real.sqrt 32 * 18) ∧
    ‖atkinsonPowerIntegral 32 8 1 (1 / 4) (-Real.sqrt 18)‖ ≤
      C * 8 ^ 2 * (32 : ℝ) ^ (-(1 / 4 : ℝ)) * 1 / (Real.sqrt 32 * 18) := by
  obtain ⟨C, hC, h⟩ := exists_norm_atkinsonPowerIntegral_index_band_secondOrder_le (1 / 4)
  exact ⟨C, hC, h 32 8 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) 18 (by norm_num)⟩

example : ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 1 ≤ T → 1 ≤ G → G ^ 2 ≤ 2 * T →
    1 ≤ L → 8 * L ≤ G → ∀ N : ℕ, 36 * T * (L / G) ^ 2 ≤ (N : ℝ) →
    ‖atkinsonLeadingSum T G L - atkinsonLeadingFiniteSum T G L N‖ ≤
      C * G ^ 2 * L * T ^ (-(3 / 4 : ℝ)) :=
  exists_norm_atkinsonLeadingSum_sub_band_finite_le

example : (1 : ℝ) ^ 2 * 1 * (1 : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 2 * 1 :=
  atkinsonBand_tail_scale_le (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : atkinsonSourceCutoff 32 8 1 = 18 := by norm_num [atkinsonSourceCutoff]

example : atkinsonSourceCutoff 40000 1200 1 = 1 := by norm_num [atkinsonSourceCutoff]

example : 10000 * (atkinsonSourceCutoff 40000 1200 1 : ℝ) ≤ 40000 :=
  atkinsonSourceCutoff_le_small (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : atkinsonStationaryMain 32 8 1 (1 / 4) (Real.sqrt 18) = 0 ∧
    atkinsonStationaryMain 32 8 1 (1 / 4) (-Real.sqrt 18) = 0 := by
  apply atkinsonStationaryMain_pair_eq_zero_after_cutoff (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (1 / 4) 18
  norm_num [atkinsonSourceCutoff]

example {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, ∀ G : ℝ, T ^ δ ≤ G →
      10000 * (atkinsonSourceCutoff T G (Real.log T) : ℝ) ≤ T :=
  eventually_atkinsonSourceCutoff_small hδ

example {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      ∀ N : ℕ, 36 * T * (Real.log T / G) ^ 2 ≤ (N : ℝ) →
      |(∫ t : ℝ, zetaGaussianWeight T G t * zetaMomentCriticalNorm t ^ 2) -
        2 * (atkinsonLeadingFiniteSum T G (Real.log T) N).re| ≤ C * G * Real.log T :=
  exists_zetaSquarePhysicalGaussian_atkinson_band_approximation hδ

example {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      ∀ N : ℕ, 36 * T * (Real.log T / G) ^ 2 ≤ (N : ℝ) →
      (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
        2 * Real.exp 1 * (atkinsonLeadingFiniteSum T G (Real.log T) N).re +
          C * G * Real.log T :=
  exists_zetaSquareLocalMean_le_atkinson_band hδ

example {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      ∀ n : ℕ, n < atkinsonSourceCutoff T G (Real.log T) →
      ‖atkinsonPowerIntegral T G (Real.log T) (1 / 4) (Real.sqrt n) -
        atkinsonStationaryMain T G (Real.log T) (1 / 4) (Real.sqrt n)‖ ≤
          C * G * T ^ (-(1 / 4 : ℝ)) * T ^ (-min (δ / 3) (1 / 10)) ∧
      ‖atkinsonPowerIntegral T G (Real.log T) (1 / 4) (-Real.sqrt n) -
        atkinsonStationaryMain T G (Real.log T) (1 / 4) (-Real.sqrt n)‖ ≤
          C * G * T ^ (-(1 / 4 : ℝ)) * T ^ (-min (δ / 3) (1 / 10)) :=
  exists_atkinsonSourceCutoff_carrier_approximation (1 / 4) hδ

end AtkinsonSourceBandRegression

section SymmetricStationarySumRegression

open Complex MeasureTheory

example {f : ℝ → ℂ} {M R r H : ℝ} (hH : 0 ≤ H)
    (hf : IntervalC2Bound f (r-H) (r+H) M R) :
    ‖f (r+H)-f r-((r+H-r : ℝ) : ℂ)*deriv f r‖ ≤ M*R^2*H^2 :=
  hf.norm_sub_linear_le hH le_rfl le_rfl (by
    simpa only [add_sub_cancel_left,abs_of_nonneg hH] using (le_rfl : H ≤ H))

example {f : ℝ → ℂ} {M R r H : ℝ} (hH : 0 ≤ H)
    (hf : IntervalC2Bound f (r-H) (r+H) M R) :
    ‖f (r-H)-f r-((r-H-r : ℝ) : ℂ)*deriv f r‖ ≤ M*R^2*H^2 :=
  hf.norm_sub_linear_le hH le_rfl le_rfl (by
    rw [show r-H-r = -H by ring,abs_neg,abs_of_nonneg hH])

example : ‖Complex.exp ((1:ℂ)*I)-1-(1:ℂ)*I‖ ≤ 3*(1:ℝ)^2 :=
  norm_exp_real_phase_sub_linear_le 1

example : ‖Complex.exp ((2:ℂ)*I)-1-(2:ℂ)*I‖ ≤ 3*(2:ℝ)^2 :=
  norm_exp_real_phase_sub_linear_le 2

example : |Real.log (1+(1/2:ℝ))-(1/2:ℝ)+(1/2:ℝ)^2/2-(1/2:ℝ)^3/3| ≤
    2*|(1/2:ℝ)|^4 :=
  abs_log_one_add_sub_cubic_le (by norm_num)

example : |Real.log (1+(-1/2:ℝ))-(-1/2:ℝ)+(-1/2:ℝ)^2/2-(-1/2:ℝ)^3/3| ≤
    2*|(-1/2:ℝ)|^4 :=
  abs_log_one_add_sub_cubic_le (by norm_num)

example (T b : ℝ) :
    (∫ y in (atkinsonSaddleRoot (T/(2*Real.pi)) b-1)..
      (atkinsonSaddleRoot (T/(2*Real.pi)) b+1),
        (((y-atkinsonSaddleRoot (T/(2*Real.pi)) b)^1 : ℝ) : ℂ) *
          atkinsonRootQuadraticKernel T b y) = 0 :=
  integral_atkinsonRootQuadratic_odd T b 1 (by decide)

example (T b : ℝ) :
    (∫ y in (atkinsonSaddleRoot (T/(2*Real.pi)) b-(-1))..
      (atkinsonSaddleRoot (T/(2*Real.pi)) b+(-1)),
        (((y-atkinsonSaddleRoot (T/(2*Real.pi)) b)^3 : ℝ) : ℂ) *
          atkinsonRootQuadraticKernel T b y) = 0 :=
  integral_atkinsonRootQuadratic_odd T b (-1) (by decide)

example : atkinsonSymmetricRadiusScale 1 1 = 1 := by
  norm_num [atkinsonSymmetricRadiusScale]

example : 1 ≤ atkinsonSymmetricRadiusScale 1 1 ∧
    1*(atkinsonSymmetricRadiusScale 1 1)^2 ≤ Real.sqrt 1 ∧
    (atkinsonSymmetricRadiusScale 1 1)^4 ≤ Real.sqrt 1 :=
  atkinsonSymmetricRadiusScale_balance (by norm_num) (by norm_num) (by norm_num)

example : 4/(((1:ℝ)/12)*Real.pi) + 4*1^2*((1:ℝ)/12)^3/1 +
    216*1*((1:ℝ)/12)^5/1 + 1296*((1:ℝ)/12)^5/1 +
      11664*((1:ℝ)/12)^7/1 ≤ 20/(1:ℝ) :=
  atkinsonSymmetric_error_le_of_power_balance (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

example : ‖divisorDirichletTerm (1/4) 0‖ ≤ (0:ℝ)^(3/4+1/8 : ℝ) *
    ‖divisorDirichletTerm ((1+1/8 : ℝ) : ℂ) 0‖ := by
  simpa only [Nat.cast_zero] using
    norm_divisorDirichletTerm_quarter_le_prefix (ε := 1/8) (N := 0) (n := 0)
      (by norm_num) (by norm_num)

example (T G L : ℝ) : atkinsonStationaryLeadingTerm T G L 0 = 0 :=
  atkinsonStationaryLeadingTerm_zero T G L

example : atkinsonStationaryLeadingTerm 32 8 1 18 = 0 := by
  apply atkinsonStationaryLeadingTerm_eq_zero_after_cutoff
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [atkinsonSourceCutoff]

example : HasSum (atkinsonStationaryLeadingTerm 32 8 1)
    (atkinsonStationaryLeadingFiniteSum 32 8 1 18) := by
  have h := hasSum_atkinsonStationaryLeadingTerm
    (T := 32) (G := 8) (L := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [atkinsonSourceCutoff] at h
  exact h

example : atkinsonStationaryLeadingSum 32 8 1 = atkinsonStationaryLeadingFiniteSum 32 8 1 18 := by
  have h := atkinsonStationaryLeadingSum_eq_finite
    (T := 32) (G := 8) (L := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [atkinsonSourceCutoff] at h
  exact h

example {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 1 ≤ T →
      T^(1/4 : ℝ) ≤ G → G ≤ Real.sqrt T → 1 ≤ L → 8*L ≤ G →
      ∀ N : ℕ, 10000*(N:ℝ) ≤ T →
      ‖atkinsonLeadingFiniteSum T G L N-atkinsonStationaryLeadingFiniteSum T G L N‖ ≤
        C*G*Real.sqrt G*T^(-(1/2 : ℝ))*(N:ℝ)^(3/4+ε) :=
  exists_norm_atkinsonLeadingFiniteSum_sub_stationary_le hε

example {T G L : ℝ} (hT : 1 ≤ T) (hG : 1 ≤ G)
    (hupper : G ≤ Real.sqrt T) (hL : 1 ≤ L) :
    G*Real.sqrt G*T^(-(1/2 : ℝ))*
      (atkinsonSourceCutoff T G L : ℝ)^(3/4 : ℝ) ≤
        37*T^((3/4:ℝ)-1/2)*L^2 :=
  atkinsonStationary_cutoff_scale_le hT hG hupper hL le_rfl (by norm_num)

example {T G L : ℝ} (hT : 1 ≤ T) (hG : 1 ≤ G)
    (hupper : G ≤ Real.sqrt T) (hL : 1 ≤ L) :
    G*Real.sqrt G*T^(-(1/2 : ℝ))*
      (atkinsonSourceCutoff T G L : ℝ)^(1 : ℝ) ≤
        37*T^((1:ℝ)-1/2)*L^2 :=
  atkinsonStationary_cutoff_scale_le hT hG hupper hL (by norm_num) le_rfl

example {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) → T^(1/4 : ℝ) ≤ G →
      ‖atkinsonLeadingSum T G (Real.log T)-atkinsonStationaryLeadingSum T G (Real.log T)‖ ≤
        C*(G+T^(1/4+ε)) :=
  exists_atkinsonLeadingSum_sub_stationary_bound hδ hε

example {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) → T^(1/4 : ℝ) ≤ G →
      |(∫ t : ℝ, zetaGaussianWeight T G t*zetaMomentCriticalNorm t^2) -
        2*(atkinsonStationaryLeadingSum T G (Real.log T)).re| ≤
          C*(G*Real.log T+T^(1/4+ε)) :=
  exists_zetaSquarePhysicalGaussian_stationary_approximation hδ hε

example {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) → T^(1/4 : ℝ) ≤ G →
      (∫ t in T-G..T+G, zetaMomentCriticalNorm t^2) ≤
        2*Real.exp 1*(atkinsonStationaryLeadingSum T G (Real.log T)).re +
          C*(G*Real.log T+T^(1/4+ε)) :=
  exists_zetaSquareLocalMean_le_stationary hδ hε

example {δ κ : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) → T^(1/4+κ) ≤ G →
      |(∫ t : ℝ, zetaGaussianWeight T G t*zetaMomentCriticalNorm t^2) -
        2*(atkinsonStationaryLeadingSum T G (Real.log T)).re| ≤ C*G*Real.log T :=
  exists_zetaSquarePhysicalGaussian_stationary_above_fourthRoot hδ hκ

example {δ κ : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) → T^(1/4+κ) ≤ G →
      (∫ t in T-G..T+G, zetaMomentCriticalNorm t^2) ≤
        2*Real.exp 1*(atkinsonStationaryLeadingSum T G (Real.log T)).re +
          C*G*Real.log T :=
  exists_zetaSquareLocalMean_le_stationary_above_fourthRoot hδ hκ

end SymmetricStationarySumRegression

section NormalizedMainAbelRegression

open TaoTrudgianYang2025 Complex MeasureTheory

example (T b : ℝ) : atkinsonCommonSaddleFactor T (-b) = atkinsonCommonSaddleFactor T b :=
  atkinsonCommonSaddleFactor_neg T b

example : 0 < atkinsonCommonSaddleFactor 1 0 :=
  atkinsonCommonSaddleFactor_pos (by norm_num) 0

example : atkinsonCommonSaddleFactor 1 (-1) =
    (1/Real.sqrt 2)*((-1:ℝ)^2+4*(1/(2*Real.pi)))^(-(1/4:ℝ)) :=
  atkinsonCommonSaddleFactor_eq_rpow (by norm_num) (-1)

example : (1:ℝ)^(-(1/4:ℝ))*(zetaAtkinsonSaddle 1 (-2)/1)^(-(1/4:ℝ)) /
    Real.sqrt (2*atkinsonSaddleCurvature 1 (-2)) = atkinsonCommonSaddleFactor 1 (-2) :=
  atkinsonSaddle_quarter_power_curvature (by norm_num) (-2)

example (G L : ℝ) :
    atkinsonSaddleProfile 1 G L (1/4) 0 / (Real.sqrt (2*atkinsonSaddleCurvature 1 0) : ℂ) =
      (atkinsonCommonSaddleFactor 1 0 : ℂ)*atkinsonSaddleResidual 1 G L 0*
        zetaSquareReflectedGammaPhase 1 :=
  atkinsonSaddleProfile_div_curvature (by norm_num) G L 0

example (T : ℝ) : atkinsonFourthRootCoefficient T 0 = 0 := by
  simp [atkinsonFourthRootCoefficient]

example : atkinsonFourthRootCoefficient 1 1 =
    (1/Real.sqrt 2)*(1:ℝ)^(-(1/4:ℝ))*(1+2*1/Real.pi)^(-(1/4:ℝ)) := by
  simpa only [Nat.cast_one] using atkinsonFourthRootCoefficient_eq (by norm_num : (0:ℝ)<1) 1

example : 2*Real.sqrt Real.pi*atkinsonBesselScale (1/4) 0 = 0 := by
  simpa only [Nat.cast_zero,Real.zero_rpow (by norm_num : -(1/4:ℝ) ≠ 0)] using
    atkinsonBesselScale_quarter_normalization 0

example : 2*Real.sqrt Real.pi*atkinsonBesselScale (1/4) 1 = 1 := by
  simpa only [Nat.cast_one,Real.one_rpow] using atkinsonBesselScale_quarter_normalization 1

example (T G L : ℝ) : atkinsonStationaryLeadingTerm T G L 0 = 0 :=
  atkinsonStationaryLeadingTerm_zero T G L

example (L : ℝ) : atkinsonStationaryLeadingTerm 1 1 L 2 = atkinsonCommonMainPhase 1 *
    (atkinsonPositiveMainWeight 1 1 L 2*atkinsonPositivePhaseTerm 1 2-
      atkinsonNegativeMainWeight 1 1 L 2*atkinsonNegativePhaseTerm 1 2) :=
  atkinsonStationaryLeadingTerm_eq_signed (by norm_num) (by norm_num) L 2

example (L : ℝ) : atkinsonStationaryLeadingFiniteSum 1 1 L 0 = atkinsonCommonMainPhase 1 *
    (atkinsonPositiveMainSum 1 1 L 0-atkinsonNegativeMainSum 1 1 L 0) :=
  atkinsonStationaryLeadingFiniteSum_eq_signed (by norm_num) (by norm_num) L 0

example : atkinsonNegativePhaseTerm 0 1 = (starRingEnd ℂ) (atkinsonPositivePhaseTerm 0 1) :=
  atkinsonNegativePhaseTerm_eq_conj 0 1

example (T : ℝ) : ‖∑ n ∈ Finset.range 0, atkinsonNegativePhaseTerm T n‖ =
    ‖atkinsonPhasePartialSum T 0‖ := norm_atkinsonNegativePhaseSum T 0

example (w a : ℕ → ℂ) : ‖∑ n ∈ Finset.range 0, w n*a n‖ ≤
    ‖w (0-1)‖*‖∑ n ∈ Finset.range 0, a n‖+
      ∑ n ∈ Finset.range (0-1),
        ‖w (n+1)-w n‖*‖∑ k ∈ Finset.range (n+1), a k‖ :=
  norm_sum_mul_le_discrete_parts w a 0

example (w a : ℕ → ℂ) : ‖w 0*a 0‖ ≤ ‖w 0‖*‖a 0‖ := by
  simpa only [Nat.sub_self,Finset.sum_range_zero,Finset.sum_range_one,add_zero] using
    norm_sum_mul_le_discrete_parts w a 1

example (T G L : ℝ) : atkinsonMainAbelBound T G L 0 = 0 := by
  simp [atkinsonMainAbelBound,atkinsonPhasePartialSum]

example (T G L : ℝ) : atkinsonMainAbelBound T G L 1 = 0 := by
  simp [atkinsonMainAbelBound,atkinsonPhasePartialSum,atkinsonPositivePhaseTerm,
    RiemannZeta.GuthMaynard.divisorWeight]

example (T G L : ℝ) : 0 ≤ atkinsonMainAbelBound T G L 2 :=
  atkinsonMainAbelBound_nonneg T G L 2

example :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (n:ℝ) ≤ 64 →
      ‖atkinsonPositiveMainWeight 64 8 1 n‖ ≤
        C*8*(64:ℝ)^(-(1/4:ℝ))*(n:ℝ)^(-(1/4:ℝ))*Real.exp (-(8^2*(n:ℝ))/(12*64)) ∧
      ‖atkinsonNegativeMainWeight 64 8 1 n‖ ≤
        C*8*(64:ℝ)^(-(1/4:ℝ))*(n:ℝ)^(-(1/4:ℝ))*Real.exp (-(8^2*(n:ℝ))/(12*64)) := by
  obtain ⟨C,hC,h⟩ := exists_norm_atkinsonMainWeights_le
  exact ⟨C,hC,h 64 8 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)⟩

example {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) → T^(1/4:ℝ) ≤ G →
      (∫ t in T-G..T+G, zetaMomentCriticalNorm t^2) ≤
        4*Real.exp 1*atkinsonMainAbelBound T G (Real.log T) (atkinsonSourceCutoff T G (Real.log T))+
          C*(G*Real.log T+T^(1/4+ε)) :=
  exists_zetaSquareLocalMean_le_mainAbel hδ hε

example {δ κ : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) → T^(1/4+κ) ≤ G →
      (∫ t in T-G..T+G, zetaMomentCriticalNorm t^2) ≤
        4*Real.exp 1*atkinsonMainAbelBound T G (Real.log T) (atkinsonSourceCutoff T G (Real.log T))+
          C*G*Real.log T :=
  exists_zetaSquareLocalMean_le_mainAbel_above_fourthRoot hδ hκ

example {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) → T^(1/4 : ℝ) ≤ G →
      |(∫ t : ℝ, zetaGaussianWeight T G t*zetaMomentCriticalNorm t^2) -
        2*(atkinsonCommonMainPhase T *
          (atkinsonPositiveMainSum T G (Real.log T) (atkinsonSourceCutoff T G (Real.log T))-
            atkinsonNegativeMainSum T G (Real.log T) (atkinsonSourceCutoff T G (Real.log T)))).re| ≤
          C*(G*Real.log T+T^(1/4+ε)) :=
  exists_zetaSquarePhysicalGaussian_signedMain_approximation hδ hε

example {δ κ : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) → T^(1/4+κ) ≤ G →
      |(∫ t : ℝ, zetaGaussianWeight T G t*zetaMomentCriticalNorm t^2) -
        2*(atkinsonCommonMainPhase T *
          (atkinsonPositiveMainSum T G (Real.log T) (atkinsonSourceCutoff T G (Real.log T))-
            atkinsonNegativeMainSum T G (Real.log T) (atkinsonSourceCutoff T G (Real.log T)))).re| ≤
          C*G*Real.log T :=
  exists_zetaSquarePhysicalGaussian_signedMain_above_fourthRoot hδ hκ

end NormalizedMainAbelRegression

section DampedWeightVariationRegression

open TaoTrudgianYang2025 Complex

example : FiniteVariationBound (fun _ => (I:ℂ)) 0 1 := by
  simpa only [Complex.norm_I] using finiteVariationBound_const I 0

example : FiniteVariationBound (fun _ => (I:ℂ)) 3 1 := by
  simpa only [Complex.norm_I] using finiteVariationBound_const I 3

example : FiniteVariationBound (fun _ => (I:ℂ)*(-I)) 3 2 := by
  simpa only [Complex.norm_I,norm_neg,mul_one] using
    (finiteVariationBound_const I 3).mul (finiteVariationBound_const (-I) 3)

example : FiniteVariationBound (fun i : ℕ => ((i:ℝ):ℂ)) 1 1 := by
  apply finiteVariationBound_of_monotone (by norm_num)
    (fun i _ j _ hij => by exact_mod_cast hij)
  intro i hi
  exact ⟨Nat.cast_nonneg i,by exact_mod_cast hi⟩

example : FiniteVariationBound (fun i : ℕ => ((1-(i:ℝ):ℝ):ℂ)) 1 1 := by
  apply finiteVariationBound_of_antitone (by norm_num)
    (fun i _ j _ hij => sub_le_sub_left (by exact_mod_cast hij) 1)
  intro i hi
  have h : (i:ℝ) ≤ 1 := by exact_mod_cast hi
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) i]

example (G : ℝ) : quadraticFrequencyEnvelope G 0 = 1 := by
  simp [quadraticFrequencyEnvelope]

example :
    ‖zetaGaussianQuadraticIntegral 1 1 0-zetaGaussianQuadraticIntegral 1 1 0‖ ≤
      2*Real.sqrt Real.pi*1*(quadraticFrequencyEnvelope 1 0-quadraticFrequencyEnvelope 1 0) :=
  norm_quadraticGaussian_increment_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) le_rfl

example (T : ℝ) : atkinsonSaddleFrequency T 0 = 0 := by
  simp [atkinsonSaddleFrequency]

example : FiniteVariationBound (fun i => atkinsonSaddleGaussian 1 1 (0+i)) 10
    (2*Real.sqrt Real.pi) := by
  simpa only [Nat.cast_zero,mul_zero,neg_zero,zero_div,Real.exp_zero,mul_one] using
    finiteVariationBound_atkinsonSaddleGaussian_physical (by norm_num : (0:ℝ)<1)
      (by norm_num : (0:ℝ)<1) (by norm_num) 0 10 (by norm_num)

example (G : ℝ) : quadraticFrequencyEnvelope G (atkinsonSaddleFrequency 1 0) ≤ 1 := by
  simpa only [Nat.cast_zero,mul_zero,neg_zero,zero_div,Real.exp_zero] using
    quadraticFrequencyEnvelope_saddle_le_physical (by norm_num : (0:ℝ)<1) G 0 (by norm_num)

example : atkinsonSaddleRoot 1 (-1)-1/atkinsonSaddleRoot 1 (-1) = -1 :=
  atkinsonSaddleRoot_inverse_identity (by norm_num) (-1)

example : zetaAtkinsonSaddle 1 (-1) ≤ zetaAtkinsonSaddle 1 1 :=
  zetaAtkinsonSaddle_monotone (by norm_num) (by norm_num)

example : Monotone (atkinsonPositiveRootSample 1 0) :=
  atkinsonPositiveRootSample_monotone (by norm_num) 0

example : Antitone (atkinsonNegativeRootSample 1 0) :=
  atkinsonNegativeRootSample_antitone (by norm_num) 0

example : atkinsonPositiveRootSample 20000 1 1 ∈ Set.Icc (1/4) 1 ∧
    atkinsonNegativeRootSample 20000 1 1 ∈ Set.Icc (1/4) 1 :=
  atkinsonRootSample_mem (by norm_num) 1 1 (by norm_num) 1 le_rfl

example : zetaMainMellinProfile (zetaAtkinsonSaddle 1 0/1) =
    atkinsonPowerProfile 0 ((atkinsonSaddleRoot (1/(2*Real.pi)) 0/Real.sqrt 1)^2) :=
  zetaMainMellinProfile_saddle_eq_root (by norm_num) 0

example :
    FiniteVariationBound (fun i => (zetaDivisorBandCutoff 1 1 100
      (zetaAtkinsonSaddle 1 (Real.sqrt ((0+i:ℕ):ℝ))) : ℂ)) 2 2 ∧
    FiniteVariationBound (fun i => (zetaDivisorBandCutoff 1 1 100
      (zetaAtkinsonSaddle 1 (-Real.sqrt ((0+i:ℕ):ℝ))) : ℂ)) 2 2 :=
  finiteVariationBound_saddleCutoff (by norm_num) (by norm_num) (by norm_num) 0 2

example : atkinsonFourthRootCoefficient 1 2 ≤ atkinsonFourthRootCoefficient 1 1 :=
  atkinsonFourthRootCoefficient_antitone (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example :
    ∃ C : ℝ, 0 < C ∧
      FiniteVariationBound (fun i => atkinsonPositiveMainWeight 20000 200 1 (1+i)) 1
        (C*200*(20000:ℝ)^(-(1/4:ℝ))*(1:ℝ)^(-(1/4:ℝ))*Real.exp (-(200^2*1)/(12*20000))) ∧
      FiniteVariationBound (fun i => atkinsonNegativeMainWeight 20000 200 1 (1+i)) 1
        (C*200*(20000:ℝ)^(-(1/4:ℝ))*(1:ℝ)^(-(1/4:ℝ))*Real.exp (-(200^2*1)/(12*20000))) := by
  obtain ⟨C,hC,h⟩ := exists_finiteVariationBound_atkinsonMainWeights
  refine ⟨C,hC,?_⟩
  simpa only [Nat.cast_one] using h 20000 200 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) 1 1 (by norm_num) (by norm_num)

example (T : ℝ) (m : ℕ) : atkinsonPhaseBlockMax T m 0 = 0 := by
  simp [atkinsonPhaseBlockMax,atkinsonPhaseBlockSum]

example (T G L : ℝ) (m : ℕ) : atkinsonStationaryBlock T G L m 0 = 0 := by
  simp [atkinsonStationaryBlock]

example (T : ℝ) : ‖atkinsonPhaseBlockSum T 1 2‖ ≤ atkinsonPhaseBlockMax T 1 2 :=
  norm_atkinsonPhaseBlockSum_le_max T 1 2 2 le_rfl

example :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 0 < T → 0 < G → G^2 ≤ 2*T → 0 < L →
      ∀ m N : ℕ, 0 < m → 10000*((m+N:ℕ):ℝ) ≤ T →
      ‖atkinsonStationaryBlock T G L m N‖ ≤
        C*G*T^(-(1/4:ℝ))*(m:ℝ)^(-(1/4:ℝ))*Real.exp (-(G^2*(m:ℝ))/(12*T))*
          atkinsonPhaseBlockMax T m N :=
  exists_norm_atkinsonStationaryBlock_le

example {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) →
      ∀ m N : ℕ, 0 < m → m+N ≤ atkinsonSourceCutoff T G (Real.log T) →
      ‖atkinsonStationaryBlock T G (Real.log T) m N‖ ≤
        C*G*T^(-(1/4:ℝ))*(m:ℝ)^(-(1/4:ℝ))*Real.exp (-(G^2*(m:ℝ))/(12*T))*
          atkinsonPhaseBlockMax T m N :=
  exists_atkinsonSourceCutoff_block_bound hδ

end DampedWeightVariationRegression

section TruncatedDyadicSourceRegression

open Complex MeasureTheory

example : Nat.clog 2 0 = 0 := by decide
example : Nat.clog 2 1 = 0 := by decide
example : Nat.clog 2 8 = 3 := by decide
example : Nat.clog 2 9 = 4 := by decide
example : truncatedDyadicLength 5 2 = 1 := by decide
example : truncatedDyadicLength 8 2 = 4 := by decide
example : truncatedDyadicLength 9 3 = 1 := by decide
example : truncatedDyadicLength 0 3 = 0 := by decide

example : 2^1+truncatedDyadicLength 3 1 ≤ 3 :=
  truncatedDyadic_endpoint_le (by decide)

example {N j : ℕ} (hj : j < Nat.clog 2 N) : 2^j < N :=
  truncatedDyadic_start_lt hj

example {N j : ℕ} (hj : 2^(j+1) ≤ N) : truncatedDyadicLength N j = 2^j :=
  truncatedDyadicLength_eq_width hj

example (f : ℕ → ℂ) (hf : f 0 = 0) (N : ℕ) :
    (∑ i ∈ Finset.range N, f i) =
      ∑ j ∈ Finset.range (Nat.clog 2 N),
        ∑ i ∈ Finset.range (truncatedDyadicLength N j), f (2^j+i) :=
  sum_range_eq_truncatedDyadic f hf N

example (T G L : ℝ) : atkinsonStationaryLeadingFiniteSum T G L 0 = 0 := by
  rw [atkinsonStationaryLeadingFiniteSum_eq_dyadic]
  simp

example (T G L : ℝ) : atkinsonStationaryLeadingFiniteSum T G L 1 = 0 := by
  rw [atkinsonStationaryLeadingFiniteSum_eq_dyadic]
  simp

example (T G L : ℝ) :
    atkinsonStationaryLeadingFiniteSum T G L 3 =
      atkinsonStationaryBlock T G L 1 1+atkinsonStationaryBlock T G L 2 1 := by
  have h := atkinsonStationaryLeadingFiniteSum_eq_dyadic T G L 3
  rw [show Nat.clog 2 3 = 2 by decide] at h
  norm_num [Finset.sum_range_succ,truncatedDyadicLength] at h
  exact h

example (T G : ℝ) : atkinsonDyadicPhaseBound T G 1 = 0 := by
  simp [atkinsonDyadicPhaseBound]

example (T G : ℝ) : atkinsonFullDyadicPhaseBound T G 0 = 0 := by
  simp [atkinsonFullDyadicPhaseBound]

example (T : ℝ) (m N : ℕ) :
    atkinsonPhaseBlockMax T m N ≤ atkinsonPhaseBlockMax T m (N+1) :=
  atkinsonPhaseBlockMax_mono T m (Nat.le_succ N)

example {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) →
      ‖atkinsonStationaryLeadingSum T G (Real.log T)‖ ≤
        C*G*T^(-(1/4:ℝ))*
          atkinsonDyadicPhaseBound T G (atkinsonSourceCutoff T G (Real.log T)) :=
  exists_norm_atkinsonStationarySum_le_dyadic hδ

example {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) →
      ‖atkinsonStationaryLeadingSum T G (Real.log T)‖ ≤
        C*G*T^(-(1/4:ℝ))*
          atkinsonFullDyadicPhaseBound T G (atkinsonSourceCutoff T G (Real.log T)) :=
  exists_norm_atkinsonStationarySum_le_fullDyadic hδ

example {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) → T^(1/4 : ℝ) ≤ G →
      (∫ t : ℝ, zetaGaussianWeight T G t*zetaMomentCriticalNorm t^2) ≤
        C*(G*T^(-(1/4:ℝ))*
          atkinsonFullDyadicPhaseBound T G (atkinsonSourceCutoff T G (Real.log T))+
            (G*Real.log T+T^(1/4+ε))) :=
  exists_zetaSquarePhysicalGaussian_le_dyadic hδ hε

example {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) → T^(1/4 : ℝ) ≤ G →
      (∫ t in T-G..T+G, zetaMomentCriticalNorm t^2) ≤
        C*(G*T^(-(1/4:ℝ))*
          atkinsonFullDyadicPhaseBound T G (atkinsonSourceCutoff T G (Real.log T))+
            (G*Real.log T+T^(1/4+ε))) :=
  exists_zetaSquareLocalMean_le_dyadic hδ hε

example {δ κ : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) → T^(1/4+κ) ≤ G →
      (∫ t : ℝ, zetaGaussianWeight T G t*zetaMomentCriticalNorm t^2) ≤
        C*(G*T^(-(1/4:ℝ))*
          atkinsonFullDyadicPhaseBound T G (atkinsonSourceCutoff T G (Real.log T))+
            (G*Real.log T)) :=
  exists_zetaSquarePhysicalGaussian_le_dyadic_above_fourthRoot hδ hκ

example {δ κ : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) → T^(1/4+κ) ≤ G →
      (∫ t in T-G..T+G, zetaMomentCriticalNorm t^2) ≤
        C*(G*T^(-(1/4:ℝ))*
          atkinsonFullDyadicPhaseBound T G (atkinsonSourceCutoff T G (Real.log T))+
            (G*Real.log T)) :=
  exists_zetaSquareLocalMean_le_dyadic_above_fourthRoot hδ hκ

end TruncatedDyadicSourceRegression

section HeightDependentPrefixGramRegression

open Complex
open scoped ComplexConjugate

example (f : ℕ → ℂ) :
    (∑ i ∈ Finset.range 3, if i < 0 then f i else 0) = 0 := by
  simpa only [Finset.sum_range_zero] using sum_range_prefix_mask f (by norm_num : 0 ≤ 3)

example (t u : ℝ) :
    (∑ i ∈ Finset.range 3,
      conj (atkinsonMaskedPhaseVector t 2 1 i)*atkinsonMaskedPhaseVector u 2 3 i) =
        atkinsonPrefixGram 2 1 t u := by
  simpa only [show min 1 3 = 1 by decide] using
    atkinsonMaskedPhaseVector_gram 2 3 (j := 1) (k := 3) (by decide) t u

example (t u : ℝ) :
    (∑ i ∈ Finset.range 3,
      conj (atkinsonMaskedPhaseVector t 2 0 i)*atkinsonMaskedPhaseVector u 2 3 i) = 0 := by
  simpa [atkinsonPrefixGram] using
    atkinsonMaskedPhaseVector_gram 2 3 (j := 0) (k := 3) (by decide) t u

example (t u : ℝ) :
    atkinsonPrefixGram 2 2 u t = conj (atkinsonPrefixGram 2 2 t u) :=
  atkinsonPrefixGram_swap 2 2 t u

example (t : ℝ) : ‖atkinsonPrefixGram 1 0 t t‖ = (0:ℝ) := by
  simpa only [Nat.cast_zero] using norm_atkinsonPrefixGram_self 1 0 t

example (t : ℝ) : ‖atkinsonPrefixGram 1 3 t t‖ = (3:ℝ) :=
  norm_atkinsonPrefixGram_self 1 3 t

example (t : ℝ) : atkinsonPrefixGramMax 1 3 t t = (3:ℝ) :=
  atkinsonPrefixGramMax_self 1 3 t

example (t u : ℝ) : atkinsonPrefixGramMax 1 0 t u = 0 := by
  simp [atkinsonPrefixGramMax,atkinsonPrefixGram]

example (t : ℝ) (m N : ℕ) :
    atkinsonPhaseBlockMax t m N = ‖atkinsonPhaseBlockSum t m (atkinsonMaximizingPrefix m N t)‖ :=
  atkinsonMaximizingPrefix_spec m N t

example (t : ℝ) : atkinsonMaximizingPrefix 1 0 t = 0 :=
  Nat.eq_zero_of_le_zero (atkinsonMaximizingPrefix_le 1 0 t)

example : atkinsonBlockCoefficientEnergy 1 0 = 0 := by
  simp [atkinsonBlockCoefficientEnergy]

example : atkinsonBlockCoefficientEnergy 1 2 = 5 := by
  have hd : (Nat.divisors 2).card = 2 := by decide
  norm_num [atkinsonBlockCoefficientEnergy,divisorWeight,Finset.sum_range_succ,hd]

example (m N : ℕ) :
    (((∅ : Finset ℝ).card : ℝ)*1)^2 ≤ atkinsonBlockCoefficientEnergy m N*
      ∑ t ∈ (∅ : Finset ℝ), ∑ u ∈ (∅ : Finset ℝ), atkinsonPrefixGramMax m N t u :=
  card_mul_atkinsonPhaseBlockMax_lower_sq_le_gramMax m N ∅ (by norm_num) (by simp)

example :
    ∃ C : ℝ, 0 < C ∧ ∀ m N : ℕ, 0 < m → N ≤ m →
      atkinsonBlockCoefficientEnergy m N ≤ C*(m:ℝ)^(1+(1/10:ℝ)) :=
  exists_atkinsonBlockCoefficientEnergy_le (by norm_num)

example {T : ℝ} (hT : 0 < T) (N : ℕ) :
    atkinsonFullDyadicPhaseBound T 0 N ≤ atkinsonUndampedDyadicPhaseBound T N :=
  atkinsonFullDyadicPhaseBound_le_undamped hT 0 N

example (t : ℝ) : atkinsonUndampedDyadicPhaseBound t 0 = 0 := by
  simp [atkinsonUndampedDyadicPhaseBound]

example (W : Finset ℝ) : atkinsonDyadicGramBudget 0 W = 0 := by
  simp [atkinsonDyadicGramBudget]

example (G : ℝ) : atkinsonPacketCutoff G ∅ = 0 := by
  simp [atkinsonPacketCutoff]

example {H G : ℝ} {W : Finset ℝ} (hH : 1 ≤ H) (hG : 0 < G)
    (hrange : ∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) :
    atkinsonPacketCutoff G W ≤ atkinsonSourceCutoff (2*H) G (Real.log (2*H)) :=
  atkinsonPacketCutoff_le_height hH hG hrange

example (G t : ℝ) : atkinsonLocalMeanExcess G t 0 =
    max 0 (∫ u in t-G..t+G, zetaMomentCriticalNorm u^2) := by
  simp [atkinsonLocalMeanExcess]

example (m N : ℕ) (W : Finset ℝ) :
    (∑ t ∈ W, atkinsonPhaseBlockMax t m N)^2 ≤
      atkinsonBlockCoefficientEnergy m N*
        ∑ t ∈ W, ∑ u ∈ W,
          ‖atkinsonPrefixGram m
            (min (atkinsonMaximizingPrefix m N t) (atkinsonMaximizingPrefix m N u)) t u‖ :=
  sum_atkinsonPhaseBlockMax_sq_le_selectedGram m N W

example {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H G : ℝ, ∀ W : Finset ℝ,
      H₀ ≤ H → 0 < G →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ)) →
      (∑ t ∈ W, ‖atkinsonStationaryLeadingSum t G (Real.log t)‖)^2 ≤
        C*G^2*H^(-(1/2:ℝ))*
          atkinsonDyadicGramBudget (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W :=
  exists_atkinsonStationaryPacket_sq_le_physicalGram hδ

example
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4 : ℝ) ≤ G) →
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*(G*Real.log t+t^(1/4+ε))))^2 ≤
        D*G^2*H^(-(1/2:ℝ))*
          atkinsonDyadicGramBudget (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W :=
  exists_atkinsonLocalMeanExcessPacket_sq_le_physicalGram hδ hε

example
    {δ κ : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*G*Real.log t))^2 ≤
        D*G^2*H^(-(1/2:ℝ))*
          atkinsonDyadicGramBudget (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W :=
  exists_atkinsonLocalMeanExcessPacket_sq_le_physicalGram_above_fourthRoot hδ hκ

end HeightDependentPrefixGramRegression

section TruncatedPhaseCancellationRegression

open Complex

example (T : ℝ) :
    atkinsonIndexRealPhase T 7 = atkinsonSourcePhase T 7 :=
  atkinsonIndexRealPhase_natCast T 7

example {T : ℝ} (hT : 0 < T) :
    HasDerivAt (atkinsonIndexRealPhase T) (Real.sqrt (2*Real.pi*T/2+Real.pi^2)) 2 :=
  hasDerivAt_atkinsonIndexRealPhase hT (by norm_num)

example {T x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    atkinsonIndexRealCurvature T x < 0 :=
  atkinsonIndexRealCurvature_neg hT hx

example {t u x : ℝ} (hu : 0 < u) (htu : u < t) (hx : 0 < x) :
    atkinsonIndexRealCurvature t x-atkinsonIndexRealCurvature u x < 0 :=
  atkinsonIndexCurvatureDifference_neg hu htu hx

example : 0 < atkinsonIndexBProcessLambda 101 100 2 4 :=
  atkinsonIndexBProcessLambda_pos (by norm_num) (by norm_num) (by norm_num)

example : 0 < atkinsonIndexBProcessLambdaUpper 101 100 2 4 :=
  atkinsonIndexBProcessLambdaUpper_pos (by norm_num) (by norm_num) (by norm_num)

example (t u : ℝ) : ‖atkinsonPrefixGram 0 0 t u‖ ≤ (0:ℝ) := by
  simpa only [Nat.cast_zero] using norm_atkinsonPrefixGram_le_length 0 0 t u

example : ‖atkinsonPrefixGram 2 0 101 100‖ ≤ atkinsonPrefixBProcessMajorant 2 4 101 100 :=
  norm_atkinsonPrefixGram_le_bProcess (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

example : ‖atkinsonPrefixGram 2 1 101 100‖ ≤ atkinsonPrefixBProcessMajorant 2 4 101 100 :=
  norm_atkinsonPrefixGram_le_bProcess (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

example : atkinsonPrefixGramMax 2 4 101 100 ≤ atkinsonPrefixBProcessMajorant 2 4 101 100 :=
  atkinsonPrefixGramMax_le_bProcess (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example (hsmall : atkinsonIndexFirstDerivativeUpper 100 101 2 7 ≤ Real.pi) :
    ‖atkinsonPrefixGram 2 3 101 100‖ ≤ atkinsonPrefixFirstDerivativeMajorant 2 4 101 100 :=
  norm_atkinsonPrefixGram_le_firstDerivative (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by convert hsmall using 1; norm_num) (by norm_num)

example (t : ℝ) : atkinsonPrefixGapMajorant 2 4 t t = 4 := by
  simpa using atkinsonPrefixGapMajorant_self 2 4 t

example (t u : ℝ) : atkinsonPrefixGapMajorant 2 4 t u = atkinsonPrefixGapMajorant 2 4 u t :=
  atkinsonPrefixGapMajorant_swap 2 4 u t

example : atkinsonPrefixGramMax 2 4 100 101 ≤ atkinsonPrefixGapMajorant 2 4 100 101 :=
  atkinsonPrefixGramMax_le_gap (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example {H : ℝ} (hH : 2 ≤ H) : (2*H)^((1/4:ℝ)/2) ≤ H^(1/4:ℝ) :=
  atkinson_doubled_height_half_power hH (by norm_num)

example {x : ℝ} (hx : 0 < x) :
    (x^(-(1/4:ℝ)))^2*x^(1+(1/10:ℝ)) = x^(1/2+(1/10:ℝ)) :=
  atkinson_quarter_energy_power hx (1/10)

example (W : Finset ℝ) : atkinsonDyadicGapBudget 0 W = 0 :=
  atkinsonDyadicGapBudget_zero W

example (N : ℕ) : atkinsonDyadicGapBudget N ∅ = 0 :=
  atkinsonDyadicGapBudget_empty N

example (η : ℝ) (W : Finset ℝ) : atkinsonArithmeticGapBudget η 0 W = 0 :=
  atkinsonArithmeticGapBudget_zero η W

example (η : ℝ) (N : ℕ) : atkinsonArithmeticGapBudget η N ∅ = 0 :=
  atkinsonArithmeticGapBudget_empty η N

example {δ : ℝ} (hδ : 0 < δ) :
    ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H G : ℝ, H₀ ≤ H → H^δ ≤ G →
      2*(atkinsonSourceCutoff (2*H) G (Real.log (2*H)):ℝ)+2 ≤ H :=
  exists_atkinsonPhysicalCutoff_prefix_geometry hδ

example {δ : ℝ} (hδ : 0 < δ) :
    ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H G : ℝ, H₀ ≤ H → H^δ ≤ G →
      ∀ j : ℕ, j < Nat.clog 2 (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) →
      ∀ t u : ℝ, H ≤ t → t ≤ 2*H → H ≤ u → u ≤ 2*H →
        atkinsonPrefixGramMax (2^j) (2^j) t u ≤ atkinsonPrefixGapMajorant (2^j) (2^j) t u :=
  exists_atkinsonPhysicalPrefixGramMax_le_gap hδ

example {δ : ℝ} (hδ : 0 < δ) :
    ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H G : ℝ, ∀ W : Finset ℝ, H₀ ≤ H →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G) →
      atkinsonDyadicGramBudget (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W ≤
        atkinsonDyadicGapBudget (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W :=
  exists_atkinsonPhysicalGramBudget_le_gapBudget hδ

example {δ η : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H G : ℝ, ∀ W : Finset ℝ,
      H₀ ≤ H → (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G) →
      atkinsonDyadicGapBudget (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W ≤
        C*atkinsonArithmeticGapBudget η (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W :=
  exists_atkinsonPhysicalGapBudget_le_arithmetic hδ hη

example {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H G : ℝ, ∀ W : Finset ℝ,
      H₀ ≤ H → 0 < G →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ)) →
      (∑ t ∈ W, ‖atkinsonStationaryLeadingSum t G (Real.log t)‖)^2 ≤
        C*G^2*H^(-(1/2:ℝ))*
          atkinsonDyadicGapBudget (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W :=
  exists_atkinsonStationaryPacket_sq_le_physicalGap hδ

example
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4 : ℝ) ≤ G) →
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*(G*Real.log t+t^(1/4+ε))))^2 ≤
        D*G^2*H^(-(1/2:ℝ))*
          atkinsonDyadicGapBudget (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W :=
  exists_atkinsonLocalMeanExcessPacket_sq_le_physicalGap hδ hε

example
    {δ κ : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*G*Real.log t))^2 ≤
        D*G^2*H^(-(1/2:ℝ))*
          atkinsonDyadicGapBudget (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W :=
  exists_atkinsonLocalMeanExcessPacket_sq_le_physicalGap_above_fourthRoot hδ hκ

example {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H G : ℝ, ∀ W : Finset ℝ,
      H₀ ≤ H → 0 < G →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ)) →
      (∑ t ∈ W, ‖atkinsonStationaryLeadingSum t G (Real.log t)‖)^2 ≤
        C*G^2*H^(-(1/2:ℝ))*
          atkinsonArithmeticGapBudget η (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W :=
  exists_atkinsonStationaryPacket_sq_le_arithmeticGap hδ hη

example
    {δ ε η : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4 : ℝ) ≤ G) →
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*(G*Real.log t+t^(1/4+ε))))^2 ≤
        D*G^2*H^(-(1/2:ℝ))*
          atkinsonArithmeticGapBudget η (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W :=
  exists_atkinsonLocalMeanExcessPacket_sq_le_arithmeticGap hδ hε hη

example
    {δ κ η : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*G*Real.log t))^2 ≤
        D*G^2*H^(-(1/2:ℝ))*
          atkinsonArithmeticGapBudget η (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W :=
  exists_atkinsonLocalMeanExcessPacket_sq_le_arithmeticGap_above_fourthRoot hδ hκ hη

end TruncatedPhaseCancellationRegression

section SeparatedNearGapRegression

example {H M : ℝ} (hM : 0 < M) :
    M*Real.sqrt (H/M) = Real.sqrt (H*M) :=
  atkinson_mul_sqrt_div hM

example : atkinsonIndexFirstDerivativeUpper 100 110 1 (1+1+1) ≤ Real.pi := by
  have h := atkinson_near_half_period (H := 100) (t := 110) (u := 100) (M := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simpa only [Nat.cast_one] using h

example : atkinsonPrefixGapMajorant 1 1 110 100 ≤ 60 := by
  have h := atkinsonPrefixGapMajorant_le_near (H := 100) (t := 110) (u := 100) (M := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

example : atkinsonPrefixGapMajorant 1 1 100 110 ≤ 60 := by
  have h := atkinsonPrefixGapMajorant_le_near (H := 100) (t := 100) (u := 110) (M := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

example (η H G : ℝ) (N : ℕ) :
    atkinsonSeparatedGapBudget η H G N ∅ = 0 :=
  atkinsonSeparatedGapBudget_empty η H G N

example (H t : ℝ) (M : ℕ) : atkinsonFarGapRow H M {t} t = 0 := by
  classical
  simp only [atkinsonFarGapRow, Finset.sum_filter, Finset.sum_singleton,
    sub_self, abs_zero, not_lt.mpr (Real.sqrt_nonneg (H*(M:ℝ))), ite_false]

example (M : ℕ) (t : ℝ) : atkinsonPrefixGapMajorant M M t t = (M:ℝ) :=
  atkinsonPrefixGapMajorant_self M M t

example {G : ℝ} {W : Finset ℝ} (hG : 0 < G) (hSep : IsSeparated G W) :
    IsSeparated 1 (W.image (fun t => t/G)) :=
  atkinson_isSeparated_div hG hSep

example {G : ℝ} {W : Finset ℝ} {t : ℝ}
    (hG : 0 < G) (hSep : IsSeparated G W) (ht : t ∈ W) :
    (∑ u ∈ W with u ≠ t ∧ |u-t| ≤ G*5, 1/|u-t|) ≤ (2/G)*(harmonic 5:ℝ) := by
  classical
  exact atkinson_sum_inv_gap_le_harmonic 5 hG hSep ht
    (Finset.filter_subset _ _) (fun u hu => (Finset.mem_filter.mp hu).2)

example {G L : ℝ} {W S : Finset ℝ} {t : ℝ}
    (hG : 0 < G) (hSep : IsSeparated G W) (ht : t ∈ W)
    (hSW : S ⊆ W) (hnear : ∀ u ∈ S, u ≠ t ∧ |u-t| ≤ L) :
    (∑ u ∈ S, 1/|u-t|) ≤ (2/G)*(harmonic (Nat.ceil (L/G)):ℝ) :=
  atkinson_sum_inv_gap_le_harmonic_ceil hG hSep ht hSW hnear

example {H G η : ℝ} {N : ℕ} {W : Finset ℝ}
    (hH : 0 < H) (hG : 0 < G) (hSep : IsSeparated G W)
    (hrange : ∀ u ∈ W, H ≤ u ∧ u ≤ 2*H) :
    atkinsonArithmeticGapBudget η N W ≤ atkinsonSeparatedGapBudget η H G N W :=
  atkinsonArithmeticGapBudget_le_separated hH hG hSep hrange

example {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H G : ℝ, ∀ W : Finset ℝ,
      H₀ ≤ H → 0 < G → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ)) →
      (∑ t ∈ W, ‖atkinsonStationaryLeadingSum t G (Real.log t)‖)^2 ≤
        C*G^2*H^(-(1/2:ℝ))*
          atkinsonSeparatedGapBudget η H G (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W :=
  exists_atkinsonStationaryPacket_sq_le_separatedNear hδ hη

example
    {δ ε η : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4 : ℝ) ≤ G) →
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*(G*Real.log t+t^(1/4+ε))))^2 ≤
        D*G^2*H^(-(1/2:ℝ))*
          atkinsonSeparatedGapBudget η H G (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W :=
  exists_atkinsonLocalMeanExcessPacket_sq_le_separatedNear hδ hε hη

example
    {δ κ η : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*G*Real.log t))^2 ≤
        D*G^2*H^(-(1/2:ℝ))*
          atkinsonSeparatedGapBudget η H G (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W :=
  exists_atkinsonLocalMeanExcessPacket_sq_le_separatedNear_above_fourthRoot hδ hκ hη

end SeparatedNearGapRegression

section FarGapPowerRegression

example {H t u : ℝ} {M : ℕ}
    (hH : 0 < H) (hHu : H ≤ u) (huH : u ≤ 2*H) (htu : u < t) (hM : 0 < M) :
    (t-u)/(320*((M:ℝ)*Real.sqrt (H*(M:ℝ)))) ≤ atkinsonIndexBProcessLambda t u M M ∧
      atkinsonIndexBProcessLambdaUpper t u M M ≤ 4*(t-u)/((M:ℝ)*Real.sqrt (H*(M:ℝ))) :=
  atkinson_far_lambda_bounds hH hHu huH htu hM

example : 1/Real.sqrt (1:ℝ) ≤ 20*Real.sqrt ((1:ℝ)/1) :=
  atkinson_far_inverse_sqrt (by norm_num) (by norm_num) (by norm_num)

example : 2*Real.pi/Real.sqrt (1:ℝ)+2*(Real.sqrt (1:ℝ)/1+1) ≤
    202*Real.sqrt ((1:ℝ)/1) :=
  atkinson_far_second_factor (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : ((16:ℝ)/4)*Real.sqrt ((9:ℝ)*4/16) = Real.sqrt ((9:ℝ)*16/4) :=
  atkinson_far_radical_identity (by norm_num) (by norm_num)

example : min (4:ℝ) ((4*1/(2*Real.pi)+2)*
    (2*Real.pi/Real.sqrt 1+2*(Real.sqrt 1/1+1))) ≤ 2000*Real.sqrt (4*1/1) :=
  atkinson_far_min_bProcess (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

example : min (4:ℝ) ((4*16/(2*Real.pi)+2)*
    (2*Real.pi/Real.sqrt 1+2*(Real.sqrt 1/1+1))) ≤ 2000*Real.sqrt (4*16/1) :=
  atkinson_far_min_bProcess (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

example : atkinsonPrefixGapMajorant 1 1 110 100 ≤ 2000 := by
  have h := atkinsonPrefixGapMajorant_le_far (H := 100) (t := 110) (u := 100) (M := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

example : atkinsonPrefixGapMajorant 1 1 100 110 ≤ 2000 := by
  have h := atkinsonPrefixGapMajorant_le_far (H := 100) (t := 100) (u := 110) (M := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

example {H : ℝ} (hH : 0 < H) {M : ℕ} (hM : 0 < M) :
    atkinsonFarGapRow H M {H} H ≤ 0 := by
  have h := atkinson_far_gap_row_le (L := 0) hH hM (by simp : H ∈ ({H}:Finset ℝ))
    (by intro u hu; simp only [Finset.mem_singleton] at hu; subst u; constructor <;> linarith)
    (by intro u hu; simp only [Finset.mem_singleton] at hu; subst u; simp)
  simpa using h

example {H L : ℝ} {M : ℕ} {W : Finset ℝ}
    (hH : 0 < H) (hM : 0 < M)
    (hrange : ∀ u ∈ W, H ≤ u ∧ u ≤ 2*H)
    (hdiam : ∀ t ∈ W, ∀ u ∈ W, |u-t| ≤ L) :
    (∑ t ∈ W, atkinsonFarGapRow H M W t) ≤
      (W.card:ℝ)^2*(2000*Real.sqrt ((M:ℝ)*L/Real.sqrt (H*(M:ℝ)))) :=
  atkinson_far_gap_double_sum_le hH hM hrange hdiam

example {H M : ℝ} (hH : 0 < H) (hM : 0 < M) (L : ℝ) :
    Real.sqrt (M*L/Real.sqrt (H*M)) = H^(-(1/4:ℝ))*M^(1/4:ℝ)*Real.sqrt L :=
  atkinson_far_radical_eq_rpow hH hM L

example {M : ℝ} (hM : 0 < M) (η : ℝ) :
    M^(1/2+η)*M = M^(3/2+η) :=
  atkinson_weighted_diagonal_power hM η

example {H M : ℝ} (hH : 0 < H) (hM : 0 < M) (η : ℝ) :
    M^(1/2+η)*Real.sqrt (H*M) = Real.sqrt H*M^(1+η) :=
  atkinson_weighted_near_power hH hM η

example {H M : ℝ} (hH : 0 < H) (hM : 0 < M) (η L : ℝ) :
    M^(1/2+η)*Real.sqrt (M*L/Real.sqrt (H*M)) =
      H^(-(1/4:ℝ))*Real.sqrt L*M^(3/4+η) :=
  atkinson_weighted_far_power hH hM η L

example {m n : ℕ} (hmn : m ≤ n) : (harmonic m:ℝ) ≤ (harmonic n:ℝ) :=
  atkinson_harmonic_mono hmn

example {H : ℝ} {M : ℕ}
    (hH : 0 < H) (hM : 0 < M) (η G L : ℝ) (R : ℕ) :
    (M:ℝ)^(1/2+η)*((R:ℝ)*atkinsonNearRowBound H G M+
      (R:ℝ)^2*(2000*Real.sqrt ((M:ℝ)*L/Real.sqrt (H*(M:ℝ))))) =
        atkinsonPowerGapTerm η H G L M R :=
  atkinson_localized_gap_term_eq hH hM η G L R

example {H G η L : ℝ} {M N : ℕ} (R : ℕ)
    (hH : 0 < H) (hG : 0 < G) (hη : 0 ≤ η) (hM : 0 < M) (hMN : M ≤ N) :
    atkinsonPowerGapTerm η H G L M R ≤ atkinsonPowerGapTerm η H G L N R :=
  atkinsonPowerGapTerm_mono_index R hH hG hη hM hMN

example {H G η L : ℝ} (N R : ℕ)
    (hH : 0 < H) (hG : 0 < G) (hη : 0 ≤ η) :
    atkinsonLocalizedGapBudget η H G L N R ≤ atkinsonPowerGapBudget η H G L N R :=
  atkinsonLocalizedGapBudget_le_power N R hH hG hη

example (η H G L : ℝ) (R : ℕ) : atkinsonPowerGapBudget η H G L 0 R = 0 := by
  simp [atkinsonPowerGapBudget]

example (η H G L : ℝ) (N : ℕ) : atkinsonPowerGapBudget η H G L N 0 = 0 :=
  atkinsonPowerGapBudget_zero_card η H G L N

example {A L : ℝ} {W : Finset ℝ} (hlocal : ∀ t ∈ W, A ≤ t ∧ t ≤ A+L) :
    ∀ t ∈ W, ∀ u ∈ W, |u-t| ≤ L :=
  atkinson_height_interval_diameter hlocal

example {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H G A L : ℝ, ∀ W : Finset ℝ,
      H₀ ≤ H → 0 < G → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ)) →
      (∀ t ∈ W, A ≤ t ∧ t ≤ A+L) →
      (∑ t ∈ W, ‖atkinsonStationaryLeadingSum t G (Real.log t)‖)^2 ≤
        C*G^2*H^(-(1/2:ℝ))*
          atkinsonPowerGapBudget η H G L (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W.card :=
  exists_atkinsonStationaryPacket_sq_le_localizedPowers hδ hη

example
    {δ ε η : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G A L : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4 : ℝ) ≤ G) →
      (∀ t ∈ W, A ≤ t ∧ t ≤ A+L) →
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*(G*Real.log t+t^(1/4+ε))))^2 ≤
        D*G^2*H^(-(1/2:ℝ))*
          atkinsonPowerGapBudget η H G L (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W.card :=
  exists_atkinsonLocalMeanExcessPacket_sq_le_localizedPowers hδ hε hη

example
    {δ κ η : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G A L : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
      (∀ t ∈ W, A ≤ t ∧ t ≤ A+L) →
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*G*Real.log t))^2 ≤
        D*G^2*H^(-(1/2:ℝ))*
          atkinsonPowerGapBudget η H G L (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W.card :=
  exists_atkinsonLocalMeanExcessPacket_sq_le_localizedPowers_above_fourthRoot hδ hκ hη

example {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H G : ℝ, ∀ W : Finset ℝ,
      H₀ ≤ H → 0 < G → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ)) →
      (∑ t ∈ W, ‖atkinsonStationaryLeadingSum t G (Real.log t)‖)^2 ≤
        C*G^2*H^(-(1/2:ℝ))*
          atkinsonPowerGapBudget η H G H (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W.card :=
  exists_atkinsonStationaryPacket_sq_le_physicalPowers hδ hη

example
    {δ ε η : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4 : ℝ) ≤ G) →
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*(G*Real.log t+t^(1/4+ε))))^2 ≤
        D*G^2*H^(-(1/2:ℝ))*
          atkinsonPowerGapBudget η H G H (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W.card :=
  exists_atkinsonLocalMeanExcessPacket_sq_le_physicalPowers hδ hε hη

example
    {δ κ η : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*G*Real.log t))^2 ≤
        D*G^2*H^(-(1/2:ℝ))*
          atkinsonPowerGapBudget η H G H (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W.card :=
  exists_atkinsonLocalMeanExcessPacket_sq_le_physicalPowers_above_fourthRoot hδ hκ hη

end FarGapPowerRegression

section PhysicalCutoffRegression

example {H : ℝ} {N : ℕ}
    (hH : 1 ≤ H) (hlog : 1 ≤ Real.log (2*H)) (hN : (N:ℝ) ≤ H) :
    (Nat.clog 2 N:ℝ) ≤ (1/Real.log 2+1)*Real.log (2*H) :=
  atkinson_clog_le_height_log hH hlog hN

example {H G : ℝ} {N : ℕ}
    (hH : 1 ≤ H) (hG : 1 ≤ G) (hlog : 1 ≤ Real.log (2*H))
    (hN : (N:ℝ) ≤ H) :
    (harmonic (Nat.ceil (Real.sqrt (H*(N:ℝ))/G)):ℝ) ≤ 2*Real.log (2*H) :=
  atkinson_harmonic_le_height_log hH hG hlog hN

example (k : ℕ) {ν : ℝ} (hν : 0 < ν) :
    ∀ᶠ H : ℝ in Filter.atTop, (Real.log (2*H))^k ≤ H^ν :=
  eventually_atkinson_height_log_pow_le_rpow k hν

example {H G : ℝ}
    (hH : 1 ≤ H) (hG : 0 < G) (hupper : G ≤ Real.sqrt (2*H))
    (hlog : 1 ≤ Real.log (2*H)) :
    (atkinsonSourceCutoff (2*H) G (Real.log (2*H)):ℝ) ≤
      74*H*(Real.log (2*H))^2/G^2 :=
  atkinsonPhysicalCutoff_le_natural hH hG hupper hlog

example {H G ℓ : ℝ}
    (hH : 0 < H) (hG : 0 < G) (hℓ : 0 < ℓ) (q : ℝ) :
    G^2*H^(-(1/2:ℝ))*(74*H*ℓ^2/G^2)^q =
      (74:ℝ)^q*H^(q-1/2)*ℓ^(2*q)*G^(2-2*q) :=
  atkinsonPhysical_cutoff_scale_identity hH hG hℓ q

example {H G ℓ : ℝ}
    (hH : 0 < H) (hG : 0 < G) (hℓ : 0 < ℓ) :
    G^2*H^(-(1/2:ℝ))*(74*H*ℓ^2/G^2)^(3/2:ℝ) ≤
      5476*(H/G)*ℓ^3 :=
  atkinsonPhysical_diagonal_scale hH hG hℓ

example {H G ℓ : ℝ}
    (hH : 0 < H) (hG : 0 < G) (hℓ : 0 < ℓ) :
    (Real.sqrt H/G)*(G^2*H^(-(1/2:ℝ))*(74*H*ℓ^2/G^2)^(1:ℝ)) =
      74*(H/G)*ℓ^2 :=
  atkinsonPhysical_near_scale hH hG hℓ

example {H G ℓ L : ℝ}
    (hH : 0 < H) (hG : 0 < G) (hℓ : 1 ≤ ℓ) :
    (H^(-(1/4:ℝ))*Real.sqrt L)*(G^2*H^(-(1/2:ℝ))*(74*H*ℓ^2/G^2)^(3/4:ℝ)) ≤
      74*Real.sqrt (G*L)*ℓ^3 :=
  atkinsonPhysical_far_scale hH hG hℓ

example {N : ℕ} (hN : 0 < N)
    (η H G L : ℝ) (R : ℕ) :
    atkinsonPowerGapTerm η H G L N R =
      (N:ℝ)^η*atkinsonPowerGapTerm 0 H G L N R :=
  atkinsonPowerGapTerm_epsilon_factor hN η H G L R

example {H G : ℝ} {N : ℕ} (L : ℝ) (R : ℕ)
    (hH : 1 ≤ H) (hG : 1 ≤ G) (hlog : 1 ≤ Real.log (2*H))
    (hN : (N:ℝ) ≤ H) (hcut : (N:ℝ) ≤ 74*H*(Real.log (2*H))^2/G^2) :
    G^2*H^(-(1/2:ℝ))*atkinsonPowerGapTerm 0 H G L N R ≤
      148000*(Real.log (2*H))^3*((R:ℝ)*H/G+(R:ℝ)^2*Real.sqrt (G*L)) :=
  atkinsonPhysical_gap_term_zero_le L R hH hG hlog hN hcut

example {H G η : ℝ} {N : ℕ} (L : ℝ) (R : ℕ)
    (hH : 1 ≤ H) (hG : 1 ≤ G) (hη : 0 ≤ η) (hN0 : 0 < N)
    (hlog : 1 ≤ Real.log (2*H)) (hN : (N:ℝ) ≤ H)
    (hcut : (N:ℝ) ≤ 74*H*(Real.log (2*H))^2/G^2) :
    G^2*H^(-(1/2:ℝ))*atkinsonPowerGapBudget η H G L N R ≤
      (148000*(1/Real.log 2+1)^2)*H^η*(Real.log (2*H))^5*
        ((R:ℝ)*H/G+(R:ℝ)^2*Real.sqrt (G*L)) :=
  atkinsonPhysical_gap_budget_log_le L R hH hG hη hN0 hlog hN hcut

example {δ ν : ℝ} (hδ : 0 < δ) (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G L : ℝ, ∀ R : ℕ, H₀ ≤ H → H^δ ≤ G → G ≤ Real.sqrt (2*H) →
        G^2*H^(-(1/2:ℝ))*
          atkinsonPowerGapBudget (ν/2) H G L
            (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) R ≤
          C*H^ν*((R:ℝ)*H/G+(R:ℝ)^2*Real.sqrt (G*L)) :=
  exists_atkinsonPhysicalGapBudget_le_twoTerm hδ hν

example {δ H G : ℝ} {W : Finset ℝ}
    (hδ : 0 < δ) (hH : 1 ≤ H) (hG : 0 < G) (hW : W.Nonempty)
    (hrange : ∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ)) :
    H^δ ≤ G ∧ G ≤ Real.sqrt (2*H) :=
  atkinson_packet_width_scales hδ hH hG hW hrange

example
    {δ ν : ℝ} (hδ : 0 < δ) (hν : 0 < ν) :
    ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G A L : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ)) →
      (∀ t ∈ W, A ≤ t ∧ t ≤ A+L) →
      (∑ t ∈ W, ‖atkinsonStationaryLeadingSum t G (Real.log t)‖)^2 ≤
        D*H^ν*((W.card:ℝ)*H/G+(W.card:ℝ)^2*Real.sqrt (G*L)) :=
  exists_atkinsonStationaryPacket_sq_le_localizedPhysical hδ hν

example
    {δ ε ν : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G A L : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4 : ℝ) ≤ G) →
      (∀ t ∈ W, A ≤ t ∧ t ≤ A+L) →
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*(G*Real.log t+t^(1/4+ε))))^2 ≤
        D*H^ν*((W.card:ℝ)*H/G+(W.card:ℝ)^2*Real.sqrt (G*L)) :=
  exists_atkinsonLocalMeanExcessPacket_sq_le_localizedPhysical hδ hε hν

example
    {δ κ ν : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G A L : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
      (∀ t ∈ W, A ≤ t ∧ t ≤ A+L) →
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*G*Real.log t))^2 ≤
        D*H^ν*((W.card:ℝ)*H/G+(W.card:ℝ)^2*Real.sqrt (G*L)) :=
  exists_atkinsonLocalMeanExcessPacket_sq_le_localizedPhysical_above_fourthRoot hδ hκ hν

example
    {δ ν : ℝ} (hδ : 0 < δ) (hν : 0 < ν) :
    ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ)) →
      (∑ t ∈ W, ‖atkinsonStationaryLeadingSum t G (Real.log t)‖)^2 ≤
        D*H^ν*((W.card:ℝ)*H/G+(W.card:ℝ)^2*Real.sqrt (G*H)) :=
  exists_atkinsonStationaryPacket_sq_le_globalPhysical hδ hν

example
    {δ ε ν : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4 : ℝ) ≤ G) →
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*(G*Real.log t+t^(1/4+ε))))^2 ≤
        D*H^ν*((W.card:ℝ)*H/G+(W.card:ℝ)^2*Real.sqrt (G*H)) :=
  exists_atkinsonLocalMeanExcessPacket_sq_le_globalPhysical hδ hε hν

example
    {δ κ ν : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*G*Real.log t))^2 ≤
        D*H^ν*((W.card:ℝ)*H/G+(W.card:ℝ)^2*Real.sqrt (G*H)) :=
  exists_atkinsonLocalMeanExcessPacket_sq_le_globalPhysical_above_fourthRoot hδ hκ hν

example (η H G L : ℝ) (R : ℕ) :
    atkinsonPowerGapTerm η H G L 1 R = atkinsonPowerGapTerm 0 H G L 1 R := by
  simpa only [Nat.cast_one,Real.one_rpow,one_mul] using
    atkinsonPowerGapTerm_epsilon_factor (by norm_num : 0 < (1:ℕ)) η H G L R

example {H G ℓ : ℝ} (hH : 0 < H) (hG : 0 < G) (hℓ : 1 ≤ ℓ) :
    (H^(-(1/4:ℝ))*Real.sqrt 0)*
      (G^2*H^(-(1/2:ℝ))*(74*H*ℓ^2/G^2)^(3/4:ℝ)) ≤
      74*Real.sqrt (G*0)*ℓ^3 :=
  atkinsonPhysical_far_scale hH hG hℓ

example {H : ℝ} (hH : 1 ≤ H) (hlog : 1 ≤ Real.log (2*H)) :
    (Nat.clog 2 0:ℝ) ≤ (1/Real.log 2+1)*Real.log (2*H) :=
  atkinson_clog_le_height_log hH hlog (by norm_num; linarith)

end PhysicalCutoffRegression

section AtkinsonCountingRegression

example {A G Y : ℝ}
    (hA : 0 < A) (hG : 0 < G) (hY : 0 < Y) :
    0 < atkinsonAbsorptionLength A G Y :=
  atkinsonAbsorptionLength_pos hA hG hY

example {A G Y : ℝ}
    (hA : 0 < A) (hG : 0 < G) :
    Real.sqrt (G*atkinsonAbsorptionLength A G Y) = Y^2/(4*A) :=
  atkinsonAbsorptionLength_radical hA hG

example {A G Y : ℝ}
    (hA : 0 < A) (hG : 0 < G) :
    2*A*Real.sqrt (G*atkinsonAbsorptionLength A G Y) ≤ Y^2 :=
  atkinsonAbsorptionLength_absorbs hA hG

example {A H G L Y : ℝ} {W : Finset ℝ} {f : ℝ → ℝ}
    (hA : 0 < A) (hH : 0 ≤ H) (hG : 0 < G) (hY : 0 < Y)
    (hlarge : ∀ t ∈ W, Y ≤ f t)
    (hpacket : (∑ t ∈ W, f t)^2 ≤
      A*((W.card:ℝ)*H/G+(W.card:ℝ)^2*Real.sqrt (G*L)))
    (habsorb : 2*A*Real.sqrt (G*L) ≤ Y^2) :
    (W.card:ℝ) ≤ 2*A*H/(G*Y^2) :=
  atkinson_card_le_of_packet hA hH hG hY hlarge hpacket habsorb

example {A H G Y : ℝ}
    (hA : 0 < A) (hH : 0 ≤ H) (hG : 0 < G) (hY : 0 < Y) :
    ((Nat.floor (H/atkinsonAbsorptionLength A G Y)+1:ℕ):ℝ)*
      (2*A*H/(G*Y^2)) ≤
      2*A*H/(G*Y^2)+32*A^3*H^2/Y^6 :=
  atkinson_covered_card_budget hA hH hG hY

example (H L : ℝ) (W : Finset ℝ) (k : ℕ) :
    atkinsonHeightFiber H L W k ⊆ W :=
  atkinsonHeightFiber_subset H L W k

example {H L t : ℝ}
    (hL : 0 < L) (ht : t ≤ 2*H) :
    atkinsonHeightBin H L t ∈ Finset.range (Nat.floor (H/L)+1) :=
  atkinsonHeightBin_mem_range hL ht

example {H L : ℝ} {W : Finset ℝ} (k : ℕ)
    (hL : 0 < L) (hrange : ∀ t ∈ W, H ≤ t) :
    ∀ t ∈ atkinsonHeightFiber H L W k,
      H+(k:ℝ)*L ≤ t ∧ t ≤ (H+(k:ℝ)*L)+L :=
  atkinsonHeightFiber_interval k hL hrange

example {H L : ℝ} (W : Finset ℝ)
    (hL : 0 < L) (hrange : ∀ t ∈ W, t ≤ 2*H) :
    W.card = ∑ k ∈ Finset.range (Nat.floor (H/L)+1),
      (atkinsonHeightFiber H L W k).card :=
  atkinsonHeightFiber_card_partition W hL hrange

example {H L B : ℝ} {W : Finset ℝ}
    (hL : 0 < L) (hrange : ∀ t ∈ W, t ≤ 2*H)
    (hcard : ∀ k ∈ Finset.range (Nat.floor (H/L)+1),
      ((atkinsonHeightFiber H L W k).card:ℝ) ≤ B) :
    (W.card:ℝ) ≤ ((Nat.floor (H/L)+1:ℕ):ℝ)*B :=
  atkinson_card_le_of_height_fibers hL hrange hcard

example {A H G Y : ℝ}
    {W : Finset ℝ} {f : ℝ → ℝ}
    (hA : 0 < A) (hH : 0 ≤ H) (hG : 0 < G) (hY : 0 < Y)
    (hrange : ∀ t ∈ W, H ≤ t ∧ t ≤ 2*H)
    (hlarge : ∀ t ∈ W, Y ≤ f t)
    (hpacket : ∀ U : Finset ℝ, U ⊆ W →
      ∀ B : ℝ, (∀ t ∈ U, B ≤ t ∧ t ≤ B+atkinsonAbsorptionLength A G Y) →
        (∑ t ∈ U, f t)^2 ≤
          A*((U.card:ℝ)*H/G+(U.card:ℝ)^2*
            Real.sqrt (G*atkinsonAbsorptionLength A G Y))) :
    (W.card:ℝ) ≤ 2*A*H/(G*Y^2)+32*A^3*H^2/Y^6 :=
  atkinson_card_le_of_local_packets hA hH hG hY hrange hlarge hpacket

example {D H G Y ν : ℝ}
    (hD : 0 ≤ D) (hH : 1 ≤ H) (hG : 0 < G) (hY : 0 < Y) (hν : 0 ≤ ν) :
    2*(D*H^(ν/3))*H/(G*Y^2)+32*(D*H^(ν/3))^3*H^2/Y^6 ≤
      (2*D+32*D^3)*H^ν*(H/(G*Y^2)+H^2/Y^6) :=
  atkinson_count_exponent_budget hD hH hG hY hν

example {G t error Y : ℝ} (hY : 0 < Y) :
    Y ≤ atkinsonLocalMeanExcess G t error ↔
      error+Y ≤ ∫ u in t-G..t+G, zetaMomentCriticalNorm u^2 :=
  atkinsonLocalMeanExcess_threshold_iff hY

example
    {δ ε ν : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G Y : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G → 0 < Y → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4 : ℝ) ≤ G) →
      (∀ t ∈ W, Y ≤ atkinsonLocalMeanExcess G t (C*(G*Real.log t+t^(1/4+ε)))) →
      (W.card:ℝ) ≤ D*H^ν*(H/(G*Y^2)+H^2/Y^6) :=
  exists_atkinsonLocalMeanExcess_card_le hδ hε hν

example
    {δ κ ν : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G Y : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G → 0 < Y → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
      (∀ t ∈ W, Y ≤ atkinsonLocalMeanExcess G t (C*G*Real.log t)) →
      (W.card:ℝ) ≤ D*H^ν*(H/(G*Y^2)+H^2/Y^6) :=
  exists_atkinsonLocalMeanExcess_card_le_above_fourthRoot hδ hκ hν

example
    {δ ε ν : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G Y : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G → 0 < Y → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4 : ℝ) ≤ G) →
      (({t ∈ W | C*(G*Real.log t+t^(1/4+ε))+Y ≤
        ∫ u in t-G..t+G, zetaMomentCriticalNorm u^2}).card:ℝ) ≤
        D*H^ν*(H/(G*Y^2)+H^2/Y^6) :=
  exists_atkinsonLocalMean_superlevel_card_le hδ hε hν

example
    {δ κ ν : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G Y : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G → 0 < Y → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
      (({t ∈ W | C*G*Real.log t+Y ≤
        ∫ u in t-G..t+G, zetaMomentCriticalNorm u^2}).card:ℝ) ≤
        D*H^ν*(H/(G*Y^2)+H^2/Y^6) :=
  exists_atkinsonLocalMean_superlevel_card_le_above_fourthRoot hδ hκ hν

example : atkinsonAbsorptionLength 1 4 2 = (1/4:ℝ) := by
  norm_num [atkinsonAbsorptionLength]

example : Real.sqrt ((4:ℝ)*atkinsonAbsorptionLength 1 4 2) = 1 := by
  have h := atkinsonAbsorptionLength_radical (A := 1) (G := 4) (Y := 2)
    (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

example : 2*(1:ℝ)*Real.sqrt (4*atkinsonAbsorptionLength 1 4 (-2)) ≤ (-2:ℝ)^2 :=
  atkinsonAbsorptionLength_absorbs (by norm_num) (by norm_num)

example (A G : ℝ) : atkinsonAbsorptionLength A G 0 = 0 := by
  simp [atkinsonAbsorptionLength]

example : atkinsonHeightBin 10 2 10 = 0 := by
  norm_num [atkinsonHeightBin]

example : atkinsonHeightBin 10 2 12 = 1 := by
  norm_num [atkinsonHeightBin]

example : atkinsonHeightBin 10 2 20 = 5 := by
  norm_num [atkinsonHeightBin]

example : atkinsonHeightFiber 10 2 {10,12,20} 0 = {10} := by
  ext t
  simp only [atkinsonHeightFiber,Finset.mem_filter,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨ht,hbin⟩
    rcases ht with ht | ht | ht
    · exact ht
    · subst t; norm_num [atkinsonHeightBin] at hbin
    · subst t; norm_num [atkinsonHeightBin] at hbin
  · intro ht
    subst t
    norm_num [atkinsonHeightBin]

example : atkinsonHeightFiber 10 2 {10,12,20} 5 = {20} := by
  ext t
  simp only [atkinsonHeightFiber,Finset.mem_filter,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨ht,hbin⟩
    rcases ht with ht | ht | ht
    · subst t; norm_num [atkinsonHeightBin] at hbin
    · subst t; norm_num [atkinsonHeightBin] at hbin
    · exact ht
  · intro ht
    subst t
    norm_num [atkinsonHeightBin]

example (H L : ℝ) (k : ℕ) : atkinsonHeightFiber H L ∅ k = ∅ := by
  simp [atkinsonHeightFiber]

end AtkinsonCountingRegression

namespace PointMeanKernelRegression

open Complex MeasureTheory
open scoped Interval

example {a b : ℝ} (ha : 0 < a) :
    ∃ D : ℝ, 0 < D ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      (Complex.digamma z).re ≤ Real.log (|z.im| + 2) + D :=
  @exists_re_digamma_le_log_add a b ha

example {a b : ℝ} (ha : 0 < a) :
    ∃ D : ℝ, 0 < D ∧ ∀ (z : ℂ) (d : ℝ),
      a ≤ z.re → z.re + d ≤ b → 0 ≤ d →
      ‖Complex.Gamma (z + (d : ℂ))‖ ^ 2 ≤
        ‖Complex.Gamma z‖ ^ 2 *
          Real.exp (2 * (Real.log (|z.im| + 2) + D) * d) :=
  @exists_norm_Gamma_sq_right_displacement_le a b ha

example {a b : ℝ} (ha : 0 < a) :
    ∃ D : ℝ, 0 < D ∧ ∀ (z : ℂ) (d : ℝ),
      a ≤ z.re → z.re + d ≤ b → 0 ≤ d →
      ‖Complex.Gamma (z + (d : ℂ))‖ ≤
        ‖Complex.Gamma z‖ *
          Real.exp ((Real.log (|z.im| + 2) + D) * d) :=
  @exists_norm_Gamma_right_displacement_le a b ha

example (u : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + (u : ℂ) * I)‖ ^ 2 ≤
      8 * Real.exp (-Real.pi * |u|) :=
  @norm_Gamma_half_vertical_sq_le_exp u

example (u : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤
      3 * Real.exp (-(Real.pi * |u|) / 2) :=
  @norm_Gamma_half_vertical_le_exp u

example :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 1 ≤ |u| →
      ‖Complex.Gamma ((u : ℂ) * I)‖ ≤
        C * (|u| + 2) * Real.exp (-(Real.pi * |u|) / 2) :=
  @exists_norm_Gamma_imaginary_le_exp

example (x : ℝ) (hx : 0 ≤ x) :
    (x + 2) * Real.exp (-(Real.pi * x) / 2) ≤
      2 * Real.exp (-x) :=
  @add_two_mul_exp_neg_pi_half_le_exp_neg x hx

example
    (x : ℝ) (hx : 0 ≤ x) :
    (x + 2) * Real.exp (-(Real.pi * x) / 2) ≤
      6 * Real.exp (-(4 / 3 : ℝ) * x) :=
  @add_two_mul_exp_neg_pi_half_le_six_mul_exp_neg_four_thirds x hx

example (a v : ℝ) (ha : 0 ≤ a) :
    a + |v| ≤ 2 * ‖(a : ℂ) + (v : ℂ) * I‖ :=
  @add_abs_le_two_mul_norm_ofReal_add_mul_I a v ha

example :
    ∃ C : ℝ, 0 < C ∧ ∀ (a v : ℝ),
      3 / 4 ≤ a → a ≤ 5 / 4 →
      ‖Complex.Gamma ((a : ℂ) + (v : ℂ) * I)‖ ≤
        C * Real.exp (-|v|) :=
  @exists_norm_Gamma_heathBrown_positive_strip_le

example :
    ∃ C : ℝ, 0 < C ∧ ∀ (a v : ℝ),
      3 / 4 ≤ a → a ≤ 5 / 4 →
      ‖Complex.Gamma ((a : ℂ) + (v : ℂ) * I)‖ ≤
        C * Real.exp (-(4 / 3 : ℝ) * |v|) :=
  @exists_norm_Gamma_heathBrown_positive_strip_strong_le

example :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ v : ℝ),
      0 < δ → δ ≤ 1 / 4 →
      (δ + |v|) * ‖Complex.Gamma ((δ : ℂ) + (v : ℂ) * I)‖ ≤
          C * Real.exp (-|v|) ∧
      (δ + |v|) * ‖Complex.Gamma ((-δ : ℝ) + (v : ℂ) * I)‖ ≤
          C * Real.exp (-|v|) :=
  @exists_heathBrown_Gamma_shift_kernel_bound

example :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta v : ℝ),
      0 < delta → delta ≤ 1 / 4 →
      (delta + |v|) *
          ‖Complex.Gamma ((delta : ℂ) + (v : ℂ) * I)‖ ≤
            C * Real.exp (-(4 / 3 : ℝ) * |v|) ∧
      (delta + |v|) *
          ‖Complex.Gamma ((-delta : ℝ) + (v : ℂ) * I)‖ ≤
            C * Real.exp (-(4 / 3 : ℝ) * |v|) :=
  @exists_heathBrown_Gamma_shift_kernel_strong_bound

example {delta : ℝ} (hdelta : 0 < delta) :
    Integrable (fun x : ℝ => (delta ^ 2 + x ^ 2)⁻¹) :=
  @integrable_inv_delta_sq_add_sq delta hdelta

example {delta : ℝ} (hdelta : 0 < delta) :
    (∫ x : ℝ, (delta ^ 2 + x ^ 2)⁻¹) = Real.pi / delta :=
  @integral_inv_delta_sq_add_sq delta hdelta

example
    {delta x : ℝ} (hdelta : 0 < delta) :
    heathBrownGammaReserveKernel delta x ^ (2 : ℕ) ≤
      (delta ^ 2 + x ^ 2)⁻¹ :=
  @heathBrownGammaReserveKernel_sq_le delta x hdelta

example
    {delta : ℝ} (hdelta : 0 < delta) :
    Integrable (fun x : ℝ =>
      heathBrownGammaReserveKernel delta x ^ (2 : ℕ)) :=
  @integrable_heathBrownGammaReserveKernel_sq delta hdelta

example
    {delta : ℝ} (hdelta : 0 < delta) :
    (∫ x : ℝ, heathBrownGammaReserveKernel delta x ^ (2 : ℕ)) ≤
      Real.pi / delta :=
  @integral_heathBrownGammaReserveKernel_sq_le delta hdelta

example
    {delta u w : ℝ} (hdelta : 0 < delta) :
    0 ≤ heathBrownStrongGammaConvolutionIntegrand delta u w :=
  @heathBrownStrongGammaConvolutionIntegrand_nonneg delta u w hdelta

example (u w : ℝ) :
    Real.exp (-(4 / 3 : ℝ) * |w|) *
        Real.exp (-(4 / 3 : ℝ) * |u - w|) ≤
      Real.exp (-|u|) * Real.exp (-|w| / 6) *
        Real.exp (-|u - w| / 6) :=
  @heathBrown_strong_exponential_reserve u w

example
    {delta u w : ℝ} (hdelta : 0 < delta) :
    heathBrownStrongGammaConvolutionIntegrand delta u w ≤
      Real.exp (-|u|) / 2 *
        (heathBrownGammaReserveKernel delta w ^ (2 : ℕ) +
          heathBrownGammaReserveKernel delta (u - w) ^ (2 : ℕ)) :=
  @heathBrownStrongGammaConvolutionIntegrand_le delta u w hdelta

example
    {delta : ℝ} (hdelta : 0 < delta) (u : ℝ) :
    Integrable (fun w : ℝ =>
      heathBrownGammaReserveKernel delta (u - w) ^ (2 : ℕ)) :=
  @integrable_heathBrownGammaReserveKernel_sq_sub delta hdelta u

example (delta u : ℝ) :
    (∫ w : ℝ, heathBrownGammaReserveKernel delta (u - w) ^ (2 : ℕ)) =
      ∫ w : ℝ, heathBrownGammaReserveKernel delta w ^ (2 : ℕ) :=
  @integral_heathBrownGammaReserveKernel_sq_sub delta u

example
    {delta u : ℝ} (hdelta : 0 < delta) :
    Integrable (heathBrownStrongGammaConvolutionIntegrand delta u) :=
  @integrable_heathBrownStrongGammaConvolutionIntegrand delta u hdelta

example
    {delta u : ℝ} (hdelta : 0 < delta) :
    (∫ w : ℝ, heathBrownStrongGammaConvolutionIntegrand delta u w) ≤
      (Real.pi / delta) * Real.exp (-|u|) :=
  @integral_heathBrownStrongGammaConvolutionIntegrand_le delta u hdelta

example (u x : ℝ) :
    Real.exp (-|u - x|) ≤
      (1 / 2 : ℝ) ^ Nat.floor |u - x| :=
  @exp_neg_abs_le_half_pow_floor u x

example
    (W : Finset ℝ) (x : ℝ) (k : ℕ) (hSep : IsSeparated 1 W) :
    ({u ∈ W | Nat.floor |u - x| = k}).card ≤ 2 :=
  @separated_distance_shell_card_le_two W x k hSep

example
    (W : Finset ℝ) (x : ℝ) (hSep : IsSeparated 1 W) :
    ∑ u ∈ W, Real.exp (-|u - x|) ≤ 4 :=
  @sum_exp_neg_abs_sub_le_four W x hSep

example
    (f : ℝ → ℝ) (hf : Continuous f) (t a b : ℝ) :
    IntervalIntegrable
      (fun u : ℝ ↦ Real.exp (-|t - u|) * f u) volume a b :=
  @intervalIntegrable_exp_neg_abs_sub_mul f hf t a b

example
    (W : Finset ℝ) (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) :
    ∑ t ∈ W, (∫ u in a..b, Real.exp (-|t - u|) * f u) =
      ∫ u in a..b, ∑ t ∈ W, Real.exp (-|t - u|) * f u :=
  @sum_intervalIntegral_exp_neg_abs_sub_mul_eq W f hf a b

example
    (W : Finset ℝ) (f : ℝ → ℝ) (hf : Continuous f)
    (hNonneg : ∀ u, 0 ≤ f u) (a b : ℝ) (hab : a ≤ b)
    (hSep : IsSeparated 1 W) :
    ∑ t ∈ W, (∫ u in a..b, Real.exp (-|t - u|) * f u) ≤
      4 * ∫ u in a..b, f u :=
  @sum_intervalIntegral_exp_neg_abs_sub_mul_le_four W f hf hNonneg a b hab hSep

example
    (W : Finset ℝ) (a b : ℝ) (hab : a ≤ b)
    (hSep : IsSeparated 1 W) :
    ∑ t ∈ W,
        (∫ u in a..b,
          Real.exp (-|t - u|) * zetaMomentCriticalNorm u ^ (2 : ℕ)) ≤
      4 * ∫ u in a..b, zetaMomentCriticalNorm u ^ (2 : ℕ) :=
  @sum_intervalIntegral_exp_kernel_zeta_sq_le_four W a b hab hSep

example
    (W : Finset ℝ) (lo hi L : ℝ) (hlohi : lo ≤ hi) (hL : 0 ≤ L)
    (hRange : ∀ t ∈ W, lo ≤ t ∧ t ≤ hi)
    (hSep : IsSeparated 1 W) :
    ∑ t ∈ W,
        (∫ u in t - L..t + L,
          Real.exp (-|t - u|) * zetaMomentCriticalNorm u ^ (2 : ℕ)) ≤
      4 * ∫ u in lo - L..hi + L,
        zetaMomentCriticalNorm u ^ (2 : ℕ) :=
  @sum_truncated_exp_kernel_zeta_sq_le_four W lo hi L hlohi hL hRange hSep

example
    (W : Finset ℝ) (center G L : ℝ) (hG : 0 ≤ G) (hL : 0 ≤ L)
    (hRange : ∀ t ∈ W, center - G / 2 ≤ t ∧ t ≤ center + G / 2)
    (hFit : G / 2 + L ≤ G) (hSep : IsSeparated 1 W) :
    ∑ t ∈ W,
        (∫ u in t - L..t + L,
          Real.exp (-|t - u|) * zetaMomentCriticalNorm u ^ (2 : ℕ)) ≤
      4 * (∫ u in center - G..center + G, zetaMomentCriticalNorm u ^ (2 : ℕ)) :=
  @sum_truncated_exp_kernel_zeta_sq_le_localSecondMoment W center G L hG hL hRange hFit hSep

example {a : ℝ} (ha : a ≠ 0)
    (haLower : -1 < a) :
    Continuous (fun w : ℝ => Complex.Gamma ((a : ℂ) + (w : ℂ) * I)) :=
  @continuous_Gamma_small_shift a ha haLower

example {a b : ℝ}
    (ha : a ≠ 0) (haLower : -1 < a)
    (hb : b ≠ 0) (hbLower : -1 < b) (u : ℝ) :
    Continuous (pointMeanGammaProduct a b u) :=
  @continuous_pointMeanGammaProduct a b ha haLower hb hbLower u

example :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta a b u : ℝ),
      0 < delta → delta ≤ 1 / 4 →
      (a = delta ∨ a = -delta) → (b = delta ∨ b = -delta) →
      Integrable (pointMeanGammaProduct a b u) ∧
      (∫ w : ℝ, pointMeanGammaProduct a b u w) ≤
        (C / delta) * Real.exp (-|u|) :=
  @exists_pointMeanGammaProduct_integral_le

example :
    ∃ C : ℝ, 0 < C ∧ ∀ (t a b u : ℝ),
      Real.exp 4 ≤ t →
      (a = 1 / Real.log t ∨ a = -(1 / Real.log t)) →
      (b = 1 / Real.log t ∨ b = -(1 / Real.log t)) →
      Integrable (pointMeanGammaProduct a b u) ∧
      (∫ w : ℝ, pointMeanGammaProduct a b u w) ≤
        C * Real.log t * Real.exp (-|u|) :=
  @exists_pointMeanGammaProduct_log_integral_le

example : ({u ∈ ({-(1/2),1/2} : Finset ℝ) |
    Nat.floor |u - 0| = 0}).card = 2 := by
  norm_num [Finset.filter_insert, Finset.filter_singleton]

example : ({u ∈ ({-1,1} : Finset ℝ) |
    Nat.floor |u - 0| = 1}).card = 2 := by
  norm_num [Finset.filter_insert, Finset.filter_singleton]

example (x : ℝ) : (∑ u ∈ (∅ : Finset ℝ), Real.exp (-|u-x|)) = 0 := by
  simp

example (a b : ℝ) :
    (∑ t ∈ (∅ : Finset ℝ), ∫ u in a..b,
      Real.exp (-|t-u|) * zetaMomentCriticalNorm u ^ 2) = 0 := by
  simp

example : heathBrownGammaReserveKernel 1 0 = 1 := by
  norm_num [heathBrownGammaReserveKernel]

example : heathBrownStrongGammaConvolutionIntegrand 1 0 0 = 1 := by
  norm_num [heathBrownStrongGammaConvolutionIntegrand]

example (a b : ℝ) : pointMeanGammaProduct a b 0 0 =
    ‖Complex.Gamma (a : ℂ)‖ * ‖Complex.Gamma (b : ℂ)‖ := by
  simp [pointMeanGammaProduct]

example : Continuous (fun w : ℝ =>
    Complex.Gamma (((-(1/4) : ℝ) : ℂ) + (w : ℂ) * I)) :=
  continuous_Gamma_small_shift (by norm_num) (by norm_num)

end PointMeanKernelRegression

namespace PointMeanContourRegression

open Complex Set MeasureTheory Filter Topology
open scoped BigOperators Interval ComplexOrder ComplexConjugate

-- PointMeanMellinExp: pintz2023_Gamma_two_vertical_decay
example (t : ℝ) :
    |t| ^ 3 * ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)‖ ≤ 24 :=
  @TaoTrudgianYang2025.pintz2023_Gamma_two_vertical_decay t

-- PointMeanMellinExp: continuous_pintz2023_Gamma_two_vertical
example :
    Continuous (fun t : ℝ => Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)) :=
  @TaoTrudgianYang2025.continuous_pintz2023_Gamma_two_vertical

-- PointMeanMellinExp: integrable_pintz2023_Gamma_two_vertical
example :
    Integrable (fun t : ℝ => Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)) :=
  @TaoTrudgianYang2025.integrable_pintz2023_Gamma_two_vertical

-- PointMeanMellinExp: pintz2023_mellinConvergent_exp_neg_two
example :
    MellinConvergent (fun x : ℝ => (Real.exp (-x) : ℂ)) 2 :=
  @TaoTrudgianYang2025.pintz2023_mellinConvergent_exp_neg_two

-- PointMeanMellinExp: pintz2023_verticalIntegrable_mellin_exp_neg_two
example :
    VerticalIntegrable
      (mellin (fun x : ℝ => (Real.exp (-x) : ℂ))) 2 :=
  @TaoTrudgianYang2025.pintz2023_verticalIntegrable_mellin_exp_neg_two

-- PointMeanMellinExp: pintz2023_inverseMellin_exp_neg
example {x : ℝ} (hx : 0 < x) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        (∫ t : ℝ, (x : ℂ) ^ (-(((2 : ℝ) : ℂ) + (t : ℂ) * I)) *
          Complex.Gamma (((2 : ℝ) : ℂ) + (t : ℂ) * I)) =
      Real.exp (-x) :=
  @TaoTrudgianYang2025.pintz2023_inverseMellin_exp_neg x hx

-- PointMeanDivisorMellin: continuous_heathBrownDivisorMellinSeriesTerm
example
    {s : ℂ} (n : ℕ) :
    Continuous (heathBrownDivisorMellinSeriesTerm s n) :=
  @TaoTrudgianYang2025.continuous_heathBrownDivisorMellinSeriesTerm s n

-- PointMeanDivisorMellin: norm_heathBrownDivisorMellinSeriesTerm_le
example
    {s : ℂ} (n : ℕ) (t : ℝ) :
    ‖heathBrownDivisorMellinSeriesTerm s n t‖ ≤
      (n : ℝ) ^ (-s.re - 1) *
        ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)‖ :=
  @TaoTrudgianYang2025.norm_heathBrownDivisorMellinSeriesTerm_le s n t

-- PointMeanDivisorMellin: integrable_heathBrownDivisorMellinSeriesTerm
example
    {s : ℂ} (n : ℕ) :
    Integrable (heathBrownDivisorMellinSeriesTerm s n) :=
  @TaoTrudgianYang2025.integrable_heathBrownDivisorMellinSeriesTerm s n

-- PointMeanDivisorMellin: summable_integral_norm_heathBrownDivisorMellinSeriesTerm
example
    {s : ℂ} (hs : 0 < s.re) :
    Summable (fun n : ℕ =>
      ∫ t : ℝ, ‖heathBrownDivisorMellinSeriesTerm s n t‖) :=
  @TaoTrudgianYang2025.summable_integral_norm_heathBrownDivisorMellinSeriesTerm s hs

-- PointMeanDivisorMellin: integral_heathBrownDivisorMellinSeriesTerm
example
    {s : ℂ} (n : ℕ) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        (∫ t : ℝ, heathBrownDivisorMellinSeriesTerm s n t) =
      heathBrownSmoothedDivisorTerm s n :=
  @TaoTrudgianYang2025.integral_heathBrownDivisorMellinSeriesTerm s n

-- PointMeanDivisorMellin: tsum_heathBrownDivisorMellinSeriesTerm_eq
example
    {s : ℂ} (hs : 0 < s.re) (t : ℝ) :
    (∑' n : ℕ, heathBrownDivisorMellinSeriesTerm s n t) =
      heathBrownDivisorMellinIntegrand s t :=
  @TaoTrudgianYang2025.tsum_heathBrownDivisorMellinSeriesTerm_eq s hs t

-- PointMeanDivisorMellin: heathBrown_smoothed_divisor_eq_right_mellin
example
    {s : ℂ} (hs : 0 < s.re) :
    heathBrownSmoothedDivisorSeries s =
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        ∫ t : ℝ, heathBrownDivisorMellinIntegrand s t :=
  @TaoTrudgianYang2025.heathBrown_smoothed_divisor_eq_right_mellin s hs

-- PointMeanDoublePole: rectangleIntegral'_div_sq_eq_deriv
example
    {N : ℂ → ℂ} {z w p : ℂ}
    (hzre : z.re ≤ w.re) (hzim : z.im ≤ w.im)
    (hp : Rectangle z w ∈ 𝓝 p)
    (hN : DifferentiableOn ℂ N (Rectangle z w)) :
    RectangleIntegral' (fun u : ℂ => N u / (u - p) ^ 2) z w =
      deriv N p :=
  @TaoTrudgianYang2025.rectangleIntegral'_div_sq_eq_deriv N z w p hzre hzim hp hN

-- PointMeanMovingPole: heathBrownMovingPoleNumerator_at_pole
example (s : ℂ) :
    heathBrownMovingPoleNumerator s (heathBrownMovingPole s) =
      Complex.Gamma (heathBrownMovingPole s) :=
  @TaoTrudgianYang2025.heathBrownMovingPoleNumerator_at_pole s

-- PointMeanMovingPole: heathBrownZetaSquareMellinIntegrand_eq_poleCleared
example
    {s w : ℂ} (hw : w ≠ heathBrownMovingPole s) :
    heathBrownZetaSquareMellinIntegrand s w =
      heathBrownMovingPoleNumerator s w /
        (w - heathBrownMovingPole s) ^ 2 :=
  @TaoTrudgianYang2025.heathBrownZetaSquareMellinIntegrand_eq_poleCleared s w hw

-- PointMeanMovingPole: differentiableOn_heathBrownMovingPoleNumerator
example
    (s : ℂ) :
    DifferentiableOn ℂ (heathBrownMovingPoleNumerator s)
      {w : ℂ | 0 < w.re} :=
  @TaoTrudgianYang2025.differentiableOn_heathBrownMovingPoleNumerator s

-- PointMeanMovingPole: heathBrownMovingPoleResidue_eq
example
    {s : ℂ} (hp : 0 < (heathBrownMovingPole s).re) :
    heathBrownMovingPoleResidue s =
      Complex.Gamma (heathBrownMovingPole s) *
          Complex.digamma (heathBrownMovingPole s) +
        2 * Complex.Gamma (heathBrownMovingPole s) *
          deriv riemannZetaPoleRemoved 0 :=
  @TaoTrudgianYang2025.heathBrownMovingPoleResidue_eq s hp

-- PointMeanMovingPole: heathBrown_movingPole_finite_rectangle
example
    {s : ℂ} {d c H : ℝ}
    (hd : 0 < d)
    (hdp : d < (heathBrownMovingPole s).re)
    (hpc : (heathBrownMovingPole s).re < c)
    (hH : 0 < H)
    (hpH : |(heathBrownMovingPole s).im| < H) :
    RectangleIntegral' (heathBrownZetaSquareMellinIntegrand s)
        ((d : ℂ) - (H : ℂ) * I) ((c : ℂ) + (H : ℂ) * I) =
      heathBrownMovingPoleResidue s :=
  @TaoTrudgianYang2025.heathBrown_movingPole_finite_rectangle s d c H hd hdp hpc hH hpH

-- PointMeanGammaPole: heathBrownGammaPoleNumerator_zero
example (s : ℂ) :
    heathBrownGammaPoleNumerator s 0 = riemannZeta s ^ 2 :=
  @TaoTrudgianYang2025.heathBrownGammaPoleNumerator_zero s

-- PointMeanGammaPole: heathBrownZetaSquareMellinIntegrand_eq_gammaPoleCleared
example
    {s w : ℂ} (hw : w ≠ 0) :
    heathBrownZetaSquareMellinIntegrand s w =
      heathBrownGammaPoleNumerator s w / w :=
  @TaoTrudgianYang2025.heathBrownZetaSquareMellinIntegrand_eq_gammaPoleCleared s w hw

-- PointMeanGammaPole: heathBrown_gammaPole_finite_rectangle
example
    {s : ℂ} {delta d H : ℝ}
    (hdelta : 0 < delta) (hdeltaUpper : delta < 1)
    (hd : 0 < d) (hdp : d < (heathBrownMovingPole s).re)
    (hH : 0 < H) :
    RectangleIntegral' (heathBrownZetaSquareMellinIntegrand s)
        ((-delta : ℂ) - (H : ℂ) * I) ((d : ℂ) + (H : ℂ) * I) =
      riemannZeta s ^ 2 :=
  @TaoTrudgianYang2025.heathBrown_gammaPole_finite_rectangle s delta d H hdelta hdeltaUpper hd hdp hH

-- PointMeanContourBasic: pintz2023_Gamma_positive_strip_decay
example
    {a t : ℝ} (haLower : 0 ≤ a) (haUpper : a ≤ 2) :
    |t| ^ 3 * ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * I)‖ ≤ 24 :=
  @TaoTrudgianYang2025.pintz2023_Gamma_positive_strip_decay a t haLower haUpper

-- PointMeanContourBasic: ford_norm_eq_re_of_nonneg
example {z : ℂ} (hz : 0 ≤ z) :
    ‖z‖ = z.re :=
  @TaoTrudgianYang2025.ford_norm_eq_re_of_nonneg z hz

-- PointMeanContourBasic: ford_norm_riemannZeta_le_real
example
    {sigma t : ℝ} (hsigma : 1 < sigma) :
    ‖riemannZeta ((sigma : ℂ) + Complex.I * t)‖ ≤
      ‖riemannZeta (sigma : ℂ)‖ :=
  @TaoTrudgianYang2025.ford_norm_riemannZeta_le_real sigma t hsigma

-- PointMeanContourBasic: pintz2023_RectangleIntegral'_eq_edges
example
    (f : ℂ → ℂ) (a b R : ℝ) :
    RectangleIntegral' f
        ((a : ℂ) - (R : ℂ) * I) ((b : ℂ) + (R : ℂ) * I) =
      HIntegral' f a b (-R) - HIntegral' f a b R +
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ u in (-R)..R, f ((b : ℂ) + (u : ℂ) * I)) -
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ u in (-R)..R, f ((a : ℂ) + (u : ℂ) * I)) :=
  @TaoTrudgianYang2025.pintz2023_RectangleIntegral'_eq_edges f a b R

-- PointMeanMellinHorizontal: heathBrown_Gamma_wide_strip_decay
example
    {a t : ℝ} (haLower : -(1 / 4 : ℝ) ≤ a) (haUpper : a ≤ 2) :
    |t| ^ 3 * ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * I)‖ ≤ 24 :=
  @TaoTrudgianYang2025.heathBrown_Gamma_wide_strip_decay a t haLower haUpper

-- PointMeanMellinHorizontal: heathBrown_Gamma_wide_strip_norm_le
example
    {a t : ℝ} (haLower : -(1 / 4 : ℝ) ≤ a) (haUpper : a ≤ 2)
    (ht : 1 ≤ |t|) :
    ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * I)‖ ≤ 24 / |t| ^ 3 :=
  @TaoTrudgianYang2025.heathBrown_Gamma_wide_strip_norm_le a t haLower haUpper ht

-- PointMeanMellinHorizontal: norm_heathBrownZetaSquareMellinIntegrand_horizontal_le
example
    {s : ℂ} (hsLower : 1 / 2 ≤ s.re)
    {x R : ℝ} (hxLower : -(1 / 4 : ℝ) ≤ x) (hxUpper : x ≤ 2)
    (hR : 1 ≤ |R|) (hheight : 1 ≤ |s.im + R|) :
    ‖heathBrownZetaSquareMellinIntegrand s
        ((x : ℂ) + (R : ℂ) * I)‖ ≤
      (24 / |R| ^ 3) *
        (5 * heathBrownMellinHorizontalSize s R) ^ 2 :=
  @TaoTrudgianYang2025.norm_heathBrownZetaSquareMellinIntegrand_horizontal_le s hsLower x R hxLower hxUpper hR hheight

-- PointMeanMellinHorizontal: norm_heathBrownMellin_HIntegral'_le
example
    {s : ℂ} (hsLower : 1 / 2 ≤ s.re)
    {a b R : ℝ} (ha : -(1 / 4 : ℝ) ≤ a) (hb : b ≤ 2) (hab : a ≤ b)
    (hR : 1 ≤ |R|) (hheight : 1 ≤ |s.im + R|) :
    ‖HIntegral' (heathBrownZetaSquareMellinIntegrand s) a b R‖ ≤
      (9 / 4 : ℝ) * ((24 / |R| ^ 3) *
        (5 * heathBrownMellinHorizontalSize s R) ^ 2) :=
  @TaoTrudgianYang2025.norm_heathBrownMellin_HIntegral'_le s hsLower a b R ha hb hab hR hheight

-- PointMeanMellinHorizontal: tendsto_heathBrownMellin_HIntegral'_zero
example
    {s : ℂ} (hsLower : 1 / 2 ≤ s.re)
    {a b : ℝ} (ha : -(1 / 4 : ℝ) ≤ a) (hb : b ≤ 2) (hab : a ≤ b) :
    Tendsto (fun R : ℝ =>
      HIntegral' (heathBrownZetaSquareMellinIntegrand s) a b R)
      atTop (nhds 0) :=
  @TaoTrudgianYang2025.tendsto_heathBrownMellin_HIntegral'_zero s hsLower a b ha hb hab

-- PointMeanMellinHorizontal: tendsto_heathBrownMellin_HIntegral'_neg_zero
example
    {s : ℂ} (hsLower : 1 / 2 ≤ s.re)
    {a b : ℝ} (ha : -(1 / 4 : ℝ) ≤ a) (hb : b ≤ 2) (hab : a ≤ b) :
    Tendsto (fun R : ℝ =>
      HIntegral' (heathBrownZetaSquareMellinIntegrand s) a b (-R))
      atTop (nhds 0) :=
  @TaoTrudgianYang2025.tendsto_heathBrownMellin_HIntegral'_neg_zero s hsLower a b ha hb hab

-- PointMeanMellinVertical: continuous_heathBrownZetaSquareMellinIntegrand_vertical
example
    {s : ℂ} {a : ℝ} (haLower : -(1 : ℝ) < a) (ha0 : a ≠ 0)
    (hpole : s.re + a ≠ 1) :
    Continuous (fun v : ℝ =>
      heathBrownZetaSquareMellinIntegrand s
        ((a : ℂ) + (v : ℂ) * I)) :=
  @TaoTrudgianYang2025.continuous_heathBrownZetaSquareMellinIntegrand_vertical s a haLower ha0 hpole

-- PointMeanMellinVertical: integrable_abs_sq_mul_exp_neg_abs
example :
    Integrable (fun v : ℝ => |v| ^ 2 * Real.exp (-|v|)) :=
  @TaoTrudgianYang2025.integrable_abs_sq_mul_exp_neg_abs

-- PointMeanMellinVertical: integrable_heathBrownZetaSquareMellinIntegrand_plus
example
    {s : ℂ} {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaUpper : delta ≤ 1 / 4) (hsRe : 1 / 4 ≤ s.re + delta)
    (hpole : s.re + delta ≠ 1) :
    Integrable (fun v : ℝ =>
      heathBrownZetaSquareMellinIntegrand s
        ((delta : ℂ) + (v : ℂ) * I)) :=
  @TaoTrudgianYang2025.integrable_heathBrownZetaSquareMellinIntegrand_plus s delta hdelta hdeltaUpper hsRe hpole

-- PointMeanMellinVertical: integrable_heathBrownZetaSquareMellinIntegrand_minus
example
    {s : ℂ} {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaUpper : delta ≤ 1 / 4) (hsRe : 1 / 4 ≤ s.re - delta)
    (hpole : s.re - delta ≠ 1) :
    Integrable (fun v : ℝ =>
      heathBrownZetaSquareMellinIntegrand s
        (((-delta : ℝ) : ℂ) + (v : ℂ) * I)) :=
  @TaoTrudgianYang2025.integrable_heathBrownZetaSquareMellinIntegrand_minus s delta hdelta hdeltaUpper hsRe hpole

-- PointMeanMellinVertical: integrable_heathBrownZetaSquareMellinIntegrand_right
example
    {s : ℂ} (hs : 0 ≤ s.re) :
    Integrable (fun v : ℝ =>
      heathBrownZetaSquareMellinIntegrand s
        (((2 : ℝ) : ℂ) + (v : ℂ) * I)) :=
  @TaoTrudgianYang2025.integrable_heathBrownZetaSquareMellinIntegrand_right s hs

-- PointMeanMellinShift: heathBrown_intermediateLine_pos
example
    {delta : ℝ} (hdeltaUpper : delta ≤ 1 / 4) :
    0 < heathBrownIntermediateLine delta :=
  @TaoTrudgianYang2025.heathBrown_intermediateLine_pos delta hdeltaUpper

-- PointMeanMellinShift: heathBrown_intermediateLine_le_quarter
example
    {delta : ℝ} (hdelta : 0 ≤ delta) :
    heathBrownIntermediateLine delta ≤ 1 / 4 :=
  @TaoTrudgianYang2025.heathBrown_intermediateLine_le_quarter delta hdelta

-- PointMeanMellinShift: heathBrown_movingPole_vertical_shift
example
    {s : ℂ} {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaUpper : delta ≤ 1 / 4)
    (hsRe : s.re = 1 / 2 + delta) :
    VerticalIntegral' (heathBrownZetaSquareMellinIntegrand s) 2 -
        VerticalIntegral' (heathBrownZetaSquareMellinIntegrand s)
          (heathBrownIntermediateLine delta) =
      heathBrownMovingPoleResidue s :=
  @TaoTrudgianYang2025.heathBrown_movingPole_vertical_shift s delta hdelta hdeltaUpper hsRe

-- PointMeanMellinShift: heathBrown_gammaPole_vertical_shift
example
    {s : ℂ} {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaUpper : delta ≤ 1 / 4)
    (hsRe : s.re = 1 / 2 + delta) :
    VerticalIntegral' (heathBrownZetaSquareMellinIntegrand s)
        (heathBrownIntermediateLine delta) -
      VerticalIntegral' (heathBrownZetaSquareMellinIntegrand s) (-delta) =
        riemannZeta s ^ 2 :=
  @TaoTrudgianYang2025.heathBrown_gammaPole_vertical_shift s delta hdelta hdeltaUpper hsRe

-- PointMeanMellinShift: heathBrown_twoPole_vertical_shift
example
    {s : ℂ} {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaUpper : delta ≤ 1 / 4)
    (hsRe : s.re = 1 / 2 + delta) :
    VerticalIntegral' (heathBrownZetaSquareMellinIntegrand s) 2 -
      VerticalIntegral' (heathBrownZetaSquareMellinIntegrand s) (-delta) =
        heathBrownMovingPoleResidue s + riemannZeta s ^ 2 :=
  @TaoTrudgianYang2025.heathBrown_twoPole_vertical_shift s delta hdelta hdeltaUpper hsRe

-- PointMeanMellinShift: heathBrownSmoothedDivisorSeries_eq_rightVertical
example
    {s : ℂ} (hs : 0 < s.re) :
    heathBrownSmoothedDivisorSeries s =
      VerticalIntegral' (heathBrownZetaSquareMellinIntegrand s) 2 :=
  @TaoTrudgianYang2025.heathBrownSmoothedDivisorSeries_eq_rightVertical s hs

-- PointMeanMellinShift: heathBrown_zetaSquare_eq_smoothed_sub_residue_sub_leftVertical
example
    {s : ℂ} {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaUpper : delta ≤ 1 / 4)
    (hsRe : s.re = 1 / 2 + delta) :
    riemannZeta s ^ 2 =
      heathBrownSmoothedDivisorSeries s - heathBrownMovingPoleResidue s -
        VerticalIntegral' (heathBrownZetaSquareMellinIntegrand s) (-delta) :=
  @TaoTrudgianYang2025.heathBrown_zetaSquare_eq_smoothed_sub_residue_sub_leftVertical s delta hdelta hdeltaUpper hsRe

-- PointMeanMellinBounds: summable_heathBrownSmoothedDivisorMajorant
example :
    Summable (fun n : ℕ => (n : ℝ) * Real.exp (-(n : ℝ))) :=
  @TaoTrudgianYang2025.summable_heathBrownSmoothedDivisorMajorant

-- PointMeanMellinBounds: heathBrownSmoothedDivisorMajorant_nonneg
example :
    0 ≤ heathBrownSmoothedDivisorMajorant :=
  @TaoTrudgianYang2025.heathBrownSmoothedDivisorMajorant_nonneg

-- PointMeanMellinBounds: norm_heathBrownSmoothedDivisorTerm_le
example
    {s : ℂ} (hs : 0 ≤ s.re) (n : ℕ) :
    ‖heathBrownSmoothedDivisorTerm s n‖ ≤
      (n : ℝ) * Real.exp (-(n : ℝ)) :=
  @TaoTrudgianYang2025.norm_heathBrownSmoothedDivisorTerm_le s hs n

-- PointMeanMellinBounds: summable_norm_heathBrownSmoothedDivisorTerm
example
    {s : ℂ} (hs : 0 ≤ s.re) :
    Summable (fun n : ℕ => ‖heathBrownSmoothedDivisorTerm s n‖) :=
  @TaoTrudgianYang2025.summable_norm_heathBrownSmoothedDivisorTerm s hs

-- PointMeanMellinBounds: norm_heathBrownSmoothedDivisorSeries_le
example
    {s : ℂ} (hs : 0 ≤ s.re) :
    ‖heathBrownSmoothedDivisorSeries s‖ ≤
      heathBrownSmoothedDivisorMajorant :=
  @TaoTrudgianYang2025.norm_heathBrownSmoothedDivisorSeries_le s hs

-- PointMeanMellinBounds: exists_norm_Gamma_heathBrown_residue_strip_le
example :
    ∃ C : ℝ, 0 < C ∧ ∀ (a v : ℝ),
      5 / 4 ≤ a → a ≤ 3 / 2 →
      ‖Complex.Gamma ((a : ℂ) + (v : ℂ) * I)‖ ≤
        C * Real.exp (-|v|) :=
  @TaoTrudgianYang2025.exists_norm_Gamma_heathBrown_residue_strip_le

-- PointMeanMellinBounds: exists_norm_Gamma_heathBrown_movingPole_le
example :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta v : ℝ),
      0 < delta → delta ≤ 1 / 4 →
      ‖Complex.Gamma
          (((1 / 2 - delta : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
        C * Real.exp (-|v|) :=
  @TaoTrudgianYang2025.exists_norm_Gamma_heathBrown_movingPole_le

-- PointMeanMellinBounds: exists_norm_heathBrownMovingPoleResidue_le
example :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta t : ℝ),
      0 < delta → delta ≤ 1 / 4 → 10 ≤ t →
      ‖heathBrownMovingPoleResidue
          (((1 / 2 + delta : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ C :=
  @TaoTrudgianYang2025.exists_norm_heathBrownMovingPoleResidue_le

-- PointMeanOffCritical: integrable_heathBrownMellinCriticalMoment
example
    {delta t : ℝ} (hdelta : 0 < delta) :
    Integrable (fun u : ℝ => Real.exp (-|u|) / (delta + |u|) *
      zetaMomentCriticalNorm (t + u) ^ (2 : ℕ)) :=
  @TaoTrudgianYang2025.integrable_heathBrownMellinCriticalMoment delta t hdelta

-- PointMeanOffCritical: integrable_heathBrownFullCriticalMoment
example (t : ℝ) :
    Integrable (fun u : ℝ => Real.exp (-|u|) *
      zetaMomentCriticalNorm (t + u) ^ (2 : ℕ)) :=
  @TaoTrudgianYang2025.integrable_heathBrownFullCriticalMoment t

-- PointMeanOffCritical: heathBrownMellinCriticalMoment_le_full
example
    {delta t : ℝ} (hdelta : 0 < delta) :
    heathBrownMellinCriticalMoment delta t ≤
      (1 / delta) * heathBrownFullCriticalMoment t :=
  @TaoTrudgianYang2025.heathBrownMellinCriticalMoment_le_full delta t hdelta

-- PointMeanOffCritical: heathBrownMellinCriticalMoment_nonneg
example
    {delta t : ℝ} (hdelta : 0 < delta) :
    0 ≤ heathBrownMellinCriticalMoment delta t :=
  @TaoTrudgianYang2025.heathBrownMellinCriticalMoment_nonneg delta t hdelta

-- PointMeanOffCritical: heathBrownFullCriticalMoment_nonneg
example (t : ℝ) :
    0 ≤ heathBrownFullCriticalMoment t :=
  @TaoTrudgianYang2025.heathBrownFullCriticalMoment_nonneg t

-- PointMeanOffCritical: exists_norm_heathBrown_leftMellinIntegrand_le
example :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta t u : ℝ),
      0 < delta → delta ≤ 1 / 4 →
      ‖heathBrownZetaSquareMellinIntegrand
          (((1 / 2 + delta : ℝ) : ℂ) + (t : ℂ) * I)
          (((-delta : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤
        C * (Real.exp (-|u|) / (delta + |u|) *
          zetaMomentCriticalNorm (t + u) ^ (2 : ℕ)) :=
  @TaoTrudgianYang2025.exists_norm_heathBrown_leftMellinIntegrand_le

-- PointMeanOffCritical: exists_norm_heathBrown_leftVertical_le
example :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta t : ℝ),
      0 < delta → delta ≤ 1 / 4 →
      ‖VerticalIntegral'
          (heathBrownZetaSquareMellinIntegrand
            (((1 / 2 + delta : ℝ) : ℂ) + (t : ℂ) * I)) (-delta)‖ ≤
        C * heathBrownMellinCriticalMoment delta t :=
  @TaoTrudgianYang2025.exists_norm_heathBrown_leftVertical_le

-- PointMeanOffCritical: exists_heathBrown_offCritical_plus_le
example :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta t : ℝ),
      0 < delta → delta ≤ 1 / 4 → 10 ≤ t →
      ‖riemannZeta
          (((1 / 2 + delta : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ (2 : ℕ) ≤
        C * (1 + heathBrownMellinCriticalMoment delta t) :=
  @TaoTrudgianYang2025.exists_heathBrown_offCritical_plus_le

-- PointMeanOffCritical: exists_heathBrown_offCritical_plus_log_le
example :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, Real.exp 4 ≤ t →
      ‖riemannZeta
          (((1 / 2 + 1 / Real.log t : ℝ) : ℂ) + (t : ℂ) * I)‖ ^
          (2 : ℕ) ≤
        C * (1 + Real.log t * heathBrownFullCriticalMoment t) :=
  @TaoTrudgianYang2025.exists_heathBrown_offCritical_plus_log_le

-- PointMeanReflection: norm_GammaR_real_im
example (r t : ℝ) :
    ‖Complex.Gammaℝ ((r : ℂ) + (t : ℂ) * I)‖ =
      Real.pi ^ (-r / 2) *
        ‖Complex.Gamma (((r / 2 : ℝ) : ℂ) +
          ((t / 2 : ℝ) : ℂ) * I)‖ :=
  @TaoTrudgianYang2025.norm_GammaR_real_im r t

-- PointMeanReflection: norm_GammaR_real_neg_im_eq
example (r t : ℝ) :
    ‖Complex.Gammaℝ ((r : ℂ) + ((-t : ℝ) : ℂ) * I)‖ =
      ‖Complex.Gammaℝ ((r : ℂ) + (t : ℂ) * I)‖ :=
  @TaoTrudgianYang2025.norm_GammaR_real_neg_im_eq r t

-- PointMeanReflection: heathBrown_zeta_displaced_reflection
example
    {delta t : ℝ} (hdelta : 0 < delta) (hdeltaUpper : delta < 1 / 2) :
    riemannZeta
        (((1 / 2 - delta : ℝ) : ℂ) + (t : ℂ) * I) =
      (Complex.Gammaℝ
          (((1 / 2 + delta : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) /
        Complex.Gammaℝ
          (((1 / 2 - delta : ℝ) : ℂ) + (t : ℂ) * I)) *
        riemannZeta
          (((1 / 2 + delta : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) :=
  @TaoTrudgianYang2025.heathBrown_zeta_displaced_reflection delta t hdelta hdeltaUpper

-- PointMeanReflection: exists_norm_GammaR_heathBrown_reflection_ratio_le
example :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta t : ℝ),
      0 < delta → delta ≤ 1 / 4 → 4 ≤ t →
      ‖Complex.Gammaℝ
          (((1 / 2 + delta : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) /
        Complex.Gammaℝ
          (((1 / 2 - delta : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        Real.exp ((Real.log (t / 2 + 2) + C) * delta) :=
  @TaoTrudgianYang2025.exists_norm_GammaR_heathBrown_reflection_ratio_le

-- PointMeanReflection: exists_heathBrown_offCritical_minus_le
example :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ (delta t : ℝ),
      0 < delta → delta ≤ 1 / 4 → 10 ≤ t →
      ‖riemannZeta
          (((1 / 2 - delta : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ (2 : ℕ) ≤
        C * Real.exp (2 * (Real.log (t / 2 + 2) + D) * delta) *
          (1 + heathBrownMellinCriticalMoment delta t) :=
  @TaoTrudgianYang2025.exists_heathBrown_offCritical_minus_le

-- PointMeanReflection: exists_heathBrown_offCritical_minus_log_le
example :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, Real.exp 4 ≤ t →
      ‖riemannZeta
          (((1 / 2 - 1 / Real.log t : ℝ) : ℂ) + (t : ℂ) * I)‖ ^
          (2 : ℕ) ≤
        C * (1 + Real.log t * heathBrownFullCriticalMoment t) :=
  @TaoTrudgianYang2025.exists_heathBrown_offCritical_minus_log_le

-- PointMeanOffCriticalStrong: integrable_heathBrownStrongMellinCriticalMoment
example
    {delta t : ℝ} (hdelta : 0 < delta) :
    Integrable (fun u : ℝ =>
      Real.exp (-(4 / 3 : ℝ) * |u|) / (delta + |u|) *
        zetaMomentCriticalNorm (t + u) ^ (2 : ℕ)) :=
  @TaoTrudgianYang2025.integrable_heathBrownStrongMellinCriticalMoment delta t hdelta

-- PointMeanOffCriticalStrong: heathBrownStrongMellinCriticalMoment_nonneg
example
    {delta t : ℝ} (hdelta : 0 < delta) :
    0 ≤ heathBrownStrongMellinCriticalMoment delta t :=
  @TaoTrudgianYang2025.heathBrownStrongMellinCriticalMoment_nonneg delta t hdelta

-- PointMeanOffCriticalStrong: exists_norm_heathBrown_leftMellinIntegrand_strong_le
example :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta t u : ℝ),
      0 < delta → delta ≤ 1 / 4 →
      ‖heathBrownZetaSquareMellinIntegrand
          (((1 / 2 + delta : ℝ) : ℂ) + (t : ℂ) * I)
          (((-delta : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤
        C * (Real.exp (-(4 / 3 : ℝ) * |u|) / (delta + |u|) *
          zetaMomentCriticalNorm (t + u) ^ (2 : ℕ)) :=
  @TaoTrudgianYang2025.exists_norm_heathBrown_leftMellinIntegrand_strong_le

-- PointMeanOffCriticalStrong: exists_norm_heathBrown_leftVertical_strong_le
example :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta t : ℝ),
      0 < delta → delta ≤ 1 / 4 →
      ‖VerticalIntegral'
          (heathBrownZetaSquareMellinIntegrand
            (((1 / 2 + delta : ℝ) : ℂ) + (t : ℂ) * I)) (-delta)‖ ≤
        C * heathBrownStrongMellinCriticalMoment delta t :=
  @TaoTrudgianYang2025.exists_norm_heathBrown_leftVertical_strong_le

-- PointMeanOffCriticalStrong: exists_heathBrown_offCritical_plus_strong_le
example :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta t : ℝ),
      0 < delta → delta ≤ 1 / 4 → 10 ≤ t →
      ‖riemannZeta
          (((1 / 2 + delta : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ (2 : ℕ) ≤
        C * (1 + heathBrownStrongMellinCriticalMoment delta t) :=
  @TaoTrudgianYang2025.exists_heathBrown_offCritical_plus_strong_le

-- PointMeanOffCriticalStrong: exists_heathBrown_offCritical_minus_strong_le
example :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ (delta t : ℝ),
      0 < delta → delta ≤ 1 / 4 → 10 ≤ t →
      ‖riemannZeta
          (((1 / 2 - delta : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ (2 : ℕ) ≤
        C * Real.exp (2 * (Real.log (t / 2 + 2) + D) * delta) *
          (1 + heathBrownStrongMellinCriticalMoment delta t) :=
  @TaoTrudgianYang2025.exists_heathBrown_offCritical_minus_strong_le

-- PointMeanLemmaThreeStatement: heathBrownLemmaThreeMoment_eq_centered
example (t L : ℝ) :
    heathBrownLemmaThreeMoment t L =
      ∫ v in t - L..t + L,
        Real.exp (-|t - v|) * zetaMomentCriticalNorm v ^ (2 : ℕ) :=
  @TaoTrudgianYang2025.heathBrownLemmaThreeMoment_eq_centered t L

-- PointMeanLemmaThreeStatement: heathBrownLemmaThreeMoment_le_centered
example
    (t L : ℝ) (hlogL : Real.log t ^ (2 : ℕ) ≤ L) :
    heathBrownLemmaThreeMoment t (Real.log t ^ (2 : ℕ)) ≤
      ∫ v in t - L..t + L,
        Real.exp (-|t - v|) * zetaMomentCriticalNorm v ^ (2 : ℕ) :=
  @TaoTrudgianYang2025.heathBrownLemmaThreeMoment_le_centered t L hlogL

-- PointMeanLemmaThreeContour: two_lt_log_of_ten_le
example {t : ℝ} (ht : 10 ≤ t) :
    2 < Real.log t :=
  @TaoTrudgianYang2025.two_lt_log_of_ten_le t ht

-- PointMeanLemmaThreeContour: heathBrownLemmaThreeDelta_pos
example {t : ℝ} (ht : 10 ≤ t) :
    0 < heathBrownLemmaThreeDelta t :=
  @TaoTrudgianYang2025.heathBrownLemmaThreeDelta_pos t ht

-- PointMeanLemmaThreeContour: heathBrownLemmaThreeDelta_lt_half
example {t : ℝ} (ht : 10 ≤ t) :
    heathBrownLemmaThreeDelta t < 1 / 2 :=
  @TaoTrudgianYang2025.heathBrownLemmaThreeDelta_lt_half t ht

-- PointMeanLemmaThreeContour: heathBrownLemmaThreeRadius_pos
example {t : ℝ} (ht : 10 ≤ t) :
    0 < heathBrownLemmaThreeRadius t :=
  @TaoTrudgianYang2025.heathBrownLemmaThreeRadius_pos t ht

-- PointMeanLemmaThreeContour: heathBrownLemmaThree_finiteRectangle
example (t : ℝ) (ht : 10 ≤ t) :
    RectangleIntegral'
        (heathBrownZetaSquareMellinIntegrand
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))
        (((-heathBrownLemmaThreeDelta t : ℝ) : ℂ) -
          (heathBrownLemmaThreeRadius t : ℂ) * I)
        (((heathBrownLemmaThreeDelta t : ℝ) : ℂ) +
          (heathBrownLemmaThreeRadius t : ℂ) * I) =
      riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ^ 2 :=
  @TaoTrudgianYang2025.heathBrownLemmaThree_finiteRectangle t ht

-- PointMeanLemmaThreeContour: heathBrownLemmaThree_rectangle_eq_edges
example (t : ℝ) :
    let s : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I
    let delta : ℝ := heathBrownLemmaThreeDelta t
    let H : ℝ := heathBrownLemmaThreeRadius t
    RectangleIntegral' (heathBrownZetaSquareMellinIntegrand s)
        (((-delta : ℝ) : ℂ) - (H : ℂ) * I)
        (((delta : ℝ) : ℂ) + (H : ℂ) * I) =
      HIntegral' (heathBrownZetaSquareMellinIntegrand s) (-delta) delta (-H) -
        HIntegral' (heathBrownZetaSquareMellinIntegrand s) (-delta) delta H +
        VIntegral' (heathBrownZetaSquareMellinIntegrand s) delta (-H) H -
        VIntegral' (heathBrownZetaSquareMellinIntegrand s) (-delta) (-H) H :=
  @TaoTrudgianYang2025.heathBrownLemmaThree_rectangle_eq_edges t

-- PointMeanLemmaThreeDouble: integrable_heathBrownCriticalWeighted
example (t : ℝ) :
    Integrable (heathBrownCriticalWeighted t) :=
  @TaoTrudgianYang2025.integrable_heathBrownCriticalWeighted t

-- PointMeanLemmaThreeDouble: heathBrownCriticalWeighted_nonneg
example (t u : ℝ) :
    0 ≤ heathBrownCriticalWeighted t u :=
  @TaoTrudgianYang2025.heathBrownCriticalWeighted_nonneg t u

-- PointMeanLemmaThreeDouble: integrable_heathBrown_reserve_sq_mul_critical_add
example
    {delta : ℝ} (hdelta : 0 < delta) (t : ℝ) :
    Integrable (fun p : ℝ × ℝ =>
      heathBrownGammaReserveKernel delta p.1 ^ (2 : ℕ) *
        heathBrownCriticalWeighted t (p.1 + p.2)) :=
  @TaoTrudgianYang2025.integrable_heathBrown_reserve_sq_mul_critical_add delta hdelta t

-- PointMeanLemmaThreeDouble: integral_heathBrown_reserve_sq_mul_critical_add
example
    {delta : ℝ} (hdelta : 0 < delta) (t : ℝ) :
    (∫ p : ℝ × ℝ,
      heathBrownGammaReserveKernel delta p.1 ^ (2 : ℕ) *
        heathBrownCriticalWeighted t (p.1 + p.2)) =
      (∫ w : ℝ, heathBrownGammaReserveKernel delta w ^ (2 : ℕ)) *
        heathBrownFullCriticalMoment t :=
  @TaoTrudgianYang2025.integral_heathBrown_reserve_sq_mul_critical_add delta hdelta t

-- PointMeanLemmaThreeDouble: integrable_heathBrown_reserve_sq_snd_mul_critical_add
example
    {delta : ℝ} (hdelta : 0 < delta) (t : ℝ) :
    Integrable (fun p : ℝ × ℝ =>
      heathBrownGammaReserveKernel delta p.2 ^ (2 : ℕ) *
        heathBrownCriticalWeighted t (p.1 + p.2)) :=
  @TaoTrudgianYang2025.integrable_heathBrown_reserve_sq_snd_mul_critical_add delta hdelta t

-- PointMeanLemmaThreeDouble: integral_heathBrown_reserve_sq_snd_mul_critical_add
example
    {delta : ℝ} (hdelta : 0 < delta) (t : ℝ) :
    (∫ p : ℝ × ℝ,
      heathBrownGammaReserveKernel delta p.2 ^ (2 : ℕ) *
        heathBrownCriticalWeighted t (p.1 + p.2)) =
      (∫ w : ℝ, heathBrownGammaReserveKernel delta w ^ (2 : ℕ)) *
        heathBrownFullCriticalMoment t :=
  @TaoTrudgianYang2025.integral_heathBrown_reserve_sq_snd_mul_critical_add delta hdelta t

-- PointMeanLemmaThreeDouble: heathBrownStrongDoubleIntegrand_nonneg
example
    {delta t : ℝ} (hdelta : 0 < delta) (p : ℝ × ℝ) :
    0 ≤ heathBrownStrongDoubleIntegrand delta t p :=
  @TaoTrudgianYang2025.heathBrownStrongDoubleIntegrand_nonneg delta t hdelta p

-- PointMeanLemmaThreeDouble: heathBrownStrongDoubleIntegrand_le
example
    {delta t : ℝ} (hdelta : 0 < delta) (p : ℝ × ℝ) :
    heathBrownStrongDoubleIntegrand delta t p ≤
      heathBrownStrongDoubleMajorant delta t p :=
  @TaoTrudgianYang2025.heathBrownStrongDoubleIntegrand_le delta t hdelta p

-- PointMeanLemmaThreeDouble: integrable_heathBrownStrongDoubleMajorant
example
    {delta : ℝ} (hdelta : 0 < delta) (t : ℝ) :
    Integrable (heathBrownStrongDoubleMajorant delta t) :=
  @TaoTrudgianYang2025.integrable_heathBrownStrongDoubleMajorant delta hdelta t

-- PointMeanLemmaThreeDouble: integrable_heathBrownStrongDoubleIntegrand
example
    {delta : ℝ} (hdelta : 0 < delta) (t : ℝ) :
    Integrable (heathBrownStrongDoubleIntegrand delta t) :=
  @TaoTrudgianYang2025.integrable_heathBrownStrongDoubleIntegrand delta hdelta t

-- PointMeanLemmaThreeDouble: integral_heathBrownStrongDoubleIntegrand_le
example
    {delta : ℝ} (hdelta : 0 < delta) (t : ℝ) :
    (∫ p : ℝ × ℝ, heathBrownStrongDoubleIntegrand delta t p) ≤
      (Real.pi / delta) * heathBrownFullCriticalMoment t :=
  @TaoTrudgianYang2025.integral_heathBrownStrongDoubleIntegrand_le delta hdelta t

-- PointMeanLemmaThreeDouble: integral_strongKernel_mul_strongMoment_eq_double
example
    {delta : ℝ} (hdelta : 0 < delta) (t : ℝ) :
    (∫ w : ℝ, heathBrownStrongSingularKernel delta w *
        heathBrownStrongMellinCriticalMoment delta (t + w)) =
      ∫ p : ℝ × ℝ, heathBrownStrongDoubleIntegrand delta t p :=
  @TaoTrudgianYang2025.integral_strongKernel_mul_strongMoment_eq_double delta hdelta t

-- PointMeanLemmaThreeDouble: integrable_strongKernel_mul_strongMoment
example
    {delta : ℝ} (hdelta : 0 < delta) (t : ℝ) :
    Integrable (fun w : ℝ => heathBrownStrongSingularKernel delta w *
        heathBrownStrongMellinCriticalMoment delta (t + w)) :=
  @TaoTrudgianYang2025.integrable_strongKernel_mul_strongMoment delta hdelta t

-- PointMeanLemmaThreeDouble: integral_strongKernel_mul_strongMoment_le
example
    {delta : ℝ} (hdelta : 0 < delta) (t : ℝ) :
    (∫ w : ℝ, heathBrownStrongSingularKernel delta w *
        heathBrownStrongMellinCriticalMoment delta (t + w)) ≤
      (Real.pi / delta) * heathBrownFullCriticalMoment t :=
  @TaoTrudgianYang2025.integral_strongKernel_mul_strongMoment_le delta hdelta t

-- PointMeanLemmaThreeEdges: eventually_log_sq_le_rpow
example {q : ℝ} (hq : 0 < q) :
    ∀ᶠ X : ℝ in atTop, (Real.log X) ^ 2 ≤ X ^ q :=
  @TaoTrudgianYang2025.eventually_log_sq_le_rpow q hq

-- PointMeanLemmaThreeEdges: eventually_const_mul_rpow_le_rpow
example
    {D a b : Real} (hab : a < b) :
    ∀ᶠ U : Real in atTop, D * U ^ a <= U ^ b :=
  @TaoTrudgianYang2025.eventually_const_mul_rpow_le_rpow D a b hab

-- PointMeanLemmaThreeEdges: integral_exp_neg_abs_heathBrown
example :
    (∫ x : ℝ, Real.exp (-|x|)) = 2 :=
  @TaoTrudgianYang2025.integral_exp_neg_abs_heathBrown

-- PointMeanLemmaThreeEdges: integrable_exp_neg_abs_heathBrown
example :
    Integrable (fun x : ℝ => Real.exp (-|x|)) :=
  @TaoTrudgianYang2025.integrable_exp_neg_abs_heathBrown

-- PointMeanLemmaThreeEdges: heathBrownStrongSingularKernel_le_exp
example
    {delta x : ℝ} (hdelta : 0 < delta) :
    heathBrownStrongSingularKernel delta x ≤
      delta⁻¹ * Real.exp (-|x|) :=
  @TaoTrudgianYang2025.heathBrownStrongSingularKernel_le_exp delta x hdelta

-- PointMeanLemmaThreeEdges: integrable_heathBrownStrongSingularKernel
example
    {delta : ℝ} (hdelta : 0 < delta) :
    Integrable (heathBrownStrongSingularKernel delta) :=
  @TaoTrudgianYang2025.integrable_heathBrownStrongSingularKernel delta hdelta

-- PointMeanLemmaThreeEdges: integral_heathBrownStrongSingularKernel_le
example
    {delta : ℝ} (hdelta : 0 < delta) :
    (∫ x : ℝ, heathBrownStrongSingularKernel delta x) ≤ 2 / delta :=
  @TaoTrudgianYang2025.integral_heathBrownStrongSingularKernel_le delta hdelta

-- PointMeanLemmaThreeEdges: intervalIntegral_heathBrownStrongSingularKernel_le
example
    {delta H : ℝ} (hdelta : 0 < delta) (hH : 0 ≤ H) :
    (∫ x in -H..H, heathBrownStrongSingularKernel delta x) ≤ 2 / delta :=
  @TaoTrudgianYang2025.intervalIntegral_heathBrownStrongSingularKernel_le delta H hdelta hH

-- PointMeanLemmaThreeEdges: norm_VIntegral'_le_intervalIntegral_norm
example
    (f : ℂ → ℂ) {x a b : ℝ} (hab : a ≤ b) :
    ‖VIntegral' f x a b‖ ≤
      ∫ y in a..b, ‖f ((x : ℂ) + (y : ℂ) * I)‖ :=
  @TaoTrudgianYang2025.norm_VIntegral'_le_intervalIntegral_norm f x a b hab

-- PointMeanLemmaThreeEdges: exists_norm_heathBrownLemmaThree_plusEdge_integrand_le
example :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta t w : ℝ),
      0 < delta → delta ≤ 1 / 4 → 10 ≤ t + w →
      ‖heathBrownZetaSquareMellinIntegrand
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
          (((delta : ℝ) : ℂ) + (w : ℂ) * I)‖ ≤
        C * (heathBrownStrongSingularKernel delta w *
          (1 + heathBrownStrongMellinCriticalMoment delta (t + w))) :=
  @TaoTrudgianYang2025.exists_norm_heathBrownLemmaThree_plusEdge_integrand_le

-- PointMeanLemmaThreeEdges: integrable_heathBrownStrongLongEdgeMajorant
example
    {delta : ℝ} (hdelta : 0 < delta) (t : ℝ) :
    Integrable (fun w : ℝ => heathBrownStrongSingularKernel delta w *
      (1 + heathBrownStrongMellinCriticalMoment delta (t + w))) :=
  @TaoTrudgianYang2025.integrable_heathBrownStrongLongEdgeMajorant delta hdelta t

-- PointMeanLemmaThreeEdges: integral_heathBrownStrongLongEdgeMajorant_le
example
    {delta : ℝ} (hdelta : 0 < delta) (t : ℝ) :
    (∫ w : ℝ, heathBrownStrongSingularKernel delta w *
      (1 + heathBrownStrongMellinCriticalMoment delta (t + w))) ≤
        ((2 + Real.pi) / delta) * (1 + heathBrownFullCriticalMoment t) :=
  @TaoTrudgianYang2025.integral_heathBrownStrongLongEdgeMajorant_le delta hdelta t

-- PointMeanLemmaThreeEdges: exists_norm_heathBrownLemmaThree_plusEdge_le
example :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta t H : ℝ),
      0 < delta → delta ≤ 1 / 4 → 0 ≤ H → 10 + H ≤ t →
      ‖VIntegral' (heathBrownZetaSquareMellinIntegrand
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) delta (-H) H‖ ≤
        (C / delta) * (1 + heathBrownFullCriticalMoment t) :=
  @TaoTrudgianYang2025.exists_norm_heathBrownLemmaThree_plusEdge_le

-- PointMeanLemmaThreeEdges: exists_norm_heathBrownLemmaThree_minusEdge_integrand_le
example :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ (delta t w : ℝ),
      0 < delta → delta ≤ 1 / 4 → 10 ≤ t + w →
      ‖heathBrownZetaSquareMellinIntegrand
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
          (((-delta : ℝ) : ℂ) + (w : ℂ) * I)‖ ≤
        C * Real.exp
          (2 * (Real.log ((t + w) / 2 + 2) + D) * delta) *
            (heathBrownStrongSingularKernel delta w *
              (1 + heathBrownStrongMellinCriticalMoment delta (t + w))) :=
  @TaoTrudgianYang2025.exists_norm_heathBrownLemmaThree_minusEdge_integrand_le

-- PointMeanLemmaThreeEdges: exists_norm_heathBrownLemmaThree_minusEdge_le
example :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ (delta t H Q : ℝ),
      0 < delta → delta ≤ 1 / 4 → 0 ≤ H → 10 + H ≤ t → 0 ≤ Q →
      (∀ w ∈ Set.Icc (-H) H,
        Real.exp (2 * (Real.log ((t + w) / 2 + 2) + D) * delta) ≤ Q) →
      ‖VIntegral' (heathBrownZetaSquareMellinIntegrand
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) (-delta) (-H) H‖ ≤
        ((C * Q) / delta) * (1 + heathBrownFullCriticalMoment t) :=
  @TaoTrudgianYang2025.exists_norm_heathBrownLemmaThree_minusEdge_le

-- PointMeanLemmaThreeEdges: eventually_heathBrownLemmaThreeRadius_le_half_identity
example :
    ∀ᶠ t : ℝ in Filter.atTop,
      heathBrownLemmaThreeRadius t ≤ t / 2 :=
  @TaoTrudgianYang2025.eventually_heathBrownLemmaThreeRadius_le_half_identity

-- PointMeanLemmaThreeEdges: heathBrownLemmaThree_minus_factor_le_exp_four
example
    {D t w : ℝ} (ht : 8 ≤ t)
    (hRadius : heathBrownLemmaThreeRadius t ≤ t / 2)
    (hDlog : D ≤ Real.log t)
    (hw : w ∈ Set.Icc (-heathBrownLemmaThreeRadius t)
      (heathBrownLemmaThreeRadius t)) :
    Real.exp (2 * (Real.log ((t + w) / 2 + 2) + D) *
      heathBrownLemmaThreeDelta t) ≤ Real.exp 4 :=
  @TaoTrudgianYang2025.heathBrownLemmaThree_minus_factor_le_exp_four D t w ht hRadius hDlog hw

-- PointMeanLemmaThreeEdges: eventually_heathBrownLemmaThree_minus_factor
example
    (D : ℝ) :
    ∀ᶠ t : ℝ in Filter.atTop, ∀ w ∈
      Set.Icc (-heathBrownLemmaThreeRadius t) (heathBrownLemmaThreeRadius t),
      Real.exp (2 * (Real.log ((t + w) / 2 + 2) + D) *
        heathBrownLemmaThreeDelta t) ≤ Real.exp 4 :=
  @TaoTrudgianYang2025.eventually_heathBrownLemmaThree_minus_factor D

-- PointMeanLemmaThreeEdges: exists_norm_Gamma_heathBrown_small_horizontal_strong_le
example :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta x R : ℝ),
      0 < delta → delta ≤ 1 / 4 → x ∈ Set.Icc (-delta) delta → 1 ≤ |R| →
      ‖Complex.Gamma ((x : ℂ) + (R : ℂ) * I)‖ ≤
        C * Real.exp (-(4 / 3 : ℝ) * |R|) :=
  @TaoTrudgianYang2025.exists_norm_Gamma_heathBrown_small_horizontal_strong_le

-- PointMeanLemmaThreeEdges: exists_norm_heathBrownLemmaThree_horizontal_integrand_le
example :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta t x R : ℝ),
      0 < delta → delta ≤ 1 / 4 → x ∈ Set.Icc (-delta) delta →
      1 ≤ |t + R| → 1 ≤ |R| →
      ‖heathBrownZetaSquareMellinIntegrand
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
          (((x : ℝ) : ℂ) + (R : ℂ) * I)‖ ≤
        C * Real.exp (-(4 / 3 : ℝ) * |R|) *
          (5 * (1 + |t| + |R|)) ^ (2 : ℕ) :=
  @TaoTrudgianYang2025.exists_norm_heathBrownLemmaThree_horizontal_integrand_le

-- PointMeanLemmaThreeEdges: exists_norm_heathBrownLemmaThree_horizontalEdge_le
example :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta t R : ℝ),
      0 < delta → delta ≤ 1 / 4 → 1 ≤ |t + R| → 1 ≤ |R| →
      ‖HIntegral' (heathBrownZetaSquareMellinIntegrand
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) (-delta) delta R‖ ≤
        C * Real.exp (-(4 / 3 : ℝ) * |R|) *
          (5 * (1 + |t| + |R|)) ^ (2 : ℕ) :=
  @TaoTrudgianYang2025.exists_norm_heathBrownLemmaThree_horizontalEdge_le

-- PointMeanLemmaThreeEdges: heathBrown_logSquare_exponential_absorption
example
    {D t : ℝ} (ht : 0 < t) (hDt : D ≤ t)
    (hlog : 9 / 4 ≤ Real.log t) :
    D * t ^ (2 : ℕ) *
      Real.exp (-(4 / 3 : ℝ) * (Real.log t ^ (2 : ℕ))) ≤ 1 :=
  @TaoTrudgianYang2025.heathBrown_logSquare_exponential_absorption D t ht hDt hlog

-- PointMeanLemmaThreeEdges: eventually_norm_heathBrownLemmaThree_horizontalEdges_le_one
example :
    ∀ᶠ t : ℝ in Filter.atTop,
      ‖HIntegral' (heathBrownZetaSquareMellinIntegrand
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))
          (-heathBrownLemmaThreeDelta t) (heathBrownLemmaThreeDelta t)
          (-heathBrownLemmaThreeRadius t)‖ ≤ 1 ∧
      ‖HIntegral' (heathBrownZetaSquareMellinIntegrand
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))
          (-heathBrownLemmaThreeDelta t) (heathBrownLemmaThreeDelta t)
          (heathBrownLemmaThreeRadius t)‖ ≤ 1 :=
  @TaoTrudgianYang2025.eventually_norm_heathBrownLemmaThree_horizontalEdges_le_one

-- PointMeanLemmaThreeEdges: exists_eventually_heathBrownLemmaThree_fullMoment
example :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in Filter.atTop,
      zetaMomentCriticalNorm t ^ (2 : ℕ) ≤
        C * Real.log t * (1 + heathBrownFullCriticalMoment t) :=
  @TaoTrudgianYang2025.exists_eventually_heathBrownLemmaThree_fullMoment

-- PointMeanLemmaThreeTail: exists_zetaMomentCriticalNorm_sq_le_quadratic
example :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ,
      zetaMomentCriticalNorm y ^ (2 : ℕ) ≤ C * (1 + y ^ (2 : ℕ)) :=
  @TaoTrudgianYang2025.exists_zetaMomentCriticalNorm_sq_le_quadratic

-- PointMeanLemmaThreeTail: integral_exp_neg_half_abs_heathBrown
example :
    (∫ x : ℝ, Real.exp (-|x| / 2)) = 4 :=
  @TaoTrudgianYang2025.integral_exp_neg_half_abs_heathBrown

-- PointMeanLemmaThreeTail: integrable_exp_neg_half_abs_heathBrown
example :
    Integrable (fun x : ℝ => Real.exp (-|x| / 2)) :=
  @TaoTrudgianYang2025.integrable_exp_neg_half_abs_heathBrown

-- PointMeanLemmaThreeTail: heathBrown_fullMoment_tail_pointwise
example
    {C t u : ℝ}
    (hC : ∀ y : ℝ,
      zetaMomentCriticalNorm y ^ (2 : ℕ) ≤ C * (1 + y ^ (2 : ℕ)))
    (ht : 10 ≤ t) (hlog : 4 ≤ Real.log t)
    (hu : Real.log t ^ (2 : ℕ) ≤ |u|) :
    Real.exp (-|u|) * zetaMomentCriticalNorm (t + u) ^ (2 : ℕ) ≤
      (19 * C) * Real.exp (-|u| / 2) :=
  @TaoTrudgianYang2025.heathBrown_fullMoment_tail_pointwise C t u hC ht hlog hu

-- PointMeanLemmaThreeTail: exists_heathBrownFullCriticalMoment_le_truncated
example :
    ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ, 10 ≤ t → 4 ≤ Real.log t →
      heathBrownFullCriticalMoment t ≤
        heathBrownLemmaThreeMoment t (Real.log t ^ (2 : ℕ)) + D :=
  @TaoTrudgianYang2025.exists_heathBrownFullCriticalMoment_le_truncated

-- PointMeanLemmaThreeTail: heathBrownLemmaThreeMoment_nonneg
example
    {t L : ℝ} (hL : 0 ≤ L) :
    0 ≤ heathBrownLemmaThreeMoment t L :=
  @TaoTrudgianYang2025.heathBrownLemmaThreeMoment_nonneg t L hL

-- PointMeanLemmaThreeTail: exists_eventually_heathBrownLemmaThree_truncated
example :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop,
      zetaMomentCriticalNorm t ^ (2 : ℕ) ≤
        C * Real.log t *
          (1 + heathBrownLemmaThreeMoment t (Real.log t ^ (2 : ℕ))) :=
  @TaoTrudgianYang2025.exists_eventually_heathBrownLemmaThree_truncated

-- PointMeanLemmaThreeTail: heathBrownLemmaThree_native
example : HeathBrownLemmaThree :=
  @TaoTrudgianYang2025.heathBrownLemmaThree_native

-- PointMeanEquation44: heathBrown_equation44_of_lemmaThree
example
    (hLemmaThree : HeathBrownLemmaThree) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T V center G L : ℝ) (W : Finset ℝ),
        10 ≤ T → 0 < V → 0 ≤ G → 0 ≤ L →
        IsSeparated 1 W →
        (∀ t ∈ W, center - G / 2 ≤ t ∧ t ≤ center + G / 2) →
        10 ≤ center - G / 2 → center + G / 2 ≤ T →
        (∀ t ∈ W, Real.log t ^ (2 : ℕ) ≤ L) →
        G / 2 + L ≤ G →
        (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
        V ^ (2 : ℕ) * (W.card : ℝ) ≤
          C * Real.log T *
            ((W.card : ℝ) + 4 * (∫ u in center - G..center + G, zetaMomentCriticalNorm u ^ (2 : ℕ))) :=
  @TaoTrudgianYang2025.heathBrown_equation44_of_lemmaThree hLemmaThree

-- PointMeanEquation44: heathBrown_equation44_native
example :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T V center G L : ℝ) (W : Finset ℝ),
        10 ≤ T → 0 < V → 0 ≤ G → 0 ≤ L →
        IsSeparated 1 W →
        (∀ t ∈ W, center - G / 2 ≤ t ∧ t ≤ center + G / 2) →
        10 ≤ center - G / 2 → center + G / 2 ≤ T →
        (∀ t ∈ W, Real.log t ^ (2 : ℕ) ≤ L) →
        G / 2 + L ≤ G →
        (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
        V ^ (2 : ℕ) * (W.card : ℝ) ≤
          C * Real.log T *
            ((W.card : ℝ) + 4 * (∫ u in center - G..center + G, zetaMomentCriticalNorm u ^ (2 : ℕ))) :=
  @TaoTrudgianYang2025.heathBrown_equation44_native

-- The source theorem has no hidden analytic parameter and uses the literal zeta integral.
example :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 10 ≤ t →
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ (2 : ℕ) ≤
        C * Real.log t *
          (1 + ∫ u in -(Real.log t ^ (2 : ℕ))..Real.log t ^ (2 : ℕ),
            Real.exp (-|u|) *
              ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I)‖ ^ (2 : ℕ)) := by
  simpa only [HeathBrownLemmaThree, heathBrownLemmaThreeMoment,
    zetaMomentCriticalNorm] using heathBrownLemmaThree_native

example (s : ℂ) : heathBrownSmoothedDivisorTerm s 0 = 0 := by
  simp [heathBrownSmoothedDivisorTerm]

example (t : ℝ) : heathBrownLemmaThreeMoment t 0 = 0 := by
  simp [heathBrownLemmaThreeMoment]

example : heathBrownLemmaThreeDelta (Real.exp 4) = (1 / 4 : ℝ) := by
  simp [heathBrownLemmaThreeDelta]

example : heathBrownLemmaThreeRadius (Real.exp 4) = (16 : ℝ) := by
  norm_num [heathBrownLemmaThreeRadius]

example : 0 < heathBrownLemmaThreeDelta 10 := by
  exact heathBrownLemmaThreeDelta_pos (by norm_num)

example : heathBrownLemmaThreeDelta 10 < (1 / 2 : ℝ) := by
  exact heathBrownLemmaThreeDelta_lt_half (by norm_num)

end PointMeanContourRegression

namespace PointClusterRegression

open Filter MeasureTheory Complex
open scoped BigOperators Interval

-- FiniteOccupancy: sum_nat_occupancy_eq_sum_superlevel
example
    {α : Type*} (S : Finset α) (f : α → ℕ) (M : ℕ)
    (hM : ∀ x ∈ S, f x ≤ M) :
    ∑ x ∈ S, f x =
      ∑ m ∈ Finset.Icc 1 M, (S.filter (fun x => m ≤ f x)).card :=
  @TaoTrudgianYang2025.sum_nat_occupancy_eq_sum_superlevel α S f M hM

-- FiniteOccupancy: sum_pos_nat_inv_sq_le_two
example (M : ℕ) :
    (∑ m ∈ Finset.Icc 1 M, ((m : ℝ)^2)⁻¹) ≤ 2 :=
  @TaoTrudgianYang2025.sum_pos_nat_inv_sq_le_two M

-- FiniteOccupancy: sum_nat_occupancy_le_of_superlevels
example
    {α : Type*} (S : Finset α) (f : α → ℕ) {B : ℝ}
    (hB : 0 ≤ B)
    (hcount : ∀ m : ℕ, 0 < m →
      ((S.filter (fun x => m ≤ f x)).card : ℝ) ≤ B / (m : ℝ)^2) :
    ((∑ x ∈ S, f x) : ℝ) ≤ 2*B :=
  @TaoTrudgianYang2025.sum_nat_occupancy_le_of_superlevels α S f B hB hcount

-- PointClusters: pointCluster_subset
example (H G : ℝ) (W : Finset ℝ) (n : ℕ) :
    pointCluster H G W n ⊆ W :=
  @TaoTrudgianYang2025.pointCluster_subset H G W n

-- PointClusters: mem_pointClusterBins_iff
example {H G : ℝ} {W : Finset ℝ} {n : ℕ} :
    n ∈ pointClusterBins H G W ↔ (pointCluster H G W n).Nonempty :=
  @TaoTrudgianYang2025.mem_pointClusterBins_iff H G W n

-- PointClusters: pointCluster_card_partition
example (H G : ℝ) (W : Finset ℝ) :
    W.card = ∑ n ∈ pointClusterBins H G W, (pointCluster H G W n).card :=
  @TaoTrudgianYang2025.pointCluster_card_partition H G W

-- PointClusters: pointCluster_interval
example {H G : ℝ} {W : Finset ℝ} (n : ℕ)
    (hG : 0 < G) (hlow : ∀ t ∈ W, H ≤ t) :
    ∀ t ∈ pointCluster H G W n,
      pointClusterCenter H G n ≤ t ∧
        t ≤ pointClusterCenter H G n+G/2 :=
  @TaoTrudgianYang2025.pointCluster_interval H G W n hG hlow

-- PointClusters: pointCluster_symmetric_interval
example {H G : ℝ} {W : Finset ℝ} (n : ℕ)
    (hG : 0 < G) (hlow : ∀ t ∈ W, H ≤ t) :
    ∀ t ∈ pointCluster H G W n,
      pointClusterCenter H G n-G/2 ≤ t ∧
        t ≤ pointClusterCenter H G n+G/2 :=
  @TaoTrudgianYang2025.pointCluster_symmetric_interval H G W n hG hlow

-- PointClusters: pointClusterCenter_range
example {H G : ℝ} {W : Finset ℝ} {n : ℕ}
    (hG : 0 < G) (hrange : ∀ t ∈ W, H ≤ t ∧ t ≤ 2*H)
    (hn : n ∈ pointClusterBins H G W) :
    H ≤ pointClusterCenter H G n ∧ pointClusterCenter H G n ≤ 2*H :=
  @TaoTrudgianYang2025.pointClusterCenter_range H G W n hG hrange hn

-- PointClusters: pointClusterCenter_injective
example {H G : ℝ} (hG : 0 < G) :
    Function.Injective (pointClusterCenter H G) :=
  @TaoTrudgianYang2025.pointClusterCenter_injective H G hG

-- PointClusters: pointClusterCenters_card
example {H G : ℝ} (hG : 0 < G) (U : Finset ℕ) :
    (pointClusterCenters H G U).card = U.card :=
  @TaoTrudgianYang2025.pointClusterCenters_card H G hG U

-- PointClusters: pointClusterCenter_gap_of_same_parity
example {H G : ℝ} {k l : ℕ}
    (hG : 0 < G) (hkl : k < l) (hmod : k%2 = l%2) :
    G ≤ pointClusterCenter H G l-pointClusterCenter H G k :=
  @TaoTrudgianYang2025.pointClusterCenter_gap_of_same_parity H G k l hG hkl hmod

-- PointClusters: pointClusterCenters_separated
example {H G : ℝ} (hG : 0 < G)
    (U : Finset ℕ) (e : ℕ) (hmod : ∀ n ∈ U, n%2 = e) :
    IsSeparated G (pointClusterCenters H G U) :=
  @TaoTrudgianYang2025.pointClusterCenters_separated H G hG U e hmod

-- PointClusters: card_eq_sum_parity_cards
example (U : Finset ℕ) :
    U.card = (U.filter (fun n => n%2 = 0)).card +
      (U.filter (fun n => n%2 = 1)).card :=
  @TaoTrudgianYang2025.card_eq_sum_parity_cards U

-- PointClusterEntry: exists_pointCluster_localMean_bound
example :
    ∃ P : ℝ, 0 < P ∧ ∀ (H G V : ℝ) (W : Finset ℝ) (n : ℕ),
      20 ≤ H → 0 < G → G ≤ H → 0 < V →
      2*(Real.log (3*H))^2 ≤ G →
      IsSeparated 1 W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
      (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
      n ∈ pointClusterBins H G W →
      V^2*((pointCluster H G W n).card:ℝ) ≤
        P*Real.log (3*H)*(((pointCluster H G W n).card:ℝ) +
          4*(∫ u in pointClusterCenter H G n-G..pointClusterCenter H G n+G,
            zetaMomentCriticalNorm u^2)) :=
  @TaoTrudgianYang2025.exists_pointCluster_localMean_bound

-- PointClusterEntry: localMean_lower_bound_of_peak_mass
example
    {P L V R I : ℝ} (hP : 0 < P) (hL : 0 < L) (hR : 0 ≤ R)
    (hV : 2*P*L ≤ V^2)
    (hsource : V^2*R ≤ P*L*(R+4*I)) :
    2*R*(V^2/(16*P*L)) ≤ I :=
  @TaoTrudgianYang2025.localMean_lower_bound_of_peak_mass P L V R I hP hL hR hV hsource

-- PointClusterEntry: exists_pointCluster_superlevel_entry
example :
    ∃ P : ℝ, 0 < P ∧
      ∀ (H G V error : ℝ) (W : Finset ℝ) (n m : ℕ),
        20 ≤ H → 0 < G → G ≤ H → 0 < V →
        2*(Real.log (3*H))^2 ≤ G →
        IsSeparated 1 W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
        n ∈ pointClusterBins H G W → 0 < m →
        m ≤ (pointCluster H G W n).card →
        2*P*Real.log (3*H) ≤ V^2 →
        error ≤ V^2/(16*P*Real.log (3*H)) →
        error+(m:ℝ)*(V^2/(16*P*Real.log (3*H))) ≤
          ∫ u in pointClusterCenter H G n-G..pointClusterCenter H G n+G,
            zetaMomentCriticalNorm u^2 :=
  @TaoTrudgianYang2025.exists_pointCluster_superlevel_entry

-- PointClusterCounting: exists_pointCluster_superlevel_count
example
    {δ κ ν : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hν : 0 < ν) :
    ∃ P C D H₀ : ℝ, 0 < P ∧ 0 < C ∧ 0 < D ∧ 40000 ≤ H₀ ∧
      ∀ (H G V : ℝ) (W : Finset ℝ) (m : ℕ),
        H₀ ≤ H → 0 < G → G ≤ H → 0 < V →
        2*(Real.log (3*H))^2 ≤ G →
        (∀ t : ℝ, H ≤ t → t ≤ 2*H →
          t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
        2*P*Real.log (3*H) ≤ V^2 →
        C*G*Real.log (3*H) ≤ V^2/(16*P*Real.log (3*H)) →
        IsSeparated 1 W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) → 0 < m →
        ((pointClusterSuperlevel H G W m).card:ℝ) ≤
          2*D*H^ν*
            (H/(G*((m:ℝ)*(V^2/(16*P*Real.log (3*H))))^2) +
              H^2/((m:ℝ)*(V^2/(16*P*Real.log (3*H))))^6) :=
  @TaoTrudgianYang2025.exists_pointCluster_superlevel_count δ κ ν hδ hκ hν

-- PointClusterCounting: occupancy_inverse_power_budget
example {H G A m : ℝ}
    (hG : 0 < G) (hA : 0 < A) (hm : 1 ≤ m) :
    H/(G*(m*A)^2)+H^2/(m*A)^6 ≤
      (H/(G*A^2)+H^2/A^6)/m^2 :=
  @TaoTrudgianYang2025.occupancy_inverse_power_budget H G A m hG hA hm

-- PointClusterCounting: exists_pointValue_card_le_with_width
example
    {δ κ ν : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hν : 0 < ν) :
    ∃ P C D H₀ : ℝ, 0 < P ∧ 0 < C ∧ 0 < D ∧ 40000 ≤ H₀ ∧
      ∀ (H G V : ℝ) (W : Finset ℝ),
        H₀ ≤ H → 0 < G → G ≤ H → 0 < V →
        2*(Real.log (3*H))^2 ≤ G →
        (∀ t : ℝ, H ≤ t → t ≤ 2*H →
          t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
        2*P*Real.log (3*H) ≤ V^2 →
        C*G*Real.log (3*H) ≤ V^2/(16*P*Real.log (3*H)) →
        IsSeparated 1 W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
        (W.card:ℝ) ≤ D*H^ν*
          (H/(G*(V^2/(16*P*Real.log (3*H)))^2) +
            H^2/(V^2/(16*P*Real.log (3*H)))^6) :=
  @TaoTrudgianYang2025.exists_pointValue_card_le_with_width δ κ ν hδ hκ hν

-- PointValueWidth: eventually_pointValue_log_scales
example {P K q : ℝ}
    (hK : 0 < K) (hq : 0 < q) :
    ∀ᶠ H : ℝ in atTop, 20 ≤ H ∧ 1 ≤ Real.log (3*H) ∧
      2*P ≤ K*Real.log (3*H) ∧ 2*(Real.log (3*H))^2 ≤ H^q :=
  @TaoTrudgianYang2025.eventually_pointValue_log_scales P K q hK hq

-- PointValueWidth: pointValueWidth_error_absorption
example {P C K L V : ℝ}
    (hP : 0 < P) (hK : 0 < K) (hL : 0 < L) (hKsize : 16*P*C ≤ K) :
    C*(V^2/(K*L^2))*L ≤ V^2/(16*P*L) :=
  @TaoTrudgianYang2025.pointValueWidth_error_absorption P C K L V hP hK hL hKsize

-- PointValueWidth: pointValueWidth_count_identity
example {P K L V H : ℝ}
    (hP : 0 < P) (hL : 0 < L) (hV : 0 < V) :
    H/((V^2/(K*L^2))*(V^2/(16*P*L))^2) +
        H^2/(V^2/(16*P*L))^6 =
      K*(16*P)^2*(H*L^4/V^6) + (16*P)^6*(H^2*L^6/V^12) :=
  @TaoTrudgianYang2025.pointValueWidth_count_identity P K L V H hP hL hV

-- PointValueWidth: exists_pointValue_card_le_source_range
example
    {δ κ ν : ℝ} (hδ : 0 < δ) (hδUpper : δ ≤ 1/4)
    (hκ : 0 < κ) (hν : 0 < ν) :
    ∃ K D H₀ : ℝ, 0 < K ∧ 0 < D ∧ 40000 ≤ H₀ ∧
      ∀ (H V : ℝ) (W : Finset ℝ),
        H₀ ≤ H → 0 < V →
        K*(Real.log (3*H))^2*(2*H)^(1/4+κ) ≤ V^2 →
        V^2 ≤ K*(Real.log (3*H))^2*H^(1/2-δ) →
        IsSeparated 1 W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
        (W.card:ℝ) ≤ D*H^ν*
          (H*(Real.log (3*H))^4/V^6 + H^2*(Real.log (3*H))^6/V^12) :=
  @TaoTrudgianYang2025.exists_pointValue_card_le_source_range δ κ ν hδ hδUpper hκ hν

-- PointValueGrowth: eventually_const_height_log_pow_mul_rpow_le_rpow
example
    {C a b : ℝ} (hC : 0 ≤ C) (k : ℕ) (hab : a < b) :
    ∀ᶠ H : ℝ in atTop,
      C*(Real.log (3*H))^k*H^a ≤ H^b :=
  @TaoTrudgianYang2025.eventually_const_height_log_pow_mul_rpow_le_rpow C a b hC k hab

-- PointValueGrowth: pointValue_sixth_power_count_identity
example {D L H η : ℝ}
    (hH : 0 < H) :
    D*H^η*(H*L^4/(H^(1/6+η))^6+H^2*L^6/(H^(1/6+η))^12) =
      D*L^4/H^(5*η)+D*L^6/H^(11*η) :=
  @TaoTrudgianYang2025.pointValue_sixth_power_count_identity D L H η hH

-- PointValueGrowth: eventually_pointValue_sixth_power_count_lt_one
example
    {D η : ℝ} (hD : 0 < D) (hη : 0 < η) :
    ∀ᶠ H : ℝ in atTop,
      D*H^η*(H*(Real.log (3*H))^4/(H^(1/6+η))^6 +
        H^2*(Real.log (3*H))^6/(H^(1/6+η))^12) < 1 :=
  @TaoTrudgianYang2025.eventually_pointValue_sixth_power_count_lt_one D η hD hη

-- PointValueGrowth: eventually_pointValue_sixth_power_source_range
example
    {K η : ℝ} (hK : 0 < K) (hη : 0 < η) (hηUpper : η ≤ 1/48) :
    ∀ᶠ H : ℝ in atTop,
      K*(Real.log (3*H))^2*(2*H)^(1/4+(1/48:ℝ)) ≤
          (H^(1/6+η))^2 ∧
      (H^(1/6+η))^2 ≤
        K*(Real.log (3*H))^2*H^(1/2-(1/48:ℝ)) :=
  @TaoTrudgianYang2025.eventually_pointValue_sixth_power_source_range K η hK hη hηUpper

-- PointValueGrowth: exists_zetaMomentCriticalNorm_lt_sixth_power
example
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H t : ℝ,
      H₀ ≤ H → H ≤ t → t ≤ 2*H →
      zetaMomentCriticalNorm t < H^(1/6+ε) :=
  @TaoTrudgianYang2025.exists_zetaMomentCriticalNorm_lt_sixth_power ε hε

-- Endpoint and multiplicity checks supplement the exact public-type checks.
example (H G : ℝ) :
    (∅ : Finset ℝ).card =
      ∑ n ∈ pointClusterBins H G ∅, (pointCluster H G ∅ n).card :=
  pointCluster_card_partition H G ∅

example : pointClusterCenter 10 2 10 = (20:ℝ) := by
  norm_num [pointClusterCenter]

example : 10 ∈ pointClusterBins 10 2 ({20}:Finset ℝ) := by
  norm_num [pointClusterBins, atkinsonHeightBin]

example : (pointCluster 10 2 ({10, 10+1/2}:Finset ℝ) 0).card = 2 := by
  norm_num [pointCluster, atkinsonHeightFiber, atkinsonHeightBin,
    Finset.filter_insert, Finset.filter_singleton]

example :
    (({0,1,2}:Finset ℕ).filter (fun n => n%2 = 0)).card = 2 ∧
    (({0,1,2}:Finset ℕ).filter (fun n => n%2 = 1)).card = 1 := by
  norm_num [Finset.filter_insert, Finset.filter_singleton]

example :
    (Finset.range 2).sum (fun n : ℕ => n+1) =
      (Finset.Icc 1 2).sum (fun m : ℕ =>
        ((Finset.range 2).filter (fun n => m ≤ n+1)).card) := by
  apply sum_nat_occupancy_eq_sum_superlevel (Finset.range 2) (fun n => n+1) 2
  intro n hn
  have := Finset.mem_range.mp hn
  omega

example : IsSeparated 2 (pointClusterCenters 10 2 ({0,2,10}:Finset ℕ)) := by
  apply pointClusterCenters_separated (by norm_num) _ 0
  intro n hn
  simp only [Finset.mem_insert,Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl <;> norm_num

-- This unfolds to the actual zeta norm, with no analytic hypothesis.
example {ε : ℝ} (hε : 0 < ε) :
    ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H t : ℝ,
      H₀ ≤ H → H ≤ t → t ≤ 2*H →
      ‖riemannZeta (((1/2:ℝ):ℂ)+(t:ℂ)*I)‖ < H^(1/6+ε) := by
  simpa only [zetaMomentCriticalNorm] using
    exists_zetaMomentCriticalNorm_lt_sixth_power hε

end PointClusterRegression

namespace PointValueMomentRegression

open Filter MeasureTheory Set Complex
open scoped BigOperators Interval ENNReal

-- PointValueRanges: eventually_pointValue_source_lower_range
example {K η : ℝ}
    (hK : 0 < K) (hη : 0 < η) :
    ∀ᶠ H : ℝ in atTop,
      K*(Real.log (3*H))^2*(2*H)^(1/4+η) ≤
        (H^(1/8+η))^2 :=
  @TaoTrudgianYang2025.eventually_pointValue_source_lower_range K η hK hη

-- PointValueRanges: pointValue_count_mul_twelfth_identity
example {D H L V η : ℝ}
    (hV : 0 < V) :
    (D*H^η*(H*L^4/V^6+H^2*L^6/V^12))*V^12 =
      D*H^η*(H*L^4*V^6+H^2*L^6) :=
  @TaoTrudgianYang2025.pointValue_count_mul_twelfth_identity D H L V η hV

-- PointValueRanges: pointValue_count_mul_twelfth_le_growth
example {D H L V η : ℝ}
    (hD : 0 ≤ D) (hH : 0 < H)
    (hV : 0 ≤ V) (hGrowth : V ≤ H^(1/6+η)) :
    D*H^η*(H*L^4*V^6+H^2*L^6) ≤
      D*L^4*H^(2+7*η)+D*L^6*H^(2+η) :=
  @TaoTrudgianYang2025.pointValue_count_mul_twelfth_le_growth D H L V η hD hH hV hGrowth

-- PointValueRanges: eventually_pointValue_high_budget
example {D η : ℝ}
    (hD : 0 < D) (hη : 0 < η) :
    ∀ᶠ H : ℝ in atTop,
      D*(Real.log (3*H))^4*H^(2+7*η) +
        D*(Real.log (3*H))^6*H^(2+η) ≤ H^(2+8*η) :=
  @TaoTrudgianYang2025.eventually_pointValue_high_budget D η hD hη

-- PointValueRanges: exists_pointValue_twelfth_weighted_card_le
example
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ (H V : ℝ) (W : Finset ℝ),
      H₀ ≤ H → 0 < V → H^(1/8+ε) ≤ V →
      IsSeparated 1 W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
      (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
      (W.card:ℝ)*V^12 ≤ H^(2+ε) :=
  @TaoTrudgianYang2025.exists_pointValue_twelfth_weighted_card_le ε hε

-- PointValueMeasure: exists_unitSeparated_closedBall_cover_of_card_bound
example
    {S : Set ℝ} {B : ℝ}
    (hcount : ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ S) →
      IsSeparated 1 W → (W.card:ℝ) ≤ B) :
    ∃ W : Finset ℝ, (∀ t ∈ W, t ∈ S) ∧ IsSeparated 1 W ∧
      ∀ t ∈ S, ∃ u ∈ W, dist t u ≤ 1 :=
  @TaoTrudgianYang2025.exists_unitSeparated_closedBall_cover_of_card_bound S B hcount

-- PointValueMeasure: volume_le_two_mul_of_separated_card_bound
example
    {S : Set ℝ} {B : ℝ}
    (hcount : ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ S) →
      IsSeparated 1 W → (W.card:ℝ) ≤ B) :
    volume S ≤ ENNReal.ofReal (2*B) :=
  @TaoTrudgianYang2025.volume_le_two_mul_of_separated_card_bound S B hcount

-- PointValueMeasure: isClosed_pointValueSuperlevel
example (H V : ℝ) :
    IsClosed (pointValueSuperlevel H V) :=
  @TaoTrudgianYang2025.isClosed_pointValueSuperlevel H V

-- PointValueMeasure: measurableSet_pointValueSuperlevel
example (H V : ℝ) :
    MeasurableSet (pointValueSuperlevel H V) :=
  @TaoTrudgianYang2025.measurableSet_pointValueSuperlevel H V

-- PointValueMeasure: exists_volume_pointValueSuperlevel_le
example {ε : ℝ} (hε : 0 < ε) :
    ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H V : ℝ,
      H₀ ≤ H → 0 < V → H^(1/8+ε) ≤ V →
      volume (pointValueSuperlevel H V) ≤ ENNReal.ofReal (2*H^(2+ε)/V^12) :=
  @TaoTrudgianYang2025.exists_volume_pointValueSuperlevel_le ε hε

-- TruncatedLayerCake: continuous_const_div_max
example {A C : ℝ} (hA : 0 < A) :
    Continuous (fun t : ℝ => C / max A t) :=
  @TaoTrudgianYang2025.continuous_const_div_max A C hA

-- TruncatedLayerCake: integral_const_div_max
example {A M C : ℝ}
    (hA : 0 < A) (hAM : A ≤ M) :
    (∫ t in 0..M, C / max A t) = C*(1+Real.log (M/A)) :=
  @TaoTrudgianYang2025.integral_const_div_max A M C hA hAM

-- TruncatedLayerCake: integral_le_log_of_truncated_tail
example
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} {A M C : ℝ}
    (hA : 0 < A) (hAM : A ≤ M)
    (hfi : Integrable f μ) (hfn : 0 ≤ᵐ[μ] f)
    (hfm : f ≤ᵐ[μ] (fun _ => M))
    (htail : ∀ t : ℝ, 0 < t → t ≤ M →
      μ.real {x | t ≤ f x} ≤ C/max A t) :
    (∫ x, f x ∂μ) ≤ C*(1+Real.log (M/A)) :=
  @TaoTrudgianYang2025.integral_le_log_of_truncated_tail α _ μ f A M C hA hAM hfi hfn hfm htail

-- PointValueTailIntegral: pointValueSuperlevel_subset_Icc
example (H V : ℝ) :
    pointValueSuperlevel H V ⊆ Icc H (2*H) :=
  @TaoTrudgianYang2025.pointValueSuperlevel_subset_Icc H V

-- PointValueTailIntegral: integrableOn_zeta_twelfth_pointValueSuperlevel
example (H V : ℝ) :
    IntegrableOn (fun t => zetaMomentCriticalNorm t^12) (pointValueSuperlevel H V) :=
  @TaoTrudgianYang2025.integrableOn_zeta_twelfth_pointValueSuperlevel H V

-- PointValueTailIntegral: pointValue_power_tail_measure_le
example {H V s C : ℝ}
    (hV : 0 < V) (hs : 0 < s) (hC : 0 ≤ C)
    (hcount : ∀ U : ℝ, V ≤ U →
      volume (pointValueSuperlevel H U) ≤ ENNReal.ofReal (C/U^12)) :
    (volume.restrict (pointValueSuperlevel H V)).real
      {t | s ≤ zetaMomentCriticalNorm t^12} ≤ C/max (V^12) s :=
  @TaoTrudgianYang2025.pointValue_power_tail_measure_le H V s C hV hs hC hcount

-- PointValueTailIntegral: zeta_twelfth_high_integral_le_log
example {H V M C : ℝ}
    (hV : 0 < V) (hVM : V^12 ≤ M) (hC : 0 ≤ C)
    (hGrowth : ∀ t ∈ pointValueSuperlevel H V, zetaMomentCriticalNorm t^12 ≤ M)
    (hcount : ∀ U : ℝ, V ≤ U →
      volume (pointValueSuperlevel H U) ≤ ENNReal.ofReal (C/U^12)) :
    (∫ t in pointValueSuperlevel H V, zetaMomentCriticalNorm t^12) ≤
      C*(1+Real.log (M/V^12)) :=
  @TaoTrudgianYang2025.zeta_twelfth_high_integral_le_log H V M C hV hVM hC hGrowth hcount

-- PointValueTailIntegral: exists_zeta_twelfth_power_le_height_cube
example :
    ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H t : ℝ,
      H₀ ≤ H → H ≤ t → t ≤ 2*H →
      zetaMomentCriticalNorm t^12 ≤ H^3 :=
  @TaoTrudgianYang2025.exists_zeta_twelfth_power_le_height_cube

-- PointValueHighMoment: log_height_cube_div_le
example {H A : ℝ} (hH : 1 ≤ H) (hA : 1 ≤ A) :
    Real.log (H^3/A) ≤ 3*Real.log H :=
  @TaoTrudgianYang2025.log_height_cube_div_le H A hH hA

-- PointValueHighMoment: eventually_zeta_high_log_budget
example {η ε : ℝ} (hgap : η < ε) :
    ∀ᶠ H : ℝ in atTop,
      2*H^(2+η)*(1+3*Real.log H) ≤ H^(2+ε) :=
  @TaoTrudgianYang2025.eventually_zeta_high_log_budget η ε hgap

-- PointValueHighMoment: exists_zeta_twelfth_high_integral_le
example {ε : ℝ} (hε : 0 < ε) :
    ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H →
      (∫ t in pointValueSuperlevel H (H^(1/8+ε)),
        zetaMomentCriticalNorm t^12) ≤ H^(2+ε) :=
  @TaoTrudgianYang2025.exists_zeta_twelfth_high_integral_le ε hε

-- PointValueLowMoment: zeta_twelfth_low_integral_le_fourth
example (H V : ℝ) :
    (∫ t in Icc H (2*H) \ pointValueSuperlevel H V, zetaMomentCriticalNorm t^12) ≤
      V^8*(∫ t in Icc H (2*H), zetaMomentCriticalNorm t^4) :=
  @TaoTrudgianYang2025.zeta_twelfth_low_integral_le_fourth H V

-- PointValueLowMoment: zeta_twelfth_integral_le_high_add_fourth
example {H V : ℝ}
    (hH : 0 ≤ H) :
    (∫ t in H..2*H, zetaMomentCriticalNorm t^12) ≤
      (∫ t in pointValueSuperlevel H V, zetaMomentCriticalNorm t^12) +
        V^8*(∫ t in H..2*H, zetaMomentCriticalNorm t^4) :=
  @TaoTrudgianYang2025.zeta_twelfth_integral_le_high_add_fourth H V hH

-- PointValueLowMoment: zeta_twelfth_dyadic_of_fourth
example
    (hFourth : ∀ η : ℝ, 0 < η → ∃ C H₀ : ℝ, 0 ≤ C ∧
      ∀ H : ℝ, H₀ ≤ H → 0 < H →
        (∫ t in H..2*H, zetaMomentCriticalNorm t^4) ≤ C*H^(1+η)) :
    ∀ ε : ℝ, 0 < ε → ∃ D H₀ : ℝ, 0 ≤ D ∧
      ∀ H : ℝ, H₀ ≤ H → 0 < H →
        (∫ t in H..2*H, zetaMomentCriticalNorm t^12) ≤ D*H^(2+ε) :=
  @TaoTrudgianYang2025.zeta_twelfth_dyadic_of_fourth hFourth

-- Boundary and literal-source regressions supplement all public types.
example (H : ℝ) : pointValueSuperlevel H 0 = Icc H (2*H) := by
  ext t
  simp only [pointValueSuperlevel,Set.mem_setOf_eq,Set.mem_Icc]
  have h := show 0 ≤ zetaMomentCriticalNorm t from norm_nonneg _
  tauto

example {H U V : ℝ} (hUV : U ≤ V) :
    pointValueSuperlevel H V ⊆ pointValueSuperlevel H U :=
  fun _ ht => ⟨ht.1,ht.2.1,hUV.trans ht.2.2⟩

example (V : ℝ) : volume (pointValueSuperlevel 0 V) = 0 := by
  apply measure_mono_null (pointValueSuperlevel_subset_Icc 0 V)
  simp

example {A C : ℝ} (hA : 0 < A) :
    (∫ t in 0..A, C/max A t) = C := by
  simpa [div_self hA.ne'] using integral_const_div_max (C := C) hA le_rfl

example (A M : ℝ) :
    (∫ t in 0..M, (0:ℝ)/max A t) = 0 := by
  simp

example {ε : ℝ} (hε : 0 < ε) :
    ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H →
      (∫ t in {t : ℝ | H ≤ t ∧ t ≤ 2*H ∧
          H^(1/8+ε) ≤ ‖riemannZeta (((1/2:ℝ):ℂ)+(t:ℂ)*I)‖},
        ‖riemannZeta (((1/2:ℝ):ℂ)+(t:ℂ)*I)‖^12) ≤ H^(2+ε) := by
  simpa only [pointValueSuperlevel,zetaMomentCriticalNorm] using
    exists_zeta_twelfth_high_integral_le hε

end PointValueMomentRegression

namespace FourthContourRegression

open Filter MeasureTheory Set Complex Topology
open scoped BigOperators Interval ENNReal ComplexConjugate
open RiemannZeta.GuthMaynard

-- ZetaFourthSource: zetaSquareNorm_eq_two_re_fourthRightPiece
example (t : ℝ) :
    zetaMomentCriticalNorm t^2 = 2*(zetaFourthRightPiece t).re :=
  @TaoTrudgianYang2025.zetaSquareNorm_eq_two_re_fourthRightPiece t

-- ZetaFourthSource: zetaFourthRightPiece_neg
example (t : ℝ) :
    zetaFourthRightPiece (-t) = conj (zetaFourthRightPiece t) :=
  @TaoTrudgianYang2025.zetaFourthRightPiece_neg t

-- ZetaFourthSource: zetaFourthRightPiece_re_nonneg
example (t : ℝ) :
    0 ≤ (zetaFourthRightPiece t).re :=
  @TaoTrudgianYang2025.zetaFourthRightPiece_re_nonneg t

-- ZetaFourthSource: zeta_fourth_le_four_mul_rightPiece_sq
example (t : ℝ) :
    zetaMomentCriticalNorm t^4 ≤ 4*‖zetaFourthRightPiece t‖^2 :=
  @TaoTrudgianYang2025.zeta_fourth_le_four_mul_rightPiece_sq t

-- ZetaFourthSource: norm_zetaSquareGammaNormalization
example (t : ℝ) :
    ‖zetaSquareGammaNormalization t‖ =
      ‖Complex.Gammaℝ (afeCriticalPoint (-t))‖^2 :=
  @TaoTrudgianYang2025.norm_zetaSquareGammaNormalization t

-- ZetaFourthSource: norm_gammaSquare_div_zetaSquareGammaNormalization
example (t : ℝ) (w : ℂ) :
    ‖Complex.Gammaℝ (afeCriticalPoint (-t)+w)^2 /
        zetaSquareGammaNormalization t‖ =
      ‖(Complex.Gammaℝ (afeCriticalPoint (-t)+w) /
        Complex.Gammaℝ (afeCriticalPoint (-t)))^2‖ :=
  @TaoTrudgianYang2025.norm_gammaSquare_div_zetaSquareGammaNormalization t w

-- ZetaFourthSource: zeta_fourth_integral_le_four_mul_rightPiece_sq
example
    {a b : ℝ} (hab : a ≤ b)
    (hint : IntervalIntegrable (fun t => ‖zetaFourthRightPiece t‖^2) volume a b) :
    (∫ t in a..b, zetaMomentCriticalNorm t^4) ≤
      4*(∫ t in a..b, ‖zetaFourthRightPiece t‖^2) :=
  @TaoTrudgianYang2025.zeta_fourth_integral_le_four_mul_rightPiece_sq a b hab hint

-- ZetaFourthGaussian: abs_polynomial_mul_exp_le_gaussian
example
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (D : ℝ) (m : ℕ) (u : ℝ) :
    (a+b*|u|)^m * Real.exp (D*|u|) ≤
      Real.exp ((m:ℝ)*a+((m:ℝ)*b+D)^2/4) * Real.exp (u^2) :=
  @TaoTrudgianYang2025.abs_polynomial_mul_exp_le_gaussian a b ha hb D m u

-- ZetaFourthGaussian: zetaGammaShiftError_le_quadratic
example
    {t c : ℝ} (ht : 4 ≤ t) (hc : 0 ≤ c) {w : ℂ} (u : ℝ)
    (hw : ‖w‖ ≤ c+|u|) :
    zetaGammaShiftError t w ≤ 17*c/4+c^2+u^2+17*|u|/4 :=
  @TaoTrudgianYang2025.zetaGammaShiftError_le_quadratic t c ht hc w u hw

-- ZetaFourthGaussian: norm_vertical_shift_le
example {c : ℝ} (hc : 0 ≤ c) (u : ℝ) :
    ‖(c:ℂ)+(u:ℂ)*I‖ ≤ c+|u| :=
  @TaoTrudgianYang2025.norm_vertical_shift_le c hc u

-- ZetaFourthGaussian: vertical_shift_re_le_norm
example {c : ℝ} (hc : 0 ≤ c) (u : ℝ) :
    c ≤ ‖(c:ℂ)+(u:ℂ)*I‖ :=
  @TaoTrudgianYang2025.vertical_shift_re_le_norm c hc u

-- ZetaFourthKernelBasic: zetaFourthKernel_one
example (t u : ℝ) :
    zetaFourthKernel t (1+(u:ℂ)*I) =
      zetaSquareRightKernel (-t) u / zetaSquareGammaNormalization t :=
  @TaoTrudgianYang2025.zetaFourthKernel_one t u

-- ZetaFourthKernelBasic: continuous_zetaFourthKernel_vertical
example (t : ℝ) {c : ℝ} (hc : 0 < c) :
    Continuous (fun u : ℝ => zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I)) :=
  @TaoTrudgianYang2025.continuous_zetaFourthKernel_vertical t c hc

-- ZetaFourthKernelBasic: norm_zetaFourthKernel_vertical
example (t c u : ℝ) :
    ‖zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I)‖ =
      Real.exp (100*c^2-100*u^2) *
        ‖hughesYoungAuxiliaryZero ((c:ℂ)+(u:ℂ)*I)‖ *
        ‖zetaSquarePoleShift t ((c:ℂ)+(u:ℂ)*I)‖ *
        ‖(Complex.Gammaℝ (afeCriticalPoint (-t)+((c:ℂ)+(u:ℂ)*I)) /
          Complex.Gammaℝ (afeCriticalPoint (-t)))^2‖ /
        ‖(c:ℂ)+(u:ℂ)*I‖ :=
  @TaoTrudgianYang2025.norm_zetaFourthKernel_vertical t c u

-- ZetaFourthKernelBasic: zetaFourthRightPiece_eq_divisor_integral
example (t : ℝ) :
    zetaFourthRightPiece t = (1/(2*Real.pi):ℂ) *
      ∫ u : ℝ, zetaFourthKernel t (1+(u:ℂ)*I) *
        LSeries (fun n : ℕ => (n.divisors.card:ℂ))
          (afeCriticalPoint (-t)+(1+(u:ℂ)*I)) :=
  @TaoTrudgianYang2025.zetaFourthRightPiece_eq_divisor_integral t

-- ZetaFourthKernelBasic: norm_gammaReal_shift_sq_le_exp
example {t : ℝ} (ht : 4 ≤ t)
    {w : ℂ} (hwre : 0 ≤ w.re) (hw : ‖w‖ ≤ t/2) :
    ‖(Complex.Gammaℝ (afeCriticalPoint (-t)+w) /
      Complex.Gammaℝ (afeCriticalPoint (-t)))^2‖ ≤
      Real.exp (zetaGammaShiftError t w) *
        Real.exp ((w*zetaGammaLeadingLog t).re) :=
  @TaoTrudgianYang2025.norm_gammaReal_shift_sq_le_exp t ht w hwre hw

-- ZetaFourthKernelNear: exp_zetaGammaLeadingLog_vertical_le
example
    {t c : ℝ} (ht : 0 < t) (hc : 0 ≤ c) (u : ℝ) :
    Real.exp ((((c:ℂ)+(u:ℂ)*I)*zetaGammaLeadingLog t).re) ≤
      t^c * Real.exp (Real.pi*|u|/2) :=
  @TaoTrudgianYang2025.exp_zetaGammaLeadingLog_vertical_le t c ht hc u

-- ZetaFourthKernelNear: exists_norm_zetaFourthKernel_near_le
example {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ t u : ℝ,
      4 ≤ t → 4*c ≤ t → |u| ≤ t/4 →
      ‖zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I)‖ ≤
        K*t^c*Real.exp (-98*u^2) :=
  @TaoTrudgianYang2025.exists_norm_zetaFourthKernel_near_le c hc

-- ZetaFourthKernelFar: norm_zetaSquarePoleShift_le_polynomial
example
    {t c : ℝ} (ht : 0 ≤ t) (hc : 0 ≤ c) (u : ℝ) :
    ‖zetaSquarePoleShift t ((c:ℂ)+(u:ℂ)*I)‖ ≤
      16*(3+c+t+|u|)^4 :=
  @TaoTrudgianYang2025.norm_zetaSquarePoleShift_le_polynomial t c ht hc u

-- ZetaFourthKernelFar: exists_norm_zetaFourthKernel_far_le
example {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ t u : ℝ,
      0 ≤ t → t ≤ 4*|u| →
      ‖zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I)‖ ≤
        K*Real.exp (-99*u^2) :=
  @TaoTrudgianYang2025.exists_norm_zetaFourthKernel_far_le c hc

-- ZetaFourthKernel: exists_norm_zetaFourthKernel_le
example {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ t u : ℝ,
      4 ≤ t → 4*c ≤ t →
      ‖zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I)‖ ≤
        K*t^c*Real.exp (-98*u^2) :=
  @TaoTrudgianYang2025.exists_norm_zetaFourthKernel_le c hc

-- ZetaFourthKernel: integrable_zetaFourthKernel_vertical
example {t c : ℝ}
    (hc : 0 < c) (ht : 4 ≤ t) (hct : 4*c ≤ t) :
    Integrable (fun u : ℝ => zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I)) :=
  @TaoTrudgianYang2025.integrable_zetaFourthKernel_vertical t c hc ht hct

-- ZetaFourthKernel: exists_integral_norm_zetaFourthKernel_le
example {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ,
      4 ≤ t → 4*c ≤ t →
      (∫ u : ℝ, ‖zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I)‖) ≤
        K*t^c*Real.sqrt (Real.pi/98) :=
  @TaoTrudgianYang2025.exists_integral_norm_zetaFourthKernel_le c hc

-- ZetaFourthContourBounds: exists_norm_zetaFourthKernel_strip_le
example
    {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : 0 ≤ t) :
    ∃ K : ℝ, 0 < K ∧ ∀ c ∈ Icc a b, ∀ u : ℝ,
      ‖zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I)‖ ≤ K*Real.exp (-99*u^2) :=
  @TaoTrudgianYang2025.exists_norm_zetaFourthKernel_strip_le a b t ha hab ht

-- ZetaFourthTerm: zetaFourthTerm_zero
example (t : ℝ) (w : ℂ) : zetaFourthTerm t 0 w = 0 :=
  @TaoTrudgianYang2025.zetaFourthTerm_zero t w

-- ZetaFourthTerm: differentiableAt_zetaFourthKernel
example (t : ℝ) {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ (zetaFourthKernel t) w :=
  @TaoTrudgianYang2025.differentiableAt_zetaFourthKernel t w hw

-- ZetaFourthTerm: differentiableAt_zetaFourthTerm
example (t : ℝ) (n : ℕ)
    {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ (zetaFourthTerm t n) w :=
  @TaoTrudgianYang2025.differentiableAt_zetaFourthTerm t n w hw

-- ZetaFourthTerm: norm_fourth_divisorTerm_vertical
example (t c u : ℝ) (n : ℕ) :
    ‖divisorDirichletTerm (afeCriticalPoint (-t)+((c:ℂ)+(u:ℂ)*I)) n‖ =
      (n.divisors.card:ℝ)*(n:ℝ)^(-(1/2+c)) :=
  @TaoTrudgianYang2025.norm_fourth_divisorTerm_vertical t c u n

-- ZetaFourthTerm: norm_zetaFourthTerm_vertical
example (t c u : ℝ) (n : ℕ) :
    ‖zetaFourthTerm t n ((c:ℂ)+(u:ℂ)*I)‖ =
      ((n.divisors.card:ℝ)*(n:ℝ)^(-(1/2+c))) *
        ‖zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I)‖ :=
  @TaoTrudgianYang2025.norm_zetaFourthTerm_vertical t c u n

-- ZetaFourthTerm: norm_fourth_divisorTerm_le_card
example {c : ℝ} (hc : 0 ≤ c) (t u : ℝ) (n : ℕ) :
    ‖divisorDirichletTerm (afeCriticalPoint (-t)+((c:ℂ)+(u:ℂ)*I)) n‖ ≤
      (n.divisors.card:ℝ) :=
  @TaoTrudgianYang2025.norm_fourth_divisorTerm_le_card c hc t u n

-- ZetaFourthTerm: zetaFourthTerm_one
example (t u : ℝ) (n : ℕ) :
    zetaFourthTerm t n (1+(u:ℂ)*I) =
      zetaSquareDivisorTerm (-t) n u / zetaSquareGammaNormalization t :=
  @TaoTrudgianYang2025.zetaFourthTerm_one t u n

-- ZetaFourthTerm: zetaFourthTerm_boundaryRect_zero
example
    (t : ℝ) (n : ℕ) {a b H : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x : ℝ in a..b, zetaFourthTerm t n ((x:ℂ)+(-H:ℂ)*I)) -
      (∫ x : ℝ in a..b, zetaFourthTerm t n ((x:ℂ)+(H:ℂ)*I)) +
      I • (∫ y : ℝ in -H..H, zetaFourthTerm t n ((b:ℂ)+(y:ℂ)*I)) -
      I • (∫ y : ℝ in -H..H, zetaFourthTerm t n ((a:ℂ)+(y:ℂ)*I)) = 0 :=
  @TaoTrudgianYang2025.zetaFourthTerm_boundaryRect_zero t n a b H ha hab

-- ZetaFourthTermBounds: continuous_zetaFourthTerm_vertical
example (t : ℝ) (n : ℕ)
    {c : ℝ} (hc : 0 < c) :
    Continuous (fun u : ℝ => zetaFourthTerm t n ((c:ℂ)+(u:ℂ)*I)) :=
  @TaoTrudgianYang2025.continuous_zetaFourthTerm_vertical t n c hc

-- ZetaFourthTermBounds: exists_norm_zetaFourthTerm_strip_le
example
    {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : 0 ≤ t) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ c ∈ Icc a b, ∀ u : ℝ,
      ‖zetaFourthTerm t n ((c:ℂ)+(u:ℂ)*I)‖ ≤ C*Real.exp (-99*u^2) :=
  @TaoTrudgianYang2025.exists_norm_zetaFourthTerm_strip_le a b t ha hab ht n

-- ZetaFourthTermBounds: integrable_zetaFourthTerm_vertical
example {t c : ℝ}
    (ht : 0 ≤ t) (hc : 0 < c) (n : ℕ) :
    Integrable (fun u : ℝ => zetaFourthTerm t n ((c:ℂ)+(u:ℂ)*I)) :=
  @TaoTrudgianYang2025.integrable_zetaFourthTerm_vertical t c ht hc n

-- ZetaFourthTermBounds: tendsto_zetaFourthTerm_horizontal_of_sq_eq
example
    {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : 0 ≤ t) (n : ℕ)
    (v : ℝ → ℝ) (hv : ∀ H : ℝ, (v H)^2 = H^2) :
    Tendsto (fun H : ℝ =>
      ∫ x : ℝ in a..b, zetaFourthTerm t n ((x:ℂ)+(v H:ℂ)*I)) atTop (𝓝 0) :=
  @TaoTrudgianYang2025.tendsto_zetaFourthTerm_horizontal_of_sq_eq a b t ha hab ht n v hv

-- ZetaFourthContourShift: integral_zetaFourthTerm_vertical_eq_of_le
example
    {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : 0 ≤ t) (n : ℕ) :
    (∫ u : ℝ, zetaFourthTerm t n ((a:ℂ)+(u:ℂ)*I)) =
      ∫ u : ℝ, zetaFourthTerm t n ((b:ℂ)+(u:ℂ)*I) :=
  @TaoTrudgianYang2025.integral_zetaFourthTerm_vertical_eq_of_le a b t ha hab ht n

-- ZetaFourthContourShift: integral_zetaFourthTerm_vertical_eq
example
    {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : 0 ≤ t) (n : ℕ) :
    (∫ u : ℝ, zetaFourthTerm t n ((a:ℂ)+(u:ℂ)*I)) =
      ∫ u : ℝ, zetaFourthTerm t n ((b:ℂ)+(u:ℂ)*I) :=
  @TaoTrudgianYang2025.integral_zetaFourthTerm_vertical_eq a b t ha hb ht n

-- ZetaFourthContourShift: zetaFourthContribution_one
example (t : ℝ) (n : ℕ) :
    zetaFourthContribution t 1 n =
      zetaSquareDivisorContribution (-t) n / zetaSquareGammaNormalization t :=
  @TaoTrudgianYang2025.zetaFourthContribution_one t n

-- ZetaFourthContourShift: zetaFourthContribution_line_eq
example
    {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : 0 ≤ t) (n : ℕ) :
    zetaFourthContribution t a n = zetaFourthContribution t b n :=
  @TaoTrudgianYang2025.zetaFourthContribution_line_eq a b t ha hb ht n

-- ZetaFourthContourShift: hasSum_zetaFourthContribution
example {t c : ℝ} (ht : 0 ≤ t) (hc : 0 < c) :
    HasSum (zetaFourthContribution t c) (zetaFourthRightPiece t) :=
  @TaoTrudgianYang2025.hasSum_zetaFourthContribution t c ht hc

-- ZetaFourthContourShift: zetaFourthRightPiece_eq_tsum
example {t c : ℝ} (ht : 0 ≤ t) (hc : 0 < c) :
    zetaFourthRightPiece t = ∑' n : ℕ, zetaFourthContribution t c n :=
  @TaoTrudgianYang2025.zetaFourthRightPiece_eq_tsum t c ht hc

-- ZetaFourthContributionBounds: integral_norm_zetaFourthTerm_vertical
example (t c : ℝ) (n : ℕ) :
    (∫ u : ℝ, ‖zetaFourthTerm t n ((c:ℂ)+(u:ℂ)*I)‖) =
      ((n.divisors.card:ℝ)*(n:ℝ)^(-(1/2+c))) *
        ∫ u : ℝ, ‖zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I)‖ :=
  @TaoTrudgianYang2025.integral_norm_zetaFourthTerm_vertical t c n

-- ZetaFourthContributionBounds: exists_norm_zetaFourthContribution_le
example {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 4 ≤ t → 4*c ≤ t → ∀ n : ℕ,
      ‖zetaFourthContribution t c n‖ ≤
        K*t^c*((n.divisors.card:ℝ)*(n:ℝ)^(-(1/2+c))) :=
  @TaoTrudgianYang2025.exists_norm_zetaFourthContribution_le c hc

-- ZetaFourthContributionBounds: summable_fourth_divisorWeight
example {c : ℝ} (hc : 3/2 < c) :
    Summable (fun n : ℕ => (n.divisors.card:ℝ)*(n:ℝ)^(-(1/2+c))) :=
  @TaoTrudgianYang2025.summable_fourth_divisorWeight c hc

-- ZetaFourthTruncation: zetaFourthPrefix_eq_integral
example {t c : ℝ} (ht : 0 ≤ t) (hc : 0 < c)
    (S : Finset ℕ) :
    zetaFourthPrefix t c S = (1/(2*Real.pi):ℂ) *
      ∫ u : ℝ, (∑ n ∈ S,
        divisorDirichletTerm (afeCriticalPoint (-t)+((c:ℂ)+(u:ℂ)*I)) n) *
          zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I) :=
  @TaoTrudgianYang2025.zetaFourthPrefix_eq_integral t c ht hc S

-- ZetaFourthTruncation: zetaFourthPrefix_line_eq
example {t a b : ℝ} (ht : 0 ≤ t)
    (ha : 0 < a) (hb : 0 < b) (S : Finset ℕ) :
    zetaFourthPrefix t a S = zetaFourthPrefix t b S :=
  @TaoTrudgianYang2025.zetaFourthPrefix_line_eq t a b ht ha hb S

-- ZetaFourthTruncation: zetaFourthRightPiece_eq_prefix_add_tail
example {t a b : ℝ} (ht : 0 ≤ t)
    (ha : 0 < a) (hb : 0 < b) (S : Finset ℕ) :
    zetaFourthRightPiece t = zetaFourthPrefix t a S + zetaFourthTail t b S :=
  @TaoTrudgianYang2025.zetaFourthRightPiece_eq_prefix_add_tail t a b ht ha hb S

-- ZetaFourthTruncation: summable_norm_zetaFourthTail
example {t c : ℝ} (ht : 0 ≤ t) (hc : 0 < c)
    (S : Finset ℕ) :
    Summable (fun n : {n : ℕ // n ∉ S} => ‖zetaFourthContribution t c n‖) :=
  @TaoTrudgianYang2025.summable_norm_zetaFourthTail t c ht hc S

-- ZetaFourthTruncation: exists_norm_zetaFourthTail_le
example {c : ℝ} (hc : 3/2 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 4 ≤ t → 4*c ≤ t → ∀ S : Finset ℕ,
      ‖zetaFourthTail t c S‖ ≤ K*t^c*
        ∑' n : {n : ℕ // n ∉ S},
          ((n:ℕ).divisors.card:ℝ)*((n:ℕ):ℝ)^(-(1/2+c)) :=
  @TaoTrudgianYang2025.exists_norm_zetaFourthTail_le c hc

-- ZetaFourthTruncation: exists_norm_fourthRightPiece_sub_prefix_le
example {b : ℝ} (hb : 3/2 < b) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 4 ≤ t → 4*b ≤ t →
      ∀ a : ℝ, 0 < a → ∀ S : Finset ℕ,
      ‖zetaFourthRightPiece t - zetaFourthPrefix t a S‖ ≤ K*t^b*
        ∑' n : {n : ℕ // n ∉ S},
          ((n:ℕ).divisors.card:ℝ)*((n:ℕ):ℝ)^(-(1/2+b)) :=
  @TaoTrudgianYang2025.exists_norm_fourthRightPiece_sub_prefix_le b hb

-- ZetaFourthTruncation: zeta_fourth_le_prefix_add_tail
example {t a b : ℝ} (ht : 0 ≤ t)
    (ha : 0 < a) (hb : 0 < b) (S : Finset ℕ) :
    zetaMomentCriticalNorm t^4 ≤
      8*‖zetaFourthPrefix t a S‖^2 + 8*‖zetaFourthTail t b S‖^2 :=
  @TaoTrudgianYang2025.zeta_fourth_le_prefix_add_tail t a b ht ha hb S

-- ZetaFourthTruncation: exists_zeta_fourth_le_prefix_add_weightTail
example {b : ℝ} (hb : 3/2 < b) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 4 ≤ t → 4*b ≤ t →
      ∀ a : ℝ, 0 < a → ∀ S : Finset ℕ,
      zetaMomentCriticalNorm t^4 ≤ 8*‖zetaFourthPrefix t a S‖^2 +
        8*(K*t^b*(∑' n : {n : ℕ // n ∉ S},
          ((n:ℕ).divisors.card:ℝ)*((n:ℕ):ℝ)^(-(1/2+b))))^2 :=
  @TaoTrudgianYang2025.exists_zeta_fourth_le_prefix_add_weightTail b hb

-- Boundary and literal-source consumers supplement every public signature.
example (t c : ℝ) : zetaFourthContribution t c 0 = 0 := by
  simp [zetaFourthContribution,zetaFourthTerm_zero]

example (t c : ℝ) : zetaFourthPrefix t c ∅ = 0 := by
  simp [zetaFourthPrefix]

example {t c : ℝ} (ht : 0 ≤ t) (hc : 0 < c) :
    zetaFourthTail t c ∅ = zetaFourthRightPiece t := by
  have h := zetaFourthRightPiece_eq_prefix_add_tail ht hc hc ∅
  simpa [zetaFourthPrefix] using h.symm

example (t c : ℝ) (n : ℕ) :
    zetaFourthPrefix t c {n} = zetaFourthContribution t c n := by
  simp [zetaFourthPrefix]

example {t : ℝ} (ht : 0 ≤ t) (S : Finset ℕ) :
    zetaFourthRightPiece t = zetaFourthPrefix t (1/100) S + zetaFourthTail t 2 S :=
  zetaFourthRightPiece_eq_prefix_add_tail ht (by norm_num) (by norm_num) S

example (t : ℝ) :
    ‖riemannZeta (((1/2:ℝ):ℂ)+(t:ℂ)*I)‖^4 ≤
      4*‖zetaSquareDivisorIntegral (-t)/zetaSquareGammaNormalization t‖^2 := by
  simpa only [zetaMomentCriticalNorm,zetaFourthRightPiece] using
    zeta_fourth_le_four_mul_rightPiece_sq t

example {t : ℝ} (ht : 0 ≤ t) (S : Finset ℕ) :
    ‖riemannZeta (((1/2:ℝ):ℂ)+(t:ℂ)*I)‖^4 ≤
      8*‖zetaFourthPrefix t (1/100) S‖^2 + 8*‖zetaFourthTail t 2 S‖^2 := by
  simpa only [zetaMomentCriticalNorm] using
    zeta_fourth_le_prefix_add_tail ht (by norm_num : (0:ℝ)<1/100)
      (by norm_num : (0:ℝ)<2) S

end FourthContourRegression

namespace FourthTwelfthMomentRegression

open TaoTrudgianYang2025 RiemannZeta.GuthMaynard Complex MeasureTheory Set
open scoped Interval

-- ZetaFourthTailPower: tsum_nat_rpow_tail_le
example {p : ℝ} (hp : p < -1) {N : ℕ} (hN : 0 < N) :
    (∑' j : ℕ, ((j+N+1:ℕ):ℝ)^p) ≤ (N:ℝ)^(p+1)/(-p-1) :=
  @TaoTrudgianYang2025.tsum_nat_rpow_tail_le p hp N hN

-- ZetaFourthTailPower: fourth_divisorWeight_le_rpow
example (b : ℝ) (n : ℕ) :
    (n.divisors.card:ℝ)*(n:ℝ)^(-(1/2+b)) ≤ (n:ℝ)^(1/2-b) :=
  @TaoTrudgianYang2025.fourth_divisorWeight_le_rpow b n

-- ZetaFourthTailPower: tsum_fourth_divisorWeight_tail_le
example {b : ℝ} (hb : 3/2 < b)
    {N : ℕ} (hN : 0 < N) :
    (∑' n : {n : ℕ // n ∉ Finset.range (N+1)},
      ((n:ℕ).divisors.card:ℝ)*((n:ℕ):ℝ)^(-(1/2+b))) ≤
      (N:ℝ)^(3/2-b)/(b-3/2) :=
  @TaoTrudgianYang2025.tsum_fourth_divisorWeight_tail_le b hb N hN

-- ZetaFourthTailPower: exists_norm_zetaFourthTail_cutoff_le
example {b : ℝ} (hb : 3/2 < b) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 4 ≤ t → 4*b ≤ t →
      ∀ N : ℕ, 0 < N →
      ‖zetaFourthTail t b (Finset.range (N+1))‖ ≤
        K*t^b*(N:ℝ)^(3/2-b) :=
  @TaoTrudgianYang2025.exists_norm_zetaFourthTail_cutoff_le b hb

-- ZetaFourthTailScale: fourth_tail_scale_le
example {δ b H t x : ℝ}
    (hH : 1 ≤ H) (ht : 0 ≤ t) (htH : t ≤ 2*H)
    (hb : 3/2 < b) (hbudget : b+(1+δ)*(3/2-b) ≤ 0)
    (hx : H^(1+δ) ≤ x) :
    t^b*x^(3/2-b) ≤ 2^b :=
  @TaoTrudgianYang2025.fourth_tail_scale_le δ b H t x hH ht htH hb hbudget hx

-- ZetaFourthTailScale: exists_norm_fourthRightPiece_sub_cutoff_le
example {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, 0 < K ∧ ∃ H₀ : ℝ, 4 ≤ H₀ ∧
      ∀ H : ℝ, H₀ ≤ H → ∀ t : ℝ, H ≤ t → t ≤ 2*H →
      ∀ N : ℕ, H^(1+δ) ≤ (N:ℝ) → ∀ a : ℝ, 0 < a →
      ‖zetaFourthRightPiece t-zetaFourthPrefix t a (Finset.range (N+1))‖ ≤ K :=
  @TaoTrudgianYang2025.exists_norm_fourthRightPiece_sub_cutoff_le δ hδ

-- DirichletMeanSquareTranslation: dirichletTime_shift
example (N : ℕ) (a : ℕ → ℂ) (v t : ℝ) :
    dirichletTime N a (t+v) = dirichletTime N (endpointTwist v a) t :=
  @TaoTrudgianYang2025.dirichletTime_shift N a v t

-- DirichletMeanSquareTranslation: integral_norm_sq_dirichletTime_interval_le
example
    (N : ℕ) (a : ℕ → ℂ) {A B : ℝ} (hN : 0 < N) (hAB : A ≤ B) :
    (∫ t : ℝ in A..B, ‖dirichletTime N a t‖^2) ≤
      (B-A+2*(5*Real.pi+1)*(N:ℝ)) *
        ∑ n ∈ Finset.Ioc N (2*N), ‖a n‖^2 :=
  @TaoTrudgianYang2025.integral_norm_sq_dirichletTime_interval_le N a A B hN hAB

-- DirichletMeanSquareTranslation: integral_norm_sq_dirichletTime_reflected_le
example
    (N : ℕ) (a : ℕ → ℂ) (u : ℝ) {H : ℝ} (hN : 0 < N) (hH : 0 ≤ H) :
    (∫ t : ℝ in H..2*H, ‖dirichletTime N a (u-t)‖^2) ≤
      (H+2*(5*Real.pi+1)*(N:ℝ)) *
        ∑ n ∈ Finset.Ioc N (2*N), ‖a n‖^2 :=
  @TaoTrudgianYang2025.integral_norm_sq_dirichletTime_reflected_le N a u H hN hH

-- DirichletPrefixBlocks: continuous_dirichletPrefix
example (N : ℕ) (a : ℕ → ℂ) :
    Continuous (dirichletPrefix N a) :=
  @TaoTrudgianYang2025.continuous_dirichletPrefix N a

-- DirichletPrefixBlocks: dirichletPrefix_one
example (a : ℕ → ℂ) (t : ℝ) :
    dirichletPrefix 1 a t = a 1 :=
  @TaoTrudgianYang2025.dirichletPrefix_one a t

-- DirichletPrefixBlocks: dirichletPrefix_double
example (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    dirichletPrefix (2*N) a t = dirichletPrefix N a t+dirichletTime N a t :=
  @TaoTrudgianYang2025.dirichletPrefix_double N a t

-- DirichletPrefixBlocks: dirichletPrefix_pow_two
example (M : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    dirichletPrefix (2^M) a t =
      a 1+∑ j ∈ Finset.range M, dirichletTime (2^j) a t :=
  @TaoTrudgianYang2025.dirichletPrefix_pow_two M a t

-- DirichletPrefixBlocks: norm_dirichletPrefix_pow_two_sq_le
example (M : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ‖dirichletPrefix (2^M) a t‖^2 ≤
      2*((M:ℝ)+1)*(‖a 1‖^2+∑ j ∈ Finset.range M, ‖dirichletTime (2^j) a t‖^2) :=
  @TaoTrudgianYang2025.norm_dirichletPrefix_pow_two_sq_le M a t

-- DirichletPrefixMeanSquare: integral_norm_sq_dirichletPrefix_le_blocks
example
    (M : ℕ) (a : ℕ → ℂ) {A B : ℝ} (hAB : A ≤ B) :
    (∫ t : ℝ in A..B, ‖dirichletPrefix (2^M) a t‖^2) ≤
      2*((M:ℝ)+1)*((B-A)*‖a 1‖^2+
        ∑ j ∈ Finset.range M, ∫ t : ℝ in A..B, ‖dirichletTime (2^j) a t‖^2) :=
  @TaoTrudgianYang2025.integral_norm_sq_dirichletPrefix_le_blocks M a A B hAB

-- DirichletPrefixMeanSquare: integral_norm_sq_dirichletPrefix_le
example
    (M : ℕ) (a : ℕ → ℂ) {A B L : ℝ} (hAB : A ≤ B)
    (hone : ‖a 1‖^2 ≤ L)
    (hcoeff : ∀ j ∈ Finset.range M,
      (∑ n ∈ Finset.Ioc (2^j) (2*(2^j)), ‖a n‖^2) ≤ L) :
    (∫ t : ℝ in A..B, ‖dirichletPrefix (2^M) a t‖^2) ≤
      2*((M:ℝ)+1)^2*(B-A+2*(5*Real.pi+1)*(2:ℝ)^M)*L :=
  @TaoTrudgianYang2025.integral_norm_sq_dirichletPrefix_le M a A B L hAB hone hcoeff

-- DirichletPrefixMeanSquare: integral_norm_sq_dirichletPrefix_reflected_le
example
    (M : ℕ) (a : ℕ → ℂ) (u : ℝ) {H L : ℝ} (hH : 0 ≤ H)
    (hone : ‖a 1‖^2 ≤ L)
    (hcoeff : ∀ j ∈ Finset.range M,
      (∑ n ∈ Finset.Ioc (2^j) (2*(2^j)), ‖a n‖^2) ≤ L) :
    (∫ t : ℝ in H..2*H, ‖dirichletPrefix (2^M) a (u-t)‖^2) ≤
      2*((M:ℝ)+1)^2*(H+2*(5*Real.pi+1)*(2:ℝ)^M)*L :=
  @TaoTrudgianYang2025.integral_norm_sq_dirichletPrefix_reflected_le M a u H L hH hone hcoeff

-- ZetaFourthCoefficients: zetaFourthCoeff_zero
example (c : ℝ) : zetaFourthCoeff c 0 = 0 :=
  @TaoTrudgianYang2025.zetaFourthCoeff_zero c

-- ZetaFourthCoefficients: zetaFourthCoeff_one
example (c : ℝ) : zetaFourthCoeff c 1 = 1 :=
  @TaoTrudgianYang2025.zetaFourthCoeff_one c

-- ZetaFourthCoefficients: norm_zetaFourthCoeff
example (c : ℝ) (n : ℕ) :
    ‖zetaFourthCoeff c n‖ = (n.divisors.card:ℝ)*(n:ℝ)^(-(1/2+c)) :=
  @TaoTrudgianYang2025.norm_zetaFourthCoeff c n

-- ZetaFourthCoefficients: fourth_divisorTerm_eq_coeff_phase
example (t c u : ℝ) (n : ℕ) :
    divisorDirichletTerm (afeCriticalPoint (-t)+((c:ℂ)+(u:ℂ)*I)) n =
      zetaFourthCoeff c n*Complex.exp (-(I*((u-t):ℂ)*(Real.log n:ℂ))) :=
  @TaoTrudgianYang2025.fourth_divisorTerm_eq_coeff_phase t c u n

-- ZetaFourthCoefficients: sum_fourth_divisorTerm_eq_prefix
example (t c u : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range (N+1),
      divisorDirichletTerm (afeCriticalPoint (-t)+((c:ℂ)+(u:ℂ)*I)) n) =
        dirichletPrefix N (zetaFourthCoeff c) (u-t) :=
  @TaoTrudgianYang2025.sum_fourth_divisorTerm_eq_prefix t c u N

-- ZetaFourthCoefficientMass: exists_norm_sq_zetaFourthCoeff_le
example {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ c : ℝ, 0 ≤ c → ∀ n : ℕ, 0 < n →
      ‖zetaFourthCoeff c n‖^2 ≤ D*(n:ℝ)^(ε-1) :=
  @TaoTrudgianYang2025.exists_norm_sq_zetaFourthCoeff_le ε hε

-- ZetaFourthCoefficientMass: sum_rpow_sub_one_dyadic_le
example {ε : ℝ} (hε : 0 ≤ ε)
    {N : ℕ} (hN : 0 < N) :
    (∑ n ∈ Finset.Ioc N (2*N), (n:ℝ)^(ε-1)) ≤ (2*(N:ℝ))^ε :=
  @TaoTrudgianYang2025.sum_rpow_sub_one_dyadic_le ε hε N hN

-- ZetaFourthCoefficientMass: exists_sum_sq_zetaFourthCoeff_dyadic_le
example {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ c : ℝ, 0 ≤ c → ∀ N : ℕ, 0 < N →
      (∑ n ∈ Finset.Ioc N (2*N), ‖zetaFourthCoeff c n‖^2) ≤
        D*(2*(N:ℝ))^ε :=
  @TaoTrudgianYang2025.exists_sum_sq_zetaFourthCoeff_dyadic_le ε hε

-- ZetaFourthPolynomialMean: exists_integral_sq_fourthPolynomial_le
example {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ c : ℝ, 0 ≤ c → ∀ M : ℕ,
      ∀ H : ℝ, 0 ≤ H → ∀ u : ℝ,
      (∫ t : ℝ in H..2*H,
        ‖dirichletPrefix (2^M) (zetaFourthCoeff c) (u-t)‖^2) ≤
          D*((M:ℝ)+1)^2*(H+2*(5*Real.pi+1)*(2:ℝ)^M)*((2:ℝ)^M)^ε :=
  @TaoTrudgianYang2025.exists_integral_sq_fourthPolynomial_le ε hε

-- ZetaFourthPolynomialMean: exists_integral_sq_fourthDivisorSum_le
example {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ c : ℝ, 0 ≤ c → ∀ M : ℕ,
      ∀ H : ℝ, 0 ≤ H → ∀ u : ℝ,
      (∫ t : ℝ in H..2*H,
        ‖∑ n ∈ Finset.range (2^M+1),
          divisorDirichletTerm (afeCriticalPoint (-t)+((c:ℂ)+(u:ℂ)*I)) n‖^2) ≤
          D*((M:ℝ)+1)^2*(H+2*(5*Real.pi+1)*(2:ℝ)^M)*((2:ℝ)^M)^ε :=
  @TaoTrudgianYang2025.exists_integral_sq_fourthDivisorSum_le ε hε

-- WeightedIntegralSquare: integral_weighted_sq_le
example
    (g f : ℝ → ℝ) (hg : ∀ x, 0 ≤ g x) (hgi : Integrable g)
    (hgf : Integrable (fun x => g x*f x))
    (hgf2 : Integrable (fun x => g x*(f x)^2))
    (hmass : 0 < ∫ x : ℝ, g x) :
    (∫ x : ℝ, g x*f x)^2 ≤ (∫ x : ℝ, g x)*(∫ x : ℝ, g x*(f x)^2) :=
  @TaoTrudgianYang2025.integral_weighted_sq_le g f hg hgi hgf hgf2 hmass

-- DirichletPrefixBounded: norm_dirichletPrefix_le
example (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ‖dirichletPrefix N a t‖ ≤ ∑ n ∈ Finset.Ioc 0 N, ‖a n‖ :=
  @TaoTrudgianYang2025.norm_dirichletPrefix_le N a t

-- DirichletPrefixBounded: continuous_dirichletPrefix_reflected
example (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    Continuous (fun u : ℝ => dirichletPrefix N a (u-t)) :=
  @TaoTrudgianYang2025.continuous_dirichletPrefix_reflected N a t

-- DirichletPrefixBounded: integrable_gaussian_dirichletPrefix_norm_pow
example
    {b : ℝ} (hb : 0 < b) (N : ℕ) (a : ℕ → ℂ) (t : ℝ) (k : ℕ) :
    Integrable (fun u : ℝ => Real.exp (-b*u^2)*‖dirichletPrefix N a (u-t)‖^k) :=
  @TaoTrudgianYang2025.integrable_gaussian_dirichletPrefix_norm_pow b hb N a t k

-- ZetaFourthPrefixGaussian: exists_norm_sq_fourthPrefix_le_gaussian
example {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 4 ≤ t → 4*c ≤ t → ∀ N : ℕ,
      ‖zetaFourthPrefix t c (Finset.range (N+1))‖^2 ≤ K*t^(2*c)*
        ∫ u : ℝ, Real.exp (-98*u^2)*
          ‖dirichletPrefix N (zetaFourthCoeff c) (u-t)‖^2 :=
  @TaoTrudgianYang2025.exists_norm_sq_fourthPrefix_le_gaussian c hc

-- GaussianPrefixMean: integrable_gaussian_dirichletPrefix_prod
example
    {b : ℝ} (hb : 0 < b) (N : ℕ) (a : ℕ → ℂ) (A B : ℝ) :
    Integrable (fun z : ℝ × ℝ =>
      Real.exp (-b*z.2^2)*‖dirichletPrefix N a (z.2-z.1)‖^2)
      ((volume.restrict (uIoc A B)).prod volume) :=
  @TaoTrudgianYang2025.integrable_gaussian_dirichletPrefix_prod b hb N a A B

-- GaussianPrefixMean: intervalIntegrable_gaussianPrefixMean
example
    {b : ℝ} (hb : 0 < b) (N : ℕ) (a : ℕ → ℂ) (A B : ℝ) :
    IntervalIntegrable (fun t : ℝ =>
      ∫ u : ℝ, Real.exp (-b*u^2)*‖dirichletPrefix N a (u-t)‖^2) volume A B :=
  @TaoTrudgianYang2025.intervalIntegrable_gaussianPrefixMean b hb N a A B

-- GaussianPrefixMean: integral_gaussianPrefixMean_swap
example
    {b : ℝ} (hb : 0 < b) (N : ℕ) (a : ℕ → ℂ) (A B : ℝ) :
    (∫ t : ℝ in A..B, ∫ u : ℝ,
      Real.exp (-b*u^2)*‖dirichletPrefix N a (u-t)‖^2) =
        ∫ u : ℝ, Real.exp (-b*u^2)*
          (∫ t : ℝ in A..B, ‖dirichletPrefix N a (u-t)‖^2) :=
  @TaoTrudgianYang2025.integral_gaussianPrefixMean_swap b hb N a A B

-- GaussianPrefixMean: exists_integral_gaussian_fourthPolynomial_le
example {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ c : ℝ, 0 ≤ c → ∀ M : ℕ, ∀ H : ℝ, 0 ≤ H →
      (∫ t : ℝ in H..2*H, ∫ u : ℝ,
        Real.exp (-98*u^2)*‖dirichletPrefix (2^M) (zetaFourthCoeff c) (u-t)‖^2) ≤
          D*((M:ℝ)+1)^2*(H+2*(5*Real.pi+1)*(2:ℝ)^M)*((2:ℝ)^M)^ε :=
  @TaoTrudgianYang2025.exists_integral_gaussian_fourthPolynomial_le ε hε

-- DyadicMomentCutoff: exists_dyadic_cutoff
example {X : ℝ} (hX : 1 ≤ X) :
    ∃ M : ℕ, X ≤ (2:ℝ)^M ∧ (2:ℝ)^M ≤ 2*X :=
  @TaoTrudgianYang2025.exists_dyadic_cutoff X hX

-- DyadicMomentCutoff: exists_dyadic_count_sq_le_rpow
example {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ M : ℕ, ((M:ℝ)+1)^2 ≤ D*((2:ℝ)^M)^ε :=
  @TaoTrudgianYang2025.exists_dyadic_count_sq_le_rpow ε hε

-- ZetaFourthDyadicBudget: fourth_height_power_identity
example {H q : ℝ} (hH : 0 < H) :
    (2*H)^(2*q)*H^(1+q)*(2*H^(1+q))^(2*q) =
      (2:ℝ)^(4*q)*H^(1+5*q+2*q^2) :=
  @TaoTrudgianYang2025.fourth_height_power_identity H q hH

-- ZetaFourthDyadicBudget: exists_fourth_dyadic_budget
example {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    ∃ D : ℝ, 0 < D ∧ ∀ H : ℝ, 1 ≤ H → ∀ M : ℕ,
      (2:ℝ)^M ≤ 2*H^(1+q) →
      (2*H)^(2*q)*((M:ℝ)+1)^2*
        (H+2*(5*Real.pi+1)*(2:ℝ)^M)*((2:ℝ)^M)^q ≤ D*H^(1+7*q) :=
  @TaoTrudgianYang2025.exists_fourth_dyadic_budget q hq hq1

-- ZetaFourthMoment: zeta_fourth_dyadic
example :
    ∀ η : ℝ, 0 < η → ∃ C H₀ : ℝ, 0 ≤ C ∧
      ∀ H : ℝ, H₀ ≤ H → 0 < H →
        (∫ t in H..2*H, zetaMomentCriticalNorm t^4) ≤ C*H^(1+η) :=
  @TaoTrudgianYang2025.zeta_fourth_dyadic

-- ZetaTwelfthMoment: zeta_twelfth_dyadic
example :
    ∀ ε : ℝ, 0 < ε → ∃ D H₀ : ℝ, 0 ≤ D ∧
      ∀ H : ℝ, H₀ ≤ H → 0 < H →
        (∫ t in H..2*H, zetaMomentCriticalNorm t^12) ≤ D*H^(2+ε) :=
  @TaoTrudgianYang2025.zeta_twelfth_dyadic

-- ZetaTwelfthMoment: zetaTwelfth_largeValueBound
example {σ τ : ℝ}
    (hσ : 1/2 ≤ σ) (hτ : 2 ≤ τ) :
    IsZetaLargeValueBound σ τ (2*τ-12*(σ-1/2)) :=
  @TaoTrudgianYang2025.zetaTwelfth_largeValueBound σ τ hσ hτ

-- ZetaTwelfthMoment: zetaTwelfth_short_largeValueBound
example {σ τ : ℝ}
    (hσ : 3/4 ≤ σ) (hτ : 3/2 ≤ τ) :
    IsZetaLargeValueBound σ τ (2*τ-12*(σ-1/2)) :=
  @TaoTrudgianYang2025.zetaTwelfth_short_largeValueBound σ τ hσ hτ

-- ZetaTwelfthMoment: energyClauseOne_short_zeta
example {σ τ : ℝ}
    (hσ : 3/4 ≤ σ) (hτ : 1 ≤ τ) (hτhi : τ ≤ 2) :
    IsZetaLargeValueEnergyBound σ τ (energyClauseOnePublicRate σ*τ) :=
  @TaoTrudgianYang2025.energyClauseOne_short_zeta σ τ hσ hτ hτhi

-- ZetaTwelfthMoment: energyClauseOne
example {σ : ℝ} (hlo : 3/4 ≤ σ) (hhi : σ ≤ 5/6) :
    IsZeroDensityEnergyBound σ (energyClauseOnePublicRate σ/(1-σ)) :=
  @TaoTrudgianYang2025.energyClauseOne σ hlo hhi

-- NewAdditiveEnergy: add_est_i_bound
example {σ : ℝ} (hlo : 3/4 ≤ σ) (hhi : σ ≤ 5/6) :
    IsZeroDensityEnergyBound σ
      (max ((18-19*σ)/(2*(3*σ-1))) (4*(10-9*σ)/(5*(4*σ-1)))/(1-σ)) :=
  @TaoTrudgianYang2025.add_est_i_bound σ hlo hhi

-- NewAdditiveEnergy: add_est_i
example {σ : ℝ} (hlo : 3/4 ≤ σ) (hhi : σ ≤ 5/6) :
    zeroDensityEnergyExponent σ*((1-σ:ℝ):EReal) ≤
      ((max ((18-19*σ)/(2*(3*σ-1))) (4*(10-9*σ)/(5*(4*σ-1))):ℝ):EReal) :=
  @TaoTrudgianYang2025.add_est_i σ hlo hhi

-- NewAdditiveEnergy: add_est_i_zero_energy
example {σ : ℝ} (hlo : 3/4 ≤ σ) (hhi : σ ≤ 5/6) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ T : ℝ, C ≤ T →
        (zeroAdditiveEnergy (σ-δ) T:ℝ) ≤ C*T^
          (max ((18-19*σ)/(2*(3*σ-1))) (4*(10-9*σ)/(5*(4*σ-1)))+ε) :=
  @TaoTrudgianYang2025.add_est_i_zero_energy σ hlo hhi

-- Literal zeta, exact source boundaries, and endpoint normalization.
example :
    ∀ η : ℝ, 0 < η → ∃ C H₀ : ℝ, 0 ≤ C ∧
      ∀ H : ℝ, H₀ ≤ H → 0 < H →
        (∫ t in H..2*H, ‖riemannZeta (((1/2:ℝ):ℂ)+(t:ℂ)*I)‖^4) ≤
          C*H^(1+η) := zeta_fourth_dyadic

example :
    ∀ ε : ℝ, 0 < ε → ∃ C H₀ : ℝ, 0 ≤ C ∧
      ∀ H : ℝ, H₀ ≤ H → 0 < H →
        (∫ t in H..2*H, ‖riemannZeta (((1/2:ℝ):ℂ)+(t:ℂ)*I)‖^12) ≤
          C*H^(2+ε) := zeta_twelfth_dyadic

example (c t : ℝ) : dirichletPrefix (2^0) (zetaFourthCoeff c) t = 1 := by
  simpa only [pow_zero,zetaFourthCoeff_one] using
    dirichletPrefix_one (zetaFourthCoeff c) t

example (a : ℕ → ℂ) (t : ℝ) : dirichletPrefix 0 a t = 0 := by
  simp [dirichletPrefix]

example : ∃ M : ℕ, (1:ℝ) ≤ (2:ℝ)^M ∧ (2:ℝ)^M ≤ 2*1 :=
  exists_dyadic_cutoff (by norm_num)

example (N : ℕ) (a : ℕ → ℂ) (hN : 0 < N) :
    (∫ t : ℝ in (-7)..(-3), ‖dirichletTime N a t‖^2) ≤
      (4+2*(5*Real.pi+1)*(N:ℝ))*∑ n ∈ Finset.Ioc N (2*N), ‖a n‖^2 := by
  convert integral_norm_sq_dirichletTime_interval_le N a
    (A := -7) (B := -3) hN (by norm_num) using 1; norm_num

example : IsZetaLargeValueBound (1/2) 2 4 := by
  convert zetaTwelfth_largeValueBound
    (σ := 1/2) (τ := 2) (by norm_num) (by norm_num) using 1; norm_num

example : IsZetaLargeValueBound (3/4) (3/2) 0 := by
  convert zetaTwelfth_short_largeValueBound
    (σ := 3/4) (τ := 3/2) (by norm_num) (by norm_num) using 1; norm_num

example : IsZeroDensityEnergyBound (3/4) 6 := by
  convert add_est_i_bound (σ := 3/4) (by norm_num) (by norm_num) using 1; norm_num

example : IsZeroDensityEnergyBound (5/6) (36/7) := by
  convert add_est_i_bound (σ := 5/6) (by norm_num) (by norm_num) using 1; norm_num

example : zeroDensityEnergyExponent (3/4)*((1/4:ℝ):EReal) ≤ ((3/2:ℝ):EReal) := by
  convert add_est_i (σ := 3/4) (by norm_num) (by norm_num) using 1 <;> norm_num

example : zeroDensityEnergyExponent (5/6)*((1/6:ℝ):EReal) ≤ ((6/7:ℝ):EReal) := by
  convert add_est_i (σ := 5/6) (by norm_num) (by norm_num) using 1 <;> norm_num

end FourthTwelfthMomentRegression

namespace EnergyClauseTwoRegression

open Complex Filter MeasureTheory Set
open scoped Interval
open TaoTrudgianYang2025 RiemannZeta.GuthMaynard

-- EnergyCardinalityBounds: InLargeValueEnergyRegion.rho_le_of_largeValueBound
example
    {σ τ ρ e s B : ℝ} (hregion : InLargeValueEnergyRegion σ τ ρ e s)
    (hbound : IsLargeValueBound σ τ B) : ρ ≤ B :=
  @TaoTrudgianYang2025.InLargeValueEnergyRegion.rho_le_of_largeValueBound σ τ ρ e s B hregion hbound

-- EnergyCardinalityBounds: InCardinalityEnergyRegion.rho_le_of_largeValueBound
example
    {σ τ ρ e B : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (hbound : IsLargeValueBound σ τ B) : ρ ≤ B :=
  @TaoTrudgianYang2025.InCardinalityEnergyRegion.rho_le_of_largeValueBound σ τ ρ e B h hbound

-- EnergyCardinalityBounds: InCardinalityEnergyRegion.mean_square_cardinality
example
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e) :
    ρ ≤ max (2-2*σ) (1-2*σ+τ) :=
  @TaoTrudgianYang2025.InCardinalityEnergyRegion.mean_square_cardinality σ τ ρ e h

-- EnergyCardinalityBounds: InCardinalityEnergyRegion.mean_square_cardinality_powered
example
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (k : ℕ) (hk : 1 ≤ k) :
    ρ/k ≤ max (2-2*σ) (1-2*σ+τ/k) :=
  @TaoTrudgianYang2025.InCardinalityEnergyRegion.mean_square_cardinality_powered σ τ ρ e h k hk

-- EnergyCardinalityBounds: InCardinalityEnergyRegion.guthMaynard_cardinality
example
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e) :
    ρ ≤ guthMaynardLargeValueExponent σ τ :=
  @TaoTrudgianYang2025.InCardinalityEnergyRegion.guthMaynard_cardinality σ τ ρ e h

-- EnergyCardinalityBounds: InCardinalityEnergyRegion.guthMaynard_cardinality_powered
example
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (k : ℕ) (hk : 1 ≤ k) :
    ρ/k ≤ guthMaynardLargeValueExponent σ (τ/k) :=
  @TaoTrudgianYang2025.InCardinalityEnergyRegion.guthMaynard_cardinality_powered σ τ ρ e h k hk

-- HeathBrownNineBranches: exists_heathBrownNineBranch
example {σ t r e : ℝ}
    (h : e ≤ heathBrownEnergyRHS σ t r e) :
    ∃ i : Fin 9, e ≤ heathBrownNineBranch σ t r 1 i :=
  @TaoTrudgianYang2025.exists_heathBrownNineBranch σ t r e h

-- HeathBrownNineBranches: heathBrownNineBranch_mono_card
example (σ t a : ℝ) (i : Fin 9) :
    Monotone (fun r => heathBrownNineBranch σ t r a i) :=
  @TaoTrudgianYang2025.heathBrownNineBranch_mono_card σ t a i

-- HeathBrownNineBranches: heathBrownNineBranch_rescale
example (σ τ ρ : ℝ) {k l : ℝ}
    (hk : k ≠ 0) (hl : l ≠ 0) (i : Fin 9) :
    (l/k)*heathBrownNineBranch σ (τ/l) (ρ/l) 1 i =
      heathBrownNineBranch σ (τ/k) (ρ/k) (l/k) i :=
  @TaoTrudgianYang2025.heathBrownNineBranch_rescale σ τ ρ k l hk hl i

-- HeathBrownNineBranches: InCardinalityEnergyRegion.heathBrown_nine_branches_powered
example
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (k l : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l) :
    ∃ i : Fin 9, e/k ≤ heathBrownNineBranch σ (τ/k) (ρ/k) ((l:ℝ)/k) i :=
  @TaoTrudgianYang2025.InCardinalityEnergyRegion.heathBrown_nine_branches_powered σ τ ρ e h k l hk hl

-- HeathBrownNineBranches: heathBrown_small_height_two_branches
example {σ r e : ℝ} (hr : r ≤ 1)
    (h : e ≤ max (max (3*r+1-2*σ) (r+4-4*σ))
      (5/2*r+(3-4*σ)/2)) :
    e ≤ max (r+4-4*σ) ((3-4*σ+5*r)/2) :=
  @TaoTrudgianYang2025.heathBrown_small_height_two_branches σ r e hr h

-- HeathBrownNineBranches: InCardinalityEnergyRegion.heathBrown_two_branches_powered
example
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (k : ℕ) (hk : 1 ≤ k) (hτ : τ/k ≤ 3/2) (hr : ρ/k ≤ 1) :
    e/k ≤ max (ρ/k+4-4*σ) ((3-4*σ+5*(ρ/k))/2) :=
  @TaoTrudgianYang2025.InCardinalityEnergyRegion.heathBrown_two_branches_powered σ τ ρ e h k hk hτ hr

-- EnergyClauseTwoCaps: energyClauseTwo_power_cover
example {τ : ℝ} (hlo : 2 ≤ τ) (hhi : τ ≤ 4) :
    ∃ k : ℕ, (k=2 ∨ k=3) ∧ (k:ℝ) ≤ τ ∧ τ ≤ k+1 :=
  @TaoTrudgianYang2025.energyClauseTwo_power_cover τ hlo hhi

-- EnergyClauseTwoCaps: InCardinalityEnergyRegion.energyClauseTwo_cardinality_caps
example
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (hσ : σ ≤ 4/5) (k : ℕ) (hk : k=2 ∨ k=3)
    (htlo : (k:ℝ) ≤ τ) (hthi : τ ≤ k+1) :
    1 ≤ τ/k ∧ τ/k ≤ 3/2 ∧
      ρ/k ≤ 1-2*σ+τ/k ∧
      ρ/k ≤ max (18/5-4*σ) (12/5-4*σ+τ/k) ∧
      ρ/k ≤ 3-3*σ :=
  @TaoTrudgianYang2025.InCardinalityEnergyRegion.energyClauseTwo_cardinality_caps σ τ ρ e h hσ k hk htlo hthi

-- EnergyClauseTwoCertificates: energy_affine_le_mul_of_endpoints
example
    (a b t u v B : ℝ) (hat : a ≤ t) (htb : t ≤ b)
    (ha : u*a+v ≤ B*a) (hb : u*b+v ≤ B*b) :
    u*t+v ≤ B*t :=
  @TaoTrudgianYang2025.energy_affine_le_mul_of_endpoints a b t u v B hat htb ha hb

-- EnergyClauseTwoCertificates: energyClauseTwoRate_pos
example {σ : ℝ} (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4) :
    0 < energyClauseTwoRate σ :=
  @TaoTrudgianYang2025.energyClauseTwoRate_pos σ hlo hhi

-- EnergyClauseTwoCertificates: energyClauseTwo_high_linear_first
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 6/5 ≤ t) (hthi : t ≤ σ+3/5) :
    (1)*t+((12/5-4*σ)+4-4*σ) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_high_linear_first σ t hlo hhi htlo hthi

-- EnergyClauseTwoCertificates: energyClauseTwo_high_linear_second
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (_hhi : σ ≤ 3/4)
    (htlo : 6/5 ≤ t) (hthi : t ≤ σ+3/5) :
    (5/2*(1))*t+((3-4*σ+5*(12/5-4*σ))/2) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_high_linear_second σ t hlo _hhi htlo hthi

-- EnergyClauseTwoCertificates: energyClauseTwo_high_constant_first
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : σ+3/5 ≤ t) (hthi : t ≤ 3/2) :
    (0)*t+((3-3*σ)+4-4*σ) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_high_constant_first σ t hlo hhi htlo hthi

-- EnergyClauseTwoCertificates: energyClauseTwo_high_constant_second
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : σ+3/5 ≤ t) (hthi : t ≤ 3/2) :
    (5/2*(0))*t+((3-4*σ+5*(3-3*σ))/2) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_high_constant_second σ t hlo hhi htlo hthi

-- EnergyClauseTwoCertificates: energyClauseTwo_low_linear_second
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 1 ≤ t) (hthi : t ≤ 13/5-2*σ) :
    (5/2*(1))*t+((3-4*σ+5*(1-2*σ))/2) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_low_linear_second σ t hlo hhi htlo hthi

-- EnergyClauseTwoCertificates: energyClauseTwo_low_constant_second
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 13/5-2*σ ≤ t) (hthi : t ≤ 6/5) :
    (5/2*(0))*t+((3-4*σ+5*(18/5-4*σ))/2) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_low_constant_second σ t hlo hhi htlo hthi

-- EnergyClauseTwoCertificates: energyClauseTwo_secondary_0_low_linear
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 1 ≤ t) (hthi : t ≤ 13/5-2*σ) :
    ((1)*(1)+(0))*t+((4-4*σ)*(2/3)+(1)*(1-2*σ)) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_secondary_0_low_linear σ t hlo hhi htlo hthi

-- EnergyClauseTwoCertificates: energyClauseTwo_secondary_0_low_constant
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 13/5-2*σ ≤ t) (hthi : t ≤ 6/5) :
    ((1)*(0)+(0))*t+((4-4*σ)*(2/3)+(1)*(18/5-4*σ)) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_secondary_0_low_constant σ t hlo hhi htlo hthi

-- EnergyClauseTwoCertificates: energyClauseTwo_secondary_1_low_linear
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 1 ≤ t) (hthi : t ≤ 13/5-2*σ) :
    ((5/2)*(1)+(0))*t+(((3-4*σ)/2)*(2/3)+(5/2)*(1-2*σ)) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_secondary_1_low_linear σ t hlo hhi htlo hthi

-- EnergyClauseTwoCertificates: energyClauseTwo_secondary_1_low_constant
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 13/5-2*σ ≤ t) (hthi : t ≤ 6/5) :
    ((5/2)*(0)+(0))*t+(((3-4*σ)/2)*(2/3)+(5/2)*(18/5-4*σ)) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_secondary_1_low_constant σ t hlo hhi htlo hthi

-- EnergyClauseTwoCertificates: energyClauseTwo_secondary_2_low_linear
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 1 ≤ t) (hthi : t ≤ 13/5-2*σ) :
    ((8/5)*(1)+(2/5))*t+(((12-16*σ)/5)*(2/3)+(8/5)*(1-2*σ)) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_secondary_2_low_linear σ t hlo hhi htlo hthi

-- EnergyClauseTwoCertificates: energyClauseTwo_secondary_2_low_constant
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 13/5-2*σ ≤ t) (hthi : t ≤ 6/5) :
    ((8/5)*(0)+(2/5))*t+(((12-16*σ)/5)*(2/3)+(8/5)*(18/5-4*σ)) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_secondary_2_low_constant σ t hlo hhi htlo hthi

-- EnergyClauseTwoCertificates: energyClauseTwo_secondary_3_low_linear
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 1 ≤ t) (hthi : t ≤ 13/5-2*σ) :
    ((2)*(1)+(0))*t+((3-4*σ)*(2/3)+(2)*(1-2*σ)) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_secondary_3_low_linear σ t hlo hhi htlo hthi

-- EnergyClauseTwoCertificates: energyClauseTwo_secondary_3_low_constant
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 13/5-2*σ ≤ t) (hthi : t ≤ 6/5) :
    ((2)*(0)+(0))*t+((3-4*σ)*(2/3)+(2)*(18/5-4*σ)) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_secondary_3_low_constant σ t hlo hhi htlo hthi

-- EnergyClauseTwoCertificates: energyClauseTwo_secondary_5_low_linear
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 1 ≤ t) (hthi : t ≤ 13/5-2*σ) :
    ((12/5)*(1)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(1-2*σ)) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_secondary_5_low_linear σ t hlo hhi htlo hthi

-- EnergyClauseTwoCertificates: energyClauseTwo_secondary_5_low_constant
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 13/5-2*σ ≤ t) (hthi : t ≤ 6/5) :
    ((12/5)*(0)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(18/5-4*σ)) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_secondary_5_low_constant σ t hlo hhi htlo hthi

-- EnergyClauseTwoCertificates: energyClauseTwo_secondary_6_low_linear
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 1 ≤ t) (hthi : t ≤ 13/5-2*σ) :
    ((5/4)*(1)+(1/2))*t+((3-4*σ)*(2/3)+(5/4)*(1-2*σ)) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_secondary_6_low_linear σ t hlo hhi htlo hthi

-- EnergyClauseTwoCertificates: energyClauseTwo_secondary_6_low_constant
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 13/5-2*σ ≤ t) (hthi : t ≤ 6/5) :
    ((5/4)*(0)+(1/2))*t+((3-4*σ)*(2/3)+(5/4)*(18/5-4*σ)) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_secondary_6_low_constant σ t hlo hhi htlo hthi

-- EnergyClauseTwoCertificates: energyClauseTwo_secondary_8_low_linear_lower
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 29/40)
    (htlo : 1 ≤ t) (hthi : t ≤ 13/5-2*σ) :
    ((9/5)*(1)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(1-2*σ)) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_secondary_8_low_linear_lower σ t hlo hhi htlo hthi

-- EnergyClauseTwoCertificates: energyClauseTwo_secondary_8_low_linear_upper
example {σ t : ℝ}
    (hlo : 29/40 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 1 ≤ t) (hthi : t ≤ 13/5-2*σ) :
    ((9/5)*(1)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(1-2*σ)) ≤ energyClauseTwoSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_secondary_8_low_linear_upper σ t hlo hhi htlo hthi

-- EnergyClauseTwoCertificates: energyClauseTwo_secondary_8_low_constant_lower
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 29/40)
    (htlo : 13/5-2*σ ≤ t) (hthi : t ≤ 6/5) :
    ((9/5)*(0)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(18/5-4*σ)) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_secondary_8_low_constant_lower σ t hlo hhi htlo hthi

-- EnergyClauseTwoCertificates: energyClauseTwo_secondary_8_low_constant_upper
example {σ t : ℝ}
    (hlo : 29/40 ≤ σ) (_hhi : σ ≤ 3/4)
    (htlo : 13/5-2*σ ≤ t) (hthi : t ≤ 6/5) :
    ((9/5)*(0)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(18/5-4*σ)) ≤ energyClauseTwoSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_secondary_8_low_constant_upper σ t hlo _hhi htlo hthi

-- EnergyClauseTwoCertificates: energyClauseTwo_trade_three_left
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 1 ≤ t) (hthi : t ≤ σ/2+3/4) :
    (3)*t+(7/2-7*σ) ≤ energyClauseTwoSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_trade_three_left σ t hlo hhi htlo hthi

-- EnergyClauseTwoCertificates: energyClauseTwo_trade_three_right
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : σ/2+3/4 ≤ t) (hthi : t ≤ 6/5) :
    (1)*t+(5-6*σ) ≤ energyClauseTwoSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_trade_three_right σ t hlo hhi htlo hthi

-- EnergyClauseTwoCertificates: energyClauseTwo_trade_phase_left
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (_hhi : σ ≤ 3/4)
    (htlo : 1 ≤ t) (hthi : t ≤ 1+2*σ/15) :
    (23/8)*t+(25/8-25/4*σ) ≤ energyClauseTwoSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_trade_phase_left σ t hlo _hhi htlo hthi

-- EnergyClauseTwoCertificates: energyClauseTwo_trade_phase_right
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 1+2*σ/15 ≤ t) (hthi : t ≤ 6/5) :
    (1)*t+(5-6*σ) ≤ energyClauseTwoSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_trade_phase_right σ t hlo hhi htlo hthi

-- EnergyClauseTwoGeneral: energyClauseTwo_primary_high
example {σ t r : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 6/5 ≤ t) (hthi : t ≤ 3/2)
    (hr : r ≤ max (18/5-4*σ) (12/5-4*σ+t))
    (hcap : r ≤ 3-3*σ) :
    max (r+4-4*σ) ((3-4*σ+5*r)/2) ≤ energyClauseTwoRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_primary_high σ t r hlo hhi htlo hthi hr hcap

-- EnergyClauseTwoGeneral: energyClauseTwo_primary_low_second
example {σ t r : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 1 ≤ t) (hthi : t ≤ 6/5)
    (hr : r ≤ 1-2*σ+t) (hg : r ≤ 18/5-4*σ) :
    (3-4*σ+5*r)/2 ≤ energyClauseTwoRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_primary_low_second σ t r hlo hhi htlo hthi hr hg

-- EnergyClauseTwoGeneral: energyClauseTwo_secondary_bound
example {σ t r a e : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 1 ≤ t) (hthi : t ≤ 6/5)
    (halo : 1/2 ≤ a) (hahi : a ≤ 2/3)
    (hr : r ≤ 1-2*σ+t) (hg : r ≤ 18/5-4*σ)
    (hprimary : e ≤ 5-6*σ+t) (i : Fin 9)
    (hbranch : e ≤ heathBrownNineBranch σ t r a i) :
    e ≤ energyClauseTwoRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_secondary_bound σ t r a e hlo hhi htlo hthi halo hahi hr hg hprimary i hbranch

-- EnergyClauseTwoGeneral: InCardinalityEnergyRegion.energyClauseTwo_general
example
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4) (htlo : 2 ≤ τ) (hthi : τ ≤ 4) :
    e ≤ energyClauseTwoRate σ*τ :=
  @TaoTrudgianYang2025.InCardinalityEnergyRegion.energyClauseTwo_general σ τ ρ e h hlo hhi htlo hthi

-- EnergyClauseTwoGeneral: energyClauseTwo_general_bound
example {σ τ : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4) (htlo : 2 ≤ τ) (hthi : τ ≤ 4) :
    IsLargeValueEnergyBound σ τ (energyClauseTwoRate σ*τ) :=
  @TaoTrudgianYang2025.energyClauseTwo_general_bound σ τ hlo hhi htlo hthi

-- ZetaSixthLocalization: ZetaLargeValuePattern.cutoff_critical_integrand_sixth_far_bound
example (P : ZetaLargeValuePattern)
    {a b : ℕ} (hactive : P.active = Finset.Icc a b) (hne : P.active.Nonempty)
    {t u : ℝ} (ht : t ∈ Icc P.T (2 * P.T)) (hu : u ∉ zetaMellinSourceWindow P.T t) :
    ‖zetaCutoffCriticalIntegrand a b t u‖ ≤
      (30 * zetaCutoffMellinConstant 6 (1 / 2) * P.N ^ (11 / 2 : ℝ)) * |u| ^ (-5 : ℝ) :=
  @TaoTrudgianYang2025.ZetaLargeValuePattern.cutoff_critical_integrand_sixth_far_bound P a b hactive hne t u ht hu

-- ZetaSixthLocalization: ZetaLargeValuePattern.cutoff_critical_sixth_far_integral
example (P : ZetaLargeValuePattern)
    {a b : ℕ} (hactive : P.active = Finset.Icc a b) (hne : P.active.Nonempty)
    {t : ℝ} (ht : t ∈ Icc P.T (2 * P.T)) :
    ‖∫ u : ℝ in (zetaMellinSourceWindow P.T t)ᶜ, zetaCutoffCriticalIntegrand a b t u‖ ≤
      240 * zetaCutoffMellinConstant 6 (1 / 2) * P.N ^ (11 / 2 : ℝ) / P.T ^ 4 :=
  @TaoTrudgianYang2025.ZetaLargeValuePattern.cutoff_critical_sixth_far_integral P a b hactive hne t ht

-- ZetaSixthPerron: ZetaLargeValuePattern.polynomial_norm_le_sixth_convolution_and_errors
example (P : ZetaLargeValuePattern)
    {a b : ℕ} (hactive : P.active = Finset.Icc a b) (hne : P.active.Nonempty)
    {t : ℝ} (ht : t ∈ Icc P.T (2 * P.T)) :
    ‖∑ n ∈ P.indices, P.coeff n * dirichletPhase n t‖ ≤
      zetaCutoffMellinConstant 1 (1 / 2) * Real.sqrt P.N * zetaMomentConvolution P.T t +
        zetaCutoffMellinConstant 6 1 * P.N ^ 6 / (1 + |t|) ^ 6 +
        240 * zetaCutoffMellinConstant 6 (1 / 2) * P.N ^ (11 / 2 : ℝ) / P.T ^ 4 :=
  @TaoTrudgianYang2025.ZetaLargeValuePattern.polynomial_norm_le_sixth_convolution_and_errors P a b hactive hne t ht

-- ZetaSixthPerron: zetaSixthPerronError_pos
example : 0 < zetaSixthPerronError :=
  @TaoTrudgianYang2025.zetaSixthPerronError_pos

-- ZetaSixthPerron: ZetaLargeValuePattern.sixth_perron_entry
example (P : ZetaLargeValuePattern)
    (hscale : P.N ^ (11 / 8 : ℝ) ≤ P.T) (hvalue : 2 * zetaSixthPerronError ≤ P.V)
    {t : ℝ} (ht : t ∈ P.ordinates) :
    P.V ≤ zetaPerronConstant * Real.sqrt P.N * zetaMomentConvolution P.T t :=
  @TaoTrudgianYang2025.ZetaLargeValuePattern.sixth_perron_entry P hscale hvalue t ht

-- ZetaSixthPerron: exists_zetaSixthPerron_uniform_threshold
example :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ P : ZetaLargeValuePattern, N₀ ≤ P.N →
      ∀ σ τ δ : ℝ, 7 / 10 ≤ σ → 7 / 5 ≤ τ → δ ≤ 1 / 80 →
        P.N ^ (τ - δ) ≤ P.T → P.N ^ (σ - δ) ≤ P.V →
          ∀ t ∈ P.ordinates,
            P.V ≤ zetaPerronConstant * Real.sqrt P.N * zetaMomentConvolution P.T t :=
  @TaoTrudgianYang2025.exists_zetaSixthPerron_uniform_threshold

-- ZetaBelowTwiceSigma: exists_zetaBelowTwiceSigma_empty_uniform_threshold
example {σ τ : ℝ}
    (_hσ : 7 / 10 ≤ σ) (hσhi : σ ≤ 3 / 4) (hτ : 1 ≤ τ) (hτhi : τ < 2 * σ) :
    ∃ C δ : ℝ, 1 ≤ C ∧ 0 < δ ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N ^ (τ - δ) ≤ P.T → P.T ≤ P.N ^ (τ + δ) →
      P.N ^ (σ - δ) ≤ P.V → P.ordinates = ∅ :=
  @TaoTrudgianYang2025.exists_zetaBelowTwiceSigma_empty_uniform_threshold σ τ _hσ hσhi hτ hτhi

-- ZetaBelowTwiceSigma: zetaBelowTwiceSigma_largeValueBound_any
example {σ τ : ℝ}
    (hσ : 7 / 10 ≤ σ) (hσhi : σ ≤ 3 / 4) (hτ : 1 ≤ τ) (hτhi : τ < 2 * σ) (B : ℝ) :
    IsZetaLargeValueBound σ τ B :=
  @TaoTrudgianYang2025.zetaBelowTwiceSigma_largeValueBound_any σ τ hσ hσhi hτ hτhi B

-- ZetaBelowTwiceSigma: zetaBelowTwiceSigma_energyBound_any
example {σ τ : ℝ}
    (hσ : 7 / 10 ≤ σ) (hσhi : σ ≤ 3 / 4) (hτ : 1 ≤ τ) (hτhi : τ < 2 * σ) (B : ℝ) :
    IsZetaLargeValueEnergyBound σ τ B :=
  @TaoTrudgianYang2025.zetaBelowTwiceSigma_energyBound_any σ τ hσ hσhi hτ hτhi B

-- ZetaTwelfthLowerShort: zetaTwelfth_lower_short_largeValueBound
example {σ τ : ℝ}
    (hσ : 7/10 ≤ σ) (hτ : 7/5 ≤ τ) :
    IsZetaLargeValueBound σ τ (2*τ-12*(σ-1/2)) :=
  @TaoTrudgianYang2025.zetaTwelfth_lower_short_largeValueBound σ τ hσ hτ

-- EnergyClauseTwoZetaCertificates: energyClauseTwo_zeta_linear_0
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 2*σ ≤ t) (hthi : t ≤ 4*σ-1) :
    ((1)*(2)+(0))*t+((4-4*σ)+(1)*(6-12*σ)) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_zeta_linear_0 σ t hlo hhi htlo hthi

-- EnergyClauseTwoZetaCertificates: energyClauseTwo_zeta_linear_1
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 2*σ ≤ t) (hthi : t ≤ 4*σ-1) :
    ((5/2)*(2)+(0))*t+(((3-4*σ)/2)+(5/2)*(6-12*σ)) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_zeta_linear_1 σ t hlo hhi htlo hthi

-- EnergyClauseTwoZetaCertificates: energyClauseTwo_zeta_linear_2
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 2*σ ≤ t) (hthi : t ≤ 4*σ-1) :
    ((8/5)*(2)+(2/5))*t+(((12-16*σ)/5)+(8/5)*(6-12*σ)) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_zeta_linear_2 σ t hlo hhi htlo hthi

-- EnergyClauseTwoZetaCertificates: energyClauseTwo_zeta_linear_3
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 2*σ ≤ t) (hthi : t ≤ 4*σ-1) :
    ((2)*(2)+(0))*t+((3-4*σ)+(2)*(6-12*σ)) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_zeta_linear_3 σ t hlo hhi htlo hthi

-- EnergyClauseTwoZetaCertificates: energyClauseTwo_zeta_linear_4
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 2*σ ≤ t) (hthi : t ≤ 4*σ-1) :
    ((3)*(2)+(0))*t+((1-2*σ)+(3)*(6-12*σ)) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_zeta_linear_4 σ t hlo hhi htlo hthi

-- EnergyClauseTwoZetaCertificates: energyClauseTwo_zeta_linear_5
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 2*σ ≤ t) (hthi : t ≤ 4*σ-1) :
    ((12/5)*(2)+(2/5))*t+(((8-16*σ)/5)+(12/5)*(6-12*σ)) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_zeta_linear_5 σ t hlo hhi htlo hthi

-- EnergyClauseTwoZetaCertificates: energyClauseTwo_zeta_linear_6
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 2*σ ≤ t) (hthi : t ≤ 4*σ-1) :
    ((5/4)*(2)+(1/2))*t+((3-4*σ)+(5/4)*(6-12*σ)) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_zeta_linear_6 σ t hlo hhi htlo hthi

-- EnergyClauseTwoZetaCertificates: energyClauseTwo_zeta_linear_7
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 2*σ ≤ t) (hthi : t ≤ 4*σ-1) :
    ((21/8)*(2)+(1/4))*t+((1-2*σ)+(21/8)*(6-12*σ)) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_zeta_linear_7 σ t hlo hhi htlo hthi

-- EnergyClauseTwoZetaCertificates: energyClauseTwo_zeta_linear_8
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 2*σ ≤ t) (hthi : t ≤ 4*σ-1) :
    ((9/5)*(2)+(4/5))*t+(((8-16*σ)/5)+(9/5)*(6-12*σ)) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_zeta_linear_8 σ t hlo hhi htlo hthi

-- EnergyClauseTwoZetaCertificates: energyClauseTwo_zeta_linear_branch
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 2*σ ≤ t) (hthi : t ≤ 4*σ-1) (i : Fin 9) :
    heathBrownNineBranch σ t ((2)*t+(6-12*σ)) 1 i ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_zeta_linear_branch σ t hlo hhi htlo hthi i

-- EnergyClauseTwoZetaCertificates: energyClauseTwo_zeta_constant_0
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 4*σ-1 ≤ t) (hthi : t ≤ 2) :
    ((1)*(0)+(0))*t+((4-4*σ)+(1)*(4-4*σ)) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_zeta_constant_0 σ t hlo hhi htlo hthi

-- EnergyClauseTwoZetaCertificates: energyClauseTwo_zeta_constant_1
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 4*σ-1 ≤ t) (hthi : t ≤ 2) :
    ((5/2)*(0)+(0))*t+(((3-4*σ)/2)+(5/2)*(4-4*σ)) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_zeta_constant_1 σ t hlo hhi htlo hthi

-- EnergyClauseTwoZetaCertificates: energyClauseTwo_zeta_constant_2
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 4*σ-1 ≤ t) (hthi : t ≤ 2) :
    ((8/5)*(0)+(2/5))*t+(((12-16*σ)/5)+(8/5)*(4-4*σ)) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_zeta_constant_2 σ t hlo hhi htlo hthi

-- EnergyClauseTwoZetaCertificates: energyClauseTwo_zeta_constant_3
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 4*σ-1 ≤ t) (hthi : t ≤ 2) :
    ((2)*(0)+(0))*t+((3-4*σ)+(2)*(4-4*σ)) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_zeta_constant_3 σ t hlo hhi htlo hthi

-- EnergyClauseTwoZetaCertificates: energyClauseTwo_zeta_constant_4
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 4*σ-1 ≤ t) (hthi : t ≤ 2) :
    ((3)*(0)+(0))*t+((1-2*σ)+(3)*(4-4*σ)) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_zeta_constant_4 σ t hlo hhi htlo hthi

-- EnergyClauseTwoZetaCertificates: energyClauseTwo_zeta_constant_5
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 4*σ-1 ≤ t) (hthi : t ≤ 2) :
    ((12/5)*(0)+(2/5))*t+(((8-16*σ)/5)+(12/5)*(4-4*σ)) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_zeta_constant_5 σ t hlo hhi htlo hthi

-- EnergyClauseTwoZetaCertificates: energyClauseTwo_zeta_constant_6
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 4*σ-1 ≤ t) (hthi : t ≤ 2) :
    ((5/4)*(0)+(1/2))*t+((3-4*σ)+(5/4)*(4-4*σ)) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_zeta_constant_6 σ t hlo hhi htlo hthi

-- EnergyClauseTwoZetaCertificates: energyClauseTwo_zeta_constant_7
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 4*σ-1 ≤ t) (hthi : t ≤ 2) :
    ((21/8)*(0)+(1/4))*t+((1-2*σ)+(21/8)*(4-4*σ)) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_zeta_constant_7 σ t hlo hhi htlo hthi

-- EnergyClauseTwoZetaCertificates: energyClauseTwo_zeta_constant_8
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 4*σ-1 ≤ t) (hthi : t ≤ 2) :
    ((9/5)*(0)+(4/5))*t+(((8-16*σ)/5)+(9/5)*(4-4*σ)) ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_zeta_constant_8 σ t hlo hhi htlo hthi

-- EnergyClauseTwoZetaCertificates: energyClauseTwo_zeta_constant_branch
example {σ t : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 4*σ-1 ≤ t) (hthi : t ≤ 2) (i : Fin 9) :
    heathBrownNineBranch σ t ((0)*t+(4-4*σ)) 1 i ≤ energyClauseTwoFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_zeta_constant_branch σ t hlo hhi htlo hthi i

-- EnergyClauseTwoZetaCertificates: energyClauseTwo_zeta_branch
example {σ t r : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4)
    (htlo : 2*σ ≤ t) (hthi : t ≤ 2)
    (hr : r ≤ 2*t+6-12*σ) (hcap : r ≤ 4-4*σ) (i : Fin 9) :
    heathBrownNineBranch σ t r 1 i ≤ energyClauseTwoRate σ*t :=
  @TaoTrudgianYang2025.energyClauseTwo_zeta_branch σ t r hlo hhi htlo hthi hr hcap i

-- EnergyClauseTwo: InZetaLargeValueEnergyRegion.energyClauseTwo
example
    {σ τ ρ e s : ℝ} (h : InZetaLargeValueEnergyRegion σ τ ρ e s)
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4) (htlo : 2*σ ≤ τ) (hthi : τ ≤ 2) :
    e ≤ energyClauseTwoRate σ*τ :=
  @TaoTrudgianYang2025.InZetaLargeValueEnergyRegion.energyClauseTwo σ τ ρ e s h hlo hhi htlo hthi

-- EnergyClauseTwo: energyClauseTwo_short_zeta
example {σ τ : ℝ}
    (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4) (htlo : 1 ≤ τ) (hthi : τ ≤ 2) :
    IsZetaLargeValueEnergyBound σ τ (energyClauseTwoRate σ*τ) :=
  @TaoTrudgianYang2025.energyClauseTwo_short_zeta σ τ hlo hhi htlo hthi

-- EnergyClauseTwo: energyClauseTwo
example {σ : ℝ} (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4) :
    IsZeroDensityEnergyBound σ (energyClauseTwoRate σ/(1-σ)) :=
  @TaoTrudgianYang2025.energyClauseTwo σ hlo hhi

-- NewAdditiveEnergy: add_est_ii_bound
example {σ : ℝ} (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4) :
    IsZeroDensityEnergyBound σ
      (max (5*(18-19*σ)/(2*(5*σ+3))) (2*(45-44*σ)/(2*σ+15))/(1-σ)) :=
  @TaoTrudgianYang2025.add_est_ii_bound σ hlo hhi

-- NewAdditiveEnergy: add_est_ii
example {σ : ℝ} (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4) :
    zeroDensityEnergyExponent σ*((1-σ:ℝ):EReal) ≤
      ((max (5*(18-19*σ)/(2*(5*σ+3))) (2*(45-44*σ)/(2*σ+15)):ℝ):EReal) :=
  @TaoTrudgianYang2025.add_est_ii σ hlo hhi

-- NewAdditiveEnergy: add_est_ii_zero_energy
example {σ : ℝ} (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ T : ℝ, C ≤ T →
        (zeroAdditiveEnergy (σ-δ) T:ℝ) ≤ C*T^
          (max (5*(18-19*σ)/(2*(5*σ+3))) (2*(45-44*σ)/(2*σ+15))+ε) :=
  @TaoTrudgianYang2025.add_est_ii_zero_energy σ hlo hhi

-- Exact physical, cardinality-cap, and printed closed endpoints.
example : IsZetaLargeValueBound (7/10) (7/5) (2/5) := by
  convert zetaTwelfth_lower_short_largeValueBound
    (σ := 7/10) (τ := 7/5) (by norm_num) (by norm_num) using 1 ; norm_num

example : IsZetaLargeValueEnergyBound (7/10) (7/5) (329/130) :=
  by
    convert energyClauseTwo_short_zeta
      (σ := 7/10) (τ := 7/5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) using 1
    norm_num [energyClauseTwoRate,energyClauseTwoFirstRate,energyClauseTwoSecondRate]

example : IsZeroDensityEnergyBound (7/10) (235/39) := by
  convert add_est_ii_bound (σ := 7/10) (by norm_num) (by norm_num) using 1 ; norm_num

example : IsZeroDensityEnergyBound (3/4) (64/11) := by
  convert add_est_ii_bound (σ := 3/4) (by norm_num) (by norm_num) using 1 ; norm_num

example : zeroDensityEnergyExponent (7/10)*((3/10:ℝ):EReal) ≤ ((47/26:ℝ):EReal) := by
  convert add_est_ii (σ := 7/10) (by norm_num) (by norm_num) using 1 <;> norm_num

example : zeroDensityEnergyExponent (3/4)*((1/4:ℝ):EReal) ≤ ((16/11:ℝ):EReal) := by
  convert add_est_ii (σ := 3/4) (by norm_num) (by norm_num) using 1 <;> norm_num

example {r : ℝ} (hr : r ≤ (1:ℝ)) :
    heathBrownNineBranch (3/4) 2 r 1 7 ≤ energyClauseTwoRate (3/4)*2 :=
  energyClauseTwo_zeta_branch (by norm_num) (by norm_num)
    (by norm_num) le_rfl (by linarith) (by linarith) 7

example :
    IsLargeValueEnergyBound (7/10) 3 (energyClauseTwoRate (7/10)*3) :=
  energyClauseTwo_general_bound (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end EnergyClauseTwoRegression

section JutilaSourceEntryRegression

open Complex MeasureTheory
open scoped Interval BigOperators ComplexConjugate

-- JutilaGram: finite_sampling_gram
example {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (W : Finset κ) (a : ι → ℂ) (y : κ → ι → ℂ)
    {V : ℝ} (hV : 0 ≤ V)
    (hlarge : ∀ t ∈ W, V ≤ ‖∑ n ∈ s, a n * y t n‖) :
    ((W.card : ℝ) * V) ^ 2 ≤
      (∑ n ∈ s, ‖a n‖ ^ 2) *
        ∑ t ∈ W, ∑ u ∈ W, ‖∑ n ∈ s, conj (y t n) * y u n‖ :=
  @TaoTrudgianYang2025.finite_sampling_gram ι κ _ _ s W a y V hV hlarge

-- JutilaGram: jutila_smooth_gram_kernel
example (cutoff : GMSmoothCutoff) (N : ℕ) (t u : ℝ) :
    (∑ n ∈ dyadicInterval N,
      conj ((cutoff ((n : ℝ) / N) : ℂ) * (n : ℂ) ^ ((t : ℂ) * I)) *
        ((cutoff ((n : ℝ) / N) : ℂ) * (n : ℂ) ^ ((u : ℂ) * I))) =
      heathBrownTracePolynomial cutoff N (u - t) :=
  @TaoTrudgianYang2025.jutila_smooth_gram_kernel cutoff N t u

-- JutilaGram: jutila_smooth_duality
example (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) (a : ℕ → ℂ) {V : ℝ} (hV : 0 ≤ V)
    (ha : ∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1)
    (hlarge : ∀ t ∈ W, V ≤ ‖gmSmoothDirichletPoly cutoff N a t‖) :
    ((W.card : ℝ) * V) ^ 2 ≤ (N : ℝ) *
      ∑ t ∈ W, ∑ u ∈ W, ‖heathBrownTracePolynomial cutoff N (u-t)‖ :=
  @TaoTrudgianYang2025.jutila_smooth_duality cutoff N W a V hV ha hlarge

-- JutilaGram: jutilaOffDiagonalMoment_nonneg
example (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) (k : ℕ) : 0 ≤ jutilaOffDiagonalMoment cutoff N W k :=
  @TaoTrudgianYang2025.jutilaOffDiagonalMoment_nonneg cutoff N W k

-- JutilaGram: jutila_off_diagonal_holder
example (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) {k : ℕ} (hk : 0 < k) :
    (∑ t ∈ W, ∑ u ∈ W,
      if t = u then 0 else ‖heathBrownTracePolynomial cutoff N (u-t)‖) ^ (2*k) ≤
      (W.card : ℝ) ^ (4*k-2) * jutilaOffDiagonalMoment cutoff N W k :=
  @TaoTrudgianYang2025.jutila_off_diagonal_holder cutoff N W k hk

-- JutilaGram: jutila_smooth_duality_off_diagonal
example (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) (a : ℕ → ℂ) {V : ℝ} (hV : 0 ≤ V)
    (ha : ∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1)
    (hlarge : ∀ t ∈ W, V ≤ ‖gmSmoothDirichletPoly cutoff N a t‖) :
    ((W.card : ℝ) * V) ^ 2 ≤ (W.card : ℝ) * N ^ 2 + (N : ℝ) *
      ∑ t ∈ W, ∑ u ∈ W,
        if t = u then 0 else ‖heathBrownTracePolynomial cutoff N (u-t)‖ :=
  @TaoTrudgianYang2025.jutila_smooth_duality_off_diagonal cutoff N W a V hV ha hlarge

-- JutilaGram: jutila_smooth_amplified_gram
example (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) (a : ℕ → ℂ) {V : ℝ} (hV : 0 < V)
    (ha : ∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1)
    (hlarge : ∀ t ∈ W, V ≤ ‖gmSmoothDirichletPoly cutoff N a t‖)
    {k : ℕ} (hk : 0 < k) :
    (W.card : ℝ) * V ^ 2 ≤ 2 * (N : ℝ) ^ 2 ∨
      (W.card : ℝ) ^ 2 * V ^ (4*k) ≤
        (2 * (N : ℝ)) ^ (2*k) * jutilaOffDiagonalMoment cutoff N W k :=
  @TaoTrudgianYang2025.jutila_smooth_amplified_gram cutoff N W a V hV ha hlarge k hk

-- JutilaPatternEntry: LargeValuePattern.jutila_gram_entry
example (P : LargeValuePattern)
    (cutoff : GMSmoothCutoff) (hN : 30 ≤ P.scale) (hV : 1 < P.V) :
    ∃ (W : Finset ℝ) (Q : ℕ) (c : ℕ → ℂ),
      W ⊆ P.reflectedOrdinates ∧ P.ordinates.card ≤ 3 * W.card ∧
      0 < Q ∧ P.N / 2 ≤ (Q : ℝ) ∧ (Q : ℝ) ≤ 2 * P.N ∧
      IsSeparated 1 W ∧ InBaseInterval P.T W ∧
      (∀ n ∈ dyadicInterval Q, ‖c n‖ ≤ 1) ∧
      (∀ t ∈ W, (P.V - 1) / 3 ≤ ‖gmSmoothDirichletPoly cutoff Q c t‖) ∧
      (∀ k : ℕ, 0 < k →
        (W.card : ℝ) * ((P.V - 1) / 3) ^ 2 ≤ 2 * (Q : ℝ) ^ 2 ∨
          (W.card : ℝ) ^ 2 * ((P.V - 1) / 3) ^ (4*k) ≤
            (2 * (Q : ℝ)) ^ (2*k) * jutilaOffDiagonalMoment cutoff Q W k) :=
  @TaoTrudgianYang2025.LargeValuePattern.jutila_gram_entry P cutoff hN hV

-- JutilaPatternEntry: LargeValuePattern.jutila_spaced_gram_entry
example (P : LargeValuePattern)
    (cutoff : GMSmoothCutoff) (hN : 30 ≤ P.scale) (hV : 1 < P.V)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (W : Finset ℝ) (Q : ℕ) (c : ℕ → ℂ),
      W ⊆ P.reflectedOrdinates ∧
      P.ordinates.card ≤ 6 * (2 * Nat.ceil δ + 1) * W.card ∧
      0 < Q ∧ P.N / 2 ≤ (Q : ℝ) ∧ (Q : ℝ) ≤ 2 * P.N ∧
      IsSeparated δ W ∧ InBaseInterval P.T W ∧
      (∀ n ∈ dyadicInterval Q, ‖c n‖ ≤ 1) ∧
      (∀ t ∈ W, (P.V - 1) / 3 ≤ ‖gmSmoothDirichletPoly cutoff Q c t‖) ∧
      (∀ k : ℕ, 0 < k →
        (W.card : ℝ) * ((P.V - 1) / 3) ^ 2 ≤ 2 * (Q : ℝ) ^ 2 ∨
          (W.card : ℝ) ^ 2 * ((P.V - 1) / 3) ^ (4*k) ≤
            (2 * (Q : ℝ)) ^ (2*k) * jutilaOffDiagonalMoment cutoff Q W k) :=
  @TaoTrudgianYang2025.LargeValuePattern.jutila_spaced_gram_entry P cutoff hN hV δ hδ

-- JutilaPoweredMoments: jutila_coefficient_moment_le
example (N : ℕ) (W : Finset ℝ)
    (a : ℕ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (ha : ∀ n ∈ dyadicInterval N, ‖a n‖ ≤ B) :
    (∑ t ∈ W, ∑ u ∈ W, ‖sourceDirichletPoly N a (t-u)‖ ^ 2) ≤
      B ^ 2 * (2 * (N : ℝ)) * heathBrownWeightedMoment N W :=
  @TaoTrudgianYang2025.jutila_coefficient_moment_le N W a B hB ha

-- JutilaPoweredMoments: jutila_powered_coefficients_uniform
example (k : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ r < k,
      ∀ m ∈ dyadicInterval (2 ^ r * N ^ k),
        ‖heathBrownPoweredCoeffs N k m‖ ≤
          C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η :=
  @TaoTrudgianYang2025.jutila_powered_coefficients_uniform k η hη

-- JutilaPoweredMoments: jutila_weighted_power_moment_uniform
example (k : ℕ) (hk : 0 < k)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
      ∀ (N : ℕ) (T : ℝ) (W : Finset ℝ), 0 < N → T₀ ≤ T →
        IsSeparated 1 W → InBaseInterval T W →
        heathBrownWeightedPowerMoment N k W ≤
          C * (((2 ^ k * N ^ k : ℕ) : ℝ) ^ η) ^ 2 * T ^ ε *
            ((W.card : ℝ) ^ 2 + (W.card : ℝ) * (2 ^ k * N ^ k : ℕ) +
              (W.card : ℝ) ^ (5/4 : ℝ) * T ^ (1/2 : ℝ)) :=
  @TaoTrudgianYang2025.jutila_weighted_power_moment_uniform k hk ε η hε hη

-- JutilaReflectedEntry: jutila_reflected_pattern_entry
example (cutoff : GMSmoothCutoff)
    (q : ℕ) (hq : 2 ≤ q) :
    ∃ C K L D : ℝ, 0 < C ∧ 0 < K ∧ 0 < L ∧ 0 < D ∧
      ∀ (P : LargeValuePattern) (δ : ℝ), 30 ≤ P.scale → 1 < P.V → 4 ≤ δ →
        ∃ (W : Finset ℝ) (Q : ℕ),
          W ⊆ P.reflectedOrdinates ∧
          P.ordinates.card ≤ 6 * (2 * Nat.ceil δ + 1) * W.card ∧
          0 < Q ∧ P.N / 2 ≤ (Q : ℝ) ∧ (Q : ℝ) ≤ 2 * P.N ∧
          IsSeparated δ W ∧ InBaseInterval P.T W ∧
          ∀ (M k : ℕ) (H : ℝ), 0 < M → 0 < k → 1 ≤ H → H ≤ δ/2 →
            (W.card : ℝ) * ((P.V-1)/3) ^ 2 ≤ 2 * (Q : ℝ) ^ 2 ∨
              (W.card : ℝ) ^ 2 * ((P.V-1)/3) ^ (4*k) ≤
                (2 * (Q : ℝ)) ^ (2*k) *
                  ∑ t ∈ W, ∑ u ∈ W, if t = u then 0 else
                    jutilaReflectionEnvelope Q M q H C K L D (u-t) ^ (2*k) :=
  @TaoTrudgianYang2025.jutila_reflected_pattern_entry cutoff q hq

-- Diagonal removal is literal, including the power 13 needed by Add-est (iii).
example (cutoff : GMSmoothCutoff) (N : ℕ) (t : ℝ) :
    jutilaOffDiagonalMoment cutoff N {t} 13 = 0 := by
  simp [jutilaOffDiagonalMoment]

example (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ) (a : ℕ → ℂ)
    {V : ℝ} (hV : 0 < V)
    (ha : ∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1)
    (hlarge : ∀ t ∈ W, V ≤ ‖gmSmoothDirichletPoly cutoff N a t‖) :
    (W.card : ℝ) * V^2 ≤ 2*(N : ℝ)^2 ∨
      (W.card : ℝ)^2 * V^52 ≤
        (2*(N : ℝ))^26 * jutilaOffDiagonalMoment cutoff N W 13 := by
  exact jutila_smooth_amplified_gram cutoff N W a hV ha hlarge (k := 13) (by norm_num)

-- The full reflected envelope retains all three error terms.
example (Q M q : ℕ) (H C K L D t : ℝ) :
    jutilaReflectionEnvelope Q M q H C K L D t =
      (Q : ℝ)*C/Real.sqrt |t| *
        (∫ u in -H..H, ‖gmReflectionDirichletPoly t M u‖) +
      (Q : ℝ)*K*(M : ℝ)^2*H^(1-(q : ℝ)) +
      (Q : ℝ)*L*(1+|t|)^(q+2)/
        ((Q : ℝ)^(q+2)*(M : ℝ)^q) +
      (Q : ℝ)*D/|t|^q := rfl

end JutilaSourceEntryRegression

section JutilaPrefixMomentRegression

open Complex MeasureTheory
open scoped Interval BigOperators

-- JutilaPolynomialMoments: jutila_source_power_identity
example (N k : ℕ) (a : ℕ → ℂ) (t : ℝ)
    (hN : 0 < N) (hk : 0 < k) :
    wideDirichletPoly (N ^ k) k (finitePoweredLineCoeffs N k a 0) (-t) =
      sourceDirichletPoly N a t ^ k :=
  @TaoTrudgianYang2025.jutila_source_power_identity N k a t hN hk

-- JutilaPolynomialMoments: jutila_source_power_moment_le_blocks
example (N k : ℕ) (W : Finset ℝ)
    (a : ℕ → ℂ) (hN : 0 < N) (hk : 0 < k) :
    (∑ t ∈ W, ∑ u ∈ W, ‖sourceDirichletPoly N a (t-u)‖ ^ (2*k)) ≤
      (k : ℝ) * ∑ r ∈ Finset.range k, ∑ t ∈ W, ∑ u ∈ W,
        ‖sourceDirichletPoly (2 ^ r * N ^ k)
          (finitePoweredLineCoeffs N k a 0) (t-u)‖ ^ 2 :=
  @TaoTrudgianYang2025.jutila_source_power_moment_le_blocks N k W a hN hk

-- JutilaPolynomialMoments: jutila_source_power_moment_uniform
example (k : ℕ) (hk : 0 < k)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
      ∀ (N : ℕ) (T : ℝ) (W : Finset ℝ) (a : ℕ → ℂ),
        0 < N → T₀ ≤ T → IsSeparated 1 W → InBaseInterval T W →
        (∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1) →
        (∑ t ∈ W, ∑ u ∈ W, ‖sourceDirichletPoly N a (t-u)‖ ^ (2*k)) ≤
          C * (2 ^ k * N ^ k : ℕ) *
            (((2 ^ k * N ^ k : ℕ) : ℝ) ^ η) ^ 2 * T ^ ε *
            ((W.card : ℝ) ^ 2 + (W.card : ℝ) * (2 ^ k * N ^ k : ℕ) +
              (W.card : ℝ) ^ (5/4 : ℝ) * T ^ (1/2 : ℝ)) :=
  @TaoTrudgianYang2025.jutila_source_power_moment_uniform k hk ε η hε hη

-- JutilaPrefixMoments: jutila_norm_one_add_sum_pow_le
example {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) {p : ℕ} (hp : 0 < p) :
    ‖1 + ∑ i ∈ s, a i‖ ^ p ≤
      ((s.card : ℝ) + 1) ^ (p-1) * (1 + ∑ i ∈ s, ‖a i‖ ^ p) :=
  @TaoTrudgianYang2025.jutila_norm_one_add_sum_pow_le ι s a p hp

-- JutilaPrefixMoments: jutila_reflected_prefix_power_le_blocks
example (t u : ℝ) {M k : ℕ}
    (hM : 0 < M) (hk : 0 < k) :
    ‖gmReflectionDirichletPoly t M u‖ ^ (2*k) ≤
      ((Nat.clog 2 M : ℝ) + 1) ^ (2*k-1) *
        (1 + ∑ r ∈ Finset.range (Nat.clog 2 M),
          ‖dirichletPoly (2 ^ r) (heathBrownReflectedPrefixCoeff M u) t‖ ^ (2*k)) :=
  @TaoTrudgianYang2025.jutila_reflected_prefix_power_le_blocks t u M k hM hk

-- JutilaPrefixMoments: jutila_reflected_prefix_moment_le_blocks
example (W : Finset ℝ) (u : ℝ)
    {M k : ℕ} (hM : 0 < M) (hk : 0 < k) :
    (∑ t ∈ W, ∑ v ∈ W, ‖gmReflectionDirichletPoly (t-v) M u‖ ^ (2*k)) ≤
      ((Nat.clog 2 M : ℝ) + 1) ^ (2*k-1) *
        ((W.card : ℝ) ^ 2 + ∑ r ∈ Finset.range (Nat.clog 2 M),
          ∑ t ∈ W, ∑ v ∈ W,
            ‖dirichletPoly (2 ^ r) (heathBrownReflectedPrefixCoeff M u) (t-v)‖ ^ (2*k)) :=
  @TaoTrudgianYang2025.jutila_reflected_prefix_moment_le_blocks W u M k hM hk

-- JutilaPrefixMoments: jutila_reflected_prefix_moment_uniform
example (k : ℕ) (hk : 0 < k)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
      ∀ (M : ℕ) (T : ℝ) (W : Finset ℝ) (u : ℝ),
        0 < M → T₀ ≤ T → IsSeparated 1 W → InBaseInterval T W →
        (∑ t ∈ W, ∑ v ∈ W, ‖gmReflectionDirichletPoly (t-v) M u‖ ^ (2*k)) ≤
          C * ((Nat.clog 2 M : ℝ) + 1) ^ (2*k) * (2 ^ k * M ^ k : ℕ) *
            (((2 ^ k * M ^ k : ℕ) : ℝ) ^ η) ^ 2 * T ^ ε *
            ((W.card : ℝ) ^ 2 + (W.card : ℝ) * (2 ^ k * M ^ k : ℕ) +
              (W.card : ℝ) ^ (5/4 : ℝ) * T ^ (1/2 : ℝ)) :=
  @TaoTrudgianYang2025.jutila_reflected_prefix_moment_uniform k hk ε η hε hη

-- JutilaReflectionIntegrals: jutila_intervalIntegral_pow_le
example (f : ℝ → ℝ) (H : ℝ) {p : ℕ}
    (hH : 0 ≤ H) (hp : 0 < p) (hf : Continuous f) (hf0 : ∀ u, 0 ≤ f u) :
    (∫ u in -H..H, f u) ^ p ≤
      (2*H) ^ (p-1) * ∫ u in -H..H, f u ^ p :=
  @TaoTrudgianYang2025.jutila_intervalIntegral_pow_le f H p hH hp hf hf0

-- JutilaReflectionIntegrals: jutila_reflected_prefix_integral_power_le
example (t : ℝ) (M k : ℕ)
    (H : ℝ) (hk : 0 < k) (hH : 0 ≤ H) :
    (∫ u in -H..H, ‖gmReflectionDirichletPoly t M u‖) ^ (2*k) ≤
      (2*H) ^ (2*k-1) *
        ∫ u in -H..H, ‖gmReflectionDirichletPoly t M u‖ ^ (2*k) :=
  @TaoTrudgianYang2025.jutila_reflected_prefix_integral_power_le t M k H hk hH

-- JutilaReflectionIntegrals: jutila_reflected_bin_integral_moment_uniform
example (k : ℕ) (hk : 0 < k)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
      ∀ (M : ℕ) (T H : ℝ) (W : Finset ℝ) (j : ℕ),
        0 < M → T₀ ≤ T → 0 ≤ H → IsSeparated 1 W → InBaseInterval T W →
        (∑ p ∈ heathBrownDifferenceBin W j,
          (∫ u in -H..H, ‖gmReflectionDirichletPoly (p.1-p.2) M u‖) ^ (2*k)) ≤
          (2*H) ^ (2*k) *
            (C * ((Nat.clog 2 M : ℝ) + 1) ^ (2*k) * (2 ^ k * M ^ k : ℕ) *
              (((2 ^ k * M ^ k : ℕ) : ℝ) ^ η) ^ 2 * T ^ ε *
              ((W.card : ℝ) ^ 2 + (W.card : ℝ) * (2 ^ k * M ^ k : ℕ) +
                (W.card : ℝ) ^ (5/4 : ℝ) * T ^ (1/2 : ℝ))) :=
  @TaoTrudgianYang2025.jutila_reflected_bin_integral_moment_uniform k hk ε η hε hη

-- JutilaTraceBins: jutila_off_diagonal_moment_eq_bins
example
    (cutoff : GMSmoothCutoff) (Q k : ℕ) {T : ℝ} {W : Finset ℝ}
    (hsep : IsSeparated 1 W) (hbase : InBaseInterval T W) :
    jutilaOffDiagonalMoment cutoff Q W k =
      ∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
        ∑ p ∈ heathBrownDifferenceBin W j,
          ‖heathBrownTracePolynomial cutoff Q (p.1-p.2)‖ ^ (2*k) :=
  @TaoTrudgianYang2025.jutila_off_diagonal_moment_eq_bins cutoff Q k T W hsep hbase

-- JutilaTraceBins: jutila_trace_bin_moment_uniform
example (cutoff : GMSmoothCutoff)
    (q k : ℕ) (hq : 2 ≤ q) (hk : 0 < k)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ A C K L D T₀ : ℝ,
      0 < A ∧ 0 < C ∧ 0 < K ∧ 0 < L ∧ 0 < D ∧ 1 ≤ T₀ ∧
      ∀ (Q M j : ℕ) (T H : ℝ) (W : Finset ℝ),
        0 < Q → 0 < M → 2 ≤ j → T₀ ≤ T → 1 ≤ H →
        H ≤ ((2 ^ j : ℕ) : ℝ) / 2 →
        IsSeparated 1 W → InBaseInterval T W →
        (∑ p ∈ heathBrownDifferenceBin W j,
          ‖heathBrownTracePolynomial cutoff Q (p.1-p.2)‖ ^ (2*k)) ≤
          jutilaTraceBinMajorant q k Q M j T H W A C K L D ε η :=
  @TaoTrudgianYang2025.jutila_trace_bin_moment_uniform cutoff q k hq hk ε η hε hη

-- JutilaBinnedPatterns: jutila_spaced_bin_parameters
example {W : Finset ℝ} {δ H : ℝ} {j : ℕ}
    (hδ : 4 ≤ δ) (hHδ : 4*H ≤ δ) (hsep : IsSeparated δ W)
    (hbin : (heathBrownDifferenceBin W j).Nonempty) :
    2 ≤ j ∧ H ≤ ((2 ^ j : ℕ) : ℝ) / 2 :=
  @TaoTrudgianYang2025.jutila_spaced_bin_parameters W δ H j hδ hHδ hsep hbin

-- JutilaBinnedPatterns: jutila_spaced_off_diagonal_moment_uniform
example (cutoff : GMSmoothCutoff)
    (q k : ℕ) (hq : 2 ≤ q) (hk : 0 < k)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ A C K L D T₀ : ℝ,
      0 < A ∧ 0 < C ∧ 0 < K ∧ 0 < L ∧ 0 < D ∧ 1 ≤ T₀ ∧
      ∀ (Q : ℕ) (M : ℕ → ℕ) (T H δ : ℝ) (W : Finset ℝ),
        0 < Q → (∀ j, 0 < M j) → T₀ ≤ T → 1 ≤ H → 4 ≤ δ → 4*H ≤ δ →
        IsSeparated δ W → InBaseInterval T W →
        jutilaOffDiagonalMoment cutoff Q W k ≤
          ∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
            jutilaTraceBinMajorant q k Q (M j) j T H W A C K L D ε η :=
  @TaoTrudgianYang2025.jutila_spaced_off_diagonal_moment_uniform cutoff q k hq hk ε η hε hη

-- JutilaBinnedPatterns: jutila_binned_pattern_bound
example (cutoff : GMSmoothCutoff)
    (q k : ℕ) (hq : 2 ≤ q) (hk : 0 < k)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ A C K L D T₀ : ℝ,
      0 < A ∧ 0 < C ∧ 0 < K ∧ 0 < L ∧ 0 < D ∧ 1 ≤ T₀ ∧
      ∀ (P : LargeValuePattern) (δ : ℝ),
        30 ≤ P.scale → 1 < P.V → T₀ ≤ P.T → 4 ≤ δ →
        ∃ (W : Finset ℝ) (Q : ℕ),
          W ⊆ P.reflectedOrdinates ∧
          P.ordinates.card ≤ 6 * (2 * Nat.ceil δ + 1) * W.card ∧
          0 < Q ∧ P.N / 2 ≤ (Q : ℝ) ∧ (Q : ℝ) ≤ 2 * P.N ∧
          IsSeparated δ W ∧ InBaseInterval P.T W ∧
          ∀ (M : ℕ → ℕ) (H : ℝ), (∀ j, 0 < M j) → 1 ≤ H → 4*H ≤ δ →
            (W.card : ℝ) * ((P.V-1)/3) ^ 2 ≤ 2 * (Q : ℝ) ^ 2 ∨
              (W.card : ℝ) ^ 2 * ((P.V-1)/3) ^ (4*k) ≤
                (2 * (Q : ℝ)) ^ (2*k) *
                  ∑ j ∈ Finset.range (Nat.log 2 (Nat.floor P.T) + 1),
                    jutilaTraceBinMajorant q k Q (M j) j P.T H W A C K L D ε η :=
  @TaoTrudgianYang2025.jutila_binned_pattern_bound cutoff q k hq hk ε η hε hη

-- JutilaHybridPatterns: jutila_near_trace_bin_moment_uniform
example (cutoff : GMSmoothCutoff)
    (q k : ℕ) :
    ∃ E F : ℝ, 0 < E ∧ 0 < F ∧
      ∀ (Q j : ℕ) (W : Finset ℝ), 0 < Q → IsSeparated 1 W →
        2 ^ (j+1) ≤ Q →
        (∑ p ∈ heathBrownDifferenceBin W j,
          ‖heathBrownTracePolynomial cutoff Q (p.1-p.2)‖ ^ (2*k)) ≤
          (2 : ℝ) ^ (2*k-1) * ((heathBrownDifferenceBin W j).card : ℝ) *
            (E ^ (2*k) * (Q : ℝ) ^ k +
              ((Q : ℝ) * F / ((2 ^ j : ℕ) : ℝ) ^ q) ^ (2*k)) :=
  @TaoTrudgianYang2025.jutila_near_trace_bin_moment_uniform cutoff q k

-- JutilaHybridPatterns: jutila_hybrid_pattern_bound
example (cutoff : GMSmoothCutoff)
    (q k : ℕ) (hq : 2 ≤ q) (hk : 0 < k)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ E F A C K L D T₀ : ℝ,
      0 < E ∧ 0 < F ∧ 0 < A ∧ 0 < C ∧ 0 < K ∧ 0 < L ∧ 0 < D ∧ 1 ≤ T₀ ∧
      ∀ (P : LargeValuePattern) (δ : ℝ),
        30 ≤ P.scale → 1 < P.V → T₀ ≤ P.T → 4 ≤ δ →
        ∃ (W : Finset ℝ) (Q : ℕ),
          W ⊆ P.reflectedOrdinates ∧
          P.ordinates.card ≤ 6 * (2 * Nat.ceil δ + 1) * W.card ∧
          0 < Q ∧ P.N / 2 ≤ (Q : ℝ) ∧ (Q : ℝ) ≤ 2 * P.N ∧
          IsSeparated δ W ∧ InBaseInterval P.T W ∧
          ∀ H : ℕ, 0 < H → 4*(H : ℝ) ≤ δ →
            (W.card : ℝ) * ((P.V-1)/3) ^ 2 ≤ 2 * (Q : ℝ) ^ 2 ∨
              (W.card : ℝ) ^ 2 * ((P.V-1)/3) ^ (4*k) ≤
                (2 * (Q : ℝ)) ^ (2*k) *
                  ∑ j ∈ Finset.range (Nat.log 2 (Nat.floor P.T) + 1),
                    jutilaTraceHybridMajorant q k Q H j P.T W E F A C K L D ε η :=
  @TaoTrudgianYang2025.jutila_hybrid_pattern_bound cutoff q k hq hk ε η hε hη

-- The literal n = 1 contribution survives at the Add-est (iii) power.
example (t u : ℝ) :
    ‖gmReflectionDirichletPoly t 1 u‖ ^ (2*13) = 1 := by
  simp [gmReflectionDirichletPoly]

example (W : Finset ℝ) (u : ℝ) :
    (∑ t ∈ W, ∑ v ∈ W, ‖gmReflectionDirichletPoly (t-v) 1 u‖ ^ (2*13)) =
      (W.card : ℝ) ^ 2 := by
  simp [gmReflectionDirichletPoly, pow_two]

-- Zero interval width has zero reflection integral even at the required power.
example (t : ℝ) (M : ℕ) :
    (∫ u in -(0 : ℝ)..0, ‖gmReflectionDirichletPoly t M u‖) ^ (2*13) = 0 := by
  simp

-- The chosen dual length is the ceiling schedule, not a free scale variable.
example (Q H j : ℕ) :
    heathBrownFixedReflectionLength Q H j = max 1 ((2 ^ j * H + Q - 1) / Q) := rfl

-- Both branches of the hybrid schedule retain the actual bin.
example (q k Q H j : ℕ) (T : ℝ) (W : Finset ℝ) (E F A C K L D ε η : ℝ)
    (hj : 2 ^ (j+1) ≤ Q) :
    jutilaTraceHybridMajorant q k Q H j T W E F A C K L D ε η =
      (2 : ℝ) ^ (2*k-1) * ((heathBrownDifferenceBin W j).card : ℝ) *
        (E ^ (2*k) * (Q : ℝ) ^ k +
          ((Q : ℝ) * F / ((2 ^ j : ℕ) : ℝ) ^ q) ^ (2*k)) := by
  simp only [jutilaTraceHybridMajorant, if_pos hj]

example (q k Q H j : ℕ) (T : ℝ) (W : Finset ℝ) (E F A C K L D ε η : ℝ)
    (hj : ¬ 2 ^ (j+1) ≤ Q) :
    jutilaTraceHybridMajorant q k Q H j T W E F A C K L D ε η =
      jutilaTraceBinMajorant q k Q (heathBrownFixedReflectionLength Q H j) j
        T H W A C K L D ε η := by
  simp only [jutilaTraceHybridMajorant, if_neg hj]

end JutilaPrefixMomentRegression


namespace JutilaPhysicalSmoothingRegression

open TaoTrudgianYang2025 RiemannZeta.GuthMaynard
open scoped BigOperators

-- JutilaDualScales: jutila_bin_scale_le_height
example {T : ℝ} {j : ℕ} (hT : 1 ≤ T)
    (hj : j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1)) :
    ((2 ^ j : ℕ) : ℝ) ≤ T :=
  @TaoTrudgianYang2025.jutila_bin_scale_le_height T j hT hj

-- JutilaDualScales: jutila_fixed_length_product_le
example (Q H j : ℕ) (hQ : 0 < Q) (hH : 0 < H)
    (hfar : ¬ 2 ^ (j+1) ≤ Q) :
    (Q : ℝ) * heathBrownFixedReflectionLength Q H j ≤
      ((2 ^ j : ℕ) : ℝ) * ((H : ℝ) + 2) :=
  @TaoTrudgianYang2025.jutila_fixed_length_product_le Q H j hQ hH hfar

-- JutilaDualScales: jutila_fixed_length_le_height_ceiling
example (Q H j : ℕ) {T : ℝ}
    (hQ : 0 < Q) (hH : 0 < H) (hT : 1 ≤ T)
    (hj : j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1)) :
    heathBrownFixedReflectionLength Q H j ≤ Nat.ceil (T * H) + 1 :=
  @TaoTrudgianYang2025.jutila_fixed_length_le_height_ceiling Q H j T hQ hH hT hj

-- JutilaDualScales: jutila_reflection_scale_one
example {Q M S H C : ℝ}
    (hQ : 0 ≤ Q) (hS : 0 < S) (hH : 0 ≤ H)
    (hscale : Q*M ≤ S*(H+2)) :
    (Q*C/Real.sqrt S) ^ 2 * (2*H) ^ 2 * (2*M) ≤
      (16*C^2*(H+2)^4) * Q :=
  @TaoTrudgianYang2025.jutila_reflection_scale_one Q M S H C hQ hS hH hscale

-- JutilaDualScales: jutila_reflection_scale_two
example {Q M S H C T : ℝ}
    (hQ : 0 ≤ Q) (hM : 0 ≤ M) (hS : 0 < S) (hH : 0 ≤ H)
    (hscale : Q*M ≤ S*(H+2)) (hST : S ≤ T) :
    (Q*C/Real.sqrt S) ^ 2 * (2*H) ^ 2 * (2*M)^2 ≤
      (16*C^2*(H+2)^4) * T :=
  @TaoTrudgianYang2025.jutila_reflection_scale_two Q M S H C T hQ hM hS hH hscale hST

-- JutilaDualScales: jutila_reflection_main_core_le
example (k : ℕ) {Q M S H C T R : ℝ}
    (hQ : 0 ≤ Q) (hM : 0 ≤ M) (hS : 0 < S) (hH : 0 ≤ H)
    (hR : 0 ≤ R) (hscale : Q*M ≤ S*(H+2)) (hST : S ≤ T) :
    (Q*C/Real.sqrt S) ^ (2*k) * (2*H) ^ (2*k) * (2*M)^k *
        (R^2 + R*(2*M)^k + R^(5/4 : ℝ)*T^(1/2 : ℝ)) ≤
      (16*C^2*(H+2)^4)^k *
        (R^2*Q^k + R*T^k + R^(5/4 : ℝ)*T^(1/2 : ℝ)*Q^k) :=
  @TaoTrudgianYang2025.jutila_reflection_main_core_le k Q M S H C T R hQ hM hS hH hR hscale hST

-- JutilaPhysicalMain: jutila_reflected_main_le_physical
example (k Q H j : ℕ) (T : ℝ) (W : Finset ℝ)
    {A C ε η : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hQ : 0 < Q) (hH : 0 < H) (hT : 1 ≤ T)
    (hj : j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1))
    (hfar : ¬ 2 ^ (j+1) ≤ Q) :
    ((Q : ℝ)*C/Real.sqrt ((2 ^ j : ℕ) : ℝ)) ^ (2*k) *
        ((2*(H : ℝ)) ^ (2*k) *
          jutilaPrefixMomentMajorant k (heathBrownFixedReflectionLength Q H j) T W A ε η) ≤
      jutilaMomentLoss k H T A ε η * jutilaPhysicalMain k Q H T W C :=
  @TaoTrudgianYang2025.jutila_reflected_main_le_physical k Q H j T W A C ε η hA hC hη hQ hH hT hj hfar

-- JutilaPhysicalPatterns: jutila_bin_card_le_square
example (W : Finset ℝ) (j : ℕ) :
    ((heathBrownDifferenceBin W j).card : ℝ) ≤ (W.card : ℝ)^2 :=
  @TaoTrudgianYang2025.jutila_bin_card_le_square W j

-- JutilaPhysicalPatterns: jutila_hybrid_sum_le_physical
example (q k Q H : ℕ) (T δ : ℝ) (W : Finset ℝ)
    {E F A C K L D ε η : ℝ}
    (hE : 0 ≤ E) (hF : 0 ≤ F) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hD : 0 ≤ D) (hη : 0 ≤ η)
    (hQ : 0 < Q) (hH : 0 < H) (hT : 1 ≤ T)
    (hδ : 4 ≤ δ) (hHδ : 4*(H : ℝ) ≤ δ) (hsep : IsSeparated δ W) :
    (∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
      jutilaTraceHybridMajorant q k Q H j T W E F A C K L D ε η) ≤
      ((Nat.log 2 (Nat.floor T) + 1 : ℕ) : ℝ) *
        jutilaPhysicalEnvelope q k Q H T W E F A C K L D ε η :=
  @TaoTrudgianYang2025.jutila_hybrid_sum_le_physical q k Q H T δ W E F A C K L D ε η hE hF hA hC hK hL hD hη hQ hH hT hδ hHδ hsep

-- JutilaPhysicalPatterns: jutila_physical_pattern_bound
example (cutoff : GMSmoothCutoff)
    (q k : ℕ) (hq : 2 ≤ q) (hk : 0 < k)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ E F A C K L D T₀ : ℝ,
      0 < E ∧ 0 < F ∧ 0 < A ∧ 0 < C ∧ 0 < K ∧ 0 < L ∧ 0 < D ∧ 1 ≤ T₀ ∧
      ∀ (P : LargeValuePattern) (δ : ℝ),
        30 ≤ P.scale → 1 < P.V → T₀ ≤ P.T → 4 ≤ δ →
        ∃ (W : Finset ℝ) (Q : ℕ),
          W ⊆ P.reflectedOrdinates ∧
          P.ordinates.card ≤ 6 * (2 * Nat.ceil δ + 1) * W.card ∧
          0 < Q ∧ P.N / 2 ≤ (Q : ℝ) ∧ (Q : ℝ) ≤ 2 * P.N ∧
          IsSeparated δ W ∧ InBaseInterval P.T W ∧
          ∀ H : ℕ, 0 < H → 4*(H : ℝ) ≤ δ →
            (W.card : ℝ) * ((P.V-1)/3) ^ 2 ≤ 2 * (Q : ℝ) ^ 2 ∨
              (W.card : ℝ) ^ 2 * ((P.V-1)/3) ^ (4*k) ≤
                (2 * (Q : ℝ)) ^ (2*k) *
                  (((Nat.log 2 (Nat.floor P.T) + 1 : ℕ) : ℝ) *
                    jutilaPhysicalEnvelope q k Q H P.T W E F A C K L D ε η) :=
  @TaoTrudgianYang2025.jutila_physical_pattern_bound cutoff q k hq hk ε η hε hη

-- JutilaSmoothingErrors: jutila_zero_mode_smoothing_le
example {a θ T F : ℝ} {Q : ℕ}
    (hθ : 0 < θ) (hT : 1 ≤ T) (hQT : (Q : ℝ) ≤ 2*T) (hF : 0 ≤ F) :
    (Q : ℝ)*F/(heathBrownSmoothingHeight T θ : ℝ)^
        heathBrownReflectionDerivativeOrder a θ ≤ 2*F*T^(-a) :=
  @TaoTrudgianYang2025.jutila_zero_mode_smoothing_le a θ T F Q hθ hT hQT hF

-- JutilaSmoothingErrors: jutila_physical_envelope_smoothing_le
example
    (k Q : ℕ) (T : ℝ) (W : Finset ℝ) {θ E F A C K L D ε η : ℝ}
    (hθ : 0 < θ) (hθOne : θ ≤ 1) (hT : 1 ≤ T) (hQ : 0 < Q)
    (hQT : (Q : ℝ) ≤ 2*T) (hF : 0 ≤ F)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hD : 0 ≤ D) :
    jutilaPhysicalEnvelope (heathBrownReflectionDerivativeOrder 0 θ) k Q
        (heathBrownSmoothingHeight T θ) T W E F A C K L D ε η ≤
      jutilaSmoothingCoefficient k T θ E F A C K L D ε η *
        jutilaMomentCore k Q T W :=
  @TaoTrudgianYang2025.jutila_physical_envelope_smoothing_le k Q T W θ E F A C K L D ε η hθ hθOne hT hQ hQT hF hK hL hD

-- JutilaSmoothingProfile: jutila_dual_cap_smoothing_le
example {θ T : ℝ}
    (hθ : 0 ≤ θ) (hθOne : θ ≤ 1) (hT : 1 ≤ T) :
    (jutilaDualLengthCap T (heathBrownSmoothingHeight T θ) : ℝ) ≤ 4*T^2 :=
  @TaoTrudgianYang2025.jutila_dual_cap_smoothing_le θ T hθ hθOne hT

-- JutilaSmoothingProfile: jutila_cap_log_smoothing_le
example {θ T : ℝ}
    (hθ : 0 ≤ θ) (hθOne : θ ≤ 1) (hT : 1 ≤ T) :
    (Nat.clog 2 (jutilaDualLengthCap T (heathBrownSmoothingHeight T θ)) : ℝ)+1 ≤
      2+(Real.log 4+2*Real.log T)/Real.log 2 :=
  @TaoTrudgianYang2025.jutila_cap_log_smoothing_le θ T hθ hθOne hT

-- JutilaSmoothingProfile: jutila_smoothing_profile_components
example (θ T : ℝ) :
    1 ≤ jutilaSmoothingProfile θ T ∧
    ((Nat.log 2 (Nat.floor T)+1 : ℕ) : ℝ) ≤ jutilaSmoothingProfile θ T ∧
    (heathBrownSmoothingHeight T θ : ℝ) ≤ jutilaSmoothingProfile θ T ∧
    ((Nat.clog 2 (jutilaDualLengthCap T (heathBrownSmoothingHeight T θ)) : ℝ)+1) ≤
      jutilaSmoothingProfile θ T ∧
    (2*(jutilaDualLengthCap T (heathBrownSmoothingHeight T θ) : ℝ))^θ ≤
      jutilaSmoothingProfile θ T :=
  @TaoTrudgianYang2025.jutila_smoothing_profile_components θ T

-- JutilaSmoothingProfile: jutila_smoothing_profile_uniform
example {θ : ℝ} (hθ : 0 < θ) (hθOne : θ ≤ 1) :
    ∃ B T₀ : ℝ, 0 < B ∧ 2 ≤ T₀ ∧
      ∀ T : ℝ, T₀ ≤ T → jutilaSmoothingProfile θ T ≤ B*T^(2*θ) :=
  @TaoTrudgianYang2025.jutila_smoothing_profile_uniform θ hθ hθOne

-- JutilaSmoothingLosses: jutila_powered_divisor_loss
example (k M : ℕ) (θ : ℝ) :
    ((((2^k*M^k : ℕ) : ℝ)^θ)^2) = ((2*(M : ℝ))^θ)^(2*k) :=
  @TaoTrudgianYang2025.jutila_powered_divisor_loss k M θ

-- JutilaSmoothingLosses: jutila_moment_loss_le_profile
example (k : ℕ) (θ T C : ℝ) {A : ℝ}
    (hA : 0 ≤ A) (hT : 0 ≤ T) :
    jutilaMomentLoss k (heathBrownSmoothingHeight T θ) T A θ θ *
        (16*C^2*((heathBrownSmoothingHeight T θ : ℝ)+2)^4)^k ≤
      (A*(16*C^2*(3 : ℝ)^4)^k) * jutilaSmoothingProfile θ T^(8*k)*T^θ :=
  @TaoTrudgianYang2025.jutila_moment_loss_le_profile k θ T C A hA hT

-- JutilaSmoothingLosses: jutila_smoothing_coefficient_uniform
example
    (k : ℕ) {θ E F A C K L D : ℝ}
    (hθ : 0 < θ) (hθOne : θ ≤ 1)
    (hE : 0 ≤ E) (hF : 0 ≤ F) (hA : 0 ≤ A)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hD : 0 ≤ D) :
    ∃ B T₀ : ℝ, 0 < B ∧ 2 ≤ T₀ ∧
      ∀ T : ℝ, T₀ ≤ T →
        ((Nat.log 2 (Nat.floor T)+1 : ℕ) : ℝ) *
          jutilaSmoothingCoefficient k T θ E F A C K L D θ θ ≤
            B*T^(((16*k : ℕ) : ℝ)*θ+3*θ) :=
  @TaoTrudgianYang2025.jutila_smoothing_coefficient_uniform k θ E F A C K L D hθ hθOne hE hF hA hK hL hD

-- JutilaSmoothedPatterns: jutila_smoothing_thinning_le
example {θ T : ℝ}
    (hθ : 0 ≤ θ) (hT : 1 ≤ T) :
    (6 : ℝ)*(2*(Nat.ceil (4*(heathBrownSmoothingHeight T θ : ℝ)) : ℝ)+1) ≤
      108*T^θ :=
  @TaoTrudgianYang2025.jutila_smoothing_thinning_le θ T hθ hT

-- JutilaSmoothedPatterns: jutila_smoothed_pattern_bound
example (cutoff : GMSmoothCutoff)
    (k : ℕ) (hk : 0 < k) {ν : ℝ} (hν : 0 < ν) :
    ∃ B T₀ : ℝ, 0 < B ∧ 2 ≤ T₀ ∧
      ∀ P : LargeValuePattern,
        30 ≤ P.scale → 1 < P.V → T₀ ≤ P.T → P.N ≤ P.T →
        ∃ (W : Finset ℝ) (Q : ℕ),
          W ⊆ P.reflectedOrdinates ∧
          (P.ordinates.card : ℝ) ≤ B*P.T^ν*(W.card : ℝ) ∧
          0 < Q ∧ P.N/2 ≤ (Q : ℝ) ∧ (Q : ℝ) ≤ 2*P.N ∧
          IsSeparated 1 W ∧ InBaseInterval P.T W ∧
          ((W.card : ℝ)*((P.V-1)/3)^2 ≤ 2*(Q : ℝ)^2 ∨
            (W.card : ℝ)^2*((P.V-1)/3)^(4*k) ≤
              B*P.T^ν*(2*(Q : ℝ))^(2*k)*jutilaMomentCore k Q P.T W) :=
  @TaoTrudgianYang2025.jutila_smoothed_pattern_bound cutoff k hk ν hν

-- The power needed for Add-est (iii) consumes the actual pattern.
example (cutoff : GMSmoothCutoff)
    {ν : ℝ} (hν : 0 < ν) :
    ∃ B T₀ : ℝ, 0 < B ∧ 2 ≤ T₀ ∧
      ∀ P : LargeValuePattern,
        30 ≤ P.scale → 1 < P.V → T₀ ≤ P.T → P.N ≤ P.T →
        ∃ (W : Finset ℝ) (Q : ℕ),
          W ⊆ P.reflectedOrdinates ∧
          (P.ordinates.card : ℝ) ≤ B*P.T^ν*(W.card : ℝ) ∧
          0 < Q ∧ P.N/2 ≤ (Q : ℝ) ∧ (Q : ℝ) ≤ 2*P.N ∧
          IsSeparated 1 W ∧ InBaseInterval P.T W ∧
          ((W.card : ℝ)*((P.V-1)/3)^2 ≤ 2*(Q : ℝ)^2 ∨
            (W.card : ℝ)^2*((P.V-1)/3)^52 ≤
              B*P.T^ν*(2*(Q : ℝ))^26*jutilaMomentCore 13 Q P.T W) :=
  @jutila_smoothed_pattern_bound cutoff 13 (by norm_num) ν hν

-- These are the literal three physical terms at k=13.
example (Q : ℕ) (T : ℝ) (W : Finset ℝ) :
    jutilaMomentCore 13 Q T W =
      (W.card : ℝ)^2*(Q : ℝ)^13+(W.card : ℝ)*T^13+
        (W.card : ℝ)^(5/4 : ℝ)*T^(1/2 : ℝ)*(Q : ℝ)^13 := rfl

-- An empty actual family contributes zero to every physical main term.
example (k Q : ℕ) (T : ℝ) : jutilaMomentCore k Q T ∅ = 0 := by
  simp [jutilaMomentCore, Real.zero_rpow (by norm_num : (5/4 : ℝ) ≠ 0)]

-- The cap retains the ceiling and its explicit endpoint padding.
example (T : ℝ) (H : ℕ) :
    jutilaDualLengthCap T H = Nat.ceil (T*H)+1 := rfl

-- The zero-mode derivative budget gives genuine negative height decay.
example {T F : ℝ} {Q : ℕ} (hT : 1 ≤ T) (hQT : (Q : ℝ) ≤ 2*T) (hF : 0 ≤ F) :
    (Q : ℝ)*F/(heathBrownSmoothingHeight T (1/2) : ℝ)^
        heathBrownReflectionDerivativeOrder 5 (1/2) ≤ 2*F*T^(-5 : ℝ) :=
  jutila_zero_mode_smoothing_le (by norm_num) hT hQT hF

-- The thinning loss is derived for every actual positive smoothing parameter.
example {ν T : ℝ} (hν : 0 < ν) (hT : 1 ≤ T) :
    (6 : ℝ)*(2*(Nat.ceil (4*(heathBrownSmoothingHeight T ν : ℝ)) : ℝ)+1) ≤
      108*T^ν := jutila_smoothing_thinning_le hν.le hT

end JutilaPhysicalSmoothingRegression
