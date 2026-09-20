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

example : ¬ ∃ ρ' ρstar' s' : ℝ,
    InLargeValueEnergyRegion (3 / 4) 1 ρ' ρstar' s' ∧ s' ≤ 1 := by
  rintro ⟨ρ', ρstar', s', hregion, hs⟩
  have hlower := hregion.two_le_s
  linarith

example : doubleZetaSum (singletonLargeValuePattern 2 (3 / 4) 2
    (by norm_num) (by norm_num)) = 9 := by
  rw [singletonLargeValuePattern_doubleZetaSum]
  norm_num

example :
    (RationalAffineFraction.mk 270 (-173) 125 (-93)).normalizeSign.eval
        (173 / 229 : ℝ) =
      (RationalAffineFraction.mk 270 (-173) 125 (-93)).eval
        (173 / 229 : ℝ) :=
  RationalAffineFraction.eval_normalizeSign _ _
