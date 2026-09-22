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

namespace JutilaFullSourceRegression

open TaoTrudgianYang2025 RiemannZeta.GuthMaynard Filter

-- JutilaRecurrence: jutila_card_five_quarters_le
example (r : ℕ) :
    (r : ℝ)^(5/4 : ℝ) ≤ (r : ℝ)*Real.sqrt (r : ℝ) :=
  @TaoTrudgianYang2025.jutila_card_five_quarters_le r

-- JutilaRecurrence: jutila_sqrt_recurrence
example {R b c : ℝ} (hR : 0 ≤ R)
    (h : R ≤ b+c*Real.sqrt R) : R ≤ 2*b+c^2 :=
  @TaoTrudgianYang2025.jutila_sqrt_recurrence R b c hR h

-- JutilaRecurrence: jutila_powered_recurrence_card_le
example (k Q : ℕ) (T D V : ℝ) (W : Finset ℝ)
    (hT : 0 ≤ T) (hD : 0 ≤ D) (hV : 0 < V)
    (habs : 2*D*(Q : ℝ)^k ≤ V^(4*k))
    (hrec : (W.card : ℝ)^2*V^(4*k) ≤ D*jutilaMomentCore k Q T W) :
    (W.card : ℝ) ≤ 4*D*T^k/V^(4*k) +
      4*D^2*T*(Q : ℝ)^(2*k)/V^(8*k) :=
  @TaoTrudgianYang2025.jutila_powered_recurrence_card_le k Q T D V W hT hD hV habs hrec

-- JutilaLocalCardinality: jutila_local_pattern_cardinality
example (cutoff : GMSmoothCutoff)
    (k : ℕ) (hk : 0 < k) {ν : ℝ} (hν : 0 < ν) :
    ∃ B T₀ : ℝ, 0 < B ∧ 2 ≤ T₀ ∧
      ∀ P : LargeValuePattern,
        30 ≤ P.scale → 1 < P.V → T₀ ≤ P.T → P.N ≤ P.T →
        2*(B*P.T^ν*(4*P.N)^(2*k))*(2*P.N)^k ≤ ((P.V-1)/3)^(4*k) →
        (P.ordinates.card : ℝ) ≤
          jutilaLocalCardinalityBound k P.N P.T P.V (B*P.T^ν) :=
  @TaoTrudgianYang2025.jutila_local_pattern_cardinality cutoff k hk ν hν

-- JutilaLocalAlgebra: jutila_local_cardinality_expand
example (k : ℕ) (N T V Z : ℝ) (hV : 1 < V) :
    jutilaLocalCardinalityBound k N T V Z =
      (72*Z)*N^2/(V-1)^2 +
      (4*Z^2*(4 : ℝ)^(2*k)*(3 : ℝ)^(4*k))*T^k*N^(2*k)/(V-1)^(4*k) +
      (4*Z^3*(4 : ℝ)^(4*k)*(2 : ℝ)^(2*k)*(3 : ℝ)^(8*k))*
        T*N^(6*k)/(V-1)^(8*k) :=
  @TaoTrudgianYang2025.jutila_local_cardinality_expand k N T V Z hV

-- JutilaLocalAlgebra: jutila_local_absorption_identity
example (k : ℕ) (N T B ν : ℝ) :
    (2*(B*T^ν*(4*N)^(2*k))*(2*N)^k)*(3 : ℝ)^(4*k) =
      (2*B*(4 : ℝ)^(2*k)*(2 : ℝ)^k*(3 : ℝ)^(4*k))*T^ν*N^(3*k) :=
  @TaoTrudgianYang2025.jutila_local_absorption_identity k N T B ν

-- JutilaLocalAlgebra: jutila_local_smoothing_powers
example {T B ν : ℝ} (hT : 0 < T) :
    (B*T^ν)^2 = B^2*T^(2*ν) ∧ (B*T^ν)^3 = B^3*T^(3*ν) :=
  @TaoTrudgianYang2025.jutila_local_smoothing_powers T B ν hT

-- JutilaLocalUniform: jutila_local_cardinality_uniform
example (cutoff : GMSmoothCutoff)
    (k : ℕ) (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 1 ≤ C ∧ 2 ≤ T₀ ∧
      ∀ P : LargeValuePattern,
        30 ≤ P.scale → 1 < P.V → T₀ ≤ P.T → P.N ≤ P.T →
        C*P.T^ε*P.N^(3*k) ≤ (P.V-1)^(4*k) →
        (P.ordinates.card : ℝ) ≤ C*P.T^ε*
          (P.N^2/(P.V-1)^2 +
            P.T^k*P.N^(2*k)/(P.V-1)^(4*k) +
            P.T*P.N^(6*k)/(P.V-1)^(8*k)) :=
  @TaoTrudgianYang2025.jutila_local_cardinality_uniform cutoff k hk ε hε

-- LargeValueSubdivision: LargeValuePattern.localBin_subset
example (P : LargeValuePattern) (L : ℝ) (j : ℕ) :
    P.localBin L j ⊆ P.ordinates :=
  @TaoTrudgianYang2025.LargeValuePattern.localBin_subset P L j

-- LargeValueSubdivision: LargeValuePattern.localBin_in_interval
example (P : LargeValuePattern) {L : ℝ}
    (hL : 0 < L) (j : ℕ) :
    ∀ t ∈ P.localBin L j,
      P.intervalLeft+(j : ℝ)*L ≤ t ∧ t ≤ P.intervalLeft+((j : ℝ)+1)*L :=
  @TaoTrudgianYang2025.LargeValuePattern.localBin_in_interval P L hL j

-- LargeValueSubdivision: LargeValuePattern.card_eq_sum_localized
example (P : LargeValuePattern)
    {L : ℝ} (hL : 0 < L) :
    P.ordinates.card =
      ∑ j ∈ Finset.range (Nat.floor (P.T/L)+1), (P.localized L hL j).ordinates.card :=
  @TaoTrudgianYang2025.LargeValuePattern.card_eq_sum_localized P L hL

-- LargeValueSubdivision: LargeValuePattern.card_le_of_localized
example (P : LargeValuePattern)
    {L : ℝ} (hL : 0 < L) (B : ℝ)
    (hbound : ∀ j ∈ Finset.range (Nat.floor (P.T/L)+1),
      ((P.localized L hL j).ordinates.card : ℝ) ≤ B) :
    (P.ordinates.card : ℝ) ≤ ((Nat.floor (P.T/L)+1 : ℕ) : ℝ)*B :=
  @TaoTrudgianYang2025.LargeValuePattern.card_le_of_localized P L hL B hbound

-- JutilaSubdivision: jutila_subdivided_cardinality
example (cutoff : GMSmoothCutoff)
    (k : ℕ) (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 1 ≤ C ∧ 2 ≤ T₀ ∧
      ∀ (P : LargeValuePattern) (L : ℝ),
        30 ≤ P.scale → 1 < P.V → T₀ ≤ L → P.N ≤ L →
        C*L^ε*P.N^(3*k) ≤ (P.V-1)^(4*k) →
        (P.ordinates.card : ℝ) ≤ C*L^ε*(1+P.T/L)*
          (P.N^2/(P.V-1)^2 +
            L^k*P.N^(2*k)/(P.V-1)^(4*k) +
            L*P.N^(6*k)/(P.V-1)^(8*k)) :=
  @TaoTrudgianYang2025.jutila_subdivided_cardinality cutoff k hk ε hε

-- JutilaSubdivision: jutila_subdivided_cardinality_native
example
    (k : ℕ) (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 1 ≤ C ∧ 2 ≤ T₀ ∧
      ∀ (P : LargeValuePattern) (L : ℝ),
        30 ≤ P.scale → 1 < P.V → T₀ ≤ L → P.N ≤ L →
        C*L^ε*P.N^(3*k) ≤ (P.V-1)^(4*k) →
        (P.ordinates.card : ℝ) ≤ C*L^ε*(1+P.T/L)*
          (P.N^2/(P.V-1)^2 +
            L^k*P.N^(2*k)/(P.V-1)^(4*k) +
            L*P.N^(6*k)/(P.V-1)^(8*k)) :=
  @TaoTrudgianYang2025.jutila_subdivided_cardinality_native k hk ε hε

-- JutilaPowerWindows: eventually_rpow_add_one_le_rpow
example {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∀ᶠ N : ℝ in atTop, N^a+1 ≤ N^b :=
  @TaoTrudgianYang2025.eventually_rpow_add_one_le_rpow a b ha hab

-- JutilaPowerWindows: jutila_local_power_identity
example (k : ℕ) {N : ℝ} (hN : 0 < N) (s ℓ : ℝ) :
    N^2/(N^s)^2+(N^ℓ)^k*N^(2*k)/(N^s)^(4*k)+N^ℓ*N^(6*k)/(N^s)^(8*k) =
      N^(2-2*s)+N^((k : ℝ)*ℓ+2*k-4*k*s)+N^(ℓ+6*k-8*k*s) :=
  @TaoTrudgianYang2025.jutila_local_power_identity k N hN s ℓ

-- JutilaPowerWindows: jutila_local_power_terms_le
example (k : ℕ) {N σ δ ℓ : ℝ}
    (hk : 0 < k) (hN : 1 ≤ N) (hδ : 0 ≤ δ)
    (hfirst : (k : ℝ)*ℓ+2*k-4*k*σ ≤ 2-2*σ)
    (hsecond : ℓ+6*k-8*k*σ ≤ 2-2*σ) :
    N^2/(N^(σ-2*δ))^2+
        (N^ℓ)^k*N^(2*k)/(N^(σ-2*δ))^(4*k)+
        N^ℓ*N^(6*k)/(N^(σ-2*δ))^(8*k) ≤
      3*N^(2-2*σ+16*k*δ) :=
  @TaoTrudgianYang2025.jutila_local_power_terms_le k N σ δ ℓ hk hN hδ hfirst hsecond

-- JutilaPowerWindows: jutila_subdivision_power_factor
example {N T τ δ ℓ : ℝ}
    (hN : 1 ≤ N) (hT : T ≤ N^(τ+δ)) (hδ : 0 ≤ δ) :
    1+T/N^ℓ ≤ 2*N^(max 0 (τ-ℓ)+δ) :=
  @TaoTrudgianYang2025.jutila_subdivision_power_factor N T τ δ ℓ hN hT hδ

-- JutilaWindowBound: jutila_largeValueBound_of_local_exponent
example
    (k : ℕ) (hk : 0 < k) {σ τ ℓ : ℝ}
    (hσ : 3/4 < σ) (hℓ : 1 ≤ ℓ)
    (hfirst : (k : ℝ)*ℓ+2*k-4*k*σ ≤ 2-2*σ)
    (hsecond : ℓ+6*k-8*k*σ ≤ 2-2*σ) :
    IsLargeValueBound σ τ (2-2*σ+max 0 (τ-ℓ)) :=
  @TaoTrudgianYang2025.jutila_largeValueBound_of_local_exponent k hk σ τ ℓ hσ hℓ hfirst hsecond

-- ClassicalMeanSquareBound: IsLargeValueBound.mono
example {σ τ ρ ρ' : ℝ}
    (h : IsLargeValueBound σ τ ρ) (hρ : ρ ≤ ρ') : IsLargeValueBound σ τ ρ' :=
  @TaoTrudgianYang2025.IsLargeValueBound.mono σ τ ρ ρ' h hρ

-- ClassicalMeanSquareBound: meanSquare_largeValueBound
example {σ τ : ℝ} (hσ : 0 < σ) :
    IsLargeValueBound σ τ (max (2-2*σ) (1+τ-2*σ)) :=
  @TaoTrudgianYang2025.meanSquare_largeValueBound σ τ hσ

-- JutilaLargeValues: jutila_optimization_identity
example (k : ℕ) (σ τ : ℝ) :
    2-2*σ+max 0 (τ-jutilaLocalExponent k σ) = jutilaLargeValueExponent k σ τ :=
  @TaoTrudgianYang2025.jutila_optimization_identity k σ τ

-- JutilaLargeValues: jutila_local_exponent_constraints
example (k : ℕ) (hk : 0 < k) (σ : ℝ) :
    (k : ℝ)*jutilaLocalExponent k σ+2*k-4*k*σ ≤ 2-2*σ ∧
    jutilaLocalExponent k σ+6*k-8*k*σ ≤ 2-2*σ :=
  @TaoTrudgianYang2025.jutila_local_exponent_constraints k hk σ

-- JutilaLargeValues: jutila_largeValueBound
example (k : ℕ) (hk : 0 < k) {σ τ : ℝ}
    (hσLower : 1/2 ≤ σ) (_hσUpper : σ ≤ 1) (hτ : 0 ≤ τ) :
    IsLargeValueBound σ τ (jutilaLargeValueExponent k σ τ) :=
  @TaoTrudgianYang2025.jutila_largeValueBound k hk σ τ hσLower _hσUpper hτ

-- JutilaLargeValues: largeValueExponent_le_jutila
example (k : ℕ) (hk : 0 < k) {σ τ : ℝ}
    (hσLower : 1/2 ≤ σ) (hσUpper : σ ≤ 1) (hτ : 0 ≤ τ) :
    largeValueExponent σ τ ≤ (jutilaLargeValueExponent k σ τ : EReal) :=
  @TaoTrudgianYang2025.largeValueExponent_le_jutila k hk σ τ hσLower hσUpper hτ

-- JutilaLargeValues: zetaLargeValueExponent_le_jutila
example (k : ℕ) (hk : 0 < k) {σ τ : ℝ}
    (hσLower : 1/2 ≤ σ) (hσUpper : σ ≤ 1) (hτ : 0 ≤ τ) :
    zetaLargeValueExponent σ τ ≤ (jutilaLargeValueExponent k σ τ : EReal) :=
  @TaoTrudgianYang2025.zetaLargeValueExponent_le_jutila k hk σ τ hσLower hσUpper hτ

-- JutilaEnergyRegions: InLargeValueEnergyRegion.rho_le_of_largeValueBound
example
    {σ τ ρ e s b : ℝ} (hregion : InLargeValueEnergyRegion σ τ ρ e s)
    (hbound : IsLargeValueBound σ τ b) : ρ ≤ b :=
  @TaoTrudgianYang2025.InLargeValueEnergyRegion.rho_le_of_largeValueBound σ τ ρ e s b hregion hbound

-- JutilaEnergyRegions: InLargeValueEnergyRegion.jutila_cardinality
example
    {σ τ ρ e s : ℝ} (h : InLargeValueEnergyRegion σ τ ρ e s)
    (k : ℕ) (hk : 0 < k) : ρ ≤ jutilaLargeValueExponent k σ τ :=
  @TaoTrudgianYang2025.InLargeValueEnergyRegion.jutila_cardinality σ τ ρ e s h k hk

-- JutilaEnergyRegions: InCardinalityEnergyRegion.jutila_cardinality
example
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (k : ℕ) (hk : 0 < k) : ρ ≤ jutilaLargeValueExponent k σ τ :=
  @TaoTrudgianYang2025.InCardinalityEnergyRegion.jutila_cardinality σ τ ρ e h k hk

-- JutilaEnergyRegions: InCardinalityEnergyRegion.jutila_cardinality_powered
example
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (q k : ℕ) (hq : 1 ≤ q) (hk : 0 < k) :
    ρ/q ≤ jutilaLargeValueExponent k σ (τ/q) :=
  @TaoTrudgianYang2025.InCardinalityEnergyRegion.jutila_cardinality_powered σ τ ρ e h q k hq hk

-- JutilaEnergyRegions: jutila_thirteen_formula
example (σ τ : ℝ) :
    jutilaLargeValueExponent 13 σ τ =
      max (2-2*σ) (max (τ+50/13-(76/13)*σ) (τ+78-104*σ)) :=
  @TaoTrudgianYang2025.jutila_thirteen_formula σ τ

-- JutilaEnergyRegions: InCardinalityEnergyRegion.jutila_thirteen_cardinality_powered
example
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (q : ℕ) (hq : 1 ≤ q) :
    ρ/q ≤ max (2-2*σ) (max (τ/q+50/13-(76/13)*σ) (τ/q+78-104*σ)) :=
  @TaoTrudgianYang2025.InCardinalityEnergyRegion.jutila_thirteen_cardinality_powered σ τ ρ e h q hq

-- Localization retains the actual source height and coefficients.
example (P : LargeValuePattern) (L : ℝ) (hL : 0 < L) (j : ℕ) :
    (P.localized L hL j).T = L := rfl

example (P : LargeValuePattern) (L : ℝ) (hL : 0 < L) (j : ℕ) :
    (P.localized L hL j).N = P.N := rfl

example (P : LargeValuePattern) (L : ℝ) (hL : 0 < L) (j : ℕ) :
    (P.localized L hL j).V = P.V := rfl

-- The lower endpoint is included, with no strict sigma hypothesis.
example (k : ℕ) (hk : 0 < k) {τ : ℝ} (hτ : 0 ≤ τ) :
    IsLargeValueBound (1/2) τ (jutilaLargeValueExponent k (1/2) τ) :=
  jutila_largeValueBound k hk (by norm_num) (by norm_num) hτ

-- The complementary branch includes the three-quarters boundary.
example (k : ℕ) (hk : 0 < k) {τ : ℝ} (hτ : 0 ≤ τ) :
    IsLargeValueBound (3/4) τ (jutilaLargeValueExponent k (3/4) τ) :=
  jutila_largeValueBound k hk (by norm_num) (by norm_num) hτ

example (k : ℕ) (hk : 0 < k) {τ : ℝ} (hτ : 0 ≤ τ) :
    IsLargeValueBound 1 τ (jutilaLargeValueExponent k 1 τ) :=
  jutila_largeValueBound k hk (by norm_num) (by norm_num) hτ

-- The actual short-height range includes tau zero.
example {σ : ℝ} (hσ : 0 < σ) :
    IsLargeValueBound σ 0 (2-2*σ) := by
  have hh := meanSquare_largeValueBound (τ := 0) hσ
  simpa only [add_zero, max_eq_left (by linarith : 1-2*σ ≤ 2-2*σ)] using hh

-- Literal paper formula at the integer needed for Add-est (iii).
example {σ τ : ℝ} (hσLower : 1/2 ≤ σ) (hσUpper : σ ≤ 1) (hτ : 0 ≤ τ) :
    IsLargeValueBound σ τ
      (max (2-2*σ) (max (τ+50/13-(76/13)*σ) (τ+78-104*σ))) := by
  simpa only [jutila_thirteen_formula] using
    (jutila_largeValueBound 13 (by norm_num) hσLower hσUpper hτ)

-- Constants and window radius precede the original source pattern.
example (k : ℕ) (hk : 0 < k) {σ τ ε : ℝ}
    (hσLower : 1/2 ≤ σ) (hσUpper : σ ≤ 1) (hτ : 0 ≤ τ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ P : LargeValuePattern, C ≤ P.N →
        P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) →
        P.N^(σ-δ) ≤ P.V → P.V ≤ P.N^(σ+δ) →
        (P.ordinates.card : ℝ) ≤ C*P.N^(jutilaLargeValueExponent k σ τ+ε) := by
  obtain ⟨C, hC, δ, hδ, hp⟩ := jutila_largeValueBound k hk hσLower hσUpper hτ ε hε
  exact ⟨C, hC, δ, hδ, fun P hN hTl hTu hVl hVu => hp P hN hTl hTu hVl hVu⟩

-- Two cardinality caps use separate corrected powering applications.
example {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (q : ℕ) (hq : 1 ≤ q) :
    ρ/q ≤ jutilaLargeValueExponent 13 σ (τ/q) ∧
    ρ/(q+1 : ℕ) ≤ jutilaLargeValueExponent 13 σ (τ/(q+1 : ℕ)) :=
  ⟨h.jutila_cardinality_powered q 13 hq (by norm_num),
    h.jutila_cardinality_powered (q+1) 13 (by omega) (by norm_num)⟩

-- The genuine zeta exponent receives the same source bound.
example {σ τ : ℝ} (hσLower : 1/2 ≤ σ) (hσUpper : σ ≤ 1) (hτ : 0 ≤ τ) :
    zetaLargeValueExponent σ τ ≤
      (max (2-2*σ) (max (τ+50/13-(76/13)*σ) (τ+78-104*σ)) : ℝ) := by
  simpa only [jutila_thirteen_formula] using
    (zetaLargeValueExponent_le_jutila 13 (by norm_num) hσLower hσUpper hτ)

end JutilaFullSourceRegression

namespace AddEstThirdRegression

open TaoTrudgianYang2025

-- EnergyClauseThreeCaps: jutila_thirteen_low_sigma
example {σ t : ℝ} (hσ : σ ≤ 241/319) :
    max (2-2*σ) (max (t+50/13-(76/13)*σ) (t+78-104*σ)) =
      max (2-2*σ) (t+78-104*σ) :=
  @TaoTrudgianYang2025.jutila_thirteen_low_sigma σ t hσ

-- EnergyClauseThreeCaps: jutila_thirteen_high_sigma
example {σ t : ℝ} (hσ : 241/319 ≤ σ) :
    max (2-2*σ) (max (t+50/13-(76/13)*σ) (t+78-104*σ)) =
      max (2-2*σ) (t+50/13-(76/13)*σ) :=
  @TaoTrudgianYang2025.jutila_thirteen_high_sigma σ t hσ

-- EnergyClauseThreeCaps: jutila_thirteen_at_most_one
example {σ t : ℝ}
    (hσ : 173/229 ≤ σ) (ht : t ≤ 1) :
    max (2-2*σ) (max (t+50/13-(76/13)*σ) (t+78-104*σ)) = 2-2*σ :=
  @TaoTrudgianYang2025.jutila_thirteen_at_most_one σ t hσ ht

-- EnergyClauseThreeCaps: InCardinalityEnergyRegion.energyClauseThree_cardinality_caps
example
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 443/586)
    (q : ℕ) (hq : q=2 ∨ q=3) (htlo : (q : ℝ) ≤ τ) (hthi : τ ≤ q+1) :
    1 ≤ τ/q ∧ τ/q ≤ 3/2 ∧
      ρ/q ≤ max (2-2*σ) (max (τ/q+50/13-(76/13)*σ) (τ/q+78-104*σ)) ∧
      ρ/q ≤ max (18/5-4*σ) (12/5-4*σ+τ/q) ∧
      ρ/q ≤ 3-3*σ :=
  @TaoTrudgianYang2025.InCardinalityEnergyRegion.energyClauseThree_cardinality_caps σ τ ρ e h hlo hhi q hq htlo hthi

-- EnergyClauseThreeRates: energyClauseThreeRate_eq_printed
example (σ : ℝ) :
    energyClauseThreeRate σ =
      max ((173-270*σ)/(16*(93-125*σ)))
        (max ((653-890*σ)/(10*(93-125*σ))) ((1151-1190*σ)/(20*(15*σ-2)))) :=
  @TaoTrudgianYang2025.energyClauseThreeRate_eq_printed σ

-- EnergyClauseThreeRates: energyClauseThreeFirstRate_le
example (σ : ℝ) :
    energyClauseThreeFirstRate σ ≤ energyClauseThreeRate σ :=
  @TaoTrudgianYang2025.energyClauseThreeFirstRate_le σ

-- EnergyClauseThreeRates: energyClauseThreeSecondRate_le
example (σ : ℝ) :
    energyClauseThreeSecondRate σ ≤ energyClauseThreeRate σ :=
  @TaoTrudgianYang2025.energyClauseThreeSecondRate_le σ

-- EnergyClauseThreeRates: energyClauseThreeThirdRate_le
example (σ : ℝ) :
    energyClauseThreeThirdRate σ ≤ energyClauseThreeRate σ :=
  @TaoTrudgianYang2025.energyClauseThreeThirdRate_le σ

-- EnergyClauseThreeRates: energyClauseThreeRate_pos
example {σ : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 443/586) :
    0 < energyClauseThreeRate σ :=
  @TaoTrudgianYang2025.energyClauseThreeRate_pos σ hlo hhi

-- EnergyClauseThreeLowCertificates: energyClauseThree_low_0_0
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 1 ≤ t) (hthi : t ≤ 102*σ-76) :
    ((1)*(0)+(0))*t+((4-4*σ)*(2/3)+(1)*(2-2*σ)) ≤ energyClauseThreeSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_low_0_0 σ t hlo hhi htlo hthi

-- EnergyClauseThreeLowCertificates: energyClauseThree_low_0_1
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (_hhi : σ ≤ 241/319)
    (htlo : 102*σ-76 ≤ t) (hthi : t ≤ 100*σ-372/5) :
    ((1)*(1)+(0))*t+((4-4*σ)*(2/3)+(1)*(78-104*σ)) ≤ energyClauseThreeSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_low_0_1 σ t hlo _hhi htlo hthi

-- EnergyClauseThreeLowCertificates: energyClauseThree_low_0_2
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 100*σ-372/5 ≤ t) (hthi : t ≤ 6/5) :
    ((1)*(0)+(0))*t+((4-4*σ)*(2/3)+(1)*(18/5-4*σ)) ≤ energyClauseThreeSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_low_0_2 σ t hlo hhi htlo hthi

-- EnergyClauseThreeLowCertificates: energyClauseThree_low_1_0
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 1 ≤ t) (hthi : t ≤ 102*σ-76) :
    ((5/2)*(0)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(2-2*σ)) ≤ energyClauseThreeSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_low_1_0 σ t hlo hhi htlo hthi

-- EnergyClauseThreeLowCertificates: energyClauseThree_low_1_1
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (_hhi : σ ≤ 241/319)
    (htlo : 102*σ-76 ≤ t) (hthi : t ≤ 100*σ-372/5) :
    ((5/2)*(1)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(78-104*σ)) ≤ energyClauseThreeSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_low_1_1 σ t hlo _hhi htlo hthi

-- EnergyClauseThreeLowCertificates: energyClauseThree_low_1_2
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 100*σ-372/5 ≤ t) (hthi : t ≤ 6/5) :
    ((5/2)*(0)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(18/5-4*σ)) ≤ energyClauseThreeSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_low_1_2 σ t hlo hhi htlo hthi

-- EnergyClauseThreeLowCertificates: energyClauseThree_low_2_0
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 1 ≤ t) (hthi : t ≤ 102*σ-76) :
    ((8/5)*(0)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(2-2*σ)) ≤ energyClauseThreeSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_low_2_0 σ t hlo hhi htlo hthi

-- EnergyClauseThreeLowCertificates: energyClauseThree_low_2_1
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (_hhi : σ ≤ 241/319)
    (htlo : 102*σ-76 ≤ t) (hthi : t ≤ 100*σ-372/5) :
    ((8/5)*(1)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(78-104*σ)) ≤ energyClauseThreeSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_low_2_1 σ t hlo _hhi htlo hthi

-- EnergyClauseThreeLowCertificates: energyClauseThree_low_2_2
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 100*σ-372/5 ≤ t) (hthi : t ≤ 6/5) :
    ((8/5)*(0)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(18/5-4*σ)) ≤ energyClauseThreeSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_low_2_2 σ t hlo hhi htlo hthi

-- EnergyClauseThreeLowCertificates: energyClauseThree_low_3_0
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 1 ≤ t) (hthi : t ≤ 102*σ-76) :
    ((2)*(0)+(0))*t+((3-4*σ)*(1/2)+(2)*(2-2*σ)) ≤ energyClauseThreeSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_low_3_0 σ t hlo hhi htlo hthi

-- EnergyClauseThreeLowCertificates: energyClauseThree_low_3_1
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (_hhi : σ ≤ 241/319)
    (htlo : 102*σ-76 ≤ t) (hthi : t ≤ 100*σ-372/5) :
    ((2)*(1)+(0))*t+((3-4*σ)*(1/2)+(2)*(78-104*σ)) ≤ energyClauseThreeSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_low_3_1 σ t hlo _hhi htlo hthi

-- EnergyClauseThreeLowCertificates: energyClauseThree_low_3_2
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 100*σ-372/5 ≤ t) (hthi : t ≤ 6/5) :
    ((2)*(0)+(0))*t+((3-4*σ)*(1/2)+(2)*(18/5-4*σ)) ≤ energyClauseThreeSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_low_3_2 σ t hlo hhi htlo hthi

-- EnergyClauseThreeLowCertificates: energyClauseThree_low_4_0
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 1 ≤ t) (hthi : t ≤ 102*σ-76) :
    ((3)*(0)+(0))*t+((1-2*σ)*(1/2)+(3)*(2-2*σ)) ≤ energyClauseThreeSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_low_4_0 σ t hlo hhi htlo hthi

-- EnergyClauseThreeLowCertificates: energyClauseThree_low_4_1
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (_hhi : σ ≤ 241/319)
    (htlo : 102*σ-76 ≤ t) (hthi : t ≤ 100*σ-372/5) :
    ((3)*(1)+(0))*t+((1-2*σ)*(1/2)+(3)*(78-104*σ)) ≤ energyClauseThreeSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_low_4_1 σ t hlo _hhi htlo hthi

-- EnergyClauseThreeLowCertificates: energyClauseThree_low_4_2
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 100*σ-372/5 ≤ t) (hthi : t ≤ 6/5) :
    ((3)*(0)+(0))*t+((1-2*σ)*(1/2)+(3)*(18/5-4*σ)) ≤ energyClauseThreeSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_low_4_2 σ t hlo hhi htlo hthi

-- EnergyClauseThreeLowCertificates: energyClauseThree_low_5_0
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 1 ≤ t) (hthi : t ≤ 102*σ-76) :
    ((12/5)*(0)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(2-2*σ)) ≤ energyClauseThreeSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_low_5_0 σ t hlo hhi htlo hthi

-- EnergyClauseThreeLowCertificates: energyClauseThree_low_5_1
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (_hhi : σ ≤ 241/319)
    (htlo : 102*σ-76 ≤ t) (hthi : t ≤ 100*σ-372/5) :
    ((12/5)*(1)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(78-104*σ)) ≤ energyClauseThreeSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_low_5_1 σ t hlo _hhi htlo hthi

-- EnergyClauseThreeLowCertificates: energyClauseThree_low_5_2
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 100*σ-372/5 ≤ t) (hthi : t ≤ 6/5) :
    ((12/5)*(0)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(18/5-4*σ)) ≤ energyClauseThreeSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_low_5_2 σ t hlo hhi htlo hthi

-- EnergyClauseThreeLowCertificates: energyClauseThree_low_6_0
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 1 ≤ t) (hthi : t ≤ 102*σ-76) :
    ((5/4)*(0)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(2-2*σ)) ≤ energyClauseThreeSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_low_6_0 σ t hlo hhi htlo hthi

-- EnergyClauseThreeLowCertificates: energyClauseThree_low_6_1
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (_hhi : σ ≤ 241/319)
    (htlo : 102*σ-76 ≤ t) (hthi : t ≤ 100*σ-372/5) :
    ((5/4)*(1)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(78-104*σ)) ≤ energyClauseThreeSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_low_6_1 σ t hlo _hhi htlo hthi

-- EnergyClauseThreeLowCertificates: energyClauseThree_low_6_2
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 100*σ-372/5 ≤ t) (hthi : t ≤ 6/5) :
    ((5/4)*(0)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(18/5-4*σ)) ≤ energyClauseThreeSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_low_6_2 σ t hlo hhi htlo hthi

-- EnergyClauseThreeLowCertificates: energyClauseThree_low_7_0
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 1 ≤ t) (hthi : t ≤ 102*σ-76) :
    ((21/8)*(0)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(2-2*σ)) ≤ energyClauseThreeFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_low_7_0 σ t hlo hhi htlo hthi

-- EnergyClauseThreeLowCertificates: energyClauseThree_low_7_1
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 102*σ-76 ≤ t) (hthi : t ≤ 100*σ-372/5) :
    ((21/8)*(1)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(78-104*σ)) ≤ energyClauseThreeFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_low_7_1 σ t hlo hhi htlo hthi

-- EnergyClauseThreeLowCertificates: energyClauseThree_low_7_2
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 100*σ-372/5 ≤ t) (hthi : t ≤ 6/5) :
    ((21/8)*(0)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(18/5-4*σ)) ≤ energyClauseThreeFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_low_7_2 σ t hlo hhi htlo hthi

-- EnergyClauseThreeLowCertificates: energyClauseThree_low_8_0
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 1 ≤ t) (hthi : t ≤ 102*σ-76) :
    ((9/5)*(0)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(2-2*σ)) ≤ energyClauseThreeSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_low_8_0 σ t hlo hhi htlo hthi

-- EnergyClauseThreeLowCertificates: energyClauseThree_low_8_1
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 102*σ-76 ≤ t) (hthi : t ≤ 100*σ-372/5) :
    ((9/5)*(1)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(78-104*σ)) ≤ energyClauseThreeSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_low_8_1 σ t hlo hhi htlo hthi

-- EnergyClauseThreeLowCertificates: energyClauseThree_low_8_2
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 100*σ-372/5 ≤ t) (hthi : t ≤ 6/5) :
    ((9/5)*(0)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(18/5-4*σ)) ≤ energyClauseThreeSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_low_8_2 σ t hlo hhi htlo hthi

-- EnergyClauseThreeHighCertificates: energyClauseThree_high_0_0
example {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : 1 ≤ t) (hthi : t ≤ (50*σ-24)/13) :
    ((1)*(0)+(0))*t+((4-4*σ)*(2/3)+(1)*(2-2*σ)) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_high_0_0 σ t hlo hhi htlo hthi

-- EnergyClauseThreeHighCertificates: energyClauseThree_high_0_1
example {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : (50*σ-24)/13 ≤ t) (hthi : t ≤ 8*(15*σ-2)/65) :
    ((1)*(1)+(0))*t+((4-4*σ)*(2/3)+(1)*(50/13-(76/13)*σ)) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_high_0_1 σ t hlo hhi htlo hthi

-- EnergyClauseThreeHighCertificates: energyClauseThree_high_0_2
example {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : 8*(15*σ-2)/65 ≤ t) (hthi : t ≤ 6/5) :
    ((1)*(0)+(0))*t+((4-4*σ)*(2/3)+(1)*(18/5-4*σ)) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_high_0_2 σ t hlo hhi htlo hthi

-- EnergyClauseThreeHighCertificates: energyClauseThree_high_1_0
example {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : 1 ≤ t) (hthi : t ≤ (50*σ-24)/13) :
    ((5/2)*(0)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(2-2*σ)) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_high_1_0 σ t hlo hhi htlo hthi

-- EnergyClauseThreeHighCertificates: energyClauseThree_high_1_1
example {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : (50*σ-24)/13 ≤ t) (hthi : t ≤ 8*(15*σ-2)/65) :
    ((5/2)*(1)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(50/13-(76/13)*σ)) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_high_1_1 σ t hlo hhi htlo hthi

-- EnergyClauseThreeHighCertificates: energyClauseThree_high_1_2
example {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (_hhi : σ ≤ 443/586)
    (htlo : 8*(15*σ-2)/65 ≤ t) (hthi : t ≤ 6/5) :
    ((5/2)*(0)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(18/5-4*σ)) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_high_1_2 σ t hlo _hhi htlo hthi

-- EnergyClauseThreeHighCertificates: energyClauseThree_high_2_0
example {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : 1 ≤ t) (hthi : t ≤ (50*σ-24)/13) :
    ((8/5)*(0)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(2-2*σ)) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_high_2_0 σ t hlo hhi htlo hthi

-- EnergyClauseThreeHighCertificates: energyClauseThree_high_2_1
example {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : (50*σ-24)/13 ≤ t) (hthi : t ≤ 8*(15*σ-2)/65) :
    ((8/5)*(1)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(50/13-(76/13)*σ)) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_high_2_1 σ t hlo hhi htlo hthi

-- EnergyClauseThreeHighCertificates: energyClauseThree_high_2_2
example {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : 8*(15*σ-2)/65 ≤ t) (hthi : t ≤ 6/5) :
    ((8/5)*(0)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(18/5-4*σ)) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_high_2_2 σ t hlo hhi htlo hthi

-- EnergyClauseThreeHighCertificates: energyClauseThree_high_3_0
example {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : 1 ≤ t) (hthi : t ≤ (50*σ-24)/13) :
    ((2)*(0)+(0))*t+((3-4*σ)*(1/2)+(2)*(2-2*σ)) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_high_3_0 σ t hlo hhi htlo hthi

-- EnergyClauseThreeHighCertificates: energyClauseThree_high_3_1
example {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : (50*σ-24)/13 ≤ t) (hthi : t ≤ 8*(15*σ-2)/65) :
    ((2)*(1)+(0))*t+((3-4*σ)*(1/2)+(2)*(50/13-(76/13)*σ)) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_high_3_1 σ t hlo hhi htlo hthi

-- EnergyClauseThreeHighCertificates: energyClauseThree_high_3_2
example {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (_hhi : σ ≤ 443/586)
    (htlo : 8*(15*σ-2)/65 ≤ t) (hthi : t ≤ 6/5) :
    ((2)*(0)+(0))*t+((3-4*σ)*(1/2)+(2)*(18/5-4*σ)) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_high_3_2 σ t hlo _hhi htlo hthi

-- EnergyClauseThreeHighCertificates: energyClauseThree_high_4_0
example {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : 1 ≤ t) (hthi : t ≤ (50*σ-24)/13) :
    ((3)*(0)+(0))*t+((1-2*σ)*(1/2)+(3)*(2-2*σ)) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_high_4_0 σ t hlo hhi htlo hthi

-- EnergyClauseThreeHighCertificates: energyClauseThree_high_4_1
example {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : (50*σ-24)/13 ≤ t) (hthi : t ≤ 8*(15*σ-2)/65) :
    ((3)*(1)+(0))*t+((1-2*σ)*(1/2)+(3)*(50/13-(76/13)*σ)) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_high_4_1 σ t hlo hhi htlo hthi

-- EnergyClauseThreeHighCertificates: energyClauseThree_high_4_2
example {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (_hhi : σ ≤ 443/586)
    (htlo : 8*(15*σ-2)/65 ≤ t) (hthi : t ≤ 6/5) :
    ((3)*(0)+(0))*t+((1-2*σ)*(1/2)+(3)*(18/5-4*σ)) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_high_4_2 σ t hlo _hhi htlo hthi

-- EnergyClauseThreeHighCertificates: energyClauseThree_high_5_0
example {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : 1 ≤ t) (hthi : t ≤ (50*σ-24)/13) :
    ((12/5)*(0)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(2-2*σ)) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_high_5_0 σ t hlo hhi htlo hthi

-- EnergyClauseThreeHighCertificates: energyClauseThree_high_5_1
example {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : (50*σ-24)/13 ≤ t) (hthi : t ≤ 8*(15*σ-2)/65) :
    ((12/5)*(1)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(50/13-(76/13)*σ)) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_high_5_1 σ t hlo hhi htlo hthi

-- EnergyClauseThreeHighCertificates: energyClauseThree_high_5_2
example {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (_hhi : σ ≤ 443/586)
    (htlo : 8*(15*σ-2)/65 ≤ t) (hthi : t ≤ 6/5) :
    ((12/5)*(0)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(18/5-4*σ)) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_high_5_2 σ t hlo _hhi htlo hthi

-- EnergyClauseThreeHighCertificates: energyClauseThree_high_6_0
example {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : 1 ≤ t) (hthi : t ≤ (50*σ-24)/13) :
    ((5/4)*(0)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(2-2*σ)) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_high_6_0 σ t hlo hhi htlo hthi

-- EnergyClauseThreeHighCertificates: energyClauseThree_high_6_1
example {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : (50*σ-24)/13 ≤ t) (hthi : t ≤ 8*(15*σ-2)/65) :
    ((5/4)*(1)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(50/13-(76/13)*σ)) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_high_6_1 σ t hlo hhi htlo hthi

-- EnergyClauseThreeHighCertificates: energyClauseThree_high_6_2
example {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : 8*(15*σ-2)/65 ≤ t) (hthi : t ≤ 6/5) :
    ((5/4)*(0)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(18/5-4*σ)) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_high_6_2 σ t hlo hhi htlo hthi

-- EnergyClauseThreeHighCertificates: energyClauseThree_high_7_0
example {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : 1 ≤ t) (hthi : t ≤ (50*σ-24)/13) :
    ((21/8)*(0)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(2-2*σ)) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_high_7_0 σ t hlo hhi htlo hthi

-- EnergyClauseThreeHighCertificates: energyClauseThree_high_7_1
example {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : (50*σ-24)/13 ≤ t) (hthi : t ≤ 8*(15*σ-2)/65) :
    ((21/8)*(1)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(50/13-(76/13)*σ)) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_high_7_1 σ t hlo hhi htlo hthi

-- EnergyClauseThreeHighCertificates: energyClauseThree_high_7_2
example {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (_hhi : σ ≤ 443/586)
    (htlo : 8*(15*σ-2)/65 ≤ t) (hthi : t ≤ 6/5) :
    ((21/8)*(0)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(18/5-4*σ)) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_high_7_2 σ t hlo _hhi htlo hthi

-- EnergyClauseThreeHighCertificates: energyClauseThree_high_8_0
example {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : 1 ≤ t) (hthi : t ≤ (50*σ-24)/13) :
    ((9/5)*(0)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(2-2*σ)) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_high_8_0 σ t hlo hhi htlo hthi

-- EnergyClauseThreeHighCertificates: energyClauseThree_high_8_1
example {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : (50*σ-24)/13 ≤ t) (hthi : t ≤ 8*(15*σ-2)/65) :
    ((9/5)*(1)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(50/13-(76/13)*σ)) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_high_8_1 σ t hlo hhi htlo hthi

-- EnergyClauseThreeHighCertificates: energyClauseThree_high_8_2
example {σ t : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : 8*(15*σ-2)/65 ≤ t) (hthi : t ≤ 6/5) :
    ((9/5)*(0)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(18/5-4*σ)) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_high_8_2 σ t hlo hhi htlo hthi

-- EnergyClauseThreeTallCertificates: energyClauseThree_tall_0_0
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : 6/5 ≤ t) (hthi : t ≤ σ+3/5) :
    (1)*t+((12/5-4*σ)+4-4*σ) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_tall_0_0 σ t hlo hhi htlo hthi

-- EnergyClauseThreeTallCertificates: energyClauseThree_tall_0_1
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : σ+3/5 ≤ t) (hthi : t ≤ 3/2) :
    (0)*t+((3-3*σ)+4-4*σ) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_tall_0_1 σ t hlo hhi htlo hthi

-- EnergyClauseThreeTallCertificates: energyClauseThree_tall_1_0
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : 6/5 ≤ t) (hthi : t ≤ σ+3/5) :
    ((5/2)*(1))*t+((3-4*σ+5*(12/5-4*σ))/2) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_tall_1_0 σ t hlo hhi htlo hthi

-- EnergyClauseThreeTallCertificates: energyClauseThree_tall_1_1
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : σ+3/5 ≤ t) (hthi : t ≤ 3/2) :
    ((5/2)*(0))*t+((3-4*σ+5*(3-3*σ))/2) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_tall_1_1 σ t hlo hhi htlo hthi

-- EnergyClauseThreeBranches: heathBrownNineBranch_le_extreme_power
example {σ t r a : ℝ}
    (hlo : 3/4 ≤ σ) (hhi : σ ≤ 1)
    (halo : 1/2 ≤ a) (hahi : a ≤ 2/3) (i : Fin 9) :
    heathBrownNineBranch σ t r a i ≤
      heathBrownNineBranch σ t r (if i=0 then 2/3 else 1/2) i :=
  @TaoTrudgianYang2025.heathBrownNineBranch_le_extreme_power σ t r a hlo hhi halo hahi i

-- EnergyClauseThreeBranches: energyClauseThree_low_short_branch
example {σ t r a e : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319)
    (htlo : 1 ≤ t) (hthi : t ≤ 6/5)
    (halo : 1/2 ≤ a) (hahi : a ≤ 2/3)
    (hj : r ≤ max (2-2*σ) (t+(78-104*σ))) (hg : r ≤ 18/5-4*σ)
    (i : Fin 9) (hb : e ≤ heathBrownNineBranch σ t r a i) :
    e ≤ energyClauseThreeRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_low_short_branch σ t r a e hlo hhi htlo hthi halo hahi hj hg i hb

-- EnergyClauseThreeBranches: energyClauseThree_high_short_branch
example {σ t r a e : ℝ}
    (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : 1 ≤ t) (hthi : t ≤ 6/5)
    (halo : 1/2 ≤ a) (hahi : a ≤ 2/3)
    (hj : r ≤ max (2-2*σ) (t+(50/13-(76/13)*σ))) (hg : r ≤ 18/5-4*σ)
    (i : Fin 9) (hb : e ≤ heathBrownNineBranch σ t r a i) :
    e ≤ energyClauseThreeRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_high_short_branch σ t r a e hlo hhi htlo hthi halo hahi hj hg i hb

-- EnergyClauseThreeGeneral: energyClauseThree_tall_bound
example {σ t r : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : 6/5 ≤ t) (hthi : t ≤ 3/2)
    (hg : r ≤ max (18/5-4*σ) (12/5-4*σ+t)) (hcap : r ≤ 3-3*σ) :
    max (r+4-4*σ) ((3-4*σ+5*r)/2) ≤ energyClauseThreeRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_tall_bound σ t r hlo hhi htlo hthi hg hcap

-- EnergyClauseThreeGeneral: InCardinalityEnergyRegion.energyClauseThree_general
example
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 443/586) (htlo : 2 ≤ τ) (hthi : τ ≤ 4) :
    e ≤ energyClauseThreeRate σ*τ :=
  @TaoTrudgianYang2025.InCardinalityEnergyRegion.energyClauseThree_general σ τ ρ e h hlo hhi htlo hthi

-- EnergyClauseThreeGeneral: energyClauseThree_general_bound
example {σ τ : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 443/586) (htlo : 2 ≤ τ) (hthi : τ ≤ 4) :
    IsLargeValueEnergyBound σ τ (energyClauseThreeRate σ*τ) :=
  @TaoTrudgianYang2025.energyClauseThree_general_bound σ τ hlo hhi htlo hthi

-- EnergyClauseThreeZetaCertificates: energyClauseThree_zeta_0
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (_hhi : σ ≤ 443/586)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((1)*2+(0))*t+((4-4*σ)+(1)*(6-12*σ)) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_zeta_0 σ t hlo _hhi htlo hthi

-- EnergyClauseThreeZetaCertificates: energyClauseThree_zeta_1
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (_hhi : σ ≤ 443/586)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((5/2)*2+(0))*t+(((3-4*σ)/2)+(5/2)*(6-12*σ)) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_zeta_1 σ t hlo _hhi htlo hthi

-- EnergyClauseThreeZetaCertificates: energyClauseThree_zeta_2
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (_hhi : σ ≤ 443/586)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((8/5)*2+(2/5))*t+(((12-16*σ)/5)+(8/5)*(6-12*σ)) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_zeta_2 σ t hlo _hhi htlo hthi

-- EnergyClauseThreeZetaCertificates: energyClauseThree_zeta_3
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (_hhi : σ ≤ 443/586)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((2)*2+(0))*t+((3-4*σ)+(2)*(6-12*σ)) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_zeta_3 σ t hlo _hhi htlo hthi

-- EnergyClauseThreeZetaCertificates: energyClauseThree_zeta_4
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (_hhi : σ ≤ 443/586)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((3)*2+(0))*t+((1-2*σ)+(3)*(6-12*σ)) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_zeta_4 σ t hlo _hhi htlo hthi

-- EnergyClauseThreeZetaCertificates: energyClauseThree_zeta_5
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (_hhi : σ ≤ 443/586)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((12/5)*2+(2/5))*t+(((8-16*σ)/5)+(12/5)*(6-12*σ)) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_zeta_5 σ t hlo _hhi htlo hthi

-- EnergyClauseThreeZetaCertificates: energyClauseThree_zeta_6
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (_hhi : σ ≤ 443/586)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((5/4)*2+(1/2))*t+((3-4*σ)+(5/4)*(6-12*σ)) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_zeta_6 σ t hlo _hhi htlo hthi

-- EnergyClauseThreeZetaCertificates: energyClauseThree_zeta_7
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (_hhi : σ ≤ 443/586)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((21/8)*2+(1/4))*t+((1-2*σ)+(21/8)*(6-12*σ)) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_zeta_7 σ t hlo _hhi htlo hthi

-- EnergyClauseThreeZetaCertificates: energyClauseThree_zeta_8
example {σ t : ℝ}
    (hlo : 173/229 ≤ σ) (_hhi : σ ≤ 443/586)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((9/5)*2+(4/5))*t+(((8-16*σ)/5)+(9/5)*(6-12*σ)) ≤ energyClauseThreeThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_zeta_8 σ t hlo _hhi htlo hthi

-- EnergyClauseThreeZetaCertificates: energyClauseThree_zeta_branch
example {σ t r : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 443/586)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) (hr : r ≤ 2*t-12*(σ-1/2)) (i : Fin 9) :
    heathBrownNineBranch σ t r 1 i ≤ energyClauseThreeRate σ*t :=
  @TaoTrudgianYang2025.energyClauseThree_zeta_branch σ t r hlo hhi htlo hthi hr i

-- EnergyClauseThree: InZetaLargeValueEnergyRegion.energyClauseThree
example
    {σ τ ρ e s : ℝ} (h : InZetaLargeValueEnergyRegion σ τ ρ e s)
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 443/586) (htlo : 3/2 ≤ τ) (hthi : τ ≤ 2) :
    e ≤ energyClauseThreeRate σ*τ :=
  @TaoTrudgianYang2025.InZetaLargeValueEnergyRegion.energyClauseThree σ τ ρ e s h hlo hhi htlo hthi

-- EnergyClauseThree: energyClauseThree_short_zeta
example {σ τ : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 443/586) (htlo : 1 ≤ τ) (hthi : τ ≤ 2) :
    IsZetaLargeValueEnergyBound σ τ (energyClauseThreeRate σ*τ) :=
  @TaoTrudgianYang2025.energyClauseThree_short_zeta σ τ hlo hhi htlo hthi

-- EnergyClauseThree: energyClauseThree
example {σ : ℝ} (hlo : 173/229 ≤ σ) (hhi : σ ≤ 443/586) :
    IsZeroDensityEnergyBound σ (energyClauseThreeRate σ/(1-σ)) :=
  @TaoTrudgianYang2025.energyClauseThree σ hlo hhi

-- NewAdditiveEnergy: add_est_iii_bound
example {σ : ℝ} (hlo : 173/229 ≤ σ) (hhi : σ ≤ 443/586) :
    IsZeroDensityEnergyBound σ
      ((max ((173-270*σ)/(16*(93-125*σ)))
        (max ((653-890*σ)/(10*(93-125*σ))) ((1151-1190*σ)/(20*(15*σ-2)))))/(1-σ)) :=
  @TaoTrudgianYang2025.add_est_iii_bound σ hlo hhi

-- NewAdditiveEnergy: add_est_iii
example {σ : ℝ} (hlo : 173/229 ≤ σ) (hhi : σ ≤ 443/586) :
    zeroDensityEnergyExponent σ*((1-σ : ℝ) : EReal) ≤
      ((max ((173-270*σ)/(16*(93-125*σ)))
        (max ((653-890*σ)/(10*(93-125*σ))) ((1151-1190*σ)/(20*(15*σ-2)))) : ℝ) : EReal) :=
  @TaoTrudgianYang2025.add_est_iii σ hlo hhi

-- NewAdditiveEnergy: add_est_iii_zero_energy
example {σ : ℝ} (hlo : 173/229 ≤ σ) (hhi : σ ≤ 443/586) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ T : ℝ, C ≤ T →
        (zeroAdditiveEnergy (σ-δ) T : ℝ) ≤ C*T^
          ((max ((173-270*σ)/(16*(93-125*σ)))
        (max ((653-890*σ)/(10*(93-125*σ))) ((1151-1190*σ)/(20*(15*σ-2)))))+ε) :=
  @TaoTrudgianYang2025.add_est_iii_zero_energy σ hlo hhi

-- Both closed sigma endpoints are retained by the final bound.
example :
    IsZeroDensityEnergyBound (173/229)
      (energyClauseThreeRate (173/229)/(1-(173/229))) :=
  energyClauseThree (by norm_num) (by norm_num)

example :
    IsZeroDensityEnergyBound (443/586)
      (energyClauseThreeRate (443/586)/(1-(443/586))) :=
  energyClauseThree (by norm_num) (by norm_num)

-- The sigma split belongs to both closed numerical subranges.
example (t : ℝ) :
    t+50/13-(76/13)*(241/319) = t+78-104*(241/319) := by ring

-- The printed first two fractions agree at the stated crossover.
example :
    energyClauseThreeFirstRate (4359/5770) =
      energyClauseThreeSecondRate (4359/5770) := by
  norm_num [energyClauseThreeFirstRate,energyClauseThreeSecondRate]

-- Both negative printed denominators are handled with their signs.
example {σ : ℝ} (hlo : 173/229 ≤ σ) :
    93-125*σ < 0 ∧ 0 < 15*σ-2 := by constructor <;> linarith

example {σ : ℝ} (hlo : 173/229 ≤ σ) (hhi : σ ≤ 241/319) :
    1 ≤ 102*σ-76 ∧ 102*σ-76 ≤ 100*σ-372/5 ∧
      100*σ-372/5 ≤ 6/5 := by
  constructor
  · linarith
  constructor <;> linarith

example {σ : ℝ} (hlo : 241/319 ≤ σ) (hhi : σ ≤ 443/586) :
    1 ≤ (50*σ-24)/13 ∧ (50*σ-24)/13 ≤ 8*(15*σ-2)/65 ∧
      8*(15*σ-2)/65 ≤ 6/5 := by
  constructor
  · linarith
  constructor <;> linarith

-- The original height-three boundary has an actual general consumer.
example {σ ρ e : ℝ} (h : InCardinalityEnergyRegion σ 3 ρ e)
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 443/586) :
    e ≤ energyClauseThreeRate σ*3 :=
  h.energyClauseThree_general hlo hhi (by norm_num) (by norm_num)

example {σ : ℝ} (hlo : 173/229 ≤ σ) (hhi : σ ≤ 443/586) :
    IsLargeValueEnergyBound σ 4 (energyClauseThreeRate σ*4) :=
  energyClauseThree_general_bound hlo hhi (by norm_num) (by norm_num)

-- Cancellation supplies height one, with no short-zeta assumption.
example {σ : ℝ} (hlo : 173/229 ≤ σ) (hhi : σ ≤ 443/586) :
    IsZetaLargeValueEnergyBound σ 1 (energyClauseThreeRate σ*1) :=
  energyClauseThree_short_zeta hlo hhi (by norm_num) (by norm_num)

-- The shared cancellation/moment boundary is included.
example {σ : ℝ} (hlo : 173/229 ≤ σ) (hhi : σ ≤ 443/586) :
    IsZetaLargeValueEnergyBound σ (3/2) (energyClauseThreeRate σ*(3/2)) :=
  energyClauseThree_short_zeta hlo hhi (by norm_num) (by norm_num)

example {σ : ℝ} (hlo : 173/229 ≤ σ) (hhi : σ ≤ 443/586) :
    IsZetaLargeValueEnergyBound σ 2 (energyClauseThreeRate σ*2) :=
  energyClauseThree_short_zeta hlo hhi (by norm_num) (by norm_num)

-- The cardinality and energy applications are independent actual witnesses.
example {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e) :
    ρ/3 ≤ jutilaLargeValueExponent 13 σ (τ/3) ∧
      ∃ i : Fin 9, e/2 ≤ heathBrownNineBranch σ (τ/2) (ρ/2) (1/2) i := by
  constructor
  · exact h.jutila_cardinality_powered 3 13 (by norm_num) (by norm_num)
  · simpa using h.heathBrown_nine_branches_powered 2 1 (by norm_num) (by norm_num)

-- General-region membership is the real upstream object.
example {σ τ ρ e s : ℝ} (h : InLargeValueEnergyRegion σ τ ρ e s)
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 443/586) (htlo : 2 ≤ τ) (hthi : τ ≤ 4) :
    e ≤ energyClauseThreeRate σ*τ :=
  (show InCardinalityEnergyRegion σ τ ρ e from ⟨s,h⟩).energyClauseThree_general
    hlo hhi htlo hthi

end AddEstThirdRegression

namespace AddEstFourthRegression

open TaoTrudgianYang2025

-- EnergyClauseFourCaps: jutila_twelve_formula
example (σ t : ℝ) :
    jutilaLargeValueExponent 12 σ t =
      max (2-2*σ) (max (t+23/6-(35/6)*σ) (t+72-96*σ)) :=
  @TaoTrudgianYang2025.jutila_twelve_formula σ t

-- EnergyClauseFourCaps: InCardinalityEnergyRegion.jutila_twelve_cardinality_powered
example
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (q : ℕ) (hq : 1 ≤ q) :
    ρ/q ≤ max (2-2*σ) (max (τ/q+23/6-(35/6)*σ) (τ/q+72-96*σ)) :=
  @TaoTrudgianYang2025.InCardinalityEnergyRegion.jutila_twelve_cardinality_powered σ τ ρ e h q hq

-- EnergyClauseFourCaps: jutila_twelve_low_sigma
example {σ t : ℝ} (hσ : σ ≤ 409/541) :
    max (2-2*σ) (max (t+23/6-(35/6)*σ) (t+72-96*σ)) =
      max (2-2*σ) (t+72-96*σ) :=
  @TaoTrudgianYang2025.jutila_twelve_low_sigma σ t hσ

-- EnergyClauseFourCaps: jutila_twelve_high_sigma
example {σ t : ℝ} (hσ : 409/541 ≤ σ) :
    max (2-2*σ) (max (t+23/6-(35/6)*σ) (t+72-96*σ)) =
      max (2-2*σ) (t+23/6-(35/6)*σ) :=
  @TaoTrudgianYang2025.jutila_twelve_high_sigma σ t hσ

-- EnergyClauseFourCaps: jutila_twelve_at_most_one
example {σ t : ℝ}
    (hσ : 443/586 ≤ σ) (ht : t ≤ 1) :
    max (2-2*σ) (max (t+23/6-(35/6)*σ) (t+72-96*σ)) = 2-2*σ :=
  @TaoTrudgianYang2025.jutila_twelve_at_most_one σ t hσ ht

-- EnergyClauseFourCaps: InCardinalityEnergyRegion.energyClauseFour_cardinality_caps
example
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493)
    (q : ℕ) (hq : q=2 ∨ q=3) (htlo : (q : ℝ) ≤ τ) (hthi : τ ≤ q+1) :
    1 ≤ τ/q ∧ τ/q ≤ 3/2 ∧
      ρ/q ≤ max (2-2*σ) (max (τ/q+23/6-(35/6)*σ) (τ/q+72-96*σ)) ∧
      ρ/q ≤ max (18/5-4*σ) (12/5-4*σ+τ/q) ∧
      ρ/q ≤ 3-3*σ :=
  @TaoTrudgianYang2025.InCardinalityEnergyRegion.energyClauseFour_cardinality_caps σ τ ρ e h hlo hhi q hq htlo hthi

-- EnergyClauseFourRates: energyClauseFourRate_eq_printed
example (σ : ℝ) :
    energyClauseFourRate σ =
      max ((593-810*σ)/(5*(171-230*σ))) (4*(266-275*σ)/(5*(55*σ-7))) :=
  @TaoTrudgianYang2025.energyClauseFourRate_eq_printed σ

-- EnergyClauseFourRates: energyClauseFourFirstRate_le
example (σ : ℝ) :
    energyClauseFourFirstRate σ ≤ energyClauseFourRate σ :=
  @TaoTrudgianYang2025.energyClauseFourFirstRate_le σ

-- EnergyClauseFourRates: energyClauseFourSecondRate_le
example (σ : ℝ) :
    energyClauseFourSecondRate σ ≤ energyClauseFourRate σ :=
  @TaoTrudgianYang2025.energyClauseFourSecondRate_le σ

-- EnergyClauseFourRates: energyClauseFourRate_pos
example {σ : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493) :
    0 < energyClauseFourRate σ :=
  @TaoTrudgianYang2025.energyClauseFourRate_pos σ hlo hhi

-- EnergyClauseFourLowCertificates: energyClauseFour_low_0_0
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 409/541)
    (htlo : 1 ≤ t) (hthi : t ≤ 94*σ-70) :
    ((1)*(0)+(0))*t+((4-4*σ)*(2/3)+(1)*(2-2*σ)) ≤ energyClauseFourFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_low_0_0 σ t hlo hhi htlo hthi

-- EnergyClauseFourLowCertificates: energyClauseFour_low_0_1
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (_hhi : σ ≤ 409/541)
    (htlo : 94*σ-70 ≤ t) (hthi : t ≤ 92*σ-342/5) :
    ((1)*(1)+(0))*t+((4-4*σ)*(2/3)+(1)*(72-96*σ)) ≤ energyClauseFourFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_low_0_1 σ t hlo _hhi htlo hthi

-- EnergyClauseFourLowCertificates: energyClauseFour_low_0_2
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 409/541)
    (htlo : 92*σ-342/5 ≤ t) (hthi : t ≤ 6/5) :
    ((1)*(0)+(0))*t+((4-4*σ)*(2/3)+(1)*(18/5-4*σ)) ≤ energyClauseFourFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_low_0_2 σ t hlo hhi htlo hthi

-- EnergyClauseFourLowCertificates: energyClauseFour_low_1_0
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 409/541)
    (htlo : 1 ≤ t) (hthi : t ≤ 94*σ-70) :
    ((5/2)*(0)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(2-2*σ)) ≤ energyClauseFourFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_low_1_0 σ t hlo hhi htlo hthi

-- EnergyClauseFourLowCertificates: energyClauseFour_low_1_1
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (_hhi : σ ≤ 409/541)
    (htlo : 94*σ-70 ≤ t) (hthi : t ≤ 92*σ-342/5) :
    ((5/2)*(1)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(72-96*σ)) ≤ energyClauseFourFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_low_1_1 σ t hlo _hhi htlo hthi

-- EnergyClauseFourLowCertificates: energyClauseFour_low_1_2
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 409/541)
    (htlo : 92*σ-342/5 ≤ t) (hthi : t ≤ 6/5) :
    ((5/2)*(0)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(18/5-4*σ)) ≤ energyClauseFourFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_low_1_2 σ t hlo hhi htlo hthi

-- EnergyClauseFourLowCertificates: energyClauseFour_low_2_0
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 409/541)
    (htlo : 1 ≤ t) (hthi : t ≤ 94*σ-70) :
    ((8/5)*(0)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(2-2*σ)) ≤ energyClauseFourFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_low_2_0 σ t hlo hhi htlo hthi

-- EnergyClauseFourLowCertificates: energyClauseFour_low_2_1
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (_hhi : σ ≤ 409/541)
    (htlo : 94*σ-70 ≤ t) (hthi : t ≤ 92*σ-342/5) :
    ((8/5)*(1)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(72-96*σ)) ≤ energyClauseFourFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_low_2_1 σ t hlo _hhi htlo hthi

-- EnergyClauseFourLowCertificates: energyClauseFour_low_2_2
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 409/541)
    (htlo : 92*σ-342/5 ≤ t) (hthi : t ≤ 6/5) :
    ((8/5)*(0)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(18/5-4*σ)) ≤ energyClauseFourFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_low_2_2 σ t hlo hhi htlo hthi

-- EnergyClauseFourLowCertificates: energyClauseFour_low_3_0
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 409/541)
    (htlo : 1 ≤ t) (hthi : t ≤ 94*σ-70) :
    ((2)*(0)+(0))*t+((3-4*σ)*(1/2)+(2)*(2-2*σ)) ≤ energyClauseFourFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_low_3_0 σ t hlo hhi htlo hthi

-- EnergyClauseFourLowCertificates: energyClauseFour_low_3_1
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (_hhi : σ ≤ 409/541)
    (htlo : 94*σ-70 ≤ t) (hthi : t ≤ 92*σ-342/5) :
    ((2)*(1)+(0))*t+((3-4*σ)*(1/2)+(2)*(72-96*σ)) ≤ energyClauseFourFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_low_3_1 σ t hlo _hhi htlo hthi

-- EnergyClauseFourLowCertificates: energyClauseFour_low_3_2
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 409/541)
    (htlo : 92*σ-342/5 ≤ t) (hthi : t ≤ 6/5) :
    ((2)*(0)+(0))*t+((3-4*σ)*(1/2)+(2)*(18/5-4*σ)) ≤ energyClauseFourFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_low_3_2 σ t hlo hhi htlo hthi

-- EnergyClauseFourLowCertificates: energyClauseFour_low_4_0
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 409/541)
    (htlo : 1 ≤ t) (hthi : t ≤ 94*σ-70) :
    ((3)*(0)+(0))*t+((1-2*σ)*(1/2)+(3)*(2-2*σ)) ≤ energyClauseFourFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_low_4_0 σ t hlo hhi htlo hthi

-- EnergyClauseFourLowCertificates: energyClauseFour_low_4_1
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (_hhi : σ ≤ 409/541)
    (htlo : 94*σ-70 ≤ t) (hthi : t ≤ 92*σ-342/5) :
    ((3)*(1)+(0))*t+((1-2*σ)*(1/2)+(3)*(72-96*σ)) ≤ energyClauseFourFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_low_4_1 σ t hlo _hhi htlo hthi

-- EnergyClauseFourLowCertificates: energyClauseFour_low_4_2
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 409/541)
    (htlo : 92*σ-342/5 ≤ t) (hthi : t ≤ 6/5) :
    ((3)*(0)+(0))*t+((1-2*σ)*(1/2)+(3)*(18/5-4*σ)) ≤ energyClauseFourFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_low_4_2 σ t hlo hhi htlo hthi

-- EnergyClauseFourLowCertificates: energyClauseFour_low_5_0
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 409/541)
    (htlo : 1 ≤ t) (hthi : t ≤ 94*σ-70) :
    ((12/5)*(0)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(2-2*σ)) ≤ energyClauseFourFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_low_5_0 σ t hlo hhi htlo hthi

-- EnergyClauseFourLowCertificates: energyClauseFour_low_5_1
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (_hhi : σ ≤ 409/541)
    (htlo : 94*σ-70 ≤ t) (hthi : t ≤ 92*σ-342/5) :
    ((12/5)*(1)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(72-96*σ)) ≤ energyClauseFourFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_low_5_1 σ t hlo _hhi htlo hthi

-- EnergyClauseFourLowCertificates: energyClauseFour_low_5_2
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 409/541)
    (htlo : 92*σ-342/5 ≤ t) (hthi : t ≤ 6/5) :
    ((12/5)*(0)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(18/5-4*σ)) ≤ energyClauseFourFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_low_5_2 σ t hlo hhi htlo hthi

-- EnergyClauseFourLowCertificates: energyClauseFour_low_6_0
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 409/541)
    (htlo : 1 ≤ t) (hthi : t ≤ 94*σ-70) :
    ((5/4)*(0)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(2-2*σ)) ≤ energyClauseFourFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_low_6_0 σ t hlo hhi htlo hthi

-- EnergyClauseFourLowCertificates: energyClauseFour_low_6_1
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (_hhi : σ ≤ 409/541)
    (htlo : 94*σ-70 ≤ t) (hthi : t ≤ 92*σ-342/5) :
    ((5/4)*(1)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(72-96*σ)) ≤ energyClauseFourFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_low_6_1 σ t hlo _hhi htlo hthi

-- EnergyClauseFourLowCertificates: energyClauseFour_low_6_2
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 409/541)
    (htlo : 92*σ-342/5 ≤ t) (hthi : t ≤ 6/5) :
    ((5/4)*(0)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(18/5-4*σ)) ≤ energyClauseFourFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_low_6_2 σ t hlo hhi htlo hthi

-- EnergyClauseFourLowCertificates: energyClauseFour_low_7_0
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 409/541)
    (htlo : 1 ≤ t) (hthi : t ≤ 94*σ-70) :
    ((21/8)*(0)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(2-2*σ)) ≤ energyClauseFourFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_low_7_0 σ t hlo hhi htlo hthi

-- EnergyClauseFourLowCertificates: energyClauseFour_low_7_1
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (_hhi : σ ≤ 409/541)
    (htlo : 94*σ-70 ≤ t) (hthi : t ≤ 92*σ-342/5) :
    ((21/8)*(1)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(72-96*σ)) ≤ energyClauseFourFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_low_7_1 σ t hlo _hhi htlo hthi

-- EnergyClauseFourLowCertificates: energyClauseFour_low_7_2
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 409/541)
    (htlo : 92*σ-342/5 ≤ t) (hthi : t ≤ 6/5) :
    ((21/8)*(0)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(18/5-4*σ)) ≤ energyClauseFourFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_low_7_2 σ t hlo hhi htlo hthi

-- EnergyClauseFourLowCertificates: energyClauseFour_low_8_0
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 409/541)
    (htlo : 1 ≤ t) (hthi : t ≤ 94*σ-70) :
    ((9/5)*(0)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(2-2*σ)) ≤ energyClauseFourFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_low_8_0 σ t hlo hhi htlo hthi

-- EnergyClauseFourLowCertificates: energyClauseFour_low_8_1
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 409/541)
    (htlo : 94*σ-70 ≤ t) (hthi : t ≤ 92*σ-342/5) :
    ((9/5)*(1)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(72-96*σ)) ≤ energyClauseFourFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_low_8_1 σ t hlo hhi htlo hthi

-- EnergyClauseFourLowCertificates: energyClauseFour_low_8_2
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 409/541)
    (htlo : 92*σ-342/5 ≤ t) (hthi : t ≤ 6/5) :
    ((9/5)*(0)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(18/5-4*σ)) ≤ energyClauseFourFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_low_8_2 σ t hlo hhi htlo hthi

-- EnergyClauseFourHighCertificates: energyClauseFour_high_0_0
example {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : 1 ≤ t) (hthi : t ≤ (23*σ-11)/6) :
    ((1)*(0)+(0))*t+((4-4*σ)*(2/3)+(1)*(2-2*σ)) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_high_0_0 σ t hlo hhi htlo hthi

-- EnergyClauseFourHighCertificates: energyClauseFour_high_0_1
example {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : (23*σ-11)/6 ≤ t) (hthi : t ≤ 11*σ/6-7/30) :
    ((1)*(1)+(0))*t+((4-4*σ)*(2/3)+(1)*(23/6-(35/6)*σ)) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_high_0_1 σ t hlo hhi htlo hthi

-- EnergyClauseFourHighCertificates: energyClauseFour_high_0_2
example {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : 11*σ/6-7/30 ≤ t) (hthi : t ≤ 6/5) :
    ((1)*(0)+(0))*t+((4-4*σ)*(2/3)+(1)*(18/5-4*σ)) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_high_0_2 σ t hlo hhi htlo hthi

-- EnergyClauseFourHighCertificates: energyClauseFour_high_1_0
example {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : 1 ≤ t) (hthi : t ≤ (23*σ-11)/6) :
    ((5/2)*(0)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(2-2*σ)) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_high_1_0 σ t hlo hhi htlo hthi

-- EnergyClauseFourHighCertificates: energyClauseFour_high_1_1
example {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : (23*σ-11)/6 ≤ t) (hthi : t ≤ 11*σ/6-7/30) :
    ((5/2)*(1)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(23/6-(35/6)*σ)) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_high_1_1 σ t hlo hhi htlo hthi

-- EnergyClauseFourHighCertificates: energyClauseFour_high_1_2
example {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (_hhi : σ ≤ 373/493)
    (htlo : 11*σ/6-7/30 ≤ t) (hthi : t ≤ 6/5) :
    ((5/2)*(0)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(18/5-4*σ)) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_high_1_2 σ t hlo _hhi htlo hthi

-- EnergyClauseFourHighCertificates: energyClauseFour_high_2_0
example {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : 1 ≤ t) (hthi : t ≤ (23*σ-11)/6) :
    ((8/5)*(0)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(2-2*σ)) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_high_2_0 σ t hlo hhi htlo hthi

-- EnergyClauseFourHighCertificates: energyClauseFour_high_2_1
example {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : (23*σ-11)/6 ≤ t) (hthi : t ≤ 11*σ/6-7/30) :
    ((8/5)*(1)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(23/6-(35/6)*σ)) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_high_2_1 σ t hlo hhi htlo hthi

-- EnergyClauseFourHighCertificates: energyClauseFour_high_2_2
example {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : 11*σ/6-7/30 ≤ t) (hthi : t ≤ 6/5) :
    ((8/5)*(0)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(18/5-4*σ)) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_high_2_2 σ t hlo hhi htlo hthi

-- EnergyClauseFourHighCertificates: energyClauseFour_high_3_0
example {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : 1 ≤ t) (hthi : t ≤ (23*σ-11)/6) :
    ((2)*(0)+(0))*t+((3-4*σ)*(1/2)+(2)*(2-2*σ)) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_high_3_0 σ t hlo hhi htlo hthi

-- EnergyClauseFourHighCertificates: energyClauseFour_high_3_1
example {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : (23*σ-11)/6 ≤ t) (hthi : t ≤ 11*σ/6-7/30) :
    ((2)*(1)+(0))*t+((3-4*σ)*(1/2)+(2)*(23/6-(35/6)*σ)) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_high_3_1 σ t hlo hhi htlo hthi

-- EnergyClauseFourHighCertificates: energyClauseFour_high_3_2
example {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (_hhi : σ ≤ 373/493)
    (htlo : 11*σ/6-7/30 ≤ t) (hthi : t ≤ 6/5) :
    ((2)*(0)+(0))*t+((3-4*σ)*(1/2)+(2)*(18/5-4*σ)) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_high_3_2 σ t hlo _hhi htlo hthi

-- EnergyClauseFourHighCertificates: energyClauseFour_high_4_0
example {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : 1 ≤ t) (hthi : t ≤ (23*σ-11)/6) :
    ((3)*(0)+(0))*t+((1-2*σ)*(1/2)+(3)*(2-2*σ)) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_high_4_0 σ t hlo hhi htlo hthi

-- EnergyClauseFourHighCertificates: energyClauseFour_high_4_1
example {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : (23*σ-11)/6 ≤ t) (hthi : t ≤ 11*σ/6-7/30) :
    ((3)*(1)+(0))*t+((1-2*σ)*(1/2)+(3)*(23/6-(35/6)*σ)) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_high_4_1 σ t hlo hhi htlo hthi

-- EnergyClauseFourHighCertificates: energyClauseFour_high_4_2
example {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (_hhi : σ ≤ 373/493)
    (htlo : 11*σ/6-7/30 ≤ t) (hthi : t ≤ 6/5) :
    ((3)*(0)+(0))*t+((1-2*σ)*(1/2)+(3)*(18/5-4*σ)) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_high_4_2 σ t hlo _hhi htlo hthi

-- EnergyClauseFourHighCertificates: energyClauseFour_high_5_0
example {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : 1 ≤ t) (hthi : t ≤ (23*σ-11)/6) :
    ((12/5)*(0)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(2-2*σ)) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_high_5_0 σ t hlo hhi htlo hthi

-- EnergyClauseFourHighCertificates: energyClauseFour_high_5_1
example {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : (23*σ-11)/6 ≤ t) (hthi : t ≤ 11*σ/6-7/30) :
    ((12/5)*(1)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(23/6-(35/6)*σ)) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_high_5_1 σ t hlo hhi htlo hthi

-- EnergyClauseFourHighCertificates: energyClauseFour_high_5_2
example {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (_hhi : σ ≤ 373/493)
    (htlo : 11*σ/6-7/30 ≤ t) (hthi : t ≤ 6/5) :
    ((12/5)*(0)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(18/5-4*σ)) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_high_5_2 σ t hlo _hhi htlo hthi

-- EnergyClauseFourHighCertificates: energyClauseFour_high_6_0
example {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : 1 ≤ t) (hthi : t ≤ (23*σ-11)/6) :
    ((5/4)*(0)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(2-2*σ)) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_high_6_0 σ t hlo hhi htlo hthi

-- EnergyClauseFourHighCertificates: energyClauseFour_high_6_1
example {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : (23*σ-11)/6 ≤ t) (hthi : t ≤ 11*σ/6-7/30) :
    ((5/4)*(1)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(23/6-(35/6)*σ)) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_high_6_1 σ t hlo hhi htlo hthi

-- EnergyClauseFourHighCertificates: energyClauseFour_high_6_2
example {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : 11*σ/6-7/30 ≤ t) (hthi : t ≤ 6/5) :
    ((5/4)*(0)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(18/5-4*σ)) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_high_6_2 σ t hlo hhi htlo hthi

-- EnergyClauseFourHighCertificates: energyClauseFour_high_7_0
example {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : 1 ≤ t) (hthi : t ≤ (23*σ-11)/6) :
    ((21/8)*(0)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(2-2*σ)) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_high_7_0 σ t hlo hhi htlo hthi

-- EnergyClauseFourHighCertificates: energyClauseFour_high_7_1
example {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : (23*σ-11)/6 ≤ t) (hthi : t ≤ 11*σ/6-7/30) :
    ((21/8)*(1)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(23/6-(35/6)*σ)) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_high_7_1 σ t hlo hhi htlo hthi

-- EnergyClauseFourHighCertificates: energyClauseFour_high_7_2
example {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (_hhi : σ ≤ 373/493)
    (htlo : 11*σ/6-7/30 ≤ t) (hthi : t ≤ 6/5) :
    ((21/8)*(0)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(18/5-4*σ)) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_high_7_2 σ t hlo _hhi htlo hthi

-- EnergyClauseFourHighCertificates: energyClauseFour_high_8_0
example {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : 1 ≤ t) (hthi : t ≤ (23*σ-11)/6) :
    ((9/5)*(0)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(2-2*σ)) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_high_8_0 σ t hlo hhi htlo hthi

-- EnergyClauseFourHighCertificates: energyClauseFour_high_8_1
example {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : (23*σ-11)/6 ≤ t) (hthi : t ≤ 11*σ/6-7/30) :
    ((9/5)*(1)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(23/6-(35/6)*σ)) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_high_8_1 σ t hlo hhi htlo hthi

-- EnergyClauseFourHighCertificates: energyClauseFour_high_8_2
example {σ t : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : 11*σ/6-7/30 ≤ t) (hthi : t ≤ 6/5) :
    ((9/5)*(0)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(18/5-4*σ)) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_high_8_2 σ t hlo hhi htlo hthi

-- EnergyClauseFourTallCertificates: energyClauseFour_tall_0_0
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : 6/5 ≤ t) (hthi : t ≤ σ+3/5) :
    (1)*t+((12/5-4*σ)+4-4*σ) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_tall_0_0 σ t hlo hhi htlo hthi

-- EnergyClauseFourTallCertificates: energyClauseFour_tall_0_1
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : σ+3/5 ≤ t) (hthi : t ≤ 3/2) :
    (0)*t+((3-3*σ)+4-4*σ) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_tall_0_1 σ t hlo hhi htlo hthi

-- EnergyClauseFourTallCertificates: energyClauseFour_tall_1_0
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : 6/5 ≤ t) (hthi : t ≤ σ+3/5) :
    ((5/2)*(1))*t+((3-4*σ+5*(12/5-4*σ))/2) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_tall_1_0 σ t hlo hhi htlo hthi

-- EnergyClauseFourTallCertificates: energyClauseFour_tall_1_1
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : σ+3/5 ≤ t) (hthi : t ≤ 3/2) :
    ((5/2)*(0))*t+((3-4*σ+5*(3-3*σ))/2) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_tall_1_1 σ t hlo hhi htlo hthi

-- EnergyClauseFourBranches: energyClauseFour_low_short_branch
example {σ t r a e : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 409/541)
    (htlo : 1 ≤ t) (hthi : t ≤ 6/5)
    (halo : 1/2 ≤ a) (hahi : a ≤ 2/3)
    (hj : r ≤ max (2-2*σ) (t+(72-96*σ))) (hg : r ≤ 18/5-4*σ)
    (i : Fin 9) (hb : e ≤ heathBrownNineBranch σ t r a i) :
    e ≤ energyClauseFourRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_low_short_branch σ t r a e hlo hhi htlo hthi halo hahi hj hg i hb

-- EnergyClauseFourBranches: energyClauseFour_high_short_branch
example {σ t r a e : ℝ}
    (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : 1 ≤ t) (hthi : t ≤ 6/5)
    (halo : 1/2 ≤ a) (hahi : a ≤ 2/3)
    (hj : r ≤ max (2-2*σ) (t+(23/6-(35/6)*σ))) (hg : r ≤ 18/5-4*σ)
    (i : Fin 9) (hb : e ≤ heathBrownNineBranch σ t r a i) :
    e ≤ energyClauseFourRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_high_short_branch σ t r a e hlo hhi htlo hthi halo hahi hj hg i hb

-- EnergyClauseFourGeneral: energyClauseFour_tall_bound
example {σ t r : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : 6/5 ≤ t) (hthi : t ≤ 3/2)
    (hg : r ≤ max (18/5-4*σ) (12/5-4*σ+t)) (hcap : r ≤ 3-3*σ) :
    max (r+4-4*σ) ((3-4*σ+5*r)/2) ≤ energyClauseFourRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_tall_bound σ t r hlo hhi htlo hthi hg hcap

-- EnergyClauseFourGeneral: InCardinalityEnergyRegion.energyClauseFour_general
example
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493) (htlo : 2 ≤ τ) (hthi : τ ≤ 4) :
    e ≤ energyClauseFourRate σ*τ :=
  @TaoTrudgianYang2025.InCardinalityEnergyRegion.energyClauseFour_general σ τ ρ e h hlo hhi htlo hthi

-- EnergyClauseFourGeneral: energyClauseFour_general_bound
example {σ τ : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493) (htlo : 2 ≤ τ) (hthi : τ ≤ 4) :
    IsLargeValueEnergyBound σ τ (energyClauseFourRate σ*τ) :=
  @TaoTrudgianYang2025.energyClauseFour_general_bound σ τ hlo hhi htlo hthi

-- EnergyClauseFourZetaCertificates: energyClauseFour_zeta_0
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (_hhi : σ ≤ 373/493)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((1)*2+(0))*t+((4-4*σ)+(1)*(6-12*σ)) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_zeta_0 σ t hlo _hhi htlo hthi

-- EnergyClauseFourZetaCertificates: energyClauseFour_zeta_1
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (_hhi : σ ≤ 373/493)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((5/2)*2+(0))*t+(((3-4*σ)/2)+(5/2)*(6-12*σ)) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_zeta_1 σ t hlo _hhi htlo hthi

-- EnergyClauseFourZetaCertificates: energyClauseFour_zeta_2
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (_hhi : σ ≤ 373/493)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((8/5)*2+(2/5))*t+(((12-16*σ)/5)+(8/5)*(6-12*σ)) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_zeta_2 σ t hlo _hhi htlo hthi

-- EnergyClauseFourZetaCertificates: energyClauseFour_zeta_3
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (_hhi : σ ≤ 373/493)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((2)*2+(0))*t+((3-4*σ)+(2)*(6-12*σ)) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_zeta_3 σ t hlo _hhi htlo hthi

-- EnergyClauseFourZetaCertificates: energyClauseFour_zeta_4
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (_hhi : σ ≤ 373/493)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((3)*2+(0))*t+((1-2*σ)+(3)*(6-12*σ)) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_zeta_4 σ t hlo _hhi htlo hthi

-- EnergyClauseFourZetaCertificates: energyClauseFour_zeta_5
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (_hhi : σ ≤ 373/493)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((12/5)*2+(2/5))*t+(((8-16*σ)/5)+(12/5)*(6-12*σ)) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_zeta_5 σ t hlo _hhi htlo hthi

-- EnergyClauseFourZetaCertificates: energyClauseFour_zeta_6
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (_hhi : σ ≤ 373/493)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((5/4)*2+(1/2))*t+((3-4*σ)+(5/4)*(6-12*σ)) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_zeta_6 σ t hlo _hhi htlo hthi

-- EnergyClauseFourZetaCertificates: energyClauseFour_zeta_7
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (_hhi : σ ≤ 373/493)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((21/8)*2+(1/4))*t+((1-2*σ)+(21/8)*(6-12*σ)) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_zeta_7 σ t hlo _hhi htlo hthi

-- EnergyClauseFourZetaCertificates: energyClauseFour_zeta_8
example {σ t : ℝ}
    (hlo : 443/586 ≤ σ) (_hhi : σ ≤ 373/493)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((9/5)*2+(4/5))*t+(((8-16*σ)/5)+(9/5)*(6-12*σ)) ≤ energyClauseFourSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_zeta_8 σ t hlo _hhi htlo hthi

-- EnergyClauseFourZetaCertificates: energyClauseFour_zeta_branch
example {σ t r : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) (hr : r ≤ 2*t-12*(σ-1/2)) (i : Fin 9) :
    heathBrownNineBranch σ t r 1 i ≤ energyClauseFourRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFour_zeta_branch σ t r hlo hhi htlo hthi hr i

-- EnergyClauseFour: InZetaLargeValueEnergyRegion.energyClauseFour
example
    {σ τ ρ e s : ℝ} (h : InZetaLargeValueEnergyRegion σ τ ρ e s)
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493) (htlo : 3/2 ≤ τ) (hthi : τ ≤ 2) :
    e ≤ energyClauseFourRate σ*τ :=
  @TaoTrudgianYang2025.InZetaLargeValueEnergyRegion.energyClauseFour σ τ ρ e s h hlo hhi htlo hthi

-- EnergyClauseFour: energyClauseFour_short_zeta
example {σ τ : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493) (htlo : 1 ≤ τ) (hthi : τ ≤ 2) :
    IsZetaLargeValueEnergyBound σ τ (energyClauseFourRate σ*τ) :=
  @TaoTrudgianYang2025.energyClauseFour_short_zeta σ τ hlo hhi htlo hthi

-- EnergyClauseFour: energyClauseFour
example {σ : ℝ} (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493) :
    IsZeroDensityEnergyBound σ (energyClauseFourRate σ/(1-σ)) :=
  @TaoTrudgianYang2025.energyClauseFour σ hlo hhi

-- NewAdditiveEnergy: add_est_iv_bound
example {σ : ℝ} (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493) :
    IsZeroDensityEnergyBound σ
      ((max ((593-810*σ)/(5*(171-230*σ))) (4*(266-275*σ)/(5*(55*σ-7))))/(1-σ)) :=
  @TaoTrudgianYang2025.add_est_iv_bound σ hlo hhi

-- NewAdditiveEnergy: add_est_iv
example {σ : ℝ} (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493) :
    zeroDensityEnergyExponent σ*((1-σ : ℝ) : EReal) ≤
      ((max ((593-810*σ)/(5*(171-230*σ))) (4*(266-275*σ)/(5*(55*σ-7))) : ℝ) : EReal) :=
  @TaoTrudgianYang2025.add_est_iv σ hlo hhi

-- NewAdditiveEnergy: add_est_iv_zero_energy
example {σ : ℝ} (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ T : ℝ, C ≤ T →
        (zeroAdditiveEnergy (σ-δ) T : ℝ) ≤ C*T^
          ((max ((593-810*σ)/(5*(171-230*σ))) (4*(266-275*σ)/(5*(55*σ-7))))+ε) :=
  @TaoTrudgianYang2025.add_est_iv_zero_energy σ hlo hhi

-- Both exact closed sigma endpoints are accepted.
example :
    IsZeroDensityEnergyBound (443/586)
      (energyClauseFourRate (443/586)/(1-(443/586))) :=
  energyClauseFour (by norm_num) (by norm_num)

example :
    IsZeroDensityEnergyBound (373/493)
      (energyClauseFourRate (373/493)/(1-(373/493))) :=
  energyClauseFour (by norm_num) (by norm_num)

-- The two Jutila affine terms agree at the source sigma split.
example (t : ℝ) :
    t+23/6-(35/6)*(409/541) = t+72-96*(409/541) := by ring

-- Both source rates agree at the shared split.
example :
    energyClauseFourFirstRate (409/541) =
      energyClauseFourSecondRate (409/541) := by
  norm_num [energyClauseFourFirstRate,energyClauseFourSecondRate]

-- The signs of the printed denominators are explicit.
example {σ : ℝ} (hlo : 443/586 ≤ σ) :
    171-230*σ < 0 ∧ 0 < 55*σ-7 := by constructor <;> linarith

example {σ : ℝ} (hlo : 443/586 ≤ σ) (hhi : σ ≤ 409/541) :
    1 ≤ 94*σ-70 ∧ 94*σ-70 ≤ 92*σ-342/5 ∧ 92*σ-342/5 ≤ 6/5 := by
  constructor
  · linarith
  constructor <;> linarith

example {σ : ℝ} (hlo : 409/541 ≤ σ) (hhi : σ ≤ 373/493) :
    1 ≤ (23*σ-11)/6 ∧ (23*σ-11)/6 ≤ 11*σ/6-7/30 ∧
      11*σ/6-7/30 ≤ 6/5 := by
  constructor
  · linarith
  constructor <;> linarith

-- The original height-three boundary retains the actual region.
example {σ ρ e : ℝ} (h : InCardinalityEnergyRegion σ 3 ρ e)
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493) :
    e ≤ energyClauseFourRate σ*3 :=
  h.energyClauseFour_general hlo hhi (by norm_num) (by norm_num)

example {σ : ℝ} (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493) :
    IsLargeValueEnergyBound σ 4 (energyClauseFourRate σ*4) :=
  energyClauseFour_general_bound hlo hhi (by norm_num) (by norm_num)

-- The complete short-zeta interval is supplied by actual estimates.
example {σ : ℝ} (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493) :
    IsZetaLargeValueEnergyBound σ 1 (energyClauseFourRate σ*1) :=
  energyClauseFour_short_zeta hlo hhi (by norm_num) (by norm_num)

example {σ : ℝ} (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493) :
    IsZetaLargeValueEnergyBound σ (3/2) (energyClauseFourRate σ*(3/2)) :=
  energyClauseFour_short_zeta hlo hhi (by norm_num) (by norm_num)

example {σ : ℝ} (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493) :
    IsZetaLargeValueEnergyBound σ 2 (energyClauseFourRate σ*2) :=
  energyClauseFour_short_zeta hlo hhi (by norm_num) (by norm_num)

-- q=2: companion cardinality and energy witnesses are independent.
example {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e) :
    ρ/3 ≤ jutilaLargeValueExponent 12 σ (τ/3) ∧
      ∃ i : Fin 9, e/2 ≤ heathBrownNineBranch σ (τ/2) (ρ/2) (1/2) i := by
  constructor
  · exact h.jutila_cardinality_powered 3 12 (by norm_num) (by norm_num)
  · simpa using h.heathBrown_nine_branches_powered 2 1 (by norm_num) (by norm_num)

-- q=3: the second actual energy-power ratio is also covered.
example {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e) :
    ρ/4 ≤ jutilaLargeValueExponent 12 σ (τ/4) ∧
      ∃ i : Fin 9, e/3 ≤ heathBrownNineBranch σ (τ/3) (ρ/3) (2/3) i := by
  constructor
  · exact h.jutila_cardinality_powered 4 12 (by norm_num) (by norm_num)
  · simpa using h.heathBrown_nine_branches_powered 3 2 (by norm_num) (by norm_num)

-- The five-coordinate region is consumed without constraining its fifth coordinate.
example {σ τ ρ e s : ℝ} (h : InLargeValueEnergyRegion σ τ ρ e s)
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493) (htlo : 2 ≤ τ) (hthi : τ ≤ 4) :
    e ≤ energyClauseFourRate σ*τ :=
  (show InCardinalityEnergyRegion σ τ ρ e from ⟨s,h⟩).energyClauseFour_general
    hlo hhi htlo hthi

end AddEstFourthRegression

namespace AddEstFifthRegression

example (σ t : ℝ) :
    jutilaLargeValueExponent 11 σ t =
      max (2-2*σ) (max (t+42/11-(64/11)*σ) (t+66-88*σ)) :=
  @TaoTrudgianYang2025.jutila_eleven_formula σ t

example
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (q : ℕ) (hq : 1 ≤ q) :
    ρ/q ≤ max (2-2*σ) (max (τ/q+42/11-(64/11)*σ) (τ/q+66-88*σ)) :=
  @TaoTrudgianYang2025.InCardinalityEnergyRegion.jutila_eleven_cardinality_powered σ τ ρ e h q hq

example {σ t : ℝ} (hσ : σ ≤ 171/226) :
    max (2-2*σ) (max (t+42/11-(64/11)*σ) (t+66-88*σ)) =
      max (2-2*σ) (t+66-88*σ) :=
  @TaoTrudgianYang2025.jutila_eleven_low_sigma σ t hσ

example {σ t : ℝ} (hσ : 171/226 ≤ σ) :
    max (2-2*σ) (max (t+42/11-(64/11)*σ) (t+66-88*σ)) =
      max (2-2*σ) (t+42/11-(64/11)*σ) :=
  @TaoTrudgianYang2025.jutila_eleven_high_sigma σ t hσ

example {σ t : ℝ}
    (hσ : 373/493 ≤ σ) (ht : t ≤ 1) :
    max (2-2*σ) (max (t+42/11-(64/11)*σ) (t+66-88*σ)) = 2-2*σ :=
  @TaoTrudgianYang2025.jutila_eleven_at_most_one σ t hσ ht

example
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 103/136)
    (q : ℕ) (hq : q=2 ∨ q=3) (htlo : (q : ℝ) ≤ τ) (hthi : τ ≤ q+1) :
    1 ≤ τ/q ∧ τ/q ≤ 3/2 ∧
      ρ/q ≤ max (2-2*σ) (max (τ/q+42/11-(64/11)*σ) (τ/q+66-88*σ)) ∧
      ρ/q ≤ max (18/5-4*σ) (12/5-4*σ+τ/q) ∧
      ρ/q ≤ 3-3*σ :=
  @TaoTrudgianYang2025.InCardinalityEnergyRegion.energyClauseFive_cardinality_caps σ τ ρ e h hlo hhi q hq htlo hthi

example (σ : ℝ) :
    energyClauseFiveRate σ =
      max ((533-730*σ)/(30*(26-35*σ)))
        (max (3*(26-33*σ)/(85*σ-62)) ((174-185*σ)/(31*σ+2))) :=
  @TaoTrudgianYang2025.energyClauseFiveRate_eq_printed σ

example (σ : ℝ) :
    energyClauseFiveFirstRate σ ≤ energyClauseFiveRate σ :=
  @TaoTrudgianYang2025.energyClauseFiveFirstRate_le σ

example (σ : ℝ) :
    energyClauseFiveSecondRate σ ≤ energyClauseFiveRate σ :=
  @TaoTrudgianYang2025.energyClauseFiveSecondRate_le σ

example (σ : ℝ) :
    energyClauseFiveThirdRate σ ≤ energyClauseFiveRate σ :=
  @TaoTrudgianYang2025.energyClauseFiveThirdRate_le σ

example {σ : ℝ} (hlo : 373/493 ≤ σ) :
    0 < 30*(35*σ-26) ∧ 0 < 85*σ-62 ∧ 0 < 31*σ+2 :=
  @TaoTrudgianYang2025.energyClauseFive_printed_denominators_pos σ hlo

example {σ : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 103/136) :
    0 < energyClauseFiveRate σ :=
  @TaoTrudgianYang2025.energyClauseFiveRate_pos σ hlo hhi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 1 ≤ t) (hthi : t ≤ 86*σ-64) :
    ((1)*(0)+(0))*t+((4-4*σ)*(2/3)+(1)*(2-2*σ)) ≤ energyClauseFiveSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_low_0_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 86*σ-64 ≤ t) (hthi : t ≤ 84*σ-312/5) :
    ((1)*(1)+(0))*t+((4-4*σ)*(2/3)+(1)*(66-88*σ)) ≤ energyClauseFiveSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_low_0_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 84*σ-312/5 ≤ t) (hthi : t ≤ 6/5) :
    ((1)*(0)+(0))*t+((4-4*σ)*(2/3)+(1)*(18/5-4*σ)) ≤ energyClauseFiveSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_low_0_2 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 1 ≤ t) (hthi : t ≤ 86*σ-64) :
    ((5/2)*(0)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(2-2*σ)) ≤ energyClauseFiveSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_low_1_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 86*σ-64 ≤ t) (hthi : t ≤ 84*σ-312/5) :
    ((5/2)*(1)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(66-88*σ)) ≤ energyClauseFiveSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_low_1_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 84*σ-312/5 ≤ t) (hthi : t ≤ 6/5) :
    ((5/2)*(0)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(18/5-4*σ)) ≤ energyClauseFiveSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_low_1_2 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 1 ≤ t) (hthi : t ≤ 86*σ-64) :
    ((8/5)*(0)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(2-2*σ)) ≤ energyClauseFiveSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_low_2_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 86*σ-64 ≤ t) (hthi : t ≤ 84*σ-312/5) :
    ((8/5)*(1)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(66-88*σ)) ≤ energyClauseFiveSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_low_2_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 84*σ-312/5 ≤ t) (hthi : t ≤ 6/5) :
    ((8/5)*(0)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(18/5-4*σ)) ≤ energyClauseFiveSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_low_2_2 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 1 ≤ t) (hthi : t ≤ 86*σ-64) :
    ((2)*(0)+(0))*t+((3-4*σ)*(1/2)+(2)*(2-2*σ)) ≤ energyClauseFiveSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_low_3_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 86*σ-64 ≤ t) (hthi : t ≤ 84*σ-312/5) :
    ((2)*(1)+(0))*t+((3-4*σ)*(1/2)+(2)*(66-88*σ)) ≤ energyClauseFiveSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_low_3_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 84*σ-312/5 ≤ t) (hthi : t ≤ 6/5) :
    ((2)*(0)+(0))*t+((3-4*σ)*(1/2)+(2)*(18/5-4*σ)) ≤ energyClauseFiveSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_low_3_2 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 1 ≤ t) (hthi : t ≤ 86*σ-64) :
    ((3)*(0)+(0))*t+((1-2*σ)*(1/2)+(3)*(2-2*σ)) ≤ energyClauseFiveSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_low_4_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 86*σ-64 ≤ t) (hthi : t ≤ 84*σ-312/5) :
    ((3)*(1)+(0))*t+((1-2*σ)*(1/2)+(3)*(66-88*σ)) ≤ energyClauseFiveSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_low_4_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 84*σ-312/5 ≤ t) (hthi : t ≤ 6/5) :
    ((3)*(0)+(0))*t+((1-2*σ)*(1/2)+(3)*(18/5-4*σ)) ≤ energyClauseFiveSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_low_4_2 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 1 ≤ t) (hthi : t ≤ 86*σ-64) :
    ((12/5)*(0)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(2-2*σ)) ≤ energyClauseFiveSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_low_5_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 86*σ-64 ≤ t) (hthi : t ≤ 84*σ-312/5) :
    ((12/5)*(1)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(66-88*σ)) ≤ energyClauseFiveSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_low_5_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 84*σ-312/5 ≤ t) (hthi : t ≤ 6/5) :
    ((12/5)*(0)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(18/5-4*σ)) ≤ energyClauseFiveSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_low_5_2 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 1 ≤ t) (hthi : t ≤ 86*σ-64) :
    ((5/4)*(0)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(2-2*σ)) ≤ energyClauseFiveSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_low_6_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 86*σ-64 ≤ t) (hthi : t ≤ 84*σ-312/5) :
    ((5/4)*(1)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(66-88*σ)) ≤ energyClauseFiveSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_low_6_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 84*σ-312/5 ≤ t) (hthi : t ≤ 6/5) :
    ((5/4)*(0)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(18/5-4*σ)) ≤ energyClauseFiveSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_low_6_2 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 1 ≤ t) (hthi : t ≤ 86*σ-64) :
    ((21/8)*(0)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(2-2*σ)) ≤ energyClauseFiveSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_low_7_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 86*σ-64 ≤ t) (hthi : t ≤ 84*σ-312/5) :
    ((21/8)*(1)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(66-88*σ)) ≤ energyClauseFiveSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_low_7_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 84*σ-312/5 ≤ t) (hthi : t ≤ 6/5) :
    ((21/8)*(0)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(18/5-4*σ)) ≤ energyClauseFiveSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_low_7_2 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 1 ≤ t) (hthi : t ≤ 86*σ-64) :
    ((9/5)*(0)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(2-2*σ)) ≤ energyClauseFiveFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_low_8_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 86*σ-64 ≤ t) (hthi : t ≤ 84*σ-312/5) :
    ((9/5)*(1)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(66-88*σ)) ≤ energyClauseFiveFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_low_8_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 84*σ-312/5 ≤ t) (hthi : t ≤ 6/5) :
    ((9/5)*(0)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(18/5-4*σ)) ≤ energyClauseFiveFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_low_8_2 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : 1 ≤ t) (hthi : t ≤ (42*σ-20)/11) :
    ((1)*(0)+(0))*t+((4-4*σ)*(2/3)+(1)*(2-2*σ)) ≤ energyClauseFiveThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_high_0_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : (42*σ-20)/11 ≤ t) (hthi : t ≤ (31*σ+2)/22) :
    ((1)*(1)+(0))*t+((4-4*σ)*(2/3)+(1)*(42/11-(64/11)*σ)) ≤ energyClauseFiveThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_high_0_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : 1 ≤ t) (hthi : t ≤ (42*σ-20)/11) :
    ((5/2)*(0)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(2-2*σ)) ≤ energyClauseFiveThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_high_1_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : (42*σ-20)/11 ≤ t) (hthi : t ≤ (31*σ+2)/22) :
    ((5/2)*(1)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(42/11-(64/11)*σ)) ≤ energyClauseFiveThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_high_1_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : 1 ≤ t) (hthi : t ≤ (42*σ-20)/11) :
    ((8/5)*(0)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(2-2*σ)) ≤ energyClauseFiveThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_high_2_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : (42*σ-20)/11 ≤ t) (hthi : t ≤ (31*σ+2)/22) :
    ((8/5)*(1)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(42/11-(64/11)*σ)) ≤ energyClauseFiveThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_high_2_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : 1 ≤ t) (hthi : t ≤ (42*σ-20)/11) :
    ((2)*(0)+(0))*t+((3-4*σ)*(1/2)+(2)*(2-2*σ)) ≤ energyClauseFiveThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_high_3_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : (42*σ-20)/11 ≤ t) (hthi : t ≤ (31*σ+2)/22) :
    ((2)*(1)+(0))*t+((3-4*σ)*(1/2)+(2)*(42/11-(64/11)*σ)) ≤ energyClauseFiveThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_high_3_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : 1 ≤ t) (hthi : t ≤ (42*σ-20)/11) :
    ((3)*(0)+(0))*t+((1-2*σ)*(1/2)+(3)*(2-2*σ)) ≤ energyClauseFiveThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_high_4_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : (42*σ-20)/11 ≤ t) (hthi : t ≤ (31*σ+2)/22) :
    ((3)*(1)+(0))*t+((1-2*σ)*(1/2)+(3)*(42/11-(64/11)*σ)) ≤ energyClauseFiveThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_high_4_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : 1 ≤ t) (hthi : t ≤ (42*σ-20)/11) :
    ((12/5)*(0)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(2-2*σ)) ≤ energyClauseFiveThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_high_5_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : (42*σ-20)/11 ≤ t) (hthi : t ≤ (31*σ+2)/22) :
    ((12/5)*(1)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(42/11-(64/11)*σ)) ≤ energyClauseFiveThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_high_5_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : 1 ≤ t) (hthi : t ≤ (42*σ-20)/11) :
    ((5/4)*(0)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(2-2*σ)) ≤ energyClauseFiveThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_high_6_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : (42*σ-20)/11 ≤ t) (hthi : t ≤ (31*σ+2)/22) :
    ((5/4)*(1)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(42/11-(64/11)*σ)) ≤ energyClauseFiveThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_high_6_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : 1 ≤ t) (hthi : t ≤ (42*σ-20)/11) :
    ((21/8)*(0)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(2-2*σ)) ≤ energyClauseFiveThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_high_7_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : (42*σ-20)/11 ≤ t) (hthi : t ≤ (31*σ+2)/22) :
    ((21/8)*(1)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(42/11-(64/11)*σ)) ≤ energyClauseFiveThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_high_7_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : 1 ≤ t) (hthi : t ≤ (42*σ-20)/11) :
    ((9/5)*(0)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(2-2*σ)) ≤ energyClauseFiveThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_high_8_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : (42*σ-20)/11 ≤ t) (hthi : t ≤ (31*σ+2)/22) :
    ((9/5)*(1)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(42/11-(64/11)*σ)) ≤ energyClauseFiveThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_high_8_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : (31*σ+2)/22 ≤ t) (hthi : t ≤ 6/5) :
    (1)*t+(42/11-(64/11)*σ+4-4*σ) ≤ energyClauseFiveThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_middle_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 171/226 ≤ σ) (_hhi : σ ≤ 103/136)
    (htlo : (31*σ+2)/22 ≤ t) (hthi : t ≤ 6/5) :
    (5/2)*t+((3-4*σ+5*(42/11-(64/11)*σ))/2) ≤ energyClauseFiveThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_middle_1 σ t hlo _hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : 6/5 ≤ t) (hthi : t ≤ σ+3/5) :
    (1)*t+((12/5-4*σ)+4-4*σ) ≤ energyClauseFiveThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_tall_0_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : σ+3/5 ≤ t) (hthi : t ≤ 3/2) :
    (0)*t+((3-3*σ)+4-4*σ) ≤ energyClauseFiveThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_tall_0_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : 6/5 ≤ t) (hthi : t ≤ σ+3/5) :
    ((5/2)*(1))*t+((3-4*σ+5*(12/5-4*σ))/2) ≤ energyClauseFiveThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_tall_1_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : σ+3/5 ≤ t) (hthi : t ≤ 3/2) :
    ((5/2)*(0))*t+((3-4*σ+5*(3-3*σ))/2) ≤ energyClauseFiveThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_tall_1_1 σ t hlo hhi htlo hthi

example {σ t r a e : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226)
    (htlo : 1 ≤ t) (hthi : t ≤ 6/5)
    (halo : 1/2 ≤ a) (hahi : a ≤ 2/3)
    (hj : r ≤ max (2-2*σ) (t+(66-88*σ))) (hg : r ≤ 18/5-4*σ)
    (i : Fin 9) (hb : e ≤ heathBrownNineBranch σ t r a i) :
    e ≤ energyClauseFiveRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_low_short_branch σ t r a e hlo hhi htlo hthi halo hahi hj hg i hb

example {σ t r a e : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : 1 ≤ t) (hthi : t ≤ (31*σ+2)/22)
    (halo : 1/2 ≤ a) (hahi : a ≤ 2/3)
    (hj : r ≤ max (2-2*σ) (t+(42/11-(64/11)*σ)))
    (i : Fin 9) (hb : e ≤ heathBrownNineBranch σ t r a i) :
    e ≤ energyClauseFiveRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_high_short_branch σ t r a e hlo hhi htlo hthi halo hahi hj i hb

example {σ t r : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : 6/5 ≤ t) (hthi : t ≤ 3/2)
    (hg : r ≤ max (18/5-4*σ) (12/5-4*σ+t)) (hcap : r ≤ 3-3*σ) :
    max (r+4-4*σ) ((3-4*σ+5*r)/2) ≤ energyClauseFiveRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_tall_bound σ t r hlo hhi htlo hthi hg hcap

example {σ t r : ℝ}
    (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : (31*σ+2)/22 ≤ t) (hthi : t ≤ 6/5)
    (hj : r ≤ max (2-2*σ) (t+(42/11-(64/11)*σ))) :
    max (r+4-4*σ) ((3-4*σ+5*r)/2) ≤ energyClauseFiveRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_middle_bound σ t r hlo hhi htlo hthi hj

example
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 103/136) (htlo : 2 ≤ τ) (hthi : τ ≤ 4) :
    e ≤ energyClauseFiveRate σ*τ :=
  @TaoTrudgianYang2025.InCardinalityEnergyRegion.energyClauseFive_general σ τ ρ e h hlo hhi htlo hthi

example {σ τ : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 103/136) (htlo : 2 ≤ τ) (hthi : τ ≤ 4) :
    IsLargeValueEnergyBound σ τ (energyClauseFiveRate σ*τ) :=
  @TaoTrudgianYang2025.energyClauseFive_general_bound σ τ hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (_hhi : σ ≤ 103/136)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((1)*2+(0))*t+((4-4*σ)+(1)*(6-12*σ)) ≤ energyClauseFiveThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_zeta_0 σ t hlo _hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (_hhi : σ ≤ 103/136)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((5/2)*2+(0))*t+(((3-4*σ)/2)+(5/2)*(6-12*σ)) ≤ energyClauseFiveThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_zeta_1 σ t hlo _hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (_hhi : σ ≤ 103/136)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((8/5)*2+(2/5))*t+(((12-16*σ)/5)+(8/5)*(6-12*σ)) ≤ energyClauseFiveThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_zeta_2 σ t hlo _hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (_hhi : σ ≤ 103/136)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((2)*2+(0))*t+((3-4*σ)+(2)*(6-12*σ)) ≤ energyClauseFiveThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_zeta_3 σ t hlo _hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (_hhi : σ ≤ 103/136)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((3)*2+(0))*t+((1-2*σ)+(3)*(6-12*σ)) ≤ energyClauseFiveThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_zeta_4 σ t hlo _hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (_hhi : σ ≤ 103/136)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((12/5)*2+(2/5))*t+(((8-16*σ)/5)+(12/5)*(6-12*σ)) ≤ energyClauseFiveThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_zeta_5 σ t hlo _hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (_hhi : σ ≤ 103/136)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((5/4)*2+(1/2))*t+((3-4*σ)+(5/4)*(6-12*σ)) ≤ energyClauseFiveThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_zeta_6 σ t hlo _hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (_hhi : σ ≤ 103/136)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((21/8)*2+(1/4))*t+((1-2*σ)+(21/8)*(6-12*σ)) ≤ energyClauseFiveThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_zeta_7 σ t hlo _hhi htlo hthi

example {σ t : ℝ}
    (hlo : 373/493 ≤ σ) (_hhi : σ ≤ 103/136)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((9/5)*2+(4/5))*t+(((8-16*σ)/5)+(9/5)*(6-12*σ)) ≤ energyClauseFiveThirdRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_zeta_8 σ t hlo _hhi htlo hthi

example {σ t r : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 103/136)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) (hr : r ≤ 2*t-12*(σ-1/2)) (i : Fin 9) :
    heathBrownNineBranch σ t r 1 i ≤ energyClauseFiveRate σ*t :=
  @TaoTrudgianYang2025.energyClauseFive_zeta_branch σ t r hlo hhi htlo hthi hr i

example
    {σ τ ρ e s : ℝ} (h : InZetaLargeValueEnergyRegion σ τ ρ e s)
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 103/136) (htlo : 3/2 ≤ τ) (hthi : τ ≤ 2) :
    e ≤ energyClauseFiveRate σ*τ :=
  @TaoTrudgianYang2025.InZetaLargeValueEnergyRegion.energyClauseFive σ τ ρ e s h hlo hhi htlo hthi

example {σ τ : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 103/136) (htlo : 1 ≤ τ) (hthi : τ ≤ 2) :
    IsZetaLargeValueEnergyBound σ τ (energyClauseFiveRate σ*τ) :=
  @TaoTrudgianYang2025.energyClauseFive_short_zeta σ τ hlo hhi htlo hthi

example {σ : ℝ} (hlo : 373/493 ≤ σ) (hhi : σ ≤ 103/136) :
    IsZeroDensityEnergyBound σ (energyClauseFiveRate σ/(1-σ)) :=
  @TaoTrudgianYang2025.energyClauseFive σ hlo hhi

example {σ : ℝ} (hlo : 373/493 ≤ σ) (hhi : σ ≤ 103/136) :
    IsZeroDensityEnergyBound σ
      ((max ((533-730*σ)/(30*(26-35*σ)))
        (max (3*(26-33*σ)/(85*σ-62)) ((174-185*σ)/(31*σ+2))))/(1-σ)) :=
  @TaoTrudgianYang2025.add_est_v_bound σ hlo hhi

example {σ : ℝ} (hlo : 373/493 ≤ σ) (hhi : σ ≤ 103/136) :
    zeroDensityEnergyExponent σ*((1-σ : ℝ) : EReal) ≤
      ((max ((533-730*σ)/(30*(26-35*σ)))
        (max (3*(26-33*σ)/(85*σ-62)) ((174-185*σ)/(31*σ+2))) : ℝ) : EReal) :=
  @TaoTrudgianYang2025.add_est_v σ hlo hhi

example {σ : ℝ} (hlo : 373/493 ≤ σ) (hhi : σ ≤ 103/136) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ T : ℝ, C ≤ T →
        (zeroAdditiveEnergy (σ-δ) T : ℝ) ≤ C*T^
          ((max ((533-730*σ)/(30*(26-35*σ)))
        (max (3*(26-33*σ)/(85*σ-62)) ((174-185*σ)/(31*σ+2))))+ε) :=
  @TaoTrudgianYang2025.add_est_v_zero_energy σ hlo hhi

-- Both exact closed sigma endpoints are accepted.
example :
    IsZeroDensityEnergyBound (373/493)
      (energyClauseFiveRate (373/493)/(1-(373/493))) :=
  energyClauseFive (by norm_num) (by norm_num)

example :
    IsZeroDensityEnergyBound (103/136)
      (energyClauseFiveRate (103/136)/(1-(103/136))) :=
  energyClauseFive (by norm_num) (by norm_num)

-- The two Jutila affine terms agree at the source sigma split.
example (t : ℝ) :
    t+42/11-(64/11)*(171/226) = t+66-88*(171/226) := by ring

-- The second and third printed rates meet at the Jutila sigma split.
example :
    energyClauseFiveSecondRate (171/226) =
      energyClauseFiveThirdRate (171/226) := by
  norm_num [energyClauseFiveSecondRate,energyClauseFiveThirdRate]

-- All printed denominator signs are explicit.
example {σ : ℝ} (hlo : 373/493 ≤ σ) :
    26-35*σ < 0 ∧ 0 < 85*σ-62 ∧ 0 < 31*σ+2 := by
  constructor
  · linarith
  constructor <;> linarith

example {σ : ℝ} (hlo : 373/493 ≤ σ) (hhi : σ ≤ 171/226) :
    1 ≤ 86*σ-64 ∧ 86*σ-64 ≤ 84*σ-312/5 ∧ 84*σ-312/5 ≤ 6/5 := by
  constructor
  · linarith
  constructor <;> linarith

-- The new switch lies after the diagonal crossover and before 6/5.
example {σ : ℝ} (hlo : 171/226 ≤ σ) (hhi : σ ≤ 103/136) :
    1 ≤ (42*σ-20)/11 ∧ (42*σ-20)/11 ≤ (31*σ+2)/22 ∧
      (31*σ+2)/22 ≤ 6/5 := by
  constructor
  · linarith
  constructor <;> linarith

-- The original height-three boundary retains the actual region.
example {σ ρ e : ℝ} (h : InCardinalityEnergyRegion σ 3 ρ e)
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 103/136) :
    e ≤ energyClauseFiveRate σ*3 :=
  h.energyClauseFive_general hlo hhi (by norm_num) (by norm_num)

example {σ : ℝ} (hlo : 373/493 ≤ σ) (hhi : σ ≤ 103/136) :
    IsLargeValueEnergyBound σ 4 (energyClauseFiveRate σ*4) :=
  energyClauseFive_general_bound hlo hhi (by norm_num) (by norm_num)

-- The complete short-zeta interval is supplied by actual estimates.
example {σ : ℝ} (hlo : 373/493 ≤ σ) (hhi : σ ≤ 103/136) :
    IsZetaLargeValueEnergyBound σ 1 (energyClauseFiveRate σ*1) :=
  energyClauseFive_short_zeta hlo hhi (by norm_num) (by norm_num)

example {σ : ℝ} (hlo : 373/493 ≤ σ) (hhi : σ ≤ 103/136) :
    IsZetaLargeValueEnergyBound σ (3/2) (energyClauseFiveRate σ*(3/2)) :=
  energyClauseFive_short_zeta hlo hhi (by norm_num) (by norm_num)

example {σ : ℝ} (hlo : 373/493 ≤ σ) (hhi : σ ≤ 103/136) :
    IsZetaLargeValueEnergyBound σ 2 (energyClauseFiveRate σ*2) :=
  energyClauseFive_short_zeta hlo hhi (by norm_num) (by norm_num)

-- q=2: companion cardinality and energy witnesses are independent.
example {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e) :
    ρ/3 ≤ jutilaLargeValueExponent 11 σ (τ/3) ∧
      ∃ i : Fin 9, e/2 ≤ heathBrownNineBranch σ (τ/2) (ρ/2) (1/2) i := by
  constructor
  · exact h.jutila_cardinality_powered 3 11 (by norm_num) (by norm_num)
  · simpa using h.heathBrown_nine_branches_powered 2 1 (by norm_num) (by norm_num)

-- q=3: the second actual energy-power ratio is also covered.
example {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e) :
    ρ/4 ≤ jutilaLargeValueExponent 11 σ (τ/4) ∧
      ∃ i : Fin 9, e/3 ≤ heathBrownNineBranch σ (τ/3) (ρ/3) (2/3) i := by
  constructor
  · exact h.jutila_cardinality_powered 4 11 (by norm_num) (by norm_num)
  · simpa using h.heathBrown_nine_branches_powered 3 2 (by norm_num) (by norm_num)

-- The five-coordinate region is consumed without constraining its fifth coordinate.
example {σ τ ρ e s : ℝ} (h : InLargeValueEnergyRegion σ τ ρ e s)
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 103/136) (htlo : 2 ≤ τ) (hthi : τ ≤ 4) :
    e ≤ energyClauseFiveRate σ*τ :=
  (show InCardinalityEnergyRegion σ τ ρ e from ⟨s,h⟩).energyClauseFive_general
    hlo hhi htlo hthi

-- The ninth q-1 energy branch is exactly balanced at the new switch.
example {σ : ℝ} (hlo : 171/226 ≤ σ) :
    heathBrownNineBranch σ ((31*σ+2)/22)
      ((31*σ+2)/22+42/11-(64/11)*σ) (1/2) 8 =
        energyClauseFiveThirdRate σ*((31*σ+2)/22) := by
  have hne : 31*σ+2 ≠ 0 := by linarith
  change ((8-16*σ)*(1/2)+9*((31*σ+2)/22+42/11-(64/11)*σ)+
    4*((31*σ+2)/22))/5 = _
  unfold energyClauseFiveThirdRate
  field_simp
  ring

-- The q energy branch gives the same rate at that exact switch.
example {σ : ℝ} (hlo : 171/226 ≤ σ) :
    ((31*σ+2)/22+42/11-(64/11)*σ)+4-4*σ =
      energyClauseFiveThirdRate σ*((31*σ+2)/22) := by
  have hne : 31*σ+2 ≠ 0 := by linarith
  unfold energyClauseFiveThirdRate
  field_simp
  ring

example {σ : ℝ} (hlo : 373/493 ≤ σ) (hhi : σ ≤ 103/136) :
    IsLargeValueEnergyBound σ 2 (energyClauseFiveRate σ*2) :=
  energyClauseFive_general_bound hlo hhi (by norm_num) (by norm_num)

-- The switch precedes the Jutila/Guth--Maynard cardinality crossover.
example {σ : ℝ} (hlo : 171/226 ≤ σ) :
    (31*σ+2)/22 ≤ 4*(25*σ-3)/55 := by linarith

end AddEstFifthRegression

namespace AddEstSixthRegression

example (σ t : ℝ) :
    jutilaLargeValueExponent 10 σ t =
      max (2-2*σ) (max (t+19/5-(29/5)*σ) (t+60-80*σ)) :=
  @TaoTrudgianYang2025.jutila_ten_formula σ t

example
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (q : ℕ) (hq : 1 ≤ q) :
    ρ/q ≤ max (2-2*σ) (max (τ/q+19/5-(29/5)*σ) (τ/q+60-80*σ)) :=
  @TaoTrudgianYang2025.InCardinalityEnergyRegion.jutila_ten_cardinality_powered σ τ ρ e h q hq

example {σ t : ℝ} (hσ : σ ≤ 281/371) :
    max (2-2*σ) (max (t+19/5-(29/5)*σ) (t+60-80*σ)) =
      max (2-2*σ) (t+60-80*σ) :=
  @TaoTrudgianYang2025.jutila_ten_low_sigma σ t hσ

example {σ t : ℝ} (hσ : 281/371 ≤ σ) :
    max (2-2*σ) (max (t+19/5-(29/5)*σ) (t+60-80*σ)) =
      max (2-2*σ) (t+19/5-(29/5)*σ) :=
  @TaoTrudgianYang2025.jutila_ten_high_sigma σ t hσ

example {σ t : ℝ}
    (hσ : 664/877 ≤ σ) (ht : t ≤ 1) :
    max (2-2*σ) (max (t+19/5-(29/5)*σ) (t+60-80*σ)) = 2-2*σ :=
  @TaoTrudgianYang2025.jutila_ten_at_most_one σ t hσ ht

example
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 31/40)
    (q : ℕ) (hq : q=2 ∨ q=3) (htlo : (q : ℝ) ≤ τ) (hthi : τ ≤ q+1) :
    1 ≤ τ/q ∧ τ/q ≤ 3/2 ∧
      ρ/q ≤ max (2-2*σ) (max (τ/q+19/5-(29/5)*σ) (τ/q+60-80*σ)) ∧
      ρ/q ≤ max (18/5-4*σ) (12/5-4*σ+τ/q) ∧
      ρ/q ≤ 3-3*σ :=
  @TaoTrudgianYang2025.InCardinalityEnergyRegion.energyClauseSix_cardinality_caps σ τ ρ e h hlo hhi q hq htlo hthi

example (σ : ℝ) :
    energyClauseSixRate σ =
      max ((72-91*σ)/(7*(11*σ-8))) (5*(18-19*σ)/(2*(5*σ+3))) :=
  @TaoTrudgianYang2025.energyClauseSixRate_eq_printed σ

example (σ : ℝ) :
    energyClauseSixFirstRate σ ≤ energyClauseSixRate σ :=
  @TaoTrudgianYang2025.energyClauseSixFirstRate_le σ

example (σ : ℝ) :
    energyClauseSixSecondRate σ ≤ energyClauseSixRate σ :=
  @TaoTrudgianYang2025.energyClauseSixSecondRate_le σ

example {σ : ℝ} (hlo : 664/877 ≤ σ) :
    0 < 7*(11*σ-8) ∧ 0 < 2*(5*σ+3) :=
  @TaoTrudgianYang2025.energyClauseSix_printed_denominators_pos σ hlo

example {σ : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 31/40) :
    0 < energyClauseSixRate σ :=
  @TaoTrudgianYang2025.energyClauseSixRate_pos σ hlo hhi

example {σ : ℝ} (hhi : σ ≤ 31/40) :
    energyClauseSixRate σ/(1-σ) =
      max ((72-91*σ)/(7*(11*σ-8)*(1-σ)))
        (5*(18-19*σ)/(2*(5*σ+3)*(1-σ))) :=
  @TaoTrudgianYang2025.energyClauseSixRate_div_eq_blueprint σ hhi

example {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 1 ≤ t) (hthi : t ≤ 78*σ-58) :
    ((1)*(0)+(0))*t+((4-4*σ)*(2/3)+(1)*(2-2*σ)) ≤ energyClauseSixFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_low_0_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 78*σ-58 ≤ t) (hthi : t ≤ 77*σ/2-28) :
    ((1)*(1)+(0))*t+((4-4*σ)*(2/3)+(1)*(60-80*σ)) ≤ energyClauseSixFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_low_0_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 1 ≤ t) (hthi : t ≤ 78*σ-58) :
    ((5/2)*(0)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(2-2*σ)) ≤ energyClauseSixFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_low_1_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 78*σ-58 ≤ t) (hthi : t ≤ 77*σ/2-28) :
    ((5/2)*(1)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(60-80*σ)) ≤ energyClauseSixFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_low_1_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 1 ≤ t) (hthi : t ≤ 78*σ-58) :
    ((8/5)*(0)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(2-2*σ)) ≤ energyClauseSixFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_low_2_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 78*σ-58 ≤ t) (hthi : t ≤ 77*σ/2-28) :
    ((8/5)*(1)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(60-80*σ)) ≤ energyClauseSixFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_low_2_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 1 ≤ t) (hthi : t ≤ 78*σ-58) :
    ((2)*(0)+(0))*t+((3-4*σ)*(1/2)+(2)*(2-2*σ)) ≤ energyClauseSixFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_low_3_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 78*σ-58 ≤ t) (hthi : t ≤ 77*σ/2-28) :
    ((2)*(1)+(0))*t+((3-4*σ)*(1/2)+(2)*(60-80*σ)) ≤ energyClauseSixFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_low_3_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 1 ≤ t) (hthi : t ≤ 78*σ-58) :
    ((3)*(0)+(0))*t+((1-2*σ)*(1/2)+(3)*(2-2*σ)) ≤ energyClauseSixFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_low_4_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 78*σ-58 ≤ t) (hthi : t ≤ 77*σ/2-28) :
    ((3)*(1)+(0))*t+((1-2*σ)*(1/2)+(3)*(60-80*σ)) ≤ energyClauseSixFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_low_4_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 1 ≤ t) (hthi : t ≤ 78*σ-58) :
    ((12/5)*(0)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(2-2*σ)) ≤ energyClauseSixFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_low_5_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 78*σ-58 ≤ t) (hthi : t ≤ 77*σ/2-28) :
    ((12/5)*(1)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(60-80*σ)) ≤ energyClauseSixFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_low_5_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 1 ≤ t) (hthi : t ≤ 78*σ-58) :
    ((5/4)*(0)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(2-2*σ)) ≤ energyClauseSixFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_low_6_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 78*σ-58 ≤ t) (hthi : t ≤ 77*σ/2-28) :
    ((5/4)*(1)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(60-80*σ)) ≤ energyClauseSixFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_low_6_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 1 ≤ t) (hthi : t ≤ 78*σ-58) :
    ((21/8)*(0)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(2-2*σ)) ≤ energyClauseSixFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_low_7_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 78*σ-58 ≤ t) (hthi : t ≤ 77*σ/2-28) :
    ((21/8)*(1)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(60-80*σ)) ≤ energyClauseSixFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_low_7_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 1 ≤ t) (hthi : t ≤ 78*σ-58) :
    ((9/5)*(0)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(2-2*σ)) ≤ energyClauseSixFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_low_8_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 78*σ-58 ≤ t) (hthi : t ≤ 77*σ/2-28) :
    ((9/5)*(1)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(60-80*σ)) ≤ energyClauseSixFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_low_8_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : 1 ≤ t) (hthi : t ≤ (19*σ-9)/5) :
    ((1)*(0)+(0))*t+((4-4*σ)*(2/3)+(1)*(2-2*σ)) ≤ energyClauseSixSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_high_0_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : (19*σ-9)/5 ≤ t) (hthi : t ≤ (14*σ+1)/10) :
    ((1)*(1)+(0))*t+((4-4*σ)*(2/3)+(1)*(19/5-(29/5)*σ)) ≤ energyClauseSixSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_high_0_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : 1 ≤ t) (hthi : t ≤ (19*σ-9)/5) :
    ((5/2)*(0)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(2-2*σ)) ≤ energyClauseSixSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_high_1_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : (19*σ-9)/5 ≤ t) (hthi : t ≤ (14*σ+1)/10) :
    ((5/2)*(1)+(0))*t+(((3-4*σ)/2)*(1/2)+(5/2)*(19/5-(29/5)*σ)) ≤ energyClauseSixSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_high_1_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : 1 ≤ t) (hthi : t ≤ (19*σ-9)/5) :
    ((8/5)*(0)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(2-2*σ)) ≤ energyClauseSixSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_high_2_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : (19*σ-9)/5 ≤ t) (hthi : t ≤ (14*σ+1)/10) :
    ((8/5)*(1)+(2/5))*t+(((12-16*σ)/5)*(1/2)+(8/5)*(19/5-(29/5)*σ)) ≤ energyClauseSixSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_high_2_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : 1 ≤ t) (hthi : t ≤ (19*σ-9)/5) :
    ((2)*(0)+(0))*t+((3-4*σ)*(1/2)+(2)*(2-2*σ)) ≤ energyClauseSixSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_high_3_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : (19*σ-9)/5 ≤ t) (hthi : t ≤ (14*σ+1)/10) :
    ((2)*(1)+(0))*t+((3-4*σ)*(1/2)+(2)*(19/5-(29/5)*σ)) ≤ energyClauseSixSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_high_3_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : 1 ≤ t) (hthi : t ≤ (19*σ-9)/5) :
    ((3)*(0)+(0))*t+((1-2*σ)*(1/2)+(3)*(2-2*σ)) ≤ energyClauseSixSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_high_4_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : (19*σ-9)/5 ≤ t) (hthi : t ≤ (14*σ+1)/10) :
    ((3)*(1)+(0))*t+((1-2*σ)*(1/2)+(3)*(19/5-(29/5)*σ)) ≤ energyClauseSixSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_high_4_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : 1 ≤ t) (hthi : t ≤ (19*σ-9)/5) :
    ((12/5)*(0)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(2-2*σ)) ≤ energyClauseSixSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_high_5_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : (19*σ-9)/5 ≤ t) (hthi : t ≤ (14*σ+1)/10) :
    ((12/5)*(1)+(2/5))*t+(((8-16*σ)/5)*(1/2)+(12/5)*(19/5-(29/5)*σ)) ≤ energyClauseSixSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_high_5_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : 1 ≤ t) (hthi : t ≤ (19*σ-9)/5) :
    ((5/4)*(0)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(2-2*σ)) ≤ energyClauseSixSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_high_6_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : (19*σ-9)/5 ≤ t) (hthi : t ≤ (14*σ+1)/10) :
    ((5/4)*(1)+(1/2))*t+((3-4*σ)*(1/2)+(5/4)*(19/5-(29/5)*σ)) ≤ energyClauseSixSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_high_6_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : 1 ≤ t) (hthi : t ≤ (19*σ-9)/5) :
    ((21/8)*(0)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(2-2*σ)) ≤ energyClauseSixSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_high_7_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : (19*σ-9)/5 ≤ t) (hthi : t ≤ (14*σ+1)/10) :
    ((21/8)*(1)+(1/4))*t+((1-2*σ)*(1/2)+(21/8)*(19/5-(29/5)*σ)) ≤ energyClauseSixSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_high_7_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : 1 ≤ t) (hthi : t ≤ (19*σ-9)/5) :
    ((9/5)*(0)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(2-2*σ)) ≤ energyClauseSixSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_high_8_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : (19*σ-9)/5 ≤ t) (hthi : t ≤ (14*σ+1)/10) :
    ((9/5)*(1)+(4/5))*t+(((8-16*σ)/5)*(1/2)+(9/5)*(19/5-(29/5)*σ)) ≤ energyClauseSixSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_high_8_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 77*σ/2-28 ≤ t) (hthi : t ≤ 6/5) :
    (1)*t+(60-80*σ+4-4*σ) ≤ energyClauseSixFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_low_middle_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (_hhi : σ ≤ 281/371)
    (htlo : 77*σ/2-28 ≤ t) (hthi : t ≤ 6/5) :
    (5/2)*t+((3-4*σ+5*(60-80*σ))/2) ≤ energyClauseSixFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_low_middle_1 σ t hlo _hhi htlo hthi

example {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : (14*σ+1)/10 ≤ t) (hthi : t ≤ 6/5) :
    (1)*t+(19/5-(29/5)*σ+4-4*σ) ≤ energyClauseSixSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_high_middle_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : (14*σ+1)/10 ≤ t) (hthi : t ≤ 6/5) :
    (5/2)*t+((3-4*σ+5*(19/5-(29/5)*σ))/2) ≤ energyClauseSixSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_high_middle_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : 6/5 ≤ t) (hthi : t ≤ σ+3/5) :
    (1)*t+((12/5-4*σ)+4-4*σ) ≤ energyClauseSixSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_tall_0_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : σ+3/5 ≤ t) (hthi : t ≤ 3/2) :
    (0)*t+((3-3*σ)+4-4*σ) ≤ energyClauseSixSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_tall_0_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (_hhi : σ ≤ 31/40)
    (htlo : 6/5 ≤ t) (hthi : t ≤ σ+3/5) :
    ((5/2)*(1))*t+((3-4*σ+5*(12/5-4*σ))/2) ≤ energyClauseSixSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_tall_1_0 σ t hlo _hhi htlo hthi

example {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : σ+3/5 ≤ t) (hthi : t ≤ 3/2) :
    ((5/2)*(0))*t+((3-4*σ+5*(3-3*σ))/2) ≤ energyClauseSixSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_tall_1_1 σ t hlo hhi htlo hthi

example {σ t r a e : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 1 ≤ t) (hthi : t ≤ 77*σ/2-28)
    (halo : 1/2 ≤ a) (hahi : a ≤ 2/3)
    (hj : r ≤ max (2-2*σ) (t+(60-80*σ)))
    (i : Fin 9) (hb : e ≤ heathBrownNineBranch σ t r a i) :
    e ≤ energyClauseSixRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_low_short_branch σ t r a e hlo hhi htlo hthi halo hahi hj i hb

example {σ t r a e : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : 1 ≤ t) (hthi : t ≤ (14*σ+1)/10)
    (halo : 1/2 ≤ a) (hahi : a ≤ 2/3)
    (hj : r ≤ max (2-2*σ) (t+(19/5-(29/5)*σ)))
    (i : Fin 9) (hb : e ≤ heathBrownNineBranch σ t r a i) :
    e ≤ energyClauseSixRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_high_short_branch σ t r a e hlo hhi htlo hthi halo hahi hj i hb

example {σ t r : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : 6/5 ≤ t) (hthi : t ≤ 3/2)
    (hg : r ≤ max (18/5-4*σ) (12/5-4*σ+t)) (hcap : r ≤ 3-3*σ) :
    max (r+4-4*σ) ((3-4*σ+5*r)/2) ≤ energyClauseSixRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_tall_bound σ t r hlo hhi htlo hthi hg hcap

example {σ t r : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371)
    (htlo : 77*σ/2-28 ≤ t) (hthi : t ≤ 6/5)
    (hj : r ≤ max (2-2*σ) (t+(60-80*σ))) :
    max (r+4-4*σ) ((3-4*σ+5*r)/2) ≤ energyClauseSixRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_low_middle_bound σ t r hlo hhi htlo hthi hj

example {σ t r : ℝ}
    (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : (14*σ+1)/10 ≤ t) (hthi : t ≤ 6/5)
    (hj : r ≤ max (2-2*σ) (t+(19/5-(29/5)*σ))) :
    max (r+4-4*σ) ((3-4*σ+5*r)/2) ≤ energyClauseSixRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_high_middle_bound σ t r hlo hhi htlo hthi hj

example
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 31/40) (htlo : 2 ≤ τ) (hthi : τ ≤ 4) :
    e ≤ energyClauseSixRate σ*τ :=
  @TaoTrudgianYang2025.InCardinalityEnergyRegion.energyClauseSix_general σ τ ρ e h hlo hhi htlo hthi

example {σ τ : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 31/40) (htlo : 2 ≤ τ) (hthi : τ ≤ 4) :
    IsLargeValueEnergyBound σ τ (energyClauseSixRate σ*τ) :=
  @TaoTrudgianYang2025.energyClauseSix_general_bound σ τ hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (_hhi : σ ≤ 31/40)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((1)*2+(0))*t+((4-4*σ)+(1)*(6-12*σ)) ≤ energyClauseSixSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_zeta_0 σ t hlo _hhi htlo hthi

example {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (_hhi : σ ≤ 31/40)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((5/2)*2+(0))*t+(((3-4*σ)/2)+(5/2)*(6-12*σ)) ≤ energyClauseSixSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_zeta_1 σ t hlo _hhi htlo hthi

example {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (_hhi : σ ≤ 31/40)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((8/5)*2+(2/5))*t+(((12-16*σ)/5)+(8/5)*(6-12*σ)) ≤ energyClauseSixSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_zeta_2 σ t hlo _hhi htlo hthi

example {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (_hhi : σ ≤ 31/40)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((2)*2+(0))*t+((3-4*σ)+(2)*(6-12*σ)) ≤ energyClauseSixSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_zeta_3 σ t hlo _hhi htlo hthi

example {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (_hhi : σ ≤ 31/40)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((3)*2+(0))*t+((1-2*σ)+(3)*(6-12*σ)) ≤ energyClauseSixSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_zeta_4 σ t hlo _hhi htlo hthi

example {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (_hhi : σ ≤ 31/40)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((12/5)*2+(2/5))*t+(((8-16*σ)/5)+(12/5)*(6-12*σ)) ≤ energyClauseSixSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_zeta_5 σ t hlo _hhi htlo hthi

example {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (_hhi : σ ≤ 31/40)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((5/4)*2+(1/2))*t+((3-4*σ)+(5/4)*(6-12*σ)) ≤ energyClauseSixSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_zeta_6 σ t hlo _hhi htlo hthi

example {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (_hhi : σ ≤ 31/40)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((21/8)*2+(1/4))*t+((1-2*σ)+(21/8)*(6-12*σ)) ≤ energyClauseSixSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_zeta_7 σ t hlo _hhi htlo hthi

example {σ t : ℝ}
    (hlo : 664/877 ≤ σ) (_hhi : σ ≤ 31/40)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((9/5)*2+(4/5))*t+(((8-16*σ)/5)+(9/5)*(6-12*σ)) ≤ energyClauseSixSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_zeta_8 σ t hlo _hhi htlo hthi

example {σ t r : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 31/40)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) (hr : r ≤ 2*t-12*(σ-1/2)) (i : Fin 9) :
    heathBrownNineBranch σ t r 1 i ≤ energyClauseSixRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSix_zeta_branch σ t r hlo hhi htlo hthi hr i

example
    {σ τ ρ e s : ℝ} (h : InZetaLargeValueEnergyRegion σ τ ρ e s)
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 31/40) (htlo : 3/2 ≤ τ) (hthi : τ ≤ 2) :
    e ≤ energyClauseSixRate σ*τ :=
  @TaoTrudgianYang2025.InZetaLargeValueEnergyRegion.energyClauseSix σ τ ρ e s h hlo hhi htlo hthi

example {σ τ : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 31/40) (htlo : 1 ≤ τ) (hthi : τ ≤ 2) :
    IsZetaLargeValueEnergyBound σ τ (energyClauseSixRate σ*τ) :=
  @TaoTrudgianYang2025.energyClauseSix_short_zeta σ τ hlo hhi htlo hthi

example {σ : ℝ} (hlo : 664/877 ≤ σ) (hhi : σ ≤ 31/40) :
    IsZeroDensityEnergyBound σ (energyClauseSixRate σ/(1-σ)) :=
  @TaoTrudgianYang2025.energyClauseSix σ hlo hhi

example {σ : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 31/40) :
    zeroDensityEnergyExponent σ ≤
      ((max ((72-91*σ)/(7*(11*σ-8)*(1-σ)))
        (5*(18-19*σ)/(2*(5*σ+3)*(1-σ))) : ℝ) : EReal) :=
  @TaoTrudgianYang2025.energyClauseSix_blueprint σ hlo hhi

example {σ : ℝ} (hlo : 103/136 ≤ σ) (hhi : σ ≤ 42/55) :
    IsZeroDensityEnergyBound σ
      ((max ((72-91*σ)/(7*(11*σ-8))) (5*(18-19*σ)/(2*(5*σ+3))))/(1-σ)) :=
  @TaoTrudgianYang2025.add_est_vi_bound σ hlo hhi

example {σ : ℝ} (hlo : 103/136 ≤ σ) (hhi : σ ≤ 42/55) :
    zeroDensityEnergyExponent σ*((1-σ : ℝ) : EReal) ≤
      ((max ((72-91*σ)/(7*(11*σ-8))) (5*(18-19*σ)/(2*(5*σ+3))) : ℝ) : EReal) :=
  @TaoTrudgianYang2025.add_est_vi σ hlo hhi

example {σ : ℝ} (hlo : 103/136 ≤ σ) (hhi : σ ≤ 42/55) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ T : ℝ, C ≤ T →
        (zeroAdditiveEnergy (σ-δ) T : ℝ) ≤ C*T^
          ((max ((72-91*σ)/(7*(11*σ-8))) (5*(18-19*σ)/(2*(5*σ+3))))+ε) :=
  @TaoTrudgianYang2025.add_est_vi_zero_energy σ hlo hhi

-- The full blueprint endpoint is included.
example :
    IsZeroDensityEnergyBound (664/877)
      (energyClauseSixRate (664/877)/(1-(664/877))) :=
  energyClauseSix (by norm_num) (by norm_num)

-- The full blueprint endpoint is included.
example :
    IsZeroDensityEnergyBound (31/40)
      (energyClauseSixRate (31/40)/(1-(31/40))) :=
  energyClauseSix (by norm_num) (by norm_num)

-- The frozen paper endpoint is accepted by the public theorem.
example :
    IsZeroDensityEnergyBound (103/136)
      (energyClauseSixRate (103/136)/(1-(103/136))) := by
  simpa only [energyClauseSixRate_eq_printed] using
    add_est_vi_bound (σ := (103/136)) (by norm_num) (by norm_num)

-- The frozen paper endpoint is accepted by the public theorem.
example :
    IsZeroDensityEnergyBound (42/55)
      (energyClauseSixRate (42/55)/(1-(42/55))) := by
  simpa only [energyClauseSixRate_eq_printed] using
    add_est_vi_bound (σ := (42/55)) (by norm_num) (by norm_num)

example (t : ℝ) :
    t+19/5-(29/5)*(281/371) = t+60-80*(281/371) := by ring

example {σ : ℝ} (hlo : 664/877 ≤ σ) :
    0 < 11*σ-8 ∧ 0 < 5*σ+3 := by constructor <;> linarith

-- The exact public interval sits inside the full source interval.
example :
    (664/877 : ℝ) ≤ 103/136 ∧ (103/136 : ℝ) ≤ 281/371 ∧
      (281/371 : ℝ) ≤ 42/55 ∧ (42/55 : ℝ) ≤ 31/40 := by norm_num

example {σ : ℝ} (hlo : 664/877 ≤ σ) (hhi : σ ≤ 281/371) :
    1 ≤ 78*σ-58 ∧ 78*σ-58 ≤ 77*σ/2-28 ∧ 77*σ/2-28 ≤ 6/5 := by
  constructor
  · linarith
  constructor <;> linarith

example {σ : ℝ} (hlo : 281/371 ≤ σ) (hhi : σ ≤ 31/40) :
    1 ≤ (19*σ-9)/5 ∧ (19*σ-9)/5 ≤ (14*σ+1)/10 ∧
      (14*σ+1)/10 ≤ 6/5 := by
  constructor
  · linarith
  constructor <;> linarith

-- Both moving switches agree at the source sigma split.
example :
    (77*(281/371)/2-28 : ℝ) = (14*(281/371)+1)/10 := by norm_num

-- The actual ninth q-1 branch meets the first rate at the low switch.
example {σ : ℝ} (hlo : 664/877 ≤ σ) :
    heathBrownNineBranch σ (77*σ/2-28) (77*σ/2-28+60-80*σ) (1/2) 8 =
      energyClauseSixFirstRate σ*(77*σ/2-28) := by
  have hne : 11*σ-8 ≠ 0 := by linarith
  change ((8-16*σ)*(1/2)+9*(77*σ/2-28+60-80*σ)+4*(77*σ/2-28))/5 = _
  unfold energyClauseSixFirstRate
  conv_rhs =>
    rw [show 77*σ/2-28 = (7*(11*σ-8))/2 by ring,
      ← mul_div_assoc, div_mul_cancel₀ _ (mul_ne_zero (by norm_num) hne)]
  ring

-- The first q branch gives the same rate at the low switch.
example {σ : ℝ} (hlo : 664/877 ≤ σ) :
    (77*σ/2-28+60-80*σ)+4-4*σ =
      energyClauseSixFirstRate σ*(77*σ/2-28) := by
  have hne : 11*σ-8 ≠ 0 := by linarith
  unfold energyClauseSixFirstRate
  conv_rhs =>
    rw [show 77*σ/2-28 = (7*(11*σ-8))/2 by ring,
      ← mul_div_assoc, div_mul_cancel₀ _ (mul_ne_zero (by norm_num) hne)]
  ring

-- At the high switch the two actual affine branches are balanced.
example (σ : ℝ) :
    heathBrownNineBranch σ ((14*σ+1)/10)
      ((14*σ+1)/10+19/5-(29/5)*σ) (1/2) 8 =
        ((14*σ+1)/10+19/5-(29/5)*σ)+4-4*σ := by
  change ((8-16*σ)*(1/2)+9*((14*σ+1)/10+19/5-(29/5)*σ)+
    4*((14*σ+1)/10))/5 = _
  ring

example {σ ρ e : ℝ} (h : InCardinalityEnergyRegion σ 2 ρ e)
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 31/40) :
    e ≤ energyClauseSixRate σ*2 :=
  h.energyClauseSix_general hlo hhi (by norm_num) (by norm_num)

example {σ ρ e : ℝ} (h : InCardinalityEnergyRegion σ 3 ρ e)
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 31/40) :
    e ≤ energyClauseSixRate σ*3 :=
  h.energyClauseSix_general hlo hhi (by norm_num) (by norm_num)

example {σ ρ e : ℝ} (h : InCardinalityEnergyRegion σ 4 ρ e)
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 31/40) :
    e ≤ energyClauseSixRate σ*4 :=
  h.energyClauseSix_general hlo hhi (by norm_num) (by norm_num)

example {σ : ℝ} (hlo : 664/877 ≤ σ) (hhi : σ ≤ 31/40) :
    IsZetaLargeValueEnergyBound σ 1 (energyClauseSixRate σ*1) :=
  energyClauseSix_short_zeta hlo hhi (by norm_num) (by norm_num)

example {σ : ℝ} (hlo : 664/877 ≤ σ) (hhi : σ ≤ 31/40) :
    IsZetaLargeValueEnergyBound σ (3/2) (energyClauseSixRate σ*(3/2)) :=
  energyClauseSix_short_zeta hlo hhi (by norm_num) (by norm_num)

example {σ : ℝ} (hlo : 664/877 ≤ σ) (hhi : σ ≤ 31/40) :
    IsZetaLargeValueEnergyBound σ 2 (energyClauseSixRate σ*2) :=
  energyClauseSix_short_zeta hlo hhi (by norm_num) (by norm_num)

-- Cardinality at q+1 and energy at q-1 come from independent witnesses.
example {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e) :
    ρ/3 ≤ jutilaLargeValueExponent 10 σ (τ/3) ∧
      ∃ i : Fin 9, e/2 ≤ heathBrownNineBranch σ (τ/2) (ρ/2) (1/2) i := by
  constructor
  · exact h.jutila_cardinality_powered 3 10 (by norm_num) (by norm_num)
  · simpa using h.heathBrown_nine_branches_powered 2 1 (by norm_num) (by norm_num)

-- Cardinality at q+1 and energy at q-1 come from independent witnesses.
example {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e) :
    ρ/4 ≤ jutilaLargeValueExponent 10 σ (τ/4) ∧
      ∃ i : Fin 9, e/3 ≤ heathBrownNineBranch σ (τ/3) (ρ/3) (2/3) i := by
  constructor
  · exact h.jutila_cardinality_powered 4 10 (by norm_num) (by norm_num)
  · simpa using h.heathBrown_nine_branches_powered 3 2 (by norm_num) (by norm_num)

-- The fifth coordinate is existentially projected, never scaled.
example {σ τ ρ e s : ℝ} (h : InLargeValueEnergyRegion σ τ ρ e s)
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 31/40) (htlo : 2 ≤ τ) (hthi : τ ≤ 4) :
    e ≤ energyClauseSixRate σ*τ :=
  (show InCardinalityEnergyRegion σ τ ρ e from ⟨s,h⟩).energyClauseSix_general
    hlo hhi htlo hthi

end AddEstSixthRegression

namespace AddEstSeventhRegression

open TaoTrudgianYang2025

example (σ t : ℝ) :
    jutilaLargeValueExponent 6 σ t =
      max (2-2*σ) (max (t+11/3-(17/3)*σ) (t+36-48*σ)) :=
  @TaoTrudgianYang2025.jutila_six_formula σ t

example
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (q : ℕ) (hq : 1 ≤ q) :
    ρ/q ≤ max (2-2*σ) (max (τ/q+11/3-(17/3)*σ) (τ/q+36-48*σ)) :=
  @TaoTrudgianYang2025.InCardinalityEnergyRegion.jutila_six_cardinality_powered σ τ ρ e h q hq

example {σ t : ℝ} (hσ : σ ≤ 97/127) :
    max (2-2*σ) (max (t+11/3-(17/3)*σ) (t+36-48*σ)) =
      max (2-2*σ) (t+36-48*σ) :=
  @TaoTrudgianYang2025.jutila_six_low_sigma σ t hσ

example {σ t : ℝ} (hσ : 97/127 ≤ σ) :
    max (2-2*σ) (max (t+11/3-(17/3)*σ) (t+36-48*σ)) =
      max (2-2*σ) (t+11/3-(17/3)*σ) :=
  @TaoTrudgianYang2025.jutila_six_high_sigma σ t hσ

example {σ t : ℝ}
    (hσ : 42/55 ≤ σ) (ht : t ≤ 1) :
    max (2-2*σ) (max (t+11/3-(17/3)*σ) (t+36-48*σ)) = 2-2*σ :=
  @TaoTrudgianYang2025.jutila_six_at_most_one σ t hσ ht

example
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 79/103)
    (q : ℕ) (hq : q=2 ∨ q=3) (htlo : (q : ℝ) ≤ τ) (hthi : τ ≤ q+1) :
    1 ≤ τ/q ∧ τ/q ≤ 3/2 ∧
      ρ/q ≤ max (2-2*σ) (max (τ/q+11/3-(17/3)*σ) (τ/q+36-48*σ)) ∧
      ρ/q ≤ 3-3*σ :=
  @TaoTrudgianYang2025.InCardinalityEnergyRegion.energyClauseSeven_cardinality_caps σ τ ρ e h hlo hhi q hq htlo hthi

example (σ : ℝ) :
    energyClauseSevenRate σ =
      max ((18-19*σ)/(6*(15*σ-11))) (3*(18-19*σ)/(4*(4*σ-1))) :=
  @TaoTrudgianYang2025.energyClauseSevenRate_eq_printed σ

example (σ : ℝ) :
    energyClauseSevenFirstRate σ ≤ energyClauseSevenRate σ :=
  @TaoTrudgianYang2025.energyClauseSevenFirstRate_le σ

example (σ : ℝ) :
    energyClauseSevenSecondRate σ ≤ energyClauseSevenRate σ :=
  @TaoTrudgianYang2025.energyClauseSevenSecondRate_le σ

example {σ : ℝ} (hlo : 42/55 ≤ σ) :
    0 < 6*(15*σ-11) ∧ 0 < 4*(4*σ-1) :=
  @TaoTrudgianYang2025.energyClauseSeven_printed_denominators_pos σ hlo

example {σ : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 79/103) :
    0 < energyClauseSevenRate σ :=
  @TaoTrudgianYang2025.energyClauseSevenRate_pos σ hlo hhi

example {σ : ℝ} (hhi : σ ≤ 79/103) :
    energyClauseSevenRate σ/(1-σ) =
      max ((18-19*σ)/(6*(15*σ-11)*(1-σ)))
        (3*(18-19*σ)/(4*(4*σ-1)*(1-σ))) :=
  @TaoTrudgianYang2025.energyClauseSevenRate_div_eq_blueprint σ hhi

example {σ t : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 97/127)
    (htlo : 1 ≤ t) (hthi : t ≤ 46*σ-34) :
    (0)*t+((4-4*σ)*(2/3)+(1)*(2-2*σ)) ≤ energyClauseSevenFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_low_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 97/127)
    (htlo : 1 ≤ t) (hthi : t ≤ 46*σ-34) :
    (0)*t+(((3-4*σ)/2)*(1/2)+(5/2)*(2-2*σ)) ≤ energyClauseSevenFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_low_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 97/127)
    (htlo : 1 ≤ t) (hthi : t ≤ 46*σ-34) :
    (2/5)*t+(((12-16*σ)/5)*(1/2)+(8/5)*(2-2*σ)) ≤ energyClauseSevenFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_low_2 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 97/127)
    (htlo : 1 ≤ t) (hthi : t ≤ 46*σ-34) :
    (0)*t+((3-4*σ)*(1/2)+(2)*(2-2*σ)) ≤ energyClauseSevenFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_low_3 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 97/127)
    (htlo : 1 ≤ t) (hthi : t ≤ 46*σ-34) :
    (0)*t+((1-2*σ)*(1/2)+(3)*(2-2*σ)) ≤ energyClauseSevenFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_low_4 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 97/127)
    (htlo : 1 ≤ t) (hthi : t ≤ 46*σ-34) :
    (2/5)*t+(((8-16*σ)/5)*(1/2)+(12/5)*(2-2*σ)) ≤ energyClauseSevenFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_low_5 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 97/127)
    (htlo : 1 ≤ t) (hthi : t ≤ 46*σ-34) :
    (1/2)*t+((3-4*σ)*(1/2)+(5/4)*(2-2*σ)) ≤ energyClauseSevenFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_low_6 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 97/127)
    (htlo : 1 ≤ t) (hthi : t ≤ 46*σ-34) :
    (1/4)*t+((1-2*σ)*(1/2)+(21/8)*(2-2*σ)) ≤ energyClauseSevenFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_low_7 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 97/127)
    (htlo : 1 ≤ t) (hthi : t ≤ 46*σ-34) :
    (4/5)*t+(((8-16*σ)/5)*(1/2)+(9/5)*(2-2*σ)) ≤ energyClauseSevenFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_low_8 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 97/127 ≤ σ) (hhi : σ ≤ 79/103)
    (htlo : 1 ≤ t) (hthi : t ≤ (11*σ-5)/3) :
    (0)*t+((4-4*σ)*(2/3)+(1)*(2-2*σ)) ≤ energyClauseSevenSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_high_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 97/127 ≤ σ) (hhi : σ ≤ 79/103)
    (htlo : 1 ≤ t) (hthi : t ≤ (11*σ-5)/3) :
    (0)*t+(((3-4*σ)/2)*(1/2)+(5/2)*(2-2*σ)) ≤ energyClauseSevenSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_high_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 97/127 ≤ σ) (hhi : σ ≤ 79/103)
    (htlo : 1 ≤ t) (hthi : t ≤ (11*σ-5)/3) :
    (2/5)*t+(((12-16*σ)/5)*(1/2)+(8/5)*(2-2*σ)) ≤ energyClauseSevenSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_high_2 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 97/127 ≤ σ) (hhi : σ ≤ 79/103)
    (htlo : 1 ≤ t) (hthi : t ≤ (11*σ-5)/3) :
    (0)*t+((3-4*σ)*(1/2)+(2)*(2-2*σ)) ≤ energyClauseSevenSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_high_3 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 97/127 ≤ σ) (hhi : σ ≤ 79/103)
    (htlo : 1 ≤ t) (hthi : t ≤ (11*σ-5)/3) :
    (0)*t+((1-2*σ)*(1/2)+(3)*(2-2*σ)) ≤ energyClauseSevenSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_high_4 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 97/127 ≤ σ) (hhi : σ ≤ 79/103)
    (htlo : 1 ≤ t) (hthi : t ≤ (11*σ-5)/3) :
    (2/5)*t+(((8-16*σ)/5)*(1/2)+(12/5)*(2-2*σ)) ≤ energyClauseSevenSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_high_5 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 97/127 ≤ σ) (hhi : σ ≤ 79/103)
    (htlo : 1 ≤ t) (hthi : t ≤ (11*σ-5)/3) :
    (1/2)*t+((3-4*σ)*(1/2)+(5/4)*(2-2*σ)) ≤ energyClauseSevenSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_high_6 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 97/127 ≤ σ) (hhi : σ ≤ 79/103)
    (htlo : 1 ≤ t) (hthi : t ≤ (11*σ-5)/3) :
    (1/4)*t+((1-2*σ)*(1/2)+(21/8)*(2-2*σ)) ≤ energyClauseSevenSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_high_7 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 97/127 ≤ σ) (hhi : σ ≤ 79/103)
    (htlo : 1 ≤ t) (hthi : t ≤ (11*σ-5)/3) :
    (4/5)*t+(((8-16*σ)/5)*(1/2)+(9/5)*(2-2*σ)) ≤ energyClauseSevenSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_high_8 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 97/127)
    (htlo : 46*σ-34 ≤ t) (hthi : t ≤ 45*σ-33) :
    (1)*t+((4-4*σ)+(1)*(36-48*σ)) ≤ energyClauseSevenFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_low_tall_0_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 97/127)
    (htlo : 45*σ-33 ≤ t) (hthi : t ≤ 3/2) :
    (0)*t+((4-4*σ)+(1)*(3-3*σ)) ≤ energyClauseSevenFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_low_tall_0_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 97/127)
    (htlo : 46*σ-34 ≤ t) (hthi : t ≤ 45*σ-33) :
    (5/2)*t+(((3-4*σ)/2)+(5/2)*(36-48*σ)) ≤ energyClauseSevenFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_low_tall_1_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 97/127)
    (htlo : 45*σ-33 ≤ t) (hthi : t ≤ 3/2) :
    (0)*t+(((3-4*σ)/2)+(5/2)*(3-3*σ)) ≤ energyClauseSevenFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_low_tall_1_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 97/127 ≤ σ) (hhi : σ ≤ 79/103)
    (htlo : (11*σ-5)/3 ≤ t) (hthi : t ≤ (8*σ-2)/3) :
    (1)*t+((4-4*σ)+(1)*(11/3-(17/3)*σ)) ≤ energyClauseSevenSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_high_tall_0_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 97/127 ≤ σ) (hhi : σ ≤ 79/103)
    (htlo : (8*σ-2)/3 ≤ t) (hthi : t ≤ 3/2) :
    (0)*t+((4-4*σ)+(1)*(3-3*σ)) ≤ energyClauseSevenSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_high_tall_0_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 97/127 ≤ σ) (hhi : σ ≤ 79/103)
    (htlo : (11*σ-5)/3 ≤ t) (hthi : t ≤ (8*σ-2)/3) :
    (5/2)*t+(((3-4*σ)/2)+(5/2)*(11/3-(17/3)*σ)) ≤ energyClauseSevenSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_high_tall_1_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 97/127 ≤ σ) (hhi : σ ≤ 79/103)
    (htlo : (8*σ-2)/3 ≤ t) (hthi : t ≤ 3/2) :
    (0)*t+(((3-4*σ)/2)+(5/2)*(3-3*σ)) ≤ energyClauseSevenSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_high_tall_1_1 σ t hlo hhi htlo hthi

example {σ t r a e : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 97/127)
    (htlo : 1 ≤ t) (hthi : t ≤ 46*σ-34)
    (halo : 1/2 ≤ a) (hahi : a ≤ 2/3)
    (hj : r ≤ max (2-2*σ) (t+(36-48*σ)))
    (i : Fin 9) (hb : e ≤ heathBrownNineBranch σ t r a i) :
    e ≤ energyClauseSevenRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_low_short_branch σ t r a e hlo hhi htlo hthi halo hahi hj i hb

example {σ t r a e : ℝ}
    (hlo : 97/127 ≤ σ) (hhi : σ ≤ 79/103)
    (htlo : 1 ≤ t) (hthi : t ≤ (11*σ-5)/3)
    (halo : 1/2 ≤ a) (hahi : a ≤ 2/3)
    (hj : r ≤ max (2-2*σ) (t+(11/3-(17/3)*σ)))
    (i : Fin 9) (hb : e ≤ heathBrownNineBranch σ t r a i) :
    e ≤ energyClauseSevenRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_high_short_branch σ t r a e hlo hhi htlo hthi halo hahi hj i hb

example {σ t r : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 97/127)
    (htlo : 46*σ-34 ≤ t) (hthi : t ≤ 3/2)
    (hj : r ≤ max (2-2*σ) (t+(36-48*σ))) (hcap : r ≤ 3-3*σ) :
    max (r+4-4*σ) ((3-4*σ+5*r)/2) ≤ energyClauseSevenRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_low_tall_bound σ t r hlo hhi htlo hthi hj hcap

example {σ t r : ℝ}
    (hlo : 97/127 ≤ σ) (hhi : σ ≤ 79/103)
    (htlo : (11*σ-5)/3 ≤ t) (hthi : t ≤ 3/2)
    (hj : r ≤ max (2-2*σ) (t+(11/3-(17/3)*σ))) (hcap : r ≤ 3-3*σ) :
    max (r+4-4*σ) ((3-4*σ+5*r)/2) ≤ energyClauseSevenRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_high_tall_bound σ t r hlo hhi htlo hthi hj hcap

example
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 79/103) (htlo : 2 ≤ τ) (hthi : τ ≤ 4) :
    e ≤ energyClauseSevenRate σ*τ :=
  @TaoTrudgianYang2025.InCardinalityEnergyRegion.energyClauseSeven_general σ τ ρ e h hlo hhi htlo hthi

example {σ τ : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 79/103) (htlo : 2 ≤ τ) (hthi : τ ≤ 4) :
    IsLargeValueEnergyBound σ τ (energyClauseSevenRate σ*τ) :=
  @TaoTrudgianYang2025.energyClauseSeven_general_bound σ τ hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 79/103)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((1)*2+(0))*t+((4-4*σ)+(1)*(6-12*σ)) ≤ energyClauseSevenSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_zeta_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 42/55 ≤ σ) (_hhi : σ ≤ 79/103)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((5/2)*2+(0))*t+(((3-4*σ)/2)+(5/2)*(6-12*σ)) ≤ energyClauseSevenSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_zeta_1 σ t hlo _hhi htlo hthi

example {σ t : ℝ}
    (hlo : 42/55 ≤ σ) (_hhi : σ ≤ 79/103)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((8/5)*2+(2/5))*t+(((12-16*σ)/5)+(8/5)*(6-12*σ)) ≤ energyClauseSevenSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_zeta_2 σ t hlo _hhi htlo hthi

example {σ t : ℝ}
    (hlo : 42/55 ≤ σ) (_hhi : σ ≤ 79/103)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((2)*2+(0))*t+((3-4*σ)+(2)*(6-12*σ)) ≤ energyClauseSevenSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_zeta_3 σ t hlo _hhi htlo hthi

example {σ t : ℝ}
    (hlo : 42/55 ≤ σ) (_hhi : σ ≤ 79/103)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((3)*2+(0))*t+((1-2*σ)+(3)*(6-12*σ)) ≤ energyClauseSevenSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_zeta_4 σ t hlo _hhi htlo hthi

example {σ t : ℝ}
    (hlo : 42/55 ≤ σ) (_hhi : σ ≤ 79/103)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((12/5)*2+(2/5))*t+(((8-16*σ)/5)+(12/5)*(6-12*σ)) ≤ energyClauseSevenSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_zeta_5 σ t hlo _hhi htlo hthi

example {σ t : ℝ}
    (hlo : 42/55 ≤ σ) (_hhi : σ ≤ 79/103)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((5/4)*2+(1/2))*t+((3-4*σ)+(5/4)*(6-12*σ)) ≤ energyClauseSevenSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_zeta_6 σ t hlo _hhi htlo hthi

example {σ t : ℝ}
    (hlo : 42/55 ≤ σ) (_hhi : σ ≤ 79/103)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((21/8)*2+(1/4))*t+((1-2*σ)+(21/8)*(6-12*σ)) ≤ energyClauseSevenSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_zeta_7 σ t hlo _hhi htlo hthi

example {σ t : ℝ}
    (hlo : 42/55 ≤ σ) (_hhi : σ ≤ 79/103)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((9/5)*2+(4/5))*t+(((8-16*σ)/5)+(9/5)*(6-12*σ)) ≤ energyClauseSevenSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_zeta_8 σ t hlo _hhi htlo hthi

example {σ t r : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 79/103)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) (hr : r ≤ 2*t-12*(σ-1/2)) (i : Fin 9) :
    heathBrownNineBranch σ t r 1 i ≤ energyClauseSevenRate σ*t :=
  @TaoTrudgianYang2025.energyClauseSeven_zeta_branch σ t r hlo hhi htlo hthi hr i

example
    {σ τ ρ e s : ℝ} (h : InZetaLargeValueEnergyRegion σ τ ρ e s)
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 79/103) (htlo : 3/2 ≤ τ) (hthi : τ ≤ 2) :
    e ≤ energyClauseSevenRate σ*τ :=
  @TaoTrudgianYang2025.InZetaLargeValueEnergyRegion.energyClauseSeven σ τ ρ e s h hlo hhi htlo hthi

example {σ τ : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 79/103) (htlo : 1 ≤ τ) (hthi : τ ≤ 2) :
    IsZetaLargeValueEnergyBound σ τ (energyClauseSevenRate σ*τ) :=
  @TaoTrudgianYang2025.energyClauseSeven_short_zeta σ τ hlo hhi htlo hthi

example {σ : ℝ} (hlo : 42/55 ≤ σ) (hhi : σ ≤ 79/103) :
    IsZeroDensityEnergyBound σ (energyClauseSevenRate σ/(1-σ)) :=
  @TaoTrudgianYang2025.energyClauseSeven σ hlo hhi

example {σ : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 79/103) :
    zeroDensityEnergyExponent σ ≤
      ((max ((18-19*σ)/(6*(15*σ-11)*(1-σ)))
        (3*(18-19*σ)/(4*(4*σ-1)*(1-σ))) : ℝ) : EReal) :=
  @TaoTrudgianYang2025.energyClauseSeven_blueprint σ hlo hhi

example {σ : ℝ} (hlo : 42/55 ≤ σ) (hhi : σ ≤ 79/103) :
    IsZeroDensityEnergyBound σ
      ((max ((18-19*σ)/(6*(15*σ-11))) (3*(18-19*σ)/(4*(4*σ-1))))/(1-σ)) :=
  @TaoTrudgianYang2025.add_est_vii_bound σ hlo hhi

example {σ : ℝ} (hlo : 42/55 ≤ σ) (hhi : σ ≤ 79/103) :
    zeroDensityEnergyExponent σ*((1-σ : ℝ) : EReal) ≤
      ((max ((18-19*σ)/(6*(15*σ-11))) (3*(18-19*σ)/(4*(4*σ-1))) : ℝ) : EReal) :=
  @TaoTrudgianYang2025.add_est_vii σ hlo hhi

example {σ : ℝ} (hlo : 42/55 ≤ σ) (hhi : σ ≤ 79/103) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ T : ℝ, C ≤ T →
        (zeroAdditiveEnergy (σ-δ) T : ℝ) ≤ C*T^
          ((max ((18-19*σ)/(6*(15*σ-11))) (3*(18-19*σ)/(4*(4*σ-1))))+ε) :=
  @TaoTrudgianYang2025.add_est_vii_zero_energy σ hlo hhi

-- Both closed paper endpoints are consumed by the literal public theorem.
example :
    zeroDensityEnergyExponent (42/55)*((1-(42/55) : ℝ) : EReal) ≤
      ((max ((18-19*(42/55))/(6*(15*(42/55)-11)))
        (3*(18-19*(42/55))/(4*(4*(42/55)-1))) : ℝ) : EReal) :=
  add_est_vii (by norm_num) (by norm_num)

-- Both closed paper endpoints are consumed by the literal public theorem.
example :
    zeroDensityEnergyExponent (79/103)*((1-(79/103) : ℝ) : EReal) ≤
      ((max ((18-19*(79/103))/(6*(15*(79/103)-11)))
        (3*(18-19*(79/103))/(4*(4*(79/103)-1))) : ℝ) : EReal) :=
  add_est_vii (by norm_num) (by norm_num)

-- The literal blueprint normalization also includes both endpoints.
example :
    zeroDensityEnergyExponent (42/55) ≤
      ((max ((18-19*(42/55))/(6*(15*(42/55)-11)*(1-(42/55))))
        (3*(18-19*(42/55))/(4*(4*(42/55)-1)*(1-(42/55)))) : ℝ) : EReal) :=
  energyClauseSeven_blueprint (by norm_num) (by norm_num)

-- The literal blueprint normalization also includes both endpoints.
example :
    zeroDensityEnergyExponent (79/103) ≤
      ((max ((18-19*(79/103))/(6*(15*(79/103)-11)*(1-(79/103))))
        (3*(18-19*(79/103))/(4*(4*(79/103)-1)*(1-(79/103)))) : ℝ) : EReal) :=
  energyClauseSeven_blueprint (by norm_num) (by norm_num)

example (t : ℝ) :
    t+11/3-(17/3)*(97/127) = t+36-48*(97/127) := by ring

example :
    energyClauseSevenFirstRate (97/127) = energyClauseSevenSecondRate (97/127) := by
  norm_num [energyClauseSevenFirstRate,energyClauseSevenSecondRate]

example :
    (42/55 : ℝ) ≤ 97/127 ∧ (97/127 : ℝ) ≤ 79/103 := by norm_num

example {σ : ℝ} (hlo : 42/55 ≤ σ) (hhi : σ ≤ 97/127) :
    1 ≤ 46*σ-34 ∧ 46*σ-34 ≤ 45*σ-33 ∧ 45*σ-33 ≤ 3/2 := by
  constructor
  · linarith
  constructor <;> linarith

example (σ : ℝ) :
    (46*σ-34)+(36-48*σ) = 2-2*σ := by ring

example (σ : ℝ) :
    (45*σ-33)+(36-48*σ) = 3-3*σ := by ring

-- The actual second q-energy branch realizes this printed rate.
example {σ : ℝ} (hlo : 42/55 ≤ σ) :
    (3-4*σ+5*(3-3*σ))/2 = energyClauseSevenFirstRate σ*(45*σ-33) := by
  have hne : 6*(15*σ-11) ≠ 0 := by linarith
  unfold energyClauseSevenFirstRate
  conv_rhs =>
    rw [show 45*σ-33 = (6*(15*σ-11))/2 by ring,
      ← mul_div_assoc, div_mul_cancel₀ _ hne]
  ring

example {σ : ℝ} (hlo : 97/127 ≤ σ) (hhi : σ ≤ 79/103) :
    1 ≤ (11*σ-5)/3 ∧ (11*σ-5)/3 ≤ (8*σ-2)/3 ∧ (8*σ-2)/3 ≤ 3/2 := by
  constructor
  · linarith
  constructor <;> linarith

example (σ : ℝ) :
    ((11*σ-5)/3)+(11/3-(17/3)*σ) = 2-2*σ := by ring

example (σ : ℝ) :
    ((8*σ-2)/3)+(11/3-(17/3)*σ) = 3-3*σ := by ring

-- The actual second q-energy branch realizes this printed rate.
example {σ : ℝ} (hlo : 42/55 ≤ σ) :
    (3-4*σ+5*(3-3*σ))/2 = energyClauseSevenSecondRate σ*((8*σ-2)/3) := by
  have hne : 4*(4*σ-1) ≠ 0 := by linarith
  unfold energyClauseSevenSecondRate
  conv_rhs =>
    rw [show (8*σ-2)/3 = (4*(4*σ-1))/6 by ring,
      ← mul_div_assoc, div_mul_cancel₀ _ hne]
  ring

example {σ ρ e : ℝ} (h : InCardinalityEnergyRegion σ 2 ρ e)
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 79/103) :
    e ≤ energyClauseSevenRate σ*2 :=
  h.energyClauseSeven_general hlo hhi (by norm_num) (by norm_num)

example {σ ρ e : ℝ} (h : InCardinalityEnergyRegion σ 3 ρ e)
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 79/103) :
    e ≤ energyClauseSevenRate σ*3 :=
  h.energyClauseSeven_general hlo hhi (by norm_num) (by norm_num)

example {σ ρ e : ℝ} (h : InCardinalityEnergyRegion σ 4 ρ e)
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 79/103) :
    e ≤ energyClauseSevenRate σ*4 :=
  h.energyClauseSeven_general hlo hhi (by norm_num) (by norm_num)

example {σ : ℝ} (hlo : 42/55 ≤ σ) (hhi : σ ≤ 79/103) :
    IsZetaLargeValueEnergyBound σ 1 (energyClauseSevenRate σ*1) :=
  energyClauseSeven_short_zeta hlo hhi (by norm_num) (by norm_num)

example {σ : ℝ} (hlo : 42/55 ≤ σ) (hhi : σ ≤ 79/103) :
    IsZetaLargeValueEnergyBound σ (3/2) (energyClauseSevenRate σ*(3/2)) :=
  energyClauseSeven_short_zeta hlo hhi (by norm_num) (by norm_num)

example {σ : ℝ} (hlo : 42/55 ≤ σ) (hhi : σ ≤ 79/103) :
    IsZetaLargeValueEnergyBound σ 2 (energyClauseSevenRate σ*2) :=
  energyClauseSeven_short_zeta hlo hhi (by norm_num) (by norm_num)

-- Cardinality at q+1 and energy at q-1 come from independent witnesses.
example {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e) :
    ρ/3 ≤ jutilaLargeValueExponent 6 σ (τ/3) ∧
      ∃ i : Fin 9, e/2 ≤ heathBrownNineBranch σ (τ/2) (ρ/2) (1/2) i := by
  constructor
  · exact h.jutila_cardinality_powered 3 6 (by norm_num) (by norm_num)
  · simpa using h.heathBrown_nine_branches_powered 2 1 (by norm_num) (by norm_num)

-- Cardinality at q+1 and energy at q-1 come from independent witnesses.
example {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e) :
    ρ/4 ≤ jutilaLargeValueExponent 6 σ (τ/4) ∧
      ∃ i : Fin 9, e/3 ≤ heathBrownNineBranch σ (τ/3) (ρ/3) (2/3) i := by
  constructor
  · exact h.jutila_cardinality_powered 4 6 (by norm_num) (by norm_num)
  · simpa using h.heathBrown_nine_branches_powered 3 2 (by norm_num) (by norm_num)

-- The fifth coordinate is existentially projected, never scaled.
example {σ τ ρ e s : ℝ} (h : InLargeValueEnergyRegion σ τ ρ e s)
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 79/103) (htlo : 2 ≤ τ) (hthi : τ ≤ 4) :
    e ≤ energyClauseSevenRate σ*τ :=
  (show InCardinalityEnergyRegion σ τ ρ e from ⟨s,h⟩).energyClauseSeven_general
    hlo hhi htlo hthi

-- Branch 2 has a negative power coefficient: its upper endpoint is a=1/2.
example {σ t r a : ℝ} (hlo : 42/55 ≤ σ) (hhi : σ ≤ 79/103)
    (halo : 1/2 ≤ a) (hahi : a ≤ 2/3) :
    heathBrownNineBranch σ t r a 2 ≤ heathBrownNineBranch σ t r (1/2) 2 := by
  simpa using heathBrownNineBranch_le_extreme_power
    (by linarith : 3/4 ≤ σ) (by linarith : σ ≤ 1) halo hahi (2 : Fin 9)

end AddEstSeventhRegression

namespace AddEstEighthRegression

open TaoTrudgianYang2025

example (σ t : ℝ) :
    jutilaLargeValueExponent 5 σ t =
      max (2-2*σ) (max (t+18/5-(28/5)*σ) (t+30-40*σ)) :=
  @TaoTrudgianYang2025.jutila_five_formula σ t

example
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (q : ℕ) (hq : 1 ≤ q) :
    ρ/q ≤ max (2-2*σ) (max (τ/q+18/5-(28/5)*σ) (τ/q+30-40*σ)) :=
  @TaoTrudgianYang2025.InCardinalityEnergyRegion.jutila_five_cardinality_powered σ τ ρ e h q hq

example {σ t : ℝ} (hσ : σ ≤ 33/43) :
    max (2-2*σ) (max (t+18/5-(28/5)*σ) (t+30-40*σ)) =
      max (2-2*σ) (t+30-40*σ) :=
  @TaoTrudgianYang2025.jutila_five_low_sigma σ t hσ

example {σ t : ℝ} (hσ : 33/43 ≤ σ) :
    max (2-2*σ) (max (t+18/5-(28/5)*σ) (t+30-40*σ)) =
      max (2-2*σ) (t+18/5-(28/5)*σ) :=
  @TaoTrudgianYang2025.jutila_five_high_sigma σ t hσ

example {σ t : ℝ}
    (hσ : 79/103 ≤ σ) (ht : t ≤ 1) :
    max (2-2*σ) (max (t+18/5-(28/5)*σ) (t+30-40*σ)) = 2-2*σ :=
  @TaoTrudgianYang2025.jutila_five_at_most_one σ t hσ ht

example
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 84/109)
    (q : ℕ) (hq : q=2 ∨ q=3) (htlo : (q : ℝ) ≤ τ) (hthi : τ ≤ q+1) :
    1 ≤ τ/q ∧ τ/q ≤ 3/2 ∧
      ρ/q ≤ max (2-2*σ) (max (τ/q+18/5-(28/5)*σ) (τ/q+30-40*σ)) ∧
      ρ/q ≤ 3-3*σ :=
  @TaoTrudgianYang2025.InCardinalityEnergyRegion.energyClauseEight_cardinality_caps σ τ ρ e h hlo hhi q hq htlo hthi

example (σ : ℝ) :
    energyClauseEightRate σ =
      max ((18-19*σ)/(2*(37*σ-27))) (5*(18-19*σ)/(2*(13*σ-3))) :=
  @TaoTrudgianYang2025.energyClauseEightRate_eq_printed σ

example (σ : ℝ) :
    energyClauseEightFirstRate σ ≤ energyClauseEightRate σ :=
  @TaoTrudgianYang2025.energyClauseEightFirstRate_le σ

example (σ : ℝ) :
    energyClauseEightSecondRate σ ≤ energyClauseEightRate σ :=
  @TaoTrudgianYang2025.energyClauseEightSecondRate_le σ

example {σ : ℝ} (hlo : 79/103 ≤ σ) :
    0 < 2*(37*σ-27) ∧ 0 < 2*(13*σ-3) :=
  @TaoTrudgianYang2025.energyClauseEight_printed_denominators_pos σ hlo

example {σ : ℝ}
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 84/109) :
    0 < energyClauseEightRate σ :=
  @TaoTrudgianYang2025.energyClauseEightRate_pos σ hlo hhi

example {σ : ℝ} (hhi : σ ≤ 84/109) :
    energyClauseEightRate σ/(1-σ) =
      max ((18-19*σ)/(2*(37*σ-27)*(1-σ)))
        (5*(18-19*σ)/(2*(13*σ-3)*(1-σ))) :=
  @TaoTrudgianYang2025.energyClauseEightRate_div_eq_blueprint σ hhi

example {σ t : ℝ}
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 33/43)
    (htlo : 1 ≤ t) (hthi : t ≤ 38*σ-28) :
    (0)*t+((4-4*σ)*(2/3)+(1)*(2-2*σ)) ≤ energyClauseEightFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_low_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 33/43)
    (htlo : 1 ≤ t) (hthi : t ≤ 38*σ-28) :
    (0)*t+(((3-4*σ)/2)*(1/2)+(5/2)*(2-2*σ)) ≤ energyClauseEightFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_low_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 33/43)
    (htlo : 1 ≤ t) (hthi : t ≤ 38*σ-28) :
    (2/5)*t+(((12-16*σ)/5)*(1/2)+(8/5)*(2-2*σ)) ≤ energyClauseEightFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_low_2 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 33/43)
    (htlo : 1 ≤ t) (hthi : t ≤ 38*σ-28) :
    (0)*t+((3-4*σ)*(1/2)+(2)*(2-2*σ)) ≤ energyClauseEightFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_low_3 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 33/43)
    (htlo : 1 ≤ t) (hthi : t ≤ 38*σ-28) :
    (0)*t+((1-2*σ)*(1/2)+(3)*(2-2*σ)) ≤ energyClauseEightFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_low_4 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 33/43)
    (htlo : 1 ≤ t) (hthi : t ≤ 38*σ-28) :
    (2/5)*t+(((8-16*σ)/5)*(1/2)+(12/5)*(2-2*σ)) ≤ energyClauseEightFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_low_5 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 33/43)
    (htlo : 1 ≤ t) (hthi : t ≤ 38*σ-28) :
    (1/2)*t+((3-4*σ)*(1/2)+(5/4)*(2-2*σ)) ≤ energyClauseEightFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_low_6 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 33/43)
    (htlo : 1 ≤ t) (hthi : t ≤ 38*σ-28) :
    (1/4)*t+((1-2*σ)*(1/2)+(21/8)*(2-2*σ)) ≤ energyClauseEightFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_low_7 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 33/43)
    (htlo : 1 ≤ t) (hthi : t ≤ 38*σ-28) :
    (4/5)*t+(((8-16*σ)/5)*(1/2)+(9/5)*(2-2*σ)) ≤ energyClauseEightFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_low_8 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 33/43 ≤ σ) (hhi : σ ≤ 84/109)
    (htlo : 1 ≤ t) (hthi : t ≤ (18*σ-8)/5) :
    (0)*t+((4-4*σ)*(2/3)+(1)*(2-2*σ)) ≤ energyClauseEightSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_high_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 33/43 ≤ σ) (hhi : σ ≤ 84/109)
    (htlo : 1 ≤ t) (hthi : t ≤ (18*σ-8)/5) :
    (0)*t+(((3-4*σ)/2)*(1/2)+(5/2)*(2-2*σ)) ≤ energyClauseEightSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_high_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 33/43 ≤ σ) (hhi : σ ≤ 84/109)
    (htlo : 1 ≤ t) (hthi : t ≤ (18*σ-8)/5) :
    (2/5)*t+(((12-16*σ)/5)*(1/2)+(8/5)*(2-2*σ)) ≤ energyClauseEightSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_high_2 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 33/43 ≤ σ) (hhi : σ ≤ 84/109)
    (htlo : 1 ≤ t) (hthi : t ≤ (18*σ-8)/5) :
    (0)*t+((3-4*σ)*(1/2)+(2)*(2-2*σ)) ≤ energyClauseEightSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_high_3 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 33/43 ≤ σ) (hhi : σ ≤ 84/109)
    (htlo : 1 ≤ t) (hthi : t ≤ (18*σ-8)/5) :
    (0)*t+((1-2*σ)*(1/2)+(3)*(2-2*σ)) ≤ energyClauseEightSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_high_4 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 33/43 ≤ σ) (hhi : σ ≤ 84/109)
    (htlo : 1 ≤ t) (hthi : t ≤ (18*σ-8)/5) :
    (2/5)*t+(((8-16*σ)/5)*(1/2)+(12/5)*(2-2*σ)) ≤ energyClauseEightSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_high_5 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 33/43 ≤ σ) (hhi : σ ≤ 84/109)
    (htlo : 1 ≤ t) (hthi : t ≤ (18*σ-8)/5) :
    (1/2)*t+((3-4*σ)*(1/2)+(5/4)*(2-2*σ)) ≤ energyClauseEightSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_high_6 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 33/43 ≤ σ) (hhi : σ ≤ 84/109)
    (htlo : 1 ≤ t) (hthi : t ≤ (18*σ-8)/5) :
    (1/4)*t+((1-2*σ)*(1/2)+(21/8)*(2-2*σ)) ≤ energyClauseEightSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_high_7 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 33/43 ≤ σ) (hhi : σ ≤ 84/109)
    (htlo : 1 ≤ t) (hthi : t ≤ (18*σ-8)/5) :
    (4/5)*t+(((8-16*σ)/5)*(1/2)+(9/5)*(2-2*σ)) ≤ energyClauseEightSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_high_8 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 33/43)
    (htlo : 38*σ-28 ≤ t) (hthi : t ≤ 37*σ-27) :
    (1)*t+((4-4*σ)+(1)*(30-40*σ)) ≤ energyClauseEightFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_low_tall_0_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 33/43)
    (htlo : 37*σ-27 ≤ t) (hthi : t ≤ 3/2) :
    (0)*t+((4-4*σ)+(1)*(3-3*σ)) ≤ energyClauseEightFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_low_tall_0_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 33/43)
    (htlo : 38*σ-28 ≤ t) (hthi : t ≤ 37*σ-27) :
    (5/2)*t+(((3-4*σ)/2)+(5/2)*(30-40*σ)) ≤ energyClauseEightFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_low_tall_1_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 33/43)
    (htlo : 37*σ-27 ≤ t) (hthi : t ≤ 3/2) :
    (0)*t+(((3-4*σ)/2)+(5/2)*(3-3*σ)) ≤ energyClauseEightFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_low_tall_1_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 33/43 ≤ σ) (hhi : σ ≤ 84/109)
    (htlo : (18*σ-8)/5 ≤ t) (hthi : t ≤ (13*σ-3)/5) :
    (1)*t+((4-4*σ)+(1)*(18/5-(28/5)*σ)) ≤ energyClauseEightSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_high_tall_0_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 33/43 ≤ σ) (hhi : σ ≤ 84/109)
    (htlo : (13*σ-3)/5 ≤ t) (hthi : t ≤ 3/2) :
    (0)*t+((4-4*σ)+(1)*(3-3*σ)) ≤ energyClauseEightSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_high_tall_0_1 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 33/43 ≤ σ) (hhi : σ ≤ 84/109)
    (htlo : (18*σ-8)/5 ≤ t) (hthi : t ≤ (13*σ-3)/5) :
    (5/2)*t+(((3-4*σ)/2)+(5/2)*(18/5-(28/5)*σ)) ≤ energyClauseEightSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_high_tall_1_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 33/43 ≤ σ) (hhi : σ ≤ 84/109)
    (htlo : (13*σ-3)/5 ≤ t) (hthi : t ≤ 3/2) :
    (0)*t+(((3-4*σ)/2)+(5/2)*(3-3*σ)) ≤ energyClauseEightSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_high_tall_1_1 σ t hlo hhi htlo hthi

example {σ t r a e : ℝ}
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 33/43)
    (htlo : 1 ≤ t) (hthi : t ≤ 38*σ-28)
    (halo : 1/2 ≤ a) (hahi : a ≤ 2/3)
    (hj : r ≤ max (2-2*σ) (t+(30-40*σ)))
    (i : Fin 9) (hb : e ≤ heathBrownNineBranch σ t r a i) :
    e ≤ energyClauseEightRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_low_short_branch σ t r a e hlo hhi htlo hthi halo hahi hj i hb

example {σ t r a e : ℝ}
    (hlo : 33/43 ≤ σ) (hhi : σ ≤ 84/109)
    (htlo : 1 ≤ t) (hthi : t ≤ (18*σ-8)/5)
    (halo : 1/2 ≤ a) (hahi : a ≤ 2/3)
    (hj : r ≤ max (2-2*σ) (t+(18/5-(28/5)*σ)))
    (i : Fin 9) (hb : e ≤ heathBrownNineBranch σ t r a i) :
    e ≤ energyClauseEightRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_high_short_branch σ t r a e hlo hhi htlo hthi halo hahi hj i hb

example {σ t r : ℝ}
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 33/43)
    (htlo : 38*σ-28 ≤ t) (hthi : t ≤ 3/2)
    (hj : r ≤ max (2-2*σ) (t+(30-40*σ))) (hcap : r ≤ 3-3*σ) :
    max (r+4-4*σ) ((3-4*σ+5*r)/2) ≤ energyClauseEightRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_low_tall_bound σ t r hlo hhi htlo hthi hj hcap

example {σ t r : ℝ}
    (hlo : 33/43 ≤ σ) (hhi : σ ≤ 84/109)
    (htlo : (18*σ-8)/5 ≤ t) (hthi : t ≤ 3/2)
    (hj : r ≤ max (2-2*σ) (t+(18/5-(28/5)*σ))) (hcap : r ≤ 3-3*σ) :
    max (r+4-4*σ) ((3-4*σ+5*r)/2) ≤ energyClauseEightRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_high_tall_bound σ t r hlo hhi htlo hthi hj hcap

example
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 84/109) (htlo : 2 ≤ τ) (hthi : τ ≤ 4) :
    e ≤ energyClauseEightRate σ*τ :=
  @TaoTrudgianYang2025.InCardinalityEnergyRegion.energyClauseEight_general σ τ ρ e h hlo hhi htlo hthi

example {σ τ : ℝ}
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 84/109) (htlo : 2 ≤ τ) (hthi : τ ≤ 4) :
    IsLargeValueEnergyBound σ τ (energyClauseEightRate σ*τ) :=
  @TaoTrudgianYang2025.energyClauseEight_general_bound σ τ hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 84/109)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((1)*2+(0))*t+((4-4*σ)+(1)*(6-12*σ)) ≤ energyClauseEightSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_zeta_0 σ t hlo hhi htlo hthi

example {σ t : ℝ}
    (hlo : 79/103 ≤ σ) (_hhi : σ ≤ 84/109)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((5/2)*2+(0))*t+(((3-4*σ)/2)+(5/2)*(6-12*σ)) ≤ energyClauseEightSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_zeta_1 σ t hlo _hhi htlo hthi

example {σ t : ℝ}
    (hlo : 79/103 ≤ σ) (_hhi : σ ≤ 84/109)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((8/5)*2+(2/5))*t+(((12-16*σ)/5)+(8/5)*(6-12*σ)) ≤ energyClauseEightSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_zeta_2 σ t hlo _hhi htlo hthi

example {σ t : ℝ}
    (hlo : 79/103 ≤ σ) (_hhi : σ ≤ 84/109)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((2)*2+(0))*t+((3-4*σ)+(2)*(6-12*σ)) ≤ energyClauseEightSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_zeta_3 σ t hlo _hhi htlo hthi

example {σ t : ℝ}
    (hlo : 79/103 ≤ σ) (_hhi : σ ≤ 84/109)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((3)*2+(0))*t+((1-2*σ)+(3)*(6-12*σ)) ≤ energyClauseEightSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_zeta_4 σ t hlo _hhi htlo hthi

example {σ t : ℝ}
    (hlo : 79/103 ≤ σ) (_hhi : σ ≤ 84/109)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((12/5)*2+(2/5))*t+(((8-16*σ)/5)+(12/5)*(6-12*σ)) ≤ energyClauseEightSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_zeta_5 σ t hlo _hhi htlo hthi

example {σ t : ℝ}
    (hlo : 79/103 ≤ σ) (_hhi : σ ≤ 84/109)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((5/4)*2+(1/2))*t+((3-4*σ)+(5/4)*(6-12*σ)) ≤ energyClauseEightSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_zeta_6 σ t hlo _hhi htlo hthi

example {σ t : ℝ}
    (hlo : 79/103 ≤ σ) (_hhi : σ ≤ 84/109)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((21/8)*2+(1/4))*t+((1-2*σ)+(21/8)*(6-12*σ)) ≤ energyClauseEightSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_zeta_7 σ t hlo _hhi htlo hthi

example {σ t : ℝ}
    (hlo : 79/103 ≤ σ) (_hhi : σ ≤ 84/109)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) :
    ((9/5)*2+(4/5))*t+(((8-16*σ)/5)+(9/5)*(6-12*σ)) ≤ energyClauseEightSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_zeta_8 σ t hlo _hhi htlo hthi

example {σ t r : ℝ}
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 84/109)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 2) (hr : r ≤ 2*t-12*(σ-1/2)) (i : Fin 9) :
    heathBrownNineBranch σ t r 1 i ≤ energyClauseEightRate σ*t :=
  @TaoTrudgianYang2025.energyClauseEight_zeta_branch σ t r hlo hhi htlo hthi hr i

example
    {σ τ ρ e s : ℝ} (h : InZetaLargeValueEnergyRegion σ τ ρ e s)
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 84/109) (htlo : 3/2 ≤ τ) (hthi : τ ≤ 2) :
    e ≤ energyClauseEightRate σ*τ :=
  @TaoTrudgianYang2025.InZetaLargeValueEnergyRegion.energyClauseEight σ τ ρ e s h hlo hhi htlo hthi

example {σ τ : ℝ}
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 84/109) (htlo : 1 ≤ τ) (hthi : τ ≤ 2) :
    IsZetaLargeValueEnergyBound σ τ (energyClauseEightRate σ*τ) :=
  @TaoTrudgianYang2025.energyClauseEight_short_zeta σ τ hlo hhi htlo hthi

example {σ : ℝ} (hlo : 79/103 ≤ σ) (hhi : σ ≤ 84/109) :
    IsZeroDensityEnergyBound σ (energyClauseEightRate σ/(1-σ)) :=
  @TaoTrudgianYang2025.energyClauseEight σ hlo hhi

example {σ : ℝ}
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 84/109) :
    zeroDensityEnergyExponent σ ≤
      ((max ((18-19*σ)/(2*(37*σ-27)*(1-σ)))
        (5*(18-19*σ)/(2*(13*σ-3)*(1-σ))) : ℝ) : EReal) :=
  @TaoTrudgianYang2025.energyClauseEight_blueprint σ hlo hhi

example {σ : ℝ} (hlo : 79/103 ≤ σ) (hhi : σ ≤ 84/109) :
    IsZeroDensityEnergyBound σ
      ((max ((18-19*σ)/(2*(37*σ-27))) (5*(18-19*σ)/(2*(13*σ-3))))/(1-σ)) :=
  @TaoTrudgianYang2025.add_est_viii_bound σ hlo hhi

example {σ : ℝ} (hlo : 79/103 ≤ σ) (hhi : σ ≤ 84/109) :
    zeroDensityEnergyExponent σ*((1-σ : ℝ) : EReal) ≤
      ((max ((18-19*σ)/(2*(37*σ-27))) (5*(18-19*σ)/(2*(13*σ-3))) : ℝ) : EReal) :=
  @TaoTrudgianYang2025.add_est_viii σ hlo hhi

example {σ : ℝ} (hlo : 79/103 ≤ σ) (hhi : σ ≤ 84/109) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ T : ℝ, C ≤ T →
        (zeroAdditiveEnergy (σ-δ) T : ℝ) ≤ C*T^
          ((max ((18-19*σ)/(2*(37*σ-27))) (5*(18-19*σ)/(2*(13*σ-3))))+ε) :=
  @TaoTrudgianYang2025.add_est_viii_zero_energy σ hlo hhi

-- Both closed paper endpoints are consumed by the literal public theorem.
example :
    zeroDensityEnergyExponent (79/103)*((1-(79/103) : ℝ) : EReal) ≤
      ((max ((18-19*(79/103))/(2*(37*(79/103)-27)))
        (5*(18-19*(79/103))/(2*(13*(79/103)-3))) : ℝ) : EReal) :=
  add_est_viii (σ := 79/103) (by norm_num) (by norm_num)

-- Both closed paper endpoints are consumed by the literal public theorem.
example :
    zeroDensityEnergyExponent (84/109)*((1-(84/109) : ℝ) : EReal) ≤
      ((max ((18-19*(84/109))/(2*(37*(84/109)-27)))
        (5*(18-19*(84/109))/(2*(13*(84/109)-3))) : ℝ) : EReal) :=
  add_est_viii (σ := 84/109) (by norm_num) (by norm_num)

-- The literal blueprint normalization also includes both endpoints.
example :
    zeroDensityEnergyExponent (79/103) ≤
      ((max ((18-19*(79/103))/(2*(37*(79/103)-27)*(1-(79/103))))
        (5*(18-19*(79/103))/(2*(13*(79/103)-3)*(1-(79/103)))) : ℝ) : EReal) :=
  energyClauseEight_blueprint (σ := 79/103) (by norm_num) (by norm_num)

-- The literal blueprint normalization also includes both endpoints.
example :
    zeroDensityEnergyExponent (84/109) ≤
      ((max ((18-19*(84/109))/(2*(37*(84/109)-27)*(1-(84/109))))
        (5*(18-19*(84/109))/(2*(13*(84/109)-3)*(1-(84/109)))) : ℝ) : EReal) :=
  energyClauseEight_blueprint (σ := 84/109) (by norm_num) (by norm_num)

example (t : ℝ) :
    t+18/5-(28/5)*(33/43) = t+30-40*(33/43) := by ring

example :
    energyClauseEightFirstRate (33/43) = energyClauseEightSecondRate (33/43) := by
  norm_num [energyClauseEightFirstRate,energyClauseEightSecondRate]

example :
    (79/103 : ℝ) ≤ 33/43 ∧ (33/43 : ℝ) ≤ 84/109 := by norm_num

example {σ : ℝ} (hlo : 79/103 ≤ σ) (hhi : σ ≤ 33/43) :
    1 ≤ 38*σ-28 ∧ 38*σ-28 ≤ 37*σ-27 ∧ 37*σ-27 ≤ 3/2 := by
  constructor
  · linarith
  constructor <;> linarith

example (σ : ℝ) :
    (38*σ-28)+(30-40*σ) = 2-2*σ := by ring

example (σ : ℝ) :
    (37*σ-27)+(30-40*σ) = 3-3*σ := by ring

-- The actual second q-energy branch realizes this printed rate.
example {σ : ℝ} (hlo : 79/103 ≤ σ) :
    (3-4*σ+5*(3-3*σ))/2 = energyClauseEightFirstRate σ*(37*σ-27) := by
  have hne : 37*σ-27 ≠ 0 := by linarith
  unfold energyClauseEightFirstRate
  conv_rhs => rw [← div_div, div_mul_cancel₀ _ hne]
  ring

example {σ : ℝ} (hlo : 33/43 ≤ σ) (hhi : σ ≤ 84/109) :
    1 ≤ (18*σ-8)/5 ∧ (18*σ-8)/5 ≤ (13*σ-3)/5 ∧ (13*σ-3)/5 ≤ 3/2 := by
  constructor
  · linarith
  constructor <;> linarith

example (σ : ℝ) :
    ((18*σ-8)/5)+(18/5-(28/5)*σ) = 2-2*σ := by ring

example (σ : ℝ) :
    ((13*σ-3)/5)+(18/5-(28/5)*σ) = 3-3*σ := by ring

-- The actual second q-energy branch realizes this printed rate.
example {σ : ℝ} (hlo : 79/103 ≤ σ) :
    (3-4*σ+5*(3-3*σ))/2 = energyClauseEightSecondRate σ*((13*σ-3)/5) := by
  have hne : 2*(13*σ-3) ≠ 0 := by linarith
  unfold energyClauseEightSecondRate
  conv_rhs =>
    rw [show (13*σ-3)/5 = (2*(13*σ-3))/10 by ring,
      ← mul_div_assoc, div_mul_cancel₀ _ hne]
  ring

example {σ ρ e : ℝ} (h : InCardinalityEnergyRegion σ 2 ρ e)
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 84/109) :
    e ≤ energyClauseEightRate σ*2 :=
  h.energyClauseEight_general hlo hhi (by norm_num) (by norm_num)

example {σ ρ e : ℝ} (h : InCardinalityEnergyRegion σ 3 ρ e)
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 84/109) :
    e ≤ energyClauseEightRate σ*3 :=
  h.energyClauseEight_general hlo hhi (by norm_num) (by norm_num)

example {σ ρ e : ℝ} (h : InCardinalityEnergyRegion σ 4 ρ e)
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 84/109) :
    e ≤ energyClauseEightRate σ*4 :=
  h.energyClauseEight_general hlo hhi (by norm_num) (by norm_num)

example {σ : ℝ} (hlo : 79/103 ≤ σ) (hhi : σ ≤ 84/109) :
    IsZetaLargeValueEnergyBound σ 1 (energyClauseEightRate σ*1) :=
  energyClauseEight_short_zeta hlo hhi (by norm_num) (by norm_num)

example {σ : ℝ} (hlo : 79/103 ≤ σ) (hhi : σ ≤ 84/109) :
    IsZetaLargeValueEnergyBound σ (3/2) (energyClauseEightRate σ*(3/2)) :=
  energyClauseEight_short_zeta hlo hhi (by norm_num) (by norm_num)

example {σ : ℝ} (hlo : 79/103 ≤ σ) (hhi : σ ≤ 84/109) :
    IsZetaLargeValueEnergyBound σ 2 (energyClauseEightRate σ*2) :=
  energyClauseEight_short_zeta hlo hhi (by norm_num) (by norm_num)

-- Cardinality at q+1 and energy at q-1 come from independent witnesses.
example {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e) :
    ρ/3 ≤ jutilaLargeValueExponent 5 σ (τ/3) ∧
      ∃ i : Fin 9, e/2 ≤ heathBrownNineBranch σ (τ/2) (ρ/2) (1/2) i := by
  constructor
  · exact h.jutila_cardinality_powered 3 5 (by norm_num) (by norm_num)
  · simpa using h.heathBrown_nine_branches_powered 2 1 (by norm_num) (by norm_num)

-- Cardinality at q+1 and energy at q-1 come from independent witnesses.
example {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e) :
    ρ/4 ≤ jutilaLargeValueExponent 5 σ (τ/4) ∧
      ∃ i : Fin 9, e/3 ≤ heathBrownNineBranch σ (τ/3) (ρ/3) (2/3) i := by
  constructor
  · exact h.jutila_cardinality_powered 4 5 (by norm_num) (by norm_num)
  · simpa using h.heathBrown_nine_branches_powered 3 2 (by norm_num) (by norm_num)

-- The fifth coordinate is existentially projected, never scaled.
example {σ τ ρ e s : ℝ} (h : InLargeValueEnergyRegion σ τ ρ e s)
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 84/109) (htlo : 2 ≤ τ) (hthi : τ ≤ 4) :
    e ≤ energyClauseEightRate σ*τ :=
  (show InCardinalityEnergyRegion σ τ ρ e from ⟨s,h⟩).energyClauseEight_general
    hlo hhi htlo hthi

-- Branch 2 has a negative power coefficient: its upper endpoint is a=1/2.
example {σ t r a : ℝ} (hlo : 79/103 ≤ σ) (hhi : σ ≤ 84/109)
    (halo : 1/2 ≤ a) (hahi : a ≤ 2/3) :
    heathBrownNineBranch σ t r a 2 ≤ heathBrownNineBranch σ t r (1/2) 2 := by
  simpa using heathBrownNineBranch_le_extreme_power
    (by linarith : 3/4 ≤ σ) (by linarith : σ ≤ 1) halo hahi (2 : Fin 9)

end AddEstEighthRegression

namespace BourgainDoubleZetaRegression

open Filter Topology Complex Finset

-- Exact signature: LargeValuePattern.phaseSum_eq_endpoint_add_source
example
    (P : LargeValuePattern) (t u : ℝ) :
    (∑ n ∈ P.indices, dirichletPhase n (t - u)) =
      dirichletPhase P.scale (t - u) +
        sourceDirichletPoly P.scale (fun _ => 1)
          ((P.intervalRight - t) - (P.intervalRight - u)) :=
  @LargeValuePattern.phaseSum_eq_endpoint_add_source P t u

-- Exact signature: LargeValuePattern.phaseSum_sq_le_reflected_source
example
    (P : LargeValuePattern) (t u : ℝ) :
    ‖∑ n ∈ P.indices, dirichletPhase n (t - u)‖ ^ 2 ≤
      2 * ‖sourceDirichletPoly P.scale (fun _ => 1)
        ((P.intervalRight - t) - (P.intervalRight - u))‖ ^ 2 + 2 :=
  @LargeValuePattern.phaseSum_sq_le_reflected_source P t u

-- Exact signature: doubleZetaSum_le_native_secondMoment
example (P : LargeValuePattern) :
    doubleZetaSum P ≤
      2 * gmDiscreteRatioMoment 2 P.scale P.reflectedOrdinates +
        2 * (P.ordinates.card : ℝ) ^ 2 :=
  @doubleZetaSum_le_native_secondMoment P

-- Exact signature: heathBrown_largeValuePattern_doubleZeta
example :
    ∀ ε : ℝ, 0 < ε → ∃ C H₀ : ℝ, 0 < C ∧ 1 ≤ H₀ ∧
      ∀ (P : LargeValuePattern) (H : ℝ), H₀ ≤ H → P.T ≤ H →
        doubleZetaSum P ≤ C * H ^ ε *
          ((P.ordinates.card : ℝ) ^ 2 * P.N +
            (P.ordinates.card : ℝ) * P.N ^ 2 +
            (P.ordinates.card : ℝ) ^ (5 / 4 : ℝ) * H ^ (1 / 2 : ℝ) * P.N) :=
  @heathBrown_largeValuePattern_doubleZeta

-- Exact signature: heathBrownDoubleZetaExponent_eq_source
example (τ ρ : ℝ) :
    heathBrownDoubleZetaExponent τ ρ =
      max (max (ρ + 1) (2 * ρ)) (5 / 4 * ρ + τ / 2) + 1 :=
  @heathBrownDoubleZetaExponent_eq_source τ ρ

-- Exact signature: heathBrownDoubleZetaExponent_max_one
example {τ ρ : ℝ} (hρ : ρ ≤ τ) :
    heathBrownDoubleZetaExponent (max 1 τ) ρ =
      heathBrownDoubleZetaExponent τ ρ :=
  @heathBrownDoubleZetaExponent_max_one τ ρ hρ

-- Exact signature: heathBrown_doubleZeta_log_bound
example
    (P : ℕ → LargeValuePattern) {τ ρ s : ℝ}
    (hNtop : Tendsto (fun n => (P n).N) atTop atTop)
    (hRpos : ∀ n, 0 < ((P n).ordinates.card : ℝ))
    (hSpos : ∀ n, 0 < doubleZetaSum (P n))
    (hTlog : Tendsto (fun n => Real.logb (P n).N (P n).T) atTop (nhds τ))
    (hRlog : Tendsto (fun n => Real.logb (P n).N ((P n).ordinates.card : ℝ))
      atTop (nhds ρ))
    (hSlog : Tendsto (fun n => Real.logb (P n).N (doubleZetaSum (P n)))
      atTop (nhds s)) :
    s ≤ heathBrownDoubleZetaExponent (max 1 τ) ρ :=
  @heathBrown_doubleZeta_log_bound P τ ρ s hNtop hRpos hSpos hTlog hRlog hSlog

-- Exact signature: InLargeValueEnergyRegion.heathBrown_doubleZeta
example
    {σ τ ρ e s : ℝ} (h : InLargeValueEnergyRegion σ τ ρ e s) :
    s ≤ max (max (ρ + 1) (2 * ρ)) (5 / 4 * ρ + τ / 2) + 1 :=
  @InLargeValueEnergyRegion.heathBrown_doubleZeta σ τ ρ e s h

-- Exact signature: InLargeValueEnergyRegion.heathBrown_doubleZeta_small_height
example
    {σ τ ρ e s : ℝ} (h : InLargeValueEnergyRegion σ τ ρ e s)
    (hτ : τ ≤ 3 / 2) :
    s ≤ max (ρ + 2) (2 * ρ + 1) :=
  @InLargeValueEnergyRegion.heathBrown_doubleZeta_small_height σ τ ρ e s h hτ

-- Exact signature: InLargeValueEnergyRegion.heathBrown_doubleZeta_eq_diagonal
example
    {σ τ ρ e s : ℝ} (h : InLargeValueEnergyRegion σ τ ρ e s)
    (hτ : τ ≤ 3 / 2) (hρ : ρ ≤ 1) :
    s = ρ + 2 :=
  @InLargeValueEnergyRegion.heathBrown_doubleZeta_eq_diagonal σ τ ρ e s h hτ hρ

-- Exact signature: InZetaLargeValueEnergyRegion.heathBrown_doubleZeta
example
    {σ τ ρ e s : ℝ} (h : InZetaLargeValueEnergyRegion σ τ ρ e s) :
    s ≤ max (max (ρ + 1) (2 * ρ)) (5 / 4 * ρ + τ / 2) + 1 :=
  @InZetaLargeValueEnergyRegion.heathBrown_doubleZeta σ τ ρ e s h

-- Exact signature: bourgain_doubleZeta_max_eq
example {τ ρ : ℝ}
    (hρ : ρ ≤ 1) (hτ : ρ ≤ 4 - 2 * τ) :
    heathBrownDoubleZetaExponent τ ρ = ρ + 2 :=
  @bourgain_doubleZeta_max_eq τ ρ hρ hτ

-- Exact signature: bourgain_auxiliary_doubleZeta_max_le
example (τ x : ℝ) :
    heathBrownDoubleZetaExponent τ x ≤
      max (x + 2) (2 * x + max 1 (2 * τ - 2)) :=
  @bourgain_auxiliary_doubleZeta_max_le τ x

-- Exact signature: bourgain_eliminate_auxiliary_witness
example
    {σ τ ρ α₁ α₂ x : ℝ} (hρ : ρ ≤ 1) (hτ : ρ ≤ 4 - 2 * τ)
    (hwitness :
      max (-2 * α₁ + 2 * σ + x + ρ)
        (-α₁ - α₂ / 2 + 2 * σ + x / 2 + 3 * ρ / 2) ≤
      heathBrownDoubleZetaExponent τ ρ / 2 + heathBrownDoubleZetaExponent τ x / 2) :
    ρ ≤ max (α₁ + α₂ / 2 + 2 - 2 * σ)
      (4 * α₁ + 2 + max 1 (2 * τ - 2) - 4 * σ) :=
  @bourgain_eliminate_auxiliary_witness σ τ ρ α₁ α₂ x hρ hτ hwitness

-- Exact signature: bourgain_simplify_log_dichotomy
example
    {σ τ ρ α₁ α₂ : ℝ} (hρ : ρ ≤ 1) (hτ : ρ ≤ 4 - 2 * τ)
    (hdichotomy :
      ρ ≤ max (max (α₂ + 2 - 2 * σ) (-α₂ + 2 * τ + 4 - 8 * σ))
        (-2 * α₁ + τ + 12 - 16 * σ) ∨
      ∃ x : ℝ, 0 ≤ x ∧
        max (-2 * α₁ + 2 * σ + x + ρ)
          (-α₁ - α₂ / 2 + 2 * σ + x / 2 + 3 * ρ / 2) ≤
        heathBrownDoubleZetaExponent τ ρ / 2 + heathBrownDoubleZetaExponent τ x / 2) :
    ρ ≤ max
      (max (max (α₂ + 2 - 2 * σ) (α₁ + α₂ / 2 + 2 - 2 * σ))
        (-α₂ + 2 * τ + 4 - 8 * σ))
      (max (-2 * α₁ + τ + 12 - 16 * σ)
        (4 * α₁ + 2 + max 1 (2 * τ - 2) - 4 * σ)) :=
  @bourgain_simplify_log_dichotomy σ τ ρ α₁ α₂ hρ hτ hdichotomy

-- Exact signature: bourgain_ninth_row_parameters_nonneg
example {σ τ : ℝ}
    (hσ : 1 / 2 ≤ σ) (hlower : 16 * σ - 11 ≤ τ) :
    0 ≤ (τ + 9 - 12 * σ) / 6 ∧ 0 ≤ max 0 (4 * σ + 4 * τ / 3 - 5) :=
  @bourgain_ninth_row_parameters_nonneg σ τ hσ hlower

-- Exact signature: bourgain_ninth_row_certificate
example {σ τ : ℝ}
    (hτlo : 1 ≤ τ) (hτhi : τ ≤ 3 / 2)
    (hlower : 16 * σ - 11 ≤ τ) (hupper : 20 * σ + τ / 3 ≤ 16) :
    let α₁ := (τ + 9 - 12 * σ) / 6
    let α₂ := max 0 (4 * σ + 4 * τ / 3 - 5)
    max
      (max (max (α₂ + 2 - 2 * σ) (α₁ + α₂ / 2 + 2 - 2 * σ))
        (-α₂ + 2 * τ + 4 - 8 * σ))
      (max (-2 * α₁ + τ + 12 - 16 * σ)
        (4 * α₁ + 2 + max 1 (2 * τ - 2) - 4 * σ)) ≤
      9 - 12 * σ + 2 * τ / 3 :=
  @bourgain_ninth_row_certificate σ τ hτlo hτhi hlower hupper

-- Exact signature: bourgain_ninth_row_of_log_dichotomy
example
    {σ τ ρ : ℝ} (hρ : ρ ≤ 1) (hτlo : 1 ≤ τ) (hτhi : τ ≤ 3 / 2)
    (hlower : 16 * σ - 11 ≤ τ) (hupper : 20 * σ + τ / 3 ≤ 16)
    (hdichotomy :
      let α₁ := (τ + 9 - 12 * σ) / 6
      let α₂ := max 0 (4 * σ + 4 * τ / 3 - 5)
      ρ ≤ max (max (α₂ + 2 - 2 * σ) (-α₂ + 2 * τ + 4 - 8 * σ))
        (-2 * α₁ + τ + 12 - 16 * σ) ∨
      ∃ x : ℝ, 0 ≤ x ∧
        max (-2 * α₁ + 2 * σ + x + ρ)
          (-α₁ - α₂ / 2 + 2 * σ + x / 2 + 3 * ρ / 2) ≤
        heathBrownDoubleZetaExponent τ ρ / 2 + heathBrownDoubleZetaExponent τ x / 2) :
    ρ ≤ 9 - 12 * σ + 2 * τ / 3 :=
  @bourgain_ninth_row_of_log_dichotomy σ τ ρ hρ hτlo hτhi hlower hupper hdichotomy

-- Exact signature: heathBrownMixedDifferenceMoment_expansion
example
    (I : Finset ℕ) (W U : Finset ℝ) (a : ℕ → ℂ) :
    (heathBrownMixedDifferenceMoment I W U a : ℂ) =
      ∑ n ∈ I, ∑ m ∈ I, star (a n) * a m *
        heathBrownPhaseCorrelation W n m * star (heathBrownPhaseCorrelation U n m) :=
  @heathBrownMixedDifferenceMoment_expansion I W U a

-- Exact signature: heathBrownMixedDifferenceMoment_le_correlation
example
    (I : Finset ℕ) (W U : Finset ℝ) (a : ℕ → ℂ)
    (ha : ∀ n ∈ I, ‖a n‖ ≤ 1) :
    heathBrownMixedDifferenceMoment I W U a ≤
      ∑ n ∈ I, ∑ m ∈ I,
        ‖heathBrownPhaseCorrelation W n m‖ * ‖heathBrownPhaseCorrelation U n m‖ :=
  @heathBrownMixedDifferenceMoment_le_correlation I W U a ha

-- Exact signature: heathBrownPhaseCorrelation_norm_sq_sum
example (I : Finset ℕ) (W : Finset ℝ) :
    (∑ nm ∈ I ×ˢ I, ‖heathBrownPhaseCorrelation W nm.1 nm.2‖ ^ 2) =
      heathBrownDifferenceMoment I W (fun _ => 1) :=
  @heathBrownPhaseCorrelation_norm_sq_sum I W

-- Exact signature: heathBrownMixedDifferenceMoment_cauchySchwarz
example
    (I : Finset ℕ) (W U : Finset ℝ) (a : ℕ → ℂ)
    (ha : ∀ n ∈ I, ‖a n‖ ≤ 1) :
    heathBrownMixedDifferenceMoment I W U a ≤
      Real.sqrt (heathBrownDifferenceMoment I W (fun _ => 1)) *
        Real.sqrt (heathBrownDifferenceMoment I U (fun _ => 1)) :=
  @heathBrownMixedDifferenceMoment_cauchySchwarz I W U a ha

-- Exact signature: heathBrownDifferencePolynomial_eq_dirichletPhase
example
    (I : Finset ℕ) (a : ℕ → ℂ) (hI : ∀ n ∈ I, 0 < n) (t u : ℝ) :
    heathBrownDifferencePolynomial I a t u =
      ∑ n ∈ I, a n * dirichletPhase n (t - u) :=
  @heathBrownDifferencePolynomial_eq_dirichletPhase I a hI t u

-- Exact signature: mixed_doubleZeta_cauchySchwarz
example
    (I : Finset ℕ) (W U : Finset ℝ) (a : ℕ → ℂ)
    (hI : ∀ n ∈ I, 0 < n) (ha : ∀ n ∈ I, ‖a n‖ ≤ 1) :
    (∑ t ∈ W, ∑ u ∈ U, ‖∑ n ∈ I, a n * dirichletPhase n (t - u)‖ ^ 2) ≤
      Real.sqrt (∑ t ∈ W, ∑ u ∈ W, ‖∑ n ∈ I, dirichletPhase n (t - u)‖ ^ 2) *
        Real.sqrt (∑ t ∈ U, ∑ u ∈ U, ‖∑ n ∈ I, dirichletPhase n (t - u)‖ ^ 2) :=
  @mixed_doubleZeta_cauchySchwarz I W U a hI ha

-- Exact signature: LargeValuePattern.mixed_doubleZeta_le
example
    (P Q : LargeValuePattern) (hI : P.indices = Q.indices)
    (a : ℕ → ℂ) (ha : ∀ n ∈ P.indices, ‖a n‖ ≤ 1) :
    (∑ t ∈ P.ordinates, ∑ u ∈ Q.ordinates,
      ‖∑ n ∈ P.indices, a n * dirichletPhase n (t - u)‖ ^ 2) ≤
      Real.sqrt (doubleZetaSum P) * Real.sqrt (doubleZetaSum Q) :=
  @LargeValuePattern.mixed_doubleZeta_le P Q hI a ha

-- Closed height endpoints, diagonal equality and both parameter branches.
example : heathBrownDoubleZetaExponent 0 0 = 2 := by
  norm_num [heathBrownDoubleZetaExponent]

example : heathBrownDoubleZetaExponent (3/2) 1 = 3 := by
  norm_num [heathBrownDoubleZetaExponent]

example {e s : ℝ} (h : InLargeValueEnergyRegion (3/4) (3/2) 1 e s) : s = 3 := by
  have hb := h.heathBrown_doubleZeta_eq_diagonal (by norm_num) (by norm_num)
  norm_num at hb
  exact hb

example :
    0 ≤ ((1 : ℝ) + 9 - 12 * (3/4)) / 6 ∧
      0 ≤ max 0 (4 * (3/4 : ℝ) + 4 * 1 / 3 - 5) :=
  bourgain_ninth_row_parameters_nonneg (by norm_num) (by norm_num)

example : max 0 (4 * (31/40 : ℝ) + 4 * (3/2) / 3 - 5) = 1/10 := by norm_num

example : max 0 (4 * (59/76 : ℝ) + 4 * (27/19) / 3 - 5) = 0 := by norm_num

example :
    max
      (max (max (0 + 2 - 2 * (3/4 : ℝ)) (((1 + 9 - 12*(3/4)) / 6) + 0/2 + 2 - 2*(3/4)))
        (-0 + 2*1 + 4 - 8*(3/4)))
      (max (-2*((1 + 9 - 12*(3/4)) / 6) + 1 + 12 - 16*(3/4))
        (4*((1 + 9 - 12*(3/4)) / 6) + 2 + max 1 (2*1-2) - 4*(3/4))) ≤ 2/3 := by
  norm_num

-- A rational test rules out merely extrapolating the previous local peak rate.
example :
    max ((18 - 19 * (771/1000 : ℝ)) / (9 * (3 * (771/1000) - 2)))
      (4 * (10 - 9 * (771/1000)) / (5 * (4 * (771/1000) - 1))) <
    5 * (18 - 19 * (771/1000)) / (2 * (13 * (771/1000) - 3)) := by
  norm_num

-- Empty and singleton sets do not erase a variable from the mixed kernel.
example (I : Finset ℕ) (U : Finset ℝ) (a : ℕ → ℂ) :
    heathBrownMixedDifferenceMoment I ∅ U a = 0 := by
  simp [heathBrownMixedDifferenceMoment]

example (I : Finset ℕ) (t u : ℝ) (a : ℕ → ℂ) :
    heathBrownMixedDifferenceMoment I {t} {u} a =
      ‖heathBrownDifferencePolynomial I a t u‖ ^ 2 := by
  simp [heathBrownMixedDifferenceMoment]

end BourgainDoubleZetaRegression

namespace BourgainDifferenceRegression

open Finset MeasureTheory
open scoped Interval Classical

-- Exact signature: bourgain_integer_near_difference
example {x : ℝ} {ℓ : ℤ}
    (h : |x - (ℓ : ℝ)| < 1) :
    ℓ = ⌊x⌋ ∨ ℓ = ⌊x⌋ + 1 :=
  @bourgain_integer_near_difference x ℓ h

-- Exact signature: bourgainDifferenceCount_eq_zero_of_not_mem
example
    (W : Finset ℝ) {ℓ : ℤ} (hℓ : ℓ ∉ bourgainDifferenceSupport W) :
    bourgainDifferenceCount W ℓ = 0 :=
  @bourgainDifferenceCount_eq_zero_of_not_mem W ℓ hℓ

-- Exact signature: bourgainDifferenceCount_eq_sum
example (W : Finset ℝ) (ℓ : ℤ) :
    bourgainDifferenceCount W ℓ =
      ∑ p ∈ W ×ˢ W, if |p.1 - p.2 - (ℓ : ℝ)| < 1 then 1 else 0 :=
  @bourgainDifferenceCount_eq_sum W ℓ

-- Exact signature: bourgainDifferenceCount_sum_le
example (W : Finset ℝ) (D : Finset ℤ) :
    ∑ ℓ ∈ D, bourgainDifferenceCount W ℓ ≤ 2 * W.card ^ 2 :=
  @bourgainDifferenceCount_sum_le W D

-- Exact signature: bourgainDifferenceCount_le_card
example {W : Finset ℝ}
    (hsep : IsSeparated 2 W) (ℓ : ℤ) :
    bourgainDifferenceCount W ℓ ≤ W.card :=
  @bourgainDifferenceCount_le_card W hsep ℓ

-- Exact signature: bourgainDifferenceCount_sum_sq_le
example {W : Finset ℝ}
    (hsep : IsSeparated 2 W) (D : Finset ℤ) :
    ∑ ℓ ∈ D, bourgainDifferenceCount W ℓ ^ 2 ≤ 2 * W.card ^ 3 :=
  @bourgainDifferenceCount_sum_sq_le W hsep D

-- Exact signature: bourgainDifferenceCount_sum_sq_cast_le
example {W : Finset ℝ}
    (hsep : IsSeparated 2 W) (D : Finset ℤ) :
    ∑ ℓ ∈ D, (bourgainDifferenceCount W ℓ : ℝ) ^ 2 ≤ 2 * (W.card : ℝ) ^ 3 :=
  @bourgainDifferenceCount_sum_sq_cast_le W hsep D

-- Exact signature: bourgainDifferenceCount_weighted_sq_le
example {W : Finset ℝ}
    (hsep : IsSeparated 2 W) (D : Finset ℤ) (f : ℤ → ℝ) :
    (∑ ℓ ∈ D, (bourgainDifferenceCount W ℓ : ℝ) * f ℓ) ^ 2 ≤
      2 * (W.card : ℝ) ^ 3 * ∑ ℓ ∈ D, f ℓ ^ 2 :=
  @bourgainDifferenceCount_weighted_sq_le W hsep D f

-- Exact signature: bourgainDifferenceSupport_bounds
example {W : Finset ℝ} {T : ℝ}
    (hbase : InBaseInterval T W) {ℓ : ℤ} (hℓ : ℓ ∈ bourgainDifferenceSupport W) :
    -T - 1 ≤ (ℓ : ℝ) ∧ (ℓ : ℝ) ≤ T + 1 :=
  @bourgainDifferenceSupport_bounds W T hbase ℓ hℓ

-- Exact signature: bourgainDifferenceCount_weighted_eq
example (W : Finset ℝ)
    (D : Finset ℤ) (g : ℤ → ℝ) :
    (∑ ℓ ∈ D, (bourgainDifferenceCount W ℓ : ℝ) * g ℓ) =
      ∑ p ∈ W ×ˢ W, ∑ ℓ ∈ D,
        if |p.1-p.2-(ℓ : ℝ)| < 1 then g ℓ else 0 :=
  @bourgainDifferenceCount_weighted_eq W D g

-- Exact signature: bourgainDifferenceLevel_bounds
example {W : Finset ℝ} {j : ℕ} {ℓ : ℤ}
    (hℓ : ℓ ∈ bourgainDifferenceLevel W j) :
    2 ^ j ≤ bourgainDifferenceCount W ℓ ∧
      bourgainDifferenceCount W ℓ < 2 ^ (j + 1) :=
  @bourgainDifferenceLevel_bounds W j ℓ hℓ

-- Exact signature: mem_bourgainDifferenceLevel_iff
example (W : Finset ℝ) (j : ℕ) (ℓ : ℤ) :
    ℓ ∈ bourgainDifferenceLevel W j ↔
      ℓ ∈ bourgainDifferenceSupport W ∧
        2 ^ j ≤ bourgainDifferenceCount W ℓ ∧
        bourgainDifferenceCount W ℓ < 2 ^ (j + 1) :=
  @mem_bourgainDifferenceLevel_iff W j ℓ

-- Exact signature: bourgainDifferenceLevel_index_le
example {W : Finset ℝ}
    (hsep : IsSeparated 2 W) {j : ℕ}
    (hne : (bourgainDifferenceLevel W j).Nonempty) :
    j ≤ Nat.log 2 W.card :=
  @bourgainDifferenceLevel_index_le W hsep j hne

-- Exact signature: bourgainDifferenceLevel_card_le
example (W : Finset ℝ) (j : ℕ) :
    2 ^ j * (bourgainDifferenceLevel W j).card ≤ 2 * W.card ^ 2 :=
  @bourgainDifferenceLevel_card_le W j

-- Exact signature: bourgainDifferenceLevel_sum_eq
example {W : Finset ℝ}
    (hsep : IsSeparated 2 W) (f : ℤ → ℝ) :
    (∑ j ∈ Finset.range (Nat.log 2 W.card + 1),
      ∑ ℓ ∈ bourgainDifferenceLevel W j,
        (bourgainDifferenceCount W ℓ : ℝ) * f ℓ) =
      ∑ ℓ ∈ bourgainDifferenceSupport W,
        (bourgainDifferenceCount W ℓ : ℝ) * f ℓ :=
  @bourgainDifferenceLevel_sum_eq W hsep f

-- Exact signature: bourgainDifferenceLevel_exists_heavy
example {W : Finset ℝ}
    (hsep : IsSeparated 2 W) (f : ℤ → ℝ) :
    ∃ j ∈ Finset.range (Nat.log 2 W.card + 1),
      (∑ ℓ ∈ bourgainDifferenceSupport W,
        (bourgainDifferenceCount W ℓ : ℝ) * f ℓ) ≤
          (Nat.log 2 W.card + 1 : ℕ) *
            ∑ ℓ ∈ bourgainDifferenceLevel W j,
              (bourgainDifferenceCount W ℓ : ℝ) * f ℓ :=
  @bourgainDifferenceLevel_exists_heavy W hsep f

-- Exact signature: bourgainDifferenceLevel_select
example {W : Finset ℝ}
    (hsep : IsSeparated 2 W) (f : ℤ → ℝ)
    (hf : ∀ ℓ ∈ bourgainDifferenceSupport W, 0 ≤ f ℓ)
    (hmass : 0 < ∑ ℓ ∈ bourgainDifferenceSupport W,
      (bourgainDifferenceCount W ℓ : ℝ) * f ℓ) :
    ∃ j ∈ Finset.range (Nat.log 2 W.card + 1),
      (bourgainDifferenceLevel W j).Nonempty ∧
      2 ^ j ≤ W.card ∧
      2 ^ j * (bourgainDifferenceLevel W j).card ≤ 2 * W.card ^ 2 ∧
      (∑ ℓ ∈ bourgainDifferenceSupport W,
        (bourgainDifferenceCount W ℓ : ℝ) * f ℓ) ≤
        (Nat.log 2 W.card + 1 : ℕ) * (2 : ℝ) ^ (j + 1) *
          ∑ ℓ ∈ bourgainDifferenceLevel W j, f ℓ :=
  @bourgainDifferenceLevel_select W hsep f hf hmass

-- Exact signature: bourgain_integer_window_count_le
example
    (D : Finset ℤ) (H x : ℝ) :
    (D.filter fun ℓ : ℤ => x ∈ Set.Ioc ((ℓ : ℝ)-H) ((ℓ : ℝ)+H)).card ≤
      2 * Nat.ceil H + 1 :=
  @bourgain_integer_window_count_le D H x

-- Exact signature: bourgain_sum_integer_window_integral_le
example
    (D : Finset ℤ) (f : ℝ → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (H a b : ℝ) (hH : 0 ≤ H) (hab : a ≤ b)
    (hrange : ∀ ℓ ∈ D, a ≤ (ℓ : ℝ) ∧ (ℓ : ℝ) ≤ b) :
    (∑ ℓ ∈ D, ∫ x in (ℓ : ℝ)-H..(ℓ : ℝ)+H, f x) ≤
      (2 * Nat.ceil H + 1 : ℕ) * ∫ x in a-H..b+H, f x :=
  @bourgain_sum_integer_window_integral_le D f hf hf0 H a b hH hab hrange

-- Exact signature: bourgain_difference_window_integral_le
example
    (W : Finset ℝ) (f : ℝ → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (H : ℝ) (hH : 0 ≤ H) :
    (∑ p ∈ W ×ˢ W, ∫ u in -H..H, f (p.1-p.2+u)) ≤
      ∑ ℓ ∈ bourgainDifferenceSupport W, (bourgainDifferenceCount W ℓ : ℝ) *
        ∫ u in -(H+1)..H+1, f ((ℓ : ℝ)+u) :=
  @bourgain_difference_window_integral_le W f hf hf0 H hH

-- Exact signature: bourgainLocalZetaSquare_nonneg
example {H : ℝ} (hH : 0 ≤ H) (ℓ : ℤ) :
    0 ≤ bourgainLocalZetaSquare H ℓ :=
  @bourgainLocalZetaSquare_nonneg H hH ℓ

-- Exact signature: bourgainLocalZetaSquare_eq
example (H : ℝ) (ℓ : ℤ) :
    bourgainLocalZetaSquare H ℓ =
      ∫ t in (ℓ : ℝ)-H..(ℓ : ℝ)+H, zetaMomentCriticalNorm t ^ 2 :=
  @bourgainLocalZetaSquare_eq H ℓ

-- Exact signature: bourgainLocalZetaSquare_sq_le
example {H : ℝ} (hH : 0 ≤ H) (ℓ : ℤ) :
    bourgainLocalZetaSquare H ℓ ^ 2 ≤
      2 * H * ∫ t in (ℓ : ℝ)-H..(ℓ : ℝ)+H, zetaMomentCriticalNorm t ^ 4 :=
  @bourgainLocalZetaSquare_sq_le H hH ℓ

-- Exact signature: bourgainLocalZetaSquare_sum_sq_le
example (D : Finset ℤ)
    (H a b : ℝ) (hH : 0 ≤ H) (hab : a ≤ b)
    (hrange : ∀ ℓ ∈ D, a ≤ (ℓ : ℝ) ∧ (ℓ : ℝ) ≤ b) :
    (∑ ℓ ∈ D, bourgainLocalZetaSquare H ℓ ^ 2) ≤
      2 * H * (2 * Nat.ceil H + 1 : ℕ) *
        ∫ t in a-H..b+H, zetaMomentCriticalNorm t ^ 4 :=
  @bourgainLocalZetaSquare_sum_sq_le D H a b hH hab hrange

-- Exact signature: bourgainZetaDifferenceMoment_sq_le
example {W : Finset ℝ} {T H : ℝ}
    (hsep : IsSeparated 2 W) (hbase : InBaseInterval T W)
    (hT : 0 ≤ T) (hH : 0 ≤ H) :
    bourgainZetaDifferenceMoment W H ^ 2 ≤
      4 * H * (2 * Nat.ceil H + 1 : ℕ) * (W.card : ℝ) ^ 3 *
        ∫ t in -(T+H+1)..T+H+1, zetaMomentCriticalNorm t ^ 4 :=
  @bourgainZetaDifferenceMoment_sq_le W T H hsep hbase hT hH

-- Exact signature: bourgainZetaDifferenceMoment_select_level
example {W : Finset ℝ} {H : ℝ}
    (hsep : IsSeparated 2 W) (hH : 0 ≤ H)
    (hmass : 0 < bourgainZetaDifferenceMoment W H) :
    ∃ j ∈ Finset.range (Nat.log 2 W.card + 1),
      (bourgainDifferenceLevel W j).Nonempty ∧
      2 ^ j ≤ W.card ∧
      2 ^ j * (bourgainDifferenceLevel W j).card ≤ 2 * W.card ^ 2 ∧
      bourgainZetaDifferenceMoment W H ≤
        (Nat.log 2 W.card + 1 : ℕ) * (2 : ℝ) ^ (j+1) *
          ∑ ℓ ∈ bourgainDifferenceLevel W j, bourgainLocalZetaSquare H ℓ :=
  @bourgainZetaDifferenceMoment_select_level W H hsep hH hmass

-- Exact signature: bourgain_pair_zeta_square_integral_le
example (W : Finset ℝ) {H : ℝ}
    (hH : 0 ≤ H) :
    (∑ t ∈ W, ∑ v ∈ W,
      ∫ u in -H..H, zetaMomentCriticalNorm (t-v+u)^2) ≤
        bourgainZetaDifferenceMoment W (H+1) :=
  @bourgain_pair_zeta_square_integral_le W H hH

-- Exact signature: integral_zero_le_of_dyadic
example (f : ℝ → ℝ) (hf : Continuous f)
    (hf0 : ∀ t, 0 ≤ f t) {p B C : ℝ} (hp : 1 ≤ p) (hB : 1 ≤ B) (hC : 0 ≤ C)
    (hdyad : ∀ H : ℝ, B ≤ H → (∫ t in H..2*H, f t) ≤ C*H^p) :
    ∃ K : ℝ, 0 < K ∧ ∀ H : ℝ, B ≤ H →
      (∫ t in 0..H, f t) ≤ K*H^p :=
  @integral_zero_le_of_dyadic f hf hf0 p B C hp hB hC hdyad

-- Exact signature: zetaMomentCriticalNorm_neg
example (t : ℝ) :
    zetaMomentCriticalNorm (-t) = zetaMomentCriticalNorm t :=
  @zetaMomentCriticalNorm_neg t

-- Exact signature: zeta_fourth_symmetric
example {η : ℝ} (hη : 0 < η) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
      ∀ T : ℝ, T₀ ≤ T →
        (∫ t in -T..T, zetaMomentCriticalNorm t^4) ≤ C*T^(1+η) :=
  @zeta_fourth_symmetric η hη

-- Exact signature: bourgainZetaDifferenceMoment_fourth_bound
example {η : ℝ} (hη : 0 < η) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
      ∀ (W : Finset ℝ) (T H : ℝ), T₀ ≤ T → 0 ≤ H →
        IsSeparated 2 W → InBaseInterval T W →
        bourgainZetaDifferenceMoment W H ^ 2 ≤
          C * H * (2 * Nat.ceil H + 1 : ℕ) * (W.card : ℝ)^3 *
            (T+H+1)^(1+η) :=
  @bourgainZetaDifferenceMoment_fourth_bound η hη


-- The support is a finite cover; the strict boundary contributes zero.
example : bourgainDifferenceCount ∅ 0 = 0 := by simp [bourgainDifferenceCount]
example : bourgainDifferenceCount {0} 0 = 1 := by
  rw [bourgainDifferenceCount_eq_sum, Finset.sum_product]
  norm_num [Finset.filter_insert, Finset.filter_singleton]
example : bourgainDifferenceCount {0} 1 = 0 := by
  rw [bourgainDifferenceCount_eq_sum, Finset.sum_product]
  norm_num [Finset.filter_insert, Finset.filter_singleton]
example : bourgainDifferenceSupport {0} = {0, 1} := by norm_num [bourgainDifferenceSupport]
example : bourgainDifferenceLevel ∅ 0 = ∅ := by
  simp [bourgainDifferenceLevel, bourgainDifferenceSupport]
example : bourgainDifferenceLevel {0} 0 = {0} := by
  norm_num [bourgainDifferenceLevel, bourgainDifferenceSupport, bourgainDifferenceCount_eq_sum,
    Finset.filter_insert, Finset.filter_singleton]

-- Two-unit separation and strict windows keep the diagonal and endpoints exact.
example : bourgainDifferenceCount {0, 2} 0 = 2 := by
  rw [bourgainDifferenceCount_eq_sum, Finset.sum_product]
  norm_num [Finset.filter_insert, Finset.filter_singleton]
example : bourgainDifferenceCount {0, 2} 1 = 0 := by
  rw [bourgainDifferenceCount_eq_sum, Finset.sum_product]
  norm_num [Finset.filter_insert, Finset.filter_singleton]
example : bourgainDifferenceCount {0, 2} 2 = 1 := by
  rw [bourgainDifferenceCount_eq_sum, Finset.sum_product]
  norm_num [Finset.filter_insert, Finset.filter_singleton]

-- One-unit separation alone does not justify Delta <= |W|.
example : IsSeparated 1 ({0, 11/10, 22/10, 33/10} : Finset ℝ) := by
  intro x hx y hy hne
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl <;> norm_num [Real.dist_eq] at *

example :
    ({0, 11/10, 22/10, 33/10} : Finset ℝ).card <
      bourgainDifferenceCount {0, 11/10, 22/10, 33/10} 2 := by
  rw [bourgainDifferenceCount_eq_sum, Finset.sum_product]
  norm_num [Finset.filter_insert, Finset.filter_singleton]

-- Degenerate windows and empty ordinate sets keep the actual integrals.
example (ℓ : ℤ) : bourgainLocalZetaSquare 0 ℓ = 0 := by
  simp [bourgainLocalZetaSquare]
example (H : ℝ) : bourgainZetaDifferenceMoment ∅ H = 0 := by
  simp [bourgainZetaDifferenceMoment, bourgainDifferenceSupport]
example (W : Finset ℝ) : bourgainZetaDifferenceMoment W 0 = 0 := by
  simp [bourgainZetaDifferenceMoment, bourgainLocalZetaSquare]

end BourgainDifferenceRegression

namespace BourgainMellinRegression

open Complex MeasureTheory Set
open scoped Interval

-- BourgainCriticalMellin: mellin_bourgainRealPowerWeight
example (a : ℝ) (g : ℝ → ℂ) (s : ℂ) :
    mellin (bourgainRealPowerWeight a g) s = mellin g (s + (a : ℂ)) :=
  @TaoTrudgianYang2025.mellin_bourgainRealPowerWeight a g s

-- BourgainCriticalMellin: mellin_bourgainDilatedProfile
example (g : ℝ → ℂ) {L : ℝ} (hL : 0 < L) (s : ℂ) :
    mellin (fun x => g (x / L)) s = (L : ℂ) ^ s * mellin g s :=
  @TaoTrudgianYang2025.mellin_bourgainDilatedProfile g L hL s

-- BourgainCriticalMellin: mellin_bourgainCriticalWeight
example (g : ℝ → ℂ) {L : ℝ} (hL : 0 < L) (s : ℂ) :
    mellin (bourgainCriticalWeight g L) s =
      (L : ℂ) ^ (s - 1/2) * mellin g (s - 1/2) :=
  @TaoTrudgianYang2025.mellin_bourgainCriticalWeight g L hL s

-- BourgainCriticalMellin: norm_bourgainCriticalWeight_mellin_critical
example
    (g : ℝ → ℂ) {L : ℝ} (hL : 0 < L) (u : ℝ) :
    ‖mellin (bourgainCriticalWeight g L) ((1/2 : ℂ) + (u : ℂ)*I)‖ =
      ‖mellin g ((u : ℂ)*I)‖ :=
  @TaoTrudgianYang2025.norm_bourgainCriticalWeight_mellin_critical g L hL u

-- BourgainCriticalMellin: norm_bourgainCriticalWeight_mellin_residue
example
    (g : ℝ → ℂ) {L : ℝ} (hL : 0 < L) (t : ℝ) :
    ‖mellin (bourgainCriticalWeight g L) (1 - (t : ℂ)*I)‖ =
      Real.sqrt L * ‖mellin g ((1/2 : ℂ) - (t : ℂ)*I)‖ :=
  @TaoTrudgianYang2025.norm_bourgainCriticalWeight_mellin_residue g L hL t

-- BourgainCriticalMellin: bourgainCriticalWeight_mellin_bounds
example {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 0 < L → ∀ u : ℝ,
      (1+|u|)^q * ‖mellin (bourgainCriticalWeight g L) ((1/2 : ℂ)+(u : ℂ)*I)‖ ≤ C ∧
      (1+|u|)^q * ‖mellin (bourgainCriticalWeight g L) (1-(u : ℂ)*I)‖ ≤
        C * Real.sqrt L :=
  @TaoTrudgianYang2025.bourgainCriticalWeight_mellin_bounds g hg q

-- BourgainCriticalMellin: bourgainCriticalWeight_zeta_mellin_entry
example {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g) {L : ℝ} (hL : 0 < L) (t : ℝ) :
    (∑' n : ℕ, bourgainCriticalWeight g L n * dirichletPhase n t) =
      (L : ℂ) ^ ((1/2 : ℂ)-(t : ℂ)*I) *
        mellin g ((1/2 : ℂ)-(t : ℂ)*I) +
      (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ,
        riemannZeta ((1/2 : ℂ) + ((u+t : ℝ) : ℂ)*I) *
          ((L : ℂ)^((u : ℂ)*I) * mellin g ((u : ℂ)*I)) :=
  @TaoTrudgianYang2025.bourgainCriticalWeight_zeta_mellin_entry g hg L hL t

-- BourgainMellinLocalization: bourgain_integrable_mellin_weight
example {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g) (q : ℕ) (σ : ℝ) :
    Integrable (fun u : ℝ =>
      (1+|u|)^q * ‖mellin g ((σ : ℂ)+(u : ℂ)*I)‖) :=
  @TaoTrudgianYang2025.bourgain_integrable_mellin_weight g hg q σ

-- BourgainMellinLocalization: bourgainZetaMellinNorm_nonneg
example (g : ℝ → ℂ) (t u : ℝ) :
    0 ≤ bourgainZetaMellinNorm g t u :=
  @TaoTrudgianYang2025.bourgainZetaMellinNorm_nonneg g t u

-- BourgainMellinLocalization: continuous_bourgainZetaMellinNorm
example {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g) (t : ℝ) :
    Continuous (bourgainZetaMellinNorm g t) :=
  @TaoTrudgianYang2025.continuous_bourgainZetaMellinNorm g hg t

-- BourgainMellinLocalization: bourgainZetaMellinNorm_le
example (g : ℝ → ℂ) (t u : ℝ) :
    bourgainZetaMellinNorm g t u ≤
      6*(1+|t|)*((1+|u|)*‖mellin g ((u : ℂ)*I)‖) :=
  @TaoTrudgianYang2025.bourgainZetaMellinNorm_le g t u

-- BourgainMellinLocalization: integrable_bourgainZetaMellinNorm
example {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g) (t : ℝ) :
    Integrable (bourgainZetaMellinNorm g t) :=
  @TaoTrudgianYang2025.integrable_bourgainZetaMellinNorm g hg t

-- BourgainMellinLocalization: bourgainZetaMellinNorm_tail
example {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t H : ℝ, 0 ≤ H →
      (∫ u in (Ioc (-H) H)ᶜ, bourgainZetaMellinNorm g t u) ≤
        C*(1+|t|)/(1+H)^q :=
  @TaoTrudgianYang2025.bourgainZetaMellinNorm_tail g hg q

-- BourgainMellinLocalization: bourgainCriticalWeight_norm_le_mellin
example {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g) {L : ℝ} (hL : 0 < L) (t : ℝ) :
    ‖∑' n : ℕ, bourgainCriticalWeight g L n * dirichletPhase n t‖ ≤
      ‖mellin (bourgainCriticalWeight g L) (1-(t : ℂ)*I)‖ +
        ∫ u, bourgainZetaMellinNorm g t u :=
  @TaoTrudgianYang2025.bourgainCriticalWeight_norm_le_mellin g hg L hL t

-- BourgainMellinLocalization: bourgainCriticalWeight_localized
example {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 0 < L → ∀ t H : ℝ, 0 ≤ H →
      ‖∑' n : ℕ, bourgainCriticalWeight g L n * dirichletPhase n t‖ ≤
        C * (Real.sqrt L / (1+|t|)^q +
          (∫ u in -H..H, zetaMomentCriticalNorm (u+t)) +
          (1+|t|)/(1+H)^q) :=
  @TaoTrudgianYang2025.bourgainCriticalWeight_localized g hg q

-- BourgainSmoothedPolynomial: bourgainDyadicProfile_weight_eq
example {L x : ℝ}
    (hL : 0 < L) (hl : L ≤ x) (hu : x ≤ 2*L) :
    bourgainCriticalWeight bourgainDyadicProfile L x = ((x^(-1/2 : ℝ) : ℝ) : ℂ) :=
  @TaoTrudgianYang2025.bourgainDyadicProfile_weight_eq L x hL hl hu

-- BourgainSmoothedPolynomial: bourgainDyadicProfile_weight_eq_zero
example {L x : ℝ}
    (hL : 0 < L) (hx : x ≤ L/2 ∨ 5*L/2 ≤ x) :
    bourgainCriticalWeight bourgainDyadicProfile L x = 0 :=
  @TaoTrudgianYang2025.bourgainDyadicProfile_weight_eq_zero L x hL hx

-- BourgainSmoothedPolynomial: bourgainSmoothedCriticalPolynomial_eq_sum
example {L : ℝ}
    (hL : 0 < L) (t : ℝ) :
    bourgainSmoothedCriticalPolynomial L t =
      ∑ n ∈ Finset.range (Nat.ceil (5*L/2)+1),
        bourgainCriticalWeight bourgainDyadicProfile L n * dirichletPhase n t :=
  @TaoTrudgianYang2025.bourgainSmoothedCriticalPolynomial_eq_sum L hL t

-- BourgainSmoothedPolynomial: bourgainCriticalWeight_localized_sq
example {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 0 < L → ∀ t H : ℝ, 0 ≤ H →
      ‖∑' n : ℕ, bourgainCriticalWeight g L n * dirichletPhase n t‖^2 ≤
        C * (L/(1+|t|)^(2*q) +
          2*H*(∫ u in -H..H, zetaMomentCriticalNorm (u+t)^2) +
          (1+|t|)^2/(1+H)^(2*q)) :=
  @TaoTrudgianYang2025.bourgainCriticalWeight_localized_sq g hg q

-- BourgainSmoothedPolynomial: bourgainSmoothedCriticalPolynomial_localized_sq
example (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 0 < L → ∀ t H : ℝ, 0 ≤ H →
      ‖bourgainSmoothedCriticalPolynomial L t‖^2 ≤
        C * (L/(1+|t|)^(2*q) +
          2*H*(∫ u in -H..H, zetaMomentCriticalNorm (u+t)^2) +
          (1+|t|)^2/(1+H)^(2*q)) :=
  @TaoTrudgianYang2025.bourgainSmoothedCriticalPolynomial_localized_sq q

-- BourgainSmoothedPolynomial: bourgainSmoothedCriticalPolynomial_pair_moment
example (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 0 < L →
      ∀ (W : Finset ℝ) (T H : ℝ), 0 ≤ T → 0 ≤ H → InBaseInterval T W →
      (∑ t ∈ W, ∑ v ∈ W, ‖bourgainSmoothedCriticalPolynomial L (t-v)‖^2) ≤
        C * (L*(∑ t ∈ W, ∑ v ∈ W, 1/(1+|t-v|)^(2*q)) +
          2*H*bourgainZetaDifferenceMoment W (H+1) +
          (W.card : ℝ)^2*(1+T)^2/(1+H)^(2*q)) :=
  @TaoTrudgianYang2025.bourgainSmoothedCriticalPolynomial_pair_moment q

-- BourgainSmoothedMoments: bourgain_sum_reciprocal_sq_le_four
example (W : Finset ℝ) (x : ℝ)
    (hsep : IsSeparated 1 W) :
    (∑ u ∈ W, 1/(1+|u-x|)^2) ≤ 4 :=
  @TaoTrudgianYang2025.bourgain_sum_reciprocal_sq_le_four W x hsep

-- BourgainSmoothedMoments: bourgain_sum_reciprocal_pow_le_four
example (W : Finset ℝ) (x : ℝ)
    (hsep : IsSeparated 1 W) {q : ℕ} (hq : 0 < q) :
    (∑ u ∈ W, 1/(1+|u-x|)^(2*q)) ≤ 4 :=
  @TaoTrudgianYang2025.bourgain_sum_reciprocal_pow_le_four W x hsep q hq

-- BourgainSmoothedMoments: bourgain_pair_reciprocal_pow_le
example (W : Finset ℝ)
    (hsep : IsSeparated 1 W) {q : ℕ} (hq : 0 < q) :
    (∑ t ∈ W, ∑ v ∈ W, 1/(1+|t-v|)^(2*q)) ≤ 4*(W.card : ℝ) :=
  @TaoTrudgianYang2025.bourgain_pair_reciprocal_pow_le W hsep q hq

-- BourgainSmoothedMoments: bourgainSmoothedCriticalPolynomial_separated_moment
example {q : ℕ} (hq : 0 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 0 < L →
      ∀ (W : Finset ℝ) (T H : ℝ), 0 ≤ T → 0 ≤ H →
      IsSeparated 1 W → InBaseInterval T W →
      (∑ t ∈ W, ∑ v ∈ W, ‖bourgainSmoothedCriticalPolynomial L (t-v)‖^2) ≤
        C*(L*(W.card : ℝ) + H*bourgainZetaDifferenceMoment W (H+1) +
          (W.card : ℝ)^2*(1+T)^2/(1+H)^(2*q)) :=
  @TaoTrudgianYang2025.bourgainSmoothedCriticalPolynomial_separated_moment q hq

-- BourgainCriticalMajorant: bourgainSmoothCriticalCoeff_nonneg
example (L : ℝ) (n : ℕ) :
    0 ≤ bourgainSmoothCriticalCoeff L n :=
  @TaoTrudgianYang2025.bourgainSmoothCriticalCoeff_nonneg L n

-- BourgainCriticalMajorant: bourgainSmoothCriticalCoeff_coe
example (L : ℝ) (n : ℕ) :
    (bourgainSmoothCriticalCoeff L n : ℂ) =
      bourgainCriticalWeight bourgainDyadicProfile L n :=
  @TaoTrudgianYang2025.bourgainSmoothCriticalCoeff_coe L n

-- BourgainCriticalMajorant: bourgainSmoothedCriticalPolynomial_eq_sum_positive
example {L : ℝ}
    (hL : 0 < L) (t : ℝ) :
    bourgainSmoothedCriticalPolynomial L t =
      ∑ n ∈ Finset.Icc 1 (Nat.ceil (5*L/2)),
        (bourgainSmoothCriticalCoeff L n : ℂ) * dirichletPhase n t :=
  @TaoTrudgianYang2025.bourgainSmoothedCriticalPolynomial_eq_sum_positive L hL t

-- BourgainCriticalMajorant: bourgain_critical_block_moment_le_smoothed
example
    (I : Finset ℕ) (W : Finset ℝ) (a : ℕ → ℂ) {L B : ℝ}
    (hL : 0 < L) (hB : 0 ≤ B)
    (hI : ∀ n ∈ I, L ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*L)
    (ha : ∀ n ∈ I, ‖a n‖ ≤ B*(n : ℝ)^(-1/2 : ℝ)) :
    (∑ t ∈ W, ∑ v ∈ W, ‖∑ n ∈ I, a n * dirichletPhase n (t-v)‖^2) ≤
      B^2 * ∑ t ∈ W, ∑ v ∈ W, ‖bourgainSmoothedCriticalPolynomial L (t-v)‖^2 :=
  @TaoTrudgianYang2025.bourgain_critical_block_moment_le_smoothed I W a L B hL hB hI ha

-- BourgainCriticalMajorant: bourgain_critical_block_retained_zeta_moment
example {q : ℕ} (hq : 0 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 0 < L →
      ∀ (I : Finset ℕ) (W : Finset ℝ) (a : ℕ → ℂ) (B T H : ℝ),
      0 ≤ B → 0 ≤ T → 0 ≤ H → IsSeparated 1 W → InBaseInterval T W →
      (∀ n ∈ I, L ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*L) →
      (∀ n ∈ I, ‖a n‖ ≤ B*(n : ℝ)^(-1/2 : ℝ)) →
      (∑ t ∈ W, ∑ v ∈ W, ‖∑ n ∈ I, a n * dirichletPhase n (t-v)‖^2) ≤
        C*B^2*(L*(W.card : ℝ) + H*bourgainZetaDifferenceMoment W (H+1) +
          (W.card : ℝ)^2*(1+T)^2/(1+H)^(2*q)) :=
  @TaoTrudgianYang2025.bourgain_critical_block_retained_zeta_moment q hq

-- Both outer support endpoints vanish; both inner endpoints retain the critical weight.
example : bourgainCriticalWeight bourgainDyadicProfile 2 1 = 0 :=
  bourgainDyadicProfile_weight_eq_zero (by norm_num) (Or.inl (by norm_num))
example : bourgainCriticalWeight bourgainDyadicProfile 2 5 = 0 :=
  bourgainDyadicProfile_weight_eq_zero (by norm_num) (Or.inr (by norm_num))
example : bourgainCriticalWeight bourgainDyadicProfile 2 2 = (((2 : ℝ)^(-1/2 : ℝ) : ℝ) : ℂ) :=
  bourgainDyadicProfile_weight_eq (by norm_num) (by norm_num) (by norm_num)
example : bourgainCriticalWeight bourgainDyadicProfile 2 4 = (((4 : ℝ)^(-1/2 : ℝ) : ℝ) : ℂ) :=
  bourgainDyadicProfile_weight_eq (by norm_num) (by norm_num) (by norm_num)
example : bourgainSmoothCriticalCoeff 10 0 = 0 := by
  apply Complex.ofReal_injective
  rw [bourgainSmoothCriticalCoeff_coe]
  exact bourgainDyadicProfile_weight_eq_zero (by norm_num) (Or.inl (by norm_num))
example : bourgainSmoothCriticalCoeff 1 1 = 1 := by
  have hz : zetaIntervalCutoff 1 2 (1 : ℝ) = 1 :=
    zetaIntervalCutoff_eq_one (by norm_num) (by norm_num)
  norm_num [bourgainSmoothCriticalCoeff, hz]
example : bourgainSmoothCriticalCoeff 1 2 = (2 : ℝ)^(-1/2 : ℝ) := by
  have hz : zetaIntervalCutoff 1 2 (2 : ℝ) = 1 :=
    zetaIntervalCutoff_eq_one (by norm_num) (by norm_num)
  norm_num [bourgainSmoothCriticalCoeff, hz]
example : bourgainSmoothCriticalCoeff 1 3 = 0 := by
  have hz : zetaIntervalCutoff 1 2 (3 : ℝ) = 0 :=
    zetaIntervalCutoff_eq_zero_right (by norm_num)
  norm_num [bourgainSmoothCriticalCoeff, hz]

-- The actual profile gives a nontrivial two-term polynomial at scale one.
example (t : ℝ) :
    bourgainSmoothedCriticalPolynomial 1 t =
      dirichletPhase 1 t + (((2 : ℝ)^(-1/2 : ℝ) : ℝ) : ℂ)*dirichletPhase 2 t := by
  rw [bourgainSmoothedCriticalPolynomial_eq_sum_positive (by norm_num)]
  simp_rw [bourgainSmoothCriticalCoeff, div_one, zetaIntervalCutoff_nat]
  norm_num only [Nat.ceil_ofNat, show Nat.ceil (5*(1 : ℝ)/2) = 3 by norm_num]
  rw [show Finset.Icc 1 3 = ({1,2,3} : Finset ℕ) by decide]
  norm_num

-- The diagonal survives and empty sets remain exact.
example (x : ℝ) : (∑ u ∈ ({x} : Finset ℝ), 1/(1+|u-x|)^2) = 1 := by simp
example (q : ℕ) (x : ℝ) :
    (∑ t ∈ ({x} : Finset ℝ), ∑ v ∈ ({x} : Finset ℝ), 1/(1+|t-v|)^(2*q)) = 1 := by
  simp
example (L : ℝ) :
    (∑ t ∈ (∅ : Finset ℝ), ∑ v ∈ (∅ : Finset ℝ),
      ‖bourgainSmoothedCriticalPolynomial L (t-v)‖^2) = 0 := by simp
example (a : ℕ → ℂ) (t : ℝ) :
    (∑ n ∈ (∅ : Finset ℕ), a n * dirichletPhase n t) = 0 := by simp
example (W : Finset ℝ) :
    bourgainZetaDifferenceMoment W 0 = 0 := by
  simp [bourgainZetaDifferenceMoment, bourgainLocalZetaSquare]

end BourgainMellinRegression

namespace BourgainRetainedPatternRegression

open Complex MeasureTheory Set
open scoped Interval

-- BourgainWeightedMoments: bourgainMomentBudget_nonneg
example (q : ℕ) {U T H : ℝ} (W : Finset ℝ)
    (hU : 0 ≤ U) (hH : 0 ≤ H) : 0 ≤ bourgainMomentBudget q U T H W :=
  @TaoTrudgianYang2025.bourgainMomentBudget_nonneg q U T H W hU hH

-- BourgainWeightedMoments: bourgainMomentBudget_mono_scale
example (q : ℕ) {U V : ℝ}
    (hUV : U ≤ V) (T H : ℝ) (W : Finset ℝ) :
    bourgainMomentBudget q U T H W ≤ bourgainMomentBudget q V T H W :=
  @TaoTrudgianYang2025.bourgainMomentBudget_mono_scale q U V hUV T H W

-- BourgainWeightedMoments: bourgain_heathBrownHalfWeight_eq_rpow
example (n : ℕ) :
    heathBrownHalfWeight n = (n : ℝ)^(-1/2 : ℝ) :=
  @TaoTrudgianYang2025.bourgain_heathBrownHalfWeight_eq_rpow n

-- BourgainWeightedMoments: bourgain_sourceDirichletPoly_eq_negative_sum
example (N : ℕ)
    (a : ℕ → ℂ) (t v : ℝ) :
    sourceDirichletPoly N a (t-v) =
      ∑ n ∈ dyadicInterval N, a n * dirichletPhase n (v-t) :=
  @TaoTrudgianYang2025.bourgain_sourceDirichletPoly_eq_negative_sum N a t v

-- BourgainWeightedMoments: bourgain_heathBrownWeightedMoment_retained
example {q : ℕ} (hq : 0 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (T H : ℝ) (W : Finset ℝ),
      0 < N → 0 ≤ T → 0 ≤ H → IsSeparated 1 W → InBaseInterval T W →
      heathBrownWeightedMoment N W ≤ C*bourgainMomentBudget q N T H W :=
  @TaoTrudgianYang2025.bourgain_heathBrownWeightedMoment_retained q hq

-- BourgainWeightedMoments: bourgain_literal_one_moment_retained
example {q : ℕ} (hq : 0 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T H : ℝ) (W : Finset ℝ),
      0 ≤ T → 0 ≤ H → IsSeparated 1 W → InBaseInterval T W →
      (W.card : ℝ)^2 ≤ C*bourgainMomentBudget q 1 T H W :=
  @TaoTrudgianYang2025.bourgain_literal_one_moment_retained q hq

-- BourgainPolynomialMoments: bourgain_source_power_moment_retained
example (k : ℕ) (hk : 0 < k)
    {q : ℕ} (hq : 0 < q) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (T H : ℝ) (W : Finset ℝ) (a : ℕ → ℂ),
        0 < N → 0 ≤ T → 0 ≤ H → IsSeparated 1 W → InBaseInterval T W →
        (∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1) →
        (∑ t ∈ W, ∑ v ∈ W, ‖sourceDirichletPoly N a (t-v)‖^(2*k)) ≤
          C*(2^k*N^k : ℕ)*(((2^k*N^k : ℕ) : ℝ)^η)^2 *
            bourgainMomentBudget q (2^k*N^k : ℕ) T H W :=
  @TaoTrudgianYang2025.bourgain_source_power_moment_retained k hk q hq η hη

-- BourgainPrefixMoments: bourgain_reflected_prefix_moment_retained
example (k : ℕ) (hk : 0 < k)
    {q : ℕ} (hq : 0 < q) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ℕ) (T H : ℝ) (W : Finset ℝ) (u : ℝ),
        0 < M → 0 ≤ T → 0 ≤ H → IsSeparated 1 W → InBaseInterval T W →
        (∑ t ∈ W, ∑ v ∈ W, ‖gmReflectionDirichletPoly (t-v) M u‖^(2*k)) ≤
          C*((Nat.clog 2 M : ℝ)+1)^(2*k)*(2^k*M^k : ℕ)*
            (((2^k*M^k : ℕ) : ℝ)^η)^2 *
              bourgainMomentBudget q (2^k*M^k : ℕ) T H W :=
  @TaoTrudgianYang2025.bourgain_reflected_prefix_moment_retained k hk q hq η hη

-- BourgainReflectionIntegrals: bourgain_reflected_bin_integral_moment_retained
example (k : ℕ) (hk : 0 < k)
    {q : ℕ} (hq : 0 < q) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ℕ) (T H : ℝ) (W : Finset ℝ) (j : ℕ),
        0 < M → 0 ≤ T → 0 ≤ H → IsSeparated 1 W → InBaseInterval T W →
        (∑ p ∈ heathBrownDifferenceBin W j,
          (∫ u in -H..H, ‖gmReflectionDirichletPoly (p.1-p.2) M u‖)^(2*k)) ≤
            (2*H)^(2*k)*bourgainPrefixMomentMajorant q k M T H W C η :=
  @TaoTrudgianYang2025.bourgain_reflected_bin_integral_moment_retained k hk q hq η hη

-- BourgainTraceBins: bourgain_trace_bin_moment_retained
example (cutoff : GMSmoothCutoff)
    (q k : ℕ) (hq : 2 ≤ q) (hk : 0 < k)
    {η : ℝ} (hη : 0 < η) :
    ∃ A C K L D : ℝ,
      0 < A ∧ 0 < C ∧ 0 < K ∧ 0 < L ∧ 0 < D ∧
      ∀ (Q M j : ℕ) (T H : ℝ) (W : Finset ℝ),
        0 < Q → 0 < M → 2 ≤ j → 0 ≤ T → 1 ≤ H →
        H ≤ ((2 ^ j : ℕ) : ℝ) / 2 →
        IsSeparated 1 W → InBaseInterval T W →
        (∑ p ∈ heathBrownDifferenceBin W j,
          ‖heathBrownTracePolynomial cutoff Q (p.1-p.2)‖ ^ (2*k)) ≤
          bourgainTraceBinMajorant q k Q M j T H W A C K L D η :=
  @TaoTrudgianYang2025.bourgain_trace_bin_moment_retained cutoff q k hq hk η hη

-- BourgainPatternEntry: bourgain_spaced_off_diagonal_moment_retained
example (cutoff : GMSmoothCutoff)
    (q k : ℕ) (hq : 2 ≤ q) (hk : 0 < k)
    {η : ℝ} (hη : 0 < η) :
    ∃ A C K L D : ℝ,
      0 < A ∧ 0 < C ∧ 0 < K ∧ 0 < L ∧ 0 < D ∧
      ∀ (Q : ℕ) (M : ℕ → ℕ) (T H δ : ℝ) (W : Finset ℝ),
        0 < Q → (∀ j, 0 < M j) → 0 ≤ T → 1 ≤ H → 4 ≤ δ → 4*H ≤ δ →
        IsSeparated δ W → InBaseInterval T W →
        jutilaOffDiagonalMoment cutoff Q W k ≤
          ∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
            bourgainTraceBinMajorant q k Q (M j) j T H W A C K L D η :=
  @TaoTrudgianYang2025.bourgain_spaced_off_diagonal_moment_retained cutoff q k hq hk η hη

-- BourgainPatternEntry: bourgain_binned_pattern_retained
example (cutoff : GMSmoothCutoff)
    (q k : ℕ) (hq : 2 ≤ q) (hk : 0 < k)
    {η : ℝ} (hη : 0 < η) :
    ∃ A C K L D : ℝ,
      0 < A ∧ 0 < C ∧ 0 < K ∧ 0 < L ∧ 0 < D ∧
      ∀ (P : LargeValuePattern) (δ : ℝ),
        30 ≤ P.scale → 1 < P.V → 0 ≤ P.T → 4 ≤ δ →
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
                    bourgainTraceBinMajorant q k Q (M j) j P.T H W A C K L D η :=
  @TaoTrudgianYang2025.bourgain_binned_pattern_retained cutoff q k hq hk η hη

-- BourgainHybridEntry: bourgain_hybrid_pattern_retained
example (cutoff : GMSmoothCutoff)
    (q k : ℕ) (hq : 2 ≤ q) (hk : 0 < k)
    {η : ℝ} (hη : 0 < η) :
    ∃ E F A C K L D : ℝ,
      0 < E ∧ 0 < F ∧ 0 < A ∧ 0 < C ∧ 0 < K ∧ 0 < L ∧ 0 < D ∧
      ∀ (P : LargeValuePattern) (δ : ℝ),
        30 ≤ P.scale → 1 < P.V → 0 ≤ P.T → 4 ≤ δ →
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
                    bourgainTraceHybridMajorant q k Q H j P.T W E F A C K L D η :=
  @TaoTrudgianYang2025.bourgain_hybrid_pattern_retained cutoff q k hq hk η hη

-- BourgainPhysicalMain: bourgainMomentRemainder_nonneg
example (q : ℕ) (T : ℝ) {H : ℝ}
    (hH : 0 ≤ H) (W : Finset ℝ) : 0 ≤ bourgainMomentRemainder q T H W :=
  @TaoTrudgianYang2025.bourgainMomentRemainder_nonneg q T H hH W

-- BourgainPhysicalMain: bourgainMomentBudget_eq
example (q : ℕ) (U T H : ℝ) (W : Finset ℝ) :
    bourgainMomentBudget q U T H W =
      U*(W.card : ℝ)+bourgainMomentRemainder q T H W :=
  @TaoTrudgianYang2025.bourgainMomentBudget_eq q U T H W

-- BourgainPhysicalMain: bourgain_reflection_main_core_le
example (k : ℕ) {Q M S H C T R Z : ℝ}
    (hQ : 0 ≤ Q) (hM : 0 ≤ M) (hS : 0 < S) (hH : 0 ≤ H)
    (hR : 0 ≤ R) (hZ : 0 ≤ Z)
    (hscale : Q*M ≤ S*(H+2)) (hST : S ≤ T) :
    (Q*C/Real.sqrt S)^(2*k)*(2*H)^(2*k)*(2*M)^k*((2*M)^k*R+Z) ≤
      (16*C^2*(H+2)^4)^k*(R*T^k+Z*Q^k) :=
  @TaoTrudgianYang2025.bourgain_reflection_main_core_le k Q M S H C T R Z hQ hM hS hH hR hZ hscale hST

-- BourgainPhysicalMain: bourgain_reflected_main_le_physical
example (q k Q H j : ℕ) (T : ℝ) (W : Finset ℝ)
    {A C η : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hQ : 0 < Q) (hH : 0 < H) (hT : 1 ≤ T)
    (hj : j ∈ Finset.range (Nat.log 2 (Nat.floor T)+1))
    (hfar : ¬ 2^(j+1) ≤ Q) :
    ((Q : ℝ)*C/Real.sqrt ((2^j : ℕ) : ℝ))^(2*k)*
        ((2*(H : ℝ))^(2*k)*
          bourgainPrefixMomentMajorant q k (heathBrownFixedReflectionLength Q H j) T H W A η) ≤
      jutilaMomentLoss k H T A 0 η * bourgainPhysicalMain q k Q H T W C :=
  @TaoTrudgianYang2025.bourgain_reflected_main_le_physical q k Q H j T W A C η hA hC hη hQ hH hT hj hfar

-- BourgainPhysicalPatterns: bourgain_hybrid_sum_le_physical
example (q k Q H : ℕ) (T δ : ℝ) (W : Finset ℝ)
    {E F A C K L D η : ℝ}
    (hE : 0 ≤ E) (hF : 0 ≤ F) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hD : 0 ≤ D) (hη : 0 ≤ η)
    (hQ : 0 < Q) (hH : 0 < H) (hT : 1 ≤ T)
    (hδ : 4 ≤ δ) (hHδ : 4*(H : ℝ) ≤ δ) (hsep : IsSeparated δ W) :
    (∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
      bourgainTraceHybridMajorant q k Q H j T W E F A C K L D η) ≤
      ((Nat.log 2 (Nat.floor T) + 1 : ℕ) : ℝ) *
        bourgainPhysicalEnvelope q k Q H T W E F A C K L D η :=
  @TaoTrudgianYang2025.bourgain_hybrid_sum_le_physical q k Q H T δ W E F A C K L D η hE hF hA hC hK hL hD hη hQ hH hT hδ hHδ hsep

-- BourgainPhysicalPatterns: bourgain_physical_pattern_retained
example (cutoff : GMSmoothCutoff)
    (q k : ℕ) (hq : 2 ≤ q) (hk : 0 < k)
    {η : ℝ} (hη : 0 < η) :
    ∃ E F A C K L D : ℝ,
      0 < E ∧ 0 < F ∧ 0 < A ∧ 0 < C ∧ 0 < K ∧ 0 < L ∧ 0 < D ∧
      ∀ (P : LargeValuePattern) (δ : ℝ),
        30 ≤ P.scale → 1 < P.V → 1 ≤ P.T → 4 ≤ δ →
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
                    bourgainPhysicalEnvelope q k Q H P.T W E F A C K L D η) :=
  @TaoTrudgianYang2025.bourgain_physical_pattern_retained cutoff q k hq hk η hη

-- BourgainSmoothingErrors: bourgain_mellin_tail_smoothing_le
example {θ T : ℝ}
    (hθ : 0 < θ) (hT : 1 ≤ T) :
    (1+T)^2 /
      (1+(heathBrownSmoothingHeight T θ : ℝ))^
        (2*heathBrownReflectionDerivativeOrder 0 θ) ≤ 4 :=
  @TaoTrudgianYang2025.bourgain_mellin_tail_smoothing_le θ T hθ hT

-- BourgainSmoothingErrors: bourgainZetaDifferenceMoment_nonneg
example (W : Finset ℝ) {H : ℝ}
    (hH : 0 ≤ H) : 0 ≤ bourgainZetaDifferenceMoment W H :=
  @TaoTrudgianYang2025.bourgainZetaDifferenceMoment_nonneg W H hH

-- BourgainSmoothingErrors: bourgainRetainedMomentCore_nonneg
example (k Q : ℕ) {T H : ℝ}
    (hT : 0 ≤ T) (hH : 0 ≤ H) (W : Finset ℝ) :
    0 ≤ bourgainRetainedMomentCore k Q T H W :=
  @TaoTrudgianYang2025.bourgainRetainedMomentCore_nonneg k Q T H hT hH W

-- BourgainSmoothingErrors: bourgain_physical_envelope_smoothing_le
example
    (k Q : ℕ) (T : ℝ) (W : Finset ℝ) {θ E F A C K L D : ℝ}
    (hθ : 0 < θ) (hθOne : θ ≤ 1) (hT : 1 ≤ T) (hQ : 0 < Q)
    (hQT : (Q : ℝ) ≤ 2*T) (hF : 0 ≤ F) (hA : 0 ≤ A)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hD : 0 ≤ D) :
    bourgainPhysicalEnvelope (heathBrownReflectionDerivativeOrder 0 θ) k Q
        (heathBrownSmoothingHeight T θ) T W E F A C K L D θ ≤
      (4*((heathBrownSmoothingHeight T θ : ℝ)+1)) *
        jutilaSmoothingCoefficient k T θ E F A C K L D θ θ *
        bourgainRetainedMomentCore k Q T (heathBrownSmoothingHeight T θ) W :=
  @TaoTrudgianYang2025.bourgain_physical_envelope_smoothing_le k Q T W θ E F A C K L D hθ hθOne hT hQ hQT hF hA hK hL hD

-- BourgainSmoothedPatterns: bourgain_smoothing_coefficient_uniform
example
    (k : ℕ) {θ E F A C K L D : ℝ}
    (hθ : 0 < θ) (hθOne : θ ≤ 1)
    (hE : 0 ≤ E) (hF : 0 ≤ F) (hA : 0 ≤ A)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hD : 0 ≤ D) :
    ∃ B T₀ : ℝ, 0 < B ∧ 2 ≤ T₀ ∧
      ∀ T : ℝ, T₀ ≤ T →
        ((Nat.log 2 (Nat.floor T)+1 : ℕ) : ℝ) *
          (4*((heathBrownSmoothingHeight T θ : ℝ)+1)) *
          jutilaSmoothingCoefficient k T θ E F A C K L D θ θ ≤
            B*T^(((16*k : ℕ) : ℝ)*θ+4*θ) :=
  @TaoTrudgianYang2025.bourgain_smoothing_coefficient_uniform k θ E F A C K L D hθ hθOne hE hF hA hK hL hD

-- BourgainSmoothedPatterns: bourgain_smoothed_pattern_retained
example (cutoff : GMSmoothCutoff)
    (k : ℕ) (hk : 0 < k) {ν : ℝ} (hν : 0 < ν) :
    ∃ θ B T₀ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ θ ≤ ν ∧ 0 < B ∧ 2 ≤ T₀ ∧
      ∀ P : LargeValuePattern,
        30 ≤ P.scale → 1 < P.V → T₀ ≤ P.T → P.N ≤ P.T →
        ∃ (W : Finset ℝ) (Q : ℕ),
          W ⊆ P.reflectedOrdinates ∧
          (P.ordinates.card : ℝ) ≤ B*P.T^ν*(W.card : ℝ) ∧
          0 < Q ∧ P.N/2 ≤ (Q : ℝ) ∧ (Q : ℝ) ≤ 2*P.N ∧
          IsSeparated 2 W ∧ InBaseInterval P.T W ∧
          ((W.card : ℝ)*((P.V-1)/3)^2 ≤ 2*(Q : ℝ)^2 ∨
            (W.card : ℝ)^2*((P.V-1)/3)^(4*k) ≤
              B*P.T^ν*(2*(Q : ℝ))^(2*k)*bourgainRetainedMomentCore k Q P.T (heathBrownSmoothingHeight P.T θ) W) :=
  @TaoTrudgianYang2025.bourgain_smoothed_pattern_retained cutoff k hk ν hν

-- BourgainRetainedCardinality: bourgain_quadratic_recurrence
example {R a b : ℝ}
    (hb : 0 ≤ b) (h : R^2 ≤ a*R+b) :
    R ≤ max a 0 + Real.sqrt b :=
  @TaoTrudgianYang2025.bourgain_quadratic_recurrence R a b hb h

-- BourgainRetainedCardinality: bourgain_retained_recurrence_card_le
example (Q : ℕ) (T H D V : ℝ) (W : Finset ℝ)
    (hH : 0 ≤ H) (hD : 0 ≤ D) (hV : 0 < V)
    (habs : 2*D*(Q : ℝ)^2 ≤ V^8)
    (hrec : (W.card : ℝ)^2*V^8 ≤ D*bourgainRetainedMomentCore 2 Q T H W) :
    (W.card : ℝ) ≤ 2*D*T^2/V^8 +
      Real.sqrt (2*D)*(Q : ℝ)*Real.sqrt (bourgainZetaDifferenceMoment W (H+1))/V^4 :=
  @TaoTrudgianYang2025.bourgain_retained_recurrence_card_le Q T H D V W hH hD hV habs hrec

-- BourgainRetainedCardinality: bourgainRetainedCardinalityBound_expand
example (N T V Z M : ℝ)
    (hZ : 0 ≤ Z) (hV : 1 < V) :
    bourgainRetainedCardinalityBound N T V Z M =
      (72*Z)*N^2/(V-1)^2 +
      (2*Z^2*(4 : ℝ)^4*(3 : ℝ)^8)*T^2*N^4/(V-1)^8 +
      (2*Z*Real.sqrt (2*Z)*(4 : ℝ)^2*(3 : ℝ)^4)*
        N^3*Real.sqrt M/(V-1)^4 :=
  @TaoTrudgianYang2025.bourgainRetainedCardinalityBound_expand N T V Z M hZ hV

-- BourgainRetainedCardinality: bourgain_retained_absorption_identity
example (N Z : ℝ) :
    (2*(Z*(4*N)^4)*(2*N)^2)*(3 : ℝ)^8 =
      (2*(4 : ℝ)^4*(2 : ℝ)^2*(3 : ℝ)^8)*Z*N^6 :=
  @TaoTrudgianYang2025.bourgain_retained_absorption_identity N Z

-- BourgainRetainedCardinality: bourgain_high_value_pattern_retained
example (cutoff : GMSmoothCutoff)
    {ν : ℝ} (hν : 0 < ν) :
    ∃ θ B T₀ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ θ ≤ ν ∧ 0 < B ∧ 2 ≤ T₀ ∧
      ∀ P : LargeValuePattern,
        30 ≤ P.scale → 1 < P.V → T₀ ≤ P.T → P.N ≤ P.T →
        2*(B*P.T^ν*(4*P.N)^4)*(2*P.N)^2 ≤ ((P.V-1)/3)^8 →
        ∃ W : Finset ℝ,
          W ⊆ P.reflectedOrdinates ∧ IsSeparated 2 W ∧ InBaseInterval P.T W ∧
          (P.ordinates.card : ℝ) ≤ B*P.T^ν*(W.card : ℝ) ∧
          (P.ordinates.card : ℝ) ≤
            bourgainRetainedCardinalityBound P.N P.T P.V (B*P.T^ν)
              (bourgainZetaDifferenceMoment W
                ((heathBrownSmoothingHeight P.T θ : ℝ)+1)) :=
  @TaoTrudgianYang2025.bourgain_high_value_pattern_retained cutoff ν hν

-- The native reflection prefix is unweighted, including the literal one.
example (t u : ℝ) : gmReflectionDirichletPoly t 0 u = 0 := by
  simp [gmReflectionDirichletPoly]
example (t u : ℝ) : gmReflectionDirichletPoly t 1 u = 1 := by
  simp [gmReflectionDirichletPoly]
example : gmReflectionDirichletPoly 0 2 0 = 2 := by
  norm_num [gmReflectionDirichletPoly, show Finset.Icc 1 2 = ({1,2} : Finset ℕ) by decide]
example (W : Finset ℝ) (u : ℝ) :
    (∑ t ∈ W, ∑ v ∈ W, ‖gmReflectionDirichletPoly (t-v) 1 u‖^4) =
      (W.card : ℝ)^2 := by
  simp [gmReflectionDirichletPoly, pow_two]
example : heathBrownHalfWeight 0 = 0 := by norm_num [heathBrownHalfWeight]
example : heathBrownHalfWeight 1 = 1 := by norm_num [heathBrownHalfWeight]

-- The actual retained moment vanishes for empty pairs and zero radius.
example (H : ℝ) : bourgainZetaDifferenceMoment ∅ H = 0 := by
  simp [bourgainZetaDifferenceMoment, bourgainDifferenceSupport]
example (q : ℕ) (U T H : ℝ) : bourgainMomentBudget q U T H ∅ = 0 := by
  simp [bourgainMomentBudget, bourgainZetaDifferenceMoment, bourgainDifferenceSupport]
example (q : ℕ) (U T : ℝ) (W : Finset ℝ) :
    bourgainMomentBudget q U T 0 W =
      U*(W.card : ℝ)+(W.card : ℝ)^2*(1+T)^2 := by
  simp [bourgainMomentBudget]
example (k Q : ℕ) (T H : ℝ) : bourgainRetainedMomentCore k Q T H ∅ = 0 := by
  simp [bourgainRetainedMomentCore, bourgainZetaDifferenceMoment, bourgainDifferenceSupport]

-- A vanishing retained term leaves precisely the linear source contribution.
example (a R : ℝ) (ha : 0 ≤ a) (h : R^2 ≤ a*R) : R ≤ a := by
  simpa [max_eq_left ha] using
    (bourgain_quadratic_recurrence (R := R) (a := a) (b := 0) (by norm_num) (by simpa using h))
example (N T V Z : ℝ) :
    bourgainRetainedCardinalityBound N T V Z 0 =
      Z*(2*(2*N)^2/((V-1)/3)^2+2*(Z*(4*N)^4)*T^2/((V-1)/3)^8) := by
  simp [bourgainRetainedCardinalityBound]
example (N T V M : ℝ) : bourgainRetainedCardinalityBound N T V 0 M = 0 := by
  simp [bourgainRetainedCardinalityBound]

end BourgainRetainedPatternRegression

namespace BourgainPowerMassRegression

open Filter Finset MeasureTheory
open RiemannZeta.GuthMaynard
open scoped BigOperators

-- BourgainMomentWindows: bourgainLocalZetaSquare_mono
example {H K : ℝ}
    (hH : 0 ≤ H) (hHK : H ≤ K) (ℓ : ℤ) :
    bourgainLocalZetaSquare H ℓ ≤ bourgainLocalZetaSquare K ℓ :=
  @TaoTrudgianYang2025.bourgainLocalZetaSquare_mono H K hH hHK ℓ

-- BourgainMomentWindows: bourgainZetaDifferenceMoment_mono
example (W : Finset ℝ) {H K : ℝ}
    (hH : 0 ≤ H) (hHK : H ≤ K) :
    bourgainZetaDifferenceMoment W H ≤ bourgainZetaDifferenceMoment W K :=
  @TaoTrudgianYang2025.bourgainZetaDifferenceMoment_mono W H K hH hHK

-- BourgainMomentWindows: eventually_bourgain_smoothing_radius_le
example {θ ε : ℝ}
    (hθ : 0 ≤ θ) (hθε : θ < ε) :
    ∀ᶠ T : ℝ in atTop,
      (heathBrownSmoothingHeight T θ : ℝ)+1 ≤ T^ε :=
  @TaoTrudgianYang2025.eventually_bourgain_smoothing_radius_le θ ε hθ hθε

-- BourgainMomentWindows: bourgain_retained_sqrt_coefficient_le
example {B T ν : ℝ}
    (hB : 0 ≤ B) (hT : 1 ≤ T) (hν : 0 ≤ ν) :
    (B*T^ν)*Real.sqrt (2*(B*T^ν)) ≤ B*Real.sqrt (2*B)*T^(2*ν) :=
  @TaoTrudgianYang2025.bourgain_retained_sqrt_coefficient_le B T ν hB hT hν

-- BourgainRetainedUniform: bourgain_retained_cardinality_uniform
example (cutoff : GMSmoothCutoff)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 1 ≤ C ∧ 2 ≤ T₀ ∧
      ∀ P : LargeValuePattern,
        30 ≤ P.scale → 1 < P.V → T₀ ≤ P.T → P.N ≤ P.T →
        C*P.T^ε*P.N^6 ≤ (P.V-1)^8 →
        ∃ W : Finset ℝ,
          W ⊆ P.reflectedOrdinates ∧ IsSeparated 2 W ∧ InBaseInterval P.T W ∧
          (P.ordinates.card : ℝ) ≤ C*P.T^ε*(W.card : ℝ) ∧
          (P.ordinates.card : ℝ) ≤ C*P.T^ε *
            (P.N^2/(P.V-1)^2 + P.T^2*P.N^4/(P.V-1)^8 +
              P.N^3*Real.sqrt (bourgainZetaDifferenceMoment W (P.T^ε))/(P.V-1)^4) :=
  @TaoTrudgianYang2025.bourgain_retained_cardinality_uniform cutoff ε hε

-- BourgainRetainedPowerWindows: bourgain_retained_power_identity
example {N : ℝ} (hN : 0 < N) (s τ M : ℝ) :
    N^2/(N^s)^2+(N^τ)^2*N^4/(N^s)^8+
      N^3*Real.sqrt M/(N^s)^4 =
        N^(2-2*s)+N^(2*τ+4-8*s)+N^(3-4*s)*Real.sqrt M :=
  @TaoTrudgianYang2025.bourgain_retained_power_identity N hN s τ M

-- BourgainRetainedPowerWindows: bourgain_retained_power_terms_le
example {N T V σ τ δ M : ℝ}
    (hN : 1 ≤ N) (hT : 0 ≤ T)
    (hTu : T ≤ N^(τ+δ)) (hVl : N^(σ-2*δ) ≤ V-1) :
    N^2/(V-1)^2 + T^2*N^4/(V-1)^8 + N^3*Real.sqrt M/(V-1)^4 ≤
      N^(2-2*σ+4*δ) + N^(2*τ+4-8*σ+18*δ) +
        N^(3-4*σ+8*δ)*Real.sqrt M :=
  @TaoTrudgianYang2025.bourgain_retained_power_terms_le N T V σ τ δ M hN hT hTu hVl

-- BourgainRetainedSource: bourgain_retained_source_power_bound
example {σ τ : ℝ} (hσ : 3/4 < σ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C δ : ℝ, 1 ≤ C ∧ 0 < δ ∧
      ∀ P : LargeValuePattern,
        C ≤ P.N → P.N ≤ P.T → P.T ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        ∃ W : Finset ℝ,
          W ⊆ P.reflectedOrdinates ∧ IsSeparated 2 W ∧ InBaseInterval P.T W ∧
          (P.ordinates.card : ℝ) ≤ C*P.N^ε*(W.card : ℝ) ∧
          (P.ordinates.card : ℝ) ≤ C *
            (P.N^(2-2*σ+ε) + P.N^(2*τ+4-8*σ+ε) +
              P.N^(3-4*σ+ε)*Real.sqrt (bourgainZetaDifferenceMoment W (P.N^ε))) :=
  @TaoTrudgianYang2025.bourgain_retained_source_power_bound σ τ hσ ε hε

-- BourgainSmallMass: bourgain_three_quarter_recurrence
example {R A B : ℝ}
    (hR : 0 ≤ R) (hA : 0 ≤ A) (h : R ≤ A+B*R^(3/4 : ℝ)) :
    R ≤ 2*A+16*B^4 :=
  @TaoTrudgianYang2025.bourgain_three_quarter_recurrence R A B hR hA h

-- BourgainSmallMass: bourgain_small_mass_sqrt_le
example {N R M α τ : ℝ}
    (hN : 0 < N) (hR : 0 ≤ R)
    (hm : M ≤ N^(-α)*R^(3/2 : ℝ)*N^(τ/2)) :
    Real.sqrt M ≤ N^(-α/2+τ/4)*R^(3/4 : ℝ) :=
  @TaoTrudgianYang2025.bourgain_small_mass_sqrt_le N R M α τ hN hR hm

-- BourgainSmallMass: bourgain_small_mass_power_bound
example {N R C σ τ α ν M : ℝ}
    (hN : 0 < N) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hm : M ≤ N^(-α)*R^(3/2 : ℝ)*N^(τ/2))
    (hr : R ≤ C*(N^(2-2*σ+ν)+N^(2*τ+4-8*σ+ν)+N^(3-4*σ+ν)*Real.sqrt M)) :
    R ≤ (2*C)*N^(2-2*σ+ν)+(2*C)*N^(2*τ+4-8*σ+ν)+
      (16*C^4)*N^(-2*α+τ+12-16*σ+4*ν) :=
  @TaoTrudgianYang2025.bourgain_small_mass_power_bound N R C σ τ α ν M hN hR hC hm hr

-- BourgainMassDichotomy: bourgain_retained_difference_level_dichotomy
example {σ τ : ℝ}
    (hσ : 3/4 < σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C δ : ℝ, 1 ≤ C ∧ 0 < δ ∧
      ∀ P : LargeValuePattern,
        C ≤ P.N → P.N ≤ P.T → P.T ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        ∃ W : Finset ℝ,
          W ⊆ P.reflectedOrdinates ∧ IsSeparated 2 W ∧ InBaseInterval P.T W ∧
          (P.ordinates.card : ℝ) ≤ C*P.N^ε*(W.card : ℝ) ∧
          ∀ α : ℝ,
            (P.ordinates.card : ℝ) ≤ C *
              (P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε)+P.N^(-2*α+τ+12-16*σ+ε)) ∨
            ∃ j ∈ Finset.range (Nat.log 2 W.card+1),
              (bourgainDifferenceLevel W j).Nonempty ∧
              2^j ≤ W.card ∧
              2^j*(bourgainDifferenceLevel W j).card ≤ 2*W.card^2 ∧
              P.N^(-α)*(W.card : ℝ)^(3/2 : ℝ)*P.N^(τ/2) <
                bourgainZetaDifferenceMoment W (P.N^(ε/8)) ∧
              bourgainZetaDifferenceMoment W (P.N^(ε/8)) ≤
                (Nat.log 2 W.card+1 : ℕ)*(2 : ℝ)^(j+1)*
                  ∑ ℓ ∈ bourgainDifferenceLevel W j,
                    bourgainLocalZetaSquare (P.N^(ε/8)) ℓ :=
  @TaoTrudgianYang2025.bourgain_retained_difference_level_dichotomy σ τ hσ ε hε

-- Monotonicity includes the zero window and empty pair set.
example (W : Finset ℝ) {H : ℝ} (hH : 0 ≤ H) :
    bourgainZetaDifferenceMoment W 0 ≤ bourgainZetaDifferenceMoment W H :=
  bourgainZetaDifferenceMoment_mono W (le_refl 0) hH
example {H K : ℝ} (hH : 0 ≤ H) (hHK : H ≤ K) :
    bourgainZetaDifferenceMoment ∅ H ≤ bourgainZetaDifferenceMoment ∅ K :=
  bourgainZetaDifferenceMoment_mono ∅ hH hHK
example (W : Finset ℝ) (H : ℝ) (hH : 0 ≤ H) :
    bourgainZetaDifferenceMoment W H ≤ bourgainZetaDifferenceMoment W H :=
  bourgainZetaDifferenceMoment_mono W hH (le_refl _)

-- The native ceiling and its unit enlargement are retained at theta zero.
example {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, (heathBrownSmoothingHeight T 0 : ℝ)+1 ≤ T^ε :=
  eventually_bourgain_smoothing_radius_le (le_refl 0) hε
example : (0 : ℝ) ≤ 2*0+16*0^4 :=
  bourgain_three_quarter_recurrence (R := 0) (A := 0) (B := 0)
    (by norm_num) (by norm_num) (by norm_num)
example {R B : ℝ} (hR : 0 ≤ R) (h : R ≤ B*R^(3/4 : ℝ)) :
    R ≤ 16*B^4 := by
  simpa using bourgain_three_quarter_recurrence hR (le_refl (0 : ℝ)) (by simpa using h)
example {R A : ℝ} (hR : 0 ≤ R) (hA : 0 ≤ A) (h : R ≤ A) :
    R ≤ 2*A := by
  simpa using bourgain_three_quarter_recurrence (B := 0) hR hA (by simpa using h)
example {N M : ℝ} (hN : 0 < N) (hM : M ≤ 0) :
    Real.sqrt M ≤ 0 := by
  simpa using bourgain_small_mass_sqrt_le (N := N) (R := 0) (α := 0) (τ := 1)
    hN (le_refl 0) (by simpa using hM)

-- The Add-est (ix) endpoint has a strict value-exponent gap; the source
-- height endpoint one is permitted when the actual N <= T condition holds.
example : (3/4 : ℝ) < 84/109 := by norm_num
example : (8 : ℝ)*(84/109)-6 = 18/109 := by norm_num
example {ε : ℝ} (hε : 0 < ε) :
    ∃ C δ : ℝ, 1 ≤ C ∧ 0 < δ ∧
      ∀ P : LargeValuePattern,
        C ≤ P.N → P.N ≤ P.T → P.T ≤ P.N^(1+δ) → P.N^(84/109-δ) ≤ P.V →
        ∃ W : Finset ℝ,
          W ⊆ P.reflectedOrdinates ∧ IsSeparated 2 W ∧ InBaseInterval P.T W ∧
          (P.ordinates.card : ℝ) ≤ C*P.N^ε*(W.card : ℝ) ∧
          (P.ordinates.card : ℝ) ≤ C *
            (P.N^(2-2*(84/109)+ε)+P.N^(2*1+4-8*(84/109)+ε)+
              P.N^(3-4*(84/109)+ε)*Real.sqrt (bourgainZetaDifferenceMoment W (P.N^ε))) :=
  bourgain_retained_source_power_bound (σ := 84/109) (τ := 1) (by norm_num) hε

end BourgainPowerMassRegression

namespace BourgainZetaBandRegression

open MeasureTheory RiemannZeta.GuthMaynard Set
open scoped Interval Classical

example (T V t : ℝ) :
    t ∈ bourgainZetaBand T V ↔
      -T ≤ t ∧ t ≤ T ∧ V ≤ zetaMomentCriticalNorm t ∧
        zetaMomentCriticalNorm t < 2*V :=
  @TaoTrudgianYang2025.mem_bourgainZetaBand T V t

example (T V : ℝ) :
    bourgainZetaBand T V ⊆ Icc (-T) T :=
  @TaoTrudgianYang2025.bourgainZetaBand_subset_Icc T V

example (T V : ℝ) :
    MeasurableSet (bourgainZetaBand T V) :=
  @TaoTrudgianYang2025.measurableSet_bourgainZetaBand T V

example (T V : ℝ) :
    volume (bourgainZetaBand T V) < ⊤ :=
  @TaoTrudgianYang2025.bourgainZetaBand_measure_lt_top T V

example {T V : ℝ} (hT : 0 ≤ T) (hV : 0 ≤ V) :
    V^4 * volume.real (bourgainZetaBand T V) ≤
      ∫ t in -T..T, zetaMomentCriticalNorm t^4 :=
  @TaoTrudgianYang2025.bourgainZetaBand_fourth_mass_le T V hT hV

example {η : ℝ} (hη : 0 < η) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧ ∀ T V : ℝ, T₀ ≤ T → 0 ≤ V →
      V^4 * volume.real (bourgainZetaBand T V) ≤ C*T^(1+η) :=
  @TaoTrudgianYang2025.bourgainZetaBand_fourth_bound η hη

example :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      zetaMomentCriticalNorm t ≤ C*(1+|t|) :=
  @TaoTrudgianYang2025.exists_zetaMomentCriticalNorm_le_linear

example (D : Finset ℤ) (S : Set ℝ) (u : ℝ) :
    bourgainBandOccupancy D S u =
      ((D.filter fun ℓ : ℤ => (ℓ : ℝ)+u ∈ S).card : ℝ) :=
  @TaoTrudgianYang2025.bourgainBandOccupancy_eq_card D S u

example (D : Finset ℤ) (S : Set ℝ) (u : ℝ) :
    0 ≤ bourgainBandOccupancy D S u ∧
      bourgainBandOccupancy D S u ≤ (D.card : ℝ) :=
  @TaoTrudgianYang2025.bourgainBandOccupancy_bounds D S u

example {S : Set ℝ} (hS : MeasurableSet S)
    (c a b : ℝ) :
    IntervalIntegrable (fun u => S.indicator (fun _ => (1 : ℝ)) (c+u)) volume a b :=
  @TaoTrudgianYang2025.bourgain_indicator_intervalIntegrable S hS c a b

example (D : Finset ℤ)
    {S : Set ℝ} (hS : MeasurableSet S) (a b : ℝ) :
    IntervalIntegrable (bourgainBandOccupancy D S) volume a b :=
  @TaoTrudgianYang2025.bourgainBandOccupancy_intervalIntegrable D S hS a b

example (D : Finset ℤ) (H T V : ℝ) :
    bourgainZetaBandMass D H T V =
      ∑ ℓ ∈ D, ∫ u in -H..H,
        (bourgainZetaBand T V).indicator (fun _ => (1 : ℝ)) ((ℓ : ℝ)+u) :=
  @TaoTrudgianYang2025.bourgainZetaBandMass_eq_sum D H T V

example (D : Finset ℤ) {H : ℝ} (hH : 0 ≤ H) (T V : ℝ) :
    0 ≤ bourgainZetaBandMass D H T V ∧
      bourgainZetaBandMass D H T V ≤ 2*H*(D.card : ℝ) :=
  @TaoTrudgianYang2025.bourgainZetaBandMass_bounds D H hH T V

example (D : Finset ℤ)
    {S : Set ℝ} (hS : MeasurableSet S) (hfin : volume S ≠ ⊤)
    {H : ℝ} (hH : 0 ≤ H) :
    (∫ u in -H..H, bourgainBandOccupancy D S u) ≤
      (2*Nat.ceil H+1 : ℕ) * volume.real S :=
  @TaoTrudgianYang2025.bourgainBandOccupancy_integral_le_measure D S hS hfin H hH

example (D : Finset ℤ)
    {H : ℝ} (hH : 0 ≤ H) (T V : ℝ) :
    bourgainZetaBandMass D H T V ≤
      (2*Nat.ceil H+1 : ℕ)*volume.real (bourgainZetaBand T V) :=
  @TaoTrudgianYang2025.bourgainZetaBandMass_le_measure D H hH T V

example {a x : ℝ} (hx : a ≤ x)
    {J : ℕ} (hupper : x < a*(2 : ℝ)^J) :
    ∃ j ∈ Finset.range J, a*(2 : ℝ)^j ≤ x ∧ x < 2*(a*(2 : ℝ)^j) :=
  @TaoTrudgianYang2025.exists_bourgain_dyadic_amplitude a x hx J hupper

example (B T a : ℝ) :
    0 < bourgainZetaBandCount B T a :=
  @TaoTrudgianYang2025.bourgainZetaBandCount_pos B T a

example {B T a : ℝ} (ha : 0 < a) :
    B*(1+T) < a*(2 : ℝ)^(bourgainZetaBandCount B T a) :=
  @TaoTrudgianYang2025.bourgainZetaBandCount_terminal B T a ha

example :
    ∃ B : ℝ, 0 < B ∧ ∀ T a : ℝ, 0 < a → ∀ t ∈ Icc (-T) T,
      zetaMomentCriticalNorm t < a*(2 : ℝ)^(bourgainZetaBandCount B T a) :=
  @TaoTrudgianYang2025.exists_bourgainZetaBand_terminal

example {T a t : ℝ}
    (ht : t ∈ Icc (-T) T) {J : ℕ}
    (hterminal : zetaMomentCriticalNorm t < a*(2 : ℝ)^J) :
    zetaMomentCriticalNorm t^2 ≤ a^2 +
      ∑ j ∈ Finset.range J, (2*(a*(2 : ℝ)^j))^2 *
        (bourgainZetaBand T (a*(2 : ℝ)^j)).indicator (fun _ => (1 : ℝ)) t :=
  @TaoTrudgianYang2025.bourgainZetaBand_square_partition T a t ht J hterminal

example (D : Finset ℤ)
    {H T a : ℝ} (hH : 0 ≤ H) {J : ℕ}
    (hrange : ∀ ℓ ∈ D, -T+H ≤ (ℓ : ℝ) ∧ (ℓ : ℝ) ≤ T-H)
    (hterminal : ∀ t ∈ Icc (-T) T, zetaMomentCriticalNorm t < a*(2 : ℝ)^J) :
    (∑ ℓ ∈ D, bourgainLocalZetaSquare H ℓ) ≤
      2*H*a^2*(D.card : ℝ) +
        ∑ j ∈ Finset.range J, (2*(a*(2 : ℝ)^j))^2 *
          bourgainZetaBandMass D H T (a*(2 : ℝ)^j) :=
  @TaoTrudgianYang2025.bourgainZetaBand_mass_partition D H T a hH J hrange hterminal

example (D : Finset ℤ)
    {H T a : ℝ} (hH : 0 ≤ H) {J : ℕ} (hJ : 0 < J)
    (hrange : ∀ ℓ ∈ D, -T+H ≤ (ℓ : ℝ) ∧ (ℓ : ℝ) ≤ T-H)
    (hterminal : ∀ t ∈ Icc (-T) T, zetaMomentCriticalNorm t < a*(2 : ℝ)^J) :
    ∃ j ∈ Finset.range J,
      (∑ ℓ ∈ D, bourgainLocalZetaSquare H ℓ) ≤ 2*H*a^2*(D.card : ℝ) +
        (J : ℝ)*(2*(a*(2 : ℝ)^j))^2*bourgainZetaBandMass D H T (a*(2 : ℝ)^j) :=
  @TaoTrudgianYang2025.bourgainZetaBand_select D H T a hH J hJ hrange hterminal

example {L H R : ℝ} (hL : 0 < L) (hH : 0 < H) (hR : 0 < R) :
    0 < Real.sqrt (L/(4*H*R)) ∧
      2*H*(Real.sqrt (L/(4*H*R)))^2*R = L/2 :=
  @TaoTrudgianYang2025.bourgainZetaBand_half_floor L H R hL hH hR

example {η : ℝ} (hη : 0 < η) :
    ∃ B C T₀ : ℝ, 0 < B ∧ 0 < C ∧ 1 ≤ T₀ ∧
      ∀ (D : Finset ℤ) (H T : ℝ), 0 < H → T₀ ≤ T →
        (∀ ℓ ∈ D, -T+H ≤ (ℓ : ℝ) ∧ (ℓ : ℝ) ≤ T-H) →
        let L := ∑ ℓ ∈ D, bourgainLocalZetaSquare H ℓ
        0 < L →
        let a := Real.sqrt (L/(4*H*(D.card : ℝ)))
        let J := bourgainZetaBandCount B T a
        ∃ j ∈ Finset.range J,
          let V := a*(2 : ℝ)^j
          0 < a ∧ 0 < V ∧ 0 < bourgainZetaBandMass D H T V ∧
          0 < volume.real (bourgainZetaBand T V) ∧
          L ≤ 2*(J : ℝ)*(2*V)^2*bourgainZetaBandMass D H T V ∧
          V^4*volume.real (bourgainZetaBand T V) ≤ C*T^(1+η) ∧
          bourgainZetaBandMass D H T V ≤ 2*H*(D.card : ℝ) ∧
          bourgainZetaBandMass D H T V ≤
            (2*Nat.ceil H+1 : ℕ)*volume.real (bourgainZetaBand T V) :=
  @TaoTrudgianYang2025.bourgainZetaBand_positive_selection η hη

example {f : ℝ → ℝ} {H : ℝ}
    (hH : 0 < H) (hf : IntervalIntegrable f volume (-H) H) :
    ∃ u ∈ Ioc (-H) H, (∫ v in -H..H, f v) ≤ 2*H*f u :=
  @TaoTrudgianYang2025.bourgain_interval_integral_common_shift f H hH hf

example {ι : Type*}
    (A : Finset ι) (w : ι → ℝ) (D : ι → Finset ℤ)
    {S : Set ℝ} (hS : MeasurableSet S) {H : ℝ} (hH : 0 < H) :
    ∃ u ∈ Ioc (-H) H,
      (∑ i ∈ A, w i*(∫ v in -H..H, bourgainBandOccupancy (D i) S v)) ≤
        2*H*∑ i ∈ A, w i*bourgainBandOccupancy (D i) S u :=
  @TaoTrudgianYang2025.bourgainBandOccupancy_weighted_common_shift ι A w D S hS H hH

example (D : Finset ℤ) {H T V : ℝ}
    (hH : 0 < H) (hmass : 0 < bourgainZetaBandMass D H T V) :
    ∃ u ∈ Ioc (-H) H,
      (D.filter fun ℓ : ℤ => (ℓ : ℝ)+u ∈ bourgainZetaBand T V).Nonempty ∧
      bourgainZetaBandMass D H T V ≤
        2*H*((D.filter fun ℓ : ℤ => (ℓ : ℝ)+u ∈ bourgainZetaBand T V).card : ℝ) :=
  @TaoTrudgianYang2025.bourgainZetaBandMass_common_shift D H T V hH hmass

example (D : Finset ℤ) {H T V : ℝ}
    (hH : 0 < H) (hmass : 0 < bourgainZetaBandMass D H T V) :
    let r := bourgainZetaBandCorrelation D H T V
    let μ := volume.real (bourgainZetaBand T V)
    let R := (D.card : ℝ)
    let K := (2*Nat.ceil H+1 : ℕ)
    0 < r ∧ 0 < μ ∧ 0 < R ∧
    bourgainZetaBandMass D H T V = r*Real.sqrt μ*Real.sqrt R ∧
    r^2 ≤ 2*H*(K : ℝ) ∧
    r^2*μ ≤ 4*H^2*R ∧
    r^2*R ≤ (K : ℝ)^2*μ :=
  @TaoTrudgianYang2025.bourgainZetaBandCorrelation_bounds D H T V hH hmass

example {σ τ : ℝ}
    (hσ : 3/4 < σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B C δ : ℝ, 0 < B ∧ 1 ≤ C ∧ 0 < δ ∧
      ∀ P : LargeValuePattern,
        C ≤ P.N → P.N ≤ P.T → P.T ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        ∃ W : Finset ℝ,
          W ⊆ P.reflectedOrdinates ∧ IsSeparated 2 W ∧ InBaseInterval P.T W ∧
          (P.ordinates.card : ℝ) ≤ C*P.N^ε*(W.card : ℝ) ∧
          ∀ α : ℝ,
            (P.ordinates.card : ℝ) ≤ C *
              (P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε)+P.N^(-2*α+τ+12-16*σ+ε)) ∨
            ∃ j ∈ Finset.range (Nat.log 2 W.card+1),
              let D := bourgainDifferenceLevel W j
              let H := P.N^(ε/8)
              let U := P.T+H+1
              let L := ∑ ℓ ∈ D, bourgainLocalZetaSquare H ℓ
              let a := Real.sqrt (L/(4*H*(D.card : ℝ)))
              let J := bourgainZetaBandCount B U a
              D.Nonempty ∧ 2^j ≤ W.card ∧ 2^j*D.card ≤ 2*W.card^2 ∧
              ∃ q ∈ Finset.range J,
                let V := a*(2 : ℝ)^q
                let K := 2*(Nat.log 2 W.card+1 : ℕ)*(2 : ℝ)^(j+1)*(J : ℝ)*(2*V)^2
                let r := bourgainZetaBandCorrelation D H U V
                0 < L ∧ 0 < a ∧ 0 < V ∧ 0 < bourgainZetaBandMass D H U V ∧
                0 < volume.real (bourgainZetaBand U V) ∧
                P.N^(-α)*(W.card : ℝ)^(3/2 : ℝ)*P.N^(τ/2) <
                  K*bourgainZetaBandMass D H U V ∧
                V^4*volume.real (bourgainZetaBand U V) ≤ C*U^(1+ε) ∧
                bourgainZetaBandMass D H U V ≤ 2*H*(D.card : ℝ) ∧
                bourgainZetaBandMass D H U V ≤
                  (2*Nat.ceil H+1 : ℕ)*volume.real (bourgainZetaBand U V) ∧
                0 < r ∧
                bourgainZetaBandMass D H U V =
                  r*Real.sqrt (volume.real (bourgainZetaBand U V))*Real.sqrt (D.card : ℝ) ∧
                r^2 ≤ 2*H*(2*Nat.ceil H+1 : ℕ) ∧
                r^2*volume.real (bourgainZetaBand U V) ≤ 4*H^2*(D.card : ℝ) ∧
                r^2*(D.card : ℝ) ≤ (2*Nat.ceil H+1 : ℕ)^2*volume.real (bourgainZetaBand U V) ∧
                ∃ u ∈ Set.Ioc (-H) H,
                  (D.filter fun ℓ : ℤ => (ℓ : ℝ)+u ∈ bourgainZetaBand U V).Nonempty ∧
                  P.N^(-α)*(W.card : ℝ)^(3/2 : ℝ)*P.N^(τ/2) <
                    K*(2*H)*((D.filter fun ℓ : ℤ =>
                      (ℓ : ℝ)+u ∈ bourgainZetaBand U V).card : ℝ) :=
  @TaoTrudgianYang2025.bourgain_retained_zeta_band_dichotomy σ τ hσ ε hε

-- Actual empty and zero-width windows retain their literal semantics.
example (S : Set ℝ) (u : ℝ) : bourgainBandOccupancy ∅ S u = 0 := by
  simp [bourgainBandOccupancy]

example (D : Finset ℤ) (u : ℝ) : bourgainBandOccupancy D ∅ u = 0 := by
  simp [bourgainBandOccupancy]

example (D : Finset ℤ) (T V : ℝ) : bourgainZetaBandMass D 0 T V = 0 := by
  simp [bourgainZetaBandMass]

example (H T V : ℝ) : bourgainZetaBandMass ∅ H T V = 0 := by
  simp [bourgainZetaBandMass, bourgainBandOccupancy]

example (T : ℝ) : bourgainZetaBand T 0 = ∅ := by
  ext t
  simp only [mem_bourgainZetaBand, mem_empty_iff_false, iff_false]
  intro ht
  have hn : 0 ≤ zetaMomentCriticalNorm t := norm_nonneg _
  linarith [ht.2.2.2]

example {T V t : ℝ} (h : zetaMomentCriticalNorm t = 2*V) :
    t ∉ bourgainZetaBand T V := by
  intro ht
  have hh := ((mem_bourgainZetaBand _ _ _).mp ht).2.2.2
  linarith

example {T V t : ℝ} (hV : 0 < V) (ht : t ∈ Icc (-T) T)
    (h : zetaMomentCriticalNorm t = V) : t ∈ bourgainZetaBand T V := by
  exact (mem_bourgainZetaBand _ _ _).mpr ⟨ht.1, ht.2, h.ge, by linarith⟩

example (T V : ℝ) : Disjoint (bourgainZetaBand T V) (bourgainZetaBand T (2*V)) := by
  apply Set.disjoint_left.mpr
  intro t ht hs
  have hu := ((mem_bourgainZetaBand _ _ _).mp ht).2.2.2
  have hl := ((mem_bourgainZetaBand _ _ _).mp hs).2.2.1
  exact (not_lt_of_ge hl) hu

example : bourgainZetaBandCount 1 0 1 = 1 := by
  norm_num [bourgainZetaBandCount, Nat.clog]

example : bourgainZetaBandCount 1 3 1 = 3 := by
  norm_num [bourgainZetaBandCount, Nat.clog]

example {j : ℕ} (hj : j ∈ Finset.range 2)
    (h : (2 : ℝ)^j ≤ 2 ∧ 2 < 2*(2 : ℝ)^j) : j = 1 := by
  have hb := Finset.mem_range.mp hj
  interval_cases j <;> norm_num at *

example : 2*(3 : ℝ)*(Real.sqrt (24/(4*3*2)))^2*2 = 24/2 :=
  (bourgainZetaBand_half_floor (by norm_num : (0 : ℝ) < 24)
    (by norm_num : (0 : ℝ) < 3) (by norm_num : (0 : ℝ) < 2)).2

example (T V : ℝ) : bourgainZetaBandCorrelation ∅ 0 T V = 0 := by
  simp [bourgainZetaBandCorrelation, bourgainZetaBandMass]

-- A common-shift lemma does not require positive weights.
example {H : ℝ} (hH : 0 < H) :
    ∃ u ∈ Ioc (-H) H, (0 : ℝ) ≤ 2*H*(0 : ℝ) := by
  simpa using bourgainBandOccupancy_weighted_common_shift
    (∅ : Finset ℕ) (fun _ => (0 : ℝ)) (fun _ => (∅ : Finset ℤ))
    (S := ∅) MeasurableSet.empty hH

end BourgainZetaBandRegression

namespace BourgainSharedGridRegression

open MeasureTheory RiemannZeta.GuthMaynard Set
open scoped Interval Classical

example (α τ : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    0 < bourgainSharedFloorExponent α τ ε :=
  @TaoTrudgianYang2025.bourgainSharedFloorExponent_pos α τ ε hε

example {α τ ε : ℝ} (hε : 0 ≤ ε) :
    ε/8-2*bourgainSharedFloorExponent α τ ε+3*(|τ|+1)+7 ≤ -α+τ/2 :=
  @TaoTrudgianYang2025.bourgain_shared_floor_exponent α τ ε hε

example {N α τ ε : ℝ}
    (hN : 2 ≤ N) (hε : 0 ≤ ε) :
    128*N^(ε/8)*(N^(-bourgainSharedFloorExponent α τ ε))^2*
      (N^(|τ|+1))^3 ≤ N^(-α+τ/2) :=
  @TaoTrudgianYang2025.bourgain_shared_floor_power_bound N α τ ε hN hε

example (W : Finset ℝ) (j : ℕ)
    {H a : ℝ} (hH : 0 ≤ H) (hW : 0 < W.card) :
    2*(Nat.log 2 W.card+1 : ℕ)*(2 : ℝ)^(j+1)*
      (2*H*a^2*((bourgainDifferenceLevel W j).card : ℝ)) ≤
        16*H*a^2*(W.card : ℝ)^3 :=
  @TaoTrudgianYang2025.bourgain_difference_level_low_mass W j H a hH hW

example (P : LargeValuePattern)
    {W : Finset ℝ} (hsub : W ⊆ P.reflectedOrdinates) {τ δ : ℝ}
    (hδ : δ ≤ 1) (hT : P.T ≤ P.N^(τ+δ)) :
    (W.card : ℝ) ≤ 2*P.N^(|τ|+1) :=
  @TaoTrudgianYang2025.bourgain_retained_card_le_shared_power P W hsub τ δ hδ hT

example (P : LargeValuePattern)
    {W : Finset ℝ} (hsub : W ⊆ P.reflectedOrdinates) (j : ℕ)
    (hW : 0 < W.card) {α τ ε δ : ℝ}
    (hN : 2 ≤ P.N) (hε : 0 ≤ ε) (hδ : δ ≤ 1) (hT : P.T ≤ P.N^(τ+δ)) :
    2*(Nat.log 2 W.card+1 : ℕ)*(2 : ℝ)^(j+1)*
      (2*P.N^(ε/8)*(P.N^(-bourgainSharedFloorExponent α τ ε))^2*
        ((bourgainDifferenceLevel W j).card : ℝ)) ≤
      P.N^(-α)*(W.card : ℝ)^(3/2 : ℝ)*P.N^(τ/2) :=
  @TaoTrudgianYang2025.bourgain_shared_floor_low_bound P W hsub j hW α τ ε δ hN hε hδ hT

example {η : ℝ} (hη : 0 < η) :
    ∃ B C T₀ : ℝ, 0 < B ∧ 0 < C ∧ 1 ≤ T₀ ∧
      ∀ (D : Finset ℤ) (H T a : ℝ), 0 < H → 0 < a → T₀ ≤ T →
        (∀ ℓ ∈ D, -T+H ≤ (ℓ : ℝ) ∧ (ℓ : ℝ) ≤ T-H) →
        let L := ∑ ℓ ∈ D, bourgainLocalZetaSquare H ℓ
        2*(2*H*a^2*(D.card : ℝ)) < L →
        let J := bourgainZetaBandCount B T a
        ∃ j ∈ Finset.range J,
          let V := a*(2 : ℝ)^j
          0 < V ∧ 0 < bourgainZetaBandMass D H T V ∧
          0 < volume.real (bourgainZetaBand T V) ∧
          L ≤ 2*(J : ℝ)*(2*V)^2*bourgainZetaBandMass D H T V ∧
          V^4*volume.real (bourgainZetaBand T V) ≤ C*T^(1+η) ∧
          bourgainZetaBandMass D H T V ≤ 2*H*(D.card : ℝ) ∧
          bourgainZetaBandMass D H T V ≤
            (2*Nat.ceil H+1 : ℕ)*volume.real (bourgainZetaBand T V) :=
  @TaoTrudgianYang2025.bourgainZetaBand_fixed_floor_selection η hη

example (P : LargeValuePattern) {τ ε δ : ℝ}
    (hε : 0 ≤ ε) (hδ : δ ≤ 1) (hT : P.T ≤ P.N^(τ+δ)) :
    P.T+P.N^(ε/8)+1 ≤ 3*P.N^(|τ|+ε+1) :=
  @TaoTrudgianYang2025.bourgain_shared_band_radius_le P τ ε δ hε hδ hT

example {B N U A u : ℝ}
    (hB : 0 < B) (hN : 1 ≤ N) (hU : 0 ≤ U) (hA : 0 ≤ A) (hu : 0 ≤ u)
    (hcap : U ≤ 3*N^u) :
    (bourgainZetaBandCount B U (N^(-A)) : ℝ) ≤
      2+(Real.log (4*B+1)+(u+A)*Real.log N)/Real.log 2 :=
  @TaoTrudgianYang2025.bourgainZetaBandCount_power_log_bound B N U A u hB hN hU hA hu hcap

example {B A u η : ℝ}
    (hB : 0 < B) (hA : 0 ≤ A) (hu : 0 ≤ u) (hη : 0 < η) :
    ∃ C N₀ : ℝ, 1 ≤ C ∧ 2 ≤ N₀ ∧ ∀ N U : ℝ, N₀ ≤ N → 0 ≤ U → U ≤ 3*N^u →
      (bourgainZetaBandCount B U (N^(-A)) : ℝ) ≤ C*N^η :=
  @TaoTrudgianYang2025.bourgainZetaBandCount_uniform_power B A u η hB hA hu hη

example {σ τ : ℝ}
    (hσ : 3/4 < σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B C δ : ℝ, 0 < B ∧ 2 ≤ C ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ P : LargeValuePattern,
        C ≤ P.N → P.N ≤ P.T → P.T ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        ∃ W : Finset ℝ,
          W ⊆ P.reflectedOrdinates ∧ IsSeparated 2 W ∧ InBaseInterval P.T W ∧
          (P.ordinates.card : ℝ) ≤ C*P.N^ε*(W.card : ℝ) ∧
          ∀ α : ℝ,
            (P.ordinates.card : ℝ) ≤ C *
              (P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε)+P.N^(-2*α+τ+12-16*σ+ε)) ∨
            ∃ j ∈ Finset.range (Nat.log 2 W.card+1),
              let D := bourgainDifferenceLevel W j
              let H := P.N^(ε/8)
              let U := P.T+H+1
              let L := ∑ ℓ ∈ D, bourgainLocalZetaSquare H ℓ
              let A := bourgainSharedFloorExponent α τ ε
              let a := P.N^(-A)
              let J := bourgainZetaBandCount B U a
              D.Nonempty ∧ 2^j ≤ W.card ∧ 2^j*D.card ≤ 2*W.card^2 ∧
              ∃ q ∈ Finset.range J,
                let V := a*(2 : ℝ)^q
                let K := 2*(Nat.log 2 W.card+1 : ℕ)*(2 : ℝ)^(j+1)*(J : ℝ)*(2*V)^2
                let r := bourgainZetaBandCorrelation D H U V
                0 < L ∧ 0 < a ∧ 0 < V ∧ 0 < bourgainZetaBandMass D H U V ∧
                0 < volume.real (bourgainZetaBand U V) ∧
                P.N^(-α)*(W.card : ℝ)^(3/2 : ℝ)*P.N^(τ/2) <
                  K*bourgainZetaBandMass D H U V ∧
                V^4*volume.real (bourgainZetaBand U V) ≤ C*U^(1+ε) ∧
                bourgainZetaBandMass D H U V ≤ 2*H*(D.card : ℝ) ∧
                bourgainZetaBandMass D H U V ≤
                  (2*Nat.ceil H+1 : ℕ)*volume.real (bourgainZetaBand U V) ∧
                0 < r ∧
                bourgainZetaBandMass D H U V =
                  r*Real.sqrt (volume.real (bourgainZetaBand U V))*Real.sqrt (D.card : ℝ) ∧
                r^2 ≤ 2*H*(2*Nat.ceil H+1 : ℕ) ∧
                r^2*volume.real (bourgainZetaBand U V) ≤ 4*H^2*(D.card : ℝ) ∧
                r^2*(D.card : ℝ) ≤ (2*Nat.ceil H+1 : ℕ)^2*volume.real (bourgainZetaBand U V) ∧
                (J : ℝ) ≤
                  2+(Real.log (4*B+1)+(|τ|+ε+1+A)*Real.log P.N)/Real.log 2 ∧
                ∃ u ∈ Set.Ioc (-H) H,
                  (D.filter fun ℓ : ℤ => (ℓ : ℝ)+u ∈ bourgainZetaBand U V).Nonempty ∧
                  P.N^(-α)*(W.card : ℝ)^(3/2 : ℝ)*P.N^(τ/2) <
                    K*(2*H)*((D.filter fun ℓ : ℤ =>
                      (ℓ : ℝ)+u ∈ bourgainZetaBand U V).card : ℝ) :=
  @TaoTrudgianYang2025.bourgain_retained_shared_grid_dichotomy σ τ hσ ε hε

example (P : LargeValuePattern) (W : Finset ℝ) :
    (P.retainedOriginal W).card = W.card :=
  @TaoTrudgianYang2025.LargeValuePattern.retainedOriginal_card P W

example (P : LargeValuePattern)
    {W : Finset ℝ} (hW : W ⊆ P.reflectedOrdinates) :
    P.retainedOriginal W ⊆ P.ordinates :=
  @TaoTrudgianYang2025.LargeValuePattern.retainedOriginal_subset P W hW

example (P : LargeValuePattern)
    {W : Finset ℝ} {δ : ℝ} (hsep : IsSeparated δ W) :
    IsSeparated δ (P.retainedOriginal W) :=
  @TaoTrudgianYang2025.LargeValuePattern.retainedOriginal_isSeparated P W δ hsep

example (P : LargeValuePattern)
    {W : Finset ℝ} (hW : W ⊆ P.reflectedOrdinates) :
    ∀ t ∈ P.retainedOriginal W,
      P.V ≤ ‖∑ n ∈ P.indices, P.coeff n * dirichletPhase n t‖ :=
  @TaoTrudgianYang2025.LargeValuePattern.retainedOriginal_large P W hW

example (W : Finset ℝ) (c : ℝ) (ℓ : ℤ) :
    bourgainDifferenceCount (W.image (fun t => c-t)) ℓ = bourgainDifferenceCount W ℓ :=
  @TaoTrudgianYang2025.bourgainDifferenceCount_reflected W c ℓ

example
    (P : LargeValuePattern) (W : Finset ℝ) (ℓ : ℤ) :
    bourgainDifferenceCount (P.retainedOriginal W) ℓ = bourgainDifferenceCount W ℓ :=
  @TaoTrudgianYang2025.LargeValuePattern.retainedOriginal_differenceCount P W ℓ

example (P : LargeValuePattern)
    {L : ℝ} (hL : 0 < L) (j : ℕ) {W : Finset ℝ}
    (hW : W ⊆ (P.localized L hL j).reflectedOrdinates) (hsep : IsSeparated 2 W) :
    let S := (P.localized L hL j).retainedOriginal W
    S ⊆ P.localBin L j ∧ S ⊆ P.ordinates ∧ S.card = W.card ∧
    IsSeparated 2 S ∧
    (∀ ℓ : ℤ, bourgainDifferenceCount S ℓ = bourgainDifferenceCount W ℓ) ∧
    (∀ t ∈ S, P.V ≤ ‖∑ n ∈ P.indices, P.coeff n * dirichletPhase n t‖) :=
  @TaoTrudgianYang2025.LargeValuePattern.localized_retainedOriginal P L hL j W hW hsep

example (P : LargeValuePattern)
    (L : ℝ) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (P.localBin L i) (P.localBin L j) :=
  @TaoTrudgianYang2025.LargeValuePattern.localBin_disjoint P L i j hij

example (P : LargeValuePattern)
    {L : ℝ} (hL : 0 < L) {i j : ℕ} (hij : i ≠ j) {W Z : Finset ℝ}
    (hW : W ⊆ (P.localized L hL i).reflectedOrdinates)
    (hZ : Z ⊆ (P.localized L hL j).reflectedOrdinates) :
    Disjoint ((P.localized L hL i).retainedOriginal W)
      ((P.localized L hL j).retainedOriginal Z) :=
  @TaoTrudgianYang2025.LargeValuePattern.localized_retainedOriginal_disjoint P L hL i j hij W Z hW hZ

example (P : LargeValuePattern)
    {L : ℝ} (hL : 0 < L) (A : Finset ℕ) (W : ℕ → Finset ℝ)
    (hW : ∀ i ∈ A, W i ⊆ (P.localized L hL i).reflectedOrdinates) :
    let S := A.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))
    S ⊆ P.ordinates ∧ S.card = ∑ i ∈ A, (W i).card ∧ IsSeparated 1 S ∧
    (∀ t ∈ S, P.V ≤ ‖∑ n ∈ P.indices, P.coeff n * dirichletPhase n t‖) :=
  @TaoTrudgianYang2025.LargeValuePattern.localized_retainedOriginal_union P L hL A W hW

example {σ τ : ℝ}
    (hσ : 3/4 < σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B C δ : ℝ, 0 < B ∧ 2 ≤ C ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ (P : LargeValuePattern) (L : ℝ) (hL : 0 < L),
        C ≤ P.N → P.N ≤ L → L ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        ∃ W : ℕ → Finset ℝ,
          (∀ i : ℕ, (W i) ⊆ (P.localized L hL i).reflectedOrdinates ∧ IsSeparated 2 (W i) ∧ InBaseInterval L (W i) ∧
          ((P.localized L hL i).ordinates.card : ℝ) ≤ C*P.N^ε*((W i).card : ℝ) ∧
          ∀ α : ℝ,
            ((P.localized L hL i).ordinates.card : ℝ) ≤ C *
              (P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε)+P.N^(-2*α+τ+12-16*σ+ε)) ∨
            ∃ j ∈ Finset.range (Nat.log 2 (W i).card+1),
              let D := bourgainDifferenceLevel (W i) j
              let H := P.N^(ε/8)
              let U := L+H+1
              let L := ∑ ℓ ∈ D, bourgainLocalZetaSquare H ℓ
              let A := bourgainSharedFloorExponent α τ ε
              let a := P.N^(-A)
              let J := bourgainZetaBandCount B U a
              D.Nonempty ∧ 2^j ≤ (W i).card ∧ 2^j*D.card ≤ 2*(W i).card^2 ∧
              ∃ q ∈ Finset.range J,
                let V := a*(2 : ℝ)^q
                let K := 2*(Nat.log 2 (W i).card+1 : ℕ)*(2 : ℝ)^(j+1)*(J : ℝ)*(2*V)^2
                let r := bourgainZetaBandCorrelation D H U V
                0 < L ∧ 0 < a ∧ 0 < V ∧ 0 < bourgainZetaBandMass D H U V ∧
                0 < volume.real (bourgainZetaBand U V) ∧
                P.N^(-α)*((W i).card : ℝ)^(3/2 : ℝ)*P.N^(τ/2) <
                  K*bourgainZetaBandMass D H U V ∧
                V^4*volume.real (bourgainZetaBand U V) ≤ C*U^(1+ε) ∧
                bourgainZetaBandMass D H U V ≤ 2*H*(D.card : ℝ) ∧
                bourgainZetaBandMass D H U V ≤
                  (2*Nat.ceil H+1 : ℕ)*volume.real (bourgainZetaBand U V) ∧
                0 < r ∧
                bourgainZetaBandMass D H U V =
                  r*Real.sqrt (volume.real (bourgainZetaBand U V))*Real.sqrt (D.card : ℝ) ∧
                r^2 ≤ 2*H*(2*Nat.ceil H+1 : ℕ) ∧
                r^2*volume.real (bourgainZetaBand U V) ≤ 4*H^2*(D.card : ℝ) ∧
                r^2*(D.card : ℝ) ≤ (2*Nat.ceil H+1 : ℕ)^2*volume.real (bourgainZetaBand U V) ∧
                (J : ℝ) ≤
                  2+(Real.log (4*B+1)+(|τ|+ε+1+A)*Real.log P.N)/Real.log 2 ∧
                ∃ u ∈ Set.Ioc (-H) H,
                  (D.filter fun ℓ : ℤ => (ℓ : ℝ)+u ∈ bourgainZetaBand U V).Nonempty ∧
                  P.N^(-α)*((W i).card : ℝ)^(3/2 : ℝ)*P.N^(τ/2) <
                    K*(2*H)*((D.filter fun ℓ : ℤ =>
                      (ℓ : ℝ)+u ∈ bourgainZetaBand U V).card : ℝ)) ∧
          let I := Finset.range (Nat.floor (P.T/L)+1)
          let S := I.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))
          S ⊆ P.ordinates ∧ S.card = ∑ i ∈ I, (W i).card ∧
          IsSeparated 1 S ∧
          (∀ t ∈ S, P.V ≤ ‖∑ n ∈ P.indices, P.coeff n * dirichletPhase n t‖) ∧
          (P.ordinates.card : ℝ) ≤ C*P.N^ε*(S.card : ℝ) ∧
          (∀ i : ℕ, ∀ ℓ : ℤ,
            bourgainDifferenceCount ((P.localized L hL i).retainedOriginal (W i)) ℓ =
              bourgainDifferenceCount (W i) ℓ) :=
  @TaoTrudgianYang2025.bourgain_subdivided_shared_grid σ τ hσ ε hε

-- The physical floor is shared, including negative alpha and tau.
example : bourgainSharedFloorExponent 0 0 0 = 20 := by
  norm_num [bourgainSharedFloorExponent]

example : bourgainSharedFloorExponent (-3) (-2) 1 = 32 := by
  norm_num [bourgainSharedFloorExponent]

example (α τ ε : ℝ) :
    bourgainSharedFloorExponent (-α) (-τ) ε = bourgainSharedFloorExponent α τ ε := by
  simp [bourgainSharedFloorExponent]

example :
    (0 : ℝ)/8-2*bourgainSharedFloorExponent (-100) (-3) 0+3*(|(-3 : ℝ)|+1)+7 ≤
      -(-100 : ℝ)+(-3)/2 :=
  bourgain_shared_floor_exponent (by norm_num)

example (P : LargeValuePattern) (L : ℝ) (hL : 0 < L) (i : ℕ) (α τ ε : ℝ) :
    (P.localized L hL i).N^(-bourgainSharedFloorExponent α τ ε) =
      P.N^(-bourgainSharedFloorExponent α τ ε) := rfl

example (P : LargeValuePattern) (L : ℝ) (hL : 0 < L) (i : ℕ) (B α τ ε : ℝ) :
    bourgainZetaBandCount B
      ((P.localized L hL i).T+(P.localized L hL i).N^(ε/8)+1)
      ((P.localized L hL i).N^(-bourgainSharedFloorExponent α τ ε)) =
    bourgainZetaBandCount B (L+P.N^(ε/8)+1)
      (P.N^(-bourgainSharedFloorExponent α τ ε)) := rfl

example (P : LargeValuePattern) (L : ℝ) (hL : 0 < L) (i : ℕ) :
    (P.localized L hL i).coeff = P.coeff := rfl

-- Actual reflection and strict bins, not a surrogate set.
example (P : LargeValuePattern) : P.retainedOriginal ∅ = ∅ := by
  simp [LargeValuePattern.retainedOriginal]

example (P : LargeValuePattern) :
    P.retainedOriginal P.reflectedOrdinates = P.ordinates := by
  apply Finset.eq_of_subset_of_card_le (P.retainedOriginal_subset (Finset.Subset.refl _))
  rw [P.retainedOriginal_card, P.reflectedOrdinates_card]

example (c : ℝ) (ℓ : ℤ) : bourgainDifferenceCount ((∅ : Finset ℝ).image (fun t => c-t)) ℓ = 0 := by
  simp [bourgainDifferenceCount]

example : bourgainDifferenceCount ({0,1} : Finset ℝ) 0 = 2 := by
  norm_num [bourgainDifferenceCount, Finset.product_eq_biUnion, Finset.filter_insert,
    Finset.filter_singleton]

example : bourgainDifferenceCount ({0,1} : Finset ℝ) 1 = 1 := by
  norm_num [bourgainDifferenceCount, Finset.product_eq_biUnion, Finset.filter_insert,
    Finset.filter_singleton]

example :
    bourgainDifferenceCount (({0,1} : Finset ℝ).image (fun t => (7 : ℝ)-t)) 1 =
      bourgainDifferenceCount ({0,1} : Finset ℝ) 1 :=
  bourgainDifferenceCount_reflected _ _ _

example (P : LargeValuePattern) (L : ℝ) :
    Disjoint (P.localBin L 0) (P.localBin L 1) :=
  P.localBin_disjoint L (by decide)

example (P : LargeValuePattern) (L : ℝ) (hL : 0 < L) (W : ℕ → Finset ℝ) :
    ((∅ : Finset ℕ).biUnion
      (fun i => (P.localized L hL i).retainedOriginal (W i))).card = 0 := by simp

end BourgainSharedGridRegression

namespace BourgainCommonComponentRegression

open MeasureTheory
open scoped Classical

-- Full public types retain the original pattern, all ranges, and exact losses.

example {ι : Type*} (I : Finset ι)
    (w : ι → ℝ) (q : ι → ℕ) {J : ℕ} (hJ : 0 < J)
    (hq : ∀ i ∈ I, q i ∈ Finset.range J) :
    ∃ q₀ ∈ Finset.range J,
      (∑ i ∈ I, w i) ≤ (J : ℝ) * ∑ i ∈ I.filter (fun i => q i = q₀), w i :=
  @TaoTrudgianYang2025.bourgain_exists_heavy_component_fiber ι I w q J hJ hq

example {ι : Type*} (I : Finset ι)
    (R w : ι → ℝ) (q : ι → ℕ) {F K : ℝ} (hF : 0 ≤ F) (hK : 0 ≤ K)
    {J : ℕ} (hJ : 0 < J)
    (hpack : ∀ i ∈ I, F < R i → R i ≤ K*w i)
    (hq : ∀ i ∈ I, F < R i → q i ∈ Finset.range J) :
    ∃ q₀ ∈ Finset.range J,
      let A := I.filter (fun i => F < R i ∧ q i = q₀)
      (∑ i ∈ I, R i) ≤ (I.card : ℝ)*F + K*(J : ℝ)*∑ i ∈ A, w i :=
  @TaoTrudgianYang2025.bourgain_small_large_component_selection ι I R w q F K hF hK J hJ hpack hq

example {σ τ : ℝ}
    (hσ : 3/4 < σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B C δ : ℝ, 0 < B ∧ 2 ≤ C ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ (P : LargeValuePattern) (L : ℝ) (hL : 0 < L),
        C ≤ P.N → P.N ≤ L → L ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        ∃ W : ℕ → Finset ℝ,
          (∀ i : ℕ, W i ⊆ (P.localized L hL i).reflectedOrdinates ∧
            IsSeparated 2 (W i) ∧ InBaseInterval L (W i) ∧
            ((P.localized L hL i).ordinates.card : ℝ) ≤ C*P.N^ε*((W i).card : ℝ)) ∧
          ∀ α : ℝ,
            let I := Finset.range (Nat.floor (P.T/L)+1)
            let a := P.N^(-bourgainSharedFloorExponent α τ ε)
            let J := bourgainZetaBandCount B (L+P.N^(ε/8)+1) a
            let F := C*(P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε)+
              P.N^(-2*α+τ+12-16*σ+ε))
            ∃ q ∈ Finset.range J, ∃ A : Finset ℕ, A ⊆ I ∧
              ∃ j : ℕ → ℕ,
                (∀ i ∈ A, F < ((P.localized L hL i).ordinates.card : ℝ) ∧
                  BourgainComponentBand P.N L B C τ α ε (W i) (j i) q) ∧
                let S := A.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))
                S ⊆ P.ordinates ∧ S.card = ∑ i ∈ A, (W i).card ∧
                IsSeparated 1 S ∧
                (∀ t ∈ S, P.V ≤ ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n t‖) ∧
                (∀ i ∈ A, ∀ ℓ : ℤ,
                  bourgainDifferenceCount ((P.localized L hL i).retainedOriginal (W i)) ℓ =
                    bourgainDifferenceCount (W i) ℓ) ∧
                (P.ordinates.card : ℝ) ≤
                  (I.card : ℝ)*F+C*P.N^ε*(J : ℝ)*(S.card : ℝ) :=
  @TaoTrudgianYang2025.bourgain_subdivided_common_band σ τ hσ ε hε

example (N τ : ℝ) :
    0 < bourgainRelativeLevelCount N τ :=
  @TaoTrudgianYang2025.bourgainRelativeLevelCount_pos N τ

example {N τ : ℝ} (hN : 1 ≤ N) :
    (bourgainRelativeLevelCount N τ : ℝ) ≤
      2+(Real.log 5+(|τ|+2)*Real.log N)/Real.log 2 :=
  @TaoTrudgianYang2025.bourgainRelativeLevelCount_log_bound N τ hN

example {N τ : ℝ} {R j : ℕ}
    (hN : 2 ≤ N) (hR : 0 < R) (hsize : (R : ℝ) ≤ 2*N^(|τ|+1))
    (hj : 2^j ≤ R) :
    N^(-(|τ|+2)) ≤ (2 : ℝ)^j/(R : ℝ) ∧ (2 : ℝ)^j/(R : ℝ) ≤ 1 :=
  @TaoTrudgianYang2025.bourgain_relative_difference_floor N τ R j hN hR hsize hj

example (P : LargeValuePattern)
    {W : Finset ℝ} (hsub : W ⊆ P.reflectedOrdinates) (j : ℕ)
    (hj : 2^j ≤ W.card) {τ δ : ℝ} (hN : 2 ≤ P.N)
    (hδ : δ ≤ 1) (hT : P.T ≤ P.N^(τ+δ)) :
    ∃ p ∈ Finset.range (bourgainRelativeLevelCount P.N τ),
      let d := bourgainRelativeLevel P.N τ p
      0 < d ∧ d ≤ 1 ∧
      d*(W.card : ℝ) ≤ (2 : ℝ)^j ∧ (2 : ℝ)^j < 2*d*(W.card : ℝ) ∧
      (∀ ℓ ∈ bourgainDifferenceLevel W j,
        d*(W.card : ℝ) ≤ (bourgainDifferenceCount W ℓ : ℝ) ∧
        (bourgainDifferenceCount W ℓ : ℝ) < 4*d*(W.card : ℝ)) ∧
      d*((bourgainDifferenceLevel W j).card : ℝ) ≤ 2*(W.card : ℝ) :=
  @TaoTrudgianYang2025.bourgain_retained_relative_level P W hsub j hj τ δ hN hδ hT

example
    {N T B C τ α ε : ℝ} {W : Finset ℝ} {j q : ℕ}
    (hband : BourgainComponentBand N T B C τ α ε W j q)
    (hN : 0 < N) {d : ℝ} (hrel : (2 : ℝ)^j ≤ 2*d*(W.card : ℝ)) :
    let H := N^(ε/8)
    let U := T+H+1
    let a := N^(-bourgainSharedFloorExponent α τ ε)
    let J := bourgainZetaBandCount B U a
    let r := bourgainZetaBandCorrelation (bourgainDifferenceLevel W j) H U (a*(2 : ℝ)^q)
    N^(-2*α)*N^τ <
      1024*(Nat.log 2 W.card+1 : ℕ)^2*(J : ℝ)^2*C*U^(1+ε)*d*r^2 :=
  @TaoTrudgianYang2025.BourgainComponentBand.relative_correlation_lower N T B C τ α ε W j q hband hN d hrel

example {σ τ : ℝ}
    (hσ : 3/4 < σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B C δ : ℝ, 0 < B ∧ 2 ≤ C ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ (P : LargeValuePattern) (L : ℝ) (hL : 0 < L),
        C ≤ P.N → P.N ≤ L → L ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        ∃ W : ℕ → Finset ℝ,
          (∀ i : ℕ, W i ⊆ (P.localized L hL i).reflectedOrdinates ∧
            IsSeparated 2 (W i) ∧ InBaseInterval L (W i) ∧
            ((P.localized L hL i).ordinates.card : ℝ) ≤ C*P.N^ε*((W i).card : ℝ)) ∧
          ∀ α : ℝ,
            let I := Finset.range (Nat.floor (P.T/L)+1)
            let a := P.N^(-bourgainSharedFloorExponent α τ ε)
            let J := bourgainZetaBandCount B (L+P.N^(ε/8)+1) a
            let F := C*(P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε)+
              P.N^(-2*α+τ+12-16*σ+ε))
            ∃ q ∈ Finset.range J, ∃ p ∈ Finset.range (bourgainRelativeLevelCount P.N τ),
              ∃ A : Finset ℕ, A ⊆ I ∧
              ∃ j : ℕ → ℕ,
                (∀ i ∈ A, F < ((P.localized L hL i).ordinates.card : ℝ) ∧
                  BourgainComponentBand P.N L B C τ α ε (W i) (j i) q ∧
                  (let d := bourgainRelativeLevel P.N τ p
                  0 < d ∧ d ≤ 1 ∧
                  d*((W i).card : ℝ) ≤ (2 : ℝ)^(j i) ∧
                  (2 : ℝ)^(j i) < 2*d*((W i).card : ℝ) ∧
                  (∀ ℓ ∈ bourgainDifferenceLevel (W i) (j i),
                    d*((W i).card : ℝ) ≤ (bourgainDifferenceCount (W i) ℓ : ℝ) ∧
                    (bourgainDifferenceCount (W i) ℓ : ℝ) < 4*d*((W i).card : ℝ)) ∧
                  d*((bourgainDifferenceLevel (W i) (j i)).card : ℝ) ≤ 2*((W i).card : ℝ)) ∧
                  let d := bourgainRelativeLevel P.N τ p
                  let r := bourgainZetaBandCorrelation
                    (bourgainDifferenceLevel (W i) (j i)) (P.N^(ε/8))
                    (L+P.N^(ε/8)+1) (a*(2 : ℝ)^q)
                  P.N^(-2*α)*P.N^τ <
                    1024*(Nat.log 2 (W i).card+1 : ℕ)^2*(J : ℝ)^2*
                      C*(L+P.N^(ε/8)+1)^(1+ε)*d*r^2) ∧
                let S := A.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))
                S ⊆ P.ordinates ∧ S.card = ∑ i ∈ A, (W i).card ∧
                IsSeparated 1 S ∧
                (∀ t ∈ S, P.V ≤ ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n t‖) ∧
                (∀ i ∈ A, ∀ ℓ : ℤ,
                  bourgainDifferenceCount ((P.localized L hL i).retainedOriginal (W i)) ℓ =
                    bourgainDifferenceCount (W i) ℓ) ∧
                (P.ordinates.card : ℝ) ≤
                  (I.card : ℝ)*F+C*P.N^ε*(J : ℝ)*(bourgainRelativeLevelCount P.N τ : ℝ)*(S.card : ℝ) :=
  @TaoTrudgianYang2025.bourgain_subdivided_common_levels σ τ hσ ε hε

-- Empty and weighted fibers, and the strict small/large threshold.
example (J : ℕ) (hJ : 0 < J) :
    ∃ q ∈ Finset.range J,
      (0 : ℝ) ≤ (J : ℝ)*∑ i ∈ (∅ : Finset ℕ).filter (fun i => i = q), (i : ℝ) := by
  simpa using bourgain_exists_heavy_component_fiber (∅ : Finset ℕ)
    (fun i => (i : ℝ)) id hJ (by simp)

example :
    (∑ i ∈ ({0,1,2} : Finset ℕ).filter (fun i => i % 2 = 0),
      (if i = 2 then 100 else 1 : ℝ)) = 101 := by
  norm_num [Finset.filter_insert, Finset.filter_singleton]

example :
    ((Finset.range 3).filter (fun i => (1 : ℝ) < (i : ℝ) ∧ i % 2 = 0)) = {2} := by
  norm_num [Finset.range_add_one, Finset.filter_insert, Finset.filter_singleton]

example : ¬ ((1 : ℝ) < 1) := by norm_num

-- Shared relative grids include exact powers and have a strict terminal band.
example : bourgainRelativeLevel 2 0 0 = (1/4 : ℝ) := by
  norm_num [bourgainRelativeLevel]

example : bourgainRelativeLevel 2 0 2 = 1 := by
  norm_num [bourgainRelativeLevel]

example : bourgainRelativeLevelCount 2 0 = 3 := by
  norm_num [bourgainRelativeLevelCount, bourgainZetaBandCount]

example (N τ : ℝ) (p : ℕ) :
    bourgainRelativeLevel N (-τ) p = bourgainRelativeLevel N τ p := by
  simp [bourgainRelativeLevel]

example (N τ : ℝ) :
    bourgainRelativeLevelCount N (-τ) = bourgainRelativeLevelCount N τ := by
  simp [bourgainRelativeLevelCount]

example : (2 : ℝ)^0/2 ≠ (2 : ℝ)^0/4 := by norm_num

-- The named component proposition contains genuine mathematical data.
example {N T B C τ α ε : ℝ} {W : Finset ℝ} {j q : ℕ}
    (h : BourgainComponentBand N T B C τ α ε W j q) :
    (bourgainDifferenceLevel W j).Nonempty := h.2.1

example {N T B C τ α ε : ℝ} {W : Finset ℝ} {j q : ℕ}
    (h : BourgainComponentBand N T B C τ α ε W j q) :
    0 < W.card := by
  exact (Nat.pow_pos (by norm_num : 0 < (2 : ℕ))).trans_le h.2.2.1

example {N T B C τ α ε : ℝ} {W : Finset ℝ} {j q : ℕ}
    (h : BourgainComponentBand N T B C τ α ε W j q) :
    q ∈ Finset.range (bourgainZetaBandCount B (T+N^(ε/8)+1)
      (N^(-bourgainSharedFloorExponent α τ ε))) := h.2.2.2.2.1

example {N T B C τ α ε : ℝ} {W : Finset ℝ} {j q : ℕ}
    (h : BourgainComponentBand N T B C τ α ε W j q) :
    0 < volume.real (bourgainZetaBand (T+N^(ε/8)+1)
      (N^(-bourgainSharedFloorExponent α τ ε)*(2 : ℝ)^q)) := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, hmeasure, _⟩
  exact hmeasure

end BourgainCommonComponentRegression

namespace BourgainCommonCorrelationRegression

open MeasureTheory
open scoped Classical

-- Exact public types preserve physical windows and all quantifier dependencies.

example {B N U A u : ℝ}
    (hB : 0 < B) (hN : 1 ≤ N) (hU : 0 ≤ U) (hA : 0 ≤ A) (hu : 0 ≤ u)
    (hcap : U ≤ 3*N^u) :
    (bourgainZetaBandCount B U (N^(-A)) : ℝ) ≤ (4*B+2)*N^(u+A) :=
  @TaoTrudgianYang2025.bourgainZetaBandCount_crude_power_bound B N U A u hB hN hU hA hu hcap

example (α τ : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ bourgainCorrelationGrowthExponent α τ ε :=
  @TaoTrudgianYang2025.bourgainCorrelationGrowthExponent_nonneg α τ ε hε

example (α τ : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    0 < bourgainCorrelationExponent α τ ε :=
  @TaoTrudgianYang2025.bourgainCorrelationExponent_pos α τ ε hε

example (B : ℝ) {C : ℝ} (hC : 0 ≤ C) (ε : ℝ) :
    1 ≤ bourgainCorrelationConstant B C ε :=
  @TaoTrudgianYang2025.bourgainCorrelationConstant_one_le B C hC ε

example {N B C α τ ε : ℝ}
    (hN : 0 < N) (hC : 0 ≤ C) :
    0 < bourgainCorrelationFloor N B C α τ ε :=
  @TaoTrudgianYang2025.bourgainCorrelationFloor_pos N B C α τ ε hN hC

example {α τ ε : ℝ} (hε : 0 ≤ ε) :
    bourgainCorrelationGrowthExponent α τ ε-2*bourgainCorrelationExponent α τ ε ≤
      -2*α+τ :=
  @TaoTrudgianYang2025.bourgain_correlation_floor_exponent α τ ε hε

example {N B C α τ ε : ℝ}
    (hN : 1 ≤ N) (hC : 0 ≤ C) (hε : 0 ≤ ε) :
    (bourgainCorrelationConstant B C ε-1)*N^(bourgainCorrelationGrowthExponent α τ ε)*
      (bourgainCorrelationFloor N B C α τ ε)^2 ≤ N^(-2*α)*N^τ :=
  @TaoTrudgianYang2025.bourgain_correlation_floor_balance N B C α τ ε hN hC hε

example (P : LargeValuePattern)
    {W : Finset ℝ} (hsub : W ⊆ P.reflectedOrdinates) (hW : 0 < W.card)
    {B C α τ ε δ : ℝ} (hB : 0 < B) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hδ : δ ≤ 1) (hT : P.T ≤ P.N^(τ+δ)) :
    let U := P.T+P.N^(ε/8)+1
    let J := bourgainZetaBandCount B U (P.N^(-bourgainSharedFloorExponent α τ ε))
    1024*(Nat.log 2 W.card+1 : ℕ)^2*(J : ℝ)^2*C*U^(1+ε) ≤
      (bourgainCorrelationConstant B C ε-1)*P.N^(bourgainCorrelationGrowthExponent α τ ε) :=
  @TaoTrudgianYang2025.bourgain_correlation_coefficient_bound P W hsub hW B C α τ ε δ hB hC hε hδ hT

example (P : LargeValuePattern)
    {W : Finset ℝ} (hsub : W ⊆ P.reflectedOrdinates)
    {B C α τ ε δ : ℝ} {j q : ℕ}
    (hband : BourgainComponentBand P.N P.T B C τ α ε W j q)
    (hB : 0 < B) (hC : 0 < C) (hε : 0 ≤ ε)
    (hδ : δ ≤ 1) (hT : P.T ≤ P.N^(τ+δ)) :
    let H := P.N^(ε/8)
    let U := P.T+H+1
    let a := P.N^(-bourgainSharedFloorExponent α τ ε)
    let r := bourgainZetaBandCorrelation (bourgainDifferenceLevel W j) H U (a*(2 : ℝ)^q)
    0 < bourgainCorrelationFloor P.N B C α τ ε ∧
      bourgainCorrelationFloor P.N B C α τ ε < r ∧ r ≤ 4*H :=
  @TaoTrudgianYang2025.bourgain_component_correlation_window P W hsub B C α τ ε δ j q hband hB hC hε hδ hT

example (N B C α τ ε : ℝ) :
    0 < bourgainCorrelationLevelCount N B C α τ ε :=
  @TaoTrudgianYang2025.bourgainCorrelationLevelCount_pos N B C α τ ε

example {N B C α τ ε : ℝ}
    (hN : 1 ≤ N) (hC : 0 ≤ C) (hε : 0 ≤ ε) :
    (bourgainCorrelationLevelCount N B C α τ ε : ℝ) ≤
      2+(Real.log (16*bourgainCorrelationConstant B C ε+1)+
        (ε/8+bourgainCorrelationExponent α τ ε)*Real.log N)/Real.log 2 :=
  @TaoTrudgianYang2025.bourgainCorrelationLevelCount_log_bound N B C α τ ε hN hC hε

example {B C α τ ε η : ℝ}
    (hC : 0 ≤ C) (hε : 0 ≤ ε) (hη : 0 < η) :
    ∃ D N₀ : ℝ, 1 ≤ D ∧ 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      (bourgainCorrelationLevelCount N B C α τ ε : ℝ) ≤ D*N^η :=
  @TaoTrudgianYang2025.bourgainCorrelationLevelCount_uniform_power B C α τ ε η hC hε hη

example {N B C α τ ε : ℝ}
    (hN : 0 < N) (hC : 0 ≤ C) :
    4*N^(ε/8) < bourgainCorrelationFloor N B C α τ ε*
      (2 : ℝ)^(bourgainCorrelationLevelCount N B C α τ ε) :=
  @TaoTrudgianYang2025.bourgainCorrelationLevel_terminal N B C α τ ε hN hC

example (P : LargeValuePattern)
    {W : Finset ℝ} (hsub : W ⊆ P.reflectedOrdinates)
    {B C α τ ε δ : ℝ} {j q : ℕ}
    (hband : BourgainComponentBand P.N P.T B C τ α ε W j q)
    (hB : 0 < B) (hC : 0 < C) (hε : 0 ≤ ε)
    (hδ : δ ≤ 1) (hT : P.T ≤ P.N^(τ+δ)) :
    let H := P.N^(ε/8)
    let U := P.T+H+1
    let a := P.N^(-bourgainSharedFloorExponent α τ ε)
    let D := bourgainDifferenceLevel W j
    let V := a*(2 : ℝ)^q
    let r := bourgainZetaBandCorrelation D H U V
    let μ := volume.real (bourgainZetaBand U V)
    ∃ k ∈ Finset.range (bourgainCorrelationLevelCount P.N B C α τ ε),
      let s := bourgainCorrelationLevel P.N B C α τ ε k
      0 < s ∧ s ≤ r ∧ r < 2*s ∧ s ≤ 4*H ∧
      s*Real.sqrt μ*Real.sqrt (D.card : ℝ) ≤ bourgainZetaBandMass D H U V ∧
      bourgainZetaBandMass D H U V < 2*s*Real.sqrt μ*Real.sqrt (D.card : ℝ) :=
  @TaoTrudgianYang2025.bourgain_component_correlation_grid P W hsub B C α τ ε δ j q hband hB hC hε hδ hT

example {σ τ : ℝ}
    (hσ : 3/4 < σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B C δ : ℝ, 0 < B ∧ 2 ≤ C ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ (P : LargeValuePattern) (L : ℝ) (hL : 0 < L),
        C ≤ P.N → P.N ≤ L → L ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        ∃ W : ℕ → Finset ℝ,
          (∀ i : ℕ, W i ⊆ (P.localized L hL i).reflectedOrdinates ∧
            IsSeparated 2 (W i) ∧ InBaseInterval L (W i) ∧
            ((P.localized L hL i).ordinates.card : ℝ) ≤ C*P.N^ε*((W i).card : ℝ)) ∧
          ∀ α : ℝ,
            let I := Finset.range (Nat.floor (P.T/L)+1)
            let a := P.N^(-bourgainSharedFloorExponent α τ ε)
            let J := bourgainZetaBandCount B (L+P.N^(ε/8)+1) a
            let F := C*(P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε)+
              P.N^(-2*α+τ+12-16*σ+ε))
            ∃ q ∈ Finset.range J, ∃ p ∈ Finset.range (bourgainRelativeLevelCount P.N τ),
              ∃ k ∈ Finset.range (bourgainCorrelationLevelCount P.N B C α τ ε),
              ∃ A : Finset ℕ, A ⊆ I ∧
              ∃ j : ℕ → ℕ,
                (∀ i ∈ A, (F < ((P.localized L hL i).ordinates.card : ℝ) ∧
                  BourgainComponentBand P.N L B C τ α ε (W i) (j i) q ∧
                  (let d := bourgainRelativeLevel P.N τ p
                  0 < d ∧ d ≤ 1 ∧
                  d*((W i).card : ℝ) ≤ (2 : ℝ)^(j i) ∧
                  (2 : ℝ)^(j i) < 2*d*((W i).card : ℝ) ∧
                  (∀ ℓ ∈ bourgainDifferenceLevel (W i) (j i),
                    d*((W i).card : ℝ) ≤ (bourgainDifferenceCount (W i) ℓ : ℝ) ∧
                    (bourgainDifferenceCount (W i) ℓ : ℝ) < 4*d*((W i).card : ℝ)) ∧
                  d*((bourgainDifferenceLevel (W i) (j i)).card : ℝ) ≤ 2*((W i).card : ℝ)) ∧
                  let d := bourgainRelativeLevel P.N τ p
                  let r := bourgainZetaBandCorrelation
                    (bourgainDifferenceLevel (W i) (j i)) (P.N^(ε/8))
                    (L+P.N^(ε/8)+1) (a*(2 : ℝ)^q)
                  P.N^(-2*α)*P.N^τ <
                    1024*(Nat.log 2 (W i).card+1 : ℕ)^2*(J : ℝ)^2*
                      C*(L+P.N^(ε/8)+1)^(1+ε)*d*r^2) ∧
                  (let H := P.N^(ε/8)
                  let U := L+H+1
                  let D := bourgainDifferenceLevel (W i) (j i)
                  let V := a*(2 : ℝ)^q
                  let r := bourgainZetaBandCorrelation D H U V
                  let μ := volume.real (bourgainZetaBand U V)
                  let s := bourgainCorrelationLevel P.N B C α τ ε k
                  0 < s ∧ s ≤ r ∧ r < 2*s ∧ s ≤ 4*H ∧
                  s*Real.sqrt μ*Real.sqrt (D.card : ℝ) ≤ bourgainZetaBandMass D H U V ∧
                  bourgainZetaBandMass D H U V < 2*s*Real.sqrt μ*Real.sqrt (D.card : ℝ)) ∧
                  let d := bourgainRelativeLevel P.N τ p
                  let s := bourgainCorrelationLevel P.N B C α τ ε k
                  P.N^(-2*α)*P.N^τ <
                    4096*(Nat.log 2 (W i).card+1 : ℕ)^2*(J : ℝ)^2*
                      C*(L+P.N^(ε/8)+1)^(1+ε)*d*s^2) ∧
                let S := A.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))
                S ⊆ P.ordinates ∧ S.card = ∑ i ∈ A, (W i).card ∧
                IsSeparated 1 S ∧
                (∀ t ∈ S, P.V ≤ ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n t‖) ∧
                (∀ i ∈ A, ∀ ℓ : ℤ,
                  bourgainDifferenceCount ((P.localized L hL i).retainedOriginal (W i)) ℓ =
                    bourgainDifferenceCount (W i) ℓ) ∧
                (P.ordinates.card : ℝ) ≤
                  (I.card : ℝ)*F+C*P.N^ε*(J : ℝ)*(bourgainRelativeLevelCount P.N τ : ℝ)*
                    (bourgainCorrelationLevelCount P.N B C α τ ε : ℝ)*(S.card : ℝ) :=
  @TaoTrudgianYang2025.bourgain_subdivided_common_correlation σ τ hσ ε hε

example {τ η : ℝ} (hη : 0 < η) :
    ∃ D N₀ : ℝ, 1 ≤ D ∧ 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      (bourgainRelativeLevelCount N τ : ℝ) ≤ D*N^η :=
  @TaoTrudgianYang2025.bourgainRelativeLevelCount_uniform_power τ η hη

example {B C α τ ε η : ℝ}
    (hB : 0 < B) (hC : 0 ≤ C) (hε : 0 ≤ ε) (hη : 0 < η) :
    ∃ D N₀ : ℝ, 1 ≤ D ∧ 2 ≤ N₀ ∧
      ∀ (P : LargeValuePattern) (δ : ℝ), δ ≤ 1 → N₀ ≤ P.N → P.T ≤ P.N^(τ+δ) →
        let U := P.T+P.N^(ε/8)+1
        let J := bourgainZetaBandCount B U (P.N^(-bourgainSharedFloorExponent α τ ε))
        let Q := bourgainRelativeLevelCount P.N τ
        let K := bourgainCorrelationLevelCount P.N B C α τ ε
        (J : ℝ)*(Q : ℝ)*(K : ℝ) ≤ D*P.N^η :=
  @TaoTrudgianYang2025.bourgain_selection_counts_uniform_power B C α τ ε η hB hC hε hη

-- Concrete scale arithmetic, including sign and exact grid endpoints.
example : bourgainCorrelationGrowthExponent 0 0 0 = 45 := by
  norm_num [bourgainCorrelationGrowthExponent, bourgainSharedFloorExponent]

example : bourgainCorrelationExponent 0 0 0 = 46 := by
  norm_num [bourgainCorrelationExponent, bourgainCorrelationGrowthExponent,
    bourgainSharedFloorExponent]

example : bourgainCorrelationConstant 1 1 0 = 442369 := by
  norm_num [bourgainCorrelationConstant]

example (B ε : ℝ) : bourgainCorrelationConstant B 0 ε = 1 := by
  simp [bourgainCorrelationConstant]

example (α τ ε : ℝ) :
    bourgainCorrelationGrowthExponent (-α) (-τ) ε =
      bourgainCorrelationGrowthExponent α τ ε := by
  simp [bourgainCorrelationGrowthExponent, bourgainSharedFloorExponent]

example (α τ ε : ℝ) :
    bourgainCorrelationExponent (-α) (-τ) ε =
      bourgainCorrelationExponent α τ ε := by
  simp [bourgainCorrelationExponent, bourgainCorrelationGrowthExponent,
    bourgainSharedFloorExponent]

example : bourgainCorrelationFloor 1 1 1 0 0 0 = (1/442369 : ℝ) := by
  norm_num [bourgainCorrelationFloor, bourgainCorrelationConstant]

example : bourgainCorrelationLevelCount 1 1 0 0 0 0 = 3 := by
  norm_num [bourgainCorrelationLevelCount, bourgainCorrelationConstant,
    bourgainZetaBandCount]

example : bourgainCorrelationLevel 1 1 0 0 0 0 2 = 4 := by
  norm_num [bourgainCorrelationLevel, bourgainCorrelationFloor, bourgainCorrelationConstant]

example (N B C α τ ε : ℝ) (k : ℕ) :
    bourgainCorrelationLevel N B C α τ ε (k+1) =
      2*bourgainCorrelationLevel N B C α τ ε k := by
  rw [bourgainCorrelationLevel, bourgainCorrelationLevel, pow_succ]
  ring

-- Localized components really have the same floor and count.
example (P : LargeValuePattern) (L : ℝ) (hL : 0 < L) (i : ℕ) (B C α τ ε : ℝ) :
    bourgainCorrelationFloor (P.localized L hL i).N B C α τ ε =
      bourgainCorrelationFloor P.N B C α τ ε := rfl

example (P : LargeValuePattern) (L : ℝ) (hL : 0 < L) (i : ℕ) (B C α τ ε : ℝ) :
    bourgainCorrelationLevelCount (P.localized L hL i).N B C α τ ε =
      bourgainCorrelationLevelCount P.N B C α τ ε := rfl

example (P : LargeValuePattern) (L : ℝ) (hL : 0 < L) (i : ℕ) :
    (P.localized L hL i).coeff = P.coeff := rfl

-- Negative exponent parameters do not break the numerical floor margin.
example :
    bourgainCorrelationGrowthExponent (-100) (-3) 0 -
      2*bourgainCorrelationExponent (-100) (-3) 0 ≤ -2*(-100 : ℝ)+(-3) :=
  bourgain_correlation_floor_exponent (by norm_num)

end BourgainCommonCorrelationRegression

namespace BourgainIntegerSliceMixedRegression

open MeasureTheory RiemannZeta.GuthMaynard Set
open scoped Interval Classical

-- BourgainIntegerSlice: exact public interface, including its quantifier order.
example {H T V u : ℝ} (hu : u ∈ Icc (-H) H)
    {ℓ : ℤ} (hℓ : (ℓ : ℝ)+u ∈ bourgainZetaBand T V) :
    ℓ ∈ bourgainIntegerCover H T := by
  exact @TaoTrudgianYang2025.bourgain_mem_integerCover H T V u hu ℓ hℓ

-- BourgainIntegerSlice: exact public interface, including its quantifier order.
example {H T V u : ℝ} (hu : u ∈ Icc (-H) H) (ℓ : ℤ) :
    ℓ ∈ bourgainIntegerSlice H T V u ↔ (ℓ : ℝ)+u ∈ bourgainZetaBand T V := by
  exact @TaoTrudgianYang2025.mem_bourgainIntegerSlice H T V u hu ℓ

-- BourgainIntegerSlice: exact public interface, including its quantifier order.
example (H T V u : ℝ) :
    ((bourgainIntegerSlice H T V u).card : ℝ) =
      bourgainBandOccupancy (bourgainIntegerCover H T) (bourgainZetaBand T V) u := by
  exact @TaoTrudgianYang2025.bourgainIntegerSlice_card H T V u

-- BourgainIntegerSlice: exact public interface, including its quantifier order.
example (D : Finset ℤ) {H T V u : ℝ}
    (hu : u ∈ Icc (-H) H) :
    ((D ∩ bourgainIntegerSlice H T V u).card : ℝ) =
      bourgainBandOccupancy D (bourgainZetaBand T V) u := by
  exact @TaoTrudgianYang2025.bourgainIntegerSlice_inter_card D H T V u hu

-- BourgainIntegerSlice: exact public interface, including its quantifier order.
example (D : Finset ℤ)
    {S : Set ℝ} (hS : MeasurableSet S) :
    Measurable (bourgainBandOccupancy D S) := by
  exact @TaoTrudgianYang2025.bourgainBandOccupancy_measurable D S hS

-- BourgainIntegerSlice: exact public interface, including its quantifier order.
example (D : Finset ℤ)
    {S : Set ℝ} (hS : MeasurableSet S) (a b : ℝ) :
    IntervalIntegrable (fun u => Real.sqrt (bourgainBandOccupancy D S u)) volume a b := by
  exact @TaoTrudgianYang2025.bourgainBandOccupancy_sqrt_intervalIntegrable D S hS a b

-- BourgainIntegerSlice: exact public interface, including its quantifier order.
example (D : Finset ℤ)
    {S : Set ℝ} (hS : MeasurableSet S) {H : ℝ} (hH : 0 ≤ H) :
    (∫ u in -H..H, Real.sqrt (bourgainBandOccupancy D S u))^2 ≤
      2*H*(∫ u in -H..H, bourgainBandOccupancy D S u) := by
  exact @TaoTrudgianYang2025.bourgainBandOccupancy_sqrt_integral_sq_le D S hS H hH

-- BourgainIntegerSlice: exact public interface, including its quantifier order.
example {H : ℝ} (hH : 0 ≤ H) (T V : ℝ) :
    (∫ u in -H..H, ((bourgainIntegerSlice H T V u).card : ℝ)) ≤
      (2*Nat.ceil H+1 : ℕ)*volume.real (bourgainZetaBand T V) := by
  exact @TaoTrudgianYang2025.bourgainIntegerSlice_integral_card_le H hH T V

-- BourgainIntegerSlice: exact public interface, including its quantifier order.
example {H : ℝ} (hH : 0 ≤ H) (T V : ℝ) :
    (∫ u in -H..H, Real.sqrt ((bourgainIntegerSlice H T V u).card : ℝ)) ≤
      Real.sqrt (2*H*(2*Nat.ceil H+1 : ℕ)*volume.real (bourgainZetaBand T V)) := by
  exact @TaoTrudgianYang2025.bourgainIntegerSlice_integral_sqrt_card_le H hH T V

-- BourgainSliceSelection: exact public interface, including its quantifier order.
example {ι : Type*}
    (A : Finset ι) (w : ι → ℝ) (D : ι → Finset ℤ)
    {H T V a b : ℝ} (hH : 0 < H) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hmass : a*(2*Nat.ceil H+1 : ℕ)*volume.real (bourgainZetaBand T V)+
      b*Real.sqrt (2*H*(2*Nat.ceil H+1 : ℕ)*volume.real (bourgainZetaBand T V)) <
      ∑ i ∈ A, w i*bourgainZetaBandMass (D i) H T V) :
    ∃ u ∈ Ioc (-H) H,
      (bourgainIntegerSlice H T V u).Nonempty ∧
      a*((bourgainIntegerSlice H T V u).card : ℝ)+
        b*Real.sqrt ((bourgainIntegerSlice H T V u).card : ℝ) <
      ∑ i ∈ A, w i*((D i ∩ bourgainIntegerSlice H T V u).card : ℝ) := by
  exact @TaoTrudgianYang2025.bourgain_full_slice_common_shift ι A w D H T V a b hH ha hb hmass

-- BourgainComponentMass: exact public interface, including its quantifier order.
example {N : ℝ} (hN : 1 ≤ N) (τ : ℝ) :
    0 < bourgainDifferenceLogLoss N τ := by
  exact @TaoTrudgianYang2025.bourgainDifferenceLogLoss_pos N hN τ

-- BourgainComponentMass: exact public interface, including its quantifier order.
example {N τ : ℝ} {R : ℕ}
    (hN : 1 ≤ N) (hR : 0 < R) (hsize : (R : ℝ) ≤ 2*N^(|τ|+1)) :
    (Nat.log 2 R+1 : ℕ) ≤ bourgainDifferenceLogLoss N τ := by
  exact @TaoTrudgianYang2025.bourgain_difference_level_count_log_bound N τ R hN hR hsize

-- BourgainComponentMass: exact public interface, including its quantifier order.
example (P : LargeValuePattern)
    {W : Finset ℝ} (hsub : W ⊆ P.reflectedOrdinates) (hW : 0 < W.card)
    {τ δ : ℝ} (hδ : δ ≤ 1) (hT : P.T ≤ P.N^(τ+δ)) :
    (Nat.log 2 W.card+1 : ℕ) ≤ bourgainDifferenceLogLoss P.N τ := by
  exact @TaoTrudgianYang2025.bourgain_retained_difference_level_count P W hsub hW τ δ hδ hT

-- BourgainComponentMass: exact public interface, including its quantifier order.
example
    {N T B C τ α ε : ℝ} {W : Finset ℝ} {j q : ℕ}
    (hband : BourgainComponentBand N T B C τ α ε W j q) (hN : 0 < N)
    {s d Z : ℝ} (hs : 0 < s) (hd : 0 < d)
    (hZ : (Nat.log 2 W.card+1 : ℕ) ≤ Z)
    (hrel : (2 : ℝ)^j ≤ 2*d*(W.card : ℝ))
    (hcorr : s ≤ bourgainZetaBandCorrelation (bourgainDifferenceLevel W j)
      (N^(ε/8)) (T+N^(ε/8)+1)
      (N^(-bourgainSharedFloorExponent α τ ε)*(2 : ℝ)^q)) :
    let H := N^(ε/8)
    let U := T+H+1
    let J := bourgainZetaBandCount B U (N^(-bourgainSharedFloorExponent α τ ε))
    let V := N^(-bourgainSharedFloorExponent α τ ε)*(2 : ℝ)^q
    let μ := volume.real (bourgainZetaBand U V)
    let M := bourgainZetaBandMass (bourgainDifferenceLevel W j) H U V
    let R := (W.card : ℝ)
    s^2*μ*R/(2*H) ≤ R*M ∧
      (N^(-α)*N^(τ/2)/(32*Z*(J : ℝ)*d*Real.sqrt (C*U^(1+ε))))*
        Real.sqrt μ*R^(3/2 : ℝ) < R*M := by
  exact @TaoTrudgianYang2025.BourgainComponentBand.weighted_mass_lower N T B C τ α ε W j q hband hN s d Z hs hd hZ hrel hcorr

-- BourgainFamilySlice: exact public interface, including its quantifier order.
example (P : LargeValuePattern)
    {L : ℝ} (hL : 0 < L) (A : Finset ℕ) (hA : A.Nonempty)
    (W : ℕ → Finset ℝ) (j : ℕ → ℕ) (q : ℕ)
    {B C τ α ε δ s d : ℝ}
    (hsub : ∀ i ∈ A, W i ⊆ (P.localized L hL i).reflectedOrdinates)
    (hδ : δ ≤ 1) (hT : L ≤ P.N^(τ+δ))
    (hband : ∀ i ∈ A, BourgainComponentBand P.N L B C τ α ε (W i) (j i) q)
    (hs : 0 < s) (hd : 0 < d)
    (hrel : ∀ i ∈ A, (2 : ℝ)^(j i) ≤ 2*d*((W i).card : ℝ))
    (hcorr : ∀ i ∈ A, s ≤ bourgainZetaBandCorrelation
      (bourgainDifferenceLevel (W i) (j i)) (P.N^(ε/8)) (L+P.N^(ε/8)+1)
      (P.N^(-bourgainSharedFloorExponent α τ ε)*(2 : ℝ)^q)) :
    let H := P.N^(ε/8)
    let U := L+H+1
    let V := P.N^(-bourgainSharedFloorExponent α τ ε)*(2 : ℝ)^q
    ∃ u ∈ Ioc (-H) H,
      (bourgainIntegerSlice H U V u).Nonempty ∧
      bourgainSliceCardCoefficient P.N ε s*
          ((bourgainIntegerSlice H U V u).card : ℝ)*(∑ i ∈ A, ((W i).card : ℝ))+
        bourgainSliceSqrtCoefficient P.N L B C τ α ε d*
          Real.sqrt ((bourgainIntegerSlice H U V u).card : ℝ)*
            (∑ i ∈ A, ((W i).card : ℝ)^(3/2 : ℝ)) <
      ∑ i ∈ A, ((W i).card : ℝ)*
        ((bourgainDifferenceLevel (W i) (j i) ∩ bourgainIntegerSlice H U V u).card : ℝ) := by
  exact @TaoTrudgianYang2025.bourgain_component_family_slice P L hL A hA W j q B C τ α ε δ s d hsub hδ hT hband hs hd hrel hcorr

-- BourgainCommonSlice: exact public interface, including its quantifier order.
example {σ τ : ℝ}
    (hσ : 3/4 < σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B C δ : ℝ, 0 < B ∧ 2 ≤ C ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ (P : LargeValuePattern) (L : ℝ) (hL : 0 < L),
        C ≤ P.N → P.N ≤ L → L ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        ∃ W : ℕ → Finset ℝ,
          (∀ i : ℕ, W i ⊆ (P.localized L hL i).reflectedOrdinates ∧
            IsSeparated 2 (W i) ∧ InBaseInterval L (W i) ∧
            ((P.localized L hL i).ordinates.card : ℝ) ≤ C*P.N^ε*((W i).card : ℝ)) ∧
          ∀ α : ℝ,
            let I := Finset.range (Nat.floor (P.T/L)+1)
            let a := P.N^(-bourgainSharedFloorExponent α τ ε)
            let J := bourgainZetaBandCount B (L+P.N^(ε/8)+1) a
            let F := C*(P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε)+
              P.N^(-2*α+τ+12-16*σ+ε))
            ∃ q ∈ Finset.range J, ∃ p ∈ Finset.range (bourgainRelativeLevelCount P.N τ),
              ∃ k ∈ Finset.range (bourgainCorrelationLevelCount P.N B C α τ ε),
              ∃ A : Finset ℕ, A ⊆ I ∧
              ∃ j : ℕ → ℕ,
                (∀ i ∈ A, (F < ((P.localized L hL i).ordinates.card : ℝ) ∧
                  BourgainComponentBand P.N L B C τ α ε (W i) (j i) q ∧
                  (let d := bourgainRelativeLevel P.N τ p
                  0 < d ∧ d ≤ 1 ∧
                  d*((W i).card : ℝ) ≤ (2 : ℝ)^(j i) ∧
                  (2 : ℝ)^(j i) < 2*d*((W i).card : ℝ) ∧
                  (∀ ℓ ∈ bourgainDifferenceLevel (W i) (j i),
                    d*((W i).card : ℝ) ≤ (bourgainDifferenceCount (W i) ℓ : ℝ) ∧
                    (bourgainDifferenceCount (W i) ℓ : ℝ) < 4*d*((W i).card : ℝ)) ∧
                  d*((bourgainDifferenceLevel (W i) (j i)).card : ℝ) ≤ 2*((W i).card : ℝ)) ∧
                  let d := bourgainRelativeLevel P.N τ p
                  let r := bourgainZetaBandCorrelation
                    (bourgainDifferenceLevel (W i) (j i)) (P.N^(ε/8))
                    (L+P.N^(ε/8)+1) (a*(2 : ℝ)^q)
                  P.N^(-2*α)*P.N^τ <
                    1024*(Nat.log 2 (W i).card+1 : ℕ)^2*(J : ℝ)^2*
                      C*(L+P.N^(ε/8)+1)^(1+ε)*d*r^2) ∧
                  (let H := P.N^(ε/8)
                  let U := L+H+1
                  let D := bourgainDifferenceLevel (W i) (j i)
                  let V := a*(2 : ℝ)^q
                  let r := bourgainZetaBandCorrelation D H U V
                  let μ := volume.real (bourgainZetaBand U V)
                  let s := bourgainCorrelationLevel P.N B C α τ ε k
                  0 < s ∧ s ≤ r ∧ r < 2*s ∧ s ≤ 4*H ∧
                  s*Real.sqrt μ*Real.sqrt (D.card : ℝ) ≤ bourgainZetaBandMass D H U V ∧
                  bourgainZetaBandMass D H U V < 2*s*Real.sqrt μ*Real.sqrt (D.card : ℝ)) ∧
                  let d := bourgainRelativeLevel P.N τ p
                  let s := bourgainCorrelationLevel P.N B C α τ ε k
                  P.N^(-2*α)*P.N^τ <
                    4096*(Nat.log 2 (W i).card+1 : ℕ)^2*(J : ℝ)^2*
                      C*(L+P.N^(ε/8)+1)^(1+ε)*d*s^2) ∧
                let S := A.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))
                S ⊆ P.ordinates ∧ S.card = ∑ i ∈ A, (W i).card ∧
                IsSeparated 1 S ∧
                (∀ t ∈ S, P.V ≤ ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n t‖) ∧
                (∀ i ∈ A, ∀ ℓ : ℤ,
                  bourgainDifferenceCount ((P.localized L hL i).retainedOriginal (W i)) ℓ =
                    bourgainDifferenceCount (W i) ℓ) ∧
                (P.ordinates.card : ℝ) ≤
                  (I.card : ℝ)*F+C*P.N^ε*(J : ℝ)*(bourgainRelativeLevelCount P.N τ : ℝ)*
                    (bourgainCorrelationLevelCount P.N B C α τ ε : ℝ)*(S.card : ℝ) ∧
                ((P.ordinates.card : ℝ) ≤ (I.card : ℝ)*F ∨
                  let H := P.N^(ε/8)
                  let U := L+H+1
                  let V := a*(2 : ℝ)^q
                  let d := bourgainRelativeLevel P.N τ p
                  let s := bourgainCorrelationLevel P.N B C α τ ε k
                  ∃ u ∈ Set.Ioc (-H) H,
                    (bourgainIntegerSlice H U V u).Nonempty ∧
                    bourgainSliceCardCoefficient P.N ε s*
                        ((bourgainIntegerSlice H U V u).card : ℝ)*(S.card : ℝ)+
                      bourgainSliceSqrtCoefficient P.N L B C τ α ε d*
                        Real.sqrt ((bourgainIntegerSlice H U V u).card : ℝ)*
                          (∑ i ∈ A, ((W i).card : ℝ)^(3/2 : ℝ)) <
                    ∑ i ∈ A, ((W i).card : ℝ)*
                      ((bourgainDifferenceLevel (W i) (j i) ∩
                        bourgainIntegerSlice H U V u).card : ℝ)) := by
  exact @TaoTrudgianYang2025.bourgain_subdivided_common_slice σ τ hσ ε hε

-- BourgainSliceGeometry: exact public interface, including its quantifier order.
example (H T V u : ℝ) :
    (bourgainRealSlice H T V u).card = (bourgainIntegerSlice H T V u).card := by
  exact @TaoTrudgianYang2025.bourgainRealSlice_card H T V u

-- BourgainSliceGeometry: exact public interface, including its quantifier order.
example (H T V u : ℝ) :
    IsSeparated 1 (bourgainRealSlice H T V u) := by
  exact @TaoTrudgianYang2025.bourgainRealSlice_separated H T V u

-- BourgainSliceGeometry: exact public interface, including its quantifier order.
example {H T V u x : ℝ}
    (hx : x ∈ bourgainRealSlice H T V u) :
    x+u ∈ bourgainZetaBand T V := by
  exact @TaoTrudgianYang2025.bourgainRealSlice_mem_band H T V u x hx

-- BourgainSliceGeometry: exact public interface, including its quantifier order.
example {H T V u : ℝ} (hu : u ∈ Icc (-H) H) :
    ∀ x ∈ bourgainRealSlice H T V u, -(T+H) ≤ x ∧ x ≤ T+H := by
  exact @TaoTrudgianYang2025.bourgainRealSlice_bounds H T V u hu

-- BourgainSliceGeometry: exact public interface, including its quantifier order.
example {H T V u : ℝ}
    (h : (bourgainIntegerSlice H T V u).Nonempty) :
    (bourgainRealSlice H T V u).Nonempty := by
  exact @TaoTrudgianYang2025.bourgainRealSlice_nonempty H T V u h

-- BourgainLocalMean: exact public interface, including its quantifier order.
example (P : LargeValuePattern) {n : ℕ}
    (hn : n ∈ P.indices) :
    |Real.log P.N-Real.log (n : ℝ)| ≤ 1 := by
  exact @TaoTrudgianYang2025.bourgain_centered_frequency_bound P n hn

-- BourgainLocalMean: exact public interface, including its quantifier order.
example (P : LargeValuePattern) (t : ℝ) :
    bourgainCenteredPolynomial P t =
      Complex.exp (((Real.log P.N*t : ℝ) : ℂ)*Complex.I)*
        ∑ n ∈ P.indices, P.coeff n*dirichletPhase n t := by
  exact @TaoTrudgianYang2025.bourgain_centered_polynomial_identity P t

-- BourgainLocalMean: exact public interface, including its quantifier order.
example (P : LargeValuePattern) (t : ℝ) :
    ‖bourgainCenteredPolynomial P t‖ =
      ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n t‖ := by
  exact @TaoTrudgianYang2025.bourgain_centered_polynomial_norm P t

-- BourgainLocalMean: exact public interface, including its quantifier order.
example (P : LargeValuePattern) :
    Continuous (fun t => ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n t‖) := by
  exact @TaoTrudgianYang2025.LargeValuePattern.polynomial_norm_continuous P

-- BourgainLocalMean: exact public interface, including its quantifier order.
example (P : LargeValuePattern) :
    (∑ n ∈ P.indices, ‖P.coeff n‖) ≤ 2*P.N := by
  exact @TaoTrudgianYang2025.LargeValuePattern.coeff_mass_le_two_mul_N P

-- BourgainLocalMean: exact public interface, including its quantifier order.
example (P : LargeValuePattern)
    (t H : ℝ) (hH : 1 ≤ H) (q : ℕ) (hq : 2 ≤ q) :
    ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n t‖ ≤
      (gmAffineLocalBumpFourierSup/(2*Real.pi))*
        (∫ y in Icc (t-2*Real.pi*H) (t+2*Real.pi*H),
          ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n y‖)+
      2*P.N*gmAffineLocalBumpFourierTailConstant q hq*H^(1-(q : ℝ)) := by
  exact @TaoTrudgianYang2025.bourgain_polynomial_local_mean_add_tail P t H hH q hq

-- BourgainPowerMean: exact public interface, including its quantifier order.
example {η : ℝ} (hη : 0 < η) :
    ∃ C N₀ : ℝ, 0 < C ∧ 2 ≤ N₀ ∧ ∀ P : LargeValuePattern,
      N₀ ≤ P.N → P.N^(-1 : ℝ) ≤ P.V →
      ∀ t ∈ P.ordinates,
        P.V ≤ C*(∫ u in -(2*Real.pi*P.N^η)..(2*Real.pi*P.N^η),
          ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n (t+u)‖) := by
  exact @TaoTrudgianYang2025.bourgain_power_window_local_mean η hη

-- BourgainPowerMean: exact public interface, including its quantifier order.
example {η : ℝ} (hη : 0 < η) :
    ∃ C N₀ : ℝ, 0 < C ∧ 2 ≤ N₀ ∧ ∀ P : LargeValuePattern,
      N₀ ≤ P.N → ∀ σ δ : ℝ, 0 ≤ σ → δ ≤ 1 → P.N^(σ-δ) ≤ P.V →
      ∀ t ∈ P.ordinates,
        P.V ≤ C*(∫ u in -(2*Real.pi*P.N^η)..(2*Real.pi*P.N^η),
          ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n (t+u)‖) := by
  exact @TaoTrudgianYang2025.bourgain_power_window_local_mean_in_source_range η hη

-- BourgainLocalSquare: exact public interface, including its quantifier order.
example {f : ℝ → ℝ} {H : ℝ}
    (hH : 0 < H) (hf : IntervalIntegrable f volume (-H) H)
    (hf₂ : IntervalIntegrable (fun u => (f u)^2) volume (-H) H) :
    (∫ u in -H..H, f u)^2 ≤ 2*H*(∫ u in -H..H, (f u)^2) := by
  exact @TaoTrudgianYang2025.bourgain_interval_integral_sq_le f H hH hf hf₂

-- BourgainLocalSquare: exact public interface, including its quantifier order.
example {η : ℝ} (hη : 0 < η) :
    ∃ C N₀ : ℝ, 0 < C ∧ 2 ≤ N₀ ∧ ∀ P : LargeValuePattern,
      N₀ ≤ P.N → ∀ σ δ : ℝ, 0 ≤ σ → δ ≤ 1 → P.N^(σ-δ) ≤ P.V →
      ∀ t ∈ P.ordinates,
        P.V^2 ≤ C*P.N^η*
          (∫ u in -(2*Real.pi*P.N^η)..(2*Real.pi*P.N^η),
            ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n (t+u)‖^2) := by
  exact @TaoTrudgianYang2025.bourgain_power_window_local_square η hη

-- BourgainLocalSquare: exact public interface, including its quantifier order.
example {η : ℝ} (hη : 0 < η) :
    ∃ C N₀ : ℝ, 0 < C ∧ 2 ≤ N₀ ∧ ∀ P : LargeValuePattern,
      N₀ ≤ P.N → ∀ σ δ : ℝ, 0 ≤ σ → δ ≤ 1 → P.N^(σ-δ) ≤ P.V →
      ∀ t ∈ P.ordinates, ∀ x : ℝ, |x-t| ≤ 1 →
        P.V^2 ≤ C*P.N^η*
          (∫ u in -(1+2*Real.pi*P.N^η)..(1+2*Real.pi*P.N^η),
            ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n (x+u)‖^2) := by
  exact @TaoTrudgianYang2025.bourgain_power_window_displaced_square η hη

-- BourgainMixedLower: exact public interface, including its quantifier order.
example {W : Finset ℝ}
    (hsep : IsSeparated 2 W) (ℓ : ℤ) :
    Set.InjOn Prod.fst
      (↑((W ×ˢ W).filter fun p => |p.1-p.2-(ℓ : ℝ)| < 1) : Set (ℝ × ℝ)) := by
  exact @TaoTrudgianYang2025.bourgain_difference_pairs_fst_injective W hsep ℓ

-- BourgainMixedLower: exact public interface, including its quantifier order.
example {W : Finset ℝ}
    (hsep : IsSeparated 2 W) (ℓ : ℤ) (v : ℝ) (f : ℝ → ℝ)
    (hf : ∀ t ∈ W, 0 ≤ f t)
    (hpairs : ∀ t ∈ W, ∀ w ∈ W, |t-w-(ℓ : ℝ)| < 1 → v ≤ f t) :
    (bourgainDifferenceCount W ℓ : ℝ)*v ≤ ∑ t ∈ W, f t := by
  exact @TaoTrudgianYang2025.bourgainDifferenceCount_mul_le W hsep ℓ v f hf hpairs

-- BourgainMixedLower: exact public interface, including its quantifier order.
example {η : ℝ} (hη : 0 < η) :
    ∃ C N₀ : ℝ, 0 < C ∧ 2 ≤ N₀ ∧ ∀ P : LargeValuePattern,
      N₀ ≤ P.N → ∀ σ δ : ℝ, 0 ≤ σ → δ ≤ 1 → P.N^(σ-δ) ≤ P.V →
      ∀ W : Finset ℝ, W ⊆ P.ordinates → IsSeparated 2 W →
      ∀ D : Finset ℤ,
        P.V^2*(∑ ℓ ∈ D, (bourgainDifferenceCount W ℓ : ℝ)) ≤
          C*P.N^η*
            (∫ u in -(1+2*Real.pi*P.N^η)..(1+2*Real.pi*P.N^η),
              ∑ t ∈ W, ∑ ℓ ∈ D,
                ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n (t-(ℓ : ℝ)+u)‖^2) := by
  exact @TaoTrudgianYang2025.bourgain_mixed_local_difference_counts η hη

-- BourgainMixedFamily: exact public interface, including its quantifier order.
example {η : ℝ} (hη : 0 < η) :
    ∃ M N₀ : ℝ, 0 < M ∧ 2 ≤ N₀ ∧ ∀ P : LargeValuePattern,
      N₀ ≤ P.N → ∀ σ δ : ℝ, 0 ≤ σ → δ ≤ 1 → P.N^(σ-δ) ≤ P.V →
      ∀ (L : ℝ) (hL : 0 < L) (A : Finset ℕ) (W : ℕ → Finset ℝ),
        (∀ i ∈ A, W i ⊆ (P.localized L hL i).reflectedOrdinates) →
        (∀ i ∈ A, IsSeparated 2 (W i)) → ∀ D : Finset ℤ,
        let S := A.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))
        P.V^2*(∑ i ∈ A, ∑ ℓ ∈ D, (bourgainDifferenceCount (W i) ℓ : ℝ)) ≤
          M*P.N^η*
            (∫ u in -(1+2*Real.pi*P.N^η)..(1+2*Real.pi*P.N^η),
              ∑ t ∈ S, ∑ ℓ ∈ D,
                ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n (t-(ℓ : ℝ)+u)‖^2) := by
  exact @TaoTrudgianYang2025.bourgain_subdivided_mixed_difference_counts η hη

-- BourgainMixedFamily: exact public interface, including its quantifier order.
example (A : Finset ℕ) (W : ℕ → Finset ℝ)
    (D : ℕ → Finset ℤ) (S : Finset ℤ) (d : ℝ)
    (hrel : ∀ i ∈ A, ∀ ℓ ∈ D i,
      d*((W i).card : ℝ) ≤ (bourgainDifferenceCount (W i) ℓ : ℝ)) :
    d*(∑ i ∈ A, ((W i).card : ℝ)*((D i ∩ S).card : ℝ)) ≤
      ∑ i ∈ A, ∑ ℓ ∈ S, (bourgainDifferenceCount (W i) ℓ : ℝ) := by
  exact @TaoTrudgianYang2025.bourgain_relative_slice_weight_le A W D S d hrel

-- BourgainMixedFamily: exact public interface, including its quantifier order.
example {η : ℝ} (hη : 0 < η) :
    ∃ M N₀ : ℝ, 0 < M ∧ 2 ≤ N₀ ∧ ∀ P : LargeValuePattern,
      N₀ ≤ P.N → ∀ σ δ : ℝ, 0 ≤ σ → δ ≤ 1 → P.N^(σ-δ) ≤ P.V →
      ∀ (L : ℝ) (hL : 0 < L) (A : Finset ℕ), A.Nonempty →
      ∀ (W : ℕ → Finset ℝ) (j : ℕ → ℕ) (q : ℕ) (B C τ α ε s d : ℝ),
        (∀ i ∈ A, W i ⊆ (P.localized L hL i).reflectedOrdinates) →
        (∀ i ∈ A, IsSeparated 2 (W i)) → L ≤ P.N^(τ+δ) →
        (∀ i ∈ A, BourgainComponentBand P.N L B C τ α ε (W i) (j i) q) →
        0 < s → 0 < d →
        (∀ i ∈ A, (2 : ℝ)^(j i) ≤ 2*d*((W i).card : ℝ)) →
        (∀ i ∈ A, ∀ ℓ ∈ bourgainDifferenceLevel (W i) (j i),
          d*((W i).card : ℝ) ≤ (bourgainDifferenceCount (W i) ℓ : ℝ)) →
        (∀ i ∈ A, s ≤ bourgainZetaBandCorrelation
          (bourgainDifferenceLevel (W i) (j i)) (P.N^(ε/8)) (L+P.N^(ε/8)+1)
          (P.N^(-bourgainSharedFloorExponent α τ ε)*(2 : ℝ)^q)) →
        let H := P.N^(ε/8)
        let U := L+H+1
        let V := P.N^(-bourgainSharedFloorExponent α τ ε)*(2 : ℝ)^q
        let S := A.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))
        ∃ u ∈ Ioc (-H) H,
          (bourgainIntegerSlice H U V u).Nonempty ∧
          P.V^2*d*(bourgainSliceCardCoefficient P.N ε s*
              ((bourgainIntegerSlice H U V u).card : ℝ)*(S.card : ℝ)+
            bourgainSliceSqrtCoefficient P.N L B C τ α ε d*
              Real.sqrt ((bourgainIntegerSlice H U V u).card : ℝ)*
                (∑ i ∈ A, ((W i).card : ℝ)^(3/2 : ℝ))) <
          M*P.N^η*(∫ v in -(1+2*Real.pi*P.N^η)..(1+2*Real.pi*P.N^η),
            ∑ t ∈ S, ∑ ℓ ∈ bourgainIntegerSlice H U V u,
              ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n (t-(ℓ : ℝ)+v)‖^2) := by
  exact @TaoTrudgianYang2025.bourgain_component_family_mixed_lower η hη

-- BourgainCommonMixed: exact public interface, including its quantifier order.
example {σ τ η : ℝ}
    (hσ : 3/4 < σ) (hη : 0 < η) {ε : ℝ} (hε : 0 < ε) :
    ∃ B C δ M N₀ : ℝ, 0 < B ∧ 2 ≤ C ∧ 0 < δ ∧ δ ≤ 1 ∧ 0 < M ∧ 2 ≤ N₀ ∧
      ∀ (P : LargeValuePattern) (L : ℝ) (hL : 0 < L),
        C ≤ P.N → N₀ ≤ P.N → P.N ≤ L → L ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        ∃ W : ℕ → Finset ℝ,
          (∀ i : ℕ, W i ⊆ (P.localized L hL i).reflectedOrdinates ∧
            IsSeparated 2 (W i) ∧ InBaseInterval L (W i) ∧
            ((P.localized L hL i).ordinates.card : ℝ) ≤ C*P.N^ε*((W i).card : ℝ)) ∧
          ∀ α : ℝ,
            let I := Finset.range (Nat.floor (P.T/L)+1)
            let a := P.N^(-bourgainSharedFloorExponent α τ ε)
            let J := bourgainZetaBandCount B (L+P.N^(ε/8)+1) a
            let F := C*(P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε)+
              P.N^(-2*α+τ+12-16*σ+ε))
            ∃ q ∈ Finset.range J, ∃ p ∈ Finset.range (bourgainRelativeLevelCount P.N τ),
              ∃ k ∈ Finset.range (bourgainCorrelationLevelCount P.N B C α τ ε),
              ∃ A : Finset ℕ, A ⊆ I ∧
              ∃ j : ℕ → ℕ,
                (∀ i ∈ A, (F < ((P.localized L hL i).ordinates.card : ℝ) ∧
                  BourgainComponentBand P.N L B C τ α ε (W i) (j i) q ∧
                  (let d := bourgainRelativeLevel P.N τ p
                  0 < d ∧ d ≤ 1 ∧
                  d*((W i).card : ℝ) ≤ (2 : ℝ)^(j i) ∧
                  (2 : ℝ)^(j i) < 2*d*((W i).card : ℝ) ∧
                  (∀ ℓ ∈ bourgainDifferenceLevel (W i) (j i),
                    d*((W i).card : ℝ) ≤ (bourgainDifferenceCount (W i) ℓ : ℝ) ∧
                    (bourgainDifferenceCount (W i) ℓ : ℝ) < 4*d*((W i).card : ℝ)) ∧
                  d*((bourgainDifferenceLevel (W i) (j i)).card : ℝ) ≤ 2*((W i).card : ℝ)) ∧
                  let d := bourgainRelativeLevel P.N τ p
                  let r := bourgainZetaBandCorrelation
                    (bourgainDifferenceLevel (W i) (j i)) (P.N^(ε/8))
                    (L+P.N^(ε/8)+1) (a*(2 : ℝ)^q)
                  P.N^(-2*α)*P.N^τ <
                    1024*(Nat.log 2 (W i).card+1 : ℕ)^2*(J : ℝ)^2*
                      C*(L+P.N^(ε/8)+1)^(1+ε)*d*r^2) ∧
                  (let H := P.N^(ε/8)
                  let U := L+H+1
                  let D := bourgainDifferenceLevel (W i) (j i)
                  let V := a*(2 : ℝ)^q
                  let r := bourgainZetaBandCorrelation D H U V
                  let μ := volume.real (bourgainZetaBand U V)
                  let s := bourgainCorrelationLevel P.N B C α τ ε k
                  0 < s ∧ s ≤ r ∧ r < 2*s ∧ s ≤ 4*H ∧
                  s*Real.sqrt μ*Real.sqrt (D.card : ℝ) ≤ bourgainZetaBandMass D H U V ∧
                  bourgainZetaBandMass D H U V < 2*s*Real.sqrt μ*Real.sqrt (D.card : ℝ)) ∧
                  let d := bourgainRelativeLevel P.N τ p
                  let s := bourgainCorrelationLevel P.N B C α τ ε k
                  P.N^(-2*α)*P.N^τ <
                    4096*(Nat.log 2 (W i).card+1 : ℕ)^2*(J : ℝ)^2*
                      C*(L+P.N^(ε/8)+1)^(1+ε)*d*s^2) ∧
                let S := A.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))
                S ⊆ P.ordinates ∧ S.card = ∑ i ∈ A, (W i).card ∧
                IsSeparated 1 S ∧
                (∀ t ∈ S, P.V ≤ ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n t‖) ∧
                (∀ i ∈ A, ∀ ℓ : ℤ,
                  bourgainDifferenceCount ((P.localized L hL i).retainedOriginal (W i)) ℓ =
                    bourgainDifferenceCount (W i) ℓ) ∧
                (P.ordinates.card : ℝ) ≤
                  (I.card : ℝ)*F+C*P.N^ε*(J : ℝ)*(bourgainRelativeLevelCount P.N τ : ℝ)*
                    (bourgainCorrelationLevelCount P.N B C α τ ε : ℝ)*(S.card : ℝ) ∧
                ((P.ordinates.card : ℝ) ≤ (I.card : ℝ)*F ∨
                  let H := P.N^(ε/8)
                  let U := L+H+1
                  let V := a*(2 : ℝ)^q
                  let d := bourgainRelativeLevel P.N τ p
                  let s := bourgainCorrelationLevel P.N B C α τ ε k
                  ∃ u ∈ Set.Ioc (-H) H,
                    (bourgainIntegerSlice H U V u).Nonempty ∧
                    P.V^2*d*(bourgainSliceCardCoefficient P.N ε s*
                        ((bourgainIntegerSlice H U V u).card : ℝ)*(S.card : ℝ)+
                      bourgainSliceSqrtCoefficient P.N L B C τ α ε d*
                        Real.sqrt ((bourgainIntegerSlice H U V u).card : ℝ)*
                          (∑ i ∈ A, ((W i).card : ℝ)^(3/2 : ℝ))) <
                    M*P.N^η*(∫ v in -(1+2*Real.pi*P.N^η)..(1+2*Real.pi*P.N^η),
                      ∑ t ∈ S, ∑ ℓ ∈ bourgainIntegerSlice H U V u,
                        ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n (t-(ℓ : ℝ)+v)‖^2)) := by
  exact @TaoTrudgianYang2025.bourgain_subdivided_mixed_lower σ τ η hσ hη ε hε

-- Complete covers, closed spatial endpoints and zero amplitude.
example : bourgainIntegerCover 0 0 = {0} := by
  norm_num [bourgainIntegerCover]

example : (3 : ℤ) ∈ bourgainIntegerCover 1 2 := by
  norm_num [bourgainIntegerCover]

example : (-3 : ℤ) ∈ bourgainIntegerCover 1 2 := by
  norm_num [bourgainIntegerCover]

example (V : ℝ) :
    (3 : ℤ) ∈ bourgainIntegerSlice 1 2 V (-1) ↔
      (2 : ℝ) ∈ bourgainZetaBand 2 V := by
  simpa only [Int.cast_ofNat, show (3 : ℝ)+(-1) = 2 by norm_num] using
    mem_bourgainIntegerSlice (H := 1) (T := 2) (V := V) (u := -1)
      (by constructor <;> norm_num) 3

example (H T u : ℝ) : bourgainIntegerSlice H T 0 u = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro ℓ hℓ
  have hb := (Finset.mem_filter.mp hℓ).2
  have hlt := ((mem_bourgainZetaBand T 0 ((ℓ : ℝ)+u)).mp hb).2.2.2
  have hn : 0 ≤ zetaMomentCriticalNorm ((ℓ : ℝ)+u) := norm_nonneg _
  linarith

example (H T u : ℝ) : bourgainRealSlice H T 0 u = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hlt := ((mem_bourgainZetaBand T 0 (x+u)).mp (bourgainRealSlice_mem_band hx)).2.2.2
  have hn : 0 ≤ zetaMomentCriticalNorm (x+u) := norm_nonneg _
  linarith

example {H T V u : ℝ} (hu : u ∈ Icc (-H) H) (ℓ : ℤ) :
    ℓ ∈ bourgainIntegerSlice H T V u ↔
      -T ≤ (ℓ : ℝ)+u ∧ (ℓ : ℝ)+u ≤ T ∧
      V ≤ zetaMomentCriticalNorm ((ℓ : ℝ)+u) ∧
        zetaMomentCriticalNorm ((ℓ : ℝ)+u) < 2*V := by
  rw [mem_bourgainIntegerSlice hu, mem_bourgainZetaBand]

-- Finite selection losses are retained, not replaced by polynomial cardinalities.
example (τ : ℝ) : bourgainDifferenceLogLoss 1 τ = 3 := by
  simp [bourgainDifferenceLogLoss]

example (N τ : ℝ) : bourgainDifferenceLogLoss N (-τ) = bourgainDifferenceLogLoss N τ := by
  simp [bourgainDifferenceLogLoss]

example : bourgainSliceCardCoefficient 1 0 2 = (1/6 : ℝ) := by
  norm_num [bourgainSliceCardCoefficient]

example (N ε s : ℝ) :
    bourgainSliceCardCoefficient N ε (-s) = bourgainSliceCardCoefficient N ε s := by
  simp [bourgainSliceCardCoefficient]

-- No component localization changes the actual polynomial or its modulation.
example (P : LargeValuePattern) (L : ℝ) (hL : 0 < L) (i : ℕ) (t : ℝ) :
    bourgainCenteredPolynomial (P.localized L hL i) t = bourgainCenteredPolynomial P t := rfl

example (P : LargeValuePattern) :
    bourgainCenteredPolynomial P 0 = ∑ n ∈ P.indices, P.coeff n := by
  simp [bourgain_centered_polynomial_identity, dirichletPhase_zero]

example (P : LargeValuePattern) :
    |Real.log P.N-Real.log (P.scale : ℝ)| = 0 := by
  rw [P.N_eq_scale, sub_self, abs_zero]

example (P : LargeValuePattern) :
    Real.log P.N-Real.log (2*P.N) = -Real.log 2 := by
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (zero_lt_one.trans P.one_lt_N).ne']
  ring

example (P : LargeValuePattern) :
    P.scale ∈ P.indices := by
  rw [P.indices_eq_dyadicInterval]
  exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩

example (P : LargeValuePattern) :
    2*P.scale ∈ P.indices := by
  rw [P.indices_eq_dyadicInterval]
  exact Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩

-- Strict one-unit bins, including their excluded boundary.
example : bourgainDifferenceCount ({(0 : ℝ),2} : Finset ℝ) 1 = 0 := by
  have hp : ({(0 : ℝ),2} : Finset ℝ) ×ˢ ({(0 : ℝ),2} : Finset ℝ) =
      {(0,0),(0,2),(2,0),(2,2)} := by
    ext ⟨a,b⟩
    simp only [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    tauto
  norm_num [bourgainDifferenceCount, hp, Finset.filter_insert, Finset.filter_singleton]

example : bourgainDifferenceCount ({(0 : ℝ),2} : Finset ℝ) 2 = 1 := by
  have hp : ({(0 : ℝ),2} : Finset ℝ) ×ˢ ({(0 : ℝ),2} : Finset ℝ) =
      {(0,0),(0,2),(2,0),(2,2)} := by
    ext ⟨a,b⟩
    simp only [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    tauto
  norm_num [bourgainDifferenceCount, hp, Finset.filter_insert, Finset.filter_singleton]

example (P : LargeValuePattern) (η : ℝ) :
    0 < 1+2*Real.pi*P.N^η := by
  have hN : 0 < P.N := zero_lt_one.trans P.one_lt_N
  positivity

end BourgainIntegerSliceMixedRegression

namespace BourgainHeathBrownComparisonRegression

open MeasureTheory RiemannZeta.GuthMaynard Set
open scoped Interval Classical

-- Exact public interfaces, including the selected-family consumer types.

example (P : LargeValuePattern) (W : Finset ℝ) :
    0 ≤ bourgainSelfMoment P W := by
  exact @TaoTrudgianYang2025.bourgainSelfMoment_nonneg P W

example {N H R : ℝ}
    (hN : 0 ≤ N) (hH : 0 ≤ H) (hR : 0 ≤ R) :
    0 ≤ bourgainSecondBudget N H R := by
  exact @TaoTrudgianYang2025.bourgainSecondBudget_nonneg N H R hN hH hR

example (P : LargeValuePattern) (W : Finset ℝ) (c : ℝ) :
    bourgainSelfMoment P W ≤
      2*gmDiscreteRatioMoment 2 P.scale (W.image (fun t => c-t))+
        2*(W.card : ℝ)^2 := by
  exact @TaoTrudgianYang2025.bourgainSelfMoment_le_native P W c

example {ε : ℝ} (hε : 0 < ε) :
    ∃ C H₀ : ℝ, 0 < C ∧ 1 ≤ H₀ ∧
      ∀ (P : LargeValuePattern) (W : Finset ℝ) (a H : ℝ),
        H₀ ≤ H → IsSeparated 1 W →
        (∀ t ∈ W, a ≤ t ∧ t ≤ a+H) →
        bourgainSelfMoment P W ≤
          C*H^ε*bourgainSecondBudget P.N H (W.card : ℝ) := by
  exact @TaoTrudgianYang2025.bourgain_separated_self_moment ε hε

example (P : LargeValuePattern)
    {n : ℕ} (hn : n ∈ P.indices) (t v : ℝ) :
    dirichletPhase n (t+v) = dirichletPhase n t*dirichletPhase n v := by
  exact @TaoTrudgianYang2025.LargeValuePattern.dirichletPhase_add P n hn t v

example (P : LargeValuePattern) (t u v : ℝ) :
    (∑ n ∈ P.indices, P.coeff n*dirichletPhase n (t-u+v)) =
      ∑ n ∈ P.indices, (P.coeff n*dirichletPhase n v)*dirichletPhase n (t-u) := by
  exact @TaoTrudgianYang2025.bourgain_shifted_polynomial P t u v

example (P : LargeValuePattern)
    (W U : Finset ℝ) (v : ℝ) :
    (∑ t ∈ W, ∑ u ∈ U,
      ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n (t-u+v)‖^2) ≤
      Real.sqrt (bourgainSelfMoment P W)*Real.sqrt (bourgainSelfMoment P U) := by
  exact @TaoTrudgianYang2025.bourgain_shifted_mixed_cauchySchwarz P W U v

example {H T V u : ℝ} (f : ℝ → ℝ) :
    (∑ ℓ ∈ bourgainIntegerSlice H T V u, f (ℓ : ℝ)) =
      ∑ x ∈ bourgainRealSlice H T V u, f x := by
  exact @TaoTrudgianYang2025.bourgain_integerSlice_sum H T V u f

example (P : LargeValuePattern)
    (W : Finset ℝ) (H T V u v : ℝ) :
    (∑ t ∈ W, ∑ ℓ ∈ bourgainIntegerSlice H T V u,
      ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n (t-(ℓ : ℝ)+v)‖^2) ≤
      Real.sqrt (bourgainSelfMoment P W)*
        Real.sqrt (bourgainSelfMoment P (bourgainRealSlice H T V u)) := by
  exact @TaoTrudgianYang2025.bourgain_slice_mixed_cauchySchwarz P W H T V u v

example (P : LargeValuePattern)
    (W : Finset ℝ) (H T V u : ℝ) :
    Continuous (fun v : ℝ => ∑ t ∈ W, ∑ ℓ ∈ bourgainIntegerSlice H T V u,
      ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n (t-(ℓ : ℝ)+v)‖^2) := by
  exact @TaoTrudgianYang2025.bourgain_mixed_slice_continuous P W H T V u

example (P : LargeValuePattern)
    (W : Finset ℝ) (H T V u r : ℝ) (hr : 0 ≤ r) :
    (∫ v in -r..r, ∑ t ∈ W, ∑ ℓ ∈ bourgainIntegerSlice H T V u,
      ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n (t-(ℓ : ℝ)+v)‖^2) ≤
      2*r*(Real.sqrt (bourgainSelfMoment P W)*
        Real.sqrt (bourgainSelfMoment P (bourgainRealSlice H T V u))) := by
  exact @TaoTrudgianYang2025.bourgain_slice_mixed_integral_cauchySchwarz P W H T V u r hr

example {A B D : ℝ} (hA : 0 ≤ A) :
    Real.sqrt (A*B)*Real.sqrt (A*D) =
      A*(Real.sqrt B*Real.sqrt D) := by
  exact @TaoTrudgianYang2025.bourgain_sqrt_common_factor A B D hA

example {ε : ℝ} (hε : 0 < ε) :
    ∃ C E₀ : ℝ, 0 < C ∧ 1 ≤ E₀ ∧
      ∀ (P : LargeValuePattern) (S : Finset ℝ), S ⊆ P.ordinates →
      ∀ (H T V u r E : ℝ), u ∈ Icc (-H) H → 0 ≤ r →
        E₀ ≤ E → P.T ≤ E → 2*(T+H) ≤ E →
        (∫ v in -r..r, ∑ t ∈ S, ∑ ℓ ∈ bourgainIntegerSlice H T V u,
          ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n (t-(ℓ : ℝ)+v)‖^2) ≤
          2*r*C*E^ε*
            (Real.sqrt (bourgainSecondBudget P.N E (S.card : ℝ))*
              Real.sqrt (bourgainSecondBudget P.N E
                ((bourgainIntegerSlice H T V u).card : ℝ))) := by
  exact @TaoTrudgianYang2025.bourgain_actual_mixed_upper ε hε

example {σ τ η θ : ℝ}
    (hσ : 3/4 < σ) (hη : 0 < η) (hθ : 0 < θ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B C δ M N₀ D E₀ : ℝ,
      0 < B ∧ 2 ≤ C ∧ 0 < δ ∧ δ ≤ 1 ∧ 0 < M ∧ 2 ≤ N₀ ∧ 0 < D ∧ 1 ≤ E₀ ∧
      ∀ (P : LargeValuePattern) (L : ℝ) (hL : 0 < L),
        C ≤ P.N → N₀ ≤ P.N → P.N ≤ L → L ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        ∃ W : ℕ → Finset ℝ,
          (∀ i : ℕ, W i ⊆ (P.localized L hL i).reflectedOrdinates ∧
            IsSeparated 2 (W i) ∧ InBaseInterval L (W i) ∧
            ((P.localized L hL i).ordinates.card : ℝ) ≤ C*P.N^ε*((W i).card : ℝ)) ∧
          ∀ α : ℝ,
            let I := Finset.range (Nat.floor (P.T/L)+1)
            let a := P.N^(-bourgainSharedFloorExponent α τ ε)
            let J := bourgainZetaBandCount B (L+P.N^(ε/8)+1) a
            let F := C*(P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε)+
              P.N^(-2*α+τ+12-16*σ+ε))
            ∃ q ∈ Finset.range J, ∃ p ∈ Finset.range (bourgainRelativeLevelCount P.N τ),
              ∃ k ∈ Finset.range (bourgainCorrelationLevelCount P.N B C α τ ε),
              ∃ A : Finset ℕ, A ⊆ I ∧
              ∃ j : ℕ → ℕ,
                (∀ i ∈ A, (F < ((P.localized L hL i).ordinates.card : ℝ) ∧
                  BourgainComponentBand P.N L B C τ α ε (W i) (j i) q ∧
                  (let d := bourgainRelativeLevel P.N τ p
                  0 < d ∧ d ≤ 1 ∧
                  d*((W i).card : ℝ) ≤ (2 : ℝ)^(j i) ∧
                  (2 : ℝ)^(j i) < 2*d*((W i).card : ℝ) ∧
                  (∀ ℓ ∈ bourgainDifferenceLevel (W i) (j i),
                    d*((W i).card : ℝ) ≤ (bourgainDifferenceCount (W i) ℓ : ℝ) ∧
                    (bourgainDifferenceCount (W i) ℓ : ℝ) < 4*d*((W i).card : ℝ)) ∧
                  d*((bourgainDifferenceLevel (W i) (j i)).card : ℝ) ≤ 2*((W i).card : ℝ)) ∧
                  let d := bourgainRelativeLevel P.N τ p
                  let r := bourgainZetaBandCorrelation
                    (bourgainDifferenceLevel (W i) (j i)) (P.N^(ε/8))
                    (L+P.N^(ε/8)+1) (a*(2 : ℝ)^q)
                  P.N^(-2*α)*P.N^τ <
                    1024*(Nat.log 2 (W i).card+1 : ℕ)^2*(J : ℝ)^2*
                      C*(L+P.N^(ε/8)+1)^(1+ε)*d*r^2) ∧
                  (let H := P.N^(ε/8)
                  let U := L+H+1
                  let D := bourgainDifferenceLevel (W i) (j i)
                  let V := a*(2 : ℝ)^q
                  let r := bourgainZetaBandCorrelation D H U V
                  let μ := volume.real (bourgainZetaBand U V)
                  let s := bourgainCorrelationLevel P.N B C α τ ε k
                  0 < s ∧ s ≤ r ∧ r < 2*s ∧ s ≤ 4*H ∧
                  s*Real.sqrt μ*Real.sqrt (D.card : ℝ) ≤ bourgainZetaBandMass D H U V ∧
                  bourgainZetaBandMass D H U V < 2*s*Real.sqrt μ*Real.sqrt (D.card : ℝ)) ∧
                  let d := bourgainRelativeLevel P.N τ p
                  let s := bourgainCorrelationLevel P.N B C α τ ε k
                  P.N^(-2*α)*P.N^τ <
                    4096*(Nat.log 2 (W i).card+1 : ℕ)^2*(J : ℝ)^2*
                      C*(L+P.N^(ε/8)+1)^(1+ε)*d*s^2) ∧
                let S := A.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))
                S ⊆ P.ordinates ∧ S.card = ∑ i ∈ A, (W i).card ∧
                IsSeparated 1 S ∧
                (∀ t ∈ S, P.V ≤ ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n t‖) ∧
                (∀ i ∈ A, ∀ ℓ : ℤ,
                  bourgainDifferenceCount ((P.localized L hL i).retainedOriginal (W i)) ℓ =
                    bourgainDifferenceCount (W i) ℓ) ∧
                (P.ordinates.card : ℝ) ≤
                  (I.card : ℝ)*F+C*P.N^ε*(J : ℝ)*(bourgainRelativeLevelCount P.N τ : ℝ)*
                    (bourgainCorrelationLevelCount P.N B C α τ ε : ℝ)*(S.card : ℝ) ∧
                ((P.ordinates.card : ℝ) ≤ (I.card : ℝ)*F ∨
                  let H := P.N^(ε/8)
                  let U := L+H+1
                  let V := a*(2 : ℝ)^q
                  let d := bourgainRelativeLevel P.N τ p
                  let s := bourgainCorrelationLevel P.N B C α τ ε k
                  ∃ u ∈ Set.Ioc (-H) H,
                    (bourgainIntegerSlice H U V u).Nonempty ∧
                    ∀ E : ℝ, E₀ ≤ E → P.T ≤ E → 2*(U+H) ≤ E →
                    P.V^2*d*(bourgainSliceCardCoefficient P.N ε s*
                        ((bourgainIntegerSlice H U V u).card : ℝ)*(S.card : ℝ)+
                      bourgainSliceSqrtCoefficient P.N L B C τ α ε d*
                        Real.sqrt ((bourgainIntegerSlice H U V u).card : ℝ)*
                          (∑ i ∈ A, ((W i).card : ℝ)^(3/2 : ℝ))) <
                    M*P.N^η*(2*(1+2*Real.pi*P.N^η)*D*E^θ*
                      (Real.sqrt (bourgainSecondBudget P.N E (S.card : ℝ))*
                        Real.sqrt (bourgainSecondBudget P.N E
                          ((bourgainIntegerSlice H U V u).card : ℝ))))) := by
  exact @TaoTrudgianYang2025.bourgain_subdivided_mixed_comparison σ τ η θ hσ hη hθ ε hε

example
    (P : LargeValuePattern) {L : ℝ} (hL : 0 < L) (i : ℕ) (W : Finset ℝ)
    (hsub : W ⊆ (P.localized L hL i).reflectedOrdinates)
    {B C τ α ε δ s d : ℝ} {j q : ℕ}
    (hC : 0 < C) (hδ : δ ≤ 1) (hT : L ≤ P.N^(τ+δ))
    (hband : BourgainComponentBand P.N L B C τ α ε W j q)
    (hd : 0 < d)
    (hproduct : P.N^(-2*α)*P.N^τ <
      4096*(Nat.log 2 W.card+1 : ℕ)^2*
        (bourgainZetaBandCount B (L+P.N^(ε/8)+1)
          (P.N^(-bourgainSharedFloorExponent α τ ε)) : ℝ)^2*
        C*(L+P.N^(ε/8)+1)^(1+ε)*d*s^2) :
    bourgainEliminatedCardCoefficient P.N L B C τ α ε <
      d*bourgainSliceCardCoefficient P.N ε s := by
  exact @TaoTrudgianYang2025.bourgain_component_card_coefficient P L hL i W hsub B C τ α ε δ s d j q hC hδ hT hband hd hproduct

example
    (N L B C τ α ε d : ℝ) (hd : d ≠ 0) :
    d*bourgainSliceSqrtCoefficient N L B C τ α ε d =
      bourgainSliceSqrtCoefficient N L B C τ α ε 1 := by
  exact @TaoTrudgianYang2025.bourgain_slice_sqrt_coefficient_cancel N L B C τ α ε d hd

example {ι : Type*} (A I : Finset ι) (hAI : A ⊆ I)
    (R : ι → ℝ) (hR : ∀ i ∈ A, 0 ≤ R i) :
    (∑ i ∈ A, R i)^(3/2 : ℝ) ≤
      Real.sqrt (I.card : ℝ)*(∑ i ∈ A, (R i)^(3/2 : ℝ)) := by
  exact @TaoTrudgianYang2025.bourgain_sum_three_halves ι A I hAI R hR

example {N L B C τ α ε : ℝ}
    (hN : 1 ≤ N) (hL : 0 < L) (hC : 0 < C) :
    0 < bourgainEliminatedCardCoefficient N L B C τ α ε := by
  exact @TaoTrudgianYang2025.bourgainEliminatedCardCoefficient_pos N L B C τ α ε hN hL hC

example {N L B C τ α ε : ℝ}
    (hN : 1 ≤ N) (hL : 0 < L) (hC : 0 < C) :
    0 < bourgainSliceSqrtCoefficient N L B C τ α ε 1 := by
  exact @TaoTrudgianYang2025.bourgainSliceSqrtCoefficient_one_pos N L B C τ α ε hN hL hC

example {σ τ η θ : ℝ}
    (hσ : 3/4 < σ) (hη : 0 < η) (hθ : 0 < θ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B C δ M N₀ D E₀ : ℝ,
      0 < B ∧ 2 ≤ C ∧ 0 < δ ∧ δ ≤ 1 ∧ 0 < M ∧ 2 ≤ N₀ ∧ 0 < D ∧ 1 ≤ E₀ ∧
      ∀ (P : LargeValuePattern) (L : ℝ) (hL : 0 < L),
        C ≤ P.N → N₀ ≤ P.N → P.N ≤ L → L ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        ∃ W : ℕ → Finset ℝ,
          (∀ i : ℕ, W i ⊆ (P.localized L hL i).reflectedOrdinates ∧
            IsSeparated 2 (W i) ∧ InBaseInterval L (W i) ∧
            ((P.localized L hL i).ordinates.card : ℝ) ≤ C*P.N^ε*((W i).card : ℝ)) ∧
          ∀ α : ℝ,
            let I := Finset.range (Nat.floor (P.T/L)+1)
            let a := P.N^(-bourgainSharedFloorExponent α τ ε)
            let J := bourgainZetaBandCount B (L+P.N^(ε/8)+1) a
            let F := C*(P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε)+
              P.N^(-2*α+τ+12-16*σ+ε))
            ∃ q ∈ Finset.range J, ∃ p ∈ Finset.range (bourgainRelativeLevelCount P.N τ),
              ∃ k ∈ Finset.range (bourgainCorrelationLevelCount P.N B C α τ ε),
              ∃ A : Finset ℕ, A ⊆ I ∧
              ∃ j : ℕ → ℕ,
                (∀ i ∈ A, (F < ((P.localized L hL i).ordinates.card : ℝ) ∧
                  BourgainComponentBand P.N L B C τ α ε (W i) (j i) q ∧
                  (let d := bourgainRelativeLevel P.N τ p
                  0 < d ∧ d ≤ 1 ∧
                  d*((W i).card : ℝ) ≤ (2 : ℝ)^(j i) ∧
                  (2 : ℝ)^(j i) < 2*d*((W i).card : ℝ) ∧
                  (∀ ℓ ∈ bourgainDifferenceLevel (W i) (j i),
                    d*((W i).card : ℝ) ≤ (bourgainDifferenceCount (W i) ℓ : ℝ) ∧
                    (bourgainDifferenceCount (W i) ℓ : ℝ) < 4*d*((W i).card : ℝ)) ∧
                  d*((bourgainDifferenceLevel (W i) (j i)).card : ℝ) ≤ 2*((W i).card : ℝ)) ∧
                  let d := bourgainRelativeLevel P.N τ p
                  let r := bourgainZetaBandCorrelation
                    (bourgainDifferenceLevel (W i) (j i)) (P.N^(ε/8))
                    (L+P.N^(ε/8)+1) (a*(2 : ℝ)^q)
                  P.N^(-2*α)*P.N^τ <
                    1024*(Nat.log 2 (W i).card+1 : ℕ)^2*(J : ℝ)^2*
                      C*(L+P.N^(ε/8)+1)^(1+ε)*d*r^2) ∧
                  (let H := P.N^(ε/8)
                  let U := L+H+1
                  let D := bourgainDifferenceLevel (W i) (j i)
                  let V := a*(2 : ℝ)^q
                  let r := bourgainZetaBandCorrelation D H U V
                  let μ := volume.real (bourgainZetaBand U V)
                  let s := bourgainCorrelationLevel P.N B C α τ ε k
                  0 < s ∧ s ≤ r ∧ r < 2*s ∧ s ≤ 4*H ∧
                  s*Real.sqrt μ*Real.sqrt (D.card : ℝ) ≤ bourgainZetaBandMass D H U V ∧
                  bourgainZetaBandMass D H U V < 2*s*Real.sqrt μ*Real.sqrt (D.card : ℝ)) ∧
                  let d := bourgainRelativeLevel P.N τ p
                  let s := bourgainCorrelationLevel P.N B C α τ ε k
                  P.N^(-2*α)*P.N^τ <
                    4096*(Nat.log 2 (W i).card+1 : ℕ)^2*(J : ℝ)^2*
                      C*(L+P.N^(ε/8)+1)^(1+ε)*d*s^2) ∧
                let S := A.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))
                S ⊆ P.ordinates ∧ S.card = ∑ i ∈ A, (W i).card ∧
                IsSeparated 1 S ∧
                (∀ t ∈ S, P.V ≤ ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n t‖) ∧
                (∀ i ∈ A, ∀ ℓ : ℤ,
                  bourgainDifferenceCount ((P.localized L hL i).retainedOriginal (W i)) ℓ =
                    bourgainDifferenceCount (W i) ℓ) ∧
                (P.ordinates.card : ℝ) ≤
                  (I.card : ℝ)*F+C*P.N^ε*(J : ℝ)*(bourgainRelativeLevelCount P.N τ : ℝ)*
                    (bourgainCorrelationLevelCount P.N B C α τ ε : ℝ)*(S.card : ℝ) ∧
                ((P.ordinates.card : ℝ) ≤ (I.card : ℝ)*F ∨
                  let H := P.N^(ε/8)
                  let U := L+H+1
                  let V := a*(2 : ℝ)^q
                  S.Nonempty ∧
                  ∃ u ∈ Set.Ioc (-H) H,
                    (bourgainIntegerSlice H U V u).Nonempty ∧
                    ∀ E : ℝ, E₀ ≤ E → P.T ≤ E → 2*(U+H) ≤ E →
                    P.V^2*(bourgainEliminatedCardCoefficient P.N L B C τ α ε*
                        ((bourgainIntegerSlice H U V u).card : ℝ)*(S.card : ℝ)+
                      bourgainSliceSqrtCoefficient P.N L B C τ α ε 1*
                        Real.sqrt ((bourgainIntegerSlice H U V u).card : ℝ)*
                          ((S.card : ℝ)^(3/2 : ℝ)/Real.sqrt (I.card : ℝ))) <
                    M*P.N^η*(2*(1+2*Real.pi*P.N^η)*D*E^θ*
                      (Real.sqrt (bourgainSecondBudget P.N E (S.card : ℝ))*
                        Real.sqrt (bourgainSecondBudget P.N E
                          ((bourgainIntegerSlice H U V u).card : ℝ))))) := by
  exact @TaoTrudgianYang2025.bourgain_subdivided_level_free_comparison σ τ η θ hσ hη hθ ε hε

example {N ε : ℝ} (hN : 1 ≤ N) (hε : ε ≤ 8) :
    N^(ε/8) ≤ N := by
  exact @TaoTrudgianYang2025.bourgain_shift_window_le_scale N ε hN hε

example (P : LargeValuePattern)
    {L ε : ℝ} (hNL : P.N ≤ L) (hLT : L ≤ P.T) (hε : ε ≤ 8) :
    2*((L+P.N^(ε/8)+1)+P.N^(ε/8)) ≤ 8*P.T := by
  exact @TaoTrudgianYang2025.bourgain_slice_height_le_original P L ε hNL hLT hε

example {N T R : ℝ}
    (hN : 0 ≤ N) (hR : 0 ≤ R) :
    bourgainSecondBudget N (8*T) R ≤ 3*bourgainSecondBudget N T R := by
  exact @TaoTrudgianYang2025.bourgainSecondBudget_eight_height N T R hN hR

example {θ : ℝ} (hθ : 0 < θ) :
    ∃ D E₀ : ℝ, 0 < D ∧ 1 ≤ E₀ ∧
      ∀ (P : LargeValuePattern) (S : Finset ℝ), S ⊆ P.ordinates →
      ∀ (L ε V u r : ℝ), E₀ ≤ P.N → P.N ≤ L → L ≤ P.T → ε ≤ 8 →
        u ∈ Icc (-(P.N^(ε/8))) (P.N^(ε/8)) → 0 ≤ r →
        (∫ v in -r..r, ∑ t ∈ S,
          ∑ ℓ ∈ bourgainIntegerSlice (P.N^(ε/8)) (L+P.N^(ε/8)+1) V u,
            ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n (t-(ℓ : ℝ)+v)‖^2) ≤
          2*r*D*P.T^θ*
            (Real.sqrt (bourgainSecondBudget P.N P.T (S.card : ℝ))*
              Real.sqrt (bourgainSecondBudget P.N P.T
                ((bourgainIntegerSlice (P.N^(ε/8)) (L+P.N^(ε/8)+1) V u).card : ℝ))) := by
  exact @TaoTrudgianYang2025.bourgain_physical_mixed_upper θ hθ

example {N T R K D r θ : ℝ}
    (hN : 0 ≤ N) (hT : 0 ≤ T) (hR : 0 ≤ R) (hK : 0 ≤ K)
    (hD : 0 ≤ D) (hr : 0 ≤ r) :
    2*r*D*(8*T)^θ*
        (Real.sqrt (bourgainSecondBudget N (8*T) R)*
          Real.sqrt (bourgainSecondBudget N (8*T) K)) ≤
      2*r*(3*D*(8 : ℝ)^θ)*T^θ*
        (Real.sqrt (bourgainSecondBudget N T R)*
          Real.sqrt (bourgainSecondBudget N T K)) := by
  exact @TaoTrudgianYang2025.bourgain_mixed_budget_eight_height N T R K D r θ hN hT hR hK hD hr

example {σ τ η θ : ℝ}
    (hσ : 3/4 < σ) (hη : 0 < η) (hθ : 0 < θ) {ε : ℝ} (hε : 0 < ε) (hε₈ : ε ≤ 8) :
    ∃ B C δ M N₀ D : ℝ,
      0 < B ∧ 2 ≤ C ∧ 0 < δ ∧ δ ≤ 1 ∧ 0 < M ∧ 2 ≤ N₀ ∧ 0 < D ∧
      ∀ (P : LargeValuePattern) (L : ℝ) (hL : 0 < L),
        C ≤ P.N → N₀ ≤ P.N → P.N ≤ L → L ≤ P.T → L ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        ∃ W : ℕ → Finset ℝ,
          (∀ i : ℕ, W i ⊆ (P.localized L hL i).reflectedOrdinates ∧
            IsSeparated 2 (W i) ∧ InBaseInterval L (W i) ∧
            ((P.localized L hL i).ordinates.card : ℝ) ≤ C*P.N^ε*((W i).card : ℝ)) ∧
          ∀ α : ℝ,
            let I := Finset.range (Nat.floor (P.T/L)+1)
            let a := P.N^(-bourgainSharedFloorExponent α τ ε)
            let J := bourgainZetaBandCount B (L+P.N^(ε/8)+1) a
            let F := C*(P.N^(2-2*σ+ε)+P.N^(2*τ+4-8*σ+ε)+
              P.N^(-2*α+τ+12-16*σ+ε))
            ∃ q ∈ Finset.range J, ∃ p ∈ Finset.range (bourgainRelativeLevelCount P.N τ),
              ∃ k ∈ Finset.range (bourgainCorrelationLevelCount P.N B C α τ ε),
              ∃ A : Finset ℕ, A ⊆ I ∧
              ∃ j : ℕ → ℕ,
                (∀ i ∈ A, (F < ((P.localized L hL i).ordinates.card : ℝ) ∧
                  BourgainComponentBand P.N L B C τ α ε (W i) (j i) q ∧
                  (let d := bourgainRelativeLevel P.N τ p
                  0 < d ∧ d ≤ 1 ∧
                  d*((W i).card : ℝ) ≤ (2 : ℝ)^(j i) ∧
                  (2 : ℝ)^(j i) < 2*d*((W i).card : ℝ) ∧
                  (∀ ℓ ∈ bourgainDifferenceLevel (W i) (j i),
                    d*((W i).card : ℝ) ≤ (bourgainDifferenceCount (W i) ℓ : ℝ) ∧
                    (bourgainDifferenceCount (W i) ℓ : ℝ) < 4*d*((W i).card : ℝ)) ∧
                  d*((bourgainDifferenceLevel (W i) (j i)).card : ℝ) ≤ 2*((W i).card : ℝ)) ∧
                  let d := bourgainRelativeLevel P.N τ p
                  let r := bourgainZetaBandCorrelation
                    (bourgainDifferenceLevel (W i) (j i)) (P.N^(ε/8))
                    (L+P.N^(ε/8)+1) (a*(2 : ℝ)^q)
                  P.N^(-2*α)*P.N^τ <
                    1024*(Nat.log 2 (W i).card+1 : ℕ)^2*(J : ℝ)^2*
                      C*(L+P.N^(ε/8)+1)^(1+ε)*d*r^2) ∧
                  (let H := P.N^(ε/8)
                  let U := L+H+1
                  let D := bourgainDifferenceLevel (W i) (j i)
                  let V := a*(2 : ℝ)^q
                  let r := bourgainZetaBandCorrelation D H U V
                  let μ := volume.real (bourgainZetaBand U V)
                  let s := bourgainCorrelationLevel P.N B C α τ ε k
                  0 < s ∧ s ≤ r ∧ r < 2*s ∧ s ≤ 4*H ∧
                  s*Real.sqrt μ*Real.sqrt (D.card : ℝ) ≤ bourgainZetaBandMass D H U V ∧
                  bourgainZetaBandMass D H U V < 2*s*Real.sqrt μ*Real.sqrt (D.card : ℝ)) ∧
                  let d := bourgainRelativeLevel P.N τ p
                  let s := bourgainCorrelationLevel P.N B C α τ ε k
                  P.N^(-2*α)*P.N^τ <
                    4096*(Nat.log 2 (W i).card+1 : ℕ)^2*(J : ℝ)^2*
                      C*(L+P.N^(ε/8)+1)^(1+ε)*d*s^2) ∧
                let S := A.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))
                S ⊆ P.ordinates ∧ S.card = ∑ i ∈ A, (W i).card ∧
                IsSeparated 1 S ∧
                (∀ t ∈ S, P.V ≤ ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n t‖) ∧
                (∀ i ∈ A, ∀ ℓ : ℤ,
                  bourgainDifferenceCount ((P.localized L hL i).retainedOriginal (W i)) ℓ =
                    bourgainDifferenceCount (W i) ℓ) ∧
                (P.ordinates.card : ℝ) ≤
                  (I.card : ℝ)*F+C*P.N^ε*(J : ℝ)*(bourgainRelativeLevelCount P.N τ : ℝ)*
                    (bourgainCorrelationLevelCount P.N B C α τ ε : ℝ)*(S.card : ℝ) ∧
                ((P.ordinates.card : ℝ) ≤ (I.card : ℝ)*F ∨
                  let H := P.N^(ε/8)
                  let U := L+H+1
                  let V := a*(2 : ℝ)^q
                  S.Nonempty ∧
                  ∃ u ∈ Set.Ioc (-H) H,
                    (bourgainIntegerSlice H U V u).Nonempty ∧
                    P.V^2*(bourgainEliminatedCardCoefficient P.N L B C τ α ε*
                        ((bourgainIntegerSlice H U V u).card : ℝ)*(S.card : ℝ)+
                      bourgainSliceSqrtCoefficient P.N L B C τ α ε 1*
                        Real.sqrt ((bourgainIntegerSlice H U V u).card : ℝ)*
                          ((S.card : ℝ)^(3/2 : ℝ)/Real.sqrt (I.card : ℝ))) <
                    M*P.N^η*(2*(1+2*Real.pi*P.N^η)*D*P.T^θ*
                      (Real.sqrt (bourgainSecondBudget P.N P.T (S.card : ℝ))*
                        Real.sqrt (bourgainSecondBudget P.N P.T
                          ((bourgainIntegerSlice H U V u).card : ℝ))))) := by
  exact @TaoTrudgianYang2025.bourgain_subdivided_physical_comparison σ τ η θ hσ hη hθ ε hε hε₈

example {σ τ : ℝ}
    (hσ : 3/4 < σ)
    (hlower : 16*σ-11 ≤ τ) (hupper : 20*σ+τ/3 ≤ 16) :
    0 ≤ max 0 (4*σ+4*τ/3-5) ∧
      1 < τ-max 0 (4*σ+4*τ/3-5) := by
  exact @TaoTrudgianYang2025.bourgain_ninth_row_local_height_margin σ τ hσ hlower hupper

example {N T τ a δ : ℝ}
    (hN : 1 < N) (ha : 0 ≤ a)
    (hmargin : 1+δ ≤ τ-a)
    (hTlo : N^(τ-δ) ≤ T) (hThi : T ≤ N^(τ+δ)) :
    0 < T/N^a ∧ N ≤ T/N^a ∧ T/N^a ≤ T ∧
      N^((τ-a)-δ) ≤ T/N^a ∧ T/N^a ≤ N^((τ-a)+δ) := by
  exact @TaoTrudgianYang2025.bourgain_subdivision_physical_scales N T τ a δ hN ha hmargin hTlo hThi

example {N T a : ℝ}
    (hN : 1 ≤ N) (hT : 0 < T) (ha : 0 ≤ a) :
    ((Finset.range (Nat.floor (T/(T/N^a))+1)).card : ℝ) ≤ 2*N^a := by
  exact @TaoTrudgianYang2025.bourgain_subdivision_bin_count N T a hN hT ha

example {σ τ χ η θ : ℝ}
    (hσ : 3/4 < σ) (hχ : 0 ≤ χ) (hmargin : 1 < τ-χ)
    (hη : 0 < η) (hθ : 0 < θ) {ε : ℝ} (hε : 0 < ε) (hε₈ : ε ≤ 8) :
    ∃ B C δ M N₀ D : ℝ,
      0 < B ∧ 2 ≤ C ∧ 0 < δ ∧ δ ≤ 1 ∧ δ ≤ (τ-χ-1)/2 ∧ 0 < M ∧ 2 ≤ N₀ ∧ 0 < D ∧
      ∀ (P : LargeValuePattern) (L : ℝ) (hL : 0 < L),
        C ≤ P.N → N₀ ≤ P.N → L = P.T/P.N^χ →
        P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        ((Finset.range (Nat.floor (P.T/L)+1)).card : ℝ) ≤ 2*P.N^χ ∧
        ∃ W : ℕ → Finset ℝ,
          (∀ i : ℕ, W i ⊆ (P.localized L hL i).reflectedOrdinates ∧
            IsSeparated 2 (W i) ∧ InBaseInterval L (W i) ∧
            ((P.localized L hL i).ordinates.card : ℝ) ≤ C*P.N^ε*((W i).card : ℝ)) ∧
          ∀ α : ℝ,
            let I := Finset.range (Nat.floor (P.T/L)+1)
            let a := P.N^(-bourgainSharedFloorExponent α (τ-χ) ε)
            let J := bourgainZetaBandCount B (L+P.N^(ε/8)+1) a
            let F := C*(P.N^(2-2*σ+ε)+P.N^(2*(τ-χ)+4-8*σ+ε)+
              P.N^(-2*α+(τ-χ)+12-16*σ+ε))
            ∃ q ∈ Finset.range J, ∃ p ∈ Finset.range (bourgainRelativeLevelCount P.N (τ-χ)),
              ∃ k ∈ Finset.range (bourgainCorrelationLevelCount P.N B C α (τ-χ) ε),
              ∃ A : Finset ℕ, A ⊆ I ∧
              ∃ j : ℕ → ℕ,
                (∀ i ∈ A, (F < ((P.localized L hL i).ordinates.card : ℝ) ∧
                  BourgainComponentBand P.N L B C (τ-χ) α ε (W i) (j i) q ∧
                  (let d := bourgainRelativeLevel P.N (τ-χ) p
                  0 < d ∧ d ≤ 1 ∧
                  d*((W i).card : ℝ) ≤ (2 : ℝ)^(j i) ∧
                  (2 : ℝ)^(j i) < 2*d*((W i).card : ℝ) ∧
                  (∀ ℓ ∈ bourgainDifferenceLevel (W i) (j i),
                    d*((W i).card : ℝ) ≤ (bourgainDifferenceCount (W i) ℓ : ℝ) ∧
                    (bourgainDifferenceCount (W i) ℓ : ℝ) < 4*d*((W i).card : ℝ)) ∧
                  d*((bourgainDifferenceLevel (W i) (j i)).card : ℝ) ≤ 2*((W i).card : ℝ)) ∧
                  let d := bourgainRelativeLevel P.N (τ-χ) p
                  let r := bourgainZetaBandCorrelation
                    (bourgainDifferenceLevel (W i) (j i)) (P.N^(ε/8))
                    (L+P.N^(ε/8)+1) (a*(2 : ℝ)^q)
                  P.N^(-2*α)*P.N^(τ-χ) <
                    1024*(Nat.log 2 (W i).card+1 : ℕ)^2*(J : ℝ)^2*
                      C*(L+P.N^(ε/8)+1)^(1+ε)*d*r^2) ∧
                  (let H := P.N^(ε/8)
                  let U := L+H+1
                  let D := bourgainDifferenceLevel (W i) (j i)
                  let V := a*(2 : ℝ)^q
                  let r := bourgainZetaBandCorrelation D H U V
                  let μ := volume.real (bourgainZetaBand U V)
                  let s := bourgainCorrelationLevel P.N B C α (τ-χ) ε k
                  0 < s ∧ s ≤ r ∧ r < 2*s ∧ s ≤ 4*H ∧
                  s*Real.sqrt μ*Real.sqrt (D.card : ℝ) ≤ bourgainZetaBandMass D H U V ∧
                  bourgainZetaBandMass D H U V < 2*s*Real.sqrt μ*Real.sqrt (D.card : ℝ)) ∧
                  let d := bourgainRelativeLevel P.N (τ-χ) p
                  let s := bourgainCorrelationLevel P.N B C α (τ-χ) ε k
                  P.N^(-2*α)*P.N^(τ-χ) <
                    4096*(Nat.log 2 (W i).card+1 : ℕ)^2*(J : ℝ)^2*
                      C*(L+P.N^(ε/8)+1)^(1+ε)*d*s^2) ∧
                let S := A.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))
                S ⊆ P.ordinates ∧ S.card = ∑ i ∈ A, (W i).card ∧
                IsSeparated 1 S ∧
                (∀ t ∈ S, P.V ≤ ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n t‖) ∧
                (∀ i ∈ A, ∀ ℓ : ℤ,
                  bourgainDifferenceCount ((P.localized L hL i).retainedOriginal (W i)) ℓ =
                    bourgainDifferenceCount (W i) ℓ) ∧
                (P.ordinates.card : ℝ) ≤
                  (I.card : ℝ)*F+C*P.N^ε*(J : ℝ)*(bourgainRelativeLevelCount P.N (τ-χ) : ℝ)*
                    (bourgainCorrelationLevelCount P.N B C α (τ-χ) ε : ℝ)*(S.card : ℝ) ∧
                ((P.ordinates.card : ℝ) ≤ (I.card : ℝ)*F ∨
                  let H := P.N^(ε/8)
                  let U := L+H+1
                  let V := a*(2 : ℝ)^q
                  S.Nonempty ∧
                  ∃ u ∈ Set.Ioc (-H) H,
                    (bourgainIntegerSlice H U V u).Nonempty ∧
                    P.V^2*(bourgainEliminatedCardCoefficient P.N L B C (τ-χ) α ε*
                        ((bourgainIntegerSlice H U V u).card : ℝ)*(S.card : ℝ)+
                      bourgainSliceSqrtCoefficient P.N L B C (τ-χ) α ε 1*
                        Real.sqrt ((bourgainIntegerSlice H U V u).card : ℝ)*
                          ((S.card : ℝ)^(3/2 : ℝ)/Real.sqrt (I.card : ℝ))) <
                    M*P.N^η*(2*(1+2*Real.pi*P.N^η)*D*P.T^θ*
                      (Real.sqrt (bourgainSecondBudget P.N P.T (S.card : ℝ))*
                        Real.sqrt (bourgainSecondBudget P.N P.T
                          ((bourgainIntegerSlice H U V u).card : ℝ))))) := by
  exact @TaoTrudgianYang2025.bourgain_linked_subdivision_comparison σ τ χ η θ hσ hχ hmargin hη hθ ε hε hε₈

example {σ τ η θ : ℝ}
    (hσ : 3/4 < σ) (hlower : 16*σ-11 ≤ τ) (hupper : 20*σ+τ/3 ≤ 16)
    (hη : 0 < η) (hθ : 0 < θ) {ε : ℝ} (hε : 0 < ε) (hε₈ : ε ≤ 8) :
    ∃ B C δ M N₀ D : ℝ,
      0 < B ∧ 2 ≤ C ∧ 0 < δ ∧ δ ≤ 1 ∧ δ ≤ (τ-(max 0 (4*σ+4*τ/3-5))-1)/2 ∧ 0 < M ∧ 2 ≤ N₀ ∧ 0 < D ∧
      ∀ (P : LargeValuePattern) (L : ℝ) (hL : 0 < L),
        C ≤ P.N → N₀ ≤ P.N → L = P.T/P.N^(max 0 (4*σ+4*τ/3-5)) →
        P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        ((Finset.range (Nat.floor (P.T/L)+1)).card : ℝ) ≤ 2*P.N^(max 0 (4*σ+4*τ/3-5)) ∧
        ∃ W : ℕ → Finset ℝ,
          (∀ i : ℕ, W i ⊆ (P.localized L hL i).reflectedOrdinates ∧
            IsSeparated 2 (W i) ∧ InBaseInterval L (W i) ∧
            ((P.localized L hL i).ordinates.card : ℝ) ≤ C*P.N^ε*((W i).card : ℝ)) ∧
          ∀ α : ℝ,
            let I := Finset.range (Nat.floor (P.T/L)+1)
            let a := P.N^(-bourgainSharedFloorExponent α (τ-(max 0 (4*σ+4*τ/3-5))) ε)
            let J := bourgainZetaBandCount B (L+P.N^(ε/8)+1) a
            let F := C*(P.N^(2-2*σ+ε)+P.N^(2*(τ-(max 0 (4*σ+4*τ/3-5)))+4-8*σ+ε)+
              P.N^(-2*α+(τ-(max 0 (4*σ+4*τ/3-5)))+12-16*σ+ε))
            ∃ q ∈ Finset.range J, ∃ p ∈ Finset.range (bourgainRelativeLevelCount P.N (τ-(max 0 (4*σ+4*τ/3-5)))),
              ∃ k ∈ Finset.range (bourgainCorrelationLevelCount P.N B C α (τ-(max 0 (4*σ+4*τ/3-5))) ε),
              ∃ A : Finset ℕ, A ⊆ I ∧
              ∃ j : ℕ → ℕ,
                (∀ i ∈ A, (F < ((P.localized L hL i).ordinates.card : ℝ) ∧
                  BourgainComponentBand P.N L B C (τ-(max 0 (4*σ+4*τ/3-5))) α ε (W i) (j i) q ∧
                  (let d := bourgainRelativeLevel P.N (τ-(max 0 (4*σ+4*τ/3-5))) p
                  0 < d ∧ d ≤ 1 ∧
                  d*((W i).card : ℝ) ≤ (2 : ℝ)^(j i) ∧
                  (2 : ℝ)^(j i) < 2*d*((W i).card : ℝ) ∧
                  (∀ ℓ ∈ bourgainDifferenceLevel (W i) (j i),
                    d*((W i).card : ℝ) ≤ (bourgainDifferenceCount (W i) ℓ : ℝ) ∧
                    (bourgainDifferenceCount (W i) ℓ : ℝ) < 4*d*((W i).card : ℝ)) ∧
                  d*((bourgainDifferenceLevel (W i) (j i)).card : ℝ) ≤ 2*((W i).card : ℝ)) ∧
                  let d := bourgainRelativeLevel P.N (τ-(max 0 (4*σ+4*τ/3-5))) p
                  let r := bourgainZetaBandCorrelation
                    (bourgainDifferenceLevel (W i) (j i)) (P.N^(ε/8))
                    (L+P.N^(ε/8)+1) (a*(2 : ℝ)^q)
                  P.N^(-2*α)*P.N^(τ-(max 0 (4*σ+4*τ/3-5))) <
                    1024*(Nat.log 2 (W i).card+1 : ℕ)^2*(J : ℝ)^2*
                      C*(L+P.N^(ε/8)+1)^(1+ε)*d*r^2) ∧
                  (let H := P.N^(ε/8)
                  let U := L+H+1
                  let D := bourgainDifferenceLevel (W i) (j i)
                  let V := a*(2 : ℝ)^q
                  let r := bourgainZetaBandCorrelation D H U V
                  let μ := volume.real (bourgainZetaBand U V)
                  let s := bourgainCorrelationLevel P.N B C α (τ-(max 0 (4*σ+4*τ/3-5))) ε k
                  0 < s ∧ s ≤ r ∧ r < 2*s ∧ s ≤ 4*H ∧
                  s*Real.sqrt μ*Real.sqrt (D.card : ℝ) ≤ bourgainZetaBandMass D H U V ∧
                  bourgainZetaBandMass D H U V < 2*s*Real.sqrt μ*Real.sqrt (D.card : ℝ)) ∧
                  let d := bourgainRelativeLevel P.N (τ-(max 0 (4*σ+4*τ/3-5))) p
                  let s := bourgainCorrelationLevel P.N B C α (τ-(max 0 (4*σ+4*τ/3-5))) ε k
                  P.N^(-2*α)*P.N^(τ-(max 0 (4*σ+4*τ/3-5))) <
                    4096*(Nat.log 2 (W i).card+1 : ℕ)^2*(J : ℝ)^2*
                      C*(L+P.N^(ε/8)+1)^(1+ε)*d*s^2) ∧
                let S := A.biUnion (fun i => (P.localized L hL i).retainedOriginal (W i))
                S ⊆ P.ordinates ∧ S.card = ∑ i ∈ A, (W i).card ∧
                IsSeparated 1 S ∧
                (∀ t ∈ S, P.V ≤ ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n t‖) ∧
                (∀ i ∈ A, ∀ ℓ : ℤ,
                  bourgainDifferenceCount ((P.localized L hL i).retainedOriginal (W i)) ℓ =
                    bourgainDifferenceCount (W i) ℓ) ∧
                (P.ordinates.card : ℝ) ≤
                  (I.card : ℝ)*F+C*P.N^ε*(J : ℝ)*(bourgainRelativeLevelCount P.N (τ-(max 0 (4*σ+4*τ/3-5))) : ℝ)*
                    (bourgainCorrelationLevelCount P.N B C α (τ-(max 0 (4*σ+4*τ/3-5))) ε : ℝ)*(S.card : ℝ) ∧
                ((P.ordinates.card : ℝ) ≤ (I.card : ℝ)*F ∨
                  let H := P.N^(ε/8)
                  let U := L+H+1
                  let V := a*(2 : ℝ)^q
                  S.Nonempty ∧
                  ∃ u ∈ Set.Ioc (-H) H,
                    (bourgainIntegerSlice H U V u).Nonempty ∧
                    P.V^2*(bourgainEliminatedCardCoefficient P.N L B C (τ-(max 0 (4*σ+4*τ/3-5))) α ε*
                        ((bourgainIntegerSlice H U V u).card : ℝ)*(S.card : ℝ)+
                      bourgainSliceSqrtCoefficient P.N L B C (τ-(max 0 (4*σ+4*τ/3-5))) α ε 1*
                        Real.sqrt ((bourgainIntegerSlice H U V u).card : ℝ)*
                          ((S.card : ℝ)^(3/2 : ℝ)/Real.sqrt (I.card : ℝ))) <
                    M*P.N^η*(2*(1+2*Real.pi*P.N^η)*D*P.T^θ*
                      (Real.sqrt (bourgainSecondBudget P.N P.T (S.card : ℝ))*
                        Real.sqrt (bourgainSecondBudget P.N P.T
                          ((bourgainIntegerSlice H U V u).card : ℝ))))) := by
  exact @TaoTrudgianYang2025.bourgain_ninth_row_physical_comparison σ τ η θ hσ hlower hupper hη hθ ε hε hε₈

-- Literal coefficient-one moments, including the diagonal and empty set.
example (P : LargeValuePattern) : bourgainSelfMoment P ∅ = 0 := by
  simp [bourgainSelfMoment]

example (P : LargeValuePattern) (t : ℝ) :
    bourgainSelfMoment P {t} = (P.indices.card : ℝ)^2 := by
  simp [bourgainSelfMoment, dirichletPhase_zero]

example (N H : ℝ) : bourgainSecondBudget N H 0 = 0 := by
  norm_num [bourgainSecondBudget]

example (H R : ℝ) : bourgainSecondBudget 0 H R = 0 := by
  simp [bourgainSecondBudget]

example : bourgainSecondBudget 1 1 1 = 3 := by
  norm_num [bourgainSecondBudget]

-- Negative phase, exact twist and both closed-support endpoints.
example (P : LargeValuePattern) {n : ℕ} (hn : n ∈ P.indices) (t : ℝ) :
    dirichletPhase n t*dirichletPhase n (-t) = 1 := by
  simpa only [add_neg_cancel, dirichletPhase_zero] using
    (P.dirichletPhase_add hn t (-t)).symm

example (P : LargeValuePattern) (t v : ℝ) :
    dirichletPhase P.scale (t+v) = dirichletPhase P.scale t*dirichletPhase P.scale v := by
  apply P.dirichletPhase_add
  rw [P.indices_eq_dyadicInterval]
  exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩

example (P : LargeValuePattern) (t v : ℝ) :
    dirichletPhase (2*P.scale) (t+v) =
      dirichletPhase (2*P.scale) t*dirichletPhase (2*P.scale) v := by
  apply P.dirichletPhase_add
  rw [P.indices_eq_dyadicInterval]
  exact Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩

-- The cancellation only needs nonzero multiplicity, not a stronger sign assumption.
example (N L B C τ α ε : ℝ) :
    (-2 : ℝ)*bourgainSliceSqrtCoefficient N L B C τ α ε (-2) =
      bourgainSliceSqrtCoefficient N L B C τ α ε 1 := by
  exact bourgain_slice_sqrt_coefficient_cancel _ _ _ _ _ _ _ _ (by norm_num)

-- Literal closed count: with no subdivision, floor(T/T)+1 is two, not one.
example {T : ℝ} (hT : 0 < T) :
    ((Finset.range (Nat.floor (T/(T/(1 : ℝ)^0))+1)).card : ℝ) = 2 := by
  norm_num [div_self hT.ne']

example {N : ℝ} (hN : 1 ≤ N) : N^((8 : ℝ)/8) ≤ N := by
  exact bourgain_shift_window_le_scale hN le_rfl

example : (max 0 (4*(31/40 : ℝ)+4*(3/2)/3-5)) = 1/10 := by
  norm_num

example :
    1 < (3/2 : ℝ)-max 0 (4*(31/40)+4*(3/2)/3-5) := by
  exact (bourgain_ninth_row_local_height_margin
    (by norm_num : (3/4 : ℝ) < 31/40)
    (by norm_num : 16*(31/40 : ℝ)-11 ≤ 3/2)
    (by norm_num : 20*(31/40 : ℝ)+(3/2)/3 ≤ 16)).2

example : max 0 (4*(84/109 : ℝ)+4*(7/5)/3-5) = 0 := by
  norm_num

end BourgainHeathBrownComparisonRegression

namespace BourgainFiniteLossRegression

open TaoTrudgianYang2025 RiemannZeta.GuthMaynard
open scoped Classical

-- Exact public types, including parameter order and original-object consumers.

example {N L B C τ α ε : ℝ}
    (hN : 1 ≤ N) (hL : 0 < L) (hC : 0 ≤ C) :
    (bourgainSliceSqrtCoefficient N L B C τ α ε 1)^2 =
      bourgainEliminatedCardCoefficient N L B C τ α ε := by
  exact @TaoTrudgianYang2025.bourgain_slice_sqrt_coefficient_sq N L B C τ α ε hN hL hC

example {N L B C τ α ε : ℝ}
    (hN : 1 ≤ N) (hL : 0 < L) (hC : 0 ≤ C) :
    bourgainSliceSqrtCoefficient N L B C τ α ε 1 =
      Real.sqrt (bourgainEliminatedCardCoefficient N L B C τ α ε) := by
  exact @TaoTrudgianYang2025.bourgain_slice_sqrt_coefficient_eq_sqrt N L B C τ α ε hN hL hC

example {τ η : ℝ} (hη : 0 < η) :
    ∃ D N₀ : ℝ, 1 ≤ D ∧ 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      bourgainDifferenceLogLoss N τ ≤ D*N^η := by
  exact @TaoTrudgianYang2025.bourgainDifferenceLogLoss_uniform_power τ η hη

example {B α τ ε η : ℝ}
    (hB : 0 < B) (hε : 0 ≤ ε) (hη : 0 < η) :
    ∃ D N₀ : ℝ, 1 ≤ D ∧ 2 ≤ N₀ ∧ ∀ N L δ : ℝ,
      N₀ ≤ N → 0 ≤ L → δ ≤ 1 → L ≤ N^(τ+δ) →
      bourgainDifferenceLogLoss N τ*
        (bourgainZetaBandCount B (L+N^(ε/8)+1)
          (N^(-bourgainSharedFloorExponent α τ ε)) : ℝ) ≤ D*N^η := by
  exact @TaoTrudgianYang2025.bourgain_comparison_logs_uniform_power B α τ ε η hB hε hη

example {N ε : ℝ}
    (hN : 1 ≤ N) (hε : 0 ≤ ε) :
    N^(ε/8)*((2*Nat.ceil (N^(ε/8))+1 : ℕ) : ℝ) ≤ 5*N^(ε/4) := by
  exact @TaoTrudgianYang2025.bourgain_window_ceiling_product N ε hN hε

example {N L τ ε δ : ℝ}
    (hN : 1 ≤ N) (hNL : N ≤ L) (hε : 0 ≤ ε) (hε₈ : ε ≤ 8)
    (hL : L ≤ N^(τ+δ)) :
    (L+N^(ε/8)+1)^(1+ε) ≤ (3 : ℝ)^(1+ε)*N^((τ+δ)*(1+ε)) := by
  exact @TaoTrudgianYang2025.bourgain_local_height_power N L τ ε δ hN hNL hε hε₈ hL

example {B C α τ ε η : ℝ}
    (hB : 0 < B) (hC : 0 < C) (hε : 0 ≤ ε) (hε₈ : ε ≤ 8) (hη : 0 < η) :
    ∃ G N₀ : ℝ, 0 < G ∧ 2 ≤ N₀ ∧ ∀ N L δ : ℝ,
      N₀ ≤ N → N ≤ L → δ ≤ 1 → L ≤ N^(τ+δ) →
      N^(-2*α-bourgainComparisonLoss τ ε δ η)/G ≤
        bourgainEliminatedCardCoefficient N L B C τ α ε ∧
      N^(-α-bourgainComparisonLoss τ ε δ η/2)/Real.sqrt G ≤
        bourgainSliceSqrtCoefficient N L B C τ α ε 1 := by
  exact @TaoTrudgianYang2025.bourgain_comparison_coefficients_uniform_power B C α τ ε η hB hC hε hε₈ hη

example {N G α E χ b m : ℝ}
    (hN : 0 < N) (hG : 0 < G) (hm : 0 < m) (hbin : m ≤ 2*N^χ)
    (hb : N^(-α-E/2)/Real.sqrt G ≤ b) :
    N^(-α-E/2-χ/2)/Real.sqrt (2*G) ≤ b/Real.sqrt m := by
  exact @TaoTrudgianYang2025.bourgain_sqrt_bin_coefficient N G α E χ b m hN hG hm hbin hb

example {N T τ δ η θ M D : ℝ}
    (hN : 1 ≤ N) (hT : 0 ≤ T) (hη : 0 ≤ η) (hθ : 0 ≤ θ)
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hcap : T ≤ N^(τ+δ)) :
    M*N^η*(2*(1+2*Real.pi*N^η)*D*T^θ) ≤
      (2*M*(1+2*Real.pi)*D)*N^(2*η+(τ+δ)*θ) := by
  exact @TaoTrudgianYang2025.bourgain_integration_power_factor N T τ δ η θ M D hN hT hη hθ hM hD hcap

example {τ ε δ η z : ℝ}
    (hε : 0 ≤ ε) (hδ : δ ≤ 1)
    (hwindow : ε ≤ z/(4*(|τ|+2)))
    (hlog : η ≤ z/4) (hheight : δ ≤ z/4) :
    bourgainComparisonLoss τ ε δ η ≤ z := by
  exact @TaoTrudgianYang2025.bourgain_comparison_loss_small τ ε δ η z hε hδ hwindow hlog hheight

example {σ τ χ α η θ κ ζ : ℝ}
    (hσ : 3/4 < σ) (hχ : 0 ≤ χ) (hmargin : 1 < τ-χ)
    (hη : 0 < η) (hθ : 0 < θ) (hκ : 0 < κ) (hζ : 0 < ζ)
    {ε : ℝ} (hε : 0 < ε) (hε₈ : ε ≤ 8) :
    ∃ B C δ K G H N₀ : ℝ,
      0 < B ∧ 2 ≤ C ∧ 0 < δ ∧ δ ≤ 1 ∧ δ ≤ (τ-χ-1)/2 ∧
      δ ≤ ζ ∧ 0 < K ∧ 0 < G ∧ 1 ≤ H ∧ 2 ≤ N₀ ∧
      ∀ (P : LargeValuePattern) (L : ℝ),
        C ≤ P.N → N₀ ≤ P.N → L = P.T/P.N^χ →
        P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        let a := P.N^(-bourgainSharedFloorExponent α (τ-χ) ε)
        let J := bourgainZetaBandCount B (L+P.N^(ε/8)+1) a
        let F := C*(P.N^(2-2*σ+ε)+P.N^(2*(τ-χ)+4-8*σ+ε)+
          P.N^(-2*α+(τ-χ)+12-16*σ+ε))
        let E := bourgainComparisonLoss (τ-χ) ε δ κ
        ∃ S : Finset ℝ, S ⊆ P.ordinates ∧ IsSeparated 1 S ∧
          (∀ t ∈ S, P.V ≤ ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n t‖) ∧
          (P.ordinates.card : ℝ) ≤ 2*P.N^χ*F+C*H*P.N^(ε+κ)*(S.card : ℝ) ∧
          ((P.ordinates.card : ℝ) ≤ 2*P.N^χ*F ∨
            S.Nonempty ∧ ∃ q ∈ Finset.range J, ∃ u ∈ Set.Ioc (-(P.N^(ε/8))) (P.N^(ε/8)),
              (bourgainIntegerSlice (P.N^(ε/8)) (L+P.N^(ε/8)+1) (a*(2 : ℝ)^q) u).Nonempty ∧
              let x := ((bourgainIntegerSlice (P.N^(ε/8)) (L+P.N^(ε/8)+1)
                (a*(2 : ℝ)^q) u).card : ℝ)
              P.N^(2*σ-2*δ)*
                (P.N^(-2*α-E)/G*x*(S.card : ℝ)+
                  P.N^(-α-E/2-χ/2)/Real.sqrt (2*G)*
                    Real.sqrt x*(S.card : ℝ)^(3/2 : ℝ)) <
                K*P.N^(2*η+(τ+δ)*θ)*
                  (Real.sqrt (bourgainSecondBudget P.N P.T (S.card : ℝ))*
                    Real.sqrt (bourgainSecondBudget P.N P.T x))) := by
  exact @TaoTrudgianYang2025.bourgain_linked_power_loss_comparison σ τ χ α η θ κ ζ hσ hχ hmargin hη hθ hκ hζ ε hε hε₈

-- The square identity also covers the zero moment constant; no division
-- cancellation silently adds a nonzero hypothesis.
example {N L B τ α ε : ℝ} (hN : 1 ≤ N) (hL : 0 < L) :
    (bourgainSliceSqrtCoefficient N L B 0 τ α ε 1)^2 =
      bourgainEliminatedCardCoefficient N L B 0 τ α ε := by
  exact bourgain_slice_sqrt_coefficient_sq hN hL le_rfl

example (N L B τ α ε : ℝ) :
    bourgainEliminatedCardCoefficient N L B 0 τ α ε = 0 := by
  simp [bourgainEliminatedCardCoefficient]

example (N L B τ α ε : ℝ) :
    bourgainSliceSqrtCoefficient N L B 0 τ α ε 1 = 0 := by
  simp [bourgainSliceSqrtCoefficient, bourgainMassCoefficient]

example (τ : ℝ) : bourgainDifferenceLogLoss 1 τ = 3 := by
  simp [bourgainDifferenceLogLoss]

example : (1 : ℝ)^((0 : ℝ)/8)*
    ((2*Nat.ceil ((1 : ℝ)^((0 : ℝ)/8))+1 : ℕ) : ℝ) = 3 := by
  norm_num

example {N : ℝ} (hN : 1 ≤ N) :
    N^((8 : ℝ)/8)*((2*Nat.ceil (N^((8 : ℝ)/8))+1 : ℕ) : ℝ) ≤ 5*N^((8 : ℝ)/4) := by
  exact bourgain_window_ceiling_product hN (by norm_num)

example (τ : ℝ) : bourgainComparisonLoss τ 0 0 0 = 0 := by
  simp [bourgainComparisonLoss]

example : bourgainComparisonLoss (7/5) (1/100) (1/100) (1/100) = 183/5000 := by
  norm_num [bourgainComparisonLoss]

example :
    bourgainComparisonLoss (7/5) (1/100) (1/100) (1/100) ≤ 1 := by
  exact bourgain_comparison_loss_small (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end BourgainFiniteLossRegression

namespace BourgainLogarithmicComparisonRegression

open TaoTrudgianYang2025 RiemannZeta.GuthMaynard Set Filter Topology
open scoped Classical

-- Exact public signatures, including the nonempty source and linked actual coordinates.

example {H T V u : ℝ}
    (hsize : 0 ≤ T+H) (hu : u ∈ Icc (-H) H) :
    ((bourgainIntegerSlice H T V u).card : ℝ) ≤ 2*(T+H)+1 := by
  exact @TaoTrudgianYang2025.bourgain_integer_slice_card_le H T V u hsize hu

example {N L τ ε δ V u : ℝ}
    (hN : 1 ≤ N) (hNL : N ≤ L) (hε₈ : ε ≤ 8)
    (hL : L ≤ N^(τ+δ)) (hu : u ∈ Icc (-(N^(ε/8))) (N^(ε/8))) :
    ((bourgainIntegerSlice (N^(ε/8)) (L+N^(ε/8)+1) V u).card : ℝ) ≤
      9*N^(τ+δ) := by
  exact @TaoTrudgianYang2025.bourgain_local_slice_card_power N L τ ε δ V u hN hNL hε₈ hL hu

example {ι : Type*} (W : Finset ι)
    {N : ℝ} (hN : 1 < N) (hW : W.Nonempty) :
    0 ≤ Real.logb N (W.card : ℝ) := by
  exact @TaoTrudgianYang2025.bourgain_nonempty_log_card_nonneg ι W N hN hW

example {N L τ ε δ V u : ℝ}
    (hN : 1 < N) (hNL : N ≤ L) (hε₈ : ε ≤ 8)
    (hL : L ≤ N^(τ+δ)) (hu : u ∈ Icc (-(N^(ε/8))) (N^(ε/8)))
    (hW : (bourgainIntegerSlice (N^(ε/8)) (L+N^(ε/8)+1) V u).Nonempty) :
    0 ≤ Real.logb N ((bourgainIntegerSlice (N^(ε/8)) (L+N^(ε/8)+1) V u).card : ℝ) ∧
      Real.logb N ((bourgainIntegerSlice (N^(ε/8)) (L+N^(ε/8)+1) V u).card : ℝ) ≤
        τ+δ+Real.logb N 9 := by
  exact @TaoTrudgianYang2025.bourgain_local_slice_log_card_bounds N L τ ε δ V u hN hNL hε₈ hL hu hW

example (P : LargeValuePattern) (S : Finset ℝ)
    (hsub : S ⊆ P.ordinates) (hS : S.Nonempty) {τ δ : ℝ}
    (hone : 1 ≤ P.N^(τ+δ)) (hT : P.T ≤ P.N^(τ+δ)) :
    0 ≤ Real.logb P.N (S.card : ℝ) ∧
      Real.logb P.N (S.card : ℝ) ≤ τ+δ+Real.logb P.N 2 := by
  exact @TaoTrudgianYang2025.bourgain_source_log_card_bounds P S hsub hS τ δ hone hT

example {N T R : ℝ}
    (hN : 0 < N) (hT : 0 ≤ T) (hR : 0 < R) :
    0 < bourgainSecondBudget N T R := by
  exact @TaoTrudgianYang2025.bourgainSecondBudget_pos N T R hN hT hR

example {N T τ r : ℝ}
    (hN : 1 ≤ N) (hT : 0 ≤ T) (hcap : T ≤ N^τ) :
    bourgainSecondBudget N T (N^r) ≤ 3*N^(heathBrownDoubleZetaExponent τ r) := by
  exact @TaoTrudgianYang2025.bourgain_budget_at_power N T τ r hN hT hcap

example {N T R τ : ℝ}
    (hN : 1 < N) (hT : 0 ≤ T) (hR : 0 < R) (hcap : T ≤ N^τ) :
    Real.logb N (bourgainSecondBudget N T R) ≤
      Real.logb N 3+heathBrownDoubleZetaExponent τ (Real.logb N R) := by
  exact @TaoTrudgianYang2025.bourgain_budget_log_bound N T R τ hN hT hR hcap

example {τ r δ : ℝ} (hδ : 0 ≤ δ) :
    heathBrownDoubleZetaExponent (τ+δ) r ≤ heathBrownDoubleZetaExponent τ r+δ/2 := by
  exact @TaoTrudgianYang2025.bourgain_doubleZeta_height_slack τ r δ hδ

example :
    Continuous (fun p : ℝ × ℝ => heathBrownDoubleZetaExponent p.1 p.2) := by
  exact @TaoTrudgianYang2025.bourgain_doubleZeta_exponent_continuous

example {N A X R : ℝ}
    (hN : 1 < N) (hA : 0 < A) (hX : 0 < X) (hR : 0 < R) (p q r : ℝ) :
    Real.logb N (N^p/A*X^q*R^r) =
      p-Real.logb N A+q*Real.logb N X+r*Real.logb N R := by
  exact @TaoTrudgianYang2025.bourgain_logb_monomial N A X R hN hA hX hR p q r

example {N T R X K τ : ℝ}
    (hN : 1 < N) (hT : 0 ≤ T) (hR : 0 < R) (hX : 0 < X) (hK : 0 < K)
    (hcap : T ≤ N^τ) (a : ℝ) :
    Real.logb N (K*N^a*
      (Real.sqrt (bourgainSecondBudget N T R)*Real.sqrt (bourgainSecondBudget N T X))) ≤
      Real.logb N (3*K)+a+
        heathBrownDoubleZetaExponent τ (Real.logb N R)/2+
        heathBrownDoubleZetaExponent τ (Real.logb N X)/2 := by
  exact @TaoTrudgianYang2025.bourgain_mixed_budget_log_bound N T R X K τ hN hT hR hX hK hcap a

example {N T R X K G σ τ δ α χ E a : ℝ}
    (hN : 1 < N) (hT : 0 ≤ T) (hR : 0 < R) (hX : 0 < X)
    (hK : 0 < K) (hG : 0 < G) (hcap : T ≤ N^τ)
    (hcomp : N^(2*σ-2*δ)*
      (N^(-2*α-E)/G*X*R+
        N^(-α-E/2-χ/2)/Real.sqrt (2*G)*Real.sqrt X*R^(3/2 : ℝ)) <
      K*N^a*(Real.sqrt (bourgainSecondBudget N T R)*Real.sqrt (bourgainSecondBudget N T X))) :
    max (-2*α+2*σ+Real.logb N X+Real.logb N R-E-2*δ-Real.logb N G)
      (-α-χ/2+2*σ+Real.logb N X/2+3*Real.logb N R/2-E/2-2*δ-Real.logb N (2*G)/2) <
      Real.logb N (3*K)+a+
        heathBrownDoubleZetaExponent τ (Real.logb N R)/2+
        heathBrownDoubleZetaExponent τ (Real.logb N X)/2 := by
  exact @TaoTrudgianYang2025.bourgain_finite_comparison_logarithm N T R X K G σ τ δ α χ E a hN hT hR hX hK hG hcap hcomp

example {N C σ τ α χ ε : ℝ}
    (hN : 1 ≤ N) (hC : 0 ≤ C) :
    2*N^χ*(C*(N^(2-2*σ+ε)+N^(2*(τ-χ)+4-8*σ+ε)+
      N^(-2*α+(τ-χ)+12-16*σ+ε))) ≤
      6*C*N^(bourgainSmallExponent σ τ α χ+ε) := by
  exact @TaoTrudgianYang2025.bourgain_small_component_power N C σ τ α χ ε hN hC

example {N A B : ℝ}
    (hN : 1 < N) (hA : 0 < A) (hB : 0 < B) (p q : ℝ) :
    Real.logb N (A*N^p+B*N^q) ≤ Real.logb N (A+B)+max p q := by
  exact @TaoTrudgianYang2025.bourgain_logb_two_power_sum N A B hN hA hB p q

example {N Q R C H σ τ α χ ε κ : ℝ}
    (hN : 1 < N) (hQ : 0 < Q) (hR : 0 < R) (hC : 0 < C) (hH : 0 < H)
    (hpack : Q ≤ 2*N^χ*(C*(N^(2-2*σ+ε)+N^(2*(τ-χ)+4-8*σ+ε)+
      N^(-2*α+(τ-χ)+12-16*σ+ε)))+C*H*N^(ε+κ)*R) :
    Real.logb N Q ≤ Real.logb N (6*C+C*H)+
      max (bourgainSmallExponent σ τ α χ+ε) (ε+κ+Real.logb N R) := by
  exact @TaoTrudgianYang2025.bourgain_original_count_log_bound N Q R C H σ τ α χ ε κ hN hQ hR hC hH hpack

example {N Q C σ τ α χ ε : ℝ}
    (hN : 1 < N) (hQ : 0 < Q) (hC : 0 < C)
    (hsmall : Q ≤ 2*N^χ*(C*(N^(2-2*σ+ε)+N^(2*(τ-χ)+4-8*σ+ε)+
      N^(-2*α+(τ-χ)+12-16*σ+ε)))) :
    Real.logb N Q ≤ bourgainSmallExponent σ τ α χ+ε+Real.logb N (6*C) := by
  exact @TaoTrudgianYang2025.bourgain_small_original_log_bound N Q C σ τ α χ ε hN hQ hC hsmall

example {σ τ χ α η θ κ ζ : ℝ}
    (hσ : 3/4 < σ) (hχ : 0 ≤ χ) (hmargin : 1 < τ-χ)
    (hη : 0 < η) (hθ : 0 < θ) (hκ : 0 < κ) (hζ : 0 < ζ)
    {ε : ℝ} (hε : 0 < ε) (hε₈ : ε ≤ 8) :
    ∃ B C δ K G H N₀ : ℝ,
      0 < B ∧ 2 ≤ C ∧ 0 < δ ∧ δ ≤ 1 ∧ δ ≤ (τ-χ-1)/2 ∧
      δ ≤ ζ ∧ 0 < K ∧ 0 < G ∧ 1 ≤ H ∧ 2 ≤ N₀ ∧
      ∀ (P : LargeValuePattern) (L : ℝ), P.ordinates.Nonempty →
        C ≤ P.N → N₀ ≤ P.N → L = P.T/P.N^χ →
        P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        let ρ := Real.logb P.N (P.ordinates.card : ℝ)
        let E := bourgainComparisonLoss (τ-χ) ε δ κ
        ρ ≤ bourgainSmallExponent σ τ α χ+ε+Real.logb P.N (6*C) ∨
          ∃ S : Finset ℝ, S ⊆ P.ordinates ∧ S.Nonempty ∧ IsSeparated 1 S ∧
            (∀ t ∈ S, P.V ≤ ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n t‖) ∧
            let r := Real.logb P.N (S.card : ℝ)
            0 ≤ r ∧ r ≤ τ+δ+Real.logb P.N 2 ∧
            ρ ≤ Real.logb P.N (6*C+C*H)+
              max (bourgainSmallExponent σ τ α χ+ε) (ε+κ+r) ∧
            let a := P.N^(-bourgainSharedFloorExponent α (τ-χ) ε)
            let J := bourgainZetaBandCount B (L+P.N^(ε/8)+1) a
            ∃ q ∈ Finset.range J, ∃ u ∈ Set.Ioc (-(P.N^(ε/8))) (P.N^(ε/8)),
              (bourgainIntegerSlice (P.N^(ε/8)) (L+P.N^(ε/8)+1) (a*(2 : ℝ)^q) u).Nonempty ∧
              let x := Real.logb P.N ((bourgainIntegerSlice (P.N^(ε/8)) (L+P.N^(ε/8)+1)
                (a*(2 : ℝ)^q) u).card : ℝ)
              0 ≤ x ∧ x ≤ (τ-χ)+δ+Real.logb P.N 9 ∧
              max (-2*α+2*σ+x+r-E-2*δ-Real.logb P.N G)
                (-α-χ/2+2*σ+x/2+3*r/2-E/2-2*δ-Real.logb P.N (2*G)/2) <
                Real.logb P.N (3*K)+(2*η+(τ+δ)*θ)+
                  heathBrownDoubleZetaExponent (τ+δ) r/2+
                  heathBrownDoubleZetaExponent (τ+δ) x/2 := by
  exact @TaoTrudgianYang2025.bourgain_linked_logarithmic_comparison σ τ χ α η θ κ ζ hσ hχ hmargin hη hθ hκ hζ ε hε hε₈

example
    (P : ℕ → LargeValuePattern) (S : ℕ → Finset ℝ)
    (L ε δ V u : ℕ → ℝ) (τ χ : ℝ)
    (hN : ∀ n, 2 ≤ (P n).N)
    (hS : ∀ n, (S n).Nonempty) (hsub : ∀ n, S n ⊆ (P n).ordinates)
    (hNL : ∀ n, (P n).N ≤ L n) (hLT : ∀ n, L n ≤ (P n).T)
    (hT : ∀ n, (P n).T ≤ (P n).N^(τ+δ n))
    (hL : ∀ n, L n ≤ (P n).N^((τ-χ)+δ n))
    (hδ : ∀ n, δ n ≤ 1) (hε : ∀ n, ε n ≤ 8)
    (hu : ∀ n, u n ∈ Icc (-((P n).N^(ε n/8))) ((P n).N^(ε n/8)))
    (hZ : ∀ n, (bourgainIntegerSlice ((P n).N^(ε n/8))
      (L n+(P n).N^(ε n/8)+1) (V n) (u n)).Nonempty) :
    ∃ r x : ℝ, 0 ≤ r ∧ r ≤ τ+2 ∧ 0 ≤ x ∧ x ≤ (τ-χ)+5 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n => Real.logb (P (φ n)).N ((S (φ n)).card : ℝ)) atTop (nhds r) ∧
        Tendsto (fun n => Real.logb (P (φ n)).N
          ((bourgainIntegerSlice ((P (φ n)).N^(ε (φ n)/8))
            (L (φ n)+(P (φ n)).N^(ε (φ n)/8)+1) (V (φ n)) (u (φ n))).card : ℝ))
          atTop (nhds x) := by
  exact @TaoTrudgianYang2025.bourgain_source_slice_log_subsequence P S L ε δ V u τ χ hN hS hsub hNL hLT hT hL hδ hε hu hZ

-- Empty-cardinality logarithms have Mathlib's zero value; source logarithmic
-- theorems deliberately require nonemptiness.
example (N : ℝ) : Real.logb N ((∅ : Finset ℤ).card : ℝ) = 0 := by simp

example (N t : ℝ) : Real.logb N (({t} : Finset ℝ).card : ℝ) = 0 := by simp

example (V : ℝ) : ((bourgainIntegerSlice 0 0 V 0).card : ℝ) ≤ 1 := by
  simpa using bourgain_integer_slice_card_le
    (H := 0) (T := 0) (V := V) (by norm_num) (by norm_num)

example {N V u : ℝ} (hN : 1 ≤ N) (hu : u ∈ Set.Icc (-N) N) :
    ((bourgainIntegerSlice N (N+N+1) V u).card : ℝ) ≤ 9*N := by
  simpa using bourgain_local_slice_card_power
    (N := N) (L := N) (τ := 1) (ε := 8) (δ := 0)
    hN le_rfl le_rfl (by simp) (by simpa using hu)

example : bourgainSecondBudget 1 1 1 = 3 := by
  norm_num [bourgainSecondBudget]

example : heathBrownDoubleZetaExponent 0 0 = 2 := by
  norm_num [heathBrownDoubleZetaExponent]

-- The third Heath--Brown term really can dominate.
example : heathBrownDoubleZetaExponent 4 0 = 3 := by
  norm_num [heathBrownDoubleZetaExponent]

example (τ r : ℝ) :
    heathBrownDoubleZetaExponent (τ+0) r ≤ heathBrownDoubleZetaExponent τ r+0/2 := by
  exact bourgain_doubleZeta_height_slack le_rfl

example :
    bourgainSmallExponent (31/40) (3/2)
      (((3/2)+9-12*(31/40))/6) (max 0 (4*(31/40)+4*(3/2)/3-5)) = 7/10 := by
  norm_num [bourgainSmallExponent]

example {N : ℝ} (hN : 1 < N) (p q : ℝ) :
    Real.logb N (N^p+N^q) ≤ Real.logb N 2+max p q := by
  simpa only [one_mul, show (1 : ℝ)+1 = 2 by norm_num] using bourgain_logb_two_power_sum hN (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1) p q

example (N : ℕ → ℝ)
    (hN : Tendsto N atTop atTop) (C : ℝ) :
    Tendsto (fun n => Real.logb (N n) C) atTop (nhds 0) := by
  exact @TaoTrudgianYang2025.bourgain_tendsto_logb_const N hN C

example {σ τ α χ δ E a r x G K : ℝ}
    (N R X : ℕ → ℝ) (hN : Tendsto N atTop atTop)
    (hr : Tendsto (fun n => Real.logb (N n) (R n)) atTop (nhds r))
    (hx : Tendsto (fun n => Real.logb (N n) (X n)) atTop (nhds x))
    (hcomp : ∀ᶠ n in atTop,
      max (-2*α+2*σ+Real.logb (N n) (X n)+Real.logb (N n) (R n)-E-2*δ-Real.logb (N n) G)
        (-α-χ/2+2*σ+Real.logb (N n) (X n)/2+3*Real.logb (N n) (R n)/2-
          E/2-2*δ-Real.logb (N n) (2*G)/2) ≤
      Real.logb (N n) (3*K)+a+
        heathBrownDoubleZetaExponent τ (Real.logb (N n) (R n))/2+
        heathBrownDoubleZetaExponent τ (Real.logb (N n) (X n))/2) :
    max (-2*α+2*σ+x+r-E-2*δ) (-α-χ/2+2*σ+x/2+3*r/2-E/2-2*δ) ≤
      a+heathBrownDoubleZetaExponent τ r/2+heathBrownDoubleZetaExponent τ x/2 := by
  exact @TaoTrudgianYang2025.bourgain_fixed_logarithmic_limit σ τ α χ δ E a r x G K N R X hN hr hx hcomp

end BourgainLogarithmicComparisonRegression

namespace BourgainSourceDichotomyRegression

open TaoTrudgianYang2025 RiemannZeta.GuthMaynard Set Filter Topology

example {N A ε : ℝ}
    (hN : 1 < N) (hε : 0 < ε)
    (hscale : Real.exp (|Real.log A|/ε+1) ≤ N) :
    |Real.logb N A| ≤ ε := by
  exact @TaoTrudgianYang2025.bourgain_abs_logb_le_of_threshold N A ε hN hε hscale

example {σ τ ρ energy : ℝ}
    (hregion : InCardinalityEnergyRegion σ τ ρ energy)
    (δ C : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) :
    ∃ P : ℕ → LargeValuePattern,
      Tendsto (fun n => (P n).N) atTop atTop ∧
      Tendsto (fun n => Real.logb (P n).N ((P n).ordinates.card : ℝ))
        atTop (nhds ρ) ∧
      ∀ n, 2 ≤ (P n).N ∧ C n ≤ (P n).N ∧
        (P n).N^(τ-δ n) ≤ (P n).T ∧ (P n).T ≤ (P n).N^(τ+δ n) ∧
        (P n).N^(σ-δ n) ≤ (P n).V ∧ (P n).ordinates.Nonempty ∧
        |Real.logb (P n).N ((P n).ordinates.card : ℝ)-ρ| ≤ poweringAccuracy n := by
  exact @TaoTrudgianYang2025.exists_bourgain_region_family σ τ ρ energy hregion δ C hδ

example {m : ℕ}
    (A : Fin m → ℝ) {N ε : ℝ} (hN : 1 < N) (hε : 0 < ε)
    (hscale : (∑ i, Real.exp (|Real.log (A i)|/ε+1)) ≤ N) (i : Fin m) :
    |Real.logb N (A i)| ≤ ε := by
  exact @TaoTrudgianYang2025.bourgain_abs_logb_le_of_sum_threshold m A N ε hN hε hscale i

example {σ τ α χ ε δ r x g g₂ k : ℝ}
    (hlocal : 0 ≤ τ-χ) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hδ : 0 ≤ δ) (hδε : δ ≤ ε)
    (hg : g ≤ ε) (hg₂ : g₂ ≤ ε) (hk : k ≤ ε)
    (hcomp :
      max (-2*α+2*σ+x+r-bourgainComparisonLoss (τ-χ) ε δ ε-2*δ-g)
        (-α-χ/2+2*σ+x/2+3*r/2-bourgainComparisonLoss (τ-χ) ε δ ε/2-2*δ-g₂/2) ≤
      k+(2*ε+(τ+δ)*ε)+heathBrownDoubleZetaExponent (τ+δ) r/2+
        heathBrownDoubleZetaExponent (τ+δ) x/2) :
    max (-2*α+2*σ+x+r) (-α-χ/2+2*σ+x/2+3*r/2) ≤
      (2*τ-χ+12)*ε+heathBrownDoubleZetaExponent τ r/2+
        heathBrownDoubleZetaExponent τ x/2 := by
  exact @TaoTrudgianYang2025.bourgain_diagonal_comparison σ τ α χ ε δ r x g g₂ k hlocal hε hε₁ hδ hδε hg hg₂ hk hcomp

example {σ τ χ α ρ energy : ℝ}
    (hregion : InCardinalityEnergyRegion σ τ ρ energy)
    (hσ : 3/4 < σ) (hχ : 0 ≤ χ) (hmargin : 1 < τ-χ)
    (hgap : bourgainSmallExponent σ τ α χ < ρ) :
    Nonempty (BourgainDiagonalFamily σ τ χ α ρ) := by
  exact @TaoTrudgianYang2025.exists_bourgain_diagonal_family σ τ χ α ρ energy hregion hσ hχ hmargin hgap

example {σ τ χ α ρ : ℝ}
    (F : BourgainDiagonalFamily σ τ χ α ρ) (n : ℕ) :
    Real.logb (F.pattern n).N ((F.retained n).card : ℝ) ≤
      Real.logb (F.pattern n).N ((F.pattern n).ordinates.card : ℝ) := by
  exact @TaoTrudgianYang2025.BourgainDiagonalFamily.retained_log_le σ τ χ α ρ F n

example {σ τ χ α ρ : ℝ}
    (F : BourgainDiagonalFamily σ τ χ α ρ)
    (hgap : bourgainSmallExponent σ τ α χ < ρ) :
    ∃ x : ℝ, 0 ≤ x ∧
      max (-2*α+2*σ+x+ρ) (-α-χ/2+2*σ+x/2+3*ρ/2) ≤
        heathBrownDoubleZetaExponent τ ρ/2+heathBrownDoubleZetaExponent τ x/2 := by
  exact @TaoTrudgianYang2025.BourgainDiagonalFamily.source_witness σ τ χ α ρ F hgap

example
    {σ τ ρ energy χ α : ℝ}
    (hregion : InCardinalityEnergyRegion σ τ ρ energy)
    (hσ : 3/4 < σ) (hχ : 0 ≤ χ) (hmargin : 1 < τ-χ) :
    ρ ≤ bourgainSmallExponent σ τ α χ ∨
      ∃ x : ℝ, 0 ≤ x ∧
        max (-2*α+2*σ+x+ρ) (-α-χ/2+2*σ+x/2+3*ρ/2) ≤
          heathBrownDoubleZetaExponent τ ρ/2+heathBrownDoubleZetaExponent τ x/2 := by
  exact @TaoTrudgianYang2025.InCardinalityEnergyRegion.bourgain_log_dichotomy σ τ ρ energy χ α hregion hσ hχ hmargin

example
    {σ τ ρ energy : ℝ} (h : InCardinalityEnergyRegion σ τ ρ energy)
    (hσ : 3/4 ≤ σ) (hτ : τ ≤ 3/2) : ρ ≤ 1 := by
  exact @TaoTrudgianYang2025.InCardinalityEnergyRegion.bourgain_cardinality_le_one σ τ ρ energy h hσ hτ

example
    {σ τ ρ energy : ℝ} (h : InCardinalityEnergyRegion σ τ ρ energy)
    (hσ : 3/4 < σ) (hτlo : 1 ≤ τ) (hτhi : τ ≤ 3/2)
    (hlower : 16*σ-11 ≤ τ) (hupper : 20*σ+τ/3 ≤ 16) :
    ρ ≤ 9-12*σ+2*τ/3 := by
  exact @TaoTrudgianYang2025.InCardinalityEnergyRegion.bourgain_ninth_row σ τ ρ energy h hσ hτlo hτhi hlower hupper

example
    {σ τ ρ energy : ℝ} (h : InCardinalityEnergyRegion σ τ ρ energy)
    (q : ℕ) (hq : 1 ≤ q) (hσ : 3/4 < σ)
    (hτlo : 1 ≤ τ/q) (hτhi : τ/q ≤ 3/2)
    (hlower : 16*σ-11 ≤ τ/q) (hupper : 20*σ+(τ/q)/3 ≤ 16) :
    ρ/q ≤ 9-12*σ+2*(τ/q)/3 := by
  exact @TaoTrudgianYang2025.InCardinalityEnergyRegion.bourgain_ninth_row_powered σ τ ρ energy h q hq hσ hτlo hτhi hlower hupper

example
    {σ τ ρ energy χ α : ℝ} (h : InCardinalityEnergyRegion σ τ ρ energy)
    (hσ : 3/4 < σ) (hχ : 0 ≤ χ) (hmargin : 1 < τ-χ)
    (hr : ρ ≤ 1) (hrt : ρ ≤ 4-2*τ) :
    ρ ≤ max
      (max (max (χ+2-2*σ) (α+χ/2+2-2*σ)) (-χ+2*τ+4-8*σ))
      (max (-2*α+τ+12-16*σ) (4*α+2+max 1 (2*τ-2)-4*σ)) := by
  exact @TaoTrudgianYang2025.InCardinalityEnergyRegion.bourgain_five_terms σ τ ρ energy χ α h hσ hχ hmargin hr hrt

example
    {σ τ ρ energy : ℝ} (h : InCardinalityEnergyRegion σ τ ρ energy)
    (hσ : 3/4 < σ) (htlo : 1 ≤ τ) (hthi : τ ≤ 3/2)
    (hlower : 14*σ-10 ≤ τ) (hslant : 5*τ ≤ 4+4*σ)
    (hupper : τ ≤ 16*σ-11) :
    ρ ≤ (16-20*σ+τ)/3 := by
  exact @TaoTrudgianYang2025.InCardinalityEnergyRegion.bourgain_first_affine_row σ τ ρ energy h hσ htlo hthi hlower hslant hupper

example
    {σ τ ρ energy : ℝ} (h : InCardinalityEnergyRegion σ τ ρ energy)
    (hσ : 3/4 < σ) (hthi : τ ≤ 3/2)
    (hslant : 4+4*σ ≤ 5*τ) (hlower : 48-60*σ ≤ τ)
    (hupper : τ ≤ 8-8*σ) :
    ρ ≤ 5-7*σ+3*τ/4 := by
  exact @TaoTrudgianYang2025.InCardinalityEnergyRegion.bourgain_mixed_affine_row σ τ ρ energy h hσ hthi hslant hlower hupper

example
    {σ τ ρ energy : ℝ} (h : InCardinalityEnergyRegion σ τ ρ energy)
    (hσ : 3/4 < σ) (htlo : 1 ≤ τ) (hthi : τ ≤ 3/2)
    (hupper : τ ≤ 14*σ-10) (hslant : τ ≤ 3*σ-1) :
    ρ ≤ 2-2*σ := by
  exact @TaoTrudgianYang2025.InCardinalityEnergyRegion.bourgain_diagonal_row σ τ ρ energy h hσ htlo hthi hupper hslant

-- Original lower endpoint of the ninth-row application.
example {ρ e : ℝ} (h : InCardinalityEnergyRegion (84/109) (3/2) ρ e) :
    ρ ≤ 82/109 := by
  have hb := h.bourgain_ninth_row (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num at hb ⊢
  exact hb

-- The three optimized affine cells meet at this exact corner.
example {ρ e : ℝ} (h : InCardinalityEnergyRegion (59/76) (27/19) ρ e) :
    ρ ≤ 12/19 := by
  have hb := h.bourgain_ninth_row (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num at hb ⊢
  exact hb

example {ρ e : ℝ} (h : InCardinalityEnergyRegion (59/76) (27/19) ρ e) :
    ρ ≤ 12/19 := by
  have hb := h.bourgain_first_affine_row (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at hb ⊢
  exact hb

example {ρ e : ℝ} (h : InCardinalityEnergyRegion (59/76) (27/19) ρ e) :
    ρ ≤ 12/19 := by
  have hb := h.bourgain_mixed_affine_row (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at hb ⊢
  exact hb

-- Height one is a classical boundary, not an assumed strict local margin.
example {ρ e : ℝ} (h : InCardinalityEnergyRegion (11/14) 1 ρ e) :
    ρ ≤ 3/7 := by
  have hb := h.bourgain_first_affine_row (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at hb ⊢
  exact hb

example {ρ e : ℝ} (h : InCardinalityEnergyRegion (4/5) (6/5) ρ e) :
    ρ ≤ 2/5 := by
  have hb := h.bourgain_diagonal_row (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num at hb ⊢
  exact hb

-- The power-two consumer preserves cardinality without a fifth-coordinate constraint.
example {ρ e : ℝ} (h : InCardinalityEnergyRegion (31/40) 3 ρ e) :
    ρ ≤ 7/5 := by
  have hb := h.bourgain_ninth_row_powered 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hb ⊢
  linarith

-- Logarithm absorption is valid at Mathlib's zero convention too.
example {N ε : ℝ} (hN : 1 < N) (hε : 0 < ε)
    (hscale : Real.exp (|Real.log (0 : ℝ)|/ε+1) ≤ N) :
    |Real.logb N 0| ≤ ε :=
  bourgain_abs_logb_le_of_threshold hN hε hscale

-- The selected objects remain actual separated subsets of the original pattern.
example {σ τ χ α ρ : ℝ} (F : BourgainDiagonalFamily σ τ χ α ρ) (n : ℕ) :
    F.retained n ⊆ (F.pattern n).ordinates ∧ IsSeparated 1 (F.retained n) :=
  ⟨F.retained_subset n, F.retained_separated n⟩

end BourgainSourceDichotomyRegression

namespace AddEstNineRegression

-- EnergyClauseNineRates: energyClauseNineRate_eq_printed
example (σ : ℝ) :
    energyClauseNineRate σ =
      max ((18-19*σ)/(9*(3*σ-2))) (4*(10-9*σ)/(5*(4*σ-1))) :=
  @TaoTrudgianYang2025.energyClauseNineRate_eq_printed σ

-- EnergyClauseNineRates: energyClauseNineFirstRate_le
example (σ : ℝ) :
    energyClauseNineFirstRate σ ≤ energyClauseNineRate σ :=
  @TaoTrudgianYang2025.energyClauseNineFirstRate_le σ

-- EnergyClauseNineRates: energyClauseNineSecondRate_le
example (σ : ℝ) :
    energyClauseNineSecondRate σ ≤ energyClauseNineRate σ :=
  @TaoTrudgianYang2025.energyClauseNineSecondRate_le σ

-- EnergyClauseNineRates: energyClauseNine_printed_denominators_pos
example {σ : ℝ} (hlo : 84/109 ≤ σ) :
    0 < 9*(3*σ-2) ∧ 0 < 5*(4*σ-1) :=
  @TaoTrudgianYang2025.energyClauseNine_printed_denominators_pos σ hlo

-- EnergyClauseNineRates: energyClauseNineRate_pos
example {σ : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 5/6) :
    0 < energyClauseNineRate σ :=
  @TaoTrudgianYang2025.energyClauseNineRate_pos σ hlo hhi

-- EnergyClauseNineRates: energyClauseNineRate_div_eq_blueprint
example {σ : ℝ} (hhi : σ ≤ 5/6) :
    energyClauseNineRate σ/(1-σ) =
      max ((18-19*σ)/(9*(3*σ-2)*(1-σ)))
        (4*(10-9*σ)/(5*(4*σ-1)*(1-σ))) :=
  @TaoTrudgianYang2025.energyClauseNineRate_div_eq_blueprint σ hhi

-- EnergyClauseNineRates: energyClauseNineRate_ge_short_linear
example {σ : ℝ} (hlo : 84/109 ≤ σ) :
    15-18*σ ≤ energyClauseNineRate σ :=
  @TaoTrudgianYang2025.energyClauseNineRate_ge_short_linear σ hlo

-- EnergyClauseNineRates: energyClauseOneZetaRate_le_nine
example {σ : ℝ} (hlo : 84/109 ≤ σ) :
    energyClauseOneZetaRate σ ≤ energyClauseNineRate σ :=
  @TaoTrudgianYang2025.energyClauseOneZetaRate_le_nine σ hlo

-- EnergyClauseNineRates: energyClauseOneGeneralRate_le_nine
example {σ : ℝ}
    (hlo : 4/5 ≤ σ) :
    energyClauseOneGeneralRate σ ≤ energyClauseNineRate σ :=
  @TaoTrudgianYang2025.energyClauseOneGeneralRate_le_nine σ hlo

-- EnergyClauseNineShortCertificates: energyClauseNine_short_diag_0
example {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5) :
    0*t+((14/3)+(-14/3)*σ) ≤ energyClauseNineSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_short_diag_0 σ t hlo hhi htlo hthi

-- EnergyClauseNineShortCertificates: energyClauseNine_short_diag_1
example {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5) :
    0*t+((23/4)+-6*σ) ≤ energyClauseNineSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_short_diag_1 σ t hlo hhi htlo hthi

-- EnergyClauseNineShortCertificates: energyClauseNine_short_diag_2
example {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5) :
    (2/5)*t+((22/5)+(-24/5)*σ) ≤ energyClauseNineSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_short_diag_2 σ t hlo hhi htlo hthi

-- EnergyClauseNineShortCertificates: energyClauseNine_short_diag_3
example {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5) :
    0*t+((11/2)+-6*σ) ≤ energyClauseNineSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_short_diag_3 σ t hlo hhi htlo hthi

-- EnergyClauseNineShortCertificates: energyClauseNine_short_diag_4
example {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5) :
    0*t+((13/2)+-7*σ) ≤ energyClauseNineSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_short_diag_4 σ t hlo hhi htlo hthi

-- EnergyClauseNineShortCertificates: energyClauseNine_short_diag_5
example {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5) :
    (2/5)*t+((28/5)+(-32/5)*σ) ≤ energyClauseNineSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_short_diag_5 σ t hlo hhi htlo hthi

-- EnergyClauseNineShortCertificates: energyClauseNine_short_diag_6
example {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5) :
    (1/2)*t+(4+(-9/2)*σ) ≤ energyClauseNineSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_short_diag_6 σ t hlo hhi htlo hthi

-- EnergyClauseNineShortCertificates: energyClauseNine_short_diag_7
example {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5) :
    (1/4)*t+((23/4)+(-25/4)*σ) ≤ energyClauseNineSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_short_diag_7 σ t hlo hhi htlo hthi

-- EnergyClauseNineShortCertificates: energyClauseNine_short_diag_8
example {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5) :
    (4/5)*t+((22/5)+(-26/5)*σ) ≤ energyClauseNineSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_short_diag_8 σ t hlo hhi htlo hthi

-- EnergyClauseNineShortCertificates: energyClauseNine_short_affine_0
example {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5) :
    1*t+((94/15)+(-124/15)*σ) ≤ energyClauseNineSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_short_affine_0 σ t hlo hhi htlo hthi

-- EnergyClauseNineShortCertificates: energyClauseNine_short_affine_1
example {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5) :
    (5/2)*t+((39/4)+-15*σ) ≤ energyClauseNineSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_short_affine_1 σ t hlo hhi htlo hthi

-- EnergyClauseNineShortCertificates: energyClauseNine_short_affine_2
example {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5) :
    2*t+((174/25)+(-264/25)*σ) ≤ energyClauseNineSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_short_affine_2 σ t hlo hhi htlo hthi

-- EnergyClauseNineShortCertificates: energyClauseNine_short_affine_3
example {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5) :
    2*t+((87/10)+(-66/5)*σ) ≤ energyClauseNineSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_short_affine_3 σ t hlo hhi htlo hthi

-- EnergyClauseNineShortCertificates: energyClauseNine_short_affine_4
example {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5) :
    3*t+((113/10)+(-89/5)*σ) ≤ energyClauseNineSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_short_affine_4 σ t hlo hhi htlo hthi

-- EnergyClauseNineShortCertificates: energyClauseNine_short_affine_5
example {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5) :
    (14/5)*t+((236/25)+(-376/25)*σ) ≤ energyClauseNineSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_short_affine_5 σ t hlo hhi htlo hthi

-- EnergyClauseNineShortCertificates: energyClauseNine_short_affine_6
example {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5) :
    (7/4)*t+(6+-9*σ) ≤ energyClauseNineSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_short_affine_6 σ t hlo hhi htlo hthi

-- EnergyClauseNineShortCertificates: energyClauseNine_short_affine_7
example {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5) :
    (23/8)*t+((199/20)+(-157/10)*σ) ≤ energyClauseNineSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_short_affine_7 σ t hlo hhi htlo hthi

-- EnergyClauseNineShortCertificates: energyClauseNine_short_affine_8
example {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5) :
    (13/5)*t+((182/25)+(-292/25)*σ) ≤ energyClauseNineSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_short_affine_8 σ t hlo hhi htlo hthi

-- EnergyClauseNineMiddleCertificates: energyClauseNine_middle_low_diag_0
example {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 17/22)
    (htlo : 6/5 ≤ t) (hthi : t ≤ (81-96*σ)/5) :
    0*t+(6+-6*σ) ≤ energyClauseNineFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_middle_low_diag_0 σ t hlo hhi htlo hthi

-- EnergyClauseNineMiddleCertificates: energyClauseNine_middle_low_diag_1
example {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 17/22)
    (htlo : 6/5 ≤ t) (hthi : t ≤ (81-96*σ)/5) :
    0*t+((13/2)+-7*σ) ≤ energyClauseNineFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_middle_low_diag_1 σ t hlo hhi htlo hthi

-- EnergyClauseNineMiddleCertificates: energyClauseNine_middle_low_affine_0
example {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 17/22)
    (htlo : 6/5 ≤ t) (hthi : t ≤ (81-96*σ)/5) :
    1*t+((38/5)+(-48/5)*σ) ≤ energyClauseNineFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_middle_low_affine_0 σ t hlo hhi htlo hthi

-- EnergyClauseNineMiddleCertificates: energyClauseNine_middle_low_affine_1
example {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 17/22)
    (htlo : 6/5 ≤ t) (hthi : t ≤ (81-96*σ)/5) :
    (5/2)*t+((21/2)+-16*σ) ≤ energyClauseNineFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_middle_low_affine_1 σ t hlo hhi htlo hthi

-- EnergyClauseNineMiddleCertificates: energyClauseNine_middle_high_diag_0
example {σ t : ℝ}
    (hlo : 17/22 ≤ σ)
    (htlo : 6/5 ≤ t) (hthi : t ≤ (13-8*σ)/5) :
    0*t+(6+-6*σ) ≤ energyClauseNineSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_middle_high_diag_0 σ t hlo htlo hthi

-- EnergyClauseNineMiddleCertificates: energyClauseNine_middle_high_diag_1
example {σ t : ℝ}
    (hlo : 17/22 ≤ σ)
    (htlo : 6/5 ≤ t) (hthi : t ≤ (13-8*σ)/5) :
    0*t+((13/2)+-7*σ) ≤ energyClauseNineSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_middle_high_diag_1 σ t hlo htlo hthi

-- EnergyClauseNineMiddleCertificates: energyClauseNine_middle_high_affine_0
example {σ t : ℝ}
    (hlo : 17/22 ≤ σ)
    (htlo : 6/5 ≤ t) (hthi : t ≤ (13-8*σ)/5) :
    1*t+((38/5)+(-48/5)*σ) ≤ energyClauseNineSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_middle_high_affine_0 σ t hlo htlo hthi

-- EnergyClauseNineMiddleCertificates: energyClauseNine_middle_high_affine_1
example {σ t : ℝ}
    (hlo : 17/22 ≤ σ)
    (htlo : 6/5 ≤ t) (hthi : t ≤ (13-8*σ)/5) :
    (5/2)*t+((21/2)+-16*σ) ≤ energyClauseNineSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_middle_high_affine_1 σ t hlo htlo hthi

-- EnergyClauseNineMiddleCertificates: energyClauseNine_middle_first_0
example {σ t : ℝ}
    (hlo : 17/22 ≤ σ)
    (htlo : (13-8*σ)/5 ≤ t) (hthi : t ≤ (4+4*σ)/5) :
    (1/3)*t+((28/3)+(-32/3)*σ) ≤ energyClauseNineSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_middle_first_0 σ t hlo htlo hthi

-- EnergyClauseNineMiddleCertificates: energyClauseNine_middle_first_1
example {σ t : ℝ}
    (hlo : 17/22 ≤ σ)
    (htlo : (13-8*σ)/5 ≤ t) (hthi : t ≤ (4+4*σ)/5) :
    (5/6)*t+((89/6)+(-56/3)*σ) ≤ energyClauseNineSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_middle_first_1 σ t hlo htlo hthi

-- EnergyClauseNineMiddleCertificates: energyClauseNine_middle_ninth_0
example {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 16*σ-11 ≤ t) (hthi : t ≤ (27*σ-18)/2) :
    (2/3)*t+(13+-16*σ) ≤ energyClauseNineFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_middle_ninth_0 σ t hlo hhi htlo hthi

-- EnergyClauseNineMiddleCertificates: energyClauseNine_middle_ninth_1
example {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 16*σ-11 ≤ t) (hthi : t ≤ (27*σ-18)/2) :
    (5/3)*t+(24+-32*σ) ≤ energyClauseNineFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_middle_ninth_1 σ t hlo hhi htlo hthi

-- EnergyClauseNineMiddleCertificates: energyClauseNine_middle_mixed_0
example {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : (4+4*σ)/5 ≤ t) (hthi : t ≤ (16*σ-8)/3) :
    (3/4)*t+(9+-11*σ) ≤ energyClauseNineSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_middle_mixed_0 σ t hlo hhi htlo hthi

-- EnergyClauseNineMiddleCertificates: energyClauseNine_middle_mixed_1
example {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : (4+4*σ)/5 ≤ t) (hthi : t ≤ (16*σ-8)/3) :
    (15/8)*t+(14+(-39/2)*σ) ≤ energyClauseNineSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_middle_mixed_1 σ t hlo hhi htlo hthi

-- EnergyClauseNineTallCertificates: energyClauseNine_tall_0
example {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 6*σ-3) :
    0*t+(7+-7*σ) ≤ energyClauseNineSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_tall_0 σ t hlo hhi htlo hthi

-- EnergyClauseNineTallCertificates: energyClauseNine_tall_1
example {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 6*σ-3) :
    0*t+(9+(-19/2)*σ) ≤ energyClauseNineSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_tall_1 σ t hlo hhi htlo hthi

-- EnergyClauseNineTallCertificates: energyClauseNine_tall_2
example {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 6*σ-3) :
    (2/5)*t+((36/5)+-8*σ) ≤ energyClauseNineSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_tall_2 σ t hlo hhi htlo hthi

-- EnergyClauseNineTallCertificates: energyClauseNine_tall_3
example {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 6*σ-3) :
    (1/2)*t+((27/4)+(-31/4)*σ) ≤ energyClauseNineSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_tall_3 σ t hlo hhi htlo hthi

-- EnergyClauseNineTallCertificates: energyClauseNine_tall_4
example {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 6*σ-3) :
    (1/4)*t+((71/8)+(-79/8)*σ) ≤ energyClauseNineSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_tall_4 σ t hlo hhi htlo hthi

-- EnergyClauseNineTallCertificates: energyClauseNine_tall_5
example {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 6*σ-3) :
    (4/5)*t+(7+(-43/5)*σ) ≤ energyClauseNineSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_tall_5 σ t hlo hhi htlo hthi

-- EnergyClauseNineTallCertificates: energyClauseNine_cap_0
example {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5) (htlo : (27*σ-18)/2 ≤ t) :
    7-7*σ ≤ energyClauseNineFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_cap_0 σ t hlo hhi htlo

-- EnergyClauseNineTallCertificates: energyClauseNine_cap_1
example {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5) (htlo : (27*σ-18)/2 ≤ t) :
    9-(19/2)*σ ≤ energyClauseNineFirstRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_cap_1 σ t hlo hhi htlo

-- EnergyClauseNineTallCertificates: energyClauseNine_cap_mixed_0
example {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5) (htlo : (16*σ-8)/3 ≤ t) :
    7-7*σ ≤ energyClauseNineSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_cap_mixed_0 σ t hlo hhi htlo

-- EnergyClauseNineTallCertificates: energyClauseNine_cap_mixed_1
example {σ t : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5) (htlo : (16*σ-8)/3 ≤ t) :
    9-(19/2)*σ ≤ energyClauseNineSecondRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_cap_mixed_1 σ t hlo hhi htlo

-- EnergyClauseNineBranches: energyClauseNine_short_branch
example {σ t r a e : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 4*σ-2 ≤ t) (hthi : t ≤ 6/5)
    (halo : 1/2 ≤ a) (hahi : a ≤ 2/3)
    (hj : r ≤ max (2-2*σ) (t+18/5-(28/5)*σ))
    (i : Fin 9) (hb : e ≤ heathBrownNineBranch σ t r a i) :
    e ≤ energyClauseNineRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_short_branch σ t r a e hlo hhi htlo hthi halo hahi hj i hb

-- EnergyClauseNineBranches: energyClauseNine_middle_first_bound
example {σ t r : ℝ}
    (hlo : 17/22 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : (13-8*σ)/5 ≤ t) (hthi : t ≤ (4+4*σ)/5) (hr : r ≤ (16-20*σ+t)/3) :
    max (r+4-4*σ) ((3-4*σ+5*r)/2) ≤ energyClauseNineRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_middle_first_bound σ t r hlo hhi htlo hthi hr

-- EnergyClauseNineBranches: energyClauseNine_middle_ninth_bound
example {σ t r : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 16*σ-11 ≤ t) (hthi : t ≤ (27*σ-18)/2) (hr : r ≤ 9-12*σ+2*t/3) :
    max (r+4-4*σ) ((3-4*σ+5*r)/2) ≤ energyClauseNineRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_middle_ninth_bound σ t r hlo hhi htlo hthi hr

-- EnergyClauseNineBranches: energyClauseNine_middle_mixed_bound
example {σ t r : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : (4+4*σ)/5 ≤ t) (hthi : t ≤ (16*σ-8)/3) (hr : r ≤ 5-7*σ+3*t/4) :
    max (r+4-4*σ) ((3-4*σ+5*r)/2) ≤ energyClauseNineRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_middle_mixed_bound σ t r hlo hhi htlo hthi hr

-- EnergyClauseNineBranches: energyClauseNine_cap_bound
example {σ t r : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5) (htlo : (27*σ-18)/2 ≤ t) (hr : r ≤ 3-3*σ) :
    max (r+4-4*σ) ((3-4*σ+5*r)/2) ≤ energyClauseNineRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_cap_bound σ t r hlo hhi htlo hr

-- EnergyClauseNineBranches: energyClauseNine_cap_mixed_bound
example {σ t r : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5) (htlo : (16*σ-8)/3 ≤ t) (hr : r ≤ 3-3*σ) :
    max (r+4-4*σ) ((3-4*σ+5*r)/2) ≤ energyClauseNineRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_cap_mixed_bound σ t r hlo hhi htlo hr

-- EnergyClauseNineBranches: energyClauseNine_middle_low_bound
example {σ t r : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 17/22)
    (htlo : 6/5 ≤ t) (hthi : t ≤ (81-96*σ)/5)
    (hj : r ≤ max (2-2*σ) (t+18/5-(28/5)*σ)) :
    max (r+4-4*σ) ((3-4*σ+5*r)/2) ≤ energyClauseNineRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_middle_low_bound σ t r hlo hhi htlo hthi hj

-- EnergyClauseNineBranches: energyClauseNine_middle_high_bound
example {σ t r : ℝ}
    (hlo : 17/22 ≤ σ)
    (htlo : 6/5 ≤ t) (hthi : t ≤ (13-8*σ)/5)
    (hj : r ≤ max (2-2*σ) (t+18/5-(28/5)*σ)) :
    max (r+4-4*σ) ((3-4*σ+5*r)/2) ≤ energyClauseNineRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_middle_high_bound σ t r hlo htlo hthi hj

-- EnergyClauseNineBranches: energyClauseNine_tall_branch
example {σ t r : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5)
    (htlo : 3/2 ≤ t) (hthi : t ≤ 6*σ-3) (hr : r ≤ 3-3*σ) (i : Fin 6) :
    heathBrownEnergyBranch σ t r i ≤ energyClauseNineRate σ*t :=
  @TaoTrudgianYang2025.energyClauseNine_tall_branch σ t r hlo hhi htlo hthi hr i

-- EnergyClauseNineRegion: InCardinalityEnergyRegion.energyClauseNine_middle
example
    {σ t r e : ℝ} (h : InCardinalityEnergyRegion σ t r e)
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 4/5) (htlo : 6/5 ≤ t) (hthi : t ≤ 3/2)
    (hj : r ≤ max (2-2*σ) (t+18/5-(28/5)*σ)) (hcap : r ≤ 3-3*σ) :
    max (r+4-4*σ) ((3-4*σ+5*r)/2) ≤ energyClauseNineRate σ*t :=
  @TaoTrudgianYang2025.InCardinalityEnergyRegion.energyClauseNine_middle σ t r e h hlo hhi htlo hthi hj hcap

-- EnergyClauseNineGeneral: InCardinalityEnergyRegion.energyClauseNine_general
example
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 5/6)
    (htlo : 8*σ-4 ≤ τ) (hthi : τ ≤ 2*(8*σ-4)) :
    e ≤ energyClauseNineRate σ*τ :=
  @TaoTrudgianYang2025.InCardinalityEnergyRegion.energyClauseNine_general σ τ ρ e h hlo hhi htlo hthi

-- EnergyClauseNineGeneral: energyClauseNine_general_bound
example {σ τ : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 5/6)
    (htlo : 8*σ-4 ≤ τ) (hthi : τ ≤ 2*(8*σ-4)) :
    IsLargeValueEnergyBound σ τ (energyClauseNineRate σ*τ) :=
  @TaoTrudgianYang2025.energyClauseNine_general_bound σ τ hlo hhi htlo hthi

-- EnergyClauseNineZeta: energyClauseNine_short_cubic_bound
example {σ τ : ℝ}
    (hlo : 84/109 ≤ σ) (htlo : 0 ≤ τ) (hthi : τ ≤ 2) :
    3*(2*τ-12*(σ-1/2)) ≤ energyClauseNineRate σ*τ :=
  @TaoTrudgianYang2025.energyClauseNine_short_cubic_bound σ τ hlo htlo hthi

-- EnergyClauseNineZeta: InZetaLargeValueEnergyRegion.energyClauseNine
example
    {σ τ ρ e s : ℝ} (h : InZetaLargeValueEnergyRegion σ τ ρ e s)
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 5/6)
    (htlo : 3/2 ≤ τ) (hthi : τ ≤ 8*σ-4) :
    e ≤ energyClauseNineRate σ*τ :=
  @TaoTrudgianYang2025.InZetaLargeValueEnergyRegion.energyClauseNine σ τ ρ e s h hlo hhi htlo hthi

-- EnergyClauseNineZeta: energyClauseNine_zeta_bound
example {σ τ : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 5/6)
    (htlo : 1 ≤ τ) (hthi : τ ≤ 8*σ-4) :
    IsZetaLargeValueEnergyBound σ τ (energyClauseNineRate σ*τ) :=
  @TaoTrudgianYang2025.energyClauseNine_zeta_bound σ τ hlo hhi htlo hthi

-- EnergyClauseNine: energyClauseNine
example {σ : ℝ} (hlo : 84/109 ≤ σ) (hhi : σ ≤ 5/6) :
    IsZeroDensityEnergyBound σ (energyClauseNineRate σ/(1-σ)) :=
  @TaoTrudgianYang2025.energyClauseNine σ hlo hhi

-- EnergyClauseNine: energyClauseNine_blueprint
example {σ : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 5/6) :
    zeroDensityEnergyExponent σ ≤
      ((max ((18-19*σ)/(9*(3*σ-2)*(1-σ)))
        (4*(10-9*σ)/(5*(4*σ-1)*(1-σ))) : ℝ) : EReal) :=
  @TaoTrudgianYang2025.energyClauseNine_blueprint σ hlo hhi

-- NewAdditiveEnergy: add_est_ix_bound
example {σ : ℝ} (hlo : 84/109 ≤ σ) (hhi : σ ≤ 5/6) :
    IsZeroDensityEnergyBound σ
      ((max ((18-19*σ)/(9*(3*σ-2))) (4*(10-9*σ)/(5*(4*σ-1))))/(1-σ)) :=
  @TaoTrudgianYang2025.add_est_ix_bound σ hlo hhi

-- NewAdditiveEnergy: add_est_ix
example {σ : ℝ} (hlo : 84/109 ≤ σ) (hhi : σ ≤ 5/6) :
    zeroDensityEnergyExponent σ*((1-σ : ℝ) : EReal) ≤
      ((max ((18-19*σ)/(9*(3*σ-2))) (4*(10-9*σ)/(5*(4*σ-1))) : ℝ) : EReal) :=
  @TaoTrudgianYang2025.add_est_ix σ hlo hhi

-- NewAdditiveEnergy: add_est_ix_zero_energy
example {σ : ℝ} (hlo : 84/109 ≤ σ) (hhi : σ ≤ 5/6) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ T : ℝ, C ≤ T →
        (zeroAdditiveEnergy (σ-δ) T : ℝ) ≤ C*T^
          ((max ((18-19*σ)/(9*(3*σ-2))) (4*(10-9*σ)/(5*(4*σ-1))))+ε) :=
  @TaoTrudgianYang2025.add_est_ix_zero_energy σ hlo hhi

-- Exact source endpoints and all operational switching heights.
example : energyClauseNineRate (84/109) = 61/51 := by
  norm_num [energyClauseNineRate, energyClauseNineFirstRate, energyClauseNineSecondRate]

example : energyClauseNineRate (5/6) = 6/7 := by
  norm_num [energyClauseNineRate, energyClauseNineFirstRate, energyClauseNineSecondRate]

example : IsZeroDensityEnergyBound (84/109) ((61/51)/(1-84/109)) := by
  have heq : energyClauseNineRate (84/109) = 61/51 := by
    norm_num [energyClauseNineRate, energyClauseNineFirstRate, energyClauseNineSecondRate]
  simpa only [heq] using energyClauseNine (σ := 84/109) (by norm_num) (by norm_num)

example : IsZeroDensityEnergyBound (5/6) (36/7) := by
  convert energyClauseNine (σ := 5/6) (by norm_num) (by norm_num) using 1
  norm_num [energyClauseNineRate, energyClauseNineFirstRate, energyClauseNineSecondRate]

example {ρ e : ℝ} (h : InCardinalityEnergyRegion (84/109) (236/109) ρ e) :
    e ≤ energyClauseNineRate (84/109)*(236/109) :=
  h.energyClauseNine_general (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example {ρ e : ℝ} (h : InCardinalityEnergyRegion (5/6) (16/3) ρ e) :
    e ≤ energyClauseNineRate (5/6)*(16/3) :=
  h.energyClauseNine_general (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : IsZetaLargeValueEnergyBound (84/109) 1 (energyClauseNineRate (84/109)*1) :=
  energyClauseNine_zeta_bound (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : IsZetaLargeValueEnergyBound (84/109) (3/2)
    (energyClauseNineRate (84/109)*(3/2)) :=
  energyClauseNine_zeta_bound (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : IsZetaLargeValueEnergyBound (84/109) 2 (energyClauseNineRate (84/109)*2) :=
  energyClauseNine_zeta_bound (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : IsZetaLargeValueEnergyBound (5/6) (8/3) (energyClauseNineRate (5/6)*(8/3)) :=
  energyClauseNine_zeta_bound (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : (81-96*(17/22 : ℝ))/5 = (13-8*(17/22 : ℝ))/5 := by norm_num

example : (16*(59/76 : ℝ)-11) = (4+4*(59/76 : ℝ))/5 ∧
    (48-60*(59/76 : ℝ)) = (27/19 : ℝ) := by norm_num

example : (27*(38/49 : ℝ)-18)/2 = 48-60*(38/49 : ℝ) := by norm_num

example : (16*(25/32 : ℝ)-8)/3 = (3/2 : ℝ) := by norm_num

end AddEstNineRegression

namespace ClosedBetaDualityRegression

open Set Expdb
open scoped ContDiff

-- BetaUniformity: approximateModelPhase_mono
example {F : ℝ → ℝ} {σ δ₀ δ₁ : ℝ} {P₀ P₁ : ℕ}
    (h : IsApproximateModelPhaseFunction F σ P₁ δ₀)
    (hP : P₀ ≤ P₁) (hδ : δ₀ ≤ δ₁) :
    IsApproximateModelPhaseFunction F σ P₀ δ₁ :=
  @TaoTrudgianYang2025.approximateModelPhase_mono F σ δ₀ δ₁ P₀ P₁ h hP hδ

-- BetaUniformity: exponentPair_rhs_eq_logb_power
example {T N : ℝ}
    (hT : 1 < T) (hN : 0 < N) (k l ε : ℝ) :
    (T/N)^(k+ε)*N^(l+ε) =
      T^(exponentPairLine k l (Real.logb T N)+ε) :=
  @TaoTrudgianYang2025.exponentPair_rhs_eq_logb_power T N hT hN k l ε

-- BetaUniformity: isExponentPairEstimateNonAsymptotic_of_beta_bound
example
    {k l : ℝ} (htri : InExponentPairTriangle k l)
    (hβ : ∀ α : ℝ≥0, (α : ℝ) ≤ 1 →
      exponentSumGrowthExponent α ≤ exponentPairLine k l α) :
    IsExponentPairEstimateNonAsymptotic k l :=
  @TaoTrudgianYang2025.isExponentPairEstimateNonAsymptotic_of_beta_bound k l htri hβ

-- BetaUniformity: exponentPair_of_beta_bound
example {k l : ℝ} (htri : InExponentPairTriangle k l)
    (hβ : ∀ α : ℝ≥0, (α : ℝ) ≤ 1 →
      exponentSumGrowthExponent α ≤ exponentPairLine k l α) :
    ExponentPair k l :=
  @TaoTrudgianYang2025.exponentPair_of_beta_bound k l htri hβ

-- BetaSecondDerivative: modelPhaseCurvatureLower_pos
example {σ : ℝ} (hσ : 0 < σ) :
    0 < modelPhaseCurvatureLower σ :=
  @TaoTrudgianYang2025.modelPhaseCurvatureLower_pos σ hσ

-- BetaSecondDerivative: approximateModelPhase_curvature_bounds
example {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {u : ℝ} (hu : u ∈ phaseInterval) :
    modelPhaseCurvatureLower σ ≤ -iteratedDerivWithin 2 F phaseInterval u ∧
      -iteratedDerivWithin 2 F phaseInterval u ≤ σ+1 :=
  @TaoTrudgianYang2025.approximateModelPhase_curvature_bounds σ δ F hσ hδ hF u hu

-- BetaSecondDerivative: approximateModelPhase_curvature_deriv_bounds
example {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) :
    modelPhaseCurvatureLower σ ≤ -deriv (deriv F) u ∧
      -deriv (deriv F) u ≤ σ+1 :=
  @TaoTrudgianYang2025.approximateModelPhase_curvature_deriv_bounds σ δ F hσ hδ hF u hu

-- BetaDiscreteCurvature: betaModelSample_hasDerivAt
example {F : ℝ → ℝ} {T N A x : ℝ}
    (hF : ContDiffOn ℝ ∞ F phaseInterval) (hu : (A+x)/N ∈ Ioo (1 : ℝ) 2) :
    HasDerivAt (betaModelSample F T N A)
      ((-2*Real.pi*T/N)*deriv F ((A+x)/N)) x :=
  @TaoTrudgianYang2025.betaModelSample_hasDerivAt F T N A x hF hu

-- BetaDiscreteCurvature: betaModelSample_firstDeriv_hasDerivAt
example {F : ℝ → ℝ} {T N A x : ℝ}
    (hF : ContDiffOn ℝ ∞ F phaseInterval) (hu : (A+x)/N ∈ Ioo (1 : ℝ) 2) :
    HasDerivAt (fun y : ℝ => (-2*Real.pi*T/N)*deriv F ((A+y)/N))
      ((-2*Real.pi*T/N^2)*deriv (deriv F) ((A+x)/N)) x :=
  @TaoTrudgianYang2025.betaModelSample_firstDeriv_hasDerivAt F T N A x hF hu

-- BetaDiscreteCurvature: betaModelSample_secondDifference_bounds
example
    {σ δ T N A : ℝ} {F : ℝ → ℝ} {L : ℕ}
    (hσ : 0 < σ) (hT : 0 < T) (hN : 0 < N)
    (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hstart : N < A) (hend : A+(L : ℝ)+1 < 2*N)
    (n : ℕ) (hn : n < L) :
    (2*Real.pi*modelPhaseCurvatureLower σ)*T/N^2 ≤
      (betaModelSample F T N A (n+2)-betaModelSample F T N A (n+1)) -
        (betaModelSample F T N A (n+1)-betaModelSample F T N A n) ∧
    (betaModelSample F T N A (n+2)-betaModelSample F T N A (n+1)) -
        (betaModelSample F T N A (n+1)-betaModelSample F T N A n) ≤
      (2*Real.pi*(σ+1))*T/N^2 :=
  @TaoTrudgianYang2025.betaModelSample_secondDifference_bounds σ δ T N A F L hσ hT hN hδ hF hstart hend n hn

-- BetaBProcessMajorant: betaBProcessConstant_pos
example {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C) :
    0 < betaBProcessConstant c C :=
  @TaoTrudgianYang2025.betaBProcessConstant_pos c C hc hC

-- BetaBProcessMajorant: betaBProcess_majorant
example {m N T c C : ℝ}
    (hN : 0 < N) (hT : 0 < T) (hc : 0 < c) (hC : 0 ≤ C)
    (hm : m ≤ N) (hscale : T ≤ N^2) :
    (m*(C*T/N^2)/(2*Real.pi)+2)*
        (2*Real.pi/Real.sqrt (c*T/N^2)+2*(Real.sqrt (c*T/N^2)/(c*T/N^2)+1)) ≤
      betaBProcessConstant c C*(Real.sqrt T+N/Real.sqrt T) :=
  @TaoTrudgianYang2025.betaBProcess_majorant m N T c C hN hT hc hC hm hscale

-- BetaFiniteSum: betaModelSample_phase_eq_conj
example (F : ℝ → ℝ) (T N A x : ℝ) :
    unitaryPhase (betaModelSample F T N A x) =
      starRingEnd ℂ (oscillatory F T N (A+x)) :=
  @TaoTrudgianYang2025.betaModelSample_phase_eq_conj F T N A x

-- BetaFiniteSum: norm_modelPhaseCore_le
example
    {σ δ T N A : ℝ} {F : ℝ → ℝ} {L : ℕ}
    (hσ : 0 < σ) (hT : 0 < T) (hN : 0 < N)
    (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hstart : N < A) (hend : A+(L : ℝ)+1 < 2*N)
    (hL : (L : ℝ) ≤ N) (hscale : T ≤ N^2) :
    ‖∑ n ∈ Finset.range (L+1), oscillatory F T N (A+n)‖ ≤
      betaBProcessConstant (2*Real.pi*modelPhaseCurvatureLower σ)
        (2*Real.pi*(σ+1))*(Real.sqrt T+N/Real.sqrt T) :=
  @TaoTrudgianYang2025.norm_modelPhaseCore_le σ δ T N A F L hσ hT hN hδ hF hstart hend hL hscale

-- BetaFiniteSum: norm_sum_Icc_le_interior_add_three
example
    (z : ℕ → ℂ) (hz : ∀ n, ‖z n‖ ≤ 1) (a L : ℕ) :
    ‖∑ n ∈ Finset.Icc a (a+L+3), z n‖ ≤
      ‖∑ n ∈ Finset.range (L+1), z (a+1+n)‖+3 :=
  @TaoTrudgianYang2025.norm_sum_Icc_le_interior_add_three z hz a L

-- BetaModelSumBound: modelPhaseSumConstant_pos
example {σ : ℝ} (hσ : 0 < σ) :
    0 < modelPhaseSumConstant σ :=
  @TaoTrudgianYang2025.modelPhaseSumConstant_pos σ hσ

-- BetaModelSumBound: norm_exponentialSumAt_le_secondDerivative
example
    {σ δ T N : ℝ} {F : ℝ → ℝ} {a b : ℕ}
    (hσ : 0 < σ) (hT : 1 ≤ T) (hN : 1 ≤ N)
    (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N)
    (hscale : T ≤ N^2) :
    ‖exponentialSumAt F T N a b‖ ≤
      modelPhaseSumConstant σ*(Real.sqrt T+N/Real.sqrt T) :=
  @TaoTrudgianYang2025.norm_exponentialSumAt_le_secondDerivative σ δ T N F a b hσ hT hN hδ hF ha hb hscale

-- BetaClosedDuality: exponentSumGrowthExponent_zero
example :
    exponentSumGrowthExponent 0 = 0 :=
  @TaoTrudgianYang2025.exponentSumGrowthExponent_zero

-- BetaClosedDuality: exponentSumGrowthExponent_one_le_half
example :
    exponentSumGrowthExponent 1 ≤ (1 : ℝ)/2 :=
  @TaoTrudgianYang2025.exponentSumGrowthExponent_one_le_half

-- BetaClosedDuality: exponentSumGrowthExponent_le_exponentPairLine_closed
example
    {k l : ℝ} (hkl : ExponentPair k l) (α : ℝ≥0)
    (hα : (α : ℝ) ≤ 1) :
    exponentSumGrowthExponent α ≤ exponentPairLine k l α :=
  @TaoTrudgianYang2025.exponentSumGrowthExponent_le_exponentPairLine_closed k l hkl α hα

-- BetaClosedDuality: exponentPair_iff_beta_bound
example {k l : ℝ}
    (htri : InExponentPairTriangle k l) :
    ExponentPair k l ↔
      ∀ α : ℝ≥0, (α : ℝ) ≤ 1 →
        exponentSumGrowthExponent α ≤ exponentPairLine k l α :=
  @TaoTrudgianYang2025.exponentPair_iff_beta_bound k l htri

-- Closed endpoints consume the actual exponent-pair predicate.
example {k l : ℝ} (h : ExponentPair k l) :
    exponentSumGrowthExponent 0 ≤ k := by
  simpa [exponentPairLine] using
    exponentSumGrowthExponent_le_exponentPairLine_closed h 0 (by norm_num)

example {k l : ℝ} (h : ExponentPair k l) :
    exponentSumGrowthExponent 1 ≤ l := by
  simpa [exponentPairLine] using
    exponentSumGrowthExponent_le_exponentPairLine_closed h 1 (by norm_num)

example : exponentSumGrowthExponent 0 = 0 :=
  TaoTrudgianYang2025.exponentSumGrowthExponent_zero

example : exponentSumGrowthExponent 1 ≤ (1 : ℝ)/2 :=
  exponentSumGrowthExponent_one_le_half

-- Compactness returns the uniform physical-parameter estimate, not a
-- separately assumed exponent-pair object.
example {k l : ℝ} (htri : InExponentPairTriangle k l)
    (hβ : ∀ α : ℝ≥0, (α : ℝ) ≤ 1 →
      exponentSumGrowthExponent α ≤ exponentPairLine k l α) :
    IsExponentPairEstimateNonAsymptotic k l :=
  isExponentPairEstimateNonAsymptotic_of_beta_bound htri hβ

-- A genuine model sum at T=N, with both closed-interval endpoints retained.
example {σ δ N : ℝ} {F : ℝ → ℝ} {a b : ℕ}
    (hσ : 0 < σ) (hN : 1 ≤ N)
    (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N) :
    ‖exponentialSumAt F N N a b‖ ≤ (2*modelPhaseSumConstant σ)*Real.sqrt N := by
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hs : N/Real.sqrt N = Real.sqrt N := by
    apply (div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr hNp))).2
    nlinarith [Real.sq_sqrt hNp.le]
  have h := norm_exponentialSumAt_le_secondDerivative hσ hN hN hδ hF ha hb
    (by nlinarith : N ≤ N^2)
  rw [hs] at h
  convert h using 1
  ring

end ClosedBetaDualityRegression

namespace ExactBetaEndpointRegression

open Expdb Filter Topology

-- BetaLogCoherence: log_one_add_quadratic_remainder
example {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ x-Real.log (1+x) ∧ x-Real.log (1+x) ≤ x^2 :=
  @TaoTrudgianYang2025.log_one_add_quadratic_remainder x hx

-- BetaLogCoherence: logPhase_integer_remainder
example {N d : ℝ}
    (hN : 0 < N) (hd : 0 ≤ d) :
    |N*Real.log ((N+d)/N)-d| ≤ d^2/N :=
  @TaoTrudgianYang2025.logPhase_integer_remainder N d hN hd

-- BetaLogCoherence: oscillatory_log_re_eq_cos_remainder
example (N : ℝ) (j : ℕ) :
    (oscillatory Real.log N N (N+j)).re =
      Real.cos (2*Real.pi*(N*Real.log ((N+j)/N)-j)) :=
  @TaoTrudgianYang2025.oscillatory_log_re_eq_cos_remainder N j

-- BetaLogCoherence: oscillatory_log_re_ge_half
example {N : ℝ} (hN : 0 < N) (j : ℕ)
    (hsmall : (j : ℝ)^2/N ≤ 1/16) :
    (1 : ℝ)/2 ≤ (oscillatory Real.log N N (N+j)).re :=
  @TaoTrudgianYang2025.oscillatory_log_re_ge_half N hN j hsmall

-- BetaResonantSum: betaResonantScale_cast
example (m : ℕ) :
    (betaResonantScale m : ℝ) = 16*((m : ℝ)+1)^2 :=
  @TaoTrudgianYang2025.betaResonantScale_cast m

-- BetaResonantSum: betaResonantScale_one_le
example (m : ℕ) :
    1 ≤ (betaResonantScale m : ℝ) :=
  @TaoTrudgianYang2025.betaResonantScale_one_le m

-- BetaResonantSum: betaResonantScale_index_le
example (m : ℕ) :
    (m : ℝ) ≤ (betaResonantScale m : ℝ) :=
  @TaoTrudgianYang2025.betaResonantScale_index_le m

-- BetaResonantSum: betaResonantScale_sqrt
example (m : ℕ) :
    Real.sqrt (betaResonantScale m) = 4*((m : ℝ)+1) :=
  @TaoTrudgianYang2025.betaResonantScale_sqrt m

-- BetaResonantSum: betaResonantScale_small
example (m j : ℕ) (hj : j ≤ m) :
    (j : ℝ)^2/(betaResonantScale m : ℝ) ≤ 1/16 :=
  @TaoTrudgianYang2025.betaResonantScale_small m j hj

-- BetaResonantSum: betaResonantScale_tendsto
example :
    Tendsto (fun m => (betaResonantScale m : ℝ)) atTop atTop :=
  @TaoTrudgianYang2025.betaResonantScale_tendsto

-- BetaResonantSum: norm_logPhase_resonant_sum_lower
example (m : ℕ) :
    Real.sqrt (betaResonantScale m)/8 ≤
      ‖exponentialSumAt Real.log (betaResonantScale m) (betaResonantScale m)
        (betaResonantScale m) (betaResonantScale m+m)‖ :=
  @TaoTrudgianYang2025.norm_logPhase_resonant_sum_lower m

-- BetaEndpoints: half_le_exponentSumGrowthExponent_one
example :
    (1 : ℝ)/2 ≤ exponentSumGrowthExponent 1 :=
  @TaoTrudgianYang2025.half_le_exponentSumGrowthExponent_one

-- BetaEndpoints: exponentSumGrowthExponent_one
example :
    exponentSumGrowthExponent 1 = (1 : ℝ)/2 :=
  @TaoTrudgianYang2025.exponentSumGrowthExponent_one

-- BetaEndpoints: exponentSumGrowthExponent_endpoints
example :
    exponentSumGrowthExponent 0 = 0 ∧ exponentSumGrowthExponent 1 = (1 : ℝ)/2 :=
  @TaoTrudgianYang2025.exponentSumGrowthExponent_endpoints

-- ClassicalSecondDerivativePair: isExponentPairEstimateNonAsymptotic_half_half
example :
    IsExponentPairEstimateNonAsymptotic ((1 : ℝ)/2) ((1 : ℝ)/2) :=
  @TaoTrudgianYang2025.isExponentPairEstimateNonAsymptotic_half_half

-- ClassicalSecondDerivativePair: exponentPair_half_half
example : ExponentPair ((1 : ℝ)/2) ((1 : ℝ)/2) :=
  @TaoTrudgianYang2025.exponentPair_half_half

-- ClassicalSecondDerivativePair: exponentSumGrowthExponent_le_half
example {α : ℝ≥0} (hα : (α : ℝ) ≤ 1) :
    exponentSumGrowthExponent α ≤ (1 : ℝ)/2 :=
  @TaoTrudgianYang2025.exponentSumGrowthExponent_le_half α hα

-- ClassicalSecondDerivativePair: exponentSumGrowthExponent_le_min_self_half
example {α : ℝ≥0} (hα : (α : ℝ) ≤ 1) :
    exponentSumGrowthExponent α ≤ min (α : ℝ) ((1 : ℝ)/2) :=
  @TaoTrudgianYang2025.exponentSumGrowthExponent_le_min_self_half α hα

-- Nontrivial actual closed-interval logarithmic sum, not merely a scale inequality.
example : 1 ≤ ‖exponentialSumAt Real.log 64 64 64 65‖ := by
  have h := norm_logPhase_resonant_sum_lower 1
  norm_num [betaResonantScale] at h
  exact h

example : exponentSumGrowthExponent (1/2) ≤ (1 : ℝ)/2 :=
  exponentSumGrowthExponent_le_half (by norm_num)

example : exponentSumGrowthExponent 1 ≤ (1 : ℝ)/2 := by
  exact (le_min_iff.mp
    (exponentSumGrowthExponent_le_min_self_half (α := 1) (by norm_num))).2

-- The seed supplies the actual asymptotic estimate, not triangle membership.
example : IsExponentPairEstimate ((1 : ℝ)/2) ((1 : ℝ)/2) :=
  exponentPair_half_half.estimate

-- These are only the two boundary cases of reflection; the interior identity stays open.
example : exponentSumGrowthExponent 1 = (1 : ℝ)/2+exponentSumGrowthExponent 0 := by
  rw [exponentSumGrowthExponent_one,exponentSumGrowthExponent_zero,add_zero]

example : exponentSumGrowthExponent 0 = (1 : ℝ)/2-1+exponentSumGrowthExponent 1 := by
  rw [exponentSumGrowthExponent_one,exponentSumGrowthExponent_zero]
  norm_num

end ExactBetaEndpointRegression

namespace ModelLegendreRegression
open Set Expdb Filter
open scoped Topology ContDiff

example {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) :
    ContDiffAt ℝ ∞ F u :=
  @TaoTrudgianYang2025.approximateModelPhase_contDiffAt σ δ P F hF u hu

example {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) :
    ContDiffAt ℝ ∞ (deriv F) u :=
  @TaoTrudgianYang2025.approximateModelPhase_deriv_contDiffAt σ δ P F hF u hu

example {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) :
    StrictAntiOn (deriv F) (Ioo (1 : ℝ) 2) :=
  @TaoTrudgianYang2025.approximateModelPhase_deriv_strictAntiOn σ δ F hσ hδ hF

example {F : ℝ → ℝ} {v : ℝ}
    (hv : v ∈ modelPhaseSlopeRange F) :
    modelPhaseInverseSlope F v ∈ Ioo (1 : ℝ) 2 :=
  @TaoTrudgianYang2025.modelPhaseInverseSlope_mem F v hv

example {F : ℝ → ℝ} {v : ℝ}
    (hv : v ∈ modelPhaseSlopeRange F) :
    deriv F (modelPhaseInverseSlope F v) = v :=
  @TaoTrudgianYang2025.deriv_modelPhaseInverseSlope_apply F v hv

example {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) :
    modelPhaseInverseSlope F (deriv F u) = u :=
  @TaoTrudgianYang2025.modelPhaseInverseSlope_deriv σ δ F hσ hδ hF u hu

example {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) :
    deriv (deriv F) u ≠ 0 :=
  @TaoTrudgianYang2025.approximateModelPhase_secondDeriv_ne_zero σ δ F hσ hδ hF u hu

example {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) :
    HasStrictDerivAt (modelPhaseInverseSlope F)
      (deriv (deriv F) (modelPhaseInverseSlope F v))⁻¹ v :=
  @TaoTrudgianYang2025.modelPhaseInverseSlope_hasStrictDerivAt σ δ F hσ hδ hF v hv

example {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) (hb : b < 2) :
    Ioo (deriv F b) (deriv F a) ⊆ modelPhaseSlopeRange F :=
  @TaoTrudgianYang2025.modelPhaseSlopeRange_contains_interval σ δ P F hF a b ha hab hb

example {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) :
    IsOpen (modelPhaseSlopeRange F) :=
  @TaoTrudgianYang2025.modelPhaseSlopeRange_isOpen σ δ F hσ hδ hF

example {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) :
    ContDiffAt ℝ ∞ (modelPhaseInverseSlope F) v :=
  @TaoTrudgianYang2025.modelPhaseInverseSlope_contDiffAt σ δ F hσ hδ hF v hv

example {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) :
    ContDiffAt ℝ ∞ (modelPhaseLegendreDual F) v :=
  @TaoTrudgianYang2025.modelPhaseLegendreDual_contDiffAt σ δ F hσ hδ hF v hv

example {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) :
    HasDerivAt (modelPhaseLegendreDual F) (modelPhaseInverseSlope F v) v :=
  @TaoTrudgianYang2025.modelPhaseLegendreDual_hasDerivAt σ δ F hσ hδ hF v hv

example {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) :
    deriv (modelPhaseLegendreDual F) v = modelPhaseInverseSlope F v :=
  @TaoTrudgianYang2025.deriv_modelPhaseLegendreDual σ δ F hσ hδ hF v hv

example {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) :
    HasDerivAt (deriv (modelPhaseLegendreDual F))
      (deriv (deriv F) (modelPhaseInverseSlope F v))⁻¹ v :=
  @TaoTrudgianYang2025.modelPhaseLegendreDual_deriv_hasDerivAt σ δ F hσ hδ hF v hv

example {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) :
    deriv (deriv (modelPhaseLegendreDual F)) v =
      (deriv (deriv F) (modelPhaseInverseSlope F v))⁻¹ :=
  @TaoTrudgianYang2025.modelPhaseLegendreDual_secondDeriv σ δ F hσ hδ hF v hv

example {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) :
    (σ+1)⁻¹ ≤ -deriv (deriv (modelPhaseLegendreDual F)) v ∧
      -deriv (deriv (modelPhaseLegendreDual F)) v ≤ (modelPhaseCurvatureLower σ)⁻¹ :=
  @TaoTrudgianYang2025.modelPhaseLegendreDual_curvature_bounds σ δ F hσ hδ hF v hv

example {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) :
    modelPhaseLegendreDual F (deriv F u) = deriv F u * u - F u :=
  @TaoTrudgianYang2025.modelPhaseLegendreDual_at_deriv σ δ F hσ hδ hF u hu

example {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) :
    F u - deriv F u * u = -modelPhaseLegendreDual F (deriv F u) :=
  @TaoTrudgianYang2025.modelPhaseLegendreDual_stationary_sign σ δ F hσ hδ hF u hu

example {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) :
    |deriv F u - u^(-σ)| ≤ δ :=
  @TaoTrudgianYang2025.approximateModelPhase_firstDeriv_error σ δ P F hF u hu

example {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {u w : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) (hw : w ∈ Ioo (1 : ℝ) 2)
    (huw : u ≤ w) :
    modelPhaseCurvatureLower σ * (w-u) ≤ deriv F u - deriv F w :=
  @TaoTrudgianYang2025.approximateModelPhase_slope_gap σ δ F hσ hδ hF u w hu hw huw

example {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {u w : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) (hw : w ∈ Ioo (1 : ℝ) 2) :
    modelPhaseCurvatureLower σ * |u-w| ≤ |deriv F u - deriv F w| :=
  @TaoTrudgianYang2025.approximateModelPhase_slope_gap_abs σ δ F hσ hδ hF u w hu hw

example {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v w : ℝ} (hv : v ∈ modelPhaseSlopeRange F) (hw : w ∈ Ioo (1 : ℝ) 2) :
    |modelPhaseInverseSlope F v - w| ≤
      |v - deriv F w| / modelPhaseCurvatureLower σ :=
  @TaoTrudgianYang2025.modelPhaseInverseSlope_distance_le σ δ F hσ hδ hF v w hv hw

example
    {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) (hb : b < 2) :
    Ioo (b^(-σ)+δ) (a^(-σ)-δ) ⊆ modelPhaseSlopeRange F :=
  @TaoTrudgianYang2025.modelPhaseSlopeRange_contains_trimmed_model_interval σ δ P F hF a b ha hab hb

example {σ v : ℝ} (hσ : 0 < σ)
    (hv : v ∈ Ioo ((2 : ℝ)^(-σ)) 1) :
    v^(-σ⁻¹) ∈ Ioo (1 : ℝ) 2 :=
  @TaoTrudgianYang2025.reciprocal_modelPhase_mem σ v hσ hv

example {σ v : ℝ} (hσ : 0 < σ) (hv : 0 ≤ v) :
    (v^(-σ⁻¹))^(-σ) = v :=
  @TaoTrudgianYang2025.reciprocal_modelPhase_identity σ v hσ hv

example {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F)
    (hvModel : v ∈ Ioo ((2 : ℝ)^(-σ)) 1) :
    |modelPhaseInverseSlope F v - v^(-σ⁻¹)| ≤ δ / modelPhaseCurvatureLower σ :=
  @TaoTrudgianYang2025.modelPhaseInverseSlope_model_error σ δ F hσ hδ hF v hv hvModel

example {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F)
    (hvModel : v ∈ Ioo ((2 : ℝ)^(-σ)) 1) :
    |deriv (modelPhaseLegendreDual F) v - v^(-σ⁻¹)| ≤
      δ / modelPhaseCurvatureLower σ :=
  @TaoTrudgianYang2025.modelPhaseLegendreDual_firstDeriv_model_error σ δ F hσ hδ hF v hv hvModel

example {F : ℝ → ℝ} {T N r : ℝ}
    (hN : 0 < N) (hv : r*N/T ∈ modelPhaseSlopeRange F) :
    modelPhaseStationaryPoint F T N r ∈ Ioo N (2*N) :=
  @TaoTrudgianYang2025.modelPhaseStationaryPoint_mem F T N r hN hv

example {F : ℝ → ℝ} {T N r : ℝ}
    (hN : N ≠ 0) :
    modelPhaseStationaryPoint F T N r / N = modelPhaseInverseSlope F (r*N/T) :=
  @TaoTrudgianYang2025.modelPhaseStationaryPoint_div F T N r hN

example
    {σ δ T N r x : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hx : x/N ∈ Ioo (1 : ℝ) 2) :
    HasDerivAt (modelPhaseFrequencyPhase F T N r) (T/N*deriv F (x/N)-r) x :=
  @TaoTrudgianYang2025.modelPhaseFrequencyPhase_hasDerivAt σ δ T N r x P F hF hx

example
    {σ δ T N r : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hT : T ≠ 0) (hN : N ≠ 0)
    (hv : r*N/T ∈ modelPhaseSlopeRange F) :
    HasDerivAt (modelPhaseFrequencyPhase F T N r) 0
      (modelPhaseStationaryPoint F T N r) :=
  @TaoTrudgianYang2025.modelPhaseStationaryPoint_hasDerivAt σ δ T N r P F hF hT hN hv

example
    {σ δ T N r x : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : T ≠ 0) (hN : 0 < N)
    (hx : x ∈ Ioo N (2*N))
    (hcrit : deriv (modelPhaseFrequencyPhase F T N r) x = 0) :
    x = modelPhaseStationaryPoint F T N r :=
  @TaoTrudgianYang2025.modelPhaseStationaryPoint_unique σ δ T N r x F hσ hδ hF hT hN hx hcrit

example
    {F : ℝ → ℝ} {T N r : ℝ} (hT : T ≠ 0) (hN : N ≠ 0) :
    modelPhaseFrequencyPhase F T N r (modelPhaseStationaryPoint F T N r) =
      -T * modelPhaseLegendreDual F (r*N/T) :=
  @TaoTrudgianYang2025.modelPhaseStationaryPoint_phase F T N r hT hN

example
    {σ δ T N r x : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hx : x/N ∈ Ioo (1 : ℝ) 2) :
    deriv (deriv (modelPhaseFrequencyPhase F T N r)) x =
      T/N^2 * deriv (deriv F) (x/N) :=
  @TaoTrudgianYang2025.modelPhaseFrequencyPhase_secondDeriv σ δ T N r x P F hF hx

example
    {σ δ T N r : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N)
    (hv : r*N/T ∈ modelPhaseSlopeRange F) :
    (T/N^2)*modelPhaseCurvatureLower σ ≤
        -deriv (deriv (modelPhaseFrequencyPhase F T N r))
          (modelPhaseStationaryPoint F T N r) ∧
      -deriv (deriv (modelPhaseFrequencyPhase F T N r))
          (modelPhaseStationaryPoint F T N r) ≤ (T/N^2)*(σ+1) :=
  @TaoTrudgianYang2025.modelPhaseStationaryPoint_curvature σ δ T N r F hσ hδ hF hT hN hv

example
    {F : ℝ → ℝ} {T N r : ℝ} (hT : T ≠ 0) (hN : N ≠ 0) :
    𝐞 (modelPhaseFrequencyPhase F T N r (modelPhaseStationaryPoint F T N r)) =
      starRingEnd ℂ (𝐞 (T * modelPhaseLegendreDual F (r*N/T))) :=
  @TaoTrudgianYang2025.modelPhaseStationaryPoint_fourier_sign F T N r hT hN


private theorem logarithmicModel : IsApproximateModelPhaseFunction Real.log 1 1 0 := by
  refine ⟨isModelPhaseFunction_log.1 0, ?_⟩
  intro p _ u
  simp only [modelPhaseErrorAt, iteratedDerivWithin_log_eq_rpow_neg_one, sub_self, norm_zero]
  exact le_rfl

private theorem logarithmicSmallError : (0 : ℝ) ≤ min (modelPhaseCurvatureLower 1) 1 :=
  le_min (modelPhaseCurvatureLower_pos (by norm_num)).le zero_le_one

example : modelPhaseInverseSlope Real.log ((2 : ℝ)/3) = (3 : ℝ)/2 := by
  have h := modelPhaseInverseSlope_deriv (by norm_num : (0 : ℝ) < 1)
    logarithmicSmallError logarithmicModel (u := (3 : ℝ)/2) (by norm_num)
  norm_num [Real.deriv_log] at h
  exact h

example : modelPhaseLegendreDual Real.log ((2 : ℝ)/3) = 1-Real.log ((3 : ℝ)/2) := by
  have h := modelPhaseLegendreDual_at_deriv (by norm_num : (0 : ℝ) < 1)
    logarithmicSmallError logarithmicModel (u := (3 : ℝ)/2) (by norm_num)
  norm_num [Real.deriv_log] at h
  exact h

example : modelPhaseStationaryPoint Real.log 9 6 1 = 9 := by
  have h := modelPhaseInverseSlope_deriv (by norm_num : (0 : ℝ) < 1)
    logarithmicSmallError logarithmicModel (u := (3 : ℝ)/2) (by norm_num)
  norm_num [Real.deriv_log] at h
  norm_num [modelPhaseStationaryPoint, h]

example : HasDerivAt (modelPhaseFrequencyPhase Real.log 9 6 1) 0 9 := by
  have hx : modelPhaseStationaryPoint Real.log 9 6 1 = 9 := by
    have h := modelPhaseInverseSlope_deriv (by norm_num : (0 : ℝ) < 1)
      logarithmicSmallError logarithmicModel (u := (3 : ℝ)/2) (by norm_num)
    norm_num [Real.deriv_log] at h
    norm_num [modelPhaseStationaryPoint, h]
  have hv : (1 : ℝ)*6/9 ∈ modelPhaseSlopeRange Real.log := by
    refine ⟨(3 : ℝ)/2, by norm_num, ?_⟩
    norm_num [Real.deriv_log]
  have hd := modelPhaseStationaryPoint_hasDerivAt logarithmicModel
    (by norm_num : (9 : ℝ) ≠ 0) (by norm_num : (6 : ℝ) ≠ 0) hv
  rw [hx] at hd
  exact hd

example {σ : ℝ} {F : ℝ → ℝ} (hσ : 0 < σ)
    (hF : IsApproximateModelPhaseFunction F σ 1 0)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F)
    (hm : v ∈ Ioo ((2 : ℝ)^(-σ)) 1) :
    deriv (modelPhaseLegendreDual F) v = v^(-σ⁻¹) := by
  have he := modelPhaseLegendreDual_firstDeriv_model_error hσ
    (le_min (modelPhaseCurvatureLower_pos hσ).le zero_le_one) hF hv hm
  rw [zero_div, abs_le] at he
  linarith [he.1, he.2]

end ModelLegendreRegression

namespace AllOrderLegendreRegression
open Set Expdb Filter
open scoped Topology ContDiff BigOperators

example (e : InversePhaseExpression) {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ inversePhaseMagnitude e B :=
  @TaoTrudgianYang2025.inversePhaseMagnitude_nonneg e B hB

example (e : InversePhaseExpression) {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ inversePhaseSensitivity e B :=
  @TaoTrudgianYang2025.inversePhaseSensitivity_nonneg e B hB

example (e : InversePhaseExpression) {B : ℝ} {x : ℕ → ℝ}
    (hx : ∀ j ≤ inversePhaseOrder e, |x j| ≤ B) :
    |inversePhaseEval e x| ≤ inversePhaseMagnitude e B :=
  @TaoTrudgianYang2025.inversePhaseEval_abs_le e B x hx

example (e : InversePhaseExpression)
    {B ε : ℝ} {x y : ℕ → ℝ} (hB : 0 ≤ B)
    (hx : ∀ j ≤ inversePhaseOrder e, |x j| ≤ B)
    (hy : ∀ j ≤ inversePhaseOrder e, |y j| ≤ B)
    (hxy : ∀ j ≤ inversePhaseOrder e, |x j-y j| ≤ ε) :
    |inversePhaseEval e x - inversePhaseEval e y| ≤ inversePhaseSensitivity e B * ε :=
  @TaoTrudgianYang2025.inversePhaseEval_difference_le e B ε x y hB hx hy hxy

example {F : ℝ → ℝ} {u : ℝ}
    (hF : ContDiffAt ℝ ∞ F u) (n : ℕ) :
    ContDiffAt ℝ ∞ (iteratedDeriv n F) u :=
  @TaoTrudgianYang2025.contDiffAt_iteratedDeriv_infty F u hF n

example
    {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) (n : ℕ) :
    ContDiffAt ℝ ∞ (iteratedDeriv n F) u :=
  @TaoTrudgianYang2025.approximateModelPhase_iteratedDeriv_contDiffAt σ δ P F hF u hu n

example
    {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) (j : ℕ) :
    HasDerivAt (fun w => modelPhaseInverseJet F w j)
      (inversePhaseEval (inversePhaseAtomDerivative j) (modelPhaseInverseJet F v)) v :=
  @TaoTrudgianYang2025.modelPhaseInverseJet_hasDerivAt σ δ F hσ hδ hF v hv j

example
    {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) (e : InversePhaseExpression) :
    HasDerivAt (fun w => inversePhaseEval e (modelPhaseInverseJet F w))
      (inversePhaseEval (inversePhaseDifferentiate e) (modelPhaseInverseJet F v)) v :=
  @TaoTrudgianYang2025.inversePhaseEval_modelPhaseInverseJet_hasDerivAt σ δ F hσ hδ hF v hv e

example
    {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) (n : ℕ) :
    iteratedDeriv n (modelPhaseInverseSlope F) v =
      inversePhaseEval (inversePhaseDerivativeExpression n) (modelPhaseInverseJet F v) :=
  @TaoTrudgianYang2025.iteratedDeriv_modelPhaseInverseSlope_formula σ δ F hσ hδ hF v hv n

example
    {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) (n : ℕ) :
    iteratedDeriv (n+1) (modelPhaseLegendreDual F) v =
      inversePhaseEval (inversePhaseDerivativeExpression n) (modelPhaseInverseJet F v) :=
  @TaoTrudgianYang2025.iteratedDeriv_modelPhaseLegendreDual_formula σ δ F hσ hδ hF v hv n

example (σ : ℝ) {u : ℝ} (hu : 0 < u) :
    ContDiffAt ℝ ∞ (referenceModelPrimitive σ) u :=
  @TaoTrudgianYang2025.referenceModelPrimitive_contDiffAt σ u hu

example (σ : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (referenceModelPrimitive σ) (u^(-σ)) u :=
  @TaoTrudgianYang2025.referenceModelPrimitive_hasDerivAt σ u hu

example (σ : ℝ) {u : ℝ} (hu : 0 < u) (p : ℕ) :
    iteratedDeriv (p+1) (referenceModelPrimitive σ) u =
      iteratedDeriv p (modelPhase σ) u :=
  @TaoTrudgianYang2025.referenceModelPrimitive_iteratedDeriv σ u hu p

example (σ : ℝ) (P : ℕ) :
    IsApproximateModelPhaseFunction (referenceModelPrimitive σ) σ P 0 :=
  @TaoTrudgianYang2025.referenceModelPrimitive_approximate σ P

example {σ v : ℝ} (hσ : 0 < σ)
    (hv : v ∈ Ioo ((2 : ℝ)^(-σ)) 1) :
    modelPhaseInverseSlope (referenceModelPrimitive σ) v = v^(-σ⁻¹) :=
  @TaoTrudgianYang2025.referenceModelPrimitive_inverse σ v hσ hv

example {σ v : ℝ} (hσ : 0 < σ)
    (hv : v ∈ Ioo ((2 : ℝ)^(-σ)) 1) :
    v ∈ modelPhaseSlopeRange (referenceModelPrimitive σ) :=
  @TaoTrudgianYang2025.referenceModelPrimitive_slopeRange σ v hσ hv

example {σ v : ℝ} (hσ : 0 < σ)
    (hv : v ∈ Ioo ((2 : ℝ)^(-σ)) 1) (n : ℕ) :
    iteratedDeriv n (modelPhase σ⁻¹) v =
      inversePhaseEval (inversePhaseDerivativeExpression n)
        (modelPhaseInverseJet (referenceModelPrimitive σ) v) :=
  @TaoTrudgianYang2025.referenceModelPrimitive_inverseJet_formula σ v hσ hv n

example (σ : ℝ) (p : ℕ) :
    0 ≤ modelPhaseJetCoefficient σ p :=
  @TaoTrudgianYang2025.modelPhaseJetCoefficient_nonneg σ p

example
    {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) (p : ℕ) (hp : p ≤ P) :
    |iteratedDeriv (p+1) F u - iteratedDeriv p (modelPhase σ) u| ≤ δ :=
  @TaoTrudgianYang2025.approximateModelPhase_iteratedDeriv_error σ δ P F hF u hu p hp

example {σ : ℝ} (hσ : 0 ≤ σ)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) (p : ℕ) :
    |iteratedDeriv p (modelPhase σ) u| ≤ modelPhaseJetCoefficient σ p :=
  @TaoTrudgianYang2025.iteratedDeriv_modelPhase_abs_le σ hσ u hu p

example {σ : ℝ} (hσ : 0 ≤ σ)
    {u w : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) (hw : w ∈ Ioo (1 : ℝ) 2) (p : ℕ) :
    |iteratedDeriv p (modelPhase σ) u - iteratedDeriv p (modelPhase σ) w| ≤
      modelPhaseJetCoefficient σ (p+1) * |u-w| :=
  @TaoTrudgianYang2025.iteratedDeriv_modelPhase_lipschitz σ hσ u w hu hw p

example
    {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ} (hσ : 0 ≤ σ)
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    {u w : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) (hw : w ∈ Ioo (1 : ℝ) 2)
    (p : ℕ) (hp : p ≤ P) :
    |iteratedDeriv (p+1) F u -
      iteratedDeriv (p+1) (referenceModelPrimitive σ) w| ≤
      δ + modelPhaseJetCoefficient σ (p+1) * |u-w| :=
  @TaoTrudgianYang2025.approximateModelPhase_iteratedDeriv_reference_gap σ δ P F hσ hF u w hu hw p hp

example
    {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hP : 1 ≤ P) (hF : IsApproximateModelPhaseFunction F σ P δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F)
    (hm : v ∈ Ioo ((2 : ℝ)^(-σ)) 1) (p : ℕ) (hp : p ≤ P) :
    |iteratedDeriv (p+1) F (modelPhaseInverseSlope F v) -
      iteratedDeriv (p+1) (referenceModelPrimitive σ)
        (modelPhaseInverseSlope (referenceModelPrimitive σ) v)| ≤
      (1 + modelPhaseJetCoefficient σ (p+1) / modelPhaseCurvatureLower σ) * δ :=
  @TaoTrudgianYang2025.modelPhaseInverse_iteratedDeriv_reference_error σ δ P F hσ hδ hP hF v hv hm p hp

example {a b c : ℝ}
    (hc : 0 < c) (ha : c ≤ -a) (hb : c ≤ -b) :
    |a⁻¹-b⁻¹| ≤ |a-b|/c^2 :=
  @TaoTrudgianYang2025.inverse_difference_le_curvature a b c hc ha hb

example {σ : ℝ} (hσ : 0 < σ) (j : ℕ) :
    0 ≤ inverseJetMagnitude σ j :=
  @TaoTrudgianYang2025.inverseJetMagnitude_nonneg σ hσ j

example {σ : ℝ} (hσ : 0 < σ) (j : ℕ) :
    0 ≤ inverseJetError σ j :=
  @TaoTrudgianYang2025.inverseJetError_nonneg σ hσ j

example
    {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hP : 1 ≤ P) (hF : IsApproximateModelPhaseFunction F σ P δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) (j : ℕ) (hj : j ≤ P) :
    |modelPhaseInverseJet F v j| ≤ inverseJetMagnitude σ j :=
  @TaoTrudgianYang2025.modelPhaseInverseJet_abs_le σ δ P F hσ hδ hP hF v hv j hj

example
    {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hP : 1 ≤ P) (hF : IsApproximateModelPhaseFunction F σ P δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F)
    (hm : v ∈ Ioo ((2 : ℝ)^(-σ)) 1) (j : ℕ) (hj : j ≤ P) :
    |modelPhaseInverseJet F v j -
      modelPhaseInverseJet (referenceModelPrimitive σ) v j| ≤ inverseJetError σ j * δ :=
  @TaoTrudgianYang2025.modelPhaseInverseJet_reference_error σ δ P F hσ hδ hP hF v hv hm j hj

example {σ : ℝ} (hσ : 0 < σ) (K : ℕ) :
    0 ≤ inverseJetMagnitudeBudget σ K :=
  @TaoTrudgianYang2025.inverseJetMagnitudeBudget_nonneg σ hσ K

example {σ : ℝ} (hσ : 0 < σ) (K : ℕ) :
    0 ≤ inverseJetErrorBudget σ K :=
  @TaoTrudgianYang2025.inverseJetErrorBudget_nonneg σ hσ K

example {σ : ℝ} (hσ : 0 < σ) {K j : ℕ} (hj : j ≤ K) :
    inverseJetMagnitude σ j ≤ inverseJetMagnitudeBudget σ K :=
  @TaoTrudgianYang2025.inverseJetMagnitude_le_budget σ hσ K j hj

example {σ : ℝ} (hσ : 0 < σ) {K j : ℕ} (hj : j ≤ K) :
    inverseJetError σ j ≤ inverseJetErrorBudget σ K :=
  @TaoTrudgianYang2025.inverseJetError_le_budget σ hσ K j hj

example {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    0 ≤ legendreModelErrorConstant σ n :=
  @TaoTrudgianYang2025.legendreModelErrorConstant_nonneg σ hσ n

example
    {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ) :
    0 ≤ δ :=
  @TaoTrudgianYang2025.approximateModelPhase_tolerance_nonneg σ δ P F hF

example
    {σ δ : ℝ} {F : ℝ → ℝ} (n : ℕ)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ
      (inversePhaseOrder (inversePhaseDerivativeExpression n)+1) δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F)
    (hm : v ∈ Ioo ((2 : ℝ)^(-σ)) 1) :
    |iteratedDeriv (n+1) (modelPhaseLegendreDual F) v -
      iteratedDeriv n (modelPhase σ⁻¹) v| ≤ legendreModelErrorConstant σ n * δ :=
  @TaoTrudgianYang2025.modelPhaseLegendreDual_iteratedDeriv_model_error σ δ F n hσ hδ hF v hv hm

example {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    ∃ P : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ δ : ℝ, δ ≤ min (modelPhaseCurvatureLower σ) 1 →
      ∀ F : ℝ → ℝ, IsApproximateModelPhaseFunction F σ P δ →
      ∀ v : ℝ, v ∈ modelPhaseSlopeRange F → v ∈ Ioo ((2 : ℝ)^(-σ)) 1 →
        |iteratedDeriv (n+1) (modelPhaseLegendreDual F) v -
          iteratedDeriv n (modelPhase σ⁻¹) v| ≤ C*δ :=
  @TaoTrudgianYang2025.modelPhaseLegendreDual_allOrder_uniformity σ hσ n

example
    {σ δ a b : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (ha : (2 : ℝ)^(-σ) < a) (hab : a ≤ b) (hb : b < 1)
    (hδ : δ ≤ min ((a-(2 : ℝ)^(-σ))/4) ((1-b)/4))
    (hF : IsApproximateModelPhaseFunction F σ P δ) :
    Icc a b ⊆ modelPhaseSlopeRange F :=
  @TaoTrudgianYang2025.modelPhaseSlopeRange_contains_compact_model_interval σ δ a b P F hσ ha hab hb hδ hF

example {Q n : ℕ} (hn : n ≤ Q) :
    inversePhaseOrder (inversePhaseDerivativeExpression n)+1 ≤ legendreFiniteInputOrder Q :=
  @TaoTrudgianYang2025.legendreFiniteInputOrder_le Q n hn

example {σ : ℝ} (hσ : 0 < σ) (Q : ℕ) :
    0 < legendreFiniteErrorConstant σ Q :=
  @TaoTrudgianYang2025.legendreFiniteErrorConstant_pos σ hσ Q

example {σ : ℝ} (hσ : 0 < σ)
    {Q n : ℕ} (hn : n ≤ Q) :
    legendreModelErrorConstant σ n ≤ legendreFiniteErrorConstant σ Q :=
  @TaoTrudgianYang2025.legendreModelErrorConstant_le_finite σ hσ Q n hn

example
    {σ δ : ℝ} {F : ℝ → ℝ} (Q : ℕ)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ (legendreFiniteInputOrder Q) δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F)
    (hm : v ∈ Ioo ((2 : ℝ)^(-σ)) 1) {n : ℕ} (hn : n ≤ Q) :
    |iteratedDeriv (n+1) (modelPhaseLegendreDual F) v -
      iteratedDeriv n (modelPhase σ⁻¹) v| ≤ legendreFiniteErrorConstant σ Q * δ :=
  @TaoTrudgianYang2025.modelPhaseLegendreDual_finiteOrder_model_error σ δ F Q hσ hδ hF v hv hm n hn

example
    {σ a b : ℝ} (hσ : 0 < σ)
    (ha : (2 : ℝ)^(-σ) < a) (hab : a ≤ b) (hb : b < 1)
    (Q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ min (modelPhaseCurvatureLower σ) 1 ∧
      ∀ F : ℝ → ℝ,
        IsApproximateModelPhaseFunction F σ (legendreFiniteInputOrder Q) δ →
      ∀ v ∈ Icc a b, v ∈ modelPhaseSlopeRange F ∧
        ∀ n ≤ Q, |iteratedDeriv (n+1) (modelPhaseLegendreDual F) v -
          iteratedDeriv n (modelPhase σ⁻¹) v| ≤ ε :=
  @TaoTrudgianYang2025.modelPhaseLegendreDual_compact_uniformity σ a b hσ ha hab hb Q ε hε

example
    {σ δ a b ε : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hJ : Icc a b ⊆ modelPhaseSlopeRange F)
    (ha : (2 : ℝ)^(-σ) < a)
    (he : ∀ v ∈ Icc a b,
      |deriv (modelPhaseLegendreDual F) v-v^(-σ⁻¹)| ≤ ε)
    {v w : ℝ} (hv : v ∈ Icc a b) (hw : w ∈ Icc a b) :
    |anchoredLegendreError F σ w v| ≤ ε*|v-w| :=
  @TaoTrudgianYang2025.modelPhaseLegendreDual_anchored_error σ δ a b ε F hσ hδ hF hJ ha he v w hv hw

example
    {σ a b : ℝ} (hσ : 0 < σ)
    (ha : (2 : ℝ)^(-σ) < a) (hab : a ≤ b) (hb : b < 1)
    (Q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ min (modelPhaseCurvatureLower σ) 1 ∧
      ∀ F : ℝ → ℝ,
        IsApproximateModelPhaseFunction F σ (legendreFiniteInputOrder Q) δ →
      ∀ v ∈ Icc a b, v ∈ modelPhaseSlopeRange F ∧
        (∀ n ≤ Q, |iteratedDeriv (n+1) (modelPhaseLegendreDual F) v -
          iteratedDeriv n (modelPhase σ⁻¹) v| ≤ ε) ∧
        ∀ w ∈ Icc a b, |anchoredLegendreError F σ w v| ≤ ε*|v-w| :=
  @TaoTrudgianYang2025.modelPhaseLegendreDual_compact_anchored_uniformity σ a b hσ ha hab hb Q ε hε


example (x : ℕ → ℝ) :
    inversePhaseEval (inversePhaseDerivativeExpression 0) x = x 0 := rfl

example (x : ℕ → ℝ) :
    inversePhaseEval (inversePhaseDerivativeExpression 1) x = x 1 := rfl

example (x : ℕ → ℝ) :
    inversePhaseEval (inversePhaseDerivativeExpression 2) x = -x 3*(x 1)^3 := by
  simp only [inversePhaseDerivativeExpression, inversePhaseDifferentiate,
    inversePhaseAtomDerivative, inversePhaseEval]
  ring

example (x : ℕ → ℝ) :
    inversePhaseEval (inversePhaseDerivativeExpression 3) x =
      3*(x 3)^2*(x 1)^5-x 4*(x 1)^4 := by
  simp only [inversePhaseDerivativeExpression, inversePhaseDifferentiate,
    inversePhaseAtomDerivative, inversePhaseEval]
  ring

example : legendreFiniteInputOrder 2 = 7 := by
  norm_num [legendreFiniteInputOrder, inversePhaseDerivativeExpression,
    inversePhaseDifferentiate, inversePhaseAtomDerivative, inversePhaseOrder,
    Finset.sum_range_succ]

example {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) :
    iteratedDeriv 3 (modelPhaseLegendreDual F) v =
      -iteratedDeriv 3 F (modelPhaseInverseSlope F v) /
        (deriv (deriv F) (modelPhaseInverseSlope F v))^3 := by
  rw [iteratedDeriv_modelPhaseLegendreDual_formula hσ hδ hF hv 2]
  simp only [inversePhaseDerivativeExpression, inversePhaseDifferentiate,
    inversePhaseAtomDerivative, inversePhaseEval, modelPhaseInverseJet, div_eq_mul_inv]
  ring

example {σ : ℝ} {F : ℝ → ℝ} (n : ℕ) (hσ : 0 < σ)
    (hF : IsApproximateModelPhaseFunction F σ
      (inversePhaseOrder (inversePhaseDerivativeExpression n)+1) 0)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F)
    (hm : v ∈ Ioo ((2 : ℝ)^(-σ)) 1) :
    iteratedDeriv (n+1) (modelPhaseLegendreDual F) v =
      iteratedDeriv n (modelPhase σ⁻¹) v := by
  have he := modelPhaseLegendreDual_iteratedDeriv_model_error n hσ
    (le_min (modelPhaseCurvatureLower_pos hσ).le zero_le_one) hF hv hm
  rw [mul_zero, abs_le] at he
  linarith [he.1,he.2]

example {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ min (modelPhaseCurvatureLower 1) 1 ∧
      ∀ F : ℝ → ℝ, IsApproximateModelPhaseFunction F 1 (legendreFiniteInputOrder 2) δ →
      ∀ v ∈ Icc ((2 : ℝ)/3) ((3 : ℝ)/4), v ∈ modelPhaseSlopeRange F ∧
        (∀ n ≤ 2, |iteratedDeriv (n+1) (modelPhaseLegendreDual F) v -
          iteratedDeriv n (modelPhase 1) v| ≤ ε) ∧
        ∀ w ∈ Icc ((2 : ℝ)/3) ((3 : ℝ)/4),
          |anchoredLegendreError F 1 w v| ≤ ε*|v-w| := by
  simpa only [inv_one] using modelPhaseLegendreDual_compact_anchored_uniformity
    (by norm_num : (0 : ℝ) < 1)
    (by norm_num [Real.rpow_neg_one] : (2 : ℝ)^(-(1 : ℝ)) < (2 : ℝ)/3)
    (by norm_num : (2 : ℝ)/3 ≤ (3 : ℝ)/4)
    (by norm_num : (3 : ℝ)/4 < 1) 2 hε

end AllOrderLegendreRegression

section CanonicalLegendreExtensionRegression

open Set Expdb Filter
open scoped Topology ContDiff

example {l a b r : ℝ}
    (hla : l < a) (hab : a ≤ b) (hbr : b < r) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧
      (∀ x ∈ Icc a b, χ x = 1) ∧ tsupport χ ⊆ Ioo l r ∧
      HasCompactSupport χ ∧ ∀ x, 0 ≤ χ x ∧ χ x ≤ 1 :=
  @exists_smooth_interval_cutoff l a b r hla hab hbr

example {χ H : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ)
    (hH : ∀ x ∈ tsupport χ, ContDiffAt ℝ ∞ H x) :
    ContDiff ℝ ∞ (fun x => χ x * H x) :=
  @smoothCutoff_mul_contDiff χ H hχ hH

example {χ H : ℝ → ℝ}
    {x : ℝ} (hx : x ∉ tsupport χ) (n : ℕ) :
    iteratedDeriv n (fun y => χ y * H y) x = 0 :=
  @smoothCutoff_mul_iteratedDeriv_zero χ H x hx n

example (χ : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    0 ≤ cutoffOrderBudget χ n x :=
  @cutoffOrderBudget_nonneg χ n x

example (χ : ℝ → ℝ) {n Q : ℕ}
    (hn : n ≤ Q) (x : ℝ) :
    cutoffOrderBudget χ n x ≤ cutoffFiniteBudget χ Q x :=
  @cutoffOrderBudget_le_finite χ n Q hn x

example {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (Q : ℕ) : Continuous (cutoffFiniteBudget χ Q) :=
  @cutoffFiniteBudget_continuous χ hχ Q

example {χ H : ℝ → ℝ}
    {x ε : ℝ} (n : ℕ)
    (hχ : ContDiffAt ℝ n χ x) (hH : ContDiffAt ℝ n H x)
    (he : ∀ j ≤ n, |iteratedDeriv j H x| ≤ ε) :
    |iteratedDeriv n (fun y => χ y * H y) x| ≤ cutoffOrderBudget χ n x * ε :=
  @smoothCutoff_mul_iteratedDeriv_le χ H x ε n hχ hH he

example {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) {S : Set ℝ} (hS : IsCompact S)
    (hs : tsupport χ ⊆ S) (Q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : ℝ → ℝ) (ε : ℝ), 0 ≤ ε →
      (∀ x ∈ tsupport χ, ContDiffAt ℝ ∞ H x) →
      (∀ x ∈ tsupport χ, ∀ j ≤ Q, |iteratedDeriv j H x| ≤ ε) →
      ∀ x : ℝ, ∀ n ≤ Q, |iteratedDeriv n (fun y => χ y*H y) x| ≤ C*ε :=
  @smoothCutoff_uniform_derivative_bound χ hχ S hS hs Q

example
    {σ δ w v : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hp : 0 < v) :
    ContDiffAt ℝ ∞ (anchoredLegendreError F σ w) v :=
  @anchoredLegendreError_contDiffAt σ δ w v F hσ hδ hF hv hp

example
    {σ δ w v : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hp : 0 < v) (n : ℕ) :
    iteratedDeriv (n+1) (anchoredLegendreError F σ w) v =
      iteratedDeriv (n+1) (modelPhaseLegendreDual F) v -
        iteratedDeriv n (modelPhase σ⁻¹) v :=
  @anchoredLegendreError_iteratedDeriv σ δ w v F hσ hδ hF hv hp n

example {χ F : ℝ → ℝ} {σ w v : ℝ}
    (hχ : χ v = 1) :
    legendreCutoffCorrection χ F σ w v = anchoredLegendreError F σ w v :=
  @legendreCutoffCorrection_agrees χ F σ w v hχ

example
    {σ c d w : ℝ} (hσ : 0 < σ)
    (hc : (2 : ℝ)^(-σ) < c) (hcd : c ≤ d) (hd : d < 1)
    (hw : w ∈ Icc c d) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Icc c d)
    (Q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ min (modelPhaseCurvatureLower σ) 1 ∧
      ∀ F : ℝ → ℝ,
        IsApproximateModelPhaseFunction F σ (legendreFiniteInputOrder Q) δ →
      Icc c d ⊆ modelPhaseSlopeRange F ∧
      ContDiff ℝ ∞ (legendreCutoffCorrection χ F σ w) ∧
        ∀ v : ℝ, ∀ n ≤ Q,
          |iteratedDeriv n (legendreCutoffCorrection χ F σ w) v| ≤ ε :=
  @legendreCutoffCorrection_uniformity σ c d w hσ hc hcd hd hw χ hχ hs Q ε hε

example {H : ℝ → ℝ}
    (hH : ContDiff ℝ ∞ H) (s A : ℝ) :
    ContDiff ℝ ∞ (rescaledPhaseCorrection H s A) :=
  @rescaledPhaseCorrection_contDiff H hH s A

example {H : ℝ → ℝ}
    (hH : ContDiff ℝ ∞ H) (s A u : ℝ) (n : ℕ) :
    iteratedDeriv n (rescaledPhaseCorrection H s A) u =
      A^(s-1) * A^n * iteratedDeriv n H (A*u) :=
  @rescaledPhaseCorrection_iteratedDeriv H hH s A u n

example (s A : ℝ) (Q : ℕ) :
    0 < phaseRescalingBudget s A Q :=
  @phaseRescalingBudget_pos s A Q

example {H : ℝ → ℝ}
    (hH : ContDiff ℝ ∞ H) (s A : ℝ) {Q : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (he : ∀ x : ℝ, ∀ n ≤ Q, |iteratedDeriv n H x| ≤ ε)
    (u : ℝ) {n : ℕ} (hn : n ≤ Q) :
    |iteratedDeriv n (rescaledPhaseCorrection H s A) u| ≤
      phaseRescalingBudget s A Q * ε :=
  @rescaledPhaseCorrection_uniform_bound H hH s A Q ε hε he u n hn

example {H : ℝ → ℝ}
    (hH : ContDiff ℝ ∞ H) (s : ℝ) (P : ℕ) {ε : ℝ}
    (he : ∀ u ∈ Icc (1 : ℝ) 2, ∀ n ≤ P, |iteratedDeriv (n+1) H u| ≤ ε) :
    IsApproximateModelPhaseFunction (fun u => referenceModelPrimitive s u + H u)
      s P ε :=
  @referencePlusCorrection_approximate H hH s P ε he

example
    (s : ℝ) {A u v : ℝ} (hA : 0 < A) (hu : 0 < u) (hv : 0 < v) :
    A^(s-1) * (referenceModelPrimitive s (A*u) -
      referenceModelPrimitive s (A*v)) =
      referenceModelPrimitive s u - referenceModelPrimitive s v :=
  @referenceModelPrimitive_scaling_difference s A u v hA hu hv

example {χ F : ℝ → ℝ} {σ A w v : ℝ}
    (hA : 0 < A) (hw : 0 < w) (hv : 0 < v) (hχ : χ v = 1) :
    canonicalLegendrePhase χ F σ A w (v/A) =
      A^(σ⁻¹-1)*(modelPhaseLegendreDual F v-modelPhaseLegendreDual F w) +
        referenceModelPrimitive σ⁻¹ (w/A) :=
  @canonicalLegendrePhase_agrees χ F σ A w v hA hw hv hχ

example
    {σ c d w : ℝ} (hσ : 0 < σ)
    (hc : (2 : ℝ)^(-σ) < c) (hcd : c ≤ d) (hd : d < 1)
    (hw : w ∈ Icc c d) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Icc c d)
    (A : ℝ) (Q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ min (modelPhaseCurvatureLower σ) 1 ∧
      ∀ F : ℝ → ℝ,
        IsApproximateModelPhaseFunction F σ (legendreFiniteInputOrder (Q+1)) δ →
      Icc c d ⊆ modelPhaseSlopeRange F ∧
        IsApproximateModelPhaseFunction (canonicalLegendrePhase χ F σ A w)
          σ⁻¹ Q ε :=
  @canonicalLegendrePhase_uniformity σ c d w hσ hc hcd hd hw χ hχ hs A Q ε hε

example
    {σ a b : ℝ} (hσ : 0 < σ)
    (ha : (2 : ℝ)^(-σ) < a) (hab : a ≤ b) (hb : b < 1)
    (hr : b < 2*a) :
    ∃ A : ℝ, 0 < A ∧ A < a ∧ b < 2*A ∧
      ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
        (∀ v ∈ Icc a b, χ v = 1) ∧
        ∀ (Q : ℕ) (ε : ℝ), 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧ δ ≤ min (modelPhaseCurvatureLower σ) 1 ∧
          ∀ F : ℝ → ℝ,
            IsApproximateModelPhaseFunction F σ (legendreFiniteInputOrder (Q+1)) δ →
          Icc a b ⊆ modelPhaseSlopeRange F ∧
          IsApproximateModelPhaseFunction (canonicalLegendrePhase χ F σ A a) σ⁻¹ Q ε ∧
          ∀ v ∈ Icc a b, v/A ∈ Ioo (1 : ℝ) 2 ∧
            canonicalLegendrePhase χ F σ A a (v/A) =
              A^(σ⁻¹-1)*(modelPhaseLegendreDual F v-modelPhaseLegendreDual F a) +
                referenceModelPrimitive σ⁻¹ (a/A) :=
  @modelPhaseLegendreDual_canonical_extension σ a b hσ ha hab hb hr

example {σ x : ℝ}
    (hx : x ∈ Ioo ((2 : ℝ)^(-σ)) 1) :
    0 < legendreWindowRadius σ x ∧
      (2 : ℝ)^(-σ) < x-legendreWindowRadius σ x ∧
      x+legendreWindowRadius σ x < 1 ∧
      x+legendreWindowRadius σ x < 2*(x-legendreWindowRadius σ x) :=
  @legendreWindowRadius_properties σ x hx

example
    {σ a b : ℝ} (hσ : 0 < σ)
    (ha : (2 : ℝ)^(-σ) < a) (hab : a ≤ b) (hb : b < 1) :
    ∃ S : Finset (Icc a b), S.Nonempty ∧
      ∃ l r A : Icc a b → ℝ, ∃ χ : Icc a b → ℝ → ℝ,
      (∀ i ∈ S, (2 : ℝ)^(-σ) < l i ∧ l i ≤ r i ∧ r i < 1 ∧
        0 < A i ∧ A i < l i ∧ r i < 2*A i ∧
        ContDiff ℝ ∞ (χ i) ∧ HasCompactSupport (χ i) ∧
        ∀ v ∈ Icc (l i) (r i), χ i v = 1) ∧
      (∀ v ∈ Icc a b, ∃ i ∈ S, v ∈ Ioo (l i) (r i)) ∧
      ∀ (Q : ℕ) (ε : ℝ), 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ min (modelPhaseCurvatureLower σ) 1 ∧
        ∀ F : ℝ → ℝ,
          IsApproximateModelPhaseFunction F σ (legendreFiniteInputOrder (Q+1)) δ →
        ∀ i ∈ S, Icc (l i) (r i) ⊆ modelPhaseSlopeRange F ∧
          IsApproximateModelPhaseFunction
            (canonicalLegendrePhase (χ i) F σ (A i) (l i)) σ⁻¹ Q ε ∧
          ∀ v ∈ Icc (l i) (r i), v/A i ∈ Ioo (1 : ℝ) 2 ∧
            canonicalLegendrePhase (χ i) F σ (A i) (l i) (v/A i) =
              (A i)^(σ⁻¹-1)*
                (modelPhaseLegendreDual F v-modelPhaseLegendreDual F (l i)) +
                referenceModelPrimitive σ⁻¹ (l i/A i) :=
  @modelPhaseLegendreDual_finite_canonical_cover σ a b hσ ha hab hb

example
    {G : VariableFunction (VariableObject.fixed ℝ) ℝ} {s : ℝ}
    (hG : IsPhaseFunction G)
    (he : ∀ (P : ℕ) (ε : ℝ), 0 < ε →
      ∀ᶠ i in atTop, IsApproximateModelPhaseFunction (G i) s P ε) :
    IsModelPhaseFunctionWith G s :=
  @modelPhaseWith_of_eventual_approximation G s hG he

example
    {H : VariableFunction (VariableObject.fixed ℝ) ℝ} (s : ℝ)
    (he : ∀ (P : ℕ) (ε : ℝ), 0 < ε →
      ∀ᶠ i in atTop, IsApproximateModelPhaseFunction (H i) s P ε) :
    ∃ G : VariableFunction (VariableObject.fixed ℝ) ℝ,
      IsModelPhaseFunctionWith G s ∧ (∀ᶠ i : ℕ in atTop, G i = H i) :=
  @modelPhaseWith_finite_initial_repair H s he

example
    {σ a b : ℝ} (hσ : 0 < σ)
    (ha : (2 : ℝ)^(-σ) < a) (hab : a ≤ b) (hb : b < 1)
    (hr : b < 2*a)
    {F : VariableFunction (VariableObject.fixed ℝ) ℝ}
    (hF : IsModelPhaseFunctionWith F σ) :
    ∃ A : ℝ, 0 < A ∧ A < a ∧ b < 2*A ∧
      ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      ∃ G : VariableFunction (VariableObject.fixed ℝ) ℝ,
        IsModelPhaseFunctionWith G σ⁻¹ ∧ IsModelPhaseFunction G ∧
        ∀ᶠ i in atTop,
          G i = canonicalLegendrePhase χ (F i) σ A a ∧
          Icc a b ⊆ modelPhaseSlopeRange (F i) ∧
          ∀ v ∈ Icc a b, v/A ∈ Ioo (1 : ℝ) 2 ∧
            G i (v/A) =
              A^(σ⁻¹-1)*(modelPhaseLegendreDual (F i) v-modelPhaseLegendreDual (F i) a) +
                referenceModelPrimitive σ⁻¹ (a/A) :=
  @modelPhaseLegendreDual_canonical_family σ a b hσ ha hab hb hr F hF

-- A real cutoff includes both plateau endpoints and has buffered support.
example : ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧
    (∀ x ∈ Icc (1 : ℝ) 2, χ x = 1) ∧ tsupport χ ⊆ Ioo (0 : ℝ) 3 ∧
    HasCompactSupport χ ∧ ∀ x, 0 ≤ χ x ∧ χ x ≤ 1 :=
  exists_smooth_interval_cutoff (by norm_num) (by norm_num) (by norm_num)

example (χ : ℝ → ℝ) (x : ℝ) : cutoffOrderBudget χ 0 x = |χ x| := by
  simp [cutoffOrderBudget]

-- Multiplicative normalization retains the actual derivative scale.
example (u : ℝ) :
    iteratedDeriv 2 (rescaledPhaseCorrection (fun x => x^3) 1 2) u = 48*u := by
  rw [rescaledPhaseCorrection_iteratedDeriv (by fun_prop)]
  norm_num [iteratedDeriv_pow]
  ring

example :
    referenceModelPrimitive 1 6-referenceModelPrimitive 1 2 =
      referenceModelPrimitive 1 3-referenceModelPrimitive 1 1 := by
  convert referenceModelPrimitive_scaling_difference 1
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 3)
    (by norm_num : (0 : ℝ) < 1) using 1
  norm_num

-- This includes both closed canonical endpoints and arbitrary exponents.
example (s : ℝ) (P : ℕ) :
    IsApproximateModelPhaseFunction
      (fun u => referenceModelPrimitive s u+(0 : ℝ)) s P 0 := by
  apply referencePlusCorrection_approximate contDiff_const
  intro u _ n _
  simp

example :
    ∃ A : ℝ, 0 < A ∧ ∃ χ : ℝ → ℝ, ∀ (Q : ℕ) (ε : ℝ), 0 < ε →
      IsApproximateModelPhaseFunction
        (canonicalLegendrePhase χ (referenceModelPrimitive 1) 1 A ((2 : ℝ)/3))
        1 Q ε := by
  obtain ⟨A,hA,_,_,χ,_,_,_,hall⟩ := modelPhaseLegendreDual_canonical_extension
    (by norm_num : (0 : ℝ) < 1)
    (by norm_num [Real.rpow_neg_one] : (2 : ℝ)^(-(1 : ℝ)) < (2 : ℝ)/3)
    (by norm_num : (2 : ℝ)/3 ≤ (3 : ℝ)/4)
    (by norm_num : (3 : ℝ)/4 < 1)
    (by norm_num : (3 : ℝ)/4 < 2*((2 : ℝ)/3))
  refine ⟨A,hA,χ,?_⟩
  intro Q ε hε
  obtain ⟨δ,hδ,_,hmodel⟩ := hall Q ε hε
  have hF := approximateModelPhase_mono
    (referenceModelPrimitive_approximate 1 (legendreFiniteInputOrder (Q+1)))
    le_rfl hδ.le
  simpa only [inv_one] using (hmodel (referenceModelPrimitive 1) hF).2.1

-- [1/3,3/4] has ratio above two: the genuine finite-cover theorem still applies.
example :
    ∃ S : Finset (Icc ((1 : ℝ)/3) ((3 : ℝ)/4)), S.Nonempty ∧
      ∃ l r : Icc ((1 : ℝ)/3) ((3 : ℝ)/4) → ℝ,
        (∀ i ∈ S, r i < 2*l i) ∧
        ∀ v ∈ Icc ((1 : ℝ)/3) ((3 : ℝ)/4), ∃ i ∈ S, v ∈ Ioo (l i) (r i) := by
  obtain ⟨S,hS,l,r,A,χ,hgeom,hcover,_⟩ := modelPhaseLegendreDual_finite_canonical_cover
    (by norm_num : (0 : ℝ) < 2)
    (by norm_num [Real.rpow_neg,Real.rpow_two] :
      (2 : ℝ)^(-(2 : ℝ)) < (1 : ℝ)/3)
    (by norm_num : (1 : ℝ)/3 ≤ (3 : ℝ)/4)
    (by norm_num : (3 : ℝ)/4 < 1)
  refine ⟨S,hS,l,r,?_,hcover⟩
  intro i hi
  have hg := hgeom i hi
  linarith [hg.2.2.2.2.1,hg.2.2.2.2.2.1]

-- Finite-prefix repair produces the literal source model predicate.
example :
    ∃ G : VariableFunction (VariableObject.fixed ℝ) ℝ,
      IsModelPhaseFunctionWith G ((1 : ℝ)/2) ∧
      ∀ᶠ i : ℕ in atTop, G i = referenceModelPrimitive ((1 : ℝ)/2) := by
  apply modelPhaseWith_finite_initial_repair
  intro P ε hε
  exact Filter.Eventually.of_forall fun _ => approximateModelPhase_mono
    (referenceModelPrimitive_approximate ((1 : ℝ)/2) P) le_rfl hε.le

example
    {σ a b : ℝ} (hσ : 0 < σ)
    (ha : (2 : ℝ)^(-σ) < a) (hab : a ≤ b) (hb : b < 1) :
    ∃ S : Finset (Icc a b), S.Nonempty ∧
      ∃ l r A : Icc a b → ℝ, ∃ χ : Icc a b → ℝ → ℝ,
      (∀ i ∈ S, (2 : ℝ)^(-σ) < l i ∧ l i ≤ r i ∧ r i < 1 ∧
        0 < A i ∧ A i < l i ∧ r i < 2*A i ∧
        ContDiff ℝ ∞ (χ i) ∧ HasCompactSupport (χ i) ∧
        ∀ v ∈ Icc (l i) (r i), χ i v = 1) ∧
      (∀ v ∈ Icc a b, ∃ i ∈ S, v ∈ Ioo (l i) (r i)) ∧
      ∀ F : VariableFunction (VariableObject.fixed ℝ) ℝ,
        IsModelPhaseFunctionWith F σ →
      ∃ G : S → VariableFunction (VariableObject.fixed ℝ) ℝ,
        (∀ j, IsModelPhaseFunctionWith (G j) σ⁻¹ ∧ IsModelPhaseFunction (G j)) ∧
        ∀ᶠ n in atTop, ∀ j : S,
          G j n = canonicalLegendrePhase (χ j) (F n) σ (A j) (l j) ∧
          Icc (l j) (r j) ⊆ modelPhaseSlopeRange (F n) ∧
          ∀ v ∈ Icc (l j) (r j), v/A j ∈ Ioo (1 : ℝ) 2 ∧
            G j n (v/A j) =
              (A j)^(σ⁻¹-1)*
                (modelPhaseLegendreDual (F n) v-modelPhaseLegendreDual (F n) (l j)) +
                referenceModelPrimitive σ⁻¹ (l j/A j) :=
  @modelPhaseLegendreDual_finite_model_family σ a b hσ ha hab hb

end CanonicalLegendreExtensionRegression

section ModelPoissonSourceRegression

open Set Expdb Filter
open scoped ContDiff FourierTransform BigOperators

example {A T N : ℝ}
    (hA : 0 < A) (hT : 0 < T) (hN : 0 < N) :
    0 < modelPhaseDualScale A T N :=
  @modelPhaseDualScale_pos A T N hA hT hN

example (σ : ℝ) {A T : ℝ}
    (hA : 0 < A) (hT : 0 < T) :
    0 < modelPhaseDualParameter σ A T :=
  @modelPhaseDualParameter_pos σ A T hA hT

example {A T N : ℝ}
    (hA : A ≠ 0) (hT : T ≠ 0) (hN : N ≠ 0) (r : ℝ) :
    r/modelPhaseDualScale A T N = (r*N/T)/A :=
  @modelPhaseDualScale_coordinate A T N hA hT hN r

example (σ : ℝ) {A : ℝ}
    (hA : 0 < A) (T : ℝ) :
    modelPhaseDualParameter σ A T * A^(σ⁻¹-1) = T :=
  @modelPhaseDualParameter_cancel σ A hA T

example (σ : ℝ) {A T N : ℝ}
    (hA : 0 < A) (hT : T ≠ 0) (hN : N ≠ 0) :
    modelPhaseDualScale A T N / modelPhaseDualParameter σ A T = A^σ⁻¹/N :=
  @modelPhaseDualScale_ratio σ A T N hA hT hN

example (σ : ℝ) {A T N : ℝ}
    (hA : 0 < A) (hT : 0 < T) (hN : 0 < N) :
    modelPhaseDualScale A T N ≤ modelPhaseDualParameter σ A T ↔ A^σ⁻¹ ≤ N :=
  @modelPhaseDualScale_le_parameter_iff σ A T N hA hT hN

example {A T N : ℝ} (hN : 0 < N) :
    1 ≤ modelPhaseDualScale A T N ↔ N ≤ A*T :=
  @one_le_modelPhaseDualScale_iff A T N hN

example
    {χ F : ℝ → ℝ} {σ A w T N r : ℝ}
    (hA : 0 < A) (hw : 0 < w) (hT : T ≠ 0) (hN : N ≠ 0)
    (hv : 0 < r*N/T) (hχ : χ (r*N/T) = 1) :
    modelPhaseFrequencyPhase F T N r (modelPhaseStationaryPoint F T N r) =
      modelPhaseDualOffset F σ A w T -
        modelPhaseDualParameter σ A T *
          canonicalLegendrePhase χ F σ A w (r/modelPhaseDualScale A T N) :=
  @modelPhaseStationaryPoint_canonical_phase χ F σ A w T N r hA hw hT hN hv hχ

example
    {χ F : ℝ → ℝ} {σ A w T N r : ℝ}
    (hA : 0 < A) (hw : 0 < w) (hT : T ≠ 0) (hN : N ≠ 0)
    (hv : 0 < r*N/T) (hχ : χ (r*N/T) = 1) :
    (𝐞 (modelPhaseFrequencyPhase F T N r (modelPhaseStationaryPoint F T N r)) : ℂ) =
      (𝐞 (modelPhaseDualOffset F σ A w T) : ℂ) *
        starRingEnd ℂ (𝐞 (modelPhaseDualParameter σ A T *
          canonicalLegendrePhase χ F σ A w (r/modelPhaseDualScale A T N))) :=
  @modelPhaseStationaryPoint_canonical_fourier χ F σ A w T N r hA hw hT hN hv hχ

example
    {χ F : ℝ → ℝ} {σ δ : ℝ} {P : ℕ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hF : IsApproximateModelPhaseFunction F σ P δ) (T N : ℝ) :
    ContDiff ℝ ∞ (modelPhaseWeightedKernel χ F T N) :=
  @modelPhaseWeightedKernel_contDiff χ F σ δ P hχ hs hF T N

example
    {χ F : ℝ → ℝ} {N x : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2) (hN : 0 < N)
    (hx : x ∉ Icc N (2*N)) (T : ℝ) :
    modelPhaseWeightedKernel χ F T N x = 0 :=
  @modelPhaseWeightedKernel_zero_of_not_mem χ F N x hs hN hx T

example
    {χ F : ℝ → ℝ} {N : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2) (hN : 0 < N) (T : ℝ) :
    HasCompactSupport (modelPhaseWeightedKernel χ F T N) :=
  @modelPhaseWeightedKernel_hasCompactSupport χ F N hs hN T

example
    {χ F : ℝ → ℝ} {σ δ N : ℝ} {P : ℕ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hF : IsApproximateModelPhaseFunction F σ P δ) (hN : 0 < N) (T x : ℝ) :
    modelPhaseWeightedSchwartz hχ hs hF hN T x =
      modelPhaseWeightedKernel χ F T N x :=
  @modelPhaseWeightedSchwartz_apply χ F σ δ N P hχ hs hF hN T x

example
    {χ F : ℝ → ℝ} {σ δ N : ℝ} {P : ℕ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hF : IsApproximateModelPhaseFunction F σ P δ) (hN : 0 < N) (T r : ℝ) :
    𝓕 (modelPhaseWeightedSchwartz hχ hs hF hN T) r =
      modelPhaseFourierMode χ F T N r :=
  @modelPhaseWeightedSchwartz_fourier χ F σ δ N P hχ hs hF hN T r

example
    {χ F : ℝ → ℝ} {N : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2) (hN : 0 < N) (T : ℝ) :
    (∑' n : ℤ, modelPhaseWeightedKernel χ F T N n) =
      ∑ n ∈ Finset.Icc ⌈N⌉ ⌊2*N⌋, modelPhaseWeightedKernel χ F T N n :=
  @modelPhaseWeightedKernel_tsum_eq_finite χ F N hs hN T

example
    {χ F : ℝ → ℝ} {σ δ N : ℝ} {P : ℕ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hF : IsApproximateModelPhaseFunction F σ P δ) (hN : 0 < N) (T : ℝ) :
    (∑ n ∈ Finset.Icc ⌈N⌉ ⌊2*N⌋, modelPhaseWeightedKernel χ F T N n) =
      ∑' r : ℤ, modelPhaseFourierMode χ F T N r :=
  @modelPhase_weighted_poisson χ F σ δ N P hχ hs hF hN T

example {N : ℝ} (hN : 0 < N)
    {a b : ℤ} (ha : N < (a : ℝ)) (hab : a ≤ b) (hb : (b : ℝ) < 2*N) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧
      tsupport χ ⊆ Ioo (1 : ℝ) 2 ∧ HasCompactSupport χ ∧
      (∀ x : ℝ, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      ∀ n : ℤ, χ ((n : ℝ)/N) = if n ∈ Finset.Icc a b then 1 else 0 :=
  @exists_modelPhase_integer_cutoff N hN a b ha hab hb

example (F : ℝ → ℝ) (T N : ℝ) (a b : ℕ) :
    exponentialSumAt F T N a b =
      ∑ n ∈ Finset.Icc (a : ℤ) (b : ℤ), (𝐞 (T*F ((n : ℝ)/N)) : ℂ) :=
  @exponentialSumAt_eq_int_sum F T N a b

example
    {F : ℝ → ℝ} {σ δ N : ℝ} {P : ℕ}
    (hF : IsApproximateModelPhaseFunction F σ P δ) (hN : 0 < N)
    {a b : ℕ} (ha : N < (a : ℝ)) (hab : a ≤ b) (hb : (b : ℝ) < 2*N) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧
      tsupport χ ⊆ Ioo (1 : ℝ) 2 ∧ HasCompactSupport χ ∧
      (∀ n : ℤ, χ ((n : ℝ)/N) = if n ∈ Finset.Icc (a : ℤ) (b : ℤ) then 1 else 0) ∧
      ∀ T : ℝ, exponentialSumAt F T N a b =
        ∑' r : ℤ, modelPhaseFourierMode χ F T N r :=
  @modelPhase_sharp_interval_poisson F σ δ N P hF hN a b ha hab hb

example
    (χ F : ℝ → ℝ) (T r : ℝ) {N : ℝ} (hN : 0 < N) :
    modelPhaseFourierMode χ F T N r = N • modelPhaseNormalizedMode χ F T (r*N) :=
  @modelPhaseFourierMode_eq_normalized χ F T r N hN

example
    (χ F : ℝ → ℝ) (T r : ℝ) {N : ℝ} (hN : 0 < N) :
    ‖modelPhaseFourierMode χ F T N r‖ ≤ N * ∫ u : ℝ, |χ u| :=
  @norm_modelPhaseFourierMode_le χ F T r N hN

example
    {χ F : ℝ → ℝ} {σ δ N : ℝ} {P : ℕ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hF : IsApproximateModelPhaseFunction F σ P δ) (hN : 0 < N) (T : ℝ) :
    Summable (fun r : ℤ => modelPhaseFourierMode χ F T N r) :=
  @summable_modelPhaseFourierMode χ F σ δ N P hχ hs hF hN T

example
    {χ F : ℝ → ℝ} {σ δ N : ℝ} {P : ℕ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hF : IsApproximateModelPhaseFunction F σ P δ) (hN : 0 < N) (T : ℝ) :
    Summable (fun r : ℤ => ‖modelPhaseFourierMode χ F T N r‖) :=
  @summable_norm_modelPhaseFourierMode χ F σ δ N P hχ hs hF hN T

example (N : ℝ) (a b : ℤ) :
    modelPhaseInteriorIndices N a b ⊆ Finset.Icc a b :=
  @modelPhaseInteriorIndices_subset N a b

example {N : ℝ} (hN : 0 < N) (a b : ℤ) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧
      tsupport χ ⊆ Ioo (1 : ℝ) 2 ∧ HasCompactSupport χ ∧
      (∀ x : ℝ, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      ∀ n : ℤ, χ ((n : ℝ)/N) =
        if n ∈ modelPhaseInteriorIndices N a b then 1 else 0 :=
  @exists_modelPhase_interior_cutoff N hN a b

example
    {N : ℝ} {a b : ℤ} (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N) :
    ((Finset.Icc a b) \ modelPhaseInteriorIndices N a b).card ≤ 2 :=
  @modelPhase_boundary_indices_card_le_two N a b ha hb

example
    (F : ℝ → ℝ) (T : ℝ) {N : ℝ} {a b : ℤ}
    (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N) :
    ‖(∑ n ∈ Finset.Icc a b, (𝐞 (T*F ((n : ℝ)/N)) : ℂ)) -
      ∑ n ∈ modelPhaseInteriorIndices N a b, (𝐞 (T*F ((n : ℝ)/N)) : ℂ)‖ ≤ 2 :=
  @norm_modelPhase_full_sub_interior_le_two F T N a b ha hb

example
    {F : ℝ → ℝ} {σ δ N : ℝ} {P : ℕ}
    (hF : IsApproximateModelPhaseFunction F σ P δ) (hN : 0 < N)
    {a b : ℕ} (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧
      tsupport χ ⊆ Ioo (1 : ℝ) 2 ∧ HasCompactSupport χ ∧
      (∀ n : ℤ, χ ((n : ℝ)/N) =
        if n ∈ modelPhaseInteriorIndices N a b then 1 else 0) ∧
      ∀ T : ℝ, Summable (fun r : ℤ => ‖modelPhaseFourierMode χ F T N r‖) ∧
        ‖exponentialSumAt F T N a b -
          ∑' r : ℤ, modelPhaseFourierMode χ F T N r‖ ≤ 2 :=
  @modelPhase_closed_interval_poisson F σ δ N P hF hN a b ha hb

example
    {χ F : ℝ → ℝ} {σ A w T N : ℝ}
    (hA : 0 < A) (hw : 0 < w) (hT : T ≠ 0) (hN : N ≠ 0)
    (S : Finset ℤ) (c : ℤ → ℝ)
    (hv : ∀ r ∈ S, 0 < (r : ℝ)*N/T)
    (hχ : ∀ r ∈ S, χ ((r : ℝ)*N/T) = 1) :
    (∑ r ∈ S, (c r : ℂ) *
      (𝐞 (modelPhaseFrequencyPhase F T N r (modelPhaseStationaryPoint F T N r)) : ℂ)) =
      (𝐞 (modelPhaseDualOffset F σ A w T) : ℂ) *
        starRingEnd ℂ (∑ r ∈ S, (c r : ℂ) *
          (𝐞 (modelPhaseDualParameter σ A T *
            canonicalLegendrePhase χ F σ A w ((r : ℝ)/modelPhaseDualScale A T N)) : ℂ)) :=
  @modelPhaseStationaryPoint_weighted_sum_canonical χ F σ A w T N hA hw hT hN S c hv hχ

example
    {χ F : ℝ → ℝ} {σ A w T N : ℝ}
    (hA : 0 < A) (hw : 0 < w) (hT : T ≠ 0) (hN : N ≠ 0)
    (S : Finset ℤ) (c : ℤ → ℝ)
    (hv : ∀ r ∈ S, 0 < (r : ℝ)*N/T)
    (hχ : ∀ r ∈ S, χ ((r : ℝ)*N/T) = 1) :
    ‖∑ r ∈ S, (c r : ℂ) *
      (𝐞 (modelPhaseFrequencyPhase F T N r (modelPhaseStationaryPoint F T N r)) : ℂ)‖ =
      ‖∑ r ∈ S, (c r : ℂ) *
        (𝐞 (modelPhaseDualParameter σ A T *
          canonicalLegendrePhase χ F σ A w ((r : ℝ)/modelPhaseDualScale A T N)) : ℂ)‖ :=
  @norm_modelPhaseStationaryPoint_weighted_sum χ F σ A w T N hA hw hT hN S c hv hχ

example
    {χ F : ℝ → ℝ} {σ A w T N : ℝ}
    (hA : 0 < A) (hw : 0 < w) (hT : T ≠ 0) (hN : N ≠ 0)
    (a b : ℕ)
    (hv : ∀ r ∈ Finset.Icc (a : ℤ) (b : ℤ), 0 < (r : ℝ)*N/T)
    (hχ : ∀ r ∈ Finset.Icc (a : ℤ) (b : ℤ), χ ((r : ℝ)*N/T) = 1) :
    (∑ r ∈ Finset.Icc (a : ℤ) (b : ℤ),
      (𝐞 (modelPhaseFrequencyPhase F T N r (modelPhaseStationaryPoint F T N r)) : ℂ)) =
      (𝐞 (modelPhaseDualOffset F σ A w T) : ℂ) *
        starRingEnd ℂ (exponentialSumAt (canonicalLegendrePhase χ F σ A w)
          (modelPhaseDualParameter σ A T) (modelPhaseDualScale A T N) a b) :=
  @modelPhaseStationaryPoint_interval_canonical χ F σ A w T N hA hw hT hN a b hv hχ

example
    {χ F : ℝ → ℝ} {σ A w T N : ℝ}
    (hA : 0 < A) (hw : 0 < w) (hT : T ≠ 0) (hN : N ≠ 0)
    (a b : ℕ)
    (hv : ∀ r ∈ Finset.Icc (a : ℤ) (b : ℤ), 0 < (r : ℝ)*N/T)
    (hχ : ∀ r ∈ Finset.Icc (a : ℤ) (b : ℤ), χ ((r : ℝ)*N/T) = 1) :
    ‖∑ r ∈ Finset.Icc (a : ℤ) (b : ℤ),
      (𝐞 (modelPhaseFrequencyPhase F T N r (modelPhaseStationaryPoint F T N r)) : ℂ)‖ =
      ‖exponentialSumAt (canonicalLegendrePhase χ F σ A w)
        (modelPhaseDualParameter σ A T) (modelPhaseDualScale A T N) a b‖ :=
  @norm_modelPhaseStationaryPoint_interval χ F σ A w T N hA hw hT hN a b hv hχ

-- Physical dual parameters are linked, not independently supplied exponents.
example : modelPhaseDualScale 3 10 5 = 6 := by
  norm_num [modelPhaseDualScale]

example : modelPhaseDualParameter 1 3 10 = 10 := by
  norm_num [modelPhaseDualParameter]

-- A closed interval retains its interior integer and discards exactly two endpoints.
example : modelPhaseInteriorIndices 2 2 4 = {3} := by
  norm_num [modelPhaseInteriorIndices,Finset.filter_insert,Finset.filter_singleton,
    show Finset.Icc (2 : ℤ) 4 = {2,3,4} by decide]

example :
    ((Finset.Icc (2 : ℤ) 4) \ modelPhaseInteriorIndices 2 2 4).card = 2 := by
  norm_num [modelPhaseInteriorIndices,Finset.filter_insert,Finset.filter_singleton,
    show Finset.Icc (2 : ℤ) 4 = {2,3,4} by decide]
  decide

-- Empty source intervals remain genuine empty intervals.
example : modelPhaseInteriorIndices 2 4 3 = ∅ := by
  simp [modelPhaseInteriorIndices]

-- Literal source sum, with no externally assumed smoothed replacement.
example :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧
      tsupport χ ⊆ Ioo (1 : ℝ) 2 ∧ HasCompactSupport χ ∧
      (∀ n : ℤ, χ ((n : ℝ)/2) =
        if n ∈ modelPhaseInteriorIndices 2 2 4 then 1 else 0) ∧
      ∀ T : ℝ,
        Summable (fun r : ℤ => ‖modelPhaseFourierMode χ (referenceModelPrimitive 1) T 2 r‖) ∧
        ‖exponentialSumAt (referenceModelPrimitive 1) T 2 2 4 -
          ∑' r : ℤ, modelPhaseFourierMode χ (referenceModelPrimitive 1) T 2 r‖ ≤ 2 := by
  exact modelPhase_closed_interval_poisson (referenceModelPrimitive_approximate 1 0)
    (by norm_num) (by norm_num) (by norm_num)

-- The strictly interior singleton has exact equality, for every phase parameter.
example :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧
      tsupport χ ⊆ Ioo (1 : ℝ) 2 ∧ HasCompactSupport χ ∧
      (∀ n : ℤ, χ ((n : ℝ)/2) = if n ∈ Finset.Icc (3 : ℤ) 3 then 1 else 0) ∧
      ∀ T : ℝ, exponentialSumAt (referenceModelPrimitive 1) T 2 3 3 =
        ∑' r : ℤ, modelPhaseFourierMode χ (referenceModelPrimitive 1) T 2 r := by
  exact modelPhase_sharp_interval_poisson (referenceModelPrimitive_approximate 1 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example (χ F : ℝ → ℝ) (T r : ℝ) :
    modelPhaseFourierMode χ F T 2 r =
      (2 : ℝ) • modelPhaseNormalizedMode χ F T (r*2) :=
  modelPhaseFourierMode_eq_normalized χ F T r (by norm_num)

end ModelPoissonSourceRegression

section StationaryAmplitudeMorseRegression

open Set Expdb Filter
open scoped ContDiff FourierTransform Topology NNReal BigOperators

example {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) :
    modelPhaseCurvatureLower σ ≤ modelPhaseCurvatureAt F v ∧
      modelPhaseCurvatureAt F v ≤ σ+1 :=
  @modelPhaseCurvatureAt_bounds σ δ F hσ hδ hF v hv

example {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) :
    0 < modelPhaseCurvatureAt F v :=
  @modelPhaseCurvatureAt_pos σ δ F hσ hδ hF v hv

example {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) :
    0 < modelPhaseStationaryAmplitude F v :=
  @modelPhaseStationaryAmplitude_pos σ δ F hσ hδ hF v hv

example {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) :
    (Real.sqrt (σ+1))⁻¹ ≤ modelPhaseStationaryAmplitude F v ∧
      modelPhaseStationaryAmplitude F v ≤ (Real.sqrt (modelPhaseCurvatureLower σ))⁻¹ :=
  @modelPhaseStationaryAmplitude_bounds σ δ F hσ hδ hF v hv

example {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) :
    ContDiffAt ℝ ∞ (modelPhaseCurvatureAt F) v :=
  @modelPhaseCurvatureAt_contDiffAt σ δ F hσ hδ hF v hv

example {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) :
    ContDiffAt ℝ ∞ (modelPhaseStationaryAmplitude F) v :=
  @modelPhaseStationaryAmplitude_contDiffAt σ δ F hσ hδ hF v hv

example {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) :
    HasDerivAt (modelPhaseCurvatureAt F)
      (deriv (deriv (deriv F)) (modelPhaseInverseSlope F v) /
        modelPhaseCurvatureAt F v) v :=
  @modelPhaseCurvatureAt_hasDerivAt σ δ F hσ hδ hF v hv

example {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) :
    HasDerivAt (modelPhaseStationaryAmplitude F)
      (-deriv (deriv (deriv F)) (modelPhaseInverseSlope F v) /
        (2*(modelPhaseCurvatureAt F v)^2*Real.sqrt (modelPhaseCurvatureAt F v))) v :=
  @modelPhaseStationaryAmplitude_hasDerivAt σ δ F hσ hδ hF v hv

example
    {σ δ T N r : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hT : 0 < T) (hN : 0 < N)
    (hv : r*N/T ∈ modelPhaseSlopeRange F) :
    (Real.sqrt (-deriv (deriv (modelPhaseFrequencyPhase F T N r))
      (modelPhaseStationaryPoint F T N r)))⁻¹ =
        (N/Real.sqrt T)*modelPhaseStationaryAmplitude F (r*N/T) :=
  @modelPhaseStationaryPoint_amplitude_scale σ δ T N r P F hF hT hN hv

example {σ : ℝ} (hσ : 0 < σ) :
    0 < modelPhaseThirdLower σ :=
  @modelPhaseThirdLower_pos σ hσ

example {σ : ℝ} (hσ : 0 < σ) :
    0 < modelPhaseAmplitudeTolerance σ :=
  @modelPhaseAmplitudeTolerance_pos σ hσ

example
    {σ δ : ℝ} {F : ℝ → ℝ} (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 2 δ)
    {u : ℝ} (hu : u ∈ phaseInterval) :
    modelPhaseThirdLower σ ≤ iteratedDerivWithin 3 F phaseInterval u ∧
      iteratedDerivWithin 3 F phaseInterval u ≤ σ*(σ+1)+1 :=
  @approximateModelPhase_thirdWithin_bounds σ δ F hσ hδ hF u hu

example
    {σ δ : ℝ} {F : ℝ → ℝ} (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 2 δ)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) :
    modelPhaseThirdLower σ ≤ deriv (deriv (deriv F)) u ∧
      deriv (deriv (deriv F)) u ≤ σ*(σ+1)+1 :=
  @approximateModelPhase_thirdDeriv_bounds σ δ F hσ hδ hF u hu

example
    {σ δ : ℝ} {F : ℝ → ℝ} (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 2 δ) :
    StrictMonoOn (deriv (deriv F)) (Ioo (1 : ℝ) 2) :=
  @approximateModelPhase_secondDeriv_strictMonoOn σ δ F hσ hδ hF

example
    {σ δ : ℝ} {F : ℝ → ℝ} (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) :
    AntitoneOn (modelPhaseInverseSlope F) (modelPhaseSlopeRange F) :=
  @modelPhaseInverseSlope_antitoneOn σ δ F hσ hδ hF

example
    {σ δ : ℝ} {F : ℝ → ℝ} (hσ : 0 < σ)
    (hδ : δ ≤ modelPhaseAmplitudeTolerance σ)
    (hF : IsApproximateModelPhaseFunction F σ 2 δ) :
    AntitoneOn (modelPhaseStationaryAmplitude F) (modelPhaseSlopeRange F) :=
  @modelPhaseStationaryAmplitude_antitoneOn σ δ F hσ hδ hF

example
    {σ δ T N r : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hT : 0 < T) (hN : 0 < N)
    (hv : r*N/T ∈ modelPhaseSlopeRange F) :
    modelPhasePhysicalAmplitude F T N r =
      (N/Real.sqrt T)*modelPhaseStationaryAmplitude F (r*N/T) :=
  @modelPhasePhysicalAmplitude_eq σ δ T N r P F hF hT hN hv

example
    {σ δ T N r : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N)
    (hv : r*N/T ∈ modelPhaseSlopeRange F) :
    0 < modelPhasePhysicalAmplitude F T N r :=
  @modelPhasePhysicalAmplitude_pos σ δ T N r F hσ hδ hF hT hN hv

example
    {σ δ T N r : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N)
    (hv : r*N/T ∈ modelPhaseSlopeRange F) :
    modelPhasePhysicalAmplitude F T N r ≤
      (N/Real.sqrt T)*(Real.sqrt (modelPhaseCurvatureLower σ))⁻¹ :=
  @modelPhasePhysicalAmplitude_le σ δ T N r F hσ hδ hF hT hN hv

example
    {σ δ T N : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ modelPhaseAmplitudeTolerance σ)
    (hF : IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hN : 0 < N) :
    AntitoneOn (modelPhasePhysicalAmplitude F T N)
      {r : ℝ | r*N/T ∈ modelPhaseSlopeRange F} :=
  @modelPhasePhysicalAmplitude_antitoneOn σ δ T N F hσ hδ hF hT hN

example
    {σ δ T N : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ modelPhaseAmplitudeTolerance σ)
    (hF : IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hN : 0 < N) (a : ℝ) (L : ℕ)
    (hv : ∀ i : ℕ, i ≤ L → (a+i)*N/T ∈ modelPhaseSlopeRange F) :
    FiniteVariationBound (fun i => (modelPhasePhysicalAmplitude F T N (a+i) : ℂ)) L
      ((N/Real.sqrt T)*(Real.sqrt (modelPhaseCurvatureLower σ))⁻¹) :=
  @finiteVariationBound_modelPhasePhysicalAmplitude σ δ T N F hσ hδ hF hT hN a L hv

example
    {w z : ℕ → ℂ} {L : ℕ} {M B : ℝ}
    (hw : FiniteVariationBound w L M) (hB : 0 ≤ B)
    (hz : ∀ j ≤ L+1, ‖∑ i ∈ Finset.range j, z i‖ ≤ B) :
    ‖∑ i ∈ Finset.range (L+1), w i*z i‖ ≤ 2*M*B :=
  @norm_sum_range_succ_mul_le_of_finiteVariation w z L M B hw hB hz

example (F : ℝ → ℝ) (T N r : ℝ) :
    ‖modelPhaseStationaryCharacter F T N r‖ = 1 :=
  @norm_modelPhaseStationaryCharacter F T N r

example (F : ℝ → ℝ) (T N : ℝ) (a L : ℕ) :
    exponentialSumAt F T N a (a+L) =
      ∑ i ∈ Finset.range (L+1), (𝐞 (T*F (((a : ℝ)+i)/N)) : ℂ) :=
  @exponentialSumAt_eq_range F T N a L

example (F : ℝ → ℝ) (T N : ℝ)
    (a L j : ℕ) (hj : j ≤ L) :
    ‖exponentialSumAt F T N a (a+j)‖ ≤ exponentialSumAtPrefixMax F T N a L :=
  @norm_exponentialSumAt_le_prefixMax F T N a L j hj

example (F : ℝ → ℝ) (T N : ℝ) (a L : ℕ) :
    0 ≤ exponentialSumAtPrefixMax F T N a L :=
  @exponentialSumAtPrefixMax_nonneg F T N a L

example {F : ℝ → ℝ} {T N B : ℝ} {a L : ℕ}
    (h : ∀ j ≤ L, ‖exponentialSumAt F T N a (a+j)‖ ≤ B) :
    exponentialSumAtPrefixMax F T N a L ≤ B :=
  @exponentialSumAtPrefixMax_le F T N B a L h

example
    {χ F : ℝ → ℝ} {σ A w T N r : ℝ}
    (hA : 0 < A) (hw : 0 < w) (hT : T ≠ 0) (hN : N ≠ 0)
    (hv : 0 < r*N/T) (hχ : χ (r*N/T) = 1) :
    modelPhaseStationaryCharacter F T N r =
      (𝐞 (modelPhaseDualOffset F σ A w T-1/8) : ℂ) *
        starRingEnd ℂ (𝐞 (modelPhaseDualParameter σ A T *
          canonicalLegendrePhase χ F σ A w (r/modelPhaseDualScale A T N))) :=
  @modelPhaseStationaryCharacter_canonical χ F σ A w T N r hA hw hT hN hv hχ

example
    {χ F : ℝ → ℝ} {σ A w T N : ℝ}
    (hA : 0 < A) (hw : 0 < w) (hT : T ≠ 0) (hN : N ≠ 0)
    (a L : ℕ)
    (hv : ∀ i : ℕ, i ≤ L → 0 < ((a : ℝ)+i)*N/T)
    (hχ : ∀ i : ℕ, i ≤ L → χ (((a : ℝ)+i)*N/T) = 1) :
    ‖∑ i ∈ Finset.range (L+1), modelPhaseStationaryCharacter F T N ((a : ℝ)+i)‖ =
      ‖exponentialSumAt (canonicalLegendrePhase χ F σ A w)
        (modelPhaseDualParameter σ A T) (modelPhaseDualScale A T N) a (a+L)‖ :=
  @norm_modelPhaseStationaryCharacter_range χ F σ A w T N hA hw hT hN a L hv hχ

example (F : ℝ → ℝ) (T N : ℝ) (a L : ℕ) :
    modelPhaseStationaryBlock F T N a L =
      ∑ i ∈ Finset.range (L+1), modelPhaseStationaryMainTerm F T N ((a : ℝ)+i) :=
  @modelPhaseStationaryBlock_eq_range F T N a L

example
    {χ F : ℝ → ℝ} {σ δ A w T N : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ modelPhaseAmplitudeTolerance σ)
    (hF : IsApproximateModelPhaseFunction F σ 2 δ)
    (hA : 0 < A) (hw : 0 < w) (hT : 0 < T) (hN : 0 < N)
    (a L : ℕ)
    (hslope : ∀ i : ℕ, i ≤ L → ((a : ℝ)+i)*N/T ∈ modelPhaseSlopeRange F)
    (hv : ∀ i : ℕ, i ≤ L → 0 < ((a : ℝ)+i)*N/T)
    (hχ : ∀ i : ℕ, i ≤ L → χ (((a : ℝ)+i)*N/T) = 1) :
    ‖modelPhaseStationaryBlock F T N a L‖ ≤
      2*((N/Real.sqrt T)*(Real.sqrt (modelPhaseCurvatureLower σ))⁻¹) *
        exponentialSumAtPrefixMax (canonicalLegendrePhase χ F σ A w)
          (modelPhaseDualParameter σ A T) (modelPhaseDualScale A T N) a L :=
  @norm_modelPhaseStationaryBlock_le_prefixMax χ F σ δ A w T N hσ hδ hF hA hw hT hN a L hslope hv hχ

example
    {α : ℝ≥0} {β σ l r : ℝ}
    (hβ : IsExponentSumBoundNonAsymptotic α β) (hσ : 0 < σ)
    (hl : (2 : ℝ)^(-σ) < l) (hlr : l ≤ r) (hr : r < 1) (hratio : r < 2*l) :
    ∃ A : ℝ, 0 < A ∧ A < l ∧ r < 2*A ∧
      ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
        (∀ v ∈ Icc l r, χ v = 1) ∧
        ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧ ∃ P : ℕ, 2 ≤ P ∧ ∃ C : ℝ, 1 ≤ C ∧
          ∀ (T N : ℝ) (F : ℝ → ℝ) (a L : ℕ),
            0 < T → 0 < N →
            IsApproximateModelPhaseFunction F σ P δ →
            C ≤ modelPhaseDualParameter σ A T →
            (modelPhaseDualParameter σ A T)^((α : ℝ)-δ) ≤ modelPhaseDualScale A T N →
            modelPhaseDualScale A T N ≤ (modelPhaseDualParameter σ A T)^((α : ℝ)+δ) →
            (∀ i : ℕ, i ≤ L → ((a : ℝ)+i)*N/T ∈ Icc l r) →
            ‖modelPhaseStationaryBlock F T N a L‖ ≤
              2*((N/Real.sqrt T)*(Real.sqrt (modelPhaseCurvatureLower σ))⁻¹) *
                C*(modelPhaseDualParameter σ A T)^(β+ε) :=
  @stationaryMain_bound_of_exponentSumBound α β σ l r hβ hσ hl hlr hr hratio

example (F : ℝ → ℝ) (v : ℝ) :
    modelPhaseStationaryDeficit F v (modelPhaseInverseSlope F v) = 0 :=
  @modelPhaseStationaryDeficit_at_inverse F v

example
    {σ δ v u : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) :
    modelPhaseCurvatureLower σ*(u-modelPhaseInverseSlope F v)^2/2 ≤
        modelPhaseStationaryDeficit F v u ∧
      modelPhaseStationaryDeficit F v u ≤
        (σ+1)*(u-modelPhaseInverseSlope F v)^2/2 :=
  @modelPhaseStationaryDeficit_bounds σ δ v u F hσ hδ hF hv hu

example
    {σ δ v u : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) :
    0 ≤ modelPhaseStationaryDeficit F v u :=
  @modelPhaseStationaryDeficit_nonneg σ δ v u F hσ hδ hF hv hu

example
    {σ δ v u : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) :
    (modelPhaseMorseCoordinate F v u)^2 = 2*modelPhaseStationaryDeficit F v u :=
  @modelPhaseMorseCoordinate_sq σ δ v u F hσ hδ hF hv hu

example
    (F : ℝ → ℝ) (v u : ℝ) :
    |modelPhaseMorseCoordinate F v u| = Real.sqrt (2*modelPhaseStationaryDeficit F v u) :=
  @modelPhaseMorseCoordinate_abs F v u

example
    {σ δ v u : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) :
    Real.sqrt (modelPhaseCurvatureLower σ)*|u-modelPhaseInverseSlope F v| ≤
        |modelPhaseMorseCoordinate F v u| ∧
      |modelPhaseMorseCoordinate F v u| ≤
        Real.sqrt (σ+1)*|u-modelPhaseInverseSlope F v| :=
  @modelPhaseMorseCoordinate_bounds σ δ v u F hσ hδ hF hv hu

example
    {σ δ v u : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) :
    F u-v*u = -modelPhaseLegendreDual F v-(modelPhaseMorseCoordinate F v u)^2/2 :=
  @modelPhaseMorseCoordinate_normalForm σ δ v u F hσ hδ hF hv hu

example
    {F : ℝ → ℝ} {T N : ℝ} (hT : T ≠ 0) (hN : N ≠ 0) (r x : ℝ) :
    modelPhaseFrequencyPhase F T N r (modelPhaseStationaryPoint F T N r) -
        modelPhaseFrequencyPhase F T N r x =
      T*modelPhaseStationaryDeficit F (r*N/T) (x/N) :=
  @modelPhaseFrequencyPhase_deficit F T N hT hN r x

example
    {σ δ T N r x : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : T ≠ 0) (hN : N ≠ 0)
    (hv : r*N/T ∈ modelPhaseSlopeRange F) (hx : x/N ∈ Ioo (1 : ℝ) 2) :
    modelPhaseFrequencyPhase F T N r x =
      modelPhaseFrequencyPhase F T N r (modelPhaseStationaryPoint F T N r) -
        (T/2)*(modelPhaseMorseCoordinate F (r*N/T) (x/N))^2 :=
  @modelPhaseFrequencyPhase_quadratic_normalForm σ δ T N r x F hσ hδ hF hT hN hv hx

example (F : ℝ → ℝ) (v : ℝ) :
    modelPhaseMorseCoordinate F v (modelPhaseInverseSlope F v) = 0 :=
  @modelPhaseMorseCoordinate_at_inverse F v

example
    {F : ℝ → ℝ} {σ δ v : ℝ} {P : ℕ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    Tendsto (fun u : ℝ => 2*modelPhaseStationaryDeficit F v u /
      (u-modelPhaseInverseSlope F v)^2)
      (𝓝[≠] modelPhaseInverseSlope F v) (𝓝 (modelPhaseCurvatureAt F v)) :=
  @modelPhaseStationaryDeficit_ratio_tendsto F σ δ v P hF hv

example (F : ℝ → ℝ) (v u : ℝ) :
    slope (modelPhaseMorseCoordinate F v) (modelPhaseInverseSlope F v) u =
      Real.sqrt (2*modelPhaseStationaryDeficit F v u /
        (u-modelPhaseInverseSlope F v)^2) :=
  @modelPhaseMorseCoordinate_slope F v u

example
    {F : ℝ → ℝ} {σ δ v : ℝ} {P : ℕ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    HasDerivAt (modelPhaseMorseCoordinate F v) (Real.sqrt (modelPhaseCurvatureAt F v))
      (modelPhaseInverseSlope F v) :=
  @modelPhaseMorseCoordinate_hasDerivAt_inverse F σ δ v P hF hv

example
    {F : ℝ → ℝ} {σ δ v : ℝ} {P : ℕ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    (deriv (modelPhaseMorseCoordinate F v) (modelPhaseInverseSlope F v))⁻¹ =
      modelPhaseStationaryAmplitude F v :=
  @modelPhaseMorseCoordinate_reciprocal_derivative_amplitude F σ δ v P hF hv

-- One tolerance simultaneously controls curvature and the third-derivative sign.
example : modelPhaseAmplitudeTolerance 1 = (1 : ℝ)/8 := by
  norm_num [modelPhaseAmplitudeTolerance,modelPhaseCurvatureLower,modelPhaseThirdLower,
    Real.rpow_neg]

example : 0 < modelPhaseStationaryAmplitude (referenceModelPrimitive 1) ((2 : ℝ)/3) := by
  exact modelPhaseStationaryAmplitude_pos (by norm_num)
    (le_min (modelPhaseCurvatureLower_pos (by norm_num)).le zero_le_one)
    (referenceModelPrimitive_approximate 1 1)
    (referenceModelPrimitive_slopeRange (by norm_num)
      (by norm_num [Real.rpow_neg_one]))

-- This variation bound needs only the singleton's frequency, not a point beyond it.
example :
    FiniteVariationBound
      (fun i => (modelPhasePhysicalAmplitude (referenceModelPrimitive 1) 1 1
        ((2 : ℝ)/3+i) : ℂ)) 0
      ((1/Real.sqrt 1)*(Real.sqrt (modelPhaseCurvatureLower 1))⁻¹) := by
  apply finiteVariationBound_modelPhasePhysicalAmplitude (by norm_num)
    (modelPhaseAmplitudeTolerance_pos (by norm_num)).le
    (referenceModelPrimitive_approximate 1 2) (by norm_num) (by norm_num)
  intro i hi
  have he : i = 0 := by omega
  subst i
  simpa only [Nat.cast_zero,add_zero,mul_one,div_one] using
    referenceModelPrimitive_slopeRange (by norm_num : (0 : ℝ) < 1)
      (by norm_num [Real.rpow_neg_one] :
        (2 : ℝ)/3 ∈ Ioo ((2 : ℝ)^(-(1 : ℝ))) 1)

example (F : ℝ → ℝ) (T N : ℝ) (a : ℕ) :
    exponentialSumAtPrefixMax F T N a 0 = 1 := by
  simp [exponentialSumAtPrefixMax]

-- The stationary main term retains its real curvature weight.
example (F : ℝ → ℝ) (T N r : ℝ) :
    ‖modelPhaseStationaryMainTerm F T N r‖ = |modelPhasePhysicalAmplitude F T N r| := by
  rw [modelPhaseStationaryMainTerm,norm_mul,norm_modelPhaseStationaryCharacter,mul_one,
    Complex.norm_real,Real.norm_eq_abs]

example (F : ℝ → ℝ) (v : ℝ) :
    modelPhaseMorseCoordinate F v (modelPhaseInverseSlope F v) = 0 :=
  modelPhaseMorseCoordinate_at_inverse F v

-- The coordinate uses the negative square root to the left of the critical point.
example (F : ℝ → ℝ) (v u : ℝ) (hu : u < modelPhaseInverseSlope F v) :
    modelPhaseMorseCoordinate F v u ≤ 0 := by
  rw [modelPhaseMorseCoordinate,if_pos hu]
  exact neg_nonpos.mpr (Real.sqrt_nonneg _)

-- A genuine logarithmic source model supplies the derivative, without a Taylor premise.
example :
    HasDerivAt (modelPhaseMorseCoordinate (referenceModelPrimitive 1) ((2 : ℝ)/3))
      (Real.sqrt (modelPhaseCurvatureAt (referenceModelPrimitive 1) ((2 : ℝ)/3)))
      (modelPhaseInverseSlope (referenceModelPrimitive 1) ((2 : ℝ)/3)) := by
  exact modelPhaseMorseCoordinate_hasDerivAt_inverse (referenceModelPrimitive_approximate 1 0)
    (referenceModelPrimitive_slopeRange (by norm_num)
      (by norm_num [Real.rpow_neg_one]))

end StationaryAmplitudeMorseRegression

section SmoothQuadraticInverseRegression

open Set Expdb Filter MeasureTheory
open scoped ContDiff Topology FourierTransform BigOperators NNReal

example {b c a x t : ℝ}
    (ha : a ∈ Icc b c) (hx : x ∈ Icc b c) (ht : t ∈ Icc (0 : ℝ) 1) :
    a+t*(x-a) ∈ Icc b c :=
  @affineSegment_mem_Icc b c a x t ha hx ht

example {b c a x t : ℝ}
    (ha : a ∈ Ioo b c) (hx : x ∈ Ioo b c) (ht : t ∈ Icc (0 : ℝ) 1) :
    a+t*(x-a) ∈ Ioo b c :=
  @affineSegment_mem_Ioo b c a x t ha hx ht

example
    {f : ℝ → ℝ} {l r a x : ℝ}
    (hf : ∀ u ∈ Ioo l r, ContDiffAt ℝ ∞ f u)
    (ha : a ∈ Ioo l r) (hx : x ∈ Ioo l r) (k : ℕ) :
    IntegrableOn (fun t : ℝ => (1-t)*t^k*iteratedDeriv k f (a+t*(x-a)))
      (Icc (0 : ℝ) 1) :=
  @segmentTaylorAverage_integrable f l r a x hf ha hx k

example
    {f : ℝ → ℝ} {l r a x : ℝ}
    (hf : ∀ u ∈ Ioo l r, ContDiffAt ℝ ∞ f u)
    (ha : a ∈ Ioo l r) (hx : x ∈ Ioo l r) (k : ℕ) :
    HasDerivAt (segmentTaylorAverage f a k)
      (segmentTaylorAverage f a (k+1) x) x :=
  @segmentTaylorAverage_hasDerivAt f l r a x hf ha hx k

example
    {f : ℝ → ℝ} {l r a : ℝ}
    (hf : ∀ u ∈ Ioo l r, ContDiffAt ℝ ∞ f u)
    (ha : a ∈ Ioo l r) (k : ℕ) :
    ContDiffOn ℝ ∞ (segmentTaylorAverage f a k) (Ioo l r) :=
  @segmentTaylorAverage_contDiffOn f l r a hf ha k

example (f : ℝ → ℝ) (a x : ℝ) :
    segmentTaylorAverage f a 0 x =
      ∫ t in (0 : ℝ)..1, (1-t)*f (a+t*(x-a)) :=
  @segmentTaylorAverage_zero_eq_intervalIntegral f a x

example (f : ℝ → ℝ) (a : ℝ) :
    segmentTaylorAverage f a 0 a = f a/2 :=
  @segmentTaylorAverage_at_center f a

example
    {F : ℝ → ℝ} {l r a x : ℝ}
    (hF : ∀ u ∈ Ioo l r, ContDiffAt ℝ ∞ F u)
    (ha : a ∈ Ioo l r) (hx : x ∈ Ioo l r) :
    (x-a)^2*segmentTaylorAverage (deriv (deriv F)) a 0 x =
      F x-F a-(x-a)*deriv F a :=
  @segmentTaylorAverage_second F l r a x hF ha hx

example (F : ℝ → ℝ) (v : ℝ) :
    modelPhaseAveragedCurvature F v (modelPhaseInverseSlope F v) =
      modelPhaseCurvatureAt F v :=
  @modelPhaseAveragedCurvature_at_inverse F v

example
    {F : ℝ → ℝ} {σ δ v u : ℝ} {P : ℕ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) :
    ContDiffAt ℝ ∞ (modelPhaseAveragedCurvature F v) u :=
  @modelPhaseAveragedCurvature_contDiffAt F σ δ v u P hF hv hu

example
    {F : ℝ → ℝ} {σ δ v u : ℝ} {P : ℕ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) :
    modelPhaseStationaryDeficit F v u =
      (u-modelPhaseInverseSlope F v)^2/2*modelPhaseAveragedCurvature F v u :=
  @modelPhaseStationaryDeficit_eq_averagedCurvature F σ δ v u P hF hv hu

example
    {F : ℝ → ℝ} {σ δ v u : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) :
    modelPhaseCurvatureLower σ ≤ modelPhaseAveragedCurvature F v u ∧
      modelPhaseAveragedCurvature F v u ≤ σ+1 :=
  @modelPhaseAveragedCurvature_bounds F σ δ v u hσ hδ hF hv hu

example
    {F : ℝ → ℝ} {σ δ v u : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) :
    0 < modelPhaseAveragedCurvature F v u :=
  @modelPhaseAveragedCurvature_pos F σ δ v u hσ hδ hF hv hu

example
    {F : ℝ → ℝ} {σ δ v u : ℝ} {P : ℕ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) :
    modelPhaseMorseCoordinate F v u =
      (u-modelPhaseInverseSlope F v)*Real.sqrt (modelPhaseAveragedCurvature F v u) :=
  @modelPhaseMorseCoordinate_eq_smooth F σ δ v u P hF hv hu

example
    {F : ℝ → ℝ} {σ δ v u : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) :
    ContDiffAt ℝ ∞ (modelPhaseMorseCoordinate F v) u :=
  @modelPhaseMorseCoordinate_contDiffAt F σ δ v u hσ hδ hF hv hu

example
    {F : ℝ → ℝ} {σ δ v : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    ContDiffOn ℝ ∞ (modelPhaseMorseCoordinate F v) (Ioo (1 : ℝ) 2) :=
  @modelPhaseMorseCoordinate_contDiffOn F σ δ v hσ hδ hF hv

example
    {F : ℝ → ℝ} {σ δ u : ℝ} {P : ℕ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (v : ℝ) (hu : u ∈ Ioo (1 : ℝ) 2) :
    HasDerivAt (modelPhaseStationaryDeficit F v) (v-deriv F u) u :=
  @modelPhaseStationaryDeficit_hasDerivAt F σ δ u P hF v hu

example
    {F : ℝ → ℝ} {σ δ v u : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) :
    modelPhaseMorseCoordinate F v u * deriv (modelPhaseMorseCoordinate F v) u =
      v-deriv F u :=
  @modelPhaseMorseCoordinate_deriv_mul F σ δ v u hσ hδ hF hv hu

example
    {F : ℝ → ℝ} {σ δ v u : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) :
    0 < deriv (modelPhaseMorseCoordinate F v) u :=
  @modelPhaseMorseCoordinate_deriv_pos F σ δ v u hσ hδ hF hv hu

example
    {F : ℝ → ℝ} {σ δ v : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    StrictMonoOn (modelPhaseMorseCoordinate F v) (Ioo (1 : ℝ) 2) :=
  @modelPhaseMorseCoordinate_strictMonoOn F σ δ v hσ hδ hF hv

example {F : ℝ → ℝ} {v z : ℝ}
    (hz : z ∈ modelPhaseMorseRange F v) :
    modelPhaseMorseInverse F v z ∈ Ioo (1 : ℝ) 2 :=
  @modelPhaseMorseInverse_mem F v z hz

example {F : ℝ → ℝ} {v z : ℝ}
    (hz : z ∈ modelPhaseMorseRange F v) :
    modelPhaseMorseCoordinate F v (modelPhaseMorseInverse F v z) = z :=
  @modelPhaseMorseCoordinate_inverse F v z hz

example
    {F : ℝ → ℝ} {σ δ v u : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) :
    modelPhaseMorseInverse F v (modelPhaseMorseCoordinate F v u) = u :=
  @modelPhaseMorseInverse_coordinate F σ δ v u hσ hδ hF hv hu

example {F : ℝ → ℝ} {v : ℝ}
    (hv : v ∈ modelPhaseSlopeRange F) :
    0 ∈ modelPhaseMorseRange F v :=
  @zero_mem_modelPhaseMorseRange F v hv

example
    {F : ℝ → ℝ} {σ δ v : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    modelPhaseMorseInverse F v 0 = modelPhaseInverseSlope F v :=
  @modelPhaseMorseInverse_zero F σ δ v hσ hδ hF hv

example
    {F : ℝ → ℝ} {σ δ v z : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v) :
    HasStrictDerivAt (modelPhaseMorseInverse F v)
      (deriv (modelPhaseMorseCoordinate F v) (modelPhaseMorseInverse F v z))⁻¹ z :=
  @modelPhaseMorseInverse_hasStrictDerivAt F σ δ v z hσ hδ hF hv hz

example
    {F : ℝ → ℝ} {σ δ v : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    IsOpen (modelPhaseMorseRange F v) :=
  @modelPhaseMorseRange_isOpen F σ δ v hσ hδ hF hv

example
    {F : ℝ → ℝ} {σ δ v z : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v) :
    ContDiffAt ℝ ∞ (modelPhaseMorseInverse F v) z :=
  @modelPhaseMorseInverse_contDiffAt F σ δ v z hσ hδ hF hv hz

example
    {F : ℝ → ℝ} {σ δ v : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    HasDerivAt (modelPhaseMorseInverse F v) (modelPhaseStationaryAmplitude F v) 0 :=
  @modelPhaseMorseInverse_hasDerivAt_zero F σ δ v hσ hδ hF hv

example
    {F : ℝ → ℝ} {σ δ v z : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v) :
    F (modelPhaseMorseInverse F v z)-v*modelPhaseMorseInverse F v z =
      -modelPhaseLegendreDual F v-z^2/2 :=
  @modelPhaseMorseInverse_quadratic F σ δ v z hσ hδ hF hv hz

example
    {F : ℝ → ℝ} {σ δ T N r z : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : T ≠ 0) (hN : N ≠ 0)
    (hv : r*N/T ∈ modelPhaseSlopeRange F)
    (hz : z ∈ modelPhaseMorseRange F (r*N/T)) :
    modelPhaseFrequencyPhase F T N r (N*modelPhaseMorseInverse F (r*N/T) z) =
      modelPhaseFrequencyPhase F T N r (modelPhaseStationaryPoint F T N r) -(T/2)*z^2 :=
  @modelPhaseFrequencyPhase_morseInverse F σ δ T N r z hσ hδ hF hT hN hv hz

example
    {F : ℝ → ℝ} {σ δ u w : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hu : u ∈ Ioo (1 : ℝ) 2) (hw : w ∈ Ioo (1 : ℝ) 2) :
    |deriv F u-deriv F w| ≤ (σ+1)*|u-w| :=
  @approximateModelPhase_slope_gap_upper_abs F σ δ u w hσ hδ hF hu hw

example
    {F : ℝ → ℝ} {σ δ v u : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) :
    modelPhaseCurvatureLower σ/Real.sqrt (σ+1) ≤ deriv (modelPhaseMorseCoordinate F v) u ∧
      deriv (modelPhaseMorseCoordinate F v) u ≤ (σ+1)/Real.sqrt (modelPhaseCurvatureLower σ) :=
  @modelPhaseMorseCoordinate_deriv_bounds F σ δ v u hσ hδ hF hv hu

example
    {F : ℝ → ℝ} {σ δ v z : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v) :
    Real.sqrt (modelPhaseCurvatureLower σ)/(σ+1) ≤ deriv (modelPhaseMorseInverse F v) z ∧
      deriv (modelPhaseMorseInverse F v) z ≤ Real.sqrt (σ+1)/modelPhaseCurvatureLower σ :=
  @modelPhaseMorseInverse_deriv_bounds F σ δ v z hσ hδ hF hv hz

example (F : ℝ → ℝ) (v : ℝ) :
    InjOn (modelPhaseMorseInverse F v) (modelPhaseMorseRange F v) :=
  @modelPhaseMorseInverse_injOn F v

example
    {F : ℝ → ℝ} {σ δ v : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    modelPhaseMorseInverse F v '' modelPhaseMorseRange F v = Ioo (1 : ℝ) 2 :=
  @modelPhaseMorseInverse_image F σ δ v hσ hδ hF hv

example
    {F : ℝ → ℝ} {σ δ v z : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v) :
    0 < deriv (modelPhaseMorseInverse F v) z :=
  @modelPhaseMorseInverse_deriv_pos F σ δ v z hσ hδ hF hv hz

example
    {F : ℝ → ℝ} {σ δ v : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (g : ℝ → ℂ) :
    (∫ u in Ioo (1 : ℝ) 2, g u) =
      ∫ z in modelPhaseMorseRange F v,
        ((deriv (modelPhaseMorseInverse F v) z : ℝ) : ℂ)*g (modelPhaseMorseInverse F v z) :=
  @integral_Ioo_eq_morseIntegral F σ δ v hσ hδ hF hv g

example
    {F : ℝ → ℝ} {σ δ v : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (g : ℝ → ℂ) :
    IntegrableOn g (Ioo (1 : ℝ) 2) ↔
      IntegrableOn (fun z => ((deriv (modelPhaseMorseInverse F v) z : ℝ) : ℂ)*
        g (modelPhaseMorseInverse F v z)) (modelPhaseMorseRange F v) :=
  @integrableOn_Ioo_iff_morseIntegral F σ δ v hσ hδ hF hv g

example
    {χ F : ℝ → ℝ} {σ δ v z : ℝ}
    (hχ : ContDiff ℝ ∞ χ)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v) :
    ContDiffAt ℝ ∞ (modelPhaseMorseAmplitude χ F v) z :=
  @modelPhaseMorseAmplitude_contDiffAt χ F σ δ v z hχ hσ hδ hF hv hz

example
    {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    modelPhaseMorseAmplitude χ F v 0 =
      χ (modelPhaseInverseSlope F v)*modelPhaseStationaryAmplitude F v :=
  @modelPhaseMorseAmplitude_zero χ F σ δ v hσ hδ hF hv

example
    {χ F : ℝ → ℝ} {σ δ v z M : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v)
    (hM : 0 ≤ M) (hχ : ∀ u ∈ Ioo (1 : ℝ) 2, |χ u| ≤ M) :
    |modelPhaseMorseAmplitude χ F v z| ≤ M*(Real.sqrt (σ+1)/modelPhaseCurvatureLower σ) :=
  @abs_modelPhaseMorseAmplitude_le χ F σ δ v z M hσ hδ hF hv hz hM hχ

example
    {χ F : ℝ → ℝ} {σ δ v z : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v)
    (hχ : ∀ u ∈ Ioo (1 : ℝ) 2, 0 ≤ χ u) :
    0 ≤ modelPhaseMorseAmplitude χ F v z :=
  @modelPhaseMorseAmplitude_nonneg χ F σ δ v z hσ hδ hF hv hz hχ

example
    {χ F : ℝ → ℝ} {σ δ : ℝ} {P : ℕ}
    (hχ : Continuous χ) (hF : IsApproximateModelPhaseFunction F σ P δ) (T q : ℝ) :
    IntegrableOn (fun u : ℝ => (χ u : ℂ)*(𝐞 (T*F u-q*u) : ℂ)) (Icc (1 : ℝ) 2) :=
  @modelPhaseNormalizedIntegrand_integrableOn χ F σ δ P hχ hF T q

example
    {χ F : ℝ → ℝ} (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2) (T q : ℝ) :
    Function.support (fun u : ℝ => (χ u : ℂ)*(𝐞 (T*F u-q*u) : ℂ)) ⊆ Ioo (1 : ℝ) 2 :=
  @modelPhaseNormalizedIntegrand_support χ F hs T q

example
    {χ F : ℝ → ℝ} {σ δ : ℝ} {P : ℕ}
    (hχ : Continuous χ) (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hF : IsApproximateModelPhaseFunction F σ P δ) (T q : ℝ) :
    Integrable (fun u : ℝ => (χ u : ℂ)*(𝐞 (T*F u-q*u) : ℂ)) :=
  @modelPhaseNormalizedIntegrand_integrable χ F σ δ P hχ hs hF T q

example
    {χ F : ℝ → ℝ} {σ δ v z : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v) (T : ℝ) :
    ((deriv (modelPhaseMorseInverse F v) z : ℝ) : ℂ)*
        ((χ (modelPhaseMorseInverse F v z) : ℂ)*
          (𝐞 (T*F (modelPhaseMorseInverse F v z)-(T*v)*modelPhaseMorseInverse F v z) : ℂ)) =
      (𝐞 (-T*modelPhaseLegendreDual F v) : ℂ)*
        ((modelPhaseMorseAmplitude χ F v z : ℂ)*(𝐞 (-(T/2)*z^2) : ℂ)) :=
  @modelPhaseMorse_integrand χ F σ δ v z hσ hδ hF hv hz T

example
    {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hχ : Continuous χ)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (T : ℝ) :
    IntegrableOn (fun z => (modelPhaseMorseAmplitude χ F v z : ℂ)*
      (𝐞 (-(T/2)*z^2) : ℂ)) (modelPhaseMorseRange F v) :=
  @modelPhaseMorseWeightedIntegrand_integrableOn χ F σ δ v hχ hσ hδ hF hv T

example
    {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (T : ℝ) :
    modelPhaseNormalizedMode χ F T (T*v) =
      (𝐞 (-T*modelPhaseLegendreDual F v) : ℂ)*modelPhaseMorseWeightedIntegral χ F T v :=
  @modelPhaseNormalizedMode_morse χ F σ δ v hs hσ hδ hF hv T

example
    {χ F : ℝ → ℝ} {σ δ T N r : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : T ≠ 0) (hN : 0 < N)
    (hv : r*N/T ∈ modelPhaseSlopeRange F) :
    modelPhaseFourierMode χ F T N r =
      (N : ℂ)*(𝐞 (modelPhaseFrequencyPhase F T N r (modelPhaseStationaryPoint F T N r)) : ℂ)*
        modelPhaseMorseWeightedIntegral χ F T (r*N/T) :=
  @modelPhaseFourierMode_morse χ F σ δ T N r hs hσ hδ hF hT hN hv

example
    {F : ℝ → ℝ} {σ δ N : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) (hN : 0 < N)
    {a b : ℕ} (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧
      tsupport χ ⊆ Ioo (1 : ℝ) 2 ∧ HasCompactSupport χ ∧
      (∀ u : ℝ, 0 ≤ χ u ∧ χ u ≤ 1) ∧
      (∀ n : ℤ, χ ((n : ℝ)/N) =
        if n ∈ modelPhaseInteriorIndices N a b then 1 else 0) ∧
      ∀ T : ℝ, 0 < T →
        Summable (fun r : ℤ => ‖modelPhaseFourierMode χ F T N r‖) ∧
        ‖exponentialSumAt F T N a b -
          ∑' r : ℤ, modelPhaseFourierMode χ F T N r‖ ≤ 2 ∧
        ∀ r : ℤ, (r : ℝ)*N/T ∈ modelPhaseSlopeRange F →
          modelPhaseFourierMode χ F T N r =
            (N : ℂ)*(𝐞 (modelPhaseFrequencyPhase F T N r (modelPhaseStationaryPoint F T N r)) : ℂ)*
              modelPhaseMorseWeightedIntegral χ F T ((r : ℝ)*N/T) ∧
          IntegrableOn (fun z => (modelPhaseMorseAmplitude χ F ((r : ℝ)*N/T) z : ℂ)*
            (𝐞 (-(T/2)*z^2) : ℂ)) (modelPhaseMorseRange F ((r : ℝ)*N/T)) ∧
          ∀ z ∈ modelPhaseMorseRange F ((r : ℝ)*N/T),
            0 ≤ modelPhaseMorseAmplitude χ F ((r : ℝ)*N/T) z ∧
            modelPhaseMorseAmplitude χ F ((r : ℝ)*N/T) z ≤
              Real.sqrt (σ+1)/modelPhaseCurvatureLower σ :=
  @modelPhase_closed_interval_poisson_morse F σ δ N hσ hδ hF hN a b ha hb

-- The original logarithmic model is smooth through its actual critical point.
example :
    ContDiffAt ℝ ∞ (modelPhaseMorseCoordinate (referenceModelPrimitive 1) ((2 : ℝ)/3))
      (modelPhaseInverseSlope (referenceModelPrimitive 1) ((2 : ℝ)/3)) := by
  have hv := referenceModelPrimitive_slopeRange (by norm_num : (0 : ℝ) < 1)
    (by norm_num [Real.rpow_neg_one] : (2 : ℝ)/3 ∈ Ioo ((2 : ℝ)^(-(1 : ℝ))) 1)
  exact modelPhaseMorseCoordinate_contDiffAt (by norm_num)
    (le_min (modelPhaseCurvatureLower_pos (by norm_num)).le zero_le_one)
    (referenceModelPrimitive_approximate 1 1) hv (modelPhaseInverseSlope_mem hv)

example :
    modelPhaseMorseInverse (referenceModelPrimitive 1) ((2 : ℝ)/3) 0 =
      modelPhaseInverseSlope (referenceModelPrimitive 1) ((2 : ℝ)/3) := by
  exact modelPhaseMorseInverse_zero (by norm_num)
    (le_min (modelPhaseCurvatureLower_pos (by norm_num)).le zero_le_one)
    (referenceModelPrimitive_approximate 1 1)
    (referenceModelPrimitive_slopeRange (by norm_num) (by norm_num [Real.rpow_neg_one]))

example {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) :
    modelPhaseMorseInverse (referenceModelPrimitive 1) ((2 : ℝ)/3)
      (modelPhaseMorseCoordinate (referenceModelPrimitive 1) ((2 : ℝ)/3) u) = u := by
  exact modelPhaseMorseInverse_coordinate (by norm_num)
    (le_min (modelPhaseCurvatureLower_pos (by norm_num)).le zero_le_one)
    (referenceModelPrimitive_approximate 1 1)
    (referenceModelPrimitive_slopeRange (by norm_num) (by norm_num [Real.rpow_neg_one])) hu

example :
    HasDerivAt (modelPhaseMorseInverse (referenceModelPrimitive 1) ((2 : ℝ)/3))
      (modelPhaseStationaryAmplitude (referenceModelPrimitive 1) ((2 : ℝ)/3)) 0 := by
  exact modelPhaseMorseInverse_hasDerivAt_zero (by norm_num)
    (le_min (modelPhaseCurvatureLower_pos (by norm_num)).le zero_le_one)
    (referenceModelPrimitive_approximate 1 1)
    (referenceModelPrimitive_slopeRange (by norm_num) (by norm_num [Real.rpow_neg_one]))

-- A cutoff vanishing at the critical point must give zero main amplitude.
example {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F)
    (hχ : χ (modelPhaseInverseSlope F v) = 0) :
    modelPhaseMorseAmplitude χ F v 0 = 0 := by
  rw [modelPhaseMorseAmplitude_zero hσ hδ hF hv,hχ,zero_mul]

-- The normalized exact identity permits T=0; it is not an asymptotic assertion.
example {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    modelPhaseNormalizedMode χ F 0 0 = modelPhaseMorseWeightedIntegral χ F 0 v := by
  simpa using modelPhaseNormalizedMode_morse hs hσ hδ hF hv 0

example (χ F : ℝ → ℝ) (v : ℝ) :
    modelPhaseMorseWeightedIntegral χ F 0 v =
      ∫ z in modelPhaseMorseRange F v, (modelPhaseMorseAmplitude χ F v z : ℂ) := by
  simp [modelPhaseMorseWeightedIntegral]

-- An original closed endpoint singleton still enters the same source consumer.
example :
    ∃ χ : ℝ → ℝ, ∀ T : ℝ, 0 < T →
      ‖exponentialSumAt (referenceModelPrimitive 1) T 1 1 1 -
        ∑' r : ℤ, modelPhaseFourierMode χ (referenceModelPrimitive 1) T 1 r‖ ≤ 2 := by
  obtain ⟨χ,_,_,_,_,_,h⟩ := modelPhase_closed_interval_poisson_morse
    (by norm_num : (0 : ℝ) < 1)
    (le_min (modelPhaseCurvatureLower_pos (by norm_num)).le zero_le_one)
    (referenceModelPrimitive_approximate 1 1) (by norm_num : (0 : ℝ) < 1)
    (a := 1) (b := 1) (by norm_num) (by norm_num)
  exact ⟨χ,fun T hT => (h T hT).2.1⟩

example {z : ℝ}
    (hz : z ∈ modelPhaseMorseRange (referenceModelPrimitive 1) ((2 : ℝ)/3)) :
    Real.sqrt (modelPhaseCurvatureLower 1)/2 ≤
        deriv (modelPhaseMorseInverse (referenceModelPrimitive 1) ((2 : ℝ)/3)) z ∧
      deriv (modelPhaseMorseInverse (referenceModelPrimitive 1) ((2 : ℝ)/3)) z ≤
        Real.sqrt 2/modelPhaseCurvatureLower 1 := by
  simpa only [show (1 : ℝ)+1 = 2 by norm_num] using
    modelPhaseMorseInverse_deriv_bounds (by norm_num : (0 : ℝ) < 1)
    (le_min (modelPhaseCurvatureLower_pos (by norm_num)).le zero_le_one)
    (referenceModelPrimitive_approximate 1 1)
    (referenceModelPrimitive_slopeRange (by norm_num) (by norm_num [Real.rpow_neg_one])) hz

-- The cutoff-weighted physical main term has the exact source remainder normalization.
example
    {χ F : ℝ → ℝ} {σ δ T N r : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N)
    (hv : r*N/T ∈ modelPhaseSlopeRange F) :
    (N : ℂ)*(𝐞 (modelPhaseFrequencyPhase F T N r (modelPhaseStationaryPoint F T N r)) : ℂ)*
        ((modelPhaseMorseAmplitude χ F (r*N/T) 0/Real.sqrt T : ℂ)*
          (𝐞 (-(1 : ℝ)/8) : ℂ)) =
      (χ (modelPhaseInverseSlope F (r*N/T)) : ℂ)*modelPhaseStationaryMainTerm F T N r :=
  @modelPhaseMorseLeadingTerm_scale χ F σ δ T N r hσ hδ hF hT hN hv

example
    {χ F : ℝ → ℝ} {σ δ T N r : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N)
    (hv : r*N/T ∈ modelPhaseSlopeRange F) :
    modelPhaseFourierMode χ F T N r -
        (χ (modelPhaseInverseSlope F (r*N/T)) : ℂ)*modelPhaseStationaryMainTerm F T N r =
      (N : ℂ)*(𝐞 (modelPhaseFrequencyPhase F T N r (modelPhaseStationaryPoint F T N r)) : ℂ)*
        modelPhaseMorseRemainder χ F T (r*N/T) :=
  @modelPhaseFourierMode_sub_main_eq_morseRemainder χ F σ δ T N r hs hσ hδ hF hT hN hv

example
    {χ F : ℝ → ℝ} {σ δ T N r : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N)
    (hv : r*N/T ∈ modelPhaseSlopeRange F) :
    ‖modelPhaseFourierMode χ F T N r -
        (χ (modelPhaseInverseSlope F (r*N/T)) : ℂ)*modelPhaseStationaryMainTerm F T N r‖ =
      N*‖modelPhaseMorseRemainder χ F T (r*N/T)‖ :=
  @norm_modelPhaseFourierMode_sub_main χ F σ δ T N r hs hσ hδ hF hT hN hv

end SmoothQuadraticInverseRegression

section UniformQuadraticRemainderRegression

open Set Expdb Filter MeasureTheory
open scoped ContDiff Topology FourierTransform BigOperators

example {χ F : ℝ → ℝ} {v z : ℝ}
    (hz : z ∈ modelPhaseMorseRange F v) :
    modelPhaseMorseWeight χ F v z = modelPhaseMorseAmplitude χ F v z :=
  @modelPhaseMorseWeight_eq χ F v z hz

example {χ F : ℝ → ℝ} {v z : ℝ}
    (hz : z ∉ modelPhaseMorseRange F v) :
    modelPhaseMorseWeight χ F v z = 0 :=
  @modelPhaseMorseWeight_zero_of_not_mem χ F v z hz

example {χ F : ℝ → ℝ} {v : ℝ} :
    Function.support (modelPhaseMorseWeight χ F v) ⊆
      modelPhaseMorseCoordinate F v '' tsupport χ :=
  @modelPhaseMorseWeight_support_subset χ F v

example
    {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    IsCompact (modelPhaseMorseCoordinate F v '' tsupport χ) :=
  @isCompact_modelPhaseMorseCoordinate_image_tsupport χ F σ δ v hs hσ hδ hF hv

example
    {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    tsupport (modelPhaseMorseWeight χ F v) ⊆
      modelPhaseMorseCoordinate F v '' tsupport χ :=
  @modelPhaseMorseWeight_tsupport_subset χ F σ δ v hs hσ hδ hF hv

example
    {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    tsupport (modelPhaseMorseWeight χ F v) ⊆ modelPhaseMorseRange F v :=
  @modelPhaseMorseWeight_tsupport_subset_range χ F σ δ v hs hσ hδ hF hv

example
    {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    ContDiff ℝ ∞ (modelPhaseMorseWeight χ F v) :=
  @modelPhaseMorseWeight_contDiff χ F σ δ v hχ hs hσ hδ hF hv

example
    {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    HasCompactSupport (modelPhaseMorseWeight χ F v) :=
  @modelPhaseMorseWeight_hasCompactSupport χ F σ δ v hs hσ hδ hF hv

example
    {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    modelPhaseMorseWeight χ F v 0 =
      χ (modelPhaseInverseSlope F v)*modelPhaseStationaryAmplitude F v :=
  @modelPhaseMorseWeight_zero χ F σ δ v hσ hδ hF hv

example
    {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    tsupport (modelPhaseMorseWeight χ F v) ⊆
      Icc (-Real.sqrt (σ+1)) (Real.sqrt (σ+1)) :=
  @modelPhaseMorseWeight_tsupport_uniform χ F σ δ v hs hσ hδ hF hv

example
    {f : ℝ → ℝ} {l r a x : ℝ}
    (hf : ∀ u ∈ Ioo l r, ContDiffAt ℝ ∞ f u)
    (ha : a ∈ Ioo l r) (hx : x ∈ Ioo l r) (k n : ℕ) :
    iteratedDeriv n (segmentTaylorAverage f a k) x =
      segmentTaylorAverage f a (k+n) x :=
  @iteratedDeriv_segmentTaylorAverage f l r a x hf ha hx k n

example
    {f : ℝ → ℝ} {l r a x M : ℝ}
    (ha : a ∈ Ioo l r) (hx : x ∈ Ioo l r) (k : ℕ)
    (hb : ∀ u ∈ Ioo l r, |iteratedDeriv k f u| ≤ M) :
    |segmentTaylorAverage f a k x| ≤ M :=
  @abs_segmentTaylorAverage_le f l r a x M ha hx k hb

example
    {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hσ : 0 ≤ σ) (hF : IsApproximateModelPhaseFunction F σ P δ)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) (p : ℕ) (hp : p ≤ P) :
    |iteratedDeriv (p+1) F u| ≤ modelPhaseJetCoefficient σ p+δ :=
  @approximateModelPhase_iteratedDeriv_abs_le σ δ P F hσ hF u hu p hp

example
    {F : ℝ → ℝ} {σ δ v u : ℝ} {P : ℕ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) (k : ℕ) :
    iteratedDeriv k (modelPhaseAveragedCurvature F v) u =
      -2*segmentTaylorAverage (deriv (deriv F)) (modelPhaseInverseSlope F v) k u :=
  @iteratedDeriv_modelPhaseAveragedCurvature F σ δ v u P hF hv hu k

example
    {F : ℝ → ℝ} {σ δ v u : ℝ} {P : ℕ}
    (hσ : 0 ≤ σ) (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2)
    (k : ℕ) (hk : k+1 ≤ P) :
    |iteratedDeriv k (modelPhaseAveragedCurvature F v) u| ≤
      2*(modelPhaseJetCoefficient σ (k+1)+δ) :=
  @abs_iteratedDeriv_modelPhaseAveragedCurvature_le F σ δ v u P hσ hF hv hu k hk

example
    {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (z : ℝ) :
    modelPhaseMorseSchwartz hχ hs hσ hδ hF hv z = modelPhaseMorseWeight χ F v z :=
  @modelPhaseMorseSchwartz_apply χ F σ δ v hχ hs hσ hδ hF hv z

example
    {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (T : ℝ) :
    modelPhaseMorseWeightedIntegral χ F T v =
      ∫ z : ℝ, (modelPhaseMorseWeight χ F v z : ℂ)*(𝐞 (-(T/2)*z^2) : ℂ) :=
  @modelPhaseMorseWeightedIntegral_eq_global χ F σ δ v hσ hδ hF hv T

example
    {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hχ : Continuous χ)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (T : ℝ) :
    Integrable (fun z : ℝ => (modelPhaseMorseWeight χ F v z : ℂ)*
      (𝐞 (-(T/2)*z^2) : ℂ)) :=
  @modelPhaseMorseGlobalIntegrand_integrable χ F σ δ v hχ hσ hδ hF hv T

example
    {χ F : ℝ → ℝ} {σ δ T N r : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : T ≠ 0) (hN : 0 < N)
    (hv : r*N/T ∈ modelPhaseSlopeRange F) :
    modelPhaseFourierMode χ F T N r =
      (N : ℂ)*(𝐞 (modelPhaseFrequencyPhase F T N r (modelPhaseStationaryPoint F T N r)) : ℂ)*
        ∫ z : ℝ, (modelPhaseMorseWeight χ F (r*N/T) z : ℂ)*(𝐞 (-(T/2)*z^2) : ℂ) :=
  @modelPhaseFourierMode_eq_global_morse χ F σ δ T N r hs hσ hδ hF hT hN hv

example
    {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (k : ℕ) :
    tsupport (iteratedDeriv k (modelPhaseMorseWeight χ F v)) ⊆
      modelPhaseMorseCoordinate F v '' tsupport χ :=
  @modelPhaseMorseWeight_deriv_support χ F σ δ v hs hσ hδ hF hv k

example
    {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (k : ℕ) :
    Integrable (iteratedDeriv k (modelPhaseMorseWeight χ F v)) :=
  @modelPhaseMorseWeight_iteratedDeriv_integrable χ F σ δ v hχ hs hσ hδ hF hv k

example
    {F : ℝ → ℝ} {σ δ v u : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) (j : ℕ) :
    HasDerivAt (fun x => modelPhaseMorseJet F v x j)
      (inversePhaseEval (morseAtomDerivative j) (modelPhaseMorseJet F v u)) u :=
  @modelPhaseMorseJet_hasDerivAt F σ δ v u hσ hδ hF hv hu j

example
    {F : ℝ → ℝ} {σ δ v u : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2)
    (e : InversePhaseExpression) :
    HasDerivAt (fun x => inversePhaseEval e (modelPhaseMorseJet F v x))
      (inversePhaseEval (morseDifferentiate e) (modelPhaseMorseJet F v u)) u :=
  @morseEval_hasDerivAt F σ δ v u hσ hδ hF hv hu e

example
    {F : ℝ → ℝ} {σ δ v u : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) (n : ℕ) :
    iteratedDeriv n (modelPhaseMorseCoordinate F v) u =
      inversePhaseEval (morseDerivativeExpression n) (modelPhaseMorseJet F v u) :=
  @iteratedDeriv_modelPhaseMorseCoordinate_formula F σ δ v u hσ hδ hF hv hu n

example (σ : ℝ) (j : ℕ) :
    0 ≤ morseJetMagnitude σ j :=
  @morseJetMagnitude_nonneg σ j

example (σ : ℝ) {K j : ℕ} (hj : j ≤ K) :
    morseJetMagnitude σ j ≤ morseJetMagnitudeBudget σ K :=
  @morseJetMagnitude_le_budget σ K j hj

example (σ : ℝ) (n : ℕ) :
    0 ≤ morseCoordinateDerivativeBound σ n :=
  @morseCoordinateDerivativeBound_nonneg σ n

example
    {F : ℝ → ℝ} {σ δ v u : ℝ} {P : ℕ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hP : 1 ≤ P) (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2)
    (j : ℕ) (hj : j ≤ P) :
    |modelPhaseMorseJet F v u j| ≤ morseJetMagnitude σ j :=
  @modelPhaseMorseJet_abs_le F σ δ v u P hσ hδ hP hF hv hu j hj

example
    {F : ℝ → ℝ} {σ δ v u : ℝ} {P : ℕ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2)
    (n : ℕ) (hP : morseCoordinateDerivativeOrder n ≤ P) :
    |iteratedDeriv n (modelPhaseMorseCoordinate F v) u| ≤
      morseCoordinateDerivativeBound σ n :=
  @modelPhaseMorseCoordinate_iteratedDeriv_bound F σ δ v u P hσ hδ hF hv hu n hP

example
    {F : ℝ → ℝ} {σ δ v z : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v) (j : ℕ) :
    HasDerivAt (fun x => modelPhaseMorseInverseJet F v x j)
      (inversePhaseEval (inversePhaseAtomDerivative j) (modelPhaseMorseInverseJet F v z)) z :=
  @modelPhaseMorseInverseJet_hasDerivAt F σ δ v z hσ hδ hF hv hz j

example
    {F : ℝ → ℝ} {σ δ v z : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v)
    (e : InversePhaseExpression) :
    HasDerivAt (fun x => inversePhaseEval e (modelPhaseMorseInverseJet F v x))
      (inversePhaseEval (inversePhaseDifferentiate e) (modelPhaseMorseInverseJet F v z)) z :=
  @morseInverseEval_hasDerivAt F σ δ v z hσ hδ hF hv hz e

example
    {F : ℝ → ℝ} {σ δ v z : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v) (n : ℕ) :
    iteratedDeriv n (modelPhaseMorseInverse F v) z =
      inversePhaseEval (inversePhaseDerivativeExpression n) (modelPhaseMorseInverseJet F v z) :=
  @iteratedDeriv_modelPhaseMorseInverse_formula F σ δ v z hσ hδ hF hv hz n

example {σ : ℝ} (hσ : 0 < σ) (j : ℕ) :
    0 ≤ morseInverseJetMagnitude σ j :=
  @morseInverseJetMagnitude_nonneg σ hσ j

example {σ : ℝ} (hσ : 0 < σ) {K j : ℕ} (hj : j ≤ K) :
    morseInverseJetMagnitude σ j ≤ morseInverseJetBudget σ K :=
  @morseInverseJetMagnitude_le_budget σ hσ K j hj

example (n : ℕ) : 1 ≤ morseInverseDerivativeOrder n :=
  @morseInverseDerivativeOrder_pos n

example {n j : ℕ}
    (hj : j ≤ inversePhaseOrder (inversePhaseDerivativeExpression n)) :
    morseInverseJetOrder j ≤ morseInverseDerivativeOrder n :=
  @morseInverseJetOrder_le_derivativeOrder n j hj

example {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    0 ≤ morseInverseDerivativeBound σ n :=
  @morseInverseDerivativeBound_nonneg σ hσ n

example
    {F : ℝ → ℝ} {σ δ v z : ℝ} {P : ℕ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hP : 1 ≤ P) (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v)
    (j : ℕ) (hj : morseInverseJetOrder j ≤ P) :
    |modelPhaseMorseInverseJet F v z j| ≤ morseInverseJetMagnitude σ j :=
  @modelPhaseMorseInverseJet_abs_le F σ δ v z P hσ hδ hP hF hv hz j hj

example
    {F : ℝ → ℝ} {σ δ v z : ℝ} {P : ℕ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v)
    (n : ℕ) (hP : morseInverseDerivativeOrder n ≤ P) :
    |iteratedDeriv n (modelPhaseMorseInverse F v) z| ≤
      morseInverseDerivativeBound σ n :=
  @modelPhaseMorseInverse_iteratedDeriv_bound F σ δ v z P hσ hδ hF hv hz n hP

example
    {χ F : ℝ → ℝ} {σ δ v z : ℝ}
    (hχ : ContDiff ℝ ∞ χ)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v) (j : ℕ) :
    HasDerivAt (fun x => morseWeightJet χ F v x j)
      (inversePhaseEval (morseWeightAtomDerivative j) (morseWeightJet χ F v z)) z :=
  @morseWeightJet_hasDerivAt χ F σ δ v z hχ hσ hδ hF hv hz j

example
    {χ F : ℝ → ℝ} {σ δ v z : ℝ}
    (hχ : ContDiff ℝ ∞ χ)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v)
    (e : InversePhaseExpression) :
    HasDerivAt (fun x => inversePhaseEval e (morseWeightJet χ F v x))
      (inversePhaseEval (morseWeightDifferentiate e) (morseWeightJet χ F v z)) z :=
  @morseWeightEval_hasDerivAt χ F σ δ v z hχ hσ hδ hF hv hz e

example
    {χ F : ℝ → ℝ} {σ δ v z : ℝ}
    (hχ : ContDiff ℝ ∞ χ)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v) (n : ℕ) :
    iteratedDeriv n (modelPhaseMorseAmplitude χ F v) z =
      inversePhaseEval (morseWeightDerivativeExpression n) (morseWeightJet χ F v z) :=
  @iteratedDeriv_modelPhaseMorseAmplitude_formula χ F σ δ v z hχ hσ hδ hF hv hz n

example
    {χ F : ℝ → ℝ} {σ δ v z : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v) (n : ℕ) :
    iteratedDeriv n (modelPhaseMorseWeight χ F v) z =
      iteratedDeriv n (modelPhaseMorseAmplitude χ F v) z :=
  @iteratedDeriv_modelPhaseMorseWeight_eq χ F σ δ v z hσ hδ hF hv hz n

example
    {χ F : ℝ → ℝ} {σ δ v z : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∉ modelPhaseMorseRange F v) (n : ℕ) :
    iteratedDeriv n (modelPhaseMorseWeight χ F v) z = 0 :=
  @iteratedDeriv_modelPhaseMorseWeight_zero χ F σ δ v z hs hσ hδ hF hv hz n

example (n : ℕ) : 1 ≤ morseWeightDerivativeOrder n :=
  @morseWeightDerivativeOrder_pos n

example {σ M : ℝ} (hσ : 0 < σ) (hM : 0 ≤ M) (n : ℕ) :
    0 ≤ morseWeightDerivativeBound σ M n :=
  @morseWeightDerivativeBound_nonneg σ M hσ hM n

example {n j : ℕ} (hj : j ≤ morseWeightCutoffOrder n+1) :
    morseInverseDerivativeOrder j ≤ morseWeightDerivativeOrder n :=
  @morseWeight_inverseOrder_le n j hj

example
    {χ F : ℝ → ℝ} {σ δ v z M : ℝ} {P : ℕ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v)
    (hM : 0 ≤ M) (n : ℕ) (hP : morseWeightDerivativeOrder n ≤ P)
    (hχ : ∀ u ∈ Ioo (1 : ℝ) 2, ∀ k ≤ morseWeightCutoffOrder n, |iteratedDeriv k χ u| ≤ M)
    (j : ℕ) (hj : j ≤ morseWeightCutoffOrder n) :
    |morseWeightJet χ F v z j| ≤ morseWeightJetBudget σ M n :=
  @morseWeightJet_abs_le χ F σ δ v z M P hσ hδ hF hv hz hM n hP hχ j hj

example
    {χ F : ℝ → ℝ} {σ δ v M : ℝ} {P : ℕ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hM : 0 ≤ M)
    (n : ℕ) (hP : morseWeightDerivativeOrder n ≤ P)
    (hb : ∀ u ∈ Ioo (1 : ℝ) 2, ∀ k ≤ morseWeightCutoffOrder n, |iteratedDeriv k χ u| ≤ M)
    (z : ℝ) :
    |iteratedDeriv n (modelPhaseMorseWeight χ F v) z| ≤ morseWeightDerivativeBound σ M n :=
  @modelPhaseMorseWeight_iteratedDeriv_bound χ F σ δ v M P hχ hs hσ hδ hF hv hM n hP hb z

example {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (Q : ℕ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ u ∈ Ioo (1 : ℝ) 2, ∀ k ≤ Q, |iteratedDeriv k χ u| ≤ M :=
  @smoothCutoff_finite_jet_bound χ hχ Q

example
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (F : ℝ → ℝ) (δ v : ℝ),
      δ ≤ min (modelPhaseCurvatureLower σ) 1 →
      IsApproximateModelPhaseFunction F σ (morseWeightDerivativeOrder n) δ →
      v ∈ modelPhaseSlopeRange F →
      ∀ z : ℝ, |iteratedDeriv n (modelPhaseMorseWeight χ F v) z| ≤ C :=
  @modelPhaseMorseWeight_uniform_derivative χ hχ hs σ hσ n

example
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (a x : ℝ) (k : ℕ) :
    HasDerivAt (segmentTaylorAverage f a k) (segmentTaylorAverage f a (k+1) x) x :=
  @segmentTaylorAverage_hasDerivAt_global f hf a x k

example
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (a : ℝ) (k : ℕ) :
    ContDiff ℝ ∞ (segmentTaylorAverage f a k) :=
  @segmentTaylorAverage_contDiff_global f hf a k

example
    {f : ℝ → ℝ} {M : ℝ} (a x : ℝ) (k : ℕ)
    (hb : ∀ u : ℝ, |iteratedDeriv k f u| ≤ M) :
    |segmentTaylorAverage f a k x| ≤ M :=
  @abs_segmentTaylorAverage_le_global f M a x k hb

example
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (a x : ℝ) :
    (x-a)^2*segmentTaylorAverage (deriv (deriv f)) a 0 x =
      f x-f a-(x-a)*deriv f a :=
  @segmentTaylorAverage_second_global f hf a x

example (T : ℝ) : Continuous (betaQuadraticKernel T) :=
  @continuous_betaQuadraticKernel T

example (T z : ℝ) : ‖betaQuadraticKernel T z‖ = 1 :=
  @norm_betaQuadraticKernel T z

example (T z : ℝ) :
    betaQuadraticKernel T (-z) = betaQuadraticKernel T z :=
  @betaQuadraticKernel_neg T z

example (T z : ℝ) :
    HasDerivAt (betaQuadraticKernel T)
      ((-2*Real.pi*T : ℂ)*Complex.I*(z : ℂ)*betaQuadraticKernel T z) z :=
  @betaQuadraticKernel_hasDerivAt T z

example (T H : ℝ) :
    (∫ z in (-H)..H, (z : ℂ)*betaQuadraticKernel T z) = 0 :=
  @integral_betaQuadraticKernel_odd T H

example (T H : ℝ) :
    (∫ z in (-H)..H, betaQuadraticKernel T z) = atkinsonQuadraticWindow (T/2) H :=
  @integral_betaQuadraticKernel_eq_window T H

example {T H : ℝ} (hT : 0 < T) (hH : 0 < H) :
    ‖(∫ z in (-H)..H, betaQuadraticKernel T z) -
      (𝐞 (-(1 : ℝ)/8) : ℂ)/(Real.sqrt T : ℂ)‖ ≤ 4/(T*H*Real.pi) :=
  @norm_betaQuadraticWindow_sub_main T H hT hH

example
    {V : ℝ → ℝ} {T H M L : ℝ}
    (hV : ContDiff ℝ ∞ V) (hT : 0 < T) (hH : 0 < H)
    (hb : ∀ z : ℝ, |V z| ≤ M) (hd : ∀ z : ℝ, |deriv V z| ≤ L) :
    ‖∫ z in (-H)..H, ((z^2*V z : ℝ) : ℂ)*betaQuadraticKernel T z‖ ≤
      (2*H*M+2*H*(M+H*L))/(2*Real.pi*T) :=
  @norm_integral_sq_mul_betaQuadraticKernel_le V T H M L hV hT hH hb hd

example {W : ℝ → ℝ} (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (quadraticTaylorCoefficient W) :=
  @quadraticTaylorCoefficient_contDiff W hW

example {W : ℝ → ℝ} (hW : ContDiff ℝ ∞ W) (z : ℝ) :
    deriv (quadraticTaylorCoefficient W) z = segmentTaylorAverage (deriv (deriv W)) 0 1 z :=
  @quadraticTaylorCoefficient_deriv W hW z

example {W : ℝ → ℝ} {M : ℝ}
    (hb : ∀ z : ℝ, |iteratedDeriv 2 W z| ≤ M) (z : ℝ) :
    |quadraticTaylorCoefficient W z| ≤ M :=
  @abs_quadraticTaylorCoefficient_le W M hb z

example {W : ℝ → ℝ} {M : ℝ}
    (hW : ContDiff ℝ ∞ W) (hb : ∀ z : ℝ, |iteratedDeriv 3 W z| ≤ M) (z : ℝ) :
    |deriv (quadraticTaylorCoefficient W) z| ≤ M :=
  @abs_deriv_quadraticTaylorCoefficient_le W M hW hb z

example
    {W : ℝ → ℝ} (hW : ContDiff ℝ ∞ W) (T H : ℝ) :
    (∫ z in (-H)..H, (W z : ℂ)*betaQuadraticKernel T z) =
      (W 0 : ℂ)*(∫ z in (-H)..H, betaQuadraticKernel T z)+
      ∫ z in (-H)..H, ((z^2*quadraticTaylorCoefficient W z : ℝ) : ℂ)*
        betaQuadraticKernel T z :=
  @integral_weighted_betaQuadraticKernel_taylor W hW T H

example {H M₀ M₂ M₃ : ℝ}
    (hH : 0 < H) (h₀ : 0 ≤ M₀) (h₂ : 0 ≤ M₂) (h₃ : 0 ≤ M₃) :
    0 ≤ quadraticRemainderConstant H M₀ M₂ M₃ :=
  @quadraticRemainderConstant_nonneg H M₀ M₂ M₃ hH h₀ h₂ h₃

example
    {W : ℝ → ℝ} {T H M₀ M₂ M₃ : ℝ}
    (hW : ContDiff ℝ ∞ W) (hT : 0 < T) (hH : 0 < H)
    (h₀ : |W 0| ≤ M₀)
    (h₂ : ∀ z : ℝ, |iteratedDeriv 2 W z| ≤ M₂)
    (h₃ : ∀ z : ℝ, |iteratedDeriv 3 W z| ≤ M₃) :
    ‖(∫ z in (-H)..H, (W z : ℂ)*betaQuadraticKernel T z)-
      (W 0 : ℂ)*((𝐞 (-(1 : ℝ)/8) : ℂ)/(Real.sqrt T : ℂ))‖ ≤
        quadraticRemainderConstant H M₀ M₂ M₃/T :=
  @norm_quadratic_window_remainder_le W T H M₀ M₂ M₃ hW hT hH h₀ h₂ h₃

example
    {W : ℝ → ℝ} {T H M₀ M₂ M₃ : ℝ}
    (hW : ContDiff ℝ ∞ W) (hT : 0 < T) (hH : 0 < H)
    (hs : Function.support W ⊆ Ioc (-H) H)
    (h₀ : |W 0| ≤ M₀)
    (h₂ : ∀ z : ℝ, |iteratedDeriv 2 W z| ≤ M₂)
    (h₃ : ∀ z : ℝ, |iteratedDeriv 3 W z| ≤ M₃) :
    ‖(∫ z : ℝ, (W z : ℂ)*betaQuadraticKernel T z)-
      (W 0 : ℂ)*((𝐞 (-(1 : ℝ)/8) : ℂ)/(Real.sqrt T : ℂ))‖ ≤
        quadraticRemainderConstant H M₀ M₂ M₃/T :=
  @norm_quadratic_global_remainder_le W T H M₀ M₂ M₃ hW hT hH hs h₀ h₂ h₃

example
    {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (T : ℝ) :
    modelPhaseMorseRemainder χ F T v =
      (∫ z : ℝ, (modelPhaseMorseWeight χ F v z : ℂ)*betaQuadraticKernel T z)-
        (modelPhaseMorseWeight χ F v 0 : ℂ)*
          ((𝐞 (-(1 : ℝ)/8) : ℂ)/(Real.sqrt T : ℂ)) :=
  @modelPhaseMorseRemainder_eq_global χ F σ δ v hσ hδ hF hv T

example
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ P : ℕ, 1 ≤ P ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ (F : ℝ → ℝ) (δ v T : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ P δ →
        v ∈ modelPhaseSlopeRange F → 0 < T →
        ‖modelPhaseMorseRemainder χ F T v‖ ≤ C/T :=
  @modelPhaseMorseRemainder_uniform χ hχ hs σ hσ

example
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ P : ℕ, 1 ≤ P ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ (F : ℝ → ℝ) (δ T N r : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ P δ →
        0 < T → 0 < N → r*N/T ∈ modelPhaseSlopeRange F →
        ‖modelPhaseFourierMode χ F T N r-
          (χ (modelPhaseInverseSlope F (r*N/T)) : ℂ)*modelPhaseStationaryMainTerm F T N r‖ ≤
            C*N/T :=
  @modelPhaseFourierMode_stationary_uniform χ hχ hs σ hσ

example
    {N : ℝ} (hN : 0 < N) {a b : ℕ}
    (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧
      tsupport χ ⊆ Ioo (1 : ℝ) 2 ∧ HasCompactSupport χ ∧
      (∀ u : ℝ, 0 ≤ χ u ∧ χ u ≤ 1) ∧
      (∀ n : ℤ, χ ((n : ℝ)/N) =
        if n ∈ modelPhaseInteriorIndices N a b then 1 else 0) ∧
      ∀ σ : ℝ, 0 < σ → ∃ P : ℕ, 1 ≤ P ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (δ : ℝ),
          δ ≤ min (modelPhaseCurvatureLower σ) 1 →
          IsApproximateModelPhaseFunction F σ P δ →
          ∀ T : ℝ, 0 < T →
            Summable (fun r : ℤ => ‖modelPhaseFourierMode χ F T N r‖) ∧
            ‖exponentialSumAt F T N a b-∑' r : ℤ, modelPhaseFourierMode χ F T N r‖ ≤ 2 ∧
            ∀ r : ℤ, (r : ℝ)*N/T ∈ modelPhaseSlopeRange F →
              ‖modelPhaseFourierMode χ F T N r-
                (χ (modelPhaseInverseSlope F ((r : ℝ)*N/T)) : ℂ)*
                  modelPhaseStationaryMainTerm F T N r‖ ≤ C*N/T :=
  @modelPhase_closed_interval_poisson_stationary N hN a b ha hb

example (F : ℝ → ℝ) (v z : ℝ) :
    modelPhaseMorseWeight (fun _ => 0) F v z = 0 := by
  simp [modelPhaseMorseWeight,modelPhaseMorseAmplitude]

example (F : ℝ → ℝ) (v z : ℝ) (n : ℕ) :
    iteratedDeriv n (modelPhaseMorseWeight (fun _ => 0) F v) z = 0 := by
  have he : modelPhaseMorseWeight (fun _ => 0) F v = fun _ => 0 := by
    funext x
    simp [modelPhaseMorseWeight,modelPhaseMorseAmplitude]
  rw [he]
  simp

example {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hzero : χ (modelPhaseInverseSlope F v) = 0) :
    modelPhaseMorseWeight χ F v 0 = 0 := by
  rw [modelPhaseMorseWeight_zero hσ hδ hF hv,hzero,zero_mul]

example {σ v u : ℝ} (hσ : 0 < σ)
    (hv : v ∈ Ioo ((2 : ℝ)^(-σ)) 1) (hu : u ∈ Ioo (1 : ℝ) 2) :
    |iteratedDeriv 3 (modelPhaseMorseCoordinate (referenceModelPrimitive σ) v) u| ≤
      morseCoordinateDerivativeBound σ 3 := by
  exact modelPhaseMorseCoordinate_iteratedDeriv_bound hσ
    (le_min (modelPhaseCurvatureLower_pos hσ).le zero_le_one)
    (referenceModelPrimitive_approximate σ (morseCoordinateDerivativeOrder 3))
    (referenceModelPrimitive_slopeRange hσ hv) hu 3 le_rfl

example {σ v : ℝ} (hσ : 0 < σ) (hv : v ∈ Ioo ((2 : ℝ)^(-σ)) 1) :
    |iteratedDeriv 2 (modelPhaseMorseInverse (referenceModelPrimitive σ) v) 0| ≤
      morseInverseDerivativeBound σ 2 := by
  have hr := referenceModelPrimitive_slopeRange hσ hv
  exact modelPhaseMorseInverse_iteratedDeriv_bound hσ
    (le_min (modelPhaseCurvatureLower_pos hσ).le zero_le_one)
    (referenceModelPrimitive_approximate σ (morseInverseDerivativeOrder 2))
    hr (zero_mem_modelPhaseMorseRange hr) 2 le_rfl

example (z : ℝ) : betaQuadraticKernel 0 z = 1 := by
  simp [betaQuadraticKernel]

example {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    modelPhaseMorseWeightedIntegral χ F 0 v =
      ∫ z : ℝ, (modelPhaseMorseWeight χ F v z : ℂ) := by
  simpa using modelPhaseMorseWeightedIntegral_eq_global (χ := χ) hσ hδ hF hv 0

example {T H : ℝ} (hT : 0 < T) (hH : 0 < H) :
    ‖(∫ z : ℝ, ((0 : ℝ) : ℂ)*betaQuadraticKernel T z)-
      ((0 : ℝ) : ℂ)*((𝐞 (-(1 : ℝ)/8) : ℂ)/(Real.sqrt T : ℂ))‖ ≤
        quadraticRemainderConstant H 0 0 0/T := by
  exact norm_quadratic_global_remainder_le contDiff_const hT hH
    (by simp) (by simp) (by simp) (by simp)

example {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ P : ℕ, 1 ≤ P ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ (F : ℝ → ℝ) (δ T N r : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ P δ →
        0 < T → 0 < N → r*N/T ∈ modelPhaseSlopeRange F →
        χ (modelPhaseInverseSlope F (r*N/T)) = 0 →
        ‖modelPhaseFourierMode χ F T N r‖ ≤ C*N/T := by
  obtain ⟨P,hP,C,hC,hbound⟩ := modelPhaseFourierMode_stationary_uniform hχ hs hσ
  refine ⟨P,hP,C,hC,?_⟩
  intro F δ T N r hδ hF hT hN hv hzero
  simpa only [hzero,Complex.ofReal_zero,zero_mul,sub_zero] using hbound F δ T N r hδ hF hT hN hv

example :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧
      tsupport χ ⊆ Ioo (1 : ℝ) 2 ∧ HasCompactSupport χ ∧
      (∀ u : ℝ, 0 ≤ χ u ∧ χ u ≤ 1) ∧
      (∀ n : ℤ, χ ((n : ℝ)/1) =
        if n ∈ modelPhaseInteriorIndices 1 1 1 then 1 else 0) ∧
      ∀ σ : ℝ, 0 < σ → ∃ P : ℕ, 1 ≤ P ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (δ : ℝ),
          δ ≤ min (modelPhaseCurvatureLower σ) 1 →
          IsApproximateModelPhaseFunction F σ P δ →
          ∀ T : ℝ, 0 < T →
            Summable (fun r : ℤ => ‖modelPhaseFourierMode χ F T 1 r‖) ∧
            ‖exponentialSumAt F T 1 1 1-∑' r : ℤ, modelPhaseFourierMode χ F T 1 r‖ ≤ 2 ∧
            ∀ r : ℤ, (r : ℝ)*1/T ∈ modelPhaseSlopeRange F →
              ‖modelPhaseFourierMode χ F T 1 r-
                (χ (modelPhaseInverseSlope F ((r : ℝ)*1/T)) : ℂ)*
                  modelPhaseStationaryMainTerm F T 1 r‖ ≤ C*1/T := by
  exact modelPhase_closed_interval_poisson_stationary (N := 1) (a := 1) (b := 1)
    (by norm_num) (by norm_num) (by norm_num)

end UniformQuadraticRemainderRegression

section BufferedFamilyRegression

open Set Expdb Filter MeasureTheory
open scoped ContDiff Topology FourierTransform BigOperators

example (Q : ℕ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ x : ℝ, ∀ j ≤ Q,
      |iteratedDeriv j Real.smoothTransition x| ≤ M :=
  @smoothTransition_finite_jet_bound Q

example (l r η u : ℝ) :
    0 ≤ modelPhaseBufferedCutoff l r η u :=
  @modelPhaseBufferedCutoff_nonneg l r η u

example (l r η u : ℝ) :
    modelPhaseBufferedCutoff l r η u ≤ 1 :=
  @modelPhaseBufferedCutoff_le_one l r η u

example (l r η : ℝ) :
    ContDiff ℝ ∞ (modelPhaseBufferedCutoff l r η) :=
  @modelPhaseBufferedCutoff_contDiff l r η

example {l r η u : ℝ}
    (hη : 0 < η) (hu : u ≤ l+η) :
    modelPhaseBufferedCutoff l r η u = 0 :=
  @modelPhaseBufferedCutoff_zero_left l r η u hη hu

example {l r η u : ℝ}
    (hη : 0 < η) (hu : r-η ≤ u) :
    modelPhaseBufferedCutoff l r η u = 0 :=
  @modelPhaseBufferedCutoff_zero_right l r η u hη hu

example {l r η u : ℝ}
    (hη : 0 < η) (hl : l+2*η ≤ u) (hr : u ≤ r-2*η) :
    modelPhaseBufferedCutoff l r η u = 1 :=
  @modelPhaseBufferedCutoff_one l r η u hη hl hr

example {l r η : ℝ} (hη : 0 < η) :
    tsupport (modelPhaseBufferedCutoff l r η) ⊆ Icc (l+η) (r-η) :=
  @modelPhaseBufferedCutoff_tsupport l r η hη

example {l r η : ℝ} (hη : 0 < η) :
    HasCompactSupport (modelPhaseBufferedCutoff l r η) :=
  @modelPhaseBufferedCutoff_hasCompactSupport l r η hη

example {l r η : ℝ}
    (hη : 0 < η) (hl : 1 ≤ l) (hr : r ≤ 2) :
    tsupport (modelPhaseBufferedCutoff l r η) ⊆ Ioo (1 : ℝ) 2 :=
  @modelPhaseBufferedCutoff_tsupport_model l r η hη hl hr

example
    (l r η u : ℝ) (n : ℕ) :
    iteratedDeriv n (modelPhaseBufferedCutoff l r η) u =
      ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) *
        ((η⁻¹)^j * iteratedDeriv j Real.smoothTransition ((u-l)/η-1)) *
        ((-η⁻¹)^(n-j) * iteratedDeriv (n-j) Real.smoothTransition ((r-u)/η-1)) :=
  @iteratedDeriv_modelPhaseBufferedCutoff l r η u n

example
    {M η : ℝ} (hM : 0 ≤ M) (hη : 0 < η)
    (n : ℕ)
    (hb : ∀ x : ℝ, ∀ j ≤ n, |iteratedDeriv j Real.smoothTransition x| ≤ M)
    (l r u : ℝ) :
    |iteratedDeriv n (modelPhaseBufferedCutoff l r η) u| ≤
      (2 : ℝ)^n*M^2*(η⁻¹)^n :=
  @abs_iteratedDeriv_modelPhaseBufferedCutoff_le M η hM hη n hb l r u

example (Q : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l r η u : ℝ), 0 < η → η ≤ 1 →
      ∀ j ≤ Q, |iteratedDeriv j (modelPhaseBufferedCutoff l r η) u| ≤ C*(η⁻¹)^Q :=
  @modelPhaseBufferedCutoff_uniform_jets Q

example (e : InversePhaseExpression)
    {B C : ℝ} (hB : 0 ≤ B) (hBC : B ≤ C) :
    inversePhaseMagnitude e B ≤ inversePhaseMagnitude e C :=
  @inversePhaseMagnitude_mono e B C hB hBC

example (e : InversePhaseExpression)
    {B A : ℝ} (hB : 0 ≤ B) (hA : 1 ≤ A) :
    inversePhaseMagnitude e (B*A) ≤ inversePhaseMagnitude e B*A^(inversePhaseDegree e) :=
  @inversePhaseMagnitude_scale_le e B A hB hA

example {σ M A : ℝ}
    (hσ : 0 < σ) (hM : 0 ≤ M) (hA : 1 ≤ A) (n Q : ℕ) :
    morseWeightDerivativeBound σ (M*A^Q) n ≤
      morseWeightDerivativeBound σ M n *
        A^(Q*inversePhaseDegree (morseWeightDerivativeExpression n)) :=
  @morseWeightDerivativeBound_scaled σ M A hσ hM hA n Q

example
    {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l r η : ℝ), 1 ≤ l → r ≤ 2 → 0 < η → η ≤ 1 →
      ∀ (F : ℝ → ℝ) (δ v : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ (morseWeightDerivativeOrder n) δ →
        v ∈ modelPhaseSlopeRange F →
        ∀ z : ℝ,
          |iteratedDeriv n (modelPhaseMorseWeight (modelPhaseBufferedCutoff l r η) F v) z| ≤
            C*(η⁻¹)^(bufferedMorseDerivativeDegree n) :=
  @modelPhaseBufferedMorseWeight_uniform_derivative σ hσ n

example (a b : ℤ) (m : ℕ) :
    (modelPhaseBufferedBoundary a b m).card ≤ 2*m :=
  @modelPhaseBufferedBoundary_card_le a b m

example
    {N η : ℝ} (hN : 0 < N) (hη : 0 < η)
    {a b n : ℤ} (hn : n ∈ Finset.Icc a b)
    (hnot : n ∉ modelPhaseBufferedBoundary a b ⌈2*N*η⌉₊) :
    modelPhaseBufferedCutoff ((a : ℝ)/N) ((b : ℝ)/N) η ((n : ℝ)/N) = 1 :=
  @modelPhaseBufferedCutoff_one_off_boundary N η hN hη a b n hn hnot

example
    {N η : ℝ} (hN : 0 < N) (hη : 0 < η)
    (F : ℝ → ℝ) (T : ℝ) {a b n : ℤ} (hn : n ∉ Finset.Icc a b) :
    modelPhaseWeightedKernel (modelPhaseBufferedCutoff ((a : ℝ)/N) ((b : ℝ)/N) η)
      F T N n = 0 :=
  @modelPhaseBufferedKernel_zero_outside N η hN hη F T a b n hn

example
    {N η : ℝ} (hN : 0 < N) (hη : 0 < η) (F : ℝ → ℝ) (T : ℝ) (a b : ℤ) :
    ‖(∑ n ∈ Finset.Icc a b, (𝐞 (T*F ((n : ℝ)/N)) : ℂ))-
      ∑' n : ℤ, modelPhaseWeightedKernel
        (modelPhaseBufferedCutoff ((a : ℝ)/N) ((b : ℝ)/N) η) F T N n‖ ≤ 4*N*η+2 :=
  @norm_modelPhase_source_sub_buffered_le N η hN hη F T a b

example
    {F : ℝ → ℝ} {σ δ N η : ℝ} {P : ℕ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hN : 0 < N) (hη : 0 < η)
    {a b : ℕ} (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N) (T : ℝ) :
    Summable (fun r : ℤ => ‖modelPhaseFourierMode
      (modelPhaseBufferedCutoff ((a : ℝ)/N) ((b : ℝ)/N) η) F T N r‖) ∧
    ‖exponentialSumAt F T N a b-
      ∑' r : ℤ, modelPhaseFourierMode
        (modelPhaseBufferedCutoff ((a : ℝ)/N) ((b : ℝ)/N) η) F T N r‖ ≤ 4*N*η+2 :=
  @modelPhase_buffered_poisson F σ δ N η P hF hN hη a b ha hb T

example (H M₀ M₂ M₃ A : ℝ) :
    quadraticRemainderConstant H (M₀*A) (M₂*A) (M₃*A) =
      quadraticRemainderConstant H M₀ M₂ M₃*A :=
  @quadraticRemainderConstant_scale H M₀ M₂ M₃ A

example : 1 ≤ bufferedStationaryPhaseOrder :=
  @bufferedStationaryPhaseOrder_pos

example
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l r η : ℝ), 1 ≤ l → r ≤ 2 → 0 < η → η ≤ 1 →
      ∀ (F : ℝ → ℝ) (δ v T : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ bufferedStationaryPhaseOrder δ →
        v ∈ modelPhaseSlopeRange F → 0 < T →
        ‖modelPhaseMorseRemainder (modelPhaseBufferedCutoff l r η) F T v‖ ≤
          C*(η⁻¹)^bufferedStationaryWidthDegree/T :=
  @modelPhaseBufferedMorseRemainder_uniform σ hσ

example
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l r η : ℝ), 1 ≤ l → r ≤ 2 → 0 < η → η ≤ 1 →
      ∀ (F : ℝ → ℝ) (δ T N q : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ bufferedStationaryPhaseOrder δ →
        0 < T → 0 < N → q*N/T ∈ modelPhaseSlopeRange F →
        ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q-
          (modelPhaseBufferedCutoff l r η
            (modelPhaseInverseSlope F (q*N/T)) : ℂ)*modelPhaseStationaryMainTerm F T N q‖ ≤
          C*(η⁻¹)^bufferedStationaryWidthDegree*N/T :=
  @modelPhaseBufferedFourierMode_stationary_uniform σ hσ

example
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N η : ℝ) (a b : ℕ),
      0 < N → 0 < η → η ≤ 1 → N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
      ∀ (F : ℝ → ℝ) (δ T : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ bufferedStationaryPhaseOrder δ → 0 < T →
        Summable (fun q : ℤ => ‖modelPhaseFourierMode
          (modelPhaseBufferedCutoff ((a : ℝ)/N) ((b : ℝ)/N) η) F T N q‖) ∧
        ‖exponentialSumAt F T N a b-
          ∑' q : ℤ, modelPhaseFourierMode
            (modelPhaseBufferedCutoff ((a : ℝ)/N) ((b : ℝ)/N) η) F T N q‖ ≤ 4*N*η+2 ∧
        ∀ q : ℤ, (q : ℝ)*N/T ∈ modelPhaseSlopeRange F →
          ‖modelPhaseFourierMode
              (modelPhaseBufferedCutoff ((a : ℝ)/N) ((b : ℝ)/N) η) F T N q-
            (modelPhaseBufferedCutoff ((a : ℝ)/N) ((b : ℝ)/N) η
              (modelPhaseInverseSlope F ((q : ℝ)*N/T)) : ℂ)*
                modelPhaseStationaryMainTerm F T N q‖ ≤
            C*(η⁻¹)^bufferedStationaryWidthDegree*N/T :=
  @modelPhase_buffered_poisson_stationary σ hσ

example {η : ℝ} (hη : 0 < η) (l r u : ℝ) :
    modelPhaseBufferedCutoff l r η u =
      zetaBandCutoff (l+η) (l+2*η) (r-2*η) (r-η) u :=
  @modelPhaseBufferedCutoff_eq_band η hη l r u

example
    {η : ℝ} (hη : 0 < η) (l r : ℝ) (u : ℕ → ℝ) (L : ℕ)
    (hu : MonotoneOn u (Iic L) ∨ AntitoneOn u (Iic L)) :
    FiniteVariationBound (fun i => (modelPhaseBufferedCutoff l r η (u i) : ℂ)) L 2 :=
  @finiteVariationBound_modelPhaseBufferedCutoff_sample η hη l r u L hu

example
    {σ δ T N η : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η)
    (l r a : ℝ) (L : ℕ)
    (hv : ∀ i : ℕ, i ≤ L → (a+i)*N/T ∈ modelPhaseSlopeRange F) :
    FiniteVariationBound
      (fun i => (modelPhaseBufferedCutoff l r η
        (modelPhaseInverseSlope F ((a+i)*N/T)) : ℂ)) L 2 :=
  @finiteVariationBound_modelPhaseBufferedCutoff_inverse σ δ T N η F hσ hδ hF hT hN hη l r a L hv

example
    {σ δ T N η : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ modelPhaseAmplitudeTolerance σ)
    (hF : IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η)
    (l r a : ℝ) (L : ℕ)
    (hv : ∀ i : ℕ, i ≤ L → (a+i)*N/T ∈ modelPhaseSlopeRange F) :
    FiniteVariationBound
      (fun i => (modelPhaseBufferedCutoff l r η
        (modelPhaseInverseSlope F ((a+i)*N/T)) : ℂ)*
          (modelPhasePhysicalAmplitude F T N (a+i) : ℂ)) L
      (4*((N/Real.sqrt T)*(Real.sqrt (modelPhaseCurvatureLower σ))⁻¹)) :=
  @finiteVariationBound_modelPhaseBufferedAmplitude σ δ T N η F hσ hδ hF hT hN hη l r a L hv

example
    (F : ℝ → ℝ) (l r η T N : ℝ) (a L : ℕ) :
    modelPhaseBufferedStationaryBlock F l r η T N a L =
      ∑ i ∈ Finset.range (L+1),
        (modelPhaseBufferedCutoff l r η
          (modelPhaseInverseSlope F (((a : ℝ)+i)*N/T)) : ℂ)*
            modelPhaseStationaryMainTerm F T N ((a : ℝ)+i) :=
  @modelPhaseBufferedStationaryBlock_eq_range F l r η T N a L

example
    {χ F : ℝ → ℝ} {σ δ A w T N η : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ modelPhaseAmplitudeTolerance σ)
    (hF : IsApproximateModelPhaseFunction F σ 2 δ)
    (hA : 0 < A) (hw : 0 < w) (hT : 0 < T) (hN : 0 < N) (hη : 0 < η)
    (l r : ℝ) (a L : ℕ)
    (hslope : ∀ i : ℕ, i ≤ L → ((a : ℝ)+i)*N/T ∈ modelPhaseSlopeRange F)
    (hv : ∀ i : ℕ, i ≤ L → 0 < ((a : ℝ)+i)*N/T)
    (hχ : ∀ i : ℕ, i ≤ L → χ (((a : ℝ)+i)*N/T) = 1) :
    ‖modelPhaseBufferedStationaryBlock F l r η T N a L‖ ≤
      8*((N/Real.sqrt T)*(Real.sqrt (modelPhaseCurvatureLower σ))⁻¹) *
        exponentialSumAtPrefixMax (canonicalLegendrePhase χ F σ A w)
          (modelPhaseDualParameter σ A T) (modelPhaseDualScale A T N) a L :=
  @norm_modelPhaseBufferedStationaryBlock_le_prefixMax χ F σ δ A w T N η hσ hδ hF hA hw hT hN hη l r a L hslope hv hχ

example
    {α : ℝ≥0} {β σ l r : ℝ}
    (hβ : IsExponentSumBoundNonAsymptotic α β) (hσ : 0 < σ)
    (hl : (2 : ℝ)^(-σ) < l) (hlr : l ≤ r) (hr : r < 1) (hratio : r < 2*l) :
    ∃ A : ℝ, 0 < A ∧ A < l ∧ r < 2*A ∧
      ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
        (∀ v ∈ Icc l r, χ v = 1) ∧
        ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧ ∃ P : ℕ, 2 ≤ P ∧ ∃ C : ℝ, 1 ≤ C ∧
          ∀ (T N : ℝ) (F : ℝ → ℝ) (a L : ℕ) (p q η : ℝ),
            0 < η →
            0 < T → 0 < N →
            IsApproximateModelPhaseFunction F σ P δ →
            C ≤ modelPhaseDualParameter σ A T →
            (modelPhaseDualParameter σ A T)^((α : ℝ)-δ) ≤ modelPhaseDualScale A T N →
            modelPhaseDualScale A T N ≤ (modelPhaseDualParameter σ A T)^((α : ℝ)+δ) →
            (∀ i : ℕ, i ≤ L → ((a : ℝ)+i)*N/T ∈ Icc l r) →
            ‖modelPhaseBufferedStationaryBlock F p q η T N a L‖ ≤
              8*((N/Real.sqrt T)*(Real.sqrt (modelPhaseCurvatureLower σ))⁻¹) *
                C*(modelPhaseDualParameter σ A T)^(β+ε) :=
  @bufferedStationaryMain_bound_of_exponentSumBound α β σ l r hβ hσ hl hlr hr hratio

example
    {f k : ℝ → ℂ} {a b M B : ℝ} {J : Set ℝ}
    (hf : IntervalC1Bound f a b M) (hab : a ≤ b)
    (hJ : IsOpen J) (hsub : Icc a b ⊆ J)
    (hk : ∀ x ∈ J, ContinuousAt k x)
    (hprimitive : ∀ x ∈ Icc a b, ‖∫ y in a..x, k y‖ ≤ B) :
    ‖∫ y in a..b, f y*k y‖ ≤ 2*B*M :=
  @IntervalC1Bound.integral_mul_of_primitive_bound f k a b M B J hf hab hJ hsub hk hprimitive

example
    {φ : ℝ → ℝ} {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam)
    (hφ : ∀ x ∈ Icc a b, ContDiffAt ℝ 2 φ x)
    (hmono : AntitoneOn (deriv φ) (Icc a b))
    (hgap : (∀ x ∈ Icc a b, lam ≤ deriv φ x) ∨
      (∀ x ∈ Icc a b, deriv φ x ≤ -lam)) :
    ‖∫ x in a..b, (𝐞 (φ x) : ℂ)‖ ≤ 1/(lam*Real.pi) :=
  @norm_fourierCharIntegral_le_of_slope_gap φ a b lam hab hlam hφ hmono hgap

example
    {f : ℝ → ℂ} {φ : ℝ → ℝ} {a b M lam : ℝ} {J : Set ℝ}
    (hf : IntervalC1Bound f a b M) (hab : a ≤ b) (hlam : 0 < lam)
    (hJ : IsOpen J) (hsub : Icc a b ⊆ J)
    (hφ : ∀ x ∈ J, ContDiffAt ℝ 2 φ x)
    (hmono : AntitoneOn (deriv φ) J)
    (hgap : (∀ x ∈ J, lam ≤ deriv φ x) ∨
      (∀ x ∈ J, deriv φ x ≤ -lam)) :
    ‖∫ x in a..b, f x*(𝐞 (φ x) : ℂ)‖ ≤ 2*M/(lam*Real.pi) :=
  @IntervalC1Bound.fourierChar_of_slope_gap f φ a b M lam J hf hab hlam hJ hsub hφ hmono hgap

example {l r η : ℝ} (hη : 0 < η) :
    Function.support (modelPhaseBufferedCutoff l r η) ⊆ Ioo (l+η) (r-η) :=
  @modelPhaseBufferedCutoff_support_open l r η hη

example {l r η : ℝ}
    (hη : 0 < η) (h : r-η ≤ l+η) :
    modelPhaseBufferedCutoff l r η = fun _ => 0 :=
  @modelPhaseBufferedCutoff_eq_zero_of_overlap l r η hη h

example
    {l r η a b : ℝ} (hη : 0 < η) (hab : a ≤ b) :
    IntervalC1Bound (fun u => (modelPhaseBufferedCutoff l r η u : ℂ)) a b 2 :=
  @intervalC1Bound_modelPhaseBufferedCutoff l r η a b hη hab

example
    {F : ℝ → ℝ} {σ δ T q l r η lam : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hη : 0 < η) (hl : 1 ≤ l) (hr : r ≤ 2) (hlam : 0 < lam)
    (hgap : (∀ u ∈ Ioo (1 : ℝ) 2, lam ≤ T*deriv F u-q) ∨
      (∀ u ∈ Ioo (1 : ℝ) 2, T*deriv F u-q ≤ -lam)) :
    ‖modelPhaseNormalizedMode (modelPhaseBufferedCutoff l r η) F T q‖ ≤
      4/(lam*Real.pi) :=
  @norm_modelPhaseBufferedNormalizedMode_nonstationary F σ δ T q l r η lam hσ hδ hF hT hη hl hr hlam hgap

example
    {F : ℝ → ℝ} {σ δ T N q l r η lam : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η)
    (hl : 1 ≤ l) (hr : r ≤ 2) (hlam : 0 < lam)
    (hgap : (∀ u ∈ Ioo (1 : ℝ) 2, lam ≤ T*deriv F u-q*N) ∨
      (∀ u ∈ Ioo (1 : ℝ) 2, T*deriv F u-q*N ≤ -lam)) :
    ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q‖ ≤
      4*N/(lam*Real.pi) :=
  @norm_modelPhaseBufferedFourierMode_nonstationary F σ δ T N q l r η lam hσ hδ hF hT hN hη hl hr hlam hgap

example
    {F : ℝ → ℝ} {σ δ : ℝ} {P : ℕ} (hσ : 0 < σ)
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) :
    (2 : ℝ)^(-σ)-δ ≤ deriv F u ∧ deriv F u ≤ 1+δ :=
  @approximateModelPhase_firstDeriv_bounds F σ δ P hσ hF u hu

example
    {F : ℝ → ℝ} {σ δ T N q l r η lam : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η)
    (hl : 1 ≤ l) (hr : r ≤ 2) (hlam : 0 < lam)
    (hgap : q*N ≤ T*((2 : ℝ)^(-σ)-δ)-lam ∨ T*(1+δ)+lam ≤ q*N) :
    ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q‖ ≤
      4*N/(lam*Real.pi) :=
  @norm_modelPhaseBufferedFourierMode_of_envelope_gap F σ δ T N q l r η lam hσ hδ hF hT hN hη hl hr hlam hgap

example
    {F : ℝ → ℝ} {σ δ T N q l r η d : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η)
    (hl : 1 ≤ l) (hr : r ≤ 2) (hd : 0 < d)
    (hgap : q ≤ (T/N)*((2 : ℝ)^(-σ)-δ)-d ∨ (T/N)*(1+δ)+d ≤ q) :
    ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q‖ ≤
      4/(d*Real.pi) :=
  @norm_modelPhaseBufferedFourierMode_of_frequency_gap F σ δ T N q l r η d hσ hδ hF hT hN hη hl hr hd hgap

example (Q : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l r η u : ℝ), 0 < η →
      ∀ j ≤ Q, |iteratedDeriv j (modelPhaseBufferedCutoff l r η) u| ≤ C*(η⁻¹)^j :=
  @modelPhaseBufferedCutoff_uniform_ordered_jets Q

example (w : ℕ → ℕ) (e : InversePhaseExpression)
    {B A : ℝ} {x : ℕ → ℝ} (hB : 0 ≤ B) (hA : 1 ≤ A)
    (hx : ∀ j ≤ inversePhaseOrder e, |x j| ≤ B*A^(w j)) :
    |inversePhaseEval e x| ≤
      inversePhaseMagnitude e B*A^(inversePhaseWeightedDegree w e) :=
  @inversePhaseEval_abs_le_weighted w e B A x hB hA hx

example (j : ℕ) :
    inversePhaseWeightedDegree morseWeightWidthAtomDegree (morseWeightAtomDerivative j) ≤
      morseWeightWidthAtomDegree j+1 :=
  @morseWeightAtomDerivative_widthDegree_le j

example (e : InversePhaseExpression) :
    inversePhaseWeightedDegree morseWeightWidthAtomDegree (morseWeightDifferentiate e) ≤
      inversePhaseWeightedDegree morseWeightWidthAtomDegree e+1 :=
  @morseWeightDifferentiate_widthDegree_le e

example (n : ℕ) :
    inversePhaseWeightedDegree morseWeightWidthAtomDegree (morseWeightDerivativeExpression n) ≤ n :=
  @morseWeightDerivativeExpression_widthDegree_le n

example : modelPhaseBufferedCutoff 1 2 (1/8) (9/8) = 0 := by
  apply modelPhaseBufferedCutoff_zero_left <;> norm_num

example : modelPhaseBufferedCutoff 1 2 (1/8) (15/8) = 0 := by
  apply modelPhaseBufferedCutoff_zero_right <;> norm_num

example : modelPhaseBufferedCutoff 1 2 (1/8) (3/2) = 1 := by
  apply modelPhaseBufferedCutoff_one <;> norm_num

example : modelPhaseBufferedCutoff 1 2 1 = fun _ => 0 := by
  apply modelPhaseBufferedCutoff_eq_zero_of_overlap <;> norm_num

example : modelPhaseBufferedCutoff 2 1 (1/8) = fun _ => 0 := by
  apply modelPhaseBufferedCutoff_eq_zero_of_overlap <;> norm_num

example (j : ℕ) (u : ℝ) :
    iteratedDeriv j (modelPhaseBufferedCutoff 1 1 (1/8)) u = 0 := by
  rw [modelPhaseBufferedCutoff_eq_zero_of_overlap (by norm_num) (by norm_num)]
  simp

example (F : ℝ → ℝ) (T N q : ℝ) :
    modelPhaseFourierMode (modelPhaseBufferedCutoff 1 1 (1/8)) F T N q = 0 := by
  rw [modelPhaseBufferedCutoff_eq_zero_of_overlap (by norm_num) (by norm_num)]
  simp [modelPhaseFourierMode]

example (a b : ℤ) : (modelPhaseBufferedBoundary a b 0).card = 0 :=
  Nat.eq_zero_of_le_zero (by simpa using modelPhaseBufferedBoundary_card_le a b 0)

example : (modelPhaseBufferedBoundary 1 1 1).card ≤ 2 := by
  simpa using modelPhaseBufferedBoundary_card_le 1 1 1

example {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) :
    (1 : ℝ)/2 ≤ deriv (referenceModelPrimitive 1) u ∧
      deriv (referenceModelPrimitive 1) u ≤ 1 := by
  have h := approximateModelPhase_firstDeriv_bounds (by norm_num : (0 : ℝ) < 1)
    (referenceModelPrimitive_approximate 1 1) hu
  norm_num [Real.rpow_neg_one] at h
  exact h

example {η : ℝ} (hη : 0 < η) :
    ‖modelPhaseFourierMode (modelPhaseBufferedCutoff 1 2 η)
      (referenceModelPrimitive 1) 1 1 3‖ ≤ 4/Real.pi := by
  have h := norm_modelPhaseBufferedFourierMode_of_frequency_gap
    (σ := 1) (δ := 0) (T := 1) (N := 1) (q := 3) (l := 1) (r := 2) (d := 1)
    (by norm_num) (le_min (modelPhaseCurvatureLower_pos (by norm_num)).le zero_le_one)
    (referenceModelPrimitive_approximate 1 1)
    (by norm_num) (by norm_num) hη (by norm_num) (by norm_num) (by norm_num)
    (Or.inr (by norm_num))
  simpa only [one_mul] using h

example {η : ℝ} (hη : 0 < η) (l r u : ℝ) :
    FiniteVariationBound (fun _ => (modelPhaseBufferedCutoff l r η u : ℂ)) 0 2 := by
  exact finiteVariationBound_modelPhaseBufferedCutoff_sample hη l r (fun _ => u) 0
    (Or.inl (fun _ _ _ _ _ => le_rfl))

example {η : ℝ} (hη : 0 < η) :
    Summable (fun q : ℤ => ‖modelPhaseFourierMode
      (modelPhaseBufferedCutoff 1 1 η) (referenceModelPrimitive 1) 0 1 q‖) ∧
      ‖exponentialSumAt (referenceModelPrimitive 1) 0 1 1 1-
        ∑' q : ℤ, modelPhaseFourierMode
          (modelPhaseBufferedCutoff 1 1 η) (referenceModelPrimitive 1) 0 1 q‖ ≤ 4*η+2 := by
  simpa only [Nat.cast_one,div_one,mul_one] using
    modelPhase_buffered_poisson (referenceModelPrimitive_approximate 1 1)
      (N := 1) (a := 1) (b := 1) (by norm_num) hη (by norm_num) (by norm_num) 0

example : bufferedStationaryWidthDegree = 3 := rfl

example (n : ℕ) : bufferedMorseDerivativeDegree n = n := rfl

example : inversePhaseWeightedDegree morseWeightWidthAtomDegree
    (morseWeightDerivativeExpression 3) = 3 := by decide

end BufferedFamilyRegression

section QuantitativeBufferedTailRegression

open Set Expdb Filter MeasureTheory
open scoped ContDiff Topology FourierTransform BigOperators

example
    {F : ℝ → ℝ} {a b K : ℝ} (hK : 1 ≤ K)
    (hF : ∀ x ∈ Icc a b, ContDiffAt ℝ 2 F x)
    (hF₁ : ∀ x ∈ Icc a b, |deriv F x| ≤ K)
    (hF₂ : ∀ x ∈ Icc a b, |iteratedDeriv 2 F x| ≤ K)
    (T : ℝ) :
    IntervalC2Bound (fun x => (𝐞 (T*F x) : ℂ)) a b
      ((2*Real.pi)^2*K^2+2*Real.pi*K+1) (1+|T|) :=
  @intervalC2Bound_fourierChar_of_derivative_bounds F a b K hK hF hF₁ hF₂ T

example :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (l r η a b : ℝ), 0 < η →
      IntervalC2Bound (fun x => (modelPhaseBufferedCutoff l r η x : ℂ))
        a b M η⁻¹ :=
  @modelPhaseBufferedCutoff_uniform_c2

example (l r η T N x : ℝ) (F : ℝ → ℝ) :
    ‖modelPhaseWeightedKernel (modelPhaseBufferedCutoff l r η) F T N x‖ ≤ 1 :=
  @norm_modelPhaseBufferedKernel_le_one l r η T N x F

example
    {σ : ℝ} (hσ : 0 ≤ σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l r η : ℝ), 1 ≤ l → r ≤ 2 → 0 < η → η ≤ 1 →
      ∀ (F : ℝ → ℝ) (δ T : ℝ), δ ≤ 1 →
        IsApproximateModelPhaseFunction F σ 1 δ →
        ∀ u : ℝ,
          ‖iteratedDeriv 2 (modelPhaseWeightedKernel
            (modelPhaseBufferedCutoff l r η) F T 1) u‖ ≤ C*(η⁻¹)^2*(1+|T|)^2 :=
  @modelPhaseBufferedKernel_uniform_second_derivative σ hσ

example (χ F : ℝ → ℝ) (T ξ : ℝ) :
    modelPhaseNormalizedMode χ F T ξ =
      𝓕 (modelPhaseWeightedKernel χ F T 1) ξ :=
  @modelPhaseNormalizedMode_eq_fourier χ F T ξ

example
    {σ : ℝ} (hσ : 0 ≤ σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l r η : ℝ), 1 ≤ l → r ≤ 2 → 0 < η → η ≤ 1 →
      ∀ (F : ℝ → ℝ) (δ T N q : ℝ), δ ≤ 1 →
        IsApproximateModelPhaseFunction F σ 1 δ → 0 < N →
        (1+|q*N|)^2 *
          ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q‖ ≤
          C*N*(η⁻¹)^2*(1+|T|)^2 :=
  @modelPhaseBufferedFourierMode_uniform_decay σ hσ

example
    {σ : ℝ} (hσ : 0 ≤ σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l r η : ℝ), 1 ≤ l → r ≤ 2 → 0 < η → η ≤ 1 →
      ∀ (F : ℝ → ℝ) (δ T N q : ℝ), δ ≤ 1 →
        IsApproximateModelPhaseFunction F σ 1 δ → 0 < N → q ≠ 0 →
        ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q‖ ≤
          C*(η⁻¹)^2*(1+|T|)^2/(N*q^2) :=
  @modelPhaseBufferedFourierMode_inverse_square_bound σ hσ

example {R : ℕ} (hR : 0 < R) :
    (∑' n : ℕ, if R < n then 1/(n : ℝ)^2 else 0) ≤ 1/(R : ℝ) :=
  @tsum_nat_inverse_square_tail_le R hR

example {R : ℕ} (hR : 0 < R) :
    (∑' q : ℤ, if R < q.natAbs then 1/(q : ℝ)^2 else 0) ≤ 2/(R : ℝ) :=
  @tsum_int_inverse_square_tail_le R hR

example
    {f : ℤ → ℂ} {K : ℝ} (hK : 0 ≤ K)
    (hf : Summable (fun q => ‖f q‖))
    (hb : ∀ q : ℤ, q ≠ 0 → ‖f q‖ ≤ K/(q : ℝ)^2)
    {R : ℕ} (hR : 0 < R) :
    ‖∑' q : ℤ, if R < q.natAbs then f q else 0‖ ≤ 2*K/(R : ℝ) :=
  @norm_integer_far_tail_le_of_inverse_square f K hK hf hb R hR

example {f : ℤ → ℂ}
    (hf : Summable f) (R : ℕ) :
    (∑' q : ℤ, f q) =
      (∑ q ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), f q) +
        ∑' q : ℤ, if R < q.natAbs then f q else 0 :=
  @tsum_int_eq_sum_Icc_add_far f hf R

example
    {σ : ℝ} (hσ : 0 ≤ σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l r η : ℝ), 1 ≤ l → r ≤ 2 → 0 < η → η ≤ 1 →
      ∀ (F : ℝ → ℝ) (δ T N : ℝ), δ ≤ 1 →
        IsApproximateModelPhaseFunction F σ 1 δ → 0 < N →
        ∀ R : ℕ, 0 < R →
          ‖modelPhaseBufferedFarTail l r η F T N R‖ ≤
            C*(η⁻¹)^2*(1+|T|)^2/(N*(R : ℝ)) :=
  @modelPhaseBufferedFarTail_uniform σ hσ

example
    {σ : ℝ} (hσ : 0 ≤ σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N η : ℝ) (a b : ℕ),
      0 < N → 0 < η → η ≤ 1 → N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
      ∀ (F : ℝ → ℝ) (δ T : ℝ), δ ≤ 1 →
        IsApproximateModelPhaseFunction F σ 1 δ →
        ∀ R : ℕ, 0 < R →
          ‖exponentialSumAt F T N a b-
            ∑ q ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
              modelPhaseFourierMode
                (modelPhaseBufferedCutoff ((a : ℝ)/N) ((b : ℝ)/N) η) F T N q‖ ≤
            4*N*η+2+C*(η⁻¹)^2*(1+|T|)^2/(N*(R : ℝ)) :=
  @modelPhase_buffered_poisson_truncated σ hσ

example
    {σ : ℝ} (hσ : 0 ≤ σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N η : ℝ) (a b : ℕ),
      0 < N → 0 < η → η ≤ 1 → N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
      ∀ (F : ℝ → ℝ) (δ T ε : ℝ), δ ≤ 1 →
        IsApproximateModelPhaseFunction F σ 1 δ → 0 < ε →
        let R : ℕ := ⌈C*(η⁻¹)^2*(1+|T|)^2/(N*ε)⌉₊+1
        0 < R ∧
          ‖exponentialSumAt F T N a b-
            ∑ q ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
              modelPhaseFourierMode
                (modelPhaseBufferedCutoff ((a : ℝ)/N) ((b : ℝ)/N) η) F T N q‖ ≤
            4*N*η+2+ε :=
  @modelPhase_buffered_poisson_truncated_precision σ hσ

example
    {F : ℝ → ℝ} {σ δ T N l r η : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η) (hl : 1 ≤ l) (hr : r ≤ 2)
    (Q : ℤ) (hQ : (T/N)*(1+δ) ≤ (Q : ℝ)) (L : ℕ) :
    (∑ n ∈ Finset.range L,
      ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N
        ((Q : ℝ)+((n+1 : ℕ) : ℝ))‖) ≤ (4/Real.pi)*(harmonic L : ℝ) :=
  @sum_norm_bufferedModes_right_le_harmonic F σ δ T N l r η hσ hδ hF hT hN hη hl hr Q hQ L

example
    {F : ℝ → ℝ} {σ δ T N l r η : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η) (hl : 1 ≤ l) (hr : r ≤ 2)
    (Q : ℤ) (hQ : (Q : ℝ) ≤ (T/N)*((2 : ℝ)^(-σ)-δ)) (L : ℕ) :
    (∑ n ∈ Finset.range L,
      ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N
        ((Q : ℝ)-((n+1 : ℕ) : ℝ))‖) ≤ (4/Real.pi)*(harmonic L : ℝ) :=
  @sum_norm_bufferedModes_left_le_harmonic F σ δ T N l r η hσ hδ hF hT hN hη hl hr Q hQ L

example
    {F : ℝ → ℝ} {σ δ T N l r η : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η) (hl : 1 ≤ l) (hr : r ≤ 2)
    (Lminus Lplus : ℕ) :
    ‖(∑ n ∈ Finset.range Lminus,
      modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N
        ((⌊(T/N)*((2 : ℝ)^(-σ)-δ)⌋ : ℤ)-((n+1 : ℕ) : ℝ)))+
      (∑ n ∈ Finset.range Lplus,
      modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N
        ((⌈(T/N)*(1+δ)⌉ : ℤ)+((n+1 : ℕ) : ℝ)))‖ ≤
      (4/Real.pi)*(2+Real.log (Lminus : ℝ)+Real.log (Lplus : ℝ)) :=
  @norm_bufferedModes_exterior_blocks_le_log F σ δ T N l r η hσ hδ hF hT hN hη hl hr Lminus Lplus

example (f : ℤ → ℂ)
    {a b c d : ℤ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    (∑ q ∈ Finset.Icc a d, f q) =
      (∑ q ∈ Finset.Ico a b, f q)+(∑ q ∈ Finset.Icc b c, f q)+
        ∑ q ∈ Finset.Ioc c d, f q :=
  @sum_int_interval_three_parts f a b c d hab hbc hcd

example (f : ℤ → ℂ) {a b : ℤ} (hab : a ≤ b) :
    (∑ q ∈ Finset.Ico a b, f q) =
      ∑ n ∈ Finset.range (b-a).toNat, f (b-((n+1 : ℕ) : ℤ)) :=
  @sum_int_Ico_eq_reverse_range f a b hab

example (f : ℤ → ℂ) {a b : ℤ} (hab : a ≤ b) :
    (∑ q ∈ Finset.Ioc a b, f q) =
      ∑ n ∈ Finset.range (b-a).toNat, f (a+((n+1 : ℕ) : ℤ)) :=
  @sum_int_Ioc_eq_forward_range f a b hab

example
    {σ δ T N : ℝ} (hσ : 0 ≤ σ) (hδ : 0 ≤ δ) (hT : 0 ≤ T) (hN : 0 < N) :
    modelPhaseCoreLower σ δ T N ≤ modelPhaseCoreUpper δ T N :=
  @modelPhaseCoreLower_le_upper σ δ T N hσ hδ hT hN

example
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N η : ℝ) (a b : ℕ),
      0 < N → 0 < η → η ≤ 1 → N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
      ∀ (F : ℝ → ℝ) (δ T : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ 1 δ → 0 < T →
        ∀ R : ℕ, 0 < R →
          -(R : ℤ) ≤ modelPhaseCoreLower σ δ T N →
          modelPhaseCoreUpper δ T N ≤ (R : ℤ) →
          ‖exponentialSumAt F T N a b-
            ∑ q ∈ Finset.Icc (modelPhaseCoreLower σ δ T N) (modelPhaseCoreUpper δ T N),
              modelPhaseFourierMode
                (modelPhaseBufferedCutoff ((a : ℝ)/N) ((b : ℝ)/N) η) F T N q‖ ≤
            4*N*η+2+C*(η⁻¹)^2*(1+|T|)^2/(N*(R : ℝ))+
              (4/Real.pi)*(2+
                Real.log (((modelPhaseCoreLower σ δ T N+(R : ℤ)).toNat : ℕ) : ℝ)+
                Real.log ((((R : ℤ)-modelPhaseCoreUpper δ T N).toNat : ℕ) : ℝ)) :=
  @modelPhase_buffered_poisson_core σ hσ

example
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N η : ℝ) (a b : ℕ),
      0 < N → 0 < η → η ≤ 1 → N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
      ∀ (F : ℝ → ℝ) (δ T ε : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ 1 δ → 0 < T → 0 < ε →
        let A := modelPhaseCoreLower σ δ T N
        let B := modelPhaseCoreUpper δ T N
        let R : ℕ := ⌈C*(η⁻¹)^2*(1+|T|)^2/(N*ε)⌉₊+A.natAbs+B.natAbs+1
        0 < R ∧ -(R : ℤ) ≤ A ∧ B ≤ (R : ℤ) ∧
          ‖exponentialSumAt F T N a b-
            ∑ q ∈ Finset.Icc A B,
              modelPhaseFourierMode
                (modelPhaseBufferedCutoff ((a : ℝ)/N) ((b : ℝ)/N) η) F T N q‖ ≤
            4*N*η+2+ε+(4/Real.pi)*(2+
              Real.log ((A+(R : ℤ)).toNat : ℝ)+Real.log (((R : ℤ)-B).toNat : ℝ)) :=
  @modelPhase_buffered_poisson_core_precision σ hσ

example
    {σ δ T N : ℝ} (hσ : 0 ≤ σ) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (hT : 0 ≤ T) (hN : 0 < N) :
    ((Finset.Icc (modelPhaseCoreLower σ δ T N) (modelPhaseCoreUpper δ T N)).card : ℝ) ≤
      3*(T/N)+3 :=
  @modelPhaseCore_card_le σ δ T N hσ hδ hδ₁ hT hN

example {F : ℝ → ℝ} {σ δ T N : ℝ} {q : ℤ} :
    q ∈ modelPhaseCoreStationarySet F σ δ T N ↔
      q ∈ Finset.Icc (modelPhaseCoreLower σ δ T N) (modelPhaseCoreUpper δ T N) ∧
        (q : ℝ)*N/T ∈ modelPhaseSlopeRange F :=
  @modelPhaseCoreStationarySet_mem F σ δ T N q

example
    {F : ℝ → ℝ} {σ δ T N : ℝ} (hσ : 0 ≤ σ) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (hT : 0 ≤ T) (hN : 0 < N) :
    ((modelPhaseCoreStationarySet F σ δ T N).card : ℝ) ≤ 3*(T/N)+3 :=
  @modelPhaseCoreStationarySet_card_le F σ δ T N hσ hδ hδ₁ hT hN

example
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l r η : ℝ), 1 ≤ l → r ≤ 2 → 0 < η → η ≤ 1 →
      ∀ (F : ℝ → ℝ) (δ T N : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ bufferedStationaryPhaseOrder δ →
        0 < T → 0 < N →
        ‖∑ q ∈ modelPhaseCoreStationarySet F σ δ T N,
          (modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q-
            (modelPhaseBufferedCutoff l r η (modelPhaseInverseSlope F ((q : ℝ)*N/T)) : ℂ)*
              modelPhaseStationaryMainTerm F T N q)‖ ≤
          C*(η⁻¹)^3*(1+N/T) :=
  @modelPhaseBufferedCoreStationary_error σ hσ

example (l r η : ℝ) (F : ℝ → ℝ)
    (σ δ T N : ℝ) :
    (∑ q ∈ Finset.Icc (modelPhaseCoreLower σ δ T N) (modelPhaseCoreUpper δ T N),
      modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q)-
        modelPhaseBufferedCoreExpansion l r η F σ δ T N =
      ∑ q ∈ modelPhaseCoreStationarySet F σ δ T N,
        (modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q-
          (modelPhaseBufferedCutoff l r η (modelPhaseInverseSlope F ((q : ℝ)*N/T)) : ℂ)*
            modelPhaseStationaryMainTerm F T N q) :=
  @modelPhaseCore_sub_bufferedExpansion l r η F σ δ T N

example
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ D : ℝ, 1 ≤ D ∧
      ∀ (N η : ℝ) (a b : ℕ),
        0 < N → 0 < η → η ≤ 1 → N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
        ∀ (F : ℝ → ℝ) (δ T ε : ℝ),
          δ ≤ min (modelPhaseCurvatureLower σ) 1 →
          IsApproximateModelPhaseFunction F σ bufferedStationaryPhaseOrder δ →
          0 < T → 0 < ε →
          let A := modelPhaseCoreLower σ δ T N
          let B := modelPhaseCoreUpper δ T N
          let R : ℕ := ⌈C*(η⁻¹)^2*(1+|T|)^2/(N*ε)⌉₊+A.natAbs+B.natAbs+1
          ‖exponentialSumAt F T N a b-
            modelPhaseBufferedCoreExpansion ((a : ℝ)/N) ((b : ℝ)/N) η F σ δ T N‖ ≤
            4*N*η+2+ε+
              (4/Real.pi)*(2+Real.log ((A+(R : ℤ)).toNat : ℝ)+
                Real.log (((R : ℤ)-B).toNat : ℝ))+
              D*(η⁻¹)^3*(1+N/T) :=
  @modelPhase_buffered_source_core_expansion σ hσ

example : (∑' n : ℕ, if 1 < n then 1/(n : ℝ)^2 else 0) ≤ 1 := by
  simpa using tsum_nat_inverse_square_tail_le (R := 1) (by decide)

example : (∑' q : ℤ, if 1 < q.natAbs then 1/(q : ℝ)^2 else 0) ≤ 2 := by
  simpa using tsum_int_inverse_square_tail_le (R := 1) (by decide)

example {f : ℤ → ℂ} (hf : Summable f) :
    (∑' q : ℤ, f q) = f 0+(∑' q : ℤ, if 0 < q.natAbs then f q else 0) := by
  simpa using tsum_int_eq_sum_Icc_add_far hf 0

example (f : ℤ → ℂ) (a : ℤ) :
    (∑ q ∈ Finset.Ico a a, f q) = 0 := by
  simp

example (f : ℤ → ℂ) (a : ℤ) :
    (∑ q ∈ Finset.Ioc a a, f q) = 0 := by
  simp

example (f : ℤ → ℂ) (a : ℤ) :
    (∑ q ∈ Finset.Icc a a, f q) = f a := by simp

example (f : ℤ → ℂ) :
    (∑ q ∈ Finset.Ico (-2 : ℤ) 0, f q) =
      ∑ n ∈ Finset.range 2, f (-((n+1 : ℕ) : ℤ)) := by
  simpa using sum_int_Ico_eq_reverse_range f (a := -2) (b := 0) (by norm_num)

example (f : ℤ → ℂ) :
    (∑ q ∈ Finset.Ioc (0 : ℤ) 2, f q) =
      ∑ n ∈ Finset.range 2, f ((n+1 : ℕ) : ℤ) := by
  simpa using sum_int_Ioc_eq_forward_range f (a := 0) (b := 2) (by norm_num)

example (l r η x : ℝ) (F : ℝ → ℝ) :
    ‖modelPhaseWeightedKernel (modelPhaseBufferedCutoff l r η) F 0 0 x‖ ≤ 1 :=
  norm_modelPhaseBufferedKernel_le_one l r η 0 0 x F

example {η : ℝ} (hη : 0 < η) (l : ℝ) (F : ℝ → ℝ) (T N : ℝ) (R : ℕ) :
    modelPhaseBufferedFarTail l l η F T N R = 0 := by
  have hzero := modelPhaseBufferedCutoff_eq_zero_of_overlap (l := l) (r := l) hη
    (by linarith : l-η ≤ l+η)
  simp [modelPhaseBufferedFarTail,hzero,modelPhaseFourierMode]

example : modelPhaseCoreLower 1 0 1 1 = 0 ∧ modelPhaseCoreUpper 0 1 1 = 1 := by
  norm_num [modelPhaseCoreLower,modelPhaseCoreUpper,Real.rpow_neg_one]

example :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ R : ℕ, 0 < R →
      ‖exponentialSumAt (referenceModelPrimitive 1) 0 1 1 1-
        ∑ q ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
          modelPhaseFourierMode (modelPhaseBufferedCutoff 1 1 1)
            (referenceModelPrimitive 1) 0 1 q‖ ≤ 6+C/(R : ℝ) := by
  obtain ⟨C,hC,htrunc⟩ := modelPhase_buffered_poisson_truncated (σ := 1) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro R hR
  simpa only [Nat.cast_one,div_one,inv_one,one_pow,mul_one,abs_zero,
    add_zero,one_mul,show (4 : ℝ)+2 = 6 by norm_num] using
    htrunc 1 1 1 1 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (referenceModelPrimitive 1) 0 0 (by norm_num)
      (referenceModelPrimitive_approximate 1 1) R hR

end QuantitativeBufferedTailRegression

section CurvatureEndpointCoreRegression

open Set Expdb MeasureTheory Filter
open scoped ContDiff FourierTransform Topology BigOperators

example {f : ℝ → ℝ} {a b m : ℝ}
    (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
    (hd : ∀ x ∈ Icc a b, deriv f x ≤ -m)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
    m*(y-x) ≤ f x-f y :=
  slope_drop_of_deriv_le (f := f) (a := a) (b := b) (m := m) hf hd (x := x) (y := y) hx hy hxy

example {f : ℝ → ℝ} {a b lam : ℝ}
    (hab : a ≤ b) (hlam : 0 ≤ lam) (hf : ContinuousOn f (Icc a b))
    (hlo : f b ≤ lam) (hhi : -lam ≤ f a) :
    ∃ c d : ℝ, a ≤ c ∧ c ≤ d ∧ d ≤ b ∧
      f c ≤ lam ∧ -lam ≤ f d ∧
      (c = a ∨ f c = lam) ∧ (d = b ∨ f d = -lam) :=
  exists_slope_transition_partition (f := f) (a := a) (b := b) (lam := lam) hab hlam hf hlo hhi

example {f : ℝ → ℝ} {a b c d m lam : ℝ}
    (hm : 0 < m)
    (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
    (hd : ∀ x ∈ Icc a b, deriv f x ≤ -m)
    (hc : c ∈ Icc a b) (he : d ∈ Icc a b) (hcd : c ≤ d)
    (hcl : f c ≤ lam) (hdl : -lam ≤ f d) :
    d-c ≤ 2*lam/m :=
  slope_transition_width_le (f := f) (a := a) (b := b) (c := c) (d := d) (m := m) (lam := lam) hm hf hd hc he hcd hcl hdl

example
    {φ : ℝ → ℝ} {a b m lam : ℝ}
    (hab : a ≤ b) (hm : 0 < m) (hlam : 0 < lam)
    (hφ : ∀ x ∈ Icc a b, ContDiffAt ℝ 2 φ x)
    (hcurv : ∀ x ∈ Icc a b, deriv (deriv φ) x ≤ -m) :
    ‖∫ x in a..b, (𝐞 (φ x) : ℂ)‖ ≤ 2/(lam*Real.pi)+2*lam/m :=
  norm_fourierCharIntegral_le_of_curvature_threshold (φ := φ) (a := a) (b := b) (m := m) (lam := lam) hab hm hlam hφ hcurv

example
    {φ : ℝ → ℝ} {a b m : ℝ}
    (hab : a ≤ b) (hm : 0 < m)
    (hφ : ∀ x ∈ Icc a b, ContDiffAt ℝ 2 φ x)
    (hcurv : ∀ x ∈ Icc a b, deriv (deriv φ) x ≤ -m) :
    ‖∫ x in a..b, (𝐞 (φ x) : ℂ)‖ ≤ (2/Real.pi+2)/Real.sqrt m :=
  norm_fourierCharIntegral_le_of_negative_curvature (φ := φ) (a := a) (b := b) (m := m) hab hm hφ hcurv

example
    {f : ℝ → ℂ} {φ : ℝ → ℝ} {a b M m : ℝ} {J : Set ℝ}
    (hf : IntervalC1Bound f a b M) (hab : a ≤ b) (hm : 0 < m)
    (hJ : IsOpen J) (hsub : Icc a b ⊆ J)
    (hφ : ∀ x ∈ J, ContDiffAt ℝ 2 φ x)
    (hcurv : ∀ x ∈ J, deriv (deriv φ) x ≤ -m) :
    ‖∫ x in a..b, f x*(𝐞 (φ x) : ℂ)‖ ≤
      2*M*(2/Real.pi+2)/Real.sqrt m :=
  IntervalC1Bound.fourierChar_of_negative_curvature (f := f) (φ := φ) (a := a) (b := b) (M := M) (m := m) (J := J) hf hab hm hJ hsub hφ hcurv

example
    {F : ℝ → ℝ} {σ δ T q l r η : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hη : 0 < η) (hl : 1 ≤ l) (hr : r ≤ 2) :
    ‖modelPhaseNormalizedMode (modelPhaseBufferedCutoff l r η) F T q‖ ≤
      4*(2/Real.pi+2)/Real.sqrt (T*modelPhaseCurvatureLower σ) :=
  norm_modelPhaseBufferedNormalizedMode_curvature (F := F) (σ := σ) (δ := δ) (T := T) (q := q) (l := l) (r := r) (η := η) hσ hδ hF hT hη hl hr

example
    {F : ℝ → ℝ} {σ δ T N q l r η : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η) (hl : 1 ≤ l) (hr : r ≤ 2) :
    ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q‖ ≤
      4*(2/Real.pi+2)*N/Real.sqrt (T*modelPhaseCurvatureLower σ) :=
  norm_modelPhaseBufferedFourierMode_curvature (F := F) (σ := σ) (δ := δ) (T := T) (N := N) (q := q) (l := l) (r := r) (η := η) hσ hδ hF hT hN hη hl hr

example {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l r η : ℝ),
      1 ≤ l → r ≤ 2 → 0 < η →
      ∀ (F : ℝ → ℝ) (δ T N q : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ 1 δ →
        0 < T → 0 < N →
        ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q‖ ≤
          C*N/Real.sqrt T :=
  modelPhaseBufferedFourierMode_uniform_curvature (σ := σ) hσ

example {F : ℝ → ℝ} {u : ℝ}
    (hu : u ∈ Ioo (1 : ℝ) 2) :
    modelPhaseClosedSlope F u = deriv F u :=
  modelPhaseClosedSlope_eq_deriv (F := F) (u := u) hu

example {F : ℝ → ℝ} {u : ℝ}
    (hu : u ∈ Ioo (1 : ℝ) 2) :
    modelPhaseClosedSlope F =ᶠ[𝓝 u] deriv F :=
  modelPhaseClosedSlope_eventuallyEq_deriv (F := F) (u := u) hu

example {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ) :
    ContinuousOn (modelPhaseClosedSlope F) (Icc (1 : ℝ) 2) :=
  modelPhaseClosedSlope_continuousOn (σ := σ) (δ := δ) (P := P) (F := F) hF

example {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {u v : ℝ} (hu : u ∈ Icc (1 : ℝ) 2) (hv : v ∈ Icc (1 : ℝ) 2)
    (huv : u ≤ v) :
    modelPhaseCurvatureLower σ*(v-u) ≤ modelPhaseClosedSlope F u-modelPhaseClosedSlope F v :=
  modelPhaseClosedSlope_drop (σ := σ) (δ := δ) (F := F) hσ hδ hF (u := u) (v := v) hu hv huv

example {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) :
    StrictAntiOn (modelPhaseClosedSlope F) (Icc (1 : ℝ) 2) :=
  modelPhaseClosedSlope_strictAntiOn (σ := σ) (δ := δ) (F := F) hσ hδ hF

example {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) :
    modelPhaseSlopeRange F = Ioo (modelPhaseClosedSlope F 2) (modelPhaseClosedSlope F 1) :=
  modelPhaseSlopeRange_eq_endpoint_Ioo (σ := σ) (δ := δ) (F := F) hσ hδ hF

example {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    {u : ℝ} (hu : u ∈ phaseInterval) :
    |modelPhaseClosedSlope F u-u^(-σ)| ≤ δ :=
  modelPhaseClosedSlope_model_error (σ := σ) (δ := δ) (P := P) (F := F) hF (u := u) hu

example {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) :
    modelPhaseClosedSlope F 2 ≤ deriv F u ∧ deriv F u ≤ modelPhaseClosedSlope F 1 :=
  modelPhaseClosedSlope_deriv_bounds (σ := σ) (δ := δ) (F := F) hσ hδ hF (u := u) hu

example
    {F : ℝ → ℝ} {σ δ T N q l r η d : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η)
    (hl : 1 ≤ l) (hr : r ≤ 2) (hd : 0 < d)
    (hgap : q ≤ (T/N)*modelPhaseClosedSlope F 2-d ∨
      (T/N)*modelPhaseClosedSlope F 1+d ≤ q) :
    ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q‖ ≤
      4/(d*Real.pi) :=
  norm_modelPhaseBufferedFourierMode_of_endpoint_gap (F := F) (σ := σ) (δ := δ) (T := T) (N := N) (q := q) (l := l) (r := r) (η := η) (d := d) hσ hδ hF hT hN hη hl hr hd hgap

example
    {F : ℝ → ℝ} {σ δ T N l r η : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η) (hl : 1 ≤ l) (hr : r ≤ 2)
    (Q : ℤ) (hQ : (T/N)*modelPhaseClosedSlope F 1 ≤ (Q : ℝ)) (L : ℕ) :
    (∑ n ∈ Finset.range L,
      ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N
        ((Q : ℝ)+((n+1 : ℕ) : ℝ))‖) ≤ (4/Real.pi)*(harmonic L : ℝ) :=
  sum_norm_bufferedModes_endpoint_right_le_harmonic (F := F) (σ := σ) (δ := δ) (T := T) (N := N) (l := l) (r := r) (η := η) hσ hδ hF hT hN hη hl hr Q hQ L

example
    {F : ℝ → ℝ} {σ δ T N l r η : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η) (hl : 1 ≤ l) (hr : r ≤ 2)
    (Q : ℤ) (hQ : (Q : ℝ) ≤ (T/N)*modelPhaseClosedSlope F 2) (L : ℕ) :
    (∑ n ∈ Finset.range L,
      ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N
        ((Q : ℝ)-((n+1 : ℕ) : ℝ))‖) ≤ (4/Real.pi)*(harmonic L : ℝ) :=
  sum_norm_bufferedModes_endpoint_left_le_harmonic (F := F) (σ := σ) (δ := δ) (T := T) (N := N) (l := l) (r := r) (η := η) hσ hδ hF hT hN hη hl hr Q hQ L

example
    {F : ℝ → ℝ} {σ δ T N l r η : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η) (hl : 1 ≤ l) (hr : r ≤ 2)
    (Lminus Lplus : ℕ) :
    ‖(∑ n ∈ Finset.range Lminus,
      modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N
        ((⌊(T/N)*modelPhaseClosedSlope F 2⌋ : ℤ)-((n+1 : ℕ) : ℝ)))+
      (∑ n ∈ Finset.range Lplus,
      modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N
        ((⌈(T/N)*modelPhaseClosedSlope F 1⌉ : ℤ)+((n+1 : ℕ) : ℝ)))‖ ≤
      (4/Real.pi)*(2+Real.log (Lminus : ℝ)+Real.log (Lplus : ℝ)) :=
  norm_bufferedModes_endpoint_blocks_le_log (F := F) (σ := σ) (δ := δ) (T := T) (N := N) (l := l) (r := r) (η := η) hσ hδ hF hT hN hη hl hr Lminus Lplus

example {σ δ T N q : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) (hT : 0 < T) (hN : 0 < N) :
    q*N/T ∈ modelPhaseSlopeRange F ↔
      (T/N)*modelPhaseClosedSlope F 2 < q ∧ q < (T/N)*modelPhaseClosedSlope F 1 :=
  modelPhaseFrequency_mem_slopeRange_iff (σ := σ) (δ := δ) (T := T) (N := N) (q := q) (F := F) hσ hδ hF hT hN

example {σ δ T N : ℝ} {F : ℝ → ℝ} {q : ℤ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) (hT : 0 < T) (hN : 0 < N) :
    (q : ℝ)*N/T ∉ modelPhaseSlopeRange F ↔
      q ≤ modelPhaseEndpointLower F T N ∨ modelPhaseEndpointUpper F T N ≤ q :=
  modelPhaseFrequency_not_stationary_iff (σ := σ) (δ := δ) (T := T) (N := N) (F := F) (q := q) hσ hδ hF hT hN

example {σ δ T N : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) (hT : 0 < T) (hN : 0 < N) :
    modelPhaseEndpointLower F T N < modelPhaseEndpointUpper F T N :=
  modelPhaseEndpointLower_lt_upper (σ := σ) (δ := δ) (T := T) (N := N) (F := F) hσ hδ hF hT hN

example {σ δ T N : ℝ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) (hT : 0 ≤ T) (hN : 0 < N) :
    modelPhaseCoreLower σ δ T N ≤ modelPhaseEndpointLower F T N ∧
      modelPhaseEndpointUpper F T N ≤ modelPhaseCoreUpper δ T N :=
  modelPhaseEndpoints_inside_core (σ := σ) (δ := δ) (T := T) (N := N) (F := F) hF hT hN

example {σ δ T N : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) (hT : 0 < T) (hN : 0 < N) :
    (Finset.Icc (modelPhaseCoreLower σ δ T N) (modelPhaseCoreUpper δ T N)) \
      modelPhaseCoreStationarySet F σ δ T N =
        Finset.Icc (modelPhaseCoreLower σ δ T N) (modelPhaseEndpointLower F T N) ∪
        Finset.Icc (modelPhaseEndpointUpper F T N) (modelPhaseCoreUpper δ T N) :=
  modelPhaseCore_nonstationary_eq_endpoint_union (σ := σ) (δ := δ) (T := T) (N := N) (F := F) hσ hδ hF hT hN

example {σ δ T N : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) (hT : 0 < T) (hN : 0 < N)
    (f : ℤ → ℂ) :
    (∑ q ∈ (Finset.Icc (modelPhaseCoreLower σ δ T N) (modelPhaseCoreUpper δ T N)) \
      modelPhaseCoreStationarySet F σ δ T N, f q) =
        (∑ q ∈ Finset.Icc (modelPhaseCoreLower σ δ T N) (modelPhaseEndpointLower F T N), f q)+
        ∑ q ∈ Finset.Icc (modelPhaseEndpointUpper F T N) (modelPhaseCoreUpper δ T N), f q :=
  modelPhaseCore_nonstationary_sum (σ := σ) (δ := δ) (T := T) (N := N) (F := F) hσ hδ hF hT hN f

example {σ δ T N : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) (hT : 0 < T) (hN : 0 < N) :
    modelPhaseCoreStationarySet F σ δ T N =
      Finset.Ioo (modelPhaseEndpointLower F T N) (modelPhaseEndpointUpper F T N) :=
  modelPhaseCoreStationarySet_eq_endpoint_Ioo (σ := σ) (δ := δ) (T := T) (N := N) (F := F) hσ hδ hF hT hN

example {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l r η : ℝ), 1 ≤ l → r ≤ 2 → 0 < η →
      ∀ (F : ℝ → ℝ) (δ T N : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ 1 δ → 0 < T → 0 < N →
        let A := modelPhaseCoreLower σ δ T N
        let B := modelPhaseCoreUpper δ T N
        let L := modelPhaseEndpointLower F T N
        let U := modelPhaseEndpointUpper F T N
        ‖∑ q ∈ (Finset.Icc A B) \ modelPhaseCoreStationarySet F σ δ T N,
          modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q‖ ≤
            2*C*N/Real.sqrt T+
              (4/Real.pi)*(2+Real.log ((L-A).toNat : ℝ)+Real.log ((B-U).toNat : ℝ)) :=
  modelPhaseBufferedCoreNonstationary_error (σ := σ) hσ

example {σ δ T N : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) (hT : 0 < T) (hN : 0 < N) :
    (((modelPhaseEndpointLower F T N-modelPhaseCoreLower σ δ T N).toNat : ℕ) : ℝ) ≤
        3*(T/N)+3 ∧
      (((modelPhaseCoreUpper δ T N-modelPhaseEndpointUpper F T N).toNat : ℕ) : ℝ) ≤
        3*(T/N)+3 :=
  modelPhaseEndpointBlockLengths_le (σ := σ) (δ := δ) (T := T) (N := N) (F := F) hσ hδ hF hT hN

example {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l r η : ℝ), 1 ≤ l → r ≤ 2 → 0 < η →
      ∀ (F : ℝ → ℝ) (δ T N : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ 1 δ → 0 < T → 0 < N →
        ‖∑ q ∈ (Finset.Icc (modelPhaseCoreLower σ δ T N) (modelPhaseCoreUpper δ T N)) \
          modelPhaseCoreStationarySet F σ δ T N,
          modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q‖ ≤
            2*C*N/Real.sqrt T+(8/Real.pi)*(1+Real.log (3*(T/N)+3)) :=
  modelPhaseBufferedCoreNonstationary_uniform (σ := σ) hσ

example
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ D : ℝ, 1 ≤ D ∧ ∃ E : ℝ, 0 < E ∧
      ∀ (N η : ℝ) (a b : ℕ),
        0 < N → 0 < η → η ≤ 1 → N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
        ∀ (F : ℝ → ℝ) (δ T ε : ℝ),
          δ ≤ min (modelPhaseCurvatureLower σ) 1 →
          IsApproximateModelPhaseFunction F σ bufferedStationaryPhaseOrder δ →
          0 < T → 0 < ε →
          let A := modelPhaseCoreLower σ δ T N
          let B := modelPhaseCoreUpper δ T N
          let R : ℕ := ⌈C*(η⁻¹)^2*(1+|T|)^2/(N*ε)⌉₊+A.natAbs+B.natAbs+1
          ‖exponentialSumAt F T N a b-
            ∑ q ∈ Finset.Ioo (modelPhaseEndpointLower F T N) (modelPhaseEndpointUpper F T N),
              (modelPhaseBufferedCutoff ((a : ℝ)/N) ((b : ℝ)/N) η
                (modelPhaseInverseSlope F ((q : ℝ)*N/T)) : ℂ)*
                  modelPhaseStationaryMainTerm F T N q‖ ≤
            4*N*η+2+ε+
              (4/Real.pi)*(2+Real.log ((A+(R : ℤ)).toNat : ℝ)+
                Real.log (((R : ℤ)-B).toNat : ℝ))+
              D*(η⁻¹)^3*(1+N/T)+
              2*E*N/Real.sqrt T+(8/Real.pi)*(1+Real.log (3*(T/N)+3)) :=
  modelPhase_buffered_source_stationary_expansion (σ := σ) hσ

example {a b : ℝ} (hab : a ≤ b) :
    ‖∫ x in a..b, (𝐞 (-(x^2)) : ℂ)‖ ≤ (2/Real.pi+2)/Real.sqrt 2 := by
  apply norm_fourierCharIntegral_le_of_negative_curvature hab (by norm_num)
    (fun x _ => by fun_prop)
  intro x hx
  have hd : deriv (fun y : ℝ => -(y^2)) = fun y => (-2)*y := by
    funext y
    convert ((hasDerivAt_id y).pow 2).neg.deriv using 1
    dsimp
    ring
  rw [hd]
  have hh := ((hasDerivAt_id x).const_mul (-2)).deriv
  simp only [mul_one] at hh
  exact hh.le

example (a : ℝ) (φ : ℝ → ℝ) :
    ‖∫ x in a..a, (𝐞 (φ x) : ℂ)‖ = 0 := by simp

example :
    ∃ c d : ℝ, (-1 : ℝ) ≤ c ∧ c ≤ d ∧ d ≤ 1 ∧
      -c ≤ 0 ∧ 0 ≤ -d ∧ (c = -1 ∨ -c = 0) ∧ (d = 1 ∨ -d = 0) := by
  simpa using exists_slope_transition_partition (f := fun x : ℝ => -x)
    (a := -1) (b := 1) (lam := 0) (by norm_num) (by norm_num)
    (by fun_prop) (by norm_num) (by norm_num)

example (F : ℝ → ℝ) (T N q : ℝ) :
    modelPhaseFourierMode (modelPhaseBufferedCutoff 1 2 2) F T N q = 0 := by
  have hz := modelPhaseBufferedCutoff_eq_zero_of_overlap
    (l := 1) (r := 2) (η := 2) (by norm_num) (by norm_num)
  simp [hz,modelPhaseFourierMode]

example {σ δ T N : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) (hT : 0 < T) (hN : 0 < N) :
    ((modelPhaseEndpointLower F T N : ℤ) : ℝ)*N/T ∉ modelPhaseSlopeRange F := by
  exact (modelPhaseFrequency_not_stationary_iff hσ hδ hF hT hN).mpr (Or.inl le_rfl)

example {σ δ T N : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) (hT : 0 < T) (hN : 0 < N) :
    ((modelPhaseEndpointUpper F T N : ℤ) : ℝ)*N/T ∉ modelPhaseSlopeRange F := by
  exact (modelPhaseFrequency_not_stationary_iff hσ hδ hF hT hN).mpr (Or.inr le_rfl)

example {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) :
    modelPhaseClosedSlope F 1 ∉ modelPhaseSlopeRange F ∧
      modelPhaseClosedSlope F 2 ∉ modelPhaseSlopeRange F := by
  rw [modelPhaseSlopeRange_eq_endpoint_Ioo hσ hδ hF]
  simp

example {σ δ T N : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) (hT : 0 < T) (hN : 0 < N)
    (hgap : modelPhaseEndpointUpper F T N = modelPhaseEndpointLower F T N+1) :
    modelPhaseCoreStationarySet F σ δ T N = ∅ := by
  rw [modelPhaseCoreStationarySet_eq_endpoint_Ioo hσ hδ hF hT hN]
  ext q
  simp only [Finset.mem_Ioo,Finset.notMem_empty,iff_false]
  omega

example {σ δ T N : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) (hT : 0 < T) (hN : 0 < N)
    (hgap : modelPhaseEndpointUpper F T N = modelPhaseEndpointLower F T N+2) :
    modelPhaseCoreStationarySet F σ δ T N = {modelPhaseEndpointLower F T N+1} := by
  rw [modelPhaseCoreStationarySet_eq_endpoint_Ioo hσ hδ hF hT hN]
  ext q
  simp only [Finset.mem_Ioo,Finset.mem_singleton]
  omega

example : modelPhaseClosedSlope (referenceModelPrimitive 1) 2 = (1 : ℝ)/2 := by
  have h := modelPhaseClosedSlope_model_error (referenceModelPrimitive_approximate 1 1)
    (show (2 : ℝ) ∈ phaseInterval by norm_num [phaseInterval])
  norm_num only [Real.rpow_neg_one,inv_eq_one_div] at h
  have he := abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  linarith

end CurvatureEndpointCoreRegression

section InteriorStationaryRegression

open Set Expdb MeasureTheory
open scoped ContDiff FourierTransform

example
    {f : ℝ → ℝ} {l r a x M : ℝ}
    (ha : a ∈ Icc l r) (hx : x ∈ Icc l r) (k : ℕ)
    (hb : ∀ u ∈ Icc l r, |iteratedDeriv k f u| ≤ M) :
    |segmentTaylorAverage f a k x| ≤ M := by
  exact @abs_segmentTaylorAverage_le_closed f l r a x M ha hx k hb

example {W : ℝ → ℝ} {H M z : ℝ}
    (hH : 0 ≤ H) (hb : ∀ x ∈ Icc (-H) H, |iteratedDeriv 2 W x| ≤ M)
    (hz : z ∈ Icc (-H) H) :
    |quadraticTaylorCoefficient W z| ≤ M := by
  exact @abs_quadraticTaylorCoefficient_le_local W H M z hH hb hz

example {W : ℝ → ℝ} {H M z : ℝ}
    (hW : ContDiff ℝ ∞ W) (hH : 0 ≤ H)
    (hb : ∀ x ∈ Icc (-H) H, |iteratedDeriv 3 W x| ≤ M)
    (hz : z ∈ Icc (-H) H) :
    |deriv (quadraticTaylorCoefficient W) z| ≤ M := by
  exact @abs_deriv_quadraticTaylorCoefficient_le_local W H M z hW hH hb hz

example
    {V : ℝ → ℝ} {T H M L : ℝ}
    (hV : ContDiff ℝ ∞ V) (hT : 0 < T) (hH : 0 < H)
    (hb : ∀ z ∈ Icc (-H) H, |V z| ≤ M)
    (hd : ∀ z ∈ Icc (-H) H, |deriv V z| ≤ L) :
    ‖∫ z in (-H)..H, ((z^2*V z : ℝ) : ℂ)*betaQuadraticKernel T z‖ ≤
      (2*H*M+2*H*(M+H*L))/(2*Real.pi*T) := by
  exact @norm_integral_sq_mul_betaQuadraticKernel_le_local V T H M L hV hT hH hb hd

example
    {W : ℝ → ℝ} {T H M₀ M₂ M₃ : ℝ}
    (hW : ContDiff ℝ ∞ W) (hT : 0 < T) (hH : 0 < H)
    (h₀ : |W 0| ≤ M₀)
    (h₂ : ∀ z ∈ Icc (-H) H, |iteratedDeriv 2 W z| ≤ M₂)
    (h₃ : ∀ z ∈ Icc (-H) H, |iteratedDeriv 3 W z| ≤ M₃) :
    ‖(∫ z in (-H)..H, (W z : ℂ)*betaQuadraticKernel T z)-
      (W 0 : ℂ)*((𝐞 (-(1 : ℝ)/8) : ℂ)/(Real.sqrt T : ℂ))‖ ≤
        quadraticRemainderConstant H M₀ M₂ M₃/T := by
  exact @norm_quadratic_window_remainder_le_local W T H M₀ M₂ M₃ hW hT hH h₀ h₂ h₃

example
    {H M₀ M₂ M₃ : ℝ} (hH : 0 < H) (hH₁ : H ≤ 1)
    (h₂ : 0 ≤ M₂) (h₃ : 0 ≤ M₃) :
    quadraticRemainderConstant H M₀ M₂ M₃ ≤
      (4*M₀/Real.pi+(4*M₂+2*M₃)/(2*Real.pi))/H := by
  exact @quadraticRemainderConstant_le_inverse_window H M₀ M₂ M₃ hH hH₁ h₂ h₃

example
    {F : ℝ → ℝ} {σ δ v d H z : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hd : 0 < d)
    (hl : 1 < modelPhaseInverseSlope F v-d)
    (hr : modelPhaseInverseSlope F v+d < 2)
    (hH : H < Real.sqrt (modelPhaseCurvatureLower σ)*d)
    (hz : z ∈ Icc (-H) H) :
    z ∈ modelPhaseMorseRange F v ∧
      |modelPhaseMorseInverse F v z-modelPhaseInverseSlope F v| < d := by
  exact @modelPhaseMorseWindow_mem_and_inverse F σ δ v d H z hσ hδ hF hv hd hl hr hH hz

example
    {F : ℝ → ℝ} {σ δ v z l r η : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v)
    (hη : 0 < η)
    (hl : l+2*η < modelPhaseMorseInverse F v z)
    (hr : modelPhaseMorseInverse F v z < r-2*η) (n : ℕ) :
    iteratedDeriv n (modelPhaseMorseWeight (modelPhaseBufferedCutoff l r η) F v) z =
      iteratedDeriv (n+1) (modelPhaseMorseInverse F v) z := by
  exact @iteratedDeriv_bufferedMorseWeight_of_flat F σ δ v z l r η hσ hδ hF hv hz hη hl hr n

example
    {F : ℝ → ℝ} {σ δ v l r η d H z : ℝ} {P : ℕ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hv : v ∈ modelPhaseSlopeRange F)
    (hη : 0 < η) (hl : 1 ≤ l) (hr : r ≤ 2) (hd : 0 < d)
    (hleft : l+2*η+d ≤ modelPhaseInverseSlope F v)
    (hright : modelPhaseInverseSlope F v+d ≤ r-2*η)
    (hH : H < Real.sqrt (modelPhaseCurvatureLower σ)*d)
    (hz : z ∈ Icc (-H) H) (n : ℕ)
    (hP : morseInverseDerivativeOrder (n+1) ≤ P) :
    |iteratedDeriv n (modelPhaseMorseWeight (modelPhaseBufferedCutoff l r η) F v) z| ≤
      morseInverseDerivativeBound σ (n+1) := by
  exact @bufferedMorseWeight_local_jet_bound F σ δ v l r η d H z P hσ hδ hF hv hη hl hr hd hleft hright hH hz n hP

example : 1 ≤ bufferedLocalStationaryOrder := by
  exact @bufferedLocalStationaryOrder_pos

example
    {F : ℝ → ℝ} {σ δ v l r η d H T : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ bufferedLocalStationaryOrder δ)
    (hv : v ∈ modelPhaseSlopeRange F)
    (hη : 0 < η) (hl : 1 ≤ l) (hr : r ≤ 2) (hd : 0 < d)
    (hleft : l+2*η+d ≤ modelPhaseInverseSlope F v)
    (hright : modelPhaseInverseSlope F v+d ≤ r-2*η)
    (hH : 0 < H) (hsmall : H < Real.sqrt (modelPhaseCurvatureLower σ)*d)
    (hT : 0 < T) :
    ‖(∫ z in (-H)..H,
      (modelPhaseMorseWeight (modelPhaseBufferedCutoff l r η) F v z : ℂ)*
        betaQuadraticKernel T z)-
      (modelPhaseStationaryAmplitude F v : ℂ)*
        ((𝐞 (-(1 : ℝ)/8) : ℂ)/(Real.sqrt T : ℂ))‖ ≤
      quadraticRemainderConstant H (morseInverseDerivativeBound σ 1)
        (morseInverseDerivativeBound σ 3) (morseInverseDerivativeBound σ 4)/T := by
  exact @bufferedMorseWeight_local_window_remainder F σ δ v l r η d H T hσ hδ hF hv hη hl hr hd hleft hright hH hsmall hT

example
    {F : ℝ → ℝ} {σ δ v l r η d H T : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ bufferedLocalStationaryOrder δ)
    (hv : v ∈ modelPhaseSlopeRange F)
    (hη : 0 < η) (hl : 1 ≤ l) (hr : r ≤ 2) (hd : 0 < d)
    (hleft : l+2*η+d ≤ modelPhaseInverseSlope F v)
    (hright : modelPhaseInverseSlope F v+d ≤ r-2*η)
    (hH : 0 < H) (hH₁ : H ≤ 1)
    (hsmall : H < Real.sqrt (modelPhaseCurvatureLower σ)*d)
    (hT : 0 < T) :
    ‖(∫ z in (-H)..H,
      (modelPhaseMorseWeight (modelPhaseBufferedCutoff l r η) F v z : ℂ)*
        betaQuadraticKernel T z)-
      (modelPhaseStationaryAmplitude F v : ℂ)*
        ((𝐞 (-(1 : ℝ)/8) : ℂ)/(Real.sqrt T : ℂ))‖ ≤
      (4*morseInverseDerivativeBound σ 1/Real.pi+
        (4*morseInverseDerivativeBound σ 3+2*morseInverseDerivativeBound σ 4)/(2*Real.pi))/(T*H) := by
  exact @bufferedMorseWeight_local_window_remainder_inverse F σ δ v l r η d H T hσ hδ hF hv hη hl hr hd hleft hright hH hH₁ hsmall hT

example
    {F : ℝ → ℝ} {σ δ v H : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hH : 0 ≤ H)
    (hs : Icc (-H) H ⊆ modelPhaseMorseRange F v)
    {g : ℝ → ℂ} (hg : ContinuousOn g (Ioo (1 : ℝ) 2)) :
    (∫ u in modelPhaseMorseInverse F v (-H)..modelPhaseMorseInverse F v H, g u) =
      ∫ z in (-H)..H, ((deriv (modelPhaseMorseInverse F v) z : ℝ) : ℂ)*
        g (modelPhaseMorseInverse F v z) := by
  exact @integral_inverseMorse_window F σ δ v H hσ hδ hF hv hH hs g hg

example
    {χ F : ℝ → ℝ} {σ δ v H : ℝ}
    (hχ : Continuous χ)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hH : 0 ≤ H)
    (hs : Icc (-H) H ⊆ modelPhaseMorseRange F v) (T : ℝ) :
    (∫ u in modelPhaseMorseInverse F v (-H)..modelPhaseMorseInverse F v H,
      (χ u : ℂ)*(𝐞 (T*F u-(T*v)*u) : ℂ)) =
      (𝐞 (-T*modelPhaseLegendreDual F v) : ℂ)*
        ∫ z in (-H)..H, (modelPhaseMorseWeight χ F v z : ℂ)*betaQuadraticKernel T z := by
  exact @modelPhaseMorse_window_integral χ F σ δ v H hχ hσ hδ hF hv hH hs T

example
    {f : ℝ → ℂ} {φ : ℝ → ℝ} {a b M lam : ℝ} {J : Set ℝ}
    (hf : IntervalC1Bound f a b M) (hab : a ≤ b) (hlam : 0 < lam)
    (hJ : IsOpen J) (hsub : Icc a b ⊆ J)
    (hφ : ∀ x ∈ J, ContDiffAt ℝ 2 φ x)
    (hmono : AntitoneOn (deriv φ) (Icc a b))
    (hgap : (∀ x ∈ Icc a b, lam ≤ deriv φ x) ∨
      (∀ x ∈ Icc a b, deriv φ x ≤ -lam)) :
    ‖∫ x in a..b, f x*(𝐞 (φ x) : ℂ)‖ ≤ 2*M/(lam*Real.pi) := by
  exact @IntervalC1Bound.fourierChar_of_closed_slope_gap f φ a b M lam J hf hab hlam hJ hsub hφ hmono hgap

example
    {F : ℝ → ℝ} {σ δ T q l r η a b lam : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hη : 0 < η) (hab : a ≤ b)
    (ha : 1 < a) (hb : b < 2) (hlam : 0 < lam)
    (hgap : (∀ u ∈ Icc a b, lam ≤ T*deriv F u-q) ∨
      (∀ u ∈ Icc a b, T*deriv F u-q ≤ -lam)) :
    ‖∫ u in a..b, (modelPhaseBufferedCutoff l r η u : ℂ)*
      (𝐞 (T*F u-q*u) : ℂ)‖ ≤ 4/(lam*Real.pi) := by
  exact @norm_buffered_subinterval_nonstationary F σ δ T q l r η a b lam hσ hδ hF hT hη hab ha hb hlam hgap

example
    {F : ℝ → ℝ} {σ δ v H : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hH : 0 ≤ H)
    (hleft : -H ∈ modelPhaseMorseRange F v) (hright : H ∈ modelPhaseMorseRange F v) :
    H*modelPhaseCurvatureLower σ/Real.sqrt (σ+1) ≤
        deriv F (modelPhaseMorseInverse F v (-H))-v ∧
      H*modelPhaseCurvatureLower σ/Real.sqrt (σ+1) ≤
        v-deriv F (modelPhaseMorseInverse F v H) := by
  exact @modelPhaseMorseInverse_window_slope_gaps F σ δ v H hσ hδ hF hv hH hleft hright

example
    {F : ℝ → ℝ} {σ δ T v l r η H : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F)
    (hT : 0 < T) (hη : 0 < η) (hl : 1 ≤ l) (hr : r ≤ 2) (hH : 0 < H)
    (hleft : -H ∈ modelPhaseMorseRange F v) (hright : H ∈ modelPhaseMorseRange F v)
    (hcutleft : l+η ≤ modelPhaseMorseInverse F v (-H))
    (hcutright : modelPhaseMorseInverse F v H ≤ r-η) :
    ‖modelPhaseNormalizedMode (modelPhaseBufferedCutoff l r η) F T (T*v)-
      (∫ u in modelPhaseMorseInverse F v (-H)..modelPhaseMorseInverse F v H,
        (modelPhaseBufferedCutoff l r η u : ℂ)*(𝐞 (T*F u-(T*v)*u) : ℂ))‖ ≤
      8*Real.sqrt (σ+1)/(T*H*modelPhaseCurvatureLower σ*Real.pi) := by
  exact @norm_bufferedNormalizedMode_sub_window_le F σ δ T v l r η H hσ hδ hF hv hT hη hl hr hH hleft hright hcutleft hcutright

example
    {F : ℝ → ℝ} {σ δ v l r η d H T : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ bufferedLocalStationaryOrder δ)
    (hv : v ∈ modelPhaseSlopeRange F)
    (hη : 0 < η) (hl : 1 ≤ l) (hr : r ≤ 2) (hd : 0 < d)
    (hleft : l+2*η+d ≤ modelPhaseInverseSlope F v)
    (hright : modelPhaseInverseSlope F v+d ≤ r-2*η)
    (hH : 0 < H) (hH₁ : H ≤ 1)
    (hsmall : H < Real.sqrt (modelPhaseCurvatureLower σ)*d) (hT : 0 < T) :
    ‖modelPhaseNormalizedMode (modelPhaseBufferedCutoff l r η) F T (T*v)-
      (𝐞 (-T*modelPhaseLegendreDual F v) : ℂ)*
        ((modelPhaseStationaryAmplitude F v : ℂ)*
          ((𝐞 (-(1 : ℝ)/8) : ℂ)/(Real.sqrt T : ℂ)))‖ ≤
      bufferedInteriorStationaryConstant σ/(T*H) := by
  exact @bufferedNormalizedMode_interior_window_remainder F σ δ v l r η d H T hσ hδ hF hv hη hl hr hd hleft hright hH hH₁ hsmall hT

example
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l r η d : ℝ), 1 ≤ l → r ≤ 2 → 0 < η → 0 < d →
      ∀ (F : ℝ → ℝ) (δ v T : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ bufferedLocalStationaryOrder δ →
        v ∈ modelPhaseSlopeRange F → 0 < T →
        l+2*η+d ≤ modelPhaseInverseSlope F v →
        modelPhaseInverseSlope F v+d ≤ r-2*η →
        ‖modelPhaseMorseRemainder (modelPhaseBufferedCutoff l r η) F T v‖ ≤ C/(T*d) := by
  exact @modelPhaseBufferedMorseRemainder_interior_uniform σ hσ

example
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l r η d : ℝ), 1 ≤ l → r ≤ 2 → 0 < η → 0 < d →
      ∀ (F : ℝ → ℝ) (δ T N q : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ bufferedLocalStationaryOrder δ →
        0 < T → 0 < N → q*N/T ∈ modelPhaseSlopeRange F →
        l+2*η+d ≤ modelPhaseInverseSlope F (q*N/T) →
        modelPhaseInverseSlope F (q*N/T)+d ≤ r-2*η →
        ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q-
          modelPhaseStationaryMainTerm F T N q‖ ≤ C*N/(T*d) := by
  exact @modelPhaseBufferedFourierMode_interior_uniform σ hσ

example
    {F : ℝ → ℝ} {σ δ v a b w : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F)
    (ha : a ∈ Ioo (1 : ℝ) 2) (hb : b ∈ Ioo (1 : ℝ) 2) (hw : 0 < w)
    (hleft : v+w ≤ deriv F a) (hright : deriv F b+w ≤ v) :
    a+w/(σ+1) ≤ modelPhaseInverseSlope F v ∧
      modelPhaseInverseSlope F v+w/(σ+1) ≤ b := by
  exact @modelPhaseInverseSlope_interior_of_gap F σ δ v a b w hσ hδ hF hv ha hb hw hleft hright

example
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l r η : ℝ), 1 ≤ l → r ≤ 2 → 0 < η → l+4*η < r →
      ∀ (F : ℝ → ℝ) (δ T N q lam : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ bufferedLocalStationaryOrder δ →
        0 < T → 0 < N → 0 < lam →
        (T/N)*deriv F (r-2*η)+lam ≤ q →
        q+lam ≤ (T/N)*deriv F (l+2*η) →
        ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q-
          modelPhaseStationaryMainTerm F T N q‖ ≤ C/lam := by
  exact @modelPhaseBufferedFourierMode_interior_frequency_uniform σ hσ

example (L : ℕ) :
    (∑ n ∈ Finset.range L, (1/((n+1 : ℕ) : ℝ)+1/((L-n : ℕ) : ℝ))) =
      2*(harmonic L : ℝ) := by
  exact @sum_range_two_edge_reciprocals L

example
    {f : ℕ → ℂ} {C : ℝ} {L : ℕ} (hC : 0 ≤ C)
    (hb : ∀ n < L, ‖f n‖ ≤ C/min ((n+1 : ℕ) : ℝ) ((L-n : ℕ) : ℝ)) :
    ‖∑ n ∈ Finset.range L, f n‖ ≤ 2*C*(harmonic L : ℝ) := by
  exact @norm_sum_range_le_two_edge_harmonic f C L hC hb

example
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l r η : ℝ), 1 ≤ l → r ≤ 2 → 0 < η → l+4*η < r →
      ∀ (F : ℝ → ℝ) (δ T N Q : ℝ) (L : ℕ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ bufferedLocalStationaryOrder δ →
        0 < T → 0 < N →
        (T/N)*deriv F (r-2*η) ≤ Q →
        Q+(L : ℝ)+1 ≤ (T/N)*deriv F (l+2*η) →
        ‖∑ n ∈ Finset.range L,
          (modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N (Q+((n+1 : ℕ) : ℝ))-
            modelPhaseStationaryMainTerm F T N (Q+((n+1 : ℕ) : ℝ)))‖ ≤
          C*(1+Real.log (L : ℝ)) := by
  exact @modelPhaseBufferedInteriorRange_error σ hσ

example
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l r η : ℝ), 1 ≤ l → r ≤ 2 → 0 < η → l+4*η < r →
      ∀ (F : ℝ → ℝ) (δ T N : ℝ) (A B : ℤ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ bufferedLocalStationaryOrder δ →
        0 < T → 0 < N →
        (T/N)*deriv F (r-2*η) ≤ (A : ℝ) →
        (B : ℝ) ≤ (T/N)*deriv F (l+2*η) →
        ‖∑ q ∈ Finset.Ioo A B,
          (modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q-
            modelPhaseStationaryMainTerm F T N q)‖ ≤
          C*(1+Real.log ((B-A-1).toNat : ℝ)) := by
  exact @modelPhaseBufferedInteriorBlock_error σ hσ

example :
    (∑ n ∈ Finset.range 0, (1/((n+1 : ℕ) : ℝ)+1/((0-n : ℕ) : ℝ))) = 0 := by
  simp

example :
    (∑ n ∈ Finset.range 1, (1/((n+1 : ℕ) : ℝ)+1/((1-n : ℕ) : ℝ))) = 2 := by
  norm_num

example :
    (∑ n ∈ Finset.range 2, (1/((n+1 : ℕ) : ℝ)+1/((2-n : ℕ) : ℝ))) = 3 := by
  norm_num [Finset.sum_range_succ]

end InteriorStationaryRegression
