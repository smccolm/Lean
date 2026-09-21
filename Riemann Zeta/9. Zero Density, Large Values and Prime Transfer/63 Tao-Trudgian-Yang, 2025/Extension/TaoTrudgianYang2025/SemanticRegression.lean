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
