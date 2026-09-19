import TaoTrudgianYang2025

open scoped NNReal
open TaoTrudgianYang2025

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

example {σ τ ρ ρstar s : ℝ}
    (h : InLargeValueEnergyRegion σ τ ρ ρstar s) :
    ρ ≤ τ ∧ 2 * ρ ≤ ρstar ∧ ρstar ≤ 3 * ρ :=
  ⟨h.rho_le_tau, h.two_mul_rho_le_rhoStar,
    h.rhoStar_le_three_mul_rho⟩

example :
    InExponentPairTriangle (89 / 1282 : ℝ) (997 / 1282 : ℝ) :=
  publishedExponentPairs_mem_triangle.1

example : generatedExponentPairCoordinates = [
    (89 / 1282, 997 / 1282),
    (652397 / 9713986, 7599781 / 9713986),
    (10769 / 351096, 609317 / 702192),
    (89 / 3478, 15327 / 17390)] := by
  rfl

example := optimizedBourgain_endpoint_agreement

example := optimizedBourgain_interval_cover

example :
    (RationalAffineFraction.mk 270 (-173) 125 (-93)).normalizeSign.eval
        (173 / 229 : ℝ) =
      (RationalAffineFraction.mk 270 (-173) 125 (-93)).eval
        (173 / 229 : ℝ) :=
  RationalAffineFraction.eval_normalizeSign _ _
