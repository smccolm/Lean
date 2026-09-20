import TaoTrudgianYang2025.EnergyExponents

/-!
# Five-dimensional large-value energy regions

The paper's `S(N,W)` is represented literally as a double sum over the
one-separated ordinate set.  Region membership uses the fully quantified
non-asymptotic formulation: every accuracy and scale threshold admits a
pattern realizing all five exponents simultaneously.
-/

noncomputable section

namespace TaoTrudgianYang2025

/-- The double zeta sum `S(N,W)` attached to a large-value pattern. -/
def doubleZetaSum (P : LargeValuePattern) : ℝ :=
  ∑ t ∈ P.ordinates, ∑ u ∈ P.ordinates,
    ‖∑ n ∈ P.indices, dirichletPhase n (t - u)‖ ^ 2

/-- The unweighted Dirichlet polynomial is the support cardinality on the
diagonal. -/
theorem LargeValuePattern.phaseSum_zero (P : LargeValuePattern) :
    ∑ n ∈ P.indices, dirichletPhase n 0 = (P.indices.card : ℂ) := by
  simp [dirichletPhase_zero]

/-- Triangle-inequality control of the unweighted Dirichlet polynomial. -/
theorem LargeValuePattern.norm_phaseSum_le (P : LargeValuePattern) (t : ℝ) :
    ‖∑ n ∈ P.indices, dirichletPhase n t‖ ≤ P.indices.card := by
  calc
    ‖∑ n ∈ P.indices, dirichletPhase n t‖ ≤
        ∑ n ∈ P.indices, ‖dirichletPhase n t‖ := norm_sum_le _ _
    _ = ∑ _n ∈ P.indices, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact P.norm_dirichletPhase hn t
    _ = P.indices.card := by simp

/-- The double zeta sum is nonnegative. -/
theorem doubleZetaSum_nonneg (P : LargeValuePattern) :
    0 ≤ doubleZetaSum P := by
  unfold doubleZetaSum
  positivity

/-- The diagonal pairs give a cardinality lower bound for the double zeta
sum. -/
theorem doubleZetaSum_diagonal_lower (P : LargeValuePattern) :
    (P.ordinates.card : ℝ) * (P.indices.card : ℝ) ^ 2 ≤
      doubleZetaSum P := by
  have hdiag (t : ℝ) (ht : t ∈ P.ordinates) :
      (P.indices.card : ℝ) ^ 2 ≤
        ∑ u ∈ P.ordinates,
          ‖∑ n ∈ P.indices, dirichletPhase n (t - u)‖ ^ 2 := by
    have hterm :
        ‖∑ n ∈ P.indices, dirichletPhase n (t - t)‖ ^ 2 =
          (P.indices.card : ℝ) ^ 2 := by
      rw [sub_self, P.phaseSum_zero]
      simp
    rw [← hterm]
    exact Finset.single_le_sum
      (fun u hu => sq_nonneg
        ‖∑ n ∈ P.indices, dirichletPhase n (t - u)‖) ht
  unfold doubleZetaSum
  calc
    (P.ordinates.card : ℝ) * (P.indices.card : ℝ) ^ 2 =
        ∑ _t ∈ P.ordinates, (P.indices.card : ℝ) ^ 2 := by simp
    _ ≤ ∑ t ∈ P.ordinates, ∑ u ∈ P.ordinates,
        ‖∑ n ∈ P.indices, dirichletPhase n (t - u)‖ ^ 2 := by
      exact Finset.sum_le_sum fun t ht => hdiag t ht

/-- Applying the triangle inequality termwise gives a polynomial upper bound
for the double zeta sum. -/
theorem doubleZetaSum_card_upper (P : LargeValuePattern) :
    doubleZetaSum P ≤
      (P.ordinates.card : ℝ) ^ 2 * (P.indices.card : ℝ) ^ 2 := by
  have hterm (t u : ℝ) :
      ‖∑ n ∈ P.indices, dirichletPhase n (t - u)‖ ^ 2 ≤
        (P.indices.card : ℝ) ^ 2 := by
    have h := P.norm_phaseSum_le (t - u)
    nlinarith [norm_nonneg (∑ n ∈ P.indices, dirichletPhase n (t - u))]
  unfold doubleZetaSum
  calc
    ∑ t ∈ P.ordinates, ∑ u ∈ P.ordinates,
        ‖∑ n ∈ P.indices, dirichletPhase n (t - u)‖ ^ 2 ≤
        ∑ _t ∈ P.ordinates, ∑ _u ∈ P.ordinates,
          (P.indices.card : ℝ) ^ 2 := by
      exact Finset.sum_le_sum fun t _ =>
        Finset.sum_le_sum fun u _ => hterm t u
    _ = (P.ordinates.card : ℝ) ^ 2 * (P.indices.card : ℝ) ^ 2 := by
      simp
      ring

/-- Non-asymptotic membership in the paper's five-dimensional region `E`.
The source TeX leaves `δ` unbound in clause (ii); the required meaning is
arbitrary positive approximation radius, made explicit here. -/
def InLargeValueEnergyRegion
    (σ τ ρ ρstar s : ℝ) : Prop :=
  1 / 2 ≤ σ ∧ σ ≤ 1 ∧ 0 ≤ τ ∧ 0 ≤ ρ ∧ 0 ≤ ρstar ∧
    ∀ ε : ℝ, 0 < ε →
      ∀ δ : ℝ, 0 < δ →
        ∀ C : ℝ, 0 < C →
          ∃ P : LargeValuePattern,
            C ≤ P.N ∧
            P.N ^ (τ - δ) ≤ P.T ∧
            P.T ≤ P.N ^ (τ + δ) ∧
            P.N ^ (σ - δ) ≤ P.V ∧
            P.V ≤ P.N ^ (σ + δ) ∧
            P.N ^ (ρ - ε) ≤ (P.ordinates.card : ℝ) ∧
            (P.ordinates.card : ℝ) ≤ P.N ^ (ρ + ε) ∧
            P.N ^ (ρstar - ε) ≤
              (finsetAdditiveEnergy P.ordinates : ℝ) ∧
            (finsetAdditiveEnergy P.ordinates : ℝ) ≤
              P.N ^ (ρstar + ε) ∧
            P.N ^ (s - ε) ≤ doubleZetaSum P ∧
            doubleZetaSum P ≤ P.N ^ (s + ε)

/-- Non-asymptotic membership in the zeta energy region `E_ζ`. -/
def InZetaLargeValueEnergyRegion
    (σ τ ρ ρstar s : ℝ) : Prop :=
  1 / 2 ≤ σ ∧ σ ≤ 1 ∧ 0 ≤ τ ∧ 0 ≤ ρ ∧ 0 ≤ ρstar ∧
    ∀ ε : ℝ, 0 < ε →
      ∀ δ : ℝ, 0 < δ →
        ∀ C : ℝ, 0 < C →
          ∃ P : ZetaLargeValuePattern,
            C ≤ P.N ∧
            P.N ^ (τ - δ) ≤ P.T ∧
            P.T ≤ P.N ^ (τ + δ) ∧
            P.N ^ (σ - δ) ≤ P.V ∧
            P.V ≤ P.N ^ (σ + δ) ∧
            P.N ^ (ρ - ε) ≤ (P.ordinates.card : ℝ) ∧
            (P.ordinates.card : ℝ) ≤ P.N ^ (ρ + ε) ∧
            P.N ^ (ρstar - ε) ≤
              (finsetAdditiveEnergy P.ordinates : ℝ) ∧
            (finsetAdditiveEnergy P.ordinates : ℝ) ≤
              P.N ^ (ρstar + ε) ∧
            P.N ^ (s - ε) ≤ doubleZetaSum P.toLargeValuePattern ∧
            doubleZetaSum P.toLargeValuePattern ≤ P.N ^ (s + ε)

/-- Forgetting the zeta restrictions sends `E_ζ` into `E`. -/
theorem InZetaLargeValueEnergyRegion.toGeneral
    {σ τ ρ ρstar s : ℝ}
    (h : InZetaLargeValueEnergyRegion σ τ ρ ρstar s) :
    InLargeValueEnergyRegion σ τ ρ ρstar s := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, ?_⟩
  intro ε hε δ hδ C hC
  obtain ⟨P, hP⟩ := h.2.2.2.2.2 ε hε δ hδ C hC
  exact ⟨P.toLargeValuePattern, hP⟩

/-- Every uniform energy bound dominates the energy coordinate of every
feasible tuple.  This is the easy direction of the paper's region-supremum
characterization. -/
theorem InLargeValueEnergyRegion.rhoStar_le_of_energyBound
    {σ τ ρ ρstar s B : ℝ}
    (hregion : InLargeValueEnergyRegion σ τ ρ ρstar s)
    (hbound : IsLargeValueEnergyBound σ τ B) :
    ρstar ≤ B := by
  by_contra hcontra
  have hgap : 0 < ρstar - B := sub_pos.mpr (lt_of_not_ge hcontra)
  let ε : ℝ := (ρstar - B) / 4
  have hε : 0 < ε := div_pos hgap (by norm_num)
  obtain ⟨K, hK, δ, hδ, henergy⟩ := hbound ε hε
  let C : ℝ := max K (K ^ (1 / ε : ℝ))
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (hK.trans (le_max_left _ _))
  obtain ⟨P, hP⟩ :=
    hregion.2.2.2.2.2 ε hε δ hδ C hC
  rcases hP with
    ⟨hNLower, hTLower, hTUpper, hVLower, hVUpper, _, _,
      hEnergyLower, _, _, _⟩
  have hKN : K ≤ P.N := (le_max_left _ _).trans hNLower
  have hEnergyUpper :=
    henergy P hKN hTLower hTUpper hVLower hVUpper
  have hKPowerBase : K ^ (1 / ε : ℝ) ≤ P.N :=
    (le_max_right _ _).trans hNLower
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hKAbsorb : K ≤ P.N ^ ε := by
    calc
      K = K ^ (1 : ℝ) := (Real.rpow_one K).symm
      _ = K ^ ((1 / ε) * ε) := by
        congr 1
        field_simp
      _ = (K ^ (1 / ε : ℝ)) ^ ε :=
        Real.rpow_mul hKpos.le _ _
      _ ≤ P.N ^ ε :=
        Real.rpow_le_rpow (by positivity) hKPowerBase hε.le
  have hPowerOrder : P.N ^ (ρstar - ε) ≤ P.N ^ (B + 2 * ε) := by
    calc
      P.N ^ (ρstar - ε) ≤
          (finsetAdditiveEnergy P.ordinates : ℝ) := hEnergyLower
      _ ≤ K * P.N ^ (B + ε) := hEnergyUpper
      _ ≤ P.N ^ ε * P.N ^ (B + ε) := by
        exact mul_le_mul_of_nonneg_right hKAbsorb
          (Real.rpow_nonneg (zero_le_one.trans P.one_lt_N.le) _)
      _ = P.N ^ (B + 2 * ε) := by
        rw [← Real.rpow_add (lt_trans zero_lt_one P.one_lt_N)]
        congr 1
        ring
  have hExponentStrict : B + 2 * ε < ρstar - ε := by
    dsimp [ε]
    linarith
  have hPowerStrict :=
    Real.rpow_lt_rpow_of_exponent_lt P.one_lt_N hExponentStrict
  exact (not_lt_of_ge hPowerOrder) hPowerStrict

/-- The zeta-restricted version of `rhoStar_le_of_energyBound`. -/
theorem InZetaLargeValueEnergyRegion.rhoStar_le_of_energyBound
    {σ τ ρ ρstar s B : ℝ}
    (hregion : InZetaLargeValueEnergyRegion σ τ ρ ρstar s)
    (hbound : IsZetaLargeValueEnergyBound σ τ B) :
    ρstar ≤ B := by
  by_contra hcontra
  have hgap : 0 < ρstar - B := sub_pos.mpr (lt_of_not_ge hcontra)
  let ε : ℝ := (ρstar - B) / 4
  have hε : 0 < ε := div_pos hgap (by norm_num)
  obtain ⟨K, hK, δ, hδ, henergy⟩ := hbound ε hε
  let C : ℝ := max K (K ^ (1 / ε : ℝ))
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (hK.trans (le_max_left _ _))
  obtain ⟨P, hP⟩ :=
    hregion.2.2.2.2.2 ε hε δ hδ C hC
  rcases hP with
    ⟨hNLower, hTLower, hTUpper, hVLower, hVUpper, _, _,
      hEnergyLower, _, _, _⟩
  have hKN : K ≤ P.N := (le_max_left _ _).trans hNLower
  have hEnergyUpper :=
    henergy P hKN hTLower hTUpper hVLower hVUpper
  have hKPowerBase : K ^ (1 / ε : ℝ) ≤ P.N :=
    (le_max_right _ _).trans hNLower
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hKAbsorb : K ≤ P.N ^ ε := by
    calc
      K = K ^ (1 : ℝ) := (Real.rpow_one K).symm
      _ = K ^ ((1 / ε) * ε) := by
        congr 1
        field_simp
      _ = (K ^ (1 / ε : ℝ)) ^ ε :=
        Real.rpow_mul hKpos.le _ _
      _ ≤ P.N ^ ε :=
        Real.rpow_le_rpow (by positivity) hKPowerBase hε.le
  have hPowerOrder : P.N ^ (ρstar - ε) ≤ P.N ^ (B + 2 * ε) := by
    calc
      P.N ^ (ρstar - ε) ≤
          (finsetAdditiveEnergy P.ordinates : ℝ) := hEnergyLower
      _ ≤ K * P.N ^ (B + ε) := hEnergyUpper
      _ ≤ P.N ^ ε * P.N ^ (B + ε) := by
        exact mul_le_mul_of_nonneg_right hKAbsorb
          (Real.rpow_nonneg (zero_le_one.trans P.one_lt_N.le) _)
      _ = P.N ^ (B + 2 * ε) := by
        rw [← Real.rpow_add (lt_trans zero_lt_one P.one_lt_N)]
        congr 1
        ring
  have hExponentStrict : B + 2 * ε < ρstar - ε := by
    dsimp [ε]
    linarith
  have hPowerStrict :=
    Real.rpow_lt_rpow_of_exponent_lt P.one_lt_N hExponentStrict
  exact (not_lt_of_ge hPowerOrder) hPowerStrict

/-- Every feasible energy tuple satisfies the diagonal constraint
`2ρ ≤ ρ*`. -/
theorem InLargeValueEnergyRegion.two_mul_rho_le_rhoStar
    {σ τ ρ ρstar s : ℝ}
    (h : InLargeValueEnergyRegion σ τ ρ ρstar s) :
    2 * ρ ≤ ρstar := by
  by_contra hcontra
  have hgap : 0 < 2 * ρ - ρstar := sub_pos.mpr (lt_of_not_ge hcontra)
  let ε : ℝ := (2 * ρ - ρstar) / 4
  have hε : 0 < ε := div_pos hgap (by norm_num)
  obtain ⟨P, hP⟩ := h.2.2.2.2.2 ε hε 1 zero_lt_one 1 zero_lt_one
  rcases hP with
    ⟨_, _, _, _, _, hCardLower, _, _, hEnergyUpper, _, _⟩
  have hSquareNat := finset_card_square_le_additiveEnergy P.ordinates
  have hSquare : (P.ordinates.card : ℝ) ^ 2 ≤
      (finsetAdditiveEnergy P.ordinates : ℝ) := by
    exact_mod_cast hSquareNat
  have hPowerSquare : (P.N ^ (ρ - ε)) ^ 2 = P.N ^ (2 * (ρ - ε)) := by
    have hNNonneg : 0 ≤ P.N := zero_le_one.trans P.one_lt_N.le
    calc
      (P.N ^ (ρ - ε)) ^ 2 = P.N ^ ((ρ - ε) * (2 : ℝ)) := by
        rw [Real.rpow_mul hNNonneg]
        exact (Real.rpow_natCast (P.N ^ (ρ - ε)) 2).symm
      _ = P.N ^ (2 * (ρ - ε)) := by ring_nf
  have hPowerOrder : P.N ^ (2 * (ρ - ε)) ≤ P.N ^ (ρstar + ε) := by
    calc
      P.N ^ (2 * (ρ - ε)) = (P.N ^ (ρ - ε)) ^ 2 := hPowerSquare.symm
      _ ≤ (P.ordinates.card : ℝ) ^ 2 := by
        gcongr
      _ ≤ (finsetAdditiveEnergy P.ordinates : ℝ) := hSquare
      _ ≤ P.N ^ (ρstar + ε) := hEnergyUpper
  have hExponentStrict : ρstar + ε < 2 * (ρ - ε) := by
    dsimp [ε]
    linarith
  have hPowerStrict :=
    Real.rpow_lt_rpow_of_exponent_lt P.one_lt_N hExponentStrict
  exact (not_lt_of_ge hPowerOrder) hPowerStrict

/-- Every feasible energy tuple satisfies the one-separated cubic constraint
`ρ* ≤ 3ρ`. -/
theorem InLargeValueEnergyRegion.rhoStar_le_three_mul_rho
    {σ τ ρ ρstar s : ℝ}
    (h : InLargeValueEnergyRegion σ τ ρ ρstar s) :
    ρstar ≤ 3 * ρ := by
  by_contra hcontra
  have hgap : 0 < ρstar - 3 * ρ := sub_pos.mpr (lt_of_not_ge hcontra)
  let ε : ℝ := (ρstar - 3 * ρ) / 6
  have hε : 0 < ε := div_pos hgap (by norm_num)
  let C : ℝ := max 1 (3 ^ (1 / ε : ℝ))
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨P, hP⟩ := h.2.2.2.2.2 ε hε 1 zero_lt_one C hC
  rcases hP with
    ⟨hNLower, _, _, _, _, _, hCardUpper, hEnergyLower, _, _, _⟩
  have hEnergyNat := finset_additiveEnergy_le_three_mul_cube
    P.ordinates P.ordinates_oneSeparated
  have hEnergy : (finsetAdditiveEnergy P.ordinates : ℝ) ≤
      3 * (P.ordinates.card : ℝ) ^ 3 := by
    exact_mod_cast hEnergyNat
  have hThreeBase : 3 ^ (1 / ε : ℝ) ≤ P.N :=
    (le_max_right _ _).trans hNLower
  have hThree : (3 : ℝ) ≤ P.N ^ ε := by
    calc
      (3 : ℝ) = 3 ^ (1 : ℝ) := (Real.rpow_one 3).symm
      _ = 3 ^ ((1 / ε) * ε) := by
        congr 1
        field_simp
      _ = (3 ^ (1 / ε : ℝ)) ^ ε :=
        Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) _ _
      _ ≤ P.N ^ ε := Real.rpow_le_rpow (by positivity) hThreeBase hε.le
  have hPowerCube : (P.N ^ (ρ + ε)) ^ 3 = P.N ^ (3 * (ρ + ε)) := by
    have hNNonneg : 0 ≤ P.N := zero_le_one.trans P.one_lt_N.le
    calc
      (P.N ^ (ρ + ε)) ^ 3 = P.N ^ ((ρ + ε) * (3 : ℝ)) := by
        rw [Real.rpow_mul hNNonneg]
        exact (Real.rpow_natCast (P.N ^ (ρ + ε)) 3).symm
      _ = P.N ^ (3 * (ρ + ε)) := by ring_nf
  have hPowerOrder : P.N ^ (ρstar - ε) ≤ P.N ^ (3 * ρ + 4 * ε) := by
    calc
      P.N ^ (ρstar - ε) ≤ (finsetAdditiveEnergy P.ordinates : ℝ) :=
        hEnergyLower
      _ ≤ 3 * (P.ordinates.card : ℝ) ^ 3 := hEnergy
      _ ≤ 3 * (P.N ^ (ρ + ε)) ^ 3 := by gcongr
      _ = 3 * P.N ^ (3 * (ρ + ε)) := by rw [hPowerCube]
      _ ≤ P.N ^ ε * P.N ^ (3 * (ρ + ε)) := by
        exact mul_le_mul_of_nonneg_right hThree
          (Real.rpow_nonneg (zero_le_one.trans P.one_lt_N.le) _)
      _ = P.N ^ (3 * ρ + 4 * ε) := by
        rw [← Real.rpow_add (lt_trans zero_lt_one P.one_lt_N)]
        congr 1
        ring
  have hExponentStrict : 3 * ρ + 4 * ε < ρstar - ε := by
    dsimp [ε]
    linarith
  have hPowerStrict :=
    Real.rpow_lt_rpow_of_exponent_lt P.one_lt_N hExponentStrict
  exact (not_lt_of_ge hPowerOrder) hPowerStrict

/-- A one-separated set in an interval of length `N^(τ+o(1))` has cardinality
exponent at most `τ`. -/
theorem InLargeValueEnergyRegion.rho_le_tau
    {σ τ ρ ρstar s : ℝ}
    (h : InLargeValueEnergyRegion σ τ ρ ρstar s) :
    ρ ≤ τ := by
  by_contra hcontra
  have hgap : 0 < ρ - τ := sub_pos.mpr (lt_of_not_ge hcontra)
  let ε : ℝ := (ρ - τ) / 4
  have hε : 0 < ε := div_pos hgap (by norm_num)
  let C : ℝ := max 1 (2 ^ (1 / ε : ℝ))
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨P, hP⟩ := h.2.2.2.2.2 ε hε ε hε C hC
  rcases hP with
    ⟨hNLower, _, hTUpper, _, _, hCardLower, _, _, _, _, _⟩
  have hTwoBase : 2 ^ (1 / ε : ℝ) ≤ P.N :=
    (le_max_right _ _).trans hNLower
  have hTwo : (2 : ℝ) ≤ P.N ^ ε := by
    calc
      (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one 2).symm
      _ = 2 ^ ((1 / ε) * ε) := by
        congr 1
        field_simp
      _ = (2 ^ (1 / ε : ℝ)) ^ ε :=
        Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) _ _
      _ ≤ P.N ^ ε := Real.rpow_le_rpow (by positivity) hTwoBase hε.le
  have hTauEpsilon : 0 ≤ τ + ε := by
    have hτ : 0 ≤ τ := h.2.2.1
    linarith
  have hScalePowerOne : 1 ≤ P.N ^ (τ + ε) :=
    Real.one_le_rpow P.one_lt_N.le hTauEpsilon
  have hPowerOrder : P.N ^ (ρ - ε) ≤ P.N ^ (τ + 2 * ε) := by
    calc
      P.N ^ (ρ - ε) ≤ (P.ordinates.card : ℝ) := hCardLower
      _ ≤ P.T + 1 := P.ordinate_card_cast_le
      _ ≤ P.N ^ (τ + ε) + 1 := by linarith
      _ ≤ 2 * P.N ^ (τ + ε) := by linarith
      _ ≤ P.N ^ ε * P.N ^ (τ + ε) := by
        exact mul_le_mul_of_nonneg_right hTwo
          (Real.rpow_nonneg (zero_le_one.trans P.one_lt_N.le) _)
      _ = P.N ^ (τ + 2 * ε) := by
        rw [← Real.rpow_add (lt_trans zero_lt_one P.one_lt_N)]
        congr 1
        ring
  have hExponentStrict : τ + 2 * ε < ρ - ε := by
    dsimp [ε]
    linarith
  have hPowerStrict :=
    Real.rpow_lt_rpow_of_exponent_lt P.one_lt_N hExponentStrict
  exact (not_lt_of_ge hPowerOrder) hPowerStrict

/-- The diagonal contribution to the double zeta sum forces
`ρ + 2 ≤ s`. -/
theorem InLargeValueEnergyRegion.rho_add_two_le_s
    {σ τ ρ ρstar s : ℝ}
    (h : InLargeValueEnergyRegion σ τ ρ ρstar s) :
    ρ + 2 ≤ s := by
  by_contra hcontra
  have hgap : 0 < ρ + 2 - s := sub_pos.mpr (lt_of_not_ge hcontra)
  let ε : ℝ := (ρ + 2 - s) / 3
  have hε : 0 < ε := div_pos hgap (by norm_num)
  obtain ⟨P, hP⟩ := h.2.2.2.2.2 ε hε 1 zero_lt_one 1 zero_lt_one
  rcases hP with
    ⟨_, _, _, _, _, hCardLower, _, _, _, _, hSumUpper⟩
  have hDiagonal := doubleZetaSum_diagonal_lower P
  have hIndexSquare : P.N ^ 2 ≤
      (P.indices.card : ℝ) ^ 2 := by
    nlinarith [P.N_le_indices_card_cast]
  have hPowerOrder : P.N ^ (ρ + 2 - ε) ≤ P.N ^ (s + ε) := by
    calc
      P.N ^ (ρ + 2 - ε) =
          P.N ^ (ρ - ε) * P.N ^ 2 := by
        rw [show ρ + 2 - ε = (ρ - ε) + 2 by ring,
          Real.rpow_add (lt_trans zero_lt_one P.one_lt_N), Real.rpow_two]
      _ ≤ (P.ordinates.card : ℝ) * (P.indices.card : ℝ) ^ 2 := by
        exact mul_le_mul hCardLower hIndexSquare
          (sq_nonneg P.N)
          (Nat.cast_nonneg _)
      _ ≤ doubleZetaSum P := hDiagonal
      _ ≤ P.N ^ (s + ε) := hSumUpper
  have hExponentStrict : s + ε < ρ + 2 - ε := by
    dsimp [ε]
    linarith
  have hPowerStrict :=
    Real.rpow_lt_rpow_of_exponent_lt P.one_lt_N hExponentStrict
  exact (not_lt_of_ge hPowerOrder) hPowerStrict

/-- Termwise triangle inequality forces the complementary upper constraint
`s ≤ 2ρ + 2`. -/
theorem InLargeValueEnergyRegion.s_le_two_mul_rho_add_two
    {σ τ ρ ρstar s : ℝ}
    (h : InLargeValueEnergyRegion σ τ ρ ρstar s) :
    s ≤ 2 * ρ + 2 := by
  by_contra hcontra
  have hgap : 0 < s - (2 * ρ + 2) := sub_pos.mpr (lt_of_not_ge hcontra)
  let ε : ℝ := (s - (2 * ρ + 2)) / 5
  have hε : 0 < ε := div_pos hgap (by norm_num)
  let C : ℝ := max 1 (4 ^ (1 / ε : ℝ))
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨P, hP⟩ := h.2.2.2.2.2 ε hε 1 zero_lt_one C hC
  rcases hP with
    ⟨hNLower, _, _, _, _, _, hCardUpper, _, _, hSumLower, _⟩
  have hSumBound := doubleZetaSum_card_upper P
  have hFourBase : 4 ^ (1 / ε : ℝ) ≤ P.N :=
    (le_max_right _ _).trans hNLower
  have hFour : (4 : ℝ) ≤ P.N ^ ε := by
    calc
      (4 : ℝ) = 4 ^ (1 : ℝ) := (Real.rpow_one 4).symm
      _ = 4 ^ ((1 / ε) * ε) := by
        congr 1
        field_simp
      _ = (4 ^ (1 / ε : ℝ)) ^ ε :=
        Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4) _ _
      _ ≤ P.N ^ ε := Real.rpow_le_rpow (by positivity) hFourBase hε.le
  have hCardSquare : (P.ordinates.card : ℝ) ^ 2 ≤
      (P.N ^ (ρ + ε)) ^ 2 := by
    exact (sq_le_sq₀ (Nat.cast_nonneg P.ordinates.card)
      (Real.rpow_nonneg (zero_le_one.trans P.one_lt_N.le) (ρ + ε))).2
        hCardUpper
  have hIndexSquare : (P.indices.card : ℝ) ^ 2 ≤
      4 * P.N ^ 2 := by
    have hi := P.indices_card_cast_le_two_mul_N
    calc
      (P.indices.card : ℝ) ^ 2 ≤ (2 * P.N) ^ 2 :=
        (sq_le_sq₀ (Nat.cast_nonneg P.indices.card)
          (mul_nonneg (by norm_num) (zero_le_one.trans P.one_lt_N.le))).2 hi
      _ = 4 * P.N ^ 2 := by ring
  have hPowerSquare : (P.N ^ (ρ + ε)) ^ 2 =
      P.N ^ (2 * (ρ + ε)) := by
    have hNNonneg : 0 ≤ P.N := P.one_lt_N.le.trans' zero_le_one
    calc
      (P.N ^ (ρ + ε)) ^ 2 = P.N ^ ((ρ + ε) * (2 : ℝ)) := by
        rw [Real.rpow_mul hNNonneg]
        exact (Real.rpow_natCast (P.N ^ (ρ + ε)) 2).symm
      _ = P.N ^ (2 * (ρ + ε)) := by ring_nf
  have hPowerOrder : P.N ^ (s - ε) ≤ P.N ^ (2 * ρ + 2 + 3 * ε) := by
    calc
      P.N ^ (s - ε) ≤ doubleZetaSum P := hSumLower
      _ ≤ (P.ordinates.card : ℝ) ^ 2 *
          (P.indices.card : ℝ) ^ 2 := hSumBound
      _ ≤ (P.N ^ (ρ + ε)) ^ 2 * (4 * P.N ^ 2) := by
        exact mul_le_mul hCardSquare hIndexSquare (sq_nonneg _)
          (sq_nonneg _)
      _ = 4 * (P.N ^ (2 * (ρ + ε)) * P.N ^ 2) := by
        rw [hPowerSquare]
        ring
      _ ≤ P.N ^ ε *
          (P.N ^ (2 * (ρ + ε)) * P.N ^ 2) := by
        exact mul_le_mul_of_nonneg_right hFour
          (mul_nonneg
            (Real.rpow_nonneg (zero_le_one.trans P.one_lt_N.le) _)
            (sq_nonneg P.N))
      _ = P.N ^ (2 * ρ + 2 + 3 * ε) := by
        rw [← Real.rpow_natCast P.N 2]
        rw [← Real.rpow_add (lt_trans zero_lt_one P.one_lt_N),
          ← Real.rpow_add (lt_trans zero_lt_one P.one_lt_N)]
        congr 1
        ring
  have hExponentStrict : 2 * ρ + 2 + 3 * ε < s - ε := by
    dsimp [ε]
    linarith
  have hPowerStrict :=
    Real.rpow_lt_rpow_of_exponent_lt P.one_lt_N hExponentStrict
  exact (not_lt_of_ge hPowerOrder) hPowerStrict

theorem InZetaLargeValueEnergyRegion.two_mul_rho_le_rhoStar
    {σ τ ρ ρstar s : ℝ}
    (h : InZetaLargeValueEnergyRegion σ τ ρ ρstar s) :
    2 * ρ ≤ ρstar :=
  h.toGeneral.two_mul_rho_le_rhoStar

theorem InZetaLargeValueEnergyRegion.rhoStar_le_three_mul_rho
    {σ τ ρ ρstar s : ℝ}
    (h : InZetaLargeValueEnergyRegion σ τ ρ ρstar s) :
    ρstar ≤ 3 * ρ :=
  h.toGeneral.rhoStar_le_three_mul_rho

theorem InZetaLargeValueEnergyRegion.rho_le_tau
    {σ τ ρ ρstar s : ℝ}
    (h : InZetaLargeValueEnergyRegion σ τ ρ ρstar s) :
    ρ ≤ τ :=
  h.toGeneral.rho_le_tau

theorem InZetaLargeValueEnergyRegion.rho_add_two_le_s
    {σ τ ρ ρstar s : ℝ}
    (h : InZetaLargeValueEnergyRegion σ τ ρ ρstar s) :
    ρ + 2 ≤ s :=
  h.toGeneral.rho_add_two_le_s

theorem InZetaLargeValueEnergyRegion.s_le_two_mul_rho_add_two
    {σ τ ρ ρstar s : ℝ}
    (h : InZetaLargeValueEnergyRegion σ τ ρ ρstar s) :
    s ≤ 2 * ρ + 2 :=
  h.toGeneral.s_le_two_mul_rho_add_two

/-- The extended-real supremum of energy coordinates occurring in the
general feasible region at fixed `(σ,τ)`. -/
noncomputable def largeValueEnergyRegionSupremum (σ τ : ℝ) : EReal :=
  sSup (((fun ρstar : ℝ => (ρstar : EReal)) ''
    {ρstar : ℝ | ∃ ρ s : ℝ,
      InLargeValueEnergyRegion σ τ ρ ρstar s}) : Set EReal)

/-- The extended-real supremum of energy coordinates occurring in the zeta
feasible region at fixed `(σ,τ)`. -/
noncomputable def zetaLargeValueEnergyRegionSupremum (σ τ : ℝ) : EReal :=
  sSup (((fun ρstar : ℝ => (ρstar : EReal)) ''
    {ρstar : ℝ | ∃ ρ s : ℝ,
      InZetaLargeValueEnergyRegion σ τ ρ ρstar s}) : Set EReal)

/-- Every feasible-region energy coordinate is controlled by every uniform
energy bound, hence the region supremum is at most `LV*`. -/
theorem largeValueEnergyRegionSupremum_le_largeValueEnergyExponent
    (σ τ : ℝ) :
    largeValueEnergyRegionSupremum σ τ ≤
      largeValueEnergyExponent σ τ := by
  unfold largeValueEnergyRegionSupremum largeValueEnergyExponent
  apply le_sInf
  rintro x ⟨B, hB, rfl⟩
  apply sSup_le
  rintro y ⟨ρstar, ⟨ρ, s, hregion⟩, rfl⟩
  exact EReal.coe_le_coe_iff.mpr
    (hregion.rhoStar_le_of_energyBound hB)

/-- The zeta feasible-region supremum is at most `LV*_ζ`. -/
theorem zetaLargeValueEnergyRegionSupremum_le_zetaLargeValueEnergyExponent
    (σ τ : ℝ) :
    zetaLargeValueEnergyRegionSupremum σ τ ≤
      zetaLargeValueEnergyExponent σ τ := by
  unfold zetaLargeValueEnergyRegionSupremum zetaLargeValueEnergyExponent
  apply le_sInf
  rintro x ⟨B, hB, rfl⟩
  apply sSup_le
  rintro y ⟨ρstar, ⟨ρ, s, hregion⟩, rfl⟩
  exact EReal.coe_le_coe_iff.mpr
    (hregion.rhoStar_le_of_energyBound hB)

end TaoTrudgianYang2025
