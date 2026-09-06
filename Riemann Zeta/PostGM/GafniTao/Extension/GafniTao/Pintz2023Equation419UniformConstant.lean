import GafniTao.Pintz2023Equation419Halasz

/-!
# Pintz (2023), equation (4.19): one constant for every selected power

The power in equation (4.16) is selected after the height.  The constants in
the fixed-power Halasz theorem are nevertheless independent of height.  This
file first combines the exact energy and diagonal majorants into the source
power of `N`, and then takes a finite sum of the resulting positive constants
over every admissible power.  The final constant is therefore chosen before
the physical height and before the selected power.
-/

open Complex Finset Filter

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- Height-local normalized form of equation (4.19), with its analytic
constant supplied independently of the height. -/
def Pintz2023Equation419NormalizedAt
    {eta target : ℝ} {k ell : ℕ}
    (data : Pintz2023PowerMarginData eta target k ell)
    (h : ℕ) (C T : ℝ) : Prop :=
  ∃ N₀ : ℕ,
    (N₀ : ℝ) ≤ T ^ pintz2023EllThreshold eta data.epsilon ell ∧
    ∀ (X U N : ℕ) (R : ℝ) (baseI : Finset ℕ)
      (Z : Finset ℝ) (etaAt : ℝ → ℝ),
      let epsilonCoeff := data.epsilon / (100 * (k : ℝ))
      let A :=
        ((1 / (32 * Real.exp 2 *
              Real.log (pintz2023SourceLambda T k)) /
            pintz2023DyadicDepth
              (pintz2023Cutoff (pintz2023SourceLambda T k))) / 2) ^ h / h
      baseI ⊆ Finset.Ioc U (2 * U) → 0 < U → 0 < N → N₀ ≤ N →
      1 ≤ T →
      T ^ pintz2023EllThreshold eta data.epsilon ell ≤ (N : ℝ) →
      (N : ℝ) ≤ T ^ (3 : ℝ) →
      IsSeparated (3 * pintz2023SourceLambda T k) Z →
      (∀ u ∈ Z, etaAt u ∈ Set.Icc 0 eta) →
      (∀ u ∈ Z, ∀ v ∈ Z, |v - u| ≤ T) →
      (∀ u ∈ Z,
        A ≤ ‖dirichletPoly N
          (pintz2023SmallMPoweredLineCoeff X R baseI h
            (1 - etaAt u + 1 / pintz2023SourceLambda T k)) u‖) →
      (Z.card : ℝ) * A ^ 2 ≤
        C * (N : ℝ) ^
          (2 * eta - 2 / pintz2023SourceLambda T k +
            2 * epsilonCoeff)

/-- For one positive power, the exact equation-(4.19) estimate has a fixed
positive constant after the energy and diagonal powers are combined. -/
theorem exists_eventually_pintz2023_equation419_normalized_at
    {eta target : ℝ} {k ell h : ℕ}
    (hcell : PintzCell eta k ell)
    (data : Pintz2023PowerMarginData eta target k ell)
    (hh : 0 < h) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ T : ℝ in atTop,
        Pintz2023Equation419NormalizedAt data h C T := by
  have heta : 0 < eta := pintzCell_eta_pos hcell
  obtain ⟨N₀, Ce, Cd, Cg, hCe, hCd, hCg, hEventually⟩ :=
    exists_eventually_pintz2023_equation419_halasz_native hcell data hh
  let C : ℝ :=
    2 * Ce ^ 2 * pintz2023HalaszKernelConstant⁻¹ * Cd * (4 * eta)⁻¹
  have hC : 0 < C := by
    dsimp only [C]
    exact mul_pos
      (mul_pos
        (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hCe))
          (inv_pos.mpr pintz2023HalaszKernelConstant_pos)) hCd)
      (inv_pos.mpr (by positivity))
  have hell : 0 < ell := lt_of_lt_of_le (by omega) hcell.2.1
  have ha : 0 < pintz2023EllThreshold eta data.epsilon ell := by
    unfold pintz2023EllThreshold
    exact one_div_pos.mpr (pintzEllDenominator_pos hell data.ell_margin)
  have hScale := (tendsto_rpow_atTop ha).eventually
    (eventually_ge_atTop (N₀ : ℝ))
  refine ⟨C, hC, ?_⟩
  filter_upwards [hEventually, hScale] with T hT hN₀
  refine ⟨N₀, hN₀, ?_⟩
  intro X U N R baseI Z etaAt
  dsimp only
  intro hbaseI hU hN hN₀N hTone hCritical hNUpper hSeparated
    hetaAt hDifference hDetected
  have hRaw := hT X U N R baseI Z etaAt hbaseI hU hN hN₀N hTone
    hCritical hNUpper hSeparated hetaAt hDifference hDetected
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hCombine :
      (N : ℝ) ^
            (-4 * eta - 2 / pintz2023SourceLambda T k +
              2 * (data.epsilon / (100 * (k : ℝ)))) *
          (N : ℝ) ^ pintz2023NearOneGramMaxDistance eta eta =
        (N : ℝ) ^
          (2 * eta - 2 / pintz2023SourceLambda T k +
            2 * (data.epsilon / (100 * (k : ℝ)))) := by
    rw [← Real.rpow_add hNReal]
    unfold pintz2023NearOneGramMaxDistance
    congr 1
    ring
  have hRhs :
      2 *
          (Ce ^ 2 * pintz2023HalaszKernelConstant⁻¹ *
            (N : ℝ) ^
              (-4 * eta - 2 / pintz2023SourceLambda T k +
                2 * (data.epsilon / (100 * (k : ℝ))))) *
          pintz2023NearOneDiagonalMajorant Cd N eta eta =
        C * (N : ℝ) ^
          (2 * eta - 2 / pintz2023SourceLambda T k +
            2 * (data.epsilon / (100 * (k : ℝ)))) := by
    unfold pintz2023NearOneDiagonalMajorant
    calc
      _ = C *
          ((N : ℝ) ^
              (-4 * eta - 2 / pintz2023SourceLambda T k +
                2 * (data.epsilon / (100 * (k : ℝ)))) *
            (N : ℝ) ^ pintz2023NearOneGramMaxDistance eta eta) := by
        dsimp only [C]
        ring
      _ = _ := by rw [hCombine]
  exact hRaw.trans_eq hRhs

/-- A single positive constant works simultaneously for every positive power
which equation (4.16) can select. -/
theorem exists_eventually_forall_pintz2023_equation419_normalized_at
    {eta target : ℝ} {k ell : ℕ}
    (hcell : PintzCell eta k ell)
    (data : Pintz2023PowerMarginData eta target k ell) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ T : ℝ in atTop,
        ∀ h ∈ Finset.range (⌈20 / data.epsilon⌉₊ + 1), 0 < h →
          Pintz2023Equation419NormalizedAt data h C T := by
  classical
  let H : Finset ℕ := Finset.range (⌈20 / data.epsilon⌉₊ + 1)
  have hEach : ∀ h : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ᶠ T : ℝ in atTop, 0 < h →
        Pintz2023Equation419NormalizedAt data h C T := by
    intro h
    by_cases hh : 0 < h
    · obtain ⟨C, hC, hEventually⟩ :=
        exists_eventually_pintz2023_equation419_normalized_at hcell data hh
      exact ⟨C, hC, hEventually.mono (fun _ hT _ => hT)⟩
    · refine ⟨1, zero_lt_one, ?_⟩
      filter_upwards [] with T
      intro hh'
      exact False.elim (hh hh')
  choose c hc hEventually using hEach
  let C : ℝ := ∑ h ∈ H, c h
  have hZeroMem : 0 ∈ H := by
    dsimp only [H]
    rw [Finset.mem_range]
    omega
  have hC : 0 < C := by
    dsimp only [C]
    have hZeroLe : c 0 ≤ ∑ h ∈ H, c h :=
      Finset.single_le_sum (fun j _ => (hc j).le) hZeroMem
    exact (hc 0).trans_le hZeroLe
  have hAll : ∀ᶠ T : ℝ in atTop,
      ∀ h ∈ H, 0 < h →
        Pintz2023Equation419NormalizedAt data h (c h) T := by
    apply (Finset.eventually_all H).2
    intro h hh
    exact hEventually h
  refine ⟨C, hC, ?_⟩
  filter_upwards [hAll] with T hAllT
  intro h hhRange hh
  obtain ⟨N₀, hN₀, hConsumer⟩ := hAllT h hhRange hh
  refine ⟨N₀, hN₀, ?_⟩
  intro X U N R baseI Z etaAt
  dsimp only
  intro hbaseI hU hN hN₀N hTone hCritical hNUpper hSeparated
    hetaAt hDifference hDetected
  have hBound := hConsumer X U N R baseI Z etaAt hbaseI hU hN hN₀N
    hTone hCritical hNUpper hSeparated hetaAt hDifference hDetected
  have hcC : c h ≤ C := by
    dsimp only [C]
    exact Finset.single_le_sum (fun j _ => (hc j).le) hhRange
  exact hBound.trans (mul_le_mul_of_nonneg_right hcC
    (Real.rpow_nonneg (by exact_mod_cast hN.le) _))

#print axioms exists_eventually_pintz2023_equation419_normalized_at
#print axioms exists_eventually_forall_pintz2023_equation419_normalized_at

end

end GafniTao
