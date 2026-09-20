import TaoTrudgianYang2025.ZetaLargeValueDiscreteness
import TaoTrudgianYang2025.ZetaIntervalCutoff

/-!
# Pointwise characterization of nonexistent zeta patterns

The singleton below uses the literal coefficient-one interval, at its actual
positive height. Conversely, a pointwise power saving excludes every
ordinate of an actual pattern. The factor two in `[T,2T]` is absorbed by a
smaller parameter radius and a common threshold, not omitted.
-/

noncomputable section

open Filter Set

namespace TaoTrudgianYang2025

private theorem sum_dyadic_indicator_eq {N : ℕ} {I : Finset ℕ}
    (hI : I ⊆ Finset.Icc N (2 * N)) (t : ℝ) :
    (∑ n ∈ Finset.Icc N (2 * N), (if n ∈ I then (1 : ℂ) else 0) * dirichletPhase n t) =
      ∑ n ∈ I, dirichletPhase n t := by
  simp_rw [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  congr 1
  ext n
  simp only [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨hI h, h⟩⟩

private def singletonZetaPattern (N : ℕ) (I : Finset ℕ) (t V : ℝ)
    (hN : 1 < N) (hI : IsIntegerInterval I) (hIN : I ⊆ Finset.Icc N (2 * N))
    (ht : 0 < t) (hV : 0 < V) (hlarge : V ≤ ‖∑ n ∈ I, dirichletPhase n t‖) :
    ZetaLargeValuePattern where
  N := N
  scale := N
  T := t
  V := V
  coeff := fun n => if n ∈ I then 1 else 0
  indices := Finset.Icc N (2 * N)
  intervalLeft := t
  intervalRight := 2 * t
  ordinates := {t}
  N_eq_scale := rfl
  one_lt_N := by exact_mod_cast hN
  T_pos := ht
  V_pos := hV
  mem_indices_iff := by intro n; simp only [Finset.mem_Icc]; norm_cast
  coeff_one_bounded := by intro n _; split_ifs <;> norm_num
  interval_length := by ring
  ordinates_in_interval := by
    intro u hu
    simp only [Finset.mem_singleton] at hu
    subst u
    exact ⟨le_rfl, by linarith⟩
  ordinates_oneSeparated := by
    intro u hu v hv huv
    simp only [Finset.mem_singleton] at hu hv
    exact (huv (hu.trans hv.symm)).elim
  large := by
    intro u hu
    simp only [Finset.mem_singleton] at hu
    subst u
    rw [sum_dyadic_indicator_eq hIN]
    exact hlarge
  active := I
  active_isInterval := hI
  active_subset := hIN
  coeff_eq_indicator := by intro n _; rfl
  intervalLeft_eq := rfl
  intervalRight_eq := rfl

/-- Negative infinity implies a uniform strict power saving for every
literal integer interval in `[N,2N]` at positive heights near `N^τ`. -/
theorem exists_zetaPointwise_powerSaving_of_exponent_eq_bot {σ τ : ℝ}
    (h : zetaLargeValueExponent σ τ = ⊥) :
    ∃ C δ : ℝ, 1 ≤ C ∧ 0 < δ ∧ ∀ (N : ℕ) (I : Finset ℕ) (t : ℝ),
      C ≤ (N : ℝ) → IsIntegerInterval I → I ⊆ Finset.Icc N (2 * N) →
      (N : ℝ) ^ (τ - δ) ≤ t → t ≤ (N : ℝ) ^ (τ + δ) →
      ‖∑ n ∈ I, dirichletPhase n t‖ < (N : ℝ) ^ (σ - δ) := by
  obtain ⟨C, δ, hC, hδ, hempty⟩ :=
    (zetaLargeValueExponent_eq_bot_iff_empty_threshold σ τ).mp h
  refine ⟨max 2 C, δ, (by have := le_max_left (2 : ℝ) C; linarith), hδ, ?_⟩
  intro N I t hNC hI hIN htl htu
  have hNtwo : (2 : ℝ) ≤ N := (le_max_left _ _).trans hNC
  have hN : 1 < N := by exact_mod_cast (show (1 : ℝ) < N by linarith)
  have hNpos : (0 : ℝ) < N := by linarith
  have ht : 0 < t := (Real.rpow_pos_of_pos hNpos _).trans_le htl
  by_contra hnot
  let P := singletonZetaPattern N I t ((N : ℝ) ^ (σ - δ)) hN hI hIN ht
    (Real.rpow_pos_of_pos hNpos _) (le_of_not_gt hnot)
  have he := hempty P ((le_max_right _ _).trans hNC) htl htu le_rfl
    (Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ N) (by linarith))
  have : t ∈ P.ordinates := by simp [P, singletonZetaPattern]
  simp [he] at this

/-- A uniform power saving rules out actual zeta patterns. The threshold
pays for passing from the pattern's height `T` to each ordinate in `[T,2T]`. -/
theorem zetaLargeValueExponent_eq_bot_of_pointwise_powerSaving {σ τ : ℝ}
    (h : ∃ C δ : ℝ, 1 ≤ C ∧ 0 < δ ∧ ∀ (N : ℕ) (I : Finset ℕ) (t : ℝ),
      C ≤ (N : ℝ) → IsIntegerInterval I → I ⊆ Finset.Icc N (2 * N) →
      (N : ℝ) ^ (τ - δ) ≤ t → t ≤ (N : ℝ) ^ (τ + δ) →
      ‖∑ n ∈ I, dirichletPhase n t‖ < (N : ℝ) ^ (σ - δ)) :
    zetaLargeValueExponent σ τ = ⊥ := by
  obtain ⟨C, δ, hC, hδ, hbound⟩ := h
  have hev : ∀ᶠ N : ℝ in atTop, 2 ≤ N ^ (δ / 2) :=
    (tendsto_rpow_atTop (by linarith : 0 < δ / 2)).eventually (eventually_ge_atTop 2)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev
  apply (zetaLargeValueExponent_eq_bot_iff_empty_threshold σ τ).mpr
  refine ⟨max C N₀, δ / 4, hC.trans (le_max_left _ _), (by linarith), ?_⟩
  intro P hN hTl hTu hVl _
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have hNpos : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have htint : t ∈ Icc P.T (2 * P.T) := by
    simpa only [P.intervalLeft_eq, P.intervalRight_eq] using P.ordinates_in_interval t ht
  have htl : P.N ^ (τ - δ) ≤ t :=
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)).trans (hTl.trans htint.1)
  have htu : t ≤ P.N ^ (τ + δ) := by
    calc
      t ≤ 2 * P.N ^ (τ + δ / 4) :=
        htint.2.trans (mul_le_mul_of_nonneg_left hTu (by norm_num))
      _ ≤ P.N ^ (δ / 2) * P.N ^ (τ + δ / 4) :=
        mul_le_mul_of_nonneg_right (hN₀ P.N ((le_max_right _ _).trans hN))
          (Real.rpow_nonneg hNpos.le _)
      _ = P.N ^ (δ / 2 + (τ + δ / 4)) := (Real.rpow_add hNpos _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)
  have hsubset : P.active ⊆ Finset.Icc P.scale (2 * P.scale) := by
    rw [← P.indices_eq_dyadicInterval]
    exact P.active_subset
  have hpoint := hbound P.scale P.active t (P.N_eq_scale ▸ ((le_max_left _ _).trans hN))
    P.active_isInterval hsubset (P.N_eq_scale ▸ htl) (P.N_eq_scale ▸ htu)
  rw [← P.N_eq_scale] at hpoint
  have hlarge := P.large t ht
  rw [P.polynomial_eq_active_sum] at hlarge
  have hp : P.N ^ (σ - δ) ≤ P.N ^ (σ - δ / 4) :=
    Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)
  exact (not_lt_of_ge (hp.trans hVl)) (hlarge.trans_lt hpoint)

theorem zetaLargeValueExponent_eq_bot_iff_pointwise_powerSaving (σ τ : ℝ) :
    zetaLargeValueExponent σ τ = ⊥ ↔
      ∃ C δ : ℝ, 1 ≤ C ∧ 0 < δ ∧ ∀ (N : ℕ) (I : Finset ℕ) (t : ℝ),
        C ≤ (N : ℝ) → IsIntegerInterval I → I ⊆ Finset.Icc N (2 * N) →
        (N : ℝ) ^ (τ - δ) ≤ t → t ≤ (N : ℝ) ^ (τ + δ) →
        ‖∑ n ∈ I, dirichletPhase n t‖ < (N : ℝ) ^ (σ - δ) :=
  ⟨exists_zetaPointwise_powerSaving_of_exponent_eq_bot,
    zetaLargeValueExponent_eq_bot_of_pointwise_powerSaving⟩

end TaoTrudgianYang2025
