import GafniTao.Pintz2023WeightedBlockBoundary

/-!
# Corollary 3 with the literal rounded source endpoints

The common critical scale is real-valued while the Dirichlet sums are over
natural numbers.  Replacing its floor by its ceiling and dividing a dyadic
interval by `d` leaves at most one term at each boundary.  This theorem
assembles the main Corollary-3 block and both explicitly bounded terms.
-/

open Complex Finset

namespace GafniTao

noncomputable section

theorem pintz2023_corollary_three_rounded
    (r : ℕ) (epsilon B₀ : ℝ) (hr : 3 ≤ r)
    (hepsilon : 0 < epsilon) (hB₀ : 0 < B₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (xi Q t T : ℝ) (A U : ℕ),
        xi ≤ pintz2023HBAlpha r - 6 * epsilon →
        0 < 1 - ((r : ℝ) - 1) * xi -
          6 * (r : ℝ) * epsilon →
        xi + 3 * epsilon ≤ 1 →
        1 ≤ Q →
        pintz2023CriticalScale r xi epsilon T ≤ Q →
        0 < |t| → |t| ≤ T → 1 ≤ T →
        0 < A → U ≤ 2 * A + 1 →
        ((max A (Nat.ceil Q) : ℕ) : ℝ) ≤
          B₀ * |t| ^ (2 / (r : ℝ)) →
        ‖pintz2023ComplexWeightedBlock xi
            (max A (Nat.floor Q)) U t‖ ≤
          C * Q ^ (-3 * epsilon) := by
  obtain ⟨C₀, hC₀, hcor⟩ :=
    pintz2023_corollary_three_abs r epsilon B₀ hr hepsilon hB₀
  refine ⟨C₀ + 2, by linarith, ?_⟩
  intro xi Q t T A U hxi hden hxiOne hQ hcritical ht htT hT
    hA hupper hphysical
  let L : ℕ := max A (Nat.floor Q)
  let N : ℕ := max A (Nat.ceil Q)
  have hfloorCeil : Nat.floor Q ≤ Nat.ceil Q := Nat.floor_le_ceil Q
  have hLN : L ≤ N := by
    dsimp only [L, N]
    exact max_le_max le_rfl hfloorCeil
  have hNL : N ≤ L + 1 := by
    dsimp only [L, N]
    have hceil := Nat.ceil_le_floor_add_one Q
    omega
  have hAN : A ≤ N := by dsimp only [N]; exact le_max_left _ _
  have hNPos : 0 < N := hA.trans_le hAN
  have hQceil : Q ≤ (Nat.ceil Q : ℝ) := Nat.le_ceil Q
  have hQN : Q ≤ (N : ℝ) := by
    exact hQceil.trans (by exact_mod_cast (le_max_right A (Nat.ceil Q)))
  have hQPos : 0 < Q := zero_lt_one.trans_le hQ
  have hexpNonpos : -3 * epsilon ≤ 0 := by linarith
  have hNpow : (N : ℝ) ^ (-3 * epsilon) ≤ Q ^ (-3 * epsilon) :=
    Real.rpow_le_rpow_of_nonpos hQPos hQN hexpNonpos
  by_cases hUN : U ≤ N
  · have hUL : U ≤ L + 1 := hUN.trans hNL
    have hAbove : ∀ n ∈ Finset.Ioc L U, Q ≤ (n : ℝ) := by
      intro n hn
      have hfloorN : Nat.floor Q < n := by
        have hLn := (Finset.mem_Ioc.mp hn).1
        have : Nat.floor Q ≤ L := by
          dsimp only [L]
          exact le_max_right _ _
        omega
      exact (Nat.floor_lt (by linarith : 0 ≤ Q)).1 hfloorN |>.le
    have hboundary := norm_pintz2023ComplexWeightedBlock_boundary
      (t := t) hepsilon hxiOne hQ hAbove hUL
    calc
      ‖pintz2023ComplexWeightedBlock xi L U t‖ ≤
          Q ^ (-3 * epsilon) := hboundary
      _ ≤ (C₀ + 2) * Q ^ (-3 * epsilon) := by
        have hpow : 0 < Q ^ (-3 * epsilon) :=
          Real.rpow_pos_of_pos hQPos _
        nlinarith
  · have hNU : N < U := lt_of_not_ge hUN
    let M : ℕ := min U (2 * N)
    have hNM : N < M := by
      dsimp only [M]
      rw [lt_min_iff]
      exact ⟨hNU, by omega⟩
    have hMU : M ≤ U := by dsimp only [M]; exact min_le_left _ _
    have hMtwo : M ≤ 2 * N := by dsimp only [M]; exact min_le_right _ _
    have hTail : U ≤ M + 1 := by
      dsimp only [M]
      by_cases hUtwo : U ≤ 2 * N
      · rw [min_eq_left hUtwo]
        omega
      · rw [min_eq_right (le_of_not_ge hUtwo)]
        have htwice : 2 * A ≤ 2 * N := Nat.mul_le_mul_left 2 hAN
        omega
    have hHeadAbove : ∀ n ∈ Finset.Ioc L N, Q ≤ (n : ℝ) := by
      intro n hn
      have hfloorN : Nat.floor Q < n := by
        have hLn := (Finset.mem_Ioc.mp hn).1
        have : Nat.floor Q ≤ L := by
          dsimp only [L]
          exact le_max_right _ _
        omega
      exact (Nat.floor_lt (by linarith : 0 ≤ Q)).1 hfloorN |>.le
    have hTailAbove : ∀ n ∈ Finset.Ioc M U, Q ≤ (n : ℝ) := by
      intro n hn
      have hnN : N < n := hNM.trans_le (Finset.mem_Ioc.mp hn).1.le
      exact hQN.trans (by exact_mod_cast hnN.le)
    have hHeadBound := norm_pintz2023ComplexWeightedBlock_boundary
      (t := t) hepsilon hxiOne hQ hHeadAbove hNL
    have hTailBound := norm_pintz2023ComplexWeightedBlock_boundary
      (t := t) hepsilon hxiOne hQ hTailAbove hTail
    have hMainRaw := hcor xi N M t T hxi hden hNPos hNM hMtwo ht htT hT
      (hcritical.trans hQN) hphysical
    have hMain : ‖pintz2023ComplexWeightedBlock xi N M t‖ ≤
        C₀ * Q ^ (-3 * epsilon) :=
      hMainRaw.trans (mul_le_mul_of_nonneg_left hNpow hC₀.le)
    have hsplit :
        pintz2023ComplexWeightedBlock xi L U t =
          pintz2023ComplexWeightedBlock xi L N t +
            pintz2023ComplexWeightedBlock xi N M t +
              pintz2023ComplexWeightedBlock xi M U t := by
      calc
        pintz2023ComplexWeightedBlock xi L U t =
            pintz2023ComplexWeightedBlock xi L M t +
              pintz2023ComplexWeightedBlock xi M U t :=
          (pintz2023ComplexWeightedBlock_add xi t
            (hLN.trans hNM.le) hMU).symm
        _ = (pintz2023ComplexWeightedBlock xi L N t +
              pintz2023ComplexWeightedBlock xi N M t) +
              pintz2023ComplexWeightedBlock xi M U t := by
          rw [pintz2023ComplexWeightedBlock_add xi t hLN hNM.le]
        _ = _ := by ring
    rw [hsplit]
    calc
      ‖pintz2023ComplexWeightedBlock xi L N t +
          pintz2023ComplexWeightedBlock xi N M t +
            pintz2023ComplexWeightedBlock xi M U t‖ ≤
          ‖pintz2023ComplexWeightedBlock xi L N t‖ +
            ‖pintz2023ComplexWeightedBlock xi N M t‖ +
              ‖pintz2023ComplexWeightedBlock xi M U t‖ := by
        exact (norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ Q ^ (-3 * epsilon) + C₀ * Q ^ (-3 * epsilon) +
          Q ^ (-3 * epsilon) := by gcongr
      _ = (C₀ + 2) * Q ^ (-3 * epsilon) := by ring

#print axioms pintz2023_corollary_three_rounded

end

end GafniTao
