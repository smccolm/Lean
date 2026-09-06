import GafniTao.ClassicalBinaryLongTailFamily
import GafniTao.RealEnergyPowerColoring
import GafniTao.RealEnergyDiscretization

/-!
# Energy-safe source classification of the retained zeta long tail

The frozen endpoint proof selects one common source scale by cardinality.
Here the same exact source decomposition is applied pointwise and the four
additive-energy coordinates are coloured before a mixed-to-self reduction.
Thus no cardinality-only selection is substituted for a four-zero estimate.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- A single long-tail large value selects an actual classified smooth source
block, with the literal `k+1` loss from the frozen decomposition. -/
theorem exists_pointwise_classified_source_of_longTail_large
    (Y A k : Nat) (sigma V t : Real)
    (hY : 1 ≤ Y) (hA : A ≤ 2 ^ k * Y)
    (hLarge : V ≤
      ‖classicalZetaLongTail Y A
        ((sigma : Complex) + Complex.I * (t : Complex))‖) :
    ∃ r : Fin (k + 1),
      V / (k + 1 : Nat) ≤ ‖typeISourceSmoothBlock Y A r.val sigma t‖ ∧
      (r.val < 2 ∨ A < 2 * (2 ^ r.val * Y) ∨
        (((Y + 1 : Nat) : Real) ≤ ((2 ^ r.val * Y : Nat) : Real) / 2 ∧
          2 * (2 ^ r.val * Y) ≤ A)) := by
  have hSingleton : ({t} : Finset Real).Nonempty := by simp
  have hSeparated : IsSeparated 1 ({t} : Finset Real) := by
    intro x hx y hy hxy
    simp only [Finset.mem_singleton] at hx hy
    exact False.elim (hxy (hx.trans hy.symm))
  have hLargeSingleton : ∀ s ∈ ({t} : Finset Real),
      V ≤ ‖classicalZetaLongTail Y A
        ((sigma : Complex) + Complex.I * (s : Complex))‖ := by
    intro s hs
    have hst : s = t := by simpa only [Finset.mem_singleton] using hs
    simpa only [hst] using hLarge
  obtain ⟨r, hr, W', hSub, _hSep, hCard, hBlock, hClass⟩ :=
    extract_common_typeISourceSmoothBlock_classified
      ({t} : Finset Real) hY hA hSingleton hSeparated hLargeSingleton
  have hW' : W'.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hEmpty
    have hCardZero : W'.card = 0 := by simp [hEmpty]
    simp only [Finset.card_singleton, hCardZero, mul_zero] at hCard
    omega
  obtain ⟨s, hs⟩ := hW'
  have hst : s = t := by simpa only [Finset.mem_singleton] using hSub hs
  subst s
  let rf : Fin (k + 1) := ⟨r, Finset.mem_range.mp hr⟩
  exact ⟨rf, by simpa only [rf] using hBlock t hs,
    by simpa only [rf] using hClass⟩

/-- Four-coordinate output of the retained-long-tail source decomposition. -/
structure LongTailSourceEnergyOutput
    (Y A k : Nat) (sigma V : Real) (W : Finset Real) where
  scale : Fin 4 → Fin (k + 1)
  Ws : Fin 4 → Finset Real
  hSubset : ∀ i : Fin 4, Ws i ⊆ W
  hSeparated : ∀ i : Fin 4, IsSeparated 1 (Ws i)
  hLarge : ∀ i : Fin 4, ∀ t, t ∈ Ws i →
    V / (k + 1 : Nat) ≤
      ‖typeISourceSmoothBlock Y A (scale i).val sigma t‖
  hClassified : ∀ i : Fin 4,
    (scale i).val < 2 ∨ A < 2 * (2 ^ (scale i).val * Y) ∨
      (((Y + 1 : Nat) : Real) ≤
          ((2 ^ (scale i).val * Y : Nat) : Real) / 2 ∧
        2 * (2 ^ (scale i).val * Y) ≤ A)
  hEnergy :
    4 * (ApproxAddEnergy 1 W : Real) ≤
      (((k + 1) ^ 4 : Nat) : Real) *
        (doubleFloorDefectWindow 1).card *
        ((ApproxAddEnergy 1 (Ws 0) : Real) +
          (ApproxAddEnergy 1 (Ws 1) : Real) +
          (ApproxAddEnergy 1 (Ws 2) : Real) +
          (ApproxAddEnergy 1 (Ws 3) : Real))

/-- Exact energy-safe smooth-source classification of a whole retained
long-tail family. -/
theorem longTail_source_energy_split
    (Y A k : Nat) (sigma V : Real) (W : Finset Real)
    (hY : 1 ≤ Y) (hA : A ≤ 2 ^ k * Y)
    (hW : IsSeparated 1 W)
    (hLarge : ∀ t ∈ W,
      V ≤ ‖classicalZetaLongTail Y A
        ((sigma : Complex) + Complex.I * (t : Complex))‖) :
    Nonempty (LongTailSourceEnergyOutput Y A k sigma V W) := by
  classical
  have hEach : ∀ t, t ∈ W → ∃ r : Fin (k + 1),
      V / (k + 1 : Nat) ≤
          ‖typeISourceSmoothBlock Y A r.val sigma t‖ ∧
        (r.val < 2 ∨ A < 2 * (2 ^ r.val * Y) ∨
          (((Y + 1 : Nat) : Real) ≤ ((2 ^ r.val * Y : Nat) : Real) / 2 ∧
            2 * (2 ^ r.val * Y) ≤ A)) := by
    intro t ht
    exact exists_pointwise_classified_source_of_longTail_large
      Y A k sigma V t hY hA (hLarge t ht)
  let selected : Real → Fin (k + 1) := fun t ↦
    if ht : t ∈ W then Classical.choose (hEach t ht) else 0
  obtain ⟨label, hEnergyNat⟩ :=
    exists_real_energy_color_classes 1 W selected
  let scale : Fin 4 → Fin (k + 1) := label
  let Ws : Fin 4 → Finset Real := fun i ↦
    W.filter (fun t ↦ selected t = scale i)
  have hSub : ∀ i : Fin 4, Ws i ⊆ W := fun i ↦ Finset.filter_subset _ _
  have hSep : ∀ i : Fin 4, IsSeparated 1 (Ws i) := by
    intro i x hx y hy hxy
    exact hW x (hSub i hx) y (hSub i hy) hxy
  have hSelected : ∀ i : Fin 4, ∀ t, t ∈ Ws i → selected t = scale i := by
    intro i t ht
    exact (Finset.mem_filter.mp ht).2
  have hBlock : ∀ i : Fin 4, ∀ t, t ∈ Ws i →
      V / (k + 1 : Nat) ≤
        ‖typeISourceSmoothBlock Y A (scale i).val sigma t‖ := by
    intro i t ht
    have htW := hSub i ht
    have hChosen := Classical.choose_spec (hEach t htW)
    have hEq : Classical.choose (hEach t htW) = scale i := by
      simpa only [selected, dif_pos htW] using hSelected i t ht
    simpa only [hEq] using hChosen.1
  have hClass : ∀ i : Fin 4,
      (scale i).val < 2 ∨ A < 2 * (2 ^ (scale i).val * Y) ∨
        (((Y + 1 : Nat) : Real) ≤
            ((2 ^ (scale i).val * Y : Nat) : Real) / 2 ∧
          2 * (2 ^ (scale i).val * Y) ≤ A) := by
    intro i
    by_cases hWi : (Ws i).Nonempty
    · obtain ⟨t, ht⟩ := hWi
      have htW := hSub i ht
      have hChosen := Classical.choose_spec (hEach t htW)
      have hEq : Classical.choose (hEach t htW) = scale i := by
        simpa only [selected, dif_pos htW] using hSelected i t ht
      simpa only [hEq] using hChosen.2
    · have hDefault := typeISourceSmoothScale_lower_terminal_or_interior
        (A := A) (r := (scale i).val) hY
      exact hDefault
  have hMixed := four_mul_mixedApproxAddEnergy_le_window_mul_sum_self
    (eta := 1) (W0 := Ws 0) (W1 := Ws 1) (W2 := Ws 2) (W3 := Ws 3)
    (hSep 0) (hSep 1) (hSep 2) (hSep 3)
  have hColored : (ApproxAddEnergy 1 W : Real) ≤
      (((k + 1) ^ 4 : Nat) : Real) *
        (MixedApproxAddEnergy 1 (Ws 0) (Ws 1) (Ws 2) (Ws 3) : Real) := by
    have hEnergyNat' : ApproxAddEnergy 1 W ≤
        (k + 1) ^ 4 *
          MixedApproxAddEnergy 1 (Ws 0) (Ws 1) (Ws 2) (Ws 3) := by
      simpa only [Fintype.card_fin, Ws, scale] using hEnergyNat
    exact_mod_cast hEnergyNat'
  have hFinal : 4 * (ApproxAddEnergy 1 W : Real) ≤
      (((k + 1) ^ 4 : Nat) : Real) *
        (doubleFloorDefectWindow 1).card *
        ((ApproxAddEnergy 1 (Ws 0) : Real) +
          (ApproxAddEnergy 1 (Ws 1) : Real) +
          (ApproxAddEnergy 1 (Ws 2) : Real) +
          (ApproxAddEnergy 1 (Ws 3) : Real)) := by
    calc
      4 * (ApproxAddEnergy 1 W : Real) ≤
          (((k + 1) ^ 4 : Nat) : Real) *
            (4 * (MixedApproxAddEnergy 1
              (Ws 0) (Ws 1) (Ws 2) (Ws 3) : Real)) := by
        nlinarith [hColored]
      _ ≤ (((k + 1) ^ 4 : Nat) : Real) *
          ((doubleFloorDefectWindow 1).card *
            ((ApproxAddEnergy 1 (Ws 0) : Real) +
              (ApproxAddEnergy 1 (Ws 1) : Real) +
              (ApproxAddEnergy 1 (Ws 2) : Real) +
              (ApproxAddEnergy 1 (Ws 3) : Real))) := by
        gcongr
      _ = (((k + 1) ^ 4 : Nat) : Real) *
          (doubleFloorDefectWindow 1).card *
          ((ApproxAddEnergy 1 (Ws 0) : Real) +
            (ApproxAddEnergy 1 (Ws 1) : Real) +
            (ApproxAddEnergy 1 (Ws 2) : Real) +
            (ApproxAddEnergy 1 (Ws 3) : Real)) := by ring
  exact ⟨⟨scale, Ws, hSub, hSep, hBlock, hClass, hFinal⟩⟩

#print axioms exists_pointwise_classified_source_of_longTail_large
#print axioms LongTailSourceEnergyOutput
#print axioms longTail_source_energy_split

end

end GafniTao
