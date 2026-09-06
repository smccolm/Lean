import GafniTao.HeathBrownInteriorReflectedEnergy
import GafniTao.FiniteEnergyColoring

/-!
# Energy-safe smoothing of an actual sharp Type-I block

The sharp polynomial is a difference of two tails and each tail is a finite
sum of smooth source blocks.  The usual common-subfamily pigeonhole controls
cardinality only.  Here all four additive-energy coordinates are coloured by
the chosen tail side and smooth scale before a mixed-to-self comparison.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- A pointwise sharp Type-I large value selects an actual tail side and an
actual smooth source scale with the literal factor `2 * (k+1)`. -/
theorem exists_pointwise_typeISourceSmoothBlock_of_sharp_large
    (C N k : Nat) (sigma t V : Real)
    (hN : 0 < N) (hC : C ≤ 2 ^ k * N)
    (hLarge : V ≤
      ‖dirichletPoly N (classicalZetaLongLineCoeff C sigma) t‖) :
    ∃ b : Fin 2, ∃ r : Fin (k + 1),
      V / (2 * (k + 1 : Nat)) ≤
        ‖typeISourceSmoothBlock (((b : Nat) + 1) * N) C
          (r : Nat) sigma t‖ := by
  have hSingleton : ({t} : Finset Real).Nonempty := by simp
  have hSeparated : IsSeparated 1 ({t} : Finset Real) := by
    intro x hx y hy hxy
    simp only [Finset.mem_singleton] at hx hy
    exact False.elim (hxy (hx.trans hy.symm))
  have hLargeSingleton : ∀ s ∈ ({t} : Finset Real),
      V ≤ ‖dirichletPoly N (classicalZetaLongLineCoeff C sigma) s‖ := by
    intro s hs
    have hst : s = t := by simpa only [Finset.mem_singleton] using hs
    subst s
    exact hLarge
  obtain ⟨b, hb, r, hr, W', hSub, _hSep, hCard, hSmooth⟩ :=
    exists_common_typeISourceSmoothBlock_of_sharp_large
      C N k sigma V ({t} : Finset Real) hN hSingleton hC hSeparated
      hLargeSingleton
  have hW' : W'.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hEmpty
    have hCardZero : W'.card = 0 := by simp [hEmpty]
    simp only [Finset.card_singleton, hCardZero, mul_zero] at hCard
    omega
  obtain ⟨s, hs⟩ := hW'
  have hst : s = t := by simpa only [Finset.mem_singleton] using hSub hs
  subst s
  let bf : Fin 2 := ⟨b, Finset.mem_range.mp hb⟩
  let rf : Fin (k + 1) := ⟨r, Finset.mem_range.mp hr⟩
  refine ⟨bf, rf, ?_⟩
  simpa only [bf, rf] using hSmooth t hs

/-- Four-coordinate output of the sharp-to-smooth Type-I decomposition. -/
structure SharpTypeISmoothEnergyOutput
    (C N k : Nat) (sigma V : Real) (W : Finset Real) where
  side : Fin 4 → Fin 2
  scale : Fin 4 → Fin (k + 1)
  Ws : Fin 4 → Finset Real
  hSubset : ∀ i : Fin 4, Ws i ⊆ W
  hSeparated : ∀ i : Fin 4, IsSeparated 1 (Ws i)
  hLarge : ∀ i : Fin 4, ∀ t, t ∈ Ws i →
    V / (2 * (k + 1 : Nat)) ≤
      ‖typeISourceSmoothBlock (((side i : Nat) + 1) * N) C
        (scale i : Nat) sigma t‖
  hEnergy :
    4 * (ApproxAddEnergy 1 W : Real) ≤
      (((2 * (k + 1)) ^ 4 : Nat) : Real) *
        (doubleFloorDefectWindow 1).card *
        ((ApproxAddEnergy 1 (Ws 0) : Real) +
          (ApproxAddEnergy 1 (Ws 1) : Real) +
          (ApproxAddEnergy 1 (Ws 2) : Real) +
          (ApproxAddEnergy 1 (Ws 3) : Real))

/-- Exact energy-safe sharp-to-smooth decomposition. -/
theorem sharp_typeI_smooth_energy_split
    (C N k : Nat) (sigma V : Real) (W : Finset Real)
    (hN : 0 < N) (hC : C ≤ 2 ^ k * N)
    (hW : IsSeparated 1 W)
    (hLarge : ∀ t ∈ W,
      V ≤ ‖dirichletPoly N (classicalZetaLongLineCoeff C sigma) t‖) :
    Nonempty (SharpTypeISmoothEnergyOutput C N k sigma V W) := by
  classical
  have hEach : ∀ t, t ∈ W → ∃ q : Fin 2 × Fin (k + 1),
      V / (2 * (k + 1 : Nat)) ≤
        ‖typeISourceSmoothBlock (((q.1 : Nat) + 1) * N) C
          (q.2 : Nat) sigma t‖ := by
    intro t ht
    obtain ⟨b, r, hbr⟩ :=
      exists_pointwise_typeISourceSmoothBlock_of_sharp_large
        C N k sigma t V hN hC (hLarge t ht)
    exact ⟨⟨b, r⟩, hbr⟩
  let selected : Real → Fin 2 × Fin (k + 1) := fun t ↦
    if ht : t ∈ W then Classical.choose (hEach t ht) else ⟨0, 0⟩
  let color : Real → Fin (2 * (k + 1)) := fun t ↦
    finProdFinEquiv (selected t)
  obtain ⟨label, hEnergyNat⟩ := exists_real_energy_color_classes 1 W color
  let pair : Fin 4 → Fin 2 × Fin (k + 1) := fun i ↦
    finProdFinEquiv.symm (label i)
  let Ws : Fin 4 → Finset Real := fun i ↦
    W.filter (fun t ↦ color t = label i)
  have hSub : ∀ i : Fin 4, Ws i ⊆ W := fun i ↦ Finset.filter_subset _ _
  have hSep : ∀ i : Fin 4, IsSeparated 1 (Ws i) := by
    intro i x hx y hy hxy
    exact hW x (hSub i hx) y (hSub i hy) hxy
  have hSelected : ∀ i : Fin 4, ∀ t, t ∈ Ws i →
      selected t = pair i := by
    intro i t ht
    have hColor := (Finset.mem_filter.mp ht).2
    apply finProdFinEquiv.injective
    simpa only [color, pair, Equiv.apply_symm_apply] using hColor
  have hSmooth : ∀ i : Fin 4, ∀ t, t ∈ Ws i →
      V / (2 * (k + 1 : Nat)) ≤
        ‖typeISourceSmoothBlock ((((pair i).1 : Nat) + 1) * N) C
          ((pair i).2 : Nat) sigma t‖ := by
    intro i t ht
    have htW := hSub i ht
    have hChosen := Classical.choose_spec (hEach t htW)
    have hEq : Classical.choose (hEach t htW) = pair i := by
      have hSelectedAt := hSelected i t ht
      simpa only [selected, dif_pos htW] using hSelectedAt
    simpa only [hEq] using hChosen
  have hMixed := four_mul_mixedApproxAddEnergy_le_window_mul_sum_self
    (eta := 1) (W0 := Ws 0) (W1 := Ws 1) (W2 := Ws 2) (W3 := Ws 3)
    (hSep 0) (hSep 1) (hSep 2) (hSep 3)
  have hColored : (ApproxAddEnergy 1 W : Real) ≤
      (((2 * (k + 1)) ^ 4 : Nat) : Real) *
        (MixedApproxAddEnergy 1 (Ws 0) (Ws 1) (Ws 2) (Ws 3) : Real) := by
    have hEnergyNat' : ApproxAddEnergy 1 W ≤
        (2 * (k + 1)) ^ 4 *
          MixedApproxAddEnergy 1 (Ws 0) (Ws 1) (Ws 2) (Ws 3) := by
      simpa only [Fintype.card_fin, Ws] using hEnergyNat
    exact_mod_cast hEnergyNat'
  have hFinal : 4 * (ApproxAddEnergy 1 W : Real) ≤
      (((2 * (k + 1)) ^ 4 : Nat) : Real) *
        (doubleFloorDefectWindow 1).card *
        ((ApproxAddEnergy 1 (Ws 0) : Real) +
          (ApproxAddEnergy 1 (Ws 1) : Real) +
          (ApproxAddEnergy 1 (Ws 2) : Real) +
          (ApproxAddEnergy 1 (Ws 3) : Real)) := by
    calc
      4 * (ApproxAddEnergy 1 W : Real) ≤
          (((2 * (k + 1)) ^ 4 : Nat) : Real) *
            (4 * (MixedApproxAddEnergy 1
              (Ws 0) (Ws 1) (Ws 2) (Ws 3) : Real)) := by
        nlinarith [hColored]
      _ ≤ (((2 * (k + 1)) ^ 4 : Nat) : Real) *
          ((doubleFloorDefectWindow 1).card *
            ((ApproxAddEnergy 1 (Ws 0) : Real) +
              (ApproxAddEnergy 1 (Ws 1) : Real) +
              (ApproxAddEnergy 1 (Ws 2) : Real) +
              (ApproxAddEnergy 1 (Ws 3) : Real))) := by
        gcongr
      _ = (((2 * (k + 1)) ^ 4 : Nat) : Real) *
          (doubleFloorDefectWindow 1).card *
          ((ApproxAddEnergy 1 (Ws 0) : Real) +
            (ApproxAddEnergy 1 (Ws 1) : Real) +
            (ApproxAddEnergy 1 (Ws 2) : Real) +
            (ApproxAddEnergy 1 (Ws 3) : Real)) := by ring
  exact ⟨⟨fun i ↦ (pair i).1, fun i ↦ (pair i).2, Ws,
    hSub, hSep, hSmooth, hFinal⟩⟩

#print axioms exists_pointwise_typeISourceSmoothBlock_of_sharp_large
#print axioms SharpTypeISmoothEnergyOutput
#print axioms sharp_typeI_smooth_energy_split

end

end GafniTao
