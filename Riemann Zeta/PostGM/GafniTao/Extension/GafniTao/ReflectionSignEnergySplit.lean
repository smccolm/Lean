import GafniTao.ShiftedWideEnergyToSelf

/-!
# Energy-preserving split of the two Poisson-reflection signs

A cardinality pigeonhole is not valid for four-coordinate additive energy.
This module colours every coordinate of every source quadruple by its chosen
reflection sign and only then applies the exact mixed-to-self comparison.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Exact sign split for a family carrying a pointwise negative-or-positive
alternative.  Each selected self family has one common sign, and the full
energy loss is the literal `2^4` colour loss followed by the tolerance-one
doubled-floor window. -/
theorem reflection_sign_energy_split
    (W : Finset Real) (hW : IsSeparated 1 W)
    (negative positive : Real → Prop)
    (hEach : ∀ t, t ∈ W → negative t ∨ positive t) :
    ∃ sign : Fin 4 → Fin 2, ∃ Ws : Fin 4 → Finset Real,
      (∀ i : Fin 4, Ws i ⊆ W) ∧
      (∀ i : Fin 4, IsSeparated 1 (Ws i)) ∧
      (∀ i : Fin 4, ∀ t, t ∈ Ws i →
        (sign i = 0 → negative t) ∧ (sign i = 1 → positive t)) ∧
      4 * (ApproxAddEnergy 1 W : Real) ≤
        16 * (doubleFloorDefectWindow 1).card *
          ((ApproxAddEnergy 1 (Ws 0) : Real) +
            (ApproxAddEnergy 1 (Ws 1) : Real) +
            (ApproxAddEnergy 1 (Ws 2) : Real) +
            (ApproxAddEnergy 1 (Ws 3) : Real)) := by
  classical
  let isNegative : Real → Prop := negative
  let color : Real → Fin 2 := fun t => if isNegative t then 0 else 1
  obtain ⟨sign, hEnergyNat⟩ := exists_real_energy_color_classes 1 W color
  let Ws := fun i : Fin 4 => W.filter (fun t => color t = sign i)
  have hSub : ∀ i : Fin 4, Ws i ⊆ W := fun i => Finset.filter_subset _ _
  have hSep : ∀ i : Fin 4, IsSeparated 1 (Ws i) := by
    intro i x hx y hy hxy
    exact hW x (hSub i hx) y (hSub i hy) hxy
  have hSign : ∀ i : Fin 4, ∀ t, t ∈ Ws i →
      (sign i = 0 → negative t) ∧ (sign i = 1 → positive t) := by
    intro i t ht
    have htData := Finset.mem_filter.mp ht
    have hcolor := htData.2
    constructor
    · intro hi
      have hc0 : color t = 0 := hcolor.trans hi
      by_contra hn
      simp only [color, isNegative, if_neg hn] at hc0
      exact Fin.zero_ne_one hc0.symm
    · intro hi
      have hc1 : color t = 1 := hcolor.trans hi
      by_cases hn : negative t
      · simp only [color, isNegative, if_pos hn] at hc1
        exact False.elim (Fin.zero_ne_one hc1)
      · rcases hEach t htData.1 with hneg | hpos
        · exact False.elim (hn hneg)
        · exact hpos
  have hMixed := four_mul_mixedApproxAddEnergy_le_window_mul_sum_self
    (eta := 1) (W0 := Ws 0) (W1 := Ws 1) (W2 := Ws 2) (W3 := Ws 3)
    (hSep 0) (hSep 1) (hSep 2) (hSep 3)
  have hEnergy : (ApproxAddEnergy 1 W : Real) ≤
      16 * (MixedApproxAddEnergy 1 (Ws 0) (Ws 1) (Ws 2) (Ws 3) : Real) := by
    have hCast : (ApproxAddEnergy 1 W : Real) ≤
        (((Fintype.card (Fin 2)) ^ 4 : Nat) : Real) *
          (MixedApproxAddEnergy 1 (Ws 0) (Ws 1) (Ws 2) (Ws 3) : Real) := by
      exact_mod_cast hEnergyNat
    norm_num at hCast ⊢
    exact hCast
  refine ⟨sign, Ws, hSub, hSep, hSign, ?_⟩
  calc
    4 * (ApproxAddEnergy 1 W : Real) ≤
        16 * (4 * (MixedApproxAddEnergy 1
          (Ws 0) (Ws 1) (Ws 2) (Ws 3) : Real)) := by
      nlinarith [hEnergy]
    _ ≤ 16 * ((doubleFloorDefectWindow 1).card *
        ((ApproxAddEnergy 1 (Ws 0) : Real) +
          (ApproxAddEnergy 1 (Ws 1) : Real) +
          (ApproxAddEnergy 1 (Ws 2) : Real) +
          (ApproxAddEnergy 1 (Ws 3) : Real))) := by
      gcongr
    _ = 16 * (doubleFloorDefectWindow 1).card *
        ((ApproxAddEnergy 1 (Ws 0) : Real) +
          (ApproxAddEnergy 1 (Ws 1) : Real) +
          (ApproxAddEnergy 1 (Ws 2) : Real) +
          (ApproxAddEnergy 1 (Ws 3) : Real)) := by ring

#print axioms reflection_sign_energy_split

end

end GafniTao
