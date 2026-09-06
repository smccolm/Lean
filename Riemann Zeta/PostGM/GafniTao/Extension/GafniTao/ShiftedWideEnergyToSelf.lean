import GafniTao.RealShiftedDyadicEnergyExtraction

/-!
# Shifted wide-polynomial energy reduced to dyadic self energies

This module performs the exact two finite reductions needed after a common
Poisson-reflection sign has been fixed: simultaneous dyadic/parity extraction
on all four coordinates, followed by the doubled-floor mixed-to-self bound.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- A common-sign family on which a wide polynomial is large is reduced to
four one-separated dyadic families.  The displayed coefficient is the full
dyadic/parity/fibre/defect-window loss. -/
theorem shifted_wide_energy_to_dyadic_self
    (W : Finset Real) (hW : IsSeparated 1 W)
    (H S R : Real) (k : Nat) (hk : 0 < k)
    (a : Nat → Complex)
    (hEach : ∀ x, x ∈ W → ∃ t : Real,
      |x - t| ≤ H ∧ (-R ≤ t ∧ t ≤ R) ∧
        S ≤ ‖wideDirichletPoly 1 k a t‖) :
    ∃ r : Fin 4 → Fin k, ∃ U : Fin 4 → Finset Real,
      (∀ i : Fin 4, IsSeparated 1 (U i)) ∧
      (∀ i : Fin 4, ∀ t, t ∈ U i → -R ≤ t ∧ t ≤ R) ∧
      (∀ i : Fin 4, ∀ t, t ∈ U i →
        S / k ≤ ‖dirichletPoly (2 ^ (r i : Nat)) a t‖) ∧
      4 * (ApproxAddEnergy 1 W : Real) ≤
        ((2 * k : Nat) : Real) ^ 4 *
          ((2 * ⌈H + 1⌉₊ + 1 : Nat) : Real) ^ 4 *
          (doubleFloorDefectWindow (1 + 4 * (H + 1))).card *
          ((ApproxAddEnergy 1 (U 0) : Real) +
            (ApproxAddEnergy 1 (U 1) : Real) +
            (ApproxAddEnergy 1 (U 2) : Real) +
            (ApproxAddEnergy 1 (U 3) : Real)) := by
  let large : Fin k → Real → Prop := fun r t =>
    S / k ≤ ‖dirichletPoly (2 ^ (r : Nat)) a t‖
  let inInterval : Real → Prop := fun t => -R ≤ t ∧ t ≤ R
  have hDyadic : ∀ x, x ∈ W → ∃ t : Real,
      |x - t| ≤ H ∧ inInterval t ∧ ∃ r : Fin k, large r t := by
    intro x hx
    obtain ⟨t, hxt, htRange, htLarge⟩ := hEach x hx
    obtain ⟨j, hj, hjLarge⟩ :=
      exists_large_dyadic_block 1 k a t S hk htLarge
    let r : Fin k := ⟨j, Finset.mem_range.mp hj⟩
    exact ⟨t, hxt, htRange, r,
      by simpa only [large, r, Nat.mul_one] using hjLarge⟩
  obtain ⟨label, hSep, hLarge, hRange, hEnergyNat⟩ :=
    finite_shifted_dyadic_real_energy_extraction W hW 1 H k hk
      large inInterval hDyadic
  let shift : Real → Real := fun x =>
    if h : x ∈ W then Classical.choose (hDyadic x h) else x
  let scale : Real → Fin k := fun x =>
    if h : x ∈ W then
      Classical.choose (Classical.choose_spec (hDyadic x h)).2.2
    else ⟨0, hk⟩
  let representative := detectorRepresentative W scale shift
  let U := fun i : Fin 4 =>
    (W.filter (fun x => detectorColor scale shift x = label i)).image
      representative
  let r : Fin 4 → Fin k := fun i => (label i).1
  have hMixed := four_mul_mixedApproxAddEnergy_le_window_mul_sum_self
    (eta := 1 + 4 * (H + 1))
    (W0 := U 0) (W1 := U 1) (W2 := U 2) (W3 := U 3)
    (hSep 0) (hSep 1) (hSep 2) (hSep 3)
  have hEnergy : (ApproxAddEnergy 1 W : Real) ≤
      (((2 * k) ^ 4 * (2 * ⌈H + 1⌉₊ + 1) ^ 4 : Nat) : Real) *
        (MixedApproxAddEnergy (1 + 4 * (H + 1))
          (U 0) (U 1) (U 2) (U 3) : Real) := by
    exact_mod_cast hEnergyNat
  refine ⟨r, U, hSep, ?_, ?_, ?_⟩
  · exact hRange
  · exact hLarge
  · calc
      4 * (ApproxAddEnergy 1 W : Real) ≤
          (((2 * k) ^ 4 * (2 * ⌈H + 1⌉₊ + 1) ^ 4 : Nat) : Real) *
            (4 * (MixedApproxAddEnergy (1 + 4 * (H + 1))
              (U 0) (U 1) (U 2) (U 3) : Real)) := by
        nlinarith [hEnergy]
      _ ≤ (((2 * k) ^ 4 * (2 * ⌈H + 1⌉₊ + 1) ^ 4 : Nat) : Real) *
          ((doubleFloorDefectWindow (1 + 4 * (H + 1))).card *
            ((ApproxAddEnergy 1 (U 0) : Real) +
              (ApproxAddEnergy 1 (U 1) : Real) +
              (ApproxAddEnergy 1 (U 2) : Real) +
              (ApproxAddEnergy 1 (U 3) : Real))) := by
        gcongr
      _ = ((2 * k : Nat) : Real) ^ 4 *
          ((2 * ⌈H + 1⌉₊ + 1 : Nat) : Real) ^ 4 *
          (doubleFloorDefectWindow (1 + 4 * (H + 1))).card *
          ((ApproxAddEnergy 1 (U 0) : Real) +
            (ApproxAddEnergy 1 (U 1) : Real) +
            (ApproxAddEnergy 1 (U 2) : Real) +
            (ApproxAddEnergy 1 (U 3) : Real)) := by
        push_cast
        ring

#print axioms shifted_wide_energy_to_dyadic_self

end

end GafniTao
