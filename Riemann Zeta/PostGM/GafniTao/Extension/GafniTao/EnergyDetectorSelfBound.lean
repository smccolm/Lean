import GafniTao.EnergyDetectorExtraction
import GafniTao.RealEnergyDiscretization

/-!
# Multiplicity-weighted zero energy reduced to four self energies

This is the complete finite consumer of the detector extraction and the
mixed-energy discretization.  It retains the actual four selected scales and
all displacement, local-multiplicity, color, and defect-window losses.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

theorem finite_shifted_dyadic_zero_energy_to_self_energies
    (sigma T H : Real) (k L : Nat) (hk : 0 < k)
    (large : Fin k → Real → Prop) (inInterval : Real → Prop)
    (hEach : ∀ rho, rho ∈ zeroSet sigma T →
      ∃ t : Real, |rho.im - t| ≤ H ∧ inInterval t ∧
        ∃ r : Fin k, large r t)
    (hLocal : ∀ z : Int,
      (∑ rho ∈ (zeroSet sigma T).filter
        (fun y => (z : Real) ≤ y.im ∧ y.im < (z : Real) + 1),
        zeroMultiplicity rho) ≤ L) :
    ∃ label : Fin 4 → (Fin k × Fin 2),
      let shift : Complex → Real := fun rho =>
        if h : rho ∈ zeroSet sigma T then Classical.choose (hEach rho h)
        else rho.im
      let scale : Complex → Fin k := fun rho =>
        if h : rho ∈ zeroSet sigma T then
          Classical.choose (Classical.choose_spec (hEach rho h)).2.2
        else ⟨0, hk⟩
      let representative :=
        detectorRepresentative (zeroSet sigma T) scale shift
      let W := fun i : Fin 4 =>
        ((zeroSet sigma T).filter
          (fun rho => detectorColor scale shift rho = label i)).image
            representative
      (∀ i : Fin 4, IsSeparated 1 (W i)) ∧
      (∀ i : Fin 4, ∀ t, t ∈ W i → large (label i).1 t) ∧
      (∀ i : Fin 4, ∀ t, t ∈ W i → inInterval t) ∧
      4 * (zeroAdditiveEnergyCount sigma T : Real) ≤
        (((2 * k) ^ 4 * ((2 * ⌈H + 1⌉₊ + 1) * L) ^ 4 : Nat) : Real) *
          (doubleFloorDefectWindow (1 + 4 * (H + 1))).card *
            ((ApproxAddEnergy 1 (W 0) : Real) +
              (ApproxAddEnergy 1 (W 1) : Real) +
              (ApproxAddEnergy 1 (W 2) : Real) +
              (ApproxAddEnergy 1 (W 3) : Real)) := by
  classical
  obtain ⟨label, hSep, hLarge, hInterval, hEnergy⟩ :=
    finite_shifted_dyadic_energy_extraction sigma T H k L hk large
      inInterval hEach hLocal
  refine ⟨label, ?_⟩
  dsimp only
  refine ⟨hSep, hLarge, hInterval, ?_⟩
  let shift : Complex → Real := fun rho =>
    if h : rho ∈ zeroSet sigma T then Classical.choose (hEach rho h)
    else rho.im
  let scale : Complex → Fin k := fun rho =>
    if h : rho ∈ zeroSet sigma T then
      Classical.choose (Classical.choose_spec (hEach rho h)).2.2
    else ⟨0, hk⟩
  let representative :=
    detectorRepresentative (zeroSet sigma T) scale shift
  let W := fun i : Fin 4 =>
    ((zeroSet sigma T).filter
      (fun rho => detectorColor scale shift rho = label i)).image
        representative
  let P : Nat := (2 * k) ^ 4 * ((2 * ⌈H + 1⌉₊ + 1) * L) ^ 4
  let M : Nat := MixedApproxAddEnergy (1 + 4 * (H + 1))
    (W 0) (W 1) (W 2) (W 3)
  let S : Real :=
    (ApproxAddEnergy 1 (W 0) : Real) +
      (ApproxAddEnergy 1 (W 1) : Real) +
      (ApproxAddEnergy 1 (W 2) : Real) +
      (ApproxAddEnergy 1 (W 3) : Real)
  have hEnergyReal : (zeroAdditiveEnergyCount sigma T : Real) ≤
      (P : Real) * (M : Real) := by
    exact_mod_cast hEnergy
  have hMixed : 4 * (M : Real) ≤
      (doubleFloorDefectWindow (1 + 4 * (H + 1))).card * S := by
    simpa only [M, S] using
      four_mul_mixedApproxAddEnergy_le_window_mul_sum_self
        (hSep 0) (hSep 1) (hSep 2) (hSep 3)
  change 4 * (zeroAdditiveEnergyCount sigma T : Real) ≤
    (P : Real) *
      (doubleFloorDefectWindow (1 + 4 * (H + 1))).card * S
  calc
    4 * (zeroAdditiveEnergyCount sigma T : Real) ≤
        4 * ((P : Real) * (M : Real)) := by gcongr
    _ = (P : Real) * (4 * (M : Real)) := by ring
    _ ≤ (P : Real) *
        ((doubleFloorDefectWindow (1 + 4 * (H + 1))).card * S) := by
      gcongr
    _ = (P : Real) *
        (doubleFloorDefectWindow (1 + 4 * (H + 1))).card * S := by ring

#print axioms finite_shifted_dyadic_zero_energy_to_self_energies

end

end GafniTao
