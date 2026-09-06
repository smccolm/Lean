import GafniTao.EnergyDetectorSelfBound
import RiemannZeta.GuthMaynard.LargeValuesEnergyFinal

/-!
# The four-colour zero detector consumed by Guth--Maynard Proposition 11.1

This file joins the multiplicity-preserving four-zero extraction to the
actual native Proposition 11.1.  The four detector colours may select four
different dyadic scales; all four scales remain visible in the conclusion.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The three-term physical bound in Guth--Maynard Proposition 11.1. -/
noncomputable def gmEnergyShape
    (sigma T : Real) (N : Nat) (W : Finset Real) : Real :=
  (W.card : Real) * (N : Real) ^ (4 - 4 * sigma) +
    (W.card : Real) ^ (21 / 8 : Real) * T ^ (1 / 4 : Real) *
      (N : Real) ^ (1 - 2 * sigma) +
    (W.card : Real) ^ 3 * (N : Real) ^ (1 - 2 * sigma)

theorem gmEnergyShape_nonneg
    (sigma T : Real) (N : Nat) (W : Finset Real) (hT : 0 <= T) :
    0 <= gmEnergyShape sigma T N W := by
  unfold gmEnergyShape
  have h0 : 0 <= (W.card : Real) := by positivity
  have hN0 : 0 <= (N : Real) := by positivity
  have hTpow : 0 <= T ^ (1 / 4 : Real) := Real.rpow_nonneg hT _
  have hA : 0 <= (W.card : Real) * (N : Real) ^ (4 - 4 * sigma) :=
    mul_nonneg h0 (Real.rpow_nonneg hN0 _)
  have hB : 0 <= (W.card : Real) ^ (21 / 8 : Real) * T ^ (1 / 4 : Real) *
      (N : Real) ^ (1 - 2 * sigma) := by positivity
  have hC : 0 <= (W.card : Real) ^ 3 * (N : Real) ^ (1 - 2 * sigma) := by
    positivity
  linarith

/-- Exact finite composition of the four-colour zero detector with the
native Guth--Maynard energy estimate.  This is the source-entry bridge needed
before exponent optimization: it consumes the real zero set, analytic
multiplicities, shifted representatives, coefficient bounds, and the actual
large-value inequalities at each of the four selected scales. -/
theorem finite_shifted_dyadic_zero_energy_gm_bound
    (epsilon sigma T B H : Real) (k L : Nat) (hk : 0 < k)
    (N : Fin k -> Nat) (b : Fin k -> Nat -> Complex)
    (hepsilon : 0 < epsilon)
    (hNpos : forall r, 0 < N r)
    (hNB : forall r, (N r : Real) <= B)
    (hNlower : forall r, B ^ (3 / 4 : Real) <= (N r : Real))
    (hCoeff : forall r n, n ∈ dyadicInterval (N r) -> ‖b r n‖ <= 1)
    (hEach : forall rho, rho ∈ zeroSet sigma T ->
      exists t : Real, |rho.im - t| <= H /\
        (0 <= t /\ t <= B) /\
        exists r : Fin k,
          (N r : Real) ^ sigma <= ‖sourceDirichletPoly (N r) (b r) t‖)
    (hLocal : forall z : Int,
      (∑ rho ∈ (zeroSet sigma T).filter
        (fun y => (z : Real) <= y.im /\ y.im < (z : Real) + 1),
        zeroMultiplicity rho) <= L) :
    exists C B0 : Real, 0 < C /\ 4 <= B0 /\
      (B0 <= B ->
      exists label : Fin 4 -> (Fin k × Fin 2),
        let shift : Complex -> Real := fun rho =>
          if h : rho ∈ zeroSet sigma T then Classical.choose (hEach rho h)
          else rho.im
        let scale : Complex -> Fin k := fun rho =>
          if h : rho ∈ zeroSet sigma T then
            Classical.choose (Classical.choose_spec (hEach rho h)).2.2
          else ⟨0, hk⟩
        let representative := detectorRepresentative (zeroSet sigma T) scale shift
        let W := fun i : Fin 4 =>
          ((zeroSet sigma T).filter
            (fun rho => detectorColor scale shift rho = label i)).image representative
        (forall i : Fin 4, IsSeparated 1 (W i)) /\
        (forall i : Fin 4, forall t, t ∈ W i ->
          (N (label i).1 : Real) ^ sigma <=
            ‖sourceDirichletPoly (N (label i).1) (b (label i).1) t‖) /\
        (forall i : Fin 4, InBaseInterval B (W i)) /\
        4 * (zeroAdditiveEnergyCount sigma T : Real) <=
          (((2 * k) ^ 4 * ((2 * ⌈H + 1⌉₊ + 1) * L) ^ 4 : Nat) : Real) *
            (doubleFloorDefectWindow (1 + 4 * (H + 1))).card *
              (C * B ^ epsilon *
                (gmEnergyShape sigma B (N (label 0).1) (W 0) +
                  gmEnergyShape sigma B (N (label 1).1) (W 1) +
                  gmEnergyShape sigma B (N (label 2).1) (W 2) +
                  gmEnergyShape sigma B (N (label 3).1) (W 3)))) := by
  obtain ⟨C, B0, hC, hB0, hGM⟩ := gmEnergy_prop11_1_native epsilon hepsilon
  refine ⟨C, B0, hC, hB0, ?_⟩
  intro hB
  let large : Fin k -> Real -> Prop := fun r t =>
    (N r : Real) ^ sigma <= ‖sourceDirichletPoly (N r) (b r) t‖
  let inInterval : Real -> Prop := fun t => 0 <= t /\ t <= B
  obtain ⟨label, hSep, hLarge, hInterval, hEnergy⟩ :=
    finite_shifted_dyadic_zero_energy_to_self_energies
      sigma T H k L hk large inInterval hEach hLocal
  refine ⟨label, ?_⟩
  dsimp only
  refine ⟨hSep, hLarge, ?_, ?_⟩
  · intro i t ht
    exact hInterval i t ht
  · let shift : Complex -> Real := fun rho =>
      if h : rho ∈ zeroSet sigma T then Classical.choose (hEach rho h)
      else rho.im
    let scale : Complex -> Fin k := fun rho =>
      if h : rho ∈ zeroSet sigma T then
        Classical.choose (Classical.choose_spec (hEach rho h)).2.2
      else ⟨0, hk⟩
    let representative := detectorRepresentative (zeroSet sigma T) scale shift
    let W := fun i : Fin 4 =>
      ((zeroSet sigma T).filter
        (fun rho => detectorColor scale shift rho = label i)).image representative
    let P : Real :=
      (((2 * k) ^ 4 * ((2 * ⌈H + 1⌉₊ + 1) * L) ^ 4 : Nat) : Real) *
        (doubleFloorDefectWindow (1 + 4 * (H + 1))).card
    let S : Real :=
      gmEnergyShape sigma B (N (label 0).1) (W 0) +
        gmEnergyShape sigma B (N (label 1).1) (W 1) +
        gmEnergyShape sigma B (N (label 2).1) (W 2) +
        gmEnergyShape sigma B (N (label 3).1) (W 3)
    have hWi : forall i : Fin 4,
        (ApproxAddEnergy 1 (W i) : Real) <=
          C * B ^ epsilon * gmEnergyShape sigma B (N (label i).1) (W i) := by
      intro i
      exact hGM (N (label i).1) B sigma (W i) (b (label i).1)
        (hNpos _) hB (hNB _) (hNlower _) (hSep i) (hInterval i)
        (hCoeff _) (hLarge i)
    have hSum :
        (ApproxAddEnergy 1 (W 0) : Real) +
            (ApproxAddEnergy 1 (W 1) : Real) +
            (ApproxAddEnergy 1 (W 2) : Real) +
            (ApproxAddEnergy 1 (W 3) : Real) <=
          C * B ^ epsilon * S := by
      calc
        _ <= C * B ^ epsilon * gmEnergyShape sigma B (N (label 0).1) (W 0) +
            C * B ^ epsilon * gmEnergyShape sigma B (N (label 1).1) (W 1) +
            C * B ^ epsilon * gmEnergyShape sigma B (N (label 2).1) (W 2) +
            C * B ^ epsilon * gmEnergyShape sigma B (N (label 3).1) (W 3) := by
              gcongr <;> apply hWi
        _ = C * B ^ epsilon * S := by
          dsimp only [S]
          ring
    change 4 * (zeroAdditiveEnergyCount sigma T : Real) <= P *
      ((ApproxAddEnergy 1 (W 0) : Real) +
        (ApproxAddEnergy 1 (W 1) : Real) +
        (ApproxAddEnergy 1 (W 2) : Real) +
        (ApproxAddEnergy 1 (W 3) : Real)) at hEnergy
    change 4 * (zeroAdditiveEnergyCount sigma T : Real) <=
      P * (C * B ^ epsilon * S)
    exact hEnergy.trans (mul_le_mul_of_nonneg_left hSum (by
      dsimp only [P]
      positivity))

#print axioms finite_shifted_dyadic_zero_energy_gm_bound

end

end GafniTao
