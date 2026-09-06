import GafniTao.SharpShellDetectorData
import GafniTao.MixedShellDetectorExtraction

/-!
# Simultaneous extraction from four sharp dyadic zero shells

This is the source-entry bridge needed after the logarithmic height-shell
coloring.  Each coordinate keeps its own shell height, detector scale, source
sign, coefficient sequence, and local multiplicity loss.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Exact mixed-energy extraction for four independently selected signed
dyadic zero shells. -/
theorem mixed_absoluteSlabs_sharp_detector_extraction
    (sigma delta eta C : Real)
    (U0 U1 U2 U3 : Real) (X0 X1 X2 X3 : Nat)
    (A0 A1 A2 A3 : Nat)
    (d0 : SharpShellDetectorData sigma U0 delta eta C X0 A0)
    (d1 : SharpShellDetectorData sigma U1 delta eta C X1 A1)
    (d2 : SharpShellDetectorData sigma U2 delta eta C X2 A2)
    (d3 : SharpShellDetectorData sigma U3 delta eta C X3 A3)
    (hU0 : 0 <= U0) (hU1 : 0 <= U1)
    (hU2 : 0 <= U2) (hU3 : 0 <= U3) :
    exists label0 : Fin (d0.k * 2) × Fin 2,
      exists label1 : Fin (d1.k * 2) × Fin 2,
      exists label2 : Fin (d2.k * 2) × Fin 2,
      exists label3 : Fin (d3.k * 2) × Fin 2,
      let f0 := detectorRepresentative
        (absoluteDyadicZeroSlab sigma U0) d0.scale d0.shift
      let f1 := detectorRepresentative
        (absoluteDyadicZeroSlab sigma U1) d1.scale d1.shift
      let f2 := detectorRepresentative
        (absoluteDyadicZeroSlab sigma U2) d2.scale d2.shift
      let f3 := detectorRepresentative
        (absoluteDyadicZeroSlab sigma U3) d3.scale d3.shift
      let W0 := ((absoluteDyadicZeroSlab sigma U0).filter
        (fun rho => detectorColor d0.scale d0.shift rho = label0)).image f0
      let W1 := ((absoluteDyadicZeroSlab sigma U1).filter
        (fun rho => detectorColor d1.scale d1.shift rho = label1)).image f1
      let W2 := ((absoluteDyadicZeroSlab sigma U2).filter
        (fun rho => detectorColor d2.scale d2.shift rho = label2)).image f2
      let W3 := ((absoluteDyadicZeroSlab sigma U3).filter
        (fun rho => detectorColor d3.scale d3.shift rho = label3)).image f3
      IsSeparated 1 W0 ∧ IsSeparated 1 W1 ∧
      IsSeparated 1 W2 ∧ IsSeparated 1 W3 ∧
      (forall t, t ∈ W0 -> SharpShellScaleLarge A0 X0 d0.k sigma eta C label0.1 t) ∧
      (forall t, t ∈ W1 -> SharpShellScaleLarge A1 X1 d1.k sigma eta C label1.1 t) ∧
      (forall t, t ∈ W2 -> SharpShellScaleLarge A2 X2 d2.k sigma eta C label2.1 t) ∧
      (forall t, t ∈ W3 -> SharpShellScaleLarge A3 X3 d3.k sigma eta C label3.1 t) ∧
      W0.card <= zeroCount sigma (2 * U0) ∧
      W1.card <= zeroCount sigma (2 * U1) ∧
      W2.card <= zeroCount sigma (2 * U2) ∧
      W3.card <= zeroCount sigma (2 * U3) ∧
      weightedMixedAdditiveEnergyOn
          (absoluteDyadicZeroSlab sigma U0)
          (absoluteDyadicZeroSlab sigma U1)
          (absoluteDyadicZeroSlab sigma U2)
          (absoluteDyadicZeroSlab sigma U3) zeroMultiplicity 1 <=
        ((4 * d0.k) * (4 * d1.k) * (4 * d2.k) * (4 * d3.k)) *
          (((2 * ⌈U0 ^ delta + 1⌉₊ + 1) * sharpShellLocalMultiplicityCap U0) *
            ((2 * ⌈U1 ^ delta + 1⌉₊ + 1) * sharpShellLocalMultiplicityCap U1) *
            ((2 * ⌈U2 ^ delta + 1⌉₊ + 1) * sharpShellLocalMultiplicityCap U2) *
            ((2 * ⌈U3 ^ delta + 1⌉₊ + 1) * sharpShellLocalMultiplicityCap U3)) *
          MixedApproxAddEnergy
            (5 + U0 ^ delta + U1 ^ delta + U2 ^ delta + U3 ^ delta)
            W0 W1 W2 W3 := by
  classical
  let f0 := detectorRepresentative
    (absoluteDyadicZeroSlab sigma U0) d0.scale d0.shift
  let f1 := detectorRepresentative
    (absoluteDyadicZeroSlab sigma U1) d1.scale d1.shift
  let f2 := detectorRepresentative
    (absoluteDyadicZeroSlab sigma U2) d2.scale d2.shift
  let f3 := detectorRepresentative
    (absoluteDyadicZeroSlab sigma U3) d3.scale d3.shift
  let K0 := Fin (d0.k * 2) × Fin 2
  let K1 := Fin (d1.k * 2) × Fin 2
  let K2 := Fin (d2.k * 2) × Fin 2
  let K3 := Fin (d3.k * 2) × Fin 2
  letI : Nonempty K0 := ⟨⟨⟨0, Nat.mul_pos d0.hk (by norm_num)⟩, 0⟩⟩
  letI : Nonempty K1 := ⟨⟨⟨0, Nat.mul_pos d1.hk (by norm_num)⟩, 0⟩⟩
  letI : Nonempty K2 := ⟨⟨⟨0, Nat.mul_pos d2.hk (by norm_num)⟩, 0⟩⟩
  letI : Nonempty K3 := ⟨⟨⟨0, Nat.mul_pos d3.hk (by norm_num)⟩, 0⟩⟩
  obtain ⟨label0, label1, label2, label3, hEnergy⟩ :=
    mixed_weighted_energy_detector_extraction
      (K0 := K0) (K1 := K1) (K2 := K2) (K3 := K3)
      (absoluteDyadicZeroSlab sigma U0)
      (absoluteDyadicZeroSlab sigma U1)
      (absoluteDyadicZeroSlab sigma U2)
      (absoluteDyadicZeroSlab sigma U3) zeroMultiplicity
      1 (U0 ^ delta + 1) (U1 ^ delta + 1)
      (U2 ^ delta + 1) (U3 ^ delta + 1)
      (detectorColor d0.scale d0.shift)
      (detectorColor d1.scale d1.shift)
      (detectorColor d2.scale d2.shift)
      (detectorColor d3.scale d3.shift)
      f0 f1 f2 f3
      ((2 * ⌈U0 ^ delta + 1⌉₊ + 1) * sharpShellLocalMultiplicityCap U0)
      ((2 * ⌈U1 ^ delta + 1⌉₊ + 1) * sharpShellLocalMultiplicityCap U1)
      ((2 * ⌈U2 ^ delta + 1⌉₊ + 1) * sharpShellLocalMultiplicityCap U2)
      ((2 * ⌈U3 ^ delta + 1⌉₊ + 1) * sharpShellLocalMultiplicityCap U3)
      d0.hShift d1.hShift d2.hShift d3.hShift
      d0.hLocal d1.hLocal d2.hLocal d3.hLocal
  let W0 := ((absoluteDyadicZeroSlab sigma U0).filter
    (fun rho => detectorColor d0.scale d0.shift rho = label0)).image f0
  let W1 := ((absoluteDyadicZeroSlab sigma U1).filter
    (fun rho => detectorColor d1.scale d1.shift rho = label1)).image f1
  let W2 := ((absoluteDyadicZeroSlab sigma U2).filter
    (fun rho => detectorColor d2.scale d2.shift rho = label2)).image f2
  let W3 := ((absoluteDyadicZeroSlab sigma U3).filter
    (fun rho => detectorColor d3.scale d3.shift rho = label3)).image f3
  have hLarge0 : forall t, t ∈ W0 ->
      SharpShellScaleLarge A0 X0 d0.k sigma eta C label0.1 t := by
    intro t ht
    obtain ⟨rho, hrho, rfl⟩ := Finset.mem_image.mp ht
    have hmem := Finset.mem_filter.mp hrho
    have hs := congrArg Prod.fst hmem.2
    rw [← hs]
    exact d0.hLarge rho hmem.1
  have hLarge1 : forall t, t ∈ W1 ->
      SharpShellScaleLarge A1 X1 d1.k sigma eta C label1.1 t := by
    intro t ht
    obtain ⟨rho, hrho, rfl⟩ := Finset.mem_image.mp ht
    have hmem := Finset.mem_filter.mp hrho
    have hs := congrArg Prod.fst hmem.2
    rw [← hs]
    exact d1.hLarge rho hmem.1
  have hLarge2 : forall t, t ∈ W2 ->
      SharpShellScaleLarge A2 X2 d2.k sigma eta C label2.1 t := by
    intro t ht
    obtain ⟨rho, hrho, rfl⟩ := Finset.mem_image.mp ht
    have hmem := Finset.mem_filter.mp hrho
    have hs := congrArg Prod.fst hmem.2
    rw [← hs]
    exact d2.hLarge rho hmem.1
  have hLarge3 : forall t, t ∈ W3 ->
      SharpShellScaleLarge A3 X3 d3.k sigma eta C label3.1 t := by
    intro t ht
    obtain ⟨rho, hrho, rfl⟩ := Finset.mem_image.mp ht
    have hmem := Finset.mem_filter.mp hrho
    have hs := congrArg Prod.fst hmem.2
    rw [← hs]
    exact d3.hLarge rho hmem.1
  refine ⟨label0, label1, label2, label3, ?_⟩
  dsimp only
  refine ⟨d0.hSeparated label0, d1.hSeparated label1,
    d2.hSeparated label2, d3.hSeparated label3,
    hLarge0, hLarge1, hLarge2, hLarge3, ?_, ?_, ?_, ?_, ?_⟩
  · exact image_filter_absoluteDyadicZeroSlab_card_le_zeroCount
      sigma U0 hU0 _ _
  · exact image_filter_absoluteDyadicZeroSlab_card_le_zeroCount
      sigma U1 hU1 _ _
  · exact image_filter_absoluteDyadicZeroSlab_card_le_zeroCount
      sigma U2 hU2 _ _
  · exact image_filter_absoluteDyadicZeroSlab_card_le_zeroCount
      sigma U3 hU3 _ _
  · dsimp only [K0, K1, K2, K3] at hEnergy
    simp only [Fintype.card_prod, Fintype.card_fin] at hEnergy
    simpa only [f0, f1, f2, f3, W0, W1, W2, W3,
      show d0.k * 2 * 2 = 4 * d0.k by omega,
      show d1.k * 2 * 2 = 4 * d1.k by omega,
      show d2.k * 2 * 2 = 4 * d2.k by omega,
      show d3.k * 2 * 2 = 4 * d3.k by omega,
      show (1 : Real) + (U0 ^ delta + 1) + (U1 ^ delta + 1) +
          (U2 ^ delta + 1) + (U3 ^ delta + 1) =
          5 + U0 ^ delta + U1 ^ delta + U2 ^ delta + U3 ^ delta by ring]
      using hEnergy

#print axioms mixed_absoluteSlabs_sharp_detector_extraction

end

end GafniTao
