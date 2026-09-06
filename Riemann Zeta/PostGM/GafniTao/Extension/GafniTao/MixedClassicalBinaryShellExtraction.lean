import GafniTao.ClassicalBinaryShellDetectorData
import GafniTao.MixedShellDetectorExtraction

/-!
# Four-shell extraction for the classical binary detector

This is the coordinate-dependent source entry needed after the logarithmic
height-shell cover.  Every coordinate retains its own Type-I/Type-II branch,
dyadic length, source sign, parity colour, displacement, and multiplicity
loss.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Exact mixed-energy extraction for four independently chosen signed shells
equipped with the real classical binary detector data. -/
theorem mixed_absoluteSlabs_classical_binary_detector_extraction
    (sigma delta : Real)
    (U0 U1 U2 U3 : Real)
    (Y0 X0 A0 Y1 X1 A1 Y2 X2 A2 Y3 X3 A3 : Nat)
    (q0 q1 q2 q3 : Real)
    (d0 : ClassicalBinaryShellDetectorData sigma U0 delta Y0 X0 A0 q0)
    (d1 : ClassicalBinaryShellDetectorData sigma U1 delta Y1 X1 A1 q1)
    (d2 : ClassicalBinaryShellDetectorData sigma U2 delta Y2 X2 A2 q2)
    (d3 : ClassicalBinaryShellDetectorData sigma U3 delta Y3 X3 A3 q3)
    (hU0 : 0 ≤ U0) (hU1 : 0 ≤ U1)
    (hU2 : 0 ≤ U2) (hU3 : 0 ≤ U3) :
    ∃ label0 : Fin (d0.kI * 2 + d0.kII * 2) × Fin 2,
      ∃ label1 : Fin (d1.kI * 2 + d1.kII * 2) × Fin 2,
      ∃ label2 : Fin (d2.kI * 2 + d2.kII * 2) × Fin 2,
      ∃ label3 : Fin (d3.kI * 2 + d3.kII * 2) × Fin 2,
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
      (∀ t ∈ W0, Sum.elim
        (ClassicalTypeIShellScaleLarge A0 Y0 d0.kI sigma q0)
        (ClassicalTypeIIShellScaleLarge Y0 X0 d0.kII sigma)
        (binaryScaleLabel label0.1) t) ∧
      (∀ t ∈ W1, Sum.elim
        (ClassicalTypeIShellScaleLarge A1 Y1 d1.kI sigma q1)
        (ClassicalTypeIIShellScaleLarge Y1 X1 d1.kII sigma)
        (binaryScaleLabel label1.1) t) ∧
      (∀ t ∈ W2, Sum.elim
        (ClassicalTypeIShellScaleLarge A2 Y2 d2.kI sigma q2)
        (ClassicalTypeIIShellScaleLarge Y2 X2 d2.kII sigma)
        (binaryScaleLabel label2.1) t) ∧
      (∀ t ∈ W3, Sum.elim
        (ClassicalTypeIShellScaleLarge A3 Y3 d3.kI sigma q3)
        (ClassicalTypeIIShellScaleLarge Y3 X3 d3.kII sigma)
        (binaryScaleLabel label3.1) t) ∧
      W0.card ≤ zeroCount sigma (2 * U0) ∧
      W1.card ≤ zeroCount sigma (2 * U1) ∧
      W2.card ≤ zeroCount sigma (2 * U2) ∧
      W3.card ≤ zeroCount sigma (2 * U3) ∧
      weightedMixedAdditiveEnergyOn
          (absoluteDyadicZeroSlab sigma U0)
          (absoluteDyadicZeroSlab sigma U1)
          (absoluteDyadicZeroSlab sigma U2)
          (absoluteDyadicZeroSlab sigma U3) zeroMultiplicity 1 ≤
        (((d0.kI * 2 + d0.kII * 2) * 2) *
          ((d1.kI * 2 + d1.kII * 2) * 2) *
          ((d2.kI * 2 + d2.kII * 2) * 2) *
          ((d3.kI * 2 + d3.kII * 2) * 2)) *
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
  let K0 := Fin (d0.kI * 2 + d0.kII * 2) × Fin 2
  let K1 := Fin (d1.kI * 2 + d1.kII * 2) × Fin 2
  let K2 := Fin (d2.kI * 2 + d2.kII * 2) × Fin 2
  let K3 := Fin (d3.kI * 2 + d3.kII * 2) × Fin 2
  have hk0 : 0 < d0.kI * 2 + d0.kII * 2 := Nat.add_pos_left d0.hkI _
  have hk1 : 0 < d1.kI * 2 + d1.kII * 2 := Nat.add_pos_left d1.hkI _
  have hk2 : 0 < d2.kI * 2 + d2.kII * 2 := Nat.add_pos_left d2.hkI _
  have hk3 : 0 < d3.kI * 2 + d3.kII * 2 := Nat.add_pos_left d3.hkI _
  letI : Nonempty K0 := ⟨⟨⟨0, hk0⟩, 0⟩⟩
  letI : Nonempty K1 := ⟨⟨⟨0, hk1⟩, 0⟩⟩
  letI : Nonempty K2 := ⟨⟨⟨0, hk2⟩, 0⟩⟩
  letI : Nonempty K3 := ⟨⟨⟨0, hk3⟩, 0⟩⟩
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
  have hLarge0 : ∀ t ∈ W0, Sum.elim
      (ClassicalTypeIShellScaleLarge A0 Y0 d0.kI sigma q0)
      (ClassicalTypeIIShellScaleLarge Y0 X0 d0.kII sigma)
      (binaryScaleLabel label0.1) t := by
    intro t ht
    obtain ⟨rho, hrho, rfl⟩ := Finset.mem_image.mp ht
    have hm := Finset.mem_filter.mp hrho
    have hs := congrArg Prod.fst hm.2
    rw [← hs]
    exact d0.hLarge rho hm.1
  have hLarge1 : ∀ t ∈ W1, Sum.elim
      (ClassicalTypeIShellScaleLarge A1 Y1 d1.kI sigma q1)
      (ClassicalTypeIIShellScaleLarge Y1 X1 d1.kII sigma)
      (binaryScaleLabel label1.1) t := by
    intro t ht
    obtain ⟨rho, hrho, rfl⟩ := Finset.mem_image.mp ht
    have hm := Finset.mem_filter.mp hrho
    have hs := congrArg Prod.fst hm.2
    rw [← hs]
    exact d1.hLarge rho hm.1
  have hLarge2 : ∀ t ∈ W2, Sum.elim
      (ClassicalTypeIShellScaleLarge A2 Y2 d2.kI sigma q2)
      (ClassicalTypeIIShellScaleLarge Y2 X2 d2.kII sigma)
      (binaryScaleLabel label2.1) t := by
    intro t ht
    obtain ⟨rho, hrho, rfl⟩ := Finset.mem_image.mp ht
    have hm := Finset.mem_filter.mp hrho
    have hs := congrArg Prod.fst hm.2
    rw [← hs]
    exact d2.hLarge rho hm.1
  have hLarge3 : ∀ t ∈ W3, Sum.elim
      (ClassicalTypeIShellScaleLarge A3 Y3 d3.kI sigma q3)
      (ClassicalTypeIIShellScaleLarge Y3 X3 d3.kII sigma)
      (binaryScaleLabel label3.1) t := by
    intro t ht
    obtain ⟨rho, hrho, rfl⟩ := Finset.mem_image.mp ht
    have hm := Finset.mem_filter.mp hrho
    have hs := congrArg Prod.fst hm.2
    rw [← hs]
    exact d3.hLarge rho hm.1
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
      show (1 : Real) + (U0 ^ delta + 1) + (U1 ^ delta + 1) +
          (U2 ^ delta + 1) + (U3 ^ delta + 1) =
          5 + U0 ^ delta + U1 ^ delta + U2 ^ delta + U3 ^ delta by ring]
      using hEnergy

#print axioms mixed_absoluteSlabs_classical_binary_detector_extraction

end

end GafniTao
