import GafniTao.HeathBrownFiniteMixedEnergy
import GafniTao.MixedSharpShellExtraction

/-!
# Sharp zero shells consumed by the finite Heath--Brown relation

This is the source-entry composition: four actual multiplicity-weighted zero
shells are passed through their sharp-mollifier detector and then through the
finite Heath--Brown energy theorem.  All selected scales and finite losses
remain visible.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Literal large-value threshold carried by a selected sharp shell. -/
noncomputable def sharpShellHeathBrownThreshold
    (k M : Nat) (C eta sigma : Real) : Real :=
  ((3 / 8) / (k : Real)) /
    (C * (2 * M : Real) ^ eta * (M : Real) ^ (-sigma))

/-- Four independently selected sharp zero shells, consumed by the exact
finite Heath--Brown relation.  The final implication contains only physical
ambient-scale comparisons; it does not assume a density or energy theorem. -/
theorem mixedSharpShell_heathBrownFiniteEnergy_native
    (epsilon sigma delta eta C : Real)
    (U0 U1 U2 U3 : Real) (X0 X1 X2 X3 : Nat)
    (A0 A1 A2 A3 : Nat)
    (d0 : SharpShellDetectorData sigma U0 delta eta C X0 A0)
    (d1 : SharpShellDetectorData sigma U1 delta eta C X1 A1)
    (d2 : SharpShellDetectorData sigma U2 delta eta C X2 A2)
    (d3 : SharpShellDetectorData sigma U3 delta eta C X3 A3)
    (B0 B1 B2 B3 : Real)
    (hepsilon : 0 < epsilon) (hC : 0 < C)
    (hX0 : 0 < X0) (hX1 : 0 < X1)
    (hX2 : 0 < X2) (hX3 : 0 < X3)
    (hU0 : 0 <= U0) (hU1 : 0 <= U1)
    (hU2 : 0 <= U2) (hU3 : 0 <= U3) :
    exists C0 C2 C4 T0 : Real,
      0 < C0 ∧ 0 < C2 ∧ 0 < C4 ∧ 1 <= T0 ∧
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
      let M0 := sharpShellScaleN X0 label0.1
      let M1 := sharpShellScaleN X1 label1.1
      let M2 := sharpShellScaleN X2 label2.1
      let M3 := sharpShellScaleN X3 label3.1
      let V0 := sharpShellHeathBrownThreshold d0.k M0 C eta sigma
      let V1 := sharpShellHeathBrownThreshold d1.k M1 C eta sigma
      let V2 := sharpShellHeathBrownThreshold d2.k M2 C eta sigma
      let V3 := sharpShellHeathBrownThreshold d3.k M3 C eta sigma
      W0.card <= zeroCount sigma (2 * U0) ∧
      W1.card <= zeroCount sigma (2 * U1) ∧
      W2.card <= zeroCount sigma (2 * U2) ∧
      W3.card <= zeroCount sigma (2 * U3) ∧
      ((T0 <= B0 ∧ T0 <= B1 ∧ T0 <= B2 ∧ T0 <= B3) ->
       ((M0 : Real) <= B0 ∧ (M1 : Real) <= B1 ∧
          (M2 : Real) <= B2 ∧ (M3 : Real) <= B3) ->
       (2 * (2 * U0 + U0 ^ delta) <= B0 ∧
          2 * (2 * U1 + U1 ^ delta) <= B1 ∧
          2 * (2 * U2 + U2 ^ delta) <= B2 ∧
          2 * (2 * U3 + U3 ^ delta) <= B3) ->
       4 * (weightedMixedAdditiveEnergyOn
          (absoluteDyadicZeroSlab sigma U0)
          (absoluteDyadicZeroSlab sigma U1)
          (absoluteDyadicZeroSlab sigma U2)
          (absoluteDyadicZeroSlab sigma U3) zeroMultiplicity 1 : Real) <=
        (((4 * d0.k) * (4 * d1.k) * (4 * d2.k) * (4 * d3.k)) *
          (((2 * ⌈U0 ^ delta + 1⌉₊ + 1) * sharpShellLocalMultiplicityCap U0) *
            ((2 * ⌈U1 ^ delta + 1⌉₊ + 1) * sharpShellLocalMultiplicityCap U1) *
            ((2 * ⌈U2 ^ delta + 1⌉₊ + 1) * sharpShellLocalMultiplicityCap U2) *
            ((2 * ⌈U3 ^ delta + 1⌉₊ + 1) * sharpShellLocalMultiplicityCap U3)) : Nat) *
          (doubleFloorDefectWindow
            (5 + U0 ^ delta + U1 ^ delta + U2 ^ delta + U3 ^ delta)).card *
          (heathBrownFiniteFamilyBound epsilon C0 C2 C4 B0 V0 M0 W0 +
            heathBrownFiniteFamilyBound epsilon C0 C2 C4 B1 V1 M1 W1 +
            heathBrownFiniteFamilyBound epsilon C0 C2 C4 B2 V2 M2 W2 +
            heathBrownFiniteFamilyBound epsilon C0 C2 C4 B3 V3 M3 W3)) := by
  obtain ⟨C0, C2, C4, T0, hC0, hC2, hC4, hT0, hFinite⟩ :=
    heathBrownFiniteMixedEnergyRelation_native epsilon hepsilon
  obtain ⟨label0, label1, label2, label3,
      hSep0, hSep1, hSep2, hSep3,
      hLarge0, hLarge1, hLarge2, hLarge3,
      hCard0, hCard1, hCard2, hCard3, hExtract⟩ :=
    mixed_absoluteSlabs_sharp_detector_extraction
      sigma delta eta C U0 U1 U2 U3 X0 X1 X2 X3 A0 A1 A2 A3
      d0 d1 d2 d3 hU0 hU1 hU2 hU3
  refine ⟨C0, C2, C4, T0, hC0, hC2, hC4, hT0,
    label0, label1, label2, label3, ?_⟩
  dsimp only
  refine ⟨hCard0, hCard1, hCard2, hCard3, ?_⟩
  intro hBs hMs hRs
  let W : Fin 4 -> Finset Real := ![
    ((absoluteDyadicZeroSlab sigma U0).filter
      (fun rho => detectorColor d0.scale d0.shift rho = label0)).image
        (detectorRepresentative
          (absoluteDyadicZeroSlab sigma U0) d0.scale d0.shift),
    ((absoluteDyadicZeroSlab sigma U1).filter
      (fun rho => detectorColor d1.scale d1.shift rho = label1)).image
        (detectorRepresentative
          (absoluteDyadicZeroSlab sigma U1) d1.scale d1.shift),
    ((absoluteDyadicZeroSlab sigma U2).filter
      (fun rho => detectorColor d2.scale d2.shift rho = label2)).image
        (detectorRepresentative
          (absoluteDyadicZeroSlab sigma U2) d2.scale d2.shift),
    ((absoluteDyadicZeroSlab sigma U3).filter
      (fun rho => detectorColor d3.scale d3.shift rho = label3)).image
        (detectorRepresentative
          (absoluteDyadicZeroSlab sigma U3) d3.scale d3.shift)]
  let M : Fin 4 -> Nat := ![
    sharpShellScaleN X0 label0.1, sharpShellScaleN X1 label1.1,
    sharpShellScaleN X2 label2.1, sharpShellScaleN X3 label3.1]
  let B : Fin 4 -> Real := ![B0, B1, B2, B3]
  let R : Fin 4 -> Real := ![
    2 * U0 + U0 ^ delta, 2 * U1 + U1 ^ delta,
    2 * U2 + U2 ^ delta, 2 * U3 + U3 ^ delta]
  let V : Fin 4 -> Real := ![
    sharpShellHeathBrownThreshold d0.k (M 0) C eta sigma,
    sharpShellHeathBrownThreshold d1.k (M 1) C eta sigma,
    sharpShellHeathBrownThreshold d2.k (M 2) C eta sigma,
    sharpShellHeathBrownThreshold d3.k (M 3) C eta sigma]
  let b : Fin 4 -> Nat -> Complex := ![
    sharpShellScaleCoeff A0 X0 sigma eta C label0.1,
    sharpShellScaleCoeff A1 X1 sigma eta C label1.1,
    sharpShellScaleCoeff A2 X2 sigma eta C label2.1,
    sharpShellScaleCoeff A3 X3 sigma eta C label3.1]
  have hMpos : forall i, 0 < M i := by
    intro i
    fin_cases i
    · simp [M, sharpShellScaleN, hX0]
    · simp [M, sharpShellScaleN, hX1]
    · simp [M, sharpShellScaleN, hX2]
    · simp [M, sharpShellScaleN, hX3]
  have hB : forall i, T0 <= B i := by
    intro i
    fin_cases i
    · simpa [B] using hBs.1
    · simpa [B] using hBs.2.1
    · simpa [B] using hBs.2.2.1
    · simpa [B] using hBs.2.2.2
  have hMB : forall i, (M i : Real) <= B i := by
    intro i
    fin_cases i
    · simpa [M, B] using hMs.1
    · simpa [M, B] using hMs.2.1
    · simpa [M, B] using hMs.2.2.1
    · simpa [M, B] using hMs.2.2.2
  have hRB : forall i, 2 * R i <= B i := by
    intro i
    fin_cases i
    · simpa [R, B] using hRs.1
    · simpa [R, B] using hRs.2.1
    · simpa [R, B] using hRs.2.2.1
    · simpa [R, B] using hRs.2.2.2
  have hVpos : forall i, 0 < V i := by
    intro i
    fin_cases i
    · have hk : (0 : Real) < d0.k := by exact_mod_cast d0.hk
      have hm : (0 : Real) < M 0 := by exact_mod_cast hMpos 0
      change 0 < sharpShellHeathBrownThreshold d0.k (M 0) C eta sigma
      unfold sharpShellHeathBrownThreshold
      positivity
    · have hk : (0 : Real) < d1.k := by exact_mod_cast d1.hk
      have hm : (0 : Real) < M 1 := by exact_mod_cast hMpos 1
      change 0 < sharpShellHeathBrownThreshold d1.k (M 1) C eta sigma
      unfold sharpShellHeathBrownThreshold
      positivity
    · have hk : (0 : Real) < d2.k := by exact_mod_cast d2.hk
      have hm : (0 : Real) < M 2 := by exact_mod_cast hMpos 2
      change 0 < sharpShellHeathBrownThreshold d2.k (M 2) C eta sigma
      unfold sharpShellHeathBrownThreshold
      positivity
    · have hk : (0 : Real) < d3.k := by exact_mod_cast d3.hk
      have hm : (0 : Real) < M 3 := by exact_mod_cast hMpos 3
      change 0 < sharpShellHeathBrownThreshold d3.k (M 3) C eta sigma
      unfold sharpShellHeathBrownThreshold
      positivity
  have hSep : forall i, IsSeparated 1 (W i) := by
    intro i
    fin_cases i
    · simpa [W] using hSep0
    · simpa [W] using hSep1
    · simpa [W] using hSep2
    · simpa [W] using hSep3
  have hSymm : forall i t, t ∈ W i -> -R i <= t ∧ t <= R i := by
    intro i t ht
    fin_cases i
    · simp only [W, R] at ht ⊢
      obtain ⟨rho, hrho, rfl⟩ := Finset.mem_image.mp ht
      exact d0.hInterval rho (Finset.mem_filter.mp hrho).1
    · simp [W, R] at ht ⊢
      obtain ⟨rho, hrho, hEq⟩ := ht
      subst t
      have hInterval := d1.hInterval rho hrho.1
      constructor <;> linarith
    · simp [W, R] at ht ⊢
      obtain ⟨rho, hrho, hEq⟩ := ht
      subst t
      have hInterval := d2.hInterval rho hrho.1
      constructor <;> linarith
    · simp [W, R] at ht ⊢
      obtain ⟨rho, hrho, hEq⟩ := ht
      subst t
      have hInterval := d3.hInterval rho hrho.1
      constructor <;> linarith
  have hb : forall i, (W i).Nonempty ->
      forall n, n ∈ dyadicInterval (M i) -> ‖b i n‖ <= 1 := by
    intro i hWi
    obtain ⟨t, ht⟩ := hWi
    fin_cases i
    · exact (hLarge0 t (by simpa [W] using ht)).1
    · exact (hLarge1 t (by simpa [W] using ht)).1
    · exact (hLarge2 t (by simpa [W] using ht)).1
    · exact (hLarge3 t (by simpa [W] using ht)).1
  have hLarge : forall i t, t ∈ W i ->
      V i <= ‖sourceDirichletPoly (M i) (b i) t‖ := by
    intro i t ht
    fin_cases i
    · simpa [W, M, V, b, sharpShellHeathBrownThreshold] using
        (hLarge0 t (by simpa [W] using ht)).2
    · simpa [W, M, V, b, sharpShellHeathBrownThreshold] using
        (hLarge1 t (by simpa [W] using ht)).2
    · simpa [W, M, V, b, sharpShellHeathBrownThreshold] using
        (hLarge2 t (by simpa [W] using ht)).2
    · simpa [W, M, V, b, sharpShellHeathBrownThreshold] using
        (hLarge3 t (by simpa [W] using ht)).2
  have hHB := hFinite
    (5 + U0 ^ delta + U1 ^ delta + U2 ^ delta + U3 ^ delta)
    M B R V W b hMpos hB hMB hVpos hRB hSep hSymm hb hLarge
  let Q : Nat :=
    ((4 * d0.k) * (4 * d1.k) * (4 * d2.k) * (4 * d3.k)) *
      (((2 * ⌈U0 ^ delta + 1⌉₊ + 1) * sharpShellLocalMultiplicityCap U0) *
        ((2 * ⌈U1 ^ delta + 1⌉₊ + 1) * sharpShellLocalMultiplicityCap U1) *
        ((2 * ⌈U2 ^ delta + 1⌉₊ + 1) * sharpShellLocalMultiplicityCap U2) *
        ((2 * ⌈U3 ^ delta + 1⌉₊ + 1) * sharpShellLocalMultiplicityCap U3))
  have hExtractReal :
      (weightedMixedAdditiveEnergyOn
        (absoluteDyadicZeroSlab sigma U0)
        (absoluteDyadicZeroSlab sigma U1)
        (absoluteDyadicZeroSlab sigma U2)
        (absoluteDyadicZeroSlab sigma U3) zeroMultiplicity 1 : Real) <=
      (Q : Real) *
        (MixedApproxAddEnergy
          (5 + U0 ^ delta + U1 ^ delta + U2 ^ delta + U3 ^ delta)
          (W 0) (W 1) (W 2) (W 3) : Real) := by
    exact_mod_cast hExtract
  calc
    4 * (weightedMixedAdditiveEnergyOn
        (absoluteDyadicZeroSlab sigma U0)
        (absoluteDyadicZeroSlab sigma U1)
        (absoluteDyadicZeroSlab sigma U2)
        (absoluteDyadicZeroSlab sigma U3) zeroMultiplicity 1 : Real) <=
      4 * ((Q : Real) *
        (MixedApproxAddEnergy
          (5 + U0 ^ delta + U1 ^ delta + U2 ^ delta + U3 ^ delta)
          (W 0) (W 1) (W 2) (W 3) : Real)) := by gcongr
    _ = (Q : Real) *
        (4 * (MixedApproxAddEnergy
          (5 + U0 ^ delta + U1 ^ delta + U2 ^ delta + U3 ^ delta)
          (W 0) (W 1) (W 2) (W 3) : Real)) := by ring
    _ <= (Q : Real) *
        ((doubleFloorDefectWindow
          (5 + U0 ^ delta + U1 ^ delta + U2 ^ delta + U3 ^ delta)).card *
          ∑ i : Fin 4,
            heathBrownFiniteFamilyBound epsilon C0 C2 C4
              (B i) (V i) (M i) (W i)) := by
      exact mul_le_mul_of_nonneg_left hHB (by positivity)
    _ = _ := by
      simp [Q, W, M, B, V, Fin.sum_univ_four]
      ring

#print axioms mixedSharpShell_heathBrownFiniteEnergy_native

end

end GafniTao
