import GafniTao.EnergyDetectorSharpShellExtraction

/-!
# Source data carried by one sharp dyadic zero-shell detector

The four coordinates of a zero-energy tuple need not lie in the same dyadic
height shell.  This module packages the exact choice functions furnished by
the signed sharp mollifier on one shell, before any energy pigeonhole is
performed.  In particular, the scale and sign labels remain available for a
later four-shell mixed extraction.
-/

open scoped BigOperators

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The complete detector data on one signed dyadic shell.  The representative
is definitionally the representative of the selected scale/unit-bin cell. -/
structure SharpShellDetectorData
    (sigma U delta eta C : Real) (X A : Nat) where
  k : Nat
  hk : 0 < k
  shift : Complex -> Real
  scale : Complex -> Fin (k * 2)
  hShift : forall rho, rho ∈ absoluteDyadicZeroSlab sigma U ->
    |rho.im - detectorRepresentative
      (absoluteDyadicZeroSlab sigma U) scale shift rho| <= U ^ delta + 1
  hLocal : forall t : Real,
    (∑ rho ∈ (absoluteDyadicZeroSlab sigma U).filter
      (fun z => detectorRepresentative
        (absoluteDyadicZeroSlab sigma U) scale shift z = t),
      zeroMultiplicity rho) <=
      (2 * ⌈U ^ delta + 1⌉₊ + 1) * sharpShellLocalMultiplicityCap U
  hSeparated : forall label : Fin (k * 2) × Fin 2,
    IsSeparated 1
      (((absoluteDyadicZeroSlab sigma U).filter
        (fun rho => detectorColor scale shift rho = label)).image
          (detectorRepresentative
            (absoluteDyadicZeroSlab sigma U) scale shift))
  hLarge : forall rho, rho ∈ absoluteDyadicZeroSlab sigma U ->
    SharpShellScaleLarge A X k sigma eta C (scale rho)
      (detectorRepresentative
        (absoluteDyadicZeroSlab sigma U) scale shift rho)
  hInterval : forall rho, rho ∈ absoluteDyadicZeroSlab sigma U ->
    -(2 * U + U ^ delta) <=
        detectorRepresentative
          (absoluteDyadicZeroSlab sigma U) scale shift rho ∧
      detectorRepresentative
          (absoluteDyadicZeroSlab sigma U) scale shift rho <=
        2 * U + U ^ delta

/-- The signed sharp-mollifier theorem supplies the full per-shell detector
data, with one coefficient constant and one eventual threshold valid for all
shells and all admissible starting blocks. -/
theorem exists_sharpShellDetectorData
    (sigma delta eta : Real) (hsigma : 1 / 2 < sigma)
    (hsigmaUpper : sigma <= 1) (hdelta : 0 < delta) (heta : 0 < eta) :
    exists C T0 : Real, 0 < C ∧
      (forall (A X n : Nat), 0 < n ->
        ‖sharpMollifiedCoeff A X n‖ <= C * (n : Real) ^ eta) ∧
      8 <= T0 ∧
      forall (U : Real) (X : Nat), T0 <= U ->
        1 <= X -> X <= ⌊sharpZetaCutoff U⌋₊ -> (X : Real) <= U ->
        Nonempty (SharpShellDetectorData sigma U delta eta C X
          ⌊sharpZetaCutoff U⌋₊) := by
  obtain ⟨C, T0, hC, hCoeff, hT0, hWitness⟩ :=
    absoluteSlab_sharpMollified_energy_witness sigma delta eta
      hsigma hsigmaUpper hdelta heta
  refine ⟨C, T0, hC, hCoeff, hT0, ?_⟩
  intro U X hU hX hXA hXU
  let A := ⌊sharpZetaCutoff U⌋₊
  let k := Nat.clog 2 A
  let H := U ^ delta
  obtain ⟨hk, hEachRaw⟩ := hWitness U X hU hX hXA hXU
  have hK : 0 < k * 2 := Nat.mul_pos hk (by norm_num)
  let large : Fin (k * 2) -> Real -> Prop :=
    SharpShellScaleLarge A X k sigma eta C
  have hEach : forall rho, rho ∈ absoluteDyadicZeroSlab sigma U ->
      exists t : Real, |rho.im - t| <= H ∧
        (-(2 * U + H) <= t ∧ t <= 2 * U + H) ∧
        exists q : Fin (k * 2), large q t := by
    intro rho hrho
    obtain ⟨t, ht, htI, r, hrCoeff, hrLarge⟩ := hEachRaw rho hrho
    let q : Fin (k * 2) := finProdFinEquiv r
    refine ⟨t, ht, htI, q, ?_⟩
    constructor
    · intro n hn
      have hn' : n ∈ dyadicInterval
          ((fun _sign : Fin 2 => 2 ^ (r.1 : Nat) * X) r.2) := by
        simpa [sharpShellScaleN, sharpShellScalePair, q] using hn
      simpa [large, SharpShellScaleLarge, sharpShellScaleCoeff,
        sharpShellScaleN, sharpShellScalePair, q] using hrCoeff n hn'
    · simpa [large, SharpShellScaleLarge, sharpShellScaleCoeff,
        sharpShellScaleN, sharpShellScalePair, q] using hrLarge
  let shift : Complex -> Real := fun rho =>
    if h : rho ∈ absoluteDyadicZeroSlab sigma U then
      Classical.choose (hEach rho h) else rho.im
  let scale : Complex -> Fin (k * 2) := fun rho =>
    if h : rho ∈ absoluteDyadicZeroSlab sigma U then
      Classical.choose (Classical.choose_spec (hEach rho h)).2.2
    else ⟨0, hK⟩
  let representative := detectorRepresentative
    (absoluteDyadicZeroSlab sigma U) scale shift
  have hShiftRaw : forall rho, rho ∈ absoluteDyadicZeroSlab sigma U ->
      |rho.im - shift rho| <= H := by
    intro rho hrho
    dsimp only [shift]
    rw [dif_pos hrho]
    exact (Classical.choose_spec (hEach rho hrho)).1
  have hRepShift : forall rho, rho ∈ absoluteDyadicZeroSlab sigma U ->
      |rho.im - representative rho| <= H + 1 := by
    intro rho hrho
    exact abs_ordinate_sub_detectorRepresentative_le
      (absoluteDyadicZeroSlab sigma U) scale Complex.im shift H
      hShiftRaw hrho
  have hLocalHeight : max (Real.exp 2) 8 <= 2 * U := by
    apply max_le
    · have hexp : Real.exp 2 <= 8 := by
        rw [show (2 : Real) = 1 + 1 by norm_num, Real.exp_add]
        nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
      exact hexp.trans (by linarith [hT0.trans hU])
    · linarith [hT0.trans hU]
  have hUnitLocal : forall z : Int,
      (∑ rho ∈ (absoluteDyadicZeroSlab sigma U).filter
        (fun y => (z : Real) <= y.im ∧ y.im < (z : Real) + 1),
        zeroMultiplicity rho) <= sharpShellLocalMultiplicityCap U := by
    intro z
    exact absoluteDyadicZeroSlab_unitBin_multiplicity_le sigma U z
      (by linarith) hLocalHeight
  have hRepLocal : forall t : Real,
      (∑ rho ∈ (absoluteDyadicZeroSlab sigma U).filter
        (fun z => representative z = t), zeroMultiplicity rho) <=
        (2 * ⌈H + 1⌉₊ + 1) * sharpShellLocalMultiplicityCap U := by
    intro t
    exact detectorRepresentative_fiber_weight_le
      (absoluteDyadicZeroSlab sigma U) scale zeroMultiplicity Complex.im
      shift H (sharpShellLocalMultiplicityCap U) hShiftRaw hUnitLocal t
  have hRepLarge : forall rho, rho ∈ absoluteDyadicZeroSlab sigma U ->
      large (scale rho) (representative rho) := by
    intro rho hrho
    apply detectorRepresentative_large
      (absoluteDyadicZeroSlab sigma U) scale shift large
    · intro z hz
      dsimp only [scale, shift]
      rw [dif_pos hz, dif_pos hz]
      exact Classical.choose_spec
        (Classical.choose_spec (hEach z hz)).2.2
    · exact hrho
  have hRepInterval : forall rho, rho ∈ absoluteDyadicZeroSlab sigma U ->
      -(2 * U + H) <= representative rho ∧
        representative rho <= 2 * U + H := by
    intro rho hrho
    obtain ⟨z, hz, hscale, hfloor, hrep⟩ :=
      detectorRepresentative_spec
        (absoluteDyadicZeroSlab sigma U) scale shift hrho
    change -(2 * U + H) <=
        detectorRepresentative
          (absoluteDyadicZeroSlab sigma U) scale shift rho ∧
      detectorRepresentative
          (absoluteDyadicZeroSlab sigma U) scale shift rho <= 2 * U + H
    rw [hrep]
    dsimp only [shift]
    rw [dif_pos hz]
    exact (Classical.choose_spec (hEach z hz)).2.1
  refine ⟨⟨k, hk, shift, scale, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simpa only [A, H, representative] using hRepShift
  · simpa only [H, representative] using hRepLocal
  · intro label
    exact isSeparated_detectorRepresentative_color
      (absoluteDyadicZeroSlab sigma U) scale shift label
  · simpa only [A, k, large, representative] using hRepLarge
  · simpa only [H, representative] using hRepInterval

#print axioms exists_sharpShellDetectorData

end

end GafniTao
