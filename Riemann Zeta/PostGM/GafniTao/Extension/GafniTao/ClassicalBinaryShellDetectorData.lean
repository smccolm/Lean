import GafniTao.ClassicalBinaryNormalization

/-!
# Choice data for the classical binary detector on one zero shell

The global zero-energy cover may select four different height shells.  This
module packages the actual pointwise Type-I/Type-II choices on one shell
before any four-coordinate pigeonhole is performed.
-/

open scoped BigOperators

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Complete per-shell data of the classical binary detector. -/
structure ClassicalBinaryShellDetectorData
    (sigma U delta : Real) (Y X A : Nat) (q0 : Real) where
  kI : Nat
  kII : Nat
  hkI_eq : kI = Nat.clog 2 A
  hkII_eq : kII = Nat.clog 2 Y
  hkI : 0 < kI * 2
  hkII : 0 < kII * 2
  shift : Complex → Real
  scale : Complex → Fin (kI * 2 + kII * 2)
  hShift : ∀ rho, rho ∈ absoluteDyadicZeroSlab sigma U →
    |rho.im - detectorRepresentative
      (absoluteDyadicZeroSlab sigma U) scale shift rho| ≤ U ^ delta + 1
  hLocal : ∀ t : Real,
    (∑ rho ∈ (absoluteDyadicZeroSlab sigma U).filter
      (fun z => detectorRepresentative
        (absoluteDyadicZeroSlab sigma U) scale shift z = t),
      zeroMultiplicity rho) ≤
      (2 * ⌈U ^ delta + 1⌉₊ + 1) * sharpShellLocalMultiplicityCap U
  hSeparated : ∀ label : Fin (kI * 2 + kII * 2) × Fin 2,
    IsSeparated 1
      (((absoluteDyadicZeroSlab sigma U).filter
        (fun rho => detectorColor scale shift rho = label)).image
          (detectorRepresentative
            (absoluteDyadicZeroSlab sigma U) scale shift))
  hLarge : ∀ rho, rho ∈ absoluteDyadicZeroSlab sigma U →
    Sum.elim
      (ClassicalTypeIShellScaleLarge A Y kI sigma q0)
      (ClassicalTypeIIShellScaleLarge Y X kII sigma)
      (binaryScaleLabel (scale rho))
      (detectorRepresentative
        (absoluteDyadicZeroSlab sigma U) scale shift rho)
  hLong : ∀ rho, rho ∈ absoluteDyadicZeroSlab sigma U →
    ∀ r : Fin (kI * 2), binaryScaleLabel (scale rho) = Sum.inl r →
      (3 / 4) * (q0 / 2) ≤
        ‖classicalZetaLongTail Y A
          ((sigma : Complex) + Complex.I *
            (((if classicalBinaryShellScaleSign (scale rho) = 0 then
                detectorRepresentative
                  (absoluteDyadicZeroSlab sigma U) scale shift rho
              else -detectorRepresentative
                  (absoluteDyadicZeroSlab sigma U) scale shift rho) : Real) :
              Complex))‖
  hInterval : ∀ rho, rho ∈ absoluteDyadicZeroSlab sigma U →
    -(2 * U + U ^ delta) ≤
        detectorRepresentative
          (absoluteDyadicZeroSlab sigma U) scale shift rho ∧
      detectorRepresentative
          (absoluteDyadicZeroSlab sigma U) scale shift rho ≤
        2 * U + U ^ delta
  hRadial : ∀ rho, rho ∈ absoluteDyadicZeroSlab sigma U →
    U - (U ^ delta + 1) ≤
      |detectorRepresentative
        (absoluteDyadicZeroSlab sigma U) scale shift rho|
  hOriented : ∀ rho, rho ∈ absoluteDyadicZeroSlab sigma U →
    if classicalBinaryShellScaleSign (scale rho) = 0 then
      U - U ^ delta ≤ detectorRepresentative
        (absoluteDyadicZeroSlab sigma U) scale shift rho
    else detectorRepresentative
        (absoluteDyadicZeroSlab sigma U) scale shift rho ≤
      -(U - U ^ delta)

private theorem exp_two_le_eight_detector : Real.exp 2 ≤ 8 := by
  rw [show (2 : Real) = 1 + 1 by norm_num, Real.exp_add]
  nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]

/-- The signed pointwise dichotomy supplies actual choice data on every
admissible dyadic height shell. -/
theorem exists_classicalBinaryShellDetectorData
    (sigma delta B₁ D₁ B₂ D₂ : Real)
    (hsigma : 1 / 2 < sigma) (hsigmaUpper : sigma ≤ 1)
    (hdelta : 0 < delta) :
    ∃ T₀ : Real, 8 ≤ T₀ ∧
      ∀ (U : Real) (Y X : Nat), T₀ ≤ U →
        1 ≤ X → 1 < Y → X ≤ Y → Y ≤ ⌊sharpZetaCutoff U⌋₊ →
        (∀ rho ∈ zerosInRect sigma 1 U (2 * U),
          149 * sharpZetaCutoff U ^ (-rho.re) ≤ U ^ (-D₁) / 2) →
        U ^ (-D₁) * (X : Real) ≤ 1 / 4 →
        finiteDirichletMass (classicalZetaLongTailSupport Y
            ⌊sharpZetaCutoff U⌋₊) (fun _n => 1) ≤ U ^ B₁ →
        U ^ (-D₁ - 1) ≤ U ^ (-D₁) / 2 →
        finiteDirichletMass (sharpMollifiedTailSupport Y X)
            (sharpMollifiedCoeff Y X) ≤ U ^ B₂ →
        U ^ (-D₂) ≤ 3 / 4 →
        Nonempty (ClassicalBinaryShellDetectorData sigma U delta Y X
          ⌊sharpZetaCutoff U⌋₊ (U ^ (-D₁))) := by
  obtain ⟨T₀, hT₀, hWitness⟩ :=
    absoluteSlab_classical_binary_pointwise_witness
      sigma delta B₁ D₁ B₂ D₂ hsigma hsigmaUpper hdelta
  refine ⟨T₀, hT₀, ?_⟩
  intro U Y X hU hX hY hXY hYA hError hShort hMassI hThresholdI
    hMassII hThresholdII
  let A := ⌊sharpZetaCutoff U⌋₊
  let q0 := U ^ (-D₁)
  let kI := Nat.clog 2 A
  let kII := Nat.clog 2 Y
  let H := U ^ delta
  obtain ⟨hkI, hkII, hEachRaw⟩ := hWitness U Y X hU hX hY hXY hYA
    hError hShort hMassI hThresholdI hMassII hThresholdII
  let largeI : Fin (kI * 2) → Real → Prop :=
    ClassicalTypeIShellScaleLarge A Y kI sigma q0
  let largeII : Fin (kII * 2) → Real → Prop :=
    ClassicalTypeIIShellScaleLarge Y X kII sigma
  let large : Fin (kI * 2 + kII * 2) → Real → Prop :=
    BinaryScaleLarge largeI largeII
  have hK : 0 < kI * 2 + kII * 2 := Nat.add_pos_left hkI _
  have hEach : ∀ rho, rho ∈ absoluteDyadicZeroSlab sigma U →
      ∃ t : Real, |rho.im - t| ≤ H ∧
        (-(2 * U + H) ≤ t ∧ t ≤ 2 * U + H) ∧
        ∃ q : Fin (kI * 2 + kII * 2), large q t ∧
          (if classicalBinaryShellScaleSign q = 0 then U - H ≤ t
            else t ≤ -(U - H)) ∧
          ∀ r : Fin (kI * 2), binaryScaleLabel q = Sum.inl r →
            (3 / 4) * (q0 / 2) ≤
              ‖classicalZetaLongTail Y A
                ((sigma : Complex) + Complex.I *
                  (((if classicalBinaryShellScaleSign q = 0 then t else -t) :
                    Real) : Complex))‖ := by
    intro rho hrho
    by_cases hb : signedChoosesClassicalTypeI Y q0 rho
    · obtain ⟨t, ht, htI, r, hrOriented, hr, hrTail⟩ :=
        (hEachRaw rho hrho).1 hb
      let q : Fin (kI * 2 + kII * 2) := finSumFinEquiv (Sum.inl r)
      refine ⟨t, ht, htI, q, ?_, ?_, ?_⟩
      · simp only [large, BinaryScaleLarge, binaryScaleLabel, q,
          Equiv.symm_apply_apply, Sum.elim_inl]
        simpa [largeI,
          ClassicalTypeIShellScaleLarge, classicalTypeIShellScaleN,
          classicalTypeIShellScaleCoeff, classicalTypeIShellScalePair] using hr
      · simp only [classicalBinaryShellScaleSign, binaryScaleLabel, q,
          Equiv.symm_apply_apply, Sum.elim_inl]
        simpa only [H] using hrOriented
      · intro r' hr'
        have hqr : binaryScaleLabel q = Sum.inl r := by
          simp only [q, binaryScaleLabel, Equiv.symm_apply_apply]
        have hrr : r = r' := Sum.inl_injective (hqr.symm.trans hr')
        subst r'
        simpa only [q, classicalBinaryShellScaleSign, binaryScaleLabel,
          Equiv.symm_apply_apply, Sum.elim_inl,
          classicalTypeIShellScalePair] using hrTail
    · obtain ⟨t, ht, htI, rII, hrOriented, hr⟩ :=
        (hEachRaw rho hrho).2 hb
      let q : Fin (kI * 2 + kII * 2) := finSumFinEquiv (Sum.inr rII)
      refine ⟨t, ht, htI, q, ?_, ?_, ?_⟩
      · simp only [large, BinaryScaleLarge, binaryScaleLabel, q,
          Equiv.symm_apply_apply, Sum.elim_inr]
        simpa [largeII,
          ClassicalTypeIIShellScaleLarge, classicalTypeIIShellScaleN,
          classicalTypeIIShellScaleCoeff, classicalTypeIIShellScalePair] using hr
      · simp only [classicalBinaryShellScaleSign, binaryScaleLabel, q,
          Equiv.symm_apply_apply, Sum.elim_inr]
        simpa only [H] using hrOriented
      · intro rI hrI
        have hqr : binaryScaleLabel q = Sum.inr rII := by
          simp only [q, binaryScaleLabel, Equiv.symm_apply_apply]
        have hneq :
            (Sum.inr rII : Sum (Fin (kI * 2)) (Fin (kII * 2))) ≠
              Sum.inl rI := by simp
        exact False.elim (hneq (hqr.symm.trans hrI))
  let shift : Complex → Real := fun rho =>
    if h : rho ∈ absoluteDyadicZeroSlab sigma U then
      Classical.choose (hEach rho h) else rho.im
  let scale : Complex → Fin (kI * 2 + kII * 2) := fun rho =>
    if h : rho ∈ absoluteDyadicZeroSlab sigma U then
      Classical.choose (Classical.choose_spec (hEach rho h)).2.2
    else ⟨0, hK⟩
  let representative := detectorRepresentative
    (absoluteDyadicZeroSlab sigma U) scale shift
  have hShiftRaw : ∀ rho, rho ∈ absoluteDyadicZeroSlab sigma U →
      |rho.im - shift rho| ≤ H := by
    intro rho hrho
    dsimp only [shift]
    rw [dif_pos hrho]
    exact (Classical.choose_spec (hEach rho hrho)).1
  have hRepShift : ∀ rho, rho ∈ absoluteDyadicZeroSlab sigma U →
      |rho.im - representative rho| ≤ H + 1 := by
    intro rho hrho
    exact abs_ordinate_sub_detectorRepresentative_le
      (absoluteDyadicZeroSlab sigma U) scale Complex.im shift H
      hShiftRaw hrho
  have hLocalHeight : max (Real.exp 2) 8 ≤ 2 * U := by
    apply max_le
    · exact exp_two_le_eight_detector.trans (by linarith [hT₀.trans hU])
    · linarith [hT₀.trans hU]
  have hUnitLocal : ∀ z : Int,
      (∑ rho ∈ (absoluteDyadicZeroSlab sigma U).filter
        (fun y => (z : Real) ≤ y.im ∧ y.im < (z : Real) + 1),
        zeroMultiplicity rho) ≤ sharpShellLocalMultiplicityCap U := by
    intro z
    exact absoluteDyadicZeroSlab_unitBin_multiplicity_le sigma U z
      (by linarith) hLocalHeight
  have hRepLocal : ∀ t : Real,
      (∑ rho ∈ (absoluteDyadicZeroSlab sigma U).filter
        (fun z => representative z = t), zeroMultiplicity rho) ≤
        (2 * ⌈H + 1⌉₊ + 1) * sharpShellLocalMultiplicityCap U := by
    intro t
    exact detectorRepresentative_fiber_weight_le
      (absoluteDyadicZeroSlab sigma U) scale zeroMultiplicity Complex.im
      shift H (sharpShellLocalMultiplicityCap U) hShiftRaw hUnitLocal t
  have hRepLarge : ∀ rho, rho ∈ absoluteDyadicZeroSlab sigma U →
      large (scale rho) (representative rho) := by
    intro rho hrho
    apply detectorRepresentative_large
      (absoluteDyadicZeroSlab sigma U) scale shift large
    · intro z hz
      dsimp only [scale, shift]
      rw [dif_pos hz, dif_pos hz]
      exact (Classical.choose_spec
        (Classical.choose_spec (hEach z hz)).2.2).1
    · exact hrho
  have hRepInterval : ∀ rho, rho ∈ absoluteDyadicZeroSlab sigma U →
      -(2 * U + H) ≤ representative rho ∧
        representative rho ≤ 2 * U + H := by
    intro rho hrho
    obtain ⟨z, hz, _hscale, _hfloor, hrep⟩ :=
      detectorRepresentative_spec
        (absoluteDyadicZeroSlab sigma U) scale shift hrho
    change -(2 * U + H) ≤
        detectorRepresentative
          (absoluteDyadicZeroSlab sigma U) scale shift rho ∧
      detectorRepresentative
          (absoluteDyadicZeroSlab sigma U) scale shift rho ≤ 2 * U + H
    rw [hrep]
    dsimp only [shift]
    rw [dif_pos hz]
    exact (Classical.choose_spec (hEach z hz)).2.1
  have hRepRadial : ∀ rho, rho ∈ absoluteDyadicZeroSlab sigma U →
      U - (H + 1) ≤ |representative rho| := by
    intro rho hrho
    have hShellLower : U ≤ |rho.im| := by
      rw [absoluteDyadicZeroSlab, Finset.mem_union] at hrho
      rcases hrho with hneg | hpos
      · have hRect := hneg
        rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
          mem_ZeroRectangle] at hRect
        rw [abs_of_neg (by linarith [hRect.1.2.2.2])]
        linarith [hRect.1.2.2.2]
      · have hRect := hpos
        rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
          mem_ZeroRectangle] at hRect
        rw [abs_of_nonneg (by linarith [hRect.1.2.2.1])]
        exact hRect.1.2.2.1
    have hTriangle : |rho.im| ≤ |rho.im - representative rho| +
        |representative rho| := by
      calc
        |rho.im| = |(rho.im - representative rho) + representative rho| := by ring_nf
        _ ≤ |rho.im - representative rho| + |representative rho| := abs_add_le _ _
    linarith [hRepShift rho hrho]
  have hRepOriented : ∀ rho, rho ∈ absoluteDyadicZeroSlab sigma U →
      if classicalBinaryShellScaleSign (scale rho) = 0 then
        U - H ≤ representative rho
      else representative rho ≤ -(U - H) := by
    intro rho hrho
    obtain ⟨z, hz, hscale, _hfloor, hrep⟩ :=
      detectorRepresentative_spec
        (absoluteDyadicZeroSlab sigma U) scale shift hrho
    have hChosen := (Classical.choose_spec
      (Classical.choose_spec (hEach z hz)).2.2).2
    change if classicalBinaryShellScaleSign (scale rho) = 0 then
        U - H ≤ detectorRepresentative
          (absoluteDyadicZeroSlab sigma U) scale shift rho
      else detectorRepresentative
          (absoluteDyadicZeroSlab sigma U) scale shift rho ≤ -(U - H)
    rw [hrep, ← hscale]
    simp only [scale, shift, dif_pos hz]
    exact hChosen.1
  have hRepLong : ∀ rho, rho ∈ absoluteDyadicZeroSlab sigma U →
      ∀ r : Fin (kI * 2), binaryScaleLabel (scale rho) = Sum.inl r →
        (3 / 4) * (q0 / 2) ≤
          ‖classicalZetaLongTail Y A
            ((sigma : Complex) + Complex.I *
              (((if classicalBinaryShellScaleSign (scale rho) = 0 then
                  representative rho else -representative rho) : Real) :
                Complex))‖ := by
    intro rho hrho r hr
    obtain ⟨z, hz, hscale, _hfloor, hrep⟩ :=
      detectorRepresentative_spec
        (absoluteDyadicZeroSlab sigma U) scale shift hrho
    have hrz : binaryScaleLabel (scale z) = Sum.inl r := by
      rw [hscale]
      exact hr
    have hChosen := (Classical.choose_spec
      (Classical.choose_spec (hEach z hz)).2.2).2.2
    change (3 / 4) * (q0 / 2) ≤
      ‖classicalZetaLongTail Y A
        ((sigma : Complex) + Complex.I *
          (((if classicalBinaryShellScaleSign (scale rho) = 0 then
              detectorRepresentative
                (absoluteDyadicZeroSlab sigma U) scale shift rho
            else -detectorRepresentative
                (absoluteDyadicZeroSlab sigma U) scale shift rho) : Real) :
            Complex))‖
    rw [hrep, ← hscale]
    simp only [scale, shift, dif_pos hz]
    apply hChosen r
    simpa only [scale, dif_pos hz] using hrz
  refine ⟨⟨kI, kII, rfl, rfl, hkI, hkII, shift, scale,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simpa only [H, representative] using hRepShift
  · simpa only [H, representative] using hRepLocal
  · intro label
    exact isSeparated_detectorRepresentative_color
      (absoluteDyadicZeroSlab sigma U) scale shift label
  · simpa only [large, BinaryScaleLarge, largeI, largeII, A, q0, kI, kII,
      representative] using hRepLarge
  · simpa only [A, q0, kI, representative] using hRepLong
  · simpa only [H, representative] using hRepInterval
  · simpa only [H, representative] using hRepRadial
  · simpa only [H, representative] using hRepOriented

#print axioms exists_classicalBinaryShellDetectorData

end

end GafniTao
