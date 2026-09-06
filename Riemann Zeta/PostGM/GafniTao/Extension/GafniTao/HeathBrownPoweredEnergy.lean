import GafniTao.HeathBrownFiniteMixedEnergy
import GafniTao.RealEnergyPowerColoring

/-!
# Exact powering before the finite Heath--Brown relation

This is the energy-preserving power transform needed in the low and middle
Heath--Brown cells.  A large polynomial is powered pointwise, the selected
dyadic block is coloured independently in all four coordinates, and each of
the four resulting families is consumed by the finite second/fourth-moment
relation.  No cardinality-only subset is substituted for this colouring.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The normalized threshold furnished by exact positive-sign powering. -/
noncomputable def heathBrownPoweredThreshold
    (N p : Nat) (L Cp eta : Real) : Real :=
  (L ^ p / (Cp * ((2 ^ p * N ^ p : Nat) : Real) ^ eta)) / p

/-- Exact finite power-and-colour consumer for fixed, already-selected
constants in the finite Heath--Brown relation.  Keeping the source relation
outside the physical parameters is what makes its height cutoff genuinely
uniform. -/
theorem finite_source_powered_energy_heathBrown_of_relation
    (epsilon B : Real) (N p : Nat) (a : Nat → Complex)
    (Cp eta L : Real) (W : Finset Real)
    (C0 C2 C4 B0 : Real)
    (hN : 0 < N) (hp : 0 < p)
    (hCp : 0 < Cp) (heta : 0 < eta) (hL : 0 < L)
    (hC0 : 0 < C0) (hB0 : 1 ≤ B0)
    (hHB : ∀ (M : Nat) (T V : Real) (W' : Finset Real)
        (b : Nat → Complex),
      0 < M → B0 ≤ T → (M : Real) ≤ T → 0 ≤ V →
      IsSeparated 1 W' → InBaseInterval T W' →
      (∀ n ∈ dyadicInterval M, ‖b n‖ ≤ 1) →
      (∀ t ∈ W', V ≤ ‖sourceDirichletPoly M b t‖) →
      (ApproxAddEnergy 1 W' : Real) * V ^ 2 ≤
        C0 * T ^ (epsilon / 2) *
          Real.sqrt (C2 * T ^ (epsilon / 2) *
            heathBrownSecondMomentShape T M W') *
          Real.sqrt (C4 * T ^ (epsilon / 2) *
            heathBrownFourthMomentShape T M W'))
    (hSep : IsSeparated 1 W) (hBase : InBaseInterval B W)
    (hPow : ∀ m : Nat, 0 < m →
      ‖finitePowCoeff N p (conjugateCoeffs a) m‖ ≤
        Cp * (m : Real) ^ eta)
    (hLarge : ∀ t ∈ W, L ≤ ‖sourceDirichletPoly N a t‖) :
    B0 ≤ B →
        (∀ r ∈ Finset.range p, (2 ^ r * N ^ p : Real) ≤ B) →
        ∃ label : Fin 4 → Fin p, ∃ Wi : Fin 4 → Finset Real,
          (∀ i : Fin 4, Wi i ⊆ W) ∧
          (∀ i : Fin 4, IsSeparated 1 (Wi i)) ∧
          (∀ i : Fin 4, InBaseInterval B (Wi i)) ∧
          (∀ i : Fin 4, ∀ n ∈ dyadicInterval
              (2 ^ (label i).val * N ^ p),
            ‖sourceNormalizedFinitePoweredCoeffs N p a Cp eta n‖ ≤ 1) ∧
          (∀ i : Fin 4, ∀ t ∈ Wi i,
            heathBrownPoweredThreshold N p L Cp eta ≤
              ‖sourceDirichletPoly (2 ^ (label i).val * N ^ p)
                (sourceNormalizedFinitePoweredCoeffs N p a Cp eta) t‖) ∧
          4 * (ApproxAddEnergy 1 W : Real) ≤
            ((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card *
              (∑ i : Fin 4,
                heathBrownFiniteFamilyBound epsilon C0 C2 C4 B
                  (heathBrownPoweredThreshold N p L Cp eta)
                  (2 ^ (label i).val * N ^ p) (Wi i)) := by
  intro hB hMUpper
  have hEach : ∀ t ∈ W, ∃ r ∈ Finset.range p,
      heathBrownPoweredThreshold N p L Cp eta ≤
        ‖sourceDirichletPoly (2 ^ r * N ^ p)
          (sourceNormalizedFinitePoweredCoeffs N p a Cp eta) t‖ := by
    intro t ht
    simpa only [heathBrownPoweredThreshold] using
      exists_source_powered_dyadic_index N p a Cp eta L t
        hN hp hCp hL.le (hLarge t ht)
  let color : Real → Fin p := fun t =>
    if ht : t ∈ W then
      ⟨Classical.choose (hEach t ht),
        Finset.mem_range.mp (Classical.choose_spec (hEach t ht)).1⟩
    else ⟨0, hp⟩
  letI : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  obtain ⟨label, hColorEnergy⟩ :=
    exists_real_energy_color_classes 1 W color
  let Wi : Fin 4 → Finset Real := fun i =>
    W.filter (fun t => color t = label i)
  have hSubset : ∀ i : Fin 4, Wi i ⊆ W := by
    intro i t ht
    exact (Finset.mem_filter.mp ht).1
  have hSepWi : ∀ i : Fin 4, IsSeparated 1 (Wi i) := by
    intro i x hx y hy hxy
    exact hSep x (hSubset i hx) y (hSubset i hy) hxy
  have hBaseWi : ∀ i : Fin 4, InBaseInterval B (Wi i) := by
    intro i t ht
    exact hBase t (hSubset i ht)
  have hLabelLarge : ∀ i : Fin 4, ∀ t ∈ Wi i,
      heathBrownPoweredThreshold N p L Cp eta ≤
        ‖sourceDirichletPoly (2 ^ (label i).val * N ^ p)
          (sourceNormalizedFinitePoweredCoeffs N p a Cp eta) t‖ := by
    intro i t ht
    have htW : t ∈ W := hSubset i ht
    have hColorEq : color t = label i := (Finset.mem_filter.mp ht).2
    have hSpec := Classical.choose_spec (hEach t htW)
    have hIndex : Classical.choose (hEach t htW) = (label i).val := by
      have hFin : (⟨Classical.choose (hEach t htW),
          Finset.mem_range.mp hSpec.1⟩ : Fin p) = label i := by
        simpa [color, htW] using hColorEq
      exact congrArg Fin.val hFin
    rw [← hIndex]
    exact hSpec.2
  have hUnit : ∀ i : Fin 4, ∀ n ∈
      dyadicInterval (2 ^ (label i).val * N ^ p),
      ‖sourceNormalizedFinitePoweredCoeffs N p a Cp eta n‖ ≤ 1 := by
    intro i n hn
    exact norm_sourceNormalizedFinitePoweredCoeffs_le_one hN hCp heta
      (label i).isLt hn hPow
  have hThresholdPos : 0 < heathBrownPoweredThreshold N p L Cp eta := by
    unfold heathBrownPoweredThreshold
    have hpReal : (0 : Real) < p := by exact_mod_cast hp
    positivity
  have hEachHB : ∀ i : Fin 4,
      (ApproxAddEnergy 1 (Wi i) : Real) ≤
        heathBrownFiniteFamilyBound epsilon C0 C2 C4 B
          (heathBrownPoweredThreshold N p L Cp eta)
          (2 ^ (label i).val * N ^ p) (Wi i) := by
    intro i
    by_cases hWi : (Wi i).Nonempty
    · have hMi : 0 < 2 ^ (label i).val * N ^ p :=
        Nat.mul_pos (pow_pos (by omega) _) (pow_pos hN p)
      have hMiB : ((2 ^ (label i).val * N ^ p : Nat) : Real) ≤ B := by
        have hRaw := hMUpper (label i).val
          (Finset.mem_range.mpr (label i).isLt)
        exact_mod_cast hRaw
      have hi := hHB (2 ^ (label i).val * N ^ p) B
        (heathBrownPoweredThreshold N p L Cp eta) (Wi i)
        (sourceNormalizedFinitePoweredCoeffs N p a Cp eta)
        hMi hB hMiB
        hThresholdPos.le (hSepWi i) (hBaseWi i) (hUnit i)
        (hLabelLarge i)
      unfold heathBrownFiniteFamilyBound
      rw [le_div_iff₀ (sq_pos_of_pos hThresholdPos)]
      exact hi
    · have hEmpty : Wi i = ∅ := Finset.not_nonempty_iff_eq_empty.mp hWi
      rw [hEmpty]
      simp only [ApproxAddEnergy, approximateAdditiveQuadruples,
        Finset.empty_product, Finset.filter_empty, Finset.card_empty,
        Nat.cast_zero]
      exact heathBrownFiniteFamilyBound_nonneg hC0.le
        (zero_le_one.trans (hB0.trans hB))
  have hMixed := four_mul_mixedApproxAddEnergy_le_window_mul_sum_self
    (eta := (1 : Real)) (hSepWi 0) (hSepWi 1) (hSepWi 2) (hSepWi 3)
  have hColorReal : (ApproxAddEnergy 1 W : Real) ≤
      (p ^ 4 : Real) *
        (MixedApproxAddEnergy 1 (Wi 0) (Wi 1) (Wi 2) (Wi 3) : Real) := by
    have hColorNat : ApproxAddEnergy 1 W ≤ p ^ 4 *
        MixedApproxAddEnergy 1 (Wi 0) (Wi 1) (Wi 2) (Wi 3) := by
      simpa [Wi] using hColorEnergy
    exact_mod_cast hColorNat
  refine ⟨label, Wi, hSubset, hSepWi, hBaseWi, hUnit, hLabelLarge, ?_⟩
  rw [Nat.cast_pow]
  calc
    4 * (ApproxAddEnergy 1 W : Real) ≤
        4 * ((p ^ 4 : Real) *
          (MixedApproxAddEnergy 1 (Wi 0) (Wi 1) (Wi 2) (Wi 3) : Real)) := by
      gcongr
    _ = (p ^ 4 : Real) *
        (4 * (MixedApproxAddEnergy 1 (Wi 0) (Wi 1) (Wi 2) (Wi 3) : Real)) := by
      ring
    _ ≤ (p ^ 4 : Real) * (doubleFloorDefectWindow 1).card *
        ((ApproxAddEnergy 1 (Wi 0) : Real) +
          (ApproxAddEnergy 1 (Wi 1) : Real) +
          (ApproxAddEnergy 1 (Wi 2) : Real) +
          (ApproxAddEnergy 1 (Wi 3) : Real)) := by
      calc
        (p : Real) ^ 4 *
            (4 * (MixedApproxAddEnergy 1
              (Wi 0) (Wi 1) (Wi 2) (Wi 3) : Real)) ≤
            (p : Real) ^ 4 *
              ((doubleFloorDefectWindow 1).card *
                ((ApproxAddEnergy 1 (Wi 0) : Real) +
                  (ApproxAddEnergy 1 (Wi 1) : Real) +
                  (ApproxAddEnergy 1 (Wi 2) : Real) +
                  (ApproxAddEnergy 1 (Wi 3) : Real))) :=
          mul_le_mul_of_nonneg_left hMixed (by positivity)
        _ = _ := by ring
    _ ≤ (p ^ 4 : Real) * (doubleFloorDefectWindow 1).card *
        (∑ i : Fin 4,
          heathBrownFiniteFamilyBound epsilon C0 C2 C4 B
            (heathBrownPoweredThreshold N p L Cp eta)
            (2 ^ (label i).val * N ^ p) (Wi i)) := by
      rw [Fin.sum_univ_four]
      gcongr <;> apply hEachHB

/-- Exact finite power-and-colour consumer for the Heath--Brown relation. -/
theorem finite_source_powered_energy_heathBrown_native
    (epsilon B : Real) (N p : Nat) (a : Nat → Complex)
    (Cp eta L : Real) (W : Finset Real)
    (hepsilon : 0 < epsilon) (hN : 0 < N) (hp : 0 < p)
    (hCp : 0 < Cp) (heta : 0 < eta) (hL : 0 < L)
    (hSep : IsSeparated 1 W) (hBase : InBaseInterval B W)
    (hPow : ∀ m : Nat, 0 < m →
      ‖finitePowCoeff N p (conjugateCoeffs a) m‖ ≤
        Cp * (m : Real) ^ eta)
    (hLarge : ∀ t ∈ W, L ≤ ‖sourceDirichletPoly N a t‖) :
    ∃ C0 C2 C4 B0 : Real,
      0 < C0 ∧ 0 < C2 ∧ 0 < C4 ∧ 1 ≤ B0 ∧
      (B0 ≤ B →
        (∀ r ∈ Finset.range p, (2 ^ r * N ^ p : Real) ≤ B) →
        ∃ label : Fin 4 → Fin p, ∃ Wi : Fin 4 → Finset Real,
          (∀ i : Fin 4, Wi i ⊆ W) ∧
          (∀ i : Fin 4, IsSeparated 1 (Wi i)) ∧
          (∀ i : Fin 4, InBaseInterval B (Wi i)) ∧
          (∀ i : Fin 4, ∀ n ∈ dyadicInterval
              (2 ^ (label i).val * N ^ p),
            ‖sourceNormalizedFinitePoweredCoeffs N p a Cp eta n‖ ≤ 1) ∧
          (∀ i : Fin 4, ∀ t ∈ Wi i,
            heathBrownPoweredThreshold N p L Cp eta ≤
              ‖sourceDirichletPoly (2 ^ (label i).val * N ^ p)
                (sourceNormalizedFinitePoweredCoeffs N p a Cp eta) t‖) ∧
          4 * (ApproxAddEnergy 1 W : Real) ≤
            ((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card *
              (∑ i : Fin 4,
                heathBrownFiniteFamilyBound epsilon C0 C2 C4 B
                  (heathBrownPoweredThreshold N p L Cp eta)
                  (2 ^ (label i).val * N ^ p) (Wi i))) := by
  obtain ⟨C0, C2, C4, B0, hC0, hC2, hC4, hB0, hHB⟩ :=
    heathBrownFiniteEnergyRelation_native epsilon hepsilon
  refine ⟨C0, C2, C4, B0, hC0, hC2, hC4, hB0, ?_⟩
  exact finite_source_powered_energy_heathBrown_of_relation
    epsilon B N p a Cp eta L W C0 C2 C4 B0 hN hp hCp heta hL
      hC0 hB0 hHB hSep hBase hPow hLarge

#print axioms finite_source_powered_energy_heathBrown_of_relation
#print axioms finite_source_powered_energy_heathBrown_native

end

end GafniTao
