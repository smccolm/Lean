import GafniTao.WeightedSubfamilyEnergy
import GafniTao.RealEnergyPowerColoring

/-!
# Four-coordinate shifted extraction for real additive energy

This is the real-valued counterpart of the weighted zero-family extractor.
It is used after the Type-I reflection sign has been fixed.  All four
coordinates are pigeonholed simultaneously, so the argument retains
additive energy rather than merely the cardinality of a selected family.
-/

open scoped BigOperators

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

theorem shifted_real_quadruple_defect_le
    {eta H : Real} {W : Finset Real}
    {q : (Real × Real) × (Real × Real)}
    (hq : q ∈ approximateAdditiveQuadruples eta W)
    (representative : Real → Real)
    (hShift : ∀ i : Fin 4,
      |realQuadrupleCoord i q - representative (realQuadrupleCoord i q)| ≤ H) :
    |representative q.1.1 + representative q.1.2 -
        representative q.2.1 - representative q.2.2| ≤ eta + 4 * H := by
  have h0 := hShift 0
  have h1 := hShift 1
  have h2 := hShift 2
  have h3 := hShift 3
  have hRes : |q.1.1 + q.1.2 - q.2.1 - q.2.2| ≤ eta := by
    exact (Finset.mem_filter.mp hq).2
  simp only [realQuadrupleCoord] at h0 h1 h2 h3
  rw [abs_le] at h0 h1 h2 h3 hRes ⊢
  constructor <;> linarith

/-- Simultaneous four-coordinate colour extraction followed by a possibly
many-to-one shifted representative.  The explicit fourth power of the fibre
cap is the complete loss from this map. -/
theorem exists_mixed_real_energy_color_classes_with_representative
    {Kappa : Type*} [Fintype Kappa] [DecidableEq Kappa] [Nonempty Kappa]
    (W : Finset Real) (eta H : Real) (L : Nat)
    (color : Real → Kappa) (representative : Real → Real)
    (hShift : ∀ x, x ∈ W → |x - representative x| ≤ H)
    (hLocal : ∀ t : Real,
      (W.filter (fun x => representative x = t)).card ≤ L) :
    ∃ label : Fin 4 → Kappa,
      let Wi := fun i : Fin 4 =>
        (W.filter (fun x => color x = label i)).image representative
      ApproxAddEnergy eta W ≤
        (Fintype.card Kappa) ^ 4 * L ^ 4 *
          MixedApproxAddEnergy (eta + 4 * H) (Wi 0) (Wi 1) (Wi 2) (Wi 3) := by
  classical
  let colorQ : ((Real × Real) × (Real × Real)) → Fin 4 → Kappa :=
    fun q i => color (realQuadrupleCoord i q)
  obtain ⟨label, hColor⟩ := exists_four_coordinate_weighted_color_fiber_type
    (approximateAdditiveQuadruples eta W) (fun _ => 1) colorQ
  let Q := (approximateAdditiveQuadruples eta W).filter
    (fun q => colorQ q = label)
  let Wi := fun i : Fin 4 =>
    (W.filter (fun x => color x = label i)).image representative
  let U := mixedApproximateAdditiveQuadruples (eta + 4 * H)
    (Wi 0) (Wi 1) (Wi 2) (Wi 3)
  have hQ : Q ⊆ quadrupleProduct W := by
    intro q hq
    have hqSource : q ∈ approximateAdditiveQuadruples eta W :=
      (Finset.mem_filter.mp hq).1
    exact (Finset.mem_filter.mp hqSource).1
  have hMaps : Set.MapsTo (mappedQuadruple representative) (Q : Set _) (U : Set _) := by
    intro q hq
    have hqFilter := Finset.mem_filter.mp hq
    have hqSource := hqFilter.1
    have hqColor := hqFilter.2
    have hqData := Finset.mem_filter.mp hqSource
    have hSource :
        q.1.1 ∈ W ∧ q.1.2 ∈ W ∧ q.2.1 ∈ W ∧ q.2.2 ∈ W := by
      simpa only [Finset.mem_product, and_assoc] using hqData.1
    have hcoord (i : Fin 4) :
        color (realQuadrupleCoord i q) = label i := congrFun hqColor i
    have hcoordMem (i : Fin 4) : realQuadrupleCoord i q ∈ W := by
      fin_cases i <;> simp only [realQuadrupleCoord] <;> tauto
    have hWi (i : Fin 4) : representative (realQuadrupleCoord i q) ∈ Wi i := by
      apply Finset.mem_image.mpr
      exact ⟨realQuadrupleCoord i q,
        Finset.mem_filter.mpr ⟨hcoordMem i, hcoord i⟩, rfl⟩
    have hDefect := shifted_real_quadruple_defect_le hqSource representative
      (fun i => hShift _ (hcoordMem i))
    unfold U mixedApproximateAdditiveQuadruples
    apply Finset.mem_filter.mpr
    constructor
    · unfold quadrupleProductOf
      exact Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨hWi 0, hWi 1⟩,
          Finset.mem_product.mpr ⟨hWi 2, hWi 3⟩⟩
    · simpa only [mappedQuadruple, realQuadrupleCoord] using hDefect
  have hTransfer :
      (∑ q ∈ Q, weightedQuadruple (fun _ : Real => 1) q) ≤ L ^ 4 * U.card := by
    apply weighted_quadruple_sum_le_fourth_power_mul_card
      W Q U (fun _ : Real => 1) representative L hQ hMaps
    intro t
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using hLocal t
  refine ⟨label, ?_⟩
  dsimp only
  change ApproxAddEnergy eta W ≤
    (Fintype.card Kappa) ^ 4 * L ^ 4 *
      MixedApproxAddEnergy (eta + 4 * H) (Wi 0) (Wi 1) (Wi 2) (Wi 3)
  calc
    ApproxAddEnergy eta W =
        ∑ q ∈ approximateAdditiveQuadruples eta W,
          weightedQuadruple (fun _ : Real => 1) q := by
      rw [ApproxAddEnergy]
      simp [weightedQuadruple]
    _ ≤ (Fintype.card Kappa) ^ 4 *
        ∑ q ∈ Q, weightedQuadruple (fun _ : Real => 1) q := hColor
    _ ≤ (Fintype.card Kappa) ^ 4 * (L ^ 4 * U.card) :=
      Nat.mul_le_mul_left _ hTransfer
    _ = (Fintype.card Kappa) ^ 4 * L ^ 4 *
        MixedApproxAddEnergy (eta + 4 * H) (Wi 0) (Wi 1) (Wi 2) (Wi 3) := by
      simp only [U, MixedApproxAddEnergy, mul_assoc]

theorem unit_bin_card_le_one_of_one_separated
    (W : Finset Real) (hW : IsSeparated 1 W) (z : Int) :
    (W.filter (fun x => (z : Real) ≤ x ∧ x < (z : Real) + 1)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  have hx' := Finset.mem_filter.mp hx
  have hy' := Finset.mem_filter.mp hy
  by_contra hxy
  have hsep : 1 ≤ |x - y| := by
    simpa only [Real.dist_eq] using hW x hx'.1 y hy'.1 hxy
  have hsmall : |x - y| < 1 := by
    rw [abs_lt]
    constructor <;> linarith [hx'.2.1, hx'.2.2, hy'.2.1, hy'.2.2]
  exact (not_lt_of_ge hsep) hsmall

/-- Exact real shifted-dyadic extraction.  The input family is already
one-separated; therefore every half-open unit bin has cardinality at most
one and no unrecorded local multiplicity is introduced. -/
theorem finite_shifted_dyadic_real_energy_extraction
    (W : Finset Real) (hW : IsSeparated 1 W)
    (eta H : Real) (k : Nat) (hk : 0 < k)
    (large : Fin k → Real → Prop) (inInterval : Real → Prop)
    (hEach : ∀ x, x ∈ W → ∃ t : Real,
      |x - t| ≤ H ∧ inInterval t ∧ ∃ r : Fin k, large r t) :
    ∃ label : Fin 4 → (Fin k × Fin 2),
      let shift : Real → Real := fun x =>
        if h : x ∈ W then Classical.choose (hEach x h) else x
      let scale : Real → Fin k := fun x =>
        if h : x ∈ W then
          Classical.choose (Classical.choose_spec (hEach x h)).2.2
        else ⟨0, hk⟩
      let representative := detectorRepresentative W scale shift
      let Wi := fun i : Fin 4 =>
        (W.filter (fun x => detectorColor scale shift x = label i)).image
          representative
      (∀ i : Fin 4, IsSeparated 1 (Wi i)) ∧
      (∀ i : Fin 4, ∀ t, t ∈ Wi i → large (label i).1 t) ∧
      (∀ i : Fin 4, ∀ t, t ∈ Wi i → inInterval t) ∧
      ApproxAddEnergy eta W ≤
        (2 * k) ^ 4 * (2 * ⌈H + 1⌉₊ + 1) ^ 4 *
          MixedApproxAddEnergy (eta + 4 * (H + 1))
            (Wi 0) (Wi 1) (Wi 2) (Wi 3) := by
  classical
  let shift : Real → Real := fun x =>
    if h : x ∈ W then Classical.choose (hEach x h) else x
  have hShiftSpec : ∀ x, x ∈ W →
      |x - shift x| ≤ H ∧ inInterval (shift x) ∧
        ∃ r : Fin k, large r (shift x) := by
    intro x hx
    dsimp only [shift]
    rw [dif_pos hx]
    exact Classical.choose_spec (hEach x hx)
  let scale : Real → Fin k := fun x =>
    if h : x ∈ W then
      Classical.choose (Classical.choose_spec (hEach x h)).2.2
    else ⟨0, hk⟩
  have hScaleSpec : ∀ x, x ∈ W → large (scale x) (shift x) := by
    intro x hx
    dsimp only [scale]
    rw [dif_pos hx]
    simpa only [shift, dif_pos hx] using
      Classical.choose_spec (Classical.choose_spec (hEach x hx)).2.2
  let representative := detectorRepresentative W scale shift
  let color := detectorColor scale shift
  let Lrep := 2 * ⌈H + 1⌉₊ + 1
  have hRepresentativeShift : ∀ x, x ∈ W →
      |x - representative x| ≤ H + 1 := by
    intro x hx
    exact abs_ordinate_sub_detectorRepresentative_le
      W scale id shift H (fun y hy => by simpa using (hShiftSpec y hy).1) hx
  have hRepresentativeLocal : ∀ t : Real,
      (W.filter (fun x => representative x = t)).card ≤ Lrep := by
    intro t
    have hLocal : ∀ z : Int,
        (∑ x ∈ W.filter
          (fun y => (z : Real) ≤ id y ∧ id y < (z : Real) + 1), 1) ≤ 1 := by
      intro z
      simpa only [id_eq, Finset.sum_const, nsmul_eq_mul, mul_one] using
        unit_bin_card_le_one_of_one_separated W hW z
    have h := detectorRepresentative_fiber_weight_le
      W scale (fun _ : Real => 1) id shift H 1
        (fun y hy => by simpa using (hShiftSpec y hy).1) hLocal t
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.mul_one,
      Lrep] using h
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨label, hEnergy⟩ :=
    exists_mixed_real_energy_color_classes_with_representative
      W eta (H + 1) Lrep color representative
        hRepresentativeShift hRepresentativeLocal
  let Wi := fun i : Fin 4 =>
    (W.filter (fun x => color x = label i)).image representative
  have hSeparated : ∀ i : Fin 4, IsSeparated 1 (Wi i) := by
    intro i
    exact isSeparated_detectorRepresentative_color W scale shift (label i)
  have hLarge : ∀ i : Fin 4, ∀ t, t ∈ Wi i → large (label i).1 t := by
    intro i t ht
    obtain ⟨x, hxColor, rfl⟩ := Finset.mem_image.mp ht
    have hx := Finset.mem_filter.mp hxColor
    have hscale : scale x = (label i).1 := congrArg Prod.fst hx.2
    rw [← hscale]
    exact detectorRepresentative_large W scale shift large hScaleSpec hx.1
  have hInterval : ∀ i : Fin 4, ∀ t, t ∈ Wi i → inInterval t := by
    intro i t ht
    obtain ⟨x, hxColor, rfl⟩ := Finset.mem_image.mp ht
    have hx := (Finset.mem_filter.mp hxColor).1
    obtain ⟨y, hy, _hscale, _hfloor, hrep⟩ :=
      detectorRepresentative_spec W scale shift hx
    change inInterval (detectorRepresentative W scale shift x)
    rw [hrep]
    exact (hShiftSpec y hy).2.1
  refine ⟨label, ?_⟩
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Wi, color, representative, scale, shift] using hSeparated
  · simpa only [Wi, color, representative, scale, shift] using hLarge
  · simpa only [Wi, color, representative, scale, shift] using hInterval
  have hCard : Fintype.card (Fin k × Fin 2) = 2 * k := by simp [mul_comm]
  simpa only [hCard, Lrep, Wi, color, representative, scale, shift, add_assoc]
    using hEnergy

#print axioms shifted_real_quadruple_defect_le
#print axioms exists_mixed_real_energy_color_classes_with_representative
#print axioms unit_bin_card_le_one_of_one_separated
#print axioms finite_shifted_dyadic_real_energy_extraction

end

end GafniTao
