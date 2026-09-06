import GafniTao.EnergyDetectorSharpSlab

/-!
# Weighted additive energy on an arbitrary zero subfamily

The source detector is first available on signed dyadic height shells.  This
module supplies the exact finite energy extraction for such a shell, while
retaining arbitrary natural multiplicities.
-/

open scoped BigOperators

namespace GafniTao

noncomputable section

/-- Tolerance-`eta` quadruples from an arbitrary finite complex family. -/
noncomputable def resonantQuadruplesOn
    (S : Finset Complex) (eta : Real) :
    Finset ((Complex × Complex) × (Complex × Complex)) :=
  (quadrupleProduct S).filter fun q =>
    |q.1.1.im + q.1.2.im - q.2.1.im - q.2.2.im| <= eta

/-- Product-multiplicity weighted energy of an arbitrary finite family. -/
noncomputable def weightedAdditiveEnergyOn
    (S : Finset Complex) (weight : Complex -> Nat) (eta : Real) : Nat :=
  ∑ q ∈ resonantQuadruplesOn S eta, weightedQuadruple weight q

theorem mem_resonantQuadruplesOn
    {S : Finset Complex} {eta : Real}
    {q : (Complex × Complex) × (Complex × Complex)} :
    q ∈ resonantQuadruplesOn S eta ↔
      q.1.1 ∈ S ∧ q.1.2 ∈ S ∧ q.2.1 ∈ S ∧ q.2.2 ∈ S ∧
        |q.1.1.im + q.1.2.im - q.2.1.im - q.2.2.im| <= eta := by
  classical
  simp only [resonantQuadruplesOn, Finset.mem_filter, quadrupleProduct]
  aesop

theorem shifted_subfamily_quadruple_defect_le
    {S : Finset Complex} {eta H : Real}
    {q : (Complex × Complex) × (Complex × Complex)}
    (hq : q ∈ resonantQuadruplesOn S eta)
    (representative : Complex -> Real)
    (hShift : forall i : Fin 4,
      |(complexQuadrupleCoord i q).im -
          representative (complexQuadrupleCoord i q)| <= H) :
    |representative q.1.1 + representative q.1.2 -
        representative q.2.1 - representative q.2.2| <= eta + 4 * H := by
  have h0 := hShift 0
  have h1 := hShift 1
  have h2 := hShift 2
  have h3 := hShift 3
  have hRes := (mem_resonantQuadruplesOn.mp hq).2.2.2.2
  simp only [complexQuadrupleCoord] at h0 h1 h2 h3
  rw [abs_le] at h0 h1 h2 h3 hRes ⊢
  constructor <;> linarith

/-- Four-coordinate detector extraction for an arbitrary weighted complex
subfamily.  This is the shell-level analogue of
`exists_mixed_energy_color_classes`. -/
theorem exists_mixed_energy_color_classes_on
    {Kappa : Type*} [Fintype Kappa] [DecidableEq Kappa] [Nonempty Kappa]
    (S : Finset Complex) (weight : Complex -> Nat) (eta H : Real) (L : Nat)
    (color : Complex -> Kappa) (representative : Complex -> Real)
    (hShift : forall rho, rho ∈ S ->
      |rho.im - representative rho| <= H)
    (hLocal : forall t : Real,
      (∑ rho ∈ S.filter (fun z => representative z = t), weight rho) <= L) :
    exists label : Fin 4 -> Kappa,
      let W := fun i : Fin 4 =>
        (S.filter (fun rho => color rho = label i)).image representative
      weightedAdditiveEnergyOn S weight eta <=
        (Fintype.card Kappa) ^ 4 * L ^ 4 *
          MixedApproxAddEnergy (eta + 4 * H) (W 0) (W 1) (W 2) (W 3) := by
  classical
  let colorQ : ((Complex × Complex) × (Complex × Complex)) ->
      Fin 4 -> Kappa := fun q i => color (complexQuadrupleCoord i q)
  obtain ⟨label, hColor⟩ := exists_four_coordinate_weighted_color_fiber_type
    (resonantQuadruplesOn S eta) (weightedQuadruple weight) colorQ
  let Q := (resonantQuadruplesOn S eta).filter (fun q => colorQ q = label)
  let W := fun i : Fin 4 =>
    (S.filter (fun rho => color rho = label i)).image representative
  let U := mixedApproximateAdditiveQuadruples (eta + 4 * H)
    (W 0) (W 1) (W 2) (W 3)
  have hQ : Q ⊆ quadrupleProduct S := by
    intro q hq
    exact Finset.filter_subset _ _ (Finset.mem_filter.mp hq).1
  have hMaps : Set.MapsTo (mappedQuadruple representative)
      (Q : Set _) (U : Set _) := by
    intro q hq
    have hqFilter := Finset.mem_filter.mp hq
    have hqRes := hqFilter.1
    have hqColor := hqFilter.2
    have hmem := mem_resonantQuadruplesOn.mp hqRes
    have hcoord (i : Fin 4) :
        color (complexQuadrupleCoord i q) = label i := congrFun hqColor i
    have hcoordMem (i : Fin 4) : complexQuadrupleCoord i q ∈ S := by
      fin_cases i <;> simp only [complexQuadrupleCoord] <;> tauto
    have hW (i : Fin 4) : representative (complexQuadrupleCoord i q) ∈ W i := by
      apply Finset.mem_image.mpr
      exact ⟨complexQuadrupleCoord i q,
        Finset.mem_filter.mpr ⟨hcoordMem i, hcoord i⟩, rfl⟩
    have hDefect := shifted_subfamily_quadruple_defect_le hqRes representative
      (fun i => hShift _ (hcoordMem i))
    unfold U mixedApproximateAdditiveQuadruples
    apply Finset.mem_filter.mpr
    constructor
    · unfold quadrupleProductOf
      apply Finset.mem_product.mpr
      exact ⟨Finset.mem_product.mpr ⟨hW 0, hW 1⟩,
        Finset.mem_product.mpr ⟨hW 2, hW 3⟩⟩
    · simpa only [mappedQuadruple, complexQuadrupleCoord] using hDefect
  have hTransfer :
      (∑ q ∈ Q, weightedQuadruple weight q) <= L ^ 4 * U.card :=
    weighted_quadruple_sum_le_fourth_power_mul_card
      S Q U weight representative L hQ hMaps hLocal
  refine ⟨label, ?_⟩
  dsimp only
  change weightedAdditiveEnergyOn S weight eta <=
    (Fintype.card Kappa) ^ 4 * L ^ 4 *
      MixedApproxAddEnergy (eta + 4 * H) (W 0) (W 1) (W 2) (W 3)
  calc
    weightedAdditiveEnergyOn S weight eta =
        ∑ q ∈ resonantQuadruplesOn S eta, weightedQuadruple weight q := rfl
    _ <= (Fintype.card Kappa) ^ 4 *
        ∑ q ∈ Q, weightedQuadruple weight q := by
      simpa only [Q] using hColor
    _ <= (Fintype.card Kappa) ^ 4 * (L ^ 4 * U.card) :=
      Nat.mul_le_mul_left _ hTransfer
    _ = (Fintype.card Kappa) ^ 4 * L ^ 4 *
        MixedApproxAddEnergy (eta + 4 * H) (W 0) (W 1) (W 2) (W 3) := by
      simp only [U, MixedApproxAddEnergy, mul_assoc]

/-- Detector representatives, parity separation, and simultaneous
four-coordinate pigeonholing for an arbitrary weighted subfamily. -/
theorem finite_shifted_dyadic_energy_extraction_on
    (S : Finset Complex) (weight : Complex -> Nat)
    (eta H : Real) (k L : Nat) (hk : 0 < k)
    (large : Fin k -> Real -> Prop) (inInterval : Real -> Prop)
    (hEach : forall rho, rho ∈ S -> exists t : Real,
      |rho.im - t| <= H ∧ inInterval t ∧
        exists r : Fin k, large r t)
    (hLocal : forall z : Int,
      (∑ rho ∈ S.filter
        (fun y => (z : Real) <= y.im ∧ y.im < (z : Real) + 1),
        weight rho) <= L) :
    exists label : Fin 4 -> (Fin k × Fin 2),
      let shift : Complex -> Real := fun rho =>
        if h : rho ∈ S then Classical.choose (hEach rho h) else rho.im
      let scale : Complex -> Fin k := fun rho =>
        if h : rho ∈ S then
          Classical.choose (Classical.choose_spec (hEach rho h)).2.2
        else ⟨0, hk⟩
      let representative := detectorRepresentative S scale shift
      let W := fun i : Fin 4 =>
        (S.filter (fun rho => detectorColor scale shift rho = label i)).image
          representative
      (forall i : Fin 4,
        RiemannZeta.GuthMaynard.IsSeparated 1 (W i)) ∧
      (forall i : Fin 4, forall t, t ∈ W i -> large (label i).1 t) ∧
      (forall i : Fin 4, forall t, t ∈ W i -> inInterval t) ∧
      weightedAdditiveEnergyOn S weight eta <=
        (2 * k) ^ 4 * ((2 * ⌈H + 1⌉₊ + 1) * L) ^ 4 *
          MixedApproxAddEnergy (eta + 4 * (H + 1))
            (W 0) (W 1) (W 2) (W 3) := by
  classical
  let shift : Complex -> Real := fun rho =>
    if h : rho ∈ S then Classical.choose (hEach rho h) else rho.im
  have hShiftSpec : forall rho, rho ∈ S ->
      |rho.im - shift rho| <= H ∧ inInterval (shift rho) ∧
        exists r : Fin k, large r (shift rho) := by
    intro rho hrho
    dsimp only [shift]
    rw [dif_pos hrho]
    exact Classical.choose_spec (hEach rho hrho)
  let scale : Complex -> Fin k := fun rho =>
    if h : rho ∈ S then
      Classical.choose (Classical.choose_spec (hEach rho h)).2.2
    else ⟨0, hk⟩
  have hScaleSpec : forall rho, rho ∈ S ->
      large (scale rho) (shift rho) := by
    intro rho hrho
    dsimp only [scale]
    rw [dif_pos hrho]
    simpa only [shift, dif_pos hrho] using
      Classical.choose_spec (Classical.choose_spec (hEach rho hrho)).2.2
  let representative := detectorRepresentative S scale shift
  let color := detectorColor scale shift
  let Lrep := (2 * ⌈H + 1⌉₊ + 1) * L
  have hRepresentativeShift : forall rho, rho ∈ S ->
      |rho.im - representative rho| <= H + 1 := by
    intro rho hrho
    exact abs_ordinate_sub_detectorRepresentative_le
      S scale Complex.im shift H (fun z hz => (hShiftSpec z hz).1) hrho
  have hRepresentativeLocal : forall t : Real,
      (∑ rho ∈ S.filter (fun z => representative z = t), weight rho) <=
        Lrep := by
    intro t
    exact detectorRepresentative_fiber_weight_le
      S scale weight Complex.im shift H L (fun z hz => (hShiftSpec z hz).1)
        hLocal t
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨label, hEnergy⟩ := exists_mixed_energy_color_classes_on
    S weight eta (H + 1) Lrep color representative
      hRepresentativeShift hRepresentativeLocal
  let W := fun i : Fin 4 =>
    (S.filter (fun rho => color rho = label i)).image representative
  have hSeparated : forall i : Fin 4,
      RiemannZeta.GuthMaynard.IsSeparated 1 (W i) := by
    intro i
    exact isSeparated_detectorRepresentative_color S scale shift (label i)
  have hLarge : forall i : Fin 4, forall t, t ∈ W i ->
      large (label i).1 t := by
    intro i t ht
    obtain ⟨rho, hrhoColor, rfl⟩ := Finset.mem_image.mp ht
    have hrho := Finset.mem_filter.mp hrhoColor
    have hscale : scale rho = (label i).1 := congrArg Prod.fst hrho.2
    rw [← hscale]
    exact detectorRepresentative_large S scale shift large hScaleSpec hrho.1
  have hInterval : forall i : Fin 4, forall t, t ∈ W i ->
      inInterval t := by
    intro i t ht
    obtain ⟨rho, hrhoColor, rfl⟩ := Finset.mem_image.mp ht
    have hrho := (Finset.mem_filter.mp hrhoColor).1
    obtain ⟨y, hy, hscale, hfloor, hrep⟩ :=
      detectorRepresentative_spec S scale shift hrho
    change inInterval (detectorRepresentative S scale shift rho)
    rw [hrep]
    exact (hShiftSpec y hy).2.1
  refine ⟨label, ?_⟩
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [W, color, representative, scale, shift] using hSeparated
  · simpa only [W, color, representative, scale, shift] using hLarge
  · simpa only [W, color, representative, scale, shift] using hInterval
  have hCard : Fintype.card (Fin k × Fin 2) = 2 * k := by simp [mul_comm]
  simpa only [hCard, Lrep, W, color, representative, scale, shift, add_assoc]
    using hEnergy

#print axioms mem_resonantQuadruplesOn
#print axioms shifted_subfamily_quadruple_defect_le
#print axioms exists_mixed_energy_color_classes_on
#print axioms finite_shifted_dyadic_energy_extraction_on

end

end GafniTao
