import GafniTao.DetectorRepresentatives

/-!
# Source-facing energy detector extraction

Every zero chooses a shifted ordinate and a dyadic scale.  Representatives
are then selected by scale and unit bin, while the four coordinates of the
zero energy are pigeonholed simultaneously.  The result retains actual
large-value predicates on four separated ordinate sets and the full analytic
multiplicity count.
-/

open scoped BigOperators

namespace GafniTao

noncomputable section

/-- Finite shifted dyadic extraction preserving the complete four-zero
energy.  Unlike the ordinary-density extractor, the output is necessarily a
mixed energy of four potentially different detector colors. -/
theorem finite_shifted_dyadic_energy_extraction
    (sigma T H : Real) (k L : Nat) (hk : 0 < k)
    (large : Fin k -> Real -> Prop) (inInterval : Real -> Prop)
    (hEach : forall rho, rho ∈ zeroSet sigma T ->
      exists t : Real, |rho.im - t| <= H ∧ inInterval t ∧
        exists r : Fin k, large r t)
    (hLocal : forall z : Int,
      (∑ rho ∈ (zeroSet sigma T).filter
        (fun y => (z : Real) <= y.im ∧ y.im < (z : Real) + 1),
        zeroMultiplicity rho) <= L) :
    exists label : Fin 4 -> (Fin k × Fin 2),
      let shift : Complex -> Real := fun rho =>
        if h : rho ∈ zeroSet sigma T then Classical.choose (hEach rho h)
        else rho.im
      let scale : Complex -> Fin k := fun rho =>
        if h : rho ∈ zeroSet sigma T then
          Classical.choose (Classical.choose_spec (hEach rho h)).2.2
        else ⟨0, hk⟩
      let representative :=
        detectorRepresentative (zeroSet sigma T) scale shift
      let W := fun i : Fin 4 =>
        ((zeroSet sigma T).filter
          (fun rho => detectorColor scale shift rho = label i)).image
            representative
      (forall i : Fin 4,
        RiemannZeta.GuthMaynard.IsSeparated 1 (W i)) ∧
      (forall i : Fin 4, forall t, t ∈ W i -> large (label i).1 t) ∧
      (forall i : Fin 4, forall t, t ∈ W i -> inInterval t) ∧
      zeroAdditiveEnergyCount sigma T <=
        (2 * k) ^ 4 * ((2 * ⌈H + 1⌉₊ + 1) * L) ^ 4 *
          MixedApproxAddEnergy (1 + 4 * (H + 1))
            (W 0) (W 1) (W 2) (W 3) := by
  classical
  let shift : Complex -> Real := fun rho =>
    if h : rho ∈ zeroSet sigma T then Classical.choose (hEach rho h)
    else rho.im
  have hShiftSpec : forall rho, rho ∈ zeroSet sigma T ->
      |rho.im - shift rho| <= H ∧ inInterval (shift rho) ∧
        exists r : Fin k, large r (shift rho) := by
    intro rho hrho
    dsimp only [shift]
    rw [dif_pos hrho]
    exact Classical.choose_spec (hEach rho hrho)
  let scale : Complex -> Fin k := fun rho =>
    if h : rho ∈ zeroSet sigma T then
      Classical.choose (Classical.choose_spec (hEach rho h)).2.2
    else ⟨0, hk⟩
  have hScaleSpec : forall rho, rho ∈ zeroSet sigma T ->
      large (scale rho) (shift rho) := by
    intro rho hrho
    dsimp only [scale]
    rw [dif_pos hrho]
    simpa only [shift, dif_pos hrho] using
      Classical.choose_spec (Classical.choose_spec (hEach rho hrho)).2.2
  let representative :=
    detectorRepresentative (zeroSet sigma T) scale shift
  let color := detectorColor scale shift
  let Lrep := (2 * ⌈H + 1⌉₊ + 1) * L
  have hRepresentativeShift : forall rho, rho ∈ zeroSet sigma T ->
      |rho.im - representative rho| <= H + 1 := by
    intro rho hrho
    exact abs_ordinate_sub_detectorRepresentative_le
      (zeroSet sigma T) scale Complex.im shift H
      (fun z hz => (hShiftSpec z hz).1) hrho
  have hRepresentativeLocal : forall t : Real,
      (∑ rho ∈ (zeroSet sigma T).filter
        (fun z => representative z = t), zeroMultiplicity rho) <= Lrep := by
    intro t
    exact detectorRepresentative_fiber_weight_le
      (zeroSet sigma T) scale zeroMultiplicity Complex.im shift H L
      (fun z hz => (hShiftSpec z hz).1) hLocal t
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨label, hEnergy⟩ :=
    exists_mixed_energy_color_classes sigma T (H + 1) Lrep color
      representative hRepresentativeShift hRepresentativeLocal
  let W := fun i : Fin 4 =>
    ((zeroSet sigma T).filter
      (fun rho => color rho = label i)).image representative
  have hSeparated : forall i : Fin 4,
      RiemannZeta.GuthMaynard.IsSeparated 1 (W i) := by
    intro i
    exact isSeparated_detectorRepresentative_color
      (zeroSet sigma T) scale shift (label i)
  have hLarge : forall i : Fin 4, forall t, t ∈ W i ->
      large (label i).1 t := by
    intro i t ht
    obtain ⟨rho, hrhoColor, rfl⟩ := Finset.mem_image.mp ht
    have hrho := Finset.mem_filter.mp hrhoColor
    have hcolor := hrho.2
    have hscale : scale rho = (label i).1 := congrArg Prod.fst hcolor
    rw [← hscale]
    exact detectorRepresentative_large (zeroSet sigma T) scale shift large
      hScaleSpec hrho.1
  have hInterval : forall i : Fin 4, forall t, t ∈ W i ->
      inInterval t := by
    intro i t ht
    obtain ⟨rho, hrhoColor, rfl⟩ := Finset.mem_image.mp ht
    have hrho := (Finset.mem_filter.mp hrhoColor).1
    obtain ⟨y, hy, hscale, hfloor, hrep⟩ :=
      detectorRepresentative_spec (zeroSet sigma T) scale shift hrho
    change inInterval
      (detectorRepresentative (zeroSet sigma T) scale shift rho)
    rw [hrep]
    exact (hShiftSpec y hy).2.1
  refine ⟨label, ?_⟩
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [W, color, representative, scale, shift] using hSeparated
  · simpa only [W, color, representative, scale, shift] using hLarge
  · simpa only [W, color, representative, scale, shift] using hInterval
  have hCard : Fintype.card (Fin k × Fin 2) = 2 * k := by
    simp [mul_comm]
  simpa only [hCard, Lrep, W, color, representative, scale, shift] using hEnergy

#print axioms finite_shifted_dyadic_energy_extraction

end

end GafniTao
