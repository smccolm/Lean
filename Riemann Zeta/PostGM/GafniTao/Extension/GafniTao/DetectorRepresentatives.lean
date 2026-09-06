import GafniTao.MixedEnergyExtraction

/-!
# Common representatives for finite detector cells

For each dyadic scale and each unit interval, choose one actual shifted
ordinate.  Coloring the cells by scale and parity makes the representatives
one-separated, while moving an original ordinate by less than one additional
unit.  The local multiplicity loss remains explicit.
-/

open scoped BigOperators

namespace GafniTao

noncomputable section

def detectorCell {Alpha : Type*} [DecidableEq Alpha]
    (S : Finset Alpha) {k : Nat} (scale : Alpha -> Fin k)
    (shift : Alpha -> Real) (r : Fin k) (z : Int) : Finset Alpha :=
  S.filter fun x => scale x = r ∧ Int.floor (shift x) = z

noncomputable def detectorCellRepresentative
    {Alpha : Type*} [DecidableEq Alpha]
    (S : Finset Alpha) {k : Nat} (scale : Alpha -> Fin k)
    (shift : Alpha -> Real) (r : Fin k) (z : Int) : Real :=
  if h : (detectorCell S scale shift r z).Nonempty then
    shift (Classical.choose h) else 0

noncomputable def detectorRepresentative
    {Alpha : Type*} [DecidableEq Alpha]
    (S : Finset Alpha) {k : Nat} (scale : Alpha -> Fin k)
    (shift : Alpha -> Real) (x : Alpha) : Real :=
  detectorCellRepresentative S scale shift (scale x) (Int.floor (shift x))

/-- Parity of an integer, represented as `Fin 2`. -/
def intParity (z : Int) : Fin 2 :=
  if z % 2 = 0 then 0 else 1

theorem intParity_eq_intParity_iff_emod_two_eq
    (a b : Int) : intParity a = intParity b ↔ a % 2 = b % 2 := by
  have ha := Int.emod_two_eq_zero_or_one a
  have hb := Int.emod_two_eq_zero_or_one b
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    simp [intParity, ha, hb]

def detectorColor {Alpha : Type*} {k : Nat}
    (scale : Alpha -> Fin k) (shift : Alpha -> Real) (x : Alpha) :
    Fin k × Fin 2 :=
  (scale x, intParity (Int.floor (shift x)))

theorem detectorCellRepresentative_spec
    {Alpha : Type*} [DecidableEq Alpha]
    (S : Finset Alpha) {k : Nat} (scale : Alpha -> Fin k)
    (shift : Alpha -> Real) (r : Fin k) (z : Int)
    (hCell : (detectorCell S scale shift r z).Nonempty) :
    exists x, x ∈ detectorCell S scale shift r z ∧
      detectorCellRepresentative S scale shift r z = shift x := by
  let x := Classical.choose hCell
  have hx := Classical.choose_spec hCell
  refine ⟨x, hx, ?_⟩
  simp only [detectorCellRepresentative, dif_pos hCell, x]

theorem detectorRepresentative_spec
    {Alpha : Type*} [DecidableEq Alpha]
    (S : Finset Alpha) {k : Nat} (scale : Alpha -> Fin k)
    (shift : Alpha -> Real) {x : Alpha} (hx : x ∈ S) :
    exists y, y ∈ S ∧ scale y = scale x ∧
      Int.floor (shift y) = Int.floor (shift x) ∧
      detectorRepresentative S scale shift x = shift y := by
  have hCell :
      (detectorCell S scale shift (scale x) (Int.floor (shift x))).Nonempty := by
    refine ⟨x, ?_⟩
    exact Finset.mem_filter.mpr ⟨hx, rfl, rfl⟩
  obtain ⟨y, hyCell, hrep⟩ :=
    detectorCellRepresentative_spec S scale shift (scale x)
      (Int.floor (shift x)) hCell
  have hy := Finset.mem_filter.mp hyCell
  exact ⟨y, hy.1, hy.2.1, hy.2.2, hrep⟩

theorem floor_detectorRepresentative_eq
    {Alpha : Type*} [DecidableEq Alpha]
    (S : Finset Alpha) {k : Nat} (scale : Alpha -> Fin k)
    (shift : Alpha -> Real) {x : Alpha} (hx : x ∈ S) :
    Int.floor (detectorRepresentative S scale shift x) =
      Int.floor (shift x) := by
  obtain ⟨y, hy, hscale, hfloor, hrep⟩ :=
    detectorRepresentative_spec S scale shift hx
  rw [hrep, hfloor]

theorem abs_shift_sub_detectorRepresentative_lt_one
    {Alpha : Type*} [DecidableEq Alpha]
    (S : Finset Alpha) {k : Nat} (scale : Alpha -> Fin k)
    (shift : Alpha -> Real) {x : Alpha} (hx : x ∈ S) :
    |shift x - detectorRepresentative S scale shift x| < 1 := by
  have hFloor := floor_detectorRepresentative_eq S scale shift hx
  have hxFloor := Int.floor_le (shift x)
  have hxUpper := Int.lt_floor_add_one (shift x)
  have hrFloor := Int.floor_le (detectorRepresentative S scale shift x)
  have hrUpper := Int.lt_floor_add_one
    (detectorRepresentative S scale shift x)
  rw [hFloor] at hrFloor hrUpper
  rw [abs_lt]
  constructor <;> linarith

theorem abs_ordinate_sub_detectorRepresentative_le
    {Alpha : Type*} [DecidableEq Alpha]
    (S : Finset Alpha) {k : Nat} (scale : Alpha -> Fin k)
    (ordinate shift : Alpha -> Real) (H : Real)
    (hShift : forall x, x ∈ S -> |ordinate x - shift x| <= H)
    {x : Alpha} (hx : x ∈ S) :
    |ordinate x - detectorRepresentative S scale shift x| <= H + 1 := by
  have h0 := hShift x hx
  have h1 := abs_shift_sub_detectorRepresentative_lt_one S scale shift hx
  have hlt : |ordinate x - detectorRepresentative S scale shift x| < H + 1 := by
    calc
    |ordinate x - detectorRepresentative S scale shift x| <=
        |ordinate x - shift x| +
          |shift x - detectorRepresentative S scale shift x| := by
      exact abs_sub_le _ _ _
    _ < H + 1 := by linarith
  exact hlt.le

/-- Every representative is an actual shifted ordinate in the same scale
cell, hence inherits the detector's large-value property. -/
theorem detectorRepresentative_large
    {Alpha : Type*} [DecidableEq Alpha]
    (S : Finset Alpha) {k : Nat} (scale : Alpha -> Fin k)
    (shift : Alpha -> Real) (large : Fin k -> Real -> Prop)
    (hLarge : forall x, x ∈ S -> large (scale x) (shift x))
    {x : Alpha} (hx : x ∈ S) :
    large (scale x) (detectorRepresentative S scale shift x) := by
  obtain ⟨y, hy, hscale, hfloor, hrep⟩ :=
    detectorRepresentative_spec S scale shift hx
  rw [hrep, ← hscale]
  exact hLarge y hy

/-- The total source weight over a single representative fiber is bounded by
the explicit displaced-unit-bin loss. -/
theorem detectorRepresentative_fiber_weight_le
    {Alpha : Type*} [DecidableEq Alpha]
    (S : Finset Alpha) {k : Nat} (scale : Alpha -> Fin k)
    (weight : Alpha -> Nat) (ordinate shift : Alpha -> Real)
    (H : Real) (L : Nat)
    (hShift : forall x, x ∈ S -> |ordinate x - shift x| <= H)
    (hLocal : forall z : Int,
      (∑ x ∈ S.filter
        (fun y => (z : Real) <= ordinate y ∧ ordinate y < (z : Real) + 1),
        weight x) <= L)
    (t : Real) :
    (∑ x ∈ S.filter
      (fun y => detectorRepresentative S scale shift y = t), weight x) <=
      (2 * ⌈H + 1⌉₊ + 1) * L := by
  let representative := detectorRepresentative S scale shift
  by_cases ht : t ∈ S.image representative
  · let z := Int.floor t
    have hBin :=
      RiemannZeta.GuthMaynard.shifted_bin_weight_le_of_unit_bin_weight
        S weight ordinate representative (H + 1) L
        (fun x hx => abs_ordinate_sub_detectorRepresentative_le
          S scale ordinate shift H hShift hx)
        hLocal z
    have htBin : t ∈ (S.image representative).filter
        (fun u => (z : Real) <= u ∧ u < (z : Real) + 1) := by
      apply Finset.mem_filter.mpr
      exact ⟨ht, Int.floor_le t, Int.lt_floor_add_one t⟩
    let B := (S.image representative).filter
      (fun u => (z : Real) <= u ∧ u < (z : Real) + 1)
    have htSub : ({t} : Finset Real) ⊆ B := by
      intro u hu
      simpa only [Finset.mem_singleton.mp hu] using htBin
    calc
      (∑ x ∈ S.filter (fun y => representative y = t), weight x) =
          ∑ u ∈ ({t} : Finset Real),
            ∑ x ∈ S.filter (fun y => representative y = u), weight x := by
        simp
      _ <= ∑ u ∈ B,
            ∑ x ∈ S.filter (fun y => representative y = u), weight x :=
        Finset.sum_le_sum_of_subset htSub
      _ <= (2 * ⌈H + 1⌉₊ + 1) * L := by
        simpa only [B] using hBin
  · have hEmpty : S.filter (fun y => representative y = t) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro x hxS hxEq
      exact ht (Finset.mem_image.mpr ⟨x, hxS, hxEq⟩)
    rw [show detectorRepresentative S scale shift = representative from rfl,
      hEmpty]
    simp

/-- For one fixed detector color, the chosen representatives form a
one-separated set. -/
theorem isSeparated_detectorRepresentative_color
    {Alpha : Type*} [DecidableEq Alpha]
    (S : Finset Alpha) {k : Nat} (scale : Alpha -> Fin k)
    (shift : Alpha -> Real) (label : Fin k × Fin 2) :
    RiemannZeta.GuthMaynard.IsSeparated 1
      ((S.filter (fun x => detectorColor scale shift x = label)).image
        (detectorRepresentative S scale shift)) := by
  classical
  intro a ha b hb hab
  obtain ⟨x, hxColor, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y, hyColor, rfl⟩ := Finset.mem_image.mp hb
  have hx := Finset.mem_filter.mp hxColor
  have hy := Finset.mem_filter.mp hyColor
  have hColor : detectorColor scale shift x =
      detectorColor scale shift y := hx.2.trans hy.2.symm
  have hScale : scale x = scale y := congrArg Prod.fst hColor
  have hParity : intParity (Int.floor (shift x)) =
      intParity (Int.floor (shift y)) := congrArg Prod.snd hColor
  have hFloorX := floor_detectorRepresentative_eq S scale shift hx.1
  have hFloorY := floor_detectorRepresentative_eq S scale shift hy.1
  have hFloorNe : Int.floor (shift x) ≠ Int.floor (shift y) := by
    intro hFloor
    apply hab
    unfold detectorRepresentative
    rw [hScale, hFloor]
  have hMod : Int.floor (shift x) % 2 =
      Int.floor (shift y) % 2 :=
    (intParity_eq_intParity_iff_emod_two_eq _ _).mp hParity
  have hEven : Even (Int.floor (shift y) - Int.floor (shift x)) := by
    rw [even_iff_two_dvd]
    apply Int.dvd_iff_emod_eq_zero.mpr
    exact (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hMod.symm)
  rw [Real.dist_eq]
  by_cases hxy : Int.floor (shift x) < Int.floor (shift y)
  · have hTwo : Int.floor (shift x) + 2 <= Int.floor (shift y) :=
      (Int.add_two_le_iff_lt_of_even_sub hEven).mpr hxy
    have hTwoR : (Int.floor (shift x) : Real) + 2 <=
        (Int.floor (shift y) : Real) := by exact_mod_cast hTwo
    have hxUpper := Int.lt_floor_add_one
      (detectorRepresentative S scale shift x)
    have hyLower := Int.floor_le
      (detectorRepresentative S scale shift y)
    rw [hFloorX] at hxUpper
    rw [hFloorY] at hyLower
    have hOrder : detectorRepresentative S scale shift x <=
        detectorRepresentative S scale shift y := by linarith
    rw [abs_of_nonpos (sub_nonpos.mpr hOrder)]
    linarith
  · have hyx : Int.floor (shift y) < Int.floor (shift x) := by
      omega
    have hEven' : Even (Int.floor (shift x) - Int.floor (shift y)) := by
      rcases hEven with ⟨c, hc⟩
      refine ⟨-c, ?_⟩
      linarith
    have hTwo : Int.floor (shift y) + 2 <= Int.floor (shift x) :=
      (Int.add_two_le_iff_lt_of_even_sub hEven').mpr hyx
    have hTwoR : (Int.floor (shift y) : Real) + 2 <=
        (Int.floor (shift x) : Real) := by exact_mod_cast hTwo
    have hyUpper := Int.lt_floor_add_one
      (detectorRepresentative S scale shift y)
    have hxLower := Int.floor_le
      (detectorRepresentative S scale shift x)
    rw [hFloorY] at hyUpper
    rw [hFloorX] at hxLower
    rw [abs_of_nonneg (sub_nonneg.mpr (by linarith))]
    linarith

#print axioms intParity_eq_intParity_iff_emod_two_eq
#print axioms detectorRepresentative_spec
#print axioms detectorRepresentative_fiber_weight_le
#print axioms isSeparated_detectorRepresentative_color

end

end GafniTao
