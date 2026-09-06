import GafniTao.ExactMixedEnergy

/-!
# Discretizing mixed real additive energy

The ordinates selected by the detector may lie at four different dyadic
scales.  This file supplies the missing scale-independent bridge: double the
ordinates, take floors, split the resulting integer defect into finitely many
bins, and control every mixed bin by the four self energies.
-/

open scoped BigOperators

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The integer discretization used for one-separated ordinates.  Doubling
before taking the floor makes this map injective on any one-separated set. -/
noncomputable def doubleFloor (x : Real) : Int := ⌊2 * x⌋

noncomputable def doubleFloorImage (W : Finset Real) : Finset Int :=
  W.image doubleFloor

theorem doubleFloor_injective_on_of_separated
    (W : Finset Real) (hW : IsSeparated 1 W) :
    ∀ x ∈ W, ∀ y ∈ W, doubleFloor x = doubleFloor y → x = y := by
  intro x hx y hy hfloor
  by_contra hxy
  have hsep : 1 ≤ |x - y| := by
    simpa [Real.dist_eq] using hW x hx y hy hxy
  have hxLower := Int.floor_le (2 * x)
  have hxUpper := Int.lt_floor_add_one (2 * x)
  have hyLower := Int.floor_le (2 * y)
  have hyUpper := Int.lt_floor_add_one (2 * y)
  change ⌊2 * x⌋ = ⌊2 * y⌋ at hfloor
  have hxyUpper : x - y < 1 / 2 := by
    rw [hfloor] at hxUpper
    linarith
  have hxyLower : -(1 / 2 : Real) < x - y := by
    rw [← hfloor] at hyUpper
    linarith
  have hsmall : |x - y| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  exact (not_lt_of_ge hsep) hsmall

/-- Integer additive defect after doubled-floor discretization. -/
noncomputable def doubleFloorDefect
    (q : (Real × Real) × (Real × Real)) : Int :=
  doubleFloor q.1.1 + doubleFloor q.1.2 -
    doubleFloor q.2.1 - doubleFloor q.2.2

/-- A literal symmetric integer window containing every doubled-floor defect
of a real quadruple of tolerance `eta`. -/
noncomputable def doubleFloorDefectWindow (eta : Real) : Finset Int :=
  Finset.Icc (-⌈2 * eta + 2⌉) ⌈2 * eta + 2⌉

theorem doubleFloorDefect_mem_window
    {eta : Real}
    {q : (Real × Real) × (Real × Real)}
    (hq : |q.1.1 + q.1.2 - q.2.1 - q.2.2| ≤ eta) :
    doubleFloorDefect q ∈ doubleFloorDefectWindow eta := by
  simp only [doubleFloorDefectWindow, Finset.mem_Icc]
  rw [abs_le] at hq
  have h1l := Int.floor_le (2 * q.1.1)
  have h1u := Int.lt_floor_add_one (2 * q.1.1)
  have h2l := Int.floor_le (2 * q.1.2)
  have h2u := Int.lt_floor_add_one (2 * q.1.2)
  have h3l := Int.floor_le (2 * q.2.1)
  have h3u := Int.lt_floor_add_one (2 * q.2.1)
  have h4l := Int.floor_le (2 * q.2.2)
  have h4u := Int.lt_floor_add_one (2 * q.2.2)
  have hLowerReal :
      -(2 * eta + 2) < (doubleFloorDefect q : Real) := by
    simp only [doubleFloorDefect, doubleFloor, Int.cast_sub, Int.cast_add]
    linarith [hq.1]
  have hUpperReal :
      (doubleFloorDefect q : Real) < 2 * eta + 2 := by
    simp only [doubleFloorDefect, doubleFloor, Int.cast_sub, Int.cast_add]
    linarith [hq.2]
  constructor
  · have hceil : -(⌈2 * eta + 2⌉ : Real) ≤ doubleFloorDefect q := by
      have hbase : -(⌈2 * eta + 2⌉ : Real) ≤ -(2 * eta + 2) := by
        have := Int.le_ceil (2 * eta + 2)
        linarith
      exact hbase.trans (le_of_lt hLowerReal)
    exact_mod_cast hceil
  · have hceil : (doubleFloorDefect q : Real) ≤ ⌈2 * eta + 2⌉ := by
      exact (le_of_lt hUpperReal).trans (Int.le_ceil _)
    exact_mod_cast hceil

/-- Apply doubled-floor discretization to all four coordinates. -/
noncomputable def doubleFloorQuadruple
    (q : (Real × Real) × (Real × Real)) :
    (Int × Int) × (Int × Int) :=
  ((doubleFloor q.1.1, doubleFloor q.1.2),
    (doubleFloor q.2.1, doubleFloor q.2.2))

/-- The finite integer target of the mixed discretization. -/
noncomputable def integerMixedWindowQuadruples
    (eta : Real) (W0 W1 W2 W3 : Finset Real) :
    Finset ((Int × Int) × (Int × Int)) :=
  (quadrupleProductOf (doubleFloorImage W0) (doubleFloorImage W1)
      (doubleFloorImage W2) (doubleFloorImage W3)).filter fun q =>
    q.1.1 + q.1.2 - q.2.1 - q.2.2 ∈ doubleFloorDefectWindow eta

theorem card_integerMixedWindowQuadruples_eq_sum
    (eta : Real) (W0 W1 W2 W3 : Finset Real) :
    (integerMixedWindowQuadruples eta W0 W1 W2 W3).card =
      ∑ j ∈ doubleFloorDefectWindow eta,
        ExactMixedShiftCount j (doubleFloorImage W0) (doubleFloorImage W1)
          (doubleFloorImage W2) (doubleFloorImage W3) := by
  classical
  unfold integerMixedWindowQuadruples ExactMixedShiftCount
    exactMixedShiftQuadruples
  exact (Finset.sum_card_fiberwise_eq_card_filter
    (quadrupleProductOf (doubleFloorImage W0) (doubleFloorImage W1)
      (doubleFloorImage W2) (doubleFloorImage W3))
    (doubleFloorDefectWindow eta)
    (fun q => q.1.1 + q.1.2 - q.2.1 - q.2.2)).symm

/-- A mixed tolerance-`eta` real quadruple injects into the corresponding
finite doubled-floor defect window when each coordinate set is one-separated.
This is the exact finite bridge; there is no same-scale assumption. -/
theorem mixedApproxAddEnergy_le_sum_exactMixedShiftCount
    {eta : Real} {W0 W1 W2 W3 : Finset Real}
    (hW0 : IsSeparated 1 W0) (hW1 : IsSeparated 1 W1)
    (hW2 : IsSeparated 1 W2) (hW3 : IsSeparated 1 W3) :
    MixedApproxAddEnergy eta W0 W1 W2 W3 ≤
      ∑ j ∈ doubleFloorDefectWindow eta,
        ExactMixedShiftCount j (doubleFloorImage W0) (doubleFloorImage W1)
          (doubleFloorImage W2) (doubleFloorImage W3) := by
  classical
  rw [← card_integerMixedWindowQuadruples_eq_sum]
  unfold MixedApproxAddEnergy
  apply Finset.card_le_card_of_injOn doubleFloorQuadruple
  · intro q hq
    change q ∈ (quadrupleProductOf W0 W1 W2 W3).filter
      (fun q => |q.1.1 + q.1.2 - q.2.1 - q.2.2| ≤ eta) at hq
    have hqData := Finset.mem_filter.mp hq
    have hqProd := hqData.1
    unfold quadrupleProductOf at hqProd
    rcases Finset.mem_product.mp hqProd with ⟨h01, h23⟩
    rcases Finset.mem_product.mp h01 with ⟨h0, h1⟩
    rcases Finset.mem_product.mp h23 with ⟨h2, h3⟩
    have hdefect := hqData.2
    unfold integerMixedWindowQuadruples
    apply Finset.mem_filter.mpr
    constructor
    · unfold quadrupleProductOf doubleFloorQuadruple
      exact Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr
          ⟨Finset.mem_image.mpr ⟨_, h0, rfl⟩,
            Finset.mem_image.mpr ⟨_, h1, rfl⟩⟩,
          Finset.mem_product.mpr
          ⟨Finset.mem_image.mpr ⟨_, h2, rfl⟩,
            Finset.mem_image.mpr ⟨_, h3, rfl⟩⟩⟩
    · simpa only [doubleFloorQuadruple, doubleFloorDefect] using
        doubleFloorDefect_mem_window hdefect
  · intro q hq q' hq' heq
    have hqData : q ∈ quadrupleProductOf W0 W1 W2 W3 ∧
        |q.1.1 + q.1.2 - q.2.1 - q.2.2| ≤ eta :=
      Finset.mem_filter.mp hq
    have hqData' : q' ∈ quadrupleProductOf W0 W1 W2 W3 ∧
        |q'.1.1 + q'.1.2 - q'.2.1 - q'.2.2| ≤ eta :=
      Finset.mem_filter.mp hq'
    rcases q with ⟨⟨a, b⟩, ⟨c, d⟩⟩
    rcases q' with ⟨⟨a', b'⟩, ⟨c', d'⟩⟩
    have hqProd := hqData.1
    have hqProd' := hqData'.1
    unfold quadrupleProductOf at hqProd hqProd'
    rcases Finset.mem_product.mp hqProd with ⟨h01, h23⟩
    rcases Finset.mem_product.mp h01 with ⟨ha, hb⟩
    rcases Finset.mem_product.mp h23 with ⟨hc, hd⟩
    rcases Finset.mem_product.mp hqProd' with ⟨h01', h23'⟩
    rcases Finset.mem_product.mp h01' with ⟨ha', hb'⟩
    rcases Finset.mem_product.mp h23' with ⟨hc', hd'⟩
    simp only [doubleFloorQuadruple, Prod.mk.injEq] at heq ⊢
    exact
      ⟨⟨doubleFloor_injective_on_of_separated W0 hW0 _ ha _ ha' heq.1.1,
          doubleFloor_injective_on_of_separated W1 hW1 _ hb _ hb' heq.1.2⟩,
        doubleFloor_injective_on_of_separated W2 hW2 _ hc _ hc' heq.2.1,
        doubleFloor_injective_on_of_separated W3 hW3 _ hd _ hd' heq.2.2⟩

#print axioms doubleFloor_injective_on_of_separated
#print axioms doubleFloorDefect_mem_window
#print axioms card_integerMixedWindowQuadruples_eq_sum
#print axioms mixedApproxAddEnergy_le_sum_exactMixedShiftCount

end

end GafniTao
