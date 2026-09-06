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

/-- The unique real point represented by an integer in a doubled-floor image.
The fallback value is unreachable in all public uses. -/
noncomputable def doubleFloorPreimage (W : Finset Real) (z : Int) : Real :=
  if hz : z ∈ doubleFloorImage W then
    Classical.choose (Finset.mem_image.mp hz)
  else 0

theorem doubleFloorPreimage_mem
    {W : Finset Real} {z : Int} (hz : z ∈ doubleFloorImage W) :
    doubleFloorPreimage W z ∈ W := by
  rw [doubleFloorPreimage, dif_pos hz]
  exact (Classical.choose_spec (Finset.mem_image.mp hz)).1

theorem doubleFloor_doubleFloorPreimage
    {W : Finset Real} {z : Int} (hz : z ∈ doubleFloorImage W) :
    doubleFloor (doubleFloorPreimage W z) = z := by
  rw [doubleFloorPreimage, dif_pos hz]
  exact (Classical.choose_spec (Finset.mem_image.mp hz)).2

noncomputable def liftDoubleFloorQuadruple (W : Finset Real)
    (q : (Int × Int) × (Int × Int)) :
    (Real × Real) × (Real × Real) :=
  ((doubleFloorPreimage W q.1.1, doubleFloorPreimage W q.1.2),
    (doubleFloorPreimage W q.2.1, doubleFloorPreimage W q.2.2))

/-- Exact doubled-floor additive energy injects back into tolerance-one real
energy.  The strict floor remainder inequalities are what make tolerance one
available rather than an unspecified constant. -/
theorem addEnergy_doubleFloorImage_le_approxAddEnergy_one
    (W : Finset Real) :
    Finset.addEnergy (doubleFloorImage W) (doubleFloorImage W) ≤
      ApproxAddEnergy 1 W := by
  classical
  rw [Finset.addEnergy_eq_card_filter]
  unfold ApproxAddEnergy
  apply Finset.card_le_card_of_injOn (liftDoubleFloorQuadruple W)
  · intro q hq
    have hqData := Finset.mem_filter.mp hq
    have hqProd := hqData.1
    have hqSum := hqData.2
    rcases q with ⟨⟨a, b⟩, ⟨c, d⟩⟩
    rcases Finset.mem_product.mp hqProd with ⟨hab, hcd⟩
    rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
    rcases Finset.mem_product.mp hcd with ⟨hc, hd⟩
    let ar := doubleFloorPreimage W a
    let br := doubleFloorPreimage W b
    let cr := doubleFloorPreimage W c
    let dr := doubleFloorPreimage W d
    have har : ar ∈ W := doubleFloorPreimage_mem ha
    have hbr : br ∈ W := doubleFloorPreimage_mem hb
    have hcr : cr ∈ W := doubleFloorPreimage_mem hc
    have hdr : dr ∈ W := doubleFloorPreimage_mem hd
    have hfa : doubleFloor ar = a := doubleFloor_doubleFloorPreimage ha
    have hfb : doubleFloor br = b := doubleFloor_doubleFloorPreimage hb
    have hfc : doubleFloor cr = c := doubleFloor_doubleFloorPreimage hc
    have hfd : doubleFloor dr = d := doubleFloor_doubleFloorPreimage hd
    have hal := Int.floor_le (2 * ar)
    have hau := Int.lt_floor_add_one (2 * ar)
    have hbl := Int.floor_le (2 * br)
    have hbu := Int.lt_floor_add_one (2 * br)
    have hcl := Int.floor_le (2 * cr)
    have hcu := Int.lt_floor_add_one (2 * cr)
    have hdl := Int.floor_le (2 * dr)
    have hdu := Int.lt_floor_add_one (2 * dr)
    have hsumReal : (a : Real) + b = c + d := by exact_mod_cast hqSum
    change liftDoubleFloorQuadruple W ((a, b), c, d) ∈
      approximateAdditiveQuadruples 1 W
    unfold approximateAdditiveQuadruples liftDoubleFloorQuadruple
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨har, hbr⟩,
          Finset.mem_product.mpr ⟨hcr, hdr⟩⟩
    · change |ar + br - cr - dr| ≤ (1 : Real)
      apply le_of_lt
      rw [abs_lt]
      constructor
      · change -(1 : Real) < ar + br - cr - dr
        change ⌊2 * ar⌋ = a at hfa
        change ⌊2 * br⌋ = b at hfb
        change ⌊2 * cr⌋ = c at hfc
        change ⌊2 * dr⌋ = d at hfd
        rw [hfa] at hal hau
        rw [hfb] at hbl hbu
        rw [hfc] at hcl hcu
        rw [hfd] at hdl hdu
        linarith
      · change ar + br - cr - dr < (1 : Real)
        change ⌊2 * ar⌋ = a at hfa
        change ⌊2 * br⌋ = b at hfb
        change ⌊2 * cr⌋ = c at hfc
        change ⌊2 * dr⌋ = d at hfd
        rw [hfa] at hal hau
        rw [hfb] at hbl hbu
        rw [hfc] at hcl hcu
        rw [hfd] at hdl hdu
        linarith
  · intro q hq q' hq' heq
    have hqProd := (Finset.mem_filter.mp hq).1
    have hqProd' := (Finset.mem_filter.mp hq').1
    rcases q with ⟨⟨a, b⟩, ⟨c, d⟩⟩
    rcases q' with ⟨⟨a', b'⟩, ⟨c', d'⟩⟩
    rcases Finset.mem_product.mp hqProd with ⟨hab, hcd⟩
    rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
    rcases Finset.mem_product.mp hcd with ⟨hc, hd⟩
    rcases Finset.mem_product.mp hqProd' with ⟨hab', hcd'⟩
    rcases Finset.mem_product.mp hab' with ⟨ha', hb'⟩
    rcases Finset.mem_product.mp hcd' with ⟨hc', hd'⟩
    simp only at ha hb hc hd ha' hb' hc' hd'
    simp only [liftDoubleFloorQuadruple, Prod.mk.injEq] at heq ⊢
    constructor
    · constructor
      · rw [← doubleFloor_doubleFloorPreimage ha,
          ← doubleFloor_doubleFloorPreimage ha', heq.1.1]
      · rw [← doubleFloor_doubleFloorPreimage hb,
          ← doubleFloor_doubleFloorPreimage hb', heq.1.2]
    · constructor
      · rw [← doubleFloor_doubleFloorPreimage hc,
          ← doubleFloor_doubleFloorPreimage hc', heq.2.1]
      · rw [← doubleFloor_doubleFloorPreimage hd,
          ← doubleFloor_doubleFloorPreimage hd', heq.2.2]

/-- Complete mixed-to-self energy comparison.  Its only loss is the literal
cardinality of the doubled-floor defect window. -/
theorem four_mul_mixedApproxAddEnergy_le_window_mul_sum_self
    {eta : Real} {W0 W1 W2 W3 : Finset Real}
    (hW0 : IsSeparated 1 W0) (hW1 : IsSeparated 1 W1)
    (hW2 : IsSeparated 1 W2) (hW3 : IsSeparated 1 W3) :
    4 * (MixedApproxAddEnergy eta W0 W1 W2 W3 : Real) ≤
      (doubleFloorDefectWindow eta).card *
        ((ApproxAddEnergy 1 W0 : Real) + (ApproxAddEnergy 1 W1 : Real) +
          (ApproxAddEnergy 1 W2 : Real) + (ApproxAddEnergy 1 W3 : Real)) := by
  let I := doubleFloorDefectWindow eta
  let E : Int → Nat := fun j =>
    ExactMixedShiftCount j (doubleFloorImage W0) (doubleFloorImage W1)
      (doubleFloorImage W2) (doubleFloorImage W3)
  let S : Real :=
    (ApproxAddEnergy 1 W0 : Real) + (ApproxAddEnergy 1 W1 : Real) +
      (ApproxAddEnergy 1 W2 : Real) + (ApproxAddEnergy 1 W3 : Real)
  have hMixedNat := mixedApproxAddEnergy_le_sum_exactMixedShiftCount
    (eta := eta) (W0 := W0) (W1 := W1) (W2 := W2) (W3 := W3)
    hW0 hW1 hW2 hW3
  have hMixed : (MixedApproxAddEnergy eta W0 W1 W2 W3 : Real) ≤
      ∑ j ∈ I, (E j : Real) := by
    exact_mod_cast hMixedNat
  have hEach (j : Int) : 4 * (E j : Real) ≤ S := by
    have hExact := four_mul_exactMixedShiftCount_le_sum_self_energies j
      (doubleFloorImage W0) (doubleFloorImage W1)
      (doubleFloorImage W2) (doubleFloorImage W3)
    have h0 : (Finset.addEnergy (doubleFloorImage W0)
        (doubleFloorImage W0) : Real) ≤ ApproxAddEnergy 1 W0 := by
      exact_mod_cast addEnergy_doubleFloorImage_le_approxAddEnergy_one W0
    have h1 : (Finset.addEnergy (doubleFloorImage W1)
        (doubleFloorImage W1) : Real) ≤ ApproxAddEnergy 1 W1 := by
      exact_mod_cast addEnergy_doubleFloorImage_le_approxAddEnergy_one W1
    have h2 : (Finset.addEnergy (doubleFloorImage W2)
        (doubleFloorImage W2) : Real) ≤ ApproxAddEnergy 1 W2 := by
      exact_mod_cast addEnergy_doubleFloorImage_le_approxAddEnergy_one W2
    have h3 : (Finset.addEnergy (doubleFloorImage W3)
        (doubleFloorImage W3) : Real) ≤ ApproxAddEnergy 1 W3 := by
      exact_mod_cast addEnergy_doubleFloorImage_le_approxAddEnergy_one W3
    dsimp only [E, S]
    linarith
  calc
    4 * (MixedApproxAddEnergy eta W0 W1 W2 W3 : Real) ≤
        4 * ∑ j ∈ I, (E j : Real) := by gcongr
    _ = ∑ j ∈ I, 4 * (E j : Real) := by
      simp only [Finset.mul_sum]
    _ ≤ ∑ _j ∈ I, S := by
      exact Finset.sum_le_sum fun j _ => hEach j
    _ = (I.card : Real) * S := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ = (doubleFloorDefectWindow eta).card *
        ((ApproxAddEnergy 1 W0 : Real) + (ApproxAddEnergy 1 W1 : Real) +
          (ApproxAddEnergy 1 W2 : Real) + (ApproxAddEnergy 1 W3 : Real)) := rfl

#print axioms doubleFloor_injective_on_of_separated
#print axioms doubleFloorDefect_mem_window
#print axioms card_integerMixedWindowQuadruples_eq_sum
#print axioms mixedApproxAddEnergy_le_sum_exactMixedShiftCount
#print axioms addEnergy_doubleFloorImage_le_approxAddEnergy_one
#print axioms four_mul_mixedApproxAddEnergy_le_window_mul_sum_self

end

end GafniTao
