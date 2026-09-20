import TaoTrudgianYang2025.DetectorPattern
import TaoTrudgianYang2025.EnergyExponents
import GuthMaynard.ClassicalDichotomy
import GuthMaynard.ClassicalEndpointSlab
import GuthMaynard.LargeValuesEnergy

/-!
# Multiplicity-safe energy input for the classical detector dichotomy

The native classical Type-I/Type-II dichotomy is formulated on the distinct
zero finset with analytic weights.  This module expands those weights into an
index type, so subsequent perturbation, branch coloring, scale coloring, and
additive-energy estimates retain every analytic-multiplicity copy.
-/

noncomputable section

namespace TaoTrudgianYang2025

open RiemannZeta.GuthMaynard
open Complex
open scoped FourierTransform

/-- One index for every analytic-multiplicity copy of a zero in the positive
dyadic slab `[T,2T]`. -/
abbrev ClassicalSlabZeroCopy (σ T : ℝ) :=
  WeightedCopy (zerosInRect σ 1 T (2 * T))
    (analyticVanishingOrder riemannZeta)

/-- Unit additive energy of the positive dyadic slab, counting analytic
multiplicity exactly. -/
def classicalSlabZeroEnergy (σ T : ℝ) : ℕ :=
  approximateAdditiveEnergyOf 1
    (fun z : ClassicalSlabZeroCopy σ T => (z.1.1 : ℂ).im)

/-- The branch-and-scale label attached to a shifted classical zero.  The
`none` constructor makes the finite color type inhabited even before the
source inequalities imply that both dyadic scale ranges are nonempty; the
source extraction theorem never assigns it. -/
abbrev ClassicalBranchScaleColor (T : ℝ) (Y : ℕ) :=
  Option
    (Fin (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊) ⊕
      Fin (Nat.clog 2 Y))

/-- The classical Type-I large-value conditions at a fixed dyadic scale. -/
def ClassicalTypeILargeAt
    (σ T D₁ : ℝ) (Y : ℕ)
    (r : Fin (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊)) (t : ℝ) : Prop :=
  ((3 / 4) * (T ^ (-D₁) / 2)) /
        Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ ≤
      ‖dirichletPoly (2 ^ (r : ℕ) * Y)
        (classicalZetaLongLineCoeff ⌊sharpZetaCutoff T⌋₊ σ) t‖ ∧
    (3 / 4) * (T ^ (-D₁) / 2) ≤
      ‖classicalZetaLongTail Y ⌊sharpZetaCutoff T⌋₊
        ((σ : ℂ) + I * (t : ℂ))‖

/-- Exact reciprocal of the source Type-I threshold.  This exposes the only
height-dependent loss as one `clog` factor and `T^D`. -/
theorem classicalTypeI_sourceThreshold_inv
    (T D : ℝ) (A : ℕ) (hT : 0 < T) (hA : 1 < A) :
    ((((3 / 4 : ℝ) * (T ^ (-D) / 2)) / Nat.clog 2 A)⁻¹) =
      (8 / 3 : ℝ) * Nat.clog 2 A * T ^ D := by
  have hClogNat : 0 < Nat.clog 2 A := Nat.clog_pos Nat.one_lt_two hA
  have hClog : (0 : ℝ) < Nat.clog 2 A := by exact_mod_cast hClogNat
  have hTD : 0 < T ^ D := Real.rpow_pos_of_pos hT _
  rw [Real.rpow_neg hT.le]
  field_simp [hTD.ne', hClog.ne']
  ring

/-- The classical Type-II large-value condition at a fixed dyadic scale. -/
def ClassicalTypeIILargeAt
    (σ : ℝ) (Y X : ℕ)
    (r : Fin (Nat.clog 2 Y)) (t : ℝ) : Prop :=
  ((3 / 4) * (3 / 4)) / Nat.clog 2 Y ≤
    ‖dirichletPoly (2 ^ (r : ℕ) * X)
      (sharpMollifiedLineCoeff Y X σ) t‖

/-- Interpret a classical branch-and-scale color as its genuine source
large-value assertion.  The artificial `none` color is impossible. -/
def ClassicalBranchScaleLarge
    (σ T D₁ : ℝ) (Y X : ℕ)
    (c : ClassicalBranchScaleColor T Y) (t : ℝ) : Prop :=
  match c with
  | none => False
  | some (Sum.inl r) => ClassicalTypeILargeAt σ T D₁ Y r t
  | some (Sum.inr r) => ClassicalTypeIILargeAt σ Y X r t

/-- Source-level classical dichotomy with one beta-removed ordinate and one
dyadic branch/scale label for every distinct zero.  Unlike the native
cardinality extraction, this retains the assignment needed for additive
energy and hence can be inherited by every analytic-multiplicity copy. -/
theorem classicalZero_exists_shifted_branch_scale
    (σ δ B₁ D₁ B₂ D₂ : ℝ)
    (hσ : 1 / 2 < σ) (hσUpper : σ ≤ 1) (hδ : 0 < δ) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧
      ∀ (T : ℝ) (Y X : ℕ), T₀ ≤ T →
        1 ≤ X → 1 < Y → X ≤ Y → Y ≤ ⌊sharpZetaCutoff T⌋₊ →
        (∀ ρ ∈ zerosInRect σ 1 T (2 * T),
          149 * sharpZetaCutoff T ^ (-ρ.re) ≤ T ^ (-D₁) / 2) →
        T ^ (-D₁) * (X : ℝ) ≤ 1 / 4 →
        finiteDirichletMass (classicalZetaLongTailSupport Y
            ⌊sharpZetaCutoff T⌋₊) (fun _n => 1) ≤ T ^ B₁ →
        T ^ (-D₁ - 1) ≤ T ^ (-D₁) / 2 →
        finiteDirichletMass (sharpMollifiedTailSupport Y X)
            (sharpMollifiedCoeff Y X) ≤ T ^ B₂ →
        T ^ (-D₂) ≤ 3 / 4 →
        ∀ ρ : ↥(zerosInRect σ 1 T (2 * T)),
          ∃ (t : ℝ) (c : ClassicalBranchScaleColor T Y),
            |(ρ : ℂ).im - t| ≤ T ^ δ ∧
            (T - T ^ δ ≤ t ∧ t ≤ 2 * T + T ^ δ) ∧
            ClassicalBranchScaleLarge σ T D₁ Y X c t := by
  obtain ⟨T₁, hT₁, hBetaI⟩ :=
    finiteDirichlet_beta_removal_power_threshold δ hδ B₁ (D₁ + 1)
  obtain ⟨T₂, hT₂, hBetaII⟩ :=
    finiteDirichlet_beta_removal_power_threshold δ hδ B₂ D₂
  refine ⟨max T₁ T₂, hT₁.trans (le_max_left _ _), ?_⟩
  intro T Y X hT hX hYStrict hXY hYA hError hShortProduct hMassI
    hThresholdI hMassII hThresholdII ρ
  have hT₁T : T₁ ≤ T := (le_max_left T₁ T₂).trans hT
  have hT₂T : T₂ ≤ T := (le_max_right T₁ T₂).trans hT
  have hTEight : 8 ≤ T := hT₁.trans hT₁T
  have hTpos : 0 < T := by linarith
  let A := ⌊sharpZetaCutoff T⌋₊
  let q := T ^ (-D₁)
  have hqPos : 0 < q := Real.rpow_pos_of_pos hTpos _
  have hA : 1 < A := by
    have hCutNonneg : 0 ≤ sharpZetaCutoff T :=
      (four_mul_lt_sharpZetaCutoff T).le.trans'
        (mul_nonneg (by norm_num) hTpos.le)
    have hTwo : (2 : ℝ) ≤ sharpZetaCutoff T := by
      linarith [four_mul_lt_sharpZetaCutoff T]
    have hTwoNat : 2 ≤ A := (Nat.le_floor_iff hCutNonneg).mpr hTwo
    omega
  have hY : 1 ≤ Y := hX.trans hXY
  have hRect : (ρ : ℂ) ∈ zerosInRect σ 1 T (2 * T) := ρ.2
  change (ρ : ℂ) ∈
    (riemannZeta_finite_zeros_in_rect σ 1 T (2 * T)).toFinset at hRect
  rw [Set.Finite.mem_toFinset, Set.mem_inter_iff, mem_ZeroRectangle] at hRect
  by_cases hChoice : ChoosesClassicalTypeI Y q (ρ : ℂ)
  · have hSharp : ‖classicalZetaPartialSum A (ρ : ℂ)‖ ≤ q / 2 := by
      have hBase := norm_zeta_zero_sharp_cutoff_sum_le
        (by linarith) ρ.2 (by linarith : 0 < σ)
      have hBase' : ‖classicalZetaPartialSum A (ρ : ℂ)‖ ≤
          149 * sharpZetaCutoff T ^ (-(ρ : ℂ).re) := by
        simpa only [A, classicalZetaPartialSum] using hBase
      have hError' : 149 * sharpZetaCutoff T ^ (-(ρ : ℂ).re) ≤ q / 2 := by
        simpa only [q] using hError ρ ρ.2
      exact hBase'.trans hError'
    have hLong : q / 2 ≤ ‖classicalZetaLongTail Y A (ρ : ℂ)‖ := by
      have hRaw := classical_typeI_of_short_sum_large A Y (ρ : ℂ)
        (q / 2) q (by simpa only [A] using hYA) hSharp hChoice
      calc
        q / 2 = q - q / 2 := by ring
        _ ≤ ‖classicalZetaLongTail Y A (ρ : ℂ)‖ := hRaw
    obtain ⟨t, htShift, htLarge⟩ := hBetaI σ T (ρ : ℂ)
      (classicalZetaLongTailSupport Y A) (fun _n => 1) (q / 2)
      hσ.le hσUpper hT₁T hRect.1.1 hRect.1.2.1
      (classicalZetaLongTailSupport_pos Y A)
      (by simpa only [A] using hMassI)
      (by simpa only [q, neg_add] using hThresholdI)
      (by simpa only [classicalZetaLongTail_eq_finiteDirichletSeries] using hLong)
    have htInterval : T - T ^ δ ≤ t ∧ t ≤ 2 * T + T ^ δ := by
      rw [abs_le] at htShift
      constructor <;> linarith [hRect.1.2.2.1, hRect.1.2.2.2]
    have htLarge' : (3 / 4) * (q / 2) ≤
        ‖classicalZetaLongTail Y A ((σ : ℂ) + I * (t : ℂ))‖ := by
      simpa only [classicalZetaLongTail_eq_finiteDirichletSeries] using htLarge
    obtain ⟨r, hr, hrLarge⟩ := exists_classicalZetaLong_large_dyadic_block
      Y A σ t ((3 / 4) * (q / 2)) hY hA htLarge'
    let rf : Fin (Nat.clog 2 A) := ⟨r, Finset.mem_range.mp hr⟩
    refine ⟨t, some (Sum.inl ?_), by simpa [abs_sub_comm] using htShift,
      htInterval, ?_⟩
    · simpa only [A] using rf
    · change ClassicalTypeILargeAt σ T D₁ Y
        (by simpa only [A] using rf) t
      refine ⟨?_, ?_⟩
      · simpa only [ClassicalTypeILargeAt, q, A] using hrLarge
      · simpa only [ClassicalTypeILargeAt, q, A] using htLarge'
  · have hShort : ‖classicalZetaPartialSum Y (ρ : ℂ)‖ ≤ q :=
      (lt_of_not_ge hChoice).le
    have hTailRaw := classical_typeII_of_short_sum_small Y X (ρ : ℂ) q
      (X : ℝ) hY hX hXY hqPos.le hShort
      (norm_zetaMollifier_le_length X (ρ : ℂ) (by linarith [hRect.1.1]))
    have hTail : 3 / 4 ≤ ‖sharpMollifiedTail Y X (ρ : ℂ)‖ := by
      linarith [hTailRaw, hShortProduct]
    obtain ⟨t, htShift, htLarge⟩ := hBetaII σ T (ρ : ℂ)
      (sharpMollifiedTailSupport Y X) (sharpMollifiedCoeff Y X) (3 / 4)
      hσ.le hσUpper hT₂T hRect.1.1 hRect.1.2.1
      (sharpMollifiedTailSupport_pos Y X) hMassII hThresholdII
      (by simpa only [sharpMollifiedTail] using hTail)
    have htInterval : T - T ^ δ ≤ t ∧ t ≤ 2 * T + T ^ δ := by
      rw [abs_le] at htShift
      constructor <;> linarith [hRect.1.2.2.1, hRect.1.2.2.2]
    have htLarge' : (3 / 4) * (3 / 4) ≤
        ‖sharpMollifiedTail Y X ((σ : ℂ) + I * (t : ℂ))‖ := by
      simpa only [sharpMollifiedTail] using htLarge
    obtain ⟨r, hr, hrLarge⟩ := exists_sharpMollified_large_dyadic_block
      Y X σ t ((3 / 4) * (3 / 4)) hYStrict htLarge'
    let rf : Fin (Nat.clog 2 Y) := ⟨r, Finset.mem_range.mp hr⟩
    refine ⟨t, some (Sum.inr rf), by simpa [abs_sub_comm] using htShift,
      htInterval, ?_⟩
    change ClassicalTypeIILargeAt σ Y X rf t
    simpa only [ClassicalTypeIILargeAt] using hrLarge

/-- Simultaneously choose the source beta-removal ordinate and branch/scale
color for every distinct zero in the slab. -/
theorem classicalSlab_exists_shifted_branch_scale
    (σ δ B₁ D₁ B₂ D₂ : ℝ)
    (hσ : 1 / 2 < σ) (hσUpper : σ ≤ 1) (hδ : 0 < δ) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧
      ∀ (T : ℝ) (Y X : ℕ), T₀ ≤ T →
        1 ≤ X → 1 < Y → X ≤ Y → Y ≤ ⌊sharpZetaCutoff T⌋₊ →
        (∀ ρ ∈ zerosInRect σ 1 T (2 * T),
          149 * sharpZetaCutoff T ^ (-ρ.re) ≤ T ^ (-D₁) / 2) →
        T ^ (-D₁) * (X : ℝ) ≤ 1 / 4 →
        finiteDirichletMass (classicalZetaLongTailSupport Y
            ⌊sharpZetaCutoff T⌋₊) (fun _n => 1) ≤ T ^ B₁ →
        T ^ (-D₁ - 1) ≤ T ^ (-D₁) / 2 →
        finiteDirichletMass (sharpMollifiedTailSupport Y X)
            (sharpMollifiedCoeff Y X) ≤ T ^ B₂ →
        T ^ (-D₂) ≤ 3 / 4 →
        ∃ (shiftedZero : ↥(zerosInRect σ 1 T (2 * T)) → ℝ)
          (baseColor : ↥(zerosInRect σ 1 T (2 * T)) →
            ClassicalBranchScaleColor T Y),
          (∀ ρ : ↥(zerosInRect σ 1 T (2 * T)),
            |(ρ : ℂ).im - shiftedZero ρ| ≤ T ^ δ) ∧
          (∀ ρ : ↥(zerosInRect σ 1 T (2 * T)),
            T - T ^ δ ≤ shiftedZero ρ ∧
            shiftedZero ρ ≤ 2 * T + T ^ δ) ∧
          ∀ ρ : ↥(zerosInRect σ 1 T (2 * T)),
            ClassicalBranchScaleLarge σ T D₁ Y X
            (baseColor ρ) (shiftedZero ρ) := by
  obtain ⟨T₀, hT₀, hEach⟩ :=
    classicalZero_exists_shifted_branch_scale σ δ B₁ D₁ B₂ D₂
      hσ hσUpper hδ
  refine ⟨T₀, hT₀, ?_⟩
  intro T Y X hT hX hYStrict hXY hYA hError hShortProduct hMassI
    hThresholdI hMassII hThresholdII
  have hWitness := hEach T Y X hT hX hYStrict hXY hYA hError
    hShortProduct hMassI hThresholdI hMassII hThresholdII
  choose shiftedZero baseColor hdata using hWitness
  exact ⟨shiftedZero, baseColor, fun ρ => (hdata ρ).1,
    fun ρ => (hdata ρ).2.1, fun ρ => (hdata ρ).2.2⟩

/-- The copy type has exactly the native analytic-multiplicity zero count. -/
theorem classicalSlabZeroCopy_card (σ T : ℝ) :
    Fintype.card (ClassicalSlabZeroCopy σ T) =
      zeroCountRect σ 1 T (2 * T) := by
  exact weightedCopy_card (zerosInRect σ 1 T (2 * T))
    (analyticVanishingOrder riemannZeta)

/-- Shifted unit-bin occupancy is exactly the corresponding weighted sum on
the attached native zero finset. -/
theorem classicalSlabZeroCopy_shifted_unitBin_card
    (σ T : ℝ) (shift : ↥(zerosInRect σ 1 T (2 * T)) → ℝ) (z : ℤ) :
    (unitBinFinset
      (fun x : ClassicalSlabZeroCopy σ T => shift x.1) z).card =
      ∑ ρ ∈ (zerosInRect σ 1 T (2 * T)).attach.filter
        (fun ρ => ⌊shift ρ⌋ = z),
        analyticVanishingOrder riemannZeta ρ.1 := by
  exact weightedCopy_unitBin_card (zerosInRect σ 1 T (2 * T))
    (analyticVanishingOrder riemannZeta) shift z

/-- Extend a shifted ordinate from the attached slab to all complex numbers.
Only values on the slab enter the subsequent finite sums. -/
def extendClassicalSlabShift (σ T : ℝ)
    (shift : ↥(zerosInRect σ 1 T (2 * T)) → ℝ) : ℂ → ℝ :=
  fun ρ => if hρ : ρ ∈ zerosInRect σ 1 T (2 * T) then shift ⟨ρ, hρ⟩ else 0

@[simp] theorem extendClassicalSlabShift_apply (σ T : ℝ)
    (shift : ↥(zerosInRect σ 1 T (2 * T)) → ℝ)
    (ρ : ↥(zerosInRect σ 1 T (2 * T))) :
    extendClassicalSlabShift σ T shift ρ = shift ρ := by
  simp [extendClassicalSlabShift, ρ.2]

/-- A displacement bound converts the native unshifted Jensen cap into a
shifted unit-bin cap for all analytic-multiplicity copies in the slab. -/
theorem classicalSlabZeroCopy_shifted_unitBin_card_le
    (σ T H : ℝ) (L₀ : ℕ)
    (shift : ↥(zerosInRect σ 1 T (2 * T)) → ℝ)
    (hshift : ∀ ρ : ↥(zerosInRect σ 1 T (2 * T)),
      |(ρ : ℂ).im - shift ρ| ≤ H)
    (hlocal : ∀ z : ℤ,
      ∑ ρ ∈ (zerosInRect σ 1 T (2 * T)).filter
        (fun ρ => (z : ℝ) ≤ ρ.im ∧ ρ.im < (z : ℝ) + 1),
        analyticVanishingOrder riemannZeta ρ ≤ L₀) :
    ∀ z : ℤ,
      (unitBinFinset
        (fun x : ClassicalSlabZeroCopy σ T => shift x.1) z).card ≤
          (2 * Nat.ceil H + 1) * L₀ := by
  classical
  intro z
  rw [classicalSlabZeroCopy_shifted_unitBin_card]
  have hnative := shifted_bin_weight_le_of_unit_bin_weight
    (zerosInRect σ 1 T (2 * T)) (analyticVanishingOrder riemannZeta)
    Complex.im (extendClassicalSlabShift σ T shift) H L₀
    (fun ρ hρ => by
      simpa only [extendClassicalSlabShift, dif_pos hρ] using hshift ⟨ρ, hρ⟩)
    hlocal z
  let A := (zerosInRect σ 1 T (2 * T)).filter
    (fun ρ => (z : ℝ) ≤ extendClassicalSlabShift σ T shift ρ ∧
      extendClassicalSlabShift σ T shift ρ < (z : ℝ) + 1)
  have hfiber := Finset.sum_fiberwise_eq_sum_filter
    (zerosInRect σ 1 T (2 * T))
    (((zerosInRect σ 1 T (2 * T)).image
      (extendClassicalSlabShift σ T shift)).filter
        (fun t => (z : ℝ) ≤ t ∧ t < (z : ℝ) + 1))
    (extendClassicalSlabShift σ T shift)
    (analyticVanishingOrder riemannZeta)
  have hfilter : (zerosInRect σ 1 T (2 * T)).filter
      (fun ρ => extendClassicalSlabShift σ T shift ρ ∈
        (((zerosInRect σ 1 T (2 * T)).image
          (extendClassicalSlabShift σ T shift)).filter
            (fun t => (z : ℝ) ≤ t ∧ t < (z : ℝ) + 1))) = A := by
    apply Finset.filter_congr
    intro ρ hρ
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨⟨ρ, hρ, rfl⟩, h⟩
  rw [hfilter] at hfiber
  have hattach :
      (∑ ρ ∈ (zerosInRect σ 1 T (2 * T)).attach.filter
          (fun ρ => ⌊shift ρ⌋ = z),
          analyticVanishingOrder riemannZeta ρ.1) =
        ∑ ρ ∈ A, analyticVanishingOrder riemannZeta ρ := by
    simpa only [A, Finset.sum_filter, extendClassicalSlabShift_apply,
      Int.floor_eq_iff] using
      (Finset.sum_attach (zerosInRect σ 1 T (2 * T))
        (fun ρ => if
          (z : ℝ) ≤ extendClassicalSlabShift σ T shift ρ ∧
            extendClassicalSlabShift σ T shift ρ < (z : ℝ) + 1
          then analyticVanishingOrder riemannZeta ρ else 0))
  rw [hattach, ← hfiber]
  exact hnative

/-- Bounded beta removal changes slab energy only by the explicit tolerance
factor, without changing the multiplicity index type. -/
theorem classicalSlabZeroEnergy_le_shifted_unit
    (σ T d : ℝ) (shifted : ClassicalSlabZeroCopy σ T → ℝ)
    (hshift : ∀ z, |shifted z - (z.1.1 : ℂ).im| ≤ d) :
    classicalSlabZeroEnergy σ T ≤
      (4 * Nat.ceil (1 + 4 * d) + 6) *
        approximateAdditiveEnergyOf 1 shifted := by
  exact (approximateAdditiveEnergyOf_perturbation_le
    (W := fun z : ClassicalSlabZeroCopy σ T => (z.1.1 : ℂ).im)
    (W' := shifted) (r := 1) (d := d) hshift).trans
    (approximateAdditiveEnergyOf_le_natCeil_mul_unit (1 + 4 * d) shifted)

/-- A fixed classical order used solely for deterministic unit-bin ranks. -/
noncomputable instance classicalSlabZeroCopyLinearOrder (σ T : ℝ) :
    LinearOrder (ClassicalSlabZeroCopy σ T) :=
  WellOrderingRel.isWellOrder.linearOrder

/-- A source branch/scale color refined by parity and local unit-bin rank. -/
abbrev ClassicalSeparatedBranchScaleColor (T : ℝ) (Y L : ℕ) :=
  ClassicalBranchScaleColor T Y × (ZMod 2 × Fin (L + 1))

/-- The actual refined coloring used by the classical slab energy split. -/
noncomputable def classicalSeparatedBranchScaleColor
    (σ T : ℝ) (Y : ℕ)
    (shiftedZero : ↥(zerosInRect σ 1 T (2 * T)) → ℝ)
    (baseColor : ↥(zerosInRect σ 1 T (2 * T)) →
      ClassicalBranchScaleColor T Y)
    (L : ℕ)
    (hlocal : ∀ z : ℤ,
      (unitBinFinset
        (fun x : ClassicalSlabZeroCopy σ T => shiftedZero x.1) z).card ≤ L) :
    ClassicalSlabZeroCopy σ T → ClassicalSeparatedBranchScaleColor T Y L :=
  separatedRefinementColor (fun x => shiftedZero x.1)
    (fun x => baseColor x.1) L hlocal

/-- Extend a half-open native dyadic coefficient sequence to the closed
paper support by assigning the omitted left endpoint coefficient zero. -/
def closedDyadicCoeff (N : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n = N then 0 else a n

/-- The closed-support sum with zero left endpoint is exactly the native
half-open Dirichlet polynomial. -/
theorem sum_closedDyadicCoeff_eq_dirichletPoly
    (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    (∑ n ∈ Finset.Icc N (2 * N),
      closedDyadicCoeff N a n * dirichletPhase n t) =
        dirichletPoly N a t := by
  have hinterval : Finset.Icc N (2 * N) =
      insert N (dyadicInterval N) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert, dyadicInterval,
      Finset.mem_Ioc]
    omega
  rw [hinterval]
  have hNnot : N ∉ dyadicInterval N := by simp [dyadicInterval]
  rw [Finset.sum_insert hNnot]
  simp only [closedDyadicCoeff, if_pos, zero_mul, zero_add, dirichletPoly]
  apply Finset.sum_congr rfl
  intro n hn
  have hnN : n ≠ N := by
    rw [dyadicInterval, Finset.mem_Ioc] at hn
    omega
  rw [if_neg hnN]
  congr 1
  unfold dirichletPhase
  congr 1
  ring

/-- Package any indexed, one-separated native Dirichlet-polynomial family as
an exact paper `LargeValuePattern`, preserving its indexed energy. -/
def indexedDirichletLargeValuePattern
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (threshold a b : ℝ) (coeff : ℕ → ℂ) (W : ι → ℝ)
    (hN : 1 < N) (hthreshold : 0 < threshold) (hab : a < b)
    (hcoeff : ∀ n ∈ dyadicInterval N, ‖coeff n‖ ≤ 1)
    (hW : ∀ x, a ≤ W x ∧ W x ≤ b)
    (hsep : ∀ x y : ι, x ≠ y → 1 ≤ |W x - W y|)
    (hlarge : ∀ x, threshold ≤ ‖dirichletPoly N coeff (W x)‖) :
    LargeValuePattern where
  N := N
  scale := N
  T := b - a
  V := threshold
  coeff := closedDyadicCoeff N coeff
  indices := Finset.Icc N (2 * N)
  intervalLeft := a
  intervalRight := b
  ordinates := Finset.univ.image W
  N_eq_scale := rfl
  one_lt_N := by exact_mod_cast hN
  T_pos := sub_pos.mpr hab
  V_pos := hthreshold
  mem_indices_iff := by
    intro n
    simp only [Finset.mem_Icc]
    norm_cast
  coeff_one_bounded := by
    intro n hn
    by_cases hnN : n = N
    · simp [closedDyadicCoeff, hnN]
    · rw [closedDyadicCoeff, if_neg hnN]
      apply hcoeff n
      rw [Finset.mem_Icc] at hn
      change n ∈ Finset.Ioc N (2 * N)
      rw [Finset.mem_Ioc]
      exact ⟨lt_of_le_of_ne hn.1 (Ne.symm hnN), hn.2⟩
  interval_length := rfl
  ordinates_in_interval := by
    intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨x, _, rfl⟩ := ht
    exact hW x
  ordinates_oneSeparated :=
    image_isOneSeparated_of_indexed_oneSeparated W hsep
  large := by
    intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨x, _, rfl⟩ := ht
    rw [sum_closedDyadicCoeff_eq_dirichletPoly]
    exact hlarge x

@[simp] theorem indexedDirichletLargeValuePattern_ordinates
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (threshold a b : ℝ) (coeff : ℕ → ℂ) (W : ι → ℝ)
    (hN : 1 < N) (hthreshold : 0 < threshold) (hab : a < b)
    (hcoeff : ∀ n ∈ dyadicInterval N, ‖coeff n‖ ≤ 1)
    (hW : ∀ x, a ≤ W x ∧ W x ≤ b)
    (hsep : ∀ x y : ι, x ≠ y → 1 ≤ |W x - W y|)
    (hlarge : ∀ x, threshold ≤ ‖dirichletPoly N coeff (W x)‖) :
    (indexedDirichletLargeValuePattern N threshold a b coeff W hN
      hthreshold hab hcoeff hW hsep hlarge).ordinates =
        Finset.univ.image W := rfl

/-- The generic Dirichlet-pattern packaging preserves indexed energy exactly. -/
theorem indexedDirichletLargeValuePattern_energy_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (threshold a b : ℝ) (coeff : ℕ → ℂ) (W : ι → ℝ)
    (hN : 1 < N) (hthreshold : 0 < threshold) (hab : a < b)
    (hcoeff : ∀ n ∈ dyadicInterval N, ‖coeff n‖ ≤ 1)
    (hW : ∀ x, a ≤ W x ∧ W x ≤ b)
    (hsep : ∀ x y : ι, x ≠ y → 1 ≤ |W x - W y|)
    (hlarge : ∀ x, threshold ≤ ‖dirichletPoly N coeff (W x)‖) :
    finsetAdditiveEnergy
      (indexedDirichletLargeValuePattern N threshold a b coeff W hN
        hthreshold hab hcoeff hW hsep hlarge).ordinates =
      approximateAdditiveEnergyOf 1 W := by
  rw [indexedDirichletLargeValuePattern_ordinates]
  exact finsetAdditiveEnergy_image_eq W hsep

/-- One of the two exact smooth source blocks carries at least half of a
large sharp Type-I dyadic block. -/
theorem exists_large_typeISourceSmoothBlock_of_sharp_large
    (A N : ℕ) (σ V t : ℝ) (hN : 0 < N)
    (hlarge : V ≤
      ‖dirichletPoly N (classicalZetaLongLineCoeff A σ) t‖) :
    ∃ r : Fin 2, V / 2 ≤
      ‖typeISourceSmoothBlock N (min (2 * N) A) r σ t‖ := by
  have hdecomp := dirichletPoly_classicalZetaLongLineCoeff_eq_two_source_blocks
    A N σ t hN
  have hsum : V ≤ ∑ r ∈ Finset.range 2,
      ‖typeISourceSmoothBlock N (min (2 * N) A) r σ t‖ := by
    calc
      V ≤ ‖dirichletPoly N (classicalZetaLongLineCoeff A σ) t‖ := hlarge
      _ = ‖∑ r ∈ Finset.range 2,
          typeISourceSmoothBlock N (min (2 * N) A) r σ t‖ := by rw [hdecomp]
      _ ≤ ∑ r ∈ Finset.range 2,
          ‖typeISourceSmoothBlock N (min (2 * N) A) r σ t‖ :=
        norm_sum_le _ _
  by_cases hzero : V / 2 ≤
      ‖typeISourceSmoothBlock N (min (2 * N) A) 0 σ t‖
  · exact ⟨0, hzero⟩
  · refine ⟨1, ?_⟩
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hsum
    have hzero' := lt_of_not_ge hzero
    change V / 2 ≤
      ‖typeISourceSmoothBlock N (min (2 * N) A) 1 σ t‖
    by_contra hone
    have hone' : ‖typeISourceSmoothBlock N (min (2 * N) A) 1 σ t‖ <
        V / 2 := lt_of_not_ge hone
    linarith

/-- Deterministically choose the large smooth block for each member of an
indexed sharp Type-I family. -/
noncomputable def chosenTypeISourceSmoothBlock
    {ι : Type*} (A N : ℕ) (σ V : ℝ) (W : ι → ℝ) (hN : 0 < N)
    (hlarge : ∀ x, V ≤
      ‖dirichletPoly N (classicalZetaLongLineCoeff A σ) (W x)‖)
    (x : ι) : Fin 2 :=
  Classical.choose
    (exists_large_typeISourceSmoothBlock_of_sharp_large A N σ V (W x)
      hN (hlarge x))

theorem chosenTypeISourceSmoothBlock_large
    {ι : Type*} (A N : ℕ) (σ V : ℝ) (W : ι → ℝ) (hN : 0 < N)
    (hlarge : ∀ x, V ≤
      ‖dirichletPoly N (classicalZetaLongLineCoeff A σ) (W x)‖)
    (x : ι) :
    V / 2 ≤ ‖typeISourceSmoothBlock N (min (2 * N) A)
      (chosenTypeISourceSmoothBlock A N σ V W hN hlarge x) σ (W x)‖ :=
  Classical.choose_spec
    (exists_large_typeISourceSmoothBlock_of_sharp_large A N σ V (W x)
      hN (hlarge x))

/-! ## Scale-independent deweighting of the sharp Type-I block -/

/-- The sharp classical Type-I polynomial is exactly the weighted sum on its
active interval. -/
theorem dirichletPoly_classicalZetaLongLineCoeff_eq_active_sum
    (A N : ℕ) (σ t : ℝ) :
    dirichletPoly N (classicalZetaLongLineCoeff A σ) t =
      ∑ n ∈ Finset.Ioc N (min (2 * N) A),
        (n : ℂ) ^ (-(σ : ℂ)) *
          (n : ℂ) ^ (-(t : ℂ) * I) := by
  unfold dirichletPoly dyadicInterval classicalZetaLongLineCoeff
  calc
    (∑ n ∈ Finset.Ioc N (2 * N),
        (if n ≤ A then (n : ℂ) ^ (-(σ : ℂ)) else 0) *
          (n : ℂ) ^ (-(t : ℂ) * I)) =
      ∑ n ∈ Finset.Ioc N (2 * N),
        if n ≤ A then
          (n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-(t : ℂ) * I)
        else 0 := by
          apply Finset.sum_congr rfl
          intro n _
          split_ifs <;> simp_all
    _ = ∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n ≤ A),
        (n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-(t : ℂ) * I) := by
          rw [Finset.sum_filter]
    _ = ∑ n ∈ Finset.Ioc N (min (2 * N) A),
        (n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-(t : ℂ) * I) := by
          congr 1
          ext n
          simp only [Finset.mem_filter, Finset.mem_Ioc]
          omega

/-- The exact sharp Type-I active interval contains at most one dyadic block's
worth of integers. -/
theorem card_classicalTypeI_activeInterval_le
    (A N : ℕ) : (Finset.Ioc N (min (2 * N) A)).card ≤ N := by
  rw [Nat.card_Ioc]
  omega

/-- On the right half-plane, the physical scale and active cardinality in the
sharp Fourier tail are bounded by the dyadic scale itself. -/
theorem classicalTypeI_scale_activeCard_le
    (A N : ℕ) (σ : ℝ) (hN : 0 < N) (hσ : 0 ≤ σ) :
    (N : ℝ) ^ (-σ) * (Finset.Ioc N (min (2 * N) A)).card ≤ N := by
  have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow : (N : ℝ) ^ (-σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hNOne (neg_nonpos.mpr hσ)
  have hcard : ((Finset.Ioc N (min (2 * N) A)).card : ℝ) ≤ N := by
    exact_mod_cast card_classicalTypeI_activeInterval_le A N
  calc
    (N : ℝ) ^ (-σ) * (Finset.Ioc N (min (2 * N) A)).card ≤
        1 * (Finset.Ioc N (min (2 * N) A)).card :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    _ ≤ 1 * N := by gcongr
    _ = N := one_mul _

/-- Coefficient-one realization of the active sharp Type-I interval inside a
full dyadic block. -/
def classicalTypeICoefficientOneCoeff (A : ℕ) (n : ℕ) : ℂ :=
  if n ≤ A then 1 else 0

theorem norm_classicalTypeICoefficientOneCoeff_le_one
    (A n : ℕ) : ‖classicalTypeICoefficientOneCoeff A n‖ ≤ 1 := by
  unfold classicalTypeICoefficientOneCoeff
  split_ifs <;> simp

/-- The coefficient-one polynomial is exactly the sum on the active sharp
interval; no endpoint or support enlargement is hidden. -/
theorem dirichletPoly_classicalTypeICoefficientOneCoeff_eq_active_sum
    (A N : ℕ) (t : ℝ) :
    dirichletPoly N (classicalTypeICoefficientOneCoeff A) t =
      ∑ n ∈ Finset.Ioc N (min (2 * N) A), dirichletPhase n t := by
  unfold dirichletPoly dyadicInterval classicalTypeICoefficientOneCoeff
  calc
    (∑ n ∈ Finset.Ioc N (2 * N),
        (if n ≤ A then (1 : ℂ) else 0) *
          (n : ℂ) ^ (-(t : ℂ) * I)) =
      ∑ n ∈ Finset.Ioc N (2 * N),
        if n ≤ A then (n : ℂ) ^ (-(t : ℂ) * I) else 0 := by
          apply Finset.sum_congr rfl
          intro n _
          split_ifs <;> simp_all
    _ = ∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n ≤ A),
        (n : ℂ) ^ (-(t : ℂ) * I) := by rw [Finset.sum_filter]
    _ = ∑ n ∈ Finset.Ioc N (min (2 * N) A),
        (n : ℂ) ^ (-(t : ℂ) * I) := by
          congr 1
          ext n
          simp only [Finset.mem_filter, Finset.mem_Ioc]
          omega
    _ = ∑ n ∈ Finset.Ioc N (min (2 * N) A),
        dirichletPhase n t := by
          apply Finset.sum_congr rfl
          intro n _
          unfold dirichletPhase
          congr 1
          ring

/-- Package a bounded, one-separated family of active coefficient-one sharp
Type-I sums as the exact paper `LargeValuePattern`. -/
noncomputable def indexedClassicalTypeICoefficientOnePattern
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A N : ℕ) (threshold a b : ℝ) (W : ι → ℝ)
    (hN : 1 < N) (hthreshold : 0 < threshold) (hab : a < b)
    (hW : ∀ x, a ≤ W x ∧ W x ≤ b)
    (hsep : ∀ x y : ι, x ≠ y → 1 ≤ |W x - W y|)
    (hlarge : ∀ x, threshold ≤
      ‖∑ n ∈ Finset.Ioc N (min (2 * N) A), dirichletPhase n (W x)‖) :
    LargeValuePattern :=
  indexedDirichletLargeValuePattern N threshold a b
    (classicalTypeICoefficientOneCoeff A) W hN hthreshold hab
    (fun n _hn => norm_classicalTypeICoefficientOneCoeff_le_one A n) hW hsep
    (fun x => by
      rw [dirichletPoly_classicalTypeICoefficientOneCoeff_eq_active_sum]
      exact hlarge x)

/-- The coefficient-one sharp Type-I pattern retains indexed additive energy
exactly. -/
theorem indexedClassicalTypeICoefficientOnePattern_energy_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A N : ℕ) (threshold a b : ℝ) (W : ι → ℝ)
    (hN : 1 < N) (hthreshold : 0 < threshold) (hab : a < b)
    (hW : ∀ x, a ≤ W x ∧ W x ≤ b)
    (hsep : ∀ x y : ι, x ≠ y → 1 ≤ |W x - W y|)
    (hlarge : ∀ x, threshold ≤
      ‖∑ n ∈ Finset.Ioc N (min (2 * N) A), dirichletPhase n (W x)‖) :
    finsetAdditiveEnergy
        (indexedClassicalTypeICoefficientOnePattern
          A N threshold a b W hN hthreshold hab hW hsep hlarge).ordinates =
      approximateAdditiveEnergyOf 1 W := by
  unfold indexedClassicalTypeICoefficientOnePattern
  apply indexedDirichletLargeValuePattern_energy_eq

/-- A pointwise `d`-perturbation of ordinates in `[a,b]` lies in the expanded
interval `[a-d,b+d]`. -/
theorem perturbedOrdinate_mem_expandedInterval
    {ι : Type*} (W W' : ι → ℝ) (a b d : ℝ)
    (hW : ∀ x, a ≤ W x ∧ W x ≤ b)
    (hpert : ∀ x, |W' x - W x| ≤ d) (x : ι) :
    a - d ≤ W' x ∧ W' x ≤ b + d := by
  have hdiff := (abs_le.mp (hpert x))
  constructor <;> linarith [hW x]

/-- Constant-factor absorption for the common height interval used after the
source beta-removal displacement and the Fourier displacement.  A half-width
exponent window for `T` becomes the full requested window for the expanded
interval once the fixed factor five is absorbed. -/
theorem classicalSlab_expanded_height_in_rpow_window
    (N : ℕ) (T u d tau delta : ℝ)
    (hN : 1 ≤ (N : ℝ)) (hdelta : 0 < delta)
    (hu : 0 ≤ u) (huT : u ≤ T) (hd : 0 ≤ d) (hdT : d ≤ T)
    (hTLower : (N : ℝ) ^ (tau - delta / 2) ≤ T)
    (hTUpper : T ≤ (N : ℝ) ^ (tau + delta / 2))
    (hFive : 5 ≤ (N : ℝ) ^ (delta / 2)) :
    (N : ℝ) ^ (tau - delta) ≤
        (2 * T + u + d) - (T - u - d) ∧
      (2 * T + u + d) - (T - u - d) ≤
        (N : ℝ) ^ (tau + delta) := by
  have hNPos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN
  have hTNonneg : 0 ≤ T :=
    (Real.rpow_nonneg hNPos.le (tau - delta / 2)).trans hTLower
  constructor
  · calc
      (N : ℝ) ^ (tau - delta) ≤
          (N : ℝ) ^ (tau - delta / 2) := by
        apply Real.rpow_le_rpow_of_exponent_le hN
        linarith
      _ ≤ T := hTLower
      _ ≤ (2 * T + u + d) - (T - u - d) := by linarith
  · calc
      (2 * T + u + d) - (T - u - d) ≤ 5 * T := by linarith
      _ ≤ (N : ℝ) ^ (delta / 2) * T :=
        mul_le_mul_of_nonneg_right hFive hTNonneg
      _ ≤ (N : ℝ) ^ (delta / 2) *
          (N : ℝ) ^ (tau + delta / 2) :=
        mul_le_mul_of_nonneg_left hTUpper
          (Real.rpow_nonneg hNPos.le (delta / 2))
      _ = (N : ℝ) ^ (tau + delta) := by
        rw [← Real.rpow_add hNPos]
        congr 1
        ring

/-- A fixed compact logarithmic profile equal to `exp (-σu)` throughout the
logarithmic image of every dyadic interval. -/
noncomputable def classicalTypeILogProfile (σ u : ℝ) : ℂ :=
  gmAffineLocalBumpFunction u * Complex.exp ((((-σ * u : ℝ) : ℂ)))

theorem contDiff_classicalTypeILogProfile (σ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (classicalTypeILogProfile σ) := by
  unfold classicalTypeILogProfile
  have hinside : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => -σ * u) := by
    fun_prop
  have hpow : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ =>
      Complex.exp ((((-σ * u : ℝ) : ℂ)))) :=
    Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.comp hinside)
  exact contDiff_gmAffineLocalBumpFunction.mul hpow

theorem hasCompactSupport_classicalTypeILogProfile (σ : ℝ) :
    HasCompactSupport (classicalTypeILogProfile σ) := by
  exact hasCompactSupport_gmAffineLocalBumpFunction.mul_right

/-- Schwartz realization of the scale-independent sharp-block profile. -/
noncomputable def classicalTypeILogProfileSchwartz (σ : ℝ) :
    SchwartzMap ℝ ℂ :=
  (hasCompactSupport_classicalTypeILogProfile σ).toSchwartzMap
    (contDiff_classicalTypeILogProfile σ)

@[simp]
theorem classicalTypeILogProfileSchwartz_apply (σ u : ℝ) :
    classicalTypeILogProfileSchwartz σ u = classicalTypeILogProfile σ u := rfl

/-- Exact scale normalization of the fixed sharp-block profile. -/
theorem classicalTypeILogProfile_scale_identity
    {N n : ℕ} {σ : ℝ} (hN : 0 < N) (hn : n ∈ dyadicInterval N) :
    ((((N : ℝ) ^ (-σ) : ℝ) : ℂ) *
        classicalTypeILogProfile σ
          (Real.log (n : ℝ) - Real.log (N : ℝ))) =
      (n : ℂ) ^ (-(σ : ℂ)) := by
  have hnPos : 0 < n := hN.trans (Finset.mem_Ioc.mp hn).1
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hnne : (n : ℂ) ≠ 0 := by exact_mod_cast hnPos.ne'
  have hnbase : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_num
  have hbump := gmAffineLocalBumpSchwartz_one_on_dyadicLog hN hn
  rw [gmAffineLocalBumpSchwartz_apply] at hbump
  unfold classicalTypeILogProfile gmAffineLocalBumpFunction
  rw [hbump, one_mul]
  rw [hnbase, Complex.cpow_def_of_ne_zero (hnbase ▸ hnne),
    ← Complex.ofReal_log hnr.le]
  rw [Real.rpow_def_of_pos hNr, Complex.ofReal_exp]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Exact Fourier deweighting of the paper's sharp Type-I block using one
fixed logarithmic profile.  Its Fourier norms are independent of the dyadic
scale and of the sharp upper endpoint. -/
theorem dirichletPoly_classicalZetaLongLineCoeff_fourierDeweight
    (A N : ℕ) (σ t : ℝ) (hN : 0 < N) :
    dirichletPoly N (classicalZetaLongLineCoeff A σ) t =
      ((((N : ℝ) ^ (-σ) : ℝ) : ℂ) *
        ∫ ξ : ℝ, 𝓕 (classicalTypeILogProfileSchwartz σ) ξ *
          Complex.exp
            (-(((2 * Real.pi * ξ * Real.log (N : ℝ) : ℝ) : ℂ) * I)) *
          ∑ n ∈ Finset.Ioc N (min (2 * N) A),
            (n : ℂ) ^
              (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)) := by
  let S : Finset ℕ := Finset.Ioc N (min (2 * N) A)
  have hS : ∀ n ∈ S, 0 < n := by
    intro n hn
    exact hN.trans (Finset.mem_Ioc.mp hn).1
  have hSdyadic : ∀ n ∈ S, n ∈ dyadicInterval N := by
    intro n hn
    rw [dyadicInterval, Finset.mem_Ioc]
    exact ⟨(Finset.mem_Ioc.mp hn).1,
      (Finset.mem_Ioc.mp hn).2.trans (min_le_left _ _)⟩
  have hFourier := fourierDeweightFiniteBlock_logShift_native
    (classicalTypeILogProfileSchwartz σ) S t (Real.log (N : ℝ)) hS
  rw [dirichletPoly_classicalZetaLongLineCoeff_eq_active_sum A N σ t]
  calc
    (∑ n ∈ Finset.Ioc N (min (2 * N) A),
        (n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-(t : ℂ) * I)) =
      ((((N : ℝ) ^ (-σ) : ℝ) : ℂ) *
        ∑ n ∈ S,
          classicalTypeILogProfileSchwartz σ
              (Real.log n - Real.log (N : ℝ)) *
            (n : ℂ) ^ (-(t : ℂ) * I)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n hn
          rw [classicalTypeILogProfileSchwartz_apply]
          have hscale :=
            classicalTypeILogProfile_scale_identity (σ := σ) hN (hSdyadic n hn)
          calc
            (n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-(t : ℂ) * I) =
                (((N : ℝ) ^ (-σ) : ℝ) : ℂ) *
                  classicalTypeILogProfile σ
                    (Real.log (n : ℝ) - Real.log (N : ℝ)) *
                    (n : ℂ) ^ (-(t : ℂ) * I) := by rw [hscale]
            _ = (((N : ℝ) ^ (-σ) : ℝ) : ℂ) *
                (classicalTypeILogProfile σ
                    (Real.log (n : ℝ) - Real.log (N : ℝ)) *
                  (n : ℂ) ^ (-(t : ℂ) * I)) := by ring
    _ = ((((N : ℝ) ^ (-σ) : ℝ) : ℂ) *
        ∫ ξ : ℝ, 𝓕 (classicalTypeILogProfileSchwartz σ) ξ *
          Complex.exp
            (-(((2 * Real.pi * ξ * Real.log (N : ℝ) : ℝ) : ℂ) * I)) *
          ∑ n ∈ Finset.Ioc N (min (2 * N) A),
            (n : ℂ) ^
              (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)) := by
          exact congrArg
            (fun z : ℂ => (((N : ℝ) ^ (-σ) : ℝ) : ℂ) * z) hFourier

/-- Fixed-line Fourier `L¹` majorant for every sharp Type-I dyadic block. -/
noncomputable def classicalTypeIFourierL1 (σ : ℝ) : ℝ :=
  1 + ∫ ξ : ℝ, ‖𝓕 (classicalTypeILogProfileSchwartz σ) ξ‖

theorem classicalTypeIFourierL1_pos (σ : ℝ) :
    0 < classicalTypeIFourierL1 σ := by
  unfold classicalTypeIFourierL1
  have hnonneg : 0 ≤ ∫ ξ : ℝ,
      ‖𝓕 (classicalTypeILogProfileSchwartz σ) ξ‖ :=
    MeasureTheory.integral_nonneg fun _ => norm_nonneg _
  linarith

/-- A large sharp weighted Type-I block yields a coefficient-one sum with a
scale-independent Fourier loss. -/
theorem exists_large_coefficientOne_shift_of_classicalTypeI
    (A N : ℕ) (σ V t : ℝ) (hN : 0 < N) (hV : 0 < V)
    (hlarge : V ≤ ‖dirichletPoly N (classicalZetaLongLineCoeff A σ) t‖) :
    ∃ ξ : ℝ,
      V / (2 * (N : ℝ) ^ (-σ) * classicalTypeIFourierL1 σ) ≤
        ‖∑ n ∈ Finset.Ioc N (min (2 * N) A),
          (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)‖ := by
  let f : SchwartzMap ℝ ℂ := classicalTypeILogProfileSchwartz σ
  let C : ℝ := classicalTypeIFourierL1 σ
  let s : ℝ := (N : ℝ) ^ (-σ)
  let P : ℝ → ℂ := fun ξ =>
    ∑ n ∈ Finset.Ioc N (min (2 * N) A),
      (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)
  have hC : 0 < C := classicalTypeIFourierL1_pos σ
  have hs : 0 < s := by
    dsimp only [s]
    positivity
  have hmass : (∫ ξ : ℝ, ‖𝓕 f ξ‖) ≤ C := by
    have hnonneg : 0 ≤ ∫ ξ : ℝ,
        ‖𝓕 (classicalTypeILogProfileSchwartz σ) ξ‖ :=
      MeasureTheory.integral_nonneg fun _ => norm_nonneg _
    dsimp only [f, C, classicalTypeIFourierL1]
    linarith
  rw [dirichletPoly_classicalZetaLongLineCoeff_fourierDeweight
    A N σ t hN] at hlarge
  change V ≤ ‖(s : ℂ) * ∫ ξ : ℝ,
    𝓕 f ξ *
      Complex.exp
        (-(((2 * Real.pi * ξ * Real.log (N : ℝ) : ℝ) : ℂ) * I)) *
      P ξ‖ at hlarge
  by_contra hexists
  push Not at hexists
  have hthreshold : 0 ≤ V / (2 * s * C) := by positivity
  have hmajorInt : MeasureTheory.Integrable
      (fun ξ : ℝ => ‖𝓕 f ξ‖ * (V / (2 * s * C))) :=
    (𝓕 f).integrable.norm.mul_const _
  have hnorm :
      ‖∫ ξ : ℝ,
        𝓕 f ξ *
          Complex.exp
            (-(((2 * Real.pi * ξ * Real.log (N : ℝ) : ℝ) : ℂ) * I)) *
          P ξ‖ ≤
        ∫ ξ : ℝ, ‖𝓕 f ξ‖ * (V / (2 * s * C)) := by
    apply MeasureTheory.norm_integral_le_of_norm_le hmajorInt
    filter_upwards with ξ
    rw [norm_mul, norm_mul]
    have hphaseNorm :
        ‖Complex.exp
          (-(((2 * Real.pi * ξ * Real.log (N : ℝ) : ℝ) : ℂ) * I))‖ = 1 := by
      simpa only [ofReal_neg, neg_mul] using
        Complex.norm_exp_ofReal_mul_I
          (-(2 * Real.pi * ξ * Real.log (N : ℝ)))
    rw [hphaseNorm, mul_one]
    exact mul_le_mul_of_nonneg_left (hexists ξ).le (norm_nonneg _)
  have hhalf :
      ‖(s : ℂ) * ∫ ξ : ℝ,
        𝓕 f ξ *
          Complex.exp
            (-(((2 * Real.pi * ξ * Real.log (N : ℝ) : ℝ) : ℂ) * I)) *
          P ξ‖ ≤ V / 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    calc
      s * ‖∫ ξ : ℝ,
          𝓕 f ξ *
            Complex.exp
              (-(((2 * Real.pi * ξ * Real.log (N : ℝ) : ℝ) : ℂ) * I)) *
            P ξ‖ ≤
          s * (∫ ξ : ℝ, ‖𝓕 f ξ‖ * (V / (2 * s * C))) :=
        mul_le_mul_of_nonneg_left hnorm hs.le
      _ = s * ((∫ ξ : ℝ, ‖𝓕 f ξ‖) * (V / (2 * s * C))) := by
        rw [MeasureTheory.integral_mul_const]
      _ ≤ s * (C * (V / (2 * s * C))) := by
        gcongr
      _ = V / 2 := by field_simp
  linarith

/-- Exact Fourier deweighting on the actual source interval.  Unlike the
ambient-support version in the imported library, the coefficient-one sum is
restricted to `Ioc Y A`, which is the integer interval carried by the paper's
zeta large-value pattern. -/
theorem typeISourceSmoothBlock_fourierDeweight_restricted
    (Y A r : ℕ) (σ t : ℝ) (hY : 0 < Y) :
    typeISourceSmoothBlock Y A r σ t =
      ∫ ξ : ℝ, 𝓕 (typeILogWeightSchwartz Y A r σ hY) ξ *
        ∑ n ∈ Finset.Ioc Y A,
          (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I) := by
  rw [typeISourceSmoothBlock_eq_restricted]
  have hPositive : ∀ n ∈ Finset.Ioc Y A, 0 < n := by
    intro n hn
    exact hY.trans (Finset.mem_Ioc.mp hn).1
  rw [← fourierDeweightFiniteBlock_native
    (typeILogWeightSchwartz Y A r σ hY) (Finset.Ioc Y A) t hPositive]
  apply Finset.sum_congr rfl
  intro n hn
  rw [typeILogWeightSchwartz_apply,
    typeILogWeight_log_nat Y A r n σ (hPositive n hn),
    typeISourceSmoothWeight, typeITailBoundary_natCast,
    if_pos hn, one_mul]

/-- A positive Fourier `L¹` majorant for an exact source smooth block.  This
quantity is intentionally block-specific; obtaining the uniform/subpower
control needed by the asymptotic argument is a separate analytic step. -/
noncomputable def typeISourceSmoothBlockFourierL1
    (Y A r : ℕ) (σ : ℝ) (hY : 0 < Y) : ℝ :=
  1 + ∫ ξ : ℝ,
    ‖𝓕 (typeILogWeightSchwartz Y A r σ hY) ξ‖

theorem typeISourceSmoothBlockFourierL1_pos
    (Y A r : ℕ) (σ : ℝ) (hY : 0 < Y) :
    0 < typeISourceSmoothBlockFourierL1 Y A r σ hY := by
  unfold typeISourceSmoothBlockFourierL1
  have hnonneg : 0 ≤ ∫ ξ : ℝ,
      ‖𝓕 (typeILogWeightSchwartz Y A r σ hY) ξ‖ :=
    MeasureTheory.integral_nonneg fun _ => norm_nonneg _
  linarith

theorem integral_norm_fourier_typeILogWeight_le
    (Y A r : ℕ) (σ : ℝ) (hY : 0 < Y) :
    (∫ ξ : ℝ, ‖𝓕 (typeILogWeightSchwartz Y A r σ hY) ξ‖) ≤
      typeISourceSmoothBlockFourierL1 Y A r σ hY := by
  unfold typeISourceSmoothBlockFourierL1
  linarith

/-- An explicit order-two tail bound for the Fourier transform of an
arbitrary Schwartz function.  This is the quantitative truncation input used
below; no compactness or nonconstructive choice of a Fourier window remains. -/
theorem integral_norm_fourier_schwartz_compl_Icc_le
    (f : SchwartzMap ℝ ℂ) (R : ℝ) (hR : 0 < R) :
    (∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ, ‖𝓕 f ξ‖) ≤
      2 * SchwartzMap.seminorm ℝ 2 0 (𝓕 f) / R := by
  let F : SchwartzMap ℝ ℂ := 𝓕 f
  let C : ℝ := SchwartzMap.seminorm ℝ 2 0 F
  have hFInt : MeasureTheory.Integrable (fun ξ : ℝ => ‖F ξ‖) :=
    F.integrable.norm
  have hDomInt : MeasureTheory.IntegrableOn
      (fun ξ : ℝ => C * |ξ| ^ (-2 : ℝ)) (Set.Icc (-R) R)ᶜ :=
    (integrableOn_abs_rpow_compl_Icc_typeI (by norm_num) hR).const_mul C
  have hPoint : ∀ᵐ ξ : ℝ ∂MeasureTheory.volume.restrict (Set.Icc (-R) R)ᶜ,
      ‖F ξ‖ ≤ C * |ξ| ^ (-2 : ℝ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc.compl]
      with ξ hξ
    have hAbs : R < |ξ| := by
      by_contra hnot
      exact hξ (abs_le.mp (le_of_not_gt hnot))
    have hAbsPos : 0 < |ξ| := hR.trans hAbs
    have hRaw := SchwartzMap.le_seminorm' ℝ 2 0 F ξ
    change |ξ| ^ 2 * ‖F ξ‖ ≤ C at hRaw
    rw [show |ξ| ^ (-2 : ℝ) = (|ξ| ^ (2 : ℕ))⁻¹ by
      rw [Real.rpow_neg hAbsPos.le]
      norm_num]
    rw [le_mul_inv_iff₀ (pow_pos hAbsPos 2)]
    simpa only [mul_comm] using hRaw
  calc
    (∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ, ‖𝓕 f ξ‖) =
        ∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ, ‖F ξ‖ := by rfl
    _ ≤ ∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ, C * |ξ| ^ (-2 : ℝ) :=
      MeasureTheory.integral_mono_ae hFInt.integrableOn hDomInt hPoint
    _ = C * (2 / R) := by
      rw [MeasureTheory.integral_const_mul]
      congr 1
      rw [integral_abs_rpow_compl_Icc_typeI (by norm_num) hR]
      rw [show (-2 : ℝ) + 1 = -1 by norm_num]
      rw [Real.rpow_neg_one]
      norm_num
      simp only [div_eq_mul_inv]
    _ = 2 * SchwartzMap.seminorm ℝ 2 0 (𝓕 f) / R := by
      dsimp only [C, F]
      ring

/-- Arbitrary-order version of the Schwartz Fourier tail estimate. -/
theorem integral_norm_fourier_schwartz_compl_Icc_le_order
    (f : SchwartzMap ℝ ℂ) (k : ℕ) (hk : 1 < k)
    (R : ℝ) (hR : 0 < R) :
    (∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ, ‖𝓕 f ξ‖) ≤
      (2 * SchwartzMap.seminorm ℝ k 0 (𝓕 f) / ((k : ℝ) - 1)) *
        R ^ (1 - (k : ℝ)) := by
  let F : SchwartzMap ℝ ℂ := 𝓕 f
  let C : ℝ := SchwartzMap.seminorm ℝ k 0 F
  have hkReal : (1 : ℝ) < k := by exact_mod_cast hk
  have hFInt : MeasureTheory.Integrable (fun ξ : ℝ => ‖F ξ‖) :=
    F.integrable.norm
  have hDomInt : MeasureTheory.IntegrableOn
      (fun ξ : ℝ => C * |ξ| ^ (-(k : ℝ))) (Set.Icc (-R) R)ᶜ :=
    (integrableOn_abs_rpow_compl_Icc_typeI (by linarith) hR).const_mul C
  have hPoint : ∀ᵐ ξ : ℝ ∂MeasureTheory.volume.restrict (Set.Icc (-R) R)ᶜ,
      ‖F ξ‖ ≤ C * |ξ| ^ (-(k : ℝ)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc.compl]
      with ξ hξ
    have hAbs : R < |ξ| := by
      by_contra hnot
      exact hξ (abs_le.mp (le_of_not_gt hnot))
    have hAbsPos : 0 < |ξ| := hR.trans hAbs
    have hRaw := SchwartzMap.le_seminorm' ℝ k 0 F ξ
    change |ξ| ^ k * ‖F ξ‖ ≤ C at hRaw
    rw [show |ξ| ^ (-(k : ℝ)) = (|ξ| ^ k)⁻¹ by
      rw [Real.rpow_neg hAbsPos.le]
      norm_num]
    rw [le_mul_inv_iff₀ (pow_pos hAbsPos k)]
    simpa only [mul_comm] using hRaw
  calc
    (∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ, ‖𝓕 f ξ‖) =
        ∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ, ‖F ξ‖ := by rfl
    _ ≤ ∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ,
        C * |ξ| ^ (-(k : ℝ)) :=
      MeasureTheory.integral_mono_ae hFInt.integrableOn hDomInt hPoint
    _ = C * (-2 * R ^ (-(k : ℝ) + 1) / (-(k : ℝ) + 1)) := by
      rw [MeasureTheory.integral_const_mul]
      congr 1
      exact integral_abs_rpow_compl_Icc_typeI (by linarith) hR
    _ = (2 * SchwartzMap.seminorm ℝ k 0 (𝓕 f) / ((k : ℝ) - 1)) *
        R ^ (1 - (k : ℝ)) := by
      dsimp only [C, F]
      rw [show -(k : ℝ) + 1 = 1 - (k : ℝ) by ring]
      field_simp [show (k : ℝ) - 1 ≠ 0 by linarith,
        show 1 - (k : ℝ) ≠ 0 by linarith]
      ring

/-- Arbitrary-order tail bound for the complete sharp Type-I Fourier
representation, including the physical scale factor and active-sum
cardinality. -/
theorem norm_classicalTypeI_fourier_tail_integral_le_order
    (A N k : ℕ) (σ t R : ℝ) (hN : 0 < N) (hk : 1 < k) (hR : 0 < R) :
    ‖(((N : ℝ) ^ (-σ) : ℝ) : ℂ) *
      ∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ,
        𝓕 (classicalTypeILogProfileSchwartz σ) ξ *
          Complex.exp
            (-(((2 * Real.pi * ξ * Real.log (N : ℝ) : ℝ) : ℂ) * I)) *
          ∑ n ∈ Finset.Ioc N (min (2 * N) A),
            (n : ℂ) ^
              (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)‖ ≤
      (N : ℝ) ^ (-σ) * (Finset.Ioc N (min (2 * N) A)).card *
        ((2 * SchwartzMap.seminorm ℝ k 0
            (𝓕 (classicalTypeILogProfileSchwartz σ)) / ((k : ℝ) - 1)) *
          R ^ (1 - (k : ℝ))) := by
  let f : SchwartzMap ℝ ℂ := classicalTypeILogProfileSchwartz σ
  let S : Finset ℕ := Finset.Ioc N (min (2 * N) A)
  let P : ℝ → ℂ := fun ξ =>
    ∑ n ∈ S, (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)
  let g : ℝ → ℂ := fun ξ =>
    𝓕 f ξ *
      Complex.exp
        (-(((2 * Real.pi * ξ * Real.log (N : ℝ) : ℝ) : ℂ) * I)) *
      P ξ
  have hPbound : ∀ ξ : ℝ, ‖P ξ‖ ≤ S.card := by
    intro ξ
    calc
      ‖P ξ‖ ≤ ∑ n ∈ S,
          ‖(n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)‖ :=
        norm_sum_le _ _
      _ = ∑ _n ∈ S, 1 := by
        apply Finset.sum_congr rfl
        intro n hn
        have hnPos : 0 < n := hN.trans (Finset.mem_Ioc.mp hn).1
        rw [Complex.norm_natCast_cpow_of_pos hnPos]
        simp
      _ = S.card := by simp
  have hmajorInt : MeasureTheory.Integrable
      (fun ξ : ℝ => ‖𝓕 f ξ‖ * (S.card : ℝ)) :=
    (𝓕 f).integrable.norm.mul_const _
  have hnorm :
      ‖∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ, g ξ‖ ≤
        ∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ,
          ‖𝓕 f ξ‖ * (S.card : ℝ) := by
    apply MeasureTheory.norm_integral_le_of_norm_le hmajorInt.integrableOn
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc.compl]
      with ξ _
    change ‖𝓕 f ξ *
      Complex.exp
        (-(((2 * Real.pi * ξ * Real.log (N : ℝ) : ℝ) : ℂ) * I)) *
      P ξ‖ ≤ ‖𝓕 f ξ‖ * (S.card : ℝ)
    rw [norm_mul, norm_mul]
    have hphaseNorm :
        ‖Complex.exp
          (-(((2 * Real.pi * ξ * Real.log (N : ℝ) : ℝ) : ℂ) * I))‖ = 1 := by
      simpa only [ofReal_neg, neg_mul] using
        Complex.norm_exp_ofReal_mul_I
          (-(2 * Real.pi * ξ * Real.log (N : ℝ)))
    rw [hphaseNorm, mul_one]
    exact mul_le_mul_of_nonneg_left (hPbound ξ) (norm_nonneg _)
  have htail := integral_norm_fourier_schwartz_compl_Icc_le_order
    f k hk R hR
  have hs : 0 ≤ (N : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  calc
    ‖(((N : ℝ) ^ (-σ) : ℝ) : ℂ) *
      ∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ,
        𝓕 (classicalTypeILogProfileSchwartz σ) ξ *
          Complex.exp
            (-(((2 * Real.pi * ξ * Real.log (N : ℝ) : ℝ) : ℂ) * I)) *
          ∑ n ∈ Finset.Ioc N (min (2 * N) A),
            (n : ℂ) ^
              (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)‖ =
        (N : ℝ) ^ (-σ) *
          ‖∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ, g ξ‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hs]
    _ ≤ (N : ℝ) ^ (-σ) *
        (∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ,
          ‖𝓕 f ξ‖ * (S.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hnorm hs
    _ = (N : ℝ) ^ (-σ) *
        ((∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ, ‖𝓕 f ξ‖) * S.card) := by
      rw [MeasureTheory.integral_mul_const]
    _ ≤ (N : ℝ) ^ (-σ) *
        (((2 * SchwartzMap.seminorm ℝ k 0 (𝓕 f) / ((k : ℝ) - 1)) *
          R ^ (1 - (k : ℝ))) * S.card) := by
      gcongr
    _ = (N : ℝ) ^ (-σ) * (Finset.Ioc N (min (2 * N) A)).card *
        ((2 * SchwartzMap.seminorm ℝ k 0
            (𝓕 (classicalTypeILogProfileSchwartz σ)) / ((k : ℝ) - 1)) *
          R ^ (1 - (k : ℝ))) := by
      dsimp only [f, S]
      ring

/-- Finite-window extraction for the sharp Type-I block.  The sole remaining
premise is the explicit numerical comparison between an arbitrary-order tail
and half the large-value threshold. -/
theorem exists_bounded_coefficientOne_shift_of_classicalTypeI
    (A N k : ℕ) (σ V t R : ℝ) (hN : 0 < N) (hV : 0 < V)
    (hk : 1 < k) (hR : 0 < R)
    (hlarge : V ≤ ‖dirichletPoly N (classicalZetaLongLineCoeff A σ) t‖)
    (htailNumeric :
      (N : ℝ) ^ (-σ) * (Finset.Ioc N (min (2 * N) A)).card *
        ((2 * SchwartzMap.seminorm ℝ k 0
            (𝓕 (classicalTypeILogProfileSchwartz σ)) / ((k : ℝ) - 1)) *
          R ^ (1 - (k : ℝ))) ≤ V / 2) :
    ∃ ξ ∈ Set.Icc (-R) R,
      V / (4 * (N : ℝ) ^ (-σ) * classicalTypeIFourierL1 σ) ≤
        ‖∑ n ∈ Finset.Ioc N (min (2 * N) A),
          (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)‖ := by
  let f : SchwartzMap ℝ ℂ := classicalTypeILogProfileSchwartz σ
  let C : ℝ := classicalTypeIFourierL1 σ
  let s : ℝ := (N : ℝ) ^ (-σ)
  let S : Finset ℕ := Finset.Ioc N (min (2 * N) A)
  let P : ℝ → ℂ := fun ξ =>
    ∑ n ∈ S, (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)
  let g : ℝ → ℂ := fun ξ =>
    𝓕 f ξ *
      Complex.exp
        (-(((2 * Real.pi * ξ * Real.log (N : ℝ) : ℝ) : ℂ) * I)) *
      P ξ
  have hs : 0 < s := by dsimp only [s]; positivity
  have hC : 0 < C := classicalTypeIFourierL1_pos σ
  have hmass : (∫ ξ : ℝ, ‖𝓕 f ξ‖) ≤ C := by
    have hnonneg : 0 ≤ ∫ ξ : ℝ,
        ‖𝓕 (classicalTypeILogProfileSchwartz σ) ξ‖ :=
      MeasureTheory.integral_nonneg fun _ => norm_nonneg _
    dsimp only [f, C, classicalTypeIFourierL1]
    linarith
  have hPcontinuous : Continuous P := by
    dsimp only [P, S]
    apply continuous_finsetSum
    intro n hn
    apply Continuous.const_cpow
    · fun_prop
    · exact Or.inl (by
        exact_mod_cast (Nat.ne_of_gt
          (hN.trans (Finset.mem_Ioc.mp hn).1)))
  have hPbound : ∀ ξ : ℝ, ‖P ξ‖ ≤ S.card := by
    intro ξ
    calc
      ‖P ξ‖ ≤ ∑ n ∈ S,
          ‖(n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)‖ :=
        norm_sum_le _ _
      _ = ∑ _n ∈ S, 1 := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [Complex.norm_natCast_cpow_of_pos
          (hN.trans (Finset.mem_Ioc.mp hn).1)]
        simp
      _ = S.card := by simp
  have hphaseContinuous : Continuous (fun ξ : ℝ =>
      Complex.exp
        (-(((2 * Real.pi * ξ * Real.log (N : ℝ) : ℝ) : ℂ) * I))) := by
    fun_prop
  have hphasePContinuous : Continuous (fun ξ : ℝ =>
      Complex.exp
          (-(((2 * Real.pi * ξ * Real.log (N : ℝ) : ℝ) : ℂ) * I)) *
        P ξ) := hphaseContinuous.mul hPcontinuous
  have hphasePBound : ∀ ξ : ℝ,
      ‖Complex.exp
          (-(((2 * Real.pi * ξ * Real.log (N : ℝ) : ℝ) : ℂ) * I)) *
        P ξ‖ ≤ S.card := by
    intro ξ
    rw [norm_mul]
    have hphaseNorm :
        ‖Complex.exp
          (-(((2 * Real.pi * ξ * Real.log (N : ℝ) : ℝ) : ℂ) * I))‖ = 1 := by
      simpa only [ofReal_neg, neg_mul] using
        Complex.norm_exp_ofReal_mul_I
          (-(2 * Real.pi * ξ * Real.log (N : ℝ)))
    rw [hphaseNorm, one_mul]
    exact hPbound ξ
  have hgInt : MeasureTheory.Integrable g := by
    have hfInt : MeasureTheory.Integrable (fun ξ : ℝ => 𝓕 f ξ) :=
      (𝓕 f).integrable
    have h := hfInt.mul_bdd (c := S.card)
      hphasePContinuous.aestronglyMeasurable
      (by
        filter_upwards with ξ
        exact hphasePBound ξ)
    simpa only [g, mul_assoc] using h
  rw [dirichletPoly_classicalZetaLongLineCoeff_fourierDeweight
    A N σ t hN] at hlarge
  change V ≤ ‖(s : ℂ) * ∫ ξ : ℝ, g ξ‖ at hlarge
  have htail : ‖(s : ℂ) *
      ∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ, g ξ‖ ≤ V / 2 := by
    exact (norm_classicalTypeI_fourier_tail_integral_le_order
      A N k σ t R hN hk hR).trans htailNumeric
  have hsplit := MeasureTheory.integral_add_compl
    (f := g) (s := Set.Icc (-R) R) measurableSet_Icc hgInt
  have hcentralLarge : V / 2 ≤
      ‖(s : ℂ) * ∫ ξ : ℝ in Set.Icc (-R) R, g ξ‖ := by
    have htriangle : ‖(s : ℂ) * ∫ ξ : ℝ, g ξ‖ ≤
        ‖(s : ℂ) * ∫ ξ : ℝ in Set.Icc (-R) R, g ξ‖ +
          ‖(s : ℂ) * ∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ, g ξ‖ := by
      rw [← hsplit, mul_add]
      exact norm_add_le _ _
    linarith
  by_contra hexists
  push Not at hexists
  have hthreshold : 0 ≤ V / (4 * s * C) := by positivity
  have hmajorInt : MeasureTheory.Integrable
      (fun ξ : ℝ => ‖𝓕 f ξ‖ * (V / (4 * s * C))) :=
    (𝓕 f).integrable.norm.mul_const _
  have hcentralNorm :
      ‖∫ ξ : ℝ in Set.Icc (-R) R, g ξ‖ ≤
        ∫ ξ : ℝ in Set.Icc (-R) R,
          ‖𝓕 f ξ‖ * (V / (4 * s * C)) := by
    apply MeasureTheory.norm_integral_le_of_norm_le hmajorInt.integrableOn
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc]
      with ξ hξ
    change ‖𝓕 f ξ *
      Complex.exp
        (-(((2 * Real.pi * ξ * Real.log (N : ℝ) : ℝ) : ℂ) * I)) *
      P ξ‖ ≤ ‖𝓕 f ξ‖ * (V / (4 * s * C))
    rw [norm_mul, norm_mul]
    have hphaseNorm :
        ‖Complex.exp
          (-(((2 * Real.pi * ξ * Real.log (N : ℝ) : ℝ) : ℂ) * I))‖ = 1 := by
      simpa only [ofReal_neg, neg_mul] using
        Complex.norm_exp_ofReal_mul_I
          (-(2 * Real.pi * ξ * Real.log (N : ℝ)))
    rw [hphaseNorm, mul_one]
    exact mul_le_mul_of_nonneg_left (hexists ξ hξ).le (norm_nonneg _)
  have hmajorSplit := MeasureTheory.integral_add_compl
    (f := fun ξ : ℝ => ‖𝓕 f ξ‖ * (V / (4 * s * C)))
    (s := Set.Icc (-R) R) measurableSet_Icc hmajorInt
  have hcentralMajor :
      (∫ ξ : ℝ in Set.Icc (-R) R,
        ‖𝓕 f ξ‖ * (V / (4 * s * C))) ≤
      ∫ ξ : ℝ, ‖𝓕 f ξ‖ * (V / (4 * s * C)) := by
    rw [← hmajorSplit]
    exact le_add_of_nonneg_right
      (MeasureTheory.integral_nonneg fun _ =>
        mul_nonneg (norm_nonneg _) hthreshold)
  have hquarter :
      ‖(s : ℂ) * ∫ ξ : ℝ in Set.Icc (-R) R, g ξ‖ ≤ V / 4 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    calc
      s * ‖∫ ξ : ℝ in Set.Icc (-R) R, g ξ‖ ≤
          s * (∫ ξ : ℝ in Set.Icc (-R) R,
            ‖𝓕 f ξ‖ * (V / (4 * s * C))) :=
        mul_le_mul_of_nonneg_left hcentralNorm hs.le
      _ ≤ s * (∫ ξ : ℝ, ‖𝓕 f ξ‖ * (V / (4 * s * C))) :=
        mul_le_mul_of_nonneg_left hcentralMajor hs.le
      _ = s * ((∫ ξ : ℝ, ‖𝓕 f ξ‖) * (V / (4 * s * C))) := by
        rw [MeasureTheory.integral_mul_const]
      _ ≤ s * (C * (V / (4 * s * C))) := by gcongr
      _ = V / 4 := by field_simp
  linarith

/-- Indexed sharp-block Fourier extraction.  One numerical tail inequality
works for the whole family because the fixed profile and active interval do
not depend on the ordinate; the resulting energy transfer keeps every index. -/
theorem exists_classicalTypeI_boundedOrdinate_family
    {ι : Type*} [Fintype ι]
    (A N k : ℕ) (σ V R : ℝ) (W : ι → ℝ)
    (hN : 0 < N) (hV : 0 < V) (hk : 1 < k) (hR : 0 < R)
    (hlarge : ∀ x,
      V ≤ ‖dirichletPoly N (classicalZetaLongLineCoeff A σ) (W x)‖)
    (htailNumeric :
      (N : ℝ) ^ (-σ) * (Finset.Ioc N (min (2 * N) A)).card *
        ((2 * SchwartzMap.seminorm ℝ k 0
            (𝓕 (classicalTypeILogProfileSchwartz σ)) / ((k : ℝ) - 1)) *
          R ^ (1 - (k : ℝ))) ≤ V / 2) :
    ∃ W' : ι → ℝ,
      (∀ x, |W' x - W x| ≤ 2 * Real.pi * R) ∧
      (∀ x,
        V / (4 * (N : ℝ) ^ (-σ) * classicalTypeIFourierL1 σ) ≤
          ‖∑ n ∈ Finset.Ioc N (min (2 * N) A),
            dirichletPhase n (W' x)‖) ∧
      approximateAdditiveEnergyOf 1 W ≤
        (4 * Nat.ceil (1 + 4 * (2 * Real.pi * R)) + 6) *
          approximateAdditiveEnergyOf 1 W' := by
  classical
  have hwitness : ∀ x : ι, ∃ ξ ∈ Set.Icc (-R) R,
      V / (4 * (N : ℝ) ^ (-σ) * classicalTypeIFourierL1 σ) ≤
        ‖∑ n ∈ Finset.Ioc N (min (2 * N) A),
          (n : ℂ) ^ (-((((W x) - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)‖ :=
    fun x => exists_bounded_coefficientOne_shift_of_classicalTypeI
      A N k σ V (W x) R hN hV hk hR (hlarge x) htailNumeric
  choose ξ hξmem hξlarge using hwitness
  let W' : ι → ℝ := fun x => W x - 2 * Real.pi * ξ x
  have hpert : ∀ x, |W' x - W x| ≤ 2 * Real.pi * R := by
    intro x
    have hξ : |ξ x| ≤ R := (abs_le).2 (hξmem x)
    dsimp only [W']
    rw [show W x - 2 * Real.pi * ξ x - W x = -(2 * Real.pi * ξ x) by ring,
      abs_neg, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ)),
      abs_of_pos Real.pi_pos]
    exact mul_le_mul_of_nonneg_left hξ (by positivity)
  have hlarge' : ∀ x,
      V / (4 * (N : ℝ) ^ (-σ) * classicalTypeIFourierL1 σ) ≤
        ‖∑ n ∈ Finset.Ioc N (min (2 * N) A),
          dirichletPhase n (W' x)‖ := by
    intro x
    calc
      V / (4 * (N : ℝ) ^ (-σ) * classicalTypeIFourierL1 σ) ≤
          ‖∑ n ∈ Finset.Ioc N (min (2 * N) A),
            (n : ℂ) ^ (-((((W x) - 2 * Real.pi * ξ x : ℝ) : ℂ)) * I)‖ :=
        hξlarge x
      _ = ‖∑ n ∈ Finset.Ioc N (min (2 * N) A),
          dirichletPhase n (W' x)‖ := by
        congr 1
        apply Finset.sum_congr rfl
        intro n _
        unfold dirichletPhase
        dsimp only [W']
        congr 1
        ring
  refine ⟨W', hpert, hlarge', ?_⟩
  calc
    approximateAdditiveEnergyOf 1 W ≤
        approximateAdditiveEnergyOf (1 + 4 * (2 * Real.pi * R)) W' :=
      approximateAdditiveEnergyOf_perturbation_le hpert
    _ ≤ (4 * Nat.ceil (1 + 4 * (2 * Real.pi * R)) + 6) *
          approximateAdditiveEnergyOf 1 W' :=
      approximateAdditiveEnergyOf_le_natCeil_mul_unit _ _

/-- Canonical arbitrary-order Fourier radius for the sharp Type-I block. -/
noncomputable def classicalTypeIFourierRadius
    (A N k : ℕ) (σ V : ℝ) : ℝ :=
  (1 +
    4 * ((N : ℝ) ^ (-σ) * (Finset.Ioc N (min (2 * N) A)).card) *
      SchwartzMap.seminorm ℝ k 0
        (𝓕 (classicalTypeILogProfileSchwartz σ)) /
      (((k : ℝ) - 1) * V)) ^ (1 / ((k : ℝ) - 1))

theorem classicalTypeIFourierRadius_pos
    (A N k : ℕ) (σ V : ℝ) (hV : 0 < V) (hk : 1 < k) :
    0 < classicalTypeIFourierRadius A N k σ V := by
  unfold classicalTypeIFourierRadius
  have hkReal : (1 : ℝ) < k := by exact_mod_cast hk
  have hq : 0 < (k : ℝ) - 1 := by linarith
  have hterm : 0 ≤
      4 * ((N : ℝ) ^ (-σ) * (Finset.Ioc N (min (2 * N) A)).card) *
        SchwartzMap.seminorm ℝ k 0
          (𝓕 (classicalTypeILogProfileSchwartz σ)) /
        (((k : ℝ) - 1) * V) := by positivity
  exact Real.rpow_pos_of_pos (by linarith) _

/-- By construction, the canonical arbitrary-order radius makes the complete
sharp Type-I Fourier tail at most half the threshold. -/
theorem classicalTypeIFourierRadius_tail_numeric
    (A N k : ℕ) (σ V : ℝ) (hV : 0 < V) (hk : 1 < k) :
    let R := classicalTypeIFourierRadius A N k σ V
    (N : ℝ) ^ (-σ) * (Finset.Ioc N (min (2 * N) A)).card *
        ((2 * SchwartzMap.seminorm ℝ k 0
            (𝓕 (classicalTypeILogProfileSchwartz σ)) / ((k : ℝ) - 1)) *
          R ^ (1 - (k : ℝ))) ≤ V / 2 := by
  dsimp only
  let q : ℝ := (k : ℝ) - 1
  let M : ℝ := (N : ℝ) ^ (-σ) *
    (Finset.Ioc N (min (2 * N) A)).card
  let C : ℝ := SchwartzMap.seminorm ℝ k 0
    (𝓕 (classicalTypeILogProfileSchwartz σ))
  let B : ℝ := 1 + 4 * M * C / (q * V)
  let R : ℝ := B ^ (1 / q)
  have hq : 0 < q := by
    dsimp only [q]
    have hkReal : (1 : ℝ) < k := by exact_mod_cast hk
    linarith
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hB : 0 < B := by
    dsimp only [B]
    have : 0 ≤ 4 * M * C / (q * V) := by positivity
    linarith
  have hR : 0 < R := Real.rpow_pos_of_pos hB _
  have hRq : R ^ q = B := by
    dsimp only [R]
    rw [← Real.rpow_mul hB.le]
    have hqne : q ≠ 0 := hq.ne'
    rw [show (1 / q) * q = 1 by field_simp]
    exact Real.rpow_one B
  have hcore : 4 * M * C / (q * V) ≤ B := by
    dsimp only [B]
    linarith
  have hmul : 4 * M * C ≤ B * (q * V) := by
    rw [div_le_iff₀ (mul_pos hq hV)] at hcore
    nlinarith
  have hRadius : classicalTypeIFourierRadius A N k σ V = R := by rfl
  rw [hRadius]
  change M * ((2 * C / q) * R ^ (1 - (k : ℝ))) ≤ V / 2
  have hexponent : 1 - (k : ℝ) = -q := by
    dsimp only [q]
    ring
  rw [hexponent]
  rw [Real.rpow_neg hR.le, hRq]
  have hrearrange : M * (2 * C / q * B⁻¹) = 2 * M * C / (q * B) := by
    field_simp
  rw [hrearrange, div_le_iff₀ (mul_pos hq hB)]
  nlinarith

/-- Abstract subpower engine for the canonical radius.  Once its defining
base has growth `T^α`, choosing the Fourier order so that
`α ≤ δ (k - 1)` places the complete radius below `T^δ`. -/
theorem classicalTypeIFourierRadius_le_rpow_of_base_growth
    (A N k : ℕ) (σ V T α δ : ℝ) (hV : 0 < V) (hk : 1 < k)
    (hT : 1 ≤ T) (horder : α ≤ δ * ((k : ℝ) - 1))
    (hbase :
      1 +
          4 * ((N : ℝ) ^ (-σ) * (Finset.Ioc N (min (2 * N) A)).card) *
            SchwartzMap.seminorm ℝ k 0
              (𝓕 (classicalTypeILogProfileSchwartz σ)) /
            (((k : ℝ) - 1) * V) ≤
        T ^ α) :
    classicalTypeIFourierRadius A N k σ V ≤ T ^ δ := by
  let q : ℝ := (k : ℝ) - 1
  have hq : 0 < q := by
    dsimp only [q]
    have hkReal : (1 : ℝ) < k := by exact_mod_cast hk
    linarith
  let B : ℝ :=
    1 +
      4 * ((N : ℝ) ^ (-σ) * (Finset.Ioc N (min (2 * N) A)).card) *
        SchwartzMap.seminorm ℝ k 0
          (𝓕 (classicalTypeILogProfileSchwartz σ)) /
        (((k : ℝ) - 1) * V)
  have hBnonneg : 0 ≤ B := by
    dsimp only [B]
    have hq' : 0 < (k : ℝ) - 1 := by simpa only [q] using hq
    have hterm : 0 ≤
        4 * ((N : ℝ) ^ (-σ) * (Finset.Ioc N (min (2 * N) A)).card) *
          SchwartzMap.seminorm ℝ k 0
            (𝓕 (classicalTypeILogProfileSchwartz σ)) /
          (((k : ℝ) - 1) * V) := by positivity
    linarith
  have hbase' : B ≤ T ^ α := by simpa only [B] using hbase
  have hexponent : α * (1 / q) ≤ δ := by
    have horder' : α ≤ δ * q := by simpa only [q] using horder
    have hdiv : α / q ≤ δ := (div_le_iff₀ hq).2 (by nlinarith)
    simpa only [div_eq_mul_inv, one_mul] using hdiv
  change B ^ (1 / q) ≤ T ^ δ
  calc
    B ^ (1 / q) ≤ (T ^ α) ^ (1 / q) :=
      Real.rpow_le_rpow hBnonneg hbase' (by positivity)
    _ = T ^ (α * (1 / q)) := by
      rw [← Real.rpow_mul (by linarith : 0 ≤ T)]
    _ ≤ T ^ δ := Real.rpow_le_rpow_of_exponent_le hT hexponent

/-- Source-scale envelope for the canonical-radius base before absorbing the
single dyadic-count factor into an epsilon power. -/
theorem classicalTypeIFourierRadius_source_base_le
    (A N k : ℕ) (σ T D : ℝ) (hT : 0 < T) (hA : 1 < A)
    (hN : 0 < N) (hσ : 0 ≤ σ) (hNA : N ≤ A)
    (hAupper : (A : ℝ) ≤ 6 * T) (hk : 1 < k) :
    1 +
          4 * ((N : ℝ) ^ (-σ) * (Finset.Ioc N (min (2 * N) A)).card) *
            SchwartzMap.seminorm ℝ k 0
              (𝓕 (classicalTypeILogProfileSchwartz σ)) /
            (((k : ℝ) - 1) *
              (((3 / 4 : ℝ) * (T ^ (-D) / 2)) / Nat.clog 2 A)) ≤
      1 +
        (64 * SchwartzMap.seminorm ℝ k 0
            (𝓕 (classicalTypeILogProfileSchwartz σ)) / ((k : ℝ) - 1)) *
          Nat.clog 2 A * T ^ (D + 1) := by
  let M : ℝ := (N : ℝ) ^ (-σ) *
    (Finset.Ioc N (min (2 * N) A)).card
  let C : ℝ := SchwartzMap.seminorm ℝ k 0
    (𝓕 (classicalTypeILogProfileSchwartz σ))
  let q : ℝ := (k : ℝ) - 1
  let V : ℝ := ((3 / 4 : ℝ) * (T ^ (-D) / 2)) / Nat.clog 2 A
  have hq : 0 < q := by
    dsimp only [q]
    have hkReal : (1 : ℝ) < k := by exact_mod_cast hk
    linarith
  have hV : 0 < V := by
    dsimp only [V]
    have hClog : 0 < Nat.clog 2 A := Nat.clog_pos Nat.one_lt_two hA
    positivity
  have hM : M ≤ 6 * T := by
    calc
      M ≤ N := by
        dsimp only [M]
        exact classicalTypeI_scale_activeCard_le A N σ hN hσ
      _ ≤ A := by exact_mod_cast hNA
      _ ≤ 6 * T := hAupper
  have hInv : V⁻¹ = (8 / 3 : ℝ) * Nat.clog 2 A * T ^ D := by
    dsimp only [V]
    exact classicalTypeI_sourceThreshold_inv T D A hT hA
  change 1 + 4 * M * C / (q * V) ≤
    1 + (64 * C / q) * Nat.clog 2 A * T ^ (D + 1)
  have hrewrite : 4 * M * C / (q * V) = (4 * M * C / q) * V⁻¹ := by
    field_simp [hq.ne', hV.ne']
  rw [hrewrite, hInv]
  rw [add_le_add_iff_left]
  calc
    (4 * M * C / q) * ((8 / 3 : ℝ) * Nat.clog 2 A * T ^ D) ≤
        (4 * (6 * T) * C / q) *
          ((8 / 3 : ℝ) * Nat.clog 2 A * T ^ D) := by
      gcongr
    _ = (64 * C / q) * Nat.clog 2 A * T ^ (D + 1) := by
      rw [show T ^ (D + 1) = T ^ D * T by
        rw [Real.rpow_add hT, Real.rpow_one]]
      ring

/-- The preceding base envelope specialized to the actual sharp cutoff and
source Type-I threshold.  Positivity of the large value forces the dyadic
start below the cutoff, so no scale-order premise remains. -/
theorem classicalTypeIFourierRadius_sharpCutoff_source_base_le
    (N k : ℕ) (σ T D t : ℝ) (hT : 8 ≤ T) (hN : 0 < N)
    (hσ : 0 ≤ σ) (hk : 1 < k)
    (hlarge :
      ((3 / 4 : ℝ) * (T ^ (-D) / 2)) /
          Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ ≤
        ‖dirichletPoly N
          (classicalZetaLongLineCoeff ⌊sharpZetaCutoff T⌋₊ σ) t‖) :
    1 +
          4 * ((N : ℝ) ^ (-σ) *
              (Finset.Ioc N (min (2 * N) ⌊sharpZetaCutoff T⌋₊)).card) *
            SchwartzMap.seminorm ℝ k 0
              (𝓕 (classicalTypeILogProfileSchwartz σ)) /
            (((k : ℝ) - 1) *
              (((3 / 4 : ℝ) * (T ^ (-D) / 2)) /
                Nat.clog 2 ⌊sharpZetaCutoff T⌋₊)) ≤
      1 +
        (64 * SchwartzMap.seminorm ℝ k 0
            (𝓕 (classicalTypeILogProfileSchwartz σ)) / ((k : ℝ) - 1)) *
          Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ * T ^ (D + 1) := by
  let A := ⌊sharpZetaCutoff T⌋₊
  have hTpos : 0 < T := by linarith
  have hCutNonneg : 0 ≤ sharpZetaCutoff T := by
    linarith [four_mul_lt_sharpZetaCutoff T]
  have hA : 1 < A := by
    dsimp only [A]
    apply lt_of_lt_of_le (by omega : 1 < (2 : ℕ))
    apply Nat.le_floor
    exact (show (2 : ℝ) ≤ 4 * T by nlinarith).trans
      (four_mul_lt_sharpZetaCutoff T).le
  have hAupper : (A : ℝ) ≤ 6 * T := by
    dsimp only [A]
    exact (Nat.floor_le hCutNonneg).trans
      (sharpZetaCutoff_le_six_mul (by linarith))
  have hV : 0 <
      ((3 / 4 : ℝ) * (T ^ (-D) / 2)) / Nat.clog 2 A := by
    have hClog : 0 < Nat.clog 2 A := Nat.clog_pos Nat.one_lt_two hA
    positivity
  have hNA : N ≤ A := by
    exact (typeI_start_lt_cutoff_of_positive_large_value
      A N σ t
        (((3 / 4 : ℝ) * (T ^ (-D) / 2)) / Nat.clog 2 A)
      hV (by simpa only [A] using hlarge)).le
  simpa only [A] using
    classicalTypeIFourierRadius_source_base_le
      A N k σ T D hTpos hA hN hσ hNA hAupper hk

/-- A fixed nonnegative constant times one logarithm is eventually absorbed by
any prescribed positive power.  The leading `1` is absorbed simultaneously. -/
theorem eventually_one_add_const_mul_log_le_rpow
    (C η : ℝ) (hη : 0 < η) :
    ∀ᶠ T : ℝ in Filter.atTop, 1 + C * Real.log T ≤ T ^ η := by
  have hhalf : 0 < η / 2 := by linarith
  have hLog := eventually_log_nat_power_le_rpow 1 (η / 2) hhalf
  have hConstGrowth : Filter.Tendsto (fun T : ℝ => T ^ (η / 2))
      Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop hhalf
  have hConst : ∀ᶠ T : ℝ in Filter.atTop, 1 + C ≤ T ^ (η / 2) :=
    hConstGrowth.eventually (Filter.eventually_ge_atTop (1 + C))
  filter_upwards [hLog, hConst, Filter.eventually_ge_atTop (Real.exp 1)] with
      T hLog hConst hT
  have hTpos : 0 < T := (Real.exp_pos 1).trans_le hT
  have hLogOne : 1 ≤ Real.log T := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hT
  have hLogNonneg : 0 ≤ Real.log T := zero_le_one.trans hLogOne
  have hLog' : Real.log T ≤ T ^ (η / 2) := by simpa using hLog
  have hPowNonneg : 0 ≤ T ^ (η / 2) := Real.rpow_nonneg hTpos.le _
  calc
    1 + C * Real.log T ≤ (1 + C) * Real.log T := by
      nlinarith
    _ ≤ T ^ (η / 2) * T ^ (η / 2) :=
      mul_le_mul hConst hLog' hLogNonneg hPowNonneg
    _ = T ^ η := by
      rw [← Real.rpow_add hTpos]
      congr 1
      ring

/-- The fixed Fourier seminorm and the single sharp-cutoff dyadic-count loss
are eventually absorbed by any positive power of the height. -/
theorem eventually_classicalTypeIFourier_clog_loss_le_rpow
    (k : ℕ) (σ η : ℝ) (hk : 1 < k) (hη : 0 < η) :
    ∀ᶠ T : ℝ in Filter.atTop,
      1 +
          (64 * SchwartzMap.seminorm ℝ k 0
              (𝓕 (classicalTypeILogProfileSchwartz σ)) / ((k : ℝ) - 1)) *
            Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ ≤
        T ^ η := by
  let K : ℝ :=
    64 * SchwartzMap.seminorm ℝ k 0
      (𝓕 (classicalTypeILogProfileSchwartz σ)) / ((k : ℝ) - 1)
  let c : ℝ := 1 + 2 / Real.log 2
  have hq : 0 < (k : ℝ) - 1 := by
    have hkReal : (1 : ℝ) < k := by exact_mod_cast hk
    linarith
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hc : 0 ≤ c := by
    dsimp only [c]
    have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hAbsorb := eventually_one_add_const_mul_log_le_rpow
    (K * c) η hη
  filter_upwards [hAbsorb, Filter.eventually_ge_atTop (8 : ℝ)] with
      T hAbsorb hT
  have hLogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLogSixT : Real.log 6 ≤ Real.log T :=
    Real.log_le_log (by norm_num) (by linarith)
  have hClogRaw := sharp_cutoff_clog_le_log_majorant T hT
  have hClog : (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ : ℝ) ≤
      c * Real.log T := by
    calc
      (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ : ℝ) ≤
          1 + (Real.log 6 + Real.log T) / Real.log 2 := hClogRaw
      _ ≤ c * Real.log T := by
        have hLogOne : 1 ≤ Real.log T := by
          have hExpT : Real.exp 1 ≤ T :=
            (Real.exp_one_lt_three.le.trans (by norm_num : (3 : ℝ) ≤ 8)).trans hT
          simpa only [Real.log_exp] using
            Real.log_le_log (Real.exp_pos 1) hExpT
        dsimp only [c]
        have hNumerator : Real.log 6 + Real.log T ≤ 2 * Real.log T := by
          linarith
        have hFrac : (Real.log 6 + Real.log T) / Real.log 2 ≤
            (2 * Real.log T) / Real.log 2 :=
          div_le_div_of_nonneg_right hNumerator hLogTwo.le
        calc
          1 + (Real.log 6 + Real.log T) / Real.log 2 ≤
              1 + (2 * Real.log T) / Real.log 2 := by linarith
          _ ≤ Real.log T + (2 * Real.log T) / Real.log 2 := by linarith
          _ = (1 + 2 / Real.log 2) * Real.log T := by ring
  change 1 + K * Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ ≤ T ^ η
  calc
    1 + K * Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ ≤
        1 + K * (c * Real.log T) := by gcongr
    _ = 1 + (K * c) * Real.log T := by ring
    _ ≤ T ^ η := hAbsorb

/-- Uniform source-specific power bound for the complete canonical-radius
base.  It holds simultaneously for every dyadic scale and ordinate on which
the genuine sharp Type-I lower bound holds. -/
theorem eventually_classicalTypeIFourierRadius_sharpCutoff_base_le_rpow
    (k : ℕ) (σ D η : ℝ) (hk : 1 < k) (hσ : 0 ≤ σ)
    (hD : 0 ≤ D + 1) (hη : 0 < η) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (N : ℕ) (t : ℝ), 0 < N →
      ((3 / 4 : ℝ) * (T ^ (-D) / 2)) /
          Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ ≤
        ‖dirichletPoly N
          (classicalZetaLongLineCoeff ⌊sharpZetaCutoff T⌋₊ σ) t‖ →
      let A := ⌊sharpZetaCutoff T⌋₊
      let V := ((3 / 4 : ℝ) * (T ^ (-D) / 2)) / Nat.clog 2 A
      1 +
            4 * ((N : ℝ) ^ (-σ) *
                (Finset.Ioc N (min (2 * N) A)).card) *
              SchwartzMap.seminorm ℝ k 0
                (𝓕 (classicalTypeILogProfileSchwartz σ)) /
              (((k : ℝ) - 1) * V) ≤
        T ^ (D + 1 + η) := by
  have hAbsorb := eventually_classicalTypeIFourier_clog_loss_le_rpow
    k σ η hk hη
  filter_upwards [hAbsorb, Filter.eventually_ge_atTop (8 : ℝ)] with
      T hAbsorb hT
  intro N t hN hlarge
  dsimp only
  let K : ℝ :=
    64 * SchwartzMap.seminorm ℝ k 0
      (𝓕 (classicalTypeILogProfileSchwartz σ)) / ((k : ℝ) - 1)
  let L : ℝ := Nat.clog 2 ⌊sharpZetaCutoff T⌋₊
  let p : ℝ := D + 1
  have hTpos : 0 < T := by linarith
  have hTone : 1 ≤ T := by linarith
  have hp : 0 ≤ p := by simpa only [p] using hD
  have hTpOne : 1 ≤ T ^ p := Real.one_le_rpow hTone hp
  have hTpNonneg : 0 ≤ T ^ p := Real.rpow_nonneg hTpos.le _
  have hKLNonneg : 0 ≤ K * L := by
    dsimp only [K, L]
    have hq : 0 < (k : ℝ) - 1 := by
      have hkReal : (1 : ℝ) < k := by exact_mod_cast hk
      linarith
    positivity
  have hEnvelope := classicalTypeIFourierRadius_sharpCutoff_source_base_le
    N k σ T D t hT hN hσ hk hlarge
  have hPower : 1 + K * L * T ^ p ≤ T ^ (p + η) := by
    calc
      1 + K * L * T ^ p ≤ T ^ p + K * L * T ^ p := by
        gcongr
      _ = (1 + K * L) * T ^ p := by ring
      _ ≤ T ^ η * T ^ p := by
        gcongr
      _ = T ^ (η + p) := (Real.rpow_add hTpos η p).symm
      _ = T ^ (p + η) := by rw [add_comm η p]
  apply hEnvelope.trans
  simpa only [K, L, p, add_assoc] using hPower

/-- Actual subpower displacement radius for the sharp source Type-I block.
The estimate is uniform in the dyadic scale and ordinate; the Fourier order
records exactly how much of the requested displacement exponent is spent on
the source threshold. -/
theorem eventually_classicalTypeIFourierRadius_sharpCutoff_le_rpow
    (k : ℕ) (σ D η δ : ℝ) (hk : 1 < k) (hσ : 0 ≤ σ)
    (hD : 0 ≤ D + 1) (hη : 0 < η)
    (horder : D + 1 + η ≤ δ * ((k : ℝ) - 1)) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (N : ℕ) (t : ℝ), 0 < N →
      ((3 / 4 : ℝ) * (T ^ (-D) / 2)) /
          Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ ≤
        ‖dirichletPoly N
          (classicalZetaLongLineCoeff ⌊sharpZetaCutoff T⌋₊ σ) t‖ →
      let A := ⌊sharpZetaCutoff T⌋₊
      let V := ((3 / 4 : ℝ) * (T ^ (-D) / 2)) / Nat.clog 2 A
      classicalTypeIFourierRadius A N k σ V ≤ T ^ δ := by
  have hBase := eventually_classicalTypeIFourierRadius_sharpCutoff_base_le_rpow
    k σ D η hk hσ hD hη
  filter_upwards [hBase, Filter.eventually_ge_atTop (8 : ℝ)] with T hBase hT
  intro N t hN hlarge
  dsimp only
  let A := ⌊sharpZetaCutoff T⌋₊
  let V := ((3 / 4 : ℝ) * (T ^ (-D) / 2)) / Nat.clog 2 A
  have hTpos : 0 < T := by linarith
  have hA : 1 < A := by
    dsimp only [A]
    apply lt_of_lt_of_le (by omega : 1 < (2 : ℕ))
    apply Nat.le_floor
    exact (show (2 : ℝ) ≤ 4 * T by nlinarith).trans
      (four_mul_lt_sharpZetaCutoff T).le
  have hV : 0 < V := by
    dsimp only [V]
    have hClog : 0 < Nat.clog 2 A := Nat.clog_pos Nat.one_lt_two hA
    positivity
  apply classicalTypeIFourierRadius_le_rpow_of_base_growth
    A N k σ V T (D + 1 + η) δ hV hk (by linarith) horder
  simpa only [A, V] using hBase N t hN hlarge

/-- A Fourier decay order can always be chosen to pay the source threshold
exponent while retaining any prescribed positive displacement exponent. -/
theorem exists_classicalTypeIFourier_order
    (D δ : ℝ) (hδ : 0 < δ) :
    ∃ k : ℕ, 1 < k ∧
      D + 1 + δ / 2 ≤ δ * ((k : ℝ) - 1) := by
  obtain ⟨k, hk⟩ := exists_nat_gt
    (max 2 ((D + 1 + δ / 2) / δ + 1))
  have hkTwoReal : (2 : ℝ) < k :=
    (le_max_left (2 : ℝ) ((D + 1 + δ / 2) / δ + 1)).trans_lt hk
  have hkTwoNat : 2 < k := by exact_mod_cast hkTwoReal
  have hkTwo : 1 < k := by omega
  have hkRatio : (D + 1 + δ / 2) / δ + 1 < (k : ℝ) :=
    (le_max_right (2 : ℝ) ((D + 1 + δ / 2) / δ + 1)).trans_lt hk
  have hscaled : D + 1 + δ / 2 < δ * ((k : ℝ) - 1) := by
    have hratio : (D + 1 + δ / 2) / δ < (k : ℝ) - 1 := by
      linarith
    rw [div_lt_iff₀ hδ] at hratio
    nlinarith
  exact ⟨k, hkTwo, hscaled.le⟩

/-- Fully quantified subpower radius for the genuine sharp Type-I source
block: for every positive displacement exponent, one fixed Fourier order works
uniformly for all sufficiently large heights, all scales, and all ordinates. -/
theorem exists_order_eventually_classicalTypeIFourierRadius_sharpCutoff_le_rpow
    (σ D δ : ℝ) (hσ : 0 ≤ σ) (hD : 0 ≤ D + 1) (hδ : 0 < δ) :
    ∃ k : ℕ, 1 < k ∧
      ∀ᶠ T : ℝ in Filter.atTop, ∀ (N : ℕ) (t : ℝ), 0 < N →
        ((3 / 4 : ℝ) * (T ^ (-D) / 2)) /
            Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ ≤
          ‖dirichletPoly N
            (classicalZetaLongLineCoeff ⌊sharpZetaCutoff T⌋₊ σ) t‖ →
        let A := ⌊sharpZetaCutoff T⌋₊
        let V := ((3 / 4 : ℝ) * (T ^ (-D) / 2)) / Nat.clog 2 A
        classicalTypeIFourierRadius A N k σ V ≤ T ^ δ := by
  obtain ⟨k, hk, horder⟩ := exists_classicalTypeIFourier_order D δ hδ
  refine ⟨k, hk, ?_⟩
  exact eventually_classicalTypeIFourierRadius_sharpCutoff_le_rpow
    k σ D (δ / 2) δ hk hσ hD (by linarith) horder

/-- The canonical radius removes the numerical-tail premise from sharp Type-I
finite-window extraction. -/
theorem exists_explicitly_bounded_coefficientOne_shift_of_classicalTypeI
    (A N k : ℕ) (σ V t : ℝ) (hN : 0 < N) (hV : 0 < V)
    (hk : 1 < k)
    (hlarge : V ≤ ‖dirichletPoly N (classicalZetaLongLineCoeff A σ) t‖) :
    let R := classicalTypeIFourierRadius A N k σ V
    ∃ ξ ∈ Set.Icc (-R) R,
      V / (4 * (N : ℝ) ^ (-σ) * classicalTypeIFourierL1 σ) ≤
        ‖∑ n ∈ Finset.Ioc N (min (2 * N) A),
          (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)‖ := by
  dsimp only
  exact exists_bounded_coefficientOne_shift_of_classicalTypeI
    A N k σ V t (classicalTypeIFourierRadius A N k σ V)
      hN hV hk (classicalTypeIFourierRadius_pos A N k σ V hV hk)
      hlarge (classicalTypeIFourierRadius_tail_numeric A N k σ V hV hk)

/-- The canonical radius simultaneously extracts a bounded coefficient-one
ordinate for every member of a finite sharp Type-I family, with the complete
energy-transfer loss displayed. -/
theorem exists_classicalTypeI_explicitBoundedOrdinate_family
    {ι : Type*} [Fintype ι]
    (A N k : ℕ) (σ V : ℝ) (W : ι → ℝ)
    (hN : 0 < N) (hV : 0 < V) (hk : 1 < k)
    (hlarge : ∀ x,
      V ≤ ‖dirichletPoly N (classicalZetaLongLineCoeff A σ) (W x)‖) :
    let R := classicalTypeIFourierRadius A N k σ V
    ∃ W' : ι → ℝ,
      (∀ x, |W' x - W x| ≤ 2 * Real.pi * R) ∧
      (∀ x,
        V / (4 * (N : ℝ) ^ (-σ) * classicalTypeIFourierL1 σ) ≤
          ‖∑ n ∈ Finset.Ioc N (min (2 * N) A),
            dirichletPhase n (W' x)‖) ∧
      approximateAdditiveEnergyOf 1 W ≤
        (4 * Nat.ceil (1 + 4 * (2 * Real.pi * R)) + 6) *
          approximateAdditiveEnergyOf 1 W' := by
  dsimp only
  exact exists_classicalTypeI_boundedOrdinate_family
    A N k σ V (classicalTypeIFourierRadius A N k σ V) W
      hN hV hk (classicalTypeIFourierRadius_pos A N k σ V hV hk)
      hlarge (classicalTypeIFourierRadius_tail_numeric A N k σ V hV hk)

/-- The canonical sharp Type-I radius followed by bounded-multiplicity
coloring produces four one-separated coefficient-one families.  Every input
index is retained through the displayed energy inequalities. -/
theorem exists_separated_classicalTypeI_explicitFourier_energy_classes
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (A N k : ℕ) (σ V : ℝ) (W : ι → ℝ)
    (hN : 0 < N) (hV : 0 < V) (hk : 1 < k)
    (hlarge : ∀ x,
      V ≤ ‖dirichletPoly N (classicalZetaLongLineCoeff A σ) (W x)‖)
    (hsep : ∀ x y : ι, x ≠ y → 1 ≤ |W x - W y|) :
    let R := classicalTypeIFourierRadius A N k σ V
    let d := 2 * Real.pi * R
    let L := Nat.ceil (2 * d + 2)
    ∃ (W' : ι → ℝ) (hpert : ∀ x, |W' x - W x| ≤ d),
      let hlocal : ∀ z : ℤ, (unitBinFinset W' z).card ≤ L := fun z =>
        unitBinFinset_perturbation_card_le_natCeil
          W W' d (by
            dsimp only [d, R]
            exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
              (classicalTypeIFourierRadius_pos A N k σ V hV hk).le) hsep hpert z
      ∃ label : Fin 4 → ZMod 2 × Fin (L + 1),
        let color := boundedMultiplicityColor W' L hlocal
        let Wᵢ := fun i : Fin 4 =>
          fun x : EnergyColorFiber color (label i) => W' x.1
        approximateAdditiveEnergyOf 1 W ≤
            (4 * Nat.ceil (1 + 4 * d) + 6) *
              approximateAdditiveEnergyOf 1 W' ∧
          4 * (approximateAdditiveEnergyOf 1 W' : ℝ) ≤
            9 * (Fintype.card (ZMod 2 × Fin (L + 1)) : ℝ) ^ 4 *
              ((approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
                (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
                (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
                (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ)) ∧
          (∀ (i : Fin 4) (x : EnergyColorFiber color (label i)),
            V / (4 * (N : ℝ) ^ (-σ) * classicalTypeIFourierL1 σ) ≤
              ‖∑ n ∈ Finset.Ioc N (min (2 * N) A),
                dirichletPhase n (Wᵢ i x)‖) ∧
          ∀ (i : Fin 4) (x y : EnergyColorFiber color (label i)),
            x ≠ y → 1 ≤ |Wᵢ i x - Wᵢ i y| := by
  classical
  dsimp only
  let R := classicalTypeIFourierRadius A N k σ V
  let d := 2 * Real.pi * R
  have hR : 0 < R := classicalTypeIFourierRadius_pos A N k σ V hV hk
  obtain ⟨W', hpert, hlarge', _htransfer⟩ :=
    exists_classicalTypeI_explicitBoundedOrdinate_family
      A N k σ V W hN hV hk hlarge
  let L := Nat.ceil (2 * d + 2)
  let hlocal : ∀ z : ℤ, (unitBinFinset W' z).card ≤ L := fun z =>
    unitBinFinset_perturbation_card_le_natCeil
      W W' d (by dsimp only [d]; positivity) hsep hpert z
  obtain ⟨label, htransfer, henergy, hseparated⟩ :=
    exists_separated_perturbed_energy_classes W W' d
      (by dsimp only [d]; positivity) hsep hpert
  refine ⟨W', hpert, label, htransfer, henergy, ?_, hseparated⟩
  intro i x
  exact hlarge' x.1

/-- Height-aware packaging of the four sharp coefficient-one classes.  Each
class becomes an exact paper `LargeValuePattern` on the common expanded
interval, and its finset energy is the indexed class energy appearing in the
transfer inequality. -/
theorem exists_classicalTypeI_explicitFourier_patterns
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (A N k : ℕ) (σ V a b : ℝ) (W : ι → ℝ)
    (hN : 1 < N) (hV : 0 < V) (hk : 1 < k) (hab : a < b)
    (hW : ∀ x, a ≤ W x ∧ W x ≤ b)
    (hlarge : ∀ x,
      V ≤ ‖dirichletPoly N (classicalZetaLongLineCoeff A σ) (W x)‖)
    (hsep : ∀ x y : ι, x ≠ y → 1 ≤ |W x - W y|) :
    let R := classicalTypeIFourierRadius A N k σ V
    let d := 2 * Real.pi * R
    let L := Nat.ceil (2 * d + 2)
    let Q := V / (4 * (N : ℝ) ^ (-σ) * classicalTypeIFourierL1 σ)
    ∃ (W' : ι → ℝ) (hpert : ∀ x, |W' x - W x| ≤ d),
      let hlocal : ∀ z : ℤ, (unitBinFinset W' z).card ≤ L := fun z =>
        unitBinFinset_perturbation_card_le_natCeil
          W W' d (by
            dsimp only [d, R]
            exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
              (classicalTypeIFourierRadius_pos A N k σ V hV hk).le) hsep hpert z
      ∃ label : Fin 4 → ZMod 2 × Fin (L + 1),
        let color := boundedMultiplicityColor W' L hlocal
        let Wᵢ := fun i : Fin 4 =>
          fun x : EnergyColorFiber color (label i) => W' x.1
        approximateAdditiveEnergyOf 1 W ≤
            (4 * Nat.ceil (1 + 4 * d) + 6) *
              approximateAdditiveEnergyOf 1 W' ∧
          4 * (approximateAdditiveEnergyOf 1 W' : ℝ) ≤
            9 * (Fintype.card (ZMod 2 × Fin (L + 1)) : ℝ) ^ 4 *
              ((approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
                (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
                (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
                (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ)) ∧
          (∀ (i : Fin 4) (x : EnergyColorFiber color (label i)),
            Q ≤ ‖∑ n ∈ Finset.Ioc N (min (2 * N) A),
              dirichletPhase n (Wᵢ i x)‖) ∧
          (∀ (i : Fin 4) (x y : EnergyColorFiber color (label i)),
            x ≠ y → 1 ≤ |Wᵢ i x - Wᵢ i y|) ∧
          ∃ P : Fin 4 → LargeValuePattern,
            ∀ i : Fin 4,
              (P i).N = N ∧
              (P i).V = Q ∧
              (P i).intervalLeft = a - d ∧
              (P i).intervalRight = b + d ∧
              (P i).ordinates = Finset.univ.image (Wᵢ i) ∧
              finsetAdditiveEnergy (P i).ordinates =
                approximateAdditiveEnergyOf 1 (Wᵢ i) := by
  classical
  dsimp only
  let R := classicalTypeIFourierRadius A N k σ V
  let d := 2 * Real.pi * R
  let L := Nat.ceil (2 * d + 2)
  let Q := V / (4 * (N : ℝ) ^ (-σ) * classicalTypeIFourierL1 σ)
  have hNpos : 0 < N := by omega
  have hR : 0 < R := classicalTypeIFourierRadius_pos A N k σ V hV hk
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  obtain ⟨W', hpert, label, htransfer, henergy, hlarge', hseparated⟩ :=
    exists_separated_classicalTypeI_explicitFourier_energy_classes
      A N k σ V W hNpos hV hk hlarge hsep
  let hlocal : ∀ z : ℤ, (unitBinFinset W' z).card ≤ L := fun z =>
    unitBinFinset_perturbation_card_le_natCeil W W' d hd hsep hpert z
  let color := boundedMultiplicityColor W' L hlocal
  let Wᵢ := fun i : Fin 4 =>
    fun x : EnergyColorFiber color (label i) => W' x.1
  have hQ : 0 < Q := by
    dsimp only [Q]
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
    have hpow : 0 < (N : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hNreal _
    exact div_pos hV
      (mul_pos (mul_pos (by norm_num) hpow) (classicalTypeIFourierL1_pos σ))
  have hab' : a - d < b + d := by linarith
  have hWᵢ : ∀ (i : Fin 4) (x : EnergyColorFiber color (label i)),
      a - d ≤ Wᵢ i x ∧ Wᵢ i x ≤ b + d := by
    intro i x
    exact perturbedOrdinate_mem_expandedInterval W W' a b d hW hpert x.1
  let P : Fin 4 → LargeValuePattern := fun i =>
    indexedClassicalTypeICoefficientOnePattern
      A N Q (a - d) (b + d) (Wᵢ i) hN hQ hab'
        (hWᵢ i) (hseparated i) (hlarge' i)
  refine ⟨W', hpert, label, htransfer, henergy, hlarge', hseparated, P, ?_⟩
  intro i
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact indexedClassicalTypeICoefficientOnePattern_energy_eq
    A N Q (a - d) (b + d) (Wᵢ i) hN hQ hab'
      (hWᵢ i) (hseparated i) (hlarge' i)

/-- The quantitative finite-scale `zeroe-from-large` composition for a
classical Type-I family.  A single witness supplied by `LV*` applies to all
four coefficient-one patterns because they have the same scale, expanded
height interval, and normalized threshold.  The conclusion keeps every
explicit perturbation and coloring loss. -/
theorem IsLargeValueEnergyBound.classicalTypeI_explicitFourier_energy_transfer
    {sigmaLV tau rhoStar : ℝ}
    (hLV : IsLargeValueEnergyBound sigmaLV tau rhoStar) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 1 ≤ C ∧
        ∃ delta : ℝ, 0 < delta ∧
          ∀ {ι : Type*} [Fintype ι] [LinearOrder ι]
            (A N k : ℕ) (sigma V a b : ℝ) (W : ι → ℝ),
            let R := classicalTypeIFourierRadius A N k sigma V
            let d := 2 * Real.pi * R
            let L := Nat.ceil (2 * d + 2)
            let Q := V / (4 * (N : ℝ) ^ (-sigma) * classicalTypeIFourierL1 sigma)
            1 < N → 0 < V → 1 < k → a < b →
            (∀ x, a ≤ W x ∧ W x ≤ b) →
            (∀ x, V ≤
              ‖dirichletPoly N (classicalZetaLongLineCoeff A sigma) (W x)‖) →
            (∀ x y : ι, x ≠ y → 1 ≤ |W x - W y|) →
            C ≤ (N : ℝ) →
            (N : ℝ) ^ (tau - delta) ≤ (b + d) - (a - d) →
            (b + d) - (a - d) ≤ (N : ℝ) ^ (tau + delta) →
            (N : ℝ) ^ (sigmaLV - delta) ≤ Q →
            Q ≤ (N : ℝ) ^ (sigmaLV + delta) →
            (approximateAdditiveEnergyOf 1 W : ℝ) ≤
              (4 * Nat.ceil (1 + 4 * d) + 6) *
                (9 * (Fintype.card (ZMod 2 × Fin (L + 1)) : ℝ) ^ 4) *
                  (C * (N : ℝ) ^ (rhoStar + epsilon)) := by
  intro epsilon hepsilon
  obtain ⟨C, hC, delta, hdelta, hLVbound⟩ := hLV epsilon hepsilon
  refine ⟨C, hC, delta, hdelta, ?_⟩
  intro ι _ _ A N k sigma V a b W
  dsimp only
  let R := classicalTypeIFourierRadius A N k sigma V
  let d := 2 * Real.pi * R
  let L := Nat.ceil (2 * d + 2)
  let Q := V / (4 * (N : ℝ) ^ (-sigma) * classicalTypeIFourierL1 sigma)
  intro hN hV hk hab hW hlarge hsep hCN hTLower hTUpper hQLower hQUpper
  obtain ⟨W', hpert, label, htransfer, henergy, hlarge', hseparated,
      P, hP⟩ :=
    exists_classicalTypeI_explicitFourier_patterns
      A N k sigma V a b W hN hV hk hab hW hlarge hsep
  let hlocal : ∀ z : ℤ, (unitBinFinset W' z).card ≤ L := fun z =>
    unitBinFinset_perturbation_card_le_natCeil W W' d
      (by
        dsimp only [d, R]
        exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
          (classicalTypeIFourierRadius_pos A N k sigma V hV hk).le)
      hsep hpert z
  let color := boundedMultiplicityColor W' L hlocal
  let Wᵢ := fun i : Fin 4 =>
    fun x : EnergyColorFiber color (label i) => W' x.1
  have hPattern (i : Fin 4) :
      (finsetAdditiveEnergy (P i).ordinates : ℝ) ≤
        C * (N : ℝ) ^ (rhoStar + epsilon) := by
    obtain ⟨hPN, hPV, hPLeft, hPRight, _hPOrd, _hPEnergy⟩ := hP i
    have hPT : (P i).T = (b + d) - (a - d) := by
      rw [← (P i).interval_length, hPLeft, hPRight]
    rw [← hPN]
    apply hLVbound (P i)
    · simpa [hPN] using hCN
    · simpa [hPN, hPT] using hTLower
    · simpa [hPN, hPT] using hTUpper
    · simpa [hPN, hPV] using hQLower
    · simpa [hPN, hPV] using hQUpper
  have hClass (i : Fin 4) :
      (approximateAdditiveEnergyOf 1 (Wᵢ i) : ℝ) ≤
        C * (N : ℝ) ^ (rhoStar + epsilon) := by
    rw [← (hP i).2.2.2.2.2]
    exact hPattern i
  have hSum :
      (approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
          (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
          (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
          (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ) ≤
        4 * (C * (N : ℝ) ^ (rhoStar + epsilon)) := by
    linarith [hClass 0, hClass 1, hClass 2, hClass 3]
  have hTransferReal :
      (approximateAdditiveEnergyOf 1 W : ℝ) ≤
        (4 * Nat.ceil (1 + 4 * d) + 6) *
          (approximateAdditiveEnergyOf 1 W' : ℝ) := by
    exact_mod_cast htransfer
  have hFactorNonneg :
      0 ≤ (4 * Nat.ceil (1 + 4 * d) + 6 : ℝ) := by positivity
  calc
    (approximateAdditiveEnergyOf 1 W : ℝ) ≤
        (4 * Nat.ceil (1 + 4 * d) + 6) *
          (approximateAdditiveEnergyOf 1 W' : ℝ) := hTransferReal
    _ ≤ (4 * Nat.ceil (1 + 4 * d) + 6) *
          ((9 * (Fintype.card (ZMod 2 × Fin (L + 1)) : ℝ) ^ 4) *
            (C * (N : ℝ) ^ (rhoStar + epsilon))) := by
      have hFourBound :
          4 * ((4 * Nat.ceil (1 + 4 * d) + 6) *
                (approximateAdditiveEnergyOf 1 W' : ℝ)) ≤
            4 * ((4 * Nat.ceil (1 + 4 * d) + 6) *
              ((9 * (Fintype.card (ZMod 2 × Fin (L + 1)) : ℝ) ^ 4) *
                (C * (N : ℝ) ^ (rhoStar + epsilon)))) := by
        calc
          4 * ((4 * Nat.ceil (1 + 4 * d) + 6) *
              (approximateAdditiveEnergyOf 1 W' : ℝ)) =
            (4 * Nat.ceil (1 + 4 * d) + 6) *
              (4 * (approximateAdditiveEnergyOf 1 W' : ℝ)) := by ring
          _ ≤ (4 * Nat.ceil (1 + 4 * d) + 6) *
              ((9 * (Fintype.card (ZMod 2 × Fin (L + 1)) : ℝ) ^ 4) *
                ((approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
                  (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
                  (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
                  (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ))) :=
          mul_le_mul_of_nonneg_left henergy hFactorNonneg
          _ ≤ (4 * Nat.ceil (1 + 4 * d) + 6) *
              ((9 * (Fintype.card (ZMod 2 × Fin (L + 1)) : ℝ) ^ 4) *
                (4 * (C * (N : ℝ) ^ (rhoStar + epsilon)))) := by
            gcongr
          _ = 4 * ((4 * Nat.ceil (1 + 4 * d) + 6) *
              ((9 * (Fintype.card (ZMod 2 × Fin (L + 1)) : ℝ) ^ 4) *
                (C * (N : ℝ) ^ (rhoStar + epsilon)))) := by ring
      linarith
    _ = (4 * Nat.ceil (1 + 4 * d) + 6) *
          (9 * (Fintype.card (ZMod 2 × Fin (L + 1)) : ℝ) ^ 4) *
            (C * (N : ℝ) ^ (rhoStar + epsilon)) := by ring

/-- The complementary Fourier integral for a source smooth block is bounded
uniformly in its ordinate by the active interval cardinality times an
explicit Schwartz seminorm tail. -/
theorem norm_typeILogWeight_fourier_tail_integral_le
    (Y A r : ℕ) (σ t R : ℝ) (hY : 0 < Y) (hR : 0 < R) :
    ‖∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ,
        𝓕 (typeILogWeightSchwartz Y A r σ hY) ξ *
          ∑ n ∈ Finset.Ioc Y A,
            (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)‖ ≤
      (Finset.Ioc Y A).card *
        (2 * SchwartzMap.seminorm ℝ 2 0
          (𝓕 (typeILogWeightSchwartz Y A r σ hY)) / R) := by
  let f : SchwartzMap ℝ ℂ := typeILogWeightSchwartz Y A r σ hY
  let S : Finset ℕ := Finset.Ioc Y A
  let P : ℝ → ℂ := fun ξ =>
    ∑ n ∈ S, (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)
  let g : ℝ → ℂ := fun ξ => 𝓕 f ξ * P ξ
  have hPcontinuous : Continuous P := by
    dsimp only [P, S]
    apply continuous_finsetSum
    intro n hn
    apply Continuous.const_cpow
    · fun_prop
    · exact Or.inl (by
        exact_mod_cast (Nat.ne_of_gt
          (hY.trans (Finset.mem_Ioc.mp hn).1)))
  have hPbound : ∀ ξ : ℝ, ‖P ξ‖ ≤ S.card := by
    intro ξ
    calc
      ‖P ξ‖ ≤ ∑ n ∈ S,
          ‖(n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)‖ :=
        norm_sum_le _ _
      _ = ∑ _n ∈ S, 1 := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [Complex.norm_natCast_cpow_of_pos
          (hY.trans (Finset.mem_Ioc.mp hn).1)]
        simp
      _ = S.card := by simp
  have hgInt : MeasureTheory.Integrable g := by
    have hfInt : MeasureTheory.Integrable (fun ξ : ℝ => 𝓕 f ξ) :=
      (𝓕 f).integrable
    apply hfInt.mul_bdd (c := S.card)
      hPcontinuous.aestronglyMeasurable
    filter_upwards with ξ
    exact hPbound ξ
  have hmajorInt : MeasureTheory.Integrable
      (fun ξ : ℝ => ‖𝓕 f ξ‖ * (S.card : ℝ)) :=
    (𝓕 f).integrable.norm.mul_const _
  have hPoint : ∀ᵐ ξ : ℝ ∂MeasureTheory.volume.restrict (Set.Icc (-R) R)ᶜ,
      ‖g ξ‖ ≤ ‖𝓕 f ξ‖ * (S.card : ℝ) := by
    filter_upwards with ξ
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hPbound ξ) (norm_nonneg _)
  calc
    ‖∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ,
        𝓕 (typeILogWeightSchwartz Y A r σ hY) ξ *
          ∑ n ∈ Finset.Ioc Y A,
            (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)‖ =
        ‖∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ, g ξ‖ := by rfl
    _ ≤ ∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ, ‖g ξ‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ,
        ‖𝓕 f ξ‖ * (S.card : ℝ) :=
      MeasureTheory.integral_mono_ae hgInt.norm.integrableOn
        hmajorInt.integrableOn hPoint
    _ = (∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ, ‖𝓕 f ξ‖) * S.card := by
      rw [MeasureTheory.integral_mul_const]
    _ ≤ (2 * SchwartzMap.seminorm ℝ 2 0 (𝓕 f) / R) * S.card :=
      mul_le_mul_of_nonneg_right
        (integral_norm_fourier_schwartz_compl_Icc_le f R hR)
        (Nat.cast_nonneg S.card)
    _ = (Finset.Ioc Y A).card *
        (2 * SchwartzMap.seminorm ℝ 2 0
          (𝓕 (typeILogWeightSchwartz Y A r σ hY)) / R) := by
      dsimp only [f, S]
      ring

/-- An explicit Fourier window large enough to retain half of a source
smooth block of size `V`. -/
noncomputable def typeISourceFourierRadius
    (Y A r : ℕ) (σ V : ℝ) (hY : 0 < Y) : ℝ :=
  max 1
    (4 * (Finset.Ioc Y A).card *
      SchwartzMap.seminorm ℝ 2 0
        (𝓕 (typeILogWeightSchwartz Y A r σ hY)) / V)

theorem typeISourceFourierRadius_pos
    (Y A r : ℕ) (σ V : ℝ) (hY : 0 < Y) :
    0 < typeISourceFourierRadius Y A r σ V hY := by
  exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)

/-- The explicit source Fourier radius makes the complementary integral at
most `V / 2`, uniformly in the original ordinate. -/
theorem norm_typeILogWeight_fourier_tail_integral_le_half
    (Y A r : ℕ) (σ V t : ℝ) (hY : 0 < Y) (hV : 0 < V) :
    let R := typeISourceFourierRadius Y A r σ V hY
    ‖∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ,
        𝓕 (typeILogWeightSchwartz Y A r σ hY) ξ *
          ∑ n ∈ Finset.Ioc Y A,
            (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)‖ ≤
      V / 2 := by
  dsimp only
  let C : ℝ := SchwartzMap.seminorm ℝ 2 0
    (𝓕 (typeILogWeightSchwartz Y A r σ hY))
  let B : ℝ := (Finset.Ioc Y A).card * C
  let R : ℝ := typeISourceFourierRadius Y A r σ V hY
  have hR : 0 < R := typeISourceFourierRadius_pos Y A r σ V hY
  have hB : 0 ≤ B := by
    dsimp only [B, C]
    positivity
  have hbase : 4 * B / V ≤ R := by
    change 4 * (((Finset.Ioc Y A).card : ℝ) * C) / V ≤
      max 1 (4 * (Finset.Ioc Y A).card * C / V)
    calc
      4 * (((Finset.Ioc Y A).card : ℝ) * C) / V =
          4 * (Finset.Ioc Y A).card * C / V := by ring
      _ ≤ max 1 (4 * (Finset.Ioc Y A).card * C / V) :=
        le_max_right _ _
  have hmul : 4 * B ≤ R * V := by
    rw [div_le_iff₀ hV] at hbase
    nlinarith
  have hnumeric :
      (Finset.Ioc Y A).card * (2 * C / R) ≤ V / 2 := by
    rw [show ((Finset.Ioc Y A).card : ℝ) * (2 * C / R) =
      2 * B / R by dsimp only [B]; ring]
    rw [div_le_iff₀ hR]
    nlinarith
  exact (norm_typeILogWeight_fourier_tail_integral_le
    Y A r σ t R hY hR).trans (by simpa only [C, R] using hnumeric)

/-- Exact (untruncated) Fourier deweighting at the large-value level.  A
large source smooth block produces a literal coefficient-one Dirichlet sum
at a common shifted ordinate.  The remaining source-specific task is to
truncate the Fourier variable while retaining this lower bound. -/
theorem exists_large_coefficientOne_shift_of_typeISourceSmoothBlock
    (Y A r : ℕ) (σ V t : ℝ) (hY : 0 < Y) (hV : 0 < V)
    (hlarge : V ≤ ‖typeISourceSmoothBlock Y A r σ t‖) :
    ∃ ξ : ℝ,
      V / (2 * typeISourceSmoothBlockFourierL1 Y A r σ hY) ≤
        ‖∑ n ∈ Finset.Ioc Y A,
          (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)‖ := by
  let f := typeILogWeightSchwartz Y A r σ hY
  let C := typeISourceSmoothBlockFourierL1 Y A r σ hY
  let P : ℝ → ℂ := fun ξ =>
    ∑ n ∈ Finset.Ioc Y A,
      (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)
  have hC : 0 < C := typeISourceSmoothBlockFourierL1_pos Y A r σ hY
  have hmass : (∫ ξ : ℝ, ‖𝓕 f ξ‖) ≤ C := by
    simpa only [f, C] using
      integral_norm_fourier_typeILogWeight_le Y A r σ hY
  rw [typeISourceSmoothBlock_fourierDeweight_restricted
    Y A r σ t hY] at hlarge
  change V ≤ ‖∫ ξ : ℝ, 𝓕 f ξ * P ξ‖ at hlarge
  by_contra hexists
  push Not at hexists
  have hmajorInt : MeasureTheory.Integrable
      (fun ξ : ℝ => ‖𝓕 f ξ‖ * (V / (2 * C))) :=
    (𝓕 f).integrable.norm.mul_const _
  have hnorm : ‖∫ ξ : ℝ, 𝓕 f ξ * P ξ‖ ≤
      ∫ ξ : ℝ, ‖𝓕 f ξ‖ * (V / (2 * C)) := by
    apply MeasureTheory.norm_integral_le_of_norm_le hmajorInt
    filter_upwards with ξ
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hexists ξ).le (norm_nonneg _)
  have hthreshold : 0 ≤ V / (2 * C) := by positivity
  have hhalf : ‖∫ ξ : ℝ, 𝓕 f ξ * P ξ‖ ≤ V / 2 := by
    calc
      ‖∫ ξ : ℝ, 𝓕 f ξ * P ξ‖ ≤
          ∫ ξ : ℝ, ‖𝓕 f ξ‖ * (V / (2 * C)) := hnorm
      _ = (∫ ξ : ℝ, ‖𝓕 f ξ‖) * (V / (2 * C)) := by
        rw [MeasureTheory.integral_mul_const]
      _ ≤ C * (V / (2 * C)) :=
        mul_le_mul_of_nonneg_right hmass hthreshold
      _ = V / 2 := by field_simp
  linarith

/-- Finite-window form of exact Fourier deweighting.  Once the complementary
Fourier integral is at most half of the original threshold, a coefficient-one
sum of controlled size occurs inside the window.  This theorem isolates the
precise tail estimate still needed for a uniform ordinate-displacement bound. -/
theorem exists_bounded_coefficientOne_shift_of_typeISourceSmoothBlock
    (Y A r : ℕ) (σ V t R : ℝ) (hY : 0 < Y) (hV : 0 < V)
    (hlarge : V ≤ ‖typeISourceSmoothBlock Y A r σ t‖)
    (htail :
      ‖∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ,
        𝓕 (typeILogWeightSchwartz Y A r σ hY) ξ *
          ∑ n ∈ Finset.Ioc Y A,
            (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)‖ ≤ V / 2) :
    ∃ ξ ∈ Set.Icc (-R) R,
      V / (4 * typeISourceSmoothBlockFourierL1 Y A r σ hY) ≤
        ‖∑ n ∈ Finset.Ioc Y A,
          (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)‖ := by
  let f := typeILogWeightSchwartz Y A r σ hY
  let C := typeISourceSmoothBlockFourierL1 Y A r σ hY
  let S : Finset ℕ := Finset.Ioc Y A
  let P : ℝ → ℂ := fun ξ =>
    ∑ n ∈ S, (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)
  let g : ℝ → ℂ := fun ξ => 𝓕 f ξ * P ξ
  have hC : 0 < C := typeISourceSmoothBlockFourierL1_pos Y A r σ hY
  have hmass : (∫ ξ : ℝ, ‖𝓕 f ξ‖) ≤ C := by
    simpa only [f, C] using
      integral_norm_fourier_typeILogWeight_le Y A r σ hY
  have hPcontinuous : Continuous P := by
    dsimp only [P, S]
    apply continuous_finsetSum
    intro n hn
    apply Continuous.const_cpow
    · fun_prop
    · exact Or.inl (by
        exact_mod_cast (Nat.ne_of_gt
          (hY.trans (Finset.mem_Ioc.mp hn).1)))
  have hPbound : ∀ ξ : ℝ, ‖P ξ‖ ≤ S.card := by
    intro ξ
    calc
      ‖P ξ‖ ≤ ∑ n ∈ S,
          ‖(n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)‖ :=
        norm_sum_le _ _
      _ = ∑ _n ∈ S, 1 := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [Complex.norm_natCast_cpow_of_pos
          (hY.trans (Finset.mem_Ioc.mp hn).1)]
        simp
      _ = S.card := by simp
  have hgInt : MeasureTheory.Integrable g := by
    have hfInt : MeasureTheory.Integrable (fun ξ : ℝ => 𝓕 f ξ) :=
      (𝓕 f).integrable
    apply hfInt.mul_bdd (c := S.card)
      hPcontinuous.aestronglyMeasurable
    filter_upwards with ξ
    exact hPbound ξ
  rw [typeISourceSmoothBlock_fourierDeweight_restricted
    Y A r σ t hY] at hlarge
  change V ≤ ‖∫ ξ : ℝ, g ξ‖ at hlarge
  change ‖∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ, g ξ‖ ≤ V / 2 at htail
  have hsplit := MeasureTheory.integral_add_compl
    (f := g) (s := Set.Icc (-R) R) measurableSet_Icc hgInt
  have hcentralLarge : V / 2 ≤ ‖∫ ξ : ℝ in Set.Icc (-R) R, g ξ‖ := by
    have htriangle : ‖∫ ξ : ℝ, g ξ‖ ≤
        ‖∫ ξ : ℝ in Set.Icc (-R) R, g ξ‖ +
          ‖∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ, g ξ‖ := by
      rw [← hsplit]
      exact norm_add_le _ _
    linarith
  by_contra hexists
  push Not at hexists
  have hthreshold : 0 ≤ V / (4 * C) := by positivity
  have hmajorInt : MeasureTheory.Integrable
      (fun ξ : ℝ => ‖𝓕 f ξ‖ * (V / (4 * C))) :=
    (𝓕 f).integrable.norm.mul_const _
  have hcentralNorm : ‖∫ ξ : ℝ in Set.Icc (-R) R, g ξ‖ ≤
      ∫ ξ : ℝ in Set.Icc (-R) R,
        ‖𝓕 f ξ‖ * (V / (4 * C)) := by
    apply MeasureTheory.norm_integral_le_of_norm_le hmajorInt.integrableOn
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc]
      with ξ hξ
    change ‖𝓕 f ξ * P ξ‖ ≤ ‖𝓕 f ξ‖ * (V / (4 * C))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hexists ξ hξ).le (norm_nonneg _)
  have hmajorSplit := MeasureTheory.integral_add_compl
    (f := fun ξ : ℝ => ‖𝓕 f ξ‖ * (V / (4 * C)))
    (s := Set.Icc (-R) R) measurableSet_Icc hmajorInt
  have hcentralMajor :
      (∫ ξ : ℝ in Set.Icc (-R) R,
        ‖𝓕 f ξ‖ * (V / (4 * C))) ≤
      ∫ ξ : ℝ, ‖𝓕 f ξ‖ * (V / (4 * C)) := by
    rw [← hmajorSplit]
    exact le_add_of_nonneg_right
      (MeasureTheory.integral_nonneg fun _ => mul_nonneg (norm_nonneg _) hthreshold)
  have hquarter : ‖∫ ξ : ℝ in Set.Icc (-R) R, g ξ‖ ≤ V / 4 := by
    calc
      ‖∫ ξ : ℝ in Set.Icc (-R) R, g ξ‖ ≤
          ∫ ξ : ℝ in Set.Icc (-R) R,
            ‖𝓕 f ξ‖ * (V / (4 * C)) := hcentralNorm
      _ ≤ ∫ ξ : ℝ, ‖𝓕 f ξ‖ * (V / (4 * C)) := hcentralMajor
      _ = (∫ ξ : ℝ, ‖𝓕 f ξ‖) * (V / (4 * C)) := by
        rw [MeasureTheory.integral_mul_const]
      _ ≤ C * (V / (4 * C)) :=
        mul_le_mul_of_nonneg_right hmass hthreshold
      _ = V / 4 := by field_simp
  linarith

/-- Unconditional bounded Fourier extraction using the explicit source
radius.  The tail premise of the finite-window theorem is discharged by the
order-two Schwartz estimate above. -/
theorem exists_explicitly_bounded_coefficientOne_shift_of_typeISourceSmoothBlock
    (Y A r : ℕ) (σ V t : ℝ) (hY : 0 < Y) (hV : 0 < V)
    (hlarge : V ≤ ‖typeISourceSmoothBlock Y A r σ t‖) :
    let R := typeISourceFourierRadius Y A r σ V hY
    ∃ ξ ∈ Set.Icc (-R) R,
      V / (4 * typeISourceSmoothBlockFourierL1 Y A r σ hY) ≤
        ‖∑ n ∈ Finset.Ioc Y A,
          (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)‖ := by
  dsimp only
  apply exists_bounded_coefficientOne_shift_of_typeISourceSmoothBlock
    Y A r σ V t (typeISourceFourierRadius Y A r σ V hY)
      hY hV hlarge
  exact norm_typeILogWeight_fourier_tail_integral_le_half
    Y A r σ V t hY hV

/-- The explicit source radius supplies the tail hypothesis simultaneously
for every member of an indexed family. -/
theorem typeISourceFourier_uniform_tail_bound
    {ι : Type*} (Y A r : ℕ) (σ V : ℝ) (W : ι → ℝ)
    (hY : 0 < Y) (hV : 0 < V) :
    let R := typeISourceFourierRadius Y A r σ V hY
    ∀ x,
      ‖∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ,
        𝓕 (typeILogWeightSchwartz Y A r σ hY) ξ *
          ∑ n ∈ Finset.Ioc Y A,
            (n : ℂ) ^ (-((((W x) - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)‖ ≤
        V / 2 := by
  dsimp only
  intro x
  exact norm_typeILogWeight_fourier_tail_integral_le_half
    Y A r σ V (W x) hY hV

/-- Deterministically select the bounded Fourier frequency supplied by the
finite-window theorem for every member of a fixed source-smooth family. -/
noncomputable def boundedTypeISourceFourierFrequency
    {ι : Type*} (Y A r : ℕ) (σ V R : ℝ) (W : ι → ℝ)
    (hY : 0 < Y) (hV : 0 < V)
    (hlarge : ∀ x, V ≤ ‖typeISourceSmoothBlock Y A r σ (W x)‖)
    (htail : ∀ x,
      ‖∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ,
        𝓕 (typeILogWeightSchwartz Y A r σ hY) ξ *
          ∑ n ∈ Finset.Ioc Y A,
            (n : ℂ) ^ (-((((W x) - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)‖ ≤
        V / 2)
    (x : ι) : ℝ :=
  Classical.choose
    (exists_bounded_coefficientOne_shift_of_typeISourceSmoothBlock
      Y A r σ V (W x) R hY hV (hlarge x) (htail x))

theorem boundedTypeISourceFourierFrequency_mem_and_large
    {ι : Type*} (Y A r : ℕ) (σ V R : ℝ) (W : ι → ℝ)
    (hY : 0 < Y) (hV : 0 < V)
    (hlarge : ∀ x, V ≤ ‖typeISourceSmoothBlock Y A r σ (W x)‖)
    (htail : ∀ x,
      ‖∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ,
        𝓕 (typeILogWeightSchwartz Y A r σ hY) ξ *
          ∑ n ∈ Finset.Ioc Y A,
            (n : ℂ) ^ (-((((W x) - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)‖ ≤
        V / 2)
    (x : ι) :
    let ξ := boundedTypeISourceFourierFrequency
      Y A r σ V R W hY hV hlarge htail x
    ξ ∈ Set.Icc (-R) R ∧
      V / (4 * typeISourceSmoothBlockFourierL1 Y A r σ hY) ≤
        ‖∑ n ∈ Finset.Ioc Y A,
          (n : ℂ) ^ (-((((W x) - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)‖ :=
  Classical.choose_spec
    (exists_bounded_coefficientOne_shift_of_typeISourceSmoothBlock
      Y A r σ V (W x) R hY hV (hlarge x) (htail x))

/-- The ordinate obtained from the selected bounded Fourier frequency. -/
noncomputable def boundedTypeISourceFourierOrdinate
    {ι : Type*} (Y A r : ℕ) (σ V R : ℝ) (W : ι → ℝ)
    (hY : 0 < Y) (hV : 0 < V)
    (hlarge : ∀ x, V ≤ ‖typeISourceSmoothBlock Y A r σ (W x)‖)
    (htail : ∀ x,
      ‖∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ,
        𝓕 (typeILogWeightSchwartz Y A r σ hY) ξ *
          ∑ n ∈ Finset.Ioc Y A,
            (n : ℂ) ^ (-((((W x) - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)‖ ≤
        V / 2)
    (x : ι) : ℝ :=
  W x - 2 * Real.pi *
    boundedTypeISourceFourierFrequency
      Y A r σ V R W hY hV hlarge htail x

theorem boundedTypeISourceFourierOrdinate_displacement_le
    {ι : Type*} (Y A r : ℕ) (σ V R : ℝ) (W : ι → ℝ)
    (hY : 0 < Y) (hV : 0 < V)
    (hlarge : ∀ x, V ≤ ‖typeISourceSmoothBlock Y A r σ (W x)‖)
    (htail : ∀ x,
      ‖∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ,
        𝓕 (typeILogWeightSchwartz Y A r σ hY) ξ *
          ∑ n ∈ Finset.Ioc Y A,
            (n : ℂ) ^ (-((((W x) - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)‖ ≤
        V / 2)
    (x : ι) :
    |boundedTypeISourceFourierOrdinate
        Y A r σ V R W hY hV hlarge htail x - W x| ≤
      2 * Real.pi * R := by
  let ξ := boundedTypeISourceFourierFrequency
    Y A r σ V R W hY hV hlarge htail x
  have hξmem := (boundedTypeISourceFourierFrequency_mem_and_large
    Y A r σ V R W hY hV hlarge htail x).1
  have hξ : |ξ| ≤ R := (abs_le).2 hξmem
  rw [boundedTypeISourceFourierOrdinate]
  change |W x - 2 * Real.pi * ξ - W x| ≤ 2 * Real.pi * R
  rw [show W x - 2 * Real.pi * ξ - W x = -(2 * Real.pi * ξ) by ring,
    abs_neg, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ)),
    abs_of_pos Real.pi_pos]
  exact mul_le_mul_of_nonneg_left hξ (by positivity)

theorem boundedTypeISourceFourierOrdinate_large
    {ι : Type*} (Y A r : ℕ) (σ V R : ℝ) (W : ι → ℝ)
    (hY : 0 < Y) (hV : 0 < V)
    (hlarge : ∀ x, V ≤ ‖typeISourceSmoothBlock Y A r σ (W x)‖)
    (htail : ∀ x,
      ‖∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ,
        𝓕 (typeILogWeightSchwartz Y A r σ hY) ξ *
          ∑ n ∈ Finset.Ioc Y A,
            (n : ℂ) ^ (-((((W x) - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)‖ ≤
        V / 2)
    (x : ι) :
    V / (4 * typeISourceSmoothBlockFourierL1 Y A r σ hY) ≤
      ‖∑ n ∈ Finset.Ioc Y A,
        dirichletPhase n
          (boundedTypeISourceFourierOrdinate
            Y A r σ V R W hY hV hlarge htail x)‖ := by
  have hx := (boundedTypeISourceFourierFrequency_mem_and_large
    Y A r σ V R W hY hV hlarge htail x).2
  calc
    V / (4 * typeISourceSmoothBlockFourierL1 Y A r σ hY) ≤
        ‖∑ n ∈ Finset.Ioc Y A,
          (n : ℂ) ^
            (-((((W x) - 2 * Real.pi *
              boundedTypeISourceFourierFrequency
                Y A r σ V R W hY hV hlarge htail x : ℝ) : ℂ)) * I)‖ := hx
    _ = ‖∑ n ∈ Finset.Ioc Y A,
          dirichletPhase n
            (boundedTypeISourceFourierOrdinate
              Y A r σ V R W hY hV hlarge htail x)‖ := by
      congr 1
      apply Finset.sum_congr rfl
      intro n _
      unfold dirichletPhase boundedTypeISourceFourierOrdinate
      congr 1
      ring

/-- Canonical bounded coefficient-one ordinate obtained from the explicit
source Fourier radius. -/
noncomputable def explicitBoundedTypeISourceFourierOrdinate
    {ι : Type*} (Y A r : ℕ) (σ V : ℝ) (W : ι → ℝ)
    (hY : 0 < Y) (hV : 0 < V)
    (hlarge : ∀ x, V ≤ ‖typeISourceSmoothBlock Y A r σ (W x)‖)
    (x : ι) : ℝ :=
  boundedTypeISourceFourierOrdinate Y A r σ V
    (typeISourceFourierRadius Y A r σ V hY) W hY hV hlarge
    (typeISourceFourier_uniform_tail_bound Y A r σ V W hY hV) x

theorem explicitBoundedTypeISourceFourierOrdinate_displacement_le
    {ι : Type*} (Y A r : ℕ) (σ V : ℝ) (W : ι → ℝ)
    (hY : 0 < Y) (hV : 0 < V)
    (hlarge : ∀ x, V ≤ ‖typeISourceSmoothBlock Y A r σ (W x)‖)
    (x : ι) :
    |explicitBoundedTypeISourceFourierOrdinate
        Y A r σ V W hY hV hlarge x - W x| ≤
      2 * Real.pi * typeISourceFourierRadius Y A r σ V hY := by
  exact boundedTypeISourceFourierOrdinate_displacement_le
    Y A r σ V (typeISourceFourierRadius Y A r σ V hY) W hY hV hlarge
      (typeISourceFourier_uniform_tail_bound Y A r σ V W hY hV) x

theorem explicitBoundedTypeISourceFourierOrdinate_large
    {ι : Type*} (Y A r : ℕ) (σ V : ℝ) (W : ι → ℝ)
    (hY : 0 < Y) (hV : 0 < V)
    (hlarge : ∀ x, V ≤ ‖typeISourceSmoothBlock Y A r σ (W x)‖)
    (x : ι) :
    V / (4 * typeISourceSmoothBlockFourierL1 Y A r σ hY) ≤
      ‖∑ n ∈ Finset.Ioc Y A,
        dirichletPhase n
          (explicitBoundedTypeISourceFourierOrdinate
            Y A r σ V W hY hV hlarge x)‖ := by
  exact boundedTypeISourceFourierOrdinate_large
    Y A r σ V (typeISourceFourierRadius Y A r σ V hY) W hY hV hlarge
      (typeISourceFourier_uniform_tail_bound Y A r σ V W hY hV) x

/-- Conditional energy transfer through the bounded Fourier witnesses.  It
retains the complete index type and makes the exact tolerance-normalization
loss explicit; no separation or multiplicity is discarded. -/
theorem typeISourceSmoothBlock_energy_le_boundedFourierOrdinate_energy
    {ι : Type*} [Fintype ι]
    (Y A r : ℕ) (σ V R : ℝ) (W : ι → ℝ)
    (hY : 0 < Y) (hV : 0 < V)
    (hlarge : ∀ x, V ≤ ‖typeISourceSmoothBlock Y A r σ (W x)‖)
    (htail : ∀ x,
      ‖∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ,
        𝓕 (typeILogWeightSchwartz Y A r σ hY) ξ *
          ∑ n ∈ Finset.Ioc Y A,
            (n : ℂ) ^ (-((((W x) - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)‖ ≤
        V / 2) :
    approximateAdditiveEnergyOf 1 W ≤
      (4 * Nat.ceil (1 + 4 * (2 * Real.pi * R)) + 6) *
        approximateAdditiveEnergyOf 1
          (boundedTypeISourceFourierOrdinate
            Y A r σ V R W hY hV hlarge htail) := by
  let W' := boundedTypeISourceFourierOrdinate
    Y A r σ V R W hY hV hlarge htail
  calc
    approximateAdditiveEnergyOf 1 W ≤
        approximateAdditiveEnergyOf (1 + 4 * (2 * Real.pi * R)) W' :=
      approximateAdditiveEnergyOf_perturbation_le
        (fun x => boundedTypeISourceFourierOrdinate_displacement_le
          Y A r σ V R W hY hV hlarge htail x)
    _ ≤ (4 * Nat.ceil (1 + 4 * (2 * Real.pi * R)) + 6) *
          approximateAdditiveEnergyOf 1 W' :=
      approximateAdditiveEnergyOf_le_natCeil_mul_unit _ _

/-- Unconditional energy transfer at the explicit Fourier radius. -/
theorem typeISourceSmoothBlock_energy_le_explicitBoundedFourierOrdinate_energy
    {ι : Type*} [Fintype ι]
    (Y A r : ℕ) (σ V : ℝ) (W : ι → ℝ)
    (hY : 0 < Y) (hV : 0 < V)
    (hlarge : ∀ x, V ≤ ‖typeISourceSmoothBlock Y A r σ (W x)‖) :
    let R := typeISourceFourierRadius Y A r σ V hY
    approximateAdditiveEnergyOf 1 W ≤
      (4 * Nat.ceil (1 + 4 * (2 * Real.pi * R)) + 6) *
        approximateAdditiveEnergyOf 1
          (explicitBoundedTypeISourceFourierOrdinate
            Y A r σ V W hY hV hlarge) := by
  dsimp only
  exact typeISourceSmoothBlock_energy_le_boundedFourierOrdinate_energy
    Y A r σ V (typeISourceFourierRadius Y A r σ V hY) W hY hV hlarge
      (typeISourceFourier_uniform_tail_bound Y A r σ V W hY hV)

/-- Conditional, fully re-separated Fourier transfer for a fixed source
smooth block.  A uniform tail bound supplies bounded coefficient-one
ordinates; all indices survive tolerance normalization, and the resulting
family is colored into four one-separated energy classes. -/
theorem exists_separated_boundedTypeISourceFourier_energy_classes
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (Y A r : ℕ) (σ V R : ℝ) (W : ι → ℝ)
    (hY : 0 < Y) (hV : 0 < V) (hR : 0 ≤ R)
    (hlarge : ∀ x, V ≤ ‖typeISourceSmoothBlock Y A r σ (W x)‖)
    (hsep : ∀ x y : ι, x ≠ y → 1 ≤ |W x - W y|)
    (htail : ∀ x,
      ‖∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ,
        𝓕 (typeILogWeightSchwartz Y A r σ hY) ξ *
          ∑ n ∈ Finset.Ioc Y A,
            (n : ℂ) ^ (-((((W x) - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)‖ ≤
        V / 2) :
    let W' := boundedTypeISourceFourierOrdinate
      Y A r σ V R W hY hV hlarge htail
    let d := 2 * Real.pi * R
    let L := Nat.ceil (2 * d + 2)
    let hpert : ∀ x, |W' x - W x| ≤ d := fun x =>
      boundedTypeISourceFourierOrdinate_displacement_le
        Y A r σ V R W hY hV hlarge htail x
    let hlocal : ∀ z : ℤ, (unitBinFinset W' z).card ≤ L := fun z =>
      unitBinFinset_perturbation_card_le_natCeil
        W W' d (by dsimp only [d]; positivity) hsep hpert z
    ∃ label : Fin 4 → ZMod 2 × Fin (L + 1),
      let color := boundedMultiplicityColor W' L hlocal
      let Wᵢ := fun i : Fin 4 =>
        fun x : EnergyColorFiber color (label i) => W' x.1
      approximateAdditiveEnergyOf 1 W ≤
          (4 * Nat.ceil (1 + 4 * d) + 6) *
            approximateAdditiveEnergyOf 1 W' ∧
        4 * (approximateAdditiveEnergyOf 1 W' : ℝ) ≤
          9 * (Fintype.card (ZMod 2 × Fin (L + 1)) : ℝ) ^ 4 *
            ((approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ)) ∧
        (∀ (i : Fin 4) (x : EnergyColorFiber color (label i)),
          V / (4 * typeISourceSmoothBlockFourierL1 Y A r σ hY) ≤
            ‖∑ n ∈ Finset.Ioc Y A, dirichletPhase n (Wᵢ i x)‖) ∧
        ∀ (i : Fin 4) (x y : EnergyColorFiber color (label i)),
          x ≠ y → 1 ≤ |Wᵢ i x - Wᵢ i y| := by
  classical
  dsimp only
  let W' := boundedTypeISourceFourierOrdinate
    Y A r σ V R W hY hV hlarge htail
  let d := 2 * Real.pi * R
  let L := Nat.ceil (2 * d + 2)
  let hpert : ∀ x, |W' x - W x| ≤ d := fun x =>
    boundedTypeISourceFourierOrdinate_displacement_le
      Y A r σ V R W hY hV hlarge htail x
  let hlocal : ∀ z : ℤ, (unitBinFinset W' z).card ≤ L := fun z =>
    unitBinFinset_perturbation_card_le_natCeil
      W W' d (by dsimp only [d]; positivity) hsep hpert z
  obtain ⟨label, htransfer, henergy, hseparated⟩ :=
    exists_separated_perturbed_energy_classes W W' d
      (by dsimp only [d]; positivity) hsep hpert
  refine ⟨label, htransfer, henergy, ?_, hseparated⟩
  intro i x
  exact boundedTypeISourceFourierOrdinate_large
    Y A r σ V R W hY hV hlarge htail x.1

/-- Fully explicit, assumption-free Fourier truncation and re-separation for
a fixed source smooth block.  The only hypotheses are positivity, largeness,
and the original one-separation; the Fourier tail is now internal. -/
theorem exists_separated_explicitTypeISourceFourier_energy_classes
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (Y A r : ℕ) (σ V : ℝ) (W : ι → ℝ)
    (hY : 0 < Y) (hV : 0 < V)
    (hlarge : ∀ x, V ≤ ‖typeISourceSmoothBlock Y A r σ (W x)‖)
    (hsep : ∀ x y : ι, x ≠ y → 1 ≤ |W x - W y|) :
    let R := typeISourceFourierRadius Y A r σ V hY
    let W' := explicitBoundedTypeISourceFourierOrdinate
      Y A r σ V W hY hV hlarge
    let d := 2 * Real.pi * R
    let L := Nat.ceil (2 * d + 2)
    let hpert : ∀ x, |W' x - W x| ≤ d := fun x =>
      explicitBoundedTypeISourceFourierOrdinate_displacement_le
        Y A r σ V W hY hV hlarge x
    let hlocal : ∀ z : ℤ, (unitBinFinset W' z).card ≤ L := fun z =>
      unitBinFinset_perturbation_card_le_natCeil
        W W' d (by
          dsimp only [d, R]
          exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
            (typeISourceFourierRadius_pos Y A r σ V hY).le) hsep hpert z
    ∃ label : Fin 4 → ZMod 2 × Fin (L + 1),
      let color := boundedMultiplicityColor W' L hlocal
      let Wᵢ := fun i : Fin 4 =>
        fun x : EnergyColorFiber color (label i) => W' x.1
      approximateAdditiveEnergyOf 1 W ≤
          (4 * Nat.ceil (1 + 4 * d) + 6) *
            approximateAdditiveEnergyOf 1 W' ∧
        4 * (approximateAdditiveEnergyOf 1 W' : ℝ) ≤
          9 * (Fintype.card (ZMod 2 × Fin (L + 1)) : ℝ) ^ 4 *
            ((approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ)) ∧
        (∀ (i : Fin 4) (x : EnergyColorFiber color (label i)),
          V / (4 * typeISourceSmoothBlockFourierL1 Y A r σ hY) ≤
            ‖∑ n ∈ Finset.Ioc Y A, dirichletPhase n (Wᵢ i x)‖) ∧
        ∀ (i : Fin 4) (x y : EnergyColorFiber color (label i)),
          x ≠ y → 1 ≤ |Wᵢ i x - Wᵢ i y| := by
  dsimp only
  exact exists_separated_boundedTypeISourceFourier_energy_classes
    Y A r σ V (typeISourceFourierRadius Y A r σ V hY) W hY hV
      (typeISourceFourierRadius_pos Y A r σ V hY).le hlarge hsep
      (typeISourceFourier_uniform_tail_bound Y A r σ V W hY hV)

/-- Apply exact Fourier deweighting to the deterministic large block selected
from a sharp Type-I family.  The witness is still recorded as a Fourier
variable so that a later tail estimate can bound the induced ordinate shift. -/
theorem exists_large_coefficientOne_shift_of_chosenTypeISourceSmoothBlock
    {ι : Type*} (A N : ℕ) (σ V : ℝ) (W : ι → ℝ) (hN : 0 < N)
    (hV : 0 < V)
    (hlarge : ∀ x, V ≤
      ‖dirichletPoly N (classicalZetaLongLineCoeff A σ) (W x)‖)
    (x : ι) :
    let r := chosenTypeISourceSmoothBlock A N σ V W hN hlarge x
    ∃ ξ : ℝ,
      (V / 2) / (2 *
          typeISourceSmoothBlockFourierL1 N (min (2 * N) A) r σ hN) ≤
        ‖∑ n ∈ Finset.Ioc N (min (2 * N) A),
          (n : ℂ) ^
            (-((((W x) - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)‖ := by
  dsimp only
  apply exists_large_coefficientOne_shift_of_typeISourceSmoothBlock
    N (min (2 * N) A)
      (chosenTypeISourceSmoothBlock A N σ V W hN hlarge x)
      σ (V / 2) (W x) hN (by positivity)
  exact chosenTypeISourceSmoothBlock_large A N σ V W hN hlarge x

/-- Energy-level smooth-block selection.  The entire indexed energy is
controlled by four fixed-smooth-block classes; unlike a cardinality
pigeonhole, this retains the source energy quantity. -/
theorem exists_typeISourceSmoothBlock_energy_classes
    {ι : Type*} [Fintype ι]
    (A N : ℕ) (σ V : ℝ) (W : ι → ℝ) (hN : 0 < N)
    (hlarge : ∀ x, V ≤
      ‖dirichletPoly N (classicalZetaLongLineCoeff A σ) (W x)‖)
    (hsep : ∀ x y : ι, x ≠ y → 1 ≤ |W x - W y|) :
    ∃ label : Fin 4 → Fin 2,
      let color := chosenTypeISourceSmoothBlock A N σ V W hN hlarge
      let Wᵢ := fun i : Fin 4 =>
        fun x : EnergyColorFiber color (label i) => W x.1
      4 * (approximateAdditiveEnergyOf 1 W : ℝ) ≤
          9 * (2 : ℝ) ^ 4 *
            ((approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ)) ∧
        (∀ (i : Fin 4) (x : EnergyColorFiber color (label i)),
          V / 2 ≤ ‖typeISourceSmoothBlock N (min (2 * N) A)
            (label i) σ (W x.1)‖) ∧
        ∀ (i : Fin 4) (x y : EnergyColorFiber color (label i)),
          x ≠ y → 1 ≤ |W x.1 - W y.1| := by
  classical
  let color := chosenTypeISourceSmoothBlock A N σ V W hN hlarge
  obtain ⟨label, henergy⟩ := exists_energy_color_classes W color
  refine ⟨label, ?_, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using henergy
  · intro i x
    have hx := chosenTypeISourceSmoothBlock_large A N σ V W hN hlarge x.1
    have hcolor : color x.1 = label i := x.2
    simpa only [color, hcolor] using hx
  · intro i x y hxy
    exact hsep x.1 y.1 (fun h => hxy (Subtype.ext h))

/-- Apply the energy-level two-block selection to an actual classical Type-I
branch/scale class returned by the slab dichotomy. -/
theorem exists_classicalTypeISourceSmoothBlock_energy_classes
    (σ T D₁ : ℝ) (Y X L : ℕ)
    (shiftedZero : ↥(zerosInRect σ 1 T (2 * T)) → ℝ)
    (baseColor : ↥(zerosInRect σ 1 T (2 * T)) →
      ClassicalBranchScaleColor T Y)
    (hlocal : ∀ z : ℤ,
      (unitBinFinset
        (fun x : ClassicalSlabZeroCopy σ T => shiftedZero x.1) z).card ≤ L)
    (branchLabel : ClassicalSeparatedBranchScaleColor T Y L)
    (r : Fin (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊))
    (hlabel : branchLabel.1 = some (Sum.inl r))
    (hN : 0 < 2 ^ (r : ℕ) * Y)
    (hlarge : ∀ x : EnergyColorFiber
      (classicalSeparatedBranchScaleColor σ T Y shiftedZero baseColor L hlocal)
        branchLabel,
      ClassicalBranchScaleLarge σ T D₁ Y X branchLabel.1
        (shiftedZero x.1.1))
    (hsep : ∀ x y : EnergyColorFiber
      (classicalSeparatedBranchScaleColor σ T Y shiftedZero baseColor L hlocal)
        branchLabel,
      x ≠ y → 1 ≤ |shiftedZero x.1.1 - shiftedZero y.1.1|) :
    let A := ⌊sharpZetaCutoff T⌋₊
    let N := 2 ^ (r : ℕ) * Y
    let V := ((3 / 4) * (T ^ (-D₁) / 2)) / Nat.clog 2 A
    let ι := EnergyColorFiber
      (classicalSeparatedBranchScaleColor σ T Y shiftedZero baseColor L hlocal)
        branchLabel
    let W : ι → ℝ := fun x => shiftedZero x.1.1
    ∃ label : Fin 4 → Fin 2,
      let color := chosenTypeISourceSmoothBlock A N σ V W hN
        (fun x => by
          have hx := hlarge x
          rw [hlabel] at hx
          simpa only [ClassicalBranchScaleLarge, ClassicalTypeILargeAt,
            A, N, V, W] using hx.1)
      let Wᵢ := fun i : Fin 4 =>
        fun x : EnergyColorFiber color (label i) => W x.1
      4 * (approximateAdditiveEnergyOf 1 W : ℝ) ≤
          9 * (2 : ℝ) ^ 4 *
            ((approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ)) ∧
        (∀ (i : Fin 4) (x : EnergyColorFiber color (label i)),
          V / 2 ≤ ‖typeISourceSmoothBlock N (min (2 * N) A)
            (label i) σ (W x.1)‖) ∧
        ∀ (i : Fin 4) (x y : EnergyColorFiber color (label i)),
          x ≠ y → 1 ≤ |W x.1 - W y.1| := by
  dsimp only
  let A := ⌊sharpZetaCutoff T⌋₊
  let N := 2 ^ (r : ℕ) * Y
  let V := ((3 / 4) * (T ^ (-D₁) / 2)) / Nat.clog 2 A
  let ι := EnergyColorFiber
    (classicalSeparatedBranchScaleColor σ T Y shiftedZero baseColor L hlocal)
      branchLabel
  let W : ι → ℝ := fun x => shiftedZero x.1.1
  have hraw : ∀ x : ι, V ≤
      ‖dirichletPoly N (classicalZetaLongLineCoeff A σ) (W x)‖ := by
    intro x
    have hx := hlarge x
    rw [hlabel] at hx
    simpa only [ClassicalBranchScaleLarge, ClassicalTypeILargeAt,
      A, N, V, W] using hx.1
  exact exists_typeISourceSmoothBlock_energy_classes A N σ V W hN hraw hsep

/-- Normalize the weighted classical Type-I line coefficient at its dyadic
scale.  This is the exact pre-Fourier-deweighting coefficient sequence. -/
noncomputable def normalizedClassicalZetaLongLineCoeff
    (A N : ℕ) (σ : ℝ) (n : ℕ) : ℂ :=
  (((N : ℝ) ^ σ : ℝ) : ℂ) * classicalZetaLongLineCoeff A σ n

theorem norm_normalizedClassicalZetaLongLineCoeff_le_one
    (A N n : ℕ) (σ : ℝ) (hN : 0 < N) (hσ : 0 ≤ σ)
    (hn : n ∈ dyadicInterval N) :
    ‖normalizedClassicalZetaLongLineCoeff A N σ n‖ ≤ 1 := by
  have hnData := Finset.mem_Ioc.mp hn
  have hnPos : 0 < n := lt_of_le_of_lt (Nat.zero_le N) hnData.1
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hnPos
  by_cases hnA : n ≤ A
  · have hNn : (N : ℝ) ≤ n := by exact_mod_cast hnData.1.le
    have hPow : (N : ℝ) ^ σ ≤ (n : ℝ) ^ σ :=
      Real.rpow_le_rpow hNreal.le hNn hσ
    have hnPowPos : 0 < (n : ℝ) ^ σ := Real.rpow_pos_of_pos hnReal _
    rw [normalizedClassicalZetaLongLineCoeff, classicalZetaLongLineCoeff,
      if_pos hnA, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hNreal.le _),
      Complex.norm_natCast_cpow_of_pos hnPos]
    change (N : ℝ) ^ σ * (n : ℝ) ^ (-σ) ≤ 1
    rw [Real.rpow_neg hnReal.le, ← div_eq_mul_inv]
    exact (div_le_one hnPowPos).2 hPow
  · simp [normalizedClassicalZetaLongLineCoeff,
      classicalZetaLongLineCoeff, hnA]

theorem dirichletPoly_normalizedClassicalZetaLongLineCoeff
    (A N : ℕ) (σ t : ℝ) :
    dirichletPoly N (normalizedClassicalZetaLongLineCoeff A N σ) t =
      (((N : ℝ) ^ σ : ℝ) : ℂ) *
        dirichletPoly N (classicalZetaLongLineCoeff A σ) t := by
  unfold dirichletPoly normalizedClassicalZetaLongLineCoeff
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- An inhabited classical Type-I branch class before Fourier deweighting is
an exact general `LargeValuePattern`.  This theorem deliberately does not
claim the zeta-specific coefficient-one conversion required by the source
endpoint. -/
theorem exists_classicalTypeIWeightedClassPattern
    (δ σ T D₁ : ℝ) (Y X L : ℕ)
    (shiftedZero : ↥(zerosInRect σ 1 T (2 * T)) → ℝ)
    (baseColor : ↥(zerosInRect σ 1 T (2 * T)) →
      ClassicalBranchScaleColor T Y)
    (hlocal : ∀ z : ℤ,
      (unitBinFinset
        (fun x : ClassicalSlabZeroCopy σ T => shiftedZero x.1) z).card ≤ L)
    (label : ClassicalSeparatedBranchScaleColor T Y L)
    (r : Fin (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊))
    (hlabel : label.1 = some (Sum.inl r))
    (hT : 0 < T) (hA : 1 < ⌊sharpZetaCutoff T⌋₊)
    (hN : 1 < 2 ^ (r : ℕ) * Y) (hσ : 0 ≤ σ)
    (hinterval : ∀ ρ : ↥(zerosInRect σ 1 T (2 * T)),
      T - T ^ δ ≤ shiftedZero ρ ∧
        shiftedZero ρ ≤ 2 * T + T ^ δ)
    (hlarge : ∀ x : EnergyColorFiber
      (classicalSeparatedBranchScaleColor σ T Y shiftedZero baseColor L hlocal)
        label,
      ClassicalBranchScaleLarge σ T D₁ Y X label.1 (shiftedZero x.1.1))
    (hsep : ∀ x y : EnergyColorFiber
      (classicalSeparatedBranchScaleColor σ T Y shiftedZero baseColor L hlocal)
        label,
      x ≠ y → 1 ≤ |shiftedZero x.1.1 - shiftedZero y.1.1|) :
    ∃ P : LargeValuePattern,
      let N := 2 ^ (r : ℕ) * Y
      P.N = (N : ℝ) ∧
      P.scale = N ∧
      P.T = (2 * T + T ^ δ) - (T - T ^ δ) ∧
      P.V = (N : ℝ) ^ σ *
        (((3 / 4) * (T ^ (-D₁) / 2)) /
          Nat.clog 2 ⌊sharpZetaCutoff T⌋₊) ∧
      finsetAdditiveEnergy P.ordinates =
        approximateAdditiveEnergyOf 1
          (fun x : EnergyColorFiber
            (classicalSeparatedBranchScaleColor σ T Y
              shiftedZero baseColor L hlocal) label => shiftedZero x.1.1) := by
  let A := ⌊sharpZetaCutoff T⌋₊
  let N := 2 ^ (r : ℕ) * Y
  let raw : ℝ := ((3 / 4) * (T ^ (-D₁) / 2)) / Nat.clog 2 A
  let threshold : ℝ := (N : ℝ) ^ σ * raw
  let W := fun x : EnergyColorFiber
      (classicalSeparatedBranchScaleColor σ T Y shiftedZero baseColor L hlocal)
        label => shiftedZero x.1.1
  have hNpos : 0 < N := by omega
  have hrawPos : 0 < raw := by
    have hk : 0 < Nat.clog 2 A :=
      Nat.clog_pos Nat.one_lt_two (by simpa only [A] using hA)
    dsimp only [raw]
    positivity
  have hthreshold : 0 < threshold := by
    dsimp only [threshold]
    positivity
  have hcoeff : ∀ n ∈ dyadicInterval N,
      ‖normalizedClassicalZetaLongLineCoeff A N σ n‖ ≤ 1 := by
    intro n hn
    exact norm_normalizedClassicalZetaLongLineCoeff_le_one A N n σ
      hNpos hσ hn
  have hW : ∀ x, T - T ^ δ ≤ W x ∧ W x ≤ 2 * T + T ^ δ := by
    intro x
    exact hinterval x.1.1
  have hsepW : ∀ x y, x ≠ y → 1 ≤ |W x - W y| := hsep
  have hrawLarge : ∀ x, raw ≤
      ‖dirichletPoly N (classicalZetaLongLineCoeff A σ) (W x)‖ := by
    intro x
    have hx := hlarge x
    rw [hlabel] at hx
    simpa only [ClassicalBranchScaleLarge, ClassicalTypeILargeAt, A, N,
      raw, W] using hx.1
  have hlargeNorm : ∀ x, threshold ≤
      ‖dirichletPoly N
        (normalizedClassicalZetaLongLineCoeff A N σ) (W x)‖ := by
    intro x
    rw [dirichletPoly_normalizedClassicalZetaLongLineCoeff, norm_mul,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact mul_le_mul_of_nonneg_left (hrawLarge x)
      (Real.rpow_nonneg (by positivity) _)
  have hab : T - T ^ δ < 2 * T + T ^ δ := by
    have hpow : 0 ≤ T ^ δ := Real.rpow_nonneg hT.le δ
    linarith
  let P := indexedDirichletLargeValuePattern N threshold
    (T - T ^ δ) (2 * T + T ^ δ)
    (normalizedClassicalZetaLongLineCoeff A N σ) W hN hthreshold hab
    hcoeff hW hsepW hlargeNorm
  refine ⟨P, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · exact indexedDirichletLargeValuePattern_energy_eq N threshold
      (T - T ^ δ) (2 * T + T ^ δ)
      (normalizedClassicalZetaLongLineCoeff A N σ) W hN hthreshold hab
      hcoeff hW hsepW hlargeNorm

/-- Every inhabited classical Type-II branch class is an exact source
`LargeValuePattern` after the native sharp-mollifier coefficient
normalization.  Its ordinate-set energy equals the indexed class energy, so
analytic multiplicity is not lost at the pattern boundary. -/
theorem exists_classicalTypeIIClassPattern
    (δ σ T D₁ η C : ℝ) (Y X L : ℕ)
    (shiftedZero : ↥(zerosInRect σ 1 T (2 * T)) → ℝ)
    (baseColor : ↥(zerosInRect σ 1 T (2 * T)) →
      ClassicalBranchScaleColor T Y)
    (hlocal : ∀ z : ℤ,
      (unitBinFinset
        (fun x : ClassicalSlabZeroCopy σ T => shiftedZero x.1) z).card ≤ L)
    (label : ClassicalSeparatedBranchScaleColor T Y L)
    (r : Fin (Nat.clog 2 Y))
    (hlabel : label.1 = some (Sum.inr r))
    (hT : 0 < T) (hY : 1 < Y)
    (hN : 1 < 2 ^ (r : ℕ) * X)
    (hσ : 0 ≤ σ) (hη : 0 ≤ η) (hC : 0 < C)
    (hCoeff : ∀ m : ℕ, 0 < m →
      ‖sharpMollifiedCoeff Y X m‖ ≤ C * (m : ℝ) ^ η)
    (hinterval : ∀ ρ : ↥(zerosInRect σ 1 T (2 * T)),
      T - T ^ δ ≤ shiftedZero ρ ∧
        shiftedZero ρ ≤ 2 * T + T ^ δ)
    (hlarge : ∀ x : EnergyColorFiber
      (classicalSeparatedBranchScaleColor σ T Y shiftedZero baseColor L hlocal)
        label,
      ClassicalBranchScaleLarge σ T D₁ Y X label.1 (shiftedZero x.1.1))
    (hsep : ∀ x y : EnergyColorFiber
      (classicalSeparatedBranchScaleColor σ T Y shiftedZero baseColor L hlocal)
        label,
      x ≠ y → 1 ≤ |shiftedZero x.1.1 - shiftedZero y.1.1|) :
    ∃ P : LargeValuePattern,
      let N := 2 ^ (r : ℕ) * X
      let D := C * (2 * N : ℝ) ^ η * (N : ℝ) ^ (-σ)
      P.N = (N : ℝ) ∧
      P.scale = N ∧
      P.T = (2 * T + T ^ δ) - (T - T ^ δ) ∧
      P.V = (((3 / 4) * (3 / 4)) / Nat.clog 2 Y) / D ∧
      finsetAdditiveEnergy P.ordinates =
        approximateAdditiveEnergyOf 1
          (fun x : EnergyColorFiber
            (classicalSeparatedBranchScaleColor σ T Y
              shiftedZero baseColor L hlocal) label => shiftedZero x.1.1) := by
  let N := 2 ^ (r : ℕ) * X
  let D : ℝ := C * (2 * N : ℝ) ^ η * (N : ℝ) ^ (-σ)
  let threshold : ℝ := (((3 / 4) * (3 / 4)) / Nat.clog 2 Y) / D
  let W := fun x : EnergyColorFiber
      (classicalSeparatedBranchScaleColor σ T Y shiftedZero baseColor L hlocal)
        label => shiftedZero x.1.1
  have hNpos : 0 < N := by omega
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hk : 0 < Nat.clog 2 Y := Nat.clog_pos Nat.one_lt_two hY
  have hkReal : (0 : ℝ) < Nat.clog 2 Y := by exact_mod_cast hk
  have hthreshold : 0 < threshold := by
    dsimp [threshold]
    positivity
  have hcoeff : ∀ n ∈ dyadicInterval N,
      ‖normalizedSharpMollifiedLineCoeff Y X N σ η C n‖ ≤ 1 := by
    intro n hn
    exact norm_normalizedSharpMollifiedLineCoeff_le_one Y X N n σ η C
      hNpos hσ hη hC hCoeff hn
  have hW : ∀ x, T - T ^ δ ≤ W x ∧ W x ≤ 2 * T + T ^ δ := by
    intro x
    exact hinterval x.1.1
  have hsepW : ∀ x y, x ≠ y → 1 ≤ |W x - W y| := hsep
  have hraw : ∀ x, ((3 / 4) * (3 / 4)) / Nat.clog 2 Y ≤
      ‖dirichletPoly N (sharpMollifiedLineCoeff Y X σ) (W x)‖ := by
    intro x
    have hx := hlarge x
    rw [hlabel] at hx
    simpa only [ClassicalBranchScaleLarge, ClassicalTypeIILargeAt, N, W] using hx
  have hlargeNorm : ∀ x, threshold ≤
      ‖dirichletPoly N
        (normalizedSharpMollifiedLineCoeff Y X N σ η C) (W x)‖ := by
    intro x
    rw [dirichletPoly_normalizedSharpMollifiedLineCoeff, norm_div,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD]
    exact div_le_div_of_nonneg_right (hraw x) hD.le
  have hab : T - T ^ δ < 2 * T + T ^ δ := by
    have hpow : 0 ≤ T ^ δ := Real.rpow_nonneg hT.le δ
    linarith
  let P := indexedDirichletLargeValuePattern N threshold
    (T - T ^ δ) (2 * T + T ^ δ)
    (normalizedSharpMollifiedLineCoeff Y X N σ η C) W hN hthreshold hab
    hcoeff hW hsepW hlargeNorm
  refine ⟨P, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · exact indexedDirichletLargeValuePattern_energy_eq N threshold
      (T - T ^ δ) (2 * T + T ^ δ)
      (normalizedSharpMollifiedLineCoeff Y X N σ η C) W hN hthreshold hab
      hcoeff hW hsepW hlargeNorm

/-- Native Type-II pattern packaging with the coefficient majorant discharged
by the proved uniform sharp-mollifier divisor bound. -/
theorem exists_classicalTypeIIClassPattern_native
    (δ σ T D₁ η : ℝ) (Y X L : ℕ)
    (shiftedZero : ↥(zerosInRect σ 1 T (2 * T)) → ℝ)
    (baseColor : ↥(zerosInRect σ 1 T (2 * T)) →
      ClassicalBranchScaleColor T Y)
    (hlocal : ∀ z : ℤ,
      (unitBinFinset
        (fun x : ClassicalSlabZeroCopy σ T => shiftedZero x.1) z).card ≤ L)
    (label : ClassicalSeparatedBranchScaleColor T Y L)
    (r : Fin (Nat.clog 2 Y))
    (hlabel : label.1 = some (Sum.inr r))
    (hT : 0 < T) (hY : 1 < Y)
    (hN : 1 < 2 ^ (r : ℕ) * X)
    (hσ : 0 ≤ σ) (hη : 0 < η)
    (hinterval : ∀ ρ : ↥(zerosInRect σ 1 T (2 * T)),
      T - T ^ δ ≤ shiftedZero ρ ∧
        shiftedZero ρ ≤ 2 * T + T ^ δ)
    (hlarge : ∀ x : EnergyColorFiber
      (classicalSeparatedBranchScaleColor σ T Y shiftedZero baseColor L hlocal)
        label,
      ClassicalBranchScaleLarge σ T D₁ Y X label.1 (shiftedZero x.1.1))
    (hsep : ∀ x y : EnergyColorFiber
      (classicalSeparatedBranchScaleColor σ T Y shiftedZero baseColor L hlocal)
        label,
      x ≠ y → 1 ≤ |shiftedZero x.1.1 - shiftedZero y.1.1|) :
    ∃ C : ℝ, 0 < C ∧ ∃ P : LargeValuePattern,
      let N := 2 ^ (r : ℕ) * X
      let D := C * (2 * N : ℝ) ^ η * (N : ℝ) ^ (-σ)
      P.N = (N : ℝ) ∧
      P.scale = N ∧
      P.T = (2 * T + T ^ δ) - (T - T ^ δ) ∧
      P.V = (((3 / 4) * (3 / 4)) / Nat.clog 2 Y) / D ∧
      finsetAdditiveEnergy P.ordinates =
        approximateAdditiveEnergyOf 1
          (fun x : EnergyColorFiber
            (classicalSeparatedBranchScaleColor σ T Y
              shiftedZero baseColor L hlocal) label => shiftedZero x.1.1) := by
  obtain ⟨C, hC, hCoeff⟩ := sharpMollifiedCoeff_bound η hη
  refine ⟨C, hC, ?_⟩
  exact exists_classicalTypeIIClassPattern δ σ T D₁ η C Y X L
    shiftedZero baseColor hlocal label r hlabel hT hY hN hσ hη.le hC
    (hCoeff Y X) hinterval hlarge hsep

/-- Complete multiplicity-safe classical branch-and-scale energy extraction.
Every one of the four selected classes is one-separated and has a single
genuine source branch and dyadic scale; all analytic-multiplicity copies are
retained, and beta removal incurs only the explicit tolerance factor. -/
theorem classicalSlabZeroEnergy_le_separated_branch_scale_class_energies
    (σ δ B₁ D₁ B₂ D₂ : ℝ)
    (hσ : 1 / 2 < σ) (hσUpper : σ ≤ 1) (hδ : 0 < δ) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧
      ∀ (T : ℝ) (Y X : ℕ), T₀ ≤ T →
        1 ≤ X → 1 < Y → X ≤ Y → Y ≤ ⌊sharpZetaCutoff T⌋₊ →
        (∀ ρ ∈ zerosInRect σ 1 T (2 * T),
          149 * sharpZetaCutoff T ^ (-ρ.re) ≤ T ^ (-D₁) / 2) →
        T ^ (-D₁) * (X : ℝ) ≤ 1 / 4 →
        finiteDirichletMass (classicalZetaLongTailSupport Y
            ⌊sharpZetaCutoff T⌋₊) (fun _n => 1) ≤ T ^ B₁ →
        T ^ (-D₁ - 1) ≤ T ^ (-D₁) / 2 →
        finiteDirichletMass (sharpMollifiedTailSupport Y X)
            (sharpMollifiedCoeff Y X) ≤ T ^ B₂ →
        T ^ (-D₂) ≤ 3 / 4 →
        let L := (2 * Nat.ceil (T ^ δ) + 1) *
          classicalLocalMultiplicityCap T
        ∃ (shiftedZero : ↥(zerosInRect σ 1 T (2 * T)) → ℝ)
          (baseColor : ↥(zerosInRect σ 1 T (2 * T)) →
            ClassicalBranchScaleColor T Y)
          (hlocal : ∀ z : ℤ,
            (unitBinFinset
              (fun x : ClassicalSlabZeroCopy σ T => shiftedZero x.1) z).card ≤ L)
          (label : Fin 4 → ClassicalSeparatedBranchScaleColor T Y L),
          (∀ ρ : ↥(zerosInRect σ 1 T (2 * T)),
            |(ρ : ℂ).im - shiftedZero ρ| ≤ T ^ δ) ∧
          (∀ ρ : ↥(zerosInRect σ 1 T (2 * T)),
            T - T ^ δ ≤ shiftedZero ρ ∧
            shiftedZero ρ ≤ 2 * T + T ^ δ) ∧
          (let shifted := fun x : ClassicalSlabZeroCopy σ T => shiftedZero x.1
           let color := classicalSeparatedBranchScaleColor σ T Y
             shiftedZero baseColor L hlocal
           let Wᵢ := fun i : Fin 4 =>
             fun x : EnergyColorFiber color (label i) => shifted x.1
           (∀ (i : Fin 4) (x : EnergyColorFiber color (label i)),
              ClassicalBranchScaleLarge σ T D₁ Y X
                (label i).1 (shifted x.1)) ∧
           (∀ (i : Fin 4) (x y : EnergyColorFiber color (label i)),
              x ≠ y → 1 ≤ |shifted x.1 - shifted y.1|) ∧
           4 * (classicalSlabZeroEnergy σ T : ℝ) ≤
             (4 * Nat.ceil (1 + 4 * T ^ δ) + 6 : ℝ) *
               (9 * (Fintype.card
                 (ClassicalSeparatedBranchScaleColor T Y L) : ℝ) ^ 4) *
                 ((approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
                   (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
                   (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
                   (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ))) := by
  obtain ⟨T₀, hT₀, hSelect⟩ :=
    classicalSlab_exists_shifted_branch_scale σ δ B₁ D₁ B₂ D₂
      hσ hσUpper hδ
  refine ⟨T₀, hT₀, ?_⟩
  intro T Y X hT hX hYStrict hXY hYA hError hShortProduct hMassI
    hThresholdI hMassII hThresholdII
  obtain ⟨shiftedZero, baseColor, hshiftZero, hinterval, hlargeZero⟩ :=
    hSelect T Y X hT hX hYStrict hXY hYA hError hShortProduct hMassI
      hThresholdI hMassII hThresholdII
  let shifted : ClassicalSlabZeroCopy σ T → ℝ := fun x => shiftedZero x.1
  let base : ClassicalSlabZeroCopy σ T → ClassicalBranchScaleColor T Y :=
    fun x => baseColor x.1
  let L := (2 * Nat.ceil (T ^ δ) + 1) * classicalLocalMultiplicityCap T
  have hTEight : 8 ≤ T := hT₀.trans hT
  have hunit : ∀ z : ℤ,
      ∑ ρ ∈ (zerosInRect σ 1 T (2 * T)).filter
        (fun ρ => (z : ℝ) ≤ ρ.im ∧ ρ.im < (z : ℝ) + 1),
        analyticVanishingOrder riemannZeta ρ ≤
          classicalLocalMultiplicityCap T := by
    intro z
    simpa only [zeroUnitBin] using
      zeroUnitBin_multiplicity_le_cap σ T z hσ.le hTEight
  have hlocal : ∀ z : ℤ, (unitBinFinset shifted z).card ≤ L := by
    intro z
    exact classicalSlabZeroCopy_shifted_unitBin_card_le σ T (T ^ δ)
      (classicalLocalMultiplicityCap T) shiftedZero hshiftZero hunit z
  obtain ⟨label, henergy, hbase, hseparated⟩ :=
    exists_separated_energy_color_classes shifted base L hlocal
  refine ⟨shiftedZero, baseColor, hlocal, label, hshiftZero, hinterval,
    ?_, ?_, ?_⟩
  · intro i x
    have hcolor : baseColor x.1.1 = (label i).1 := hbase i x
    rw [← hcolor]
    exact hlargeZero x.1.1
  · exact hseparated
  · let Wᵢ := fun i : Fin 4 =>
      fun x : EnergyColorFiber
        (classicalSeparatedBranchScaleColor σ T Y shiftedZero baseColor L hlocal)
          (label i) => shifted x.1
    have hzeroNat : classicalSlabZeroEnergy σ T ≤
        (4 * Nat.ceil (1 + 4 * T ^ δ) + 6) *
          approximateAdditiveEnergyOf 1 shifted := by
      exact classicalSlabZeroEnergy_le_shifted_unit σ T (T ^ δ) shifted
        (fun x => by
          simpa only [shifted, abs_sub_comm] using hshiftZero x.1)
    have hzero : (classicalSlabZeroEnergy σ T : ℝ) ≤
        (4 * Nat.ceil (1 + 4 * T ^ δ) + 6 : ℕ) *
          (approximateAdditiveEnergyOf 1 shifted : ℝ) := by
      exact_mod_cast hzeroNat
    change 4 * (classicalSlabZeroEnergy σ T : ℝ) ≤ _
    calc
      4 * (classicalSlabZeroEnergy σ T : ℝ) ≤
          4 * ((4 * Nat.ceil (1 + 4 * T ^ δ) + 6 : ℕ) *
            (approximateAdditiveEnergyOf 1 shifted : ℝ)) := by gcongr
      _ = (4 * Nat.ceil (1 + 4 * T ^ δ) + 6 : ℝ) *
          (4 * (approximateAdditiveEnergyOf 1 shifted : ℝ)) := by
        push_cast
        ring
      _ ≤ (4 * Nat.ceil (1 + 4 * T ^ δ) + 6 : ℝ) *
          (9 * (Fintype.card
            (ClassicalSeparatedBranchScaleColor T Y L) : ℝ) ^ 4 *
              ((approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
                (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
                (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
                (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [Wᵢ, classicalSeparatedBranchScaleColor, shifted, base] using
          henergy
      _ = (4 * Nat.ceil (1 + 4 * T ^ δ) + 6 : ℝ) *
          (9 * (Fintype.card
            (ClassicalSeparatedBranchScaleColor T Y L) : ℝ) ^ 4) *
              ((approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
                (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
                (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
                (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ)) := by ring

end TaoTrudgianYang2025
