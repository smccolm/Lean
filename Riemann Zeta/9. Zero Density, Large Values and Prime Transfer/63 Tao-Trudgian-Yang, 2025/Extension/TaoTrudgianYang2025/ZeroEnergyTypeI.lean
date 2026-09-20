import TaoTrudgianYang2025.EnergySeparation
import GuthMaynard.BetaDependence

/-!
# Multiplicity-safe Type-I zero perturbations

This module lifts the native Guth--Maynard beta-removal theorem from distinct
zeros to an index type containing one copy for every analytic multiplicity.
It then applies the generic perturbation and tolerance-normalization theorems
without quotienting equal ordinates.
-/

open Complex

noncomputable section

namespace TaoTrudgianYang2025

open RiemannZeta.GuthMaynard

/-- A Type-I zero in the positive dyadic slab, together with one index for
each copy counted by its analytic vanishing order. -/
abbrev TypeIZeroCopy (σ T : ℝ) :=
  Σ ρ : ↥(typeIZeroSet σ T),
    Fin (analyticVanishingOrder riemannZeta (ρ : ℂ))

/-- Unit-tolerance energy of the Type-I zero copies in the positive dyadic
slab. -/
def typeIZeroAdditiveEnergy (σ T : ℝ) : ℕ :=
  approximateAdditiveEnergyOf 1
    (fun z : TypeIZeroCopy σ T => ((z.1.1 : ℂ).im : ℝ))

/-- Extend a shift defined on the Type-I zero subtype to all complex
numbers.  Values outside the finite Type-I set are irrelevant. -/
def extendTypeIShift (σ T : ℝ)
    (shift : ↥(typeIZeroSet σ T) → ℝ) : ℂ → ℝ :=
  fun ρ => if hρ : ρ ∈ typeIZeroSet σ T then shift ⟨ρ, hρ⟩ else 0

@[simp] theorem extendTypeIShift_apply (σ T : ℝ)
    (shift : ↥(typeIZeroSet σ T) → ℝ)
    (ρ : ↥(typeIZeroSet σ T)) :
    extendTypeIShift σ T shift ρ = shift ρ := by
  simp [extendTypeIShift, ρ.2]

/-- The number of multiplicity copies in a shifted unit bin is the weighted
sum over the underlying distinct Type-I zeros. -/
theorem typeIZeroCopy_shifted_unitBin_card
    (σ T : ℝ) (shift : ↥(typeIZeroSet σ T) → ℝ) (z : ℤ) :
    (unitBinFinset (fun x : TypeIZeroCopy σ T => shift x.1) z).card =
      ∑ ρ ∈ (typeIZeroSet σ T).filter
        (fun ρ => (z : ℝ) ≤ extendTypeIShift σ T shift ρ ∧
          extendTypeIShift σ T shift ρ < (z : ℝ) + 1),
        analyticVanishingOrder riemannZeta ρ := by
  classical
  let pred : ℂ → Prop := fun ρ =>
    ρ ∈ typeIZeroSet σ T ∧
      (z : ℝ) ≤ extendTypeIShift σ T shift ρ ∧
      extendTypeIShift σ T shift ρ < (z : ℝ) + 1
  letI : Fintype {ρ : ℂ // pred ρ} :=
    Fintype.ofFinset ((typeIZeroSet σ T).filter fun ρ =>
      (z : ℝ) ≤ extendTypeIShift σ T shift ρ ∧
      extendTypeIShift σ T shift ρ < (z : ℝ) + 1) (by
        intro ρ
        rw [Finset.mem_filter]
        rfl)
  change ((Finset.univ : Finset (TypeIZeroCopy σ T)).filter
    (fun x => ⌊shift x.1⌋ = z)).card = _
  rw [← Fintype.card_subtype]
  let e : {x : TypeIZeroCopy σ T // ⌊shift x.1⌋ = z} ≃
      Σ ρ : {ρ : ℂ // pred ρ},
        Fin (analyticVanishingOrder riemannZeta (ρ : ℂ)) :=
    { toFun := fun x =>
        ⟨⟨x.1.1.1, x.1.1.2, by
          simpa only [extendTypeIShift_apply] using
            (Int.floor_eq_iff.mp x.2)⟩, x.1.2⟩
      invFun := fun x =>
        ⟨⟨⟨x.1.1, x.1.2.1⟩, x.2⟩, by
          apply Int.floor_eq_iff.mpr
          simpa only [extendTypeIShift, dif_pos x.1.2.1] using x.1.2.2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact (Finset.sum_subtype
    ((typeIZeroSet σ T).filter fun ρ =>
      (z : ℝ) ≤ extendTypeIShift σ T shift ρ ∧
      extendTypeIShift σ T shift ρ < (z : ℝ) + 1)
    (fun ρ => by simp [pred])
    (fun ρ : ℂ => analyticVanishingOrder riemannZeta ρ)).symm

/-- A displacement bound transfers the native weighted unit-bin estimate to
the multiplicity-copy index type. -/
theorem typeIZeroCopy_shifted_unitBin_card_le
    (σ T H : ℝ) (L₀ : ℕ)
    (shift : ↥(typeIZeroSet σ T) → ℝ)
    (hshift : ∀ ρ : ↥(typeIZeroSet σ T),
      |(ρ : ℂ).im - shift ρ| ≤ H)
    (hlocal : ∀ z : ℤ,
      ∑ ρ ∈ (typeIZeroSet σ T).filter
        (fun ρ => (z : ℝ) ≤ ρ.im ∧ ρ.im < (z : ℝ) + 1),
        analyticVanishingOrder riemannZeta ρ ≤ L₀) :
    ∀ z : ℤ,
      (unitBinFinset (fun x : TypeIZeroCopy σ T => shift x.1) z).card ≤
        (2 * Nat.ceil H + 1) * L₀ := by
  classical
  intro z
  rw [typeIZeroCopy_shifted_unitBin_card]
  have hnative := shifted_bin_weight_le_of_unit_bin_weight
    (typeIZeroSet σ T) (analyticVanishingOrder riemannZeta)
    Complex.im (extendTypeIShift σ T shift) H L₀
    (fun ρ hρ => by
      simpa only [extendTypeIShift, dif_pos hρ] using hshift ⟨ρ, hρ⟩)
    hlocal z
  let A := (typeIZeroSet σ T).filter
    (fun ρ => (z : ℝ) ≤ extendTypeIShift σ T shift ρ ∧
      extendTypeIShift σ T shift ρ < (z : ℝ) + 1)
  have hfiber := Finset.sum_fiberwise_eq_sum_filter
    (typeIZeroSet σ T)
    (((typeIZeroSet σ T).image (extendTypeIShift σ T shift)).filter
      (fun t => (z : ℝ) ≤ t ∧ t < (z : ℝ) + 1))
    (extendTypeIShift σ T shift) (analyticVanishingOrder riemannZeta)
  have hfilter : (typeIZeroSet σ T).filter
      (fun ρ => extendTypeIShift σ T shift ρ ∈
        ((typeIZeroSet σ T).image (extendTypeIShift σ T shift)).filter
          (fun t => (z : ℝ) ≤ t ∧ t < (z : ℝ) + 1)) = A := by
    apply Finset.filter_congr
    intro ρ hρ
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨⟨ρ, hρ, rfl⟩, h⟩
  rw [hfilter] at hfiber
  change (∑ ρ ∈ A, analyticVanishingOrder riemannZeta ρ) ≤ _
  rw [← hfiber]
  exact hnative

/-- The Type-I copy type has exactly the analytic-multiplicity-weighted
cardinality of the underlying Type-I zero set. -/
theorem typeIZeroCopy_card (σ T : ℝ) :
    Fintype.card (TypeIZeroCopy σ T) =
      ∑ ρ ∈ typeIZeroSet σ T,
        analyticVanishingOrder riemannZeta ρ := by
  simp only [Fintype.card_sigma, Fintype.card_fin]
  exact Finset.sum_attach (typeIZeroSet σ T)
    (fun ρ => analyticVanishingOrder riemannZeta ρ)

/-- Native beta removal with one chosen shifted ordinate for each underlying
distinct Type-I zero.  All analytic-multiplicity copies of a zero therefore
inherit the same shift. -/
theorem typeIZero_exists_shifted_detector
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ T₀ : ℝ, Real.exp 2 ≤ T₀ ∧
      ∀ (σ T : ℝ), 7 / 10 ≤ σ → σ ≤ 4 / 5 → T₀ ≤ T →
        ∃ shifted : ↥(typeIZeroSet σ T) → ℝ,
          (∀ ρ : ↥(typeIZeroSet σ T),
            |(ρ : ℂ).im - shifted ρ| ≤ T ^ δ) ∧
          (∀ ρ : ↥(typeIZeroSet σ T), 1 / (4 * Real.log T) ≤
            ‖detectPoly (2 ^ chosenTypeIScale ρ T)
              (σ + I * shifted ρ) T‖) := by
  obtain ⟨T₀, hT₀, hBeta⟩ := beta_dependence_removal δ hδ
  refine ⟨T₀, hT₀, ?_⟩
  intro σ T hσLower hσUpper hT
  have hpoint : ∀ ρ : ↥(typeIZeroSet σ T),
      ∃ γ' : ℝ,
        |(ρ : ℂ).im - γ'| ≤ T ^ δ ∧
        1 / (4 * Real.log T) ≤
          ‖detectPoly (2 ^ chosenTypeIScale ρ T)
            (σ + I * γ') T‖ := by
    intro ρ
    exact hBeta σ T hσLower hσUpper hT ρ ρ.2
  choose shifted hshift hlarge using hpoint
  exact ⟨shifted, hshift, hlarge⟩

/-- Native beta removal lifted pointwise to all analytic-multiplicity copies.
The chosen ordinate and detector scale may depend on the copy's underlying
zero, but copies are never collapsed. -/
theorem typeIZeroCopy_exists_shifted_detector
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ T₀ : ℝ, Real.exp 2 ≤ T₀ ∧
      ∀ (σ T : ℝ), 7 / 10 ≤ σ → σ ≤ 4 / 5 → T₀ ≤ T →
        ∃ shifted : TypeIZeroCopy σ T → ℝ,
          (∀ z, |(z.1.1 : ℂ).im - shifted z| ≤ T ^ δ) ∧
          (∀ z, 1 / (4 * Real.log T) ≤
            ‖detectPoly (2 ^ chosenTypeIScale z.1.1 T)
              (σ + I * shifted z) T‖) := by
  obtain ⟨T₀, hT₀, hBeta⟩ := typeIZero_exists_shifted_detector δ hδ
  refine ⟨T₀, hT₀, ?_⟩
  intro σ T hσLower hσUpper hT
  obtain ⟨shiftedZero, hshift, hlarge⟩ :=
    hBeta σ T hσLower hσUpper hT
  exact ⟨fun z => shiftedZero z.1, fun z => hshift z.1,
    fun z => hlarge z.1⟩

/-- Type-I zero energy is controlled by the unit-tolerance energy of the
native fixed-line detector ordinates, with an explicit subpower-compatible
tolerance cost and exact analytic multiplicity. -/
theorem typeIZeroAdditiveEnergy_le_shifted_detector_energy
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ T₀ : ℝ, Real.exp 2 ≤ T₀ ∧
      ∀ (σ T : ℝ), 7 / 10 ≤ σ → σ ≤ 4 / 5 → T₀ ≤ T →
        ∃ shifted : TypeIZeroCopy σ T → ℝ,
          (∀ z, |(z.1.1 : ℂ).im - shifted z| ≤ T ^ δ) ∧
          (∀ z, 1 / (4 * Real.log T) ≤
            ‖detectPoly (2 ^ chosenTypeIScale z.1.1 T)
              (σ + I * shifted z) T‖) ∧
          typeIZeroAdditiveEnergy σ T ≤
            (4 * Nat.ceil (1 + 4 * T ^ δ) + 6) *
              approximateAdditiveEnergyOf 1 shifted := by
  obtain ⟨T₀, hT₀, hShifted⟩ :=
    typeIZeroCopy_exists_shifted_detector δ hδ
  refine ⟨T₀, hT₀, ?_⟩
  intro σ T hσLower hσUpper hT
  obtain ⟨shifted, hshift, hlarge⟩ :=
    hShifted σ T hσLower hσUpper hT
  refine ⟨shifted, hshift, hlarge, ?_⟩
  exact (approximateAdditiveEnergyOf_perturbation_le
    (W := fun z : TypeIZeroCopy σ T => ((z.1.1 : ℂ).im : ℝ))
    (W' := shifted) (r := 1) (d := T ^ δ) (fun z => by
      simpa [abs_sub_comm] using hshift z)).trans
    (approximateAdditiveEnergyOf_le_natCeil_mul_unit
      (1 + 4 * T ^ δ) shifted)

/-- A finite color recording the native admissible detector scale.  The
`none` color makes the type inhabited even when the admissible-scale finset is
empty; actual Type-I copies always receive `some`. -/
abbrev TypeIScaleColor (T : ℝ) := Option ↥(admissibleDyadicIndices T)

noncomputable def typeIScaleColor (σ T : ℝ) (z : TypeIZeroCopy σ T) :
    TypeIScaleColor T := by
  classical
  exact some ⟨chosenTypeIScale z.1.1 T,
    chosenTypeIScale_mem z.1.1 T (Finset.mem_filter.mp z.1.2).2⟩

/-- Read the natural scale index from a Type-I scale color.  The fallback
value is unreachable on every nonempty color fiber produced below. -/
def typeIScaleColorIndex {T : ℝ} : TypeIScaleColor T → ℕ
  | none => 0
  | some j => j.1

/-- A fixed classical order used only to assign deterministic ranks inside
unit bins.  It carries no analytic content. -/
noncomputable instance typeIZeroCopyLinearOrder (σ T : ℝ) :
    LinearOrder (TypeIZeroCopy σ T) :=
  WellOrderingRel.isWellOrder.linearOrder

/-- Detector scale refined by the unit-bin separation color. -/
abbrev TypeISeparatedScaleColor (T : ℝ) (L : ℕ) :=
  TypeIScaleColor T × (ZMod 2 × Fin (L + 1))

noncomputable def typeISeparatedScaleColor
    (σ T : ℝ) (shifted : TypeIZeroCopy σ T → ℝ) (L : ℕ)
    (hlocal : ∀ z : ℤ, (unitBinFinset shifted z).card ≤ L) :
    TypeIZeroCopy σ T → TypeISeparatedScaleColor T L :=
  separatedRefinementColor shifted (typeIScaleColor σ T) L hlocal

/-- Every inhabited refined color fiber carries an actual admissible native
detector scale; the fallback `none` color is unreachable. -/
theorem typeISeparatedScaleColor_index_mem
    (σ T : ℝ) (shifted : TypeIZeroCopy σ T → ℝ) (L : ℕ)
    (hlocal : ∀ z : ℤ, (unitBinFinset shifted z).card ≤ L)
    (label : TypeISeparatedScaleColor T L)
    (x : EnergyColorFiber
      (typeISeparatedScaleColor σ T shifted L hlocal) label) :
    typeIScaleColorIndex label.1 ∈ admissibleDyadicIndices T := by
  classical
  have hbase : typeIScaleColor σ T x.1 = label.1 :=
    separatedRefinementColor_base shifted (typeIScaleColor σ T) L hlocal x.2
  rw [← hbase]
  simp only [typeIScaleColor, typeIScaleColorIndex]
  exact chosenTypeIScale_mem x.1.1.1 T (Finset.mem_filter.mp x.1.1.2).2

/-- The four-coordinate energy coloring specialized to the actual native
Type-I detector scale.  Every member of each selected color class satisfies
the detector bound at the single scale encoded by that class, while indexed
multiplicity is retained exactly. -/
theorem typeIZeroShiftedEnergy_exists_scale_classes
    (σ T L : ℝ) (shifted : TypeIZeroCopy σ T → ℝ)
    (hlarge : ∀ z, L ≤
      ‖detectPoly (2 ^ chosenTypeIScale z.1.1 T)
        (σ + I * shifted z) T‖) :
    ∃ label : Fin 4 → TypeIScaleColor T,
      let Wᵢ := fun i : Fin 4 =>
        fun x : EnergyColorFiber (typeIScaleColor σ T) (label i) => shifted x.1
      4 * (approximateAdditiveEnergyOf 1 shifted : ℝ) ≤
          9 * (Fintype.card (TypeIScaleColor T) : ℝ) ^ 4 *
            ((approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ)) ∧
        ∀ (i : Fin 4)
          (x : EnergyColorFiber (typeIScaleColor σ T) (label i)),
          L ≤ ‖detectPoly (2 ^ typeIScaleColorIndex (label i))
            (σ + I * shifted x.1) T‖ := by
  obtain ⟨label, henergy⟩ :=
    exists_energy_color_classes shifted (typeIScaleColor σ T)
  refine ⟨label, henergy, ?_⟩
  intro i x
  have hx : typeIScaleColor σ T x.1 = label i := x.2
  have hindex : chosenTypeIScale x.1.1.1 T =
      typeIScaleColorIndex (label i) := by
    have hi := congrArg typeIScaleColorIndex hx
    change chosenTypeIScale x.1.1.1 T = typeIScaleColorIndex (label i) at hi
    exact hi
  simpa only [hindex] using hlarge x.1

/-- Refine the detector-scale coloring by the explicit local-rank coloring.
The resulting four indexed classes retain the complete energy estimate, use
one detector scale per class, and are genuinely one-separated. -/
theorem typeIZeroShiftedEnergy_exists_separated_scale_classes
    (σ T threshold : ℝ) (shifted : TypeIZeroCopy σ T → ℝ) (L : ℕ)
    (hlocal : ∀ z : ℤ, (unitBinFinset shifted z).card ≤ L)
    (hlarge : ∀ x, threshold ≤
      ‖detectPoly (2 ^ chosenTypeIScale x.1.1 T)
        (σ + I * shifted x) T‖) :
    ∃ label : Fin 4 → TypeISeparatedScaleColor T L,
      let Wᵢ := fun i : Fin 4 =>
        fun x : EnergyColorFiber
          (typeISeparatedScaleColor σ T shifted L hlocal) (label i) =>
            shifted x.1
      4 * (approximateAdditiveEnergyOf 1 shifted : ℝ) ≤
          9 * (Fintype.card (TypeISeparatedScaleColor T L) : ℝ) ^ 4 *
            ((approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ)) ∧
        (∀ (i : Fin 4)
          (x : EnergyColorFiber
            (typeISeparatedScaleColor σ T shifted L hlocal) (label i)),
          threshold ≤ ‖detectPoly (2 ^ typeIScaleColorIndex (label i).1)
            (σ + I * shifted x.1) T‖) ∧
        (∀ (i : Fin 4)
          (x y : EnergyColorFiber
            (typeISeparatedScaleColor σ T shifted L hlocal) (label i)),
          x ≠ y → 1 ≤ |shifted x.1 - shifted y.1|) := by
  classical
  obtain ⟨label, henergy⟩ := exists_energy_color_classes shifted
    (typeISeparatedScaleColor σ T shifted L hlocal)
  refine ⟨label, henergy, ?_, ?_⟩
  · intro i x
    have hscale : typeIScaleColor σ T x.1 = (label i).1 :=
      separatedRefinementColor_base shifted (typeIScaleColor σ T) L hlocal x.2
    have hindex : chosenTypeIScale x.1.1.1 T =
        typeIScaleColorIndex (label i).1 := by
      have hi := congrArg typeIScaleColorIndex hscale
      change chosenTypeIScale x.1.1.1 T =
        typeIScaleColorIndex (label i).1 at hi
      exact hi
    simpa only [hindex] using hlarge x.1
  · intro i x y hxy
    exact separatedRefinementColor_oneSeparated shifted
      (typeIScaleColor σ T) L hlocal (label i) x y hxy

/-- Complete finite Type-I energy reduction: actual multiplicity-weighted zero
energy is bounded by four single-scale detector-class energies.  The displayed
losses are the explicit perturbation/tolerance factor and the fourth power of
the finite admissible-scale count. -/
theorem typeIZeroAdditiveEnergy_le_detector_scale_class_energies
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ T₀ : ℝ, Real.exp 2 ≤ T₀ ∧
      ∀ (σ T : ℝ), 7 / 10 ≤ σ → σ ≤ 4 / 5 → T₀ ≤ T →
        ∃ (shifted : TypeIZeroCopy σ T → ℝ)
          (label : Fin 4 → TypeIScaleColor T),
          (∀ z, |(z.1.1 : ℂ).im - shifted z| ≤ T ^ δ) ∧
          (let Wᵢ := fun i : Fin 4 =>
              fun x : EnergyColorFiber (typeIScaleColor σ T) (label i) =>
                shifted x.1;
            (∀ (i : Fin 4)
              (x : EnergyColorFiber (typeIScaleColor σ T) (label i)),
              1 / (4 * Real.log T) ≤
                ‖detectPoly (2 ^ typeIScaleColorIndex (label i))
                  (σ + I * shifted x.1) T‖) ∧
            4 * (typeIZeroAdditiveEnergy σ T : ℝ) ≤
              (4 * Nat.ceil (1 + 4 * T ^ δ) + 6 : ℝ) *
                (9 * (Fintype.card (TypeIScaleColor T) : ℝ) ^ 4) *
                  ((approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
                    (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
                    (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
                    (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ))) := by
  obtain ⟨T₀, hT₀, hshifted⟩ :=
    typeIZeroAdditiveEnergy_le_shifted_detector_energy δ hδ
  refine ⟨T₀, hT₀, ?_⟩
  intro σ T hσLower hσUpper hT
  obtain ⟨shifted, hshift, hlarge, hzeroNat⟩ :=
    hshifted σ T hσLower hσUpper hT
  obtain ⟨label, hclasses, hclassLarge⟩ :=
    typeIZeroShiftedEnergy_exists_scale_classes σ T
      (1 / (4 * Real.log T)) shifted hlarge
  refine ⟨shifted, label, hshift, hclassLarge, ?_⟩
  let Wᵢ := fun i : Fin 4 =>
    fun x : EnergyColorFiber (typeIScaleColor σ T) (label i) => shifted x.1
  have hzero : (typeIZeroAdditiveEnergy σ T : ℝ) ≤
      (4 * Nat.ceil (1 + 4 * T ^ δ) + 6 : ℕ) *
        (approximateAdditiveEnergyOf 1 shifted : ℝ) := by
    exact_mod_cast hzeroNat
  change 4 * (typeIZeroAdditiveEnergy σ T : ℝ) ≤ _
  calc
    4 * (typeIZeroAdditiveEnergy σ T : ℝ) ≤
        4 * ((4 * Nat.ceil (1 + 4 * T ^ δ) + 6 : ℕ) *
          (approximateAdditiveEnergyOf 1 shifted : ℝ)) := by gcongr
    _ = (4 * Nat.ceil (1 + 4 * T ^ δ) + 6 : ℝ) *
        (4 * (approximateAdditiveEnergyOf 1 shifted : ℝ)) := by
      push_cast
      ring
    _ ≤ (4 * Nat.ceil (1 + 4 * T ^ δ) + 6 : ℝ) *
        (9 * (Fintype.card (TypeIScaleColor T) : ℝ) ^ 4 *
          ((approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
            (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
            (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
            (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ))) := by
      gcongr
    _ = (4 * Nat.ceil (1 + 4 * T ^ δ) + 6 : ℝ) *
        (9 * (Fintype.card (TypeIScaleColor T) : ℝ) ^ 4) *
          ((approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
            (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
            (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
            (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ)) := by ring

/-- Complete finite Type-I reduction through one-separated detector classes.
The local Jensen estimate controls the extra rank colors by an explicit
shifted-bin factor, while beta removal and scale coloring retain every
analytic-multiplicity copy. -/
theorem typeIZeroAdditiveEnergy_le_separated_detector_scale_class_energies
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C T₀ : ℝ, 0 < C ∧ Real.exp 2 ≤ T₀ ∧
      ∀ (σ T : ℝ), 7 / 10 ≤ σ → σ ≤ 4 / 5 → T₀ ≤ T →
        ∃ (shiftedZero : ↥(typeIZeroSet σ T) → ℝ) (L₀ : ℕ)
          (hlocal : ∀ z : ℤ,
            (unitBinFinset
              (fun x : TypeIZeroCopy σ T => shiftedZero x.1) z).card ≤
                (2 * Nat.ceil (T ^ δ) + 1) * L₀)
          (label : Fin 4 → TypeISeparatedScaleColor T
            ((2 * Nat.ceil (T ^ δ) + 1) * L₀)),
          (L₀ : ℝ) ≤ C * Real.log T ∧
          (∀ x : TypeIZeroCopy σ T,
            |(x.1.1 : ℂ).im - shiftedZero x.1| ≤ T ^ δ) ∧
          (let shifted := fun x : TypeIZeroCopy σ T => shiftedZero x.1
           let color := typeISeparatedScaleColor σ T shifted
             ((2 * Nat.ceil (T ^ δ) + 1) * L₀) hlocal
           let Wᵢ := fun i : Fin 4 =>
             fun x : EnergyColorFiber color (label i) => shifted x.1
           (∀ (i : Fin 4) (x : EnergyColorFiber color (label i)),
              1 / (4 * Real.log T) ≤
                ‖detectPoly (2 ^ typeIScaleColorIndex (label i).1)
                  (σ + I * shifted x.1) T‖) ∧
           (∀ (i : Fin 4) (x y : EnergyColorFiber color (label i)),
              x ≠ y → 1 ≤ |shifted x.1 - shifted y.1|) ∧
           4 * (typeIZeroAdditiveEnergy σ T : ℝ) ≤
             (4 * Nat.ceil (1 + 4 * T ^ δ) + 6 : ℝ) *
               (9 * (Fintype.card
                 (TypeISeparatedScaleColor T
                   ((2 * Nat.ceil (T ^ δ) + 1) * L₀)) : ℝ) ^ 4) *
                 ((approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
                   (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
                   (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
                   (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ))) := by
  obtain ⟨Tβ, hTβ, hBeta⟩ := typeIZero_exists_shifted_detector δ hδ
  obtain ⟨C, TL, hC, hTL, hLocal⟩ := localZeroMultiplicityBound_native
  refine ⟨C, max Tβ TL, hC, le_max_of_le_left hTβ, ?_⟩
  intro σ T hσLower hσUpper hT
  have hTβT : Tβ ≤ T := (le_max_left Tβ TL).trans hT
  have hTLT : TL ≤ T := (le_max_right Tβ TL).trans hT
  obtain ⟨shiftedZero, hshiftZero, hlargeZero⟩ :=
    hBeta σ T hσLower hσUpper hTβT
  obtain ⟨L₀, hL₀, hunit⟩ :=
    hLocal σ T hσLower hσUpper hTLT
  let shifted : TypeIZeroCopy σ T → ℝ := fun x => shiftedZero x.1
  let L : ℕ := (2 * Nat.ceil (T ^ δ) + 1) * L₀
  have hlocal : ∀ z : ℤ, (unitBinFinset shifted z).card ≤ L := by
    intro z
    exact typeIZeroCopy_shifted_unitBin_card_le σ T (T ^ δ) L₀
      shiftedZero hshiftZero hunit z
  have hlarge : ∀ x : TypeIZeroCopy σ T,
      1 / (4 * Real.log T) ≤
        ‖detectPoly (2 ^ chosenTypeIScale x.1.1 T)
          (σ + I * shifted x) T‖ := fun x => hlargeZero x.1
  obtain ⟨label, hclasses, hclassLarge, hseparated⟩ :=
    typeIZeroShiftedEnergy_exists_separated_scale_classes σ T
      (1 / (4 * Real.log T)) shifted L hlocal hlarge
  refine ⟨shiftedZero, L₀, hlocal, label, hL₀, ?_, ?_, ?_, ?_⟩
  · exact fun x => hshiftZero x.1
  · exact hclassLarge
  · exact hseparated
  · let Wᵢ := fun i : Fin 4 =>
      fun x : EnergyColorFiber
        (typeISeparatedScaleColor σ T shifted L hlocal) (label i) => shifted x.1
    have hzeroNat : typeIZeroAdditiveEnergy σ T ≤
        (4 * Nat.ceil (1 + 4 * T ^ δ) + 6) *
          approximateAdditiveEnergyOf 1 shifted := by
      exact (approximateAdditiveEnergyOf_perturbation_le
        (W := fun x : TypeIZeroCopy σ T => ((x.1.1 : ℂ).im : ℝ))
        (W' := shifted) (r := 1) (d := T ^ δ) (fun x => by
          simpa [shifted, abs_sub_comm] using hshiftZero x.1)).trans
        (approximateAdditiveEnergyOf_le_natCeil_mul_unit
          (1 + 4 * T ^ δ) shifted)
    have hzero : (typeIZeroAdditiveEnergy σ T : ℝ) ≤
        (4 * Nat.ceil (1 + 4 * T ^ δ) + 6 : ℕ) *
          (approximateAdditiveEnergyOf 1 shifted : ℝ) := by
      exact_mod_cast hzeroNat
    change 4 * (typeIZeroAdditiveEnergy σ T : ℝ) ≤ _
    calc
      4 * (typeIZeroAdditiveEnergy σ T : ℝ) ≤
          4 * ((4 * Nat.ceil (1 + 4 * T ^ δ) + 6 : ℕ) *
            (approximateAdditiveEnergyOf 1 shifted : ℝ)) := by gcongr
      _ = (4 * Nat.ceil (1 + 4 * T ^ δ) + 6 : ℝ) *
          (4 * (approximateAdditiveEnergyOf 1 shifted : ℝ)) := by
        push_cast
        ring
      _ ≤ (4 * Nat.ceil (1 + 4 * T ^ δ) + 6 : ℝ) *
          (9 * (Fintype.card (TypeISeparatedScaleColor T L) : ℝ) ^ 4 *
            ((approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ))) := by
        gcongr
      _ = (4 * Nat.ceil (1 + 4 * T ^ δ) + 6 : ℝ) *
          (9 * (Fintype.card (TypeISeparatedScaleColor T L) : ℝ) ^ 4) *
            ((approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
              (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ)) := by ring

end TaoTrudgianYang2025
