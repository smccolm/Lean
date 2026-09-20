import TaoTrudgianYang2025.ClassicalTypeIIEnergyTransfer
import TaoTrudgianYang2025.ZeroEnergyMultiplicity

/-!
# Classical slab energy assembly

The multiplicity-preserving source extraction has explicit tolerance and
coloring losses. This module controls those losses in the physical height.
-/

noncomputable section

namespace TaoTrudgianYang2025

open RiemannZeta.GuthMaynard

/-- Complete outer loss in the multiplicity-preserving branch/scale split.
The local multiplicity cap is the actual proved zero-count cap. -/
def classicalSlabEnergyLoss (T θ : ℝ) (Y : ℕ) : ℝ :=
  let L := (2 * Nat.ceil (T ^ θ) + 1) * classicalLocalMultiplicityCap T
  (4 * Nat.ceil (1 + 4 * T ^ θ) + 6) *
    (9 * (Fintype.card (ClassicalSeparatedBranchScaleColor T Y L) : ℝ) ^ 4)

/-- The outer source extraction loss has at most thirteen displacement
powers, uniformly in the actual short cutoff. Both logarithmic dyadic counts
and the proved analytic-multiplicity cap are absorbed explicitly. -/
theorem eventually_classicalSlabEnergyLoss_le_const_mul_rpow
    (θ : ℝ) (hθ : 0 < θ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in Filter.atTop, ∀ Y : ℕ,
      Y ≤ ⌊sharpZetaCutoff T⌋₊ →
      classicalSlabEnergyLoss T θ Y ≤ K * T ^ (13 * θ) := by
  obtain ⟨c, hc, hcap⟩ := localMultiplicityCap_le_rpow hθ
  let K : ℝ := 349920 * (5 * c + 1) ^ 4
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  filter_upwards [eventually_const_mul_classicalTypeI_clog_le_rpow 1 θ
    (by norm_num) hθ, Filter.eventually_ge_atTop (8 : ℝ)] with T hclog hT
  intro Y hYA
  have hTpos : 0 < T := by linarith
  let q := T ^ θ
  have hq : 1 ≤ q := Real.one_le_rpow (by linarith) hθ.le
  have hqpos : 0 < q := by linarith
  have hclogA : (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ : ℝ) ≤ q := by
    simpa only [one_mul] using hclog
  have hclogY : (Nat.clog 2 Y : ℝ) ≤ q :=
    (show (Nat.clog 2 Y : ℝ) ≤ Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ by
      exact_mod_cast Nat.clog_mono_right 2 hYA).trans hclogA
  let L := (2 * Nat.ceil (T ^ θ) + 1) * classicalLocalMultiplicityCap T
  have hceil : (Nat.ceil q : ℝ) ≤ q + 1 := (Nat.ceil_lt_add_one hqpos.le).le
  have hL : (L : ℝ) ≤ 5 * c * q ^ 2 := by
    calc
      (L : ℝ) = (2 * (Nat.ceil q : ℝ) + 1) *
          (classicalLocalMultiplicityCap T : ℝ) := by
        simp only [L, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, q]
      _ ≤ (5 * q) * (c * q) := by
        apply mul_le_mul
        · linarith
        · exact hcap T hT
        · exact Nat.cast_nonneg _
        · positivity
      _ = 5 * c * q ^ 2 := by ring
  have hLp : ((L + 1 : ℕ) : ℝ) ≤ (5 * c + 1) * q ^ 2 := by
    push_cast
    nlinarith
  have hbase : (Fintype.card (ClassicalBranchScaleColor T Y) : ℝ) ≤ 3 * q := by
    simp only [ClassicalBranchScaleColor, Fintype.card_option, Fintype.card_sum,
      Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    linarith
  have hcolors : (Fintype.card (ClassicalSeparatedBranchScaleColor T Y L) : ℝ) ≤
      6 * (5 * c + 1) * q ^ 3 := by
    calc
      (Fintype.card (ClassicalSeparatedBranchScaleColor T Y L) : ℝ) =
          (Fintype.card (ClassicalBranchScaleColor T Y) : ℝ) * (2 * (L + 1 : ℕ)) := by
        simp only [ClassicalSeparatedBranchScaleColor, Fintype.card_prod, ZMod.card,
          Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
      _ ≤ (3 * q) * (2 * ((5 * c + 1) * q ^ 2)) := by
        gcongr
      _ = 6 * (5 * c + 1) * q ^ 3 := by ring
  have hfirst : (4 * Nat.ceil (1 + 4 * q) + 6 : ℝ) ≤ 30 * q := by
    have hceil' := Nat.ceil_lt_add_one (show 0 ≤ 1 + 4 * q by linarith)
    linarith
  calc
    classicalSlabEnergyLoss T θ Y =
        (4 * Nat.ceil (1 + 4 * q) + 6) *
          (9 * (Fintype.card (ClassicalSeparatedBranchScaleColor T Y L) : ℝ) ^ 4) := rfl
    _ ≤ (30 * q) * (9 * (6 * (5 * c + 1) * q ^ 3) ^ 4) := by gcongr
    _ = K * q ^ 13 := by dsimp [K]; ring
    _ = K * T ^ (13 * θ) := by
      rw [← Real.rpow_natCast q 13, ← Real.rpow_mul hTpos.le]
      congr 2
      push_cast
      ring

/-- The two genuine large-value energy hypotheses imply a shifted zero-slab
energy estimate. All source cutoffs and threshold parameters are selected in
the correct order; neither an unrelated scale nor a zero-energy estimate is
assumed. The final symmetric-rectangle and exponent-extremum bridges are
separate from this positive-slab theorem. -/
theorem classicalSlabZeroEnergy_bound_of_uniform_energy_bounds
    (σ B τ₀ : ℝ) (hσ : 1 / 2 < σ) (hσUpper : σ ≤ 1)
    (hB : 0 ≤ B) (hτ₀ : 0 < τ₀)
    (hZeta : ∀ τ : ℝ, 1 ≤ τ → IsZetaLargeValueEnergyBound σ τ (B * τ))
    (hGeneral : ∀ τ : ℝ, τ₀ ≤ τ → IsLargeValueEnergyBound σ τ (B * τ)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ 1 / 2 < σ - δ ∧
        ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ T : ℝ in Filter.atTop,
          (classicalSlabZeroEnergy (σ - δ) T : ℝ) ≤ C * T ^ (B + ε) := by
  intro ε hε
  let a : ℝ := min (1 / 2) (1 / (4 * τ₀))
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have haHalf : a ≤ 1 / 2 := min_le_left _ _
  have haSmall : a ≤ 1 / (4 * τ₀) := min_le_right _ _
  have hτa : τ₀ ≤ 1 / (2 * a) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * a)).mpr
    have hx := (le_div_iff₀ (by positivity : 0 < 4 * τ₀)).mp haSmall
    nlinarith
  obtain ⟨CI, hCI, δI, hδI, hI⟩ :=
    classicalTypeI_uniform_source_class_energy_bound σ B a hB ha (by linarith)
      (fun τ hτ => hZeta τ hτ.1) (ε / 2) (by linarith)
  let D : ℝ := min (a * δI / 16) (min a (1 / 4))
  have hD : 0 < D := lt_min (by positivity) (lt_min ha (by norm_num))
  have hDsmall : D ≤ a * δI / 16 := min_le_left _ _
  have hDa : D ≤ a := (min_le_right _ _).trans (min_le_left _ _)
  have hDquarter : D ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  let b := D / 2
  have hb : 0 < b := by dsimp [b]; positivity
  have hba : b ≤ a := by dsimp [b]; linarith
  have hτab : τ₀ ≤ 1 / (a + b) :=
    hτa.trans (one_div_le_one_div_of_le (by positivity) (by linarith))
  obtain ⟨CII, hCII, δII, hδII, hII⟩ :=
    classicalTypeII_uniform_source_class_energy_bound σ B a b hB ha hb hba
      (by linarith) (fun τ hτ => hGeneral τ (hτab.trans hτ.1))
      (ε / 2) (by linarith)
  let δ := min ((σ - 1 / 2) / 2) (min (δI / 4) (δII / 4))
  have hδ : 0 < δ := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hδσ : δ ≤ (σ - 1 / 2) / 2 := min_le_left _ _
  have hδIle : δ ≤ δI / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hδIIle : δ ≤ δII / 4 := (min_le_right _ _).trans (min_le_right _ _)
  let s := σ - δ
  have hs : 1 / 2 < s := by dsimp [s]; linarith
  have hsUpper : s ≤ 1 := by dsimp [s]; linarith
  obtain ⟨θ, hθ, hθone, hθε, hIbound⟩ := hI s D (by linarith)
    (by dsimp [s]; linarith) (by linarith) (by linarith)
  have hIIbound := hII s D θ (by linarith) (by dsimp [s]; linarith) hθone.le
  obtain ⟨K, hK, hloss⟩ := eventually_classicalSlabEnergyLoss_le_const_mul_rpow θ hθ
  obtain ⟨Tbranch, hTbranch, hbranch⟩ :=
    classicalSlabZeroEnergy_le_separated_branch_scale_class_energies
      s θ 2 D 4 1 hs hsUpper hθ
  obtain ⟨Tcut, hTcut, hcut⟩ := eventually_classical_dichotomy_cutoffs
    a D ha hD (by dsimp [b] at hba; exact hba) (by linarith)
  obtain ⟨Tproduct, _hTproduct, hproduct⟩ := eventually_classical_short_product_le_quarter D hD
  obtain ⟨Terror, _hTerror, herror⟩ :=
    eventually_sharp_full_error_le_split_threshold s D (by linarith) (by linarith)
  let C : ℝ := max 1 (K * max CI CII)
  refine ⟨δ, hδ, hs, C, le_max_left _ _, ?_⟩
  filter_upwards [hIbound, hIIbound, hloss,
    Filter.eventually_ge_atTop Tbranch, Filter.eventually_ge_atTop Tcut,
    Filter.eventually_ge_atTop Tproduct, Filter.eventually_ge_atTop Terror] with
      T hIbound hIIbound hloss hTB hTC hTP hTE
  have hT : 8 ≤ T := hTbranch.trans hTB
  have hTpos : 0 < T := by linarith
  have hTone : 1 ≤ T := by linarith
  let Y := ⌊T ^ a⌋₊
  let X := ⌊T ^ b⌋₊
  let L := (2 * Nat.ceil (T ^ θ) + 1) * classicalLocalMultiplicityCap T
  have hcut' := hcut T hTC
  dsimp only at hcut'
  obtain ⟨hMassI, hThresholdI, hMassII, hThresholdII⟩ :=
    classical_dichotomy_mass_and_threshold_bounds T D Y X hT
      hcut'.2.2.2.2.2 hcut'.2.2.2.2.1
  obtain ⟨shiftedZero, baseColor, hlocal, label, _hshift, hinterval,
    hlarge, _hsep, henergy⟩ :=
    hbranch T Y X hTB hcut'.1 hcut'.2.1 hcut'.2.2.1 hcut'.2.2.2.1
      (herror T hTE) (hproduct T hTP) hMassI hThresholdI hMassII hThresholdII
  let color := classicalSeparatedBranchScaleColor s T Y shiftedZero baseColor L hlocal
  let Wᵢ := fun i : Fin 4 =>
    fun x : EnergyColorFiber color (label i) => shiftedZero x.1.1
  have hclass (i : Fin 4) : (approximateAdditiveEnergyOf 1 (Wᵢ i) : ℝ) ≤
      max CI CII * T ^ (B + ε / 2) := by
    cases hlabel : (label i).1 with
    | none =>
      haveI : IsEmpty (EnergyColorFiber color (label i)) := ⟨fun x => by
        have hx := hlarge i x
        change ClassicalBranchScaleLarge s T D Y X (label i).1 (shiftedZero x.1.1) at hx
        simp only [hlabel, ClassicalBranchScaleLarge] at hx⟩
      have hempty : approximateAdditiveEnergyOf 1 (Wᵢ i) = 0 := by
        simp [approximateAdditiveEnergyOf]
      rw [hempty, Nat.cast_zero]
      exact mul_nonneg (zero_le_one.trans (hCI.trans (le_max_left _ _)))
        (Real.rpow_nonneg hTpos.le _)
    | some branch =>
      cases branch with
      | inl r =>
        exact (hIbound X L shiftedZero baseColor hlocal (label i) r hlabel
          hinterval (hlarge i)).trans (mul_le_mul_of_nonneg_right
            (le_max_left _ _) (Real.rpow_nonneg hTpos.le _))
      | inr r =>
        exact (hIIbound L shiftedZero baseColor hlocal (label i) r hlabel
          hinterval (hlarge i)).trans (mul_le_mul_of_nonneg_right
            (le_max_right _ _) (Real.rpow_nonneg hTpos.le _))
  have hsum :
      (approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
        (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
        (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
        (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ) ≤
          4 * (max CI CII * T ^ (B + ε / 2)) := by
    linarith [hclass 0, hclass 1, hclass 2, hclass 3]
  have hLossNonneg : 0 ≤ classicalSlabEnergyLoss T θ Y := by
    unfold classicalSlabEnergyLoss
    positivity
  have hslab : (classicalSlabZeroEnergy s T : ℝ) ≤
      classicalSlabEnergyLoss T θ Y * (max CI CII * T ^ (B + ε / 2)) := by
    have hmul := mul_le_mul_of_nonneg_left hsum hLossNonneg
    change 4 * (classicalSlabZeroEnergy s T : ℝ) ≤
      classicalSlabEnergyLoss T θ Y *
        ((approximateAdditiveEnergyOf 1 (Wᵢ 0) : ℝ) +
          (approximateAdditiveEnergyOf 1 (Wᵢ 1) : ℝ) +
          (approximateAdditiveEnergyOf 1 (Wᵢ 2) : ℝ) +
          (approximateAdditiveEnergyOf 1 (Wᵢ 3) : ℝ)) at henergy
    nlinarith
  have hMaxNonneg : 0 ≤ max CI CII := zero_le_one.trans (hCI.trans (le_max_left _ _))
  calc
    (classicalSlabZeroEnergy (σ - δ) T : ℝ) ≤
        classicalSlabEnergyLoss T θ Y * (max CI CII * T ^ (B + ε / 2)) := hslab
    _ ≤ (K * T ^ (13 * θ)) * (max CI CII * T ^ (B + ε / 2)) :=
      mul_le_mul_of_nonneg_right (hloss Y hcut'.2.2.2.1) (by positivity)
    _ = (K * max CI CII) * T ^ (13 * θ + (B + ε / 2)) := by
      rw [Real.rpow_add hTpos (13 * θ) (B + ε / 2)]
      ring
    _ ≤ C * T ^ (B + ε) :=
      mul_le_mul (le_max_right _ _)
        (Real.rpow_le_rpow_of_exponent_le hTone (by linarith))
        (Real.rpow_nonneg hTpos.le _) (zero_le_one.trans (le_max_left _ _))

end TaoTrudgianYang2025
