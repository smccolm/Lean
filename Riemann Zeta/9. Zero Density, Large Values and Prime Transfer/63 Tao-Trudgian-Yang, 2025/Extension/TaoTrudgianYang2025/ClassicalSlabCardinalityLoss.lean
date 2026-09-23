import TaoTrudgianYang2025.ClassicalSlabEnergyTransfer

/-!
# Multiplicity-preserving slab cardinality loss

Every branch/scale and parity/rank color is counted. The cost has three
subpower factors: displacement, local multiplicity, and dyadic scales.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

def classicalSlabCardinalityLoss (T θ : ℝ) (Y : ℕ) : ℝ :=
  let L := (2 * Nat.ceil (T ^ θ) + 1) * classicalLocalMultiplicityCap T
  (Fintype.card (ClassicalSeparatedBranchScaleColor T Y L) : ℝ)

theorem eventually_classicalSlabCardinalityLoss_le_const_mul_rpow
    (θ : ℝ) (hθ : 0 < θ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in Filter.atTop, ∀ Y : ℕ,
      Y ≤ ⌊sharpZetaCutoff T⌋₊ →
      classicalSlabCardinalityLoss T θ Y ≤ K * T ^ (3 * θ) := by
  obtain ⟨c, hc, hcap⟩ := localMultiplicityCap_le_rpow hθ
  let K : ℝ := 6 * (5 * c + 1)
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
  calc
    classicalSlabCardinalityLoss T θ Y ≤ 6 * (5 * c + 1) * q ^ 3 := hcolors
    _ = K * T ^ (3 * θ) := by
      rw [← Real.rpow_natCast q 3, ← Real.rpow_mul hTpos.le]
      dsimp only [K]
      congr 2
      push_cast
      ring


end TaoTrudgianYang2025
