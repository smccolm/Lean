import TaoTrudgianYang2025.EnergyPoweringObstruction
import TaoTrudgianYang2025.EnergyPartition

/-!
# Cardinality/energy repair of the printed powering lemma

The four-coordinate region is the existential projection of the real
five-coordinate region, not a new model for its double zeta sum. The
corrected powering proposition below is a specification, not a proved
analytic theorem. The finite energy-selection lemma and the consumers of
its two separate output witnesses are proved here. In particular, the
Heath--Brown consumer never assumes a transformation law for `s`.
-/

noncomputable section

namespace TaoTrudgianYang2025

/-- Forget only the double-zeta-sum exponent, retaining actual realizability. -/
def InCardinalityEnergyRegion (σ τ ρ ρstar : ℝ) : Prop :=
  ∃ s : ℝ, InLargeValueEnergyRegion σ τ ρ ρstar s

/-- The repaired conclusion has two possibly different witnesses. Their
uncontrolled double-zeta exponents are existentially quantified separately. -/
def CardinalityEnergyPoweringWitnesses (σ τ ρ ρstar : ℝ) (k : ℕ) : Prop :=
  (∃ energy : ℝ,
    InCardinalityEnergyRegion σ (τ / k) (ρ / k) energy ∧ energy ≤ ρstar / k) ∧
  (∃ card : ℝ,
    InCardinalityEnergyRegion σ (τ / k) card (ρstar / k) ∧ card ≤ ρ / k)

/-- Authorized replacement target for EPZAE-34. This declaration states
the analytic theorem still to be proved; no proof is claimed by this `def`.
The power is a positive integer, as required by polynomial expansion. -/
def CorrectedCardinalityEnergyPowering : Prop :=
  ∀ (σ τ ρ ρstar : ℝ) (k : ℕ), 1 ≤ k →
    InCardinalityEnergyRegion σ τ ρ ρstar →
      CardinalityEnergyPoweringWitnesses σ τ ρ ρstar k

/-- Expansion of the projection makes the two independent `s` witnesses
and the absence of either false scaling restriction explicit. -/
theorem cardinalityEnergyPoweringWitnesses_iff
    (σ τ ρ ρstar : ℝ) (k : ℕ) :
    CardinalityEnergyPoweringWitnesses σ τ ρ ρstar k ↔
      (∃ energy sCard : ℝ,
        InLargeValueEnergyRegion σ (τ / k) (ρ / k) energy sCard ∧
          energy ≤ ρstar / k) ∧
      (∃ card sEnergy : ℝ,
        InLargeValueEnergyRegion σ (τ / k) card (ρstar / k) sEnergy ∧
          card ≤ ρ / k) := by
  simp only [CardinalityEnergyPoweringWitnesses, InCardinalityEnergyRegion,
    exists_and_right]

/-- Identity-power regression, not a proof for arbitrary powers. -/
theorem cardinalityEnergyPoweringWitnesses_one
    {σ τ ρ ρstar : ℝ} (h : InCardinalityEnergyRegion σ τ ρ ρstar) :
    CardinalityEnergyPoweringWitnesses σ τ ρ ρstar 1 := by
  simpa only [CardinalityEnergyPoweringWitnesses, Nat.cast_one, div_one] using
    (show (∃ energy, InCardinalityEnergyRegion σ τ ρ energy ∧ energy ≤ ρstar) ∧
      (∃ card, InCardinalityEnergyRegion σ τ card ρstar ∧ card ≤ ρ) from
      ⟨⟨ρstar, h, le_rfl⟩, ⟨ρ, h, le_rfl⟩⟩)

/-- The retained counterexample family satisfies the repaired conclusion
for every positive integer power. Its new `s` remains two, not `2/k`. -/
theorem singleton_cardinalityEnergyPoweringWitnesses
    (σ τ : ℝ) (k : ℕ) (hσLower : 1 / 2 ≤ σ) (hσUpper : σ ≤ 1)
    (hτ : 0 ≤ τ) (hk : 1 ≤ k) :
    CardinalityEnergyPoweringWitnesses σ τ 0 0 k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hregion : InCardinalityEnergyRegion σ (τ / k) 0 0 :=
    ⟨2, singleton_mem_largeValueEnergyRegion _ _ hσLower hσUpper
      (div_nonneg hτ hkpos.le)⟩
  refine ⟨⟨0, ?_, ?_⟩, ⟨0, ?_, ?_⟩⟩
  all_goals simpa only [zero_div] using (by first | exact hregion | exact le_rfl)

/-- A monochromatic class retains energy up to a fixed fourth-power
color loss. This is the finite partition step required by energy powering. -/
theorem exists_energy_preserving_color
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (W : ι → ℝ) (color : ι → κ) :
    ∃ c : κ,
      (approximateAdditiveEnergyOf 1 W : ℝ) ≤
        9 * (Fintype.card κ : ℝ) ^ 4 *
          (approximateAdditiveEnergyOf 1
            (fun x : EnergyColorFiber color c => W x.1) : ℝ) := by
  classical
  obtain ⟨label, hbound⟩ := exists_energy_color_classes W color
  let E : Fin 4 → ℝ := fun i =>
    approximateAdditiveEnergyOf 1
      (fun x : EnergyColorFiber color (label i) => W x.1)
  obtain ⟨i, _hi, hmax⟩ := Finset.exists_max_image Finset.univ E Finset.univ_nonempty
  have h0 := hmax 0 (Finset.mem_univ _)
  have h1 := hmax 1 (Finset.mem_univ _)
  have h2 := hmax 2 (Finset.mem_univ _)
  have h3 := hmax 3 (Finset.mem_univ _)
  have hsum : E 0 + E 1 + E 2 + E 3 ≤ 4 * E i := by linarith
  have hfactor : 0 ≤ 9 * (Fintype.card κ : ℝ) ^ 4 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hsum hfactor
  refine ⟨label i, ?_⟩
  change 4 * (approximateAdditiveEnergyOf 1 W : ℝ) ≤
    9 * (Fintype.card κ : ℝ) ^ 4 * (E 0 + E 1 + E 2 + E 3) at hbound
  change (approximateAdditiveEnergyOf 1 W : ℝ) ≤ 9 * (Fintype.card κ : ℝ) ^ 4 * E i
  nlinarith

/-- The cardinality witness transfers any bound monotone in the energy
coordinate. This is conditional on that separately stated upstream bound. -/
theorem CardinalityEnergyPoweringWitnesses.cardinality_bound
    {σ τ ρ ρstar : ℝ} {k : ℕ}
    (h : CardinalityEnergyPoweringWitnesses σ τ ρ ρstar k)
    (F : ℝ → ℝ) (hF : Monotone F)
    (hbound : ∀ card energy : ℝ,
      InCardinalityEnergyRegion σ (τ / k) card energy → card ≤ F energy) :
    ρ / k ≤ F (ρstar / k) := by
  obtain ⟨energy, hregion, hle⟩ := h.1
  exact (hbound _ _ hregion).trans (hF hle)

/-- The energy witness transfers any relation monotone in cardinality;
the energy coordinate is preserved exactly for this witness. -/
theorem CardinalityEnergyPoweringWitnesses.energy_relation
    {σ τ ρ ρstar : ℝ} {k : ℕ}
    (h : CardinalityEnergyPoweringWitnesses σ τ ρ ρstar k)
    (F : ℝ → ℝ → ℝ) (hF : ∀ energy, Monotone (fun card => F card energy))
    (hbound : ∀ card energy : ℝ,
      InCardinalityEnergyRegion σ (τ / k) card energy → energy ≤ F card energy) :
    ρstar / k ≤ F (ρ / k) (ρstar / k) := by
  obtain ⟨card, hregion, hle⟩ := h.2
  exact (hbound _ _ hregion).trans (hF _ hle)

/-- Intersections of coordinatewise monotone cardinality/energy constraints
can be saturated using separate witnesses. This does not claim closure of
an arbitrary four- or five-dimensional polytope under powering. -/
theorem CardinalityEnergyPoweringWitnesses.monotone_constraints
    {σ τ ρ ρstar : ℝ} {k : ℕ}
    (h : CardinalityEnergyPoweringWitnesses σ τ ρ ρstar k)
    {I : Type*} (F G : I → ℝ → ℝ)
    (hF : ∀ i, Monotone (F i)) (hG : ∀ i, Monotone (G i))
    (hbound : ∀ card energy : ℝ,
      InCardinalityEnergyRegion σ (τ / k) card energy →
        ∀ i, card ≤ F i energy ∧ energy ≤ G i card) :
    ∀ i, ρ / k ≤ F i (ρstar / k) ∧ ρstar / k ≤ G i (ρ / k) := by
  intro i
  constructor
  · exact h.cardinality_bound (F i) (hF i) (fun card energy hregion => (hbound card energy hregion i).1)
  · exact h.energy_relation (fun card _ => G i card) (fun _ => hG i)
      (fun card energy hregion => (hbound card energy hregion i).2)

/-- Exact right side of the printed Heath--Brown energy relation.
Its absence of an `s` parameter is mathematical, not a new normalization. -/
def heathBrownEnergyRHS (σ τ ρ ρstar : ℝ) : ℝ :=
  1 - 2 * σ +
    1 / 2 * max (max (ρ + 1) (2 * ρ)) (5 / 4 * ρ + τ / 2) +
    1 / 2 * max (max (ρstar + 1) (4 * ρ)) (3 / 4 * ρstar + ρ + τ / 2)

theorem heathBrownEnergyRHS_mono_card (σ τ ρstar : ℝ) :
    Monotone (fun ρ => heathBrownEnergyRHS σ τ ρ ρstar) := by
  intro ρ₁ ρ₂ hρ
  have hfirst : max (max (ρ₁ + 1) (2 * ρ₁)) (5 / 4 * ρ₁ + τ / 2) ≤
      max (max (ρ₂ + 1) (2 * ρ₂)) (5 / 4 * ρ₂ + τ / 2) :=
    max_le_max (max_le_max (by linarith) (by linarith)) (by linarith)
  have hsecond : max (max (ρstar + 1) (4 * ρ₁)) (3 / 4 * ρstar + ρ₁ + τ / 2) ≤
      max (max (ρstar + 1) (4 * ρ₂)) (3 / 4 * ρstar + ρ₂ + τ / 2) :=
    max_le_max (max_le_max le_rfl (by linarith)) (by linarith)
  unfold heathBrownEnergyRHS
  linarith

/-- Kernel-checked logical repair of the Heath--Brown powering step:
consume the repaired output witnesses and the separately stated analytic
relation at the powered height. Neither input is proved by this theorem. -/
theorem CardinalityEnergyPoweringWitnesses.heathBrown_relation
    {σ τ ρ ρstar : ℝ} {k : ℕ}
    (h : CardinalityEnergyPoweringWitnesses σ τ ρ ρstar k)
    (hHeathBrown : ∀ card energy : ℝ,
      InCardinalityEnergyRegion σ (τ / k) card energy →
        energy ≤ heathBrownEnergyRHS σ (τ / k) card energy) :
    ρstar / k ≤ heathBrownEnergyRHS σ (τ / k) (ρ / k) (ρstar / k) :=
  h.energy_relation _ (heathBrownEnergyRHS_mono_card σ (τ / k)) hHeathBrown

end TaoTrudgianYang2025
