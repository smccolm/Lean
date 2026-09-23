import TaoTrudgianYang2025.ClassicalTypeICardinalityTransfer

/-!
# Fourier deweighting for cardinality

The actual bounded shifted family is partitioned into every parity/rank
color. Its index type is unchanged, so no energy inequality or accidental
identification of coincident ordinates enters this cardinality transfer.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem IsZetaLargeValueBound.classicalTypeI_fourier_cardinality_transfer
    {σLV τ ρ : ℝ} (hLV : IsZetaLargeValueBound σLV τ ρ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
        ∀ {ι : Type*} [Fintype ι] [LinearOrder ι]
          (A N k : ℕ) (σ V T u : ℝ) (W : ι → ℝ),
          let d := 2 * Real.pi * classicalTypeIFourierRadius A N k σ V
          let L := Nat.ceil (2 * d + 2)
          let Q := V / (4 * (N : ℝ) ^ (-σ) * classicalTypeIFourierL1 σ)
          1 < N → 0 < V → 1 < k → 0 < T →
          u + d ≤ T / 2 →
          (∀ x, T - u ≤ W x ∧ W x ≤ 2 * T + u) →
          (∀ x, V ≤
            ‖dirichletPoly N (classicalZetaLongLineCoeff A σ) (W x)‖) →
          (∀ x y : ι, x ≠ y → 1 ≤ |W x - W y|) →
          C ≤ (N : ℝ) →
          (N : ℝ) ^ (τ - δ) ≤ T / 2 →
          2 * T ≤ (N : ℝ) ^ (τ + δ) →
          (N : ℝ) ^ (σLV - δ) ≤ Q →
          (Fintype.card ι : ℝ) ≤
            (Fintype.card (ZMod 2 × Fin (L + 1)) : ℝ) *
              (3 * (C * (N : ℝ) ^ (ρ + ε))) := by
  intro ε hε
  obtain ⟨C, hC, δ, hδ, hZeta⟩ :=
    hLV.classicalTypeI_expanded_slab_bound ε hε
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro ι _ _ A N k σ V T u W
  dsimp only
  let d := 2 * Real.pi * classicalTypeIFourierRadius A N k σ V
  let L := Nat.ceil (2 * d + 2)
  let Q := V / (4 * (N : ℝ) ^ (-σ) * classicalTypeIFourierL1 σ)
  intro hN hV hk hT hroom hW hlarge hsep hCN hTL hTU hQL
  classical
  have hd : 0 ≤ d :=
    mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
      (classicalTypeIFourierRadius_pos A N k σ V hV hk).le
  obtain ⟨W', hpert, hlarge', _henergy⟩ :=
    exists_classicalTypeI_explicitBoundedOrdinate_family
      A N k σ V W (by omega) hV hk hlarge
  let hlocal : ∀ z : ℤ, (unitBinFinset W' z).card ≤ L := fun z =>
    unitBinFinset_perturbation_card_le_natCeil W W' d hd hsep hpert z
  let color := boundedMultiplicityColor W' L hlocal
  let Wᵢ := fun c : ZMod 2 × Fin (L + 1) =>
    fun x : EnergyColorFiber color c => W' x.1
  apply cardinality_le_color_count_mul color
  intro c
  apply hZeta A N Q T (Wᵢ c) hN hT
    _ (oneSeparated_on_boundedMultiplicityColor W' L hlocal c)
    (fun x => hlarge' x.1) hCN hTL hTU hQL
  intro x
  have hx := hW x.1
  have hp := abs_le.mp (hpert x.1)
  change T / 2 ≤ W' x.1 ∧ W' x.1 ≤ 4 * T
  constructor <;> linarith

end TaoTrudgianYang2025
