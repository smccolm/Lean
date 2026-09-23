import TaoTrudgianYang2025.ClassicalTypeISourceCardinality

/-!
# Cardinality of actual Type-I zero-copy color classes

Largeness and separation come from the literal branch label and its refined
color. Analytic multiplicities remain in the indexed zero-copy domain.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem classicalTypeI_uniform_source_class_cardinality_bound
    (σ B a : ℝ) (hB : 0 ≤ B) (ha : 0 < a) (hatwo : a ≤ 2)
    (hLV : ∀ τ ∈ Set.Icc (1 : ℝ) (2 / a),
      IsZetaLargeValueBound σ τ (B * τ)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
        ∀ s D : ℝ, 0 ≤ s → σ - δ / 2 ≤ s → 0 ≤ D + 1 → D ≤ a * δ / 8 →
          ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ θ ≤ ε / 40 ∧
            ∀ᶠ T : ℝ in Filter.atTop,
              let Y := ⌊T ^ a⌋₊
              ∀ (X L : ℕ)
                (shiftedZero : ↥(zerosInRect s 1 T (2 * T)) → ℝ)
                (baseColor : ↥(zerosInRect s 1 T (2 * T)) →
                  ClassicalBranchScaleColor T Y)
                (hlocal : ∀ z : ℤ,
                  (unitBinFinset (fun x : ClassicalSlabZeroCopy s T =>
                    shiftedZero x.1) z).card ≤ L)
                (label : ClassicalSeparatedBranchScaleColor T Y L)
                (r : Fin (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊)),
                label.1 = some (Sum.inl r) →
                (∀ ρ, T - T ^ θ ≤ shiftedZero ρ ∧
                  shiftedZero ρ ≤ 2 * T + T ^ θ) →
                (∀ x : EnergyColorFiber
                  (classicalSeparatedBranchScaleColor s T Y
                    shiftedZero baseColor L hlocal) label,
                  ClassicalBranchScaleLarge s T D Y X label.1 (shiftedZero x.1.1)) →
                (Fintype.card (EnergyColorFiber
                    (classicalSeparatedBranchScaleColor s T Y
                      shiftedZero baseColor L hlocal) label) : ℝ) ≤ C * T ^ (B + ε) := by
  intro ε hε
  have hinterval : 1 / (a / 2) = 2 / a := by rw [div_div_eq_mul_div]; ring
  have hLV' : ∀ τ ∈ Set.Icc (1 : ℝ) (1 / (a / 2)),
      IsZetaLargeValueBound σ τ (B * τ) := by
    simpa only [hinterval] using hLV
  obtain ⟨C, hC, δ, hδ, hsource⟩ :=
    classicalTypeI_uniform_source_cardinality_bound σ B (a / 2)
      hB (by linarith) (by linarith) hLV' ε hε
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro s D hs hsσ hD hDloss
  obtain ⟨θ, hθ, hθone, hθε, hbound⟩ := hsource s D hs hsσ hD (by linarith)
  refine ⟨θ, hθ, hθone, hθε, ?_⟩
  filter_upwards [hbound, eventually_classicalTypeI_sourceScale_lower a ha] with
    T hbound hscale
  dsimp only
  intro X L shiftedZero baseColor hlocal label r hlabel hW hlarge
  let Y := ⌊T ^ a⌋₊
  let N := 2 ^ (r : ℕ) * Y
  let color := classicalSeparatedBranchScaleColor s T Y shiftedZero baseColor L hlocal
  let W := fun x : EnergyColorFiber color label => shiftedZero x.1.1
  apply hbound N W (hscale r)
  · intro x
    exact hW x.1.1
  · intro x
    have hx := hlarge x
    rw [hlabel] at hx
    exact hx.1
  · intro x y hxy
    exact separatedRefinementColor_oneSeparated
      (fun z : ClassicalSlabZeroCopy s T => shiftedZero z.1)
      (fun z => baseColor z.1) L hlocal label x y hxy


end TaoTrudgianYang2025
