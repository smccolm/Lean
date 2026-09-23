import TaoTrudgianYang2025.ClassicalPatternCardinality

/-!
# Cardinality transfer on the expanded Type-I source slab

Three positive dyadic slabs cover the original ordinates without translating
the polynomial. All color fibers are counted, preserving every source index.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem IsZetaLargeValueBound.classicalTypeI_expanded_slab_bound
    {σ τ ρ : ℝ} (hLV : IsZetaLargeValueBound σ τ ρ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
        ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
          (A N : ℕ) (V T : ℝ) (W : ι → ℝ),
          1 < N → 0 < T →
          (∀ x, T / 2 ≤ W x ∧ W x ≤ 4 * T) →
          (∀ x y : ι, x ≠ y → 1 ≤ |W x - W y|) →
          (∀ x, V ≤ ‖∑ n ∈ Finset.Ioc N (min (2 * N) A),
            dirichletPhase n (W x)‖) →
          C ≤ (N : ℝ) →
          (N : ℝ) ^ (τ - δ) ≤ T / 2 →
          2 * T ≤ (N : ℝ) ^ (τ + δ) →
          (N : ℝ) ^ (σ - δ) ≤ V →
          (Fintype.card ι : ℝ) ≤
            3 * (C * (N : ℝ) ^ (ρ + ε)) := by
  intro ε hε
  obtain ⟨C, hC, δ, hδ, hbound⟩ := hLV ε hε
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro ι _ _ A N V T W hN hT hW hsep hlarge hCN hTL hTU hVL
  classical
  let color : ι → Fin 3 := fun x => classicalTypeIHeightColor T (W x)
  let Wᵢ := fun i : Fin 3 =>
    fun x : EnergyColorFiber color i => W x.1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hVpos : 0 < (N : ℝ) ^ (σ - δ) := Real.rpow_pos_of_pos hNpos _
  have hclass (i : Fin 3) :
      (Fintype.card (EnergyColorFiber color i) : ℝ) ≤
        C * (N : ℝ) ^ (ρ + ε) := by
    let H := classicalTypeIHeight T i
    have hH := classicalTypeIHeight_bounds T hT i
    have hWi : ∀ x : EnergyColorFiber color i,
        H ≤ Wᵢ i x ∧ Wᵢ i x ≤ 2 * H := by
      intro x
      have hx := classicalTypeIHeightColor_mem T (W x.1) (hW x.1)
      change classicalTypeIHeight T (color x.1) ≤ Wᵢ i x ∧
        Wᵢ i x ≤ 2 * classicalTypeIHeight T (color x.1) at hx
      simpa only [x.2] using hx
    have hsepi : ∀ x y : EnergyColorFiber color i,
        x ≠ y → 1 ≤ |Wᵢ i x - Wᵢ i y| := by
      intro x y hxy
      exact hsep x.1 y.1 (fun h => hxy (Subtype.ext h))
    have hlargei : ∀ x : EnergyColorFiber color i,
        (N : ℝ) ^ (σ - δ) ≤
          ‖∑ n ∈ Finset.Ioc N (min (2 * N) A), dirichletPhase n (Wᵢ i x)‖ :=
      fun x => hVL.trans (hlarge x.1)
    let P := indexedClassicalTypeIZetaPattern
      A N ((N : ℝ) ^ (σ - δ)) H (Wᵢ i) hN hVpos hH.1 hWi hsepi hlargei
    have hPN : P.N = N := rfl
    have hPT : P.T = H := by change 2 * H - H = H; ring
    have hPV : P.V = (N : ℝ) ^ (σ - δ) := rfl
    have hlow : P.N ^ (τ - δ) ≤ P.T := by
      rw [hPN, hPT]
      exact hTL.trans hH.2.1
    have hupp : P.T ≤ P.N ^ (τ + δ) := by
      rw [hPN, hPT]
      exact hH.2.2.trans hTU
    have hvupp : P.V ≤ P.N ^ (σ + δ) := by
      rw [hPV, hPN]
      exact Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast hN.le) (by linarith)
    have heq := indexedClassicalTypeIZetaPattern_card
      A N ((N : ℝ) ^ (σ - δ)) H (Wᵢ i) hN hVpos hH.1 hWi hsepi hlargei
    have hp := hbound P hCN hlow hupp (by rw [hPN, hPV]) hvupp
    rw [show P.ordinates.card = Fintype.card (EnergyColorFiber color i) from heq,
      hPN] at hp
    exact hp
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using
    cardinality_le_color_count_mul color (C * (N : ℝ) ^ (ρ + ε)) hclass


end TaoTrudgianYang2025
