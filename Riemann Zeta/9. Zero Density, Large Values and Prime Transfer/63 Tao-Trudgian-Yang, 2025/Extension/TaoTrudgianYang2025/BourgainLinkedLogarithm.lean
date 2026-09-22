import TaoTrudgianYang2025.BourgainLinkedPowerLoss
import TaoTrudgianYang2025.BourgainLogCardinality
import TaoTrudgianYang2025.BourgainLogPacking

/-!
# Actual nonempty patterns enter the finite logarithmic dichotomy

The logarithmic coordinates below are the literal original, retained and
full-slice cardinalities. The nonempty restriction is explicit because the
small branch also takes the logarithm of the original count.
-/

open RiemannZeta.GuthMaynard
open scoped Classical

noncomputable section

namespace TaoTrudgianYang2025

theorem bourgain_linked_logarithmic_comparison {σ τ χ α η θ κ ζ : ℝ}
    (hσ : 3/4 < σ) (hχ : 0 ≤ χ) (hmargin : 1 < τ-χ)
    (hη : 0 < η) (hθ : 0 < θ) (hκ : 0 < κ) (hζ : 0 < ζ)
    {ε : ℝ} (hε : 0 < ε) (hε₈ : ε ≤ 8) :
    ∃ B C δ K G H N₀ : ℝ,
      0 < B ∧ 2 ≤ C ∧ 0 < δ ∧ δ ≤ 1 ∧ δ ≤ (τ-χ-1)/2 ∧
      δ ≤ ζ ∧ 0 < K ∧ 0 < G ∧ 1 ≤ H ∧ 2 ≤ N₀ ∧
      ∀ (P : LargeValuePattern) (L : ℝ), P.ordinates.Nonempty →
        C ≤ P.N → N₀ ≤ P.N → L = P.T/P.N^χ →
        P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
        let ρ := Real.logb P.N (P.ordinates.card : ℝ)
        let E := bourgainComparisonLoss (τ-χ) ε δ κ
        ρ ≤ bourgainSmallExponent σ τ α χ+ε+Real.logb P.N (6*C) ∨
          ∃ S : Finset ℝ, S ⊆ P.ordinates ∧ S.Nonempty ∧ IsSeparated 1 S ∧
            (∀ t ∈ S, P.V ≤ ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n t‖) ∧
            let r := Real.logb P.N (S.card : ℝ)
            0 ≤ r ∧ r ≤ τ+δ+Real.logb P.N 2 ∧
            ρ ≤ Real.logb P.N (6*C+C*H)+
              max (bourgainSmallExponent σ τ α χ+ε) (ε+κ+r) ∧
            let a := P.N^(-bourgainSharedFloorExponent α (τ-χ) ε)
            let J := bourgainZetaBandCount B (L+P.N^(ε/8)+1) a
            ∃ q ∈ Finset.range J, ∃ u ∈ Set.Ioc (-(P.N^(ε/8))) (P.N^(ε/8)),
              (bourgainIntegerSlice (P.N^(ε/8)) (L+P.N^(ε/8)+1) (a*(2 : ℝ)^q) u).Nonempty ∧
              let x := Real.logb P.N ((bourgainIntegerSlice (P.N^(ε/8)) (L+P.N^(ε/8)+1)
                (a*(2 : ℝ)^q) u).card : ℝ)
              0 ≤ x ∧ x ≤ (τ-χ)+δ+Real.logb P.N 9 ∧
              max (-2*α+2*σ+x+r-E-2*δ-Real.logb P.N G)
                (-α-χ/2+2*σ+x/2+3*r/2-E/2-2*δ-Real.logb P.N (2*G)/2) <
                Real.logb P.N (3*K)+(2*η+(τ+δ)*θ)+
                  heathBrownDoubleZetaExponent (τ+δ) r/2+
                  heathBrownDoubleZetaExponent (τ+δ) x/2 := by
  obtain ⟨B, C, δ, K, G, H, N₀, hB, hC, hδ, hδ₁, hδmargin,
    hδζ, hK, hG, hH, hN₀, hp⟩ :=
    bourgain_linked_power_loss_comparison (α := α) hσ hχ hmargin hη hθ hκ hζ hε hε₈
  refine ⟨B, C, δ, K, G, H, N₀, hB, hC, hδ, hδ₁, hδmargin,
    hδζ, hK, hG, hH, hN₀, ?_⟩
  intro P L hP hNC hN hLeq hTlo hThi hVl
  have hQ : (0 : ℝ) < P.ordinates.card := by exact_mod_cast hP.card_pos
  have hCp : 0 < C := by linarith
  have hHp : 0 < H := by linarith
  have hscales := bourgain_subdivision_physical_scales P.one_lt_N hχ
    (by linarith : 1+δ ≤ τ-χ) hTlo hThi
  have hNL : P.N ≤ L := by simpa only [hLeq] using hscales.2.1
  have hLT : L ≤ P.T := by simpa only [hLeq] using hscales.2.2.1
  have hLu : L ≤ P.N^((τ-χ)+δ) := by simpa only [hLeq] using hscales.2.2.2.2
  have hone : 1 ≤ P.N^(τ+δ) := P.one_lt_N.le.trans (hNL.trans (hLT.trans hThi))
  obtain ⟨S, hsource, hsep, hlarge, hpack, hbranch⟩ :=
    hp P L hNC hN hLeq hTlo hThi hVl
  rcases hbranch with hsmall | ⟨hS, q, hq, u, hu, hZ, hcomp⟩
  · exact Or.inl (bourgain_small_original_log_bound P.one_lt_N hQ hCp hsmall)
  · right
    have hR : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
    have hX : (0 : ℝ) <
        (bourgainIntegerSlice (P.N^(ε/8)) (L+P.N^(ε/8)+1)
          (P.N^(-bourgainSharedFloorExponent α (τ-χ) ε)*(2 : ℝ)^q) u).card := by
      exact_mod_cast hZ.card_pos
    have hr := bourgain_source_log_card_bounds P S hsource hS hone hThi
    have hx := bourgain_local_slice_log_card_bounds P.one_lt_N hNL hε₈ hLu
      ⟨hu.1.le, hu.2⟩ hZ
    refine ⟨S, hsource, hS, hsep, hlarge, hr.1, hr.2,
      bourgain_original_count_log_bound P.one_lt_N hQ hR hCp hHp hpack,
      q, hq, u, hu, hZ, hx.1, hx.2, ?_⟩
    exact bourgain_finite_comparison_logarithm P.one_lt_N P.T_pos.le hR hX hK hG hThi hcomp

end TaoTrudgianYang2025
