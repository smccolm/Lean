import TaoTrudgianYang2025.BourgainLogCardinality
import Mathlib.Topology.MetricSpace.Sequences

/-!
# A common compactness subsequence for actual retained sets and full slices

Both cardinality coordinates are extracted together. Their compact box is
derived from physical interval geometry, not supplied as a hypothesis.
-/

open Filter Set Topology
open scoped Classical

noncomputable section

namespace TaoTrudgianYang2025

theorem bourgain_source_slice_log_subsequence
    (P : ℕ → LargeValuePattern) (S : ℕ → Finset ℝ)
    (L ε δ V u : ℕ → ℝ) (τ χ : ℝ)
    (hN : ∀ n, 2 ≤ (P n).N)
    (hS : ∀ n, (S n).Nonempty) (hsub : ∀ n, S n ⊆ (P n).ordinates)
    (hNL : ∀ n, (P n).N ≤ L n) (hLT : ∀ n, L n ≤ (P n).T)
    (hT : ∀ n, (P n).T ≤ (P n).N^(τ+δ n))
    (hL : ∀ n, L n ≤ (P n).N^((τ-χ)+δ n))
    (hδ : ∀ n, δ n ≤ 1) (hε : ∀ n, ε n ≤ 8)
    (hu : ∀ n, u n ∈ Icc (-((P n).N^(ε n/8))) ((P n).N^(ε n/8)))
    (hZ : ∀ n, (bourgainIntegerSlice ((P n).N^(ε n/8))
      (L n+(P n).N^(ε n/8)+1) (V n) (u n)).Nonempty) :
    ∃ r x : ℝ, 0 ≤ r ∧ r ≤ τ+2 ∧ 0 ≤ x ∧ x ≤ (τ-χ)+5 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n => Real.logb (P (φ n)).N ((S (φ n)).card : ℝ)) atTop (nhds r) ∧
        Tendsto (fun n => Real.logb (P (φ n)).N
          ((bourgainIntegerSlice ((P (φ n)).N^(ε (φ n)/8))
            (L (φ n)+(P (φ n)).N^(ε (φ n)/8)+1) (V (φ n)) (u (φ n))).card : ℝ))
          atTop (nhds x) := by
  let f := fun n => (Real.logb (P n).N ((S n).card : ℝ),
    Real.logb (P n).N ((bourgainIntegerSlice ((P n).N^(ε n/8))
      (L n+(P n).N^(ε n/8)+1) (V n) (u n)).card : ℝ))
  have hbounded : ∀ n, f n ∈ Icc (0, 0) (τ+2, (τ-χ)+5) := by
    intro n
    have hone : 1 ≤ (P n).N^(τ+δ n) :=
      (P n).one_lt_N.le.trans ((hNL n).trans ((hLT n).trans (hT n)))
    have hr := bourgain_source_log_card_bounds (P n) (S n) (hsub n) (hS n) hone (hT n)
    have hx := bourgain_local_slice_log_card_bounds (P n).one_lt_N (hNL n)
      (hε n) (hL n) (hu n) (hZ n)
    have htwo : Real.logb (P n).N 2 ≤ 1 := by
      apply (Real.logb_le_iff_le_rpow (P n).one_lt_N (by norm_num : (0 : ℝ) < 2)).mpr
      simpa only [Real.rpow_one] using hN n
    have hnine : Real.logb (P n).N 9 ≤ 4 := by
      apply (Real.logb_le_iff_le_rpow (P n).one_lt_N (by norm_num : (0 : ℝ) < 9)).mpr
      have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (hN n) 4
      rw [Real.rpow_ofNat]
      norm_num at hp
      linarith
    exact ⟨⟨hr.1, hx.1⟩, ⟨by dsimp only [f]; linarith [hr.2, hδ n],
      by dsimp only [f]; linarith [hx.2, hδ n]⟩⟩
  obtain ⟨z, hz, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hbounded
  refine ⟨z.1, z.2, hz.1.1, hz.2.1, hz.1.2, hz.2.2, φ, hφ, ?_, ?_⟩
  · simpa only [Function.comp_def, f] using (continuous_fst.tendsto z).comp hlim
  · simpa only [Function.comp_def, f] using (continuous_snd.tendsto z).comp hlim

end TaoTrudgianYang2025
