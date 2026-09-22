import TaoTrudgianYang2025.BourgainDiagonalLoss
import TaoTrudgianYang2025.BourgainSliceCompactness

/-!
# Actual source families on Bourgain's large branch

This witness structure records actual patterns, retained source subsets and
complete integer slices. The constructor below derives every field from
region membership and the proved finite analytic alternative.
-/

open Filter Set Topology RiemannZeta.GuthMaynard
open scoped Classical

noncomputable section

namespace TaoTrudgianYang2025

structure BourgainDiagonalFamily (σ τ χ α ρ : ℝ) where
  pattern : ℕ → LargeValuePattern
  retained : ℕ → Finset ℝ
  localHeight : ℕ → ℝ
  sliceValue : ℕ → ℝ
  shift : ℕ → ℝ
  accuracy : ℕ → ℝ
  delta : ℕ → ℝ
  scale_top : Tendsto (fun n => (pattern n).N) atTop atTop
  source_log : Tendsto (fun n => Real.logb (pattern n).N
    ((pattern n).ordinates.card : ℝ)) atTop (nhds ρ)
  accuracy_pos : ∀ n, 0 < accuracy n
  accuracy_le : ∀ n, accuracy n ≤ 1
  accuracy_zero : Tendsto accuracy atTop (nhds 0)
  delta_nonneg : ∀ n, 0 ≤ delta n
  delta_le : ∀ n, delta n ≤ accuracy n
  scale_two : ∀ n, 2 ≤ (pattern n).N
  retained_nonempty : ∀ n, (retained n).Nonempty
  retained_subset : ∀ n, retained n ⊆ (pattern n).ordinates
  retained_separated : ∀ n, IsSeparated 1 (retained n)
  retained_large : ∀ n, ∀ t ∈ retained n,
    (pattern n).V ≤ ‖∑ j ∈ (pattern n).indices, (pattern n).coeff j*dirichletPhase j t‖
  local_eq : ∀ n, localHeight n = (pattern n).T/(pattern n).N^χ
  scale_le_local : ∀ n, (pattern n).N ≤ localHeight n
  local_le_time : ∀ n, localHeight n ≤ (pattern n).T
  time_upper : ∀ n, (pattern n).T ≤ (pattern n).N^(τ+delta n)
  local_upper : ∀ n, localHeight n ≤ (pattern n).N^((τ-χ)+delta n)
  shift_mem : ∀ n, shift n ∈ Icc (-((pattern n).N^(accuracy n/8)))
    ((pattern n).N^(accuracy n/8))
  slice_nonempty : ∀ n, (bourgainIntegerSlice ((pattern n).N^(accuracy n/8))
    (localHeight n+(pattern n).N^(accuracy n/8)+1) (sliceValue n) (shift n)).Nonempty
  packing : ∀ n,
    Real.logb (pattern n).N ((pattern n).ordinates.card : ℝ) ≤ accuracy n+
      max (bourgainSmallExponent σ τ α χ+accuracy n)
        (2*accuracy n+Real.logb (pattern n).N ((retained n).card : ℝ))
  comparison : ∀ n,
    let r := Real.logb (pattern n).N ((retained n).card : ℝ)
    let x := Real.logb (pattern n).N
      ((bourgainIntegerSlice ((pattern n).N^(accuracy n/8))
        (localHeight n+(pattern n).N^(accuracy n/8)+1) (sliceValue n) (shift n)).card : ℝ)
    max (-2*α+2*σ+x+r) (-α-χ/2+2*σ+x/2+3*r/2) ≤
      (2*τ-χ+12)*accuracy n+heathBrownDoubleZetaExponent τ r/2+
        heathBrownDoubleZetaExponent τ x/2

/-- A strict gap above the small-branch bound selects the genuine large branch
on a tail of actual region realizations. No branch stability is assumed. -/
theorem exists_bourgain_diagonal_family {σ τ χ α ρ energy : ℝ}
    (hregion : InCardinalityEnergyRegion σ τ ρ energy)
    (hσ : 3/4 < σ) (hχ : 0 ≤ χ) (hmargin : 1 < τ-χ)
    (hgap : bourgainSmallExponent σ τ α χ < ρ) :
    Nonempty (BourgainDiagonalFamily σ τ χ α ρ) := by
  have he₈ (n : ℕ) : poweringAccuracy n ≤ 8 := (poweringAccuracy_le n).trans (by norm_num)
  have he₁ (n : ℕ) : poweringAccuracy n ≤ 1 := (poweringAccuracy_le n).trans (by norm_num)
  have hex (n : ℕ) := bourgain_linked_logarithmic_comparison
    (α := α) hσ hχ hmargin (poweringAccuracy_pos n) (poweringAccuracy_pos n)
    (poweringAccuracy_pos n) (poweringAccuracy_pos n) (poweringAccuracy_pos n) (he₈ n)
  choose B C δ K G H N₀ hB hC hδ hδ₁ hδmargin hδε hK hG hH hN₀ hf using hex
  let A : ℕ → Fin 5 → ℝ := fun n => ![G n, 2*G n, 3*K n, 6*C n, 6*C n+C n*H n]
  let R : ℕ → ℝ := fun n => max (C n) (max (N₀ n)
    (∑ i, Real.exp (|Real.log (A n i)|/poweringAccuracy n+1)))
  obtain ⟨P, hNtop, hρ, hP⟩ := exists_bourgain_region_family hregion δ R hδ
  have hthreshold (n : ℕ) : C n ≤ (P n).N ∧ N₀ n ≤ (P n).N ∧
      (∑ i, Real.exp (|Real.log (A n i)|/poweringAccuracy n+1)) ≤ (P n).N := by
    simpa only [R, max_le_iff] using (hP n).2.1
  have hA (n : ℕ) (i : Fin 5) : |Real.logb (P n).N (A n i)| ≤ poweringAccuracy n :=
    bourgain_abs_logb_le_of_sum_threshold (A n) (P n).one_lt_N
      (poweringAccuracy_pos n) (hthreshold n).2.2 i
  have hsmall (n : ℕ) : Real.logb (P n).N (6*C n) ≤ poweringAccuracy n := by
    have ht := (le_abs_self (Real.logb (P n).N (A n 3))).trans (hA n 3)
    simpa only [A, Matrix.cons_val_succ, Matrix.cons_val_zero] using ht
  have heLim : Tendsto (fun n => bourgainSmallExponent σ τ α χ+2*poweringAccuracy n)
      atTop (nhds (bourgainSmallExponent σ τ α χ)) := by
    simpa using (poweringAccuracy_tendsto.const_mul 2).const_add
      (bourgainSmallExponent σ τ α χ)
  obtain ⟨n₀, hn₀⟩ := (heLim.eventually_lt hρ hgap).exists_forall_of_atTop
  let L : ℕ → ℝ := fun n => (P n).T/(P n).N^χ
  have hgeom (n : ℕ) : (P n).N ≤ L n ∧ L n ≤ (P n).T ∧
      L n ≤ (P n).N^((τ-χ)+δ n) := by
    have hs := bourgain_subdivision_physical_scales (P n).one_lt_N hχ
      (by linarith [hδmargin n] : 1+δ n ≤ τ-χ) (hP n).2.2.1 (hP n).2.2.2.1
    exact ⟨hs.2.1, hs.2.2.1, hs.2.2.2.2⟩
  have hlarge (n : ℕ) (hn : n₀ ≤ n) :
      ∃ S : Finset ℝ, ∃ V u : ℝ,
        S ⊆ (P n).ordinates ∧ S.Nonempty ∧ IsSeparated 1 S ∧
        (∀ t ∈ S, (P n).V ≤ ‖∑ j ∈ (P n).indices, (P n).coeff j*dirichletPhase j t‖) ∧
        u ∈ Icc (-((P n).N^(poweringAccuracy n/8))) ((P n).N^(poweringAccuracy n/8)) ∧
        (bourgainIntegerSlice ((P n).N^(poweringAccuracy n/8))
          (L n+(P n).N^(poweringAccuracy n/8)+1) V u).Nonempty ∧
        Real.logb (P n).N ((P n).ordinates.card : ℝ) ≤ poweringAccuracy n+
          max (bourgainSmallExponent σ τ α χ+poweringAccuracy n)
            (2*poweringAccuracy n+Real.logb (P n).N (S.card : ℝ)) ∧
        let r := Real.logb (P n).N (S.card : ℝ)
        let x := Real.logb (P n).N ((bourgainIntegerSlice ((P n).N^(poweringAccuracy n/8))
          (L n+(P n).N^(poweringAccuracy n/8)+1) V u).card : ℝ)
        max (-2*α+2*σ+x+r) (-α-χ/2+2*σ+x/2+3*r/2) ≤
          (2*τ-χ+12)*poweringAccuracy n+heathBrownDoubleZetaExponent τ r/2+
            heathBrownDoubleZetaExponent τ x/2 := by
    have halt := hf n (P n) (L n) (hP n).2.2.2.2.2.1
      (hthreshold n).1 (hthreshold n).2.1 rfl
      (hP n).2.2.1 (hP n).2.2.2.1 (hP n).2.2.2.2.1
    rcases halt with hfirst | ⟨S, hsub, hS, hsep, hvalues, _, _, hpack,
      q, hq, u, hu, hZ, _, _, hcomp⟩
    · exfalso
      have hg := hn₀ n hn
      have hc := hsmall n
      linarith
    · refine ⟨S, _, u, hsub, hS, hsep, hvalues, ⟨hu.1.le, hu.2⟩, hZ, ?_, ?_⟩
      · have hc : Real.logb (P n).N (6*C n+C n*H n) ≤ poweringAccuracy n := by
          have ht := (le_abs_self (Real.logb (P n).N (A n 4))).trans (hA n 4)
          simpa only [A, Matrix.cons_val_succ, Matrix.cons_val_zero] using ht
        have hp := hpack.trans (add_le_add hc le_rfl)
        simpa only [show poweringAccuracy n+poweringAccuracy n =
          2*poweringAccuracy n by ring] using hp
      · apply bourgain_diagonal_comparison (by linarith : 0 ≤ τ-χ)
          (poweringAccuracy_pos n) (he₁ n) (hδ n).le (hδε n)
        · simpa only [A, Matrix.cons_val_zero] using
            (le_abs_self (Real.logb (P n).N (A n 0))).trans (hA n 0)
        · simpa only [A, Matrix.cons_val_succ, Matrix.cons_val_zero] using
            (le_abs_self (Real.logb (P n).N (A n 1))).trans (hA n 1)
        · simpa only [A, Matrix.cons_val_succ, Matrix.cons_val_zero] using
            (le_abs_self (Real.logb (P n).N (A n 2))).trans (hA n 2)
        · exact hcomp.le
  have hselected (n : ℕ) := hlarge (n+n₀) (Nat.le_add_left _ _)
  choose S V u hsub hS hsep hvalues hu hZ hpack hcomp using hselected
  refine ⟨{
    pattern := fun n => P (n+n₀)
    retained := S
    localHeight := fun n => L (n+n₀)
    sliceValue := V
    shift := u
    accuracy := fun n => poweringAccuracy (n+n₀)
    delta := fun n => δ (n+n₀)
    scale_top := hNtop.comp (tendsto_add_atTop_nat n₀)
    source_log := hρ.comp (tendsto_add_atTop_nat n₀)
    accuracy_pos := fun n => poweringAccuracy_pos (n+n₀)
    accuracy_le := fun n => he₁ (n+n₀)
    accuracy_zero := poweringAccuracy_tendsto.comp (tendsto_add_atTop_nat n₀)
    delta_nonneg := fun n => (hδ (n+n₀)).le
    delta_le := fun n => hδε (n+n₀)
    scale_two := fun n => (hP (n+n₀)).1
    retained_nonempty := hS
    retained_subset := hsub
    retained_separated := hsep
    retained_large := hvalues
    local_eq := fun _ => rfl
    scale_le_local := fun n => (hgeom (n+n₀)).1
    local_le_time := fun n => (hgeom (n+n₀)).2.1
    time_upper := fun n => (hP (n+n₀)).2.2.2.1
    local_upper := fun n => (hgeom (n+n₀)).2.2
    shift_mem := hu
    slice_nonempty := hZ
    packing := hpack
    comparison := hcomp }⟩

end TaoTrudgianYang2025
