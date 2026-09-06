import GafniTao.RealEnergyPowerColoring
import RiemannZeta.GuthMaynard.LargeValuesEnergyFinal

/-!
# Powered detector energy consumed by Guth--Maynard Proposition 11.1

This is the energy-preserving powered consumer. The dyadic block selected
after powering is colored independently in all four coordinates of an
additive quadruple; a mere large-cardinality subset is deliberately not used.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Exact finite composition of positive-sign powering, four-coordinate
energy coloring, mixed-to-self discretization, and the real frozen
Guth--Maynard Proposition 11.1. The four selected subfamilies remain explicit
because additive energy is not monotone under a cardinality-only extraction. -/
theorem finite_source_powered_energy_gm_bound
    (epsilon sigma B : Real) (N p : Nat) (a : Nat → Complex)
    (Cp eta L : Real) (W : Finset Real)
    (hepsilon : 0 < epsilon) (hN : 0 < N) (hp : 0 < p)
    (hCp : 0 < Cp) (heta : 0 < eta) (hL : 0 ≤ L)
    (hSep : IsSeparated 1 W) (hBase : InBaseInterval B W)
    (hPow : ∀ m : Nat, 0 < m →
      ‖finitePowCoeff N p (conjugateCoeffs a) m‖ ≤
        Cp * (m : Real) ^ eta)
    (hLarge : ∀ t ∈ W, L ≤ ‖sourceDirichletPoly N a t‖) :
    ∃ Cgm B0 : Real, 0 < Cgm ∧ 4 ≤ B0 ∧
      (B0 ≤ B →
        (∀ r ∈ Finset.range p, (2 ^ r * N ^ p : Real) ≤ B) →
        (∀ r ∈ Finset.range p,
          B ^ (3 / 4 : Real) ≤ (2 ^ r * N ^ p : Real)) →
        (∀ r ∈ Finset.range p,
          (2 ^ r * N ^ p : Real) ^ sigma ≤
            (L ^ p /
              (Cp * ((2 ^ p * N ^ p : Nat) : Real) ^ eta)) / p) →
        ∃ label : Fin 4 → Fin p, ∃ Wi : Fin 4 → Finset Real,
          (∀ i : Fin 4, Wi i ⊆ W) ∧
          (∀ i : Fin 4, IsSeparated 1 (Wi i)) ∧
          (∀ i : Fin 4, InBaseInterval B (Wi i)) ∧
          (∀ i : Fin 4, ∀ n ∈ dyadicInterval
              (2 ^ (label i).val * N ^ p),
            ‖sourceNormalizedFinitePoweredCoeffs N p a Cp eta n‖ ≤ 1) ∧
          (∀ i : Fin 4, ∀ t ∈ Wi i,
            (2 ^ (label i).val * N ^ p : Real) ^ sigma ≤
              ‖sourceDirichletPoly (2 ^ (label i).val * N ^ p)
                (sourceNormalizedFinitePoweredCoeffs N p a Cp eta) t‖) ∧
          4 * (ApproxAddEnergy 1 W : Real) ≤
            ((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card *
              (Cgm * B ^ epsilon *
                (gmEnergyShape sigma B
                    (2 ^ (label 0).val * N ^ p) (Wi 0) +
                  gmEnergyShape sigma B
                    (2 ^ (label 1).val * N ^ p) (Wi 1) +
                  gmEnergyShape sigma B
                    (2 ^ (label 2).val * N ^ p) (Wi 2) +
                  gmEnergyShape sigma B
                    (2 ^ (label 3).val * N ^ p) (Wi 3)))) := by
  obtain ⟨Cgm, B0, hCgm, hB0, hGM⟩ :=
    gmEnergy_prop11_1_native epsilon hepsilon
  refine ⟨Cgm, B0, hCgm, hB0, ?_⟩
  intro hB hMUpper hMLower hThreshold
  have hEach : ∀ t ∈ W, ∃ r ∈ Finset.range p,
      (L ^ p / (Cp * ((2 ^ p * N ^ p : Nat) : Real) ^ eta)) / p ≤
        ‖sourceDirichletPoly (2 ^ r * N ^ p)
          (sourceNormalizedFinitePoweredCoeffs N p a Cp eta) t‖ := by
    intro t ht
    exact exists_source_powered_dyadic_index N p a Cp eta L t
      hN hp hCp hL (hLarge t ht)
  let color : Real → Fin p := fun t =>
    if ht : t ∈ W then
      ⟨Classical.choose (hEach t ht),
        Finset.mem_range.mp (Classical.choose_spec (hEach t ht)).1⟩
    else ⟨0, hp⟩
  letI : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  obtain ⟨label, hColorEnergy⟩ :=
    exists_real_energy_color_classes 1 W color
  let Wi : Fin 4 → Finset Real := fun i =>
    W.filter (fun t => color t = label i)
  have hSubset : ∀ i : Fin 4, Wi i ⊆ W := by
    intro i t ht
    exact (Finset.mem_filter.mp ht).1
  have hSepWi : ∀ i : Fin 4, IsSeparated 1 (Wi i) := by
    intro i x hx y hy hxy
    exact hSep x (hSubset i hx) y (hSubset i hy) hxy
  have hBaseWi : ∀ i : Fin 4, InBaseInterval B (Wi i) := by
    intro i t ht
    exact hBase t (hSubset i ht)
  have hLabelLarge : ∀ i : Fin 4, ∀ t ∈ Wi i,
      (L ^ p / (Cp * ((2 ^ p * N ^ p : Nat) : Real) ^ eta)) / p ≤
        ‖sourceDirichletPoly (2 ^ (label i).val * N ^ p)
          (sourceNormalizedFinitePoweredCoeffs N p a Cp eta) t‖ := by
    intro i t ht
    have htW : t ∈ W := hSubset i ht
    have hColorEq : color t = label i := (Finset.mem_filter.mp ht).2
    have hSpec := Classical.choose_spec (hEach t htW)
    have hIndex : Classical.choose (hEach t htW) = (label i).val := by
      have hFin : (⟨Classical.choose (hEach t htW),
          Finset.mem_range.mp hSpec.1⟩ : Fin p) = label i := by
        simpa [color, htW] using hColorEq
      exact congrArg Fin.val hFin
    rw [← hIndex]
    exact hSpec.2
  have hUnit : ∀ i : Fin 4, ∀ n ∈
      dyadicInterval (2 ^ (label i).val * N ^ p),
      ‖sourceNormalizedFinitePoweredCoeffs N p a Cp eta n‖ ≤ 1 := by
    intro i n hn
    exact norm_sourceNormalizedFinitePoweredCoeffs_le_one hN hCp heta
      (label i).isLt hn hPow
  have hGMLarge : ∀ i : Fin 4, ∀ t ∈ Wi i,
      (2 ^ (label i).val * N ^ p : Real) ^ sigma ≤
        ‖sourceDirichletPoly (2 ^ (label i).val * N ^ p)
          (sourceNormalizedFinitePoweredCoeffs N p a Cp eta) t‖ := by
    intro i t ht
    exact (hThreshold _ (Finset.mem_range.mpr (label i).isLt)).trans
      (hLabelLarge i t ht)
  have hEachGM : ∀ i : Fin 4,
      (ApproxAddEnergy 1 (Wi i) : Real) ≤
        Cgm * B ^ epsilon *
          gmEnergyShape sigma B
            (2 ^ (label i).val * N ^ p) (Wi i) := by
    intro i
    exact hGM (2 ^ (label i).val * N ^ p) B sigma (Wi i)
      (sourceNormalizedFinitePoweredCoeffs N p a Cp eta)
      (Nat.mul_pos (pow_pos (by omega) _) (pow_pos hN p)) hB
      (by exact_mod_cast
        hMUpper _ (Finset.mem_range.mpr (label i).isLt))
      (by exact_mod_cast
        hMLower _ (Finset.mem_range.mpr (label i).isLt))
      (hSepWi i) (hBaseWi i) (hUnit i) (by
        intro t ht
        simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
          hGMLarge i t ht)
  have hMixed := four_mul_mixedApproxAddEnergy_le_window_mul_sum_self
    (eta := (1 : Real)) (hSepWi 0) (hSepWi 1) (hSepWi 2) (hSepWi 3)
  have hColorReal : (ApproxAddEnergy 1 W : Real) ≤
      (p ^ 4 : Real) *
        (MixedApproxAddEnergy 1 (Wi 0) (Wi 1) (Wi 2) (Wi 3) : Real) := by
    have hColorNat : ApproxAddEnergy 1 W ≤ p ^ 4 *
        MixedApproxAddEnergy 1 (Wi 0) (Wi 1) (Wi 2) (Wi 3) := by
      simpa [Wi] using hColorEnergy
    exact_mod_cast hColorNat
  refine ⟨label, Wi, hSubset, hSepWi, hBaseWi, hUnit, hGMLarge, ?_⟩
  rw [Nat.cast_pow]
  calc
    4 * (ApproxAddEnergy 1 W : Real) ≤
        4 * ((p ^ 4 : Real) *
          (MixedApproxAddEnergy 1 (Wi 0) (Wi 1) (Wi 2) (Wi 3) : Real)) := by
      gcongr
    _ = (p ^ 4 : Real) *
        (4 * (MixedApproxAddEnergy 1 (Wi 0) (Wi 1) (Wi 2) (Wi 3) : Real)) := by
      ring
    _ ≤ (p ^ 4 : Real) * (doubleFloorDefectWindow 1).card *
        ((ApproxAddEnergy 1 (Wi 0) : Real) +
          (ApproxAddEnergy 1 (Wi 1) : Real) +
          (ApproxAddEnergy 1 (Wi 2) : Real) +
          (ApproxAddEnergy 1 (Wi 3) : Real)) := by
      calc
        (p : Real) ^ 4 *
            (4 * (MixedApproxAddEnergy 1
              (Wi 0) (Wi 1) (Wi 2) (Wi 3) : Real)) ≤
            (p : Real) ^ 4 *
              ((doubleFloorDefectWindow 1).card *
                ((ApproxAddEnergy 1 (Wi 0) : Real) +
                  (ApproxAddEnergy 1 (Wi 1) : Real) +
                  (ApproxAddEnergy 1 (Wi 2) : Real) +
                  (ApproxAddEnergy 1 (Wi 3) : Real))) :=
          mul_le_mul_of_nonneg_left hMixed (by positivity)
        _ = _ := by ring
    _ ≤ (p ^ 4 : Real) * (doubleFloorDefectWindow 1).card *
        (Cgm * B ^ epsilon *
          (gmEnergyShape sigma B
              (2 ^ (label 0).val * N ^ p) (Wi 0) +
            gmEnergyShape sigma B
              (2 ^ (label 1).val * N ^ p) (Wi 1) +
            gmEnergyShape sigma B
              (2 ^ (label 2).val * N ^ p) (Wi 2) +
            gmEnergyShape sigma B
              (2 ^ (label 3).val * N ^ p) (Wi 3))) := by
      have hFactor : 0 ≤ (p ^ 4 : Real) *
          (doubleFloorDefectWindow 1).card := by positivity
      apply mul_le_mul_of_nonneg_left _ hFactor
      calc
        _ ≤ Cgm * B ^ epsilon *
              gmEnergyShape sigma B
                (2 ^ (label 0).val * N ^ p) (Wi 0) +
            Cgm * B ^ epsilon *
              gmEnergyShape sigma B
                (2 ^ (label 1).val * N ^ p) (Wi 1) +
            Cgm * B ^ epsilon *
              gmEnergyShape sigma B
                (2 ^ (label 2).val * N ^ p) (Wi 2) +
            Cgm * B ^ epsilon *
              gmEnergyShape sigma B
                (2 ^ (label 3).val * N ^ p) (Wi 3) := by
          gcongr <;> apply hEachGM
        _ = _ := by ring

#print axioms finite_source_powered_energy_gm_bound

end

end GafniTao
