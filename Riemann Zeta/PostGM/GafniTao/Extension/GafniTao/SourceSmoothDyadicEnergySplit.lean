import GafniTao.SharpTypeISmoothEnergySplit
import RiemannZeta.GuthMaynard.MediumTypeIEndpoint

/-!
# Energy-safe dyadic extraction from a source-smooth Type-I block

The frozen endpoint development extracts one ordinary dyadic polynomial from
a source-smooth block on a large subfamily.  For zero additive energy the
choice must instead be made independently in all four coordinates of an
additive quadruple.  This file performs that finite colouring and then uses
the exact mixed-to-self comparison.  The selected polynomials, normalization,
and two physical scale inequalities are the literal outputs of the frozen
source extraction.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Singleton form of the frozen source-block extraction.  It is the choice
function used by the four-coordinate energy colouring below. -/
theorem exists_pointwise_normalized_source_dyadic_block
    {Y A r : Nat} {sigma V t : Real}
    (hY : 0 < Y) (hA : 1 < A) (hV : 0 < V)
    (hLarge : V <= ‖typeISourceSmoothBlock Y A r sigma t‖) :
    let k := Nat.clog 2 (A + 1)
    ∃ j : Fin k,
      (((((2 ^ r * Y : Nat) : Real) / 2) ^ sigma) * V) / k <=
        ‖dirichletPoly (2 ^ (j : Nat))
          (normalizedTypeISourceDirichletCoeff Y A r sigma) t‖ ∧
      2 ^ (j : Nat) < 2 * (2 ^ r * Y) ∧
      2 ^ r * Y < 4 * 2 ^ (j : Nat) := by
  dsimp only
  let k := Nat.clog 2 (A + 1)
  have hk : 0 < k := Nat.clog_pos Nat.one_lt_two (by omega)
  have hSingleton : ({t} : Finset Real).Nonempty := by simp
  have hSeparated : IsSeparated 1 ({t} : Finset Real) := by
    intro x hx y hy hxy
    simp only [Finset.mem_singleton] at hx hy
    exact False.elim (hxy (hx.trans hy.symm))
  have hLargeSingleton : ∀ s ∈ ({t} : Finset Real),
      V <= ‖typeISourceSmoothBlock Y A r sigma s‖ := by
    intro s hs
    have hst : s = t := by simpa only [Finset.mem_singleton] using hs
    subst s
    exact hLarge
  obtain ⟨j, hj, W', hW'sub, _hSep, hCard, hLarge', hUpper, hLower⟩ :=
    extract_normalized_source_dyadic_block ({t} : Finset Real)
      hY hA hV hSingleton hSeparated hLargeSingleton
  have hW' : W'.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hEmpty
    have hCardZero : W'.card = 0 := by simp [hEmpty]
    simp only [Finset.card_singleton, hCardZero, Nat.cast_zero, mul_zero] at hCard
    norm_num at hCard
  obtain ⟨s, hs⟩ := hW'
  have hst : s = t := by simpa only [Finset.mem_singleton] using hW'sub hs
  subst s
  let jf : Fin k := ⟨j, Finset.mem_range.mp hj⟩
  refine ⟨jf, ?_, ?_, ?_⟩
  · simpa only [jf, k] using hLarge' t hs
  · simpa only [jf] using hUpper
  · simpa only [jf] using hLower

/-- Four independently selected dyadic blocks controlling the additive energy
of one actual source-smooth family. -/
structure SourceSmoothDyadicEnergyOutput
    (Y A r : Nat) (sigma V : Real) (W : Finset Real) where
  scale : Fin 4 -> Fin (Nat.clog 2 (A + 1))
  Ws : Fin 4 -> Finset Real
  hSubset : ∀ i : Fin 4, Ws i ⊆ W
  hSeparated : ∀ i : Fin 4, IsSeparated 1 (Ws i)
  hLarge : ∀ i : Fin 4, ∀ t, t ∈ Ws i ->
    (((((2 ^ r * Y : Nat) : Real) / 2) ^ sigma) * V) /
        Nat.clog 2 (A + 1) <=
      ‖dirichletPoly (2 ^ ((scale i : Fin _) : Nat))
        (normalizedTypeISourceDirichletCoeff Y A r sigma) t‖
  hScaleUpper : ∀ i : Fin 4, (Ws i).Nonempty ->
    2 ^ ((scale i : Fin _) : Nat) < 2 * (2 ^ r * Y)
  hScaleLower : ∀ i : Fin 4, (Ws i).Nonempty ->
    2 ^ r * Y < 4 * 2 ^ ((scale i : Fin _) : Nat)
  hEnergy :
    4 * (ApproxAddEnergy 1 W : Real) <=
      (((Nat.clog 2 (A + 1)) ^ 4 : Nat) : Real) *
        (doubleFloorDefectWindow 1).card *
        ((ApproxAddEnergy 1 (Ws 0) : Real) +
          (ApproxAddEnergy 1 (Ws 1) : Real) +
          (ApproxAddEnergy 1 (Ws 2) : Real) +
          (ApproxAddEnergy 1 (Ws 3) : Real))

/-- Exact energy-safe version of the frozen source-smooth dyadic extraction. -/
theorem source_smooth_dyadic_energy_split
    (Y A r : Nat) (sigma V : Real) (W : Finset Real)
    (hY : 0 < Y) (hA : 1 < A) (hV : 0 < V)
    (hSeparated : IsSeparated 1 W)
    (hLarge : ∀ t ∈ W, V <= ‖typeISourceSmoothBlock Y A r sigma t‖) :
    Nonempty (SourceSmoothDyadicEnergyOutput Y A r sigma V W) := by
  classical
  let k := Nat.clog 2 (A + 1)
  have hk : 0 < k := Nat.clog_pos Nat.one_lt_two (by omega)
  have hEach : ∀ t, t ∈ W -> ∃ j : Fin k,
      (((((2 ^ r * Y : Nat) : Real) / 2) ^ sigma) * V) / k <=
        ‖dirichletPoly (2 ^ (j : Nat))
          (normalizedTypeISourceDirichletCoeff Y A r sigma) t‖ ∧
      2 ^ (j : Nat) < 2 * (2 ^ r * Y) ∧
      2 ^ r * Y < 4 * 2 ^ (j : Nat) := by
    intro t ht
    simpa only [k] using exists_pointwise_normalized_source_dyadic_block
      hY hA hV (hLarge t ht)
  let selected : Real -> Fin k := fun t =>
    if ht : t ∈ W then Classical.choose (hEach t ht) else ⟨0, hk⟩
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨label, hEnergyNat⟩ := exists_real_energy_color_classes 1 W selected
  let Ws : Fin 4 -> Finset Real := fun i =>
    W.filter (fun t => selected t = label i)
  have hSub : ∀ i : Fin 4, Ws i ⊆ W := fun i => Finset.filter_subset _ _
  have hSep : ∀ i : Fin 4, IsSeparated 1 (Ws i) := by
    intro i x hx y hy hxy
    exact hSeparated x (hSub i hx) y (hSub i hy) hxy
  have hSelected : ∀ i : Fin 4, ∀ t, t ∈ Ws i -> selected t = label i := by
    intro i t ht
    exact (Finset.mem_filter.mp ht).2
  have hSpec : ∀ i : Fin 4, ∀ t, t ∈ Ws i ->
      (((((2 ^ r * Y : Nat) : Real) / 2) ^ sigma) * V) / k <=
        ‖dirichletPoly (2 ^ ((label i : Fin k) : Nat))
          (normalizedTypeISourceDirichletCoeff Y A r sigma) t‖ ∧
      2 ^ ((label i : Fin k) : Nat) < 2 * (2 ^ r * Y) ∧
      2 ^ r * Y < 4 * 2 ^ ((label i : Fin k) : Nat) := by
    intro i t ht
    have htW := hSub i ht
    have hChosen := Classical.choose_spec (hEach t htW)
    have hEq : Classical.choose (hEach t htW) = label i := by
      have hAt := hSelected i t ht
      simpa only [selected, dif_pos htW] using hAt
    simpa only [hEq] using hChosen
  have hMixed := four_mul_mixedApproxAddEnergy_le_window_mul_sum_self
    (eta := 1) (W0 := Ws 0) (W1 := Ws 1) (W2 := Ws 2) (W3 := Ws 3)
    (hSep 0) (hSep 1) (hSep 2) (hSep 3)
  have hColored : (ApproxAddEnergy 1 W : Real) <=
      ((k ^ 4 : Nat) : Real) *
        (MixedApproxAddEnergy 1 (Ws 0) (Ws 1) (Ws 2) (Ws 3) : Real) := by
    have hEnergyNat' : ApproxAddEnergy 1 W <=
        k ^ 4 * MixedApproxAddEnergy 1 (Ws 0) (Ws 1) (Ws 2) (Ws 3) := by
      simpa only [Fintype.card_fin, Ws] using hEnergyNat
    exact_mod_cast hEnergyNat'
  have hFinal : 4 * (ApproxAddEnergy 1 W : Real) <=
      ((k ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card *
        ((ApproxAddEnergy 1 (Ws 0) : Real) +
          (ApproxAddEnergy 1 (Ws 1) : Real) +
          (ApproxAddEnergy 1 (Ws 2) : Real) +
          (ApproxAddEnergy 1 (Ws 3) : Real)) := by
    calc
      4 * (ApproxAddEnergy 1 W : Real) <=
          ((k ^ 4 : Nat) : Real) *
            (4 * (MixedApproxAddEnergy 1
              (Ws 0) (Ws 1) (Ws 2) (Ws 3) : Real)) := by
        nlinarith [hColored]
      _ <= ((k ^ 4 : Nat) : Real) *
          ((doubleFloorDefectWindow 1).card *
            ((ApproxAddEnergy 1 (Ws 0) : Real) +
              (ApproxAddEnergy 1 (Ws 1) : Real) +
              (ApproxAddEnergy 1 (Ws 2) : Real) +
              (ApproxAddEnergy 1 (Ws 3) : Real))) := by
        gcongr
      _ = _ := by ring
  exact ⟨⟨label, Ws, hSub, hSep,
    fun i t ht => (hSpec i t ht).1,
    fun i hi => by
      obtain ⟨t, ht⟩ := hi
      exact (hSpec i t ht).2.1,
    fun i hi => by
      obtain ⟨t, ht⟩ := hi
      exact (hSpec i t ht).2.2,
    hFinal⟩⟩

#print axioms exists_pointwise_normalized_source_dyadic_block
#print axioms SourceSmoothDyadicEnergyOutput
#print axioms source_smooth_dyadic_energy_split

end

end GafniTao
