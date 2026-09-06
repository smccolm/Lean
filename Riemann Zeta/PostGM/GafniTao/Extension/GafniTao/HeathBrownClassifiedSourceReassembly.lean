import GafniTao.SourceEnergySplitReassembly
import GafniTao.HeathBrownSourceDyadicLowerScale

/-!
# Exhaustive reassembly of one classified Type-I source family

The classification exported by the frozen source decomposition has three
members.  The interior member has a further exact physical split at `Q`,
`Q^2`, and the dyadically selected `P^2`.  This theorem performs that entire
case analysis and reassembles all four-coordinate energy colourings.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

theorem classified_source_family_energy_le
    {sigma U delta u : Real} {Y A r : Nat} {W : Finset Real}
    (hUPos : 0 < U) (hY : 0 < Y) (hAOne : 1 < A)
    (hSeparated : IsSeparated 1 W)
    (hRange : forall t, t ∈ W ->
      U - U ^ delta <= t ∧ t <= 2 * U + U ^ delta)
    (hLarge : forall t, t ∈ W ->
      ((3 / 4 : Real) * (U ^ (-u) / 2)) /
          (Nat.clog 2 A + 1 : Nat) <=
        ‖typeISourceSmoothBlock Y A r sigma t‖)
    (hClassified : r < 2 ∨ A < 2 * (2 ^ r * Y) ∨
      (((Y + 1 : Nat) : Real) <= ((2 ^ r * Y : Nat) : Real) / 2 ∧
        2 * (2 ^ r * Y) <= A))
    {M : Real} (hM : 0 <= M)
    (hTerminal : 2 <= r -> A < 2 * (2 ^ r * Y) -> False)
    (hLower : forall {P : Nat} (W' : Finset Real),
      W' ⊆ W -> r < 2 ->
      P < 2 * (2 ^ r * Y) -> 2 ^ r * Y < 4 * P ->
      W'.Nonempty -> IsSeparated 1 W' ->
      (forall t, t ∈ W' -> U - U ^ delta <= t ∧
        t <= 2 * U + U ^ delta) ->
      (forall t, t ∈ W' ->
        (((((2 ^ r * Y : Nat) : Real) / 2) ^ sigma) *
          (((3 / 4 : Real) * (U ^ (-u) / 2)) /
            (Nat.clog 2 A + 1 : Nat))) /
          (Nat.clog 2 (A + 1) : Real) <=
        ‖dirichletPoly P
          (normalizedTypeISourceDirichletCoeff Y A r sigma) t‖) ->
      (ApproxAddEnergy 1 W' : Real) <= M)
    (hWide : forall {P : Nat} (W' : Finset Real),
      W' ⊆ W -> U <= (2 ^ r * Y : Nat) ->
      P < 2 * (2 ^ r * Y) -> 2 ^ r * Y < 4 * P ->
      2 * (2 ^ r * Y) <= A ->
      W'.Nonempty -> IsSeparated 1 W' ->
      (forall t, t ∈ W' -> U - U ^ delta <= t ∧
        t <= 2 * U + U ^ delta) ->
      (forall t, t ∈ W' ->
        (((((2 ^ r * Y : Nat) : Real) / 2) ^ sigma) *
          (((3 / 4 : Real) * (U ^ (-u) / 2)) /
            (Nat.clog 2 A + 1 : Nat))) /
          (Nat.clog 2 (A + 1) : Real) <=
        ‖dirichletPoly P
          (normalizedTypeISourceDirichletCoeff Y A r sigma) t‖) ->
      (ApproxAddEnergy 1 W' : Real) <= M)
    (hSquare : forall {P : Nat} (W' : Finset Real),
      W' ⊆ W -> (2 ^ r * Y : Real) ^ 2 <= U ->
      (P : Real) ^ 2 <= U -> P < 2 * (2 ^ r * Y) ->
      2 ^ r * Y < 4 * P -> W'.Nonempty -> IsSeparated 1 W' ->
      (forall t, t ∈ W' -> U - U ^ delta <= t ∧
        t <= 2 * U + U ^ delta) ->
      (forall t, t ∈ W' ->
        (((((2 ^ r * Y : Nat) : Real) / 2) ^ sigma) *
          (((3 / 4 : Real) * (U ^ (-u) / 2)) /
            (Nat.clog 2 A + 1 : Nat))) /
          (Nat.clog 2 (A + 1) : Real) <=
        ‖dirichletPoly P
          (normalizedTypeISourceDirichletCoeff Y A r sigma) t‖) ->
      (ApproxAddEnergy 1 W' : Real) <= M)
    (hTransition : forall {P : Nat} (W' : Finset Real),
      W' ⊆ W -> (2 ^ r * Y : Real) ^ 2 <= U ->
      U < (P : Real) ^ 2 -> (P : Real) ^ 2 <= 4 * U ->
      P < 2 * (2 ^ r * Y) -> 2 ^ r * Y < 4 * P ->
      W'.Nonempty -> IsSeparated 1 W' ->
      (forall t, t ∈ W' -> U - U ^ delta <= t ∧
        t <= 2 * U + U ^ delta) ->
      (forall t, t ∈ W' ->
        (((((2 ^ r * Y : Nat) : Real) / 2) ^ sigma) *
          (((3 / 4 : Real) * (U ^ (-u) / 2)) /
            (Nat.clog 2 A + 1 : Nat))) /
          (Nat.clog 2 (A + 1) : Real) <=
        ‖dirichletPoly P
          (normalizedTypeISourceDirichletCoeff Y A r sigma) t‖) ->
      (ApproxAddEnergy 1 W' : Real) <= M)
    (hReflected : forall {tau : Real},
      tau = typeILogarithmicScale U (2 ^ r * Y) ->
      1 < tau -> tau < 2 -> 2 <= r -> 2 * (2 ^ r * Y) <= A ->
      (ApproxAddEnergy 1 W : Real) <=
        (((Nat.clog 2 (A + 1)) ^ 4 : Nat) : Real) *
          (doubleFloorDefectWindow 1).card * M) :
    (ApproxAddEnergy 1 W : Real) <=
      (((Nat.clog 2 (A + 1)) ^ 4 : Nat) : Real) *
        (doubleFloorDefectWindow 1).card * M := by
  by_cases hLowerClass : r < 2
  · obtain ⟨split⟩ := source_smooth_dyadic_energy_split Y A r sigma
      (((3 / 4 : Real) * (U ^ (-u) / 2)) /
        (Nat.clog 2 A + 1 : Nat)) W hY hAOne (by positivity)
      hSeparated hLarge
    apply split.energy_le_of_all_cells
    intro i
    by_cases hNonempty : (split.Ws i).Nonempty
    · exact hLower (split.Ws i) (split.hSubset i) hLowerClass
        (split.hScaleUpper i hNonempty) (split.hScaleLower i hNonempty)
        hNonempty (split.hSeparated i)
        (fun t ht => hRange t (split.hSubset i ht)) (split.hLarge i)
    · have hEmpty : split.Ws i = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hNonempty
      rw [hEmpty]
      simpa [ApproxAddEnergy, approximateAdditiveQuadruples] using hM
  · rcases hClassified with hImpossible | hTerminalClass | hInteriorClass
    · exact False.elim (hLowerClass hImpossible)
    · exact False.elim (hTerminal (by omega) hTerminalClass)
    · let Q : Nat := 2 ^ r * Y
      have hrTwo : 2 <= r := by omega
      by_cases hUQ : U <= (Q : Real)
      · obtain ⟨split⟩ := source_smooth_dyadic_energy_split Y A r sigma
          (((3 / 4 : Real) * (U ^ (-u) / 2)) /
            (Nat.clog 2 A + 1 : Nat)) W hY hAOne (by positivity)
          hSeparated hLarge
        apply split.energy_le_of_all_cells
        intro i
        by_cases hNonempty : (split.Ws i).Nonempty
        · apply hWide (P := 2 ^ ((split.scale i : Fin _) : Nat))
              (split.Ws i)
          · exact split.hSubset i
          · simpa only [Q] using hUQ
          · exact split.hScaleUpper i hNonempty
          · exact split.hScaleLower i hNonempty
          · simpa only [Q] using hInteriorClass.2
          · exact hNonempty
          · exact split.hSeparated i
          · exact fun t ht => hRange t (split.hSubset i ht)
          · exact split.hLarge i
        · have hEmpty : split.Ws i = ∅ :=
            Finset.not_nonempty_iff_eq_empty.mp hNonempty
          rw [hEmpty]
          simpa [ApproxAddEnergy, approximateAdditiveQuadruples] using hM
      · have hQU : (Q : Real) < U := lt_of_not_ge hUQ
        by_cases hUQsq : U < (Q : Real) ^ 2
        · let tau := typeILogarithmicScale U Q
          have hQOne : 1 < Q := by
            have hPow : 4 <= 2 ^ r := by
              have h := Nat.pow_le_pow_right (by omega : 0 < (2 : Nat)) hrTwo
              norm_num at h
              exact h
            have hFourY : 4 * Y <= Q := by
              dsimp only [Q]
              exact Nat.mul_le_mul_right Y hPow
            have hYOne : 1 <= Y := hY
            omega
          have hScale : (Q : Real) ^ tau = U := by
            dsimp only [tau]
            exact rpow_typeILogarithmicScale_eq hUPos hQOne
          have hBaseOne : (1 : Real) < (Q : Real) := by
            exact_mod_cast hQOne
          have hTauOne : 1 < tau := by
            apply (Real.strictMono_rpow_of_base_gt_one hBaseOne).lt_iff_lt.mp
            simpa only [Real.rpow_one, hScale] using hQU
          have hTauTwo : tau < 2 := by
            apply (Real.strictMono_rpow_of_base_gt_one hBaseOne).lt_iff_lt.mp
            simpa only [Real.rpow_two, hScale] using hUQsq
          exact hReflected (by rfl) hTauOne hTauTwo hrTwo
            (by simpa only [Q] using hInteriorClass.2)
        · have hQsqU : (Q : Real) ^ 2 <= U := le_of_not_gt hUQsq
          obtain ⟨split⟩ := source_smooth_dyadic_energy_split Y A r sigma
            (((3 / 4 : Real) * (U ^ (-u) / 2)) /
              (Nat.clog 2 A + 1 : Nat)) W hY hAOne (by positivity)
            hSeparated hLarge
          apply split.energy_le_of_all_cells
          intro i
          by_cases hNonempty : (split.Ws i).Nonempty
          · let P : Nat := 2 ^ ((split.scale i : Fin _) : Nat)
            have hPUpper : P < 2 * Q := by
              simpa only [P, Q] using split.hScaleUpper i hNonempty
            have hPLower : Q < 4 * P := by
              simpa only [P, Q] using split.hScaleLower i hNonempty
            by_cases hPsq : (P : Real) ^ 2 <= U
            · apply hSquare (P := P) (split.Ws i)
              · exact split.hSubset i
              · simpa only [Q, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hQsqU
              · exact hPsq
              · simpa only [P, Q] using hPUpper
              · simpa only [P, Q] using hPLower
              · exact hNonempty
              · exact split.hSeparated i
              · exact fun t ht => hRange t (split.hSubset i ht)
              · simpa only [P] using split.hLarge i
            · have hUPsq : U < (P : Real) ^ 2 := lt_of_not_ge hPsq
              have hPtwoQ : (P : Real) < 2 * (Q : Real) := by
                exact_mod_cast hPUpper
              have hPsqFour : (P : Real) ^ 2 <= 4 * U := by
                nlinarith [sq_nonneg ((P : Real) - 2 * Q)]
              apply hTransition (P := P) (split.Ws i)
              · exact split.hSubset i
              · simpa only [Q, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hQsqU
              · exact hUPsq
              · exact hPsqFour
              · simpa only [P, Q] using hPUpper
              · simpa only [P, Q] using hPLower
              · exact hNonempty
              · exact split.hSeparated i
              · exact fun t ht => hRange t (split.hSubset i ht)
              · simpa only [P] using split.hLarge i
          · have hEmpty : split.Ws i = ∅ :=
              Finset.not_nonempty_iff_eq_empty.mp hNonempty
            rw [hEmpty]
            simpa [ApproxAddEnergy, approximateAdditiveQuadruples] using hM

#print axioms classified_source_family_energy_le

end

end GafniTao
