import TaoTrudgianYang2025.ClassicalGlobalInteriorSource

/-!
# Pointwise exclusion of terminal global source blocks

The native terminal estimate is applied to a singleton only to exclude
one actual ordinate. The resulting statement makes every terminal
indexed fiber empty; it does not replace an energy family by a subset.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem eventually_no_terminal_global_source_point
    (s d u : ℝ) (hs : 1/2 < s) (hd : d < 1) (hu : u < s-1/2) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ (T t : ℝ) (Y A r : ℕ), T₀ ≤ T →
      A = ⌊sharpZetaCutoff T⌋₊ → 0 < Y → 2 ≤ r → A < 2*(2^r*Y) →
      T-T^d ≤ t → t ≤ 2*T+T^d →
      ((3/4)*(T^(-u)/2))/(Nat.clog 2 A+1 : ℕ) ≤
        ‖typeISourceSmoothBlock Y A r s t‖ → False := by
  classical
  obtain ⟨Tterminal,hTterminal,hTerminal⟩ :=
    eventually_no_terminal_classified_source (d := d) hs hu
  obtain ⟨Tdisp,_hTdisp,hDisp⟩ := eventually_rpow_le_half_self d hd
  refine ⟨max Tterminal Tdisp,hTterminal.trans (le_max_left _ _),?_⟩
  intro T t Y A r hT hA hY hr hEdge hLower hUpper hLarge
  apply hTerminal T Y A r {t} ((le_max_left _ _).trans hT) hA hY hr hEdge
  · exact Finset.singleton_nonempty t
  · simp [IsSeparated]
  · simpa only [Finset.mem_singleton,forall_eq] using hLarge
  · simpa only [Finset.mem_singleton,forall_eq] using And.intro hLower hUpper
  · exact hDisp T ((le_max_right _ _).trans hT)

theorem eventually_terminal_global_source_index_isEmpty
    (s d u : ℝ) (hs : 1/2 < s) (hd : d < 1) (hu : u < s-1/2) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ {ι : Type*} (T : ℝ) (Y A r : ℕ) (W : ι → ℝ),
      T₀ ≤ T → A = ⌊sharpZetaCutoff T⌋₊ → 0 < Y → 2 ≤ r →
      A < 2*(2^r*Y) →
      (∀ x, T-T^d ≤ W x ∧ W x ≤ 2*T+T^d) →
      (∀ x, ((3/4)*(T^(-u)/2))/(Nat.clog 2 A+1 : ℕ) ≤
        ‖typeISourceSmoothBlock Y A r s (W x)‖) → IsEmpty ι := by
  obtain ⟨T₀,hT₀,hPoint⟩ := eventually_no_terminal_global_source_point s d u hs hd hu
  refine ⟨T₀,hT₀,?_⟩
  intro ι T Y A r W hT hA hY hr hEdge hRange hLarge
  exact ⟨fun x => hPoint T (W x) Y A r hT hA hY hr hEdge
    (hRange x).1 (hRange x).2 (hLarge x)⟩

end TaoTrudgianYang2025
