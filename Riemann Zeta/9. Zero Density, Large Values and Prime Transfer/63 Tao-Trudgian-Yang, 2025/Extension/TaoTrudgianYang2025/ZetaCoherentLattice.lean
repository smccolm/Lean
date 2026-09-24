import TaoTrudgianYang2025.ZetaCoherentPattern
import TaoTrudgianYang2025.LargeValueRandomLattice
import TaoTrudgianYang2025.ZetaIntervalCutoff

/-! Genuine coefficient-one patterns on a full translated, separated lattice. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem exists_coherentZetaLatticePattern
    (N L : ℕ) (hN : 1 < N) (hL : 0 < L) (hLN : L ≤ N)
    (T : ℝ) (hT : 0 < T) (hheight : 2*T ≤ (N : ℝ)/(2*(L : ℝ))) :
    ∃ P : ZetaLargeValuePattern, P.N = (N : ℝ) ∧ P.T = T ∧
      P.V = (L : ℝ)/2 ∧ T ≤ (P.ordinates.card : ℝ) := by
  classical
  let Q := coherentZetaPattern N L hN hL hLN T hT (by linarith)
  let W := (largeValueLattice T).image (fun u => T+u)
  have hinterval {t : ℝ} (ht : t ∈ W) : T ≤ t ∧ t ≤ 2*T := by
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ht
    have hb := largeValueLattice_in_interval hT.le hu
    constructor <;> linarith
  have hsep : IsOneSeparated W := by
    intro t ht u hu hne
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hu
    have hxy : x ≠ y := by intro he; subst y; exact hne rfl
    simpa only [add_sub_add_left_eq_sub] using
      largeValueLattice_oneSeparated T x hx y hy hxy
  have hlarge {t : ℝ} (ht : t ∈ W) :
      Q.V ≤ ‖∑ n ∈ Q.indices, Q.coeff n*dirichletPhase n t‖ := by
    rw [Q.polynomial_eq_active_sum]
    change (L : ℝ)/2 ≤ ‖∑ n ∈ largeValueBlock N L 0, dirichletPhase n t‖
    exact largeValueBlock_sum_lower (by omega) hL
      (hT.le.trans (hinterval ht).1) ((hinterval ht).2.trans hheight)
  let P : ZetaLargeValuePattern := {
    Q with
    ordinates := W
    ordinates_in_interval := fun _ ht => hinterval ht
    ordinates_oneSeparated := hsep
    large := fun _ ht => hlarge ht }
  refine ⟨P,rfl,rfl,rfl,?_⟩
  change T ≤ ((Finset.image (fun u => T+u) (largeValueLattice T)).card : ℝ)
  rw [Finset.card_image_of_injective _ (fun _ _ h => add_left_cancel h)]
  exact largeValueLattice_card_lower T

end TaoTrudgianYang2025

