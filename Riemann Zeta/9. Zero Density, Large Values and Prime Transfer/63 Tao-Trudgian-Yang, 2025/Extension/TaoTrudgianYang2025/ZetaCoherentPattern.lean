import TaoTrudgianYang2025.LargeValueBlockCoherence
import TaoTrudgianYang2025.ZetaLargeValueDiscreteness

/-!
# Genuine coherent zeta patterns below the oscillatory range

The coefficients are exactly one on a short integer interval. These are
source zeta patterns, not arbitrarily modulated large-value patterns.
-/

noncomputable section
namespace TaoTrudgianYang2025

def coherentZetaPattern (N L : ℕ) (hN : 1 < N) (hL : 0 < L) (hLN : L ≤ N)
    (T : ℝ) (hT : 0 < T) (hheight : T ≤ (N : ℝ)/(2*(L : ℝ))) :
    ZetaLargeValuePattern := by
  classical
  let A := largeValueBlock N L 0
  have hsub : A ⊆ Finset.Icc N (2*N) := by
    intro n hn
    simp only [A,largeValueBlock,Nat.zero_mul,Nat.add_zero,zero_add,one_mul,
      Finset.mem_Ico] at hn
    exact Finset.mem_Icc.mpr ⟨hn.1,by omega⟩
  have heval : (∑ n ∈ Finset.Icc N (2*N),
      (if n ∈ A then (1 : ℂ) else 0)*dirichletPhase n T) =
      ∑ n ∈ A, dirichletPhase n T := by
    simp only [ite_mul,one_mul,zero_mul,← Finset.sum_filter]
    rw [Finset.filter_mem_eq_inter,Finset.inter_eq_right.mpr hsub]
  refine {
    N := N
    scale := N
    T := T
    V := (L : ℝ)/2
    coeff := fun n => if n ∈ A then 1 else 0
    indices := Finset.Icc N (2*N)
    intervalLeft := T
    intervalRight := 2*T
    ordinates := {T}
    N_eq_scale := rfl
    one_lt_N := by exact_mod_cast hN
    T_pos := hT
    V_pos := by exact_mod_cast (show (0 : ℝ) < (L : ℝ)/2 by positivity)
    mem_indices_iff := ?_
    coeff_one_bounded := ?_
    interval_length := by ring
    ordinates_in_interval := ?_
    ordinates_oneSeparated := ?_
    large := ?_
    active := A
    active_isInterval := ?_
    active_subset := hsub
    coeff_eq_indicator := fun _ _ => rfl
    intervalLeft_eq := rfl
    intervalRight_eq := rfl }
  · intro n
    simp only [Finset.mem_Icc]
    norm_cast
  · intro n _
    split_ifs <;> simp
  · intro t ht
    have he : t = T := Finset.mem_singleton.mp ht
    subst t
    constructor <;> linarith
  · intro t ht u hu hne
    have ht' := Finset.mem_singleton.mp ht
    have hu' := Finset.mem_singleton.mp hu
    exact (hne (ht'.trans hu'.symm)).elim
  · intro t ht
    have he : t = T := Finset.mem_singleton.mp ht
    subst t
    rw [heval]
    exact largeValueBlock_sum_lower (j:=0) (by omega) hL hT.le hheight
  · refine ⟨N,N+L-1,?_⟩
    ext n
    simp only [A,largeValueBlock,Nat.zero_mul,Nat.add_zero,zero_add,one_mul,
      Finset.mem_Ico,Finset.mem_Icc]
    omega

theorem coherentZetaPattern_scale (N L : ℕ) (hN : 1 < N) (hL : 0 < L) (hLN : L ≤ N)
    (T : ℝ) (hT : 0 < T) (hheight : T ≤ (N : ℝ)/(2*(L : ℝ))) :
    (coherentZetaPattern N L hN hL hLN T hT hheight).N = (N : ℝ) := rfl

theorem coherentZetaPattern_time (N L : ℕ) (hN : 1 < N) (hL : 0 < L) (hLN : L ≤ N)
    (T : ℝ) (hT : 0 < T) (hheight : T ≤ (N : ℝ)/(2*(L : ℝ))) :
    (coherentZetaPattern N L hN hL hLN T hT hheight).T = T := rfl

theorem coherentZetaPattern_value (N L : ℕ) (hN : 1 < N) (hL : 0 < L) (hLN : L ≤ N)
    (T : ℝ) (hT : 0 < T) (hheight : T ≤ (N : ℝ)/(2*(L : ℝ))) :
    (coherentZetaPattern N L hN hL hLN T hT hheight).V = (L : ℝ)/2 := rfl

theorem coherentZetaPattern_ordinates (N L : ℕ) (hN : 1 < N) (hL : 0 < L) (hLN : L ≤ N)
    (T : ℝ) (hT : 0 < T) (hheight : T ≤ (N : ℝ)/(2*(L : ℝ))) :
    (coherentZetaPattern N L hN hL hLN T hT hheight).ordinates = {T} := rfl

end TaoTrudgianYang2025
