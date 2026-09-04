import GafniTao.HeathBrownLemmaOneDivision
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Removing the endpoint-regularity mismatch in Heath-Brown Theorem 1

The source assumes `C^k` regularity only on `(0,N)`.  The finite spacing
argument is applied here to `x ↦ f (x + 1)` on the compact interval
`[0,N-2]`.  The original exponential sum differs from that compact-interior
sum by precisely its two endpoint phases, whose total norm is at most two.
-/

open Complex Finset Set
open scoped BigOperators

namespace GafniTao

noncomputable section

noncomputable def heathBrownInteriorShift (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  f (x + 1)

theorem iteratedDeriv_heathBrownInteriorShift
    (k : ℕ) (f : ℝ → ℝ) :
    iteratedDeriv k (heathBrownInteriorShift f) =
      fun x => iteratedDeriv k f (x + 1) := by
  exact iteratedDeriv_comp_add_const k f 1

theorem heathBrownInteriorShift_contDiffOn
    {N k : ℕ} {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ k f (Set.Ioo 0 (N : ℝ))) :
    ContDiffOn ℝ k (heathBrownInteriorShift f)
      (Set.Ioo (-1 : ℝ) ((N : ℝ) - 1)) := by
  have hmap : Set.MapsTo (fun x : ℝ => x + 1)
      (Set.Ioo (-1 : ℝ) ((N : ℝ) - 1)) (Set.Ioo 0 (N : ℝ)) := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hshift : ContDiffOn ℝ k (fun x : ℝ => x + 1)
      (Set.Ioo (-1 : ℝ) ((N : ℝ) - 1)) :=
    (contDiff_id.add contDiff_const).contDiffOn
  simpa only [heathBrownInteriorShift, Function.comp_apply] using
    hf.comp hshift hmap

theorem heathBrownInteriorCompact_subset
    {N : ℕ} (hN : 2 ≤ N) :
    Set.Icc (0 : ℝ) ((N - 2 : ℕ) : ℝ) ⊆
      Set.Ioo (-1 : ℝ) ((N : ℝ) - 1) := by
  intro x hx
  constructor
  · linarith [hx.1]
  · rw [Nat.cast_sub hN] at hx
    norm_num at hx ⊢
    linarith [hx.2]

theorem heathBrownInteriorShift_deriv_bounds
    {N k : ℕ} {f : ℝ → ℝ} {A lambda : ℝ}
    (hkBounds : ∀ x ∈ Set.Ioo (0 : ℝ) (N : ℝ),
      lambda ≤ iteratedDeriv k f x ∧
        iteratedDeriv k f x ≤ A * lambda) :
    ∀ x ∈ Set.Ioo (-1 : ℝ) ((N : ℝ) - 1),
      lambda ≤ iteratedDeriv k (heathBrownInteriorShift f) x ∧
        iteratedDeriv k (heathBrownInteriorShift f) x ≤ A * lambda := by
  intro x hx
  rw [iteratedDeriv_heathBrownInteriorShift]
  exact hkBounds (x + 1) ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem sum_Icc_two_sub_one_eq_shifted
    {R : Type*} [AddCommMonoid R] (N : ℕ) (hN : 2 ≤ N) (F : ℕ → R) :
    (∑ n ∈ Finset.Icc 2 (N - 1), F n) =
      ∑ n ∈ Finset.Icc 1 (N - 2), F (n + 1) := by
  classical
  symm
  refine Finset.sum_nbij (fun n => n + 1) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  · intro a _ b _ hab
    exact Nat.add_right_cancel hab
  · intro b hb
    change b ∈ Finset.Icc 2 (N - 1) at hb
    rw [Finset.mem_Icc] at hb
    have heq : b - 1 + 1 = b := by omega
    refine ⟨b - 1, ?_, heq⟩
    · rw [Finset.mem_coe, Finset.mem_Icc]
      constructor
      · omega
      · calc
          b - 1 ≤ (N - 1) - 1 := Nat.sub_le_sub_right hb.2 1
          _ = N - 2 := by omega
  · intro _ _
    rfl

theorem heathBrownExponentialSum_interior_identity
    {N : ℕ} (hN : 2 ≤ N) (f : ℝ → ℝ) :
    heathBrownExponentialSum N f =
      heathBrownPhase (f 1) +
        heathBrownExponentialSum (N - 2) (heathBrownInteriorShift f) +
          heathBrownPhase (f N) := by
  classical
  unfold heathBrownExponentialSum heathBrownInteriorShift
  have htop : N - 1 + 1 = N := by omega
  have honeN : 1 ≤ N - 1 := by omega
  have htopSum :
      (∑ n ∈ Finset.Icc 1 N, heathBrownPhase (f n)) =
        (∑ n ∈ Finset.Icc 1 (N - 1), heathBrownPhase (f n)) +
          heathBrownPhase (f N) := by
    rw [← htop]
    exact Finset.sum_Icc_succ_top (by omega : 1 ≤ N - 1 + 1) _
  have hbottomSum :
      (∑ n ∈ Finset.Icc 1 (N - 1), heathBrownPhase (f n)) =
        heathBrownPhase (f 1) +
          ∑ n ∈ Finset.Icc 2 (N - 1), heathBrownPhase (f n) := by
    have hnot : 1 ∉ Finset.Icc 2 (N - 1) := by
      simp only [Finset.mem_Icc, not_and_or, not_le]
      omega
    rw [← Finset.insert_Icc_add_one_left_eq_Icc honeN]
    simpa only [Nat.reduceAdd, Nat.cast_one] using
      (Finset.sum_insert hnot
        (f := fun n : ℕ => heathBrownPhase (f n)))
  calc
    (∑ n ∈ Finset.Icc 1 N, heathBrownPhase (f n)) =
        (∑ n ∈ Finset.Icc 1 (N - 1), heathBrownPhase (f n)) +
          heathBrownPhase (f N) := htopSum
    _ = (heathBrownPhase (f 1) +
          ∑ n ∈ Finset.Icc 2 (N - 1), heathBrownPhase (f n)) +
          heathBrownPhase (f N) := by
      rw [hbottomSum]
    _ = heathBrownPhase (f 1) +
          (∑ n ∈ Finset.Icc 1 (N - 2), heathBrownPhase (f (n + 1))) +
          heathBrownPhase (f N) := by
      rw [sum_Icc_two_sub_one_eq_shifted N hN]
      simp only [Nat.cast_add, Nat.cast_one]

theorem norm_heathBrownExponentialSum_le_interior_add_two
    {N : ℕ} (hN : 2 ≤ N) (f : ℝ → ℝ) :
    ‖heathBrownExponentialSum N f‖ ≤
      ‖heathBrownExponentialSum (N - 2) (heathBrownInteriorShift f)‖ + 2 := by
  rw [heathBrownExponentialSum_interior_identity hN]
  calc
    ‖heathBrownPhase (f 1) +
        heathBrownExponentialSum (N - 2) (heathBrownInteriorShift f) +
        heathBrownPhase (f N)‖ ≤
        ‖heathBrownPhase (f 1)‖ +
          ‖heathBrownExponentialSum (N - 2) (heathBrownInteriorShift f)‖ +
          ‖heathBrownPhase (f N)‖ := by
      calc
        _ ≤ ‖heathBrownPhase (f 1) +
              heathBrownExponentialSum (N - 2) (heathBrownInteriorShift f)‖ +
              ‖heathBrownPhase (f N)‖ := norm_add_le _ _
        _ ≤ _ := by
          gcongr
          exact norm_add_le _ _
    _ = ‖heathBrownExponentialSum (N - 2) (heathBrownInteriorShift f)‖ + 2 := by
      rw [norm_heathBrownPhase, norm_heathBrownPhase]
      ring

#print axioms iteratedDeriv_heathBrownInteriorShift
#print axioms heathBrownInteriorShift_contDiffOn
#print axioms heathBrownInteriorCompact_subset
#print axioms heathBrownInteriorShift_deriv_bounds
#print axioms sum_Icc_two_sub_one_eq_shifted
#print axioms heathBrownExponentialSum_interior_identity
#print axioms norm_heathBrownExponentialSum_le_interior_add_two

end

end GafniTao
