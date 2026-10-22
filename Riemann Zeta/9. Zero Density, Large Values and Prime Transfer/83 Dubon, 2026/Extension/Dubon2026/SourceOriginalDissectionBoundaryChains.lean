import Dubon2026.SourceOriginalEulerCellDissection
import Dubon2026.SourceCellIntegerTreeCardinality

/-! DUB-17/18 -> original Abel-Jacobi -> 2g generating loops -> tree/cotree.
The graph chains use the actual cells, edges, vertices and orientation signs.
The boundary cancellation and connectivity clauses are needed to remove a
dual tree while preserving primal connectivity. Adapted from the frozen
source tree/cotree proof; actual loop generation remains a later consumer.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.DissectionTrees
noncomputable section
open SourceCurve Set Real IntegerEdgeChains
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] (𝒟 : CellDissection N)

/-- Head vertex of the actual oriented edge. -/
abbrev hdΓ : 𝒟.ιE → 𝒟.ιV := fun e => (𝒟.ends e).2
/-- Tail vertex of the actual oriented edge. -/
abbrev tlΓ : 𝒟.ιE → 𝒟.ιV := fun e => (𝒟.ends e).1

/-- Actual cell on the selected side of an edge. -/
noncomputable abbrev Cside : 𝒟.ιE → Bool → 𝒟.ιC :=
  fun e s => (Function.surjInv 𝒟.side_bij.surjective (e, s)).1

/-- Signed integer boundary chain of an actual analytic cell. -/
def cellBdryChain (C : 𝒟.ιC) : 𝒟.ιE → ℤ := fun e =>
  ∑ k : Fin (𝒟.cell C).R.N,
    (if (𝒟.side C k).2 then (1 : ℤ) else (-1)) * (if (𝒟.side C k).1 = e then 1 else 0)

/-- Successor arc with the final endpoint identified with the first. -/
def nxt {N : ℕ} (k : Fin N) : Fin N :=
  if h : k.val + 1 < N then ⟨k.val + 1, h⟩ else ⟨0, k.pos⟩

theorem nxt_bijective {N : ℕ} : Function.Bijective (nxt (N := N)) := by
  rw [← Finite.injective_iff_bijective]
  intro k k' h
  simp only [nxt] at h
  split_ifs at h with h1 h2 h2
  · exact Fin.ext (by simpa using Fin.mk.inj_iff.1 h)
  · simp at h
  · simp at h
  · exact Fin.ext (by omega)

theorem nxt_val {N : ℕ} (j : Fin N) : (nxt j).val = (j.val + 1) % N := by
  simp only [nxt]
  split_ifs with h
  · exact (Nat.mod_eq_of_lt h).symm
  · have hj := j.isLt
    have heq : j.val + 1 = N := by omega
    simp [heq]

theorem nxt_iterate_val {N : ℕ} (k : Fin N) (m : ℕ) :
    (nxt^[m] k).val = (k.val + m) % N := by
  induction m with
  | zero => simp [Nat.mod_eq_of_lt k.isLt]
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp_apply, nxt_val, ih,
      Nat.mod_add_mod, Nat.add_assoc]

theorem cell_bdry_periodic (C : Cell N) (φ : ℝ) :
    C.bdry (φ + 2 * π) = C.bdry φ := by
  exact congrArg C.ζ.symm (C.R.loop_periodic φ)

theorem bd_cellBdryChain (hvert : Function.Injective 𝒟.vert) :
    ∀ C w, bd (hdΓ 𝒟) (tlΓ 𝒟) (cellBdryChain 𝒟 C) w = 0 := by
  classical
  intro C w

  set sV : Fin (𝒟.cell C).R.N → 𝒟.ιV := fun k =>
    if (𝒟.side C k).2 then (𝒟.ends (𝒟.side C k).1).1 else (𝒟.ends (𝒟.side C k).1).2
    with hsV_def
  set eV : Fin (𝒟.cell C).R.N → 𝒟.ιV := fun k =>
    if (𝒟.side C k).2 then (𝒟.ends (𝒟.side C k).1).2 else (𝒟.ends (𝒟.side C k).1).1
    with heV_def

  have hfilt : ∀ (P : 𝒟.ιE → Prop) [DecidablePred P] (x : 𝒟.ιE) (s : ℤ),
      (∑ e with P e, s * (if x = e then (1 : ℤ) else 0)) =
      s * (if P x then 1 else 0) := by
    intro P _ x s
    rw [Finset.sum_filter,
      Finset.sum_eq_single x (fun b _ hne => by rw [if_neg (Ne.symm hne), mul_zero, ite_self])
        (fun h => absurd (Finset.mem_univ x) h), if_pos rfl]
    split_ifs <;> ring

  have hbd_eq : bd (hdΓ 𝒟) (tlΓ 𝒟) (cellBdryChain 𝒟 C) w =
      ∑ k, ((if eV k = w then (1:ℤ) else 0) - (if sV k = w then 1 else 0)) := by
    unfold bd cellBdryChain
    rw [Finset.sum_comm (t := Finset.univ (α := Fin (𝒟.cell C).R.N)),
        Finset.sum_comm (t := Finset.univ (α := Fin (𝒟.cell C).R.N)),
        ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hfilt (fun e => hdΓ 𝒟 e = w), hfilt (fun e => tlΓ 𝒟 e = w)]
    simp only [hdΓ, tlΓ, hsV_def, heV_def]
    by_cases hσ : (𝒟.side C k).2 <;>
      simp only [hσ, if_true] <;>
      split_ifs <;> ring

  have hcorner : ∀ k, eV k = sV (nxt k) := by
    intro k
    apply hvert
    have h1 := (𝒟.arc_ends C k).2
    have h2 := (𝒟.arc_ends C (nxt k)).1
    have hb : (𝒟.cell C).bdry ((𝒟.cell C).R.φs k.succ) =
        (𝒟.cell C).bdry ((𝒟.cell C).R.φs (nxt k).castSucc) := by
      by_cases hk : k.val + 1 < (𝒟.cell C).R.N
      · rw [show (nxt k).castSucc = k.succ from Fin.ext (by simp [nxt, hk])]
      · have h0 : (nxt k).castSucc = (0 : Fin _) := Fin.ext (by simp [nxt, hk])
        have hl : k.succ = Fin.last _ := Fin.ext (by
          simp only [Fin.val_succ, Fin.val_last]; omega)
        rw [h0, hl, (𝒟.cell C).R.hφ0, (𝒟.cell C).R.hφN,
          show (2 * π : ℝ) = 0 + 2 * π from by ring, cell_bdry_periodic]
    simp only [heV_def, hsV_def]
    rw [← h1, ← h2, hb]
  rw [hbd_eq]
  simp_rw [hcorner, Finset.sum_sub_distrib]
  rw [Fintype.sum_bijective nxt nxt_bijective
    (fun k => if sV (nxt k) = w then (1:ℤ) else 0)
    (fun k => if sV k = w then (1:ℤ) else 0) (fun k => rfl)]
  ring

theorem Cside_eq_iff (e : 𝒟.ιE) (σ : Bool) (C : 𝒟.ιC) :
    Cside 𝒟 e σ = C ↔ ∃ k, 𝒟.side C k = (e, σ) := by
  classical
  have hsurj := Function.surjInv_eq 𝒟.side_bij.surjective (e, σ)
  constructor
  · intro hC
    subst hC
    exact ⟨_, hsurj⟩
  · rintro ⟨k, hk⟩
    have heq : Function.surjInv 𝒟.side_bij.surjective (e, σ) = ⟨C, k⟩ :=
      𝒟.side_bij.injective (a₁ := Function.surjInv 𝒟.side_bij.surjective (e, σ))
        (a₂ := ⟨C, k⟩) (hsurj.trans hk.symm)
    exact congrArg Sigma.fst heq

theorem sum_side_indicator (e : 𝒟.ιE) (σ : Bool) (C : 𝒟.ιC) :
    (∑ k : Fin (𝒟.cell C).R.N, if 𝒟.side C k = (e, σ) then (1 : ℤ) else 0) =
      if Cside 𝒟 e σ = C then 1 else 0 := by
  classical
  by_cases h : Cside 𝒟 e σ = C
  · obtain ⟨k₀, hk₀⟩ := (Cside_eq_iff 𝒟 e σ C).mp h
    rw [if_pos h, Finset.sum_eq_single k₀]
    · rw [if_pos hk₀]
    · intro k' _ hne
      rw [if_neg]
      intro hk'
      have : (⟨C, k'⟩ : Σ D, Fin (𝒟.cell D).R.N) = ⟨C, k₀⟩ :=
        𝒟.side_bij.injective (hk'.trans hk₀.symm)
      exact hne (by injection this)
    · intro h'; exact absurd (Finset.mem_univ k₀) h'
  · rw [if_neg h, Finset.sum_eq_zero]
    intro k _
    rw [if_neg]
    intro hk
    exact h ((Cside_eq_iff 𝒟 e σ C).mpr ⟨k, hk⟩)

theorem cellBdryChain_eq (C : 𝒟.ιC) (e : 𝒟.ιE) :
    cellBdryChain 𝒟 C e =
      (if Cside 𝒟 e true = C then (1 : ℤ) else 0) -
      (if Cside 𝒟 e false = C then 1 else 0) := by
  classical
  unfold cellBdryChain
  have hrw : ∀ k, (if (𝒟.side C k).2 then (1 : ℤ) else (-1)) *
      (if (𝒟.side C k).1 = e then 1 else 0) =
      (if 𝒟.side C k = (e, true) then 1 else 0) -
      (if 𝒟.side C k = (e, false) then 1 else 0) := by
    intro k
    obtain ⟨e', σ⟩ := 𝒟.side C k
    by_cases he' : e' = e <;> rcases σ <;>
      simp only [he', if_true, if_false, Prod.mk.injEq, and_true, and_false,
        mul_one, mul_zero, sub_zero, zero_sub, reduceCtorEq, sub_self]
  simp_rw [hrw, Finset.sum_sub_distrib, sum_side_indicator]

end
end Dubon2026.SourceFunctionField.CellGeometry.DissectionTrees
