import GafniTao.FordFiniteAMGM

/-!
# Partition of residue tuples by their first `d` power sums

This is the bookkeeping step after Ford's fibrewise Cauchy--AM--GM bound.
The dependent union of the sets `B_s(w)` is proved equivalent to the whole
residue box, and every fixed coordinate occurs exactly `p^(s-1)` times.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

def fordBJoinEquiv {p d s : ℕ} (hds : d ≤ s) :
    ((Fin d → ZMod p) × (Fin (s - d) → ZMod p)) ≃
      (Fin s → ZMod p) where
  toFun := fordBJoin hds
  invFun x :=
    (fun i => x ((finSumFinEquiv.trans
      (finCongr (Nat.add_sub_of_le hds))) (Sum.inl i)),
     fun i => x ((finSumFinEquiv.trans
      (finCongr (Nat.add_sub_of_le hds))) (Sum.inr i)))
  left_inv c := by
    let e := finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hds))
    apply Prod.ext
    · funext i
      change Sum.elim c.1 c.2 (e.symm (e (Sum.inl i))) = c.1 i
      rw [e.symm_apply_apply]
      rfl
    · funext i
      change Sum.elim c.1 c.2 (e.symm (e (Sum.inr i))) = c.2 i
      rw [e.symm_apply_apply]
      rfl
  right_inv x := by
    funext i
    let e := finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hds))
    change Sum.elim _ _ (e.symm i) = x i
    conv_rhs => rw [← e.apply_symm_apply i]
    generalize e.symm i = u
    cases u <;> rfl

def fordBSignature (p d s : ℕ)
    (c : (Fin d → ZMod p) × (Fin (s - d) → ZMod p)) :
    Fin d → ZMod p :=
  fun j => fordPowerSum c.1 ((j : ℕ) + 1) +
    fordPowerSum c.2 ((j : ℕ) + 1)

def fordBResidueClassEquivFiber
    (p d s : ℕ) (v : Fin d → ZMod p) :
    FordBResidueClass p d s v ≃
      {c : (Fin d → ZMod p) × (Fin (s - d) → ZMod p) //
        fordBSignature p d s c = v} where
  toFun c := ⟨c.1, funext c.2⟩
  invFun c := ⟨c.1, fun j => congrFun c.2 j⟩
  left_inv _c := rfl
  right_inv _c := rfl

def fordBAllEquiv (p d s : ℕ) :
    (Σ v : Fin d → ZMod p, FordBResidueClass p d s v) ≃
      ((Fin d → ZMod p) × (Fin (s - d) → ZMod p)) :=
  (Equiv.sigmaCongrRight fun v => fordBResidueClassEquivFiber p d s v).trans
    (Equiv.sigmaFiberEquiv (fordBSignature p d s))

@[simp] theorem fordBAllEquiv_apply
    (p d s : ℕ)
    (x : Σ v : Fin d → ZMod p, FordBResidueClass p d s v) :
    fordBAllEquiv p d s x = x.2.1 := rfl

/-- Summing over the moment vector and then its fibre is exactly summing over
all split residue tuples. -/
theorem ford_sum_BResidueClass
    {p d s : ℕ} [NeZero p]
    (F : ((Fin d → ZMod p) × (Fin (s - d) → ZMod p)) → ℝ) :
    ∑ v : Fin d → ZMod p, ∑ c : FordBResidueClass p d s v, F c.1 =
      ∑ c : (Fin d → ZMod p) × (Fin (s - d) → ZMod p), F c := by
  rw [← Fintype.sum_sigma']
  exact Fintype.sum_equiv (fordBAllEquiv p d s)
    (fun x => F x.2.1) F (fun x => rfl)

/-- A fixed coordinate of the full `s`-tuple takes each residue exactly
`p^(s-1)` times. -/
theorem ford_sum_residue_tuple_coordinate
    {p s : ℕ} [NeZero p] (i : Fin s)
    (f : ZMod p → ℝ) :
    ∑ x : Fin s → ZMod p, f (x i) =
      (p : ℝ) ^ (s - 1) * ∑ a : ZMod p, f a := by
  classical
  let X := Fin s → ZMod p
  have hfiber (a : ZMod p) :
      ((Finset.univ : Finset X).filter fun x => x i = a).card = p ^ (s - 1) := by
    simpa [X] using
      (Fintype.card_filter_piFinset_const_eq_of_mem
        (Finset.univ : Finset (ZMod p)) i (Finset.mem_univ a))
  have hpartition := Finset.sum_fiberwise_eq_sum_filter
    (Finset.univ : Finset X) (Finset.univ : Finset (ZMod p))
    (fun x => x i) (fun x => f (x i))
  have hpartition' :
      ∑ a : ZMod p,
          ∑ x ∈ (Finset.univ : Finset X) with x i = a, f (x i) =
        ∑ x : X, f (x i) := by simpa [X] using hpartition
  rw [← hpartition']
  calc
    ∑ a : ZMod p,
        ∑ x ∈ (Finset.univ : Finset X) with x i = a, f (x i) =
      ∑ a : ZMod p, (p ^ (s - 1) : ℕ) * f a := by
        apply Finset.sum_congr rfl
        intro a ha
        calc
          ∑ x ∈ (Finset.univ : Finset X) with x i = a, f (x i) =
              (((Finset.univ : Finset X).filter fun x => x i = a).card : ℝ) *
                f a := by
            calc
              ∑ x ∈ ((Finset.univ : Finset X).filter fun x => x i = a),
                  f (x i) =
                ∑ _x ∈ ((Finset.univ : Finset X).filter fun x => x i = a),
                  f a := by
                    apply Finset.sum_congr rfl
                    intro x hx
                    exact congrArg f (Finset.mem_filter.mp hx).2
              _ = _ := by simp
          _ = (p ^ (s - 1) : ℕ) * f a := by rw [hfiber a]
    _ = (p : ℝ) ^ (s - 1) * ∑ a : ZMod p, f a := by
      push_cast
      rw [Finset.mul_sum]

/-- After the `B_s(w)` partition, summing the AM--GM coordinate terms gives
the exact source multiplicity `s p^(s-1)`. -/
theorem ford_sum_BResidueClass_coordinates
    {p d s : ℕ} [NeZero p] (hds : d ≤ s)
    (f : ZMod p → ℝ) :
    ∑ v : Fin d → ZMod p,
        ∑ c : FordBResidueClass p d s v,
          ∑ i : Fin s, f (fordBJoin hds c.1 i) =
      (s : ℝ) * (p : ℝ) ^ (s - 1) * ∑ a : ZMod p, f a := by
  rw [ford_sum_BResidueClass
    (F := fun c => ∑ i : Fin s, f (fordBJoin hds c i))]
  rw [Finset.sum_comm]
  have hsplit (i : Fin s) :
      ∑ c : (Fin d → ZMod p) × (Fin (s - d) → ZMod p),
          f (fordBJoin hds c i) =
        (p : ℝ) ^ (s - 1) * ∑ a : ZMod p, f a := by
    calc
      ∑ c : (Fin d → ZMod p) × (Fin (s - d) → ZMod p),
          f (fordBJoin hds c i) =
        ∑ x : Fin s → ZMod p, f (x i) := by
          exact Fintype.sum_equiv (fordBJoinEquiv hds)
            (fun c => f (fordBJoin hds c i)) (fun x => f (x i))
              (fun c => rfl)
      _ = _ := ford_sum_residue_tuple_coordinate i f
  simp_rw [hsplit]
  simp
  ring

#print axioms ford_sum_BResidueClass
#print axioms ford_sum_residue_tuple_coordinate
#print axioms ford_sum_BResidueClass_coordinates

end

end GafniTao
