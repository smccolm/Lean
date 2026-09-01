import GafniTao.FordCrossCollision

/-!
# Ford Lemma 3.2: one pinned residue coordinate

The source boundary contains at most one residue value.  Splitting a tuple at
one coordinate therefore removes exactly one copy of the residue Weyl sum.
This file proves that statement for the literal finite character sums.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

-- The residue class is a type parameter; the formula itself does not use it.
def fordResidueSingleMomentAt {k Q q p : ℕ} {c : ZMod p}
    (x : FordResidueInterval Q p c) : Fin k → ℤ :=
  fun j ↦ ((q ^ ((j : ℕ) + 1) *
    ((x.1 : ℕ) + 1) ^ ((j : ℕ) + 1) : ℕ) : ℤ)

def fordResidueFamilyMoment
    {k Q q p : ℕ} {c : ZMod p} {I : Type*} [Fintype I]
    (u : I → FordResidueInterval Q p c) : Fin k → ℤ :=
  ∑ i : I, fordResidueSingleMomentAt (k := k) (q := q) (u i)

theorem fordResidueFamilyMoment_fin
    {k s Q q p : ℕ} (c : ZMod p)
    (u : Fin s → FordResidueInterval Q p c) :
    fordResidueFamilyMoment (k := k) (q := q) u =
      fordS4ResidueMoment (k := k) q c u := by
  ext j
  simp [fordResidueFamilyMoment, fordResidueSingleMomentAt,
    fordS4ResidueMoment]

theorem ford_mFourier_familyMoment
    {k Q q p : ℕ} {c : ZMod p} {I : Type*} [Fintype I]
    (u : I → FordResidueInterval Q p c)
    (α : UnitAddTorus (Fin k)) :
    UnitAddTorus.mFourier (fordResidueFamilyMoment (k := k) (q := q) u) α =
      ∏ i : I, UnitAddTorus.mFourier
      (fordResidueSingleMomentAt (k := k) (q := q) (u i)) α := by
  classical
  unfold fordResidueFamilyMoment
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty => simp [UnitAddTorus.mFourier_zero]
  | @insert i t hi ih =>
      rw [Finset.sum_insert hi, UnitAddTorus.mFourier_add,
        Finset.prod_insert hi, ih]

theorem fordResidueFamilyCharacterSum_eq_pow_card
    {k Q q p : ℕ} {c : ZMod p} {I : Type*} [Fintype I] [DecidableEq I]
    (α : UnitAddTorus (Fin k)) :
    fordCharacterSum
        (fordResidueFamilyMoment (k := k) (Q := Q) (q := q) (p := p) (c := c) :
          (I → FordResidueInterval Q p c) → Fin k → ℤ) α =
      fordResidueWeylSum k Q q p c α ^ Fintype.card I := by
  classical
  let eI := Fintype.equivFin I
  let eFun : (I → FordResidueInterval Q p c) ≃
      (Fin (Fintype.card I) → FordResidueInterval Q p c) :=
    Equiv.arrowCongr eI (Equiv.refl _)
  have hmoment : ∀ u : I → FordResidueInterval Q p c,
      fordResidueFamilyMoment (k := k) (q := q) u =
        fordS4ResidueMoment (k := k) q c (eFun u) := by
    intro u
    ext j
    simp only [fordResidueFamilyMoment, fordResidueSingleMomentAt,
      fordS4ResidueMoment, eFun, eI, Finset.sum_apply]
    change (∑ x : I,
        ((q ^ ((j : ℕ) + 1) * ((u x).1.1 + 1) ^ ((j : ℕ) + 1) : ℕ) : ℤ)) =
      ∑ x : Fin (Fintype.card I),
        ((q ^ ((j : ℕ) + 1) *
          ((u (eI.symm x)).1.1 + 1) ^ ((j : ℕ) + 1) : ℕ) : ℤ)
    simpa using eI.sum_comp (fun x : Fin (Fintype.card I) ↦
      ((q ^ ((j : ℕ) + 1) *
        ((u (eI.symm x)).1.1 + 1) ^ ((j : ℕ) + 1) : ℕ) : ℤ))
  calc
    fordCharacterSum
        (fordResidueFamilyMoment (k := k) (Q := Q) (q := q) (p := p) (c := c) :
          (I → FordResidueInterval Q p c) → Fin k → ℤ) α =
        fordCharacterSum
          (fordS4ResidueMoment (k := k) q c :
            FordS4ResidueTuple (Fintype.card I) Q p c → Fin k → ℤ) α := by
      unfold fordCharacterSum
      exact Fintype.sum_equiv eFun _ _ fun u ↦
        congrArg (fun M ↦ UnitAddTorus.mFourier M α) (hmoment u)
    _ = fordResidueWeylSum k Q q p c α ^ Fintype.card I :=
      (fordResidueWeylSum_pow (Fintype.card I) k Q q p c α).symm

def fordResidueIsBoundary
    {Q p : ℕ} [NeZero p] (c : ZMod p)
    (x : FordResidueInterval Q p c) : Prop :=
  ¬ (fordResidueIntervalToShiftIndex c x).1 < Q / p

instance fordResidueBoundarySubsingleton
    {Q p : ℕ} [NeZero p] (c : ZMod p) :
    Subsingleton {x : FordResidueInterval Q p c // fordResidueIsBoundary c x} where
  allEq x y := by
    apply Subtype.ext
    apply (fordResidueShiftEquiv c).injective
    exact ford_shiftedResidueIndex_boundary_unique c x.property y.property

noncomputable instance (priority := 2000) fordResidueBoundaryFintype
    {Q p : ℕ} [NeZero p] (c : ZMod p) :
    Fintype {x : FordResidueInterval Q p c // fordResidueIsBoundary c x} :=
  Fintype.ofFinite _

def fordBoundaryResidueWeylSum
    (k Q q p : ℕ) [NeZero p] (c : ZMod p)
    (α : UnitAddTorus (Fin k)) : ℂ := by
  classical
  exact ∑ x : {x : FordResidueInterval Q p c // fordResidueIsBoundary c x},
      UnitAddTorus.mFourier
        (fordResidueSingleMomentAt (k := k) (q := q) x.1) α

theorem norm_fordBoundaryResidueWeylSum_le_one
    (k Q q p : ℕ) [NeZero p] (c : ZMod p)
    (α : UnitAddTorus (Fin k)) :
    ‖fordBoundaryResidueWeylSum k Q q p c α‖ ≤ 1 := by
  classical
  unfold fordBoundaryResidueWeylSum
  let B := {x : FordResidueInterval Q p c // fordResidueIsBoundary c x}
  cases isEmpty_or_nonempty B with
  | inl hempty =>
      letI : IsEmpty B := hempty
      simp
  | inr hnonempty =>
      letI : Nonempty B := hnonempty
      letI : Unique B :=
        { default := Classical.choice hnonempty
          uniq := fun _ ↦ Subsingleton.elim _ _ }
      simp only [Fintype.sum_unique]
      exact (ContinuousMap.norm_coe_le_norm _ _).trans_eq
        UnitAddTorus.mFourier_norm

def fordBoundaryTupleSplitEquiv
    {s Q p : ℕ} [NeZero p] (c : ZMod p) (i : Fin s) :
    {u : FordS4ResidueTuple s Q p c // fordResidueIsBoundary c (u i)} ≃
      {x : FordResidueInterval Q p c // fordResidueIsBoundary c x} ×
        ({j : Fin s // j ≠ i} → FordResidueInterval Q p c) where
  toFun u := (⟨u.1 i, u.2⟩, fun j ↦ u.1 j.1)
  invFun v := ⟨(Equiv.funSplitAt i _).symm (v.1.1, v.2), by
    simpa using v.1.2⟩
  left_inv u := by
    apply Subtype.ext
    exact (Equiv.funSplitAt i _).left_inv u.1
  right_inv v := by
    have hsplit := (Equiv.funSplitAt i
      (FordResidueInterval Q p c)).apply_symm_apply (v.1.1, v.2)
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hsplit
    · change (fun j : {j : Fin s // j ≠ i} ↦
          ((Equiv.funSplitAt i (FordResidueInterval Q p c)).symm
            (v.1.1, v.2)) j.1) = v.2
      exact congrArg Prod.snd hsplit

abbrev FordBoundaryResidueTupleAt
    {s Q p : ℕ} [NeZero p] (c : ZMod p) (i : Fin s) :=
  {u : FordS4ResidueTuple s Q p c // fordResidueIsBoundary c (u i)}

noncomputable instance (priority := 2000) fordBoundaryResidueTupleAtFintype
    {s Q p : ℕ} [NeZero p] (c : ZMod p) (i : Fin s) :
    Fintype (FordBoundaryResidueTupleAt (Q := Q) c i) :=
  Fintype.ofFinite _

def fordBoundaryTupleWeylSum
    {s : ℕ} (k Q q p : ℕ) [NeZero p] (c : ZMod p) (i : Fin s)
    (α : UnitAddTorus (Fin k)) : ℂ := by
  classical
  exact ∑ u : FordBoundaryResidueTupleAt (Q := Q) c i,
      UnitAddTorus.mFourier (fordS4ResidueMoment (k := k) q c u.1) α

theorem fordBoundaryTupleWeylSum_eq
    {s : ℕ} (k Q q p : ℕ) [NeZero p] (c : ZMod p) (i : Fin s)
    (α : UnitAddTorus (Fin k)) :
    fordBoundaryTupleWeylSum k Q q p c i α =
      fordBoundaryResidueWeylSum k Q q p c α *
        fordResidueWeylSum k Q q p c α ^ (s - 1) := by
  classical
  unfold fordBoundaryResidueWeylSum
  let e := fordBoundaryTupleSplitEquiv (Q := Q) c i
  let g := fun v :
      {x : FordResidueInterval Q p c // fordResidueIsBoundary c x} ×
        ({j : Fin s // j ≠ i} → FordResidueInterval Q p c) ↦
    UnitAddTorus.mFourier
        (fordResidueSingleMomentAt (k := k) (q := q) v.1.1) α *
      UnitAddTorus.mFourier
        (fordResidueFamilyMoment (k := k) (q := q) v.2) α
  have hfg : ∀ u : {u : FordS4ResidueTuple s Q p c //
      fordResidueIsBoundary c (u i)},
      UnitAddTorus.mFourier (fordS4ResidueMoment (k := k) q c u.1) α =
        g (e u) := by
    intro u
    have hmoment : fordS4ResidueMoment (k := k) q c u.1 =
        fordResidueSingleMomentAt (k := k) (q := q) (u.1 i) +
          fordResidueFamilyMoment (k := k) (q := q)
            (fun j : {j : Fin s // j ≠ i} ↦ u.1 j.1) := by
      ext j
      simp only [fordS4ResidueMoment, fordResidueSingleMomentAt,
        fordResidueFamilyMoment, Pi.add_apply, Finset.sum_apply]
      change (∑ x : Fin s,
          ((q ^ ((j : ℕ) + 1) * ((u.1 x).1.1 + 1) ^ ((j : ℕ) + 1) : ℕ) : ℤ)) =
        ((q ^ ((j : ℕ) + 1) * ((u.1 i).1.1 + 1) ^ ((j : ℕ) + 1) : ℕ) : ℤ) +
          ∑ x : {j : Fin s // j ≠ i},
            ((q ^ ((j : ℕ) + 1) * ((u.1 x.1).1.1 + 1) ^ ((j : ℕ) + 1) : ℕ) : ℤ)
      simpa using (Fintype.sum_subtype_add_sum_subtype
        (fun x : Fin s ↦ x = i)
        (fun x ↦ ((q ^ ((j : ℕ) + 1) *
          ((u.1 x).1.1 + 1) ^ ((j : ℕ) + 1) : ℕ) : ℤ))).symm
    change UnitAddTorus.mFourier (fordS4ResidueMoment (k := k) q c u.1) α = _
    rw [hmoment, UnitAddTorus.mFourier_add]
    rfl
  calc
    fordBoundaryTupleWeylSum k Q q p c i α =
        ∑ v, g v := by
      simpa only [fordBoundaryTupleWeylSum] using
        (Fintype.sum_equiv e _ g hfg)
    _ = (∑ x : {x : FordResidueInterval Q p c // fordResidueIsBoundary c x},
          UnitAddTorus.mFourier
            (fordResidueSingleMomentAt (k := k) (q := q) x.1) α) *
        ∑ v : ({j : Fin s // j ≠ i} → FordResidueInterval Q p c),
          UnitAddTorus.mFourier
            (fordResidueFamilyMoment (k := k) (q := q) v) α := by
      rw [Fintype.sum_prod_type, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
    _ = _ := by
      have hfamily := fordResidueFamilyCharacterSum_eq_pow_card
        (k := k) (Q := Q) (q := q) (p := p) (c := c)
        (I := {j : Fin s // j ≠ i}) α
      unfold fordCharacterSum at hfamily
      have hcard : Fintype.card {j : Fin s // j ≠ i} = s - 1 := by
        calc
        Fintype.card {j : Fin s // j ≠ i} =
            Fintype.card (Fin s) - Fintype.card {j : Fin s // j = i} :=
          Fintype.card_subtype_compl (fun j : Fin s ↦ j = i)
        _ = s - 1 := by simp
      rw [hfamily, hcard]

theorem norm_fordBoundaryTupleWeylSum_le
    {s : ℕ} (k Q q p : ℕ) [NeZero p] (c : ZMod p) (i : Fin s)
    (α : UnitAddTorus (Fin k)) :
    ‖fordBoundaryTupleWeylSum k Q q p c i α‖ ≤
      ‖fordResidueWeylSum k Q q p c α‖ ^ (s - 1) := by
  rw [fordBoundaryTupleWeylSum_eq]
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (by positivity)
    (norm_fordBoundaryResidueWeylSum_le_one k Q q p c α)

#print axioms fordResidueFamilyCharacterSum_eq_pow_card
#print axioms norm_fordBoundaryTupleWeylSum_le

end

end GafniTao
