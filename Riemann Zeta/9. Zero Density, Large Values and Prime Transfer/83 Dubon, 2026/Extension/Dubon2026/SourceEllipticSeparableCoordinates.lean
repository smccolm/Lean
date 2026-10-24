import Dubon2026.SourceEllipticTorsionCardinality
import Dubon2026.SourceEllipticOddOrbitDistinctness
import Mathlib.FieldTheory.SeparableClosure

/-! Coordinate descent to the separable closure for the finite Galois torsion
field. This supplies the inertia specialization and exceptional-fiber census
in DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2. Adapted from
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, the finite division-field proof.
The later torsion separability proof uses the local all-order multiplication
formula and cardinality, avoiding the archived order induction. -/
namespace Dubon2026.SourceEllipticDivisionField
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open Dubon2026.SourceEllipticVelu.OddDiscriminant
noncomputable section
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [DecidableEq Ω]

section FieldHelpers

omit [DecidableEq Ω] in
lemma mem_separableClosure_of_root {z : Ω} (q : Polynomial (separableClosure F Ω))
    (hsep : (q.map (algebraMap (separableClosure F Ω) Ω)).Separable) (hroot : (q.map (algebraMap (separableClosure F Ω) Ω)).IsRoot z) :
    z ∈ (separableClosure F Ω) := by
  rw [mem_separableClosure_iff]
  have hq : q.Separable := (Polynomial.separable_map (algebraMap (separableClosure F Ω) Ω)).mp hsep
  have haeval : aeval z q = 0 := by rwa [aeval_def, eval₂_eq_eval_map]
  have hz : IsSeparable ((separableClosure F Ω)) z := (hq.of_dvd (minpoly.dvd (separableClosure F Ω) z haeval))
  exact IsSeparable.of_algebra_isSeparable_of_isSeparable F hz

lemma separable_of_natDegree_le_card {f : Polynomial Ω} (hf : f ≠ 0) (T : Finset Ω)
    (hT : ∀ t ∈ T, f.IsRoot t) (hdeg : f.natDegree ≤ T.card) : f.Separable := by
  classical
  have hsub : T ⊆ f.roots.toFinset := fun t ht => by
    rw [Multiset.mem_toFinset, mem_roots hf]; exact hT t ht
  have h1 : T.card ≤ f.roots.toFinset.card := Finset.card_le_card hsub
  have h2 : f.roots.toFinset.card ≤ f.roots.card := Multiset.toFinset_card_le _
  have h3 : f.roots.card ≤ f.natDegree := card_roots' f
  have hnodup : f.roots.Nodup := by
    rw [← Multiset.toFinset_card_eq_card_iff_nodup]; omega
  have hsplits : f.Splits := by
    rw [splits_iff_card_roots]; omega
  exact (nodup_roots_iff_of_splits hf hsplits).mp hnodup

end FieldHelpers

section SepPoints

variable (E : WeierstrassCurve F)

/-- The actual points coming from the separable closure of the base field. -/
noncomputable def sepPoints : AddSubgroup (E.baseChange Ω).toAffine.Point :=
  (Point.map (IntermediateField.val (separableClosure F Ω)) :
    (E.baseChange (separableClosure F Ω)).toAffine.Point →+ (E.baseChange Ω).toAffine.Point).range

variable {E}

lemma some_mem_sepPoints_iff {x y : Ω} (h : (E.baseChange Ω).toAffine.Nonsingular x y) :
    Point.some x y h ∈ sepPoints E ↔ x ∈ (separableClosure F Ω) ∧ y ∈ (separableClosure F Ω) := by
  constructor
  · rintro ⟨P', hP'⟩
    cases P' with
    | zero => exact absurd hP'.symm (Point.some_ne_zero h)
    | some x' y' h' =>
      rw [Point.map_some] at hP'
      obtain ⟨rfl, rfl⟩ := Point.some.inj hP'
      exact ⟨x'.2, y'.2⟩
  · rintro ⟨hx, hy⟩
    have h' : (E.baseChange (separableClosure F Ω)).toAffine.Nonsingular ⟨x, hx⟩ ⟨y, hy⟩ :=
      (Affine.baseChange_nonsingular E (f := IntermediateField.val (separableClosure F Ω))
        Subtype.val_injective ⟨x, hx⟩ ⟨y, hy⟩).mp h
    exact ⟨Point.some _ _ h', by rw [Point.map_some]; rfl⟩

lemma Y_mem_of_X_mem {x y : Ω} (h : (E.baseChange Ω).toAffine.Equation x y) (hx : x ∈ (separableClosure F Ω))
    (hy : y ≠ (E.baseChange Ω).toAffine.negY x y ∨ (2 : F) ≠ 0) : y ∈ (separableClosure F Ω) := by

  set c : Ω := (E.baseChange Ω).a₁ * x + (E.baseChange Ω).a₃ with hc_def
  set f₀ : Ω := x ^ 3 + (E.baseChange Ω).a₂ * x ^ 2 + (E.baseChange Ω).a₄ * x
    + (E.baseChange Ω).a₆ with hf₀_def
  have ha₁ : (E.baseChange Ω).a₁ ∈ (separableClosure F Ω) :=
    IntermediateField.algebraMap_mem _ E.a₁
  have ha₂ : (E.baseChange Ω).a₂ ∈ (separableClosure F Ω) :=
    IntermediateField.algebraMap_mem _ E.a₂
  have ha₃ : (E.baseChange Ω).a₃ ∈ (separableClosure F Ω) :=
    IntermediateField.algebraMap_mem _ E.a₃
  have ha₄ : (E.baseChange Ω).a₄ ∈ (separableClosure F Ω) :=
    IntermediateField.algebraMap_mem _ E.a₄
  have ha₆ : (E.baseChange Ω).a₆ ∈ (separableClosure F Ω) :=
    IntermediateField.algebraMap_mem _ E.a₆
  have hc : c ∈ (separableClosure F Ω) := add_mem (mul_mem ha₁ hx) ha₃
  have hf₀ : f₀ ∈ (separableClosure F Ω) :=
    add_mem (add_mem (add_mem (pow_mem hx 3) (mul_mem ha₂ (pow_mem hx 2))) (mul_mem ha₄ hx)) ha₆
  have hnegY : (E.baseChange Ω).toAffine.negY x y = -y - c := by
    rw [negY, hc_def]; ring
  have heq : y ^ 2 + c * y = f₀ := by
    rw [equation_iff] at h
    rw [hc_def, hf₀_def]; linear_combination h
  by_cases hyn : y = (E.baseChange Ω).toAffine.negY x y
  ·
    have h2 : (2 : F) ≠ 0 := hy.resolve_left (not_not.mpr hyn)
    have h2Ω : (2 : Ω) ≠ 0 := by
      intro h0
      apply h2
      apply (algebraMap F Ω).injective
      rw [map_ofNat, _root_.map_zero, h0]
    have hyc : y = -c * 2⁻¹ := by
      rw [hnegY] at hyn
      field_simp
      linear_combination hyn
    rw [hyc]
    have h2S : (2 : Ω)⁻¹ ∈ (separableClosure F Ω) := by
      have : (2 : Ω)⁻¹ = algebraMap F Ω (2 : F)⁻¹ := by rw [map_inv₀, map_ofNat]
      rw [this]; exact IntermediateField.algebraMap_mem _ _
    exact mul_mem (neg_mem hc) h2S
  ·
    set y' : Ω := (E.baseChange Ω).toAffine.negY x y with hy'_def
    have hsum : y + y' = -c := by rw [hnegY]; ring
    have hprod : y * y' = -f₀ := by rw [hnegY, ← heq]; ring
    let cS : (separableClosure F Ω) := ⟨c, hc⟩
    let fS : (separableClosure F Ω) := ⟨f₀, hf₀⟩
    let q : Polynomial (separableClosure F Ω) := X ^ 2 + Polynomial.C cS * X - Polynomial.C fS
    have hqmap : q.map (algebraMap (separableClosure F Ω) Ω) =
        (X - Polynomial.C y) * (X - Polynomial.C y') := by
      have hq : q.map (algebraMap (separableClosure F Ω) Ω) =
          X ^ 2 + Polynomial.C c * X - Polynomial.C f₀ := by
        simp only [q, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow,
          Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C]
        rfl
      have h1 : Polynomial.C c = -(Polynomial.C y + Polynomial.C y') := by
        rw [← Polynomial.C_add, hsum, Polynomial.C_neg, neg_neg]
      have h2 : Polynomial.C f₀ = -(Polynomial.C y * Polynomial.C y') := by
        rw [← Polynomial.C_mul, hprod, Polynomial.C_neg, neg_neg]
      rw [hq, h1, h2]
      ring
    refine mem_separableClosure_of_root q ?_ ?_
    · rw [hqmap]
      exact separable_X_sub_C.mul separable_X_sub_C
        (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hyn).isUnit)
    · rw [hqmap, IsRoot, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul]

end SepPoints
end
end Dubon2026.SourceEllipticDivisionField
