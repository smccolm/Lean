import Dubon2026.RepresentationCoordinateRelations
import Mathlib.GroupTheory.Finiteness
import Mathlib.RingTheory.FiniteType

/-! # Generation of the actual representation coordinate algebra -/

namespace Dubon2026

noncomputable section
open Matrix MvPolynomial
open scoped BigOperators

variable (G ι R : Type*) [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- All original coordinate matrix entries generate the entire concrete quotient algebra. -/
theorem representationCoordinateMatrix_adjoin :
    Algebra.adjoin R (Set.range (fun t : G × ι × ι =>
      representationCoordinateMatrix G ι R t.1 t.2.1 t.2.2)) = ⊤ := by
  let q := Ideal.Quotient.mkₐ R (representationCoordinateIdeal G ι R)
  have h := congrArg (fun S : Subalgebra R (MvPolynomial (G × ι × ι) R) => S.map q) (MvPolynomial.adjoin_range_X (R := R) (σ := G × ι × ι))
  dsimp only at h
  rw [AlgHom.map_adjoin, Algebra.map_top] at h
  have hq : q.range = ⊤ := (AlgHom.range_eq_top q).mpr (Ideal.Quotient.mkₐ_surjective R _)
  rw [hq] at h
  simpa only [← Set.range_comp, Function.comp_def, q, representationCoordinateMatrix] using h

/-- If the original group elements are generated multiplicatively by a set, the matrix entries at that set generate all original coordinate entries. -/
theorem representationCoordinateMatrix_mem_adjoin (S : Set G)
    (hS : Submonoid.closure S = ⊤) (g : G) (i j : ι) :
    representationCoordinateMatrix G ι R g i j ∈
      Algebra.adjoin R (Set.range (fun t : S × ι × ι =>
        representationCoordinateMatrix G ι R t.1.val t.2.1 t.2.2)) := by
  let A := Algebra.adjoin R (Set.range (fun t : S × ι × ι =>
    representationCoordinateMatrix G ι R t.1.val t.2.1 t.2.2))
  have hg : g ∈ Submonoid.closure S := by rw [hS]; trivial
  have hm : ∀ a ∈ Submonoid.closure S, ∀ i j,
      representationCoordinateMatrix G ι R a i j ∈ A := by
    intro a ha
    induction ha using Submonoid.closure_induction with
    | mem a ha =>
      intro i j
      exact Algebra.subset_adjoin ⟨(⟨a, ha⟩, i, j), rfl⟩
    | one =>
      intro i j
      rw [representationCoordinateMatrix_one]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    | mul a b _ _ ha hb =>
      intro i j
      rw [representationCoordinateMatrix_mul, Matrix.mul_apply]
      exact A.sum_mem (fun k _ => A.mul_mem (ha i k) (hb k j))
  exact hm g hg i j

/-- The original matrix entries at any multiplicative generating set generate the whole actual representation coordinate algebra. -/
theorem representationCoordinateMatrix_generators_adjoin (S : Set G)
    (hS : Submonoid.closure S = ⊤) :
    Algebra.adjoin R (Set.range (fun t : S × ι × ι =>
      representationCoordinateMatrix G ι R t.1.val t.2.1 t.2.2)) = ⊤ := by
  apply top_unique
  rw [← representationCoordinateMatrix_adjoin G ι R]
  apply Algebra.adjoin_le
  rintro _ ⟨⟨g, i, j⟩, rfl⟩
  exact representationCoordinateMatrix_mem_adjoin G ι R S hS g i j

end
end Dubon2026
