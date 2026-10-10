import Dubon2026.CoefficientRepresentationMatrixAlgebra
import Dubon2026.MatrixBasisIdealCoordinates
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Ideal.Operations

/-! # The actual maximal-coefficient kernel in the original representation matrix algebra -/

namespace Dubon2026
noncomputable section
open Matrix Module

variable {G ι κ O R : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [CommRing O] [CommRing R] [Algebra O R]

/-- The actual coefficient-algebra basis retains each original full-matrix basis vector literally. -/
theorem coefficientRepresentationMatrixBasis_val
    (S : Subalgebra O R) (ρ : G →* GeneralLinearGroup ι R) (a : κ → G)
    (b : Basis κ R (Matrix ι ι R)) (hb : ∀ i, b i = (ρ (a i)).val)
    (hcoord : ∀ x i, b.repr (ρ x).val i ∈ S) (i : κ) :
    (coefficientRepresentationMatrixBasis S ρ a b hb hcoord i).val = b i := by
  change ((Basis.span (b.linearIndependent.restrict_scalars' S) i :
    Submodule.span S (Set.range b)) : Matrix ι ι R) = b i
  exact Basis.coe_span_apply (b.linearIndependent.restrict_scalars' S) i

/-- If an actual element of the original representation matrix algebra has all entries in the ambient maximal ideal, it lies in the maximal-ideal multiple of that same algebra over its original local coefficient subalgebra. -/
theorem coefficientRepresentationMatrixAlgebra_mem_maximal_smul
    [IsLocalRing R] (S : Subalgebra O R) [IsLocalRing S] [IsLocalHom S.val.toRingHom]
    (ρ : G →* GeneralLinearGroup ι R) (a : κ → G)
    (b : Basis κ R (Matrix ι ι R)) (hb : ∀ i, b i = (ρ (a i)).val)
    (hcoord : ∀ x i, b.repr (ρ x).val i ∈ S)
    (X : coefficientRepresentationMatrixAlgebra S ρ)
    (hX : ∀ i j, X.val i j ∈ IsLocalRing.maximalIdeal R) :
    X ∈ IsLocalRing.maximalIdeal S •
      (⊤ : Submodule S (coefficientRepresentationMatrixAlgebra S ρ)) := by
  let bs := coefficientRepresentationMatrixBasis S ρ a b hb hcoord
  have hspan : X.val ∈ Submodule.span S (Set.range b) := by
    rw [← coefficientRepresentationMatrixAlgebra_eq_basis_span S ρ a b hb hcoord]
    exact X.property
  have hcS := (matrix_mem_subalgebra_basis_span_iff S b X.val).mp hspan
  let c : κ → S := fun i => ⟨b.repr X.val i, hcS i⟩
  have hc (i : κ) : c i ∈ IsLocalRing.maximalIdeal S := by
    rw [← IsLocalRing.maximalIdeal_comap S.val.toRingHom]
    exact matrixBasisCoordinate_mem_ideal (IsLocalRing.maximalIdeal R) b X.val hX i
  have hsum : (∑ i, c i • bs i) = X := by
    apply Subtype.ext
    change (coefficientRepresentationMatrixAlgebra S ρ).val (∑ i, c i • bs i) = X.val
    simp only [map_sum, map_smul]
    change (∑ i, (c i : R) • (bs i).val) = X.val
    simp only [bs, coefficientRepresentationMatrixBasis_val]
    exact b.sum_repr X.val
  rw [← hsum]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hc i) Submodule.mem_top

end
end Dubon2026
