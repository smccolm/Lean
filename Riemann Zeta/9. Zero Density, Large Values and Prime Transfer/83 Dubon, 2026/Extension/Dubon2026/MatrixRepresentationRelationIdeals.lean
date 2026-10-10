import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # The actual ideal of every matrix relation in an original normal subgroup -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι R A : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing R] [CommRing A]

/-- All original relation matrices contribute their actual differences from the identity, entry by entry. -/
def matrixRepresentationRelationIdeal (ρ : G →* GeneralLinearGroup ι R)
    (N : Subgroup G) : Ideal R :=
  Ideal.span (Set.range (fun t : N × ι × ι =>
    (ρ t.1.val).val t.2.1 t.2.2 - (1 : Matrix ι ι R) t.2.1 t.2.2))

/-- Killing the literal coefficient ideal is equivalent to killing every original relation matrix after coefficient change. -/
theorem matrixRepresentationRelationIdeal_le_kernel_iff
    (ρ : G →* GeneralLinearGroup ι R) (N : Subgroup G) (f : R →+* A) :
    matrixRepresentationRelationIdeal ρ N ≤ RingHom.ker f ↔
      N ≤ ((GeneralLinearGroup.map (n := ι) f).comp ρ).ker := by
  constructor
  · intro h g hg
    apply Units.ext
    apply Matrix.ext
    intro i j
    have hentry := h (Ideal.subset_span
      (show (ρ g).val i j - (1 : Matrix ι ι R) i j ∈ Set.range
        (fun t : N × ι × ι =>
          (ρ t.1.val).val t.2.1 t.2.2 - (1 : Matrix ι ι R) t.2.1 t.2.2) from
        ⟨(⟨g, hg⟩, i, j), rfl⟩))
    change f ((ρ g).val i j - (1 : Matrix ι ι R) i j) = 0 at hentry
    rw [map_sub, sub_eq_zero] at hentry
    change f ((ρ g).val i j) = (1 : Matrix ι ι A) i j
    by_cases hij : i = j <;> simpa [Matrix.one_apply, hij] using hentry
  · intro h
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨g, i, j⟩, rfl⟩
    have hg := congrArg (fun u : GeneralLinearGroup ι A => u.val i j) (h g.property)
    change f ((ρ g.val).val i j) = (1 : Matrix ι ι A) i j at hg
    change f ((ρ g.val).val i j - (1 : Matrix ι ι R) i j) = 0
    rw [map_sub, hg]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

/-- Reduction by the actual ideal kills every original relation simultaneously. -/
theorem matrixRepresentationRelationIdeal_quotient_kills
    (ρ : G →* GeneralLinearGroup ι R) (N : Subgroup G) :
    N ≤ ((GeneralLinearGroup.map (n := ι)
      (Ideal.Quotient.mk (matrixRepresentationRelationIdeal ρ N))).comp ρ).ker := by
  apply (matrixRepresentationRelationIdeal_le_kernel_iff ρ N _).mp
  intro r hr
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hr

/-- The actual representation descends to the entire original group quotient after imposing all original matrix relations. -/
def matrixRelationQuotientRepresentation
    (ρ : G →* GeneralLinearGroup ι R) (N : Subgroup G) [N.Normal] :
    G ⧸ N →* GeneralLinearGroup ι (R ⧸ matrixRepresentationRelationIdeal ρ N) :=
  QuotientGroup.lift N
    ((GeneralLinearGroup.map (n := ι)
      (Ideal.Quotient.mk (matrixRepresentationRelationIdeal ρ N))).comp ρ)
    (matrixRepresentationRelationIdeal_quotient_kills ρ N)

/-- The descended original representation retains every original matrix after literal relation reduction. -/
theorem matrixRelationQuotientRepresentation_mk
    (ρ : G →* GeneralLinearGroup ι R) (N : Subgroup G) [N.Normal] (g : G) :
    matrixRelationQuotientRepresentation ρ N (QuotientGroup.mk' N g) =
      GeneralLinearGroup.map (n := ι)
        (Ideal.Quotient.mk (matrixRepresentationRelationIdeal ρ N)) (ρ g) := rfl

end
end Dubon2026
