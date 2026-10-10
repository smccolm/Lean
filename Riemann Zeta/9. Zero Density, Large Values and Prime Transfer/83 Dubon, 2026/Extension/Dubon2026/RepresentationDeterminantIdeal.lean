import Dubon2026.MatrixRepresentationRelationIdeals
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # The actual coefficient ideal imposing a prescribed determinant -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι O R A : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [CommRing R] [Algebra O R]
  [CommRing A] [Algebra O A]

/-- The original determinant differences, for every original group element, generate the actual fixed-determinant coefficient ideal. -/
def representationDeterminantIdeal (ρ : G →* GeneralLinearGroup ι R)
    (δ : G →* Oˣ) : Ideal R :=
  Ideal.span (Set.range fun g : G =>
    (GeneralLinearGroup.det (ρ g) : R) - algebraMap O R (δ g : O))

/-- A genuine coefficient map kills this actual ideal exactly when the original representation acquires the specified determinant after coefficient change. -/
theorem representationDeterminantIdeal_le_kernel_iff
    (ρ : G →* GeneralLinearGroup ι R) (δ : G →* Oˣ) (f : R →ₐ[O] A) :
    representationDeterminantIdeal ρ δ ≤ RingHom.ker f.toRingHom ↔
      ∀ g : G, GeneralLinearGroup.det (GeneralLinearGroup.map (n := ι) f.toRingHom (ρ g)) =
        Units.map (algebraMap O A) (δ g) := by
  constructor
  · intro hf g
    have hg := hf (Ideal.subset_span (Set.mem_range_self g))
    change f ((GeneralLinearGroup.det (ρ g) : R) - algebraMap O R (δ g : O)) = 0 at hg
    rw [map_sub, f.commutes, sub_eq_zero] at hg
    rw [GeneralLinearGroup.map_det]
    apply Units.ext
    exact hg
  · intro hf
    apply Ideal.span_le.mpr
    rintro _ ⟨g, rfl⟩
    have hg := congrArg (fun x : Aˣ => (x : A)) (hf g)
    rw [GeneralLinearGroup.map_det] at hg
    change f ((GeneralLinearGroup.det (ρ g) : R)) = algebraMap O A (δ g : O) at hg
    change f ((GeneralLinearGroup.det (ρ g) : R) - algebraMap O R (δ g : O)) = 0
    rw [map_sub, f.commutes, hg, sub_self]

/-- The original coefficient quotient imposes the actual prescribed determinant at every original group element. -/
theorem representationDeterminantIdeal_quotient_det
    (ρ : G →* GeneralLinearGroup ι R) (δ : G →* Oˣ) (g : G) :
    GeneralLinearGroup.det (GeneralLinearGroup.map (n := ι)
      (Ideal.Quotient.mk (representationDeterminantIdeal ρ δ)) (ρ g)) =
        Units.map (algebraMap O (R ⧸ representationDeterminantIdeal ρ δ)) (δ g) := by
  apply (representationDeterminantIdeal_le_kernel_iff ρ δ
    (Ideal.Quotient.mkₐ O (representationDeterminantIdeal ρ δ))).mp ?_ g
  intro r hr
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hr

end
end Dubon2026
