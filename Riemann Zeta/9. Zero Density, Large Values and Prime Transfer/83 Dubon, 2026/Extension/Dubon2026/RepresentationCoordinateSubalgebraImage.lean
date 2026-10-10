import Dubon2026.RepresentationCoordinateGeneration

/-! # Original matrix coordinates determine the actual coefficient-subalgebra image -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι O A : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [CommRing A] [Algebra O A]

/-- If the actual images of all original representation matrix entries belong to a coefficient subalgebra, the image of the entire original coordinate algebra belongs to it. -/
theorem representationCoordinate_image_mem_subalgebra (S : Subalgebra O A)
    (f : RepresentationCoordinateAlgebra G ι O →ₐ[O] A)
    (hentry : ∀ g i j, f (representationCoordinateMatrix G ι O g i j) ∈ S)
    (x : RepresentationCoordinateAlgebra G ι O) : f x ∈ S := by
  have h : (⊤ : Subalgebra O (RepresentationCoordinateAlgebra G ι O)) ≤ S.comap f := by
    rw [← representationCoordinateMatrix_adjoin G ι O]
    apply Algebra.adjoin_le
    rintro _ ⟨⟨g, i, j⟩, rfl⟩
    exact hentry g i j
  exact h (show x ∈ (⊤ : Subalgebra O (RepresentationCoordinateAlgebra G ι O)) from trivial)

end
end Dubon2026
