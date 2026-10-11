import Dubon2026.ArtinianAlgebraPointKernelOrbit
import Dubon2026.HopfPointVanishingKernelSelection
import Dubon2026.CommutativeHopfPointsCoefficientChange

/-! # Exact geometric point closure for a finite original Galois-stable point set -/

namespace Dubon2026
noncomputable section

variable {F A K : Type*} [Field F] [CommRing A] [HopfAlgebra F A]
  [IsArtinianRing A] [Field K] [Algebra F K] [Normal F K]

/-- A finite point set stable under the actual field-automorphism action is exactly the set of genuine points killing its original joint vanishing ideal. -/
theorem hopfGaloisStablePointSet_eq_vanishing
    (X : Set (WithConv (A →ₐ[F] K))) [Finite X]
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[F] K)), p ∈ X →
      commutativeHopfPointsAutomorphism g p ∈ X) :
    X = {p : WithConv (A →ₐ[F] K) |
      hopfPointsVanishingIdeal X ≤ RingHom.ker p.ofConv.toRingHom} := by
  ext p
  constructor
  · intro hp a ha
    exact (hopfPointsVanishingIdeal_mem_iff X a).mp ha ⟨p, hp⟩
  · intro hp
    obtain ⟨q, hq⟩ := hopfPointVanishingIdeal_kernel_selection X p hp
    obtain ⟨g, hg⟩ := artinianAlgebraPoint_sameKernel_galois q.val.ofConv p.ofConv hq
    have he : commutativeHopfPointsAutomorphism g q.val = p := by
      apply WithConv.ext
      exact hg
    exact he ▸ hX g q.val q.property

end
end Dubon2026
