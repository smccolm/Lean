import Mathlib.FieldTheory.Normal.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Original field-valued points with the same kernel are Galois conjugate -/

namespace Dubon2026
noncomputable section

variable {F A K : Type*} [Field F] [CommRing A] [Algebra F A]
  [IsArtinianRing A] [Field K] [Algebra F K] [Normal F K]

/-- Two genuine field-valued points of the original Artinian algebra with the same kernel differ by an automorphism of the original normal field extension. -/
theorem artinianAlgebraPoint_sameKernel_galois (p q : A →ₐ[F] K)
    (h : RingHom.ker p.toRingHom = RingHom.ker q.toRingHom) :
    ∃ g : K ≃ₐ[F] K, g.toAlgHom.comp p = q := by
  letI : (RingHom.ker p.toRingHom).IsPrime := RingHom.ker_isPrime p.toRingHom
  letI : (RingHom.ker p.toRingHom).IsMaximal := inferInstance
  letI := Ideal.Quotient.field (RingHom.ker p.toRingHom)
  let pbar := Ideal.kerLiftAlg p
  let qbar : A ⧸ RingHom.ker p.toRingHom →ₐ[F] K :=
    Ideal.Quotient.liftₐ _ q h.le
  letI : Algebra (A ⧸ RingHom.ker p.toRingHom) K := pbar.toRingHom.toAlgebra
  letI : IsScalarTower F (A ⧸ RingHom.ker p.toRingHom) K := IsScalarTower.of_algHom pbar
  let g := AlgEquiv.ofBijective (qbar.liftNormal K)
    (AlgHom.normal_bijective F K K (qbar.liftNormal K))
  refine ⟨g, ?_⟩
  apply AlgHom.ext
  intro a
  exact qbar.liftNormal_commutes K (Ideal.Quotient.mk (RingHom.ker p.toRingHom) a)

end
end Dubon2026
