import Dubon2026.FiniteReducedAlgebraPointSeparation
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Genuine tensor-coordinate separation over a perfect field -/

namespace Dubon2026
noncomputable section
open scoped TensorProduct

variable {F A B K : Type*} [Field F] [PerfectField F]
  [CommRing A] [Algebra F A] [Module.Finite F A] [IsReduced A]
  [CommRing B] [Algebra F B] [Module.Finite F B] [IsReduced B]

/-- A finite reduced algebra over the original perfect field is formally étale, via its actual Artinian field factors and their separability. -/
theorem finiteReducedAlgebra_formallyEtale : Algebra.FormallyEtale F A := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite F A
  letI (I : MaximalSpectrum A) : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
  letI (I : MaximalSpectrum A) : Algebra.FormallyEtale F (A ⧸ I.asIdeal) :=
    Algebra.FormallyEtale.of_isSeparable F (A ⧸ I.asIdeal)
  exact Algebra.FormallyEtale.of_equiv ((IsArtinianRing.equivPi A).restrictScalars F).symm

/-- The tensor product of the two original finite reduced algebras over a perfect field is reduced, derived through actual étale base change and composition. -/
theorem finiteReducedAlgebra_tensor_isReduced : IsReduced (A ⊗[F] B) := by
  letI := finiteReducedAlgebra_formallyEtale (F := F) (A := A)
  letI := finiteReducedAlgebra_formallyEtale (F := F) (A := B)
  letI : Algebra.FormallyEtale F (A ⊗[F] B) := Algebra.FormallyEtale.comp F A (A ⊗[F] B)
  exact Algebra.FormallyUnramified.isReduced_of_field F (A ⊗[F] B)

/-- Pairs of genuine original geometric points separate coordinates in the actual tensor product of finite reduced algebras over a perfect field. -/
theorem finiteReducedTensor_eq_zero_of_point_pairs [Field K] [Algebra F K] [IsAlgClosed K]
    (z : A ⊗[F] B)
    (hz : ∀ (p : A →ₐ[F] K) (q : B →ₐ[F] K),
      Algebra.TensorProduct.productMap p q z = 0) : z = 0 := by
  letI := finiteReducedAlgebra_tensor_isReduced (F := F) (A := A) (B := B)
  apply finiteReducedAlgebra_eq_zero_of_points (F := F) (K := K) z
  intro f
  have hf : Algebra.TensorProduct.productMap
      (f.comp Algebra.TensorProduct.includeLeft)
      (f.comp Algebra.TensorProduct.includeRight) = f := by
    apply Algebra.TensorProduct.ext'
    intro a b
    change f (a ⊗ₜ[F] (1 : B)) * f ((1 : A) ⊗ₜ[F] b) = f (a ⊗ₜ[F] b)
    rw [← map_mul]
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [← hf]
  exact hz _ _

end
end Dubon2026
