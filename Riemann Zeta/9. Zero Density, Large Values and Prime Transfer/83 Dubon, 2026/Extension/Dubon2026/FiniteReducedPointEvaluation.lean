import Dubon2026.ArtinianAlgebraPointKernelOrbit
import Dubon2026.FiniteReducedAlgebraPointSeparation
import Mathlib.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Actual coordinates recovered from genuine geometric points -/

namespace Dubon2026
noncomputable section

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A] [Module.Finite K A]

/-- The original coordinate algebra evaluated at all its genuine field-valued points. -/
def finiteAlgebraPointEvaluation : A →ₐ[K] ((A →ₐ[K] K) → K) :=
  Pi.algHom K (fun _ : A →ₐ[K] K => K) (fun p => p)

/-- Every assignment of values at the original rational points of a finite algebra is realized by an actual original coordinate. Distinct original point kernels are maximal and distinct, so the pinned Chinese remainder theorem applies to those same kernels. -/
theorem finiteAlgebraPointEvaluation_surjective :
    Function.Surjective (finiteAlgebraPointEvaluation (K := K) (A := A)) := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite K A
  letI : Finite (A →ₐ[K] K) := inferInstance
  let I : (A →ₐ[K] K) → Ideal A := fun p => RingHom.ker p.toRingHom
  letI (p : A →ₐ[K] K) : (I p).IsPrime := RingHom.ker_isPrime p.toRingHom
  letI (p : A →ₐ[K] K) : (I p).IsMaximal := inferInstance
  have hI : Pairwise (fun p q => IsCoprime (I p) (I q)) := by
    intro p q hpq
    apply Ideal.isCoprime_of_isMaximal
    intro h
    apply hpq
    obtain ⟨g, hg⟩ := artinianAlgebraPoint_sameKernel_galois p q h
    apply AlgHom.ext
    intro a
    calc
      p a = g (p a) := (g.commutes (p a)).symm
      _ = q a := AlgHom.congr_fun hg a
  intro u
  obtain ⟨a, ha⟩ := Ideal.exists_forall_sub_mem_ideal hI (fun p => algebraMap K A (u p))
  refine ⟨a, ?_⟩
  funext p
  have h := ha p
  change p (a - algebraMap K A (u p)) = 0 at h
  rw [map_sub, show p (algebraMap K A (u p)) = u p from p.commutes (u p)] at h
  exact sub_eq_zero.mp h

/-- Genuine geometric point evaluation is injective for the original finite reduced algebra over the algebraically closed field. -/
theorem finiteReducedAlgebraPointEvaluation_injective [IsAlgClosed K] [IsReduced A] :
    Function.Injective (finiteAlgebraPointEvaluation (K := K) (A := A)) := by
  intro a b h
  apply sub_eq_zero.mp
  apply finiteReducedAlgebra_eq_zero_of_points (F := K) (K := K)
  intro p
  rw [map_sub]
  exact sub_eq_zero.mpr (congrFun h p)

/-- Recover the actual original finite reduced coordinate algebra as the full algebra of functions on its genuine geometric points. -/
def finiteReducedPointEvaluationEquiv [IsAlgClosed K] [IsReduced A] :
    A ≃ₐ[K] ((A →ₐ[K] K) → K) :=
  AlgEquiv.ofBijective finiteAlgebraPointEvaluation
    ⟨finiteReducedAlgebraPointEvaluation_injective, finiteAlgebraPointEvaluation_surjective⟩

/-- The actual coordinate reconstruction evaluates the same original point on the same original coordinate. -/
theorem finiteReducedPointEvaluationEquiv_apply [IsAlgClosed K] [IsReduced A]
    (a : A) (p : A →ₐ[K] K) : finiteReducedPointEvaluationEquiv a p = p a := by
  rfl

end
end Dubon2026
