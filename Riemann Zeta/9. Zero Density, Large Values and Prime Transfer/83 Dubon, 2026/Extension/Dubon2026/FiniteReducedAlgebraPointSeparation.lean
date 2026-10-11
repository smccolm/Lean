import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Nilpotent.Lemmas

/-! # Genuine geometric points separate a finite reduced algebra -/

namespace Dubon2026
noncomputable section

variable {F A K : Type*} [Field F] [CommRing A] [Algebra F A]
  [Module.Finite F A] [IsReduced A] [Field K] [Algebra F K] [IsAlgClosed K]

/-- An original coordinate in a finite reduced algebra is zero if every genuine point in the algebraically closed value field vanishes on it. Prime quotients and actual field embeddings prove separation. -/
theorem finiteReducedAlgebra_eq_zero_of_points (a : A)
    (ha : ∀ p : A →ₐ[F] K, p a = 0) : a = 0 := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite F A
  apply IsReduced.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro I hI
  letI : I.IsPrime := hI
  letI : I.IsMaximal := inferInstance
  letI := Ideal.Quotient.field I
  let e : A ⧸ I →ₐ[F] K := IsAlgClosed.lift
  have hz : Ideal.Quotient.mkₐ F I a = 0 := by
    apply e.injective
    simpa only [map_zero, AlgHom.comp_apply] using ha (e.comp (Ideal.Quotient.mkₐ F I))
  exact Ideal.Quotient.eq_zero_iff_mem.mp hz

end
end Dubon2026
