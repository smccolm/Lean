/-
Copyright (c) 2024 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Riccardo Brasca

The quotient-basis comparison below adapts Algebra.trace_quotient_mk from
Mathlib/RingTheory/Trace/Quotient.lean at
c5ea00351c28e24afc9f0f84379aa41082b1188f, using the actual determinant
instead of the trace of the same original multiplication matrix.
-/
import Mathlib.RingTheory.Trace.Quotient
import Mathlib.RingTheory.Norm.Defs

/-! # Reduction of the original finite-free algebra norm at the base maximal ideal -/

namespace Dubon2026
noncomputable section

open IsLocalRing Module

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [Module.Free R S] [Module.Finite R S]

attribute [local instance] Ideal.Quotient.field

/-- The original norm reduces to the actual norm on the original quotient
algebra. This follows from the genuine quotient basis and its multiplication
matrix, without an assumed compatibility certificate. -/
theorem localRingNorm_quotient_mk (x : S) :
    Algebra.norm (R ⧸ maximalIdeal R)
      (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (maximalIdeal R)) x) =
      Ideal.Quotient.mk (maximalIdeal R) (Algebra.norm R x) := by
  classical
  let ι := Module.Free.ChooseBasisIndex R S
  let b : Module.Basis ι R S := Module.Free.chooseBasis R S
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det (basisQuotient b),
    RingHom.map_det]
  congr 1
  ext i j
  simp only [Algebra.leftMulMatrix_apply, Algebra.coe_lmul_eq_mul, LinearMap.toMatrix_apply,
    basisQuotient_apply, LinearMap.mul_apply', RingHom.mapMatrix_apply, Matrix.map_apply, ← map_mul,
    basisQuotient_repr]

end
end Dubon2026
