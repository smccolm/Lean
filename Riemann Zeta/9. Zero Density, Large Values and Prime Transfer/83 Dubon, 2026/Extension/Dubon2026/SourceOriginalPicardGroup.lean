import Dubon2026.SourceCurvePicardGroup
import Dubon2026.SourceOriginalPrincipalDivisors

/-! DUB-17/18 -> actual modular Galois association -> the original
Jacobian torsion and Tate module. This module identifies torsion classes
in the literal degree-zero divisor quotient of the original modular
function field over the algebraic closure of Q. Their nonzero function
representatives and exact normalized orders are derived from quotient
membership, not supplied as an additional arithmetic hypothesis.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve

/-- The degree-zero divisor-class group of the original modular field over Qbar. -/
abbrev originalJZero (N : ℕ) :=
  Pic0 (AlgebraicClosure ℚ) (modularFunctionFieldOver N (AlgebraicClosure ℚ))

theorem originalPic0_principal_eq_zero (N : ℕ) [NeZero N]
    (L : Type*) [Field L] [Algebra ℚ L] (f : modularFunctionFieldOver N L) (hf : f ≠ 0) :
    Pic0.mk ⟨originalPrincipalDivisor N L f, degree_originalPrincipalDivisor N L f⟩ = 0 :=
  (Pic0.mk_eq_zero_iff _).mpr ⟨f, hf, originalPrincipalDivisor_apply N L f⟩

theorem originalPic0_torsion_representative (N : ℕ) [NeZero N]
    (L : Type*) [Field L] [Algebra ℚ L] (n : ℕ)
    (x : Pic0 L (modularFunctionFieldOver N L)) (hx : x ∈ Pic0.torsion n) :
    ∃ (D : Divisor.degZero (K := L) (F := modularFunctionFieldOver N L))
      (f : modularFunctionFieldOver N L), f ≠ 0 ∧ Pic0.mk D = x ∧
      originalPrincipalDivisor N L f = n • D.val := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  obtain ⟨f, hf, hD⟩ := (Pic0.mk_mem_torsion_iff D n).mp hx
  exact ⟨D, f, hf, rfl, Finsupp.ext fun v => (hD v).symm⟩

theorem originalJZero_torsion_orders (N : ℕ) [NeZero N] (n : ℕ)
    (x : originalJZero N) (hx : x ∈ Pic0.torsion n) :
    ∃ (D : Divisor.degZero (K := AlgebraicClosure ℚ)
      (F := modularFunctionFieldOver N (AlgebraicClosure ℚ)))
      (f : modularFunctionFieldOver N (AlgebraicClosure ℚ)), f ≠ 0 ∧ Pic0.mk D = x ∧
      ∀ v, v.ord f = (n : ℤ) * D.val v := by
  obtain ⟨D, f, hf, hx, hD⟩ := originalPic0_torsion_representative N (AlgebraicClosure ℚ) n x hx
  refine ⟨D, f, hf, hx, fun v => ?_⟩
  have h := congrArg (fun E : Divisor (AlgebraicClosure ℚ)
    (modularFunctionFieldOver N (AlgebraicClosure ℚ)) => E v) hD
  simpa only [originalPrincipalDivisor_apply, Finsupp.smul_apply, nsmul_eq_mul] using h

end
end Dubon2026.SourceFunctionField
