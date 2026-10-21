import Dubon2026.SourcePrimitiveH1HeckeRelations
import Dubon2026.SourcePrimitiveAlgebraicIntegerReduction

/-! The original primitive H1 character takes algebraic-integer values.
DUB-17/18 -> residual modular Galois association -> residual H1 eigensystem
-> actual integral H1 Hecke character and its specialization. Finiteness of
the genuine integral operator algebra gives integrality of every character
value, and each generator agrees with the original analytic Hecke character.
-/

namespace Dubon2026
noncomputable section

variable {Q : ℕ} [NeZero Q] {k : ℤ}

/-- The character of the actual integral binary H1 Hecke algebra supplied by the original primitive form. -/
def sourcePrimitiveH1HeckeCharacter (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) :
    sourceBinaryH1HeckeAlgebra Q (k - 2).toNat →ₐ[ℤ] ℂ :=
  (sourcePrimitive_exists_H1HeckeCharacter f hk).choose

/-- Every genuine good-prime H1 Hecke generator has the original Fourier eigenvalue. -/
theorem sourcePrimitiveH1HeckeCharacter_hecke (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (p : sourceBinaryHeckePrime Q) :
    sourcePrimitiveH1HeckeCharacter f hk
      ⟨sourceBinaryH1PrimeOperators ℤ Q (k - 2).toNat p,
        Algebra.subset_adjoin ⟨p, rfl⟩⟩ = cuspCoefficients f.toCuspForm p.val :=
  (sourcePrimitive_exists_H1HeckeCharacter f hk).choose_spec p

/-- Every value of the actual H1 character is integral over Z, by finite integral H1 Hecke algebra. -/
theorem sourcePrimitiveH1HeckeCharacter_isIntegral (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (T : sourceBinaryH1HeckeAlgebra Q (k - 2).toNat) :
    IsIntegral ℤ (sourcePrimitiveH1HeckeCharacter f hk T) := by
  letI := sourceBinaryH1HeckeAlgebra_finite Q (k - 2).toNat
  exact (IsIntegral.of_finite ℤ T).map (sourcePrimitiveH1HeckeCharacter f hk)

/-- The actual original H1 Hecke character with its proved algebraic-integer codomain. -/
def sourcePrimitiveIntegralH1HeckeCharacter (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) :
    sourceBinaryH1HeckeAlgebra Q (k - 2).toNat →ₐ[ℤ] integralClosure ℤ ℂ :=
  (sourcePrimitiveH1HeckeCharacter f hk).codRestrict _
    (sourcePrimitiveH1HeckeCharacter_isIntegral f hk)

/-- The integral H1 character retains its exact original complex value. -/
theorem sourcePrimitiveIntegralH1HeckeCharacter_coe (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (T : sourceBinaryH1HeckeAlgebra Q (k - 2).toNat) :
    (sourcePrimitiveIntegralH1HeckeCharacter f hk T : ℂ) =
      sourcePrimitiveH1HeckeCharacter f hk T := rfl

/-- The original good-prime H1 character value is precisely the algebraic integer given by its Fourier coefficient. -/
theorem sourcePrimitiveIntegralH1HeckeCharacter_hecke (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (p : sourceBinaryHeckePrime Q) :
    sourcePrimitiveIntegralH1HeckeCharacter f hk
      ⟨sourceBinaryH1PrimeOperators ℤ Q (k - 2).toNat p,
        Algebra.subset_adjoin ⟨p, rfl⟩⟩ =
      ⟨cuspCoefficients f.toCuspForm p.val, sourcePrimitiveCoefficient_isIntegral f hk p.val⟩ := by
  apply Subtype.ext
  exact sourcePrimitiveH1HeckeCharacter_hecke f hk p

/-- The actual integral H1 and analytic primitive Hecke characters agree on every original good prime. -/
theorem sourcePrimitiveIntegralH1HeckeCharacter_original (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (p : sourceBinaryHeckePrime Q) :
    sourcePrimitiveIntegralH1HeckeCharacter f hk
      ⟨sourceBinaryH1PrimeOperators ℤ Q (k - 2).toNat p,
        Algebra.subset_adjoin ⟨p, rfl⟩⟩ =
      sourcePrimitiveIntegralHeckeCharacter f hk
        ⟨cuspHeckeLinear Q k p.val, Algebra.subset_adjoin
          ⟨(⟨p.val, p.property.1.pos⟩ : ℕ+), rfl⟩⟩ := by
  apply Subtype.ext
  rw [sourcePrimitiveIntegralH1HeckeCharacter_coe,
    sourcePrimitiveH1HeckeCharacter_hecke, sourcePrimitiveIntegralHeckeCharacter_coe]
  exact (sourcePrimitiveHeckeCharacter_hecke f ⟨p.val, p.property.1.pos⟩).symm

end
end Dubon2026
