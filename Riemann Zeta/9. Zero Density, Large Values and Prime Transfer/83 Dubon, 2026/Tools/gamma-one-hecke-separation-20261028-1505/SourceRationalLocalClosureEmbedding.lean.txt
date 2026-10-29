import Dubon2026.SourceRationalLocalValuation

/-! DUB-17/18 -> original all-weight association -> all-good-prime
operators on the actual diamond quotient. Native algebraic-closure
lifting supplies an embedding into each original rational local closure.
Only its existence is needed for Hecke stability; prescribed arithmetic
compatibility remains available in the separate native extension theorem. -/
namespace Dubon2026
noncomputable section
attribute [local instance] rationalPrimeLocalField_charZero
local notation "Qbar" => AlgebraicClosure ℚ
private local instance : IsGalois ℚ Qbar := sourceRationalAlgebraicClosure_isGalois

theorem sourceRationalLocalClosure_nonempty_embedding (q : ℕ) (hq : q.Prime) :
    Nonempty (Qbar →ₐ[ℚ] rationalPrimeLocalClosure q hq) :=
  ⟨IsAlgClosed.lift⟩

end
end Dubon2026
