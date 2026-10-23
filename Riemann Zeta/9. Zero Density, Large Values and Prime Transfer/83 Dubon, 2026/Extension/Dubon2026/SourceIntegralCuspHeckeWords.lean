import Dubon2026.SourceCuspDualHeckeWords

/-! DUB-17/18 -> prescribed primitive eigenvalue specialization -> the
actual integral cusp Hecke quotient of prime words. Existing integral
membership and word generation give the literal surjective evaluation. -/
namespace Dubon2026
noncomputable section
variable (N : ℕ) [NeZero N]

/-- Prime-word evaluation into the actual original integral weight-two cusp Hecke algebra. -/
def sourceIntegralCuspHeckeWord :
    FreeAlgebra ℤ Nat.Primes →ₐ[ℤ] sourceOriginalIntegralHeckeAlgebra N 2 :=
  (sourceWeightTwoCuspHeckeWord N).codRestrict _ (sourceWeightTwoCuspHeckeWord_mem_integral N)

theorem sourceIntegralCuspHeckeWord_surjective : Function.Surjective (sourceIntegralCuspHeckeWord N) := by
  intro t
  obtain ⟨a, ha⟩ := sourceWeightTwoCuspHeckeWord_exists N t
  exact ⟨a, Subtype.ext ha⟩

theorem sourceIntegralCuspHeckeWord_prime (ell : Nat.Primes) :
    (sourceIntegralCuspHeckeWord N (FreeAlgebra.ι ℤ ell)).val = cuspHeckeLinear N 2 ell.val :=
  FreeAlgebra.lift_ι_apply _ ell

end
end Dubon2026
