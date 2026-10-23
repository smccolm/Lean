import Dubon2026.SourceAllPrimeHeckeCharacters
import Dubon2026.SourceAllPrimeCosetPointTransition
import Dubon2026.SourceOriginalCuspPeriodLattice

/-! DUB-17/18 -> rational rank-two Hecke descent -> actual all-prime
period-character compatibility. Reindex the proved primitive trace by the
Gamma action on genuine cosets. The exact transition formula turns each
term into its period character plus a correction; the finite correction
sum cancels. No bad-prime integration or cohomology comparison is assumed.
-/
namespace Dubon2026
noncomputable section
open UpperHalfPlane CongruenceSubgroup SourceFunctionField SourceFunctionField.OriginalChart
open scoped MatrixGroups
variable (N : ℕ) [NeZero N]
private local instance (ell : Nat.Primes) : NeZero ell.val := ⟨ell.property.ne_zero⟩

theorem sourceAllPrimePeriodValue_hecke (ell : Nat.Primes)
    (f : CuspForm (Gamma0 N) 2) (γ : Gamma0 N) :
    sourceWeightTwoPeriodValue (Gamma0 N) (cuspHeckePrime ell.property f) γ =
      sourceAllPrimeHeckeHom ℂ N ell (sourceWeightTwoPeriodHom (Gamma0 N) f) (Additive.ofMul γ) := by
  letI := sourceHeckeUpperFintype N ell.val
  let G := sourceWeightTwoPrimitive 1 f
  have ht (q : Gamma0 N ⧸ heckeUpperSubgroup N ell.val) :
      G (originalHeckeCosetPoint N ell.val (γ.val • I) (γ • q)) -
        G (originalHeckeCosetPoint N ell.val I (γ • q)) =
      G (originalHeckeCosetPoint N ell.val I q) +
        sourceWeightTwoPeriodValue (Gamma0 N) f
          (sourceHeckeConjugation ell.property (cosetTransition (heckeUpperSubgroup N ell.val) γ q)) -
        G (originalHeckeCosetPoint N ell.val I (γ • q)) := by
    dsimp only [G]
    rw [originalHeckeCosetPoint_transition N ell.val ell.property, original_cusp_primitive_period]
  have hd := originalHeckePrimitiveTrace_all_difference N ell.val ell.property f I (γ.val • I)
  rw [original_cusp_primitive_period, add_sub_cancel_left] at hd
  have hr := Equiv.sum_comp (MulAction.toPerm γ)
    (fun q : Gamma0 N ⧸ heckeUpperSubgroup N ell.val => G (originalHeckeCosetPoint N ell.val I q))
  change (∑ q : Gamma0 N ⧸ heckeUpperSubgroup N ell.val,
    G (originalHeckeCosetPoint N ell.val I (γ • q))) =
    ∑ q : Gamma0 N ⧸ heckeUpperSubgroup N ell.val, G (originalHeckeCosetPoint N ell.val I q) at hr
  have he := Equiv.sum_comp (MulAction.toPerm γ)
    (fun q : Gamma0 N ⧸ heckeUpperSubgroup N ell.val =>
      G (originalHeckeCosetPoint N ell.val (γ.val • I) q) - G (originalHeckeCosetPoint N ell.val I q))
  rw [sourceAllPrimeHeckeHom_apply]
  rw [← hd, ← he]
  change (∑ q : Gamma0 N ⧸ heckeUpperSubgroup N ell.val,
    (G (originalHeckeCosetPoint N ell.val (γ.val • I) (γ • q)) -
      G (originalHeckeCosetPoint N ell.val I (γ • q)))) = _
  rw [Finset.sum_congr rfl (fun q _ => ht q)]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hr]
  change (∑ q : Gamma0 N ⧸ heckeUpperSubgroup N ell.val,
      G (originalHeckeCosetPoint N ell.val I q)) +
      (∑ q : Gamma0 N ⧸ heckeUpperSubgroup N ell.val,
        sourceWeightTwoPeriodValue (Gamma0 N) f
          (sourceHeckeConjugation ell.property (cosetTransition (heckeUpperSubgroup N ell.val) γ q))) -
      (∑ q : Gamma0 N ⧸ heckeUpperSubgroup N ell.val, G (originalHeckeCosetPoint N ell.val I q)) = _
  exact add_sub_cancel_left _ _

theorem sourceAllPrimePeriodHom_hecke (ell : Nat.Primes) (f : CuspForm (Gamma0 N) 2) :
    sourceWeightTwoPeriodHom (Gamma0 N) (cuspHeckePrime ell.property f) =
      sourceAllPrimeHeckeHom ℂ N ell (sourceWeightTwoPeriodHom (Gamma0 N) f) := by
  ext γ
  exact sourceAllPrimePeriodValue_hecke N ell f γ

end
end Dubon2026
