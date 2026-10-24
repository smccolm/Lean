import Dubon2026.SourceIntegralPrimeAnalyticProduct
import Dubon2026.SourceEllipticOddQuotientGeneratorJ
import Dubon2026.SourceEllipticStandardOddQuotientJ
import Dubon2026.SourceIntegralOddQuotientProduct

/-! The exact integral modular polynomial is the product of all actual
odd-prime cyclic quotient factors over the complex numbers. Every quotient
map, kernel, period model and analytic j-factor has been constructed. The
family may use arbitrary generators of distinct subgroups. This closes the
complex product obligation before characteristic-zero descent and integral
reduction on the DUB-17/18 cyclic-root dependency chain. -/

namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
open Polynomial WeierstrassCurve UpperHalfPlane SourceEllipticPeriod
open SourceEllipticVelu.OddDiscriminant

theorem modularPolynomial_eq_oddQuotientProduct_period_model
    (τ : ℍ) (C : VariableChange ℂ) (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (Q : Fin (p + 1) → (C • periodCurve (PeriodLattice.ofTau τ)).toAffine.Point)
    (hQ : ∀ i, addOrderOf (Q i) = 2 * (p / 2) + 1)
    (hinj : Function.Injective (fun i => AddSubgroup.zmultiples (Q i))) :
    relationAtSeed (modularPolynomial p) (C • periodCurve (PeriodLattice.ofTau τ)).j =
      oddQuotientProduct (C • periodCurve (PeriodLattice.ofTau τ)) hQ := by
  classical
  have hodd : 2 * (p / 2) + 1 = p := by
    rcases hp.out.eq_two_or_odd' with h | h
    · exact (hp2 h).elim
    · exact Nat.two_mul_div_two_add_one_of_odd h
  have hR : ∀ i, addOrderOf (standardTorsionPoint τ C p i) = 2 * (p / 2) + 1 :=
    fun i => (standardTorsionPoint_order τ C p i).trans hodd.symm
  have hex : ∀ i, ∃ j,
      AddSubgroup.zmultiples (standardTorsionPoint τ C p j) = AddSubgroup.zmultiples (Q i) := by
    intro i
    exact standardTorsionPoint_zmultiples_complete τ C p _ inferInstance
      ((Nat.card_zmultiples _).trans ((hQ i).trans hodd))
  choose f hf using hex
  have hfi : Function.Injective f := by
    intro i j hij
    apply hinj
    change AddSubgroup.zmultiples (Q i) = AddSubgroup.zmultiples (Q j)
    rw [← hf i, ← hf j, hij]
  let e : Fin (p + 1) ≃ Fin (p + 1) :=
    Equiv.ofBijective f ⟨hfi, Finite.surjective_of_injective hfi⟩
  have hj (i : Fin (p + 1)) :
      oddQuotientJ (C • periodCurve (PeriodLattice.ofTau τ)) (hQ i) =
        JMultiplicity.jf (rep p (e i) • τ) := by
    exact (oddQuotientJ_eq_of_zmultiples_eq _ (hQ i) (hR (f i)) (hf i).symm).trans
      (standardOddQuotientJ_eq τ C p (f i) (hR (f i)))
  rw [variableChange_j, periodCurve_ofTau_j, modularPolynomial_prime_analytic_product,
    oddQuotientProduct]
  simp_rw [hj]
  exact e.prod_comp (fun i => X - Polynomial.C (JMultiplicity.jf (rep p i • τ))) |>.symm

theorem modularPolynomial_eq_oddQuotientProduct_complex
    (W : WeierstrassCurve ℂ) [W.IsElliptic] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (Q : Fin (p + 1) → W.toAffine.Point)
    (hQ : ∀ i, addOrderOf (Q i) = 2 * (p / 2) + 1)
    (hinj : Function.Injective (fun i => AddSubgroup.zmultiples (Q i))) :
    relationAtSeed (modularPolynomial p) W.j = oddQuotientProduct W hQ := by
  obtain ⟨τ, C, hC⟩ := exists_complex_period_model W
  subst W
  exact modularPolynomial_eq_oddQuotientProduct_period_model τ C p hp2 Q hQ hinj

end Dubon2026.SourceFunctionField.IntegralJCoordinate
