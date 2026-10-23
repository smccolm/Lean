import Dubon2026.SourceIntegralPrimeTwoIdentification
import Dubon2026.SourcePrimeTwoEnumeratedProduct
import Dubon2026.SourceEllipticVeluTwoQuotientFibers

/-! The actual integral modular polynomial at level two factors into the
j-invariants of the three actual degree-two quotient curves. Each quotient
map is the proved surjective homomorphism with its two-element cyclic kernel
and two-element fibers. The algebraic identity is integral, so specialization
retains every algebraically closed characteristic other than two, including
three. This discharges the degree-two polynomial and quotient-map inputs to
the cyclic-subgroup root interpretation and inertia census, DUB-17/18.
Odd-prime quotients, the root correspondence and inertia census remain open. -/
namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
noncomputable section
open Polynomial WeierstrassCurve
open Dubon2026.SourcePrimeTwoPolynomial Dubon2026.SourceEllipticVelu

theorem exists_integral_prime_two_quotient_product
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] (h2 : (2 : K) ≠ 0)
    (W : WeierstrassCurve K) [W.IsElliptic] :
    ∃ (ι : Type) (_ : Fintype ι), Fintype.card ι = 3 ∧
      ∃ (P : ι → K × K) (_ : Function.Injective P)
        (heq : ∀ i, W.toAffine.Equation (P i).1 (P i).2)
        (hgy : ∀ i, veluGy W (P i).1 (P i).2 = 0)
        (hΔ : ∀ i, (veluQuotient2 W (P i).1 (P i).2).Δ ≠ 0),
        fibrePoly (modularPolynomial 2) W.j =
          ∏ i, (X - C (@WeierstrassCurve.j K _ (veluQuotient2 W (P i).1 (P i).2)
            ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)) ∧
        ∀ i, Nat.card (veluTwoHom (heq i) (hgy i)).ker = 2 ∧
          ∀ Q, Nat.card {R : W.toAffine.Point // veluTwoHom (heq i) (hgy i) R = Q} = 2 := by
  obtain ⟨ι, hfin, hι, P, hinj, heq, hgy, hΔ, hprod⟩ :=
    exists_enumerated_prime_two_product h2 W
  refine ⟨ι, hfin, hι, P, hinj, heq, hgy, hΔ, ?_, ?_⟩
  · rw [modularPolynomial_two_eq_phiTwo]
    exact hprod
  · intro i
    exact ⟨veluTwoHom_kernel_cardinality (heq i) (hgy i),
      veluTwoHom_fiber_cardinality (heq i) (hgy i)⟩

end
end Dubon2026.SourceFunctionField.IntegralJCoordinate
