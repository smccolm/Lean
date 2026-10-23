import Dubon2026.SourcePrimeTwoProduct
import Dubon2026.SourceEllipticVeluTwoEnumeration

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> continuation -> original
Frobenius/inertia -> good reduction -> reverse genus -> elliptic inertia orbits
-> cyclic-quotient interpretation of integral modular-polynomial roots.
This step factors the explicit classical prime-two polynomial into the j-values
of the three actual degree-two Velu curves. Identification of this explicit
polynomial with the existing integral minimal polynomial is a separate required
bridge. The quotient group homomorphism and its kernel remain required too.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, the VeluQuotient2 cFour/j solutions,
Def_ModularCurve_ClassicalModularPolynomials, Def_ModularCurve_FibrePoly and
S_ModularCurve_fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j. -/
namespace Dubon2026.SourcePrimeTwoPolynomial
open Polynomial WeierstrassCurve
open Dubon2026.SourceEllipticVelu
noncomputable section
theorem exists_enumerated_prime_two_product
    {K : Type*} [Field K] [IsAlgClosed K] (h2 : (2 : K) ≠ 0)
    (W : WeierstrassCurve K) [W.IsElliptic] :
    ∃ (ι : Type) (_ : Fintype ι), Fintype.card ι = 3 ∧
      ∃ (P : ι → K × K) (_ : Function.Injective P)
        (_ : ∀ i, W.toAffine.Equation (P i).1 (P i).2)
        (_ : ∀ i, veluGy W (P i).1 (P i).2 = 0)
        (hΔ : ∀ i, (veluQuotient2 W (P i).1 (P i).2).Δ ≠ 0),
        fibrePoly phiTwo W.j =
          ∏ i, (X - C (@WeierstrassCurve.j K _ (veluQuotient2 W (P i).1 (P i).2)
            ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)) := by
  obtain ⟨ι, hfin, hι, P, hinj, heq, hgy, hΔ⟩ :=
    exists_enum_twoTorsion_veluQuotient2_discriminant_ne_zero h2 W
  exact ⟨ι, hfin, hι, P, hinj, heq, hgy, hΔ,
    fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j h2 W hι P hinj heq hgy hΔ⟩

end
end Dubon2026.SourcePrimeTwoPolynomial
