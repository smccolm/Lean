import Dubon2026.SourcePrimeTwoPolynomial

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
variable {K : Type*} [Field K] {x0 x1 x2 c4 Δ g0 g1 g2 d0 d1 d2 : K}

private theorem sixteen_ne_zero (h2 : (2 : K) ≠ 0) : (16 : K) ≠ 0 := by
  rw [show (16 : K) = 2 ^ 4 by norm_num]; exact pow_ne_zero _ h2

theorem coeff_two_identity (h01 : x0 ≠ x1) (h02 : x0 ≠ x2) (h12 : x1 ≠ x2) (h2 : (2 : K) ≠ 0)
    (hc4 : c4 = 16 * (x0 ^ 2 + x1 ^ 2 + x2 ^ 2 - x0 * x1 - x0 * x2 - x1 * x2))
    (hΔ : Δ = 16 * (x0 - x1) ^ 2 * (x0 - x2) ^ 2 * (x1 - x2) ^ 2)
    (hg0 : g0 = (x0 - x1) * (x0 - x2)) (hg1 : g1 = (x1 - x0) * (x1 - x2))
    (hg2 : g2 = (x2 - x0) * (x2 - x1))
    (hd0 : d0 = 16 * (x1 - x2) ^ 2) (hd1 : d1 = 16 * (x0 - x2) ^ 2) (hd2 : d2 = 16 * (x0 - x1) ^ 2) :
    -(c4 ^ 3 / Δ) ^ 2 + 1488 * (c4 ^ 3 / Δ) - 162000
      = -((c4 + 240 * g0) ^ 3 / (g0 * d0 ^ 2) + (c4 + 240 * g1) ^ 3 / (g1 * d1 ^ 2)
          + (c4 + 240 * g2) ^ 3 / (g2 * d2 ^ 2)) := by
  have h16 := sixteen_ne_zero h2
  have h01' := sub_ne_zero.mpr h01; have h02' := sub_ne_zero.mpr h02; have h12' := sub_ne_zero.mpr h12
  have h10' := sub_ne_zero.mpr h01.symm; have h20' := sub_ne_zero.mpr h02.symm
  have h21' := sub_ne_zero.mpr h12.symm
  subst hc4 hΔ hg0 hg1 hg2 hd0 hd1 hd2
  field_simp
  ring

theorem coeff_one_identity (h01 : x0 ≠ x1) (h02 : x0 ≠ x2) (h12 : x1 ≠ x2) (h2 : (2 : K) ≠ 0)
    (hc4 : c4 = 16 * (x0 ^ 2 + x1 ^ 2 + x2 ^ 2 - x0 * x1 - x0 * x2 - x1 * x2))
    (hΔ : Δ = 16 * (x0 - x1) ^ 2 * (x0 - x2) ^ 2 * (x1 - x2) ^ 2)
    (hg0 : g0 = (x0 - x1) * (x0 - x2)) (hg1 : g1 = (x1 - x0) * (x1 - x2))
    (hg2 : g2 = (x2 - x0) * (x2 - x1))
    (hd0 : d0 = 16 * (x1 - x2) ^ 2) (hd1 : d1 = 16 * (x0 - x2) ^ 2) (hd2 : d2 = 16 * (x0 - x1) ^ 2) :
    1488 * (c4 ^ 3 / Δ) ^ 2 + 40773375 * (c4 ^ 3 / Δ) + 8748000000
      = (c4 + 240 * g0) ^ 3 / (g0 * d0 ^ 2) * ((c4 + 240 * g1) ^ 3 / (g1 * d1 ^ 2))
        + (c4 + 240 * g0) ^ 3 / (g0 * d0 ^ 2) * ((c4 + 240 * g2) ^ 3 / (g2 * d2 ^ 2))
        + (c4 + 240 * g1) ^ 3 / (g1 * d1 ^ 2) * ((c4 + 240 * g2) ^ 3 / (g2 * d2 ^ 2)) := by
  have h16 := sixteen_ne_zero h2
  have h01' := sub_ne_zero.mpr h01; have h02' := sub_ne_zero.mpr h02; have h12' := sub_ne_zero.mpr h12
  have h10' := sub_ne_zero.mpr h01.symm; have h20' := sub_ne_zero.mpr h02.symm
  have h21' := sub_ne_zero.mpr h12.symm
  subst hc4 hΔ hg0 hg1 hg2 hd0 hd1 hd2
  field_simp
  ring

theorem coeff_zero_identity (h01 : x0 ≠ x1) (h02 : x0 ≠ x2) (h12 : x1 ≠ x2) (h2 : (2 : K) ≠ 0)
    (hc4 : c4 = 16 * (x0 ^ 2 + x1 ^ 2 + x2 ^ 2 - x0 * x1 - x0 * x2 - x1 * x2))
    (hΔ : Δ = 16 * (x0 - x1) ^ 2 * (x0 - x2) ^ 2 * (x1 - x2) ^ 2)
    (hg0 : g0 = (x0 - x1) * (x0 - x2)) (hg1 : g1 = (x1 - x0) * (x1 - x2))
    (hg2 : g2 = (x2 - x0) * (x2 - x1))
    (hd0 : d0 = 16 * (x1 - x2) ^ 2) (hd1 : d1 = 16 * (x0 - x2) ^ 2) (hd2 : d2 = 16 * (x0 - x1) ^ 2) :
    (c4 ^ 3 / Δ) ^ 3 - 162000 * (c4 ^ 3 / Δ) ^ 2 + 8748000000 * (c4 ^ 3 / Δ) - 157464000000000
      = -((c4 + 240 * g0) ^ 3 / (g0 * d0 ^ 2) * ((c4 + 240 * g1) ^ 3 / (g1 * d1 ^ 2))
          * ((c4 + 240 * g2) ^ 3 / (g2 * d2 ^ 2))) := by
  have h16 := sixteen_ne_zero h2
  have h01' := sub_ne_zero.mpr h01; have h02' := sub_ne_zero.mpr h02; have h12' := sub_ne_zero.mpr h12
  have h10' := sub_ne_zero.mpr h01.symm; have h20' := sub_ne_zero.mpr h02.symm
  have h21' := sub_ne_zero.mpr h12.symm
  subst hc4 hΔ hg0 hg1 hg2 hd0 hd1 hd2
  field_simp
  ring


end
end Dubon2026.SourcePrimeTwoPolynomial
