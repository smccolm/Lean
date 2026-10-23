import Dubon2026.SourceEllipticVeluTwoSecantXRelations

/-! Remaining coordinate and case analysis for the actual degree-two Velu
group homomorphism. The dependency is DUB-17 / DUB-18 -> continuation -> good
reduction -> reverse genus -> elliptic inertia census -> cyclic-quotient root
interpretation -> quotient homomorphisms with their actual cyclic kernels.
Compatibility predicates in intermediate lemmas describe explicit secant and
tangent coordinate obligations; the final consumer must derive them all.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2. All source option
changes and irrelevant logical anchors are omitted. -/
namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve Polynomial
noncomputable section
section Field

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {x₀ y₀ x y : F}

end Field

section CommRing

variable {R : Type*} [CommRing R] {W : WeierstrassCurve R} {x₀ y₀ x y : R}

theorem velu2_tanY_SI2c (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0) :
    (2 * y + W.a₁ * x + W.a₃) ^ 3 * ((x - x₀) ^ 2 - veluGx W x₀ y₀) * (y - y₀)
        + (W.a₁ ^ 2 * (x - x₀)
              + 4 * (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y₀))
          * (x - x₀) ^ 2
          * ((3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) ^ 2
              + W.a₁ * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * (2 * y + W.a₁ * x + W.a₃)
              - (W.a₂ + 2 * x + x₀) * (2 * y + W.a₁ * x + W.a₃) ^ 2)
        - ((x - x₀) ^ 2 - veluGx W x₀ y₀) * (x - x₀)
          * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * (2 * y + W.a₁ * x + W.a₃) ^ 2
      = 0 := by
  rw [WeierstrassCurve.Affine.equation_iff] at hP hQ
  simp only [veluGx]
  linear_combination
    (-W.a₁^4*x^3 + 3*W.a₁^4*x^2*x₀ - 3*W.a₁^4*x*x₀^2 + W.a₁^4*x₀^3 + 6*W.a₁^3*x^2*y₀ - 12*W.a₁^3*x*x₀*y₀ + 6*W.a₁^3*x₀^2*y₀ - 8*W.a₁^2*W.a₂*x^3 + 12*W.a₁^2*W.a₂*x^2*x₀ - 4*W.a₁^2*W.a₂*x₀^3 - 6*W.a₁^2*W.a₄*x^2 + 12*W.a₁^2*W.a₄*x*x₀ - 6*W.a₁^2*W.a₄*x₀^2 - 10*W.a₁^2*x^4 + 16*W.a₁^2*x^3*x₀ - 6*W.a₁^2*x^2*x₀^2 + 4*W.a₁^2*x*x₀^3 + 8*W.a₁^2*x*y*y₀ - 12*W.a₁^2*x*y₀^2 - 4*W.a₁^2*x₀^4 - 8*W.a₁^2*x₀*y*y₀ + 12*W.a₁^2*x₀*y₀^2 + 16*W.a₁*W.a₂*x^2*y₀ - 16*W.a₁*W.a₂*x*x₀*y + 16*W.a₁*W.a₂*x₀^2*y - 8*W.a₁*W.a₂*x₀^2*y₀ - 8*W.a₁*W.a₄*x*y + 16*W.a₁*W.a₄*x*y₀ + 8*W.a₁*W.a₄*x₀*y - 8*W.a₁*W.a₄*x₀*y₀ + 8*W.a₁*W.a₆*y₀ + 8*W.a₁*x^3*y + 16*W.a₁*x^3*y₀ - 24*W.a₁*x^2*x₀*y + 16*W.a₁*x₀^3*y - 8*W.a₁*x₀^3*y₀ + 8*W.a₁*y^2*y₀ - 16*W.a₁*y*y₀^2 + 16*W.a₁*y₀^3 - 16*W.a₂^2*x^3 + 16*W.a₂^2*x^2*x₀ - 16*W.a₂^2*x₀^3 - 16*W.a₂*W.a₄*x^2 + 16*W.a₂*W.a₄*x*x₀ - 24*W.a₂*W.a₄*x₀^2 - 16*W.a₂*W.a₆*x₀ - 48*W.a₂*x^4 + 48*W.a₂*x^3*x₀ + 8*W.a₂*x^2*x₀^2 - 16*W.a₂*x*x₀^3 - 32*W.a₂*x₀^4 - 16*W.a₂*x₀*y^2 + 32*W.a₂*x₀*y*y₀ - 32*W.a₂*x₀*y₀^2 - 4*W.a₄^2*x - 4*W.a₄^2*x₀ - 8*W.a₄*W.a₆ - 24*W.a₄*x^3 + 32*W.a₄*x^2*x₀ - 16*W.a₄*x*x₀^2 - 24*W.a₄*x₀^3 - 8*W.a₄*y^2 + 16*W.a₄*y*y₀ - 16*W.a₄*y₀^2 + 8*W.a₆*x^2 - 16*W.a₆*x*x₀ - 16*W.a₆*x₀^2 - 36*x^5 + 36*x^4*x₀ + 8*x^2*x₀^3 + 8*x^2*y^2 - 16*x^2*y*y₀ + 16*x^2*y₀^2 - 16*x*x₀^4 - 16*x*x₀*y^2 + 32*x*x₀*y*y₀ - 32*x*x₀*y₀^2 - 16*x₀^5 - 16*x₀^2*y^2 + 32*x₀^2*y*y₀ - 32*x₀^2*y₀^2) * hP
    + (W.a₁^4*x^3 - 3*W.a₁^4*x^2*x₀ + 3*W.a₁^4*x*x₀^2 - W.a₁^4*x₀^3 - 6*W.a₁^3*x^2*y₀ + 12*W.a₁^3*x*x₀*y₀ - 6*W.a₁^3*x₀^2*y₀ + 8*W.a₁^2*W.a₂*x^3 - 12*W.a₁^2*W.a₂*x^2*x₀ + 4*W.a₁^2*W.a₂*x₀^3 + 6*W.a₁^2*W.a₄*x^2 - 12*W.a₁^2*W.a₄*x*x₀ + 6*W.a₁^2*W.a₄*x₀^2 + 10*W.a₁^2*x^4 - 16*W.a₁^2*x^3*x₀ + 6*W.a₁^2*x^2*x₀^2 - 4*W.a₁^2*x*x₀^3 + 12*W.a₁^2*x*y₀^2 + 4*W.a₁^2*x₀^4 - 12*W.a₁^2*x₀*y₀^2 - 24*W.a₁*W.a₂*x^2*y₀ + 16*W.a₁*W.a₂*x₀^2*y₀ - 24*W.a₁*W.a₄*x*y₀ + 16*W.a₁*W.a₄*x₀*y₀ - 8*W.a₁*W.a₆*y₀ - 24*W.a₁*x^3*y₀ + 16*W.a₁*x₀^3*y₀ - 8*W.a₁*y₀^3 + 16*W.a₂^2*x^3 + 24*W.a₂*W.a₄*x^2 + 16*W.a₂*W.a₆*x₀ + 40*W.a₂*x^4 - 16*W.a₂*x^3*x₀ + 16*W.a₂*x^2*x₀^2 + 16*W.a₂*x₀*y₀^2 + 12*W.a₄^2*x - 4*W.a₄^2*x₀ + 8*W.a₄*W.a₆ + 24*W.a₄*x^3 - 8*W.a₄*x^2*x₀ + 16*W.a₄*x*x₀^2 + 8*W.a₄*y₀^2 - 8*W.a₆*x^2 + 16*W.a₆*x*x₀ + 16*W.a₆*x₀^2 + 28*x^5 - 20*x^4*x₀ + 16*x^3*x₀^2 - 8*x^2*y₀^2 + 16*x*x₀*y₀^2 + 16*x₀^2*y₀^2) * hQ
    + (-W.a₁^4*x^3*y₀ + 3*W.a₁^4*x^2*x₀*y₀ - 3*W.a₁^4*x*x₀^2*y₀ + W.a₁^4*x₀^3*y₀ + W.a₁^3*W.a₂*x^3*x₀ - 3*W.a₁^3*W.a₂*x^2*x₀^2 + 3*W.a₁^3*W.a₂*x*x₀^3 - W.a₁^3*W.a₂*x₀^4 + W.a₁^3*W.a₄*x^3 - 3*W.a₁^3*W.a₄*x^2*x₀ + 3*W.a₁^3*W.a₄*x*x₀^2 - W.a₁^3*W.a₄*x₀^3 - W.a₁^3*x^5 + 3*W.a₁^3*x^4*x₀ - 2*W.a₁^3*x^3*x₀^2 - 2*W.a₁^3*x^2*x₀^3 + 3*W.a₁^3*x^2*y*y₀ + 3*W.a₁^3*x^2*y₀^2 + 3*W.a₁^3*x*x₀^4 - 2*W.a₁^3*x*x₀*y*y₀ - 9*W.a₁^3*x*x₀*y₀^2 - W.a₁^3*x₀^5 + 5*W.a₁^3*x₀^2*y₀^2 - W.a₁^2*W.a₂*W.a₃*x^3 + 3*W.a₁^2*W.a₂*W.a₃*x^2*x₀ - 3*W.a₁^2*W.a₂*W.a₃*x*x₀^2 + W.a₁^2*W.a₂*W.a₃*x₀^3 - 10*W.a₁^2*W.a₂*x^3*y₀ - 6*W.a₁^2*W.a₂*x^2*x₀*y + 14*W.a₁^2*W.a₂*x^2*x₀*y₀ + 4*W.a₁^2*W.a₂*x*x₀^2*y + 6*W.a₁^2*W.a₂*x*x₀^2*y₀ - 8*W.a₁^2*W.a₂*x₀^3*y₀ - 2*W.a₁^2*W.a₃*x^4 + 5*W.a₁^2*W.a₃*x^3*x₀ - 3*W.a₁^2*W.a₃*x^2*x₀^2 - W.a₁^2*W.a₃*x*x₀^3 + 4*W.a₁^2*W.a₃*x*y*y₀ - 3*W.a₁^2*W.a₃*x*y₀^2 + W.a₁^2*W.a₃*x₀^4 - 2*W.a₁^2*W.a₃*x₀*y*y₀ + W.a₁^2*W.a₃*x₀*y₀^2 - 3*W.a₁^2*W.a₄*x^2*y - 9*W.a₁^2*W.a₄*x^2*y₀ + 2*W.a₁^2*W.a₄*x*x₀*y + 20*W.a₁^2*W.a₄*x*x₀*y₀ - 10*W.a₁^2*W.a₄*x₀^2*y₀ + 3*W.a₁^2*x^4*y - 11*W.a₁^2*x^4*y₀ - 8*W.a₁^2*x^3*x₀*y + 16*W.a₁^2*x^3*x₀*y₀ - 2*W.a₁^2*x^2*x₀^2*y - 4*W.a₁^2*x^2*x₀^2*y₀ + 4*W.a₁^2*x*x₀^3*y + 10*W.a₁^2*x*x₀^3*y₀ + 8*W.a₁^2*x*y^2*y₀ - 8*W.a₁^2*x*y*y₀^2 - 6*W.a₁^2*x*y₀^3 - 8*W.a₁^2*x₀^4*y₀ - 2*W.a₁^2*x₀*y^2*y₀ + 8*W.a₁^2*x₀*y₀^3 + 12*W.a₁*W.a₂^2*x^3*x₀ - 16*W.a₁*W.a₂^2*x^2*x₀^2 + 4*W.a₁*W.a₂^2*x₀^4 + 2*W.a₁*W.a₂*W.a₃*x^2*y₀ - 8*W.a₁*W.a₂*W.a₃*x*x₀*y + 4*W.a₁*W.a₂*W.a₃*x₀^2*y + 2*W.a₁*W.a₂*W.a₃*x₀^2*y₀ + 8*W.a₁*W.a₂*W.a₄*x^3 - 2*W.a₁*W.a₂*W.a₄*x^2*x₀ - 16*W.a₁*W.a₂*W.a₄*x*x₀^2 + 10*W.a₁*W.a₂*W.a₄*x₀^3 - 8*W.a₁*W.a₂*x^5 + 34*W.a₁*W.a₂*x^4*x₀ - 20*W.a₁*W.a₂*x^3*x₀^2 - 10*W.a₁*W.a₂*x^2*x₀^3 - 8*W.a₁*W.a₂*x^2*y*y₀ + 20*W.a₁*W.a₂*x^2*y₀^2 - 4*W.a₁*W.a₂*x*x₀^4 - 16*W.a₁*W.a₂*x*x₀*y^2 + 16*W.a₁*W.a₂*x*x₀*y*y₀ + 8*W.a₁*W.a₂*x₀^5 + 4*W.a₁*W.a₂*x₀^2*y^2 - 16*W.a₁*W.a₂*x₀^2*y₀^2 + W.a₁*W.a₃^2*y*y₀ - W.a₁*W.a₃^2*y₀^2 - 4*W.a₁*W.a₃*W.a₄*x*y + 2*W.a₁*W.a₃*W.a₄*x*y₀ + 2*W.a₁*W.a₃*W.a₄*x₀*y + 4*W.a₁*W.a₃*x^3*y + 2*W.a₁*W.a₃*x^3*y₀ - 10*W.a₁*W.a₃*x^2*x₀*y - 2*W.a₁*W.a₃*x^2*x₀*y₀ - 4*W.a₁*W.a₃*x*x₀^2*y + 4*W.a₁*W.a₃*x*x₀^2*y₀ + 4*W.a₁*W.a₃*x₀^3*y + 2*W.a₁*W.a₃*x₀^3*y₀ + 6*W.a₁*W.a₃*y^2*y₀ - 8*W.a₁*W.a₃*y*y₀^2 + 2*W.a₁*W.a₃*y₀^3 + 6*W.a₁*W.a₄^2*x^2 - 11*W.a₁*W.a₄^2*x*x₀ + 5*W.a₁*W.a₄^2*x₀^2 + 4*W.a₁*W.a₄*x^4 + 2*W.a₁*W.a₄*x^3*x₀ - 16*W.a₁*W.a₄*x*x₀^3 - 8*W.a₁*W.a₄*x*y^2 + 20*W.a₁*W.a₄*x*y₀^2 + 10*W.a₁*W.a₄*x₀^4 + 2*W.a₁*W.a₄*x₀*y^2 - 14*W.a₁*W.a₄*x₀*y₀^2 - 8*W.a₁*W.a₆*y*y₀ + 8*W.a₁*W.a₆*y₀^2 - 10*W.a₁*x^6 + 25*W.a₁*x^5*x₀ - 5*W.a₁*x^4*x₀^2 - 12*W.a₁*x^3*x₀^3 + 8*W.a₁*x^3*y^2 - 16*W.a₁*x^3*y*y₀ + 20*W.a₁*x^3*y₀^2 + 2*W.a₁*x^2*x₀^4 - 18*W.a₁*x^2*x₀*y^2 + 16*W.a₁*x^2*x₀*y*y₀ + 2*W.a₁*x^2*x₀*y₀^2 - 4*W.a₁*x*x₀^5 - 12*W.a₁*x*x₀^2*y^2 + 16*W.a₁*x*x₀^2*y*y₀ - 4*W.a₁*x*x₀^2*y₀^2 + 4*W.a₁*x₀^6 + 4*W.a₁*x₀^3*y^2 - 16*W.a₁*x₀^3*y₀^2 + 4*W.a₁*y^3*y₀ - 8*W.a₁*y^2*y₀^2 + 4*W.a₁*y₀^4 - 4*W.a₂^2*W.a₃*x^3 + 8*W.a₂^2*W.a₃*x^2*x₀ - 4*W.a₂^2*W.a₃*x₀^3 - 8*W.a₂^2*x^3*y₀ + 16*W.a₂^2*x^2*x₀*y - 16*W.a₂^2*x^2*x₀*y₀ + 8*W.a₂^2*x₀^3*y₀ - 2*W.a₂*W.a₃^2*x₀*y + 2*W.a₂*W.a₃^2*x₀*y₀ - 2*W.a₂*W.a₃*W.a₄*x^2 + 8*W.a₂*W.a₃*W.a₄*x*x₀ - 6*W.a₂*W.a₃*W.a₄*x₀^2 - 14*W.a₂*W.a₃*x^4 + 20*W.a₂*W.a₃*x^3*x₀ + 6*W.a₂*W.a₃*x^2*x₀^2 - 4*W.a₂*W.a₃*x*x₀^3 - 8*W.a₂*W.a₃*x₀^4 - 12*W.a₂*W.a₃*x₀*y^2 + 16*W.a₂*W.a₃*x₀*y*y₀ - 4*W.a₂*W.a₃*x₀*y₀^2 + 8*W.a₂*W.a₄*x^2*y - 20*W.a₂*W.a₄*x^2*y₀ + 16*W.a₂*W.a₄*x*x₀*y - 16*W.a₂*W.a₄*x*x₀*y₀ + 12*W.a₂*W.a₄*x₀^2*y₀ + 16*W.a₂*W.a₆*x₀*y - 16*W.a₂*W.a₆*x₀*y₀ - 8*W.a₂*x^4*y - 12*W.a₂*x^4*y₀ + 32*W.a₂*x^3*x₀*y - 24*W.a₂*x^3*x₀*y₀ + 16*W.a₂*x^2*x₀^2*y - 28*W.a₂*x^2*x₀^2*y₀ + 8*W.a₂*x*x₀^3*y₀ + 16*W.a₂*x₀^4*y₀ - 8*W.a₂*x₀*y^3 + 16*W.a₂*x₀*y^2*y₀ - 8*W.a₂*x₀*y₀^3 - W.a₃^2*W.a₄*y + W.a₃^2*W.a₄*y₀ + W.a₃^2*x^2*y - W.a₃^2*x^2*y₀ - 2*W.a₃^2*x*x₀*y + 2*W.a₃^2*x*x₀*y₀ - 2*W.a₃^2*x₀^2*y + 2*W.a₃^2*x₀^2*y₀ + W.a₃*W.a₄^2*x - W.a₃*W.a₄^2*x₀ - 6*W.a₃*W.a₄*x^3 + 12*W.a₃*W.a₄*x^2*x₀ - 6*W.a₃*W.a₄*x₀^3 - 6*W.a₃*W.a₄*y^2 + 8*W.a₃*W.a₄*y*y₀ - 2*W.a₃*W.a₄*y₀^2 - 11*W.a₃*x^5 + 13*W.a₃*x^4*x₀ + 4*W.a₃*x^3*x₀^2 + 2*W.a₃*x^2*x₀^3 + 6*W.a₃*x^2*y^2 - 8*W.a₃*x^2*y*y₀ + 2*W.a₃*x^2*y₀^2 - 4*W.a₃*x*x₀^4 - 12*W.a₃*x*x₀*y^2 + 16*W.a₃*x*x₀*y*y₀ - 4*W.a₃*x*x₀*y₀^2 - 4*W.a₃*x₀^5 - 12*W.a₃*x₀^2*y^2 + 16*W.a₃*x₀^2*y*y₀ - 4*W.a₃*x₀^2*y₀^2 + 8*W.a₄^2*x*y - 14*W.a₄^2*x*y₀ + 6*W.a₄^2*x₀*y₀ + 8*W.a₄*W.a₆*y - 8*W.a₄*W.a₆*y₀ - 12*W.a₄*x^3*y₀ + 16*W.a₄*x^2*x₀*y - 16*W.a₄*x^2*x₀*y₀ + 16*W.a₄*x*x₀^2*y - 16*W.a₄*x*x₀^2*y₀ + 12*W.a₄*x₀^3*y₀ - 4*W.a₄*y^3 + 8*W.a₄*y^2*y₀ - 4*W.a₄*y₀^3 - 8*W.a₆*x^2*y + 8*W.a₆*x^2*y₀ + 16*W.a₆*x*x₀*y - 16*W.a₆*x*x₀*y₀ + 16*W.a₆*x₀^2*y - 16*W.a₆*x₀^2*y₀ - 8*x^5*y - 6*x^5*y₀ + 16*x^4*x₀*y - 6*x^4*x₀*y₀ + 16*x^3*x₀^2*y - 24*x^3*x₀^2*y₀ - 4*x^2*x₀^3*y₀ + 4*x^2*y^3 - 8*x^2*y^2*y₀ + 4*x^2*y₀^3 + 8*x*x₀^4*y₀ - 8*x*x₀*y^3 + 16*x*x₀*y^2*y₀ - 8*x*x₀*y₀^3 + 8*x₀^5*y₀ - 8*x₀^2*y^3 + 16*x₀^2*y^2*y₀ - 8*x₀^2*y₀^3) * hord

end CommRing


end
end Dubon2026.SourceEllipticVelu
