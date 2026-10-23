import Dubon2026.SourceEllipticVeluTwoKernelTranslation
import Dubon2026.SourceEllipticVeluTwoTangentYCleared

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
section CommRing

variable {R : Type*} [CommRing R] {W : WeierstrassCurve R} {x₀ y₀ x₁ y₁ x₂ y₂ : R}

theorem velu2_secX_SI2 (hP₁ : W.toAffine.Equation x₁ y₁)
    (hP₂ : W.toAffine.Equation x₂ y₂) (hQ : W.toAffine.Equation x₀ y₀)
    (hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0) :
    (x₁ - x₀) * (x₂ - x₀) * (x₁ - x₂) * ((x₁ - x₀) * (x₂ - x₀) - veluGx W x₀ y₀)
      = ((x₂ - x₀) * (W.a₁ * (x₁ - x₀) + y₁ - y₀)
            + (x₁ - x₀) * (W.a₁ * (x₂ - x₀) + y₂ - y₀) - W.a₁ * ((x₁ - x₀) * (x₂ - x₀)))
        * ((x₂ - x₀) * (y₁ - y₀) - (x₁ - x₀) * (y₂ - y₀)) := by
  rw [WeierstrassCurve.Affine.equation_iff] at hP₁ hP₂ hQ
  simp only [veluGx]
  linear_combination (-(x₂ - x₀) ^ 2) * hP₁ + (x₁ - x₀) ^ 2 * hP₂
    + (-(x₁ - x₂) * ((x₁ - x₀) + (x₂ - x₀))) * hQ
    + ((x₂ - x₀) ^ 2 * y₁ - (x₁ - x₀) ^ 2 * y₂
        + (x₁ - x₂) * ((x₁ - x₀) + (x₂ - x₀)) * y₀) * hord

theorem velu2_secX_SI3 (hP₁ : W.toAffine.Equation x₁ y₁)
    (hP₂ : W.toAffine.Equation x₂ y₂) (hQ : W.toAffine.Equation x₀ y₀)
    (hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0) :
    ((y₁ - y₂) ^ 2 + W.a₁ * (y₁ - y₂) * (x₁ - x₂) - (W.a₂ + x₀ + x₁ + x₂) * (x₁ - x₂) ^ 2)
        * ((x₂ - x₀) * (W.a₁ * (x₁ - x₀) + y₁ - y₀)
            + (x₁ - x₀) * (W.a₁ * (x₂ - x₀) + y₂ - y₀) - W.a₁ * ((x₁ - x₀) * (x₂ - x₀)))
      = (x₁ - x₂) * ((x₁ - x₀) * (x₂ - x₀) - veluGx W x₀ y₀)
        * ((x₂ - x₀) * (y₁ - y₀) - (x₁ - x₀) * (y₂ - y₀)) := by
  rw [WeierstrassCurve.Affine.equation_iff] at hP₁ hP₂ hQ
  simp only [veluGx]
  linear_combination
    (-W.a₁*x₀*x₁ + W.a₁*x₀*x₂ + W.a₁*x₁*x₂ - W.a₁*x₂^2 - x₀*y₁ + x₀*y₂ - x₁*y₀ + x₁*y₂ + x₂*y₀
     + x₂*y₁ - 2*x₂*y₂) * hP₁
    + (W.a₁*x₀*x₁ - W.a₁*x₀*x₂ - W.a₁*x₁^2 + W.a₁*x₁*x₂ + x₀*y₁ - x₀*y₂ + x₁*y₀ - 2*x₁*y₁
     + x₁*y₂ - x₂*y₀ + x₂*y₁) * hP₂
    + ((x₁ - x₂) * (W.a₁ * (x₁ - x₂) + 2 * (y₁ - y₂))) * hQ
    + (-(W.a₁ * (x₁ - x₂) + (y₁ - y₂))
        * ((x₂ - x₀) * (y₁ - y₀) - (x₁ - x₀) * (y₂ - y₀))) * hord

end CommRing


end
end Dubon2026.SourceEllipticVelu
