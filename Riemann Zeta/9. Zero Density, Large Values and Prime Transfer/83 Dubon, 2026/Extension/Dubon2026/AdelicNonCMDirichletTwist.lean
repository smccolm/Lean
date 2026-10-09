import Dubon2026.AdelicDirichletSelfTwist

/-! # Original non-CM cusp forms exclude actual primitive quadratic Dirichlet adelic self-twists -/

namespace Dubon2026

noncomputable section

/-- The original classical non-CM condition rules out every injective original adelic self-twist by a nontrivial primitive quadratic Dirichlet determinant character. -/
theorem nonCM_no_adelicDirichletSelfTwist {N : ℕ} [NeZero N] {k : ℤ}
    (F : NonCMPrimitiveCuspForm N k) (D : ℕ+) (χ : DirichletCharacter ℂ D)
    (hχp : χ.IsPrimitive) (hχne : χ ≠ 1) (hχq : χ.IsQuadratic)
    (T : Representation.IntertwiningMap (adelicCyclicHilbertRepresentation F.toCuspForm)
      (scalarTwistRepresentation (adelicCyclicHilbertRepresentation F.toCuspForm)
        (adelicDirichletDeterminant χ))) : ¬ Function.Injective T := by
  intro hT
  exact F.nonCM ⟨D, χ, hχp, hχne, hχq,
    adelicDirichletSelfTwist_classical F.toPrimitiveCuspForm χ T hχq hT⟩

end
end Dubon2026
