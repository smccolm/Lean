import Dubon2026.SourceEllipticPrimeAbscissaQuotient
import Dubon2026.SourceEllipticOddPointSurjective
import Dubon2026.SourceEllipticVeluTwoHom

/-! Attach the existing actual point homomorphisms to the intrinsic prime
quotient curve. Their exact kernel and surjectivity are inherited through
proved equality of literal models. These supply the subgroup image and order
reduction in composite cyclic quotients, required for the DUB-17/18 census. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve SourceFunctionField.IntegralJCoordinate SourceEllipticFunctionField
noncomputable section
variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
variable (W : WeierstrassCurve F) [W.IsElliptic]

/-- The actual intrinsic prime quotient admits a surjective point homomorphism with precisely the given kernel. -/
theorem exists_primeAbscissaHom (p : ℕ) [Fact p.Prime] (hp : (p : F) ≠ 0)
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p}) :
    ∃ φ : W.toAffine.Point →+ (primeAbscissaQuotient W p H).toAffine.Point,
      φ.ker = H.1 ∧ Function.Surjective φ := by
  by_cases hp2 : p = 2
  · subst p
    let P := primeKernelGenerator W 2 H
    have hP : addOrderOf P = 2 := primeKernelGenerator_order W 2 H
    have hP0 : P ≠ 0 := by
      intro hz
      rw [hz, addOrderOf_zero] at hP
      omega
    have he := (two_torsion_coordinates W hP).1
    have hg := (two_torsion_coordinates W hP).2
    rw [primeAbscissaQuotient_two_eq W hp H hP (primeKernelGenerator_zmultiples W 2 H)]
    refine ⟨veluTwoHom he hg, ?_, ?_⟩
    · rw [veluTwoHom_ker]
      have hr : Affine.Point.some (coordsOrZero P).1 (coordsOrZero P).2
          (W.toAffine.equation_iff_nonsingular.mp he) = P := some_coordsOrZero hP0
      rw [hr]
      exact primeKernelGenerator_zmultiples W 2 H
    · rw [show Function.Surjective (veluTwoHom he hg) ↔
          Function.Surjective (veluPointMap2 he hg
            (veluQuotient2_Delta_ne_zero W.isUnit_Δ.ne_zero he hg)) by
        rw [veluTwoHom_coe]]
      exact veluPointMap2_surjective he hg _
  · have hP := primeKernelGenerator_oddOrder W p hp2 H
    rw [primeAbscissaQuotient_odd_eq W p hp2 H hP (primeKernelGenerator_zmultiples W p H)]
    refine ⟨oddPointNorm W hP, ?_, oddPointNorm_surjective W hP⟩
    exact (ker_oddPointNorm W hP).trans (primeKernelGenerator_zmultiples W p H)

end
end Dubon2026.SourceEllipticVelu
