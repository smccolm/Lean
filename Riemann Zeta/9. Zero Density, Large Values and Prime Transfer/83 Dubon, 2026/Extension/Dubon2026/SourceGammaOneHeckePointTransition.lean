import Dubon2026.SourceGammaOneHeckePrimitiveTrace
import Dubon2026.SourceGammaOneConstantHecke

/-! DUB17/18 -> original all-weight arithmetic association -> actual
Gamma1 Picard/H1 Hecke comparison -> actual scalar period trace.
The native coset transition and integral conjugation give the precise
change of the inverse-dilation point under the Gamma1 action. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups
variable (M d : ℕ) [NeZero d]

theorem heckeCosetPoint_transition (g : Gamma1 M) (τ : ℍ)
    (q : Gamma1 M ⧸ sourceGammaOneHeckeUpper M d) :
    heckeCosetPoint M d (g.val • τ) (g • q) =
      (sourceGammaOneHeckeConjugation M d
        (cosetTransition (sourceGammaOneHeckeUpper M d) g q)).val •
          heckeCosetPoint M d τ q := by
  let t := cosetTransition (sourceGammaOneHeckeUpper M d) g q
  have ht : (g • q).out.val⁻¹ * g.val = t.val.val * q.out.val⁻¹ := by
    change (g • q).out.val⁻¹ * g.val =
      ((g • q).out.val⁻¹ * (g.val * q.out.val)) * q.out.val⁻¹
    group
  have hp : (g • q).out.val⁻¹ • (g.val • τ) =
      t.val.val • (q.out.val⁻¹ • τ) := by
    rw [← mul_smul, ht, mul_smul]
  rw [heckeCosetPoint_eq_triangular, heckeCosetPoint_eq_triangular, mul_smul, mul_smul]
  change heckeTriangularMatrix 1 d 0 • ((g • q).out.val⁻¹ • (g.val • τ)) =
    (sourceGammaOneHeckeConjugation M d t).val •
      (heckeTriangularMatrix 1 d 0 • (q.out.val⁻¹ • τ))
  rw [hp]
  have hs := congrArg (fun A : GL (Fin 2) ℝ => A • (q.out.val⁻¹ • τ))
    (sourceGammaOneHeckeConjugation_matrix M d t)
  simpa only [mul_smul] using hs

end
end Dubon2026.SourceFunctionField.GammaOne
