from pathlib import Path

root = Path("Riemann Zeta")
here = Path(__file__).resolve().parent
src, = root.glob("7. Weil*/84 Alpoge*/.lake/lean/src/Development/AutomorphicArithmetic/AutomorphicVarieties")
defs = (src/"AutomorphicForms/Newform.lean").read_text(encoding="utf-8")
eigen = (src/"IdeleGenerators/ConstSmall.lean").read_text(encoding="utf-8")
defs = defs[defs.index("def coef "):defs.index("structure Newform ")]
eigen = eigen[eigen.index("structure Eigenform "):eigen.index("def LkDist ")]
probe = """import Dubon2026.AlpogeEigenformInput
open CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm
noncomputable section
namespace UpperTheory.V.Af
""" + defs + """end UpperTheory.V.Af
namespace UpperTheory.V.Sd
open UpperTheory.V.Af
""" + eigen + """end UpperTheory.V.Sd
open Dubon2026 UpperTheory.V

theorem original_eigenform_constructor {Q k : ℕ} [NeZero Q] (hk : 2 ≤ k)
    (f : PrimitiveCuspForm Q (k : ℤ)) :
    ∃ g : Sd.Eigenform k Q 1, (g.f : ℍ → ℂ) = f.toCuspForm ∧
      ∀ n, g.a n = cuspCoefficients f.toCuspForm n := by
  obtain ⟨g, he, hc, h1, hp⟩ := primitive_alpoge_eigenform_input (by omega) f
  refine ⟨⟨g, hc, h1, hp⟩, he, ?_⟩
  intro n
  change (qExpansion 1 (g : ℍ → ℂ)).coeff n = _
  rw [he]
  rfl

#print axioms original_eigenform_constructor
end
"""
(here/"UpstreamConstructor.lean").write_text(probe,encoding="utf-8")
