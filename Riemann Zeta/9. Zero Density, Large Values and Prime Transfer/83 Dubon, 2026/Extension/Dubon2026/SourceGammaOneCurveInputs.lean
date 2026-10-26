import Dubon2026.SourceGammaOneCurveGeometry
import Dubon2026.SourceGammaOneCurveFinite

/-! DUB-17/18 -> original all-weight adic association -> actual Gamma1
arithmetic realization -> Picard/H1 comparison -> actual curve and
differential inputs. Native congruence facts discharge the finite-index and
translation requirements for both Gamma1 and its actual Hecke subgroup.
The original j, Laurent field, places and differential expansion are kept. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open CongruenceSubgroup SourceCurve SourceDifferential KaehlerDifferential
open scoped MatrixGroups
variable (M : ℕ) [NeZero M] (L : Type*) [Field L] [Algebra ℚ L]

omit [NeZero M] in
private theorem translation_gamma1 : ModularGroup.T ∈ Gamma1 M := by
  simp [Gamma1_mem, ModularGroup.T]

theorem gamma1_diffQExp_injective :
    Function.Injective (diffQExp (functionFieldOver (Gamma1 M) L)) :=
  functionFieldOver_diffQExp_injective (Gamma1 M) L (translation_gamma1 M)

theorem gamma1_localDifferentials (P : Place L (functionFieldOver (Gamma1 M) L)) :
    P.DCoordGenerates ∧ Module.Finite P.toValuationSubring Ω[P.toValuationSubring⁄L] :=
  ⟨functionFieldOver_dCoordGenerates (Gamma1 M) L (translation_gamma1 M) P,
    functionFieldOver_localDifferentials (Gamma1 M) L (translation_gamma1 M) P⟩

theorem gamma1_isCurveOver [IsAlgClosed L] :
    IsCurveOver L (functionFieldOver (Gamma1 M) L) :=
  functionFieldOver_isCurveOver (Gamma1 M) L (translation_gamma1 M)

theorem gamma1_hasCanonicalDivisor [IsAlgClosed L] :
    HasCanonicalDivisor (K := L) (F := functionFieldOver (Gamma1 M) L) :=
  functionFieldOver_hasCanonicalDivisor (Gamma1 M) L (translation_gamma1 M)

variable (d : ℕ) [NeZero d]

omit [NeZero M] [NeZero d] in
private theorem translation_hecke :
    ModularGroup.T ∈ Gamma1 M ⊓ Gamma0 (d * M) := by
  constructor <;> simp [Gamma1_mem, Gamma0_mem, ModularGroup.T]

theorem gamma1_hecke_diffQExp_injective :
    Function.Injective (diffQExp (functionFieldOver (Gamma1 M ⊓ Gamma0 (d * M)) L)) :=
  functionFieldOver_diffQExp_injective (Gamma1 M ⊓ Gamma0 (d * M)) L (translation_hecke M d)

theorem gamma1_hecke_localDifferentials
    (P : Place L (functionFieldOver (Gamma1 M ⊓ Gamma0 (d * M)) L)) :
    P.DCoordGenerates ∧ Module.Finite P.toValuationSubring Ω[P.toValuationSubring⁄L] :=
  ⟨functionFieldOver_dCoordGenerates (Gamma1 M ⊓ Gamma0 (d * M)) L (translation_hecke M d) P,
    functionFieldOver_localDifferentials (Gamma1 M ⊓ Gamma0 (d * M)) L (translation_hecke M d) P⟩

theorem gamma1_hecke_isCurveOver [IsAlgClosed L] :
    IsCurveOver L (functionFieldOver (Gamma1 M ⊓ Gamma0 (d * M)) L) :=
  functionFieldOver_isCurveOver (Gamma1 M ⊓ Gamma0 (d * M)) L (translation_hecke M d)

theorem gamma1_hecke_hasCanonicalDivisor [IsAlgClosed L] :
    HasCanonicalDivisor (K := L) (F := functionFieldOver (Gamma1 M ⊓ Gamma0 (d * M)) L) :=
  functionFieldOver_hasCanonicalDivisor (Gamma1 M ⊓ Gamma0 (d * M)) L (translation_hecke M d)

end
end Dubon2026.SourceFunctionField.GammaOne
