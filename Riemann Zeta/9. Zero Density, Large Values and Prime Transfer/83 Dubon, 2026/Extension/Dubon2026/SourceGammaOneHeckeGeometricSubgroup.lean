import Dubon2026.SourceGammaOneModularStretch
import Dubon2026.SourceGammaOneHeckeSubgroup
import Dubon2026.SourceOriginalHeckeUpperEquiv

/-! DUB-17/18 -> original all-weight adic association -> actual finite
Gamma1 character realization -> geometric/H1 comparison with the original
homogeneous coefficient action -> exact upper/lower correspondence.
Restrict the already proved original conjugation equivalence to Gamma1.
This identifies the actual upper subgroup with the actual geometric Hecke
subgroup and records its analytic matrix equation. Operator transpose,
diamond and original coefficient-action comparisons remain required. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open CongruenceSubgroup Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups
variable (M d : ℕ) [NeZero d]

/-- The original upper-subgroup conjugation into the actual geometric Hecke subgroup. -/
def upperToGeometric :
    sourceGammaOneHeckeUpper M d →* ↥(Gamma1 M ⊓ Gamma0 (d * M)) :=
  ((Gamma1 M).subtype.comp (sourceGammaOneHeckeConjugation M d)).codRestrict _ (by
    intro g
    refine ⟨(sourceGammaOneHeckeConjugation M d g).property, ?_⟩
    simpa only [Nat.mul_comm] using
      (originalHeckeUpperToRaised M d (sourceGammaOneUpperToGammaZero M d g)).property)

/-- The inverse original level-raising matrix, retaining the Gamma1 congruences. -/
def geometricToUpper (g : ↥(Gamma1 M ⊓ Gamma0 (d * M))) :
    sourceGammaOneHeckeUpper M d := by
  let γ : Gamma0 (M * d) := ⟨g.val, by simpa only [Nat.mul_comm] using g.property.2⟩
  let u := originalHeckeRaisedToUpper M d γ
  refine ⟨⟨u.val.val, ?_⟩, u.property⟩
  exact levelRaiseConj_mem_Gamma1 M d g.val g.property

theorem geometricToUpper_upperToGeometric (g : sourceGammaOneHeckeUpper M d) :
    geometricToUpper M d (upperToGeometric M d g) = g := by
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : heckeUpperSubgroup M d => z.val.val)
    (originalHeckeRaisedToUpper_toRaised M d (sourceGammaOneUpperToGammaZero M d g))

theorem upperToGeometric_geometricToUpper (g : ↥(Gamma1 M ⊓ Gamma0 (d * M))) :
    upperToGeometric M d (geometricToUpper M d g) = g := by
  apply Subtype.ext
  exact congrArg (fun z : Gamma0 (M * d) => z.val)
    (originalHeckeUpperToRaised_toUpper M d
      ⟨g.val, by simpa only [Nat.mul_comm] using g.property.2⟩)

/-- The actual upper/geometric Hecke subgroup isomorphism, at every positive index. -/
def heckeUpperGeometricEquiv :
    sourceGammaOneHeckeUpper M d ≃* ↥(Gamma1 M ⊓ Gamma0 (d * M)) where
  toFun := upperToGeometric M d
  invFun := geometricToUpper M d
  left_inv := geometricToUpper_upperToGeometric M d
  right_inv := upperToGeometric_geometricToUpper M d
  map_mul' := (upperToGeometric M d).map_mul

theorem upperToGeometric_conjugation (g : sourceGammaOneHeckeUpper M d) :
    (upperToGeometric M d g).val = (sourceGammaOneHeckeConjugation M d g).val := rfl

theorem upperToGeometric_matrix (g : sourceGammaOneHeckeUpper M d) :
    levelRaiseMatrix d * mapGL ℝ (upperToGeometric M d g).val =
      mapGL ℝ g.val.val * levelRaiseMatrix d :=
  originalHeckeUpperToRaised_matrix M d (sourceGammaOneUpperToGammaZero M d g)

theorem upperToGeometric_smul (g : sourceGammaOneHeckeUpper M d) (z : ℍ) :
    levelRaiseMatrix d • ((upperToGeometric M d g).val • z) =
      g.val.val • (levelRaiseMatrix d • z) :=
  originalHeckeUpperToRaised_smul M d (sourceGammaOneUpperToGammaZero M d g) z

end
end Dubon2026.SourceFunctionField.GammaOne
