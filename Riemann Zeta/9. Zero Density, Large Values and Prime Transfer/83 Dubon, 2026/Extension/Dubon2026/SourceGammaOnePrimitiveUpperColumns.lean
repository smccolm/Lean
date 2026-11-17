import Dubon2026.SourceGammaOnePrimitiveCuspConjugation
import Dubon2026.SourceCuspBoundaryValues

/-! DUB-17/18 -> original all-weight association -> exact joint arithmetic
realization -> primitive two-term boundary formula on finite columns.
Reuse the native Borel lift at diagonal one: it lies in the actual
Gamma1 group. Thus its upper-column change preserves primitive cusp
values, including torsion values. This removes the coset representative
from the two explicitly computed Hecke contributions. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open CongruenceSubgroup SourceCuspBoundary
open scoped MatrixGroups

/-- An upper-unipotent change of reduced columns preserves the actual
primitive Gamma1 cusp value. -/
theorem primitiveCuspValue_eq_of_upper_columns (M : ℕ) [NeZero M]
    {A : Type*} [AddCommGroup A] (φ : Additive (Gamma1 M) →+ A)
    (δ σ : SL(2, ℤ)) (t : ZMod M)
    (h0 : (colRed M σ).1 = (colRed M δ).1 + t * (colRed M δ).2)
    (h1 : (colRed M σ).2 = (colRed M δ).2) :
    primitiveCuspValue M φ σ = primitiveCuspValue M φ δ := by
  obtain ⟨γ, hγ0, hγ1, hγ2⟩ := exists_borel (1 : (ZMod M)ˣ) t
  have hg0 : ((γ.val 0 0 : ℤ) : ZMod M) = 1 := by simpa only [inv_one, Units.val_one] using hγ0
  have hg2 : ((γ.val 1 1 : ℤ) : ZMod M) = 1 := by simpa only [Units.val_one] using hγ2
  let r : Gamma1 M := ⟨γ.val, (Gamma1_mem M γ.val).mpr
    ⟨hg0, hg2, Gamma0_mem.mp γ.property⟩⟩
  have hc : colRed M σ = colRed M (γ.val * δ) := by
    rw [colRed_mul_of_mem_Gamma0 γ.property, hg0, hγ1, hg2, one_mul, one_mul]
    exact Prod.ext h0 h1
  have hv := primitiveCuspValue_congr M φ σ (γ.val * δ)
    (congrArg Prod.fst hc) (congrArg Prod.snd hc)
  apply hv.trans
  have he := primitiveCuspValue_conjugate M φ δ r⁻¹
  simpa only [Subgroup.coe_inv, inv_inv] using he

end
end Dubon2026.SourceFunctionField.GammaOne
