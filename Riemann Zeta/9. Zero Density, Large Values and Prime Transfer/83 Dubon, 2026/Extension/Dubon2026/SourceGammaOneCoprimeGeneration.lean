import Dubon2026.SourceGammaOnePrimeHeckeIndex

/-! DUB-17/18 -> original Gamma1 Frobenius norm -> explicit embedding
census -> generation by the adjacent j-coordinate. To exclude j_p
from the lower field, its hypothetical Gamma1 invariance combines with
its genuine Gamma0(p) invariance. Existing coprime reduction proves that
these two actual subgroups generate the full modular group. The analytic
invariance and Laurent nonmembership consumers remain to be supplied.
-/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

theorem gammaOne_sup_gamma0_coprime (M n : ℕ) [NeZero M] [NeZero n]
    (h : Nat.Coprime M n) : Gamma1 M ⊔ Gamma0 n = ⊤ := by
  apply top_unique
  intro g _
  let red := Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod n))
  obtain ⟨a, ha⟩ := gammaOneReduction_surjective M n h (red g)
  have he : red (a.val⁻¹ * g) = 1 := by
    rw [map_mul, map_inv]
    change red a.val = red g at ha
    rw [ha, inv_mul_cancel]
  have hg : a.val⁻¹ * g ∈ Gamma0 n := by
    rw [Gamma0_mem]
    have hc := congrArg (fun z : SL(2, ZMod n) => z 1 0) he
    exact hc
  have hm := (Gamma1 M ⊔ Gamma0 n).mul_mem
    (Subgroup.mem_sup_left a.property) (Subgroup.mem_sup_right hg)
  simpa only [mul_inv_cancel_left] using hm

end
end Dubon2026.SourceFunctionField.GammaOne
