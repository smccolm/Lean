import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-! DUB-17/18 -> original Weil reciprocity and Hecke adjointness ->
evaluation on pushed-forward divisors. Integer coefficients can cancel
under a map of places, so nonvanishing on the actual source support is
essential. The finite-product proof below requires it only there. -/
namespace Dubon2026
noncomputable section

theorem finsupp_prod_zpow_mapDomain {A B K : Type*} [CommGroupWithZero K]
    (q : A → B) (D : A →₀ ℤ) (a : B → K)
    (ha : ∀ w ∈ D.support, a (q w) ≠ 0) :
    (D.mapDomain q).prod (fun v n => a v ^ n) = D.prod (fun w n => a (q w) ^ n) := by
  classical
  let b : B → K := fun v => if a v = 0 then 1 else a v
  have hb (v : B) : b v ≠ 0 := by
    dsimp [b]
    split_ifs with h
    · exact one_ne_zero
    · exact h
  have he (v : B) (hv : v ∈ D.support.image q) : b v = a v := by
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact if_neg (ha w hw)
  calc
    _ = (D.mapDomain q).prod (fun v n => b v ^ n) := by
      apply Finsupp.prod_congr
      intro v hv
      rw [he v (Finsupp.mapDomain_support hv)]
    _ = D.prod (fun w n => b (q w) ^ n) :=
      Finsupp.prod_mapDomain_index (fun _ => zpow_zero _) (fun v m n => zpow_add₀ (hb v) m n)
    _ = _ := by
      apply Finsupp.prod_congr
      intro w hw
      rw [he (q w) (Finset.mem_image.mpr ⟨w, hw, rfl⟩)]

end
end Dubon2026
