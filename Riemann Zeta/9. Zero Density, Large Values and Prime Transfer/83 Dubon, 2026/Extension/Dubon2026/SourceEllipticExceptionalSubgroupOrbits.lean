import Dubon2026.SourceEllipticExceptionalStabilizers
import Dubon2026.SourceEllipticScalingComposition

/-! Every actual stabilizer of an exceptional short model acts on its
subgroups as the identity or one of the two required cyclic powers.
The full coordinate-change relation is therefore controlled by the
quartic/cubic automorphisms whose fixed counts have already been proved. -/
namespace Dubon2026.SourceEllipticExceptional
open WeierstrassCurve SourceEllipticStabilizer
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K]

theorem quartic_stabilizer_subgroup_orbit (A : K) (hA : A ≠ 0)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (u : Kˣ) (hu : (u : K) ^ 2 = -1)
    (C : VariableChange K) (hC : C • EA A = EA A) (H : AddSubgroup (EA A).toAffine.Point) :
    H.map (stabilizerPointEquiv (EA A) C hC).toAddMonoidHom = H ∨
      H.map (stabilizerPointEquiv (EA A) C hC).toAddMonoidHom =
        H.map (stabilizerPointEquiv (EA A) ⟨u, 0, 0, 0⟩ (quartic_change_fixes u hu A)).toAddMonoidHom := by
  obtain ⟨he, hv⟩ := quartic_stabilizer_scaling A hA h2 h3 C hC
  have hC' : (⟨C.u, 0, 0, 0⟩ : VariableChange K) • EA A = EA A := by
    rw [← he]
    exact hC
  rw [stabilizerPointEquiv_congr (EA A) he hC hC']
  rcases fourth_roots_mod_sign hu hv with hs | hs
  · left
    have h1 : (⟨1, 0, 0, 0⟩ : VariableChange K) • EA A = EA A := one_smul _ _
    have hm := pure_scaling_subgroup_map_eq_of_sign (EA A) rfl rfl C.u 1 hC' h1 hs H
    have hid : (stabilizerPointEquiv (EA A) ⟨1, 0, 0, 0⟩ h1).toAddMonoidHom =
        AddMonoidHom.id _ := AddMonoidHom.ext (pure_scaling_one_point (EA A) h1)
    simpa only [hid, AddSubgroup.map_id] using hm
  · right
    exact pure_scaling_subgroup_map_eq_of_sign (EA A) rfl rfl C.u u hC'
      (quartic_change_fixes u hu A) hs H

theorem cubic_stabilizer_subgroup_orbit (B : K) (hB : B ≠ 0)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (u : Kˣ) (hu : (u : K) ^ 3 = 1) (hu1 : (u : K) ≠ 1)
    (C : VariableChange K) (hC : C • EB B = EB B) (H : AddSubgroup (EB B).toAffine.Point) :
    let σ := (stabilizerPointEquiv (EB B) ⟨u, 0, 0, 0⟩ (cubic_change_fixes u hu B)).toAddMonoidHom
    H.map (stabilizerPointEquiv (EB B) C hC).toAddMonoidHom = H ∨
      H.map (stabilizerPointEquiv (EB B) C hC).toAddMonoidHom = H.map σ ∨
      H.map (stabilizerPointEquiv (EB B) C hC).toAddMonoidHom = (H.map σ).map σ := by
  dsimp only
  obtain ⟨he, hv⟩ := cubic_stabilizer_scaling B hB h2 h3 C hC
  have hC' : (⟨C.u, 0, 0, 0⟩ : VariableChange K) • EB B = EB B := by
    rw [← he]
    exact hC
  rw [stabilizerPointEquiv_congr (EB B) he hC hC']
  rcases sixth_roots_mod_sign hu hu1 hv with hs | hs | hs
  · left
    have h1 : (⟨1, 0, 0, 0⟩ : VariableChange K) • EB B = EB B := one_smul _ _
    have hm := pure_scaling_subgroup_map_eq_of_sign (EB B) rfl rfl C.u 1 hC' h1 hs H
    have hid : (stabilizerPointEquiv (EB B) ⟨1, 0, 0, 0⟩ h1).toAddMonoidHom =
        AddMonoidHom.id _ := AddMonoidHom.ext (pure_scaling_one_point (EB B) h1)
    simpa only [hid, AddSubgroup.map_id] using hm
  · right; left
    exact pure_scaling_subgroup_map_eq_of_sign (EB B) rfl rfl C.u u hC'
      (cubic_change_fixes u hu B) hs H
  · right; right
    have hu2 : ((u ^ 2 : Kˣ) : K) ^ 3 = 1 := by
      rw [Units.val_pow_eq_pow_val, ← pow_mul, Nat.mul_comm 2 3, pow_mul, hu, one_pow]
    have hm := pure_scaling_subgroup_map_eq_of_sign (EB B) rfl rfl C.u (u ^ 2) hC'
      (cubic_change_fixes (u ^ 2) hu2 B) hs H
    exact hm.trans (pure_scaling_subgroup_square (EB B) u (cubic_change_fixes u hu B)
      (cubic_change_fixes (u ^ 2) hu2 B) H)

end
end Dubon2026.SourceEllipticExceptional
