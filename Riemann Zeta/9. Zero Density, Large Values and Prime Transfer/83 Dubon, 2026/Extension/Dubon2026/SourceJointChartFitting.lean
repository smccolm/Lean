import Mathlib

/-! DUB-17/18 -> Picard torsion injectivity -> Kummer power lifting ->
sum-of-genera inequality -> dimensions of simultaneous residue chart spaces.
This finite-window linear algebra supplies the eventual comparison needed
for pole spaces on the coordinate and inverse-coordinate charts. Chart
generation, monic torsion and constant intersection remain separate inputs
to discharge in the actual curve argument. Adapted from Apache-2.0 FLT,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2. Native eventual Fitting
disjointness replaces the external auxiliary stabilization proof. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartLinearAlgebra
noncomputable section
open Submodule LinearMap Module
variable {k : Type*} [Field k] {W : Type*} [AddCommGroup W] [Module k W]

theorem fitting_step
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
    [AddCommGroup V₂] [Module k V₂] [FiniteDimensional k V₂]
    (f : V₁ →ₗ[k] V₁) (g : V₂ →ₗ[k] V₂) (S : Submodule k (V₁ × V₂)) :
    ∃ M₀, ∀ M ≥ M₀,
      Module.finrank k S ≤
        Module.finrank k ↥(S.map (LinearMap.prodMap (f ^ M) LinearMap.id) ⊔
          S.map (LinearMap.prodMap LinearMap.id (g ^ M))) := by
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (Module.End.eventually_disjoint_ker_pow_range_pow g)
  refine ⟨N₀, fun M hM => ?_⟩
  set ψ : (V₁ × V₂) →ₗ[k] (V₁ × V₂) := LinearMap.prodMap LinearMap.id (g ^ M) with hψ
  set T := S.map ψ with hT
  set J : Submodule k (V₁ × V₂) := S ⊓ LinearMap.ker ψ with hJ
  have hkerψ : LinearMap.ker ψ = (⊥ : Submodule k V₁).prod (LinearMap.ker (g^M)) := by
    rw [hψ, LinearMap.ker_prodMap, LinearMap.ker_id]

  have hrn := LinearMap.finrank_range_add_finrank_ker (ψ.comp S.subtype)
  rw [LinearMap.range_comp, Submodule.range_subtype, LinearMap.ker_comp] at hrn
  have hkereq : (LinearMap.ker ψ).comap S.subtype = J.comap S.subtype := by
    rw [hJ, Submodule.comap_inf, Submodule.comap_subtype_self, top_inf_eq]
  have hJdim : Module.finrank k ↥((LinearMap.ker ψ).comap S.subtype) =
      Module.finrank k ↥J := by
    rw [hkereq]
    exact (Submodule.comapSubtypeEquivOfLe (hJ ▸ inf_le_left)).finrank_eq
  have hSdim : Module.finrank k ↥S = Module.finrank k ↥T + Module.finrank k ↥J := by
    rw [← hT] at hrn; omega

  have hJT : Disjoint J T := by
    rw [Submodule.disjoint_def]
    rintro ⟨a, b⟩ hJmem hTmem
    obtain ⟨hS, hK⟩ := Submodule.mem_inf.mp hJmem
    rw [hkerψ] at hK
    obtain ⟨ha, hb⟩ := Submodule.mem_prod.mp hK
    obtain ⟨c, hcS, hc⟩ := Submodule.mem_map.mp hTmem
    have hcb : (g^M) c.2 = b := by
      have h := congrArg Prod.snd hc
      simpa [hψ, LinearMap.prodMap_apply] using h
    have hb0 : b = 0 :=
      Submodule.disjoint_def.mp (hN₀ M hM) b hb ⟨c.2, hcb⟩
    have ha0 : a = 0 := (Submodule.mem_bot k).mp ha
    exact Prod.ext ha0 hb0

  have hJle : J ≤ S.map (LinearMap.prodMap (f^M) LinearMap.id) := by
    rintro ⟨a, b⟩ hJmem
    obtain ⟨hS, hK⟩ := Submodule.mem_inf.mp hJmem
    rw [hkerψ] at hK
    obtain ⟨ha, _⟩ := Submodule.mem_prod.mp hK
    have ha0 : a = 0 := (Submodule.mem_bot k).mp ha
    refine ⟨(a, b), hS, ?_⟩
    simp only [LinearMap.prodMap_apply, LinearMap.id_apply, ha0, map_zero]

  have hGrass := Submodule.finrank_sup_add_finrank_inf_eq J T
  rw [hJT.eq_bot, finrank_bot] at hGrass
  have hJTdim : Module.finrank k ↥(J ⊔ T) = Module.finrank k ↥S := by omega
  have hbig : J ⊔ T ≤ S.map (LinearMap.prodMap (f^M) LinearMap.id) ⊔
      S.map (LinearMap.prodMap LinearMap.id (g^M)) :=
    sup_le_sup hJle (le_of_eq hT)
  calc Module.finrank k ↥S = Module.finrank k ↥(J ⊔ T) := hJTdim.symm
    _ ≤ _ := Submodule.finrank_mono hbig


end
end Dubon2026.SourceCurve.RegularProlongation.JointChartLinearAlgebra
