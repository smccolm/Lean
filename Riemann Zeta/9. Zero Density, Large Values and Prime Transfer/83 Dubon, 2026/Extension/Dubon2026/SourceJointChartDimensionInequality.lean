import Dubon2026.SourceJointChartQuotientMaps
import Dubon2026.SourceJointChartFitting

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

theorem eventual_chart_intersection_dimension
    {k : Type*} [Field k] {W : Type*} [AddCommGroup W] [Module k W]
    (φ : W ≃ₗ[k] W) (P B P' B' : Submodule k W) (hPB : P ≤ B) (hP'B' : P' ≤ B')
    (hP : P.map (φ : W →ₗ[k] W) ≤ P) (hB : B.map (φ : W →ₗ[k] W) ≤ B)
    (hP' : P'.map (φ.symm : W →ₗ[k] W) ≤ P') (hB' : B'.map (φ.symm : W →ₗ[k] W) ≤ B')
    (hfin : ∀ M : ℕ, FiniteDimensional k ↥(B ⊓ B'.map ((φ : W →ₗ[k] W) ^ M)))
    (hgen : ∃ M₁ : ℕ, B ≤ ⨆ j : ℕ,
      (B ⊓ B'.map ((φ : W →ₗ[k] W) ^ M₁)).map ((φ : W →ₗ[k] W) ^ j))
    (hgen' : ∃ M₁ : ℕ, B' ≤ ⨆ j : ℕ,
      (B' ⊓ B.map ((φ.symm : W →ₗ[k] W) ^ M₁)).map ((φ.symm : W →ₗ[k] W) ^ j))
    (htor : ∀ y ∈ B, ∃ c : Polynomial k, c.Monic ∧
      Polynomial.aeval (φ : W →ₗ[k] W) c y ∈ P)
    (htor' : ∀ y ∈ B', ∃ c : Polynomial k, c.Monic ∧
      Polynomial.aeval (φ.symm : W →ₗ[k] W) c y ∈ P') :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      Module.finrank k ↥(P ⊓ P'.map ((φ : W →ₗ[k] W) ^ M)) + Module.finrank k ↥(B ⊓ B') ≤
        Module.finrank k ↥(B ⊓ B'.map ((φ : W →ₗ[k] W) ^ M)) +
          Module.finrank k ↥(P ⊓ P') := by
  classical
  obtain ⟨M₁, hM₁⟩ := hgen
  haveI := hfin M₁
  haveI hBP : FiniteDimensional k (B ⧸ P.comap B.subtype) :=
    finiteDimensional_quot_of_monicTorsion (φ:W→ₗ[k]W) P B hP hB
      (B ⊓ B'.map ((φ:W→ₗ[k]W)^M₁)) inf_le_left hM₁ htor
  obtain ⟨M₁', hM₁'⟩ := hgen'
  haveI hfin' : FiniteDimensional k ↥(B' ⊓ B.map ((φ.symm:W→ₗ[k]W)^M₁')) := by
    have e : B' ⊓ B.map ((φ.symm:W→ₗ[k]W)^M₁') =
        (B ⊓ B'.map ((φ:W→ₗ[k]W)^M₁')).map ((φ.symm:W→ₗ[k]W)^M₁') := by
      ext x; simp only [mem_inf, mem_map]
      constructor
      · rintro ⟨hxB', z, hzB, hzx⟩
        refine ⟨((φ:W→ₗ[k]W)^M₁') x, ⟨?_, x, hxB', rfl⟩, pow_symm_pow φ M₁' x⟩
        rw [← hzx, pow_pow_symm]; exact hzB
      · rintro ⟨y, ⟨hyB, z, hzB', hzy⟩, hyx⟩
        refine ⟨?_, y, hyB, hyx⟩
        rw [← hyx, ← hzy, pow_symm_pow]; exact hzB'
    rw [e]; haveI := hfin M₁'; exact Module.Finite.map _ _
  haveI hB'P' : FiniteDimensional k (B' ⧸ P'.comap B'.subtype) :=
    finiteDimensional_quot_of_monicTorsion (φ.symm:W→ₗ[k]W) P' B' hP' hB'
      (B' ⊓ B.map ((φ.symm:W→ₗ[k]W)^M₁')) inf_le_left hM₁' htor'

  have hrank : ∀ M, Module.finrank k ↥(B ⊓ B'.map ((φ:W→ₗ[k]W)^M)) =
      Module.finrank k (LinearMap.range (Psi φ P B P' B' M)) +
        Module.finrank k ↥(P ⊓ P'.map ((φ:W→ₗ[k]W)^M)) := by
    intro M; haveI := hfin M
    have hle : P ⊓ P'.map ((φ:W→ₗ[k]W)^M) ≤ B ⊓ B'.map ((φ:W→ₗ[k]W)^M) :=
      inf_le_inf hPB (Submodule.map_mono hP'B')
    have hrn := LinearMap.finrank_range_add_finrank_ker (Psi φ P B P' B' M)
    rw [ker_Psi_eq φ P B P' B' M] at hrn
    have heq : Module.finrank k ↥((P ⊓ P'.map ((φ:W→ₗ[k]W)^M)).comap
        (B ⊓ B'.map ((φ:W→ₗ[k]W)^M)).subtype) =
        Module.finrank k ↥(P ⊓ P'.map ((φ:W→ₗ[k]W)^M)) :=
      (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
    omega

  obtain ⟨M₀, hM₀⟩ := fitting_step
    (barEnd (φ:W→ₗ[k]W) P B hP hB) (barEnd (φ.symm:W→ₗ[k]W) P' B' hP' hB')
    (LinearMap.range (Psi φ P B P' B' 0))
  refine ⟨M₀, fun M hM => ?_⟩
  haveI := hfin M; haveI := hfin 0
  have hwin0 : B ⊓ B'.map ((φ:W→ₗ[k]W)^(0:ℕ)) = B ⊓ B' := by
    rw [pow_zero, show (1:W→ₗ[k]W) = LinearMap.id from rfl, Submodule.map_id]
  have hP0 : P ⊓ P'.map ((φ:W→ₗ[k]W)^(0:ℕ)) = P ⊓ P' := by
    rw [pow_zero, show (1:W→ₗ[k]W) = LinearMap.id from rfl, Submodule.map_id]
  have h0' := hrank 0
  have hB0 : Module.finrank k ↥(B ⊓ B') =
      Module.finrank k ↥(B ⊓ B'.map ((φ:W→ₗ[k]W)^(0:ℕ))) := by rw [hwin0]
  have hP0' : Module.finrank k ↥(P ⊓ P') =
      Module.finrank k ↥(P ⊓ P'.map ((φ:W→ₗ[k]W)^(0:ℕ))) := by rw [hP0]
  have hMr := hrank M
  have hI : Module.finrank k ↥(LinearMap.range (Psi φ P B P' B' 0)) ≤
      Module.finrank k ↥(LinearMap.range (Psi φ P B P' B' M)) :=
    (hM₀ M hM).trans (Submodule.finrank_mono (range_Psi_superset φ P B P' B' hP hB hP' hB' M))
  omega

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartLinearAlgebra
