import Dubon2026.SourceOriginalWeilCoverMeromorphicPathAtlas
import Dubon2026.SourceOriginalRegularLoopJumpClosure
import Dubon2026.SourceOriginalWeilCoverRegularPathPrimitives

/-! DUB-17/18 -> cover Abel converse -> meromorphic loop generation.
Endpoint cancellation and the existing integer-span API give common integer
coefficients for every finite family of actual simple-pole differentials. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Filter KaehlerDifferential CellGeometry
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders
local notation "PC" => placeChart N n radicand baseDivisor hRadicand hOrders
local notation "PF" => placeFamily N n radicand baseDivisor hRadicand hOrders
local notation "RD" => readDifferential N n radicand baseDivisor hRadicand hOrders
local notation "CF" => coverCoeffIn N n radicand baseDivisor hRadicand hOrders



open RadialMeromorphicPeriods RadialDissectionPeriods


theorem cover_loop_period_mem_ΛJ {R : Type*} [Finite R] :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)),
      (∀ C P, P ∈ (D.cell C).ζ.source →
        AnalyticAt ℂ ((D.cell C).ζ ∘ PF P) 0 ∧ deriv ((D.cell C).ζ ∘ PF P) 0 ≠ 0) →
      ∀ (S : Finset (Place ℂ EE)) (θ : R → Ω[EE⁄ℂ]),
      (∀ r v, -1 ≤ v.ordDifferential (θ r) ∧ (v ∉ S → 0 ≤ v.ordDifferential (θ r))) →
      PolePos D S → ∀ {V : D.ιC → Set ℂ} {Ψ : R → D.ιC → ℂ → ℂ},
      RegPrimData D S (coverRegCoeff N n radicand baseDivisor hRadicand hOrders D S θ) V Ψ →
      ∀ {J : D.ιE → R → ℂ}, IsJumpH D
        (coverMeromorphicBoundaryValue N n radicand baseDivisor hRadicand hOrders D S θ Ψ) J →
      ∀ {P : Place ℂ EE} (δ : Path P P), (∀ t, δ t ∉ S) →
      (fun r => pathIntegral N n radicand baseDivisor hRadicand hOrders (θ r) δ) ∈
        ΛJ D S (fun v r => v.rationalEval
          (originalWeilKummerCover_residue_bijective N ℂ n radicand v)
            (v.uniformizer * v.differentialCoeff (θ r))) J := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D hD S θ hθ hS V Ψ hP J hJ P δ hδ
  choose g hg using fun r => exists_isPrimitiveAlong_of_coeff_mem N n radicand baseDivisor hRadicand hOrders
    (θ r) δ (fun t => (δ t).mem_of_ord_nonneg ((hθ r (δ t)).2 (hδ t)))
  have hm := cover_meromorphic_path_sub_mem N n radicand baseDivisor hRadicand hOrders
    D hD S θ hθ hS hP hJ δ hδ g hg
  simp only [sub_self, sub_zero] at hm
  have he : (fun r => pathIntegral N n radicand baseDivisor hRadicand hOrders (θ r) δ) =
      fun r => g r 1 - g r 0 := by
    funext r
    exact pathIntegral_eq_of_isPrimitiveAlong N n radicand baseDivisor hRadicand hOrders (hg r)
  rw [he]
  exact hm

/-- Common integer cycle and cell-residue coefficients for a finite family of actual differentials. -/
def CoverMeromorphicFamilyGeneration {R : Type*} :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    (D : RadialCellDissection (Place ℂ EE)) → Finset (Place ℂ EE) →
      (R → Ω[EE⁄ℂ]) → Finset D.ιE → Finset D.ιE →
      ((j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1)) → Prop := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  exact fun D S θ T Ts γ =>
    ∀ (P : Place ℂ EE) (δ : Path P P), (∀ t, δ t ∉ S) →
      ∃ (a : D.ιE → ℤ) (m : D.ιC → ℤ), ∀ r,
        pathIntegral N n radicand baseDivisor hRadicand hOrders (θ r) δ =
          ∑ l ∈ (T ∪ Ts)ᶜ, (a l : ℂ) * pathIntegral N n radicand baseDivisor hRadicand hOrders (θ r) (γ l) +
          ∑ C, (m C : ℂ) * (2 * Real.pi * Complex.I * ρ D S (fun v r => v.rationalEval
            (originalWeilKummerCover_residue_bijective N ℂ n radicand v)
              (v.uniformizer * v.differentialCoeff (θ r))) C r)

theorem cover_meromorphic_family_generation_of_jumps {R : Type*} [Finite R] :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)),
      (∀ C P, P ∈ (D.cell C).ζ.source →
        AnalyticAt ℂ ((D.cell C).ζ ∘ PF P) 0 ∧ deriv ((D.cell C).ζ ∘ PF P) 0 ≠ 0) →
      ∀ (S : Finset (Place ℂ EE)) (θ : R → Ω[EE⁄ℂ]),
      (∀ r v, -1 ≤ v.ordDifferential (θ r) ∧ (v ∉ S → 0 ≤ v.ordDifferential (θ r))) →
      PolePos D S → ∀ {V : D.ιC → Set ℂ} {Ψ : R → D.ιC → ℂ → ℂ},
      RegPrimData D S (coverRegCoeff N n radicand baseDivisor hRadicand hOrders D S θ) V Ψ →
      ∀ {J : D.ιE → R → ℂ}, IsJumpH D
        (coverMeromorphicBoundaryValue N n radicand baseDivisor hRadicand hOrders D S θ Ψ) J →
      ∀ (T Ts : Finset D.ιE)
        (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1)),
      (∀ e, J e ∈ AddSubgroup.closure
        ((fun l r => pathIntegral N n radicand baseDivisor hRadicand hOrders (θ r) (γ l)) ''
          ((T ∪ Ts)ᶜ : Finset D.ιE)) ⊔ Λres D S (fun v r => v.rationalEval
            (originalWeilKummerCover_residue_bijective N ℂ n radicand v)
              (v.uniformizer * v.differentialCoeff (θ r)))) →
      CoverMeromorphicFamilyGeneration N n radicand baseDivisor hRadicand hOrders D S θ T Ts γ := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  classical
  intro D hD S θ hθ hS V Ψ hP J hJ T Ts γ hcl
  unfold CoverMeromorphicFamilyGeneration
  intro P δ hδ
  let residue : Place ℂ EE → R → ℂ := fun v r => v.rationalEval
    (originalWeilKummerCover_residue_bijective N ℂ n radicand v)
      (v.uniformizer * v.differentialCoeff (θ r))
  have hle : ΛJ D S residue J ≤ AddSubgroup.closure
      ((fun l r => pathIntegral N n radicand baseDivisor hRadicand hOrders (θ r) (γ l)) ''
        ((T ∪ Ts)ᶜ : Finset D.ιE)) ⊔ Λres D S residue := by
    refine sup_le ?_ le_sup_right
    rw [AddSubgroup.closure_le]
    rintro _ ⟨e, rfl⟩
    exact hcl e
  have hm := hle (cover_loop_period_mem_ΛJ N n radicand baseDivisor hRadicand hOrders
    D hD S θ hθ hS hP hJ δ hδ)
  rw [AddSubgroup.mem_sup] at hm
  obtain ⟨x, hx, y, hy, hxy⟩ := hm
  rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup,
    Submodule.mem_span_image_finset_iff_exists_fun'] at hx
  obtain ⟨a, ha⟩ := hx
  have hy' : y ∈ Submodule.span ℤ
      (Set.range fun C : D.ιC => (2 * Real.pi * Complex.I) • ρ D S residue C) := by
    rw [← Submodule.mem_toAddSubgroup, Submodule.span_int_eq_addSubgroupClosure]
    exact hy
  rw [Submodule.mem_span_range_iff_exists_fun] at hy'
  obtain ⟨m, hms⟩ := hy'
  refine ⟨a, m, fun r => ?_⟩
  have he := congrFun hxy r
  rw [← he, ← ha, ← hms]
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply]
  simp only [zsmul_eq_mul, smul_eq_mul]
  rfl

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
