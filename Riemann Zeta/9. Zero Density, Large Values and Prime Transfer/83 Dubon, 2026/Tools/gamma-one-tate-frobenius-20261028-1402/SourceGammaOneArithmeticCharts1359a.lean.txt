import Dubon2026.SourceGammaOneArithmeticPlaces
import Dubon2026.SourceReductionChartGluing
import Dubon2026.SourceGammaOneDecompositionGauss

/-! DUB-17/18 -> original Gamma1 Tate inertia -> arithmetic compatibility
of actual place specialization. Transport the native monic chart equations
and valuation nonunits by the original coefficient automorphism. These are
the exact two charts used by the existing specialization construction. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve SourceCurve.RegularProlongation
local notation "Qbar" => AlgebraicClosure ℚ
variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
local notation "F" => functionFieldOver Γ Qbar

theorem arithmeticRingAut_mem_adjoin (σ : Qbar ≃ₐ[ℚ] Qbar)
    (y : F) (hy : arithmeticRingAut Γ σ y = y)
    {f : F} (hf : f ∈ Algebra.adjoin Qbar ({y} : Set F)) :
    arithmeticRingAut Γ σ f ∈ Algebra.adjoin Qbar ({y} : Set F) := by
  induction hf using Algebra.adjoin_induction with
  | mem x hx =>
    obtain rfl := Set.mem_singleton_iff.mp hx
    rw [hy]
    exact Algebra.subset_adjoin (Set.mem_singleton _)
  | algebraMap a =>
    rw [arithmeticRingAut_constants]
    exact (Algebra.adjoin Qbar ({y} : Set F)).algebraMap_mem _
  | add x z _ _ hx hz => simpa only [map_add] using add_mem hx hz
  | mul x z _ _ hx hz => simpa only [map_mul] using mul_mem hx hz

theorem arithmeticRingAut_isIntegral (σ : Qbar ≃ₐ[ℚ] Qbar)
    (y : F) (hy : arithmeticRingAut Γ σ y = y)
    {f : F} (hf : IsIntegral (Algebra.adjoin Qbar ({y} : Set F)) f) :
    IsIntegral (Algebra.adjoin Qbar ({y} : Set F)) (arithmeticRingAut Γ σ f) := by
  let φ : Algebra.adjoin Qbar ({y} : Set F) →+* Algebra.adjoin Qbar ({y} : Set F) :=
    { toFun := fun f => ⟨arithmeticRingAut Γ σ f.val,
        arithmeticRingAut_mem_adjoin Γ σ y hy f.property⟩
      map_one' := Subtype.ext (map_one (arithmeticRingAut Γ σ))
      map_mul' := fun f g => Subtype.ext (map_mul (arithmeticRingAut Γ σ) f.val g.val)
      map_zero' := Subtype.ext (map_zero (arithmeticRingAut Γ σ))
      map_add' := fun f g => Subtype.ext (map_add (arithmeticRingAut Γ σ) f.val g.val) }
  exact IsIntegral.map_of_comp_eq φ (arithmeticRingAut Γ σ).toRingHom (by ext x; rfl) hf

theorem nonunit_arithmeticPlace_iff (σ : Qbar ≃ₐ[ℚ] Qbar)
    (P : Place Qbar F) (f : F) :
    f ∈ (arithmeticPlace Γ σ P).toValuationSubring.nonunits ↔
      arithmeticRingAut Γ σ.symm f ∈ P.toValuationSubring.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or]
  change f = 0 ∨ arithmeticRingAut Γ σ.symm f⁻¹ ∉ P.toValuationSubring ↔ _
  rw [map_inv₀]
  simp only [map_eq_zero]

theorem chartDomain_arithmeticPlace (A : ValuationSubring Qbar)
    (d : A.decompositionSubgroup ℚ) (P : Place Qbar F) (y : F)
    (hy : arithmeticRingAut Γ d.val.symm y = y) (hP : ChartDomain A P y) :
    ChartDomain A (arithmeticPlace Γ d.val P) y := by
  obtain ⟨a, ha⟩ := hP
  refine ⟨d • a, (nonunit_arithmeticPlace_iff Γ d.val P _).mpr ?_⟩
  rw [map_sub, hy, arithmeticRingAut_constants]
  change y - algebraMap Qbar F (d.val.symm (d.val a)) ∈ P.toValuationSubring.nonunits
  simpa only [AlgEquiv.symm_apply_apply] using ha

end
end Dubon2026.SourceFunctionField.GammaOne
