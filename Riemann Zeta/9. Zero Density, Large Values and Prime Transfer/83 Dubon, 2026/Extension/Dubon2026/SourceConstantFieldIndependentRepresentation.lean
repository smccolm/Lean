import Dubon2026.SourceOriginalComplexSpanDescent

/-! DUB-17/18 -> original Picard injectivity -> principal-divisor descent.
Independent constant coefficients prevent cancellation of the least local
order. Adapted from the ord_sum_le and coefficient-representation arguments
in S_AlgebraicCurve_Divisor_isPrincipal_of_constantFieldExtension,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Existing order/unit identities replace the external local foundations.
-/
namespace Dubon2026.SourceCurve.ConstantField
noncomputable section
variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F'] [Algebra K F]
  [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F']
  [IsScalarTower K F F']

theorem exists_linearIndependent_repr {z : F'}
    (hz : z ∈ Submodule.span K' (Set.range (algebraMap F F'))) :
    ∃ (n : ℕ) (β : Fin n → K') (u : Fin n → F), LinearIndependent K β ∧
      z = ∑ k, algebraMap K' F' (β k) * algebraMap F F' (u k) := by
  classical
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hz
  set W : Submodule K K' := Submodule.span K (↑(c.support.image c) : Set K') with hW
  haveI : Module.Finite K W := FiniteDimensional.span_of_finite K (Finset.finite_toSet _)
  set b := Module.finBasis K W
  have hcW : ∀ f : F, c f ∈ W := by
    intro f
    by_cases hf : f ∈ c.support
    · exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem c hf))
    · rw [Finsupp.notMem_support_iff.1 hf]; exact zero_mem _
  refine ⟨_, fun k => (b k : K'), fun k => ∑ f ∈ c.support, b.repr ⟨c f, hcW f⟩ k • f,
    b.linearIndependent.map' W.subtype (Submodule.ker_subtype W), ?_⟩
  have hcf : ∀ f : F, c f = ∑ k, b.repr ⟨c f, hcW f⟩ k • (b k : K') := by
    intro f
    have h2 := congrArg Subtype.val (b.sum_repr ⟨c f, hcW f⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    exact h2.symm
  simp only [Finsupp.sum, map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  conv_lhs => rw [hcf f]
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul, map_mul,
    ← IsScalarTower.algebraMap_apply K K' F', ← IsScalarTower.algebraMap_apply K F F']
  ring


end
end Dubon2026.SourceCurve.ConstantField
