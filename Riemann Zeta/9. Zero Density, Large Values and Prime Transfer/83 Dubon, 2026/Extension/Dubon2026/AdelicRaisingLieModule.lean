import Dubon2026.AdelicLowestWeightJets
import Mathlib.LinearAlgebra.Basis.Basic

/-! # The genuine Lie submodule spanned by the original raising derivatives -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup Module
open scoped MatrixGroups

private theorem linearMap_span_invariant {W : Type*} [AddCommGroup W] [Module ℂ W]
    (T : Module.End ℂ W) (v : ℕ → W)
    (h : ∀ n, T (v n) ∈ Submodule.span ℂ (Set.range v))
    (w : W) (hw : w ∈ Submodule.span ℂ (Set.range v)) :
    T w ∈ Submodule.span ℂ (Set.range v) := by
  have he : Submodule.span ℂ (Set.range v) ≤
      (Submodule.span ℂ (Set.range v)).comap T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact h n
  exact he hw

private theorem compactLie_invariant {W : Type*} [AddCommGroup W] [Module ℂ W]
    [LieRingModule ComplexSl2 W] [LieModule ℂ ComplexSl2 W]
    (p : Submodule ℂ W) (x : ComplexSl2) (v : W)
    (hH : ⁅compactSl2H, v⁆ ∈ p) (hE : ⁅compactSl2E, v⁆ ∈ p) (hF : ⁅compactSl2F, v⁆ ∈ p) :
    ⁅x, v⁆ ∈ p := by
  rw [compactSl2_decomposition x, add_lie, add_lie, smul_lie, smul_lie, smul_lie]
  exact p.add_mem (p.add_mem (p.smul_mem _ hH) (p.smul_mem _ hE)) (p.smul_mem _ hF)

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The actual complex span of all original raising derivatives in the genuine adelic smooth space. -/
def adelicRaisingSpan : Submodule ℂ (adelicRealSmoothSubmodule f) :=
  Submodule.span ℂ (Set.range (adelicRaisingJet f))

/-- Every original raising derivative belongs to its literal complex span. -/
theorem adelicRaisingJet_mem_span (n : ℕ) : adelicRaisingJet f n ∈ adelicRaisingSpan f :=
  Submodule.subset_span ⟨n, rfl⟩

/-- The original cusp generator belongs to the original raising span. -/
theorem adelicSmoothGenerator_mem_raisingSpan : adelicSmoothGenerator f ∈ adelicRaisingSpan f :=
  adelicRaisingJet_mem_span f 0

/-- The actual raising matrix preserves the span of the original raising derivatives. -/
theorem adelicRaisingSpan_raise (v : adelicRealSmoothSubmodule f) (hv : v ∈ adelicRaisingSpan f) :
    ⁅compactSl2E, v⁆ ∈ adelicRaisingSpan f := by
  apply linearMap_span_invariant (adelicComplexSl2Action f compactSl2E) (adelicRaisingJet f) _ v hv
  intro n
  change ⁅compactSl2E, adelicRaisingJet f n⁆ ∈ adelicRaisingSpan f
  rw [adelicRaisingJet_raise]
  exact adelicRaisingJet_mem_span f (n + 1)

/-- The actual compact Cartan preserves the span of the original raising derivatives. -/
theorem adelicRaisingSpan_Cartan (hf : f ≠ 0) (v : adelicRealSmoothSubmodule f)
    (hv : v ∈ adelicRaisingSpan f) : ⁅compactSl2H, v⁆ ∈ adelicRaisingSpan f := by
  apply linearMap_span_invariant (adelicComplexSl2Action f compactSl2H) (adelicRaisingJet f) _ v hv
  intro n
  change ⁅compactSl2H, adelicRaisingJet f n⁆ ∈ adelicRaisingSpan f
  rw [adelicRaisingJet_weight f hf]
  exact (adelicRaisingSpan f).smul_mem _ (adelicRaisingJet_mem_span f n)

/-- The actual lowering matrix preserves the span of the original raising derivatives. -/
theorem adelicRaisingSpan_lower (hf : f ≠ 0) (v : adelicRealSmoothSubmodule f)
    (hv : v ∈ adelicRaisingSpan f) : ⁅compactSl2F, v⁆ ∈ adelicRaisingSpan f := by
  apply linearMap_span_invariant (adelicComplexSl2Action f compactSl2F) (adelicRaisingJet f) _ v hv
  intro n
  change ⁅compactSl2F, adelicRaisingJet f n⁆ ∈ adelicRaisingSpan f
  cases n with
  | zero =>
      rw [adelicRaisingJet_zero, adelicSmoothGenerator_lowering_zero]
      exact (adelicRaisingSpan f).zero_mem
  | succ n =>
      rw [adelicRaisingJet_lower f hf]
      exact (adelicRaisingSpan f).smul_mem _ (adelicRaisingJet_mem_span f n)

/-- Every actual traceless complex matrix preserves the genuine original raising span. -/
theorem adelicRaisingSpan_lie (hf : f ≠ 0) (x : ComplexSl2) (v : adelicRealSmoothSubmodule f)
    (hv : v ∈ adelicRaisingSpan f) : ⁅x, v⁆ ∈ adelicRaisingSpan f := by
  exact compactLie_invariant (adelicRaisingSpan f) x v (adelicRaisingSpan_Cartan f hf v hv)
    (adelicRaisingSpan_raise f v hv) (adelicRaisingSpan_lower f hf v hv)

/-- The literal original raising span is a genuine Lie submodule of the original adelic smooth representation. -/
def adelicRaisingLieSubmodule (hf : f ≠ 0) : LieSubmodule ℂ ComplexSl2 (adelicRealSmoothSubmodule f) :=
  { adelicRaisingSpan f with
    lie_mem := fun {x v} hv => adelicRaisingSpan_lie f hf x v hv }

/-- The original raising derivatives give an actual basis of their genuine Lie submodule for every nonzero positive-weight cusp form. -/
def adelicRaisingBasis (hf : f ≠ 0) (hk : 0 < k) : Basis ℕ ℂ (adelicRaisingSpan f) :=
  Basis.span (adelicRaisingJet_linearIndependent f hf hk)

/-- The actual basis vector is precisely the original raising derivative, without a replacement model. -/
theorem adelicRaisingBasis_apply (hf : f ≠ 0) (hk : 0 < k) (n : ℕ) :
    (adelicRaisingBasis f hf hk n).val = adelicRaisingJet f n := by
  exact Basis.coe_span_apply (adelicRaisingJet_linearIndependent f hf hk) n

end
end Dubon2026
