import Dubon2026.SourcePrimitiveFiniteGoodEigensystem
import Dubon2026.SourceSymmetricSumSquaresKernel
import Dubon2026.PrimitiveCoefficientReality
import Dubon2026.CuspPeterssonCore

/-! DUB-17/18 -> primitive determinant -> exact required component.
The finite good-prime equations give a literal sum of squared shifted Hecke
operators. Their actual Petersson adjointness and real primitive coefficients
prove that its kernel is the primitive line, without a spectral premise. -/
namespace Dubon2026
noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups
variable (N : ℕ) [NeZero N]
local notation "S" => CuspForm (Subgroup.map (mapGL ℝ) (Gamma0 N)) 2

/-- The actual good Hecke operator minus its prescribed primitive eigenvalue. -/
def primitiveGoodShift (f : PrimitiveCuspForm N 2) (q : {q : Nat.Primes // q.val.Coprime N}) :
    Module.End ℂ S :=
  cuspHeckeLinear N 2 q.val.val - cuspCoefficients f.toCuspForm q.val.val • 1

/-- A finite sum of squares of the actual shifted good Hecke operators. -/
def primitiveGoodAnnihilator (f : PrimitiveCuspForm N 2)
    (s : Finset {q : Nat.Primes // q.val.Coprime N}) : Module.End ℂ S :=
  ∑ q ∈ s, primitiveGoodShift N f q ^ 2

theorem primitiveGoodShift_selfAdjoint (f : PrimitiveCuspForm N 2)
    (q : {q : Nat.Primes // q.val.Coprime N}) :
    IsCuspPeterssonSelfAdjoint (primitiveGoodShift N f q) :=
  cuspPeterssonSelfAdjoint_sub (cuspHeckeLinear_coprime_selfAdjoint N 2 q.val.val q.property)
    (cuspPeterssonSelfAdjoint_smul (cuspPeterssonSelfAdjoint_one N 2) _
      (primitiveCuspForm_coefficient_conj f q.val.val q.property))

theorem primitiveGoodAnnihilator_selfAdjoint (f : PrimitiveCuspForm N 2)
    (s : Finset {q : Nat.Primes // q.val.Coprime N}) :
    IsCuspPeterssonSelfAdjoint (primitiveGoodAnnihilator N f s) := by
  letI := cuspPeterssonCore N 2
  letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := S)
  letI := InnerProductSpace.ofCore (cuspPeterssonCore N 2).toCore
  exact LinearMap.isSymmetric_sum s (fun q _ =>
    (show (primitiveGoodShift N f q).IsSymmetric from primitiveGoodShift_selfAdjoint N f q).pow 2)

theorem primitiveGoodAnnihilator_eq_zero_iff (f : PrimitiveCuspForm N 2)
    (s : Finset {q : Nat.Primes // q.val.Coprime N}) (g : S) :
    primitiveGoodAnnihilator N f s g = 0 ↔
      ∀ q ∈ s, cuspHeckeLinear N 2 q.val.val g = cuspCoefficients f.toCuspForm q.val.val • g := by
  letI := cuspPeterssonCore N 2
  letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := S)
  letI := InnerProductSpace.ofCore (cuspPeterssonCore N 2).toCore
  have h := symmetric_sum_squares_eq_zero_iff s (primitiveGoodShift N f)
    (fun q _ => primitiveGoodShift_selfAdjoint N f q) g
  simpa only [primitiveGoodAnnihilator, primitiveGoodShift, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] using h

theorem exists_primitive_good_annihilator (f : PrimitiveCuspForm N 2) :
    ∃ s : Finset {q : Nat.Primes // q.val.Coprime N},
      IsCuspPeterssonSelfAdjoint (primitiveGoodAnnihilator N f s) ∧
      LinearMap.ker (primitiveGoodAnnihilator N f s) = Submodule.span ℂ {f.toCuspForm} := by
  classical
  obtain ⟨s, hs⟩ := exists_primitive_finite_good_eigensystem N f
  refine ⟨s, primitiveGoodAnnihilator_selfAdjoint N f s, ?_⟩
  apply le_antisymm
  · intro g hg
    have he := (hs g).mp ((primitiveGoodAnnihilator_eq_zero_iff N f s g).mp hg)
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton f.toCuspForm))
  · apply Submodule.span_le.mpr
    rintro g (rfl : g = f.toCuspForm)
    apply (primitiveGoodAnnihilator_eq_zero_iff N f s f.toCuspForm).mpr
    intro q _
    exact primitiveCuspForm_eigenvector f q.val.property.pos q.property

end
end Dubon2026
