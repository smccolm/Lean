import Dubon2026.SourceOriginalCuspPeriodTranspose

/-! DUB-17/18 -> actual rank-two matrix descent -> faithful real matrix
realization of cusp Hecke operators. The actual transpose and the original
real lattice basis give an injective real-linear map. Its integral Hecke
image is precisely the cast matrix image of the original lattice algebra.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential CongruenceSubgroup

private def complex_operator_real_matrix {P : Type*} [AddCommGroup P] [Module ℂ P]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ P) :
    Module.End ℂ P →ₗ[ℝ] Matrix ι ι ℝ :=
  (LinearMap.toMatrix b b).toLinearMap.comp
    (LinearMap.restrictScalarsₗ (R := ℝ) (S := ℂ) (R₁ := ℝ) (M := P) (N := P))

private theorem complex_operator_real_matrix_injective
    {P : Type*} [AddCommGroup P] [Module ℂ P]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ P) :
    Function.Injective (complex_operator_real_matrix b) := by
  intro T U h
  exact LinearMap.restrictScalars_injective ℝ ((LinearMap.toMatrix b b).injective h)

variable (N : ℕ) [NeZero N]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)
local notation "S" => CuspForm (Gamma0 N) 2

/-- Faithful real matrices of actual cusp operators, through the original period lattice. -/
def originalCuspRealHeckeMatrix {n : ℕ} (b : Module.Basis (Fin n) ℂ V)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lb : Module.Basis ι ℤ (pathPeriodLattice N (fun i => (b i).val))) :
    Module.End ℂ S →ₗ[ℝ] Matrix ι ι ℝ :=
  (complex_operator_real_matrix (originalPeriodRealBasis N b lb)).comp
    ((originalCuspPeriodTranspose N b).restrictScalars ℝ)

theorem originalCuspRealHeckeMatrix_apply {n : ℕ} (b : Module.Basis (Fin n) ℂ V)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lb : Module.Basis ι ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (T : Module.End ℂ S) :
    originalCuspRealHeckeMatrix N b lb T =
      originalPeriodRealMatrix N b lb (originalCuspPeriodTranspose N b T) := rfl

theorem originalCuspRealHeckeMatrix_injective {n : ℕ} (b : Module.Basis (Fin n) ℂ V)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lb : Module.Basis ι ℤ (pathPeriodLattice N (fun i => (b i).val))) :
    Function.Injective (originalCuspRealHeckeMatrix N b lb) :=
  (complex_operator_real_matrix_injective (originalPeriodRealBasis N b lb)).comp
    (originalCuspPeriodTranspose_injective N b)

theorem originalCuspRealHeckeMatrix_word {n : ℕ} (b : Module.Basis (Fin n) ℂ V)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lb : Module.Basis ι ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (a : FreeAlgebra ℤ Nat.Primes) :
    originalCuspRealHeckeMatrix N b lb (sourceWeightTwoCuspHeckeWord N a) =
      originalPeriodRealMatrix N b lb (originalPeriodHeckeWord N b a) :=
  congrArg (originalPeriodRealMatrix N b lb) (originalCuspPeriodTranspose_heckeWord N b a)

theorem originalCuspRealHeckeMatrix_range {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V)
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val))) :
    Set.range (fun t : sourceOriginalIntegralHeckeAlgebra N 2 =>
      originalCuspRealHeckeMatrix N b lb t.val) =
      Set.range (fun t : originalFullLatticeHeckeAlgebra N b =>
        (originalLatticeHeckeMatrix N b lb t).map (Int.cast : ℤ → ℝ)) := by
  apply Eq.trans _ (originalFullHecke_real_matrix_range N b lb).symm
  apply Set.ext
  intro M
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨a, ha⟩ := sourceWeightTwoCuspHeckeWord_exists N t
    exact ⟨a, (originalCuspRealHeckeMatrix_word N b lb a).symm.trans
      ((congrArg (originalCuspRealHeckeMatrix N b lb) ha).trans ht)⟩
  · rintro ⟨a, ha⟩
    exact ⟨⟨sourceWeightTwoCuspHeckeWord N a, sourceWeightTwoCuspHeckeWord_mem_integral N a⟩,
      (originalCuspRealHeckeMatrix_word N b lb a).trans ha⟩

end
end Dubon2026.SourceFunctionField.OriginalChart
