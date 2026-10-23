import Dubon2026.SourceOriginalCuspRealHeckeMatrix

/-! DUB-17/18 -> specialization of the original rank-two representation
to the prescribed eigenform -> identical integral Hecke relations on
cusp forms and the actual original period lattice. The faithful real
matrix comparison proves both directions, retaining the same prime words. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)

theorem originalCuspHecke_lattice_matrix_word {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V)
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (a : FreeAlgebra ℤ Nat.Primes) :
    originalCuspRealHeckeMatrix N b lb (sourceWeightTwoCuspHeckeWord N a) =
      (LinearMap.toMatrix lb lb (originalLatticeHeckeWord N b a)).map
        (Int.cast : ℤ → ℝ) :=
  (originalCuspRealHeckeMatrix_word N b lb a).trans (originalPeriodRealMatrix_heckeWord N b lb a)

theorem originalLatticeHeckeWord_eq_iff_cusp {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V)
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (a c : FreeAlgebra ℤ Nat.Primes) :
    originalLatticeHeckeWord N b a = originalLatticeHeckeWord N b c ↔
      sourceWeightTwoCuspHeckeWord N a = sourceWeightTwoCuspHeckeWord N c := by
  constructor
  · intro h
    apply originalCuspRealHeckeMatrix_injective N b lb
    have hm := congrArg (fun U : Module.End ℤ (pathPeriodLattice N (fun i => (b i).val)) =>
      (LinearMap.toMatrix lb lb U).map (Int.cast : ℤ → ℝ)) h
    exact (originalCuspHecke_lattice_matrix_word N b lb a).trans
      (hm.trans (originalCuspHecke_lattice_matrix_word N b lb c).symm)
  · intro h
    have hm := congrArg (originalCuspRealHeckeMatrix N b lb) h
    have hc := (originalCuspHecke_lattice_matrix_word N b lb a).symm.trans
      (hm.trans (originalCuspHecke_lattice_matrix_word N b lb c))
    apply (LinearMap.toMatrix lb lb).injective
    apply Matrix.ext
    intro i j
    exact Int.cast_injective (congrFun (congrFun hc i) j)

end
end Dubon2026.SourceFunctionField.OriginalChart
