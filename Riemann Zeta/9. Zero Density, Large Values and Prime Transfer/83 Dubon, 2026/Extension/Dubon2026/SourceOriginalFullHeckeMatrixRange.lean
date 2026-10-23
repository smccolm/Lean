import Dubon2026.SourceOriginalPeriodHeckeMatrices

/-! DUB-17/18 -> original rank-two Tate descent -> identify the exact
integral matrix action used by descent with all original Hecke words.
The already proved free-algebra range theorem supplies every operator;
the real matrix range therefore agrees with the genuine period-word range.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)

/-- The actual integral word evaluation, with codomain its full lattice algebra. -/
def originalFullLatticeHeckeWord {n : ℕ} (b : Module.Basis (Fin n) ℂ V) :
    FreeAlgebra ℤ Nat.Primes →ₐ[ℤ] originalFullLatticeHeckeAlgebra N b :=
  (originalLatticeHeckeWord N b).codRestrict _ (fun a => by
    exact (originalLatticeHeckeWord_range N b).le ⟨a, rfl⟩)

theorem originalFullLatticeHeckeWord_surjective {n : ℕ} (b : Module.Basis (Fin n) ℂ V) :
    Function.Surjective (originalFullLatticeHeckeWord N b) := by
  intro T
  have ht : T.val ∈ (originalLatticeHeckeWord N b).range :=
    (originalLatticeHeckeWord_range N b).ge T.property
  obtain ⟨a, ha⟩ := ht
  exact ⟨a, Subtype.ext ha⟩

theorem originalLatticeHeckeMatrix_word {n : ℕ} (b : Module.Basis (Fin n) ℂ V)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lb : Module.Basis ι ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (a : FreeAlgebra ℤ Nat.Primes) :
    originalLatticeHeckeMatrix N b lb (originalFullLatticeHeckeWord N b a) =
      LinearMap.toMatrix lb lb (originalLatticeHeckeWord N b a) := rfl

theorem originalFullHecke_real_matrix_range {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V)
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val))) :
    Set.range (fun t : originalFullLatticeHeckeAlgebra N b =>
      (originalLatticeHeckeMatrix N b lb t).map (Int.cast : ℤ → ℝ)) =
      Set.range (fun a => originalPeriodRealMatrix N b lb (originalPeriodHeckeWord N b a)) := by
  have hw (a : FreeAlgebra ℤ Nat.Primes) :
      (originalLatticeHeckeMatrix N b lb (originalFullLatticeHeckeWord N b a)).map
        (Int.cast : ℤ → ℝ) =
      originalPeriodRealMatrix N b lb (originalPeriodHeckeWord N b a) :=
    (congrArg (fun A : Matrix (Fin m) (Fin m) ℤ => A.map (Int.cast : ℤ → ℝ))
      (originalLatticeHeckeMatrix_word N b lb a)).trans
        (originalPeriodRealMatrix_heckeWord N b lb a).symm
  apply Set.ext
  intro M
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨a, ha⟩ := originalFullLatticeHeckeWord_surjective N b t
    exact ⟨a, (hw a).symm.trans ((congrArg
      (fun z => (originalLatticeHeckeMatrix N b lb z).map (Int.cast : ℤ → ℝ)) ha).trans ht)⟩
  · rintro ⟨a, ha⟩
    exact ⟨originalFullLatticeHeckeWord N b a, (hw a).trans ha⟩

end
end Dubon2026.SourceFunctionField.OriginalChart
