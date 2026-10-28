import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq

open AlgebraicCurve Polynomial

theorem AlgebraicCurve.RegularProlongation.exists_prolongation_of_card_roots_eq
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    {q : ℕ} [Fact q.Prime] (f : R.integers)
    (S : Finset Fbar) (hS : S.card = q) (hSf : ∀ s ∈ S, s ^ q = R.residue f)
    (F' : Type*) [Field F'] [Algebra F F'] [Algebra L F'] [IsScalarTower L F F']
    [IsSplittingField F F' (X ^ q - C (f : F))] (hdeg : Module.finrank F F' = q) :
    ∃ R' : Fin q → RegularProlongation A F' Fbar,
      Function.Injective (fun i => (R' i).integers) ∧
      ∀ i, (R' i).integers.comap (algebraMap F F') = R.integers ∧
        ∀ (x : (R' i).integers) (y : R.integers), algebraMap F F' y = x →
          (R' i).residue x = R.residue y := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq.solution
