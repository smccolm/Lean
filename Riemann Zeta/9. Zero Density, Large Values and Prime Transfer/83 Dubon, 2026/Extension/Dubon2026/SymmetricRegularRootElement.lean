import Dubon2026.SymmetricResidualRootLifts
import Dubon2026.FiniteSymmetricRegularDiagonal

/-! A genuine higher symmetric residual image contains a regular element
fixing any prescribed original root of unity. This removes the regular
root-fixing witness from DUB-17's auxiliary-prime construction; residual
image containment and dual-class detection remain separate obligations. -/

namespace Dubon2026
noncomputable section
open scoped MatrixGroups

/-- Construct a root-fixing original Galois element whose actual residual
matrix is a literal split diagonal symmetric matrix with distinct weights. -/
theorem galois_exists_root_fixing_symmetric_regular
    {F Ω K : Type} [Field F] [Field Ω] [Algebra F Ω] [Field K] [Finite K]
    [NeZero (2 : K)] [NeZero (3 : K)]
    (n : ℕ) (hn : 2 * n < Nat.card K - 1)
    (ρ : Gal(Ω/F) →* Matrix.GeneralLinearGroup (Fin (n + 1)) K)
    (himage : ((homogeneousSymmetricGL (R := K) n).comp
      Matrix.SpecialLinearGroup.toGL).range ≤ ρ.range)
    {m : ℕ} [NeZero m] {ζ : Ω} (hζ : IsPrimitiveRoot ζ m) :
    ∃ u : Kˣ, orderOf u = Nat.card K - 1 ∧
      ∃ γ : Gal(Ω/F), γ ζ = ζ ∧
        ρ γ = homogeneousSymmetricGL n
          (Matrix.SpecialLinearGroup.toGL (ringSL2UnitDiagonal u)) ∧
        (ρ γ).val.charpoly.Separable := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [Nat.card_units] at hu
  have horder : 2 * n < orderOf u := by rwa [hu]
  obtain ⟨γ, hfix, hγ⟩ :=
    galois_symmetricSL2_exists_root_fixing_lift n ρ himage hζ (ringSL2UnitDiagonal u)
  refine ⟨u, hu, γ, hfix, hγ, ?_⟩
  rw [hγ]
  exact homogeneousSymmetricGL_unitDiagonal_separable u n horder

end
end Dubon2026
