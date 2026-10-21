import Dubon2026.SourceLaurentRootTwist
import Dubon2026.SourceModularJSeries


/-! DUB-17/18 -> cusp-form lower dimension bound -> original regular
differential realization -> finite function-field extension -> monic relations.
This is the literal finite conjugate product and its coefficient descent.
SourcePrimeCoefficientPolynomialDescent proves analytic invariance and
polynomial descent, and SourcePrimeMonicRelation assembles the monic relation.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_ModularCurve_PhiGen.lean, literal conjugates, product and descent.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open PowerSeries HahnSeries Polynomial

namespace PhiGen

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- The actual prime-level conjugates after the common substitution q to q^ell. -/
def conj (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (ζ : Kˣ) : Fin (ℓ + 1) → LaurentSeries K :=
  Fin.cases (qExpand K (ℓ * ℓ) (coeffEmb K jq))
    (fun b : Fin ℓ => qTwist (ζ ^ (b : ℕ)) (coeffEmb K jq))

theorem conj_zero (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (ζ : Kˣ) :
    conj ℓ ζ (0 : Fin (ℓ + 1)) = qExpand K (ℓ * ℓ) (coeffEmb K jq) := rfl

theorem conj_succ (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (ζ : Kˣ) (b : Fin ℓ) :
    conj ℓ ζ b.succ = qTwist (ζ ^ (b : ℕ)) (coeffEmb K jq) := rfl

section Product

variable {K : Type*} [Field K] (ℓ : ℕ)

/-- The actual monic product of the linear factors of the finite conjugate family. -/
def phiProd (conj : Fin (ℓ + 1) → LaurentSeries K) : Polynomial (LaurentSeries K) :=
  ∏ i : Fin (ℓ + 1), (Polynomial.X - Polynomial.C (conj i))

theorem phiProd_monic (conj : Fin (ℓ + 1) → LaurentSeries K) : (phiProd ℓ conj).Monic :=
  monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (conj i)

theorem phiProd_natDegree (conj : Fin (ℓ + 1) → LaurentSeries K) :
    (phiProd ℓ conj).natDegree = ℓ + 1 := by
  rw [phiProd, natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
  simp

theorem phiProd_ne_zero (conj : Fin (ℓ + 1) → LaurentSeries K) : phiProd ℓ conj ≠ 0 :=
  (phiProd_monic ℓ conj).ne_zero

theorem phiProd_eval_conj (conj : Fin (ℓ + 1) → LaurentSeries K) (i : Fin (ℓ + 1)) :
    (phiProd ℓ conj).eval (conj i) = 0 := by
  rw [phiProd, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

end Product

section Descends

variable {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)

/-- Coefficientwise descent to the original rational series after the common q substitution. -/
def PhiGenDescends (c : ℕ → LaurentSeries ℚ) : Prop :=
  ∀ k : ℕ, (phiProd ℓ (conj ℓ ζ)).coeff k = coeffEmb K (qExpand ℚ ℓ (c k))

end Descends


end PhiGen

end
end Dubon2026.SourceFunctionField
