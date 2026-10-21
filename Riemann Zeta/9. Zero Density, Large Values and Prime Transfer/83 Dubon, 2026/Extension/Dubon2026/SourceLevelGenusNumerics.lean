import Dubon2026.SourceLevelPsi

/-! DUB-17/18 -> parabolic geometric realization -> matching period
dimensions. Original arithmetic counts for the genus formula, selected from
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_ModularCurve_GenusNumerics.lean.
-/
namespace Dubon2026.SourceLevelProjective

/-- The exact residue-root count for the order-two elliptic action. -/
noncomputable def nuTwo (N : ℕ) : ℕ := Nat.card {x : ZMod N // x ^ 2 + 1 = 0}

/-- The exact residue-root count for the order-three elliptic action. -/
noncomputable def nuThree (N : ℕ) : ℕ := Nat.card {x : ZMod N // x ^ 2 + x + 1 = 0}

/-- The original arithmetic cusp-count expression. -/
def cuspCount (N : ℕ) : ℕ :=
  ∑ d ∈ N.divisors, Nat.totient (Nat.gcd d (N / d))

@[simp]
lemma cuspCount_one : cuspCount 1 = 1 := by
  simp [cuspCount]

/-- The arithmetic genus expression required by the geometric dimension comparison. -/
noncomputable def genusFormula (N : ℕ) : ℚ :=
  1 + (dedekindPsi N : ℚ) / 12 - (nuTwo N : ℚ) / 4 - (nuThree N : ℚ) / 3
    - (cuspCount N : ℚ) / 2


end Dubon2026.SourceLevelProjective
