import Dubon2026.AlgebraicLocalResidueLift

/-! The actual inertia kernel and Frobenius powers for the original
normed algebraic extension. These are the arithmetic inputs to DUB-17's
continuous unramified H1 dimension, not a supplied abstract inertia group. -/

namespace Dubon2026
noncomputable section

variable (K L : Type) [NontriviallyNormedField K] [NormedField L]
  [NormedAlgebra K L] [IsUltrametricDist K] [IsUltrametricDist L] [CompleteSpace K]
  [IsGalois K L]

attribute [local instance] algebraicLocalIntegerAction algebraicLocalIntegerBaseAlgebra

/-- The original local inertia is the kernel of the original residue action. -/
def algebraicLocalInertia : Subgroup Gal(L/K) :=
  (MulSemiringAction.toRingAut Gal(L/K) (IsLocalRing.ResidueField (algebraicLocalIntegerRing L))).ker

/-- The actual residue-action kernel is normal in the original Galois group. -/
instance algebraicLocalInertia_normal : (algebraicLocalInertia K L).Normal :=
  MonoidHom.normal_ker _

/-- Membership in original local inertia means fixing every original residue class. -/
theorem algebraicLocalInertia_mem_iff (g : Gal(L/K)) :
    g ∈ algebraicLocalInertia K L ↔
      ∀ x : IsLocalRing.ResidueField (algebraicLocalIntegerRing L), g • x = x := by
  change MulSemiringAction.toRingAut Gal(L/K) _ g = 1 ↔ _
  constructor
  · intro h x
    exact congrArg (fun e => e x) h
  · intro h
    exact RingEquiv.ext h

/-- An actual arithmetic Frobenius lift has the required power action
on every original residue element, with the same original Galois element. -/
theorem algebraicLocal_frobenius_pow_residue (φ : Gal(L/K)) (q : ℕ)
    (hφ : ∀ x : algebraicLocalIntegerRing L,
      IsLocalRing.residue _ (φ • x) = (IsLocalRing.residue _ x) ^ q)
    (n : ℕ) (x : IsLocalRing.ResidueField (algebraicLocalIntegerRing L)) :
    φ ^ n • x = x ^ (q ^ n) := by
  have hφ' (y : IsLocalRing.ResidueField (algebraicLocalIntegerRing L)) : φ • y = y ^ q := by
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective y
    rw [← IsLocalRing.ResidueField.residue_smul]
    exact hφ y
  induction n generalizing x with
  | zero => simp only [pow_zero, one_smul, pow_one]
  | succ n ih =>
    rw [pow_succ, mul_smul, hφ', smul_pow', ih, ← pow_mul, ← pow_succ]

end
end Dubon2026
