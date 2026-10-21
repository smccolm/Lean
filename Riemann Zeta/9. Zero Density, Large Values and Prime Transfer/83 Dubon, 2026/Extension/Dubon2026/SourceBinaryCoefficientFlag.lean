import Dubon2026.HomogeneousMonomialBasis

/-! The actual coefficient flag for residual weight reduction.
DUB-17/18 -> residual modular Galois association -> finite-characteristic
weight/level reduction -> the successive one-dimensional quotients of the
original binary polynomial coefficient system at a level divisible by the
residue characteristic. Invariance under the actual group and Hecke actions
is the next required step.

Adapted from the coefficient flag in anthropics/fermats-last-theorem,
revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_HeckeEis_exists_isEigensystemH1_gamma0NebenRep_of_isEigensystemH1_binaryFormRepSL_of_dvd.lean
(Apache-2.0; retained LICENSE and NOTICE), on the existing native homogeneous
polynomial space.
-/

namespace Dubon2026
noncomputable section
open MvPolynomial

variable (R : Type) [CommRing R] (n : ℕ)

/-- The original degree-n coefficient flag: all monomials with first exponent
below j have zero coefficient. -/
def sourceBinaryCoefficientFlag (j : ℕ) :
    Submodule R (homogeneousSubmodule (Fin 2) R n) where
  carrier := {P | ∀ m : Fin 2 →₀ ℕ, m 0 < j → coeff m P.val = 0}
  zero_mem' := fun _ _ => by simp
  add_mem' := by
    intro P Q hP hQ m hm
    simp [hP m hm, hQ m hm]
  smul_mem' := by
    intro r P hP m hm
    simp [hP m hm]

/-- The actual coefficient flag begins with the full original coefficient space. -/
theorem sourceBinaryCoefficientFlag_zero :
    sourceBinaryCoefficientFlag R n 0 = ⊤ :=
  eq_top_iff.mpr fun _ _ _ hm => absurd hm (Nat.not_lt_zero _)

/-- The literal coefficient flag is decreasing. -/
theorem sourceBinaryCoefficientFlag_antitone :
    Antitone (sourceBinaryCoefficientFlag R n) :=
  fun _ _ h _ hP m hm => hP m (lt_of_lt_of_le hm h)

private theorem coefficient_degree {P : homogeneousSubmodule (Fin 2) R n}
    {m : Fin 2 →₀ ℕ} (hm : coeff m P.val ≠ 0) : m 0 + m 1 = n := by
  have hd : m.degree = n := by
    by_contra h
    exact hm (P.property.coeff_eq_zero h)
  simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_two] using hd

/-- The actual degree-n coefficient flag ends at zero after n+1 steps. -/
theorem sourceBinaryCoefficientFlag_succ_eq_bot :
    sourceBinaryCoefficientFlag R n (n + 1) = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro P hP
  apply Subtype.ext
  apply MvPolynomial.eq_zero_iff.mpr
  intro m
  by_contra h
  have hd := coefficient_degree R n h
  exact h (hP m (by omega))

/-- The original monomial exponent used for the j-th coefficient quotient. -/
def sourceBinaryFlagExponent (n j : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 j + Finsupp.single 1 (n - j)

/-- The first coordinate of the actual coefficient-quotient monomial is j. -/
theorem sourceBinaryFlagExponent_zero (n j : ℕ) : sourceBinaryFlagExponent n j 0 = j := by
  simp [sourceBinaryFlagExponent]

/-- The second coordinate of the actual coefficient-quotient monomial is n-j. -/
theorem sourceBinaryFlagExponent_one (n j : ℕ) : sourceBinaryFlagExponent n j 1 = n - j := by
  simp [sourceBinaryFlagExponent]

/-- The actual j-th coefficient map on its original coefficient-flag submodule. -/
def sourceBinaryFlagGraded (j : ℕ) : sourceBinaryCoefficientFlag R n j →ₗ[R] R where
  toFun P := coeff (sourceBinaryFlagExponent n j) P.val.val
  map_add' P Q := by simp
  map_smul' r P := by simp

/-- The kernel of the original j-th coefficient is exactly the next flag step. -/
theorem sourceBinaryFlagGraded_eq_zero_iff (j : ℕ) (P : sourceBinaryCoefficientFlag R n j) :
    sourceBinaryFlagGraded R n j P = 0 ↔ P.val ∈ sourceBinaryCoefficientFlag R n (j + 1) := by
  constructor
  · intro h m hm
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm' | hm'
    · exact P.property m hm'
    · by_contra hne
      have hd := coefficient_degree R n hne
      have he : m = sourceBinaryFlagExponent n j := by
        ext i
        fin_cases i
        · simpa [sourceBinaryFlagExponent] using hm'
        · simpa [sourceBinaryFlagExponent] using (show m 1 = n - j by omega)
      rw [he] at hne
      exact hne h
  · intro h
    exact h (sourceBinaryFlagExponent n j) (by rw [sourceBinaryFlagExponent_zero]; omega)

/-- Each nonterminal original coefficient-flag quotient maps onto the actual coefficient ring. -/
theorem sourceBinaryFlagGraded_surjective (j : ℕ) (hj : j ≤ n) :
    Function.Surjective (sourceBinaryFlagGraded R n j) := by
  intro r
  have hd : (sourceBinaryFlagExponent n j).degree = n := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two,
      sourceBinaryFlagExponent_zero, sourceBinaryFlagExponent_one]
    omega
  have hp : (monomial (sourceBinaryFlagExponent n j) r).IsHomogeneous n :=
    isHomogeneous_monomial r hd
  have hf : (⟨_, hp⟩ : homogeneousSubmodule (Fin 2) R n) ∈
      sourceBinaryCoefficientFlag R n j := by
    intro m hm
    change coeff m (monomial (sourceBinaryFlagExponent n j) r) = 0
    rw [coeff_monomial, if_neg]
    intro he
    rw [← he, sourceBinaryFlagExponent_zero] at hm
    exact lt_irrefl _ hm
  refine ⟨⟨_, hf⟩, ?_⟩
  change coeff (sourceBinaryFlagExponent n j) (monomial (sourceBinaryFlagExponent n j) r) = r
  simp

end
end Dubon2026
