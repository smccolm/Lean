import Dubon2026.SourceBinaryFlagEigenStep

/-! Finite descent of the actual residual binary H1 eigensystem to a character piece.
DUB-17/18 -> residual modular Galois association -> weight/level reduction
-> original coefficient-flag descent. The flag has exactly n+1 possible
nonzero character pieces and a zero terminal H1; no chosen surviving piece
or nonzero eigenclass in a quotient is assumed.
-/

namespace Dubon2026
noncomputable section

variable (F : Type) [Field F] (p Q : ℕ) [CharP F p] (hpQ : p ∣ Q) (n : ℕ)

private theorem terminalH1_zero
    (x : groupCohomology.H1 (sourceBinaryFlagRep F p Q hpQ n (n + 1))) : x = 0 := by
  refine groupCohomology.H1_induction_on x ?_
  intro c
  have hc : c = 0 := by
    apply groupCohomology.cocycles₁_ext
    intro g
    apply Subtype.ext
    have hm : (c g).val ∈ sourceBinaryCoefficientFlag F n (n + 1) := (c g).property
    rw [sourceBinaryCoefficientFlag_succ_eq_bot] at hm
    exact hm
  rw [hc]
  exact map_zero (groupCohomology.H1π _).hom

private theorem flag_descent [NeZero Q] (eigenvalues : sourceBinaryHeckePrime Q → F) :
    ∀ (d j : ℕ), j + d = n + 1 →
      ∀ x : groupCohomology.H1 (sourceBinaryFlagRep F p Q hpQ n j), x ≠ 0 →
        (∀ ell, sourceBinaryFlagHeckeOperators F p Q hpQ n j ell x = eigenvalues ell • x) →
        ∃ r : ℕ, j ≤ r ∧ r ≤ n ∧
          ∃ y : groupCohomology.H1 (sourceBinaryFlagQuotientRep F p Q hpQ n r),
            y ≠ 0 ∧ ∀ ell, sourceBinaryFlagQuotientOperators F p Q hpQ n r ell y =
              eigenvalues ell • y := by
  intro d
  induction d with
  | zero =>
    intro j hj x hx _
    have he : j = n + 1 := by omega
    subst j
    exact (hx (terminalH1_zero F p Q hpQ n x)).elim
  | succ d ih =>
    intro j hj x hx heig
    have hjn : j ≤ n := by omega
    rcases sourceBinaryFlag_eigen_step F p Q hpQ n j hjn eigenvalues x hx heig with h | h
    · obtain ⟨y, hy, he⟩ := h
      exact ⟨j, le_refl j, hjn, y, hy, he⟩
    · obtain ⟨y, hy, he⟩ := h
      obtain ⟨r, hjr, hrn, z, hz, hze⟩ := ih (j + 1) (by omega) y hy he
      exact ⟨r, (Nat.le_succ j).trans hjr, hrn, z, hz, hze⟩

/-- A nonzero original residual flag H1 eigensystem has all its good-prime
eigenvalues realized on one of the actual one-dimensional coefficient
characters. The exact sequence, finite descent and nonzero surviving
character piece are all proved. -/
theorem sourceBinaryFlag_exists_characterPiece [NeZero Q]
    (eigenvalues : sourceBinaryHeckePrime Q → F)
    (x : groupCohomology.H1 (sourceBinaryFlagRep F p Q hpQ n 0)) (hx : x ≠ 0)
    (heig : ∀ ell, sourceBinaryFlagHeckeOperators F p Q hpQ n 0 ell x = eigenvalues ell • x) :
    ∃ j : ℕ, j ≤ n ∧
      ∃ y : groupCohomology.H1 (sourceBinaryFlagQuotientRep F p Q hpQ n j),
        y ≠ 0 ∧ ∀ ell, sourceBinaryFlagQuotientOperators F p Q hpQ n j ell y =
          eigenvalues ell • y := by
  obtain ⟨j, _, hj, y, hy, he⟩ :=
    flag_descent F p Q hpQ n eigenvalues (n + 1) 0 (Nat.zero_add _) x hx heig
  exact ⟨j, hj, y, hy, he⟩

end
end Dubon2026
