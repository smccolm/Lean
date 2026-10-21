import Dubon2026.SourceAffineFlagInclusion
import Dubon2026.SourceNativeH1KernelHecke
import Dubon2026.SourceAffineFlagH1Lifting

/-! The actual weight-reduction eigenclass survives or has the exact Eisenstein exception.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> this survival alternative -> original evaluation at raised level
or removal of the explicitly computed exceptional eigenvalues.
Native H1 inclusion, the proved invariant quotient, actual prime-field
diagonal units and full original Hecke trace discharge every alternative.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup CategoryTheory groupCohomology

variable (F : Type) [Field F] (p Q : ℕ) [Fact p.Prime] [CharP F p] [NeZero Q]
    (hpQ : p ∣ Q) (j : Fin p)

private local instance affineSurvivalPrimeNeZero (ell : sourceBinaryHeckePrime Q) : NeZero ell.val :=
  ⟨ell.property.1.ne_zero⟩

/-- An actual nonzero function-flag H1 eigensystem either survives in the
whole original function representation, or has exactly the source's
exceptional exponent and Eisenstein eigenvalues at every good prime. -/
theorem sourceAffineFlag_eigen_survival (values : sourceBinaryHeckePrime Q → F)
    (x : H1 (sourceAffineFlagRep F p Q hpQ j)) (hx : x ≠ 0)
    (heig : ∀ ell, sourceAffineFlagHeckeOperators F p Q hpQ j ell x = values ell • x) :
    (∃ y : H1 (sourceAffineFunctionRep p Q F hpQ), y ≠ 0 ∧
      ∀ ell, sourceAffineFunctionHeckeOperators F p Q hpQ ell y = values ell • y) ∨
    (j.val + 1 < p ∧ (p - 1) ∣ 2 * (j.val + 1) ∧
      ∀ ell : sourceBinaryHeckePrime Q,
        values ell = ((ell.val : F) + 1) *
          (ZMod.castHom (dvd_refl p) F ((ell.val : ZMod p)⁻¹)) ^ (j.val + 1)) := by
  by_cases hzero : sourceAffineFlagInclusionH1 F p Q hpQ j x = 0
  · right
    have hj : j.val + 1 < p := by
      by_contra hn
      have htop : p - 1 ≤ j.val := by omega
      apply hx
      apply sourceAffineFlagInclusionH1_top_injective F p Q hpQ j htop
      rw [hzero, map_zero]
    induction x using H1_induction_on with
    | h z =>
      let A := sourceAffineFlagRep F p Q hpQ j
      let B := sourceAffineFunctionRep p Q F hpQ
      let f := sourceAffineFlagInclusion F p Q hpQ j
      let q : B := sourceFiniteFunctionMonomial F p (j.val + 1)
      have hq : ∀ v : B, (∀ g : Gamma0 Q, B.ρ g v - v ∈ LinearMap.range f.hom.toLinearMap) →
          ∃ r : F, v - r • q ∈ LinearMap.range f.hom.toLinearMap := by
        intro v hv
        change ∀ g : Gamma0 Q, B.ρ g v - v ∈
          LinearMap.range (sourceAffineFlagInclusion F p Q hpQ j).hom.toLinearMap at hv
        change ∃ r : F, v - r • q ∈
          LinearMap.range (sourceAffineFlagInclusion F p Q hpQ j).hom.toLinearMap
        rw [sourceAffineFlagInclusion_range] at hv ⊢
        exact sourceAffineFunction_invariant_quotient F p Q hj hv
      obtain ⟨v, r, _, hv, hr, hinv⟩ :=
        sourceNativeH1_kernel_representative A B f
          (sourceAffineFlagInclusion_injective F p Q hpQ j) q hq z hzero hx
      have hexp : (p - 1) ∣ 2 * (j.val + 1) := by
        apply sourceAffineFunction_invariant_exponent F p Q hpQ hj
        intro g
        have h := hinv g
        change B.ρ g q - q ∈
          LinearMap.range (sourceAffineFlagInclusion F p Q hpQ j).hom.toLinearMap at h
        rw [sourceAffineFlagInclusion_range] at h
        exact h
      refine ⟨hj, hexp, fun ell => ?_⟩
      let c : F := (ZMod.castHom (dvd_refl p) F ((ell.val : ZMod p)⁻¹)) ^ (j.val + 1)
      let b : Module.End F B := sourceAffineFunctionDiagonal p F ell.val
      have hc : b q - c • q ∈
          LinearMap.range f.hom.toLinearMap := by
        change sourceAffineFunctionDiagonal p F ell.val
            (sourceFiniteFunctionMonomial F p (j.val + 1)) -
          c • sourceFiniteFunctionMonomial F p (j.val + 1) ∈ _
        rw [sourceAffineFunctionDiagonal_monomial F p ell.val (j.val + 1)]
        change c • sourceFiniteFunctionMonomial F p (j.val + 1) -
          c • sourceFiniteFunctionMonomial F p (j.val + 1) ∈ _
        rw [sub_self]
        exact Submodule.zero_mem _
      have hT := sourceNativeH1_kernel_hecke ell.property.1 ell.property.2 A B f
        (sourceAffineFlagInclusion_injective F p Q hpQ j)
        (sourceAffineFlagDiagonal F p j ell.val) (sourceAffineFunctionDiagonal p F ell.val)
        (sourceAffineFlagDiagonal_intertwine F p Q hpQ j ell)
        (sourceAffineFunctionDiagonal_intertwine F p Q hpQ ell)
        (LinearMap.ext fun _ => rfl) q c hc hinv z v r hv hr
      have he : (values ell - (((ell.val : F) + 1) * c)) • H1π A z = 0 := by
        rw [sub_smul, ← heig ell]
        change sourcePrimeHeckeH1 ell.property.1 A _ _ (H1π A z) -
          (((ell.val : F) + 1) * c) • H1π A z = 0
        rw [hT, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp he).resolve_right hx)
  · left
    refine ⟨sourceAffineFlagInclusionH1 F p Q hpQ j x, hzero, fun ell => ?_⟩
    rw [← sourceAffineFlagInclusionH1_hecke, heig, map_smul]

/-- The actual character eigenclass gives the original full-function
eigensystem or exactly the computed source Eisenstein exception.
All native coefficient lifting prerequisites are proved. -/
theorem sourceAffineCharacter_eigen_survival (h6 : (6 : F) ≠ 0)
    (values : sourceBinaryHeckePrime Q → F)
    (x : H1 (sourceBinaryFlagQuotientRep F p Q hpQ (2 * j.val) 0))
    (hx : x ≠ 0)
    (heig : ∀ ell, sourceBinaryFlagUntwistedOperators F p Q hpQ (2 * j.val) 0 ell x =
      values ell • x) :
    (∃ y : H1 (sourceAffineFunctionRep p Q F hpQ), y ≠ 0 ∧
      ∀ ell, sourceAffineFunctionHeckeOperators F p Q hpQ ell y =
        (sourceAffineFlagHeckeScalar F p j ell.val * values ell) • y) ∨
    (j.val + 1 < p ∧ (p - 1) ∣ 2 * (j.val + 1) ∧
      ∀ ell : sourceBinaryHeckePrime Q,
        sourceAffineFlagHeckeScalar F p j ell.val * values ell =
          ((ell.val : F) + 1) *
            (ZMod.castHom (dvd_refl p) F ((ell.val : ZMod p)⁻¹)) ^ (j.val + 1)) := by
  obtain ⟨y, hy, he⟩ := sourceAffineFlag_exists_characterEigenlift F p Q hpQ j h6 values x hx heig
  exact sourceAffineFlag_eigen_survival F p Q hpQ j
    (fun ell => sourceAffineFlagHeckeScalar F p j ell.val * values ell) y hy he

end
end Dubon2026
