import Dubon2026.SourceTrivialHeckeAlgebra
import Dubon2026.SourceTrivialIntegralChange
import Dubon2026.SourceResidualHeckeWords
import Dubon2026.SourceFiniteOrderHeckeEigen

/-! DUB-17/18 -> residual Galois association -> characteristic-zero
weight-two eigenvalue lifting. The original integral-span eigenclass
constructs a character of the genuine finite integral Hecke algebra.
The existing word-to-character theorem is reused. Integral relations are
transported to the actual residue class using its proved integral span.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology

variable (F : Type) [Field F] (Q : ℕ)

/-- A nonzero original integral-span weight-two eigenclass supplies a
character of the actual integral Hecke algebra, with its exact eigenvalues. -/
theorem sourceTrivialIntegralSpan_exists_HeckeCharacter
    (values : sourceBinaryHeckePrime Q → F)
    (x : H1 (Rep.trivial F (Gamma0 Q) F)) (hx : x ≠ 0)
    (heig : ∀ ell, sourceTrivialCoefficientHeckeOperators F Q ell x = values ell • x)
    (hspan : x ∈ Submodule.span F (Set.range fun z : Additive (Gamma0 Q) →+ ℤ =>
      (H1IsoOfIsTrivial (Rep.trivial F (Gamma0 Q) F)).inv ((Int.castAddHom F).comp z))) :
    ∃ χ : sourceTrivialHeckeAlgebra Q →ₐ[ℤ] F,
      ∀ ell : sourceBinaryHeckePrime Q,
        χ ⟨sourceTrivialRingHeckeOperators ℤ Q ell, Algebra.subset_adjoin ⟨ell, rfl⟩⟩ =
          values ell := by
  apply sourceHeckeWord_exists_character (sourceTrivialRingHeckeOperators ℤ Q) values
  intro a ha
  have hv : ∀ y ∈ Submodule.span F (Set.range fun z : Additive (Gamma0 Q) →+ ℤ =>
      (H1IsoOfIsTrivial (Rep.trivial F (Gamma0 Q) F)).inv ((Int.castAddHom F).comp z)),
      FreeAlgebra.lift ℤ (sourceTrivialRingHeckeOperators F Q) a y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, rfl⟩ := hy
      let z₁ := (H1IsoOfIsTrivial (Rep.trivial ℤ (Gamma0 Q) ℤ)).inv z
      have hc : sourceTrivialH1IntegerChange F Q z₁ =
          (H1IsoOfIsTrivial (Rep.trivial F (Gamma0 Q) F)).inv ((Int.castAddHom F).comp z) := by
        change (H1IsoOfIsTrivial (Rep.trivial F (Gamma0 Q) F)).inv
          ((Int.castAddHom F).comp
            ((H1IsoOfIsTrivial (Rep.trivial ℤ (Gamma0 Q) ℤ)).hom
              ((H1IsoOfIsTrivial (Rep.trivial ℤ (Gamma0 Q) ℤ)).inv z))) = _
        simp
      have h := sourceResidualHeckeWord_intertwine (sourceTrivialRingHeckeOperators ℤ Q)
        (sourceTrivialRingHeckeOperators F Q) (sourceTrivialH1IntegerChange F Q).toAddMonoidHom
        (fun ell v => sourceTrivialH1IntegerChange_hecke F Q ell v) a z₁
      rw [ha, LinearMap.zero_apply, map_zero] at h
      exact (congrArg (fun y =>
        FreeAlgebra.lift ℤ (sourceTrivialRingHeckeOperators F Q) a y) hc).symm.trans h.symm
    | zero => exact map_zero _
    | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
    | smul r y _ hy => rw [map_smul, hy, smul_zero]
  have h := sourceResidualHeckeWord_eigenvector (sourceTrivialRingHeckeOperators F Q)
    values x heig a
  rw [hv x hspan] at h
  exact (smul_eq_zero.mp h.symm).resolve_right hx

/-- Every nonzero original weight-two eigensystem either constructs its
actual integral Hecke character or has the exact Eisenstein eigenvalues. -/
theorem sourceTrivialH1Eigen_HeckeCharacter_or_eisenstein [NeZero Q]
    (values : sourceBinaryHeckePrime Q → F)
    (x : H1 (Rep.trivial F (Gamma0 Q) F)) (hx : x ≠ 0)
    (heig : ∀ ell, sourceTrivialCoefficientHeckeOperators F Q ell x = values ell • x) :
    (∃ χ : sourceTrivialHeckeAlgebra Q →ₐ[ℤ] F,
      ∀ ell : sourceBinaryHeckePrime Q,
        χ ⟨sourceTrivialRingHeckeOperators ℤ Q ell, Algebra.subset_adjoin ⟨ell, rfl⟩⟩ =
          values ell) ∨
      ∀ ell, values ell = (ell.val : F) + 1 := by
  rcases sourceTrivialH1Eigen_integral_or_eisenstein F Q values x heig with hs | he
  · exact Or.inl (sourceTrivialIntegralSpan_exists_HeckeCharacter F Q values x hx heig hs)
  · exact Or.inr he

end
end Dubon2026
