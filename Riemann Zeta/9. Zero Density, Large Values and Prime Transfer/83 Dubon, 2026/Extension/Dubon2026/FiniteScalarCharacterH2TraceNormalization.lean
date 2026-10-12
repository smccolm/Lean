import Dubon2026.FiniteScalarCharacterH2Normalization
import Dubon2026.FiniteScalarTraceCup

/-! # The original extension-field invariant has the genuine trace normalization

The extended normalized unit sends its actual scalar multiple to that scalar,
and scalar trace on original H2 agrees with the actual field trace. Thus the
new extension-field invariant is the original prime-field normalization
extended linearly, as required by DUB-17's finite-field trace pairing.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] characterDualSequenceContinuousSMul

variable {k G : Type} [Field k] [Group G]
  (q : ℕ) [Fact q.Prime] [CharP k q] [Algebra (ZMod q) k]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (χ : G →* ZMod q) (hχ : Continuous χ)
/-- Genuine scalar trace carries a scalar multiple of an original
extended prime-field H2 class to its field trace times that same class. -/
theorem finiteScalarTraceCharacterH2Map_extend_smul (a : k)
    (u : ContinuousRepresentationH2 (coefficientCharacterRep χ) (coefficientCharacterAction_continuous χ hχ)) :
    finiteScalarTraceCharacterH2Map q χ hχ (k := k) (a • finiteScalarCharacterH2Extend q χ hχ (k := k) u) =
      Algebra.trace (ZMod q) k a • u := by
  induction u using Submodule.Quotient.induction_on with
  | _ c =>
    letI : Module (ZMod q) (continuousRepresentationCocyclesTwo (coefficientCharacterRep χ)) :=
      (continuousRepresentationCocyclesTwo (coefficientCharacterRep χ)).module
    apply congrArg (continuousRepresentationCoboundariesTwo (coefficientCharacterRep χ)
      (coefficientCharacterAction_continuous χ hχ)).mkQ
    apply Subtype.ext
    apply Subtype.ext
    funext z
    change Algebra.trace (ZMod q) k (a * algebraMap (ZMod q) k (c.val z)) =
      Algebra.trace (ZMod q) k a * c.val z
    rw [mul_comm a]
    have ht : Algebra.trace (ZMod q) k (algebraMap (ZMod q) k (c.val z) * a) =
        c.val z * Algebra.trace (ZMod q) k a := by
      simpa only [Algebra.smul_def, smul_eq_mul] using (Algebra.trace (ZMod q) k).map_smul (c.val z) a
    exact ht.trans (mul_comm _ _)

variable [Finite k]
  (σ : ContinuousRepresentationH2 (coefficientCharacterRep χ)
    (coefficientCharacterAction_continuous χ hχ) ≃ₗ[ZMod q] ZMod q)

/-- The constructed extension-field invariant is normalized by the actual
field trace and original prime-field invariant on every original H2 class. -/
theorem finiteScalarCharacterH2ScalarEquiv_trace
    (x : ContinuousRepresentationH2 (coefficientCharacterRep ((algebraMap (ZMod q) k).toMonoidHom.comp χ))
      (coefficientCharacterAction_continuous _ (finiteScalarCharacter_continuous q χ hχ))) :
    σ (finiteScalarTraceCharacterH2Map q χ hχ (k := k) x) =
      Algebra.trace (ZMod q) k (finiteScalarCharacterH2ScalarEquiv q χ hχ σ x) := by
  obtain ⟨a, rfl⟩ := (finiteScalarCharacterH2Span_bijective q χ hχ σ (k := k)).surjective x
  have he : finiteScalarCharacterH2ScalarEquiv q χ hχ σ (finiteScalarCharacterH2Span q χ hχ σ a) = a :=
    (LinearEquiv.ofBijective (finiteScalarCharacterH2Span q χ hχ σ)
      (finiteScalarCharacterH2Span_bijective q χ hχ σ)).symm_apply_apply a
  rw [he]
  change σ (finiteScalarTraceCharacterH2Map q χ hχ (k := k) (a • finiteScalarCharacterH2Extend q χ hχ (k := k) (σ.symm 1))) = _
  rw [finiteScalarTraceCharacterH2Map_extend_smul, map_smul, σ.apply_symm_apply, smul_eq_mul, mul_one]

end
end Dubon2026
