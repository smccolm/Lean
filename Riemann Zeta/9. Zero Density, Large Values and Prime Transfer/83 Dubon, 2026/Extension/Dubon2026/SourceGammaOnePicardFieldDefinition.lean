import Dubon2026.SourceGammaOnePlaceFieldDefinition
import Dubon2026.SourceGammaOneArithmeticTateOperators
import Mathlib.Algebra.GroupWithZero.Action.End

/-! DUB-17/18 -> original all-weight arithmetic association -> continuous
finite homogeneous-valued Tate action -> open stabilizers on actual Gamma1
Picard classes. Reuse the original finite-support argument with the proved
finite fields of definition of the literal Gamma1 places. This constructs
the finite field fixing each actual divisor class, without a continuity
or finite-image premise. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve CongruenceSubgroup
local notation "Qbar" => AlgebraicClosure ℚ
local notation "J" N => Pic0 Qbar (functionFieldOver (Gamma1 N) Qbar)

/-- The literal original Pic0 representation as the native arithmetic group action. -/
instance gammaOnePicardArithmeticAction (N : ℕ) [NeZero N] :
    DistribMulAction (Qbar ≃ₐ[ℚ] Qbar) (J N) :=
  DistribMulAction.compHom _ (arithmeticPicardRep (Gamma1 N) (by simp [Gamma1_mem, ModularGroup.T]))

private theorem divisor_fixed_of_support_fixed (N : ℕ) (σ : Qbar ≃ₐ[ℚ] Qbar)
    (D : Divisor Qbar (functionFieldOver (Gamma1 N) Qbar))
    (hD : ∀ v ∈ D.support, arithmeticPlace (Gamma1 N) σ v = v) :
    arithmeticDivisorEquiv (Gamma1 N) σ D = D := by
  classical
  conv_lhs => rw [← D.sum_single]
  rw [map_finsuppSum]
  calc
    D.sum (fun v n => arithmeticDivisorEquiv (Gamma1 N) σ (Finsupp.single v n)) =
        D.sum (fun v n => Finsupp.single v n) := by
      apply Finsupp.sum_congr
      intro v hv
      change Finsupp.equivMapDomain (arithmeticPlaceEquiv (Gamma1 N) σ) (Finsupp.single v (D v)) = _
      rw [Finsupp.equivMapDomain_single]
      change Finsupp.single (arithmeticPlace (Gamma1 N) σ v) (D v) = _
      rw [hD v hv]
    _ = D := D.sum_single

theorem gammaOne_picard_fieldOfDefinition (N : ℕ) [NeZero N] (x : J N) :
    ∃ E : IntermediateField ℚ Qbar, FiniteDimensional ℚ E ∧
      ∀ σ : Qbar ≃ₐ[ℚ] Qbar, σ ∈ E.fixingSubgroup → σ • x = x := by
  classical
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  choose E hE hfix using gammaOne_place_fieldOfDefinition N
  letI : ∀ v, FiniteDimensional ℚ (E v) := hE
  refine ⟨⨆ v ∈ D.val.support, E v, IntermediateField.finiteDimensional_iSup_of_finset, fun σ hσ => ?_⟩
  have hD : arithmeticDivisorEquiv (Gamma1 N) σ D.val = D.val := by
    apply divisor_fixed_of_support_fixed
    intro v hv
    exact hfix v σ (IntermediateField.fixingSubgroup_le (le_iSup₂_of_le v hv le_rfl) hσ)
  change arithmeticPicard (Gamma1 N) (by simp [Gamma1_mem, ModularGroup.T]) σ (Pic0.mk D) = Pic0.mk D
  rw [arithmeticPicard_mk]
  exact congrArg Pic0.mk (Subtype.ext hD)

theorem gammaOnePicard_isOpen_stabilizer (N : ℕ) [NeZero N] (x : J N) :
    IsOpen (MulAction.stabilizer (Qbar ≃ₐ[ℚ] Qbar) x : Set (Qbar ≃ₐ[ℚ] Qbar)) := by
  obtain ⟨E, hE, hfix⟩ := gammaOne_picard_fieldOfDefinition N x
  letI := hE
  apply Subgroup.isOpen_mono (H₁ := E.fixingSubgroup) ?_ E.fixingSubgroup_isOpen
  intro σ hσ
  exact MulAction.mem_stabilizer_iff.mpr (hfix σ hσ)

end
end Dubon2026.SourceFunctionField.GammaOne
