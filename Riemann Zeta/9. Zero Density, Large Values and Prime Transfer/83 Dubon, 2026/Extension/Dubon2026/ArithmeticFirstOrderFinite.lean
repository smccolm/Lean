import Dubon2026.ArithmeticFramedFiniteCoefficients
import Dubon2026.DualNumberOriginalResidue
import Dubon2026.DualNumberAdicTopology
import Dubon2026.ContinuousFirstOrderDeformation
import Mathlib.Algebra.CharP.Algebra

/-! # Finiteness of original continuous first-order arithmetic lifts -/

namespace Dubon2026

noncomputable section
open Matrix
open scoped NumberField

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K]
  [TopologicalSpace K] [DiscreteTopology K]

/-- Every original continuous first-order lift of an actual finite-field arithmetic representation lies in a proved finite framed coefficient fiber. The genuine dual-number residue and original topology are retained. -/
theorem arithmeticContinuousFirstOrderLift_finite
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP K p]
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι K) (hρ : Continuous ρ) :
    Finite {τ : MatrixFirstOrderLift ρ // Continuous τ.val} := by
  letI : TopologicalSpace (IsLocalRing.ResidueField K) := ⊥
  letI : DiscreteTopology (IsLocalRing.ResidueField K) := ⟨rfl⟩
  letI : Finite (IsLocalRing.ResidueField K) :=
    Finite.of_surjective (IsLocalRing.residue K) IsLocalRing.residue_surjective
  letI : CharP (IsLocalRing.ResidueField K) p :=
    ((IsLocalRing.residue K).charP_iff (IsLocalRing.residue K).injective p).mp inferInstance
  letI : Finite (DualNumber K) := inferInstanceAs (Finite (K × K))
  letI : WithIdeal (DualNumber K) := ⟨IsLocalRing.maximalIdeal (DualNumber K)⟩
  letI : IsAdicComplete (IsLocalRing.maximalIdeal (DualNumber K)) (DualNumber K) :=
    finiteDualNumber_maximal_isAdicComplete K
  let σ := (GeneralLinearGroup.map (n := ι) (IsLocalRing.residue K)).comp ρ
  have hσ : Continuous σ := by
    have hmap : Continuous (GeneralLinearGroup.map (n := ι) (IsLocalRing.residue K)) := by
      apply Units.continuous_map
      apply continuous_matrix
      intro i j
      exact (continuous_of_discreteTopology : Continuous (IsLocalRing.residue K)).comp
        (continuous_apply_apply i j)
    exact hmap.comp hρ
  let eA := dualNumberOriginalResidueEquiv K
  letI : Finite (OriginalContinuousFramedFiber eA (rationalArithmeticGaloisGroup a) σ) :=
    arithmeticOriginalFramedFiber_finite rfl eA a ha p hp hpa σ hσ
  let F : {τ : MatrixFirstOrderLift ρ // Continuous τ.val} →
      OriginalContinuousFramedFiber eA (rationalArithmeticGaloisGroup a) σ := fun τ => by
    letI : TopologicalSpace (DualNumber K) :=
      (IsLocalRing.maximalIdeal (DualNumber K)).adicTopology
    refine ⟨⟨τ.val.val, (dualNumberGL_continuous_iff K τ.val.val).mpr τ.property⟩, ?_⟩
    apply MonoidHom.ext
    intro g
    apply Units.ext
    apply Matrix.ext
    intro i j
    have hτ := congrArg (fun v : GeneralLinearGroup ι K => v.val i j)
      (DFunLike.congr_fun τ.val.property g)
    exact (dualNumberOriginalResidueEquiv_reduction K ((τ.val.val g).val i j)).trans
      (congrArg (IsLocalRing.residue K) hτ)
  apply Finite.of_injective F
  intro τ υ h
  letI : TopologicalSpace (DualNumber K) :=
    (IsLocalRing.maximalIdeal (DualNumber K)).adicTopology
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun f : OriginalContinuousFramedFiber eA (rationalArithmeticGaloisGroup a) σ =>
    f.val.toMonoidHom) h

end
end Dubon2026
