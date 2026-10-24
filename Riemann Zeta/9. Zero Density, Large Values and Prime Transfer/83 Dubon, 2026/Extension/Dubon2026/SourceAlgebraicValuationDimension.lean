import Dubon2026.SourceAlgebraicValuationComparison
import Dubon2026.SourceRationalValuationDimension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! DUB-17/18 -> Kummer power lifting -> sum-of-genera inequality.
Every valuation of the actual algebraic constant field has dimension at
most one. Native prime-ideal/coarsening correspondence and the proved
algebraic comparison replace the general Abhyankar inequality. -/
namespace Dubon2026.SourceCurve
noncomputable section
variable {L : Type*} [Field L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L]

theorem algebraic_rat_valuation_krullDimLE_one (A : ValuationSubring L) :
    Ring.KrullDimLE 1 A := by
  let B := A.comap (algebraMap ℚ L)
  letI : Ring.KrullDimLE 1 B := Ring.krullDimLE_iff.mpr (RationalValuation.ringKrullDim_le_one B)
  have hcoarse (V : ValuationSubring L) (hAV : A ≤ V) : A = V ∨ V = ⊤ := by
    have hle : B ≤ V.comap (algebraMap ℚ L) := fun _ hx => hAV hx
    rcases ValuationSubring.eq_self_or_eq_top_of_le hle with heq | htop
    · exact Or.inl (algebraic_valuation_eq_of_le hAV heq)
    · exact Or.inr (algebraic_valuation_eq_top_of_comap_eq_top V htop)
  apply Ring.KrullDimLE.mk₁'
  intro P hP hprime
  letI : P.IsPrime := hprime
  rcases hcoarse (A.ofPrime P) (A.le_ofPrime P) with heq | htop
  · have hPmax : P = IsLocalRing.maximalIdeal A := by
      have h := A.idealOfLE_ofPrime P
      simpa only [← heq, ValuationSubring.idealOfLE_self] using h.symm
    rw [hPmax]
    infer_instance
  · have h := A.idealOfLE_ofPrime P
    have hbot : P = ⊥ := by
      simpa only [htop, ValuationSubring.idealOfLE_top] using h.symm
    exact (hP hbot).elim

theorem algebraicClosure_rat_valuation_krullDimLE_one (A : ValuationSubring (AlgebraicClosure ℚ)) :
    Ring.KrullDimLE 1 A := by
  letI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  exact algebraic_rat_valuation_krullDimLE_one A

end
end Dubon2026.SourceCurve
