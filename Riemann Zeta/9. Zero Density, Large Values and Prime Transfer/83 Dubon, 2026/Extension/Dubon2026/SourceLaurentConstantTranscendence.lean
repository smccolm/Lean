import Dubon2026.SourceTranscendentalConstantAlgebraV2
import Dubon2026.SourceLaurentIntegralDescent

/-! DUB-17/18 -> actual Gamma1 character realization -> differential/cusp
comparison -> rational Fourier spanning -> Fricke integral base change.
A transcendental complex constant remains transcendental over a Laurent
subfield whose coefficients lie in the original constant field. Taking each
Laurent coefficient of a polynomial relation reduces it to a polynomial over
the original constants. This discharges the relative-transcendence premise
of the constant-adjoining descent for the actual cyclotomic Fricke series. -/
namespace Dubon2026.SourceFricke.ConstantDescent
noncomputable section
open Polynomial
open Dubon2026.SourceFunctionField

theorem constant_transcendental_of_coeff_mem
    (F : IntermediateField ℚ ℂ) (E : Subfield (LaurentSeries ℂ))
    (hE : ∀ z ∈ E, ∀ m : ℤ, z.coeff m ∈ F)
    {c : ℂ} (hc : Transcendental ↥F c) :
    Transcendental ↥E (algebraMap ℂ (LaurentSeries ℂ) c) := by
  classical
  rw [transcendental_iff]
  intro P hP
  ext i : 1
  apply Subtype.ext
  ext m
  simp only [Polynomial.coeff_zero, ZeroMemClass.coe_zero, HahnSeries.coeff_zero]
  let d := P.natDegree + 1
  by_cases hi : i < d
  · let a : ℕ → F := fun k => ⟨((P.coeff k : E) : LaurentSeries ℂ).coeff m,
      hE _ (P.coeff k).property m⟩
    let Q : Polynomial F := ∑ k ∈ Finset.range d, Polynomial.C (a k) * Polynomial.X ^ k
    have hterm : ∀ k : ℕ,
        ((algebraMap E (LaurentSeries ℂ) (P.coeff k)) *
          (algebraMap ℂ (LaurentSeries ℂ) c) ^ k).coeff m = (a k : ℂ) * c ^ k := by
      intro k
      rw [← map_pow, mul_comm, SourceDifferential.algebraMap_laurentSeries_apply_alt,
        HahnSeries.coeff_single_zero_mul, mul_comm]
      rfl
    have hcoeff := congrArg (fun z : LaurentSeries ℂ => z.coeff m) hP
    dsimp only at hcoeff
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, HahnSeries.coeff_sum,
      HahnSeries.coeff_zero] at hcoeff
    have heval : Polynomial.aeval c Q = 0 := by
      rw [Polynomial.aeval_def]
      simp only [Q, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul,
        Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X]
      exact (Finset.sum_congr rfl fun k _ => hterm k).symm.trans hcoeff
    have hQ : Q = 0 := (transcendental_iff.mp hc) Q heval
    have ha : a i = 0 := by
      have h := congrArg (fun q : Polynomial F => q.coeff i) hQ
      simpa [Q, Polynomial.coeff_sum, Polynomial.coeff_C_mul_X_pow, Finset.mem_range.mpr hi] using h
    exact congrArg (fun z : F => (z : ℂ)) ha
  · have hp : P.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp only [hp, ZeroMemClass.coe_zero, HahnSeries.coeff_zero]

end
end Dubon2026.SourceFricke.ConstantDescent