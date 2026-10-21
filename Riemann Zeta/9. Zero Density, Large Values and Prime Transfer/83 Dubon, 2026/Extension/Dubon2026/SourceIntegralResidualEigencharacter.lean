import Dubon2026.SourceMinimalPrimeEigenvector
import Dubon2026.SourceIntegralReductionExtension
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! DUB-17/18 -> residual Galois association -> characteristic-zero
weight-two Hecke eigenvalue lift with its prescribed residual values.
The existing integral-reduction extension theorem removes the external
finite-residue-field and maximal-ideal extension constructions. A minimal
prime below the residual character kernel supplies an actual complex
eigenvector; finite integrality and reduction extension supply exact values.
-/

namespace Dubon2026
noncomputable section

private theorem integralEigencharacter_reduction_extension
    {T F : Type*} [CommRing T] [Field F] [IsAlgClosed F]
    (χ : T →+* integralClosure ℤ ℂ) (r : T →+* F)
    (hker : RingHom.ker χ ≤ RingHom.ker r) :
    ∃ φ : integralClosure ℤ ℂ →+* F, φ.comp χ = r := by
  let A := T ⧸ RingHom.ker χ
  let B := integralClosure ℤ ℂ
  let i : A →+* B := RingHom.kerLift χ
  letI : Algebra A B := i.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨fun b => by
    obtain ⟨p, hp, hpb⟩ := integralClosure.isIntegral (R := ℤ) (A := ℂ) b
    refine ⟨p.map (algebraMap ℤ A), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, RingHom.algebraMap_toAlgebra,
      RingHom.ext_int (i.comp (algebraMap ℤ A)) (algebraMap ℤ B)]
    exact hpb⟩
  let rA : A →+* F := Ideal.Quotient.lift _ r (fun t ht => hker ht)
  obtain ⟨φ, hφ⟩ := sourceIntegralReduction_exists_extension (RingHom.kerLift_injective χ) rA
  refine ⟨φ, ?_⟩
  ext t
  exact RingHom.congr_fun hφ (Ideal.Quotient.mk (RingHom.ker χ) t)

/-- A prescribed residue-field character of an actual finite integral
algebra acting faithfully on complex V lifts to a genuine integral
eigencharacter, an exact reduction map and a nonzero vector in that same V. -/
theorem sourceIntegralFaithfulAction_exists_residualEigencharacter
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {T : Type*} [CommRing T] [Module T V] [SMulCommClass T ℂ V]
    [FaithfulSMul T V] [Module.Finite ℤ T]
    {F : Type*} [Field F] [IsAlgClosed F] (r : T →+* F) :
    ∃ (χ : T →+* integralClosure ℤ ℂ) (φ : integralClosure ℤ ℂ →+* F)
      (x : V), x ≠ 0 ∧
      (∀ t : T, t • x = ((χ t : integralClosure ℤ ℂ) : ℂ) • x) ∧ φ.comp χ = r := by
  letI : (RingHom.ker r).IsPrime := RingHom.ker_isPrime r
  obtain ⟨p, hp, hpr⟩ := Ideal.exists_minimalPrimes_le
    (I := (⊥ : Ideal T)) (J := RingHom.ker r) bot_le
  obtain ⟨χ₀, hker, x, hx, _, _, heig⟩ :=
    sourceMinimalPrime_exists_eigenvector (K := ℂ) (V := V) (T := T) hp
  haveI : Algebra.IsIntegral ℤ T := Algebra.IsIntegral.of_finite ℤ T
  have hint (t : T) : χ₀ t ∈ integralClosure ℤ ℂ :=
    (Algebra.IsIntegral.isIntegral (R := ℤ) t).map χ₀.toIntAlgHom
  let χ : T →+* integralClosure ℤ ℂ := χ₀.codRestrict (integralClosure ℤ ℂ) hint
  have hχ : RingHom.ker χ ≤ RingHom.ker r := by
    intro t ht
    apply hpr
    rw [← hker, RingHom.mem_ker]
    exact congrArg Subtype.val (show χ t = 0 from ht)
  obtain ⟨φ, hφ⟩ := integralEigencharacter_reduction_extension χ r hχ
  exact ⟨χ, φ, x, hx, heig, hφ⟩

end
end Dubon2026
