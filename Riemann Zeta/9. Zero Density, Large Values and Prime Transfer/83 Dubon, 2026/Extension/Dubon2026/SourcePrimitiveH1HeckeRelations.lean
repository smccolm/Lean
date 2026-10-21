import Dubon2026.SourceBinaryH1HeckeAlgebra
import Dubon2026.SourceComplexBinaryH1Span
import Dubon2026.SourceHeckeWordTransport

/-! Original primitive Fourier eigenvalues satisfy every integral H1 Hecke relation.
DUB-17/18 -> residual modular Galois association -> residual H1 eigensystem
-> integral H1 Hecke character. Integral relations extend to complex H1 by
the proved spanning theorem and are evaluated on the actual nonzero
primitive period class.
-/

namespace Dubon2026
noncomputable section

variable {Q : ℕ} [NeZero Q] {k : ℤ}

/-- Every actual integral H1 Hecke relation vanishes at the original primitive Fourier eigenvalues. -/
theorem sourcePrimitiveH1Hecke_relation (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (a : FreeAlgebra ℤ (sourceBinaryHeckePrime Q))
    (ha : FreeAlgebra.lift ℤ (sourceBinaryH1PrimeOperators ℤ Q (k - 2).toNat) a = 0) :
    FreeAlgebra.lift ℤ (fun p : sourceBinaryHeckePrime Q => cuspCoefficients f.toCuspForm p.val) a = 0 := by
  let w := (k - 2).toNat
  let Φ := (sourceBinaryH1Change (Int.castRingHom ℂ) Q w).toAddMonoidHom
  have hΦ (p : sourceBinaryHeckePrime Q)
      (x : groupCohomology.H1 (sourceBinaryCoefficientRep ℤ Q w)) :
      Φ (sourceBinaryH1PrimeOperators ℤ Q w p x) =
        sourceBinaryH1PrimeOperators ℂ Q w p (Φ x) :=
    sourceBinaryH1PrimeOperators_change Q w p x
  have hc : FreeAlgebra.lift ℤ (sourceBinaryH1PrimeOperators ℂ Q w) a = 0 := by
    apply sourceComplexBinaryH1_end_zero_of_integer Q w
    intro x
    change FreeAlgebra.lift ℤ (sourceBinaryH1PrimeOperators ℂ Q w) a (Φ x) = 0
    rw [← sourceHeckeWord_intertwine _ _ Φ hΦ a x, ha, LinearMap.zero_apply, map_zero]
  obtain ⟨hne, heig⟩ := sourcePrimitive_nonzero_integralModelComplexEigensystem f hk
  have h := sourceHeckeWord_eigenvector (sourceBinaryH1PrimeOperators ℂ Q w)
    (fun p : sourceBinaryHeckePrime Q => cuspCoefficients f.toCuspForm p.val)
    (sourceOriginalBinaryPeriodCohomology Q k hk f.toCuspForm)
    (fun p => heig p.val p.property.1 p.property.2) a
  rw [hc, LinearMap.zero_apply] at h
  exact (smul_eq_zero.mp h.symm).resolve_right hne

/-- The original primitive form supplies a character of the actual integral H1 Hecke algebra,
with every good-prime value equal to its original Fourier coefficient. -/
theorem sourcePrimitive_exists_H1HeckeCharacter (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) :
    ∃ χ : sourceBinaryH1HeckeAlgebra Q (k - 2).toNat →ₐ[ℤ] ℂ,
      ∀ p : sourceBinaryHeckePrime Q,
        χ ⟨sourceBinaryH1PrimeOperators ℤ Q (k - 2).toNat p,
          Algebra.subset_adjoin ⟨p, rfl⟩⟩ = cuspCoefficients f.toCuspForm p.val :=
  sourceHeckeWord_exists_character (sourceBinaryH1PrimeOperators ℤ Q (k - 2).toNat)
    (fun p : sourceBinaryHeckePrime Q => cuspCoefficients f.toCuspForm p.val)
    (sourcePrimitiveH1Hecke_relation f hk)

end
end Dubon2026
