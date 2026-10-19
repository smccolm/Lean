import Dubon2026.ArithmeticSymmetricRegularPrimes
import Dubon2026.ArithmeticTraceCocycleDetection

/-! Regularity and original trace-cocycle detection at the same auxiliary
prime. The symmetric residual image supplies the regular root-fixing
element; the remaining input is a scalar-kernel cocycle value paired
nontrivially with a commuting trace-zero matrix. -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField MatrixGroups

/-- Nonzero scalar multiplication preserves the distinct diagonal weights. -/
theorem diagonal_smul_charpoly_separable {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] (w : ι → K) (hw : Function.Injective w)
    (d : K) (hd : d ≠ 0) : (d • Matrix.diagonal w).charpoly.Separable := by
  rw [← Matrix.diagonal_smul, Matrix.charpoly_diagonal]
  apply Polynomial.separable_prod_X_sub_C_iff.mpr
  intro i j hij
  apply hw
  exact mul_left_cancel₀ hd hij

/-- The scalar kernel translate in the detecting-cocycle argument retains
regularity of the literal symmetric diagonal residual matrix. -/
theorem symmetric_scalar_translate_charpoly_separable
    {G K : Type} [Group G] [Field K] (degree : ℕ)
    (ρ : G →* GeneralLinearGroup (Fin (degree + 1)) K)
    (g τ : G) (u : Kˣ) (hu : 2 * degree < orderOf u)
    (hg : ρ g = homogeneousSymmetricGL degree
      (Matrix.SpecialLinearGroup.toGL (ringSL2UnitDiagonal u)))
    (d : K) (hτ : (ρ τ).val = d • (1 : Matrix (Fin (degree + 1)) (Fin (degree + 1)) K)) :
    (ρ (τ * g)).val.charpoly.Separable := by
  have hd : d ≠ 0 := by
    intro hd
    have hz : (ρ τ).val = 0 := by rw [hτ, hd, zero_smul]
    exact Units.ne_zero (ρ τ) hz
  rw [map_mul, Units.val_mul, hτ, hg, homogeneousSymmetricGL_unitDiagonal,
    smul_mul_assoc, one_mul]
  exact diagonal_smul_charpoly_separable _ (symmetric_unit_weights_injective u degree hu) d hd

/-- A sufficiently large actual symmetric SL2 image removes the regular
root-fixing witness from trace-cocycle prime selection. Scalar kernel test
data still remain explicit; the selected prime has nonzero native local
H1 restriction and a regular original local residual image simultaneously. -/
theorem rationalArithmetic_symmetric_trace_exists_detecting_regular_prime
    (a : 𝓞 ℚ) (ha : a ≠ 0) (q degree level : ℕ) [Fact q.Prime]
    [NeZero (2 : ZMod q)] [NeZero (3 : ZMod q)]
    (hqa : (q : 𝓞 ℚ) ∣ a) (hsize : 2 * degree < Nat.card (ZMod q) - 1)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin (degree + 1)) (ZMod q))
    (hρ : Continuous ρ)
    (himage : ((homogeneousSymmetricGL (R := ZMod q) degree).comp
      Matrix.SpecialLinearGroup.toGL).range ≤ ρ.range)
    (c : continuousRepresentationCocyclesOne (matrixTraceZeroCharacterRep ρ
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)) :
    let U := rationalUnramifiedExtension a
    letI : Algebra ℚ U := U.algebra'
    letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
    ∃ ζ : U, IsPrimitiveRoot ζ (q ^ (level + 1)) ∧
      ∃ g : Gal(U/ℚ), g ζ = ζ ∧ (ρ g).val.charpoly.Separable ∧
        ∀ τ : Gal(U/ℚ), τ ζ = ζ →
          ∀ d : ZMod q, (ρ τ).val = d • (1 : Matrix (Fin (degree + 1)) (Fin (degree + 1)) (ZMod q)) →
            ∀ M : matrixTraceZeroSubmodule (Fin (degree + 1)) (ZMod q),
              (ρ g).val * M.val = M.val * (ρ g).val →
              Matrix.trace ((c.val τ).val * M.val) ≠ 0 →
              ∀ S : Finset ℕ, ∃ p : ℕ, ∃ hp : p.Prime,
                p ∉ S ∧ ¬ (p : 𝓞 ℚ) ∣ a ∧ p ≡ 1 [MOD q ^ level] ∧
                (∃ γ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp),
                  (ρ (rationalPrimeArithmeticRestriction a p hp γ)).val.charpoly.Separable) ∧
                rationalPrimeCyclotomicAdjointH1Restriction a q hqa p hp ρ hρ
                  (Submodule.Quotient.mk c) ≠ 0 := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
  have hprime := rationalArithmetic_trace_exists_detecting_prime a q hqa ρ hρ
  have hprime' := hprime ha level c
  obtain ⟨ζ, hζ, hF⟩ := hprime'
  have hregulars := galois_exists_root_fixing_symmetric_regular
    (F := ℚ) (Ω := U) (K := ZMod q) degree hsize ρ himage
    (m := q ^ (level + 1)) (ζ := ζ)
  have hregularζ := hregulars hζ
  obtain ⟨u, hu, g, hg, hdiag, hregular⟩ := hregularζ
  refine ⟨ζ, hζ, g, hg, hregular, ?_⟩
  intro τ hτ d hscalar M hM hc S
  have hselected := hF g τ hg hτ d hscalar
  have hselected' := hselected M hM hc S
  obtain ⟨p, hp, hpS, hpa, hmod, ⟨γ, hγ⟩, hne⟩ := hselected'
  refine ⟨p, hp, hpS, hpa, hmod, ⟨γ, ?_⟩, hne⟩
  rcases hγ with hγ | hγ
  · rw [generalLinearGroup_charpoly_eq_of_isConj hγ]
    exact hregular
  · rw [generalLinearGroup_charpoly_eq_of_isConj hγ]
    apply symmetric_scalar_translate_charpoly_separable degree ρ g τ u _ hdiag d hscalar
    rwa [hu]

end
end Dubon2026
