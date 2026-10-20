/-
Selected period transformation proofs adapted from the Tau Ceti contributors,
TauCetiProject/TauCeti 199786c594817a82fdd2fab04d3ae4cc5eb837d5.
Copyright (c) 2026 The Tau Ceti contributors. Apache-2.0.
-/
import Dubon2026.SourcePeriodIntegrand
import Dubon2026.SourceModularBinaryForms

/-! The analytic period integral uses the existing integral coefficient action.
The exact dependency is DUB-17/18 -> modular Galois association -> integral
Hecke finiteness -> an injective, Hecke-adjoint period pairing. The identities
below identify polynomial substitution with the already proved representation,
so that periods respect the actual modular-symbol relation.
-/

namespace Dubon2026
noncomputable section
open Matrix Matrix.SpecialLinearGroup MvPolynomial MulOpposite
open UpperHalfPlane
open scoped MatrixGroups ModularForm
variable {R : Type*} [CommRing R] [Algebra R ℂ] {w : ℕ}

/-- Evaluation of the original coefficient action is actual integral row substitution. -/
theorem sourceModularBinaryFormRep_aeval (M : Matrix (Fin 2) (Fin 2) ℤ)
    (P : homogeneousSubmodule (Fin 2) R w) (v : Fin 2 → ℂ) :
    aeval v (sourceModularBinaryFormRep R w (op M) P).val =
      aeval ((M.map (Int.cast : ℤ → ℂ)) *ᵥ v) P.val := by
  rw [sourceModularBinaryFormRep_apply]
  have h : (aeval v).comp (matrixPolynomialAction (M.map (Int.castRingHom R))ᵀ) =
      aeval ((M.map (Int.cast : ℤ → ℂ)) *ᵥ v) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [matrixPolynomialAction_X, Algebra.smul_def]
  exact AlgHom.congr_fun h P.val

namespace SourceModularSymbols
variable {F : Type*} [FunLike F ℍ ℂ] {k : ℤ}

/-- The actual weight-two integrand transforms by the existing integral right action. -/
theorem periodIntegrand_slash_mapGL {k : ℤ} (hk : k = w + 2) (f : ℍ → ℂ)
    (P : homogeneousSubmodule (Fin 2) R w) (γ : SL(2, ℤ)) :
    periodIntegrand f P ∣[(2 : ℤ)] (mapGL ℚ γ) =
      periodIntegrand (f ∣[k] γ)
        (sourceModularBinaryFormRep R w (op (γ : Matrix (Fin 2) (Fin 2) ℤ)) P) := by
  have hdet : ((mapGL ℚ γ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, det_mapGL, Units.val_one]
  funext τ
  rw [periodIntegrand_slash_apply hk f P (by rw [hdet]; exact one_pos) τ,
    periodIntegrand_apply, hdet, sourceRat_slash_mapGL, ← sourceSL_coe_eq_mapGL,
    ← ModularForm.SL_slash, map_mapGL, sourceModularBinaryFormRep_aeval]
  push_cast
  rw [one_zpow, one_mul]
  congr 2
  ext i
  fin_cases i <;>
    simp [num, denom, mapGL_coe_matrix, Matrix.map_apply]

/-- **The transformation law of the periods under `SL(2, ℤ)`**:
`∫_{γ g • 0}^{γ g • ∞} f(z) P(z, 1) dz = ∫_{g • 0}^{g • ∞} (f ∣[k] γ)(z) (P ∣ γ)(z, 1) dz`,
the substitution `z ↦ γ • z` in the period integral. The identity holds for every rational `g`
(it is `sourceGeodesicIntegral_mul` and the transformation law of the
integrand); both sides are period integrals along geodesics when `0 < det g`. -/
theorem geodesicIntegral_mapGL_mul_periodIntegrand {k : ℤ} (hk : k = w + 2) (f : ℍ → ℂ)
    (P : homogeneousSubmodule (Fin 2) R w) (γ : SL(2, ℤ)) (g : GL (Fin 2) ℚ) :
    sourceGeodesicIntegral (mapGL ℚ γ * g) (periodIntegrand f P) =
      sourceGeodesicIntegral g
        (periodIntegrand (f ∣[k] γ) (sourceModularBinaryFormRep R w (op (γ : Matrix (Fin 2) (Fin 2) ℤ)) P)) := by
  rw [sourceGeodesicIntegral_mul, periodIntegrand_slash_mapGL hk]

/-- **The periods of a form respect the modular-symbol relation**: for `γ` in the level `Γ` of a
slash-invariant `f`,
`∫_{γ g • 0}^{γ g • ∞} f(z) P(z, 1) dz = ∫_{g • 0}^{g • ∞} f(z) (P ∣ γ)(z, 1) dz`, the analytic
counterpart of `{γα, γβ} ⊗ P = {α, β} ⊗ (P ∣ γ)` in `𝕄_w(Γ; R)`. As for
`geodesicIntegral_mapGL_mul_periodIntegrand`, the identity holds for every rational `g`, and both
sides are period integrals along geodesics when `0 < det g`. -/
theorem geodesicIntegral_mapGL_mul_periodIntegrand_of_mem {Γ : Subgroup SL(2, ℤ)}
    [SlashInvariantFormClass F (Γ.map (mapGL ℝ)) k] (f : F) (hk : k = w + 2)
    (P : homogeneousSubmodule (Fin 2) R w) {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (g : GL (Fin 2) ℚ) :
    sourceGeodesicIntegral (mapGL ℚ γ * g) (periodIntegrand f P) =
      sourceGeodesicIntegral g
        (periodIntegrand f (sourceModularBinaryFormRep R w (op (γ : Matrix (Fin 2) (Fin 2) ℤ)) P)) := by
  rw [geodesicIntegral_mapGL_mul_periodIntegrand hk, ModularForm.SL_slash,
    sourceSL_coe_eq_mapGL,
    SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ)]

/-- **The periods between cusps respect the modular-symbol relation**: for `γ` in the level `Γ`
of a slash-invariant `f` and cusps `α`, `β`,
`∫_{γβ}^{γα} f(z) P(z, 1) dz = ∫_β^α f(z) (P ∣ γ)(z, 1) dz`, the analytic counterpart of
`{γα, γβ} ⊗ P = {α, β} ⊗ (P ∣ γ)` in `𝕄_w(Γ; R)` (`TauCeti.ModularSymbols.symbol_mapGL_smul`). -/
theorem sourceCuspIntegral_periodIntegrand_mapGL_smul_of_mem {Γ : Subgroup SL(2, ℤ)}
    [SlashInvariantFormClass F (Γ.map (mapGL ℝ)) k] (f : F) (hk : k = w + 2)
    (P : homogeneousSubmodule (Fin 2) R w) {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (α β : OnePoint ℚ) :
    sourceCuspIntegral (periodIntegrand f P) (mapGL ℚ γ • β) (mapGL ℚ γ • α) =
      sourceCuspIntegral
        (periodIntegrand f (sourceModularBinaryFormRep R w (op (γ : Matrix (Fin 2) (Fin 2) ℤ)) P)) β α := by
  have hdet : 0 < ((mapGL ℚ γ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, det_mapGL, Units.val_one]
    exact one_pos
  rw [← sourceCuspIntegral_slash _ hdet, periodIntegrand_slash_mapGL hk, ModularForm.SL_slash,
    sourceSL_coe_eq_mapGL,
    SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ)]

/-! ### The transformation law under integral matrices -/

/-- **The transformation law under integral matrices of positive determinant.** For a rational
matrix `g` with integral entries `A` and `0 < det g`, slashing the integrand of `f` against
`P ∣ adj A` in weight `2` by `g` gives the integrand of `f ∣[k] g` against `P`: the adjugate sends
`(aτ + b, cτ + d)` to `det g • (τ, 1)`, and the resulting factor `(det g)ʷ` cancels the
`(det g)⁻ʷ` of `periodIntegrand_slash_apply`. On `SL(2, ℤ)` the adjugate is the inverse, and this
is `periodIntegrand_slash_mapGL` read backwards. -/
theorem periodIntegrand_adjugate_slash {k : ℤ} (hk : k = w + 2) (f : ℍ → ℂ)
    (P : homogeneousSubmodule (Fin 2) R w) {g : GL (Fin 2) ℚ} {A : Matrix (Fin 2) (Fin 2) ℤ}
    (hA : (g : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det) :
    periodIntegrand f (sourceModularBinaryFormRep R w (op (adjugate A)) P) ∣[(2 : ℤ)] g =
      periodIntegrand (f ∣[k] g) P := by
  funext τ
  set g' := Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g with hg'
  -- the adjugate sends `(aτ + b, cτ + d)` to `det g • (τ, 1)`
  have hvec : (adjugate A).map (Int.cast : ℤ → ℂ) *ᵥ
      ![num g' τ, denom g' τ] = ((g : Matrix (Fin 2) (Fin 2) ℚ).det : ℂ) • ![(τ : ℂ), 1] := by
    have hent (i j : Fin 2) : ((g' i j : ℝ) : ℂ) = ((A i j : ℤ) : ℂ) := by
      simp [hg', hA]
    rw [hA, det_fin_two]
    ext i
    fin_cases i <;>
      simp [adjugate_fin_two, num, denom, mulVec, dotProduct, Fin.sum_univ_two, hent] <;> ring
  rw [periodIntegrand_slash_apply hk f _ hg τ, periodIntegrand_apply, sourceModularBinaryFormRep_aeval, ← hg', hvec, sourceHomogeneous_aeval_smul ((mem_homogeneousSubmodule w _).mp P.2),
    smul_eq_mul, zpow_neg, zpow_natCast]
  have hD : ((g : Matrix (Fin 2) (Fin 2) ℚ).det : ℂ) ≠ 0 := by
    exact_mod_cast hg.ne'
  field_simp [hD]

/-- **The substitution `z ↦ g • z` for integral matrices of positive determinant**: for a rational
matrix `g` with integral entries `A` and `0 < det g`,
`∫_β^α (f ∣[k] g)(z) P(z, 1) dz = ∫_{gβ}^{gα} f(z) (P ∣ adj A)(z, 1) dz`. Since the symbol
`{α, β} ⊗ P` pairs to `∫_β^α f(z) P(z, 1) dz`, this says that slashing a form by `g` is adjoint to
the action `{α, β} ⊗ P ↦ {gα, gβ} ⊗ (P ∣ adj A)` of `g` on modular symbols. -/
theorem sourceCuspIntegral_periodIntegrand_slash {k : ℤ} (hk : k = w + 2) (f : ℍ → ℂ)
    (P : homogeneousSubmodule (Fin 2) R w) {g : GL (Fin 2) ℚ} {A : Matrix (Fin 2) (Fin 2) ℤ}
    (hA : (g : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det) (α β : OnePoint ℚ) :
    sourceCuspIntegral (periodIntegrand (f ∣[k] g) P) β α =
      sourceCuspIntegral (periodIntegrand f (sourceModularBinaryFormRep R w (op (adjugate A)) P)) (g • β)
        (g • α) := by
  rw [← periodIntegrand_adjugate_slash hk f P hA hg, sourceCuspIntegral_slash _ hg]

end SourceModularSymbols
end
end Dubon2026
