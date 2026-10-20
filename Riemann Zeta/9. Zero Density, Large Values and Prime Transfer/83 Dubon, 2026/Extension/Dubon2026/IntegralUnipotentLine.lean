import Dubon2026.IntegralWeightUnitriangularCell
import Dubon2026.IntegralDominantHighestLine

/-! Uniqueness of the actual source unipotent invariant line.
The original induced module's lower-unitriangular invariants are its
explicit dominant line. Longest translation identifies upper-unitriangular
invariants with the exact highest line, without assuming a torus character.
This is the invariant-line input to characteristic-zero irreducibility.
-/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable (R : Type u) [CommRing R] [IsDomain R] (n : ℕ) (lam : Fin n → ℤ)

/-- Two original induced functions invariant under every lower-unitriangular coefficient-algebra point agree if their identity values agree. -/
theorem integralInduced_opposite_unipotent_ext
    (p q : generalLinearIntegralInducedSubmodule R n lam)
    (hp : ∀ (A : Type u) [CommRing A] [Algebra R A]
      (g : GeneralLinearGroup (Fin n) A) (b : generalLinearBorel A n),
        (∀ i, generalLinearBorelDiagonalUnit b i = 1) →
          generalLinearRegularEval (g * integralWeightTranspose b.val) p.val =
            generalLinearRegularEval g p.val)
    (hq : ∀ (A : Type u) [CommRing A] [Algebra R A]
      (g : GeneralLinearGroup (Fin n) A) (b : generalLinearBorel A n),
        (∀ i, generalLinearBorelDiagonalUnit b i = 1) →
          generalLinearRegularEval (g * integralWeightTranspose b.val) q.val =
            generalLinearRegularEval g q.val)
    (he : generalLinearRegularEval (1 : GeneralLinearGroup (Fin n) R) p.val =
      generalLinearRegularEval (1 : GeneralLinearGroup (Fin n) R) q.val) : p = q := by
  let S := GeneralLinearRegularFunctions R n
  let F := FractionRing S
  let f : S →ₐ[R] F := IsScalarTower.toAlgHom R S F
  apply Subtype.ext
  apply IsFractionRing.injective S F
  change f p.val = f q.val
  rw [← generalLinearRegularEval_map_generic f]
  obtain ⟨b, c, hcell, hc⟩ := integralWeightGeneric_fraction_unitriangularCell R n
  change generalLinearRegularEval
      (GeneralLinearGroup.map (algebraMap S F) (generalLinearRegularGeneric R n)) p.val =
    generalLinearRegularEval
      (GeneralLinearGroup.map (algebraMap S F) (generalLinearRegularGeneric R n)) q.val
  rw [hcell, p.property F (integralWeightTranspose c.val) b,
    q.property F (integralWeightTranspose c.val) b]
  have hpc := hp F 1 c hc
  have hqc := hq F 1 c hc
  simp only [one_mul] at hpc hqc
  rw [hpc, hqc, integralWeight_eval_one_baseChange R n F p.val,
    integralWeight_eval_one_baseChange R n F q.val, he]

/-- Every actual lower-unitriangular invariant in the literal source induction is its identity-value multiple of the original dominant vector; no weight-character premise is needed. -/
theorem integralInduced_opposite_unipotent_eq_dominant {m : ℕ}
    (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam)
    (p : generalLinearIntegralInducedSubmodule R (m + 1) lam)
    (hp : ∀ (A : Type u) [CommRing A] [Algebra R A]
      (g : GeneralLinearGroup (Fin (m + 1)) A) (b : generalLinearBorel A (m + 1)),
        (∀ i, generalLinearBorelDiagonalUnit b i = 1) →
          generalLinearRegularEval (g * integralWeightTranspose b.val) p.val =
            generalLinearRegularEval g p.val) :
    p.val = generalLinearRegularEval (1 : GeneralLinearGroup (Fin (m + 1)) R) p.val •
      integralDominantInducedVector R lam := by
  let c := generalLinearRegularEval (1 : GeneralLinearGroup (Fin (m + 1)) R) p.val
  let q : generalLinearIntegralInducedSubmodule R (m + 1) lam :=
    ⟨c • integralDominantInducedVector R lam,
      (generalLinearIntegralInducedSubmodule R (m + 1) lam).smul_mem c
        (integralDominantInducedVector_mem R lam hlam)⟩
  have hq : ∀ (A : Type u) [CommRing A] [Algebra R A]
      (g : GeneralLinearGroup (Fin (m + 1)) A) (b : generalLinearBorel A (m + 1)),
        (∀ i, generalLinearBorelDiagonalUnit b i = 1) →
          generalLinearRegularEval (g * integralWeightTranspose b.val) q.val =
            generalLinearRegularEval g q.val := by
    intro A _ _ g b hb
    have hchar : generalLinearBorelWeight lam b = 1 := by
      simp only [generalLinearBorelWeight_apply, hb, one_zpow, Finset.prod_const_one]
    change generalLinearRegularEval (g * integralWeightTranspose b.val)
      (c • integralDominantInducedVector R lam) =
        generalLinearRegularEval g (c • integralDominantInducedVector R lam)
    simp only [Algebra.smul_def, map_mul, AlgHom.commutes,
      integralDominantInducedVector_right_transpose_borel lam hlam,
      hchar, Units.val_one, one_mul]
  have he : generalLinearRegularEval (1 : GeneralLinearGroup (Fin (m + 1)) R) p.val =
      generalLinearRegularEval (1 : GeneralLinearGroup (Fin (m + 1)) R) q.val := by
    simp only [q, map_smul, integralDominantInducedVector_one, smul_eq_mul, mul_one]
    rfl
  exact congrArg Subtype.val (integralInduced_opposite_unipotent_ext R (m + 1) lam p q hp hq he)

/-- Every upper-unitriangular invariant in the original source induction is the longest-value multiple of the original highest vector, without a supplied highest-weight character. -/
theorem integralInduced_unipotent_eq_highest {m : ℕ}
    (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam)
    (q : generalLinearIntegralInducedSubmodule R (m + 1) lam)
    (hq : ∀ (A : Type u) [CommRing A] [Algebra R A]
      (g : GeneralLinearGroup (Fin (m + 1)) A) (b : generalLinearBorel A (m + 1)),
        (∀ i, generalLinearBorelDiagonalUnit b i = 1) →
          generalLinearRegularEval (g * b.val) q.val = generalLinearRegularEval g q.val) :
    q = generalLinearRegularEval (integralWeightLongest R (m + 1)) q.val •
      integralDominantHighestVector R lam hlam := by
  let W := integralWeightLongest R (m + 1)
  let p : generalLinearIntegralInducedSubmodule R (m + 1) lam :=
    ⟨generalLinearRegularRightTranslate W q.val,
      generalLinearIntegralInducedSubmodule_stable R (m + 1) lam W q.property⟩
  have hpu : ∀ (A : Type u) [CommRing A] [Algebra R A]
      (g : GeneralLinearGroup (Fin (m + 1)) A) (b : generalLinearBorel A (m + 1)),
        (∀ i, generalLinearBorelDiagonalUnit b i = 1) →
          generalLinearRegularEval (g * integralWeightTranspose b.val) p.val =
            generalLinearRegularEval g p.val := by
    intro A _ _ g b hb
    have hl := AlgHom.congr_fun (generalLinearRegularEval_rightTranslate W
      (g * integralWeightTranspose b.val)) q.val
    have hr := AlgHom.congr_fun (generalLinearRegularEval_rightTranslate W g) q.val
    simp only [AlgHom.comp_apply, W, integralWeightLongest_map] at hl hr
    change generalLinearRegularEval (g * integralWeightTranspose b.val)
      (generalLinearRegularRightTranslate W q.val) =
        generalLinearRegularEval g (generalLinearRegularRightTranslate W q.val)
    rw [hl, hr, mul_assoc, integralWeightLongestBorel_transport, ← mul_assoc]
    exact hq A (g * integralWeightLongest A (m + 1))
      (integralWeightLongestBorel A (m + 1) b) (fun i => by
        rw [integralWeightLongestBorel_diagonal, hb])
  have hp := integralInduced_opposite_unipotent_eq_dominant R lam hlam p hpu
  have he : generalLinearRegularEval (1 : GeneralLinearGroup (Fin (m + 1)) R) p.val =
      generalLinearRegularEval W q.val := by
    have h := AlgHom.congr_fun (generalLinearRegularEval_rightTranslate W
      (1 : GeneralLinearGroup (Fin (m + 1)) R)) q.val
    simpa only [AlgHom.comp_apply, W, integralWeightLongest_map, one_mul] using h
  rw [he] at hp
  have ht := congrArg (generalLinearRegularRightTranslate W) hp
  have hWW : (generalLinearRegularRightTranslate W).comp
      (generalLinearRegularRightTranslate W) =
        AlgHom.id R (GeneralLinearRegularFunctions R (m + 1)) := by
    rw [← generalLinearRegularRightTranslate_mul,
      integralWeightLongest_mul_self, generalLinearRegularRightTranslate_one]
  have hqq : generalLinearRegularRightTranslate W p.val = q.val :=
    AlgHom.congr_fun hWW q.val
  rw [hqq] at ht
  apply Subtype.ext
  change q.val = generalLinearRegularEval W q.val • integralDominantHighestRegular R lam
  simpa only [Algebra.smul_def, map_mul, AlgHom.commutes,
    W, integralDominantHighestRegular] using ht

end
end Dubon2026
