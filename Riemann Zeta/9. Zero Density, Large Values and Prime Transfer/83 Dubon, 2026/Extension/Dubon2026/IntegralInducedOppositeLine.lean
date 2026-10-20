import Dubon2026.IntegralWeightBorelOpenCell

/-! Faithful evaluation of the original opposite-weight line.
The all-algebra source covariance and the proved generic open-cell
factorization show that a function on this line is determined by its
identity value. This is the uniqueness input for the actual highest line.
-/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable (R : Type u) [CommRing R] [IsDomain R] (n : ℕ) (lam : Fin n → ℤ)

omit [IsDomain R] in
/-- Identity evaluation of the original regular function commutes with actual coefficient extension. -/
theorem integralWeight_eval_one_baseChange
    (A : Type u) [CommRing A] [Algebra R A] (p : GeneralLinearRegularFunctions R n) :
    generalLinearRegularEval (1 : GeneralLinearGroup (Fin n) A) p =
      algebraMap R A (generalLinearRegularEval (1 : GeneralLinearGroup (Fin n) R) p) := by
  have h := AlgHom.congr_fun (generalLinearRegularEval_natural
    (Algebra.ofId R A) (1 : GeneralLinearGroup (Fin n) R)) p
  simpa only [AlgHom.comp_apply, map_one, Algebra.ofId_apply] using h.symm

/-- Two original induced functions with the same opposite-Borel character agree if their original identity values agree. -/
theorem integralInduced_opposite_character_ext
    (p q : generalLinearIntegralInducedSubmodule R n lam)
    (hp : ∀ (A : Type u) [CommRing A] [Algebra R A]
      (g : GeneralLinearGroup (Fin n) A) (b : generalLinearBorel A n),
        generalLinearRegularEval (g * integralWeightTranspose b.val) p.val =
          (generalLinearBorelWeight lam b : A) * generalLinearRegularEval g p.val)
    (hq : ∀ (A : Type u) [CommRing A] [Algebra R A]
      (g : GeneralLinearGroup (Fin n) A) (b : generalLinearBorel A n),
        generalLinearRegularEval (g * integralWeightTranspose b.val) q.val =
          (generalLinearBorelWeight lam b : A) * generalLinearRegularEval g q.val)
    (he : generalLinearRegularEval (1 : GeneralLinearGroup (Fin n) R) p.val =
      generalLinearRegularEval (1 : GeneralLinearGroup (Fin n) R) q.val) : p = q := by
  let S := GeneralLinearRegularFunctions R n
  let F := FractionRing S
  let f : S →ₐ[R] F := IsScalarTower.toAlgHom R S F
  apply Subtype.ext
  apply IsFractionRing.injective S F
  change f p.val = f q.val
  rw [← generalLinearRegularEval_map_generic f]
  obtain ⟨b, c, hcell⟩ := integralWeightGeneric_fraction_openCell R n
  change generalLinearRegularEval
      (GeneralLinearGroup.map (algebraMap S F) (generalLinearRegularGeneric R n)) p.val =
    generalLinearRegularEval
      (GeneralLinearGroup.map (algebraMap S F) (generalLinearRegularGeneric R n)) q.val
  rw [hcell, p.property F (integralWeightTranspose c.val) b,
    q.property F (integralWeightTranspose c.val) b]
  have hpc := hp F 1 c
  have hqc := hq F 1 c
  simp only [one_mul] at hpc hqc
  rw [hpc, hqc, integralWeight_eval_one_baseChange R n F p.val,
    integralWeight_eval_one_baseChange R n F q.val, he]

/-- Every original induced function of the required opposite character is the identity-value multiple of the explicitly constructed dominant minor vector. -/
theorem integralInduced_opposite_character_eq_dominant {m : ℕ}
    (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam)
    (p : generalLinearIntegralInducedSubmodule R (m + 1) lam)
    (hp : ∀ (A : Type u) [CommRing A] [Algebra R A]
      (g : GeneralLinearGroup (Fin (m + 1)) A) (b : generalLinearBorel A (m + 1)),
        generalLinearRegularEval (g * integralWeightTranspose b.val) p.val =
          (generalLinearBorelWeight lam b : A) * generalLinearRegularEval g p.val) :
    p.val = generalLinearRegularEval (1 : GeneralLinearGroup (Fin (m + 1)) R) p.val •
      integralDominantInducedVector R lam := by
  let c := generalLinearRegularEval (1 : GeneralLinearGroup (Fin (m + 1)) R) p.val
  let q : generalLinearIntegralInducedSubmodule R (m + 1) lam :=
    ⟨c • integralDominantInducedVector R lam,
      (generalLinearIntegralInducedSubmodule R (m + 1) lam).smul_mem c
        (integralDominantInducedVector_mem R lam hlam)⟩
  have hq : ∀ (A : Type u) [CommRing A] [Algebra R A]
      (g : GeneralLinearGroup (Fin (m + 1)) A) (b : generalLinearBorel A (m + 1)),
        generalLinearRegularEval (g * integralWeightTranspose b.val) q.val =
          (generalLinearBorelWeight lam b : A) * generalLinearRegularEval g q.val := by
    intro A _ _ g b
    change generalLinearRegularEval (g * integralWeightTranspose b.val)
      (c • integralDominantInducedVector R lam) =
        (generalLinearBorelWeight lam b : A) *
          generalLinearRegularEval g (c • integralDominantInducedVector R lam)
    simp only [Algebra.smul_def, map_mul, AlgHom.commutes,
      integralDominantInducedVector_right_transpose_borel lam hlam]
    ring
  have he : generalLinearRegularEval (1 : GeneralLinearGroup (Fin (m + 1)) R) p.val =
      generalLinearRegularEval (1 : GeneralLinearGroup (Fin (m + 1)) R) q.val := by
    simp only [q, map_smul, integralDominantInducedVector_one, smul_eq_mul, mul_one]
    rfl
  exact congrArg Subtype.val (integralInduced_opposite_character_ext R (m + 1) lam p q hp hq he)

end
end Dubon2026
