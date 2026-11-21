import Dubon2026.PrimitiveFullCoefficients
import Dubon2026.Gamma0PrincipalFactor

/-! # Dubon's original primitive form as input to Alpöge's adelisation

The target fields are those of `UpperTheory.V.Sd.Eigenform` from
`IdeleGenerators/ConstSmall.lean`, with `coef`, `HasChar` and `IsEigAt`
expanded as in `AutomorphicForms/Newform.lean`. The natural weight is the
one used by the upstream adelisation theorem.
-/

namespace Dubon2026

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

/-- Restricting the level subgroup supplies the same holomorphic function,
the trivial nebentypus, normalized first coefficient and all prime Hecke
relations, including the U-operator relation at primes dividing the level. -/
theorem primitive_alpoge_eigenform_input {Q k : ℕ} [NeZero Q] (hk : 1 ≤ k)
    (f : PrimitiveCuspForm Q (k : ℤ)) :
    ∃ g : CuspForm (Gamma1 Q) (k : ℤ), (g : ℍ → ℂ) = f.toCuspForm ∧
      (∀ γ : SL(2, ℤ), γ ∈ Gamma0 Q →
        ((g : ℍ → ℂ) ∣[(k : ℤ)] γ) = (1 : DirichletCharacter ℂ Q) ((γ 1 1 : ℤ) : ZMod Q) • (g : ℍ → ℂ)) ∧
      (qExpansion 1 (g : ℍ → ℂ)).coeff 1 = 1 ∧
      ∀ p : ℕ, p.Prime → ∀ n : ℕ, 1 ≤ n →
        (qExpansion 1 (g : ℍ → ℂ)).coeff (p * n) +
          (1 : DirichletCharacter ℂ Q) (p : ZMod Q) * (p : ℂ) ^ (k - 1) *
            (if p ∣ n then (qExpansion 1 (g : ℍ → ℂ)).coeff (n / p) else 0) =
          (qExpansion 1 (g : ℍ → ℂ)).coeff p * (qExpansion 1 (g : ℍ → ℂ)).coeff n := by
  let g : CuspForm (Gamma1 Q) (k : ℤ) :=
    cuspRestrictSubgroup (Subgroup.map_mono (f := mapGL ℝ) (Gamma1_in_Gamma0 Q)) f.toCuspForm
  refine ⟨g, rfl, ?_, f.normalized, ?_⟩
  · intro γ hγ
    have hu : IsUnit ((γ 1 1 : ℤ) : ZMod Q) :=
      (Group.isUnit (⟨γ, hγ⟩ : Gamma0 Q)).map (Gamma0Map Q)
    rw [MulChar.one_apply hu, one_smul]
    exact SlashInvariantForm.slash_action_eqn f.toCuspForm (mapGL ℝ γ) ⟨γ, hγ, rfl⟩
  · intro p hp n _
    have he := primitiveCuspForm_hecke_coefficient_all f hp.pos n
    rw [classicalHeckeCoefficient_prime Q (k : ℤ) hp] at he
    change cuspCoefficients f.toCuspForm (p*n) + _ * _ *
      (if p ∣ n then cuspCoefficients f.toCuspForm (n/p) else 0) = _
    rw [principalCharacter_nat_indicator]
    have hweight : (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ) := by omega
    rw [hweight, zpow_natCast] at he
    by_cases hc : p.Coprime Q <;> by_cases hd : p ∣ n <;> simpa [hc, hd] using he

end Dubon2026
