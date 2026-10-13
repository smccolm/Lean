import Dubon2026.NumberFieldIdeleSupport
import Dubon2026.PrincipalIdealValuationBridge

/-! # Original finite idele orders and the existing principal-ideal bridge

Only the orders needed to build the original fractional ideal are added.
They have finite support by the original finite-adele unit criterion.
The already proved principal-ideal multiplicity theorem is reused to
connect the same principal idele with its actual ideal. This advances
surjectivity of supported ideles for sufficiently large S, needed for
DUB-17's supported-idele sequence and global norm-index calculation.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors
variable (K : Type) [Field K] [NumberField K]

/-- The normalized integral order of the original local component of the original idele. -/
def numberFieldIdeleOrder (a : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) : ℤ :=
  -WithZero.log (Valued.v ((numberFieldIdeleFiniteComponent K v a).val))

/-- Order zero is exactly local integral invertibility for the original idele component. -/
theorem numberFieldIdeleOrder_eq_zero_iff
    (a : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    numberFieldIdeleOrder K a v = 0 ↔
      numberFieldIdeleFiniteComponent K v a ∈ (v.adicCompletionIntegers K).units := by
  rw [numberFieldIdeleOrder, neg_eq_zero,
    HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
  have hz : Valued.v (numberFieldIdeleFiniteComponent K v a).val ≠ 0 := by simp
  constructor
  · intro h
    rw [← WithZero.exp_log hz, h, WithZero.exp_zero]
  · intro h
    rw [h, WithZero.log_one]

/-- The actual original finite idele orders vanish outside finitely many original places. -/
theorem numberFieldIdeleOrder_finite_support (a : (AdeleRing (𝓞 K) K)ˣ) :
    {v : HeightOneSpectrum (𝓞 K) | numberFieldIdeleOrder K a v ≠ 0}.Finite := by
  let b : (FiniteAdeleRing (𝓞 K) K)ˣ :=
    Units.map (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).toMonoidHom a
  have h := (FiniteAdeleRing.isUnit_iff.mp b.isUnit).2
  apply Filter.eventually_cofinite.mp
  filter_upwards [h] with v hv
  change -WithZero.log (Valued.v (b.val v)) = 0
  rw [hv, WithZero.log_one, neg_zero]

/-- The order of an original principal idele is the multiplicity of its actual original principal ideal. -/
theorem numberFieldIdeleOrder_principal (x : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    numberFieldIdeleOrder K (numberFieldPrincipalIdele K x) v =
      FractionalIdeal.count K v (toPrincipalIdeal (𝓞 K) K x).val := by
  rw [principalIdeal_count_eq_neg_valuation]
  change -WithZero.log (Valued.v (algebraMap K (v.adicCompletion K) x.val)) = _
  simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    Algebra.algebraMap_self, RingHom.id_apply, Valued.valuedCompletion_apply]
  change -WithZero.log (v.valuation K x.val) = _
  have h := HeightOneSpectrum.valuationOfNeZero_eq v x
  rw [← h]
  rfl

end
end Dubon2026
