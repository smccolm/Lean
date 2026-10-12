import Dubon2026.LocalFieldFiniteScalarCoefficientH1
import Dubon2026.CharacterDualCoefficientSequence
import Mathlib.FieldTheory.Finite.Trace

/-! # The actual finite-field trace identifies the prime-field character dual

Keep the original coefficient action under the existing prime-field
restriction, and compose actual coefficient functionals with the field trace.
Trace nondegeneracy proves injectivity; pinned finite basis dualities prove
surjectivity without introducing extra dimension formulas. This identifies
the original finite extension-field dual needed by DUB-17's trace pairing.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] finiteScalarPrimeModule

variable {k G : Type} [Field k] [Finite k] [Group G]
  (q : ℕ) [Fact q.Prime] [CharP k q] [Algebra (ZMod q) k]
  (A : Rep.{0} k G) (χ : G →* ZMod q)

/-- Compose the original coefficient functional with the genuine field trace,
retaining the actual character-dual coefficient groups on both sides. -/
def finiteScalarTraceDualMap :
    characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ) →+
      characterDualCoefficientRep (finiteScalarPrimeRep q A) χ where
  toFun ℓ := ((Algebra.trace (ZMod q) k).toAddMonoidHom.comp ℓ.toAddMonoidHom).toZModLinearMap q
  map_zero' := by
    apply LinearMap.ext
    intro a
    exact map_zero (Algebra.trace (ZMod q) k)
  map_add' ℓ m := by
    apply LinearMap.ext
    intro a
    exact map_add (Algebra.trace (ZMod q) k) (ℓ a) (m a)

/-- Trace nondegeneracy detects the original extension-field functional
by evaluating its trace on all original scalar multiples of each coefficient. -/
theorem finiteScalarTraceDualMap_injective : Function.Injective (finiteScalarTraceDualMap q A χ) := by
  intro ℓ m h
  apply LinearMap.ext
  intro a
  apply sub_eq_zero.mp
  apply (traceForm_nondegenerate (ZMod q) k).1
  intro t
  have ht := DFunLike.congr_fun h (t • a)
  change Algebra.trace (ZMod q) k (ℓ (t • a)) = Algebra.trace (ZMod q) k (m (t • a)) at ht
  rw [map_smul ℓ, map_smul m] at ht
  change Algebra.trace (ZMod q) k ((ℓ a - m a) * t) = 0
  rw [sub_mul, map_sub, mul_comm (ℓ a), mul_comm (m a)]
  exact sub_eq_zero.mpr ht

omit [Finite k] in
/-- The field trace identifies the genuine dual actions because the original
cyclotomic scalar lies in the actual prime field. -/
theorem finiteScalarTraceDualMap_equivariant (g : G)
    (ℓ : characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ)) :
    finiteScalarTraceDualMap q A χ
      ((characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ)).ρ g ℓ) =
      (characterDualCoefficientRep (finiteScalarPrimeRep q A) χ).ρ g
        (finiteScalarTraceDualMap q A χ ℓ) := by
  apply LinearMap.ext
  intro a
  change Algebra.trace (ZMod q) k (algebraMap (ZMod q) k (χ g) * ℓ (A.ρ g⁻¹ a)) =
    χ g * Algebra.trace (ZMod q) k (ℓ (A.ρ g⁻¹ a))
  simpa only [Algebra.smul_def, smul_eq_mul] using
    (Algebra.trace (ZMod q) k).map_smul (χ g) (ℓ (A.ρ g⁻¹ a))

variable [Finite A]

/-- The original two coefficient duals have the same finite cardinality by
pinned basis dualities; trace injectivity therefore gives actual surjectivity. -/
theorem finiteScalarTraceDualMap_surjective : Function.Surjective (finiteScalarTraceDualMap q A χ) := by
  haveI : Finite (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ)) :=
    Finite.of_injective (fun ℓ : characterDualCoefficientRep A
      ((algebraMap (ZMod q) k).toMonoidHom.comp χ) => (ℓ : A → k)) DFunLike.coe_injective
  let e : characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ) ≃
      characterDualCoefficientRep (finiteScalarPrimeRep q A) χ :=
    (Module.finBasis k A).toDualEquiv.symm.toEquiv.trans
      (Module.finBasis (ZMod q) (finiteScalarPrimeRep q A)).toDualEquiv.toEquiv
  have hs : Function.Surjective (fun ℓ => e.symm (finiteScalarTraceDualMap q A χ ℓ)) :=
    Finite.surjective_of_injective (e.symm.injective.comp (finiteScalarTraceDualMap_injective q A χ))
  intro u
  obtain ⟨ℓ, hℓ⟩ := hs (e.symm u)
  exact ⟨ℓ, e.symm.injective hℓ⟩

/-- The genuine trace gives an additive equivalence from the original
extension-field character dual to the actual prime-field character dual. -/
def finiteScalarTraceDualEquiv :
    characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ) ≃+
      characterDualCoefficientRep (finiteScalarPrimeRep q A) χ :=
  AddEquiv.ofBijective (finiteScalarTraceDualMap q A χ)
    ⟨finiteScalarTraceDualMap_injective q A χ, finiteScalarTraceDualMap_surjective q A χ⟩

end
end Dubon2026
