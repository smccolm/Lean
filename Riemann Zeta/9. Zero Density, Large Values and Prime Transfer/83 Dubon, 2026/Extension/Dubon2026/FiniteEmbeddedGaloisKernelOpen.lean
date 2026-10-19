import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Galois.Profinite

/-! # Openness of the original finite embedded restriction kernel

The literal embedding square makes a finite number-field restriction
continuous in the original local Galois group. This permits the proved
Frobenius generation theorem to classify the whole local deformation
representation needed for Dubon Theorem 2.6.
-/

namespace Dubon2026
noncomputable section

/-- The kernel of the original finite field action is a finite intersection
of open stabilizers of embedded basis elements. No continuity premise for
the restriction homomorphism is required. -/
theorem finiteEmbeddedGalois_kernel_isOpen
    {K L F : Type} [Field K] [Field L] [Algebra K L] [Algebra.IsIntegral K L]
    [Field F] [NumberField F]
    (e : F →+* L) (r : Gal(L/K) →* Gal(F/ℚ))
    (he : ∀ g x, e (r g x) = g (e x)) : IsOpen (r.ker : Set Gal(L/K)) := by
  classical
  let b := Module.Free.chooseBasis ℚ F
  have hk : (r.ker : Set Gal(L/K)) =
      ⋂ i : Module.Free.ChooseBasisIndex ℚ F,
        (MulAction.stabilizer Gal(L/K) (e (b i)) : Set Gal(L/K)) := by
    ext g
    simp only [Set.mem_iInter, SetLike.mem_coe, MonoidHom.mem_ker,
      MulAction.mem_stabilizer_iff]
    constructor
    · intro h i
      change g (e (b i)) = e (b i)
      rw [← he, h]
      rfl
    · intro h
      have hb : (r g).toAlgHom = (1 : Gal(F/ℚ)).toAlgHom := by
        apply AlgHom.toLinearMap_injective
        apply b.ext
        intro i
        apply e.injective
        change e (r g (b i)) = e (b i)
        rw [he]
        exact h i
      exact AlgEquiv.ext (fun x => DFunLike.congr_fun hb x)
  rw [hk]
  exact isOpen_iInter_of_finite fun i => stabilizer_isOpen_of_isIntegral (K := K) (e (b i))

end
end Dubon2026
