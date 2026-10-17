import Dubon2026.OriginalRelationModuleSequence
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod

/-! # Integral coordinates for the original prime-torsion coefficient

Choose a basis over the actual prime field and lift its coordinates to
integers. The kernel consists precisely of prime multiples. These are the
coordinates needed to construct the norm-witness extension through the
original free relation cover on DUB-17's finite class/Ext route.
-/
namespace Dubon2026
noncomputable section

variable {G : Type} [Group G] (B : Rep.{0} ℤ G)

/-- Evaluate the original integral coordinates in the given coefficient elements. -/
def originalPrimeCoordinateEvaluation {ι : Type} (a : ι → B) : (ι →₀ ℤ) →+ B :=
  Finsupp.liftAddHom fun i => zmultiplesHom B (a i)

/-- The actual prime-torsion coefficient has integral representatives whose evaluation kernel consists of prime multiples; no coordinate certificate is assumed. -/
theorem originalPrimeCoefficient_exists_coordinates
    (p : ℕ) [Fact p.Prime] (hB : ∀ b : B, p • b = 0) :
    ∃ (ι : Type) (a : ι → B) (v : B → (ι →₀ ℤ)),
      (∀ b : B, originalPrimeCoordinateEvaluation B a (v b) = b) ∧
      (∀ z : ι →₀ ℤ, originalPrimeCoordinateEvaluation B a z = 0 →
        ∃ y : ι →₀ ℤ, z = p • y) := by
  haveI : Module (ZMod p) B := AddCommGroup.zmodModule hB
  obtain ⟨bs⟩ : Nonempty
      (Module.Basis (Module.Basis.ofVectorSpaceIndex (ZMod p) B) (ZMod p) B) :=
    ⟨Module.Basis.ofVectorSpace (ZMod p) B⟩
  have hlin : ∀ z : Module.Basis.ofVectorSpaceIndex (ZMod p) B →₀ ℤ,
      originalPrimeCoordinateEvaluation B (⇑bs) z =
        Finsupp.linearCombination (ZMod p) (⇑bs)
          (z.mapRange (Int.cast : ℤ → ZMod p) Int.cast_zero) := by
    intro z
    rw [originalPrimeCoordinateEvaluation, Finsupp.liftAddHom_apply, Finsupp.linearCombination_apply,
      Finsupp.sum_mapRange_index (fun i => zero_smul (ZMod p) (bs i))]
    refine Finsupp.sum_congr fun i _ => ?_
    rw [Int.cast_smul_eq_zsmul]
    exact zmultiplesHom_apply _ (bs i) (z i)
  refine ⟨Module.Basis.ofVectorSpaceIndex (ZMod p) B, ⇑bs,
    fun b => (bs.repr b).mapRange (fun c => (c.val : ℤ)) (by simp), ?_, ?_⟩
  · intro b
    have hm : ((bs.repr b).mapRange (fun c => (c.val : ℤ)) (by simp)).mapRange
        (Int.cast : ℤ → ZMod p) Int.cast_zero = bs.repr b := by
      ext i
      simp
    rw [hlin, hm, Module.Basis.linearCombination_repr]
  · intro z hz
    rw [hlin] at hz
    have hz' := linearIndependent_iff.1 bs.linearIndependent _ hz
    have hdvd : ∀ i, (p : ℤ) ∣ z i := fun i => by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact DFunLike.congr_fun hz' i
    refine ⟨z.mapRange (fun n => n / p) (by simp), Finsupp.ext fun i => ?_⟩
    simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, nsmul_eq_mul]
    exact (Int.mul_ediv_cancel' (hdvd i)).symm

end
end Dubon2026
