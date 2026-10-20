import Dubon2026.CMFiniteAdelicUnitaryGroup
import Dubon2026.NumberFieldIntegralFiniteAdeles

/-! # Actual CM adelic pairings and integrality

The place-permuting involution preserves the original integral finite
adeles. The actual unitary group preserves the specified pairing, and
the principal pairing is the original CM field pairing. These identities
serve DUB-17's uniform integral trace-form restriction on the attached
adelic lattices.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped NumberField

attribute [local instance] cmFiniteAdeleStarRing

variable (K : Type) [Field K] [NumberField K] [IsCMField K]

/-- The actual place-permuting CM conjugation preserves all original local integrality conditions. -/
theorem cmFiniteAdele_star_integral {x : FiniteAdeleRing (𝓞 K) K}
    (hx : x ∈ numberFieldIntegralFiniteAdeles K) :
    star x ∈ numberFieldIntegralFiniteAdeles K := by
  let σ := (IsCMField.complexConj K).restrictScalars ℚ
  let e := numberFieldGaloisPlaceEquiv ℚ K σ
  intro w
  change Valued.v (numberFieldFiniteAdeleGaloisMap ℚ K σ x w) ≤ 1
  rw [numberFieldFiniteAdeleGaloisMap_apply ℚ K σ x (e.symm w) w (e.apply_symm_apply w),
    numberFieldGaloisLocalTransport_valuation]
  exact hx (e.symm w)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual finite-adelic unitary group preserves the specified sesquilinear pairing. -/
theorem cmFiniteAdelicPairing_preserved (H : Matrix ι ι K)
    (g : cmFiniteAdelicUnitaryGroup K H)
    (x y : ι → FiniteAdeleRing (𝓞 K) K) :
    dotProduct (star (g.val.val.mulVec x))
      (((algebraMap K (FiniteAdeleRing (𝓞 K) K)).mapMatrix H).mulVec (g.val.val.mulVec y)) =
        dotProduct (star x) (((algebraMap K (FiniteAdeleRing (𝓞 K) K)).mapMatrix H).mulVec y) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  have hg := g.property
  change star g.val.val * _ * g.val.val = _ at hg
  rw [show g.val.val.conjTranspose = star g.val.val from rfl, hg]

/-- The principal embedding carries the original CM field pairing to the actual adelic pairing. -/
theorem cmFiniteAdelicPairing_principal (H : Matrix ι ι K) (x y : ι → K) :
    algebraMap K (FiniteAdeleRing (𝓞 K) K) (dotProduct (star x) (H.mulVec y)) =
      dotProduct (star (fun i => algebraMap K (FiniteAdeleRing (𝓞 K) K) (x i)))
        (((algebraMap K (FiniteAdeleRing (𝓞 K) K)).mapMatrix H).mulVec
          (fun i => algebraMap K (FiniteAdeleRing (𝓞 K) K) (y i))) := by
  change algebraMap K (FiniteAdeleRing (𝓞 K) K) (∑ i, star (x i) * (∑ j, H i j * y j)) =
    ∑ i, star (algebraMap K (FiniteAdeleRing (𝓞 K) K) (x i)) *
      (∑ j, algebraMap K (FiniteAdeleRing (𝓞 K) K) (H i j) *
        algebraMap K (FiniteAdeleRing (𝓞 K) K) (y j))
  simp only [map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [← cmFiniteAdeleConjugation_algebraMap K (x i)]
  rfl

end
end Dubon2026
