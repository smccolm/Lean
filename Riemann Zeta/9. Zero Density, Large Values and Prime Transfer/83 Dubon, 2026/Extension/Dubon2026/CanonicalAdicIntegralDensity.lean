import Dubon2026.IntegralSL2PrimeProductDensity
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-! # Integral matrix density in the canonical adic completions of the rationals -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup IsDedekindDomain
open scoped MatrixGroups

/-- A continuous scalar-ring equivalence gives the actual matrix-group homeomorphism. -/
def sl2RingHomeomorph {R S : Type*} [CommRing R] [CommRing S]
    [TopologicalSpace R] [TopologicalSpace S] (e : R ≃+* S)
    (he : Continuous e) (hei : Continuous e.symm) : SL(2, R) ≃ₜ SL(2, S) where
  toEquiv := (sl2RingEquiv e).toEquiv
  continuous_toFun := he.specialLinearGroup_map
  continuous_invFun := hei.specialLinearGroup_map

/-- The prime attached to a canonical rational finite place is prime. -/
local instance rationalFinitePlacePrime (v : HeightOneSpectrum ℤ) :
    Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩

/-- The actual integral diagonal is dense in the product of canonical compact local matrix groups. -/
theorem integralSL2_dense_adic_integer_product :
    DenseRange (fun γ : SL(2, ℤ) => fun v : HeightOneSpectrum ℤ =>
      Matrix.SpecialLinearGroup.map (Int.castRingHom (v.adicCompletionIntegers ℚ)) γ) := by
  letI (v : HeightOneSpectrum ℤ) : Algebra ℤ (v.adicCompletionIntegers ℚ) :=
    Ring.toIntAlgebra _
  let e (v : HeightOneSpectrum ℤ) :=
    Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v
  let H := Homeomorph.piCongrRight (fun v : HeightOneSpectrum ℤ =>
    sl2RingHomeomorph (e v).toRingEquiv (e v).continuous (e v).symm.continuous)
  have hp : Function.Injective (fun v : HeightOneSpectrum ℤ =>
      (Rat.HeightOneSpectrum.primesEquiv v).val) :=
    Subtype.val_injective.comp Rat.HeightOneSpectrum.primesEquiv.injective
  have hd := H.symm.surjective.denseRange.comp
    (integralSL2_dense_prime_product _ hp) H.symm.continuous
  have heq : H.symm ∘ (fun γ : SL(2, ℤ) => fun v : HeightOneSpectrum ℤ =>
      Matrix.SpecialLinearGroup.map
        (Int.castRingHom ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) γ) =
      (fun γ : SL(2, ℤ) => fun v : HeightOneSpectrum ℤ =>
        Matrix.SpecialLinearGroup.map (Int.castRingHom (v.adicCompletionIntegers ℚ)) γ) := by
    funext γ v
    apply Subtype.ext
    funext i j
    exact map_intCast (e v).symm.toRingEquiv (γ i j)
  rw [heq] at hd
  exact hd

/-- Extracting an upper unipotent entry shows density of integers in the canonical compact product. -/
theorem integer_dense_adic_integer_product :
    DenseRange (fun n : ℤ => fun v : HeightOneSpectrum ℤ =>
      (n : v.adicCompletionIntegers ℚ)) := by
  let F : (∀ v : HeightOneSpectrum ℤ, SL(2, v.adicCompletionIntegers ℚ)) →
      (∀ v : HeightOneSpectrum ℤ, v.adicCompletionIntegers ℚ) := fun g v => g v 0 1
  have hF : Function.Surjective F := by
    intro x
    refine ⟨fun v => ⟨!![1, x v; 0, 1], ?_⟩, rfl⟩
    simp [Matrix.det_fin_two]
  have hc : Continuous F := by
    apply continuous_pi
    intro v
    exact (_root_.continuous_apply 1).comp
      ((Matrix.SpecialLinearGroup.continuous_apply _ (_root_.continuous_apply v) 0))
  have hd := hF.denseRange.comp integralSL2_dense_adic_integer_product hc
  exact Dense.mono (by
    rintro x ⟨γ, rfl⟩
    exact ⟨γ 0 1, rfl⟩) hd

end
end Dubon2026
