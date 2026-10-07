import Dubon2026.HeckeProjectiveConjugation
import Dubon2026.HeckeTraceIntegral
import Dubon2026.HeckeAllIndices

/-! # Self-adjointness of the actual good-prime classical Hecke operator -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane MeasureTheory
open scoped MatrixGroups ModularForm Pointwise

noncomputable section

/-- The actual mixed adjugate integrand is invariant under the lower Hecke subgroup. -/
theorem petersson_lowerHecke_invariant {p Q : ℕ} [NeZero p] {k : ℤ}
    (hpQ : Nat.Coprime p Q) (f g : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k)
    (δ : heckeRealLowerSubgroup Q p) (τ : ℍ) :
    petersson k f (⇑g ∣[k] heckeTriangularMatrix p 1 0) (δ • τ) =
      petersson k f (⇑g ∣[k] heckeTriangularMatrix p 1 0) τ := by
  obtain ⟨η, hη, heη⟩ := (mem_heckeRealLower_iff Q p δ.val).mp δ.property
  change petersson k f (⇑g ∣[k] heckeTriangularMatrix p 1 0) (δ.val • τ) = _
  rw [← heη]
  obtain ⟨γ, hγ, he⟩ := heckeLowerSubgroup_transition hpQ η hη
  have hg := cusp_slash_factor g η.val ⟨γ.val, γ.property, he⟩
  have h := petersson_slash_SL k f (⇑g ∣[k] heckeTriangularMatrix p 1 0) η.val τ
  rw [slash_Gamma0_eq f η.val η.property] at h
  change petersson k f ((⇑g ∣[k] heckeTriangularMatrix p 1 0) ∣[k] mapGL ℝ η.val) τ = _ at h
  rw [hg] at h
  exact h.symm

/-- The literal classical good-prime operator is self-adjoint for the actual Petersson pairing. -/
theorem cuspHecke_prime_selfAdjoint {p Q : ℕ} [NeZero Q] [NeZero p] {k : ℤ}
    (hp : Nat.Prime p) (hpQ : Nat.Coprime p Q)
    (f g : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) :
    cuspPetersson (cuspHecke p f) g = cuspPetersson f (cuspHecke p g) := by
  let r := heckeUpperRepresentative p Q hpQ
  let s := heckeLowerRepresentative p Q hpQ
  have hr := heckeUpperRepresentative_projective_injective hp hpQ
  have hs := heckeLowerRepresentative_projective_injective hp hpQ
  have hD : IsFundamentalDomain (heckeRealLowerSubgroup Q p)
      (heckeTriangularMatrix 1 p 0 • heckeTransversalDomain r) (volume : Measure ℍ) :=
    isFundamentalDomain_heckeUpper_translate hp hpQ
  have hE : IsFundamentalDomain (heckeRealLowerSubgroup Q p)
      (heckeTransversalDomain s) (volume : Measure ℍ) := isFundamentalDomain_heckeLower hp hpQ
  have hmove : peterssonInner k (heckeTriangularMatrix 1 p 0 • heckeTransversalDomain r)
      f (⇑g ∣[k] heckeTriangularMatrix p 1 0) =
        peterssonInner k (heckeTransversalDomain s) f (⇑g ∣[k] heckeTriangularMatrix p 1 0) :=
    hD.setIntegral_eq hE (petersson_lowerHecke_invariant hpQ f g)
  rw [cuspPetersson_eq_gamma0Domain_integral Q, cuspPetersson_eq_gamma0Domain_integral Q]
  change peterssonInner k (gamma0FundamentalDomain Q) (cuspHecke p f) g =
    peterssonInner k (gamma0FundamentalDomain Q) f (cuspHecke p g)
  have hf : ⇑(cuspHecke p f) = classicalHeckeFunction Q k p f := funext (cuspHecke_apply p f)
  have hg : ⇑(cuspHecke p g) = classicalHeckeFunction Q k p g := funext (cuspHecke_apply p g)
  rw [hf, hg, ← heckeUpperTrace_eq hp hpQ f, ← heckeLowerTrace_eq hp hpQ g]
  rw [peterssonInner_trace_left f g _ r hr, peterssonInner_trace_right f g _ s hs,
    peterssonInner_slash_adjugate _ _ (heckeTriangularMatrix_det_pos 1 p 0),
    peterssonAdj_heckeDiagonal]
  exact hmove

end
end Dubon2026
