import Dubon2026.SourceEllipticTwoCyclicAbscissae

/-! DUB-17/18 -> all-level inertia census -> successive cyclic quotient
compatibility. The intrinsic finite abscissa coefficient models commute with
the original field embedding. Native finite-sum transport and the existing
division-polynomial formula suffice; no general isogeny framework is needed. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve Polynomial
noncomputable section
variable {F K : Type*} [Field F] [Field K]
variable (f : F →+* K) (W : WeierstrassCurve F)

theorem map_abscissaVeluT (x : F) :
    f (abscissaVeluT W x) = abscissaVeluT (W.map f) (f x) := by
  simp [abscissaVeluT, map_ofNat]

theorem map_abscissaVeluW (x : F) :
    f (abscissaVeluW W x) = abscissaVeluW (W.map f) (f x) := by
  simp [abscissaVeluW, Ψ₂Sq, map_abscissaVeluT, map_ofNat]

theorem map_twoAbscissaG [DecidableEq F] [DecidableEq K] (x : F) :
    f (twoAbscissaG W x) = twoAbscissaG (W.map f) (f x) := by
  simp [twoAbscissaG, veluGx, map_ofNat]

/-- The intrinsic odd coefficient model commutes with an actual field embedding. -/
theorem abscissaQuotient_map [DecidableEq K] (S : Finset F) :
    abscissaQuotient (W.map f) (S.image f) = (abscissaQuotient W S).map f := by
  have hT : ∑ x ∈ S.image f, abscissaVeluT (W.map f) x =
      f (∑ x ∈ S, abscissaVeluT W x) := by
    rw [Finset.sum_image f.injective.injOn, map_sum]
    exact Finset.sum_congr rfl fun x _ => (map_abscissaVeluT f W x).symm
  have hW : ∑ x ∈ S.image f, abscissaVeluW (W.map f) x =
      f (∑ x ∈ S, abscissaVeluW W x) := by
    rw [Finset.sum_image f.injective.injOn, map_sum]
    exact Finset.sum_congr rfl fun x _ => (map_abscissaVeluW f W x).symm
  ext <;> simp [abscissaQuotient, hT, hW, map_ofNat]

/-- The intrinsic degree-two coefficient model commutes with an actual field embedding. -/
theorem twoAbscissaQuotient_map [DecidableEq F] [DecidableEq K] (S : Finset F) :
    twoAbscissaQuotient (W.map f) (S.image f) = (twoAbscissaQuotient W S).map f := by
  have hG : ∑ x ∈ S.image f, twoAbscissaG (W.map f) x =
      f (∑ x ∈ S, twoAbscissaG W x) := by
    rw [Finset.sum_image f.injective.injOn, map_sum]
    exact Finset.sum_congr rfl fun x _ => (map_twoAbscissaG f W x).symm
  have hXG : ∑ x ∈ S.image f, x * twoAbscissaG (W.map f) x =
      f (∑ x ∈ S, x * twoAbscissaG W x) := by
    rw [Finset.sum_image f.injective.injOn, map_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [map_mul, map_twoAbscissaG]
  ext <;> simp [twoAbscissaQuotient, hG, hXG, map_ofNat]

end
end Dubon2026.SourceEllipticVelu
