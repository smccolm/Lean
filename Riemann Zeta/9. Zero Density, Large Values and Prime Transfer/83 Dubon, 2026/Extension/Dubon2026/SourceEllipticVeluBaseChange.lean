import Dubon2026.SourceEllipticVeluTwoQuotient

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> good reduction
-> reverse genus -> finite exceptional fibers -> elliptic inertia orbits
-> actual cyclic-quotient interpretation of modular-polynomial roots
-> actual Velu quotients and their specialization. These are the literal
coefficient formulas and their proved identities, including base change
under injectivity on the finite coordinate set. Ellipticity of the quotient,
the quotient homomorphism, its kernel and the modular-polynomial identity
still require proofs. No such conclusions are packaged as assumptions here.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, Definitions/Def_WeierstrassCurve_Velu.lean,
Def_WeierstrassCurve_VeluOrderTwo.lean and
P2M/Sol/S_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient_j.lean. -/
namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve Polynomial
noncomputable section
variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (W : WeierstrassCurve R)

theorem map_veluT (x y : R) : φ (veluT W x y) = veluT (W.map φ) (φ x) (φ y) := by
  simp [veluT, veluGx, veluGy, map_ofNat]

theorem map_veluW (x y : R) : φ (veluW W x y) = veluW (W.map φ) (φ x) (φ y) := by
  simp [veluW, veluU, veluT,
    veluGx, veluGy, map_ofNat]

variable [DecidableEq S]

theorem map_veluTSum (T : Finset (R × R)) (hφ : Set.InjOn (Prod.map φ φ) T) :
    φ (veluTSum W T) = veluTSum (W.map φ) (T.image (Prod.map φ φ)) := by
  rw [veluTSum, veluTSum, Finset.sum_image hφ, map_sum]
  exact Finset.sum_congr rfl fun P _ => map_veluT φ W P.1 P.2

theorem map_veluWSum (T : Finset (R × R)) (hφ : Set.InjOn (Prod.map φ φ) T) :
    φ (veluWSum W T) = veluWSum (W.map φ) (T.image (Prod.map φ φ)) := by
  rw [veluWSum, veluWSum, Finset.sum_image hφ, map_sum]
  exact Finset.sum_congr rfl fun P _ => map_veluW φ W P.1 P.2

theorem veluQuotient_map (T : Finset (R × R)) (hφ : Set.InjOn (Prod.map φ φ) T) :
    (veluQuotient W T).map φ = veluQuotient (W.map φ) (T.image (Prod.map φ φ)) := by
  ext
  · rfl
  · rfl
  · rfl
  · show φ (W.a₄ - 5 * veluTSum W T) = _
    rw [veluQuotient_a₄, map_sub, map_mul, map_ofNat, map_veluTSum φ W T hφ]
    rfl
  · show φ (W.a₆ - W.b₂ * veluTSum W T - 7 * veluWSum W T) = _
    rw [veluQuotient_a₆, map_sub, map_sub, map_mul, map_mul, map_ofNat,
      map_veluTSum φ W T hφ, map_veluWSum φ W T hφ, ← WeierstrassCurve.map_b₂]
    rfl


end
end Dubon2026.SourceEllipticVelu
