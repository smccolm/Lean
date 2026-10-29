import Dubon2026.SourceTateDualQuadratic

/-! DUB-17/18 -> original all-weight association -> finite Hecke-character
quotient. Retain the combined diamond in the inverse-action Frobenius
identity, so that it can descend through actual diamond-minus-one
relations. No fixed-vector hypothesis is imposed. -/
namespace Dubon2026
noncomputable section
variable {R S T V : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup T] [Module R T] [AddCommGroup V]
  [Module R V] [Module S V] [IsScalarTower R S V]

theorem sourceTateDual_arithmetic_diamond_quadratic
    (b c : Module.End S V) (H F G D : Module.End R T) (ell w : ℕ)
    (hquad : H * F = F * F * D + ell • 1) (hFG : F * G = 1) (hcomm : Commute G D)
    (hcoeff : b.comp b = (ell : S) ^ w • c)
    (φ : T →ₗ[R] V) :
    (ell : S) • (b.restrictScalars R).comp
        (((b.restrictScalars R).comp (φ.comp H)).comp G) =
      (ell : S) • (b.restrictScalars R).comp
        (((ell : S) • (b.restrictScalars R).comp (φ.comp G)).comp G) +
        (ell : S) ^ (w + 1) • (c.restrictScalars R).comp (φ.comp D) := by
  apply LinearMap.ext
  intro x
  change (ell : S) • b (b (φ (H (G x)))) =
    (ell : S) • b ((ell : S) • b (φ (G (G x)))) + (ell : S) ^ (w + 1) • c (φ (D x))
  have hfg (y : T) : F (G y) = y := LinearMap.congr_fun hFG y
  have hdg (y : T) : D (G y) = G (D y) := (LinearMap.congr_fun hcomm.eq y).symm
  have hx : H (G x) = D x + ell • G (G x) := by
    have hh : H (F (G (G x))) = F (F (D (G (G x)))) + ell • G (G x) :=
      LinearMap.congr_fun hquad (G (G x))
    simpa only [hdg, hfg] using hh
  have hc : b (b (φ (D x))) = (ell : S) ^ w • c (φ (D x)) :=
    LinearMap.congr_fun hcoeff _
  rw [hx, map_add, map_add, map_add, smul_add, map_nsmul, map_nsmul, map_nsmul,
    hc, smul_smul, ← pow_succ', ← Nat.cast_smul_eq_nsmul S, map_smul]
  exact add_comm _ _

end
end Dubon2026
