import Dubon2026.SourceEllipticVeluTwoHom
import Dubon2026.SourceEllipticVeluTwoSurjective

/-! The actual degree-two quotient homomorphism is surjective and every fiber
has cardinality two. This is the finite cyclic quotient needed for transport
of cyclic subgroups in the modular-polynomial root interpretation, then the
elliptic inertia census and good reduction on the DUB-17 / DUB-18 chain.
The fiber-count argument reuses native translation equivalences, exactly as
in the existing multiplication-fiber count; no quotient-cardinality input is
assumed. The identification with integral modular-polynomial roots remains open. -/
namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve
noncomputable section
variable {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]
  {W : WeierstrassCurve F} [W.IsElliptic] {x₀ y₀ : F}

theorem veluTwoHom_surjective (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : veluGy W x₀ y₀ = 0) : Function.Surjective (veluTwoHom hQ hgy) := by
  rw [veluTwoHom_coe]
  exact veluPointMap2_surjective hQ hgy _

theorem veluTwoHom_fiber_cardinality (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : veluGy W x₀ y₀ = 0) (Q : (veluQuotient2 W x₀ y₀).toAffine.Point) :
    Nat.card {P : W.toAffine.Point // veluTwoHom hQ hgy P = Q} = 2 := by
  obtain ⟨P₀, hP₀⟩ := veluTwoHom_surjective hQ hgy Q
  have e : (veluTwoHom hQ hgy).ker ≃ {P : W.toAffine.Point // veluTwoHom hQ hgy P = Q} := by
    refine Equiv.subtypeEquiv (Equiv.addRight P₀) fun P => ?_
    change veluTwoHom hQ hgy P = 0 ↔ veluTwoHom hQ hgy (P + P₀) = Q
    rw [map_add, hP₀, add_eq_right]
  exact (Nat.card_congr e).symm.trans (veluTwoHom_kernel_cardinality hQ hgy)

end
end Dubon2026.SourceEllipticVelu
