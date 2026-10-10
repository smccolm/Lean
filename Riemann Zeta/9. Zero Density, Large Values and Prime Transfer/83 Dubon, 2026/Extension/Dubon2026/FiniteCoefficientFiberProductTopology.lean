import Dubon2026.LocalCoefficientFiberProduct
import Dubon2026.FiniteLocalCoefficientTopology

/-! # The actual maximal-adic and product-subtype topologies of finite coefficient fiber products -/

namespace Dubon2026
noncomputable section

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [IsLocalRing A] [Finite A] [Finite B]

/-- The genuine compatible-pair coefficient ring is Noetherian and complete for its actual maximal ideal. -/
theorem finiteCoefficientFiberProduct_noetherian_complete
    (f : A →+* C) (g : B →+* C) [IsLocalHom g] :
    (letI := coefficientFiberProduct_isLocalRing f g
     IsNoetherianRing (CoefficientFiberProduct f g) ∧
       IsAdicComplete (IsLocalRing.maximalIdeal (CoefficientFiberProduct f g))
         (CoefficientFiberProduct f g)) := by
  letI := coefficientFiberProduct_isLocalRing f g
  exact ⟨inferInstance, finiteLocalCoefficient_complete (CoefficientFiberProduct f g)⟩

/-- The same actual coefficient fiber-product ring has identical maximal-adic and product-subtype topologies when its two original coefficient topologies are discrete. -/
theorem finiteCoefficientFiberProduct_adicTopology_eq_product
    [TopologicalSpace A] [TopologicalSpace B] [DiscreteTopology A] [DiscreteTopology B]
    (f : A →+* C) (g : B →+* C) [IsLocalHom g] :
    (letI := coefficientFiberProduct_isLocalRing f g
     (IsLocalRing.maximalIdeal (CoefficientFiberProduct f g)).adicTopology =
       (inferInstance : TopologicalSpace (CoefficientFiberProduct f g))) := by
  letI := coefficientFiberProduct_isLocalRing f g
  exact (finiteLocalCoefficient_adicTopology_eq_bot (CoefficientFiberProduct f g)).trans
    DiscreteTopology.eq_bot.symm

/-- For the original finite local maximal-adic coefficient rings, the genuine fiber-product maximal-adic topology equals its actual original product-subtype topology. -/
theorem finiteCoefficientFiberProduct_original_adicTopology_eq_product
    [IsLocalRing B] [WithIdeal A] [WithIdeal B]
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (f : A →+* C) (g : B →+* C) [IsLocalHom g] :
    (letI := coefficientFiberProduct_isLocalRing f g
     (IsLocalRing.maximalIdeal (CoefficientFiberProduct f g)).adicTopology =
       (inferInstance : TopologicalSpace (CoefficientFiberProduct f g))) := by
  letI : DiscreteTopology A := finiteLocalCoefficient_discrete A hA
  letI : DiscreteTopology B := finiteLocalCoefficient_discrete B hB
  exact finiteCoefficientFiberProduct_adicTopology_eq_product f g

end
end Dubon2026
