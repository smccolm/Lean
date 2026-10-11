import Dubon2026.CommutativeHopfPointsGroup

/-! # The genuine contravariant point map induced by a coordinate bialgebra map -/

namespace Dubon2026
noncomputable section
open WithConv

variable {R A B K : Type*} [CommSemiring R] [CommSemiring A] [HopfAlgebra R A]
  [CommSemiring B] [HopfAlgebra R B] [CommSemiring K] [Algebra R K]

/-- A genuine coordinate bialgebra homomorphism induces a homomorphism on the actual convolution point groups by restriction. -/
def hopfPointsRestriction (h : A →ₐc[R] B) :
    WithConv (B →ₐ[R] K) →* WithConv (A →ₐ[R] K) where
  toFun p := toConv (p.ofConv.comp h.toAlgHom)
  map_one' := by
    apply WithConv.ext
    apply AlgHom.ext
    intro a
    exact congrArg (algebraMap R K) (AlgHom.congr_fun (BialgHom.counitAlgHom_comp h) a)
  map_mul' p q := by
    apply WithConv.ext
    exact AlgHom.convMul_comp_bialgHom_distrib p q h

/-- Point restriction evaluates the same original point on the original coordinate image. -/
theorem hopfPointsRestriction_apply (h : A →ₐc[R] B)
    (p : WithConv (B →ₐ[R] K)) (a : A) :
    hopfPointsRestriction h p a = p (h a) := by
  rfl

end
end Dubon2026
