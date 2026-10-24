import Dubon2026.SourceEllipticResidueActionConjugacy

/-! The actual residue-field map followed by conjugation transports
inertia homomorphisms to the prescribed elliptic curve's coordinate
stabilizer. Native group conjugation and injective field coefficient maps
preserve faithfulness, as required by the DUB-17/18 inertia orbit census. -/
namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve
noncomputable section
variable {k K : Type*} [Field k] [Field K]

/-- Map the literal coefficients, then conjugate by the prescribed residue-model change. -/
def residueConjugateHom (e : k ≃+* K) (γ : VariableChange K) :
    VariableChange k →* VariableChange K :=
  (MulAut.conj γ).toMonoidHom.comp (VariableChange.mapHom e.toRingHom)

theorem residueConjugateHom_injective (e : k ≃+* K) (γ : VariableChange K) :
    Function.Injective (residueConjugateHom e γ) :=
  (MulAut.conj γ).injective.comp (VariableChange.map_injective e.injective)

theorem residueConjugateHom_stabilizes (e : k ≃+* K) (V : WeierstrassCurve k)
    (E₀ : WeierstrassCurve K) (γ : VariableChange K)
    (hγ : γ • V.map e.toRingHom = E₀) (g : VariableChange k) (hg : g • V = V) :
    residueConjugateHom e γ g • E₀ = E₀ :=
  residueConjugate_stabilizes e V E₀ γ hγ g hg

end
end Dubon2026.SourceEllipticReduction
