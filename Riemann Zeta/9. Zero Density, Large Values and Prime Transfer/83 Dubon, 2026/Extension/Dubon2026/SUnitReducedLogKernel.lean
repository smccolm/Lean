import Dubon2026.SUnitReducedLogarithm

/-! # The finite kernel of the original reduced S-unit logarithm

The finite-coordinate kernel is the already proved original ordinary-unit
image. The pinned Dirichlet logarithm then identifies its zero vectors
with actual roots of unity. Finiteness, rather than an assumed lattice
rank, supplies the next step toward DUB-17's S-unit Herbrand quotient.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
variable (K : Type*) [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- The original reduced logarithm vanishes precisely on the original ordinary torsion units. -/
theorem sUnitReducedLog_eq_zero_iff
    (x : Additive ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) :
    sUnitReducedLog K S x = 0 ↔
      ∃ u : (𝓞 K)ˣ, u ∈ Units.torsion K ∧
        sUnitOrdinaryUnitEmbedding (R := 𝓞 K) (K := K) S u = x.toMul := by
  constructor
  · intro hx
    obtain ⟨u, hu⟩ := sUnitReducedLog_finite_zero_ordinary K S x (congrArg Prod.snd hx)
    have hx' : x = Additive.ofMul (sUnitOrdinaryUnitEmbedding (R := 𝓞 K) (K := K) S u) :=
      congrArg Additive.ofMul hu.symm
    have hlog := congrArg Prod.fst hx
    rw [hx', sUnitReducedLog_ordinary_fst] at hlog
    exact ⟨u, Units.dirichletUnitTheorem.logEmbedding_eq_zero_iff.mp hlog, hu⟩
  · rintro ⟨u, hu, hux⟩
    have hx' : x = Additive.ofMul (sUnitOrdinaryUnitEmbedding (R := 𝓞 K) (K := K) S u) :=
      congrArg Additive.ofMul hux.symm
    rw [hx']
    apply Prod.ext
    · rw [sUnitReducedLog_ordinary_fst]
      exact Units.dirichletUnitTheorem.logEmbedding_eq_zero_iff.mpr hu
    · exact sUnitReducedLog_ordinary_snd K S u

/-- The actual kernel of the original reduced logarithm is finite. -/
theorem sUnitReducedLog_finite_kernel : Finite (sUnitReducedLog K S).ker := by
  let f : Units.torsion K → (sUnitReducedLog K S).ker := fun u =>
    ⟨Additive.ofMul (sUnitOrdinaryUnitEmbedding (R := 𝓞 K) (K := K) S u.val),
      (sUnitReducedLog_eq_zero_iff K S _).mpr ⟨u.val, u.property, rfl⟩⟩
  apply Finite.of_surjective f
  intro x
  obtain ⟨u, hu, hux⟩ := (sUnitReducedLog_eq_zero_iff K S x.val).mp x.property
  exact ⟨⟨u, hu⟩, Subtype.ext (congrArg Additive.ofMul hux)⟩

end
end Dubon2026
