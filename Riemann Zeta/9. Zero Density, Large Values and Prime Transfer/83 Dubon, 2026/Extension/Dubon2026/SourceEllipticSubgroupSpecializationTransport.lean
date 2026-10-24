import Dubon2026.SourceEllipticCyclicStabilizerRelation
import Dubon2026.SourceEllipticCyclicTorsionSpecialization

/-! DUB-17/18 exceptional-fiber orbits require transport through literal
torsion specialization. Injective subgroup images preserve equality;
negation preserves every additive subgroup. These two facts turn the
already proved point equivariance up to sign into the required equality
of actual subgroup orbits, with no orbit-comparison premise. -/
namespace Dubon2026.SourceEllipticReduction
noncomputable section

theorem subgroup_map_neg_eq {G : Type*} [AddCommGroup G] (S : AddSubgroup G) :
    S.map (-(AddMonoidHom.id G)) = S := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact S.neg_mem hy
  · intro hx
    exact ⟨-x, S.neg_mem hx, neg_neg x⟩

theorem subgroup_map_eq_of_eq_or_neg {A H : Type*} [AddCommGroup A] [AddCommGroup H]
    (S : AddSubgroup A) (f g : A →+ H)
    (h : (∀ x, f x = g x) ∨ (∀ x, f x = -(g x))) : S.map f = S.map g := by
  rcases h with h | h
  · exact congrArg (S.map) (AddMonoidHom.ext h)
  · have hf : f = (-(AddMonoidHom.id H)).comp g := AddMonoidHom.ext h
    rw [hf, ← AddSubgroup.map_map, subgroup_map_neg_eq]

theorem specialization_subgroup_map_eq_iff
    {A G H : Type*} [AddCommGroup A] [AddCommGroup G] [AddCommGroup H]
    (ι : A →+ G) (hι : Function.Injective ι)
    (θ : A →+ H) (hθ : Function.Injective θ)
    (S T : AddSubgroup G) (hS : S ≤ ι.range) (hT : T ≤ ι.range)
    (f : A →+ A) (a : G →+ G) (e : H →+ H)
    (ha : ∀ x, ι (f x) = a (ι x))
    (he : (∀ x, e (θ x) = θ (f x)) ∨ (∀ x, e (θ x) = -(θ (f x)))) :
    ((S.comap ι).map θ).map e = (T.comap ι).map θ ↔ S.map a = T := by
  have hleft : ((S.comap ι).map θ).map e = ((S.comap ι).map f).map θ := by
    rw [AddSubgroup.map_map, AddSubgroup.map_map]
    exact subgroup_map_eq_of_eq_or_neg (S.comap ι) (e.comp θ) (θ.comp f) he
  rw [hleft, (AddSubgroup.map_injective hθ).eq_iff]
  rw [← (AddSubgroup.map_injective hι).eq_iff]
  have hcomp : ι.comp f = a.comp ι := AddMonoidHom.ext ha
  rw [AddSubgroup.map_map, hcomp, ← AddSubgroup.map_map,
    AddSubgroup.map_comap_eq_self hS, AddSubgroup.map_comap_eq_self hT]

end
end Dubon2026.SourceEllipticReduction
