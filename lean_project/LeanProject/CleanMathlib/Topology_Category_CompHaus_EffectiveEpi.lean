import Mathlib.Topology.Category.CompHaus.Limits
import Mathlib.Topology.Category.CompHausLike.EffectiveEpi
universe u
open CategoryTheory Limits CompHausLike
attribute [local instance] ConcreteCategory.instFunLike
namespace CompHaus
open List in
theorem effectiveEpi_tfae
    {B X : CompHaus.{u}} (π : X ⟶ B) :
    TFAE
    [ EffectiveEpi π
    , Epi π
    , Function.Surjective π
    ] := by
  tfae_have 1 → 2 := fun _ ↦ inferInstance
  tfae_have 2 ↔ 3 := epi_iff_surjective π
  tfae_have 3 → 1 := fun hπ ↦ ⟨⟨effectiveEpiStruct π hπ⟩⟩
  tfae_finish
instance : Preregular CompHaus :=
  preregular fun _ _ _ ↦ ((effectiveEpi_tfae _).out 0 2).mp
example : Precoherent CompHaus.{u} := inferInstance
open List in
theorem effectiveEpiFamily_tfae
    {α : Type} [Finite α] {B : CompHaus.{u}}
    (X : α → CompHaus.{u}) (π : (a : α) → (X a ⟶ B)) :
    TFAE
    [ EffectiveEpiFamily X π
    , Epi (Sigma.desc π)
    , ∀ b : B, ∃ (a : α) (x : X a), π a x = b
    ] := by
  tfae_have 2 → 1
  | _ => by
    simpa [← effectiveEpi_desc_iff_effectiveEpiFamily, (effectiveEpi_tfae (Sigma.desc π)).out 0 1]
  tfae_have 1 → 2
  | _ => inferInstance
  tfae_have 3 → 2
  | e => by
    rw [epi_iff_surjective]
    intro b
    obtain ⟨t, x, h⟩ := e b
    refine ⟨Sigma.ι X t x, ?_⟩
    change (Sigma.ι X t ≫ Sigma.desc π) x = _
    simpa using h
  tfae_have 2 → 3
  | e => by
    rw [epi_iff_surjective] at e
    let i : ∐ X ≅ finiteCoproduct X :=
      (colimit.isColimit _).coconePointUniqueUpToIso (finiteCoproduct.isColimit _)
    intro b
    obtain ⟨t, rfl⟩ := e b
    let q := i.hom t
    refine ⟨q.1,q.2,?_⟩
    have : t = i.inv (i.hom t) := show t = (i.hom ≫ i.inv) t by simp only [i.hom_inv_id]; rfl
    rw [this]
    show _ = (i.inv ≫ Sigma.desc π) (i.hom t)
    suffices i.inv ≫ Sigma.desc π = finiteCoproduct.desc X π by
      rw [this]; rfl
    rw [Iso.inv_comp_eq]
    apply colimit.hom_ext
    rintro ⟨a⟩
    simp only [i, Discrete.functor_obj, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app,
      colimit.comp_coconePointUniqueUpToIso_hom_assoc]
    ext; rfl
  tfae_finish
theorem effectiveEpiFamily_of_jointly_surjective
    {α : Type} [Finite α] {B : CompHaus.{u}}
    (X : α → CompHaus.{u}) (π : (a : α) → (X a ⟶ B))
    (surj : ∀ b : B, ∃ (a : α) (x : X a), π a x = b) :
    EffectiveEpiFamily X π :=
  ((effectiveEpiFamily_tfae X π).out 2 0).mp surj
end CompHaus