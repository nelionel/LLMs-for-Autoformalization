import Mathlib.CategoryTheory.Category.Pointed
import Mathlib.Data.PFun
open CategoryTheory Option
universe u
def PartialFun : Type _ :=
  Type*
namespace PartialFun
instance : CoeSort PartialFun Type* :=
  ⟨id⟩
def of : Type* → PartialFun :=
  id
instance : Inhabited PartialFun :=
  ⟨Type*⟩
instance largeCategory : LargeCategory.{u} PartialFun where
  Hom := PFun
  id := PFun.id
  comp f g := g.comp f
  id_comp := @PFun.comp_id
  comp_id := @PFun.id_comp
  assoc _ _ _ := (PFun.comp_assoc _ _ _).symm
@[simps]
def Iso.mk {α β : PartialFun.{u}} (e : α ≃ β) : α ≅ β where
  hom x := e x
  inv x := e.symm x
  hom_inv_id := (PFun.coe_comp _ _).symm.trans (by
    simp only [Equiv.symm_comp_self, PFun.coe_id]
    rfl)
  inv_hom_id := (PFun.coe_comp _ _).symm.trans (by
    simp only [Equiv.self_comp_symm, PFun.coe_id]
    rfl)
end PartialFun
def typeToPartialFun : Type u ⥤ PartialFun where
  obj := id
  map := @PFun.lift
  map_comp _ _ := PFun.coe_comp _ _
instance : typeToPartialFun.Faithful where
  map_injective {_ _} := PFun.lift_injective
@[simps obj map]
def pointedToPartialFun : Pointed.{u} ⥤ PartialFun where
  obj X := { x : X // x ≠ X.point }
  map f := PFun.toSubtype _ f.toFun ∘ Subtype.val
  map_id _ :=
    PFun.ext fun _ b =>
      PFun.mem_toSubtype_iff (b := b).trans (Subtype.coe_inj.trans Part.mem_some_iff.symm)
  map_comp f g := by
    apply PFun.ext _
    rintro ⟨a, ha⟩ ⟨c, hc⟩
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨⟨fun h₀ => h₁ ((congr_arg g.toFun h₀).trans g.map_point), h₁⟩, h₂⟩
    · rintro ⟨_, _, _⟩
      exact ⟨_, rfl⟩
@[simps obj map]
noncomputable def partialFunToPointed : PartialFun ⥤ Pointed := by
  classical
  exact
    { obj := fun X => ⟨Option X, none⟩
      map := fun f => ⟨Option.elim' none fun a => (f a).toOption, rfl⟩
      map_id := fun X => Pointed.Hom.ext <| funext fun o => Option.recOn o rfl fun a => (by
        dsimp [CategoryStruct.id]
        convert Part.some_toOption a)
      map_comp := fun f g => Pointed.Hom.ext <| funext fun o => Option.recOn o rfl fun a => by
        dsimp [CategoryStruct.comp]
        rw [Part.bind_toOption g (f a), Option.elim'_eq_elim] }
@[simps!]
noncomputable def partialFunEquivPointed : PartialFun.{u} ≌ Pointed where
  functor := partialFunToPointed
  inverse := pointedToPartialFun
  unitIso := NatIso.ofComponents (fun X => PartialFun.Iso.mk
      { toFun := fun a => ⟨some a, some_ne_none a⟩
        invFun := fun a => Option.get _ (Option.ne_none_iff_isSome.1 a.2)
        left_inv := fun _ => Option.get_some _ _
        right_inv := fun a => by simp only [some_get, Subtype.coe_eta] })
      fun f =>
        PFun.ext fun a b => by
          dsimp [PartialFun.Iso.mk, CategoryStruct.comp, pointedToPartialFun]
          rw [Part.bind_some]
          refine (Part.mem_bind_iff.trans ?_).trans PFun.mem_toSubtype_iff.symm
          obtain ⟨b | b, hb⟩ := b
          · exact (hb rfl).elim
          · dsimp [Part.toOption]
            simp_rw [Part.mem_some_iff, Subtype.mk_eq_mk]
            constructor
            · rintro ⟨_, ⟨h₁, h₂⟩, h₃⟩
              rw [h₃, ← h₂, dif_pos h₁]
            · intro h
              split_ifs at h with ha
              rw [some_inj] at h
              exact ⟨b, ⟨ha, h.symm⟩, rfl⟩
  counitIso :=
    NatIso.ofComponents
      (fun X ↦ Pointed.Iso.mk (by classical exact Equiv.optionSubtypeNe X.point) (by rfl))
      fun {X Y} f ↦ Pointed.Hom.ext <| funext fun a ↦ by
        obtain _ | ⟨a, ha⟩ := a
        · exact f.map_point.symm
        simp_all [Option.casesOn'_eq_elim, Part.elim_toOption]
  functor_unitIso_comp X := by
    ext (_ | x)
    · rfl
    · simp
      rfl
@[simps!]
noncomputable def typeToPartialFunIsoPartialFunToPointed :
    typeToPartialFun ⋙ partialFunToPointed ≅ typeToPointed :=
  NatIso.ofComponents
    (fun _ =>
      { hom := ⟨id, rfl⟩
        inv := ⟨id, rfl⟩
        hom_inv_id := rfl
        inv_hom_id := rfl })
    fun f =>
    Pointed.Hom.ext <|
      funext fun a => Option.recOn a rfl fun a => by
        convert Part.some_toOption _
        simpa using (Part.get_eq_iff_mem (by trivial)).mp rfl