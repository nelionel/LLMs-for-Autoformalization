import Mathlib.Control.Functor
import Mathlib.Tactic.Common
universe u₀ u₁ u₂ v₀ v₁ v₂
open Function
class Bifunctor (F : Type u₀ → Type u₁ → Type u₂) where
  bimap : ∀ {α α' β β'}, (α → α') → (β → β') → F α β → F α' β'
export Bifunctor (bimap)
class LawfulBifunctor (F : Type u₀ → Type u₁ → Type u₂) [Bifunctor F] : Prop where
  id_bimap : ∀ {α β} (x : F α β), bimap id id x = x
  bimap_bimap :
    ∀ {α₀ α₁ α₂ β₀ β₁ β₂} (f : α₀ → α₁) (f' : α₁ → α₂) (g : β₀ → β₁) (g' : β₁ → β₂) (x : F α₀ β₀),
      bimap f' g' (bimap f g x) = bimap (f' ∘ f) (g' ∘ g) x
export LawfulBifunctor (id_bimap bimap_bimap)
attribute [higher_order bimap_id_id] id_bimap
attribute [higher_order bimap_comp_bimap] bimap_bimap
export LawfulBifunctor (bimap_id_id bimap_comp_bimap)
variable {F : Type u₀ → Type u₁ → Type u₂} [Bifunctor F]
namespace Bifunctor
abbrev fst {α α' β} (f : α → α') : F α β → F α' β :=
  bimap f id
abbrev snd {α β β'} (f : β → β') : F α β → F α β' :=
  bimap id f
variable [LawfulBifunctor F]
@[higher_order fst_id]
theorem id_fst : ∀ {α β} (x : F α β), fst id x = x :=
  @id_bimap _ _ _
@[higher_order snd_id]
theorem id_snd : ∀ {α β} (x : F α β), snd id x = x :=
  @id_bimap _ _ _
@[higher_order fst_comp_fst]
theorem comp_fst {α₀ α₁ α₂ β} (f : α₀ → α₁) (f' : α₁ → α₂) (x : F α₀ β) :
    fst f' (fst f x) = fst (f' ∘ f) x := by simp [fst, bimap_bimap]
@[higher_order fst_comp_snd]
theorem fst_snd {α₀ α₁ β₀ β₁} (f : α₀ → α₁) (f' : β₀ → β₁) (x : F α₀ β₀) :
    fst f (snd f' x) = bimap f f' x := by simp [fst, bimap_bimap]
@[higher_order snd_comp_fst]
theorem snd_fst {α₀ α₁ β₀ β₁} (f : α₀ → α₁) (f' : β₀ → β₁) (x : F α₀ β₀) :
    snd f' (fst f x) = bimap f f' x := by simp [snd, bimap_bimap]
@[higher_order snd_comp_snd]
theorem comp_snd {α β₀ β₁ β₂} (g : β₀ → β₁) (g' : β₁ → β₂) (x : F α β₀) :
    snd g' (snd g x) = snd (g' ∘ g) x := by simp [snd, bimap_bimap]
attribute [functor_norm]
  bimap_bimap comp_snd comp_fst snd_comp_snd snd_comp_fst fst_comp_snd fst_comp_fst
  bimap_comp_bimap bimap_id_id fst_id snd_id
end Bifunctor
open Functor
instance Prod.bifunctor : Bifunctor Prod where bimap := @Prod.map
instance Prod.lawfulBifunctor : LawfulBifunctor Prod where
  id_bimap _ := rfl
  bimap_bimap _ _ _ _ _ := rfl
instance Bifunctor.const : Bifunctor Const where bimap f _ := f
instance LawfulBifunctor.const : LawfulBifunctor Const where
  id_bimap _ := rfl
  bimap_bimap _ _ _ _ _ := rfl
instance Bifunctor.flip : Bifunctor (flip F) where
  bimap {_α α' _β β'} f f' x := (bimap f' f x : F β' α')
instance LawfulBifunctor.flip [LawfulBifunctor F] : LawfulBifunctor (flip F) where
  id_bimap := by simp [bimap, functor_norm]
  bimap_bimap := by simp [bimap, functor_norm]
instance Sum.bifunctor : Bifunctor Sum where bimap := @Sum.map
instance Sum.lawfulBifunctor : LawfulBifunctor Sum where
  id_bimap := by aesop
  bimap_bimap := by aesop
open Bifunctor Functor
instance (priority := 10) Bifunctor.functor {α} : Functor (F α) where map f x := snd f x
instance (priority := 10) Bifunctor.lawfulFunctor [LawfulBifunctor F] {α} :
    LawfulFunctor (F α) where
  id_map := by simp [Functor.map, functor_norm]
  comp_map := by simp [Functor.map, functor_norm]
  map_const := by simp [mapConst, Functor.map]
section Bicompl
variable (G : Type* → Type u₀) (H : Type* → Type u₁) [Functor G] [Functor H]
instance Function.bicompl.bifunctor : Bifunctor (bicompl F G H) where
  bimap {_α α' _β β'} f f' x := (bimap (map f) (map f') x : F (G α') (H β'))
instance Function.bicompl.lawfulBifunctor [LawfulFunctor G] [LawfulFunctor H] [LawfulBifunctor F] :
    LawfulBifunctor (bicompl F G H) := by
  constructor <;> intros <;> simp [bimap, map_id, map_comp_map, functor_norm]
end Bicompl
section Bicompr
variable (G : Type u₂ → Type*) [Functor G]
instance Function.bicompr.bifunctor : Bifunctor (bicompr G F) where
  bimap {_α α' _β β'} f f' x := (map (bimap f f') x : G (F α' β'))
instance Function.bicompr.lawfulBifunctor [LawfulFunctor G] [LawfulBifunctor F] :
    LawfulBifunctor (bicompr G F) := by
  constructor <;> intros <;> simp [bimap, functor_norm]
end Bicompr