import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
universe w w₁ w₂ v v₁ v₂ u u₁ u₂
namespace CategoryTheory
open Category Bicategory
open Bicategory
def FreeBicategory (B : Type u) :=
  B
instance (B : Type u) : ∀ [Inhabited B], Inhabited (FreeBicategory B) := by
  intro h
  exact id h
namespace FreeBicategory
section
variable {B : Type u} [Quiver.{v + 1} B]
inductive Hom : B → B → Type max u v
  | of {a b : B} (f : a ⟶ b) : Hom a b
  | id (a : B) : Hom a a
  | comp {a b c : B} (f : Hom a b) (g : Hom b c) : Hom a c
instance (a b : B) [Inhabited (a ⟶ b)] : Inhabited (Hom a b) :=
  ⟨Hom.of default⟩
instance quiver : Quiver.{max u v + 1} (FreeBicategory B) where
  Hom := fun a b : B => Hom a b
instance categoryStruct : CategoryStruct.{max u v} (FreeBicategory B) where
  id   := fun a : B => Hom.id a
  comp := @fun _ _ _ => Hom.comp
inductive Hom₂ : ∀ {a b : FreeBicategory B}, (a ⟶ b) → (a ⟶ b) → Type max u v
  | id {a b} (f : a ⟶ b) : Hom₂ f f
  | vcomp {a b} {f g h : a ⟶ b} (η : Hom₂ f g) (θ : Hom₂ g h) : Hom₂ f h
  | whisker_left {a b c} (f : a ⟶ b) {g h : b ⟶ c} (η : Hom₂ g h) :
      Hom₂ (f ≫ g) (f ≫ h)
  | whisker_right {a b c} {f g : a ⟶ b} (h : b ⟶ c) (η : Hom₂ f g) : Hom₂ (f.comp h) (g.comp h)
  | associator {a b c d} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
      Hom₂ ((f ≫ g) ≫ h) (f ≫ (g ≫ h))
  | associator_inv {a b c d} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
      Hom₂ (f ≫ (g ≫ h)) ((f ≫ g) ≫ h)
  | right_unitor {a b} (f : a ⟶ b) : Hom₂ (f ≫ (𝟙 b)) f
  | right_unitor_inv {a b} (f : a ⟶ b) : Hom₂ f (f ≫ (𝟙 b))
  | left_unitor {a b} (f : a ⟶ b) : Hom₂ ((𝟙 a) ≫ f) f
  | left_unitor_inv {a b} (f : a ⟶ b) : Hom₂ f ((𝟙 a) ≫ f)
section
local infixr:0 " ≫ " => Hom₂.vcomp
local notation "𝟙" => Hom₂.id
local notation f " ◁ " η => Hom₂.whisker_left f η
local notation η " ▷ " h => Hom₂.whisker_right h η
local notation "α_" => Hom₂.associator
local notation "λ_" => Hom₂.left_unitor
local notation "ρ_" => Hom₂.right_unitor
local notation "α⁻¹_" => Hom₂.associator_inv
local notation "λ⁻¹_" => Hom₂.left_unitor_inv
local notation "ρ⁻¹_" => Hom₂.right_unitor_inv
inductive Rel : ∀ {a b : FreeBicategory B} {f g : a ⟶ b}, Hom₂ f g → Hom₂ f g → Prop
  | vcomp_right {a b} {f g h : Hom a b} (η : Hom₂ f g) (θ₁ θ₂ : Hom₂ g h) :
      Rel θ₁ θ₂ → Rel (η ≫ θ₁) (η ≫ θ₂)
  | vcomp_left {a b} {f g h : Hom a b} (η₁ η₂ : Hom₂ f g) (θ : Hom₂ g h) :
      Rel η₁ η₂ → Rel (η₁ ≫ θ) (η₂ ≫ θ)
  | id_comp {a b} {f g : Hom a b} (η : Hom₂ f g) : Rel (𝟙 f ≫ η) η
  | comp_id {a b} {f g : Hom a b} (η : Hom₂ f g) : Rel (η ≫ 𝟙 g) η
  | assoc {a b} {f g h i : Hom a b} (η : Hom₂ f g) (θ : Hom₂ g h) (ι : Hom₂ h i) :
      Rel ((η ≫ θ) ≫ ι) (η ≫ θ ≫ ι)
  | whisker_left {a b c} (f : Hom a b) (g h : Hom b c) (η η' : Hom₂ g h) :
      Rel η η' → Rel (f ◁ η) (f ◁ η')
  | whisker_left_id {a b c} (f : Hom a b) (g : Hom b c) : Rel (f ◁ 𝟙 g) (𝟙 (f.comp g))
  | whisker_left_comp {a b c} (f : Hom a b) {g h i : Hom b c} (η : Hom₂ g h) (θ : Hom₂ h i) :
      Rel (f ◁ η ≫ θ) ((f ◁ η) ≫ f ◁ θ)
  | id_whisker_left {a b} {f g : Hom a b} (η : Hom₂ f g) : Rel (Hom.id a ◁ η) (λ_ f ≫ η ≫ λ⁻¹_ g)
  | comp_whisker_left {a b c d} (f : Hom a b) (g : Hom b c) {h h' : Hom c d} (η : Hom₂ h h') :
     Rel (f.comp g ◁ η) (α_ f g h ≫ (f ◁ g ◁ η) ≫ α⁻¹_ f g h')
  | whisker_right {a b c} (f g : Hom a b) (h : Hom b c) (η η' : Hom₂ f g) :
      Rel η η' → Rel (η ▷ h) (η' ▷ h)
  | id_whisker_right {a b c} (f : Hom a b) (g : Hom b c) : Rel (𝟙 f ▷ g) (𝟙 (f.comp g))
  | comp_whisker_right {a b c} {f g h : Hom a b} (i : Hom b c) (η : Hom₂ f g) (θ : Hom₂ g h) :
      Rel ((η ≫ θ) ▷ i) ((η ▷ i) ≫ θ ▷ i)
  | whisker_right_id {a b} {f g : Hom a b} (η : Hom₂ f g) : Rel (η ▷ Hom.id b) (ρ_ f ≫ η ≫ ρ⁻¹_ g)
  | whisker_right_comp {a b c d} {f f' : Hom a b} (g : Hom b c) (h : Hom c d) (η : Hom₂ f f') :
      Rel (η ▷ g.comp h) (α⁻¹_ f g h ≫ ((η ▷ g) ▷ h) ≫ α_ f' g h)
  | whisker_assoc {a b c d} (f : Hom a b) {g g' : Hom b c} (η : Hom₂ g g') (h : Hom c d) :
      Rel ((f ◁ η) ▷ h) (α_ f g h ≫ (f ◁ η ▷ h) ≫ α⁻¹_ f g' h)
  | whisker_exchange {a b c} {f g : Hom a b} {h i : Hom b c} (η : Hom₂ f g) (θ : Hom₂ h i) :
      Rel ((f ◁ θ) ≫ η ▷ i) ((η ▷ h) ≫ g ◁ θ)
  | associator_hom_inv {a b c d} (f : Hom a b) (g : Hom b c) (h : Hom c d) :
      Rel (α_ f g h ≫ α⁻¹_ f g h) (𝟙 ((f.comp g).comp h))
  | associator_inv_hom {a b c d} (f : Hom a b) (g : Hom b c) (h : Hom c d) :
      Rel (α⁻¹_ f g h ≫ α_ f g h) (𝟙 (f.comp (g.comp h)))
  | left_unitor_hom_inv {a b} (f : Hom a b) : Rel (λ_ f ≫ λ⁻¹_ f) (𝟙 ((Hom.id a).comp f))
  | left_unitor_inv_hom {a b} (f : Hom a b) : Rel (λ⁻¹_ f ≫ λ_ f) (𝟙 f)
  | right_unitor_hom_inv {a b} (f : Hom a b) : Rel (ρ_ f ≫ ρ⁻¹_ f) (𝟙 (f.comp (Hom.id b)))
  | right_unitor_inv_hom {a b} (f : Hom a b) : Rel (ρ⁻¹_ f ≫ ρ_ f) (𝟙 f)
  | pentagon {a b c d e} (f : Hom a b) (g : Hom b c) (h : Hom c d) (i : Hom d e) :
      Rel ((α_ f g h ▷ i) ≫ α_ f (g.comp h) i ≫ f ◁ α_ g h i)
        (α_ (f.comp g) h i ≫ α_ f g (h.comp i))
  | triangle {a b c} (f : Hom a b) (g : Hom b c) : Rel (α_ f (Hom.id b) g ≫ f ◁ λ_ g) (ρ_ f ▷ g)
end
instance homCategory (a b : FreeBicategory B) : Category (a ⟶ b) where
  Hom f g := Quot (@Rel _ _ a b f g)
  id f := Quot.mk Rel (Hom₂.id f)
  comp := @fun _ _ _ => Quot.map₂ Hom₂.vcomp Rel.vcomp_right Rel.vcomp_left
  id_comp := by
    rintro f g ⟨η⟩
    exact Quot.sound (Rel.id_comp η)
  comp_id := by
    rintro f g ⟨η⟩
    exact Quot.sound (Rel.comp_id η)
  assoc := by
    rintro f g h i ⟨η⟩ ⟨θ⟩ ⟨ι⟩
    exact Quot.sound (Rel.assoc η θ ι)
instance bicategory : Bicategory (FreeBicategory B) where
  homCategory := @fun (a b : B) => FreeBicategory.homCategory a b
  whiskerLeft := @fun _ _ _ f g h η => Quot.map (Hom₂.whisker_left f) (Rel.whisker_left f g h) η
  whiskerLeft_id := @fun _ _ _ f g => Quot.sound (Rel.whisker_left_id f g)
  associator := @fun _ _ _ _ f g h =>
    { hom := Quot.mk Rel (Hom₂.associator f g h)
      inv := Quot.mk Rel (Hom₂.associator_inv f g h)
      hom_inv_id := Quot.sound (Rel.associator_hom_inv f g h)
      inv_hom_id := Quot.sound (Rel.associator_inv_hom f g h) }
  leftUnitor := @fun _ _ f =>
    { hom := Quot.mk Rel (Hom₂.left_unitor f)
      inv := Quot.mk Rel (Hom₂.left_unitor_inv f)
      hom_inv_id := Quot.sound (Rel.left_unitor_hom_inv f)
      inv_hom_id := Quot.sound (Rel.left_unitor_inv_hom f) }
  rightUnitor := @fun _ _ f =>
    { hom := Quot.mk Rel (Hom₂.right_unitor f)
      inv := Quot.mk Rel (Hom₂.right_unitor_inv f)
      hom_inv_id := Quot.sound (Rel.right_unitor_hom_inv f)
      inv_hom_id := Quot.sound (Rel.right_unitor_inv_hom f) }
  whiskerLeft_comp := by
    rintro a b c f g h i ⟨η⟩ ⟨θ⟩
    exact Quot.sound (Rel.whisker_left_comp f η θ)
  id_whiskerLeft := by
    rintro a b f g ⟨η⟩
    exact Quot.sound (Rel.id_whisker_left η)
  comp_whiskerLeft := by
    rintro a b c d f g h h' ⟨η⟩
    exact Quot.sound (Rel.comp_whisker_left f g η)
  whiskerRight := @fun _ _ _ f g η h => Quot.map (Hom₂.whisker_right h) (Rel.whisker_right f g h) η
  id_whiskerRight := @fun _ _ _ f g => Quot.sound (Rel.id_whisker_right f g)
  comp_whiskerRight := by
    rintro a b c f g h ⟨η⟩ ⟨θ⟩ i
    exact Quot.sound (Rel.comp_whisker_right i η θ)
  whiskerRight_id := by
    rintro a b f g ⟨η⟩
    exact Quot.sound (Rel.whisker_right_id η)
  whiskerRight_comp := by
    rintro a b c d f f' ⟨η⟩ g h
    exact Quot.sound (Rel.whisker_right_comp g h η)
  whisker_assoc := by
    rintro a b c d f g g' ⟨η⟩ h
    exact Quot.sound (Rel.whisker_assoc f η h)
  whisker_exchange := by
    rintro a b c f g h i ⟨η⟩ ⟨θ⟩
    exact Quot.sound (Rel.whisker_exchange η θ)
  pentagon := @fun _ _ _ _ _ f g h i => Quot.sound (Rel.pentagon f g h i)
  triangle := @fun _ _ _ f g => Quot.sound (Rel.triangle f g)
variable {a b c d : FreeBicategory B}
abbrev Hom₂.mk {f g : a ⟶ b} (η : Hom₂ f g) : f ⟶ g :=
  Quot.mk Rel η
@[simp]
theorem mk_vcomp {f g h : a ⟶ b} (η : Hom₂ f g) (θ : Hom₂ g h) :
    (η.vcomp θ).mk = (η.mk ≫ θ.mk : f ⟶ h) :=
  rfl
@[simp]
theorem mk_whisker_left (f : a ⟶ b) {g h : b ⟶ c} (η : Hom₂ g h) :
    (Hom₂.whisker_left f η).mk = (f ◁ η.mk : f ≫ g ⟶ f ≫ h) :=
  rfl
@[simp]
theorem mk_whisker_right {f g : a ⟶ b} (η : Hom₂ f g) (h : b ⟶ c) :
    (Hom₂.whisker_right h η).mk = (η.mk ▷ h : f ≫ h ⟶ g ≫ h) :=
  rfl
variable (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
theorem comp_def : Hom.comp f g = f ≫ g :=
  rfl
@[simp]
theorem mk_id : Quot.mk _ (Hom₂.id f) = 𝟙 f :=
  rfl
@[simp]
theorem mk_associator_hom : Quot.mk _ (Hom₂.associator f g h) = (α_ f g h).hom :=
  rfl
@[simp]
theorem mk_associator_inv : Quot.mk _ (Hom₂.associator_inv f g h) = (α_ f g h).inv :=
  rfl
@[simp]
theorem mk_left_unitor_hom : Quot.mk _ (Hom₂.left_unitor f) = (λ_ f).hom :=
  rfl
@[simp]
theorem mk_left_unitor_inv : Quot.mk _ (Hom₂.left_unitor_inv f) = (λ_ f).inv :=
  rfl
@[simp]
theorem mk_right_unitor_hom : Quot.mk _ (Hom₂.right_unitor f) = (ρ_ f).hom :=
  rfl
@[simp]
theorem mk_right_unitor_inv : Quot.mk _ (Hom₂.right_unitor_inv f) = (ρ_ f).inv :=
  rfl
@[simps]
def of : Prefunctor B (FreeBicategory B) where
  obj := id
  map := @fun _ _ => Hom.of
end
section
variable {B : Type u₁} [Quiver.{v₁ + 1} B] {C : Type u₂} [CategoryStruct.{v₂} C]
variable (F : Prefunctor B C)
@[simp]
def liftHom : ∀ {a b : FreeBicategory B}, (a ⟶ b) → (F.obj a ⟶ F.obj b)
  | _, _, Hom.of f => F.map f
  | _, _, Hom.id a => 𝟙 (F.obj a)
  | _, _, Hom.comp f g => liftHom f ≫ liftHom g
@[simp]
theorem liftHom_id (a : FreeBicategory B) : liftHom F (𝟙 a) = 𝟙 (F.obj a) :=
  rfl
@[simp]
theorem liftHom_comp {a b c : FreeBicategory B} (f : a ⟶ b) (g : b ⟶ c) :
    liftHom F (f ≫ g) = liftHom F f ≫ liftHom F g :=
  rfl
end
section
variable {B : Type u₁} [Quiver.{v₁ + 1} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
variable (F : Prefunctor B C)
def liftHom₂ : ∀ {a b : FreeBicategory B} {f g : a ⟶ b}, Hom₂ f g → (liftHom F f ⟶ liftHom F g)
  | _, _, _, _, Hom₂.id _ => 𝟙 _
  | _, _, _, _, Hom₂.associator _ _ _ => (α_ _ _ _).hom
  | _, _, _, _, Hom₂.associator_inv _ _ _ => (α_ _ _ _).inv
  | _, _, _, _, Hom₂.left_unitor _ => (λ_ _).hom
  | _, _, _, _, Hom₂.left_unitor_inv _ => (λ_ _).inv
  | _, _, _, _, Hom₂.right_unitor _ => (ρ_ _).hom
  | _, _, _, _, Hom₂.right_unitor_inv _ => (ρ_ _).inv
  | _, _, _, _, Hom₂.vcomp η θ => liftHom₂ η ≫ liftHom₂ θ
  | _, _, _, _, Hom₂.whisker_left f η => liftHom F f ◁ liftHom₂ η
  | _, _, _, _, Hom₂.whisker_right h η => liftHom₂ η ▷ liftHom F h
attribute [local simp] whisker_exchange
theorem liftHom₂_congr {a b : FreeBicategory B} {f g : a ⟶ b} {η θ : Hom₂ f g} (H : Rel η θ) :
    liftHom₂ F η = liftHom₂ F θ := by induction H <;> (dsimp [liftHom₂]; aesop_cat)
@[simps]
def lift : Pseudofunctor (FreeBicategory B) C where
  obj := F.obj
  map := liftHom F
  mapId _ := Iso.refl _
  mapComp _ _ := Iso.refl _
  map₂ := Quot.lift (liftHom₂ F) fun _ _ H => liftHom₂_congr F H
  map₂_comp := by
    intros a b f g h η θ
    induction η using Quot.rec
    · induction θ using Quot.rec <;> rfl
    · rfl
  map₂_whisker_left := by
    intro a b c f g h η
    induction η using Quot.rec
    · aesop_cat
    · rfl
  map₂_whisker_right := by intro _ _ _ _ _ η h; dsimp; induction η using Quot.rec <;> aesop_cat
end
end FreeBicategory
end CategoryTheory