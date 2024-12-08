import Mathlib.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
namespace CategoryTheory
namespace Bicategory
universe w v u
variable {B : Type u} [Bicategory.{w, v} B] {a b c : B}
abbrev LeftExtension (f : a ⟶ b) (g : a ⟶ c) := StructuredArrow g (precomp _ f)
namespace LeftExtension
variable {f : a ⟶ b} {g : a ⟶ c}
abbrev extension (t : LeftExtension f g) : b ⟶ c := t.right
abbrev unit (t : LeftExtension f g) : g ⟶ f ≫ t.extension := t.hom
abbrev mk (h : b ⟶ c) (unit : g ⟶ f ≫ h) : LeftExtension f g :=
  StructuredArrow.mk unit
variable {s t : LeftExtension f g}
abbrev homMk (η : s.extension ⟶ t.extension) (w : s.unit ≫ f ◁ η = t.unit := by aesop_cat) :
    s ⟶ t :=
  StructuredArrow.homMk η w
@[reassoc (attr := simp)]
theorem w (η : s ⟶ t) : s.unit ≫ f ◁ η.right = t.unit :=
  StructuredArrow.w η
def alongId (g : a ⟶ c) : LeftExtension (𝟙 a) g := .mk _ (λ_ g).inv
instance : Inhabited (LeftExtension (𝟙 a) g) := ⟨alongId g⟩
@[simps!]
def ofCompId (t : LeftExtension f (g ≫ 𝟙 c)) : LeftExtension f g :=
  mk (extension t) ((ρ_ g).inv ≫ unit t)
def whisker (t : LeftExtension f g) {x : B} (h : c ⟶ x) : LeftExtension f (g ≫ h) :=
  .mk _ <| t.unit ▷ h ≫ (α_ _ _ _).hom
@[simp]
theorem whisker_extension (t : LeftExtension f g) {x : B} (h : c ⟶ x) :
    (t.whisker h).extension = t.extension ≫ h :=
  rfl
@[simp]
theorem whisker_unit (t : LeftExtension f g) {x : B} (h : c ⟶ x) :
    (t.whisker h).unit = t.unit ▷ h ≫ (α_ f t.extension h).hom :=
  rfl
@[simps]
def whiskering {x : B} (h : c ⟶ x) : LeftExtension f g ⥤ LeftExtension f (g ≫ h) where
  obj t := t.whisker h
  map η := LeftExtension.homMk (η.right ▷ h) <| by
    simp [- LeftExtension.w, ← LeftExtension.w η]
@[simps! right]
def whiskerIdCancel
    (s : LeftExtension f (g ≫ 𝟙 c)) {t : LeftExtension f g} (τ : s ⟶ t.whisker (𝟙 c)) :
    s.ofCompId ⟶ t :=
  LeftExtension.homMk (τ.right ≫ (ρ_ _).hom)
@[simps! right]
def whiskerHom (i : s ⟶ t) {x : B} (h : c ⟶ x) :
    s.whisker h ⟶ t.whisker h :=
  StructuredArrow.homMk (i.right ▷ h) <| by
    rw [← cancel_mono (α_ _ _ _).inv]
    calc
      _ = (unit s ≫ f ◁ i.right) ▷ h := by simp [- LeftExtension.w]
      _ = unit t ▷ h := congrArg (· ▷ h) (LeftExtension.w i)
      _ = _ := by simp
def whiskerIso (i : s ≅ t) {x : B} (h : c ⟶ x) :
    s.whisker h ≅ t.whisker h :=
  Iso.mk (whiskerHom i.hom h) (whiskerHom i.inv h)
    (StructuredArrow.hom_ext _ _ <|
      calc
        _ = (i.hom ≫ i.inv).right ▷ h := by simp [- Iso.hom_inv_id]
        _ = 𝟙 _ := by simp [Iso.hom_inv_id])
    (StructuredArrow.hom_ext _ _ <|
      calc
        _ = (i.inv ≫ i.hom).right ▷ h := by simp [- Iso.inv_hom_id]
        _ = 𝟙 _ := by simp [Iso.inv_hom_id])
@[simps! hom_right inv_right]
def whiskerOfCompIdIsoSelf (t : LeftExtension f g) : (t.whisker (𝟙 c)).ofCompId ≅ t :=
  StructuredArrow.isoMk (ρ_ (t.extension))
end LeftExtension
abbrev LeftLift (f : b ⟶ a) (g : c ⟶ a) := StructuredArrow g (postcomp _ f)
namespace LeftLift
variable {f : b ⟶ a} {g : c ⟶ a}
abbrev lift (t : LeftLift f g) : c ⟶ b := t.right
abbrev unit (t : LeftLift f g) : g ⟶ t.lift ≫ f := t.hom
abbrev mk (h : c ⟶ b) (unit : g ⟶ h ≫ f) : LeftLift f g :=
  StructuredArrow.mk unit
variable {s t : LeftLift f g}
abbrev homMk (η : s.lift ⟶ t.lift) (w : s.unit ≫ η ▷ f = t.unit := by aesop_cat) :
    s ⟶ t :=
  StructuredArrow.homMk η w
@[reassoc (attr := simp)]
theorem w (h : s ⟶ t) : s.unit ≫ h.right ▷ f = t.unit :=
  StructuredArrow.w h
def alongId (g : c ⟶ a) : LeftLift (𝟙 a) g := .mk _ (ρ_ g).inv
instance : Inhabited (LeftLift (𝟙 a) g) := ⟨alongId g⟩
@[simps!]
def ofIdComp (t : LeftLift f (𝟙 c ≫ g)) : LeftLift f g :=
  mk (lift t) ((λ_ _).inv ≫ unit t)
def whisker (t : LeftLift f g) {x : B} (h : x ⟶ c) : LeftLift f (h ≫ g) :=
  .mk _ <| h ◁ t.unit ≫ (α_ _ _ _).inv
@[simp]
theorem whisker_lift (t : LeftLift f g) {x : B} (h : x ⟶ c) :
    (t.whisker h).lift = h ≫ t.lift :=
  rfl
@[simp]
theorem whisker_unit (t : LeftLift f g) {x : B} (h : x ⟶ c) :
    (t.whisker h).unit = h ◁ t.unit ≫ (α_ h t.lift f).inv :=
  rfl
@[simps]
def whiskering {x : B} (h : x ⟶ c) : LeftLift f g ⥤ LeftLift f (h ≫ g) where
  obj t := t.whisker h
  map η := LeftLift.homMk (h ◁ η.right) <| by
    dsimp only [whisker_lift, whisker_unit]
    rw [← LeftLift.w η]
    simp [- LeftLift.w]
@[simps! right]
def whiskerIdCancel
    (s : LeftLift f (𝟙 c ≫ g)) {t : LeftLift f g} (τ : s ⟶ t.whisker (𝟙 c)) :
    s.ofIdComp ⟶ t :=
  LeftLift.homMk (τ.right ≫ (λ_ _).hom)
@[simps! right]
def whiskerHom (i : s ⟶ t) {x : B} (h : x ⟶ c) :
    s.whisker h ⟶ t.whisker h :=
  StructuredArrow.homMk (h ◁ i.right) <| by
    rw [← cancel_mono (α_ h _ _).hom]
    calc
      _ = h ◁ (unit s ≫ i.right ▷ f) := by simp [- LeftLift.w]
      _ = h ◁ unit t := congrArg (h ◁ ·) (LeftLift.w i)
      _ = _ := by simp
def whiskerIso (i : s ≅ t) {x : B} (h : x ⟶ c) :
    s.whisker h ≅ t.whisker h :=
  Iso.mk (whiskerHom i.hom h) (whiskerHom i.inv h)
    (StructuredArrow.hom_ext _ _ <|
      calc
        _ = h ◁ (i.hom ≫ i.inv).right := by simp [- Iso.hom_inv_id]
        _ = 𝟙 _ := by simp [Iso.hom_inv_id])
    (StructuredArrow.hom_ext _ _ <|
      calc
        _ = h ◁ (i.inv ≫ i.hom).right := by simp [- Iso.inv_hom_id]
        _ = 𝟙 _ := by simp [Iso.inv_hom_id])
@[simps! hom_right inv_right]
def whiskerOfIdCompIsoSelf (t : LeftLift f g) : (t.whisker (𝟙 c)).ofIdComp ≅ t :=
  StructuredArrow.isoMk (λ_ (lift t))
end LeftLift
abbrev RightExtension (f : a ⟶ b) (g : a ⟶ c) := CostructuredArrow (precomp _ f) g
namespace RightExtension
variable {f : a ⟶ b} {g : a ⟶ c}
abbrev extension (t : RightExtension f g) : b ⟶ c := t.left
abbrev counit (t : RightExtension f g) : f ≫ t.extension ⟶ g := t.hom
abbrev mk (h : b ⟶ c) (counit : f ≫ h ⟶ g) : RightExtension f g :=
  CostructuredArrow.mk counit
abbrev homMk {s t : RightExtension f g} (η : s.extension ⟶ t.extension)
    (w : f ◁ η ≫ t.counit = s.counit) : s ⟶ t :=
  CostructuredArrow.homMk η w
@[reassoc (attr := simp)]
theorem w {s t : RightExtension f g} (η : s ⟶ t) :
    f ◁ η.left ≫ t.counit = s.counit :=
  CostructuredArrow.w η
def alongId (g : a ⟶ c) : RightExtension (𝟙 a) g := .mk _ (λ_ g).hom
instance : Inhabited (RightExtension (𝟙 a) g) := ⟨alongId g⟩
end RightExtension
abbrev RightLift (f : b ⟶ a) (g : c ⟶ a) := CostructuredArrow (postcomp _ f) g
namespace RightLift
variable {f : b ⟶ a} {g : c ⟶ a}
abbrev lift (t : RightLift f g) : c ⟶ b := t.left
abbrev counit (t : RightLift f g) : t.lift ≫ f ⟶ g := t.hom
abbrev mk (h : c ⟶ b) (counit : h ≫ f ⟶ g) : RightLift f g :=
  CostructuredArrow.mk counit
abbrev homMk {s t : RightLift f g} (η : s.lift ⟶ t.lift) (w : η ▷ f ≫ t.counit = s.counit) :
    s ⟶ t :=
  CostructuredArrow.homMk η w
@[reassoc (attr := simp)]
theorem w {s t : RightLift f g} (h : s ⟶ t) :
    h.left ▷ f ≫ t.counit = s.counit :=
  CostructuredArrow.w h
def alongId (g : c ⟶ a) : RightLift (𝟙 a) g := .mk _ (ρ_ g).hom
instance : Inhabited (RightLift (𝟙 a) g) := ⟨alongId g⟩
end RightLift
end Bicategory
end CategoryTheory