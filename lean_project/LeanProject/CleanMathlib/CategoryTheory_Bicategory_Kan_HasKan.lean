import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Bicategory.Kan.IsKan
noncomputable section
namespace CategoryTheory
namespace Bicategory
universe w v u
variable {B : Type u} [Bicategory.{w, v} B] {a b c : B}
open Limits
section LeftKan
open LeftExtension
variable {f : a ⟶ b} {g : a ⟶ c}
class HasLeftKanExtension (f : a ⟶ b) (g : a ⟶ c) : Prop where
  hasInitial : HasInitial <| LeftExtension f g
theorem LeftExtension.IsKan.hasLeftKanExtension {t : LeftExtension f g} (H : IsKan t) :
    HasLeftKanExtension f g :=
  ⟨IsInitial.hasInitial H⟩
instance [HasLeftKanExtension f g] : HasInitial <| LeftExtension f g :=
  HasLeftKanExtension.hasInitial
def lanLeftExtension (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] : LeftExtension f g :=
  ⊥_ (LeftExtension f g)
def lan (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] : b ⟶ c :=
  (lanLeftExtension f g).extension
scoped infixr:90 "⁺ " => lan
@[simp]
theorem lanLeftExtension_extension (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] :
    (lanLeftExtension f g).extension = f⁺ g := rfl
def lanUnit (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] : g ⟶ f ≫ f⁺ g :=
  (lanLeftExtension f g).unit
@[simp]
theorem lanLeftExtension_unit (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] :
    (lanLeftExtension f g).unit = lanUnit f g := rfl
def lanIsKan (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] : (lanLeftExtension f g).IsKan :=
  initialIsInitial
variable {f : a ⟶ b} {g : a ⟶ c}
def lanDesc [HasLeftKanExtension f g] (s : LeftExtension f g) :
    f⁺ g ⟶ s.extension :=
  (lanIsKan f g).desc s
@[reassoc (attr := simp)]
theorem lanUnit_desc [HasLeftKanExtension f g] (s : LeftExtension f g) :
    lanUnit f g ≫ f ◁ lanDesc s = s.unit :=
  (lanIsKan f g).fac s
@[simp]
theorem lanIsKan_desc [HasLeftKanExtension f g] (s : LeftExtension f g) :
    (lanIsKan f g).desc s = lanDesc s :=
  rfl
theorem Lan.existsUnique [HasLeftKanExtension f g] (s : LeftExtension f g) :
    ∃! τ, lanUnit f g ≫ f ◁ τ = s.unit :=
  (lanIsKan f g).existsUnique _
class Lan.CommuteWith
    (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] {x : B} (h : c ⟶ x) : Prop where
  commute : Nonempty <| IsKan <| (lanLeftExtension f g).whisker h
namespace Lan.CommuteWith
theorem of_isKan_whisker [HasLeftKanExtension f g] (t : LeftExtension f g) {x : B} (h : c ⟶ x)
    (H : IsKan (t.whisker h)) (i : t.whisker h ≅ (lanLeftExtension f g).whisker h) :
    Lan.CommuteWith f g h :=
  ⟨⟨IsKan.ofIsoKan H i⟩⟩
theorem of_lan_comp_iso [HasLeftKanExtension f g]
    {x : B} {h : c ⟶ x} [HasLeftKanExtension f (g ≫ h)]
    (i : f⁺ (g ≫ h) ≅ f⁺ g ≫ h)
    (w : lanUnit f (g ≫ h) ≫ f ◁ i.hom = lanUnit f g ▷ h ≫ (α_ _ _ _).hom) :
    Lan.CommuteWith f g h :=
  ⟨⟨(lanIsKan f (g ≫ h)).ofIsoKan <| StructuredArrow.isoMk i⟩⟩
variable (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g]
variable {x : B} (h : c ⟶ x) [Lan.CommuteWith f g h]
def isKan : IsKan <| (lanLeftExtension f g).whisker h := Classical.choice Lan.CommuteWith.commute
instance : HasLeftKanExtension f (g ≫ h) := (Lan.CommuteWith.isKan f g h).hasLeftKanExtension
def isKanWhisker
    (t : LeftExtension f g) (H : IsKan t) {x : B} (h : c ⟶ x) [Lan.CommuteWith f g h] :
    IsKan (t.whisker h) :=
  IsKan.whiskerOfCommute (lanLeftExtension f g) t (IsKan.uniqueUpToIso (lanIsKan f g) H) h
    (isKan f g h)
def lanCompIsoWhisker : lanLeftExtension f (g ≫ h) ≅ (lanLeftExtension f g).whisker h :=
  IsKan.uniqueUpToIso (lanIsKan f (g ≫ h)) (Lan.CommuteWith.isKan f g h)
@[simp]
theorem lanCompIsoWhisker_hom_right :
    (lanCompIsoWhisker f g h).hom.right = lanDesc ((lanLeftExtension f g).whisker h) :=
  rfl
@[simp]
theorem lanCompIsoWhisker_inv_right :
    (lanCompIsoWhisker f g h).inv.right = (isKan f g h).desc (lanLeftExtension f (g ≫ h)) :=
  rfl
@[simps!]
def lanCompIso : f⁺ (g ≫ h) ≅ f⁺ g ≫ h := Comma.rightIso <| lanCompIsoWhisker f g h
end Lan.CommuteWith
class HasAbsLeftKanExtension (f : a ⟶ b) (g : a ⟶ c) extends HasLeftKanExtension f g : Prop where
  commute {x : B} (h : c ⟶ x) : Lan.CommuteWith f g h
instance [HasAbsLeftKanExtension f g] {x : B} (h : c ⟶ x) : Lan.CommuteWith f g h :=
  HasAbsLeftKanExtension.commute h
theorem LeftExtension.IsAbsKan.hasAbsLeftKanExtension {t : LeftExtension f g} (H : IsAbsKan t) :
    HasAbsLeftKanExtension f g :=
  have : HasLeftKanExtension f g := H.isKan.hasLeftKanExtension
  ⟨fun h ↦ ⟨⟨H.ofIsoAbsKan (IsKan.uniqueUpToIso H.isKan (lanIsKan f g)) h⟩⟩⟩
end LeftKan
section LeftLift
open LeftLift
variable {f : b ⟶ a} {g : c ⟶ a}
class HasLeftKanLift (f : b ⟶ a) (g : c ⟶ a) : Prop where mk' ::
  hasInitial : HasInitial <| LeftLift f g
theorem LeftLift.IsKan.hasLeftKanLift {t : LeftLift f g} (H : IsKan t) : HasLeftKanLift f g :=
  ⟨IsInitial.hasInitial H⟩
instance [HasLeftKanLift f g] : HasInitial <| LeftLift f g := HasLeftKanLift.hasInitial
def lanLiftLeftLift (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] : LeftLift f g :=
  ⊥_ (LeftLift f g)
def lanLift (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] : c ⟶ b :=
  (lanLiftLeftLift f g).lift
scoped infixr:90 "₊ " => lanLift
@[simp]
theorem lanLiftLeftLift_lift (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] :
    (lanLiftLeftLift f g).lift = f₊ g := rfl
def lanLiftUnit (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] : g ⟶ f₊ g ≫ f :=
  (lanLiftLeftLift f g).unit
@[simp]
theorem lanLiftLeftLift_unit (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] :
    (lanLiftLeftLift f g).unit = lanLiftUnit f g := rfl
def lanLiftIsKan (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] : (lanLiftLeftLift f g).IsKan :=
  initialIsInitial
variable {f : b ⟶ a} {g : c ⟶ a}
def lanLiftDesc [HasLeftKanLift f g] (s : LeftLift f g) :
    f ₊ g ⟶ s.lift :=
  (lanLiftIsKan f g).desc s
@[reassoc (attr := simp)]
theorem lanLiftUnit_desc [HasLeftKanLift f g] (s : LeftLift f g) :
    lanLiftUnit f g ≫ lanLiftDesc s ▷ f = s.unit :=
  (lanLiftIsKan f g).fac s
@[simp]
theorem lanLiftIsKan_desc [HasLeftKanLift f g] (s : LeftLift f g) :
    (lanLiftIsKan f g).desc s = lanLiftDesc s :=
  rfl
theorem LanLift.existsUnique [HasLeftKanLift f g] (s : LeftLift f g) :
    ∃! τ, lanLiftUnit f g ≫ τ ▷ f = s.unit :=
  (lanLiftIsKan f g).existsUnique _
class LanLift.CommuteWith
    (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] {x : B} (h : x ⟶ c) : Prop where
  commute : Nonempty <| IsKan <| (lanLiftLeftLift f g).whisker h
namespace LanLift.CommuteWith
theorem of_isKan_whisker [HasLeftKanLift f g] (t : LeftLift f g) {x : B} (h : x ⟶ c)
    (H : IsKan (t.whisker h)) (i : t.whisker h ≅ (lanLiftLeftLift f g).whisker h) :
    LanLift.CommuteWith f g h :=
  ⟨⟨IsKan.ofIsoKan H i⟩⟩
theorem of_lanLift_comp_iso [HasLeftKanLift f g]
    {x : B} {h : x ⟶ c} [HasLeftKanLift f (h ≫ g)]
    (i : f₊ (h ≫ g) ≅ h ≫ f₊ g)
    (w : lanLiftUnit f (h ≫ g) ≫ i.hom ▷ f = h ◁ lanLiftUnit f g ≫ (α_ _ _ _).inv) :
    LanLift.CommuteWith f g h :=
  ⟨⟨(lanLiftIsKan f (h ≫ g)).ofIsoKan <| StructuredArrow.isoMk i⟩⟩
variable (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g]
variable {x : B} (h : x ⟶ c) [LanLift.CommuteWith f g h]
def isKan : IsKan <| (lanLiftLeftLift f g).whisker h :=
    Classical.choice LanLift.CommuteWith.commute
instance : HasLeftKanLift f (h ≫ g) := (LanLift.CommuteWith.isKan f g h).hasLeftKanLift
def isKanWhisker
    (t : LeftLift f g) (H : IsKan t) {x : B} (h : x ⟶ c) [LanLift.CommuteWith f g h] :
    IsKan (t.whisker h) :=
  IsKan.whiskerOfCommute (lanLiftLeftLift f g) t (IsKan.uniqueUpToIso (lanLiftIsKan f g) H) h
    (isKan f g h)
def lanLiftCompIsoWhisker :
    lanLiftLeftLift f (h ≫ g) ≅ (lanLiftLeftLift f g).whisker h :=
  IsKan.uniqueUpToIso (lanLiftIsKan f (h ≫ g)) (LanLift.CommuteWith.isKan f g h)
@[simp]
theorem lanLiftCompIsoWhisker_hom_right :
    (lanLiftCompIsoWhisker f g h).hom.right = lanLiftDesc ((lanLiftLeftLift f g).whisker h) :=
  rfl
@[simp]
theorem lanLiftCompIsoWhisker_inv_right :
    (lanLiftCompIsoWhisker f g h).inv.right = (isKan f g h).desc (lanLiftLeftLift f (h ≫ g)) :=
  rfl
@[simps!]
def lanLiftCompIso : f₊ (h ≫ g) ≅ h ≫ f₊ g := Comma.rightIso <| lanLiftCompIsoWhisker f g h
end LanLift.CommuteWith
class HasAbsLeftKanLift (f : b ⟶ a) (g : c ⟶ a) extends HasLeftKanLift f g : Prop where
  commute : ∀ {x : B} (h : x ⟶ c), LanLift.CommuteWith f g h
instance [HasAbsLeftKanLift f g] {x : B} (h : x ⟶ c) : LanLift.CommuteWith f g h :=
  HasAbsLeftKanLift.commute h
theorem LeftLift.IsAbsKan.hasAbsLeftKanLift {t : LeftLift f g} (H : IsAbsKan t) :
    HasAbsLeftKanLift f g :=
  have : HasLeftKanLift f g := H.isKan.hasLeftKanLift
  ⟨fun h ↦ ⟨⟨H.ofIsoAbsKan (IsKan.uniqueUpToIso H.isKan (lanLiftIsKan f g)) h⟩⟩⟩
end LeftLift
end Bicategory
end CategoryTheory