import Mathlib.CategoryTheory.Bicategory.Extension
namespace CategoryTheory
namespace Bicategory
universe w v u
variable {B : Type u} [Bicategory.{w, v} B] {a b c : B}
namespace LeftExtension
variable {f : a ⟶ b} {g : a ⟶ c}
abbrev IsKan (t : LeftExtension f g) := t.IsUniversal
abbrev IsAbsKan (t : LeftExtension f g) :=
  ∀ {x : B} (h : c ⟶ x), IsKan (t.whisker h)
namespace IsKan
variable {s t : LeftExtension f g}
abbrev mk (desc : ∀ s, t ⟶ s) (w : ∀ s τ, τ = desc s) :
    IsKan t :=
  .ofUniqueHom desc w
abbrev desc (H : IsKan t) (s : LeftExtension f g) : t.extension ⟶ s.extension :=
  StructuredArrow.IsUniversal.desc H s
@[reassoc (attr := simp)]
theorem fac (H : IsKan t) (s : LeftExtension f g) :
    t.unit ≫ f ◁ H.desc s = s.unit :=
  StructuredArrow.IsUniversal.fac H s
theorem hom_ext (H : IsKan t) {k : b ⟶ c} {τ τ' : t.extension ⟶ k}
    (w : t.unit ≫ f ◁ τ = t.unit ≫ f ◁ τ') : τ = τ' :=
  StructuredArrow.IsUniversal.hom_ext H w
def uniqueUpToIso (P : IsKan s) (Q : IsKan t) : s ≅ t :=
  Limits.IsInitial.uniqueUpToIso P Q
@[simp]
theorem uniqueUpToIso_hom_right (P : IsKan s) (Q : IsKan t) :
    (uniqueUpToIso P Q).hom.right = P.desc t := rfl
@[simp]
theorem uniqueUpToIso_inv_right (P : IsKan s) (Q : IsKan t) :
    (uniqueUpToIso P Q).inv.right = Q.desc s := rfl
def ofIsoKan (P : IsKan s) (i : s ≅ t) : IsKan t :=
  Limits.IsInitial.ofIso P i
def ofCompId (t : LeftExtension f (g ≫ 𝟙 c)) (P : IsKan t) : IsKan t.ofCompId :=
  .mk (fun s ↦ t.whiskerIdCancel <| P.to (s.whisker (𝟙 c))) <| by
    intro s τ
    ext
    apply P.hom_ext
    simp [← LeftExtension.w τ]
def whiskerOfCommute (s t : LeftExtension f g) (i : s ≅ t) {x : B} (h : c ⟶ x)
    (P : IsKan (s.whisker h)) :
    IsKan (t.whisker h) :=
  P.ofIsoKan <| whiskerIso i h
end IsKan
namespace IsAbsKan
variable {s t : LeftExtension f g}
abbrev desc (H : IsAbsKan t) {x : B} {h : c ⟶ x} (s : LeftExtension f (g ≫ h)) :
    t.extension ≫ h ⟶ s.extension :=
  (H h).desc s
def isKan (H : IsAbsKan t) : IsKan t :=
  ((H (𝟙 c)).ofCompId _).ofIsoKan <| whiskerOfCompIdIsoSelf t
def ofIsoAbsKan (P : IsAbsKan s) (i : s ≅ t) : IsAbsKan t :=
  fun h ↦ (P h).ofIsoKan (whiskerIso i h)
end IsAbsKan
end LeftExtension
namespace LeftLift
variable {f : b ⟶ a} {g : c ⟶ a}
abbrev IsKan (t : LeftLift f g) := t.IsUniversal
abbrev IsAbsKan (t : LeftLift f g) :=
  ∀ {x : B} (h : x ⟶ c), IsKan (t.whisker h)
namespace IsKan
variable {s t : LeftLift f g}
abbrev mk (desc : ∀ s, t ⟶ s) (w : ∀ s τ, τ = desc s) :
    IsKan t :=
  .ofUniqueHom desc w
abbrev desc (H : IsKan t) (s : LeftLift f g) : t.lift ⟶ s.lift :=
  StructuredArrow.IsUniversal.desc H s
@[reassoc (attr := simp)]
theorem fac (H : IsKan t) (s : LeftLift f g) :
    t.unit ≫ H.desc s ▷ f = s.unit :=
  StructuredArrow.IsUniversal.fac H s
theorem hom_ext (H : IsKan t) {k : c ⟶ b} {τ τ' : t.lift ⟶ k}
    (w : t.unit ≫ τ ▷ f = t.unit ≫ τ' ▷ f) : τ = τ' :=
  StructuredArrow.IsUniversal.hom_ext H w
def uniqueUpToIso (P : IsKan s) (Q : IsKan t) : s ≅ t :=
  Limits.IsInitial.uniqueUpToIso P Q
@[simp]
theorem uniqueUpToIso_hom_right (P : IsKan s) (Q : IsKan t) :
    (uniqueUpToIso P Q).hom.right = P.desc t := rfl
@[simp]
theorem uniqueUpToIso_inv_right (P : IsKan s) (Q : IsKan t) :
    (uniqueUpToIso P Q).inv.right = Q.desc s := rfl
def ofIsoKan (P : IsKan s) (i : s ≅ t) : IsKan t :=
  Limits.IsInitial.ofIso P i
def ofIdComp (t : LeftLift f (𝟙 c ≫ g)) (P : IsKan t) : IsKan t.ofIdComp :=
  .mk (fun s ↦ t.whiskerIdCancel <| P.to (s.whisker (𝟙 c))) <| by
    intro s τ
    ext
    apply P.hom_ext
    simp [← LeftLift.w τ]
def whiskerOfCommute (s t : LeftLift f g) (i : s ≅ t) {x : B} (h : x ⟶ c)
    (P : IsKan (s.whisker h)) :
    IsKan (t.whisker h) :=
  P.ofIsoKan <| whiskerIso i h
end IsKan
namespace IsAbsKan
variable {s t : LeftLift f g}
abbrev desc (H : IsAbsKan t) {x : B} {h : x ⟶ c} (s : LeftLift f (h ≫ g)) :
    h ≫ t.lift ⟶ s.lift :=
  (H h).desc s
def isKan (H : IsAbsKan t) : IsKan t :=
  ((H (𝟙 c)).ofIdComp _).ofIsoKan <| whiskerOfIdCompIsoSelf t
def ofIsoAbsKan (P : IsAbsKan s) (i : s ≅ t) : IsAbsKan t :=
  fun h ↦ (P h).ofIsoKan (whiskerIso i h)
end IsAbsKan
end LeftLift
namespace RightExtension
variable {f : a ⟶ b} {g : a ⟶ c}
abbrev IsKan (t : RightExtension f g) := t.IsUniversal
end RightExtension
namespace RightLift
variable {f : b ⟶ a} {g : c ⟶ a}
abbrev IsKan (t : RightLift f g) := t.IsUniversal
end RightLift
end Bicategory
end CategoryTheory