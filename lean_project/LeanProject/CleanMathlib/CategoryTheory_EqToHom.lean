import Mathlib.CategoryTheory.Opposites
universe v₁ v₂ v₃ u₁ u₂ u₃
namespace CategoryTheory
open Opposite
variable {C : Type u₁} [Category.{v₁} C]
def eqToHom {X Y : C} (p : X = Y) : X ⟶ Y := by rw [p]; exact 𝟙 _
@[simp]
theorem eqToHom_refl (X : C) (p : X = X) : eqToHom p = 𝟙 X :=
  rfl
@[reassoc (attr := simp)]
theorem eqToHom_trans {X Y Z : C} (p : X = Y) (q : Y = Z) :
    eqToHom p ≫ eqToHom q = eqToHom (p.trans q) := by
  cases p
  cases q
  simp
theorem conj_eqToHom_iff_heq {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) (h : W = Y) (h' : X = Z) :
    f = eqToHom h ≫ g ≫ eqToHom h'.symm ↔ HEq f g := by
  cases h
  cases h'
  simp
theorem conj_eqToHom_iff_heq' {C} [Category C] {W X Y Z : C}
    (f : W ⟶ X) (g : Y ⟶ Z) (h : W = Y) (h' : Z = X) :
    f = eqToHom h ≫ g ≫ eqToHom h' ↔ HEq f g := conj_eqToHom_iff_heq _ _ _ h'.symm
theorem comp_eqToHom_iff {X Y Y' : C} (p : Y = Y') (f : X ⟶ Y) (g : X ⟶ Y') :
    f ≫ eqToHom p = g ↔ f = g ≫ eqToHom p.symm :=
  { mp := fun h => h ▸ by simp
    mpr := fun h => by simp [eq_whisker h (eqToHom p)] }
theorem eqToHom_comp_iff {X X' Y : C} (p : X = X') (f : X ⟶ Y) (g : X' ⟶ Y) :
    eqToHom p ≫ g = f ↔ g = eqToHom p.symm ≫ f :=
  { mp := fun h => h ▸ by simp
    mpr := fun h => h ▸ by simp [whisker_eq _ h] }
theorem eqToHom_comp_heq {C} [Category C] {W X Y : C}
    (f : Y ⟶ X) (h : W = Y) : HEq (eqToHom h ≫ f) f := by
  rw [← conj_eqToHom_iff_heq _ _ h rfl, eqToHom_refl, Category.comp_id]
@[simp] theorem eqToHom_comp_heq_iff {C} [Category C] {W X Y Z Z' : C}
    (f : Y ⟶ X) (g : Z ⟶ Z') (h : W = Y) :
    HEq (eqToHom h ≫ f) g ↔ HEq f g :=
  ⟨(eqToHom_comp_heq ..).symm.trans, (eqToHom_comp_heq ..).trans⟩
@[simp] theorem heq_eqToHom_comp_iff {C} [Category C] {W X Y Z Z' : C}
    (f : Y ⟶ X) (g : Z ⟶ Z') (h : W = Y) :
    HEq g (eqToHom h ≫ f) ↔ HEq g f :=
  ⟨(·.trans (eqToHom_comp_heq ..)), (·.trans (eqToHom_comp_heq ..).symm)⟩
theorem comp_eqToHom_heq {C} [Category C] {X Y Z : C}
    (f : X ⟶ Y) (h : Y = Z) : HEq (f ≫ eqToHom h) f := by
  rw [← conj_eqToHom_iff_heq' _ _ rfl h, eqToHom_refl, Category.id_comp]
@[simp] theorem comp_eqToHom_heq_iff {C} [Category C] {W X Y Z Z' : C}
    (f : X ⟶ Y) (g : Z ⟶ Z') (h : Y = W) :
    HEq (f ≫ eqToHom h) g ↔ HEq f g :=
  ⟨(comp_eqToHom_heq ..).symm.trans, (comp_eqToHom_heq ..).trans⟩
@[simp] theorem heq_comp_eqToHom_iff {C} [Category C] {W X Y Z Z' : C}
    (f : X ⟶ Y) (g : Z ⟶ Z') (h : Y = W) :
    HEq g (f ≫ eqToHom h) ↔ HEq g f :=
  ⟨(·.trans (comp_eqToHom_heq ..)), (·.trans (comp_eqToHom_heq ..).symm)⟩
theorem heq_comp {C} [Category C] {X Y Z X' Y' Z' : C}
    {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'}
    (eq1 : X = X') (eq2 : Y = Y') (eq3 : Z = Z')
    (H1 : HEq f f') (H2 : HEq g g') :
    HEq (f ≫ g) (f' ≫ g') := by
  cases eq1; cases eq2; cases eq3; cases H1; cases H2; rfl
variable {β : Sort*}
@[reassoc (attr := simp, nolint simpNF)]
theorem eqToHom_naturality {f g : β → C} (z : ∀ b, f b ⟶ g b) {j j' : β} (w : j = j') :
    z j ≫ eqToHom (by simp [w]) = eqToHom (by simp [w]) ≫ z j' := by
  cases w
  simp
@[reassoc (attr := simp, nolint simpNF)]
theorem eqToHom_iso_hom_naturality {f g : β → C} (z : ∀ b, f b ≅ g b) {j j' : β} (w : j = j') :
    (z j).hom ≫ eqToHom (by simp [w]) = eqToHom (by simp [w]) ≫ (z j').hom := by
  cases w
  simp
@[reassoc (attr := simp, nolint simpNF)]
theorem eqToHom_iso_inv_naturality {f g : β → C} (z : ∀ b, f b ≅ g b) {j j' : β} (w : j = j') :
    (z j).inv ≫ eqToHom (by simp [w]) = eqToHom (by simp [w]) ≫ (z j').inv := by
  cases w
  simp
@[simp]
theorem congrArg_cast_hom_left {X Y Z : C} (p : X = Y) (q : Y ⟶ Z) :
    cast (congrArg (fun W : C => W ⟶ Z) p.symm) q = eqToHom p ≫ q := by
  cases p
  simp
theorem congrArg_mpr_hom_left {X Y Z : C} (p : X = Y) (q : Y ⟶ Z) :
    (congrArg (fun W : C => W ⟶ Z) p).mpr q = eqToHom p ≫ q := by
  cases p
  simp
@[simp]
theorem congrArg_cast_hom_right {X Y Z : C} (p : X ⟶ Y) (q : Z = Y) :
    cast (congrArg (fun W : C => X ⟶ W) q.symm) p = p ≫ eqToHom q.symm := by
  cases q
  simp
theorem congrArg_mpr_hom_right {X Y Z : C} (p : X ⟶ Y) (q : Z = Y) :
    (congrArg (fun W : C => X ⟶ W) q).mpr p = p ≫ eqToHom q.symm := by
  cases q
  simp
def eqToIso {X Y : C} (p : X = Y) : X ≅ Y :=
  ⟨eqToHom p, eqToHom p.symm, by simp, by simp⟩
@[simp]
theorem eqToIso.hom {X Y : C} (p : X = Y) : (eqToIso p).hom = eqToHom p :=
  rfl
@[simp]
theorem eqToIso.inv {X Y : C} (p : X = Y) : (eqToIso p).inv = eqToHom p.symm :=
  rfl
@[simp]
theorem eqToIso_refl {X : C} (p : X = X) : eqToIso p = Iso.refl X :=
  rfl
@[simp]
theorem eqToIso_trans {X Y Z : C} (p : X = Y) (q : Y = Z) :
    eqToIso p ≪≫ eqToIso q = eqToIso (p.trans q) := by ext; simp
@[simp]
theorem eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h).op = eqToHom (congr_arg op h.symm) := by
  cases h
  rfl
@[simp]
theorem eqToHom_unop {X Y : Cᵒᵖ} (h : X = Y) :
    (eqToHom h).unop = eqToHom (congr_arg unop h.symm) := by
  cases h
  rfl
instance {X Y : C} (h : X = Y) : IsIso (eqToHom h) :=
  (eqToIso h).isIso_hom
@[simp]
theorem inv_eqToHom {X Y : C} (h : X = Y) : inv (eqToHom h) = eqToHom h.symm := by
  aesop_cat
variable {D : Type u₂} [Category.{v₂} D]
namespace Functor
theorem ext {F G : C ⥤ D} (h_obj : ∀ X, F.obj X = G.obj X)
    (h_map : ∀ X Y f,
      F.map f = eqToHom (h_obj X) ≫ G.map f ≫ eqToHom (h_obj Y).symm := by aesop_cat) :
    F = G := by
  match F, G with
  | mk F_pre _ _ , mk G_pre _ _ =>
    match F_pre, G_pre with  
    | Prefunctor.mk F_obj _ , Prefunctor.mk G_obj _ =>
    obtain rfl : F_obj = G_obj := by
      ext X
      apply h_obj
    congr
    funext X Y f
    simpa using h_map X Y f
lemma ext_of_iso {F G : C ⥤ D} (e : F ≅ G) (hobj : ∀ X, F.obj X = G.obj X)
    (happ : ∀ X, e.hom.app X = eqToHom (hobj X)) : F = G :=
  Functor.ext hobj (fun X Y f => by
    rw [← cancel_mono (e.hom.app Y), e.hom.naturality f, happ, happ, Category.assoc,
    Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id])
theorem hext {F G : C ⥤ D} (h_obj : ∀ X, F.obj X = G.obj X)
    (h_map : ∀ (X Y) (f : X ⟶ Y), HEq (F.map f) (G.map f)) : F = G :=
  Functor.ext h_obj fun _ _ f => (conj_eqToHom_iff_heq _ _ (h_obj _) (h_obj _)).2 <| h_map _ _ f
theorem congr_obj {F G : C ⥤ D} (h : F = G) (X) : F.obj X = G.obj X := by rw [h]
theorem congr_hom {F G : C ⥤ D} (h : F = G) {X Y} (f : X ⟶ Y) :
    F.map f = eqToHom (congr_obj h X) ≫ G.map f ≫ eqToHom (congr_obj h Y).symm := by
  subst h; simp
theorem congr_inv_of_congr_hom (F G : C ⥤ D) {X Y : C} (e : X ≅ Y) (hX : F.obj X = G.obj X)
    (hY : F.obj Y = G.obj Y)
    (h₂ : F.map e.hom = eqToHom (by rw [hX]) ≫ G.map e.hom ≫ eqToHom (by rw [hY])) :
    F.map e.inv = eqToHom (by rw [hY]) ≫ G.map e.inv ≫ eqToHom (by rw [hX]) := by
  simp only [← IsIso.Iso.inv_hom e, Functor.map_inv, h₂, IsIso.inv_comp, inv_eqToHom,
    Category.assoc]
section HEq
variable {E : Type u₃} [Category.{v₃} E] {F G : C ⥤ D} {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
theorem map_comp_heq (hx : F.obj X = G.obj X) (hy : F.obj Y = G.obj Y) (hz : F.obj Z = G.obj Z)
    (hf : HEq (F.map f) (G.map f)) (hg : HEq (F.map g) (G.map g)) :
    HEq (F.map (f ≫ g)) (G.map (f ≫ g)) := by
  rw [F.map_comp, G.map_comp]
  congr
theorem map_comp_heq' (hobj : ∀ X : C, F.obj X = G.obj X)
    (hmap : ∀ {X Y} (f : X ⟶ Y), HEq (F.map f) (G.map f)) :
    HEq (F.map (f ≫ g)) (G.map (f ≫ g)) := by
  rw [Functor.hext hobj fun _ _ => hmap]
theorem precomp_map_heq (H : E ⥤ C) (hmap : ∀ {X Y} (f : X ⟶ Y), HEq (F.map f) (G.map f)) {X Y : E}
    (f : X ⟶ Y) : HEq ((H ⋙ F).map f) ((H ⋙ G).map f) :=
  hmap _
theorem postcomp_map_heq (H : D ⥤ E) (hx : F.obj X = G.obj X) (hy : F.obj Y = G.obj Y)
    (hmap : HEq (F.map f) (G.map f)) : HEq ((F ⋙ H).map f) ((G ⋙ H).map f) := by
  dsimp
  congr
theorem postcomp_map_heq' (H : D ⥤ E) (hobj : ∀ X : C, F.obj X = G.obj X)
    (hmap : ∀ {X Y} (f : X ⟶ Y), HEq (F.map f) (G.map f)) :
    HEq ((F ⋙ H).map f) ((G ⋙ H).map f) := by rw [Functor.hext hobj fun _ _ => hmap]
theorem hcongr_hom {F G : C ⥤ D} (h : F = G) {X Y} (f : X ⟶ Y) : HEq (F.map f) (G.map f) := by
  rw [h]
end HEq
end Functor
theorem eqToHom_map (F : C ⥤ D) {X Y : C} (p : X = Y) :
    F.map (eqToHom p) = eqToHom (congr_arg F.obj p) := by cases p; simp
@[reassoc (attr := simp)]
theorem eqToHom_map_comp (F : C ⥤ D) {X Y Z : C} (p : X = Y) (q : Y = Z) :
    F.map (eqToHom p) ≫ F.map (eqToHom q) = F.map (eqToHom <| p.trans q) := by aesop_cat
theorem eqToIso_map (F : C ⥤ D) {X Y : C} (p : X = Y) :
    F.mapIso (eqToIso p) = eqToIso (congr_arg F.obj p) := by ext; cases p; simp
@[simp]
theorem eqToIso_map_trans (F : C ⥤ D) {X Y Z : C} (p : X = Y) (q : Y = Z) :
    F.mapIso (eqToIso p) ≪≫ F.mapIso (eqToIso q) = F.mapIso (eqToIso <| p.trans q) := by aesop_cat
@[simp]
theorem eqToHom_app {F G : C ⥤ D} (h : F = G) (X : C) :
    (eqToHom h : F ⟶ G).app X = eqToHom (Functor.congr_obj h X) := by subst h; rfl
theorem NatTrans.congr {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (h : X = Y) :
    α.app X = F.map (eqToHom h) ≫ α.app Y ≫ G.map (eqToHom h.symm) := by
  rw [α.naturality_assoc]
  simp [eqToHom_map]
theorem eq_conj_eqToHom {X Y : C} (f : X ⟶ Y) : f = eqToHom rfl ≫ f ≫ eqToHom rfl := by
  simp only [Category.id_comp, eqToHom_refl, Category.comp_id]
theorem dcongr_arg {ι : Type*} {F G : ι → C} (α : ∀ i, F i ⟶ G i) {i j : ι} (h : i = j) :
    α i = eqToHom (congr_arg F h) ≫ α j ≫ eqToHom (congr_arg G h.symm) := by
  subst h
  simp
end CategoryTheory