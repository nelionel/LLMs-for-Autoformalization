import Mathlib.CategoryTheory.Subobject.MonoOver
import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.Tactic.ApplyFun
import Mathlib.Tactic.CategoryTheory.Elementwise
universe v₁ v₂ u₁ u₂
noncomputable section
namespace CategoryTheory
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
variable {C : Type u₁} [Category.{v₁} C] {X Y Z : C}
variable {D : Type u₂} [Category.{v₂} D]
def Subobject (X : C) :=
  ThinSkeleton (MonoOver X)
instance (X : C) : PartialOrder (Subobject X) := by
  dsimp only [Subobject]
  infer_instance
namespace Subobject
def mk {X A : C} (f : A ⟶ X) [Mono f] : Subobject X :=
  (toThinSkeleton _).obj (MonoOver.mk' f)
section
attribute [local ext] CategoryTheory.Comma
protected theorem ind {X : C} (p : Subobject X → Prop)
    (h : ∀ ⦃A : C⦄ (f : A ⟶ X) [Mono f], p (Subobject.mk f)) (P : Subobject X) : p P := by
  apply Quotient.inductionOn'
  intro a
  exact h a.arrow
protected theorem ind₂ {X : C} (p : Subobject X → Subobject X → Prop)
    (h : ∀ ⦃A B : C⦄ (f : A ⟶ X) (g : B ⟶ X) [Mono f] [Mono g],
      p (Subobject.mk f) (Subobject.mk g))
    (P Q : Subobject X) : p P Q := by
  apply Quotient.inductionOn₂'
  intro a b
  exact h a.arrow b.arrow
end
protected def lift {α : Sort*} {X : C} (F : ∀ ⦃A : C⦄ (f : A ⟶ X) [Mono f], α)
    (h :
      ∀ ⦃A B : C⦄ (f : A ⟶ X) (g : B ⟶ X) [Mono f] [Mono g] (i : A ≅ B),
        i.hom ≫ g = f → F f = F g) :
    Subobject X → α := fun P =>
  Quotient.liftOn' P (fun m => F m.arrow) fun m n ⟨i⟩ =>
    h m.arrow n.arrow ((MonoOver.forget X ⋙ Over.forget X).mapIso i) (Over.w i.hom)
@[simp]
protected theorem lift_mk {α : Sort*} {X : C} (F : ∀ ⦃A : C⦄ (f : A ⟶ X) [Mono f], α) {h A}
    (f : A ⟶ X) [Mono f] : Subobject.lift F h (Subobject.mk f) = F f :=
  rfl
noncomputable def equivMonoOver (X : C) : Subobject X ≌ MonoOver X :=
  ThinSkeleton.equivalence _
noncomputable def representative {X : C} : Subobject X ⥤ MonoOver X :=
  (equivMonoOver X).functor
noncomputable def representativeIso {X : C} (A : MonoOver X) :
    representative.obj ((toThinSkeleton _).obj A) ≅ A :=
  (equivMonoOver X).counitIso.app A
noncomputable def underlying {X : C} : Subobject X ⥤ C :=
  representative ⋙ MonoOver.forget _ ⋙ Over.forget _
instance : CoeOut (Subobject X) C where coe Y := underlying.obj Y
noncomputable def underlyingIso {X Y : C} (f : X ⟶ Y) [Mono f] : (Subobject.mk f : C) ≅ X :=
  (MonoOver.forget _ ⋙ Over.forget _).mapIso (representativeIso (MonoOver.mk' f))
noncomputable def arrow {X : C} (Y : Subobject X) : (Y : C) ⟶ X :=
  (representative.obj Y).obj.hom
instance arrow_mono {X : C} (Y : Subobject X) : Mono Y.arrow :=
  (representative.obj Y).property
@[simp]
theorem arrow_congr {A : C} (X Y : Subobject A) (h : X = Y) :
    eqToHom (congr_arg (fun X : Subobject A => (X : C)) h) ≫ Y.arrow = X.arrow := by
  induction h
  simp
@[simp]
theorem representative_coe (Y : Subobject X) : (representative.obj Y : C) = (Y : C) :=
  rfl
@[simp]
theorem representative_arrow (Y : Subobject X) : (representative.obj Y).arrow = Y.arrow :=
  rfl
@[reassoc (attr := simp)]
theorem underlying_arrow {X : C} {Y Z : Subobject X} (f : Y ⟶ Z) :
    underlying.map f ≫ arrow Z = arrow Y :=
  Over.w (representative.map f)
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem underlyingIso_arrow {X Y : C} (f : X ⟶ Y) [Mono f] :
    (underlyingIso f).inv ≫ (Subobject.mk f).arrow = f :=
  Over.w _
@[reassoc (attr := simp)]
theorem underlyingIso_hom_comp_eq_mk {X Y : C} (f : X ⟶ Y) [Mono f] :
    (underlyingIso f).hom ≫ f = (mk f).arrow :=
  (Iso.eq_inv_comp _).1 (underlyingIso_arrow f).symm
@[ext]
theorem eq_of_comp_arrow_eq {X Y : C} {P : Subobject Y} {f g : X ⟶ P}
    (h : f ≫ P.arrow = g ≫ P.arrow) : f = g :=
  (cancel_mono P.arrow).mp h
theorem mk_le_mk_of_comm {B A₁ A₂ : C} {f₁ : A₁ ⟶ B} {f₂ : A₂ ⟶ B} [Mono f₁] [Mono f₂] (g : A₁ ⟶ A₂)
    (w : g ≫ f₂ = f₁) : mk f₁ ≤ mk f₂ :=
  ⟨MonoOver.homMk _ w⟩
@[simp]
theorem mk_arrow (P : Subobject X) : mk P.arrow = P :=
  Quotient.inductionOn' P fun Q => by
    obtain ⟨e⟩ := @Quotient.mk_out' _ (isIsomorphicSetoid _) Q
    exact Quotient.sound' ⟨MonoOver.isoMk (Iso.refl _) ≪≫ e⟩
theorem le_of_comm {B : C} {X Y : Subobject B} (f : (X : C) ⟶ (Y : C)) (w : f ≫ Y.arrow = X.arrow) :
    X ≤ Y := by
  convert mk_le_mk_of_comm _ w <;> simp
theorem le_mk_of_comm {B A : C} {X : Subobject B} {f : A ⟶ B} [Mono f] (g : (X : C) ⟶ A)
    (w : g ≫ f = X.arrow) : X ≤ mk f :=
  le_of_comm (g ≫ (underlyingIso f).inv) <| by simp [w]
theorem mk_le_of_comm {B A : C} {X : Subobject B} {f : A ⟶ B} [Mono f] (g : A ⟶ (X : C))
    (w : g ≫ X.arrow = f) : mk f ≤ X :=
  le_of_comm ((underlyingIso f).hom ≫ g) <| by simp [w]
@[ext (iff := false)]
theorem eq_of_comm {B : C} {X Y : Subobject B} (f : (X : C) ≅ (Y : C))
    (w : f.hom ≫ Y.arrow = X.arrow) : X = Y :=
  le_antisymm (le_of_comm f.hom w) <| le_of_comm f.inv <| f.inv_comp_eq.2 w.symm
theorem eq_mk_of_comm {B A : C} {X : Subobject B} (f : A ⟶ B) [Mono f] (i : (X : C) ≅ A)
    (w : i.hom ≫ f = X.arrow) : X = mk f :=
  eq_of_comm (i.trans (underlyingIso f).symm) <| by simp [w]
theorem mk_eq_of_comm {B A : C} {X : Subobject B} (f : A ⟶ B) [Mono f] (i : A ≅ (X : C))
    (w : i.hom ≫ X.arrow = f) : mk f = X :=
  Eq.symm <| eq_mk_of_comm _ i.symm <| by rw [Iso.symm_hom, Iso.inv_comp_eq, w]
theorem mk_eq_mk_of_comm {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (i : A₁ ≅ A₂)
    (w : i.hom ≫ g = f) : mk f = mk g :=
  eq_mk_of_comm _ ((underlyingIso f).trans i) <| by simp [w]
def ofLE {B : C} (X Y : Subobject B) (h : X ≤ Y) : (X : C) ⟶ (Y : C) :=
  underlying.map <| h.hom
@[reassoc (attr := simp)]
theorem ofLE_arrow {B : C} {X Y : Subobject B} (h : X ≤ Y) : ofLE X Y h ≫ Y.arrow = X.arrow :=
  underlying_arrow _
instance {B : C} (X Y : Subobject B) (h : X ≤ Y) : Mono (ofLE X Y h) := by
  fconstructor
  intro Z f g w
  replace w := w =≫ Y.arrow
  ext
  simpa using w
theorem ofLE_mk_le_mk_of_comm {B A₁ A₂ : C} {f₁ : A₁ ⟶ B} {f₂ : A₂ ⟶ B} [Mono f₁] [Mono f₂]
    (g : A₁ ⟶ A₂) (w : g ≫ f₂ = f₁) :
    ofLE _ _ (mk_le_mk_of_comm g w) = (underlyingIso _).hom ≫ g ≫ (underlyingIso _).inv := by
  ext
  simp [w]
def ofLEMk {B A : C} (X : Subobject B) (f : A ⟶ B) [Mono f] (h : X ≤ mk f) : (X : C) ⟶ A :=
  ofLE X (mk f) h ≫ (underlyingIso f).hom
instance {B A : C} (X : Subobject B) (f : A ⟶ B) [Mono f] (h : X ≤ mk f) :
    Mono (ofLEMk X f h) := by
  dsimp only [ofLEMk]
  infer_instance
@[simp]
theorem ofLEMk_comp {B A : C} {X : Subobject B} {f : A ⟶ B} [Mono f] (h : X ≤ mk f) :
    ofLEMk X f h ≫ f = X.arrow := by simp [ofLEMk]
def ofMkLE {B A : C} (f : A ⟶ B) [Mono f] (X : Subobject B) (h : mk f ≤ X) : A ⟶ (X : C) :=
  (underlyingIso f).inv ≫ ofLE (mk f) X h
instance {B A : C} (f : A ⟶ B) [Mono f] (X : Subobject B) (h : mk f ≤ X) :
    Mono (ofMkLE f X h) := by
  dsimp only [ofMkLE]
  infer_instance
@[simp]
theorem ofMkLE_arrow {B A : C} {f : A ⟶ B} [Mono f] {X : Subobject B} (h : mk f ≤ X) :
    ofMkLE f X h ≫ X.arrow = f := by simp [ofMkLE]
def ofMkLEMk {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (h : mk f ≤ mk g) :
    A₁ ⟶ A₂ :=
  (underlyingIso f).inv ≫ ofLE (mk f) (mk g) h ≫ (underlyingIso g).hom
instance {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (h : mk f ≤ mk g) :
    Mono (ofMkLEMk f g h) := by
  dsimp only [ofMkLEMk]
  infer_instance
@[simp]
theorem ofMkLEMk_comp {B A₁ A₂ : C} {f : A₁ ⟶ B} {g : A₂ ⟶ B} [Mono f] [Mono g] (h : mk f ≤ mk g) :
    ofMkLEMk f g h ≫ g = f := by simp [ofMkLEMk]
@[reassoc (attr := simp)]
theorem ofLE_comp_ofLE {B : C} (X Y Z : Subobject B) (h₁ : X ≤ Y) (h₂ : Y ≤ Z) :
    ofLE X Y h₁ ≫ ofLE Y Z h₂ = ofLE X Z (h₁.trans h₂) := by
  simp only [ofLE, ← Functor.map_comp underlying]
  congr 1
@[reassoc (attr := simp)]
theorem ofLE_comp_ofLEMk {B A : C} (X Y : Subobject B) (f : A ⟶ B) [Mono f] (h₁ : X ≤ Y)
    (h₂ : Y ≤ mk f) : ofLE X Y h₁ ≫ ofLEMk Y f h₂ = ofLEMk X f (h₁.trans h₂) := by
  simp only [ofMkLE, ofLEMk, ofLE, ← Functor.map_comp_assoc underlying]
  congr 1
@[reassoc (attr := simp)]
theorem ofLEMk_comp_ofMkLE {B A : C} (X : Subobject B) (f : A ⟶ B) [Mono f] (Y : Subobject B)
    (h₁ : X ≤ mk f) (h₂ : mk f ≤ Y) : ofLEMk X f h₁ ≫ ofMkLE f Y h₂ = ofLE X Y (h₁.trans h₂) := by
  simp only [ofMkLE, ofLEMk, ofLE, ← Functor.map_comp underlying, assoc, Iso.hom_inv_id_assoc]
  congr 1
@[reassoc (attr := simp)]
theorem ofLEMk_comp_ofMkLEMk {B A₁ A₂ : C} (X : Subobject B) (f : A₁ ⟶ B) [Mono f] (g : A₂ ⟶ B)
    [Mono g] (h₁ : X ≤ mk f) (h₂ : mk f ≤ mk g) :
    ofLEMk X f h₁ ≫ ofMkLEMk f g h₂ = ofLEMk X g (h₁.trans h₂) := by
  simp only [ofMkLE, ofLEMk, ofLE, ofMkLEMk, ← Functor.map_comp_assoc underlying,
    assoc, Iso.hom_inv_id_assoc]
  congr 1
@[reassoc (attr := simp)]
theorem ofMkLE_comp_ofLE {B A₁ : C} (f : A₁ ⟶ B) [Mono f] (X Y : Subobject B) (h₁ : mk f ≤ X)
    (h₂ : X ≤ Y) : ofMkLE f X h₁ ≫ ofLE X Y h₂ = ofMkLE f Y (h₁.trans h₂) := by
  simp only [ofMkLE, ofLEMk, ofLE, ofMkLEMk, ← Functor.map_comp underlying,
    assoc]
  congr 1
@[reassoc (attr := simp)]
theorem ofMkLE_comp_ofLEMk {B A₁ A₂ : C} (f : A₁ ⟶ B) [Mono f] (X : Subobject B) (g : A₂ ⟶ B)
    [Mono g] (h₁ : mk f ≤ X) (h₂ : X ≤ mk g) :
    ofMkLE f X h₁ ≫ ofLEMk X g h₂ = ofMkLEMk f g (h₁.trans h₂) := by
  simp only [ofMkLE, ofLEMk, ofLE, ofMkLEMk, ← Functor.map_comp_assoc underlying, assoc]
  congr 1
@[reassoc (attr := simp)]
theorem ofMkLEMk_comp_ofMkLE {B A₁ A₂ : C} (f : A₁ ⟶ B) [Mono f] (g : A₂ ⟶ B) [Mono g]
    (X : Subobject B) (h₁ : mk f ≤ mk g) (h₂ : mk g ≤ X) :
    ofMkLEMk f g h₁ ≫ ofMkLE g X h₂ = ofMkLE f X (h₁.trans h₂) := by
  simp only [ofMkLE, ofLEMk, ofLE, ofMkLEMk, ← Functor.map_comp underlying,
    assoc, Iso.hom_inv_id_assoc]
  congr 1
@[reassoc (attr := simp)]
theorem ofMkLEMk_comp_ofMkLEMk {B A₁ A₂ A₃ : C} (f : A₁ ⟶ B) [Mono f] (g : A₂ ⟶ B) [Mono g]
    (h : A₃ ⟶ B) [Mono h] (h₁ : mk f ≤ mk g) (h₂ : mk g ≤ mk h) :
    ofMkLEMk f g h₁ ≫ ofMkLEMk g h h₂ = ofMkLEMk f h (h₁.trans h₂) := by
  simp only [ofMkLE, ofLEMk, ofLE, ofMkLEMk, ← Functor.map_comp_assoc underlying, assoc,
    Iso.hom_inv_id_assoc]
  congr 1
@[simp]
theorem ofLE_refl {B : C} (X : Subobject B) : ofLE X X le_rfl = 𝟙 _ := by
  apply (cancel_mono X.arrow).mp
  simp
@[simp]
theorem ofMkLEMk_refl {B A₁ : C} (f : A₁ ⟶ B) [Mono f] : ofMkLEMk f f le_rfl = 𝟙 _ := by
  apply (cancel_mono f).mp
  simp
@[simps]
def isoOfEq {B : C} (X Y : Subobject B) (h : X = Y) : (X : C) ≅ (Y : C) where
  hom := ofLE _ _ h.le
  inv := ofLE _ _ h.ge
@[simps]
def isoOfEqMk {B A : C} (X : Subobject B) (f : A ⟶ B) [Mono f] (h : X = mk f) : (X : C) ≅ A where
  hom := ofLEMk X f h.le
  inv := ofMkLE f X h.ge
@[simps]
def isoOfMkEq {B A : C} (f : A ⟶ B) [Mono f] (X : Subobject B) (h : mk f = X) : A ≅ (X : C) where
  hom := ofMkLE f X h.le
  inv := ofLEMk X f h.ge
@[simps]
def isoOfMkEqMk {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (h : mk f = mk g) :
    A₁ ≅ A₂ where
  hom := ofMkLEMk f g h.le
  inv := ofMkLEMk g f h.ge
end Subobject
open CategoryTheory.Limits
namespace Subobject
def lower {Y : D} (F : MonoOver X ⥤ MonoOver Y) : Subobject X ⥤ Subobject Y :=
  ThinSkeleton.map F
theorem lower_iso (F₁ F₂ : MonoOver X ⥤ MonoOver Y) (h : F₁ ≅ F₂) : lower F₁ = lower F₂ :=
  ThinSkeleton.map_iso_eq h
def lower₂ (F : MonoOver X ⥤ MonoOver Y ⥤ MonoOver Z) : Subobject X ⥤ Subobject Y ⥤ Subobject Z :=
  ThinSkeleton.map₂ F
@[simp]
theorem lower_comm (F : MonoOver Y ⥤ MonoOver X) :
    toThinSkeleton _ ⋙ lower F = F ⋙ toThinSkeleton _ :=
  rfl
def lowerAdjunction {A : C} {B : D} {L : MonoOver A ⥤ MonoOver B} {R : MonoOver B ⥤ MonoOver A}
    (h : L ⊣ R) : lower L ⊣ lower R :=
  ThinSkeleton.lowerAdjunction _ _ h
@[simps]
def lowerEquivalence {A : C} {B : D} (e : MonoOver A ≌ MonoOver B) : Subobject A ≌ Subobject B where
  functor := lower e.functor
  inverse := lower e.inverse
  unitIso := by
    apply eqToIso
    convert ThinSkeleton.map_iso_eq e.unitIso
    · exact ThinSkeleton.map_id_eq.symm
    · exact (ThinSkeleton.map_comp_eq _ _).symm
  counitIso := by
    apply eqToIso
    convert ThinSkeleton.map_iso_eq e.counitIso
    · exact (ThinSkeleton.map_comp_eq _ _).symm
    · exact ThinSkeleton.map_id_eq.symm
section Pullback
variable [HasPullbacks C]
def pullback (f : X ⟶ Y) : Subobject Y ⥤ Subobject X :=
  lower (MonoOver.pullback f)
theorem pullback_id (x : Subobject X) : (pullback (𝟙 X)).obj x = x := by
  induction' x using Quotient.inductionOn' with f
  exact Quotient.sound ⟨MonoOver.pullbackId.app f⟩
theorem pullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : Subobject Z) :
    (pullback (f ≫ g)).obj x = (pullback f).obj ((pullback g).obj x) := by
  induction' x using Quotient.inductionOn' with t
  exact Quotient.sound ⟨(MonoOver.pullbackComp _ _).app t⟩
instance (f : X ⟶ Y) : (pullback f).Faithful where
end Pullback
section Map
def map (f : X ⟶ Y) [Mono f] : Subobject X ⥤ Subobject Y :=
  lower (MonoOver.map f)
theorem map_id (x : Subobject X) : (map (𝟙 X)).obj x = x := by
  induction' x using Quotient.inductionOn' with f
  exact Quotient.sound ⟨(MonoOver.mapId _).app f⟩
theorem map_comp (f : X ⟶ Y) (g : Y ⟶ Z) [Mono f] [Mono g] (x : Subobject X) :
    (map (f ≫ g)).obj x = (map g).obj ((map f).obj x) := by
  induction' x using Quotient.inductionOn' with t
  exact Quotient.sound ⟨(MonoOver.mapComp _ _).app t⟩
def mapIso {A B : C} (e : A ≅ B) : Subobject A ≌ Subobject B :=
  lowerEquivalence (MonoOver.mapIso e)
def mapIsoToOrderIso (e : X ≅ Y) : Subobject X ≃o Subobject Y where
  toFun := (map e.hom).obj
  invFun := (map e.inv).obj
  left_inv g := by simp_rw [← map_comp, e.hom_inv_id, map_id]
  right_inv g := by simp_rw [← map_comp, e.inv_hom_id, map_id]
  map_rel_iff' {A B} := by
    dsimp
    constructor
    · intro h
      apply_fun (map e.inv).obj at h
      · simpa only [← map_comp, e.hom_inv_id, map_id] using h
      · apply Functor.monotone
    · intro h
      apply_fun (map e.hom).obj at h
      · exact h
      · apply Functor.monotone
@[simp]
theorem mapIsoToOrderIso_apply (e : X ≅ Y) (P : Subobject X) :
    mapIsoToOrderIso e P = (map e.hom).obj P :=
  rfl
@[simp]
theorem mapIsoToOrderIso_symm_apply (e : X ≅ Y) (Q : Subobject Y) :
    (mapIsoToOrderIso e).symm Q = (map e.inv).obj Q :=
  rfl
def mapPullbackAdj [HasPullbacks C] (f : X ⟶ Y) [Mono f] : map f ⊣ pullback f :=
  lowerAdjunction (MonoOver.mapPullbackAdj f)
@[simp]
theorem pullback_map_self [HasPullbacks C] (f : X ⟶ Y) [Mono f] (g : Subobject X) :
    (pullback f).obj ((map f).obj g) = g := by
  revert g
  exact Quotient.ind (fun g' => Quotient.sound ⟨(MonoOver.pullbackMapSelf f).app _⟩)
theorem map_pullback [HasPullbacks C] {X Y Z W : C} {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W}
    [Mono h] [Mono g] (comm : f ≫ h = g ≫ k) (t : IsLimit (PullbackCone.mk f g comm))
    (p : Subobject Y) : (map g).obj ((pullback f).obj p) = (pullback k).obj ((map h).obj p) := by
  revert p
  apply Quotient.ind'
  intro a
  apply Quotient.sound
  apply ThinSkeleton.equiv_of_both_ways
  · refine MonoOver.homMk (pullback.lift (pullback.fst _ _) _ ?_) (pullback.lift_snd _ _ _)
    change _ ≫ a.arrow ≫ h = (pullback.snd _ _ ≫ g) ≫ _
    rw [assoc, ← comm, pullback.condition_assoc]
  · refine MonoOver.homMk (pullback.lift (pullback.fst _ _)
      (PullbackCone.IsLimit.lift t (pullback.fst _ _ ≫ a.arrow) (pullback.snd _ _) _)
      (PullbackCone.IsLimit.lift_fst _ _ _ ?_).symm) ?_
    · rw [← pullback.condition, assoc]
      rfl
    · dsimp
      rw [pullback.lift_snd_assoc]
      apply PullbackCone.IsLimit.lift_snd
end Map
section Exists
variable [HasImages C]
def «exists» (f : X ⟶ Y) : Subobject X ⥤ Subobject Y :=
  lower (MonoOver.exists f)
theorem exists_iso_map (f : X ⟶ Y) [Mono f] : «exists» f = map f :=
  lower_iso _ _ (MonoOver.existsIsoMap f)
def existsPullbackAdj (f : X ⟶ Y) [HasPullbacks C] : «exists» f ⊣ pullback f :=
  lowerAdjunction (MonoOver.existsPullbackAdj f)
end Exists
end Subobject
end CategoryTheory