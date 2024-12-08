import Mathlib.Data.TypeMax
import Mathlib.Logic.UnivLE
import Mathlib.CategoryTheory.Limits.Shapes.Images
open CategoryTheory CategoryTheory.Limits
universe v u w
namespace CategoryTheory.Limits
namespace Types
section limit_characterization
variable {J : Type v} [Category.{w} J] {F : J ⥤ Type u}
def coneOfSection {s} (hs : s ∈ F.sections) : Cone F where
  pt := PUnit
  π :=
  { app := fun j _ ↦ s j,
    naturality := fun i j f ↦ by ext; exact (hs f).symm }
def sectionOfCone (c : Cone F) (x : c.pt) : F.sections :=
  ⟨fun j ↦ c.π.app j x, fun f ↦ congr_fun (c.π.naturality f).symm x⟩
theorem isLimit_iff (c : Cone F) :
    Nonempty (IsLimit c) ↔ ∀ s ∈ F.sections, ∃! x : c.pt, ∀ j, c.π.app j x = s j := by
  refine ⟨fun ⟨t⟩ s hs ↦ ?_, fun h ↦ ⟨?_⟩⟩
  · let cs := coneOfSection hs
    exact ⟨t.lift cs ⟨⟩, fun j ↦ congr_fun (t.fac cs j) ⟨⟩,
      fun x hx ↦ congr_fun (t.uniq cs (fun _ ↦ x) fun j ↦ funext fun _ ↦ hx j) ⟨⟩⟩
  · choose x hx using fun c y ↦ h _ (sectionOfCone c y).2
    exact ⟨x, fun c j ↦ funext fun y ↦ (hx c y).1 j,
      fun c f hf ↦ funext fun y ↦ (hx c y).2 (f y) (fun j ↦ congr_fun (hf j) y)⟩
theorem isLimit_iff_bijective_sectionOfCone (c : Cone F) :
    Nonempty (IsLimit c) ↔ (Types.sectionOfCone c).Bijective := by
  simp_rw [isLimit_iff, Function.bijective_iff_existsUnique, Subtype.forall, F.sections_ext_iff,
    sectionOfCone]
noncomputable def isLimitEquivSections {c : Cone F} (t : IsLimit c) :
    c.pt ≃ F.sections where
  toFun := sectionOfCone c
  invFun s := t.lift (coneOfSection s.2) ⟨⟩
  left_inv x := (congr_fun (t.uniq (coneOfSection _) (fun _ ↦ x) fun _ ↦ rfl) ⟨⟩).symm
  right_inv s := Subtype.ext (funext fun j ↦ congr_fun (t.fac (coneOfSection s.2) j) ⟨⟩)
@[simp]
theorem isLimitEquivSections_apply {c : Cone F} (t : IsLimit c) (j : J)
    (x : c.pt) : (isLimitEquivSections t x : ∀ j, F.obj j) j = c.π.app j x := rfl
@[simp]
theorem isLimitEquivSections_symm_apply {c : Cone F} (t : IsLimit c)
    (x : F.sections) (j : J) :
    c.π.app j ((isLimitEquivSections t).symm x) = (x : ∀ j, F.obj j) j := by
  conv_rhs => rw [← (isLimitEquivSections t).right_inv x]
  rfl
end limit_characterization
variable {J : Type v} [Category.{w} J]
namespace Small
variable (F : J ⥤ Type u)
section
variable [Small.{u} F.sections]
@[simps]
noncomputable def limitCone : Cone F where
  pt := Shrink F.sections
  π :=
    { app := fun j u => ((equivShrink F.sections).symm u).val j
      naturality := fun j j' f => by
        funext x
        simp }
@[ext]
lemma limitCone_pt_ext {x y : (limitCone F).pt}
    (w : (equivShrink F.sections).symm x = (equivShrink F.sections).symm y) : x = y := by
  aesop
@[simps]
noncomputable def limitConeIsLimit : IsLimit (limitCone.{v, u} F) where
  lift s v := equivShrink F.sections
    { val := fun j => s.π.app j v
      property := fun f => congr_fun (Cone.w s f) _ }
  uniq := fun _ _ w => by
    ext x j
    simpa using congr_fun (w j) x
end
end Small
theorem hasLimit_iff_small_sections (F : J ⥤ Type u) : HasLimit F ↔ Small.{u} F.sections :=
  ⟨fun _ => .mk ⟨_, ⟨(Equiv.ofBijective _
    ((isLimit_iff_bijective_sectionOfCone (limit.cone F)).mp ⟨limit.isLimit _⟩)).symm⟩⟩,
   fun _ => ⟨_, Small.limitConeIsLimit F⟩⟩
section TypeMax
@[simps]
noncomputable def limitCone (F : J ⥤ TypeMax.{v, u}) : Cone F where
  pt := F.sections
  π :=
    { app := fun j u => u.val j
      naturality := fun j j' f => by
        funext x
        simp }
@[simps]
noncomputable def limitConeIsLimit (F : J ⥤ TypeMax.{v, u}) : IsLimit (limitCone F) where
  lift s v :=
    { val := fun j => s.π.app j v
      property := fun f => congr_fun (Cone.w s f) _ }
  uniq := fun _ _ w => by
    funext x
    apply Subtype.ext
    funext j
    exact congr_fun (w j) x
end TypeMax
section UnivLE
open UnivLE
instance hasLimit [Small.{u} J] (F : J ⥤ Type u) : HasLimit F :=
  (hasLimit_iff_small_sections F).mpr inferInstance
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J (Type u) where
instance (priority := 1300) hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} (Type u) where
  has_limits_of_shape _ := { }
variable (F : J ⥤ Type u) [HasLimit F]
noncomputable def limitEquivSections : limit F ≃ F.sections :=
  isLimitEquivSections (limit.isLimit F)
@[simp]
theorem limitEquivSections_apply (x : limit F) (j : J) :
    ((limitEquivSections F) x : ∀ j, F.obj j) j = limit.π F j x :=
  isLimitEquivSections_apply _ _ _
@[simp]
theorem limitEquivSections_symm_apply (x : F.sections) (j : J) :
    limit.π F j ((limitEquivSections F).symm x) = (x : ∀ j, F.obj j) j :=
  isLimitEquivSections_symm_apply _ _ _
noncomputable def Limit.mk (x : ∀ j, F.obj j) (h : ∀ (j j') (f : j ⟶ j'), F.map f (x j) = x j') :
    limit F :=
  (limitEquivSections F).symm ⟨x, h _ _⟩
@[simp]
theorem Limit.π_mk (x : ∀ j, F.obj j) (h : ∀ (j j') (f : j ⟶ j'), F.map f (x j) = x j') (j) :
    limit.π F j (Limit.mk F x h) = x j := by
  dsimp [Limit.mk]
  simp
@[ext]
theorem limit_ext (x y : limit F) (w : ∀ j, limit.π F j x = limit.π F j y) : x = y := by
  apply (limitEquivSections F).injective
  ext j
  simp [w j]
@[ext]
theorem limit_ext' (F : J ⥤ Type v) (x y : limit F) (w : ∀ j, limit.π F j x = limit.π F j y) :
    x = y :=
  limit_ext F x y w
theorem limit_ext_iff' (F : J ⥤ Type v) (x y : limit F) :
    x = y ↔ ∀ j, limit.π F j x = limit.π F j y :=
  ⟨fun t _ => t ▸ rfl, limit_ext' _ _ _⟩
variable {F} in
theorem Limit.w_apply {j j' : J} {x : limit F} (f : j ⟶ j') :
    F.map f (limit.π F j x) = limit.π F j' x :=
  congr_fun (limit.w F f) x
theorem Limit.lift_π_apply (s : Cone F) (j : J) (x : s.pt) :
    limit.π F j (limit.lift F s x) = s.π.app j x :=
  congr_fun (limit.lift_π s j) x
theorem Limit.map_π_apply {F G : J ⥤ Type u} [HasLimit F] [HasLimit G] (α : F ⟶ G) (j : J)
    (x : limit F) : limit.π G j (limMap α x) = α.app j (limit.π F j x) :=
  congr_fun (limMap_π α j) x
@[simp]
theorem Limit.w_apply' {F : J ⥤ Type v} {j j' : J} {x : limit F} (f : j ⟶ j') :
    F.map f (limit.π F j x) = limit.π F j' x :=
  congr_fun (limit.w F f) x
@[simp]
theorem Limit.lift_π_apply' (F : J ⥤ Type v) (s : Cone F) (j : J) (x : s.pt) :
    limit.π F j (limit.lift F s x) = s.π.app j x :=
  congr_fun (limit.lift_π s j) x
@[simp]
theorem Limit.map_π_apply' {F G : J ⥤ Type v} (α : F ⟶ G) (j : J) (x : limit F) :
    limit.π G j (limMap α x) = α.app j (limit.π F j x) :=
  congr_fun (limMap_π α j) x
end UnivLE
section instances
example : HasLimitsOfSize.{w, w, max v w, max (v + 1) (w + 1)} (TypeMax.{w, v}) := inferInstance
example : HasLimitsOfSize.{w, w, max v w, max (v + 1) (w + 1)} (Type max v w) := inferInstance
example : HasLimitsOfSize.{0, 0, v, v+1} (Type v) := inferInstance
example : HasLimitsOfSize.{v, v, v, v+1} (Type v) := inferInstance
example [UnivLE.{v, u}] : HasLimitsOfSize.{v, v, u, u+1} (Type u) := inferInstance
end instances
def Quot.Rel (F : J ⥤ Type u) : (Σ j, F.obj j) → (Σ j, F.obj j) → Prop := fun p p' =>
  ∃ f : p.1 ⟶ p'.1, p'.2 = F.map f p.2
def Quot (F : J ⥤ Type u) : Type (max v u) :=
  _root_.Quot (Quot.Rel F)
instance [Small.{u} J] (F : J ⥤ Type u) : Small.{u} (Quot F) :=
  small_of_surjective Quot.mk_surjective
def Quot.ι (F : J ⥤ Type u) (j : J) : F.obj j → Quot F :=
  fun x => Quot.mk _ ⟨j, x⟩
lemma Quot.jointly_surjective {F : J ⥤ Type u} (x : Quot F) : ∃ j y, x = Quot.ι F j y :=
  Quot.ind (β := fun x => ∃ j y, x = Quot.ι F j y) (fun ⟨j, y⟩ => ⟨j, y, rfl⟩) x
section
variable {F : J ⥤ Type u} (c : Cocone F)
def Quot.desc : Quot F → c.pt :=
  Quot.lift (fun x => c.ι.app x.1 x.2) <| by
    rintro ⟨j, x⟩ ⟨j', _⟩ ⟨φ : j ⟶ j', rfl : _ = F.map φ x⟩
    exact congr_fun (c.ι.naturality φ).symm x
@[simp]
lemma Quot.ι_desc (j : J) (x : F.obj j) : Quot.desc c (Quot.ι F j x) = c.ι.app j x := rfl
@[simp]
lemma Quot.map_ι {j j' : J} {f : j ⟶ j'} (x : F.obj j) : Quot.ι F j' (F.map f x) = Quot.ι F j x :=
  (Quot.sound ⟨f, rfl⟩).symm
@[simps]
def toCocone {α : Type u} (f : Quot F → α) : Cocone F where
  pt := α
  ι := { app := fun j => f ∘ Quot.ι F j }
lemma Quot.desc_toCocone_desc {α : Type u} (f : Quot F → α) (hc : IsColimit c) (x : Quot F) :
    hc.desc (toCocone f) (Quot.desc c x) = f x := by
  obtain ⟨j, y, rfl⟩ := Quot.jointly_surjective x
  simpa using congrFun (hc.fac _ j) y
theorem isColimit_iff_bijective_desc : Nonempty (IsColimit c) ↔ (Quot.desc c).Bijective := by
  classical
  refine ⟨?_, ?_⟩
  · refine fun ⟨hc⟩ => ⟨fun x y h => ?_, fun x => ?_⟩
    · let f : Quot F → ULift.{u} Bool := fun z => ULift.up (x = z)
      suffices f x = f y by simpa [f] using this
      rw [← Quot.desc_toCocone_desc c f hc x, h, Quot.desc_toCocone_desc]
    · let f₁ : c.pt ⟶ ULift.{u} Bool := fun _ => ULift.up true
      let f₂ : c.pt ⟶ ULift.{u} Bool := fun x => ULift.up (∃ a, Quot.desc c a = x)
      suffices f₁ = f₂ by simpa [f₁, f₂] using congrFun this x
      refine hc.hom_ext fun j => funext fun x => ?_
      simpa [f₁, f₂] using ⟨Quot.ι F j x, by simp⟩
  · refine fun h => ⟨?_⟩
    let e := Equiv.ofBijective _ h
    have h : ∀ j x, e.symm (c.ι.app j x) = Quot.ι F j x :=
      fun j x => e.injective (Equiv.ofBijective_apply_symm_apply _ _ _)
    exact
      { desc := fun s => Quot.desc s ∘ e.symm
        fac := fun s j => by
          ext x
          simp [h]
        uniq := fun s m hm => by
          ext x
          obtain ⟨x, rfl⟩ := e.surjective x
          obtain ⟨j, x, rfl⟩ := Quot.jointly_surjective x
          rw [← h, Equiv.apply_symm_apply]
          simpa [h] using congrFun (hm j) x }
end
@[simps]
noncomputable def colimitCocone (F : J ⥤ Type u) [Small.{u} (Quot F)] : Cocone F where
  pt := Shrink (Quot F)
  ι :=
    { app := fun j x => equivShrink.{u} _ (Quot.mk _ ⟨j, x⟩)
      naturality := fun _ _ f => funext fun _ => congrArg _ (Quot.sound ⟨f, rfl⟩).symm }
@[simp]
theorem Quot.desc_colimitCocone (F : J ⥤ Type u) [Small.{u} (Quot F)] :
    Quot.desc (colimitCocone F) = equivShrink.{u} (Quot F) := by
  ext ⟨j, x⟩
  rfl
noncomputable def colimitCoconeIsColimit (F : J ⥤ Type u) [Small.{u} (Quot F)] :
    IsColimit (colimitCocone F) :=
  Nonempty.some <| by
    rw [isColimit_iff_bijective_desc, Quot.desc_colimitCocone]
    exact (equivShrink _).bijective
theorem hasColimit_iff_small_quot (F : J ⥤ Type u) : HasColimit F ↔ Small.{u} (Quot F) :=
  ⟨fun _ => .mk ⟨_, ⟨(Equiv.ofBijective _
    ((isColimit_iff_bijective_desc (colimit.cocone F)).mp ⟨colimit.isColimit _⟩))⟩⟩,
   fun _ => ⟨_, colimitCoconeIsColimit F⟩⟩
theorem small_quot_of_hasColimit (F : J ⥤ Type u) [HasColimit F] : Small.{u} (Quot F) :=
  (hasColimit_iff_small_quot F).mp inferInstance
instance hasColimit [Small.{u} J] (F : J ⥤ Type u) : HasColimit F :=
  (hasColimit_iff_small_quot F).mpr inferInstance
instance hasColimitsOfShape [Small.{u} J] : HasColimitsOfShape J (Type u) where
instance (priority := 1300) hasColimitsOfSize [UnivLE.{v, u}] :
    HasColimitsOfSize.{w, v} (Type u) where
section instances
example : HasColimitsOfSize.{w, w, max v w, max (v + 1) (w + 1)} (TypeMax.{w, v}) := inferInstance
example : HasColimitsOfSize.{w, w, max v w, max (v + 1) (w + 1)} (Type max v w) := inferInstance
example : HasColimitsOfSize.{0, 0, v, v+1} (Type v) := inferInstance
example : HasColimitsOfSize.{v, v, v, v+1} (Type v) := inferInstance
example [UnivLE.{v, u}] : HasColimitsOfSize.{v, v, u, u+1} (Type u) := inferInstance
end instances
namespace TypeMax
@[simps]
def colimitCocone (F : J ⥤ TypeMax.{v, u}) : Cocone F where
  pt := Quot F
  ι :=
    { app := fun j x => Quot.mk (Quot.Rel F) ⟨j, x⟩
      naturality := fun _ _ f => funext fun _ => (Quot.sound ⟨f, rfl⟩).symm }
def colimitCoconeIsColimit (F : J ⥤ TypeMax.{v, u}) : IsColimit (colimitCocone F) where
  desc s :=
    Quot.lift (fun p : Σj, F.obj j => s.ι.app p.1 p.2) fun ⟨j, x⟩ ⟨j', x'⟩ ⟨f, hf⟩ => by
      dsimp at hf
      rw [hf]
      exact (congr_fun (Cocone.w s f) x).symm
  uniq s m hm := by
    funext x
    induction' x using Quot.ind with x
    exact congr_fun (hm x.1) x.2
end TypeMax
variable (F : J ⥤ Type u) [HasColimit F]
attribute [local instance] small_quot_of_hasColimit
noncomputable def colimitEquivQuot : colimit F ≃ Quot F :=
  (IsColimit.coconePointUniqueUpToIso
    (colimit.isColimit F) (colimitCoconeIsColimit F)).toEquiv.trans (equivShrink _).symm
@[simp]
theorem colimitEquivQuot_symm_apply (j : J) (x : F.obj j) :
    (colimitEquivQuot F).symm (Quot.mk _ ⟨j, x⟩) = colimit.ι F j x :=
  congrFun (IsColimit.comp_coconePointUniqueUpToIso_inv (colimit.isColimit F) _ _) x
@[simp]
theorem colimitEquivQuot_apply (j : J) (x : F.obj j) :
    (colimitEquivQuot F) (colimit.ι F j x) = Quot.mk _ ⟨j, x⟩ := by
  apply (colimitEquivQuot F).symm.injective
  simp
variable {F} in
theorem Colimit.w_apply {j j' : J} {x : F.obj j} (f : j ⟶ j') :
    colimit.ι F j' (F.map f x) = colimit.ι F j x :=
  congr_fun (colimit.w F f) x
theorem Colimit.ι_desc_apply (s : Cocone F) (j : J) (x : F.obj j) :
    colimit.desc F s (colimit.ι F j x) = s.ι.app j x :=
   congr_fun (colimit.ι_desc s j) x
theorem Colimit.ι_map_apply {F G : J ⥤ Type u} [HasColimitsOfShape J (Type u)] (α : F ⟶ G) (j : J)
    (x : F.obj j) : colim.map α (colimit.ι F j x) = colimit.ι G j (α.app j x) :=
  congr_fun (colimit.ι_map α j) x
@[simp]
theorem Colimit.w_apply' {F : J ⥤ Type v} {j j' : J} {x : F.obj j} (f : j ⟶ j') :
    colimit.ι F j' (F.map f x) = colimit.ι F j x :=
  congr_fun (colimit.w F f) x
@[simp]
theorem Colimit.ι_desc_apply' (F : J ⥤ Type v) (s : Cocone F) (j : J) (x : F.obj j) :
    colimit.desc F s (colimit.ι F j x) = s.ι.app j x :=
  congr_fun (colimit.ι_desc s j) x
@[simp]
theorem Colimit.ι_map_apply' {F G : J ⥤ Type v} (α : F ⟶ G) (j : J) (x) :
    colim.map α (colimit.ι F j x) = colimit.ι G j (α.app j x) :=
  congr_fun (colimit.ι_map α j) x
variable {F} in
theorem colimit_sound {j j' : J} {x : F.obj j} {x' : F.obj j'} (f : j ⟶ j')
    (w : F.map f x = x') : colimit.ι F j x = colimit.ι F j' x' := by
  rw [← w, Colimit.w_apply]
variable {F} in
theorem colimit_sound' {j j' : J} {x : F.obj j} {x' : F.obj j'} {j'' : J}
    (f : j ⟶ j'') (f' : j' ⟶ j'') (w : F.map f x = F.map f' x') :
    colimit.ι F j x = colimit.ι F j' x' := by
  rw [← colimit.w _ f, ← colimit.w _ f']
  rw [types_comp_apply, types_comp_apply, w]
variable {F} in
theorem colimit_eq {j j' : J} {x : F.obj j} {x' : F.obj j'}
    (w : colimit.ι F j x = colimit.ι F j' x') :
      Relation.EqvGen (Quot.Rel F) ⟨j, x⟩ ⟨j', x'⟩ := by
  apply Quot.eq.1
  simpa using congr_arg (colimitEquivQuot F) w
theorem jointly_surjective_of_isColimit {F : J ⥤ Type u} {t : Cocone F} (h : IsColimit t)
    (x : t.pt) : ∃ j y, t.ι.app j y = x := by
  by_contra hx
  simp_rw [not_exists] at hx
  apply (_ : (fun _ ↦ ULift.up True) ≠ (⟨· ≠ x⟩))
  · refine h.hom_ext fun j ↦ ?_
    ext y
    exact (true_iff _).mpr (hx j y)
  · exact fun he ↦ of_eq_true (congr_arg ULift.down <| congr_fun he x).symm rfl
theorem jointly_surjective (F : J ⥤ Type u) {t : Cocone F} (h : IsColimit t) (x : t.pt) :
    ∃ j y, t.ι.app j y = x := jointly_surjective_of_isColimit h x
variable {F} in
theorem jointly_surjective' (x : colimit F) :
    ∃ j y, colimit.ι F j y = x :=
  jointly_surjective F (colimit.isColimit F) x
theorem nonempty_of_nonempty_colimit {F : J ⥤ Type u} [HasColimit F] :
    Nonempty (colimit F) → Nonempty J :=
  Nonempty.map <| Sigma.fst ∘ Quot.out ∘ (colimitEquivQuot F).toFun
variable {α β : Type u} (f : α ⟶ β)
section
def Image : Type u :=
  Set.range f
instance [Inhabited α] : Inhabited (Image f) where default := ⟨f default, ⟨_, rfl⟩⟩
def Image.ι : Image f ⟶ β :=
  Subtype.val
instance : Mono (Image.ι f) :=
  (mono_iff_injective _).2 Subtype.val_injective
variable {f}
noncomputable def Image.lift (F' : MonoFactorisation f) : Image f ⟶ F'.I :=
  (fun x => F'.e (Classical.indefiniteDescription _ x.2).1 : Image f → F'.I)
theorem Image.lift_fac (F' : MonoFactorisation f) : Image.lift F' ≫ F'.m = Image.ι f := by
  funext x
  change (F'.e ≫ F'.m) _ = _
  rw [F'.fac, (Classical.indefiniteDescription _ x.2).2]
  rfl
end
def monoFactorisation : MonoFactorisation f where
  I := Image f
  m := Image.ι f
  e := Set.rangeFactorization f
noncomputable def isImage : IsImage (monoFactorisation f) where
  lift := Image.lift
  lift_fac := Image.lift_fac
instance : HasImage f :=
  HasImage.mk ⟨_, isImage f⟩
instance : HasImages (Type u) where
  has_image := by infer_instance
instance : HasImageMaps (Type u) where
  has_image_map {f g} st :=
    HasImageMap.transport st (monoFactorisation f.hom) (isImage g.hom)
      (fun x => ⟨st.right x.1, ⟨st.left (Classical.choose x.2), by
        have p := st.w
        replace p := congr_fun p (Classical.choose x.2)
        simp only [Functor.id_obj, Functor.id_map, types_comp_apply] at p
        rw [p, Classical.choose_spec x.2]⟩⟩) rfl
variable {F : ℕᵒᵖ ⥤ Type u} {c : Cone F}
  (hF : ∀ n, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op))
private noncomputable def limitOfSurjectionsSurjective.preimage
    (a : F.obj ⟨0⟩) : (n : ℕ) → F.obj ⟨n⟩
    | 0 => a
    | n+1 => (hF n (preimage a n)).choose
include hF in
open limitOfSurjectionsSurjective in
lemma surjective_π_app_zero_of_surjective_map_aux :
    Function.Surjective ((limitCone F).π.app ⟨0⟩) := by
  intro a
  refine ⟨⟨fun ⟨n⟩ ↦ preimage hF a n, ?_⟩, rfl⟩
  intro ⟨n⟩ ⟨m⟩ ⟨⟨⟨(h : m ≤ n)⟩⟩⟩
  induction h with
  | refl =>
    erw [CategoryTheory.Functor.map_id, types_id_apply]
  | @step p h ih =>
    rw [← ih]
    have h' : m ≤ p := h
    erw [CategoryTheory.Functor.map_comp (f := (homOfLE (Nat.le_succ p)).op) (g := (homOfLE h').op),
      types_comp_apply, (hF p _).choose_spec]
    rfl
lemma surjective_π_app_zero_of_surjective_map
    (hc : IsLimit c)
    (hF : ∀ n, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op)) :
    Function.Surjective (c.π.app ⟨0⟩) := by
  let i := hc.conePointUniqueUpToIso (limitConeIsLimit F)
  have : c.π.app ⟨0⟩ = i.hom ≫ (limitCone F).π.app ⟨0⟩ := by simp [i]
  rw [this]
  apply Function.Surjective.comp
  · exact surjective_π_app_zero_of_surjective_map_aux hF
  · rw [← epi_iff_surjective]
    infer_instance
end Types
open Functor Opposite
section
variable {J C : Type*} [Category J] [Category C]
@[simps]
def compCoyonedaSectionsEquiv (F : J ⥤ C) (X : C) :
    (F ⋙ coyoneda.obj (op X)).sections ≃ ((const J).obj X ⟶ F) where
  toFun s :=
    { app := fun j => s.val j
      naturality := fun j j' f => by
        dsimp
        rw [Category.id_comp]
        exact (s.property f).symm }
  invFun τ := ⟨τ.app, fun {j j'} f => by simpa using (τ.naturality f).symm⟩
  left_inv _ := rfl
  right_inv _ := rfl
@[simps]
def opCompYonedaSectionsEquiv (F : J ⥤ C) (X : C) :
    (F.op ⋙ yoneda.obj X).sections ≃ (F ⟶ (const J).obj X) where
  toFun s :=
    { app := fun j => s.val (op j)
      naturality := fun j j' f => by
        dsimp
        rw [Category.comp_id]
        exact (s.property f.op) }
  invFun τ := ⟨fun j => τ.app j.unop, fun {j j'} f => by simp [τ.naturality f.unop]⟩
  left_inv _ := rfl
  right_inv _ := rfl
@[simps]
def compYonedaSectionsEquiv (F : J ⥤ Cᵒᵖ) (X : C) :
    (F ⋙ yoneda.obj X).sections ≃ ((const J).obj (op X) ⟶ F) where
  toFun s :=
    { app := fun j => (s.val j).op
      naturality := fun j j' f => by
        dsimp
        rw [Category.id_comp]
        exact Quiver.Hom.unop_inj (s.property f).symm }
  invFun τ := ⟨fun j => (τ.app j).unop,
    fun {j j'} f => Quiver.Hom.op_inj (by simpa using (τ.naturality f).symm)⟩
  left_inv _ := rfl
  right_inv _ := rfl
end
variable {J : Type v} [SmallCategory J] {C : Type u} [Category.{v} C]
@[simps!]
noncomputable def limitCompCoyonedaIsoCone (F : J ⥤ C) (X : C) :
    limit (F ⋙ coyoneda.obj (op X)) ≅ ((const J).obj X ⟶ F) :=
  ((Types.limitEquivSections _).trans (compCoyonedaSectionsEquiv F X)).toIso
@[simps!]
noncomputable def coyonedaCompLimIsoCones (F : J ⥤ C) :
    coyoneda ⋙ (whiskeringLeft _ _ _).obj F ⋙ lim ≅ F.cones :=
  NatIso.ofComponents (fun X => limitCompCoyonedaIsoCone F X.unop)
variable (J) (C) in
@[simps!]
noncomputable def whiskeringLimYonedaIsoCones : whiskeringLeft _ _ _ ⋙
    (whiskeringRight _ _ _).obj lim ⋙ (whiskeringLeft _ _ _).obj coyoneda ≅ cones J C :=
  NatIso.ofComponents coyonedaCompLimIsoCones
@[simps!]
noncomputable def limitCompYonedaIsoCocone (F : J ⥤ C) (X : C) :
    limit (F.op ⋙ yoneda.obj X) ≅ (F ⟶ (const J).obj X) :=
  ((Types.limitEquivSections _).trans (opCompYonedaSectionsEquiv F X)).toIso
@[simps!]
noncomputable def yonedaCompLimIsoCocones (F : J ⥤ C) :
    yoneda ⋙ (whiskeringLeft _ _ _).obj F.op ⋙ lim ≅ F.cocones :=
  NatIso.ofComponents (limitCompYonedaIsoCocone F)
variable (J) (C) in
@[simps!]
noncomputable def opHomCompWhiskeringLimYonedaIsoCocones : opHom _ _ ⋙ whiskeringLeft _ _ _ ⋙
      (whiskeringRight _ _ _).obj lim ⋙ (whiskeringLeft _ _ _).obj yoneda ≅ cocones J C :=
  NatIso.ofComponents (fun F => yonedaCompLimIsoCocones F.unop)
end CategoryTheory.Limits