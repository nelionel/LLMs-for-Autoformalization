import Mathlib.Topology.Sheaves.PUnit
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.Sheaves.Functors
noncomputable section
open TopologicalSpace TopCat CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry
universe u v w
variable {X : TopCat.{u}} (p₀ : X) [∀ U : Opens X, Decidable (p₀ ∈ U)]
section
variable {C : Type v} [Category.{w} C] [HasTerminal C] (A : C)
@[simps]
def skyscraperPresheaf : Presheaf C X where
  obj U := if p₀ ∈ unop U then A else terminal C
  map {U V} i :=
    if h : p₀ ∈ unop V then eqToHom <| by dsimp; rw [if_pos h, if_pos (by simpa using i.unop.le h)]
    else ((if_neg h).symm.ndrec terminalIsTerminal).from _
  map_id U :=
    (em (p₀ ∈ U.unop)).elim (fun h => dif_pos h) fun h =>
      ((if_neg h).symm.ndrec terminalIsTerminal).hom_ext _ _
  map_comp {U V W} iVU iWV := by
    by_cases hW : p₀ ∈ unop W
    · have hV : p₀ ∈ unop V := leOfHom iWV.unop hW
      simp only [dif_pos hW, dif_pos hV, eqToHom_trans]
    · dsimp; rw [dif_neg hW]; apply ((if_neg hW).symm.ndrec terminalIsTerminal).hom_ext
theorem skyscraperPresheaf_eq_pushforward
    [hd : ∀ U : Opens (TopCat.of PUnit.{u + 1}), Decidable (PUnit.unit ∈ U)] :
    skyscraperPresheaf p₀ A =
      ContinuousMap.const (TopCat.of PUnit) p₀ _*
        skyscraperPresheaf (X := TopCat.of PUnit) PUnit.unit A := by
  convert_to @skyscraperPresheaf X p₀ (fun U => hd <| (Opens.map <| ContinuousMap.const _ p₀).obj U)
    C _ _ A = _ <;> congr
@[simps]
def SkyscraperPresheafFunctor.map' {a b : C} (f : a ⟶ b) :
    skyscraperPresheaf p₀ a ⟶ skyscraperPresheaf p₀ b where
  app U :=
    if h : p₀ ∈ U.unop then eqToHom (if_pos h) ≫ f ≫ eqToHom (if_pos h).symm
    else ((if_neg h).symm.ndrec terminalIsTerminal).from _
  naturality U V i := by
    simp only [skyscraperPresheaf_map]
    by_cases hV : p₀ ∈ V.unop
    · have hU : p₀ ∈ U.unop := leOfHom i.unop hV
      simp only [skyscraperPresheaf_obj, hU, hV, ↓reduceDIte, eqToHom_trans_assoc, Category.assoc,
        eqToHom_trans]
    · apply ((if_neg hV).symm.ndrec terminalIsTerminal).hom_ext
theorem SkyscraperPresheafFunctor.map'_id {a : C} :
    SkyscraperPresheafFunctor.map' p₀ (𝟙 a) = 𝟙 _ := by
  ext U
  simp only [SkyscraperPresheafFunctor.map'_app, NatTrans.id_app]; split_ifs <;> aesop_cat
theorem SkyscraperPresheafFunctor.map'_comp {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
    SkyscraperPresheafFunctor.map' p₀ (f ≫ g) =
      SkyscraperPresheafFunctor.map' p₀ f ≫ SkyscraperPresheafFunctor.map' p₀ g := by
  ext U
  simp only [SkyscraperPresheafFunctor.map'_app, NatTrans.comp_app]
  split_ifs with h <;> aesop_cat
@[simps]
def skyscraperPresheafFunctor : C ⥤ Presheaf C X where
  obj := skyscraperPresheaf p₀
  map := SkyscraperPresheafFunctor.map' p₀
  map_id _ := SkyscraperPresheafFunctor.map'_id p₀
  map_comp := SkyscraperPresheafFunctor.map'_comp p₀
end
section
variable {C : Type v} [Category.{u} C] (A : C) [HasTerminal C]
@[simps]
def skyscraperPresheafCoconeOfSpecializes {y : X} (h : p₀ ⤳ y) :
    Cocone ((OpenNhds.inclusion y).op ⋙ skyscraperPresheaf p₀ A) where
  pt := A
  ι :=
    { app := fun U => eqToHom <| if_pos <| h.mem_open U.unop.1.2 U.unop.2
      naturality := fun U V inc => by
        change dite _ _ _ ≫ _ = _; rw [dif_pos]
        swap 
        · exact h.mem_open V.unop.1.2 V.unop.2
        · simp only [Functor.comp_obj, Functor.op_obj, skyscraperPresheaf_obj, unop_op,
            Functor.const_obj_obj, eqToHom_trans, Functor.const_obj_map, Category.comp_id] }
noncomputable def skyscraperPresheafCoconeIsColimitOfSpecializes {y : X} (h : p₀ ⤳ y) :
    IsColimit (skyscraperPresheafCoconeOfSpecializes p₀ A h) where
  desc c := eqToHom (if_pos trivial).symm ≫ c.ι.app (op ⊤)
  fac c U := by
    dsimp 
    rw [← c.w (homOfLE <| (le_top : unop U ≤ _)).op]
    change _ ≫ _ ≫ dite _ _ _ ≫ _ = _
    rw [dif_pos]
    · simp only [skyscraperPresheafCoconeOfSpecializes_ι_app, eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp, unop_op, op_unop]
    · exact h.mem_open U.unop.1.2 U.unop.2
  uniq c f h := by
    dsimp 
    rw [← h, skyscraperPresheafCoconeOfSpecializes_ι_app, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
noncomputable def skyscraperPresheafStalkOfSpecializes [HasColimits C] {y : X} (h : p₀ ⤳ y) :
    (skyscraperPresheaf p₀ A).stalk y ≅ A :=
  colimit.isoColimitCocone ⟨_, skyscraperPresheafCoconeIsColimitOfSpecializes p₀ A h⟩
@[reassoc (attr := simp)]
lemma germ_skyscraperPresheafStalkOfSpecializes_hom [HasColimits C] {y : X} (h : p₀ ⤳ y) (U hU) :
    (skyscraperPresheaf p₀ A).germ U y hU ≫
      (skyscraperPresheafStalkOfSpecializes p₀ A h).hom = eqToHom (if_pos (h.mem_open U.2 hU)) :=
  colimit.isoColimitCocone_ι_hom _ _
@[simps]
def skyscraperPresheafCocone (y : X) :
    Cocone ((OpenNhds.inclusion y).op ⋙ skyscraperPresheaf p₀ A) where
  pt := terminal C
  ι :=
    { app := fun _ => terminal.from _
      naturality := fun _ _ _ => terminalIsTerminal.hom_ext _ _ }
noncomputable def skyscraperPresheafCoconeIsColimitOfNotSpecializes {y : X} (h : ¬p₀ ⤳ y) :
    IsColimit (skyscraperPresheafCocone p₀ A y) :=
  let h1 : ∃ U : OpenNhds y, p₀ ∉ U.1 :=
    let ⟨U, ho, h₀, hy⟩ := not_specializes_iff_exists_open.mp h
    ⟨⟨⟨U, ho⟩, h₀⟩, hy⟩
  { desc := fun c => eqToHom (if_neg h1.choose_spec).symm ≫ c.ι.app (op h1.choose)
    fac := fun c U => by
      change _ = c.ι.app (op U.unop)
      simp only [← c.w (homOfLE <| @inf_le_left _ _ h1.choose U.unop).op, ←
        c.w (homOfLE <| @inf_le_right _ _ h1.choose U.unop).op, ← Category.assoc]
      congr 1
      refine ((if_neg ?_).symm.ndrec terminalIsTerminal).hom_ext _ _
      exact fun h => h1.choose_spec h.1
    uniq := fun c f H => by
      dsimp 
      rw [← Category.id_comp f, ← H, ← Category.assoc]
      congr 1; apply terminalIsTerminal.hom_ext }
noncomputable def skyscraperPresheafStalkOfNotSpecializes [HasColimits C] {y : X} (h : ¬p₀ ⤳ y) :
    (skyscraperPresheaf p₀ A).stalk y ≅ terminal C :=
  colimit.isoColimitCocone ⟨_, skyscraperPresheafCoconeIsColimitOfNotSpecializes _ A h⟩
def skyscraperPresheafStalkOfNotSpecializesIsTerminal [HasColimits C] {y : X} (h : ¬p₀ ⤳ y) :
    IsTerminal ((skyscraperPresheaf p₀ A).stalk y) :=
  IsTerminal.ofIso terminalIsTerminal <| (skyscraperPresheafStalkOfNotSpecializes _ _ h).symm
theorem skyscraperPresheaf_isSheaf : (skyscraperPresheaf p₀ A).IsSheaf := by
  classical exact
    (Presheaf.isSheaf_iso_iff (eqToIso <| skyscraperPresheaf_eq_pushforward p₀ A)).mpr <|
      (Sheaf.pushforward_sheaf_of_sheaf _
        (Presheaf.isSheaf_on_punit_of_isTerminal _ (by
          dsimp [skyscraperPresheaf]
          rw [if_neg]
          · exact terminalIsTerminal
          · #adaptation_note 
            exact Set.not_mem_empty PUnit.unit.{u+1})))
def skyscraperSheaf : Sheaf C X :=
  ⟨skyscraperPresheaf p₀ A, skyscraperPresheaf_isSheaf _ _⟩
def skyscraperSheafFunctor : C ⥤ Sheaf C X where
  obj c := skyscraperSheaf p₀ c
  map f := Sheaf.Hom.mk <| (skyscraperPresheafFunctor p₀).map f
  map_id _ := Sheaf.Hom.ext <| (skyscraperPresheafFunctor p₀).map_id _
  map_comp _ _ := Sheaf.Hom.ext <| (skyscraperPresheafFunctor p₀).map_comp _ _
namespace StalkSkyscraperPresheafAdjunctionAuxs
variable [HasColimits C]
@[simps]
def toSkyscraperPresheaf {𝓕 : Presheaf C X} {c : C} (f : 𝓕.stalk p₀ ⟶ c) :
    𝓕 ⟶ skyscraperPresheaf p₀ c where
  app U :=
    if h : p₀ ∈ U.unop then 𝓕.germ _ p₀ h ≫ f ≫ eqToHom (if_pos h).symm
    else ((if_neg h).symm.ndrec terminalIsTerminal).from _
  naturality U V inc := by
    dsimp
    by_cases hV : p₀ ∈ V.unop
    · have hU : p₀ ∈ U.unop := leOfHom inc.unop hV
      split_ifs
      rw [← Category.assoc, 𝓕.germ_res' inc, Category.assoc, Category.assoc, eqToHom_trans]
    · split_ifs
      exact ((if_neg hV).symm.ndrec terminalIsTerminal).hom_ext ..
def fromStalk {𝓕 : Presheaf C X} {c : C} (f : 𝓕 ⟶ skyscraperPresheaf p₀ c) : 𝓕.stalk p₀ ⟶ c :=
  let χ : Cocone ((OpenNhds.inclusion p₀).op ⋙ 𝓕) :=
    Cocone.mk c <|
      { app := fun U => f.app ((OpenNhds.inclusion p₀).op.obj U) ≫ eqToHom (if_pos U.unop.2)
        naturality := fun U V inc => by
          dsimp only [Functor.const_obj_map, Functor.const_obj_obj, Functor.comp_map,
            Functor.comp_obj, Functor.op_obj, skyscraperPresheaf_obj]
          rw [Category.comp_id, ← Category.assoc, comp_eqToHom_iff, Category.assoc,
            eqToHom_trans, f.naturality, skyscraperPresheaf_map]
          have hV : p₀ ∈ (OpenNhds.inclusion p₀).obj V.unop := V.unop.2
          simp only [dif_pos hV] }
  colimit.desc _ χ
@[reassoc (attr := simp)]
lemma germ_fromStalk {𝓕 : Presheaf C X} {c : C} (f : 𝓕 ⟶ skyscraperPresheaf p₀ c) (U) (hU) :
    𝓕.germ U p₀ hU ≫ fromStalk p₀ f = f.app (op U) ≫ eqToHom (if_pos hU) :=
  colimit.ι_desc _ _
theorem to_skyscraper_fromStalk {𝓕 : Presheaf C X} {c : C} (f : 𝓕 ⟶ skyscraperPresheaf p₀ c) :
    toSkyscraperPresheaf p₀ (fromStalk _ f) = f := by
  apply NatTrans.ext
  ext U
  dsimp
  split_ifs with h
  · rw [← Category.assoc, germ_fromStalk, Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.comp_id]
  · exact ((if_neg h).symm.ndrec terminalIsTerminal).hom_ext ..
theorem fromStalk_to_skyscraper {𝓕 : Presheaf C X} {c : C} (f : 𝓕.stalk p₀ ⟶ c) :
    fromStalk p₀ (toSkyscraperPresheaf _ f) = f := by
  refine 𝓕.stalk_hom_ext fun U hxU ↦ ?_
  rw [germ_fromStalk, toSkyscraperPresheaf_app, dif_pos hxU, Category.assoc, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id, Presheaf.germ]
@[simps]
protected def unit :
    𝟭 (Presheaf C X) ⟶ Presheaf.stalkFunctor C p₀ ⋙ skyscraperPresheafFunctor p₀ where
  app _ := toSkyscraperPresheaf _ <| 𝟙 _
  naturality 𝓕 𝓖 f := by
    ext U; dsimp
    split_ifs with h
    · simp only [Category.id_comp, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Presheaf.stalkFunctor_map_germ_assoc, Presheaf.stalkFunctor_obj]
    · apply ((if_neg h).symm.ndrec terminalIsTerminal).hom_ext
@[simps]
protected def counit :
    skyscraperPresheafFunctor p₀ ⋙ (Presheaf.stalkFunctor C p₀ : Presheaf C X ⥤ C) ⟶ 𝟭 C where
  app c := (skyscraperPresheafStalkOfSpecializes p₀ c specializes_rfl).hom
  naturality x y f := TopCat.Presheaf.stalk_hom_ext _ fun U hxU ↦ by simp [hxU]
end StalkSkyscraperPresheafAdjunctionAuxs
section
open StalkSkyscraperPresheafAdjunctionAuxs
def skyscraperPresheafStalkAdjunction [HasColimits C] :
    (Presheaf.stalkFunctor C p₀ : Presheaf C X ⥤ C) ⊣ skyscraperPresheafFunctor p₀ where
  unit := StalkSkyscraperPresheafAdjunctionAuxs.unit _
  counit := StalkSkyscraperPresheafAdjunctionAuxs.counit _
  left_triangle_components X := by
    dsimp [Presheaf.stalkFunctor, toSkyscraperPresheaf]
    ext
    simp only [Functor.comp_obj, Functor.op_obj, ι_colimMap_assoc, skyscraperPresheaf_obj,
      whiskerLeft_app, Category.comp_id]
    split_ifs with h
    · simp [skyscraperPresheafStalkOfSpecializes]
      rfl
    · simp only [skyscraperPresheafStalkOfSpecializes, colimit.isoColimitCocone_ι_hom,
        skyscraperPresheafCoconeOfSpecializes_pt, skyscraperPresheafCoconeOfSpecializes_ι_app,
        Functor.comp_obj, Functor.op_obj, skyscraperPresheaf_obj, Functor.const_obj_obj]
      rw [comp_eqToHom_iff]
      apply ((if_neg h).symm.ndrec terminalIsTerminal).hom_ext
  right_triangle_components Y := by
    ext
    simp only [skyscraperPresheafFunctor_obj, Functor.id_obj, skyscraperPresheaf_obj,
      Functor.comp_obj, Presheaf.stalkFunctor_obj, unit_app, counit_app,
      skyscraperPresheafStalkOfSpecializes, skyscraperPresheafFunctor_map, Presheaf.comp_app,
      toSkyscraperPresheaf_app, Category.id_comp, SkyscraperPresheafFunctor.map'_app]
    split_ifs with h
    · simp [Presheaf.germ]
      rfl
    · simp
      rfl
instance [HasColimits C] : (skyscraperPresheafFunctor p₀ : C ⥤ Presheaf C X).IsRightAdjoint  :=
  (skyscraperPresheafStalkAdjunction _).isRightAdjoint
instance [HasColimits C] : (Presheaf.stalkFunctor C p₀).IsLeftAdjoint  :=
  have : ∀ U : Opens X, Decidable (p₀ ∈ U) := fun _ ↦ Classical.dec _
  (skyscraperPresheafStalkAdjunction _).isLeftAdjoint
def stalkSkyscraperSheafAdjunction [HasColimits C] :
    Sheaf.forget C X ⋙ Presheaf.stalkFunctor _ p₀ ⊣ skyscraperSheafFunctor p₀ where
  unit :=
    { app := fun 𝓕 => ⟨(StalkSkyscraperPresheafAdjunctionAuxs.unit p₀).app 𝓕.1⟩
      naturality := fun 𝓐 𝓑 f => Sheaf.Hom.ext <| by
        apply (StalkSkyscraperPresheafAdjunctionAuxs.unit p₀).naturality }
  counit := StalkSkyscraperPresheafAdjunctionAuxs.counit p₀
  left_triangle_components X :=
    ((skyscraperPresheafStalkAdjunction p₀).left_triangle_components X.val)
  right_triangle_components _ :=
    Sheaf.Hom.ext ((skyscraperPresheafStalkAdjunction p₀).right_triangle_components _)
instance [HasColimits C] : (skyscraperSheafFunctor p₀ : C ⥤ Sheaf C X).IsRightAdjoint  :=
  (stalkSkyscraperSheafAdjunction _).isRightAdjoint
end
end