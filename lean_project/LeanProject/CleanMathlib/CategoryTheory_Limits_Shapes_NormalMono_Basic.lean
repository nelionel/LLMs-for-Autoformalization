import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Basic
noncomputable section
namespace CategoryTheory
open CategoryTheory.Limits
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C]
variable {X Y : C}
section
variable [HasZeroMorphisms C]
class NormalMono (f : X ⟶ Y) where
  Z : C 
  g : Y ⟶ Z
  w : f ≫ g = 0
  isLimit : IsLimit (KernelFork.ofι f w)
attribute [inherit_doc NormalMono] NormalMono.Z NormalMono.g NormalMono.w NormalMono.isLimit
section
def equivalenceReflectsNormalMono {D : Type u₂} [Category.{v₁} D] [HasZeroMorphisms D] (F : C ⥤ D)
    [F.IsEquivalence] {X Y : C} {f : X ⟶ Y} (hf : NormalMono (F.map f)) : NormalMono f where
  Z := F.objPreimage hf.Z
  g := F.preimage (hf.g ≫ (F.objObjPreimageIso hf.Z).inv)
  w := F.map_injective <| by
    have reassoc' {W : D} (h : hf.Z ⟶ W) : F.map f ≫ hf.g ≫ h = 0 ≫ h := by
      rw [← Category.assoc, eq_whisker hf.w]
    simp [reassoc']
  isLimit := isLimitOfReflects F <|
    IsLimit.ofConeEquiv (Cones.postcomposeEquivalence (compNatIso F)) <|
      (IsLimit.ofIsoLimit (IsKernel.ofCompIso _ _ (F.objObjPreimageIso hf.Z) (by
        simp only [Functor.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id])
        hf.isLimit)) (Fork.ext (Iso.refl _) (by simp [compNatIso, Fork.ι]))
end
instance (priority := 100) NormalMono.regularMono (f : X ⟶ Y) [I : NormalMono f] : RegularMono f :=
  { I with
    left := I.g
    right := 0
    w := by simpa using I.w }
def NormalMono.lift' {W : C} (f : X ⟶ Y) [hf : NormalMono f] (k : W ⟶ Y) (h : k ≫ hf.g = 0) :
    { l : W ⟶ X // l ≫ f = k } :=
  KernelFork.IsLimit.lift' NormalMono.isLimit _ h
def normalOfIsPullbackSndOfNormal {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    [hn : NormalMono h] (comm : f ≫ h = g ≫ k) (t : IsLimit (PullbackCone.mk _ _ comm)) :
    NormalMono g where
  Z := hn.Z
  g := k ≫ hn.g
  w := by
    have reassoc' {W : C} (h' : S ⟶ W) : f ≫ h ≫ h' = g ≫ k ≫ h' := by
      simp only [← Category.assoc, eq_whisker comm]
    rw [← reassoc', hn.w, HasZeroMorphisms.comp_zero]
  isLimit := by
    letI gr := regularOfIsPullbackSndOfRegular comm t
    have q := (HasZeroMorphisms.comp_zero k hn.Z).symm
    convert gr.isLimit
def normalOfIsPullbackFstOfNormal {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    [NormalMono k] (comm : f ≫ h = g ≫ k) (t : IsLimit (PullbackCone.mk _ _ comm)) :
    NormalMono f :=
  normalOfIsPullbackSndOfNormal comm.symm (PullbackCone.flipIsLimit t)
section
variable (C)
class NormalMonoCategory where
  normalMonoOfMono : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], NormalMono f
attribute [inherit_doc NormalMonoCategory] NormalMonoCategory.normalMonoOfMono
end
def normalMonoOfMono [NormalMonoCategory C] (f : X ⟶ Y) [Mono f] : NormalMono f :=
  NormalMonoCategory.normalMonoOfMono _
instance (priority := 100) regularMonoCategoryOfNormalMonoCategory [NormalMonoCategory C] :
    RegularMonoCategory C where
  regularMonoOfMono f _ := by
    haveI := normalMonoOfMono f
    infer_instance
end
section
variable [HasZeroMorphisms C]
class NormalEpi (f : X ⟶ Y) where
  W : C
  g : W ⟶ X
  w : g ≫ f = 0
  isColimit : IsColimit (CokernelCofork.ofπ f w)
attribute [inherit_doc NormalEpi] NormalEpi.W NormalEpi.g NormalEpi.w NormalEpi.isColimit
section
def equivalenceReflectsNormalEpi {D : Type u₂} [Category.{v₁} D] [HasZeroMorphisms D] (F : C ⥤ D)
    [F.IsEquivalence] {X Y : C} {f : X ⟶ Y} (hf : NormalEpi (F.map f)) : NormalEpi f where
  W := F.objPreimage hf.W
  g := F.preimage ((F.objObjPreimageIso hf.W).hom ≫ hf.g)
  w := F.map_injective <| by simp [hf.w]
  isColimit := isColimitOfReflects F <|
    IsColimit.ofCoconeEquiv (Cocones.precomposeEquivalence (compNatIso F).symm) <|
      (IsColimit.ofIsoColimit
        (IsCokernel.ofIsoComp _ _ (F.objObjPreimageIso hf.W).symm (by simp) hf.isColimit)
          (Cofork.ext (Iso.refl _) (by simp [compNatIso, Cofork.π])))
end
instance (priority := 100) NormalEpi.regularEpi (f : X ⟶ Y) [I : NormalEpi f] : RegularEpi f :=
  { I with
    left := I.g
    right := 0
    w := by simpa using I.w }
def NormalEpi.desc' {W : C} (f : X ⟶ Y) [nef : NormalEpi f] (k : X ⟶ W) (h : nef.g ≫ k = 0) :
    { l : Y ⟶ W // f ≫ l = k } :=
  CokernelCofork.IsColimit.desc' NormalEpi.isColimit _ h
def normalOfIsPushoutSndOfNormal {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    [gn : NormalEpi g] (comm : f ≫ h = g ≫ k) (t : IsColimit (PushoutCocone.mk _ _ comm)) :
    NormalEpi h where
  W := gn.W
  g := gn.g ≫ f
  w := by
    have reassoc' {W : C} (h' : R ⟶ W) :  gn.g ≫ g ≫ h' = 0 ≫ h' := by
      rw [← Category.assoc, eq_whisker gn.w]
    rw [Category.assoc, comm, reassoc', zero_comp]
  isColimit := by
    letI hn := regularOfIsPushoutSndOfRegular comm t
    have q := (@zero_comp _ _ _ gn.W _ _ f).symm
    convert hn.isColimit
def normalOfIsPushoutFstOfNormal {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    [NormalEpi f] (comm : f ≫ h = g ≫ k) (t : IsColimit (PushoutCocone.mk _ _ comm)) :
    NormalEpi k :=
  normalOfIsPushoutSndOfNormal comm.symm (PushoutCocone.flipIsColimit t)
end
open Opposite
variable [HasZeroMorphisms C]
def normalEpiOfNormalMonoUnop {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : NormalMono f.unop) : NormalEpi f where
  W := op m.Z
  g := m.g.op
  w := congrArg Quiver.Hom.op m.w
  isColimit :=
    CokernelCofork.IsColimit.ofπ _ _
      (fun g' w' =>
        (KernelFork.IsLimit.lift' m.isLimit g'.unop (congrArg Quiver.Hom.unop w')).1.op)
      (fun g' w' =>
        congrArg Quiver.Hom.op
          (KernelFork.IsLimit.lift' m.isLimit g'.unop (congrArg Quiver.Hom.unop w')).2)
      (by
        rintro Z' g' w' m' rfl
        apply Quiver.Hom.unop_inj
        apply m.isLimit.uniq (KernelFork.ofι (m'.unop ≫ f.unop) _) m'.unop
        rintro (⟨⟩ | ⟨⟩) <;> simp)
def normalMonoOfNormalEpiUnop {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : NormalEpi f.unop) : NormalMono f where
  Z := op m.W
  g := m.g.op
  w := congrArg Quiver.Hom.op m.w
  isLimit :=
    KernelFork.IsLimit.ofι _ _
      (fun g' w' =>
        (CokernelCofork.IsColimit.desc' m.isColimit g'.unop (congrArg Quiver.Hom.unop w')).1.op)
      (fun g' w' =>
        congrArg Quiver.Hom.op
          (CokernelCofork.IsColimit.desc' m.isColimit g'.unop (congrArg Quiver.Hom.unop w')).2)
      (by
        rintro Z' g' w' m' rfl
        apply Quiver.Hom.unop_inj
        apply m.isColimit.uniq (CokernelCofork.ofπ (f.unop ≫ m'.unop) _) m'.unop
        rintro (⟨⟩ | ⟨⟩) <;> simp)
section
variable (C)
class NormalEpiCategory where
  normalEpiOfEpi : ∀ {X Y : C} (f : X ⟶ Y) [Epi f], NormalEpi f
attribute [inherit_doc NormalEpiCategory] NormalEpiCategory.normalEpiOfEpi
end
def normalEpiOfEpi [NormalEpiCategory C] (f : X ⟶ Y) [Epi f] : NormalEpi f :=
  NormalEpiCategory.normalEpiOfEpi _
instance (priority := 100) regularEpiCategoryOfNormalEpiCategory [NormalEpiCategory C] :
    RegularEpiCategory C where
  regularEpiOfEpi f _ := by
    haveI := normalEpiOfEpi f
    infer_instance
end CategoryTheory