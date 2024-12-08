import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Basic
universe w v v₁ v₂ u u₁ u₂
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (G : C ⥤ D)
namespace CategoryTheory.Limits
variable (X : C)
section Terminal
def isLimitMapConeEmptyConeEquiv :
    IsLimit (G.mapCone (asEmptyCone X)) ≃ IsTerminal (G.obj X) :=
  isLimitEmptyConeEquiv D _ _ (eqToIso rfl)
def IsTerminal.isTerminalObj [PreservesLimit (Functor.empty.{0} C) G] (l : IsTerminal X) :
    IsTerminal (G.obj X) :=
  isLimitMapConeEmptyConeEquiv G X (isLimitOfPreserves G l)
def IsTerminal.isTerminalOfObj [ReflectsLimit (Functor.empty.{0} C) G] (l : IsTerminal (G.obj X)) :
    IsTerminal X :=
  isLimitOfReflects G ((isLimitMapConeEmptyConeEquiv G X).symm l)
def IsTerminal.isTerminalIffObj [PreservesLimit (Functor.empty.{0} C) G]
    [ReflectsLimit (Functor.empty.{0} C) G] (X : C) :
    IsTerminal X ≃ IsTerminal (G.obj X) where
  toFun := IsTerminal.isTerminalObj G X
  invFun := IsTerminal.isTerminalOfObj G X
  left_inv := by aesop_cat
  right_inv := by aesop_cat
lemma preservesLimitsOfShape_pempty_of_preservesTerminal [PreservesLimit (Functor.empty.{0} C) G] :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) G where
  preservesLimit := preservesLimit_of_iso_diagram G (Functor.emptyExt (Functor.empty.{0} C) _)
variable [HasTerminal C]
def isLimitOfHasTerminalOfPreservesLimit [PreservesLimit (Functor.empty.{0} C) G] :
    IsTerminal (G.obj (⊤_ C)) :=
  terminalIsTerminal.isTerminalObj G (⊤_ C)
theorem hasTerminal_of_hasTerminal_of_preservesLimit [PreservesLimit (Functor.empty.{0} C) G] :
    HasTerminal D := ⟨fun F => by
  haveI := HasLimit.mk ⟨_, isLimitOfHasTerminalOfPreservesLimit G⟩
  apply hasLimitOfIso F.uniqueFromEmpty.symm⟩
variable [HasTerminal D]
lemma PreservesTerminal.of_iso_comparison [i : IsIso (terminalComparison G)] :
    PreservesLimit (Functor.empty.{0} C) G := by
  apply preservesLimit_of_preserves_limit_cone terminalIsTerminal
  apply (isLimitMapConeEmptyConeEquiv _ _).symm _
  exact @IsLimit.ofPointIso _ _ _ _ _ _ _ (limit.isLimit (Functor.empty.{0} D)) i
lemma preservesTerminal_of_isIso (f : G.obj (⊤_ C) ⟶ ⊤_ D) [i : IsIso f] :
    PreservesLimit (Functor.empty.{0} C) G := by
  rw [Subsingleton.elim f (terminalComparison G)] at i
  exact PreservesTerminal.of_iso_comparison G
lemma preservesTerminal_of_iso (f : G.obj (⊤_ C) ≅ ⊤_ D) : PreservesLimit (Functor.empty.{0} C) G :=
  preservesTerminal_of_isIso G f.hom
variable [PreservesLimit (Functor.empty.{0} C) G]
def PreservesTerminal.iso : G.obj (⊤_ C) ≅ ⊤_ D :=
  (isLimitOfHasTerminalOfPreservesLimit G).conePointUniqueUpToIso (limit.isLimit _)
@[simp]
theorem PreservesTerminal.iso_hom : (PreservesTerminal.iso G).hom = terminalComparison G :=
  rfl
instance : IsIso (terminalComparison G) := by
  rw [← PreservesTerminal.iso_hom]
  infer_instance
end Terminal
section Initial
def isColimitMapCoconeEmptyCoconeEquiv :
    IsColimit (G.mapCocone (asEmptyCocone.{v₁} X)) ≃ IsInitial (G.obj X) :=
  isColimitEmptyCoconeEquiv D _ _ (eqToIso rfl)
def IsInitial.isInitialObj [PreservesColimit (Functor.empty.{0} C) G] (l : IsInitial X) :
    IsInitial (G.obj X) :=
  isColimitMapCoconeEmptyCoconeEquiv G X (isColimitOfPreserves G l)
def IsInitial.isInitialOfObj [ReflectsColimit (Functor.empty.{0} C) G] (l : IsInitial (G.obj X)) :
    IsInitial X :=
  isColimitOfReflects G ((isColimitMapCoconeEmptyCoconeEquiv G X).symm l)
def IsInitial.isInitialIffObj [PreservesColimit (Functor.empty.{0} C) G]
    [ReflectsColimit (Functor.empty.{0} C) G] (X : C) :
    IsInitial X ≃ IsInitial (G.obj X) where
  toFun := IsInitial.isInitialObj G X
  invFun := IsInitial.isInitialOfObj G X
  left_inv := by aesop_cat
  right_inv := by aesop_cat
lemma preservesColimitsOfShape_pempty_of_preservesInitial
    [PreservesColimit (Functor.empty.{0} C) G] :
    PreservesColimitsOfShape (Discrete PEmpty.{1}) G where
  preservesColimit :=
    preservesColimit_of_iso_diagram G (Functor.emptyExt (Functor.empty.{0} C) _)
variable [HasInitial C]
def isColimitOfHasInitialOfPreservesColimit [PreservesColimit (Functor.empty.{0} C) G] :
    IsInitial (G.obj (⊥_ C)) :=
  initialIsInitial.isInitialObj G (⊥_ C)
theorem hasInitial_of_hasInitial_of_preservesColimit [PreservesColimit (Functor.empty.{0} C) G] :
    HasInitial D :=
  ⟨fun F => by
    haveI := HasColimit.mk ⟨_, isColimitOfHasInitialOfPreservesColimit G⟩
    apply hasColimitOfIso F.uniqueFromEmpty⟩
variable [HasInitial D]
lemma PreservesInitial.of_iso_comparison [i : IsIso (initialComparison G)] :
    PreservesColimit (Functor.empty.{0} C) G := by
  apply preservesColimit_of_preserves_colimit_cocone initialIsInitial
  apply (isColimitMapCoconeEmptyCoconeEquiv _ _).symm _
  exact @IsColimit.ofPointIso _ _ _ _ _ _ _ (colimit.isColimit (Functor.empty.{0} D)) i
lemma preservesInitial_of_isIso (f : ⊥_ D ⟶ G.obj (⊥_ C)) [i : IsIso f] :
    PreservesColimit (Functor.empty.{0} C) G := by
  rw [Subsingleton.elim f (initialComparison G)] at i
  exact PreservesInitial.of_iso_comparison G
lemma preservesInitial_of_iso (f : ⊥_ D ≅ G.obj (⊥_ C)) :
    PreservesColimit (Functor.empty.{0} C) G :=
  preservesInitial_of_isIso G f.hom
variable [PreservesColimit (Functor.empty.{0} C) G]
def PreservesInitial.iso : G.obj (⊥_ C) ≅ ⊥_ D :=
  (isColimitOfHasInitialOfPreservesColimit G).coconePointUniqueUpToIso (colimit.isColimit _)
@[simp]
theorem PreservesInitial.iso_hom : (PreservesInitial.iso G).inv = initialComparison G :=
  rfl
instance : IsIso (initialComparison G) := by
  rw [← PreservesInitial.iso_hom]
  infer_instance
end Initial
end CategoryTheory.Limits