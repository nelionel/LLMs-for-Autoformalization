import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
noncomputable section
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]
namespace CategoryTheory.Limits
namespace KernelFork
variable {X Y : C} {f : X ⟶ Y} (c : KernelFork f)
  (G : C ⥤ D) [Functor.PreservesZeroMorphisms G]
@[reassoc (attr := simp)]
lemma map_condition : G.map c.ι ≫ G.map f = 0 := by
  rw [← G.map_comp, c.condition, G.map_zero]
def map : KernelFork (G.map f) :=
  KernelFork.ofι (G.map c.ι) (c.map_condition G)
@[simp]
lemma map_ι : (c.map G).ι = G.map c.ι := rfl
def isLimitMapConeEquiv :
    IsLimit (G.mapCone c) ≃ IsLimit (c.map G) := by
  refine (IsLimit.postcomposeHomEquiv ?_ _).symm.trans (IsLimit.equivIsoLimit ?_)
  refine parallelPair.ext (Iso.refl _) (Iso.refl _) ?_ ?_ <;> simp
  exact Cones.ext (Iso.refl _) (by rintro (_|_) <;> aesop_cat)
def mapIsLimit (hc : IsLimit c) (G : C ⥤ D)
    [Functor.PreservesZeroMorphisms G] [PreservesLimit (parallelPair f 0) G] :
    IsLimit (c.map G) :=
  c.isLimitMapConeEquiv G (isLimitOfPreserves G hc)
end KernelFork
section Kernels
variable (G : C ⥤ D) [Functor.PreservesZeroMorphisms G]
  {X Y Z : C} {f : X ⟶ Y} {h : Z ⟶ X} (w : h ≫ f = 0)
def isLimitMapConeForkEquiv' :
    IsLimit (G.mapCone (KernelFork.ofι h w)) ≃
      IsLimit
        (KernelFork.ofι (G.map h) (by simp only [← G.map_comp, w, Functor.map_zero]) :
          Fork (G.map f) 0) :=
  KernelFork.isLimitMapConeEquiv _ _
def isLimitForkMapOfIsLimit' [PreservesLimit (parallelPair f 0) G]
    (l : IsLimit (KernelFork.ofι h w)) :
    IsLimit
      (KernelFork.ofι (G.map h) (by simp only [← G.map_comp, w, Functor.map_zero]) :
        Fork (G.map f) 0) :=
  isLimitMapConeForkEquiv' G w (isLimitOfPreserves G l)
variable (f)
variable [HasKernel f]
def isLimitOfHasKernelOfPreservesLimit [PreservesLimit (parallelPair f 0) G] :
    IsLimit
      (Fork.ofι (G.map (kernel.ι f))
          (by simp only [← G.map_comp, kernel.condition, comp_zero, Functor.map_zero]) :
        Fork (G.map f) 0) :=
  isLimitForkMapOfIsLimit' G (kernel.condition f) (kernelIsKernel f)
instance [PreservesLimit (parallelPair f 0) G] : HasKernel (G.map f) where
  exists_limit := ⟨⟨_, isLimitOfHasKernelOfPreservesLimit G f⟩⟩
variable [HasKernel (G.map f)]
lemma PreservesKernel.of_iso_comparison [i : IsIso (kernelComparison f G)] :
    PreservesLimit (parallelPair f 0) G := by
  apply preservesLimit_of_preserves_limit_cone (kernelIsKernel f)
  apply (isLimitMapConeForkEquiv' G (kernel.condition f)).symm _
  exact @IsLimit.ofPointIso _ _ _ _ _ _ _ (kernelIsKernel (G.map f)) i
variable [PreservesLimit (parallelPair f 0) G]
def PreservesKernel.iso : G.obj (kernel f) ≅ kernel (G.map f) :=
  IsLimit.conePointUniqueUpToIso (isLimitOfHasKernelOfPreservesLimit G f) (limit.isLimit _)
@[simp]
theorem PreservesKernel.iso_hom : (PreservesKernel.iso G f).hom = kernelComparison f G := by
  rw [← cancel_mono (kernel.ι _)]
  simp [PreservesKernel.iso]
instance : IsIso (kernelComparison f G) := by
  rw [← PreservesKernel.iso_hom]
  infer_instance
@[reassoc]
theorem kernel_map_comp_preserves_kernel_iso_inv {X' Y' : C} (g : X' ⟶ Y') [HasKernel g]
    [HasKernel (G.map g)] [PreservesLimit (parallelPair g 0) G] (p : X ⟶ X') (q : Y ⟶ Y')
    (hpq : f ≫ q = p ≫ g) :
    kernel.map (G.map f) (G.map g) (G.map p) (G.map q) (by rw [← G.map_comp, hpq, G.map_comp]) ≫
        (PreservesKernel.iso G _).inv =
      (PreservesKernel.iso G _).inv ≫ G.map (kernel.map f g p q hpq) := by
  rw [Iso.comp_inv_eq, Category.assoc, PreservesKernel.iso_hom, Iso.eq_inv_comp,
    PreservesKernel.iso_hom, kernelComparison_comp_kernel_map]
end Kernels
namespace CokernelCofork
variable {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f)
  (G : C ⥤ D) [Functor.PreservesZeroMorphisms G]
@[reassoc (attr := simp)]
lemma map_condition : G.map f ≫ G.map c.π = 0 := by
  rw [← G.map_comp, c.condition, G.map_zero]
def map : CokernelCofork (G.map f) :=
  CokernelCofork.ofπ (G.map c.π) (c.map_condition G)
@[simp]
lemma map_π : (c.map G).π = G.map c.π := rfl
def isColimitMapCoconeEquiv :
    IsColimit (G.mapCocone c) ≃ IsColimit (c.map G) := by
  refine (IsColimit.precomposeHomEquiv ?_ _).symm.trans (IsColimit.equivIsoColimit ?_)
  refine parallelPair.ext (Iso.refl _) (Iso.refl _) ?_ ?_ <;> simp
  exact Cocones.ext (Iso.refl _) (by rintro (_|_) <;> aesop_cat)
def mapIsColimit (hc : IsColimit c) (G : C ⥤ D)
    [Functor.PreservesZeroMorphisms G] [PreservesColimit (parallelPair f 0) G] :
    IsColimit (c.map G) :=
  c.isColimitMapCoconeEquiv G (isColimitOfPreserves G hc)
end CokernelCofork
section Cokernels
variable (G : C ⥤ D) [Functor.PreservesZeroMorphisms G]
  {X Y Z : C} {f : X ⟶ Y} {h : Y ⟶ Z} (w : f ≫ h = 0)
def isColimitMapCoconeCoforkEquiv' :
    IsColimit (G.mapCocone (CokernelCofork.ofπ h w)) ≃
      IsColimit
        (CokernelCofork.ofπ (G.map h) (by simp only [← G.map_comp, w, Functor.map_zero]) :
          Cofork (G.map f) 0) :=
  CokernelCofork.isColimitMapCoconeEquiv _ _
def isColimitCoforkMapOfIsColimit' [PreservesColimit (parallelPair f 0) G]
    (l : IsColimit (CokernelCofork.ofπ h w)) :
    IsColimit
      (CokernelCofork.ofπ (G.map h) (by simp only [← G.map_comp, w, Functor.map_zero]) :
        Cofork (G.map f) 0) :=
  isColimitMapCoconeCoforkEquiv' G w (isColimitOfPreserves G l)
variable (f)
variable [HasCokernel f]
def isColimitOfHasCokernelOfPreservesColimit [PreservesColimit (parallelPair f 0) G] :
    IsColimit
      (Cofork.ofπ (G.map (cokernel.π f))
          (by simp only [← G.map_comp, cokernel.condition, zero_comp, Functor.map_zero]) :
        Cofork (G.map f) 0) :=
  isColimitCoforkMapOfIsColimit' G (cokernel.condition f) (cokernelIsCokernel f)
instance [PreservesColimit (parallelPair f 0) G] : HasCokernel (G.map f) where
  exists_colimit := ⟨⟨_, isColimitOfHasCokernelOfPreservesColimit G f⟩⟩
variable [HasCokernel (G.map f)]
lemma PreservesCokernel.of_iso_comparison [i : IsIso (cokernelComparison f G)] :
    PreservesColimit (parallelPair f 0) G := by
  apply preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f)
  apply (isColimitMapCoconeCoforkEquiv' G (cokernel.condition f)).symm _
  exact @IsColimit.ofPointIso _ _ _ _ _ _ _ (cokernelIsCokernel (G.map f)) i
variable [PreservesColimit (parallelPair f 0) G]
def PreservesCokernel.iso : G.obj (cokernel f) ≅ cokernel (G.map f) :=
  IsColimit.coconePointUniqueUpToIso (isColimitOfHasCokernelOfPreservesColimit G f)
    (colimit.isColimit _)
@[simp]
theorem PreservesCokernel.iso_inv : (PreservesCokernel.iso G f).inv = cokernelComparison f G := by
  rw [← cancel_epi (cokernel.π _)]
  simp [PreservesCokernel.iso]
instance : IsIso (cokernelComparison f G) := by
  rw [← PreservesCokernel.iso_inv]
  infer_instance
@[reassoc]
theorem preserves_cokernel_iso_comp_cokernel_map {X' Y' : C} (g : X' ⟶ Y') [HasCokernel g]
    [HasCokernel (G.map g)] [PreservesColimit (parallelPair g 0) G] (p : X ⟶ X') (q : Y ⟶ Y')
    (hpq : f ≫ q = p ≫ g) :
    (PreservesCokernel.iso G _).hom ≫
        cokernel.map (G.map f) (G.map g) (G.map p) (G.map q)
          (by rw [← G.map_comp, hpq, G.map_comp]) =
      G.map (cokernel.map f g p q hpq) ≫ (PreservesCokernel.iso G _).hom := by
  rw [← Iso.comp_inv_eq, Category.assoc, ← Iso.eq_inv_comp, PreservesCokernel.iso_inv,
    cokernel_map_comp_cokernelComparison, PreservesCokernel.iso_inv]
end Cokernels
variable (X Y : C) (G : C ⥤ D) [Functor.PreservesZeroMorphisms G]
instance preservesKernel_zero :
    PreservesLimit (parallelPair (0 : X ⟶ Y) 0) G where
  preserves {c} hc := ⟨by
    have := KernelFork.IsLimit.isIso_ι c hc rfl
    refine (KernelFork.isLimitMapConeEquiv c G).symm ?_
    refine IsLimit.ofIsoLimit (KernelFork.IsLimit.ofId _ (G.map_zero _ _)) ?_
    exact (Fork.ext (G.mapIso (asIso (Fork.ι c))).symm (by simp))⟩
noncomputable instance preservesCokernel_zero :
    PreservesColimit (parallelPair (0 : X ⟶ Y) 0) G where
  preserves {c} hc := ⟨by
    have := CokernelCofork.IsColimit.isIso_π c hc rfl
    refine (CokernelCofork.isColimitMapCoconeEquiv c G).symm ?_
    refine IsColimit.ofIsoColimit (CokernelCofork.IsColimit.ofId _ (G.map_zero _ _)) ?_
    exact (Cofork.ext (G.mapIso (asIso (Cofork.π c))) (by simp))⟩
variable {X Y}
lemma preservesKernel_zero' (f : X ⟶ Y) (hf : f = 0) :
    PreservesLimit (parallelPair f 0) G := by
  rw [hf]
  infer_instance
lemma preservesCokernel_zero' (f : X ⟶ Y) (hf : f = 0) :
    PreservesColimit (parallelPair f 0) G := by
  rw [hf]
  infer_instance
end CategoryTheory.Limits