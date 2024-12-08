import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Generator
universe v v₁ u u₁
open CategoryTheory Limits
namespace PresheafOfModules
variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{v}}
noncomputable def freeYonedaEquiv {M : PresheafOfModules.{v} R} {X : C} :
    ((free R).obj (yoneda.obj X) ⟶ M) ≃ M.obj (Opposite.op X) :=
  freeHomEquiv.trans yonedaEquiv
lemma freeYonedaEquiv_symm_app (M : PresheafOfModules.{v} R) (X : C)
    (x : M.obj (Opposite.op X)) :
    (freeYonedaEquiv.symm x).app (Opposite.op X) (ModuleCat.freeMk (𝟙 _)) = x := by
  dsimp [freeYonedaEquiv, freeHomEquiv, yonedaEquiv]
  rw [ModuleCat.freeDesc_apply, op_id, M.presheaf.map_id]
  rfl
lemma freeYonedaEquiv_comp {M N : PresheafOfModules.{v} R} {X : C}
    (m : ((free R).obj (yoneda.obj X) ⟶ M)) (φ : M ⟶ N) :
    freeYonedaEquiv (m ≫ φ) = φ.app _ (freeYonedaEquiv m) := rfl
variable (R) in
def freeYoneda : Set (PresheafOfModules.{v} R) := Set.range (yoneda ⋙ free R).obj
namespace freeYoneda
instance : Small.{u} (freeYoneda R) := by
  let π : C → freeYoneda R := fun X ↦ ⟨_, ⟨X, rfl⟩⟩
  have hπ : Function.Surjective π := by rintro ⟨_, ⟨X, rfl⟩⟩; exact ⟨X, rfl⟩
  exact small_of_surjective hπ
variable (R)
lemma isSeparating : IsSeparating (freeYoneda R) := by
  intro M N f₁ f₂ h
  ext ⟨X⟩ m
  obtain ⟨g, rfl⟩ := freeYonedaEquiv.surjective m
  exact congr_arg freeYonedaEquiv (h _ ⟨X, rfl⟩ g)
lemma isDetecting : IsDetecting (freeYoneda R) :=
  (isSeparating R).isDetecting
end freeYoneda
instance wellPowered {C₀ : Type u} [SmallCategory C₀] (R₀ : C₀ᵒᵖ ⥤ RingCat.{u}) :
    WellPowered (PresheafOfModules.{u} R₀) :=
  wellPowered_of_isDetecting (freeYoneda.isDetecting R₀)
abbrev Elements {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  (M : PresheafOfModules.{v} R) := ((toPresheaf R).obj M ⋙ forget Ab).Elements
abbrev elementsMk {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    (M : PresheafOfModules.{v} R) (X : Cᵒᵖ) (x : M.obj X) : M.Elements :=
  Functor.elementsMk _ X x
namespace Elements
variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{v}} {M : PresheafOfModules.{v} R}
noncomputable abbrev freeYoneda (m : M.Elements) :
    PresheafOfModules.{v} R := (free R).obj (yoneda.obj m.1.unop)
noncomputable abbrev fromFreeYoneda (m : M.Elements) :
    m.freeYoneda ⟶ M :=
  freeYonedaEquiv.symm m.2
lemma fromFreeYoneda_app_apply (m : M.Elements) :
    m.fromFreeYoneda.app m.1 (ModuleCat.freeMk (𝟙 _)) = m.2 := by
  apply freeYonedaEquiv_symm_app
end Elements
section
variable {C : Type u} [SmallCategory.{u} C] {R : Cᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{u} R)
noncomputable abbrev freeYonedaCoproduct : PresheafOfModules.{u} R :=
  ∐ (Elements.freeYoneda (M := M))
noncomputable abbrev ιFreeYonedaCoproduct (m : M.Elements) :
    m.freeYoneda ⟶ M.freeYonedaCoproduct :=
  Sigma.ι _ m
noncomputable def fromFreeYonedaCoproduct :
    M.freeYonedaCoproduct ⟶ M :=
  Sigma.desc Elements.fromFreeYoneda
noncomputable def freeYonedaCoproductMk (m : M.Elements) :
    M.freeYonedaCoproduct.obj m.1 :=
  (M.ιFreeYonedaCoproduct m).app _ (ModuleCat.freeMk (𝟙 _))
@[reassoc (attr := simp)]
lemma ι_fromFreeYonedaCoproduct (m : M.Elements) :
    M.ιFreeYonedaCoproduct m ≫ M.fromFreeYonedaCoproduct = m.fromFreeYoneda := by
  apply Sigma.ι_desc
lemma ι_fromFreeYonedaCoproduct_apply (m : M.Elements) (X : Cᵒᵖ) (x : m.freeYoneda.obj X) :
    M.fromFreeYonedaCoproduct.app X ((M.ιFreeYonedaCoproduct m).app X x) =
      m.fromFreeYoneda.app X x :=
  congr_fun ((evaluation R X ⋙ forget _).congr_map (M.ι_fromFreeYonedaCoproduct m)) x
@[simp]
lemma fromFreeYonedaCoproduct_app_mk (m : M.Elements) :
    M.fromFreeYonedaCoproduct.app _ (M.freeYonedaCoproductMk m) = m.2 := by
  dsimp [freeYonedaCoproductMk]
  erw [M.ι_fromFreeYonedaCoproduct_apply m]
  rw [m.fromFreeYoneda_app_apply]
instance : Epi M.fromFreeYonedaCoproduct :=
  epi_of_surjective (fun X m ↦ ⟨M.freeYonedaCoproductMk (M.elementsMk X m),
    M.fromFreeYonedaCoproduct_app_mk (M.elementsMk X m)⟩)
noncomputable def toFreeYonedaCoproduct :
    (kernel M.fromFreeYonedaCoproduct).freeYonedaCoproduct ⟶ M.freeYonedaCoproduct :=
  (kernel M.fromFreeYonedaCoproduct).fromFreeYonedaCoproduct ≫ kernel.ι _
@[reassoc (attr := simp)]
lemma toFreeYonedaCoproduct_fromFreeYonedaCoproduct :
    M.toFreeYonedaCoproduct ≫ M.fromFreeYonedaCoproduct = 0 := by
  simp [toFreeYonedaCoproduct]
noncomputable abbrev freeYonedaCoproductsCokernelCofork :
    CokernelCofork M.toFreeYonedaCoproduct :=
  CokernelCofork.ofπ _ M.toFreeYonedaCoproduct_fromFreeYonedaCoproduct
noncomputable def isColimitFreeYonedaCoproductsCokernelCofork :
    IsColimit M.freeYonedaCoproductsCokernelCofork := by
  let S := ShortComplex.mk _ _ M.toFreeYonedaCoproduct_fromFreeYonedaCoproduct
  let T := ShortComplex.mk _ _ (kernel.condition M.fromFreeYonedaCoproduct)
  let φ : S ⟶ T :=
    { τ₁ := fromFreeYonedaCoproduct _
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }
  exact ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2
    (T.exact_of_f_is_kernel (kernelIsKernel _))).gIsCokernel
end
end PresheafOfModules