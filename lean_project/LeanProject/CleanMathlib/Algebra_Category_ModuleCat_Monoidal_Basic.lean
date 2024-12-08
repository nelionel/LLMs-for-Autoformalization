import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.CategoryTheory.Monoidal.Linear
suppress_compilation
universe v w x u
open CategoryTheory
namespace ModuleCat
variable {R : Type u} [CommRing R]
namespace MonoidalCategory
open TensorProduct
attribute [local ext] TensorProduct.ext
def tensorObj (M N : ModuleCat R) : ModuleCat R :=
  ModuleCat.of R (M ⊗[R] N)
def tensorHom {M N M' N' : ModuleCat R} (f : M ⟶ N) (g : M' ⟶ N') :
    tensorObj M M' ⟶ tensorObj N N' :=
  TensorProduct.map f g
def whiskerLeft (M : ModuleCat R) {N₁ N₂ : ModuleCat R} (f : N₁ ⟶ N₂) :
    tensorObj M N₁ ⟶ tensorObj M N₂ :=
  f.lTensor M
def whiskerRight {M₁ M₂ : ModuleCat R} (f : M₁ ⟶ M₂) (N : ModuleCat R) :
    tensorObj M₁ N ⟶ tensorObj M₂ N :=
  f.rTensor N
theorem tensor_id (M N : ModuleCat R) : tensorHom (𝟙 M) (𝟙 N) = 𝟙 (ModuleCat.of R (M ⊗ N)) := by
  apply TensorProduct.ext
  rfl
theorem tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : ModuleCat R} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁)
    (g₂ : Y₂ ⟶ Z₂) : tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) = tensorHom f₁ f₂ ≫ tensorHom g₁ g₂ := by
  apply TensorProduct.ext
  rfl
def associator (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) (K : ModuleCat.{x} R) :
    tensorObj (tensorObj M N) K ≅ tensorObj M (tensorObj N K) :=
  (TensorProduct.assoc R M N K).toModuleIso
def leftUnitor (M : ModuleCat.{u} R) : ModuleCat.of R (R ⊗[R] M) ≅ M :=
  (LinearEquiv.toModuleIso (TensorProduct.lid R M) : of R (R ⊗ M) ≅ of R M).trans (ofSelfIso M)
def rightUnitor (M : ModuleCat.{u} R) : ModuleCat.of R (M ⊗[R] R) ≅ M :=
  (LinearEquiv.toModuleIso (TensorProduct.rid R M) : of R (M ⊗ R) ≅ of R M).trans (ofSelfIso M)
@[simps (config := .lemmasOnly)]
instance instMonoidalCategoryStruct : MonoidalCategoryStruct (ModuleCat.{u} R) where
  tensorObj := tensorObj
  whiskerLeft := whiskerLeft
  whiskerRight := whiskerRight
  tensorHom f g := TensorProduct.map f g
  tensorUnit := ModuleCat.of R R
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor
section
open TensorProduct (assoc map)
private theorem associator_naturality_aux {X₁ X₂ X₃ : Type*} [AddCommMonoid X₁] [AddCommMonoid X₂]
    [AddCommMonoid X₃] [Module R X₁] [Module R X₂] [Module R X₃] {Y₁ Y₂ Y₃ : Type*}
    [AddCommMonoid Y₁] [AddCommMonoid Y₂] [AddCommMonoid Y₃] [Module R Y₁] [Module R Y₂]
    [Module R Y₃] (f₁ : X₁ →ₗ[R] Y₁) (f₂ : X₂ →ₗ[R] Y₂) (f₃ : X₃ →ₗ[R] Y₃) :
    ↑(assoc R Y₁ Y₂ Y₃) ∘ₗ map (map f₁ f₂) f₃ = map f₁ (map f₂ f₃) ∘ₗ ↑(assoc R X₁ X₂ X₃) := by
  apply TensorProduct.ext_threefold
  intro x y z
  rfl
variable (R)
private theorem pentagon_aux (W X Y Z : Type*) [AddCommMonoid W] [AddCommMonoid X]
    [AddCommMonoid Y] [AddCommMonoid Z] [Module R W] [Module R X] [Module R Y] [Module R Z] :
    (((assoc R X Y Z).toLinearMap.lTensor W).comp
            (assoc R W (X ⊗[R] Y) Z).toLinearMap).comp
        ((assoc R W X Y).toLinearMap.rTensor Z) =
      (assoc R W X (Y ⊗[R] Z)).toLinearMap.comp (assoc R (W ⊗[R] X) Y Z).toLinearMap := by
  apply TensorProduct.ext_fourfold
  intro w x y z
  rfl
end
theorem associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : ModuleCat R} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (f₃ : X₃ ⟶ Y₃) :
    tensorHom (tensorHom f₁ f₂) f₃ ≫ (associator Y₁ Y₂ Y₃).hom =
      (associator X₁ X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) := by
  convert associator_naturality_aux f₁ f₂ f₃ using 1
theorem pentagon (W X Y Z : ModuleCat R) :
    whiskerRight (associator W X Y).hom Z ≫
        (associator W (tensorObj X Y) Z).hom ≫ whiskerLeft W (associator X Y Z).hom =
      (associator (tensorObj W X) Y Z).hom ≫ (associator W X (tensorObj Y Z)).hom := by
  convert pentagon_aux R W X Y Z using 1
theorem leftUnitor_naturality {M N : ModuleCat R} (f : M ⟶ N) :
    tensorHom (𝟙 (ModuleCat.of R R)) f ≫ (leftUnitor N).hom = (leftUnitor M).hom ≫ f := by
  apply TensorProduct.ext
  apply LinearMap.ext_ring
  apply LinearMap.ext; intro x
  change ((leftUnitor N).hom) ((tensorHom (𝟙 (of R R)) f) ((1 : R) ⊗ₜ[R] x)) =
    f (((leftUnitor M).hom) (1 ⊗ₜ[R] x))
  erw [TensorProduct.lid_tmul, TensorProduct.lid_tmul]
  rw [LinearMap.map_smul]
  rfl
theorem rightUnitor_naturality {M N : ModuleCat R} (f : M ⟶ N) :
    tensorHom f (𝟙 (ModuleCat.of R R)) ≫ (rightUnitor N).hom = (rightUnitor M).hom ≫ f := by
  apply TensorProduct.ext
  apply LinearMap.ext; intro x
  apply LinearMap.ext_ring
  change ((rightUnitor N).hom) ((tensorHom f (𝟙 (of R R))) (x ⊗ₜ[R] (1 : R))) =
    f (((rightUnitor M).hom) (x ⊗ₜ[R] 1))
  erw [TensorProduct.rid_tmul, TensorProduct.rid_tmul]
  rw [LinearMap.map_smul]
  rfl
theorem triangle (M N : ModuleCat.{u} R) :
    (associator M (ModuleCat.of R R) N).hom ≫ tensorHom (𝟙 M) (leftUnitor N).hom =
      tensorHom (rightUnitor M).hom (𝟙 N) := by
  apply TensorProduct.ext_threefold
  intro x y z
  change R at y
  change x ⊗ₜ[R] ((leftUnitor N).hom) (y ⊗ₜ[R] z) = ((rightUnitor M).hom) (x ⊗ₜ[R] y) ⊗ₜ[R] z
  erw [TensorProduct.lid_tmul, TensorProduct.rid_tmul]
  exact (TensorProduct.smul_tmul _ _ _).symm
end MonoidalCategory
open MonoidalCategory
instance monoidalCategory : MonoidalCategory (ModuleCat.{u} R) := MonoidalCategory.ofTensorHom
  (tensor_id := fun M N ↦ tensor_id M N)
  (tensor_comp := fun f g h ↦ MonoidalCategory.tensor_comp f g h)
  (associator_naturality := fun f g h ↦ MonoidalCategory.associator_naturality f g h)
  (leftUnitor_naturality := fun f ↦ MonoidalCategory.leftUnitor_naturality f)
  (rightUnitor_naturality := fun f ↦ rightUnitor_naturality f)
  (pentagon := fun M N K L ↦ pentagon M N K L)
  (triangle := fun M N ↦ triangle M N)
instance : CommRing ((𝟙_ (ModuleCat.{u} R) : ModuleCat.{u} R) : Type u) :=
  inferInstanceAs <| CommRing R
namespace MonoidalCategory
@[simp]
theorem tensorHom_tmul {K L M N : ModuleCat.{u} R} (f : K ⟶ L) (g : M ⟶ N) (k : K) (m : M) :
    (f ⊗ g) (k ⊗ₜ m) = f k ⊗ₜ g m :=
  rfl
@[deprecated (since := "2024-09-30")] alias hom_apply := tensorHom_tmul
@[simp]
theorem whiskerLeft_apply (L : ModuleCat.{u} R) {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (l : L) (m : M) :
    (L ◁ f) (l ⊗ₜ m) = l ⊗ₜ f m :=
  rfl
@[simp]
theorem whiskerRight_apply {L M : ModuleCat.{u} R} (f : L ⟶ M) (N : ModuleCat.{u} R)
    (l : L) (n : N) :
    (f ▷ N) (l ⊗ₜ n) = f l ⊗ₜ n :=
  rfl
@[simp]
theorem leftUnitor_hom_apply {M : ModuleCat.{u} R} (r : R) (m : M) :
    ((λ_ M).hom : 𝟙_ (ModuleCat R) ⊗ M ⟶ M) (r ⊗ₜ[R] m) = r • m :=
  TensorProduct.lid_tmul m r
@[simp]
theorem leftUnitor_inv_apply {M : ModuleCat.{u} R} (m : M) :
    ((λ_ M).inv : M ⟶ 𝟙_ (ModuleCat.{u} R) ⊗ M) m = 1 ⊗ₜ[R] m :=
  TensorProduct.lid_symm_apply m
@[simp]
theorem rightUnitor_hom_apply {M : ModuleCat.{u} R} (m : M) (r : R) :
    ((ρ_ M).hom : M ⊗ 𝟙_ (ModuleCat R) ⟶ M) (m ⊗ₜ r) = r • m :=
  TensorProduct.rid_tmul m r
@[simp]
theorem rightUnitor_inv_apply {M : ModuleCat.{u} R} (m : M) :
    ((ρ_ M).inv : M ⟶ M ⊗ 𝟙_ (ModuleCat.{u} R)) m = m ⊗ₜ[R] 1 :=
  TensorProduct.rid_symm_apply m
@[simp]
theorem associator_hom_apply {M N K : ModuleCat.{u} R} (m : M) (n : N) (k : K) :
    ((α_ M N K).hom : (M ⊗ N) ⊗ K ⟶ M ⊗ N ⊗ K) (m ⊗ₜ n ⊗ₜ k) = m ⊗ₜ (n ⊗ₜ k) :=
  rfl
@[simp]
theorem associator_inv_apply {M N K : ModuleCat.{u} R} (m : M) (n : N) (k : K) :
    ((α_ M N K).inv : M ⊗ N ⊗ K ⟶ (M ⊗ N) ⊗ K) (m ⊗ₜ (n ⊗ₜ k)) = m ⊗ₜ n ⊗ₜ k :=
  rfl
variable {M₁ M₂ M₃ M₄ : ModuleCat.{u} R}
section
variable (f : M₁ → M₂ → M₃) (h₁ : ∀ m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
  (h₂ : ∀ (a : R) m n, f (a • m) n = a • f m n)
  (h₃ : ∀ m n₁ n₂, f m (n₁ + n₂) = f m n₁ + f m n₂)
  (h₄ : ∀ (a : R) m n, f m (a • n) = a • f m n)
noncomputable def tensorLift : M₁ ⊗ M₂ ⟶ M₃ :=
  TensorProduct.lift (LinearMap.mk₂ R f h₁ h₂ h₃ h₄)
@[simp]
lemma tensorLift_tmul (m : M₁) (n : M₂) :
    tensorLift f h₁ h₂ h₃ h₄ (m ⊗ₜ n) = f m n := rfl
end
lemma tensor_ext {f g : M₁ ⊗ M₂ ⟶ M₃} (h : ∀ m n, f (m ⊗ₜ n) = g (m ⊗ₜ n)) :
    f = g :=
  TensorProduct.ext (by ext; apply h)
lemma tensor_ext₃' {f g : (M₁ ⊗ M₂) ⊗ M₃ ⟶ M₄}
    (h : ∀ m₁ m₂ m₃, f (m₁ ⊗ₜ m₂ ⊗ₜ m₃) = g (m₁ ⊗ₜ m₂ ⊗ₜ m₃)) :
    f = g :=
  TensorProduct.ext_threefold h
lemma tensor_ext₃ {f g : M₁ ⊗ (M₂ ⊗ M₃) ⟶ M₄}
    (h : ∀ m₁ m₂ m₃, f (m₁ ⊗ₜ (m₂ ⊗ₜ m₃)) = g (m₁ ⊗ₜ (m₂ ⊗ₜ m₃))) :
    f = g := by
  rw [← cancel_epi (α_ _ _ _).hom]
  exact tensor_ext₃' h
end MonoidalCategory
open Opposite
instance : MonoidalPreadditive (ModuleCat.{u} R) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intros
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply]
    rw [LinearMap.zero_apply]
    erw [MonoidalCategory.whiskerLeft_apply]
    rw [LinearMap.zero_apply, TensorProduct.tmul_zero]
  · intros
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply]
    rw [LinearMap.zero_apply]
    erw [MonoidalCategory.whiskerRight_apply]
    rw [LinearMap.zero_apply, TensorProduct.zero_tmul]
  · intros
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply]
    rw [LinearMap.add_apply]
    erw [MonoidalCategory.whiskerLeft_apply, MonoidalCategory.whiskerLeft_apply]
    erw [MonoidalCategory.whiskerLeft_apply]
    rw [LinearMap.add_apply, TensorProduct.tmul_add]
  · intros
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply]
    rw [LinearMap.add_apply]
    erw [MonoidalCategory.whiskerRight_apply, MonoidalCategory.whiskerRight_apply]
    erw [MonoidalCategory.whiskerRight_apply]
    rw [LinearMap.add_apply, TensorProduct.add_tmul]
instance : MonoidalLinear R (ModuleCat.{u} R) := by
  refine ⟨?_, ?_⟩
  · intros
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply]
    rw [LinearMap.smul_apply]
    erw [MonoidalCategory.whiskerLeft_apply, MonoidalCategory.whiskerLeft_apply]
    rw [LinearMap.smul_apply, TensorProduct.tmul_smul]
  · intros
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply]
    rw [LinearMap.smul_apply]
    erw [MonoidalCategory.whiskerRight_apply, MonoidalCategory.whiskerRight_apply]
    rw [LinearMap.smul_apply, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
end ModuleCat