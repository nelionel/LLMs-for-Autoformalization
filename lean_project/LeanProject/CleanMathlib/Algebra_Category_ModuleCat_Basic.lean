import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.PUnitInstances.Module
import Mathlib.CategoryTheory.Conj
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Limits.WalkingParallelPair
universe v u
variable (R : Type u) [Ring R]
structure ModuleCat where
  carrier : Type v
  [isAddCommGroup : AddCommGroup carrier]
  [isModule : Module R carrier]
attribute [instance] ModuleCat.isAddCommGroup ModuleCat.isModule
@[nolint checkUnivs]
abbrev ModuleCatMax.{v₁, v₂, u₁} (R : Type u₁) [Ring R] := ModuleCat.{max v₁ v₂, u₁} R
namespace ModuleCat
instance : CoeSort (ModuleCat.{v} R) (Type v) :=
  ⟨ModuleCat.carrier⟩
attribute [coe] ModuleCat.carrier
instance moduleCategory : Category.{v, max (v+1) u} (ModuleCat.{v} R) where
  Hom M N := M →ₗ[R] N
  id _ := LinearMap.id
  comp f g := g.comp f
  id_comp _ := LinearMap.id_comp _
  comp_id _ := LinearMap.comp_id _
  assoc f g h := LinearMap.comp_assoc (f := f) (g := g) (h := h)
instance {M N : ModuleCat.{v} R} : FunLike (M ⟶ N) M N :=
  LinearMap.instFunLike
instance {M N : ModuleCat.{v} R} : LinearMapClass (M ⟶ N) R M N :=
  LinearMap.semilinearMapClass
instance moduleConcreteCategory : ConcreteCategory.{v} (ModuleCat.{v} R) where
  forget :=
    { obj := fun R => R
      map := fun f => f.toFun }
  forget_faithful := ⟨fun h => LinearMap.ext (fun x => by
    dsimp at h
    rw [h])⟩
instance {M : ModuleCat.{v} R} : AddCommGroup ((forget (ModuleCat R)).obj M) :=
  (inferInstance : AddCommGroup M)
instance {M : ModuleCat.{v} R} : Module R ((forget (ModuleCat R)).obj M) :=
  (inferInstance : Module R M)
@[ext]
lemma ext {M N : ModuleCat.{v} R} {f₁ f₂ : M ⟶ N} (h : ∀ (x : M), f₁ x = f₂ x) : f₁ = f₂ :=
  DFunLike.ext _ _ h
instance hasForgetToAddCommGroup : HasForget₂ (ModuleCat R) AddCommGrp where
  forget₂ :=
    { obj := fun M => AddCommGrp.of M
      map := fun f => AddCommGrp.ofHom f.toAddMonoidHom }
def of (X : Type v) [AddCommGroup X] [Module R X] : ModuleCat R :=
  ⟨X⟩
@[simp]
theorem forget₂_obj (X : ModuleCat R) :
    (forget₂ (ModuleCat R) AddCommGrp).obj X = AddCommGrp.of X :=
  rfl
theorem forget₂_obj_moduleCat_of (X : Type v) [AddCommGroup X] [Module R X] :
    (forget₂ (ModuleCat R) AddCommGrp).obj (of R X) = AddCommGrp.of X :=
  rfl
@[simp]
theorem forget₂_map (X Y : ModuleCat R) (f : X ⟶ Y) :
    (forget₂ (ModuleCat R) AddCommGrp).map f = LinearMap.toAddMonoidHom f :=
  rfl
instance : Inhabited (ModuleCat R) :=
  ⟨of R PUnit⟩
instance ofUnique {X : Type v} [AddCommGroup X] [Module R X] [i : Unique X] : Unique (of R X) :=
  i
@[simp] theorem of_coe (X : ModuleCat R) : of R X = X := rfl
theorem coe_of (X : Type v) [AddCommGroup X] [Module R X] : (of R X : Type v) = X :=
  rfl
variable {R}
@[simps]
def ofSelfIso (M : ModuleCat R) : ModuleCat.of R M ≅ M where
  hom := 𝟙 M
  inv := 𝟙 M
theorem isZero_of_subsingleton (M : ModuleCat R) [Subsingleton M] : IsZero M where
  unique_to X := ⟨⟨⟨(0 : M →ₗ[R] X)⟩, fun f => by
    ext x
    rw [Subsingleton.elim x (0 : M)]
    dsimp
    simp⟩⟩
  unique_from X := ⟨⟨⟨(0 : X →ₗ[R] M)⟩, fun f => by
    ext x
    subsingleton⟩⟩
instance : HasZeroObject (ModuleCat.{v} R) :=
  ⟨⟨of R PUnit, isZero_of_subsingleton _⟩⟩
variable {M N U : ModuleCat.{v} R}
@[simp]
theorem id_apply (m : M) : (𝟙 M : M → M) m = m :=
  rfl
@[simp]
theorem coe_comp (f : M ⟶ N) (g : N ⟶ U) : (f ≫ g : M → U) = g ∘ f :=
  rfl
theorem comp_def (f : M ⟶ N) (g : N ⟶ U) : f ≫ g = g.comp f :=
  rfl
@[simp] lemma forget_map (f : M ⟶ N) : (forget (ModuleCat R)).map f = (f : M → N) := rfl
end ModuleCat
variable {R}
variable {X₁ X₂ : Type v}
open ModuleCat
def ModuleCat.ofHom [AddCommGroup X₁] [Module R X₁] [AddCommGroup X₂] [Module R X₂] :
    (X₁ →ₗ[R] X₂) → (ModuleCat.of R X₁ ⟶ ModuleCat.of R X₂) :=
  id
@[deprecated (since := "2024-12-03")] alias ModuleCat.asHom := ModuleCat.ofHom
scoped[ModuleCat] notation "↟" f:1024 => ModuleCat.ofHom f
@[simp 1100]
theorem ModuleCat.ofHom_apply {R : Type u} [Ring R] {X Y : Type v} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (f : X →ₗ[R] Y) (x : X) : (↟ f) x = f x :=
  rfl
@[deprecated (since := "2024-10-06")] alias ModuleCat.asHom_apply := ModuleCat.ofHom_apply
def ModuleCat.asHomRight [AddCommGroup X₁] [Module R X₁] {X₂ : ModuleCat.{v} R} :
    (X₁ →ₗ[R] X₂) → (ModuleCat.of R X₁ ⟶ X₂) :=
  id
scoped[ModuleCat] notation "↾" f:1024 => ModuleCat.asHomRight f
def ModuleCat.asHomLeft {X₁ : ModuleCat.{v} R} [AddCommGroup X₂] [Module R X₂] :
    (X₁ →ₗ[R] X₂) → (X₁ ⟶ ModuleCat.of R X₂) :=
  id
scoped[ModuleCat] notation "↿" f:1024 => ModuleCat.asHomLeft f
section
@[simps]
def LinearEquiv.toModuleIso {g₁ : AddCommGroup X₁} {g₂ : AddCommGroup X₂} {m₁ : Module R X₁}
    {m₂ : Module R X₂} (e : X₁ ≃ₗ[R] X₂) : ModuleCat.of R X₁ ≅ ModuleCat.of R X₂ where
  hom := (e : X₁ →ₗ[R] X₂)
  inv := (e.symm : X₂ →ₗ[R] X₁)
  hom_inv_id := by ext; apply e.left_inv
  inv_hom_id := by ext; apply e.right_inv
abbrev LinearEquiv.toModuleIso' {M N : ModuleCat.{v} R} (i : M ≃ₗ[R] N) : M ≅ N :=
  i.toModuleIso
abbrev LinearEquiv.toModuleIso'Left {X₁ : ModuleCat.{v} R} [AddCommGroup X₂] [Module R X₂]
    (e : X₁ ≃ₗ[R] X₂) : X₁ ≅ ModuleCat.of R X₂ :=
  e.toModuleIso
abbrev LinearEquiv.toModuleIso'Right [AddCommGroup X₁] [Module R X₁] {X₂ : ModuleCat.{v} R}
    (e : X₁ ≃ₗ[R] X₂) : ModuleCat.of R X₁ ≅ X₂ :=
  e.toModuleIso
namespace CategoryTheory.Iso
def toLinearEquiv {X Y : ModuleCat R} (i : X ≅ Y) : X ≃ₗ[R] Y :=
  LinearEquiv.ofLinear i.hom i.inv i.inv_hom_id i.hom_inv_id
end CategoryTheory.Iso
@[simps]
def linearEquivIsoModuleIso {X Y : Type u} [AddCommGroup X] [AddCommGroup Y] [Module R X]
    [Module R Y] : (X ≃ₗ[R] Y) ≅ ModuleCat.of R X ≅ ModuleCat.of R Y where
  hom e := e.toModuleIso
  inv i := i.toLinearEquiv
end
namespace ModuleCat
instance {M N : ModuleCat.{v} R} : AddCommGroup (M ⟶ N) := LinearMap.addCommGroup
instance : Preadditive (ModuleCat.{v} R) where
  add_comp P Q R f f' g := by
    ext
    dsimp
    erw [map_add]
    rfl
instance forget₂_addCommGrp_additive :
    (forget₂ (ModuleCat.{v} R) AddCommGrp).Additive where
section
variable {S : Type u} [CommRing S]
instance : Linear S (ModuleCat.{v} S) where
  homModule _ _ := LinearMap.module
  smul_comp := by
    intros
    ext
    dsimp
    rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul]
    rfl
variable {X Y X' Y' : ModuleCat.{v} S}
theorem Iso.homCongr_eq_arrowCongr (i : X ≅ X') (j : Y ≅ Y') (f : X ⟶ Y) :
    Iso.homCongr i j f = LinearEquiv.arrowCongr i.toLinearEquiv j.toLinearEquiv f :=
  rfl
theorem Iso.conj_eq_conj (i : X ≅ X') (f : End X) :
    Iso.conj i f = LinearEquiv.conj i.toLinearEquiv f :=
  rfl
end
variable (M N : ModuleCat.{v} R)
def smul : R →+* End ((forget₂ (ModuleCat R) AddCommGrp).obj M) where
  toFun r :=
    { toFun := fun (m : M) => r • m
      map_zero' := by dsimp; rw [smul_zero]
      map_add' := fun x y => by dsimp; rw [smul_add] }
  map_one' := AddMonoidHom.ext (fun x => by dsimp; rw [one_smul])
  map_zero' := AddMonoidHom.ext (fun x => by dsimp; rw [zero_smul]; rfl)
  map_mul' r s := AddMonoidHom.ext (fun (x : M) => (smul_smul r s x).symm)
  map_add' r s := AddMonoidHom.ext (fun (x : M) => add_smul r s x)
lemma smul_naturality {M N : ModuleCat.{v} R} (f : M ⟶ N) (r : R) :
    (forget₂ (ModuleCat R) AddCommGrp).map f ≫ N.smul r =
      M.smul r ≫ (forget₂ (ModuleCat R) AddCommGrp).map f := by
  ext x
  exact (f.map_smul r x).symm
variable (R)
@[simps]
def smulNatTrans : R →+* End (forget₂ (ModuleCat R) AddCommGrp) where
  toFun r :=
    { app := fun M => M.smul r
      naturality := fun _ _ _ => smul_naturality _ r }
  map_one' := NatTrans.ext (by aesop_cat)
  map_zero' := NatTrans.ext (by aesop_cat)
  map_mul' _ _ := NatTrans.ext (by aesop_cat)
  map_add' _ _ := NatTrans.ext (by aesop_cat)
variable {R}
@[nolint unusedArguments]
def mkOfSMul' {A : AddCommGrp} (_ : R →+* End A) := A
section
variable {A : AddCommGrp} (φ : R →+* End A)
instance : AddCommGroup (mkOfSMul' φ) := by
  dsimp only [mkOfSMul']
  infer_instance
instance : SMul R (mkOfSMul' φ) := ⟨fun r (x : A) => (show A ⟶ A from φ r) x⟩
@[simp]
lemma mkOfSMul'_smul (r : R) (x : mkOfSMul' φ) :
    r • x = (show A ⟶ A from φ r) x := rfl
instance : Module R (mkOfSMul' φ) where
  smul_zero _ := map_zero (N := A) _
  smul_add _ _ _ := map_add (N := A) _ _ _
  one_smul := by simp
  mul_smul := by simp
  add_smul _ _ _ := by simp; rfl
  zero_smul := by simp
abbrev mkOfSMul := ModuleCat.of R (mkOfSMul' φ)
@[simp, nolint simpNF]
lemma mkOfSMul_smul (r : R) : (mkOfSMul φ).smul r = φ r := rfl
end
section
variable {M N}
  (φ : (forget₂ (ModuleCat R) AddCommGrp).obj M ⟶
      (forget₂ (ModuleCat R) AddCommGrp).obj N)
  (hφ : ∀ (r : R), φ ≫ N.smul r = M.smul r ≫ φ)
@[simps]
def homMk : M ⟶ N where
  toFun := φ
  map_add' _ _ := φ.map_add _ _
  map_smul' r x := (congr_hom (hφ r) x).symm
lemma forget₂_map_homMk :
    (forget₂ (ModuleCat R) AddCommGrp).map (homMk φ hφ) = φ := rfl
end
instance : (forget (ModuleCat.{v} R)).ReflectsIsomorphisms where
  reflects f _ :=
    (inferInstance : IsIso ((LinearEquiv.mk f
      (asIso ((forget (ModuleCat R)).map f)).toEquiv.invFun
      (Equiv.left_inv _) (Equiv.right_inv _)).toModuleIso).hom)
instance : (forget₂ (ModuleCat.{v} R) AddCommGrp.{v}).ReflectsIsomorphisms where
  reflects f _ := by
    have : IsIso ((forget _).map f) := by
      change IsIso ((forget _).map ((forget₂ _ AddCommGrp).map f))
      infer_instance
    apply isIso_of_reflects_iso _ (forget _)
end ModuleCat
@[simp] theorem LinearMap.comp_id_moduleCat
    {R} [Ring R] {G : ModuleCat.{u} R} {H : Type u} [AddCommGroup H] [Module R H] (f : G →ₗ[R] H) :
    f.comp (𝟙 G) = f :=
  Category.id_comp (ModuleCat.ofHom f)
@[simp] theorem LinearMap.id_moduleCat_comp
    {R} [Ring R] {G : Type u} [AddCommGroup G] [Module R G] {H : ModuleCat.{u} R} (f : G →ₗ[R] H) :
    LinearMap.comp (𝟙 H) f = f :=
  Category.comp_id (ModuleCat.ofHom f)