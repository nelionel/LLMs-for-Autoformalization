import Mathlib.LinearAlgebra.RootSystem.Defs
open Set Function
noncomputable section
variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
namespace RootPairing
@[ext]
structure Hom {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) where
  weightMap : M →ₗ[R] M₂
  coweightMap : N₂ →ₗ[R] N
  indexEquiv : ι ≃ ι₂
  weight_coweight_transpose : weightMap.dualMap ∘ₗ Q.toDualRight = P.toDualRight ∘ₗ coweightMap
  root_weightMap : weightMap ∘ P.root = Q.root ∘ indexEquiv
  coroot_coweightMap : coweightMap ∘ Q.coroot = P.coroot ∘ indexEquiv.symm
namespace Hom
lemma weight_coweight_transpose_apply {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) (x : N₂) (f : Hom P Q) :
    f.weightMap.dualMap (Q.toDualRight x) = P.toDualRight (f.coweightMap x) :=
  Eq.mp (propext LinearMap.ext_iff) f.weight_coweight_transpose x
lemma root_weightMap_apply {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) (i : ι) (f : Hom P Q) :
    f.weightMap (P.root i) = Q.root (f.indexEquiv i) :=
  Eq.mp (propext funext_iff) f.root_weightMap i
lemma coroot_coweightMap_apply {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) (i : ι₂) (f : Hom P Q) :
    f.coweightMap (Q.coroot i) = P.coroot (f.indexEquiv.symm i) :=
  Eq.mp (propext funext_iff) f.coroot_coweightMap i
@[simps!]
def id (P : RootPairing ι R M N) : Hom P P where
  weightMap := LinearMap.id
  coweightMap := LinearMap.id
  indexEquiv := Equiv.refl ι
  weight_coweight_transpose := by simp
  root_weightMap := by simp
  coroot_coweightMap := by simp
@[simps!]
def comp {ι₁ M₁ N₁ ι₂ M₂ N₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup N₁]
    [Module R N₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    {P : RootPairing ι R M N} {P₁ : RootPairing ι₁ R M₁ N₁} {P₂ : RootPairing ι₂ R M₂ N₂}
    (g : Hom P₁ P₂) (f : Hom P P₁) : Hom P P₂ where
  weightMap := g.weightMap ∘ₗ f.weightMap
  coweightMap := f.coweightMap ∘ₗ g.coweightMap
  indexEquiv := f.indexEquiv.trans g.indexEquiv
  weight_coweight_transpose := by
    ext φ x
    rw [← LinearMap.dualMap_comp_dualMap, ← LinearMap.comp_assoc _ f.coweightMap,
      ← f.weight_coweight_transpose, LinearMap.comp_assoc g.coweightMap,
      ← g.weight_coweight_transpose, ← LinearMap.comp_assoc]
  root_weightMap := by
    ext i
    simp only [LinearMap.coe_comp, Equiv.coe_trans]
    rw [comp_assoc, f.root_weightMap, ← comp_assoc, g.root_weightMap, comp_assoc]
  coroot_coweightMap := by
    ext i
    simp only [LinearMap.coe_comp, Equiv.symm_trans_apply]
    rw [comp_assoc, g.coroot_coweightMap, ← comp_assoc, f.coroot_coweightMap, comp_assoc]
    simp
@[simp]
lemma id_comp {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) (f : Hom P Q) :
    comp f (id P) = f := by
  ext x <;> simp
@[simp]
lemma comp_id {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) (f : Hom P Q) :
    comp (id Q) f = f := by
  ext x <;> simp
@[simp]
lemma comp_assoc {ι₁ M₁ N₁ ι₂ M₂ N₂ ι₃ M₃ N₃ : Type*} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    [AddCommGroup M₃] [Module R M₃] [AddCommGroup N₃] [Module R N₃] {P : RootPairing ι R M N}
    {P₁ : RootPairing ι₁ R M₁ N₁} {P₂ : RootPairing ι₂ R M₂ N₂} {P₃ : RootPairing ι₃ R M₃ N₃}
    (h : Hom P₂ P₃) (g : Hom P₁ P₂) (f : Hom P P₁) :
    comp (comp h g) f = comp h (comp g f) := by
  ext <;> simp
instance (P : RootPairing ι R M N) : Monoid (Hom P P) where
  mul := comp
  mul_assoc := comp_assoc
  one := id P
  one_mul := id_comp P P
  mul_one := comp_id P P
@[simp]
lemma weightMap_one (P : RootPairing ι R M N) :
    weightMap (P := P) (Q := P) 1 = LinearMap.id (R := R) (M := M) :=
  rfl
@[simp]
lemma coweightMap_one (P : RootPairing ι R M N) :
    coweightMap (P := P) (Q := P) 1 = LinearMap.id (R := R) (M := N) :=
  rfl
@[simp]
lemma indexEquiv_one (P : RootPairing ι R M N) :
    indexEquiv (P := P) (Q := P) 1 = Equiv.refl ι :=
  rfl
@[simp]
lemma weightMap_mul (P : RootPairing ι R M N) (x y : Hom P P) :
    weightMap (x * y) = weightMap x ∘ₗ weightMap y :=
  rfl
@[simp]
lemma coweightMap_mul (P : RootPairing ι R M N) (x y : Hom P P) :
    coweightMap (x * y) = coweightMap y ∘ₗ coweightMap x :=
  rfl
@[simp]
lemma indexEquiv_mul (P : RootPairing ι R M N) (x y : Hom P P) :
    indexEquiv (x * y) = indexEquiv x ∘ indexEquiv y :=
  rfl
abbrev _root_.RootPairing.End (P : RootPairing ι R M N) := Hom P P
def weightHom (P : RootPairing ι R M N) : End P →* (Module.End R M) where
  toFun g := Hom.weightMap (P := P) (Q := P) g
  map_mul' g h := by ext; simp
  map_one' := by ext; simp
lemma weightHom_injective (P : RootPairing ι R M N) : Injective (weightHom P) := by
  intro f g hfg
  ext x
  · exact LinearMap.congr_fun hfg x
  · refine (LinearEquiv.injective P.toDualRight) ?_
    simp_rw [← weight_coweight_transpose_apply]
    exact congrFun (congrArg DFunLike.coe (congrArg LinearMap.dualMap hfg)) (P.toDualRight x)
  · refine (Embedding.injective P.root) ?_
    simp_rw [← root_weightMap_apply]
    exact congrFun (congrArg DFunLike.coe hfg) (P.root x)
def coweightHom (P : RootPairing ι R M N) : End P →* (N →ₗ[R] N)ᵐᵒᵖ where
  toFun g := MulOpposite.op (Hom.coweightMap (P := P) (Q := P) g)
  map_mul' g h := by
    simp only [← MulOpposite.op_mul, coweightMap_mul, LinearMap.mul_eq_comp]
  map_one' := by
    simp only [MulOpposite.op_eq_one_iff, coweightMap_one, LinearMap.one_eq_id]
lemma coweightHom_injective (P : RootPairing ι R M N) : Injective (coweightHom P) := by
  intro f g hfg
  ext x
  · dsimp [coweightHom] at hfg
    rw [MulOpposite.op_inj] at hfg
    have h := congrArg (LinearMap.comp (M₃ := Module.Dual R M)
        (σ₂₃ := RingHom.id R) (P.toDualRight)) hfg
    rw [← f.weight_coweight_transpose, ← g.weight_coweight_transpose] at h
    have : f.weightMap = g.weightMap := by
      haveI : Module.IsReflexive R M := PerfectPairing.reflexive_left P.toPerfectPairing
      refine (Module.dualMap_dualMap_eq_iff R M).mp (congrArg LinearMap.dualMap
        ((LinearEquiv.eq_comp_toLinearMap_iff f.weightMap.dualMap g.weightMap.dualMap).mp h))
    exact congrFun (congrArg DFunLike.coe this) x
  · dsimp [coweightHom] at hfg
    simp_all only [MulOpposite.op_inj]
  · dsimp [coweightHom] at hfg
    rw [MulOpposite.op_inj] at hfg
    set y := f.indexEquiv x with hy
    have : f.coweightMap (P.coroot y) = g.coweightMap (P.coroot y) := by
      exact congrFun (congrArg DFunLike.coe hfg) (P.coroot y)
    rw [coroot_coweightMap_apply, coroot_coweightMap_apply, Embedding.apply_eq_iff_eq, hy] at this
    rw [Equiv.symm_apply_apply] at this
    rw [this, Equiv.apply_symm_apply]
end Hom
variable {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂)
@[ext]
protected structure Equiv extends Hom P Q where
  bijective_weightMap : Bijective weightMap
  bijective_coweightMap : Bijective coweightMap
attribute [coe] Equiv.toHom
add_decl_doc Equiv.toHom
namespace Equiv
def weightEquiv (e : RootPairing.Equiv P Q) : M ≃ₗ[R] M₂ :=
    LinearEquiv.ofBijective _ e.bijective_weightMap
@[simp]
lemma weightEquiv_apply (e : RootPairing.Equiv P Q) (m : M) :
    weightEquiv P Q e m = e.toHom.weightMap m :=
  rfl
@[simp]
lemma weightEquiv_symm_weightMap (e : RootPairing.Equiv P Q) (m : M) :
    (weightEquiv P Q e).symm (e.toHom.weightMap m) = m :=
  (LinearEquiv.symm_apply_eq (weightEquiv P Q e)).mpr rfl
@[simp]
lemma weightMap_weightEquiv_symm (e : RootPairing.Equiv P Q) (m : M₂) :
    e.toHom.weightMap ((weightEquiv P Q e).symm m) = m := by
  rw [← weightEquiv_apply]
  exact LinearEquiv.apply_symm_apply (weightEquiv P Q e) m
def coweightEquiv (e : RootPairing.Equiv P Q) : N₂ ≃ₗ[R] N :=
  LinearEquiv.ofBijective _ e.bijective_coweightMap
@[simp]
lemma coweightEquiv_apply (e : RootPairing.Equiv P Q) (n : N₂) :
    coweightEquiv P Q e n = e.toHom.coweightMap n :=
  rfl
@[simp]
lemma coweightEquiv_symm_coweightMap (e : RootPairing.Equiv P Q) (n : N₂) :
    (coweightEquiv P Q e).symm (e.toHom.coweightMap n) = n :=
  (LinearEquiv.symm_apply_eq (coweightEquiv P Q e)).mpr rfl
@[simp]
lemma coweightMap_coweightEquiv_symm (e : RootPairing.Equiv P Q) (n : N) :
    e.toHom.coweightMap ((coweightEquiv P Q e).symm n) = n := by
  rw [← coweightEquiv_apply]
  exact LinearEquiv.apply_symm_apply (coweightEquiv P Q e) n
@[simps!]
def id (P : RootPairing ι R M N) : RootPairing.Equiv P P :=
  { Hom.id P with
    bijective_weightMap := _root_.id bijective_id
    bijective_coweightMap := _root_.id bijective_id }
@[simps!]
def comp {ι₁ M₁ N₁ ι₂ M₂ N₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup N₁]
    [Module R N₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    {P : RootPairing ι R M N} {P₁ : RootPairing ι₁ R M₁ N₁} {P₂ : RootPairing ι₂ R M₂ N₂}
    (g : RootPairing.Equiv P₁ P₂) (f : RootPairing.Equiv P P₁) : RootPairing.Equiv P P₂ :=
  { Hom.comp g.toHom f.toHom with
    bijective_weightMap := by
      simp only [Hom.comp, LinearMap.coe_comp]
      exact Bijective.comp g.bijective_weightMap f.bijective_weightMap
    bijective_coweightMap := by
      simp only [Hom.comp, LinearMap.coe_comp]
      exact Bijective.comp f.bijective_coweightMap g.bijective_coweightMap }
@[simp]
lemma toHom_comp {ι₁ M₁ N₁ ι₂ M₂ N₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup N₁]
    [Module R N₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    {P : RootPairing ι R M N} {P₁ : RootPairing ι₁ R M₁ N₁} {P₂ : RootPairing ι₂ R M₂ N₂}
    (g : RootPairing.Equiv P₁ P₂) (f : RootPairing.Equiv P P₁) :
    (Equiv.comp g f).toHom = Hom.comp g.toHom f.toHom := by
  rfl
@[simp]
lemma id_comp {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) (f : RootPairing.Equiv P Q) :
    comp f (id P) = f := by
  ext x <;> simp
@[simp]
lemma comp_id {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) (f : RootPairing.Equiv P Q) :
    comp (id Q) f = f := by
  ext x <;> simp
@[simp]
lemma comp_assoc {ι₁ M₁ N₁ ι₂ M₂ N₂ ι₃ M₃ N₃ : Type*} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    [AddCommGroup M₃] [Module R M₃] [AddCommGroup N₃] [Module R N₃] {P : RootPairing ι R M N}
    {P₁ : RootPairing ι₁ R M₁ N₁} {P₂ : RootPairing ι₂ R M₂ N₂} {P₃ : RootPairing ι₃ R M₃ N₃}
    (h : RootPairing.Equiv P₂ P₃) (g : RootPairing.Equiv P₁ P₂) (f : RootPairing.Equiv P P₁) :
    comp (comp h g) f = comp h (comp g f) := by
  ext <;> simp
instance (P : RootPairing ι R M N) : Monoid (RootPairing.Equiv P P) where
  mul := comp
  mul_assoc := comp_assoc
  one := id P
  one_mul := id_comp P P
  mul_one := comp_id P P
@[simp]
lemma weightEquiv_one (P : RootPairing ι R M N) :
    weightEquiv (P := P) (Q := P) 1 = LinearMap.id (R := R) (M := M) :=
  rfl
@[simp]
lemma coweightEquiv_one (P : RootPairing ι R M N) :
    coweightEquiv (P := P) (Q := P) 1 = LinearMap.id (R := R) (M := N) :=
  rfl
@[simp]
lemma toHom_one (P : RootPairing ι R M N) :
    (1 : RootPairing.Equiv P P).toHom = (1 : RootPairing.Hom P P) :=
  rfl
@[simp]
lemma mul_eq_comp {P : RootPairing ι R M N} (x y : RootPairing.Equiv P P) :
    x * y = Equiv.comp x y :=
  rfl
@[simp]
lemma weightEquiv_comp_toLin {P : RootPairing ι R M N} (x y : RootPairing.Equiv P P) :
    weightEquiv P P (Equiv.comp x y) = weightEquiv P P y ≪≫ₗ weightEquiv P P x := by
  ext; simp
@[simp]
lemma weightEquiv_mul {P : RootPairing ι R M N} (x y : RootPairing.Equiv P P) :
    weightEquiv P P x * weightEquiv P P y = weightEquiv P P y ≪≫ₗ weightEquiv P P x := by
  rfl
@[simp]
lemma coweightEquiv_comp_toLin {P : RootPairing ι R M N} (x y : RootPairing.Equiv P P) :
    coweightEquiv P P (Equiv.comp x y) = coweightEquiv P P x ≪≫ₗ coweightEquiv P P y := by
  ext; simp
@[simp]
lemma coweightEquiv_mul {P : RootPairing ι R M N} (x y : RootPairing.Equiv P P) :
    coweightEquiv P P x * coweightEquiv P P y = coweightEquiv P P y ≪≫ₗ coweightEquiv P P x := by
  rfl
def symm {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) (f : RootPairing.Equiv P Q) :
    RootPairing.Equiv Q P where
  weightMap := (weightEquiv P Q f).symm
  coweightMap := (coweightEquiv P Q f).symm
  indexEquiv := f.indexEquiv.symm
  weight_coweight_transpose := by
    ext n m
    nth_rw 2 [show m = (weightEquiv P Q f) ((weightEquiv P Q f).symm m) by
      exact (LinearEquiv.symm_apply_eq (weightEquiv P Q f)).mp rfl]
    nth_rw 1 [show n = (coweightEquiv P Q f) ((coweightEquiv P Q f).symm n) by
      exact (LinearEquiv.symm_apply_eq (coweightEquiv P Q f)).mp rfl]
    have := f.weight_coweight_transpose
    rw [LinearMap.ext_iff₂] at this
    exact Eq.symm (this ((coweightEquiv P Q f).symm n) ((weightEquiv P Q f).symm m))
  root_weightMap := by
    ext i
    simp only [LinearEquiv.coe_coe, comp_apply]
    have := f.root_weightMap
    rw [funext_iff] at this
    specialize this (f.indexEquiv.symm i)
    simp only [comp_apply, Equiv.apply_symm_apply] at this
    simp [← this]
  coroot_coweightMap := by
    ext i
    simp only [LinearEquiv.coe_coe, comp_apply, Equiv.symm_symm]
    have := f.coroot_coweightMap
    rw [funext_iff] at this
    specialize this (f.indexEquiv i)
    simp only [comp_apply, Equiv.symm_apply_apply] at this
    simp [← this]
  bijective_weightMap := by
    simp only [LinearEquiv.coe_coe]
    exact LinearEquiv.bijective (weightEquiv P Q f).symm
  bijective_coweightMap := by
    simp only [LinearEquiv.coe_coe]
    exact LinearEquiv.bijective (coweightEquiv P Q f).symm
@[simp]
lemma inv_weightMap {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂]
    [Module R N₂] (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂)
    (f : RootPairing.Equiv P Q) : (symm P Q f).weightMap = (weightEquiv P Q f).symm :=
  rfl
@[simp]
lemma inv_coweightMap {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂]
    [Module R N₂] (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂)
    (f : RootPairing.Equiv P Q) : (symm P Q f).coweightMap = (coweightEquiv P Q f).symm :=
  rfl
@[simp]
lemma inv_indexEquiv {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂]
    [Module R N₂] (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂)
    (f : RootPairing.Equiv P Q) : (symm P Q f).indexEquiv = (Hom.indexEquiv f.toHom).symm :=
  rfl
instance (P : RootPairing ι R M N) : Group (RootPairing.Equiv P P) where
  mul := comp
  mul_assoc := comp_assoc
  one := id P
  one_mul := id_comp P P
  mul_one := comp_id P P
  inv := symm P P
  inv_mul_cancel e := by
    ext m
    · rw [← weightEquiv_apply]
      simp
    · rw [← coweightEquiv_apply]
      simp
    · simp
end Equiv
abbrev Aut (P : RootPairing ι R M N) := (RootPairing.Equiv P P)
namespace Equiv
def toEndUnit (P : RootPairing ι R M N) : Aut P ≃* (End P)ˣ where
  toFun f :=
  { val :=  f.toHom
    inv := (Equiv.symm P P f).toHom
    val_inv := by ext <;> simp
    inv_val := by ext <;> simp }
  invFun f :=
  { f.val with
    bijective_weightMap := by
      refine bijective_iff_has_inverse.mpr ?_
      use f.inv.weightMap
      constructor
      · refine leftInverse_iff_comp.mpr ?_
        simp only [← @LinearMap.coe_comp]
        rw [← Hom.weightMap_mul, f.inv_val, Hom.weightMap_one, LinearMap.id_coe]
      · refine rightInverse_iff_comp.mpr ?_
        simp only [← @LinearMap.coe_comp]
        rw [← Hom.weightMap_mul, f.val_inv, Hom.weightMap_one, LinearMap.id_coe]
    bijective_coweightMap := by
      refine bijective_iff_has_inverse.mpr ?_
      use f.inv.coweightMap
      constructor
      · refine leftInverse_iff_comp.mpr ?_
        simp only [← @LinearMap.coe_comp]
        rw [← Hom.coweightMap_mul, f.val_inv, Hom.coweightMap_one, LinearMap.id_coe]
      · refine rightInverse_iff_comp.mpr ?_
        simp only [← @LinearMap.coe_comp]
        rw [← Hom.coweightMap_mul, f.inv_val, Hom.coweightMap_one, LinearMap.id_coe] }
  left_inv f := by simp
  right_inv f := by simp
  map_mul' f g := by
    simp only [Equiv.mul_eq_comp, Equiv.toHom_comp]
    ext <;> simp
lemma toEndUnit_val (P : RootPairing ι R M N) (g : Aut P) : (toEndUnit P g).val = g.toHom :=
  rfl
lemma toEndUnit_inv (P : RootPairing ι R M N) (g : Aut P) :
    (toEndUnit P g).inv = (symm P P g).toHom :=
  rfl
@[simps]
def weightHom (P : RootPairing ι R M N) : Aut P →* (M ≃ₗ[R] M) where
  toFun := weightEquiv P P
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
lemma weightHom_toLinearMap {P : RootPairing ι R M N} (g : Aut P) :
    ((weightHom P) g).toLinearMap = (Hom.weightHom P) g.toHom :=
  rfl
lemma weightHom_injective (P : RootPairing ι R M N) : Injective (Equiv.weightHom P) := by
  refine Injective.of_comp (f := LinearEquiv.toLinearMap) fun g g' hgg' => ?_
  let h : ((weightHom P) g).toLinearMap = ((weightHom P) g').toLinearMap := hgg' 
  rw [weightHom_toLinearMap, weightHom_toLinearMap] at h
  suffices h' : g.toHom = g'.toHom by
    exact Equiv.ext hgg' (congrArg Hom.coweightMap h') (congrArg Hom.indexEquiv h')
  exact Hom.weightHom_injective P hgg'
@[simps]
def coweightHom (P : RootPairing ι R M N) : Aut P →* (N ≃ₗ[R] N)ᵐᵒᵖ where
  toFun g := MulOpposite.op ((coweightEquiv P P) g)
  map_one' := by
    simp only [MulOpposite.op_eq_one_iff]
    exact LinearEquiv.toLinearMap_inj.mp rfl
  map_mul' := by
    simp only [mul_eq_comp, coweightEquiv_comp_toLin]
    exact fun x y ↦ rfl
lemma coweightHom_toLinearMap {P : RootPairing ι R M N} (g : Aut P) :
    (MulOpposite.unop ((coweightHom P) g)).toLinearMap =
      MulOpposite.unop ((Hom.coweightHom P) g.toHom) :=
  rfl
lemma coweightHom_injective (P : RootPairing ι R M N) : Injective (Equiv.coweightHom P) := by
  refine Injective.of_comp (f := fun a => MulOpposite.op a) fun g g' hgg' => ?_
  have h : (MulOpposite.unop ((coweightHom P) g)).toLinearMap =
      (MulOpposite.unop ((coweightHom P) g')).toLinearMap := by
    simp_all
  rw [coweightHom_toLinearMap, coweightHom_toLinearMap] at h
  suffices h' : g.toHom = g'.toHom by
    exact Equiv.ext (congrArg Hom.weightMap h') h (congrArg Hom.indexEquiv h')
  apply Hom.coweightHom_injective P
  exact MulOpposite.unop_inj.mp h
def reflection (P : RootPairing ι R M N) (i : ι) : Aut P where
  weightMap := P.reflection i
  coweightMap := P.coreflection i
  indexEquiv := P.reflection_perm i
  weight_coweight_transpose := by
    ext f x
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply,
      PerfectPairing.toDualRight_apply, LinearMap.dualMap_apply, PerfectPairing.flip_apply_apply,
      LinearEquiv.comp_coe, LinearEquiv.trans_apply]
    rw [RootPairing.reflection_apply, RootPairing.coreflection_apply]
    simp only [← PerfectPairing.toLin_apply, map_sub, map_smul, LinearMap.sub_apply,
      toLin_toPerfectPairing, LinearMap.smul_apply, smul_eq_mul, sub_right_inj]
    simp only [PerfectPairing.toLin_apply, PerfectPairing.flip_apply_apply, mul_comm]
  root_weightMap := by ext; simp
  coroot_coweightMap := by ext; simp
  bijective_weightMap := by
    simp only [LinearEquiv.coe_coe]
    exact LinearEquiv.bijective (P.reflection i)
  bijective_coweightMap := by
    simp only [LinearEquiv.coe_coe]
    exact LinearEquiv.bijective (P.coreflection i)
@[simp]
lemma reflection_weightEquiv (P : RootPairing ι R M N) (i : ι) :
    (reflection P i).weightEquiv = P.reflection i :=
  LinearEquiv.toLinearMap_inj.mp rfl
@[simp]
lemma reflection_coweightEquiv (P : RootPairing ι R M N) (i : ι) :
    (reflection P i).coweightEquiv = P.coreflection i :=
  LinearEquiv.toLinearMap_inj.mp rfl
@[simp]
lemma reflection_indexEquiv (P : RootPairing ι R M N) (i : ι) :
    (reflection P i).indexEquiv = P.reflection_perm i := rfl
end Equiv
end RootPairing