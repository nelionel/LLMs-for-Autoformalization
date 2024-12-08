import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Ring.Opposite
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.SingleObj
import Mathlib.Data.Matrix.DMatrix
import Mathlib.Data.Matrix.Mul
open CategoryTheory CategoryTheory.Preadditive
open scoped Classical
noncomputable section
namespace CategoryTheory
universe w v₁ v₂ u₁ u₂
variable (C : Type u₁) [Category.{v₁} C] [Preadditive C]
structure Mat_ where
  ι : Type
  [fintype : Fintype ι]
  X : ι → C
attribute [instance] Mat_.fintype
namespace Mat_
variable {C}
def Hom (M N : Mat_ C) : Type v₁ :=
  DMatrix M.ι N.ι fun i j => M.X i ⟶ N.X j
namespace Hom
def id (M : Mat_ C) : Hom M M := fun i j => if h : i = j then eqToHom (congr_arg M.X h) else 0
def comp {M N K : Mat_ C} (f : Hom M N) (g : Hom N K) : Hom M K := fun i k =>
  ∑ j : N.ι, f i j ≫ g j k
end Hom
section
attribute [local simp] Hom.id Hom.comp
instance : Category.{v₁} (Mat_ C) where
  Hom := Hom
  id := Hom.id
  comp f g := f.comp g
  id_comp f := by simp (config := { unfoldPartialApp := true }) [dite_comp]
  comp_id f := by simp (config := { unfoldPartialApp := true }) [comp_dite]
  assoc f g h := by
    apply DMatrix.ext
    intros
    simp_rw [Hom.comp, sum_comp, comp_sum, Category.assoc]
    rw [Finset.sum_comm]
@[ext]
theorem hom_ext {M N : Mat_ C} (f g : M ⟶ N) (H : ∀ i j, f i j = g i j) : f = g :=
  DMatrix.ext_iff.mp H
theorem id_def (M : Mat_ C) :
    (𝟙 M : Hom M M) = fun i j => if h : i = j then eqToHom (congr_arg M.X h) else 0 :=
  rfl
theorem id_apply (M : Mat_ C) (i j : M.ι) :
    (𝟙 M : Hom M M) i j = if h : i = j then eqToHom (congr_arg M.X h) else 0 :=
  rfl
@[simp]
theorem id_apply_self (M : Mat_ C) (i : M.ι) : (𝟙 M : Hom M M) i i = 𝟙 _ := by simp [id_apply]
@[simp]
theorem id_apply_of_ne (M : Mat_ C) (i j : M.ι) (h : i ≠ j) : (𝟙 M : Hom M M) i j = 0 := by
  simp [id_apply, h]
theorem comp_def {M N K : Mat_ C} (f : M ⟶ N) (g : N ⟶ K) :
    f ≫ g = fun i k => ∑ j : N.ι, f i j ≫ g j k :=
  rfl
@[simp]
theorem comp_apply {M N K : Mat_ C} (f : M ⟶ N) (g : N ⟶ K) (i k) :
    (f ≫ g) i k = ∑ j : N.ι, f i j ≫ g j k :=
  rfl
instance (M N : Mat_ C) : Inhabited (M ⟶ N) :=
  ⟨fun i j => (0 : M.X i ⟶ N.X j)⟩
end
instance (M N : Mat_ C) : AddCommGroup (M ⟶ N) := by
  change AddCommGroup (DMatrix M.ι N.ι _)
  infer_instance
@[simp]
theorem add_apply {M N : Mat_ C} (f g : M ⟶ N) (i j) : (f + g) i j = f i j + g i j :=
  rfl
instance : Preadditive (Mat_ C) where
  add_comp M N K f f' g := by ext; simp [Finset.sum_add_distrib]
  comp_add M N K f g g' := by ext; simp [Finset.sum_add_distrib]
open CategoryTheory.Limits
instance hasFiniteBiproducts : HasFiniteBiproducts (Mat_ C) where
  out n :=
    { has_biproduct := fun f =>
        hasBiproduct_of_total
          { pt := ⟨Σ j, (f j).ι, fun p => (f p.1).X p.2⟩
            π := fun j x y => by
              refine if h : x.1 = j then ?_ else 0
              refine if h' : @Eq.ndrec (Fin n) x.1 (fun j => (f j).ι) x.2 _ h = y then ?_ else 0
              apply eqToHom
              substs h h'
              rfl
            ι := fun j x y => by
              refine if h : y.1 = j then ?_ else 0
              refine if h' : @Eq.ndrec _ y.1 (fun j => (f j).ι) y.2 _ h = x then ?_ else 0
              apply eqToHom
              substs h h'
              rfl
            ι_π := fun j j' => by
              ext x y
              dsimp
              simp_rw [dite_comp, comp_dite]
              simp only [ite_self, dite_eq_ite, Limits.comp_zero, Limits.zero_comp,
                eqToHom_trans, Finset.sum_congr]
              erw [Finset.sum_sigma]
              dsimp
              simp only [if_true, Finset.sum_dite_irrel, Finset.mem_univ,
                Finset.sum_const_zero, Finset.sum_congr, Finset.sum_dite_eq']
              split_ifs with h h'
              · substs h h'
                simp only [CategoryTheory.eqToHom_refl, CategoryTheory.Mat_.id_apply_self]
              · subst h
                rw [eqToHom_refl, id_apply_of_ne _ _ _ h']
              · rfl }
          (by
            dsimp
            ext1 ⟨i, j⟩
            rintro ⟨i', j'⟩
            rw [Finset.sum_apply, Finset.sum_apply]
            dsimp
            rw [Finset.sum_eq_single i]; rotate_left
            · intro b _ hb
              apply Finset.sum_eq_zero
              intro x _
              rw [dif_neg hb.symm, zero_comp]
            · intro hi
              simp at hi
            rw [Finset.sum_eq_single j]; rotate_left
            · intro b _ hb
              rw [dif_pos rfl, dif_neg, zero_comp]
              simp only
              tauto
            · intro hj
              simp at hj
            simp only [eqToHom_refl, dite_eq_ite, ite_true, Category.id_comp, ne_eq,
              Sigma.mk.inj_iff, not_and, id_def]
            by_cases h : i' = i
            · subst h
              rw [dif_pos rfl]
              simp only [heq_eq_eq, true_and]
              by_cases h : j' = j
              · subst h
                simp
              · rw [dif_neg h, dif_neg (Ne.symm h)]
            · rw [dif_neg h, dif_neg]
              tauto) }
end Mat_
namespace Functor
variable {C} {D : Type*} [Category.{v₁} D] [Preadditive D]
attribute [local simp] Mat_.id_apply eqToHom_map
@[simps]
def mapMat_ (F : C ⥤ D) [Functor.Additive F] : Mat_ C ⥤ Mat_ D where
  obj M := ⟨M.ι, fun i => F.obj (M.X i)⟩
  map f i j := F.map (f i j)
@[simps!]
def mapMatId : (𝟭 C).mapMat_ ≅ 𝟭 (Mat_ C) :=
  NatIso.ofComponents (fun M => eqToIso (by cases M; rfl)) fun {M N} f => by
    ext
    cases M; cases N
    simp [comp_dite, dite_comp]
@[simps!]
def mapMatComp {E : Type*} [Category.{v₁} E] [Preadditive E] (F : C ⥤ D) [Functor.Additive F]
    (G : D ⥤ E) [Functor.Additive G] : (F ⋙ G).mapMat_ ≅ F.mapMat_ ⋙ G.mapMat_ :=
  NatIso.ofComponents (fun M => eqToIso (by cases M; rfl)) fun {M N} f => by
    ext
    cases M; cases N
    simp [comp_dite, dite_comp]
end Functor
namespace Mat_
@[simps]
def embedding : C ⥤ Mat_ C where
  obj X := ⟨PUnit, fun _ => X⟩
  map f _ _ := f
  map_id _ := by ext ⟨⟩; simp
  map_comp _ _ := by ext ⟨⟩; simp
namespace Embedding
instance : (embedding C).Faithful where
  map_injective h := congr_fun (congr_fun h PUnit.unit) PUnit.unit
instance : (embedding C).Full where map_surjective f := ⟨f PUnit.unit PUnit.unit, rfl⟩
instance : Functor.Additive (embedding C) where
end Embedding
instance [Inhabited C] : Inhabited (Mat_ C) :=
  ⟨(embedding C).obj default⟩
open CategoryTheory.Limits
variable {C}
@[simps]
def isoBiproductEmbedding (M : Mat_ C) : M ≅ ⨁ fun i => (embedding C).obj (M.X i) where
  hom := biproduct.lift fun i j _ => if h : j = i then eqToHom (congr_arg M.X h) else 0
  inv := biproduct.desc fun i _ k => if h : i = k then eqToHom (congr_arg M.X h) else 0
  hom_inv_id := by
    simp only [biproduct.lift_desc]
    funext i j
    dsimp [id_def]
    rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single i]; rotate_left
    · intro b _ hb
      dsimp
      rw [Fintype.univ_ofSubsingleton, Finset.sum_singleton, dif_neg hb.symm, zero_comp]
    · intro h
      simp at h
    simp
  inv_hom_id := by
    apply biproduct.hom_ext
    intro i
    apply biproduct.hom_ext'
    intro j
    simp only [Category.id_comp, Category.assoc, biproduct.lift_π, biproduct.ι_desc_assoc,
      biproduct.ι_π]
    ext ⟨⟩ ⟨⟩
    simp only [embedding, comp_apply, comp_dite, dite_comp, comp_zero, zero_comp,
      Finset.sum_dite_eq', Finset.mem_univ, ite_true, eqToHom_refl, Category.comp_id]
    split_ifs with h
    · subst h
      simp
    · rfl
variable {D : Type u₁} [Category.{v₁} D] [Preadditive D]
instance (F : Mat_ C ⥤ D) [Functor.Additive F] (M : Mat_ C) :
    HasBiproduct (fun i => F.obj ((embedding C).obj (M.X i))) :=
  F.hasBiproduct_of_preserves _
def additiveObjIsoBiproduct (F : Mat_ C ⥤ D) [Functor.Additive F] (M : Mat_ C) :
    F.obj M ≅ ⨁ fun i => F.obj ((embedding C).obj (M.X i)) :=
  F.mapIso (isoBiproductEmbedding M) ≪≫ F.mapBiproduct _
@[reassoc (attr := simp)]
lemma additiveObjIsoBiproduct_hom_π (F : Mat_ C ⥤ D) [Functor.Additive F] (M : Mat_ C) (i : M.ι) :
    (additiveObjIsoBiproduct F M).hom ≫ biproduct.π _ i =
      F.map (M.isoBiproductEmbedding.hom ≫ biproduct.π _ i) := by
  dsimp [additiveObjIsoBiproduct]
  rw [biproduct.lift_π, Category.assoc]
  erw [biproduct.lift_π, ← F.map_comp]
  simp
@[reassoc (attr := simp)]
lemma ι_additiveObjIsoBiproduct_inv (F : Mat_ C ⥤ D) [Functor.Additive F] (M : Mat_ C) (i : M.ι) :
    biproduct.ι _ i ≫ (additiveObjIsoBiproduct F M).inv =
      F.map (biproduct.ι _ i ≫ M.isoBiproductEmbedding.inv) := by
  dsimp [additiveObjIsoBiproduct, Functor.mapBiproduct, Functor.mapBicone]
  simp only [biproduct.ι_desc, biproduct.ι_desc_assoc, ← F.map_comp]
variable [HasFiniteBiproducts D]
@[reassoc]
theorem additiveObjIsoBiproduct_naturality (F : Mat_ C ⥤ D) [Functor.Additive F] {M N : Mat_ C}
    (f : M ⟶ N) :
    F.map f ≫ (additiveObjIsoBiproduct F N).hom =
      (additiveObjIsoBiproduct F M).hom ≫
        biproduct.matrix fun i j => F.map ((embedding C).map (f i j)) := by
  ext i : 1
  simp only [Category.assoc, additiveObjIsoBiproduct_hom_π, isoBiproductEmbedding_hom,
    embedding_obj_ι, embedding_obj_X, biproduct.lift_π, biproduct.matrix_π,
    ← cancel_epi (additiveObjIsoBiproduct F M).inv, Iso.inv_hom_id_assoc]
  ext j : 1
  simp only [ι_additiveObjIsoBiproduct_inv_assoc, isoBiproductEmbedding_inv,
    biproduct.ι_desc, ← F.map_comp]
  congr 1
  funext ⟨⟩ ⟨⟩
  simp [comp_apply, dite_comp, comp_dite]
@[reassoc]
theorem additiveObjIsoBiproduct_naturality' (F : Mat_ C ⥤ D) [Functor.Additive F] {M N : Mat_ C}
    (f : M ⟶ N) :
    (additiveObjIsoBiproduct F M).inv ≫ F.map f =
      biproduct.matrix (fun i j => F.map ((embedding C).map (f i j)) : _) ≫
        (additiveObjIsoBiproduct F N).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, additiveObjIsoBiproduct_naturality]
attribute [local simp] biproduct.lift_desc
@[simps]
def lift (F : C ⥤ D) [Functor.Additive F] : Mat_ C ⥤ D where
  obj X := ⨁ fun i => F.obj (X.X i)
  map f := biproduct.matrix fun i j => F.map (f i j)
  map_id X := by
    dsimp
    ext i j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
instance lift_additive (F : C ⥤ D) [Functor.Additive F] : Functor.Additive (lift F) where
@[simps!]
def embeddingLiftIso (F : C ⥤ D) [Functor.Additive F] : embedding C ⋙ lift F ≅ F :=
  NatIso.ofComponents
    (fun X =>
      { hom := biproduct.desc fun _ => 𝟙 (F.obj X)
        inv := biproduct.lift fun _ => 𝟙 (F.obj X) })
def liftUnique (F : C ⥤ D) [Functor.Additive F] (L : Mat_ C ⥤ D) [Functor.Additive L]
    (α : embedding C ⋙ L ≅ F) : L ≅ lift F :=
  NatIso.ofComponents
    (fun M =>
      additiveObjIsoBiproduct L M ≪≫
        (biproduct.mapIso fun i => α.app (M.X i)) ≪≫
          (biproduct.mapIso fun i => (embeddingLiftIso F).symm.app (M.X i)) ≪≫
            (additiveObjIsoBiproduct (lift F) M).symm)
    fun f => by
      dsimp only [Iso.trans_hom, Iso.symm_hom, biproduct.mapIso_hom]
      simp only [additiveObjIsoBiproduct_naturality_assoc]
      simp only [biproduct.matrix_map_assoc, Category.assoc]
      simp only [additiveObjIsoBiproduct_naturality']
      simp only [biproduct.map_matrix_assoc, Category.assoc]
      congr 3
      ext j k
      apply biproduct.hom_ext
      rintro ⟨⟩
      dsimp
      simpa using α.hom.naturality (f j k)
def ext {F G : Mat_ C ⥤ D} [Functor.Additive F] [Functor.Additive G]
    (α : embedding C ⋙ F ≅ embedding C ⋙ G) : F ≅ G :=
  liftUnique (embedding C ⋙ G) _ α ≪≫ (liftUnique _ _ (Iso.refl _)).symm
def equivalenceSelfOfHasFiniteBiproductsAux [HasFiniteBiproducts C] :
    embedding C ⋙ 𝟭 (Mat_ C) ≅ embedding C ⋙ lift (𝟭 C) ⋙ embedding C :=
  Functor.rightUnitor _ ≪≫
    (Functor.leftUnitor _).symm ≪≫
      isoWhiskerRight (embeddingLiftIso _).symm _ ≪≫ Functor.associator _ _ _
def equivalenceSelfOfHasFiniteBiproducts (C : Type (u₁ + 1)) [LargeCategory C] [Preadditive C]
    [HasFiniteBiproducts C] : Mat_ C ≌ C :=
  Equivalence.mk
    (
      lift
      (𝟭 C))
    (embedding C) (ext equivalenceSelfOfHasFiniteBiproductsAux) (embeddingLiftIso (𝟭 C))
@[simp]
theorem equivalenceSelfOfHasFiniteBiproducts_functor {C : Type (u₁ + 1)} [LargeCategory C]
    [Preadditive C] [HasFiniteBiproducts C] :
    (equivalenceSelfOfHasFiniteBiproducts C).functor = lift (𝟭 C) :=
  rfl
@[simp]
theorem equivalenceSelfOfHasFiniteBiproducts_inverse {C : Type (u₁ + 1)} [LargeCategory C]
    [Preadditive C] [HasFiniteBiproducts C] :
    (equivalenceSelfOfHasFiniteBiproducts C).inverse = embedding C :=
  rfl
end Mat_
universe u
@[nolint unusedArguments]
def Mat (_ : Type u) :=
  FintypeCat.{u}
instance (R : Type u) : Inhabited (Mat R) := by
  dsimp [Mat]
  infer_instance
instance (R : Type u) : CoeSort (Mat R) (Type u) :=
  Bundled.coeSort
open Matrix
instance (R : Type u) [Semiring R] : Category (Mat R) where
  Hom X Y := Matrix X Y R
  id X := (1 : Matrix X X R)
  comp {X Y Z} f g := (show Matrix X Y R from f) * (show Matrix Y Z R from g)
  assoc := by intros; simp [Matrix.mul_assoc]
namespace Mat
section
variable {R : Type u} [Semiring R]
@[ext]
theorem hom_ext {X Y : Mat R} (f g : X ⟶ Y) (h : ∀ i j, f i j = g i j) : f = g :=
  Matrix.ext_iff.mp h
variable (R)
theorem id_def (M : Mat R) : 𝟙 M = fun i j => if i = j then 1 else 0 :=
  rfl
theorem id_apply (M : Mat R) (i j : M) : (𝟙 M : Matrix M M R) i j = if i = j then 1 else 0 :=
  rfl
@[simp]
theorem id_apply_self (M : Mat R) (i : M) : (𝟙 M : Matrix M M R) i i = 1 := by simp [id_apply]
@[simp]
theorem id_apply_of_ne (M : Mat R) (i j : M) (h : i ≠ j) : (𝟙 M : Matrix M M R) i j = 0 := by
  simp [id_apply, h]
theorem comp_def {M N K : Mat R} (f : M ⟶ N) (g : N ⟶ K) :
    f ≫ g = fun i k => ∑ j : N, f i j * g j k :=
  rfl
@[simp]
theorem comp_apply {M N K : Mat R} (f : M ⟶ N) (g : N ⟶ K) (i k) :
    (f ≫ g) i k = ∑ j : N, f i j * g j k :=
  rfl
instance (M N : Mat R) : Inhabited (M ⟶ N) :=
  ⟨fun (_ : M) (_ : N) => (0 : R)⟩
end
variable (R : Type) [Ring R]
open Opposite
@[simps]
def equivalenceSingleObjInverse : Mat_ (SingleObj Rᵐᵒᵖ) ⥤ Mat R where
  obj X := FintypeCat.of X.ι
  map f i j := MulOpposite.unop (f i j)
  map_id X := by
    ext
    simp only [Mat_.id_def, id_def]
    split_ifs <;> rfl
  map_comp f g := by
    ext
    simp only [Mat_.comp_apply, comp_apply]
    apply Finset.unop_sum
instance : (equivalenceSingleObjInverse R).Faithful where
  map_injective w := by
    ext
    apply_fun MulOpposite.unop using MulOpposite.unop_injective
    exact congr_fun (congr_fun w _) _
instance : (equivalenceSingleObjInverse R).Full where
  map_surjective f := ⟨fun i j => MulOpposite.op (f i j), rfl⟩
instance : (equivalenceSingleObjInverse R).EssSurj where
  mem_essImage X :=
    ⟨{  ι := X
        X := fun _ => PUnit.unit }, ⟨eqToIso (by dsimp; cases X; congr)⟩⟩
instance : (equivalenceSingleObjInverse R).IsEquivalence where
def equivalenceSingleObj : Mat R ≌ Mat_ (SingleObj Rᵐᵒᵖ) :=
  (equivalenceSingleObjInverse R).asEquivalence.symm
instance (X Y : Mat R) : AddCommGroup (X ⟶ Y) := by
  change AddCommGroup (Matrix X Y R)
  infer_instance
variable {R}
@[simp]
theorem add_apply {M N : Mat R} (f g : M ⟶ N) (i j) : (f + g) i j = f i j + g i j :=
  rfl
attribute [local simp] add_mul mul_add Finset.sum_add_distrib
instance : Preadditive (Mat R) where
end Mat
end CategoryTheory