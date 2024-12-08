import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
universe w v u
namespace CategoryTheory
open Category Limits
namespace SmallObject
variable {C : Type u} [Category.{v} C] {I : Type w} {A B : I → C} (f : ∀ i, A i ⟶ B i)
section
variable {S : C} {X Y : C} (πX : X ⟶ S) (πY : Y ⟶ S) (φ : X ⟶ Y)
structure FunctorObjIndex where
  i : I
  t : A i ⟶ X
  b : B i ⟶ S
  w : t ≫ πX = f i ≫ b
attribute [reassoc (attr := simp)] FunctorObjIndex.w
variable [HasColimitsOfShape (Discrete (FunctorObjIndex f πX)) C]
  [HasColimitsOfShape (Discrete (FunctorObjIndex f πY)) C]
abbrev functorObjSrcFamily (x : FunctorObjIndex f πX) : C := A x.i
abbrev functorObjTgtFamily (x : FunctorObjIndex f πX) : C := B x.i
abbrev functorObjLeftFamily (x : FunctorObjIndex f πX) :
    functorObjSrcFamily f πX x ⟶ functorObjTgtFamily f πX x := f x.i
noncomputable abbrev functorObjTop : ∐ functorObjSrcFamily f πX ⟶ X :=
  Limits.Sigma.desc (fun x => x.t)
noncomputable abbrev functorObjLeft :
    ∐ functorObjSrcFamily f πX ⟶ ∐ functorObjTgtFamily f πX :=
  Limits.Sigma.map (functorObjLeftFamily f πX)
section
variable [HasPushout (functorObjTop f πX) (functorObjLeft f πX)]
noncomputable abbrev functorObj : C :=
  pushout (functorObjTop f πX) (functorObjLeft f πX)
noncomputable abbrev ιFunctorObj : X ⟶ functorObj f πX := pushout.inl _ _
noncomputable abbrev ρFunctorObj : ∐ functorObjTgtFamily f πX ⟶ functorObj f πX := pushout.inr _ _
@[reassoc]
lemma functorObj_comm :
    functorObjTop f πX ≫ ιFunctorObj f πX = functorObjLeft f πX ≫ ρFunctorObj f πX :=
  pushout.condition
@[reassoc]
lemma FunctorObjIndex.comm (x : FunctorObjIndex f πX) :
    f x.i ≫ Sigma.ι (functorObjTgtFamily f πX) x ≫ ρFunctorObj f πX = x.t ≫ ιFunctorObj f πX := by
  simpa using (Sigma.ι (functorObjSrcFamily f πX) x ≫= functorObj_comm f πX).symm
noncomputable abbrev π'FunctorObj : ∐ functorObjTgtFamily f πX ⟶ S := Sigma.desc (fun x => x.b)
noncomputable def πFunctorObj : functorObj f πX ⟶ S :=
  pushout.desc πX (π'FunctorObj f πX) (by ext; simp [π'FunctorObj])
@[reassoc (attr := simp)]
lemma ρFunctorObj_π : ρFunctorObj f πX ≫ πFunctorObj f πX = π'FunctorObj f πX := by
  simp [πFunctorObj]
@[reassoc (attr := simp)]
lemma ιFunctorObj_πFunctorObj : ιFunctorObj f πX ≫ πFunctorObj f πX = πX := by
  simp [ιFunctorObj, πFunctorObj]
noncomputable def functorMapSrc (hφ : φ ≫ πY = πX) :
    ∐ (functorObjSrcFamily f πX) ⟶ ∐ functorObjSrcFamily f πY :=
  Sigma.map' (fun x => FunctorObjIndex.mk x.i (x.t ≫ φ) x.b (by simp [hφ])) (fun _ => 𝟙 _)
end
variable (hφ : φ ≫ πY = πX)
@[reassoc]
lemma ι_functorMapSrc (i : I) (t : A i ⟶ X) (b : B i ⟶ S) (w : t ≫ πX = f i ≫ b)
    (t' : A i ⟶ Y) (fac : t ≫ φ = t') :
    Sigma.ι _ (FunctorObjIndex.mk i t b w) ≫ functorMapSrc f πX πY φ hφ =
      Sigma.ι (functorObjSrcFamily f πY)
        (FunctorObjIndex.mk i t' b (by rw [← w, ← fac, assoc, hφ])) := by
  subst fac
  simp [functorMapSrc]
@[reassoc (attr := simp)]
lemma functorMapSrc_functorObjTop :
    functorMapSrc f πX πY φ hφ ≫ functorObjTop f πY = functorObjTop f πX ≫ φ := by
  ext ⟨i, t, b, w⟩
  simp [ι_functorMapSrc_assoc f πX πY φ hφ i t b w _ rfl]
noncomputable def functorMapTgt (hφ : φ ≫ πY = πX) :
    ∐ functorObjTgtFamily f πX ⟶ ∐ functorObjTgtFamily f πY :=
  Sigma.map' (fun x => FunctorObjIndex.mk x.i (x.t ≫ φ) x.b (by simp [hφ])) (fun _ => 𝟙 _)
@[reassoc]
lemma ι_functorMapTgt (i : I) (t : A i ⟶ X) (b : B i ⟶ S) (w : t ≫ πX = f i ≫ b)
    (t' : A i ⟶ Y) (fac : t ≫ φ = t') :
    Sigma.ι _ (FunctorObjIndex.mk i t b w) ≫ functorMapTgt f πX πY φ hφ =
      Sigma.ι (functorObjTgtFamily f πY)
        (FunctorObjIndex.mk i t' b (by rw [← w, ← fac, assoc, hφ])) := by
  subst fac
  simp [functorMapTgt]
lemma functorMap_comm :
    functorObjLeft f πX ≫ functorMapTgt f πX πY φ hφ =
      functorMapSrc f πX πY φ hφ ≫ functorObjLeft f πY := by
  ext ⟨i, t, b, w⟩
  simp only [ι_colimMap_assoc, Discrete.natTrans_app, ι_colimMap,
    ι_functorMapTgt f πX πY φ hφ i t b w _ rfl,
    ι_functorMapSrc_assoc f πX πY φ hφ i t b w _ rfl]
variable [HasPushout (functorObjTop f πX) (functorObjLeft f πX)]
  [HasPushout (functorObjTop f πY) (functorObjLeft f πY)]
noncomputable def functorMap : functorObj f πX ⟶ functorObj f πY :=
  pushout.map _ _ _ _ φ (functorMapTgt f πX πY φ hφ) (functorMapSrc f πX πY φ hφ) (by simp)
    (functorMap_comm f πX πY φ hφ)
@[reassoc (attr := simp)]
lemma functorMap_π : functorMap f πX πY φ hφ ≫ πFunctorObj f πY = πFunctorObj f πX := by
  ext ⟨i, t, b, w⟩
  · simp [functorMap, hφ]
  · simp [functorMap, ι_functorMapTgt_assoc f πX πY φ hφ i t b w _ rfl]
variable (X) in
@[simp]
lemma functorMap_id : functorMap f πX πX (𝟙 X) (by simp) = 𝟙 _ := by
  ext ⟨i, t, b, w⟩
  · simp [functorMap]
  · simp [functorMap, ι_functorMapTgt_assoc f πX πX (𝟙 X) (by simp) i t b w t (by simp)]
@[reassoc (attr := simp)]
lemma ιFunctorObj_naturality :
    ιFunctorObj f πX ≫ functorMap f πX πY φ hφ = φ ≫ ιFunctorObj f πY := by
  simp [ιFunctorObj, functorMap]
lemma ιFunctorObj_extension {i : I} (t : A i ⟶ X) (b : B i ⟶ S)
    (sq : CommSq t (f i) πX b) :
    ∃ (l : B i ⟶ functorObj f πX), f i ≫ l = t ≫ ιFunctorObj f πX ∧
      l ≫ πFunctorObj f πX = b :=
  ⟨Sigma.ι (functorObjTgtFamily f πX) (FunctorObjIndex.mk i t b sq.w) ≫
    ρFunctorObj f πX, (FunctorObjIndex.mk i t b _).comm, by simp⟩
end
variable (S : C) [HasPushouts C]
  [∀ {X : C} (πX : X ⟶ S), HasColimitsOfShape (Discrete (FunctorObjIndex f πX)) C]
@[simps! obj map]
noncomputable def functor : Over S ⥤ Over S where
  obj π := Over.mk (πFunctorObj f π.hom)
  map {π₁ π₂} φ := Over.homMk (functorMap f π₁.hom π₂.hom φ.left (Over.w φ))
  map_id _ := by ext; dsimp; simp
  map_comp {π₁ π₂ π₃} φ φ' := by
    ext1
    dsimp
    ext ⟨i, t, b, w⟩
    · simp
    · simp [functorMap, ι_functorMapTgt_assoc f π₁.hom π₂.hom φ.left (Over.w φ) i t b w _ rfl,
        ι_functorMapTgt_assoc f π₁.hom π₃.hom (φ.left ≫ φ'.left) (Over.w (φ ≫ φ')) i t b w _ rfl,
        ι_functorMapTgt_assoc f π₂.hom π₃.hom (φ'.left) (Over.w φ') i (t ≫ φ.left) b
          (by simp [w]) (t ≫ φ.left ≫ φ'.left) (by simp)]
@[simps! app]
noncomputable def ε : 𝟭 (Over S) ⟶ functor f S where
  app w := Over.homMk (ιFunctorObj f w.hom)
end SmallObject
end CategoryTheory