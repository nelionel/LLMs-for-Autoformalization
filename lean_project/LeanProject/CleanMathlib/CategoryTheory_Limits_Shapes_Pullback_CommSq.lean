import Mathlib.CategoryTheory.Limits.Constructions.ZeroObjects
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
noncomputable section
open CategoryTheory
open CategoryTheory.Limits
universe v₁ v₂ u₁ u₂
namespace CategoryTheory
variable {C : Type u₁} [Category.{v₁} C]
attribute [simp] CommSq.mk
namespace CommSq
variable {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
def cone (s : CommSq f g h i) : PullbackCone h i :=
  PullbackCone.mk _ _ s.w
def cocone (s : CommSq f g h i) : PushoutCocone f g :=
  PushoutCocone.mk _ _ s.w
@[simp]
theorem cone_fst (s : CommSq f g h i) : s.cone.fst = f :=
  rfl
@[simp]
theorem cone_snd (s : CommSq f g h i) : s.cone.snd = g :=
  rfl
@[simp]
theorem cocone_inl (s : CommSq f g h i) : s.cocone.inl = h :=
  rfl
@[simp]
theorem cocone_inr (s : CommSq f g h i) : s.cocone.inr = i :=
  rfl
def coneOp (p : CommSq f g h i) : p.cone.op ≅ p.flip.op.cocone :=
  PushoutCocone.ext (Iso.refl _) (by aesop_cat) (by aesop_cat)
def coconeOp (p : CommSq f g h i) : p.cocone.op ≅ p.flip.op.cone :=
  PullbackCone.ext (Iso.refl _) (by aesop_cat) (by aesop_cat)
def coneUnop {W X Y Z : Cᵒᵖ} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z} (p : CommSq f g h i) :
    p.cone.unop ≅ p.flip.unop.cocone :=
  PushoutCocone.ext (Iso.refl _) (by aesop_cat) (by aesop_cat)
def coconeUnop {W X Y Z : Cᵒᵖ} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
    (p : CommSq f g h i) : p.cocone.unop ≅ p.flip.unop.cone :=
  PullbackCone.ext (Iso.refl _) (by aesop_cat) (by aesop_cat)
end CommSq
structure IsPullback {P X Y Z : C} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z) extends
  CommSq fst snd f g : Prop where
  isLimit' : Nonempty (IsLimit (PullbackCone.mk _ _ w))
structure IsPushout {Z X Y P : C} (f : Z ⟶ X) (g : Z ⟶ Y) (inl : X ⟶ P) (inr : Y ⟶ P) extends
  CommSq f g inl inr : Prop where
  isColimit' : Nonempty (IsColimit (PushoutCocone.mk _ _ w))
section
structure BicartesianSq {W X Y Z : C} (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (i : Y ⟶ Z) extends
  IsPullback f g h i, IsPushout f g h i : Prop
attribute [nolint defLemma docBlame] BicartesianSq.toIsPushout
end
namespace IsPullback
variable {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
def cone (h : IsPullback fst snd f g) : PullbackCone f g :=
  h.toCommSq.cone
@[simp]
theorem cone_fst (h : IsPullback fst snd f g) : h.cone.fst = fst :=
  rfl
@[simp]
theorem cone_snd (h : IsPullback fst snd f g) : h.cone.snd = snd :=
  rfl
noncomputable def isLimit (h : IsPullback fst snd f g) : IsLimit h.cone :=
  h.isLimit'.some
noncomputable def lift (hP : IsPullback fst snd f g) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : W ⟶ P :=
  PullbackCone.IsLimit.lift hP.isLimit h k w
@[reassoc (attr := simp)]
lemma lift_fst (hP : IsPullback fst snd f g) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : hP.lift h k w ≫ fst = h :=
  PullbackCone.IsLimit.lift_fst hP.isLimit h k w
@[reassoc (attr := simp)]
lemma lift_snd (hP : IsPullback fst snd f g) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : hP.lift h k w ≫ snd = k :=
  PullbackCone.IsLimit.lift_snd hP.isLimit h k w
lemma hom_ext (hP : IsPullback fst snd f g) {W : C} {k l : W ⟶ P}
    (h₀ : k ≫ fst = l ≫ fst) (h₁ : k ≫ snd = l ≫ snd) : k = l :=
  PullbackCone.IsLimit.hom_ext hP.isLimit h₀ h₁
theorem of_isLimit {c : PullbackCone f g} (h : Limits.IsLimit c) : IsPullback c.fst c.snd f g :=
  { w := c.condition
    isLimit' := ⟨IsLimit.ofIsoLimit h (Limits.PullbackCone.ext (Iso.refl _)
      (by aesop_cat) (by aesop_cat))⟩ }
theorem of_isLimit' (w : CommSq fst snd f g) (h : Limits.IsLimit w.cone) :
    IsPullback fst snd f g :=
  of_isLimit h
lemma of_isLimit_cone {D : WalkingCospan ⥤ C} {c : Cone D} (hc : IsLimit c) :
    IsPullback (c.π.app .left) (c.π.app .right) (D.map WalkingCospan.Hom.inl)
      (D.map WalkingCospan.Hom.inr) where
  w := by simp_rw [Cone.w]
  isLimit' := ⟨IsLimit.equivOfNatIsoOfIso _ _ _ (PullbackCone.isoMk c) hc⟩
lemma hasPullback (h : IsPullback fst snd f g) : HasPullback f g where
  exists_limit := ⟨⟨h.cone, h.isLimit⟩⟩
theorem of_hasPullback (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    IsPullback (pullback.fst f g) (pullback.snd f g) f g :=
  of_isLimit (limit.isLimit (cospan f g))
theorem of_is_product {c : BinaryFan X Y} (h : Limits.IsLimit c) (t : IsTerminal Z) :
    IsPullback c.fst c.snd (t.from _) (t.from _) :=
  of_isLimit
    (isPullbackOfIsTerminalIsProduct _ _ _ _ t
      (IsLimit.ofIsoLimit h
        (Limits.Cones.ext (Iso.refl c.pt)
          (by
            rintro ⟨⟨⟩⟩ <;>
              · dsimp
                simp))))
theorem of_is_product' (h : Limits.IsLimit (BinaryFan.mk fst snd)) (t : IsTerminal Z) :
    IsPullback fst snd (t.from _) (t.from _) :=
  of_is_product h t
variable (X Y)
theorem of_hasBinaryProduct' [HasBinaryProduct X Y] [HasTerminal C] :
    IsPullback Limits.prod.fst Limits.prod.snd (terminal.from X) (terminal.from Y) :=
  of_is_product (limit.isLimit _) terminalIsTerminal
open ZeroObject
theorem of_hasBinaryProduct [HasBinaryProduct X Y] [HasZeroObject C] [HasZeroMorphisms C] :
    IsPullback Limits.prod.fst Limits.prod.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) := by
  convert @of_is_product _ _ X Y 0 _ (limit.isLimit _) HasZeroObject.zeroIsTerminal
    <;> subsingleton
section
variable {P' : C} {fst' : P' ⟶ X} {snd' : P' ⟶ Y}
noncomputable def isoIsPullback (h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g) :
    P ≅ P' :=
  IsLimit.conePointUniqueUpToIso h.isLimit h'.isLimit
@[reassoc (attr := simp)]
theorem isoIsPullback_hom_fst (h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g) :
    (h.isoIsPullback _ _ h').hom ≫ fst' = fst :=
  IsLimit.conePointUniqueUpToIso_hom_comp h.isLimit h'.isLimit WalkingCospan.left
@[reassoc (attr := simp)]
theorem isoIsPullback_hom_snd (h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g) :
    (h.isoIsPullback _ _ h').hom ≫ snd' = snd :=
  IsLimit.conePointUniqueUpToIso_hom_comp h.isLimit h'.isLimit WalkingCospan.right
@[reassoc (attr := simp)]
theorem isoIsPullback_inv_fst (h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g) :
    (h.isoIsPullback _ _ h').inv ≫ fst = fst' := by
  simp only [Iso.inv_comp_eq, isoIsPullback_hom_fst]
@[reassoc (attr := simp)]
theorem isoIsPullback_inv_snd (h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g) :
    (h.isoIsPullback _ _ h').inv ≫ snd = snd' := by
  simp only [Iso.inv_comp_eq, isoIsPullback_hom_snd]
end
variable {X Y}
noncomputable def isoPullback (h : IsPullback fst snd f g) [HasPullback f g] : P ≅ pullback f g :=
  (limit.isoLimitCone ⟨_, h.isLimit⟩).symm
@[reassoc (attr := simp)]
theorem isoPullback_hom_fst (h : IsPullback fst snd f g) [HasPullback f g] :
    h.isoPullback.hom ≫ pullback.fst _ _ = fst := by
  dsimp [isoPullback, cone, CommSq.cone]
  simp
@[reassoc (attr := simp)]
theorem isoPullback_hom_snd (h : IsPullback fst snd f g) [HasPullback f g] :
    h.isoPullback.hom ≫ pullback.snd _ _ = snd := by
  dsimp [isoPullback, cone, CommSq.cone]
  simp
@[reassoc (attr := simp)]
theorem isoPullback_inv_fst (h : IsPullback fst snd f g) [HasPullback f g] :
    h.isoPullback.inv ≫ fst = pullback.fst _ _ := by simp [Iso.inv_comp_eq]
@[reassoc (attr := simp)]
theorem isoPullback_inv_snd (h : IsPullback fst snd f g) [HasPullback f g] :
    h.isoPullback.inv ≫ snd = pullback.snd _ _ := by simp [Iso.inv_comp_eq]
theorem of_iso_pullback (h : CommSq fst snd f g) [HasPullback f g] (i : P ≅ pullback f g)
    (w₁ : i.hom ≫ pullback.fst _ _ = fst) (w₂ : i.hom ≫ pullback.snd _ _ = snd) :
      IsPullback fst snd f g :=
  of_isLimit' h
    (Limits.IsLimit.ofIsoLimit (limit.isLimit _)
      (@PullbackCone.ext _ _ _ _ _ _ _ (PullbackCone.mk _ _ _) _ i w₁.symm w₂.symm).symm)
theorem of_horiz_isIso [IsIso fst] [IsIso g] (sq : CommSq fst snd f g) : IsPullback fst snd f g :=
  of_isLimit' sq
    (by
      refine
        PullbackCone.IsLimit.mk _ (fun s => s.fst ≫ inv fst) (by aesop_cat)
          (fun s => ?_) (by aesop_cat)
      simp only [← cancel_mono g, Category.assoc, ← sq.w, IsIso.inv_hom_id_assoc, s.condition])
lemma of_iso (h : IsPullback fst snd f g)
    {P' X' Y' Z' : C} {fst' : P' ⟶ X'} {snd' : P' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}
    (e₁ : P ≅ P') (e₂ : X ≅ X') (e₃ : Y ≅ Y') (e₄ : Z ≅ Z')
    (commfst : fst ≫ e₂.hom = e₁.hom ≫ fst')
    (commsnd : snd ≫ e₃.hom = e₁.hom ≫ snd')
    (commf : f ≫ e₄.hom = e₂.hom ≫ f')
    (commg : g ≫ e₄.hom = e₃.hom ≫ g') :
    IsPullback fst' snd' f' g' where
  w := by
    rw [← cancel_epi e₁.hom, ← reassoc_of% commfst, ← commf,
      ← reassoc_of% commsnd, ← commg, h.w_assoc]
  isLimit' :=
    ⟨(IsLimit.postcomposeInvEquiv
        (cospanExt e₂ e₃ e₄ commf.symm commg.symm) _).1
          (IsLimit.ofIsoLimit h.isLimit (by
            refine PullbackCone.ext e₁ ?_ ?_
            · change fst = e₁.hom ≫ fst' ≫ e₂.inv
              rw [← reassoc_of% commfst, e₂.hom_inv_id, Category.comp_id]
            · change snd = e₁.hom ≫ snd' ≫ e₃.inv
              rw [← reassoc_of% commsnd, e₃.hom_inv_id, Category.comp_id]))⟩
section
variable {P X Y : C} {fst : P ⟶ X} {snd : P ⟶ X} {f : X ⟶ Y} [Mono f]
lemma isIso_fst_of_mono (h : IsPullback fst snd f f) : IsIso fst :=
  h.cone.isIso_fst_of_mono_of_isLimit h.isLimit
lemma isIso_snd_iso_of_mono {P X Y : C} {fst : P ⟶ X} {snd : P ⟶ X} {f : X ⟶ Y} [Mono f]
    (h : IsPullback fst snd f f) : IsIso snd :=
  h.cone.isIso_snd_of_mono_of_isLimit h.isLimit
end
end IsPullback
namespace IsPushout
variable {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
def cocone (h : IsPushout f g inl inr) : PushoutCocone f g :=
  h.toCommSq.cocone
@[simp]
theorem cocone_inl (h : IsPushout f g inl inr) : h.cocone.inl = inl :=
  rfl
@[simp]
theorem cocone_inr (h : IsPushout f g inl inr) : h.cocone.inr = inr :=
  rfl
noncomputable def isColimit (h : IsPushout f g inl inr) : IsColimit h.cocone :=
  h.isColimit'.some
noncomputable def desc (hP : IsPushout f g inl inr) {W : C} (h : X ⟶ W) (k : Y ⟶ W)
    (w : f ≫ h = g ≫ k) : P ⟶ W :=
  PushoutCocone.IsColimit.desc hP.isColimit h k w
@[reassoc (attr := simp)]
lemma inl_desc (hP : IsPushout f g inl inr) {W : C} (h : X ⟶ W) (k : Y ⟶ W)
    (w : f ≫ h = g ≫ k) : inl ≫ hP.desc h k w = h :=
  PushoutCocone.IsColimit.inl_desc hP.isColimit h k w
@[reassoc (attr := simp)]
lemma inr_desc (hP : IsPushout f g inl inr) {W : C} (h : X ⟶ W) (k : Y ⟶ W)
    (w : f ≫ h = g ≫ k) : inr ≫ hP.desc h k w = k :=
  PushoutCocone.IsColimit.inr_desc hP.isColimit h k w
lemma hom_ext (hP : IsPushout f g inl inr) {W : C} {k l : P ⟶ W}
    (h₀ : inl ≫ k = inl ≫ l) (h₁ : inr ≫ k = inr ≫ l) : k = l :=
  PushoutCocone.IsColimit.hom_ext hP.isColimit h₀ h₁
theorem of_isColimit {c : PushoutCocone f g} (h : Limits.IsColimit c) : IsPushout f g c.inl c.inr :=
  { w := c.condition
    isColimit' :=
      ⟨IsColimit.ofIsoColimit h (Limits.PushoutCocone.ext (Iso.refl _)
        (by aesop_cat) (by aesop_cat))⟩ }
theorem of_isColimit' (w : CommSq f g inl inr) (h : Limits.IsColimit w.cocone) :
    IsPushout f g inl inr :=
  of_isColimit h
lemma of_isColimit_cocone {D : WalkingSpan ⥤ C} {c : Cocone D} (hc : IsColimit c) :
    IsPushout (D.map WalkingSpan.Hom.fst) (D.map WalkingSpan.Hom.snd)
      (c.ι.app .left) (c.ι.app .right) where
  w := by simp_rw [Cocone.w]
  isColimit' := ⟨IsColimit.equivOfNatIsoOfIso _ _ _ (PushoutCocone.isoMk c) hc⟩
lemma hasPushout (h : IsPushout f g inl inr) : HasPushout f g where
  exists_colimit := ⟨⟨h.cocone, h.isColimit⟩⟩
theorem of_hasPushout (f : Z ⟶ X) (g : Z ⟶ Y) [HasPushout f g] :
    IsPushout f g (pushout.inl f g) (pushout.inr f g) :=
  of_isColimit (colimit.isColimit (span f g))
theorem of_is_coproduct {c : BinaryCofan X Y} (h : Limits.IsColimit c) (t : IsInitial Z) :
    IsPushout (t.to _) (t.to _) c.inl c.inr :=
  of_isColimit
    (isPushoutOfIsInitialIsCoproduct _ _ _ _ t
      (IsColimit.ofIsoColimit h
        (Limits.Cocones.ext (Iso.refl c.pt)
          (by
            rintro ⟨⟨⟩⟩ <;>
              · dsimp
                simp))))
theorem of_is_coproduct' (h : Limits.IsColimit (BinaryCofan.mk inl inr)) (t : IsInitial Z) :
    IsPushout (t.to _) (t.to _) inl inr :=
  of_is_coproduct h t
variable (X Y)
theorem of_hasBinaryCoproduct' [HasBinaryCoproduct X Y] [HasInitial C] :
    IsPushout (initial.to _) (initial.to _) (coprod.inl : X ⟶ _) (coprod.inr : Y ⟶ _) :=
  of_is_coproduct (colimit.isColimit _) initialIsInitial
open ZeroObject
theorem of_hasBinaryCoproduct [HasBinaryCoproduct X Y] [HasZeroObject C] [HasZeroMorphisms C] :
    IsPushout (0 : 0 ⟶ X) (0 : 0 ⟶ Y) coprod.inl coprod.inr := by
  convert @of_is_coproduct _ _ 0 X Y _ (colimit.isColimit _) HasZeroObject.zeroIsInitial
    <;> subsingleton
section
variable {P': C} {inl' : X ⟶ P'} {inr' : Y ⟶ P'}
noncomputable def isoIsPushout (h : IsPushout f g inl inr) (h' : IsPushout f g inl' inr') :
    P ≅ P' :=
  IsColimit.coconePointUniqueUpToIso h.isColimit h'.isColimit
@[reassoc (attr := simp)]
theorem inl_isoIsPushout_hom (h : IsPushout f g inl inr) (h' : IsPushout f g inl' inr') :
    inl ≫ (h.isoIsPushout _ _ h').hom = inl' :=
  IsColimit.comp_coconePointUniqueUpToIso_hom h.isColimit h'.isColimit WalkingSpan.left
@[reassoc (attr := simp)]
theorem inr_isoIsPushout_hom (h : IsPushout f g inl inr) (h' : IsPushout f g inl' inr') :
    inr ≫ (h.isoIsPushout _ _ h').hom = inr' :=
  IsColimit.comp_coconePointUniqueUpToIso_hom h.isColimit h'.isColimit WalkingSpan.right
@[reassoc (attr := simp)]
theorem inl_isoIsPushout_inv (h : IsPushout f g inl inr) (h' : IsPushout f g inl' inr') :
    inl' ≫ (h.isoIsPushout _ _ h').inv = inl := by
  simp only [Iso.comp_inv_eq, inl_isoIsPushout_hom]
@[reassoc (attr := simp)]
theorem inr_isoIsPushout_inv (h : IsPushout f g inl inr) (h' : IsPushout f g inl' inr') :
    inr' ≫ (h.isoIsPushout _ _ h').inv = inr := by
  simp only [Iso.comp_inv_eq, inr_isoIsPushout_hom]
end
variable {X Y}
noncomputable def isoPushout (h : IsPushout f g inl inr) [HasPushout f g] : P ≅ pushout f g :=
  (colimit.isoColimitCocone ⟨_, h.isColimit⟩).symm
@[reassoc (attr := simp)]
theorem inl_isoPushout_inv (h : IsPushout f g inl inr) [HasPushout f g] :
    pushout.inl _ _ ≫ h.isoPushout.inv = inl := by
  dsimp [isoPushout, cocone, CommSq.cocone]
  simp
@[reassoc (attr := simp)]
theorem inr_isoPushout_inv (h : IsPushout f g inl inr) [HasPushout f g] :
    pushout.inr _ _ ≫ h.isoPushout.inv = inr := by
  dsimp [isoPushout, cocone, CommSq.cocone]
  simp
@[reassoc (attr := simp)]
theorem inl_isoPushout_hom (h : IsPushout f g inl inr) [HasPushout f g] :
    inl ≫ h.isoPushout.hom = pushout.inl _ _ := by simp [← Iso.eq_comp_inv]
@[reassoc (attr := simp)]
theorem inr_isoPushout_hom (h : IsPushout f g inl inr) [HasPushout f g] :
    inr ≫ h.isoPushout.hom = pushout.inr _ _ := by simp [← Iso.eq_comp_inv]
theorem of_iso_pushout (h : CommSq f g inl inr) [HasPushout f g] (i : P ≅ pushout f g)
    (w₁ : inl ≫ i.hom = pushout.inl _ _) (w₂ : inr ≫ i.hom = pushout.inr _ _) :
      IsPushout f g inl inr :=
  of_isColimit' h
    (Limits.IsColimit.ofIsoColimit (colimit.isColimit _)
      (PushoutCocone.ext (s := PushoutCocone.mk ..) i w₁ w₂).symm)
lemma of_iso (h : IsPushout f g inl inr)
    {Z' X' Y' P' : C} {f' : Z' ⟶ X'} {g' : Z' ⟶ Y'} {inl' : X' ⟶ P'} {inr' : Y' ⟶ P'}
    (e₁ : Z ≅ Z') (e₂ : X ≅ X') (e₃ : Y ≅ Y') (e₄ : P ≅ P')
    (commf : f ≫ e₂.hom = e₁.hom ≫ f')
    (commg : g ≫ e₃.hom = e₁.hom ≫ g')
    (comminl : inl ≫ e₄.hom = e₂.hom ≫ inl')
    (comminr : inr ≫ e₄.hom = e₃.hom ≫ inr') :
    IsPushout f' g' inl' inr' where
  w := by
    rw [← cancel_epi e₁.hom, ← reassoc_of% commf, ← comminl,
      ← reassoc_of% commg, ← comminr, h.w_assoc]
  isColimit' :=
    ⟨(IsColimit.precomposeHomEquiv
        (spanExt e₁ e₂ e₃ commf.symm commg.symm) _).1
          (IsColimit.ofIsoColimit h.isColimit
            (PushoutCocone.ext e₄ comminl comminr))⟩
section
variable {P X Y : C} {inl : X ⟶ P} {inr : X ⟶ P} {f : Y ⟶ X} [Epi f]
lemma isIso_inl_iso_of_epi (h : IsPushout f f inl inr) : IsIso inl :=
  h.cocone.isIso_inl_of_epi_of_isColimit h.isColimit
lemma isIso_inr_iso_of_epi (h : IsPushout f f inl inr) : IsIso inr :=
  h.cocone.isIso_inr_of_epi_of_isColimit h.isColimit
end
end IsPushout
namespace IsPullback
variable {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
theorem flip (h : IsPullback fst snd f g) : IsPullback snd fst g f :=
  of_isLimit (PullbackCone.flipIsLimit h.isLimit)
theorem flip_iff : IsPullback fst snd f g ↔ IsPullback snd fst g f :=
  ⟨flip, flip⟩
section
variable [HasZeroObject C] [HasZeroMorphisms C]
open ZeroObject
@[simp]
theorem zero_left (X : C) : IsPullback (0 : 0 ⟶ X) (0 : (0 : C) ⟶ 0) (𝟙 X) (0 : 0 ⟶ X) :=
  { w := by simp
    isLimit' :=
      ⟨{  lift := fun _ => 0
          fac := fun s => by
            simpa [eq_iff_true_of_subsingleton] using
              @PullbackCone.equalizer_ext _ _ _ _ _ _ _ s _ 0 (𝟙 _)
                (by simpa using (PullbackCone.condition s).symm) }⟩ }
@[simp]
theorem zero_top (X : C) : IsPullback (0 : (0 : C) ⟶ 0) (0 : 0 ⟶ X) (0 : 0 ⟶ X) (𝟙 X) :=
  (zero_left X).flip
@[simp]
theorem zero_right (X : C) : IsPullback (0 : X ⟶ 0) (𝟙 X) (0 : (0 : C) ⟶ 0) (0 : X ⟶ 0) :=
  of_iso_pullback (by simp) ((zeroProdIso X).symm ≪≫ (pullbackZeroZeroIso _ _).symm)
    (by simp [eq_iff_true_of_subsingleton]) (by simp)
@[simp]
theorem zero_bot (X : C) : IsPullback (𝟙 X) (0 : X ⟶ 0) (0 : X ⟶ 0) (0 : (0 : C) ⟶ 0) :=
  (zero_right X).flip
end
theorem paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
    (s : IsPullback h₁₁ v₁₁ v₁₂ h₂₁) (t : IsPullback h₂₁ v₂₁ v₂₂ h₃₁) :
    IsPullback h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁ :=
  of_isLimit (pasteHorizIsPullback rfl t.isLimit s.isLimit)
theorem paste_horiz {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃}
    {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPullback h₁₁ v₁₁ v₁₂ h₂₁) (t : IsPullback h₁₂ v₁₂ v₁₃ h₂₂) :
    IsPullback (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂) :=
  (paste_vert s.flip t.flip).flip
theorem of_bot {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂}
    {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
    (s : IsPullback h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁) (p : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁)
    (t : IsPullback h₂₁ v₂₁ v₂₂ h₃₁) : IsPullback h₁₁ v₁₁ v₁₂ h₂₁ :=
  of_isLimit (leftSquareIsPullback (PullbackCone.mk h₁₁ _ p) rfl t.isLimit s.isLimit)
theorem of_right {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPullback (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂)) (p : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁)
    (t : IsPullback h₁₂ v₁₂ v₁₃ h₂₂) : IsPullback h₁₁ v₁₁ v₁₂ h₂₁ :=
  (of_bot s.flip p.symm t.flip).flip
theorem paste_vert_iff {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
    (s : IsPullback h₂₁ v₂₁ v₂₂ h₃₁) (e : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁) :
    IsPullback h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁ ↔ IsPullback h₁₁ v₁₁ v₁₂ h₂₁ :=
  ⟨fun h => h.of_bot e s, fun h => h.paste_vert s⟩
theorem paste_horiz_iff {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃}
    {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPullback h₁₂ v₁₂ v₁₃ h₂₂) (e : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁) :
    IsPullback (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂) ↔ IsPullback h₁₁ v₁₁ v₁₂ h₂₁ :=
  ⟨fun h => h.of_right e s, fun h => h.paste_horiz s⟩
theorem of_right' {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₂₂ : X₂₂ ⟶ X₂₃} {h₁₃ : X₁₁ ⟶ X₁₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPullback h₁₃ v₁₁ v₁₃ (h₂₁ ≫ h₂₂)) (t : IsPullback h₁₂ v₁₂ v₁₃ h₂₂) :
    IsPullback (t.lift h₁₃ (v₁₁ ≫ h₂₁) (by rw [s.w, Category.assoc])) v₁₁ v₁₂ h₂₁ :=
  of_right ((t.lift_fst _ _ _) ▸ s) (t.lift_snd _ _ _) t
theorem of_bot' {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₃₁ : X₃₁ ⟶ X₃₂} {v₃₁ : X₁₁ ⟶ X₃₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
    (s : IsPullback h₁₁ v₃₁ (v₁₂ ≫ v₂₂) h₃₁) (t : IsPullback h₂₁ v₂₁ v₂₂ h₃₁) :
    IsPullback h₁₁ (t.lift (h₁₁ ≫ v₁₂) v₃₁ (by rw [Category.assoc, s.w])) v₁₂ h₂₁ :=
  of_bot ((t.lift_snd _ _ _) ▸ s) (by simp only [lift_fst]) t
section
variable [HasZeroObject C] [HasZeroMorphisms C]
open ZeroObject
theorem of_isBilimit {b : BinaryBicone X Y} (h : b.IsBilimit) :
    IsPullback b.fst b.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) := by
  convert IsPullback.of_is_product' h.isLimit HasZeroObject.zeroIsTerminal
    <;> subsingleton
@[simp]
theorem of_has_biproduct (X Y : C) [HasBinaryBiproduct X Y] :
    IsPullback biprod.fst biprod.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) :=
  of_isBilimit (BinaryBiproduct.isBilimit X Y)
theorem inl_snd' {b : BinaryBicone X Y} (h : b.IsBilimit) :
    IsPullback b.inl (0 : X ⟶ 0) b.snd (0 : 0 ⟶ Y) := by
  refine of_right ?_ (by simp) (of_isBilimit h)
  simp
@[simp]
theorem inl_snd (X Y : C) [HasBinaryBiproduct X Y] :
    IsPullback biprod.inl (0 : X ⟶ 0) biprod.snd (0 : 0 ⟶ Y) :=
  inl_snd' (BinaryBiproduct.isBilimit X Y)
theorem inr_fst' {b : BinaryBicone X Y} (h : b.IsBilimit) :
    IsPullback b.inr (0 : Y ⟶ 0) b.fst (0 : 0 ⟶ X) := by
  apply flip
  refine of_bot ?_ (by simp) (of_isBilimit h)
  simp
@[simp]
theorem inr_fst (X Y : C) [HasBinaryBiproduct X Y] :
    IsPullback biprod.inr (0 : Y ⟶ 0) biprod.fst (0 : 0 ⟶ X) :=
  inr_fst' (BinaryBiproduct.isBilimit X Y)
theorem of_is_bilimit' {b : BinaryBicone X Y} (h : b.IsBilimit) :
    IsPullback (0 : 0 ⟶ X) (0 : 0 ⟶ Y) b.inl b.inr := by
  refine IsPullback.of_right ?_ (by simp) (IsPullback.inl_snd' h).flip
  simp
theorem of_hasBinaryBiproduct (X Y : C) [HasBinaryBiproduct X Y] :
    IsPullback (0 : 0 ⟶ X) (0 : 0 ⟶ Y) biprod.inl biprod.inr :=
  of_is_bilimit' (BinaryBiproduct.isBilimit X Y)
instance hasPullback_biprod_fst_biprod_snd [HasBinaryBiproduct X Y] :
    HasPullback (biprod.inl : X ⟶ _) (biprod.inr : Y ⟶ _) :=
  HasLimit.mk ⟨_, (of_hasBinaryBiproduct X Y).isLimit⟩
def pullbackBiprodInlBiprodInr [HasBinaryBiproduct X Y] :
    pullback (biprod.inl : X ⟶ _) (biprod.inr : Y ⟶ _) ≅ 0 :=
  limit.isoLimitCone ⟨_, (of_hasBinaryBiproduct X Y).isLimit⟩
end
theorem op (h : IsPullback fst snd f g) : IsPushout g.op f.op snd.op fst.op :=
  IsPushout.of_isColimit
    (IsColimit.ofIsoColimit (Limits.PullbackCone.isLimitEquivIsColimitOp h.flip.cone h.flip.isLimit)
      h.toCommSq.flip.coneOp)
theorem unop {P X Y Z : Cᵒᵖ} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) : IsPushout g.unop f.unop snd.unop fst.unop :=
  IsPushout.of_isColimit
    (IsColimit.ofIsoColimit
      (Limits.PullbackCone.isLimitEquivIsColimitUnop h.flip.cone h.flip.isLimit)
      h.toCommSq.flip.coneUnop)
theorem of_vert_isIso [IsIso snd] [IsIso f] (sq : CommSq fst snd f g) : IsPullback fst snd f g :=
  IsPullback.flip (of_horiz_isIso sq.flip)
lemma of_id_fst : IsPullback (𝟙 _) f f (𝟙 _) := IsPullback.of_horiz_isIso ⟨by simp⟩
lemma of_id_snd : IsPullback f (𝟙 _) (𝟙 _) f := IsPullback.of_vert_isIso ⟨by simp⟩
lemma id_vert (f : X ⟶ Z) : IsPullback f (𝟙 X) (𝟙 Z) f :=
  of_vert_isIso ⟨by simp only [Category.id_comp, Category.comp_id]⟩
lemma id_horiz (f : X ⟶ Z) : IsPullback (𝟙 X) f f (𝟙 Z) :=
  of_horiz_isIso ⟨by simp only [Category.id_comp, Category.comp_id]⟩
end IsPullback
namespace IsPushout
variable {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
theorem flip (h : IsPushout f g inl inr) : IsPushout g f inr inl :=
  of_isColimit (PushoutCocone.flipIsColimit h.isColimit)
theorem flip_iff : IsPushout f g inl inr ↔ IsPushout g f inr inl :=
  ⟨flip, flip⟩
section
variable [HasZeroObject C] [HasZeroMorphisms C]
open ZeroObject
@[simp]
theorem zero_right (X : C) : IsPushout (0 : X ⟶ 0) (𝟙 X) (0 : (0 : C) ⟶ 0) (0 : X ⟶ 0) :=
  { w := by simp
    isColimit' :=
      ⟨{  desc := fun _ => 0
          fac := fun s => by
            have c :=
              @PushoutCocone.coequalizer_ext _ _ _ _ _ _ _ s _ 0 (𝟙 _)
                (by simp [eq_iff_true_of_subsingleton]) (by simpa using PushoutCocone.condition s)
            dsimp at c
            simpa using c }⟩ }
@[simp]
theorem zero_bot (X : C) : IsPushout (𝟙 X) (0 : X ⟶ 0) (0 : X ⟶ 0) (0 : (0 : C) ⟶ 0) :=
  (zero_right X).flip
@[simp]
theorem zero_left (X : C) : IsPushout (0 : 0 ⟶ X) (0 : (0 : C) ⟶ 0) (𝟙 X) (0 : 0 ⟶ X) :=
  of_iso_pushout (by simp) ((coprodZeroIso X).symm ≪≫ (pushoutZeroZeroIso _ _).symm) (by simp)
    (by simp [eq_iff_true_of_subsingleton])
@[simp]
theorem zero_top (X : C) : IsPushout (0 : (0 : C) ⟶ 0) (0 : 0 ⟶ X) (0 : 0 ⟶ X) (𝟙 X) :=
  (zero_left X).flip
end
theorem paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
    (s : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) (t : IsPushout h₂₁ v₂₁ v₂₂ h₃₁) :
    IsPushout h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁ :=
  of_isColimit (pasteHorizIsPushout rfl s.isColimit t.isColimit)
theorem paste_horiz {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃}
    {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) (t : IsPushout h₁₂ v₁₂ v₁₃ h₂₂) :
    IsPushout (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂) :=
  (paste_vert s.flip t.flip).flip
theorem of_top {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂}
    {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
    (s : IsPushout h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁) (p : h₂₁ ≫ v₂₂ = v₂₁ ≫ h₃₁)
    (t : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) : IsPushout h₂₁ v₂₁ v₂₂ h₃₁ :=
  of_isColimit <| rightSquareIsPushout
    (PushoutCocone.mk _ _ p) (cocone_inr _) t.isColimit s.isColimit
theorem of_left {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPushout (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂)) (p : h₁₂ ≫ v₁₃ = v₁₂ ≫ h₂₂)
    (t : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) : IsPushout h₁₂ v₁₂ v₁₃ h₂₂ :=
  (of_top s.flip p.symm t.flip).flip
theorem paste_vert_iff {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
    (s : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) (e : h₂₁ ≫ v₂₂ = v₂₁ ≫ h₃₁) :
    IsPushout h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁ ↔ IsPushout h₂₁ v₂₁ v₂₂ h₃₁ :=
  ⟨fun h => h.of_top e s, s.paste_vert⟩
theorem paste_horiz_iff {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃}
    {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) (e : h₁₂ ≫ v₁₃ = v₁₂ ≫ h₂₂) :
    IsPushout (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂) ↔ IsPushout h₁₂ v₁₂ v₁₃ h₂₂ :=
  ⟨fun h => h.of_left e s, s.paste_horiz⟩
theorem of_top' {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂}
    {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₂ ⟶ X₃₂} {v₂₁ : X₂₁ ⟶ X₃₁}
    (s : IsPushout h₁₁ (v₁₁ ≫ v₂₁) v₁₃ h₃₁) (t : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) :
      IsPushout h₂₁ v₂₁ (t.desc v₁₃ (v₂₁ ≫ h₃₁) (by rw [s.w, Category.assoc])) h₃₁ :=
  of_top ((t.inl_desc _ _ _).symm ▸ s) (t.inr_desc _ _ _) t
theorem of_left' {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₂₃ : X₂₁ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPushout (h₁₁ ≫ h₁₂) v₁₁ v₁₃ h₂₃) (t : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) :
    IsPushout h₁₂ v₁₂ v₁₃ (t.desc (h₁₂ ≫ v₁₃) h₂₃ (by rw [← Category.assoc, s.w])) :=
  of_left ((t.inr_desc _ _ _).symm ▸ s) (by simp only [inl_desc]) t
section
variable [HasZeroObject C] [HasZeroMorphisms C]
open ZeroObject
theorem of_isBilimit {b : BinaryBicone X Y} (h : b.IsBilimit) :
    IsPushout (0 : 0 ⟶ X) (0 : 0 ⟶ Y) b.inl b.inr := by
  convert IsPushout.of_is_coproduct' h.isColimit HasZeroObject.zeroIsInitial
    <;> subsingleton
@[simp]
theorem of_has_biproduct (X Y : C) [HasBinaryBiproduct X Y] :
    IsPushout (0 : 0 ⟶ X) (0 : 0 ⟶ Y) biprod.inl biprod.inr :=
  of_isBilimit (BinaryBiproduct.isBilimit X Y)
theorem inl_snd' {b : BinaryBicone X Y} (h : b.IsBilimit) :
    IsPushout b.inl (0 : X ⟶ 0) b.snd (0 : 0 ⟶ Y) := by
  apply flip
  refine of_left ?_ (by simp) (of_isBilimit h)
  simp
theorem inl_snd (X Y : C) [HasBinaryBiproduct X Y] :
    IsPushout biprod.inl (0 : X ⟶ 0) biprod.snd (0 : 0 ⟶ Y) :=
  inl_snd' (BinaryBiproduct.isBilimit X Y)
theorem inr_fst' {b : BinaryBicone X Y} (h : b.IsBilimit) :
    IsPushout b.inr (0 : Y ⟶ 0) b.fst (0 : 0 ⟶ X) := by
  refine of_top ?_ (by simp) (of_isBilimit h)
  simp
theorem inr_fst (X Y : C) [HasBinaryBiproduct X Y] :
    IsPushout biprod.inr (0 : Y ⟶ 0) biprod.fst (0 : 0 ⟶ X) :=
  inr_fst' (BinaryBiproduct.isBilimit X Y)
theorem of_is_bilimit' {b : BinaryBicone X Y} (h : b.IsBilimit) :
    IsPushout b.fst b.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) := by
  refine IsPushout.of_left ?_ (by simp) (IsPushout.inl_snd' h)
  simp
theorem of_hasBinaryBiproduct (X Y : C) [HasBinaryBiproduct X Y] :
    IsPushout biprod.fst biprod.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) :=
  of_is_bilimit' (BinaryBiproduct.isBilimit X Y)
instance hasPushout_biprod_fst_biprod_snd [HasBinaryBiproduct X Y] :
    HasPushout (biprod.fst : _ ⟶ X) (biprod.snd : _ ⟶ Y) :=
  HasColimit.mk ⟨_, (of_hasBinaryBiproduct X Y).isColimit⟩
def pushoutBiprodFstBiprodSnd [HasBinaryBiproduct X Y] :
    pushout (biprod.fst : _ ⟶ X) (biprod.snd : _ ⟶ Y) ≅ 0 :=
  colimit.isoColimitCocone ⟨_, (of_hasBinaryBiproduct X Y).isColimit⟩
end
theorem op (h : IsPushout f g inl inr) : IsPullback inr.op inl.op g.op f.op :=
  IsPullback.of_isLimit
    (IsLimit.ofIsoLimit
      (Limits.PushoutCocone.isColimitEquivIsLimitOp h.flip.cocone h.flip.isColimit)
      h.toCommSq.flip.coconeOp)
theorem unop {Z X Y P : Cᵒᵖ} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
    (h : IsPushout f g inl inr) : IsPullback inr.unop inl.unop g.unop f.unop :=
  IsPullback.of_isLimit
    (IsLimit.ofIsoLimit
      (Limits.PushoutCocone.isColimitEquivIsLimitUnop h.flip.cocone h.flip.isColimit)
      h.toCommSq.flip.coconeUnop)
theorem of_horiz_isIso [IsIso f] [IsIso inr] (sq : CommSq f g inl inr) : IsPushout f g inl inr :=
  of_isColimit' sq
    (by
      refine
        PushoutCocone.IsColimit.mk _ (fun s => inv inr ≫ s.inr) (fun s => ?_)
          (by aesop_cat) (by aesop_cat)
      simp only [← cancel_epi f, s.condition, sq.w_assoc, IsIso.hom_inv_id_assoc])
theorem of_vert_isIso [IsIso g] [IsIso inl] (sq : CommSq f g inl inr) : IsPushout f g inl inr :=
  (of_horiz_isIso sq.flip).flip
lemma of_id_fst : IsPushout (𝟙 _) f f (𝟙 _) := IsPushout.of_horiz_isIso ⟨by simp⟩
lemma of_id_snd : IsPushout f (𝟙 _) (𝟙 _) f := IsPushout.of_vert_isIso ⟨by simp⟩
lemma id_vert (f : X ⟶ Z) : IsPushout f (𝟙 X) (𝟙 Z) f :=
  of_vert_isIso ⟨by simp only [Category.id_comp, Category.comp_id]⟩
lemma id_horiz (f : X ⟶ Z) : IsPushout (𝟙 X) f f (𝟙 Z) :=
  of_horiz_isIso ⟨by simp only [Category.id_comp, Category.comp_id]⟩
end IsPushout
section Equalizer
variable {X Y Z : C} {f f' : X ⟶ Y} {g g' : Y ⟶ Z}
noncomputable def IsPullback.isLimitFork (H : IsPullback f f g g') : IsLimit (Fork.ofι f H.w) := by
  fapply Fork.IsLimit.mk
  · exact fun s => H.isLimit.lift (PullbackCone.mk s.ι s.ι s.condition)
  · exact fun s => H.isLimit.fac _ WalkingCospan.left
  · intro s m e
    apply PullbackCone.IsLimit.hom_ext H.isLimit <;> refine e.trans ?_ <;> symm <;>
      exact H.isLimit.fac _ _
noncomputable def IsPushout.isLimitFork (H : IsPushout f f' g g) :
    IsColimit (Cofork.ofπ g H.w) := by
  fapply Cofork.IsColimit.mk
  · exact fun s => H.isColimit.desc (PushoutCocone.mk s.π s.π s.condition)
  · exact fun s => H.isColimit.fac _ WalkingSpan.left
  · intro s m e
    apply PushoutCocone.IsColimit.hom_ext H.isColimit <;> refine e.trans ?_ <;> symm <;>
      exact H.isColimit.fac _ _
end Equalizer
namespace BicartesianSq
variable {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
theorem of_isPullback_isPushout (p₁ : IsPullback f g h i) (p₂ : IsPushout f g h i) :
    BicartesianSq f g h i :=
  BicartesianSq.mk p₁ p₂.isColimit'
theorem flip (p : BicartesianSq f g h i) : BicartesianSq g f i h :=
  of_isPullback_isPushout p.toIsPullback.flip p.toIsPushout.flip
variable [HasZeroObject C] [HasZeroMorphisms C]
open ZeroObject
theorem of_is_biproduct₁ {b : BinaryBicone X Y} (h : b.IsBilimit) :
    BicartesianSq b.fst b.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) :=
  of_isPullback_isPushout (IsPullback.of_isBilimit h) (IsPushout.of_is_bilimit' h)
theorem of_is_biproduct₂ {b : BinaryBicone X Y} (h : b.IsBilimit) :
    BicartesianSq (0 : 0 ⟶ X) (0 : 0 ⟶ Y) b.inl b.inr :=
  of_isPullback_isPushout (IsPullback.of_is_bilimit' h) (IsPushout.of_isBilimit h)
@[simp]
theorem of_has_biproduct₁ [HasBinaryBiproduct X Y] :
    BicartesianSq biprod.fst biprod.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) := by
  convert of_is_biproduct₁ (BinaryBiproduct.isBilimit X Y)
@[simp]
theorem of_has_biproduct₂ [HasBinaryBiproduct X Y] :
    BicartesianSq (0 : 0 ⟶ X) (0 : 0 ⟶ Y) biprod.inl biprod.inr := by
  convert of_is_biproduct₂ (BinaryBiproduct.isBilimit X Y)
end BicartesianSq
section Functor
variable {D : Type u₂} [Category.{v₂} D]
variable (F : C ⥤ D) {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
theorem Functor.map_isPullback [PreservesLimit (cospan h i) F] (s : IsPullback f g h i) :
    IsPullback (F.map f) (F.map g) (F.map h) (F.map i) := by
  refine
    IsPullback.of_isLimit' (F.map_commSq s.toCommSq)
      (IsLimit.equivOfNatIsoOfIso (cospanCompIso F h i) _ _ (WalkingCospan.ext ?_ ?_ ?_)
        (isLimitOfPreserves F s.isLimit))
  · rfl
  · simp
  · simp
theorem Functor.map_isPushout [PreservesColimit (span f g) F] (s : IsPushout f g h i) :
    IsPushout (F.map f) (F.map g) (F.map h) (F.map i) := by
  refine
    IsPushout.of_isColimit' (F.map_commSq s.toCommSq)
      (IsColimit.equivOfNatIsoOfIso (spanCompIso F f g) _ _ (WalkingSpan.ext ?_ ?_ ?_)
        (isColimitOfPreserves F s.isColimit))
  · rfl
  · simp
  · simp
alias IsPullback.map := Functor.map_isPullback
alias IsPushout.map := Functor.map_isPushout
theorem IsPullback.of_map [ReflectsLimit (cospan h i) F] (e : f ≫ h = g ≫ i)
    (H : IsPullback (F.map f) (F.map g) (F.map h) (F.map i)) : IsPullback f g h i := by
  refine ⟨⟨e⟩, ⟨isLimitOfReflects F <| ?_⟩⟩
  refine
    (IsLimit.equivOfNatIsoOfIso (cospanCompIso F h i) _ _ (WalkingCospan.ext ?_ ?_ ?_)).symm
      H.isLimit
  exacts [Iso.refl _, (Category.comp_id _).trans (Category.id_comp _).symm,
    (Category.comp_id _).trans (Category.id_comp _).symm]
theorem IsPullback.of_map_of_faithful [ReflectsLimit (cospan h i) F] [F.Faithful]
    (H : IsPullback (F.map f) (F.map g) (F.map h) (F.map i)) : IsPullback f g h i :=
  H.of_map F (F.map_injective <| by simpa only [F.map_comp] using H.w)
theorem IsPullback.map_iff {D : Type*} [Category D] (F : C ⥤ D) [PreservesLimit (cospan h i) F]
    [ReflectsLimit (cospan h i) F] (e : f ≫ h = g ≫ i) :
    IsPullback (F.map f) (F.map g) (F.map h) (F.map i) ↔ IsPullback f g h i :=
  ⟨fun h => h.of_map F e, fun h => h.map F⟩
theorem IsPushout.of_map [ReflectsColimit (span f g) F] (e : f ≫ h = g ≫ i)
    (H : IsPushout (F.map f) (F.map g) (F.map h) (F.map i)) : IsPushout f g h i := by
  refine ⟨⟨e⟩, ⟨isColimitOfReflects F <| ?_⟩⟩
  refine
    (IsColimit.equivOfNatIsoOfIso (spanCompIso F f g) _ _ (WalkingSpan.ext ?_ ?_ ?_)).symm
      H.isColimit
  exacts [Iso.refl _, (Category.comp_id _).trans (Category.id_comp _),
    (Category.comp_id _).trans (Category.id_comp _)]
theorem IsPushout.of_map_of_faithful [ReflectsColimit (span f g) F] [F.Faithful]
    (H : IsPushout (F.map f) (F.map g) (F.map h) (F.map i)) : IsPushout f g h i :=
  H.of_map F (F.map_injective <| by simpa only [F.map_comp] using H.w)
theorem IsPushout.map_iff {D : Type*} [Category D] (F : C ⥤ D) [PreservesColimit (span f g) F]
    [ReflectsColimit (span f g) F] (e : f ≫ h = g ≫ i) :
    IsPushout (F.map f) (F.map g) (F.map h) (F.map i) ↔ IsPushout f g h i :=
  ⟨fun h => h.of_map F e, fun h => h.map F⟩
end Functor
end CategoryTheory