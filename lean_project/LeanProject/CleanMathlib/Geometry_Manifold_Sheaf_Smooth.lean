import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.Sheaf.Basic
noncomputable section
open TopologicalSpace Opposite
local notation "∞" => (⊤ : ℕ∞)
universe u
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] (IM : ModelWithCorners 𝕜 EM HM)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E H')
  (M : Type u) [TopologicalSpace M] [ChartedSpace HM M]
  (N G A A' R : Type u) [TopologicalSpace N] [ChartedSpace H N]
  [TopologicalSpace G] [ChartedSpace H G] [TopologicalSpace A] [ChartedSpace H A]
  [TopologicalSpace A'] [ChartedSpace H' A'] [TopologicalSpace R] [ChartedSpace H R]
section TypeCat
def smoothSheaf : TopCat.Sheaf (Type u) (TopCat.of M) :=
  (contDiffWithinAt_localInvariantProp (I := IM) (I' := I) ⊤).sheaf M N
variable {M}
instance smoothSheaf.coeFun (U : (Opens (TopCat.of M))ᵒᵖ) :
    CoeFun ((smoothSheaf IM I M N).presheaf.obj U) (fun _ ↦ ↑(unop U) → N) :=
  (contDiffWithinAt_localInvariantProp ⊤).sheafHasCoeToFun _ _ _
open Manifold in
lemma smoothSheaf.obj_eq (U : (Opens (TopCat.of M))ᵒᵖ) :
    (smoothSheaf IM I M N).presheaf.obj U = C^∞⟮IM, (unop U : Opens M); I, N⟯ := rfl
def smoothSheaf.eval (x : M) : (smoothSheaf IM I M N).presheaf.stalk x → N :=
  TopCat.stalkToFiber (StructureGroupoid.LocalInvariantProp.localPredicate M N _) x
def smoothSheaf.evalHom (x : TopCat.of M) : (smoothSheaf IM I M N).presheaf.stalk x ⟶ N :=
  TopCat.stalkToFiber (StructureGroupoid.LocalInvariantProp.localPredicate M N _) x
open CategoryTheory Limits
def smoothSheaf.evalAt (x : TopCat.of M) (U : OpenNhds x)
    (i : (smoothSheaf IM I M N).presheaf.obj (Opposite.op U.obj)) : N :=
  i.1 ⟨x, U.2⟩
@[simp, reassoc, elementwise] lemma smoothSheaf.ι_evalHom (x : TopCat.of M) (U) :
    colimit.ι ((OpenNhds.inclusion x).op ⋙ (smoothSheaf IM I M N).val) U ≫
    smoothSheaf.evalHom IM I N x =
    smoothSheaf.evalAt _ _ _ _ _ :=
  colimit.ι_desc _ _
lemma smoothSheaf.eval_surjective (x : M) : Function.Surjective (smoothSheaf.eval IM I N x) := by
  apply TopCat.stalkToFiber_surjective
  intro n
  exact ⟨⊤, fun _ ↦ n, contMDiff_const, rfl⟩
instance [Nontrivial N] (x : M) : Nontrivial ((smoothSheaf IM I M N).presheaf.stalk x) :=
  (smoothSheaf.eval_surjective IM I N x).nontrivial
variable {IM I N}
@[simp] lemma smoothSheaf.eval_germ (U : Opens M) (x : M) (hx : x ∈ U)
    (f : (smoothSheaf IM I M N).presheaf.obj (op U)) :
    smoothSheaf.eval IM I N (x : M) ((smoothSheaf IM I M N).presheaf.germ U x hx f) = f ⟨x, hx⟩ :=
  TopCat.stalkToFiber_germ ((contDiffWithinAt_localInvariantProp ⊤).localPredicate M N) _ _ _ _
lemma smoothSheaf.contMDiff_section {U : (Opens (TopCat.of M))ᵒᵖ}
    (f : (smoothSheaf IM I M N).presheaf.obj U) :
    ContMDiff IM I ⊤ f :=
  (contDiffWithinAt_localInvariantProp ⊤).section_spec _ _ _ _
@[deprecated (since := "2024-11-21")]
alias smoothSheaf.smooth_section := smoothSheaf.contMDiff_section
end TypeCat
section LieGroup
variable [Group G] [LieGroup I G]
open Manifold in
@[to_additive]
noncomputable instance (U : (Opens (TopCat.of M))ᵒᵖ) :
    Group ((smoothSheaf IM I M G).presheaf.obj U) :=
  (SmoothMap.group : Group C^∞⟮IM, (unop U : Opens M); I, G⟯)
@[to_additive "The presheaf of smooth functions from `M` to `G`, for `G` an additive Lie group, as a
presheaf of additive groups."]
noncomputable def smoothPresheafGroup : TopCat.Presheaf Grp.{u} (TopCat.of M) :=
  { obj := fun U ↦ Grp.of ((smoothSheaf IM I M G).presheaf.obj U)
    map := fun h ↦ Grp.ofHom <|
      SmoothMap.restrictMonoidHom IM I G <| CategoryTheory.leOfHom h.unop
    map_id := fun _ ↦ rfl
    map_comp := fun _ _ ↦ rfl }
@[to_additive "The sheaf of smooth functions from `M` to `G`, for `G` an additive Lie group, as a
sheaf of additive groups."]
noncomputable def smoothSheafGroup : TopCat.Sheaf Grp.{u} (TopCat.of M) :=
  { val := smoothPresheafGroup IM I M G
    cond := by
      rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget Grp)]
      exact CategoryTheory.Sheaf.cond (smoothSheaf IM I M G) }
end LieGroup
section CommLieGroup
variable [CommGroup A] [CommGroup A'] [LieGroup I A] [LieGroup I' A']
open Manifold in
@[to_additive] noncomputable instance (U : (Opens (TopCat.of M))ᵒᵖ) :
    CommGroup ((smoothSheaf IM I M A).presheaf.obj U) :=
  (SmoothMap.commGroup : CommGroup C^∞⟮IM, (unop U : Opens M); I, A⟯)
@[to_additive "The presheaf of smooth functions from `M` to `A`, for `A` an additive abelian Lie
group, as a presheaf of additive abelian groups."]
noncomputable def smoothPresheafCommGroup : TopCat.Presheaf CommGrp.{u} (TopCat.of M) :=
  { obj := fun U ↦ CommGrp.of ((smoothSheaf IM I M A).presheaf.obj U)
    map := fun h ↦ CommGrp.ofHom <|
      SmoothMap.restrictMonoidHom IM I A <| CategoryTheory.leOfHom h.unop
    map_id := fun _ ↦ rfl
    map_comp := fun _ _ ↦ rfl }
@[to_additive "The sheaf of smooth functions from `M` to
`A`, for `A` an abelian additive Lie group, as a sheaf of abelian additive groups."]
noncomputable def smoothSheafCommGroup : TopCat.Sheaf CommGrp.{u} (TopCat.of M) :=
  { val := smoothPresheafCommGroup IM I M A
    cond := by
      rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
        (CategoryTheory.forget CommGrp)]
      exact CategoryTheory.Sheaf.cond (smoothSheaf IM I M A) }
@[to_additive "For a manifold `M` and a smooth homomorphism `φ` between abelian additive Lie groups
`A`, `A'`, the 'left-composition-by-`φ`' morphism of sheaves from `smoothSheafAddCommGroup IM I M A`
to `smoothSheafAddCommGroup IM I' M A'`."]
def smoothSheafCommGroup.compLeft (φ : A →* A') (hφ : ContMDiff I I' ⊤ φ) :
    smoothSheafCommGroup IM I M A ⟶ smoothSheafCommGroup IM I' M A' :=
  CategoryTheory.Sheaf.Hom.mk <|
  { app := fun _ ↦ CommGrp.ofHom <| SmoothMap.compLeftMonoidHom _ _ φ hφ
    naturality := fun _ _ _ ↦ rfl }
end CommLieGroup
section SmoothRing
variable [Ring R] [SmoothRing I R]
open Manifold in
instance (U : (Opens (TopCat.of M))ᵒᵖ) : Ring ((smoothSheaf IM I M R).presheaf.obj U) :=
  (SmoothMap.ring : Ring C^∞⟮IM, (unop U : Opens M); I, R⟯)
def smoothPresheafRing : TopCat.Presheaf RingCat.{u} (TopCat.of M) :=
  { obj := fun U ↦ RingCat.of ((smoothSheaf IM I M R).presheaf.obj U)
    map := fun h ↦ RingCat.ofHom <|
      SmoothMap.restrictRingHom IM I R <| CategoryTheory.leOfHom h.unop
    map_id := fun _ ↦ rfl
    map_comp := fun _ _ ↦ rfl }
def smoothSheafRing : TopCat.Sheaf RingCat.{u} (TopCat.of M) :=
  { val := smoothPresheafRing IM I M R
    cond := by
      rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget RingCat)]
      exact CategoryTheory.Sheaf.cond (smoothSheaf IM I M R) }
end SmoothRing
section SmoothCommRing
variable [CommRing R] [SmoothRing I R]
open Manifold in
instance (U : (Opens (TopCat.of M))ᵒᵖ) : CommRing ((smoothSheaf IM I M R).presheaf.obj U) :=
  (SmoothMap.commRing : CommRing C^∞⟮IM, (unop U : Opens M); I, R⟯)
def smoothPresheafCommRing : TopCat.Presheaf CommRingCat.{u} (TopCat.of M) :=
  { obj := fun U ↦ CommRingCat.of ((smoothSheaf IM I M R).presheaf.obj U)
    map := fun h ↦ CommRingCat.ofHom <|
      SmoothMap.restrictRingHom IM I R <| CategoryTheory.leOfHom h.unop
    map_id := fun _ ↦ rfl
    map_comp := fun _ _ ↦ rfl }
def smoothSheafCommRing : TopCat.Sheaf CommRingCat.{u} (TopCat.of M) :=
  { val := smoothPresheafCommRing IM I M R
    cond := by
      rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
        (CategoryTheory.forget CommRingCat)]
      exact CategoryTheory.Sheaf.cond (smoothSheaf IM I M R) }
example : (CategoryTheory.sheafCompose _ (CategoryTheory.forget CommRingCat.{u})).obj
    (smoothSheafCommRing IM I M R) = (smoothSheaf IM I M R) := rfl
instance smoothSheafCommRing.coeFun (U : (Opens (TopCat.of M))ᵒᵖ) :
    CoeFun ((smoothSheafCommRing IM I M R).presheaf.obj U) (fun _ ↦ ↑(unop U) → R) :=
  (contDiffWithinAt_localInvariantProp ⊤).sheafHasCoeToFun _ _ _
open CategoryTheory Limits
def smoothSheafCommRing.forgetStalk (x : TopCat.of M) :
    (forget _).obj ((smoothSheafCommRing IM I M R).presheaf.stalk x) ≅
    (smoothSheaf IM I M R).presheaf.stalk x :=
  preservesColimitIso _ _
@[simp, reassoc, elementwise] lemma smoothSheafCommRing.ι_forgetStalk_hom (x : TopCat.of M) (U) :
    CategoryStruct.comp
      (Z := (smoothSheaf IM I M R).presheaf.stalk x)
      (DFunLike.coe
        (α := ((forget CommRingCat).obj ((smoothSheafCommRing IM I M R).presheaf.obj
          (op ((OpenNhds.inclusion x).obj U.unop)))))
        (colimit.ι ((OpenNhds.inclusion x).op ⋙ (smoothSheafCommRing IM I M R).presheaf) U))
      (forgetStalk IM I M R x).hom =
    colimit.ι ((OpenNhds.inclusion x).op ⋙ (smoothSheaf IM I M R).presheaf) U :=
  ι_preservesColimitIso_hom _ _ _
@[simp, reassoc, elementwise] lemma smoothSheafCommRing.ι_forgetStalk_inv (x : TopCat.of M) (U) :
    colimit.ι ((OpenNhds.inclusion x).op ⋙ (smoothSheaf IM I M R).presheaf) U ≫
    (smoothSheafCommRing.forgetStalk IM I M R x).inv =
    (forget CommRingCat).map
      (colimit.ι ((OpenNhds.inclusion x).op ⋙ (smoothSheafCommRing IM I M R).presheaf) U) := by
  rw [Iso.comp_inv_eq, ← smoothSheafCommRing.ι_forgetStalk_hom, CommRingCat.forget_map]
  simp_rw [Functor.comp_obj, Functor.op_obj]
def smoothSheafCommRing.evalAt (x : TopCat.of M) (U : OpenNhds x) :
    (smoothSheafCommRing IM I M R).presheaf.obj (Opposite.op U.1) ⟶ CommRingCat.of R :=
  SmoothMap.evalRingHom ⟨x, U.2⟩
def smoothSheafCommRing.evalHom (x : TopCat.of M) :
    (smoothSheafCommRing IM I M R).presheaf.stalk x ⟶ CommRingCat.of R := by
  refine CategoryTheory.Limits.colimit.desc _ ⟨_, ⟨fun U ↦ ?_, ?_⟩⟩
  · apply smoothSheafCommRing.evalAt
  · aesop_cat
def smoothSheafCommRing.eval (x : M) : (smoothSheafCommRing IM I M R).presheaf.stalk x →+* R :=
  smoothSheafCommRing.evalHom IM I M R x
@[simp, reassoc, elementwise] lemma smoothSheafCommRing.ι_evalHom (x : TopCat.of M) (U) :
    colimit.ι ((OpenNhds.inclusion x).op ⋙ _) U ≫ smoothSheafCommRing.evalHom IM I M R x =
    smoothSheafCommRing.evalAt _ _ _ _ _ _ :=
  colimit.ι_desc _ _
@[simp] lemma smoothSheafCommRing.evalHom_germ (U : Opens (TopCat.of M)) (x : M) (hx : x ∈ U)
    (f : (smoothSheafCommRing IM I M R).presheaf.obj (op U)) :
    smoothSheafCommRing.evalHom IM I M R (x : TopCat.of M)
      ((smoothSheafCommRing IM I M R).presheaf.germ U x hx f)
    = f ⟨x, hx⟩ :=
  congr_arg (fun a ↦ a f) <| smoothSheafCommRing.ι_evalHom IM I M R x ⟨U, hx⟩
@[simp, reassoc, elementwise] lemma smoothSheafCommRing.forgetStalk_inv_comp_eval
    (x : TopCat.of M) :
    (smoothSheafCommRing.forgetStalk IM I M R x).inv ≫
     (DFunLike.coe (smoothSheafCommRing.evalHom IM I M R x)) =
    smoothSheaf.evalHom _ _ _ _ := by
  apply Limits.colimit.hom_ext
  intro U
  show (colimit.ι _ U) ≫ _ = colimit.ι ((OpenNhds.inclusion x).op ⋙ _) U ≫ _
  rw [smoothSheafCommRing.ι_forgetStalk_inv_assoc]
  convert congr_arg (fun i ↦ (forget CommRingCat).map i) (smoothSheafCommRing.ι_evalHom ..)
  exact smoothSheaf.ι_evalHom IM I R x U
@[simp, reassoc, elementwise] lemma smoothSheafCommRing.forgetStalk_hom_comp_evalHom
    (x : TopCat.of M) :
    (smoothSheafCommRing.forgetStalk IM I M R x).hom ≫ (smoothSheaf.evalHom IM I R x) =
    (forget _).map (smoothSheafCommRing.evalHom _ _ _ _ _) := by
  simp_rw [← CategoryTheory.Iso.eq_inv_comp]
  rw [← smoothSheafCommRing.forgetStalk_inv_comp_eval]
  rfl
lemma smoothSheafCommRing.eval_surjective (x) :
    Function.Surjective (smoothSheafCommRing.eval IM I M R x) := by
  intro r
  obtain ⟨y, rfl⟩ := smoothSheaf.eval_surjective IM I R x r
  use (smoothSheafCommRing.forgetStalk IM I M R x).inv y
  apply smoothSheafCommRing.forgetStalk_inv_comp_eval_apply
instance [Nontrivial R] (x : M) : Nontrivial ((smoothSheafCommRing IM I M R).presheaf.stalk x) :=
  (smoothSheafCommRing.eval_surjective IM I M R x).nontrivial
variable {IM I M R}
@[simp] lemma smoothSheafCommRing.eval_germ (U : Opens M) (x : M) (hx : x ∈ U)
    (f : (smoothSheafCommRing IM I M R).presheaf.obj (op U)) :
    smoothSheafCommRing.eval IM I M R x ((smoothSheafCommRing IM I M R).presheaf.germ U x hx f)
    = f ⟨x, hx⟩ :=
  smoothSheafCommRing.evalHom_germ IM I M R U x hx f
end SmoothCommRing