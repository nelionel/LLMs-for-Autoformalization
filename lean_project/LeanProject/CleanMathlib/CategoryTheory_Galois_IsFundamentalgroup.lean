import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Galois.Topology
import Mathlib.CategoryTheory.Galois.Prorepresentability
import Mathlib.Topology.Algebra.OpenSubgroup
universe u₁ u₂ w
namespace CategoryTheory
namespace PreGaloisCategory
open Limits Functor
variable {C : Type u₁} [Category.{u₂} C] (F : C ⥤ FintypeCat.{w})
section
variable (G : Type*) [Group G] [∀ X, MulAction G (F.obj X)]
class IsNaturalSMul : Prop where
  naturality (g : G) {X Y : C} (f : X ⟶ Y) (x : F.obj X) : F.map f (g • x) = g • F.map f x
variable {G} in
@[simps!]
private def isoOnObj (g : G) (X : C) : F.obj X ≅ F.obj X :=
  FintypeCat.equivEquivIso <| {
    toFun := fun x ↦ g • x
    invFun := fun x ↦ g⁻¹ • x
    left_inv := fun _ ↦ by simp
    right_inv := fun _ ↦ by simp
  }
variable [IsNaturalSMul F G]
def toAut : G →* Aut F where
  toFun g := NatIso.ofComponents (isoOnObj F g) <| by
    intro X Y f
    ext
    simp [IsNaturalSMul.naturality]
  map_one' := by
    ext
    simp only [NatIso.ofComponents_hom_app, isoOnObj_hom, one_smul]
    rfl
  map_mul' := by
    intro g h
    ext X x
    simp only [NatIso.ofComponents_hom_app, isoOnObj_hom, mul_smul]
    rfl
variable {G} in
@[simp]
lemma toAut_hom_app_apply (g : G) {X : C} (x : F.obj X) : (toAut F G g).hom.app X x = g • x :=
  rfl
lemma toAut_injective_of_non_trivial (h : ∀ (g : G), (∀ (X : C) (x : F.obj X), g • x = x) → g = 1) :
    Function.Injective (toAut F G) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g (hg : toAut F G g = 1)
  refine h g (fun X x ↦ ?_)
  have : (toAut F G g).hom.app X = 𝟙 (F.obj X) := by
    rw [hg]
    rfl
  rw [← toAut_hom_app_apply, this, FintypeCat.id_apply]
variable [GaloisCategory C] [FiberFunctor F]
lemma toAut_continuous [TopologicalSpace G] [TopologicalGroup G]
    [∀ (X : C), ContinuousSMul G (F.obj X)] :
    Continuous (toAut F G) := by
  apply continuous_of_continuousAt_one
  rw [continuousAt_def, map_one]
  intro A hA
  obtain ⟨X, _, hX⟩ := ((nhds_one_has_basis_stabilizers F).mem_iff' A).mp hA
  rw [mem_nhds_iff]
  exact ⟨MulAction.stabilizer G X.pt, Set.preimage_mono (f := toAut F G) hX,
    stabilizer_isOpen G X.pt, one_mem _⟩
variable {G}
lemma action_ext_of_isGalois {t : F ⟶ F} {X : C} [IsGalois X] {g : G} (x : F.obj X)
    (hg : g • x = t.app X x) (y : F.obj X) : g • y = t.app X y := by
  obtain ⟨φ, (rfl : F.map φ.hom y = x)⟩ := MulAction.exists_smul_eq (Aut X) y x
  have : Function.Injective (F.map φ.hom) :=
    ConcreteCategory.injective_of_mono_of_preservesPullback (F.map φ.hom)
  apply this
  rw [IsNaturalSMul.naturality, hg, FunctorToFintypeCat.naturality]
variable (G)
lemma toAut_surjective_isGalois (t : Aut F) (X : C) [IsGalois X]
    [MulAction.IsPretransitive G (F.obj X)] :
    ∃ (g : G), ∀ (x : F.obj X), g • x = t.hom.app X x := by
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F X
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G a (t.hom.app X a)
  exact ⟨g, action_ext_of_isGalois F _ hg⟩
lemma toAut_surjective_isGalois_finite_family (t : Aut F) {ι : Type*} [Finite ι] (X : ι → C)
    [∀ i, IsGalois (X i)] (h : ∀ (X : C) [IsGalois X], MulAction.IsPretransitive G (F.obj X)) :
    ∃ (g : G), ∀ (i : ι) (x : F.obj (X i)), g • x = t.hom.app (X i) x := by
  let x (i : ι) : F.obj (X i) := (nonempty_fiber_of_isConnected F (X i)).some
  let P : C := ∏ᶜ X
  letI : Fintype ι := Fintype.ofFinite ι
  let is₁ : F.obj P ≅ ∏ᶜ fun i ↦ (F.obj (X i)) := PreservesProduct.iso F X
  let is₂ : (∏ᶜ fun i ↦ F.obj (X i) : FintypeCat) ≃ ∀ i, F.obj (X i) :=
    Limits.FintypeCat.productEquiv (fun i ↦ (F.obj (X i)))
  let px : F.obj P := is₁.inv (is₂.symm x)
  have hpx (i : ι) : F.map (Pi.π X i) px = x i := by
    simp only [px, is₁, is₂, ← piComparison_comp_π, ← PreservesProduct.iso_hom]
    simp only [FintypeCat.comp_apply, FintypeCat.inv_hom_id_apply,
      FintypeCat.productEquiv_symm_comp_π_apply]
  obtain ⟨A, f, a, _, hfa⟩ := exists_hom_from_galois_of_fiber F P px
  obtain ⟨g, hg⟩ := toAut_surjective_isGalois F G t A
  refine ⟨g, fun i y ↦ action_ext_of_isGalois F (x i) ?_ _⟩
  rw [← hpx i, ← IsNaturalSMul.naturality, FunctorToFintypeCat.naturality,
    ← hfa, FunctorToFintypeCat.naturality, ← IsNaturalSMul.naturality, hg]
open Pointwise
lemma toAut_surjective_of_isPretransitive [TopologicalSpace G] [TopologicalGroup G] [CompactSpace G]
    [∀ (X : C), ContinuousSMul G (F.obj X)]
    (h : ∀ (X : C) [IsGalois X], MulAction.IsPretransitive G (F.obj X)) :
    Function.Surjective (toAut F G) := by
  intro t
  choose gi hgi using (fun X : PointedGaloisObject F ↦ toAut_surjective_isGalois F G t X)
  let cl (X : PointedGaloisObject F) : Set G := gi X • MulAction.stabilizer G X.pt
  let c : Set G := ⋂ i, cl i
  have hne : c.Nonempty := by
    rw [← Set.univ_inter c]
    apply CompactSpace.isCompact_univ.inter_iInter_nonempty
    · intro X
      apply IsClosed.leftCoset
      exact Subgroup.isClosed_of_isOpen _ (stabilizer_isOpen G X.pt)
    · intro s
      rw [Set.univ_inter]
      obtain ⟨gs, hgs⟩ :=
        toAut_surjective_isGalois_finite_family F G t (fun X : s ↦ X.val.obj) h
      use gs
      simp only [Set.mem_iInter]
      intro X hXmem
      rw [mem_leftCoset_iff, SetLike.mem_coe, MulAction.mem_stabilizer_iff, mul_smul,
        hgs ⟨X, hXmem⟩, ← hgi X, inv_smul_smul]
  obtain ⟨g, hg⟩ := hne
  refine ⟨g, Iso.ext <| natTrans_ext_of_isGalois _ <| fun X _ ↦ ?_⟩
  ext x
  simp only [toAut_hom_app_apply]
  have : g ∈ (gi ⟨X, x, inferInstance⟩ • MulAction.stabilizer G x : Set G) := by
    simp only [Set.mem_iInter, c] at hg
    exact hg _
  obtain ⟨s, (hsmem : s • x = x), (rfl : gi ⟨X, x, inferInstance⟩ • s = _)⟩ := this
  rw [smul_eq_mul, mul_smul, hsmem]
  exact hgi ⟨X, x, inferInstance⟩ x
lemma isPretransitive_of_surjective (h : Function.Surjective (toAut F G)) (X : C)
    [IsConnected X] : MulAction.IsPretransitive G (F.obj X) where
  exists_smul_eq x y := by
    obtain ⟨t, ht⟩ := MulAction.exists_smul_eq (Aut F) x y
    obtain ⟨g, rfl⟩ := h t
    exact ⟨g, ht⟩
end
section
variable [GaloisCategory C]
variable (G : Type*) [Group G] [∀ (X : C), MulAction G (F.obj X)]
class IsFundamentalGroup [TopologicalSpace G] [TopologicalGroup G] [CompactSpace G]
    extends IsNaturalSMul F G : Prop where
  transitive_of_isGalois (X : C) [IsGalois X] : MulAction.IsPretransitive G (F.obj X)
  continuous_smul (X : C) : ContinuousSMul G (F.obj X)
  non_trivial' (g : G) : (∀ (X : C) (x : F.obj X), g • x = x) → g = 1
namespace IsFundamentalGroup
attribute [instance] continuous_smul transitive_of_isGalois
variable {G} [TopologicalSpace G] [TopologicalGroup G] [CompactSpace G] [IsFundamentalGroup F G]
lemma non_trivial (g : G) (h : ∀ (X : C) (x : F.obj X), g • x = x) : g = 1 :=
  IsFundamentalGroup.non_trivial' g h
end IsFundamentalGroup
variable [FiberFunctor F]
instance : IsFundamentalGroup F (Aut F) where
  naturality g _ _ f x := (FunctorToFintypeCat.naturality F F g.hom f x).symm
  transitive_of_isGalois X := FiberFunctor.isPretransitive_of_isConnected F X
  continuous_smul X := continuousSMul_aut_fiber F X
  non_trivial' g h := by
    ext X x
    exact h X x
variable [TopologicalSpace G] [TopologicalGroup G] [CompactSpace G] [IsFundamentalGroup F G]
lemma toAut_bijective : Function.Bijective (toAut F G) where
  left := toAut_injective_of_non_trivial F G IsFundamentalGroup.non_trivial'
  right := toAut_surjective_of_isPretransitive F G IsFundamentalGroup.transitive_of_isGalois
instance (X : C) [IsConnected X] : MulAction.IsPretransitive G (F.obj X) :=
  isPretransitive_of_surjective F G (toAut_bijective F G).surjective X
noncomputable def toAutMulEquiv : G ≃* Aut F :=
  MulEquiv.ofBijective (toAut F G) (toAut_bijective F G)
lemma toAut_isHomeomorph : IsHomeomorph (toAut F G) := by
  rw [isHomeomorph_iff_continuous_bijective]
  exact ⟨toAut_continuous F G, toAut_bijective F G⟩
lemma toAutMulEquiv_isHomeomorph : IsHomeomorph (toAutMulEquiv F G) :=
  toAut_isHomeomorph F G
noncomputable def toAutHomeo : G ≃ₜ Aut F := (toAut_isHomeomorph F G).homeomorph
variable {G}
@[simp]
lemma toAutMulEquiv_apply (g : G) : toAutMulEquiv F G g = toAut F G g := rfl
@[simp]
lemma toAutHomeo_apply (g : G) : toAutHomeo F G g = toAut F G g := rfl
end
end PreGaloisCategory
end CategoryTheory