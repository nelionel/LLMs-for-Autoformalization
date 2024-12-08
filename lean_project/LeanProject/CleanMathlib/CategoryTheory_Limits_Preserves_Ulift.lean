import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.Data.Set.Subsingleton
universe v w w' u
namespace CategoryTheory.Limits.Types
def sectionsEquiv {J : Type*} [Category J] (K : J ⥤ Type u) :
    K.sections ≃ (K ⋙ uliftFunctor.{v, u}).sections where
  toFun := fun ⟨u, hu⟩ => ⟨fun j => ⟨u j⟩, fun f => by simp [hu f]⟩
  invFun := fun ⟨u, hu⟩ => ⟨fun j => (u j).down, @fun j j' f => by simp [← hu f]⟩
  left_inv _ := rfl
  right_inv _ := rfl
noncomputable
instance : PreservesLimitsOfSize.{w', w} uliftFunctor.{v, u} where
  preservesLimitsOfShape {J} := {
    preservesLimit := fun {K} => {
      preserves := fun {c} hc => by
        rw [Types.isLimit_iff ((uliftFunctor.{v, u}).mapCone c)]
        intro s hs
        obtain ⟨x, hx₁, hx₂⟩ := (Types.isLimit_iff c).mp ⟨hc⟩ _ ((sectionsEquiv K).symm ⟨s, hs⟩).2
        exact ⟨⟨x⟩, fun i => ULift.ext _ _ (hx₁ i),
          fun y hy => ULift.ext _ _ (hx₂ y.down fun i ↦ ULift.ext_iff.mp (hy i))⟩ } }
noncomputable instance : CreatesLimitsOfSize.{w, u} uliftFunctor.{v, u} where
  CreatesLimitsOfShape := { CreatesLimit := fun {_} ↦ createsLimitOfFullyFaithfulOfPreserves }
variable {J : Type*} [Category J] {K : J ⥤ Type u} {c : Cocone K} (hc : IsColimit c)
variable {lc : Cocone (K ⋙ uliftFunctor.{v, u})}
def coconeOfSet (ls : Set lc.pt) : Cocone K where
  pt := ULift Prop
  ι :=
  { app := fun j x ↦ ⟨lc.ι.app j ⟨x⟩ ∈ ls⟩
    naturality := fun i j f ↦ by dsimp only; rw [← lc.w f]; rfl }
def descSet (ls : Set lc.pt) : Set c.pt := {x | (hc.desc (coconeOfSet ls) x).down}
lemma descSet_spec (s : Set c.pt) (ls : Set lc.pt) :
    descSet hc ls = s ↔ ∀ j x, lc.ι.app j ⟨x⟩ ∈ ls ↔ c.ι.app j x ∈ s := by
  refine ⟨?_, fun he ↦ funext fun x ↦ ?_⟩
  · rintro rfl j x
    exact (congr_arg ULift.down (congr_fun (hc.fac (coconeOfSet ls) j) x).symm).to_iff
  · refine (congr_arg ULift.down (congr_fun (hc.uniq (coconeOfSet ls) (⟨· ∈ s⟩) fun j ↦ ?_) x)).symm
    ext y; exact congr_arg ULift.up (propext (he j y).symm)
lemma mem_descSet_singleton {x : lc.pt} {j : J} {y : K.obj j} :
    c.ι.app j y ∈ descSet hc {x} ↔ lc.ι.app j ⟨y⟩ = x :=
  ((descSet_spec hc _ {x}).mp rfl j y).symm
variable (lc)
lemma descSet_univ : descSet hc (@Set.univ lc.pt) = Set.univ := by simp [descSet_spec]
lemma iUnion_descSet_singleton : ⋃ x : lc.pt, descSet hc {x} = Set.univ := by
  rw [← descSet_univ hc lc, eq_comm, descSet_spec]
  intro j x
  erw [true_iff, Set.mem_iUnion]
  use lc.ι.app j ⟨x⟩
  rw [mem_descSet_singleton]
lemma descSet_empty : descSet hc (∅ : Set lc.pt) = ∅ := by simp [descSet_spec]
lemma descSet_inter_of_ne (x y : lc.pt) (hn : x ≠ y) : descSet hc {x} ∩ descSet hc {y} = ∅ := by
  rw [eq_comm, ← descSet_empty hc lc, descSet_spec]
  intro j z
  erw [false_iff]
  rintro ⟨hx, hy⟩
  rw [mem_descSet_singleton] at hx hy
  exact hn (hx ▸ hy)
lemma exists_unique_mem_descSet (x : c.pt) : ∃! y : lc.pt, x ∈ descSet hc {y} :=
  exists_unique_of_exists_of_unique
    (Set.mem_iUnion.mp <| Set.eq_univ_iff_forall.mp (iUnion_descSet_singleton hc lc) x)
    fun y₁ y₂ h₁ h₂ ↦ by_contra fun hn ↦
      Set.eq_empty_iff_forall_not_mem.1 (descSet_inter_of_ne hc lc y₁ y₂ hn) x ⟨h₁, h₂⟩
noncomputable def descFun (x : c.pt) : lc.pt := (exists_unique_mem_descSet hc lc x).exists.choose
lemma descFun_apply_spec {x : c.pt} {y : lc.pt} : descFun hc lc x = y ↔ x ∈ descSet hc {y} :=
  have hu := exists_unique_mem_descSet hc lc x
  have hm := hu.exists.choose_spec
  ⟨fun he ↦ he ▸ hm, hu.unique hm⟩
lemma descFun_spec (f : c.pt → lc.pt) :
    f = descFun hc lc ↔ ∀ j, f ∘ c.ι.app j = lc.ι.app j ∘ ULift.up := by
  refine ⟨?_, fun he ↦ funext fun x ↦ ((descFun_apply_spec hc lc).mpr ?_).symm⟩
  · rintro rfl j; ext
    apply (descFun_apply_spec hc lc).mpr
    rw [mem_descSet_singleton]; rfl
  · rw [← (jointly_surjective_of_isColimit hc x).choose_spec.choose_spec, mem_descSet_singleton]
    exact (congr_fun (he _) _).symm
noncomputable instance : PreservesColimitsOfSize.{w', w} uliftFunctor.{v, u} where
  preservesColimitsOfShape {J _} :=
  { preservesColimit := fun {F} ↦
    { preserves := fun {c} hc ↦ ⟨{
        desc := fun lc x ↦ descFun hc lc x.down
        fac := fun lc j ↦ by ext ⟨⟩; apply congr_fun ((descFun_spec hc lc _).mp rfl j)
        uniq := fun lc f hf ↦ by ext ⟨⟩; apply congr_fun ((descFun_spec hc lc (f ∘ ULift.up)).mpr
          fun j ↦ funext fun y ↦ congr_fun (hf j) ⟨y⟩) }⟩ } }
noncomputable instance : CreatesColimitsOfSize.{w, u} uliftFunctor.{v, u} where
  CreatesColimitsOfShape := { CreatesColimit := fun {_} ↦ createsColimitOfFullyFaithfulOfPreserves }
end CategoryTheory.Limits.Types