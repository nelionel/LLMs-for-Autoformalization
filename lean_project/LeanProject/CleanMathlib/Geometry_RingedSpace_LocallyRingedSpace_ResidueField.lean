import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
universe u
open CategoryTheory TopologicalSpace Opposite
noncomputable section
namespace AlgebraicGeometry.LocallyRingedSpace
variable (X : LocallyRingedSpace.{u}) {U : Opens X}
def residueField (x : X) : CommRingCat :=
  CommRingCat.of <| IsLocalRing.ResidueField (X.presheaf.stalk x)
instance (x : X) : Field (X.residueField x) :=
  inferInstanceAs <| Field (IsLocalRing.ResidueField (X.presheaf.stalk x))
def evaluation (x : U) : X.presheaf.obj (op U) ⟶ X.residueField x :=
  X.presheaf.germ U x.1 x.2 ≫ IsLocalRing.residue _
def Γevaluation (x : X) : X.presheaf.obj (op ⊤) ⟶ X.residueField x :=
  X.evaluation ⟨x, show x ∈ ⊤ from trivial⟩
@[simp]
lemma evaluation_eq_zero_iff_not_mem_basicOpen (x : U) (f : X.presheaf.obj (op U)) :
    X.evaluation x f = 0 ↔ x.val ∉ X.toRingedSpace.basicOpen f := by
  rw [X.toRingedSpace.mem_basicOpen f x.1 x.2, ← not_iff_not, not_not]
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _)
lemma evaluation_ne_zero_iff_mem_basicOpen (x : U) (f : X.presheaf.obj (op U)) :
    X.evaluation x f ≠ 0 ↔ x.val ∈ X.toRingedSpace.basicOpen f := by
  simp
lemma basicOpen_eq_bot_iff_forall_evaluation_eq_zero (f : X.presheaf.obj (op U)) :
    X.toRingedSpace.basicOpen f = ⊥ ↔ ∀ (x : U), X.evaluation x f = 0 := by
  simp only [evaluation_eq_zero_iff_not_mem_basicOpen, Subtype.forall]
  exact ⟨fun h ↦ h ▸ fun a _ hc ↦ hc,
    fun h ↦ eq_bot_iff.mpr <| fun a ha ↦ h a (X.toRingedSpace.basicOpen_le f ha) ha⟩
@[simp]
lemma Γevaluation_eq_zero_iff_not_mem_basicOpen (x : X) (f : X.presheaf.obj (op ⊤)) :
    X.Γevaluation x f = 0 ↔ x ∉ X.toRingedSpace.basicOpen f :=
  evaluation_eq_zero_iff_not_mem_basicOpen X ⟨x, show x ∈ ⊤ by trivial⟩ f
lemma Γevaluation_ne_zero_iff_mem_basicOpen (x : X) (f : X.presheaf.obj (op ⊤)) :
    X.Γevaluation x f ≠ 0 ↔ x ∈ X.toRingedSpace.basicOpen f :=
  evaluation_ne_zero_iff_mem_basicOpen X ⟨x, show x ∈ ⊤ by trivial⟩ f
variable {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X)
def residueFieldMap (x : X) : Y.residueField (f.base x) ⟶ X.residueField x :=
  IsLocalRing.ResidueField.map (f.stalkMap x)
lemma residue_comp_residueFieldMap_eq_stalkMap_comp_residue (x : X) :
    IsLocalRing.residue _ ≫ residueFieldMap f x = f.stalkMap x ≫ IsLocalRing.residue _ := by
  simp [residueFieldMap]
  rfl
@[simp]
lemma residueFieldMap_id (x : X) :
    residueFieldMap (𝟙 X) x = 𝟙 (X.residueField x) := by
  simp only [id_toShHom', SheafedSpace.id_base, TopCat.coe_id, id_eq, residueFieldMap, stalkMap_id]
  apply IsLocalRing.ResidueField.map_id
@[simp]
lemma residueFieldMap_comp {Z : LocallyRingedSpace.{u}} (g : Y ⟶ Z) (x : X) :
    residueFieldMap (f ≫ g) x = residueFieldMap g (f.base x) ≫ residueFieldMap f x := by
  simp only [comp_toShHom, SheafedSpace.comp_base, Function.comp_apply, residueFieldMap]
  simp_rw [stalkMap_comp]
  apply IsLocalRing.ResidueField.map_comp
@[reassoc]
lemma evaluation_naturality {V : Opens Y} (x : (Opens.map f.base).obj V) :
    Y.evaluation ⟨f.base x, x.property⟩ ≫ residueFieldMap f x.val =
      f.c.app (op V) ≫ X.evaluation x := by
  dsimp only [LocallyRingedSpace.evaluation,
    LocallyRingedSpace.residueFieldMap]
  rw [Category.assoc]
  ext a
  simp only [comp_apply]
  erw [IsLocalRing.ResidueField.map_residue, PresheafedSpace.stalkMap_germ_apply]
  rfl
lemma evaluation_naturality_apply {V : Opens Y} (x : (Opens.map f.base).obj V)
    (a : Y.presheaf.obj (op V)) :
    residueFieldMap f x.val (Y.evaluation ⟨f.base x, x.property⟩ a) =
      X.evaluation x (f.c.app (op V) a) := by
  simpa using congrFun (congrArg DFunLike.coe <| evaluation_naturality f x) a
@[reassoc]
lemma Γevaluation_naturality (x : X) :
    Y.Γevaluation (f.base x) ≫ residueFieldMap f x =
      f.c.app (op ⊤) ≫ X.Γevaluation x :=
  evaluation_naturality f ⟨x, by simp only [Opens.map_top]; trivial⟩
lemma Γevaluation_naturality_apply (x : X) (a : Y.presheaf.obj (op ⊤)) :
    residueFieldMap f x (Y.Γevaluation (f.base x) a) =
      X.Γevaluation x (f.c.app (op ⊤) a) :=
  evaluation_naturality_apply f ⟨x, by simp only [Opens.map_top]; trivial⟩ a
end LocallyRingedSpace
end AlgebraicGeometry