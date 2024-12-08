import Mathlib.CategoryTheory.Category.Grpd
import Mathlib.CategoryTheory.Groupoid
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Homotopy.Path
import Mathlib.Data.Set.Subsingleton
open CategoryTheory
universe u
variable {X : Type u} [TopologicalSpace X]
variable {x₀ x₁ : X}
noncomputable section
open unitInterval
namespace Path
namespace Homotopy
section
def reflTransSymmAux (x : I × I) : ℝ :=
  if (x.2 : ℝ) ≤ 1 / 2 then x.1 * 2 * x.2 else x.1 * (2 - 2 * x.2)
@[continuity]
theorem continuous_reflTransSymmAux : Continuous reflTransSymmAux := by
  refine continuous_if_le ?_ ?_ (Continuous.continuousOn ?_) (Continuous.continuousOn ?_) ?_
  · continuity
  · continuity
  · continuity
  · continuity
  intro x hx
  norm_num [hx, mul_assoc]
theorem reflTransSymmAux_mem_I (x : I × I) : reflTransSymmAux x ∈ I := by
  dsimp only [reflTransSymmAux]
  split_ifs
  · constructor
    · apply mul_nonneg
      · apply mul_nonneg
        · unit_interval
        · norm_num
      · unit_interval
    · rw [mul_assoc]
      apply mul_le_one₀
      · unit_interval
      · apply mul_nonneg
        · norm_num
        · unit_interval
      · linarith
  · constructor
    · apply mul_nonneg
      · unit_interval
      linarith [unitInterval.nonneg x.2, unitInterval.le_one x.2]
    · apply mul_le_one₀
      · unit_interval
      · linarith [unitInterval.nonneg x.2, unitInterval.le_one x.2]
      · linarith [unitInterval.nonneg x.2, unitInterval.le_one x.2]
def reflTransSymm (p : Path x₀ x₁) : Homotopy (Path.refl x₀) (p.trans p.symm) where
  toFun x := p ⟨reflTransSymmAux x, reflTransSymmAux_mem_I x⟩
  continuous_toFun := by continuity
  map_zero_left := by simp [reflTransSymmAux]
  map_one_left x := by
    dsimp only [reflTransSymmAux, Path.coe_toContinuousMap, Path.trans]
    change _ = ite _ _ _
    split_ifs with h
    · rw [Path.extend, Set.IccExtend_of_mem]
      · norm_num
      · rw [unitInterval.mul_pos_mem_iff zero_lt_two]
        exact ⟨unitInterval.nonneg x, h⟩
    · rw [Path.symm, Path.extend, Set.IccExtend_of_mem]
      · simp only [Set.Icc.coe_one, one_mul, coe_mk_mk, Function.comp_apply]
        congr 1
        ext
        norm_num [sub_sub_eq_add_sub]
      · rw [unitInterval.two_mul_sub_one_mem_iff]
        exact ⟨(not_le.1 h).le, unitInterval.le_one x⟩
  prop' t x hx := by
    simp only [Set.mem_singleton_iff, Set.mem_insert_iff] at hx
    simp only [ContinuousMap.coe_mk, coe_toContinuousMap, Path.refl_apply]
    cases hx with
    | inl hx
    | inr hx =>
      rw [hx]
      norm_num [reflTransSymmAux]
def reflSymmTrans (p : Path x₀ x₁) : Homotopy (Path.refl x₁) (p.symm.trans p) :=
  (reflTransSymm p.symm).cast rfl <| congr_arg _ (Path.symm_symm _)
end
section TransRefl
def transReflReparamAux (t : I) : ℝ :=
  if (t : ℝ) ≤ 1 / 2 then 2 * t else 1
@[continuity]
theorem continuous_transReflReparamAux : Continuous transReflReparamAux := by
  refine continuous_if_le ?_ ?_ (Continuous.continuousOn ?_) (Continuous.continuousOn ?_) ?_ <;>
    [continuity; continuity; continuity; continuity; skip]
  intro x hx
  simp [hx]
theorem transReflReparamAux_mem_I (t : I) : transReflReparamAux t ∈ I := by
  unfold transReflReparamAux
  split_ifs <;> constructor <;> linarith [unitInterval.le_one t, unitInterval.nonneg t]
theorem transReflReparamAux_zero : transReflReparamAux 0 = 0 := by
  norm_num [transReflReparamAux]
theorem transReflReparamAux_one : transReflReparamAux 1 = 1 := by
  norm_num [transReflReparamAux]
theorem trans_refl_reparam (p : Path x₀ x₁) :
    p.trans (Path.refl x₁) =
      p.reparam (fun t => ⟨transReflReparamAux t, transReflReparamAux_mem_I t⟩) (by continuity)
        (Subtype.ext transReflReparamAux_zero) (Subtype.ext transReflReparamAux_one) := by
  ext
  unfold transReflReparamAux
  simp only [Path.trans_apply, not_le, coe_reparam, Function.comp_apply, one_div, Path.refl_apply]
  split_ifs
  · rfl
  · rfl
  · simp
  · simp
def transRefl (p : Path x₀ x₁) : Homotopy (p.trans (Path.refl x₁)) p :=
  ((Homotopy.reparam p (fun t => ⟨transReflReparamAux t, transReflReparamAux_mem_I t⟩)
          (by continuity) (Subtype.ext transReflReparamAux_zero)
          (Subtype.ext transReflReparamAux_one)).cast
      rfl (trans_refl_reparam p).symm).symm
def reflTrans (p : Path x₀ x₁) : Homotopy ((Path.refl x₀).trans p) p :=
  (transRefl p.symm).symm₂.cast (by simp) (by simp)
end TransRefl
section Assoc
def transAssocReparamAux (t : I) : ℝ :=
  if (t : ℝ) ≤ 1 / 4 then 2 * t else if (t : ℝ) ≤ 1 / 2 then t + 1 / 4 else 1 / 2 * (t + 1)
@[continuity]
theorem continuous_transAssocReparamAux : Continuous transAssocReparamAux := by
  refine continuous_if_le ?_ ?_ (Continuous.continuousOn ?_)
    (continuous_if_le ?_ ?_
      (Continuous.continuousOn ?_) (Continuous.continuousOn ?_) ?_).continuousOn
      ?_ <;>
    [continuity; continuity; continuity; continuity; continuity; continuity; continuity; skip;
      skip] <;>
    · intro x hx
      norm_num [hx]
theorem transAssocReparamAux_mem_I (t : I) : transAssocReparamAux t ∈ I := by
  unfold transAssocReparamAux
  split_ifs <;> constructor <;> linarith [unitInterval.le_one t, unitInterval.nonneg t]
theorem transAssocReparamAux_zero : transAssocReparamAux 0 = 0 := by
  norm_num [transAssocReparamAux]
theorem transAssocReparamAux_one : transAssocReparamAux 1 = 1 := by
  norm_num [transAssocReparamAux]
theorem trans_assoc_reparam {x₀ x₁ x₂ x₃ : X} (p : Path x₀ x₁) (q : Path x₁ x₂) (r : Path x₂ x₃) :
    (p.trans q).trans r =
      (p.trans (q.trans r)).reparam
        (fun t => ⟨transAssocReparamAux t, transAssocReparamAux_mem_I t⟩) (by continuity)
        (Subtype.ext transAssocReparamAux_zero) (Subtype.ext transAssocReparamAux_one) := by
  ext x
  simp only [transAssocReparamAux, Path.trans_apply, mul_inv_cancel_left₀, not_le,
    Function.comp_apply, Ne, not_false_iff, one_ne_zero, mul_ite, Subtype.coe_mk,
    Path.coe_reparam]
  split_ifs with h₁ h₂ h₃ h₄ h₅
  · rfl
  · exfalso
    linarith
  · exfalso
    linarith
  · exfalso
    linarith
  · exfalso
    linarith
  · exfalso
    linarith
  · exfalso
    linarith
  · have h : 2 * (2 * (x : ℝ)) - 1 = 2 * (2 * (↑x + 1 / 4) - 1) := by linarith
    simp [h₂, h₁, h, dif_neg (show ¬False from id), dif_pos True.intro, if_false, if_true]
  · exfalso
    linarith
  · exfalso
    linarith
  · exfalso
    linarith
  · exfalso
    linarith
  · exfalso
    linarith
  · exfalso
    linarith
  · congr
    ring
def transAssoc {x₀ x₁ x₂ x₃ : X} (p : Path x₀ x₁) (q : Path x₁ x₂) (r : Path x₂ x₃) :
    Homotopy ((p.trans q).trans r) (p.trans (q.trans r)) :=
  ((Homotopy.reparam (p.trans (q.trans r))
          (fun t => ⟨transAssocReparamAux t, transAssocReparamAux_mem_I t⟩) (by continuity)
          (Subtype.ext transAssocReparamAux_zero) (Subtype.ext transAssocReparamAux_one)).cast
      rfl (trans_assoc_reparam p q r).symm).symm
end Assoc
end Homotopy
end Path
@[ext]
structure FundamentalGroupoid (X : Type u) where
  as : X
namespace FundamentalGroupoid
@[simps]
def equiv (X : Type*) : FundamentalGroupoid X ≃ X where
  toFun x := x.as
  invFun x := .mk x
  left_inv _ := rfl
  right_inv _ := rfl
@[simp]
lemma isEmpty_iff (X : Type*) :
    IsEmpty (FundamentalGroupoid X) ↔ IsEmpty X :=
  equiv _ |>.isEmpty_congr
instance (X : Type*) [IsEmpty X] :
    IsEmpty (FundamentalGroupoid X) :=
  equiv _ |>.isEmpty
@[simp]
lemma nonempty_iff (X : Type*) :
    Nonempty (FundamentalGroupoid X) ↔ Nonempty X :=
  equiv _ |>.nonempty_congr
instance (X : Type*) [Nonempty X] :
    Nonempty (FundamentalGroupoid X) :=
  equiv _ |>.nonempty
@[simp]
lemma subsingleton_iff (X : Type*) :
    Subsingleton (FundamentalGroupoid X) ↔ Subsingleton X :=
  equiv _ |>.subsingleton_congr
instance (X : Type*) [Subsingleton X] :
    Subsingleton (FundamentalGroupoid X) :=
  equiv _ |>.subsingleton
instance {X : Type u} [Inhabited X] : Inhabited (FundamentalGroupoid X) :=
  ⟨⟨default⟩⟩
attribute [local instance] Path.Homotopic.setoid
instance : CategoryTheory.Groupoid (FundamentalGroupoid X) where
  Hom x y := Path.Homotopic.Quotient x.as y.as
  id x := ⟦Path.refl x.as⟧
  comp {_ _ _} := Path.Homotopic.Quotient.comp
  id_comp {x _} f :=
    Quotient.inductionOn f fun a =>
      show ⟦(Path.refl x.as).trans a⟧ = ⟦a⟧ from Quotient.sound ⟨Path.Homotopy.reflTrans a⟩
  comp_id {_ y} f :=
    Quotient.inductionOn f fun a =>
      show ⟦a.trans (Path.refl y.as)⟧ = ⟦a⟧ from Quotient.sound ⟨Path.Homotopy.transRefl a⟩
  assoc {_ _ _ _} f g h :=
    Quotient.inductionOn₃ f g h fun p q r =>
      show ⟦(p.trans q).trans r⟧ = ⟦p.trans (q.trans r)⟧ from
        Quotient.sound ⟨Path.Homotopy.transAssoc p q r⟩
  inv {x y} p :=
    Quotient.lift (fun l : Path x.as y.as => ⟦l.symm⟧)
      (by
        rintro a b ⟨h⟩
        simp only
        rw [Quotient.eq]
        exact ⟨h.symm₂⟩)
      p
  inv_comp {_ y} f :=
    Quotient.inductionOn f fun a =>
      show ⟦a.symm.trans a⟧ = ⟦Path.refl y.as⟧ from
        Quotient.sound ⟨(Path.Homotopy.reflSymmTrans a).symm⟩
  comp_inv {x _} f :=
    Quotient.inductionOn f fun a =>
      show ⟦a.trans a.symm⟧ = ⟦Path.refl x.as⟧ from
        Quotient.sound ⟨(Path.Homotopy.reflTransSymm a).symm⟩
theorem comp_eq (x y z : FundamentalGroupoid X) (p : x ⟶ y) (q : y ⟶ z) : p ≫ q = p.comp q := rfl
theorem id_eq_path_refl (x : FundamentalGroupoid X) : 𝟙 x = ⟦Path.refl x.as⟧ := rfl
def fundamentalGroupoidFunctor : TopCat ⥤ CategoryTheory.Grpd where
  obj X := { α := FundamentalGroupoid X }
  map f :=
    { obj := fun x => ⟨f x.as⟩
      map := fun {X Y} p => by exact Path.Homotopic.Quotient.mapFn p f
      map_id := fun _ => rfl
      map_comp := fun {x y z} p q => by
        refine Quotient.inductionOn₂ p q fun a b => ?_
        simp only [comp_eq, ← Path.Homotopic.map_lift, ← Path.Homotopic.comp_lift, Path.map_trans] }
  map_id X := by
    simp only
    change _ = (⟨_, _, _⟩ : FundamentalGroupoid X ⥤ FundamentalGroupoid X)
    congr
    ext x y p
    refine Quotient.inductionOn p fun q => ?_
    rw [← Path.Homotopic.map_lift]
    conv_rhs => rw [← q.map_id]
    rfl
  map_comp f g := by
    simp only
    congr
    ext x y p
    refine Quotient.inductionOn p fun q => ?_
    simp only [Quotient.map_mk, Path.map_map, Quotient.eq']
    rfl
@[inherit_doc] scoped notation "π" => FundamentalGroupoid.fundamentalGroupoidFunctor
scoped notation "πₓ" => FundamentalGroupoid.fundamentalGroupoidFunctor.obj
scoped notation "πₘ" => FundamentalGroupoid.fundamentalGroupoidFunctor.map
theorem map_eq {X Y : TopCat} {x₀ x₁ : X} (f : C(X, Y)) (p : Path.Homotopic.Quotient x₀ x₁) :
    (πₘ f).map p = p.mapFn f := rfl
abbrev toTop {X : TopCat} (x : πₓ X) : X := x.as
abbrev fromTop {X : TopCat} (x : X) : πₓ X := ⟨x⟩
abbrev toPath {X : TopCat} {x₀ x₁ : πₓ X} (p : x₀ ⟶ x₁) :
    Path.Homotopic.Quotient (X := X) x₀.as x₁.as :=
  p
abbrev fromPath {X : TopCat} {x₀ x₁ : X} (p : Path.Homotopic.Quotient x₀ x₁) :
    FundamentalGroupoid.mk x₀ ⟶ FundamentalGroupoid.mk x₁ := p
end FundamentalGroupoid