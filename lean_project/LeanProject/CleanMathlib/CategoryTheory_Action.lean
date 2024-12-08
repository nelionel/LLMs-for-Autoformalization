import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.IsConnected
import Mathlib.CategoryTheory.SingleObj
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.SemidirectProduct
open MulAction SemidirectProduct
namespace CategoryTheory
universe u
variable (M : Type*) [Monoid M] (X : Type u) [MulAction M X]
@[simps]
def actionAsFunctor : SingleObj M ⥤ Type u where
  obj _ := X
  map := (· • ·)
  map_id _ := funext <| MulAction.one_smul
  map_comp f g := funext fun x => (smul_smul g f x).symm
def ActionCategory :=
  (actionAsFunctor M X).Elements
instance : Category (ActionCategory M X) := by
  dsimp only [ActionCategory]
  infer_instance
namespace ActionCategory
def π : ActionCategory M X ⥤ SingleObj M :=
  CategoryOfElements.π _
@[simp]
theorem π_map (p q : ActionCategory M X) (f : p ⟶ q) : (π M X).map f = f.val :=
  rfl
@[simp]
theorem π_obj (p : ActionCategory M X) : (π M X).obj p = SingleObj.star M :=
  Unit.ext _ _
variable {M X}
protected def back : ActionCategory M X → X := fun x => x.snd
instance : CoeTC X (ActionCategory M X) :=
  ⟨fun x => ⟨(), x⟩⟩
@[simp]
theorem coe_back (x : X) : ActionCategory.back (x : ActionCategory M X) = x :=
  rfl
@[simp]
theorem back_coe (x : ActionCategory M X) : ↑x.back = x := by cases x; rfl
variable (M X)
def objEquiv : X ≃ ActionCategory M X where
  toFun x := x
  invFun x := x.back
  left_inv := coe_back
  right_inv := back_coe
theorem hom_as_subtype (p q : ActionCategory M X) : (p ⟶ q) = { m : M // m • p.back = q.back } :=
  rfl
instance [Inhabited X] : Inhabited (ActionCategory M X) :=
  ⟨show X from default⟩
instance [Nonempty X] : Nonempty (ActionCategory M X) :=
  Nonempty.map (objEquiv M X) inferInstance
variable {X} (x : X)
def stabilizerIsoEnd : stabilizerSubmonoid M x ≃* @End (ActionCategory M X) _ x :=
  MulEquiv.refl _
@[simp]
theorem stabilizerIsoEnd_apply (f : stabilizerSubmonoid M x) :
    (stabilizerIsoEnd M x) f = f :=
  rfl
@[simp 1100]
theorem stabilizerIsoEnd_symm_apply (f : End _) : (stabilizerIsoEnd M x).symm f = f :=
  rfl
variable {M}
@[simp]
protected theorem id_val (x : ActionCategory M X) : Subtype.val (𝟙 x) = 1 :=
  rfl
@[simp]
protected theorem comp_val {x y z : ActionCategory M X} (f : x ⟶ y) (g : y ⟶ z) :
    (f ≫ g).val = g.val * f.val :=
  rfl
instance [IsPretransitive M X] [Nonempty X] : IsConnected (ActionCategory M X) :=
  zigzag_isConnected fun x y =>
    Relation.ReflTransGen.single <|
      Or.inl <| nonempty_subtype.mpr (show _ from exists_smul_eq M x.back y.back)
section Group
variable {G : Type*} [Group G] [MulAction G X]
instance : Groupoid (ActionCategory G X) :=
  CategoryTheory.groupoidOfElements _
def endMulEquivSubgroup (H : Subgroup G) : End (objEquiv G (G ⧸ H) ↑(1 : G)) ≃* H :=
  MulEquiv.trans (stabilizerIsoEnd G ((1 : G) : G ⧸ H)).symm
    (MulEquiv.subgroupCongr <| stabilizer_quotient H)
def homOfPair (t : X) (g : G) : @Quiver.Hom (ActionCategory G X) _ (g⁻¹ • t :) t :=
  Subtype.mk g (smul_inv_smul g t)
@[simp]
theorem homOfPair.val (t : X) (g : G) : (homOfPair t g).val = g :=
  rfl
protected def cases {P : ∀ ⦃a b : ActionCategory G X⦄, (a ⟶ b) → Sort*}
    (hyp : ∀ t g, P (homOfPair t g)) ⦃a b⦄ (f : a ⟶ b) : P f := by
  refine cast ?_ (hyp b.back f.val)
  rcases a with ⟨⟨⟩, a : X⟩
  rcases b with ⟨⟨⟩, b : X⟩
  rcases f with ⟨g : G, h : g • a = b⟩
  cases inv_smul_eq_iff.mpr h.symm
  rfl
lemma cases' ⦃a' b' : ActionCategory G X⦄ (f : a' ⟶ b') :
    ∃ (a b : X) (g : G) (ha : a' = a) (hb : b' = b) (hg : a = g⁻¹ • b),
      f = eqToHom (by rw [ha, hg]) ≫ homOfPair b g ≫ eqToHom (by rw [hb]) := by
  revert a' b' f
  exact ActionCategory.cases (fun t g => ⟨g⁻¹ • t, t, g, rfl, rfl, rfl, by simp⟩)
variable {H : Type*} [Group H]
@[simps]
def curry (F : ActionCategory G X ⥤ SingleObj H) : G →* (X → H) ⋊[mulAutArrow] G :=
  have F_map_eq : ∀ {a b} {f : a ⟶ b}, F.map f = (F.map (homOfPair b.back f.val) : H) := by
    apply ActionCategory.cases
    intros
    rfl
  { toFun := fun g => ⟨fun b => F.map (homOfPair b g), g⟩
    map_one' := by
      dsimp
      ext1
      · ext b
        exact F_map_eq.symm.trans (F.map_id b)
      rfl
    map_mul' := by
      intro g h
      ext b
      · exact F_map_eq.symm.trans (F.map_comp (homOfPair (g⁻¹ • b) h) (homOfPair b g))
      rfl }
@[simps]
def uncurry (F : G →* (X → H) ⋊[mulAutArrow] G) (sane : ∀ g, (F g).right = g) :
    ActionCategory G X ⥤ SingleObj H where
  obj _ := ()
  map {_ b} f := (F f.val).left b.back
  map_id x := by
    dsimp
    rw [F.map_one]
    rfl
  map_comp f g := by
    obtain ⟨_, z, γ₁, rfl, rfl, rfl, rfl⟩ := ActionCategory.cases' g
    obtain ⟨_, y, γ₂, rfl, hy, rfl, rfl⟩ := ActionCategory.cases' f
    obtain rfl : y = γ₁⁻¹ • z := congr_arg Sigma.snd hy.symm
    simp [sane]
    rfl
end Group
end ActionCategory
end CategoryTheory