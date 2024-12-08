import Mathlib.GroupTheory.FreeGroup.Basic
universe u
open Function Set
noncomputable section
structure FreeGroupBasis (ι : Type*) (G : Type*) [Group G] where
  ofRepr ::
    repr : G ≃* FreeGroup ι
class IsFreeGroup (G : Type u) [Group G] : Prop where
  nonempty_basis : ∃ (ι : Type u), Nonempty (FreeGroupBasis ι G)
namespace FreeGroupBasis
variable {ι ι' G H : Type*} [Group G] [Group H]
instance instFunLike : FunLike (FreeGroupBasis ι G) ι G where
  coe b := fun i ↦ b.repr.symm (FreeGroup.of i)
  coe_injective' := by
    rintro ⟨b⟩  ⟨b'⟩ hbb'
    have H : (b.symm : FreeGroup ι →* G) = (b'.symm : FreeGroup ι →* G) := by
      ext i; exact congr_fun hbb' i
    have : b.symm = b'.symm := by ext x; exact DFunLike.congr_fun H x
    rw [ofRepr.injEq, ← MulEquiv.symm_symm b, ← MulEquiv.symm_symm b', this]
@[simp] lemma repr_apply_coe (b : FreeGroupBasis ι G) (i : ι) : b.repr (b i) = FreeGroup.of i := by
  change b.repr (b.repr.symm (FreeGroup.of i)) = FreeGroup.of i
  simp
def ofFreeGroup (X : Type*) : FreeGroupBasis X (FreeGroup X) := ofRepr (MulEquiv.refl _)
@[simp] lemma ofFreeGroup_apply {X : Type*} (x : X) :
    FreeGroupBasis.ofFreeGroup X x = FreeGroup.of x :=
  rfl
protected def reindex (b : FreeGroupBasis ι G) (e : ι ≃ ι') : FreeGroupBasis ι' G :=
  ofRepr (b.repr.trans (FreeGroup.freeGroupCongr e))
@[simp] lemma reindex_apply (b : FreeGroupBasis ι G) (e : ι ≃ ι') (x : ι') :
    b.reindex e x = b (e.symm x) := rfl
protected def map (b : FreeGroupBasis ι G) (e : G ≃* H) : FreeGroupBasis ι H :=
  ofRepr (e.symm.trans b.repr)
@[simp] lemma map_apply (b : FreeGroupBasis ι G) (e : G ≃* H) (x : ι) :
    b.map e x = e (b x) := rfl
protected lemma injective (b : FreeGroupBasis ι G) : Injective b :=
  b.repr.symm.injective.comp FreeGroup.of_injective
lemma isFreeGroup (b : FreeGroupBasis ι G) : IsFreeGroup G :=
  ⟨range b, ⟨b.reindex (Equiv.ofInjective (↑b) b.injective)⟩⟩
instance (X : Type*) : IsFreeGroup (FreeGroup X) :=
  (ofFreeGroup X).isFreeGroup
@[simps!]
def lift (b : FreeGroupBasis ι G) : (ι → H) ≃ (G →* H) :=
  FreeGroup.lift.trans
    { toFun := fun f => f.comp b.repr.toMonoidHom
      invFun := fun f => f.comp b.repr.symm.toMonoidHom
      left_inv := fun f => by
        ext
        simp
      right_inv := fun f => by
        ext
        simp }
lemma ext_hom (b : FreeGroupBasis ι G) (f g : G →* H) (h : ∀ i, f (b i) = g (b i)) : f = g :=
  b.lift.symm.injective <| funext h
def ofLift {G : Type u} [Group G] (X : Type u) (of : X → G)
    (lift : ∀ {H : Type u} [Group H], (X → H) ≃ (G →* H))
    (lift_of : ∀ {H : Type u} [Group H], ∀ (f : X → H) (a), lift f (of a) = f a) :
    FreeGroupBasis X G where
  repr := MulEquiv.symm <| MonoidHom.toMulEquiv (FreeGroup.lift of) (lift FreeGroup.of)
      (by
        apply FreeGroup.ext_hom; intro x
        simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.id_apply, FreeGroup.lift.of,
          lift_of])
      (by
        let lift_symm_of : ∀ {H : Type u} [Group H], ∀ (f : G →* H) (a), lift.symm f a = f (of a) :=
          by intro H _ f a; simp [← lift_of (lift.symm f)]
        apply lift.symm.injective; ext x
        simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.id_apply, FreeGroup.lift.of,
          lift_of, lift_symm_of])
def ofUniqueLift {G : Type u} [Group G] (X : Type u) (of : X → G)
    (h : ∀ {H : Type u} [Group H] (f : X → H), ∃! F : G →* H, ∀ a, F (of a) = f a) :
    FreeGroupBasis X G :=
  let lift {H : Type u} [Group H] : (X → H) ≃ (G →* H) :=
    { toFun := fun f => Classical.choose (h f)
      invFun := fun F => F ∘ of
      left_inv := fun f => funext (Classical.choose_spec (h f)).left
      right_inv := fun F => ((Classical.choose_spec (h (F ∘ of))).right F fun _ => rfl).symm }
  let lift_of {H : Type u} [Group H] (f : X → H) (a : X) : lift f (of a) = f a :=
    congr_fun (lift.symm_apply_apply f) a
  ofLift X of @lift @lift_of
end FreeGroupBasis
namespace IsFreeGroup
variable (G : Type*) [Group G] [IsFreeGroup G]
def Generators : Type _ := (IsFreeGroup.nonempty_basis (G := G)).choose
irreducible_def mulEquiv : FreeGroup (Generators G) ≃* G :=
  (IsFreeGroup.nonempty_basis (G := G)).choose_spec.some.repr.symm
def basis : FreeGroupBasis (Generators G) G := FreeGroupBasis.ofRepr (mulEquiv G).symm
@[simps!]
def toFreeGroup : G ≃* FreeGroup (Generators G) :=
  (mulEquiv G).symm
variable {G}
def of : Generators G → G :=
  (mulEquiv G).toFun ∘ FreeGroup.of
variable {H : Type*} [Group H]
def lift : (Generators G → H) ≃ (G →* H) :=
  (basis G).lift
@[simp]
theorem lift_of (f : Generators G → H) (a : Generators G) : lift f (of a) = f a :=
  congr_fun (lift.symm_apply_apply f) a
@[simp]
theorem lift_symm_apply (f : G →* H) (a : Generators G) : (lift.symm f) a = f (of a) :=
  rfl
theorem ext_hom ⦃f g : G →* H⦄ (h : ∀ a : Generators G, f (of a) = g (of a)) : f = g :=
  lift.symm.injective (funext h)
theorem unique_lift (f : Generators G → H) : ∃! F : G →* H, ∀ a, F (of a) = f a := by
  simpa only [funext_iff] using lift.symm.bijective.existsUnique f
lemma ofLift {G : Type u} [Group G] (X : Type u) (of : X → G)
    (lift : ∀ {H : Type u} [Group H], (X → H) ≃ (G →* H))
    (lift_of : ∀ {H : Type u} [Group H], ∀ (f : X → H) (a), lift f (of a) = f a) :
    IsFreeGroup G :=
  (FreeGroupBasis.ofLift X of lift lift_of).isFreeGroup
lemma ofUniqueLift {G : Type u} [Group G] (X : Type u) (of : X → G)
    (h : ∀ {H : Type u} [Group H] (f : X → H), ∃! F : G →* H, ∀ a, F (of a) = f a) :
    IsFreeGroup G :=
  (FreeGroupBasis.ofUniqueLift X of h).isFreeGroup
lemma ofMulEquiv (e : G ≃* H) : IsFreeGroup H :=
  ((basis G).map e).isFreeGroup
end IsFreeGroup