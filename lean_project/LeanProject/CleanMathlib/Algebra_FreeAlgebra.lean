import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
variable (R : Type*) [CommSemiring R]
variable (X : Type*)
namespace FreeAlgebra
inductive Pre
  | of : X → Pre
  | ofScalar : R → Pre
  | add : Pre → Pre → Pre
  | mul : Pre → Pre → Pre
namespace Pre
instance : Inhabited (Pre R X) := ⟨ofScalar 0⟩
def hasCoeGenerator : Coe X (Pre R X) := ⟨of⟩
def hasCoeSemiring : Coe R (Pre R X) := ⟨ofScalar⟩
def hasMul : Mul (Pre R X) := ⟨mul⟩
def hasAdd : Add (Pre R X) := ⟨add⟩
def hasZero : Zero (Pre R X) := ⟨ofScalar 0⟩
def hasOne : One (Pre R X) := ⟨ofScalar 1⟩
def hasSMul : SMul R (Pre R X) := ⟨fun r m ↦ mul (ofScalar r) m⟩
end Pre
attribute [local instance] Pre.hasCoeGenerator Pre.hasCoeSemiring Pre.hasMul Pre.hasAdd
  Pre.hasZero Pre.hasOne Pre.hasSMul
def liftFun {A : Type*} [Semiring A] [Algebra R A] (f : X → A) :
    Pre R X → A
  | .of t => f t
  | .add a b => liftFun f a + liftFun f b
  | .mul a b => liftFun f a * liftFun f b
  | .ofScalar c => algebraMap _ _ c
inductive Rel : Pre R X → Pre R X → Prop
  | add_scalar {r s : R} : Rel (↑(r + s)) (↑r + ↑s)
  | mul_scalar {r s : R} : Rel (↑(r * s)) (↑r * ↑s)
  | central_scalar {r : R} {a : Pre R X} : Rel (r * a) (a * r)
  | add_assoc {a b c : Pre R X} : Rel (a + b + c) (a + (b + c))
  | add_comm {a b : Pre R X} : Rel (a + b) (b + a)
  | zero_add {a : Pre R X} : Rel (0 + a) a
  | mul_assoc {a b c : Pre R X} : Rel (a * b * c) (a * (b * c))
  | one_mul {a : Pre R X} : Rel (1 * a) a
  | mul_one {a : Pre R X} : Rel (a * 1) a
  | left_distrib {a b c : Pre R X} : Rel (a * (b + c)) (a * b + a * c)
  | right_distrib {a b c : Pre R X} :
      Rel ((a + b) * c) (a * c + b * c)
  | zero_mul {a : Pre R X} : Rel (0 * a) 0
  | mul_zero {a : Pre R X} : Rel (a * 0) 0
  | add_compat_left {a b c : Pre R X} : Rel a b → Rel (a + c) (b + c)
  | add_compat_right {a b c : Pre R X} : Rel a b → Rel (c + a) (c + b)
  | mul_compat_left {a b c : Pre R X} : Rel a b → Rel (a * c) (b * c)
  | mul_compat_right {a b c : Pre R X} : Rel a b → Rel (c * a) (c * b)
end FreeAlgebra
def FreeAlgebra :=
  Quot (FreeAlgebra.Rel R X)
namespace FreeAlgebra
attribute [local instance] Pre.hasCoeGenerator Pre.hasCoeSemiring Pre.hasMul Pre.hasAdd
  Pre.hasZero Pre.hasOne Pre.hasSMul
instance instSMul {A} [CommSemiring A] [Algebra R A] : SMul R (FreeAlgebra A X) where
  smul r := Quot.map (HMul.hMul (algebraMap R A r : Pre A X)) fun _ _ ↦ Rel.mul_compat_right
instance instZero : Zero (FreeAlgebra R X) where zero := Quot.mk _ 0
instance instOne : One (FreeAlgebra R X) where one := Quot.mk _ 1
instance instAdd : Add (FreeAlgebra R X) where
  add := Quot.map₂ HAdd.hAdd (fun _ _ _ ↦ Rel.add_compat_right) fun _ _ _ ↦ Rel.add_compat_left
instance instMul : Mul (FreeAlgebra R X) where
  mul := Quot.map₂ HMul.hMul (fun _ _ _ ↦ Rel.mul_compat_right) fun _ _ _ ↦ Rel.mul_compat_left
private theorem mk_mul (x y : Pre R X) :
    Quot.mk (Rel R X) (x * y) = (HMul.hMul (self := instHMul (α := FreeAlgebra R X))
    (Quot.mk (Rel R X) x) (Quot.mk (Rel R X) y)) :=
  rfl
instance instMonoidWithZero : MonoidWithZero (FreeAlgebra R X) where
  mul_assoc := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩
    exact Quot.sound Rel.mul_assoc
  one := Quot.mk _ 1
  one_mul := by
    rintro ⟨⟩
    exact Quot.sound Rel.one_mul
  mul_one := by
    rintro ⟨⟩
    exact Quot.sound Rel.mul_one
  zero_mul := by
    rintro ⟨⟩
    exact Quot.sound Rel.zero_mul
  mul_zero := by
    rintro ⟨⟩
    exact Quot.sound Rel.mul_zero
instance instDistrib : Distrib (FreeAlgebra R X) where
  left_distrib := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩
    exact Quot.sound Rel.left_distrib
  right_distrib := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩
    exact Quot.sound Rel.right_distrib
instance instAddCommMonoid : AddCommMonoid (FreeAlgebra R X) where
  add_assoc := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩
    exact Quot.sound Rel.add_assoc
  zero_add := by
    rintro ⟨⟩
    exact Quot.sound Rel.zero_add
  add_zero := by
    rintro ⟨⟩
    change Quot.mk _ _ = _
    rw [Quot.sound Rel.add_comm, Quot.sound Rel.zero_add]
  add_comm := by
    rintro ⟨⟩ ⟨⟩
    exact Quot.sound Rel.add_comm
  nsmul := (· • ·)
  nsmul_zero := by
    rintro ⟨⟩
    change Quot.mk _ (_ * _) = _
    rw [map_zero]
    exact Quot.sound Rel.zero_mul
  nsmul_succ n := by
    rintro ⟨a⟩
    dsimp only [HSMul.hSMul, instSMul, Quot.map]
    rw [map_add, map_one, mk_mul, mk_mul, ← add_one_mul (_ : FreeAlgebra R X)]
    congr 1
    exact Quot.sound Rel.add_scalar
instance : Semiring (FreeAlgebra R X) where
  __ := instMonoidWithZero R X
  __ := instAddCommMonoid R X
  __ := instDistrib R X
  natCast n := Quot.mk _ (n : R)
  natCast_zero := by simp; rfl
  natCast_succ n := by simpa using Quot.sound Rel.add_scalar
instance : Inhabited (FreeAlgebra R X) :=
  ⟨0⟩
instance instAlgebra {A} [CommSemiring A] [Algebra R A] : Algebra R (FreeAlgebra A X) where
  toRingHom := ({
      toFun := fun r => Quot.mk _ r
      map_one' := rfl
      map_mul' := fun _ _ => Quot.sound Rel.mul_scalar
      map_zero' := rfl
      map_add' := fun _ _ => Quot.sound Rel.add_scalar } : A →+* FreeAlgebra A X).comp
      (algebraMap R A)
  commutes' _ := by
    rintro ⟨⟩
    exact Quot.sound Rel.central_scalar
  smul_def' _ _ := rfl
variable (S : Type) [CommSemiring S] in
example : (Semiring.toNatAlgebra : Algebra ℕ (FreeAlgebra S X)) = instAlgebra _ _ := rfl
instance {R S A} [CommSemiring R] [CommSemiring S] [CommSemiring A]
    [SMul R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] :
    IsScalarTower R S (FreeAlgebra A X) where
  smul_assoc r s x := by
    change algebraMap S A (r • s) • x = algebraMap R A _ • (algebraMap S A _ • x)
    rw [← smul_assoc]
    congr
    simp only [Algebra.algebraMap_eq_smul_one, smul_eq_mul]
    rw [smul_assoc, ← smul_one_mul]
instance {R S A} [CommSemiring R] [CommSemiring S] [CommSemiring A] [Algebra R A] [Algebra S A] :
    SMulCommClass R S (FreeAlgebra A X) where
  smul_comm r s x := smul_comm (algebraMap R A r) (algebraMap S A s) x
instance {S : Type*} [CommRing S] : Ring (FreeAlgebra S X) :=
  Algebra.semiringToRing S
variable (S : Type) [CommRing S] in
example : (Ring.toIntAlgebra _ : Algebra ℤ (FreeAlgebra S X)) = instAlgebra _ _ := rfl
variable {X}
irreducible_def ι : X → FreeAlgebra R X := fun m ↦ Quot.mk _ m
@[simp]
theorem quot_mk_eq_ι (m : X) : Quot.mk (FreeAlgebra.Rel R X) m = ι R m := by rw [ι_def]
variable {A : Type*} [Semiring A] [Algebra R A]
private def liftAux (f : X → A) : FreeAlgebra R X →ₐ[R] A where
  toFun a :=
    Quot.liftOn a (liftFun _ _ f) fun a b h ↦ by
      induction h
      · exact (algebraMap R A).map_add _ _
      · exact (algebraMap R A).map_mul _ _
      · apply Algebra.commutes
      · change _ + _ + _ = _ + (_ + _)
        rw [add_assoc]
      · change _ + _ = _ + _
        rw [add_comm]
      · change algebraMap _ _ _ + liftFun R X f _ = liftFun R X f _
        simp
      · change _ * _ * _ = _ * (_ * _)
        rw [mul_assoc]
      · change algebraMap _ _ _ * liftFun R X f _ = liftFun R X f _
        simp
      · change liftFun R X f _ * algebraMap _ _ _ = liftFun R X f _
        simp
      · change _ * (_ + _) = _ * _ + _ * _
        rw [left_distrib]
      · change (_ + _) * _ = _ * _ + _ * _
        rw [right_distrib]
      · change algebraMap _ _ _ * _ = algebraMap _ _ _
        simp
      · change _ * algebraMap _ _ _ = algebraMap _ _ _
        simp
      repeat
        change liftFun R X f _ + liftFun R X f _ = _
        simp only [*]
        rfl
      repeat
        change liftFun R X f _ * liftFun R X f _ = _
        simp only [*]
        rfl
  map_one' := by
    change algebraMap _ _ _ = _
    simp
  map_mul' := by
    rintro ⟨⟩ ⟨⟩
    rfl
  map_zero' := by
    dsimp
    change algebraMap _ _ _ = _
    simp
  map_add' := by
    rintro ⟨⟩ ⟨⟩
    rfl
  commutes' := by tauto
@[irreducible]
def lift : (X → A) ≃ (FreeAlgebra R X →ₐ[R] A) :=
  { toFun := liftAux R
    invFun := fun F ↦ F ∘ ι R
    left_inv := fun f ↦ by
      ext
      simp only [Function.comp_apply, ι_def]
      rfl
    right_inv := fun F ↦ by
      ext t
      rcases t with ⟨x⟩
      induction x with
      | of =>
        change ((F : FreeAlgebra R X → A) ∘ ι R) _ = _
        simp only [Function.comp_apply, ι_def]
      | ofScalar x =>
        change algebraMap _ _ x = F (algebraMap _ _ x)
        rw [AlgHom.commutes F _]
      | add a b ha hb =>
        let fa : FreeAlgebra R X := Quot.mk (Rel R X) a
        let fb : FreeAlgebra R X := Quot.mk (Rel R X) b
        change liftAux R (F ∘ ι R) (fa + fb) = F (fa + fb)
        rw [map_add, map_add, ha, hb]
      | mul a b ha hb =>
        let fa : FreeAlgebra R X := Quot.mk (Rel R X) a
        let fb : FreeAlgebra R X := Quot.mk (Rel R X) b
        change liftAux R (F ∘ ι R) (fa * fb) = F (fa * fb)
        rw [map_mul, map_mul, ha, hb] }
@[simp]
theorem liftAux_eq (f : X → A) : liftAux R f = lift R f := by
  rw [lift]
  rfl
@[simp]
theorem lift_symm_apply (F : FreeAlgebra R X →ₐ[R] A) : (lift R).symm F = F ∘ ι R := by
  rw [lift]
  rfl
variable {R}
@[simp]
theorem ι_comp_lift (f : X → A) : (lift R f : FreeAlgebra R X → A) ∘ ι R = f := by
  ext
  rw [Function.comp_apply, ι_def, lift]
  rfl
@[simp]
theorem lift_ι_apply (f : X → A) (x) : lift R f (ι R x) = f x := by
  rw [ι_def, lift]
  rfl
@[simp]
theorem lift_unique (f : X → A) (g : FreeAlgebra R X →ₐ[R] A) :
    (g : FreeAlgebra R X → A) ∘ ι R = f ↔ g = lift R f := by
  rw [← (lift R).symm_apply_eq, lift]
  rfl
@[simp]
theorem lift_comp_ι (g : FreeAlgebra R X →ₐ[R] A) :
    lift R ((g : FreeAlgebra R X → A) ∘ ι R) = g := by
  rw [← lift_symm_apply]
  exact (lift R).apply_symm_apply g
@[ext high]
theorem hom_ext {f g : FreeAlgebra R X →ₐ[R] A}
    (w : (f : FreeAlgebra R X → A) ∘ ι R = (g : FreeAlgebra R X → A) ∘ ι R) : f = g := by
  rw [← lift_symm_apply, ← lift_symm_apply] at w
  exact (lift R).symm.injective w
noncomputable def equivMonoidAlgebraFreeMonoid :
    FreeAlgebra R X ≃ₐ[R] MonoidAlgebra R (FreeMonoid X) :=
  AlgEquiv.ofAlgHom (lift R fun x ↦ (MonoidAlgebra.of R (FreeMonoid X)) (FreeMonoid.of x))
    ((MonoidAlgebra.lift R (FreeMonoid X) (FreeAlgebra R X)) (FreeMonoid.lift (ι R)))
    (by
      apply MonoidAlgebra.algHom_ext; intro x
      refine FreeMonoid.recOn x ?_ ?_
      · simp
        rfl
      · intro x y ih
        simp at ih
        simp [ih])
    (by
      ext
      simp)
instance [Nontrivial R] : Nontrivial (FreeAlgebra R X) :=
  equivMonoidAlgebraFreeMonoid.surjective.nontrivial
instance instNoZeroDivisors [NoZeroDivisors R] : NoZeroDivisors (FreeAlgebra R X) :=
  equivMonoidAlgebraFreeMonoid.toMulEquiv.noZeroDivisors
instance instIsDomain {R X} [CommRing R] [IsDomain R] : IsDomain (FreeAlgebra R X) :=
  NoZeroDivisors.to_isDomain _
section
def algebraMapInv : FreeAlgebra R X →ₐ[R] R :=
  lift R (0 : X → R)
theorem algebraMap_leftInverse :
    Function.LeftInverse algebraMapInv (algebraMap R <| FreeAlgebra R X) := fun x ↦ by
  simp [algebraMapInv]
@[simp]
theorem algebraMap_inj (x y : R) :
    algebraMap R (FreeAlgebra R X) x = algebraMap R (FreeAlgebra R X) y ↔ x = y :=
  algebraMap_leftInverse.injective.eq_iff
@[simp]
theorem algebraMap_eq_zero_iff (x : R) : algebraMap R (FreeAlgebra R X) x = 0 ↔ x = 0 :=
  map_eq_zero_iff (algebraMap _ _) algebraMap_leftInverse.injective
@[simp]
theorem algebraMap_eq_one_iff (x : R) : algebraMap R (FreeAlgebra R X) x = 1 ↔ x = 1 :=
  map_eq_one_iff (algebraMap _ _) algebraMap_leftInverse.injective
theorem ι_injective [Nontrivial R] : Function.Injective (ι R : X → FreeAlgebra R X) :=
  fun x y hoxy ↦
  by_contradiction <| by
    classical exact fun hxy : x ≠ y ↦
        let f : FreeAlgebra R X →ₐ[R] R := lift R fun z ↦ if x = z then (1 : R) else 0
        have hfx1 : f (ι R x) = 1 := (lift_ι_apply _ _).trans <| if_pos rfl
        have hfy1 : f (ι R y) = 1 := hoxy ▸ hfx1
        have hfy0 : f (ι R y) = 0 := (lift_ι_apply _ _).trans <| if_neg hxy
        one_ne_zero <| hfy1.symm.trans hfy0
@[simp]
theorem ι_inj [Nontrivial R] (x y : X) : ι R x = ι R y ↔ x = y :=
  ι_injective.eq_iff
@[simp]
theorem ι_ne_algebraMap [Nontrivial R] (x : X) (r : R) : ι R x ≠ algebraMap R _ r := fun h ↦ by
  let f0 : FreeAlgebra R X →ₐ[R] R := lift R 0
  let f1 : FreeAlgebra R X →ₐ[R] R := lift R 1
  have hf0 : f0 (ι R x) = 0 := lift_ι_apply _ _
  have hf1 : f1 (ι R x) = 1 := lift_ι_apply _ _
  rw [h, f0.commutes, Algebra.id.map_eq_self] at hf0
  rw [h, f1.commutes, Algebra.id.map_eq_self] at hf1
  exact zero_ne_one (hf0.symm.trans hf1)
@[simp]
theorem ι_ne_zero [Nontrivial R] (x : X) : ι R x ≠ 0 :=
  ι_ne_algebraMap x 0
@[simp]
theorem ι_ne_one [Nontrivial R] (x : X) : ι R x ≠ 1 :=
  ι_ne_algebraMap x 1
end
end FreeAlgebra
namespace FreeAlgebra
@[elab_as_elim, induction_eliminator]
theorem induction {C : FreeAlgebra R X → Prop}
    (h_grade0 : ∀ r, C (algebraMap R (FreeAlgebra R X) r)) (h_grade1 : ∀ x, C (ι R x))
    (h_mul : ∀ a b, C a → C b → C (a * b)) (h_add : ∀ a b, C a → C b → C (a + b))
    (a : FreeAlgebra R X) : C a := by
  let s : Subalgebra R (FreeAlgebra R X) :=
    { carrier := C
      mul_mem' := h_mul _ _
      add_mem' := h_add _ _
      algebraMap_mem' := h_grade0 }
  let of : X → s := Subtype.coind (ι R) h_grade1
  have of_id : AlgHom.id R (FreeAlgebra R X) = s.val.comp (lift R of) := by
    ext
    simp [of, Subtype.coind]
  suffices a = lift R of a by
    rw [this]
    exact Subtype.prop (lift R of a)
  simp [AlgHom.ext_iff] at of_id
  exact of_id a
@[simp]
theorem adjoin_range_ι : Algebra.adjoin R (Set.range (ι R : X → FreeAlgebra R X)) = ⊤ := by
  set S := Algebra.adjoin R (Set.range (ι R : X → FreeAlgebra R X))
  refine top_unique fun x hx => ?_; clear hx
  induction x with
  | h_grade0 => exact S.algebraMap_mem _
  | h_add x y hx hy => exact S.add_mem hx hy
  | h_mul x y hx hy => exact S.mul_mem hx hy
  | h_grade1 x => exact Algebra.subset_adjoin (Set.mem_range_self _)
variable {A : Type*} [Semiring A] [Algebra R A]
theorem _root_.Algebra.adjoin_range_eq_range_freeAlgebra_lift (f : X → A) :
    Algebra.adjoin R (Set.range f) = (FreeAlgebra.lift R f).range := by
  simp only [← Algebra.map_top, ← adjoin_range_ι, AlgHom.map_adjoin, ← Set.range_comp,
    Function.comp_def, lift_ι_apply]
theorem _root_.Algebra.adjoin_eq_range_freeAlgebra_lift (s : Set A) :
    Algebra.adjoin R s = (FreeAlgebra.lift R ((↑) : s → A)).range := by
  rw [← Algebra.adjoin_range_eq_range_freeAlgebra_lift, Subtype.range_coe]
end FreeAlgebra