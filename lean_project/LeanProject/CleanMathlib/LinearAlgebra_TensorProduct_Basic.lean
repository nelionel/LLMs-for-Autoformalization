import Mathlib.Algebra.Module.Submodule.Bilinear
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.GroupTheory.Congruence.Hom
import Mathlib.Tactic.Abel
import Mathlib.Tactic.SuppressCompilation
suppress_compilation
section Semiring
variable {R : Type*} [CommSemiring R]
variable {R' : Type*} [Monoid R']
variable {R'' : Type*} [Semiring R'']
variable {M : Type*} {N : Type*} {P : Type*} {Q : Type*} {S : Type*} {T : Type*}
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
variable [AddCommMonoid Q] [AddCommMonoid S] [AddCommMonoid T]
variable [Module R M] [Module R N] [Module R Q] [Module R S] [Module R T]
variable [DistribMulAction R' M]
variable [Module R'' M]
variable (M N)
namespace TensorProduct
section
variable (R)
inductive Eqv : FreeAddMonoid (M × N) → FreeAddMonoid (M × N) → Prop
  | of_zero_left : ∀ n : N, Eqv (.of (0, n)) 0
  | of_zero_right : ∀ m : M, Eqv (.of (m, 0)) 0
  | of_add_left : ∀ (m₁ m₂ : M) (n : N), Eqv (.of (m₁, n) + .of (m₂, n)) (.of (m₁ + m₂, n))
  | of_add_right : ∀ (m : M) (n₁ n₂ : N), Eqv (.of (m, n₁) + .of (m, n₂)) (.of (m, n₁ + n₂))
  | of_smul : ∀ (r : R) (m : M) (n : N), Eqv (.of (r • m, n)) (.of (m, r • n))
  | add_comm : ∀ x y, Eqv (x + y) (y + x)
end
end TensorProduct
variable (R)
def TensorProduct : Type _ :=
  (addConGen (TensorProduct.Eqv R M N)).Quotient
variable {R}
set_option quotPrecheck false in
@[inherit_doc TensorProduct] scoped[TensorProduct] infixl:100 " ⊗ " => TensorProduct _
@[inherit_doc] scoped[TensorProduct] notation:100 M " ⊗[" R "] " N:100 => TensorProduct R M N
namespace TensorProduct
section Module
protected instance zero : Zero (M ⊗[R] N) :=
  (addConGen (TensorProduct.Eqv R M N)).zero
protected instance add : Add (M ⊗[R] N) :=
  (addConGen (TensorProduct.Eqv R M N)).hasAdd
instance addZeroClass : AddZeroClass (M ⊗[R] N) :=
  { (addConGen (TensorProduct.Eqv R M N)).addMonoid with
    toAdd := TensorProduct.add _ _
    toZero := TensorProduct.zero _ _ }
instance addSemigroup : AddSemigroup (M ⊗[R] N) :=
  { (addConGen (TensorProduct.Eqv R M N)).addMonoid with
    toAdd := TensorProduct.add _ _ }
instance addCommSemigroup : AddCommSemigroup (M ⊗[R] N) :=
  { (addConGen (TensorProduct.Eqv R M N)).addMonoid with
    toAddSemigroup := TensorProduct.addSemigroup _ _
    add_comm := fun x y =>
      AddCon.induction_on₂ x y fun _ _ =>
        Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.add_comm _ _ }
instance : Inhabited (M ⊗[R] N) :=
  ⟨0⟩
variable (R) {M N}
def tmul (m : M) (n : N) : M ⊗[R] N :=
  AddCon.mk' _ <| FreeAddMonoid.of (m, n)
variable {R}
infixl:100 " ⊗ₜ " => tmul _
notation:100 x " ⊗ₜ[" R "] " y:100 => tmul R x y
@[elab_as_elim, induction_eliminator]
protected theorem induction_on {motive : M ⊗[R] N → Prop} (z : M ⊗[R] N)
    (zero : motive 0)
    (tmul : ∀ x y, motive <| x ⊗ₜ[R] y)
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  AddCon.induction_on z fun x =>
    FreeAddMonoid.recOn x zero fun ⟨m, n⟩ y ih => by
      rw [AddCon.coe_add]
      exact add _ _ (tmul ..) ih
def liftAddHom (f : M →+ N →+ P)
    (hf : ∀ (r : R) (m : M) (n : N), f (r • m) n = f m (r • n)) :
    M ⊗[R] N →+ P :=
  (addConGen (TensorProduct.Eqv R M N)).lift (FreeAddMonoid.lift (fun mn : M × N => f mn.1 mn.2)) <|
    AddCon.addConGen_le fun x y hxy =>
      match x, y, hxy with
      | _, _, .of_zero_left n =>
        (AddCon.ker_rel _).2 <| by simp_rw [map_zero, FreeAddMonoid.lift_eval_of, map_zero,
          AddMonoidHom.zero_apply]
      | _, _, .of_zero_right m =>
        (AddCon.ker_rel _).2 <| by simp_rw [map_zero, FreeAddMonoid.lift_eval_of, map_zero]
      | _, _, .of_add_left m₁ m₂ n =>
        (AddCon.ker_rel _).2 <| by simp_rw [map_add, FreeAddMonoid.lift_eval_of, map_add,
          AddMonoidHom.add_apply]
      | _, _, .of_add_right m n₁ n₂ =>
        (AddCon.ker_rel _).2 <| by simp_rw [map_add, FreeAddMonoid.lift_eval_of, map_add]
      | _, _, .of_smul s m n =>
        (AddCon.ker_rel _).2 <| by rw [FreeAddMonoid.lift_eval_of, FreeAddMonoid.lift_eval_of, hf]
      | _, _, .add_comm x y =>
        (AddCon.ker_rel _).2 <| by simp_rw [map_add, add_comm]
@[simp]
theorem liftAddHom_tmul (f : M →+ N →+ P)
    (hf : ∀ (r : R) (m : M) (n : N), f (r • m) n = f m (r • n)) (m : M) (n : N) :
    liftAddHom f hf (m ⊗ₜ n) = f m n :=
  rfl
variable (M)
@[simp]
theorem zero_tmul (n : N) : (0 : M) ⊗ₜ[R] n = 0 :=
  Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_zero_left _
variable {M}
theorem add_tmul (m₁ m₂ : M) (n : N) : (m₁ + m₂) ⊗ₜ n = m₁ ⊗ₜ n + m₂ ⊗ₜ[R] n :=
  Eq.symm <| Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_add_left _ _ _
variable (N)
@[simp]
theorem tmul_zero (m : M) : m ⊗ₜ[R] (0 : N) = 0 :=
  Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_zero_right _
variable {N}
theorem tmul_add (m : M) (n₁ n₂ : N) : m ⊗ₜ (n₁ + n₂) = m ⊗ₜ n₁ + m ⊗ₜ[R] n₂ :=
  Eq.symm <| Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_add_right _ _ _
instance uniqueLeft [Subsingleton M] : Unique (M ⊗[R] N) where
  default := 0
  uniq z := z.induction_on rfl (fun x y ↦ by rw [Subsingleton.elim x 0, zero_tmul]; rfl) <| by
    rintro _ _ rfl rfl; apply add_zero
instance uniqueRight [Subsingleton N] : Unique (M ⊗[R] N) where
  default := 0
  uniq z := z.induction_on rfl (fun x y ↦ by rw [Subsingleton.elim y 0, tmul_zero]; rfl) <| by
    rintro _ _ rfl rfl; apply add_zero
section
variable (R R' M N)
class CompatibleSMul [DistribMulAction R' N] : Prop where
  smul_tmul : ∀ (r : R') (m : M) (n : N), (r • m) ⊗ₜ n = m ⊗ₜ[R] (r • n)
end
instance (priority := 100) CompatibleSMul.isScalarTower [SMul R' R] [IsScalarTower R' R M]
    [DistribMulAction R' N] [IsScalarTower R' R N] : CompatibleSMul R R' M N :=
  ⟨fun r m n => by
    conv_lhs => rw [← one_smul R m]
    conv_rhs => rw [← one_smul R n]
    rw [← smul_assoc, ← smul_assoc]
    exact Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_smul _ _ _⟩
theorem smul_tmul [DistribMulAction R' N] [CompatibleSMul R R' M N] (r : R') (m : M) (n : N) :
    (r • m) ⊗ₜ n = m ⊗ₜ[R] (r • n) :=
  CompatibleSMul.smul_tmul _ _ _
private def addMonoidWithWrongNSMul : AddMonoid (M ⊗[R] N) :=
  { (addConGen (TensorProduct.Eqv R M N)).addMonoid with }
attribute [local instance] addMonoidWithWrongNSMul in
def SMul.aux {R' : Type*} [SMul R' M] (r : R') : FreeAddMonoid (M × N) →+ M ⊗[R] N :=
  FreeAddMonoid.lift fun p : M × N => (r • p.1) ⊗ₜ p.2
theorem SMul.aux_of {R' : Type*} [SMul R' M] (r : R') (m : M) (n : N) :
    SMul.aux r (.of (m, n)) = (r • m) ⊗ₜ[R] n :=
  rfl
variable [SMulCommClass R R' M] [SMulCommClass R R'' M]
instance leftHasSMul : SMul R' (M ⊗[R] N) :=
  ⟨fun r =>
    (addConGen (TensorProduct.Eqv R M N)).lift (SMul.aux r : _ →+ M ⊗[R] N) <|
      AddCon.addConGen_le fun x y hxy =>
        match x, y, hxy with
        | _, _, .of_zero_left n =>
          (AddCon.ker_rel _).2 <| by simp_rw [map_zero, SMul.aux_of, smul_zero, zero_tmul]
        | _, _, .of_zero_right m =>
          (AddCon.ker_rel _).2 <| by simp_rw [map_zero, SMul.aux_of, tmul_zero]
        | _, _, .of_add_left m₁ m₂ n =>
          (AddCon.ker_rel _).2 <| by simp_rw [map_add, SMul.aux_of, smul_add, add_tmul]
        | _, _, .of_add_right m n₁ n₂ =>
          (AddCon.ker_rel _).2 <| by simp_rw [map_add, SMul.aux_of, tmul_add]
        | _, _, .of_smul s m n =>
          (AddCon.ker_rel _).2 <| by rw [SMul.aux_of, SMul.aux_of, ← smul_comm, smul_tmul]
        | _, _, .add_comm x y =>
          (AddCon.ker_rel _).2 <| by simp_rw [map_add, add_comm]⟩
instance : SMul R (M ⊗[R] N) :=
  TensorProduct.leftHasSMul
protected theorem smul_zero (r : R') : r • (0 : M ⊗[R] N) = 0 :=
  AddMonoidHom.map_zero _
protected theorem smul_add (r : R') (x y : M ⊗[R] N) : r • (x + y) = r • x + r • y :=
  AddMonoidHom.map_add _ _ _
protected theorem zero_smul (x : M ⊗[R] N) : (0 : R'') • x = 0 :=
  have : ∀ (r : R'') (m : M) (n : N), r • m ⊗ₜ[R] n = (r • m) ⊗ₜ n := fun _ _ _ => rfl
  x.induction_on (by rw [TensorProduct.smul_zero])
    (fun m n => by rw [this, zero_smul, zero_tmul]) fun x y ihx ihy => by
    rw [TensorProduct.smul_add, ihx, ihy, add_zero]
protected theorem one_smul (x : M ⊗[R] N) : (1 : R') • x = x :=
  have : ∀ (r : R') (m : M) (n : N), r • m ⊗ₜ[R] n = (r • m) ⊗ₜ n := fun _ _ _ => rfl
  x.induction_on (by rw [TensorProduct.smul_zero])
    (fun m n => by rw [this, one_smul])
    fun x y ihx ihy => by rw [TensorProduct.smul_add, ihx, ihy]
protected theorem add_smul (r s : R'') (x : M ⊗[R] N) : (r + s) • x = r • x + s • x :=
  have : ∀ (r : R'') (m : M) (n : N), r • m ⊗ₜ[R] n = (r • m) ⊗ₜ n := fun _ _ _ => rfl
  x.induction_on (by simp_rw [TensorProduct.smul_zero, add_zero])
    (fun m n => by simp_rw [this, add_smul, add_tmul]) fun x y ihx ihy => by
    simp_rw [TensorProduct.smul_add]
    rw [ihx, ihy, add_add_add_comm]
instance addMonoid : AddMonoid (M ⊗[R] N) :=
  { TensorProduct.addZeroClass _ _ with
    toAddSemigroup := TensorProduct.addSemigroup _ _
    toZero := TensorProduct.zero _ _
    nsmul := fun n v => n • v
    nsmul_zero := by simp [TensorProduct.zero_smul]
    nsmul_succ := by simp only [TensorProduct.one_smul, TensorProduct.add_smul, add_comm,
      forall_const] }
instance addCommMonoid : AddCommMonoid (M ⊗[R] N) :=
  { TensorProduct.addCommSemigroup _ _ with
    toAddMonoid := TensorProduct.addMonoid }
instance leftDistribMulAction : DistribMulAction R' (M ⊗[R] N) :=
  have : ∀ (r : R') (m : M) (n : N), r • m ⊗ₜ[R] n = (r • m) ⊗ₜ n := fun _ _ _ => rfl
  { smul_add := fun r x y => TensorProduct.smul_add r x y
    mul_smul := fun r s x =>
      x.induction_on (by simp_rw [TensorProduct.smul_zero])
        (fun m n => by simp_rw [this, mul_smul]) fun x y ihx ihy => by
        simp_rw [TensorProduct.smul_add]
        rw [ihx, ihy]
    one_smul := TensorProduct.one_smul
    smul_zero := TensorProduct.smul_zero }
instance : DistribMulAction R (M ⊗[R] N) :=
  TensorProduct.leftDistribMulAction
theorem smul_tmul' (r : R') (m : M) (n : N) : r • m ⊗ₜ[R] n = (r • m) ⊗ₜ n :=
  rfl
@[simp]
theorem tmul_smul [DistribMulAction R' N] [CompatibleSMul R R' M N] (r : R') (x : M) (y : N) :
    x ⊗ₜ (r • y) = r • x ⊗ₜ[R] y :=
  (smul_tmul _ _ _).symm
theorem smul_tmul_smul (r s : R) (m : M) (n : N) : (r • m) ⊗ₜ[R] (s • n) = (r * s) • m ⊗ₜ[R] n := by
  simp_rw [smul_tmul, tmul_smul, mul_smul]
instance leftModule : Module R'' (M ⊗[R] N) :=
  { add_smul := TensorProduct.add_smul
    zero_smul := TensorProduct.zero_smul }
instance : Module R (M ⊗[R] N) :=
  TensorProduct.leftModule
instance [Module R''ᵐᵒᵖ M] [IsCentralScalar R'' M] : IsCentralScalar R'' (M ⊗[R] N) where
  op_smul_eq_smul r x :=
    x.induction_on (by rw [smul_zero, smul_zero])
      (fun x y => by rw [smul_tmul', smul_tmul', op_smul_eq_smul]) fun x y hx hy => by
      rw [smul_add, smul_add, hx, hy]
section
variable {R'₂ : Type*} [Monoid R'₂] [DistribMulAction R'₂ M]
variable [SMulCommClass R R'₂ M]
instance smulCommClass_left [SMulCommClass R' R'₂ M] : SMulCommClass R' R'₂ (M ⊗[R] N) where
  smul_comm r' r'₂ x :=
    TensorProduct.induction_on x (by simp_rw [TensorProduct.smul_zero])
      (fun m n => by simp_rw [smul_tmul', smul_comm]) fun x y ihx ihy => by
      simp_rw [TensorProduct.smul_add]; rw [ihx, ihy]
variable [SMul R'₂ R']
instance isScalarTower_left [IsScalarTower R'₂ R' M] : IsScalarTower R'₂ R' (M ⊗[R] N) :=
  ⟨fun s r x =>
    x.induction_on (by simp)
      (fun m n => by rw [smul_tmul', smul_tmul', smul_tmul', smul_assoc]) fun x y ihx ihy => by
      rw [smul_add, smul_add, smul_add, ihx, ihy]⟩
variable [DistribMulAction R'₂ N] [DistribMulAction R' N]
variable [CompatibleSMul R R'₂ M N] [CompatibleSMul R R' M N]
instance isScalarTower_right [IsScalarTower R'₂ R' N] : IsScalarTower R'₂ R' (M ⊗[R] N) :=
  ⟨fun s r x =>
    x.induction_on (by simp)
      (fun m n => by rw [← tmul_smul, ← tmul_smul, ← tmul_smul, smul_assoc]) fun x y ihx ihy => by
      rw [smul_add, smul_add, smul_add, ihx, ihy]⟩
end
instance isScalarTower [SMul R' R] [IsScalarTower R' R M] : IsScalarTower R' R (M ⊗[R] N) :=
  TensorProduct.isScalarTower_left
variable (R M N)
def mk : M →ₗ[R] N →ₗ[R] M ⊗[R] N :=
  LinearMap.mk₂ R (· ⊗ₜ ·) add_tmul (fun c m n => by simp_rw [smul_tmul, tmul_smul])
    tmul_add tmul_smul
variable {R M N}
@[simp]
theorem mk_apply (m : M) (n : N) : mk R M N m n = m ⊗ₜ n :=
  rfl
theorem ite_tmul (x₁ : M) (x₂ : N) (P : Prop) [Decidable P] :
    (if P then x₁ else 0) ⊗ₜ[R] x₂ = if P then x₁ ⊗ₜ x₂ else 0 := by split_ifs <;> simp
theorem tmul_ite (x₁ : M) (x₂ : N) (P : Prop) [Decidable P] :
    (x₁ ⊗ₜ[R] if P then x₂ else 0) = if P then x₁ ⊗ₜ x₂ else 0 := by split_ifs <;> simp
lemma tmul_single {ι : Type*} [DecidableEq ι] {M : ι → Type*} [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)] (i : ι) (x : N) (m : M i) (j : ι) :
    x ⊗ₜ[R] Pi.single i m j = (Pi.single i (x ⊗ₜ[R] m) : ∀ i, N ⊗[R] M i) j := by
  by_cases h : i = j <;> aesop
lemma single_tmul {ι : Type*} [DecidableEq ι] {M : ι → Type*} [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)] (i : ι) (x : N) (m : M i) (j : ι) :
    Pi.single i m j ⊗ₜ[R] x = (Pi.single i (m ⊗ₜ[R] x) : ∀ i, M i ⊗[R] N) j := by
  by_cases h : i = j <;> aesop
section
theorem sum_tmul {α : Type*} (s : Finset α) (m : α → M) (n : N) :
    (∑ a ∈ s, m a) ⊗ₜ[R] n = ∑ a ∈ s, m a ⊗ₜ[R] n := by
  classical
    induction' s using Finset.induction with a s has ih h
    · simp
    · simp [Finset.sum_insert has, add_tmul, ih]
theorem tmul_sum (m : M) {α : Type*} (s : Finset α) (n : α → N) :
    (m ⊗ₜ[R] ∑ a ∈ s, n a) = ∑ a ∈ s, m ⊗ₜ[R] n a := by
  classical
    induction' s using Finset.induction with a s has ih h
    · simp
    · simp [Finset.sum_insert has, tmul_add, ih]
end
variable (R M N)
theorem span_tmul_eq_top : Submodule.span R { t : M ⊗[R] N | ∃ m n, m ⊗ₜ n = t } = ⊤ := by
  ext t; simp only [Submodule.mem_top, iff_true]
  refine t.induction_on ?_ ?_ ?_
  · exact Submodule.zero_mem _
  · intro m n
    apply Submodule.subset_span
    use m, n
  · intro t₁ t₂ ht₁ ht₂
    exact Submodule.add_mem _ ht₁ ht₂
@[simp]
theorem map₂_mk_top_top_eq_top : Submodule.map₂ (mk R M N) ⊤ ⊤ = ⊤ := by
  rw [← top_le_iff, ← span_tmul_eq_top, Submodule.map₂_eq_span_image2]
  exact Submodule.span_mono fun _ ⟨m, n, h⟩ => ⟨m, trivial, n, trivial, h⟩
theorem exists_eq_tmul_of_forall (x : TensorProduct R M N)
    (h : ∀ (m₁ m₂ : M) (n₁ n₂ : N), ∃ m n, m₁ ⊗ₜ n₁ + m₂ ⊗ₜ n₂ = m ⊗ₜ[R] n) :
    ∃ m n, x = m ⊗ₜ n := by
  induction x with
  | zero =>
    use 0, 0
    rw [TensorProduct.zero_tmul]
  | tmul m n => use m, n
  | add x y h₁ h₂ =>
    obtain ⟨m₁, n₁, rfl⟩ := h₁
    obtain ⟨m₂, n₂, rfl⟩ := h₂
    apply h
end Module
variable [Module R P]
section UMP
variable {M N}
variable (f : M →ₗ[R] N →ₗ[R] P)
def liftAux : M ⊗[R] N →+ P :=
  liftAddHom (LinearMap.toAddMonoidHom'.comp <| f.toAddMonoidHom)
    fun r m n => by dsimp; rw [LinearMap.map_smul₂, map_smul]
theorem liftAux_tmul (m n) : liftAux f (m ⊗ₜ n) = f m n :=
  rfl
variable {f}
@[simp]
theorem liftAux.smul (r : R) (x) : liftAux f (r • x) = r • liftAux f x :=
  TensorProduct.induction_on x (smul_zero _).symm
    (fun p q => by simp_rw [← tmul_smul, liftAux_tmul, (f p).map_smul])
    fun p q ih1 ih2 => by simp_rw [smul_add, (liftAux f).map_add, ih1, ih2, smul_add]
variable (f)
def lift : M ⊗[R] N →ₗ[R] P :=
  { liftAux f with map_smul' := liftAux.smul }
variable {f}
@[simp]
theorem lift.tmul (x y) : lift f (x ⊗ₜ y) = f x y :=
  rfl
@[simp]
theorem lift.tmul' (x y) : (lift f).1 (x ⊗ₜ y) = f x y :=
  rfl
theorem ext' {g h : M ⊗[R] N →ₗ[R] P} (H : ∀ x y, g (x ⊗ₜ y) = h (x ⊗ₜ y)) : g = h :=
  LinearMap.ext fun z =>
    TensorProduct.induction_on z (by simp_rw [LinearMap.map_zero]) H fun x y ihx ihy => by
      rw [g.map_add, h.map_add, ihx, ihy]
theorem lift.unique {g : M ⊗[R] N →ₗ[R] P} (H : ∀ x y, g (x ⊗ₜ y) = f x y) : g = lift f :=
  ext' fun m n => by rw [H, lift.tmul]
theorem lift_mk : lift (mk R M N) = LinearMap.id :=
  Eq.symm <| lift.unique fun _ _ => rfl
theorem lift_compr₂ (g : P →ₗ[R] Q) : lift (f.compr₂ g) = g.comp (lift f) :=
  Eq.symm <| lift.unique fun _ _ => by simp
theorem lift_mk_compr₂ (f : M ⊗ N →ₗ[R] P) : lift ((mk R M N).compr₂ f) = f := by
  rw [lift_compr₂ f, lift_mk, LinearMap.comp_id]
section ScalarTower
variable (R M N A) [CommSemiring A] [Module A M] [Module A N] [SMulCommClass R A M]
  [CompatibleSMul R A M N]
def mapOfCompatibleSMul : M ⊗[A] N →ₗ[A] M ⊗[R] N :=
  lift
  { toFun := fun m ↦
    { __ := mk R M N m
      map_smul' := fun _ _ ↦ (smul_tmul _ _ _).symm }
    map_add' := fun _ _ ↦ LinearMap.ext <| by simp
    map_smul' := fun _ _ ↦ rfl }
@[simp] theorem mapOfCompatibleSMul_tmul (m n) : mapOfCompatibleSMul R M N A (m ⊗ₜ n) = m ⊗ₜ n :=
  rfl
attribute [local instance] SMulCommClass.symm
def mapOfCompatibleSMul' : M ⊗[A] N →ₗ[R] M ⊗[R] N where
  __ := mapOfCompatibleSMul R M N A
  map_smul' _ x := x.induction_on (map_zero _) (fun _ _ ↦ by simp [smul_tmul'])
    fun _ _ h h' ↦ by simpa using congr($h + $h')
theorem mapOfCompatibleSMul_surjective : Function.Surjective (mapOfCompatibleSMul R M N A) :=
  fun x ↦ x.induction_on (⟨0, map_zero _⟩) (fun m n ↦ ⟨_, mapOfCompatibleSMul_tmul ..⟩)
    fun _ _ ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x + y, by simpa using congr($hx + $hy)⟩
def equivOfCompatibleSMul [CompatibleSMul A R M N] : M ⊗[A] N ≃ₗ[A] M ⊗[R] N where
  __ := mapOfCompatibleSMul R M N A
  invFun := mapOfCompatibleSMul A M N R
  left_inv x := x.induction_on (map_zero _) (fun _ _ ↦ rfl)
    fun _ _ h h' ↦ by simpa using congr($h + $h')
  right_inv x := x.induction_on (map_zero _) (fun _ _ ↦ rfl)
    fun _ _ h h' ↦ by simpa using congr($h + $h')
end ScalarTower
theorem ext {g h : M ⊗ N →ₗ[R] P} (H : (mk R M N).compr₂ g = (mk R M N).compr₂ h) : g = h := by
  rw [← lift_mk_compr₂ g, H, lift_mk_compr₂]
attribute [local ext high] ext
example : M → N → (M → N → P) → P := fun m => flip fun f => f m
variable (R M N P)
def uncurry : (M →ₗ[R] N →ₗ[R] P) →ₗ[R] M ⊗[R] N →ₗ[R] P :=
  LinearMap.flip <| lift <| LinearMap.lflip.comp (LinearMap.flip LinearMap.id)
variable {R M N P}
@[simp]
theorem uncurry_apply (f : M →ₗ[R] N →ₗ[R] P) (m : M) (n : N) :
    uncurry R M N P f (m ⊗ₜ n) = f m n := by rw [uncurry, LinearMap.flip_apply, lift.tmul]; rfl
variable (R M N P)
def lift.equiv : (M →ₗ[R] N →ₗ[R] P) ≃ₗ[R] M ⊗[R] N →ₗ[R] P :=
  { uncurry R M N P with
    invFun := fun f => (mk R M N).compr₂ f
    left_inv := fun _ => LinearMap.ext₂ fun _ _ => lift.tmul _ _
    right_inv := fun _ => ext' fun _ _ => lift.tmul _ _ }
@[simp]
theorem lift.equiv_apply (f : M →ₗ[R] N →ₗ[R] P) (m : M) (n : N) :
    lift.equiv R M N P f (m ⊗ₜ n) = f m n :=
  uncurry_apply f m n
@[simp]
theorem lift.equiv_symm_apply (f : M ⊗[R] N →ₗ[R] P) (m : M) (n : N) :
    (lift.equiv R M N P).symm f m n = f (m ⊗ₜ n) :=
  rfl
def lcurry : (M ⊗[R] N →ₗ[R] P) →ₗ[R] M →ₗ[R] N →ₗ[R] P :=
  (lift.equiv R M N P).symm
variable {R M N P}
@[simp]
theorem lcurry_apply (f : M ⊗[R] N →ₗ[R] P) (m : M) (n : N) : lcurry R M N P f m n = f (m ⊗ₜ n) :=
  rfl
def curry (f : M ⊗[R] N →ₗ[R] P) : M →ₗ[R] N →ₗ[R] P :=
  lcurry R M N P f
@[simp]
theorem curry_apply (f : M ⊗ N →ₗ[R] P) (m : M) (n : N) : curry f m n = f (m ⊗ₜ n) :=
  rfl
theorem curry_injective : Function.Injective (curry : (M ⊗[R] N →ₗ[R] P) → M →ₗ[R] N →ₗ[R] P) :=
  fun _ _ H => ext H
theorem ext_threefold {g h : (M ⊗[R] N) ⊗[R] P →ₗ[R] Q}
    (H : ∀ x y z, g (x ⊗ₜ y ⊗ₜ z) = h (x ⊗ₜ y ⊗ₜ z)) : g = h := by
  ext x y z
  exact H x y z
@[deprecated (since := "2024-10-18")] alias ext₃ := ext_threefold
theorem ext_fourfold {g h : ((M ⊗[R] N) ⊗[R] P) ⊗[R] Q →ₗ[R] S}
    (H : ∀ w x y z, g (w ⊗ₜ x ⊗ₜ y ⊗ₜ z) = h (w ⊗ₜ x ⊗ₜ y ⊗ₜ z)) : g = h := by
  ext w x y z
  exact H w x y z
theorem ext_fourfold' {φ ψ : (M ⊗[R] N) ⊗[R] P ⊗[R] Q →ₗ[R] S}
    (H : ∀ w x y z, φ (w ⊗ₜ x ⊗ₜ (y ⊗ₜ z)) = ψ (w ⊗ₜ x ⊗ₜ (y ⊗ₜ z))) : φ = ψ := by
  ext m n p q
  exact H m n p q
end UMP
variable {M N}
section
variable (R M)
protected def lid : R ⊗[R] M ≃ₗ[R] M :=
  LinearEquiv.ofLinear (lift <| LinearMap.lsmul R M) (mk R R M 1) (LinearMap.ext fun _ => by simp)
    (ext' fun r m => by simp; rw [← tmul_smul, ← smul_tmul, smul_eq_mul, mul_one])
end
@[simp]
theorem lid_tmul (m : M) (r : R) : (TensorProduct.lid R M : R ⊗ M → M) (r ⊗ₜ m) = r • m :=
  rfl
@[simp]
theorem lid_symm_apply (m : M) : (TensorProduct.lid R M).symm m = 1 ⊗ₜ m :=
  rfl
section
variable (R M N)
protected def comm : M ⊗[R] N ≃ₗ[R] N ⊗[R] M :=
  LinearEquiv.ofLinear (lift (mk R N M).flip) (lift (mk R M N).flip) (ext' fun _ _ => rfl)
    (ext' fun _ _ => rfl)
@[simp]
theorem comm_tmul (m : M) (n : N) : (TensorProduct.comm R M N) (m ⊗ₜ n) = n ⊗ₜ m :=
  rfl
@[simp]
theorem comm_symm_tmul (m : M) (n : N) : (TensorProduct.comm R M N).symm (n ⊗ₜ m) = m ⊗ₜ n :=
  rfl
lemma lift_comp_comm_eq (f : M →ₗ[R] N →ₗ[R] P) :
    lift f ∘ₗ TensorProduct.comm R N M = lift f.flip :=
  ext rfl
end
section
variable (R M)
protected def rid : M ⊗[R] R ≃ₗ[R] M :=
  LinearEquiv.trans (TensorProduct.comm R M R) (TensorProduct.lid R M)
end
@[simp]
theorem rid_tmul (m : M) (r : R) : (TensorProduct.rid R M) (m ⊗ₜ r) = r • m :=
  rfl
@[simp]
theorem rid_symm_apply (m : M) : (TensorProduct.rid R M).symm m = m ⊗ₜ 1 :=
  rfl
variable (R) in
theorem lid_eq_rid : TensorProduct.lid R R = TensorProduct.rid R R :=
  LinearEquiv.toLinearMap_injective <| ext' mul_comm
open LinearMap
section
variable (R M N P)
protected def assoc : (M ⊗[R] N) ⊗[R] P ≃ₗ[R] M ⊗[R] N ⊗[R] P := by
  refine
      LinearEquiv.ofLinear (lift <| lift <| comp (lcurry R _ _ _) <| mk _ _ _)
        (lift <| comp (uncurry R _ _ _) <| curry <| mk _ _ _)
        (ext <| LinearMap.ext fun m => ext' fun n p => ?_)
        (ext <| flip_inj <| LinearMap.ext fun p => ext' fun m n => ?_) <;>
    repeat'
      first
        |rw [lift.tmul]|rw [compr₂_apply]|rw [comp_apply]|rw [mk_apply]|rw [flip_apply]
        |rw [lcurry_apply]|rw [uncurry_apply]|rw [curry_apply]|rw [id_apply]
end
@[simp]
theorem assoc_tmul (m : M) (n : N) (p : P) :
    (TensorProduct.assoc R M N P) (m ⊗ₜ n ⊗ₜ p) = m ⊗ₜ (n ⊗ₜ p) :=
  rfl
@[simp]
theorem assoc_symm_tmul (m : M) (n : N) (p : P) :
    (TensorProduct.assoc R M N P).symm (m ⊗ₜ (n ⊗ₜ p)) = m ⊗ₜ n ⊗ₜ p :=
  rfl
def map (f : M →ₗ[R] P) (g : N →ₗ[R] Q) : M ⊗[R] N →ₗ[R] P ⊗[R] Q :=
  lift <| comp (compl₂ (mk _ _ _) g) f
@[simp]
theorem map_tmul (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (m : M) (n : N) : map f g (m ⊗ₜ n) = f m ⊗ₜ g n :=
  rfl
lemma map_comp_comm_eq (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    map f g ∘ₗ TensorProduct.comm R N M = TensorProduct.comm R Q P ∘ₗ map g f :=
  ext rfl
lemma map_comm (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (x : N ⊗[R] M) :
    map f g (TensorProduct.comm R N M x) = TensorProduct.comm R Q P (map g f x) :=
  DFunLike.congr_fun (map_comp_comm_eq _ _) _
lemma map_map_comp_assoc_eq (f : M →ₗ[R] Q) (g : N →ₗ[R] S) (h : P →ₗ[R] T) :
    map f (map g h) ∘ₗ TensorProduct.assoc R M N P =
      TensorProduct.assoc R Q S T ∘ₗ map (map f g) h :=
  ext <| ext <| LinearMap.ext fun _ => LinearMap.ext fun _ => LinearMap.ext fun _ => rfl
lemma map_map_assoc (f : M →ₗ[R] Q) (g : N →ₗ[R] S) (h : P →ₗ[R] T) (x : (M ⊗[R] N) ⊗[R] P) :
    map f (map g h) (TensorProduct.assoc R M N P x) =
      TensorProduct.assoc R Q S T (map (map f g) h x) :=
  DFunLike.congr_fun (map_map_comp_assoc_eq _ _ _) _
lemma map_map_comp_assoc_symm_eq (f : M →ₗ[R] Q) (g : N →ₗ[R] S) (h : P →ₗ[R] T) :
    map (map f g) h ∘ₗ (TensorProduct.assoc R M N P).symm =
      (TensorProduct.assoc R Q S T).symm ∘ₗ map f (map g h) :=
  ext <| LinearMap.ext fun _ => ext <| LinearMap.ext fun _ => LinearMap.ext fun _ => rfl
lemma map_map_assoc_symm (f : M →ₗ[R] Q) (g : N →ₗ[R] S) (h : P →ₗ[R] T) (x : M ⊗[R] (N ⊗[R] P)) :
    map (map f g) h ((TensorProduct.assoc R M N P).symm x) =
      (TensorProduct.assoc R Q S T).symm (map f (map g h) x) :=
  DFunLike.congr_fun (map_map_comp_assoc_symm_eq _ _ _) _
theorem map_range_eq_span_tmul (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    range (map f g) = Submodule.span R { t | ∃ m n, f m ⊗ₜ g n = t } := by
  simp only [← Submodule.map_top, ← span_tmul_eq_top, Submodule.map_span, Set.mem_image,
    Set.mem_setOf_eq]
  congr; ext t
  constructor
  · rintro ⟨_, ⟨⟨m, n, rfl⟩, rfl⟩⟩
    use m, n
    simp only [map_tmul]
  · rintro ⟨m, n, rfl⟩
    refine ⟨_, ⟨⟨m, n, rfl⟩, ?_⟩⟩
    simp only [map_tmul]
@[simp]
def mapIncl (p : Submodule R P) (q : Submodule R Q) : p ⊗[R] q →ₗ[R] P ⊗[R] Q :=
  map p.subtype q.subtype
lemma range_mapIncl (p : Submodule R P) (q : Submodule R Q) :
    LinearMap.range (mapIncl p q) = Submodule.span R (Set.image2 (· ⊗ₜ ·) p q) := by
  rw [mapIncl, map_range_eq_span_tmul]
  congr; ext; simp
theorem map₂_eq_range_lift_comp_mapIncl (f : P →ₗ[R] Q →ₗ[R] M)
    (p : Submodule R P) (q : Submodule R Q) :
    Submodule.map₂ f p q = LinearMap.range (lift f ∘ₗ mapIncl p q) := by
  simp_rw [LinearMap.range_comp, range_mapIncl, Submodule.map_span,
    Set.image_image2, Submodule.map₂_eq_span_image2, lift.tmul]
section
variable {P' Q' : Type*}
variable [AddCommMonoid P'] [Module R P']
variable [AddCommMonoid Q'] [Module R Q']
theorem map_comp (f₂ : P →ₗ[R] P') (f₁ : M →ₗ[R] P) (g₂ : Q →ₗ[R] Q') (g₁ : N →ₗ[R] Q) :
    map (f₂.comp f₁) (g₂.comp g₁) = (map f₂ g₂).comp (map f₁ g₁) :=
  ext' fun _ _ => rfl
lemma range_mapIncl_mono {p p' : Submodule R P} {q q' : Submodule R Q} (hp : p ≤ p') (hq : q ≤ q') :
    LinearMap.range (mapIncl p q) ≤ LinearMap.range (mapIncl p' q') := by
  simp_rw [range_mapIncl]
  exact Submodule.span_mono (Set.image2_subset hp hq)
theorem lift_comp_map (i : P →ₗ[R] Q →ₗ[R] Q') (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    (lift i).comp (map f g) = lift ((i.comp f).compl₂ g) :=
  ext' fun _ _ => rfl
attribute [local ext high] ext
@[simp]
theorem map_id : map (id : M →ₗ[R] M) (id : N →ₗ[R] N) = .id := by
  ext
  simp only [mk_apply, id_coe, compr₂_apply, _root_.id, map_tmul]
@[simp]
protected theorem map_one : map (1 : M →ₗ[R] M) (1 : N →ₗ[R] N) = 1 :=
  map_id
protected theorem map_mul (f₁ f₂ : M →ₗ[R] M) (g₁ g₂ : N →ₗ[R] N) :
    map (f₁ * f₂) (g₁ * g₂) = map f₁ g₁ * map f₂ g₂ :=
  map_comp f₁ f₂ g₁ g₂
@[simp]
protected theorem map_pow (f : M →ₗ[R] M) (g : N →ₗ[R] N) (n : ℕ) :
    map f g ^ n = map (f ^ n) (g ^ n) := by
  induction n with
  | zero => simp only [pow_zero, TensorProduct.map_one]
  | succ n ih => simp only [pow_succ', ih, TensorProduct.map_mul]
theorem map_add_left (f₁ f₂ : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    map (f₁ + f₂) g = map f₁ g + map f₂ g := by
  ext
  simp only [add_tmul, compr₂_apply, mk_apply, map_tmul, add_apply]
theorem map_add_right (f : M →ₗ[R] P) (g₁ g₂ : N →ₗ[R] Q) :
    map f (g₁ + g₂) = map f g₁ + map f g₂ := by
  ext
  simp only [tmul_add, compr₂_apply, mk_apply, map_tmul, add_apply]
theorem map_smul_left (r : R) (f : M →ₗ[R] P) (g : N →ₗ[R] Q) : map (r • f) g = r • map f g := by
  ext
  simp only [smul_tmul, compr₂_apply, mk_apply, map_tmul, smul_apply, tmul_smul]
theorem map_smul_right (r : R) (f : M →ₗ[R] P) (g : N →ₗ[R] Q) : map f (r • g) = r • map f g := by
  ext
  simp only [smul_tmul, compr₂_apply, mk_apply, map_tmul, smul_apply, tmul_smul]
variable (R M N P Q)
def mapBilinear : (M →ₗ[R] P) →ₗ[R] (N →ₗ[R] Q) →ₗ[R] M ⊗[R] N →ₗ[R] P ⊗[R] Q :=
  LinearMap.mk₂ R map map_add_left map_smul_left map_add_right map_smul_right
def lTensorHomToHomLTensor : P ⊗[R] (M →ₗ[R] Q) →ₗ[R] M →ₗ[R] P ⊗[R] Q :=
  TensorProduct.lift (llcomp R M Q _ ∘ₗ mk R P Q)
def rTensorHomToHomRTensor : (M →ₗ[R] P) ⊗[R] Q →ₗ[R] M →ₗ[R] P ⊗[R] Q :=
  TensorProduct.lift (llcomp R M P _ ∘ₗ (mk R P Q).flip).flip
def homTensorHomMap : (M →ₗ[R] P) ⊗[R] (N →ₗ[R] Q) →ₗ[R] M ⊗[R] N →ₗ[R] P ⊗[R] Q :=
  lift (mapBilinear R M N P Q)
variable {R M N P Q}
def map₂ (f : M →ₗ[R] P →ₗ[R] Q) (g : N →ₗ[R] S →ₗ[R] T) :
    M ⊗[R] N →ₗ[R] P ⊗[R] S →ₗ[R] Q ⊗[R] T :=
  homTensorHomMap R _ _ _ _ ∘ₗ map f g
@[simp]
theorem mapBilinear_apply (f : M →ₗ[R] P) (g : N →ₗ[R] Q) : mapBilinear R M N P Q f g = map f g :=
  rfl
@[simp]
theorem lTensorHomToHomLTensor_apply (p : P) (f : M →ₗ[R] Q) (m : M) :
    lTensorHomToHomLTensor R M P Q (p ⊗ₜ f) m = p ⊗ₜ f m :=
  rfl
@[simp]
theorem rTensorHomToHomRTensor_apply (f : M →ₗ[R] P) (q : Q) (m : M) :
    rTensorHomToHomRTensor R M P Q (f ⊗ₜ q) m = f m ⊗ₜ q :=
  rfl
@[simp]
theorem homTensorHomMap_apply (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    homTensorHomMap R M N P Q (f ⊗ₜ g) = map f g :=
  rfl
@[simp]
theorem map₂_apply_tmul (f : M →ₗ[R] P →ₗ[R] Q) (g : N →ₗ[R] S →ₗ[R] T) (m : M) (n : N) :
    map₂ f g (m ⊗ₜ n) = map (f m) (g n) := rfl
@[simp]
theorem map_zero_left (g : N →ₗ[R] Q) : map (0 : M →ₗ[R] P) g = 0 :=
  (mapBilinear R M N P Q).map_zero₂ _
@[simp]
theorem map_zero_right (f : M →ₗ[R] P) : map f (0 : N →ₗ[R] Q) = 0 :=
  (mapBilinear R M N P Q _).map_zero
end
def congr (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) : M ⊗[R] N ≃ₗ[R] P ⊗[R] Q :=
  LinearEquiv.ofLinear (map f g) (map f.symm g.symm)
    (ext' fun m n => by simp)
    (ext' fun m n => by simp)
@[simp]
theorem congr_tmul (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) (m : M) (n : N) :
    congr f g (m ⊗ₜ n) = f m ⊗ₜ g n :=
  rfl
@[simp]
theorem congr_symm_tmul (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) (p : P) (q : Q) :
    (congr f g).symm (p ⊗ₜ q) = f.symm p ⊗ₜ g.symm q :=
  rfl
theorem congr_symm (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) : (congr f g).symm = congr f.symm g.symm := rfl
@[simp] theorem congr_refl_refl : congr (.refl R M) (.refl R N) = .refl R _ :=
  LinearEquiv.toLinearMap_injective <| ext' fun _ _ ↦ rfl
theorem congr_trans (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) (f' : P ≃ₗ[R] S) (g' : Q ≃ₗ[R] T) :
    congr (f ≪≫ₗ f') (g ≪≫ₗ g') = congr f g ≪≫ₗ congr f' g' :=
  LinearEquiv.toLinearMap_injective <| map_comp _ _ _ _
theorem congr_mul (f : M ≃ₗ[R] M) (g : N ≃ₗ[R] N) (f' : M ≃ₗ[R] M) (g' : N ≃ₗ[R] N) :
    congr (f * f') (g * g') = congr f g * congr f' g' := congr_trans _ _ _ _
@[simp] theorem congr_pow (f : M ≃ₗ[R] M) (g : N ≃ₗ[R] N) (n : ℕ) :
    congr f g ^ n = congr (f ^ n) (g ^ n) := by
  induction n with
  | zero => exact congr_refl_refl.symm
  | succ n ih => simp_rw [pow_succ, ih, congr_mul]
@[simp] theorem congr_zpow (f : M ≃ₗ[R] M) (g : N ≃ₗ[R] N) (n : ℤ) :
    congr f g ^ n = congr (f ^ n) (g ^ n) := by
  induction n with
  | ofNat n => exact congr_pow _ _ _
  | negSucc n => simp_rw [zpow_negSucc, congr_pow]; exact congr_symm _ _
variable (R M N P Q)
def leftComm : M ⊗[R] N ⊗[R] P ≃ₗ[R] N ⊗[R] M ⊗[R] P :=
  let e₁ := (TensorProduct.assoc R M N P).symm
  let e₂ := congr (TensorProduct.comm R M N) (1 : P ≃ₗ[R] P)
  let e₃ := TensorProduct.assoc R N M P
  e₁ ≪≫ₗ (e₂ ≪≫ₗ e₃)
variable {M N P Q}
@[simp]
theorem leftComm_tmul (m : M) (n : N) (p : P) : leftComm R M N P (m ⊗ₜ (n ⊗ₜ p)) = n ⊗ₜ (m ⊗ₜ p) :=
  rfl
@[simp]
theorem leftComm_symm_tmul (m : M) (n : N) (p : P) :
    (leftComm R M N P).symm (n ⊗ₜ (m ⊗ₜ p)) = m ⊗ₜ (n ⊗ₜ p) :=
  rfl
variable (M N P Q)
def tensorTensorTensorComm : (M ⊗[R] N) ⊗[R] P ⊗[R] Q ≃ₗ[R] (M ⊗[R] P) ⊗[R] N ⊗[R] Q :=
  let e₁ := TensorProduct.assoc R M N (P ⊗[R] Q)
  let e₂ := congr (1 : M ≃ₗ[R] M) (leftComm R N P Q)
  let e₃ := (TensorProduct.assoc R M P (N ⊗[R] Q)).symm
  e₁ ≪≫ₗ (e₂ ≪≫ₗ e₃)
variable {M N P Q}
@[simp]
theorem tensorTensorTensorComm_tmul (m : M) (n : N) (p : P) (q : Q) :
    tensorTensorTensorComm R M N P Q (m ⊗ₜ n ⊗ₜ (p ⊗ₜ q)) = m ⊗ₜ p ⊗ₜ (n ⊗ₜ q) :=
  rfl
@[simp]
theorem tensorTensorTensorComm_symm :
    (tensorTensorTensorComm R M N P Q).symm = tensorTensorTensorComm R M P N Q := by
  ext; rfl
variable (M N P Q)
def tensorTensorTensorAssoc : (M ⊗[R] N) ⊗[R] P ⊗[R] Q ≃ₗ[R] (M ⊗[R] N ⊗[R] P) ⊗[R] Q :=
  (TensorProduct.assoc R (M ⊗[R] N) P Q).symm ≪≫ₗ
    congr (TensorProduct.assoc R M N P) (1 : Q ≃ₗ[R] Q)
variable {M N P Q}
@[simp]
theorem tensorTensorTensorAssoc_tmul (m : M) (n : N) (p : P) (q : Q) :
    tensorTensorTensorAssoc R M N P Q (m ⊗ₜ n ⊗ₜ (p ⊗ₜ q)) = m ⊗ₜ (n ⊗ₜ p) ⊗ₜ q :=
  rfl
@[simp]
theorem tensorTensorTensorAssoc_symm_tmul (m : M) (n : N) (p : P) (q : Q) :
    (tensorTensorTensorAssoc R M N P Q).symm (m ⊗ₜ (n ⊗ₜ p) ⊗ₜ q) = m ⊗ₜ n ⊗ₜ (p ⊗ₜ q) :=
  rfl
end TensorProduct
open scoped TensorProduct
variable [Module R P]
namespace LinearMap
variable {N}
def lTensor (f : N →ₗ[R] P) : M ⊗[R] N →ₗ[R] M ⊗[R] P :=
  TensorProduct.map id f
def rTensor (f : N →ₗ[R] P) : N ⊗[R] M →ₗ[R] P ⊗[R] M :=
  TensorProduct.map f id
variable (g : P →ₗ[R] Q) (f : N →ₗ[R] P)
@[simp]
theorem lTensor_tmul (m : M) (n : N) : f.lTensor M (m ⊗ₜ n) = m ⊗ₜ f n :=
  rfl
@[simp]
theorem rTensor_tmul (m : M) (n : N) : f.rTensor M (n ⊗ₜ m) = f n ⊗ₜ m :=
  rfl
@[simp]
theorem lTensor_comp_mk (m : M) :
    f.lTensor M ∘ₗ TensorProduct.mk R M N m = TensorProduct.mk R M P m ∘ₗ f :=
  rfl
@[simp]
theorem rTensor_comp_flip_mk (m : M) :
    f.rTensor M ∘ₗ (TensorProduct.mk R N M).flip m = (TensorProduct.mk R P M).flip m ∘ₗ f :=
  rfl
lemma comm_comp_rTensor_comp_comm_eq (g : N →ₗ[R] P) :
    TensorProduct.comm R P Q ∘ₗ rTensor Q g ∘ₗ TensorProduct.comm R Q N =
      lTensor Q g :=
  TensorProduct.ext rfl
theorem rTensor_tensor : rTensor (M ⊗[R] N) g =
    TensorProduct.assoc R Q M N ∘ₗ rTensor N (rTensor M g) ∘ₗ (TensorProduct.assoc R P M N).symm :=
  TensorProduct.ext <| LinearMap.ext fun _ ↦ TensorProduct.ext rfl
lemma comm_comp_lTensor_comp_comm_eq (g : N →ₗ[R] P) :
    TensorProduct.comm R Q P ∘ₗ lTensor Q g ∘ₗ TensorProduct.comm R N Q =
      rTensor Q g :=
  TensorProduct.ext rfl
theorem lTensor_inj_iff_rTensor_inj :
    Function.Injective (lTensor M f) ↔ Function.Injective (rTensor M f) := by
  simp [← comm_comp_rTensor_comp_comm_eq]
theorem lTensor_surj_iff_rTensor_surj :
    Function.Surjective (lTensor M f) ↔ Function.Surjective (rTensor M f) := by
  simp [← comm_comp_rTensor_comp_comm_eq]
theorem lTensor_bij_iff_rTensor_bij :
    Function.Bijective (lTensor M f) ↔ Function.Bijective (rTensor M f) := by
  simp [← comm_comp_rTensor_comp_comm_eq]
open TensorProduct
attribute [local ext high] TensorProduct.ext
def lTensorHom : (N →ₗ[R] P) →ₗ[R] M ⊗[R] N →ₗ[R] M ⊗[R] P where
  toFun := lTensor M
  map_add' f g := by
    ext x y
    simp only [compr₂_apply, mk_apply, add_apply, lTensor_tmul, tmul_add]
  map_smul' r f := by
    dsimp
    ext x y
    simp only [compr₂_apply, mk_apply, tmul_smul, smul_apply, lTensor_tmul]
def rTensorHom : (N →ₗ[R] P) →ₗ[R] N ⊗[R] M →ₗ[R] P ⊗[R] M where
  toFun f := f.rTensor M
  map_add' f g := by
    ext x y
    simp only [compr₂_apply, mk_apply, add_apply, rTensor_tmul, add_tmul]
  map_smul' r f := by
    dsimp
    ext x y
    simp only [compr₂_apply, mk_apply, smul_tmul, tmul_smul, smul_apply, rTensor_tmul]
@[simp]
theorem coe_lTensorHom : (lTensorHom M : (N →ₗ[R] P) → M ⊗[R] N →ₗ[R] M ⊗[R] P) = lTensor M :=
  rfl
@[simp]
theorem coe_rTensorHom : (rTensorHom M : (N →ₗ[R] P) → N ⊗[R] M →ₗ[R] P ⊗[R] M) = rTensor M :=
  rfl
@[simp]
theorem lTensor_add (f g : N →ₗ[R] P) : (f + g).lTensor M = f.lTensor M + g.lTensor M :=
  (lTensorHom M).map_add f g
@[simp]
theorem rTensor_add (f g : N →ₗ[R] P) : (f + g).rTensor M = f.rTensor M + g.rTensor M :=
  (rTensorHom M).map_add f g
@[simp]
theorem lTensor_zero : lTensor M (0 : N →ₗ[R] P) = 0 :=
  (lTensorHom M).map_zero
@[simp]
theorem rTensor_zero : rTensor M (0 : N →ₗ[R] P) = 0 :=
  (rTensorHom M).map_zero
@[simp]
theorem lTensor_smul (r : R) (f : N →ₗ[R] P) : (r • f).lTensor M = r • f.lTensor M :=
  (lTensorHom M).map_smul r f
@[simp]
theorem rTensor_smul (r : R) (f : N →ₗ[R] P) : (r • f).rTensor M = r • f.rTensor M :=
  (rTensorHom M).map_smul r f
theorem lTensor_comp : (g.comp f).lTensor M = (g.lTensor M).comp (f.lTensor M) := by
  ext m n
  simp only [compr₂_apply, mk_apply, comp_apply, lTensor_tmul]
theorem lTensor_comp_apply (x : M ⊗[R] N) :
    (g.comp f).lTensor M x = (g.lTensor M) ((f.lTensor M) x) := by rw [lTensor_comp, coe_comp]; rfl
theorem rTensor_comp : (g.comp f).rTensor M = (g.rTensor M).comp (f.rTensor M) := by
  ext m n
  simp only [compr₂_apply, mk_apply, comp_apply, rTensor_tmul]
theorem rTensor_comp_apply (x : N ⊗[R] M) :
    (g.comp f).rTensor M x = (g.rTensor M) ((f.rTensor M) x) := by rw [rTensor_comp, coe_comp]; rfl
theorem lTensor_mul (f g : Module.End R N) : (f * g).lTensor M = f.lTensor M * g.lTensor M :=
  lTensor_comp M f g
theorem rTensor_mul (f g : Module.End R N) : (f * g).rTensor M = f.rTensor M * g.rTensor M :=
  rTensor_comp M f g
variable (N)
@[simp]
theorem lTensor_id : (id : N →ₗ[R] N).lTensor M = id :=
  map_id
theorem lTensor_id_apply (x : M ⊗[R] N) : (LinearMap.id : N →ₗ[R] N).lTensor M x = x := by
  rw [lTensor_id, id_coe, _root_.id]
@[simp]
theorem rTensor_id : (id : N →ₗ[R] N).rTensor M = id :=
  map_id
theorem rTensor_id_apply (x : N ⊗[R] M) : (LinearMap.id : N →ₗ[R] N).rTensor M x = x := by
  rw [rTensor_id, id_coe, _root_.id]
@[simp]
theorem lTensor_smul_action (r : R) :
    (DistribMulAction.toLinearMap R N r).lTensor M =
      DistribMulAction.toLinearMap R (M ⊗[R] N) r :=
  (lTensor_smul M r LinearMap.id).trans (congrArg _ (lTensor_id M N))
@[simp]
theorem rTensor_smul_action (r : R) :
    (DistribMulAction.toLinearMap R N r).rTensor M =
      DistribMulAction.toLinearMap R (N ⊗[R] M) r :=
  (rTensor_smul M r LinearMap.id).trans (congrArg _ (rTensor_id M N))
variable {N}
theorem lid_comp_rTensor (f : N →ₗ[R] R) :
    (TensorProduct.lid R M).comp (rTensor M f) = lift ((lsmul R M).comp f) := ext' fun _ _ ↦ rfl
@[simp]
theorem lTensor_comp_rTensor (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    (g.lTensor P).comp (f.rTensor N) = map f g := by
  simp only [lTensor, rTensor, ← map_comp, id_comp, comp_id]
@[simp]
theorem rTensor_comp_lTensor (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    (f.rTensor Q).comp (g.lTensor M) = map f g := by
  simp only [lTensor, rTensor, ← map_comp, id_comp, comp_id]
@[simp]
theorem map_comp_rTensor (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (f' : S →ₗ[R] M) :
    (map f g).comp (f'.rTensor _) = map (f.comp f') g := by
  simp only [lTensor, rTensor, ← map_comp, id_comp, comp_id]
@[simp]
theorem map_comp_lTensor (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (g' : S →ₗ[R] N) :
    (map f g).comp (g'.lTensor _) = map f (g.comp g') := by
  simp only [lTensor, rTensor, ← map_comp, id_comp, comp_id]
@[simp]
theorem rTensor_comp_map (f' : P →ₗ[R] S) (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    (f'.rTensor _).comp (map f g) = map (f'.comp f) g := by
  simp only [lTensor, rTensor, ← map_comp, id_comp, comp_id]
@[simp]
theorem lTensor_comp_map (g' : Q →ₗ[R] S) (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    (g'.lTensor _).comp (map f g) = map f (g'.comp g) := by
  simp only [lTensor, rTensor, ← map_comp, id_comp, comp_id]
variable {M}
@[simp]
theorem rTensor_pow (f : M →ₗ[R] M) (n : ℕ) : f.rTensor N ^ n = (f ^ n).rTensor N := by
  have h := TensorProduct.map_pow f (id : N →ₗ[R] N) n
  rwa [id_pow] at h
@[simp]
theorem lTensor_pow (f : N →ₗ[R] N) (n : ℕ) : f.lTensor M ^ n = (f ^ n).lTensor M := by
  have h := TensorProduct.map_pow (id : M →ₗ[R] M) f n
  rwa [id_pow] at h
end LinearMap
namespace LinearEquiv
variable {N}
def lTensor (f : N ≃ₗ[R] P) : M ⊗[R] N ≃ₗ[R] M ⊗[R] P := TensorProduct.congr (refl R M) f
def rTensor (f : N ≃ₗ[R] P) : N ⊗[R] M ≃ₗ[R] P ⊗[R] M := TensorProduct.congr f (refl R M)
variable (g : P ≃ₗ[R] Q) (f : N ≃ₗ[R] P) (m : M) (n : N) (p : P) (x : M ⊗[R] N) (y : N ⊗[R] M)
@[simp] theorem coe_lTensor : lTensor M f = (f : N →ₗ[R] P).lTensor M := rfl
@[simp] theorem coe_lTensor_symm : (lTensor M f).symm = (f.symm : P →ₗ[R] N).lTensor M := rfl
@[simp] theorem coe_rTensor : rTensor M f = (f : N →ₗ[R] P).rTensor M := rfl
@[simp] theorem coe_rTensor_symm : (rTensor M f).symm = (f.symm : P →ₗ[R] N).rTensor M := rfl
@[simp] theorem lTensor_tmul : f.lTensor M (m ⊗ₜ n) = m ⊗ₜ f n := rfl
@[simp] theorem lTensor_symm_tmul : (f.lTensor M).symm (m ⊗ₜ p) = m ⊗ₜ f.symm p := rfl
@[simp] theorem rTensor_tmul : f.rTensor M (n ⊗ₜ m) = f n ⊗ₜ m := rfl
@[simp] theorem rTensor_symm_tmul : (f.rTensor M).symm (p ⊗ₜ m) = f.symm p ⊗ₜ m := rfl
lemma comm_trans_rTensor_trans_comm_eq (g : N ≃ₗ[R] P) :
    TensorProduct.comm R Q N ≪≫ₗ rTensor Q g ≪≫ₗ TensorProduct.comm R P Q = lTensor Q g :=
  toLinearMap_injective <| TensorProduct.ext rfl
lemma comm_trans_lTensor_trans_comm_eq (g : N ≃ₗ[R] P) :
    TensorProduct.comm R N Q ≪≫ₗ lTensor Q g ≪≫ₗ TensorProduct.comm R Q P = rTensor Q g :=
  toLinearMap_injective <| TensorProduct.ext rfl
theorem lTensor_trans : (f ≪≫ₗ g).lTensor M = f.lTensor M ≪≫ₗ g.lTensor M :=
  toLinearMap_injective <| LinearMap.lTensor_comp M _ _
theorem lTensor_trans_apply : (f ≪≫ₗ g).lTensor M x = g.lTensor M (f.lTensor M x) :=
  LinearMap.lTensor_comp_apply M _ _ x
theorem rTensor_trans : (f ≪≫ₗ g).rTensor M = f.rTensor M ≪≫ₗ g.rTensor M :=
  toLinearMap_injective <| LinearMap.rTensor_comp M _ _
theorem rTensor_trans_apply : (f ≪≫ₗ g).rTensor M y = g.rTensor M (f.rTensor M y) :=
  LinearMap.rTensor_comp_apply M _ _ y
theorem lTensor_mul (f g : N ≃ₗ[R] N) : (f * g).lTensor M = f.lTensor M * g.lTensor M :=
  lTensor_trans M f g
theorem rTensor_mul (f g : N ≃ₗ[R] N) : (f * g).rTensor M = f.rTensor M * g.rTensor M :=
  rTensor_trans M f g
variable (N)
@[simp] theorem lTensor_refl : (refl R N).lTensor M = refl R _ := TensorProduct.congr_refl_refl
theorem lTensor_refl_apply : (refl R N).lTensor M x = x := by rw [lTensor_refl, refl_apply]
@[simp] theorem rTensor_refl : (refl R N).rTensor M = refl R _ := TensorProduct.congr_refl_refl
theorem rTensor_refl_apply : (refl R N).rTensor M y = y := by rw [rTensor_refl, refl_apply]
variable {N}
@[simp] theorem rTensor_trans_lTensor (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) :
    f.rTensor N ≪≫ₗ g.lTensor P = TensorProduct.congr f g :=
  toLinearMap_injective <| LinearMap.lTensor_comp_rTensor M _ _
@[simp] theorem lTensor_trans_rTensor (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) :
    g.lTensor M ≪≫ₗ f.rTensor Q = TensorProduct.congr f g :=
  toLinearMap_injective <| LinearMap.rTensor_comp_lTensor M _ _
@[simp] theorem rTensor_trans_congr (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) (f' : S ≃ₗ[R] M) :
    f'.rTensor _ ≪≫ₗ TensorProduct.congr f g = TensorProduct.congr (f' ≪≫ₗ f) g :=
  toLinearMap_injective <| LinearMap.map_comp_rTensor M _ _ _
@[simp] theorem lTensor_trans_congr (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) (g' : S ≃ₗ[R] N) :
    g'.lTensor _ ≪≫ₗ TensorProduct.congr f g = TensorProduct.congr f (g' ≪≫ₗ g) :=
  toLinearMap_injective <| LinearMap.map_comp_lTensor M _ _ _
@[simp] theorem congr_trans_rTensor (f' : P ≃ₗ[R] S) (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) :
    TensorProduct.congr f g ≪≫ₗ f'.rTensor _ = TensorProduct.congr (f ≪≫ₗ f') g :=
  toLinearMap_injective <| LinearMap.rTensor_comp_map M _ _ _
@[simp] theorem congr_trans_lTensor (g' : Q ≃ₗ[R] S) (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) :
    TensorProduct.congr f g ≪≫ₗ g'.lTensor _ = TensorProduct.congr f (g ≪≫ₗ g') :=
  toLinearMap_injective <| LinearMap.lTensor_comp_map M _ _ _
variable {M}
@[simp] theorem rTensor_pow (f : M ≃ₗ[R] M) (n : ℕ) : f.rTensor N ^ n = (f ^ n).rTensor N := by
  simpa only [one_pow] using TensorProduct.congr_pow f (1 : N ≃ₗ[R] N) n
@[simp] theorem rTensor_zpow (f : M ≃ₗ[R] M) (n : ℤ) : f.rTensor N ^ n = (f ^ n).rTensor N := by
  simpa only [one_zpow] using TensorProduct.congr_zpow f (1 : N ≃ₗ[R] N) n
@[simp] theorem lTensor_pow (f : N ≃ₗ[R] N) (n : ℕ) : f.lTensor M ^ n = (f ^ n).lTensor M := by
  simpa only [one_pow] using TensorProduct.congr_pow (1 : M ≃ₗ[R] M) f n
@[simp] theorem lTensor_zpow (f : N ≃ₗ[R] N) (n : ℤ) : f.lTensor M ^ n = (f ^ n).lTensor M := by
  simpa only [one_zpow] using TensorProduct.congr_zpow (1 : M ≃ₗ[R] M) f n
end LinearEquiv
end Semiring
section Ring
variable {R : Type*} [CommSemiring R]
variable {M : Type*} {N : Type*} {P : Type*} {Q : Type*} {S : Type*}
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q] [AddCommGroup S]
variable [Module R M] [Module R N] [Module R P] [Module R Q] [Module R S]
namespace TensorProduct
open TensorProduct
open LinearMap
variable (R)
def Neg.aux : M ⊗[R] N →ₗ[R] M ⊗[R] N :=
  lift <| (mk R M N).comp (-LinearMap.id)
variable {R}
instance neg : Neg (M ⊗[R] N) where
  neg := Neg.aux R
protected theorem neg_add_cancel (x : M ⊗[R] N) : -x + x = 0 :=
  x.induction_on
    (by rw [add_zero]; apply (Neg.aux R).map_zero)
    (fun x y => by convert (add_tmul (R := R) (-x) x y).symm; rw [neg_add_cancel, zero_tmul])
    fun x y hx hy => by
    suffices -x + x + (-y + y) = 0 by
      rw [← this]
      unfold Neg.neg neg
      simp only
      rw [map_add]
      abel
    rw [hx, hy, add_zero]
instance addCommGroup : AddCommGroup (M ⊗[R] N) :=
  { TensorProduct.addCommMonoid with
    neg := Neg.neg
    sub := _
    sub_eq_add_neg := fun _ _ => rfl
    neg_add_cancel := fun x => TensorProduct.neg_add_cancel x
    zsmul := fun n v => n • v
    zsmul_zero' := by simp [TensorProduct.zero_smul]
    zsmul_succ' := by simp [add_comm, TensorProduct.one_smul, TensorProduct.add_smul]
    zsmul_neg' := fun n x => by
      change (-n.succ : ℤ) • x = -(((n : ℤ) + 1) • x)
      rw [← zero_add (_ • x), ← TensorProduct.neg_add_cancel ((n.succ : ℤ) • x), add_assoc,
        ← add_smul, ← sub_eq_add_neg, sub_self, zero_smul, add_zero]
      rfl }
theorem neg_tmul (m : M) (n : N) : (-m) ⊗ₜ n = -m ⊗ₜ[R] n :=
  rfl
theorem tmul_neg (m : M) (n : N) : m ⊗ₜ (-n) = -m ⊗ₜ[R] n :=
  (mk R M N _).map_neg _
theorem tmul_sub (m : M) (n₁ n₂ : N) : m ⊗ₜ (n₁ - n₂) = m ⊗ₜ[R] n₁ - m ⊗ₜ[R] n₂ :=
  (mk R M N _).map_sub _ _
theorem sub_tmul (m₁ m₂ : M) (n : N) : (m₁ - m₂) ⊗ₜ n = m₁ ⊗ₜ[R] n - m₂ ⊗ₜ[R] n :=
  (mk R M N).map_sub₂ _ _ _
instance CompatibleSMul.int : CompatibleSMul R ℤ M N :=
  ⟨fun r m n =>
    Int.induction_on r (by simp) (fun r ih => by simpa [add_smul, tmul_add, add_tmul] using ih)
      fun r ih => by simpa [sub_smul, tmul_sub, sub_tmul] using ih⟩
instance CompatibleSMul.unit {S} [Monoid S] [DistribMulAction S M] [DistribMulAction S N]
    [CompatibleSMul R S M N] : CompatibleSMul R Sˣ M N :=
  ⟨fun s m n => (CompatibleSMul.smul_tmul (s : S) m n : _)⟩
end TensorProduct
namespace LinearMap
@[simp]
theorem lTensor_sub (f g : N →ₗ[R] P) : (f - g).lTensor M = f.lTensor M - g.lTensor M := by
  simp_rw [← coe_lTensorHom]
  exact (lTensorHom (R := R) (N := N) (P := P) M).map_sub f g
@[simp]
theorem rTensor_sub (f g : N →ₗ[R] P) : (f - g).rTensor M = f.rTensor M - g.rTensor M := by
  simp only [← coe_rTensorHom]
  exact (rTensorHom (R := R) (N := N) (P := P) M).map_sub f g
@[simp]
theorem lTensor_neg (f : N →ₗ[R] P) : (-f).lTensor M = -f.lTensor M := by
  simp only [← coe_lTensorHom]
  exact (lTensorHom (R := R) (N := N) (P := P) M).map_neg f
@[simp]
theorem rTensor_neg (f : N →ₗ[R] P) : (-f).rTensor M = -f.rTensor M := by
  simp only [← coe_rTensorHom]
  exact (rTensorHom (R := R) (N := N) (P := P) M).map_neg f
end LinearMap
end Ring
set_option linter.style.longFile 1700