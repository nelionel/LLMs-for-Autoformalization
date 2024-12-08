import Mathlib.LinearAlgebra.CliffordAlgebra.Fold
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
namespace CliffordAlgebra
universe uR uM uA uB
variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommGroup M] [Module R M]
variable {Q : QuadraticForm R M}
variable {A : Type uA} {B : Type uB} [Ring A] [Ring B] [Algebra R A] [Algebra R B]
open scoped DirectSum
variable (Q)
def even : Subalgebra R (CliffordAlgebra Q) :=
  (evenOdd Q 0).toSubalgebra (SetLike.one_mem_graded _) fun _x _y hx hy =>
    add_zero (0 : ZMod 2) ▸ SetLike.mul_mem_graded hx hy
instance : AddCommMonoid (even Q) := AddSubmonoidClass.toAddCommMonoid _
@[simp]
theorem even_toSubmodule : Subalgebra.toSubmodule (even Q) = evenOdd Q 0 :=
  rfl
variable (A)
@[ext]
structure EvenHom : Type max uA uM where
  bilin : M →ₗ[R] M →ₗ[R] A
  contract (m : M) : bilin m m = algebraMap R A (Q m)
  contract_mid (m₁ m₂ m₃ : M) : bilin m₁ m₂ * bilin m₂ m₃ = Q m₂ • bilin m₁ m₃
variable {A Q}
@[simps]
def EvenHom.compr₂ (g : EvenHom Q A) (f : A →ₐ[R] B) : EvenHom Q B where
  bilin := g.bilin.compr₂ f.toLinearMap
  contract _m := (f.congr_arg <| g.contract _).trans <| f.commutes _
  contract_mid _m₁ _m₂ _m₃ :=
    (map_mul f _ _).symm.trans <| (f.congr_arg <| g.contract_mid _ _ _).trans <| map_smul f _ _
variable (Q)
nonrec def even.ι : EvenHom Q (even Q) where
  bilin :=
    LinearMap.mk₂ R (fun m₁ m₂ => ⟨ι Q m₁ * ι Q m₂, ι_mul_ι_mem_evenOdd_zero Q _ _⟩)
      (fun _ _ _ => by simp only [LinearMap.map_add, add_mul]; rfl)
      (fun _ _ _ => by simp only [LinearMap.map_smul, smul_mul_assoc]; rfl)
      (fun _ _ _ => by simp only [LinearMap.map_add, mul_add]; rfl) fun _ _ _ => by
      simp only [LinearMap.map_smul, mul_smul_comm]; rfl
  contract m := Subtype.ext <| ι_sq_scalar Q m
  contract_mid m₁ m₂ m₃ :=
    Subtype.ext <|
      calc
        ι Q m₁ * ι Q m₂ * (ι Q m₂ * ι Q m₃) = ι Q m₁ * (ι Q m₂ * ι Q m₂ * ι Q m₃) := by
          simp only [mul_assoc]
        _ = Q m₂ • (ι Q m₁ * ι Q m₃) := by rw [Algebra.smul_def, ι_sq_scalar, Algebra.left_comm]
instance : Inhabited (EvenHom Q (even Q)) :=
  ⟨even.ι Q⟩
variable (f : EvenHom Q A)
@[ext high]
theorem even.algHom_ext ⦃f g : even Q →ₐ[R] A⦄ (h : (even.ι Q).compr₂ f = (even.ι Q).compr₂ g) :
    f = g := by
  rw [EvenHom.ext_iff] at h
  ext ⟨x, hx⟩
  induction x, hx using even_induction with
  | algebraMap r =>
    exact (f.commutes r).trans (g.commutes r).symm
  | add x y hx hy ihx ihy =>
    have := congr_arg₂ (· + ·) ihx ihy
    exact (map_add f _ _).trans (this.trans <| (map_add g _ _).symm)
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    have := congr_arg₂ (· * ·) (LinearMap.congr_fun (LinearMap.congr_fun h m₁) m₂) ih
    exact (map_mul f _ _).trans (this.trans <| (map_mul g _ _).symm)
variable {Q}
namespace even.lift
private def S : Submodule R (M →ₗ[R] A) :=
  Submodule.span R
    {f' | ∃ x m₂, f' = LinearMap.lcomp R _ (f.bilin.flip m₂) (LinearMap.mulRight R x)}
private def fFold : M →ₗ[R] A × S f →ₗ[R] A × S f :=
  LinearMap.mk₂ R
    (fun m acc =>
      (acc.2.val m,
        ⟨(LinearMap.mulRight R acc.1).comp (f.bilin.flip m), Submodule.subset_span <| ⟨_, _, rfl⟩⟩))
    (fun m₁ m₂ a =>
      Prod.ext (LinearMap.map_add _ m₁ m₂)
        (Subtype.ext <|
          LinearMap.ext fun m₃ =>
            show f.bilin m₃ (m₁ + m₂) * a.1 = f.bilin m₃ m₁ * a.1 + f.bilin m₃ m₂ * a.1 by
              rw [map_add, add_mul]))
    (fun c m a =>
      Prod.ext (LinearMap.map_smul _ c m)
        (Subtype.ext <|
          LinearMap.ext fun m₃ =>
            show f.bilin m₃ (c • m) * a.1 = c • (f.bilin m₃ m * a.1) by
              rw [LinearMap.map_smul, smul_mul_assoc]))
    (fun _ _ _ => Prod.ext rfl (Subtype.ext <| LinearMap.ext fun _ => mul_add _ _ _))
    fun _ _ _ => Prod.ext rfl (Subtype.ext <| LinearMap.ext fun _ => mul_smul_comm _ _ _)
@[simp]
private theorem fst_fFold_fFold (m₁ m₂ : M) (x : A × S f) :
    (fFold f m₁ (fFold f m₂ x)).fst = f.bilin m₁ m₂ * x.fst :=
  rfl
@[simp]
private theorem snd_fFold_fFold (m₁ m₂ m₃ : M) (x : A × S f) :
    ((fFold f m₁ (fFold f m₂ x)).snd : M →ₗ[R] A) m₃ = f.bilin m₃ m₁ * (x.snd : M →ₗ[R] A) m₂ :=
  rfl
private theorem fFold_fFold (m : M) (x : A × S f) : fFold f m (fFold f m x) = Q m • x := by
  obtain ⟨a, ⟨g, hg⟩⟩ := x
  ext : 2
  · change f.bilin m m * a = Q m • a
    rw [Algebra.smul_def, f.contract]
  · ext m₁
    change f.bilin _ _ * g m = Q m • g m₁
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hg
    · rintro _ ⟨b, m₃, rfl⟩
      change f.bilin _ _ * (f.bilin _ _ * b) = Q m • (f.bilin _ _ * b)
      rw [← smul_mul_assoc, ← mul_assoc, f.contract_mid]
    · change f.bilin m₁ m * 0 = Q m • (0 : A)  
      rw [mul_zero, smul_zero]
    · rintro x y _hx _hy ihx ihy
      rw [LinearMap.add_apply, LinearMap.add_apply, mul_add, smul_add, ihx, ihy]
    · rintro x hx _c ihx
      rw [LinearMap.smul_apply, LinearMap.smul_apply, mul_smul_comm, ihx, smul_comm]
@[simps! (config := .lemmasOnly) apply]
def aux (f : EvenHom Q A) : CliffordAlgebra.even Q →ₗ[R] A := by
  refine ?_ ∘ₗ (even Q).val.toLinearMap
  letI : AddCommGroup (S f) := AddSubgroupClass.toAddCommGroup _
  exact LinearMap.fst R _ _ ∘ₗ foldr Q (fFold f) (fFold_fFold f) (1, 0)
@[simp, nolint simpNF] 
theorem aux_one : aux f 1 = 1 :=
  congr_arg Prod.fst (foldr_one _ _ _ _)
@[simp, nolint simpNF] 
theorem aux_ι (m₁ m₂ : M) : aux f ((even.ι Q).bilin m₁ m₂) = f.bilin m₁ m₂ :=
  (congr_arg Prod.fst (foldr_mul _ _ _ _ _ _)).trans
    (by
      rw [foldr_ι, foldr_ι]
      exact mul_one _)
@[simp, nolint simpNF] 
theorem aux_algebraMap (r) (hr) : aux f ⟨algebraMap R _ r, hr⟩ = algebraMap R _ r :=
  (congr_arg Prod.fst (foldr_algebraMap _ _ _ _ _)).trans (Algebra.algebraMap_eq_smul_one r).symm
@[simp, nolint simpNF] 
theorem aux_mul (x y : even Q) : aux f (x * y) = aux f x * aux f y := by
  cases' x with x x_property
  cases y
  refine (congr_arg Prod.fst (foldr_mul _ _ _ _ _ _)).trans ?_
  dsimp only
  induction x, x_property using even_induction Q with
  | algebraMap r =>
    rw [foldr_algebraMap, aux_algebraMap]
    exact Algebra.smul_def r _
  | add x y hx hy ihx ihy =>
    rw [LinearMap.map_add, Prod.fst_add, ihx, ihy, ← add_mul, ← LinearMap.map_add]
    rfl
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    rw [aux_apply, foldr_mul, foldr_mul, foldr_ι, foldr_ι, fst_fFold_fFold, ih, ← mul_assoc,
      Subtype.coe_mk, foldr_mul, foldr_mul, foldr_ι, foldr_ι, fst_fFold_fFold]
    rfl
end even.lift
open even.lift
variable (Q)
@[simps! symm_apply_bilin]
def even.lift : EvenHom Q A ≃ (CliffordAlgebra.even Q →ₐ[R] A) where
  toFun f := AlgHom.ofLinearMap (aux f) (aux_one f) (aux_mul f)
  invFun F := (even.ι Q).compr₂ F
  left_inv f := EvenHom.ext <| LinearMap.ext₂ <| even.lift.aux_ι f
  right_inv _ := even.algHom_ext Q <| EvenHom.ext <| LinearMap.ext₂ <| even.lift.aux_ι _
theorem even.lift_ι (f : EvenHom Q A) (m₁ m₂ : M) :
    even.lift Q f ((even.ι Q).bilin m₁ m₂) = f.bilin m₁ m₂ :=
  even.lift.aux_ι _ _ _
end CliffordAlgebra