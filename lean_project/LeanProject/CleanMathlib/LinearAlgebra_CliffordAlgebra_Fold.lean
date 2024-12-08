import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
universe u1 u2 u3
variable {R M N : Type*}
variable [CommRing R] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N]
variable (Q : QuadraticForm R M)
namespace CliffordAlgebra
section Foldr
def foldr (f : M →ₗ[R] N →ₗ[R] N) (hf : ∀ m x, f m (f m x) = Q m • x) :
    N →ₗ[R] CliffordAlgebra Q →ₗ[R] N :=
  (CliffordAlgebra.lift Q ⟨f, fun v => LinearMap.ext <| hf v⟩).toLinearMap.flip
@[simp]
theorem foldr_ι (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) (m : M) : foldr Q f hf n (ι Q m) = f m n :=
  LinearMap.congr_fun (lift_ι_apply _ _ _) n
@[simp]
theorem foldr_algebraMap (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) (r : R) :
    foldr Q f hf n (algebraMap R _ r) = r • n :=
  LinearMap.congr_fun (AlgHom.commutes _ r) n
@[simp]
theorem foldr_one (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) : foldr Q f hf n 1 = n :=
  LinearMap.congr_fun (map_one (lift Q _)) n
@[simp]
theorem foldr_mul (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) (a b : CliffordAlgebra Q) :
    foldr Q f hf n (a * b) = foldr Q f hf (foldr Q f hf n b) a :=
  LinearMap.congr_fun (map_mul (lift Q _) _ _) n
theorem foldr_prod_map_ι (l : List M) (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) :
    foldr Q f hf n (l.map <| ι Q).prod = List.foldr (fun m n => f m n) n l := by
  induction' l with hd tl ih
  · rw [List.map_nil, List.prod_nil, List.foldr_nil, foldr_one]
  · rw [List.map_cons, List.prod_cons, List.foldr_cons, foldr_mul, foldr_ι, ih]
end Foldr
section Foldl
def foldl (f : M →ₗ[R] N →ₗ[R] N) (hf : ∀ m x, f m (f m x) = Q m • x) :
    N →ₗ[R] CliffordAlgebra Q →ₗ[R] N :=
  LinearMap.compl₂ (foldr Q f hf) reverse
@[simp]
theorem foldl_reverse (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) (x : CliffordAlgebra Q) :
    foldl Q f hf n (reverse x) = foldr Q f hf n x :=
  DFunLike.congr_arg (foldr Q f hf n) <| reverse_reverse _
@[simp]
theorem foldr_reverse (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) (x : CliffordAlgebra Q) :
    foldr Q f hf n (reverse x) = foldl Q f hf n x :=
  rfl
@[simp]
theorem foldl_ι (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) (m : M) : foldl Q f hf n (ι Q m) = f m n := by
  rw [← foldr_reverse, reverse_ι, foldr_ι]
@[simp]
theorem foldl_algebraMap (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) (r : R) :
    foldl Q f hf n (algebraMap R _ r) = r • n := by
  rw [← foldr_reverse, reverse.commutes, foldr_algebraMap]
@[simp]
theorem foldl_one (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) : foldl Q f hf n 1 = n := by
  rw [← foldr_reverse, reverse.map_one, foldr_one]
@[simp]
theorem foldl_mul (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) (a b : CliffordAlgebra Q) :
    foldl Q f hf n (a * b) = foldl Q f hf (foldl Q f hf n a) b := by
  rw [← foldr_reverse, ← foldr_reverse, ← foldr_reverse, reverse.map_mul, foldr_mul]
theorem foldl_prod_map_ι (l : List M) (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) :
    foldl Q f hf n (l.map <| ι Q).prod = List.foldl (fun m n => f n m) n l := by
  rw [← foldr_reverse, reverse_prod_map_ι, ← List.map_reverse, foldr_prod_map_ι, List.foldr_reverse]
end Foldl
@[elab_as_elim]
theorem right_induction {P : CliffordAlgebra Q → Prop} (algebraMap : ∀ r : R, P (algebraMap _ _ r))
    (add : ∀ x y, P x → P y → P (x + y)) (mul_ι : ∀ m x, P x → P (x * ι Q m)) : ∀ x, P x := by
  intro x
  have : x ∈ ⊤ := Submodule.mem_top (R := R)
  rw [← iSup_ι_range_eq_top] at this
  induction this using Submodule.iSup_induction' with
  | mem i x hx =>
    induction hx using Submodule.pow_induction_on_right' with
    | algebraMap r => exact algebraMap r
    | add _x _y _i _ _ ihx ihy => exact add _ _ ihx ihy
    | mul_mem _i x _hx px m hm =>
      obtain ⟨m, rfl⟩ := hm
      exact mul_ι _ _ px
  | zero => simpa only [map_zero] using algebraMap 0
  | add _x _y _ _ ihx ihy =>
    exact add _ _ ihx ihy
@[elab_as_elim]
theorem left_induction {P : CliffordAlgebra Q → Prop} (algebraMap : ∀ r : R, P (algebraMap _ _ r))
    (add : ∀ x y, P x → P y → P (x + y)) (ι_mul : ∀ x m, P x → P (ι Q m * x)) : ∀ x, P x := by
  refine reverse_involutive.surjective.forall.2 ?_
  intro x
  induction' x using CliffordAlgebra.right_induction with r x y hx hy m x hx
  · simpa only [reverse.commutes] using algebraMap r
  · simpa only [map_add] using add _ _ hx hy
  · simpa only [reverse.map_mul, reverse_ι] using ι_mul _ _ hx
def foldr'Aux (f : M →ₗ[R] CliffordAlgebra Q × N →ₗ[R] N) :
    M →ₗ[R] Module.End R (CliffordAlgebra Q × N) := by
  have v_mul := (Algebra.lmul R (CliffordAlgebra Q)).toLinearMap ∘ₗ ι Q
  have l := v_mul.compl₂ (LinearMap.fst _ _ N)
  exact
    { toFun := fun m => (l m).prod (f m)
      map_add' := fun v₂ v₂ =>
        LinearMap.ext fun x =>
          Prod.ext (LinearMap.congr_fun (l.map_add _ _) x) (LinearMap.congr_fun (f.map_add _ _) x)
      map_smul' := fun c v =>
        LinearMap.ext fun x =>
          Prod.ext (LinearMap.congr_fun (l.map_smul _ _) x)
            (LinearMap.congr_fun (f.map_smul _ _) x) }
theorem foldr'Aux_apply_apply (f : M →ₗ[R] CliffordAlgebra Q × N →ₗ[R] N) (m : M) (x_fx) :
    foldr'Aux Q f m x_fx = (ι Q m * x_fx.1, f m x_fx) :=
  rfl
theorem foldr'Aux_foldr'Aux (f : M →ₗ[R] CliffordAlgebra Q × N →ₗ[R] N)
    (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx) (v : M) (x_fx) :
    foldr'Aux Q f v (foldr'Aux Q f v x_fx) = Q v • x_fx := by
  cases' x_fx with x fx
  simp only [foldr'Aux_apply_apply]
  rw [← mul_assoc, ι_sq_scalar, ← Algebra.smul_def, hf, Prod.smul_mk]
def foldr' (f : M →ₗ[R] CliffordAlgebra Q × N →ₗ[R] N)
    (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx) (n : N) : CliffordAlgebra Q →ₗ[R] N :=
  LinearMap.snd _ _ _ ∘ₗ foldr Q (foldr'Aux Q f) (foldr'Aux_foldr'Aux Q _ hf) (1, n)
theorem foldr'_algebraMap (f : M →ₗ[R] CliffordAlgebra Q × N →ₗ[R] N)
    (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx) (n r) :
    foldr' Q f hf n (algebraMap R _ r) = r • n :=
  congr_arg Prod.snd (foldr_algebraMap _ _ _ _ _)
theorem foldr'_ι (f : M →ₗ[R] CliffordAlgebra Q × N →ₗ[R] N)
    (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx) (n m) :
    foldr' Q f hf n (ι Q m) = f m (1, n) :=
  congr_arg Prod.snd (foldr_ι _ _ _ _ _)
theorem foldr'_ι_mul (f : M →ₗ[R] CliffordAlgebra Q × N →ₗ[R] N)
    (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx) (n m) (x) :
    foldr' Q f hf n (ι Q m * x) = f m (x, foldr' Q f hf n x) := by
  dsimp [foldr']
  rw [foldr_mul, foldr_ι, foldr'Aux_apply_apply]
  refine congr_arg (f m) (Prod.mk.eta.symm.trans ?_)
  congr 1
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp_rw [foldr_algebraMap, Prod.smul_mk, Algebra.algebraMap_eq_smul_one]
  | add x y hx hy => rw [map_add, Prod.fst_add, hx, hy]
  | ι_mul m x hx => rw [foldr_mul, foldr_ι, foldr'Aux_apply_apply, hx]
end CliffordAlgebra