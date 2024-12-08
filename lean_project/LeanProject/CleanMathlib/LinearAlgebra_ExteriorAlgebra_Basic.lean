import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.Alternating.Basic
universe u1 u2 u3 u4 u5
variable (R : Type u1) [CommRing R]
variable (M : Type u2) [AddCommGroup M] [Module R M]
abbrev ExteriorAlgebra :=
  CliffordAlgebra (0 : QuadraticForm R M)
namespace ExteriorAlgebra
variable {M}
abbrev ι : M →ₗ[R] ExteriorAlgebra R M :=
  CliffordAlgebra.ι _
section exteriorPower
variable (n : ℕ) (M : Type u2) [AddCommGroup M] [Module R M]
abbrev exteriorPower : Submodule R (ExteriorAlgebra R M) :=
  LinearMap.range (ι R : M →ₗ[R] ExteriorAlgebra R M) ^ n
@[inherit_doc exteriorPower]
notation:max "⋀[" R "]^" n:arg => exteriorPower R n
end exteriorPower
variable {R}
theorem ι_sq_zero (m : M) : ι R m * ι R m = 0 :=
  (CliffordAlgebra.ι_sq_scalar _ m).trans <| map_zero _
section
variable {A : Type*} [Semiring A] [Algebra R A]
theorem comp_ι_sq_zero (g : ExteriorAlgebra R M →ₐ[R] A) (m : M) : g (ι R m) * g (ι R m) = 0 := by
  rw [← map_mul, ι_sq_zero, map_zero]
variable (R)
@[simps! symm_apply]
def lift : { f : M →ₗ[R] A // ∀ m, f m * f m = 0 } ≃ (ExteriorAlgebra R M →ₐ[R] A) :=
  Equiv.trans (Equiv.subtypeEquiv (Equiv.refl _) <| by simp) <| CliffordAlgebra.lift _
@[simp]
theorem ι_comp_lift (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = 0) :
    (lift R ⟨f, cond⟩).toLinearMap.comp (ι R) = f :=
  CliffordAlgebra.ι_comp_lift f _
@[simp]
theorem lift_ι_apply (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = 0) (x) :
    lift R ⟨f, cond⟩ (ι R x) = f x :=
  CliffordAlgebra.lift_ι_apply f _ x
@[simp]
theorem lift_unique (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = 0) (g : ExteriorAlgebra R M →ₐ[R] A) :
    g.toLinearMap.comp (ι R) = f ↔ g = lift R ⟨f, cond⟩ :=
  CliffordAlgebra.lift_unique f _ _
variable {R}
@[simp]
theorem lift_comp_ι (g : ExteriorAlgebra R M →ₐ[R] A) :
    lift R ⟨g.toLinearMap.comp (ι R), comp_ι_sq_zero _⟩ = g :=
  CliffordAlgebra.lift_comp_ι g
@[ext]
theorem hom_ext {f g : ExteriorAlgebra R M →ₐ[R] A}
    (h : f.toLinearMap.comp (ι R) = g.toLinearMap.comp (ι R)) : f = g :=
  CliffordAlgebra.hom_ext h
@[elab_as_elim]
theorem induction {C : ExteriorAlgebra R M → Prop}
    (algebraMap : ∀ r, C (algebraMap R (ExteriorAlgebra R M) r)) (ι : ∀ x, C (ι R x))
    (mul : ∀ a b, C a → C b → C (a * b)) (add : ∀ a b, C a → C b → C (a + b))
    (a : ExteriorAlgebra R M) : C a :=
  CliffordAlgebra.induction algebraMap ι mul add a
def algebraMapInv : ExteriorAlgebra R M →ₐ[R] R :=
  ExteriorAlgebra.lift R ⟨(0 : M →ₗ[R] R), fun _ => by simp⟩
variable (M)
theorem algebraMap_leftInverse :
    Function.LeftInverse algebraMapInv (algebraMap R <| ExteriorAlgebra R M) := fun x => by
  simp [algebraMapInv]
@[simp]
theorem algebraMap_inj (x y : R) :
    algebraMap R (ExteriorAlgebra R M) x = algebraMap R (ExteriorAlgebra R M) y ↔ x = y :=
  (algebraMap_leftInverse M).injective.eq_iff
@[simp]
theorem algebraMap_eq_zero_iff (x : R) : algebraMap R (ExteriorAlgebra R M) x = 0 ↔ x = 0 :=
  map_eq_zero_iff (algebraMap _ _) (algebraMap_leftInverse _).injective
@[simp]
theorem algebraMap_eq_one_iff (x : R) : algebraMap R (ExteriorAlgebra R M) x = 1 ↔ x = 1 :=
  map_eq_one_iff (algebraMap _ _) (algebraMap_leftInverse _).injective
@[instance]
theorem isLocalHom_algebraMap : IsLocalHom (algebraMap R (ExteriorAlgebra R M)) :=
  isLocalHom_of_leftInverse _ (algebraMap_leftInverse M)
@[deprecated (since := "2024-10-10")]
alias isLocalRingHom_algebraMap := isLocalHom_algebraMap
theorem isUnit_algebraMap (r : R) : IsUnit (algebraMap R (ExteriorAlgebra R M) r) ↔ IsUnit r :=
  isUnit_map_of_leftInverse _ (algebraMap_leftInverse M)
@[simps!]
def invertibleAlgebraMapEquiv (r : R) :
    Invertible (algebraMap R (ExteriorAlgebra R M) r) ≃ Invertible r :=
  invertibleEquivOfLeftInverse _ _ _ (algebraMap_leftInverse M)
variable {M}
def toTrivSqZeroExt [Module Rᵐᵒᵖ M] [IsCentralScalar R M] :
    ExteriorAlgebra R M →ₐ[R] TrivSqZeroExt R M :=
  lift R ⟨TrivSqZeroExt.inrHom R M, fun m => TrivSqZeroExt.inr_mul_inr R m m⟩
@[simp]
theorem toTrivSqZeroExt_ι [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (x : M) :
    toTrivSqZeroExt (ι R x) = TrivSqZeroExt.inr x :=
  lift_ι_apply _ _ _ _
def ιInv : ExteriorAlgebra R M →ₗ[R] M := by
  letI : Module Rᵐᵒᵖ M := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
  haveI : IsCentralScalar R M := ⟨fun r m => rfl⟩
  exact (TrivSqZeroExt.sndHom R M).comp toTrivSqZeroExt.toLinearMap
theorem ι_leftInverse : Function.LeftInverse ιInv (ι R : M → ExteriorAlgebra R M) := fun x => by
  letI : Module Rᵐᵒᵖ M := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
  haveI : IsCentralScalar R M := ⟨fun r m => rfl⟩
  simp [ιInv]
variable (R)
@[simp]
theorem ι_inj (x y : M) : ι R x = ι R y ↔ x = y :=
  ι_leftInverse.injective.eq_iff
variable {R}
@[simp]
theorem ι_eq_zero_iff (x : M) : ι R x = 0 ↔ x = 0 := by rw [← ι_inj R x 0, LinearMap.map_zero]
@[simp]
theorem ι_eq_algebraMap_iff (x : M) (r : R) : ι R x = algebraMap R _ r ↔ x = 0 ∧ r = 0 := by
  refine ⟨fun h => ?_, ?_⟩
  · letI : Module Rᵐᵒᵖ M := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
    haveI : IsCentralScalar R M := ⟨fun r m => rfl⟩
    have hf0 : toTrivSqZeroExt (ι R x) = (0, x) := toTrivSqZeroExt_ι _
    rw [h, AlgHom.commutes] at hf0
    have : r = 0 ∧ 0 = x := Prod.ext_iff.1 hf0
    exact this.symm.imp_left Eq.symm
  · rintro ⟨rfl, rfl⟩
    rw [LinearMap.map_zero, RingHom.map_zero]
@[simp]
theorem ι_ne_one [Nontrivial R] (x : M) : ι R x ≠ 1 := by
  rw [← (algebraMap R (ExteriorAlgebra R M)).map_one, Ne, ι_eq_algebraMap_iff]
  exact one_ne_zero ∘ And.right
theorem ι_range_disjoint_one :
    Disjoint (LinearMap.range (ι R : M →ₗ[R] ExteriorAlgebra R M))
      (1 : Submodule R (ExteriorAlgebra R M)) := by
  rw [Submodule.disjoint_def]
  rintro _ ⟨x, hx⟩ h
  obtain ⟨r, rfl : algebraMap R (ExteriorAlgebra R M) r = _⟩ := Submodule.mem_one.mp h
  rw [ι_eq_algebraMap_iff x] at hx
  rw [hx.2, RingHom.map_zero]
@[simp]
theorem ι_add_mul_swap (x y : M) : ι R x * ι R y + ι R y * ι R x = 0 :=
  CliffordAlgebra.ι_mul_ι_add_swap_of_isOrtho <| .all _ _
theorem ι_mul_prod_list {n : ℕ} (f : Fin n → M) (i : Fin n) :
    (ι R <| f i) * (List.ofFn fun i => ι R <| f i).prod = 0 := by
  induction n with
  | zero => exact i.elim0
  | succ n hn =>
    rw [List.ofFn_succ, List.prod_cons, ← mul_assoc]
    by_cases h : i = 0
    · rw [h, ι_sq_zero, zero_mul]
    · replace hn :=
        congr_arg (ι R (f 0) * ·) <| hn (fun i => f <| Fin.succ i) (i.pred h)
      simp only at hn
      rw [Fin.succ_pred, ← mul_assoc, mul_zero] at hn
      refine (eq_zero_iff_eq_zero_of_add_eq_zero ?_).mp hn
      rw [← add_mul, ι_add_mul_swap, zero_mul]
end
variable (R)
def ιMulti (n : ℕ) : M [⋀^Fin n]→ₗ[R] ExteriorAlgebra R M :=
  let F := (MultilinearMap.mkPiAlgebraFin R n (ExteriorAlgebra R M)).compLinearMap fun _ => ι R
  { F with
    map_eq_zero_of_eq' := fun f x y hfxy hxy => by
      dsimp [F]
      clear F
      wlog h : x < y
      · exact this R n f y x hfxy.symm hxy.symm (hxy.lt_or_lt.resolve_left h)
      clear hxy
      induction' n with n hn
      · exact x.elim0
      · rw [List.ofFn_succ, List.prod_cons]
        by_cases hx : x = 0
        · rw [hx] at hfxy h
          rw [hfxy, ← Fin.succ_pred y (ne_of_lt h).symm]
          exact ι_mul_prod_list (f ∘ Fin.succ) _
        · convert mul_zero (ι R (f 0))
          refine
            hn
              (fun i => f <| Fin.succ i) (x.pred hx)
              (y.pred (ne_of_lt <| lt_of_le_of_lt x.zero_le h).symm) ?_
              (Fin.pred_lt_pred_iff.mpr h)
          simp only [Fin.succ_pred]
          exact hfxy
    toFun := F }
variable {R}
theorem ιMulti_apply {n : ℕ} (v : Fin n → M) : ιMulti R n v = (List.ofFn fun i => ι R (v i)).prod :=
  rfl
@[simp]
theorem ιMulti_zero_apply (v : Fin 0 → M) : ιMulti R 0 v = 1 := by
  simp [ιMulti]
@[simp]
theorem ιMulti_succ_apply {n : ℕ} (v : Fin n.succ → M) :
    ιMulti R _ v = ι R (v 0) * ιMulti R _ (Matrix.vecTail v) := by
  simp [ιMulti, Matrix.vecTail]
theorem ιMulti_succ_curryLeft {n : ℕ} (m : M) :
    (ιMulti R n.succ).curryLeft m = (LinearMap.mulLeft R (ι R m)).compAlternatingMap (ιMulti R n) :=
  AlternatingMap.ext fun v =>
    (ιMulti_succ_apply _).trans <| by
      simp_rw [Matrix.tail_cons]
      rfl
variable (R)
lemma ιMulti_range (n : ℕ) :
    Set.range (ιMulti R n (M := M)) ⊆ ↑(⋀[R]^n M) := by
  rw [Set.range_subset_iff]
  intro v
  rw [ιMulti_apply]
  apply Submodule.pow_subset_pow
  rw [Set.mem_pow]
  exact ⟨fun i => ⟨ι R (v i), LinearMap.mem_range_self _ _⟩, rfl⟩
lemma ιMulti_span_fixedDegree (n : ℕ) :
    Submodule.span R (Set.range (ιMulti R n)) = ⋀[R]^n M := by
  refine le_antisymm (Submodule.span_le.2 (ιMulti_range R n)) ?_
  rw [exteriorPower, Submodule.pow_eq_span_pow_set, Submodule.span_le]
  refine fun u hu ↦ Submodule.subset_span ?_
  obtain ⟨f, rfl⟩ := Set.mem_pow.mp hu
  refine ⟨fun i => ιInv (f i).1, ?_⟩
  rw [ιMulti_apply]
  congr with i
  obtain ⟨v, hv⟩ := (f i).prop
  rw [← hv, ι_leftInverse]
abbrev ιMulti_family (n : ℕ) {I : Type*} [LinearOrder I] (v : I → M)
    (s : {s : Finset I // Finset.card s = n}) : ExteriorAlgebra R M :=
  ιMulti R n fun i => v (Finset.orderIsoOfFin _ s.prop i)
variable {R}
instance [Nontrivial R] : Nontrivial (ExteriorAlgebra R M) :=
  (algebraMap_leftInverse M).injective.nontrivial
variable {N : Type u4} {N' : Type u5} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
def map (f : M →ₗ[R] N) : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra R N :=
  CliffordAlgebra.map { f with map_app' := fun _ => rfl }
@[simp]
theorem map_comp_ι (f : M →ₗ[R] N) : (map f).toLinearMap ∘ₗ ι R = ι R ∘ₗ f :=
  CliffordAlgebra.map_comp_ι _
@[simp]
theorem map_apply_ι (f : M →ₗ[R] N) (m : M) : map f (ι R m) = ι R (f m) :=
  CliffordAlgebra.map_apply_ι _ m
@[simp]
theorem map_apply_ιMulti {n : ℕ} (f : M →ₗ[R] N) (m : Fin n → M) :
    map f (ιMulti R n m) = ιMulti R n (f ∘ m) := by
  rw [ιMulti_apply, ιMulti_apply, map_list_prod]
  simp only [List.map_ofFn, Function.comp_def, map_apply_ι]
@[simp]
theorem map_comp_ιMulti {n : ℕ} (f : M →ₗ[R] N) :
    (map f).toLinearMap.compAlternatingMap (ιMulti R n (M := M)) =
    (ιMulti R n (M := N)).compLinearMap f := by
  ext m
  exact map_apply_ιMulti _ _
@[simp]
theorem map_id :
    map LinearMap.id = AlgHom.id R (ExteriorAlgebra R M) :=
  CliffordAlgebra.map_id 0
@[simp]
theorem map_comp_map (f : M →ₗ[R] N) (g : N →ₗ[R] N') :
    AlgHom.comp (map g) (map f) = map (LinearMap.comp g f) :=
  CliffordAlgebra.map_comp_map _ _
@[simp]
theorem ι_range_map_map (f : M →ₗ[R] N) :
    Submodule.map (AlgHom.toLinearMap (map f)) (LinearMap.range (ι R (M := M))) =
    Submodule.map (ι R) (LinearMap.range f) :=
  CliffordAlgebra.ι_range_map_map _
theorem toTrivSqZeroExt_comp_map [Module Rᵐᵒᵖ M] [IsCentralScalar R M] [Module Rᵐᵒᵖ N]
    [IsCentralScalar R N] (f : M →ₗ[R] N) :
    toTrivSqZeroExt.comp (map f) = (TrivSqZeroExt.map f).comp toTrivSqZeroExt := by
  apply hom_ext
  apply LinearMap.ext
  simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, Function.comp_apply,
    AlgHom.toLinearMap_apply, map_apply_ι, toTrivSqZeroExt_ι, TrivSqZeroExt.map_inr, forall_const]
theorem ιInv_comp_map (f : M →ₗ[R] N) :
    ιInv.comp (map f).toLinearMap = f.comp ιInv := by
  letI : Module Rᵐᵒᵖ M := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
  haveI : IsCentralScalar R M := ⟨fun r m => rfl⟩
  letI : Module Rᵐᵒᵖ N := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
  haveI : IsCentralScalar R N := ⟨fun r m => rfl⟩
  unfold ιInv
  conv_lhs => rw [LinearMap.comp_assoc, ← AlgHom.comp_toLinearMap, toTrivSqZeroExt_comp_map,
                AlgHom.comp_toLinearMap, ← LinearMap.comp_assoc, TrivSqZeroExt.sndHom_comp_map]
  rfl
open Function in
@[simp]
lemma leftInverse_map_iff {f : M →ₗ[R] N} {g : N →ₗ[R] M} :
    LeftInverse (map g) (map f) ↔ LeftInverse g f := by
  refine ⟨fun h x => ?_, fun h => CliffordAlgebra.leftInverse_map_of_leftInverse _ _ h⟩
  simpa using h (ι _ x)
lemma map_injective {f : M →ₗ[R] N} (hf : ∃ (g : N →ₗ[R] M), g.comp f = LinearMap.id) :
    Function.Injective (map f) :=
  let ⟨_, hgf⟩ := hf; (leftInverse_map_iff.mpr (DFunLike.congr_fun hgf)).injective
@[simp]
lemma map_surjective_iff {f : M →ₗ[R] N} :
    Function.Surjective (map f) ↔ Function.Surjective f := by
  refine ⟨fun h y ↦ ?_, fun h ↦ CliffordAlgebra.map_surjective _ h⟩
  obtain ⟨x, hx⟩ := h (ι R y)
  existsi ιInv x
  rw [← LinearMap.comp_apply, ← ιInv_comp_map, LinearMap.comp_apply]
  erw [hx, ExteriorAlgebra.ι_leftInverse]
variable {K E F : Type*} [Field K] [AddCommGroup E]
  [Module K E] [AddCommGroup F] [Module K F]
lemma map_injective_field {f : E →ₗ[K] F} (hf : LinearMap.ker f = ⊥) :
    Function.Injective (map f) :=
  map_injective (LinearMap.exists_leftInverse_of_injective f hf)
end ExteriorAlgebra
namespace TensorAlgebra
variable {R M}
def toExterior : TensorAlgebra R M →ₐ[R] ExteriorAlgebra R M :=
  TensorAlgebra.lift R (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M)
@[simp]
theorem toExterior_ι (m : M) :
    TensorAlgebra.toExterior (TensorAlgebra.ι R m) = ExteriorAlgebra.ι R m := by
  simp [toExterior]
end TensorAlgebra