import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.PowerBasis
open scoped Polynomial
open Polynomial
noncomputable section
universe u v
structure IsAdjoinRoot {R : Type u} (S : Type v) [CommSemiring R] [Semiring S] [Algebra R S]
    (f : R[X]) : Type max u v where
  map : R[X] →+* S
  map_surjective : Function.Surjective map
  ker_map : RingHom.ker map = Ideal.span {f}
  algebraMap_eq : algebraMap R S = map.comp Polynomial.C
structure IsAdjoinRootMonic {R : Type u} (S : Type v) [CommSemiring R] [Semiring S] [Algebra R S]
    (f : R[X]) extends IsAdjoinRoot S f where
  Monic : Monic f
section Ring
variable {R : Type u} {S : Type v} [CommRing R] [Ring S] {f : R[X]} [Algebra R S]
namespace IsAdjoinRoot
def root (h : IsAdjoinRoot S f) : S :=
  h.map X
theorem subsingleton (h : IsAdjoinRoot S f) [Subsingleton R] : Subsingleton S :=
  h.map_surjective.subsingleton
theorem algebraMap_apply (h : IsAdjoinRoot S f) (x : R) :
    algebraMap R S x = h.map (Polynomial.C x) := by rw [h.algebraMap_eq, RingHom.comp_apply]
theorem mem_ker_map (h : IsAdjoinRoot S f) {p} : p ∈ RingHom.ker h.map ↔ f ∣ p := by
  rw [h.ker_map, Ideal.mem_span_singleton]
@[simp]
theorem map_eq_zero_iff (h : IsAdjoinRoot S f) {p} : h.map p = 0 ↔ f ∣ p := by
  rw [← h.mem_ker_map, RingHom.mem_ker]
@[simp]
theorem map_X (h : IsAdjoinRoot S f) : h.map X = h.root := rfl
@[simp]
theorem map_self (h : IsAdjoinRoot S f) : h.map f = 0 := h.map_eq_zero_iff.mpr dvd_rfl
@[simp]
theorem aeval_eq (h : IsAdjoinRoot S f) (p : R[X]) : aeval h.root p = h.map p :=
  Polynomial.induction_on p (fun x => by rw [aeval_C, h.algebraMap_apply])
    (fun p q ihp ihq => by rw [map_add, RingHom.map_add, ihp, ihq]) fun n x _ => by
    rw [map_mul, aeval_C, map_pow, aeval_X, RingHom.map_mul, ← h.algebraMap_apply,
      RingHom.map_pow, map_X]
theorem aeval_root (h : IsAdjoinRoot S f) : aeval h.root f = 0 := by rw [aeval_eq, map_self]
def repr (h : IsAdjoinRoot S f) (x : S) : R[X] :=
  (h.map_surjective x).choose
theorem map_repr (h : IsAdjoinRoot S f) (x : S) : h.map (h.repr x) = x :=
  (h.map_surjective x).choose_spec
theorem repr_zero_mem_span (h : IsAdjoinRoot S f) : h.repr 0 ∈ Ideal.span ({f} : Set R[X]) := by
  rw [← h.ker_map, RingHom.mem_ker, h.map_repr]
theorem repr_add_sub_repr_add_repr_mem_span (h : IsAdjoinRoot S f) (x y : S) :
    h.repr (x + y) - (h.repr x + h.repr y) ∈ Ideal.span ({f} : Set R[X]) := by
  rw [← h.ker_map, RingHom.mem_ker, map_sub, h.map_repr, map_add, h.map_repr, h.map_repr, sub_self]
theorem ext_map (h h' : IsAdjoinRoot S f) (eq : ∀ x, h.map x = h'.map x) : h = h' := by
  cases h; cases h'; congr
  exact RingHom.ext eq
@[ext]
theorem ext (h h' : IsAdjoinRoot S f) (eq : h.root = h'.root) : h = h' :=
  h.ext_map h' fun x => by rw [← h.aeval_eq, ← h'.aeval_eq, eq]
section lift
variable {T : Type*} [CommRing T] {i : R →+* T} {x : T}
section
variable (hx : f.eval₂ i x = 0)
include hx
theorem eval₂_repr_eq_eval₂_of_map_eq (h : IsAdjoinRoot S f) (z : S) (w : R[X])
    (hzw : h.map w = z) : (h.repr z).eval₂ i x = w.eval₂ i x := by
  rw [eq_comm, ← sub_eq_zero, ← h.map_repr z, ← map_sub, h.map_eq_zero_iff] at hzw
  obtain ⟨y, hy⟩ := hzw
  rw [← sub_eq_zero, ← eval₂_sub, hy, eval₂_mul, hx, zero_mul]
variable (i x)
def lift (h : IsAdjoinRoot S f) (hx : f.eval₂ i x = 0) : S →+* T where
  toFun z := (h.repr z).eval₂ i x
  map_zero' := by
    dsimp only 
    rw [h.eval₂_repr_eq_eval₂_of_map_eq hx _ _ (map_zero _), eval₂_zero]
  map_add' z w := by
    dsimp only 
    rw [h.eval₂_repr_eq_eval₂_of_map_eq hx _ (h.repr z + h.repr w), eval₂_add]
    rw [map_add, map_repr, map_repr]
  map_one' := by
    beta_reduce 
    rw [h.eval₂_repr_eq_eval₂_of_map_eq hx _ _ (map_one _), eval₂_one]
  map_mul' z w := by
    dsimp only 
    rw [h.eval₂_repr_eq_eval₂_of_map_eq hx _ (h.repr z * h.repr w), eval₂_mul]
    rw [map_mul, map_repr, map_repr]
variable {i x}
@[simp]
theorem lift_map (h : IsAdjoinRoot S f) (z : R[X]) : h.lift i x hx (h.map z) = z.eval₂ i x := by
  rw [lift, RingHom.coe_mk]
  dsimp 
  rw [h.eval₂_repr_eq_eval₂_of_map_eq hx _ _ rfl]
@[simp]
theorem lift_root (h : IsAdjoinRoot S f) : h.lift i x hx h.root = x := by
  rw [← h.map_X, lift_map, eval₂_X]
@[simp]
theorem lift_algebraMap (h : IsAdjoinRoot S f) (a : R) :
    h.lift i x hx (algebraMap R S a) = i a := by rw [h.algebraMap_apply, lift_map, eval₂_C]
theorem apply_eq_lift (h : IsAdjoinRoot S f) (g : S →+* T) (hmap : ∀ a, g (algebraMap R S a) = i a)
    (hroot : g h.root = x) (a : S) : g a = h.lift i x hx a := by
  rw [← h.map_repr a, Polynomial.as_sum_range_C_mul_X_pow (h.repr a)]
  simp only [map_sum, map_mul, map_pow, h.map_X, hroot, ← h.algebraMap_apply, hmap, lift_root,
    lift_algebraMap]
theorem eq_lift (h : IsAdjoinRoot S f) (g : S →+* T) (hmap : ∀ a, g (algebraMap R S a) = i a)
    (hroot : g h.root = x) : g = h.lift i x hx :=
  RingHom.ext (h.apply_eq_lift hx g hmap hroot)
end
variable [Algebra R T] (hx' : aeval x f = 0)
variable (x)
def liftHom (h : IsAdjoinRoot S f) : S →ₐ[R] T :=
  { h.lift (algebraMap R T) x hx' with commutes' := fun a => h.lift_algebraMap hx' a }
variable {x}
@[simp]
theorem coe_liftHom (h : IsAdjoinRoot S f) :
    (h.liftHom x hx' : S →+* T) = h.lift (algebraMap R T) x hx' := rfl
theorem lift_algebraMap_apply (h : IsAdjoinRoot S f) (z : S) :
    h.lift (algebraMap R T) x hx' z = h.liftHom x hx' z := rfl
@[simp]
theorem liftHom_map (h : IsAdjoinRoot S f) (z : R[X]) : h.liftHom x hx' (h.map z) = aeval x z := by
  rw [← lift_algebraMap_apply, lift_map, aeval_def]
@[simp]
theorem liftHom_root (h : IsAdjoinRoot S f) : h.liftHom x hx' h.root = x := by
  rw [← lift_algebraMap_apply, lift_root]
theorem eq_liftHom (h : IsAdjoinRoot S f) (g : S →ₐ[R] T) (hroot : g h.root = x) :
    g = h.liftHom x hx' :=
  AlgHom.ext (h.apply_eq_lift hx' g g.commutes hroot)
end lift
end IsAdjoinRoot
namespace AdjoinRoot
variable (f)
protected def isAdjoinRoot : IsAdjoinRoot (AdjoinRoot f) f where
  map := AdjoinRoot.mk f
  map_surjective := Ideal.Quotient.mk_surjective
  ker_map := by
    ext
    rw [RingHom.mem_ker, ← @AdjoinRoot.mk_self _ _ f, AdjoinRoot.mk_eq_mk, Ideal.mem_span_singleton,
      ← dvd_add_left (dvd_refl f), sub_add_cancel]
  algebraMap_eq := AdjoinRoot.algebraMap_eq f
protected def isAdjoinRootMonic (hf : Monic f) : IsAdjoinRootMonic (AdjoinRoot f) f :=
  { AdjoinRoot.isAdjoinRoot f with Monic := hf }
@[simp]
theorem isAdjoinRoot_map_eq_mk : (AdjoinRoot.isAdjoinRoot f).map = AdjoinRoot.mk f :=
  rfl
@[simp]
theorem isAdjoinRootMonic_map_eq_mk (hf : f.Monic) :
    (AdjoinRoot.isAdjoinRootMonic f hf).map = AdjoinRoot.mk f :=
  rfl
@[simp]
theorem isAdjoinRoot_root_eq_root : (AdjoinRoot.isAdjoinRoot f).root = AdjoinRoot.root f := by
  simp only [IsAdjoinRoot.root, AdjoinRoot.root, AdjoinRoot.isAdjoinRoot_map_eq_mk]
@[simp]
theorem isAdjoinRootMonic_root_eq_root (hf : Monic f) :
    (AdjoinRoot.isAdjoinRootMonic f hf).root = AdjoinRoot.root f := by
  simp only [IsAdjoinRoot.root, AdjoinRoot.root, AdjoinRoot.isAdjoinRootMonic_map_eq_mk]
end AdjoinRoot
namespace IsAdjoinRootMonic
open IsAdjoinRoot
theorem map_modByMonic (h : IsAdjoinRootMonic S f) (g : R[X]) : h.map (g %ₘ f) = h.map g := by
  rw [← RingHom.sub_mem_ker_iff, mem_ker_map, modByMonic_eq_sub_mul_div _ h.Monic, sub_right_comm,
    sub_self, zero_sub, dvd_neg]
  exact ⟨_, rfl⟩
theorem modByMonic_repr_map (h : IsAdjoinRootMonic S f) (g : R[X]) :
    h.repr (h.map g) %ₘ f = g %ₘ f :=
  modByMonic_eq_of_dvd_sub h.Monic <| by rw [← h.mem_ker_map, RingHom.sub_mem_ker_iff, map_repr]
def modByMonicHom (h : IsAdjoinRootMonic S f) : S →ₗ[R] R[X] where
  toFun x := h.repr x %ₘ f
  map_add' x y := by
    conv_lhs =>
      rw [← h.map_repr x, ← h.map_repr y, ← map_add]
      beta_reduce 
      rw [h.modByMonic_repr_map, add_modByMonic]
  map_smul' c x := by
    rw [RingHom.id_apply, ← h.map_repr x, Algebra.smul_def, h.algebraMap_apply, ← map_mul]
    dsimp only 
    rw [h.modByMonic_repr_map, ← smul_eq_C_mul, smul_modByMonic, h.map_repr]
@[simp]
theorem modByMonicHom_map (h : IsAdjoinRootMonic S f) (g : R[X]) :
    h.modByMonicHom (h.map g) = g %ₘ f := h.modByMonic_repr_map g
@[simp]
theorem map_modByMonicHom (h : IsAdjoinRootMonic S f) (x : S) : h.map (h.modByMonicHom x) = x := by
  rw [modByMonicHom, LinearMap.coe_mk]
  dsimp 
  rw [map_modByMonic, map_repr]
@[simp]
theorem modByMonicHom_root_pow (h : IsAdjoinRootMonic S f) {n : ℕ} (hdeg : n < natDegree f) :
    h.modByMonicHom (h.root ^ n) = X ^ n := by
  nontriviality R
  rw [← h.map_X, ← map_pow, modByMonicHom_map, modByMonic_eq_self_iff h.Monic, degree_X_pow]
  contrapose! hdeg
  simpa [natDegree_le_iff_degree_le] using hdeg
@[simp]
theorem modByMonicHom_root (h : IsAdjoinRootMonic S f) (hdeg : 1 < natDegree f) :
    h.modByMonicHom h.root = X := by simpa using modByMonicHom_root_pow h hdeg
def basis (h : IsAdjoinRootMonic S f) : Basis (Fin (natDegree f)) R S :=
  Basis.ofRepr
    { toFun := fun x => (h.modByMonicHom x).toFinsupp.comapDomain _ Fin.val_injective.injOn
      invFun := fun g => h.map (ofFinsupp (g.mapDomain Fin.val))
      left_inv := fun x => by
        cases subsingleton_or_nontrivial R
        · subsingleton [h.subsingleton]
        simp only
        rw [Finsupp.mapDomain_comapDomain, Polynomial.eta, h.map_modByMonicHom x]
        · exact Fin.val_injective
        intro i hi
        refine Set.mem_range.mpr ⟨⟨i, ?_⟩, rfl⟩
        contrapose! hi
        simp only [Polynomial.toFinsupp_apply, Classical.not_not, Finsupp.mem_support_iff, Ne,
          modByMonicHom, LinearMap.coe_mk, Finset.mem_coe]
        by_cases hx : h.toIsAdjoinRoot.repr x %ₘ f = 0
        · simp [hx]
        refine coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le ?_ hi)
        dsimp 
        rw [natDegree_lt_natDegree_iff hx]
        exact degree_modByMonic_lt _ h.Monic
      right_inv := fun g => by
        nontriviality R
        ext i
        simp only [h.modByMonicHom_map, Finsupp.comapDomain_apply, Polynomial.toFinsupp_apply]
        rw [(Polynomial.modByMonic_eq_self_iff h.Monic).mpr, Polynomial.coeff]
        · rw [Finsupp.mapDomain_apply Fin.val_injective]
        rw [degree_eq_natDegree h.Monic.ne_zero, degree_lt_iff_coeff_zero]
        intro m hm
        rw [Polynomial.coeff]
        rw [Finsupp.mapDomain_notin_range]
        rw [Set.mem_range, not_exists]
        rintro i rfl
        exact i.prop.not_le hm
      map_add' := fun x y => by
        beta_reduce 
        rw [map_add, toFinsupp_add, Finsupp.comapDomain_add_of_injective Fin.val_injective]
      map_smul' := fun c x => by
        dsimp only 
        rw [map_smul, toFinsupp_smul, Finsupp.comapDomain_smul_of_injective Fin.val_injective,
          RingHom.id_apply] }
@[simp]
theorem basis_apply (h : IsAdjoinRootMonic S f) (i) : h.basis i = h.root ^ (i : ℕ) :=
  Basis.apply_eq_iff.mpr <|
    show (h.modByMonicHom (h.toIsAdjoinRoot.root ^ (i : ℕ))).toFinsupp.comapDomain _
          Fin.val_injective.injOn = Finsupp.single _ _ by
      ext j
      rw [Finsupp.comapDomain_apply, modByMonicHom_root_pow]
      · rw [X_pow_eq_monomial, toFinsupp_monomial, Finsupp.single_apply_left Fin.val_injective]
      · exact i.is_lt
theorem deg_pos [Nontrivial S] (h : IsAdjoinRootMonic S f) : 0 < natDegree f := by
  rcases h.basis.index_nonempty with ⟨⟨i, hi⟩⟩
  exact (Nat.zero_le _).trans_lt hi
theorem deg_ne_zero [Nontrivial S] (h : IsAdjoinRootMonic S f) : natDegree f ≠ 0 :=
  h.deg_pos.ne'
@[simps! gen dim basis]
def powerBasis (h : IsAdjoinRootMonic S f) : PowerBasis R S where
  gen := h.root
  dim := natDegree f
  basis := h.basis
  basis_eq_pow := h.basis_apply
@[simp]
theorem basis_repr (h : IsAdjoinRootMonic S f) (x : S) (i : Fin (natDegree f)) :
    h.basis.repr x i = (h.modByMonicHom x).coeff (i : ℕ) := by
  change (h.modByMonicHom x).toFinsupp.comapDomain _ Fin.val_injective.injOn i = _
  rw [Finsupp.comapDomain_apply, Polynomial.toFinsupp_apply]
theorem basis_one (h : IsAdjoinRootMonic S f) (hdeg : 1 < natDegree f) :
    h.basis ⟨1, hdeg⟩ = h.root := by rw [h.basis_apply, Fin.val_mk, pow_one]
@[simps!]
def liftPolyₗ {T : Type*} [AddCommGroup T] [Module R T] (h : IsAdjoinRootMonic S f)
    (g : R[X] →ₗ[R] T) : S →ₗ[R] T :=
  g.comp h.modByMonicHom
def coeff (h : IsAdjoinRootMonic S f) : S →ₗ[R] ℕ → R :=
  h.liftPolyₗ
    { toFun := Polynomial.coeff
      map_add' := fun p q => funext (Polynomial.coeff_add p q)
      map_smul' := fun c p => funext (Polynomial.coeff_smul c p) }
theorem coeff_apply_lt (h : IsAdjoinRootMonic S f) (z : S) (i : ℕ) (hi : i < natDegree f) :
    h.coeff z i = h.basis.repr z ⟨i, hi⟩ := by
  simp only [coeff, LinearMap.comp_apply, Finsupp.lcoeFun_apply, Finsupp.lmapDomain_apply,
    LinearEquiv.coe_coe, liftPolyₗ_apply, LinearMap.coe_mk, h.basis_repr]
  rfl
theorem coeff_apply_coe (h : IsAdjoinRootMonic S f) (z : S) (i : Fin (natDegree f)) :
    h.coeff z i = h.basis.repr z i := h.coeff_apply_lt z i i.prop
theorem coeff_apply_le (h : IsAdjoinRootMonic S f) (z : S) (i : ℕ) (hi : natDegree f ≤ i) :
    h.coeff z i = 0 := by
  simp only [coeff, LinearMap.comp_apply, Finsupp.lcoeFun_apply, Finsupp.lmapDomain_apply,
    LinearEquiv.coe_coe, liftPolyₗ_apply, LinearMap.coe_mk, h.basis_repr]
  nontriviality R
  exact
    Polynomial.coeff_eq_zero_of_degree_lt
      ((degree_modByMonic_lt _ h.Monic).trans_le (Polynomial.degree_le_of_natDegree_le hi))
theorem coeff_apply (h : IsAdjoinRootMonic S f) (z : S) (i : ℕ) :
    h.coeff z i = if hi : i < natDegree f then h.basis.repr z ⟨i, hi⟩ else 0 := by
  split_ifs with hi
  · exact h.coeff_apply_lt z i hi
  · exact h.coeff_apply_le z i (le_of_not_lt hi)
theorem coeff_root_pow (h : IsAdjoinRootMonic S f) {n} (hn : n < natDegree f) :
    h.coeff (h.root ^ n) = Pi.single n 1 := by
  ext i
  rw [coeff_apply]
  split_ifs with hi
  · calc
      h.basis.repr (h.root ^ n) ⟨i, _⟩ = h.basis.repr (h.basis ⟨n, hn⟩) ⟨i, hi⟩ := by
        rw [h.basis_apply, Fin.val_mk]
      _ = Pi.single (f := fun _ => R) ((⟨n, hn⟩ : Fin _) : ℕ) (1 : (fun _ => R) n)
        ↑(⟨i, _⟩ : Fin _) := by
        rw [h.basis.repr_self, ← Finsupp.single_eq_pi_single,
          Finsupp.single_apply_left Fin.val_injective]
      _ = Pi.single (f := fun _ => R) n 1 i := by rw [Fin.val_mk, Fin.val_mk]
  · refine (Pi.single_eq_of_ne (f := fun _ => R) ?_ (1 : (fun _ => R) n)).symm
    rintro rfl
    simp [hi] at hn
theorem coeff_one [Nontrivial S] (h : IsAdjoinRootMonic S f) : h.coeff 1 = Pi.single 0 1 := by
  rw [← h.coeff_root_pow h.deg_pos, pow_zero]
theorem coeff_root (h : IsAdjoinRootMonic S f) (hdeg : 1 < natDegree f) :
    h.coeff h.root = Pi.single 1 1 := by rw [← h.coeff_root_pow hdeg, pow_one]
theorem coeff_algebraMap [Nontrivial S] (h : IsAdjoinRootMonic S f) (x : R) :
    h.coeff (algebraMap R S x) = Pi.single 0 x := by
  ext i
  rw [Algebra.algebraMap_eq_smul_one, map_smul, coeff_one, Pi.smul_apply, smul_eq_mul]
  refine (Pi.apply_single (fun _ y => x * y) ?_ 0 1 i).trans (by simp)
  simp
theorem ext_elem (h : IsAdjoinRootMonic S f) ⦃x y : S⦄
    (hxy : ∀ i < natDegree f, h.coeff x i = h.coeff y i) : x = y :=
  EquivLike.injective h.basis.equivFun <|
    funext fun i => by
      rw [Basis.equivFun_apply, ← h.coeff_apply_coe, Basis.equivFun_apply, ← h.coeff_apply_coe,
        hxy i i.prop]
theorem ext_elem_iff (h : IsAdjoinRootMonic S f) {x y : S} :
    x = y ↔ ∀ i < natDegree f, h.coeff x i = h.coeff y i :=
  ⟨fun hxy _ _=> hxy ▸ rfl, fun hxy => h.ext_elem hxy⟩
theorem coeff_injective (h : IsAdjoinRootMonic S f) : Function.Injective h.coeff := fun _ _ hxy =>
  h.ext_elem fun _ _ => hxy ▸ rfl
theorem isIntegral_root (h : IsAdjoinRootMonic S f) : IsIntegral R h.root :=
  ⟨f, h.Monic, h.aeval_root⟩
end IsAdjoinRootMonic
end Ring
section CommRing
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] {f : R[X]}
namespace IsAdjoinRoot
section lift
@[simp]
theorem lift_self_apply (h : IsAdjoinRoot S f) (x : S) :
    h.lift (algebraMap R S) h.root h.aeval_root x = x := by
  rw [← h.map_repr x, lift_map, ← aeval_def, h.aeval_eq]
theorem lift_self (h : IsAdjoinRoot S f) :
    h.lift (algebraMap R S) h.root h.aeval_root = RingHom.id S :=
  RingHom.ext h.lift_self_apply
end lift
section Equiv
variable {T : Type*} [CommRing T] [Algebra R T]
def aequiv (h : IsAdjoinRoot S f) (h' : IsAdjoinRoot T f) : S ≃ₐ[R] T :=
  { h.liftHom h'.root h'.aeval_root with
    toFun := h.liftHom h'.root h'.aeval_root
    invFun := h'.liftHom h.root h.aeval_root
    left_inv := fun x => by rw [← h.map_repr x, liftHom_map, aeval_eq, liftHom_map, aeval_eq]
    right_inv := fun x => by rw [← h'.map_repr x, liftHom_map, aeval_eq, liftHom_map, aeval_eq] }
@[simp]
theorem aequiv_map (h : IsAdjoinRoot S f) (h' : IsAdjoinRoot T f) (z : R[X]) :
    h.aequiv h' (h.map z) = h'.map z := by
  rw [aequiv, AlgEquiv.coe_mk, Equiv.coe_fn_mk, liftHom_map, aeval_eq]
@[simp]
theorem aequiv_root (h : IsAdjoinRoot S f) (h' : IsAdjoinRoot T f) :
    h.aequiv h' h.root = h'.root := by
  rw [aequiv, AlgEquiv.coe_mk, Equiv.coe_fn_mk, liftHom_root]
@[simp]
theorem aequiv_self (h : IsAdjoinRoot S f) : h.aequiv h = AlgEquiv.refl := by
  ext a; exact h.lift_self_apply a
@[simp]
theorem aequiv_symm (h : IsAdjoinRoot S f) (h' : IsAdjoinRoot T f) :
    (h.aequiv h').symm = h'.aequiv h := by ext; rfl
@[simp]
theorem lift_aequiv {U : Type*} [CommRing U] (h : IsAdjoinRoot S f) (h' : IsAdjoinRoot T f)
    (i : R →+* U) (x hx z) : h'.lift i x hx (h.aequiv h' z) = h.lift i x hx z := by
  rw [← h.map_repr z, aequiv_map, lift_map, lift_map]
@[simp]
theorem liftHom_aequiv {U : Type*} [CommRing U] [Algebra R U] (h : IsAdjoinRoot S f)
    (h' : IsAdjoinRoot T f) (x : U) (hx z) : h'.liftHom x hx (h.aequiv h' z) = h.liftHom x hx z :=
  h.lift_aequiv h' _ _ hx _
@[simp]
theorem aequiv_aequiv {U : Type*} [CommRing U] [Algebra R U] (h : IsAdjoinRoot S f)
    (h' : IsAdjoinRoot T f) (h'' : IsAdjoinRoot U f) (x) :
    (h'.aequiv h'') (h.aequiv h' x) = h.aequiv h'' x :=
  h.liftHom_aequiv _ _ h''.aeval_root _
@[simp]
theorem aequiv_trans {U : Type*} [CommRing U] [Algebra R U] (h : IsAdjoinRoot S f)
    (h' : IsAdjoinRoot T f) (h'' : IsAdjoinRoot U f) :
    (h.aequiv h').trans (h'.aequiv h'') = h.aequiv h'' := by ext z; exact h.aequiv_aequiv h' h'' z
@[simps! map_apply]
def ofEquiv (h : IsAdjoinRoot S f) (e : S ≃ₐ[R] T) : IsAdjoinRoot T f where
  map := ((e : S ≃+* T) : S →+* T).comp h.map
  map_surjective := e.surjective.comp h.map_surjective
  ker_map := by
    rw [← RingHom.comap_ker, RingHom.ker_coe_equiv, ← RingHom.ker_eq_comap_bot, h.ker_map]
  algebraMap_eq := by
    ext
    simp only [AlgEquiv.commutes, RingHom.comp_apply, AlgEquiv.coe_ringEquiv,
      RingEquiv.coe_toRingHom, ← h.algebraMap_apply]
@[simp]
theorem ofEquiv_root (h : IsAdjoinRoot S f) (e : S ≃ₐ[R] T) : (h.ofEquiv e).root = e h.root := rfl
@[simp]
theorem aequiv_ofEquiv {U : Type*} [CommRing U] [Algebra R U] (h : IsAdjoinRoot S f)
    (h' : IsAdjoinRoot T f) (e : T ≃ₐ[R] U) : h.aequiv (h'.ofEquiv e) = (h.aequiv h').trans e := by
  ext a; rw [← h.map_repr a, aequiv_map, AlgEquiv.trans_apply, aequiv_map, ofEquiv_map_apply]
@[simp]
theorem ofEquiv_aequiv {U : Type*} [CommRing U] [Algebra R U] (h : IsAdjoinRoot S f)
    (h' : IsAdjoinRoot U f) (e : S ≃ₐ[R] T) :
    (h.ofEquiv e).aequiv h' = e.symm.trans (h.aequiv h') := by
  ext a
  rw [← (h.ofEquiv e).map_repr a, aequiv_map, AlgEquiv.trans_apply, ofEquiv_map_apply,
    e.symm_apply_apply, aequiv_map]
end Equiv
end IsAdjoinRoot
namespace IsAdjoinRootMonic
theorem minpoly_eq [IsDomain R] [IsDomain S] [NoZeroSMulDivisors R S] [IsIntegrallyClosed R]
    (h : IsAdjoinRootMonic S f) (hirr : Irreducible f) : minpoly R h.root = f :=
  let ⟨q, hq⟩ := minpoly.isIntegrallyClosed_dvd h.isIntegral_root h.aeval_root
  symm <|
    eq_of_monic_of_associated h.Monic (minpoly.monic h.isIntegral_root) <| by
      convert
        Associated.mul_left (minpoly R h.root) <|
          associated_one_iff_isUnit.2 <|
            (hirr.isUnit_or_isUnit hq).resolve_left <| minpoly.not_isUnit R h.root
      rw [mul_one]
end IsAdjoinRootMonic
section Algebra
open AdjoinRoot IsAdjoinRoot minpoly PowerBasis IsAdjoinRootMonic Algebra
theorem Algebra.adjoin.powerBasis'_minpoly_gen [IsDomain R] [IsDomain S] [NoZeroSMulDivisors R S]
    [IsIntegrallyClosed R] {x : S} (hx' : IsIntegral R x) :
    minpoly R x = minpoly R (Algebra.adjoin.powerBasis' hx').gen := by
  haveI := isDomain_of_prime (prime_of_isIntegrallyClosed hx')
  haveI :=
    noZeroSMulDivisors_of_prime_of_degree_ne_zero (prime_of_isIntegrallyClosed hx')
      (ne_of_lt (degree_pos hx')).symm
  rw [← minpolyGen_eq, adjoin.powerBasis', minpolyGen_map, minpolyGen_eq,
    AdjoinRoot.powerBasis'_gen, ← isAdjoinRootMonic_root_eq_root _ (monic hx'), minpoly_eq]
  exact irreducible hx'
end Algebra
end CommRing