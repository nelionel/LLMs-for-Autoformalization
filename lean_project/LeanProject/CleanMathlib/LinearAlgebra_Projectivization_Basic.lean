import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
variable (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]
def projectivizationSetoid : Setoid { v : V // v ≠ 0 } :=
  (MulAction.orbitRel Kˣ V).comap (↑)
def Projectivization := Quotient (projectivizationSetoid K V)
scoped[LinearAlgebra.Projectivization] notation "ℙ" => Projectivization
namespace Projectivization
open scoped LinearAlgebra.Projectivization
variable {V}
def mk (v : V) (hv : v ≠ 0) : ℙ K V :=
  Quotient.mk'' ⟨v, hv⟩
def mk' (v : { v : V // v ≠ 0 }) : ℙ K V :=
  Quotient.mk'' v
@[simp]
theorem mk'_eq_mk (v : { v : V // v ≠ 0 }) : mk' K v = mk K ↑v v.2 := rfl
instance [Nontrivial V] : Nonempty (ℙ K V) :=
  let ⟨v, hv⟩ := exists_ne (0 : V)
  ⟨mk K v hv⟩
variable {K}
protected def lift {α : Type*} (f : { v : V // v ≠ 0 } → α)
    (hf : ∀ (a b : { v : V // v ≠ 0 }) (t : K), a = t • (b : V) → f a = f b)
    (x : ℙ K V) : α :=
  Quotient.lift f (by rintro ⟨-, hv⟩ ⟨w, hw⟩ ⟨⟨t, -⟩, rfl⟩; exact hf ⟨_, hv⟩ ⟨w, hw⟩ t rfl) x
@[simp]
protected lemma lift_mk {α : Type*} (f : { v : V // v ≠ 0 } → α)
    (hf : ∀ (a b : { v : V // v ≠ 0 }) (t : K), a = t • (b : V) → f a = f b)
    (v : V) (hv : v ≠ 0) :
    Projectivization.lift f hf (mk K v hv) = f ⟨v, hv⟩ :=
  rfl
protected noncomputable def rep (v : ℙ K V) : V :=
  v.out
theorem rep_nonzero (v : ℙ K V) : v.rep ≠ 0 :=
  v.out.2
@[simp]
theorem mk_rep (v : ℙ K V) : mk K v.rep v.rep_nonzero = v := Quotient.out_eq' _
open Module
protected def submodule (v : ℙ K V) : Submodule K V :=
  (Quotient.liftOn' v fun v => K ∙ (v : V)) <| by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨x, rfl : x • b = a⟩
    exact Submodule.span_singleton_group_smul_eq _ x _
variable (K)
theorem mk_eq_mk_iff (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) :
    mk K v hv = mk K w hw ↔ ∃ a : Kˣ, a • w = v :=
  Quotient.eq''
theorem mk_eq_mk_iff' (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) :
    mk K v hv = mk K w hw ↔ ∃ a : K, a • w = v := by
  rw [mk_eq_mk_iff K v w hv hw]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    refine ⟨Units.mk0 a fun c => hv.symm ?_, ha⟩
    rwa [c, zero_smul] at ha
theorem exists_smul_eq_mk_rep (v : V) (hv : v ≠ 0) : ∃ a : Kˣ, a • v = (mk K v hv).rep :=
  (mk_eq_mk_iff K _ _ (rep_nonzero _) hv).1 (mk_rep _)
variable {K}
@[elab_as_elim, cases_eliminator, induction_eliminator]
theorem ind {P : ℙ K V → Prop} (h : ∀ (v : V) (h : v ≠ 0), P (mk K v h)) : ∀ p, P p :=
  Quotient.ind' <| Subtype.rec <| h
@[simp]
theorem submodule_mk (v : V) (hv : v ≠ 0) : (mk K v hv).submodule = K ∙ v :=
  rfl
theorem submodule_eq (v : ℙ K V) : v.submodule = K ∙ v.rep := by
  conv_lhs => rw [← v.mk_rep]
  rfl
theorem finrank_submodule (v : ℙ K V) : finrank K v.submodule = 1 := by
  rw [submodule_eq]
  exact finrank_span_singleton v.rep_nonzero
instance (v : ℙ K V) : FiniteDimensional K v.submodule := by
  rw [← v.mk_rep]
  change FiniteDimensional K (K ∙ v.rep)
  infer_instance
theorem submodule_injective :
    Function.Injective (Projectivization.submodule : ℙ K V → Submodule K V) := fun u v h ↦ by
  induction' u using ind with u hu
  induction' v using ind with v hv
  rw [submodule_mk, submodule_mk, Submodule.span_singleton_eq_span_singleton] at h
  exact ((mk_eq_mk_iff K v u hv hu).2 h).symm
variable (K V)
noncomputable def equivSubmodule : ℙ K V ≃ { H : Submodule K V // finrank K H = 1 } :=
  (Equiv.ofInjective _ submodule_injective).trans <| .subtypeEquiv (.refl _) fun H ↦ by
    refine ⟨fun ⟨v, hv⟩ ↦ hv ▸ v.finrank_submodule, fun h ↦ ?_⟩
    rcases finrank_eq_one_iff'.1 h with ⟨v : H, hv₀, hv : ∀ w : H, _⟩
    use mk K (v : V) (Subtype.coe_injective.ne hv₀)
    rw [submodule_mk, SetLike.ext'_iff, Submodule.span_singleton_eq_range]
    refine (Set.range_subset_iff.2 fun _ ↦ H.smul_mem _ v.2).antisymm fun x hx ↦ ?_
    rcases hv ⟨x, hx⟩ with ⟨c, hc⟩
    exact ⟨c, congr_arg Subtype.val hc⟩
variable {K V}
noncomputable def mk'' (H : Submodule K V) (h : finrank K H = 1) : ℙ K V :=
  (equivSubmodule K V).symm ⟨H, h⟩
@[simp]
theorem submodule_mk'' (H : Submodule K V) (h : finrank K H = 1) : (mk'' H h).submodule = H :=
  congr_arg Subtype.val <| (equivSubmodule K V).apply_symm_apply ⟨H, h⟩
@[simp]
theorem mk''_submodule (v : ℙ K V) : mk'' v.submodule v.finrank_submodule = v :=
  (equivSubmodule K V).symm_apply_apply v
section Map
variable {L W : Type*} [DivisionRing L] [AddCommGroup W] [Module L W]
def map {σ : K →+* L} (f : V →ₛₗ[σ] W) (hf : Function.Injective f) : ℙ K V → ℙ L W :=
  Quotient.map' (fun v => ⟨f v, fun c => v.2 (hf (by simp [c]))⟩)
    (by
      rintro ⟨u, hu⟩ ⟨v, hv⟩ ⟨a, ha⟩
      use Units.map σ.toMonoidHom a
      dsimp at ha ⊢
      erw [← f.map_smulₛₗ, ha])
theorem map_mk {σ : K →+* L} (f : V →ₛₗ[σ] W) (hf : Function.Injective f) (v : V) (hv : v ≠ 0) :
    map f hf (mk K v hv) = mk L (f v) (map_zero f ▸ hf.ne hv) :=
  rfl
theorem map_injective {σ : K →+* L} {τ : L →+* K} [RingHomInvPair σ τ] (f : V →ₛₗ[σ] W)
    (hf : Function.Injective f) : Function.Injective (map f hf) := fun u v h ↦ by
  induction' u using ind with u hu; induction' v using ind with v hv
  simp only [map_mk, mk_eq_mk_iff'] at h ⊢
  rcases h with ⟨a, ha⟩
  refine ⟨τ a, hf ?_⟩
  rwa [f.map_smulₛₗ, RingHomInvPair.comp_apply_eq₂]
@[simp]
theorem map_id : map (LinearMap.id : V →ₗ[K] V) (LinearEquiv.refl K V).injective = id := by
  ext ⟨v⟩
  rfl
theorem map_comp {F U : Type*} [Field F] [AddCommGroup U] [Module F U] {σ : K →+* L} {τ : L →+* F}
    {γ : K →+* F} [RingHomCompTriple σ τ γ] (f : V →ₛₗ[σ] W) (hf : Function.Injective f)
    (g : W →ₛₗ[τ] U) (hg : Function.Injective g) :
    map (g.comp f) (hg.comp hf) = map g hg ∘ map f hf := by
  ext ⟨v⟩
  rfl
end Map
end Projectivization