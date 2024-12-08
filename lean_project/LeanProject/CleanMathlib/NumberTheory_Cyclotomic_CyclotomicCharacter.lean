import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
universe u
variable {L : Type u} [CommRing L] [IsDomain L]
variable (n : ℕ) [NeZero n]
theorem rootsOfUnity.integer_power_of_ringEquiv (g : L ≃+* L) :
    ∃ m : ℤ, ∀ t : rootsOfUnity n L, g (t : Lˣ) = (t ^ m : Lˣ) := by
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic ((g : L ≃* L).restrictRootsOfUnity n).toMonoidHom
  exact ⟨m, fun t ↦ Units.ext_iff.1 <| SetCoe.ext_iff.2 <| hm t⟩
theorem rootsOfUnity.integer_power_of_ringEquiv' (g : L ≃+* L) :
    ∃ m : ℤ, ∀ t ∈ rootsOfUnity n L, g (t : Lˣ) = (t ^ m : Lˣ) := by
  simpa using rootsOfUnity.integer_power_of_ringEquiv n g
noncomputable def ModularCyclotomicCharacter_aux (g : L ≃+* L) (n : ℕ) [NeZero n] : ℤ :=
  (rootsOfUnity.integer_power_of_ringEquiv n g).choose
theorem ModularCyclotomicCharacter_aux_spec (g : L ≃+* L) (n : ℕ) [NeZero n] :
    ∀ t : rootsOfUnity n L, g (t : Lˣ) = (t ^ (ModularCyclotomicCharacter_aux g n) : Lˣ) :=
  (rootsOfUnity.integer_power_of_ringEquiv n g).choose_spec
noncomputable def ModularCyclotomicCharacter.toFun (n : ℕ) [NeZero n] (g : L ≃+* L) :
    ZMod (Fintype.card (rootsOfUnity n L)) :=
  ModularCyclotomicCharacter_aux g n
namespace ModularCyclotomicCharacter
local notation "χ₀" => ModularCyclotomicCharacter.toFun
theorem toFun_spec (g : L ≃+* L) {n : ℕ} [NeZero n] (t : rootsOfUnity n L) :
    g (t : Lˣ) = (t ^ (χ₀ n g).val : Lˣ) := by
  rw [ModularCyclotomicCharacter_aux_spec g n t, ← zpow_natCast, ModularCyclotomicCharacter.toFun,
    ZMod.val_intCast, ← Subgroup.coe_zpow]
  exact Units.ext_iff.1 <| SetCoe.ext_iff.2 <|
    zpow_eq_zpow_emod _ pow_card_eq_one (G := rootsOfUnity n L)
theorem toFun_spec' (g : L ≃+* L) {n : ℕ} [NeZero n] {t : Lˣ} (ht : t ∈ rootsOfUnity n L) :
    g t = t ^ (χ₀ n g).val :=
  toFun_spec g ⟨t, ht⟩
theorem toFun_spec'' (g : L ≃+* L) {n : ℕ} [NeZero n] {t : L} (ht : IsPrimitiveRoot t n) :
    g t = t ^ (χ₀ n g).val :=
  toFun_spec' g (SetLike.coe_mem ht.toRootsOfUnity)
theorem toFun_unique (g : L ≃+* L) (c : ZMod (Fintype.card (rootsOfUnity n L)))
    (hc : ∀ t : rootsOfUnity n L, g (t : Lˣ) = (t ^ c.val : Lˣ)) : c = χ₀ n g := by
  apply IsCyclic.ext Nat.card_eq_fintype_card (fun ζ ↦ ?_)
  specialize hc ζ
  suffices ((ζ ^ c.val : Lˣ) : L) = (ζ ^ (χ₀ n g).val : Lˣ) by exact_mod_cast this
  rw [← toFun_spec g ζ, hc]
theorem toFun_unique' (g : L ≃+* L) (c : ZMod (Fintype.card (rootsOfUnity n L)))
    (hc : ∀ t ∈ rootsOfUnity n L, g t = t ^ c.val) : c = χ₀ n g :=
  toFun_unique n g c (fun ⟨_, ht⟩ ↦ hc _ ht)
lemma id : χ₀ n (RingEquiv.refl L) = 1 := by
  refine (toFun_unique n (RingEquiv.refl L) 1 <| fun t ↦ ?_).symm
  have : 1 ≤ Fintype.card { x // x ∈ rootsOfUnity n L } := Fin.size_positive'
  obtain (h | h) := this.lt_or_eq
  · have := Fact.mk h
    simp [ZMod.val_one]
  · have := Fintype.card_le_one_iff_subsingleton.mp h.ge
    obtain rfl : t = 1 := Subsingleton.elim t 1
    simp
lemma comp (g h : L ≃+* L) : χ₀ n (g * h) =
    χ₀ n g * χ₀ n h := by
  refine (toFun_unique n (g * h) _ <| fun ζ ↦ ?_).symm
  change g (h (ζ : Lˣ)) = _
  rw [toFun_spec, ← Subgroup.coe_pow, toFun_spec, mul_comm, Subgroup.coe_pow, ← pow_mul,
    ← Subgroup.coe_pow]
  congr 2
  norm_cast
  simp only [pow_eq_pow_iff_modEq, ← ZMod.natCast_eq_natCast_iff, SubmonoidClass.coe_pow,
    ZMod.natCast_val, Nat.cast_mul, ZMod.cast_mul (m := orderOf ζ) orderOf_dvd_card]
end ModularCyclotomicCharacter
variable (L)
noncomputable
def ModularCyclotomicCharacter' (n : ℕ) [NeZero n] :
    (L ≃+* L) →* (ZMod (Fintype.card { x // x ∈ rootsOfUnity n L }))ˣ := MonoidHom.toHomUnits
  { toFun := ModularCyclotomicCharacter.toFun n
    map_one' := ModularCyclotomicCharacter.id n
    map_mul' := ModularCyclotomicCharacter.comp n }
lemma spec' (g : L ≃+* L) {t : Lˣ} (ht : t ∈ rootsOfUnity n L) :
    g t = t ^ ((ModularCyclotomicCharacter' L n g) : ZMod
      (Fintype.card { x // x ∈ rootsOfUnity n L })).val :=
  ModularCyclotomicCharacter.toFun_spec' g ht
lemma unique' (g : L ≃+* L) {c : ZMod (Fintype.card { x // x ∈ rootsOfUnity n L })}
    (hc : ∀ t ∈ rootsOfUnity n L, g t = t ^ c.val) :
    c = ModularCyclotomicCharacter' L n g :=
  ModularCyclotomicCharacter.toFun_unique' _ _ _ hc
noncomputable def ModularCyclotomicCharacter {n : ℕ} [NeZero n]
    (hn : Fintype.card { x // x ∈ rootsOfUnity n L } = n) :
    (L ≃+* L) →* (ZMod n)ˣ :=
  (Units.mapEquiv <| (ZMod.ringEquivCongr hn).toMulEquiv).toMonoidHom.comp
  (ModularCyclotomicCharacter' L n)
namespace ModularCyclotomicCharacter
variable {n : ℕ} [NeZero n] (hn : Fintype.card { x // x ∈ rootsOfUnity n L } = n)
lemma spec (g : L ≃+* L) {t : Lˣ} (ht : t ∈ rootsOfUnity n L) :
    g t = t ^ ((ModularCyclotomicCharacter L hn g) : ZMod n).val := by
  rw [toFun_spec' g ht]
  congr 1
  exact (ZMod.ringEquivCongr_val _ _).symm
lemma unique (g : L ≃+* L) {c : ZMod n} (hc : ∀ t ∈ rootsOfUnity n L, g t = t ^ c.val) :
    c = ModularCyclotomicCharacter L hn g := by
  change c = (ZMod.ringEquivCongr hn) (toFun n g)
  rw [← toFun_unique' n g (ZMod.ringEquivCongr hn.symm c)
    (fun t ht ↦ by rw [hc t ht, ZMod.ringEquivCongr_val]), ← ZMod.ringEquivCongr_symm hn,
    RingEquiv.apply_symm_apply]
end ModularCyclotomicCharacter
variable {L}
lemma IsPrimitiveRoot.autToPow_eq_ModularCyclotomicCharacter (n : ℕ) [NeZero n]
    (R : Type*) [CommRing R] [Algebra R L] {μ : L} (hμ : IsPrimitiveRoot μ n) (g : L ≃ₐ[R] L) :
    hμ.autToPow R g = ModularCyclotomicCharacter L hμ.card_rootsOfUnity g := by
  ext
  apply ZMod.val_injective
  apply hμ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  simpa only [autToPow_spec R hμ g, ModularCyclotomicCharacter, RingEquiv.toMulEquiv_eq_coe,
    MulEquiv.toMonoidHom_eq_coe, ModularCyclotomicCharacter', MonoidHom.coe_comp, MonoidHom.coe_coe,
    Function.comp_apply, Units.coe_mapEquiv, MonoidHom.coe_toHomUnits, MonoidHom.coe_mk,
    OneHom.coe_mk, RingEquiv.coe_toMulEquiv, ZMod.ringEquivCongr_val, AlgEquiv.coe_ringEquiv]
    using ModularCyclotomicCharacter.toFun_spec'' g hμ