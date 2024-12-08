import Mathlib.Algebra.CharP.ExpChar
import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.FieldTheory.SeparableClosure
open Module Polynomial IntermediateField Field Finsupp
noncomputable section
universe u v w
section IsPurelyInseparable
variable (F : Type u) (E : Type v) [CommRing F] [Ring E] [Algebra F E]
variable (K : Type w) [Ring K] [Algebra F K]
class IsPurelyInseparable : Prop where
  isIntegral : Algebra.IsIntegral F E
  inseparable' (x : E) : IsSeparable F x → x ∈ (algebraMap F E).range
attribute [instance] IsPurelyInseparable.isIntegral
variable {E} in
theorem IsPurelyInseparable.isIntegral' [IsPurelyInseparable F E] (x : E) : IsIntegral F x :=
  Algebra.IsIntegral.isIntegral _
theorem IsPurelyInseparable.isAlgebraic [Nontrivial F] [IsPurelyInseparable F E] :
    Algebra.IsAlgebraic F E := inferInstance
variable {E}
theorem IsPurelyInseparable.inseparable [IsPurelyInseparable F E] :
    ∀ x : E, IsSeparable F x → x ∈ (algebraMap F E).range :=
  IsPurelyInseparable.inseparable'
variable {F K}
theorem isPurelyInseparable_iff : IsPurelyInseparable F E ↔ ∀ x : E,
    IsIntegral F x ∧ (IsSeparable F x → x ∈ (algebraMap F E).range) :=
  ⟨fun h x ↦ ⟨h.isIntegral' _ x, h.inseparable' x⟩, fun h ↦ ⟨⟨fun x ↦ (h x).1⟩, fun x ↦ (h x).2⟩⟩
theorem AlgEquiv.isPurelyInseparable (e : K ≃ₐ[F] E) [IsPurelyInseparable F K] :
    IsPurelyInseparable F E := by
  refine ⟨⟨fun _ ↦ by rw [← isIntegral_algEquiv e.symm]; exact IsPurelyInseparable.isIntegral' F _⟩,
    fun x h ↦ ?_⟩
  rw [IsSeparable, ← minpoly.algEquiv_eq e.symm] at h
  simpa only [RingHom.mem_range, algebraMap_eq_apply] using IsPurelyInseparable.inseparable F _ h
theorem AlgEquiv.isPurelyInseparable_iff (e : K ≃ₐ[F] E) :
    IsPurelyInseparable F K ↔ IsPurelyInseparable F E :=
  ⟨fun _ ↦ e.isPurelyInseparable, fun _ ↦ e.symm.isPurelyInseparable⟩
instance Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed
    {F : Type u} {E : Type v} [Field F] [Ring E] [IsDomain E] [Algebra F E]
    [Algebra.IsAlgebraic F E]
    [IsSepClosed F] : IsPurelyInseparable F E :=
  ⟨inferInstance, fun x h ↦ minpoly.mem_range_of_degree_eq_one F x <|
    IsSepClosed.degree_eq_one_of_irreducible F (minpoly.irreducible
      (Algebra.IsIntegral.isIntegral _)) h⟩
variable (F E K)
theorem IsPurelyInseparable.surjective_algebraMap_of_isSeparable
    [IsPurelyInseparable F E] [Algebra.IsSeparable F E] : Function.Surjective (algebraMap F E) :=
  fun x ↦ IsPurelyInseparable.inseparable F x (Algebra.IsSeparable.isSeparable F x)
theorem IsPurelyInseparable.bijective_algebraMap_of_isSeparable
    [Nontrivial E] [NoZeroSMulDivisors F E]
    [IsPurelyInseparable F E] [Algebra.IsSeparable F E] : Function.Bijective (algebraMap F E) :=
  ⟨NoZeroSMulDivisors.algebraMap_injective F E, surjective_algebraMap_of_isSeparable F E⟩
variable {F E} in
theorem Subalgebra.eq_bot_of_isPurelyInseparable_of_isSeparable (L : Subalgebra F E)
    [IsPurelyInseparable F L] [Algebra.IsSeparable F L] : L = ⊥ := bot_unique fun x hx ↦ by
  obtain ⟨y, hy⟩ := IsPurelyInseparable.surjective_algebraMap_of_isSeparable F L ⟨x, hx⟩
  exact ⟨y, congr_arg (Subalgebra.val _) hy⟩
theorem IntermediateField.eq_bot_of_isPurelyInseparable_of_isSeparable
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E] (L : IntermediateField F E)
    [IsPurelyInseparable F L] [Algebra.IsSeparable F L] : L = ⊥ := bot_unique fun x hx ↦ by
  obtain ⟨y, hy⟩ := IsPurelyInseparable.surjective_algebraMap_of_isSeparable F L ⟨x, hx⟩
  exact ⟨y, congr_arg (algebraMap L E) hy⟩
theorem separableClosure.eq_bot_of_isPurelyInseparable
    (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E] [IsPurelyInseparable F E] :
    separableClosure F E = ⊥ :=
  bot_unique fun x h ↦ IsPurelyInseparable.inseparable F x (mem_separableClosure_iff.1 h)
theorem separableClosure.eq_bot_iff
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E] [Algebra.IsAlgebraic F E] :
    separableClosure F E = ⊥ ↔ IsPurelyInseparable F E :=
  ⟨fun h ↦ isPurelyInseparable_iff.2 fun x ↦ ⟨Algebra.IsIntegral.isIntegral x, fun hs ↦ by
    simpa only [h] using mem_separableClosure_iff.2 hs⟩, fun _ ↦ eq_bot_of_isPurelyInseparable F E⟩
instance isPurelyInseparable_self : IsPurelyInseparable F F :=
  ⟨inferInstance, fun x _ ↦ ⟨x, rfl⟩⟩
section
variable (F : Type u) {E : Type v} [Field F] [Ring E] [IsDomain E] [Algebra F E]
variable (q : ℕ) [ExpChar F q] (x : E)
@[stacks 09HE]
theorem isPurelyInseparable_iff_pow_mem :
    IsPurelyInseparable F E ↔ ∀ x : E, ∃ n : ℕ, x ^ q ^ n ∈ (algebraMap F E).range := by
  rw [isPurelyInseparable_iff]
  refine ⟨fun h x ↦ ?_, fun h x ↦ ?_⟩
  · obtain ⟨g, h1, n, h2⟩ := (minpoly.irreducible (h x).1).hasSeparableContraction q
    exact ⟨n, (h _).2 <| h1.of_dvd <| minpoly.dvd F _ <| by
      simpa only [expand_aeval, minpoly.aeval] using congr_arg (aeval x) h2⟩
  have hdeg := (minpoly.natSepDegree_eq_one_iff_pow_mem q).2 (h x)
  have halg : IsIntegral F x := by_contra fun h' ↦ by
    simp only [minpoly.eq_zero h', natSepDegree_zero, zero_ne_one] at hdeg
  refine ⟨halg, fun hsep ↦ ?_⟩
  rwa [hsep.natSepDegree_eq_natDegree, minpoly.natDegree_eq_one_iff] at hdeg
theorem IsPurelyInseparable.pow_mem [IsPurelyInseparable F E] :
    ∃ n : ℕ, x ^ q ^ n ∈ (algebraMap F E).range :=
  (isPurelyInseparable_iff_pow_mem F q).1 ‹_› x
end
end IsPurelyInseparable
variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
variable (K : Type w) [Field K] [Algebra F K]
section perfectClosure
@[stacks 09HH]
def perfectClosure : IntermediateField F E where
  carrier := {x : E | ∃ n : ℕ, x ^ (ringExpChar F) ^ n ∈ (algebraMap F E).range}
  add_mem' := by
    rintro x y ⟨n, hx⟩ ⟨m, hy⟩
    use n + m
    have := expChar_of_injective_algebraMap (algebraMap F E).injective (ringExpChar F)
    rw [add_pow_expChar_pow, pow_add, pow_mul, mul_comm (_ ^ n), pow_mul]
    exact add_mem (pow_mem hx _) (pow_mem hy _)
  mul_mem' := by
    rintro x y ⟨n, hx⟩ ⟨m, hy⟩
    use n + m
    rw [mul_pow, pow_add, pow_mul, mul_comm (_ ^ n), pow_mul]
    exact mul_mem (pow_mem hx _) (pow_mem hy _)
  inv_mem' := by
    rintro x ⟨n, hx⟩
    use n; rw [inv_pow]
    apply inv_mem (id hx : _ ∈ (⊥ : IntermediateField F E))
  algebraMap_mem' := fun x ↦ ⟨0, by rw [pow_zero, pow_one]; exact ⟨x, rfl⟩⟩
variable {F E}
theorem mem_perfectClosure_iff {x : E} :
    x ∈ perfectClosure F E ↔ ∃ n : ℕ, x ^ (ringExpChar F) ^ n ∈ (algebraMap F E).range := Iff.rfl
theorem mem_perfectClosure_iff_pow_mem (q : ℕ) [ExpChar F q] {x : E} :
    x ∈ perfectClosure F E ↔ ∃ n : ℕ, x ^ q ^ n ∈ (algebraMap F E).range := by
  rw [mem_perfectClosure_iff, ringExpChar.eq F q]
theorem mem_perfectClosure_iff_natSepDegree_eq_one {x : E} :
    x ∈ perfectClosure F E ↔ (minpoly F x).natSepDegree = 1 := by
  rw [mem_perfectClosure_iff, minpoly.natSepDegree_eq_one_iff_pow_mem (ringExpChar F)]
theorem isPurelyInseparable_iff_perfectClosure_eq_top :
    IsPurelyInseparable F E ↔ perfectClosure F E = ⊤ := by
  rw [isPurelyInseparable_iff_pow_mem F (ringExpChar F)]
  exact ⟨fun H ↦ top_unique fun x _ ↦ H x, fun H _ ↦ H.ge trivial⟩
variable (F E)
instance perfectClosure.isPurelyInseparable : IsPurelyInseparable F (perfectClosure F E) := by
  rw [isPurelyInseparable_iff_pow_mem F (ringExpChar F)]
  exact fun ⟨_, n, y, h⟩ ↦ ⟨n, y, (algebraMap _ E).injective h⟩
instance perfectClosure.isAlgebraic : Algebra.IsAlgebraic F (perfectClosure F E) :=
  IsPurelyInseparable.isAlgebraic F _
theorem perfectClosure.eq_bot_of_isSeparable [Algebra.IsSeparable F E] : perfectClosure F E = ⊥ :=
  haveI := Algebra.isSeparable_tower_bot_of_isSeparable F (perfectClosure F E) E
  eq_bot_of_isPurelyInseparable_of_isSeparable _
theorem le_perfectClosure (L : IntermediateField F E) [h : IsPurelyInseparable F L] :
    L ≤ perfectClosure F E := by
  rw [isPurelyInseparable_iff_pow_mem F (ringExpChar F)] at h
  intro x hx
  obtain ⟨n, y, hy⟩ := h ⟨x, hx⟩
  exact ⟨n, y, congr_arg (algebraMap L E) hy⟩
theorem le_perfectClosure_iff (L : IntermediateField F E) :
    L ≤ perfectClosure F E ↔ IsPurelyInseparable F L := by
  refine ⟨fun h ↦ (isPurelyInseparable_iff_pow_mem F (ringExpChar F)).2 fun x ↦ ?_,
    fun _ ↦ le_perfectClosure F E L⟩
  obtain ⟨n, y, hy⟩ := h x.2
  exact ⟨n, y, (algebraMap L E).injective hy⟩
theorem separableClosure_inf_perfectClosure : separableClosure F E ⊓ perfectClosure F E = ⊥ :=
  haveI := (le_separableClosure_iff F E _).mp (inf_le_left (b := perfectClosure F E))
  haveI := (le_perfectClosure_iff F E _).mp (inf_le_right (a := separableClosure F E))
  eq_bot_of_isPurelyInseparable_of_isSeparable _
section map
variable {F E K}
theorem map_mem_perfectClosure_iff (i : E →ₐ[F] K) {x : E} :
    i x ∈ perfectClosure F K ↔ x ∈ perfectClosure F E := by
  simp_rw [mem_perfectClosure_iff]
  refine ⟨fun ⟨n, y, h⟩ ↦ ⟨n, y, ?_⟩, fun ⟨n, y, h⟩ ↦ ⟨n, y, ?_⟩⟩
  · apply_fun i using i.injective
    rwa [AlgHom.commutes, map_pow]
  simpa only [AlgHom.commutes, map_pow] using congr_arg i h
theorem perfectClosure.comap_eq_of_algHom (i : E →ₐ[F] K) :
    (perfectClosure F K).comap i = perfectClosure F E := by
  ext x
  exact map_mem_perfectClosure_iff i
theorem perfectClosure.map_le_of_algHom (i : E →ₐ[F] K) :
    (perfectClosure F E).map i ≤ perfectClosure F K :=
  map_le_iff_le_comap.mpr (perfectClosure.comap_eq_of_algHom i).ge
theorem perfectClosure.map_eq_of_algEquiv (i : E ≃ₐ[F] K) :
    (perfectClosure F E).map i.toAlgHom = perfectClosure F K :=
  (map_le_of_algHom i.toAlgHom).antisymm (fun x hx ↦ ⟨i.symm x,
    (map_mem_perfectClosure_iff i.symm.toAlgHom).2 hx, i.right_inv x⟩)
def perfectClosure.algEquivOfAlgEquiv (i : E ≃ₐ[F] K) :
    perfectClosure F E ≃ₐ[F] perfectClosure F K :=
  (intermediateFieldMap i _).trans (equivOfEq (map_eq_of_algEquiv i))
alias AlgEquiv.perfectClosure := perfectClosure.algEquivOfAlgEquiv
end map
instance perfectClosure.perfectRing (p : ℕ) [ExpChar E p]
    [PerfectRing E p] : PerfectRing (perfectClosure F E) p := .ofSurjective _ p fun x ↦ by
  haveI := RingHom.expChar _ (algebraMap F E).injective p
  obtain ⟨x', hx⟩ := surjective_frobenius E p x.1
  obtain ⟨n, y, hy⟩ := (mem_perfectClosure_iff_pow_mem p).1 x.2
  rw [frobenius_def] at hx
  rw [← hx, ← pow_mul, ← pow_succ'] at hy
  exact ⟨⟨x', (mem_perfectClosure_iff_pow_mem p).2 ⟨n + 1, y, hy⟩⟩, by
    simp_rw [frobenius_def, SubmonoidClass.mk_pow, hx]⟩
instance perfectClosure.perfectField [PerfectField E] : PerfectField (perfectClosure F E) :=
  PerfectRing.toPerfectField _ (ringExpChar E)
end perfectClosure
section IsPurelyInseparable
theorem IsPurelyInseparable.tower_bot [Algebra E K] [IsScalarTower F E K]
    [IsPurelyInseparable F K] : IsPurelyInseparable F E := by
  refine ⟨⟨fun x ↦ (isIntegral' F (algebraMap E K x)).tower_bot_of_field⟩, fun x h ↦ ?_⟩
  rw [IsSeparable, ← minpoly.algebraMap_eq (algebraMap E K).injective] at h
  obtain ⟨y, h⟩ := inseparable F _ h
  exact ⟨y, (algebraMap E K).injective (h.symm ▸ (IsScalarTower.algebraMap_apply F E K y).symm)⟩
theorem IsPurelyInseparable.tower_top [Algebra E K] [IsScalarTower F E K]
    [h : IsPurelyInseparable F K] : IsPurelyInseparable E K := by
  obtain ⟨q, _⟩ := ExpChar.exists F
  haveI := expChar_of_injective_algebraMap (algebraMap F E).injective q
  rw [isPurelyInseparable_iff_pow_mem _ q] at h ⊢
  intro x
  obtain ⟨n, y, h⟩ := h x
  exact ⟨n, (algebraMap F E) y, h.symm ▸ (IsScalarTower.algebraMap_apply F E K y).symm⟩
@[stacks 02JJ "See also 00GM"]
theorem IsPurelyInseparable.trans [Algebra E K] [IsScalarTower F E K]
    [h1 : IsPurelyInseparable F E] [h2 : IsPurelyInseparable E K] : IsPurelyInseparable F K := by
  obtain ⟨q, _⟩ := ExpChar.exists F
  haveI := expChar_of_injective_algebraMap (algebraMap F E).injective q
  rw [isPurelyInseparable_iff_pow_mem _ q] at h1 h2 ⊢
  intro x
  obtain ⟨n, y, h2⟩ := h2 x
  obtain ⟨m, z, h1⟩ := h1 y
  refine ⟨n + m, z, ?_⟩
  rw [IsScalarTower.algebraMap_apply F E K, h1, map_pow, h2, ← pow_mul, ← pow_add]
namespace IntermediateField
variable (M : IntermediateField F K)
instance isPurelyInseparable_tower_bot [IsPurelyInseparable F K] : IsPurelyInseparable F M :=
  IsPurelyInseparable.tower_bot F M K
instance isPurelyInseparable_tower_top [IsPurelyInseparable F K] : IsPurelyInseparable M K :=
  IsPurelyInseparable.tower_top F M K
end IntermediateField
variable {E}
theorem isPurelyInseparable_iff_natSepDegree_eq_one :
    IsPurelyInseparable F E ↔ ∀ x : E, (minpoly F x).natSepDegree = 1 := by
  obtain ⟨q, _⟩ := ExpChar.exists F
  simp_rw [isPurelyInseparable_iff_pow_mem F q, minpoly.natSepDegree_eq_one_iff_pow_mem q]
theorem IsPurelyInseparable.natSepDegree_eq_one [IsPurelyInseparable F E] (x : E) :
    (minpoly F x).natSepDegree = 1 :=
  (isPurelyInseparable_iff_natSepDegree_eq_one F).1 ‹_› x
theorem isPurelyInseparable_iff_minpoly_eq_X_pow_sub_C (q : ℕ) [hF : ExpChar F q] :
    IsPurelyInseparable F E ↔ ∀ x : E, ∃ (n : ℕ) (y : F), minpoly F x = X ^ q ^ n - C y := by
  simp_rw [isPurelyInseparable_iff_natSepDegree_eq_one,
    minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C q]
theorem IsPurelyInseparable.minpoly_eq_X_pow_sub_C (q : ℕ) [ExpChar F q] [IsPurelyInseparable F E]
    (x : E) : ∃ (n : ℕ) (y : F), minpoly F x = X ^ q ^ n - C y :=
  (isPurelyInseparable_iff_minpoly_eq_X_pow_sub_C F q).1 ‹_› x
theorem isPurelyInseparable_iff_minpoly_eq_X_sub_C_pow (q : ℕ) [hF : ExpChar F q] :
    IsPurelyInseparable F E ↔
    ∀ x : E, ∃ n : ℕ, (minpoly F x).map (algebraMap F E) = (X - C x) ^ q ^ n := by
  simp_rw [isPurelyInseparable_iff_natSepDegree_eq_one,
    minpoly.natSepDegree_eq_one_iff_eq_X_sub_C_pow q]
theorem IsPurelyInseparable.minpoly_eq_X_sub_C_pow (q : ℕ) [ExpChar F q] [IsPurelyInseparable F E]
    (x : E) : ∃ n : ℕ, (minpoly F x).map (algebraMap F E) = (X - C x) ^ q ^ n :=
  (isPurelyInseparable_iff_minpoly_eq_X_sub_C_pow F q).1 ‹_› x
variable (E)
variable {F E} in
theorem isPurelyInseparable_of_finSepDegree_eq_one
    (hdeg : finSepDegree F E = 1) : IsPurelyInseparable F E := by
  by_cases H : Algebra.IsAlgebraic F E
  · rw [isPurelyInseparable_iff]
    refine fun x ↦ ⟨Algebra.IsIntegral.isIntegral x, fun hsep ↦ ?_⟩
    have : Algebra.IsAlgebraic F⟮x⟯ E := Algebra.IsAlgebraic.tower_top (K := F) F⟮x⟯
    have := finSepDegree_mul_finSepDegree_of_isAlgebraic F F⟮x⟯ E
    rw [hdeg, mul_eq_one, (finSepDegree_adjoin_simple_eq_finrank_iff F E x
        (Algebra.IsAlgebraic.isAlgebraic x)).2 hsep,
      IntermediateField.finrank_eq_one_iff] at this
    simpa only [this.1] using mem_adjoin_simple_self F x
  · rw [← Algebra.transcendental_iff_not_isAlgebraic] at H
    simp [finSepDegree_eq_zero_of_transcendental F E] at hdeg
namespace IsPurelyInseparable
variable [IsPurelyInseparable F E] (R L : Type*) [CommSemiring R] [Algebra R F] [Algebra R E]
theorem injective_comp_algebraMap [CommRing L] [IsReduced L] :
    Function.Injective fun f : E →+* L ↦ f.comp (algebraMap F E) := fun f g heq ↦ by
  ext x
  let q := ringExpChar F
  obtain ⟨n, y, h⟩ := IsPurelyInseparable.pow_mem F q x
  replace heq := congr($heq y)
  simp_rw [RingHom.comp_apply, h, map_pow] at heq
  nontriviality L
  haveI := expChar_of_injective_ringHom (f.comp (algebraMap F E)).injective q
  exact iterateFrobenius_inj L q n heq
theorem injective_restrictDomain [CommRing L] [IsReduced L] [Algebra R L] [IsScalarTower R F E] :
    Function.Injective (AlgHom.restrictDomain (A := R) F (C := E) (D := L)) := fun _ _ eq ↦
  AlgHom.coe_ringHom_injective <| injective_comp_algebraMap F E L <| congr_arg AlgHom.toRingHom eq
instance [Field L] [PerfectField L] [Algebra F L] : Nonempty (E →ₐ[F] L) :=
  nonempty_algHom_of_splits fun x ↦ ⟨IsPurelyInseparable.isIntegral' _ _,
    have ⟨q, _⟩ := ExpChar.exists F
    PerfectField.splits_of_natSepDegree_eq_one (algebraMap F L)
      ((minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C q).mpr <|
        IsPurelyInseparable.minpoly_eq_X_pow_sub_C F q x)⟩
theorem bijective_comp_algebraMap [Field L] [PerfectField L] :
    Function.Bijective fun f : E →+* L ↦ f.comp (algebraMap F E) :=
  ⟨injective_comp_algebraMap F E L, fun g ↦ let _ := g.toAlgebra
    ⟨_, (Classical.arbitrary <| E →ₐ[F] L).comp_algebraMap⟩⟩
theorem bijective_restrictDomain [Field L] [PerfectField L] [Algebra R L] [IsScalarTower R F E] :
    Function.Bijective (AlgHom.restrictDomain (A := R) F (C := E) (D := L)) :=
  ⟨injective_restrictDomain F E R L, fun g ↦ let _ := g.toAlgebra
    let f := Classical.arbitrary (E →ₐ[F] L)
    ⟨f.restrictScalars R, AlgHom.coe_ringHom_injective f.comp_algebraMap⟩⟩
end IsPurelyInseparable
instance instSubsingletonAlgHomOfIsPurelyInseparable [IsPurelyInseparable F E] (L : Type w)
    [CommRing L] [IsReduced L] [Algebra F L] : Subsingleton (E →ₐ[F] L) where
  allEq f g := AlgHom.coe_ringHom_injective <|
    IsPurelyInseparable.injective_comp_algebraMap F E L (by simp_rw [AlgHom.comp_algebraMap])
instance instUniqueAlgHomOfIsPurelyInseparable [IsPurelyInseparable F E] (L : Type w)
    [CommRing L] [IsReduced L] [Algebra F L] [Algebra E L] [IsScalarTower F E L] :
    Unique (E →ₐ[F] L) := uniqueOfSubsingleton (IsScalarTower.toAlgHom F E L)
instance instUniqueEmbOfIsPurelyInseparable [IsPurelyInseparable F E] :
    Unique (Emb F E) := instUniqueAlgHomOfIsPurelyInseparable F E _
theorem IsPurelyInseparable.finSepDegree_eq_one [IsPurelyInseparable F E] :
    finSepDegree F E = 1 := Nat.card_unique
theorem IsPurelyInseparable.sepDegree_eq_one [IsPurelyInseparable F E] :
    sepDegree F E = 1 := by
  rw [sepDegree, separableClosure.eq_bot_of_isPurelyInseparable, IntermediateField.rank_bot]
theorem IsPurelyInseparable.insepDegree_eq [IsPurelyInseparable F E] :
    insepDegree F E = Module.rank F E := by
  rw [insepDegree, separableClosure.eq_bot_of_isPurelyInseparable, rank_bot']
theorem IsPurelyInseparable.finInsepDegree_eq [IsPurelyInseparable F E] :
    finInsepDegree F E = finrank F E := congr(Cardinal.toNat $(insepDegree_eq F E))
theorem isPurelyInseparable_iff_finSepDegree_eq_one :
    IsPurelyInseparable F E ↔ finSepDegree F E = 1 :=
  ⟨fun _ ↦ IsPurelyInseparable.finSepDegree_eq_one F E,
    fun h ↦ isPurelyInseparable_of_finSepDegree_eq_one h⟩
variable {F E} in
theorem isPurelyInseparable_iff_fd_isPurelyInseparable [Algebra.IsAlgebraic F E] :
    IsPurelyInseparable F E ↔
    ∀ L : IntermediateField F E, FiniteDimensional F L → IsPurelyInseparable F L := by
  refine ⟨fun _ _ _ ↦ IsPurelyInseparable.tower_bot F _ E,
    fun h ↦ isPurelyInseparable_iff.2 fun x ↦ ?_⟩
  have hx : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  refine ⟨hx, fun _ ↦ ?_⟩
  obtain ⟨y, h⟩ := (h _ (adjoin.finiteDimensional hx)).inseparable' _ <|
    show Separable (minpoly F (AdjoinSimple.gen F x)) by rwa [minpoly_eq]
  exact ⟨y, congr_arg (algebraMap _ E) h⟩
instance IsPurelyInseparable.normal [IsPurelyInseparable F E] : Normal F E where
  toIsAlgebraic := isAlgebraic F E
  splits' x := by
    obtain ⟨n, h⟩ := IsPurelyInseparable.minpoly_eq_X_sub_C_pow F (ringExpChar F) x
    rw [← splits_id_iff_splits, h]
    exact splits_pow _ (splits_X_sub_C _) _
@[stacks 030K "$E/E_{sep}$ is purely inseparable."]
instance separableClosure.isPurelyInseparable [Algebra.IsAlgebraic F E] :
    IsPurelyInseparable (separableClosure F E) E := isPurelyInseparable_iff.2 fun x ↦ by
  set L := separableClosure F E
  refine ⟨(IsAlgebraic.tower_top L (Algebra.IsAlgebraic.isAlgebraic (R := F) x)).isIntegral,
    fun h ↦ ?_⟩
  haveI := (isSeparable_adjoin_simple_iff_isSeparable L E).2 h
  haveI : Algebra.IsSeparable F (restrictScalars F L⟮x⟯) := Algebra.IsSeparable.trans F L L⟮x⟯
  have hx : x ∈ restrictScalars F L⟮x⟯ := mem_adjoin_simple_self _ x
  exact ⟨⟨x, mem_separableClosure_iff.2 <| isSeparable_of_mem_isSeparable F E hx⟩, rfl⟩
open Cardinal in
theorem Field.Emb.cardinal_separableClosure [Algebra.IsAlgebraic F E] :
    #(Field.Emb F <| separableClosure F E) = #(Field.Emb F E) := by
  rw [← (embProdEmbOfIsAlgebraic F (separableClosure F E) E).cardinal_eq,
    mk_prod, mk_eq_one (Emb _ E), lift_one, mul_one, lift_id]
theorem separableClosure_le (L : IntermediateField F E)
    [h : IsPurelyInseparable L E] : separableClosure F E ≤ L := fun x hx ↦ by
  obtain ⟨y, rfl⟩ := h.inseparable' _ <|
    IsSeparable.tower_top L (mem_separableClosure_iff.1 hx)
  exact y.2
theorem separableClosure_le_iff [Algebra.IsAlgebraic F E] (L : IntermediateField F E) :
    separableClosure F E ≤ L ↔ IsPurelyInseparable L E := by
  refine ⟨fun h ↦ ?_, fun _ ↦ separableClosure_le F E L⟩
  have := separableClosure.isPurelyInseparable F E
  letI := (inclusion h).toAlgebra
  letI : SMul (separableClosure F E) L := Algebra.toSMul
  haveI : IsScalarTower (separableClosure F E) L E := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  exact IsPurelyInseparable.tower_top (separableClosure F E) L E
theorem eq_separableClosure (L : IntermediateField F E)
    [Algebra.IsSeparable F L] [IsPurelyInseparable L E] : L = separableClosure F E :=
  le_antisymm (le_separableClosure F E L) (separableClosure_le F E L)
open separableClosure in
theorem eq_separableClosure_iff [Algebra.IsAlgebraic F E] (L : IntermediateField F E) :
    L = separableClosure F E ↔ Algebra.IsSeparable F L ∧ IsPurelyInseparable L E :=
  ⟨by rintro rfl; exact ⟨isSeparable F E, isPurelyInseparable F E⟩,
   fun ⟨_, _⟩ ↦ eq_separableClosure F E L⟩
theorem IsPurelyInseparable.of_injective_comp_algebraMap (L : Type w) [Field L] [IsAlgClosed L]
    [Nonempty (E →+* L)] (h : Function.Injective fun f : E →+* L ↦ f.comp (algebraMap F E)) :
    IsPurelyInseparable F E := by
  rw [isPurelyInseparable_iff_finSepDegree_eq_one, finSepDegree, Nat.card_eq_one_iff_unique]
  letI := (Classical.arbitrary (E →+* L)).toAlgebra
  let j : AlgebraicClosure E →ₐ[E] L := IsAlgClosed.lift
  exact ⟨⟨fun f g ↦ DFunLike.ext' <| j.injective.comp_left (congr_arg (⇑) <|
    @h (j.toRingHom.comp f) (j.toRingHom.comp g) (by ext; simp))⟩, inferInstance⟩
end IsPurelyInseparable
namespace IntermediateField
instance isPurelyInseparable_bot : IsPurelyInseparable F (⊥ : IntermediateField F E) :=
  (botEquiv F E).symm.isPurelyInseparable
theorem isPurelyInseparable_adjoin_simple_iff_natSepDegree_eq_one {x : E} :
    IsPurelyInseparable F F⟮x⟯ ↔ (minpoly F x).natSepDegree = 1 := by
  rw [← le_perfectClosure_iff, adjoin_simple_le_iff, mem_perfectClosure_iff_natSepDegree_eq_one]
theorem isPurelyInseparable_adjoin_simple_iff_pow_mem (q : ℕ) [hF : ExpChar F q] {x : E} :
    IsPurelyInseparable F F⟮x⟯ ↔ ∃ n : ℕ, x ^ q ^ n ∈ (algebraMap F E).range := by
  rw [← le_perfectClosure_iff, adjoin_simple_le_iff, mem_perfectClosure_iff_pow_mem q]
theorem isPurelyInseparable_adjoin_iff_pow_mem (q : ℕ) [hF : ExpChar F q] {S : Set E} :
    IsPurelyInseparable F (adjoin F S) ↔ ∀ x ∈ S, ∃ n : ℕ, x ^ q ^ n ∈ (algebraMap F E).range := by
  simp_rw [← le_perfectClosure_iff, adjoin_le_iff, ← mem_perfectClosure_iff_pow_mem q,
    Set.subset_def, SetLike.mem_coe]
instance isPurelyInseparable_sup (L1 L2 : IntermediateField F E)
    [h1 : IsPurelyInseparable F L1] [h2 : IsPurelyInseparable F L2] :
    IsPurelyInseparable F (L1 ⊔ L2 : IntermediateField F E) := by
  rw [← le_perfectClosure_iff] at h1 h2 ⊢
  exact sup_le h1 h2
instance isPurelyInseparable_iSup {ι : Sort*} {t : ι → IntermediateField F E}
    [h : ∀ i, IsPurelyInseparable F (t i)] :
    IsPurelyInseparable F (⨆ i, t i : IntermediateField F E) := by
  simp_rw [← le_perfectClosure_iff] at h ⊢
  exact iSup_le h
theorem adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable (S : Set E)
    [Algebra.IsSeparable F (adjoin F S)] (q : ℕ) [ExpChar F q] (n : ℕ) :
    adjoin F S = adjoin F ((· ^ q ^ n) '' S) := by
  set L := adjoin F S
  set M := adjoin F ((· ^ q ^ n) '' S)
  have hi : M ≤ L := by
    rw [adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    exact pow_mem (subset_adjoin F S hy) _
  letI := (inclusion hi).toAlgebra
  haveI : Algebra.IsSeparable M (extendScalars hi) :=
    Algebra.isSeparable_tower_top_of_isSeparable F M L
  haveI : IsPurelyInseparable M (extendScalars hi) := by
    haveI := expChar_of_injective_algebraMap (algebraMap F M).injective q
    rw [extendScalars_adjoin hi, isPurelyInseparable_adjoin_iff_pow_mem M _ q]
    exact fun x hx ↦ ⟨n, ⟨x ^ q ^ n, subset_adjoin F _ ⟨x, hx, rfl⟩⟩, rfl⟩
  simpa only [extendScalars_restrictScalars, restrictScalars_bot_eq_self] using congr_arg
    (restrictScalars F) (extendScalars hi).eq_bot_of_isPurelyInseparable_of_isSeparable
theorem adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable' [Algebra.IsSeparable F E] (S : Set E)
    (q : ℕ) [ExpChar F q] (n : ℕ) : adjoin F S = adjoin F ((· ^ q ^ n) '' S) :=
  haveI := Algebra.isSeparable_tower_bot_of_isSeparable F (adjoin F S) E
  adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable F E S q n
theorem adjoin_eq_adjoin_pow_expChar_of_isSeparable (S : Set E) [Algebra.IsSeparable F (adjoin F S)]
    (q : ℕ) [ExpChar F q] : adjoin F S = adjoin F ((· ^ q) '' S) :=
  pow_one q ▸ adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable F E S q 1
theorem adjoin_eq_adjoin_pow_expChar_of_isSeparable' [Algebra.IsSeparable F E] (S : Set E)
    (q : ℕ) [ExpChar F q] : adjoin F S = adjoin F ((· ^ q) '' S) :=
  pow_one q ▸ adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable' F E S q 1
end IntermediateField
section
variable (q n : ℕ) [hF : ExpChar F q] {ι : Type*} {v : ι → E} {F E}
theorem Field.span_map_pow_expChar_pow_eq_top_of_isSeparable [Algebra.IsSeparable F E]
    (h : Submodule.span F (Set.range v) = ⊤) :
    Submodule.span F (Set.range (v · ^ q ^ n)) = ⊤ := by
  erw [← Algebra.top_toSubmodule, ← top_toSubalgebra, ← adjoin_univ,
    adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable' F E _ q n,
    adjoin_algebraic_toSubalgebra fun x _ ↦ Algebra.IsAlgebraic.isAlgebraic x,
    Set.image_univ, Algebra.adjoin_eq_span, (powMonoidHom _).mrange.closure_eq]
  refine (Submodule.span_mono <| Set.range_comp_subset_range _ _).antisymm (Submodule.span_le.2 ?_)
  rw [Set.range_comp, ← Set.image_univ]
  haveI := expChar_of_injective_algebraMap (algebraMap F E).injective q
  apply h ▸ Submodule.image_span_subset_span (LinearMap.iterateFrobenius F E q n) _
private theorem LinearIndependent.map_pow_expChar_pow_of_fd_isSeparable
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (h : LinearIndependent F v) : LinearIndependent F (v · ^ q ^ n) := by
  have h' := h.coe_range
  let ι' := h'.extend (Set.range v).subset_univ
  let b : Basis ι' F E := Basis.extend h'
  letI : Fintype ι' := FiniteDimensional.fintypeBasisIndex b
  have H := linearIndependent_of_top_le_span_of_card_eq_finrank
    (span_map_pow_expChar_pow_eq_top_of_isSeparable q n b.span_eq).ge
    (finrank_eq_card_basis b).symm
  let f (i : ι) : ι' := ⟨v i, h'.subset_extend _ ⟨i, rfl⟩⟩
  convert H.comp f fun _ _ heq ↦ h.injective (by simpa only [f, Subtype.mk.injEq] using heq)
  simp_rw [Function.comp_apply, b]
  rw [Basis.extend_apply_self]
theorem LinearIndependent.map_pow_expChar_pow_of_isSeparable [Algebra.IsSeparable F E]
    (h : LinearIndependent F v) : LinearIndependent F (v · ^ q ^ n) := by
  classical
  have halg := Algebra.IsSeparable.isAlgebraic F E
  rw [linearIndependent_iff_finset_linearIndependent] at h ⊢
  intro s
  let E' := adjoin F (s.image v : Set E)
  haveI : FiniteDimensional F E' := finiteDimensional_adjoin
    fun x _ ↦ Algebra.IsIntegral.isIntegral x
  haveI : Algebra.IsSeparable F E' := Algebra.isSeparable_tower_bot_of_isSeparable F E' E
  let v' (i : s) : E' := ⟨v i.1, subset_adjoin F _ (Finset.mem_image.2 ⟨i.1, i.2, rfl⟩)⟩
  have h' : LinearIndependent F v' := (h s).of_comp E'.val.toLinearMap
  exact (h'.map_pow_expChar_pow_of_fd_isSeparable q n).map'
    E'.val.toLinearMap (LinearMap.ker_eq_bot_of_injective E'.val.injective)
theorem LinearIndependent.map_pow_expChar_pow_of_isSeparable'
    (hsep : ∀ i : ι, IsSeparable F (v i))
    (h : LinearIndependent F v) : LinearIndependent F (v · ^ q ^ n) := by
  let E' := adjoin F (Set.range v)
  haveI : Algebra.IsSeparable F E' := (isSeparable_adjoin_iff_isSeparable F _).2 <| by
    rintro _ ⟨y, rfl⟩; exact hsep y
  let v' (i : ι) : E' := ⟨v i, subset_adjoin F _ ⟨i, rfl⟩⟩
  have h' : LinearIndependent F v' := h.of_comp E'.val.toLinearMap
  exact (h'.map_pow_expChar_pow_of_isSeparable q n).map'
    E'.val.toLinearMap (LinearMap.ker_eq_bot_of_injective E'.val.injective)
def Basis.mapPowExpCharPowOfIsSeparable [Algebra.IsSeparable F E]
    (b : Basis ι F E) : Basis ι F E :=
  Basis.mk (b.linearIndependent.map_pow_expChar_pow_of_isSeparable q n)
    (span_map_pow_expChar_pow_eq_top_of_isSeparable q n b.span_eq).ge
end
theorem isSepClosed_iff_isPurelyInseparable_algebraicClosure [IsAlgClosure F E] :
    IsSepClosed F ↔ IsPurelyInseparable F E :=
  ⟨fun _ ↦ inferInstance, fun H ↦ by
    haveI := IsAlgClosure.isAlgClosed F (K := E)
    rwa [← separableClosure.eq_bot_iff, IsSepClosed.separableClosure_eq_bot_iff] at H⟩
variable {F E} in
theorem Algebra.IsAlgebraic.isSepClosed [Algebra.IsAlgebraic F E]
    [IsSepClosed F] : IsSepClosed E :=
  have : Algebra.IsAlgebraic F (AlgebraicClosure E) := Algebra.IsAlgebraic.trans (L := E)
  (isSepClosed_iff_isPurelyInseparable_algebraicClosure E _).mpr
    (IsPurelyInseparable.tower_top F E <| AlgebraicClosure E)
theorem perfectField_of_perfectClosure_eq_bot [h : PerfectField E] (eq : perfectClosure F E = ⊥) :
    PerfectField F := by
  let p := ringExpChar F
  haveI := expChar_of_injective_algebraMap (algebraMap F E).injective p
  haveI := PerfectRing.ofSurjective F p fun x ↦ by
    obtain ⟨y, h⟩ := surjective_frobenius E p (algebraMap F E x)
    have : y ∈ perfectClosure F E := ⟨1, x, by rw [← h, pow_one, frobenius_def, ringExpChar.eq F p]⟩
    obtain ⟨z, rfl⟩ := eq ▸ this
    exact ⟨z, (algebraMap F E).injective (by erw [RingHom.map_frobenius, h])⟩
  exact PerfectRing.toPerfectField F p
theorem perfectField_of_isSeparable_of_perfectField_top [Algebra.IsSeparable F E] [PerfectField E] :
    PerfectField F :=
  perfectField_of_perfectClosure_eq_bot F E (perfectClosure.eq_bot_of_isSeparable F E)
theorem perfectField_iff_isSeparable_algebraicClosure [IsAlgClosure F E] :
    PerfectField F ↔ Algebra.IsSeparable F E :=
  ⟨fun _ ↦ IsSepClosure.separable, fun _ ↦ haveI : IsAlgClosed E := IsAlgClosure.isAlgClosed F
    perfectField_of_isSeparable_of_perfectField_top F E⟩
namespace Field
@[stacks 09HJ "`sepDegree` is defined as the right hand side of 09HJ"]
theorem finSepDegree_eq [Algebra.IsAlgebraic F E] :
    finSepDegree F E = Cardinal.toNat (sepDegree F E) := by
  have : Algebra.IsAlgebraic (separableClosure F E) E := Algebra.IsAlgebraic.tower_top (K := F) _
  have h := finSepDegree_mul_finSepDegree_of_isAlgebraic F (separableClosure F E) E |>.symm
  haveI := separableClosure.isSeparable F E
  haveI := separableClosure.isPurelyInseparable F E
  rwa [finSepDegree_eq_finrank_of_isSeparable F (separableClosure F E),
    IsPurelyInseparable.finSepDegree_eq_one (separableClosure F E) E, mul_one] at h
theorem finSepDegree_mul_finInsepDegree : finSepDegree F E * finInsepDegree F E = finrank F E := by
  by_cases halg : Algebra.IsAlgebraic F E
  · have := congr_arg Cardinal.toNat (sepDegree_mul_insepDegree F E)
    rwa [Cardinal.toNat_mul, ← finSepDegree_eq F E] at this
  rw [finInsepDegree, finrank_of_infinite_dimensional (K := F) (V := E) fun _ ↦
      halg (Algebra.IsAlgebraic.of_finite F E),
    finrank_of_infinite_dimensional (K := separableClosure F E) (V := E) fun _ ↦
      halg ((separableClosure.isAlgebraic F E).trans),
    mul_zero]
end Field
namespace separableClosure
variable [Algebra E K] [IsScalarTower F E K] {F E}
lemma adjoin_eq_of_isAlgebraic_of_isSeparable [Algebra.IsAlgebraic F E]
    [Algebra.IsSeparable E K] : adjoin E (separableClosure F K : Set K) = ⊤ :=
  top_unique fun x _ ↦ by
    set S := separableClosure F K
    set L := adjoin E (S : Set K)
    have := Algebra.isSeparable_tower_top_of_isSeparable E L K
    let i : S →+* L := Subsemiring.inclusion fun x hx ↦ subset_adjoin E (S : Set K) hx
    let _ : Algebra S L := i.toAlgebra
    let _ : SMul S L := Algebra.toSMul
    have : IsScalarTower S L K := IsScalarTower.of_algebraMap_eq (congrFun rfl)
    have : Algebra.IsAlgebraic F K := Algebra.IsAlgebraic.trans (L := E)
    have : IsPurelyInseparable S K := separableClosure.isPurelyInseparable F K
    have := IsPurelyInseparable.tower_top S L K
    obtain ⟨y, rfl⟩ := IsPurelyInseparable.surjective_algebraMap_of_isSeparable L K x
    exact y.2
theorem adjoin_eq_of_isAlgebraic [Algebra.IsAlgebraic F E] :
    adjoin E (separableClosure F K) = separableClosure E K := by
  set S := separableClosure E K
  have h := congr_arg lift (adjoin_eq_of_isAlgebraic_of_isSeparable (F := F) S)
  rw [lift_top, lift_adjoin] at h
  haveI : IsScalarTower F S K := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  rw [← h, ← map_eq_of_separableClosure_eq_bot F (separableClosure_eq_bot E K)]
  simp only [coe_map, IsScalarTower.coe_toAlgHom', IntermediateField.algebraMap_apply]
end separableClosure
section TowerLaw
variable [Algebra E K] [IsScalarTower F E K]
variable {F K} in
theorem LinearIndependent.map_of_isPurelyInseparable_of_isSeparable [IsPurelyInseparable F E]
    {ι : Type*} {v : ι → K} (hsep : ∀ i : ι, IsSeparable F (v i))
    (h : LinearIndependent F v) : LinearIndependent E v := by
  obtain ⟨q, _⟩ := ExpChar.exists F
  haveI := expChar_of_injective_algebraMap (algebraMap F K).injective q
  refine linearIndependent_iff.mpr fun l hl ↦ Finsupp.ext fun i ↦ ?_
  choose f hf using fun i ↦ (isPurelyInseparable_iff_pow_mem F q).1 ‹_› (l i)
  let n := l.support.sup f
  have := (expChar_pow_pos F q n).ne'
  replace hf (i : ι) : l i ^ q ^ n ∈ (algebraMap F E).range := by
    by_cases hs : i ∈ l.support
    · convert pow_mem (hf i) (q ^ (n - f i)) using 1
      rw [← pow_mul, ← pow_add, Nat.add_sub_of_le (Finset.le_sup hs)]
    exact ⟨0, by rw [map_zero, Finsupp.not_mem_support_iff.1 hs, zero_pow this]⟩
  choose lF hlF using hf
  let lF₀ := Finsupp.onFinset l.support lF fun i ↦ by
    contrapose!
    refine fun hs ↦ (injective_iff_map_eq_zero _).mp (algebraMap F E).injective _ ?_
    rw [hlF, Finsupp.not_mem_support_iff.1 hs, zero_pow this]
  replace h := linearIndependent_iff.1 (h.map_pow_expChar_pow_of_isSeparable' q n hsep) lF₀ <| by
    replace hl := congr($hl ^ q ^ n)
    rw [linearCombination_apply, Finsupp.sum, sum_pow_char_pow, zero_pow this] at hl
    rw [← hl, linearCombination_apply, onFinset_sum _ (fun _ ↦ by exact zero_smul _ _)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp_rw [Algebra.smul_def, mul_pow, IsScalarTower.algebraMap_apply F E K, hlF, map_pow]
  refine pow_eq_zero ((hlF _).symm.trans ?_)
  convert map_zero (algebraMap F E)
  exact congr($h i)
namespace Field
lemma sepDegree_eq_of_isPurelyInseparable_of_isSeparable
    [IsPurelyInseparable F E] [Algebra.IsSeparable E K] : sepDegree F K = Module.rank E K := by
  let S := separableClosure F K
  have h := S.adjoin_rank_le_of_isAlgebraic_right E
  rw [separableClosure.adjoin_eq_of_isAlgebraic_of_isSeparable K, rank_top'] at h
  obtain ⟨ι, ⟨b⟩⟩ := Basis.exists_basis F S
  exact h.antisymm' (b.mk_eq_rank'' ▸ (b.linearIndependent.map' S.val.toLinearMap
    (LinearMap.ker_eq_bot_of_injective S.val.injective)
    |>.map_of_isPurelyInseparable_of_isSeparable E (fun i ↦
      by simpa only [IsSeparable, minpoly_eq] using Algebra.IsSeparable.isSeparable F (b i))
    |>.cardinal_le_rank))
lemma lift_rank_mul_lift_sepDegree_of_isSeparable [Algebra.IsSeparable F E] :
    Cardinal.lift.{w} (Module.rank F E) * Cardinal.lift.{v} (sepDegree E K) =
    Cardinal.lift.{v} (sepDegree F K) := by
  rw [sepDegree, sepDegree, separableClosure.eq_restrictScalars_of_isSeparable F E K]
  exact lift_rank_mul_lift_rank F E (separableClosure E K)
lemma rank_mul_sepDegree_of_isSeparable (K : Type v) [Field K] [Algebra F K]
    [Algebra E K] [IsScalarTower F E K] [Algebra.IsSeparable F E] :
    Module.rank F E * sepDegree E K = sepDegree F K := by
  simpa only [Cardinal.lift_id] using lift_rank_mul_lift_sepDegree_of_isSeparable F E K
lemma sepDegree_eq_of_isPurelyInseparable [IsPurelyInseparable F E] :
    sepDegree F K = sepDegree E K := by
  convert sepDegree_eq_of_isPurelyInseparable_of_isSeparable F E (separableClosure E K)
  haveI : IsScalarTower F (separableClosure E K) K := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  rw [sepDegree, ← separableClosure.map_eq_of_separableClosure_eq_bot F
    (separableClosure.separableClosure_eq_bot E K)]
  exact (separableClosure F (separableClosure E K)).equivMap
    (IsScalarTower.toAlgHom F (separableClosure E K) K) |>.symm.toLinearEquiv.rank_eq
theorem lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic [Algebra.IsAlgebraic F E] :
    Cardinal.lift.{w} (sepDegree F E) * Cardinal.lift.{v} (sepDegree E K) =
    Cardinal.lift.{v} (sepDegree F K) := by
  have h := lift_rank_mul_lift_sepDegree_of_isSeparable F (separableClosure F E) K
  haveI := separableClosure.isPurelyInseparable F E
  rwa [sepDegree_eq_of_isPurelyInseparable (separableClosure F E) E K] at h
@[stacks 09HK "Part 1"]
theorem sepDegree_mul_sepDegree_of_isAlgebraic (K : Type v) [Field K] [Algebra F K]
    [Algebra E K] [IsScalarTower F E K] [Algebra.IsAlgebraic F E] :
    sepDegree F E * sepDegree E K = sepDegree F K := by
  simpa only [Cardinal.lift_id] using lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic F E K
end Field
variable {F K} in
theorem IntermediateField.sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable
    (S : Set K) [Algebra.IsAlgebraic F (adjoin F S)] [IsPurelyInseparable F E] :
    sepDegree E (adjoin E S) = sepDegree F (adjoin F S) := by
  set M := adjoin F S
  set L := adjoin E S
  let E' := (IsScalarTower.toAlgHom F E K).fieldRange
  let j : E ≃ₐ[F] E' := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F E K)
  have hi : M ≤ L.restrictScalars F := by
    rw [restrictScalars_adjoin_of_algEquiv (E := K) j rfl, restrictScalars_adjoin]
    exact adjoin.mono _ _ _ Set.subset_union_right
  let i : M →+* L := Subsemiring.inclusion hi
  letI : Algebra M L := i.toAlgebra
  letI : SMul M L := Algebra.toSMul
  haveI : IsScalarTower F M L := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  haveI : IsPurelyInseparable M L := by
    change IsPurelyInseparable M (extendScalars hi)
    obtain ⟨q, _⟩ := ExpChar.exists F
    have : extendScalars hi = adjoin M (E' : Set K) := restrictScalars_injective F <| by
      conv_lhs => rw [extendScalars_restrictScalars, restrictScalars_adjoin_of_algEquiv
        (E := K) j rfl, ← adjoin_self F E', adjoin_adjoin_comm]
    rw [this, isPurelyInseparable_adjoin_iff_pow_mem _ _ q]
    rintro x ⟨y, hy⟩
    obtain ⟨n, z, hz⟩ := IsPurelyInseparable.pow_mem F q y
    refine ⟨n, algebraMap F M z, ?_⟩
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply F E K, hz, ← hy, map_pow,
      AlgHom.toRingHom_eq_coe, IsScalarTower.coe_toAlgHom]
  have h := lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic F E L
  rw [IsPurelyInseparable.sepDegree_eq_one F E, Cardinal.lift_one, one_mul] at h
  rw [Cardinal.lift_injective h, ← sepDegree_mul_sepDegree_of_isAlgebraic F M L,
    IsPurelyInseparable.sepDegree_eq_one M L, mul_one]
variable {F K} in
theorem IntermediateField.sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable'
    (S : IntermediateField F K) [Algebra.IsAlgebraic F S] [IsPurelyInseparable F E] :
    sepDegree E (adjoin E (S : Set K)) = sepDegree F S := by
  have : Algebra.IsAlgebraic F (adjoin F (S : Set K)) := by rwa [adjoin_self]
  have := sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable (F := F) E (S : Set K)
  rwa [adjoin_self] at this
variable {F K} in
theorem minpoly.map_eq_of_isSeparable_of_isPurelyInseparable (x : K)
    (hsep : IsSeparable F x) [IsPurelyInseparable F E] :
    (minpoly F x).map (algebraMap F E) = minpoly E x := by
  have hi := IsSeparable.isIntegral hsep
  have hi' : IsIntegral E x := IsIntegral.tower_top hi
  refine eq_of_monic_of_dvd_of_natDegree_le (monic hi') ((monic hi).map (algebraMap F E))
    (dvd_map_of_isScalarTower F E x) (le_of_eq ?_)
  have hsep' := IsSeparable.tower_top E hsep
  haveI := (isSeparable_adjoin_simple_iff_isSeparable _ _).2 hsep
  haveI := (isSeparable_adjoin_simple_iff_isSeparable _ _).2 hsep'
  have := Algebra.IsSeparable.isAlgebraic F F⟮x⟯
  have := Algebra.IsSeparable.isAlgebraic E E⟮x⟯
  rw [Polynomial.natDegree_map, ← adjoin.finrank hi, ← adjoin.finrank hi',
    ← finSepDegree_eq_finrank_of_isSeparable F _, ← finSepDegree_eq_finrank_of_isSeparable E _,
    finSepDegree_eq, finSepDegree_eq,
    sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable (F := F) E]
variable {F} in
theorem Polynomial.Separable.map_irreducible_of_isPurelyInseparable {f : F[X]} (hsep : f.Separable)
    (hirr : Irreducible f) [IsPurelyInseparable F E] : Irreducible (f.map (algebraMap F E)) := by
  let K := AlgebraicClosure E
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero K f
    (natDegree_pos_iff_degree_pos.1 hirr.natDegree_pos).ne'
  have ha : Associated f (minpoly F x) := by
    have := isUnit_C.2 (leadingCoeff_ne_zero.2 hirr.ne_zero).isUnit.inv
    exact ⟨this.unit, by rw [IsUnit.unit_spec, minpoly.eq_of_irreducible hirr hx]⟩
  have ha' : Associated (f.map (algebraMap F E)) ((minpoly F x).map (algebraMap F E)) :=
    ha.map (mapRingHom (algebraMap F E)).toMonoidHom
  have heq := minpoly.map_eq_of_isSeparable_of_isPurelyInseparable E x (ha.separable hsep)
  rw [ha'.irreducible_iff, heq]
  exact minpoly.irreducible (Algebra.IsIntegral.isIntegral x)
end TowerLaw