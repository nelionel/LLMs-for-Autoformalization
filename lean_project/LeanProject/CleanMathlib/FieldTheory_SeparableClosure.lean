import Mathlib.FieldTheory.SeparableDegree
import Mathlib.FieldTheory.IsSepClosed
open Module Polynomial IntermediateField Field
noncomputable section
universe u v w
variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
variable (K : Type w) [Field K] [Algebra F K]
section separableClosure
@[stacks 09HC]
def separableClosure : IntermediateField F E where
  carrier := {x | IsSeparable F x}
  mul_mem' := isSeparable_mul
  add_mem' := isSeparable_add
  algebraMap_mem' := isSeparable_algebraMap E
  inv_mem' _ := isSeparable_inv
variable {F E K}
theorem mem_separableClosure_iff {x : E} :
    x ∈ separableClosure F E ↔ IsSeparable F x := Iff.rfl
theorem map_mem_separableClosure_iff (i : E →ₐ[F] K) {x : E} :
    i x ∈ separableClosure F K ↔ x ∈ separableClosure F E := by
  simp_rw [mem_separableClosure_iff, IsSeparable, minpoly.algHom_eq i i.injective]
theorem separableClosure.comap_eq_of_algHom (i : E →ₐ[F] K) :
    (separableClosure F K).comap i = separableClosure F E := by
  ext x
  exact map_mem_separableClosure_iff i
theorem separableClosure.map_le_of_algHom (i : E →ₐ[F] K) :
    (separableClosure F E).map i ≤ separableClosure F K :=
  map_le_iff_le_comap.2 (comap_eq_of_algHom i).ge
variable (F) in
theorem separableClosure.map_eq_of_separableClosure_eq_bot [Algebra E K] [IsScalarTower F E K]
    (h : separableClosure E K = ⊥) :
    (separableClosure F E).map (IsScalarTower.toAlgHom F E K) = separableClosure F K := by
  refine le_antisymm (map_le_of_algHom _) (fun x hx ↦ ?_)
  obtain ⟨y, rfl⟩ := mem_bot.1 <| h ▸ mem_separableClosure_iff.2
    (IsSeparable.tower_top E <| mem_separableClosure_iff.1 hx)
  exact ⟨y, (map_mem_separableClosure_iff <| IsScalarTower.toAlgHom F E K).mp hx, rfl⟩
theorem separableClosure.map_eq_of_algEquiv (i : E ≃ₐ[F] K) :
    (separableClosure F E).map i = separableClosure F K :=
  (map_le_of_algHom i.toAlgHom).antisymm
    (fun x h ↦ ⟨_, (map_mem_separableClosure_iff i.symm).2 h, by simp⟩)
def separableClosure.algEquivOfAlgEquiv (i : E ≃ₐ[F] K) :
    separableClosure F E ≃ₐ[F] separableClosure F K :=
  (intermediateFieldMap i _).trans (equivOfEq (map_eq_of_algEquiv i))
alias AlgEquiv.separableClosure := separableClosure.algEquivOfAlgEquiv
variable (F E K)
instance separableClosure.isAlgebraic : Algebra.IsAlgebraic F (separableClosure F E) :=
  ⟨fun x ↦ isAlgebraic_iff.2 (IsSeparable.isIntegral x.2).isAlgebraic⟩
@[stacks 030K "$E_{sep}/F$ is separable"]
instance separableClosure.isSeparable : Algebra.IsSeparable F (separableClosure F E) :=
  ⟨fun x ↦ by simpa only [IsSeparable, minpoly_eq] using x.2⟩
theorem le_separableClosure' {L : IntermediateField F E} (hs : ∀ x : L, IsSeparable F x) :
    L ≤ separableClosure F E := fun x h ↦ by simpa only [IsSeparable, minpoly_eq] using hs ⟨x, h⟩
theorem le_separableClosure (L : IntermediateField F E) [Algebra.IsSeparable F L] :
    L ≤ separableClosure F E := le_separableClosure' F E (Algebra.IsSeparable.isSeparable F)
theorem le_separableClosure_iff (L : IntermediateField F E) :
    L ≤ separableClosure F E ↔ Algebra.IsSeparable F L :=
  ⟨fun h ↦ ⟨fun x ↦ by simpa only [IsSeparable, minpoly_eq] using h x.2⟩,
    fun _ ↦ le_separableClosure _ _ _⟩
theorem separableClosure.separableClosure_eq_bot :
    separableClosure (separableClosure F E) E = ⊥ :=
  bot_unique fun x hx ↦ mem_bot.2
    ⟨⟨x, IsSeparable.of_algebra_isSeparable_of_isSeparable F (mem_separableClosure_iff.1 hx)⟩, rfl⟩
theorem separableClosure.normalClosure_eq_self :
    normalClosure F (separableClosure F E) E = separableClosure F E :=
  le_antisymm (normalClosure_le_iff.2 fun i ↦
    have : Algebra.IsSeparable F i.fieldRange :=
      (AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField i))
    le_separableClosure F E _) (le_normalClosure _)
@[stacks 0EXK]
instance separableClosure.isGalois [Normal F E] : IsGalois F (separableClosure F E) where
  to_isSeparable := separableClosure.isSeparable F E
  to_normal := by
    rw [← separableClosure.normalClosure_eq_self]
    exact normalClosure.normal F _ E
theorem IsSepClosed.separableClosure_eq_bot_iff [IsSepClosed E] :
    separableClosure F E = ⊥ ↔ IsSepClosed F := by
  refine ⟨fun h ↦ IsSepClosed.of_exists_root _ fun p _ hirr hsep ↦ ?_,
    fun _ ↦ IntermediateField.eq_bot_of_isSepClosed_of_isSeparable _⟩
  obtain ⟨x, hx⟩ := IsSepClosed.exists_aeval_eq_zero E p (degree_pos_of_irreducible hirr).ne' hsep
  obtain ⟨x, rfl⟩ := h ▸ mem_separableClosure_iff.2 (hsep.of_dvd <| minpoly.dvd _ x hx)
  exact ⟨x, by simpa [Algebra.ofId_apply] using hx⟩
instance separableClosure.isSepClosure [IsSepClosed E] : IsSepClosure F (separableClosure F E) :=
  ⟨(IsSepClosed.separableClosure_eq_bot_iff _ E).mp (separableClosure.separableClosure_eq_bot F E),
    isSeparable F E⟩
abbrev SeparableClosure : Type _ := separableClosure F (AlgebraicClosure F)
theorem IntermediateField.isSeparable_adjoin_iff_isSeparable {S : Set E} :
    Algebra.IsSeparable F (adjoin F S) ↔ ∀ x ∈ S, IsSeparable F x :=
  (le_separableClosure_iff F E _).symm.trans adjoin_le_iff
theorem separableClosure.eq_top_iff : separableClosure F E = ⊤ ↔ Algebra.IsSeparable F E :=
  ⟨fun h ↦ ⟨fun _ ↦ mem_separableClosure_iff.1 (h ▸ mem_top)⟩,
    fun _ ↦ top_unique fun x _ ↦ mem_separableClosure_iff.2 (Algebra.IsSeparable.isSeparable _ x)⟩
theorem separableClosure.le_restrictScalars [Algebra E K] [IsScalarTower F E K] :
    separableClosure F K ≤ (separableClosure E K).restrictScalars F :=
  fun _ ↦ IsSeparable.tower_top E
theorem separableClosure.eq_restrictScalars_of_isSeparable [Algebra E K] [IsScalarTower F E K]
    [Algebra.IsSeparable F E] : separableClosure F K = (separableClosure E K).restrictScalars F :=
  (separableClosure.le_restrictScalars F E K).antisymm fun _ h ↦
    IsSeparable.of_algebra_isSeparable_of_isSeparable F h
theorem separableClosure.adjoin_le [Algebra E K] [IsScalarTower F E K] :
    adjoin E (separableClosure F K) ≤ separableClosure E K :=
  adjoin_le_iff.2 <| le_restrictScalars F E K
instance IntermediateField.isSeparable_sup (L1 L2 : IntermediateField F E)
    [h1 : Algebra.IsSeparable F L1] [h2 : Algebra.IsSeparable F L2] :
    Algebra.IsSeparable F (L1 ⊔ L2 : IntermediateField F E) := by
  rw [← le_separableClosure_iff] at h1 h2 ⊢
  exact sup_le h1 h2
instance IntermediateField.isSeparable_iSup {ι : Type*} {t : ι → IntermediateField F E}
    [h : ∀ i, Algebra.IsSeparable F (t i)] :
    Algebra.IsSeparable F (⨆ i, t i : IntermediateField F E) := by
  simp_rw [← le_separableClosure_iff] at h ⊢
  exact iSup_le h
end separableClosure
namespace Field
@[stacks 030L "Part 1"]
def sepDegree := Module.rank F (separableClosure F E)
@[stacks 030L "Part 2"]
def insepDegree := Module.rank (separableClosure F E) E
def finInsepDegree : ℕ := finrank (separableClosure F E) E
theorem finInsepDegree_def' : finInsepDegree F E = Cardinal.toNat (insepDegree F E) := rfl
instance instNeZeroSepDegree : NeZero (sepDegree F E) := ⟨rank_pos.ne'⟩
instance instNeZeroInsepDegree : NeZero (insepDegree F E) := ⟨rank_pos.ne'⟩
instance instNeZeroFinInsepDegree [FiniteDimensional F E] :
    NeZero (finInsepDegree F E) := ⟨finrank_pos.ne'⟩
theorem lift_sepDegree_eq_of_equiv (i : E ≃ₐ[F] K) :
    Cardinal.lift.{w} (sepDegree F E) = Cardinal.lift.{v} (sepDegree F K) :=
  i.separableClosure.toLinearEquiv.lift_rank_eq
theorem sepDegree_eq_of_equiv (K : Type v) [Field K] [Algebra F K] (i : E ≃ₐ[F] K) :
    sepDegree F E = sepDegree F K :=
  i.separableClosure.toLinearEquiv.rank_eq
theorem sepDegree_mul_insepDegree : sepDegree F E * insepDegree F E = Module.rank F E :=
  rank_mul_rank F (separableClosure F E) E
theorem lift_insepDegree_eq_of_equiv (i : E ≃ₐ[F] K) :
    Cardinal.lift.{w} (insepDegree F E) = Cardinal.lift.{v} (insepDegree F K) :=
  Algebra.lift_rank_eq_of_equiv_equiv i.separableClosure i rfl
theorem insepDegree_eq_of_equiv (K : Type v) [Field K] [Algebra F K] (i : E ≃ₐ[F] K) :
    insepDegree F E = insepDegree F K :=
  Algebra.rank_eq_of_equiv_equiv i.separableClosure i rfl
theorem finInsepDegree_eq_of_equiv (i : E ≃ₐ[F] K) :
    finInsepDegree F E = finInsepDegree F K := by
  simpa only [Cardinal.toNat_lift] using congr_arg Cardinal.toNat
    (lift_insepDegree_eq_of_equiv F E K i)
@[simp]
theorem sepDegree_self : sepDegree F F = 1 := by
  rw [sepDegree, Subsingleton.elim (separableClosure F F) ⊥, IntermediateField.rank_bot]
@[simp]
theorem insepDegree_self : insepDegree F F = 1 := by
  rw [insepDegree, Subsingleton.elim (separableClosure F F) ⊤, IntermediateField.rank_top]
@[simp]
theorem finInsepDegree_self : finInsepDegree F F = 1 := by
  rw [finInsepDegree_def', insepDegree_self, Cardinal.one_toNat]
end Field
namespace IntermediateField
@[simp]
theorem sepDegree_bot : sepDegree F (⊥ : IntermediateField F E) = 1 := by
  have := lift_sepDegree_eq_of_equiv _ _ _ (botEquiv F E)
  rwa [sepDegree_self, Cardinal.lift_one, ← Cardinal.lift_one.{v, u}, Cardinal.lift_inj] at this
@[simp]
theorem insepDegree_bot : insepDegree F (⊥ : IntermediateField F E) = 1 := by
  have := lift_insepDegree_eq_of_equiv _ _ _ (botEquiv F E)
  rwa [insepDegree_self, Cardinal.lift_one, ← Cardinal.lift_one.{v, u}, Cardinal.lift_inj] at this
@[simp]
theorem finInsepDegree_bot : finInsepDegree F (⊥ : IntermediateField F E) = 1 := by
  rw [finInsepDegree_eq_of_equiv _ _ _ (botEquiv F E), finInsepDegree_self]
section Tower
variable [Algebra E K] [IsScalarTower F E K]
theorem lift_sepDegree_bot' : Cardinal.lift.{v} (sepDegree F (⊥ : IntermediateField E K)) =
    Cardinal.lift.{w} (sepDegree F E) :=
  lift_sepDegree_eq_of_equiv _ _ _ ((botEquiv E K).restrictScalars F)
theorem lift_insepDegree_bot' : Cardinal.lift.{v} (insepDegree F (⊥ : IntermediateField E K)) =
    Cardinal.lift.{w} (insepDegree F E) :=
  lift_insepDegree_eq_of_equiv _ _ _ ((botEquiv E K).restrictScalars F)
variable {F}
@[simp]
theorem finInsepDegree_bot' :
    finInsepDegree F (⊥ : IntermediateField E K) = finInsepDegree F E := by
  simpa only [Cardinal.toNat_lift] using congr_arg Cardinal.toNat (lift_insepDegree_bot' F E K)
@[simp]
theorem sepDegree_top : sepDegree F (⊤ : IntermediateField E K) = sepDegree F K :=
  sepDegree_eq_of_equiv _ _ _ ((topEquiv (F := E) (E := K)).restrictScalars F)
@[simp]
theorem insepDegree_top : insepDegree F (⊤ : IntermediateField E K) = insepDegree F K :=
  insepDegree_eq_of_equiv _ _ _ ((topEquiv (F := E) (E := K)).restrictScalars F)
@[simp]
theorem finInsepDegree_top : finInsepDegree F (⊤ : IntermediateField E K) = finInsepDegree F K := by
  rw [finInsepDegree_def', insepDegree_top, ← finInsepDegree_def']
variable (K : Type v) [Field K] [Algebra F K] [Algebra E K] [IsScalarTower F E K]
@[simp]
theorem sepDegree_bot' : sepDegree F (⊥ : IntermediateField E K) = sepDegree F E :=
  sepDegree_eq_of_equiv _ _ _ ((botEquiv E K).restrictScalars F)
@[simp]
theorem insepDegree_bot' : insepDegree F (⊥ : IntermediateField E K) = insepDegree F E :=
  insepDegree_eq_of_equiv _ _ _ ((botEquiv E K).restrictScalars F)
end Tower
end IntermediateField
theorem Algebra.IsSeparable.sepDegree_eq [Algebra.IsSeparable F E] :
    sepDegree F E = Module.rank F E := by
  rw [sepDegree, (separableClosure.eq_top_iff F E).2 ‹_›, IntermediateField.rank_top']
theorem Algebra.IsSeparable.insepDegree_eq [Algebra.IsSeparable F E] : insepDegree F E = 1 := by
  rw [insepDegree, (separableClosure.eq_top_iff F E).2 ‹_›, IntermediateField.rank_top]
theorem Algebra.IsSeparable.finInsepDegree_eq [Algebra.IsSeparable F E] : finInsepDegree F E = 1 :=
  Cardinal.one_toNat ▸ congr(Cardinal.toNat $(insepDegree_eq F E))