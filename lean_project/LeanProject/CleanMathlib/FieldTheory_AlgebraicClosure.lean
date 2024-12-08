import Mathlib.FieldTheory.NormalClosure
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic
noncomputable section
open Polynomial FiniteDimensional IntermediateField Field
variable (F E : Type*) [Field F] [Field E] [Algebra F E]
variable {K : Type*} [Field K] [Algebra F K]
@[stacks 09GI]
def algebraicClosure : IntermediateField F E :=
  Algebra.IsAlgebraic.toIntermediateField (integralClosure F E)
variable {F E}
theorem mem_algebraicClosure_iff' {x : E} :
    x ∈ algebraicClosure F E ↔ IsIntegral F x := Iff.rfl
theorem mem_algebraicClosure_iff {x : E} :
    x ∈ algebraicClosure F E ↔ IsAlgebraic F x := isAlgebraic_iff_isIntegral.symm
theorem map_mem_algebraicClosure_iff (i : E →ₐ[F] K) {x : E} :
    i x ∈ algebraicClosure F K ↔ x ∈ algebraicClosure F E := by
  simp_rw [mem_algebraicClosure_iff', ← minpoly.ne_zero_iff, minpoly.algHom_eq i i.injective]
namespace algebraicClosure
theorem comap_eq_of_algHom (i : E →ₐ[F] K) :
    (algebraicClosure F K).comap i = algebraicClosure F E := by
  ext x
  exact map_mem_algebraicClosure_iff i
theorem map_le_of_algHom (i : E →ₐ[F] K) :
    (algebraicClosure F E).map i ≤ algebraicClosure F K :=
  map_le_iff_le_comap.2 (comap_eq_of_algHom i).ge
variable (F) in
theorem map_eq_of_algebraicClosure_eq_bot [Algebra E K] [IsScalarTower F E K]
    (h : algebraicClosure E K = ⊥) :
    (algebraicClosure F E).map (IsScalarTower.toAlgHom F E K) = algebraicClosure F K := by
  refine le_antisymm (map_le_of_algHom _) (fun x hx ↦ ?_)
  obtain ⟨y, rfl⟩ := mem_bot.1 <| h ▸ mem_algebraicClosure_iff'.2
    (IsIntegral.tower_top <| mem_algebraicClosure_iff'.1 hx)
  exact ⟨y, (map_mem_algebraicClosure_iff <| IsScalarTower.toAlgHom F E K).mp hx, rfl⟩
theorem map_eq_of_algEquiv (i : E ≃ₐ[F] K) :
    (algebraicClosure F E).map i = algebraicClosure F K :=
  (map_le_of_algHom i.toAlgHom).antisymm
    (fun x h ↦ ⟨_, (map_mem_algebraicClosure_iff i.symm).2 h, by simp⟩)
def algEquivOfAlgEquiv (i : E ≃ₐ[F] K) :
    algebraicClosure F E ≃ₐ[F] algebraicClosure F K :=
  (intermediateFieldMap i _).trans (equivOfEq (map_eq_of_algEquiv i))
alias _root_.AlgEquiv.algebraicClosure := algEquivOfAlgEquiv
variable (F E K)
instance isAlgebraic : Algebra.IsAlgebraic F (algebraicClosure F E) :=
  ⟨fun x ↦
    isAlgebraic_iff.mpr (IsAlgebraic.isIntegral (mem_algebraicClosure_iff.mp x.2)).isAlgebraic⟩
instance isIntegralClosure : IsIntegralClosure (algebraicClosure F E) F E :=
  inferInstanceAs (IsIntegralClosure (integralClosure F E) F E)
end algebraicClosure
variable (F E K)
theorem le_algebraicClosure' {L : IntermediateField F E} (hs : ∀ x : L, IsAlgebraic F x) :
    L ≤ algebraicClosure F E := fun x h ↦ by
  simpa only [mem_algebraicClosure_iff, IsAlgebraic, ne_eq, ← aeval_algebraMap_eq_zero_iff E,
    Algebra.id.map_eq_id, RingHom.id_apply, IntermediateField.algebraMap_apply] using hs ⟨x, h⟩
theorem le_algebraicClosure (L : IntermediateField F E) [Algebra.IsAlgebraic F L] :
    L ≤ algebraicClosure F E := le_algebraicClosure' F E (Algebra.IsAlgebraic.isAlgebraic)
theorem le_algebraicClosure_iff (L : IntermediateField F E) :
    L ≤ algebraicClosure F E ↔ Algebra.IsAlgebraic F L :=
  ⟨fun h ↦ ⟨fun x ↦ by simpa only [IsAlgebraic, ne_eq, ← aeval_algebraMap_eq_zero_iff E,
    IntermediateField.algebraMap_apply,
    Algebra.id.map_eq_id, RingHomCompTriple.comp_apply, mem_algebraicClosure_iff] using h x.2⟩,
    fun _ ↦ le_algebraicClosure _ _ _⟩
namespace algebraicClosure
theorem algebraicClosure_eq_bot :
    algebraicClosure (algebraicClosure F E) E = ⊥ :=
  bot_unique fun x hx ↦ mem_bot.2
    ⟨⟨x, isIntegral_trans x (mem_algebraicClosure_iff'.1 hx)⟩, rfl⟩
theorem normalClosure_eq_self :
    normalClosure F (algebraicClosure F E) E = algebraicClosure F E :=
  le_antisymm (normalClosure_le_iff.2 fun i ↦
    haveI : Algebra.IsAlgebraic F i.fieldRange := (AlgEquiv.ofInjectiveField i).isAlgebraic
    le_algebraicClosure F E _) (le_normalClosure _)
end algebraicClosure
theorem IsAlgClosed.algebraicClosure_eq_bot_iff [IsAlgClosed E] :
    algebraicClosure F E = ⊥ ↔ IsAlgClosed F := by
  refine ⟨fun h ↦ IsAlgClosed.of_exists_root _ fun p hmon hirr ↦ ?_,
    fun _ ↦ IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic _⟩
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero E p (degree_pos_of_irreducible hirr).ne'
  obtain ⟨x, rfl⟩ := h ▸ mem_algebraicClosure_iff'.2 (minpoly.ne_zero_iff.1 <|
    ne_zero_of_dvd_ne_zero hmon.ne_zero (minpoly.dvd _ x hx))
  exact ⟨x, by simpa [Algebra.ofId_apply] using hx⟩
theorem IntermediateField.isAlgebraic_adjoin_iff_isAlgebraic {S : Set E} :
    Algebra.IsAlgebraic F (adjoin F S) ↔ ∀ x ∈ S, IsAlgebraic F x :=
  ((le_algebraicClosure_iff F E _).symm.trans (adjoin_le_iff.trans <| forall_congr' <|
    fun _ => Iff.imp Iff.rfl mem_algebraicClosure_iff))
namespace algebraicClosure
instance isAlgClosure [IsAlgClosed E] : IsAlgClosure F (algebraicClosure F E) :=
  ⟨(IsAlgClosed.algebraicClosure_eq_bot_iff _ E).mp (algebraicClosure_eq_bot F E),
    isAlgebraic F E⟩
theorem eq_top_iff : algebraicClosure F E = ⊤ ↔ Algebra.IsAlgebraic F E :=
  ⟨fun h ↦ ⟨fun _ ↦ mem_algebraicClosure_iff.1 (h ▸ mem_top)⟩,
    fun _ ↦ top_unique fun x _ ↦ mem_algebraicClosure_iff.2 (Algebra.IsAlgebraic.isAlgebraic x)⟩
theorem le_restrictScalars [Algebra E K] [IsScalarTower F E K] :
    algebraicClosure F K ≤ (algebraicClosure E K).restrictScalars F :=
  fun _ h ↦ mem_algebraicClosure_iff.2 <| IsAlgebraic.tower_top E (mem_algebraicClosure_iff.1 h)
theorem eq_restrictScalars_of_isAlgebraic [Algebra E K] [IsScalarTower F E K]
    [Algebra.IsAlgebraic F E] : algebraicClosure F K = (algebraicClosure E K).restrictScalars F :=
  (algebraicClosure.le_restrictScalars F E K).antisymm fun _ h ↦
    isIntegral_trans _ h
theorem adjoin_le [Algebra E K] [IsScalarTower F E K] :
    adjoin E (algebraicClosure F K) ≤ algebraicClosure E K :=
  adjoin_le_iff.2 <| le_restrictScalars F E K
end algebraicClosure
variable {F}
theorem Splits.algebraicClosure {p : F[X]} (h : p.Splits (algebraMap F E)) :
    p.Splits (algebraMap F (algebraicClosure F E)) :=
  splits_of_splits h fun _ hx ↦ (isAlgebraic_of_mem_rootSet hx).isIntegral