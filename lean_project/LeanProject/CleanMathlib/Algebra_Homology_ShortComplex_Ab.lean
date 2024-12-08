import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.Kernels
import Mathlib.Algebra.Exact
universe u
namespace CategoryTheory
namespace ShortComplex
variable (S : ShortComplex Ab.{u})
@[simp]
lemma ab_zero_apply (x : S.X₁) : S.g (S.f x) = 0 := by
  rw [← comp_apply, S.zero]
  rfl
@[simps!]
def abToCycles : S.X₁ →+ AddMonoidHom.ker S.g :=
    AddMonoidHom.mk' (fun x => ⟨S.f x, S.ab_zero_apply x⟩) (by aesop)
@[simps]
def abLeftHomologyData : S.LeftHomologyData where
  K := AddCommGrp.of (AddMonoidHom.ker S.g)
  H := AddCommGrp.of ((AddMonoidHom.ker S.g) ⧸ AddMonoidHom.range S.abToCycles)
  i := (AddMonoidHom.ker S.g).subtype
  π := QuotientAddGroup.mk' _
  wi := by
    ext ⟨_, hx⟩
    exact hx
  hi := AddCommGrp.kernelIsLimit _
  wπ := by
    ext (x : S.X₁)
    erw [QuotientAddGroup.eq_zero_iff]
    rw [AddMonoidHom.mem_range]
    apply exists_apply_eq_apply
  hπ := AddCommGrp.cokernelIsColimit (AddCommGrp.ofHom S.abToCycles)
@[simp]
lemma abLeftHomologyData_f' : S.abLeftHomologyData.f' = S.abToCycles := rfl
noncomputable def abCyclesIso : S.cycles ≅ AddCommGrp.of (AddMonoidHom.ker S.g) :=
  S.abLeftHomologyData.cyclesIso
lemma abCyclesIso_inv_apply_iCycles (x : AddMonoidHom.ker S.g) :
    S.iCycles (S.abCyclesIso.inv x) = x := by
  dsimp only [abCyclesIso]
  rw [← comp_apply, S.abLeftHomologyData.cyclesIso_inv_comp_iCycles]
  rfl
noncomputable def abHomologyIso : S.homology ≅
    AddCommGrp.of ((AddMonoidHom.ker S.g) ⧸ AddMonoidHom.range S.abToCycles) :=
  S.abLeftHomologyData.homologyIso
lemma exact_iff_surjective_abToCycles :
    S.Exact ↔ Function.Surjective S.abToCycles := by
  rw [S.abLeftHomologyData.exact_iff_epi_f', abLeftHomologyData_f',
    AddCommGrp.epi_iff_surjective]
  rfl
lemma ab_exact_iff :
    S.Exact ↔ ∀ (x₂ : S.X₂) (_ : S.g x₂ = 0), ∃ (x₁ : S.X₁), S.f x₁ = x₂ := by
  rw [exact_iff_surjective_abToCycles]
  constructor
  · intro h x₂ hx₂
    obtain ⟨x₁, hx₁⟩ := h ⟨x₂, hx₂⟩
    exact ⟨x₁, by simpa only [Subtype.ext_iff, abToCycles_apply_coe] using hx₁⟩
  · rintro h ⟨x₂, hx₂⟩
    obtain ⟨x₁, rfl⟩ := h x₂ hx₂
    exact ⟨x₁, rfl⟩
lemma ab_exact_iff_function_exact :
    S.Exact ↔ Function.Exact S.f S.g := by
  rw [S.ab_exact_iff]
  apply forall_congr'
  intro x₂
  constructor
  · intro h
    refine ⟨h, ?_⟩
    rintro ⟨x₁, rfl⟩
    simp only [ab_zero_apply]
  · tauto
lemma ab_exact_iff_ker_le_range : S.Exact ↔ S.g.ker ≤ S.f.range := S.ab_exact_iff
lemma ab_exact_iff_range_eq_ker : S.Exact ↔ S.f.range = S.g.ker := by
  rw [ab_exact_iff_ker_le_range]
  constructor
  · intro h
    refine le_antisymm ?_ h
    rintro _ ⟨x₁, rfl⟩
    rw [AddMonoidHom.mem_ker, ← comp_apply, S.zero]
    rfl
  · intro h
    rw [h]
variable {S}
lemma ShortExact.ab_injective_f (hS : S.ShortExact) :
    Function.Injective S.f :=
  (AddCommGrp.mono_iff_injective _).1 hS.mono_f
lemma ShortExact.ab_surjective_g (hS : S.ShortExact) :
    Function.Surjective S.g :=
  (AddCommGrp.epi_iff_surjective _).1 hS.epi_g
variable (S)
lemma ShortExact.ab_exact_iff_function_exact :
    S.Exact ↔ Function.Exact S.f S.g := by
  rw [ab_exact_iff_range_eq_ker, AddMonoidHom.exact_iff]
  tauto
end ShortComplex
end CategoryTheory