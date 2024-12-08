import Mathlib.Algebra.Module.Presentation.DirectSum
import Mathlib.Algebra.Module.Presentation.Cokernel
namespace Module
variable {B : Type*} [Ring B] {M : Type*} [AddCommGroup M] [Module B M]
  [DecidableEq B]
  (presM : Presentation B M) [DecidableEq presM.G]
  {A : Type*} [CommRing A] [Algebra A B] [Module A M] [IsScalarTower A B M]
  (presB : Presentation A B)
namespace Presentation
abbrev RestrictScalarsData : Type _ :=
  (presB.finsupp presM.G).CokernelData
    (LinearMap.restrictScalars A presM.map)
    (fun (⟨g, g'⟩ : presB.G × presM.R) ↦ presB.var g • Finsupp.single g' (1 : B))
variable (data : presM.RestrictScalarsData presB)
noncomputable def restrictScalars : Presentation A M :=
  ofExact (g := LinearMap.restrictScalars A presM.π) (presB.finsupp presM.G) data
    presM.exact presM.surjective_π (by
      ext v
      dsimp
      simp only [Submodule.mem_top, iff_true]
      apply Finsupp.induction
      · simp
      · intro r b w _ _ hw
        refine Submodule.add_mem _ ?_ hw
        obtain ⟨β, rfl⟩ := presB.surjective_π b
        apply Finsupp.induction (p := fun β ↦ Finsupp.single r (presB.π β) ∈ _)
        · simp
        · intro g a f _ _ hf
          rw [map_add, Finsupp.single_add]
          refine Submodule.add_mem _ ?_ hf
          rw [← Finsupp.smul_single_one, ← Finsupp.smul_single_one,
            map_smul, Relations.Solution.π_single, smul_assoc]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨g, r⟩, rfl⟩))
end Presentation
end Module