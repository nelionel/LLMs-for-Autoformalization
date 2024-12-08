import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Algebra.Algebra.Pi
namespace Filter
variable {𝕜 α β : Type*}
open Topology
def ZeroAtFilter [Zero β] [TopologicalSpace β] (l : Filter α) (f : α → β) : Prop :=
  Filter.Tendsto f l (𝓝 0)
theorem zero_zeroAtFilter [Zero β] [TopologicalSpace β] (l : Filter α) :
    ZeroAtFilter l (0 : α → β) :=
  tendsto_const_nhds
nonrec theorem ZeroAtFilter.add [TopologicalSpace β] [AddZeroClass β] [ContinuousAdd β]
    {l : Filter α} {f g : α → β} (hf : ZeroAtFilter l f) (hg : ZeroAtFilter l g) :
    ZeroAtFilter l (f + g) := by
  simpa using hf.add hg
nonrec theorem ZeroAtFilter.neg [TopologicalSpace β] [AddGroup β] [ContinuousNeg β] {l : Filter α}
    {f : α → β} (hf : ZeroAtFilter l f) : ZeroAtFilter l (-f) := by simpa using hf.neg
theorem ZeroAtFilter.smul [TopologicalSpace β] [Zero 𝕜] [Zero β]
    [SMulWithZero 𝕜 β] [ContinuousConstSMul 𝕜 β] {l : Filter α} {f : α → β} (c : 𝕜)
    (hf : ZeroAtFilter l f) : ZeroAtFilter l (c • f) := by simpa using hf.const_smul c
variable (𝕜) in
def zeroAtFilterSubmodule
    [TopologicalSpace β] [Semiring 𝕜] [AddCommMonoid β] [Module 𝕜 β]
    [ContinuousAdd β] [ContinuousConstSMul 𝕜 β]
    (l : Filter α) : Submodule 𝕜 (α → β) where
  carrier := ZeroAtFilter l
  zero_mem' := zero_zeroAtFilter l
  add_mem' ha hb := ha.add hb
  smul_mem' c _ hf := hf.smul c
def zeroAtFilterAddSubmonoid [TopologicalSpace β] [AddZeroClass β] [ContinuousAdd β]
    (l : Filter α) : AddSubmonoid (α → β) where
  carrier := ZeroAtFilter l
  add_mem' ha hb := ha.add hb
  zero_mem' := zero_zeroAtFilter l
def BoundedAtFilter [Norm β] (l : Filter α) (f : α → β) : Prop :=
  Asymptotics.IsBigO l f (1 : α → ℝ)
theorem ZeroAtFilter.boundedAtFilter [SeminormedAddGroup β] {l : Filter α} {f : α → β}
    (hf : ZeroAtFilter l f) : BoundedAtFilter l f :=
  ((Asymptotics.isLittleO_one_iff _).mpr hf).isBigO
theorem const_boundedAtFilter [Norm β] (l : Filter α) (c : β) :
    BoundedAtFilter l (Function.const α c : α → β) :=
  Asymptotics.isBigO_const_const c one_ne_zero l
nonrec theorem BoundedAtFilter.add [SeminormedAddCommGroup β] {l : Filter α} {f g : α → β}
    (hf : BoundedAtFilter l f) (hg : BoundedAtFilter l g) : BoundedAtFilter l (f + g) := by
  simpa using hf.add hg
theorem BoundedAtFilter.neg [SeminormedAddCommGroup β] {l : Filter α} {f : α → β}
    (hf : BoundedAtFilter l f) : BoundedAtFilter l (-f) :=
  hf.neg_left
theorem BoundedAtFilter.smul
    [SeminormedRing 𝕜] [SeminormedAddCommGroup β] [Module 𝕜 β] [BoundedSMul 𝕜 β]
    {l : Filter α} {f : α → β} (c : 𝕜) (hf : BoundedAtFilter l f) : BoundedAtFilter l (c • f) :=
  hf.const_smul_left c
nonrec theorem BoundedAtFilter.mul [SeminormedRing β] {l : Filter α} {f g : α → β}
    (hf : BoundedAtFilter l f) (hg : BoundedAtFilter l g) : BoundedAtFilter l (f * g) := by
  refine (hf.mul hg).trans ?_
  convert Asymptotics.isBigO_refl (E := ℝ) _ l
  simp
variable (𝕜) in
def boundedFilterSubmodule
    [SeminormedRing 𝕜] [SeminormedAddCommGroup β] [Module 𝕜 β] [BoundedSMul 𝕜 β] (l : Filter α) :
    Submodule 𝕜 (α → β) where
  carrier := BoundedAtFilter l
  zero_mem' := const_boundedAtFilter l 0
  add_mem' hf hg := hf.add hg
  smul_mem' c _ hf := hf.smul c
variable (𝕜) in
def boundedFilterSubalgebra
    [SeminormedCommRing 𝕜] [SeminormedRing β] [Algebra 𝕜 β] [BoundedSMul 𝕜 β] (l : Filter α) :
    Subalgebra 𝕜 (α → β) :=
  Submodule.toSubalgebra
    (boundedFilterSubmodule 𝕜 l)
    (const_boundedAtFilter l (1 : β))
    (fun f g hf hg ↦ by simpa only [Pi.one_apply, mul_one, norm_mul] using hf.mul hg)
end Filter