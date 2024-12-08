import Mathlib.Topology.Homeomorph
import Mathlib.Topology.Order.LeftRightNhds
open Set Filter
open Topology
section LinearOrder
variable {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
variable [LinearOrder β] [TopologicalSpace β] [OrderTopology β]
theorem StrictMonoOn.continuousWithinAt_right_of_exists_between {f : α → β} {s : Set α} {a : α}
    (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝[≥] a) (hfs : ∀ b > f a, ∃ c ∈ s, f c ∈ Ioc (f a) b) :
    ContinuousWithinAt f (Ici a) a := by
  have ha : a ∈ Ici a := left_mem_Ici
  have has : a ∈ s := mem_of_mem_nhdsWithin ha hs
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [hs, @self_mem_nhdsWithin _ _ a (Ici a)] with _ hxs hxa using hb.trans_le
      ((h_mono.le_iff_le has hxs).2 hxa)
  · rcases hfs b hb with ⟨c, hcs, hac, hcb⟩
    rw [h_mono.lt_iff_lt has hcs] at hac
    filter_upwards [hs, Ico_mem_nhdsWithin_Ici (left_mem_Ico.2 hac)]
    rintro x hx ⟨_, hxc⟩
    exact ((h_mono.lt_iff_lt hx hcs).2 hxc).trans_le hcb
theorem continuousWithinAt_right_of_monotoneOn_of_exists_between {f : α → β} {s : Set α} {a : α}
    (h_mono : MonotoneOn f s) (hs : s ∈ 𝓝[≥] a) (hfs : ∀ b > f a, ∃ c ∈ s, f c ∈ Ioo (f a) b) :
    ContinuousWithinAt f (Ici a) a := by
  have ha : a ∈ Ici a := left_mem_Ici
  have has : a ∈ s := mem_of_mem_nhdsWithin ha hs
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [hs, @self_mem_nhdsWithin _ _ a (Ici a)] with _ hxs hxa using hb.trans_le
      (h_mono has hxs hxa)
  · rcases hfs b hb with ⟨c, hcs, hac, hcb⟩
    have : a < c := not_le.1 fun h => hac.not_le <| h_mono hcs has h
    filter_upwards [hs, Ico_mem_nhdsWithin_Ici (left_mem_Ico.2 this)]
    rintro x hx ⟨_, hxc⟩
    exact (h_mono hx hcs hxc.le).trans_lt hcb
theorem continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin [DenselyOrdered β]
    {f : α → β} {s : Set α} {a : α} (h_mono : MonotoneOn f s) (hs : s ∈ 𝓝[≥] a)
    (hfs : closure (f '' s) ∈ 𝓝[≥] f a) : ContinuousWithinAt f (Ici a) a := by
  refine continuousWithinAt_right_of_monotoneOn_of_exists_between h_mono hs fun b hb => ?_
  rcases (mem_nhdsWithin_Ici_iff_exists_mem_Ioc_Ico_subset hb).1 hfs with ⟨b', ⟨hab', hbb'⟩, hb'⟩
  rcases exists_between hab' with ⟨c', hc'⟩
  rcases mem_closure_iff.1 (hb' ⟨hc'.1.le, hc'.2⟩) (Ioo (f a) b') isOpen_Ioo hc' with
    ⟨_, hc, ⟨c, hcs, rfl⟩⟩
  exact ⟨c, hcs, hc.1, hc.2.trans_le hbb'⟩
theorem continuousWithinAt_right_of_monotoneOn_of_image_mem_nhdsWithin [DenselyOrdered β]
    {f : α → β} {s : Set α} {a : α} (h_mono : MonotoneOn f s) (hs : s ∈ 𝓝[≥] a)
    (hfs : f '' s ∈ 𝓝[≥] f a) : ContinuousWithinAt f (Ici a) a :=
  continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin h_mono hs <|
    mem_of_superset hfs subset_closure
theorem StrictMonoOn.continuousWithinAt_right_of_closure_image_mem_nhdsWithin [DenselyOrdered β]
    {f : α → β} {s : Set α} {a : α} (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝[≥] a)
    (hfs : closure (f '' s) ∈ 𝓝[≥] f a) : ContinuousWithinAt f (Ici a) a :=
  continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin
    (fun _ hx _ hy => (h_mono.le_iff_le hx hy).2) hs hfs
theorem StrictMonoOn.continuousWithinAt_right_of_image_mem_nhdsWithin [DenselyOrdered β] {f : α → β}
    {s : Set α} {a : α} (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝[≥] a) (hfs : f '' s ∈ 𝓝[≥] f a) :
    ContinuousWithinAt f (Ici a) a :=
  h_mono.continuousWithinAt_right_of_closure_image_mem_nhdsWithin hs
    (mem_of_superset hfs subset_closure)
theorem StrictMonoOn.continuousWithinAt_right_of_surjOn {f : α → β} {s : Set α} {a : α}
    (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝[≥] a) (hfs : SurjOn f s (Ioi (f a))) :
    ContinuousWithinAt f (Ici a) a :=
  h_mono.continuousWithinAt_right_of_exists_between hs fun _ hb =>
    let ⟨c, hcs, hcb⟩ := hfs hb
    ⟨c, hcs, hcb.symm ▸ hb, hcb.le⟩
theorem StrictMonoOn.continuousWithinAt_left_of_exists_between {f : α → β} {s : Set α} {a : α}
    (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝[≤] a) (hfs : ∀ b < f a, ∃ c ∈ s, f c ∈ Ico b (f a)) :
    ContinuousWithinAt f (Iic a) a :=
  h_mono.dual.continuousWithinAt_right_of_exists_between hs fun b hb =>
    let ⟨c, hcs, hcb, hca⟩ := hfs b hb
    ⟨c, hcs, hca, hcb⟩
theorem continuousWithinAt_left_of_monotoneOn_of_exists_between {f : α → β} {s : Set α} {a : α}
    (hf : MonotoneOn f s) (hs : s ∈ 𝓝[≤] a) (hfs : ∀ b < f a, ∃ c ∈ s, f c ∈ Ioo b (f a)) :
    ContinuousWithinAt f (Iic a) a :=
  @continuousWithinAt_right_of_monotoneOn_of_exists_between αᵒᵈ βᵒᵈ _ _ _ _ _ _ f s a hf.dual hs
    fun b hb =>
    let ⟨c, hcs, hcb, hca⟩ := hfs b hb
    ⟨c, hcs, hca, hcb⟩
theorem continuousWithinAt_left_of_monotoneOn_of_closure_image_mem_nhdsWithin [DenselyOrdered β]
    {f : α → β} {s : Set α} {a : α} (hf : MonotoneOn f s) (hs : s ∈ 𝓝[≤] a)
    (hfs : closure (f '' s) ∈ 𝓝[≤] f a) : ContinuousWithinAt f (Iic a) a :=
  @continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin αᵒᵈ βᵒᵈ _ _ _ _ _ _ _ f s
    a hf.dual hs hfs
theorem continuousWithinAt_left_of_monotoneOn_of_image_mem_nhdsWithin [DenselyOrdered β] {f : α → β}
    {s : Set α} {a : α} (h_mono : MonotoneOn f s) (hs : s ∈ 𝓝[≤] a) (hfs : f '' s ∈ 𝓝[≤] f a) :
    ContinuousWithinAt f (Iic a) a :=
  continuousWithinAt_left_of_monotoneOn_of_closure_image_mem_nhdsWithin h_mono hs
    (mem_of_superset hfs subset_closure)
theorem StrictMonoOn.continuousWithinAt_left_of_closure_image_mem_nhdsWithin [DenselyOrdered β]
    {f : α → β} {s : Set α} {a : α} (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝[≤] a)
    (hfs : closure (f '' s) ∈ 𝓝[≤] f a) : ContinuousWithinAt f (Iic a) a :=
  h_mono.dual.continuousWithinAt_right_of_closure_image_mem_nhdsWithin hs hfs
theorem StrictMonoOn.continuousWithinAt_left_of_image_mem_nhdsWithin [DenselyOrdered β] {f : α → β}
    {s : Set α} {a : α} (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝[≤] a) (hfs : f '' s ∈ 𝓝[≤] f a) :
    ContinuousWithinAt f (Iic a) a :=
  h_mono.dual.continuousWithinAt_right_of_image_mem_nhdsWithin hs hfs
theorem StrictMonoOn.continuousWithinAt_left_of_surjOn {f : α → β} {s : Set α} {a : α}
    (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝[≤] a) (hfs : SurjOn f s (Iio (f a))) :
    ContinuousWithinAt f (Iic a) a :=
  h_mono.dual.continuousWithinAt_right_of_surjOn hs hfs
theorem StrictMonoOn.continuousAt_of_exists_between {f : α → β} {s : Set α} {a : α}
    (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝 a) (hfs_l : ∀ b < f a, ∃ c ∈ s, f c ∈ Ico b (f a))
    (hfs_r : ∀ b > f a, ∃ c ∈ s, f c ∈ Ioc (f a) b) : ContinuousAt f a :=
  continuousAt_iff_continuous_left_right.2
    ⟨h_mono.continuousWithinAt_left_of_exists_between (mem_nhdsWithin_of_mem_nhds hs) hfs_l,
      h_mono.continuousWithinAt_right_of_exists_between (mem_nhdsWithin_of_mem_nhds hs) hfs_r⟩
theorem StrictMonoOn.continuousAt_of_closure_image_mem_nhds [DenselyOrdered β] {f : α → β}
    {s : Set α} {a : α} (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝 a)
    (hfs : closure (f '' s) ∈ 𝓝 (f a)) : ContinuousAt f a :=
  continuousAt_iff_continuous_left_right.2
    ⟨h_mono.continuousWithinAt_left_of_closure_image_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hs)
        (mem_nhdsWithin_of_mem_nhds hfs),
      h_mono.continuousWithinAt_right_of_closure_image_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds hs) (mem_nhdsWithin_of_mem_nhds hfs)⟩
theorem StrictMonoOn.continuousAt_of_image_mem_nhds [DenselyOrdered β] {f : α → β} {s : Set α}
    {a : α} (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝 a) (hfs : f '' s ∈ 𝓝 (f a)) :
    ContinuousAt f a :=
  h_mono.continuousAt_of_closure_image_mem_nhds hs (mem_of_superset hfs subset_closure)
theorem continuousAt_of_monotoneOn_of_exists_between {f : α → β} {s : Set α} {a : α}
    (h_mono : MonotoneOn f s) (hs : s ∈ 𝓝 a) (hfs_l : ∀ b < f a, ∃ c ∈ s, f c ∈ Ioo b (f a))
    (hfs_r : ∀ b > f a, ∃ c ∈ s, f c ∈ Ioo (f a) b) : ContinuousAt f a :=
  continuousAt_iff_continuous_left_right.2
    ⟨continuousWithinAt_left_of_monotoneOn_of_exists_between h_mono (mem_nhdsWithin_of_mem_nhds hs)
        hfs_l,
      continuousWithinAt_right_of_monotoneOn_of_exists_between h_mono
        (mem_nhdsWithin_of_mem_nhds hs) hfs_r⟩
theorem continuousAt_of_monotoneOn_of_closure_image_mem_nhds [DenselyOrdered β] {f : α → β}
    {s : Set α} {a : α} (h_mono : MonotoneOn f s) (hs : s ∈ 𝓝 a)
    (hfs : closure (f '' s) ∈ 𝓝 (f a)) : ContinuousAt f a :=
  continuousAt_iff_continuous_left_right.2
    ⟨continuousWithinAt_left_of_monotoneOn_of_closure_image_mem_nhdsWithin h_mono
        (mem_nhdsWithin_of_mem_nhds hs) (mem_nhdsWithin_of_mem_nhds hfs),
      continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin h_mono
        (mem_nhdsWithin_of_mem_nhds hs) (mem_nhdsWithin_of_mem_nhds hfs)⟩
theorem continuousAt_of_monotoneOn_of_image_mem_nhds [DenselyOrdered β] {f : α → β} {s : Set α}
    {a : α} (h_mono : MonotoneOn f s) (hs : s ∈ 𝓝 a) (hfs : f '' s ∈ 𝓝 (f a)) : ContinuousAt f a :=
  continuousAt_of_monotoneOn_of_closure_image_mem_nhds h_mono hs
    (mem_of_superset hfs subset_closure)
theorem Monotone.continuous_of_denseRange [DenselyOrdered β] {f : α → β} (h_mono : Monotone f)
    (h_dense : DenseRange f) : Continuous f :=
  continuous_iff_continuousAt.mpr fun a =>
    continuousAt_of_monotoneOn_of_closure_image_mem_nhds (fun _ _ _ _ hxy => h_mono hxy)
        univ_mem <|
      by simp only [image_univ, h_dense.closure_eq, univ_mem]
theorem Monotone.continuous_of_surjective [DenselyOrdered β] {f : α → β} (h_mono : Monotone f)
    (h_surj : Function.Surjective f) : Continuous f :=
  h_mono.continuous_of_denseRange h_surj.denseRange
end LinearOrder
namespace OrderIso
variable {α β : Type*} [PartialOrder α] [PartialOrder β] [TopologicalSpace α] [TopologicalSpace β]
  [OrderTopology α] [OrderTopology β]
protected theorem continuous (e : α ≃o β) : Continuous e := by
  rw [‹OrderTopology β›.topology_eq_generate_intervals, continuous_generateFrom_iff]
  rintro s ⟨a, rfl | rfl⟩
  · rw [e.preimage_Ioi]
    apply isOpen_lt'
  · rw [e.preimage_Iio]
    apply isOpen_gt'
def toHomeomorph (e : α ≃o β) : α ≃ₜ β :=
  { e with
    continuous_toFun := e.continuous
    continuous_invFun := e.symm.continuous }
@[simp]
theorem coe_toHomeomorph (e : α ≃o β) : ⇑e.toHomeomorph = e :=
  rfl
@[simp]
theorem coe_toHomeomorph_symm (e : α ≃o β) : ⇑e.toHomeomorph.symm = e.symm :=
  rfl
end OrderIso