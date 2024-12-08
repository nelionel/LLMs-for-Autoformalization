import Mathlib.Algebra.GroupPower.IterateHom
import Mathlib.Data.Set.Pointwise.SMul
import Mathlib.Dynamics.FixedPoints.Basic
open Pointwise
open Set Function
@[to_additive
      "Let `n : ℤ` and `s` a subset of an additive commutative group `G` that is invariant
      under preimage for the map `x ↦ n • x`. Then `s` is invariant under the pointwise action of
      the additive subgroup of elements `g : G` such that `(n^j) • g = 0` for some `j : ℕ`.
      (This additive subgroup is called the Prüfer subgroup when `G` is the `AddCircle` and `n` is
      prime.)"]
theorem smul_eq_self_of_preimage_zpow_eq_self {G : Type*} [CommGroup G] {n : ℤ} {s : Set G}
    (hs : (fun x => x ^ n) ⁻¹' s = s) {g : G} {j : ℕ} (hg : g ^ n ^ j = 1) : g • s = s := by
  suffices ∀ {g' : G} (_ : g' ^ n ^ j = 1), g' • s ⊆ s by
    refine le_antisymm (this hg) ?_
    conv_lhs => rw [← smul_inv_smul g s]
    replace hg : g⁻¹ ^ n ^ j = 1 := by rw [inv_zpow, hg, inv_one]
    simpa only [le_eq_subset, set_smul_subset_set_smul_iff] using this hg
  rw [(IsFixedPt.preimage_iterate hs j : (zpowGroupHom n)^[j] ⁻¹' s = s).symm]
  rintro g' hg' - ⟨y, hy, rfl⟩
  change (zpowGroupHom n)^[j] (g' * y) ∈ s
  replace hg' : (zpowGroupHom n)^[j] g' = 1 := by simpa [zpowGroupHom]
  rwa [iterate_map_mul, hg', one_mul]