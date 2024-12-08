import Mathlib.Algebra.Lie.Submodule
universe u v w w₁ w₂
namespace LieSubmodule
variable {R : Type u} {L : Type v} {M : Type w} {M₂ : Type w₁}
variable [CommRing R] [LieRing L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M]
variable [AddCommGroup M₂] [Module R M₂] [LieRingModule L M₂]
variable (N N' : LieSubmodule R L M) (N₂ : LieSubmodule R L M₂)
variable (f : M →ₗ⁅R,L⁆ M₂)
section LieIdealOperations
theorem map_comap_le : map f (comap f N₂) ≤ N₂ :=
  (N₂ : Set M₂).image_preimage_subset f
theorem map_comap_eq (hf : N₂ ≤ f.range) : map f (comap f N₂) = N₂ := by
  rw [SetLike.ext'_iff]
  exact Set.image_preimage_eq_of_subset hf
theorem le_comap_map : N ≤ comap f (map f N) :=
  (N : Set M).subset_preimage_image f
theorem comap_map_eq (hf : f.ker = ⊥) : comap f (map f N) = N := by
  rw [SetLike.ext'_iff]
  exact (N : Set M).preimage_image_eq (f.ker_eq_bot.mp hf)
@[simp]
theorem map_comap_incl : map N.incl (comap N.incl N') = N ⊓ N' := by
  rw [← coe_toSubmodule_eq_iff]
  exact (N : Submodule R M).map_comap_subtype N'
variable [LieAlgebra R L] [LieModule R L M₂] (I J : LieIdeal R L)
instance hasBracket : Bracket (LieIdeal R L) (LieSubmodule R L M) :=
  ⟨fun I N => lieSpan R L { m | ∃ (x : I) (n : N), ⁅(x : L), (n : M)⁆ = m }⟩
theorem lieIdeal_oper_eq_span :
    ⁅I, N⁆ = lieSpan R L { m | ∃ (x : I) (n : N), ⁅(x : L), (n : M)⁆ = m } :=
  rfl
theorem lieIdeal_oper_eq_linear_span [LieModule R L M] :
    (↑⁅I, N⁆ : Submodule R M) =
      Submodule.span R { m | ∃ (x : I) (n : N), ⁅(x : L), (n : M)⁆ = m } := by
  apply le_antisymm
  · let s := { m : M | ∃ (x : ↥I) (n : ↥N), ⁅(x : L), (n : M)⁆ = m }
    have aux : ∀ (y : L), ∀ m' ∈ Submodule.span R s, ⁅y, m'⁆ ∈ Submodule.span R s := by
      intro y m' hm'
      refine Submodule.span_induction (R := R) (M := M) (s := s)
        (p := fun m' _ ↦ ⁅y, m'⁆ ∈ Submodule.span R s) ?_ ?_ ?_ ?_ hm'
      · rintro m'' ⟨x, n, hm''⟩; rw [← hm'', leibniz_lie]
        refine Submodule.add_mem _ ?_ ?_ <;> apply Submodule.subset_span
        · use ⟨⁅y, ↑x⁆, I.lie_mem x.property⟩, n
        · use x, ⟨⁅y, ↑n⁆, N.lie_mem n.property⟩
      · simp only [lie_zero, Submodule.zero_mem]
      · intro m₁ m₂ _ _ hm₁ hm₂; rw [lie_add]; exact Submodule.add_mem _ hm₁ hm₂
      · intro t m'' _ hm''; rw [lie_smul]; exact Submodule.smul_mem _ t hm''
    change _ ≤ ({ Submodule.span R s with lie_mem := fun hm' => aux _ _ hm' } : LieSubmodule R L M)
    rw [lieIdeal_oper_eq_span, lieSpan_le]
    exact Submodule.subset_span
  · rw [lieIdeal_oper_eq_span]; apply submodule_span_le_lieSpan
theorem lieIdeal_oper_eq_linear_span' [LieModule R L M] :
    (↑⁅I, N⁆ : Submodule R M) = Submodule.span R { m | ∃ x ∈ I, ∃ n ∈ N, ⁅x, n⁆ = m } := by
  rw [lieIdeal_oper_eq_linear_span]
  congr
  ext m
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨n, hn⟩, rfl⟩
    exact ⟨x, hx, n, hn, rfl⟩
  · rintro ⟨x, hx, n, hn, rfl⟩
    exact ⟨⟨x, hx⟩, ⟨n, hn⟩, rfl⟩
theorem lie_le_iff : ⁅I, N⁆ ≤ N' ↔ ∀ x ∈ I, ∀ m ∈ N, ⁅x, m⁆ ∈ N' := by
  rw [lieIdeal_oper_eq_span, LieSubmodule.lieSpan_le]
  refine ⟨fun h x hx m hm => h ⟨⟨x, hx⟩, ⟨m, hm⟩, rfl⟩, ?_⟩
  rintro h _ ⟨⟨x, hx⟩, ⟨m, hm⟩, rfl⟩
  exact h x hx m hm
variable {N I} in
theorem lie_coe_mem_lie (x : I) (m : N) : ⁅(x : L), (m : M)⁆ ∈ ⁅I, N⁆ := by
  rw [lieIdeal_oper_eq_span]; apply subset_lieSpan; use x, m
variable {N I} in
theorem lie_mem_lie {x : L} {m : M} (hx : x ∈ I) (hm : m ∈ N) : ⁅x, m⁆ ∈ ⁅I, N⁆ :=
  lie_coe_mem_lie ⟨x, hx⟩ ⟨m, hm⟩
theorem lie_comm : ⁅I, J⁆ = ⁅J, I⁆ := by
  suffices ∀ I J : LieIdeal R L, ⁅I, J⁆ ≤ ⁅J, I⁆ by exact le_antisymm (this I J) (this J I)
  clear! I J; intro I J
  rw [lieIdeal_oper_eq_span, lieSpan_le]; rintro x ⟨y, z, h⟩; rw [← h]
  rw [← lie_skew, ← lie_neg, ← LieSubmodule.coe_neg]
  apply lie_coe_mem_lie
theorem lie_le_right : ⁅I, N⁆ ≤ N := by
  rw [lieIdeal_oper_eq_span, lieSpan_le]; rintro m ⟨x, n, hn⟩; rw [← hn]
  exact N.lie_mem n.property
theorem lie_le_left : ⁅I, J⁆ ≤ I := by rw [lie_comm]; exact lie_le_right I J
theorem lie_le_inf : ⁅I, J⁆ ≤ I ⊓ J := by rw [le_inf_iff]; exact ⟨lie_le_left I J, lie_le_right J I⟩
@[simp]
theorem lie_bot : ⁅I, (⊥ : LieSubmodule R L M)⁆ = ⊥ := by rw [eq_bot_iff]; apply lie_le_right
@[simp]
theorem bot_lie : ⁅(⊥ : LieIdeal R L), N⁆ = ⊥ := by
  suffices ⁅(⊥ : LieIdeal R L), N⁆ ≤ ⊥ by exact le_bot_iff.mp this
  rw [lieIdeal_oper_eq_span, lieSpan_le]; rintro m ⟨⟨x, hx⟩, n, hn⟩; rw [← hn]
  change x ∈ (⊥ : LieIdeal R L) at hx; rw [mem_bot] at hx; simp [hx]
theorem lie_eq_bot_iff : ⁅I, N⁆ = ⊥ ↔ ∀ x ∈ I, ∀ m ∈ N, ⁅(x : L), m⁆ = 0 := by
  rw [lieIdeal_oper_eq_span, LieSubmodule.lieSpan_eq_bot_iff]
  refine ⟨fun h x hx m hm => h ⁅x, m⁆ ⟨⟨x, hx⟩, ⟨m, hm⟩, rfl⟩, ?_⟩
  rintro h - ⟨⟨x, hx⟩, ⟨⟨n, hn⟩, rfl⟩⟩
  exact h x hx n hn
variable {I J N N'} in
theorem mono_lie (h₁ : I ≤ J) (h₂ : N ≤ N') : ⁅I, N⁆ ≤ ⁅J, N'⁆ := by
  intro m h
  rw [lieIdeal_oper_eq_span, mem_lieSpan] at h; rw [lieIdeal_oper_eq_span, mem_lieSpan]
  intro N hN; apply h; rintro m' ⟨⟨x, hx⟩, ⟨n, hn⟩, hm⟩; rw [← hm]; apply hN
  use ⟨x, h₁ hx⟩, ⟨n, h₂ hn⟩
variable {I J} in
theorem mono_lie_left (h : I ≤ J) : ⁅I, N⁆ ≤ ⁅J, N⁆ :=
  mono_lie h (le_refl N)
variable {N N'} in
theorem mono_lie_right (h : N ≤ N') : ⁅I, N⁆ ≤ ⁅I, N'⁆ :=
  mono_lie (le_refl I) h
@[simp]
theorem lie_sup : ⁅I, N ⊔ N'⁆ = ⁅I, N⁆ ⊔ ⁅I, N'⁆ := by
  have h : ⁅I, N⁆ ⊔ ⁅I, N'⁆ ≤ ⁅I, N ⊔ N'⁆ := by
    rw [sup_le_iff]; constructor <;>
    apply mono_lie_right <;> [exact le_sup_left; exact le_sup_right]
  suffices ⁅I, N ⊔ N'⁆ ≤ ⁅I, N⁆ ⊔ ⁅I, N'⁆ by exact le_antisymm this h
  rw [lieIdeal_oper_eq_span, lieSpan_le]; rintro m ⟨x, ⟨n, hn⟩, h⟩; erw [LieSubmodule.mem_sup]
  rw [LieSubmodule.mem_sup] at hn; rcases hn with ⟨n₁, hn₁, n₂, hn₂, hn'⟩
  use ⁅(x : L), (⟨n₁, hn₁⟩ : N)⁆; constructor; · apply lie_coe_mem_lie
  use ⁅(x : L), (⟨n₂, hn₂⟩ : N')⁆; constructor; · apply lie_coe_mem_lie
  simp [← h, ← hn']
@[simp]
theorem sup_lie : ⁅I ⊔ J, N⁆ = ⁅I, N⁆ ⊔ ⁅J, N⁆ := by
  have h : ⁅I, N⁆ ⊔ ⁅J, N⁆ ≤ ⁅I ⊔ J, N⁆ := by
    rw [sup_le_iff]; constructor <;>
    apply mono_lie_left <;> [exact le_sup_left; exact le_sup_right]
  suffices ⁅I ⊔ J, N⁆ ≤ ⁅I, N⁆ ⊔ ⁅J, N⁆ by exact le_antisymm this h
  rw [lieIdeal_oper_eq_span, lieSpan_le]; rintro m ⟨⟨x, hx⟩, n, h⟩; erw [LieSubmodule.mem_sup]
  rw [LieSubmodule.mem_sup] at hx; rcases hx with ⟨x₁, hx₁, x₂, hx₂, hx'⟩
  use ⁅((⟨x₁, hx₁⟩ : I) : L), (n : N)⁆; constructor; · apply lie_coe_mem_lie
  use ⁅((⟨x₂, hx₂⟩ : J) : L), (n : N)⁆; constructor; · apply lie_coe_mem_lie
  simp [← h, ← hx']
theorem lie_inf : ⁅I, N ⊓ N'⁆ ≤ ⁅I, N⁆ ⊓ ⁅I, N'⁆ := by
  rw [le_inf_iff]; constructor <;>
  apply mono_lie_right <;> [exact inf_le_left; exact inf_le_right]
theorem inf_lie : ⁅I ⊓ J, N⁆ ≤ ⁅I, N⁆ ⊓ ⁅J, N⁆ := by
  rw [le_inf_iff]; constructor <;>
  apply mono_lie_left <;> [exact inf_le_left; exact inf_le_right]
theorem map_bracket_eq [LieModule R L M] : map f ⁅I, N⁆ = ⁅I, map f N⁆ := by
  rw [← coe_toSubmodule_eq_iff, coeSubmodule_map, lieIdeal_oper_eq_linear_span,
    lieIdeal_oper_eq_linear_span, Submodule.map_span]
  congr
  ext m
  constructor
  · rintro ⟨-, ⟨⟨x, ⟨n, hn⟩, rfl⟩, hm⟩⟩
    simp only [LieModuleHom.coe_toLinearMap, LieModuleHom.map_lie] at hm
    exact ⟨x, ⟨f n, (mem_map (f n)).mpr ⟨n, hn, rfl⟩⟩, hm⟩
  · rintro ⟨x, ⟨m₂, hm₂ : m₂ ∈ map f N⟩, rfl⟩
    obtain ⟨n, hn, rfl⟩ := (mem_map m₂).mp hm₂
    exact ⟨⁅x, n⁆, ⟨x, ⟨n, hn⟩, rfl⟩, by simp⟩
theorem comap_bracket_eq [LieModule R L M] (hf₁ : f.ker = ⊥) (hf₂ : N₂ ≤ f.range) :
    comap f ⁅I, N₂⁆ = ⁅I, comap f N₂⁆ := by
  conv_lhs => rw [← map_comap_eq N₂ f hf₂]
  rw [← map_bracket_eq, comap_map_eq _ f hf₁]
end LieIdealOperations
end LieSubmodule
namespace LieIdeal
open LieAlgebra
variable {R : Type u} {L : Type v} {L' : Type w₂}
variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
variable (f : L →ₗ⁅R⁆ L') (I : LieIdeal R L) (J : LieIdeal R L')
theorem map_bracket_le {I₁ I₂ : LieIdeal R L} : map f ⁅I₁, I₂⁆ ≤ ⁅map f I₁, map f I₂⁆ := by
  rw [map_le_iff_le_comap]; erw [LieSubmodule.lieSpan_le]
  intro x hx; obtain ⟨⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩, hx⟩ := hx; rw [← hx]
  let fy₁ : ↥(map f I₁) := ⟨f y₁, mem_map hy₁⟩
  let fy₂ : ↥(map f I₂) := ⟨f y₂, mem_map hy₂⟩
  change _ ∈ comap f ⁅map f I₁, map f I₂⁆
  simp only [Submodule.coe_mk, mem_comap, LieHom.map_lie]
  exact LieSubmodule.lie_coe_mem_lie fy₁ fy₂
theorem map_bracket_eq {I₁ I₂ : LieIdeal R L} (h : Function.Surjective f) :
    map f ⁅I₁, I₂⁆ = ⁅map f I₁, map f I₂⁆ := by
  suffices ⁅map f I₁, map f I₂⁆ ≤ map f ⁅I₁, I₂⁆ by exact le_antisymm (map_bracket_le f) this
  rw [← LieSubmodule.coeSubmodule_le_coeSubmodule, coe_map_of_surjective h,
    LieSubmodule.lieIdeal_oper_eq_linear_span, LieSubmodule.lieIdeal_oper_eq_linear_span,
    LinearMap.map_span]
  apply Submodule.span_mono
  rintro x ⟨⟨z₁, h₁⟩, ⟨z₂, h₂⟩, rfl⟩
  obtain ⟨y₁, rfl⟩ := mem_map_of_surjective h h₁
  obtain ⟨y₂, rfl⟩ := mem_map_of_surjective h h₂
  exact ⟨⁅(y₁ : L), (y₂ : L)⁆, ⟨y₁, y₂, rfl⟩, by apply f.map_lie⟩
theorem comap_bracket_le {J₁ J₂ : LieIdeal R L'} : ⁅comap f J₁, comap f J₂⁆ ≤ comap f ⁅J₁, J₂⁆ := by
  rw [← map_le_iff_le_comap]
  exact le_trans (map_bracket_le f) (LieSubmodule.mono_lie map_comap_le map_comap_le)
variable {f}
theorem map_comap_incl {I₁ I₂ : LieIdeal R L} : map I₁.incl (comap I₁.incl I₂) = I₁ ⊓ I₂ := by
  conv_rhs => rw [← I₁.incl_idealRange]
  rw [← map_comap_eq]
  exact I₁.incl_isIdealMorphism
theorem comap_bracket_eq {J₁ J₂ : LieIdeal R L'} (h : f.IsIdealMorphism) :
    comap f ⁅f.idealRange ⊓ J₁, f.idealRange ⊓ J₂⁆ = ⁅comap f J₁, comap f J₂⁆ ⊔ f.ker := by
  rw [← LieSubmodule.coe_toSubmodule_eq_iff, comap_coeSubmodule,
    LieSubmodule.sup_coe_toSubmodule, f.ker_coeSubmodule, ← Submodule.comap_map_eq,
    LieSubmodule.lieIdeal_oper_eq_linear_span, LieSubmodule.lieIdeal_oper_eq_linear_span,
    LinearMap.map_span]
  congr; simp only [LieHom.coe_toLinearMap, Set.mem_setOf_eq]; ext y
  constructor
  · rintro ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩, hy⟩; rw [← hy]
    rw [LieSubmodule.mem_inf, f.mem_idealRange_iff h] at hx₁ hx₂
    obtain ⟨⟨z₁, hz₁⟩, hz₁'⟩ := hx₁; rw [← hz₁] at hz₁'
    obtain ⟨⟨z₂, hz₂⟩, hz₂'⟩ := hx₂; rw [← hz₂] at hz₂'
    refine ⟨⁅z₁, z₂⁆, ⟨⟨z₁, hz₁'⟩, ⟨z₂, hz₂'⟩, rfl⟩, ?_⟩
    simp only [hz₁, hz₂, Submodule.coe_mk, LieHom.map_lie]
  · rintro ⟨x, ⟨⟨z₁, hz₁⟩, ⟨z₂, hz₂⟩, hx⟩, hy⟩; rw [← hy, ← hx]
    have hz₁' : f z₁ ∈ f.idealRange ⊓ J₁ := by
      rw [LieSubmodule.mem_inf]; exact ⟨f.mem_idealRange z₁, hz₁⟩
    have hz₂' : f z₂ ∈ f.idealRange ⊓ J₂ := by
      rw [LieSubmodule.mem_inf]; exact ⟨f.mem_idealRange z₂, hz₂⟩
    use ⟨f z₁, hz₁'⟩, ⟨f z₂, hz₂'⟩; simp only [Submodule.coe_mk, LieHom.map_lie]
theorem map_comap_bracket_eq {J₁ J₂ : LieIdeal R L'} (h : f.IsIdealMorphism) :
    map f ⁅comap f J₁, comap f J₂⁆ = ⁅f.idealRange ⊓ J₁, f.idealRange ⊓ J₂⁆ := by
  rw [← map_sup_ker_eq_map, ← comap_bracket_eq h, map_comap_eq h, inf_eq_right]
  exact le_trans (LieSubmodule.lie_le_left _ _) inf_le_left
theorem comap_bracket_incl {I₁ I₂ : LieIdeal R L} :
    ⁅comap I.incl I₁, comap I.incl I₂⁆ = comap I.incl ⁅I ⊓ I₁, I ⊓ I₂⁆ := by
  conv_rhs =>
    congr
    next => skip
    rw [← I.incl_idealRange]
  rw [comap_bracket_eq]
  · simp only [ker_incl, sup_bot_eq]
  · exact I.incl_isIdealMorphism
theorem comap_bracket_incl_of_le {I₁ I₂ : LieIdeal R L} (h₁ : I₁ ≤ I) (h₂ : I₂ ≤ I) :
    ⁅comap I.incl I₁, comap I.incl I₂⁆ = comap I.incl ⁅I₁, I₂⁆ := by
    rw [comap_bracket_incl]; rw [← inf_eq_right] at h₁ h₂; rw [h₁, h₂]
end LieIdeal