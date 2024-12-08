import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.PowerBasis
universe u v w
open Polynomial Finset
namespace Polynomial
section CommSemiring
variable {R : Type u} [CommSemiring R] {S : Type v} [CommSemiring S]
@[stacks 09H1 "first part"]
def Separable (f : R[X]) : Prop :=
  IsCoprime f (derivative f)
theorem separable_def (f : R[X]) : f.Separable ↔ IsCoprime f (derivative f) :=
  Iff.rfl
theorem separable_def' (f : R[X]) : f.Separable ↔ ∃ a b : R[X], a * f + b * (derivative f) = 1 :=
  Iff.rfl
theorem not_separable_zero [Nontrivial R] : ¬Separable (0 : R[X]) := by
  rintro ⟨x, y, h⟩
  simp only [derivative_zero, mul_zero, add_zero, zero_ne_one] at h
theorem Separable.ne_zero [Nontrivial R] {f : R[X]} (h : f.Separable) : f ≠ 0 :=
  (not_separable_zero <| · ▸ h)
@[simp]
theorem separable_one : (1 : R[X]).Separable :=
  isCoprime_one_left
@[nontriviality]
theorem separable_of_subsingleton [Subsingleton R] (f : R[X]) : f.Separable := by
  simp [Separable, IsCoprime, eq_iff_true_of_subsingleton]
theorem separable_X_add_C (a : R) : (X + C a).Separable := by
  rw [separable_def, derivative_add, derivative_X, derivative_C, add_zero]
  exact isCoprime_one_right
theorem separable_X : (X : R[X]).Separable := by
  rw [separable_def, derivative_X]
  exact isCoprime_one_right
theorem separable_C (r : R) : (C r).Separable ↔ IsUnit r := by
  rw [separable_def, derivative_C, isCoprime_zero_right, isUnit_C]
theorem Separable.of_mul_left {f g : R[X]} (h : (f * g).Separable) : f.Separable := by
  have := h.of_mul_left_left; rw [derivative_mul] at this
  exact IsCoprime.of_mul_right_left (IsCoprime.of_add_mul_left_right this)
theorem Separable.of_mul_right {f g : R[X]} (h : (f * g).Separable) : g.Separable := by
  rw [mul_comm] at h
  exact h.of_mul_left
theorem Separable.of_dvd {f g : R[X]} (hf : f.Separable) (hfg : g ∣ f) : g.Separable := by
  rcases hfg with ⟨f', rfl⟩
  exact Separable.of_mul_left hf
theorem separable_gcd_left {F : Type*} [Field F] [DecidableEq F[X]]
    {f : F[X]} (hf : f.Separable) (g : F[X]) :
    (EuclideanDomain.gcd f g).Separable :=
  Separable.of_dvd hf (EuclideanDomain.gcd_dvd_left f g)
theorem separable_gcd_right {F : Type*} [Field F] [DecidableEq F[X]]
    {g : F[X]} (f : F[X]) (hg : g.Separable) :
    (EuclideanDomain.gcd f g).Separable :=
  Separable.of_dvd hg (EuclideanDomain.gcd_dvd_right f g)
theorem Separable.isCoprime {f g : R[X]} (h : (f * g).Separable) : IsCoprime f g := by
  have := h.of_mul_left_left; rw [derivative_mul] at this
  exact IsCoprime.of_mul_right_right (IsCoprime.of_add_mul_left_right this)
theorem Separable.of_pow' {f : R[X]} :
    ∀ {n : ℕ} (_h : (f ^ n).Separable), IsUnit f ∨ f.Separable ∧ n = 1 ∨ n = 0
  | 0 => fun _h => Or.inr <| Or.inr rfl
  | 1 => fun h => Or.inr <| Or.inl ⟨pow_one f ▸ h, rfl⟩
  | n + 2 => fun h => by
    rw [pow_succ, pow_succ] at h
    exact Or.inl (isCoprime_self.1 h.isCoprime.of_mul_left_right)
theorem Separable.of_pow {f : R[X]} (hf : ¬IsUnit f) {n : ℕ} (hn : n ≠ 0)
    (hfs : (f ^ n).Separable) : f.Separable ∧ n = 1 :=
  (hfs.of_pow'.resolve_left hf).resolve_right hn
theorem Separable.map {p : R[X]} (h : p.Separable) {f : R →+* S} : (p.map f).Separable :=
  let ⟨a, b, H⟩ := h
  ⟨a.map f, b.map f, by
    rw [derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add, H,
      Polynomial.map_one]⟩
theorem _root_.Associated.separable {f g : R[X]}
    (ha : Associated f g) (h : f.Separable) : g.Separable := by
  obtain ⟨⟨u, v, h1, h2⟩, ha⟩ := ha
  obtain ⟨a, b, h⟩ := h
  refine ⟨a * v + b * derivative v, b * v, ?_⟩
  replace h := congr($h * $(h1))
  have h3 := congr(derivative $(h1))
  simp only [← ha, derivative_mul, derivative_one] at h3 ⊢
  calc
    _ = (a * f + b * derivative f) * (u * v)
      + (b * f) * (derivative u * v + u * derivative v) := by ring1
    _ = 1 := by rw [h, h3]; ring1
theorem _root_.Associated.separable_iff {f g : R[X]}
    (ha : Associated f g) : f.Separable ↔ g.Separable := ⟨ha.separable, ha.symm.separable⟩
theorem Separable.mul_unit {f g : R[X]} (hf : f.Separable) (hg : IsUnit g) : (f * g).Separable :=
  (associated_mul_unit_right f g hg).separable hf
theorem Separable.unit_mul {f g : R[X]} (hf : IsUnit f) (hg : g.Separable) : (f * g).Separable :=
  (associated_unit_mul_right g f hf).separable hg
theorem Separable.eval₂_derivative_ne_zero [Nontrivial S] (f : R →+* S) {p : R[X]}
    (h : p.Separable) {x : S} (hx : p.eval₂ f x = 0) :
    (derivative p).eval₂ f x ≠ 0 := by
  intro hx'
  obtain ⟨a, b, e⟩ := h
  apply_fun Polynomial.eval₂ f x at e
  simp only [eval₂_add, eval₂_mul, hx, mul_zero, hx', add_zero, eval₂_one, zero_ne_one] at e
theorem Separable.aeval_derivative_ne_zero [Nontrivial S] [Algebra R S] {p : R[X]}
    (h : p.Separable) {x : S} (hx : aeval x p = 0) :
    aeval x (derivative p) ≠ 0 :=
  h.eval₂_derivative_ne_zero (algebraMap R S) hx
variable (p q : ℕ)
theorem isUnit_of_self_mul_dvd_separable {p q : R[X]} (hp : p.Separable) (hq : q * q ∣ p) :
    IsUnit q := by
  obtain ⟨p, rfl⟩ := hq
  apply isCoprime_self.mp
  have : IsCoprime (q * (q * p))
      (q * (derivative q * p + derivative q * p + q * derivative p)) := by
    simp only [← mul_assoc, mul_add]
    dsimp only [Separable] at hp
    convert hp using 1
    rw [derivative_mul, derivative_mul]
    ring
  exact IsCoprime.of_mul_right_left (IsCoprime.of_mul_left_left this)
theorem emultiplicity_le_one_of_separable {p q : R[X]} (hq : ¬IsUnit q) (hsep : Separable p) :
    emultiplicity q p ≤ 1 := by
  contrapose! hq
  apply isUnit_of_self_mul_dvd_separable hsep
  rw [← sq]
  apply pow_dvd_of_le_emultiplicity
  exact Order.add_one_le_of_lt hq
theorem Separable.squarefree {p : R[X]} (hsep : Separable p) : Squarefree p := by
  classical
  rw [multiplicity.squarefree_iff_emultiplicity_le_one p]
  exact fun f => or_iff_not_imp_right.mpr fun hunit => emultiplicity_le_one_of_separable hunit hsep
end CommSemiring
section CommRing
variable {R : Type u} [CommRing R]
theorem separable_X_sub_C {x : R} : Separable (X - C x) := by
  simpa only [sub_eq_add_neg, C_neg] using separable_X_add_C (-x)
theorem Separable.mul {f g : R[X]} (hf : f.Separable) (hg : g.Separable) (h : IsCoprime f g) :
    (f * g).Separable := by
  rw [separable_def, derivative_mul]
  exact
    ((hf.mul_right h).add_mul_left_right _).mul_left ((h.symm.mul_right hg).mul_add_right_right _)
theorem separable_prod' {ι : Sort _} {f : ι → R[X]} {s : Finset ι} :
    (∀ x ∈ s, ∀ y ∈ s, x ≠ y → IsCoprime (f x) (f y)) →
      (∀ x ∈ s, (f x).Separable) → (∏ x ∈ s, f x).Separable := by
  classical
  exact Finset.induction_on s (fun _ _ => separable_one) fun a s has ih h1 h2 => by
    simp_rw [Finset.forall_mem_insert, forall_and] at h1 h2; rw [prod_insert has]
    exact
      h2.1.mul (ih h1.2.2 h2.2)
        (IsCoprime.prod_right fun i his => h1.1.2 i his <| Ne.symm <| ne_of_mem_of_not_mem his has)
theorem separable_prod {ι : Sort _} [Fintype ι] {f : ι → R[X]} (h1 : Pairwise (IsCoprime on f))
    (h2 : ∀ x, (f x).Separable) : (∏ x, f x).Separable :=
  separable_prod' (fun _x _hx _y _hy hxy => h1 hxy) fun x _hx => h2 x
theorem Separable.inj_of_prod_X_sub_C [Nontrivial R] {ι : Sort _} {f : ι → R} {s : Finset ι}
    (hfs : (∏ i ∈ s, (X - C (f i))).Separable) {x y : ι} (hx : x ∈ s) (hy : y ∈ s)
    (hfxy : f x = f y) : x = y := by
  classical
  by_contra hxy
  rw [← insert_erase hx, prod_insert (not_mem_erase _ _), ←
    insert_erase (mem_erase_of_ne_of_mem (Ne.symm hxy) hy), prod_insert (not_mem_erase _ _), ←
    mul_assoc, hfxy, ← sq] at hfs
  cases (hfs.of_mul_left.of_pow (not_isUnit_X_sub_C _) two_ne_zero).2
theorem Separable.injective_of_prod_X_sub_C [Nontrivial R] {ι : Sort _} [Fintype ι] {f : ι → R}
    (hfs : (∏ i, (X - C (f i))).Separable) : Function.Injective f := fun _x _y hfxy =>
  hfs.inj_of_prod_X_sub_C (mem_univ _) (mem_univ _) hfxy
theorem nodup_of_separable_prod [Nontrivial R] {s : Multiset R}
    (hs : Separable (Multiset.map (fun a => X - C a) s).prod) : s.Nodup := by
  rw [Multiset.nodup_iff_ne_cons_cons]
  rintro a t rfl
  refine not_isUnit_X_sub_C a (isUnit_of_self_mul_dvd_separable hs ?_)
  simpa only [Multiset.map_cons, Multiset.prod_cons] using mul_dvd_mul_left _ (dvd_mul_right _ _)
theorem separable_X_pow_sub_C_unit {n : ℕ} (u : Rˣ) (hn : IsUnit (n : R)) :
    Separable (X ^ n - C (u : R)) := by
  nontriviality R
  rcases n.eq_zero_or_pos with (rfl | hpos)
  · simp at hn
  apply (separable_def' (X ^ n - C (u : R))).2
  obtain ⟨n', hn'⟩ := hn.exists_left_inv
  refine ⟨-C ↑u⁻¹, C (↑u⁻¹ : R) * C n' * X, ?_⟩
  rw [derivative_sub, derivative_C, sub_zero, derivative_pow X n, derivative_X, mul_one]
  calc
    -C ↑u⁻¹ * (X ^ n - C ↑u) + C ↑u⁻¹ * C n' * X * (↑n * X ^ (n - 1)) =
        C (↑u⁻¹ * ↑u) - C ↑u⁻¹ * X ^ n + C ↑u⁻¹ * C (n' * ↑n) * (X * X ^ (n - 1)) := by
      simp only [C.map_mul, C_eq_natCast]
      ring
    _ = 1 := by
      simp only [Units.inv_mul, hn', C.map_one, mul_one, ← pow_succ',
        Nat.sub_add_cancel (show 1 ≤ n from hpos), sub_add_cancel]
theorem separable_C_mul_X_pow_add_C_mul_X_add_C
    {n : ℕ} (a b c : R) (hn : (n : R) = 0) (hb : IsUnit b) :
    (C a * X ^ n + C b * X + C c).Separable := by
  set f := C a * X ^ n + C b * X + C c
  have hderiv : derivative f = C b := by
    simp_rw [f, map_add derivative, derivative_C]
    simp [hn]
  obtain ⟨e, hb⟩ := hb.exists_left_inv
  refine ⟨-derivative f, f + C e, ?_⟩
  rw [hderiv, right_distrib, ← add_assoc, neg_mul, mul_comm, neg_add_cancel, zero_add,
    ← map_mul, hb, map_one]
theorem separable_C_mul_X_pow_add_C_mul_X_add_C'
    (p n : ℕ) (a b c : R) [CharP R p] (hn : p ∣ n) (hb : IsUnit b) :
    (C a * X ^ n + C b * X + C c).Separable :=
  separable_C_mul_X_pow_add_C_mul_X_add_C a b c ((CharP.cast_eq_zero_iff R p n).2 hn) hb
theorem rootMultiplicity_le_one_of_separable [Nontrivial R] {p : R[X]} (hsep : Separable p)
    (x : R) : rootMultiplicity x p ≤ 1 := by
  classical
  by_cases hp : p = 0
  · simp [hp]
  rw [rootMultiplicity_eq_multiplicity, if_neg hp, ← Nat.cast_le (α := ℕ∞),
    Nat.cast_one, ← (multiplicity_X_sub_C_finite x hp).emultiplicity_eq_multiplicity]
  apply emultiplicity_le_one_of_separable (not_isUnit_X_sub_C _) hsep
end CommRing
section IsDomain
variable {R : Type u} [CommRing R] [IsDomain R]
theorem count_roots_le_one [DecidableEq R] {p : R[X]} (hsep : Separable p) (x : R) :
    p.roots.count x ≤ 1 := by
  rw [count_roots p]
  exact rootMultiplicity_le_one_of_separable hsep x
theorem nodup_roots {p : R[X]} (hsep : Separable p) : p.roots.Nodup := by
  classical
  exact Multiset.nodup_iff_count_le_one.mpr (count_roots_le_one hsep)
end IsDomain
section Field
variable {F : Type u} [Field F] {K : Type v} [Field K]
theorem separable_iff_derivative_ne_zero {f : F[X]} (hf : Irreducible f) :
    f.Separable ↔ derivative f ≠ 0 :=
  ⟨fun h1 h2 => hf.not_unit <| isCoprime_zero_right.1 <| h2 ▸ h1, fun h =>
    EuclideanDomain.isCoprime_of_dvd (mt And.right h) fun g hg1 _hg2 ⟨p, hg3⟩ hg4 =>
      let ⟨u, hu⟩ := (hf.isUnit_or_isUnit hg3).resolve_left hg1
      have : f ∣ derivative f := by
        conv_lhs => rw [hg3, ← hu]
        rwa [Units.mul_right_dvd]
      not_lt_of_le (natDegree_le_of_dvd this h) <|
        natDegree_derivative_lt <| mt derivative_of_natDegree_zero h⟩
attribute [local instance] Ideal.Quotient.field in
theorem separable_map {S} [CommRing S] [Nontrivial S] (f : F →+* S) {p : F[X]} :
    (p.map f).Separable ↔ p.Separable := by
  refine ⟨fun H ↦ ?_, fun H ↦ H.map⟩
  obtain ⟨m, hm⟩ := Ideal.exists_maximal S
  have := Separable.map H (f := Ideal.Quotient.mk m)
  rwa [map_map, separable_def, derivative_map, isCoprime_map] at this
theorem separable_prod_X_sub_C_iff' {ι : Sort _} {f : ι → F} {s : Finset ι} :
    (∏ i ∈ s, (X - C (f i))).Separable ↔ ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y :=
  ⟨fun hfs _ hx _ hy hfxy => hfs.inj_of_prod_X_sub_C hx hy hfxy, fun H => by
    rw [← prod_attach]
    exact
      separable_prod'
        (fun x _hx y _hy hxy =>
          @pairwise_coprime_X_sub_C _ _ { x // x ∈ s } (fun x => f x)
            (fun x y hxy => Subtype.eq <| H x.1 x.2 y.1 y.2 hxy) _ _ hxy)
        fun _ _ => separable_X_sub_C⟩
theorem separable_prod_X_sub_C_iff {ι : Sort _} [Fintype ι] {f : ι → F} :
    (∏ i, (X - C (f i))).Separable ↔ Function.Injective f :=
  separable_prod_X_sub_C_iff'.trans <| by simp_rw [mem_univ, true_imp_iff, Function.Injective]
section CharP
variable (p : ℕ) [HF : CharP F p]
theorem separable_or {f : F[X]} (hf : Irreducible f) :
    f.Separable ∨ ¬f.Separable ∧ ∃ g : F[X], Irreducible g ∧ expand F p g = f := by
  classical
  exact if H : derivative f = 0 then by
    rcases p.eq_zero_or_pos with (rfl | hp)
    · haveI := CharP.charP_to_charZero F
      have := natDegree_eq_zero_of_derivative_eq_zero H
      have := (natDegree_pos_iff_degree_pos.mpr <| degree_pos_of_irreducible hf).ne'
      contradiction
    haveI := isLocalHom_expand F hp
    exact
      Or.inr
        ⟨by rw [separable_iff_derivative_ne_zero hf, Classical.not_not, H], contract p f,
          Irreducible.of_map (by rwa [← expand_contract p H hp.ne'] at hf),
          expand_contract p H hp.ne'⟩
  else Or.inl <| (separable_iff_derivative_ne_zero hf).2 H
theorem exists_separable_of_irreducible {f : F[X]} (hf : Irreducible f) (hp : p ≠ 0) :
    ∃ (n : ℕ) (g : F[X]), g.Separable ∧ expand F (p ^ n) g = f := by
  replace hp : p.Prime := (CharP.char_is_prime_or_zero F p).resolve_right hp
  induction' hn : f.natDegree using Nat.strong_induction_on with N ih generalizing f
  rcases separable_or p hf with (h | ⟨h1, g, hg, hgf⟩)
  · refine ⟨0, f, h, ?_⟩
    rw [pow_zero, expand_one]
  · cases' N with N
    · rw [natDegree_eq_zero_iff_degree_le_zero, degree_le_zero_iff] at hn
      rw [hn, separable_C, isUnit_iff_ne_zero, Classical.not_not] at h1
      have hf0 : f ≠ 0 := hf.ne_zero
      rw [h1, C_0] at hn
      exact absurd hn hf0
    have hg1 : g.natDegree * p = N.succ := by rwa [← natDegree_expand, hgf]
    have hg2 : g.natDegree ≠ 0 := by
      intro this
      rw [this, zero_mul] at hg1
      cases hg1
    have hg3 : g.natDegree < N.succ := by
      rw [← mul_one g.natDegree, ← hg1]
      exact Nat.mul_lt_mul_of_pos_left hp.one_lt hg2.bot_lt
    rcases ih _ hg3 hg rfl with ⟨n, g, hg4, rfl⟩
    refine ⟨n + 1, g, hg4, ?_⟩
    rw [← hgf, expand_expand, pow_succ']
theorem isUnit_or_eq_zero_of_separable_expand {f : F[X]} (n : ℕ) (hp : 0 < p)
    (hf : (expand F (p ^ n) f).Separable) : IsUnit f ∨ n = 0 := by
  rw [or_iff_not_imp_right]
  rintro hn : n ≠ 0
  have hf2 : derivative (expand F (p ^ n) f) = 0 := by
    rw [derivative_expand, Nat.cast_pow, CharP.cast_eq_zero, zero_pow hn, zero_mul, mul_zero]
  rw [separable_def, hf2, isCoprime_zero_right, isUnit_iff] at hf
  rcases hf with ⟨r, hr, hrf⟩
  rw [eq_comm, expand_eq_C (pow_pos hp _)] at hrf
  rwa [hrf, isUnit_C]
theorem unique_separable_of_irreducible {f : F[X]} (hf : Irreducible f) (hp : 0 < p) (n₁ : ℕ)
    (g₁ : F[X]) (hg₁ : g₁.Separable) (hgf₁ : expand F (p ^ n₁) g₁ = f) (n₂ : ℕ) (g₂ : F[X])
    (hg₂ : g₂.Separable) (hgf₂ : expand F (p ^ n₂) g₂ = f) : n₁ = n₂ ∧ g₁ = g₂ := by
  revert g₁ g₂
  wlog hn : n₁ ≤ n₂
  · intro g₁ hg₁ Hg₁ g₂ hg₂ Hg₂
    simpa only [eq_comm] using this p hf hp n₂ n₁ (le_of_not_le hn) g₂ hg₂ Hg₂ g₁ hg₁ Hg₁
  have hf0 : f ≠ 0 := hf.ne_zero
  intros g₁ hg₁ hgf₁ g₂ hg₂ hgf₂
  rw [le_iff_exists_add] at hn
  rcases hn with ⟨k, rfl⟩
  rw [← hgf₁, pow_add, expand_mul, expand_inj (pow_pos hp n₁)] at hgf₂
  subst hgf₂
  subst hgf₁
  rcases isUnit_or_eq_zero_of_separable_expand p k hp hg₁ with (h | rfl)
  · rw [isUnit_iff] at h
    rcases h with ⟨r, hr, rfl⟩
    simp_rw [expand_C] at hf
    exact absurd (isUnit_C.2 hr) hf.1
  · rw [add_zero, pow_zero, expand_one]
    constructor <;> rfl
end CharP
theorem separable_X_pow_sub_C {n : ℕ} (a : F) (hn : (n : F) ≠ 0) (ha : a ≠ 0) :
    Separable (X ^ n - C a) :=
  separable_X_pow_sub_C_unit (Units.mk0 a ha) (IsUnit.mk0 (n : F) hn)
theorem separable_X_pow_sub_C' (p n : ℕ) (a : F) [CharP F p] (hn : ¬p ∣ n) (ha : a ≠ 0) :
    Separable (X ^ n - C a) :=
  separable_X_pow_sub_C a (by rwa [← CharP.cast_eq_zero_iff F p n] at hn) ha
theorem X_pow_sub_one_separable_iff {n : ℕ} : (X ^ n - 1 : F[X]).Separable ↔ (n : F) ≠ 0 := by
  refine ⟨?_, fun h => separable_X_pow_sub_C_unit 1 (IsUnit.mk0 _ h)⟩
  rw [separable_def', derivative_sub, derivative_X_pow, derivative_one, sub_zero]
  rintro (h : IsCoprime _ _) hn'
  rw [hn', C_0, zero_mul, isCoprime_zero_right] at h
  exact not_isUnit_X_pow_sub_one F n h
section Splits
theorem card_rootSet_eq_natDegree [Algebra F K] {p : F[X]} (hsep : p.Separable)
    (hsplit : Splits (algebraMap F K) p) : Fintype.card (p.rootSet K) = p.natDegree := by
  classical
  simp_rw [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe]
  rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep.map), ← natDegree_eq_card_roots hsplit]
theorem nodup_roots_iff_of_splits {f : F[X]} (hf : f ≠ 0) (h : f.Splits (RingHom.id F)) :
    f.roots.Nodup ↔ f.Separable := by
  classical
  refine ⟨(fun hnsep ↦ ?_).mtr, nodup_roots⟩
  rw [Separable, ← gcd_isUnit_iff, isUnit_iff_degree_eq_zero] at hnsep
  obtain ⟨x, hx⟩ := exists_root_of_splits _
    (splits_of_splits_of_dvd _ hf h (gcd_dvd_left f _)) hnsep
  simp_rw [Multiset.nodup_iff_count_le_one, not_forall, not_le]
  exact ⟨x, ((one_lt_rootMultiplicity_iff_isRoot_gcd hf).2 hx).trans_eq f.count_roots.symm⟩
@[stacks 09H3 "Here we only require `f` splits instead of `K` is algebraically closed."]
theorem nodup_aroots_iff_of_splits [Algebra F K] {f : F[X]} (hf : f ≠ 0)
    (h : f.Splits (algebraMap F K)) : (f.aroots K).Nodup ↔ f.Separable := by
  rw [← (algebraMap F K).id_comp, ← splits_map_iff] at h
  rw [nodup_roots_iff_of_splits (map_ne_zero hf) h, separable_map]
theorem card_rootSet_eq_natDegree_iff_of_splits [Algebra F K] {f : F[X]} (hf : f ≠ 0)
    (h : f.Splits (algebraMap F K)) : Fintype.card (f.rootSet K) = f.natDegree ↔ f.Separable := by
  classical
  simp_rw [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe, natDegree_eq_card_roots h,
    Multiset.toFinset_card_eq_card_iff_nodup, nodup_aroots_iff_of_splits hf h]
variable {i : F →+* K}
theorem eq_X_sub_C_of_separable_of_root_eq {x : F} {h : F[X]} (h_sep : h.Separable)
    (h_root : h.eval x = 0) (h_splits : Splits i h) (h_roots : ∀ y ∈ (h.map i).roots, y = i x) :
    h = C (leadingCoeff h) * (X - C x) := by
  have h_ne_zero : h ≠ 0 := by
    rintro rfl
    exact not_separable_zero h_sep
  apply Polynomial.eq_X_sub_C_of_splits_of_single_root i h_splits
  apply Finset.mk.inj
  · change _ = {i x}
    rw [Finset.eq_singleton_iff_unique_mem]
    constructor
    · apply Finset.mem_mk.mpr
      · rw [mem_roots (show h.map i ≠ 0 from map_ne_zero h_ne_zero)]
        rw [IsRoot.def, ← eval₂_eq_eval_map, eval₂_hom, h_root]
        exact RingHom.map_zero i
      · exact nodup_roots (Separable.map h_sep)
    · exact h_roots
theorem exists_finset_of_splits (i : F →+* K) {f : F[X]} (sep : Separable f) (sp : Splits i f) :
    ∃ s : Finset K, f.map i = C (i f.leadingCoeff) * s.prod fun a : K => X - C a := by
  classical
  obtain ⟨s, h⟩ := (splits_iff_exists_multiset _).1 sp
  use s.toFinset
  rw [h, Finset.prod_eq_multiset_prod, ← Multiset.toFinset_eq]
  apply nodup_of_separable_prod
  apply Separable.of_mul_right
  rw [← h]
  exact sep.map
end Splits
theorem _root_.Irreducible.separable [CharZero F] {f : F[X]} (hf : Irreducible f) :
    f.Separable := by
  rw [separable_iff_derivative_ne_zero hf, Ne, ← degree_eq_bot, degree_derivative_eq]
  · rintro ⟨⟩
  rw [pos_iff_ne_zero, Ne, natDegree_eq_zero_iff_degree_le_zero, degree_le_zero_iff]
  refine fun hf1 => hf.not_unit ?_
  rw [hf1, isUnit_C, isUnit_iff_ne_zero]
  intro hf2
  rw [hf2, C_0] at hf1
  exact absurd hf1 hf.ne_zero
end Field
end Polynomial
open Polynomial
section CommRing
variable (F L K : Type*) [CommRing F] [Ring K] [Algebra F K]
variable {K} in
@[stacks 09H1 "second part"]
def IsSeparable (x : K) : Prop := Polynomial.Separable (minpoly F x)
@[mk_iff isSeparable_def, stacks 09H1 "third part"]
protected class Algebra.IsSeparable : Prop where
  isSeparable' : ∀ x : K, IsSeparable F x
variable {K}
theorem Algebra.IsSeparable.isSeparable [Algebra.IsSeparable F K] : ∀ x : K, IsSeparable F x :=
  Algebra.IsSeparable.isSeparable'
variable {F} in
theorem IsSeparable.isIntegral {x : K} (h : IsSeparable F x) : IsIntegral F x := by
  cases subsingleton_or_nontrivial F
  · haveI := Module.subsingleton F K
    exact ⟨1, monic_one, Subsingleton.elim _ _⟩
  · exact of_not_not (h.ne_zero <| minpoly.eq_zero ·)
theorem Algebra.IsSeparable.isIntegral [Algebra.IsSeparable F K] : ∀ x : K, IsIntegral F x :=
  fun x ↦ _root_.IsSeparable.isIntegral (Algebra.IsSeparable.isSeparable F x)
variable (K) in
instance Algebra.IsSeparable.isAlgebraic [Nontrivial F] [Algebra.IsSeparable F K] :
    Algebra.IsAlgebraic F K :=
  ⟨fun x ↦ (Algebra.IsSeparable.isIntegral F x).isAlgebraic⟩
variable {F}
theorem Algebra.isSeparable_iff :
    Algebra.IsSeparable F K ↔ ∀ x : K, IsIntegral F x ∧ IsSeparable F x :=
  ⟨fun _ x => ⟨Algebra.IsSeparable.isIntegral F x, Algebra.IsSeparable.isSeparable F x⟩,
    fun h => ⟨fun x => (h x).2⟩⟩
variable {E : Type*}
section AlgEquiv
variable [Ring E] [Algebra F E] (e : K ≃ₐ[F] E)
include e
theorem AlgEquiv.isSeparable_iff {x : K} : IsSeparable F (e x) ↔ IsSeparable F x := by
  simp only [IsSeparable, minpoly.algEquiv_eq e x]
theorem AlgEquiv.Algebra.isSeparable [Algebra.IsSeparable F K] : Algebra.IsSeparable F E :=
  ⟨fun _ ↦ e.symm.isSeparable_iff.mp (Algebra.IsSeparable.isSeparable _ _)⟩
@[deprecated (since := "2024-08-06")]
alias AlgEquiv.isSeparable := AlgEquiv.Algebra.isSeparable
theorem AlgEquiv.Algebra.isSeparable_iff : Algebra.IsSeparable F K ↔ Algebra.IsSeparable F E :=
  ⟨fun _ ↦ AlgEquiv.Algebra.isSeparable e, fun _ ↦ AlgEquiv.Algebra.isSeparable e.symm⟩
end AlgEquiv
section IsScalarTower
variable [Field L] [Ring E] [Algebra F L]
    [Algebra F E] [Algebra L E] [IsScalarTower F L E]
@[stacks 09H2 "first part"]
theorem IsSeparable.tower_top
    {x : E} (h : IsSeparable F x) : IsSeparable L x :=
  h.map.of_dvd (minpoly.dvd_map_of_isScalarTower _ _ _)
variable (F E) in
@[stacks 09H2 "second part"]
theorem Algebra.isSeparable_tower_top_of_isSeparable [Algebra.IsSeparable F E] :
    Algebra.IsSeparable L E :=
  ⟨fun x ↦ IsSeparable.tower_top _ (Algebra.IsSeparable.isSeparable F x)⟩
@[deprecated (since := "2024-08-06")]
alias IsSeparable.of_isScalarTower := Algebra.isSeparable_tower_top_of_isSeparable
end IsScalarTower
end CommRing
section Field
variable (F : Type*) [Field F] {K E E' : Type*}
section IsIntegral
variable [Ring K] [Algebra F K]
variable {F} in
theorem isSeparable_algebraMap (x : F) : IsSeparable F (algebraMap F K x) :=
  Polynomial.Separable.of_dvd (Polynomial.separable_X_sub_C (x := x))
    (minpoly.dvd F (algebraMap F K x) (by simp only [map_sub, aeval_X, aeval_C, sub_self]))
instance Algebra.isSeparable_self : Algebra.IsSeparable F F :=
  ⟨isSeparable_algebraMap⟩
variable [IsDomain K] [Algebra.IsIntegral F K] [CharZero F]
theorem IsSeparable.of_integral (x : K) : IsSeparable F x :=
  (minpoly.irreducible <| Algebra.IsIntegral.isIntegral x).separable
variable (K) in
protected instance (priority := 100) Algebra.IsSeparable.of_integral : Algebra.IsSeparable F K :=
  ⟨_root_.IsSeparable.of_integral _⟩
end IsIntegral
section IsScalarTower
variable [Field K] [Ring E] [Algebra F K] [Algebra F E] [Algebra K E]
  [Nontrivial E] [IsScalarTower F K E]
variable {F} in
theorem IsSeparable.tower_bot {x : K} (h : IsSeparable F (algebraMap K E x)) : IsSeparable F x :=
    have ⟨_q, hq⟩ :=
      minpoly.dvd F x
        ((aeval_algebraMap_eq_zero_iff _ _ _).mp (minpoly.aeval F ((algebraMap K E) x)))
    (Eq.mp (congrArg Separable hq) h).of_mul_left
variable (K E) in
theorem Algebra.isSeparable_tower_bot_of_isSeparable [h : Algebra.IsSeparable F E] :
    Algebra.IsSeparable F K :=
  ⟨fun _ ↦ IsSeparable.tower_bot (h.isSeparable _ _)⟩
end IsScalarTower
section
variable [Field E] [Field E'] [Algebra F E] [Algebra F E']
    (f : E →ₐ[F] E')
include f
variable {F} in
theorem IsSeparable.of_algHom {x : E} (h : IsSeparable F (f x)) : IsSeparable F x := by
  let _ : Algebra E E' := RingHom.toAlgebra f.toRingHom
  haveI : IsScalarTower F E E' := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  exact h.tower_bot
variable (E') in
theorem Algebra.IsSeparable.of_algHom [Algebra.IsSeparable F E'] : Algebra.IsSeparable F E :=
  ⟨fun x => (Algebra.IsSeparable.isSeparable F (f x)).of_algHom⟩
end
namespace IntermediateField
variable [Field K] [Algebra F K] (M : IntermediateField F K)
instance isSeparable_tower_bot [Algebra.IsSeparable F K] : Algebra.IsSeparable F M :=
  Algebra.isSeparable_tower_bot_of_isSeparable F M K
instance isSeparable_tower_top [Algebra.IsSeparable F K] : Algebra.IsSeparable M K :=
  Algebra.isSeparable_tower_top_of_isSeparable F M K
end IntermediateField
end Field
section AlgEquiv
open RingHom RingEquiv
variable {A₁ B₁ A₂ B₂ : Type*} [Field A₁] [Ring B₁] [Field A₂] [Ring B₂]
    [Algebra A₁ B₁] [Algebra A₂ B₂] (e₁ : A₁ ≃+* A₂) (e₂ : B₁ ≃+* B₂)
    (he : RingHom.comp (algebraMap A₂ B₂) ↑e₁ = RingHom.comp ↑e₂ (algebraMap A₁ B₁))
include he
lemma IsSeparable.of_equiv_equiv {x : B₁} (h : IsSeparable A₁ x) : IsSeparable A₂ (e₂ x) :=
  letI := e₁.toRingHom.toAlgebra
  letI : Algebra A₂ B₁ :=
    { (algebraMap A₁ B₁).comp e₁.symm.toRingHom with
        smul := fun a b ↦ ((algebraMap A₁ B₁).comp e₁.symm.toRingHom a) * b
        commutes' := fun r x ↦ (Algebra.commutes) (e₁.symm.toRingHom r) x
        smul_def' := fun _ _ ↦ rfl }
  haveI : IsScalarTower A₁ A₂ B₁ := IsScalarTower.of_algebraMap_eq <| fun x ↦
      (algebraMap A₁ B₁).congr_arg <| id ((e₁.symm_apply_apply x).symm)
  let e : B₁ ≃ₐ[A₂] B₂ :=
    { e₂ with
      commutes' := fun x ↦ by
        simpa [RingHom.algebraMap_toAlgebra] using DFunLike.congr_fun he.symm (e₁.symm x) }
  (AlgEquiv.isSeparable_iff e).mpr <| IsSeparable.tower_top A₂ h
lemma Algebra.IsSeparable.of_equiv_equiv [Algebra.IsSeparable A₁ B₁] : Algebra.IsSeparable A₂ B₂ :=
  ⟨fun x ↦ (e₂.apply_symm_apply x) ▸ _root_.IsSeparable.of_equiv_equiv e₁ e₂ he
    (Algebra.IsSeparable.isSeparable _ _)⟩
end AlgEquiv
section CardAlgHom
variable {R S T : Type*} [CommRing S]
variable {K L F : Type*} [Field K] [Field L] [Field F]
variable [Algebra K S] [Algebra K L]
theorem AlgHom.card_of_powerBasis (pb : PowerBasis K S) (h_sep : IsSeparable K pb.gen)
    (h_splits : (minpoly K pb.gen).Splits (algebraMap K L)) :
    @Fintype.card (S →ₐ[K] L) (PowerBasis.AlgHom.fintype pb) = pb.dim := by
  classical
  let _ := (PowerBasis.AlgHom.fintype pb : Fintype (S →ₐ[K] L))
  rw [Fintype.card_congr pb.liftEquiv', Fintype.card_of_subtype _ (fun x => Multiset.mem_toFinset),
    ← pb.natDegree_minpoly, natDegree_eq_card_roots h_splits, Multiset.toFinset_card_of_nodup]
  exact nodup_roots ((separable_map (algebraMap K L)).mpr h_sep)
end CardAlgHom