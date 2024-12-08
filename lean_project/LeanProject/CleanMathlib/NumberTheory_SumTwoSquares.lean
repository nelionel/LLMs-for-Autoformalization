import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.Zsqrtd.QuadraticReciprocity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
section Fermat
open GaussianInt
theorem Nat.Prime.sq_add_sq {p : ℕ} [Fact p.Prime] (hp : p % 4 ≠ 3) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by
  apply sq_add_sq_of_nat_prime_of_not_irreducible p
  rwa [_root_.irreducible_iff_prime, prime_iff_mod_four_eq_three_of_nat_prime p]
end Fermat
section General
theorem sq_add_sq_mul {R} [CommRing R] {a b x y u v : R} (ha : a = x ^ 2 + y ^ 2)
    (hb : b = u ^ 2 + v ^ 2) : ∃ r s : R, a * b = r ^ 2 + s ^ 2 :=
  ⟨x * u - y * v, x * v + y * u, by rw [ha, hb]; ring⟩
theorem Nat.sq_add_sq_mul {a b x y u v : ℕ} (ha : a = x ^ 2 + y ^ 2) (hb : b = u ^ 2 + v ^ 2) :
    ∃ r s : ℕ, a * b = r ^ 2 + s ^ 2 := by
  zify at ha hb ⊢
  obtain ⟨r, s, h⟩ := _root_.sq_add_sq_mul ha hb
  refine ⟨r.natAbs, s.natAbs, ?_⟩
  simpa only [Int.natCast_natAbs, sq_abs]
end General
section NegOneSquare
theorem ZMod.isSquare_neg_one_of_dvd {m n : ℕ} (hd : m ∣ n) (hs : IsSquare (-1 : ZMod n)) :
    IsSquare (-1 : ZMod m) := by
  let f : ZMod n →+* ZMod m := ZMod.castHom hd _
  rw [← RingHom.map_one f, ← RingHom.map_neg]
  exact hs.map f
theorem ZMod.isSquare_neg_one_mul {m n : ℕ} (hc : m.Coprime n) (hm : IsSquare (-1 : ZMod m))
    (hn : IsSquare (-1 : ZMod n)) : IsSquare (-1 : ZMod (m * n)) := by
  have : IsSquare (-1 : ZMod m × ZMod n) := by
    rw [show (-1 : ZMod m × ZMod n) = ((-1 : ZMod m), (-1 : ZMod n)) from rfl]
    obtain ⟨x, hx⟩ := hm
    obtain ⟨y, hy⟩ := hn
    rw [hx, hy]
    exact ⟨(x, y), rfl⟩
  simpa only [RingEquiv.map_neg_one] using this.map (ZMod.chineseRemainder hc).symm
theorem Nat.Prime.mod_four_ne_three_of_dvd_isSquare_neg_one {p n : ℕ} (hpp : p.Prime) (hp : p ∣ n)
    (hs : IsSquare (-1 : ZMod n)) : p % 4 ≠ 3 := by
  obtain ⟨y, h⟩ := ZMod.isSquare_neg_one_of_dvd hp hs
  rw [← sq, eq_comm, show (-1 : ZMod p) = -1 ^ 2 by ring] at h
  haveI : Fact p.Prime := ⟨hpp⟩
  exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' one_ne_zero h
theorem ZMod.isSquare_neg_one_iff {n : ℕ} (hn : Squarefree n) :
    IsSquare (-1 : ZMod n) ↔ ∀ {q : ℕ}, q.Prime → q ∣ n → q % 4 ≠ 3 := by
  refine ⟨fun H q hqp hqd => hqp.mod_four_ne_three_of_dvd_isSquare_neg_one hqd H, fun H => ?_⟩
  induction' n using induction_on_primes with p n hpp ih
  · exact False.elim (hn.ne_zero rfl)
  · exact ⟨0, by simp only [mul_zero, eq_iff_true_of_subsingleton]⟩
  · haveI : Fact p.Prime := ⟨hpp⟩
    have hcp : p.Coprime n := by
      by_contra hc
      exact hpp.not_unit (hn p <| mul_dvd_mul_left p <| hpp.dvd_iff_not_coprime.mpr hc)
    have hp₁ := ZMod.exists_sq_eq_neg_one_iff.mpr (H hpp (dvd_mul_right p n))
    exact ZMod.isSquare_neg_one_mul hcp hp₁
      (ih hn.of_mul_right fun hqp hqd => H hqp <| dvd_mul_of_dvd_right hqd _)
theorem ZMod.isSquare_neg_one_iff' {n : ℕ} (hn : Squarefree n) :
    IsSquare (-1 : ZMod n) ↔ ∀ {q : ℕ}, q ∣ n → q % 4 ≠ 3 := by
  have help : ∀ a b : ZMod 4, a ≠ 3 → b ≠ 3 → a * b ≠ 3 := by decide
  rw [ZMod.isSquare_neg_one_iff hn]
  refine ⟨?_, fun H q _ => H⟩
  intro H
  refine @induction_on_primes _ ?_ ?_ (fun p q hp hq hpq => ?_)
  · exact fun _ => by norm_num
  · exact fun _ => by norm_num
  · replace hp := H hp (dvd_of_mul_right_dvd hpq)
    replace hq := hq (dvd_of_mul_left_dvd hpq)
    rw [show 3 = 3 % 4 by norm_num, Ne, ← ZMod.natCast_eq_natCast_iff'] at hp hq ⊢
    rw [Nat.cast_mul]
    exact help p q hp hq
theorem Nat.eq_sq_add_sq_of_isSquare_mod_neg_one {n : ℕ} (h : IsSquare (-1 : ZMod n)) :
    ∃ x y : ℕ, n = x ^ 2 + y ^ 2 := by
  induction' n using induction_on_primes with p n hpp ih
  · exact ⟨0, 0, rfl⟩
  · exact ⟨0, 1, rfl⟩
  · haveI : Fact p.Prime := ⟨hpp⟩
    have hp : IsSquare (-1 : ZMod p) := ZMod.isSquare_neg_one_of_dvd ⟨n, rfl⟩ h
    obtain ⟨u, v, huv⟩ := Nat.Prime.sq_add_sq (ZMod.exists_sq_eq_neg_one_iff.mp hp)
    obtain ⟨x, y, hxy⟩ := ih (ZMod.isSquare_neg_one_of_dvd ⟨p, mul_comm _ _⟩ h)
    exact Nat.sq_add_sq_mul huv.symm hxy
theorem ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_isCoprime {n x y : ℤ} (h : n = x ^ 2 + y ^ 2)
    (hc : IsCoprime x y) : IsSquare (-1 : ZMod n.natAbs) := by
  obtain ⟨u, v, huv⟩ : IsCoprime x n := by
    have hc2 : IsCoprime (x ^ 2) (y ^ 2) := hc.pow
    rw [show y ^ 2 = n + -1 * x ^ 2 by rw [h]; ring] at hc2
    exact (IsCoprime.pow_left_iff zero_lt_two).mp hc2.of_add_mul_right_right
  have H : u * y * (u * y) - -1 = n * (-v ^ 2 * n + u ^ 2 + 2 * v) := by
    linear_combination -u ^ 2 * h + (n * v - u * x - 1) * huv
  refine ⟨u * y, ?_⟩
  conv_rhs => tactic => norm_cast
  rw [(by norm_cast : (-1 : ZMod n.natAbs) = (-1 : ℤ))]
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (Int.natAbs_dvd.mpr ⟨_, H⟩)
theorem ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime {n x y : ℕ} (h : n = x ^ 2 + y ^ 2)
    (hc : x.Coprime y) : IsSquare (-1 : ZMod n) := by
  zify at h
  exact ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_isCoprime h hc.isCoprime
theorem Nat.eq_sq_add_sq_iff_eq_sq_mul {n : ℕ} :
    (∃ x y : ℕ, n = x ^ 2 + y ^ 2) ↔ ∃ a b : ℕ, n = a ^ 2 * b ∧ IsSquare (-1 : ZMod b) := by
  constructor
  · rintro ⟨x, y, h⟩
    by_cases hxy : x = 0 ∧ y = 0
    · exact ⟨0, 1, by rw [h, hxy.1, hxy.2, zero_pow two_ne_zero, add_zero, zero_mul],
        ⟨0, by rw [zero_mul, neg_eq_zero, Fin.one_eq_zero_iff]⟩⟩
    · have hg := Nat.pos_of_ne_zero (mt Nat.gcd_eq_zero_iff.mp hxy)
      obtain ⟨g, x₁, y₁, _, h₂, h₃, h₄⟩ := Nat.exists_coprime' hg
      exact ⟨g, x₁ ^ 2 + y₁ ^ 2, by rw [h, h₃, h₄]; ring,
        ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime rfl h₂⟩
  · rintro ⟨a, b, h₁, h₂⟩
    obtain ⟨x', y', h⟩ := Nat.eq_sq_add_sq_of_isSquare_mod_neg_one h₂
    exact ⟨a * x', a * y', by rw [h₁, h]; ring⟩
end NegOneSquare
section Main
theorem Nat.eq_sq_add_sq_iff {n : ℕ} :
    (∃ x y : ℕ, n = x ^ 2 + y ^ 2) ↔ ∀ {q : ℕ}, q.Prime → q % 4 = 3 → Even (padicValNat q n) := by
  rcases n.eq_zero_or_pos with (rfl | hn₀)
  · exact ⟨fun _ q _ _ => (@padicValNat.zero q).symm ▸ even_zero, fun _ => ⟨0, 0, rfl⟩⟩
  rw [Nat.eq_sq_add_sq_iff_eq_sq_mul]
  refine ⟨fun H q hq h => ?_, fun H => ?_⟩
  · obtain ⟨a, b, h₁, h₂⟩ := H
    have hqb := padicValNat.eq_zero_of_not_dvd fun hf =>
      (hq.mod_four_ne_three_of_dvd_isSquare_neg_one hf h₂) h
    have hab : a ^ 2 * b ≠ 0 := h₁ ▸ hn₀.ne'
    have ha₂ := left_ne_zero_of_mul hab
    have ha := mt sq_eq_zero_iff.mpr ha₂
    have hb := right_ne_zero_of_mul hab
    haveI hqi : Fact q.Prime := ⟨hq⟩
    simp_rw [h₁, padicValNat.mul ha₂ hb, padicValNat.pow 2 ha, hqb, add_zero]
    exact even_two_mul _
  · obtain ⟨b, a, hb₀, ha₀, hab, hb⟩ := Nat.sq_mul_squarefree_of_pos hn₀
    refine ⟨a, b, hab.symm, (ZMod.isSquare_neg_one_iff hb).mpr fun {q} hqp hqb hq4 => ?_⟩
    refine Nat.not_even_iff_odd.2 ?_ (H hqp hq4)
    have hqb' : padicValNat q b = 1 :=
      b.factorization_def hqp ▸ le_antisymm (hb.natFactorization_le_one _)
        ((hqp.dvd_iff_one_le_factorization hb₀.ne').mp hqb)
    haveI hqi : Fact q.Prime := ⟨hqp⟩
    simp_rw [← hab, padicValNat.mul (pow_ne_zero 2 ha₀.ne') hb₀.ne', hqb',
      padicValNat.pow 2 ha₀.ne']
    exact odd_two_mul_add_one _
end Main