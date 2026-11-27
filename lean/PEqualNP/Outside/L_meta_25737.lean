import PEqualNP.Defs
import PEqualNP.Outside.L_lib_420

namespace PEqualNP.Outside.L_meta_25737_aux

open scoped Classical

abbrev F := ZMod 2

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

-- Section 1: Basic ZMod 2, sgn, dotProduct, and cyclic index helpers

private def sgn (b : F) : ℤ := if b = 0 then 1 else -1

private lemma z2_char2 : (2 : F) = 0 := by decide
private lemma z2_add_self (a : F) : a + a = 0 := by revert a; decide
private lemma z2_add_cancel_right (a b : F) : a + b + b = a := by revert a b; decide
private lemma z2_add_eq_zero_iff (a b : F) : a + b = 0 ↔ a = b := by revert a b; decide
private lemma z2_eq_zero_or_one (a : F) : a = 0 ∨ a = 1 := by revert a; decide
private lemma z2_mul_self (a : F) : a * a = a := by revert a; decide
private lemma z2_ite_eq_iff (a b : F) :
    ((if a = 0 then (0 : ℕ) else 1) = (if b = 0 then 0 else 1)) ↔ a = b := by
  revert a b; decide
private lemma z2_polar_prod (a1 a2 b1 b2 : F) :
    (a1 + a2) * (b1 + b2) + a1 * b1 + a2 * b2 = a1 * b2 + a2 * b1 := by
  revert a1 a2 b1 b2; decide
private lemma z2_four_lin (a b e : F) :
    (a + b + e) + (a + e) + (b + e) + e = 0 := by
  revert a b e; decide
private lemma z2_three_eq (a b c d : F) (h1 : a + b + c = 0) (h2 : b + d + a = 0) : d = c := by
  revert a b c d h1 h2; decide
private lemma z2_cancel3 (a b c : F) : a + b + (a + c) + (c + b) = 0 := by
  revert a b c; decide

private lemma sgn_add (a b : F) : sgn (a + b) = sgn a * sgn b := by revert a b; decide
private lemma sgn_sq (a : F) : sgn a * sgn a = 1 := by revert a; decide
private lemma sgn_zero : sgn 0 = 1 := rfl
private lemma sgn_one : sgn 1 = -1 := rfl

private lemma le_of_sq_le_sq_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : b ^ 2 ≤ a ^ 2) : b ≤ a := by
  by_contra hlt; push_neg at hlt; nlinarith

private lemma vec_add_self {n : ℕ} (u : Fin n → F) : u + u = 0 :=
  funext fun i => z2_add_self (u i)

private lemma vec_add_cancel_right {n : ℕ} (u v : Fin n → F) : u + v + v = u := by
  rw [add_assoc, vec_add_self, add_zero]

private lemma vec_add_cancel_left {n : ℕ} (u v : Fin n → F) : u + (u + v) = v := by
  rw [← add_assoc, vec_add_self, zero_add]

private lemma dot_add_right {n : ℕ} (a x y : Fin n → F) :
    dotProduct a (x + y) = dotProduct a x + dotProduct a y := by
  simp [dotProduct, mul_add, Finset.sum_add_distrib]

private def dotLin {n : ℕ} (a : Fin n → F) : (Fin n → F) →ₗ[F] F where
  toFun x := dotProduct a x
  map_add' x y := dot_add_right a x y
  map_smul' c x := by
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

private lemma add_to_linearMap {V : Type*} [AddCommGroup V] [Module F V]
    (g : V → F) (hadd : ∀ x y, g (x + y) = g x + g y) :
    ∃ L : V →ₗ[F] F, ∀ x, L x = g x := by
  have hg0 : g 0 = 0 := by
    have h := hadd 0 0
    rw [add_zero] at h
    rw [h, z2_add_self]
  refine ⟨{
    toFun := g
    map_add' := hadd
    map_smul' := fun c x => by
      rcases z2_eq_zero_or_one c with rfl | rfl
      · simp [hg0]
      · simp
  }, fun _ => rfl⟩

private lemma linearMap_eq_dotProduct {n : ℕ} (L : (Fin n → F) →ₗ[F] F) :
    ∃ a : Fin n → F, ∀ x, L x = dotProduct a x := by
  refine ⟨fun i => L (Pi.single i 1), fun x => ?_⟩
  have hx : x = ∑ i : Fin n, x i • Pi.single i (1 : F) := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hkj; simp [Pi.single_eq_of_ne (Ne.symm hkj)]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  conv_lhs => rw [hx]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, dotProduct]
  refine Finset.sum_congr rfl fun i _ => mul_comm _ _

private lemma sum_sgn_eq_two_mul_card_sub {α : Type*} [Fintype α] (f : α → F) :
    (∑ x : α, sgn (f x)) =
      2 * ((Finset.univ.filter (fun x => f x = 0)).card : ℤ) - (Fintype.card α : ℤ) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset α)
    (fun x => f x = 0) (fun x => sgn (f x))
  have h1 : (∑ x ∈ Finset.univ.filter (fun x => f x = 0), sgn (f x)) =
      ((Finset.univ.filter (fun x => f x = 0)).card : ℤ) := by
    trans (∑ _x ∈ Finset.univ.filter (fun x => f x = 0), (1 : ℤ))
    · refine Finset.sum_congr rfl fun x hx => by simp [(Finset.mem_filter.1 hx).2, sgn]
    · simp
  have h2 : (∑ x ∈ Finset.univ.filter (fun x => ¬ f x = 0), sgn (f x)) =
      -((Finset.univ.filter (fun x => ¬ f x = 0)).card : ℤ) := by
    trans (∑ _x ∈ Finset.univ.filter (fun x => ¬ f x = 0), (-1 : ℤ))
    · refine Finset.sum_congr rfl fun x hx => by simp [(Finset.mem_filter.1 hx).2, sgn]
    · simp
  have hcard : (Finset.univ.filter (fun x => f x = 0)).card +
      (Finset.univ.filter (fun x => ¬ f x = 0)).card = Fintype.card α := by
    have hs := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset α)
      (fun x => f x = 0) (fun _ => (1 : ℕ))
    simpa [Finset.card_univ] using hs
  rw [← hsplit, h1, h2]
  omega

private lemma card_vec (n : ℕ) : Fintype.card (Fin n → F) = 2 ^ n := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

private lemma card_finset_univ_vec (n : ℕ) : (Finset.univ : Finset (Fin n → F)).card = 2 ^ n := by
  rw [Finset.card_univ, card_vec]

-- Cyclic index arithmetic

private def ix (k : ℕ) (hk : 0 < k) (z : ℕ) : Fin k := ⟨z % k, Nat.mod_lt _ hk⟩

private lemma ix_val_eq (k : ℕ) (hk : 0 < k) (i : Fin k) : ix k hk i.val = i :=
  Fin.ext (Nat.mod_eq_of_lt i.isLt)

private lemma ix_add_ix (k : ℕ) (hk : 0 < k) (a b : ℕ) :
    ix k hk ((ix k hk a).val + b) = ix k hk (a + b) :=
  Fin.ext (by simp [ix, Nat.add_mod])

private lemma ix_add_mul_k (k : ℕ) (hk : 0 < k) (a m : ℕ) :
    ix k hk (a + m * k) = ix k hk a :=
  Fin.ext (by simp [ix, Nat.add_mul_mod_self_right])

private lemma ix_sub_add (k : ℕ) (hk : 0 < k) (i : Fin k) (r : ℕ) :
    ix k hk ((ix k hk (i.val + k - r % k)).val + r) = i := by
  rw [ix_add_ix]
  have hr : r % k < k := Nat.mod_lt r hk
  have hdiv : k * (r / k) + r % k = r := Nat.div_add_mod r k
  have heq : i.val + k - r % k + r = i.val + (1 + r / k) * k := by
    rw [Nat.add_mul, one_mul, mul_comm (r / k) k]
    omega
  rw [heq, ix_add_mul_k, ix_val_eq]

private lemma ix_add_sub (k : ℕ) (hk : 0 < k) (i : Fin k) (r : ℕ) :
    ix k hk ((ix k hk (i.val + r)).val + k - r % k) = i := by
  apply Fin.ext
  dsimp [ix]
  have hi : i.val < k := i.isLt
  have hr : r % k < k := Nat.mod_lt r hk
  have hmod : (i.val + r) % k = (i.val + r % k) % k := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt hi]
  rw [hmod]
  by_cases hlt : i.val + r % k < k
  · rw [Nat.mod_eq_of_lt hlt]
    have h1 : i.val + r % k + k - r % k = i.val + 1 * k := by omega
    rw [h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  · have h2 : (i.val + r % k) % k = i.val + r % k - k := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [h2]
    have h3 : i.val + r % k - k + k - r % k = i.val := by omega
    rw [h3, Nat.mod_eq_of_lt hi]

private lemma ix_next_injective (k : ℕ) (hk : 0 < k) :
    Function.Injective (fun i : Fin k => ix k hk (i.val + 1)) := by
  intro a b h
  dsimp only at h
  have ha := ix_add_sub k hk a 1
  have hb := ix_add_sub k hk b 1
  rw [← ha, ← hb, h]

-- Section 2: Invertibility of rot and mix, and reduction to qS

private def rotLin (k : ℕ) (hk : 0 < k) (q : ℕ) : (Fin k → F) →ₗ[F] (Fin k → F) where
  toFun x i := x (ix k hk (i.val + k - q % k))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma rotLin_injective (k : ℕ) (hk : 0 < k) (q : ℕ) :
    Function.Injective (rotLin k hk q) := by
  intro x y h
  funext i
  have hi := congrFun h (ix k hk (i.val + q))
  simpa [rotLin, ix_add_sub] using hi

private noncomputable def rotEquiv (k : ℕ) (hk : 0 < k) (q : ℕ) :
    (Fin k → F) ≃ₗ[F] (Fin k → F) :=
  LinearEquiv.ofBijective (rotLin k hk q)
    (Finite.injective_iff_bijective.mp (rotLin_injective k hk q))

private def mixLin (k : ℕ) (hk : 0 < k) (spacing : ℕ) : (Fin k → F) →ₗ[F] (Fin k → F) where
  toFun z j := z j + z (ix k hk (j.val + spacing)) + z (ix k hk (j.val + k - spacing % k))
  map_add' x y := by funext j; simp only [Pi.add_apply]; ring
  map_smul' c x := by funext j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

private lemma mixLin_ker_zero (k : ℕ) (hk : 0 < k) (hk3 : k % 3 ≠ 0) (spacing : ℕ)
    (z : Fin k → F) (hz : mixLin k hk spacing z = 0) : z = 0 := by
  have hval : ∀ j : Fin k,
      z j + z (ix k hk (j.val + spacing)) + z (ix k hk (j.val + k - spacing % k)) = 0 :=
    fun j => congrFun hz j
  have hper3 : ∀ j : Fin k, z (ix k hk (j.val + 3 * spacing)) = z j := by
    intro j
    let j1 := ix k hk (j.val + spacing)
    let j2 := ix k hk (j.val + 2 * spacing)
    have h1 := hval j1
    have hj1_next : ix k hk (j1.val + spacing) = j2 := by
      dsimp [j1, j2]; rw [ix_add_ix]; congr 1; omega
    have hj1_prev : ix k hk (j1.val + k - spacing % k) = j := ix_add_sub k hk j spacing
    rw [hj1_next, hj1_prev] at h1
    have h2 := hval j2
    have hj2_next : ix k hk (j2.val + spacing) = ix k hk (j.val + 3 * spacing) := by
      dsimp [j2]; rw [ix_add_ix]; congr 1; omega
    have hj2_prev : ix k hk (j2.val + k - spacing % k) = j1 := by
      rw [← hj1_next]; exact ix_add_sub k hk j1 spacing
    rw [hj2_next, hj2_prev] at h2
    exact z2_three_eq (z j1) (z j2) (z j) (z (ix k hk (j.val + 3 * spacing))) h1 h2
  have hperm : ∀ (m : ℕ) (j : Fin k), z (ix k hk (j.val + 3 * m * spacing)) = z j := by
    intro m
    induction m with
    | zero => intro j; simp [ix_val_eq]
    | succ m ih =>
      intro j
      have heq : j.val + 3 * (m + 1) * spacing = (j.val + 3 * m * spacing) + 3 * spacing := by ring
      rw [heq, ← ix_add_ix, hper3, ih]
  have hper1 : ∀ j : Fin k, z (ix k hk (j.val + spacing)) = z j := by
    intro j
    have hmod3 : k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hmod3 with h31 | h32
    · have hm := hperm (k / 3) (ix k hk (j.val + spacing))
      rw [ix_add_ix] at hm
      have heq : j.val + spacing + 3 * (k / 3) * spacing = j.val + spacing * k := by
        have hk' : 3 * (k / 3) + 1 = k := by omega
        calc j.val + spacing + 3 * (k / 3) * spacing
            = j.val + spacing * (3 * (k / 3) + 1) := by ring
          _ = j.val + spacing * k := by rw [hk']
      rw [heq, ix_add_mul_k, ix_val_eq] at hm
      exact hm.symm
    · have hm := hperm (k / 3 + 1) j
      have heq : j.val + 3 * (k / 3 + 1) * spacing = (j.val + spacing) + spacing * k := by
        have hk' : 3 * (k / 3 + 1) = k + 1 := by omega
        calc j.val + 3 * (k / 3 + 1) * spacing
            = j.val + (k + 1) * spacing := by rw [hk']
          _ = (j.val + spacing) + spacing * k := by ring
      rw [heq, ix_add_mul_k] at hm
      exact hm
  funext j
  have hprev : z (ix k hk (j.val + k - spacing % k)) = z j := by
    have hp := hper1 (ix k hk (j.val + k - spacing % k))
    rw [ix_sub_add] at hp
    exact hp.symm
  have hj := hval j
  rw [hper1 j, hprev, z2_add_self, zero_add] at hj
  exact hj

private lemma mixLin_injective (k : ℕ) (hk : 0 < k) (hk3 : k % 3 ≠ 0) (spacing : ℕ) :
    Function.Injective (mixLin k hk spacing) := by
  intro x y h
  have h0 : mixLin k hk spacing (x + y) = 0 := by rw [map_add, h, vec_add_self]
  have hxy : x + y = 0 := mixLin_ker_zero k hk hk3 spacing (x + y) h0
  funext i
  exact (z2_add_eq_zero_iff (x i) (y i)).1 (congrFun hxy i)

private noncomputable def mixEquiv (k : ℕ) (hk : 0 < k) (hk3 : k % 3 ≠ 0) (spacing : ℕ) :
    (Fin k → F) ≃ₗ[F] (Fin k → F) :=
  LinearEquiv.ofBijective (mixLin k hk spacing)
    (Finite.injective_iff_bijective.mp (mixLin_injective k hk hk3 spacing))

private def shift1Lin (k : ℕ) (hk : 0 < k) : (Fin k → F) →ₗ[F] (Fin k → F) where
  toFun u i := u (ix k hk (i.val + 1))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma shift1Lin_injective (k : ℕ) (hk : 0 < k) :
    Function.Injective (shift1Lin k hk) := by
  intro x y h
  funext i
  have hi := congrFun h (ix k hk (i.val + k - 1 % k))
  simpa [shift1Lin, ix_sub_add] using hi

private noncomputable def shift1Equiv (k : ℕ) (hk : 0 < k) :
    (Fin k → F) ≃ₗ[F] (Fin k → F) :=
  LinearEquiv.ofBijective (shift1Lin k hk)
    (Finite.injective_iff_bijective.mp (shift1Lin_injective k hk))

private def qS (k : ℕ) (hk : 0 < k) (S : Finset (Fin k)) (v : Fin k → F) : F :=
  ∑ i ∈ S, v i * v (ix k hk (i.val + 1))

private lemma qS_zero (k : ℕ) (hk : 0 < k) (S : Finset (Fin k)) : qS k hk S 0 = 0 := by
  simp [qS]

private def outFn (k : ℕ) (hk : 0 < k) (spacing s t : ℕ) (name c : Fin k → F)
    (x : Fin k → F) (i : Fin k) : F :=
  let z := rotLin k hk s x + name
  let y := fun j : Fin k =>
    z j + z (ix k hk (j.val + spacing)) + z (ix k hk (j.val + k - spacing % k))
  y i + (1 + y (ix k hk (i.val + 1))) * y (ix k hk (i.val + 2)) + rotLin k hk t x i + c i

private lemma outSum_eq_qS_add_affine (k : ℕ) (hk : 0 < k) (hk3 : k % 3 ≠ 0)
    (spacing s t : ℕ) (name c : Fin k → F) (S : Finset (Fin k)) :
    let E : (Fin k → F) ≃ₗ[F] (Fin k → F) :=
      (rotEquiv k hk s).trans ((mixEquiv k hk hk3 spacing).trans (shift1Equiv k hk))
    ∃ (L_aff : (Fin k → F) →ₗ[F] F) (c_aff : F),
      ∀ x : Fin k → F,
        (∑ i ∈ S, outFn k hk spacing s t name c x i) = qS k hk S (E x) + L_aff x + c_aff := by
  intro E
  let U_lin : (Fin k → F) →ₗ[F] (Fin k → F) := (mixLin k hk spacing).comp (rotLin k hk s)
  let y₀ : Fin k → F := mixLin k hk spacing name
  let L_term (i : Fin k) : (Fin k → F) →ₗ[F] F :=
    (LinearMap.proj i).comp U_lin +
    (1 + y₀ (ix k hk (i.val + 1))) • (LinearMap.proj (ix k hk (i.val + 2))).comp U_lin +
    (y₀ (ix k hk (i.val + 2))) • (LinearMap.proj (ix k hk (i.val + 1))).comp U_lin +
    (LinearMap.proj i).comp (rotLin k hk t)
  let c_term (i : Fin k) : F :=
    y₀ i + (1 + y₀ (ix k hk (i.val + 1))) * y₀ (ix k hk (i.val + 2)) + c i
  refine ⟨∑ i ∈ S, L_term i, ∑ i ∈ S, c_term i, fun x => ?_⟩
  simp only [qS, LinearMap.sum_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hy : ∀ j : Fin k,
      (let z := rotLin k hk s x + name
       z j + z (ix k hk (j.val + spacing)) + z (ix k hk (j.val + k - spacing % k))) =
        U_lin x j + y₀ j := by
    intro j
    change mixLin k hk spacing (rotLin k hk s x + name) j = _
    rw [map_add]; rfl
  have hE1 : E x i = U_lin x (ix k hk (i.val + 1)) := rfl
  have hE2 : E x (ix k hk (i.val + 1)) = U_lin x (ix k hk (i.val + 2)) := by
    change U_lin x (ix k hk ((ix k hk (i.val + 1)).val + 1)) = _
    rw [ix_add_ix]
  dsimp only [outFn]
  rw [hy i, hy (ix k hk (i.val + 1)), hy (ix k hk (i.val + 2)), hE1, hE2]
  simp only [L_term, c_term, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, smul_eq_mul]
  ring

-- Section 3: Polar form of qS

private def MS_lin (k : ℕ) (hk : 0 < k) (S : Finset (Fin k)) : (Fin k → F) →ₗ[F] (Fin k → F) where
  toFun v j :=
    (if j ∈ S then v (ix k hk (j.val + 1)) else 0) +
    (if ix k hk (j.val + k - 1 % k) ∈ S then v (ix k hk (j.val + k - 1 % k)) else 0)
  map_add' x y := by funext j; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c x := by
    funext j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

private lemma polar_qS_eq (k : ℕ) (hk : 0 < k) (S : Finset (Fin k)) (u v : Fin k → F) :
    qS k hk S (u + v) + qS k hk S u + qS k hk S v + qS k hk S 0 =
      dotProduct u (MS_lin k hk S v) := by
  rw [qS_zero, add_zero]
  have hlhs :
      qS k hk S (u + v) + qS k hk S u + qS k hk S v =
        (∑ i ∈ S, u i * v (ix k hk (i.val + 1))) +
        (∑ i ∈ S, u (ix k hk (i.val + 1)) * v i) := by
    dsimp only [qS]
    rw [← Finset.sum_add_distrib]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply]
    simpa [mul_comm] using z2_polar_prod (u i) (v i) (u (ix k hk (i.val + 1))) (v (ix k hk (i.val + 1)))
  rw [hlhs]
  dsimp only [dotProduct, MS_lin, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
  congr 1
  · rw [← Finset.sum_filter]; congr 1; ext j; simp
  · trans (∑ j : Fin k, if j ∈ S then u (ix k hk (j.val + 1)) * v j else 0)
    · rw [← Finset.sum_filter]; congr 1; ext j; simp
    · refine Finset.sum_bij (fun j _ => ix k hk (j.val + 1))
        (fun _ _ => Finset.mem_univ _)
        (fun a _ b _ h => ix_next_injective k hk h)
        (fun y _ => ⟨ix k hk (y.val + k - 1 % k), Finset.mem_univ _, ix_sub_add k hk y 1⟩)
        (fun j _ => by rw [ix_add_sub])

-- Section 3a: Linear path induction (modular helpers)

private def qLin (n : ℕ) (A : Finset (Fin n)) (v : Fin (n + 1) → F) : F :=
  ∑ i ∈ A, v i.castSucc * v i.succ

private def MLin (n : ℕ) (A : Finset (Fin n)) (v : Fin (n + 1) → F) (j : Fin (n + 1)) : F :=
  (if h1 : j.val < n then if (⟨j.val, h1⟩ : Fin n) ∈ A then v ⟨j.val + 1, by omega⟩ else 0 else 0) +
  (if h2 : 0 < j.val then if (⟨j.val - 1, by omega⟩ : Fin n) ∈ A then v ⟨j.val - 1, by omega⟩ else 0 else 0)

private def isIndepLin (n : ℕ) (E : Finset (Fin n)) : Prop :=
  ∀ i ∈ E, ∀ h : i.val + 1 < n, (⟨i.val + 1, h⟩ : Fin n) ∉ E

private noncomputable def muLin (n : ℕ) (A : Finset (Fin n)) : ℕ :=
  (A.powerset.filter (isIndepLin n)).sup Finset.card

private lemma lin_mu_step_mem (n' : ℕ) (A : Finset (Fin (n' + 2)))
    (hlast : (⟨n' + 1, by omega⟩ : Fin (n' + 2)) ∈ A) :
    let emb : Fin n' → Fin (n' + 2) := fun i => ⟨i.val, by omega⟩
    let A' : Finset (Fin n') := Finset.univ.filter (fun i : Fin n' => emb i ∈ A)
    muLin (n' + 2) A = muLin n' A' + 1 := by
  intro emb A'
  let last : Fin (n' + 2) := ⟨n' + 1, by omega⟩
  let prevLast : Fin (n' + 2) := ⟨n', by omega⟩
  have hemb_inj : Function.Injective emb :=
    fun a b h => Fin.ext (by simpa [emb] using congrArg Fin.val h)
  apply le_antisymm
  · apply Finset.sup_le
    intro E hE
    rw [Finset.mem_filter, Finset.mem_powerset] at hE
    rcases hE with ⟨hEA, hEind⟩
    let E' : Finset (Fin n') := Finset.univ.filter (fun i : Fin n' => emb i ∈ E)
    have hE'mem : E' ∈ A'.powerset.filter (isIndepLin n') := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨fun i hi => Finset.mem_filter.2 ⟨Finset.mem_univ _, hEA (Finset.mem_filter.1 hi).2⟩,
        fun i hi hlt hmem => ?_⟩
      exact hEind (emb i) (Finset.mem_filter.1 hi).2 (by dsimp [emb]; omega) (Finset.mem_filter.1 hmem).2
    have hE'le : E'.card ≤ muLin n' A' := Finset.le_sup (f := Finset.card) hE'mem
    have hnotboth : ¬ (prevLast ∈ E ∧ last ∈ E) := by
      rintro ⟨hp, hl⟩
      exact hEind prevLast hp (by dsimp [prevLast]; omega) hl
    have hsub : E ⊆ E'.image emb ∪ (if last ∈ E then {last} else {prevLast}) := by
      intro i hi
      rw [Finset.mem_union]
      by_cases hlt : i.val < n'
      · left
        rw [Finset.mem_image]
        exact ⟨⟨i.val, hlt⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩, Fin.ext rfl⟩
      · right
        by_cases hil : i = last
        · rw [hil] at hi ⊢; simp [hi]
        · have hip : i = prevLast := Fin.ext (by have := i.isLt; have hne : i.val ≠ last.val := fun h => hil (Fin.ext h); dsimp [prevLast, last] at *; omega)
          rw [hip] at hi ⊢
          have hnl : last ∉ E := fun hl => hnotboth ⟨hi, hl⟩
          simp [hnl]
    have hcard_tail : (if last ∈ E then ({last} : Finset (Fin (n' + 2))) else {prevLast}).card = 1 := by
      split_ifs <;> simp
    calc E.card
        ≤ (E'.image emb ∪ (if last ∈ E then {last} else {prevLast})).card := Finset.card_le_card hsub
      _ ≤ (E'.image emb).card + (if last ∈ E then ({last} : Finset (Fin (n' + 2))) else {prevLast}).card :=
          Finset.card_union_le _ _
      _ = E'.card + 1 := by rw [Finset.card_image_of_injective _ hemb_inj, hcard_tail]
      _ ≤ muLin n' A' + 1 := by omega
  · have hne : (A'.powerset.filter (isIndepLin n')).Nonempty :=
      ⟨∅, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.empty_subset _), fun _ hi => by simp at hi⟩⟩
    obtain ⟨E', hE'mem, hE'card⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
    rw [Finset.mem_filter, Finset.mem_powerset] at hE'mem
    rcases hE'mem with ⟨hE'A', hE'ind⟩
    let E : Finset (Fin (n' + 2)) := insert last (E'.image emb)
    have hnotmem : last ∉ E'.image emb := by
      rw [Finset.mem_image]; rintro ⟨i, _, hi⟩
      have := congrArg Fin.val hi; dsimp [emb, last] at this; omega
    have hEmem : E ∈ A.powerset.filter (isIndepLin (n' + 2)) := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨?_, ?_⟩
      · intro i hi
        rcases Finset.mem_insert.1 hi with rfl | hi'
        · exact hlast
        · rcases Finset.mem_image.1 hi' with ⟨j, hj, rfl⟩
          exact (Finset.mem_filter.1 (hE'A' hj)).2
      · intro i hi hlt hnext
        rcases Finset.mem_insert.1 hi with rfl | hi'
        · dsimp [last] at hlt; omega
        · rcases Finset.mem_image.1 hi' with ⟨j, hj, rfl⟩
          rcases Finset.mem_insert.1 hnext with hnl | hni
          · have := congrArg Fin.val hnl; dsimp [emb, last] at this; omega
          · rcases Finset.mem_image.1 hni with ⟨j2, hj2, hjeq⟩
            have hjval : j2.val = j.val + 1 := by
              have := congrArg Fin.val hjeq; dsimp [emb] at this; omega
            have hlt' : j.val + 1 < n' := by omega
            have hjeq2 : (⟨j.val + 1, hlt'⟩ : Fin n') = j2 := Fin.ext hjval.symm
            exact hE'ind j hj hlt' (hjeq2 ▸ hj2)
    have hEcard : E.card = muLin n' A' + 1 := by
      rw [Finset.card_insert_of_notMem hnotmem, Finset.card_image_of_injective _ hemb_inj]
      exact congrArg (· + 1) hE'card.symm
    rw [← hEcard]
    exact Finset.le_sup (f := Finset.card) hEmem

private lemma lin_ker_step_mem (n' : ℕ) (A : Finset (Fin (n' + 2)))
    (hlast : (⟨n' + 1, by omega⟩ : Fin (n' + 2)) ∈ A) :
    let emb : Fin n' → Fin (n' + 2) := fun i => ⟨i.val, by omega⟩
    let A' : Finset (Fin n') := Finset.univ.filter (fun i : Fin n' => emb i ∈ A)
    (Finset.univ.filter (fun v : Fin (n' + 3) → F => MLin (n' + 2) A v = 0)).card =
      (Finset.univ.filter (fun w : Fin (n' + 1) → F => MLin n' A' w = 0)).card := by
  intro emb A'
  let last : Fin (n' + 2) := ⟨n' + 1, by omega⟩
  let prevLast : Fin (n' + 2) := ⟨n', by omega⟩
  let b : F := if prevLast ∈ A then 1 else 0
  have hmem_iff : ∀ (j : ℕ) (hjn : j < n'),
      ((⟨j, by omega⟩ : Fin (n' + 2)) ∈ A) ↔ ((⟨j, hjn⟩ : Fin n') ∈ A') := by
    intro j hjn; simp [A', emb]
  have hrow_le : ∀ (v : Fin (n' + 3) → F), v ⟨n' + 1, by omega⟩ = 0 →
      ∀ j : Fin (n' + 1),
        MLin (n' + 2) A v ⟨j.val, by omega⟩ =
          MLin n' A' (fun t : Fin (n' + 1) => v ⟨t.val, by omega⟩) j := by
    intro v hv1 j
    dsimp only [MLin]
    congr 1
    · by_cases hjn : j.val < n'
      · have h1a : j.val < n' + 2 := by omega
        simp only [hjn, h1a, ↓reduceDIte]
        by_cases hm : (⟨j.val, hjn⟩ : Fin n') ∈ A'
        · simp [hm, (hmem_iff j.val hjn).2 hm]
        · simp [hm, mt (hmem_iff j.val hjn).1 hm]
      · have h1a : j.val < n' + 2 := by omega
        simp only [hjn, h1a, ↓reduceDIte]
        have hv1' : v ⟨j.val + 1, by omega⟩ = 0 := by
          have : (⟨j.val + 1, by omega⟩ : Fin (n' + 3)) = ⟨n' + 1, by omega⟩ := Fin.ext (by dsimp; have := j.isLt; omega)
          rw [this, hv1]
        rw [hv1']; split_ifs <;> rfl
    · by_cases h2 : 0 < j.val
      · simp only [h2, ↓reduceDIte]
        have hjn' : j.val - 1 < n' := by omega
        by_cases hm : (⟨j.val - 1, hjn'⟩ : Fin n') ∈ A'
        · simp [hm, (hmem_iff (j.val - 1) hjn').2 hm]
        · simp [hm, mt (hmem_iff (j.val - 1) hjn').1 hm]
      · simp [h2]
  have hker_iff : ∀ v : Fin (n' + 3) → F,
      MLin (n' + 2) A v = 0 ↔
        MLin n' A' (fun j : Fin (n' + 1) => v ⟨j.val, by omega⟩) = 0 ∧
        v ⟨n' + 1, by omega⟩ = 0 ∧
        v ⟨n' + 2, by omega⟩ = b * v ⟨n', by omega⟩ := by
    intro v
    constructor
    · intro hv
      have hv1 : v ⟨n' + 1, by omega⟩ = 0 := by
        have h := congrFun hv ⟨n' + 2, by omega⟩
        simp only [MLin, Pi.zero_apply] at h
        have h1 : ¬ (n' + 2 < n' + 2) := by omega
        have h2 : (0 : ℕ) < n' + 2 := by omega
        simp only [h1, h2, ↓reduceDIte, zero_add] at h
        have hmem : (⟨n' + 2 - 1, by omega⟩ : Fin (n' + 2)) ∈ A := by convert hlast using 1; exact Fin.ext rfl
        rw [if_pos hmem] at h; exact h
      have hv2 : v ⟨n' + 2, by omega⟩ = b * v ⟨n', by omega⟩ := by
        have h := congrFun hv ⟨n' + 1, by omega⟩
        simp only [MLin, Pi.zero_apply] at h
        have h1 : n' + 1 < n' + 2 := by omega
        have h2 : (0 : ℕ) < n' + 1 := by omega
        simp only [h1, h2, ↓reduceDIte, hlast, ↓reduceIte] at h
        have hterm : (if (⟨n' + 1 - 1, by omega⟩ : Fin (n' + 2)) ∈ A then
            v ⟨n' + 1 - 1, by omega⟩ else 0) = b * v ⟨n', by omega⟩ := by
          dsimp [b, prevLast]; split_ifs <;> simp
        rw [hterm] at h
        exact (z2_add_eq_zero_iff _ _).1 h
      refine ⟨?_, hv1, hv2⟩
      funext j
      rw [← hrow_le v hv1 j, hv]; rfl
    · rintro ⟨hw, hv1, hv2⟩
      funext j
      simp only [Pi.zero_apply]
      by_cases hlt : j.val < n' + 1
      · have := hrow_le v hv1 ⟨j.val, hlt⟩
        rw [this, hw]; rfl
      · by_cases hj1 : j.val = n' + 1
        · have heq : j = ⟨n' + 1, by omega⟩ := Fin.ext hj1
          rw [heq]
          simp only [MLin]
          have h1 : n' + 1 < n' + 2 := by omega
          have h2 : (0 : ℕ) < n' + 1 := by omega
          simp only [h1, h2, ↓reduceDIte, hlast, ↓reduceIte]
          have hterm : (if (⟨n' + 1 - 1, by omega⟩ : Fin (n' + 2)) ∈ A then
              v ⟨n' + 1 - 1, by omega⟩ else 0) = b * v ⟨n', by omega⟩ := by
            dsimp [b, prevLast]; split_ifs <;> simp
          rw [hterm, hv2, z2_add_self]
        · have heq : j = ⟨n' + 2, by omega⟩ := Fin.ext (by dsimp; have := j.isLt; omega)
          rw [heq]
          simp only [MLin]
          have h1 : ¬ (n' + 2 < n' + 2) := by omega
          have h2 : (0 : ℕ) < n' + 2 := by omega
          simp only [h1, h2, ↓reduceDIte, zero_add]
          have hmem : (⟨n' + 2 - 1, by omega⟩ : Fin (n' + 2)) ∈ A := by convert hlast using 1; exact Fin.ext rfl
          rw [if_pos hmem]; exact hv1
  refine Finset.card_bij
    (fun v _ => fun j : Fin (n' + 1) => v ⟨j.val, by omega⟩)
    (fun v hv => Finset.mem_filter.2 ⟨Finset.mem_univ _, ((hker_iff v).1 (Finset.mem_filter.1 hv).2).1⟩)
    (fun v1 hv1 v2 hv2 heq => ?_)
    (fun w hw => ?_)
  · have h1 := (hker_iff v1).1 (Finset.mem_filter.1 hv1).2
    have h2 := (hker_iff v2).1 (Finset.mem_filter.1 hv2).2
    funext j
    by_cases hlt : j.val < n' + 1
    · exact congrFun heq ⟨j.val, hlt⟩
    · by_cases hj1 : j.val = n' + 1
      · rw [(Fin.ext hj1 : j = ⟨n' + 1, by omega⟩), h1.2.1, h2.2.1]
      · rw [(Fin.ext (by dsimp; have := j.isLt; omega) : j = ⟨n' + 2, by omega⟩), h1.2.2, h2.2.2, congrFun heq ⟨n', by omega⟩]
  · let v : Fin (n' + 3) → F := fun j =>
      if hlt : j.val < n' + 1 then w ⟨j.val, hlt⟩
      else if j.val = n' + 1 then 0
      else b * w ⟨n', by omega⟩
    have hvw : (fun j : Fin (n' + 1) => v ⟨j.val, by omega⟩) = w := by
      funext j; dsimp only [v]; rw [dif_pos j.isLt]
    refine ⟨v, Finset.mem_filter.2 ⟨Finset.mem_univ _, (hker_iff v).2 ⟨?_, ?_, ?_⟩⟩, hvw⟩
    · rw [hvw]; exact (Finset.mem_filter.1 hw).2
    · simp [v]
    · simp [v]

private lemma lin_pairs_step_mem (n' : ℕ) (A : Finset (Fin (n' + 2)))
    (hlast : (⟨n' + 1, by omega⟩ : Fin (n' + 2)) ∈ A)
    (m : ℕ)
    (P' Q' : Fin m → (Fin (n' + 1) → F) →ₗ[F] F)
    (hq' : ∀ w : Fin (n' + 1) → F,
      qLin n' (Finset.univ.filter (fun i : Fin n' => (⟨i.val, by omega⟩ : Fin (n' + 2)) ∈ A)) w =
        ∑ j : Fin m, P' j w * Q' j w) :
    ∃ (P Q : Fin (m + 1) → (Fin (n' + 3) → F) →ₗ[F] F),
      ∀ v : Fin (n' + 3) → F, qLin (n' + 2) A v = ∑ j : Fin (m + 1), P j v * Q j v := by
  let last : Fin (n' + 2) := ⟨n' + 1, by omega⟩
  let prevLast : Fin (n' + 2) := ⟨n', by omega⟩
  let emb : Fin n' → Fin (n' + 2) := fun i => ⟨i.val, by omega⟩
  have hemb_inj : Function.Injective emb :=
    fun a b h => Fin.ext (by simpa [emb] using congrArg Fin.val h)
  let A' : Finset (Fin n') := Finset.univ.filter (fun i : Fin n' => emb i ∈ A)
  let b : F := if prevLast ∈ A then 1 else 0
  let proj : (Fin (n' + 3) → F) →ₗ[F] (Fin (n' + 1) → F) := {
    toFun := fun v j => v ⟨j.val, by omega⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
  }
  let P_new : (Fin (n' + 3) → F) →ₗ[F] F := LinearMap.proj (⟨n' + 1, by omega⟩ : Fin (n' + 3))
  let Q_new : (Fin (n' + 3) → F) →ₗ[F] F :=
    LinearMap.proj (⟨n' + 2, by omega⟩ : Fin (n' + 3)) +
      b • LinearMap.proj (⟨n', by omega⟩ : Fin (n' + 3))
  let P : Fin (m + 1) → (Fin (n' + 3) → F) →ₗ[F] F := fun j =>
    if hj : j.val < m then (P' ⟨j.val, hj⟩).comp proj else P_new
  let Q : Fin (m + 1) → (Fin (n' + 3) → F) →ₗ[F] F := fun j =>
    if hj : j.val < m then (Q' ⟨j.val, hj⟩).comp proj else Q_new
  refine ⟨P, Q, fun v => ?_⟩
  rw [Fin.sum_univ_castSucc]
  have h1 : (∑ j : Fin m, P j.castSucc v * Q j.castSucc v) = qLin n' A' (proj v) := by
    rw [hq' (proj v)]
    refine Finset.sum_congr rfl fun j _ => by simp [P, Q, j.isLt]
  have h2 : P (Fin.last m) v * Q (Fin.last m) v = P_new v * Q_new v := by simp [P, Q]
  rw [h1, h2]
  have hA_eq : A = A'.image emb ∪ (if prevLast ∈ A then {prevLast, last} else {last}) := by
    ext i
    simp only [Finset.mem_union, Finset.mem_image]
    by_cases hlt : i.val < n'
    · have hne1 : i ≠ last := fun h => by have := congrArg Fin.val h; dsimp [last] at this; omega
      have hne2 : i ≠ prevLast := fun h => by have := congrArg Fin.val h; dsimp [prevLast] at this; omega
      have hr : i ∉ (if prevLast ∈ A then ({prevLast, last} : Finset (Fin (n' + 2))) else {last}) := by
        split_ifs <;> simp [hne1, hne2]
      simp only [hr, or_false]
      constructor
      · intro hi; exact ⟨⟨i.val, hlt⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩, Fin.ext rfl⟩
      · rintro ⟨j, hj, rfl⟩; exact (Finset.mem_filter.1 hj).2
    · have hl : ¬ ∃ j ∈ A', emb j = i := by
        rintro ⟨j, _, rfl⟩; dsimp [emb] at hlt; omega
      simp only [hl, false_or]
      by_cases hil : i = last
      · rw [hil]; split_ifs <;> simp [last, hlast]
      · have hip : i = prevLast := Fin.ext (by have := i.isLt; have hne : i.val ≠ last.val := fun h => hil (Fin.ext h); dsimp [prevLast, last] at *; omega)
        rw [hip]; split_ifs with hp <;> simp [hp, prevLast, last]
  have hdisj : Disjoint (A'.image emb) (if prevLast ∈ A then {prevLast, last} else {last}) := by
    rw [Finset.disjoint_left]
    intro i hi htail
    rcases Finset.mem_image.1 hi with ⟨j, _, rfl⟩
    split_ifs at htail with hp
    · rcases Finset.mem_insert.1 htail with h | h
      · have := congrArg Fin.val h; dsimp [emb, prevLast] at this; omega
      · have := congrArg Fin.val (Finset.mem_singleton.1 h); dsimp [emb, last] at this; omega
    · have := congrArg Fin.val (Finset.mem_singleton.1 htail); dsimp [emb, last] at this; omega
  dsimp only [qLin]
  rw [hA_eq, Finset.sum_union hdisj, Finset.sum_image (fun _ _ _ _ h => hemb_inj h)]
  congr 1
  have hne : prevLast ≠ last := fun h => by have := congrArg Fin.val h; dsimp [prevLast, last] at this; omega
  dsimp only [P_new, Q_new, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul, b]
  split_ifs with hp
  · rw [Finset.sum_pair hne]
    change v ⟨n', by omega⟩ * v ⟨n' + 1, by omega⟩ + v ⟨n' + 1, by omega⟩ * v ⟨n' + 2, by omega⟩ =
      v ⟨n' + 1, by omega⟩ * (v ⟨n' + 2, by omega⟩ + 1 * v ⟨n', by omega⟩)
    ring
  · rw [Finset.sum_singleton]
    change v ⟨n' + 1, by omega⟩ * v ⟨n' + 2, by omega⟩ =
      v ⟨n' + 1, by omega⟩ * (v ⟨n' + 2, by omega⟩ + 0 * v ⟨n', by omega⟩)
    ring

private lemma lin_mu_step_not_mem (m : ℕ) (A : Finset (Fin (m + 1)))
    (hlast : (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) ∉ A) :
    let A' : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => i.castSucc ∈ A)
    muLin (m + 1) A = muLin m A' := by
  intro A'
  let last : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
  apply le_antisymm
  · apply Finset.sup_le
    intro E hE
    rw [Finset.mem_filter, Finset.mem_powerset] at hE
    rcases hE with ⟨hEA, hEind⟩
    let E' : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => i.castSucc ∈ E)
    have hE'mem : E' ∈ A'.powerset.filter (isIndepLin m) := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨fun i hi => Finset.mem_filter.2 ⟨Finset.mem_univ _, hEA (Finset.mem_filter.1 hi).2⟩,
        fun i hi hlt hmem => ?_⟩
      exact hEind i.castSucc (Finset.mem_filter.1 hi).2 (Nat.succ_lt_succ i.isLt) (Finset.mem_filter.1 hmem).2
    have hEeq : E = E'.image Fin.castSucc := by
      ext i
      simp only [Finset.mem_image, E', Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hi
        have hne : i.val ≠ m := fun h => hlast ((Fin.ext h : i = ⟨m, Nat.lt_succ_self m⟩) ▸ hEA hi)
        exact ⟨⟨i.val, by have := i.isLt; omega⟩, hi, Fin.ext rfl⟩
      · rintro ⟨j, hj, rfl⟩; exact hj
    rw [hEeq, Finset.card_image_of_injective _ (Fin.castSucc_injective m)]
    exact Finset.le_sup (f := Finset.card) hE'mem
  · apply Finset.sup_le
    intro E' hE'
    rw [Finset.mem_filter, Finset.mem_powerset] at hE'
    rcases hE' with ⟨hE'A', hE'ind⟩
    let E := E'.image Fin.castSucc
    have hEmem : E ∈ A.powerset.filter (isIndepLin (m + 1)) := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨?_, ?_⟩
      · intro i hi
        rcases Finset.mem_image.1 hi with ⟨j, hj, rfl⟩
        exact (Finset.mem_filter.1 (hE'A' hj)).2
      · intro i hi hlt hnext
        rcases Finset.mem_image.1 hi with ⟨j, hj, rfl⟩
        rcases Finset.mem_image.1 hnext with ⟨j2, hj2, hjeq⟩
        have hjval : j2.val = j.val + 1 := by
          have := congrArg Fin.val hjeq; simpa using this
        have hlt' : j.val + 1 < m := by omega
        exact hE'ind j hj hlt' ((Fin.ext hjval.symm : (⟨j.val + 1, hlt'⟩ : Fin m) = j2) ▸ hj2)
    rw [← Finset.card_image_of_injective E' (Fin.castSucc_injective m)]
    exact Finset.le_sup (f := Finset.card) hEmem

private lemma lin_ker_step_not_mem (m : ℕ) (A : Finset (Fin (m + 1)))
    (hlast : (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) ∉ A) :
    let A' : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => i.castSucc ∈ A)
    (Finset.univ.filter (fun v : Fin (m + 2) → F => MLin (m + 1) A v = 0)).card =
      2 * (Finset.univ.filter (fun w : Fin (m + 1) → F => MLin m A' w = 0)).card := by
  intro A'
  let last : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
  have hmem_iff : ∀ (j : ℕ) (hjm : j < m),
      ((⟨j, by omega⟩ : Fin (m + 1)) ∈ A) ↔ ((⟨j, hjm⟩ : Fin m) ∈ A') := by
    intro j hjm; simp [A', Fin.castSucc]
  have hrow_le : ∀ (v : Fin (m + 2) → F) (j : Fin (m + 1)),
      MLin (m + 1) A v j.castSucc = MLin m A' (fun t : Fin (m + 1) => v t.castSucc) j := by
    intro v j
    dsimp only [MLin, Fin.val_castSucc]
    congr 1
    · by_cases hjm : j.val < m
      · have h1a : j.val < m + 1 := by omega
        simp only [hjm, h1a, ↓reduceDIte]
        by_cases hm : (⟨j.val, hjm⟩ : Fin m) ∈ A'
        · simp [hm, (hmem_iff j.val hjm).2 hm]
        · simp [hm, mt (hmem_iff j.val hjm).1 hm]
      · have h1a : j.val < m + 1 := by omega
        simp only [hjm, h1a, ↓reduceDIte]
        have hnotm : (⟨j.val, h1a⟩ : Fin (m + 1)) ∉ A := by
          have : (⟨j.val, h1a⟩ : Fin (m + 1)) = last := Fin.ext (by dsimp [last]; omega)
          rw [this]; exact hlast
        simp [hnotm]
    · by_cases h2 : 0 < j.val
      · simp only [h2, ↓reduceDIte]
        have hjm' : j.val - 1 < m := by omega
        by_cases hm : (⟨j.val - 1, hjm'⟩ : Fin m) ∈ A'
        · simp [hm, (hmem_iff (j.val - 1) hjm').2 hm]
        · simp [hm, mt (hmem_iff (j.val - 1) hjm').1 hm]
      · simp [h2]
  have hker_iff : ∀ v : Fin (m + 2) → F,
      MLin (m + 1) A v = 0 ↔ MLin m A' (fun j : Fin (m + 1) => v j.castSucc) = 0 := by
    intro v
    constructor
    · intro hv; funext j; rw [← hrow_le v j, hv]; rfl
    · intro hw
      funext j
      simp only [Pi.zero_apply]
      by_cases hlt : j.val < m + 1
      · have h := hrow_le v ⟨j.val, hlt⟩
        have heq : (⟨j.val, hlt⟩ : Fin (m + 1)).castSucc = j := Fin.ext rfl
        rw [heq] at h
        rw [h, hw]; rfl
      · have heq : j = Fin.last (m + 1) := Fin.ext (by dsimp [Fin.last]; have := j.isLt; omega)
        rw [heq]; dsimp only [MLin]
        have h1 : ¬ ((Fin.last (m + 1)).val < m + 1) := by simp
        have h2 : 0 < (Fin.last (m + 1)).val := by simp
        simp only [h1, h2, ↓reduceDIte, zero_add]
        have hnotm : (⟨(Fin.last (m + 1)).val - 1, by simp⟩ : Fin (m + 1)) ∉ A := by
          have : (⟨(Fin.last (m + 1)).val - 1, by simp⟩ : Fin (m + 1)) = last := Fin.ext (by simp [last])
          rw [this]; exact hlast
        rw [if_neg hnotm]
  have hcard_eq :
      (Finset.univ.filter (fun v : Fin (m + 2) → F => MLin (m + 1) A v = 0)).card =
      ((Finset.univ.filter (fun w : Fin (m + 1) → F => MLin m A' w = 0)) ×ˢ
        (Finset.univ : Finset F)).card := by
    refine Finset.card_bij
      (fun v _ => (fun j : Fin (m + 1) => v j.castSucc, v (Fin.last (m + 1))))
      (fun v hv => Finset.mem_product.2
        ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, (hker_iff v).1 (Finset.mem_filter.1 hv).2⟩, Finset.mem_univ _⟩)
      (fun v1 _ v2 _ heq => by
        funext j
        by_cases hlt : j.val < m + 1
        · exact congrFun (congrArg Prod.fst heq) ⟨j.val, hlt⟩
        · rw [(Fin.ext (by dsimp [Fin.last]; have := j.isLt; omega) : j = Fin.last (m + 1))]; exact congrArg Prod.snd heq)
      (fun p hp => by
        rcases p with ⟨w, b⟩
        rw [Finset.mem_product, Finset.mem_filter] at hp
        let v : Fin (m + 2) → F := fun j => if hlt : j.val < m + 1 then w ⟨j.val, hlt⟩ else b
        have hvw : (fun j : Fin (m + 1) => v j.castSucc) = w := by funext j; dsimp only [v]; simp only [Fin.val_castSucc]; rw [dif_pos j.isLt]
        refine ⟨v, Finset.mem_filter.2 ⟨Finset.mem_univ _, (hker_iff v).2 (by rw [hvw]; exact hp.1.2)⟩,
          Prod.ext hvw (by simp [v])⟩)
  rw [hcard_eq, Finset.card_product, Finset.card_univ, ZMod.card, mul_comm]

private lemma lin_main : ∀ (n : ℕ) (A : Finset (Fin n)),
    2 * muLin n A ≤ n + 1 ∧
    (Finset.univ.filter (fun v : Fin (n + 1) → F => MLin n A v = 0)).card =
      2 ^ (n + 1 - 2 * muLin n A) ∧
    ∃ (P Q : Fin (muLin n A) → (Fin (n + 1) → F) →ₗ[F] F),
      ∀ v : Fin (n + 1) → F, qLin n A v = ∑ j : Fin (muLin n A), P j v * Q j v := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro A
    cases n with
    | zero =>
      have hA : A = ∅ := Finset.eq_empty_of_isEmpty A
      have hmu : muLin 0 A = 0 := by dsimp [muLin]; rw [hA]; simp
      refine ⟨by omega, ?_, ?_⟩
      · rw [hmu]
        have hflt : Finset.univ.filter (fun v : Fin 1 → F => MLin 0 A v = 0) = Finset.univ := by
          ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          funext j; simp [MLin]
        rw [hflt, card_finset_univ_vec]
      · let P0 : Fin (muLin 0 A) → (Fin 1 → F) →ₗ[F] F := fun j => (hmu ▸ j).elim0
        refine ⟨P0, P0, fun v => ?_⟩
        have hsum0 : (∑ j : Fin (muLin 0 A), P0 j v * P0 j v) = 0 := by
          haveI : IsEmpty (Fin (muLin 0 A)) := by rw [hmu]; infer_instance
          simp
        rw [hsum0, hA]; simp [qLin]
    | succ m =>
      let last : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
      by_cases hlast : last ∈ A
      · cases m with
        | zero =>
          have hA : A = {last} := by
            ext i; simp only [Finset.mem_singleton]
            rw [(Fin.ext (by have := i.isLt; dsimp [last]; omega) : i = last)]; simp [hlast]
          have hmu : muLin 1 A = 1 := by
            apply le_antisymm
            · apply Finset.sup_le; intro E hE
              calc E.card ≤ A.card := Finset.card_le_card (Finset.mem_powerset.1 (Finset.mem_filter.1 hE).1)
                _ = 1 := by rw [hA]; simp
            · have hmem : ({last} : Finset (Fin 1)) ∈ A.powerset.filter (isIndepLin 1) := by
                rw [Finset.mem_filter, Finset.mem_powerset, hA]
                exact ⟨Finset.Subset.refl _, fun i _ hlt => by omega⟩
              have hle := Finset.le_sup (f := Finset.card) hmem
              simpa [muLin] using hle
          refine ⟨by change 2 * muLin 1 A ≤ 1 + 1; rw [hmu], ?_, ?_⟩
          · change (Finset.univ.filter (fun v : Fin 2 → F => MLin 1 A v = 0)).card = 2 ^ (1 + 1 - 2 * muLin 1 A)
            rw [hmu]
            have hflt : Finset.univ.filter (fun v : Fin 2 → F => MLin 1 A v = 0) = {0} := by
              ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
              constructor
              · intro hv; funext j; fin_cases j
                · simpa [MLin, hA, last] using congrFun hv ⟨1, by omega⟩
                · simpa [MLin, hA, last] using congrFun hv ⟨0, by omega⟩
              · rintro rfl; funext j; fin_cases j <;> simp [MLin, hA, last]
            rw [hflt]; simp
          · refine ⟨fun _ => LinearMap.proj (⟨0, by omega⟩ : Fin 2),
                    fun _ => LinearMap.proj (⟨1, by omega⟩ : Fin 2), fun v => ?_⟩
            simp only [LinearMap.proj_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin, hmu, one_smul]
            rw [hA]; simp [qLin, last]
        | succ n' =>
          let A' : Finset (Fin n') := Finset.univ.filter (fun i : Fin n' => (⟨i.val, by omega⟩ : Fin (n' + 2)) ∈ A)
          have hmu : muLin (n' + 1 + 1) A = muLin n' A' + 1 := lin_mu_step_mem n' A hlast
          have hker_step : (Finset.univ.filter (fun v : Fin (n' + 1 + 1 + 1) → F => MLin (n' + 1 + 1) A v = 0)).card =
              (Finset.univ.filter (fun w : Fin (n' + 1) → F => MLin n' A' w = 0)).card := lin_ker_step_mem n' A hlast
          obtain ⟨h2le, hker', P', Q', hq'⟩ := ih n' (by omega) A'
          obtain ⟨P, Q, hq⟩ := lin_pairs_step_mem n' A hlast (muLin n' A') P' Q' hq'
          refine ⟨by omega, ?_, ?_⟩
          · rw [hker_step, hker', hmu]; congr 1; omega
          · refine ⟨fun j => P ⟨j.val, by have := j.isLt; omega⟩, fun j => Q ⟨j.val, by have := j.isLt; omega⟩, fun v => ?_⟩
            rw [hq v]
            symm
            refine Finset.sum_bij (fun j _ => ⟨j.val, by have := j.isLt; omega⟩)
              (fun _ _ => Finset.mem_univ _)
              (fun a _ b _ h => Fin.ext (by simpa using congrArg Fin.val h))
              (fun j _ => ⟨⟨j.val, by have := j.isLt; omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
              (fun _ _ => rfl)
      · let A' : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => i.castSucc ∈ A)
        have hmu : muLin (m + 1) A = muLin m A' := lin_mu_step_not_mem m A hlast
        have hker_step : (Finset.univ.filter (fun v : Fin (m + 2) → F => MLin (m + 1) A v = 0)).card =
            2 * (Finset.univ.filter (fun w : Fin (m + 1) → F => MLin m A' w = 0)).card := lin_ker_step_not_mem m A hlast
        obtain ⟨h2le, hker', P', Q', hq'⟩ := ih m (by omega) A'
        refine ⟨by omega, ?_, ?_⟩
        · rw [hker_step, hker', hmu]
          have hexp : m + 2 - 2 * muLin m A' = (m + 1 - 2 * muLin m A') + 1 := by omega
          rw [hexp, pow_succ, mul_comm]
        · let proj : (Fin (m + 2) → F) →ₗ[F] (Fin (m + 1) → F) := {
            toFun := fun v j => v j.castSucc
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl
          }
          refine ⟨fun j => (P' ⟨j.val, by have := j.isLt; omega⟩).comp proj,
                  fun j => (Q' ⟨j.val, by have := j.isLt; omega⟩).comp proj, fun v => ?_⟩
          have hAeq : A = A'.image Fin.castSucc := by
            ext i; simp only [Finset.mem_image, A', Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · intro hi
              have hne : i.val ≠ m := fun h => hlast ((Fin.ext h : i = last) ▸ hi)
              exact ⟨⟨i.val, by have := i.isLt; omega⟩, hi, Fin.ext rfl⟩
            · rintro ⟨j, hj, rfl⟩; exact hj
          simp only [LinearMap.comp_apply]
          have hsum_eq :
              (∑ j : Fin (muLin (m + 1) A), P' ⟨j.val, by have := j.isLt; omega⟩ (proj v) * Q' ⟨j.val, by have := j.isLt; omega⟩ (proj v)) =
              ∑ j : Fin (muLin m A'), P' j (proj v) * Q' j (proj v) := by
            refine Finset.sum_bij (fun j _ => ⟨j.val, by have := j.isLt; omega⟩)
              (fun _ _ => Finset.mem_univ _)
              (fun a _ b _ h => Fin.ext (by simpa using congrArg Fin.val h))
              (fun j _ => ⟨⟨j.val, by have := j.isLt; omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
              (fun _ _ => rfl)
          rw [hsum_eq, ← hq' (proj v)]
          dsimp only [qLin]
          rw [hAeq, Finset.sum_image (fun _ _ _ _ h => Fin.castSucc_injective m h)]
          refine Finset.sum_congr rfl fun _ _ => rfl

-- Section 3b: Cycle main theorem (modular helpers)

private def isIndepCyc (k : ℕ) (hk : 0 < k) (E : Finset (Fin k)) : Prop :=
  ∀ i ∈ E, ix k hk (i.val + 1) ∉ E

private noncomputable def muCyc (k : ℕ) (hk : 0 < k) (S : Finset (Fin k)) : ℕ :=
  (S.powerset.filter (isIndepCyc k hk)).sup Finset.card

private noncomputable def pCyc (k : ℕ) (hk : 0 < k) (S : Finset (Fin k)) : ℕ :=
  if S = Finset.univ ∧ k % 2 = 0 then muCyc k hk S - 1 else muCyc k hk S

private lemma muCyc_univ_eq (k : ℕ) (hk : 0 < k) (hk2 : 2 ≤ k) :
    muCyc k hk Finset.univ = k / 2 := by
  apply le_antisymm
  · apply Finset.sup_le
    intro E hE
    rw [Finset.mem_filter] at hE
    have hdisj : Disjoint E (E.image (fun i : Fin k => ix k hk (i.val + 1))) := by
      rw [Finset.disjoint_right]
      intro y hy
      rcases Finset.mem_image.1 hy with ⟨i, hi, rfl⟩
      exact hE.2 i hi
    have hcard : E.card + (E.image (fun i : Fin k => ix k hk (i.val + 1))).card ≤ k := by
      rw [← Finset.card_union_of_disjoint hdisj]
      calc (E ∪ E.image (fun i : Fin k => ix k hk (i.val + 1))).card
          ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_univ _
        _ = k := by simp
    rw [Finset.card_image_of_injective _ (ix_next_injective k hk)] at hcard
    omega
  · let f : Fin (k / 2) → Fin k := fun t => ⟨2 * t.val, by omega⟩
    have hf_inj : Function.Injective f := fun a b h => Fin.ext (by have := congrArg Fin.val h; dsimp [f] at this; omega)
    let E : Finset (Fin k) := Finset.univ.image f
    have hEmem : E ∈ (Finset.univ : Finset (Fin k)).powerset.filter (isIndepCyc k hk) := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.subset_univ _, fun i hi hnext => ?_⟩
      rcases Finset.mem_image.1 hi with ⟨t1, _, rfl⟩
      rcases Finset.mem_image.1 hnext with ⟨t2, _, ht2⟩
      have hval := congrArg Fin.val ht2
      dsimp [f, ix] at hval
      rw [Nat.mod_eq_of_lt (by omega)] at hval
      omega
    have hEcard : E.card = k / 2 := by
      rw [Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_fin]
    rw [← hEcard]
    exact Finset.le_sup (f := Finset.card) hEmem

private lemma cycle_ker_per2 (k : ℕ) (hk : 0 < k) (hk3 : 3 ≤ k) (v : Fin k → F) :
    MS_lin k hk Finset.univ v = 0 ↔ ∀ j : Fin k, v (ix k hk (j.val + 2)) = v j := by
  constructor
  · intro hv j
    have h := congrFun hv (ix k hk (j.val + 1))
    change (if ix k hk (j.val + 1) ∈ Finset.univ then v (ix k hk ((ix k hk (j.val + 1)).val + 1)) else 0) +
      (if ix k hk ((ix k hk (j.val + 1)).val + k - 1 % k) ∈ Finset.univ then
        v (ix k hk ((ix k hk (j.val + 1)).val + k - 1 % k)) else 0) = 0 at h
    simp only [Finset.mem_univ, ↓reduceIte, ix_add_ix, ix_add_sub] at h
    exact (z2_add_eq_zero_iff _ _).1 h
  · intro hper
    funext j
    change (if j ∈ Finset.univ then v (ix k hk (j.val + 1)) else 0) +
      (if ix k hk (j.val + k - 1 % k) ∈ Finset.univ then v (ix k hk (j.val + k - 1 % k)) else 0) = 0
    simp only [Finset.mem_univ, ↓reduceIte]
    have h2 := hper (ix k hk (j.val + k - 1 % k))
    rw [ix_add_ix] at h2
    have h1m : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
    have heq : j.val + k - 1 % k + 2 = (j.val + 1) + 1 * k := by omega
    rw [heq, ix_add_mul_k] at h2
    rw [h2, z2_add_self]

private lemma per2_mul (k : ℕ) (hk : 0 < k) (v : Fin k → F)
    (hper : ∀ j : Fin k, v (ix k hk (j.val + 2)) = v j) :
    ∀ (m : ℕ) (j : Fin k), v (ix k hk (j.val + 2 * m)) = v j := by
  intro m
  induction m with
  | zero => intro j; simp [ix_val_eq]
  | succ m ih =>
    intro j
    have heq : j.val + 2 * (m + 1) = (j.val + 2 * m) + 2 := by ring
    rw [heq, ← ix_add_ix, hper, ih]

private lemma cycle_even_main (k : ℕ) (hk : 0 < k) (hk4 : 4 ≤ k) (hpar : k % 2 = 0) :
    let p := k / 2 - 1
    (Finset.univ.filter (fun v : Fin k → F => MS_lin k hk Finset.univ v = 0)).card = 2 ^ (k - 2 * p) ∧
    ∃ (A B : Fin p → (Fin k → F) →ₗ[F] F) (L : (Fin k → F) →ₗ[F] F) (e : F),
      ∀ v : Fin k → F, qS k hk Finset.univ v = L v + e + ∑ j : Fin p, A j v * B j v := by
  intro p
  have h2dvd : 2 ∣ k := Nat.dvd_of_mod_eq_zero hpar
  constructor
  · have hker_iff : ∀ v : Fin k → F,
        MS_lin k hk Finset.univ v = 0 ↔
          ∀ j : Fin k, v j = if j.val % 2 = 0 then v ⟨0, hk⟩ else v ⟨1, by omega⟩ := by
      intro v
      rw [cycle_ker_per2 k hk (by omega)]
      constructor
      · intro hper j
        by_cases hj : j.val % 2 = 0
        · simp only [hj, ↓reduceIte]
          have hm := per2_mul k hk v hper (j.val / 2) ⟨0, hk⟩
          have heq : (0 : ℕ) + 2 * (j.val / 2) = j.val := by omega
          rw [heq, ix_val_eq] at hm; exact hm
        · simp only [hj, ↓reduceIte]
          have hm := per2_mul k hk v hper (j.val / 2) ⟨1, by omega⟩
          have heq : (1 : ℕ) + 2 * (j.val / 2) = j.val := by omega
          rw [heq, ix_val_eq] at hm; exact hm
      · intro hval j
        rw [hval (ix k hk (j.val + 2)), hval j]
        have hmod : (ix k hk (j.val + 2)).val % 2 = j.val % 2 := by
          dsimp [ix]; rw [Nat.mod_mod_of_dvd _ h2dvd]; omega
        rw [hmod]
    have hcard_eq :
        (Finset.univ.filter (fun v : Fin k → F => MS_lin k hk Finset.univ v = 0)).card =
        (Finset.univ : Finset (F × F)).card := by
      refine Finset.card_bij
        (fun v _ => (v ⟨0, hk⟩, v ⟨1, by omega⟩))
        (fun _ _ => Finset.mem_univ _)
        (fun v1 hv1 v2 hv2 heq => by
          funext j
          have ha : v1 ⟨0, hk⟩ = v2 ⟨0, hk⟩ := congrArg Prod.fst heq
          have hb : v1 ⟨1, by omega⟩ = v2 ⟨1, by omega⟩ := congrArg Prod.snd heq
          rw [(hker_iff v1).1 (Finset.mem_filter.1 hv1).2 j,
              (hker_iff v2).1 (Finset.mem_filter.1 hv2).2 j, ha, hb])
        (fun ab _ => ⟨fun j => if j.val % 2 = 0 then ab.1 else ab.2,
          Finset.mem_filter.2 ⟨Finset.mem_univ _, (hker_iff _).2 (fun j => by simp)⟩,
          Prod.ext (by simp) (by simp)⟩)
    rw [hcard_eq, Finset.card_univ, Fintype.card_prod, ZMod.card]
    have hexp : k - 2 * p = 2 := by omega
    rw [hexp]; decide
  · let wLin (i : Fin k) : (Fin k → F) →ₗ[F] F :=
      LinearMap.proj i +
        if i.val % 2 = 0 then (LinearMap.proj (⟨0, hk⟩ : Fin k) : (Fin k → F) →ₗ[F] F) else LinearMap.proj (⟨1, by omega⟩ : Fin k)
    let A : Fin p → (Fin k → F) →ₗ[F] F := fun j => wLin ⟨2 * j.val + 3, by omega⟩
    let B : Fin p → (Fin k → F) →ₗ[F] F := fun j =>
      wLin ⟨2 * j.val + 2, by omega⟩ +
        if h : 2 * j.val + 4 < k then wLin ⟨2 * j.val + 4, h⟩ else 0
    refine ⟨A, B, 0, 0, fun v => ?_⟩
    simp only [LinearMap.zero_apply, zero_add]
    let cpar : Fin k → F := fun i => if i.val % 2 = 0 then v ⟨0, hk⟩ else v ⟨1, by omega⟩
    let w : Fin k → F := fun i => v i + cpar i
    have hw_eq : ∀ i : Fin k, wLin i v = w i := fun i => by dsimp [wLin, w, cpar]; split_ifs <;> rfl
    have hcpar_next : ∀ i : Fin k, cpar (ix k hk (i.val + 1)) =
        if i.val % 2 = 0 then v ⟨1, by omega⟩ else v ⟨0, hk⟩ := by
      intro i; dsimp [cpar, ix]
      rw [Nat.mod_mod_of_dvd _ h2dvd]
      by_cases h : i.val % 2 = 0
      · have h1 : (i.val + 1) % 2 ≠ 0 := by omega
        simp [h, h1]
      · have h1 : (i.val + 1) % 2 = 0 := by omega
        simp [h, h1]
    have hq_eq_w : qS k hk Finset.univ v = ∑ i : Fin k, w i * w (ix k hk (i.val + 1)) := by
      have hexp : ∀ i : Fin k,
          w i * w (ix k hk (i.val + 1)) =
            v i * v (ix k hk (i.val + 1)) +
            v i * cpar (ix k hk (i.val + 1)) +
            cpar i * v (ix k hk (i.val + 1)) +
            v ⟨0, hk⟩ * v ⟨1, by omega⟩ := by
        intro i; dsimp only [w]
        have hprod : cpar i * cpar (ix k hk (i.val + 1)) = v ⟨0, hk⟩ * v ⟨1, by omega⟩ := by
          rw [hcpar_next]; dsimp only [cpar]; split_ifs
          · rfl
          · exact mul_comm _ _
        calc (v i + cpar i) * (v (ix k hk (i.val + 1)) + cpar (ix k hk (i.val + 1)))
            = v i * v (ix k hk (i.val + 1)) + v i * cpar (ix k hk (i.val + 1)) +
              cpar i * v (ix k hk (i.val + 1)) + cpar i * cpar (ix k hk (i.val + 1)) := by ring
          _ = _ := by rw [hprod]
      simp only [hexp, Finset.sum_add_distrib]
      have hconst : (∑ _i : Fin k, v ⟨0, hk⟩ * v ⟨1, by omega⟩) = 0 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hk0 : (k : F) = 0 := (ZMod.natCast_eq_zero_iff k 2).2 h2dvd
        rw [hk0, zero_mul]
      have hcross : (∑ i : Fin k, v i * cpar (ix k hk (i.val + 1))) =
          (∑ i : Fin k, cpar i * v (ix k hk (i.val + 1))) := by
        refine Finset.sum_bij (fun i _ => ix k hk (i.val + k - 1 % k))
          (fun _ _ => Finset.mem_univ _)
          (fun a _ b _ h => by
            have ha := ix_sub_add k hk a 1; have hb := ix_sub_add k hk b 1; rw [← ha, ← hb, h])
          (fun y _ => ⟨ix k hk (y.val + 1), Finset.mem_univ _, ix_add_sub k hk y 1⟩)
          (fun i _ => ?_)
        rw [ix_sub_add, mul_comm]; congr 1
        rw [hcpar_next]; dsimp [cpar, ix]
        have h1m : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
        rw [h1m, Nat.mod_mod_of_dvd _ h2dvd]
        by_cases h : i.val % 2 = 0
        · have h1 : (i.val + k - 1) % 2 ≠ 0 := by omega
          simp [h, h1]
        · have h1 : (i.val + k - 1) % 2 = 0 := by omega
          simp [h, h1]
      rw [hconst, add_zero, hcross, add_assoc, z2_add_self, add_zero]; rfl
    rw [hq_eq_w]
    have hw0 : w ⟨0, hk⟩ = 0 := by simp [w, cpar, z2_add_self]
    have hw1 : w ⟨1, by omega⟩ = 0 := by simp [w, cpar, z2_add_self]
    have hrhs : (∑ j : Fin p, A j v * B j v) =
        (∑ j : Fin p, w ⟨2 * j.val + 2, by omega⟩ * w ⟨2 * j.val + 3, by omega⟩) +
        (∑ j : Fin p, if h : 2 * j.val + 4 < k then
          w ⟨2 * j.val + 3, by omega⟩ * w ⟨2 * j.val + 4, h⟩ else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      dsimp only [A, B, LinearMap.add_apply]; rw [hw_eq, hw_eq]
      split_ifs with h
      · rw [hw_eq]; ring
      · rw [LinearMap.zero_apply, add_zero, add_zero, mul_comm]
    rw [hrhs]
    let f_w : Fin k → F := fun i => w i * w (ix k hk (i.val + 1))
    have hterm_zero : ∀ i : Fin k, (i.val < 2 ∨ i.val = k - 1) → f_w i = 0 := by
      intro i hi; dsimp only [f_w]
      rcases hi with hlt | hlast
      · by_cases h0 : i.val = 0
        · rw [(Fin.ext h0 : i = ⟨0, hk⟩), hw0, zero_mul]
        · rw [(Fin.ext (by dsimp; omega) : i = ⟨1, by omega⟩), hw1, zero_mul]
      · have hnext : ix k hk (i.val + 1) = ⟨0, hk⟩ := by
          apply Fin.ext; change (i.val + 1) % k = 0; rw [show i.val + 1 = k by omega, Nat.mod_self]
        rw [hnext, hw0, mul_zero]
    have hlhs_split :
        (∑ i : Fin k, f_w i) =
          (∑ i ∈ Finset.univ.filter (fun i : Fin k => 2 ≤ i.val ∧ i.val < k - 1 ∧ i.val % 2 = 0), f_w i) +
          (∑ i ∈ Finset.univ.filter (fun i : Fin k => 2 ≤ i.val ∧ i.val < k - 1 ∧ i.val % 2 ≠ 0), f_w i) := by
      rw [← Finset.sum_union]
      · symm; refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact hterm_zero i (by omega)
      · rw [Finset.disjoint_left]; intro i h1 h2; simp only [Finset.mem_filter] at h1 h2; exact h2.2.2.2 h1.2.2.2
    rw [hlhs_split]
    congr 1
    · symm
      refine Finset.sum_bij (fun j _ => (⟨2 * j.val + 2, by omega⟩ : Fin k))
        (fun j _ => by simp; omega)
        (fun a _ b _ h => Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega))
        (fun i hi => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          exact ⟨⟨(i.val - 2) / 2, by omega⟩, Finset.mem_univ _, Fin.ext (by dsimp; omega)⟩)
        (fun j _ => by
          dsimp only [f_w]
          have hnext : ix k hk (2 * j.val + 2 + 1) = ⟨2 * j.val + 3, by omega⟩ :=
            Fin.ext (by dsimp [ix]; exact Nat.mod_eq_of_lt (by omega))
          rw [hnext])
    · symm
      have hfilt_eq : (∑ j : Fin p, if h : 2 * j.val + 4 < k then
          w ⟨2 * j.val + 3, by omega⟩ * w ⟨2 * j.val + 4, h⟩ else 0) =
          ∑ j ∈ Finset.univ.filter (fun j : Fin p => 2 * j.val + 4 < k),
            if h : 2 * j.val + 4 < k then w ⟨2 * j.val + 3, by omega⟩ * w ⟨2 * j.val + 4, h⟩ else 0 := by
        symm; refine Finset.sum_subset (Finset.filter_subset _ _) fun j _ hj => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        exact dif_neg hj
      rw [hfilt_eq]
      refine Finset.sum_bij (fun j _ => (⟨2 * j.val + 3, by omega⟩ : Fin k))
        (fun j hj => by rw [Finset.mem_filter] at hj ⊢; exact ⟨Finset.mem_univ _, by dsimp; omega, by dsimp; omega, by dsimp; omega⟩)
        (fun a _ b _ h => Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega))
        (fun i hi => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          exact ⟨⟨(i.val - 3) / 2, by omega⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, by dsimp; omega⟩, Fin.ext (by dsimp; omega)⟩)
        (fun j hj => by
          have hj' := (Finset.mem_filter.1 hj).2
          rw [dif_pos hj']
          dsimp only [f_w]
          have hnext : ix k hk (2 * j.val + 3 + 1) = ⟨2 * j.val + 4, hj'⟩ :=
            Fin.ext (by dsimp [ix]; exact Nat.mod_eq_of_lt hj')
          rw [hnext])

private lemma cycle_odd_main (k : ℕ) (hk : 0 < k) (hk3 : 3 ≤ k) (hodd : k % 2 = 1) :
    let p := k / 2
    (Finset.univ.filter (fun v : Fin k → F => MS_lin k hk Finset.univ v = 0)).card = 2 ^ (k - 2 * p) ∧
    ∃ (A B : Fin p → (Fin k → F) →ₗ[F] F) (L : (Fin k → F) →ₗ[F] F) (e : F),
      ∀ v : Fin k → F, qS k hk Finset.univ v = L v + e + ∑ j : Fin p, A j v * B j v := by
  intro p
  constructor
  · have hker_iff : ∀ v : Fin k → F,
        MS_lin k hk Finset.univ v = 0 ↔ ∀ j : Fin k, v j = v ⟨0, hk⟩ := by
      intro v
      rw [cycle_ker_per2 k hk hk3]
      constructor
      · intro hper j
        by_cases hj : j.val % 2 = 0
        · have hm := per2_mul k hk v hper (j.val / 2) ⟨0, hk⟩
          have heq : (0 : ℕ) + 2 * (j.val / 2) = j.val := by omega
          rw [heq, ix_val_eq] at hm; exact hm
        · have hm := per2_mul k hk v hper ((j.val + k) / 2) ⟨0, hk⟩
          have heq : (0 : ℕ) + 2 * ((j.val + k) / 2) = j.val + 1 * k := by omega
          rw [heq, ix_add_mul_k, ix_val_eq] at hm; exact hm
      · intro hconst j; rw [hconst (ix k hk (j.val + 2)), hconst j]
    have hcard_eq :
        (Finset.univ.filter (fun v : Fin k → F => MS_lin k hk Finset.univ v = 0)).card =
        (Finset.univ : Finset F).card := by
      refine Finset.card_bij (fun v _ => v ⟨0, hk⟩)
        (fun _ _ => Finset.mem_univ _)
        (fun v1 hv1 v2 hv2 heq => by
          funext j
          rw [(hker_iff v1).1 (Finset.mem_filter.1 hv1).2 j,
              (hker_iff v2).1 (Finset.mem_filter.1 hv2).2 j, heq])
        (fun a _ => ⟨fun _ => a, Finset.mem_filter.2 ⟨Finset.mem_univ _, (hker_iff _).2 (fun _ => rfl)⟩, rfl⟩)
    rw [hcard_eq, Finset.card_univ, ZMod.card]
    have hexp : k - 2 * p = 1 := by omega
    rw [hexp]; simp
  · let wLin (i : Fin k) : (Fin k → F) →ₗ[F] F :=
      (LinearMap.proj i : (Fin k → F) →ₗ[F] F) + LinearMap.proj (⟨0, hk⟩ : Fin k)
    let A : Fin p → (Fin k → F) →ₗ[F] F := fun j => wLin ⟨2 * j.val + 2, by omega⟩
    let B : Fin p → (Fin k → F) →ₗ[F] F := fun j =>
      wLin ⟨2 * j.val + 1, by omega⟩ +
        if h : 2 * j.val + 3 < k then wLin ⟨2 * j.val + 3, h⟩ else 0
    refine ⟨A, B, LinearMap.proj (⟨0, hk⟩ : Fin k), 0, fun v => ?_⟩
    simp only [LinearMap.proj_apply, add_zero]
    let w : Fin k → F := fun i => v i + v ⟨0, hk⟩
    have hw_eq : ∀ i : Fin k, wLin i v = w i := fun _ => rfl
    have hq_eq_w : qS k hk Finset.univ v = v ⟨0, hk⟩ + ∑ i : Fin k, w i * w (ix k hk (i.val + 1)) := by
      have hexp : ∀ i : Fin k,
          w i * w (ix k hk (i.val + 1)) =
            v i * v (ix k hk (i.val + 1)) +
            v ⟨0, hk⟩ * v i + v ⟨0, hk⟩ * v (ix k hk (i.val + 1)) + v ⟨0, hk⟩ := by
        intro i; dsimp only [w]
        have hsq : v ⟨0, hk⟩ * v ⟨0, hk⟩ = v ⟨0, hk⟩ := z2_mul_self _
        calc (v i + v ⟨0, hk⟩) * (v (ix k hk (i.val + 1)) + v ⟨0, hk⟩)
            = v i * v (ix k hk (i.val + 1)) + v ⟨0, hk⟩ * v i +
              v ⟨0, hk⟩ * v (ix k hk (i.val + 1)) + v ⟨0, hk⟩ * v ⟨0, hk⟩ := by ring
          _ = _ := by rw [hsq]
      simp only [hexp, Finset.sum_add_distrib]
      have hconst : (∑ _i : Fin k, v ⟨0, hk⟩) = v ⟨0, hk⟩ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hk1 : (k : F) = 1 := by
          calc (k : F) = ((2 * (k / 2) + 1 : ℕ) : F) := by congr 1; omega
            _ = (2 : F) * (k / 2 : ℕ) + 1 := by push_cast; rfl
            _ = 1 := by rw [z2_char2, zero_mul, zero_add]
        rw [hk1, one_mul]
      have hcross : (∑ i : Fin k, v ⟨0, hk⟩ * v (ix k hk (i.val + 1))) =
          (∑ i : Fin k, v ⟨0, hk⟩ * v i) := by
        refine Finset.sum_bij (fun i _ => ix k hk (i.val + 1))
          (fun _ _ => Finset.mem_univ _)
          (fun a _ b _ h => ix_next_injective k hk h)
          (fun y _ => ⟨ix k hk (y.val + k - 1 % k), Finset.mem_univ _, ix_sub_add k hk y 1⟩)
          (fun _ _ => rfl)
      rw [hconst, hcross]
      dsimp only [qS]
      have h1 : (∑ i : Fin k, v ⟨0, hk⟩ * v i) + (∑ i : Fin k, v ⟨0, hk⟩ * v i) = 0 := z2_add_self _
      have h2 : v ⟨0, hk⟩ + v ⟨0, hk⟩ = 0 := z2_add_self _
      calc (∑ i : Fin k, v i * v (ix k hk (i.val + 1)))
          = (∑ i : Fin k, v i * v (ix k hk (i.val + 1))) +
            ((∑ i : Fin k, v ⟨0, hk⟩ * v i) + (∑ i : Fin k, v ⟨0, hk⟩ * v i)) +
            (v ⟨0, hk⟩ + v ⟨0, hk⟩) := by rw [h1, h2, add_zero, add_zero]
        _ = v ⟨0, hk⟩ + ((∑ i : Fin k, v i * v (ix k hk (i.val + 1))) +
            (∑ i : Fin k, v ⟨0, hk⟩ * v i) + (∑ i : Fin k, v ⟨0, hk⟩ * v i) + v ⟨0, hk⟩) := by ring
    rw [hq_eq_w]
    congr 1
    have hw0 : w ⟨0, hk⟩ = 0 := z2_add_self _
    have hrhs : (∑ j : Fin p, A j v * B j v) =
        (∑ j : Fin p, w ⟨2 * j.val + 1, by omega⟩ * w ⟨2 * j.val + 2, by omega⟩) +
        (∑ j : Fin p, if h : 2 * j.val + 3 < k then
          w ⟨2 * j.val + 2, by omega⟩ * w ⟨2 * j.val + 3, h⟩ else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      dsimp only [A, B, LinearMap.add_apply]; rw [hw_eq, hw_eq]
      split_ifs with h
      · rw [hw_eq]; ring
      · rw [LinearMap.zero_apply, add_zero, add_zero, mul_comm]
    rw [hrhs]
    let f_w : Fin k → F := fun i => w i * w (ix k hk (i.val + 1))
    have hterm_zero : ∀ i : Fin k, (i.val = 0 ∨ i.val = k - 1) → f_w i = 0 := by
      intro i hi; dsimp only [f_w]
      rcases hi with h0 | hlast
      · rw [(Fin.ext h0 : i = ⟨0, hk⟩), hw0, zero_mul]
      · have hnext : ix k hk (i.val + 1) = ⟨0, hk⟩ := by
          apply Fin.ext; change (i.val + 1) % k = 0; rw [show i.val + 1 = k by omega, Nat.mod_self]
        rw [hnext, hw0, mul_zero]
    have hlhs_split :
        (∑ i : Fin k, f_w i) =
          (∑ i ∈ Finset.univ.filter (fun i : Fin k => 1 ≤ i.val ∧ i.val < k - 1 ∧ i.val % 2 = 1), f_w i) +
          (∑ i ∈ Finset.univ.filter (fun i : Fin k => 1 ≤ i.val ∧ i.val < k - 1 ∧ i.val % 2 = 0), f_w i) := by
      rw [← Finset.sum_union]
      · symm; refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact hterm_zero i (by omega)
      · rw [Finset.disjoint_left]; intro i h1 h2; simp only [Finset.mem_filter] at h1 h2; omega
    rw [hlhs_split]
    congr 1
    · symm
      refine Finset.sum_bij (fun j _ => (⟨2 * j.val + 1, by omega⟩ : Fin k))
        (fun j _ => by simp; omega)
        (fun a _ b _ h => Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega))
        (fun i hi => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          exact ⟨⟨(i.val - 1) / 2, by omega⟩, Finset.mem_univ _, Fin.ext (by dsimp; omega)⟩)
        (fun j _ => by
          dsimp only [f_w]
          have hnext : ix k hk (2 * j.val + 1 + 1) = ⟨2 * j.val + 2, by omega⟩ :=
            Fin.ext (by dsimp [ix]; exact Nat.mod_eq_of_lt (by omega))
          rw [hnext])
    · symm
      have hfilt_eq : (∑ j : Fin p, if h : 2 * j.val + 3 < k then
          w ⟨2 * j.val + 2, by omega⟩ * w ⟨2 * j.val + 3, h⟩ else 0) =
          ∑ j ∈ Finset.univ.filter (fun j : Fin p => 2 * j.val + 3 < k),
            if h : 2 * j.val + 3 < k then w ⟨2 * j.val + 2, by omega⟩ * w ⟨2 * j.val + 3, h⟩ else 0 := by
        symm; refine Finset.sum_subset (Finset.filter_subset _ _) fun j _ hj => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        exact dif_neg hj
      rw [hfilt_eq]
      refine Finset.sum_bij (fun j _ => (⟨2 * j.val + 2, by omega⟩ : Fin k))
        (fun j hj => by rw [Finset.mem_filter] at hj ⊢; exact ⟨Finset.mem_univ _, by dsimp; omega, by dsimp; omega, by dsimp; omega⟩)
        (fun a _ b _ h => Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega))
        (fun i hi => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          exact ⟨⟨(i.val - 2) / 2, by omega⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, by dsimp; omega⟩, Fin.ext (by dsimp; omega)⟩)
        (fun j hj => by
          have hj' := (Finset.mem_filter.1 hj).2
          rw [dif_pos hj']
          dsimp only [f_w]
          have hnext : ix k hk (2 * j.val + 2 + 1) = ⟨2 * j.val + 3, hj'⟩ :=
            Fin.ext (by dsimp [ix]; exact Nat.mod_eq_of_lt hj')
          rw [hnext])

private lemma cycle_proper_main (k : ℕ) (hk : 0 < k) (S : Finset (Fin k)) (hS : S ≠ Finset.univ) :
    2 * pCyc k hk S ≤ k ∧
    (Finset.univ.filter (fun v : Fin k → F => MS_lin k hk S v = 0)).card = 2 ^ (k - 2 * pCyc k hk S) ∧
    ∃ (A B : Fin (pCyc k hk S) → (Fin k → F) →ₗ[F] F) (L : (Fin k → F) →ₗ[F] F) (e : F),
      ∀ v : Fin k → F, qS k hk S v = L v + e + ∑ j : Fin (pCyc k hk S), A j v * B j v := by
  have hexr : ∃ r : Fin k, r ∉ S := by
    by_contra h; push_neg at h; exact hS (Finset.eq_univ_iff_forall.2 h)
  obtain ⟨r, hr⟩ := hexr
  let pos : Fin k → Fin k := fun t => ix k hk (r.val + 1 + t.val)
  let posInv : Fin k → Fin k := fun i => ix k hk (i.val + k - (r.val + 1) % k)
  have hpos_left : ∀ t : Fin k, posInv (pos t) = t := fun t => by
    dsimp only [pos, posInv]
    have hcomm : r.val + 1 + t.val = t.val + (r.val + 1) := by omega
    rw [hcomm]; exact ix_add_sub k hk t (r.val + 1)
  have hpos_right : ∀ i : Fin k, pos (posInv i) = i := fun i => by
    dsimp only [pos, posInv]
    have hcomm : r.val + 1 + (ix k hk (i.val + k - (r.val + 1) % k)).val =
        (ix k hk (i.val + k - (r.val + 1) % k)).val + (r.val + 1) := by omega
    rw [hcomm]; exact ix_sub_add k hk i (r.val + 1)
  have hpos_inj : Function.Injective pos := Function.LeftInverse.injective hpos_left
  have hpos_last : pos ⟨k - 1, by omega⟩ = r := by
    dsimp only [pos]
    have heq : r.val + 1 + (k - 1) = r.val + 1 * k := by omega
    rw [heq, ix_add_mul_k, ix_val_eq]
  have hpos_next : ∀ (t : Fin k) (hlt : t.val + 1 < k),
      ix k hk ((pos t).val + 1) = pos ⟨t.val + 1, hlt⟩ := fun t hlt => by
    dsimp only [pos]; rw [ix_add_ix]; simp [add_assoc]
  have hpos_prev : ∀ (t : Fin k) (h0 : 0 < t.val),
      ix k hk ((pos t).val + k - 1 % k) = pos ⟨t.val - 1, by omega⟩ := fun t h0 => by
    have h1 : pos t = ix k hk ((pos ⟨t.val - 1, by omega⟩).val + 1) := by
      have ht := t.isLt
      rw [hpos_next ⟨t.val - 1, by omega⟩ (by dsimp; omega)]; congr 1; exact Fin.ext (by dsimp; omega)
    rw [h1]; exact ix_add_sub k hk (pos ⟨t.val - 1, by omega⟩) 1
  have hpos_prev0 : ix k hk ((pos ⟨0, hk⟩).val + k - 1 % k) = r := by
    have h1 : pos ⟨0, hk⟩ = ix k hk (r.val + 1) := by dsimp [pos]
    rw [h1]; exact ix_add_sub k hk r 1
  let n := k - 1
  have hkn : n + 1 = k := Nat.sub_add_cancel hk
  let A : Finset (Fin n) := Finset.univ.filter (fun t : Fin n => pos ⟨t.val, by omega⟩ ∈ S)
  have hp_eq : pCyc k hk S = muLin n A := by
    have hp1 : pCyc k hk S = muCyc k hk S := by dsimp [pCyc]; simp [hS]
    rw [hp1]
    apply le_antisymm
    · apply Finset.sup_le
      intro E hE
      rw [Finset.mem_filter, Finset.mem_powerset] at hE
      rcases hE with ⟨hES, hEind⟩
      let E' : Finset (Fin n) := Finset.univ.filter (fun t : Fin n => pos ⟨t.val, by omega⟩ ∈ E)
      have hE'mem : E' ∈ A.powerset.filter (isIndepLin n) := by
        rw [Finset.mem_filter, Finset.mem_powerset]
        refine ⟨fun t ht => Finset.mem_filter.2 ⟨Finset.mem_univ _, hES (Finset.mem_filter.1 ht).2⟩,
          fun t ht hlt hmem => ?_⟩
        have hnx := hpos_next ⟨t.val, by omega⟩ (by omega : t.val + 1 < k)
        exact hEind (pos ⟨t.val, by omega⟩) (Finset.mem_filter.1 ht).2 (hnx.symm ▸ (Finset.mem_filter.1 hmem).2)
      have hEeq : E = E'.image (fun t : Fin n => pos ⟨t.val, by omega⟩) := by
        ext i; simp only [Finset.mem_image, E', Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hi
          let t := posInv i
          have hti : pos t = i := hpos_right i
          have htn : t.val < n := by
            by_contra hge
            have hir : i = r := by rw [← hti, (Fin.ext (by dsimp [n] at *; have := t.isLt; omega) : t = ⟨k - 1, by omega⟩), hpos_last]
            exact hr (hir ▸ hES hi)
          exact ⟨⟨t.val, htn⟩, hti.symm ▸ hi, hti⟩
        · rintro ⟨t, ht, rfl⟩; exact ht
      have hinj : Function.Injective (fun t : Fin n => pos ⟨t.val, by omega⟩) :=
        fun a b h => Fin.ext (by simpa using congrArg Fin.val (hpos_inj h))
      rw [hEeq, Finset.card_image_of_injective _ hinj]
      exact Finset.le_sup (f := Finset.card) hE'mem
    · apply Finset.sup_le
      intro E' hE'
      rw [Finset.mem_filter, Finset.mem_powerset] at hE'
      rcases hE' with ⟨hE'A, hE'ind⟩
      let embPos : Fin n → Fin k := fun t => pos ⟨t.val, by omega⟩
      have hinj : Function.Injective embPos := fun a b h => Fin.ext (by simpa using congrArg Fin.val (hpos_inj h))
      let E := E'.image embPos
      have hEmem : E ∈ S.powerset.filter (isIndepCyc k hk) := by
        rw [Finset.mem_filter, Finset.mem_powerset]
        refine ⟨?_, ?_⟩
        · intro i hi; rcases Finset.mem_image.1 hi with ⟨t, ht, rfl⟩; exact (Finset.mem_filter.1 (hE'A ht)).2
        · intro i hi hnext
          rcases Finset.mem_image.1 hi with ⟨t, ht, rfl⟩
          rcases Finset.mem_image.1 hnext with ⟨t2, ht2, hteq⟩
          have htlt := t.isLt
          rw [hpos_next ⟨t.val, by omega⟩ (by dsimp [n] at *; omega)] at hteq
          have hval := congrArg Fin.val (hpos_inj hteq)
          dsimp at hval
          have hlt' : t.val + 1 < n := by have := t2.isLt; omega
          exact hE'ind t ht hlt' ((Fin.ext (by simpa using hval.symm) : (⟨t.val + 1, hlt'⟩ : Fin n) = t2) ▸ ht2)
      rw [← Finset.card_image_of_injective E' hinj]
      exact Finset.le_sup (f := Finset.card) hEmem
  obtain ⟨h2le, hkerL, PL, QL, hqL⟩ := lin_main n A
  let piLin : (Fin k → F) →ₗ[F] (Fin (n + 1) → F) := {
    toFun := fun v t => v (pos ⟨t.val, by omega⟩)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
  }
  have hpi_bij : Function.Bijective piLin := by
    constructor
    · intro v1 v2 h; funext i
      simpa [piLin, hpos_right] using congrFun h ⟨(posInv i).val, by omega⟩
    · intro w; exact ⟨fun i => w ⟨(posInv i).val, by omega⟩, funext fun t => by simp [piLin, hpos_left]⟩
  refine ⟨by omega, ?_, ?_⟩
  · have hker_iff : ∀ v : Fin k → F, MS_lin k hk S v = 0 ↔ MLin n A (piLin v) = 0 := by
      intro v
      have hpt : ∀ t : Fin (n + 1), MS_lin k hk S v (pos ⟨t.val, by omega⟩) = MLin n A (piLin v) t := by
        intro t
        change (if pos ⟨t.val, by omega⟩ ∈ S then v (ix k hk ((pos ⟨t.val, by omega⟩).val + 1)) else 0) +
          (if ix k hk ((pos ⟨t.val, by omega⟩).val + k - 1 % k) ∈ S then
            v (ix k hk ((pos ⟨t.val, by omega⟩).val + k - 1 % k)) else 0) = _
        dsimp only [MLin, piLin, LinearMap.coe_mk, AddHom.coe_mk]
        congr 1
        · by_cases hlt : t.val < n
          · simp only [hlt, ↓reduceDIte]
            have hmem : (pos ⟨t.val, by omega⟩ ∈ S) ↔ ((⟨t.val, hlt⟩ : Fin n) ∈ A) := by simp [A]
            have hnx := hpos_next ⟨t.val, by omega⟩ (by omega : t.val + 1 < k)
            by_cases hm : (⟨t.val, hlt⟩ : Fin n) ∈ A
            · simp [hm, hmem.2 hm, hnx]
            · simp [hm, mt hmem.1 hm]
          · have hteq : (⟨t.val, by omega⟩ : Fin k) = ⟨k - 1, by omega⟩ := Fin.ext (by dsimp [n] at *; have := t.isLt; omega)
            simp only [hlt, ↓reduceDIte, hteq, hpos_last, hr, ↓reduceIte]
        · by_cases h0 : 0 < t.val
          · simp only [h0, ↓reduceDIte]
            rw [hpos_prev ⟨t.val, by omega⟩ h0]
            have hmem : (pos ⟨t.val - 1, by omega⟩ ∈ S) ↔ ((⟨t.val - 1, by omega⟩ : Fin n) ∈ A) := by simp [A]
            by_cases hm : (⟨t.val - 1, by omega⟩ : Fin n) ∈ A
            · simp [hm, hmem.2 hm]
            · simp [hm, mt hmem.1 hm]
          · have hteq : (⟨t.val, by omega⟩ : Fin k) = ⟨0, hk⟩ := Fin.ext (by dsimp; omega)
            simp only [h0, ↓reduceDIte, hteq, hpos_prev0, hr, ↓reduceIte]
      constructor
      · intro hv; funext t; rw [← hpt t, hv]; rfl
      · intro hw; funext i
        have ht := hpt ⟨(posInv i).val, by omega⟩
        rw [hpos_right i] at ht; rw [ht, hw]; rfl
    have hcard_eq :
        (Finset.univ.filter (fun v : Fin k → F => MS_lin k hk S v = 0)).card =
        (Finset.univ.filter (fun w : Fin (n + 1) → F => MLin n A w = 0)).card := by
      refine Finset.card_bij (fun v _ => piLin v)
        (fun v hv => Finset.mem_filter.2 ⟨Finset.mem_univ _, (hker_iff v).1 (Finset.mem_filter.1 hv).2⟩)
        (fun _ _ _ _ h => hpi_bij.1 h)
        (fun w hw => by
          obtain ⟨v, rfl⟩ := hpi_bij.2 w
          exact ⟨v, Finset.mem_filter.2 ⟨Finset.mem_univ _, (hker_iff v).2 (Finset.mem_filter.1 hw).2⟩, rfl⟩)
    rw [hcard_eq, hkerL, hp_eq, hkn]
  · refine ⟨fun j => (PL ⟨j.val, by omega⟩).comp piLin,
            fun j => (QL ⟨j.val, by omega⟩).comp piLin, 0, 0, fun v => ?_⟩
    simp only [LinearMap.zero_apply, zero_add, LinearMap.comp_apply]
    have hsum_eq :
        (∑ j : Fin (pCyc k hk S), PL ⟨j.val, by omega⟩ (piLin v) * QL ⟨j.val, by omega⟩ (piLin v)) =
        ∑ j : Fin (muLin n A), PL j (piLin v) * QL j (piLin v) := by
      refine Finset.sum_bij (fun j _ => ⟨j.val, by omega⟩)
        (fun _ _ => Finset.mem_univ _)
        (fun a _ b _ h => Fin.ext (by simpa using congrArg Fin.val h))
        (fun j _ => ⟨⟨j.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
        (fun _ _ => rfl)
    rw [hsum_eq, ← hqL (piLin v)]
    dsimp only [qS, qLin]
    symm
    refine Finset.sum_bij (fun t _ => pos ⟨t.val, by omega⟩)
      (fun t ht => (Finset.mem_filter.1 ht).2)
      (fun a _ b _ h => Fin.ext (by simpa using congrArg Fin.val (hpos_inj h)))
      (fun i hi => by
        let t := posInv i
        have hti : pos t = i := hpos_right i
        have htn : t.val < n := by
          by_contra hge
          exact hr ((by rw [← hti, (Fin.ext (by dsimp [n] at *; have := t.isLt; omega) : t = ⟨k - 1, by omega⟩), hpos_last] : i = r) ▸ hi)
        exact ⟨⟨t.val, htn⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hti.symm ▸ hi⟩, hti⟩)
      (fun t _ => by have := t.isLt; rw [hpos_next ⟨t.val, by omega⟩ (by dsimp [n] at *; omega)]; rfl)

private lemma cycle_main (k : ℕ) (hk : 0 < k) (S : Finset (Fin k)) :
    2 * pCyc k hk S ≤ k ∧
    (Finset.univ.filter (fun v : Fin k → F => MS_lin k hk S v = 0)).card = 2 ^ (k - 2 * pCyc k hk S) ∧
    ∃ (A B : Fin (pCyc k hk S) → (Fin k → F) →ₗ[F] F) (L : (Fin k → F) →ₗ[F] F) (e : F),
      ∀ v : Fin k → F, qS k hk S v = L v + e + ∑ j : Fin (pCyc k hk S), A j v * B j v := by
  by_cases hS : S = Finset.univ
  · subst hS
    by_cases hk1 : k = 1
    · subst hk1
      have hmu : muCyc 1 hk Finset.univ = 0 := by
        apply Nat.eq_zero_of_le_zero; apply Finset.sup_le; intro E hE
        rw [Finset.mem_filter] at hE
        have hE0 : E = ∅ := by
          ext i; simp only [Finset.notMem_empty, iff_false]; intro hi
          have h1 : ix 1 hk (i.val + 1) = i := Fin.ext (by dsimp [ix]; omega)
          exact hE.2 i hi (h1.symm ▸ hi)
        rw [hE0]; simp
      have hp : pCyc 1 hk Finset.univ = 0 := by unfold pCyc; rw [if_neg (by decide)]; exact hmu
      rw [hp]
      refine ⟨by omega, ?_, ?_⟩
      · have hflt : Finset.univ.filter (fun v : Fin 1 → F => MS_lin 1 hk Finset.univ v = 0) = Finset.univ := by
          ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; funext j
          have h1 : ix 1 hk (j.val + 1) = j := Fin.ext (by dsimp [ix]; omega)
          have h2 : ix 1 hk (j.val + 1 - 1 % 1) = j := Fin.ext (by dsimp [ix]; omega)
          change (if j ∈ Finset.univ then v (ix 1 hk (j.val + 1)) else 0) +
            (if ix 1 hk (j.val + 1 - 1 % 1) ∈ Finset.univ then v (ix 1 hk (j.val + 1 - 1 % 1)) else 0) = 0
          rw [if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _), h1, h2, z2_add_self]
        rw [hflt, card_finset_univ_vec]
      · refine ⟨Fin.elim0, Fin.elim0, LinearMap.proj (⟨0, hk⟩ : Fin 1), 0, fun v => ?_⟩
        simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, LinearMap.proj_apply]
        dsimp [qS]
        have hu : (Finset.univ : Finset (Fin 1)) = {⟨0, hk⟩} := by ext i; simp [Fin.ext_iff]
        rw [hu, Finset.sum_singleton]
        have h0 : ix 1 hk (0 + 1) = ⟨0, hk⟩ := Fin.ext (by dsimp [ix])
        simp [h0, z2_mul_self]
    · by_cases hk2 : k = 2
      · subst hk2
        have hmu : muCyc 2 hk Finset.univ = 1 := muCyc_univ_eq 2 hk (by omega)
        have hp : pCyc 2 hk Finset.univ = 0 := by dsimp [pCyc]; simp [hmu]
        rw [hp]
        refine ⟨by omega, ?_, ?_⟩
        · have hflt : Finset.univ.filter (fun v : Fin 2 → F => MS_lin 2 hk Finset.univ v = 0) = Finset.univ := by
            ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; funext j
            have h12 : ix 2 hk (j.val + 2 - 1 % 2) = ix 2 hk (j.val + 1) := rfl
            change (if j ∈ Finset.univ then v (ix 2 hk (j.val + 1)) else 0) +
              (if ix 2 hk (j.val + 2 - 1 % 2) ∈ Finset.univ then v (ix 2 hk (j.val + 2 - 1 % 2)) else 0) = 0
            simp [h12, z2_add_self]
          rw [hflt, card_finset_univ_vec]
        · refine ⟨Fin.elim0, Fin.elim0, 0, 0, fun v => ?_⟩
          simp only [Finset.univ_eq_empty, Finset.sum_empty, LinearMap.zero_apply, add_zero]
          dsimp [qS]; rw [Fin.sum_univ_two]
          have h0 : ix 2 hk (0 + 1) = ⟨1, by omega⟩ := Fin.ext (by dsimp [ix])
          have h1 : ix 2 hk (1 + 1) = ⟨0, by omega⟩ := Fin.ext (by dsimp [ix])
          change v ⟨0, by omega⟩ * v (ix 2 hk (0 + 1)) + v ⟨1, by omega⟩ * v (ix 2 hk (1 + 1)) = 0
          rw [h0, h1, mul_comm (v ⟨1, by omega⟩), z2_add_self]
      · have hmu : muCyc k hk Finset.univ = k / 2 := muCyc_univ_eq k hk (by omega)
        by_cases hpar : k % 2 = 0
        · have hp : pCyc k hk Finset.univ = k / 2 - 1 := by dsimp [pCyc]; simp [hmu, hpar]
          rw [hp]
          obtain ⟨hker, hdec⟩ := cycle_even_main k hk (by omega) hpar
          exact ⟨by omega, hker, hdec⟩
        · have hp : pCyc k hk Finset.univ = k / 2 := by dsimp [pCyc]; simp [hmu, hpar]
          rw [hp]
          obtain ⟨hker, hdec⟩ := cycle_odd_main k hk (by omega) (by omega)
          exact ⟨by omega, hker, hdec⟩
  · exact cycle_proper_main k hk S hS

-- Section 4: Linear algebra cardinality & annihilator helpers

private lemma card_mul_ker_of_fn {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Fintype A] [Fintype B] [DecidableEq B] (f : A → B)
    (hadd : ∀ x y, f (x + y) = f x + f y) (hsub : ∀ x y, f (x - y) = f x - f y) :
    Fintype.card A = Fintype.card {a : A // f a = 0} * (Finset.univ.image f).card := by
  have hpart := Finset.card_eq_sum_card_fiberwise (f := f)
    (s := (Finset.univ : Finset A)) (t := Finset.univ.image f)
    (fun a _ => Finset.mem_image_of_mem f (Finset.mem_univ a))
  rw [Finset.card_univ] at hpart
  rw [hpart]
  trans (∑ _b ∈ Finset.univ.image f, Fintype.card {a : A // f a = 0})
  · refine Finset.sum_congr rfl fun b hb => ?_
    rcases Finset.mem_image.1 hb with ⟨a₀, _, rfl⟩
    rw [← Finset.card_univ]
    refine Finset.card_bij
      (fun a ha => (⟨a - a₀, by rw [hsub, (Finset.mem_filter.1 ha).2, sub_self]⟩ : {a : A // f a = 0}))
      (fun _ _ => Finset.mem_univ _)
      (fun x _ y _ h => sub_left_inj.1 (congrArg Subtype.val h))
      (fun u _ => ⟨u.val + a₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [hadd, u.2, zero_add]⟩, Subtype.ext (by abel)⟩)
  · rw [Finset.sum_const, smul_eq_mul, mul_comm]

private lemma card_le_ker_mul_codomain {R : Type*} [Semiring R] {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module R B] [Fintype A] [Fintype B] (L : A →ₗ[R] B) :
    Fintype.card A ≤ Fintype.card (LinearMap.ker L) * Fintype.card B := by
  have h := card_mul_ker_of_fn (fun a => L a) (fun x y => map_add L x y) (fun x y => map_sub L x y)
  have hkeq : Fintype.card {a : A // L a = 0} = Fintype.card (LinearMap.ker L) :=
    Fintype.card_congr ⟨fun u => ⟨u.1, u.2⟩, fun u => ⟨u.1, u.2⟩, fun _ => rfl, fun _ => rfl⟩
  rw [hkeq] at h; rw [h]
  exact Nat.mul_le_mul_left _ (by simpa [Finset.card_univ] using Finset.card_le_univ (Finset.univ.image (fun a => L a)))

private lemma card_eq_ker_mul_codomain_of_surj {R : Type*} [Semiring R] {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module R B] [Fintype A] [Fintype B] (L : A →ₗ[R] B)
    (hsurj : Function.Surjective L) :
    Fintype.card A = Fintype.card (LinearMap.ker L) * Fintype.card B := by
  have h := card_mul_ker_of_fn (fun a => L a) (fun x y => map_add L x y) (fun x y => map_sub L x y)
  have hkeq : Fintype.card {a : A // L a = 0} = Fintype.card (LinearMap.ker L) :=
    Fintype.card_congr ⟨fun u => ⟨u.1, u.2⟩, fun u => ⟨u.1, u.2⟩, fun _ => rfl, fun _ => rfl⟩
  rw [hkeq] at h; rw [h]
  have himg : Finset.univ.image (fun a => L a) = Finset.univ := by
    ext b; simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]; exact hsurj b
  rw [himg, Finset.card_univ]

private lemma subspace_equiv_fin {k : ℕ} (U : Submodule F (Fin k → F)) :
    ∃ r : ℕ, Nonempty ((Fin r → F) ≃ₗ[F] U) :=
  ⟨Module.finrank F U, ⟨(Module.finBasis F U).equivFun.symm⟩⟩

private def annSub {k : ℕ} (U : Submodule F (Fin k → F)) : Submodule F (Fin k → F) :=
  { carrier := {w | ∀ u ∈ U, dotProduct u w = 0}, add_mem' := fun {w1 w2} h1 h2 u hu => by
      rw [dot_add_right, h1 u hu, h2 u hu, add_zero]
    zero_mem' := fun u _ => by simp [dotProduct]
    smul_mem' := fun c {w} hw u hu => by
      change dotProduct u (c • w) = 0
      simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
      calc (∑ i, u i * (c * w i)) = c * (∑ i, u i * w i) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
        _ = c * dotProduct u w := rfl
        _ = c * 0 := by rw [hw u hu]
        _ = 0 := mul_zero c }

private lemma card_mul_ann {k : ℕ} (U : Submodule F (Fin k → F)) :
    Fintype.card U * Fintype.card (annSub U) = 2 ^ k := by
  obtain ⟨r, ⟨e⟩⟩ := subspace_equiv_fin U
  let res : (Fin k → F) →ₗ[F] (Fin r → F) := {
    toFun := fun w i => dotProduct (e (Pi.single i 1)).val w
    map_add' := fun w1 w2 => funext fun i => dot_add_right _ w1 w2
    map_smul' := fun c w => funext fun i => by
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
  }
  have hker : LinearMap.ker res = annSub U := by
    ext w
    simp only [LinearMap.mem_ker, annSub, Submodule.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
    constructor
    · intro hw u hu
      let v : Fin r → F := e.symm ⟨u, hu⟩
      have hu_eq : u = ∑ i : Fin r, v i • (e (Pi.single i 1)).val := by
        have hv : v = ∑ i : Fin r, v i • Pi.single i (1 : F) := by
          funext j; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          rw [Finset.sum_eq_single j]
          · simp
          · intro l _ hlj; simp [Pi.single_eq_of_ne (Ne.symm hlj)]
          · intro hj; exact absurd (Finset.mem_univ j) hj
        have hev : (⟨u, hu⟩ : U) = e v := (e.apply_symm_apply ⟨u, hu⟩).symm
        calc u = U.subtype (e v) := congrArg Subtype.val hev
          _ = U.subtype (e (∑ i : Fin r, v i • Pi.single i 1)) := by rw [← hv]
          _ = ∑ i : Fin r, v i • U.subtype (e (Pi.single i 1)) := by
              rw [map_sum, map_sum]; refine Finset.sum_congr rfl fun i _ => by rw [map_smul, map_smul]
          _ = ∑ i : Fin r, v i • (e (Pi.single i 1)).val := rfl
      rw [hu_eq, sum_dotProduct]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [smul_dotProduct]
      have hwi : dotProduct (e (Pi.single i 1)).val w = 0 := congrFun hw i
      rw [hwi, smul_zero]
    · intro hw; funext i
      exact hw (e (Pi.single i 1)).val (e (Pi.single i 1)).property
  have hsurj : Function.Surjective res := by
    intro y
    let phi : U →ₗ[F] F := (dotLin y).comp e.symm.toLinearMap
    obtain ⟨Phi, hPhi⟩ := LinearMap.exists_extend phi
    obtain ⟨w, hw⟩ := linearMap_eq_dotProduct Phi
    refine ⟨w, funext fun i => ?_⟩
    have h1 : Phi (e (Pi.single i 1)).val = phi (e (Pi.single i 1)) := by
      simpa using congrArg (fun f => f (e (Pi.single i 1))) hPhi
    calc res w i = dotProduct (e (Pi.single i 1)).val w := rfl
      _ = dotProduct w (e (Pi.single i 1)).val := dotProduct_comm _ _
      _ = Phi (e (Pi.single i 1)).val := (hw _).symm
      _ = phi (e (Pi.single i 1)) := h1
      _ = dotProduct y (Pi.single i 1) := by simp [phi, dotLin]
      _ = y i := by
          simp only [dotProduct]
          rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hji; simp [Pi.single_eq_of_ne hji]
          · intro hi; exact absurd (Finset.mem_univ i) hi
  have hcard := card_eq_ker_mul_codomain_of_surj res hsurj
  rw [card_vec k, hker] at hcard
  have hU : Fintype.card U = Fintype.card (Fin r → F) := Fintype.card_congr e.symm.toEquiv
  rw [hU, mul_comm]
  exact hcard.symm

private lemma card_U_mul_rad_le {k : ℕ} (M_lin : (Fin k → F) →ₗ[F] (Fin k → F))
    (U : Submodule F (Fin k → F)) :
    let R_U : Submodule F U := {
      carrier := {u | ∀ u' : U, dotProduct u'.val (M_lin u.val) = 0}, add_mem' := fun {a b} ha hb u' => by
        change dotProduct u'.val (M_lin (a.val + b.val)) = 0
        rw [map_add, dot_add_right, ha u', hb u', add_zero]
      zero_mem' := fun u' => by simp [dotProduct]
      smul_mem' := fun c {a} ha u' => by
        change dotProduct u'.val (M_lin (c • a.val)) = 0
        rw [map_smul, dotProduct_smul, ha u', smul_zero]
    }
    Fintype.card U * Fintype.card R_U ≤ Fintype.card (LinearMap.ker M_lin) * 2 ^ k := by
  intro R_U
  let Psi : R_U →ₗ[F] annSub U := {
    toFun := fun u => ⟨M_lin u.val.val, fun u' hu' => u.property ⟨u', hu'⟩⟩
    map_add' := fun a b => Subtype.ext (map_add M_lin _ _)
    map_smul' := fun c a => Subtype.ext (map_smul M_lin c _)
  }
  have h2 : Fintype.card R_U ≤ Fintype.card (LinearMap.ker M_lin) * Fintype.card (annSub U) := by
    have ha := card_mul_ker_of_fn (fun u : R_U => Psi u) (fun a b => map_add Psi a b) (fun a b => map_sub Psi a b)
    rw [ha]
    refine Nat.mul_le_mul ?_ (by simpa [Finset.card_univ] using Finset.card_le_univ (Finset.univ.image (fun u : R_U => Psi u)))
    refine Fintype.card_le_of_injective
      (fun u => ⟨u.val.val.val, by rw [LinearMap.mem_ker]; exact congrArg Subtype.val u.property⟩)
      (fun a b h => by dsimp only at h; exact Subtype.ext (Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h))))
  calc Fintype.card U * Fintype.card R_U
      ≤ Fintype.card U * (Fintype.card (LinearMap.ker M_lin) * Fintype.card (annSub U)) :=
        Nat.mul_le_mul_left _ h2
    _ = Fintype.card (LinearMap.ker M_lin) * (Fintype.card U * Fintype.card (annSub U)) := by ring
    _ = Fintype.card (LinearMap.ker M_lin) * 2 ^ k := by rw [card_mul_ann U]

-- Section 5: Decision tree runAux & Upper Bound

private def runAux {k d : ℕ} (ask : Fin d → ℕ → ((Fin k → F) →ₗ[F] F))
    (l : List (Fin d)) (x : Fin k → F) : ℕ :=
  l.foldl (fun h j => 2 * h + (if ask j h x = 0 then 0 else 1)) 0

private lemma runAux_lt {k d : ℕ} (ask : Fin d → ℕ → ((Fin k → F) →ₗ[F] F))
    (l : List (Fin d)) (x : Fin k → F) : runAux ask l x < 2 ^ l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [runAux]
  | append_singleton l j ih =>
    simp only [runAux, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.length_append, List.length_singleton, pow_succ]
    change 2 * runAux ask l x + (if ask j (runAux ask l x) x = 0 then 0 else 1) < 2 ^ l.length * 2
    split_ifs <;> omega

private lemma runAux_leaf_subspace {k d : ℕ} (ask : Fin d → ℕ → ((Fin k → F) →ₗ[F] F))
    (l : List (Fin d)) (x₀ : Fin k → F) :
    ∃ U : Submodule F (Fin k → F), ∀ x : Fin k → F, runAux ask l x = runAux ask l x₀ ↔ x + x₀ ∈ U := by
  induction l using List.reverseRecOn with
  | nil => exact ⟨⊤, fun _ => by simp [runAux]⟩
  | append_singleton l j ih =>
    obtain ⟨U, hU⟩ := ih
    let h₀ := runAux ask l x₀
    let f := ask j h₀
    refine ⟨U ⊓ LinearMap.ker f, fun x => ?_⟩
    simp only [runAux, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Submodule.mem_inf, LinearMap.mem_ker]
    change (2 * runAux ask l x + (if ask j (runAux ask l x) x = 0 then 0 else 1) =
            2 * h₀ + (if f x₀ = 0 then 0 else 1)) ↔ x + x₀ ∈ U ∧ f (x + x₀) = 0
    constructor
    · intro heq
      have hdiv : runAux ask l x = h₀ ∧
          (if ask j (runAux ask l x) x = 0 then (0 : ℕ) else 1) = (if f x₀ = 0 then 0 else 1) := by
        split_ifs at heq ⊢ <;> constructor <;> omega
      have hmemU : x + x₀ ∈ U := (hU x).1 hdiv.1
      have hfx : f x = f x₀ := by
        have h2 := hdiv.2; rw [hdiv.1] at h2; exact (z2_ite_eq_iff (f x) (f x₀)).1 h2
      exact ⟨hmemU, by rw [map_add, hfx, z2_add_self]⟩
    · rintro ⟨hmemU, hker⟩
      have hpre : runAux ask l x = h₀ := (hU x).2 hmemU
      rw [hpre]; rw [map_add] at hker
      have hfx : f x = f x₀ := (z2_add_eq_zero_iff _ _).1 hker
      rw [show ask j h₀ = f from rfl, hfx]

private lemma runAux_nonadaptive_iff {k d : ℕ} (f : Fin d → ((Fin k → F) →ₗ[F] F))
    (l : List (Fin d)) (x x₀ : Fin k → F) :
    runAux (fun j _ => f j) l x = runAux (fun j _ => f j) l x₀ ↔
      ∀ j ∈ l, f j x = f j x₀ := by
  induction l using List.reverseRecOn with
  | nil => simp [runAux]
  | append_singleton l j ih =>
    simp only [runAux, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.mem_append, List.mem_singleton]
    change (2 * runAux (fun j _ => f j) l x + (if f j x = 0 then 0 else 1) =
            2 * runAux (fun j _ => f j) l x₀ + (if f j x₀ = 0 then 0 else 1)) ↔
            ∀ j' : Fin d, j' ∈ l ∨ j' = j → f j' x = f j' x₀
    constructor
    · intro heq
      have hdiv : runAux (fun j _ => f j) l x = runAux (fun j _ => f j) l x₀ ∧
          (if f j x = 0 then (0 : ℕ) else 1) = (if f j x₀ = 0 then 0 else 1) := by
        split_ifs at heq ⊢ <;> constructor <;> omega
      have hl := ih.1 hdiv.1
      have hj := (z2_ite_eq_iff (f j x) (f j x₀)).1 hdiv.2
      rintro j' (h' | rfl)
      · exact hl j' h'
      · exact hj
    · intro hall
      rw [ih.2 (fun j' h' => hall j' (Or.inl h')), hall j (Or.inr rfl)]

private lemma polar_translate {k : ℕ} {q : (Fin k → F) → F} {M : (Fin k → F) →ₗ[F] (Fin k → F)}
    (hq : ∀ u v, q (u + v) + q u + q v + q 0 = dotProduct u (M v))
    (x₀ u v : Fin k → F) :
    q (x₀ + (u + v)) + q (x₀ + u) + q (x₀ + v) + q x₀ = dotProduct u (M v) := by
  have h1 := hq x₀ (u + v)
  have h2 := hq x₀ u
  have h3 := hq x₀ v
  have h4 := hq u v
  have hlin : dotProduct x₀ (M (u + v)) = dotProduct x₀ (M u) + dotProduct x₀ (M v) := by
    rw [map_add, dot_add_right]
  have hsum :
      (q (x₀ + (u + v)) + q x₀ + q (u + v) + q 0) +
      (q (x₀ + u) + q x₀ + q u + q 0) +
      (q (x₀ + v) + q x₀ + q v + q 0) +
      (q (u + v) + q u + q v + q 0) =
      dotProduct u (M v) := by
    rw [h1, h2, h3, h4, hlin]
    have ha : dotProduct x₀ (M u) + dotProduct x₀ (M u) = 0 := z2_add_self _
    have hb : dotProduct x₀ (M v) + dotProduct x₀ (M v) = 0 := z2_add_self _
    calc dotProduct x₀ (M u) + dotProduct x₀ (M v) + dotProduct x₀ (M u) + dotProduct x₀ (M v) +
          dotProduct u (M v)
        = (dotProduct x₀ (M u) + dotProduct x₀ (M u)) +
          (dotProduct x₀ (M v) + dotProduct x₀ (M v)) + dotProduct u (M v) := by ring
      _ = dotProduct u (M v) := by rw [ha, hb, zero_add, zero_add]
  rw [← hsum]
  have hq0 : q 0 + q 0 = 0 := z2_add_self _
  have hqx0 : q x₀ + q x₀ = 0 := z2_add_self _
  have hqu : q u + q u = 0 := z2_add_self _
  have hqv : q v + q v = 0 := z2_add_self _
  have hquv : q (u + v) + q (u + v) = 0 := z2_add_self _
  calc q (x₀ + (u + v)) + q (x₀ + u) + q (x₀ + v) + q x₀
      = q (x₀ + (u + v)) + q (x₀ + u) + q (x₀ + v) + q x₀ +
        (q x₀ + q x₀) + (q (u + v) + q (u + v)) + (q u + q u) + (q v + q v) +
        (q 0 + q 0) + (q 0 + q 0) := by rw [hqx0, hquv, hqu, hqv, hq0]; simp
    _ = (q (x₀ + (u + v)) + q x₀ + q (u + v) + q 0) +
        (q (x₀ + u) + q x₀ + q u + q 0) +
        (q (x₀ + v) + q x₀ + q v + q 0) +
        (q (u + v) + q u + q v + q 0) := by ring

private lemma upper_bound_leaf (k : ℕ) (hk : 0 < k) (S : Finset (Fin k)) (p : ℕ)
    (h2pk : 2 * p ≤ k)
    (hker_Fintype : Fintype.card (LinearMap.ker (MS_lin k hk S)) = 2 ^ (k - 2 * p))
    (Lh : Finset (Fin k → F)) (x₀ : Fin k → F) (U : Submodule F (Fin k → F))
    (hLh_iff : ∀ x : Fin k → F, x ∈ Lh ↔ x + x₀ ∈ U)
    (pr : (Fin k → F) →ₗ[F] F) (bi : F) :
    2 * (Lh.filter (fun x => qS k hk S x = pr x + bi)).card ≤ Lh.card + 2 ^ (k - p) := by
  obtain ⟨r, ⟨e⟩⟩ := subspace_equiv_fin U
  have hLh_card : Lh.card = 2 ^ r := by
    rw [← card_finset_univ_vec r]
    refine Finset.card_bij (fun x hx => e.symm ⟨x + x₀, (hLh_iff x).1 hx⟩)
      (fun _ _ => Finset.mem_univ _)
      (fun x1 _ x2 _ heq => by
        have h1 := congrArg (fun z => (e z).val) heq
        simp only [LinearEquiv.apply_symm_apply] at h1
        simpa [vec_add_cancel_right] using congrArg (fun z => z + x₀) h1)
      (fun v _ => ⟨x₀ + (e v).val,
        (hLh_iff _).2 (by rw [add_comm x₀, vec_add_cancel_right]; exact (e v).property),
        by apply e.injective; simp only [LinearEquiv.apply_symm_apply]; apply Subtype.ext; change (x₀ + (e v).val) + x₀ = (e v).val; rw [add_comm x₀, vec_add_cancel_right]⟩)
  let qh : (Fin r → F) → F := fun v => qS k hk S (x₀ + (e v).val)
  obtain ⟨ah, hah⟩ := linearMap_eq_dotProduct (pr.comp (U.subtype.comp e.toLinearMap))
  let bh : F := pr x₀ + bi
  let Hh := Lh.filter (fun x => qS k hk S x = pr x + bi)
  have hHh_card : Hh.card =
      ((Finset.univ : Finset (Fin r → F)).filter (fun v => qh v + dotProduct ah v + bh = 0)).card := by
    refine Finset.card_bij (fun x hx => e.symm ⟨x + x₀, (hLh_iff x).1 (Finset.mem_filter.1 hx).1⟩)
      (fun x hx => by
        rw [Finset.mem_filter] at hx ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        let v := e.symm ⟨x + x₀, (hLh_iff x).1 hx.1⟩
        have hev : (e v).val = x + x₀ := congrArg Subtype.val (e.apply_symm_apply _)
        have hxv : x₀ + (e v).val = x := by rw [hev, add_comm x₀, vec_add_cancel_right]
        have hpred : dotProduct ah v = pr (e v).val := (hah v).symm
        dsimp only [qh, bh]
        rw [hxv, hpred, hev, map_add, hx.2]
        exact z2_cancel3 (pr x) bi (pr x₀))
      (fun x1 _ x2 _ heq => by
        have h1 := congrArg (fun z => (e z).val) heq
        simp only [LinearEquiv.apply_symm_apply] at h1
        simpa [vec_add_cancel_right] using congrArg (fun z => z + x₀) h1)
      (fun v hv => by
        rw [Finset.mem_filter] at hv
        let x := x₀ + (e v).val
        have hxL : x ∈ Lh := (hLh_iff x).2 (by dsimp [x]; rw [add_comm x₀, vec_add_cancel_right]; exact (e v).property)
        refine ⟨x, Finset.mem_filter.2 ⟨hxL, ?_⟩, ?_⟩
        · have hprx : pr x = pr x₀ + dotProduct ah v := by dsimp [x]; rw [map_add, ← hah v]; rfl
          rw [hprx]; apply (z2_add_eq_zero_iff _ _).1
          have hv0 := hv.2; dsimp only [qh, bh] at hv0
          calc qS k hk S x + (pr x₀ + dotProduct ah v + bi)
              = qS k hk S (x₀ + (e v).val) + dotProduct ah v + (pr x₀ + bi) := by ring
            _ = 0 := hv0
        · apply e.injective; simp only [LinearEquiv.apply_symm_apply]; apply Subtype.ext
          dsimp [x]; rw [add_comm x₀, vec_add_cancel_right])
  have hpol_h : ∀ u v : Fin r → F,
      qh (u + v) + qh u + qh v + qh 0 = dotProduct (e u).val (MS_lin k hk S (e v).val) := by
    intro u v; dsimp only [qh]
    have hadd : (e (u + v)).val = (e u).val + (e v).val := by rw [map_add]; rfl
    have hzero : (e 0).val = 0 := by rw [map_zero]; rfl
    rw [hadd, hzero, add_zero]
    exact polar_translate (polar_qS_eq k hk S) x₀ (e u).val (e v).val
  have hpol_lin : ∀ u v w : Fin r → F,
      (qh (u + (v + w)) + qh u + qh (v + w) + qh 0) =
        (qh (u + v) + qh u + qh v + qh 0) + (qh (u + w) + qh u + qh w + qh 0) := by
    intro u v w; rw [hpol_h, hpol_h, hpol_h]
    have hadd : (e (v + w)).val = (e v).val + (e w).val := by rw [map_add]; rfl
    rw [hadd, map_add, dot_add_right]
  have hwalsh := PEqualNP.Outside.L_lib_420 r qh hpol_lin ah
  dsimp only at hwalsh
  let radical_h := (Finset.univ : Finset (Fin r → F)).filter
    (fun u : Fin r → F => ∀ w : Fin r → F, qh (u + w) + qh u + qh w + qh 0 = 0)
  have hW_sq_le : (∑ v : Fin r → F, sgn (qh v + dotProduct ah v)) ^ 2 ≤
      (2 : ℤ) ^ r * (radical_h.card : ℤ) := by
    change (∑ v : Fin r → F, (if qh v + dotProduct ah v = 0 then (1 : ℤ) else -1)) ^ 2 ≤ _
    rw [hwalsh]; split_ifs
    · exact le_rfl
    · positivity
  let R_U : Submodule F U := {
    carrier := {u | ∀ u' : U, dotProduct u'.val (MS_lin k hk S u.val) = 0}, add_mem' := fun {a b} ha hb u' => by
      change dotProduct u'.val (MS_lin k hk S (a.val + b.val)) = 0
      rw [map_add, dot_add_right, ha u', hb u', add_zero]
    zero_mem' := fun u' => by simp [dotProduct]
    smul_mem' := fun c {a} ha u' => by
      change dotProduct u'.val (MS_lin k hk S (c • a.val)) = 0
      rw [map_smul, dotProduct_smul, ha u', smul_zero]
  }
  have hrad_card : radical_h.card = Fintype.card R_U := by
    rw [← Finset.card_univ]
    refine Finset.card_bij
      (fun v hv => ⟨e v, fun u' => by
        have hpol0 := (Finset.mem_filter.1 hv).2 (e.symm u')
        have hsymm : qh (e.symm u' + v) + qh (e.symm u') + qh v + qh 0 = 0 := by
          rw [add_comm]; convert hpol0 using 1; ring
        rw [hpol_h, e.apply_symm_apply] at hsymm; exact hsymm⟩)
      (fun _ _ => Finset.mem_univ _)
      (fun a _ b _ h => e.injective (congrArg Subtype.val h))
      (fun u _ => ⟨e.symm u.val, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun w => by
        rw [hpol_h, e.apply_symm_apply]
        have hpol_symm : dotProduct u.val.val (MS_lin k hk S (e w).val) =
            dotProduct (e w).val (MS_lin k hk S u.val.val) := by
          rw [← polar_qS_eq k hk S, ← polar_qS_eq k hk S, add_comm]; ring
        rw [hpol_symm]; exact u.property (e w)⟩,
        Subtype.ext (e.apply_symm_apply u.val)⟩)
  have hU_card : Fintype.card U = 2 ^ r := by
    rw [← card_vec r]; exact Fintype.card_congr e.symm.toEquiv
  have hprod_le : 2 ^ r * radical_h.card ≤ (2 ^ (k - p)) ^ 2 := by
    rw [← hU_card, hrad_card]
    have hbound := card_U_mul_rad_le (MS_lin k hk S) U
    rw [hker_Fintype] at hbound
    calc Fintype.card U * Fintype.card R_U
        ≤ 2 ^ (k - 2 * p) * 2 ^ k := hbound
      _ = 2 ^ ((k - 2 * p) + k) := (pow_add 2 _ _).symm
      _ = 2 ^ (2 * (k - p)) := by congr 1; omega
      _ = (2 ^ (k - p)) ^ 2 := by rw [mul_comm, pow_mul]
  have hsgn_sum : (∑ v : Fin r → F, sgn (qh v + dotProduct ah v + bh)) =
      sgn bh * (∑ v : Fin r → F, sgn (qh v + dotProduct ah v)) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun v _ => by rw [sgn_add, mul_comm]
  have hdiff := sum_sgn_eq_two_mul_card_sub (fun v : Fin r → F => qh v + dotProduct ah v + bh)
  rw [card_vec r, ← hHh_card, hsgn_sum] at hdiff
  have hsq_eq : (2 * (Hh.card : ℤ) - ((2 ^ r : ℕ) : ℤ)) ^ 2 =
      (∑ v : Fin r → F, sgn (qh v + dotProduct ah v)) ^ 2 := by
    rw [← hdiff, mul_pow]
    have h1 : (sgn bh) ^ 2 = 1 := by rw [sq, sgn_sq]
    rw [h1, one_mul]
  have hsq_le : (2 * (Hh.card : ℤ) - ((2 ^ r : ℕ) : ℤ)) ^ 2 ≤ ((2 ^ (k - p) : ℕ) : ℤ) ^ 2 := by
    rw [hsq_eq]
    have hcast : (2 : ℤ) ^ r * (radical_h.card : ℤ) ≤ ((2 ^ (k - p) : ℕ) : ℤ) ^ 2 := by
      exact_mod_cast hprod_le
    exact le_trans hW_sq_le hcast
  have hlin_le : (2 * (Hh.card : ℤ)) ≤ ((2 ^ r : ℕ) : ℤ) + ((2 ^ (k - p) : ℕ) : ℤ) := by nlinarith
  rw [hLh_card]
  exact_mod_cast hlin_le

private lemma upper_bound_qS (k : ℕ) (hk : 0 < k) (S : Finset (Fin k)) (p d : ℕ)
    (h2pk : 2 * p ≤ k)
    (hker_card : (Finset.univ.filter (fun v : Fin k → F => MS_lin k hk S v = 0)).card = 2 ^ (k - 2 * p))
    (ask : Fin d → ℕ → ((Fin k → F) →ₗ[F] F))
    (pred : ℕ → ((Fin k → F) →ₗ[F] F)) (bias : ℕ → F) :
    ((Finset.univ : Finset (Fin k → F)).filter (fun x =>
      qS k hk S x = pred (runAux ask (List.finRange d) x) x +
        bias (runAux ask (List.finRange d) x))).card ≤ (2 ^ k + 2 ^ (k - (p - d))) / 2 := by
  have hker_Fintype : Fintype.card (LinearMap.ker (MS_lin k hk S)) = 2 ^ (k - 2 * p) := by
    rw [← hker_card, ← Finset.card_univ]
    refine Finset.card_bij (fun u _ => u.val)
      (fun u _ => Finset.mem_filter.2 ⟨Finset.mem_univ _, u.property⟩)
      (fun a _ b _ h => Subtype.ext h)
      (fun v hv => ⟨⟨v, (Finset.mem_filter.1 hv).2⟩, Finset.mem_univ _, rfl⟩)
  by_cases hpd : p ≤ d
  · have hsub : p - d = 0 := Nat.sub_eq_zero_of_le hpd
    rw [hsub, Nat.sub_zero]
    have hcap : (2 ^ k + 2 ^ k) / 2 = 2 ^ k := by omega
    rw [hcap]
    calc _ ≤ (Finset.univ : Finset (Fin k → F)).card := Finset.card_filter_le _ _
      _ = 2 ^ k := card_finset_univ_vec k
  · have hdp : d < p := by omega
    let run := fun x => runAux ask (List.finRange d) x
    have hrun_lt : ∀ x : Fin k → F, run x < 2 ^ d := fun x => by
      simpa [run, List.length_finRange] using runAux_lt ask (List.finRange d) x
    let hitSet := (Finset.univ : Finset (Fin k → F)).filter
      (fun x => qS k hk S x = pred (run x) x + bias (run x))
    have hhit_part := Finset.card_eq_sum_card_fiberwise (f := run)
      (s := hitSet) (t := Finset.range (2 ^ d))
      (fun x _ => Finset.mem_range.2 (hrun_lt x))
    have hall_part := Finset.card_eq_sum_card_fiberwise (f := run)
      (s := (Finset.univ : Finset (Fin k → F))) (t := Finset.range (2 ^ d))
      (fun x _ => Finset.mem_range.2 (hrun_lt x))
    rw [card_finset_univ_vec k] at hall_part
    have h2hit : 2 * hitSet.card ≤ 2 ^ k + 2 ^ (k - (p - d)) := by
      calc 2 * hitSet.card
          = ∑ h ∈ Finset.range (2 ^ d), 2 * (hitSet.filter (fun x => run x = h)).card := by
              rw [hhit_part, Finset.mul_sum]
        _ ≤ ∑ h ∈ Finset.range (2 ^ d),
              (((Finset.univ : Finset (Fin k → F)).filter (fun x => run x = h)).card + 2 ^ (k - p)) := by
              refine Finset.sum_le_sum fun h _ => ?_
              let Lh := (Finset.univ : Finset (Fin k → F)).filter (fun x => run x = h)
              have heq_f : hitSet.filter (fun x => run x = h) =
                  Lh.filter (fun x => qS k hk S x = pred h x + bias h) := by
                ext x; simp only [hitSet, Lh, Finset.mem_filter, Finset.mem_univ, true_and]
                constructor
                · rintro ⟨hq, hr⟩; rw [hr] at hq; exact ⟨hr, hq⟩
                · rintro ⟨hr, hq⟩; rw [hr]; exact ⟨hq, rfl⟩
              rw [heq_f]
              by_cases hne : Lh.Nonempty
              · obtain ⟨x₀, hx₀⟩ := hne
                obtain ⟨U, hU⟩ := runAux_leaf_subspace ask (List.finRange d) x₀
                have hx₀_run : run x₀ = h := (Finset.mem_filter.1 hx₀).2
                have hLh_iff : ∀ x, x ∈ Lh ↔ x + x₀ ∈ U := fun x => by
                  simp only [Lh, Finset.mem_filter, Finset.mem_univ, true_and, run, ← hx₀_run]; exact hU x
                exact upper_bound_leaf k hk S p h2pk hker_Fintype Lh x₀ U hLh_iff (pred h) (bias h)
              · rw [Finset.not_nonempty_iff_eq_empty] at hne
                rw [hne]; simp
        _ = (∑ h ∈ Finset.range (2 ^ d),
              ((Finset.univ : Finset (Fin k → F)).filter (fun x => run x = h)).card) +
            (∑ _h ∈ Finset.range (2 ^ d), 2 ^ (k - p)) := Finset.sum_add_distrib
        _ = 2 ^ k + 2 ^ d * 2 ^ (k - p) := by
              rw [← hall_part, Finset.sum_const, Finset.card_range, smul_eq_mul]
        _ = 2 ^ k + 2 ^ (k - (p - d)) := by rw [← pow_add]; congr 2; omega
    change hitSet.card ≤ (2 ^ k + 2 ^ (k - (p - d))) / 2
    omega

-- Section 6: Achievability (∃ ask pred bias, cap ≤ hits)

private lemma polar_of_decomp {k p : ℕ} (q : (Fin k → F) → F)
    (A B : Fin p → (Fin k → F) →ₗ[F] F) (L₀ : (Fin k → F) →ₗ[F] F) (e₀ : F)
    (hq : ∀ v : Fin k → F, q v = L₀ v + e₀ + ∑ i : Fin p, A i v * B i v)
    (u v : Fin k → F) :
    q (u + v) + q u + q v + q 0 = ∑ i : Fin p, (A i u * B i v + A i v * B i u) := by
  rw [hq (u + v), hq u, hq v, hq 0]
  simp only [map_add, map_zero, zero_mul, Finset.sum_const_zero, zero_add, add_zero]
  have hlin : (L₀ u + L₀ v + e₀) + (L₀ u + e₀) + (L₀ v + e₀) + e₀ = 0 := z2_four_lin (L₀ u) (L₀ v) e₀
  have hquad :
      (∑ i : Fin p, (A i u + A i v) * (B i u + B i v)) + (∑ i : Fin p, A i u * B i u) +
      (∑ i : Fin p, A i v * B i v) = ∑ i : Fin p, (A i u * B i v + A i v * B i u) := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => z2_polar_prod (A i u) (A i v) (B i u) (B i v)
  let s1 := ∑ i : Fin p, (A i u + A i v) * (B i u + B i v)
  let s2 := ∑ i : Fin p, A i u * B i u
  let s3 := ∑ i : Fin p, A i v * B i v
  calc (L₀ u + L₀ v + e₀ + s1) + (L₀ u + e₀ + s2) + (L₀ v + e₀ + s3) + e₀
      = ((L₀ u + L₀ v + e₀) + (L₀ u + e₀) + (L₀ v + e₀) + e₀) + (s1 + s2 + s3) := by ring
    _ = ∑ i : Fin p, (A i u * B i v + A i v * B i u) := by rw [hlin, zero_add]; exact hquad

private lemma achievability_leaf (k : ℕ) (hk : 0 < k) (S : Finset (Fin k)) (p d : ℕ)
    (A B : Fin p → (Fin k → F) →ₗ[F] F) (L₀ : (Fin k → F) →ₗ[F] F) (e₀ : F)
    (hq_decomp : ∀ v : Fin k → F, qS k hk S v = L₀ v + e₀ + ∑ i : Fin p, A i v * B i v)
    (Lh : Finset (Fin k → F)) (x₀ : Fin k → F) (U : Submodule F (Fin k → F))
    (hLh_iff : ∀ x : Fin k → F, x ∈ Lh ↔ x + x₀ ∈ U)
    (hA_zero : ∀ (i : Fin p) (_hi : i.val < d) (u : U), A i u.val = 0) :
    let t := p - d
    ∃ (pr : (Fin k → F) →ₗ[F] F) (bi : F),
      (2 ^ t + 1) * Lh.card ≤
        2 ^ t * (2 * (Lh.filter (fun x => qS k hk S x = pr x + bi)).card) := by
  intro t
  obtain ⟨r, ⟨e⟩⟩ := subspace_equiv_fin U
  have hLh_card : Lh.card = 2 ^ r := by
    rw [← card_finset_univ_vec r]
    refine Finset.card_bij (fun x hx => e.symm ⟨x + x₀, (hLh_iff x).1 hx⟩)
      (fun _ _ => Finset.mem_univ _)
      (fun x1 _ x2 _ heq => by
        have h1 := congrArg (fun z => (e z).val) heq
        simp only [LinearEquiv.apply_symm_apply] at h1
        simpa [vec_add_cancel_right] using congrArg (fun z => z + x₀) h1)
      (fun v _ => ⟨x₀ + (e v).val,
        (hLh_iff _).2 (by rw [add_comm x₀, vec_add_cancel_right]; exact (e v).property),
        by apply e.injective; simp only [LinearEquiv.apply_symm_apply]; apply Subtype.ext; change (x₀ + (e v).val) + x₀ = (e v).val; rw [add_comm x₀, vec_add_cancel_right]⟩)
  let qh : (Fin r → F) → F := fun v => qS k hk S (x₀ + (e v).val)
  have hpol_h_eq : ∀ u v : Fin r → F,
      qh (u + v) + qh u + qh v + qh 0 =
        ∑ j : Fin t,
          (A ⟨d + j.val, by omega⟩ (e u).val * B ⟨d + j.val, by omega⟩ (e v).val +
           A ⟨d + j.val, by omega⟩ (e v).val * B ⟨d + j.val, by omega⟩ (e u).val) := by
    intro u v
    have h1 : qh (u + v) + qh u + qh v + qh 0 = dotProduct (e u).val (MS_lin k hk S (e v).val) := by
      dsimp only [qh]
      have hadd : (e (u + v)).val = (e u).val + (e v).val := by rw [map_add]; rfl
      have hzero : (e 0).val = 0 := by rw [map_zero]; rfl
      rw [hadd, hzero, add_zero]
      exact polar_translate (polar_qS_eq k hk S) x₀ (e u).val (e v).val
    rw [h1, ← polar_qS_eq k hk S, polar_of_decomp (qS k hk S) A B L₀ e₀ hq_decomp]
    symm
    trans (∑ i ∈ (Finset.univ : Finset (Fin p)).filter (fun i : Fin p => d ≤ i.val),
        (A i (e u).val * B i (e v).val + A i (e v).val * B i (e u).val))
    · refine Finset.sum_bij (fun j _ => (⟨d + j.val, by have := j.isLt; dsimp [t] at *; omega⟩ : Fin p))
        (fun j _ => Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp⟩)
        (fun a _ b _ h => Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega))
        (fun i hi => ⟨⟨i.val - d, by have := i.isLt; have := (Finset.mem_filter.1 hi).2; dsimp [t]; omega⟩,
          Finset.mem_univ _, Fin.ext (by have := (Finset.mem_filter.1 hi).2; dsimp; omega)⟩)
        (fun _ _ => rfl)
    · refine Finset.sum_subset (Finset.filter_subset _ _) fun i _ hi => ?_
      have hlt : i.val < d := by
        rw [Finset.mem_filter] at hi; simp only [Finset.mem_univ, true_and] at hi; omega
      rw [hA_zero i hlt (e u), hA_zero i hlt (e v), zero_mul, zero_mul, add_zero]
  have hpol_lin : ∀ u v w : Fin r → F,
      (qh (u + (v + w)) + qh u + qh (v + w) + qh 0) =
        (qh (u + v) + qh u + qh v + qh 0) + (qh (u + w) + qh u + qh w + qh 0) := by
    intro u v w; rw [hpol_h_eq, hpol_h_eq, hpol_h_eq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hadd : (e (v + w)).val = (e v).val + (e w).val := by rw [map_add]; rfl
    rw [hadd, map_add, map_add]; ring
  let radical_h := (Finset.univ : Finset (Fin r → F)).filter
    (fun u : Fin r → F => ∀ w : Fin r → F, qh (u + w) + qh u + qh w + qh 0 = 0)
  let Psi : (Fin r → F) →ₗ[F] (Fin t → F × F) := {
    toFun := fun u j => (A ⟨d + j.val, by omega⟩ (e u).val, B ⟨d + j.val, by omega⟩ (e u).val)
    map_add' := fun u1 u2 => funext fun j => by
      have hadd : (e (u1 + u2)).val = (e u1).val + (e u2).val := by rw [map_add]; rfl
      apply Prod.ext <;> simp [hadd, map_add]
    map_smul' := fun c u => funext fun j => by
      have hsm : (e (c • u)).val = c • (e u).val := by rw [map_smul]; rfl
      apply Prod.ext <;> simp [hsm, map_smul]
  }
  have hker_le_rad : Fintype.card (LinearMap.ker Psi) ≤ radical_h.card := by
    rw [← Finset.card_univ]
    refine Finset.card_le_card_of_injOn (fun u => u.val)
      (fun u _ => Finset.mem_filter.2 ⟨Finset.mem_univ _, fun w => by
        rw [hpol_h_eq]
        refine Finset.sum_eq_zero fun j _ => ?_
        have hj := congrFun u.property j
        have hA0 : A ⟨d + j.val, by omega⟩ (e u.val).val = 0 := congrArg Prod.fst hj
        have hB0 : B ⟨d + j.val, by omega⟩ (e u.val).val = 0 := congrArg Prod.snd hj
        change A ⟨d + j.val, by omega⟩ (e u.val).val * B ⟨d + j.val, by omega⟩ (e w).val +
          A ⟨d + j.val, by omega⟩ (e w).val * B ⟨d + j.val, by omega⟩ (e u.val).val = 0
        rw [hA0, hB0, zero_mul, mul_zero, add_zero]⟩)
      (fun _ _ _ _ h => Subtype.ext h)
  have hrad_lower : 2 ^ r ≤ radical_h.card * 2 ^ (2 * t) := by
    have h1 := card_le_ker_mul_codomain Psi
    rw [card_vec r] at h1
    have hcod : Fintype.card (Fin t → F × F) = 2 ^ (2 * t) := by
      rw [Fintype.card_fun, Fintype.card_prod, ZMod.card, Fintype.card_fin]
      calc (2 * 2) ^ t = (2 ^ 2) ^ t := by norm_num
        _ = 2 ^ (2 * t) := (pow_mul 2 2 t).symm
    rw [hcod] at h1
    exact le_trans h1 (Nat.mul_le_mul_right _ hker_le_rad)
  let R_sub : Submodule F (Fin r → F) := {
    carrier := {u | ∀ w : Fin r → F, qh (u + w) + qh u + qh w + qh 0 = 0}, add_mem' := fun {u1 u2} hu1 hu2 w => by
      have hsym : ∀ a b, qh (a + b) + qh a + qh b + qh 0 = qh (b + a) + qh b + qh a + qh 0 :=
        fun a b => by rw [add_comm a b]; ring
      rw [hsym (u1 + u2) w, hpol_lin w u1 u2, hsym w u1, hsym w u2, hu1 w, hu2 w, add_zero]
    zero_mem' := fun w => by
      rw [zero_add]
      have h1 : qh w + qh w = 0 := z2_add_self _
      have h2 : qh 0 + qh 0 = 0 := z2_add_self _
      calc qh w + qh 0 + qh w + qh 0 = (qh w + qh w) + (qh 0 + qh 0) := by ring
        _ = 0 := by rw [h1, h2, add_zero]
    smul_mem' := fun c {u} hu w => by
      rcases z2_eq_zero_or_one c with rfl | rfl
      · simp only [zero_smul, zero_add]
        have h1 : qh w + qh w = 0 := z2_add_self _
        have h2 : qh 0 + qh 0 = 0 := z2_add_self _
        calc qh w + qh 0 + qh w + qh 0 = (qh w + qh w) + (qh 0 + qh 0) := by ring
          _ = 0 := by rw [h1, h2, add_zero]
      · simpa using hu w
  }
  have hphi_add : ∀ u1 u2 : R_sub,
      (qh (u1 + u2).val + qh 0) = (qh u1.val + qh 0) + (qh u2.val + qh 0) := by
    intro u1 u2
    have hp0 : qh (u1.val + u2.val) + qh u1.val + qh u2.val + qh 0 = 0 := u1.property u2.val
    have h0 : qh 0 + qh 0 = 0 := z2_add_self _
    have h1 : (qh (u1.val + u2.val) + qh 0) + ((qh u1.val + qh 0) + (qh u2.val + qh 0)) = 0 := by
      calc (qh (u1.val + u2.val) + qh 0) + ((qh u1.val + qh 0) + (qh u2.val + qh 0))
          = (qh (u1.val + u2.val) + qh u1.val + qh u2.val + qh 0) + (qh 0 + qh 0) := by ring
        _ = 0 := by rw [hp0, h0, add_zero]
    exact (z2_add_eq_zero_iff _ _).1 h1
  obtain ⟨phiR, hphiR⟩ := add_to_linearMap (fun u : R_sub => qh u.val + qh 0) hphi_add
  obtain ⟨Phi_r, hPhi_r⟩ := LinearMap.exists_extend phiR
  obtain ⟨ah, hah⟩ := linearMap_eq_dotProduct Phi_r
  have hah_rad : ∀ u ∈ radical_h, qh u + qh 0 = dotProduct ah u := by
    intro u hu
    have huR : u ∈ R_sub := (Finset.mem_filter.1 hu).2
    have h1 : Phi_r u = phiR ⟨u, huR⟩ := by simpa using congrArg (fun f => f ⟨u, huR⟩) hPhi_r
    rw [← hah u, h1, hphiR ⟨u, huR⟩]
  obtain ⟨pr, hpr⟩ := LinearMap.exists_extend (Phi_r.comp e.symm.toLinearMap)
  have hpr_e : ∀ v : Fin r → F, pr (e v).val = dotProduct ah v := by
    intro v
    have h1 : pr (e v).val = (Phi_r.comp e.symm.toLinearMap) (e v) := by
      simpa using congrArg (fun f => f (e v)) hpr
    rw [h1]; simp [hah v]
  have hwalsh := PEqualNP.Outside.L_lib_420 r qh hpol_lin ah
  dsimp only at hwalsh
  let Wsum : ℤ := ∑ v : Fin r → F, sgn (qh v + dotProduct ah v)
  have hW_sq : Wsum ^ 2 = (2 : ℤ) ^ r * (radical_h.card : ℤ) := by
    change (∑ v : Fin r → F, (if qh v + dotProduct ah v = 0 then (1 : ℤ) else -1)) ^ 2 = _
    rw [hwalsh, if_pos hah_rad]
  have hW_scaled : ((2 : ℤ) ^ t * Wsum) ^ 2 ≥ ((2 : ℤ) ^ r) ^ 2 := by
    have hcast : ((2 : ℤ) ^ r) ≤ (radical_h.card : ℤ) * (2 : ℤ) ^ (2 * t) := by exact_mod_cast hrad_lower
    calc ((2 : ℤ) ^ t * Wsum) ^ 2
        = (2 : ℤ) ^ (2 * t) * Wsum ^ 2 := by rw [mul_pow, ← pow_mul, mul_comm t 2]
      _ = (2 : ℤ) ^ r * ((radical_h.card : ℤ) * (2 : ℤ) ^ (2 * t)) := by rw [hW_sq]; ring
      _ ≥ (2 : ℤ) ^ r * (2 : ℤ) ^ r := mul_le_mul_of_nonneg_left hcast (by positivity)
      _ = ((2 : ℤ) ^ r) ^ 2 := by ring
  let bi : F := if 0 ≤ Wsum then pr x₀ else pr x₀ + 1
  refine ⟨pr, bi, ?_⟩
  let bh : F := pr x₀ + bi
  have hsgn_W : (2 : ℤ) ^ r ≤ (2 : ℤ) ^ t * (sgn bh * Wsum) := by
    have h2t_pos : (0 : ℤ) < (2 : ℤ) ^ t := by positivity
    have h2r_nonneg : (0 : ℤ) ≤ (2 : ℤ) ^ r := by positivity
    by_cases hW0 : 0 ≤ Wsum
    · have hbh : bh = 0 := by dsimp [bh, bi]; rw [if_pos hW0, z2_add_self]
      rw [hbh, sgn_zero, one_mul]
      exact le_of_sq_le_sq_nonneg (mul_nonneg (le_of_lt h2t_pos) hW0) h2r_nonneg hW_scaled
    · have hbh : bh = 1 := by dsimp [bh, bi]; rw [if_neg hW0, ← add_assoc, z2_add_self, zero_add]
      rw [hbh, sgn_one]
      have hneg_sq : ((2 : ℤ) ^ t * (-1 * Wsum)) ^ 2 = ((2 : ℤ) ^ t * Wsum) ^ 2 := by ring
      exact le_of_sq_le_sq_nonneg (mul_nonneg (le_of_lt h2t_pos) (by linarith)) h2r_nonneg (hneg_sq.symm ▸ hW_scaled)
  have hHh_card : (Lh.filter (fun x => qS k hk S x = pr x + bi)).card =
      ((Finset.univ : Finset (Fin r → F)).filter (fun v => qh v + dotProduct ah v + bh = 0)).card := by
    refine Finset.card_bij (fun x hx => e.symm ⟨x + x₀, (hLh_iff x).1 (Finset.mem_filter.1 hx).1⟩)
      (fun x hx => by
        rw [Finset.mem_filter] at hx ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        let v := e.symm ⟨x + x₀, (hLh_iff x).1 hx.1⟩
        have hev : (e v).val = x + x₀ := congrArg Subtype.val (e.apply_symm_apply _)
        have hxv : x₀ + (e v).val = x := by rw [hev, add_comm x₀, vec_add_cancel_right]
        dsimp only [qh, bh]; rw [hxv, ← hpr_e v, hev, map_add, hx.2]
        exact z2_cancel3 (pr x) bi (pr x₀))
      (fun x1 _ x2 _ heq => by
        have h1 := congrArg (fun z => (e z).val) heq
        simp only [LinearEquiv.apply_symm_apply] at h1
        simpa [vec_add_cancel_right] using congrArg (fun z => z + x₀) h1)
      (fun v hv => by
        rw [Finset.mem_filter] at hv
        let x := x₀ + (e v).val
        have hxL : x ∈ Lh := (hLh_iff x).2 (by dsimp [x]; rw [add_comm x₀, vec_add_cancel_right]; exact (e v).property)
        refine ⟨x, Finset.mem_filter.2 ⟨hxL, ?_⟩, ?_⟩
        · have hprx : pr x = pr x₀ + dotProduct ah v := by dsimp [x]; rw [map_add, hpr_e v]
          rw [hprx]; apply (z2_add_eq_zero_iff _ _).1
          have hv0 := hv.2; dsimp only [qh, bh] at hv0
          calc qS k hk S x + (pr x₀ + dotProduct ah v + bi)
              = qS k hk S (x₀ + (e v).val) + dotProduct ah v + (pr x₀ + bi) := by ring
            _ = 0 := hv0
        · apply e.injective; simp only [LinearEquiv.apply_symm_apply]; apply Subtype.ext
          dsimp [x]; rw [add_comm x₀, vec_add_cancel_right])
  have hsgn_sum : (∑ v : Fin r → F, sgn (qh v + dotProduct ah v + bh)) = sgn bh * Wsum := by
    dsimp only [Wsum]; rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => by rw [sgn_add, mul_comm]
  have hdiff := sum_sgn_eq_two_mul_card_sub (fun v : Fin r → F => qh v + dotProduct ah v + bh)
  rw [card_vec r, ← hHh_card, hsgn_sum] at hdiff
  have hineqZ : ((2 : ℤ) ^ t + 1) * ((2 ^ r : ℕ) : ℤ) ≤
      (2 : ℤ) ^ t * (2 * ((Lh.filter (fun x => qS k hk S x = pr x + bi)).card : ℤ)) := by
    rw [hdiff] at hsgn_W
    push_cast at hsgn_W ⊢
    linarith
  rw [hLh_card]
  exact_mod_cast hineqZ

private lemma achievability_qS (k : ℕ) (hk : 0 < k) (S : Finset (Fin k)) (p d : ℕ)
    (h2pk : 2 * p ≤ k)
    (A B : Fin p → (Fin k → F) →ₗ[F] F) (L₀ : (Fin k → F) →ₗ[F] F) (e₀ : F)
    (hq_decomp : ∀ v : Fin k → F, qS k hk S v = L₀ v + e₀ + ∑ i : Fin p, A i v * B i v) :
    ∃ (ask : Fin d → ℕ → ((Fin k → F) →ₗ[F] F))
      (pred : ℕ → ((Fin k → F) →ₗ[F] F)) (bias : ℕ → F),
      (2 ^ k + 2 ^ (k - (p - d))) / 2 ≤
        ((Finset.univ : Finset (Fin k → F)).filter (fun x =>
          qS k hk S x = pred (runAux ask (List.finRange d) x) x +
            bias (runAux ask (List.finRange d) x))).card := by
  let fAsk : Fin d → ((Fin k → F) →ₗ[F] F) := fun j => if hj : j.val < p then A ⟨j.val, hj⟩ else 0
  let ask : Fin d → ℕ → ((Fin k → F) →ₗ[F] F) := fun j _ => fAsk j
  let run : (Fin k → F) → ℕ := fun x => runAux ask (List.finRange d) x
  have hrun_lt : ∀ x : Fin k → F, run x < 2 ^ d := fun x => by
    simpa [run, List.length_finRange] using runAux_lt ask (List.finRange d) x
  let t : ℕ := p - d
  have hleaf_exists : ∀ h : ℕ,
      let Lh := (Finset.univ : Finset (Fin k → F)).filter (fun x => run x = h)
      ∃ (pr : (Fin k → F) →ₗ[F] F) (bi : F),
        (2 ^ t + 1) * Lh.card ≤
          2 ^ t * (2 * (Lh.filter (fun x => qS k hk S x = pr x + bi)).card) := by
    intro h Lh
    by_cases hne : Lh.Nonempty
    · obtain ⟨x₀, hx₀⟩ := hne
      have hx₀_run : run x₀ = h := (Finset.mem_filter.1 hx₀).2
      let U : Submodule F (Fin k → F) := ⨅ j : Fin d, LinearMap.ker (fAsk j)
      have hLh_iff : ∀ x : Fin k → F, x ∈ Lh ↔ x + x₀ ∈ U := by
        intro x
        simp only [Lh, Finset.mem_filter, Finset.mem_univ, true_and, run, ← hx₀_run]
        rw [runAux_nonadaptive_iff fAsk (List.finRange d) x x₀]
        simp only [U, Submodule.mem_iInf, LinearMap.mem_ker, map_add, z2_add_eq_zero_iff]
        exact ⟨fun hall j => hall j (List.mem_finRange j), fun hall j _ => hall j⟩
      have hA_zero : ∀ (i : Fin p) (_hi : i.val < d) (u : U), A i u.val = 0 := by
        intro i hi u
        have hu := (Submodule.mem_iInf _).1 u.property ⟨i.val, hi⟩
        rw [LinearMap.mem_ker] at hu
        dsimp only [fAsk] at hu
        rw [dif_pos i.isLt] at hu
        exact hu
      exact achievability_leaf k hk S p d A B L₀ e₀ hq_decomp Lh x₀ U hLh_iff hA_zero
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      exact ⟨0, 0, by rw [hne]; simp⟩
  let pred : ℕ → ((Fin k → F) →ₗ[F] F) := fun h => Classical.choose (hleaf_exists h)
  let bias : ℕ → F := fun h => Classical.choose (Classical.choose_spec (hleaf_exists h))
  have hleaf_ok : ∀ h : ℕ,
      let Lh := (Finset.univ : Finset (Fin k → F)).filter (fun x => run x = h)
      (2 ^ t + 1) * Lh.card ≤
        2 ^ t * (2 * (Lh.filter (fun x => qS k hk S x = pred h x + bias h)).card) :=
    fun h => Classical.choose_spec (Classical.choose_spec (hleaf_exists h))
  refine ⟨ask, pred, bias, ?_⟩
  let hitSet := (Finset.univ : Finset (Fin k → F)).filter
    (fun x => qS k hk S x = pred (run x) x + bias (run x))
  have hhit_part := Finset.card_eq_sum_card_fiberwise (f := run)
    (s := hitSet) (t := Finset.range (2 ^ d))
    (fun x _ => Finset.mem_range.2 (hrun_lt x))
  have hall_part := Finset.card_eq_sum_card_fiberwise (f := run)
    (s := (Finset.univ : Finset (Fin k → F))) (t := Finset.range (2 ^ d))
    (fun x _ => Finset.mem_range.2 (hrun_lt x))
  rw [card_finset_univ_vec k] at hall_part
  have hscaled : 2 ^ t * (2 ^ k + 2 ^ (k - t)) ≤ 2 ^ t * (2 * hitSet.card) := by
    have htk : t ≤ k := by omega
    have hlhs : 2 ^ t * (2 ^ k + 2 ^ (k - t)) = (2 ^ t + 1) * 2 ^ k := by
      rw [mul_add, ← pow_add 2 t (k - t), Nat.add_sub_of_le htk]; ring
    rw [hlhs, hall_part, Finset.mul_sum, hhit_part, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun h _ => ?_
    have heq_f : hitSet.filter (fun x => run x = h) =
        ((Finset.univ : Finset (Fin k → F)).filter (fun x => run x = h)).filter
          (fun x => qS k hk S x = pred h x + bias h) := by
      ext x; simp only [hitSet, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hq, hr⟩; rw [hr] at hq; exact ⟨hr, hq⟩
      · rintro ⟨hr, hq⟩; rw [hr]; exact ⟨hq, rfl⟩
    rw [heq_f]
    exact hleaf_ok h
  have h2t_pos : 0 < 2 ^ t := pow_pos (by omega) t
  have h2hit : 2 ^ k + 2 ^ (k - t) ≤ 2 * hitSet.card := Nat.le_of_mul_le_mul_left hscaled h2t_pos
  change (2 ^ k + 2 ^ (k - t)) / 2 ≤ hitSet.card
  omega

-- Section 7: Final transport back from qS to outFn

private lemma main_theorem_abs (k : ℕ) (hk : 0 < k) (hk3 : k % 3 ≠ 0)
    (spacing s t : ℕ) (name c : Fin k → F) (S : Finset (Fin k)) (d p_abs : ℕ)
    (hp_eq : p_abs = pCyc k hk S) :
    let run := fun (ask : Fin d → ℕ → ((Fin k → F) →ₗ[F] F)) (x : Fin k → F) =>
      (List.finRange d).foldl (fun h j =>
        2 * h + (if ask j h x = 0 then 0 else 1)) (0 : ℕ)
    let cap := (2 ^ k + 2 ^ (k - (p_abs - d))) / 2
    let hits := fun (ask : Fin d → ℕ → ((Fin k → F) →ₗ[F] F))
        (pred : ℕ → ((Fin k → F) →ₗ[F] F)) (bias : ℕ → F) =>
      ((Finset.univ : Finset (Fin k → F)).filter (fun x =>
        (∑ i ∈ S, outFn k hk spacing s t name c x i) =
          pred (run ask x) x + bias (run ask x))).card
    (∀ ask pred bias, hits ask pred bias ≤ cap) ∧
      (∃ ask pred bias, hits ask pred bias = cap) := by
  intro run cap hits
  have hcyc := cycle_main k hk S
  rw [← hp_eq] at hcyc
  obtain ⟨h2pk, hker_card, A, B, L₀, e₀, hq_decomp⟩ := hcyc
  let E : (Fin k → F) ≃ₗ[F] (Fin k → F) :=
    (rotEquiv k hk s).trans ((mixEquiv k hk hk3 spacing).trans (shift1Equiv k hk))
  obtain ⟨L_aff, c_aff, hout_eq⟩ := outSum_eq_qS_add_affine k hk hk3 spacing s t name c S
  have hrun_conj : ∀ (ask : Fin d → ℕ → ((Fin k → F) →ₗ[F] F)) (l : List (Fin d)) (x : Fin k → F),
      runAux (fun j h => (ask j h).comp E.symm.toLinearMap) l (E x) = runAux ask l x := by
    intro ask l x
    induction l using List.reverseRecOn with
    | nil => rfl
    | append_singleton l j ih =>
      simp only [runAux, List.foldl_append, List.foldl_cons, List.foldl_nil]
      change 2 * runAux (fun j h => (ask j h).comp E.symm.toLinearMap) l (E x) +
          (if ask j (runAux (fun j h => (ask j h).comp E.symm.toLinearMap) l (E x)) (E.symm (E x)) = 0 then 0 else 1) =
        2 * runAux ask l x + (if ask j (runAux ask l x) x = 0 then 0 else 1)
      rw [ih, E.symm_apply_apply]
  have hhits_eq : ∀ ask pred bias,
      let ask' := fun j h => (ask j h).comp E.symm.toLinearMap
      let pred' := fun h => (pred h + L_aff).comp E.symm.toLinearMap
      let bias' := fun h => bias h + c_aff
      hits ask pred bias =
        ((Finset.univ : Finset (Fin k → F)).filter (fun v =>
          qS k hk S v = pred' (runAux ask' (List.finRange d) v) v +
            bias' (runAux ask' (List.finRange d) v))).card := by
    intro ask pred bias ask' pred' bias'
    refine Finset.card_bij (fun x _ => E x)
      (fun x hx => by
        rw [Finset.mem_filter] at hx ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        have hr : runAux ask' (List.finRange d) (E x) = run ask x := hrun_conj ask (List.finRange d) x
        rw [hr]
        have hx_eq := hx.2
        rw [hout_eq x] at hx_eq
        change qS k hk S (E x) = (pred (run ask x) (E.symm (E x)) + L_aff (E.symm (E x))) + (bias (run ask x) + c_aff)
        rw [E.symm_apply_apply]
        have h1 : L_aff x + L_aff x = 0 := z2_add_self _
        have h2 : c_aff + c_aff = 0 := z2_add_self _
        calc qS k hk S (E x)
            = (qS k hk S (E x) + L_aff x + c_aff) + L_aff x + c_aff := by
                calc qS k hk S (E x) = qS k hk S (E x) + (L_aff x + L_aff x) + (c_aff + c_aff) := by
                      rw [h1, h2, add_zero, add_zero]
                  _ = _ := by ring
          _ = (pred (run ask x) x + bias (run ask x)) + L_aff x + c_aff := by rw [hx_eq]
          _ = (pred (run ask x) x + L_aff x) + (bias (run ask x) + c_aff) := by ring)
      (fun _ _ _ _ h => E.injective h)
      (fun v hv => by
        rw [Finset.mem_filter] at hv
        refine ⟨E.symm v, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, E.apply_symm_apply v⟩
        have hr : runAux ask' (List.finRange d) v = run ask (E.symm v) := by
          have := hrun_conj ask (List.finRange d) (E.symm v)
          rw [E.apply_symm_apply] at this
          exact this
        have hv_eq := hv.2
        rw [hr] at hv_eq
        rw [hout_eq (E.symm v), E.apply_symm_apply, hv_eq]
        change (pred (run ask (E.symm v)) (E.symm v) + L_aff (E.symm v)) +
            (bias (run ask (E.symm v)) + c_aff) + L_aff (E.symm v) + c_aff =
          pred (run ask (E.symm v)) (E.symm v) + bias (run ask (E.symm v))
        have h1 : L_aff (E.symm v) + L_aff (E.symm v) = 0 := z2_add_self _
        have h2 : c_aff + c_aff = 0 := z2_add_self _
        calc (pred (run ask (E.symm v)) (E.symm v) + L_aff (E.symm v)) +
              (bias (run ask (E.symm v)) + c_aff) + L_aff (E.symm v) + c_aff
            = pred (run ask (E.symm v)) (E.symm v) + bias (run ask (E.symm v)) +
              (L_aff (E.symm v) + L_aff (E.symm v)) + (c_aff + c_aff) := by ring
          _ = pred (run ask (E.symm v)) (E.symm v) + bias (run ask (E.symm v)) := by
              rw [h1, h2, add_zero, add_zero])
  have hub : ∀ ask pred bias, hits ask pred bias ≤ cap := by
    intro ask pred bias
    rw [hhits_eq ask pred bias]
    exact upper_bound_qS k hk S p_abs d h2pk hker_card
      (fun j h => (ask j h).comp E.symm.toLinearMap)
      (fun h => (pred h + L_aff).comp E.symm.toLinearMap)
      (fun h => bias h + c_aff)
  refine ⟨hub, ?_⟩
  obtain ⟨ask', pred', bias', hlow⟩ := achievability_qS k hk S p_abs d h2pk A B L₀ e₀ hq_decomp
  let ask := fun j h => (ask' j h).comp E.toLinearMap
  let pred := fun h => (pred' h).comp E.toLinearMap + L_aff
  let bias := fun h => bias' h + c_aff
  refine ⟨ask, pred, bias, le_antisymm (hub ask pred bias) ?_⟩
  rw [hhits_eq ask pred bias]
  have hask_eq : (fun j h => (ask j h).comp E.symm.toLinearMap) = ask' := by
    funext j h; ext v; simp [ask]
  have hpred_eq : (fun h => (pred h + L_aff).comp E.symm.toLinearMap) = pred' := by
    funext h; ext v
    simp only [pred, LinearMap.comp_apply, LinearMap.add_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
    rw [add_assoc, z2_add_self, add_zero]
  have hbias_eq : (fun h => bias h + c_aff) = bias' := by
    funext h; dsimp only [bias]; rw [add_assoc, z2_add_self, add_zero]
  rw [hask_eq, hpred_eq, hbias_eq]
  exact hlow

private lemma main_theorem (k : ℕ) (hk : 0 < k) (hk3 : k % 3 ≠ 0)
    (spacing s t : ℕ) (name c : Fin k → F) (S : Finset (Fin k)) (d : ℕ) :
    let mu := (S.powerset.filter (fun E => ∀ i ∈ E, ix k hk (i.val + 1) ∉ E)).sup Finset.card
    let run := fun (ask : Fin d → ℕ → ((Fin k → F) →ₗ[F] F)) (x : Fin k → F) =>
      (List.finRange d).foldl (fun h j =>
        2 * h + (if ask j h x = 0 then 0 else 1)) (0 : ℕ)
    let p := if S = Finset.univ ∧ k % 2 = 0 then mu - 1 else mu
    let cap := (2 ^ k + 2 ^ (k - (p - d))) / 2
    let hits := fun (ask : Fin d → ℕ → ((Fin k → F) →ₗ[F] F))
        (pred : ℕ → ((Fin k → F) →ₗ[F] F)) (bias : ℕ → F) =>
      ((Finset.univ : Finset (Fin k → F)).filter (fun x =>
        (∑ i ∈ S, outFn k hk spacing s t name c x i) =
          pred (run ask x) x + bias (run ask x))).card
    (∀ ask pred bias, hits ask pred bias ≤ cap) ∧
      (∃ ask pred bias, hits ask pred bias = cap) := by
  intro mu run p cap hits
  have hp_def : p = pCyc k hk S := by
    have hmu_eq : mu = muCyc k hk S := by
      dsimp only [mu, muCyc]
      congr 1; ext E; simp [isIndepCyc]
    dsimp only [p, pCyc]
    rw [hmu_eq]
  exact main_theorem_abs k hk hk3 spacing s t name c S d p hp_def

end PEqualNP.Outside.L_meta_25737_aux

theorem PEqualNP.Outside.L_meta_25737 :
    ∀ (k : ℕ) (hk : 0 < k), k % 3 ≠ 0 →
  let F := ZMod 2
  let W := Fin k → F
  let D := W →ₗ[F] F
  let ix := fun z : ℕ => (⟨z % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (q : ℕ) (x : W) (i : Fin k) => x (ix (i.val + k - q % k))
  ∀ (spacing s t : ℕ) (name c : W) (S : Finset (Fin k)) (d : ℕ),
    let out := fun (x : W) (i : Fin k) =>
      let z := rot s x + name
      let y := fun j : Fin k =>
        z j + z (ix (j.val + spacing)) + z (ix (j.val + k - spacing % k))
      y i + (1 + y (ix (i.val + 1))) * y (ix (i.val + 2)) + rot t x i + c i
    let mu := (S.powerset.filter (fun E => ∀ i ∈ E, ix (i.val + 1) ∉ E)).sup Finset.card
    let run := fun (ask : Fin d → ℕ → D) (x : W) =>
      (List.finRange d).foldl (fun h j =>
        2 * h + (if ask j h x = 0 then 0 else 1)) (0 : ℕ)
    let p := if S = Finset.univ ∧ k % 2 = 0 then mu - 1 else mu
    let cap := (2 ^ k + 2 ^ (k - (p - d))) / 2
    let hits := fun (ask : Fin d → ℕ → D) (pred : ℕ → D) (bias : ℕ → F) =>
      ((Finset.univ : Finset W).filter (fun x =>
        (∑ i ∈ S, out x i) = pred (run ask x) x + bias (run ask x))).card
    (∀ ask pred bias, hits ask pred bias ≤ cap) ∧
      (∃ ask pred bias, hits ask pred bias = cap) := by
  intro k hk hk3 F W D ix rot spacing s t name c S d out mu run p cap hits
  exact PEqualNP.Outside.L_meta_25737_aux.main_theorem k hk hk3 spacing s t name c S d
