import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33630

noncomputable section

open Classical

def toZ2 (b : Bool) : ZMod 2 := if b then 1 else 0

lemma toZ2_false : toZ2 false = 0 := rfl
lemma toZ2_true : toZ2 true = 1 := rfl

lemma toZ2_xor (a b : Bool) : toZ2 (xor a b) = toZ2 a + toZ2 b := by
  cases a <;> cases b <;> decide

lemma toZ2_bne (a b : Bool) : toZ2 (a != b) = toZ2 a + toZ2 b := by
  cases a <;> cases b <;> decide

lemma toZ2_and (a b : Bool) : toZ2 (a && b) = toZ2 a * toZ2 b := by
  cases a <;> cases b <;> decide

lemma toZ2_inj : Function.Injective toZ2 := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

lemma toZ2_eq_zero_iff (b : Bool) : toZ2 b = 0 ↔ b = false := by
  cases b <;> decide

lemma toZ2_eq_one_iff (b : Bool) : toZ2 b = 1 ↔ b = true := by
  cases b <;> decide

lemma zmod2_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl hx
  · rfl

lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

lemma zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma testBit_add_two_pow_of_lt {a k : ℕ} (ha : a < 2 ^ k) (j : ℕ) :
    (a + 2 ^ k).testBit j = if j = k then true else a.testBit j := by
  by_cases hjk : j = k
  · subst hjk
    rw [if_pos rfl, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.add_div_right _ (Nat.two_pow_pos j),
      Nat.div_eq_of_lt ha]
    rfl
  · rw [if_neg hjk]
    by_cases hlt : j < k
    · rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
      have hpow : 2 ^ k = 2 ^ (k - j) * 2 ^ j := by rw [← pow_add, Nat.sub_add_cancel (le_of_lt hlt)]
      rw [hpow, Nat.add_mul_div_right _ _ (Nat.two_pow_pos j)]
      have heven : 2 ^ (k - j) = 2 * 2 ^ (k - j - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel (by omega)]
      rw [heven, Nat.and_comm 1 _, Nat.and_comm 1 _, Nat.and_one_is_mod, Nat.and_one_is_mod,
        Nat.add_mul_mod_self_left]
    · have hgt : k + 1 ≤ j := by omega
      have h1 : a + 2 ^ k < 2 ^ j :=
        lt_of_lt_of_le (by rw [pow_succ, mul_two]; omega) (Nat.pow_le_pow_right (by omega) hgt)
      have h2 : a < 2 ^ j := lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (by omega))
      rw [Nat.testBit_eq_false_of_lt h1, Nat.testBit_eq_false_of_lt h2]

def fromBits : ∀ (k : ℕ), (Fin k → ZMod 2) → Fin (2 ^ k)
  | 0, _ => ⟨0, Nat.one_pos⟩
  | k + 1, v =>
    let r := fromBits k (fun i => v i.castSucc)
    ⟨r.val + (if v (Fin.last k) = 0 then 0 else 2 ^ k), by
      have hr := r.isLt
      have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ, mul_two]
      split_ifs <;> omega⟩

lemma fromBits_testBit : ∀ (k : ℕ) (v : Fin k → ZMod 2) (j : ℕ),
    (fromBits k v).val.testBit j = if hj : j < k then decide (v ⟨j, hj⟩ ≠ 0) else false
  | 0, v, j => by simp [fromBits]
  | k + 1, v, j => by
    simp only [fromBits]
    have hr := (fromBits k (fun i => v i.castSucc)).isLt
    by_cases hlast : v (Fin.last k) = 0
    · rw [if_pos hlast, Nat.add_zero, fromBits_testBit k (fun i => v i.castSucc) j]
      by_cases hjk : j < k
      · rw [dif_pos hjk, dif_pos (Nat.lt_succ_of_lt hjk)]
        rfl
      · rw [dif_neg hjk]
        by_cases hjk1 : j < k + 1
        · rw [dif_pos hjk1]
          have hjeq : (⟨j, hjk1⟩ : Fin (k + 1)) = Fin.last k := Fin.ext (by simp only [Fin.val_last]; omega)
          rw [hjeq, hlast]
          simp
        · rw [dif_neg hjk1]
    · rw [if_neg hlast, testBit_add_two_pow_of_lt hr j, fromBits_testBit k (fun i => v i.castSucc) j]
      by_cases hjk : j < k
      · have hne : j ≠ k := by omega
        rw [if_neg hne, dif_pos hjk, dif_pos (Nat.lt_succ_of_lt hjk)]
        rfl
      · rw [dif_neg hjk]
        by_cases hjk1 : j < k + 1
        · have hjeq : j = k := by omega
          have hfin : (⟨j, hjk1⟩ : Fin (k + 1)) = Fin.last k := Fin.ext (by simp only [Fin.val_last]; omega)
          rw [if_pos hjeq, dif_pos hjk1, hfin]
          simp [hlast]
        · have hne : j ≠ k := by omega
          rw [if_neg hne, dif_neg hjk1]

def bitsEquiv (k : ℕ) : Fin (2 ^ k) ≃ (Fin k → ZMod 2) where
  toFun := fun x i => toZ2 (x.val.testBit i.val)
  invFun := fromBits k
  left_inv := fun x => by
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro j
    rw [fromBits_testBit]
    by_cases hj : j < k
    · rw [dif_pos hj]
      cases ht : x.val.testBit j <;> simp [toZ2, ht]
    · rw [dif_neg hj]
      exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le x.isLt
        (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_lt hj)))).symm
  right_inv := fun v => by
    funext i
    dsimp only
    rw [fromBits_testBit, dif_pos i.isLt]
    rcases zmod2_cases (v i) with h | h <;> simp [h, toZ2]

def dot {D : ℕ} (u v : Fin D → ZMod 2) : ZMod 2 := ∑ i : Fin D, u i * v i

lemma dot_comm {D : ℕ} (u v : Fin D → ZMod 2) : dot u v = dot v u := by
  simp only [dot, mul_comm]

lemma dot_add_right {D : ℕ} (u v1 v2 : Fin D → ZMod 2) : dot u (v1 + v2) = dot u v1 + dot u v2 := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma dot_add_left {D : ℕ} (u1 u2 v : Fin D → ZMod 2) : dot (u1 + u2) v = dot u1 v + dot u2 v := by
  simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma dot_zero_right {D : ℕ} (u : Fin D → ZMod 2) : dot u 0 = 0 := by
  simp [dot]

lemma dot_single_right {D : ℕ} (u : Fin D → ZMod 2) (j : Fin D) :
    dot u (Pi.single j 1) = u j := by
  simp only [dot]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij; simp [Pi.single_eq_of_ne hij]
  · intro h; exact absurd (Finset.mem_univ j) h

def dotLin {D : ℕ} (p : Fin D → ZMod 2) : (Fin D → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun := fun v => dot p v
  map_add' := fun v1 v2 => dot_add_right p v1 v2
  map_smul' := fun c v => by
    simp only [dot, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_left_comm, ← Finset.mul_sum]

def perpSub {D : ℕ} (U : Submodule (ZMod 2) (Fin D → ZMod 2)) :
    Submodule (ZMod 2) (Fin D → ZMod 2) :=
  { carrier := {p | ∀ u ∈ U, dot p u = 0}
    zero_mem' := fun _ _ => by simp [dot]
    smul_mem' := fun c _ ha u hu => by
      have h0 : ∑ i : Fin D, _ * u i = 0 := ha u hu
      simp only [dot, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
      rw [h0, mul_zero]
    , add_mem' := fun ha hb u hu => by
      rw [dot_add_left, ha u hu, hb u hu, add_zero] }

lemma finrank_perpSub {D : ℕ} (U : Submodule (ZMod 2) (Fin D → ZMod 2)) :
    Module.finrank (ZMod 2) (perpSub U) = D - Module.finrank (ZMod 2) U := by
  let Φ : (Fin D → ZMod 2) →ₗ[ZMod 2] (U →ₗ[ZMod 2] ZMod 2) :=
    { toFun := fun p =>
        { toFun := fun u => dot p u.1
          map_add' := fun u1 u2 => dot_add_right p u1.1 u2.1
          map_smul' := fun c u => by
            simp only [dot, Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul,
              RingHom.id_apply, mul_left_comm, ← Finset.mul_sum] }
      map_add' := fun p1 p2 => by
        ext u; exact dot_add_left p1 p2 u.1
      map_smul' := fun c p => by
        ext u
        simp only [dot, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, Pi.smul_apply,
          smul_eq_mul, RingHom.id_apply, mul_assoc, ← Finset.mul_sum] }
  have hker : LinearMap.ker Φ = perpSub U := by
    ext p
    simp only [LinearMap.mem_ker, perpSub, Submodule.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_setOf_eq, Φ]
    constructor
    · intro h u hu
      have h1 := LinearMap.congr_fun h ⟨u, hu⟩
      exact h1
    · intro h
      ext u
      exact h u.1 u.2
  have hsurj : Function.Surjective Φ := by
    intro f
    obtain ⟨g, hg⟩ := LinearMap.exists_extend f
    refine ⟨fun i => g (Pi.single i 1), ?_⟩
    ext ⟨u, hu⟩
    change ∑ i : Fin D, g (Pi.single i 1) * u i = f ⟨u, hu⟩
    have hgu : g u = f ⟨u, hu⟩ := by
      have := LinearMap.congr_fun hg ⟨u, hu⟩
      exact this
    rw [← hgu]
    conv_rhs => rw [← Finset.univ_sum_single u]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsm : Pi.single i (u i) = u i • (Pi.single i (1 : ZMod 2)) := by
      ext j
      by_cases hji : j = i
      · subst hji; simp
      · simp [Pi.single_eq_of_ne hji]
    rw [hsm, map_smul, smul_eq_mul, mul_comm]
  have hdim_range : Module.finrank (ZMod 2) (LinearMap.range Φ) = Module.finrank (ZMod 2) U := by
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top]
    exact Module.finrank_linearMap (ZMod 2) (ZMod 2) U (ZMod 2) |>.trans (by simp)
  have hrn := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hdim_range, hker, Module.finrank_fin_fun] at hrn
  omega

lemma card_submodule_eq_two_pow {D : ℕ} (U : Submodule (ZMod 2) (Fin D → ZMod 2)) :
    Nat.card U = 2 ^ Module.finrank (ZMod 2) U := by
  let e : (Fin (Module.finrank (ZMod 2) U) → ZMod 2) ≃ₗ[ZMod 2] U :=
    LinearEquiv.ofFinrankEq _ _ (by simp)
  rw [← Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_fun,
    ZMod.card, Fintype.card_fin]

lemma fiber_card_affine {q m : ℕ}
    (T : (Fin q → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)) (y0 y : Fin m → ZMod 2) :
    Nat.card {v : Fin q → ZMod 2 // T v + y0 = y} =
      if y - y0 ∈ LinearMap.range T then 2 ^ Module.finrank (ZMod 2) (LinearMap.ker T) else 0 := by
  by_cases hmem : y - y0 ∈ LinearMap.range T
  · rw [if_pos hmem]
    obtain ⟨v0, hv0⟩ := hmem
    let e : {v : Fin q → ZMod 2 // T v + y0 = y} ≃ LinearMap.ker T :=
      { toFun := fun v => ⟨v.1 - v0, by
          rw [LinearMap.mem_ker, map_sub, hv0]
          have h1 : T v.1 = y - y0 := eq_sub_of_add_eq v.2
          rw [h1, sub_self]⟩
        invFun := fun u => ⟨u.1 + v0, by
          rw [map_add, LinearMap.mem_ker.1 u.2, zero_add, hv0, sub_add_cancel]⟩
        left_inv := fun v => Subtype.ext (sub_add_cancel v.1 v0)
        right_inv := fun u => Subtype.ext (add_sub_cancel_right u.1 v0) }
    rw [Nat.card_congr e, card_submodule_eq_two_pow]
  · rw [if_neg hmem]
    haveI : IsEmpty {v : Fin q → ZMod 2 // T v + y0 = y} :=
      ⟨fun v => hmem ⟨v.1, eq_sub_of_add_eq v.2⟩⟩
    rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero]

lemma range_eq_top_of_perp_eq_bot {q m : ℕ} (hmq : m ≤ q)
    (T : (Fin q → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (hbot : ∀ p ∈ perpSub (LinearMap.range T), p = 0) :
    LinearMap.range T = ⊤ ∧ Module.finrank (ZMod 2) (LinearMap.ker T) = q - m := by
  have hperp : perpSub (LinearMap.range T) = ⊥ := by
    ext p; simp only [Submodule.mem_bot]; exact ⟨hbot p, fun h => h ▸ (perpSub _).zero_mem⟩
  have hfrp := finrank_perpSub (LinearMap.range T)
  rw [hperp, finrank_bot] at hfrp
  have hle : Module.finrank (ZMod 2) (LinearMap.range T) ≤ m := by
    have := Submodule.finrank_le (LinearMap.range T)
    rwa [Module.finrank_fin_fun] at this
  have hfrr : Module.finrank (ZMod 2) (LinearMap.range T) = m := by omega
  have htop : LinearMap.range T = ⊤ :=
    Submodule.eq_of_le_of_finrank_eq le_top (by rw [hfrr, finrank_top, Module.finrank_fin_fun])
  have hrn := LinearMap.finrank_range_add_finrank_ker T
  rw [hfrr, Module.finrank_fin_fun] at hrn
  exact ⟨htop, by omega⟩

lemma range_eq_ker_dot_of_perp_unique {q m : ℕ} (hmpos : 0 < m) (hmq : m ≤ q)
    (T : (Fin q → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (p0 : Fin m → ZMod 2) (hp0ne : p0 ≠ 0) (hp0mem : p0 ∈ perpSub (LinearMap.range T))
    (huniq : ∀ p ∈ perpSub (LinearMap.range T), p = 0 ∨ p = p0) :
    LinearMap.range T = LinearMap.ker (dotLin p0) ∧
    Module.finrank (ZMod 2) (LinearMap.ker T) = q - m + 1 := by
  have hcard_perp : Nat.card (perpSub (LinearMap.range T)) = 2 := by
    let e : perpSub (LinearMap.range T) ≃ Bool :=
      { toFun := fun p => decide (p.1 ≠ 0)
        invFun := fun b => if b then ⟨p0, hp0mem⟩ else ⟨0, (perpSub _).zero_mem⟩
        left_inv := fun p => by
          rcases huniq p.1 p.2 with h0 | h1
          · apply Subtype.ext; simp [h0]
          · apply Subtype.ext; simp [h1, hp0ne]
        right_inv := fun b => by
          cases b <;> simp [hp0ne] }
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_bool]
  have hfr_perp : Module.finrank (ZMod 2) (perpSub (LinearMap.range T)) = 1 := by
    have hpow := card_submodule_eq_two_pow (perpSub (LinearMap.range T))
    rw [hcard_perp] at hpow
    have h1 : 2 ^ 1 = 2 ^ Module.finrank (ZMod 2) (perpSub (LinearMap.range T)) := hpow
    exact (Nat.pow_right_injective (by omega : 1 < 2) h1).symm
  have hfrp := finrank_perpSub (LinearMap.range T)
  rw [hfr_perp] at hfrp
  have hle_m : Module.finrank (ZMod 2) (LinearMap.range T) ≤ m := by
    have := Submodule.finrank_le (LinearMap.range T)
    rwa [Module.finrank_fin_fun] at this
  have hfrr : Module.finrank (ZMod 2) (LinearMap.range T) = m - 1 := by omega
  have hsurj_dot : Function.Surjective (dotLin p0) := by
    have hex : ∃ j : Fin m, p0 j ≠ 0 := by
      by_contra h
      push Not at h
      exact hp0ne (funext h)
    obtain ⟨j, hj⟩ := hex
    intro z
    refine ⟨z • Pi.single j 1, ?_⟩
    change dot p0 (z • Pi.single j 1) = z
    have h1 := (dotLin p0).map_smul z (Pi.single j 1)
    change dot p0 (z • Pi.single j 1) = z * dot p0 (Pi.single j 1) at h1
    rw [h1, dot_single_right, zmod2_eq_one_of_ne_zero hj, mul_one]
  have hfr_kerdot : Module.finrank (ZMod 2) (LinearMap.ker (dotLin p0)) = m - 1 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (dotLin p0)
    rw [LinearMap.range_eq_top.2 hsurj_dot, finrank_top, Module.finrank_self,
      Module.finrank_fin_fun] at hrn
    omega
  have hsub : LinearMap.range T ≤ LinearMap.ker (dotLin p0) := by
    intro u hu
    rw [LinearMap.mem_ker]
    exact hp0mem u hu
  have heq : LinearMap.range T = LinearMap.ker (dotLin p0) :=
    Submodule.eq_of_le_of_finrank_eq hsub (by rw [hfrr, hfr_kerdot])
  have hrn := LinearMap.finrank_range_add_finrank_ker T
  rw [hfrr, Module.finrank_fin_fun] at hrn
  exact ⟨heq, by omega⟩

def loNat {n : ℕ} (i : Fin n) : ℕ := (1 : ℕ) <<< (2 * i.val + 1)
def hiNat {n : ℕ} (i : Fin n) : ℕ := (1 : ℕ) <<< (2 * i.val + 2)

def colsOf (n : ℕ) (es : List (Fin n × Fin n)) : List ℕ :=
  [1, 1, 1] ++
    (List.finRange n).flatMap (fun i => [loNat i, hiNat i, 1]) ++
    es.flatMap (fun e => [loNat e.1 ^^^ loNat e.2, hiNat e.1 ^^^ hiNat e.2, 1])

lemma list_flatMap_length_const {α β : Type*} (l : List α) (f : α → List β) (k : ℕ)
    (hf : ∀ a, (f a).length = k) : (l.flatMap f).length = l.length * k := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.flatMap_cons, List.length_append, hf a, List.length_cons, ih]
    ring

lemma list_flatMap_getElem_const {α β : Type*} (l : List α) (f : α → List β) (k : ℕ)
    (hf : ∀ a, (f a).length = k) (r : ℕ) (hr : r < l.length) (s : ℕ) (hs : s < k) :
    (l.flatMap f)[r * k + s]'(by
      rw [list_flatMap_length_const l f k hf]
      have : (r + 1) * k ≤ l.length * k := Nat.mul_le_mul_right k hr
      linarith) = (f (l[r]'hr))[s]'(by rw [hf]; exact hs) := by
  induction l generalizing r with
  | nil => simp at hr
  | cons a t ih =>
    cases r with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, List.flatMap_cons, List.getElem_cons_zero]
      rw [List.getElem_append_left (by rw [hf]; exact hs)]
    | succ r =>
      simp only [List.flatMap_cons, List.getElem_cons_succ]
      have hge : (f a).length ≤ (r + 1) * k + s := by rw [hf]; nlinarith
      rw [List.getElem_append_right hge]
      have hidx : (r + 1) * k + s - (f a).length = r * k + s := by rw [hf, Nat.succ_mul]; omega
      simp only [hidx]
      exact ih r (Nat.lt_of_succ_lt_succ hr)

lemma colsOf_length (n : ℕ) (es : List (Fin n × Fin n)) :
    (colsOf n es).length = 3 + 3 * n + 3 * es.length := by
  unfold colsOf
  rw [List.length_append, List.length_append,
    list_flatMap_length_const _ _ 3 (fun _ => rfl),
    list_flatMap_length_const _ _ 3 (fun _ => rfl),
    List.length_finRange]
  simp only [List.length_cons, List.length_nil]
  ring

lemma loNat_lt {n : ℕ} (i : Fin n) : loNat i < 2 ^ (2 * n + 1) := by
  simp only [loNat, Nat.shiftLeft_eq, one_mul]
  exact Nat.pow_lt_pow_right (by omega) (by have := i.isLt; omega)

lemma hiNat_lt {n : ℕ} (i : Fin n) : hiNat i < 2 ^ (2 * n + 1) := by
  simp only [hiNat, Nat.shiftLeft_eq, one_mul]
  exact Nat.pow_lt_pow_right (by omega) (by have := i.isLt; omega)

lemma loNat_testBit {n : ℕ} (i : Fin n) (j : ℕ) :
    (loNat i).testBit j = decide (j = 2 * i.val + 1) := by
  simp only [loNat, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow, eq_comm]

lemma hiNat_testBit {n : ℕ} (i : Fin n) (j : ℕ) :
    (hiNat i).testBit j = decide (j = 2 * i.val + 2) := by
  simp only [hiNat, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow, eq_comm]

lemma one_testBit (j : ℕ) : (1 : ℕ).testBit j = decide (j = 0) := by
  simpa [eq_comm] using Nat.testBit_two_pow (n := 0) (m := j)

lemma colsOf_lt (n : ℕ) (es : List (Fin n × Fin n)) (i : Fin (colsOf n es).length) :
    (colsOf n es).get i < 2 ^ (2 * n + 1) := by
  have hall : ∀ x ∈ colsOf n es, x < 2 ^ (2 * n + 1) := by
    intro x hx
    simp only [colsOf, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_flatMap, List.mem_finRange, true_and] at hx
    rcases hx with ((rfl | rfl | rfl) | ⟨k, rfl | rfl | rfl⟩) | ⟨e, _, rfl | rfl | rfl⟩
    · exact Nat.one_lt_pow (by omega) (by omega)
    · exact Nat.one_lt_pow (by omega) (by omega)
    · exact Nat.one_lt_pow (by omega) (by omega)
    · exact loNat_lt k
    · exact hiNat_lt k
    · exact Nat.one_lt_pow (by omega) (by omega)
    · exact Nat.xor_lt_two_pow (loNat_lt e.1) (loNat_lt e.2)
    · exact Nat.xor_lt_two_pow (hiNat_lt e.1) (hiNat_lt e.2)
    · exact Nat.one_lt_pow (by omega) (by omega)
  exact hall _ (List.get_mem _ _)

lemma colsOf_get_anchor (n : ℕ) (es : List (Fin n × Fin n)) (r : ℕ) (hr : r < 3) :
    (colsOf n es).get ⟨r, by rw [colsOf_length]; omega⟩ = 1 := by
  simp only [List.get_eq_getElem, colsOf]
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega)]
  interval_cases r <;> rfl

lemma colsOf_get_vert (n : ℕ) (es : List (Fin n × Fin n)) (k : Fin n) :
    (colsOf n es).get ⟨3 + 3 * k.val, by rw [colsOf_length]; have := k.isLt; omega⟩ = loNat k ∧
    (colsOf n es).get ⟨3 + 3 * k.val + 1, by rw [colsOf_length]; have := k.isLt; omega⟩ = hiNat k ∧
    (colsOf n es).get ⟨3 + 3 * k.val + 2, by rw [colsOf_length]; have := k.isLt; omega⟩ = 1 := by
  have hlen1 : ([1, 1, 1] : List ℕ).length = 3 := rfl
  have hlen2 : ((List.finRange n).flatMap (fun i => [loNat i, hiNat i, 1])).length = 3 * n := by
    rw [list_flatMap_length_const _ _ 3 (fun _ => rfl), List.length_finRange]; ring
  have hk := k.isLt
  have hstep : ∀ s (hs : s < 3),
      (colsOf n es).get ⟨3 + 3 * k.val + s, by rw [colsOf_length]; omega⟩ =
      ([loNat k, hiNat k, 1] : List ℕ)[s]'(by simp; omega) := by
    intro s hs
    simp only [List.get_eq_getElem, colsOf]
    rw [List.getElem_append_left (by rw [List.length_append, hlen1, hlen2]; omega)]
    rw [List.getElem_append_right (by rw [hlen1]; omega)]
    have hidx : 3 + 3 * k.val + s - ([1, 1, 1] : List ℕ).length = k.val * 3 + s := by rw [hlen1]; omega
    simp only [hidx]
    have h1 := list_flatMap_getElem_const (List.finRange n) (fun i => [loNat i, hiNat i, 1]) 3
      (fun _ => rfl) k.val (by rw [List.length_finRange]; exact hk) s hs
    simpa [List.getElem_finRange] using h1
  exact ⟨hstep 0 (by omega), hstep 1 (by omega), hstep 2 (by omega)⟩

lemma colsOf_get_edge (n : ℕ) (es : List (Fin n × Fin n)) (r : Fin es.length) :
    let e := es.get r
    (colsOf n es).get ⟨3 + 3 * n + 3 * r.val, by rw [colsOf_length]; have := r.isLt; omega⟩ =
      loNat e.1 ^^^ loNat e.2 ∧
    (colsOf n es).get ⟨3 + 3 * n + 3 * r.val + 1, by rw [colsOf_length]; have := r.isLt; omega⟩ =
      hiNat e.1 ^^^ hiNat e.2 ∧
    (colsOf n es).get ⟨3 + 3 * n + 3 * r.val + 2, by rw [colsOf_length]; have := r.isLt; omega⟩ = 1 := by
  intro e
  have hlen1 : ([1, 1, 1] ++ (List.finRange n).flatMap (fun i => [loNat i, hiNat i, 1])).length =
      3 + 3 * n := by
    rw [List.length_append, list_flatMap_length_const _ _ 3 (fun _ => rfl), List.length_finRange]
    simp only [List.length_cons, List.length_nil]; ring
  have hr := r.isLt
  have hstep : ∀ s (hs : s < 3),
      (colsOf n es).get ⟨3 + 3 * n + 3 * r.val + s, by rw [colsOf_length]; omega⟩ =
      ([loNat e.1 ^^^ loNat e.2, hiNat e.1 ^^^ hiNat e.2, 1] : List ℕ)[s]'(by simp; omega) := by
    intro s hs
    simp only [List.get_eq_getElem, colsOf]
    rw [List.getElem_append_right (by rw [hlen1]; omega)]
    have hidx : 3 + 3 * n + 3 * r.val + s -
        ([1, 1, 1] ++ (List.finRange n).flatMap (fun i => [loNat i, hiNat i, 1])).length =
        r.val * 3 + s := by rw [hlen1]; omega
    simp only [hidx]
    exact list_flatMap_getElem_const es
      (fun e' => [loNat e'.1 ^^^ loNat e'.2, hiNat e'.1 ^^^ hiNat e'.2, 1]) 3
      (fun _ => rfl) r.val hr s hs
  exact ⟨hstep 0 (by omega), hstep 1 (by omega), hstep 2 (by omega)⟩

def normalOf {n : ℕ} (c : Fin n → Fin 3) : ℕ :=
  (List.finRange n).foldl (fun p i => p ||| (((c i).val + 1) <<< (2 * i.val + 1))) (1 : ℕ)

lemma foldl_or_testBit {α : Type*} (l : List α) (f : α → ℕ) (init j : ℕ) :
    (l.foldl (fun p a => p ||| f a) init).testBit j =
      (init.testBit j || l.any (fun a => (f a).testBit j)) := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.any_cons, ih, Nat.testBit_or, Bool.or_assoc]

lemma normalOf_testBit {n : ℕ} (c : Fin n → Fin 3) :
    (normalOf c).testBit 0 = true ∧
    (∀ k : Fin n, (normalOf c).testBit (2 * k.val + 1) = ((c k).val + 1).testBit 0) ∧
    (∀ k : Fin n, (normalOf c).testBit (2 * k.val + 2) = ((c k).val + 1).testBit 1) := by
  unfold normalOf
  refine ⟨?_, ?_, ?_⟩
  · rw [foldl_or_testBit]; simp [one_testBit]
  · intro k
    rw [foldl_or_testBit, one_testBit]
    simp only [Nat.succ_ne_zero, decide_false, Bool.false_or]
    have h1 : ∀ i : Fin n, (((c i).val + 1) <<< (2 * i.val + 1)).testBit (2 * k.val + 1) =
        if i = k then ((c k).val + 1).testBit 0 else false := by
      intro i
      rw [Nat.testBit_shiftLeft]
      by_cases hik : i = k
      · subst hik; simp
      · rw [if_neg hik]
        by_cases hle : 2 * i.val + 1 ≤ 2 * k.val + 1
        · have hge2 : 2 ≤ 2 * k.val + 1 - (2 * i.val + 1) := by
            have hne : i.val ≠ k.val := fun h => hik (Fin.ext h)
            omega
          have hlt4 : (c i).val + 1 < 2 ^ (2 * k.val + 1 - (2 * i.val + 1)) := by
            have := (c i).isLt
            calc (c i).val + 1 < 2 ^ 2 := by omega
              _ ≤ 2 ^ (2 * k.val + 1 - (2 * i.val + 1)) := Nat.pow_le_pow_right (by omega) hge2
          rw [Nat.testBit_eq_false_of_lt hlt4, Bool.and_false]
        · simp [hle]
    cases hb : ((c k).val + 1).testBit 0
    · rw [Bool.eq_false_iff]
      intro hany
      rw [List.any_eq_true] at hany
      obtain ⟨i, _, hi⟩ := hany
      rw [h1 i] at hi
      by_cases hik : i = k
      · rw [if_pos hik, hb] at hi; exact Bool.noConfusion hi
      · rw [if_neg hik] at hi; exact Bool.noConfusion hi
    · rw [List.any_eq_true]
      refine ⟨k, List.mem_finRange k, ?_⟩
      rw [h1 k, if_pos rfl, hb]
  · intro k
    rw [foldl_or_testBit, one_testBit]
    simp only [Nat.succ_ne_zero, decide_false, Bool.false_or]
    have h1 : ∀ i : Fin n, (((c i).val + 1) <<< (2 * i.val + 1)).testBit (2 * k.val + 2) =
        if i = k then ((c k).val + 1).testBit 1 else false := by
      intro i
      rw [Nat.testBit_shiftLeft]
      by_cases hik : i = k
      · subst hik
        have hsub : 2 * i.val + 2 - (2 * i.val + 1) = 1 := by omega
        simp [hsub]
      · rw [if_neg hik]
        by_cases hle : 2 * i.val + 1 ≤ 2 * k.val + 2
        · have hge2 : 2 ≤ 2 * k.val + 2 - (2 * i.val + 1) := by
            have hne : i.val ≠ k.val := fun h => hik (Fin.ext h)
            omega
          have hlt4 : (c i).val + 1 < 2 ^ (2 * k.val + 2 - (2 * i.val + 1)) := by
            have := (c i).isLt
            calc (c i).val + 1 < 2 ^ 2 := by omega
              _ ≤ 2 ^ (2 * k.val + 2 - (2 * i.val + 1)) := Nat.pow_le_pow_right (by omega) hge2
          rw [Nat.testBit_eq_false_of_lt hlt4, Bool.and_false]
        · simp [hle]
    cases hb : ((c k).val + 1).testBit 1
    · rw [Bool.eq_false_iff]
      intro hany
      rw [List.any_eq_true] at hany
      obtain ⟨i, _, hi⟩ := hany
      rw [h1 i] at hi
      by_cases hik : i = k
      · rw [if_pos hik, hb] at hi; exact Bool.noConfusion hi
      · rw [if_neg hik] at hi; exact Bool.noConfusion hi
    · rw [List.any_eq_true]
      refine ⟨k, List.mem_finRange k, ?_⟩
      rw [h1 k, if_pos rfl, hb]

def parOf (m : ℕ) (mask : ℕ) (y : Fin (2 ^ m)) : Bool :=
  (List.range m).foldl (fun b j => xor b (mask.testBit j && y.val.testBit j)) false

lemma foldl_xor_toZ2 {α : Type*} (l : List α) (f : α → Bool) (init : Bool) :
    toZ2 (l.foldl (fun b a => xor b (f a)) init) =
      toZ2 init + (l.map (fun a => toZ2 (f a))).sum := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, toZ2_xor, add_assoc]

lemma list_range_map_sum (m : ℕ) (f : ℕ → ZMod 2) :
    ((List.range m).map f).sum = ∑ j : Fin m, f j.val := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton,
      Fin.sum_univ_castSucc, ih]
    rfl

lemma toZ2_parOf (m : ℕ) (mask : ℕ) (y : Fin (2 ^ m)) :
    toZ2 (parOf m mask y) =
      dot (fun j : Fin m => toZ2 (mask.testBit j.val)) (bitsEquiv m y) := by
  unfold parOf
  rw [foldl_xor_toZ2, toZ2_false, zero_add,
    list_range_map_sum m (fun j => toZ2 (mask.testBit j && y.val.testBit j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [toZ2_and]
  rfl

def ringL (q : ℕ) (h : Fin q → Fin 3) : (Fin q → ZMod 2) →ₗ[ZMod 2] (Fin q → ZMod 2) where
  toFun := fun v i =>
    v i + if (h i).val ≠ 0 then v ⟨(i.val + (h i).val) % q, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ else 0
  map_add' := fun v1 v2 => by
    funext i
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' := fun c v => by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

def matM (n : ℕ) (es : List (Fin n × Fin n)) :
    (Fin (colsOf n es).length → ZMod 2) →ₗ[ZMod 2] (Fin (2 * n + 1) → ZMod 2) where
  toFun := fun a j => ∑ i : Fin (colsOf n es).length, a i * toZ2 (((colsOf n es).get i).testBit j.val)
  map_add' := fun a1 a2 => by
    funext j
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' := fun c a => by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, ← Finset.mul_sum]

def matMT (n : ℕ) (es : List (Fin n × Fin n)) :
    (Fin (2 * n + 1) → ZMod 2) →ₗ[ZMod 2] (Fin (colsOf n es).length → ZMod 2) where
  toFun := fun p i => ∑ j : Fin (2 * n + 1), p j * toZ2 (((colsOf n es).get i).testBit j.val)
  map_add' := fun p1 p2 => by
    funext i
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' := fun c p => by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, ← Finset.mul_sum]

lemma dot_matM (n : ℕ) (es : List (Fin n × Fin n))
    (p : Fin (2 * n + 1) → ZMod 2) (a : Fin (colsOf n es).length → ZMod 2) :
    dot p (matM n es a) = dot (matMT n es p) a := by
  simp only [dot, matM, matMT, LinearMap.coe_mk, AddHom.coe_mk, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

def outputOf (n : ℕ) (es : List (Fin n × Fin n))
    (h : Fin (colsOf n es).length → Fin 3)
    (c : Fin (colsOf n es).length → Bool)
    (x : Fin (2 ^ (colsOf n es).length)) : ℕ :=
  (List.finRange (colsOf n es).length).foldl (fun y i =>
    let a := xor (c i) (xor (x.val.testBit i.val)
      (decide ((h i).val ≠ 0) && x.val.testBit ((i.val + (h i).val) % (colsOf n es).length)))
    if a then y ^^^ ((colsOf n es).get i) else y) (0 : ℕ)

lemma foldl_xor_nat_lt {α : Type*} (l : List α) (a : α → Bool) (f : α → ℕ) (k init : ℕ)
    (hinit : init < 2 ^ k) (hf : ∀ x ∈ l, f x < 2 ^ k) :
    l.foldl (fun y x => if a x then y ^^^ f x else y) init < 2 ^ k := by
  induction l generalizing init with
  | nil => exact hinit
  | cons x t ih =>
    simp only [List.foldl_cons]
    apply ih
    · split_ifs
      · exact Nat.xor_lt_two_pow hinit (hf x (List.mem_cons_self ..))
      · exact hinit
    · intro z hz; exact hf z (List.mem_cons_of_mem x hz)

lemma foldl_xor_nat_testBit {α : Type*} (l : List α) (a : α → Bool) (f : α → ℕ) (init j : ℕ) :
    (l.foldl (fun y x => if a x then y ^^^ f x else y) init).testBit j =
      l.foldl (fun b x => xor b (a x && (f x).testBit j)) (init.testBit j) := by
  induction l generalizing init with
  | nil => rfl
  | cons x t ih =>
    simp only [List.foldl_cons]
    cases ha : a x
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_and, Bool.xor_false]
      exact ih init
    · simp only [↓reduceIte, Bool.true_and]
      rw [ih (init ^^^ f x), Nat.testBit_xor]

lemma outputOf_lt (n : ℕ) (es : List (Fin n × Fin n))
    (h : Fin (colsOf n es).length → Fin 3)
    (c : Fin (colsOf n es).length → Bool)
    (x : Fin (2 ^ (colsOf n es).length)) :
    outputOf n es h c x < 2 ^ (2 * n + 1) :=
  foldl_xor_nat_lt _ _ _ (2 * n + 1) 0 (Nat.two_pow_pos _) (fun i _ => colsOf_lt n es i)

lemma list_finRange_map_sum {q : ℕ} (f : Fin q → ZMod 2) :
    ((List.finRange q).map f).sum = ∑ i : Fin q, f i := by
  have h1 : (List.finRange q).toFinset = Finset.univ := by
    ext i; simp
  rw [← h1, List.sum_toFinset _ (List.nodup_finRange q)]

lemma bits_outputOf (n : ℕ) (es : List (Fin n × Fin n))
    (h : Fin (colsOf n es).length → Fin 3)
    (c : Fin (colsOf n es).length → Bool)
    (x : Fin (2 ^ (colsOf n es).length)) :
    bitsEquiv (2 * n + 1) ⟨outputOf n es h c x, outputOf_lt n es h c x⟩ =
      matM n es (ringL (colsOf n es).length h (bitsEquiv (colsOf n es).length x)) +
        matM n es (fun i => toZ2 (c i)) := by
  rw [← map_add]
  funext j
  change toZ2 ((outputOf n es h c x).testBit j.val) = _
  unfold outputOf
  rw [foldl_xor_nat_testBit, foldl_xor_toZ2, Nat.zero_testBit, toZ2_false, zero_add,
    list_finRange_map_sum]
  simp only [matM, ringL, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, bitsEquiv,
    Equiv.coe_fn_mk]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [toZ2_and, toZ2_xor, toZ2_xor, toZ2_and]
  congr 1
  by_cases hnz : (h i).val ≠ 0
  · simp [hnz, toZ2]
    ring
  · simp [hnz, toZ2]
    ring

lemma matMT_eval_anchor (n : ℕ) (es : List (Fin n × Fin n))
    (p : Fin (2 * n + 1) → ZMod 2) (r : ℕ) (hr : r < 3) :
    matMT n es p ⟨r, by rw [colsOf_length]; omega⟩ = p ⟨0, by omega⟩ := by
  simp only [matMT, LinearMap.coe_mk, AddHom.coe_mk, colsOf_get_anchor n es r hr, one_testBit]
  rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin (2 * n + 1))]
  · simp [toZ2]
  · intro j _ hj
    have hne : j.val ≠ 0 := fun h => hj (Fin.ext h)
    simp [hne, toZ2]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma matMT_eval_vert (n : ℕ) (es : List (Fin n × Fin n))
    (p : Fin (2 * n + 1) → ZMod 2) (k : Fin n) :
    matMT n es p ⟨3 + 3 * k.val, by rw [colsOf_length]; have := k.isLt; omega⟩ =
      p ⟨2 * k.val + 1, by have := k.isLt; omega⟩ ∧
    matMT n es p ⟨3 + 3 * k.val + 1, by rw [colsOf_length]; have := k.isLt; omega⟩ =
      p ⟨2 * k.val + 2, by have := k.isLt; omega⟩ ∧
    matMT n es p ⟨3 + 3 * k.val + 2, by rw [colsOf_length]; have := k.isLt; omega⟩ =
      p ⟨0, by omega⟩ := by
  obtain ⟨h0, h1, h2⟩ := colsOf_get_vert n es k
  refine ⟨?_, ?_, ?_⟩
  · simp only [matMT, LinearMap.coe_mk, AddHom.coe_mk, h0, loNat_testBit]
    rw [Finset.sum_eq_single (⟨2 * k.val + 1, by have := k.isLt; omega⟩ : Fin (2 * n + 1))]
    · simp [toZ2]
    · intro j _ hj
      have hne : j.val ≠ 2 * k.val + 1 := fun h => hj (Fin.ext h)
      simp [hne, toZ2]
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp only [matMT, LinearMap.coe_mk, AddHom.coe_mk, h1, hiNat_testBit]
    rw [Finset.sum_eq_single (⟨2 * k.val + 2, by have := k.isLt; omega⟩ : Fin (2 * n + 1))]
    · simp [toZ2]
    · intro j _ hj
      have hne : j.val ≠ 2 * k.val + 2 := fun h => hj (Fin.ext h)
      simp [hne, toZ2]
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp only [matMT, LinearMap.coe_mk, AddHom.coe_mk, h2, one_testBit]
    rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin (2 * n + 1))]
    · simp [toZ2]
    · intro j _ hj
      have hne : j.val ≠ 0 := fun h => hj (Fin.ext h)
      simp [hne, toZ2]
    · intro h; exact absurd (Finset.mem_univ _) h

lemma matMT_eval_edge (n : ℕ) (es : List (Fin n × Fin n))
    (p : Fin (2 * n + 1) → ZMod 2) (r : Fin es.length) :
    let e := es.get r
    matMT n es p ⟨3 + 3 * n + 3 * r.val, by rw [colsOf_length]; have := r.isLt; omega⟩ =
      p ⟨2 * e.1.val + 1, by have := e.1.isLt; omega⟩ + p ⟨2 * e.2.val + 1, by have := e.2.isLt; omega⟩ ∧
    matMT n es p ⟨3 + 3 * n + 3 * r.val + 1, by rw [colsOf_length]; have := r.isLt; omega⟩ =
      p ⟨2 * e.1.val + 2, by have := e.1.isLt; omega⟩ + p ⟨2 * e.2.val + 2, by have := e.2.isLt; omega⟩ ∧
    matMT n es p ⟨3 + 3 * n + 3 * r.val + 2, by rw [colsOf_length]; have := r.isLt; omega⟩ =
      p ⟨0, by omega⟩ := by
  intro e
  obtain ⟨h0, h1, h2⟩ := colsOf_get_edge n es r
  dsimp only [e] at h0 h1 h2 ⊢
  refine ⟨?_, ?_, ?_⟩
  · simp only [matMT, LinearMap.coe_mk, AddHom.coe_mk, h0, Nat.testBit_xor, loNat_testBit,
      toZ2_bne, mul_add, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_eq_single (⟨2 * (es.get r).1.val + 1, by have := (es.get r).1.isLt; omega⟩ : Fin (2 * n + 1))]
      · simp [toZ2]
      · intro j _ hj; have hne : j.val ≠ 2 * (es.get r).1.val + 1 := fun h => hj (Fin.ext h); simp [List.get_eq_getElem] at hne; simp [hne, toZ2]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [Finset.sum_eq_single (⟨2 * (es.get r).2.val + 1, by have := (es.get r).2.isLt; omega⟩ : Fin (2 * n + 1))]
      · simp [toZ2]
      · intro j _ hj; have hne : j.val ≠ 2 * (es.get r).2.val + 1 := fun h => hj (Fin.ext h); simp [List.get_eq_getElem] at hne; simp [hne, toZ2]
      · intro h; exact absurd (Finset.mem_univ _) h
  · simp only [matMT, LinearMap.coe_mk, AddHom.coe_mk, h1, Nat.testBit_xor, hiNat_testBit,
      toZ2_bne, mul_add, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_eq_single (⟨2 * (es.get r).1.val + 2, by have := (es.get r).1.isLt; omega⟩ : Fin (2 * n + 1))]
      · simp [toZ2]
      · intro j _ hj; have hne : j.val ≠ 2 * (es.get r).1.val + 2 := fun h => hj (Fin.ext h); simp [List.get_eq_getElem] at hne; simp [hne, toZ2]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [Finset.sum_eq_single (⟨2 * (es.get r).2.val + 2, by have := (es.get r).2.isLt; omega⟩ : Fin (2 * n + 1))]
      · simp [toZ2]
      · intro j _ hj; have hne : j.val ≠ 2 * (es.get r).2.val + 2 := fun h => hj (Fin.ext h); simp [List.get_eq_getElem] at hne; simp [hne, toZ2]
      · intro h; exact absurd (Finset.mem_univ _) h
  · simp only [matMT, LinearMap.coe_mk, AddHom.coe_mk, h2, one_testBit]
    rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin (2 * n + 1))]
    · simp [toZ2]
    · intro j _ hj; have hne : j.val ≠ 0 := fun h => hj (Fin.ext h); simp [hne, toZ2]
    · intro h; exact absurd (Finset.mem_univ _) h

lemma matMT_injective (n : ℕ) (es : List (Fin n × Fin n)) : Function.Injective (matMT n es) := by
  intro p1 p2 heq
  funext j
  by_cases hj0 : j.val = 0
  · have hjeq : j = ⟨0, by omega⟩ := Fin.ext hj0
    rw [hjeq]
    have h := congrFun heq ⟨0, by rw [colsOf_length]; omega⟩
    rw [matMT_eval_anchor n es p1 0 (by omega), matMT_eval_anchor n es p2 0 (by omega)] at h
    exact h
  · by_cases hodd : j.val % 2 = 1
    · let k : Fin n := ⟨(j.val - 1) / 2, by have := j.isLt; omega⟩
      have hjeq : j = ⟨2 * k.val + 1, by have := k.isLt; omega⟩ := Fin.ext (by dsimp [k]; omega)
      rw [hjeq]
      have h := congrFun heq ⟨3 + 3 * k.val, by rw [colsOf_length]; have := k.isLt; omega⟩
      rw [(matMT_eval_vert n es p1 k).1, (matMT_eval_vert n es p2 k).1] at h
      exact h
    · let k : Fin n := ⟨(j.val - 2) / 2, by have := j.isLt; omega⟩
      have hjeq : j = ⟨2 * k.val + 2, by have := k.isLt; omega⟩ := Fin.ext (by dsimp [k]; omega)
      rw [hjeq]
      have h := congrFun heq ⟨3 + 3 * k.val + 1, by rw [colsOf_length]; have := k.isLt; omega⟩
      rw [(matMT_eval_vert n es p1 k).2.1, (matMT_eval_vert n es p2 k).2.1] at h
      exact h

def next1 {q : ℕ} (i : Fin q) : Fin q :=
  ⟨(i.val + 1) % q, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

def prev1 {q : ℕ} (i : Fin q) : Fin q :=
  ⟨(i.val + q - 1) % q, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

def prev2 {q : ℕ} (i : Fin q) : Fin q :=
  ⟨(i.val + q - 2) % q, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

lemma next1_prev1 {q : ℕ} (hq : 3 ≤ q) (i : Fin q) : next1 (prev1 i) = i := by
  ext
  simp only [next1, prev1]
  have hi := i.isLt
  by_cases h0 : i.val = 0
  · have hp : (i.val + q - 1) % q = q - 1 := by rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    rw [hp, Nat.sub_add_cancel (by omega), Nat.mod_self, h0]
  · have hp : (i.val + q - 1) % q = i.val - 1 := by
      have h1 : i.val + q - 1 = (i.val - 1) + q := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hp, Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt hi]

lemma prev1_next1 {q : ℕ} (hq : 3 ≤ q) (i : Fin q) : prev1 (next1 i) = i := by
  ext
  simp only [next1, prev1]
  have hi := i.isLt
  by_cases hlast : i.val + 1 = q
  · have hn : (i.val + 1) % q = 0 := by rw [hlast, Nat.mod_self]
    rw [hn, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]; omega
  · have hn : (i.val + 1) % q = i.val + 1 := Nat.mod_eq_of_lt (by omega)
    rw [hn]
    have h1 : i.val + 1 + q - 1 = i.val + q := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hi]

lemma prev2_eq_prev1_prev1 {q : ℕ} (hq : 3 ≤ q) (i : Fin q) : prev2 i = prev1 (prev1 i) := by
  ext
  simp only [prev2, prev1]
  have hi := i.isLt
  by_cases h0 : i.val = 0
  · have hp1 : (i.val + q - 1) % q = q - 1 := by rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    have hp2 : (i.val + q - 2) % q = q - 2 := by rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    rw [hp1, hp2]
    have h1 : q - 1 + q - 1 = (q - 2) + q := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · by_cases h1 : i.val = 1
    · have hp1 : (i.val + q - 1) % q = 0 := by
        have hb : i.val + q - 1 = 0 + q := by omega
        rw [hb, Nat.add_mod_right, Nat.zero_mod]
      have hp2 : (i.val + q - 2) % q = q - 1 := by
        have ha : i.val + q - 2 = q - 1 := by omega
        rw [ha, Nat.mod_eq_of_lt (by omega)]
      rw [hp1, hp2, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    · have hp1 : (i.val + q - 1) % q = i.val - 1 := by
        have hb : i.val + q - 1 = (i.val - 1) + q := by omega
        rw [hb, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have hp2 : (i.val + q - 2) % q = i.val - 2 := by
        have ha : i.val + q - 2 = (i.val - 2) + q := by omega
        rw [ha, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hp1, hp2]
      have hc : i.val - 1 + q - 1 = (i.val - 2) + q := by omega
      rw [hc, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

lemma add_mod_eq_iff_prev1 {q : ℕ} (hq : 3 ≤ q) (i j : Fin q) :
    (⟨(i.val + 1) % q, Nat.mod_lt _ (by omega)⟩ : Fin q) = j ↔ i = prev1 j := by
  constructor
  · intro h
    have h' : next1 i = j := h
    rw [← h', prev1_next1 hq]
  · rintro rfl
    exact next1_prev1 hq j

lemma add_mod_eq_iff_prev2 {q : ℕ} (hq : 3 ≤ q) (i j : Fin q) :
    (⟨(i.val + 2) % q, Nat.mod_lt _ (by omega)⟩ : Fin q) = j ↔ i = prev2 j := by
  have hstep : (⟨(i.val + 2) % q, Nat.mod_lt _ (by omega)⟩ : Fin q) = next1 (next1 i) := by
    ext
    simp only [next1]
    rw [Nat.add_mod ((i.val + 1) % q) 1 q, Nat.mod_mod, ← Nat.add_mod, add_assoc]
  rw [hstep, prev2_eq_prev1_prev1 hq]
  constructor
  · intro h
    rw [← prev1_next1 hq i, ← prev1_next1 hq (next1 i), h]
  · rintro rfl
    rw [next1_prev1 hq, next1_prev1 hq]

lemma dot_ringL_single {q : ℕ} (hq : 3 ≤ q) (h : Fin q → Fin 3)
    (w : Fin q → ZMod 2) (j : Fin q) :
    dot w (ringL q h (Pi.single j 1)) =
      w j + (if (h (prev1 j)).val = 1 then w (prev1 j) else 0) +
        (if (h (prev2 j)).val = 2 then w (prev2 j) else 0) := by
  simp only [dot, ringL, LinearMap.coe_mk, AddHom.coe_mk, mul_add, Finset.sum_add_distrib]
  have hterm1 : ∑ i : Fin q, w i * (Pi.single j (1 : ZMod 2) : Fin q → ZMod 2) i = w j := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij; simp [Pi.single_eq_of_ne hij]
    · intro hm; exact absurd (Finset.mem_univ j) hm
  rw [hterm1]
  have hsplit : ∀ i : Fin q,
      w i * (if (h i).val ≠ 0 then
        (Pi.single j (1 : ZMod 2) : Fin q → ZMod 2) ⟨(i.val + (h i).val) % q, Nat.mod_lt _ (by omega)⟩ else 0) =
      (if (h i).val = 1 then
        w i * (Pi.single j (1 : ZMod 2) : Fin q → ZMod 2) ⟨(i.val + 1) % q, Nat.mod_lt _ (by omega)⟩ else 0) +
      (if (h i).val = 2 then
        w i * (Pi.single j (1 : ZMod 2) : Fin q → ZMod 2) ⟨(i.val + 2) % q, Nat.mod_lt _ (by omega)⟩ else 0) := by
    intro i
    have hi := (h i).isLt
    interval_cases hv : (h i).val <;> simp [hv]
  simp_rw [hsplit, Finset.sum_add_distrib]
  rw [add_assoc]
  congr 1
  congr 1
  · rw [Finset.sum_eq_single (prev1 j)]
    · have h1 : (⟨((prev1 j).val + 1) % q, Nat.mod_lt _ (by omega)⟩ : Fin q) = j :=
        (add_mod_eq_iff_prev1 hq (prev1 j) j).2 rfl
      rw [h1, Pi.single_eq_same, mul_one]
    · intro i _ hij
      have hne : (⟨(i.val + 1) % q, Nat.mod_lt _ (by omega)⟩ : Fin q) ≠ j :=
        fun he => hij ((add_mod_eq_iff_prev1 hq i j).1 he)
      simp [Pi.single_eq_of_ne hne]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  · rw [Finset.sum_eq_single (prev2 j)]
    · have h2 : (⟨((prev2 j).val + 2) % q, Nat.mod_lt _ (by omega)⟩ : Fin q) = j :=
        (add_mod_eq_iff_prev2 hq (prev2 j) j).2 rfl
      rw [h2, Pi.single_eq_same, mul_one]
    · intro i _ hij
      have hne : (⟨(i.val + 2) % q, Nat.mod_lt _ (by omega)⟩ : Fin q) ≠ j :=
        fun he => hij ((add_mod_eq_iff_prev2 hq i j).1 he)
      simp [Pi.single_eq_of_ne hne]
    · intro hm; exact absurd (Finset.mem_univ _) hm

lemma mem_perp_comp_iff (n : ℕ) (es : List (Fin n × Fin n))
    (h : Fin (colsOf n es).length → Fin 3) (p : Fin (2 * n + 1) → ZMod 2) :
    p ∈ perpSub (LinearMap.range ((matM n es).comp (ringL (colsOf n es).length h))) ↔
      ∀ j : Fin (colsOf n es).length,
        let w := matMT n es p
        w j + (if (h (prev1 j)).val = 1 then w (prev1 j) else 0) +
          (if (h (prev2 j)).val = 2 then w (prev2 j) else 0) = 0 := by
  have hq : 3 ≤ (colsOf n es).length := by rw [colsOf_length]; omega
  constructor
  · intro hp j
    have hmem : ((matM n es).comp (ringL (colsOf n es).length h)) (Pi.single j 1) ∈
        LinearMap.range ((matM n es).comp (ringL (colsOf n es).length h)) := ⟨Pi.single j 1, rfl⟩
    have h0 := hp _ hmem
    simp only [LinearMap.comp_apply] at h0
    rw [dot_matM, dot_ringL_single hq] at h0
    exact h0
  · intro hw u hu
    obtain ⟨v, rfl⟩ := hu
    simp only [LinearMap.comp_apply]
    rw [dot_matM]
    conv_lhs => rw [← Finset.univ_sum_single v]
    rw [map_sum]
    have hsum : dot (matMT n es p) (∑ j : Fin (colsOf n es).length, ringL _ h (Pi.single j (v j))) =
        ∑ j : Fin (colsOf n es).length, dot (matMT n es p) (ringL _ h (Pi.single j (v j))) :=
      map_sum (dotLin (matMT n es p)) (fun j => ringL _ h (Pi.single j (v j))) Finset.univ
    rw [hsum]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hsm : Pi.single j (v j) = v j • Pi.single j (1 : ZMod 2) := by
      ext i
      by_cases hij : i = j
      · subst hij; simp
      · simp [Pi.single_eq_of_ne hij]
    rw [hsm, map_smul]
    have hsc := (dotLin (matMT n es p)).map_smul (v j) (ringL _ h (Pi.single j 1))
    change dot (matMT n es p) (v j • ringL _ h (Pi.single j 1)) =
      v j * dot (matMT n es p) (ringL _ h (Pi.single j 1)) at hsc
    rw [hsc, dot_ringL_single hq, hw j, mul_zero]

lemma ring_law_zero_of_consec {q : ℕ} (hq : 3 ≤ q) (h : Fin q → Fin 3)
    (w : Fin q → ZMod 2)
    (hlaw : ∀ j : Fin q,
      w j + (if (h (prev1 j)).val = 1 then w (prev1 j) else 0) +
        (if (h (prev2 j)).val = 2 then w (prev2 j) else 0) = 0)
    (i0 : Fin q) (h0 : w i0 = 0) (h1 : w (next1 i0) = 0) : w = 0 := by
  have hstep : ∀ i : Fin q, w i = 0 → w (next1 i) = 0 → w (next1 (next1 i)) = 0 := by
    intro i hi0 hi1
    have hlj := hlaw (next1 (next1 i))
    rw [prev2_eq_prev1_prev1 hq, prev1_next1 hq, prev1_next1 hq, hi0, hi1] at hlj
    simp only [ite_self, add_zero] at hlj
    exact hlj
  have hall : ∀ k : ℕ, w (next1^[k] i0) = 0 ∧ w (next1^[k + 1] i0) = 0 := by
    intro k
    induction k with
    | zero => exact ⟨h0, h1⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have heq : next1^[k + 2] i0 = next1 (next1 (next1^[k] i0)) := by
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have heq1 : next1^[k + 1] i0 = next1 (next1^[k] i0) := Function.iterate_succ_apply' _ _ _
      rw [heq]
      exact hstep _ ih.1 (heq1 ▸ ih.2)
  have hiter_val : ∀ k : ℕ, (next1^[k] i0).val = (i0.val + k) % q := by
    intro k
    induction k with
    | zero => simp [Nat.mod_eq_of_lt i0.isLt]
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      simp only [next1, ih]
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, add_assoc]
  funext j
  let k := (j.val + q - i0.val) % q
  have hjk : next1^[k] i0 = j := by
    ext
    rw [hiter_val k]
    have hi0 := i0.isLt
    have hj := j.isLt
    dsimp only [k]
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have he : i0.val + (j.val + q - i0.val) = j.val + q := by omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
  rw [← hjk]
  exact (hall k).1

lemma perp_anchor_one (n : ℕ) (es : List (Fin n × Fin n))
    (h : Fin (colsOf n es).length → Fin 3) (p : Fin (2 * n + 1) → ZMod 2)
    (hp : p ∈ perpSub (LinearMap.range ((matM n es).comp (ringL (colsOf n es).length h))))
    (hpne : p ≠ 0) : p ⟨0, by omega⟩ = 1 := by
  have hq : 3 ≤ (colsOf n es).length := by rw [colsOf_length]; omega
  have hlaw := (mem_perp_comp_iff n es h p).1 hp
  by_contra hne1
  have h0 : p ⟨0, by omega⟩ = 0 := by
    by_contra hne0
    exact hne1 (zmod2_eq_one_of_ne_zero hne0)
  have hw0 : matMT n es p ⟨0, by omega⟩ = 0 := by
    rw [matMT_eval_anchor n es p 0 (by omega), h0]
  have hw1 : matMT n es p (next1 ⟨0, by omega⟩) = 0 := by
    have hn1 : next1 (⟨0, by omega⟩ : Fin (colsOf n es).length) = ⟨1, by omega⟩ := by
      ext; simp only [next1, Nat.zero_add, Nat.mod_eq_of_lt (by omega : 1 < (colsOf n es).length)]
    rw [hn1, matMT_eval_anchor n es p 1 (by omega), h0]
  have hwz := ring_law_zero_of_consec hq h (matMT n es p) hlaw ⟨0, by omega⟩ hw0 hw1
  have hpz : p = 0 := matMT_injective n es (by rw [hwz, map_zero])
  exact hpne hpz

lemma perp_at_most_one_nonzero (n : ℕ) (es : List (Fin n × Fin n))
    (h : Fin (colsOf n es).length → Fin 3) (p1 p2 : Fin (2 * n + 1) → ZMod 2)
    (hp1 : p1 ∈ perpSub (LinearMap.range ((matM n es).comp (ringL (colsOf n es).length h))))
    (hp2 : p2 ∈ perpSub (LinearMap.range ((matM n es).comp (ringL (colsOf n es).length h))))
    (h1ne : p1 ≠ 0) (h2ne : p2 ≠ 0) : p1 = p2 := by
  have ha1 := perp_anchor_one n es h p1 hp1 h1ne
  have ha2 := perp_anchor_one n es h p2 hp2 h2ne
  have hp12 : p1 + p2 ∈ perpSub (LinearMap.range ((matM n es).comp (ringL (colsOf n es).length h))) :=
    (perpSub _).add_mem hp1 hp2
  have ha12 : (p1 + p2) ⟨0, by omega⟩ = 0 := by
    simp only [Pi.add_apply, ha1, ha2]; decide
  have hsum0 : p1 + p2 = 0 := by
    by_contra hne
    have := perp_anchor_one n es h (p1 + p2) hp12 hne
    rw [ha12] at this
    exact absurd this (by decide)
  funext j
  have hj := congrFun hsum0 j
  simp only [Pi.add_apply, Pi.zero_apply] at hj
  have hself := zmod2_add_self (p2 j)
  calc p1 j = p1 j + (p2 j + p2 j) := by rw [hself, add_zero]
    _ = (p1 j + p2 j) + p2 j := by ring
    _ = p2 j := by rw [hj, zero_add]

lemma perp_nonzero_gives_proper (n : ℕ) (es : List (Fin n × Fin n))
    (h : Fin (colsOf n es).length → Fin 3) (p : Fin (2 * n + 1) → ZMod 2)
    (hp : p ∈ perpSub (LinearMap.range ((matM n es).comp (ringL (colsOf n es).length h))))
    (hpne : p ≠ 0) :
    ∃ c : Fin n → Fin 3, (∀ e ∈ es, c e.1 ≠ c e.2) ∧
      p = fun j : Fin (2 * n + 1) => toZ2 ((normalOf c).testBit j.val) := by
  have hq : 3 ≤ (colsOf n es).length := by rw [colsOf_length]; omega
  have hlaw := (mem_perp_comp_iff n es h p).1 hp
  have hno2 : ∀ i : Fin (colsOf n es).length,
      matMT n es p i ≠ 0 ∨ matMT n es p (next1 i) ≠ 0 := by
    intro i
    by_contra hboth
    push Not at hboth
    have hwz := ring_law_zero_of_consec hq h (matMT n es p) hlaw i hboth.1 hboth.2
    exact hpne (matMT_injective n es (by rw [hwz, map_zero]))
  have hanc := perp_anchor_one n es h p hp hpne
  have hv_nz : ∀ k : Fin n,
      p ⟨2 * k.val + 1, by have := k.isLt; omega⟩ ≠ 0 ∨
      p ⟨2 * k.val + 2, by have := k.isLt; omega⟩ ≠ 0 := by
    intro k
    have hk := k.isLt
    let i : Fin (colsOf n es).length := ⟨3 + 3 * k.val, by rw [colsOf_length]; omega⟩
    have hni : next1 i = ⟨3 + 3 * k.val + 1, by rw [colsOf_length]; omega⟩ := by
      ext; simp only [next1, i]; rw [Nat.mod_eq_of_lt (by rw [colsOf_length]; omega)]
    have hpair := hno2 i
    rw [hni, (matMT_eval_vert n es p k).1, (matMT_eval_vert n es p k).2.1] at hpair
    exact hpair
  let c : Fin n → Fin 3 := fun k =>
    let u := if p ⟨2 * k.val + 1, by have := k.isLt; omega⟩ = 0 then 0 else 1
    let v := if p ⟨2 * k.val + 2, by have := k.isLt; omega⟩ = 0 then 0 else 1
    ⟨u + 2 * v - 1, by
      rcases hv_nz k with hu | hv <;> simp only [u, v] <;> split_ifs <;> omega⟩
  have hc_bits : ∀ k : Fin n,
      toZ2 (((c k).val + 1).testBit 0) = p ⟨2 * k.val + 1, by have := k.isLt; omega⟩ ∧
      toZ2 (((c k).val + 1).testBit 1) = p ⟨2 * k.val + 2, by have := k.isLt; omega⟩ := by
    intro k
    have hnz := hv_nz k
    generalize hu : p ⟨2 * k.val + 1, by have := k.isLt; omega⟩ = u at hnz ⊢
    generalize hv : p ⟨2 * k.val + 2, by have := k.isLt; omega⟩ = v at hnz ⊢
    rcases zmod2_cases u with rfl | rfl <;> rcases zmod2_cases v with rfl | rfl
    · exfalso; rcases hnz with h1 | h1 <;> exact h1 rfl
    · have hcval : (c k).val + 1 = 2 := by dsimp only [c]; rw [hu, hv]; decide
      rw [hcval]; decide
    · have hcval : (c k).val + 1 = 1 := by dsimp only [c]; rw [hu, hv]; decide
      rw [hcval]; decide
    · have hcval : (c k).val + 1 = 3 := by dsimp only [c]; rw [hu, hv]; decide
      rw [hcval]; decide
  refine ⟨c, ?_, ?_⟩
  · intro e he
    obtain ⟨r, rfl⟩ := List.mem_iff_get.1 he
    let i : Fin (colsOf n es).length := ⟨3 + 3 * n + 3 * r.val, by rw [colsOf_length]; have := r.isLt; omega⟩
    have hni : next1 i = ⟨3 + 3 * n + 3 * r.val + 1, by rw [colsOf_length]; have := r.isLt; omega⟩ := by
      ext; simp only [next1, i]; rw [Nat.mod_eq_of_lt (by rw [colsOf_length]; have := r.isLt; omega)]
    have hpair := hno2 i
    rw [hni, (matMT_eval_edge n es p r).1, (matMT_eval_edge n es p r).2.1] at hpair
    intro hceq
    have h1 := (hc_bits (es.get r).1).1
    have h2 := (hc_bits (es.get r).2).1
    have h3 := (hc_bits (es.get r).1).2
    have h4 := (hc_bits (es.get r).2).2
    rw [hceq] at h1 h3
    have he1 : p ⟨2 * (es.get r).1.val + 1, by have := (es.get r).1.isLt; omega⟩ =
        p ⟨2 * (es.get r).2.val + 1, by have := (es.get r).2.isLt; omega⟩ := h1.symm.trans h2
    have he2 : p ⟨2 * (es.get r).1.val + 2, by have := (es.get r).1.isLt; omega⟩ =
        p ⟨2 * (es.get r).2.val + 2, by have := (es.get r).2.isLt; omega⟩ := h3.symm.trans h4
    rcases hpair with hne | hne
    · rw [he1, zmod2_add_self] at hne; exact hne rfl
    · rw [he2, zmod2_add_self] at hne; exact hne rfl
  · funext j
    obtain ⟨hn0, hn1, hn2⟩ := normalOf_testBit c
    by_cases hj0 : j.val = 0
    · have hjeq : j = ⟨0, by omega⟩ := Fin.ext hj0
      rw [hjeq, hanc, hn0]; rfl
    · by_cases hodd : j.val % 2 = 1
      · let k : Fin n := ⟨(j.val - 1) / 2, by have := j.isLt; omega⟩
        have hjeq : j = ⟨2 * k.val + 1, by have := k.isLt; omega⟩ := Fin.ext (by dsimp [k]; omega)
        rw [hjeq, hn1 k, (hc_bits k).1]
      · let k : Fin n := ⟨(j.val - 2) / 2, by have := j.isLt; omega⟩
        have hjeq : j = ⟨2 * k.val + 2, by have := k.isLt; omega⟩ := Fin.ext (by dsimp [k]; omega)
        rw [hjeq, hn2 k, (hc_bits k).2]

lemma exists_h_for_word {q : ℕ} (hq : 3 ≤ q) (w : Fin q → ZMod 2)
    (hno2 : ∀ i : Fin q, w i ≠ 0 ∨ w (next1 i) ≠ 0) :
    ∃ h : Fin q → Fin 3, ∀ j : Fin q,
      w j + (if (h (prev1 j)).val = 1 then w (prev1 j) else 0) +
        (if (h (prev2 j)).val = 2 then w (prev2 j) else 0) = 0 := by
  let h : Fin q → Fin 3 := fun i =>
    if w i = 0 then ⟨0, by omega⟩
    else if w (next1 i) = 0 then ⟨2, by omega⟩
    else ⟨1, by omega⟩
  refine ⟨h, fun j => ?_⟩
  have h1 : (h (prev1 j)).val = 1 ↔ w (prev1 j) ≠ 0 ∧ w j ≠ 0 := by
    dsimp only [h]
    rw [next1_prev1 hq j]
    by_cases hp1 : w (prev1 j) = 0 <;> by_cases hj : w j = 0 <;> simp [hp1, hj]
  have h2 : (h (prev2 j)).val = 2 ↔ w (prev2 j) ≠ 0 ∧ w (prev1 j) = 0 := by
    dsimp only [h]
    have hnp : next1 (prev2 j) = prev1 j := by
      rw [prev2_eq_prev1_prev1 hq, next1_prev1 hq]
    rw [hnp]
    by_cases hp2 : w (prev2 j) = 0 <;> by_cases hp1 : w (prev1 j) = 0 <;> simp [hp2, hp1]
  by_cases hj : w j = 0
  · have hn1 : ¬ ((h (prev1 j)).val = 1) := fun ht => (h1.1 ht).2 hj
    have hp1 : w (prev1 j) ≠ 0 := by
      rcases hno2 (prev1 j) with ha | hb
      · exact ha
      · rw [next1_prev1 hq] at hb; exact absurd hj hb
    have hn2 : ¬ ((h (prev2 j)).val = 2) := fun ht => hp1 (h2.1 ht).2
    rw [hj, if_neg hn1, if_neg hn2]; simp
  · have hj1 : w j = 1 := zmod2_eq_one_of_ne_zero hj
    by_cases hp1 : w (prev1 j) = 0
    · have hn1 : ¬ ((h (prev1 j)).val = 1) := fun ht => (h1.1 ht).1 hp1
      have hp2 : w (prev2 j) ≠ 0 := by
        rcases hno2 (prev2 j) with ha | hb
        · exact ha
        · rw [prev2_eq_prev1_prev1 hq, next1_prev1 hq] at hb; exact absurd hp1 hb
      have hy2 : (h (prev2 j)).val = 2 := h2.2 ⟨hp2, hp1⟩
      rw [if_neg hn1, if_pos hy2, hj1, zmod2_eq_one_of_ne_zero hp2]; decide
    · have hy1 : (h (prev1 j)).val = 1 := h1.2 ⟨hp1, hj⟩
      have hn2 : ¬ ((h (prev2 j)).val = 2) := fun ht => hp1 (h2.1 ht).2
      rw [if_pos hy1, if_neg hn2, hj1, zmod2_eq_one_of_ne_zero hp1]; decide

lemma proper_gives_no_consec_zeros (n : ℕ) (es : List (Fin n × Fin n))
    (c : Fin n → Fin 3) (hprop : ∀ e ∈ es, c e.1 ≠ c e.2) :
    let p : Fin (2 * n + 1) → ZMod 2 := fun j => toZ2 ((normalOf c).testBit j.val)
    ∀ i : Fin (colsOf n es).length,
      matMT n es p i ≠ 0 ∨ matMT n es p (next1 i) ≠ 0 := by
  intro p i
  have hq : (colsOf n es).length = 3 + 3 * n + 3 * es.length := colsOf_length n es
  obtain ⟨hn0, hn1, hn2⟩ := normalOf_testBit c
  have hp0 : p ⟨0, by omega⟩ = 1 := by simp only [p, hn0]; rfl
  have hpk_nz : ∀ k : Fin n,
      p ⟨2 * k.val + 1, by have := k.isLt; omega⟩ ≠ 0 ∨
      p ⟨2 * k.val + 2, by have := k.isLt; omega⟩ ≠ 0 := by
    intro k
    simp only [p, hn1 k, hn2 k]
    have hk := (c k).isLt
    interval_cases hcv : (c k).val <;> decide
  have hpe_nz : ∀ r : Fin es.length,
      let e := es.get r
      p ⟨2 * e.1.val + 1, by have := e.1.isLt; omega⟩ + p ⟨2 * e.2.val + 1, by have := e.2.isLt; omega⟩ ≠ 0 ∨
      p ⟨2 * e.1.val + 2, by have := e.1.isLt; omega⟩ + p ⟨2 * e.2.val + 2, by have := e.2.isLt; omega⟩ ≠ 0 := by
    intro r e
    have hne : c e.1 ≠ c e.2 := hprop e (List.get_mem es r)
    simp only [p, hn1, hn2]
    have h1 := (c e.1).isLt
    have h2 := (c e.2).isLt
    have hvalne : (c e.1).val ≠ (c e.2).val := fun h => hne (Fin.ext h)
    interval_cases ha : (c e.1).val <;> interval_cases hb : (c e.2).val <;>
      first | exact absurd rfl hvalne | decide
  have ha_mod : ∀ idx : Fin (colsOf n es).length, idx.val % 3 = 2 → matMT n es p idx = 1 := by
    intro idx hmod
    by_cases hlt3 : idx.val < 3
    · have h2 : idx = ⟨2, by omega⟩ := Fin.ext (by change idx.val = 2; omega)
      rw [h2, matMT_eval_anchor n es p 2 (by omega), hp0]
    · by_cases hltv : idx.val < 3 + 3 * n
      · let k : Fin n := ⟨(idx.val - 3) / 3, by omega⟩
        have heq : idx = ⟨3 + 3 * k.val + 2, by rw [hq]; have := k.isLt; omega⟩ :=
          Fin.ext (by dsimp [k]; omega)
        rw [heq, (matMT_eval_vert n es p k).2.2, hp0]
      · let r : Fin es.length := ⟨(idx.val - (3 + 3 * n)) / 3, by have := idx.isLt; omega⟩
        have heq : idx = ⟨3 + 3 * n + 3 * r.val + 2, by rw [hq]; have := r.isLt; omega⟩ :=
          Fin.ext (by dsimp [r]; omega)
        rw [heq, (matMT_eval_edge n es p r).2.2, hp0]
  by_cases hm2 : i.val % 3 = 2
  · left; rw [ha_mod i hm2]; decide
  · by_cases hm1 : i.val % 3 = 1
    · right
      have hni_mod : (next1 i).val % 3 = 2 := by
        simp only [next1]
        have hi := i.isLt
        have hlt : i.val + 1 < (colsOf n es).length := by omega
        rw [Nat.mod_eq_of_lt hlt]
        omega
      rw [ha_mod (next1 i) hni_mod]; decide
    · have hm0 : i.val % 3 = 0 := by omega
      have hni_val : (next1 i).val = i.val + 1 := by
        simp only [next1]
        have hi := i.isLt
        rw [Nat.mod_eq_of_lt (by omega)]
      by_cases hlt3 : i.val < 3
      · left
        have heq : i = ⟨0, by omega⟩ := Fin.ext (by change i.val = 0; omega)
        rw [heq, matMT_eval_anchor n es p 0 (by omega), hp0]; decide
      · by_cases hltv : i.val < 3 + 3 * n
        · let k : Fin n := ⟨(i.val - 3) / 3, by omega⟩
          have heq0 : i = ⟨3 + 3 * k.val, by rw [hq]; have := k.isLt; omega⟩ :=
            Fin.ext (by dsimp [k]; omega)
          have heq1 : next1 i = ⟨3 + 3 * k.val + 1, by rw [hq]; have := k.isLt; omega⟩ :=
            Fin.ext (by rw [hni_val]; dsimp [k]; omega)
          have hv0 : matMT n es p i = p ⟨2 * k.val + 1, by have := k.isLt; omega⟩ :=
            (congrArg (matMT n es p) heq0).trans (matMT_eval_vert n es p k).1
          have hv1 : matMT n es p (next1 i) = p ⟨2 * k.val + 2, by have := k.isLt; omega⟩ :=
            (congrArg (matMT n es p) heq1).trans (matMT_eval_vert n es p k).2.1
          rw [hv0, hv1]
          exact hpk_nz k
        · let r : Fin es.length := ⟨(i.val - (3 + 3 * n)) / 3, by have := i.isLt; omega⟩
          have heq0 : i = ⟨3 + 3 * n + 3 * r.val, by rw [hq]; have := r.isLt; omega⟩ :=
            Fin.ext (by dsimp [r]; omega)
          have heq1 : next1 i = ⟨3 + 3 * n + 3 * r.val + 1, by rw [hq]; have := r.isLt; omega⟩ :=
            Fin.ext (by rw [hni_val]; dsimp [r]; omega)
          have hv0 : matMT n es p i =
              p ⟨2 * (es.get r).1.val + 1, by have := (es.get r).1.isLt; omega⟩ +
              p ⟨2 * (es.get r).2.val + 1, by have := (es.get r).2.isLt; omega⟩ :=
            (congrArg (matMT n es p) heq0).trans (matMT_eval_edge n es p r).1
          have hv1 : matMT n es p (next1 i) =
              p ⟨2 * (es.get r).1.val + 2, by have := (es.get r).1.isLt; omega⟩ +
              p ⟨2 * (es.get r).2.val + 2, by have := (es.get r).2.isLt; omega⟩ :=
            (congrArg (matMT n es p) heq1).trans (matMT_eval_edge n es p r).2.1
          rw [hv0, hv1]
          exact hpe_nz r

lemma fiber_card_outputOf (n : ℕ) (es : List (Fin n × Fin n))
    (h : Fin (colsOf n es).length → Fin 3)
    (c : Fin (colsOf n es).length → Bool)
    (y : Fin (2 ^ (2 * n + 1))) :
    Nat.card {x : Fin (2 ^ (colsOf n es).length) // outputOf n es h c x = y.val} =
      Nat.card {v : Fin (colsOf n es).length → ZMod 2 //
        ((matM n es).comp (ringL (colsOf n es).length h)) v +
          matM n es (fun i => toZ2 (c i)) = bitsEquiv (2 * n + 1) y} := by
  let e : {x : Fin (2 ^ (colsOf n es).length) // outputOf n es h c x = y.val} ≃
      {v : Fin (colsOf n es).length → ZMod 2 //
        ((matM n es).comp (ringL (colsOf n es).length h)) v +
          matM n es (fun i => toZ2 (c i)) = bitsEquiv (2 * n + 1) y} :=
    { toFun := fun x => ⟨bitsEquiv _ x.1, by
        have h1 := bits_outputOf n es h c x.1
        have h2 : (⟨outputOf n es h c x.1, outputOf_lt n es h c x.1⟩ : Fin (2 ^ (2 * n + 1))) = y :=
          Fin.ext x.2
        rw [h2] at h1
        exact h1.symm⟩
      invFun := fun v => ⟨(bitsEquiv _).symm v.1, by
        have h1 := bits_outputOf n es h c ((bitsEquiv _).symm v.1)
        rw [Equiv.apply_symm_apply] at h1
        have h2 : bitsEquiv (2 * n + 1)
            ⟨outputOf n es h c ((bitsEquiv _).symm v.1), outputOf_lt n es h c _⟩ =
            bitsEquiv (2 * n + 1) y := h1.trans v.2
        exact congrArg Fin.val ((bitsEquiv (2 * n + 1)).injective h2)⟩
      left_inv := fun x => Subtype.ext ((bitsEquiv _).symm_apply_apply x.1)
      right_inv := fun v => Subtype.ext ((bitsEquiv _).apply_symm_apply v.1) }
  exact Nat.card_congr e

lemma normalOf_inj {n : ℕ} {c1 c2 : Fin n → Fin 3}
    (h : ∀ y : Fin (2 ^ (2 * n + 1)), parOf (2 * n + 1) (normalOf c1) y = parOf (2 * n + 1) (normalOf c2) y) :
    c1 = c2 := by
  have hbit : ∀ j : Fin (2 * n + 1), (normalOf c1).testBit j.val = (normalOf c2).testBit j.val := by
    intro j
    let y : Fin (2 ^ (2 * n + 1)) := ⟨2 ^ j.val, Nat.pow_lt_pow_right (by omega) j.isLt⟩
    have hy := congrArg toZ2 (h y)
    rw [toZ2_parOf, toZ2_parOf] at hy
    have hbits_y : bitsEquiv (2 * n + 1) y = Pi.single j 1 := by
      funext i
      simp only [bitsEquiv, Equiv.coe_fn_mk, y, Nat.testBit_two_pow]
      by_cases hij : i = j
      · subst hij; simp [toZ2]
      · have hne : j.val ≠ i.val := fun he => hij (Fin.ext he.symm)
        simp [hne, toZ2, Pi.single_eq_of_ne hij]
    rw [hbits_y, dot_single_right, dot_single_right] at hy
    exact toZ2_inj hy
  funext k
  obtain ⟨_, ha1, ha2⟩ := normalOf_testBit c1
  obtain ⟨_, hb1, hb2⟩ := normalOf_testBit c2
  have h0 : ((c1 k).val + 1).testBit 0 = ((c2 k).val + 1).testBit 0 := by
    rw [← ha1 k, ← hb1 k]
    exact hbit ⟨2 * k.val + 1, by have := k.isLt; omega⟩
  have h1 : ((c1 k).val + 1).testBit 1 = ((c2 k).val + 1).testBit 1 := by
    rw [← ha2 k, ← hb2 k]
    exact hbit ⟨2 * k.val + 2, by have := k.isLt; omega⟩
  have hk1 := (c1 k).isLt
  have hk2 := (c2 k).isLt
  apply Fin.ext
  interval_cases ha : (c1 k).val <;> interval_cases hb : (c2 k).val <;>
    first | rfl | exact absurd h0 (by decide) | exact absurd h1 (by decide)

lemma parOf_zero (m mask : ℕ) : parOf m mask ⟨0, Nat.two_pow_pos m⟩ = false := by
  apply toZ2_inj
  rw [toZ2_parOf, toZ2_false]
  have h0 : bitsEquiv m ⟨0, Nat.two_pow_pos m⟩ = 0 := by
    funext j; simp [bitsEquiv, toZ2]
  rw [h0, dot_zero_right]

lemma parOf_one {n : ℕ} (c : Fin n → Fin 3) :
    parOf (2 * n + 1) (normalOf c) ⟨1, Nat.one_lt_pow (by omega) (by omega)⟩ = true := by
  apply toZ2_inj
  rw [toZ2_parOf, toZ2_true]
  have h1 : bitsEquiv (2 * n + 1) ⟨1, Nat.one_lt_pow (by omega) (by omega)⟩ =
      Pi.single ⟨0, by omega⟩ 1 := by
    funext j
    simp only [bitsEquiv, Equiv.coe_fn_mk, one_testBit]
    by_cases hj : j = ⟨0, by omega⟩
    · subst hj; simp [toZ2]
    · have hne : j.val ≠ 0 := fun he => hj (Fin.ext he)
      rw [Pi.single_eq_of_ne hj]
      simp [hne, toZ2]
  rw [h1, dot_single_right, (normalOf_testBit c).1]
  rfl

lemma main_result (n : ℕ) (es : List (Fin n × Fin n)) (aff : Bool) :
    let m := 2 * n + 1
    let cols := colsOf n es
    let q := cols.length
    let W := Fin (2 ^ q)
    let Y := Fin (2 ^ m)
    let C := Fin n → Fin 3
    let proper := fun (c : C) => ∀ e ∈ es, c e.1 ≠ c e.2
    let realizes := fun (H : Y → ℕ) =>
      ∃ (h : Fin q → Fin 3) (c : Fin q → Bool), (aff = true ∨ ∀ i, c i = false) ∧
        ∀ y : Y, H y = Nat.card {x : W // outputOf n es h c x = y.val}
    let base := 2 ^ (q - m)
    (∀ H : Y → ℕ, realizes H ↔ (∀ y, H y = base) ∨
      ∃ (c : C) (b : Bool), proper c ∧ (aff = true ∨ b = false) ∧
        ∀ y, H y = if parOf m (normalOf c) y = b then 2 * base else 0) ∧
    Nat.card {H : Y → ℕ // realizes H} =
      1 + (if aff then 2 else 1) * Nat.card {c : C // proper c} := by
  intro m cols q W Y C proper realizes base
  have hq_len : q = 3 + 3 * n + 3 * es.length := colsOf_length n es
  have hq3 : 3 ≤ q := by omega
  have hmq : m ≤ q := by dsimp only [m]; omega
  have hmpos : 0 < m := by dsimp only [m]; omega
  have hbase_pos : 0 < base := Nat.two_pow_pos _
  have hchar : ∀ H : Y → ℕ, realizes H ↔ (∀ y, H y = base) ∨
      ∃ (c : C) (b : Bool), proper c ∧ (aff = true ∨ b = false) ∧
        ∀ y, H y = if parOf m (normalOf c) y = b then 2 * base else 0 := by
    intro H
    constructor
    · rintro ⟨h, cshift, haff, hH⟩
      let T := (matM n es).comp (ringL q h)
      let y0 := matM n es (fun i => toZ2 (cshift i))
      by_cases hbot : ∀ p ∈ perpSub (LinearMap.range T), p = 0
      · left
        obtain ⟨htop, hker⟩ := range_eq_top_of_perp_eq_bot hmq T hbot
        intro y
        rw [hH y, fiber_card_outputOf n es h cshift y, fiber_card_affine T y0 (bitsEquiv m y),
          htop, if_pos Submodule.mem_top, hker]
      · right
        push Not at hbot
        obtain ⟨p0, hp0mem, hp0ne⟩ := hbot
        obtain ⟨c, hprop, hp0eq⟩ := perp_nonzero_gives_proper n es h p0 hp0mem hp0ne
        have huniq : ∀ p ∈ perpSub (LinearMap.range T), p = 0 ∨ p = p0 := fun p hp =>
          if hpz : p = 0 then Or.inl hpz
          else Or.inr (perp_at_most_one_nonzero n es h p p0 hp hp0mem hpz hp0ne)
        obtain ⟨hrange, hker⟩ := range_eq_ker_dot_of_perp_unique hmpos hmq T p0 hp0ne hp0mem huniq
        let b : Bool := decide (dot p0 y0 ≠ 0)
        have hb_eq : toZ2 b = dot p0 y0 := by
          dsimp only [b]
          by_cases h0 : dot p0 y0 = 0
          · simp [h0, toZ2]
          · simp [h0, toZ2, zmod2_eq_one_of_ne_zero h0]
        have hb_aff : aff = true ∨ b = false := by
          rcases haff with ha | hc0
          · exact Or.inl ha
          · right
            have hy0z : y0 = 0 := by
              have hcz : (fun i => toZ2 (cshift i)) = 0 := by
                funext i; rw [hc0 i]; rfl
              change matM n es (fun i => toZ2 (cshift i)) = 0
              rw [hcz, map_zero]
            simp only [b, hy0z, dot_zero_right, ne_eq, not_true_eq_false, decide_false]
        refine ⟨c, b, hprop, hb_aff, fun y => ?_⟩
        rw [hH y, fiber_card_outputOf n es h cshift y, fiber_card_affine T y0 (bitsEquiv m y),
          hrange, LinearMap.mem_ker, hker]
        have hmem_iff : dotLin p0 (bitsEquiv m y - y0) = 0 ↔ parOf m (normalOf c) y = b := by
          change dot p0 (bitsEquiv m y - y0) = 0 ↔ _
          have hsub : dot p0 (bitsEquiv m y - y0) = dot p0 (bitsEquiv m y) - dot p0 y0 := by
            have := (dotLin p0).map_sub (bitsEquiv m y) y0
            exact this
          rw [hsub, sub_eq_zero, ← hb_eq, hp0eq, ← toZ2_parOf m (normalOf c) y]
          exact ⟨fun he => toZ2_inj he, fun he => congrArg toZ2 he⟩
        have hpow : 2 ^ (q - m + 1) = 2 * base := by
          dsimp only [base]; rw [pow_succ, mul_comm]
        by_cases hp : parOf m (normalOf c) y = b
        · rw [if_pos (hmem_iff.2 hp), if_pos hp, hpow]
        · rw [if_neg (fun hm => hp (hmem_iff.1 hm)), if_neg hp]
    · rintro (hunif | ⟨c, b, hprop, haff_b, hH⟩)
      · let h : Fin q → Fin 3 := fun _ => ⟨0, by omega⟩
        let cshift : Fin q → Bool := fun _ => false
        refine ⟨h, cshift, Or.inr (fun _ => rfl), fun y => ?_⟩
        rw [hunif y, fiber_card_outputOf n es h cshift y]
        let T := (matM n es).comp (ringL q h)
        have hbot : ∀ p ∈ perpSub (LinearMap.range T), p = 0 := by
          intro p hp
          have hlaw := (mem_perp_comp_iff n es h p).1 hp
          have hwz : matMT n es p = 0 := by
            funext j
            have hlj := hlaw j
            simp only [h] at hlj
            simpa using hlj
          exact matMT_injective n es (by rw [hwz, map_zero])
        obtain ⟨htop, hker⟩ := range_eq_top_of_perp_eq_bot hmq T hbot
        rw [fiber_card_affine T _ (bitsEquiv m y), htop, if_pos Submodule.mem_top, hker]
      · let p0 : Fin m → ZMod 2 := fun j => toZ2 ((normalOf c).testBit j.val)
        have hp0ne : p0 ≠ 0 := by
          intro h0
          have := congrFun h0 ⟨0, by omega⟩
          simp only [p0, (normalOf_testBit c).1, Pi.zero_apply, toZ2_true] at this
          exact absurd this (by decide)
        have hno2 := proper_gives_no_consec_zeros n es c hprop
        obtain ⟨h, hlaw⟩ := exists_h_for_word hq3 (matMT n es p0) hno2
        let T := (matM n es).comp (ringL q h)
        have hp0mem : p0 ∈ perpSub (LinearMap.range T) := (mem_perp_comp_iff n es h p0).2 hlaw
        have huniq : ∀ p ∈ perpSub (LinearMap.range T), p = 0 ∨ p = p0 := fun p hp =>
          if hpz : p = 0 then Or.inl hpz
          else Or.inr (perp_at_most_one_nonzero n es h p p0 hp hp0mem hpz hp0ne)
        obtain ⟨hrange, hker⟩ := range_eq_ker_dot_of_perp_unique hmpos hmq T p0 hp0ne hp0mem huniq
        let cshift : Fin q → Bool := fun i => b && decide (i.val = 0)
        have hcshift_aff : aff = true ∨ ∀ i, cshift i = false := by
          rcases haff_b with ha | hb0
          · exact Or.inl ha
          · exact Or.inr (fun i => by simp [cshift, hb0])
        let y0 := matM n es (fun i => toZ2 (cshift i))
        have hy0_dot : dot p0 y0 = toZ2 b := by
          dsimp only [y0]
          rw [dot_matM]
          simp only [dot]
          rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin q)]
          · rw [matMT_eval_anchor n es p0 0 (by omega)]
            simp only [p0, (normalOf_testBit c).1, toZ2_true, one_mul, cshift, decide_true, Bool.and_true]
          · intro i _ hi
            have hne : i.val ≠ 0 := fun he => hi (Fin.ext he)
            simp [cshift, hne, toZ2]
          · intro hm; exact absurd (Finset.mem_univ _) hm
        refine ⟨h, cshift, hcshift_aff, fun y => ?_⟩
        rw [hH y, fiber_card_outputOf n es h cshift y, fiber_card_affine T y0 (bitsEquiv m y),
          hrange, LinearMap.mem_ker, hker]
        have hmem_iff : dotLin p0 (bitsEquiv m y - y0) = 0 ↔ parOf m (normalOf c) y = b := by
          change dot p0 (bitsEquiv m y - y0) = 0 ↔ _
          have hsub : dot p0 (bitsEquiv m y - y0) = dot p0 (bitsEquiv m y) - dot p0 y0 :=
            (dotLin p0).map_sub (bitsEquiv m y) y0
          rw [hsub, sub_eq_zero, hy0_dot, ← toZ2_parOf m (normalOf c) y]
          exact ⟨fun he => toZ2_inj he, fun he => congrArg toZ2 he⟩
        have hpow : 2 ^ (q - m + 1) = 2 * base := by
          dsimp only [base]; rw [pow_succ, mul_comm]
        by_cases hp : parOf m (normalOf c) y = b
        · rw [if_pos (hmem_iff.2 hp), if_pos hp, hpow]
        · rw [if_neg (fun hm => hp (hmem_iff.1 hm)), if_neg hp]
  refine ⟨hchar, ?_⟩
  let B := {b : Bool // aff = true ∨ b = false}
  let PC := {c : C // proper c}
  let mkH : Unit ⊕ (PC × B) → {H : Y → ℕ // realizes H} := fun s =>
    match s with
    | Sum.inl () => ⟨fun _ => base, (hchar _).2 (Or.inl (fun _ => rfl))⟩
    | Sum.inr (c, b) => ⟨fun y => if parOf m (normalOf c.1) y = b.1 then 2 * base else 0,
        (hchar _).2 (Or.inr ⟨c.1, b.1, c.2, b.2, fun _ => rfl⟩)⟩
  have hmkH_inj : Function.Injective mkH := by
    intro s1 s2 heq
    have hval := congrArg Subtype.val heq
    cases s1 with
    | inl u1 =>
      cases s2 with
      | inl u2 => rfl
      | inr cb2 =>
        exfalso
        rcases cb2 with ⟨c2, b2⟩
        cases hb2 : b2.1
        · have hy := congrFun hval ⟨1, Nat.one_lt_pow (by omega) (by omega)⟩
          dsimp only [mkH] at hy
          rw [parOf_one c2.1, hb2] at hy
          simp at hy
          omega
        · have hy := congrFun hval ⟨0, Nat.two_pow_pos m⟩
          dsimp only [mkH] at hy
          rw [parOf_zero, hb2] at hy
          simp at hy
          omega
    | inr cb1 =>
      cases s2 with
      | inl u2 =>
        exfalso
        rcases cb1 with ⟨c1, b1⟩
        cases hb1 : b1.1
        · have hy := congrFun hval ⟨1, Nat.one_lt_pow (by omega) (by omega)⟩
          dsimp only [mkH] at hy
          rw [parOf_one c1.1, hb1] at hy
          simp at hy
          omega
        · have hy := congrFun hval ⟨0, Nat.two_pow_pos m⟩
          dsimp only [mkH] at hy
          rw [parOf_zero, hb1] at hy
          simp at hy
          omega
      | inr cb2 =>
        rcases cb1 with ⟨c1, b1⟩
        rcases cb2 with ⟨c2, b2⟩
        have hb_eq : b1.1 = b2.1 := by
          have hy := congrFun hval ⟨0, Nat.two_pow_pos m⟩
          dsimp only [mkH] at hy
          rw [parOf_zero, parOf_zero] at hy
          cases hb1 : b1.1 <;> cases hb2 : b2.1 <;> rw [hb1, hb2] at hy <;> simp at hy <;> try rfl
          all_goals omega
        have hpar_eq : ∀ y : Y, parOf m (normalOf c1.1) y = parOf m (normalOf c2.1) y := by
          intro y
          have hy := congrFun hval y
          dsimp only [mkH] at hy
          rw [hb_eq] at hy
          cases hp1 : parOf m (normalOf c1.1) y <;> cases hp2 : parOf m (normalOf c2.1) y <;>
            cases hb2 : b2.1 <;> rw [hp1, hp2, hb2] at hy <;> simp at hy <;> try rfl
          all_goals omega
        have hc_eq : c1.1 = c2.1 := normalOf_inj hpar_eq
        congr 1
        exact Prod.ext (Subtype.ext hc_eq) (Subtype.ext hb_eq)
  have hmkH_surj : Function.Surjective mkH := by
    intro ⟨H, hH⟩
    rcases (hchar H).1 hH with hunif | ⟨c, b, hprop, haff_b, hHeq⟩
    · exact ⟨Sum.inl (), Subtype.ext (funext fun y => (hunif y).symm)⟩
    · exact ⟨Sum.inr (⟨c, hprop⟩, ⟨b, haff_b⟩), Subtype.ext (funext fun y => (hHeq y).symm)⟩
  let e : Unit ⊕ (PC × B) ≃ {H : Y → ℕ // realizes H} := Equiv.ofBijective mkH ⟨hmkH_inj, hmkH_surj⟩
  rw [← Nat.card_congr e, Nat.card_sum, Nat.card_prod]
  have hunit : Nat.card Unit = 1 := by simp
  have hB : Nat.card B = if aff then 2 else 1 := by
    cases haff : aff
    · simp only [Bool.false_eq_true, ↓reduceIte]
      let eB : B ≃ Unit :=
        { toFun := fun _ => ()
          invFun := fun _ => ⟨false, Or.inr rfl⟩
          left_inv := fun b => by
            apply Subtype.ext
            rcases b.2 with h1 | h2
            · rw [haff] at h1; exact absurd h1 (by decide)
            · exact h2.symm
          right_inv := fun _ => rfl }
      rw [Nat.card_congr eB]; simp
    · simp only [↓reduceIte]
      let eB : B ≃ Bool :=
        { toFun := fun b => b.1
          invFun := fun b => ⟨b, Or.inl haff⟩
          left_inv := fun b => Subtype.ext rfl
          right_inv := fun _ => rfl }
      rw [Nat.card_congr eB, Nat.card_eq_fintype_card, Fintype.card_bool]
  rw [hunit, hB, mul_comm]

end

end PEqualNP.Outside.L_meta_33630

theorem PEqualNP.Outside.L_meta_33630 : (∀ (n : Nat) (es : List (Fin n × Fin n)) (aff : Bool),
  let m := 2*n+1
  let lo := fun i : Fin n => (1 : Nat) <<< (2*i.val+1)
  let hi := fun i : Fin n => (1 : Nat) <<< (2*i.val+2)
  let cols : List Nat := [1,1,1] ++
    (List.finRange n).flatMap (fun i => [lo i, hi i, 1]) ++
    es.flatMap (fun e => [lo e.1 ^^^ lo e.2, hi e.1 ^^^ hi e.2, 1])
  let q := cols.length
  let W := Fin (2^q)
  let Y := Fin (2^m)
  let C := Fin n → Fin 3
  let proper := fun (c : C) => ∀ e ∈ es, c e.1 ≠ c e.2
  let normal := fun (c : C) => (List.finRange n).foldl
    (fun p i => p ||| (((c i).val+1) <<< (2*i.val+1))) (1 : Nat)
  let par := fun (mask : Nat) (y : Y) => (List.range m).foldl
    (fun b j => xor b (mask.testBit j && y.val.testBit j)) false
  let output := fun (h : Fin q → Fin 3) (c : Fin q → Bool) (x : W) =>
    (List.finRange q).foldl (fun y i =>
      let a := xor (c i) (xor (x.val.testBit i.val)
        (decide ((h i).val ≠ 0) && x.val.testBit ((i.val+(h i).val)%q)))
      if a then y ^^^ (cols.get i) else y) (0 : Nat)
  let realizes := fun (H : Y → Nat) =>
    ∃ (h : Fin q → Fin 3) (c : Fin q → Bool), (aff = true ∨ ∀ i, c i = false) ∧
      ∀ y : Y, H y = Nat.card {x : W // output h c x = y.val}
  let base := 2^(q-m)
  (∀ H : Y → Nat, realizes H ↔ (∀ y, H y = base) ∨
    ∃ (c : C) (b : Bool), proper c ∧ (aff = true ∨ b = false) ∧
      ∀ y, H y = if par (normal c) y = b then 2*base else 0) ∧
  Nat.card {H : Y → Nat // realizes H} =
    1 + (if aff then 2 else 1) * Nat.card {c : C // proper c}) :=
  PEqualNP.Outside.L_meta_33630.main_result
