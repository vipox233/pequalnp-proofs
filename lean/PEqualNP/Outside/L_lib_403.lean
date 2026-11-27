import PEqualNP.Defs
import PEqualNP.Outside.L_lib_394

namespace PEqualNP.Outside.L_lib_403_aux

-- The path-count recurrence and the pair enumeration are from L-lib-402.
open Finset

def massF (w : Nat) (rows : Nat → Nat → Bool) (h seed tail : Nat) : Nat :=
  ((List.range (2 ^ (w + h))).filter (fun bits =>
    bits % (2 ^ w) == seed && (bits >>> h) % (2 ^ w) == tail &&
    (List.range h).all (fun i => rows i ((bits >>> i) % (2 * 2 ^ w))))).length

theorem filter_congr_mem {α : Type} {l : List α} {p q : α → Bool}
    (h : ∀ x ∈ l, p x = q x) : l.filter p = l.filter q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.filter_cons, h a (List.mem_cons_self ..),
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem list_all_true {α : Type} {l : List α} {p : α → Bool}
    (h : ∀ x ∈ l, p x = true) : l.all p = true := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons, h a (List.mem_cons_self ..),
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx)), Bool.and_true]

theorem list_all_congr {α : Type} {l : List α} {p q : α → Bool}
    (h : ∀ x ∈ l, p x = q x) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons, h a (List.mem_cons_self ..),
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem range_add_eq (a b : Nat) :
    List.range (a + b) = List.range a ++ (List.range b).map (· + a) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← Nat.add_assoc, List.range_succ, ih, List.range_succ, List.map_append,
      List.map_singleton, List.append_assoc, Nat.add_comm b a]

theorem filter_length_split {α : Type} (l : List α) (p q : α → Bool) :
    (l.filter p).length = (l.filter (fun x => p x && q x)).length +
      (l.filter (fun x => p x && !q x)).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.filter_cons]
    cases p a <;> cases q a <;> simp [ih] <;> omega

theorem filter_false_length {α : Type} (l : List α) (p : α → Bool)
    (h : ∀ x ∈ l, p x = false) : (l.filter p).length = 0 := by
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro x hx
  simp [h x hx]

theorem filter_range_eq_single (N k : Nat) (hk : k < N) :
    ((List.range N).filter (fun x => x == k)).length = 1 := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [List.range_succ, List.filter_append, List.length_append, List.filter_cons, List.filter_nil]
    by_cases h : N = k
    · subst h
      have h0 : ((List.range N).filter (fun x => x == N)).length = 0 := by
        apply filter_false_length
        intro x hx
        rw [List.mem_range] at hx
        simp [Nat.ne_of_lt hx]
      simp [h0]
    · have hk' : k < N := by omega
      simp [ih hk', h]

theorem two_mul_H (w : Nat) (hw : 0 < w) : 2 * (2 ^ w / 2) = 2 ^ w := by
  cases w with
  | zero => omega
  | succ w =>
    rw [Nat.pow_succ, Nat.mul_div_cancel _ (by decide : 0 < 2), Nat.mul_comm]

theorem H_pos (w : Nat) (hw : 0 < w) : 0 < 2 ^ w / 2 := by
  have h1 := two_mul_H w hw
  have h2 : 0 < 2 ^ w := Nat.pow_pos (by decide : 0 < 2)
  omega

theorem pow_add_mul (a b : Nat) : 2 ^ (a + b) = 2 ^ a * 2 ^ b :=
  Nat.pow_add 2 a b

theorem shift_mod_twoD (w h i b lo : Nat) (hi : i < h) :
    ((lo + b * 2 ^ (w + h)) >>> i) % (2 * 2 ^ w) = (lo >>> i) % (2 * 2 ^ w) := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have hsplit : 2 ^ (w + h) = 2 ^ i * ((2 * 2 ^ w) * 2 ^ (h - 1 - i)) := by
    have he : w + h = i + (1 + w + (h - 1 - i)) := by omega
    rw [he, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_one]
  have hmul : b * 2 ^ (w + h) = (b * (2 * 2 ^ w) * 2 ^ (h - 1 - i)) * 2 ^ i := by
    rw [hsplit]; ring
  rw [hmul, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide : 0 < 2))]
  have hmul2 : b * (2 * 2 ^ w) * 2 ^ (h - 1 - i) = (2 * 2 ^ w) * (b * 2 ^ (h - 1 - i)) := by ring
  rw [hmul2, Nat.add_mul_mod_self_left]

theorem add_pow_mod_D (w h b lo : Nat) :
    (lo + b * 2 ^ (w + h)) % 2 ^ w = lo % 2 ^ w := by
  rw [Nat.pow_add]
  have : b * (2 ^ w * 2 ^ h) = 2 ^ w * (b * 2 ^ h) := by ring
  rw [this, Nat.add_mul_mod_self_left]

theorem shift_h_val (w h b lo : Nat) (hlo : lo < 2 ^ (w + h)) (hb : b < 2) :
    ((lo + b * 2 ^ (w + h)) >>> h) % (2 * 2 ^ w) = b * 2 ^ w + lo / 2 ^ h := by
  rw [Nat.shiftRight_eq_div_pow]
  have h1 : b * 2 ^ (w + h) = (b * 2 ^ w) * 2 ^ h := by
    rw [Nat.pow_add]; ring
  rw [h1, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide : 0 < 2))]
  have h2 : lo / 2 ^ h < 2 ^ w := by
    rw [Nat.pow_add, Nat.mul_comm] at hlo
    exact Nat.div_lt_of_lt_mul hlo
  rw [Nat.add_comm, Nat.mod_eq_of_lt]
  have : b = 0 ∨ b = 1 := by omega
  rcases this with rfl | rfl <;> omega

theorem shift_h1_val (w h b lo : Nat) (hw : 0 < w) (hlo : lo < 2 ^ (w + h)) (hb : b < 2) :
    ((lo + b * 2 ^ (w + h)) >>> (h + 1)) % 2 ^ w = b * (2 ^ w / 2) + (lo / 2 ^ h) / 2 := by
  rw [Nat.shiftRight_eq_div_pow, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  have h1 : b * 2 ^ (w + h) = (b * 2 ^ w) * 2 ^ h := by
    rw [Nat.pow_add]; ring
  rw [h1, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide : 0 < 2))]
  have h2H := two_mul_H w hw
  have h2 : b * 2 ^ w = (b * (2 ^ w / 2)) * 2 := by
    conv_lhs => rw [← h2H]
    ring
  rw [h2, Nat.add_mul_div_right _ _ (by decide : 0 < 2), Nat.add_comm]
  have hlt : lo / 2 ^ h < 2 ^ w := by
    rw [Nat.pow_add, Nat.mul_comm] at hlo
    exact Nat.div_lt_of_lt_mul hlo
  have hlt2 : (lo / 2 ^ h) / 2 < 2 ^ w / 2 := by omega
  have : b = 0 ∨ b = 1 := by omega
  rcases this with rfl | rfl
  · rw [Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]

theorem mass_step (w : Nat) (hw : 0 < w) (rows : Nat → Nat → Bool) (h s z : Nat)
    (hz : z < 2 ^ w) :
    massF w rows (h + 1) s z =
      (if rows h ((z / (2 ^ w / 2)) * 2 ^ w + 2 * (z % (2 ^ w / 2))) then
        massF w rows h s (2 * (z % (2 ^ w / 2))) else 0) +
      (if rows h ((z / (2 ^ w / 2)) * 2 ^ w + (2 * (z % (2 ^ w / 2)) + 1)) then
        massF w rows h s (2 * (z % (2 ^ w / 2)) + 1) else 0) := by
  set D := 2 ^ w with hD
  set H := D / 2 with hH
  have h2H : 2 * H = D := two_mul_H w hw
  have hHpos : 0 < H := H_pos w hw
  set b0 := z / H with hb0
  set u := z % H with hu
  have hz_eq : z = b0 * H + u := by
    have := Nat.div_add_mod z H
    rw [Nat.mul_comm] at this
    rw [hb0, hu]
    omega
  have hu_lt : u < H := Nat.mod_lt z hHpos
  have hb0_lt : b0 < 2 := by
    rw [hb0]
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, h2H]; exact hz)
  set N := 2 ^ (w + h) with hN
  have h2N : 2 ^ (w + (h + 1)) = N + N := by
    rw [← Nat.add_assoc, Nat.pow_succ, Nat.mul_two]
  unfold massF
  rw [h2N, range_add_eq N N, List.filter_append, List.length_append,
    List.filter_map, List.length_map]
  set P : Nat → Bool := fun bits =>
    bits % D == s && (bits >>> (h + 1)) % D == z &&
    (List.range (h + 1)).all (fun i => rows i ((bits >>> i) % (2 * D)))
  have hbranch : ∀ b : Nat, b < 2 →
      ((List.range N).filter (fun lo => P (lo + b * N))).length =
        if b = b0 then
          (if rows h (b0 * D + 2 * u) then massF w rows h s (2 * u) else 0) +
          (if rows h (b0 * D + (2 * u + 1)) then massF w rows h s (2 * u + 1) else 0)
        else 0 := by
    intro b hb
    by_cases hbb : b = b0
    · simp only [hbb, ↓reduceIte]
      subst hbb
      rw [filter_length_split (List.range N) (fun lo => P (lo + b0 * N))
        (fun lo => (lo / 2 ^ h) % 2 == 0)]
      congr 1
      · cases hr : rows h (b0 * D + 2 * u)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          apply filter_false_length
          intro lo hlo
          rw [List.mem_range] at hlo
          have hs1 := shift_h1_val w h b0 lo hw hlo hb
          have hsh := shift_h_val w h b0 lo hlo hb
          have hlo_div_lt : lo / 2 ^ h < D := by
            rw [hN, Nat.pow_add, Nat.mul_comm] at hlo
            exact Nat.div_lt_of_lt_mul hlo
          by_cases hcond : (lo / 2 ^ h) / 2 = u ∧ (lo / 2 ^ h) % 2 = 0
          · have hval : lo / 2 ^ h = 2 * u := by omega
            have : P (lo + b0 * N) = false := by
              simp only [P, List.range_succ, List.all_append, List.all_cons, List.all_nil,
                Bool.and_true]
              rw [hsh, hval, hr]
              simp
            simp [this]
          · by_cases hm : (lo / 2 ^ h) % 2 = 0
            · have hne : (lo / 2 ^ h) / 2 ≠ u := fun he => hcond ⟨he, hm⟩
              have hne2 : b0 * H + (lo / 2 ^ h) / 2 ≠ z := by omega
              have : ((lo + b0 * N) >>> (h + 1)) % D = b0 * H + (lo / 2 ^ h) / 2 := hs1
              simp [P, this, hne2]
            · simp [hm]
        · simp only [↓reduceIte]
          unfold massF
          congr 1
          apply filter_congr_mem
          intro lo hlo
          rw [List.mem_range] at hlo
          have hs0 : (lo + b0 * N) % D = lo % D := add_pow_mod_D w h b0 lo
          have hs1 : ((lo + b0 * N) >>> (h + 1)) % D = b0 * H + (lo / 2 ^ h) / 2 :=
            shift_h1_val w h b0 lo hw hlo hb
          have hsh : ((lo + b0 * N) >>> h) % (2 * D) = b0 * D + lo / 2 ^ h :=
            shift_h_val w h b0 lo hlo hb
          have hall : (List.range h).all (fun i => rows i (((lo + b0 * N) >>> i) % (2 * D))) =
              (List.range h).all (fun i => rows i ((lo >>> i) % (2 * D))) := by
            apply list_all_congr
            intro i hi
            rw [List.mem_range] at hi
            rw [shift_mod_twoD w h i b0 lo hi]
          have hlo_div_lt : lo / 2 ^ h < D := by
            rw [hN, Nat.pow_add, Nat.mul_comm] at hlo
            exact Nat.div_lt_of_lt_mul hlo
          simp only [P, List.range_succ, List.all_append, List.all_cons, List.all_nil,
            Bool.and_true, hs0, hs1, hsh, hall]
          rw [← hD, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hlo_div_lt]
          by_cases hval : lo / 2 ^ h = 2 * u
          · simp [hval, hr, ← hz_eq]
          · have hq : ¬ ((b0 * H + (lo / 2 ^ h) / 2 = z) ∧ (lo / 2 ^ h) % 2 = 0) := by omega
            have hfalse : ((b0 * H + (lo / 2 ^ h) / 2 == z) && ((lo / 2 ^ h) % 2 == 0)) = false := by
              by_cases ha : b0 * H + (lo / 2 ^ h) / 2 = z
              · have hb' : (lo / 2 ^ h) % 2 ≠ 0 := fun h' => hq ⟨ha, h'⟩
                simp [ha, hb']
              · simp [ha]
            have hlhs : ((lo % D == s && (b0 * H + (lo / 2 ^ h) / 2 == z) &&
                ((List.range h).all (fun i => rows i ((lo >>> i) % (2 * D))) &&
                rows h (b0 * D + lo / 2 ^ h))) && ((lo / 2 ^ h) % 2 == 0)) = false := by
              cases h1 : (b0 * H + (lo / 2 ^ h) / 2 == z)
              · simp
              · cases h2 : ((lo / 2 ^ h) % 2 == 0)
                · simp
                · rw [h1, h2] at hfalse
                  exact absurd hfalse (by decide)
            rw [hlhs]
            simp [hval]
      · cases hr : rows h (b0 * D + (2 * u + 1))
        · simp only [Bool.false_eq_true, ↓reduceIte]
          apply filter_false_length
          intro lo hlo
          rw [List.mem_range] at hlo
          have hs1 := shift_h1_val w h b0 lo hw hlo hb
          have hsh := shift_h_val w h b0 lo hlo hb
          have hlo_div_lt : lo / 2 ^ h < D := by
            rw [hN, Nat.pow_add, Nat.mul_comm] at hlo
            exact Nat.div_lt_of_lt_mul hlo
          by_cases hcond : (lo / 2 ^ h) / 2 = u ∧ (lo / 2 ^ h) % 2 ≠ 0
          · have hval : lo / 2 ^ h = 2 * u + 1 := by omega
            have : P (lo + b0 * N) = false := by
              simp only [P, List.range_succ, List.all_append, List.all_cons, List.all_nil,
                Bool.and_true]
              rw [hsh, hval, hr]
              simp
            simp [this]
          · by_cases hm : (lo / 2 ^ h) % 2 = 0
            · simp [hm]
            · have hne : (lo / 2 ^ h) / 2 ≠ u := fun he => hcond ⟨he, hm⟩
              have hne2 : b0 * H + (lo / 2 ^ h) / 2 ≠ z := by omega
              have : ((lo + b0 * N) >>> (h + 1)) % D = b0 * H + (lo / 2 ^ h) / 2 := hs1
              simp [P, this, hne2]
        · simp only [↓reduceIte]
          unfold massF
          congr 1
          apply filter_congr_mem
          intro lo hlo
          rw [List.mem_range] at hlo
          have hs0 : (lo + b0 * N) % D = lo % D := add_pow_mod_D w h b0 lo
          have hs1 : ((lo + b0 * N) >>> (h + 1)) % D = b0 * H + (lo / 2 ^ h) / 2 :=
            shift_h1_val w h b0 lo hw hlo hb
          have hsh : ((lo + b0 * N) >>> h) % (2 * D) = b0 * D + lo / 2 ^ h :=
            shift_h_val w h b0 lo hlo hb
          have hall : (List.range h).all (fun i => rows i (((lo + b0 * N) >>> i) % (2 * D))) =
              (List.range h).all (fun i => rows i ((lo >>> i) % (2 * D))) := by
            apply list_all_congr
            intro i hi
            rw [List.mem_range] at hi
            rw [shift_mod_twoD w h i b0 lo hi]
          have hlo_div_lt : lo / 2 ^ h < D := by
            rw [hN, Nat.pow_add, Nat.mul_comm] at hlo
            exact Nat.div_lt_of_lt_mul hlo
          simp only [P, List.range_succ, List.all_append, List.all_cons, List.all_nil,
            Bool.and_true, hs0, hs1, hsh, hall]
          rw [← hD, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hlo_div_lt]
          by_cases hval : lo / 2 ^ h = 2 * u + 1
          · have hdiv2 : (2 * u + 1) / 2 = u := by omega
            have hmod2 : (2 * u + 1) % 2 = 1 := by omega
            simp [hval, hdiv2, hmod2, hr, ← hz_eq]
          · have hq : ¬ ((b0 * H + (lo / 2 ^ h) / 2 = z) ∧ (lo / 2 ^ h) % 2 ≠ 0) := by omega
            have hfalse : ((b0 * H + (lo / 2 ^ h) / 2 == z) && !((lo / 2 ^ h) % 2 == 0)) = false := by
              by_cases ha : b0 * H + (lo / 2 ^ h) / 2 = z
              · have hb' : (lo / 2 ^ h) % 2 = 0 := by
                  by_contra hne
                  exact hq ⟨ha, hne⟩
                simp [ha, hb']
              · simp [ha]
            have hlhs : ((lo % D == s && (b0 * H + (lo / 2 ^ h) / 2 == z) &&
                ((List.range h).all (fun i => rows i ((lo >>> i) % (2 * D))) &&
                rows h (b0 * D + lo / 2 ^ h))) && !((lo / 2 ^ h) % 2 == 0)) = false := by
              cases h1 : (b0 * H + (lo / 2 ^ h) / 2 == z)
              · simp
              · cases h2 : ((lo / 2 ^ h) % 2 == 0)
                · rw [h1, h2] at hfalse
                  exact absurd hfalse (by decide)
                · simp
            rw [hlhs]
            simp [hval]
    · simp only [hbb, ↓reduceIte]
      apply filter_false_length
      intro lo hlo
      rw [List.mem_range] at hlo
      have hs1 : ((lo + b * N) >>> (h + 1)) % D = b * H + (lo / 2 ^ h) / 2 :=
        shift_h1_val w h b lo hw hlo hb
      have hlo_div_lt : lo / 2 ^ h < D := by
        rw [hN, Nat.pow_add, Nat.mul_comm] at hlo
        exact Nat.div_lt_of_lt_mul hlo
      have hne : b * H + (lo / 2 ^ h) / 2 ≠ z := by
        have hcases : (b = 0 ∧ b0 = 1) ∨ (b = 1 ∧ b0 = 0) := by
          generalize b0 = m at hb0_lt hbb ⊢
          omega
        rcases hcases with ⟨rfl, hb0e⟩ | ⟨rfl, hb0e⟩
        · have hz1 : z = H + u := by rw [hz_eq, hb0e]; simp
          have hlt2 : (lo / 2 ^ h) / 2 < H := by omega
          rw [hz1]; simp; omega
        · have hz0 : z = u := by rw [hz_eq, hb0e]; simp
          rw [hz0, Nat.one_mul]
          exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hu_lt (Nat.le_add_right H _))
      simp [P, hs1, hne]
  have h0 := hbranch 0 (by decide)
  have h1 := hbranch 1 (by decide)
  have e0 : (fun lo => P (lo + 0 * N)) = P := by
    funext lo; simp
  have e1 : (fun lo => P (lo + 1 * N)) = (P ∘ (· + N)) := by
    funext lo; simp [Function.comp]
  rw [e0] at h0
  rw [e1] at h1
  rw [h0, h1]
  have hcases : b0 = 0 ∨ b0 = 1 := by
    generalize b0 = m at hb0_lt ⊢
    omega
  rcases hcases with hb0v | hb0v <;> simp [hb0v, massF]

theorem mass_zero (w : Nat) (rows : Nat → Nat → Bool) (s z : Nat) (hs : s < 2 ^ w) :
    massF w rows 0 s z = if s = z then 1 else 0 := by
  unfold massF
  by_cases hsz : s = z
  · subst hsz
    rw [if_pos rfl, ← filter_range_eq_single (2 ^ (w + 0)) s (by simpa using hs)]
    congr 1
    apply filter_congr_mem
    intro bits hbits
    rw [List.mem_range] at hbits
    have hb : bits < 2 ^ w := by simpa using hbits
    simp [Nat.mod_eq_of_lt hb]
  · rw [if_neg hsz]
    apply filter_false_length
    intro bits hbits
    rw [List.mem_range] at hbits
    have hb : bits < 2 ^ w := by simpa using hbits
    by_cases h1 : bits = s
    · subst h1; simp [Nat.mod_eq_of_lt hb, hsz]
    · simp [Nat.mod_eq_of_lt hb, h1]

theorem list_range_filter_length_eq_card (N : Nat) (p : Nat → Bool) :
    ((List.range N).filter p).length = ((Finset.range N).filter (fun x => p x = true)).card := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.filter_append, List.length_append, List.filter_cons, List.filter_nil,
      Finset.range_add_one, Finset.filter_insert]
    cases hp : p N
    · simp [ih]
    · simp only [List.length_cons, List.length_nil, Nat.zero_add, ↓reduceIte]
      rw [Finset.card_insert_of_notMem, ih]
      simp

theorem list_range_map_sum (N : Nat) (f : Nat → Nat) :
    ((List.range N).map f).sum = ∑ i ∈ Finset.range N, f i := by
  induction N with
  | zero => simp
  | succ N ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem card_pairs (D : Nat) (hD : 0 < D) (P : Nat → Nat → Prop) [∀ a b, Decidable (P a b)] :
    ((Finset.range (D * D)).filter (fun key => P (key % D) (key / D))).card =
      ∑ q ∈ Finset.range D, ((Finset.range D).filter (fun z => P q z)).card := by
  simp only [Finset.card_filter]
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun key => (key % D, key / D)) (fun p => p.1 + D * p.2) ?_ ?_ ?_ ?_ ?_
  · intro key hk
    rw [Finset.mem_range] at hk
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨Nat.mod_lt _ hD, Nat.div_lt_of_lt_mul hk⟩
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    rw [Finset.mem_range]
    have : D * (p.2 + 1) ≤ D * D := Nat.mul_le_mul_left D hp.2
    rw [Nat.mul_succ] at this
    omega
  · intro key _
    exact Nat.mod_add_div key D
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    ext
    · simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp.1]
    · simp [Nat.add_mul_div_left _ _ hD, Nat.div_eq_of_lt hp.1]
  · intro key _
    rfl

def addEdges {V : Type} (flip : V → V) (pick : V → Bool)
    (M : V → V → Nat) (s t : V) : Nat :=
  M s t + if pick (flip t) then M s (flip t) else 0

theorem le_addEdges {V : Type} (flip : V → V) (pick : V → Bool)
    (M : V → V → Nat) (s t : V) : M s t ≤ addEdges flip pick M s t :=
  Nat.le_add_right _ _

theorem addEdges_twice {V : Type} (flip : V → V) (pick : V → Bool)
    (hinv : Function.Involutive flip)
    (hdisj : ∀ x, pick x = true → pick (flip x) = false)
    (M : V → V → Nat) (s t : V) :
    addEdges flip pick (addEdges flip pick M) s t =
      M s t + if pick (flip t) then 2 * M s (flip t) else 0 := by
  cases hp : pick (flip t)
  · simp [addEdges, hp]
  · have ht := hdisj (flip t) hp
    rw [hinv t] at ht
    simp [addEdges, hp, ht, hinv t]
    omega

theorem odd_addEdges_twice {V : Type} (flip : V → V) (pick : V → Bool)
    (hinv : Function.Involutive flip)
    (hdisj : ∀ x, pick x = true → pick (flip x) = false)
    (M : V → V → Nat) (s t : V) :
    (addEdges flip pick (addEdges flip pick M) s t).testBit 0 = (M s t).testBit 0 := by
  rw [addEdges_twice flip pick hinv hdisj]
  cases hp : pick (flip t)
  · simp
  · simp only [ite_true, Nat.testBit_eq_decide_div_mod_eq, Nat.pow_zero, Nat.div_one]
    rw [show (M s t + 2 * M s (flip t)) % 2 = M s t % 2 by omega]

theorem addEdges_positive {V : Type} (flip : V → V) (pick : V → Bool)
    (hinv : Function.Involutive flip) (M : V → V → Nat) (s t : V)
    (hp : pick t = true) (hm : 0 < M s t) :
    0 < addEdges flip pick M s (flip t) := by
  simp only [addEdges, hinv t, hp, Bool.true_eq, if_true]
  omega

def oddPairs {V : Type} [Fintype V] [DecidableEq V] (M : V → V → Nat) :
    Finset (V × V) :=
  Finset.univ.filter fun p => (M p.1 p.2).testBit 0 = true

theorem oddPairs_addEdges_le {V : Type} [Fintype V] [DecidableEq V]
    (flip : V → V) (pick : V → Bool) (hinv : Function.Involutive flip)
    (M : V → V → Nat) (hdiag : ∀ s t, (M s t).testBit 0 = true ↔ s = t) :
    (oddPairs (addEdges flip pick M)).card ≤
      Fintype.card V + (Finset.univ.filter fun s => pick s = true).card := by
  let diag := (Finset.univ : Finset V).image fun s => (s, s)
  let edges := (Finset.univ.filter fun s => pick s = true).image fun s => (s, flip s)
  have hsub : oddPairs (addEdges flip pick M) ⊆ diag ∪ edges := by
    intro p hp
    obtain ⟨s, t⟩ := p
    simp only [oddPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    by_cases hs : s = t
    · subst t
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩)
    · have h0 : (M s t).testBit 0 = false := Bool.eq_false_of_not_eq_true (hs ∘ (hdiag s t).mp)
      cases hpick : pick (flip t)
      · simpa [addEdges, hpick, h0] using hp
      · have h1 : (M s (flip t)).testBit 0 = true := by
          simp only [addEdges, hpick, Bool.true_eq, if_true,
            Nat.testBit_eq_decide_div_mod_eq, Nat.pow_zero, Nat.div_one] at hp h0 ⊢
          simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hp h0 ⊢
          omega
        have he : s = flip t := (hdiag s _).mp h1
        refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s, ?_, ?_⟩)
        · simp [he, hpick]
        · simp [he, hinv t]
  have hcard₁ : diag.card = Fintype.card V :=
    Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)
  have hcard₂ : edges.card = (Finset.univ.filter fun s => pick s = true).card :=
    Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)
  exact (Finset.card_le_card hsub).trans (by
    simpa only [hcard₁, hcard₂] using Finset.card_union_le diag edges)

abbrev Word (w : Nat) := Fin w → Bool

def readBits (w : Nat) (n : Nat) : Word w := fun j => n.testBit j

theorem readBits_inj {w : Nat} {x y : Fin (2 ^ w)}
    (h : readBits w x.val = readBits w y.val) : x = y := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < w
  · exact congrFun h ⟨j, hj⟩
  · rw [Nat.testBit_lt_two_pow, Nat.testBit_lt_two_pow] <;>
      exact Nat.lt_of_lt_of_le (Fin.isLt _) (Nat.pow_le_pow_right (by decide) (by omega))

noncomputable def wordEquiv (w : Nat) : Fin (2 ^ w) ≃ Word w :=
  Equiv.ofBijective (fun n => readBits w n.val)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨fun _ _ => readBits_inj,
      by simp [Word]⟩)

theorem readBits_cons (d a b : Nat) (hb : b < 2) :
    readBits (d + 1) (2 * a + b) = Fin.cons (b.testBit 0) (readBits d a) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [readBits, Fin.cons_zero, Fin.val_zero, Nat.testBit_eq_decide_div_mod_eq,
      Nat.pow_zero, Nat.div_one]
    rw [show (2 * a + b) % 2 = b % 2 by omega]
  · simp only [readBits, Fin.cons_succ, Fin.val_succ, Nat.testBit_div_two]
    rw [Nat.testBit_add_one, show (2 * a + b) / 2 = a by omega]

theorem readBits_snoc (d a b : Nat) (ha : a < 2 ^ d) :
    readBits (d + 1) (b * 2 ^ d + a) =
      Fin.snoc (α := fun _ : Fin (d + 1) => Bool) (readBits d a) (b.testBit 0) := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [readBits, Nat.mul_comm b, Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_lt_two_pow ha]
  · have hj := j.isLt
    simp [readBits, Nat.mul_comm b, Nat.testBit_two_pow_mul_add _ ha, show ¬d ≤ j.val by omega]

def scanRows (d : Nat) (table : Nat → Word (d + 1) → Bool → Bool)
    (h n : Nat) : Bool :=
  table h (readBits (d + 1) (n % 2 ^ (d + 1))) ((n / 2 ^ (d + 1)).testBit 0)

noncomputable def scanMass (d : Nat) (table : Nat → Word (d + 1) → Bool → Bool)
    (h : Nat) (s t : Word (d + 1)) : Nat :=
  massF (d + 1) (scanRows d table) h ((wordEquiv (d + 1)).symm s).val
    ((wordEquiv (d + 1)).symm t).val

theorem scanMass_zero (d : Nat) (table : Nat → Word (d + 1) → Bool → Bool)
    (s t : Word (d + 1)) :
    scanMass d table 0 s t = if s = t then 1 else 0 := by
  rw [scanMass, mass_zero _ _ _ _ (Fin.isLt _)]
  simp [(Fin.val_injective.eq_iff), (wordEquiv (d + 1)).symm.injective.eq_iff]

theorem scanMass_step (d : Nat) (table : Nat → Word (d + 1) → Bool → Bool)
    (h : Nat) (s : Word (d + 1)) (tail : Word d) (b : Bool) :
    scanMass d table (h + 1) s (Fin.snoc (α := fun _ => Bool) tail b) =
      (if table h (Fin.cons false tail) b then scanMass d table h s (Fin.cons false tail) else 0) +
      (if table h (Fin.cons true tail) b then scanMass d table h s (Fin.cons true tail) else 0) := by
  let D := 2 ^ (d + 1)
  let H := 2 ^ d
  let z := ((wordEquiv (d + 1)).symm (Fin.snoc (α := fun _ => Bool) tail b)).val
  have hD : 0 < D := Nat.two_pow_pos _
  have hH : 0 < H := Nat.two_pow_pos _
  have hhalf : D / 2 = H := by simp [D, H, pow_succ]
  have hz : z < D := Fin.isLt _
  have hzbits : readBits (d + 1) z = Fin.snoc (α := fun _ => Bool) tail b :=
    (wordEquiv (d + 1)).apply_symm_apply _
  have hsplit : z / H * H + z % H = z := by simpa [Nat.mul_comm] using Nat.div_add_mod z H
  have htail : readBits d (z % H) = tail := by
    have hh := readBits_snoc d (z % H) (z / H) (Nat.mod_lt _ hH)
    rw [hsplit, hzbits] at hh
    funext j
    simpa using (congrFun hh j.castSucc).symm
  have hb : (z / H).testBit 0 = b := by
    have hh := readBits_snoc d (z % H) (z / H) (Nat.mod_lt _ hH)
    rw [hsplit, hzbits] at hh
    simpa using (congrFun hh (Fin.last d)).symm
  have hpin (a : Nat) (ha : a < 2) : 2 * (z % H) + a < D := by
    have hmod := Nat.mod_lt z hH
    dsimp [D, H] at *
    rw [pow_succ]
    omega
  have hbits (a : Nat) (ha : a < 2) :
      readBits (d + 1) (2 * (z % H) + a) = Fin.cons (a.testBit 0) tail := by
    rw [readBits_cons d _ a ha, htail]
  have hinv (a : Nat) (ha : a < 2) :
      ((wordEquiv (d + 1)).symm (Fin.cons (a.testBit 0) tail)).val =
        2 * (z % H) + a := by
    let k : Fin D := ⟨_, hpin a ha⟩
    have hh : wordEquiv (d + 1) k = Fin.cons (a.testBit 0) tail := hbits a ha
    exact congrArg Fin.val (((wordEquiv (d + 1)).symm_apply_eq).mpr hh.symm)
  have hrow (a : Nat) (ha : a < 2) :
      scanRows d table h ((z / H) * D + (2 * (z % H) + a)) =
        table h (Fin.cons (a.testBit 0) tail) b := by
    dsimp only [scanRows]
    change table h (readBits (d + 1) (((z / H) * D + (2 * (z % H) + a)) % D))
      ((((z / H) * D + (2 * (z % H) + a)) / D).testBit 0) = _
    rw [Nat.mul_comm (z / H) D, Nat.mul_add_mod_self_left,
      Nat.mod_eq_of_lt (hpin a ha), Nat.mul_add_div (by omega : 0 < D),
      Nat.div_eq_of_lt (hpin a ha)]
    simp only [Nat.add_zero, hbits a ha, hb]
  unfold scanMass
  change massF (d + 1) (scanRows d table) (h + 1) _ z = _
  rw [mass_step _ (Nat.succ_pos _) _ _ _ _ hz, hhalf]
  change (if scanRows d table h ((z / H) * D + 2 * (z % H)) then _ else _) + _ = _
  have h0 := hrow 0 (by decide)
  have h1 := hrow 1 (by decide)
  have hi0 := hinv 0 (by decide)
  have hi1 := hinv 1 (by decide)
  change scanRows d table h ((z / H) * D + 2 * (z % H)) = table h (Fin.cons false tail) b at h0
  change scanRows d table h ((z / H) * D + (2 * (z % H) + 1)) = table h (Fin.cons true tail) b at h1
  change ((wordEquiv (d + 1)).symm (Fin.cons false tail)).val = 2 * (z % H) at hi0
  change ((wordEquiv (d + 1)).symm (Fin.cons true tail)).val = 2 * (z % H) + 1 at hi1
  rw [h0, h1, hi0, hi1]

def rot {d : Nat} (r : Nat) (s : Word (d + 1)) : Word (d + 1) :=
  fun j => s ⟨(j.val + r) % (d + 1), Nat.mod_lt _ (Nat.succ_pos d)⟩

theorem rot_zero {d : Nat} (s : Word (d + 1)) : rot 0 s = s := by
  funext j
  simp [rot, Nat.mod_eq_of_lt j.isLt]

theorem rot_add {d : Nat} (a b : Nat) (s : Word (d + 1)) :
    rot a (rot b s) = rot (a + b) s := by
  funext j
  unfold rot
  congr 1
  apply Fin.ext
  dsimp only
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]

theorem rot_period {d : Nat} (s : Word (d + 1)) : rot (d + 1) s = s := by
  funext j
  unfold rot
  congr 1
  apply Fin.ext
  exact (Nat.add_mod_right _ _).trans (Nat.mod_eq_of_lt j.isLt)

theorem rot_inj {d : Nat} (r : Nat) : Function.Injective (rot (d := d) r) := by
  intro x y h
  let w := d + 1
  have hr : r % w < w := Nat.mod_lt _ (Nat.succ_pos _)
  let a := w - r % w
  have hh : a + r % w = w := Nat.sub_add_cancel (Nat.le_of_lt hr)
  have he (u : Word w) : rot (a + r) u = u := by
    funext j
    unfold rot
    congr 1
    apply Fin.ext
    change (j.val + (a + r)) % w = j.val
    rw [← Nat.add_assoc, ← Nat.add_mod_mod (j.val + a) r w, Nat.add_assoc, hh,
      Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
  have h' := congrArg (rot a) h
  rw [rot_add, rot_add, he, he] at h'
  exact h'

def flipAt {w : Nat} (j : Fin w) (s : Word w) : Word w :=
  fun k => if k = j then !s k else s k

theorem flipAt_involutive {w : Nat} (j : Fin w) : Function.Involutive (flipAt j) := by
  intro x
  funext k
  by_cases h : k = j <;> simp [flipAt, h]

theorem rot_flipAt {d : Nat} (j : Fin (d + 1)) (s : Word (d + 1)) :
    rot j.val (flipAt j s) = flipAt 0 (rot j.val s) := by
  funext k
  unfold rot flipAt
  have he : (⟨(k.val + j.val) % (d + 1), Nat.mod_lt _ (Nat.succ_pos d)⟩ : Fin (d + 1)) = j ↔ k = 0 := by
    rw [Fin.ext_iff, Fin.ext_iff]
    change (k.val + j.val) % (d + 1) = j.val ↔ k.val = 0
    constructor
    · intro h
      have hk := k.isLt
      by_cases hlt : k.val + j.val < d + 1
      · rw [Nat.mod_eq_of_lt hlt] at h
        omega
      · have hsub : k.val + j.val - (d + 1) < d + 1 := by
          have := j.isLt
          omega
        rw [Nat.mod_eq_sub_mod (show d + 1 ≤ k.val + j.val by omega),
          Nat.mod_eq_of_lt hsub] at h
        omega
    · intro h
      simp [h, Nat.mod_eq_of_lt j.isLt]
  simp only [he]

theorem rot_cons {d : Nat} (tail : Word d) (b : Bool) :
    rot 1 (Fin.cons b tail) = Fin.snoc (α := fun _ => Bool) tail b := by
  funext k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · simpa [rot] using (Fin.snoc_last tail b).symm
  · have h : (i.val + 1) < d + 1 := by have := i.isLt; omega
    have hi : (⟨(i.val + 1) % (d + 1), Nat.mod_lt _ (Nat.succ_pos d)⟩ : Fin (d + 1)) = i.succ :=
      Fin.ext (Nat.mod_eq_of_lt h)
    simp [rot, hi]

theorem flipAt_cons {d : Nat} (tail : Word d) (b : Bool) :
    flipAt 0 (Fin.cons b tail) = Fin.cons (!b) tail := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k <;> simp [flipAt]

def branchRow {d : Nat} (pick : Word (d + 1) → Bool) (x : Word (d + 1))
    (b : Bool) : Bool :=
  (b == x 0) || pick x

theorem scanMass_branch {d : Nat} (table : Nat → Word (d + 1) → Bool → Bool)
    (h : Nat) (pick : Word (d + 1) → Bool) (ht : table h = branchRow pick)
    (s x : Word (d + 1)) :
    scanMass d table (h + 1) s (rot 1 x) =
      addEdges (flipAt 0) pick (scanMass d table h) s x := by
  let tail : Word d := fun i => x i.succ
  have hx : Fin.cons (x 0) tail = x := Fin.cons_self_tail _
  conv => lhs; rw [← hx, rot_cons]
  rw [scanMass_step, ht, ← hx]
  unfold addEdges
  rw [flipAt_cons]
  cases x 0 <;> simp [branchRow, Nat.add_comm]

noncomputable def rotEquiv (d r : Nat) : Equiv.Perm (Word (d + 1)) :=
  Equiv.ofBijective (rot r) (Finite.injective_iff_bijective.mp (rot_inj r))

noncomputable def sweepRow {d : Nat} (j : Fin (d + 1)) (pick : Word (d + 1) → Bool)
    (i : Nat) : Word (d + 1) → Bool → Bool :=
  branchRow (if i = j.val then pick ∘ (rotEquiv d i).symm else fun _ => false)

theorem scanMass_sweep {d : Nat} (table : Nat → Word (d + 1) → Bool → Bool)
    (h : Nat) (j : Fin (d + 1)) (pick : Word (d + 1) → Bool)
    (ht : ∀ i < d + 1, table (h + i) = sweepRow j pick i)
    (i : Nat) (hi : i ≤ d + 1) (s x : Word (d + 1)) :
    scanMass d table (h + i) s (rot i x) =
      if i ≤ j.val then scanMass d table h s x
      else addEdges (flipAt j) pick (scanMass d table h) s x := by
  induction i generalizing x with
  | zero => simp [rot_zero]
  | succ i ih =>
    have hui : i < d + 1 := by omega
    have h' := scanMass_branch table (h + i)
      (if i = j.val then pick ∘ (rotEquiv d i).symm else fun _ => false) (ht i hui) s (rot i x)
    rw [rot_add, Nat.add_comm 1 i, Nat.add_assoc] at h'
    rw [h']
    by_cases hij : i = j.val
    · subst i
      have hbefore (y : Word (d + 1)) := ih (Nat.le_of_lt hui) y
      simp only [le_refl, ite_true] at hbefore
      simp only [addEdges, Function.comp_apply, ite_true, ← rot_flipAt, hbefore]
      have hsame (y : Word (d + 1)) : (rotEquiv d j.val).symm (rot j.val y) = y :=
        (rotEquiv d j.val).symm_apply_apply y
      rw [hsame]
      simp
    · simp only [addEdges, if_neg hij, Bool.false_eq_true, ite_false, Nat.add_zero]
      rw [ih (Nat.le_of_lt hui) x]
      have he : (i ≤ j.val) = (i + 1 ≤ j.val) := propext (by omega)
      simp only [← he, addEdges]

theorem scanMass_sweep_end {d : Nat} (table : Nat → Word (d + 1) → Bool → Bool)
    (h : Nat) (j : Fin (d + 1)) (pick : Word (d + 1) → Bool)
    (ht : ∀ i < d + 1, table (h + i) = sweepRow j pick i) :
    scanMass d table (h + (d + 1)) = addEdges (flipAt j) pick (scanMass d table h) := by
  funext s t
  simpa only [rot_period, if_neg (not_le_of_gt j.isLt)] using
    scanMass_sweep table h j pick ht (d + 1) (le_refl _) s t

theorem scanMass_double_sweep {d : Nat} (table : Nat → Word (d + 1) → Bool → Bool)
    (h : Nat) (j : Fin (d + 1)) (pick : Word (d + 1) → Bool)
    (ht : ∀ i < d + 1, table (h + i) = sweepRow j pick i)
    (hu : ∀ i < d + 1, table (h + (d + 1) + i) = sweepRow j pick i)
    (hp : ∀ x, pick x = true → pick (flipAt j x) = false)
    (s t : Word (d + 1)) :
    scanMass d table (h + (d + 1) + (d + 1)) s t =
      scanMass d table h s t +
        if pick (flipAt j t) then 2 * scanMass d table h s (flipAt j t) else 0 := by
  rw [scanMass_sweep_end _ _ _ _ hu, scanMass_sweep_end _ _ _ _ ht]
  exact addEdges_twice _ _ (flipAt_involutive j) hp _ _ _

theorem oddPairs_comp_right {V : Type} [Fintype V] [DecidableEq V]
    (e : Equiv.Perm V) (M : V → V → Nat) :
    (oddPairs (fun s t => M s (e t))).card = (oddPairs M).card := by
  let e' := (Equiv.refl V).prodCongr e
  apply Finset.card_bij (fun p _ => e' p)
  · intro p hp
    simpa [oddPairs, e'] using hp
  · intro p _ q _ hpq
    exact e'.injective hpq
  · intro p hp
    refine ⟨e'.symm p, ?_, e'.apply_symm_apply p⟩
    have he (q : V × V) : q ∈ oddPairs (fun s t => M s (e t)) ↔ e' q ∈ oddPairs M := by
      simp [oddPairs, e']
    rw [he, e'.apply_symm_apply]
    exact hp

theorem oddPairs_diag_card {V : Type} [Fintype V] [DecidableEq V]
    (M : V → V → Nat) (h : ∀ s t, (M s t).testBit 0 = true ↔ s = t) :
    (oddPairs M).card = Fintype.card V := by
  have he : oddPairs M = Finset.univ.image (fun s => (s, s)) := by
    ext ⟨s, t⟩
    simp only [oddPairs, Finset.mem_filter, Finset.mem_univ, true_and, h]
    constructor
    · rintro rfl
      exact Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩
    · intro hm
      obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hm
      exact (congrArg Prod.fst hu).symm.trans (congrArg Prod.snd hu)
  rw [he, Finset.card_image_of_injective _ (fun _ _ hh => congrArg Prod.fst hh)]
  rfl

theorem oddPairs_double_sweep {d : Nat} (table : Nat → Word (d + 1) → Bool → Bool)
    (h : Nat) (j : Fin (d + 1)) (pick : Word (d + 1) → Bool)
    (ht : ∀ i < d + 1, table (h + i) = sweepRow j pick i)
    (hu : ∀ i < d + 1, table (h + (d + 1) + i) = sweepRow j pick i)
    (hp : ∀ x, pick x = true → pick (flipAt j x) = false)
    (hdiag : ∀ s t, (scanMass d table h s t).testBit 0 = true ↔ s = t)
    (i : Nat) (hi : i ≤ 2 * (d + 1)) :
    (oddPairs (scanMass d table (h + i))).card ≤
      2 ^ (d + 1) + (Finset.univ.filter fun s => pick s = true).card := by
  classical
  have hc : Fintype.card (Word (d + 1)) = 2 ^ (d + 1) := by simp [Word]
  let M := scanMass d table h
  let A := addEdges (flipAt j) pick M
  have hA := oddPairs_addEdges_le (flipAt j) pick (flipAt_involutive j) M hdiag
  have hM := oddPairs_diag_card M hdiag
  have hAA : oddPairs (addEdges (flipAt j) pick A) = oddPairs M := by
    ext ⟨s, t⟩
    simp only [oddPairs, Finset.mem_filter, Finset.mem_univ, true_and, A,
      odd_addEdges_twice _ _ (flipAt_involutive j) hp]
  rw [← hc]
  by_cases he : i ≤ d + 1
  · rw [← oddPairs_comp_right (rotEquiv d i)]
    have hs : (fun s t => scanMass d table (h + i) s (rotEquiv d i t)) =
        if i ≤ j.val then M else A := by
      funext s t
      change scanMass d table (h + i) s (rot i t) = _
      rw [scanMass_sweep table h j pick ht i he]
      split_ifs <;> rfl
    rw [hs]
    split_ifs
    · rw [hM]; exact Nat.le_add_right _ _
    · exact hA
  · let k := i - (d + 1)
    have hk : k ≤ d + 1 := by dsimp [k]; omega
    have hi' : h + i = h + (d + 1) + k := by dsimp [k]; omega
    rw [hi', ← oddPairs_comp_right (rotEquiv d k)]
    have hs : (fun s t => scanMass d table (h + (d + 1) + k) s (rotEquiv d k t)) =
        if k ≤ j.val then A else addEdges (flipAt j) pick A := by
      funext s t
      change scanMass d table (h + (d + 1) + k) s (rot k t) = _
      rw [scanMass_sweep table (h + (d + 1)) j pick hu k hk,
        scanMass_sweep_end table h j pick ht]
      split_ifs <;> rfl
    rw [hs]
    split_ifs
    · exact hA
    · rw [hAA, hM]; exact Nat.le_add_right _ _

theorem flipAt_readBits {w : Nat} (j : Fin w) {a : Nat} (ha : a < 2 ^ j.val) :
    flipAt j (readBits w a) = readBits w (a + 2 ^ j.val) := by
  funext k
  change (if k = j then !a.testBit k.val else a.testBit k.val) =
    (a + 2 ^ j.val).testBit k.val
  by_cases hk : k = j
  · subst k
    rw [if_pos rfl, Nat.add_comm, Nat.testBit_two_pow_add_eq]
  · rw [if_neg hk]
    rcases lt_or_gt_of_ne (fun h => hk (Fin.ext h)) with hlt | hgt
    · rw [Nat.add_comm, Nat.testBit_two_pow_add_gt hlt]
    · have hp : 2 ^ (j.val + 1) ≤ 2 ^ k.val :=
        Nat.pow_le_pow_right (by decide) hgt
      have hab : a + 2 ^ j.val < 2 ^ k.val := by
        apply Nat.lt_of_lt_of_le _ hp
        rw [pow_succ]
        omega
      have haa : a < 2 ^ k.val := by omega
      rw [Nat.testBit_lt_two_pow hab, Nat.testBit_lt_two_pow haa]

theorem wordWidth_eq (d : Nat) (table : Nat → Word (d + 1) → Bool → Bool)
    (h : Nat) :
    ((List.range (2 ^ (d + 1) * 2 ^ (d + 1))).filter (fun k =>
      (massF (d + 1) (scanRows d table) h (k % 2 ^ (d + 1)) (k / 2 ^ (d + 1))).testBit 0)).length =
      (oddPairs (scanMass d table h)).card := by
  rw [list_range_filter_length_eq_card]
  let D := 2 ^ (d + 1)
  let e := wordEquiv (d + 1)
  let p : Fin (D * D) ≃ Word (d + 1) × Word (d + 1) :=
    finProdFinEquiv.symm.trans (Equiv.prodComm _ _ |>.trans (e.prodCongr e))
  have hp (k : Fin (D * D)) :
      (scanMass d table h (p k).1 (p k).2).testBit 0 =
        (massF (d + 1) (scanRows d table) h (k.val % D) (k.val / D)).testBit 0 := by
    change (massF (d + 1) (scanRows d table) h
      (e.symm (e (finProdFinEquiv.symm k).2)).val
      (e.symm (e (finProdFinEquiv.symm k).1)).val).testBit 0 = _
    rw [e.symm_apply_apply, e.symm_apply_apply]
    rfl
  apply Finset.card_bij (fun k hk => p ⟨k, Finset.mem_range.mp (Finset.mem_filter.mp hk).1⟩)
  · intro k hk
    simp only [oddPairs, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hp]
    exact (Finset.mem_filter.mp hk).2
  · intro k _ l _ hkl
    exact congrArg Fin.val (p.injective hkl)
  · intro q hq
    let k := p.symm q
    have he : p k = q := p.apply_symm_apply _
    refine ⟨k.val, ?_, he⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr k.isLt, ?_⟩
    rw [← hp, he]
    exact (Finset.mem_filter.mp hq).2

structure Batch (w extra : Nat) where
  coordinate : Fin w
  pick : Word w → Bool
  disjoint : ∀ x, pick x = true → pick (flipAt coordinate x) = false
  card_le : (Finset.univ.filter fun x => pick x = true).card ≤ extra

def Batch.apply {w extra : Nat} (b : Batch w extra) (M : Word w → Word w → Nat) :=
  addEdges (flipAt b.coordinate) b.pick (addEdges (flipAt b.coordinate) b.pick M)

theorem Batch.le_apply {w extra : Nat} (b : Batch w extra) (M : Word w → Word w → Nat)
    (s t : Word w) : M s t ≤ b.apply M s t :=
  (le_addEdges _ _ _ _ _).trans (le_addEdges _ _ _ _ _)

theorem Batch.odd_apply {w extra : Nat} (b : Batch w extra) (M : Word w → Word w → Nat)
    (s t : Word w) : (b.apply M s t).testBit 0 = (M s t).testBit 0 :=
  odd_addEdges_twice _ _ (flipAt_involutive _) b.disjoint _ _ _

theorem Batch.positive {w extra : Nat} (b : Batch w extra) (M : Word w → Word w → Nat)
    (s x : Word w) (hp : b.pick x = true) (hm : 0 < M s x) :
    0 < b.apply M s (flipAt b.coordinate x) :=
  (addEdges_positive _ _ (flipAt_involutive _) _ _ _ hp hm).trans_le
    (le_addEdges _ _ _ _ _)

def runBatches {w extra : Nat} (bs : List (Batch w extra)) (M : Word w → Word w → Nat) :=
  bs.foldl (fun N b => b.apply N) M

theorem runBatches_append {w extra : Nat} (bs cs : List (Batch w extra))
    (M : Word w → Word w → Nat) :
    runBatches (bs ++ cs) M = runBatches cs (runBatches bs M) := by
  simp [runBatches, List.foldl_append]

theorem le_runBatches {w extra : Nat} (bs : List (Batch w extra))
    (M : Word w → Word w → Nat) (s t : Word w) :
    M s t ≤ runBatches bs M s t := by
  induction bs generalizing M with
  | nil => exact le_rfl
  | cons b bs ih => exact (b.le_apply M s t).trans (ih (b.apply M))

theorem runBatches_positive {w extra : Nat} (bs : List (Batch w extra))
    (M : Word w → Word w → Nat) (b : Batch w extra) (hb : b ∈ bs)
    (s x : Word w) (hp : b.pick x = true) (hm : 0 < M s x) :
    0 < runBatches bs M s (flipAt b.coordinate x) := by
  induction bs generalizing M with
  | nil => simp at hb
  | cons c cs ih =>
    rcases List.mem_cons.mp hb with rfl | hc
    · exact (b.positive M s x hp hm).trans_le (le_runBatches cs _ _ _)
    · exact ih (c.apply M) hc (hm.trans_le (c.le_apply M s x))

def lowerWord {w : Nat} (j : Fin w) (up : Bool) (a : Nat) : Word w :=
  if up then readBits w a else flipAt j (readBits w a)

theorem lowerWord_bit {w : Nat} (j : Fin w) (up : Bool) {a : Nat} (ha : a < 2 ^ j.val) :
    lowerWord j up a j = !up := by
  have hh := Nat.testBit_lt_two_pow ha
  cases up <;> simp [lowerWord, flipAt, readBits, hh]

def blockSources {w : Nat} (j : Fin w) (up : Bool) (extra k : Nat) : Finset (Word w) :=
  ((Finset.range extra).filter fun r => k * extra + r < 2 ^ j.val).image
    (fun r => lowerWord j up (k * extra + r))

def treeBatch {w : Nat} (j : Fin w) (up : Bool) (extra k : Nat) : Batch w extra where
  coordinate := j
  pick x := decide (x ∈ blockSources j up extra k)
  disjoint := by
    intro x hx
    have hbit (y : Word w) (hy : y ∈ blockSources j up extra k) : y j = !up := by
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hy
      exact lowerWord_bit j up (Finset.mem_filter.mp hr).2
    change decide (x ∈ blockSources j up extra k) = true at hx
    apply decide_eq_false
    intro hy
    have hh := hbit x (of_decide_eq_true hx)
    have hh' := hbit (flipAt j x) hy
    simp [flipAt, hh] at hh'
  card_le := by
    have he : (Finset.univ.filter (fun x => decide (x ∈ blockSources j up extra k) = true)) =
        blockSources j up extra k := by ext; simp
    rw [he]
    exact Finset.card_image_le.trans
      ((Finset.card_filter_le _ _).trans (by rw [Finset.card_range]))

def batchCount (extra j : Nat) := (2 ^ j + extra - 1) / extra

def treeLevel {w : Nat} (j : Fin w) (up : Bool) (extra : Nat) : List (Batch w extra) :=
  (List.range (batchCount extra j.val)).map (treeBatch j up extra)

theorem treeLevel_positive {w extra : Nat} (j : Fin w) (up : Bool)
    (he : 0 < extra) {a : Nat} (ha : a < 2 ^ j.val)
    (M : Word w → Word w → Nat) (s : Word w)
    (hm : 0 < M s (lowerWord j up a)) :
    0 < runBatches (treeLevel j up extra) M s (flipAt j (lowerWord j up a)) := by
  let k := a / extra
  have hdiv := Nat.div_add_mod a extra
  have hrem := Nat.mod_lt a he
  have hk : k < batchCount extra j.val := by
    change k + 1 ≤ (2 ^ j.val + extra - 1) / extra
    apply (Nat.le_div_iff_mul_le he).2
    rw [Nat.add_mul]
    dsimp [k]
    rw [Nat.mul_comm (a / extra) extra]
    omega
  have hp : (treeBatch j up extra k).pick (lowerWord j up a) = true := by
    apply decide_eq_true
    refine Finset.mem_image.mpr ⟨a % extra, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hrem, ?_⟩, ?_⟩
    · simpa only [k, Nat.mul_comm (a / extra) extra, hdiv] using ha
    · rw [show k * extra + a % extra = a by simpa only [k, Nat.mul_comm] using hdiv]
  exact runBatches_positive _ M (treeBatch j up extra k)
    (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩) s _ hp hm

def treeLevels {w : Nat} (extra : Nat) (up : Bool) :
    (n : Nat) → n ≤ w → List (Batch w extra)
  | 0, _ => []
  | n + 1, hn =>
    let lev := treeLevel ⟨n, by omega⟩ up extra
    let rest := treeLevels extra up n (by omega)
    if up then rest ++ lev else lev ++ rest

theorem treeLevels_length {w : Nat} (extra : Nat) (up : Bool) (n : Nat) (hn : n ≤ w) :
    (treeLevels extra up n hn).length = ((List.range n).map (batchCount extra)).sum := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    cases up <;> simp [treeLevels, treeLevel, ih, Nat.add_comm]

theorem gather_positive {w extra : Nat} (he : 0 < extra)
    (n : Nat) (hn : n ≤ w) (M : Word w → Word w → Nat) (s : Word w)
    (a : Nat) (ha : a < 2 ^ n) (hm : 0 < M s (readBits w a)) :
    0 < runBatches (treeLevels extra false n hn) M s (readBits w 0) := by
  induction n generalizing a M with
  | zero =>
    have : a = 0 := by simp at ha; omega
    simpa [this, treeLevels, runBatches] using hm
  | succ n ih =>
    let j : Fin w := ⟨n, by omega⟩
    let N := runBatches (treeLevel j false extra) M
    change 0 < runBatches (treeLevel j false extra ++ treeLevels extra false n (by omega)) M s _
    rw [runBatches_append]
    by_cases hlo : a < 2 ^ n
    · exact ih _ N a hlo (hm.trans_le (le_runBatches _ _ _ _))
    · let p := a - 2 ^ n
      have hp : p < 2 ^ n := by rw [pow_succ] at ha; dsimp [p]; omega
      have heq : p + 2 ^ n = a := by dsimp [p]; omega
      have hsrc : lowerWord j false p = readBits w a := by
        change flipAt j (readBits w p) = _
        rw [flipAt_readBits j hp]
        exact congrArg (readBits w) heq
      have hpos := treeLevel_positive j false he hp M s (hsrc ▸ hm : 0 < M s (lowerWord j false p))
      change 0 < N s (flipAt j (flipAt j (readBits w p))) at hpos
      rw [flipAt_involutive] at hpos
      exact ih _ N p hp hpos

theorem broadcast_positive {w extra : Nat} (he : 0 < extra)
    (n : Nat) (hn : n ≤ w) (M : Word w → Word w → Nat) (s : Word w)
    (hm : 0 < M s (readBits w 0)) (a : Nat) (ha : a < 2 ^ n) :
    0 < runBatches (treeLevels extra true n hn) M s (readBits w a) := by
  induction n generalizing a with
  | zero =>
    have : a = 0 := by simp at ha; omega
    simpa [this, treeLevels, runBatches] using hm
  | succ n ih =>
    let j : Fin w := ⟨n, by omega⟩
    let N := runBatches (treeLevels extra true n (by omega)) M
    change 0 < runBatches (treeLevels extra true n (by omega) ++ treeLevel j true extra) M s _
    rw [runBatches_append]
    by_cases hlo : a < 2 ^ n
    · exact (ih _ a hlo).trans_le (le_runBatches _ _ _ _)
    · let p := a - 2 ^ n
      have hp : p < 2 ^ n := by rw [pow_succ] at ha; dsimp [p]; omega
      have heq : p + 2 ^ n = a := by dsimp [p]; omega
      have hpos := treeLevel_positive j true he hp N s (ih _ p hp)
      change 0 < runBatches (treeLevel j true extra) N s (flipAt j (readBits w p)) at hpos
      rw [flipAt_readBits j hp] at hpos
      simpa only [show j.val = n from rfl, heq] using hpos

noncomputable def batchRowAt {d extra : Nat} (bs : List (Batch (d + 1) extra))
    (i : Nat) : Word (d + 1) → Bool → Bool :=
  if hb : i / (2 * (d + 1)) < bs.length then
    let b := bs[i / (2 * (d + 1))]
    sweepRow b.coordinate b.pick (i % (d + 1))
  else branchRow (fun _ => false)

theorem batchRowAt_offset {d extra : Nat} (bs : List (Batch (d + 1) extra))
    (k : Nat) (hk : k < bs.length) (i : Nat) (hi : i < 2 * (d + 1)) :
    batchRowAt bs (2 * (d + 1) * k + i) =
      sweepRow bs[k].coordinate bs[k].pick (i % (d + 1)) := by
  have hq : (2 * (d + 1) * k + i) / (2 * (d + 1)) = k := by
    rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hi, Nat.add_zero]
  unfold batchRowAt
  simp only [hq, hk, dite_true]
  have hr : (2 * (d + 1) * k + i) % (d + 1) = i % (d + 1) := by
    rw [show 2 * (d + 1) * k = (d + 1) * (2 * k) by ac_rfl]
    exact Nat.mul_add_mod_self_left _ _ _
  rw [hr]

theorem scanBatches {d extra : Nat} (table : Nat → Word (d + 1) → Bool → Bool)
    (bs : List (Batch (d + 1) extra)) (h : Nat)
    (ht : ∀ k (hk : k < bs.length) i, i < 2 * (d + 1) →
      table (h + (2 * (d + 1) * k + i)) =
        sweepRow bs[k].coordinate bs[k].pick (i % (d + 1)))
    (hdiag : ∀ s t, (scanMass d table h s t).testBit 0 = true ↔ s = t) :
    scanMass d table (h + 2 * (d + 1) * bs.length) = runBatches bs (scanMass d table h) ∧
    (∀ s t, (scanMass d table (h + 2 * (d + 1) * bs.length) s t).testBit 0 = true ↔ s = t) ∧
    ∀ i ≤ 2 * (d + 1) * bs.length,
      (oddPairs (scanMass d table (h + i))).card ≤ 2 ^ (d + 1) + extra := by
  induction bs generalizing h with
  | nil =>
    simp only [List.length_nil, Nat.mul_zero, Nat.add_zero]
    refine ⟨rfl, hdiag, fun i hi => ?_⟩
    have : i = 0 := by omega
    simp only [this, Nat.add_zero, oddPairs_diag_card _ hdiag]
    simpa [Word] using Nat.le_add_right (2 ^ (d + 1)) extra
  | cons b bs ih =>
    let w := d + 1
    have hfirst : ∀ i < w, table (h + i) = sweepRow b.coordinate b.pick i := by
      intro i hi
      have hh := ht 0 (by simp) i (by omega)
      change table (h + (2 * w * 0 + i)) = sweepRow b.coordinate b.pick (i % w) at hh
      simpa only [Nat.mul_zero, Nat.zero_add, Nat.mod_eq_of_lt hi] using hh
    have hsecond : ∀ i < w, table (h + w + i) = sweepRow b.coordinate b.pick i := by
      intro i hi
      have he : (w + i) % w = i := by simp [Nat.add_mod, Nat.mod_eq_of_lt hi]
      have hh := ht 0 (by simp) (w + i) (by omega)
      change table (h + (2 * w * 0 + (w + i))) =
        sweepRow b.coordinate b.pick ((w + i) % w) at hh
      simpa only [Nat.mul_zero, Nat.zero_add, ← Nat.add_assoc, he] using hh
    have hend : scanMass d table (h + 2 * w) = b.apply (scanMass d table h) := by
      rw [show h + 2 * w = h + w + w by omega,
        scanMass_sweep_end table (h + w) _ _ hsecond,
        scanMass_sweep_end table h _ _ hfirst]
      rfl
    have hdiag' : ∀ s t, (scanMass d table (h + 2 * w) s t).testBit 0 = true ↔ s = t := by
      intro s t
      rw [hend, b.odd_apply]
      exact hdiag s t
    have htail : ∀ k (hk : k < bs.length) i, i < 2 * w →
        table (h + 2 * w + (2 * w * k + i)) =
          sweepRow bs[k].coordinate bs[k].pick (i % w) := by
      intro k hk i hi
      have hh := ht (k + 1) (by simp; omega) i hi
      change table (h + (2 * w * (k + 1) + i)) =
        sweepRow bs[k].coordinate bs[k].pick (i % w) at hh
      simpa only [Nat.mul_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hh
    obtain ⟨hM, hpar, hwidth⟩ := ih (h + 2 * w) htail hdiag'
    have hlen : 2 * w * (b :: bs).length = 2 * w + 2 * w * bs.length := by
      rw [List.length_cons, Nat.mul_succ, Nat.add_comm]
    change scanMass d table (h + 2 * w * (b :: bs).length) = _ ∧ _ ∧ _
    rw [hlen, ← Nat.add_assoc]
    refine ⟨hM.trans ?_, hpar, ?_⟩
    · rw [hend]
      rfl
    · intro i hi
      by_cases hle : i ≤ 2 * w
      · exact (oddPairs_double_sweep table h _ _ hfirst hsecond b.disjoint hdiag i hle).trans
          (Nat.add_le_add_left b.card_le _)
      · have hh : h + i = h + 2 * w + (i - 2 * w) := by omega
        rw [hh]
        apply hwidth
        change i - 2 * w ≤ 2 * w * bs.length
        omega

def shiftWord {d : Nat} (c : Word d → Bool) (x : Word (d + 1)) : Word (d + 1) :=
  let tail : Word d := fun j => x j.succ
  Fin.snoc (α := fun _ => Bool) tail (xor (x 0) (c tail))

theorem shiftWord_injective {d : Nat} (c : Word d → Bool) :
    Function.Injective (shiftWord c) := by
  intro x y h
  let xt : Word d := fun j => x j.succ
  let yt : Word d := fun j => y j.succ
  have ht : xt = yt := by
    funext j
    simpa [shiftWord, xt, yt] using congrFun h j.castSucc
  have hb : xor (x 0) (c xt) = xor (y 0) (c yt) := by
    simpa [shiftWord, xt, yt] using congrFun h (Fin.last d)
  rw [ht] at hb
  have hz : x 0 = y 0 := by cases c yt <;> simpa using hb
  funext j
  refine Fin.cases hz (fun j => congrFun ht j) j

noncomputable def shiftEquiv {d : Nat} (c : Word d → Bool) : Equiv.Perm (Word (d + 1)) :=
  Equiv.ofBijective (shiftWord c) (Finite.injective_iff_bijective.mp (shiftWord_injective c))

def controlRow {d : Nat} (c : Word d → Bool) (x : Word (d + 1)) (b : Bool) : Bool :=
  b == xor (x 0) (c fun j => x j.succ)

theorem scanMass_control {d : Nat} (table : Nat → Word (d + 1) → Bool → Bool)
    (h : Nat) (c : Word d → Bool) (ht : table h = controlRow c) (s x : Word (d + 1)) :
    scanMass d table (h + 1) s (shiftEquiv c x) = scanMass d table h s x := by
  let tail : Word d := fun j => x j.succ
  have hx : Fin.cons (x 0) tail = x := Fin.cons_self_tail _
  change scanMass d table (h + 1) s (Fin.snoc (α := fun _ => Bool) tail (xor (x 0) (c tail))) = _
  rw [scanMass_step, ht, ← hx]
  cases hx0 : x 0 <;> cases hc : c tail <;>
    simp [controlRow, hx0, hc, tail]

noncomputable def runControls {d : Nat} : List (Word d → Bool) → Equiv.Perm (Word (d + 1))
  | [] => Equiv.refl _
  | c :: cs => (shiftEquiv c).trans (runControls cs)

theorem runControls_apply {d : Nat} (cs : List (Word d → Bool)) (x : Word (d + 1)) :
    runControls cs x = cs.foldl (fun y c => shiftWord c y) x := by
  induction cs generalizing x with
  | nil => rfl
  | cons c cs ih => exact ih (shiftWord c x)

theorem runControls_append {d : Nat} (cs ds : List (Word d → Bool)) (x : Word (d + 1)) :
    runControls (cs ++ ds) x = runControls ds (runControls cs x) := by
  simp only [runControls_apply, List.foldl_append]

theorem scanControls {d : Nat} (table : Nat → Word (d + 1) → Bool → Bool)
    (cs : List (Word d → Bool)) (h : Nat)
    (ht : ∀ i (hi : i < cs.length), table (h + i) = controlRow cs[i]) :
    (∀ s x, scanMass d table (h + cs.length) s (runControls cs x) = scanMass d table h s x) ∧
    ∀ i ≤ cs.length, (oddPairs (scanMass d table (h + i))).card =
      (oddPairs (scanMass d table h)).card := by
  induction cs generalizing h with
  | nil =>
    refine ⟨fun s x => by simp [runControls], fun i hi => ?_⟩
    have : i = 0 := by simpa using hi
    simp [this]
  | cons c cs ih =>
    have ht0 : table h = controlRow c := ht 0 (by simp)
    have hnext : ∀ i (hi : i < cs.length), table (h + 1 + i) = controlRow cs[i] := by
      intro i hi
      have hh := ht (i + 1) (by simpa)
      change table (h + (i + 1)) = controlRow cs[i] at hh
      simpa only [Nat.add_assoc, Nat.add_comm i 1] using hh
    obtain ⟨hM, hwidth⟩ := ih (h + 1) hnext
    have hs := scanMass_control table h c ht0
    refine ⟨fun s x => ?_, fun i hi => ?_⟩
    · change scanMass d table (h + (cs.length + 1)) s (runControls cs (shiftEquiv c x)) = _
      rw [show h + (cs.length + 1) = h + 1 + cs.length by omega, hM, hs]
    · cases i with
      | zero => rfl
      | succ i =>
        change i + 1 ≤ cs.length + 1 at hi
        rw [show h + (i + 1) = h + 1 + i by omega, hwidth i (by omega),
          ← oddPairs_comp_right (shiftEquiv c)]
        rw [show (fun s x => scanMass d table (h + 1) s (shiftEquiv c x)) =
          scanMass d table h from funext fun s => funext (hs s)]

noncomputable def joinedTable {d extra : Nat} (bs : List (Batch (d + 1) extra))
    (cs : List (Word d → Bool)) (h : Nat) : Word (d + 1) → Bool → Bool :=
  if h < 2 * (d + 1) * bs.length then batchRowAt bs h
  else controlRow (cs[h - 2 * (d + 1) * bs.length]?.getD (fun _ => false))

theorem joinedTable_batch {d extra : Nat} (bs : List (Batch (d + 1) extra))
    (cs : List (Word d → Bool)) (k : Nat) (hk : k < bs.length)
    (i : Nat) (hi : i < 2 * (d + 1)) :
    joinedTable bs cs (0 + (2 * (d + 1) * k + i)) =
      sweepRow bs[k].coordinate bs[k].pick (i % (d + 1)) := by
  have hk' : 2 * (d + 1) * (k + 1) ≤ 2 * (d + 1) * bs.length :=
    Nat.mul_le_mul_left _ (by omega)
  rw [Nat.mul_succ] at hk'
  rw [Nat.zero_add, joinedTable, if_pos (by omega)]
  exact batchRowAt_offset bs k hk i hi

theorem joinedTable_control {d extra : Nat} (bs : List (Batch (d + 1) extra))
    (cs : List (Word d → Bool)) (i : Nat) (hi : i < cs.length) :
    joinedTable bs cs (2 * (d + 1) * bs.length + i) = controlRow cs[i] := by
  have hh : 2 * (d + 1) * bs.length + i - 2 * (d + 1) * bs.length = i := by omega
  simp [joinedTable, Nat.not_lt.mpr (Nat.le_add_right _ _), hh, List.getElem?_eq_getElem hi]

theorem solve (d extra L : Nat) (he : 0 < extra)
    (hL : 4 * (d + 1) * (((List.range (d + 1)).map (batchCount extra)).sum + 1) ≤ L)
    (perm : Equiv.Perm (Word (d + 1))) :
    ∃ table : Nat → Word (d + 1) → Bool → Bool,
      (∀ h ≤ L, (oddPairs (scanMass d table h)).card ≤ 2 ^ (d + 1) + extra) ∧
      ∀ s t, 0 < scanMass d table L s t ∧
        ((scanMass d table L s t).testBit 0 = true ↔ perm s = t) := by
  let w := d + 1
  let down := treeLevels (w := w) extra false w le_rfl
  let up := treeLevels (w := w) extra true w le_rfl
  let bs := down ++ up
  let B := ((List.range w).map (batchCount extra)).sum
  let T := 2 * w * bs.length
  have hbs : bs.length = B + B := by simp [bs, down, up, B, treeLevels_length]
  have hT : T + 4 * w = 4 * w * (B + 1) := by
    dsimp only [T]
    rw [hbs]
    ring
  let pad := L - (T + 4 * w)
  let pads : List (Word d → Bool) := List.replicate pad (fun _ => false)
  let R := runControls pads
  obtain ⟨control, hc⟩ := PEqualNP.Outside.L_lib_394 d (R.symm.trans perm)
  let router := (List.finRange (4 * w)).map control
  let cs := pads ++ router
  have hcs : T + cs.length = L := by
    have hbound : T + 4 * w ≤ L := hT.trans_le hL
    simp only [cs, pads, router, List.length_append, List.length_replicate, List.length_map,
      List.length_finRange, pad]
    omega
  have hperm (s : Word w) : runControls cs s = perm s := by
    rw [runControls_append, runControls_apply router, List.foldl_map]
    change (List.finRange (4 * w)).foldl (fun x i => shiftWord (control i) x) (R s) = perm s
    have hh := hc (R s)
    change (List.finRange (4 * w)).foldl (fun x i => shiftWord (control i) x) (R s) =
      perm (R.symm (R s)) at hh
    simpa only [R.symm_apply_apply] using hh
  let table := joinedTable bs cs
  have hz (s t : Word w) : (scanMass d table 0 s t).testBit 0 = true ↔ s = t := by
    rw [scanMass_zero]
    by_cases h : s = t <;> simp [h]
  obtain ⟨hbatch, hdiag, hwidth⟩ := scanBatches table bs 0 (joinedTable_batch bs cs) hz
  simp only [Nat.zero_add] at hbatch hdiag hwidth
  change scanMass d table T = runBatches bs (scanMass d table 0) at hbatch
  have hfull (s t : Word w) : 0 < scanMass d table T s t := by
    let e := wordEquiv w
    let a := e.symm s
    let b := e.symm t
    have ha : readBits w a.val = s := e.apply_symm_apply s
    have hb : readBits w b.val = t := e.apply_symm_apply t
    have hm : 0 < scanMass d table 0 s (readBits w a.val) := by
      rw [ha, scanMass_zero, if_pos rfl]
      decide
    have hg : 0 < runBatches down (scanMass d table 0) s (readBits w 0) :=
      gather_positive he w le_rfl _ s _ a.isLt hm
    rw [hbatch, runBatches_append, ← hb]
    exact broadcast_positive he w le_rfl _ s hg _ b.isLt
  obtain ⟨hroute, hrouteWidth⟩ := scanControls table cs T (joinedTable_control bs cs)
  rw [hcs] at hroute
  refine ⟨table, ?_, ?_⟩
  · intro h hh
    by_cases hb : h ≤ T
    · exact hwidth h hb
    · have ht : T + (h - T) = h := by omega
      have hi : h - T ≤ cs.length := by omega
      rw [← ht, hrouteWidth _ hi, oddPairs_diag_card _ hdiag]
      simpa [Word] using Nat.le_add_right (2 ^ w) extra
  · intro s t
    let x := (runControls cs).symm t
    have hx : runControls cs x = t := (runControls cs).apply_symm_apply t
    have hmass := hroute s x
    rw [hx] at hmass
    rw [hmass]
    refine ⟨hfull s x, (hdiag s x).trans ?_⟩
    rw [← hperm, ← hx]
    exact (runControls cs).injective.eq_iff.symm

end PEqualNP.Outside.L_lib_403_aux

theorem PEqualNP.Outside.L_lib_403 : ∀ (w : Nat), 0 < w →
  let D := 2^w
  let Rows := Nat → Nat → Bool
  let mass := fun (rows : Rows) (h seed tail : Nat) =>
    ((List.range (2^(w+h))).filter (fun bits =>
      bits % D == seed && (bits >>> h) % D == tail &&
      (List.range h).all (fun i => rows i ((bits >>> i) % (2*D))))).length
  let widthAt := fun (rows : Rows) (h : Nat) =>
    ((List.range (D*D)).filter (fun key => (mass rows h (key % D) (key / D)).testBit 0)).length
  ∀ (extra L : Nat), 0 < extra →
    let batches := ((List.range w).map (fun j => (2^j + extra - 1) / extra)).sum
    4 * w * (batches + 1) ≤ L →
    ∀ perm : Equiv.Perm (Fin D), ∃ rows : Rows,
      (∀ h ≤ L, widthAt rows h ≤ D + extra) ∧
      ∀ s z : Fin D, 0 < mass rows L s.val z.val ∧
        ((mass rows L s.val z.val).testBit 0 = true ↔ perm s = z) := by
  open PEqualNP.Outside.L_lib_403_aux in
  intro w hw
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hw)
  dsimp only
  intro extra L he hL perm
  let e := wordEquiv (d + 1)
  let wordPerm := e.symm.trans (perm.trans e)
  obtain ⟨table, hwidth, hmass⟩ := solve d extra L he hL wordPerm
  refine ⟨scanRows d table, fun h hh => ?_, fun s t => ?_⟩
  · exact (wordWidth_eq d table h).le.trans (hwidth h hh)
  · have hm := hmass (e s) (e t)
    have hs : scanMass d table L (e s) (e t) =
        massF (d + 1) (scanRows d table) L s.val t.val := by
      change massF (d + 1) (scanRows d table) L (e.symm (e s)).val (e.symm (e t)).val = _
      rw [e.symm_apply_apply, e.symm_apply_apply]
    rw [hs] at hm
    refine ⟨hm.1, hm.2.trans ?_⟩
    change e (perm (e.symm (e s))) = e t ↔ perm s = t
    rw [e.symm_apply_apply]
    exact e.injective.eq_iff
