import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_402_aux

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

def Step (w : Nat) (m : Nat → Nat → Nat) (r : Nat → Nat → Bool) : Prop :=
  ∀ h z, z < 2 ^ w → m (h + 1) z =
    (if r h ((z / (2 ^ w / 2)) * 2 ^ w + 2 * (z % (2 ^ w / 2))) then
      m h (2 * (z % (2 ^ w / 2))) else 0) +
    (if r h ((z / (2 ^ w / 2)) * 2 ^ w + (2 * (z % (2 ^ w / 2)) + 1)) then
      m h (2 * (z % (2 ^ w / 2)) + 1) else 0)

theorem pred_lt (w : Nat) (hw : 0 < w) (z : Nat) : 2 * (z % (2 ^ w / 2)) + 1 < 2 ^ w := by
  have h1 := two_mul_H w hw
  have h2 := Nat.mod_lt z (H_pos w hw)
  omega

theorem even_prop (w : Nat) (hw : 0 < w) (m : Nat → Nat → Nat) (r : Nat → Nat → Bool)
    (hstep : Step w m r) (h : Nat) (he : ∀ z, z < 2 ^ w → m h z % 2 = 0) :
    ∀ t z, z < 2 ^ w → m (h + t) z % 2 = 0 := by
  intro t
  induction t with
  | zero => exact he
  | succ t ih =>
    intro z hz
    have hp := pred_lt w hw z
    have a := ih (2 * (z % (2 ^ w / 2))) (by omega)
    have b := ih (2 * (z % (2 ^ w / 2)) + 1) hp
    rw [show h + (t + 1) = (h + t) + 1 from rfl, hstep _ z hz]
    split_ifs <;> omega

theorem odd_exists (w : Nat) (hw : 0 < w) (m : Nat → Nat → Nat) (r : Nat → Nat → Bool)
    (hstep : Step w m r) (L : Nat) (hL : ∃ z, z < 2 ^ w ∧ m L z % 2 = 1) (h : Nat) (hh : h ≤ L) :
    ∃ z, z < 2 ^ w ∧ m h z % 2 = 1 := by
  by_contra hcon
  have he : ∀ z, z < 2 ^ w → m h z % 2 = 0 := by
    intro z hz
    by_contra h1
    exact hcon ⟨z, hz, by omega⟩
  obtain ⟨z, hz, ho⟩ := hL
  have := even_prop w hw m r hstep h he (L - h) z hz
  rw [show h + (L - h) = L by omega] at this
  omega

theorem zone (w : Nat) (hw : 0 < w) (m : Nat → Nat → Nat) (r : Nat → Nat → Bool)
    (hstep : Step w m r) (c τ : Nat)
    (hrow : ∀ z, z < 2 ^ w → m c z = if z = τ then 1 else 0) :
    ∀ t, t ≤ w → ∀ z, z < 2 ^ w →
      m (c + t) z ≤ 1 ∧ (m (c + t) z ≠ 0 → z % 2 ^ (w - t) = τ / 2 ^ t) := by
  intro t
  induction t with
  | zero =>
    intro _ z hz
    rw [Nat.add_zero, hrow z hz]
    by_cases hzt : z = τ
    · subst hzt; simp [Nat.mod_eq_of_lt hz]
    · simp [hzt]
  | succ t ih =>
    intro ht z hz
    have hp := pred_lt w hw z
    obtain ⟨a1, a2⟩ := ih (by omega) (2 * (z % (2 ^ w / 2))) (by omega)
    obtain ⟨b1, b2⟩ := ih (by omega) (2 * (z % (2 ^ w / 2)) + 1) hp
    have hK : 2 ^ (w - t) = 2 * 2 ^ (w - (t + 1)) := by
      rw [show w - t = (w - (t + 1)) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    have hdvd : 2 ^ (w - (t + 1)) ∣ 2 ^ w / 2 := by
      refine ⟨2 ^ t, ?_⟩
      have h1 : 2 ^ w = 2 ^ (w - (t + 1)) * 2 ^ (t + 1) := by
        rw [← Nat.pow_add]; congr 1; omega
      have h2 := two_mul_H w hw
      rw [Nat.pow_succ] at h1
      have h3 : 2 * (2 ^ w / 2) = 2 * (2 ^ (w - (t + 1)) * 2 ^ t) := by
        rw [h2, h1]; ring
      exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h3
    have hzK : z % (2 ^ w / 2) % 2 ^ (w - (t + 1)) = z % 2 ^ (w - (t + 1)) :=
      Nat.mod_mod_of_dvd z hdvd
    have hdiv : τ / 2 ^ (t + 1) = τ / 2 ^ t / 2 := by
      rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
    have key : ∀ σ, σ / 2 = z % (2 ^ w / 2) → σ % 2 ^ (w - t) = τ / 2 ^ t →
        z % 2 ^ (w - (t + 1)) = τ / 2 ^ (t + 1) := by
      intro σ h1 h2
      rw [hdiv, ← h2, hK, Nat.mod_mul_right_div_self, h1, hzK]
    have hpar : ∀ σ, σ % 2 ^ (w - t) % 2 = σ % 2 := by
      intro σ
      exact Nat.mod_mod_of_dvd σ ⟨2 ^ (w - (t + 1)), hK⟩
    have hA := hpar (2 * (z % (2 ^ w / 2)))
    have hB := hpar (2 * (z % (2 ^ w / 2)) + 1)
    have k1 := key (2 * (z % (2 ^ w / 2))) (by omega)
    have k2 := key (2 * (z % (2 ^ w / 2)) + 1) (by omega)
    rw [show c + (t + 1) = (c + t) + 1 from rfl, hstep _ z hz]
    constructor
    · split_ifs
      · by_contra hcon
        have e1 := a2 (by omega)
        have e2 := b2 (by omega)
        rw [e1] at hA
        rw [e2] at hB
        omega
      · omega
      · omega
      · omega
    · intro hne
      by_cases ha : m (c + t) (2 * (z % (2 ^ w / 2))) = 0
      · by_cases hb : m (c + t) (2 * (z % (2 ^ w / 2)) + 1) = 0
        · exfalso; apply hne; rw [ha, hb]; simp
        · exact k2 (b2 hb)
      · exact k1 (a2 ha)

theorem count_eq_sum (D : Nat) (f : Nat → Nat) (hf : ∀ z, z < D → f z ≤ 1) :
    ((Finset.range D).filter (fun z => f z % 2 = 1)).card = ∑ z ∈ Finset.range D, f z := by
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro z hz
  have := hf z (Finset.mem_range.mp hz)
  split_ifs <;> omega

theorem seed_cuts (w : Nat) (hw : 0 < w) (m : Nat → Nat → Nat) (r : Nat → Nat → Bool)
    (hstep : Step w m r)
    (h0 : ∑ z ∈ Finset.range (2 ^ w), m 0 z ≤ 1) (L : Nat)
    (hLodd : ∃ z, z < 2 ^ w ∧ m L z % 2 = 1)
    (hL1 : ((Finset.range (2 ^ w)).filter (fun z => m L z % 2 = 1)).card ≤ 1)
    (hbr : 1 < ∑ z ∈ Finset.range (2 ^ w), m L z) :
    w ≤ ((Finset.range L).filter (fun h =>
      2 ≤ ((Finset.range (2 ^ w)).filter (fun z => m h z % 2 = 1)).card)).card := by
  have hc : ∑ z ∈ Finset.range (2 ^ w), m (Nat.findGreatest (fun h => ∑ z ∈ Finset.range (2 ^ w), m h z ≤ 1) L) z ≤ 1 :=
    Nat.findGreatest_spec (P := fun h => ∑ z ∈ Finset.range (2 ^ w), m h z ≤ 1) (Nat.zero_le L) h0
  have hcL : Nat.findGreatest (fun h => ∑ z ∈ Finset.range (2 ^ w), m h z ≤ 1) L ≤ L :=
    Nat.findGreatest_le L
  have hgt : ∀ k, Nat.findGreatest (fun h => ∑ z ∈ Finset.range (2 ^ w), m h z ≤ 1) L < k → k ≤ L →
      ¬ (∑ z ∈ Finset.range (2 ^ w), m k z ≤ 1) := fun k h1 h2 =>
    Nat.findGreatest_is_greatest (P := fun h => ∑ z ∈ Finset.range (2 ^ w), m h z ≤ 1) h1 h2
  generalize Nat.findGreatest (fun h => ∑ z ∈ Finset.range (2 ^ w), m h z ≤ 1) L = c at hc hcL hgt
  have hcne : c ≠ L := by
    rintro rfl; omega
  obtain ⟨τ, hτ, hodd⟩ := odd_exists w hw m r hstep L hLodd c hcL
  have hτm : τ ∈ Finset.range (2 ^ w) := Finset.mem_range.mpr hτ
  have hsplit := Finset.add_sum_erase (Finset.range (2 ^ w)) (m c) hτm
  have hτ1 : m c τ = 1 := by omega
  have hrest : ∑ z ∈ (Finset.range (2 ^ w)).erase τ, m c z = 0 := by omega
  have hrow : ∀ z, z < 2 ^ w → m c z = if z = τ then 1 else 0 := by
    intro z hz
    by_cases hzt : z = τ
    · rw [if_pos hzt, hzt, hτ1]
    · rw [if_neg hzt]
      exact Finset.sum_eq_zero_iff.mp hrest z
        (Finset.mem_erase.mpr ⟨hzt, Finset.mem_range.mpr hz⟩)
  have Z := zone w hw m r hstep c τ hrow
  have key : ∀ t, 1 ≤ t → t ≤ w → c + t ≤ L →
      2 ≤ ((Finset.range (2 ^ w)).filter (fun z => m (c + t) z % 2 = 1)).card := by
    intro t t1 tw tL
    rw [count_eq_sum (2 ^ w) (m (c + t)) (fun z hz => (Z t tw z hz).1)]
    have := hgt (c + t) (by omega) tL
    omega
  have hcw : c + w < L := by
    by_contra hcon
    have := key (L - c) (by omega) (by omega) (by omega)
    rw [show c + (L - c) = L by omega] at this
    omega
  calc w = (Finset.Ioc c (c + w)).card := by simp
    _ ≤ _ := by
      apply Finset.card_le_card
      intro h hh
      rw [Finset.mem_Ioc] at hh
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      have := key (h - c) (by omega) (by omega) (by omega)
      rwa [show c + (h - c) = h by omega] at this

theorem count_main (D L w : Nat) (O : Nat → Nat → Nat) (B : Finset Nat)
    (hB : B ⊆ Finset.range D)
    (h1 : ∀ h, h < L → ∀ q, q < D → 1 ≤ O h q)
    (hw : ∀ q ∈ B, w ≤ ((Finset.range L).filter (fun h => 2 ≤ O h q)).card) :
    w * B.card ≤ ∑ h ∈ Finset.range L, ((∑ q ∈ Finset.range D, O h q) - D) := by
  have e : ∀ h ∈ Finset.range L, ((Finset.range D).filter (fun q => 2 ≤ O h q)).card ≤
      (∑ q ∈ Finset.range D, O h q) - D := by
    intro h hh
    have h2 : ∑ q ∈ Finset.range D, (1 + if 2 ≤ O h q then 1 else 0) ≤
        ∑ q ∈ Finset.range D, O h q := by
      apply Finset.sum_le_sum
      intro q hq
      have := h1 h (Finset.mem_range.mp hh) q (Finset.mem_range.mp hq)
      split_ifs <;> omega
    rw [Finset.sum_add_distrib, ← Finset.card_filter, Finset.sum_const, Finset.card_range,
      smul_eq_mul, mul_one] at h2
    omega
  calc w * B.card = ∑ _q ∈ B, w := by simp [mul_comm]
    _ ≤ ∑ q ∈ B, ((Finset.range L).filter (fun h => 2 ≤ O h q)).card := Finset.sum_le_sum hw
    _ ≤ ∑ q ∈ Finset.range D, ((Finset.range L).filter (fun h => 2 ≤ O h q)).card :=
      Finset.sum_le_sum_of_subset hB
    _ = ∑ q ∈ Finset.range D, ∑ h ∈ Finset.range L, (if 2 ≤ O h q then 1 else 0) := by
      simp only [Finset.card_filter]
    _ = ∑ h ∈ Finset.range L, ∑ q ∈ Finset.range D, (if 2 ≤ O h q then 1 else 0) :=
      Finset.sum_comm
    _ = ∑ h ∈ Finset.range L, ((Finset.range D).filter (fun q => 2 ≤ O h q)).card := by
      simp only [Finset.card_filter]
    _ ≤ _ := Finset.sum_le_sum e

theorem solve (w : Nat) (hw : 0 < w) (L : Nat) (rows : Nat → Nat → Bool)
    (perm : Equiv.Perm (Fin (2 ^ w)))
    (hperm : ∀ s z : Fin (2 ^ w), (massF w rows L s.val z.val).testBit 0 = true ↔ perm s = z) :
    w * ((List.range (2 ^ w)).filter (fun q =>
      1 < ((List.range (2 ^ w)).map (fun e => massF w rows L q e)).sum)).length ≤
    ((List.range L).map (fun cut =>
      ((List.range (2 ^ w * 2 ^ w)).filter (fun key =>
        (massF w rows cut (key % 2 ^ w) (key / 2 ^ w)).testBit 0)).length - 2 ^ w)).sum := by
  have hD : 0 < 2 ^ w := Nat.pow_pos (by decide)
  have hstep : ∀ q, Step w (fun h z => massF w rows h q z) rows := fun q h z hz =>
    mass_step w hw rows h q z hz
  have hLodd : ∀ q, q < 2 ^ w → ∃ z, z < 2 ^ w ∧ massF w rows L q z % 2 = 1 := by
    intro q hq
    refine ⟨(perm ⟨q, hq⟩).val, (perm ⟨q, hq⟩).isLt, ?_⟩
    have := (hperm ⟨q, hq⟩ (perm ⟨q, hq⟩)).mpr rfl
    rw [Nat.testBit_zero] at this
    simpa using this
  have hL1 : ∀ q, q < 2 ^ w →
      ((Finset.range (2 ^ w)).filter (fun z => massF w rows L q z % 2 = 1)).card ≤ 1 := by
    intro q hq
    apply Finset.card_le_one.mpr
    intro a ha b hb
    rw [Finset.mem_filter, Finset.mem_range] at ha hb
    have h1 := (hperm ⟨q, hq⟩ ⟨a, ha.1⟩).mp (by rw [Nat.testBit_zero]; simpa using ha.2)
    have h2 := (hperm ⟨q, hq⟩ ⟨b, hb.1⟩).mp (by rw [Nat.testBit_zero]; simpa using hb.2)
    have := h1.symm.trans h2
    simpa using congrArg Fin.val this
  have hwidth : ∀ cut, ((List.range (2 ^ w * 2 ^ w)).filter (fun key =>
        (massF w rows cut (key % 2 ^ w) (key / 2 ^ w)).testBit 0)).length =
      ∑ q ∈ Finset.range (2 ^ w),
        ((Finset.range (2 ^ w)).filter (fun z => massF w rows cut q z % 2 = 1)).card := by
    intro cut
    rw [list_range_filter_length_eq_card]
    simp only [Nat.testBit_zero, decide_eq_true_eq]
    exact card_pairs (2 ^ w) hD (fun q z => massF w rows cut q z % 2 = 1)
  rw [list_range_filter_length_eq_card, list_range_map_sum]
  simp only [hwidth, list_range_map_sum, decide_eq_true_eq]
  apply count_main (2 ^ w) L w
    (fun h q => ((Finset.range (2 ^ w)).filter (fun z => massF w rows h q z % 2 = 1)).card)
  · exact Finset.filter_subset _ _
  · intro h hh q hq
    obtain ⟨z, hz, ho⟩ := odd_exists w hw (fun h z => massF w rows h q z) rows (hstep q) L
      (hLodd q hq) h (Nat.le_of_lt hh)
    exact Finset.card_pos.mpr ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hz, ho⟩⟩
  · intro q hq
    rw [Finset.mem_filter, Finset.mem_range] at hq
    apply seed_cuts w hw (fun h z => massF w rows h q z) rows (hstep q) _ L (hLodd q hq.1)
      (hL1 q hq.1) hq.2
    rw [Finset.sum_congr rfl (fun z _ => mass_zero w rows q z hq.1)]
    simp only [Finset.sum_ite_eq, Finset.mem_range]
    split_ifs <;> omega

end PEqualNP.Outside.L_lib_402_aux

open PEqualNP.Outside.L_lib_402_aux in
theorem PEqualNP.Outside.L_lib_402 : ∀ (w : Nat), 0 < w →
  let D := 2^w
  let Rows := Nat → Nat → Bool
  let mass := fun (rows : Rows) (h seed tail : Nat) =>
    ((List.range (2^(w+h))).filter (fun bits =>
      bits % D == seed && (bits >>> h) % D == tail &&
      (List.range h).all (fun i => rows i ((bits >>> i) % (2*D))))).length
  let widthAt := fun (rows : Rows) (h : Nat) =>
    ((List.range (D*D)).filter (fun key => (mass rows h (key % D) (key / D)).testBit 0)).length
  ∀ (L : Nat) (rows : Rows) (perm : Equiv.Perm (Fin D)),
    (∀ s z : Fin D, (mass rows L s.val z.val).testBit 0 = true ↔ perm s = z) →
    let branched := ((List.range D).filter (fun q =>
      1 < ((List.range D).map (fun e => mass rows L q e)).sum)).length
    w * branched ≤ ((List.range L).map (fun cut => widthAt rows cut - D)).sum
  := by
  intro w hw D Rows mass widthAt L rows perm hperm branched
  exact solve w hw L rows perm hperm
