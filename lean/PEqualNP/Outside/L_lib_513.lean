import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_513_aux

private def massF (w : Nat) (rows : Nat → Nat → Bool) (h seed tail : Nat) : Nat :=
  ((List.range (2 ^ (w + h))).filter (fun bits =>
    bits % (2 ^ w) == seed && (bits >>> h) % (2 ^ w) == tail &&
    (List.range h).all (fun i => rows i ((bits >>> i) % (2 * 2 ^ w))))).length

private def undoF (w : Nat) (v : Nat → Nat) (j : Nat) : Nat :=
  let H := 2 ^ w / 2
  let x := v (j / 2)
  let y := v (j / 2 + H)
  if j % 2 = 0 then (if x < y then x else x - y)
  else (if x < y then y - x else y)

private def tableF (w : Nat) (flags : Nat → Nat → Bool) (site pattern : Nat) : Bool :=
  let D := 2 ^ w
  let old := pattern % 2
  let newBit := (pattern / D) % 2
  decide (site < w) || (old == newBit) ||
    ((old == 1) == flags (site - w) ((pattern % D) / 2))

private def stepF (H : Nat) (f : Nat → Bool) (v : Nat → Nat) (z : Nat) : Nat :=
  if z < H then
    v (2 * z) + (if f z then v (2 * z + 1) else 0)
  else
    (if f (z - H) then 0 else v (2 * (z - H))) + v (2 * (z - H) + 1)

private def vecF (w : Nat) (flags : Nat → Nat → Bool) : Nat → Nat → Nat
  | 0, _ => 1
  | k + 1, z => stepF (2 ^ w / 2) (flags k) (vecF w flags k) z

private theorem filter_congr_mem {α : Type} {l : List α} {p q : α → Bool}
    (h : ∀ x ∈ l, p x = q x) : l.filter p = l.filter q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.filter_cons, h a (List.mem_cons_self ..),
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

private theorem list_all_true {α : Type} {l : List α} {p : α → Bool}
    (h : ∀ x ∈ l, p x = true) : l.all p = true := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons, h a (List.mem_cons_self ..),
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx)), Bool.and_true]

private theorem list_all_congr {α : Type} {l : List α} {p q : α → Bool}
    (h : ∀ x ∈ l, p x = q x) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons, h a (List.mem_cons_self ..),
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

private theorem range_add_eq (a b : Nat) :
    List.range (a + b) = List.range a ++ (List.range b).map (· + a) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← Nat.add_assoc, List.range_succ, ih, List.range_succ, List.map_append,
      List.map_singleton, List.append_assoc, Nat.add_comm b a]

private theorem filter_length_split {α : Type} (l : List α) (p q : α → Bool) :
    (l.filter p).length = (l.filter (fun x => p x && q x)).length +
      (l.filter (fun x => p x && !q x)).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.filter_cons]
    cases p a <;> cases q a <;> simp [ih] <;> omega

private theorem filter_false_length {α : Type} (l : List α) (p : α → Bool)
    (h : ∀ x ∈ l, p x = false) : (l.filter p).length = 0 := by
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro x hx
  simp [h x hx]

private theorem filter_range_eq_single (N k : Nat) (hk : k < N) :
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

private theorem two_mul_H (w : Nat) (hw : 0 < w) : 2 * (2 ^ w / 2) = 2 ^ w := by
  cases w with
  | zero => omega
  | succ w =>
    rw [Nat.pow_succ, Nat.mul_div_cancel _ (by decide : 0 < 2), Nat.mul_comm]

private theorem H_pos (w : Nat) (hw : 0 < w) : 0 < 2 ^ w / 2 := by
  have h1 := two_mul_H w hw
  have h2 : 0 < 2 ^ w := Nat.pow_pos (by decide : 0 < 2)
  omega

private theorem pow_add_mul (a b : Nat) : 2 ^ (a + b) = 2 ^ a * 2 ^ b :=
  Nat.pow_add 2 a b

private theorem mass_base (w : Nat) (flags : Nat → Nat → Bool) (s z : Nat)
    (hs : s < 2 ^ w) (hz : z < 2 ^ w) :
    massF w (tableF w flags) w s z = 1 := by
  unfold massF
  have hlen : z * 2 ^ w + s < 2 ^ (w + w) := by
    rw [Nat.pow_add]
    have h1 : (z + 1) * 2 ^ w ≤ 2 ^ w * 2 ^ w := Nat.mul_le_mul_right (2 ^ w) hz
    have h2 : (z + 1) * 2 ^ w = z * 2 ^ w + 2 ^ w := Nat.succ_mul z (2 ^ w)
    omega
  rw [← filter_range_eq_single (2 ^ (w + w)) (z * 2 ^ w + s) hlen]
  congr 1
  apply filter_congr_mem
  intro bits hbits
  rw [List.mem_range] at hbits
  have hall : (List.range w).all (fun i => tableF w flags i ((bits >>> i) % (2 * 2 ^ w))) = true := by
    apply list_all_true
    intro i hi
    rw [List.mem_range] at hi
    simp [tableF, hi]
  rw [hall, Bool.and_true]
  rw [Nat.shiftRight_eq_div_pow]
  have hdivlt : bits / 2 ^ w < 2 ^ w := by
    rw [Nat.pow_add] at hbits
    exact Nat.div_lt_of_lt_mul hbits
  rw [Nat.mod_eq_of_lt hdivlt]
  by_cases heq : bits = z * 2 ^ w + s
  · subst heq
    have hm : (z * 2 ^ w + s) % 2 ^ w = s := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hs]
    have hd : (z * 2 ^ w + s) / 2 ^ w = z := by
      rw [Nat.mul_comm, Nat.mul_add_div (Nat.pow_pos (by decide : 0 < 2)),
        Nat.div_eq_of_lt hs, Nat.add_zero]
    simp [hm, hd]
  · have hneq : (bits == z * 2 ^ w + s) = false := beq_false_of_ne heq
    rw [hneq]
    by_cases h1 : bits % 2 ^ w = s
    · by_cases h2 : bits / 2 ^ w = z
      · exfalso
        apply heq
        have := Nat.div_add_mod bits (2 ^ w)
        rw [h1, h2, Nat.mul_comm] at this
        omega
      · simp [h1, h2]
    · simp [h1]

private theorem shift_mod_twoD (w h i b lo : Nat) (hi : i < h) :
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

private theorem add_pow_mod_D (w h b lo : Nat) :
    (lo + b * 2 ^ (w + h)) % 2 ^ w = lo % 2 ^ w := by
  rw [Nat.pow_add]
  have : b * (2 ^ w * 2 ^ h) = 2 ^ w * (b * 2 ^ h) := by ring
  rw [this, Nat.add_mul_mod_self_left]

private theorem shift_h_val (w h b lo : Nat) (hlo : lo < 2 ^ (w + h)) (hb : b < 2) :
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

private theorem shift_h1_val (w h b lo : Nat) (hw : 0 < w) (hlo : lo < 2 ^ (w + h)) (hb : b < 2) :
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

private theorem mass_step (w : Nat) (hw : 0 < w) (rows : Nat → Nat → Bool) (h s z : Nat)
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

private theorem table_eval (w k u b0 old : Nat) (hw : 0 < w) (hu : u < 2 ^ w / 2)
    (hb0 : b0 < 2) (hold : old < 2) (flags : Nat → Nat → Bool) :
    tableF w flags (w + k) (b0 * 2 ^ w + (2 * u + old)) =
      ((old == b0) || ((old == 1) == flags k u)) := by
  have h2H := two_mul_H w hw
  have hlt : 2 * u + old < 2 ^ w := by omega
  have hmod2 : (b0 * 2 ^ w + (2 * u + old)) % 2 = old := by
    have : b0 * 2 ^ w + (2 * u + old) = old + 2 * (b0 * (2 ^ w / 2) + u) := by
      conv_lhs => rw [← h2H]
      ring
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hold]
  have hdivD : (b0 * 2 ^ w + (2 * u + old)) / 2 ^ w = b0 := by
    rw [Nat.mul_comm, Nat.mul_add_div (Nat.pow_pos (by decide : 0 < 2)),
      Nat.div_eq_of_lt hlt, Nat.add_zero]
  have hmodD : (b0 * 2 ^ w + (2 * u + old)) % 2 ^ w = 2 * u + old := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
  have hdiv2 : (2 * u + old) / 2 = u := by omega
  have hsub : w + k - w = k := by omega
  have hnotlt : ¬ (w + k < w) := by omega
  unfold tableF
  dsimp only
  rw [hmod2, hdivD, Nat.mod_eq_of_lt hb0, hmodD, hdiv2, hsub]
  simp [hnotlt]

private theorem mass_eq_vec (w : Nat) (hw : 0 < w) (flags : Nat → Nat → Bool) :
    ∀ k s z, s < 2 ^ w → z < 2 ^ w → massF w (tableF w flags) (w + k) s z = vecF w flags k z := by
  intro k
  induction k with
  | zero =>
    intro s z hs hz
    rw [Nat.add_zero]
    exact mass_base w flags s z hs hz
  | succ k ih =>
    intro s z hs hz
    have h2H := two_mul_H w hw
    have hHpos := H_pos w hw
    rw [← Nat.add_assoc, mass_step w hw (tableF w flags) (w + k) s z hz]
    simp only [vecF, stepF]
    by_cases hzH : z < 2 ^ w / 2
    · rw [if_pos hzH]
      have hdiv : z / (2 ^ w / 2) = 0 := Nat.div_eq_of_lt hzH
      have hmod : z % (2 ^ w / 2) = z := Nat.mod_eq_of_lt hzH
      rw [hdiv, hmod]
      have ht0 := table_eval w k z 0 0 hw hzH (by decide) (by decide) flags
      have ht1 := table_eval w k z 0 1 hw hzH (by decide) (by decide) flags
      have e0 : 0 * 2 ^ w + 2 * z = 0 * 2 ^ w + (2 * z + 0) := by omega
      rw [e0, ht0, ht1]
      rw [ih s (2 * z) hs (by omega), ih s (2 * z + 1) hs (by omega)]
      cases flags k z <;> simp
    · rw [if_neg hzH]
      have hu : z - 2 ^ w / 2 < 2 ^ w / 2 := by omega
      have hdiv : z / (2 ^ w / 2) = 1 := by
        have : z = 1 * (2 ^ w / 2) + (z - 2 ^ w / 2) := by omega
        conv_lhs => rw [this]
        rw [Nat.mul_comm, Nat.mul_add_div hHpos, Nat.div_eq_of_lt hu, Nat.add_zero]
      have hmod : z % (2 ^ w / 2) = z - 2 ^ w / 2 := by
        have : z = 1 * (2 ^ w / 2) + (z - 2 ^ w / 2) := by omega
        conv_lhs => rw [this]
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hu]
      rw [hdiv, hmod]
      have ht0 := table_eval w k (z - 2 ^ w / 2) 1 0 hw hu (by decide) (by decide) flags
      have ht1 := table_eval w k (z - 2 ^ w / 2) 1 1 hw hu (by decide) (by decide) flags
      have e0 : 1 * 2 ^ w + 2 * (z - 2 ^ w / 2) = 1 * 2 ^ w + (2 * (z - 2 ^ w / 2) + 0) := by omega
      rw [e0, ht0, ht1]
      rw [ih s (2 * (z - 2 ^ w / 2)) hs (by omega),
        ih s (2 * (z - 2 ^ w / 2) + 1) hs (by omega)]
      cases flags k (z - 2 ^ w / 2) <;> simp

private theorem vec_bounds (w : Nat) (hw : 0 < w) (flags : Nat → Nat → Bool) :
    ∀ k z, z < 2 ^ w → 1 ≤ vecF w flags k z ∧ vecF w flags k z ≤ 2 ^ k := by
  have h2H := two_mul_H w hw
  intro k
  induction k with
  | zero =>
    intro z _
    simp [vecF]
  | succ k ih =>
    intro z hz
    simp only [vecF, stepF]
    rw [Nat.pow_succ, Nat.mul_two]
    by_cases hzH : z < 2 ^ w / 2
    · rw [if_pos hzH]
      have h1 := ih (2 * z) (by omega)
      have h2 := ih (2 * z + 1) (by omega)
      cases flags k z <;> simp <;> omega
    · rw [if_neg hzH]
      have h1 := ih (2 * (z - 2 ^ w / 2)) (by omega)
      have h2 := ih (2 * (z - 2 ^ w / 2) + 1) (by omega)
      cases flags k (z - 2 ^ w / 2) <;> simp <;> omega

private theorem undo_step (w : Nat) (hw : 0 < w) (f : Nat → Bool) (v : Nat → Nat)
    (hv : ∀ j, j < 2 ^ w → 1 ≤ v j) (j : Nat) (hj : j < 2 ^ w) :
    undoF w (stepF (2 ^ w / 2) f v) j = v j := by
  have h2H := two_mul_H w hw
  have hu : j / 2 < 2 ^ w / 2 := by omega
  have h1 : 1 ≤ v (2 * (j / 2)) := hv _ (by omega)
  have h2 : 1 ≤ v (2 * (j / 2) + 1) := hv _ (by omega)
  have hnotlt : ¬ (j / 2 + 2 ^ w / 2 < 2 ^ w / 2) := by omega
  have hsub : j / 2 + 2 ^ w / 2 - 2 ^ w / 2 = j / 2 := by omega
  unfold undoF
  dsimp only
  simp only [stepF, if_pos hu, if_neg hnotlt, hsub]
  by_cases hpar : j % 2 = 0
  · have ej : 2 * (j / 2) = j := by omega
    rw [if_pos hpar]
    cases f (j / 2)
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      rw [if_pos (by omega), ej]
    · simp only [↓reduceIte, Nat.zero_add]
      rw [if_neg (by omega), Nat.add_sub_cancel, ej]
  · have ej : 2 * (j / 2) + 1 = j := by omega
    rw [if_neg hpar]
    cases f (j / 2)
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      rw [if_pos (by omega), Nat.add_sub_cancel_left, ej]
    · simp only [↓reduceIte, Nat.zero_add]
      rw [if_neg (by omega), ej]

private theorem blt_step (w : Nat) (hw : 0 < w) (f : Nat → Bool) (v : Nat → Nat)
    (hv : ∀ j, j < 2 ^ w → 1 ≤ v j) (u : Nat) (hu : u < 2 ^ w / 2) :
    Nat.blt (stepF (2 ^ w / 2) f v (u + 2 ^ w / 2)) (stepF (2 ^ w / 2) f v u) = f u := by
  have h2H := two_mul_H w hw
  have h1 : 1 ≤ v (2 * u) := hv _ (by omega)
  have h2 : 1 ≤ v (2 * u + 1) := hv _ (by omega)
  have hnotlt : ¬ (u + 2 ^ w / 2 < 2 ^ w / 2) := by omega
  have hsub : u + 2 ^ w / 2 - 2 ^ w / 2 = u := by omega
  simp only [stepF, if_pos hu, if_neg hnotlt, hsub]
  cases f u
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    cases hb : Nat.blt (v (2 * u) + v (2 * u + 1)) (v (2 * u))
    · rfl
    · have := Nat.blt_eq.mp hb
      omega
  · simp only [↓reduceIte, Nat.zero_add]
    exact Nat.blt_eq.mpr (by omega)

private theorem undo_congr (w : Nat) (hw : 0 < w) (v1 v2 : Nat → Nat)
    (h : ∀ z, z < 2 ^ w → v1 z = v2 z) (j : Nat) (hj : j < 2 ^ w) :
    undoF w v1 j = undoF w v2 j := by
  have h2H := two_mul_H w hw
  unfold undoF
  dsimp only
  rw [h (j / 2) (by omega), h (j / 2 + 2 ^ w / 2) (by omega)]

private theorem back_eq_vec (w t : Nat) (hw : 0 < w) (flags : Nat → Nat → Bool) :
    ∀ r, r ≤ t → ∀ j, j < 2 ^ w →
      Nat.rec (motive := fun _ => Nat → Nat)
        (fun z => massF w (tableF w flags) (w + t) 0 z)
        (fun _ prev => undoF w prev) r j = vecF w flags (t - r) j := by
  intro r
  induction r with
  | zero =>
    intro _ j hj
    rw [Nat.sub_zero]
    exact mass_eq_vec w hw flags t 0 j (Nat.pow_pos (by decide : 0 < 2)) hj
  | succ r ih =>
    intro hr j hj
    change undoF w (Nat.rec (motive := fun _ => Nat → Nat)
      (fun z => massF w (tableF w flags) (w + t) 0 z)
      (fun _ prev => undoF w prev) r) j = vecF w flags (t - (r + 1)) j
    rw [undo_congr w hw _ (vecF w flags (t - r)) (ih (by omega)) j hj]
    have htr : t - r = (t - (r + 1)) + 1 := by omega
    rw [htr]
    exact undo_step w hw (flags (t - (r + 1))) (vecF w flags (t - (r + 1)))
      (fun z hz => (vec_bounds w hw flags (t - (r + 1)) z hz).1) j hj

theorem solve_513 (w t : Nat) (hw : 0 < w) (flags : Nat → Nat → Bool) :
    let D := 2^w
    let Rows := Nat → Nat → Bool
    let mass := fun (rows : Rows) (h seed tail : Nat) =>
      ((List.range (2^(w+h))).filter (fun bits =>
        bits % D == seed && (bits >>> h) % D == tail &&
        (List.range h).all (fun i => rows i ((bits >>> i) % (2*D))))).length
    let H := D/2
    let undo := fun (v : Nat → Nat) (j : Nat) =>
      let x := v (j/2)
      let y := v (j/2+H)
      if j%2 = 0 then (if x < y then x else x-y)
      else (if x < y then y-x else y)
    let table : Rows := fun site pattern =>
      let old := pattern % 2
      let newBit := (pattern / D) % 2
      decide (site < w) || (old == newBit) ||
        ((old == 1) == flags (site - w) ((pattern % D) / 2))
    let last := fun z : Nat => mass table (w+t) 0 z
    let back : Nat → Nat → Nat := fun steps =>
      Nat.rec (motive := fun _ => Nat → Nat) last (fun _ prev => undo prev) steps
    (∀ s z : Fin D, mass table (w+t) s.val z.val = last z.val ∧
      1 ≤ last z.val ∧ last z.val ≤ 2^t) ∧
    (∀ j : Fin D, back t j.val = 1) ∧
    ∀ (i : Fin t) (u : Fin H),
      let v : Nat → Nat := back (t-1-i.val)
      Nat.blt (v (u.val+H)) (v u.val) = flags i.val u.val := by
  dsimp only
  have h2H := two_mul_H w hw
  refine ⟨?_, ?_, ?_⟩
  · intro s z
    have h1 : massF w (tableF w flags) (w + t) s.val z.val = vecF w flags t z.val :=
      mass_eq_vec w hw flags t s.val z.val s.isLt z.isLt
    have h2 : massF w (tableF w flags) (w + t) 0 z.val = vecF w flags t z.val :=
      mass_eq_vec w hw flags t 0 z.val (Nat.pow_pos (by decide : 0 < 2)) z.isLt
    have hb := vec_bounds w hw flags t z.val z.isLt
    change massF w (tableF w flags) (w + t) s.val z.val =
        massF w (tableF w flags) (w + t) 0 z.val ∧
      1 ≤ massF w (tableF w flags) (w + t) 0 z.val ∧
      massF w (tableF w flags) (w + t) 0 z.val ≤ 2 ^ t
    rw [h1, h2]
    exact ⟨rfl, hb.1, hb.2⟩
  · intro j
    have h := back_eq_vec w t hw flags t le_rfl j.val j.isLt
    rw [Nat.sub_self] at h
    exact h
  · intro i u
    have hr : t - 1 - i.val ≤ t := by omega
    have htr : t - (t - 1 - i.val) = i.val + 1 := by omega
    have hv1 := back_eq_vec w t hw flags (t - 1 - i.val) hr u.val (by omega)
    have hv2 := back_eq_vec w t hw flags (t - 1 - i.val) hr (u.val + 2 ^ w / 2) (by omega)
    rw [htr] at hv1 hv2
    change Nat.blt
      (Nat.rec (motive := fun _ => Nat → Nat)
        (fun z => massF w (tableF w flags) (w + t) 0 z)
        (fun _ prev => undoF w prev) (t - 1 - i.val) (u.val + 2 ^ w / 2))
      (Nat.rec (motive := fun _ => Nat → Nat)
        (fun z => massF w (tableF w flags) (w + t) 0 z)
        (fun _ prev => undoF w prev) (t - 1 - i.val) u.val) = flags i.val u.val
    rw [hv1, hv2]
    exact blt_step w hw (flags i.val) (vecF w flags i.val)
      (fun j hj => (vec_bounds w hw flags i.val j hj).1) u.val u.isLt

end PEqualNP.Outside.L_lib_513_aux

theorem PEqualNP.Outside.L_lib_513 : ∀ (w t : Nat), 0 < w →
  let D := 2^w
  let Rows := Nat → Nat → Bool
  let mass := fun (rows : Rows) (h seed tail : Nat) =>
    ((List.range (2^(w+h))).filter (fun bits =>
      bits % D == seed && (bits >>> h) % D == tail &&
      (List.range h).all (fun i => rows i ((bits >>> i) % (2*D))))).length
  let H := D/2
  let undo := fun (v : Nat → Nat) (j : Nat) =>
    let x := v (j/2)
    let y := v (j/2+H)
    if j%2 = 0 then (if x < y then x else x-y)
    else (if x < y then y-x else y)
  ∀ flags : Nat → Nat → Bool,
    let table : Rows := fun site pattern =>
      let old := pattern % 2
      let newBit := (pattern / D) % 2
      decide (site < w) || (old == newBit) ||
        ((old == 1) == flags (site - w) ((pattern % D) / 2))
    let last := fun z : Nat => mass table (w+t) 0 z
    let back : Nat → Nat → Nat := fun steps =>
      Nat.rec (motive := fun _ => Nat → Nat) last (fun _ prev => undo prev) steps
    (∀ s z : Fin D, mass table (w+t) s.val z.val = last z.val ∧
      1 ≤ last z.val ∧ last z.val ≤ 2^t) ∧
    (∀ j : Fin D, back t j.val = 1) ∧
    ∀ (i : Fin t) (u : Fin H),
      let v : Nat → Nat := back (t-1-i.val)
      Nat.blt (v (u.val+H)) (v u.val) = flags i.val u.val := by
  intro w t hw D Rows mass H undo flags
  exact PEqualNP.Outside.L_lib_513_aux.solve_513 w t hw flags
