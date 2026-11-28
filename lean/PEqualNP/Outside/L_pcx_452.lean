import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_452

private def tail452 (t : ℕ) (e : Fin 3 × Fin t) : Option (Fin t × Bool) :=
  if e.1 = 0 then some (e.2, false) else none

private def head452 (t : ℕ) (e : Fin 3 × Fin t) : Option (Fin t × Bool) :=
  some (e.2, decide (e.1 ≠ 1))

private def weight452 (t : ℕ) (g : Option {p : Fin t × Fin t // p.1 < p.2})
    (e : Fin 3 × Fin t) (diff : Bool) : ℕ :=
  if e.1 = 0 then diff.toNat
  else if e.1 = 2 then 1
  else if g.elim false (fun p => decide (p.val.1 = e.2 ∨ p.val.2 = e.2)) then
    (if diff then 1 else 3)
  else 2

private def obs452 (t : ℕ) (g : Option {p : Fin t × Fin t // p.1 < p.2})
    (p : Fin t → Fin 3) : ℕ :=
  ∑ x : Option (Fin t × Bool) → Bool,
    if (∀ i : Fin t, p i = 0 ∨ p i = (if x (some (i, false)) then 2 else 1)) ∧
      (Finset.univ.filter (fun e : Fin 3 × Fin t => x (tail452 t e) ≠ x (head452 t e))).card = 2 * t then
      ∏ e : Fin 3 × Fin t, weight452 t g e (xor (x (tail452 t e)) (x (head452 t e)))
    else 0

private def raw452 (t : ℕ) (g : Option {p : Fin t × Fin t // p.1 < p.2})
    (p : Fin t → Fin 3) : Fin 3 :=
  g.elim (0 : Fin 3) (fun e =>
    if p e.val.1 = 0 ∨ p e.val.2 = 0 then 0
    else if p e.val.1 = p e.val.2 then 1 else 2)

private def answer452 (t : ℕ) (g : Option {p : Fin t × Fin t // p.1 < p.2})
    (p : Fin t → Fin 3) : Fin 3 :=
  if obs452 t g p = obs452 t none p then (0 : Fin 3)
  else if obs452 t none p < obs452 t g p then 1 else 2

private def triFac (t : ℕ) (g : Option {p : Fin t × Fin t // p.1 < p.2})
    (p : Fin t → Fin 3) (h : Bool) (i : Fin t) : ℕ :=
  if p i = 0 then 4
  else if g.elim false (fun e => decide (e.val.1 = i ∨ e.val.2 = i)) then
    (if decide (p i = 2) = h then 3 else 1)
  else 2

private lemma obs452_eq_sum_prod (t : ℕ) (g : Option {p : Fin t × Fin t // p.1 < p.2})
    (p : Fin t → Fin 3) :
    obs452 t g p = ∑ h : Bool, ∏ i : Fin t, triFac t g p h i := by
  let eX : (Bool × (Fin t → Bool) × (Fin t → Bool)) ≃ (Option (Fin t × Bool) → Bool) :=
    { toFun := fun q v =>
        match v with
        | none => q.1
        | some (i, false) => q.2.1 i
        | some (i, true) => q.2.2 i
      invFun := fun x => (x none, fun i => x (some (i, false)), fun i => x (some (i, true)))
      left_inv := fun ⟨_, _, _⟩ => rfl
      right_inv := fun x => by
        funext v
        rcases v with _ | ⟨i, b⟩
        · rfl
        · cases b <;> rfl }
  dsimp only [obs452]
  rw [← Fintype.sum_equiv eX
    (fun q => if (∀ i : Fin t, p i = 0 ∨ p i = (if eX q (some (i, false)) then 2 else 1)) ∧
        (Finset.univ.filter (fun e : Fin 3 × Fin t => eX q (tail452 t e) ≠ eX q (head452 t e))).card = 2 * t then
        ∏ e : Fin 3 × Fin t, weight452 t g e (xor (eX q (tail452 t e)) (eX q (head452 t e))) else 0)
    (fun x => if (∀ i : Fin t, p i = 0 ∨ p i = (if x (some (i, false)) then 2 else 1)) ∧
        (Finset.univ.filter (fun e : Fin 3 × Fin t => x (tail452 t e) ≠ x (head452 t e))).card = 2 * t then
        ∏ e : Fin 3 × Fin t, weight452 t g e (xor (x (tail452 t e)) (x (head452 t e))) else 0)
    (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Fintype.sum_prod_type]
  have hinner : ∀ a : Fin t → Bool,
      ∑ b : Fin t → Bool,
        (if (∀ i : Fin t, p i = 0 ∨ p i = (if eX (h, a, b) (some (i, false)) then 2 else 1)) ∧
          (Finset.univ.filter (fun e : Fin 3 × Fin t => eX (h, a, b) (tail452 t e) ≠ eX (h, a, b) (head452 t e))).card = 2 * t then
          ∏ e : Fin 3 × Fin t, weight452 t g e (xor (eX (h, a, b) (tail452 t e)) (eX (h, a, b) (head452 t e)))
        else 0) =
      ∏ i : Fin t,
        (if p i = 0 ∨ p i = (if a i then 2 else 1) then
          (if g.elim false (fun e => decide (e.val.1 = i ∨ e.val.2 = i)) then
            (if a i = h then 3 else 1) else 2)
        else 0) := by
    intro a
    rw [Finset.sum_eq_single (fun i => !a i)]
    · have hcut : (Finset.univ.filter (fun e : Fin 3 × Fin t =>
          eX (h, a, fun i => !a i) (tail452 t e) ≠ eX (h, a, fun i => !a i) (head452 t e))).card = 2 * t := by
        rw [Finset.card_filter, Fintype.sum_prod_type_right]
        have heach : ∀ i : Fin t, ∑ k : Fin 3,
            (if eX (h, a, fun j => !a j) (tail452 t (k, i)) ≠ eX (h, a, fun j => !a j) (head452 t (k, i)) then 1 else 0) = 2 := by
          intro i
          rw [Fin.sum_univ_three]
          dsimp only [eX, Equiv.coe_fn_mk, tail452, head452]
          simp only [Fin.reduceEq, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true]
          generalize a i = ai
          cases h <;> cases ai <;> decide
        rw [Finset.sum_congr rfl fun i _ => heach i, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]
      have hprod_eq : ∏ e : Fin 3 × Fin t,
          weight452 t g e (xor (eX (h, a, fun i => !a i) (tail452 t e)) (eX (h, a, fun i => !a i) (head452 t e))) =
          ∏ i : Fin t, (if g.elim false (fun e => decide (e.val.1 = i ∨ e.val.2 = i)) then
            (if a i = h then 3 else 1) else 2) := by
        rw [Fintype.prod_prod_type_right]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Fin.prod_univ_three]
        dsimp only [eX, Equiv.coe_fn_mk, tail452, head452, weight452]
        simp only [Fin.reduceEq, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true]
        generalize a i = ai
        generalize g.elim false (fun e => decide (e.val.1 = i ∨ e.val.2 = i)) = act
        cases h <;> cases ai <;> cases act <;> decide
      by_cases hpin : ∀ i : Fin t, p i = 0 ∨ p i = (if a i then 2 else 1)
      · have hcond : (∀ i : Fin t, p i = 0 ∨ p i = (if eX (h, a, fun j => !a j) (some (i, false)) then 2 else 1)) ∧
            (Finset.univ.filter (fun e : Fin 3 × Fin t =>
              eX (h, a, fun j => !a j) (tail452 t e) ≠ eX (h, a, fun j => !a j) (head452 t e))).card = 2 * t :=
          ⟨hpin, hcut⟩
        rw [if_pos hcond, hprod_eq]
        refine Finset.prod_congr rfl fun i _ => (if_pos (hpin i)).symm
      · have hcond : ¬ ((∀ i : Fin t, p i = 0 ∨ p i = (if eX (h, a, fun j => !a j) (some (i, false)) then 2 else 1)) ∧
            (Finset.univ.filter (fun e : Fin 3 × Fin t =>
              eX (h, a, fun j => !a j) (tail452 t e) ≠ eX (h, a, fun j => !a j) (head452 t e))).card = 2 * t) :=
          fun hc => hpin hc.1
        rw [if_neg hcond]
        push_neg at hpin
        rcases hpin with ⟨i0, hi0⟩
        symm
        exact Finset.prod_eq_zero (Finset.mem_univ i0) (if_neg (fun hp => by
          rcases hp with h0 | h1
          · exact hi0.1 h0
          · exact hi0.2 h1))
    · intro b _ hb_ne
      have hex : ∃ i0 : Fin t, b i0 = a i0 := by
        by_contra hall
        push_neg at hall
        apply hb_ne; funext i
        cases hb : b i <;> cases ha : a i
        · exact (hall i (hb.trans ha.symm)).elim
        · rfl
        · rfl
        · exact (hall i (hb.trans ha.symm)).elim
      rcases hex with ⟨i0, hi0⟩
      split_ifs with hc
      · exact Finset.prod_eq_zero (Finset.mem_univ ((0 : Fin 3), i0)) (by
          dsimp only [eX, Equiv.coe_fn_mk, tail452, head452, weight452]
          simp [hi0])
      · rfl
    · intro hm; exact (hm (Finset.mem_univ _)).elim
  rw [Finset.sum_congr rfl fun a _ => hinner a]
  let F : Fin t → Bool → ℕ := fun i b =>
    if p i = 0 ∨ p i = (if b then 2 else 1) then
      (if g.elim false (fun e => decide (e.val.1 = i ∨ e.val.2 = i)) then
        (if b = h then 3 else 1) else 2)
    else 0
  change ∑ a : Fin t → Bool, ∏ i : Fin t, F i (a i) = ∏ i : Fin t, triFac t g p h i
  rw [← Fintype.prod_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.sum_bool]
  dsimp only [F, triFac]
  generalize p i = pi
  generalize g.elim false (fun e => decide (e.val.1 = i ∨ e.val.2 = i)) = act
  fin_cases pi <;> cases h <;> cases act <;> decide

private lemma obs452_none_pos (t : ℕ) (p : Fin t → Fin 3) : 0 < obs452 t none p := by
  rw [obs452_eq_sum_prod, Fintype.sum_bool]
  have h1 : 0 < ∏ i : Fin t, triFac t none p false i := by
    refine Finset.prod_pos fun i _ => ?_
    dsimp only [triFac, Option.elim]
    split_ifs <;> omega
  omega

private lemma obs_and_answer_452 (t : ℕ) (g : Option {p : Fin t × Fin t // p.1 < p.2})
    (p : Fin t → Fin 3) :
    answer452 t g p = raw452 t g p ∧
    4 * obs452 t g p = (if raw452 t g p = 0 then 4 else if raw452 t g p = 1 then 5 else 3) * obs452 t none p := by
  have hpos := obs452_none_pos t p
  have hmul : 4 * obs452 t g p =
      (if raw452 t g p = 0 then 4 else if raw452 t g p = 1 then 5 else 3) * obs452 t none p := by
    rcases g with _ | e
    · simp [raw452]
    · have huv : e.val.1 ≠ e.val.2 := ne_of_lt e.2
      let rest : Finset (Fin t) := (Finset.univ.erase e.val.1).erase e.val.2
      let R : ℕ := ∏ i ∈ rest, (if p i = 0 then 4 else 2)
      have hprod_split : ∀ (g' : Option {p : Fin t × Fin t // p.1 < p.2}) (h : Bool),
          (∀ i ∈ rest, g'.elim false (fun q => decide (q.val.1 = i ∨ q.val.2 = i)) = false) →
          ∏ i : Fin t, triFac t g' p h i =
            triFac t g' p h e.val.1 * triFac t g' p h e.val.2 * R := by
        intro g' h hrest
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e.val.1)]
        have hv_mem : e.val.2 ∈ Finset.univ.erase e.val.1 := Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_univ _⟩
        rw [← Finset.mul_prod_erase (Finset.univ.erase e.val.1) _ hv_mem]
        rw [← mul_assoc]
        congr 1
        refine Finset.prod_congr rfl fun i hi => ?_
        dsimp only [triFac]
        rw [hrest i hi]
        simp only [Bool.false_eq_true, ↓reduceIte]
      have hrest_e : ∀ i ∈ rest, (some e : Option {p : Fin t × Fin t // p.1 < p.2}).elim false
          (fun q => decide (q.val.1 = i ∨ q.val.2 = i)) = false := by
        intro i hi
        have h1 : i ≠ e.val.2 := (Finset.mem_erase.mp hi).1
        have h2 : i ≠ e.val.1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
        simp [Option.elim, h1.symm, h2.symm]
      have hobs_none : obs452 t none p =
          (triFac t none p false e.val.1 * triFac t none p false e.val.2 +
           triFac t none p true e.val.1 * triFac t none p true e.val.2) * R := by
        rw [obs452_eq_sum_prod, Fintype.sum_bool,
          hprod_split none false (fun _ _ => rfl), hprod_split none true (fun _ _ => rfl)]
        ring
      have hobs_e : obs452 t (some e) p =
          (triFac t (some e) p false e.val.1 * triFac t (some e) p false e.val.2 +
           triFac t (some e) p true e.val.1 * triFac t (some e) p true e.val.2) * R := by
        rw [obs452_eq_sum_prod, Fintype.sum_bool,
          hprod_split (some e) false hrest_e, hprod_split (some e) true hrest_e]
        ring
      rw [hobs_e, hobs_none]
      have hcoeff : 4 * (triFac t (some e) p false e.val.1 * triFac t (some e) p false e.val.2 +
            triFac t (some e) p true e.val.1 * triFac t (some e) p true e.val.2) =
          (if raw452 t (some e) p = 0 then 4 else if raw452 t (some e) p = 1 then 5 else 3) *
            (triFac t none p false e.val.1 * triFac t none p false e.val.2 +
             triFac t none p true e.val.1 * triFac t none p true e.val.2) := by
        have h9 : ∀ pu pv : Fin 3,
            4 * ((if pu = 0 then 4 else if decide (pu = 2) = false then 3 else 1) *
                 (if pv = 0 then 4 else if decide (pv = 2) = false then 3 else 1) +
                 (if pu = 0 then 4 else if decide (pu = 2) = true then 3 else 1) *
                 (if pv = 0 then 4 else if decide (pv = 2) = true then 3 else 1)) =
            (if (if pu = 0 ∨ pv = 0 then (0 : Fin 3) else if pu = pv then 1 else 2) = 0 then 4
             else if (if pu = 0 ∨ pv = 0 then (0 : Fin 3) else if pu = pv then 1 else 2) = 1 then 5 else 3) *
            ((if pu = 0 then 4 else 2) * (if pv = 0 then 4 else 2) +
             (if pu = 0 then 4 else 2) * (if pv = 0 then 4 else 2)) := by
          intro pu pv; fin_cases pu <;> fin_cases pv <;> decide
        dsimp only [triFac, raw452, Option.elim]
        simp only [true_or, or_true, decide_true, ↓reduceIte, Bool.false_eq_true]
        exact h9 (p e.val.1) (p e.val.2)
      calc 4 * ((triFac t (some e) p false e.val.1 * triFac t (some e) p false e.val.2 +
              triFac t (some e) p true e.val.1 * triFac t (some e) p true e.val.2) * R)
          = (4 * (triFac t (some e) p false e.val.1 * triFac t (some e) p false e.val.2 +
              triFac t (some e) p true e.val.1 * triFac t (some e) p true e.val.2)) * R := by ring
        _ = ((if raw452 t (some e) p = 0 then 4 else if raw452 t (some e) p = 1 then 5 else 3) *
              (triFac t none p false e.val.1 * triFac t none p false e.val.2 +
               triFac t none p true e.val.1 * triFac t none p true e.val.2)) * R := by rw [hcoeff]
        _ = _ := by ring
  refine ⟨?_, hmul⟩
  dsimp only [answer452]
  generalize hraw : raw452 t g p = r at hmul ⊢
  rcases r with ⟨rv, hrv⟩
  interval_cases rv
  · change (if obs452 t g p = obs452 t none p then (0 : Fin 3) else if obs452 t none p < obs452 t g p then 1 else 2) = 0
    have hmul' : 4 * obs452 t g p = 4 * obs452 t none p := by
      simpa [show (⟨0, hrv⟩ : Fin 3) = 0 from rfl] using hmul
    have heq : obs452 t g p = obs452 t none p := by omega
    rw [if_pos heq]
  · change (if obs452 t g p = obs452 t none p then (0 : Fin 3) else if obs452 t none p < obs452 t g p then 1 else 2) = 1
    have hmul' : 4 * obs452 t g p = 5 * obs452 t none p := by
      simpa [show (⟨1, hrv⟩ : Fin 3) = 1 from rfl] using hmul
    have hgt : obs452 t none p < obs452 t g p := by omega
    rw [if_neg (ne_of_gt hgt), if_pos hgt]
  · change (if obs452 t g p = obs452 t none p then (0 : Fin 3) else if obs452 t none p < obs452 t g p then 1 else 2) = 2
    have hmul' : 4 * obs452 t g p = 3 * obs452 t none p := by
      simpa [show (⟨2, hrv⟩ : Fin 3) = 2 from rfl] using hmul
    have hlt : obs452 t g p < obs452 t none p := by omega
    rw [if_neg (ne_of_lt hlt), if_neg (not_lt_of_gt hlt)]

private def ball452 (r j : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (j + 1), 2 ^ k * r.choose k

private def ballPrev452 (r b : ℕ) : ℕ :=
  if b = 0 then 0 else ball452 r (b - 1)

private lemma ball452_zero (r : ℕ) : ball452 r 0 = 1 := by
  simp [ball452]

private lemma ball452_zero_dim (j : ℕ) : ball452 0 j = 1 := by
  dsimp only [ball452]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    rcases k with _ | k'
    · exact (hk rfl).elim
    · simp [Nat.choose_zero_succ]
  · intro h; exact (h (Finset.mem_range.mpr (by omega))).elim

private lemma ball452_eq_prev_add (r b : ℕ) :
    ball452 r b = ballPrev452 r b + 2 ^ b * r.choose b := by
  cases b with
  | zero => simp [ball452, ballPrev452]
  | succ b' =>
    dsimp only [ball452, ballPrev452]
    rw [if_neg (Nat.succ_ne_zero b'), Nat.succ_sub_one, Finset.sum_range_succ]

private lemma ball452_succ (r b : ℕ) :
    ball452 (r + 1) b = ball452 r b + 2 * ballPrev452 r b := by
  cases b with
  | zero => simp [ball452, ballPrev452]
  | succ b' =>
    dsimp only [ball452, ballPrev452]
    rw [if_neg (Nat.succ_ne_zero b'), Nat.succ_sub_one]
    conv_lhs => rw [Finset.sum_range_succ']
    conv_rhs => rw [Finset.sum_range_succ', Finset.mul_sum]
    simp only [pow_zero, Nat.choose_zero_right, mul_one]
    have hstep : ∑ k ∈ Finset.range (b' + 1), 2 ^ (k + 1) * (r + 1).choose (k + 1) =
        ∑ k ∈ Finset.range (b' + 1), 2 ^ (k + 1) * r.choose (k + 1) +
        ∑ k ∈ Finset.range (b' + 1), 2 * (2 ^ k * r.choose k) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Nat.choose_succ_succ, pow_succ']
      ring
    rw [hstep]; ring

private lemma card_hamming_ball_fin3 (d k : ℕ) :
    ((Finset.univ : Finset (Fin d → Fin 3)).filter
      (fun δ => (Finset.univ.filter (fun i : Fin d => δ i ≠ 0)).card ≤ k)).card = ball452 d k := by
  induction d generalizing k with
  | zero =>
    rw [ball452_zero_dim]
    have hall : (Finset.univ : Finset (Fin 0 → Fin 3)).filter
        (fun δ => (Finset.univ.filter (fun i : Fin 0 => δ i ≠ 0)).card ≤ k) = Finset.univ := by
      ext δ; simp
    rw [hall, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, pow_zero]
  | succ d ih =>
    let eS : (Fin 3 × (Fin d → Fin 3)) ≃ (Fin (d + 1) → Fin 3) :=
      { toFun := fun q => Fin.cons (α := fun _ => Fin 3) q.1 q.2
        invFun := fun δ => (δ 0, Fin.tail δ)
        left_inv := fun ⟨c, v⟩ => Prod.ext rfl (by funext i; rfl)
        right_inv := fun δ => by
          funext i
          refine Fin.cases rfl (fun j => rfl) i }
    have hwt : ∀ (c : Fin 3) (v : Fin d → Fin 3),
        (Finset.univ.filter (fun i : Fin (d + 1) => Fin.cons (α := fun _ => Fin 3) c v i ≠ 0)).card =
        (if c ≠ 0 then 1 else 0) + (Finset.univ.filter (fun i : Fin d => v i ≠ 0)).card := by
      intro c v
      rw [Finset.card_filter, Fin.sum_univ_succ, ← Finset.card_filter]
      rfl
    have hbij : ((Finset.univ : Finset (Fin (d + 1) → Fin 3)).filter
        (fun δ => (Finset.univ.filter (fun i : Fin (d + 1) => δ i ≠ 0)).card ≤ k)).card =
        ((Finset.univ : Finset (Fin 3 × (Fin d → Fin 3))).filter
          (fun q => (if q.1 ≠ 0 then 1 else 0) + (Finset.univ.filter (fun i : Fin d => q.2 i ≠ 0)).card ≤ k)).card := by
      refine Finset.card_bij (fun δ _ => eS.symm δ) ?_ ?_ ?_
      · intro δ hδ
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        have h1 := (Finset.mem_filter.mp hδ).2
        have heq : eS (eS.symm δ) = δ := eS.apply_symm_apply δ
        rw [← heq] at h1
        exact (hwt (eS.symm δ).1 (eS.symm δ).2) ▸ h1
      · intro _ _ _ _ h; exact eS.symm.injective h
      · intro q hq
        refine ⟨eS q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, eS.symm_apply_apply q⟩
        dsimp only [eS, Equiv.coe_fn_mk]
        rw [hwt q.1 q.2]
        exact (Finset.mem_filter.mp hq).2
    rw [hbij, Finset.card_filter, Fintype.sum_prod_type, Fin.sum_univ_three]
    have h0 : ∑ v : Fin d → Fin 3,
        (if (if (0 : Fin 3) ≠ 0 then 1 else 0) + (Finset.univ.filter (fun i : Fin d => v i ≠ 0)).card ≤ k then 1 else 0) =
        ball452 d k := by
      simp only [ne_eq, not_true_eq_false, ↓reduceIte, zero_add, ← Finset.card_filter]
      exact ih k
    have hnz : ∀ c : Fin 3, c ≠ 0 →
        ∑ v : Fin d → Fin 3,
          (if (if c ≠ 0 then 1 else 0) + (Finset.univ.filter (fun i : Fin d => v i ≠ 0)).card ≤ k then 1 else 0) =
        ballPrev452 d k := by
      intro c hc
      simp only [if_pos hc]
      cases k with
      | zero =>
        simp [ballPrev452]
      | succ k' =>
        have hrew : ∀ v : Fin d → Fin 3,
            (if 1 + (Finset.univ.filter (fun i : Fin d => v i ≠ 0)).card ≤ k' + 1 then 1 else 0) =
            (if (Finset.univ.filter (fun i : Fin d => v i ≠ 0)).card ≤ k' then 1 else 0) := by
          intro v; by_cases h : (Finset.univ.filter (fun i : Fin d => v i ≠ 0)).card ≤ k'
          · rw [if_pos (by omega), if_pos h]
          · rw [if_neg (by omega), if_neg h]
        rw [Finset.sum_congr rfl fun v _ => hrew v, ← Finset.card_filter, ih k']
        simp [ballPrev452]
    rw [h0, hnz 1 (by decide), hnz 2 (by decide), ball452_succ]
    ring

private lemma card_transcript_ball {M : Type*} (d k : ℕ)
    (ask : (i : Fin d) → (Fin i.val → Fin 3) → M) (ans : M → Fin 3) :
    ((Finset.univ : Finset (Fin d → Fin 3)).filter
      (fun τ => (Finset.univ.filter (fun i : Fin d =>
        τ i ≠ ans (ask i (fun j => τ (j.castLE (Nat.le_of_lt i.isLt)))))).card ≤ k)).card = ball452 d k := by
  let fwd : (Fin d → Fin 3) → (Fin d → Fin 3) := fun τ i =>
    τ i - ans (ask i (fun j => τ (j.castLE (Nat.le_of_lt i.isLt))))
  have hinj : Function.Injective fwd := by
    intro τ1 τ2 heq
    have hstep : ∀ m (hm : m < d), τ1 ⟨m, hm⟩ = τ2 ⟨m, hm⟩ := by
      intro m
      induction m using Nat.strong_induction_on with
      | ind m ih =>
        intro hm
        have hpref : (fun j : Fin m => τ1 (j.castLE (Nat.le_of_lt hm))) =
            (fun j : Fin m => τ2 (j.castLE (Nat.le_of_lt hm))) := by
          funext j; exact ih j.val j.isLt (Nat.lt_trans j.isLt hm)
        have hfi : fwd τ1 ⟨m, hm⟩ = fwd τ2 ⟨m, hm⟩ := congrFun heq ⟨m, hm⟩
        dsimp only [fwd] at hfi
        rw [hpref] at hfi
        exact sub_left_injective hfi
    funext i; exact hstep i.val i.isLt
  let eF : (Fin d → Fin 3) ≃ (Fin d → Fin 3) :=
    Equiv.ofBijective fwd (Finite.injective_iff_bijective.mp hinj)
  have hiff : ∀ (τ : Fin d → Fin 3) (i : Fin d),
      τ i ≠ ans (ask i (fun j => τ (j.castLE (Nat.le_of_lt i.isLt)))) ↔ fwd τ i ≠ 0 := by
    intro τ i
    dsimp only [fwd]
    exact sub_ne_zero.symm
  rw [← card_hamming_ball_fin3 d k]
  refine Finset.card_bij (fun τ _ => eF τ) ?_ ?_ ?_
  · intro τ hτ
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have h1 := (Finset.mem_filter.mp hτ).2
    have hfeq : Finset.univ.filter (fun i : Fin d => eF τ i ≠ 0) =
        Finset.univ.filter (fun i : Fin d => τ i ≠ ans (ask i (fun j => τ (j.castLE (Nat.le_of_lt i.isLt))))) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hiff τ i).symm
    rwa [hfeq]
  · intro _ _ _ _ h; exact eF.injective h
  · intro δ hδ
    refine ⟨eF.symm δ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, eF.apply_symm_apply δ⟩
    have h1 := (Finset.mem_filter.mp hδ).2
    have hfeq : Finset.univ.filter (fun i : Fin d =>
        eF.symm δ i ≠ ans (ask i (fun j => eF.symm δ (j.castLE (Nat.le_of_lt i.isLt))))) =
        Finset.univ.filter (fun i : Fin d => δ i ≠ 0) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hiff (eF.symm δ) i]
      have : fwd (eF.symm δ) i = δ i := congrFun (eF.apply_symm_apply δ) i
      rw [this]
    rwa [hfeq]

private lemma weighted_cut_split (t : ℕ) (S : Finset (Fin t)) (M : ℝ) (hM : 0 ≤ M)
    (w : {p : Fin t × Fin t // p.1 < p.2} → ℝ) (hw : ∀ e, 0 ≤ w e ∧ w e ≤ M) :
    let ES := (Finset.univ : Finset {p : Fin t × Fin t // p.1 < p.2}).filter (fun e => e.val.1 ∈ S ∧ e.val.2 ∈ S)
    let WS := ∑ e ∈ ES, w e
    ∃ σ : Fin t → Bool,
      (∑ e ∈ ES, (if σ e.val.1 = σ e.val.2 then (1 : ℝ) else -1) * w e) ^ 2 ≤ M * WS := by
  intro ES WS
  let sgn : (Fin t → Bool) → {p : Fin t × Fin t // p.1 < p.2} → ℝ := fun σ e =>
    if σ e.val.1 = σ e.val.2 then 1 else -1
  have hsum_sq : ∑ σ : Fin t → Bool, (∑ e ∈ ES, sgn σ e * w e) ^ 2 =
      ((2 ^ t : ℕ) : ℝ) * ∑ e ∈ ES, (w e) ^ 2 := by
    have hexp : ∀ σ : Fin t → Bool, (∑ e ∈ ES, sgn σ e * w e) ^ 2 =
        ∑ e1 ∈ ES, ∑ e2 ∈ ES, (w e1 * w e2) * (sgn σ e1 * sgn σ e2) := by
      intro σ
      rw [sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun e1 _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e2 _ => by ring
    rw [Finset.sum_congr rfl fun σ _ => hexp σ, Finset.sum_comm]
    have hswap : ∀ e1 ∈ ES, ∑ σ : Fin t → Bool, ∑ e2 ∈ ES, (w e1 * w e2) * (sgn σ e1 * sgn σ e2) =
        ∑ e2 ∈ ES, (w e1 * w e2) * ∑ σ : Fin t → Bool, sgn σ e1 * sgn σ e2 := by
      intro e1 _
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun e2 _ => (Finset.mul_sum _ _ _).symm
    rw [Finset.sum_congr rfl hswap, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e1 he1 => ?_
    rw [Finset.sum_eq_single e1]
    · have h1 : ∀ σ : Fin t → Bool, sgn σ e1 * sgn σ e1 = 1 := fun σ => by
        dsimp only [sgn]; split_ifs <;> norm_num
      rw [Finset.sum_congr rfl fun σ _ => h1 σ, Finset.sum_const, Finset.card_univ,
        Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, mul_one, sq]
      ring
    · intro e2 _ hne
      have hxor : ∃ v0 : Fin t, ((v0 = e1.val.1 ∨ v0 = e1.val.2) ∧ v0 ≠ e2.val.1 ∧ v0 ≠ e2.val.2) ∨
          ((v0 = e2.val.1 ∨ v0 = e2.val.2) ∧ v0 ≠ e1.val.1 ∧ v0 ≠ e1.val.2) := by
        by_contra hall
        push_neg at hall
        have h1 : e1.val.1 = e2.val.1 ∨ e1.val.1 = e2.val.2 := by
          by_contra hnot; push_neg at hnot; exact hnot.2 ((hall e1.val.1).1 (Or.inl rfl) hnot.1)
        have h2 : e1.val.2 = e2.val.1 ∨ e1.val.2 = e2.val.2 := by
          by_contra hnot; push_neg at hnot; exact hnot.2 ((hall e1.val.2).1 (Or.inr rfl) hnot.1)
        have hlt1 := e1.2
        have hlt2 := e2.2
        have heq : e1 = e2 := Subtype.ext (Prod.ext (by omega) (by omega))
        exact hne heq.symm
      rcases hxor with ⟨v0, hv0⟩
      let flip : (Fin t → Bool) ≃ (Fin t → Bool) :=
        { toFun := fun σ => Function.update σ v0 (!σ v0)
          invFun := fun σ => Function.update σ v0 (!σ v0)
          left_inv := fun σ => by funext i; by_cases hi : i = v0 <;> simp [hi]
          right_inv := fun σ => by funext i; by_cases hi : i = v0 <;> simp [hi] }
      have hneg : ∀ σ : Fin t → Bool, sgn (flip σ) e1 * sgn (flip σ) e2 = -(sgn σ e1 * sgn σ e2) := by
        intro σ
        have hflip_one : ∀ (e : {p : Fin t × Fin t // p.1 < p.2}),
            (v0 = e.val.1 ∨ v0 = e.val.2) → sgn (flip σ) e = -sgn σ e := by
          intro e hv
          have hne_e : e.val.1 ≠ e.val.2 := ne_of_lt e.2
          dsimp only [sgn, flip, Equiv.coe_fn_mk]
          rcases hv with rfl | rfl
          · rw [Function.update_self, Function.update_of_ne hne_e.symm]
            cases (σ e.val.1) <;> cases (σ e.val.2) <;> norm_num
          · rw [Function.update_of_ne hne_e, Function.update_self]
            cases (σ e.val.1) <;> cases (σ e.val.2) <;> norm_num
        have hfix_one : ∀ (e : {p : Fin t × Fin t // p.1 < p.2}),
            v0 ≠ e.val.1 → v0 ≠ e.val.2 → sgn (flip σ) e = sgn σ e := by
          intro e h1 h2
          dsimp only [sgn, flip, Equiv.coe_fn_mk]
          rw [Function.update_of_ne h1.symm, Function.update_of_ne h2.symm]
        rcases hv0 with ⟨h1, h2a, h2b⟩ | ⟨h2, h1a, h1b⟩
        · rw [hflip_one e1 h1, hfix_one e2 h2a h2b]; ring
        · rw [hfix_one e1 h1a h1b, hflip_one e2 h2]; ring
      have hzero : ∑ σ : Fin t → Bool, sgn σ e1 * sgn σ e2 = 0 := by
        have hs1 : ∑ σ : Fin t → Bool, sgn σ e1 * sgn σ e2 =
            ∑ σ : Fin t → Bool, sgn (flip σ) e1 * sgn (flip σ) e2 :=
          (Fintype.sum_equiv flip (fun σ => sgn (flip σ) e1 * sgn (flip σ) e2)
            (fun σ => sgn σ e1 * sgn σ e2) fun _ => rfl).symm
        have hs2 : ∑ σ : Fin t → Bool, sgn (flip σ) e1 * sgn (flip σ) e2 =
            -(∑ σ : Fin t → Bool, sgn σ e1 * sgn σ e2) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun σ _ => hneg σ
        linarith
      rw [hzero, mul_zero]
    · intro hm; exact (hm he1).elim
  have hsum_le : ∑ e ∈ ES, (w e) ^ 2 ≤ M * WS := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun e _ => ?_
    rw [sq]; exact mul_le_mul_of_nonneg_right (hw e).2 (hw e).1
  by_contra hnone
  push_neg at hnone
  have hlt : ((2 ^ t : ℕ) : ℝ) * (M * WS) < ∑ σ : Fin t → Bool, (∑ e ∈ ES, sgn σ e * w e) ^ 2 := by
    have hconst : ((2 ^ t : ℕ) : ℝ) * (M * WS) = ∑ _σ : Fin t → Bool, (M * WS) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
    rw [hconst]
    exact Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty) fun σ _ => hnone σ
  have hle : ∑ σ : Fin t → Bool, (∑ e ∈ ES, sgn σ e * w e) ^ 2 ≤ ((2 ^ t : ℕ) : ℝ) * (M * WS) := by
    rw [hsum_sq]; exact mul_le_mul_of_nonneg_left hsum_le (by positivity)
  linarith

private lemma weighted_graph_split (t : ℕ) (M : ℝ) (hM : 0 < M)
    (w : Option {p : Fin t × Fin t // p.1 < p.2} → ℝ) (hw : ∀ g, 0 ≤ w g ∧ w g ≤ M) :
    let W := ∑ g : Option {p : Fin t × Fin t // p.1 < p.2}, w g
    ∃ p : Fin t → Fin 3, ∀ c : Fin 3,
      ∑ g ∈ Finset.univ.filter (fun g => raw452 t g p = c), w g ≤
        W / 3 + Real.sqrt (2 * W * M) + 3 * M := by
  intro W
  have hW_nn : 0 ≤ W := Finset.sum_nonneg fun g _ => (hw g).1
  let W0 : Finset (Fin t) → ℝ := fun Z =>
    w none + ∑ e : {p : Fin t × Fin t // p.1 < p.2},
      if e.val.1 ∈ Z ∨ e.val.2 ∈ Z then w (some e) else 0
  let WS : Finset (Fin t) → ℝ := fun Z =>
    ∑ e ∈ Finset.univ.filter (fun e : {p : Fin t × Fin t // p.1 < p.2} => e.val.1 ∉ Z ∧ e.val.2 ∉ Z), w (some e)
  have hW_decomp : ∀ Z : Finset (Fin t), W0 Z + WS Z = W := by
    intro Z
    dsimp only [W0, WS, W]
    rw [Fintype.sum_option, add_assoc]
    congr 1
    have h1 : ∑ e : {p : Fin t × Fin t // p.1 < p.2}, (if e.val.1 ∈ Z ∨ e.val.2 ∈ Z then w (some e) else 0) =
        ∑ e ∈ Finset.univ.filter (fun e : {p : Fin t × Fin t // p.1 < p.2} => e.val.1 ∈ Z ∨ e.val.2 ∈ Z), w (some e) :=
      (Finset.sum_filter _ _).symm
    have h2 : ∑ e ∈ Finset.univ.filter (fun e : {p : Fin t × Fin t // p.1 < p.2} => e.val.1 ∉ Z ∧ e.val.2 ∉ Z), w (some e) =
        ∑ e ∈ Finset.univ.filter (fun e : {p : Fin t × Fin t // p.1 < p.2} => ¬ (e.val.1 ∈ Z ∨ e.val.2 ∈ Z)), w (some e) := by
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext e; simp [not_or]
    rw [h1, h2, Finset.sum_filter_add_sum_filter_not]
  have hfinish : ∀ Z : Finset (Fin t),
      W0 Z ≤ W / 3 + Real.sqrt (2 * W * M) + 3 * M →
      WS Z ≤ 2 * W / 3 →
      ∃ p : Fin t → Fin 3, ∀ c : Fin 3,
        ∑ g ∈ Finset.univ.filter (fun g => raw452 t g p = c), w g ≤
          W / 3 + Real.sqrt (2 * W * M) + 3 * M := by
    intro Z hZ0 hZS
    let S := Finset.univ \ Z
    have hWS_eq : WS Z = ∑ e ∈ Finset.univ.filter (fun e : {p : Fin t × Fin t // p.1 < p.2} => e.val.1 ∈ S ∧ e.val.2 ∈ S),
        w (some e) := by
      dsimp only [WS, S]; refine Finset.sum_congr ?_ fun _ _ => rfl
      ext e; simp
    rcases weighted_cut_split t S M (le_of_lt hM) (fun e => w (some e)) (fun e => hw (some e)) with ⟨σ, hσ⟩
    let p : Fin t → Fin 3 := fun i => if i ∈ Z then 0 else if σ i then 1 else 2
    refine ⟨p, fun c => ?_⟩
    let E1 := Finset.univ.filter (fun e : {p : Fin t × Fin t // p.1 < p.2} => e.val.1 ∈ S ∧ e.val.2 ∈ S ∧ σ e.val.1 = σ e.val.2)
    let E2 := Finset.univ.filter (fun e : {p : Fin t × Fin t // p.1 < p.2} => e.val.1 ∈ S ∧ e.val.2 ∈ S ∧ σ e.val.1 ≠ σ e.val.2)
    let W1 := ∑ e ∈ E1, w (some e)
    let W2 := ∑ e ∈ E2, w (some e)
    have h12_sum : W1 + W2 = WS Z := by
      rw [hWS_eq]
      dsimp only [W1, W2, E1, E2]
      rw [← Finset.sum_union]
      · refine Finset.sum_congr ?_ fun _ _ => rfl
        ext e; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        tauto
      · rw [Finset.disjoint_left]; intro e h1 h2
        exact (Finset.mem_filter.mp h2).2.2.2 (Finset.mem_filter.mp h1).2.2.2
    have h12_diff : W1 - W2 = ∑ e ∈ Finset.univ.filter (fun e : {p : Fin t × Fin t // p.1 < p.2} => e.val.1 ∈ S ∧ e.val.2 ∈ S),
        (if σ e.val.1 = σ e.val.2 then (1 : ℝ) else -1) * w (some e) := by
      dsimp only [W1, W2, E1, E2]
      rw [← Finset.sum_filter_add_sum_filter_not
        (Finset.univ.filter (fun e : {p : Fin t × Fin t // p.1 < p.2} => e.val.1 ∈ S ∧ e.val.2 ∈ S))
        (fun e => σ e.val.1 = σ e.val.2)]
      have hf1 : (Finset.univ.filter (fun e : {p : Fin t × Fin t // p.1 < p.2} => e.val.1 ∈ S ∧ e.val.2 ∈ S)).filter
          (fun e => σ e.val.1 = σ e.val.2) = E1 := by
        ext e; simp [E1, and_assoc]
      have hf2 : (Finset.univ.filter (fun e : {p : Fin t × Fin t // p.1 < p.2} => e.val.1 ∈ S ∧ e.val.2 ∈ S)).filter
          (fun e => ¬ σ e.val.1 = σ e.val.2) = E2 := by
        ext e; simp [E2, and_assoc]
      rw [hf1, hf2]
      have hs1 : ∑ e ∈ E1, (if σ e.val.1 = σ e.val.2 then (1 : ℝ) else -1) * w (some e) = ∑ e ∈ E1, w (some e) :=
        Finset.sum_congr rfl fun e he => by rw [if_pos (Finset.mem_filter.mp he).2.2.2, one_mul]
      have hs2 : ∑ e ∈ E2, (if σ e.val.1 = σ e.val.2 then (1 : ℝ) else -1) * w (some e) = -(∑ e ∈ E2, w (some e)) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun e he => by rw [if_neg (Finset.mem_filter.mp he).2.2.2]; ring
      rw [hs1, hs2]; ring
    have hdiff_le : |W1 - W2| ≤ Real.sqrt (2 * W * M) := by
      rw [← Real.sqrt_sq_eq_abs]
      refine Real.sqrt_le_sqrt ?_
      rw [h12_diff]
      have h1 : M * ∑ e ∈ Finset.univ.filter (fun e : {p : Fin t × Fin t // p.1 < p.2} => e.val.1 ∈ S ∧ e.val.2 ∈ S), w (some e) ≤
          2 * W * M := by
        rw [← hWS_eq]
        have hWS_nn : 0 ≤ WS Z := Finset.sum_nonneg fun e _ => (hw (some e)).1
        nlinarith
      exact hσ.trans h1
    have hW1_le : W1 ≤ W / 3 + Real.sqrt (2 * W * M) + 3 * M := by
      have := (abs_le.mp hdiff_le).2
      have hsq_nn : 0 ≤ Real.sqrt (2 * W * M) := Real.sqrt_nonneg _
      linarith
    have hW2_le : W2 ≤ W / 3 + Real.sqrt (2 * W * M) + 3 * M := by
      have := (abs_le.mp hdiff_le).1
      have hsq_nn : 0 ≤ Real.sqrt (2 * W * M) := Real.sqrt_nonneg _
      linarith
    have hraw_p : ∀ e : {p : Fin t × Fin t // p.1 < p.2},
        (raw452 t (some e) p = 0 ↔ e.val.1 ∈ Z ∨ e.val.2 ∈ Z) ∧
        (raw452 t (some e) p = 1 ↔ e.val.1 ∈ S ∧ e.val.2 ∈ S ∧ σ e.val.1 = σ e.val.2) ∧
        (raw452 t (some e) p = 2 ↔ e.val.1 ∈ S ∧ e.val.2 ∈ S ∧ σ e.val.1 ≠ σ e.val.2) := by
      intro e
      dsimp only [raw452, Option.elim, p, S]
      by_cases h1 : e.val.1 ∈ Z <;> by_cases h2 : e.val.2 ∈ Z <;>
        rcases Bool.eq_false_or_eq_true (σ e.val.1) with hσ1 | hσ1 <;>
        rcases Bool.eq_false_or_eq_true (σ e.val.2) with hσ2 | hσ2 <;>
        simp [h1, h2, hσ1, hσ2]
    rcases c with ⟨cv, hcv⟩
    interval_cases cv
    · change ∑ g ∈ Finset.univ.filter (fun g => raw452 t g p = (0 : Fin 3)), w g ≤ W / 3 + Real.sqrt (2 * W * M) + 3 * M
      have hsum0 : ∑ g ∈ Finset.univ.filter (fun g => raw452 t g p = (0 : Fin 3)), w g = W0 Z := by
        rw [Finset.sum_filter, Fintype.sum_option]
        dsimp only [W0]
        rw [show raw452 t none p = 0 from rfl, if_pos rfl]
        congr 1
        refine Finset.sum_congr rfl fun e _ => by simp [(hraw_p e).1]
      rw [hsum0]; exact hZ0
    · change ∑ g ∈ Finset.univ.filter (fun g => raw452 t g p = (1 : Fin 3)), w g ≤ W / 3 + Real.sqrt (2 * W * M) + 3 * M
      have hsum1 : ∑ g ∈ Finset.univ.filter (fun g => raw452 t g p = (1 : Fin 3)), w g = W1 := by
        rw [Finset.sum_filter, Fintype.sum_option]
        rw [show raw452 t none p = 0 from rfl, if_neg (by decide), zero_add]
        dsimp only [W1, E1]
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun e _ => by simp [(hraw_p e).2.1]
      rw [hsum1]; exact hW1_le
    · change ∑ g ∈ Finset.univ.filter (fun g => raw452 t g p = (2 : Fin 3)), w g ≤ W / 3 + Real.sqrt (2 * W * M) + 3 * M
      have hsum2 : ∑ g ∈ Finset.univ.filter (fun g => raw452 t g p = (2 : Fin 3)), w g = W2 := by
        rw [Finset.sum_filter, Fintype.sum_option]
        rw [show raw452 t none p = 0 from rfl, if_neg (by decide), zero_add]
        dsimp only [W2, E2]
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun e _ => by simp [(hraw_p e).2.2]
      rw [hsum2]; exact hW2_le
  by_cases hbig0 : W / 3 ≤ w none
  · have hW0_emp : W0 ∅ = w none := by simp [W0]
    have hWS_emp : WS ∅ ≤ 2 * W / 3 := by
      have := hW_decomp ∅; rw [hW0_emp] at this; linarith
    exact hfinish ∅ (by
      rw [hW0_emp]
      have hsq_nn : 0 ≤ Real.sqrt (2 * W * M) := Real.sqrt_nonneg _
      have := (hw none).2
      linarith) hWS_emp
  · push_neg at hbig0
    have hW_pos : 0 < W := by have := (hw none).1; linarith
    let cand : Finset (Finset (Fin t)) := Finset.univ.filter (fun Z => W0 Z < W / 3)
    have hemp_mem : (∅ : Finset (Fin t)) ∈ cand := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      simpa [W0] using hbig0
    rcases Finset.exists_max_image cand Finset.card ⟨∅, hemp_mem⟩ with ⟨Z, hZ_mem, hZ_max⟩
    have hZ_lt : W0 Z < W / 3 := (Finset.mem_filter.mp hZ_mem).2
    let S := Finset.univ \ Z
    let D := Real.sqrt (2 * W * M)
    have hD_sq : D ^ 2 = 2 * W * M := Real.sq_sqrt (by positivity)
    have hD_pos : 0 < D := Real.sqrt_pos.mpr (by positivity)
    let degS : Fin t → ℝ := fun v =>
      ∑ e ∈ Finset.univ.filter (fun e : {p : Fin t × Fin t // p.1 < p.2} =>
        e.val.1 ∉ Z ∧ e.val.2 ∉ Z ∧ (e.val.1 = v ∨ e.val.2 = v)), w (some e)
    have hstep_W0 : ∀ v ∈ S, W0 (insert v Z) = W0 Z + degS v := by
      intro v hv
      have hv_notZ : v ∉ Z := (Finset.mem_sdiff.mp hv).2
      dsimp only [W0, degS]
      rw [add_assoc]
      congr 1
      rw [Finset.sum_filter, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      by_cases h1 : e.val.1 ∈ Z <;> by_cases h2 : e.val.2 ∈ Z <;>
        by_cases hv1 : e.val.1 = v <;> by_cases hv2 : e.val.2 = v <;>
        simp [h1, h2, hv1, hv2, hv_notZ]
    have hex_light : ∃ v ∈ S, degS v ≤ D := by
      by_contra hall
      push_neg at hall
      have hWS_pos : 0 < WS Z := by have := hW_decomp Z; linarith
      have hS_ne : S.Nonempty := by
        by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        have hWS0 : WS Z = 0 := by
          refine Finset.sum_eq_zero fun e he => ?_
          have h1 : e.val.1 ∈ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).2.1⟩
          rw [hemp] at h1; exact (Finset.notMem_empty _ h1).elim
        linarith
      have hhandshake : ∑ v ∈ S, degS v = 2 * WS Z := by
        dsimp only [degS, WS]
        simp_rw [Finset.sum_filter]
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        by_cases h1 : e.val.1 ∉ Z ∧ e.val.2 ∉ Z
        · rw [if_pos h1]
          have hne_e : e.val.1 ≠ e.val.2 := ne_of_lt e.2
          have hm1 : e.val.1 ∈ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h1.1⟩
          have hm2 : e.val.2 ∈ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h1.2⟩
          have hs : ∑ v ∈ S, (if e.val.1 ∉ Z ∧ e.val.2 ∉ Z ∧ (e.val.1 = v ∨ e.val.2 = v) then w (some e) else 0) =
              ∑ v ∈ ({e.val.1, e.val.2} : Finset (Fin t)), w (some e) := by
            rw [← Finset.sum_filter]
            have hf : S.filter (fun v => e.val.1 ∉ Z ∧ e.val.2 ∉ Z ∧ (e.val.1 = v ∨ e.val.2 = v)) = {e.val.1, e.val.2} := by
              ext v; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
              constructor
              · rintro ⟨_, _, _, rfl | rfl⟩ <;> simp
              · rintro (rfl | rfl)
                · exact ⟨hm1, h1.1, h1.2, Or.inl rfl⟩
                · exact ⟨hm2, h1.1, h1.2, Or.inr rfl⟩
            rw [hf]
          rw [hs, Finset.sum_pair hne_e]; ring
        · rw [if_neg h1, mul_zero]
          refine Finset.sum_eq_zero fun v _ => if_neg fun h => h1 ⟨h.1, h.2.1⟩
      have hlb : (S.card : ℝ) * D < 2 * WS Z := by
        rw [← hhandshake, ← nsmul_eq_mul, ← Finset.sum_const]
        exact Finset.sum_lt_sum_of_nonempty hS_ne hall
      have hub : 2 * WS Z ≤ (S.card : ℝ) * (S.card : ℝ) * M := by
        have hdeg_le : ∀ v ∈ S, degS v ≤ (S.card : ℝ) * M := by
          intro v _
          dsimp only [degS]
          have hsum_le : ∑ e ∈ Finset.univ.filter (fun e : {p : Fin t × Fin t // p.1 < p.2} =>
                e.val.1 ∉ Z ∧ e.val.2 ∉ Z ∧ (e.val.1 = v ∨ e.val.2 = v)), w (some e) ≤
              ((Finset.univ.filter (fun e : {p : Fin t × Fin t // p.1 < p.2} =>
                e.val.1 ∉ Z ∧ e.val.2 ∉ Z ∧ (e.val.1 = v ∨ e.val.2 = v))).card : ℝ) * M := by
            calc _ ≤ ∑ _e ∈ _, M := Finset.sum_le_sum fun e _ => (hw (some e)).2
              _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
          refine hsum_le.trans (mul_le_mul_of_nonneg_right ?_ (le_of_lt hM))
          have hcard_le : (Finset.univ.filter (fun e : {p : Fin t × Fin t // p.1 < p.2} =>
              e.val.1 ∉ Z ∧ e.val.2 ∉ Z ∧ (e.val.1 = v ∨ e.val.2 = v))).card ≤ S.card := by
            refine Finset.card_le_card_of_injOn (fun e => if e.val.1 = v then e.val.2 else e.val.1) ?_ ?_
            · intro e he
              have hm := (Finset.mem_filter.mp he).2
              dsimp only
              split_ifs
              · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hm.2.1⟩
              · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hm.1⟩
            · intro e1 he1 e2 he2 heq
              have hm1 := (Finset.mem_filter.mp he1).2.2.2
              have hm2 := (Finset.mem_filter.mp he2).2.2.2
              have hlt1 := e1.2
              have hlt2 := e2.2
              dsimp only at heq
              split_ifs at heq with h1 h2 h2
              · exact Subtype.ext (Prod.ext (h1.trans h2.symm) heq)
              · have : e2.val.2 = v := hm2.resolve_left h2
                omega
              · have : e1.val.2 = v := hm1.resolve_left h1
                omega
              · have h1' : e1.val.2 = v := hm1.resolve_left h1
                have h2' : e2.val.2 = v := hm2.resolve_left h2
                exact Subtype.ext (Prod.ext heq (h1'.trans h2'.symm))
          exact_mod_cast hcard_le
        rw [← hhandshake]
        calc ∑ v ∈ S, degS v ≤ ∑ _v ∈ S, ((S.card : ℝ) * M) := Finset.sum_le_sum hdeg_le
          _ = (S.card : ℝ) * (S.card : ℝ) * M := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      have hSc_pos : (0 : ℝ) < S.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hS_ne)
      have hsq_lt : ((S.card : ℝ) * D) ^ 2 < (2 * WS Z) ^ 2 := by nlinarith [mul_pos hSc_pos hD_pos]
      have hWS_le_W : WS Z ≤ W := by
        have hW0_nn : 0 ≤ W0 Z := add_nonneg (hw none).1 (Finset.sum_nonneg fun e _ => by split_ifs; exact (hw (some e)).1; exact le_rfl)
        linarith [hW_decomp Z]
      have hcontra : (S.card : ℝ) ^ 2 * D ^ 2 < (S.card : ℝ) ^ 2 * (2 * W * M) := by
        calc (S.card : ℝ) ^ 2 * D ^ 2 = ((S.card : ℝ) * D) ^ 2 := by ring
          _ < (2 * WS Z) ^ 2 := hsq_lt
          _ = (2 * WS Z) * (2 * WS Z) := by ring
          _ ≤ (2 * WS Z) * ((S.card : ℝ) * (S.card : ℝ) * M) := mul_le_mul_of_nonneg_left hub (by linarith)
          _ = (S.card : ℝ) ^ 2 * (2 * WS Z * M) := by ring
          _ ≤ (S.card : ℝ) ^ 2 * (2 * W * M) := by
              refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
              nlinarith
      rw [hD_sq] at hcontra
      linarith
    rcases hex_light with ⟨v0, hv0_S, hv0_deg⟩
    have hv0_notZ : v0 ∉ Z := (Finset.mem_sdiff.mp hv0_S).2
    let Z' := insert v0 Z
    have hZ'_ge : W / 3 ≤ W0 Z' := by
      by_contra hlt
      push_neg at hlt
      have hmem' : Z' ∈ cand := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
      have hle := hZ_max Z' hmem'
      have hcard' : Z'.card = Z.card + 1 := Finset.card_insert_of_notMem hv0_notZ
      omega
    have hZ'_le : W0 Z' ≤ W / 3 + D + 3 * M := by
      dsimp only [Z']
      rw [hstep_W0 v0 hv0_S]; linarith
    have hWS'_le : WS Z' ≤ 2 * W / 3 := by
      have := hW_decomp Z'; linarith
    exact hfinish Z' hZ'_le hWS'_le

private lemma sqrt_step_bound (V M : ℝ) (hV : 0 ≤ V) (hM : 0 ≤ M) :
    Real.sqrt (V / 3 + Real.sqrt (2 * V * M) + 3 * M) ≤ Real.sqrt V / Real.sqrt 3 + 2 * Real.sqrt M := by
  have h3_pos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hrhs_nn : 0 ≤ Real.sqrt V / Real.sqrt 3 + 2 * Real.sqrt M := by positivity
  rw [← Real.sqrt_sq hrhs_nn]
  refine Real.sqrt_le_sqrt ?_
  have hsq : (Real.sqrt V / Real.sqrt 3 + 2 * Real.sqrt M) ^ 2 =
      V / 3 + (4 / Real.sqrt 3) * Real.sqrt (V * M) + 4 * M := by
    have hsqV : Real.sqrt V ^ 2 = V := Real.sq_sqrt hV
    have hsqM : Real.sqrt M ^ 2 = M := Real.sq_sqrt hM
    have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hmulVM : Real.sqrt V * Real.sqrt M = Real.sqrt (V * M) := (Real.sqrt_mul hV M).symm
    calc (Real.sqrt V / Real.sqrt 3 + 2 * Real.sqrt M) ^ 2
        = Real.sqrt V ^ 2 / Real.sqrt 3 ^ 2 + (4 / Real.sqrt 3) * (Real.sqrt V * Real.sqrt M) + 4 * Real.sqrt M ^ 2 := by ring
      _ = V / 3 + (4 / Real.sqrt 3) * Real.sqrt (V * M) + 4 * M := by rw [hsqV, hsq3, hsqM, hmulVM]
  rw [hsq]
  have h2VM : Real.sqrt (2 * V * M) = Real.sqrt 2 * Real.sqrt (V * M) := by
    rw [mul_assoc, Real.sqrt_mul (by norm_num)]
  rw [h2VM]
  have hcoeff : Real.sqrt 2 ≤ 4 / Real.sqrt 3 := by
    rw [le_div_iff₀ h3_pos, ← Real.sqrt_mul (by norm_num)]
    have h1 : Real.sqrt (2 * 3) ≤ Real.sqrt 16 := Real.sqrt_le_sqrt (by norm_num)
    have h16 : Real.sqrt 16 = 4 := by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith
  have hVM_nn : 0 ≤ Real.sqrt (V * M) := Real.sqrt_nonneg _
  nlinarith

private lemma sqrt_pow_eq (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    Real.sqrt (x ^ n) = Real.sqrt x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, Real.sqrt_mul (pow_nonneg hx n), ih]

private lemma poly_le_exp_4_3 (E : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ k : ℕ, ((k + 1 : ℕ) : ℝ) ^ E ≤ A * (4 / 3 : ℝ) ^ k := by
  let A : ℝ := max (((2 * E + 1 : ℕ) : ℝ) ^ E) ((9 : ℝ) ^ E * (E.factorial : ℝ))
  have hA_pos : 0 < A := by
    refine lt_of_lt_of_le ?_ (le_max_left _ _)
    positivity
  refine ⟨A, hA_pos, fun k => ?_⟩
  by_cases hk : k ≤ 2 * E
  · have h1 : ((k + 1 : ℕ) : ℝ) ^ E ≤ ((2 * E + 1 : ℕ) : ℝ) ^ E :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast (show k + 1 ≤ 2 * E + 1 by omega)) E
    have h2 : (1 : ℝ) ≤ (4 / 3 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    have h3 : ((2 * E + 1 : ℕ) : ℝ) ^ E ≤ A := le_max_left _ _
    nlinarith
  · have hk_gt : 2 * E < k := by omega
    have hE_le : E ≤ k := by omega
    have hbinom : (k.choose E : ℝ) * (1 / 3 : ℝ) ^ E ≤ (4 / 3 : ℝ) ^ k := by
      have hpow : (4 / 3 : ℝ) ^ k = ((1 / 3 : ℝ) + 1) ^ k := by norm_num
      rw [hpow, add_pow]
      have hterm : (1 / 3 : ℝ) ^ E * (1 : ℝ) ^ (k - E) * (k.choose E : ℝ) ≤
          ∑ j ∈ Finset.range (k + 1), (1 / 3 : ℝ) ^ j * (1 : ℝ) ^ (k - j) * (k.choose j : ℝ) :=
        Finset.single_le_sum (f := fun j => (1 / 3 : ℝ) ^ j * (1 : ℝ) ^ (k - j) * (k.choose j : ℝ))
          (fun j _ => by positivity) (Finset.mem_range.mpr (by omega : E < k + 1))
      simp only [one_pow, mul_one] at hterm ⊢
      linarith
    have hdesc : (k + 1) ^ E ≤ 3 ^ E * (E.factorial * k.choose E) := by
      rw [← Nat.descFactorial_eq_factorial_mul_choose]
      have hprod : ∀ m : ℕ, m ≤ E → (k + 1) ^ m ≤ 3 ^ m * k.descFactorial m := by
        intro m hm
        induction m with
        | zero => simp
        | succ m' ihm =>
          rw [pow_succ, pow_succ, Nat.descFactorial_succ]
          have hstep : k + 1 ≤ 3 * (k - m') := by omega
          have hprev := ihm (by omega)
          calc (k + 1) ^ m' * (k + 1)
              ≤ (3 ^ m' * k.descFactorial m') * (3 * (k - m')) := Nat.mul_le_mul hprev hstep
            _ = 3 ^ m' * 3 * ((k - m') * k.descFactorial m') := by ring
      exact hprod E le_rfl
    have hdesc_r : ((k + 1 : ℕ) : ℝ) ^ E ≤ (3 : ℝ) ^ E * (E.factorial : ℝ) * (k.choose E : ℝ) := by
      have h1 : (((k + 1) ^ E : ℕ) : ℝ) ≤ ((3 ^ E * (E.factorial * k.choose E) : ℕ) : ℝ) := by
        exact_mod_cast hdesc
      simp only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] at h1
      linarith
    have hstep1 : ((k + 1 : ℕ) : ℝ) ^ E ≤ (9 : ℝ) ^ E * (E.factorial : ℝ) * (4 / 3 : ℝ) ^ k := by
      have h9 : (9 : ℝ) ^ E * (E.factorial : ℝ) * ((k.choose E : ℝ) * (1 / 3 : ℝ) ^ E) =
          (3 : ℝ) ^ E * (E.factorial : ℝ) * (k.choose E : ℝ) := by
        have h93 : (9 : ℝ) ^ E * (1 / 3 : ℝ) ^ E = (3 : ℝ) ^ E := by
          rw [← mul_pow]; norm_num
        calc (9 : ℝ) ^ E * (E.factorial : ℝ) * ((k.choose E : ℝ) * (1 / 3 : ℝ) ^ E)
            = ((9 : ℝ) ^ E * (1 / 3 : ℝ) ^ E) * (E.factorial : ℝ) * (k.choose E : ℝ) := by ring
          _ = (3 : ℝ) ^ E * (E.factorial : ℝ) * (k.choose E : ℝ) := by rw [h93]
      have hmul := mul_le_mul_of_nonneg_left hbinom (by positivity : (0 : ℝ) ≤ (9 : ℝ) ^ E * (E.factorial : ℝ))
      linarith
    have hA_ge : (9 : ℝ) ^ E * (E.factorial : ℝ) ≤ A := le_max_right _ _
    have hpow_nn : (0 : ℝ) ≤ (4 / 3 : ℝ) ^ k := by positivity
    nlinarith

private lemma ball452_le_poly (E r : ℕ) :
    (ball452 r E : ℝ) ≤ ((E + 1 : ℕ) : ℝ) * (2 : ℝ) ^ E * ((r + 1 : ℕ) : ℝ) ^ E := by
  dsimp only [ball452]
  push_cast
  calc ∑ k ∈ Finset.range (E + 1), (2 : ℝ) ^ k * (r.choose k : ℝ)
      ≤ ∑ _k ∈ Finset.range (E + 1), (2 : ℝ) ^ E * ((r + 1 : ℕ) : ℝ) ^ E := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hkE : k ≤ E := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have h2 : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ E := by
          exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ 2) hkE
        have hch : (r.choose k : ℝ) ≤ ((r + 1 : ℕ) : ℝ) ^ E := by
          have h1 : r.choose k ≤ r ^ k := by
            have hfac : 1 ≤ k.factorial := Nat.factorial_pos k
            have hle1 : r.choose k ≤ k.factorial * r.choose k := Nat.le_mul_of_pos_left _ hfac
            rw [← Nat.descFactorial_eq_factorial_mul_choose] at hle1
            exact hle1.trans (Nat.descFactorial_le_pow r k)
          have h2' : r ^ k ≤ (r + 1) ^ k := Nat.pow_le_pow_left (by omega) k
          have h3 : (r + 1) ^ k ≤ (r + 1) ^ E := Nat.pow_le_pow_right (by omega) hkE
          exact_mod_cast (h1.trans (h2'.trans h3))
        exact mul_le_mul h2 hch (by positivity) (by positivity)
    _ = ((E + 1 : ℕ) : ℝ) * (2 : ℝ) ^ E * ((r + 1 : ℕ) : ℝ) ^ E := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    _ = ((E : ℝ) + 1) * (2 : ℝ) ^ E * ((r : ℝ) + 1) ^ E := by push_cast; rfl

private lemma geom_sum_two_thirds (d : ℕ) :
    ∑ k ∈ Finset.range d, ((2 / 3 : ℝ) ^ k) ≤ 3 := by
  have heq : ∑ k ∈ Finset.range d, ((2 / 3 : ℝ) ^ k) = 3 - 3 * (2 / 3 : ℝ) ^ d := by
    induction d with
    | zero => simp
    | succ d ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring
  rw [heq]
  have : (0 : ℝ) ≤ (2 / 3 : ℝ) ^ d := by positivity
  linarith

private def distinguishMask452 (t : ℕ) (g1 g2 : Option {p : Fin t × Fin t // p.1 < p.2}) : Fin t → Fin 3 :=
  match g1, g2 with
  | some e, _ => fun i => if i = e.val.1 ∨ i = e.val.2 then 1 else 0
  | none, some e => fun i => if i = e.val.1 ∨ i = e.val.2 then 1 else 0
  | none, none => fun _ => 0

private lemma distinguishMask452_spec (t : ℕ) (g1 g2 : Option {p : Fin t × Fin t // p.1 < p.2})
    (hne : g1 ≠ g2) :
    raw452 t g1 (distinguishMask452 t g1 g2) ≠ raw452 t g2 (distinguishMask452 t g1 g2) := by
  rcases g1 with _ | e1 <;> rcases g2 with _ | e2
  · exact (hne rfl).elim
  · dsimp only [distinguishMask452, raw452, Option.elim]
    simp
  · dsimp only [distinguishMask452, raw452, Option.elim]
    simp
  · dsimp only [distinguishMask452, raw452, Option.elim]
    have h1 : (if (if e1.val.1 = e1.val.1 ∨ e1.val.1 = e1.val.2 then (1 : Fin 3) else 0) = 0 ∨
          (if e1.val.2 = e1.val.1 ∨ e1.val.2 = e1.val.2 then (1 : Fin 3) else 0) = 0 then (0 : Fin 3)
        else if (if e1.val.1 = e1.val.1 ∨ e1.val.1 = e1.val.2 then (1 : Fin 3) else 0) =
          (if e1.val.2 = e1.val.1 ∨ e1.val.2 = e1.val.2 then (1 : Fin 3) else 0) then 1 else 2) = 1 := by
      simp
    have hnot_both : ¬ ((e2.val.1 = e1.val.1 ∨ e2.val.1 = e1.val.2) ∧ (e2.val.2 = e1.val.1 ∨ e2.val.2 = e1.val.2)) := by
      rintro ⟨ha, hb⟩
      have hlt1 := e1.2
      have hlt2 := e2.2
      have heq : e1 = e2 := Subtype.ext (Prod.ext (by omega) (by omega))
      exact hne (congrArg some heq)
    have h2 : (if (if e2.val.1 = e1.val.1 ∨ e2.val.1 = e1.val.2 then (1 : Fin 3) else 0) = 0 ∨
          (if e2.val.2 = e1.val.1 ∨ e2.val.2 = e1.val.2 then (1 : Fin 3) else 0) = 0 then (0 : Fin 3)
        else if (if e2.val.1 = e1.val.1 ∨ e2.val.1 = e1.val.2 then (1 : Fin 3) else 0) =
          (if e2.val.2 = e1.val.1 ∨ e2.val.2 = e1.val.2 then (1 : Fin 3) else 0) then 1 else 2) = 0 := by
      by_cases ha : e2.val.1 = e1.val.1 ∨ e2.val.1 = e1.val.2
      · have hb : ¬ (e2.val.2 = e1.val.1 ∨ e2.val.2 = e1.val.2) := fun hb => hnot_both ⟨ha, hb⟩
        simp [ha, hb]
      · simp [ha]
    rw [h1, h2]; decide

private noncomputable def nextState452 (t : ℕ)
    (st : Finset (Option {p : Fin t × Fin t // p.1 < p.2}) × (Option {p : Fin t × Fin t // p.1 < p.2} → ℕ))
    (p : Fin t → Fin 3) (c : Fin 3) :
    Finset (Option {p : Fin t × Fin t // p.1 < p.2}) × (Option {p : Fin t × Fin t // p.1 < p.2} → ℕ) :=
  (st.1.filter (fun g => raw452 t g p = c ∨ 0 < st.2 g),
   fun g => if raw452 t g p = c then st.2 g else st.2 g - 1)

private noncomputable def chooseStepMask452 (t E r : ℕ)
    (st : Finset (Option {p : Fin t × Fin t // p.1 < p.2}) × (Option {p : Fin t × Fin t // p.1 < p.2} → ℕ)) :
    Fin t → Fin 3 :=
  let M : ℝ := (ball452 r E : ℝ)
  let w : Option {p : Fin t × Fin t // p.1 < p.2} → ℝ := fun g =>
    if g ∈ st.1 then min ((2 ^ st.2 g * r.choose (st.2 g) : ℕ) : ℝ) M else 0
  have hM : 0 < M := by
    dsimp only [M, ball452]
    have h1 : 1 ≤ ∑ k ∈ Finset.range (E + 1), 2 ^ k * r.choose k := by
      have := Finset.single_le_sum (f := fun k => 2 ^ k * r.choose k) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr (Nat.zero_lt_succ E))
      simpa using this
    exact_mod_cast (by omega : 0 < ∑ k ∈ Finset.range (E + 1), 2 ^ k * r.choose k)
  Classical.choose (weighted_graph_split t M hM w (fun g => by
    dsimp only [w]
    split_ifs
    · exact ⟨le_min (by positivity) (le_of_lt hM), min_le_right _ _⟩
    · exact ⟨le_rfl, le_of_lt hM⟩))

private noncomputable def phase1State452 (t E d : ℕ)
    (pool : Finset (Option {p : Fin t × Fin t // p.1 < p.2}))
    (budget : Option {p : Fin t × Fin t // p.1 < p.2} → ℕ) :
    (k : ℕ) → (Fin k → Fin 3) →
    Finset (Option {p : Fin t × Fin t // p.1 < p.2}) × (Option {p : Fin t × Fin t // p.1 < p.2} → ℕ)
  | 0, _ => (pool, budget)
  | k + 1, hist =>
    let st := phase1State452 t E d pool budget k (fun j => hist j.castSucc)
    let p := chooseStepMask452 t E (d - (k + 1)) st
    nextState452 t st p (hist (Fin.last k))

private noncomputable def phase2Mask452 (t : ℕ)
    (S : Finset (Option {p : Fin t × Fin t // p.1 < p.2})) : Fin t → Fin 3 :=
  if h : 1 < S.card then
    let hpair := Finset.one_lt_card.mp h
    let g1 := Classical.choose hpair
    let h2 := Classical.choose_spec hpair
    let g2 := Classical.choose h2.2
    distinguishMask452 t g1 g2
  else fun _ => 0

private noncomputable def phase2State452 (t E d : ℕ)
    (pool : Finset (Option {p : Fin t × Fin t // p.1 < p.2}))
    (budget : Option {p : Fin t × Fin t // p.1 < p.2} → ℕ) :
    (blk : ℕ) → (Fin (d + blk * (2 * E + 1)) → Fin 3) →
    Finset (Option {p : Fin t × Fin t // p.1 < p.2})
  | 0, hist => (phase1State452 t E d pool budget d (fun j => hist ⟨j.val, by omega⟩)).1
  | blk + 1, hist =>
    let S := phase2State452 t E d pool budget blk (fun j => hist ⟨j.val, by nlinarith [j.isLt]⟩)
    if 1 < S.card then
      let p := phase2Mask452 t S
      S.filter (fun g =>
        (Finset.univ.filter (fun r : Fin (2 * E + 1) =>
          hist ⟨d + blk * (2 * E + 1) + r.val, by nlinarith [r.isLt]⟩ ≠ raw452 t g p)).card ≤ E)
    else S

set_option maxHeartbeats 800000 in
private lemma upper_bound_452 (errors : ℕ) :
    ∃ C : ℕ, ∀ (t : ℕ), 2 ≤ t →
      ∀ (pool : Finset (Option {p : Fin t × Fin t // p.1 < p.2}))
        (budget : Option {p : Fin t × Fin t // p.1 < p.2} → ℕ),
        (∀ g ∈ pool, budget g ≤ errors) →
        ∀ d : ℕ,
          (∑ g ∈ pool, ball452 d (budget g)) ≤ 3 ^ d →
          ∃ (ask : (i : Fin (d + C)) → (Fin i.val → Fin 3) → (Fin t → Fin 3))
            (out : (Fin (d + C) → Fin 3) → Option {p : Fin t × Fin t // p.1 < p.2}),
            ∀ g ∈ pool, ∀ transcript : Fin (d + C) → Fin 3,
              (Finset.univ.filter (fun i : Fin (d + C) =>
                transcript i ≠ raw452 t g
                  (ask i (fun j => transcript (j.castLE (Nat.le_of_lt i.isLt)))))).card ≤ budget g →
              out transcript = g := by
  classical
  rcases poly_le_exp_4_3 errors with ⟨A, hA_pos, hA_bound⟩
  let B_E : ℝ := ((errors + 1 : ℕ) : ℝ) * (2 : ℝ) ^ errors * A
  have hB_pos : 0 < B_E := by dsimp only [B_E]; positivity
  let K0 : ℕ := Nat.ceil ((1 + 6 * Real.sqrt B_E) ^ 2)
  let C : ℕ := K0 * (2 * errors + 1)
  refine ⟨C, fun t _ pool budget hbud d hvol => ?_⟩
  let ask : (i : Fin (d + C)) → (Fin i.val → Fin 3) → (Fin t → Fin 3) := fun i hist =>
    if hi : i.val < d then
      let st := phase1State452 t errors d pool budget i.val hist
      chooseStepMask452 t errors (d - (i.val + 1)) st
    else
      let blk := (i.val - d) / (2 * errors + 1)
      have hle : d + blk * (2 * errors + 1) ≤ i.val := by
        have h1 := Nat.div_mul_le_self (i.val - d) (2 * errors + 1)
        dsimp only [blk]; omega
      let S := phase2State452 t errors d pool budget blk (fun j => hist ⟨j.val, by omega⟩)
      phase2Mask452 t S
  let out : (Fin (d + C) → Fin 3) → Option {p : Fin t × Fin t // p.1 < p.2} := fun transcript =>
    let S := phase2State452 t errors d pool budget K0 transcript
    if h : S.Nonempty then h.choose else none
  refine ⟨ask, out, fun g hg transcript hmis => ?_⟩
  have hphase1_inv : ∀ (k : ℕ) (hk : k ≤ d),
      let pref : Fin k → Fin 3 := fun j => transcript ⟨j.val, by omega⟩
      let st := phase1State452 t errors d pool budget k pref
      let mis_k := (Finset.univ.filter (fun j : Fin k =>
        transcript ⟨j.val, by omega⟩ ≠ raw452 t g
          (ask ⟨j.val, by omega⟩ (fun l => transcript (l.castLE (by omega)))))).card
      (∀ x ∈ st.1, st.2 x ≤ errors) ∧
      (g ∈ st.1 ∧ st.2 g = budget g - mis_k) ∧
      (1 / Real.sqrt 3) ^ (d - k) * Real.sqrt (∑ x ∈ st.1, (ball452 (d - k) (st.2 x) : ℝ)) ≤
        1 + 2 * Real.sqrt B_E * ∑ j ∈ Finset.range k, (2 / 3 : ℝ) ^ (d - 1 - j) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨hbud, ⟨hg, by dsimp only [phase1State452]; simp⟩, ?_⟩
      have h3_pos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
      have h3_pow : (Real.sqrt 3) ^ d = Real.sqrt ((3 ^ d : ℕ) : ℝ) := by
        rw [← sqrt_pow_eq 3 (by norm_num) d]; push_cast; rfl
      have hvol_r : ∑ x ∈ pool, (ball452 d (budget x) : ℝ) ≤ ((3 ^ d : ℕ) : ℝ) := by
        exact_mod_cast hvol
      have hsq_le : Real.sqrt (∑ x ∈ pool, (ball452 d (budget x) : ℝ)) ≤ (Real.sqrt 3) ^ d := by
        rw [h3_pow]; exact Real.sqrt_le_sqrt hvol_r
      have hdiv : (1 / Real.sqrt 3) ^ d * Real.sqrt (∑ x ∈ pool, (ball452 d (budget x) : ℝ)) ≤ 1 := by
        rw [one_div, inv_pow, inv_mul_le_iff₀ (pow_pos h3_pos d), mul_one]
        exact hsq_le
      dsimp only [phase1State452]
      simpa using hdiv
    | succ k ih =>
      intro hk
      rcases ih (by omega) with ⟨hbud_k, ⟨hg_k, hbg_k⟩, hpot_k⟩
      set pref_k : Fin k → Fin 3 := fun j => transcript ⟨j.val, by omega⟩
      set pref_k1 : Fin (k + 1) → Fin 3 := fun j => transcript ⟨j.val, by omega⟩
      set st_k := phase1State452 t errors d pool budget k pref_k
      set r := d - (k + 1)
      have hr_succ : d - k = r + 1 := by dsimp only [r]; omega
      set p_k := chooseStepMask452 t errors r st_k
      have hst_eq : phase1State452 t errors d pool budget (k + 1) pref_k1 =
          nextState452 t st_k p_k (transcript ⟨k, by omega⟩) := rfl
      have hask_k : ask ⟨k, by omega⟩ (fun l => transcript (l.castLE (by omega))) = p_k := by
        dsimp only [ask]
        rw [dif_pos (by omega : k < d)]
        rfl
      have hmis_succ : (Finset.univ.filter (fun j : Fin (k + 1) =>
          transcript ⟨j.val, by omega⟩ ≠ raw452 t g
            (ask ⟨j.val, by omega⟩ (fun l => transcript (l.castLE (by omega)))))).card =
          (Finset.univ.filter (fun j : Fin k =>
            transcript ⟨j.val, by omega⟩ ≠ raw452 t g
              (ask ⟨j.val, by omega⟩ (fun l => transcript (l.castLE (by omega)))))).card +
          (if transcript ⟨k, by omega⟩ ≠ raw452 t g p_k then 1 else 0) := by
        rw [Finset.card_filter, Fin.sum_univ_castSucc, ← Finset.card_filter]
        congr 1
        dsimp only [Fin.val_last]
        exact congrArg (fun x => if transcript ⟨k, by omega⟩ ≠ raw452 t g x then 1 else 0) hask_k
      have hmis_le_tot : (Finset.univ.filter (fun j : Fin (k + 1) =>
          transcript ⟨j.val, by omega⟩ ≠ raw452 t g
            (ask ⟨j.val, by omega⟩ (fun l => transcript (l.castLE (by omega)))))).card ≤ budget g := by
        refine le_trans ?_ hmis
        refine Finset.card_le_card_of_injOn (fun j => ⟨j.val, by omega⟩) ?_ ?_
        · intro j hj
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          exact (Finset.mem_filter.mp hj).2
        · intro j1 _ j2 _ h; exact Fin.ext (Fin.mk.inj h)
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        rw [hst_eq] at hx ⊢
        dsimp only [nextState452] at hx ⊢
        have hx_k : x ∈ st_k.1 := (Finset.mem_filter.mp hx).1
        have hle := hbud_k x hx_k
        split_ifs <;> omega
      · rw [hst_eq]
        dsimp only [nextState452]
        by_cases hmatch : raw452 t g p_k = transcript ⟨k, by omega⟩
        · refine ⟨Finset.mem_filter.mpr ⟨hg_k, Or.inl hmatch⟩, ?_⟩
          rw [if_pos hmatch, hmis_succ, if_neg (not_not.mpr hmatch.symm), add_zero, hbg_k]
        · have hne : transcript ⟨k, by omega⟩ ≠ raw452 t g p_k := fun h => hmatch h.symm
          rw [hmis_succ, if_pos hne] at hmis_le_tot
          have hpos_bg : 0 < st_k.2 g := by omega
          refine ⟨Finset.mem_filter.mpr ⟨hg_k, Or.inr hpos_bg⟩, ?_⟩
          rw [if_neg hmatch, hmis_succ, if_pos hne, hbg_k]
          omega
      · rw [hst_eq]
        set c := transcript ⟨k, by omega⟩
        set M : ℝ := (ball452 r errors : ℝ)
        have hM_pos : 0 < M := by
          dsimp only [M, ball452]
          have h1 : 1 ≤ ∑ j ∈ Finset.range (errors + 1), 2 ^ j * r.choose j := by
            have := Finset.single_le_sum (f := fun j => 2 ^ j * r.choose j) (fun _ _ => Nat.zero_le _)
              (Finset.mem_range.mpr (Nat.zero_lt_succ errors))
            simpa using this
          exact_mod_cast (by omega : 0 < ∑ j ∈ Finset.range (errors + 1), 2 ^ j * r.choose j)
        let w : Option {p : Fin t × Fin t // p.1 < p.2} → ℝ := fun x =>
          if x ∈ st_k.1 then min ((2 ^ st_k.2 x * r.choose (st_k.2 x) : ℕ) : ℝ) M else 0
        have hw_eq : ∀ x ∈ st_k.1, w x = ((2 ^ st_k.2 x * r.choose (st_k.2 x) : ℕ) : ℝ) := by
          intro x hx
          dsimp only [w]
          rw [if_pos hx, min_eq_left]
          have hle : 2 ^ st_k.2 x * r.choose (st_k.2 x) ≤ ball452 r errors := by
            dsimp only [ball452]
            exact Finset.single_le_sum (f := fun j => 2 ^ j * r.choose j) (fun _ _ => Nat.zero_le _)
              (Finset.mem_range.mpr (Nat.lt_succ_of_le (hbud_k x hx)))
          dsimp only [M]
          exact_mod_cast hle
        have hsplit := Classical.choose_spec (weighted_graph_split t M hM_pos w (fun x => by
          dsimp only [w]
          split_ifs
          · exact ⟨le_min (by positivity) (le_of_lt hM_pos), min_le_right _ _⟩
          · exact ⟨le_rfl, le_of_lt hM_pos⟩)) c
        change ∑ x ∈ Finset.univ.filter (fun x => raw452 t x p_k = c), w x ≤
          (∑ x, w x) / 3 + Real.sqrt (2 * (∑ x, w x) * M) + 3 * M at hsplit
        set Vprev : ℝ := ∑ x ∈ st_k.1, (ball452 (r + 1) (st_k.2 x) : ℝ)
        set Bbase : ℝ := ∑ x ∈ st_k.1, (ballPrev452 r (st_k.2 x) : ℝ)
        set Wtot : ℝ := ∑ x, w x
        have hWtot_eq : Wtot = ∑ x ∈ st_k.1, ((2 ^ st_k.2 x * r.choose (st_k.2 x) : ℕ) : ℝ) := by
          dsimp only [Wtot]
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => x ∈ st_k.1)]
          have hz : ∑ x ∈ Finset.univ.filter (fun x => ¬ x ∈ st_k.1), w x = 0 :=
            Finset.sum_eq_zero fun x hx => by dsimp only [w]; rw [if_neg (Finset.mem_filter.mp hx).2]
          rw [hz, add_zero]
          have hf : Finset.univ.filter (fun x => x ∈ st_k.1) = st_k.1 := by ext x; simp
          rw [hf]
          exact Finset.sum_congr rfl fun x hx => hw_eq x hx
        have hVprev_rel : Vprev = 3 * Bbase + Wtot := by
          dsimp only [Vprev, Bbase]
          rw [hWtot_eq, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun x _ => ?_
          have h1 := ball452_succ r (st_k.2 x)
          have h2 := ball452_eq_prev_add r (st_k.2 x)
          have h3 : ball452 (r + 1) (st_k.2 x) = 3 * ballPrev452 r (st_k.2 x) + 2 ^ st_k.2 x * r.choose (st_k.2 x) := by
            omega
          exact_mod_cast h3
        have hVnext_eq : ∑ x ∈ (nextState452 t st_k p_k c).1, (ball452 r ((nextState452 t st_k p_k c).2 x) : ℝ) =
            Bbase + ∑ x ∈ Finset.univ.filter (fun x => raw452 t x p_k = c), w x := by
          dsimp only [nextState452, Bbase]
          have hrew_w : ∑ x ∈ Finset.univ.filter (fun x => raw452 t x p_k = c), w x =
              ∑ x ∈ st_k.1, if raw452 t x p_k = c then ((2 ^ st_k.2 x * r.choose (st_k.2 x) : ℕ) : ℝ) else 0 := by
            rw [Finset.sum_filter, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => x ∈ st_k.1)]
            have hz : ∑ x ∈ Finset.univ.filter (fun x => ¬ x ∈ st_k.1),
                (if raw452 t x p_k = c then w x else 0) = 0 :=
              Finset.sum_eq_zero fun x hx => by
                dsimp only [w]; rw [if_neg (Finset.mem_filter.mp hx).2]; split_ifs <;> rfl
            rw [hz, add_zero]
            have hf : Finset.univ.filter (fun x => x ∈ st_k.1) = st_k.1 := by ext x; simp
            rw [hf]
            refine Finset.sum_congr rfl fun x hx => by rw [hw_eq x hx]
          rw [hrew_w, ← Finset.sum_add_distrib, Finset.sum_filter]
          refine Finset.sum_congr rfl fun x _ => ?_
          by_cases hm : raw452 t x p_k = c
          · rw [if_pos (Or.inl hm), if_pos hm, if_pos hm]
            exact_mod_cast ball452_eq_prev_add r (st_k.2 x)
          · by_cases hb : 0 < st_k.2 x
            · rw [if_pos (Or.inr hb), if_neg hm, if_neg hm, add_zero]
              dsimp only [ballPrev452]; rw [if_neg (by omega)]
            · rw [if_neg (by tauto), if_neg hm, add_zero]
              dsimp only [ballPrev452]; rw [if_pos (by omega)]; norm_num
        have hWtot_le_V : Wtot ≤ Vprev := by
          have hB_nn : 0 ≤ Bbase := Finset.sum_nonneg fun _ _ => by positivity
          linarith
        have hVprev_nn : 0 ≤ Vprev := Finset.sum_nonneg fun _ _ => by positivity
        have hVnext_le : ∑ x ∈ (nextState452 t st_k p_k c).1, (ball452 r ((nextState452 t st_k p_k c).2 x) : ℝ) ≤
            Vprev / 3 + Real.sqrt (2 * Vprev * M) + 3 * M := by
          rw [hVnext_eq]
          have hsq_mono : Real.sqrt (2 * Wtot * M) ≤ Real.sqrt (2 * Vprev * M) :=
            Real.sqrt_le_sqrt (by nlinarith)
          linarith
        have hsqrt_le : Real.sqrt (∑ x ∈ (nextState452 t st_k p_k c).1, (ball452 r ((nextState452 t st_k p_k c).2 x) : ℝ)) ≤
            Real.sqrt Vprev / Real.sqrt 3 + 2 * Real.sqrt M :=
          (Real.sqrt_le_sqrt hVnext_le).trans (sqrt_step_bound Vprev M hVprev_nn (le_of_lt hM_pos))
        have hM_bound : M ≤ B_E * (4 / 3 : ℝ) ^ r := by
          have h1 := ball452_le_poly errors r
          have h2 := hA_bound r
          dsimp only [M, B_E]
          have hcoef_nn : (0 : ℝ) ≤ ((errors + 1 : ℕ) : ℝ) * (2 : ℝ) ^ errors := by positivity
          calc (ball452 r errors : ℝ) ≤ ((errors + 1 : ℕ) : ℝ) * (2 : ℝ) ^ errors * ((r + 1 : ℕ) : ℝ) ^ errors := h1
            _ ≤ ((errors + 1 : ℕ) : ℝ) * (2 : ℝ) ^ errors * (A * (4 / 3 : ℝ) ^ r) := mul_le_mul_of_nonneg_left h2 hcoef_nn
            _ = ((errors + 1 : ℕ) : ℝ) * (2 : ℝ) ^ errors * A * (4 / 3 : ℝ) ^ r := by ring
        have hsqrtM_le : (1 / Real.sqrt 3) ^ r * (2 * Real.sqrt M) ≤ 2 * Real.sqrt B_E * (2 / 3 : ℝ) ^ r := by
          have hsqM : Real.sqrt M ≤ Real.sqrt B_E * (2 / Real.sqrt 3) ^ r := by
            have h1 := Real.sqrt_le_sqrt hM_bound
            rw [Real.sqrt_mul (le_of_lt hB_pos), sqrt_pow_eq (4 / 3 : ℝ) (by norm_num) r] at h1
            have h43 : Real.sqrt (4 / 3 : ℝ) = 2 / Real.sqrt 3 := by
              rw [Real.sqrt_div (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
            rwa [h43] at h1
          have h3_nn : (0 : ℝ) ≤ (1 / Real.sqrt 3) ^ r := by positivity
          calc (1 / Real.sqrt 3) ^ r * (2 * Real.sqrt M)
              ≤ (1 / Real.sqrt 3) ^ r * (2 * (Real.sqrt B_E * (2 / Real.sqrt 3) ^ r)) := by nlinarith
            _ = 2 * Real.sqrt B_E * ((1 / Real.sqrt 3) * (2 / Real.sqrt 3)) ^ r := by rw [mul_pow]; ring
            _ = 2 * Real.sqrt B_E * (2 / 3 : ℝ) ^ r := by
                congr 1; congr 1
                have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
                field_simp [show Real.sqrt 3 ≠ 0 from ne_of_gt (Real.sqrt_pos.mpr (by norm_num))]
                linarith
        have hstep_pot : (1 / Real.sqrt 3) ^ r *
            Real.sqrt (∑ x ∈ (nextState452 t st_k p_k c).1, (ball452 r ((nextState452 t st_k p_k c).2 x) : ℝ)) ≤
            (1 / Real.sqrt 3) ^ (r + 1) * Real.sqrt Vprev + 2 * Real.sqrt B_E * (2 / 3 : ℝ) ^ r := by
          have h3_nn : (0 : ℝ) ≤ (1 / Real.sqrt 3) ^ r := by positivity
          calc (1 / Real.sqrt 3) ^ r *
                Real.sqrt (∑ x ∈ (nextState452 t st_k p_k c).1, (ball452 r ((nextState452 t st_k p_k c).2 x) : ℝ))
              ≤ (1 / Real.sqrt 3) ^ r * (Real.sqrt Vprev / Real.sqrt 3 + 2 * Real.sqrt M) :=
                mul_le_mul_of_nonneg_left hsqrt_le h3_nn
            _ = (1 / Real.sqrt 3) ^ (r + 1) * Real.sqrt Vprev + (1 / Real.sqrt 3) ^ r * (2 * Real.sqrt M) := by
                rw [pow_succ]; ring
            _ ≤ (1 / Real.sqrt 3) ^ (r + 1) * Real.sqrt Vprev + 2 * Real.sqrt B_E * (2 / 3 : ℝ) ^ r := by
                linarith
        rw [hr_succ] at hpot_k
        rw [Finset.sum_range_succ, mul_add]
        have hr_eq : d - 1 - k = r := by dsimp only [r]; omega
        rw [hr_eq]
        linarith
  rcases hphase1_inv d le_rfl with ⟨_, ⟨hg_d, _⟩, hpot_d⟩
  set Sd := (phase1State452 t errors d pool budget d (fun j => transcript ⟨j.val, by omega⟩)).1
  have hSd_card : Sd.card ≤ K0 := by
    have hsum_d : ∑ x ∈ Sd, (ball452 0 ((phase1State452 t errors d pool budget d (fun j => transcript ⟨j.val, by omega⟩)).2 x) : ℝ) =
        (Sd.card : ℝ) := by
      simp [ball452_zero_dim]
    rw [Nat.sub_self, pow_zero, one_mul, hsum_d] at hpot_d
    have hgeom : ∑ j ∈ Finset.range d, (2 / 3 : ℝ) ^ (d - 1 - j) ≤ 3 := by
      have hrev : ∑ j ∈ Finset.range d, (2 / 3 : ℝ) ^ (d - 1 - j) = ∑ j ∈ Finset.range d, (2 / 3 : ℝ) ^ j := by
        refine Finset.sum_bij (fun j _ => d - 1 - j)
          (fun j hj => Finset.mem_range.mpr (by have := Finset.mem_range.mp hj; omega))
          (fun j1 hj1 j2 hj2 h => by have := Finset.mem_range.mp hj1; have := Finset.mem_range.mp hj2; omega)
          (fun j hj => ⟨d - 1 - j, Finset.mem_range.mpr (by have := Finset.mem_range.mp hj; omega), by
            have := Finset.mem_range.mp hj; omega⟩)
          (fun _ _ => rfl)
      rw [hrev]; exact geom_sum_two_thirds d
    have hsq_le : Real.sqrt (Sd.card : ℝ) ≤ 1 + 6 * Real.sqrt B_E := by
      have hB_nn : 0 ≤ Real.sqrt B_E := Real.sqrt_nonneg _
      nlinarith
    have hcard_r : (Sd.card : ℝ) ≤ (1 + 6 * Real.sqrt B_E) ^ 2 := by
      rw [← Real.sq_sqrt (by positivity : (0 : ℝ) ≤ Sd.card)]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq_le 2
    exact_mod_cast (hcard_r.trans (Nat.le_ceil _))
  have hblk_le_C : ∀ blk : ℕ, blk ≤ K0 → blk * (2 * errors + 1) ≤ C := fun blk hblk =>
    Nat.mul_le_mul_right (2 * errors + 1) hblk
  have hblk_lt_C : ∀ (blk : ℕ), blk + 1 ≤ K0 → ∀ r : Fin (2 * errors + 1),
      d + blk * (2 * errors + 1) + r.val < d + C := by
    intro blk hblk r
    have h1 : (blk + 1) * (2 * errors + 1) ≤ C := hblk_le_C (blk + 1) hblk
    have h2 : (blk + 1) * (2 * errors + 1) = blk * (2 * errors + 1) + (2 * errors + 1) := by ring
    omega
  have hphase2_congr : ∀ (b1 b2 : ℕ) (hb : b1 = b2)
      (h1 : Fin (d + b1 * (2 * errors + 1)) → Fin 3)
      (h2 : Fin (d + b2 * (2 * errors + 1)) → Fin 3),
      (∀ j (hj1 : j < d + b1 * (2 * errors + 1)) (hj2 : j < d + b2 * (2 * errors + 1)),
        h1 ⟨j, hj1⟩ = h2 ⟨j, hj2⟩) →
      phase2State452 t errors d pool budget b1 h1 = phase2State452 t errors d pool budget b2 h2 := by
    rintro b1 _ rfl h1 h2 hh
    congr 1; funext j; exact hh j.val j.isLt j.isLt
  have hphase2_inv : ∀ (blk : ℕ) (hblk : blk ≤ K0),
      let S := phase2State452 t errors d pool budget blk (fun j => transcript ⟨j.val, by have := hblk_le_C blk hblk; omega⟩)
      g ∈ S ∧ (S.card ≤ K0 - blk ∨ S.card ≤ 1) := by
    intro blk
    induction blk with
    | zero =>
      intro _
      change g ∈ Sd ∧ (Sd.card ≤ K0 - 0 ∨ Sd.card ≤ 1)
      exact ⟨hg_d, Or.inl (by simpa using hSd_card)⟩
    | succ blk ih =>
      intro hblk
      rcases ih (by omega) with ⟨hg_b, hcard_b⟩
      set Sb := phase2State452 t errors d pool budget blk (fun j => transcript ⟨j.val, by have := hblk_le_C blk (by omega); omega⟩)
      have hstep_eq : phase2State452 t errors d pool budget (blk + 1)
            (fun j => transcript ⟨j.val, by have := hblk_le_C (blk + 1) hblk; omega⟩) =
          if 1 < Sb.card then
            Sb.filter (fun x =>
              (Finset.univ.filter (fun r : Fin (2 * errors + 1) =>
                transcript ⟨d + blk * (2 * errors + 1) + r.val, hblk_lt_C blk hblk r⟩ ≠
                  raw452 t x (phase2Mask452 t Sb))).card ≤ errors)
          else Sb := rfl
      rw [hstep_eq]
      by_cases hgt1 : 1 < Sb.card
      · rw [if_pos hgt1]
        have hask_blk : ∀ r : Fin (2 * errors + 1),
            ask ⟨d + blk * (2 * errors + 1) + r.val, hblk_lt_C blk hblk r⟩
              (fun j => transcript (j.castLE (Nat.le_of_lt (hblk_lt_C blk hblk r)))) = phase2Mask452 t Sb := by
          intro r
          dsimp only [ask]
          rw [dif_neg (by omega : ¬ d + blk * (2 * errors + 1) + r.val < d)]
          have hdiv : (d + blk * (2 * errors + 1) + r.val - d) / (2 * errors + 1) = blk := by
            have h1 : d + blk * (2 * errors + 1) + r.val - d = blk * (2 * errors + 1) + r.val := by omega
            rw [h1, Nat.mul_comm blk (2 * errors + 1), Nat.mul_add_div (by omega),
              Nat.div_eq_of_lt r.isLt, add_zero]
          congr 1
          exact hphase2_congr _ blk hdiv _ _ fun _ _ _ => rfl
        have hmis_g : (Finset.univ.filter (fun r : Fin (2 * errors + 1) =>
            transcript ⟨d + blk * (2 * errors + 1) + r.val, hblk_lt_C blk hblk r⟩ ≠
              raw452 t g (phase2Mask452 t Sb))).card ≤ errors := by
          refine le_trans ?_ (hmis.trans (hbud g hg))
          refine Finset.card_le_card_of_injOn (fun r => ⟨d + blk * (2 * errors + 1) + r.val, hblk_lt_C blk hblk r⟩) ?_ ?_
          · intro r hr
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            rw [hask_blk r]
            exact (Finset.mem_filter.mp hr).2
          · intro r1 _ r2 _ h; exact Fin.ext (by have := Fin.mk.inj h; omega)
        refine ⟨Finset.mem_filter.mpr ⟨hg_b, hmis_g⟩, ?_⟩
        have hpair := Finset.one_lt_card.mp hgt1
        set g1 := Classical.choose hpair
        have hg1_spec := Classical.choose_spec hpair
        set g2 := Classical.choose hg1_spec.2
        have hg2_spec := Classical.choose_spec hg1_spec.2
        have hg1_mem : g1 ∈ Sb := hg1_spec.1
        have hg2_mem : g2 ∈ Sb := hg2_spec.1
        have hg12_ne : g1 ≠ g2 := hg2_spec.2
        have hmask_eq : phase2Mask452 t Sb = distinguishMask452 t g1 g2 := by
          dsimp only [phase2Mask452]
          rw [dif_pos hgt1]
        have hdiff_raw : raw452 t g1 (phase2Mask452 t Sb) ≠ raw452 t g2 (phase2Mask452 t Sb) := by
          rw [hmask_eq]; exact distinguishMask452_spec t g1 g2 hg12_ne
        have helim : ¬ ((Finset.univ.filter (fun r : Fin (2 * errors + 1) =>
              transcript ⟨d + blk * (2 * errors + 1) + r.val, hblk_lt_C blk hblk r⟩ ≠
                raw452 t g1 (phase2Mask452 t Sb))).card ≤ errors ∧
            (Finset.univ.filter (fun r : Fin (2 * errors + 1) =>
              transcript ⟨d + blk * (2 * errors + 1) + r.val, hblk_lt_C blk hblk r⟩ ≠
                raw452 t g2 (phase2Mask452 t Sb))).card ≤ errors) := by
          rintro ⟨h1, h2⟩
          have hunion : (Finset.univ : Finset (Fin (2 * errors + 1))) ⊆
              (Finset.univ.filter (fun r : Fin (2 * errors + 1) =>
                transcript ⟨d + blk * (2 * errors + 1) + r.val, hblk_lt_C blk hblk r⟩ ≠
                  raw452 t g1 (phase2Mask452 t Sb))) ∪
              (Finset.univ.filter (fun r : Fin (2 * errors + 1) =>
                transcript ⟨d + blk * (2 * errors + 1) + r.val, hblk_lt_C blk hblk r⟩ ≠
                  raw452 t g2 (phase2Mask452 t Sb))) := by
            intro r _
            rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
            by_cases hc : transcript ⟨d + blk * (2 * errors + 1) + r.val, hblk_lt_C blk hblk r⟩ =
                raw452 t g1 (phase2Mask452 t Sb)
            · right; exact ⟨Finset.mem_univ _, fun hc2 => hdiff_raw (hc.symm.trans hc2)⟩
            · left; exact ⟨Finset.mem_univ _, hc⟩
          have hcard_le := (Finset.card_le_card hunion).trans (Finset.card_union_le _ _)
          rw [Finset.card_univ, Fintype.card_fin] at hcard_le
          omega
        have hlt_card : (Sb.filter (fun x =>
            (Finset.univ.filter (fun r : Fin (2 * errors + 1) =>
              transcript ⟨d + blk * (2 * errors + 1) + r.val, hblk_lt_C blk hblk r⟩ ≠
                raw452 t x (phase2Mask452 t Sb))).card ≤ errors)).card < Sb.card := by
          refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, fun heq => ?_⟩)
          have hm1 := (Finset.mem_filter.mp (heq ▸ hg1_mem)).2
          have hm2 := (Finset.mem_filter.mp (heq ▸ hg2_mem)).2
          exact helim ⟨hm1, hm2⟩
        rcases hcard_b with hle | hle1
        · left; omega
        · omega
      · rw [if_neg hgt1]
        exact ⟨hg_b, Or.inr (by omega)⟩
  rcases hphase2_inv K0 le_rfl with ⟨hg_end, hcard_end⟩
  set Send := phase2State452 t errors d pool budget K0 transcript
  have hcard1 : Send.card ≤ 1 := by rcases hcard_end with h | h <;> omega
  have hne : Send.Nonempty := ⟨g, hg_end⟩
  dsimp only [out]
  rw [dif_pos hne]
  have hchoose_mem : hne.choose ∈ Send := hne.choose_spec
  exact Finset.card_le_one.mp hcard1 _ hchoose_mem _ hg_end

end PEqualNP.Outside.L_pcx_452

theorem PEqualNP.Outside.L_pcx_452 :
    ∀ errors : ℕ, ∃ C : ℕ, ∀ t : ℕ, 2 ≤ t →
      let T := Fin t
      let V := Option (T × Bool)
      let Pair := {p : T × T // p.1 < p.2}
      let E := Fin 3 × T
      let Mask := T → Fin 3
      let tail := fun e : E => if e.1 = 0 then some (e.2,false) else (none : V)
      let head := fun e : E => some (e.2,decide (e.1 ≠ 1))
      let weight := fun (g : Option Pair) (e : E) (diff : Bool) =>
        if e.1 = 0 then diff.toNat else if e.1 = 2 then 1 else
        if g.elim false (fun p => decide (p.val.1 = e.2 ∨ p.val.2 = e.2)) then
          (if diff then 1 else 3) else (2 : ℕ)
      let obs := fun (g : Option Pair) (p : Mask) =>
        ∑ x : V → Bool, if (∀ i : T, p i = 0 ∨ p i = (if x (some (i,false)) then 2 else 1)) ∧
          (Finset.univ.filter (fun e : E => x (tail e) ≠ x (head e))).card = 2*t then
          ∏ e : E, weight g e (xor (x (tail e)) (x (head e))) else 0
      let raw := fun (g : Option Pair) (p : Mask) =>
        g.elim (0 : Fin 3) (fun e => if p e.val.1 = 0 ∨ p e.val.2 = 0 then 0
          else if p e.val.1 = p e.val.2 then 1 else 2)
      let answer := fun (g : Option Pair) (p : Mask) =>
        if obs g p = obs none p then (0 : Fin 3) else if obs none p < obs g p then 1 else 2
      (∀ (g : Option Pair) (p : Mask), answer g p = raw g p ∧
        4*obs g p = (if raw g p = 0 then 4 else if raw g p = 1 then 5 else 3)*obs none p) ∧
      ∀ (pool : Finset (Option Pair)) (budget : Option Pair → ℕ),
        (∀ g ∈ pool, budget g ≤ errors) →
        let feasible := fun d : ℕ =>
          ∃ (ask : (i : Fin d) → (Fin i.val → Fin 3) → Mask)
            (out : (Fin d → Fin 3) → Option Pair),
            ∀ g ∈ pool, ∀ transcript : Fin d → Fin 3,
              (Finset.univ.filter (fun i : Fin d => transcript i ≠ answer g
                (ask i (fun j => transcript (j.castLE (Nat.le_of_lt i.isLt)))))).card ≤ budget g →
              out transcript = g
        let volume := fun (d : ℕ) => ∑ g ∈ pool,
          ∑ j ∈ Finset.range (budget g+1), 2^j * d.choose j
        ∀ d : ℕ, (feasible d → volume d ≤ 3^d) ∧ (volume d ≤ 3^d → feasible (d+C)) := by
  intro errors
  rcases PEqualNP.Outside.L_pcx_452.upper_bound_452 errors with ⟨C, hC⟩
  refine ⟨C, fun t ht => ?_⟩
  intro T V Pair E Mask tail head weight obs raw answer
  have hpart1 : ∀ (g : Option Pair) (p : Mask), answer g p = raw g p ∧
      4 * obs g p = (if raw g p = 0 then 4 else if raw g p = 1 then 5 else 3) * obs none p :=
    fun g p => PEqualNP.Outside.L_pcx_452.obs_and_answer_452 t g p
  refine ⟨hpart1, fun pool budget hbud => ?_⟩
  intro feasible volume d
  constructor
  · rintro ⟨ask, out, hsolve⟩
    let Ball : Option Pair → Finset (Fin d → Fin 3) := fun g =>
      Finset.univ.filter (fun τ =>
        (Finset.univ.filter (fun i : Fin d =>
          τ i ≠ answer g (ask i (fun j => τ (j.castLE (Nat.le_of_lt i.isLt)))))).card ≤ budget g)
    have hdisj : Set.PairwiseDisjoint (pool : Set (Option Pair)) Ball := by
      intro g1 hg1 g2 hg2 hne
      rw [Function.onFun, Finset.disjoint_left]
      intro τ h1 h2
      have ho1 := hsolve g1 hg1 τ (Finset.mem_filter.mp h1).2
      have ho2 := hsolve g2 hg2 τ (Finset.mem_filter.mp h2).2
      exact hne (ho1.symm.trans ho2)
    have hcard_ball : ∀ g ∈ pool, (Ball g).card = PEqualNP.Outside.L_pcx_452.ball452 d (budget g) :=
      fun g _ => PEqualNP.Outside.L_pcx_452.card_transcript_ball d (budget g) ask (answer g)
    calc volume d = ∑ g ∈ pool, (Ball g).card :=
          Finset.sum_congr rfl fun g hg => (hcard_ball g hg).symm
      _ = (pool.biUnion Ball).card := (Finset.card_biUnion hdisj).symm
      _ ≤ (Finset.univ : Finset (Fin d → Fin 3)).card := Finset.card_le_univ _
      _ = 3 ^ d := by simp [Fintype.card_fun, Fintype.card_fin]
  · intro hvol
    rcases hC t ht pool budget hbud d hvol with ⟨ask, out, hsolve⟩
    refine ⟨ask, out, fun g hg transcript hmis => ?_⟩
    apply hsolve g hg transcript
    have heq : Finset.univ.filter (fun i : Fin (d + C) =>
        transcript i ≠ PEqualNP.Outside.L_pcx_452.raw452 t g
          (ask i (fun j => transcript (j.castLE (Nat.le_of_lt i.isLt))))) =
        Finset.univ.filter (fun i : Fin (d + C) =>
          transcript i ≠ answer g
            (ask i (fun j => transcript (j.castLE (Nat.le_of_lt i.isLt))))) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [(hpart1 g _).1]; rfl
    rwa [heq]
