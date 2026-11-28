import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_457

private def tail457 (t : ℕ) (e : Fin 3 × Fin t) : Option (Fin t × Bool) :=
  if e.1 = 0 then some (e.2, false) else none

private def head457 (t : ℕ) (e : Fin 3 × Fin t) : Option (Fin t × Bool) :=
  some (e.2, decide (e.1 ≠ 1))

private def weight457 (t : ℕ) (g : Option {p : Fin t × Fin t // p.1 < p.2})
    (e : Fin 3 × Fin t) (diff : Bool) : ℕ :=
  if e.1 = 0 then diff.toNat
  else if e.1 = 2 then 1
  else if g.elim false (fun p => decide (p.val.1 = e.2 ∨ p.val.2 = e.2)) then
    (if diff then 1 else 3)
  else 2

private def obs457 (t : ℕ) (g : Option {p : Fin t × Fin t // p.1 < p.2})
    (p : Fin t → Fin 3) : ℕ :=
  ∑ x : Option (Fin t × Bool) → Bool,
    if (∀ i : Fin t, p i = 0 ∨ p i = (if x (some (i, false)) then 2 else 1)) ∧
      (Finset.univ.filter (fun e : Fin 3 × Fin t => x (tail457 t e) ≠ x (head457 t e))).card = 2 * t then
      ∏ e : Fin 3 × Fin t, weight457 t g e (xor (x (tail457 t e)) (x (head457 t e)))
    else 0

private def triFac457 (t : ℕ) (g : Option {p : Fin t × Fin t // p.1 < p.2})
    (p : Fin t → Fin 3) (h : Bool) (i : Fin t) : ℕ :=
  if p i = 0 then 4
  else if g.elim false (fun e => decide (e.val.1 = i ∨ e.val.2 = i)) then
    (if decide (p i = 2) = h then 3 else 1)
  else 2

private lemma obs457_eq_sum_prod (t : ℕ) (g : Option {p : Fin t × Fin t // p.1 < p.2})
    (p : Fin t → Fin 3) :
    obs457 t g p = ∑ h : Bool, ∏ i : Fin t, triFac457 t g p h i := by
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
  dsimp only [obs457]
  rw [← Fintype.sum_equiv eX
    (fun q => if (∀ i : Fin t, p i = 0 ∨ p i = (if eX q (some (i, false)) then 2 else 1)) ∧
        (Finset.univ.filter (fun e : Fin 3 × Fin t => eX q (tail457 t e) ≠ eX q (head457 t e))).card = 2 * t then
        ∏ e : Fin 3 × Fin t, weight457 t g e (xor (eX q (tail457 t e)) (eX q (head457 t e))) else 0)
    (fun x => if (∀ i : Fin t, p i = 0 ∨ p i = (if x (some (i, false)) then 2 else 1)) ∧
        (Finset.univ.filter (fun e : Fin 3 × Fin t => x (tail457 t e) ≠ x (head457 t e))).card = 2 * t then
        ∏ e : Fin 3 × Fin t, weight457 t g e (xor (x (tail457 t e)) (x (head457 t e))) else 0)
    (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Fintype.sum_prod_type]
  have hinner : ∀ a : Fin t → Bool,
      ∑ b : Fin t → Bool,
        (if (∀ i : Fin t, p i = 0 ∨ p i = (if eX (h, a, b) (some (i, false)) then 2 else 1)) ∧
          (Finset.univ.filter (fun e : Fin 3 × Fin t => eX (h, a, b) (tail457 t e) ≠ eX (h, a, b) (head457 t e))).card = 2 * t then
          ∏ e : Fin 3 × Fin t, weight457 t g e (xor (eX (h, a, b) (tail457 t e)) (eX (h, a, b) (head457 t e)))
        else 0) =
      ∏ i : Fin t,
        (if p i = 0 ∨ p i = (if a i then 2 else 1) then
          (if g.elim false (fun e => decide (e.val.1 = i ∨ e.val.2 = i)) then
            (if a i = h then 3 else 1) else 2)
        else 0) := by
    intro a
    rw [Finset.sum_eq_single (fun i => !a i)]
    · have hcut : (Finset.univ.filter (fun e : Fin 3 × Fin t =>
          eX (h, a, fun i => !a i) (tail457 t e) ≠ eX (h, a, fun i => !a i) (head457 t e))).card = 2 * t := by
        rw [Finset.card_filter, Fintype.sum_prod_type_right]
        have heach : ∀ i : Fin t, ∑ k : Fin 3,
            (if eX (h, a, fun j => !a j) (tail457 t (k, i)) ≠ eX (h, a, fun j => !a j) (head457 t (k, i)) then 1 else 0) = 2 := by
          intro i
          rw [Fin.sum_univ_three]
          dsimp only [eX, Equiv.coe_fn_mk, tail457, head457]
          simp only [Fin.reduceEq, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true]
          generalize a i = ai
          cases h <;> cases ai <;> decide
        rw [Finset.sum_congr rfl fun i _ => heach i, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]
      have hprod_eq : ∏ e : Fin 3 × Fin t,
          weight457 t g e (xor (eX (h, a, fun i => !a i) (tail457 t e)) (eX (h, a, fun i => !a i) (head457 t e))) =
          ∏ i : Fin t, (if g.elim false (fun e => decide (e.val.1 = i ∨ e.val.2 = i)) then
            (if a i = h then 3 else 1) else 2) := by
        rw [Fintype.prod_prod_type_right]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Fin.prod_univ_three]
        dsimp only [eX, Equiv.coe_fn_mk, tail457, head457, weight457]
        simp only [Fin.reduceEq, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true]
        generalize a i = ai
        generalize g.elim false (fun e => decide (e.val.1 = i ∨ e.val.2 = i)) = act
        cases h <;> cases ai <;> cases act <;> decide
      by_cases hpin : ∀ i : Fin t, p i = 0 ∨ p i = (if a i then 2 else 1)
      · have hcond : (∀ i : Fin t, p i = 0 ∨ p i = (if eX (h, a, fun j => !a j) (some (i, false)) then 2 else 1)) ∧
            (Finset.univ.filter (fun e : Fin 3 × Fin t =>
              eX (h, a, fun j => !a j) (tail457 t e) ≠ eX (h, a, fun j => !a j) (head457 t e))).card = 2 * t :=
          ⟨hpin, hcut⟩
        rw [if_pos hcond, hprod_eq]
        refine Finset.prod_congr rfl fun i _ => (if_pos (hpin i)).symm
      · have hcond : ¬ ((∀ i : Fin t, p i = 0 ∨ p i = (if eX (h, a, fun j => !a j) (some (i, false)) then 2 else 1)) ∧
            (Finset.univ.filter (fun e : Fin 3 × Fin t =>
              eX (h, a, fun j => !a j) (tail457 t e) ≠ eX (h, a, fun j => !a j) (head457 t e))).card = 2 * t) :=
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
          dsimp only [eX, Equiv.coe_fn_mk, tail457, head457, weight457]
          simp [hi0])
      · rfl
    · intro hm; exact (hm (Finset.mem_univ _)).elim
  rw [Finset.sum_congr rfl fun a _ => hinner a]
  let F : Fin t → Bool → ℕ := fun i b =>
    if p i = 0 ∨ p i = (if b then 2 else 1) then
      (if g.elim false (fun e => decide (e.val.1 = i ∨ e.val.2 = i)) then
        (if b = h then 3 else 1) else 2)
    else 0
  change ∑ a : Fin t → Bool, ∏ i : Fin t, F i (a i) = ∏ i : Fin t, triFac457 t g p h i
  rw [← Fintype.prod_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.sum_bool]
  dsimp only [F, triFac457]
  generalize p i = pi
  generalize g.elim false (fun e => decide (e.val.1 = i ∨ e.val.2 = i)) = act
  fin_cases pi <;> cases h <;> cases act <;> decide

private lemma obs457_none_pos (t : ℕ) (p : Fin t → Fin 3) : 0 < obs457 t none p := by
  rw [obs457_eq_sum_prod, Fintype.sum_bool]
  have h1 : 0 < ∏ i : Fin t, triFac457 t none p false i := by
    refine Finset.prod_pos fun i _ => ?_
    dsimp only [triFac457, Option.elim]
    split_ifs <;> omega
  omega

private lemma obs457_edge_formula (t : ℕ) (e : {p : Fin t × Fin t // p.1 < p.2}) (p : Fin t → Fin 3) :
    (p e.val.1 = 0 ∨ p e.val.2 = 0 → obs457 t (some e) p = obs457 t none p) ∧
    (p e.val.1 ≠ 0 ∧ p e.val.2 ≠ 0 ∧ p e.val.1 = p e.val.2 → 4 * obs457 t (some e) p = 5 * obs457 t none p) ∧
    (p e.val.1 ≠ 0 ∧ p e.val.2 ≠ 0 ∧ p e.val.1 ≠ p e.val.2 → 4 * obs457 t (some e) p = 3 * obs457 t none p) := by
  have huv : e.val.1 ≠ e.val.2 := ne_of_lt e.2
  let rest : Finset (Fin t) := (Finset.univ.erase e.val.1).erase e.val.2
  let R : ℕ := ∏ i ∈ rest, (if p i = 0 then 4 else 2)
  have hprod_split : ∀ (g' : Option {p : Fin t × Fin t // p.1 < p.2}) (h : Bool),
      (∀ i ∈ rest, g'.elim false (fun q => decide (q.val.1 = i ∨ q.val.2 = i)) = false) →
      ∏ i : Fin t, triFac457 t g' p h i =
        triFac457 t g' p h e.val.1 * triFac457 t g' p h e.val.2 * R := by
    intro g' h hrest
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e.val.1)]
    have hv_mem : e.val.2 ∈ Finset.univ.erase e.val.1 := Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_univ _⟩
    rw [← Finset.mul_prod_erase (Finset.univ.erase e.val.1) _ hv_mem]
    rw [← mul_assoc]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    dsimp only [triFac457]
    rw [hrest i hi]
    simp only [Bool.false_eq_true, ↓reduceIte]
  have hrest_e : ∀ i ∈ rest, (some e : Option {p : Fin t × Fin t // p.1 < p.2}).elim false
      (fun q => decide (q.val.1 = i ∨ q.val.2 = i)) = false := by
    intro i hi
    have h1 : i ≠ e.val.2 := (Finset.mem_erase.mp hi).1
    have h2 : i ≠ e.val.1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    simp [Option.elim, h1.symm, h2.symm]
  have hobs_none : obs457 t none p =
      (triFac457 t none p false e.val.1 * triFac457 t none p false e.val.2 +
       triFac457 t none p true e.val.1 * triFac457 t none p true e.val.2) * R := by
    rw [obs457_eq_sum_prod, Fintype.sum_bool,
      hprod_split none false (fun _ _ => rfl), hprod_split none true (fun _ _ => rfl)]
    ring
  have hobs_e : obs457 t (some e) p =
      (triFac457 t (some e) p false e.val.1 * triFac457 t (some e) p false e.val.2 +
       triFac457 t (some e) p true e.val.1 * triFac457 t (some e) p true e.val.2) * R := by
    rw [obs457_eq_sum_prod, Fintype.sum_bool,
      hprod_split (some e) false hrest_e, hprod_split (some e) true hrest_e]
    ring
  have h9 : ∀ pu pv : Fin 3,
      let lhs := (if pu = 0 then 4 else if decide (pu = 2) = false then 3 else 1) *
                 (if pv = 0 then 4 else if decide (pv = 2) = false then 3 else 1) +
                 (if pu = 0 then 4 else if decide (pu = 2) = true then 3 else 1) *
                 (if pv = 0 then 4 else if decide (pv = 2) = true then 3 else 1)
      let rhs := (if pu = 0 then 4 else 2) * (if pv = 0 then 4 else 2) +
                 (if pu = 0 then 4 else 2) * (if pv = 0 then 4 else 2)
      (pu = 0 ∨ pv = 0 → lhs = rhs) ∧
      (pu ≠ 0 ∧ pv ≠ 0 ∧ pu = pv → 4 * lhs = 5 * rhs) ∧
      (pu ≠ 0 ∧ pv ≠ 0 ∧ pu ≠ pv → 4 * lhs = 3 * rhs) := by
    intro pu pv; fin_cases pu <;> fin_cases pv <;> decide
  have hspec := h9 (p e.val.1) (p e.val.2)
  rw [hobs_e, hobs_none]
  dsimp only [triFac457, Option.elim]
  simp only [true_or, or_true, decide_true, ↓reduceIte, Bool.false_eq_true]
  refine ⟨fun h => by rw [hspec.1 h], fun h => ?_, fun h => ?_⟩
  · rw [← mul_assoc, hspec.2.1 h, mul_assoc]
  · rw [← mul_assoc, hspec.2.2 h, mul_assoc]

private lemma read_formula_457 (t k : ℕ) (G : Finset {p : Fin t × Fin t // p.1 < p.2})
    (hG : G.card ≤ k) (p : Fin t → Fin 3) :
    let plus := (G.filter (fun e => p e.val.1 ≠ 0 ∧ p e.val.2 ≠ 0 ∧ p e.val.1 = p e.val.2)).card
    let minus := (G.filter (fun e => p e.val.1 ≠ 0 ∧ p e.val.2 ≠ 0 ∧ p e.val.1 ≠ p e.val.2)).card
    4 ^ (plus + minus) * ((obs457 t none p) ^ (k - G.card) * ∏ e ∈ G, obs457 t (some e) p) =
      (obs457 t none p) ^ k * 5 ^ plus * 3 ^ minus := by
  intro plus minus
  have hprod : ∀ S : Finset {p : Fin t × Fin t // p.1 < p.2},
      let ps := (S.filter (fun e => p e.val.1 ≠ 0 ∧ p e.val.2 ≠ 0 ∧ p e.val.1 = p e.val.2)).card
      let ms := (S.filter (fun e => p e.val.1 ≠ 0 ∧ p e.val.2 ≠ 0 ∧ p e.val.1 ≠ p e.val.2)).card
      4 ^ (ps + ms) * ∏ e ∈ S, obs457 t (some e) p =
        (obs457 t none p) ^ S.card * 5 ^ ps * 3 ^ ms := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert e S he ih =>
      dsimp only at ih ⊢
      rw [Finset.prod_insert he, Finset.card_insert_of_notMem he, Finset.filter_insert, Finset.filter_insert]
      set ps := (S.filter (fun x => p x.val.1 ≠ 0 ∧ p x.val.2 ≠ 0 ∧ p x.val.1 = p x.val.2)).card
      set ms := (S.filter (fun x => p x.val.1 ≠ 0 ∧ p x.val.2 ≠ 0 ∧ p x.val.1 ≠ p x.val.2)).card
      have hedge := obs457_edge_formula t e p
      by_cases h0 : p e.val.1 = 0 ∨ p e.val.2 = 0
      · have hnp : ¬ (p e.val.1 ≠ 0 ∧ p e.val.2 ≠ 0 ∧ p e.val.1 = p e.val.2) := by tauto
        have hnm : ¬ (p e.val.1 ≠ 0 ∧ p e.val.2 ≠ 0 ∧ p e.val.1 ≠ p e.val.2) := by tauto
        rw [if_neg hnp, if_neg hnm, hedge.1 h0, pow_succ]
        calc 4 ^ (ps + ms) * (obs457 t none p * ∏ x ∈ S, obs457 t (some x) p)
            = obs457 t none p * (4 ^ (ps + ms) * ∏ x ∈ S, obs457 t (some x) p) := by ring
          _ = obs457 t none p * ((obs457 t none p) ^ S.card * 5 ^ ps * 3 ^ ms) := by rw [ih]
          _ = (obs457 t none p) ^ S.card * obs457 t none p * 5 ^ ps * 3 ^ ms := by ring
      · push_neg at h0
        by_cases heq : p e.val.1 = p e.val.2
        · have hp : p e.val.1 ≠ 0 ∧ p e.val.2 ≠ 0 ∧ p e.val.1 = p e.val.2 := ⟨h0.1, h0.2, heq⟩
          have hnm : ¬ (p e.val.1 ≠ 0 ∧ p e.val.2 ≠ 0 ∧ p e.val.1 ≠ p e.val.2) := by tauto
          rw [if_pos hp, if_neg hnm, Finset.card_insert_of_notMem (fun hm => he (Finset.mem_filter.mp hm).1)]
          rw [show ps + 1 + ms = (ps + ms) + 1 by omega, pow_succ, pow_succ, pow_succ]
          calc 4 ^ (ps + ms) * 4 * (obs457 t (some e) p * ∏ x ∈ S, obs457 t (some x) p)
              = (4 * obs457 t (some e) p) * (4 ^ (ps + ms) * ∏ x ∈ S, obs457 t (some x) p) := by ring
            _ = (5 * obs457 t none p) * ((obs457 t none p) ^ S.card * 5 ^ ps * 3 ^ ms) := by rw [hedge.2.1 hp, ih]
            _ = (obs457 t none p) ^ S.card * obs457 t none p * (5 ^ ps * 5) * 3 ^ ms := by ring
        · have hnp : ¬ (p e.val.1 ≠ 0 ∧ p e.val.2 ≠ 0 ∧ p e.val.1 = p e.val.2) := by tauto
          have hm : p e.val.1 ≠ 0 ∧ p e.val.2 ≠ 0 ∧ p e.val.1 ≠ p e.val.2 := ⟨h0.1, h0.2, heq⟩
          rw [if_neg hnp, if_pos hm, Finset.card_insert_of_notMem (fun hm' => he (Finset.mem_filter.mp hm').1)]
          rw [show ps + (ms + 1) = (ps + ms) + 1 by omega, pow_succ, pow_succ, pow_succ]
          calc 4 ^ (ps + ms) * 4 * (obs457 t (some e) p * ∏ x ∈ S, obs457 t (some x) p)
              = (4 * obs457 t (some e) p) * (4 ^ (ps + ms) * ∏ x ∈ S, obs457 t (some x) p) := by ring
            _ = (3 * obs457 t none p) * ((obs457 t none p) ^ S.card * 5 ^ ps * 3 ^ ms) := by rw [hedge.2.2 hm, ih]
            _ = (obs457 t none p) ^ S.card * obs457 t none p * 5 ^ ps * (3 ^ ms * 3) := by ring
  have h1 := hprod G
  calc 4 ^ (plus + minus) * ((obs457 t none p) ^ (k - G.card) * ∏ e ∈ G, obs457 t (some e) p)
      = (obs457 t none p) ^ (k - G.card) * (4 ^ (plus + minus) * ∏ e ∈ G, obs457 t (some e) p) := by ring
    _ = (obs457 t none p) ^ (k - G.card) * ((obs457 t none p) ^ G.card * 5 ^ plus * 3 ^ minus) := by rw [h1]
    _ = ((obs457 t none p) ^ (k - G.card) * (obs457 t none p) ^ G.card) * 5 ^ plus * 3 ^ minus := by ring
    _ = (obs457 t none p) ^ k * 5 ^ plus * 3 ^ minus := by
        rw [← pow_add, show k - G.card + G.card = k by omega]

private def maskToInt (p : Fin t → Fin 3) : Fin t → ℤ :=
  fun i => if p i = 0 then 0 else if p i = 1 then 1 else -1

private def maskToAbs (p : Fin t → Fin 3) : Fin t → ℤ :=
  fun i => if p i = 0 then 0 else 1

private def poly457 (t : ℕ) (G : Finset {p : Fin t × Fin t // p.1 < p.2}) (x : Fin t → ℤ) : ℤ :=
  ∑ e ∈ G, x e.val.1 * x e.val.2

private lemma read_eq_iff_poly (t k : ℕ)
    (G H : Finset {p : Fin t × Fin t // p.1 < p.2}) (hG : G.card ≤ k) (hH : H.card ≤ k)
    (p : Fin t → Fin 3) :
    ((obs457 t none p) ^ (k - G.card) * ∏ e ∈ G, obs457 t (some e) p =
     (obs457 t none p) ^ (k - H.card) * ∏ e ∈ H, obs457 t (some e) p) ↔
    (poly457 t G (maskToInt p) = poly457 t H (maskToInt p) ∧
     poly457 t G (maskToAbs p) = poly457 t H (maskToAbs p)) := by
  let a1 := (G.filter (fun e => p e.val.1 ≠ 0 ∧ p e.val.2 ≠ 0 ∧ p e.val.1 = p e.val.2)).card
  let b1 := (G.filter (fun e => p e.val.1 ≠ 0 ∧ p e.val.2 ≠ 0 ∧ p e.val.1 ≠ p e.val.2)).card
  let a2 := (H.filter (fun e => p e.val.1 ≠ 0 ∧ p e.val.2 ≠ 0 ∧ p e.val.1 = p e.val.2)).card
  let b2 := (H.filter (fun e => p e.val.1 ≠ 0 ∧ p e.val.2 ≠ 0 ∧ p e.val.1 ≠ p e.val.2)).card
  have hpoly_rel : ∀ S : Finset {p : Fin t × Fin t // p.1 < p.2},
      let a := (S.filter (fun e => p e.val.1 ≠ 0 ∧ p e.val.2 ≠ 0 ∧ p e.val.1 = p e.val.2)).card
      let b := (S.filter (fun e => p e.val.1 ≠ 0 ∧ p e.val.2 ≠ 0 ∧ p e.val.1 ≠ p e.val.2)).card
      poly457 t S (maskToInt p) = (a : ℤ) - (b : ℤ) ∧
      poly457 t S (maskToAbs p) = (a : ℤ) + (b : ℤ) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [poly457]
    | @insert e S he ih =>
      dsimp only [poly457] at ih ⊢
      rw [Finset.sum_insert he, Finset.sum_insert he, Finset.filter_insert, Finset.filter_insert]
      dsimp only [maskToInt, maskToAbs] at ih ⊢
      by_cases h0 : p e.val.1 = 0 ∨ p e.val.2 = 0
      · have hnp : ¬ (p e.val.1 ≠ 0 ∧ p e.val.2 ≠ 0 ∧ p e.val.1 = p e.val.2) := by tauto
        have hnm : ¬ (p e.val.1 ≠ 0 ∧ p e.val.2 ≠ 0 ∧ p e.val.1 ≠ p e.val.2) := by tauto
        rw [if_neg hnp, if_neg hnm]
        rcases h0 with h | h
        · rw [h, if_pos rfl, if_pos rfl, zero_mul, zero_mul, zero_add, zero_add, ih.1, ih.2]; exact ⟨rfl, rfl⟩
        · rw [h, if_pos rfl, if_pos rfl, mul_zero, mul_zero, zero_add, zero_add, ih.1, ih.2]; exact ⟨rfl, rfl⟩
      · push_neg at h0
        by_cases heq : p e.val.1 = p e.val.2
        · have hp : p e.val.1 ≠ 0 ∧ p e.val.2 ≠ 0 ∧ p e.val.1 = p e.val.2 := ⟨h0.1, h0.2, heq⟩
          have hnm : ¬ (p e.val.1 ≠ 0 ∧ p e.val.2 ≠ 0 ∧ p e.val.1 ≠ p e.val.2) := by tauto
          rw [if_pos hp, if_neg hnm, Finset.card_insert_of_notMem (fun hm => he (Finset.mem_filter.mp hm).1)]
          have hmul1 : (if p e.val.1 = 0 then (0 : ℤ) else if p e.val.1 = 1 then 1 else -1) *
              (if p e.val.2 = 0 then (0 : ℤ) else if p e.val.2 = 1 then 1 else -1) = 1 := by
            rw [if_neg h0.1, if_neg h0.2, heq]; split_ifs <;> norm_num
          have hmul2 : (if p e.val.1 = 0 then (0 : ℤ) else 1) * (if p e.val.2 = 0 then (0 : ℤ) else 1) = 1 := by
            rw [if_neg h0.1, if_neg h0.2]; norm_num
          rw [hmul1, hmul2, ih.1, ih.2]; push_cast; constructor <;> ring
        · have hnp : ¬ (p e.val.1 ≠ 0 ∧ p e.val.2 ≠ 0 ∧ p e.val.1 = p e.val.2) := by tauto
          have hm : p e.val.1 ≠ 0 ∧ p e.val.2 ≠ 0 ∧ p e.val.1 ≠ p e.val.2 := ⟨h0.1, h0.2, heq⟩
          rw [if_neg hnp, if_pos hm, Finset.card_insert_of_notMem (fun hm' => he (Finset.mem_filter.mp hm').1)]
          have hmul1 : (if p e.val.1 = 0 then (0 : ℤ) else if p e.val.1 = 1 then 1 else -1) *
              (if p e.val.2 = 0 then (0 : ℤ) else if p e.val.2 = 1 then 1 else -1) = -1 := by
            rw [if_neg h0.1, if_neg h0.2]
            have h1 := h0.1; have h2 := h0.2
            generalize p e.val.1 = u at h1 heq ⊢
            generalize p e.val.2 = v at h2 heq ⊢
            fin_cases u <;> fin_cases v <;> simp_all
          have hmul2 : (if p e.val.1 = 0 then (0 : ℤ) else 1) * (if p e.val.2 = 0 then (0 : ℤ) else 1) = 1 := by
            rw [if_neg h0.1, if_neg h0.2]; norm_num
          rw [hmul1, hmul2, ih.1, ih.2]; push_cast; constructor <;> ring
  have hrG := read_formula_457 t k G hG p
  have hrH := read_formula_457 t k H hH p
  have hpG := hpoly_rel G
  have hpH := hpoly_rel H
  have hobs_pos : 0 < (obs457 t none p) ^ k := pow_pos (obs457_none_pos t p) k
  constructor
  · intro heq
    have hmul : (obs457 t none p) ^ k * (4 ^ (a2 + b2) * 5 ^ a1 * 3 ^ b1) =
        (obs457 t none p) ^ k * (4 ^ (a1 + b1) * 5 ^ a2 * 3 ^ b2) := by
      calc (obs457 t none p) ^ k * (4 ^ (a2 + b2) * 5 ^ a1 * 3 ^ b1)
          = 4 ^ (a2 + b2) * ((obs457 t none p) ^ k * 5 ^ a1 * 3 ^ b1) := by ring
        _ = 4 ^ (a2 + b2) * (4 ^ (a1 + b1) * ((obs457 t none p) ^ (k - G.card) * ∏ e ∈ G, obs457 t (some e) p)) := by rw [← hrG]
        _ = 4 ^ (a1 + b1) * (4 ^ (a2 + b2) * ((obs457 t none p) ^ (k - H.card) * ∏ e ∈ H, obs457 t (some e) p)) := by rw [heq]; ring
        _ = 4 ^ (a1 + b1) * ((obs457 t none p) ^ k * 5 ^ a2 * 3 ^ b2) := by rw [hrH]
        _ = _ := by ring
    have hpow_eq : 4 ^ (a2 + b2) * 5 ^ a1 * 3 ^ b1 = 4 ^ (a1 + b1) * 5 ^ a2 * 3 ^ b2 :=
      Nat.eq_of_mul_eq_mul_left hobs_pos hmul
    have ha_eq : a1 = a2 := by
      have h51 : 5 ^ a1 ∣ 5 ^ a2 := by
        have hd : 5 ^ a1 ∣ 4 ^ (a1 + b1) * 5 ^ a2 * 3 ^ b2 := by
          rw [← hpow_eq]; exact ⟨4 ^ (a2 + b2) * 3 ^ b1, by ring⟩
        have hc3 : Nat.Coprime (5 ^ a1) (3 ^ b2) := (by decide : Nat.Coprime 5 3).pow a1 b2
        have hc4 : Nat.Coprime (5 ^ a1) (4 ^ (a1 + b1)) := (by decide : Nat.Coprime 5 4).pow a1 (a1 + b1)
        exact hc4.dvd_of_dvd_mul_left (hc3.dvd_of_dvd_mul_right hd)
      have h52 : 5 ^ a2 ∣ 5 ^ a1 := by
        have hd : 5 ^ a2 ∣ 4 ^ (a2 + b2) * 5 ^ a1 * 3 ^ b1 := by
          rw [hpow_eq]; exact ⟨4 ^ (a1 + b1) * 3 ^ b2, by ring⟩
        have hc3 : Nat.Coprime (5 ^ a2) (3 ^ b1) := (by decide : Nat.Coprime 5 3).pow a2 b1
        have hc4 : Nat.Coprime (5 ^ a2) (4 ^ (a2 + b2)) := (by decide : Nat.Coprime 5 4).pow a2 (a2 + b2)
        exact hc4.dvd_of_dvd_mul_left (hc3.dvd_of_dvd_mul_right hd)
      have hle1 : a1 ≤ a2 := (Nat.pow_dvd_pow_iff_le_right (by omega : 1 < 5)).mp h51
      have hle2 : a2 ≤ a1 := (Nat.pow_dvd_pow_iff_le_right (by omega : 1 < 5)).mp h52
      omega
    have hb_eq : b1 = b2 := by
      have h31 : 3 ^ b1 ∣ 3 ^ b2 := by
        have hd : 3 ^ b1 ∣ 4 ^ (a1 + b1) * 5 ^ a2 * 3 ^ b2 := by
          rw [← hpow_eq]; exact ⟨4 ^ (a2 + b2) * 5 ^ a1, by ring⟩
        have hc : Nat.Coprime (3 ^ b1) (4 ^ (a1 + b1) * 5 ^ a2) :=
          ((by decide : Nat.Coprime 3 4).pow b1 (a1 + b1)).mul_right ((by decide : Nat.Coprime 3 5).pow b1 a2)
        exact hc.dvd_of_dvd_mul_left hd
      have h32 : 3 ^ b2 ∣ 3 ^ b1 := by
        have hd : 3 ^ b2 ∣ 4 ^ (a2 + b2) * 5 ^ a1 * 3 ^ b1 := by
          rw [hpow_eq]; exact ⟨4 ^ (a1 + b1) * 5 ^ a2, by ring⟩
        have hc : Nat.Coprime (3 ^ b2) (4 ^ (a2 + b2) * 5 ^ a1) :=
          ((by decide : Nat.Coprime 3 4).pow b2 (a2 + b2)).mul_right ((by decide : Nat.Coprime 3 5).pow b2 a1)
        exact hc.dvd_of_dvd_mul_left hd
      have hle1 : b1 ≤ b2 := (Nat.pow_dvd_pow_iff_le_right (by omega : 1 < 3)).mp h31
      have hle2 : b2 ≤ b1 := (Nat.pow_dvd_pow_iff_le_right (by omega : 1 < 3)).mp h32
      omega
    rw [hpG.1, hpG.2, hpH.1, hpH.2]
    change (a1 : ℤ) - (b1 : ℤ) = (a2 : ℤ) - (b2 : ℤ) ∧ (a1 : ℤ) + (b1 : ℤ) = (a2 : ℤ) + (b2 : ℤ)
    rw [ha_eq, hb_eq]; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    rw [hpG.1, hpH.1] at h1
    rw [hpG.2, hpH.2] at h2
    have ha_eq : a1 = a2 := by omega
    have hb_eq : b1 = b2 := by omega
    have h4pos : 0 < 4 ^ (a1 + b1) := pow_pos (by omega) _
    have hmul : 4 ^ (a1 + b1) * ((obs457 t none p) ^ (k - G.card) * ∏ e ∈ G, obs457 t (some e) p) =
        4 ^ (a1 + b1) * ((obs457 t none p) ^ (k - H.card) * ∏ e ∈ H, obs457 t (some e) p) := by
      rw [hrG]
      have h2' : 4 ^ (a1 + b1) * ((obs457 t none p) ^ (k - H.card) * ∏ e ∈ H, obs457 t (some e) p) =
          (obs457 t none p) ^ k * 5 ^ a1 * 3 ^ b1 := by
        rw [ha_eq, hb_eq]; exact hrH
      rw [h2']
    exact Nat.eq_of_mul_eq_mul_left h4pos hmul

private def evalQuad (t : ℕ) (coef : {p : Fin t × Fin t // p.1 < p.2} → ℤ) (x : Fin t → ℤ) : ℤ :=
  ∑ e : {p : Fin t × Fin t // p.1 < p.2}, coef e * x e.val.1 * x e.val.2

private def evalLin (t : ℕ) (lin : Fin t → ℤ) (x : Fin t → ℤ) : ℤ :=
  ∑ i : Fin t, lin i * x i

private lemma quad_nz_ge_four_ninths (t : ℕ) (coef : {p : Fin t × Fin t // p.1 < p.2} → ℤ)
    (hne : ∃ e0, coef e0 ≠ 0) :
    4 * 3 ^ t ≤ 9 * ((Finset.univ : Finset (Fin t → Fin 3)).filter
      (fun p => evalQuad t coef (maskToInt p) ≠ 0)).card := by
  rcases hne with ⟨e0, he0⟩
  let u := e0.val.1
  let v := e0.val.2
  have huv : u ≠ v := ne_of_lt e0.2
  let Z : Type := {i : Fin t // i ≠ u ∧ i ≠ v}
  let eM : ((Fin 3 × Fin 3) × (Z → Fin 3)) ≃ (Fin t → Fin 3) :=
    { toFun := fun q i =>
        if hi1 : i = u then q.1.1
        else if hi2 : i = v then q.1.2
        else q.2 ⟨i, hi1, hi2⟩
      invFun := fun p => ((p u, p v), fun z => p z.1)
      left_inv := fun ⟨⟨a, b⟩, r⟩ => by
        refine Prod.ext (Prod.ext ?_ ?_) ?_
        · simp
        · simp [huv.symm]
        · funext ⟨i, hi1, hi2⟩; simp [hi1, hi2]
      right_inv := fun p => by
        funext i; by_cases h1 : i = u
        · subst h1; simp
        · by_cases h2 : i = v
          · subst h2; simp [h1]
          · simp [h1, h2] }
  have hbij : ((Finset.univ : Finset (Fin t → Fin 3)).filter (fun p => evalQuad t coef (maskToInt p) ≠ 0)).card =
      ∑ r : Z → Fin 3, ((Finset.univ : Finset (Fin 3 × Fin 3)).filter
        (fun ab => evalQuad t coef (maskToInt (eM (ab, r))) ≠ 0)).card := by
    rw [Finset.card_filter]
    rw [← Fintype.sum_equiv eM
      (fun q => if evalQuad t coef (maskToInt (eM q)) ≠ 0 then 1 else 0)
      (fun p => if evalQuad t coef (maskToInt p) ≠ 0 then 1 else 0) (fun _ => rfl)]
    rw [Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun r _ => (Finset.card_filter _ _).symm
  have hcardZ : Fintype.card (Z → Fin 3) * 9 = 3 ^ t := by
    have hcard : Fintype.card Z = t - 2 := by
      have h1 : Fintype.card Z = ((Finset.univ.erase u).erase v).card := by
        rw [Fintype.card_subtype]
        congr 1; ext i; simp [and_comm]
      have hv_mem : v ∈ (Finset.univ : Finset (Fin t)).erase u := Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_univ _⟩
      rw [h1, Finset.card_erase_of_mem hv_mem, Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, Fintype.card_fin]
      omega
    rw [Fintype.card_fun, Fintype.card_fin, hcard]
    have ht2 : 2 ≤ t := by
      have := e0.2; omega
    calc 3 ^ (t - 2) * 9 = 3 ^ (t - 2) * 3 ^ 2 := by norm_num
      _ = 3 ^ (t - 2 + 2) := (pow_add 3 _ 2).symm
      _ = 3 ^ t := by congr 1; omega
  have hfiber : ∀ r : Z → Fin 3,
      4 ≤ ((Finset.univ : Finset (Fin 3 × Fin 3)).filter
        (fun ab => evalQuad t coef (maskToInt (eM (ab, r))) ≠ 0)).card := by
    intro r
    let x0 : Fin t → ℤ := fun i => if hi1 : i = u then 0 else if hi2 : i = v then 0 else maskToInt (eM ((0, 0), r)) i
    let c0 := coef e0
    let Lu : ℤ := ∑ e ∈ Finset.univ.filter (fun e : {p : Fin t × Fin t // p.1 < p.2} => e ≠ e0 ∧ (e.val.1 = u ∨ e.val.2 = u)),
      coef e * (if e.val.1 = u then x0 e.val.2 else x0 e.val.1)
    let Lv : ℤ := ∑ e ∈ Finset.univ.filter (fun e : {p : Fin t × Fin t // p.1 < p.2} => e ≠ e0 ∧ (e.val.1 = v ∨ e.val.2 = v)),
      coef e * (if e.val.1 = v then x0 e.val.2 else x0 e.val.1)
    let C : ℤ := ∑ e ∈ Finset.univ.filter (fun e : {p : Fin t × Fin t // p.1 < p.2} =>
        e.val.1 ≠ u ∧ e.val.2 ≠ u ∧ e.val.1 ≠ v ∧ e.val.2 ≠ v),
      coef e * x0 e.val.1 * x0 e.val.2
    let f3 : Fin 3 → ℤ := fun a => if a = 0 then 0 else if a = 1 then 1 else -1
    have hf3_inj : ∀ a1 a2 : Fin 3, f3 a1 = f3 a2 → a1 = a2 := by
      intro a1 a2 h; fin_cases a1 <;> fin_cases a2 <;> simp [f3] at h ⊢
    have hform : ∀ ab : Fin 3 × Fin 3,
        evalQuad t coef (maskToInt (eM (ab, r))) = c0 * f3 ab.1 * f3 ab.2 + Lu * f3 ab.1 + Lv * f3 ab.2 + C := by
      intro ⟨a, b⟩
      have hx_eq : ∀ i : Fin t, maskToInt (eM ((a, b), r)) i =
          if i = u then f3 a else if i = v then f3 b else x0 i := by
        intro i
        by_cases h1 : i = u
        · subst h1; simp [maskToInt, eM, f3]
        · by_cases h2 : i = v
          · subst h2; simp [maskToInt, eM, f3, huv.symm]
          · dsimp only [maskToInt, eM, Equiv.coe_fn_mk, f3, x0]
            simp only [h1, h2, ↓reduceDIte, ↓reduceIte]
      dsimp only [evalQuad, c0, Lu, Lv, C]
      rw [Finset.sum_mul, Finset.sum_mul]
      have hpart : ∀ e : {p : Fin t × Fin t // p.1 < p.2},
          coef e * maskToInt (eM ((a, b), r)) e.val.1 * maskToInt (eM ((a, b), r)) e.val.2 =
          (if e = e0 then coef e * f3 a * f3 b else 0) +
          (if e ≠ e0 ∧ (e.val.1 = u ∨ e.val.2 = u) then coef e * (if e.val.1 = u then x0 e.val.2 else x0 e.val.1) * f3 a else 0) +
          (if e ≠ e0 ∧ (e.val.1 = v ∨ e.val.2 = v) then coef e * (if e.val.1 = v then x0 e.val.2 else x0 e.val.1) * f3 b else 0) +
          (if e.val.1 ≠ u ∧ e.val.2 ≠ u ∧ e.val.1 ≠ v ∧ e.val.2 ≠ v then coef e * x0 e.val.1 * x0 e.val.2 else 0) := by
        intro e
        rw [hx_eq e.val.1, hx_eq e.val.2]
        have hlt := e.2
        have hlt0 := e0.2
        by_cases he : e = e0
        · subst he; simp [u, v, huv, huv.symm]
        · have hnotuv : ¬ ((e.val.1 = u ∧ e.val.2 = v) ∨ (e.val.1 = v ∧ e.val.2 = u)) := by
            rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
            · exact he (Subtype.ext (Prod.ext h1 h2))
            · dsimp only [u, v] at h1 h2; omega
          by_cases h1u : e.val.1 = u
          · have h2u : e.val.2 ≠ u := ne_of_gt (h1u ▸ hlt)
            have h2v : e.val.2 ≠ v := fun h2v => hnotuv (Or.inl ⟨h1u, h2v⟩)
            have h1v : e.val.1 ≠ v := by rw [h1u]; exact huv
            simp only [ne_eq, eq_self_iff_true, he, h1u, h2u, h1v, h2v, huv, huv.symm,
              not_false_eq_true, not_true_eq_false, true_or, or_true, or_false, false_or,
              and_true, true_and, and_false, false_and, ↓reduceIte, add_zero, zero_add]
            ring
          · by_cases h2u : e.val.2 = u
            · have h1v : e.val.1 ≠ v := fun h1v => hnotuv (Or.inr ⟨h1v, h2u⟩)
              have h2v : e.val.2 ≠ v := by rw [h2u]; exact huv
              simp only [ne_eq, eq_self_iff_true, he, h1u, h2u, h1v, h2v, huv, huv.symm,
                not_false_eq_true, not_true_eq_false, true_or, or_true, or_false, false_or,
                and_true, true_and, and_false, false_and, ↓reduceIte, add_zero, zero_add]
            · by_cases h1v : e.val.1 = v
              · have h2v : e.val.2 ≠ v := ne_of_gt (h1v ▸ hlt)
                simp only [ne_eq, eq_self_iff_true, he, h1u, h2u, h1v, h2v, huv, huv.symm,
                  not_false_eq_true, not_true_eq_false, true_or, or_true, or_false, false_or,
                  and_true, true_and, and_false, false_and, ↓reduceIte, add_zero, zero_add]
                ring
              · by_cases h2v : e.val.2 = v
                · simp only [ne_eq, eq_self_iff_true, he, h1u, h2u, h1v, h2v, huv, huv.symm,
                    not_false_eq_true, not_true_eq_false, true_or, or_true, or_false, false_or,
                    and_true, true_and, and_false, false_and, ↓reduceIte, add_zero, zero_add]
                · simp only [ne_eq, eq_self_iff_true, he, h1u, h2u, h1v, h2v, huv, huv.symm,
                    not_false_eq_true, not_true_eq_false, true_or, or_true, or_false, false_or,
                    and_true, true_and, and_false, false_and, ↓reduceIte, add_zero, zero_add]
      rw [Finset.sum_congr rfl fun e _ => hpart e, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ e0, if_pos (Finset.mem_univ e0),
        ← Finset.sum_filter, ← Finset.sum_filter, ← Finset.sum_filter]
    have h4 : ∀ (c0 Lu Lv C : ℤ), c0 ≠ 0 →
        4 ≤ ((Finset.univ : Finset (Fin 3 × Fin 3)).filter
          (fun ab => c0 * f3 ab.1 * f3 ab.2 + Lu * f3 ab.1 + Lv * f3 ab.2 + C ≠ 0)).card := by
      intro c0 Lu Lv C hc0
      have ha_good : 2 ≤ ((Finset.univ : Finset (Fin 3)).filter (fun a => c0 * f3 a + Lv ≠ 0)).card := by
        have hbad : ((Finset.univ : Finset (Fin 3)).filter (fun a => c0 * f3 a + Lv = 0)).card ≤ 1 := by
          refine Finset.card_le_one.mpr fun a1 ha1 a2 ha2 => ?_
          have h1 := (Finset.mem_filter.mp ha1).2
          have h2 := (Finset.mem_filter.mp ha2).2
          have hfeq : f3 a1 = f3 a2 := mul_left_cancel₀ hc0 (by linarith)
          exact hf3_inj a1 a2 hfeq
        have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 3)))
          (p := fun a => c0 * f3 a + Lv = 0)
        rw [Finset.card_univ, Fintype.card_fin] at htot
        have hne_f : (Finset.univ.filter (fun a : Fin 3 => ¬ c0 * f3 a + Lv = 0)) =
            Finset.univ.filter (fun a : Fin 3 => c0 * f3 a + Lv ≠ 0) := rfl
        rw [hne_f] at htot
        omega
      have hb_good : ∀ a : Fin 3, c0 * f3 a + Lv ≠ 0 →
          2 ≤ ((Finset.univ : Finset (Fin 3)).filter
            (fun b => c0 * f3 a * f3 b + Lu * f3 a + Lv * f3 b + C ≠ 0)).card := by
        intro a ha
        have hbad : ((Finset.univ : Finset (Fin 3)).filter
            (fun b => c0 * f3 a * f3 b + Lu * f3 a + Lv * f3 b + C = 0)).card ≤ 1 := by
          refine Finset.card_le_one.mpr fun b1 hb1 b2 hb2 => ?_
          have h1 := (Finset.mem_filter.mp hb1).2
          have h2 := (Finset.mem_filter.mp hb2).2
          have hmul : (c0 * f3 a + Lv) * (f3 b1 - f3 b2) = 0 := by linarith
          have hfeq : f3 b1 = f3 b2 := sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left ha)
          exact hf3_inj b1 b2 hfeq
        have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 3)))
          (p := fun b => c0 * f3 a * f3 b + Lu * f3 a + Lv * f3 b + C = 0)
        rw [Finset.card_univ, Fintype.card_fin] at htot
        have hne_f : (Finset.univ.filter (fun b : Fin 3 => ¬ c0 * f3 a * f3 b + Lu * f3 a + Lv * f3 b + C = 0)) =
            Finset.univ.filter (fun b : Fin 3 => c0 * f3 a * f3 b + Lu * f3 a + Lv * f3 b + C ≠ 0) := rfl
        rw [hne_f] at htot
        omega
      rw [Finset.card_filter, Fintype.sum_prod_type]
      calc 4 ≤ ((Finset.univ : Finset (Fin 3)).filter (fun a => c0 * f3 a + Lv ≠ 0)).card * 2 := by omega
        _ = ∑ _a ∈ Finset.univ.filter (fun a : Fin 3 => c0 * f3 a + Lv ≠ 0), 2 := by
            rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ a ∈ Finset.univ.filter (fun a : Fin 3 => c0 * f3 a + Lv ≠ 0),
              ∑ b : Fin 3, (if c0 * f3 a * f3 b + Lu * f3 a + Lv * f3 b + C ≠ 0 then 1 else 0) :=
            Finset.sum_le_sum fun a ha => by
              rw [← Finset.card_filter]; exact hb_good a (Finset.mem_filter.mp ha).2
        _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, (if c0 * f3 a * f3 b + Lu * f3 a + Lv * f3 b + C ≠ 0 then 1 else 0) :=
            Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
    have hrew : (Finset.univ : Finset (Fin 3 × Fin 3)).filter (fun ab => evalQuad t coef (maskToInt (eM (ab, r))) ≠ 0) =
        (Finset.univ : Finset (Fin 3 × Fin 3)).filter (fun ab => c0 * f3 ab.1 * f3 ab.2 + Lu * f3 ab.1 + Lv * f3 ab.2 + C ≠ 0) := by
      ext ab; simp [hform ab]
    rw [hrew]; exact h4 c0 Lu Lv C he0
  rw [hbij]
  have hsum : 4 * Fintype.card (Z → Fin 3) ≤
      ∑ r : Z → Fin 3, ((Finset.univ : Finset (Fin 3 × Fin 3)).filter
        (fun ab => evalQuad t coef (maskToInt (eM (ab, r))) ≠ 0)).card := by
    calc 4 * Fintype.card (Z → Fin 3) = ∑ _r : Z → Fin 3, 4 := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun r _ => hfiber r
  nlinarith

set_option maxHeartbeats 1200000 in
private lemma nonsimple_nz_ge_37_81 (t : ℕ)
    (G H : Finset {p : Fin t × Fin t // p.1 < p.2}) (hne : G ≠ H)
    (hnonsimp : ¬ ∃ (c : ℤ) (i j : Fin t) (v w : Option (Fin t)),
      c ≠ 0 ∧ v ≠ some i ∧ w ≠ some j ∧
      Disjoint (insert i (v.elim (∅ : Finset (Fin t)) (fun x => {x})))
        (insert j (w.elim (∅ : Finset (Fin t)) (fun x => {x}))) ∧
      ∀ x : Fin t → ℤ, poly457 t G x - poly457 t H x =
        c * (x i - v.elim 0 x) * (x j - w.elim 0 x)) :
    37 * 3 ^ t ≤ 81 * ((Finset.univ : Finset (Fin t → Fin 3)).filter
      (fun p => poly457 t G (maskToInt p) ≠ poly457 t H (maskToInt p) ∨
        poly457 t G (maskToAbs p) ≠ poly457 t H (maskToAbs p))).card := by
  let coef : {p : Fin t × Fin t // p.1 < p.2} → ℤ := fun e =>
    (if e ∈ G then 1 else 0) - (if e ∈ H then 1 else 0)
  have hdiff_eq : ∀ x : Fin t → ℤ, poly457 t G x - poly457 t H x = evalQuad t coef x := by
    intro x
    dsimp only [poly457, evalQuad, coef]
    have h1 : ∑ e ∈ G, x e.val.1 * x e.val.2 =
        ∑ e : {p : Fin t × Fin t // p.1 < p.2}, if e ∈ G then x e.val.1 * x e.val.2 else 0 := by
      rw [← Finset.sum_filter]; congr 1; ext e; simp
    have h2 : ∑ e ∈ H, x e.val.1 * x e.val.2 =
        ∑ e : {p : Fin t × Fin t // p.1 < p.2}, if e ∈ H then x e.val.1 * x e.val.2 else 0 := by
      rw [← Finset.sum_filter]; congr 1; ext e; simp
    rw [h1, h2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases a : e ∈ G <;> by_cases b : e ∈ H <;> simp [a, b]
  have hex_e0 : ∃ e0, coef e0 ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hne; ext e
    have h0 := hall e
    dsimp only [coef] at h0
    by_cases h1 : e ∈ G <;> by_cases h2 : e ∈ H <;> simp_all
  rcases hex_e0 with ⟨e0, he0⟩
  let u := e0.val.1
  let v := e0.val.2
  have huv : u ≠ v := ne_of_lt e0.2
  let c0 : ℤ := coef e0
  have hc0_pm : c0 = 1 ∨ c0 = -1 := by
    dsimp only [c0, coef] at he0 ⊢
    by_cases h1 : e0 ∈ G <;> by_cases h2 : e0 ∈ H <;> simp_all
  have hc0_sq : c0 * c0 = 1 := by rcases hc0_pm with h | h <;> rw [h] <;> norm_num
  have hcoef_val : ∀ e, coef e = 0 ∨ coef e = 1 ∨ coef e = -1 := fun e => by
    dsimp only [coef]; by_cases h1 : e ∈ G <;> by_cases h2 : e ∈ H <;> simp [h1, h2]
  let Z : Type := {i : Fin t // i ≠ u ∧ i ≠ v}
  let aA : Fin t → ℤ := fun k =>
    if hk : k = u ∨ k = v then 0
    else -c0 * (∑ e ∈ Finset.univ.filter (fun e : {p : Fin t × Fin t // p.1 < p.2} =>
      (e.val.1 = v ∧ e.val.2 = k) ∨ (e.val.1 = k ∧ e.val.2 = v)), coef e)
  let aB : Fin t → ℤ := fun k =>
    if hk : k = u ∨ k = v then 0
    else -c0 * (∑ e ∈ Finset.univ.filter (fun e : {p : Fin t × Fin t // p.1 < p.2} =>
      (e.val.1 = u ∧ e.val.2 = k) ∨ (e.val.1 = k ∧ e.val.2 = u)), coef e)
  have haA_val : ∀ k, aA k = 0 ∨ aA k = 1 ∨ aA k = -1 := by
    intro k
    dsimp only [aA]
    split_ifs with hk
    · left; rfl
    · push_neg at hk
      by_cases hlt : v < k
      · let ek : {p : Fin t × Fin t // p.1 < p.2} := ⟨(v, k), hlt⟩
        have hfilt : Finset.univ.filter (fun e : {p : Fin t × Fin t // p.1 < p.2} =>
            (e.val.1 = v ∧ e.val.2 = k) ∨ (e.val.1 = k ∧ e.val.2 = v)) = {ek} := by
          ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
            · exact Subtype.ext (Prod.ext h1 h2)
            · have := e.2; omega
          · rintro rfl; left; exact ⟨rfl, rfl⟩
        rw [hfilt, Finset.sum_singleton]
        rcases hc0_pm with h1 | h1 <;> rcases hcoef_val ek with h2 | h2 | h2 <;> simp [h1, h2]
      · have hgt : k < v := lt_of_le_of_ne (not_lt.mp hlt) hk.2
        let ek : {p : Fin t × Fin t // p.1 < p.2} := ⟨(k, v), hgt⟩
        have hfilt : Finset.univ.filter (fun e : {p : Fin t × Fin t // p.1 < p.2} =>
            (e.val.1 = v ∧ e.val.2 = k) ∨ (e.val.1 = k ∧ e.val.2 = v)) = {ek} := by
          ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
            · have := e.2; omega
            · exact Subtype.ext (Prod.ext h1 h2)
          · rintro rfl; right; exact ⟨rfl, rfl⟩
        rw [hfilt, Finset.sum_singleton]
        rcases hc0_pm with h1 | h1 <;> rcases hcoef_val ek with h2 | h2 | h2 <;> simp [h1, h2]
  have haB_val : ∀ k, aB k = 0 ∨ aB k = 1 ∨ aB k = -1 := by
    intro k
    dsimp only [aB]
    split_ifs with hk
    · left; rfl
    · push_neg at hk
      by_cases hlt : u < k
      · let ek : {p : Fin t × Fin t // p.1 < p.2} := ⟨(u, k), hlt⟩
        have hfilt : Finset.univ.filter (fun e : {p : Fin t × Fin t // p.1 < p.2} =>
            (e.val.1 = u ∧ e.val.2 = k) ∨ (e.val.1 = k ∧ e.val.2 = u)) = {ek} := by
          ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
            · exact Subtype.ext (Prod.ext h1 h2)
            · have := e.2; omega
          · rintro rfl; left; exact ⟨rfl, rfl⟩
        rw [hfilt, Finset.sum_singleton]
        rcases hc0_pm with h1 | h1 <;> rcases hcoef_val ek with h2 | h2 | h2 <;> simp [h1, h2]
      · have hgt : k < u := lt_of_le_of_ne (not_lt.mp hlt) hk.1
        let ek : {p : Fin t × Fin t // p.1 < p.2} := ⟨(k, u), hgt⟩
        have hfilt : Finset.univ.filter (fun e : {p : Fin t × Fin t // p.1 < p.2} =>
            (e.val.1 = u ∧ e.val.2 = k) ∨ (e.val.1 = k ∧ e.val.2 = u)) = {ek} := by
          ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
            · have := e.2; omega
            · exact Subtype.ext (Prod.ext h1 h2)
          · rintro rfl; right; exact ⟨rfl, rfl⟩
        rw [hfilt, Finset.sum_singleton]
        rcases hc0_pm with h1 | h1 <;> rcases hcoef_val ek with h2 | h2 | h2 <;> simp [h1, h2]
  let Aval : (Fin t → ℤ) → ℤ := fun x => ∑ k : Fin t, aA k * x k
  let Bval : (Fin t → ℤ) → ℤ := fun x => ∑ k : Fin t, aB k * x k
  let Rval : (Fin t → ℤ) → ℤ := fun x =>
    ∑ e ∈ Finset.univ.filter (fun e : {p : Fin t × Fin t // p.1 < p.2} =>
      e.val.1 ≠ u ∧ e.val.2 ≠ u ∧ e.val.1 ≠ v ∧ e.val.2 ≠ v), coef e * x e.val.1 * x e.val.2
  let Dval : (Fin t → ℤ) → ℤ := fun x => Rval x - c0 * Aval x * Bval x
  have hQ_decomp : ∀ x : Fin t → ℤ,
      evalQuad t coef x = c0 * (x u - Aval x) * (x v - Bval x) + Dval x := by
    intro x
    have hLu : -c0 * Bval x * x u =
        ∑ e ∈ Finset.univ.filter (fun e : {p : Fin t × Fin t // p.1 < p.2} => e ≠ e0 ∧ (e.val.1 = u ∨ e.val.2 = u)),
          coef e * x e.val.1 * x e.val.2 := by
      dsimp only [Bval, aB]
      rw [Finset.mul_sum, Finset.sum_mul]
      have hterm : ∀ k : Fin t,
          -c0 * ((if _hk : k = u ∨ k = v then 0 else
            -c0 * ∑ e ∈ Finset.univ.filter (fun e : {p : Fin t × Fin t // p.1 < p.2} =>
              (e.val.1 = u ∧ e.val.2 = k) ∨ (e.val.1 = k ∧ e.val.2 = u)), coef e) * x k) * x u =
          ∑ e ∈ Finset.univ.filter (fun e : {p : Fin t × Fin t // p.1 < p.2} =>
              e ≠ e0 ∧ ((e.val.1 = u ∧ e.val.2 = k) ∨ (e.val.1 = k ∧ e.val.2 = u))),
            coef e * x e.val.1 * x e.val.2 := by
        intro k
        by_cases hk : k = u ∨ k = v
        · rw [dif_pos hk, zero_mul, mul_zero, zero_mul]
          symm; refine Finset.sum_eq_zero fun e he => ?_
          rcases (Finset.mem_filter.mp he).2 with ⟨hne0, h1 | h2⟩
          · rcases hk with rfl | rfl
            · exact (ne_of_lt e.2 (h1.1.trans h1.2.symm)).elim
            · exact (hne0 (Subtype.ext (Prod.ext h1.1 h1.2))).elim
          · rcases hk with rfl | rfl
            · exact (ne_of_lt e.2 (h2.1.trans h2.2.symm)).elim
            · have := e.2; have := e0.2; dsimp only [u, v] at h2; omega
        · rw [dif_neg hk]
          have hfilt_eq : Finset.univ.filter (fun e : {p : Fin t × Fin t // p.1 < p.2} =>
              e ≠ e0 ∧ ((e.val.1 = u ∧ e.val.2 = k) ∨ (e.val.1 = k ∧ e.val.2 = u))) =
            Finset.univ.filter (fun e : {p : Fin t × Fin t // p.1 < p.2} =>
              (e.val.1 = u ∧ e.val.2 = k) ∨ (e.val.1 = k ∧ e.val.2 = u)) := by
            ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
            rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) rfl
            · exact hk (Or.inr h2.symm)
            · exact hk (Or.inl h1.symm)
          rw [hfilt_eq]
          calc -c0 * (-c0 * (∑ e ∈ _, coef e) * x k) * x u
              = (c0 * c0) * ((∑ e ∈ _, coef e) * (x u * x k)) := by ring
            _ = (∑ e ∈ _, coef e) * (x u * x k) := by rw [hc0_sq, one_mul]
            _ = ∑ e ∈ _, coef e * (x u * x k) := Finset.sum_mul _ _ _
            _ = ∑ e ∈ _, coef e * x e.val.1 * x e.val.2 :=
                Finset.sum_congr rfl fun e he => by
                  rcases (Finset.mem_filter.mp he).2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
                  · rw [h1, h2]; ring
                  · rw [h1, h2]; ring
      rw [Finset.sum_congr rfl fun k _ => hterm k]
      rw [← Finset.sum_biUnion]
      · refine Finset.sum_congr ?_ fun _ _ => rfl
        ext e; simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
        constructor
        · rintro ⟨k, hne0, ⟨h1, _⟩ | ⟨_, h2⟩⟩
          · exact ⟨hne0, Or.inl h1⟩
          · exact ⟨hne0, Or.inr h2⟩
        · rintro ⟨hne0, h1 | h2⟩
          · exact ⟨e.val.2, hne0, Or.inl ⟨h1, rfl⟩⟩
          · exact ⟨e.val.1, hne0, Or.inr ⟨rfl, h2⟩⟩
      · intro k1 _ k2 _ hne12
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]; intro e h1 h2
        rcases (Finset.mem_filter.mp h1).2.2 with ⟨ha1, hb1⟩ | ⟨ha1, hb1⟩ <;>
        rcases (Finset.mem_filter.mp h2).2.2 with ⟨ha2, hb2⟩ | ⟨ha2, hb2⟩
        · exact hne12 (hb1.symm.trans hb2)
        · exact ne_of_lt e.2 (ha1.trans hb2.symm)
        · exact ne_of_lt e.2 (ha2.trans hb1.symm)
        · exact hne12 (ha1.symm.trans ha2)
    have hLv : -c0 * Aval x * x v =
        ∑ e ∈ Finset.univ.filter (fun e : {p : Fin t × Fin t // p.1 < p.2} => e ≠ e0 ∧ (e.val.1 = v ∨ e.val.2 = v)),
          coef e * x e.val.1 * x e.val.2 := by
      dsimp only [Aval, aA]
      rw [Finset.mul_sum, Finset.sum_mul]
      have hterm : ∀ k : Fin t,
          -c0 * ((if _hk : k = u ∨ k = v then 0 else
            -c0 * ∑ e ∈ Finset.univ.filter (fun e : {p : Fin t × Fin t // p.1 < p.2} =>
              (e.val.1 = v ∧ e.val.2 = k) ∨ (e.val.1 = k ∧ e.val.2 = v)), coef e) * x k) * x v =
          ∑ e ∈ Finset.univ.filter (fun e : {p : Fin t × Fin t // p.1 < p.2} =>
              e ≠ e0 ∧ ((e.val.1 = v ∧ e.val.2 = k) ∨ (e.val.1 = k ∧ e.val.2 = v))),
            coef e * x e.val.1 * x e.val.2 := by
        intro k
        by_cases hk : k = u ∨ k = v
        · rw [dif_pos hk, zero_mul, mul_zero, zero_mul]
          symm; refine Finset.sum_eq_zero fun e he => ?_
          rcases (Finset.mem_filter.mp he).2 with ⟨hne0, h1 | h2⟩
          · rcases hk with rfl | rfl
            · have := e.2; have := e0.2; dsimp only [u, v] at h1; omega
            · exact (ne_of_lt e.2 (h1.1.trans h1.2.symm)).elim
          · rcases hk with rfl | rfl
            · exact (hne0 (Subtype.ext (Prod.ext h2.1 h2.2))).elim
            · exact (ne_of_lt e.2 (h2.1.trans h2.2.symm)).elim
        · rw [dif_neg hk]
          have hfilt_eq : Finset.univ.filter (fun e : {p : Fin t × Fin t // p.1 < p.2} =>
              e ≠ e0 ∧ ((e.val.1 = v ∧ e.val.2 = k) ∨ (e.val.1 = k ∧ e.val.2 = v))) =
            Finset.univ.filter (fun e : {p : Fin t × Fin t // p.1 < p.2} =>
              (e.val.1 = v ∧ e.val.2 = k) ∨ (e.val.1 = k ∧ e.val.2 = v)) := by
            ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
            rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) rfl
            · exact hk (Or.inr h2.symm)
            · exact hk (Or.inl h1.symm)
          rw [hfilt_eq]
          calc -c0 * (-c0 * (∑ e ∈ _, coef e) * x k) * x v
              = (c0 * c0) * ((∑ e ∈ _, coef e) * (x v * x k)) := by ring
            _ = (∑ e ∈ _, coef e) * (x v * x k) := by rw [hc0_sq, one_mul]
            _ = ∑ e ∈ _, coef e * (x v * x k) := Finset.sum_mul _ _ _
            _ = ∑ e ∈ _, coef e * x e.val.1 * x e.val.2 :=
                Finset.sum_congr rfl fun e he => by
                  rcases (Finset.mem_filter.mp he).2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
                  · rw [h1, h2]; ring
                  · rw [h1, h2]; ring
      rw [Finset.sum_congr rfl fun k _ => hterm k]
      rw [← Finset.sum_biUnion]
      · refine Finset.sum_congr ?_ fun _ _ => rfl
        ext e; simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
        constructor
        · rintro ⟨k, hne0, ⟨h1, _⟩ | ⟨_, h2⟩⟩
          · exact ⟨hne0, Or.inl h1⟩
          · exact ⟨hne0, Or.inr h2⟩
        · rintro ⟨hne0, h1 | h2⟩
          · exact ⟨e.val.2, hne0, Or.inl ⟨h1, rfl⟩⟩
          · exact ⟨e.val.1, hne0, Or.inr ⟨rfl, h2⟩⟩
      · intro k1 _ k2 _ hne12
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]; intro e h1 h2
        rcases (Finset.mem_filter.mp h1).2.2 with ⟨ha1, hb1⟩ | ⟨ha1, hb1⟩ <;>
        rcases (Finset.mem_filter.mp h2).2.2 with ⟨ha2, hb2⟩ | ⟨ha2, hb2⟩
        · exact hne12 (hb1.symm.trans hb2)
        · exact ne_of_lt e.2 (ha1.trans hb2.symm)
        · exact ne_of_lt e.2 (ha2.trans hb1.symm)
        · exact hne12 (ha1.symm.trans ha2)
    have hsplit : evalQuad t coef x =
        c0 * x u * x v + (-c0 * Bval x * x u) + (-c0 * Aval x * x v) + Rval x := by
      rw [hLu, hLv]
      dsimp only [evalQuad, c0, Rval]
      have hpart : ∀ e : {p : Fin t × Fin t // p.1 < p.2},
          coef e * x e.val.1 * x e.val.2 =
          (if e = e0 then coef e * x u * x v else 0) +
          (if e ≠ e0 ∧ (e.val.1 = u ∨ e.val.2 = u) then coef e * x e.val.1 * x e.val.2 else 0) +
          (if e ≠ e0 ∧ (e.val.1 = v ∨ e.val.2 = v) then coef e * x e.val.1 * x e.val.2 else 0) +
          (if e.val.1 ≠ u ∧ e.val.2 ≠ u ∧ e.val.1 ≠ v ∧ e.val.2 ≠ v then coef e * x e.val.1 * x e.val.2 else 0) := by
        intro e
        have hlt := e.2; have hlt0 := e0.2
        by_cases he : e = e0
        · subst he; simp [u, v]
        · have hnotuv : ¬ ((e.val.1 = u ∧ e.val.2 = v) ∨ (e.val.1 = v ∧ e.val.2 = u)) := by
            rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
            · exact he (Subtype.ext (Prod.ext h1 h2))
            · dsimp only [u, v] at h1 h2; omega
          by_cases h1u : e.val.1 = u
          · have h2v : e.val.2 ≠ v := fun h2v => hnotuv (Or.inl ⟨h1u, h2v⟩)
            have h1v : e.val.1 ≠ v := by rw [h1u]; exact huv
            simp [he, h1u, h1v, h2v, huv, huv.symm]
          · by_cases h2u : e.val.2 = u
            · have h1v : e.val.1 ≠ v := fun h1v => hnotuv (Or.inr ⟨h1v, h2u⟩)
              have h2v : e.val.2 ≠ v := by rw [h2u]; exact huv
              simp [he, h1u, h2u, h1v, h2v, huv, huv.symm]
            · by_cases h1v : e.val.1 = v
              · simp [he, h1u, h2u, h1v, huv, huv.symm]
              · by_cases h2v : e.val.2 = v
                · simp [he, h1u, h2u, h1v, h2v, huv, huv.symm]
                · simp [he, h1u, h2u, h1v, h2v, huv, huv.symm]
      rw [Finset.sum_congr rfl fun e _ => hpart e, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ e0, if_pos (Finset.mem_univ e0),
        ← Finset.sum_filter, ← Finset.sum_filter, ← Finset.sum_filter]
    dsimp only [Dval]; linarith
  let eM : ((Fin 3 × Fin 3) × (Z → Fin 3)) ≃ (Fin t → Fin 3) :=
    { toFun := fun q i =>
        if hi1 : i = u then q.1.1
        else if hi2 : i = v then q.1.2
        else q.2 ⟨i, hi1, hi2⟩
      invFun := fun p => ((p u, p v), fun z => p z.1)
      left_inv := fun ⟨⟨a, b⟩, r⟩ => by
        refine Prod.ext (Prod.ext ?_ ?_) ?_
        · simp
        · simp [huv.symm]
        · funext ⟨i, hi1, hi2⟩; simp [hi1, hi2]
      right_inv := fun p => by
        funext i; by_cases h1 : i = u
        · subst h1; simp
        · by_cases h2 : i = v
          · subst h2; simp [h1]
          · simp [h1, h2] }
  have hcardZ : Fintype.card (Z → Fin 3) * 9 = 3 ^ t := by
    have hcard : Fintype.card Z = t - 2 := by
      have h1 : Fintype.card Z = ((Finset.univ.erase u).erase v).card := by
        rw [Fintype.card_subtype]; congr 1; ext i; simp [and_comm]
      have hv_mem : v ∈ (Finset.univ : Finset (Fin t)).erase u := Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_univ _⟩
      rw [h1, Finset.card_erase_of_mem hv_mem, Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, Fintype.card_fin]
      omega
    rw [Fintype.card_fun, Fintype.card_fin, hcard]
    have ht2 : 2 ≤ t := by have := e0.2; omega
    calc 3 ^ (t - 2) * 9 = 3 ^ (t - 2) * 3 ^ 2 := by norm_num
      _ = 3 ^ (t - 2 + 2) := (pow_add 3 _ 2).symm
      _ = 3 ^ t := by congr 1; omega
  let f3 : Fin 3 → ℤ := fun a => if a = 0 then 0 else if a = 1 then 1 else -1
  let g3 : Fin 3 → ℤ := fun a => if a = 0 then 0 else 1
  have hf3_inj : ∀ a1 a2 : Fin 3, f3 a1 = f3 a2 → a1 = a2 := fun a1 a2 h => by
    fin_cases a1 <;> fin_cases a2 <;> simp [f3] at h ⊢
  have hcard_ge2 : ∀ P : Fin 3 → ℤ,
      ((Finset.univ : Finset (Fin 3)).filter (fun x => P x = 0)).card ≤ 1 →
      2 ≤ ((Finset.univ : Finset (Fin 3)).filter (fun x => P x ≠ 0)).card := by
    intro P hle
    have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 3))) (p := fun x => P x = 0)
    rw [Finset.card_univ, Fintype.card_fin] at htot
    have hne_f : Finset.univ.filter (fun x : Fin 3 => ¬ P x = 0) = Finset.univ.filter (fun x : Fin 3 => P x ≠ 0) := rfl
    rw [hne_f] at htot; omega
  have hA_indep : ∀ (r : Z → Fin 3) (ab : Fin 3 × Fin 3),
      Aval (maskToInt (eM (ab, r))) = Aval (maskToInt (eM ((0, 0), r))) ∧
      Aval (maskToAbs (eM (ab, r))) = Aval (maskToAbs (eM ((0, 0), r))) := by
    intro r ab
    constructor <;> (refine Finset.sum_congr rfl fun k _ => ?_; by_cases hk : k = u ∨ k = v)
    · dsimp only [aA]; rw [dif_pos hk, zero_mul, zero_mul]
    · push_neg at hk; dsimp only [maskToInt, eM, Equiv.coe_fn_mk]; simp [hk.1, hk.2]
    · dsimp only [aA]; rw [dif_pos hk, zero_mul, zero_mul]
    · push_neg at hk; dsimp only [maskToAbs, eM, Equiv.coe_fn_mk]; simp [hk.1, hk.2]
  have hB_indep : ∀ (r : Z → Fin 3) (ab : Fin 3 × Fin 3),
      Bval (maskToInt (eM (ab, r))) = Bval (maskToInt (eM ((0, 0), r))) ∧
      Bval (maskToAbs (eM (ab, r))) = Bval (maskToAbs (eM ((0, 0), r))) := by
    intro r ab
    constructor <;> (refine Finset.sum_congr rfl fun k _ => ?_; by_cases hk : k = u ∨ k = v)
    · dsimp only [aB]; rw [dif_pos hk, zero_mul, zero_mul]
    · push_neg at hk; dsimp only [maskToInt, eM, Equiv.coe_fn_mk]; simp [hk.1, hk.2]
    · dsimp only [aB]; rw [dif_pos hk, zero_mul, zero_mul]
    · push_neg at hk; dsimp only [maskToAbs, eM, Equiv.coe_fn_mk]; simp [hk.1, hk.2]
  have hR_indep : ∀ (r : Z → Fin 3) (ab : Fin 3 × Fin 3),
      Rval (maskToInt (eM (ab, r))) = Rval (maskToInt (eM ((0, 0), r))) ∧
      Rval (maskToAbs (eM (ab, r))) = Rval (maskToAbs (eM ((0, 0), r))) := by
    intro r ab
    constructor <;> refine Finset.sum_congr rfl fun e he => ?_
    · rcases (Finset.mem_filter.mp he).2 with ⟨h1, h2, h3, h4⟩
      dsimp only [maskToInt, eM, Equiv.coe_fn_mk]; simp [h1, h2, h3, h4]
    · rcases (Finset.mem_filter.mp he).2 with ⟨h1, h2, h3, h4⟩
      dsimp only [maskToAbs, eM, Equiv.coe_fn_mk]; simp [h1, h2, h3, h4]
  have hD_indep : ∀ (r : Z → Fin 3) (ab : Fin 3 × Fin 3),
      Dval (maskToInt (eM (ab, r))) = Dval (maskToInt (eM ((0, 0), r))) ∧
      Dval (maskToAbs (eM (ab, r))) = Dval (maskToAbs (eM ((0, 0), r))) := fun r ab =>
    ⟨by dsimp only [Dval]; rw [(hR_indep r ab).1, (hA_indep r ab).1, (hB_indep r ab).1],
     by dsimp only [Dval]; rw [(hR_indep r ab).2, (hA_indep r ab).2, (hB_indep r ab).2]⟩
  let cnt : (Z → Fin 3) → ℕ := fun r =>
    ((Finset.univ : Finset (Fin 3 × Fin 3)).filter
      (fun ab => evalQuad t coef (maskToInt (eM (ab, r))) ≠ 0 ∨
        evalQuad t coef (maskToAbs (eM (ab, r))) ≠ 0)).card
  have htot_eq : ((Finset.univ : Finset (Fin t → Fin 3)).filter
      (fun p => poly457 t G (maskToInt p) ≠ poly457 t H (maskToInt p) ∨
        poly457 t G (maskToAbs p) ≠ poly457 t H (maskToAbs p))).card = ∑ r : Z → Fin 3, cnt r := by
    have hrew : (Finset.univ : Finset (Fin t → Fin 3)).filter
        (fun p => poly457 t G (maskToInt p) ≠ poly457 t H (maskToInt p) ∨
          poly457 t G (maskToAbs p) ≠ poly457 t H (maskToAbs p)) =
        (Finset.univ : Finset (Fin t → Fin 3)).filter
          (fun p => evalQuad t coef (maskToInt p) ≠ 0 ∨ evalQuad t coef (maskToAbs p) ≠ 0) := by
      ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← hdiff_eq, sub_ne_zero]
    rw [hrew, Finset.card_filter]
    rw [← Fintype.sum_equiv eM
      (fun q => if evalQuad t coef (maskToInt (eM q)) ≠ 0 ∨ evalQuad t coef (maskToAbs (eM q)) ≠ 0 then 1 else 0)
      (fun p => if evalQuad t coef (maskToInt p) ≠ 0 ∨ evalQuad t coef (maskToAbs p) ≠ 0 then 1 else 0)
      (fun _ => rfl)]
    rw [Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun r _ => (Finset.card_filter _ _).symm
  have hcnt_4 : ∀ r : Z → Fin 3, 4 ≤ cnt r := by
    intro r
    let A0 := Aval (maskToInt (eM ((0, 0), r)))
    let B0 := Bval (maskToInt (eM ((0, 0), r)))
    let D0 := Dval (maskToInt (eM ((0, 0), r)))
    have h4 : 4 ≤ ((Finset.univ : Finset (Fin 3 × Fin 3)).filter
        (fun ab => c0 * (f3 ab.1 - A0) * (f3 ab.2 - B0) + D0 ≠ 0)).card := by
      have ha_good : 2 ≤ ((Finset.univ : Finset (Fin 3)).filter (fun a => f3 a - A0 ≠ 0)).card :=
        hcard_ge2 (fun a => f3 a - A0) (Finset.card_le_one.mpr fun a1 ha1 a2 ha2 =>
          hf3_inj a1 a2 (by linarith [(Finset.mem_filter.mp ha1).2, (Finset.mem_filter.mp ha2).2]))
      have hb_good : ∀ a : Fin 3, f3 a - A0 ≠ 0 →
          2 ≤ ((Finset.univ : Finset (Fin 3)).filter (fun b => c0 * (f3 a - A0) * (f3 b - B0) + D0 ≠ 0)).card := by
        intro a ha
        refine hcard_ge2 (fun b => c0 * (f3 a - A0) * (f3 b - B0) + D0) (Finset.card_le_one.mpr fun b1 hb1 b2 hb2 => ?_)
        have h1 := (Finset.mem_filter.mp hb1).2
        have h2 := (Finset.mem_filter.mp hb2).2
        have hmul : c0 * (f3 a - A0) * (f3 b1 - f3 b2) = 0 := by linarith
        exact hf3_inj b1 b2 (sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left (mul_ne_zero he0 ha)))
      rw [Finset.card_filter, Fintype.sum_prod_type]
      calc 4 ≤ ((Finset.univ : Finset (Fin 3)).filter (fun a => f3 a - A0 ≠ 0)).card * 2 := by omega
        _ = ∑ _a ∈ Finset.univ.filter (fun a : Fin 3 => f3 a - A0 ≠ 0), 2 := by
            rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ a ∈ Finset.univ.filter (fun a : Fin 3 => f3 a - A0 ≠ 0),
              ∑ b : Fin 3, (if c0 * (f3 a - A0) * (f3 b - B0) + D0 ≠ 0 then 1 else 0) :=
            Finset.sum_le_sum fun a ha => by rw [← Finset.card_filter]; exact hb_good a (Finset.mem_filter.mp ha).2
        _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, (if c0 * (f3 a - A0) * (f3 b - B0) + D0 ≠ 0 then 1 else 0) :=
            Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
    refine h4.trans (Finset.card_le_card fun ab hab => ?_)
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ?_⟩
    rw [hQ_decomp, (hA_indep r ab).1, (hB_indep r ab).1, (hD_indep r ab).1]
    have hu_eq : maskToInt (eM (ab, r)) u = f3 ab.1 := by dsimp only [maskToInt, eM, Equiv.coe_fn_mk, f3]; simp
    have hv_eq : maskToInt (eM (ab, r)) v = f3 ab.2 := by dsimp only [maskToInt, eM, Equiv.coe_fn_mk, f3]; simp [huv.symm]
    rw [hu_eq, hv_eq]
    exact (Finset.mem_filter.mp hab).2
  have hcnt_5 : ∀ r : Z → Fin 3,
      (2 ≤ |Aval (maskToInt (eM ((0, 0), r)))| ∨ 2 ≤ |Bval (maskToInt (eM ((0, 0), r)))| ∨
        Dval (maskToInt (eM ((0, 0), r))) ≠ 0) → 5 ≤ cnt r := by
    intro r hcond
    let A0 := Aval (maskToInt (eM ((0, 0), r)))
    let B0 := Bval (maskToInt (eM ((0, 0), r)))
    let D0 := Dval (maskToInt (eM ((0, 0), r)))
    have hsub : ((Finset.univ : Finset (Fin 3 × Fin 3)).filter
        (fun ab => c0 * (f3 ab.1 - A0) * (f3 ab.2 - B0) + D0 ≠ 0)).card ≤ cnt r := by
      refine Finset.card_le_card fun ab hab => Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ?_⟩
      rw [hQ_decomp, (hA_indep r ab).1, (hB_indep r ab).1, (hD_indep r ab).1]
      have hu_eq : maskToInt (eM (ab, r)) u = f3 ab.1 := by dsimp only [maskToInt, eM, Equiv.coe_fn_mk, f3]; simp
      have hv_eq : maskToInt (eM (ab, r)) v = f3 ab.2 := by dsimp only [maskToInt, eM, Equiv.coe_fn_mk, f3]; simp [huv.symm]
      rw [hu_eq, hv_eq]; exact (Finset.mem_filter.mp hab).2
    refine le_trans ?_ hsub
    have hbd_f3 : ∀ a : Fin 3, |f3 a| ≤ 1 := fun a => by fin_cases a <;> decide
    rcases hcond with hA2 | hB2 | hD0
    · have ha_all : ∀ a : Fin 3, f3 a - A0 ≠ 0 := fun a h => by
        have h1 := hbd_f3 a; have h2 : f3 a = A0 := by linarith
        rw [h2] at h1; dsimp only [A0] at h1; omega
      have hb_good : ∀ a : Fin 3,
          2 ≤ ((Finset.univ : Finset (Fin 3)).filter (fun b => c0 * (f3 a - A0) * (f3 b - B0) + D0 ≠ 0)).card := by
        intro a
        refine hcard_ge2 (fun b => c0 * (f3 a - A0) * (f3 b - B0) + D0) (Finset.card_le_one.mpr fun b1 hb1 b2 hb2 => ?_)
        have h1 := (Finset.mem_filter.mp hb1).2; have h2 := (Finset.mem_filter.mp hb2).2
        have hmul : c0 * (f3 a - A0) * (f3 b1 - f3 b2) = 0 := by linarith
        exact hf3_inj b1 b2 (sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left (mul_ne_zero he0 (ha_all a))))
      rw [Finset.card_filter, Fintype.sum_prod_type]
      calc 5 ≤ ∑ _a : Fin 3, 2 := by simp
        _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, (if c0 * (f3 a - A0) * (f3 b - B0) + D0 ≠ 0 then 1 else 0) :=
            Finset.sum_le_sum fun a _ => by rw [← Finset.card_filter]; exact hb_good a
    · have hb_all : ∀ b : Fin 3, f3 b - B0 ≠ 0 := fun b h => by
        have h1 := hbd_f3 b; have h2 : f3 b = B0 := by linarith
        rw [h2] at h1; dsimp only [B0] at h1; omega
      have ha_good : ∀ b : Fin 3,
          2 ≤ ((Finset.univ : Finset (Fin 3)).filter (fun a => c0 * (f3 a - A0) * (f3 b - B0) + D0 ≠ 0)).card := by
        intro b
        refine hcard_ge2 (fun a => c0 * (f3 a - A0) * (f3 b - B0) + D0) (Finset.card_le_one.mpr fun a1 ha1 a2 ha2 => ?_)
        have h1 := (Finset.mem_filter.mp ha1).2; have h2 := (Finset.mem_filter.mp ha2).2
        have hmul : c0 * (f3 b - B0) * (f3 a1 - f3 a2) = 0 := by linarith
        exact hf3_inj a1 a2 (sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left (mul_ne_zero he0 (hb_all b))))
      rw [Finset.card_filter, Fintype.sum_prod_type_right]
      calc 5 ≤ ∑ _b : Fin 3, 2 := by simp
        _ ≤ ∑ b : Fin 3, ∑ a : Fin 3, (if c0 * (f3 a - A0) * (f3 b - B0) + D0 ≠ 0 then 1 else 0) :=
            Finset.sum_le_sum fun b _ => by rw [← Finset.card_filter]; exact ha_good b
    · by_cases hA1 : ∃ a0 : Fin 3, f3 a0 = A0
      · by_cases hB1 : ∃ b0 : Fin 3, f3 b0 = B0
        · rcases hA1 with ⟨a0, ha0⟩; rcases hB1 with ⟨b0, hb0⟩
          let cross := (Finset.univ : Finset (Fin 3 × Fin 3)).filter (fun ab => ab.1 = a0 ∨ ab.2 = b0)
          have hcross_card : cross.card = 5 := by
            dsimp only [cross]
            fin_cases a0 <;> fin_cases b0 <;> decide
          rw [← hcross_card]
          refine Finset.card_le_card fun ab hab => ?_
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rcases (Finset.mem_filter.mp hab).2 with rfl | rfl
          · rw [ha0, sub_self, mul_zero, zero_mul, zero_add]; exact hD0
          · rw [hb0, sub_self, mul_zero, zero_add]; exact hD0
        · push_neg at hB1
          have hb_all : ∀ b : Fin 3, f3 b - B0 ≠ 0 := fun b h => hB1 b (sub_eq_zero.mp h)
          have ha_good : ∀ b : Fin 3,
              2 ≤ ((Finset.univ : Finset (Fin 3)).filter (fun a => c0 * (f3 a - A0) * (f3 b - B0) + D0 ≠ 0)).card := by
            intro b
            refine hcard_ge2 (fun a => c0 * (f3 a - A0) * (f3 b - B0) + D0) (Finset.card_le_one.mpr fun a1 ha1 a2 ha2 => ?_)
            have h1 := (Finset.mem_filter.mp ha1).2; have h2 := (Finset.mem_filter.mp ha2).2
            have hmul : c0 * (f3 b - B0) * (f3 a1 - f3 a2) = 0 := by linarith
            exact hf3_inj a1 a2 (sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left (mul_ne_zero he0 (hb_all b))))
          rw [Finset.card_filter, Fintype.sum_prod_type_right]
          calc 5 ≤ ∑ _b : Fin 3, 2 := by simp
            _ ≤ ∑ b : Fin 3, ∑ a : Fin 3, (if c0 * (f3 a - A0) * (f3 b - B0) + D0 ≠ 0 then 1 else 0) :=
                Finset.sum_le_sum fun b _ => by rw [← Finset.card_filter]; exact ha_good b
      · push_neg at hA1
        have ha_all : ∀ a : Fin 3, f3 a - A0 ≠ 0 := fun a h => hA1 a (sub_eq_zero.mp h)
        have hb_good : ∀ a : Fin 3,
            2 ≤ ((Finset.univ : Finset (Fin 3)).filter (fun b => c0 * (f3 a - A0) * (f3 b - B0) + D0 ≠ 0)).card := by
          intro a
          refine hcard_ge2 (fun b => c0 * (f3 a - A0) * (f3 b - B0) + D0) (Finset.card_le_one.mpr fun b1 hb1 b2 hb2 => ?_)
          have h1 := (Finset.mem_filter.mp hb1).2; have h2 := (Finset.mem_filter.mp hb2).2
          have hmul : c0 * (f3 a - A0) * (f3 b1 - f3 b2) = 0 := by linarith
          exact hf3_inj b1 b2 (sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left (mul_ne_zero he0 (ha_all a))))
        rw [Finset.card_filter, Fintype.sum_prod_type]
        calc 5 ≤ ∑ _a : Fin 3, 2 := by simp
          _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, (if c0 * (f3 a - A0) * (f3 b - B0) + D0 ≠ 0 then 1 else 0) :=
              Finset.sum_le_sum fun a _ => by rw [← Finset.card_filter]; exact hb_good a
  have hgoal_of_bonus : (Fintype.card (Z → Fin 3) ≤ 9 * ((Finset.univ : Finset (Z → Fin 3)).filter (fun r => 5 ≤ cnt r)).card) →
      37 * 3 ^ t ≤ 81 * ∑ r : Z → Fin 3, cnt r := by
    intro hbon
    let S5 := (Finset.univ : Finset (Z → Fin 3)).filter (fun r => 5 ≤ cnt r)
    have hsum_lb : 4 * Fintype.card (Z → Fin 3) + S5.card ≤ ∑ r : Z → Fin 3, cnt r := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun r => 5 ≤ cnt r)]
      have h1 : 5 * S5.card ≤ ∑ r ∈ S5, cnt r := by
        calc 5 * S5.card = ∑ _r ∈ S5, 5 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
          _ ≤ ∑ r ∈ S5, cnt r := Finset.sum_le_sum fun r hr => (Finset.mem_filter.mp hr).2
      have h2 : 4 * (Finset.univ.filter (fun r => ¬ 5 ≤ cnt r)).card ≤
          ∑ r ∈ Finset.univ.filter (fun r => ¬ 5 ≤ cnt r), cnt r := by
        calc 4 * _ = ∑ _r ∈ _, 4 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
          _ ≤ _ := Finset.sum_le_sum fun r _ => hcnt_4 r
      have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Z → Fin 3)))
        (p := fun r => 5 ≤ cnt r)
      rw [Finset.card_univ] at htot
      dsimp only [S5] at h1 htot ⊢
      omega
    dsimp only [S5] at hsum_lb
    nlinarith [hcardZ]
  rw [htot_eq]
  apply hgoal_of_bonus
  let suppA := Finset.univ.filter (fun k : Fin t => aA k ≠ 0)
  let suppB := Finset.univ.filter (fun k : Fin t => aB k ≠ 0)
  have htwo_lin : ∀ (lin : Fin t → ℤ),
      (∀ k, lin k = 0 ∨ lin k = 1 ∨ lin k = -1) →
      lin u = 0 → lin v = 0 →
      2 ≤ (Finset.univ.filter (fun k : Fin t => lin k ≠ 0)).card →
      Fintype.card (Z → Fin 3) ≤ 9 * ((Finset.univ : Finset (Z → Fin 3)).filter
        (fun r => 2 ≤ |∑ k : Fin t, lin k * maskToInt (eM ((0, 0), r)) k|)).card := by
    intro lin hlv hlu hlv0 hcard2
    rcases Finset.one_lt_card.mp (by omega : 1 < (Finset.univ.filter (fun k : Fin t => lin k ≠ 0)).card) with
      ⟨w1, hw1, w2, hw2, hw12⟩
    have hw1_nz : lin w1 ≠ 0 := (Finset.mem_filter.mp hw1).2
    have hw2_nz : lin w2 ≠ 0 := (Finset.mem_filter.mp hw2).2
    have hw1_Z : w1 ≠ u ∧ w1 ≠ v := ⟨fun h => hw1_nz (h ▸ hlu), fun h => hw1_nz (h ▸ hlv0)⟩
    have hw2_Z : w2 ≠ u ∧ w2 ≠ v := ⟨fun h => hw2_nz (h ▸ hlu), fun h => hw2_nz (h ▸ hlv0)⟩
    let z1 : Z := ⟨w1, hw1_Z⟩
    let z2 : Z := ⟨w2, hw2_Z⟩
    have hz12 : z1 ≠ z2 := fun h => hw12 (congrArg Subtype.val h)
    let Z' : Type := {z : Z // z ≠ z1 ∧ z ≠ z2}
    let eR : ((Fin 3 × Fin 3) × (Z' → Fin 3)) ≃ (Z → Fin 3) :=
      { toFun := fun q z => if h1 : z = z1 then q.1.1 else if h2 : z = z2 then q.1.2 else q.2 ⟨z, h1, h2⟩
        invFun := fun r => ((r z1, r z2), fun z' => r z'.1)
        left_inv := fun ⟨⟨a, b⟩, s⟩ => Prod.ext (Prod.ext (by simp) (by simp [hz12.symm]))
          (by funext ⟨z, h1, h2⟩; simp [h1, h2])
        right_inv := fun r => by
          funext z; by_cases h1 : z = z1
          · subst h1; simp
          · by_cases h2 : z = z2
            · subst h2; simp [h1]
            · simp [h1, h2] }
    have hcard_split : Fintype.card (Z → Fin 3) = 9 * Fintype.card (Z' → Fin 3) := by
      rw [← Fintype.card_congr eR, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin]
    have hsum_split : ((Finset.univ : Finset (Z → Fin 3)).filter
        (fun r => 2 ≤ |∑ k : Fin t, lin k * maskToInt (eM ((0, 0), r)) k|)).card =
        ∑ s : Z' → Fin 3, ((Finset.univ : Finset (Fin 3 × Fin 3)).filter
          (fun ab => 2 ≤ |∑ k : Fin t, lin k * maskToInt (eM ((0, 0), eR (ab, s))) k|)).card := by
      rw [Finset.card_filter]
      rw [← Fintype.sum_equiv eR
        (fun q => if 2 ≤ |∑ k : Fin t, lin k * maskToInt (eM ((0, 0), eR q)) k| then 1 else 0)
        (fun r => if 2 ≤ |∑ k : Fin t, lin k * maskToInt (eM ((0, 0), r)) k| then 1 else 0)
        (fun _ => rfl)]
      rw [Fintype.sum_prod_type_right]
      refine Finset.sum_congr rfl fun s _ => (Finset.card_filter _ _).symm
    rw [hcard_split, hsum_split]
    have hge1 : ∀ s : Z' → Fin 3,
        1 ≤ ((Finset.univ : Finset (Fin 3 × Fin 3)).filter
          (fun ab => 2 ≤ |∑ k : Fin t, lin k * maskToInt (eM ((0, 0), eR (ab, s))) k|)).card := by
      intro s
      let restS := ∑ k ∈ (Finset.univ.erase w1).erase w2, lin k * maskToInt (eM ((0, 0), eR ((0, 0), s))) k
      have hval : ∀ ab : Fin 3 × Fin 3,
          ∑ k : Fin t, lin k * maskToInt (eM ((0, 0), eR (ab, s))) k =
            lin w1 * f3 ab.1 + lin w2 * f3 ab.2 + restS := by
        intro ab
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ w1)]
        have hw2m : w2 ∈ (Finset.univ : Finset (Fin t)).erase w1 := Finset.mem_erase.mpr ⟨hw12.symm, Finset.mem_univ _⟩
        rw [← Finset.add_sum_erase ((Finset.univ : Finset (Fin t)).erase w1) _ hw2m]
        have h1 : maskToInt (eM ((0, 0), eR (ab, s))) w1 = f3 ab.1 := by
          dsimp only [maskToInt, eM, eR, Equiv.coe_fn_mk, f3, z1]; simp [hw1_Z.1, hw1_Z.2]
        have h2 : maskToInt (eM ((0, 0), eR (ab, s))) w2 = f3 ab.2 := by
          have hv2 : eM ((0, 0), eR (ab, s)) w2 = ab.2 := by
            dsimp only [eM, eR, Equiv.coe_fn_mk]
            rw [dif_neg hw2_Z.1, dif_neg hw2_Z.2, dif_neg hz12.symm, dif_pos rfl]
          dsimp only [maskToInt, f3]; rw [hv2]
        have hrest : ∑ k ∈ (Finset.univ.erase w1).erase w2, lin k * maskToInt (eM ((0, 0), eR (ab, s))) k = restS := by
          refine Finset.sum_congr rfl fun k hk => ?_
          have hne2 : k ≠ w2 := (Finset.mem_erase.mp hk).1
          have hne1 : k ≠ w1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
          by_cases hku : k = u
          · subst hku; simp [hlu]
          · by_cases hkv : k = v
            · subst hkv; simp [hlv0]
            · dsimp only [maskToInt, eM, eR, Equiv.coe_fn_mk, z1, z2]
              have hz1' : (⟨k, hku, hkv⟩ : Z) ≠ ⟨w1, hw1_Z⟩ := fun h => hne1 (congrArg Subtype.val h)
              have hz2' : (⟨k, hku, hkv⟩ : Z) ≠ ⟨w2, hw2_Z⟩ := fun h => hne2 (congrArg Subtype.val h)
              simp [hku, hkv, hz1', hz2']
        rw [h1, h2, hrest]; ring
      have hpm1 : lin w1 = 1 ∨ lin w1 = -1 := (hlv w1).resolve_left hw1_nz
      have hpm2 : lin w2 = 1 ∨ lin w2 = -1 := (hlv w2).resolve_left hw2_nz
      have hex_ab : ∃ ab : Fin 3 × Fin 3, 2 ≤ |lin w1 * f3 ab.1 + lin w2 * f3 ab.2 + restS| := by
        by_cases hr0 : 0 ≤ restS
        · refine ⟨(if lin w1 = 1 then 1 else 2, if lin w2 = 1 then 1 else 2), ?_⟩
          have hsum_eq : lin w1 * f3 (if lin w1 = 1 then 1 else 2) + lin w2 * f3 (if lin w2 = 1 then 1 else 2) + restS = 2 + restS := by
            rcases hpm1 with h1 | h1 <;> rcases hpm2 with h2 | h2 <;> simp [h1, h2, f3] <;> ring
          rw [hsum_eq, abs_of_nonneg (by omega)]; omega
        · refine ⟨(if lin w1 = 1 then 2 else 1, if lin w2 = 1 then 2 else 1), ?_⟩
          have hsum_eq : lin w1 * f3 (if lin w1 = 1 then 2 else 1) + lin w2 * f3 (if lin w2 = 1 then 2 else 1) + restS = -2 + restS := by
            rcases hpm1 with h1 | h1 <;> rcases hpm2 with h2 | h2 <;> simp [h1, h2, f3] <;> ring
          rw [hsum_eq, abs_of_neg (by omega)]; omega
      rcases hex_ab with ⟨ab, hab⟩
      exact Finset.card_pos.mpr ⟨ab, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hval ab]; exact hab⟩⟩
    have hsum_ge : Fintype.card (Z' → Fin 3) ≤
        ∑ s : Z' → Fin 3, ((Finset.univ : Finset (Fin 3 × Fin 3)).filter
          (fun ab => 2 ≤ |∑ k : Fin t, lin k * maskToInt (eM ((0, 0), eR (ab, s))) k|)).card := by
      calc Fintype.card (Z' → Fin 3) = ∑ _s : Z' → Fin 3, 1 := by simp
        _ ≤ _ := Finset.sum_le_sum fun s _ => hge1 s
    omega
  by_cases hA2 : 2 ≤ suppA.card
  · have h1 := htwo_lin aA haA_val (by simp [aA]) (by simp [aA]) hA2
    refine h1.trans (Nat.mul_le_mul_left 9 (Finset.card_le_card fun r hr => ?_))
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcnt_5 r (Or.inl (Finset.mem_filter.mp hr).2)⟩
  · by_cases hB2 : 2 ≤ suppB.card
    · have h1 := htwo_lin aB haB_val (by simp [aB]) (by simp [aB]) hB2
      refine h1.trans (Nat.mul_le_mul_left 9 (Finset.card_le_card fun r hr => ?_))
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcnt_5 r (Or.inr (Or.inl (Finset.mem_filter.mp hr).2))⟩
    · by_cases hAneg : ∃ w : Fin t, aA w = -1
      · rcases hAneg with ⟨w0, hw0⟩
        have hw0_Z : w0 ≠ u ∧ w0 ≠ v := by
          constructor <;> intro h <;> (subst h; simp [aA] at hw0)
        have hA_only : ∀ k : Fin t, k ≠ w0 → aA k = 0 := by
          intro k hk
          by_contra hnz
          have hmem1 : w0 ∈ suppA := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
          have hmem2 : k ∈ suppA := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnz⟩
          have : 1 < suppA.card := Finset.one_lt_card.mpr ⟨w0, hmem1, k, hmem2, hk.symm⟩
          omega
        have hAval_eq : ∀ x : Fin t → ℤ, Aval x = -x w0 := fun x => by
          dsimp only [Aval]
          rw [Finset.sum_eq_single w0]
          · rw [hw0]; ring
          · intro k _ hk; rw [hA_only k hk, zero_mul]
          · intro h; exact (h (Finset.mem_univ _)).elim
        let z0 : Z := ⟨w0, hw0_Z⟩
        have hgood_z0 : ∀ r : Z → Fin 3, r z0 = 1 → 5 ≤ cnt r := by
          intro r hr1
          by_cases hcond : 2 ≤ |Bval (maskToInt (eM ((0, 0), r)))| ∨ Dval (maskToInt (eM ((0, 0), r))) ≠ 0
          · exact hcnt_5 r (Or.inr hcond)
          · push_neg at hcond
            rcases hcond with ⟨hB1, hD0⟩
            have hA_r : Aval (maskToInt (eM ((0, 0), r))) = -1 := by
              rw [hAval_eq]; dsimp only [maskToInt, eM, Equiv.coe_fn_mk]
              simp [hw0_Z.1, hw0_Z.2, show r ⟨w0, hw0_Z⟩ = 1 from hr1]
            have hA_abs : Aval (maskToAbs (eM ((0, 0), r))) = -1 := by
              rw [hAval_eq]; dsimp only [maskToAbs, eM, Equiv.coe_fn_mk]
              simp [hw0_Z.1, hw0_Z.2, show r ⟨w0, hw0_Z⟩ = 1 from hr1]
            have hQ4 : 4 ≤ ((Finset.univ : Finset (Fin 3 × Fin 3)).filter
                (fun ab => ab.1 ≠ 2 ∧ evalQuad t coef (maskToInt (eM (ab, r))) ≠ 0)).card := by
              let B0 := Bval (maskToInt (eM ((0, 0), r)))
              have hb_good : 2 ≤ ((Finset.univ : Finset (Fin 3)).filter (fun b => f3 b - B0 ≠ 0)).card :=
                hcard_ge2 (fun b => f3 b - B0) (Finset.card_le_one.mpr fun b1 hb1 b2 hb2 =>
                  hf3_inj b1 b2 (by linarith [(Finset.mem_filter.mp hb1).2, (Finset.mem_filter.mp hb2).2]))
              have hprod_sub : ({0, 1} : Finset (Fin 3)) ×ˢ (Finset.univ.filter (fun b : Fin 3 => f3 b - B0 ≠ 0)) ⊆
                  (Finset.univ : Finset (Fin 3 × Fin 3)).filter
                    (fun ab => ab.1 ≠ 2 ∧ evalQuad t coef (maskToInt (eM (ab, r))) ≠ 0) := by
                intro ⟨a, b⟩ hab
                rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
                have ha2 : a ≠ 2 := by simp only [Finset.mem_insert, Finset.mem_singleton] at ha; rcases ha with rfl | rfl <;> decide
                have hfa : f3 a - (-1) ≠ 0 := by
                  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
                  rcases ha with rfl | rfl <;> decide
                refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha2, ?_⟩
                rw [hQ_decomp, (hA_indep r (a, b)).1, (hB_indep r (a, b)).1, (hD_indep r (a, b)).1, hA_r, hD0, add_zero]
                have hu_eq : maskToInt (eM ((a, b), r)) u = f3 a := by dsimp only [maskToInt, eM, Equiv.coe_fn_mk, f3]; simp
                have hv_eq : maskToInt (eM ((a, b), r)) v = f3 b := by dsimp only [maskToInt, eM, Equiv.coe_fn_mk, f3]; simp [huv.symm]
                rw [hu_eq, hv_eq]
                exact mul_ne_zero (mul_ne_zero he0 hfa) (Finset.mem_filter.mp hb).2
              have hc := Finset.card_le_card hprod_sub
              rw [Finset.card_product] at hc
              have h2c : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
              rw [h2c] at hc; omega
            have hex_abs : ∃ b : Fin 3, evalQuad t coef (maskToAbs (eM ((2, b), r))) ≠ 0 := by
              have hdiff : evalQuad t coef (maskToAbs (eM ((2, 1), r))) - evalQuad t coef (maskToAbs (eM ((2, 0), r))) = 2 * c0 := by
                rw [hQ_decomp, hQ_decomp, (hA_indep r (2, 1)).2, (hB_indep r (2, 1)).2, (hD_indep r (2, 1)).2,
                  (hA_indep r (2, 0)).2, (hB_indep r (2, 0)).2, (hD_indep r (2, 0)).2, hA_abs]
                have hu1 : maskToAbs (eM ((2, 1), r)) u = 1 := by dsimp only [maskToAbs, eM, Equiv.coe_fn_mk]; simp
                have hu0 : maskToAbs (eM ((2, 0), r)) u = 1 := by dsimp only [maskToAbs, eM, Equiv.coe_fn_mk]; simp
                have hv1 : maskToAbs (eM ((2, 1), r)) v = 1 := by dsimp only [maskToAbs, eM, Equiv.coe_fn_mk]; simp [huv.symm]
                have hv0 : maskToAbs (eM ((2, 0), r)) v = 0 := by dsimp only [maskToAbs, eM, Equiv.coe_fn_mk]; simp [huv.symm]
                rw [hu1, hu0, hv1, hv0]; ring
              by_cases h1 : evalQuad t coef (maskToAbs (eM ((2, 1), r))) ≠ 0
              · exact ⟨1, h1⟩
              · push_neg at h1; refine ⟨0, fun h0 => he0 (by linarith)⟩
            rcases hex_abs with ⟨b0, hb0⟩
            have hsub5 : insert ((2 : Fin 3), b0) ((Finset.univ : Finset (Fin 3 × Fin 3)).filter
                (fun ab => ab.1 ≠ 2 ∧ evalQuad t coef (maskToInt (eM (ab, r))) ≠ 0)) ⊆
                (Finset.univ : Finset (Fin 3 × Fin 3)).filter
                  (fun ab => evalQuad t coef (maskToInt (eM (ab, r))) ≠ 0 ∨
                    evalQuad t coef (maskToAbs (eM (ab, r))) ≠ 0) := by
              intro ab hab
              rcases Finset.mem_insert.mp hab with rfl | hmem
              · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr hb0⟩
              · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl (Finset.mem_filter.mp hmem).2.2⟩
            have hnotmem : ((2 : Fin 3), b0) ∉ (Finset.univ : Finset (Fin 3 × Fin 3)).filter
                (fun ab => ab.1 ≠ 2 ∧ evalQuad t coef (maskToInt (eM (ab, r))) ≠ 0) := by
              simp
            have hc := Finset.card_le_card hsub5
            rw [Finset.card_insert_of_notMem hnotmem] at hc
            dsimp only [cnt]; omega
        have hthird : Fintype.card (Z → Fin 3) = 3 * ((Finset.univ : Finset (Z → Fin 3)).filter (fun r => r z0 = 1)).card := by
          let eZ1 : (Fin 3 × ({z : Z // z ≠ z0} → Fin 3)) ≃ (Z → Fin 3) :=
            { toFun := fun q z => if h : z = z0 then q.1 else q.2 ⟨z, h⟩
              invFun := fun r => (r z0, fun z' => r z'.1)
              left_inv := fun ⟨a, s⟩ => Prod.ext (by simp) (by funext ⟨z, hz⟩; simp [hz])
              right_inv := fun r => funext fun z => by dsimp only; by_cases h : z = z0; exact (dif_pos h).trans (congrArg r h.symm); exact dif_neg h }
          have h1 : Fintype.card (Z → Fin 3) = 3 * Fintype.card ({z : Z // z ≠ z0} → Fin 3) := by
            rw [← Fintype.card_congr eZ1, Fintype.card_prod, Fintype.card_fin]
          have h2 : ((Finset.univ : Finset (Z → Fin 3)).filter (fun r => r z0 = 1)).card =
              Fintype.card ({z : Z // z ≠ z0} → Fin 3) := by
            refine Finset.card_bij (fun r _ => fun z' => r z'.1) (fun _ _ => Finset.mem_univ _) ?_ ?_
            · intro r1 hr1 r2 hr2 heq
              funext z; by_cases h : z = z0
              · subst h; exact (Finset.mem_filter.mp hr1).2.trans (Finset.mem_filter.mp hr2).2.symm
              · exact congrFun heq ⟨z, h⟩
            · intro s _
              refine ⟨eZ1 (1, s), Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [eZ1]⟩,
                by funext ⟨z, hz⟩; simp [eZ1, hz]⟩
          rw [h1, h2]
        have hle_cnt : ((Finset.univ : Finset (Z → Fin 3)).filter (fun r => r z0 = 1)).card ≤
            ((Finset.univ : Finset (Z → Fin 3)).filter (fun r => 5 ≤ cnt r)).card :=
          Finset.card_le_card fun r hr => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgood_z0 r (Finset.mem_filter.mp hr).2⟩
        omega
      · by_cases hBneg : ∃ w : Fin t, aB w = -1
        · rcases hBneg with ⟨w0, hw0⟩
          have hw0_Z : w0 ≠ u ∧ w0 ≠ v := by
            constructor <;> intro h <;> (subst h; simp [aB] at hw0)
          have hB_only : ∀ k : Fin t, k ≠ w0 → aB k = 0 := by
            intro k hk
            by_contra hnz
            have hmem1 : w0 ∈ suppB := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
            have hmem2 : k ∈ suppB := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnz⟩
            have : 1 < suppB.card := Finset.one_lt_card.mpr ⟨w0, hmem1, k, hmem2, hk.symm⟩
            omega
          have hBval_eq : ∀ x : Fin t → ℤ, Bval x = -x w0 := fun x => by
            dsimp only [Bval]
            rw [Finset.sum_eq_single w0]
            · rw [hw0]; ring
            · intro k _ hk; rw [hB_only k hk, zero_mul]
            · intro h; exact (h (Finset.mem_univ _)).elim
          let z0 : Z := ⟨w0, hw0_Z⟩
          have hgood_z0 : ∀ r : Z → Fin 3, r z0 = 1 → 5 ≤ cnt r := by
            intro r hr1
            by_cases hcond : 2 ≤ |Aval (maskToInt (eM ((0, 0), r)))| ∨ Dval (maskToInt (eM ((0, 0), r))) ≠ 0
            · rcases hcond with h1 | h2
              · exact hcnt_5 r (Or.inl h1)
              · exact hcnt_5 r (Or.inr (Or.inr h2))
            · push_neg at hcond
              rcases hcond with ⟨hA1, hD0⟩
              have hB_r : Bval (maskToInt (eM ((0, 0), r))) = -1 := by
                rw [hBval_eq]; dsimp only [maskToInt, eM, Equiv.coe_fn_mk]
                simp [hw0_Z.1, hw0_Z.2, show r ⟨w0, hw0_Z⟩ = 1 from hr1]
              have hB_abs : Bval (maskToAbs (eM ((0, 0), r))) = -1 := by
                rw [hBval_eq]; dsimp only [maskToAbs, eM, Equiv.coe_fn_mk]
                simp [hw0_Z.1, hw0_Z.2, show r ⟨w0, hw0_Z⟩ = 1 from hr1]
              have hQ4 : 4 ≤ ((Finset.univ : Finset (Fin 3 × Fin 3)).filter
                  (fun ab => ab.2 ≠ 2 ∧ evalQuad t coef (maskToInt (eM (ab, r))) ≠ 0)).card := by
                let A0 := Aval (maskToInt (eM ((0, 0), r)))
                have ha_good : 2 ≤ ((Finset.univ : Finset (Fin 3)).filter (fun a => f3 a - A0 ≠ 0)).card :=
                  hcard_ge2 (fun a => f3 a - A0) (Finset.card_le_one.mpr fun a1 ha1 a2 ha2 =>
                    hf3_inj a1 a2 (by linarith [(Finset.mem_filter.mp ha1).2, (Finset.mem_filter.mp ha2).2]))
                have hprod_sub : (Finset.univ.filter (fun a : Fin 3 => f3 a - A0 ≠ 0)) ×ˢ ({0, 1} : Finset (Fin 3)) ⊆
                    (Finset.univ : Finset (Fin 3 × Fin 3)).filter
                      (fun ab => ab.2 ≠ 2 ∧ evalQuad t coef (maskToInt (eM (ab, r))) ≠ 0) := by
                  intro ⟨a, b⟩ hab
                  rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
                  have hb2 : b ≠ 2 := by simp only [Finset.mem_insert, Finset.mem_singleton] at hb; rcases hb with rfl | rfl <;> decide
                  have hfb : f3 b - (-1) ≠ 0 := by
                    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
                    rcases hb with rfl | rfl <;> decide
                  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb2, ?_⟩
                  rw [hQ_decomp, (hA_indep r (a, b)).1, (hB_indep r (a, b)).1, (hD_indep r (a, b)).1, hB_r, hD0, add_zero]
                  have hu_eq : maskToInt (eM ((a, b), r)) u = f3 a := by dsimp only [maskToInt, eM, Equiv.coe_fn_mk, f3]; simp
                  have hv_eq : maskToInt (eM ((a, b), r)) v = f3 b := by dsimp only [maskToInt, eM, Equiv.coe_fn_mk, f3]; simp [huv.symm]
                  rw [hu_eq, hv_eq]
                  exact mul_ne_zero (mul_ne_zero he0 (Finset.mem_filter.mp ha).2) hfb
                have hc := Finset.card_le_card hprod_sub
                rw [Finset.card_product] at hc
                have h2c : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
                rw [h2c] at hc; omega
              have hex_abs : ∃ a : Fin 3, evalQuad t coef (maskToAbs (eM ((a, 2), r))) ≠ 0 := by
                have hdiff : evalQuad t coef (maskToAbs (eM ((1, 2), r))) - evalQuad t coef (maskToAbs (eM ((0, 2), r))) = 2 * c0 := by
                  rw [hQ_decomp, hQ_decomp, (hA_indep r (1, 2)).2, (hB_indep r (1, 2)).2, (hD_indep r (1, 2)).2,
                    (hA_indep r (0, 2)).2, (hB_indep r (0, 2)).2, (hD_indep r (0, 2)).2, hB_abs]
                  have hu1 : maskToAbs (eM ((1, 2), r)) u = 1 := by dsimp only [maskToAbs, eM, Equiv.coe_fn_mk]; simp
                  have hu0 : maskToAbs (eM ((0, 2), r)) u = 0 := by dsimp only [maskToAbs, eM, Equiv.coe_fn_mk]; simp
                  have hv1 : maskToAbs (eM ((1, 2), r)) v = 1 := by dsimp only [maskToAbs, eM, Equiv.coe_fn_mk]; simp [huv.symm]
                  have hv0 : maskToAbs (eM ((0, 2), r)) v = 1 := by dsimp only [maskToAbs, eM, Equiv.coe_fn_mk]; simp [huv.symm]
                  rw [hu1, hu0, hv1, hv0]; ring
                by_cases h1 : evalQuad t coef (maskToAbs (eM ((1, 2), r))) ≠ 0
                · exact ⟨1, h1⟩
                · push_neg at h1; refine ⟨0, fun h0 => he0 (by linarith)⟩
              rcases hex_abs with ⟨a0, ha0⟩
              have hsub5 : insert (a0, (2 : Fin 3)) ((Finset.univ : Finset (Fin 3 × Fin 3)).filter
                  (fun ab => ab.2 ≠ 2 ∧ evalQuad t coef (maskToInt (eM (ab, r))) ≠ 0)) ⊆
                  (Finset.univ : Finset (Fin 3 × Fin 3)).filter
                    (fun ab => evalQuad t coef (maskToInt (eM (ab, r))) ≠ 0 ∨
                      evalQuad t coef (maskToAbs (eM (ab, r))) ≠ 0) := by
                intro ab hab
                rcases Finset.mem_insert.mp hab with rfl | hmem
                · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ha0⟩
                · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl (Finset.mem_filter.mp hmem).2.2⟩
              have hnotmem : (a0, (2 : Fin 3)) ∉ (Finset.univ : Finset (Fin 3 × Fin 3)).filter
                  (fun ab => ab.2 ≠ 2 ∧ evalQuad t coef (maskToInt (eM (ab, r))) ≠ 0) := by
                simp
              have hc := Finset.card_le_card hsub5
              rw [Finset.card_insert_of_notMem hnotmem] at hc
              dsimp only [cnt]; omega
          have hthird : Fintype.card (Z → Fin 3) = 3 * ((Finset.univ : Finset (Z → Fin 3)).filter (fun r => r z0 = 1)).card := by
            let eZ1 : (Fin 3 × ({z : Z // z ≠ z0} → Fin 3)) ≃ (Z → Fin 3) :=
              { toFun := fun q z => if h : z = z0 then q.1 else q.2 ⟨z, h⟩
                invFun := fun r => (r z0, fun z' => r z'.1)
                left_inv := fun ⟨a, s⟩ => Prod.ext (by simp) (by funext ⟨z, hz⟩; simp [hz])
                right_inv := fun r => funext fun z => by dsimp only; by_cases h : z = z0; exact (dif_pos h).trans (congrArg r h.symm); exact dif_neg h }
            have h1 : Fintype.card (Z → Fin 3) = 3 * Fintype.card ({z : Z // z ≠ z0} → Fin 3) := by
              rw [← Fintype.card_congr eZ1, Fintype.card_prod, Fintype.card_fin]
            have h2 : ((Finset.univ : Finset (Z → Fin 3)).filter (fun r => r z0 = 1)).card =
                Fintype.card ({z : Z // z ≠ z0} → Fin 3) := by
              refine Finset.card_bij (fun r _ => fun z' => r z'.1) (fun _ _ => Finset.mem_univ _) ?_ ?_
              · intro r1 hr1 r2 hr2 heq
                funext z; by_cases h : z = z0
                · subst h; exact (Finset.mem_filter.mp hr1).2.trans (Finset.mem_filter.mp hr2).2.symm
                · exact congrFun heq ⟨z, h⟩
              · intro s _
                refine ⟨eZ1 (1, s), Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [eZ1]⟩,
                  by funext ⟨z, hz⟩; simp [eZ1, hz]⟩
            rw [h1, h2]
          have hle_cnt : ((Finset.univ : Finset (Z → Fin 3)).filter (fun r => r z0 = 1)).card ≤
              ((Finset.univ : Finset (Z → Fin 3)).filter (fun r => 5 ≤ cnt r)).card :=
            Finset.card_le_card fun r hr => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgood_z0 r (Finset.mem_filter.mp hr).2⟩
          omega
        · push_neg at hAneg hBneg
          have hA_opt : ∃ v_opt : Option (Fin t),
              (∀ w, v_opt = some w → w ≠ u ∧ w ≠ v) ∧
              ∀ x : Fin t → ℤ, Aval x = v_opt.elim 0 x := by
            by_cases hemp : suppA = ∅
            · refine ⟨none, fun _ h => (by cases h), fun x => ?_⟩
              dsimp only [Aval, Option.elim]
              refine Finset.sum_eq_zero fun k _ => ?_
              have h0 : aA k = 0 := by
                by_contra hnz
                have hm : k ∈ suppA := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnz⟩
                rw [hemp] at hm; exact Finset.notMem_empty _ hm
              rw [h0, zero_mul]
            · rcases Finset.nonempty_iff_ne_empty.mpr hemp with ⟨w, hw⟩
              have hw_nz : aA w ≠ 0 := (Finset.mem_filter.mp hw).2
              have hw_1 : aA w = 1 := ((haA_val w).resolve_left hw_nz).resolve_right (hAneg w)
              have hw_uv : w ≠ u ∧ w ≠ v := ⟨fun h => hw_nz (by subst h; simp [aA]), fun h => hw_nz (by subst h; simp [aA])⟩
              refine ⟨some w, fun _ h => by rcases Option.some.inj h with rfl; exact hw_uv, fun x => ?_⟩
              dsimp only [Aval, Option.elim]
              rw [Finset.sum_eq_single w]
              · rw [hw_1, one_mul]
              · intro k _ hk
                by_contra hmul
                have hknz : aA k ≠ 0 := fun h => hmul (by rw [h, zero_mul])
                have hm2 : k ∈ suppA := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hknz⟩
                have : 1 < suppA.card := Finset.one_lt_card.mpr ⟨w, hw, k, hm2, hk.symm⟩
                omega
              · intro h; exact (h (Finset.mem_univ _)).elim
          have hB_opt : ∃ w_opt : Option (Fin t),
              (∀ w, w_opt = some w → w ≠ u ∧ w ≠ v) ∧
              ∀ x : Fin t → ℤ, Bval x = w_opt.elim 0 x := by
            by_cases hemp : suppB = ∅
            · refine ⟨none, fun _ h => (by cases h), fun x => ?_⟩
              dsimp only [Bval, Option.elim]
              refine Finset.sum_eq_zero fun k _ => ?_
              have h0 : aB k = 0 := by
                by_contra hnz
                have hm : k ∈ suppB := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnz⟩
                rw [hemp] at hm; exact Finset.notMem_empty _ hm
              rw [h0, zero_mul]
            · rcases Finset.nonempty_iff_ne_empty.mpr hemp with ⟨w, hw⟩
              have hw_nz : aB w ≠ 0 := (Finset.mem_filter.mp hw).2
              have hw_1 : aB w = 1 := ((haB_val w).resolve_left hw_nz).resolve_right (hBneg w)
              have hw_uv : w ≠ u ∧ w ≠ v := ⟨fun h => hw_nz (by subst h; simp [aB]), fun h => hw_nz (by subst h; simp [aB])⟩
              refine ⟨some w, fun _ h => by rcases Option.some.inj h with rfl; exact hw_uv, fun x => ?_⟩
              dsimp only [Bval, Option.elim]
              rw [Finset.sum_eq_single w]
              · rw [hw_1, one_mul]
              · intro k _ hk
                by_contra hmul
                have hknz : aB k ≠ 0 := fun h => hmul (by rw [h, zero_mul])
                have hm2 : k ∈ suppB := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hknz⟩
                have : 1 < suppB.card := Finset.one_lt_card.mpr ⟨w, hw, k, hm2, hk.symm⟩
                omega
              · intro h; exact (h (Finset.mem_univ _)).elim
          rcases hA_opt with ⟨v_opt, hv_opt_uv, hAv⟩
          rcases hB_opt with ⟨w_opt, hw_opt_uv, hBw⟩
          by_cases hsame : ∃ w0 : Fin t, v_opt = some w0 ∧ w_opt = some w0
          · rcases hsame with ⟨w0, rfl, rfl⟩
            have hw0_Z : w0 ≠ u ∧ w0 ≠ v := hv_opt_uv w0 rfl
            let z0 : Z := ⟨w0, hw0_Z⟩
            let eZ1 : (Fin 3 × ({z : Z // z ≠ z0} → Fin 3)) ≃ (Z → Fin 3) :=
              { toFun := fun q z => if h : z = z0 then q.1 else q.2 ⟨z, h⟩
                invFun := fun r => (r z0, fun z' => r z'.1)
                left_inv := fun ⟨a, s⟩ => Prod.ext (by simp) (by funext ⟨z, hz⟩; simp [hz])
                right_inv := fun r => funext fun z => by dsimp only; by_cases h : z = z0; exact (dif_pos h).trans (congrArg r h.symm); exact dif_neg h }
            have hcard_split : Fintype.card (Z → Fin 3) = 3 * Fintype.card ({z : Z // z ≠ z0} → Fin 3) := by
              rw [← Fintype.card_congr eZ1, Fintype.card_prod, Fintype.card_fin]
            have hsum_split : ((Finset.univ : Finset (Z → Fin 3)).filter (fun r => Dval (maskToInt (eM ((0, 0), r))) ≠ 0)).card =
                ∑ s : {z : Z // z ≠ z0} → Fin 3, ((Finset.univ : Finset (Fin 3)).filter
                  (fun a => Dval (maskToInt (eM ((0, 0), eZ1 (a, s)))) ≠ 0)).card := by
              rw [Finset.card_filter]
              rw [← Fintype.sum_equiv eZ1
                (fun q => if Dval (maskToInt (eM ((0, 0), eZ1 q))) ≠ 0 then 1 else 0)
                (fun r => if Dval (maskToInt (eM ((0, 0), r))) ≠ 0 then 1 else 0) (fun _ => rfl)]
              rw [Fintype.sum_prod_type_right]
              refine Finset.sum_congr rfl fun s _ => (Finset.card_filter _ _).symm
            have hge1 : ∀ s : {z : Z // z ≠ z0} → Fin 3,
                1 ≤ ((Finset.univ : Finset (Fin 3)).filter
                  (fun a => Dval (maskToInt (eM ((0, 0), eZ1 (a, s)))) ≠ 0)).card := by
              intro s
              have hquad_d : Dval (maskToInt (eM ((0, 0), eZ1 (1, s)))) + Dval (maskToInt (eM ((0, 0), eZ1 (2, s)))) -
                  2 * Dval (maskToInt (eM ((0, 0), eZ1 (0, s)))) = -2 * c0 := by
                dsimp only [Dval]
                rw [hAv, hBw, hAv, hBw, hAv, hBw]
                dsimp only [Option.elim]
                have hx1 : maskToInt (eM ((0, 0), eZ1 (1, s))) w0 = 1 := by
                  dsimp only [maskToInt, eM, eZ1, Equiv.coe_fn_mk, z0]; simp [hw0_Z.1, hw0_Z.2]
                have hx2 : maskToInt (eM ((0, 0), eZ1 (2, s))) w0 = -1 := by
                  dsimp only [maskToInt, eM, eZ1, Equiv.coe_fn_mk, z0]; simp [hw0_Z.1, hw0_Z.2]
                have hx0 : maskToInt (eM ((0, 0), eZ1 (0, s))) w0 = 0 := by
                  dsimp only [maskToInt, eM, eZ1, Equiv.coe_fn_mk, z0]; simp [hw0_Z.1, hw0_Z.2]
                have hRlin : Rval (maskToInt (eM ((0, 0), eZ1 (1, s)))) + Rval (maskToInt (eM ((0, 0), eZ1 (2, s)))) -
                    2 * Rval (maskToInt (eM ((0, 0), eZ1 (0, s)))) = 0 := by
                  dsimp only [Rval]
                  rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
                  refine Finset.sum_eq_zero fun e he => ?_
                  rcases (Finset.mem_filter.mp he).2 with ⟨h1, h2, h3, h4⟩
                  have hother : ∀ (k : Fin t) (hku : k ≠ u) (hkv : k ≠ v), k ≠ w0 →
                      maskToInt (eM ((0, 0), eZ1 (1, s))) k = maskToInt (eM ((0, 0), eZ1 (0, s))) k ∧
                      maskToInt (eM ((0, 0), eZ1 (2, s))) k = maskToInt (eM ((0, 0), eZ1 (0, s))) k := by
                    intro k hku hkv hkw
                    have hzk : (⟨k, hku, hkv⟩ : Z) ≠ z0 := fun h => hkw (congrArg Subtype.val h)
                    dsimp only [maskToInt, eM, eZ1, Equiv.coe_fn_mk]; simp [hku, hkv, hzk]
                  by_cases hw1 : e.val.1 = w0
                  · have hw2 : e.val.2 ≠ w0 := by rw [← hw1]; exact (ne_of_lt e.2).symm
                    rcases hother e.val.2 h2 h4 hw2 with ⟨ha, hb⟩
                    rw [hw1, hx1, hx2, hx0, ha, hb]; ring
                  · by_cases hw2 : e.val.2 = w0
                    · rcases hother e.val.1 h1 h3 hw1 with ⟨ha, hb⟩
                      rw [hw2, hx1, hx2, hx0, ha, hb]; ring
                    · rcases hother e.val.1 h1 h3 hw1 with ⟨ha1, hb1⟩
                      rcases hother e.val.2 h2 h4 hw2 with ⟨ha2, hb2⟩
                      rw [ha1, hb1, ha2, hb2]; ring
                rw [hx1, hx2, hx0]; linarith
              by_cases h1 : Dval (maskToInt (eM ((0, 0), eZ1 (1, s)))) ≠ 0
              · exact Finset.card_pos.mpr ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩⟩
              · by_cases h2 : Dval (maskToInt (eM ((0, 0), eZ1 (2, s)))) ≠ 0
                · exact Finset.card_pos.mpr ⟨2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩⟩
                · by_cases h0 : Dval (maskToInt (eM ((0, 0), eZ1 (0, s)))) ≠ 0
                  · exact Finset.card_pos.mpr ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩⟩
                  · push_neg at h1 h2 h0; exfalso; exact he0 (by linarith)
            have hle_D : ((Finset.univ : Finset (Z → Fin 3)).filter (fun r => Dval (maskToInt (eM ((0, 0), r))) ≠ 0)).card ≤
                ((Finset.univ : Finset (Z → Fin 3)).filter (fun r => 5 ≤ cnt r)).card :=
              Finset.card_le_card fun r hr => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcnt_5 r (Or.inr (Or.inr (Finset.mem_filter.mp hr).2))⟩
            have hsum_ge : Fintype.card ({z : Z // z ≠ z0} → Fin 3) ≤
                ((Finset.univ : Finset (Z → Fin 3)).filter (fun r => Dval (maskToInt (eM ((0, 0), r))) ≠ 0)).card := by
              rw [hsum_split]
              calc Fintype.card ({z : Z // z ≠ z0} → Fin 3) = ∑ _s : {z : Z // z ≠ z0} → Fin 3, 1 := by simp
                _ ≤ _ := Finset.sum_le_sum fun s _ => hge1 s
            omega
          · push_neg at hsame
            let dcoef : {p : Fin t × Fin t // p.1 < p.2} → ℤ := fun e =>
              (if e.val.1 ≠ u ∧ e.val.2 ≠ u ∧ e.val.1 ≠ v ∧ e.val.2 ≠ v then coef e else 0) -
              (if (v_opt = some e.val.1 ∧ w_opt = some e.val.2) ∨ (v_opt = some e.val.2 ∧ w_opt = some e.val.1) then c0 else 0)
            have hD_quad : ∀ x : Fin t → ℤ, Dval x = evalQuad t dcoef x := by
              intro x
              dsimp only [Dval, Rval, evalQuad, dcoef]
              rw [hAv, hBw]
              have hprod_opt : c0 * v_opt.elim 0 x * w_opt.elim 0 x =
                  ∑ e : {p : Fin t × Fin t // p.1 < p.2},
                    (if (v_opt = some e.val.1 ∧ w_opt = some e.val.2) ∨ (v_opt = some e.val.2 ∧ w_opt = some e.val.1) then c0 else 0) *
                      x e.val.1 * x e.val.2 := by
                rcases v_opt with _ | w1 <;> rcases w_opt with _ | w2
                · simp [Option.elim]
                · simp [Option.elim]
                · simp [Option.elim]
                · have hne12 : w1 ≠ w2 := fun h => hsame w1 rfl (h ▸ rfl)
                  by_cases hlt : w1 < w2
                  · let e12 : {p : Fin t × Fin t // p.1 < p.2} := ⟨(w1, w2), hlt⟩
                    rw [Finset.sum_eq_single e12]
                    · simp [e12, Option.elim]
                    · intro e _ hne
                      have hcond : ¬ ((some w1 = some e.val.1 ∧ some w2 = some e.val.2) ∨
                          (some w1 = some e.val.2 ∧ some w2 = some e.val.1)) := by
                        rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
                        · exact hne (Subtype.ext (Prod.ext (Option.some.inj h1).symm (Option.some.inj h2).symm))
                        · have h1' := Option.some.inj h1; have h2' := Option.some.inj h2
                          exact absurd e.2 (by rw [← h1', ← h2']; exact not_lt.mpr (le_of_lt hlt))
                      rw [if_neg hcond, zero_mul, zero_mul]
                    · intro h; exact (h (Finset.mem_univ _)).elim
                  · have hgt : w2 < w1 := lt_of_le_of_ne (not_lt.mp hlt) hne12.symm
                    let e21 : {p : Fin t × Fin t // p.1 < p.2} := ⟨(w2, w1), hgt⟩
                    rw [Finset.sum_eq_single e21]
                    · simp [e21, Option.elim]; ring
                    · intro e _ hne
                      have hcond : ¬ ((some w1 = some e.val.1 ∧ some w2 = some e.val.2) ∨
                          (some w1 = some e.val.2 ∧ some w2 = some e.val.1)) := by
                        rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
                        · have h1' := Option.some.inj h1; have h2' := Option.some.inj h2
                          exact absurd e.2 (by rw [← h1', ← h2']; exact not_lt.mpr (le_of_lt hgt))
                        · exact hne (Subtype.ext (Prod.ext (Option.some.inj h2).symm (Option.some.inj h1).symm))
                      rw [if_neg hcond, zero_mul, zero_mul]
                    · intro h; exact (h (Finset.mem_univ _)).elim
              rw [hprod_opt, Finset.sum_filter, ← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl fun e _ => ?_
              split_ifs <;> ring
            have hd_nz : ∃ e1, dcoef e1 ≠ 0 := by
              by_contra hall
              push_neg at hall
              apply hnonsimp
              refine ⟨c0, u, v, v_opt, w_opt, he0, ?_, ?_, ?_, fun x => ?_⟩
              · intro h; exact (hv_opt_uv u h).1 rfl
              · intro h; exact (hw_opt_uv v h).2 rfl
              · rw [Finset.disjoint_left]
                intro k hk1 hk2
                rcases Finset.mem_insert.mp hk1 with rfl | hk1'
                · rcases Finset.mem_insert.mp hk2 with h | hk2'
                  · exact huv h
                  · rcases w_opt with _ | w2
                    · exact Finset.notMem_empty _ hk2'
                    · exact (hw_opt_uv w2 rfl).1 (Finset.mem_singleton.mp hk2').symm
                · rcases v_opt with _ | w1
                  · exact Finset.notMem_empty _ hk1'
                  · have hkw1 : k = w1 := Finset.mem_singleton.mp hk1'
                    subst hkw1
                    rcases Finset.mem_insert.mp hk2 with h | hk2'
                    · exact (hv_opt_uv k rfl).2 h
                    · rcases w_opt with _ | w2
                      · exact Finset.notMem_empty _ hk2'
                      · exact hsame k rfl (congrArg some (Finset.mem_singleton.mp hk2').symm)
              · rw [hdiff_eq, hQ_decomp, hAv, hBw, hD_quad]
                have h0 : evalQuad t dcoef x = 0 := Finset.sum_eq_zero fun e _ => by rw [hall e, zero_mul, zero_mul]
                rw [h0, add_zero]
            have h49 := quad_nz_ge_four_ninths t dcoef hd_nz
            have hD_card_eq : ((Finset.univ : Finset (Fin t → Fin 3)).filter (fun p => evalQuad t dcoef (maskToInt p) ≠ 0)).card =
                9 * ((Finset.univ : Finset (Z → Fin 3)).filter (fun r => Dval (maskToInt (eM ((0, 0), r))) ≠ 0)).card := by
              rw [Finset.card_filter]
              rw [← Fintype.sum_equiv eM
                (fun q => if evalQuad t dcoef (maskToInt (eM q)) ≠ 0 then 1 else 0)
                (fun p => if evalQuad t dcoef (maskToInt p) ≠ 0 then 1 else 0) (fun _ => rfl)]
              rw [Fintype.sum_prod_type_right]
              have hconst : ∀ r : Z → Fin 3,
                  ∑ ab : Fin 3 × Fin 3, (if evalQuad t dcoef (maskToInt (eM (ab, r))) ≠ 0 then 1 else 0) =
                  9 * (if Dval (maskToInt (eM ((0, 0), r))) ≠ 0 then 1 else 0) := by
                intro r
                have h1 : ∀ ab : Fin 3 × Fin 3,
                    (if evalQuad t dcoef (maskToInt (eM (ab, r))) ≠ 0 then 1 else 0) =
                    (if Dval (maskToInt (eM ((0, 0), r))) ≠ 0 then 1 else 0) := fun ab => by
                  rw [← hD_quad, (hD_indep r ab).1]
                rw [Finset.sum_congr rfl fun ab _ => h1 ab, Finset.sum_const, Finset.card_univ,
                  Fintype.card_prod, Fintype.card_fin, smul_eq_mul]
              rw [Finset.sum_congr rfl fun r _ => hconst r, ← Finset.mul_sum, ← Finset.card_filter]
            rw [hD_card_eq, ← hcardZ] at h49
            have hle_cnt : ((Finset.univ : Finset (Z → Fin 3)).filter (fun r => Dval (maskToInt (eM ((0, 0), r))) ≠ 0)).card ≤
                ((Finset.univ : Finset (Z → Fin 3)).filter (fun r => 5 ≤ cnt r)).card :=
              Finset.card_le_card fun r hr => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcnt_5 r (Or.inr (Or.inr (Finset.mem_filter.mp hr).2))⟩
            omega

private lemma exp_le_quad_on_unit (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 := by
  have hb := Real.exp_bound (x := x) (n := 3) (by rw [abs_of_nonneg hx0]; exact hx1) (by omega)
  have hsum : ∑ m ∈ Finset.range 3, x ^ m / (m.factorial : ℝ) = 1 + x + x ^ 2 / 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    norm_num
  rw [hsum, abs_of_nonneg hx0] at hb
  have h1 := (abs_le.mp hb).2
  have hfac : ((3 : ℕ).factorial : ℝ) = 6 := by norm_num
  rw [hfac] at h1
  have h3 : x ^ 3 ≤ x ^ 2 := by nlinarith
  nlinarith

private lemma pair_mgf_bound {α : Type*} [Fintype α] [Nonempty α]
    (bad : α → Prop) [DecidablePred bad] (q : ℝ) (hq : q * (Fintype.card α : ℝ) ≤ ((Finset.univ.filter (fun p => ¬ bad p)).card : ℝ))
    (s d : ℕ) (hs : 3 ≤ s) :
    let lam : ℝ := 1 / (2 * (s : ℝ))
    let badBatch := (Finset.univ : Finset (Fin d → α)).filter
      (fun batch => (((Finset.univ : Finset (Fin d)).filter (fun i => ¬ bad (batch i))).card : ℝ) < (q - 1 / (s : ℝ)) * (d : ℝ))
    (badBatch.card : ℝ) ≤ ((Fintype.card α : ℝ) ^ d) * Real.exp (-(d : ℝ) / (4 * (s : ℝ) ^ 2)) := by
  intro lam badBatch
  have hlam_pos : 0 < lam := by dsimp only [lam]; positivity
  have hlam_le1 : lam ≤ 1 := by
    dsimp only [lam]
    rw [div_le_one (by positivity)]
    have : (3 : ℝ) ≤ s := by exact_mod_cast hs
    linarith
  have hcard_pos : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
  have hone : ∑ p : α, Real.exp (lam * (if bad p then (1 : ℝ) else 0)) ≤
      (Fintype.card α : ℝ) * Real.exp ((1 - q) * lam + lam ^ 2) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ bad]
    have h1 : ∑ p ∈ Finset.univ.filter bad, Real.exp (lam * (if bad p then (1 : ℝ) else 0)) =
        ((Finset.univ.filter bad).card : ℝ) * Real.exp lam := by
      have hc : ∀ p ∈ Finset.univ.filter bad, Real.exp (lam * (if bad p then (1 : ℝ) else 0)) = Real.exp lam :=
        fun p hp => by rw [if_pos (Finset.mem_filter.mp hp).2, mul_one]
      rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]
    have h2 : ∑ p ∈ Finset.univ.filter (fun p => ¬ bad p), Real.exp (lam * (if bad p then (1 : ℝ) else 0)) =
        ((Finset.univ.filter (fun p => ¬ bad p)).card : ℝ) := by
      have hc : ∀ p ∈ Finset.univ.filter (fun p => ¬ bad p), Real.exp (lam * (if bad p then (1 : ℝ) else 0)) = 1 :=
        fun p hp => by rw [if_neg (Finset.mem_filter.mp hp).2, mul_zero, Real.exp_zero]
      rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [h1, h2]
    have htot : ((Finset.univ.filter bad).card : ℝ) + ((Finset.univ.filter (fun p => ¬ bad p)).card : ℝ) = (Fintype.card α : ℝ) := by
      have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset α)) (p := bad)
      rw [Finset.card_univ] at h; exact_mod_cast h
    have hbad_le : ((Finset.univ.filter bad).card : ℝ) ≤ (1 - q) * (Fintype.card α : ℝ) := by linarith
    have hexp_ge1 : (1 : ℝ) ≤ Real.exp lam := Real.one_le_exp (le_of_lt hlam_pos)
    have hexp_le := exp_le_quad_on_unit lam (le_of_lt hlam_pos) hlam_le1
    have hstep1 : ((Finset.univ.filter bad).card : ℝ) * Real.exp lam + ((Finset.univ.filter (fun p => ¬ bad p)).card : ℝ) ≤
        (Fintype.card α : ℝ) * (1 + (1 - q) * lam + lam ^ 2) := by
      have hrew : ((Finset.univ.filter bad).card : ℝ) * Real.exp lam + ((Finset.univ.filter (fun p => ¬ bad p)).card : ℝ) =
          (Fintype.card α : ℝ) + ((Finset.univ.filter bad).card : ℝ) * (Real.exp lam - 1) := by linarith
      rw [hrew]
      have hbad_nn : 0 ≤ ((Finset.univ.filter bad).card : ℝ) := by positivity
      have hbad_le_tot : ((Finset.univ.filter bad).card : ℝ) ≤ (Fintype.card α : ℝ) := by
        exact_mod_cast Finset.card_le_univ _
      nlinarith
    have hstep2 : 1 + (1 - q) * lam + lam ^ 2 ≤ Real.exp ((1 - q) * lam + lam ^ 2) := by
      linarith [Real.add_one_le_exp ((1 - q) * lam + lam ^ 2)]
    exact hstep1.trans (mul_le_mul_of_nonneg_left hstep2 (le_of_lt hcard_pos))
  have hprod : ∑ batch : Fin d → α, Real.exp (lam * ∑ i : Fin d, (if bad (batch i) then (1 : ℝ) else 0)) ≤
      ((Fintype.card α : ℝ) ^ d) * Real.exp (((1 - q) * lam + lam ^ 2) * (d : ℝ)) := by
    have hfac : ∑ batch : Fin d → α, Real.exp (lam * ∑ i : Fin d, (if bad (batch i) then (1 : ℝ) else 0)) =
        (∑ p : α, Real.exp (lam * (if bad p then (1 : ℝ) else 0))) ^ d := by
      have hterm : ∀ batch : Fin d → α,
          Real.exp (lam * ∑ i : Fin d, (if bad (batch i) then (1 : ℝ) else 0)) =
          ∏ i : Fin d, Real.exp (lam * (if bad (batch i) then (1 : ℝ) else 0)) := fun batch => by
        rw [Finset.mul_sum, Real.exp_sum]
      rw [Finset.sum_congr rfl fun batch _ => hterm batch,
        ← Fintype.prod_sum (fun (_ : Fin d) (p : α) => Real.exp (lam * (if bad p then (1 : ℝ) else 0))),
        Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hfac]
    have hsum_nn : 0 ≤ ∑ p : α, Real.exp (lam * (if bad p then (1 : ℝ) else 0)) :=
      Finset.sum_nonneg fun _ _ => le_of_lt (Real.exp_pos _)
    calc (∑ p : α, Real.exp (lam * (if bad p then (1 : ℝ) else 0))) ^ d
        ≤ ((Fintype.card α : ℝ) * Real.exp ((1 - q) * lam + lam ^ 2)) ^ d := pow_le_pow_left₀ hsum_nn hone d
      _ = (Fintype.card α : ℝ) ^ d * (Real.exp ((1 - q) * lam + lam ^ 2)) ^ d := mul_pow _ _ _
      _ = (Fintype.card α : ℝ) ^ d * Real.exp (((1 - q) * lam + lam ^ 2) * (d : ℝ)) := by
          rw [← Real.exp_nat_mul]; ring_nf
  have hmarkov : (badBatch.card : ℝ) * Real.exp (lam * ((1 - q + 1 / (s : ℝ)) * (d : ℝ))) ≤
      ∑ batch : Fin d → α, Real.exp (lam * ∑ i : Fin d, (if bad (batch i) then (1 : ℝ) else 0)) := by
    calc (badBatch.card : ℝ) * Real.exp (lam * ((1 - q + 1 / (s : ℝ)) * (d : ℝ)))
        = ∑ _batch ∈ badBatch, Real.exp (lam * ((1 - q + 1 / (s : ℝ)) * (d : ℝ))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ batch ∈ badBatch, Real.exp (lam * ∑ i : Fin d, (if bad (batch i) then (1 : ℝ) else 0)) := by
          refine Finset.sum_le_sum fun batch hbatch => Real.exp_le_exp.mpr ?_
          have hlt := (Finset.mem_filter.mp hbatch).2
          have htot : (((Finset.univ : Finset (Fin d)).filter (fun i => bad (batch i))).card : ℝ) +
              (((Finset.univ : Finset (Fin d)).filter (fun i => ¬ bad (batch i))).card : ℝ) = (d : ℝ) := by
            have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin d))) (p := fun i => bad (batch i))
            rw [Finset.card_univ, Fintype.card_fin] at h; exact_mod_cast h
          have hsum_eq : ∑ i : Fin d, (if bad (batch i) then (1 : ℝ) else 0) =
              (((Finset.univ : Finset (Fin d)).filter (fun i => bad (batch i))).card : ℝ) := by
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
          rw [hsum_eq]
          nlinarith
      _ ≤ ∑ batch : Fin d → α, Real.exp (lam * ∑ i : Fin d, (if bad (batch i) then (1 : ℝ) else 0)) :=
          Finset.sum_le_univ_sum_of_nonneg fun _ => le_of_lt (Real.exp_pos _)
  have hcomb := hmarkov.trans hprod
  have hden_pos : 0 < Real.exp (lam * ((1 - q + 1 / (s : ℝ)) * (d : ℝ))) := Real.exp_pos _
  have hfin : (badBatch.card : ℝ) ≤
      (Fintype.card α : ℝ) ^ d *
        (Real.exp (((1 - q) * lam + lam ^ 2) * (d : ℝ)) / Real.exp (lam * ((1 - q + 1 / (s : ℝ)) * (d : ℝ)))) := by
    rw [← mul_div_assoc, le_div_iff₀ hden_pos]
    exact hcomb
  refine hfin.trans (le_of_eq ?_)
  congr 1
  rw [← Real.exp_sub]
  congr 1
  dsimp only [lam]
  have hs_ne : (s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp [hs_ne]; ring

private lemma converse_457 (t k d : ℕ) (ht : 4 ≤ t) (hk : 2 ≤ k)
    (batch : Fin d → (Fin t → Fin 3)) :
    ∃ (G H : Finset {p : Fin t × Fin t // p.1 < p.2}),
      G.card ≤ k ∧ H.card ≤ k ∧ G ≠ H ∧ G.card = 2 ∧ H.card = 2 ∧
      9 * t * ((Finset.univ : Finset (Fin d)).filter
        (fun i => (obs457 t none (batch i)) ^ (k - G.card) * ∏ e ∈ G, obs457 t (some e) (batch i) ≠
          (obs457 t none (batch i)) ^ (k - H.card) * ∏ e ∈ H, obs457 t (some e) (batch i))).card ≤
        (4 * t + 54) * d := by
  let mkPair : (a b : Fin t) → a ≠ b → {p : Fin t × Fin t // p.1 < p.2} := fun a b hab =>
    if h : a < b then ⟨(a, b), h⟩ else ⟨(b, a), lt_of_le_of_ne (not_lt.mp h) hab.symm⟩
  by_cases ht10 : t ≤ 10
  · let e01 : {p : Fin t × Fin t // p.1 < p.2} := ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp⟩
    let e23 : {p : Fin t × Fin t // p.1 < p.2} := ⟨(⟨2, by omega⟩, ⟨3, by omega⟩), by simp⟩
    let e02 : {p : Fin t × Fin t // p.1 < p.2} := ⟨(⟨0, by omega⟩, ⟨2, by omega⟩), by simp⟩
    let e13 : {p : Fin t × Fin t // p.1 < p.2} := ⟨(⟨1, by omega⟩, ⟨3, by omega⟩), by simp⟩
    let G : Finset {p : Fin t × Fin t // p.1 < p.2} := {e01, e23}
    let H : Finset {p : Fin t × Fin t // p.1 < p.2} := {e02, e13}
    have hneG : e01 ≠ e23 := fun h => by have := congrArg (fun x => x.val.1.val) h; dsimp [e01, e23] at this; omega
    have hneH : e02 ≠ e13 := fun h => by have := congrArg (fun x => x.val.1.val) h; dsimp [e02, e13] at this; omega
    have hGc : G.card = 2 := Finset.card_pair hneG
    have hHc : H.card = 2 := Finset.card_pair hneH
    have hGH : G ≠ H := fun heq => by
      have hm : e01 ∈ H := heq ▸ Finset.mem_insert_self e01 {e23}
      rcases Finset.mem_insert.mp hm with h | h
      · have := congrArg (fun x => x.val.2.val) h; dsimp [e01, e02] at this; omega
      · have := congrArg (fun x => x.val.1.val) (Finset.mem_singleton.mp h); dsimp [e01, e13] at this; omega
    refine ⟨G, H, by omega, by omega, hGH, hGc, hHc, ?_⟩
    have hle_d : ((Finset.univ : Finset (Fin d)).filter
        (fun i => (obs457 t none (batch i)) ^ (k - G.card) * ∏ e ∈ G, obs457 t (some e) (batch i) ≠
          (obs457 t none (batch i)) ^ (k - H.card) * ∏ e ∈ H, obs457 t (some e) (batch i))).card ≤ d := by
      have h1 := Finset.card_le_univ ((Finset.univ : Finset (Fin d)).filter
        (fun i => (obs457 t none (batch i)) ^ (k - G.card) * ∏ e ∈ G, obs457 t (some e) (batch i) ≠
          (obs457 t none (batch i)) ^ (k - H.card) * ∏ e ∈ H, obs457 t (some e) (batch i)))
      simpa using h1
    have hmul : 9 * t ≤ 4 * t + 54 := by omega
    calc 9 * t * _ ≤ 9 * t * d := Nat.mul_le_mul_left _ hle_d
      _ ≤ (4 * t + 54) * d := Nat.mul_le_mul_right d hmul
  · have ht11 : 11 ≤ t := by omega
    let Q4 := (Finset.univ : Finset ((Fin t × Fin t) × (Fin t × Fin t))).filter
      (fun q => q.1.1 ≠ q.1.2 ∧ q.1.1 ≠ q.2.1 ∧ q.1.1 ≠ q.2.2 ∧
        q.1.2 ≠ q.2.1 ∧ q.1.2 ≠ q.2.2 ∧ q.2.1 ≠ q.2.2)
    have hQ4_card : Q4.card = t * (t - 1) * (t - 2) * (t - 3) := by
      dsimp only [Q4]
      rw [Finset.card_filter, Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
      have hinner : ∀ a b c : Fin t, a ≠ b → a ≠ c → b ≠ c →
          ∑ d' : Fin t, (if a ≠ b ∧ a ≠ c ∧ a ≠ d' ∧ b ≠ c ∧ b ≠ d' ∧ c ≠ d' then 1 else 0) = t - 3 := by
        intro a b c hab hac hbc
        have hrew : ∀ d' : Fin t,
            (if a ≠ b ∧ a ≠ c ∧ a ≠ d' ∧ b ≠ c ∧ b ≠ d' ∧ c ≠ d' then 1 else 0) =
            (if d' ∈ (((Finset.univ.erase a).erase b).erase c) then 1 else 0) := by
          intro d'; by_cases h : d' ≠ a ∧ d' ≠ b ∧ d' ≠ c
          · rw [if_pos ⟨hab, hac, h.1.symm, hbc, h.2.1.symm, h.2.2.symm⟩, if_pos (by simp [h.1, h.2.1, h.2.2])]
          · rw [if_neg (fun hc => h ⟨hc.2.2.1.symm, hc.2.2.2.2.1.symm, hc.2.2.2.2.2.symm⟩),
              if_neg (by simp only [Finset.mem_erase, Finset.mem_univ, and_true]; tauto)]
        rw [Finset.sum_congr rfl fun d' _ => hrew d', ← Finset.sum_filter]
        have hf : Finset.univ.filter (fun d' => d' ∈ (((Finset.univ.erase a).erase b).erase c)) =
            (((Finset.univ.erase a).erase b).erase c) := by ext d'; simp
        rw [hf, Finset.sum_const, smul_eq_mul, mul_one]
        have hcm : c ∈ (Finset.univ.erase a).erase b := Finset.mem_erase.mpr ⟨hbc.symm, Finset.mem_erase.mpr ⟨hac.symm, Finset.mem_univ _⟩⟩
        have hbm : b ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ _⟩
        rw [Finset.card_erase_of_mem hcm, Finset.card_erase_of_mem hbm, Finset.card_erase_of_mem (Finset.mem_univ a),
          Finset.card_univ, Fintype.card_fin]
        omega
      have hmid : ∀ a b : Fin t, a ≠ b →
          ∑ c : Fin t, ∑ d' : Fin t, (if a ≠ b ∧ a ≠ c ∧ a ≠ d' ∧ b ≠ c ∧ b ≠ d' ∧ c ≠ d' then 1 else 0) =
            (t - 2) * (t - 3) := by
        intro a b hab
        have hterm : ∀ c : Fin t,
            ∑ d' : Fin t, (if a ≠ b ∧ a ≠ c ∧ a ≠ d' ∧ b ≠ c ∧ b ≠ d' ∧ c ≠ d' then 1 else 0) =
            if c ∈ (Finset.univ.erase a).erase b then t - 3 else 0 := by
          intro c
          by_cases hc : c ≠ a ∧ c ≠ b
          · rw [if_pos (by simp [hc.1, hc.2])]; exact hinner a b c hab hc.1.symm hc.2.symm
          · rw [if_neg (by simp only [Finset.mem_erase, Finset.mem_univ, and_true]; tauto)]
            exact Finset.sum_eq_zero fun d' _ => if_neg fun h => hc ⟨h.2.1.symm, h.2.2.2.1.symm⟩
        rw [Finset.sum_congr rfl fun c _ => hterm c, ← Finset.sum_filter]
        have hf : Finset.univ.filter (fun c => c ∈ (Finset.univ.erase a).erase b) = (Finset.univ.erase a).erase b := by ext c; simp
        rw [hf, Finset.sum_const, smul_eq_mul]
        have hbm : b ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ _⟩
        rw [Finset.card_erase_of_mem hbm, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
        rfl
      have hout : ∀ a : Fin t,
          ∑ b : Fin t, ∑ c : Fin t, ∑ d' : Fin t,
            (if a ≠ b ∧ a ≠ c ∧ a ≠ d' ∧ b ≠ c ∧ b ≠ d' ∧ c ≠ d' then 1 else 0) =
          (t - 1) * ((t - 2) * (t - 3)) := by
        intro a
        have hterm : ∀ b : Fin t,
            ∑ c : Fin t, ∑ d' : Fin t, (if a ≠ b ∧ a ≠ c ∧ a ≠ d' ∧ b ≠ c ∧ b ≠ d' ∧ c ≠ d' then 1 else 0) =
            if b ∈ Finset.univ.erase a then (t - 2) * (t - 3) else 0 := by
          intro b
          by_cases hb : b ≠ a
          · rw [if_pos (by simp [hb])]; exact hmid a b hb.symm
          · rw [if_neg (by simp [hb])]
            exact Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d' _ => if_neg fun h => hb h.1.symm
        rw [Finset.sum_congr rfl fun b _ => hterm b, ← Finset.sum_filter]
        have hf : Finset.univ.filter (fun b => b ∈ Finset.univ.erase a) = Finset.univ.erase a := by ext b; simp
        rw [hf, Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
      rw [Finset.sum_congr rfl fun a _ => hout a, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      ring
    have hQ4_pos : 0 < Q4.card := by
      rw [hQ4_card]; exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) (by omega)
    let pairGH : ∀ q : (Fin t × Fin t) × (Fin t × Fin t),
        q ∈ Q4 → Finset {p : Fin t × Fin t // p.1 < p.2} × Finset {p : Fin t × Fin t // p.1 < p.2} := fun q hq =>
      have hm := (Finset.mem_filter.mp hq).2
      ({mkPair q.1.1 q.2.1 hm.2.1, mkPair q.1.2 q.2.2 hm.2.2.2.2.1},
       {mkPair q.1.1 q.2.2 hm.2.2.1, mkPair q.1.2 q.2.1 hm.2.2.2.1})
    have hGH_props : ∀ q (hq : q ∈ Q4),
        let G := (pairGH q hq).1
        let H := (pairGH q hq).2
        G ≠ H ∧ G.card = 2 ∧ H.card = 2 ∧
        ∀ p : Fin t → Fin 3,
          (obs457 t none p) ^ (k - G.card) * ∏ e ∈ G, obs457 t (some e) p ≠
          (obs457 t none p) ^ (k - H.card) * ∏ e ∈ H, obs457 t (some e) p →
          p q.1.1 ≠ p q.1.2 ∧ p q.2.1 ≠ p q.2.2 := by
      intro q hq
      have hm := (Finset.mem_filter.mp hq).2
      rcases q with ⟨⟨a, b⟩, ⟨c, d'⟩⟩
      rcases hm with ⟨hab, hac, had, hbc, hbd, hcd⟩
      dsimp only at hab hac had hbc hbd hcd
      have hmk_set : ∀ (x y : Fin t) (hxy : x ≠ y), ({(mkPair x y hxy).val.1, (mkPair x y hxy).val.2} : Finset (Fin t)) = {x, y} := by
        intro x y hxy; dsimp only [mkPair]; split_ifs
        · rfl
        · exact Finset.pair_comm y x
      have hmk_mul : ∀ (x y : Fin t) (hxy : x ≠ y) (f : Fin t → ℤ),
          f (mkPair x y hxy).val.1 * f (mkPair x y hxy).val.2 = f x * f y := by
        intro x y hxy f; dsimp only [mkPair]; split_ifs
        · rfl
        · ring
      have hneG : mkPair a c hac ≠ mkPair b d' hbd := fun h => by
        have hs := congrArg (fun e : {p : Fin t × Fin t // p.1 < p.2} => ({e.val.1, e.val.2} : Finset (Fin t))) h
        rw [hmk_set a c hac, hmk_set b d' hbd] at hs
        have : a ∈ ({b, d'} : Finset (Fin t)) := hs ▸ Finset.mem_insert_self a {c}
        rcases Finset.mem_insert.mp this with h1 | h1
        · exact hab h1
        · exact had (Finset.mem_singleton.mp h1)
      have hneH : mkPair a d' had ≠ mkPair b c hbc := fun h => by
        have hs := congrArg (fun e : {p : Fin t × Fin t // p.1 < p.2} => ({e.val.1, e.val.2} : Finset (Fin t))) h
        rw [hmk_set a d' had, hmk_set b c hbc] at hs
        have : a ∈ ({b, c} : Finset (Fin t)) := hs ▸ Finset.mem_insert_self a {d'}
        rcases Finset.mem_insert.mp this with h1 | h1
        · exact hab h1
        · exact hac (Finset.mem_singleton.mp h1)
      have hGc : (pairGH ((a, b), (c, d')) hq).1.card = 2 := Finset.card_pair hneG
      have hHc : (pairGH ((a, b), (c, d')) hq).2.card = 2 := Finset.card_pair hneH
      have hGH_ne : (pairGH ((a, b), (c, d')) hq).1 ≠ (pairGH ((a, b), (c, d')) hq).2 := fun h => by
        have hmem : mkPair a c hac ∈ (pairGH ((a, b), (c, d')) hq).2 := h ▸ Finset.mem_insert_self _ _
        rcases Finset.mem_insert.mp hmem with h1 | h1
        · have hs := congrArg (fun e : {p : Fin t × Fin t // p.1 < p.2} => ({e.val.1, e.val.2} : Finset (Fin t))) h1
          rw [hmk_set a c hac, hmk_set a d' had] at hs
          have : c ∈ ({a, d'} : Finset (Fin t)) := hs ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self c)
          rcases Finset.mem_insert.mp this with h2 | h2
          · exact hac h2.symm
          · exact hcd (Finset.mem_singleton.mp h2)
        · have hs := congrArg (fun e : {p : Fin t × Fin t // p.1 < p.2} => ({e.val.1, e.val.2} : Finset (Fin t))) (Finset.mem_singleton.mp h1)
          rw [hmk_set a c hac, hmk_set b c hbc] at hs
          have : a ∈ ({b, c} : Finset (Fin t)) := hs ▸ Finset.mem_insert_self a {c}
          rcases Finset.mem_insert.mp this with h2 | h2
          · exact hab h2
          · exact hac (Finset.mem_singleton.mp h2)
      refine ⟨hGH_ne, hGc, hHc, fun p hne_r => ?_⟩
      by_contra hnot
      apply hne_r
      rw [read_eq_iff_poly t k _ _ (by omega) (by omega) p]
      have hpoly_diff : ∀ f : Fin t → ℤ,
          poly457 t (pairGH ((a, b), (c, d')) hq).1 f - poly457 t (pairGH ((a, b), (c, d')) hq).2 f =
          (f a - f b) * (f c - f d') := by
        intro f
        dsimp only [poly457, pairGH]
        rw [Finset.sum_pair hneG, Finset.sum_pair hneH,
          hmk_mul a c hac f, hmk_mul b d' hbd f, hmk_mul a d' had f, hmk_mul b c hbc f]
        ring
      have hpa : p a = p b ∨ p c = p d' := by tauto
      rcases hpa with h1 | h2
      · constructor
        · apply sub_eq_zero.mp; rw [hpoly_diff]; dsimp only [maskToInt]; rw [h1]; ring
        · apply sub_eq_zero.mp; rw [hpoly_diff]; dsimp only [maskToAbs]; rw [h1]; ring
      · constructor
        · apply sub_eq_zero.mp; rw [hpoly_diff]; dsimp only [maskToInt]; rw [h2]; ring
        · apply sub_eq_zero.mp; rw [hpoly_diff]; dsimp only [maskToAbs]; rw [h2]; ring
    have hone_mask : ∀ p : Fin t → Fin 3,
        9 * (Q4.filter (fun q => p q.1.1 ≠ p q.1.2 ∧ p q.2.1 ≠ p q.2.2)).card ≤ 4 * t ^ 4 := by
      intro p
      have hsub : Q4.filter (fun q => p q.1.1 ≠ p q.1.2 ∧ p q.2.1 ≠ p q.2.2) ⊆
          (Finset.univ.filter (fun ab : Fin t × Fin t => p ab.1 ≠ p ab.2)) ×ˢ
          (Finset.univ.filter (fun cd : Fin t × Fin t => p cd.1 ≠ p cd.2)) := by
        intro q hq
        rcases Finset.mem_filter.mp hq with ⟨_, h1, h2⟩
        exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩⟩
      have hc_le := Finset.card_le_card hsub
      rw [Finset.card_product] at hc_le
      let n0 := (Finset.univ.filter (fun i : Fin t => p i = 0)).card
      let n1 := (Finset.univ.filter (fun i : Fin t => p i = 1)).card
      let n2 := (Finset.univ.filter (fun i : Fin t => p i = 2)).card
      have hn_sum : n0 + n1 + n2 = t := by
        have htot : (Finset.univ : Finset (Fin t)).card = n0 + n1 + n2 := by
          dsimp only [n0, n1, n2]
          have hdisj01 : Disjoint (Finset.univ.filter (fun i : Fin t => p i = 0))
              (Finset.univ.filter (fun i : Fin t => p i = 1)) := by
            rw [Finset.disjoint_left]; intro i h0 h1
            have := (Finset.mem_filter.mp h0).2.symm.trans (Finset.mem_filter.mp h1).2
            exact (by decide : (0 : Fin 3) ≠ 1) this
          have hdisj012 : Disjoint ((Finset.univ.filter (fun i : Fin t => p i = 0)) ∪
              (Finset.univ.filter (fun i : Fin t => p i = 1)))
              (Finset.univ.filter (fun i : Fin t => p i = 2)) := by
            rw [Finset.disjoint_left]; intro i h01 h2
            rcases Finset.mem_union.mp h01 with h0 | h1
            · exact (by decide : (0 : Fin 3) ≠ 2) ((Finset.mem_filter.mp h0).2.symm.trans (Finset.mem_filter.mp h2).2)
            · exact (by decide : (1 : Fin 3) ≠ 2) ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
          have hunion : (Finset.univ : Finset (Fin t)) =
              ((Finset.univ.filter (fun i : Fin t => p i = 0)) ∪
               (Finset.univ.filter (fun i : Fin t => p i = 1))) ∪
               (Finset.univ.filter (fun i : Fin t => p i = 2)) := by
            ext i; simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]
            have := p i; generalize p i = c; fin_cases c <;> simp
          conv_lhs => rw [hunion]
          rw [Finset.card_union_of_disjoint hdisj012, Finset.card_union_of_disjoint hdisj01]
        rw [Finset.card_univ, Fintype.card_fin] at htot; exact htot.symm
      have heq_pairs : ((Finset.univ : Finset (Fin t × Fin t)).filter (fun ab => p ab.1 = p ab.2)).card =
          n0 * n0 + n1 * n1 + n2 * n2 := by
        let S0 := Finset.univ.filter (fun i : Fin t => p i = 0)
        let S1 := Finset.univ.filter (fun i : Fin t => p i = 1)
        let S2 := Finset.univ.filter (fun i : Fin t => p i = 2)
        have hEq : (Finset.univ : Finset (Fin t × Fin t)).filter (fun ab => p ab.1 = p ab.2) =
            (S0 ×ˢ S0 ∪ S1 ×ˢ S1) ∪ S2 ×ˢ S2 := by
          ext ⟨a, b⟩; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_product, S0, S1, S2]
          constructor
          · intro h; generalize hc : p a = c; rw [hc] at h; fin_cases c <;> simp [h.symm]
          · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) <;> rw [h1, h2]
        have hd01 : Disjoint (S0 ×ˢ S0) (S1 ×ˢ S1) := by
          rw [Finset.disjoint_left]; rintro ⟨a, b⟩ h0 h1
          exact (by decide : (0 : Fin 3) ≠ 1) ((Finset.mem_filter.mp (Finset.mem_product.mp h0).1).2.symm.trans
            (Finset.mem_filter.mp (Finset.mem_product.mp h1).1).2)
        have hd012 : Disjoint (S0 ×ˢ S0 ∪ S1 ×ˢ S1) (S2 ×ˢ S2) := by
          rw [Finset.disjoint_left]; rintro ⟨a, b⟩ h01 h2
          rcases Finset.mem_union.mp h01 with h0 | h1
          · exact (by decide : (0 : Fin 3) ≠ 2) ((Finset.mem_filter.mp (Finset.mem_product.mp h0).1).2.symm.trans
              (Finset.mem_filter.mp (Finset.mem_product.mp h2).1).2)
          · exact (by decide : (1 : Fin 3) ≠ 2) ((Finset.mem_filter.mp (Finset.mem_product.mp h1).1).2.symm.trans
              (Finset.mem_filter.mp (Finset.mem_product.mp h2).1).2)
        rw [hEq, Finset.card_union_of_disjoint hd012, Finset.card_union_of_disjoint hd01,
          Finset.card_product, Finset.card_product, Finset.card_product]
      have hpair_le : 3 * ((Finset.univ : Finset (Fin t × Fin t)).filter (fun ab => p ab.1 ≠ p ab.2)).card ≤ 2 * t ^ 2 := by
        have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin t × Fin t)))
          (p := fun ab => p ab.1 = p ab.2)
        rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, heq_pairs] at htot
        have hcs : t ^ 2 ≤ 3 * (n0 * n0 + n1 * n1 + n2 * n2) := by
          zify
          have h1 : (t : ℤ) = (n0 : ℤ) + (n1 : ℤ) + (n2 : ℤ) := by exact_mod_cast hn_sum.symm
          rw [h1]
          nlinarith [sq_nonneg ((n0 : ℤ) - (n1 : ℤ)), sq_nonneg ((n1 : ℤ) - (n2 : ℤ)), sq_nonneg ((n2 : ℤ) - (n0 : ℤ))]
        have hne_eq : (Finset.univ.filter (fun ab : Fin t × Fin t => ¬ p ab.1 = p ab.2)).card =
            (Finset.univ.filter (fun ab : Fin t × Fin t => p ab.1 ≠ p ab.2)).card := rfl
        rw [hne_eq] at htot
        zify at htot hcs ⊢; linarith
      have hsq : 9 * (((Finset.univ : Finset (Fin t × Fin t)).filter (fun ab => p ab.1 ≠ p ab.2)).card *
          ((Finset.univ : Finset (Fin t × Fin t)).filter (fun ab => p ab.1 ≠ p ab.2)).card) ≤ 4 * t ^ 4 := by
        zify at hpair_le ⊢
        nlinarith
      exact (Nat.mul_le_mul_left 9 hc_le).trans hsq
    let distQ : ∀ q ∈ Q4, ℕ := fun q hq =>
      ((Finset.univ : Finset (Fin d)).filter
        (fun i => (obs457 t none (batch i)) ^ (k - (pairGH q hq).1.card) * ∏ e ∈ (pairGH q hq).1, obs457 t (some e) (batch i) ≠
          (obs457 t none (batch i)) ^ (k - (pairGH q hq).2.card) * ∏ e ∈ (pairGH q hq).2, obs457 t (some e) (batch i))).card
    have hsum_le : 9 * ∑ q : Q4, distQ q.1 q.2 ≤ 4 * t ^ 4 * d := by
      have hle1 : ∑ q : Q4, distQ q.1 q.2 ≤
          ∑ q : Q4, ((Finset.univ : Finset (Fin d)).filter (fun i => batch i q.1.1.1 ≠ batch i q.1.1.2 ∧ batch i q.1.2.1 ≠ batch i q.1.2.2)).card := by
        refine Finset.sum_le_sum fun q _ => Finset.card_le_card fun i hi => ?_
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hGH_props q.1 q.2).2.2.2 (batch i) (Finset.mem_filter.mp hi).2⟩
      have hswap : ∑ q : Q4, ((Finset.univ : Finset (Fin d)).filter (fun i => batch i q.1.1.1 ≠ batch i q.1.1.2 ∧ batch i q.1.2.1 ≠ batch i q.1.2.2)).card =
          ∑ i : Fin d, (Q4.filter (fun q => batch i q.1.1 ≠ batch i q.1.2 ∧ batch i q.2.1 ≠ batch i q.2.2)).card := by
        simp_rw [Finset.card_filter]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        exact Finset.sum_coe_sort Q4 (fun q => if batch i q.1.1 ≠ batch i q.1.2 ∧ batch i q.2.1 ≠ batch i q.2.2 then 1 else 0)
      calc 9 * ∑ q : Q4, distQ q.1 q.2
          ≤ 9 * ∑ i : Fin d, (Q4.filter (fun q => batch i q.1.1 ≠ batch i q.1.2 ∧ batch i q.2.1 ≠ batch i q.2.2)).card := by
              rw [← hswap]; exact Nat.mul_le_mul_left 9 hle1
        _ = ∑ i : Fin d, 9 * (Q4.filter (fun q => batch i q.1.1 ≠ batch i q.1.2 ∧ batch i q.2.1 ≠ batch i q.2.2)).card := Finset.mul_sum _ _ _
        _ ≤ ∑ _i : Fin d, (4 * t ^ 4) := Finset.sum_le_sum fun i _ => hone_mask (batch i)
        _ = 4 * t ^ 4 * d := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]
    have hpoly_t : 4 * t ^ 5 ≤ (4 * t + 54) * Q4.card := by
      rw [hQ4_card]
      zify [show 3 ≤ t by omega, show 2 ≤ t by omega, show 1 ≤ t by omega]
      have h11 : (11 : ℤ) ≤ t := by exact_mod_cast ht11
      have hdiff : (4 * (t : ℤ) + 54) * ((t : ℤ) * ((t : ℤ) - 1) * ((t : ℤ) - 2) * ((t : ℤ) - 3)) - 4 * (t : ℤ) ^ 5 =
          (t : ℤ) * (30 * (t : ℤ) ^ 2 * ((t : ℤ) - 10) + 20 * (t : ℤ) ^ 2 + 570 * (t : ℤ) - 324) := by ring
      have ht2 : (0 : ℤ) ≤ (t : ℤ) ^ 2 := sq_nonneg _
      have ht3 : (0 : ℤ) ≤ (t : ℤ) ^ 2 * ((t : ℤ) - 10) := mul_nonneg ht2 (by linarith)
      have hpos_in : (0 : ℤ) ≤ 30 * (t : ℤ) ^ 2 * ((t : ℤ) - 10) + 20 * (t : ℤ) ^ 2 + 570 * (t : ℤ) - 324 := by linarith
      have hprod_nn : (0 : ℤ) ≤ (t : ℤ) * (30 * (t : ℤ) ^ 2 * ((t : ℤ) - 10) + 20 * (t : ℤ) ^ 2 + 570 * (t : ℤ) - 324) :=
        mul_nonneg (by linarith) hpos_in
      linarith
    have havg : ∃ q : Q4, 9 * t * distQ q.1 q.2 ≤ (4 * t + 54) * d := by
      by_contra hall
      push_neg at hall
      have hgt : Q4.card * ((4 * t + 54) * d) < ∑ q : Q4, 9 * t * distQ q.1 q.2 := by
        have hconst : Q4.card * ((4 * t + 54) * d) = ∑ _q : Q4, ((4 * t + 54) * d) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul]
        rw [hconst]
        have hneQ : (Finset.univ : Finset Q4).Nonempty := by
          rcases Finset.card_pos.mp hQ4_pos with ⟨q, hq⟩
          exact ⟨⟨q, hq⟩, Finset.mem_univ _⟩
        exact Finset.sum_lt_sum_of_nonempty hneQ fun q _ => hall q
      have hle_tot : ∑ q : Q4, 9 * t * distQ q.1 q.2 ≤ Q4.card * ((4 * t + 54) * d) := by
        calc ∑ q : Q4, 9 * t * distQ q.1 q.2
            = t * (9 * ∑ q : Q4, distQ q.1 q.2) := by rw [← Finset.mul_sum]; ring
          _ ≤ t * (4 * t ^ 4 * d) := Nat.mul_le_mul_left t hsum_le
          _ = 4 * t ^ 5 * d := by ring
          _ ≤ (4 * t + 54) * Q4.card * d := Nat.mul_le_mul_right d hpoly_t
          _ = Q4.card * ((4 * t + 54) * d) := by ring
      omega
    rcases havg with ⟨⟨q, hq⟩, hq_le⟩
    rcases hGH_props q hq with ⟨hGH_ne, hGc, hHc, _⟩
    exact ⟨(pairGH q hq).1, (pairGH q hq).2, by omega, by omega, hGH_ne, hGc, hHc, hq_le⟩

end PEqualNP.Outside.L_pcx_457

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.L_pcx_457 :
    ∃ C : ℕ, 0 < C ∧ ∀ t k : ℕ, 2 ≤ t →
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
      let Pool := Finset Pair
      let family := (Finset.univ : Finset Pool).filter (fun G => G.card ≤ k)
      let read := fun (G : Pool) (p : Mask) =>
        (obs none p)^(k-G.card) * ∏ e ∈ G, obs (some e) p
      let supp := fun (i : T) (j : Option T) => insert i (j.elim (∅ : Finset T) (fun v => ({v} : Finset T)))
      let factor := fun (x : T → ℤ) (i : T) (j : Option T) => x i - j.elim 0 x
      let poly := fun (G : Pool) (x : T → ℤ) => ∑ e ∈ G, x e.val.1 * x e.val.2
      let simple := fun (G H : Pool) => ∃ (c : ℤ) (i j : T) (v w : Option T),
        c ≠ 0 ∧ v ≠ some i ∧ w ≠ some j ∧ Disjoint (supp i v) (supp j w) ∧
        ∀ x : T → ℤ, poly G x - poly H x = c * factor x i v * factor x j w
      (∀ G ∈ family, ∀ p : Mask,
        let plus := (G.filter (fun e => p e.val.1 ≠ 0 ∧ p e.val.2 ≠ 0 ∧ p e.val.1 = p e.val.2)).card
        let minus := (G.filter (fun e => p e.val.1 ≠ 0 ∧ p e.val.2 ≠ 0 ∧ p e.val.1 ≠ p e.val.2)).card
        4^(plus+minus) * read G p = (obs none p)^k * 5^plus * 3^minus) ∧
      (∀ s : ℕ, 3 ≤ s →
        ∃ (d : ℕ) (batch : Fin d → Mask) (decode : (Fin d → Option ℕ) → Pool),
          0 < d ∧ d ≤ C*s^2*(Nat.log 2 family.card+1) ∧
          (∀ G ∈ family, ∀ H ∈ family, G ≠ H →
            let dist := ((Finset.univ : Finset (Fin d)).filter (fun i =>
              read G (batch i) ≠ read H (batch i))).card
            (4*s-9)*d ≤ 9*s*dist ∧ (¬simple G H → (37*s-81)*d ≤ 81*s*dist)) ∧
          ∀ G ∈ family, ∀ y : Fin d → Option ℕ,
            let erasures := (Finset.univ.filter (fun i : Fin d => y i = none)).card
            let errors := (Finset.univ.filter (fun i : Fin d => y i ≠ none ∧
              y i ≠ some (read G (batch i)))).card
            9*s*(2*errors+erasures) < (4*s-9)*d → decode y = G) ∧
      (4 ≤ t → 2 ≤ k → ∀ (d : ℕ) (batch : Fin d → Mask),
        ∃ G ∈ family, ∃ H ∈ family, G ≠ H ∧ G.card = 2 ∧ H.card = 2 ∧
          9*t*((Finset.univ : Finset (Fin d)).filter
            (fun i => read G (batch i) ≠ read H (batch i))).card ≤ (4*t+54)*d) := by
  classical
  refine ⟨12, by omega, fun t k ht => ?_⟩
  intro T V Pair E Mask tail head weight obs Pool family read supp factor poly simple
  refine ⟨?_, ?_, ?_⟩
  · intro G hG p
    exact PEqualNP.Outside.L_pcx_457.read_formula_457 t k G (Finset.mem_filter.mp hG).2 p
  · intro s hs
    let L := Nat.log 2 family.card + 1
    let d := 12 * s ^ 2 * L
    have hd_pos : 0 < d := Nat.mul_pos (Nat.mul_pos (by omega) (by positivity)) (by omega)
    have hex_batch : ∃ batch : Fin d → Mask,
        ∀ G ∈ family, ∀ H ∈ family, G ≠ H →
          let dist := ((Finset.univ : Finset (Fin d)).filter (fun i => read G (batch i) ≠ read H (batch i))).card
          (4 * s - 9) * d ≤ 9 * s * dist ∧ (¬ simple G H → (37 * s - 81) * d ≤ 81 * s * dist) := by
      let pairs := (family ×ˢ family).filter (fun gh => gh.1 ≠ gh.2)
      let bad1 : Pool × Pool → Finset (Fin d → Mask) := fun gh =>
        (Finset.univ : Finset (Fin d → Mask)).filter (fun batch =>
          (((Finset.univ : Finset (Fin d)).filter (fun i => read gh.1 (batch i) ≠ read gh.2 (batch i))).card : ℝ) <
            (4 / 9 - 1 / (s : ℝ)) * (d : ℝ))
      let bad2 : Pool × Pool → Finset (Fin d → Mask) := fun gh =>
        if simple gh.1 gh.2 then ∅ else
        (Finset.univ : Finset (Fin d → Mask)).filter (fun batch =>
          (((Finset.univ : Finset (Fin d)).filter (fun i => read gh.1 (batch i) ≠ read gh.2 (batch i))).card : ℝ) <
            (37 / 81 - 1 / (s : ℝ)) * (d : ℝ))
      have hbad1_le : ∀ gh ∈ pairs, (bad1 gh).card ≤ ((Fintype.card Mask : ℝ) ^ d) * Real.exp (-(d : ℝ) / (4 * (s : ℝ) ^ 2)) := by
        intro gh hgh
        rcases Finset.mem_filter.mp hgh with ⟨hmem, hne⟩
        rcases Finset.mem_product.mp hmem with ⟨hG, hH⟩
        have hG_le := (Finset.mem_filter.mp hG).2
        have hH_le := (Finset.mem_filter.mp hH).2
        let coef : Pair → ℤ := fun e => (if e ∈ gh.1 then 1 else 0) - (if e ∈ gh.2 then 1 else 0)
        have hcoef_nz : ∃ e0, coef e0 ≠ 0 := by
          by_contra hall; push_neg at hall; apply hne; ext e
          have h0 := hall e; dsimp only [coef] at h0
          by_cases h1 : e ∈ gh.1 <;> by_cases h2 : e ∈ gh.2 <;> simp_all
        have h49 := PEqualNP.Outside.L_pcx_457.quad_nz_ge_four_ninths t coef hcoef_nz
        have hdiff_eq : ∀ p : Mask, PEqualNP.Outside.L_pcx_457.evalQuad t coef (PEqualNP.Outside.L_pcx_457.maskToInt p) ≠ 0 →
            read gh.1 p ≠ read gh.2 p := by
          intro p hnz heq
          have hpoly := (PEqualNP.Outside.L_pcx_457.read_eq_iff_poly t k gh.1 gh.2 hG_le hH_le p).mp heq
          apply hnz
          have heval : PEqualNP.Outside.L_pcx_457.evalQuad t coef (PEqualNP.Outside.L_pcx_457.maskToInt p) =
              PEqualNP.Outside.L_pcx_457.poly457 t gh.1 (PEqualNP.Outside.L_pcx_457.maskToInt p) -
              PEqualNP.Outside.L_pcx_457.poly457 t gh.2 (PEqualNP.Outside.L_pcx_457.maskToInt p) := by
            dsimp only [PEqualNP.Outside.L_pcx_457.evalQuad, PEqualNP.Outside.L_pcx_457.poly457, coef]
            have h1 : ∑ e ∈ gh.1, PEqualNP.Outside.L_pcx_457.maskToInt p e.val.1 * PEqualNP.Outside.L_pcx_457.maskToInt p e.val.2 =
                ∑ e : Pair, if e ∈ gh.1 then PEqualNP.Outside.L_pcx_457.maskToInt p e.val.1 * PEqualNP.Outside.L_pcx_457.maskToInt p e.val.2 else 0 := by
              rw [← Finset.sum_filter]; congr 1; ext e; simp
            have h2 : ∑ e ∈ gh.2, PEqualNP.Outside.L_pcx_457.maskToInt p e.val.1 * PEqualNP.Outside.L_pcx_457.maskToInt p e.val.2 =
                ∑ e : Pair, if e ∈ gh.2 then PEqualNP.Outside.L_pcx_457.maskToInt p e.val.1 * PEqualNP.Outside.L_pcx_457.maskToInt p e.val.2 else 0 := by
              rw [← Finset.sum_filter]; congr 1; ext e; simp
            rw [h1, h2, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun e _ => by by_cases h1' : e ∈ gh.1 <;> by_cases h2' : e ∈ gh.2 <;> simp [h1', h2']
          rw [heval, hpoly.1, sub_self]
        have hcard_ge : 4 * 3 ^ t ≤ 9 * ((Finset.univ : Finset Mask).filter (fun p => ¬ read gh.1 p = read gh.2 p)).card :=
          h49.trans (Nat.mul_le_mul_left 9 (Finset.card_le_card fun p hp =>
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdiff_eq p (Finset.mem_filter.mp hp).2⟩))
        have hq_r : (4 / 9 : ℝ) * (Fintype.card Mask : ℝ) ≤
            (((Finset.univ : Finset Mask).filter (fun p => ¬ read gh.1 p = read gh.2 p)).card : ℝ) := by
          have hc : Fintype.card Mask = 3 ^ t := by simp [Mask, T, Fintype.card_fun, Fintype.card_fin]
          rw [hc]
          have h1 : (4 * (3 ^ t : ℕ) : ℝ) ≤ 9 * (((Finset.univ : Finset Mask).filter (fun p => ¬ read gh.1 p = read gh.2 p)).card : ℝ) := by
            exact_mod_cast hcard_ge
          push_cast at h1 ⊢; linarith
        exact PEqualNP.Outside.L_pcx_457.pair_mgf_bound (fun p => read gh.1 p = read gh.2 p) (4 / 9) hq_r s d hs
      have hbad2_le : ∀ gh ∈ pairs, (bad2 gh).card ≤ ((Fintype.card Mask : ℝ) ^ d) * Real.exp (-(d : ℝ) / (4 * (s : ℝ) ^ 2)) := by
        intro gh hgh
        dsimp only [bad2]
        by_cases hsimp : simple gh.1 gh.2
        · rw [if_pos hsimp, Finset.card_empty, Nat.cast_zero]; positivity
        · rw [if_neg hsimp]
          rcases Finset.mem_filter.mp hgh with ⟨hmem, hne⟩
          rcases Finset.mem_product.mp hmem with ⟨hG, hH⟩
          have hG_le := (Finset.mem_filter.mp hG).2
          have hH_le := (Finset.mem_filter.mp hH).2
          have h37 := PEqualNP.Outside.L_pcx_457.nonsimple_nz_ge_37_81 t gh.1 gh.2 hne hsimp
          have hcard_ge : 37 * 3 ^ t ≤ 81 * ((Finset.univ : Finset Mask).filter (fun p => ¬ read gh.1 p = read gh.2 p)).card :=
            h37.trans (Nat.mul_le_mul_left 81 (Finset.card_le_card fun p hp => by
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun heq => ?_⟩
              have hpoly := (PEqualNP.Outside.L_pcx_457.read_eq_iff_poly t k gh.1 gh.2 hG_le hH_le p).mp heq
              rcases (Finset.mem_filter.mp hp).2 with h1 | h2
              · exact h1 hpoly.1
              · exact h2 hpoly.2))
          have hq_r : (37 / 81 : ℝ) * (Fintype.card Mask : ℝ) ≤
              (((Finset.univ : Finset Mask).filter (fun p => ¬ read gh.1 p = read gh.2 p)).card : ℝ) := by
            have hc : Fintype.card Mask = 3 ^ t := by simp [Mask, T, Fintype.card_fun, Fintype.card_fin]
            rw [hc]
            have h1 : (37 * (3 ^ t : ℕ) : ℝ) ≤ 81 * (((Finset.univ : Finset Mask).filter (fun p => ¬ read gh.1 p = read gh.2 p)).card : ℝ) := by
              exact_mod_cast hcard_ge
            push_cast at h1 ⊢; linarith
          exact PEqualNP.Outside.L_pcx_457.pair_mgf_bound (fun p => read gh.1 p = read gh.2 p) (37 / 81) hq_r s d hs
      let badAll := pairs.biUnion bad1 ∪ pairs.biUnion bad2
      have hbadAll_lt : (badAll.card : ℝ) < (Fintype.card Mask : ℝ) ^ d := by
        have hle1 : (badAll.card : ℝ) ≤ ∑ gh ∈ pairs, ((bad1 gh).card : ℝ) + ∑ gh ∈ pairs, ((bad2 gh).card : ℝ) := by
          have hnat : badAll.card ≤ (∑ gh ∈ pairs, (bad1 gh).card) + (∑ gh ∈ pairs, (bad2 gh).card) :=
            (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_biUnion_le Finset.card_biUnion_le)
          exact_mod_cast hnat
        have hle2 : ∑ gh ∈ pairs, ((bad1 gh).card : ℝ) + ∑ gh ∈ pairs, ((bad2 gh).card : ℝ) ≤
            2 * (pairs.card : ℝ) * (((Fintype.card Mask : ℝ) ^ d) * Real.exp (-(d : ℝ) / (4 * (s : ℝ) ^ 2))) := by
          have ha : ∑ gh ∈ pairs, ((bad1 gh).card : ℝ) ≤ (pairs.card : ℝ) * (((Fintype.card Mask : ℝ) ^ d) * Real.exp (-(d : ℝ) / (4 * (s : ℝ) ^ 2))) := by
            calc _ ≤ ∑ _gh ∈ pairs, _ := Finset.sum_le_sum hbad1_le
              _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
          have hb : ∑ gh ∈ pairs, ((bad2 gh).card : ℝ) ≤ (pairs.card : ℝ) * (((Fintype.card Mask : ℝ) ^ d) * Real.exp (-(d : ℝ) / (4 * (s : ℝ) ^ 2))) := by
            calc _ ≤ ∑ _gh ∈ pairs, _ := Finset.sum_le_sum hbad2_le
              _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
          linarith
        have hpairs_le : pairs.card ≤ family.card ^ 2 := by
          have h1 : pairs.card ≤ (family ×ˢ family).card := Finset.card_le_card (Finset.filter_subset _ _)
          rw [Finset.card_product, ← sq] at h1; exact h1
        have hfam_lt : family.card < 2 ^ L := by
          by_cases h0 : family.card = 0
          · rw [h0]; positivity
          · exact Nat.lt_pow_succ_log_self (by omega) family.card
        have hexp_eq : -(d : ℝ) / (4 * (s : ℝ) ^ 2) = -3 * (L : ℝ) := by
          dsimp only [d]; push_cast
          have hs_ne : (s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          field_simp [hs_ne]; ring
        have h2p_lt : 2 * (pairs.card : ℝ) * Real.exp (-3 * (L : ℝ)) < 1 := by
          have hp_lt : (pairs.card : ℝ) < (4 : ℝ) ^ L := by
            have hnat : pairs.card < 4 ^ L := by
              calc pairs.card ≤ family.card ^ 2 := hpairs_le
                _ < (2 ^ L) ^ 2 := Nat.pow_lt_pow_left hfam_lt (by omega)
                _ = 4 ^ L := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
            exact_mod_cast hnat
          have he3 : (8 : ℝ) ≤ Real.exp 3 := by
            have h1 := Real.sum_le_exp_of_nonneg (x := (3 : ℝ)) (by norm_num) 4
            rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one] at h1
            norm_num at h1; linarith
          have he3L : (8 : ℝ) ^ L ≤ Real.exp (3 * (L : ℝ)) := by
            rw [mul_comm, Real.exp_nat_mul]
            exact pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8) he3 L
          have hinv : Real.exp (-3 * (L : ℝ)) = (Real.exp (3 * (L : ℝ)))⁻¹ := by
            rw [← Real.exp_neg]; congr 1; ring
          rw [hinv, mul_inv_lt_iff₀ (Real.exp_pos _), one_mul]
          have h2_4 : 2 * (4 : ℝ) ^ L ≤ (8 : ℝ) ^ L := by
            have hL1 : 1 ≤ L := by dsimp only [L]; omega
            calc 2 * (4 : ℝ) ^ L ≤ (2 : ℝ) ^ L * (4 : ℝ) ^ L := by
                  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                  calc (2 : ℝ) = 2 ^ 1 := by norm_num
                    _ ≤ (2 : ℝ) ^ L := by exact_mod_cast Nat.pow_le_pow_right (by omega) hL1
              _ = (8 : ℝ) ^ L := by rw [← mul_pow]; norm_num
          linarith
        have hM_pos : (0 : ℝ) < (Fintype.card Mask : ℝ) ^ d := by
          have : 0 < Fintype.card Mask := Fintype.card_pos
          positivity
        rw [hexp_eq] at hle2
        calc (badAll.card : ℝ)
            ≤ 2 * (pairs.card : ℝ) * Real.exp (-3 * (L : ℝ)) * (Fintype.card Mask : ℝ) ^ d := by linarith
          _ < 1 * (Fintype.card Mask : ℝ) ^ d := mul_lt_mul_of_pos_right h2p_lt hM_pos
          _ = (Fintype.card Mask : ℝ) ^ d := one_mul _
      have hex_good : ∃ batch : Fin d → Mask, batch ∉ badAll := by
        by_contra hall
        push_neg at hall
        have huniv : badAll = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
        rw [huniv, Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at hbadAll_lt
        push_cast at hbadAll_lt
        exact lt_irrefl _ hbadAll_lt
      rcases hex_good with ⟨batch, hbatch⟩
      refine ⟨batch, fun G hG H hH hne => ?_⟩
      have hpair_mem : (G, H) ∈ pairs := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hG, hH⟩, hne⟩
      have hnot1 : batch ∉ bad1 (G, H) := fun hm => hbatch (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨(G, H), hpair_mem, hm⟩))
      have hnot2 : batch ∉ bad2 (G, H) := fun hm => hbatch (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨(G, H), hpair_mem, hm⟩))
      have hge1 : (4 / 9 - 1 / (s : ℝ)) * (d : ℝ) ≤
          (((Finset.univ : Finset (Fin d)).filter (fun i => read G (batch i) ≠ read H (batch i))).card : ℝ) := by
        by_contra hlt; push_neg at hlt
        exact hnot1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
      constructor
      · have hs_pos : (0 : ℝ) < s := Nat.cast_pos.mpr (by omega)
        have hmul : (4 * (s : ℝ) - 9) * (d : ℝ) ≤ 9 * (s : ℝ) *
            (((Finset.univ : Finset (Fin d)).filter (fun i => read G (batch i) ≠ read H (batch i))).card : ℝ) := by
          have h1 := mul_le_mul_of_nonneg_left hge1 (by positivity : (0 : ℝ) ≤ 9 * s)
          have hrew : 9 * (s : ℝ) * ((4 / 9 - 1 / (s : ℝ)) * (d : ℝ)) = (4 * (s : ℝ) - 9) * (d : ℝ) := by
            field_simp [ne_of_gt hs_pos]
          linarith
        have h9le : 9 ≤ 4 * s := by omega
        have hnat_r : (((4 * s - 9) * d : ℕ) : ℝ) ≤ ((9 * s * ((Finset.univ : Finset (Fin d)).filter (fun i => read G (batch i) ≠ read H (batch i))).card : ℕ) : ℝ) := by
          push_cast [Nat.cast_sub h9le]; exact hmul
        exact_mod_cast hnat_r
      · intro hns
        have hge2 : (37 / 81 - 1 / (s : ℝ)) * (d : ℝ) ≤
            (((Finset.univ : Finset (Fin d)).filter (fun i => read G (batch i) ≠ read H (batch i))).card : ℝ) := by
          by_contra hlt; push_neg at hlt
          apply hnot2; dsimp only [bad2]; rw [if_neg hns]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
        have hs_pos : (0 : ℝ) < s := Nat.cast_pos.mpr (by omega)
        have hmul : (37 * (s : ℝ) - 81) * (d : ℝ) ≤ 81 * (s : ℝ) *
            (((Finset.univ : Finset (Fin d)).filter (fun i => read G (batch i) ≠ read H (batch i))).card : ℝ) := by
          have h1 := mul_le_mul_of_nonneg_left hge2 (by positivity : (0 : ℝ) ≤ 81 * s)
          have hrew : 81 * (s : ℝ) * ((37 / 81 - 1 / (s : ℝ)) * (d : ℝ)) = (37 * (s : ℝ) - 81) * (d : ℝ) := by
            field_simp [ne_of_gt hs_pos]
          linarith
        have h81le : 81 ≤ 37 * s := by omega
        have hnat_r : (((37 * s - 81) * d : ℕ) : ℝ) ≤ ((81 * s * ((Finset.univ : Finset (Fin d)).filter (fun i => read G (batch i) ≠ read H (batch i))).card : ℕ) : ℝ) := by
          push_cast [Nat.cast_sub h81le]; exact hmul
        exact_mod_cast hnat_r
    rcases hex_batch with ⟨batch, hbatch⟩
    let decode : (Fin d → Option ℕ) → Pool := fun y =>
      let eras := (Finset.univ.filter (fun i : Fin d => y i = none)).card
      if h : ∃ H ∈ family, 9 * s * (2 * (Finset.univ.filter (fun i : Fin d =>
          y i ≠ none ∧ y i ≠ some (read H (batch i)))).card + eras) < (4 * s - 9) * d then
        Classical.choose h
      else ∅
    refine ⟨d, batch, decode, hd_pos, le_rfl, hbatch, fun G hG y herr => ?_⟩
    have hex : ∃ H ∈ family, 9 * s * (2 * (Finset.univ.filter (fun i : Fin d =>
        y i ≠ none ∧ y i ≠ some (read H (batch i)))).card +
        (Finset.univ.filter (fun i : Fin d => y i = none)).card) < (4 * s - 9) * d :=
      ⟨G, hG, herr⟩
    dsimp only [decode]
    rw [dif_pos hex]
    set H := Classical.choose hex
    have hH_spec := Classical.choose_spec hex
    by_contra hne
    have hdist := (hbatch G hG H hH_spec.1 (Ne.symm hne)).1
    have htri : ((Finset.univ : Finset (Fin d)).filter (fun i => read G (batch i) ≠ read H (batch i))).card ≤
        (Finset.univ.filter (fun i : Fin d => y i = none)).card +
        (Finset.univ.filter (fun i : Fin d => y i ≠ none ∧ y i ≠ some (read G (batch i)))).card +
        (Finset.univ.filter (fun i : Fin d => y i ≠ none ∧ y i ≠ some (read H (batch i)))).card := by
      have hsub : (Finset.univ : Finset (Fin d)).filter (fun i => read G (batch i) ≠ read H (batch i)) ⊆
          ((Finset.univ.filter (fun i : Fin d => y i = none)) ∪
           (Finset.univ.filter (fun i : Fin d => y i ≠ none ∧ y i ≠ some (read G (batch i))))) ∪
           (Finset.univ.filter (fun i : Fin d => y i ≠ none ∧ y i ≠ some (read H (batch i)))) := by
        intro i hi
        have hne_i := (Finset.mem_filter.mp hi).2
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hyn : y i = none
        · left; left; exact hyn
        · by_cases hyG : y i = some (read G (batch i))
          · right; exact ⟨hyn, fun hyH => hne_i (Option.some.inj (hyG.symm.trans hyH))⟩
          · left; right; exact ⟨hyn, hyG⟩
      exact (Finset.card_le_card hsub).trans
        ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    have hmul_tri : 2 * (9 * s * ((Finset.univ : Finset (Fin d)).filter (fun i => read G (batch i) ≠ read H (batch i))).card) ≤
        9 * s * (2 * (Finset.univ.filter (fun i : Fin d => y i ≠ none ∧ y i ≠ some (read G (batch i)))).card +
          (Finset.univ.filter (fun i : Fin d => y i = none)).card) +
        9 * s * (2 * (Finset.univ.filter (fun i : Fin d => y i ≠ none ∧ y i ≠ some (read H (batch i)))).card +
          (Finset.univ.filter (fun i : Fin d => y i = none)).card) := by
      have h1 : 2 * ((Finset.univ : Finset (Fin d)).filter (fun i => read G (batch i) ≠ read H (batch i))).card ≤
          (2 * (Finset.univ.filter (fun i : Fin d => y i ≠ none ∧ y i ≠ some (read G (batch i)))).card +
            (Finset.univ.filter (fun i : Fin d => y i = none)).card) +
          (2 * (Finset.univ.filter (fun i : Fin d => y i ≠ none ∧ y i ≠ some (read H (batch i)))).card +
            (Finset.univ.filter (fun i : Fin d => y i = none)).card) := by omega
      have h2 := Nat.mul_le_mul_left (9 * s) h1
      linarith
    have hH_err : 9 * s * (2 * (Finset.univ.filter (fun i : Fin d => y i ≠ none ∧ y i ≠ some (read H (batch i)))).card +
        (Finset.univ.filter (fun i : Fin d => y i = none)).card) < (4 * s - 9) * d := by
      convert hH_spec.2
    have hG_err : 9 * s * (2 * (Finset.univ.filter (fun i : Fin d => y i ≠ none ∧ y i ≠ some (read G (batch i)))).card +
        (Finset.univ.filter (fun i : Fin d => y i = none)).card) < (4 * s - 9) * d := by
      convert herr
    have hdist' : (4 * s - 9) * d ≤ 9 * s * ((Finset.univ : Finset (Fin d)).filter (fun i => read G (batch i) ≠ read H (batch i))).card := by
      convert hdist
    omega
  · intro ht4 hk2 d batch
    rcases PEqualNP.Outside.L_pcx_457.converse_457 t k d ht4 hk2 batch with ⟨G, H, hGk, hHk, hGH, hGc, hHc, hle⟩
    exact ⟨G, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hGk⟩,
      H, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hHk⟩, hGH, hGc, hHc, hle⟩
