import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1181_aux

open scoped Classical
open PEqualNP.CircuitLowerBounds (Circuit Gate GateOp)

/-! ### Part 0: Small Boolean order helpers -/

lemma bool_true_le_eq {b : Bool} (h : true ≤ b) : b = true := by
  cases b
  · exact absurd h (by decide)
  · rfl

lemma bool_le_false_eq {b : Bool} (h : b ≤ false) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

lemma bool_eq_of_le_not {a b : Bool} (h1 : a ≤ b) (h2 : (!a) ≤ (!b)) : a = b := by
  revert h1 h2
  cases a <;> cases b <;> decide

/-! ### Part 1: Wire evaluation and Markov negation-chain lower bound -/

def evalWires (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def isNotOp : GateOp → Bool
  | GateOp.not => true
  | _ => false

lemma isNotOp_eq_decide (op : GateOp) : isNotOp op = decide (op = GateOp.not) := by
  cases op <;> simp [isNotOp]

def notCountL (gs : List Gate) : ℕ :=
  (gs.filter fun g => isNotOp g.op).length

lemma notCountL_eq_notCount (C : Circuit) :
    notCountL C.gates = PEqualNP.NotBracket.notCount C := by
  unfold notCountL PEqualNP.NotBracket.notCount
  congr 1
  apply List.filter_congr
  intro g _
  cases g.op <;> simp [isNotOp]

def notCode : List Gate → List Bool → ℕ
  | [], _ => 0
  | g :: gs, w =>
    let val := g.op.eval (g.inputs.map fun i => w.getD i false)
    let rest := notCode gs (w ++ [val])
    if isNotOp g.op then
      (if val then 1 else 0) * 2 ^ (notCountL gs) + rest
    else
      rest

lemma notCountL_cons_not (g : Gate) (gs : List Gate) (h : isNotOp g.op = true) :
    notCountL (g :: gs) = notCountL gs + 1 := by
  simp [notCountL, h]

lemma notCountL_cons_ne (g : Gate) (gs : List Gate) (h : isNotOp g.op = false) :
    notCountL (g :: gs) = notCountL gs := by
  simp [notCountL, h]

lemma notCountL_append (gs1 gs2 : List Gate) :
    notCountL (gs1 ++ gs2) = notCountL gs1 + notCountL gs2 := by
  simp [notCountL, List.filter_append]

lemma notCode_lt : ∀ (gs : List Gate) (w : List Bool), notCode gs w < 2 ^ notCountL gs
  | [], _ => by simp [notCode, notCountL]
  | g :: gs, w => by
    have ih := notCode_lt gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    dsimp only [notCode]
    cases h : isNotOp g.op
    · simp only [Bool.false_eq_true, ↓reduceIte, notCountL_cons_ne g gs h]
      exact ih
    · simp only [↓reduceIte, notCountL_cons_not g gs h, pow_succ]
      generalize g.op.eval (g.inputs.map fun i => w.getD i false) = v at ih ⊢
      cases v <;> simp <;> omega

lemma getD_append_singleton {α : Type*} (w : List α) (a d : α) (i : ℕ) :
    (w ++ [a]).getD i d = if i < w.length then w.getD i d else if i = w.length then a else d := by
  by_cases h1 : i < w.length
  · rw [if_pos h1, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left h1]
  · rw [if_neg h1]
    have hge : w.length ≤ i := Nat.le_of_not_lt h1
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hge]
    by_cases h2 : i = w.length
    · subst h2; simp
    · rw [if_neg h2]
      have hgt : 1 ≤ i - w.length := by omega
      rw [List.getElem?_eq_none (by simp; omega)]
      rfl

lemma getD_append_le {wa wb : List Bool} (hlen : wa.length = wb.length)
    (hle : ∀ i, wa.getD i false ≤ wb.getD i false) {va vb : Bool} (hv : va ≤ vb) :
    ∀ i, (wa ++ [va]).getD i false ≤ (wb ++ [vb]).getD i false := by
  intro i
  rw [getD_append_singleton, getD_append_singleton, hlen]
  by_cases h1 : i < wb.length
  · rw [if_pos h1, if_pos h1]; exact hle i
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : i = wb.length
    · rw [if_pos h2, if_pos h2]; exact hv
    · rw [if_neg h2, if_neg h2]

lemma eval_and_mono (l : List ℕ) (wa wb : List Bool)
    (hle : ∀ i, wa.getD i false ≤ wb.getD i false) :
    GateOp.and.eval (l.map fun i => wa.getD i false) ≤
    GateOp.and.eval (l.map fun i => wb.getD i false) := by
  dsimp only [GateOp.eval]
  cases ha : (l.map fun i => wa.getD i false).all id
  · exact Bool.false_le _
  · have hb : (l.map fun i => wb.getD i false).all id = true := by
      rw [List.all_eq_true] at ha ⊢
      intro x hx
      rcases List.mem_map.mp hx with ⟨i, hi, rfl⟩
      have h1 : wa.getD i false = true := ha (wa.getD i false) (List.mem_map.mpr ⟨i, hi, rfl⟩)
      exact bool_true_le_eq (h1 ▸ hle i)
    rw [hb]

lemma eval_or_mono (l : List ℕ) (wa wb : List Bool)
    (hle : ∀ i, wa.getD i false ≤ wb.getD i false) :
    GateOp.or.eval (l.map fun i => wa.getD i false) ≤
    GateOp.or.eval (l.map fun i => wb.getD i false) := by
  dsimp only [GateOp.eval]
  cases ha : (l.map fun i => wa.getD i false).any id
  · exact Bool.false_le _
  · have hb : (l.map fun i => wb.getD i false).any id = true := by
      rw [List.any_eq_true] at ha ⊢
      rcases ha with ⟨x, hx, hxt⟩
      rcases List.mem_map.mp hx with ⟨i, hi, rfl⟩
      refine ⟨wb.getD i false, List.mem_map.mpr ⟨i, hi, rfl⟩, ?_⟩
      exact bool_true_le_eq (hxt ▸ hle i)
    rw [hb]

lemma eval_not_anti (l : List ℕ) (wa wb : List Bool)
    (hle : ∀ i, wa.getD i false ≤ wb.getD i false) :
    GateOp.not.eval (l.map fun i => wb.getD i false) ≤
    GateOp.not.eval (l.map fun i => wa.getD i false) := by
  cases l with
  | nil => simp [GateOp.eval]
  | cons i _ =>
    simp only [GateOp.eval, List.map_cons, List.headD_cons]
    have h := hle i
    generalize wa.getD i false = a at h ⊢
    generalize wb.getD i false = b at h ⊢
    revert h
    cases a <;> cases b <;> decide

lemma notCode_step : ∀ (gs : List Gate),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) →
    ∀ (wa wb : List Bool), wa.length = wb.length →
    (∀ i, wa.getD i false ≤ wb.getD i false) →
    (notCode gs wb < notCode gs wa) ∨
    (notCode gs wb = notCode gs wa ∧
      ∀ i, (evalWires gs wa).getD i false ≤ (evalWires gs wb).getD i false)
  | [], _, wa, wb, _, hle => Or.inr ⟨rfl, hle⟩
  | g :: gs, hfit, wa, wb, hlen, hle => by
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
      have hm := hfit g (List.mem_cons_self ..)
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hm
    have hfit' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) :=
      fun g' hg' => hfit g' (List.mem_cons_of_mem g hg')
    set va := g.op.eval (g.inputs.map fun i => wa.getD i false)
    set vb := g.op.eval (g.inputs.map fun i => wb.getD i false)
    have hlen' : (wa ++ [va]).length = (wb ++ [vb]).length := by simp [hlen]
    rcases hg with hand | hor | hnot
    · have hv : va ≤ vb := by
        dsimp only [va, vb]; rw [hand]; exact eval_and_mono g.inputs wa wb hle
      have hle' := getD_append_le hlen hle hv
      have hne : isNotOp g.op = false := by rw [hand]; rfl
      have ih := notCode_step gs hfit' (wa ++ [va]) (wb ++ [vb]) hlen' hle'
      simpa [notCode, evalWires, hne, va, vb] using ih
    · have hv : va ≤ vb := by
        dsimp only [va, vb]; rw [hor]; exact eval_or_mono g.inputs wa wb hle
      have hle' := getD_append_le hlen hle hv
      have hne : isNotOp g.op = false := by rw [hor]; rfl
      have ih := notCode_step gs hfit' (wa ++ [va]) (wb ++ [vb]) hlen' hle'
      simpa [notCode, evalWires, hne, va, vb] using ih
    · have hv_anti : vb ≤ va := by
        dsimp only [va, vb]; rw [hnot]; exact eval_not_anti g.inputs wa wb hle
      have hyes : isNotOp g.op = true := by rw [hnot]; rfl
      by_cases heq : va = vb
      · have hle' := getD_append_le hlen hle (le_of_eq heq)
        have ih := notCode_step gs hfit' (wa ++ [va]) (wb ++ [vb]) hlen' hle'
        dsimp only [notCode]
        rw [hyes]
        change (if vb then 1 else 0) * 2 ^ notCountL gs + notCode gs (wb ++ [vb]) <
            (if va then 1 else 0) * 2 ^ notCountL gs + notCode gs (wa ++ [va]) ∨
            ((if vb then 1 else 0) * 2 ^ notCountL gs + notCode gs (wb ++ [vb]) =
              (if va then 1 else 0) * 2 ^ notCountL gs + notCode gs (wa ++ [va]) ∧
              ∀ i, (evalWires gs (wa ++ [va])).getD i false ≤ (evalWires gs (wb ++ [vb])).getD i false)
        rw [heq] at ih ⊢
        rcases ih with hlt | ⟨heq', hw⟩
        · exact Or.inl (Nat.add_lt_add_left hlt _)
        · exact Or.inr ⟨by rw [heq'], hw⟩
      · have hva : va = true := by
          revert hv_anti heq; cases va <;> cases vb <;> decide
        have hvb : vb = false := by
          revert hv_anti heq; cases va <;> cases vb <;> decide
        left
        dsimp only [notCode]
        rw [hyes]
        change (if vb then 1 else 0) * 2 ^ notCountL gs + notCode gs (wb ++ [vb]) <
            (if va then 1 else 0) * 2 ^ notCountL gs + notCode gs (wa ++ [va])
        rw [hva, hvb]
        have hltb := notCode_lt gs (wb ++ [false])
        simp only [Bool.false_eq_true, ↓reduceIte, zero_mul, zero_add, one_mul]
        omega

lemma chain_card_lt_two_pow {n r : ℕ} (G H : Finset (Fin n × Fin n))
    (hltG : ∀ e ∈ G, e.1 < e.2) (hHG : H ⊆ G)
    (C : Circuit) (tap : ↥H → Fin (n + 2 + C.size))
    (hfit : PEqualNP.MetaComplexity.FanInTwo C)
    (hnot : PEqualNP.NotBracket.notCount C ≤ r)
    (hspec : ∀ x : Fin n → Bool,
      let inputs := List.ofFn x ++ [false, true]
      (C.eval inputs = true ↔ ∀ e ∈ G, x e.1 = true ∨ x e.2 = true) ∧
      ((∀ e ∈ G, x e.1 = true ∨ x e.2 = true) →
        ∀ e, (C.wires inputs).getD (tap e).val false = xor (x e.val.1) (x e.val.2)))
    (S : Finset (Fin n))
    (hsub : S ⊆ H.image Prod.fst ∪ H.image Prod.snd)
    (hind : ∀ e ∈ G, ¬(e.1 ∈ S ∧ e.2 ∈ S)) :
    S.card < 2 ^ r := by
  let m := S.card
  let eS : Fin m ≃ {u // u ∈ S} := (Fintype.equivFinOfCardEq (by simp [m])).symm
  let X : ℕ → (Fin n → Bool) := fun t u =>
    decide (u ∉ S ∨ ∃ i : Fin m, i.val < t ∧ (eS i).val = u)
  let inp : ℕ → List Bool := fun t => List.ofFn (X t) ++ [false, true]
  have hX_cov : ∀ t : ℕ, ∀ e ∈ G, X t e.1 = true ∨ X t e.2 = true := by
    intro t e he
    by_cases h1 : e.1 ∈ S
    · right
      have h2 : e.2 ∉ S := fun h2 => hind e he ⟨h1, h2⟩
      simp [X, h2]
    · left; simp [X, h1]
  have hX_mono : ∀ t : ℕ, ∀ i : ℕ, (inp t).getD i false ≤ (inp (t + 1)).getD i false := by
    intro t i
    dsimp only [inp]
    by_cases hi : i < n
    · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by simp [hi]), List.getElem?_append_left (by simp [hi]),
        List.getElem?_ofFn, List.getElem?_ofFn, dif_pos hi, dif_pos hi]
      dsimp only [Option.getD, X]
      by_cases hp : (⟨i, hi⟩ : Fin n) ∉ S ∨ ∃ j : Fin m, j.val < t ∧ (eS j).val = ⟨i, hi⟩
      · have hp' : (⟨i, hi⟩ : Fin n) ∉ S ∨ ∃ j : Fin m, j.val < t + 1 ∧ (eS j).val = ⟨i, hi⟩ := by
          rcases hp with h1 | ⟨j, hj, heq⟩
          · exact Or.inl h1
          · exact Or.inr ⟨j, by omega, heq⟩
        rw [decide_eq_true hp, decide_eq_true hp']
      · rw [decide_eq_false hp]; exact Bool.false_le _
    · have hge : (List.ofFn (X t)).length ≤ i := by simp; omega
      have hge' : (List.ofFn (X (t + 1))).length ≤ i := by simp; omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_right hge, List.getElem?_append_right hge']
      simp
  have hfit_op : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) :=
    fun g hg => (hfit g hg).1
  have hdec_step : ∀ t : ℕ, t < m → notCode C.gates (inp (t + 1)) < notCode C.gates (inp t) := by
    intro t ht
    have hlen : (inp t).length = (inp (t + 1)).length := by simp [inp]
    rcases notCode_step C.gates hfit_op (inp t) (inp (t + 1)) hlen (hX_mono t) with hlt | ⟨_, hwire⟩
    · exact hlt
    · exfalso
      let w : Fin n := (eS ⟨t, ht⟩).val
      have hwS : w ∈ S := (eS ⟨t, ht⟩).property
      have hw_act : w ∈ H.image Prod.fst ∪ H.image Prod.snd := hsub hwS
      have hex_e : ∃ e ∈ H, e.1 = w ∨ e.2 = w := by
        rcases Finset.mem_union.mp hw_act with h1 | h2
        · rcases Finset.mem_image.mp h1 with ⟨e, heH, heq⟩; exact ⟨e, heH, Or.inl heq⟩
        · rcases Finset.mem_image.mp h2 with ⟨e, heH, heq⟩; exact ⟨e, heH, Or.inr heq⟩
      rcases hex_e with ⟨e, heH, hwe⟩
      have heG : e ∈ G := hHG heH
      have hXt_w : X t w = false := by
        dsimp only [X]
        rw [decide_eq_false_iff_not]
        rintro (hnot | ⟨j, hj, heq⟩)
        · exact hnot hwS
        · have hj_eq : j = ⟨t, ht⟩ := eS.injective (Subtype.ext heq)
          have hval := congrArg Fin.val hj_eq
          dsimp at hval; omega
      have hXt1_w : X (t + 1) w = true := by
        dsimp only [X]
        exact decide_eq_true (Or.inr ⟨⟨t, ht⟩, Nat.lt_succ_self t, rfl⟩)
      have hxor_t : xor (X t e.1) (X t e.2) = true := by
        rcases hwe with h1 | h2
        · have h2notS : e.2 ∉ S := fun h2S => hind e heG ⟨h1 ▸ hwS, h2S⟩
          have hXt2 : X t e.2 = true := decide_eq_true (Or.inl h2notS)
          rw [h1, hXt_w, hXt2]; rfl
        · have h1notS : e.1 ∉ S := fun h1S => hind e heG ⟨h1S, h2 ▸ hwS⟩
          have hXt1 : X t e.1 = true := decide_eq_true (Or.inl h1notS)
          rw [h2, hXt_w, hXt1]; rfl
      have hxor_t1 : xor (X (t + 1) e.1) (X (t + 1) e.2) = false := by
        rcases hwe with h1 | h2
        · have h2notS : e.2 ∉ S := fun h2S => hind e heG ⟨h1 ▸ hwS, h2S⟩
          have hXt2 : X (t + 1) e.2 = true := decide_eq_true (Or.inl h2notS)
          rw [h1, hXt1_w, hXt2]; rfl
        · have h1notS : e.1 ∉ S := fun h1S => hind e heG ⟨h1S, h2 ▸ hwS⟩
          have hXt1 : X (t + 1) e.1 = true := decide_eq_true (Or.inl h1notS)
          rw [h2, hXt1_w, hXt1]; rfl
      have htap_t := (hspec (X t)).2 (hX_cov t) ⟨e, heH⟩
      have htap_t1 := (hspec (X (t + 1))).2 (hX_cov (t + 1)) ⟨e, heH⟩
      have hle_tap := hwire (tap ⟨e, heH⟩).val
      change (C.wires (inp t)).getD (tap ⟨e, heH⟩).val false ≤
          (C.wires (inp (t + 1))).getD (tap ⟨e, heH⟩).val false at hle_tap
      rw [htap_t, htap_t1, hxor_t, hxor_t1] at hle_tap
      exact absurd hle_tap (by decide)
  have hdrop : ∀ t : ℕ, t ≤ m → notCode C.gates (inp t) + t ≤ notCode C.gates (inp 0) := by
    intro t
    induction t with
    | zero => intro _; omega
    | succ t ih =>
      intro ht
      have h1 := ih (by omega)
      have h2 := hdec_step t (by omega)
      omega
  have h0 := hdrop m le_rfl
  have hbound := notCode_lt C.gates (inp 0)
  have hnc := notCountL_eq_notCount C
  have hpow : 2 ^ notCountL C.gates ≤ 2 ^ r := Nat.pow_le_pow_right (by omega) (hnc ▸ hnot)
  have _ := hltG
  omega

/-! ### Part 2: Bitwise monotonicity helpers -/

lemma testBit_eq_of_div_eq {A B p : ℕ}
    (hdiv : A / 2 ^ (p + 1) = B / 2 ^ (p + 1))
    (hle : A ≤ B) :
    A.testBit p ≤ B.testBit p := by
  have hdiv_le : A / 2 ^ p ≤ B / 2 ^ p := Nat.div_le_div_right hle
  have hA2 : (A / 2 ^ p) / 2 = A / 2 ^ (p + 1) := by
    rw [Nat.div_div_eq_div_mul, pow_succ]
  have hB2 : (B / 2 ^ p) / 2 = B / 2 ^ (p + 1) := by
    rw [Nat.div_div_eq_div_mul, pow_succ]
  have hq : (A / 2 ^ p) / 2 = (B / 2 ^ p) / 2 := by rw [hA2, hB2, hdiv]
  have hbit : ∀ n : ℕ, n.testBit p = decide ((n / 2 ^ p) % 2 = 1) := by
    intro n
    rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two]
    have hlt : (n / 2 ^ p) % 2 < 2 := Nat.mod_lt _ (by omega)
    rcases (show (n / 2 ^ p) % 2 = 0 ∨ (n / 2 ^ p) % 2 = 1 by omega) with h | h <;> rw [h] <;> rfl
  rw [hbit A, hbit B]
  by_cases hA : (A / 2 ^ p) % 2 = 1
  · rw [decide_eq_true hA]
    have hB : (B / 2 ^ p) % 2 = 1 := by
      have h1 := Nat.div_add_mod (A / 2 ^ p) 2
      have h2 := Nat.div_add_mod (B / 2 ^ p) 2
      have hlt : (B / 2 ^ p) % 2 < 2 := Nat.mod_lt _ (by omega)
      omega
    rw [decide_eq_true hB]
  · rw [decide_eq_false hA]; exact Bool.false_le _

lemma testBit_mono_given_high {r k A B : ℕ} (hk : k < r)
    (hA : A < 2 ^ r) (hB : B < 2 ^ r) (hle : A ≤ B)
    (hhigh : ∀ j : Fin r, j.val < k → A.testBit (r - 1 - j.val) = B.testBit (r - 1 - j.val)) :
    A.testBit (r - 1 - k) ≤ B.testBit (r - 1 - k) := by
  apply testBit_eq_of_div_eq _ hle
  apply Nat.eq_of_testBit_eq
  intro m
  rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
  set q := m + (r - 1 - k + 1)
  by_cases hqr : q < r
  · let j : Fin r := ⟨r - 1 - q, by omega⟩
    have hjk : j.val < k := by dsimp only [j, q]; omega
    have hjeq : r - 1 - j.val = q := by dsimp only [j]; omega
    have h := hhigh j hjk
    rwa [hjeq] at h
  · have hpow : 2 ^ r ≤ 2 ^ q := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hA hpow),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hB hpow)]

lemma eq_of_all_high_bits_eq {r A B : ℕ} (hA : A < 2 ^ r) (hB : B < 2 ^ r)
    (hall : ∀ j : Fin r, A.testBit (r - 1 - j.val) = B.testBit (r - 1 - j.val)) :
    A = B := by
  apply Nat.eq_of_testBit_eq
  intro q
  by_cases hqr : q < r
  · let j : Fin r := ⟨r - 1 - q, by omega⟩
    have hjeq : r - 1 - j.val = q := by dsimp only [j]; omega
    have h := hall j
    rwa [hjeq] at h
  · have hpow : 2 ^ r ≤ 2 ^ q := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hA hpow),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hB hpow)]

/-! ### Part 3: Constructive circuit builder for monotone DNF and NOT stages -/

def WellFormed (n : ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
  (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + 2 + j)

def wireVal (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (evalWires gs (List.ofFn x ++ [false, true])).getD w false

def Extends (n : ℕ) (gs1 gs2 : List Gate) : Prop :=
  gs1.length ≤ gs2.length ∧
  ∀ (x : Fin n → Bool) (w : ℕ), w < n + 2 + gs1.length → wireVal n gs2 x w = wireVal n gs1 x w

lemma Extends.refl (n : ℕ) (gs : List Gate) : Extends n gs gs :=
  ⟨le_rfl, fun _ _ _ => rfl⟩

lemma Extends.trans {n : ℕ} {gs1 gs2 gs3 : List Gate}
    (h12 : Extends n gs1 gs2) (h23 : Extends n gs2 gs3) : Extends n gs1 gs3 :=
  ⟨le_trans h12.1 h23.1, fun x w hw =>
    (h23.2 x w (by have := h12.1; omega)).trans (h12.2 x w hw)⟩

lemma evalWires_length (gs : List Gate) (w : List Bool) :
    (evalWires gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [evalWires]
  | cons g gs ih =>
    simp only [evalWires, List.foldl_cons] at ih ⊢
    rw [ih, List.length_append, List.length_singleton, List.length_cons]
    omega

lemma evalWires_append (gs1 gs2 : List Gate) (w : List Bool) :
    evalWires (gs1 ++ gs2) w = evalWires gs2 (evalWires gs1 w) := by
  simp [evalWires, List.foldl_append]

lemma wireVal_input_lt {n : ℕ} (x : Fin n → Bool) (u : Fin n) :
    wireVal n [] x u.val = x u := by
  dsimp only [wireVal, evalWires, List.foldl_nil]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [u.isLt]),
      List.getElem?_ofFn, dif_pos u.isLt]
  rfl

lemma wireVal_const_false {n : ℕ} (x : Fin n → Bool) :
    wireVal n [] x n = false := by
  dsimp only [wireVal, evalWires, List.foldl_nil]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

lemma wireVal_const_true {n : ℕ} (x : Fin n → Bool) :
    wireVal n [] x (n + 1) = true := by
  dsimp only [wireVal, evalWires, List.foldl_nil]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

lemma wellFormed_push {n : ℕ} {gs : List Gate} (hwf : WellFormed n gs) (g : Gate)
    (hfit : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hrb : ∀ i ∈ g.inputs, i < n + 2 + gs.length) :
    WellFormed n (gs ++ [g]) := by
  constructor
  · intro g' hg'
    rcases List.mem_append.mp hg' with h1 | h2
    · exact hwf.1 g' h1
    · rw [List.mem_singleton.mp h2]; exact hfit
  · intro j hj i hi
    rw [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · have hget : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        rw [getD_append_singleton, if_pos hlt]
      rw [hget] at hi
      exact hwf.2 j hlt i hi
    · have heq : j = gs.length := by omega
      have hget : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = g := by
        rw [getD_append_singleton, if_neg hlt, if_pos heq]
      rw [hget] at hi
      rw [heq]
      exact hrb i hi

lemma extends_push {n : ℕ} (gs : List Gate) (g : Gate) :
    Extends n gs (gs ++ [g]) := by
  refine ⟨by simp, fun x w hw => ?_⟩
  dsimp only [wireVal]
  rw [evalWires_append]
  set ws := evalWires gs (List.ofFn x ++ [false, true])
  have hlen : ws.length = n + 2 + gs.length := by
    dsimp only [ws]; rw [evalWires_length, List.length_append, List.length_ofFn]; simp
  change (ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]).getD w false = ws.getD w false
  rw [getD_append_singleton, if_pos (by omega)]

lemma wireVal_push_new {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    wireVal n (gs ++ [g]) x (n + 2 + gs.length) =
    g.op.eval (g.inputs.map fun i => wireVal n gs x i) := by
  dsimp only [wireVal]
  rw [evalWires_append]
  set ws := evalWires gs (List.ofFn x ++ [false, true])
  have hlen : ws.length = n + 2 + gs.length := by
    dsimp only [ws]; rw [evalWires_length, List.length_append, List.length_ofFn]; simp
  change (ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]).getD (n + 2 + gs.length) false =
    g.op.eval (g.inputs.map fun i => ws.getD i false)
  rw [getD_append_singleton, if_neg (by omega), if_pos hlen.symm]

lemma extends_nil (n : ℕ) (gs : List Gate) : Extends n [] gs := by
  induction gs using List.reverseRecOn with
  | nil => exact Extends.refl n []
  | append_singleton l g ih => exact ih.trans (extends_push l g)

def addAndList (n : ℕ) (gs : List Gate) : List ℕ → List Gate × ℕ
  | [] => (gs, n + 1)
  | [w] => (gs, w)
  | w :: w' :: ws =>
    let res := addAndList n gs (w' :: ws)
    (res.1 ++ [⟨GateOp.and, [w, res.2]⟩], n + 2 + res.1.length)

lemma addAndList_spec (n : ℕ) : ∀ (ws : List ℕ) (gs : List Gate),
    WellFormed n gs → (∀ w ∈ ws, w < n + 2 + gs.length) →
    let res := addAndList n gs ws
    WellFormed n res.1 ∧
    notCountL res.1 = notCountL gs ∧
    Extends n gs res.1 ∧
    res.2 < n + 2 + res.1.length ∧
    (∀ x : Fin n → Bool, wireVal n res.1 x res.2 = ws.all (fun w => wireVal n gs x w))
  | [], gs, hwf, _ => by
    dsimp only [addAndList]
    refine ⟨hwf, rfl, Extends.refl n gs, by omega, fun x => ?_⟩
    rw [(extends_nil n gs).2 x (n + 1) (by simp), wireVal_const_true]
    rfl
  | [w], gs, hwf, hws => by
    dsimp only [addAndList]
    refine ⟨hwf, rfl, Extends.refl n gs, hws w (List.mem_cons_self ..), fun x => ?_⟩
    simp
  | w :: w' :: ws, gs, hwf, hws => by
    have hws' : ∀ u ∈ (w' :: ws), u < n + 2 + gs.length :=
      fun u hu => hws u (List.mem_cons_of_mem w hu)
    have ih := addAndList_spec n (w' :: ws) gs hwf hws'
    set res := addAndList n gs (w' :: ws)
    rcases ih with ⟨hwf1, hnc1, hext1, hw1lt, hval1⟩
    have hwlt : w < n + 2 + res.1.length := by
      have := hws w (List.mem_cons_self ..); have := hext1.1; omega
    let g : Gate := ⟨GateOp.and, [w, res.2]⟩
    have hfitg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
      ⟨by simp [g], by simp [g]⟩
    have hrbg : ∀ i ∈ g.inputs, i < n + 2 + res.1.length := by
      intro i hi
      simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact hwlt
      · exact hw1lt
    dsimp only [addAndList]
    change WellFormed n (res.1 ++ [g]) ∧ notCountL (res.1 ++ [g]) = notCountL gs ∧
      Extends n gs (res.1 ++ [g]) ∧ n + 2 + res.1.length < n + 2 + (res.1 ++ [g]).length ∧
      ∀ x : Fin n → Bool, wireVal n (res.1 ++ [g]) x (n + 2 + res.1.length) =
        (w :: w' :: ws).all (fun u => wireVal n gs x u)
    refine ⟨wellFormed_push hwf1 g hfitg hrbg, ?_, hext1.trans (extends_push res.1 g),
      by simp, fun x => ?_⟩
    · rw [notCountL_append, hnc1]; simp [notCountL, g, isNotOp]
    · rw [wireVal_push_new]
      simp only [g, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
        Bool.and_true]
      rw [hext1.2 x w (hws w (List.mem_cons_self ..)), hval1 x]
      rfl

def addOrList (n : ℕ) (gs : List Gate) : List ℕ → List Gate × ℕ
  | [] => (gs, n)
  | [w] => (gs, w)
  | w :: w' :: ws =>
    let res := addOrList n gs (w' :: ws)
    (res.1 ++ [⟨GateOp.or, [w, res.2]⟩], n + 2 + res.1.length)

lemma addOrList_spec (n : ℕ) : ∀ (ws : List ℕ) (gs : List Gate),
    WellFormed n gs → (∀ w ∈ ws, w < n + 2 + gs.length) →
    let res := addOrList n gs ws
    WellFormed n res.1 ∧
    notCountL res.1 = notCountL gs ∧
    Extends n gs res.1 ∧
    res.2 < n + 2 + res.1.length ∧
    (∀ x : Fin n → Bool, wireVal n res.1 x res.2 = ws.any (fun w => wireVal n gs x w))
  | [], gs, hwf, _ => by
    dsimp only [addOrList]
    refine ⟨hwf, rfl, Extends.refl n gs, by omega, fun x => ?_⟩
    rw [(extends_nil n gs).2 x n (by simp), wireVal_const_false]
    rfl
  | [w], gs, hwf, hws => by
    dsimp only [addOrList]
    refine ⟨hwf, rfl, Extends.refl n gs, hws w (List.mem_cons_self ..), fun x => ?_⟩
    simp
  | w :: w' :: ws, gs, hwf, hws => by
    have hws' : ∀ u ∈ (w' :: ws), u < n + 2 + gs.length :=
      fun u hu => hws u (List.mem_cons_of_mem w hu)
    have ih := addOrList_spec n (w' :: ws) gs hwf hws'
    set res := addOrList n gs (w' :: ws)
    rcases ih with ⟨hwf1, hnc1, hext1, hw1lt, hval1⟩
    have hwlt : w < n + 2 + res.1.length := by
      have := hws w (List.mem_cons_self ..); have := hext1.1; omega
    let g : Gate := ⟨GateOp.or, [w, res.2]⟩
    have hfitg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
      ⟨by simp [g], by simp [g]⟩
    have hrbg : ∀ i ∈ g.inputs, i < n + 2 + res.1.length := by
      intro i hi
      simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact hwlt
      · exact hw1lt
    dsimp only [addOrList]
    change WellFormed n (res.1 ++ [g]) ∧ notCountL (res.1 ++ [g]) = notCountL gs ∧
      Extends n gs (res.1 ++ [g]) ∧ n + 2 + res.1.length < n + 2 + (res.1 ++ [g]).length ∧
      ∀ x : Fin n → Bool, wireVal n (res.1 ++ [g]) x (n + 2 + res.1.length) =
        (w :: w' :: ws).any (fun u => wireVal n gs x u)
    refine ⟨wellFormed_push hwf1 g hfitg hrbg, ?_, hext1.trans (extends_push res.1 g),
      by simp, fun x => ?_⟩
    · rw [notCountL_append, hnc1]; simp [notCountL, g, isNotOp]
    · rw [wireVal_push_new]
      simp only [g, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
        Bool.or_false]
      rw [hext1.2 x w (hws w (List.mem_cons_self ..)), hval1 x]
      rfl

def addTerms (n : ℕ) (gs : List Gate) (W : List ℕ) : List (Fin n → Bool) → List Gate × List ℕ
  | [] => (gs, [])
  | x₀ :: xs =>
    let posW := W.filter (fun w => wireVal n gs x₀ w)
    let res1 := addAndList n gs posW
    let res2 := addTerms n res1.1 W xs
    (res2.1, res1.2 :: res2.2)

lemma addTerms_spec (n : ℕ) (W : List ℕ) : ∀ (D : List (Fin n → Bool)) (gs : List Gate),
    WellFormed n gs → (∀ w ∈ W, w < n + 2 + gs.length) →
    let res := addTerms n gs W D
    WellFormed n res.1 ∧
    notCountL res.1 = notCountL gs ∧
    Extends n gs res.1 ∧
    (∀ u ∈ res.2, u < n + 2 + res.1.length) ∧
    (∀ y : Fin n → Bool,
      res.2.any (fun u => wireVal n res.1 y u) = true ↔
      ∃ x₀ ∈ D, ∀ w ∈ W, wireVal n gs x₀ w ≤ wireVal n gs y w)
  | [], gs, hwf, _ => by
    dsimp only [addTerms]
    refine ⟨hwf, rfl, Extends.refl n gs, fun _ h => absurd h List.not_mem_nil, fun _ => by simp⟩
  | x₀ :: xs, gs, hwf, hW => by
    set posW := W.filter (fun w => wireVal n gs x₀ w)
    have hposW : ∀ w ∈ posW, w < n + 2 + gs.length :=
      fun w hw => hW w (List.mem_of_mem_filter hw)
    have h1 := addAndList_spec n posW gs hwf hposW
    set res1 := addAndList n gs posW
    rcases h1 with ⟨hwf1, hnc1, hext1, hw1lt, hval1⟩
    have hW1 : ∀ w ∈ W, w < n + 2 + res1.1.length :=
      fun w hw => lt_of_lt_of_le (hW w hw) (by have := hext1.1; omega)
    have h2 := addTerms_spec n W xs res1.1 hwf1 hW1
    set res2 := addTerms n res1.1 W xs
    rcases h2 with ⟨hwf2, hnc2, hext2, hws2lt, hval2⟩
    dsimp only [addTerms]
    change WellFormed n res2.1 ∧ notCountL res2.1 = notCountL gs ∧ Extends n gs res2.1 ∧
      (∀ u ∈ res1.2 :: res2.2, u < n + 2 + res2.1.length) ∧
      ∀ y : Fin n → Bool,
        (res1.2 :: res2.2).any (fun u => wireVal n res2.1 y u) = true ↔
        ∃ x₁ ∈ x₀ :: xs, ∀ w ∈ W, wireVal n gs x₁ w ≤ wireVal n gs y w
    refine ⟨hwf2, hnc2.trans hnc1, hext1.trans hext2, ?_, fun y => ?_⟩
    · intro u hu
      rcases List.mem_cons.mp hu with rfl | hu'
      · have := hext2.1; omega
      · exact hws2lt u hu'
    · rw [List.any_cons, Bool.or_eq_true, hext2.2 y res1.2 hw1lt, hval1 y, hval2 y]
      have hterm : posW.all (fun w => wireVal n gs y w) = true ↔
          ∀ w ∈ W, wireVal n gs x₀ w ≤ wireVal n gs y w := by
        simp only [posW, List.all_eq_true, List.mem_filter]
        constructor
        · intro hall w hw
          cases hx : wireVal n gs x₀ w
          · exact Bool.false_le _
          · rw [hall w ⟨hw, hx⟩]
        · intro hle w ⟨hw, hx⟩
          exact bool_true_le_eq (hx ▸ hle w hw)
      have htail : (∃ x₁ ∈ xs, ∀ w ∈ W, wireVal n res1.1 x₁ w ≤ wireVal n res1.1 y w) ↔
          (∃ x₁ ∈ xs, ∀ w ∈ W, wireVal n gs x₁ w ≤ wireVal n gs y w) := by
        refine exists_congr fun x₁ => and_congr_right fun _ => forall_congr' fun w =>
          imp_congr_right fun hw => ?_
        rw [hext1.2 x₁ w (hW w hw), hext1.2 y w (hW w hw)]
      rw [hterm, htail]
      simp

lemma addMonotoneDNF_exists {n : ℕ} (gs : List Gate) (W : List ℕ)
    (hwf : WellFormed n gs) (hW : ∀ w ∈ W, w < n + 2 + gs.length)
    (cover : (Fin n → Bool) → Prop) (f : (Fin n → Bool) → Bool)
    (hmono : ∀ x y : Fin n → Bool, cover x → cover y →
      (∀ w ∈ W, wireVal n gs x w ≤ wireVal n gs y w) → f x ≤ f y) :
    ∃ (gs' : List Gate) (wf : ℕ),
      WellFormed n gs' ∧
      notCountL gs' = notCountL gs ∧
      Extends n gs gs' ∧
      wf < n + 2 + gs'.length ∧
      ∀ x : Fin n → Bool, cover x → wireVal n gs' x wf = f x := by
  let D : List (Fin n → Bool) :=
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun x => cover x ∧ f x = true)).toList
  have h1 := addTerms_spec n W D gs hwf hW
  set res1 := addTerms n gs W D
  rcases h1 with ⟨hwf1, hnc1, hext1, hws1lt, hval1⟩
  have h2 := addOrList_spec n res1.2 res1.1 hwf1 hws1lt
  set res2 := addOrList n res1.1 res1.2
  rcases h2 with ⟨hwf2, hnc2, hext2, hw2lt, hval2⟩
  refine ⟨res2.1, res2.2, hwf2, hnc2.trans hnc1, hext1.trans hext2, hw2lt, fun y hcy => ?_⟩
  apply Bool.eq_iff_iff.mpr
  rw [hval2 y, hval1 y]
  constructor
  · rintro ⟨x₀, hx₀D, hle⟩
    have hx₀ : cover x₀ ∧ f x₀ = true := by
      have hm : x₀ ∈ (Finset.univ.filter (fun x => cover x ∧ f x = true)) :=
        Finset.mem_toList.mp hx₀D
      exact (Finset.mem_filter.mp hm).2
    exact bool_true_le_eq (hx₀.2 ▸ hmono x₀ y hx₀.1 hcy hle)
  · intro hfy
    refine ⟨y, ?_, fun _ _ => le_rfl⟩
    exact Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hcy, hfy⟩)

def addEdgeOrs (n : ℕ) (gs : List Gate) : List (Fin n × Fin n) → List Gate × List ℕ
  | [] => (gs, [])
  | e :: es =>
    let g : Gate := ⟨GateOp.or, [e.1.val, e.2.val]⟩
    let w := n + 2 + gs.length
    let res := addEdgeOrs n (gs ++ [g]) es
    (res.1, w :: res.2)

lemma addEdgeOrs_spec (n : ℕ) : ∀ (es : List (Fin n × Fin n)) (gs : List Gate),
    WellFormed n gs →
    let res := addEdgeOrs n gs es
    WellFormed n res.1 ∧
    notCountL res.1 = notCountL gs ∧
    Extends n gs res.1 ∧
    (∀ w ∈ res.2, w < n + 2 + res.1.length) ∧
    (∀ x : Fin n → Bool,
      res.2.all (fun w => wireVal n res.1 x w) = true ↔
      ∀ e ∈ es, x e.1 = true ∨ x e.2 = true)
  | [], gs, hwf => by
    dsimp only [addEdgeOrs]
    refine ⟨hwf, rfl, Extends.refl n gs, fun _ h => absurd h List.not_mem_nil, fun _ => by simp⟩
  | e :: es, gs, hwf => by
    let g : Gate := ⟨GateOp.or, [e.1.val, e.2.val]⟩
    have hfitg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
      ⟨by simp [g], by simp [g]⟩
    have hrbg : ∀ i ∈ g.inputs, i < n + 2 + gs.length := by
      intro i hi
      simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · have := e.1.isLt; omega
      · have := e.2.isLt; omega
    have hwf1 := wellFormed_push hwf g hfitg hrbg
    have hext1 : Extends n gs (gs ++ [g]) := extends_push gs g
    have h2 := addEdgeOrs_spec n es (gs ++ [g]) hwf1
    set res := addEdgeOrs n (gs ++ [g]) es
    rcases h2 with ⟨hwf2, hnc2, hext2, hws2lt, hval2⟩
    dsimp only [addEdgeOrs]
    change WellFormed n res.1 ∧ notCountL res.1 = notCountL gs ∧ Extends n gs res.1 ∧
      (∀ w ∈ (n + 2 + gs.length) :: res.2, w < n + 2 + res.1.length) ∧
      ∀ x : Fin n → Bool,
        ((n + 2 + gs.length) :: res.2).all (fun w => wireVal n res.1 x w) = true ↔
        ∀ e' ∈ e :: es, x e'.1 = true ∨ x e'.2 = true
    refine ⟨hwf2, ?_, hext1.trans hext2, ?_, fun x => ?_⟩
    · rw [hnc2, notCountL_append]; simp [notCountL, g, isNotOp]
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw'
      · have := hext2.1; simp at this; omega
      · exact hws2lt w hw'
    · rw [List.all_cons, Bool.and_eq_true, hval2 x]
      have hhead : wireVal n res.1 x (n + 2 + gs.length) = (x e.1 || x e.2) := by
        rw [hext2.2 x (n + 2 + gs.length) (by simp), wireVal_push_new]
        simp only [g, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
          Bool.or_false]
        have he1 : wireVal n gs x e.1.val = x e.1 := by
          rw [(extends_nil n gs).2 x e.1.val (by have := e.1.isLt; simp; omega), wireVal_input_lt]
        have he2 : wireVal n gs x e.2.val = x e.2 := by
          rw [(extends_nil n gs).2 x e.2.val (by have := e.2.isLt; simp; omega), wireVal_input_lt]
        rw [he1, he2]
      rw [hhead, Bool.or_eq_true]
      simp

lemma upper_construction {n r : ℕ} (G H : Finset (Fin n × Fin n))
    (hbound : ∀ S : Finset (Fin n),
      (S ⊆ H.image Prod.fst ∪ H.image Prod.snd ∧ ∀ e ∈ G, ¬(e.1 ∈ S ∧ e.2 ∈ S)) →
      S.card < 2 ^ r) :
    ∃ (C : Circuit) (tap : ↥H → Fin (n + 2 + C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C ∧
      C.output < n + 2 + C.size ∧ PEqualNP.NotBracket.notCount C ≤ r ∧
      ∀ x : Fin n → Bool,
        let inputs := List.ofFn x ++ [false, true]
        (C.eval inputs = true ↔ ∀ e ∈ G, x e.1 = true ∨ x e.2 = true) ∧
        ((∀ e ∈ G, x e.1 = true ∨ x e.2 = true) →
          ∀ e, (C.wires inputs).getD (tap e).val false = xor (x e.val.1) (x e.val.2)) := by
  let active : Finset (Fin n) := H.image Prod.fst ∪ H.image Prod.snd
  let cover : (Fin n → Bool) → Prop := fun x => ∀ e ∈ G, x e.1 = true ∨ x e.2 = true
  let Z : (Fin n → Bool) → Finset (Fin n) := fun x => active.filter (fun u => x u = false)
  let rank : (Fin n → Bool) → ℕ := fun x => (2 ^ r - 1) - (Z x).card
  have hZ_lt : ∀ x, cover x → (Z x).card < 2 ^ r := by
    intro x hx
    apply hbound (Z x)
    refine ⟨Finset.filter_subset _ active, fun e he ⟨h1, h2⟩ => ?_⟩
    have hf1 : x e.1 = false := (Finset.mem_filter.mp h1).2
    have hf2 : x e.2 = false := (Finset.mem_filter.mp h2).2
    rcases hx e he with ht1 | ht2
    · rw [hf1] at ht1; exact Bool.false_ne_true ht1
    · rw [hf2] at ht2; exact Bool.false_ne_true ht2
  have hrank_lt : ∀ x, rank x < 2 ^ r := by
    intro x
    have hpow : 1 ≤ 2 ^ r := Nat.one_le_pow r 2 (by omega)
    dsimp only [rank]; omega
  have hrank_mono : ∀ x y, cover x → cover y → (∀ u : Fin n, x u ≤ y u) → rank x ≤ rank y := by
    intro x y _ _ hxy
    have hsub : Z y ⊆ Z x := by
      intro u hu
      refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).1, ?_⟩
      exact bool_le_false_eq ((Finset.mem_filter.mp hu).2 ▸ hxy u)
    have hcard : (Z y).card ≤ (Z x).card := Finset.card_le_card hsub
    dsimp only [rank]; omega
  have hZ_eq_of_rank_eq : ∀ x y, cover x → cover y → (∀ u : Fin n, x u ≤ y u) →
      rank x = rank y → ∀ u ∈ active, x u = y u := by
    intro x y hcx hcy hxy hreq u hu
    have hsub : Z y ⊆ Z x := by
      intro v hv
      refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).1, ?_⟩
      exact bool_le_false_eq ((Finset.mem_filter.mp hv).2 ▸ hxy v)
    have hltX := hZ_lt x hcx
    have hltY := hZ_lt y hcy
    have hcard_eq : (Z y).card = (Z x).card := by dsimp only [rank] at hreq; omega
    have hZeq : Z y = Z x := Finset.eq_of_subset_of_card_le hsub (by omega)
    have hmem : u ∈ Z y ↔ u ∈ Z x := by rw [hZeq]
    simp only [Z, Finset.mem_filter, hu, true_and] at hmem
    cases hxu : x u <;> cases hyu : y u
    · rfl
    · exact absurd (hmem.mpr hxu) (by simp [hyu])
    · exact absurd (hmem.mp hyu) (by simp [hxu])
    · rfl
  -- Step 1: build cover circuit
  have hwf0 : WellFormed n [] := ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => by simp at h⟩
  have hedge := addEdgeOrs_spec n G.toList [] hwf0
  set resE := addEdgeOrs n [] G.toList
  rcases hedge with ⟨hwfE, hncE, _, hwsElt, hvalE⟩
  have hcov := addAndList_spec n resE.2 resE.1 hwfE hwsElt
  set resC := addAndList n resE.1 resE.2
  rcases hcov with ⟨hwfC, hncC, _, wCov_lt, hvalC⟩
  let gs0 := resC.1
  let wCov := resC.2
  have hnc0 : notCountL gs0 = 0 := by dsimp only [gs0]; rw [hncC, hncE]; rfl
  have hcov_spec : ∀ x : Fin n → Bool, wireVal n gs0 x wCov = true ↔ cover x := by
    intro x
    dsimp only [gs0, wCov]
    rw [hvalC x, hvalE x]
    simp only [cover, Finset.mem_toList]
  -- Step 2: inductively build r NOT stages for bits of rank
  have hstages : ∀ k : ℕ, k ≤ r →
      ∃ (gs : List Gate) (W : List ℕ),
        WellFormed n gs ∧
        notCountL gs = k ∧
        Extends n gs0 gs ∧
        (∀ w ∈ W, w < n + 2 + gs.length) ∧
        (∀ u : Fin n, u.val ∈ W) ∧
        (∀ j : Fin r, j.val < k →
          (∃ wb ∈ W, ∀ x, cover x → wireVal n gs x wb = (rank x).testBit (r - 1 - j.val)) ∧
          (∃ wn ∈ W, ∀ x, cover x → wireVal n gs x wn = !((rank x).testBit (r - 1 - j.val)))) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨gs0, (List.finRange n).map Fin.val, hwfC, hnc0, Extends.refl n gs0, ?_, ?_, ?_⟩
      · intro w hw
        rcases List.mem_map.mp hw with ⟨u, _, rfl⟩
        have := u.isLt; omega
      · intro u
        exact List.mem_map.mpr ⟨u, List.mem_finRange u, rfl⟩
      · intro j hj; omega
    | succ k ih =>
      intro hkr
      rcases ih (by omega) with ⟨gs, W, hwf, hnc, hext, hWlt, hWin, hbits⟩
      let f_k : (Fin n → Bool) → Bool := fun x => (rank x).testBit (r - 1 - k)
      have hmono_k : ∀ x y : Fin n → Bool, cover x → cover y →
          (∀ w ∈ W, wireVal n gs x w ≤ wireVal n gs y w) → f_k x ≤ f_k y := by
        intro x y hcx hcy hWle
        have hxy : ∀ u : Fin n, x u ≤ y u := by
          intro u
          have h := hWle u.val (hWin u)
          rwa [(extends_nil n gs).2 x u.val (by have := u.isLt; simp; omega), wireVal_input_lt,
               (extends_nil n gs).2 y u.val (by have := u.isLt; simp; omega), wireVal_input_lt] at h
        have hrle : rank x ≤ rank y := hrank_mono x y hcx hcy hxy
        have hhigh : ∀ j : Fin r, j.val < k →
            (rank x).testBit (r - 1 - j.val) = (rank y).testBit (r - 1 - j.val) := by
          intro j hjk
          rcases hbits j hjk with ⟨⟨wb, hwbW, hwb⟩, ⟨wn, hwnW, hwn⟩⟩
          have h1 := hWle wb hwbW
          have h2 := hWle wn hwnW
          rw [hwb x hcx, hwb y hcy] at h1
          rw [hwn x hcx, hwn y hcy] at h2
          exact bool_eq_of_le_not h1 h2
        exact testBit_mono_given_high (by omega) (hrank_lt x) (hrank_lt y) hrle hhigh
      rcases addMonotoneDNF_exists gs W hwf hWlt cover f_k hmono_k with
        ⟨gs1, wb, hwf1, hnc1, hext1, hwb_lt, hwb_val⟩
      let gnot : Gate := ⟨GateOp.not, [wb]⟩
      let gs2 := gs1 ++ [gnot]
      let wn := n + 2 + gs1.length
      have hfitnot : gnot.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
          gnot.inputs.length ≤ 2 := ⟨by simp [gnot], by simp [gnot]⟩
      have hrbnot : ∀ i ∈ gnot.inputs, i < n + 2 + gs1.length := by
        intro i hi
        simp only [gnot, List.mem_cons, List.not_mem_nil, or_false] at hi
        subst hi; exact hwb_lt
      have hwf2 := wellFormed_push hwf1 gnot hfitnot hrbnot
      have hext12 : Extends n gs1 gs2 := extends_push gs1 gnot
      have hext_all : Extends n gs gs2 := hext1.trans hext12
      refine ⟨gs2, wb :: wn :: W, hwf2, ?_, hext.trans hext_all, ?_, ?_, ?_⟩
      · dsimp only [gs2]; rw [notCountL_append, hnc1, hnc]; simp [notCountL, gnot, isNotOp]
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw1
        · have := hext12.1; omega
        · rcases List.mem_cons.mp hw1 with rfl | hw2
          · dsimp only [gs2, wn]; simp
          · have := hWlt w hw2; have := hext_all.1; omega
      · intro u; exact List.mem_cons_of_mem wb (List.mem_cons_of_mem wn (hWin u))
      · intro j hj
        by_cases hjk : j.val < k
        · rcases hbits j hjk with ⟨⟨wb', hwb'W, hwb'⟩, ⟨wn', hwn'W, hwn'⟩⟩
          refine ⟨⟨wb', List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hwb'W), fun x hx => ?_⟩,
                  ⟨wn', List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hwn'W), fun x hx => ?_⟩⟩
          · rw [hext_all.2 x wb' (hWlt wb' hwb'W), hwb' x hx]
          · rw [hext_all.2 x wn' (hWlt wn' hwn'W), hwn' x hx]
        · have hjeq : j.val = k := by omega
          refine ⟨⟨wb, List.mem_cons_self .., fun x hx => ?_⟩,
                  ⟨wn, List.mem_cons_of_mem wb (List.mem_cons_self ..), fun x hx => ?_⟩⟩
          · rw [hext12.2 x wb hwb_lt, hwb_val x hx, hjeq]
          · dsimp only [gs2, wn]
            rw [wireVal_push_new]
            simp only [gnot, GateOp.eval, List.map_cons, List.map_nil, List.headD_cons]
            rw [hwb_val x hx, hjeq]
  rcases hstages r le_rfl with ⟨gsr, Wr, hwfr, hncr, hextr, hWrlt, hWrin, hbitsr⟩
  -- Step 3: build monotone DNF taps for each edge e in H
  have hparity_mono : ∀ e : ↥H, ∀ x y : Fin n → Bool, cover x → cover y →
      (∀ w ∈ Wr, wireVal n gsr x w ≤ wireVal n gsr y w) →
      xor (x e.val.1) (x e.val.2) ≤ xor (y e.val.1) (y e.val.2) := by
    intro e x y hcx hcy hWle
    have hxy : ∀ u : Fin n, x u ≤ y u := by
      intro u
      have h := hWle u.val (hWrin u)
      rwa [(extends_nil n gsr).2 x u.val (by have := u.isLt; simp; omega), wireVal_input_lt,
           (extends_nil n gsr).2 y u.val (by have := u.isLt; simp; omega), wireVal_input_lt] at h
    have hall : ∀ j : Fin r, (rank x).testBit (r - 1 - j.val) = (rank y).testBit (r - 1 - j.val) := by
      intro j
      rcases hbitsr j j.isLt with ⟨⟨wb, hwbW, hwb⟩, ⟨wn, hwnW, hwn⟩⟩
      have h1 := hWle wb hwbW
      have h2 := hWle wn hwnW
      rw [hwb x hcx, hwb y hcy] at h1
      rw [hwn x hcx, hwn y hcy] at h2
      exact bool_eq_of_le_not h1 h2
    have hreq : rank x = rank y := eq_of_all_high_bits_eq (hrank_lt x) (hrank_lt y) hall
    have heq_act := hZ_eq_of_rank_eq x y hcx hcy hxy hreq
    have h1act : e.val.1 ∈ active :=
      Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e.val, e.property, rfl⟩)
    have h2act : e.val.2 ∈ active :=
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e.val, e.property, rfl⟩)
    rw [heq_act e.val.1 h1act, heq_act e.val.2 h2act]
  have htaps : ∀ L : List ↥H,
      ∃ (gs : List Gate) (f : ↥H → ℕ),
        WellFormed n gs ∧
        notCountL gs = r ∧
        Extends n gsr gs ∧
        ∀ e ∈ L, f e < n + 2 + gs.length ∧
          ∀ x, cover x → wireVal n gs x (f e) = xor (x e.val.1) (x e.val.2) := by
    intro L
    induction L with
    | nil =>
      exact ⟨gsr, fun _ => 0, hwfr, hncr, Extends.refl n gsr, fun _ h => absurd h List.not_mem_nil⟩
    | cons e es ih =>
      rcases ih with ⟨gs1, f1, hwf1, hnc1, hext1, hf1⟩
      have hW1lt : ∀ w ∈ Wr, w < n + 2 + gs1.length :=
        fun w hw => lt_of_lt_of_le (hWrlt w hw) (by have := hext1.1; omega)
      have hmono_e : ∀ x y : Fin n → Bool, cover x → cover y →
          (∀ w ∈ Wr, wireVal n gs1 x w ≤ wireVal n gs1 y w) →
          xor (x e.val.1) (x e.val.2) ≤ xor (y e.val.1) (y e.val.2) := by
        intro x y hcx hcy hle
        apply hparity_mono e x y hcx hcy
        intro w hw
        have h := hle w hw
        rwa [hext1.2 x w (hWrlt w hw), hext1.2 y w (hWrlt w hw)] at h
      rcases addMonotoneDNF_exists gs1 Wr hwf1 hW1lt cover (fun x => xor (x e.val.1) (x e.val.2))
        hmono_e with ⟨gs2, we, hwf2, hnc2, hext2, hwe_lt, hwe_val⟩
      refine ⟨gs2, fun e' => if e' = e then we else f1 e', hwf2, hnc2.trans hnc1,
        hext1.trans hext2, fun e' he' => ?_⟩
      by_cases heq : e' = e
      · subst heq
        simp only [↓reduceIte]
        exact ⟨hwe_lt, hwe_val⟩
      · simp only [heq, ↓reduceIte]
        have he'es : e' ∈ es := (List.mem_cons.mp he').resolve_left heq
        rcases hf1 e' he'es with ⟨hflt, hfval⟩
        refine ⟨lt_of_lt_of_le hflt (by have := hext2.1; omega), fun x hx => ?_⟩
        rw [hext2.2 x (f1 e') hflt, hfval x hx]
  rcases htaps (Finset.univ : Finset ↥H).toList with ⟨gsF, fF, hwfF, hncF, hextF, hfF⟩
  let C : Circuit := ⟨gsF, wCov⟩
  have hext0F : Extends n gs0 gsF := hextr.trans hextF
  have hwCovF : wCov < n + 2 + C.size := by
    change resC.2 < n + 2 + gsF.length
    have h1 : resC.1.length ≤ gsF.length := hext0F.1
    omega
  let tap : ↥H → Fin (n + 2 + C.size) := fun e =>
    ⟨fF e, (hfF e (Finset.mem_toList.mpr (Finset.mem_univ e))).1⟩
  have hnc_le : PEqualNP.NotBracket.notCount C ≤ r := by
    rw [← notCountL_eq_notCount C]
    change notCountL gsF ≤ r
    omega
  refine ⟨C, tap, hwfF.1, hwfF.2, hwCovF, hnc_le, fun x => ?_⟩
  constructor
  · change wireVal n gsF x wCov = true ↔ cover x
    rw [hext0F.2 x wCov wCov_lt, hcov_spec x]
  · intro hcx e
    change wireVal n gsF x (fF e) = xor (x e.val.1) (x e.val.2)
    exact (hfF e (Finset.mem_toList.mpr (Finset.mem_univ e))).2 x hcx

theorem main :
    ∀ n : Nat, ∀ G H : Finset (Fin n × Fin n),
      (∀ e ∈ G, e.1 < e.2) → H ⊆ G →
      let active := H.image Prod.fst ∪ H.image Prod.snd
      let independent := fun S : Finset (Fin n) =>
        S ⊆ active ∧ ∀ e ∈ G, ¬(e.1 ∈ S ∧ e.2 ∈ S)
      let cover := fun x : Fin n → Bool => ∀ e ∈ G, x e.1=true ∨ x e.2=true
      ∀ r : Nat,
        (∃ (C : PEqualNP.CircuitLowerBounds.Circuit)
            (tap : ↥H → Fin (n+2+C.size)),
          PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
          C.output < n+2+C.size ∧ PEqualNP.NotBracket.notCount C ≤ r ∧
          ∀ x : Fin n → Bool,
            let inputs := List.ofFn x ++ [false,true]
            (C.eval inputs = true ↔ cover x) ∧
            (cover x → ∀ e, (C.wires inputs).getD (tap e).val false = xor (x e.val.1) (x e.val.2))) ↔
        ∀ S : Finset (Fin n), independent S → S.card < 2^r := by
  intro n G H hltG hHG
  dsimp only
  intro r
  constructor
  · rintro ⟨C, tap, hfit, _, _, hnot, hspec⟩ S ⟨hsub, hind⟩
    exact chain_card_lt_two_pow G H hltG hHG C tap hfit hnot hspec S hsub hind
  · intro hbound
    exact upper_construction G H hbound

end PEqualNP.Outside.L_lib_1181_aux

theorem PEqualNP.Outside.L_lib_1181 :
∀ n : Nat, ∀ G H : Finset (Fin n × Fin n),
  (∀ e ∈ G, e.1 < e.2) → H ⊆ G →
  let active := H.image Prod.fst ∪ H.image Prod.snd
  let independent := fun S : Finset (Fin n) =>
    S ⊆ active ∧ ∀ e ∈ G, ¬(e.1 ∈ S ∧ e.2 ∈ S)
  let cover := fun x : Fin n → Bool => ∀ e ∈ G, x e.1=true ∨ x e.2=true
  ∀ r : Nat,
    (∃ (C : PEqualNP.CircuitLowerBounds.Circuit)
        (tap : ↥H → Fin (n+2+C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
      C.output < n+2+C.size ∧ PEqualNP.NotBracket.notCount C ≤ r ∧
      ∀ x : Fin n → Bool,
        let inputs := List.ofFn x ++ [false,true]
        (C.eval inputs = true ↔ cover x) ∧
        (cover x → ∀ e, (C.wires inputs).getD (tap e).val false = xor (x e.val.1) (x e.val.2))) ↔
    ∀ S : Finset (Fin n), independent S → S.card < 2^r :=
  PEqualNP.Outside.L_lib_1181_aux.main
