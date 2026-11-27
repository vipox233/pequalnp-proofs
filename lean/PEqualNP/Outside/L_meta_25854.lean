import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25854_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

lemma lt_two_pow_iff_testBit (m : ℕ) :
    ∀ x : ℕ, x < 2 ^ m ↔ ∀ i : ℕ, m ≤ i → x.testBit i = false := by
  induction m with
  | zero =>
    intro x
    constructor
    · intro hx i _
      have hx0 : x = 0 := by omega
      subst hx0
      simp
    · intro h
      have hx0 : x = 0 := by
        apply Nat.eq_of_testBit_eq
        intro i
        simpa using h i (Nat.zero_le i)
      omega
  | succ m ih =>
    intro x
    constructor
    · intro hx i hi
      cases i with
      | zero => omega
      | succ j =>
        rw [Nat.testBit_succ]
        have hdiv : x / 2 < 2 ^ m := by
          rw [pow_succ] at hx
          omega
        exact (ih (x / 2)).mp hdiv j (by omega)
    · intro h
      have hdiv : x / 2 < 2 ^ m := by
        apply (ih (x / 2)).mpr
        intro j hj
        have := h (j + 1) (by omega)
        rwa [Nat.testBit_succ] at this
      rw [pow_succ]
      omega

lemma testBit_natXor (x y i : ℕ) : (Nat.xor x y).testBit i = xor (x.testBit i) (y.testBit i) :=
  Nat.testBit_xor x y i

lemma natXor_comm (x y : ℕ) : Nat.xor x y = Nat.xor y x := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [testBit_natXor]
  cases x.testBit i <;> cases y.testBit i <;> rfl

lemma natXor_cancel_left (x y : ℕ) : Nat.xor x (Nat.xor x y) = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [testBit_natXor]
  cases x.testBit i <;> cases y.testBit i <;> rfl

lemma natXor_eq_zero {x y : ℕ} : Nat.xor x y = 0 ↔ x = y := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    have hi := congrArg (fun n => n.testBit i) h
    simp only [testBit_natXor, Nat.zero_testBit] at hi
    cases hx : x.testBit i <;> cases hy : y.testBit i <;> simp_all
  · intro h
    subst h
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [testBit_natXor, Nat.zero_testBit]
    cases x.testBit i <;> rfl

lemma xor_lt_two_pow_aux {x y m : ℕ} (hx : x < 2 ^ m) (hy : y < 2 ^ m) :
    Nat.xor x y < 2 ^ m := by
  rw [lt_two_pow_iff_testBit] at hx hy ⊢
  intro i hi
  rw [testBit_natXor, hx i hi, hy i hi]
  rfl

lemma mod_two_pow_succ (m : ℕ) :
    ∀ v : ℕ, v % 2 ^ (m + 1) = v % 2 ^ m + if v.testBit m then 2 ^ m else 0 := by
  induction m with
  | zero =>
    intro v
    simp only [pow_zero, Nat.mod_one, zero_add, pow_one, Nat.testBit_zero, decide_eq_true_eq]
    split_ifs <;> omega
  | succ m ih =>
    intro v
    have h1 : v % 2 ^ (m + 2) = v % 2 + 2 * ((v / 2) % 2 ^ (m + 1)) := by
      have hpow : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by ring
      rw [hpow]
      have hdm := Nat.div_add_mod (v % (2 * 2 ^ (m + 1))) 2
      rw [Nat.mod_mul_right_div_self,
          Nat.mod_mod_of_dvd v (Nat.dvd_mul_right 2 (2 ^ (m + 1)))] at hdm
      omega
    have h2 : v % 2 ^ (m + 1) = v % 2 + 2 * ((v / 2) % 2 ^ m) := by
      have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
      rw [hpow]
      have hdm := Nat.div_add_mod (v % (2 * 2 ^ m)) 2
      rw [Nat.mod_mul_right_div_self,
          Nat.mod_mod_of_dvd v (Nat.dvd_mul_right 2 (2 ^ m))] at hdm
      omega
    rw [h1, h2, ih (v / 2), Nat.testBit_succ]
    have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    split_ifs <;> omega

lemma testBit_mod_two_pow_lt (m : ℕ) :
    ∀ (v i : ℕ), i < m → (v % 2 ^ m).testBit i = v.testBit i := by
  induction m with
  | zero => intro v i hi; omega
  | succ m ih =>
    intro v i hi
    cases i with
    | zero =>
      simp only [Nat.testBit_zero]
      have hdvd : 2 ∣ 2 ^ (m + 1) := by
        rw [pow_succ']
        exact Nat.dvd_mul_right 2 (2 ^ m)
      rw [Nat.mod_mod_of_dvd v hdvd]
    | succ j =>
      rw [Nat.testBit_succ, Nat.testBit_succ]
      have hdiv : (v % 2 ^ (m + 1)) / 2 = (v / 2) % 2 ^ m := by
        have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
        rw [hpow, Nat.mod_mul_right_div_self]
      rw [hdiv]
      exact ih (v / 2) j (by omega)

lemma tableIndex_succ {k : ℕ} (u : Fin (k + 1) → Bool) :
    tableIndex u = (if u 0 = true then 1 else 0) + 2 * tableIndex (fun i : Fin k => u i.succ) := by
  unfold tableIndex
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fin.val_succ, pow_succ]
  split_ifs <;> ring

lemma tableIndex_lt {k : ℕ} (u : Fin k → Bool) : tableIndex u < 2 ^ k := by
  induction k with
  | zero => simp [tableIndex]
  | succ k ih =>
    rw [tableIndex_succ, pow_succ]
    have h := ih (fun i : Fin k => u i.succ)
    split_ifs <;> omega

lemma testBit_tableIndex {k : ℕ} :
    ∀ (u : Fin k → Bool) (j : ℕ),
      (tableIndex u).testBit j = if h : j < k then u ⟨j, h⟩ else false := by
  induction k with
  | zero =>
    intro u j
    simp [tableIndex]
  | succ k ih =>
    intro u j
    rw [tableIndex_succ]
    cases j with
    | zero =>
      simp only [Nat.testBit_zero, Nat.zero_lt_succ, dite_true]
      cases hu : u 0 <;> simp [hu]
    | succ j =>
      rw [Nat.testBit_succ]
      have hdiv : ((if u 0 = true then 1 else 0) + 2 * tableIndex (fun i : Fin k => u i.succ)) / 2 =
          tableIndex (fun i : Fin k => u i.succ) := by
        split_ifs <;> omega
      rw [hdiv, ih (fun i : Fin k => u i.succ) j]
      by_cases hj : j < k
      · have hj1 : j + 1 < k + 1 := by omega
        simp [hj, hj1, Fin.succ]
      · have hj1 : ¬ (j + 1 < k + 1) := by omega
        simp [hj, hj1]

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wf_nil (w : List Bool) : wf [] w = w := rfl

lemma wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma wf_append (gs1 gs2 : List Gate) (w : List Bool) :
    wf (gs1 ++ gs2) w = wf gs2 (wf gs1 w) := by
  simp [wf, List.foldl_append]

lemma wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    rw [wf_cons, ih]
    simp
    omega

lemma getD_snoc_lt (L : List Bool) (a : Bool) (i : ℕ) (h : i < L.length) :
    (L ++ [a]).getD i false = L.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

lemma wf_getD_lt (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [wf_cons, ih]
    · exact getD_snoc_lt _ _ _ hi
    · simp; omega

def Mono2List (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma Mono2List.to_monotone2 {gs : List Gate} (h : Mono2List gs) (out : ℕ) :
    Monotone2 ⟨gs, out⟩ := by
  intro g hg
  have ⟨hop, hlen⟩ := h g hg
  exact ⟨by rcases hop with h1 | h1 <;> simp [h1], hlen⟩

lemma Mono2List.nil : Mono2List [] := by
  intro g hg
  simp at hg

lemma Mono2List.append {gs1 gs2 : List Gate} (h1 : Mono2List gs1) (h2 : Mono2List gs2) :
    Mono2List (gs1 ++ gs2) := by
  intro g hg
  rcases List.mem_append.mp hg with hg1 | hg2
  · exact h1 g hg1
  · exact h2 g hg2

def gAnd (u v : ℕ) : Gate := ⟨GateOp.and, [u, v]⟩
def gOr (u v : ℕ) : Gate := ⟨GateOp.or, [u, v]⟩
def gTrue : Gate := ⟨GateOp.and, []⟩
def gFalse : Gate := ⟨GateOp.or, []⟩

lemma mono2_gAnd (u v : ℕ) : Mono2List [gAnd u v] := by
  intro g hg; simp at hg; subst hg; simp [gAnd]

lemma mono2_gOr (u v : ℕ) : Mono2List [gOr u v] := by
  intro g hg; simp at hg; subst hg; simp [gOr]

lemma mono2_gTrue : Mono2List [gTrue] := by
  intro g hg; simp at hg; subst hg; simp [gTrue]

lemma mono2_gFalse : Mono2List [gFalse] := by
  intro g hg; simp at hg; subst hg; simp [gFalse]

lemma wf_gAnd_eq (u v : ℕ) (w : List Bool) :
    (wf [gAnd u v] w).getD w.length false = (w.getD u false && w.getD v false) := by
  simp [wf, gAnd, GateOp.eval]

lemma wf_gOr_eq (u v : ℕ) (w : List Bool) :
    (wf [gOr u v] w).getD w.length false = (w.getD u false || w.getD v false) := by
  simp [wf, gOr, GateOp.eval]

lemma wf_gTrue_eq (w : List Bool) :
    (wf [gTrue] w).getD w.length false = true := by
  simp [wf, gTrue, GateOp.eval]

lemma wf_gFalse_eq (w : List Bool) :
    (wf [gFalse] w).getD w.length false = false := by
  simp [wf, gFalse, GateOp.eval]

lemma buildAndPairs (n base : ℕ) (u v : ℕ → ℕ)
    (huv : ∀ i < n, u i < base ∧ v i < base) :
    ∃ gs : List Gate,
      Mono2List gs ∧ gs.length = n ∧
      ∀ (w : List Bool), w.length = base →
        ∀ i < n, (wf gs w).getD (base + i) false = (w.getD (u i) false && w.getD (v i) false) := by
  induction n with
  | zero =>
    refine ⟨[], Mono2List.nil, rfl, ?_⟩
    intro w _ i hi; omega
  | succ n ih =>
    obtain ⟨gs, hmono, hlen, heval⟩ := ih (fun i hi => huv i (by omega))
    refine ⟨gs ++ [gAnd (u n) (v n)], hmono.append (mono2_gAnd _ _), by simp [hlen], ?_⟩
    intro w hw i hi
    rw [wf_append]
    have hlen1 : (wf gs w).length = base + n := by rw [wf_len, hw, hlen]
    by_cases hin : i < n
    · rw [wf_getD_lt [gAnd (u n) (v n)] (wf gs w) (base + i) (by omega)]
      exact heval w hw i hin
    · have hin_eq : i = n := by omega
      subst i
      rw [← hlen1, wf_gAnd_eq]
      have ⟨hu, hv⟩ := huv n (Nat.lt_succ_self n)
      rw [wf_getD_lt gs w (u n) (by omega), wf_getD_lt gs w (v n) (by omega)]

lemma buildXorPairs (m base : ℕ) (xp xn yp yn : ℕ → ℕ)
    (hbd : ∀ i < m, xp i < base ∧ xn i < base ∧ yp i < base ∧ yn i < base) :
    ∃ (gs : List Gate) (xorW xnorW : ℕ → ℕ),
      Mono2List gs ∧ gs.length = 6 * m ∧
      (∀ i < m, xorW i < base + gs.length ∧ xnorW i < base + gs.length) ∧
      ∀ (w : List Bool), w.length = base →
        ∀ i < m,
          (wf gs w).getD (xorW i) false =
            ((w.getD (xp i) false && w.getD (yn i) false) ||
              (w.getD (xn i) false && w.getD (yp i) false)) ∧
          (wf gs w).getD (xnorW i) false =
            ((w.getD (xp i) false && w.getD (yp i) false) ||
              (w.getD (xn i) false && w.getD (yn i) false)) := by
  induction m with
  | zero =>
    refine ⟨[], fun _ => 0, fun _ => 0, Mono2List.nil, rfl, ?_, ?_⟩
    · intro i hi; omega
    · intro w _ i hi; omega
  | succ m ih =>
    obtain ⟨gs, xorW, xnorW, hmono, hlen, hlt, heval⟩ := ih (fun i hi => hbd i (by omega))
    let b := base + 6 * m
    let step : List Gate :=
      [gAnd (xp m) (yn m), gAnd (xn m) (yp m), gOr b (b + 1),
       gAnd (xp m) (yp m), gAnd (xn m) (yn m), gOr (b + 3) (b + 4)]
    have hstep_mono : Mono2List step := by
      intro g hg
      simp only [step, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gAnd, gOr]
    have hstep_len : step.length = 6 := rfl
    refine ⟨gs ++ step,
      fun i => if i < m then xorW i else b + 2,
      fun i => if i < m then xnorW i else b + 5,
      hmono.append hstep_mono, by simp [hlen, hstep_len]; omega, ?_, ?_⟩
    · intro i hi
      by_cases him : i < m
      · have ⟨h1, h2⟩ := hlt i him
        simp only [him, ↓reduceIte, List.length_append, hlen, hstep_len] at h1 h2 ⊢
        omega
      · simp only [him, ↓reduceIte, List.length_append, hlen, hstep_len, b]
        omega
    · intro w hw i hi
      rw [wf_append]
      have hlen1 : (wf gs w).length = b := by rw [wf_len, hw, hlen]
      by_cases him : i < m
      · simp only [him, ↓reduceIte]
        have ⟨h1, h2⟩ := hlt i him
        rw [wf_getD_lt step (wf gs w) (xorW i) (by omega),
            wf_getD_lt step (wf gs w) (xnorW i) (by omega)]
        exact heval w hw i him
      · have him_eq : i = m := by omega
        subst i
        simp only [lt_irrefl, ↓reduceIte]
        have ⟨hxp, hxn, hyp, hyn⟩ := hbd m (Nat.lt_succ_self m)
        let w0 := wf gs w
        have hw0 : w0.length = b := hlen1
        have hread : ∀ u < base, w0.getD u false = w.getD u false :=
          fun u hu => wf_getD_lt gs w u (by omega)
        have hstep_split : step =
            ([gAnd (xp m) (yn m)] ++ [gAnd (xn m) (yp m)] ++ [gOr b (b + 1)]) ++
            ([gAnd (xp m) (yp m)] ++ [gAnd (xn m) (yn m)] ++ [gOr (b + 3) (b + 4)]) := rfl
        let w1 := wf [gAnd (xp m) (yn m)] w0
        let w2 := wf [gAnd (xn m) (yp m)] w1
        let w3 := wf [gOr b (b + 1)] w2
        let w4 := wf [gAnd (xp m) (yp m)] w3
        let w5 := wf [gAnd (xn m) (yn m)] w4
        let w6 := wf [gOr (b + 3) (b + 4)] w5
        have hw1_len : w1.length = b + 1 := by simp [w1, wf_len, hw0]
        have hw2_len : w2.length = b + 2 := by simp [w2, wf_len, hw1_len]
        have hw3_len : w3.length = b + 3 := by simp [w3, wf_len, hw2_len]
        have hw4_len : w4.length = b + 4 := by simp [w4, wf_len, hw3_len]
        have hw5_len : w5.length = b + 5 := by simp [w5, wf_len, hw4_len]
        have hwf_eq : wf step w0 = w6 := by
          simp only [hstep_split, wf_append, w1, w2, w3, w4, w5, w6]
        have hv1 : w1.getD b false = (w.getD (xp m) false && w.getD (yn m) false) := by
          rw [← hw0, wf_gAnd_eq, hread _ hxp, hread _ hyn]
        have hv2 : w2.getD (b + 1) false = (w.getD (xn m) false && w.getD (yp m) false) := by
          rw [← hw1_len, wf_gAnd_eq,
              wf_getD_lt [gAnd (xp m) (yn m)] w0 (xn m) (by omega),
              wf_getD_lt [gAnd (xp m) (yn m)] w0 (yp m) (by omega),
              hread _ hxn, hread _ hyp]
        have hv3 : w3.getD (b + 2) false =
            ((w.getD (xp m) false && w.getD (yn m) false) ||
              (w.getD (xn m) false && w.getD (yp m) false)) := by
          rw [← hw2_len, wf_gOr_eq,
              wf_getD_lt [gAnd (xn m) (yp m)] w1 b (by omega), hv1, hv2]
        have hv4 : w4.getD (b + 3) false = (w.getD (xp m) false && w.getD (yp m) false) := by
          have hw3_eq : w3 = wf ([gAnd (xp m) (yn m)] ++ [gAnd (xn m) (yp m)] ++ [gOr b (b + 1)]) w0 := by
            simp only [w3, w2, w1, wf_append]
          rw [← hw3_len, wf_gAnd_eq, hw3_eq,
              wf_getD_lt _ w0 (xp m) (by omega),
              wf_getD_lt _ w0 (yp m) (by omega),
              hread _ hxp, hread _ hyp]
        have hv5 : w5.getD (b + 4) false = (w.getD (xn m) false && w.getD (yn m) false) := by
          have hw4_eq : w4 = wf (([gAnd (xp m) (yn m)] ++ [gAnd (xn m) (yp m)] ++ [gOr b (b + 1)]) ++
              [gAnd (xp m) (yp m)]) w0 := by
            simp only [w4, w3, w2, w1, wf_append]
          rw [← hw4_len, wf_gAnd_eq, hw4_eq,
              wf_getD_lt _ w0 (xn m) (by omega),
              wf_getD_lt _ w0 (yn m) (by omega),
              hread _ hxn, hread _ hyn]
        have hv6 : w6.getD (b + 5) false =
            ((w.getD (xp m) false && w.getD (yp m) false) ||
              (w.getD (xn m) false && w.getD (yn m) false)) := by
          rw [← hw5_len, wf_gOr_eq,
              wf_getD_lt [gAnd (xn m) (yn m)] w4 (b + 3) (by omega), hv4, hv5]
        constructor
        · rw [hwf_eq]
          have hw6_from3 : w6 = wf ([gAnd (xp m) (yp m)] ++ [gAnd (xn m) (yn m)] ++ [gOr (b + 3) (b + 4)]) w3 := by
            simp only [w6, w5, w4, wf_append]
          rw [hw6_from3, wf_getD_lt _ w3 (b + 2) (by omega), hv3]
        · rw [hwf_eq, hv6]

lemma list_all_congr {α : Type*} {l : List α} {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [h x (by simp), ih (fun a ha => h a (by simp [ha]))]

lemma list_any_congr {α : Type*} {l : List α} {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [h x (by simp), ih (fun a ha => h a (by simp [ha]))]

lemma buildFoldAnd (ws : List ℕ) :
    ∀ (base accW : ℕ), accW < base → (∀ u ∈ ws, u < base) →
    ∃ (gs : List Gate) (out : ℕ),
      Mono2List gs ∧ gs.length = ws.length ∧ out < base + gs.length ∧
      ∀ (w : List Bool), w.length = base →
        (wf gs w).getD out false = (w.getD accW false && ws.all (fun u => w.getD u false)) := by
  induction ws with
  | nil =>
    intro base accW hacc _
    refine ⟨[], accW, Mono2List.nil, rfl, by simpa using hacc, ?_⟩
    intro w _
    simp [wf]
  | cons u us ih =>
    intro base accW hacc hws
    have hu : u < base := hws u (by simp)
    have hus : ∀ v ∈ us, v < base + 1 := fun v hv => by
      have := hws v (by simp [hv])
      omega
    obtain ⟨gs, out, hmono, hlen, hout, heval⟩ := ih (base + 1) base (by omega) hus
    refine ⟨[gAnd accW u] ++ gs, out, (mono2_gAnd accW u).append hmono, by simp [hlen],
      by simp [hlen]; omega, ?_⟩
    intro w hw
    rw [wf_append]
    have hlen1 : (wf [gAnd accW u] w).length = base + 1 := by simp [wf_len, hw]
    rw [heval _ hlen1, ← hw, wf_gAnd_eq]
    have hall : us.all (fun v => (wf [gAnd accW u] w).getD v false) =
        us.all (fun v => w.getD v false) := by
      apply list_all_congr
      intro v hv
      have hv_lt : v < base := hws v (by simp [hv])
      rw [wf_getD_lt [gAnd accW u] w v (by omega)]
    rw [hall, List.all_cons, Bool.and_assoc]

lemma buildFoldOr (ws : List ℕ) :
    ∀ (base accW : ℕ), accW < base → (∀ u ∈ ws, u < base) →
    ∃ (gs : List Gate) (out : ℕ),
      Mono2List gs ∧ gs.length = ws.length ∧ out < base + gs.length ∧
      ∀ (w : List Bool), w.length = base →
        (wf gs w).getD out false = (w.getD accW false || ws.any (fun u => w.getD u false)) := by
  induction ws with
  | nil =>
    intro base accW hacc _
    refine ⟨[], accW, Mono2List.nil, rfl, by simpa using hacc, ?_⟩
    intro w _
    simp [wf]
  | cons u us ih =>
    intro base accW hacc hws
    have hu : u < base := hws u (by simp)
    have hus : ∀ v ∈ us, v < base + 1 := fun v hv => by
      have := hws v (by simp [hv])
      omega
    obtain ⟨gs, out, hmono, hlen, hout, heval⟩ := ih (base + 1) base (by omega) hus
    refine ⟨[gOr accW u] ++ gs, out, (mono2_gOr accW u).append hmono, by simp [hlen],
      by simp [hlen]; omega, ?_⟩
    intro w hw
    rw [wf_append]
    have hlen1 : (wf [gOr accW u] w).length = base + 1 := by simp [wf_len, hw]
    rw [heval _ hlen1, ← hw, wf_gOr_eq]
    have hany : us.any (fun v => (wf [gOr accW u] w).getD v false) =
        us.any (fun v => w.getD v false) := by
      apply list_any_congr
      intro v hv
      have hv_lt : v < base := hws v (by simp [hv])
      rw [wf_getD_lt [gOr accW u] w v (by omega)]
    rw [hany, List.any_cons, Bool.or_assoc]

lemma buildDecoder (m : ℕ) :
    ∀ (base rootW : ℕ) (posBit negBit : ℕ → ℕ),
      rootW < base →
      (∀ j < m, posBit j < base ∧ negBit j < base) →
      ∃ (gs : List Gate) (sel : ℕ → ℕ),
        Mono2List gs ∧ gs.length ≤ 2 * 2 ^ m ∧
        (∀ t < 2 ^ m, sel t < base + gs.length) ∧
        ∀ (w : List Bool) (rb : Bool) (v : ℕ),
          w.length = base →
          w.getD rootW false = rb →
          (∀ j < m, w.getD (posBit j) false = v.testBit j ∧
            w.getD (negBit j) false = !(v.testBit j)) →
          ∀ t < 2 ^ m, (wf gs w).getD (sel t) false = (rb && decide (v % 2 ^ m = t)) := by
  induction m with
  | zero =>
    intro base rootW posBit negBit hroot _
    refine ⟨[], fun _ => rootW, Mono2List.nil, by simp, ?_, ?_⟩
    · intro t _; simpa using hroot
    · intro w rb v _ hrb _ t ht
      have ht0 : t = 0 := by omega
      subst ht0
      simp only [wf, List.foldl_nil, pow_zero, Nat.mod_one, decide_true, Bool.and_true, hrb]
  | succ m ih =>
    intro base rootW posBit negBit hroot hbits
    obtain ⟨gs1, sel1, hmono1, hlen1, hlt1, heval1⟩ :=
      ih base rootW posBit negBit hroot (fun j hj => hbits j (by omega))
    let base1 := base + gs1.length
    have hbitm := hbits m (Nat.lt_succ_self m)
    let uFn : ℕ → ℕ := fun t => sel1 (t % 2 ^ m)
    let vFn : ℕ → ℕ := fun t => if t < 2 ^ m then negBit m else posBit m
    have huv : ∀ t < 2 ^ (m + 1), uFn t < base1 ∧ vFn t < base1 := by
      intro t _
      constructor
      · exact hlt1 (t % 2 ^ m) (Nat.mod_lt t (Nat.two_pow_pos m))
      · dsimp only [vFn]
        split_ifs <;> omega
    obtain ⟨gs2, hmono2, hlen2, heval2⟩ := buildAndPairs (2 ^ (m + 1)) base1 uFn vFn huv
    refine ⟨gs1 ++ gs2, fun t => base1 + t, hmono1.append hmono2, ?_, ?_, ?_⟩
    · simp only [List.length_append, hlen2]
      have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
      omega
    · intro t ht
      simp only [List.length_append, hlen2, base1]
      omega
    · intro w rb v hw hrb hvb t ht
      rw [wf_append]
      have hw1 : (wf gs1 w).length = base1 := by rw [wf_len, hw]
      rw [heval2 (wf gs1 w) hw1 t ht]
      have hsel : (wf gs1 w).getD (uFn t) false = (rb && decide (v % 2 ^ m = t % 2 ^ m)) :=
        heval1 w rb v hw hrb (fun j hj => hvb j (by omega)) (t % 2 ^ m)
          (Nat.mod_lt t (Nat.two_pow_pos m))
      have hbitval : (wf gs1 w).getD (vFn t) false =
          if t < 2 ^ m then !(v.testBit m) else v.testBit m := by
        dsimp only [vFn]
        split_ifs
        · rw [wf_getD_lt gs1 w (negBit m) (by omega), (hvb m (Nat.lt_succ_self m)).2]
        · rw [wf_getD_lt gs1 w (posBit m) (by omega), (hvb m (Nat.lt_succ_self m)).1]
      rw [hsel, hbitval, Bool.and_assoc]
      congr 1
      have hmod := mod_two_pow_succ m v
      have hvm : v % 2 ^ m < 2 ^ m := Nat.mod_lt v (Nat.two_pow_pos m)
      have hpow : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
      by_cases htm : t < 2 ^ m
      · simp only [htm, ↓reduceIte, Nat.mod_eq_of_lt htm]
        cases htb : v.testBit m
        · simp only [htb, Bool.not_false, Bool.and_true, Bool.false_eq_true, ↓reduceIte, add_zero] at hmod ⊢
          rw [hmod]
        · simp only [htb, Bool.not_true, Bool.and_false, ↓reduceIte] at hmod ⊢
          have hne : v % 2 ^ (m + 1) ≠ t := by omega
          simp [hne]
      · simp only [htm, ↓reduceIte]
        have htm2 : t % 2 ^ m = t - 2 ^ m := by
          have : t = (t - 2 ^ m) + 2 ^ m := by omega
          conv_lhs => rw [this]
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [htm2]
        cases htb : v.testBit m
        · simp only [htb, Bool.and_false, Bool.false_eq_true, ↓reduceIte, add_zero] at hmod ⊢
          have hne : v % 2 ^ (m + 1) ≠ t := by omega
          simp [hne]
        · simp only [htb, Bool.and_true, ↓reduceIte] at hmod ⊢
          rw [hmod]
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_eq]
          omega

lemma conj1_decoders (k a : ℕ) (ha : 0 < a) (hak : 2 ^ a ≤ k) :
    let r := 2 ^ a
    ∃ (gsA : List Gate) (falseW anyOneHigh : ℕ) (selY selXor : ℕ → ℕ),
      Mono2List gsA ∧ gsA.length ≤ 8 * k + 4 * r + 2 ∧
      falseW < 4 * k + gsA.length ∧
      anyOneHigh < 4 * k + gsA.length ∧
      (∀ t < r, selY t < 4 * k + gsA.length ∧ selXor t < 4 * k + gsA.length) ∧
      ∀ (z : Fin (k + k) → Bool),
        let wInit := List.ofFn z ++ List.ofFn (fun i => !z i)
        let xVal := tableIndex (fun i : Fin k => z (Fin.castAdd k i))
        let yVal := tableIndex (fun j : Fin k => z (Fin.natAdd k j))
        let wA := wf gsA wInit
        wA.getD falseW false = false ∧
        wA.getD anyOneHigh false = decide (r ≤ Nat.xor xVal yVal) ∧
        (∀ t < r, wA.getD (selY t) false = decide (yVal % r = t) ∧
          wA.getD (selXor t) false = decide (Nat.xor xVal yVal = t)) := by
  intro r
  have har : a < r := Nat.lt_two_pow_self
  have hak_lt : a < k := lt_of_lt_of_le har hak
  let base0 := 4 * k
  let gs0 : List Gate := [gFalse, gTrue]
  have hmono0 : Mono2List gs0 := mono2_gFalse.append mono2_gTrue
  have hlen0 : gs0.length = 2 := rfl
  let falseW := base0
  let trueW := base0 + 1
  let base1 := base0 + gs0.length
  obtain ⟨gs1, xorW, xnorW, hmono1, hlen1, hlt1, heval1⟩ :=
    buildXorPairs k base1 (fun i => i) (fun i => 2 * k + i) (fun i => k + i) (fun i => 3 * k + i)
      (fun i hi => by simp only [base1, base0, hlen0]; omega)
  let base2 := base1 + gs1.length
  let highXnor : List ℕ := (List.range (k - a)).map (fun j => xnorW (a + j))
  obtain ⟨gs2, allZeroHigh, hmono2, hlen2, hlt2, heval2⟩ :=
    buildFoldAnd highXnor base2 trueW (by simp only [base2, base1, trueW, base0, hlen0]; omega)
      (by
        intro u hu
        rcases List.mem_map.mp hu with ⟨j, hj, rfl⟩
        have hj' : j < k - a := List.mem_range.mp hj
        exact (hlt1 (a + j) (by omega)).2)
  let base3 := base2 + gs2.length
  let highXor : List ℕ := (List.range (k - a)).map (fun j => xorW (a + j))
  obtain ⟨gs3, anyOneHigh, hmono3, hlen3, hlt3, heval3⟩ :=
    buildFoldOr highXor base3 falseW (by simp only [base3, base2, base1, falseW, base0, hlen0]; omega)
      (by
        intro u hu
        rcases List.mem_map.mp hu with ⟨j, hj, rfl⟩
        have hj' : j < k - a := List.mem_range.mp hj
        have := (hlt1 (a + j) (by omega)).1
        omega)
  let base4 := base3 + gs3.length
  obtain ⟨gs4, selY, hmono4, hlen4, hlt4, heval4⟩ :=
    buildDecoder a base4 trueW (fun j => k + j) (fun j => 3 * k + j)
      (by simp only [base4, base3, base2, base1, trueW, base0, hlen0]; omega)
      (fun j hj => by simp only [base4, base3, base2, base1, base0, hlen0]; omega)
  let base5 := base4 + gs4.length
  obtain ⟨gs5, selXor, hmono5, hlen5, hlt5, heval5⟩ :=
    buildDecoder a base5 allZeroHigh xorW xnorW
      (by simp only [base5, base4, base3]; omega)
      (fun j hj => by
        have := hlt1 j (by omega)
        simp only [base5, base4, base3, base2]
        omega)
  let gsA : List Gate := gs0 ++ gs1 ++ gs2 ++ gs3 ++ gs4 ++ gs5
  have hmonoA : Mono2List gsA :=
    ((((hmono0.append hmono1).append hmono2).append hmono3).append hmono4).append hmono5
  have hlenA_eq : gsA.length = gs0.length + gs1.length + gs2.length + gs3.length + gs4.length + gs5.length := by
    simp only [gsA, List.length_append]
  have hlenA : gsA.length ≤ 8 * k + 4 * r + 2 := by
    have h2 : gs2.length = k - a := by simp [hlen2, highXnor]
    have h3 : gs3.length = k - a := by simp [hlen3, highXor]
    rw [hlenA_eq, hlen0, hlen1, h2, h3]
    omega
  refine ⟨gsA, falseW, anyOneHigh, selY, selXor, hmonoA, hlenA, ?_, ?_, ?_, ?_⟩
  · simp only [falseW, base0, hlenA_eq, hlen0]; omega
  · simp only [hlenA_eq, base3, base2, base1, base0] at hlt3 ⊢; omega
  · intro t ht
    have h4 := hlt4 t ht
    have h5 := hlt5 t ht
    simp only [hlenA_eq, base5, base4, base3, base2, base1, base0] at h4 h5 ⊢
    exact ⟨by omega, by omega⟩
  · intro z wInit xVal yVal wA
    have hwInit_len : wInit.length = base0 := by
      simp [wInit, base0]
      omega
    have hxVal_lt : xVal < 2 ^ k := tableIndex_lt (fun i : Fin k => z (Fin.castAdd k i))
    have hyVal_lt : yVal < 2 ^ k := tableIndex_lt (fun j : Fin k => z (Fin.natAdd k j))
    have hxBit : ∀ (i : ℕ) (hi : i < k), xVal.testBit i = z (Fin.castAdd k ⟨i, hi⟩) := by
      intro i hi
      simp [xVal, testBit_tableIndex, hi]
    have hyBit : ∀ (j : ℕ) (hj : j < k), yVal.testBit j = z (Fin.natAdd k ⟨j, hj⟩) := by
      intro j hj
      simp [yVal, testBit_tableIndex, hj]
    have hwInit_x : ∀ i < k, wInit.getD i false = xVal.testBit i := by
      intro i hi
      have h1 : i < (List.ofFn z).length := by simp; omega
      simp only [wInit, List.getD_eq_getElem?_getD, List.getElem?_append_left h1,
        List.getElem?_ofFn, show i < k + k by omega, ↓reduceDIte, Option.getD_some]
      rw [hxBit i hi]
      rfl
    have hwInit_y : ∀ j < k, wInit.getD (k + j) false = yVal.testBit j := by
      intro j hj
      have h1 : k + j < (List.ofFn z).length := by simp; omega
      simp only [wInit, List.getD_eq_getElem?_getD, List.getElem?_append_left h1,
        List.getElem?_ofFn, show k + j < k + k by omega, ↓reduceDIte, Option.getD_some]
      rw [hyBit j hj]
      rfl
    have hwInit_nx : ∀ i < k, wInit.getD (2 * k + i) false = !(xVal.testBit i) := by
      intro i hi
      have h1 : (List.ofFn z).length ≤ 2 * k + i := by simp; omega
      simp only [wInit, List.getD_eq_getElem?_getD, List.getElem?_append_right h1,
        List.length_ofFn, List.getElem?_ofFn]
      have hsub : 2 * k + i - (k + k) = i := by omega
      simp only [hsub, show i < k + k by omega, ↓reduceDIte, Option.getD_some]
      rw [hxBit i hi]
      rfl
    have hwInit_ny : ∀ j < k, wInit.getD (3 * k + j) false = !(yVal.testBit j) := by
      intro j hj
      have h1 : (List.ofFn z).length ≤ 3 * k + j := by simp; omega
      simp only [wInit, List.getD_eq_getElem?_getD, List.getElem?_append_right h1,
        List.length_ofFn, List.getElem?_ofFn]
      have hsub : 3 * k + j - (k + k) = k + j := by omega
      simp only [hsub, show k + j < k + k by omega, ↓reduceDIte, Option.getD_some]
      rw [hyBit j hj]
      rfl
    let w1 := wf gs0 wInit
    let w2 := wf gs1 w1
    let w3 := wf gs2 w2
    let w4 := wf gs3 w3
    let w5 := wf gs4 w4
    let w6 := wf gs5 w5
    have hw1_len : w1.length = base1 := by simp [w1, wf_len, hwInit_len, base1]
    have hw2_len : w2.length = base2 := by simp [w2, wf_len, hw1_len, base2]
    have hw3_len : w3.length = base3 := by simp [w3, wf_len, hw2_len, base3]
    have hw4_len : w4.length = base4 := by simp [w4, wf_len, hw3_len, base4]
    have hw5_len : w5.length = base5 := by simp [w5, wf_len, hw4_len, base5]
    have hwA_eq : wA = w6 := by simp only [wA, gsA, w6, w5, w4, w3, w2, w1, wf_append]
    have hFalse_w1 : w1.getD falseW false = false := by
      have hl : wInit.length = falseW := hwInit_len
      rw [show w1 = wf ([gFalse] ++ [gTrue]) wInit from rfl, wf_append,
          wf_getD_lt [gTrue] (wf [gFalse] wInit) falseW (by simp [wf_len, hwInit_len, falseW]),
          ← hl, wf_gFalse_eq]
    have hTrue_w1 : w1.getD trueW false = true := by
      rw [show w1 = wf ([gFalse] ++ [gTrue]) wInit from rfl, wf_append]
      have hl : (wf [gFalse] wInit).length = trueW := by simp [wf_len, hwInit_len, trueW, base0]
      rw [← hl, wf_gTrue_eq]
    have hXor_w2 : ∀ i < k,
        w2.getD (xorW i) false = (Nat.xor xVal yVal).testBit i ∧
        w2.getD (xnorW i) false = !((Nat.xor xVal yVal).testBit i) := by
      intro i hi
      have ⟨h1, h2⟩ := heval1 w1 hw1_len i hi
      rw [wf_getD_lt gs0 wInit i (by rw [hwInit_len]; simp only [base0]; omega),
          wf_getD_lt gs0 wInit (2 * k + i) (by rw [hwInit_len]; simp only [base0]; omega),
          wf_getD_lt gs0 wInit (k + i) (by rw [hwInit_len]; simp only [base0]; omega),
          wf_getD_lt gs0 wInit (3 * k + i) (by rw [hwInit_len]; simp only [base0]; omega),
          hwInit_x i hi, hwInit_nx i hi, hwInit_y i hi, hwInit_ny i hi] at h1 h2
      rw [h1, h2, testBit_natXor]
      cases xVal.testBit i <;> cases yVal.testBit i <;> simp
    have hXor_lt_N : Nat.xor xVal yVal < 2 ^ k := xor_lt_two_pow_aux hxVal_lt hyVal_lt
    have hAllZero_w3 : w3.getD allZeroHigh false = decide (Nat.xor xVal yVal < r) := by
      rw [heval2 w2 hw2_len,
          wf_getD_lt gs1 w1 trueW (by rw [hw1_len]; simp only [trueW, base1, base0, hlen0]; omega), hTrue_w1,
          Bool.true_and]
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true, highXnor, List.mem_map, List.mem_range, forall_exists_index,
        and_imp, forall_apply_eq_imp_iff₂, decide_eq_true_eq]
      rw [show r = 2 ^ a from rfl, lt_two_pow_iff_testBit]
      constructor
      · intro h i hi
        by_cases hik : i < k
        · have := h (i - a) (by omega)
          have hidx : a + (i - a) = i := by omega
          rw [hidx, (hXor_w2 i hik).2] at this
          simpa using this
        · exact (lt_two_pow_iff_testBit k (Nat.xor xVal yVal)).mp hXor_lt_N i (by omega)
      · intro h j hj
        rw [(hXor_w2 (a + j) (by omega)).2, h (a + j) (by omega)]
        rfl
    have hAnyOne_w4 : w4.getD anyOneHigh false = decide (r ≤ Nat.xor xVal yVal) := by
      rw [heval3 w3 hw3_len,
          wf_getD_lt gs2 w2 falseW (by rw [hw2_len]; simp only [falseW, base2, base1, base0, hlen0]; omega),
          wf_getD_lt gs1 w1 falseW (by rw [hw1_len]; simp only [falseW, base1, base0, hlen0]; omega),
          hFalse_w1, Bool.false_or]
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true, highXor, List.mem_map, List.mem_range, exists_exists_and_eq_and,
        decide_eq_true_eq]
      constructor
      · rintro ⟨j, hj, hbit⟩
        rw [wf_getD_lt gs2 w2 (xorW (a + j)) (by rw [hw2_len]; exact (hlt1 (a + j) (by omega)).1),
            (hXor_w2 (a + j) (by omega)).1] at hbit
        by_contra hlt
        have hfalse := (lt_two_pow_iff_testBit a (Nat.xor xVal yVal)).mp (by omega) (a + j) (by omega)
        rw [hfalse] at hbit
        cases hbit
      · intro hge
        by_contra hnone
        push Not at hnone
        have hlt : Nat.xor xVal yVal < r := by
          rw [show r = 2 ^ a from rfl, lt_two_pow_iff_testBit]
          intro i hi
          by_cases hik : i < k
          · have := hnone (i - a) (by omega)
            have hidx : a + (i - a) = i := by omega
            rw [hidx, wf_getD_lt gs2 w2 (xorW i) (by rw [hw2_len]; exact (hlt1 i hik).1),
                (hXor_w2 i hik).1] at this
            exact Bool.eq_false_iff.mpr this
          · exact (lt_two_pow_iff_testBit k (Nat.xor xVal yVal)).mp hXor_lt_N i (by omega)
        omega
    have hSelY_w5 : ∀ t < r, w5.getD (selY t) false = decide (yVal % r = t) := by
      intro t ht
      have h4eq : w4 = wf (gs0 ++ gs1 ++ gs2 ++ gs3) wInit := by simp only [w4, w3, w2, w1, wf_append]
      have h1_4 : w4 = wf (gs1 ++ gs2 ++ gs3) w1 := by simp only [w4, w3, w2, wf_append]
      have hev := heval4 w4 true yVal hw4_len
        (by rw [h1_4, wf_getD_lt _ w1 trueW (by rw [hw1_len]; simp only [base1, trueW, base0, hlen0]; omega), hTrue_w1])
        (fun j hj => by
          constructor
          · rw [h4eq, wf_getD_lt _ wInit (k + j) (by rw [hwInit_len]; simp only [base0]; omega),
                hwInit_y j (by omega)]
          · rw [h4eq, wf_getD_lt _ wInit (3 * k + j) (by rw [hwInit_len]; simp only [base0]; omega),
                hwInit_ny j (by omega)])
        t ht
      simpa using hev
    have hSelXor_w6 : ∀ t < r, w6.getD (selXor t) false = decide (Nat.xor xVal yVal = t) := by
      intro t ht
      have h3_5 : w5 = wf (gs3 ++ gs4) w3 := by simp only [w5, w4, wf_append]
      have h2_5 : w5 = wf (gs2 ++ gs3 ++ gs4) w2 := by simp only [w5, w4, w3, wf_append]
      have hev := heval5 w5 (decide (Nat.xor xVal yVal < r)) (Nat.xor xVal yVal) hw5_len
        (by rw [h3_5, wf_getD_lt _ w3 allZeroHigh (by rw [hw3_len]; exact hlt2), hAllZero_w3])
        (fun j hj => by
          have hlt1j := hlt1 j (by omega)
          constructor
          · rw [h2_5, wf_getD_lt _ w2 (xorW j) (by rw [hw2_len]; exact hlt1j.1),
                (hXor_w2 j (by omega)).1]
          · rw [h2_5, wf_getD_lt _ w2 (xnorW j) (by rw [hw2_len]; exact hlt1j.2),
                (hXor_w2 j (by omega)).2])
        t ht
      rw [hev]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨hlt, hmod⟩
        rwa [Nat.mod_eq_of_lt hlt] at hmod
      · intro heq
        subst heq
        exact ⟨ht, Nat.mod_eq_of_lt ht⟩
    rw [hwA_eq]
    refine ⟨?_, ?_, ?_⟩
    · have h1_6 : w6 = wf (gs1 ++ gs2 ++ gs3 ++ gs4 ++ gs5) w1 := by
        simp only [w6, w5, w4, w3, w2, wf_append]
      rw [h1_6, wf_getD_lt _ w1 falseW (by rw [hw1_len]; simp only [base1, falseW, base0, hlen0]; omega),
          hFalse_w1]
    · have h4_6 : w6 = wf (gs4 ++ gs5) w4 := by simp only [w6, w5, wf_append]
      rw [h4_6, wf_getD_lt _ w4 anyOneHigh (by rw [hw4_len]; exact hlt3), hAnyOne_w4]
    · intro t ht
      exact ⟨by rw [wf_getD_lt gs5 w5 (selY t) (by rw [hw5_len]; exact hlt4 t ht), hSelY_w5 t ht],
        hSelXor_w6 t ht⟩

lemma conj1_circuit (k a : ℕ) (ha : 0 < a) (hak : 2 ^ a ≤ k)
    (D : Finset ℕ) (hDsub : D ⊆ Finset.range (2 ^ a)) :
    let N := 2 ^ k
    let r := 2 ^ a
    let I := Fin N
    let F := fun x y : I => x.val.testBit (y.val % r)
    let G := fun x y : I => xor (F x y) (decide (Nat.xor x.val y.val ∈ D))
    HasLitSize (k + k) (adjFun (k := k) (l := k) G) (8 * k + 12 * r + 12) := by
  intro N r I F G
  have hr_pos : 0 < r := Nat.two_pow_pos a
  obtain ⟨gsA, falseW, anyOneHigh, selY, selXor, hmonoA, hlenA, hfalseA, hanyA, hselA, hevalA⟩ :=
    conj1_decoders k a ha hak
  let baseA := 4 * k + gsA.length
  obtain ⟨gs6, hmono6, hlen6, heval6⟩ :=
    buildAndPairs r baseA selY (fun t => t)
      (fun t ht => ⟨(hselA t ht).1, by dsimp only [baseA]; omega⟩)
  let base7 := baseA + gs6.length
  let fPosTerms : List ℕ := (List.range r).map (fun t => baseA + t)
  obtain ⟨gs7, fPos, hmono7, hlen7, hlt7, heval7⟩ :=
    buildFoldOr fPosTerms base7 falseW
      (by dsimp only [base7]; omega)
      (by
        intro u hu
        rcases List.mem_map.mp hu with ⟨t, ht, rfl⟩
        have ht' : t < r := List.mem_range.mp ht
        dsimp only [base7]; omega)
  let base8 := base7 + gs7.length
  obtain ⟨gs8, hmono8, hlen8, heval8⟩ :=
    buildAndPairs r base8 selY (fun t => 2 * k + t)
      (fun t ht => ⟨lt_of_lt_of_le (hselA t ht).1 (by dsimp only [base8, base7]; omega),
        by dsimp only [base8, base7, baseA]; omega⟩)
  let base9 := base8 + gs8.length
  let fNegTerms : List ℕ := (List.range r).map (fun t => base8 + t)
  obtain ⟨gs9, fNeg, hmono9, hlen9, hlt9, heval9⟩ :=
    buildFoldOr fNegTerms base9 falseW
      (by dsimp only [base9, base8, base7]; omega)
      (by
        intro u hu
        rcases List.mem_map.mp hu with ⟨t, ht, rfl⟩
        have ht' : t < r := List.mem_range.mp ht
        dsimp only [base9]; omega)
  let base10 := base9 + gs9.length
  let dPosTerms : List ℕ := ((List.range r).filter (fun t => decide (t ∈ D))).map selXor
  obtain ⟨gs10, dPos, hmono10, hlen10, hlt10, heval10⟩ :=
    buildFoldOr dPosTerms base10 falseW
      (by dsimp only [base10, base9, base8, base7]; omega)
      (by
        intro u hu
        rcases List.mem_map.mp hu with ⟨t, ht, rfl⟩
        have ht' : t < r := List.mem_range.mp (List.mem_filter.mp ht).1
        have := (hselA t ht').2
        dsimp only [base10, base9, base8, base7, baseA] at this ⊢
        omega)
  let base11 := base10 + gs10.length
  let dNegTerms : List ℕ := ((List.range r).filter (fun t => decide (t ∉ D))).map selXor
  obtain ⟨gs11, dNeg, hmono11, hlen11, hlt11, heval11⟩ :=
    buildFoldOr dNegTerms base11 anyOneHigh
      (by dsimp only [base11, base10, base9, base8, base7]; omega)
      (by
        intro u hu
        rcases List.mem_map.mp hu with ⟨t, ht, rfl⟩
        have ht' : t < r := List.mem_range.mp (List.mem_filter.mp ht).1
        have := (hselA t ht').2
        dsimp only [base11, base10, base9, base8, base7, baseA] at this ⊢
        omega)
  let base12 := base11 + gs11.length
  let gs12 : List Gate := [gAnd fPos dNeg, gAnd fNeg dPos, gOr base12 (base12 + 1)]
  have hmono12 : Mono2List gs12 :=
    ((mono2_gAnd fPos dNeg).append (mono2_gAnd fNeg dPos)).append (mono2_gOr base12 (base12 + 1))
  let allGs : List Gate := gsA ++ gs6 ++ gs7 ++ gs8 ++ gs9 ++ gs10 ++ gs11 ++ gs12
  have hallMono : Mono2List allGs :=
    ((((((hmonoA.append hmono6).append hmono7).append hmono8).append hmono9).append hmono10).append
      hmono11).append hmono12
  have hdPos_len : dPosTerms.length ≤ r := by
    simp only [dPosTerms, List.length_map]
    exact le_trans (List.length_filter_le _ _) (by simp)
  have hdNeg_len : dNegTerms.length ≤ r := by
    simp only [dNegTerms, List.length_map]
    exact le_trans (List.length_filter_le _ _) (by simp)
  have hallLen : allGs.length ≤ 8 * k + 12 * r + 12 := by
    have h7 : gs7.length = r := by simp [hlen7, fPosTerms]
    have h9 : gs9.length = r := by simp [hlen9, fNegTerms]
    have h12 : gs12.length = 3 := rfl
    simp only [allGs, List.length_append, hlen6, h7, hlen8, h9, hlen10, hlen11, h12]
    omega
  refine ⟨⟨allGs, base12 + 2⟩, hallMono.to_monotone2 _, hallLen, ?_⟩
  intro z
  change (wf allGs (List.ofFn z ++ List.ofFn fun i => !z i)).getD (base12 + 2) false =
    adjFun (k := k) (l := k) G z
  let wInit := List.ofFn z ++ List.ofFn (fun i => !z i)
  have hwInit_len : wInit.length = 4 * k := by simp [wInit]; omega
  let xVal := tableIndex (fun i : Fin k => z (Fin.castAdd k i))
  let yVal := tableIndex (fun j : Fin k => z (Fin.natAdd k j))
  have hxVal_lt : xVal < N := tableIndex_lt (fun i : Fin k => z (Fin.castAdd k i))
  have hyVal_lt : yVal < N := tableIndex_lt (fun j : Fin k => z (Fin.natAdd k j))
  have hxBit : ∀ (i : ℕ) (hi : i < k), xVal.testBit i = z (Fin.castAdd k ⟨i, hi⟩) := by
    intro i hi; simp [xVal, testBit_tableIndex, hi]
  have hwInit_x : ∀ i < k, wInit.getD i false = xVal.testBit i := by
    intro i hi
    have h1 : i < (List.ofFn z).length := by simp; omega
    simp only [wInit, List.getD_eq_getElem?_getD, List.getElem?_append_left h1,
      List.getElem?_ofFn, show i < k + k by omega, ↓reduceDIte, Option.getD_some]
    rw [hxBit i hi]; rfl
  have hwInit_nx : ∀ i < k, wInit.getD (2 * k + i) false = !(xVal.testBit i) := by
    intro i hi
    have h1 : (List.ofFn z).length ≤ 2 * k + i := by simp; omega
    simp only [wInit, List.getD_eq_getElem?_getD, List.getElem?_append_right h1,
      List.length_ofFn, List.getElem?_ofFn]
    have hsub : 2 * k + i - (k + k) = i := by omega
    simp only [hsub, show i < k + k by omega, ↓reduceDIte, Option.getD_some]
    rw [hxBit i hi]; rfl
  let wA := wf gsA wInit
  let w7 := wf gs6 wA
  let w8 := wf gs7 w7
  let w9 := wf gs8 w8
  let w10 := wf gs9 w9
  let w11 := wf gs10 w10
  let w12 := wf gs11 w11
  have hwA_len : wA.length = baseA := by simp [wA, wf_len, hwInit_len, baseA]
  have hw7_len : w7.length = base7 := by simp [w7, wf_len, hwA_len, base7]
  have hw8_len : w8.length = base8 := by simp [w8, wf_len, hw7_len, base8]
  have hw9_len : w9.length = base9 := by simp [w9, wf_len, hw8_len, base9]
  have hw10_len : w10.length = base10 := by simp [w10, wf_len, hw9_len, base10]
  have hw11_len : w11.length = base11 := by simp [w11, wf_len, hw10_len, base11]
  have hw12_len : w12.length = base12 := by simp [w12, wf_len, hw11_len, base12]
  have hFalse_wA : wA.getD falseW false = false := (hevalA z).1
  have hAnyOne_wA : wA.getD anyOneHigh false = decide (r ≤ Nat.xor xVal yVal) := (hevalA z).2.1
  have hSel_wA : ∀ t < r, wA.getD (selY t) false = decide (yVal % r = t) ∧
      wA.getD (selXor t) false = decide (Nat.xor xVal yVal = t) := (hevalA z).2.2
  have hfPos_w8 : w8.getD fPos false = xVal.testBit (yVal % r) := by
    rw [heval7 w7 hw7_len,
        wf_getD_lt gs6 wA falseW (by rw [hwA_len]; exact hfalseA),
        hFalse_wA, Bool.false_or]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, fPosTerms, List.mem_map, List.mem_range, exists_exists_and_eq_and]
    constructor
    · rintro ⟨t, ht, hv⟩
      rw [heval6 wA hwA_len t ht, (hSel_wA t ht).1,
          wf_getD_lt gsA wInit t (by rw [hwInit_len]; omega), hwInit_x t (by omega)] at hv
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
      rw [hv.1]; exact hv.2
    · intro hbit
      refine ⟨yVal % r, Nat.mod_lt yVal hr_pos, ?_⟩
      have hmod_lt : yVal % r < r := Nat.mod_lt yVal hr_pos
      rw [heval6 wA hwA_len _ hmod_lt, (hSel_wA _ hmod_lt).1,
          wf_getD_lt gsA wInit _ (by rw [hwInit_len]; omega),
          hwInit_x _ (lt_of_lt_of_le hmod_lt hak)]
      simp [hbit]
  have hfNeg_w10 : w10.getD fNeg false = !(xVal.testBit (yVal % r)) := by
    have hA_9 : w9 = wf (gs6 ++ gs7 ++ gs8) wA := by simp only [w9, w8, w7, wf_append]
    have hA_8 : w8 = wf (gs6 ++ gs7) wA := by simp only [w8, w7, wf_append]
    have h0_8 : w8 = wf (gsA ++ gs6 ++ gs7) wInit := by simp only [w8, w7, wA, wf_append]
    rw [heval9 w9 hw9_len,
        hA_9, wf_getD_lt _ wA falseW (by rw [hwA_len]; exact hfalseA),
        hFalse_wA, Bool.false_or]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, fNegTerms, List.mem_map, List.mem_range, exists_exists_and_eq_and]
    constructor
    · rintro ⟨t, ht, hv⟩
      rw [← hA_9, heval8 w8 hw8_len t ht,
          hA_8, wf_getD_lt _ wA (selY t) (by rw [hwA_len]; exact (hselA t ht).1),
          (hSel_wA t ht).1,
          ← hA_8, h0_8, wf_getD_lt _ wInit (2 * k + t) (by rw [hwInit_len]; omega),
          hwInit_nx t (by omega)] at hv
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
      rw [hv.1]; exact hv.2
    · intro hbit
      have hmod_lt : yVal % r < r := Nat.mod_lt yVal hr_pos
      refine ⟨yVal % r, hmod_lt, ?_⟩
      rw [← hA_9, heval8 w8 hw8_len _ hmod_lt,
          hA_8, wf_getD_lt _ wA (selY (yVal % r)) (by rw [hwA_len]; exact (hselA _ hmod_lt).1),
          (hSel_wA _ hmod_lt).1,
          ← hA_8, h0_8, wf_getD_lt _ wInit (2 * k + yVal % r) (by rw [hwInit_len]; omega),
          hwInit_nx _ (lt_of_lt_of_le hmod_lt hak)]
      simp [hbit]
  have hdPos_w11 : w11.getD dPos false = decide (Nat.xor xVal yVal ∈ D) := by
    have hA_10 : w10 = wf (gs6 ++ gs7 ++ gs8 ++ gs9) wA := by simp only [w10, w9, w8, w7, wf_append]
    rw [heval10 w10 hw10_len,
        hA_10, wf_getD_lt _ wA falseW (by rw [hwA_len]; exact hfalseA),
        hFalse_wA, Bool.false_or]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, dPosTerms, List.mem_map, List.mem_filter, List.mem_range,
      decide_eq_true_eq, exists_exists_and_eq_and]
    constructor
    · rintro ⟨t, ⟨ht, htD⟩, hv⟩
      rw [wf_getD_lt _ wA (selXor t) (by rw [hwA_len]; exact (hselA t ht).2),
          (hSel_wA t ht).2] at hv
      simp only [decide_eq_true_eq] at hv
      rwa [hv]
    · intro hmem
      have hlt : Nat.xor xVal yVal < r := Finset.mem_range.mp (hDsub hmem)
      refine ⟨Nat.xor xVal yVal, ⟨hlt, hmem⟩, ?_⟩
      rw [wf_getD_lt _ wA (selXor (Nat.xor xVal yVal)) (by rw [hwA_len]; exact (hselA _ hlt).2),
          (hSel_wA _ hlt).2]
      simp
  have hdNeg_w12 : w12.getD dNeg false = !(decide (Nat.xor xVal yVal ∈ D)) := by
    have hA_11 : w11 = wf (gs6 ++ gs7 ++ gs8 ++ gs9 ++ gs10) wA := by
      simp only [w11, w10, w9, w8, w7, wf_append]
    rw [heval11 w11 hw11_len,
        hA_11, wf_getD_lt _ wA anyOneHigh (by rw [hwA_len]; exact hanyA),
        hAnyOne_wA]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, List.any_eq_true, dNegTerms, List.mem_map, List.mem_filter,
      List.mem_range, decide_eq_true_eq, exists_exists_and_eq_and, Bool.not_eq_true',
      decide_eq_false_iff_not]
    constructor
    · rintro (hge | ⟨t, ⟨ht, htD⟩, hv⟩)
      · intro hmem
        have hlt : Nat.xor xVal yVal < r := Finset.mem_range.mp (hDsub hmem)
        omega
      · rw [wf_getD_lt _ wA (selXor t) (by rw [hwA_len]; exact (hselA t ht).2),
            (hSel_wA t ht).2] at hv
        simp only [decide_eq_true_eq] at hv
        rwa [hv]
    · intro hnmem
      by_cases hge : r ≤ Nat.xor xVal yVal
      · exact Or.inl hge
      · right
        have hlt : Nat.xor xVal yVal < r := by omega
        refine ⟨Nat.xor xVal yVal, ⟨hlt, hnmem⟩, ?_⟩
        rw [wf_getD_lt _ wA (selXor (Nat.xor xVal yVal)) (by rw [hwA_len]; exact (hselA _ hlt).2),
            (hSel_wA _ hlt).2]
        simp
  have hall_eq : wf allGs wInit = wf gs12 w12 := by
    simp only [allGs, w12, w11, w10, w9, w8, w7, wA, wf_append]
  rw [hall_eq]
  have hfPos_w12 : w12.getD fPos false = xVal.testBit (yVal % r) := by
    have h8_12 : w12 = wf (gs8 ++ gs9 ++ gs10 ++ gs11) w8 := by
      simp only [w12, w11, w10, w9, wf_append]
    rw [h8_12, wf_getD_lt _ w8 fPos (by rw [hw8_len]; exact hlt7), hfPos_w8]
  have hfNeg_w12 : w12.getD fNeg false = !(xVal.testBit (yVal % r)) := by
    have h10_12 : w12 = wf (gs10 ++ gs11) w10 := by simp only [w12, w11, wf_append]
    rw [h10_12, wf_getD_lt _ w10 fNeg (by rw [hw10_len]; exact hlt9), hfNeg_w10]
  have hdPos_w12 : w12.getD dPos false = decide (Nat.xor xVal yVal ∈ D) := by
    rw [wf_getD_lt gs11 w11 dPos (by rw [hw11_len]; exact hlt10), hdPos_w11]
  have hfNeg_lt12 : fNeg < w12.length := by
    rw [hw12_len]; dsimp only [base12, base11, base10]; omega
  have hdPos_lt12 : dPos < w12.length := by
    rw [hw12_len]; dsimp only [base12, base11]; omega
  have hgs12_split : gs12 = [gAnd fPos dNeg] ++ [gAnd fNeg dPos] ++ [gOr base12 (base12 + 1)] := rfl
  let u1 := wf [gAnd fPos dNeg] w12
  let u2 := wf [gAnd fNeg dPos] u1
  let u3 := wf [gOr base12 (base12 + 1)] u2
  have hu1_len : u1.length = base12 + 1 := by simp [u1, wf_len, hw12_len]
  have hu2_len : u2.length = base12 + 2 := by simp [u2, wf_len, hu1_len]
  have hu3_eq : wf gs12 w12 = u3 := by simp only [hgs12_split, wf_append, u1, u2, u3]
  have hval1 : u1.getD base12 false =
      (xVal.testBit (yVal % r) && !(decide (Nat.xor xVal yVal ∈ D))) := by
    rw [← hw12_len, wf_gAnd_eq, hfPos_w12, hdNeg_w12]
  have hval2 : u2.getD (base12 + 1) false =
      (!(xVal.testBit (yVal % r)) && decide (Nat.xor xVal yVal ∈ D)) := by
    rw [← hu1_len, wf_gAnd_eq,
        wf_getD_lt [gAnd fPos dNeg] w12 fNeg hfNeg_lt12,
        wf_getD_lt [gAnd fPos dNeg] w12 dPos hdPos_lt12,
        hfNeg_w12, hdPos_w12]
  rw [hu3_eq, ← hu2_len, wf_gOr_eq,
      wf_getD_lt [gAnd fNeg dPos] u1 base12 (by rw [hu1_len]; omega), hval1, hval2]
  have hfinX : (Fin.ofNat N xVal).val = xVal := Nat.mod_eq_of_lt hxVal_lt
  have hfinY : (Fin.ofNat N yVal).val = yVal := Nat.mod_eq_of_lt hyVal_lt
  change ((xVal.testBit (yVal % r) && !decide (Nat.xor xVal yVal ∈ D)) ||
      (!xVal.testBit (yVal % r) && decide (Nat.xor xVal yVal ∈ D))) =
    xor ((Fin.ofNat N xVal).val.testBit ((Fin.ofNat N yVal).val % r))
      (decide (Nat.xor (Fin.ofNat N xVal).val (Fin.ofNat N yVal).val ∈ D))
  rw [hfinX, hfinY]
  cases xVal.testBit (yVal % r) <;> cases decide (Nat.xor xVal yVal ∈ D) <;> rfl

lemma conj2_edits (k a : ℕ) (hak : 2 ^ a ≤ k)
    (D : Finset ℕ) (hDsub : D ⊆ Finset.range (2 ^ a)) :
    let N := 2 ^ k
    let r := 2 ^ a
    let I := Fin N
    let F := fun x y : I => x.val.testBit (y.val % r)
    let G := fun x y : I => xor (F x y) (decide (Nat.xor x.val y.val ∈ D))
    ∀ i : I, (Finset.univ.filter (fun j : I => G i j ≠ F i j)).card = D.card ∧
      (Finset.univ.filter (fun j : I => G j i ≠ F j i)).card = D.card := by
  intro N r I F G i
  have hrN : r < N := lt_of_le_of_lt hak Nat.lt_two_pow_self
  have hiff1 : ∀ j : I, G i j ≠ F i j ↔ Nat.xor i.val j.val ∈ D := by
    intro j
    change xor (F i j) (decide (Nat.xor i.val j.val ∈ D)) ≠ F i j ↔ _
    cases F i j <;> cases h : decide (Nat.xor i.val j.val ∈ D) <;> simp_all
  have hiff2 : ∀ j : I, G j i ≠ F j i ↔ Nat.xor i.val j.val ∈ D := by
    intro j
    change xor (F j i) (decide (Nat.xor j.val i.val ∈ D)) ≠ F j i ↔ _
    rw [natXor_comm]
    cases F j i <;> cases h : decide (Nat.xor i.val j.val ∈ D) <;> simp_all
  have hcard1 : (Finset.univ.filter (fun j : I => G i j ≠ F i j)).card = D.card := by
    symm
    apply Finset.card_bij (fun d hd =>
      (⟨Nat.xor i.val d, xor_lt_two_pow_aux i.isLt (lt_trans (Finset.mem_range.mp (hDsub hd)) hrN)⟩ : I))
    · intro d hd
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hiff1, natXor_cancel_left]
      exact hd
    · intro d1 _ d2 _ heq
      have hval : Nat.xor i.val d1 = Nat.xor i.val d2 := congrArg Fin.val heq
      have := congrArg (Nat.xor i.val) hval
      simpa [natXor_cancel_left] using this
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hiff1] at hj
      refine ⟨Nat.xor i.val j.val, hj, ?_⟩
      ext
      simp
  have hset_eq : Finset.univ.filter (fun j : I => G j i ≠ F j i) =
      Finset.univ.filter (fun j : I => G i j ≠ F i j) := by
    ext j
    simp [hiff1, hiff2]
  exact ⟨hcard1, by rw [hset_eq, hcard1]⟩

lemma card_fiber (k a : ℕ) (hak : 2 ^ a ≤ k) (t : ℕ) (ht : t < 2 ^ a) :
    (Finset.univ.filter (fun z : Fin (2 ^ k) => z.val % 2 ^ a = t)).card = 2 ^ k / 2 ^ a := by
  have hak_le : a ≤ k := le_of_lt (lt_of_lt_of_le Nat.lt_two_pow_self hak)
  have hdvd : 2 ^ a ∣ 2 ^ k := Nat.pow_dvd_pow 2 hak_le
  have hmul : (2 ^ k / 2 ^ a) * 2 ^ a = 2 ^ k := Nat.div_mul_cancel hdvd
  have hr_pos : 0 < 2 ^ a := Nat.two_pow_pos a
  symm
  rw [← Fintype.card_fin (2 ^ k / 2 ^ a), ← Finset.card_univ]
  apply Finset.card_bij (fun (q : Fin (2 ^ k / 2 ^ a)) _ =>
    (⟨q.val * 2 ^ a + t, by
      have h1 : (q.val + 1) * 2 ^ a ≤ (2 ^ k / 2 ^ a) * 2 ^ a :=
        Nat.mul_le_mul_right (2 ^ a) (Nat.succ_le_of_lt q.isLt)
      nlinarith⟩ : Fin (2 ^ k)))
  · intro q _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
  · intro q1 _ q2 _ heq
    have hval : q1.val * 2 ^ a + t = q2.val * 2 ^ a + t := congrArg Fin.val heq
    have : q1.val * 2 ^ a = q2.val * 2 ^ a := by omega
    exact Fin.ext (Nat.eq_of_mul_eq_mul_right hr_pos this)
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    have hq_lt : z.val / 2 ^ a < 2 ^ k / 2 ^ a :=
      (Nat.div_lt_iff_lt_mul hr_pos).mpr (by rw [hmul]; exact z.isLt)
    refine ⟨⟨z.val / 2 ^ a, hq_lt⟩, Finset.mem_univ _, ?_⟩
    ext
    have hdm := Nat.div_add_mod z.val (2 ^ a)
    rw [hz] at hdm
    linarith

lemma card_xor_diff_ge {α : Type*} [Fintype α] [DecidableEq α]
    (P Q : α → Bool) (E1 E2 : Finset α) (d : ℕ)
    (hM : 4 * d ≤ (Finset.univ.filter (fun z : α => P z ≠ Q z)).card)
    (hE1 : E1.card = d) (hE2 : E2.card = d) :
    2 * d ≤ (Finset.univ.filter
      (fun z : α => xor (P z) (decide (z ∈ E1)) ≠ xor (Q z) (decide (z ∈ E2)))).card := by
  let M := Finset.univ.filter (fun z : α => P z ≠ Q z)
  let S := Finset.univ.filter
    (fun z : α => xor (P z) (decide (z ∈ E1)) ≠ xor (Q z) (decide (z ∈ E2)))
  have hsub : M \ (E1 ∪ E2) ⊆ S := by
    intro z hz
    rw [Finset.mem_sdiff, Finset.mem_union] at hz
    have hzM := (Finset.mem_filter.mp hz.1).2
    have h1 : z ∉ E1 := fun h => hz.2 (Or.inl h)
    have h2 : z ∉ E2 := fun h => hz.2 (Or.inr h)
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, h1, h2, decide_false,
      Bool.xor_false]
    exact hzM
  have h1 : M.card ≤ (M \ (E1 ∪ E2)).card + (E1 ∪ E2).card := by
    have hsubU : M ⊆ (M \ (E1 ∪ E2)) ∪ (E1 ∪ E2) := by
      intro z hz
      by_cases h : z ∈ E1 ∪ E2
      · exact Finset.mem_union_right _ h
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hz, h⟩)
    exact le_trans (Finset.card_le_card hsubU) (Finset.card_union_le _ _)
  have h2 : (M \ (E1 ∪ E2)).card ≤ S.card := Finset.card_le_card hsub
  have h3 : (E1 ∪ E2).card ≤ E1.card + E2.card := Finset.card_union_le E1 E2
  change 4 * d ≤ M.card at hM
  change 2 * d ≤ S.card
  omega

lemma card_xor_diff_eq {α : Type*} [Fintype α] [DecidableEq α]
    (P Q : α → Bool) (E1 E2 : Finset α)
    (hPQ : ∀ z, P z = Q z) (hdisj : Disjoint E1 E2) :
    (Finset.univ.filter
      (fun z : α => xor (P z) (decide (z ∈ E1)) ≠ xor (Q z) (decide (z ∈ E2)))).card =
      E1.card + E2.card := by
  have hset : Finset.univ.filter
      (fun z : α => xor (P z) (decide (z ∈ E1)) ≠ xor (Q z) (decide (z ∈ E2))) = E1 ∪ E2 := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, hPQ z]
    by_cases h1 : z ∈ E1 <;> by_cases h2 : z ∈ E2
    · exfalso
      exact Finset.disjoint_left.mp hdisj h1 h2
    · cases Q z <;> simp [h1, h2]
    · cases Q z <;> simp [h1, h2]
    · cases Q z <;> simp [h1, h2]
  rw [hset, Finset.card_union_of_disjoint hdisj]

lemma xor_cancel_mid (a b c : ℕ) : Nat.xor (Nat.xor a c) (Nat.xor b c) = Nat.xor a b := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [testBit_natXor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i <;> rfl

lemma conj3_distances (k a : ℕ) (ha : 0 < a) (hak : 2 ^ a ≤ k)
    (D : Finset ℕ) (hDsub : D ⊆ Finset.range (2 ^ a)) (hDcard : 4 * D.card ≤ 2 ^ k / 2 ^ a) :
    let N := 2 ^ k
    let r := 2 ^ a
    let I := Fin N
    let F := fun x y : I => x.val.testBit (y.val % r)
    let G := fun x y : I => xor (F x y) (decide (Nat.xor x.val y.val ∈ D))
    ∀ f g : I → Bool,
      let T := fun x y : I => xor (G x y) (xor (f x) (g y))
      ∀ i j : I, i ≠ j →
        2 * D.card ≤ (Finset.univ.filter (fun z : I => T i z ≠ T j z)).card ∧
        2 * D.card ≤ (Finset.univ.filter (fun z : I => T z i ≠ T z j)).card := by
  intro N r I F G f g T i j hij
  have har : a < r := Nat.lt_two_pow_self
  have hak_le : a ≤ k := le_of_lt (lt_of_lt_of_le har hak)
  have hr_pos : 0 < r := Nat.two_pow_pos a
  have hr_ge2 : 2 ≤ r := by
    have : 2 ^ 1 ≤ 2 ^ a := Nat.pow_le_pow_right (by omega) ha
    simpa using this
  have hmul : (N / r) * r = N := Nat.div_mul_cancel (Nat.pow_dvd_pow 2 hak_le)
  have hNr_le_N : N / r ≤ N := Nat.div_le_self N r
  have hedits := conj2_edits k a hak D hDsub
  have hEcard_row : ∀ u : I, (Finset.univ.filter (fun z : I => Nat.xor u.val z.val ∈ D)).card = D.card := by
    intro u
    have heq : Finset.univ.filter (fun z : I => Nat.xor u.val z.val ∈ D) =
        Finset.univ.filter (fun z : I => G u z ≠ F u z) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, G]
      cases F u z <;> cases h : decide (Nat.xor u.val z.val ∈ D) <;> simp_all
    rw [heq]
    exact (hedits u).1
  have hEcard_col : ∀ u : I, (Finset.univ.filter (fun x : I => Nat.xor x.val u.val ∈ D)).card = D.card := by
    intro u
    have heq : Finset.univ.filter (fun x : I => Nat.xor x.val u.val ∈ D) =
        Finset.univ.filter (fun x : I => Nat.xor u.val x.val ∈ D) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [natXor_comm]
    rw [heq]
    exact hEcard_row u
  constructor
  · let c := xor (f i) (f j)
    let P : I → Bool := fun z => F i z
    let Q : I → Bool := fun z => xor (F j z) c
    let E1 : Finset I := Finset.univ.filter (fun z : I => Nat.xor i.val z.val ∈ D)
    let E2 : Finset I := Finset.univ.filter (fun z : I => Nat.xor j.val z.val ∈ D)
    have hrew : Finset.univ.filter (fun z : I => T i z ≠ T j z) =
        Finset.univ.filter
          (fun z : I => xor (P z) (decide (z ∈ E1)) ≠ xor (Q z) (decide (z ∈ E2))) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, T, G, P, Q, c, E1, E2]
      by_cases h1 : Nat.xor i.val z.val ∈ D <;> by_cases h2 : Nat.xor j.val z.val ∈ D <;>
        simp only [h1, h2, decide_true, decide_false] <;>
        cases F i z <;> cases F j z <;> cases f i <;> cases f j <;> cases g z <;> decide
    rw [hrew]
    by_cases hR1 : (∃ t0 < r, i.val.testBit t0 ≠ j.val.testBit t0) ∧
        (∃ t1 < r, i.val.testBit t1 = j.val.testBit t1)
    · apply card_xor_diff_ge P Q E1 E2 D.card _ (hEcard_row i) (hEcard_row j)
      cases hc : c
      · obtain ⟨t0, ht0, hne⟩ := hR1.1
        have hsub : Finset.univ.filter (fun z : I => z.val % r = t0) ⊆
            Finset.univ.filter (fun z : I => P z ≠ Q z) := by
          intro z hz
          have hmod := (Finset.mem_filter.mp hz).2
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, P, Q, F, hc, Bool.xor_false, hmod]
          exact hne
        have hcf := card_fiber k a hak t0 ht0
        exact le_trans hDcard (le_trans (le_of_eq hcf.symm) (Finset.card_le_card hsub))
      · obtain ⟨t1, ht1, heq⟩ := hR1.2
        have hsub : Finset.univ.filter (fun z : I => z.val % r = t1) ⊆
            Finset.univ.filter (fun z : I => P z ≠ Q z) := by
          intro z hz
          have hmod := (Finset.mem_filter.mp hz).2
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, P, Q, F, hc, Bool.xor_true, hmod, heq]
          cases j.val.testBit t1 <;> decide
        have hcf := card_fiber k a hak t1 ht1
        exact le_trans hDcard (le_trans (le_of_eq hcf.symm) (Finset.card_le_card hsub))
    · have hdisj : Disjoint E1 E2 := by
        rw [Finset.disjoint_left]
        intro z hz1 hz2
        have h1 : Nat.xor i.val z.val < r :=
          Finset.mem_range.mp (hDsub (Finset.mem_filter.mp hz1).2)
        have h2 : Nat.xor j.val z.val < r :=
          Finset.mem_range.mp (hDsub (Finset.mem_filter.mp hz2).2)
        have hdel_lt : Nat.xor i.val j.val < r := by
          rw [← xor_cancel_mid i.val j.val z.val]
          exact xor_lt_two_pow_aux h1 h2
        have hdel_ne : Nat.xor i.val j.val ≠ 0 := by
          intro h0
          have hv : i.val = j.val := natXor_eq_zero.mp h0
          exact hij (Fin.ext hv)
        have ht1 : i.val.testBit a = j.val.testBit a := by
          have hb := (lt_two_pow_iff_testBit a (Nat.xor i.val j.val)).mp hdel_lt a (le_refl a)
          rw [testBit_natXor] at hb
          cases hi : i.val.testBit a <;> cases hj : j.val.testBit a <;> simp_all
        have ht0 : ∃ b0 < r, i.val.testBit b0 ≠ j.val.testBit b0 := by
          by_contra hall
          push Not at hall
          apply hdel_ne
          apply Nat.eq_of_testBit_eq
          intro b
          rw [Nat.zero_testBit, testBit_natXor]
          by_cases hba : b < a
          · rw [hall b (lt_trans hba har)]
            cases j.val.testBit b <;> rfl
          · have hb := (lt_two_pow_iff_testBit a (Nat.xor i.val j.val)).mp hdel_lt b (by omega)
            rwa [testBit_natXor] at hb
        exact hR1 ⟨ht0, ⟨a, har, ht1⟩⟩
      have hcases : (∀ t < r, i.val.testBit t = j.val.testBit t) ∨
          (∀ t < r, i.val.testBit t ≠ j.val.testBit t) := by
        by_cases hne : ∃ t0 < r, i.val.testBit t0 ≠ j.val.testBit t0
        · right
          intro t ht heq
          exact hR1 ⟨hne, ⟨t, ht, heq⟩⟩
        · left
          push Not at hne
          exact hne
      rcases hcases with heq | hne
      · cases hc : c
        · have hPQ : ∀ z : I, P z = Q z := by
            intro z
            simp only [P, Q, F, hc, Bool.xor_false]
            exact heq (z.val % r) (Nat.mod_lt z.val hr_pos)
          rw [card_xor_diff_eq P Q E1 E2 hPQ hdisj, hEcard_row i, hEcard_row j]
          omega
        · apply card_xor_diff_ge P Q E1 E2 D.card _ (hEcard_row i) (hEcard_row j)
          have hall : Finset.univ.filter (fun z : I => P z ≠ Q z) = Finset.univ := by
            ext z
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true, P, Q, F, hc,
              Bool.xor_true, heq (z.val % r) (Nat.mod_lt z.val hr_pos)]
            cases j.val.testBit (z.val % r) <;> decide
          rw [hall, Finset.card_univ, Fintype.card_fin]
          exact le_trans hDcard hNr_le_N
      · cases hc : c
        · apply card_xor_diff_ge P Q E1 E2 D.card _ (hEcard_row i) (hEcard_row j)
          have hall : Finset.univ.filter (fun z : I => P z ≠ Q z) = Finset.univ := by
            ext z
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true, P, Q, F, hc,
              Bool.xor_false]
            exact hne (z.val % r) (Nat.mod_lt z.val hr_pos)
          rw [hall, Finset.card_univ, Fintype.card_fin]
          exact le_trans hDcard hNr_le_N
        · have hPQ : ∀ z : I, P z = Q z := by
            intro z
            simp only [P, Q, F, hc, Bool.xor_true]
            have h := hne (z.val % r) (Nat.mod_lt z.val hr_pos)
            cases hi : i.val.testBit (z.val % r) <;> cases hj : j.val.testBit (z.val % r) <;> simp_all
          rw [card_xor_diff_eq P Q E1 E2 hPQ hdisj, hEcard_row i, hEcard_row j]
          omega
  · let c := xor (g i) (g j)
    let P : I → Bool := fun x => F x i
    let Q : I → Bool := fun x => xor (F x j) c
    let E1 : Finset I := Finset.univ.filter (fun x : I => Nat.xor x.val i.val ∈ D)
    let E2 : Finset I := Finset.univ.filter (fun x : I => Nat.xor x.val j.val ∈ D)
    have hrew : Finset.univ.filter (fun x : I => T x i ≠ T x j) =
        Finset.univ.filter
          (fun x : I => xor (P x) (decide (x ∈ E1)) ≠ xor (Q x) (decide (x ∈ E2))) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, T, G, P, Q, c, E1, E2]
      by_cases h1 : Nat.xor x.val i.val ∈ D <;> by_cases h2 : Nat.xor x.val j.val ∈ D <;>
        simp only [h1, h2, decide_true, decide_false] <;>
        cases F x i <;> cases F x j <;> cases f x <;> cases g i <;> cases g j <;> decide
    rw [hrew]
    by_cases hmod : i.val % r = j.val % r
    · have hdisj : Disjoint E1 E2 := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        have h1 : Nat.xor i.val x.val < r := by
          rw [natXor_comm]
          exact Finset.mem_range.mp (hDsub (Finset.mem_filter.mp hx1).2)
        have h2 : Nat.xor j.val x.val < r := by
          rw [natXor_comm]
          exact Finset.mem_range.mp (hDsub (Finset.mem_filter.mp hx2).2)
        have hdel_lt : Nat.xor i.val j.val < r := by
          rw [← xor_cancel_mid i.val j.val x.val]
          exact xor_lt_two_pow_aux h1 h2
        have heq_val : i.val = j.val := by
          apply Nat.eq_of_testBit_eq
          intro b
          by_cases hba : b < a
          · rw [← testBit_mod_two_pow_lt a i.val b hba, hmod, testBit_mod_two_pow_lt a j.val b hba]
          · have hb := (lt_two_pow_iff_testBit a (Nat.xor i.val j.val)).mp hdel_lt b (by omega)
            rw [testBit_natXor] at hb
            cases hi : i.val.testBit b <;> cases hj : j.val.testBit b <;> simp_all
        exact hij (Fin.ext heq_val)
      cases hc : c
      · have hPQ : ∀ x : I, P x = Q x := by
          intro x
          simp only [P, Q, F, hc, Bool.xor_false, hmod]
        rw [card_xor_diff_eq P Q E1 E2 hPQ hdisj, hEcard_col i, hEcard_col j]
        omega
      · apply card_xor_diff_ge P Q E1 E2 D.card _ (hEcard_col i) (hEcard_col j)
        have hall : Finset.univ.filter (fun x : I => P x ≠ Q x) = Finset.univ := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true, P, Q, F, hc,
            Bool.xor_true, hmod]
          cases x.val.testBit (j.val % r) <;> decide
        rw [hall, Finset.card_univ, Fintype.card_fin]
        exact le_trans hDcard hNr_le_N
    · apply card_xor_diff_ge P Q E1 E2 D.card _ (hEcard_col i) (hEcard_col j)
      let u := i.val % r
      let v := j.val % r
      have hu : u < k := lt_of_lt_of_le (Nat.mod_lt i.val hr_pos) hak
      have hpow_u : 2 ^ u < N := Nat.pow_lt_pow_right (by omega) hu
      let phi : I → I := fun x => ⟨Nat.xor x.val (2 ^ u), xor_lt_two_pow_aux x.isLt hpow_u⟩
      have hphi_inv : ∀ x : I, phi (phi x) = x := by
        intro x
        ext
        simp only [phi]
        rw [natXor_comm (Nat.xor x.val (2 ^ u)) (2 ^ u), natXor_comm x.val (2 ^ u),
            natXor_cancel_left]
      have hphi_u : ∀ x : I, (phi x).val.testBit u = !(x.val.testBit u) := by
        intro x
        simp only [phi, testBit_natXor, Nat.testBit_two_pow_self]
        cases x.val.testBit u <;> rfl
      have hphi_v : ∀ x : I, (phi x).val.testBit v = x.val.testBit v := by
        intro x
        simp only [phi, testBit_natXor, Nat.testBit_two_pow, show u ≠ v from hmod, decide_false,
          Bool.xor_false]
      let M := Finset.univ.filter (fun x : I => P x ≠ Q x)
      let Mc := Finset.univ.filter (fun x : I => P x = Q x)
      have hM_eq_Mc : M.card = Mc.card := by
        apply Finset.card_bij (fun x _ => phi x)
        · intro x hx
          have hne := (Finset.mem_filter.mp hx).2
          simp only [Mc, Finset.mem_filter, Finset.mem_univ, true_and, P, Q, F] at hne ⊢
          change x.val.testBit u ≠ xor (x.val.testBit v) c at hne
          change (phi x).val.testBit u = xor ((phi x).val.testBit v) c
          rw [hphi_u x, hphi_v x]
          cases h1 : x.val.testBit u <;> cases h2 : x.val.testBit v <;> cases h3 : c <;> simp_all
        · intro x1 _ x2 _ heq
          have := congrArg phi heq
          simpa [hphi_inv] using this
        · intro y hy
          have heq := (Finset.mem_filter.mp hy).2
          refine ⟨phi y, ?_, hphi_inv y⟩
          simp only [M, Finset.mem_filter, Finset.mem_univ, true_and, P, Q, F] at heq ⊢
          change y.val.testBit u = xor (y.val.testBit v) c at heq
          change (phi y).val.testBit u ≠ xor ((phi y).val.testBit v) c
          rw [hphi_u y, hphi_v y]
          cases h1 : y.val.testBit u <;> cases h2 : y.val.testBit v <;> cases h3 : c <;> simp_all
      have hsum_card : M.card + Mc.card = N := by
        have hdisj : Disjoint M Mc := by
          rw [Finset.disjoint_left]
          intro x h1 h2
          exact (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
        have hunion : M ∪ Mc = Finset.univ := by
          ext x
          simp only [M, Mc, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          exact ne_or_eq (P x) (Q x)
        rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
      have h2M : 2 * M.card = N := by omega
      have h2Nr : 2 * (N / r) ≤ N := by
        calc 2 * (N / r) ≤ r * (N / r) := Nat.mul_le_mul_right (N / r) hr_ge2
          _ = N := by rw [Nat.mul_comm, hmul]
      have hDcard' : 4 * D.card ≤ N / r := hDcard
      change 4 * D.card ≤ M.card
      omega

lemma sum_erase_add {α : Type*} [DecidableEq α] (A : Finset α) (f : α → ℕ) :
    ∑ i ∈ A, ∑ j ∈ A.erase i, (f i + f j) = 2 * (A.card - 1) * ∑ i ∈ A, f i := by
  have hsplit : ∑ i ∈ A, ∑ j ∈ A.erase i, (f i + f j) =
      (∑ i ∈ A, ∑ _j ∈ A.erase i, f i) + (∑ i ∈ A, ∑ j ∈ A.erase i, f j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_add_distrib
  have h1 : ∑ i ∈ A, ∑ _j ∈ A.erase i, f i = (A.card - 1) * ∑ i ∈ A, f i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_const, Finset.card_erase_of_mem hi, smul_eq_mul]
  have h2 : ∑ i ∈ A, ∑ j ∈ A.erase i, f j = (A.card - 1) * ∑ j ∈ A, f j := by
    have hrew : ∀ i ∈ A, ∑ j ∈ A.erase i, f j = ∑ j ∈ A, if j = i then 0 else f j := by
      intro i _
      have hfilt : A.erase i = A.filter (fun j => j ≠ i) := by
        ext j; simp [Finset.mem_erase, and_comm]
      rw [hfilt, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i <;> simp [hji]
    rw [Finset.sum_congr rfl hrew, Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hinner : ∑ i ∈ A, (if j = i then 0 else f j) = ∑ _i ∈ A.erase j, f j := by
      have hfilt : A.erase j = A.filter (fun i => i ≠ j) := by
        ext i; simp [Finset.mem_erase, and_comm]
      rw [hfilt, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hij : j = i
      · simp [hij]
      · have hji : i ≠ j := Ne.symm hij
        simp [hij, hji]
    rw [hinner, Finset.sum_const, Finset.card_erase_of_mem hj, smul_eq_mul]
  rw [hsplit, h1, h2]
  ring

lemma add_mod_ne_self {N x d : ℕ} (hx : x < N) (hd0 : 0 < d) (hdN : d < N) :
    (x + d) % N ≠ x := by
  by_cases hlt : x + d < N
  · rw [Nat.mod_eq_of_lt hlt]
    omega
  · have hsub : (x + d) % N = x + d - N := by
      have : x + d = (x + d - N) + N := by omega
      conv_lhs => rw [this]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hsub]
    omega

lemma conj4_lower_bound (k a : ℕ) (ha : 0 < a) (hak : 2 ^ a ≤ k) (hq4 : 4 ≤ 2 ^ k / 2 ^ a) :
    let N := 2 ^ k
    let r := 2 ^ a
    let I := Fin N
    let F := fun x y : I => x.val.testBit (y.val % r)
    ∀ (s : ℕ) (H : I → I → Bool),
      (∀ i j : I, i ≠ j → i.val % r = j.val % r →
        2 * s ≤ (Finset.univ.filter (fun x : I => H x i ≠ H x j)).card) →
      let w := (Finset.univ.filter (fun z : I × I => H z.1 z.2 ≠ F z.1 z.2)).card
      N * s ≤ w ∧ (w = N * s →
        s ≤ r ∧ (∀ j : I, (Finset.univ.filter (fun x : I => H x j ≠ F x j)).card = s) ∧
        ∀ x i j : I, i ≠ j → i.val % r = j.val % r → H x i ≠ F x i → H x j = F x j) := by
  intro N r I F s H hH w
  have har : a < r := Nat.lt_two_pow_self
  have hak_le : a ≤ k := le_of_lt (lt_of_lt_of_le har hak)
  have hr_pos : 0 < r := Nat.two_pow_pos a
  have hN_pos : 0 < N := Nat.two_pow_pos k
  have hdvd : r ∣ N := Nat.pow_dvd_pow 2 hak_le
  let q := N / r
  have hq4' : 4 ≤ q := hq4
  have hmul : q * r = N := Nat.div_mul_cancel hdvd
  let wCol : I → ℕ := fun j => (Finset.univ.filter (fun x : I => H x j ≠ F x j)).card
  let fib : Fin r → Finset I := fun t => Finset.univ.filter (fun j : I => j.val % r = t.val)
  let ov : I → I → ℕ := fun i j =>
    (Finset.univ.filter (fun x : I => H x i ≠ F x i ∧ H x j ≠ F x j)).card
  have hw_eq : w = ∑ j : I, wCol j := by
    simp only [w, wCol, Finset.card_filter]
    rw [Fintype.sum_prod_type_right]
  have hfib_card : ∀ t : Fin r, (fib t).card = q :=
    fun t => card_fiber k a hak t.val t.isLt
  have hsum_fib : ∑ t : Fin r, ∑ j ∈ fib t, wCol j = w := by
    rw [hw_eq]
    have hrew : ∀ t : Fin r, ∑ j ∈ fib t, wCol j = ∑ j : I, if j.val % r = t.val then wCol j else 0 := by
      intro t
      simp only [fib, Finset.sum_filter]
    rw [Finset.sum_congr rfl (fun t _ => hrew t), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    have huniq : ∑ t : Fin r, (if j.val % r = t.val then wCol j else 0) =
        ∑ t : Fin r, (if t = ⟨j.val % r, Nat.mod_lt j.val hr_pos⟩ then wCol j else 0) := by
      apply Finset.sum_congr rfl
      intro t _
      by_cases h : t = ⟨j.val % r, Nat.mod_lt j.val hr_pos⟩
      · subst h; simp
      · have hne : j.val % r ≠ t.val := fun heq => h (Fin.ext heq.symm)
        simp [h, hne]
    rw [huniq, Finset.sum_ite_eq']
    simp
  have hpair_le : ∀ (i j : I), i ≠ j → i.val % r = j.val % r →
      2 * s + 2 * ov i j ≤ wCol i + wCol j := by
    intro i j hij hmod
    have hFij : ∀ x : I, F x i = F x j := fun x => by simp only [F, hmod]
    have hdist_eq : (Finset.univ.filter (fun x : I => H x i ≠ H x j)).card + 2 * ov i j =
        wCol i + wCol j := by
      simp only [ov, wCol, Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      rw [hFij x]
      cases H x i <;> cases H x j <;> cases F x j <;> decide
    have h2s := hH i j hij hmod
    omega
  have hfib_double : ∀ t : Fin r,
      2 * (q - 1) * (q * s) + 2 * (∑ i ∈ fib t, ∑ j ∈ (fib t).erase i, ov i j) ≤
        2 * (q - 1) * ∑ i ∈ fib t, wCol i := by
    intro t
    have h1 : ∑ i ∈ fib t, ∑ j ∈ (fib t).erase i, (2 * s + 2 * ov i j) ≤
        ∑ i ∈ fib t, ∑ j ∈ (fib t).erase i, (wCol i + wCol j) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have hij : i ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
      have hmod : i.val % r = j.val % r := by
        rw [(Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp (Finset.mem_erase.mp hj).2).2]
      exact hpair_le i j hij hmod
    have hlhs : ∑ i ∈ fib t, ∑ j ∈ (fib t).erase i, (2 * s + 2 * ov i j) =
        2 * (q - 1) * (q * s) + 2 * ∑ i ∈ fib t, ∑ j ∈ (fib t).erase i, ov i j := by
      have hsp : ∑ i ∈ fib t, ∑ j ∈ (fib t).erase i, (2 * s + 2 * ov i j) =
          (∑ i ∈ fib t, ∑ _j ∈ (fib t).erase i, (2 * s)) +
          (∑ i ∈ fib t, ∑ j ∈ (fib t).erase i, 2 * ov i j) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_add_distrib
      rw [hsp]
      congr 1
      · have hconst : ∑ i ∈ fib t, ∑ _j ∈ (fib t).erase i, (2 * s) =
            ∑ _i ∈ fib t, (q - 1) * (2 * s) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_const, Finset.card_erase_of_mem hi, hfib_card t, smul_eq_mul]
        rw [hconst, Finset.sum_const, hfib_card t, smul_eq_mul]
        ring
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
    have hrhs : ∑ i ∈ fib t, ∑ j ∈ (fib t).erase i, (wCol i + wCol j) =
        2 * (q - 1) * ∑ i ∈ fib t, wCol i := by
      rw [sum_erase_add, hfib_card t]
    omega
  have hfib_le : ∀ t : Fin r, q * s ≤ ∑ i ∈ fib t, wCol i := by
    intro t
    have hd := hfib_double t
    have hpos : 0 < 2 * (q - 1) := by omega
    exact Nat.le_of_mul_le_mul_left (by omega) hpos
  have hNs_le : N * s ≤ w := by
    rw [← hsum_fib]
    calc N * s = r * (q * s) := by rw [← hmul]; ring
      _ = ∑ _t : Fin r, (q * s) := by simp [Finset.sum_const]
      _ ≤ ∑ t : Fin r, ∑ i ∈ fib t, wCol i := Finset.sum_le_sum (fun t _ => hfib_le t)
  refine ⟨hNs_le, ?_⟩
  intro hw_eq_Ns
  have hfib_eq : ∀ t : Fin r, ∑ i ∈ fib t, wCol i = q * s := by
    have htot : ∑ t : Fin r, (q * s) = ∑ t : Fin r, ∑ i ∈ fib t, wCol i := by
      rw [hsum_fib, hw_eq_Ns]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      rw [← hmul]
      ring
    intro t
    exact ((Finset.sum_eq_sum_iff_of_le (fun u _ => hfib_le u)).mp htot t (Finset.mem_univ t)).symm
  have hpair_eq : ∀ (i j : I), i ≠ j → i.val % r = j.val % r →
      wCol i + wCol j = 2 * s ∧ ov i j = 0 := by
    intro i j hij hmod
    let t : Fin r := ⟨i.val % r, Nat.mod_lt i.val hr_pos⟩
    have hi : i ∈ fib t := by simp [fib, t]
    have hj : j ∈ (fib t).erase i := by
      simp [Finset.mem_erase, fib, t, hij.symm, hmod]
    have hdouble_eq : ∑ u ∈ fib t, ∑ v ∈ (fib t).erase u, (2 * s + 2 * ov u v) =
        ∑ u ∈ fib t, ∑ v ∈ (fib t).erase u, (wCol u + wCol v) := by
      have h1 : ∑ u ∈ fib t, ∑ v ∈ (fib t).erase u, (2 * s + 2 * ov u v) ≤
          ∑ u ∈ fib t, ∑ v ∈ (fib t).erase u, (wCol u + wCol v) := by
        apply Finset.sum_le_sum
        intro u hu
        apply Finset.sum_le_sum
        intro v hv
        exact hpair_le u v (Ne.symm (Finset.mem_erase.mp hv).1)
          (by rw [(Finset.mem_filter.mp hu).2, (Finset.mem_filter.mp (Finset.mem_erase.mp hv).2).2])
      have h2 : 2 * (q - 1) * (q * s) ≤ ∑ u ∈ fib t, ∑ v ∈ (fib t).erase u, (2 * s + 2 * ov u v) := by
        have hconst : 2 * (q - 1) * (q * s) = ∑ u ∈ fib t, ∑ _v ∈ (fib t).erase u, (2 * s) := by
          have : ∑ u ∈ fib t, ∑ _v ∈ (fib t).erase u, (2 * s) = ∑ _u ∈ fib t, (q - 1) * (2 * s) := by
            apply Finset.sum_congr rfl
            intro u hu
            rw [Finset.sum_const, Finset.card_erase_of_mem hu, hfib_card t, smul_eq_mul]
          rw [this, Finset.sum_const, hfib_card t, smul_eq_mul]
          ring
        rw [hconst]
        apply Finset.sum_le_sum
        intro u _
        apply Finset.sum_le_sum
        intro v _
        omega
      have h3 : ∑ u ∈ fib t, ∑ v ∈ (fib t).erase u, (wCol u + wCol v) = 2 * (q - 1) * (q * s) := by
        rw [sum_erase_add, hfib_card t, hfib_eq t]
      omega
    have hinner_eq : ∑ v ∈ (fib t).erase i, (2 * s + 2 * ov i v) =
        ∑ v ∈ (fib t).erase i, (wCol i + wCol v) := by
      refine (Finset.sum_eq_sum_iff_of_le ?_).mp hdouble_eq i hi
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      exact hpair_le u v (Ne.symm (Finset.mem_erase.mp hv).1)
        (by rw [(Finset.mem_filter.mp hu).2, (Finset.mem_filter.mp (Finset.mem_erase.mp hv).2).2])
    have hpt_eq : 2 * s + 2 * ov i j = wCol i + wCol j := by
      refine (Finset.sum_eq_sum_iff_of_le ?_).mp hinner_eq j hj
      intro v hv
      exact hpair_le i v (Ne.symm (Finset.mem_erase.mp hv).1)
        (by rw [(Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp (Finset.mem_erase.mp hv).2).2])
    have hov_sum0 : ∑ u ∈ fib t, ∑ v ∈ (fib t).erase u, ov u v = 0 := by
      have hd := hfib_double t
      rw [hfib_eq t] at hd
      omega
    have hov_inner0 : ∑ v ∈ (fib t).erase i, ov i v = 0 :=
      (Finset.sum_eq_zero_iff.mp hov_sum0) i hi
    have hov0 : ov i j = 0 :=
      (Finset.sum_eq_zero_iff.mp hov_inner0) j hj
    exact ⟨by omega, hov0⟩
  have hdisj_pt : ∀ x i j : I, i ≠ j → i.val % r = j.val % r → H x i ≠ F x i → H x j = F x j := by
    intro x i j hij hmod hxi
    have hov0 := (hpair_eq i j hij hmod).2
    have hmem : x ∉ Finset.univ.filter (fun x : I => H x i ≠ F x i ∧ H x j ≠ F x j) := by
      rw [Finset.card_eq_zero.mp hov0]
      simp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hmem
    by_contra hxj
    exact hmem hxi hxj
  have hwCol_eq : ∀ j : I, wCol j = s := by
    intro j
    have hr_lt_N : r < N := by nlinarith
    have h2r_lt_N : 2 * r < N := by nlinarith
    let j1 : I := ⟨(j.val + r) % N, Nat.mod_lt _ hN_pos⟩
    let j2 : I := ⟨(j.val + 2 * r) % N, Nat.mod_lt _ hN_pos⟩
    have hmod1 : j1.val % r = j.val % r := by
      simp only [j1]
      rw [Nat.mod_mod_of_dvd _ hdvd, Nat.add_mod_right]
    have hmod2 : j2.val % r = j.val % r := by
      simp only [j2]
      rw [Nat.mod_mod_of_dvd _ hdvd]
      have : j.val + 2 * r = j.val + r * 2 := by ring
      rw [this, Nat.add_mul_mod_self_left]
    have hne1 : j ≠ j1 := fun h => add_mod_ne_self j.isLt hr_pos hr_lt_N (congrArg Fin.val h).symm
    have hne2 : j ≠ j2 := fun h => add_mod_ne_self j.isLt (by omega) h2r_lt_N (congrArg Fin.val h).symm
    have hj2_from_j1 : j2.val = (j1.val + r) % N := by
      simp only [j1, j2]
      conv_rhs => rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      congr 1
      omega
    have hne12 : j1 ≠ j2 := by
      intro h
      have hval := congrArg Fin.val h
      rw [hj2_from_j1] at hval
      exact add_mod_ne_self j1.isLt hr_pos hr_lt_N hval.symm
    have he1 := (hpair_eq j j1 hne1 hmod1.symm).1
    have he2 := (hpair_eq j j2 hne2 hmod2.symm).1
    have he12 := (hpair_eq j1 j2 hne12 (by rw [hmod1, hmod2])).1
    omega
  have hs_le_r : s ≤ r := by
    let t0 : Fin r := ⟨0, hr_pos⟩
    let S : I → Finset I := fun j => Finset.univ.filter (fun x : I => H x j ≠ F x j)
    have hpw : Set.PairwiseDisjoint (↑(fib t0) : Set I) S := by
      intro i hi j hj hij
      change Disjoint (S i) (S j)
      rw [Finset.disjoint_left]
      intro x hxi hxj
      have hmod : i.val % r = j.val % r := by
        rw [(Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2]
      exact (Finset.mem_filter.mp hxj).2 (hdisj_pt x i j hij hmod (Finset.mem_filter.mp hxi).2)
    have hcard_bi : ((fib t0).biUnion S).card = q * s := by
      rw [Finset.card_biUnion hpw]
      have : ∑ j ∈ fib t0, (S j).card = ∑ _j ∈ fib t0, s :=
        Finset.sum_congr rfl (fun j _ => hwCol_eq j)
      rw [this, Finset.sum_const, hfib_card t0, smul_eq_mul]
    have hle_N : q * s ≤ q * r := by
      rw [← hcard_bi, hmul]
      calc ((fib t0).biUnion S).card ≤ (Finset.univ : Finset I).card :=
            Finset.card_le_card (Finset.subset_univ _)
        _ = N := by simp [I]
    exact Nat.le_of_mul_le_mul_left hle_N (by omega)
  exact ⟨hs_le_r, hwCol_eq, hdisj_pt⟩

end PEqualNP.Outside.L_meta_25854_aux

theorem PEqualNP.Outside.L_meta_25854 : (∀ k a : ℕ, (0 < a ∧ 2^a ≤ k ∧ 4 ≤ 2^k / 2^a) →
  let N := 2^k
  let r := 2^a
  let I := Fin N
  let F := fun x y : I => x.val.testBit (y.val % r)
  ∀ D : Finset ℕ, D ⊆ Finset.range r → 4*D.card ≤ N/r →
    let G := fun x y : I => xor (F x y) (decide (Nat.xor x.val y.val ∈ D))
    PEqualNP.Represents.HasLitSize (k+k) (PEqualNP.Represents.adjFun (k := k) (l := k) G)
      (8*k+12*r+12) ∧
    (∀ i : I, (Finset.univ.filter (fun j : I => G i j ≠ F i j)).card = D.card ∧
      (Finset.univ.filter (fun j : I => G j i ≠ F j i)).card = D.card) ∧
    (∀ f g : I → Bool,
      let T := fun x y : I => xor (G x y) (xor (f x) (g y))
      ∀ i j : I, i ≠ j →
        2*D.card ≤ (Finset.univ.filter (fun z : I => T i z ≠ T j z)).card ∧
        2*D.card ≤ (Finset.univ.filter (fun z : I => T z i ≠ T z j)).card) ∧
    ∀ (s : ℕ) (H : I → I → Bool),
      (∀ i j : I, i ≠ j → i.val % r = j.val % r →
        2*s ≤ (Finset.univ.filter (fun x : I => H x i ≠ H x j)).card) →
      let w := (Finset.univ.filter (fun z : I × I => H z.1 z.2 ≠ F z.1 z.2)).card
      N*s ≤ w ∧ (w = N*s →
        s ≤ r ∧ (∀ j : I, (Finset.univ.filter (fun x : I => H x j ≠ F x j)).card = s) ∧
        ∀ x i j : I, i ≠ j → i.val % r = j.val % r → H x i ≠ F x i → H x j = F x j)) := by
  intro k a ⟨ha, hak, hq4⟩ N r I F D hDsub hDcard G
  exact ⟨PEqualNP.Outside.L_meta_25854_aux.conj1_circuit k a ha hak D hDsub,
    PEqualNP.Outside.L_meta_25854_aux.conj2_edits k a hak D hDsub,
    PEqualNP.Outside.L_meta_25854_aux.conj3_distances k a ha hak D hDsub hDcard,
    PEqualNP.Outside.L_meta_25854_aux.conj4_lower_bound k a ha hak hq4⟩
