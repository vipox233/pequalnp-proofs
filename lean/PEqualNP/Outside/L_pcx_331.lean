import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_331_aux

abbrev BGate := PEqualNP.MetaComplexity.BinaryGate
abbrev BCircuit := PEqualNP.MetaComplexity.BinaryCircuit

def stepW (w : List Bool) (g : BGate) : List Bool :=
  w ++ [g.op (w.getD g.left false) (w.getD g.right false)]

def runW (G : List BGate) (src : List Bool) : List Bool :=
  (PEqualNP.MetaComplexity.BinaryCircuit.mk G 0).wires src

def evalW (G : List BGate) (src : List Bool) (u : ℕ) : Bool :=
  (runW G src).getD u false

def WF (N : ℕ) (G : List BGate) : Prop :=
  ∀ i : Fin G.length, (G.get i).left < N + i.val ∧ (G.get i).right < N + i.val

def Extends (G1 G2 : List BGate) : Prop :=
  ∃ d, G2 = G1 ++ d

def HasBase (src : List Bool) (N : ℕ) : Prop :=
  src.length = N ∧ src.getD 0 false = false ∧ src.getD 1 false = true

lemma hasBase_two_le {src : List Bool} {N : ℕ} (h : HasBase src N) : 2 ≤ N := by
  by_contra hlt
  have hlen : src.length = N := h.1
  have hle : src.length ≤ 1 := by omega
  have h1 : src.getD 1 false = false := by
    simp [List.getD, List.getElem?_eq_none hle]
  rw [h.2.2] at h1
  cases h1

lemma extends_rfl (G : List BGate) : Extends G G := ⟨[], by simp⟩

lemma extends_trans {A B C : List BGate} (h1 : Extends A B) (h2 : Extends B C) : Extends A C := by
  rcases h1 with ⟨d1, rfl⟩
  rcases h2 with ⟨d2, rfl⟩
  exact ⟨d1 ++ d2, by simp [List.append_assoc]⟩

lemma extends_len {A B : List BGate} (h : Extends A B) : A.length ≤ B.length := by
  rcases h with ⟨d, rfl⟩
  simp

lemma getD_append_left {α : Type} (l r : List α) (i : ℕ) (d : α) (h : i < l.length) :
    (l ++ r).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left h]

lemma getD_append_right {α : Type} (l r : List α) (i : ℕ) (d : α) (h : l.length ≤ i) :
    (l ++ r).getD i d = r.getD (i - l.length) d := by
  simp [List.getD, List.getElem?_append_right h]

lemma runW_eq_foldl (G : List BGate) (src : List Bool) :
    runW G src = G.foldl stepW src := rfl

lemma runW_append (G1 G2 : List BGate) (src : List Bool) :
    runW (G1 ++ G2) src = runW G2 (runW G1 src) := by
  simp [runW_eq_foldl, List.foldl_append]

lemma runW_len (G : List BGate) (src : List Bool) :
    (runW G src).length = src.length + G.length := by
  rw [runW_eq_foldl]
  induction G generalizing src with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons, ih, stepW, List.length_append, List.length_nil]
    omega

lemma runW_getD_lt (G : List BGate) (src : List Bool) (u : ℕ) (hu : u < src.length) :
    (runW G src).getD u false = src.getD u false := by
  rw [runW_eq_foldl]
  induction G generalizing src with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hu' : u < (stepW src g).length := by simp [stepW]; omega
    rw [ih (stepW src g) hu', stepW, getD_append_left _ _ _ _ hu]

lemma evalW_extends {G1 G2 : List BGate} {src : List Bool} {u : ℕ}
    (he : Extends G1 G2) (hu : u < src.length + G1.length) :
    evalW G2 src u = evalW G1 src u := by
  rcases he with ⟨d, rfl⟩
  simp only [evalW, runW_append]
  have hlen : u < (runW G1 src).length := by rw [runW_len]; exact hu
  exact runW_getD_lt d (runW G1 src) u hlen

lemma evalW_zero {G : List BGate} {src : List Bool} {N : ℕ} (hb : HasBase src N) :
    evalW G src 0 = false := by
  have h2 : 2 ≤ N := hasBase_two_le hb
  have hlen : src.length = N := hb.1
  have h := runW_getD_lt G src 0 (by omega)
  rw [evalW, h, hb.2.1]

lemma evalW_one {G : List BGate} {src : List Bool} {N : ℕ} (hb : HasBase src N) :
    evalW G src 1 = true := by
  have h2 : 2 ≤ N := hasBase_two_le hb
  have hlen : src.length = N := hb.1
  have h := runW_getD_lt G src 1 (by omega)
  rw [evalW, h, hb.2.2]

def emitGate (N : ℕ) (G : List BGate) (op : Bool → Bool → Bool) (l r : ℕ) :
    List BGate × ℕ :=
  (G ++ [⟨op, l, r⟩], N + G.length)

lemma emitGate_extends (N : ℕ) (G : List BGate) (op : Bool → Bool → Bool) (l r : ℕ) :
    Extends G (emitGate N G op l r).1 := ⟨[⟨op, l, r⟩], rfl⟩

lemma emitGate_len (N : ℕ) (G : List BGate) (op : Bool → Bool → Bool) (l r : ℕ) :
    (emitGate N G op l r).1.length = G.length + 1 := by
  simp [emitGate]

lemma emitGate_out_lt (N : ℕ) (G : List BGate) (op : Bool → Bool → Bool) (l r : ℕ) :
    (emitGate N G op l r).2 < N + (emitGate N G op l r).1.length := by
  simp [emitGate]

lemma emitGate_wf {N : ℕ} {G : List BGate} (op : Bool → Bool → Bool) {l r : ℕ}
    (hWF : WF N G) (hl : l < N + G.length) (hr : r < N + G.length) :
    WF N (emitGate N G op l r).1 := by
  intro i
  dsimp only [emitGate] at i ⊢
  by_cases hi : i.val < G.length
  · have hget : (G ++ [({ op := op, left := l, right := r } : BGate)]).get i = G.get ⟨i.val, hi⟩ := by
      simp [List.get_eq_getElem, List.getElem_append_left hi]
    rw [hget]
    exact hWF ⟨i.val, hi⟩
  · have hlen : (G ++ [({ op := op, left := l, right := r } : BGate)]).length = G.length + 1 := by simp
    have hiEq : i.val = G.length := by have := i.isLt; omega
    have hget : (G ++ [({ op := op, left := l, right := r } : BGate)]).get i =
        ({ op := op, left := l, right := r } : BGate) := by
      simp [List.get_eq_getElem, hiEq]
    rw [hget, hiEq]
    exact ⟨hl, hr⟩

lemma emitGate_eval {N : ℕ} {G : List BGate} {src : List Bool}
    (op : Bool → Bool → Bool) (l r : ℕ) (hlen : src.length = N) :
    evalW (emitGate N G op l r).1 src (emitGate N G op l r).2 =
      op (evalW G src l) (evalW G src r) := by
  simp only [emitGate, evalW]
  rw [runW_append]
  simp only [runW_eq_foldl, List.foldl_cons, List.foldl_nil, stepW]
  have hL : (runW G src).length = N + G.length := by rw [runW_len, hlen]
  rw [← runW_eq_foldl, getD_append_right _ _ _ _ (by omega)]
  simp [hL]

def buildMap {β T : Type} [DecidableEq β]
    (step : List BGate → β → List BGate × T)
    (d : T) (G : List BGate) : List β → List BGate × (β → T)
  | [] => (G, fun _ => d)
  | b :: bs =>
    let r1 := step G b
    let r2 := buildMap step d r1.1 bs
    (r2.1, fun x => if x = b then r1.2 else r2.2 x)

lemma buildMap_spec {β T : Type} [DecidableEq β] {N cost : ℕ}
    (step : List BGate → β → List BGate × T)
    (Valid : List BGate → T → Prop)
    (Spec : List BGate → β → T → Prop)
    (hVM : ∀ {G1 G2 t}, Extends G1 G2 → Valid G1 t → Valid G2 t)
    (hSM : ∀ {G1 G2 b t}, Extends G1 G2 → Valid G1 t → Spec G1 b t → Spec G2 b t)
    (d : T) (l : List β) (hl : l.Nodup) (G : List BGate) (hWF : WF N G)
    (hstep : ∀ G0 b, b ∈ l → Extends G G0 → WF N G0 →
      Extends G0 (step G0 b).1 ∧
      (step G0 b).1.length ≤ G0.length + cost ∧
      WF N (step G0 b).1 ∧
      Valid (step G0 b).1 (step G0 b).2 ∧
      Spec (step G0 b).1 b (step G0 b).2) :
    let res := buildMap step d G l
    Extends G res.1 ∧
    res.1.length ≤ G.length + cost * l.length ∧
    WF N res.1 ∧
    (∀ b ∈ l, Valid res.1 (res.2 b) ∧ Spec res.1 b (res.2 b)) := by
  induction l generalizing G with
  | nil =>
    exact ⟨extends_rfl G, by simp [buildMap], hWF, by intro b hb; simp at hb⟩
  | cons a bs ih =>
    have hnodup := List.nodup_cons.mp hl
    have hs := hstep G a (by simp) (extends_rfl G) hWF
    have hstep_bs : ∀ G0 b, b ∈ bs → Extends (step G a).1 G0 → WF N G0 →
        Extends G0 (step G0 b).1 ∧ (step G0 b).1.length ≤ G0.length + cost ∧
        WF N (step G0 b).1 ∧ Valid (step G0 b).1 (step G0 b).2 ∧ Spec (step G0 b).1 b (step G0 b).2 :=
      fun G0 b hb he0 => hstep G0 b (by simp [hb]) (extends_trans hs.1 he0)
    have hib := ih hnodup.2 (step G a).1 hs.2.2.1 hstep_bs
    refine ⟨extends_trans hs.1 hib.1, ?_, hib.2.2.1, ?_⟩
    · simp only [buildMap, List.length_cons]
      have h1 := hs.2.1
      have h2 := hib.2.1
      have hmul : cost * (bs.length + 1) = cost * bs.length + cost := Nat.mul_succ cost bs.length
      omega
    · intro b hb
      simp only [buildMap]
      by_cases hba : b = a
      · subst hba
        simp only [ite_true]
        exact ⟨hVM hib.1 hs.2.2.2.1, hSM hib.1 hs.2.2.2.1 hs.2.2.2.2⟩
      · have hbs : b ∈ bs := by
          rcases List.mem_cons.mp hb with rfl | hmem
          · exact absurd rfl hba
          · exact hmem
        simp only [hba, ite_false]
        exact hib.2.2.2 b hbs

def RegOK (N : ℕ) (G : List BGate) {B : ℕ} (r : Fin B → ℕ) : Prop :=
  ∀ i : Fin B, r i < N + G.length

lemma regOK_extends {N B : ℕ} {G1 G2 : List BGate} {r : Fin B → ℕ}
    (he : Extends G1 G2) (hr : RegOK N G1 r) : RegOK N G2 r := by
  intro i
  have := extends_len he
  have := hr i
  omega

def regVal {B : ℕ} (G : List BGate) (src : List Bool) (r : Fin B → ℕ) : ℕ :=
  ∑ i : Fin B, (evalW G src (r i)).toNat * 2 ^ i.val

lemma regVal_extends {N B : ℕ} {G1 G2 : List BGate} {src : List Bool} {r : Fin B → ℕ}
    (he : Extends G1 G2) (hlen : src.length = N) (hr : RegOK N G1 r) :
    regVal G2 src r = regVal G1 src r := by
  unfold regVal
  apply Finset.sum_congr rfl
  intro i _
  rw [evalW_extends he (by rw [hlen]; exact hr i)]

lemma sum_pow_two (B : ℕ) : (∑ i : Fin B, 2 ^ i.val) + 1 = 2 ^ B := by
  induction B with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.pow_succ]
    omega

lemma sum_range_pow_two (B : ℕ) : (∑ i ∈ Finset.range B, 2 ^ i) + 1 = 2 ^ B := by
  induction B with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.pow_succ]
    omega

lemma sum_range_bits_lt (f : ℕ → Bool) (B : ℕ) :
    (∑ i ∈ Finset.range B, (f i).toNat * 2 ^ i) < 2 ^ B := by
  have hle : ∑ i ∈ Finset.range B, (f i).toNat * 2 ^ i ≤ ∑ i ∈ Finset.range B, 2 ^ i := by
    apply Finset.sum_le_sum
    intro i _
    cases f i <;> simp
  have hs := sum_range_pow_two B
  omega

lemma regVal_lt {B : ℕ} (G : List BGate) (src : List Bool) (r : Fin B → ℕ) :
    regVal G src r < 2 ^ B := by
  unfold regVal
  have hle : ∑ i : Fin B, (evalW G src (r i)).toNat * 2 ^ i.val ≤ ∑ i : Fin B, 2 ^ i.val := by
    apply Finset.sum_le_sum
    intro i _
    cases evalW G src (r i) <;> simp
  have hs := sum_pow_two B
  omega

lemma testBit_sum_range (f : ℕ → Bool) (B k : ℕ) :
    (∑ i ∈ Finset.range B, (f i).toNat * 2 ^ i).testBit k =
      if k < B then f k else false := by
  induction B with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Nat.add_comm, Nat.mul_comm (f m).toNat (2 ^ m)]
    rw [Nat.testBit_two_pow_mul_add _ (sum_range_bits_lt f m)]
    by_cases hkm : k < m
    · have hks : k < m + 1 := by omega
      simp [hkm, hks, ih]
    · by_cases hkeq : k = m
      · subst hkeq
        simp only [lt_irrefl, ite_false, lt_add_iff_pos_right, zero_lt_one,
          ite_true, Nat.sub_self]
        cases f k <;> decide
      · have hkgt : ¬ k < m + 1 := by omega
        have hpos : 0 < k - m := by omega
        simp only [hkm, hkgt, ite_false]
        cases hfm : f m with
        | false => simp
        | true =>
          change (1 : ℕ).testBit (k - m) = false
          cases hsub : k - m with
          | zero => omega
          | succ t => simp [Nat.testBit_succ]

lemma sum_fin_eq_range {B : ℕ} (g : ℕ → ℕ) :
    (∑ i : Fin B, g i.val) = ∑ i ∈ Finset.range B, g i := by
  rw [Fin.sum_univ_eq_sum_range]

lemma regVal_testBit {B : ℕ} (G : List BGate) (src : List Bool) (r : Fin B → ℕ) (k : ℕ) :
    (regVal G src r).testBit k =
      if h : k < B then evalW G src (r ⟨k, h⟩) else false := by
  let f : ℕ → Bool := fun i => if h : i < B then evalW G src (r ⟨i, h⟩) else false
  have hEq : regVal G src r = ∑ i ∈ Finset.range B, (f i).toNat * 2 ^ i := by
    unfold regVal
    rw [← sum_fin_eq_range (fun i => (f i).toNat * 2 ^ i)]
    apply Finset.sum_congr rfl
    intro i _
    simp [f, i.isLt]
  rw [hEq, testBit_sum_range]
  by_cases hk : k < B
  · simp [f, hk]
  · simp [hk]

lemma regVal_testBit_fin {B : ℕ} (G : List BGate) (src : List Bool) (r : Fin B → ℕ) (k : Fin B) :
    (regVal G src r).testBit k.val = evalW G src (r k) := by
  rw [regVal_testBit]
  simp [k.isLt]

lemma regVal_eq_iff {B : ℕ} (G : List BGate) (src : List Bool) (r1 r2 : Fin B → ℕ) :
    regVal G src r1 = regVal G src r2 ↔ ∀ i : Fin B, evalW G src (r1 i) = evalW G src (r2 i) := by
  constructor
  · intro h i
    have ht := congrArg (fun x => x.testBit i.val) h
    simpa [regVal_testBit_fin] using ht
  · intro h
    apply Nat.eq_of_testBit_eq
    intro k
    rw [regVal_testBit, regVal_testBit]
    by_cases hk : k < B
    · simp [hk, h ⟨k, hk⟩]
    · simp [hk]

def constReg (B v : ℕ) : Fin B → ℕ :=
  fun i => if v.testBit i.val then 1 else 0

lemma constReg_ok {N B : ℕ} (hN : 2 ≤ N) (G : List BGate) (v : ℕ) :
    RegOK N G (constReg B v) := by
  intro i
  unfold constReg
  split <;> omega

lemma constReg_val {N B : ℕ} {G : List BGate} {src : List Bool} (hb : HasBase src N) (v : ℕ) :
    regVal G src (constReg B v) = v % 2 ^ B := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [regVal_testBit, Nat.testBit_mod_two_pow]
  by_cases hk : k < B
  · simp only [hk, dite_true, decide_true, Bool.true_and, constReg]
    cases hv : v.testBit k
    · simp [evalW_zero hb]
    · simp [evalW_one hb]
  · simp [hk]

lemma constReg_val_of_lt {N B : ℕ} {G : List BGate} {src : List Bool} (hb : HasBase src N)
    {v : ℕ} (hv : v < 2 ^ B) :
    regVal G src (constReg B v) = v := by
  rw [constReg_val hb, Nat.mod_eq_of_lt hv]

def shiftReg {B : ℕ} (t : ℕ) (r : Fin B → ℕ) : Fin B → ℕ :=
  fun i => if h : t ≤ i.val then r ⟨i.val - t, by omega⟩ else 0

lemma shiftReg_ok {N B : ℕ} {G : List BGate} {r : Fin B → ℕ}
    (hN : 2 ≤ N) (hr : RegOK N G r) (t : ℕ) : RegOK N G (shiftReg t r) := by
  intro i
  unfold shiftReg
  split
  · exact hr _
  · omega

lemma testBit_mul_two_pow (x t k : ℕ) :
    (x * 2 ^ t).testBit k = if t ≤ k then x.testBit (k - t) else false := by
  by_cases htk : t ≤ k
  · have hk : k = (k - t) + t := by omega
    conv_lhs => rw [hk]
    rw [Nat.testBit_add, Nat.mul_div_cancel _ (Nat.two_pow_pos t)]
    simp [htk]
  · simp only [htk, ite_false]
    have hlt : k < t := by omega
    rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
    have hdvd : 2 ^ (t - k) ∣ (x * 2 ^ t) / 2 ^ k := by
      have hpow : 2 ^ t = 2 ^ k * 2 ^ (t - k) := by rw [← Nat.pow_add]; congr 1; omega
      rw [hpow, ← Nat.mul_assoc, Nat.mul_comm x (2 ^ k), Nat.mul_assoc,
        Nat.mul_div_cancel_left _ (Nat.two_pow_pos k)]
      exact dvd_mul_left _ _
    have h2 : 2 ∣ 2 ^ (t - k) := by
      have hpos : 0 < t - k := by omega
      cases hsub : t - k with
      | zero => omega
      | succ m => rw [Nat.pow_succ]; exact dvd_mul_left 2 _
    have h2dvd : 2 ∣ (x * 2 ^ t) / 2 ^ k := dvd_trans h2 hdvd
    rcases h2dvd with ⟨q, hq⟩
    rw [hq]
    simp

lemma shiftReg_val {N B : ℕ} {G : List BGate} {src : List Bool}
    (hb : HasBase src N) (t : ℕ) (r : Fin B → ℕ) :
    regVal G src (shiftReg t r) = (regVal G src r * 2 ^ t) % 2 ^ B := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [regVal_testBit, Nat.testBit_mod_two_pow, testBit_mul_two_pow]
  by_cases hk : k < B
  · simp only [hk, dite_true, decide_true, Bool.true_and, shiftReg]
    by_cases htk : t ≤ k
    · simp only [htk, dite_true, ite_true]
      rw [← regVal_testBit_fin]
    · simp only [htk, dite_false, ite_false]
      exact evalW_zero hb
  · simp [hk]

def fullAdd (N : ℕ) (G : List BGate) (a b cin : ℕ) : List BGate × ℕ × ℕ :=
  let r1 := emitGate N G xor a b
  let r2 := emitGate N r1.1 xor r1.2 cin
  let r3 := emitGate N r2.1 and a b
  let r4 := emitGate N r3.1 and r1.2 cin
  let r5 := emitGate N r4.1 or r3.2 r4.2
  (r5.1, r2.2, r5.2)

lemma fullAdd_spec {N : ℕ} {G : List BGate} {a b cin : ℕ}
    (hWF : WF N G) (ha : a < N + G.length) (hb : b < N + G.length) (hc : cin < N + G.length) :
    let res := fullAdd N G a b cin
    Extends G res.1 ∧ res.1.length = G.length + 5 ∧ WF N res.1 ∧
    res.2.1 < N + res.1.length ∧ res.2.2 < N + res.1.length ∧
    ∀ src, src.length = N →
      (evalW res.1 src res.2.1).toNat + 2 * (evalW res.1 src res.2.2).toNat =
        (evalW G src a).toNat + (evalW G src b).toNat + (evalW G src cin).toNat := by
  dsimp only [fullAdd]
  set r1 := emitGate N G xor a b
  set r2 := emitGate N r1.1 xor r1.2 cin
  set r3 := emitGate N r2.1 and a b
  set r4 := emitGate N r3.1 and r1.2 cin
  set r5 := emitGate N r4.1 or r3.2 r4.2
  have he1 : Extends G r1.1 := emitGate_extends N G xor a b
  have he2 : Extends r1.1 r2.1 := emitGate_extends N r1.1 xor r1.2 cin
  have he3 : Extends r2.1 r3.1 := emitGate_extends N r2.1 and a b
  have he4 : Extends r3.1 r4.1 := emitGate_extends N r3.1 and r1.2 cin
  have he5 : Extends r4.1 r5.1 := emitGate_extends N r4.1 or r3.2 r4.2
  have hl1 : r1.1.length = G.length + 1 := emitGate_len N G xor a b
  have hl2 : r2.1.length = r1.1.length + 1 := emitGate_len N r1.1 xor r1.2 cin
  have hl3 : r3.1.length = r2.1.length + 1 := emitGate_len N r2.1 and a b
  have hl4 : r4.1.length = r3.1.length + 1 := emitGate_len N r3.1 and r1.2 cin
  have hl5 : r5.1.length = r4.1.length + 1 := emitGate_len N r4.1 or r3.2 r4.2
  have ho1 : r1.2 < N + r1.1.length := emitGate_out_lt N G xor a b
  have ho2 : r2.2 < N + r2.1.length := emitGate_out_lt N r1.1 xor r1.2 cin
  have ho3 : r3.2 < N + r3.1.length := emitGate_out_lt N r2.1 and a b
  have ho4 : r4.2 < N + r4.1.length := emitGate_out_lt N r3.1 and r1.2 cin
  have ho5 : r5.2 < N + r5.1.length := emitGate_out_lt N r4.1 or r3.2 r4.2
  have hw1 : WF N r1.1 := emitGate_wf xor hWF ha hb
  have hw2 : WF N r2.1 := emitGate_wf xor hw1 ho1 (by omega)
  have hw3 : WF N r3.1 := emitGate_wf and hw2 (by omega) (by omega)
  have hw4 : WF N r4.1 := emitGate_wf and hw3 (by omega) (by omega)
  have hw5 : WF N r5.1 := emitGate_wf or hw4 (by omega) ho4
  refine ⟨extends_trans he1 (extends_trans he2 (extends_trans he3 (extends_trans he4 he5))),
    by omega, hw5, by omega, ho5, ?_⟩
  intro src hsrc
  have e1 : evalW r1.1 src r1.2 = xor (evalW G src a) (evalW G src b) := emitGate_eval xor a b hsrc
  have e2 : evalW r2.1 src r2.2 = xor (evalW r1.1 src r1.2) (evalW r1.1 src cin) := emitGate_eval xor r1.2 cin hsrc
  have e3 : evalW r3.1 src r3.2 = (evalW r2.1 src a && evalW r2.1 src b) := emitGate_eval and a b hsrc
  have e4 : evalW r4.1 src r4.2 = (evalW r3.1 src r1.2 && evalW r3.1 src cin) := emitGate_eval and r1.2 cin hsrc
  have e5 : evalW r5.1 src r5.2 = (evalW r4.1 src r3.2 || evalW r4.1 src r4.2) := emitGate_eval or r3.2 r4.2 hsrc
  have s_r2 : evalW r5.1 src r2.2 = evalW r2.1 src r2.2 :=
    evalW_extends (extends_trans he3 (extends_trans he4 he5))
      (by rw [hsrc]; exact emitGate_out_lt N r1.1 xor r1.2 cin)
  have s_r3 : evalW r4.1 src r3.2 = evalW r3.1 src r3.2 :=
    evalW_extends he4 (by rw [hsrc]; exact emitGate_out_lt N r2.1 and a b)
  have s_cin1 : evalW r1.1 src cin = evalW G src cin :=
    evalW_extends he1 (by rw [hsrc]; exact hc)
  have s_a2 : evalW r2.1 src a = evalW G src a :=
    evalW_extends (extends_trans he1 he2) (by rw [hsrc]; exact ha)
  have s_b2 : evalW r2.1 src b = evalW G src b :=
    evalW_extends (extends_trans he1 he2) (by rw [hsrc]; exact hb)
  have s_r1_3 : evalW r3.1 src r1.2 = evalW r1.1 src r1.2 :=
    evalW_extends (extends_trans he2 he3) (by rw [hsrc]; exact emitGate_out_lt N G xor a b)
  have s_cin3 : evalW r3.1 src cin = evalW G src cin :=
    evalW_extends (extends_trans he1 (extends_trans he2 he3)) (by rw [hsrc]; exact hc)
  rw [s_r2, e2, e5, s_r3, e3, e4, s_cin1, s_a2, s_b2, s_r1_3, s_cin3, e1]
  cases evalW G src a <;> cases evalW G src b <;> cases evalW G src cin <;> decide

def fullSub (N : ℕ) (G : List BGate) (a b bin : ℕ) : List BGate × ℕ × ℕ :=
  let r1 := emitGate N G xor a b
  let r2 := emitGate N r1.1 xor r1.2 bin
  let r3 := emitGate N r2.1 (fun x y => !x && y) a b
  let r4 := emitGate N r3.1 (fun x y => !x && y) r1.2 bin
  let r5 := emitGate N r4.1 or r3.2 r4.2
  (r5.1, r2.2, r5.2)

lemma fullSub_spec {N : ℕ} {G : List BGate} {a b bin : ℕ}
    (hWF : WF N G) (ha : a < N + G.length) (hb : b < N + G.length) (hc : bin < N + G.length) :
    let res := fullSub N G a b bin
    Extends G res.1 ∧ res.1.length = G.length + 5 ∧ WF N res.1 ∧
    res.2.1 < N + res.1.length ∧ res.2.2 < N + res.1.length ∧
    ∀ src, src.length = N →
      (evalW G src a).toNat + 2 * (evalW res.1 src res.2.2).toNat =
        (evalW G src b).toNat + (evalW G src bin).toNat + (evalW res.1 src res.2.1).toNat := by
  dsimp only [fullSub]
  set opSub : Bool → Bool → Bool := fun x y => !x && y
  set r1 := emitGate N G xor a b
  set r2 := emitGate N r1.1 xor r1.2 bin
  set r3 := emitGate N r2.1 opSub a b
  set r4 := emitGate N r3.1 opSub r1.2 bin
  set r5 := emitGate N r4.1 or r3.2 r4.2
  have he1 : Extends G r1.1 := emitGate_extends N G xor a b
  have he2 : Extends r1.1 r2.1 := emitGate_extends N r1.1 xor r1.2 bin
  have he3 : Extends r2.1 r3.1 := emitGate_extends N r2.1 opSub a b
  have he4 : Extends r3.1 r4.1 := emitGate_extends N r3.1 opSub r1.2 bin
  have he5 : Extends r4.1 r5.1 := emitGate_extends N r4.1 or r3.2 r4.2
  have hl1 : r1.1.length = G.length + 1 := emitGate_len N G xor a b
  have hl2 : r2.1.length = r1.1.length + 1 := emitGate_len N r1.1 xor r1.2 bin
  have hl3 : r3.1.length = r2.1.length + 1 := emitGate_len N r2.1 opSub a b
  have hl4 : r4.1.length = r3.1.length + 1 := emitGate_len N r3.1 opSub r1.2 bin
  have hl5 : r5.1.length = r4.1.length + 1 := emitGate_len N r4.1 or r3.2 r4.2
  have ho1 : r1.2 < N + r1.1.length := emitGate_out_lt N G xor a b
  have ho2 : r2.2 < N + r2.1.length := emitGate_out_lt N r1.1 xor r1.2 bin
  have ho3 : r3.2 < N + r3.1.length := emitGate_out_lt N r2.1 opSub a b
  have ho4 : r4.2 < N + r4.1.length := emitGate_out_lt N r3.1 opSub r1.2 bin
  have ho5 : r5.2 < N + r5.1.length := emitGate_out_lt N r4.1 or r3.2 r4.2
  have hw1 : WF N r1.1 := emitGate_wf xor hWF ha hb
  have hw2 : WF N r2.1 := emitGate_wf xor hw1 ho1 (by omega)
  have hw3 : WF N r3.1 := emitGate_wf opSub hw2 (by omega) (by omega)
  have hw4 : WF N r4.1 := emitGate_wf opSub hw3 (by omega) (by omega)
  have hw5 : WF N r5.1 := emitGate_wf or hw4 (by omega) ho4
  refine ⟨extends_trans he1 (extends_trans he2 (extends_trans he3 (extends_trans he4 he5))),
    by omega, hw5, by omega, ho5, ?_⟩
  intro src hsrc
  have e1 : evalW r1.1 src r1.2 = xor (evalW G src a) (evalW G src b) := emitGate_eval xor a b hsrc
  have e2 : evalW r2.1 src r2.2 = xor (evalW r1.1 src r1.2) (evalW r1.1 src bin) := emitGate_eval xor r1.2 bin hsrc
  have e3 : evalW r3.1 src r3.2 = opSub (evalW r2.1 src a) (evalW r2.1 src b) := emitGate_eval opSub a b hsrc
  have e4 : evalW r4.1 src r4.2 = opSub (evalW r3.1 src r1.2) (evalW r3.1 src bin) := emitGate_eval opSub r1.2 bin hsrc
  have e5 : evalW r5.1 src r5.2 = (evalW r4.1 src r3.2 || evalW r4.1 src r4.2) := emitGate_eval or r3.2 r4.2 hsrc
  have s_r2 : evalW r5.1 src r2.2 = evalW r2.1 src r2.2 :=
    evalW_extends (extends_trans he3 (extends_trans he4 he5))
      (by rw [hsrc]; exact emitGate_out_lt N r1.1 xor r1.2 bin)
  have s_r3 : evalW r4.1 src r3.2 = evalW r3.1 src r3.2 :=
    evalW_extends he4 (by rw [hsrc]; exact emitGate_out_lt N r2.1 opSub a b)
  have s_bin1 : evalW r1.1 src bin = evalW G src bin :=
    evalW_extends he1 (by rw [hsrc]; exact hc)
  have s_a2 : evalW r2.1 src a = evalW G src a :=
    evalW_extends (extends_trans he1 he2) (by rw [hsrc]; exact ha)
  have s_b2 : evalW r2.1 src b = evalW G src b :=
    evalW_extends (extends_trans he1 he2) (by rw [hsrc]; exact hb)
  have s_r1_3 : evalW r3.1 src r1.2 = evalW r1.1 src r1.2 :=
    evalW_extends (extends_trans he2 he3) (by rw [hsrc]; exact emitGate_out_lt N G xor a b)
  have s_bin3 : evalW r3.1 src bin = evalW G src bin :=
    evalW_extends (extends_trans he1 (extends_trans he2 he3)) (by rw [hsrc]; exact hc)
  rw [s_r2, e2, e5, s_r3, e3, e4, s_bin1, s_a2, s_b2, s_r1_3, s_bin3, e1]
  cases evalW G src a <;> cases evalW G src b <;> cases evalW G src bin <;> decide

def bitMux (N : ℕ) (G : List BGate) (s a b : ℕ) : List BGate × ℕ :=
  let r1 := emitGate N G and s a
  let r2 := emitGate N r1.1 (fun x y => !x && y) s b
  let r3 := emitGate N r2.1 or r1.2 r2.2
  (r3.1, r3.2)

lemma bitMux_spec {N : ℕ} {G : List BGate} {s a b : ℕ}
    (hWF : WF N G) (hs : s < N + G.length) (ha : a < N + G.length) (hb : b < N + G.length) :
    let res := bitMux N G s a b
    Extends G res.1 ∧ res.1.length = G.length + 3 ∧ WF N res.1 ∧
    res.2 < N + res.1.length ∧
    ∀ src, src.length = N →
      evalW res.1 src res.2 = if evalW G src s then evalW G src a else evalW G src b := by
  dsimp only [bitMux]
  set opNB : Bool → Bool → Bool := fun x y => !x && y
  set r1 := emitGate N G and s a
  set r2 := emitGate N r1.1 opNB s b
  set r3 := emitGate N r2.1 or r1.2 r2.2
  have he1 : Extends G r1.1 := emitGate_extends N G and s a
  have he2 : Extends r1.1 r2.1 := emitGate_extends N r1.1 opNB s b
  have he3 : Extends r2.1 r3.1 := emitGate_extends N r2.1 or r1.2 r2.2
  have hl1 : r1.1.length = G.length + 1 := emitGate_len N G and s a
  have hl2 : r2.1.length = r1.1.length + 1 := emitGate_len N r1.1 opNB s b
  have hl3 : r3.1.length = r2.1.length + 1 := emitGate_len N r2.1 or r1.2 r2.2
  have ho1 : r1.2 < N + r1.1.length := emitGate_out_lt N G and s a
  have ho2 : r2.2 < N + r2.1.length := emitGate_out_lt N r1.1 opNB s b
  have ho3 : r3.2 < N + r3.1.length := emitGate_out_lt N r2.1 or r1.2 r2.2
  have hw1 : WF N r1.1 := emitGate_wf and hWF hs ha
  have hw2 : WF N r2.1 := emitGate_wf opNB hw1 (l := s) (r := b) (by omega) (by omega)
  have hw3 : WF N r3.1 := emitGate_wf or hw2 (l := r1.2) (r := r2.2) (by omega) ho2
  refine ⟨extends_trans he1 (extends_trans he2 he3), by omega, hw3, ho3, ?_⟩
  intro src hsrc
  have e1 := emitGate_eval (G := G) and s a hsrc
  have e2 := emitGate_eval (G := r1.1) opNB s b hsrc
  have e3 := emitGate_eval (G := r2.1) or r1.2 r2.2 hsrc
  have s_r1 : evalW r2.1 src r1.2 = evalW r1.1 src r1.2 :=
    evalW_extends he2 (by rw [hsrc]; exact emitGate_out_lt N G and s a)
  have s_s : evalW r1.1 src s = evalW G src s := evalW_extends he1 (by rw [hsrc]; exact hs)
  have s_b : evalW r1.1 src b = evalW G src b := evalW_extends he1 (by rw [hsrc]; exact hb)
  rw [e3, s_r1, e1, e2, s_s, s_b]
  cases evalW G src s <;> cases evalW G src a <;> cases evalW G src b <;> decide

def regAddAux (N : ℕ) (G : List BGate) (a b : ℕ → ℕ) : ℕ → List BGate × (ℕ → ℕ) × ℕ
  | 0 => (G, fun _ => 0, 0)
  | k + 1 =>
    let r1 := regAddAux N G a b k
    let fa := fullAdd N r1.1 (a k) (b k) r1.2.2
    (fa.1, fun i => if i = k then fa.2.1 else r1.2.1 i, fa.2.2)

lemma regAddAux_spec {N : ℕ} (hN : 2 ≤ N) {G : List BGate} {a b : ℕ → ℕ} (k : ℕ)
    (hWF : WF N G) (ha : ∀ i < k, a i < N + G.length) (hb : ∀ i < k, b i < N + G.length) :
    let res := regAddAux N G a b k
    Extends G res.1 ∧ res.1.length = G.length + 5 * k ∧ WF N res.1 ∧
    (∀ i < k, res.2.1 i < N + res.1.length) ∧ res.2.2 < N + res.1.length ∧
    ∀ src, HasBase src N →
      (∑ i ∈ Finset.range k, (evalW res.1 src (res.2.1 i)).toNat * 2 ^ i) +
          (evalW res.1 src res.2.2).toNat * 2 ^ k =
        (∑ i ∈ Finset.range k, (evalW G src (a i)).toNat * 2 ^ i) +
          (∑ i ∈ Finset.range k, (evalW G src (b i)).toNat * 2 ^ i) := by
  induction k with
  | zero =>
    refine ⟨extends_rfl G, by simp [regAddAux], hWF, by intro i hi; omega, by simp [regAddAux]; omega, ?_⟩
    intro src hbase
    simp [regAddAux, evalW_zero hbase]
  | succ m ih =>
    have hm := ih (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega))
    dsimp only [regAddAux]
    set r1 := regAddAux N G a b m
    have he1 := hm.1
    have hl1 := hm.2.1
    have hw1 := hm.2.2.1
    have hout1 := hm.2.2.2.1
    have hc1 := hm.2.2.2.2.1
    have hev1 := hm.2.2.2.2.2
    have ham : a m < N + r1.1.length := by have := ha m (by omega); omega
    have hbm : b m < N + r1.1.length := by have := hb m (by omega); omega
    have hfa := fullAdd_spec hw1 ham hbm hc1
    set fa := fullAdd N r1.1 (a m) (b m) r1.2.2
    refine ⟨extends_trans he1 hfa.1, by omega, hfa.2.2.1, ?_, hfa.2.2.2.2.1, ?_⟩
    · intro i hi
      by_cases him : i = m
      · subst him; simp only [ite_true]; exact hfa.2.2.2.1
      · simp only [him, ite_false]
        have := hout1 i (by omega)
        have := extends_len hfa.1
        omega
    · intro src hbase
      have hsum :
          ∑ i ∈ Finset.range m, (evalW fa.1 src (if i = m then fa.2.1 else r1.2.1 i)).toNat * 2 ^ i =
            ∑ i ∈ Finset.range m, (evalW r1.1 src (r1.2.1 i)).toNat * 2 ^ i := by
        apply Finset.sum_congr rfl
        intro i hi
        have hne : i ≠ m := by simp only [Finset.mem_range] at hi; omega
        simp only [hne, ite_false]
        rw [evalW_extends hfa.1 (by rw [hbase.1]; exact hout1 i (Finset.mem_range.mp hi))]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, hsum]
      simp only [ite_true]
      have hbit := hfa.2.2.2.2.2 src hbase.1
      have ha_eq : evalW r1.1 src (a m) = evalW G src (a m) :=
        evalW_extends he1 (by rw [hbase.1]; exact ha m (by omega))
      have hb_eq : evalW r1.1 src (b m) = evalW G src (b m) :=
        evalW_extends he1 (by rw [hbase.1]; exact hb m (by omega))
      rw [ha_eq, hb_eq] at hbit
      have hih := hev1 src hbase
      have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [hpow]
      have hbitM : (evalW fa.1 src fa.2.1).toNat * 2 ^ m +
          (evalW fa.1 src fa.2.2).toNat * (2 * 2 ^ m) =
          (evalW G src (a m)).toNat * 2 ^ m + (evalW G src (b m)).toNat * 2 ^ m +
          (evalW r1.1 src r1.2.2).toNat * 2 ^ m := by
        have := congrArg (· * 2 ^ m) hbit
        ring_nf at this ⊢
        omega
      omega

def regAdd (N : ℕ) (G : List BGate) {B : ℕ} (a b : Fin B → ℕ) :
    List BGate × (Fin B → ℕ) × ℕ :=
  let res := regAddAux N G (fun i => if h : i < B then a ⟨i, h⟩ else 0)
    (fun i => if h : i < B then b ⟨i, h⟩ else 0) B
  (res.1, fun i : Fin B => res.2.1 i.val, res.2.2)

lemma regAdd_spec {N B : ℕ} (hN : 2 ≤ N) {G : List BGate} {a b : Fin B → ℕ}
    (hWF : WF N G) (ha : RegOK N G a) (hb : RegOK N G b) :
    let res := regAdd N G a b
    Extends G res.1 ∧ res.1.length = G.length + 5 * B ∧ WF N res.1 ∧
    RegOK N res.1 res.2.1 ∧ res.2.2 < N + res.1.length ∧
    ∀ src, HasBase src N →
      regVal res.1 src res.2.1 + (evalW res.1 src res.2.2).toNat * 2 ^ B =
        regVal G src a + regVal G src b := by
  have h := regAddAux_spec hN B hWF
    (a := fun i => if h : i < B then a ⟨i, h⟩ else 0)
    (b := fun i => if h : i < B then b ⟨i, h⟩ else 0)
    (fun i hi => by simp [hi, ha ⟨i, hi⟩])
    (fun i hi => by simp [hi, hb ⟨i, hi⟩])
  refine ⟨h.1, h.2.1, h.2.2.1, fun i => h.2.2.2.1 i.val i.isLt, h.2.2.2.2.1, ?_⟩
  intro src hbase
  have hev := h.2.2.2.2.2 src hbase
  have h1 : regVal (regAdd N G a b).1 src (regAdd N G a b).2.1 =
      ∑ i ∈ Finset.range B, (evalW (regAdd N G a b).1 src ((regAddAux N G
        (fun i => if h : i < B then a ⟨i, h⟩ else 0)
        (fun i => if h : i < B then b ⟨i, h⟩ else 0) B).2.1 i)).toNat * 2 ^ i := by
    simp only [regVal, regAdd]
    exact Fin.sum_univ_eq_sum_range (fun i =>
      (evalW (regAddAux N G (fun i => if h : i < B then a ⟨i, h⟩ else 0)
        (fun i => if h : i < B then b ⟨i, h⟩ else 0) B).1 src
        ((regAddAux N G (fun i => if h : i < B then a ⟨i, h⟩ else 0)
        (fun i => if h : i < B then b ⟨i, h⟩ else 0) B).2.1 i)).toNat * 2 ^ i) B
  have h2 : regVal G src a = ∑ i ∈ Finset.range B,
      (evalW G src (if h : i < B then a ⟨i, h⟩ else 0)).toNat * 2 ^ i := by
    unfold regVal
    rw [← sum_fin_eq_range]
    apply Finset.sum_congr rfl
    intro i _
    simp [i.isLt]
  have h3 : regVal G src b = ∑ i ∈ Finset.range B,
      (evalW G src (if h : i < B then b ⟨i, h⟩ else 0)).toNat * 2 ^ i := by
    unfold regVal
    rw [← sum_fin_eq_range]
    apply Finset.sum_congr rfl
    intro i _
    simp [i.isLt]
  rw [h1, h2, h3]
  exact hev

lemma regAdd_val_of_lt {N B : ℕ} (hN : 2 ≤ N) {G : List BGate} {src : List Bool} {a b : Fin B → ℕ}
    (hWF : WF N G) (ha : RegOK N G a) (hb : RegOK N G b) (hbase : HasBase src N)
    (hlt : regVal G src a + regVal G src b < 2 ^ B) :
    regVal (regAdd N G a b).1 src (regAdd N G a b).2.1 = regVal G src a + regVal G src b := by
  have hev := (regAdd_spec hN hWF ha hb).2.2.2.2.2 src hbase
  cases hc : evalW (regAdd N G a b).1 src (regAdd N G a b).2.2
  · simp [hc] at hev; omega
  · simp [hc] at hev; omega

def regSubAux (N : ℕ) (G : List BGate) (a b : ℕ → ℕ) : ℕ → List BGate × (ℕ → ℕ) × ℕ
  | 0 => (G, fun _ => 0, 0)
  | k + 1 =>
    let r1 := regSubAux N G a b k
    let fs := fullSub N r1.1 (a k) (b k) r1.2.2
    (fs.1, fun i => if i = k then fs.2.1 else r1.2.1 i, fs.2.2)

lemma regSubAux_spec {N : ℕ} (hN : 2 ≤ N) {G : List BGate} {a b : ℕ → ℕ} (k : ℕ)
    (hWF : WF N G) (ha : ∀ i < k, a i < N + G.length) (hb : ∀ i < k, b i < N + G.length) :
    let res := regSubAux N G a b k
    Extends G res.1 ∧ res.1.length = G.length + 5 * k ∧ WF N res.1 ∧
    (∀ i < k, res.2.1 i < N + res.1.length) ∧ res.2.2 < N + res.1.length ∧
    ∀ src, HasBase src N →
      (∑ i ∈ Finset.range k, (evalW G src (a i)).toNat * 2 ^ i) +
          (evalW res.1 src res.2.2).toNat * 2 ^ k =
        (∑ i ∈ Finset.range k, (evalW G src (b i)).toNat * 2 ^ i) +
          (∑ i ∈ Finset.range k, (evalW res.1 src (res.2.1 i)).toNat * 2 ^ i) := by
  induction k with
  | zero =>
    refine ⟨extends_rfl G, by simp [regSubAux], hWF, by intro i hi; omega, by simp [regSubAux]; omega, ?_⟩
    intro src hbase
    simp [regSubAux, evalW_zero hbase]
  | succ m ih =>
    have hm := ih (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega))
    dsimp only [regSubAux]
    set r1 := regSubAux N G a b m
    have he1 := hm.1
    have hl1 := hm.2.1
    have hw1 := hm.2.2.1
    have hout1 := hm.2.2.2.1
    have hc1 := hm.2.2.2.2.1
    have hev1 := hm.2.2.2.2.2
    have ham : a m < N + r1.1.length := by have := ha m (by omega); omega
    have hbm : b m < N + r1.1.length := by have := hb m (by omega); omega
    have hfs := fullSub_spec hw1 ham hbm hc1
    set fs := fullSub N r1.1 (a m) (b m) r1.2.2
    refine ⟨extends_trans he1 hfs.1, by omega, hfs.2.2.1, ?_, hfs.2.2.2.2.1, ?_⟩
    · intro i hi
      by_cases him : i = m
      · subst him; simp only [ite_true]; exact hfs.2.2.2.1
      · simp only [him, ite_false]
        have := hout1 i (by omega)
        have := extends_len hfs.1
        omega
    · intro src hbase
      have hsum :
          ∑ i ∈ Finset.range m, (evalW fs.1 src (if i = m then fs.2.1 else r1.2.1 i)).toNat * 2 ^ i =
            ∑ i ∈ Finset.range m, (evalW r1.1 src (r1.2.1 i)).toNat * 2 ^ i := by
        apply Finset.sum_congr rfl
        intro i hi
        have hne : i ≠ m := by simp only [Finset.mem_range] at hi; omega
        simp only [hne, ite_false]
        rw [evalW_extends hfs.1 (by rw [hbase.1]; exact hout1 i (Finset.mem_range.mp hi))]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, hsum]
      simp only [ite_true]
      have hbit := hfs.2.2.2.2.2 src hbase.1
      have ha_eq : evalW r1.1 src (a m) = evalW G src (a m) :=
        evalW_extends he1 (by rw [hbase.1]; exact ha m (by omega))
      have hb_eq : evalW r1.1 src (b m) = evalW G src (b m) :=
        evalW_extends he1 (by rw [hbase.1]; exact hb m (by omega))
      rw [ha_eq, hb_eq] at hbit
      have hih := hev1 src hbase
      have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [hpow]
      have hbitM : (evalW G src (a m)).toNat * 2 ^ m +
          (evalW fs.1 src fs.2.2).toNat * (2 * 2 ^ m) =
          (evalW G src (b m)).toNat * 2 ^ m + (evalW r1.1 src r1.2.2).toNat * 2 ^ m +
          (evalW fs.1 src fs.2.1).toNat * 2 ^ m := by
        have := congrArg (· * 2 ^ m) hbit
        ring_nf at this ⊢
        omega
      omega

def regSub (N : ℕ) (G : List BGate) {B : ℕ} (a b : Fin B → ℕ) :
    List BGate × (Fin B → ℕ) × ℕ :=
  let res := regSubAux N G (fun i => if h : i < B then a ⟨i, h⟩ else 0)
    (fun i => if h : i < B then b ⟨i, h⟩ else 0) B
  (res.1, fun i : Fin B => res.2.1 i.val, res.2.2)

lemma regSub_spec {N B : ℕ} (hN : 2 ≤ N) {G : List BGate} {a b : Fin B → ℕ}
    (hWF : WF N G) (ha : RegOK N G a) (hb : RegOK N G b) :
    let res := regSub N G a b
    Extends G res.1 ∧ res.1.length = G.length + 5 * B ∧ WF N res.1 ∧
    RegOK N res.1 res.2.1 ∧ res.2.2 < N + res.1.length ∧
    ∀ src, HasBase src N →
      regVal G src a + (evalW res.1 src res.2.2).toNat * 2 ^ B =
        regVal G src b + regVal res.1 src res.2.1 := by
  have h := regSubAux_spec hN B hWF
    (a := fun i => if h : i < B then a ⟨i, h⟩ else 0)
    (b := fun i => if h : i < B then b ⟨i, h⟩ else 0)
    (fun i hi => by simp [hi, ha ⟨i, hi⟩])
    (fun i hi => by simp [hi, hb ⟨i, hi⟩])
  refine ⟨h.1, h.2.1, h.2.2.1, fun i => h.2.2.2.1 i.val i.isLt, h.2.2.2.2.1, ?_⟩
  intro src hbase
  have hev := h.2.2.2.2.2 src hbase
  have h1 : regVal (regSub N G a b).1 src (regSub N G a b).2.1 =
      ∑ i ∈ Finset.range B, (evalW (regSub N G a b).1 src ((regSubAux N G
        (fun i => if h : i < B then a ⟨i, h⟩ else 0)
        (fun i => if h : i < B then b ⟨i, h⟩ else 0) B).2.1 i)).toNat * 2 ^ i := by
    simp only [regVal, regSub]
    exact Fin.sum_univ_eq_sum_range (fun i =>
      (evalW (regSubAux N G (fun i => if h : i < B then a ⟨i, h⟩ else 0)
        (fun i => if h : i < B then b ⟨i, h⟩ else 0) B).1 src
        ((regSubAux N G (fun i => if h : i < B then a ⟨i, h⟩ else 0)
        (fun i => if h : i < B then b ⟨i, h⟩ else 0) B).2.1 i)).toNat * 2 ^ i) B
  have h2 : regVal G src a = ∑ i ∈ Finset.range B,
      (evalW G src (if h : i < B then a ⟨i, h⟩ else 0)).toNat * 2 ^ i := by
    unfold regVal
    rw [← sum_fin_eq_range]
    apply Finset.sum_congr rfl
    intro i _
    simp [i.isLt]
  have h3 : regVal G src b = ∑ i ∈ Finset.range B,
      (evalW G src (if h : i < B then b ⟨i, h⟩ else 0)).toNat * 2 ^ i := by
    unfold regVal
    rw [← sum_fin_eq_range]
    apply Finset.sum_congr rfl
    intro i _
    simp [i.isLt]
  rw [h1, h2, h3]
  exact hev

lemma regSub_borrow_iff {N B : ℕ} (hN : 2 ≤ N) {G : List BGate} {src : List Bool} {a b : Fin B → ℕ}
    (hWF : WF N G) (ha : RegOK N G a) (hb : RegOK N G b) (hbase : HasBase src N) :
    evalW (regSub N G a b).1 src (regSub N G a b).2.2 = true ↔
      regVal G src a < regVal G src b := by
  have hev := (regSub_spec hN hWF ha hb).2.2.2.2.2 src hbase
  have ha_lt := regVal_lt G src a
  have hb_lt := regVal_lt G src b
  have hd_lt := regVal_lt (regSub N G a b).1 src (regSub N G a b).2.1
  cases hbor : evalW (regSub N G a b).1 src (regSub N G a b).2.2
  · simp [hbor] at hev ⊢; omega
  · simp [hbor] at hev ⊢; omega

lemma regSub_val_of_le {N B : ℕ} (hN : 2 ≤ N) {G : List BGate} {src : List Bool} {a b : Fin B → ℕ}
    (hWF : WF N G) (ha : RegOK N G a) (hb : RegOK N G b) (hbase : HasBase src N)
    (hle : regVal G src b ≤ regVal G src a) :
    regVal (regSub N G a b).1 src (regSub N G a b).2.1 = regVal G src a - regVal G src b := by
  have hev := (regSub_spec hN hWF ha hb).2.2.2.2.2 src hbase
  have hbor := regSub_borrow_iff hN hWF ha hb hbase
  have hf : evalW (regSub N G a b).1 src (regSub N G a b).2.2 = false := by
    cases hb' : evalW (regSub N G a b).1 src (regSub N G a b).2.2
    · rfl
    · have := hbor.mp hb'; omega
  rw [hf] at hev
  simp at hev
  omega

def regGateAux (N : ℕ) (G : List BGate) (cond : ℕ) (a : ℕ → ℕ) : ℕ → List BGate × (ℕ → ℕ)
  | 0 => (G, fun _ => 0)
  | k + 1 =>
    let r1 := regGateAux N G cond a k
    let r2 := emitGate N r1.1 and cond (a k)
    (r2.1, fun i => if i = k then r2.2 else r1.2 i)

lemma regGateAux_spec {N : ℕ} {G : List BGate} {cond : ℕ} {a : ℕ → ℕ} (k : ℕ)
    (hWF : WF N G) (hc : cond < N + G.length) (ha : ∀ i < k, a i < N + G.length) :
    let res := regGateAux N G cond a k
    Extends G res.1 ∧ res.1.length = G.length + k ∧ WF N res.1 ∧
    (∀ i < k, res.2 i < N + res.1.length) ∧
    ∀ src, src.length = N → ∀ i < k,
      evalW res.1 src (res.2 i) = (evalW G src cond && evalW G src (a i)) := by
  induction k with
  | zero =>
    exact ⟨extends_rfl G, by simp [regGateAux], hWF, by intro i hi; omega, by intro src _ i hi; omega⟩
  | succ m ih =>
    have hm := ih (fun i hi => ha i (by omega))
    dsimp only [regGateAux]
    set r1 := regGateAux N G cond a m
    have he1 := hm.1
    have hl1 := hm.2.1
    have hw1 := hm.2.2.1
    have hout1 := hm.2.2.2.1
    have hev1 := hm.2.2.2.2
    have hcm : cond < N + r1.1.length := by omega
    have ham : a m < N + r1.1.length := by have := ha m (by omega); omega
    set r2 := emitGate N r1.1 and cond (a m)
    have he2 : Extends r1.1 r2.1 := emitGate_extends N r1.1 and cond (a m)
    have hl2 : r2.1.length = r1.1.length + 1 := emitGate_len N r1.1 and cond (a m)
    have ho2 : r2.2 < N + r2.1.length := emitGate_out_lt N r1.1 and cond (a m)
    have hw2 : WF N r2.1 := emitGate_wf and hw1 hcm ham
    refine ⟨extends_trans he1 he2, by omega, hw2, ?_, ?_⟩
    · intro i hi
      by_cases him : i = m
      · subst him; simp only [ite_true]; exact ho2
      · simp only [him, ite_false]; have := hout1 i (by omega); omega
    · intro src hsrc i hi
      by_cases him : i = m
      · subst him
        simp only [ite_true]
        rw [emitGate_eval and cond (a i) hsrc]
        rw [evalW_extends he1 (by rw [hsrc]; exact hc)]
        rw [evalW_extends he1 (by rw [hsrc]; exact ha i (by omega))]
      · simp only [him, ite_false]
        rw [evalW_extends he2 (by rw [hsrc]; exact hout1 i (by omega))]
        exact hev1 src hsrc i (by omega)

def regGate (N : ℕ) (G : List BGate) (cond : ℕ) {B : ℕ} (a : Fin B → ℕ) :
    List BGate × (Fin B → ℕ) :=
  let res := regGateAux N G cond (fun i => if h : i < B then a ⟨i, h⟩ else 0) B
  (res.1, fun i : Fin B => res.2 i.val)

lemma regGate_spec {N B : ℕ} {G : List BGate} {cond : ℕ} {a : Fin B → ℕ}
    (hWF : WF N G) (hc : cond < N + G.length) (ha : RegOK N G a) :
    let res := regGate N G cond a
    Extends G res.1 ∧ res.1.length = G.length + B ∧ WF N res.1 ∧
    RegOK N res.1 res.2 ∧
    ∀ src, src.length = N →
      regVal res.1 src res.2 = if evalW G src cond then regVal G src a else 0 := by
  have h := regGateAux_spec B hWF hc
    (a := fun i => if h : i < B then a ⟨i, h⟩ else 0)
    (fun i hi => by simp [hi, ha ⟨i, hi⟩])
  refine ⟨h.1, h.2.1, h.2.2.1, fun i => h.2.2.2.1 i.val i.isLt, ?_⟩
  intro src hsrc
  unfold regVal regGate
  cases hcv : evalW G src cond
  · simp only [Bool.false_eq_true, ite_false]
    apply Finset.sum_eq_zero
    intro i _
    have hb := h.2.2.2.2 src hsrc i.val i.isLt
    simp [i.isLt, hcv] at hb
    simp [hb]
  · simp only [ite_true]
    apply Finset.sum_congr rfl
    intro i _
    have hb := h.2.2.2.2 src hsrc i.val i.isLt
    simp [i.isLt, hcv] at hb
    simp [hb]

def regMuxAux (N : ℕ) (G : List BGate) (s : ℕ) (a b : ℕ → ℕ) : ℕ → List BGate × (ℕ → ℕ)
  | 0 => (G, fun _ => 0)
  | k + 1 =>
    let r1 := regMuxAux N G s a b k
    let r2 := bitMux N r1.1 s (a k) (b k)
    (r2.1, fun i => if i = k then r2.2 else r1.2 i)

lemma regMuxAux_spec {N : ℕ} {G : List BGate} {s : ℕ} {a b : ℕ → ℕ} (k : ℕ)
    (hWF : WF N G) (hs : s < N + G.length)
    (ha : ∀ i < k, a i < N + G.length) (hb : ∀ i < k, b i < N + G.length) :
    let res := regMuxAux N G s a b k
    Extends G res.1 ∧ res.1.length = G.length + 3 * k ∧ WF N res.1 ∧
    (∀ i < k, res.2 i < N + res.1.length) ∧
    ∀ src, src.length = N → ∀ i < k,
      evalW res.1 src (res.2 i) = if evalW G src s then evalW G src (a i) else evalW G src (b i) := by
  induction k with
  | zero =>
    exact ⟨extends_rfl G, by simp [regMuxAux], hWF, by intro i hi; omega, by intro src _ i hi; omega⟩
  | succ m ih =>
    have hm := ih (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega))
    dsimp only [regMuxAux]
    set r1 := regMuxAux N G s a b m
    have he1 := hm.1
    have hl1 := hm.2.1
    have hw1 := hm.2.2.1
    have hout1 := hm.2.2.2.1
    have hev1 := hm.2.2.2.2
    have hsm : s < N + r1.1.length := by omega
    have ham : a m < N + r1.1.length := by have := ha m (by omega); omega
    have hbm : b m < N + r1.1.length := by have := hb m (by omega); omega
    have hbmux := bitMux_spec hw1 hsm ham hbm
    set r2 := bitMux N r1.1 s (a m) (b m)
    refine ⟨extends_trans he1 hbmux.1, by omega, hbmux.2.2.1, ?_, ?_⟩
    · intro i hi
      by_cases him : i = m
      · subst him; simp only [ite_true]; exact hbmux.2.2.2.1
      · simp only [him, ite_false]; have := hout1 i (by omega); have := extends_len hbmux.1; omega
    · intro src hsrc i hi
      by_cases him : i = m
      · subst him
        simp only [ite_true]
        rw [hbmux.2.2.2.2 src hsrc]
        rw [evalW_extends he1 (by rw [hsrc]; exact hs)]
        rw [evalW_extends he1 (by rw [hsrc]; exact ha i (by omega))]
        rw [evalW_extends he1 (by rw [hsrc]; exact hb i (by omega))]
      · simp only [him, ite_false]
        rw [evalW_extends hbmux.1 (by rw [hsrc]; exact hout1 i (by omega))]
        exact hev1 src hsrc i (by omega)

def regMux (N : ℕ) (G : List BGate) (s : ℕ) {B : ℕ} (a b : Fin B → ℕ) :
    List BGate × (Fin B → ℕ) :=
  let res := regMuxAux N G s (fun i => if h : i < B then a ⟨i, h⟩ else 0)
    (fun i => if h : i < B then b ⟨i, h⟩ else 0) B
  (res.1, fun i : Fin B => res.2 i.val)

lemma regMux_spec {N B : ℕ} {G : List BGate} {s : ℕ} {a b : Fin B → ℕ}
    (hWF : WF N G) (hs : s < N + G.length) (ha : RegOK N G a) (hb : RegOK N G b) :
    let res := regMux N G s a b
    Extends G res.1 ∧ res.1.length = G.length + 3 * B ∧ WF N res.1 ∧
    RegOK N res.1 res.2 ∧
    ∀ src, src.length = N →
      regVal res.1 src res.2 = if evalW G src s then regVal G src a else regVal G src b := by
  have h := regMuxAux_spec B hWF hs
    (a := fun i => if h : i < B then a ⟨i, h⟩ else 0)
    (b := fun i => if h : i < B then b ⟨i, h⟩ else 0)
    (fun i hi => by simp [hi, ha ⟨i, hi⟩])
    (fun i hi => by simp [hi, hb ⟨i, hi⟩])
  refine ⟨h.1, h.2.1, h.2.2.1, fun i => h.2.2.2.1 i.val i.isLt, ?_⟩
  intro src hsrc
  unfold regVal regMux
  cases hsv : evalW G src s
  · simp only [Bool.false_eq_true, ite_false]
    apply Finset.sum_congr rfl
    intro i _
    have hb' := h.2.2.2.2 src hsrc i.val i.isLt
    simp [i.isLt, hsv] at hb'
    simp [hb']
  · simp only [ite_true]
    apply Finset.sum_congr rfl
    intro i _
    have hb' := h.2.2.2.2 src hsrc i.val i.isLt
    simp [i.isLt, hsv] at hb'
    simp [hb']

def regEqAux (N : ℕ) (G : List BGate) (a b : ℕ → ℕ) : ℕ → List BGate × ℕ
  | 0 => (G, 1)
  | k + 1 =>
    let r1 := regEqAux N G a b k
    let r2 := emitGate N r1.1 (fun x y => x == y) (a k) (b k)
    let r3 := emitGate N r2.1 and r1.2 r2.2
    (r3.1, r3.2)

lemma regEqAux_spec {N : ℕ} (hN : 2 ≤ N) {G : List BGate} {a b : ℕ → ℕ} (k : ℕ)
    (hWF : WF N G) (ha : ∀ i < k, a i < N + G.length) (hb : ∀ i < k, b i < N + G.length) :
    let res := regEqAux N G a b k
    Extends G res.1 ∧ res.1.length = G.length + 2 * k ∧ WF N res.1 ∧
    res.2 < N + res.1.length ∧
    ∀ src, HasBase src N →
      (evalW res.1 src res.2 = true ↔ ∀ i < k, evalW G src (a i) = evalW G src (b i)) := by
  induction k with
  | zero =>
    refine ⟨extends_rfl G, by simp [regEqAux], hWF, by simp [regEqAux]; omega, ?_⟩
    intro src hbase
    simp [regEqAux, evalW_one hbase]
  | succ m ih =>
    have hm := ih (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega))
    dsimp only [regEqAux]
    set opEq : Bool → Bool → Bool := fun x y => x == y
    set r1 := regEqAux N G a b m
    have he1 := hm.1
    have hl1 := hm.2.1
    have hw1 := hm.2.2.1
    have hout1 := hm.2.2.2.1
    have hev1 := hm.2.2.2.2
    set r2 := emitGate N r1.1 opEq (a m) (b m)
    set r3 := emitGate N r2.1 and r1.2 r2.2
    have he2 : Extends r1.1 r2.1 := emitGate_extends N r1.1 opEq (a m) (b m)
    have he3 : Extends r2.1 r3.1 := emitGate_extends N r2.1 and r1.2 r2.2
    have hl2 : r2.1.length = r1.1.length + 1 := emitGate_len N r1.1 opEq (a m) (b m)
    have hl3 : r3.1.length = r2.1.length + 1 := emitGate_len N r2.1 and r1.2 r2.2
    have ho2 : r2.2 < N + r2.1.length := emitGate_out_lt N r1.1 opEq (a m) (b m)
    have ho3 : r3.2 < N + r3.1.length := emitGate_out_lt N r2.1 and r1.2 r2.2
    have hw2 : WF N r2.1 := emitGate_wf opEq hw1 (l := a m) (r := b m)
      (by have := ha m (by omega); omega) (by have := hb m (by omega); omega)
    have hw3 : WF N r3.1 := emitGate_wf and hw2 (l := r1.2) (r := r2.2) (by omega) ho2
    refine ⟨extends_trans he1 (extends_trans he2 he3), by omega, hw3, ho3, ?_⟩
    intro src hbase
    rw [emitGate_eval and r1.2 r2.2 hbase.1]
    rw [evalW_extends he2 (by rw [hbase.1]; exact hout1)]
    rw [emitGate_eval opEq (a m) (b m) hbase.1]
    have ham_eq : evalW r1.1 src (a m) = evalW G src (a m) :=
      evalW_extends he1 (by rw [hbase.1]; exact ha m (by omega))
    have hbm_eq : evalW r1.1 src (b m) = evalW G src (b m) :=
      evalW_extends he1 (by rw [hbase.1]; exact hb m (by omega))
    rw [ham_eq, hbm_eq, Bool.and_eq_true, hev1 src hbase]
    simp only [opEq, beq_iff_eq]
    constructor
    · intro ⟨hprev, hm'⟩ i hi
      by_cases him : i = m
      · subst him; exact hm'
      · exact hprev i (by omega)
    · intro hall
      exact ⟨fun i hi => hall i (by omega), hall m (by omega)⟩

def regEq (N : ℕ) (G : List BGate) {B : ℕ} (a b : Fin B → ℕ) : List BGate × ℕ :=
  regEqAux N G (fun i => if h : i < B then a ⟨i, h⟩ else 0)
    (fun i => if h : i < B then b ⟨i, h⟩ else 0) B

lemma regEq_spec {N B : ℕ} (hN : 2 ≤ N) {G : List BGate} {a b : Fin B → ℕ}
    (hWF : WF N G) (ha : RegOK N G a) (hb : RegOK N G b) :
    let res := regEq N G a b
    Extends G res.1 ∧ res.1.length = G.length + 2 * B ∧ WF N res.1 ∧
    res.2 < N + res.1.length ∧
    ∀ src, HasBase src N → (evalW res.1 src res.2 = true ↔ regVal G src a = regVal G src b) := by
  have h := regEqAux_spec hN B hWF
    (a := fun i => if h : i < B then a ⟨i, h⟩ else 0)
    (b := fun i => if h : i < B then b ⟨i, h⟩ else 0)
    (fun i hi => by simp [hi, ha ⟨i, hi⟩])
    (fun i hi => by simp [hi, hb ⟨i, hi⟩])
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  intro src hbase
  simp only [regEq]
  rw [h.2.2.2.2 src hbase, regVal_eq_iff]
  constructor
  · intro hall i; simpa [i.isLt] using hall i.val i.isLt
  · intro hall i hi; simpa [hi] using hall ⟨i, hi⟩

def regNzAux (N : ℕ) (G : List BGate) (a : ℕ → ℕ) : ℕ → List BGate × ℕ
  | 0 => (G, 0)
  | k + 1 =>
    let r1 := regNzAux N G a k
    let r2 := emitGate N r1.1 or r1.2 (a k)
    (r2.1, r2.2)

lemma regNzAux_spec {N : ℕ} (hN : 2 ≤ N) {G : List BGate} {a : ℕ → ℕ} (k : ℕ)
    (hWF : WF N G) (ha : ∀ i < k, a i < N + G.length) :
    let res := regNzAux N G a k
    Extends G res.1 ∧ res.1.length = G.length + k ∧ WF N res.1 ∧
    res.2 < N + res.1.length ∧
    ∀ src, HasBase src N →
      (evalW res.1 src res.2 = true ↔ ∃ i < k, evalW G src (a i) = true) := by
  induction k with
  | zero =>
    refine ⟨extends_rfl G, by simp [regNzAux], hWF, by simp [regNzAux]; omega, ?_⟩
    intro src hbase
    simp [regNzAux, evalW_zero hbase]
  | succ m ih =>
    have hm := ih (fun i hi => ha i (by omega))
    dsimp only [regNzAux]
    set r1 := regNzAux N G a m
    have he1 := hm.1
    have hl1 := hm.2.1
    have hw1 := hm.2.2.1
    have hout1 := hm.2.2.2.1
    have hev1 := hm.2.2.2.2
    set r2 := emitGate N r1.1 or r1.2 (a m)
    have he2 : Extends r1.1 r2.1 := emitGate_extends N r1.1 or r1.2 (a m)
    have hl2 : r2.1.length = r1.1.length + 1 := emitGate_len N r1.1 or r1.2 (a m)
    have ho2 : r2.2 < N + r2.1.length := emitGate_out_lt N r1.1 or r1.2 (a m)
    have hw2 : WF N r2.1 := emitGate_wf or hw1 (l := r1.2) (r := a m) hout1 (by have := ha m (by omega); omega)
    refine ⟨extends_trans he1 he2, by omega, hw2, ho2, ?_⟩
    intro src hbase
    rw [emitGate_eval or r1.2 (a m) hbase.1]
    have ham_eq : evalW r1.1 src (a m) = evalW G src (a m) :=
      evalW_extends he1 (by rw [hbase.1]; exact ha m (by omega))
    rw [ham_eq, Bool.or_eq_true, hev1 src hbase]
    constructor
    · rintro (⟨i, hi, hv⟩ | hv)
      · exact ⟨i, by omega, hv⟩
      · exact ⟨m, by omega, hv⟩
    · rintro ⟨i, hi, hv⟩
      by_cases him : i = m
      · subst him; exact Or.inr hv
      · exact Or.inl ⟨i, by omega, hv⟩

def regNz (N : ℕ) (G : List BGate) {B : ℕ} (a : Fin B → ℕ) : List BGate × ℕ :=
  regNzAux N G (fun i => if h : i < B then a ⟨i, h⟩ else 0) B

lemma regNz_spec {N B : ℕ} (hN : 2 ≤ N) {G : List BGate} {a : Fin B → ℕ}
    (hWF : WF N G) (ha : RegOK N G a) :
    let res := regNz N G a
    Extends G res.1 ∧ res.1.length = G.length + B ∧ WF N res.1 ∧
    res.2 < N + res.1.length ∧
    ∀ src, HasBase src N → (evalW res.1 src res.2 = true ↔ regVal G src a ≠ 0) := by
  have h := regNzAux_spec hN B hWF
    (a := fun i => if h : i < B then a ⟨i, h⟩ else 0)
    (fun i hi => by simp [hi, ha ⟨i, hi⟩])
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  intro src hbase
  simp only [regNz]
  rw [h.2.2.2.2 src hbase]
  constructor
  · rintro ⟨i, hi, hv⟩ hzero
    simp only [hi, dite_true] at hv
    have ht := congrArg (fun x => x.testBit i) hzero
    rw [regVal_testBit] at ht
    simp [hi, hv] at ht
  · intro hne
    by_contra hall
    push Not at hall
    apply hne
    apply Nat.eq_of_testBit_eq
    intro k
    rw [regVal_testBit]
    simp only [Nat.zero_testBit]
    by_cases hk : k < B
    · simp only [hk, dite_true]
      have hnot := hall k hk
      simp only [hk, dite_true] at hnot
      cases hval : evalW G src (a ⟨k, hk⟩)
      · rfl
      · exact absurd hval hnot
    · simp [hk]

def regMulConst (N : ℕ) (G : List BGate) {B : ℕ} (K : ℕ) (r : Fin B → ℕ) :
    ℕ → List BGate × (Fin B → ℕ)
  | 0 => (G, constReg B 0)
  | k + 1 =>
    let r1 := regMulConst N G K r k
    if K.testBit k then
      let r2 := regAdd N r1.1 r1.2 (shiftReg k r)
      (r2.1, r2.2.1)
    else
      r1

lemma mod_two_pow_succ_eq (K k : ℕ) :
    K % 2 ^ (k + 1) = K % 2 ^ k + (K.testBit k).toNat * 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow, Nat.add_comm (K % 2 ^ k), Nat.mul_comm (K.testBit k).toNat (2 ^ k)]
  rw [Nat.testBit_two_pow_mul_add _ (Nat.mod_lt K (Nat.two_pow_pos k))]
  by_cases hjk : j < k
  · have hjs : j < k + 1 := by omega
    simp [hjk, hjs, Nat.testBit_mod_two_pow]
  · by_cases hjeq : j = k
    · subst hjeq
      simp only [lt_irrefl, ite_false, Nat.lt_succ_self, decide_true, Bool.true_and, Nat.sub_self]
      cases K.testBit j <;> decide
    · have hjgt : ¬ j < k + 1 := by omega
      simp only [hjk, hjgt, decide_false, Bool.false_and, ite_false]
      cases hbit : K.testBit k with
      | false => simp
      | true =>
        change false = (1 : ℕ).testBit (j - k)
        cases hsub : j - k with
        | zero => omega
        | succ t => simp [Nat.testBit_succ]

lemma regMulConst_spec {N B : ℕ} (hN : 2 ≤ N) {G : List BGate} (K : ℕ) {r : Fin B → ℕ} (k : ℕ)
    (hWF : WF N G) (hr : RegOK N G r) :
    let res := regMulConst N G K r k
    Extends G res.1 ∧ res.1.length ≤ G.length + 5 * B * k ∧ WF N res.1 ∧
    RegOK N res.1 res.2 ∧
    ∀ src, HasBase src N → (K % 2 ^ k) * regVal G src r < 2 ^ B →
      regVal res.1 src res.2 = (K % 2 ^ k) * regVal G src r := by
  induction k with
  | zero =>
    refine ⟨extends_rfl G, by simp [regMulConst], hWF, constReg_ok hN G 0, ?_⟩
    intro src hbase _
    simp [regMulConst, constReg_val hbase, Nat.mod_one]
  | succ m ih =>
    dsimp only [regMulConst]
    set r1 := regMulConst N G K r m
    have he1 := ih.1
    have hl1 := ih.2.1
    have hw1 := ih.2.2.1
    have hok1 := ih.2.2.2.1
    have hev1 := ih.2.2.2.2
    have hmod := mod_two_pow_succ_eq K m
    by_cases hbit : K.testBit m = true
    · simp only [hbit, ite_true]
      have hrok1 : RegOK N r1.1 r := regOK_extends he1 hr
      have hshok : RegOK N r1.1 (shiftReg m r) := shiftReg_ok hN hrok1 m
      have hadd := regAdd_spec hN hw1 hok1 hshok
      refine ⟨extends_trans he1 hadd.1, ?_, hadd.2.2.1, hadd.2.2.2.1, ?_⟩
      · have h1 := hadd.2.1
        have hmul : 5 * B * (m + 1) = 5 * B * m + 5 * B := Nat.mul_succ (5 * B) m
        omega
      · intro src hbase hlt
        rw [hbit] at hmod
        simp only [Bool.toNat_true, one_mul] at hmod
        have hle1 : K % 2 ^ m ≤ K % 2 ^ (m + 1) := by omega
        have hlt1 : (K % 2 ^ m) * regVal G src r < 2 ^ B :=
          lt_of_le_of_lt (Nat.mul_le_mul_right _ hle1) hlt
        have hv1 := hev1 src hbase hlt1
        have hrv1 : regVal r1.1 src r = regVal G src r := regVal_extends he1 hbase.1 hr
        have hlt2 : regVal G src r * 2 ^ m < 2 ^ B := by
          have h2le : 2 ^ m ≤ K % 2 ^ (m + 1) := by omega
          calc regVal G src r * 2 ^ m = 2 ^ m * regVal G src r := Nat.mul_comm _ _
            _ ≤ (K % 2 ^ (m + 1)) * regVal G src r := Nat.mul_le_mul_right _ h2le
            _ < 2 ^ B := hlt
        have hshv : regVal r1.1 src (shiftReg m r) = regVal G src r * 2 ^ m := by
          rw [shiftReg_val hbase, hrv1, Nat.mod_eq_of_lt hlt2]
        have hsum_eq : regVal r1.1 src r1.2 + regVal r1.1 src (shiftReg m r) =
            (K % 2 ^ (m + 1)) * regVal G src r := by
          rw [hv1, hshv, hmod, Nat.add_mul, Nat.mul_comm (2 ^ m)]
        have hsum_lt : regVal r1.1 src r1.2 + regVal r1.1 src (shiftReg m r) < 2 ^ B := by
          rw [hsum_eq]; exact hlt
        rw [regAdd_val_of_lt hN hw1 hok1 hshok hbase hsum_lt, hsum_eq]
    · have hbf : K.testBit m = false := Bool.eq_false_iff.mpr hbit
      simp only [hbf, Bool.false_eq_true, ite_false]
      rw [hbf] at hmod
      simp only [Bool.toNat_false, zero_mul, Nat.add_zero] at hmod
      refine ⟨he1, ?_, hw1, hok1, ?_⟩
      · have hmul : 5 * B * (m + 1) = 5 * B * m + 5 * B := Nat.mul_succ (5 * B) m
        omega
      · intro src hbase hlt
        rw [hmod] at hlt ⊢
        exact hev1 src hbase hlt

def regDivConst (N : ℕ) (G : List BGate) {B : ℕ} (d : ℕ) :
    (m : ℕ) → (Fin B → ℕ) → List BGate × (Fin m → ℕ)
  | 0, _ => (G, Fin.elim0)
  | m + 1, r =>
    let C := d * 2 ^ m
    let rs := regSub N G r (constReg B C)
    let rn := emitGate N rs.1 (fun x _ => !x) rs.2.2 0
    let rm := regMux N rn.1 rn.2 rs.2.1 r
    let rd := regDivConst N rm.1 d m rm.2
    (rd.1, fun i : Fin (m + 1) => if h : i.val < m then rd.2 ⟨i.val, h⟩ else rn.2)

lemma regDivConst_spec {N B : ℕ} (hN : 2 ≤ N) (d : ℕ) (hd : 0 < d) :
    ∀ (m : ℕ) (G : List BGate) (r : Fin B → ℕ),
      WF N G → RegOK N G r → d * 2 ^ m ≤ 2 ^ B →
      let res := regDivConst N G d m r
      Extends G res.1 ∧ res.1.length ≤ G.length + m * (8 * B + 1) ∧ WF N res.1 ∧
      RegOK N res.1 res.2 ∧
      ∀ src, HasBase src N → regVal G src r < d * 2 ^ m →
        regVal res.1 src res.2 = regVal G src r / d := by
  intro m
  induction m with
  | zero =>
    intro G r hWF _ _
    refine ⟨extends_rfl G, by simp [regDivConst], hWF, fun i => Fin.elim0 i, ?_⟩
    intro src _ hlt
    simp only [Nat.pow_zero, Nat.mul_one] at hlt
    rw [Nat.div_eq_of_lt hlt]
    simp [regDivConst, regVal]
  | succ k ih =>
    intro G r hWF hr hdB
    dsimp only [regDivConst]
    set C := d * 2 ^ k
    have hCB : C < 2 ^ B := by
      have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
      have hpos : 0 < C := Nat.mul_pos hd (Nat.two_pow_pos k)
      have h2C : 2 * C ≤ 2 ^ B := by
        calc 2 * C = d * (2 * 2 ^ k) := by simp only [C]; ring
          _ = d * 2 ^ (k + 1) := by rw [← hpow]
          _ ≤ 2 ^ B := hdB
      omega
    have hcok := constReg_ok hN G C (B := B)
    have hsub := regSub_spec hN hWF hr hcok
    set rs := regSub N G r (constReg B C)
    set opNot : Bool → Bool → Bool := fun x _ => !x
    set rn := emitGate N rs.1 opNot rs.2.2 0
    have hen : Extends rs.1 rn.1 := emitGate_extends N rs.1 opNot rs.2.2 0
    have hln : rn.1.length = rs.1.length + 1 := emitGate_len N rs.1 opNot rs.2.2 0
    have hon : rn.2 < N + rn.1.length := emitGate_out_lt N rs.1 opNot rs.2.2 0
    have hwn : WF N rn.1 := emitGate_wf opNot hsub.2.2.1 (l := rs.2.2) (r := 0) hsub.2.2.2.2.1 (by omega)
    have hok_diff : RegOK N rn.1 rs.2.1 := regOK_extends hen hsub.2.2.2.1
    have hok_r : RegOK N rn.1 r := regOK_extends (extends_trans hsub.1 hen) hr
    have hmux := regMux_spec hwn hon hok_diff hok_r
    set rm := regMux N rn.1 rn.2 rs.2.1 r
    have hdBk : d * 2 ^ k ≤ 2 ^ B := le_of_lt hCB
    have hrd := ih rm.1 rm.2 hmux.2.2.1 hmux.2.2.2.1 hdBk
    set rd := regDivConst N rm.1 d k rm.2
    have he_all : Extends G rd.1 :=
      extends_trans hsub.1 (extends_trans hen (extends_trans hmux.1 hrd.1))
    refine ⟨he_all, ?_, hrd.2.2.1, ?_, ?_⟩
    · have h1 := hsub.2.1
      have h2 := hmux.2.1
      have h3 := hrd.2.1
      have hmul : (k + 1) * (8 * B + 1) = k * (8 * B + 1) + (8 * B + 1) := Nat.succ_mul k _
      omega
    · intro i
      by_cases hi : i.val < k
      · simp only [hi, dite_true]; exact hrd.2.2.2.1 ⟨i.val, hi⟩
      · simp only [hi, dite_false]
        have := extends_len (extends_trans hmux.1 hrd.1)
        omega
    · intro src hbase hlt
      have hcv : regVal G src (constReg B C) = C := constReg_val_of_lt hbase hCB
      have hbor := regSub_borrow_iff hN hWF hr hcok hbase
      rw [hcv] at hbor
      have hqbit : evalW rn.1 src rn.2 = decide (C ≤ regVal G src r) := by
        rw [emitGate_eval opNot rs.2.2 0 hbase.1]
        simp only [opNot]
        cases hb' : evalW rs.1 src rs.2.2
        · have hnotlt : ¬ regVal G src r < C := by
            intro hlt'; have := hbor.mpr hlt'; rw [hb'] at this; cases this
          have hge : C ≤ regVal G src r := Nat.le_of_not_lt hnotlt
          simp [hge]
        · have hlt' : regVal G src r < C := hbor.mp hb'
          have hnotge : ¬ C ≤ regVal G src r := Nat.not_le.mpr hlt'
          simp [hnotge]
      have hqbit_rd : evalW rd.1 src rn.2 = decide (C ≤ regVal G src r) := by
        rw [evalW_extends (extends_trans hmux.1 hrd.1)
          (by rw [hbase.1]; exact emitGate_out_lt N rs.1 opNot rs.2.2 0), hqbit]
      have hrm_val : regVal rm.1 src rm.2 =
          if C ≤ regVal G src r then regVal G src r - C else regVal G src r := by
        rw [hmux.2.2.2.2 src hbase.1, hqbit]
        rw [regVal_extends (extends_trans hsub.1 hen) hbase.1 hr]
        rw [regVal_extends hen hbase.1 hsub.2.2.2.1]
        by_cases hge : C ≤ regVal G src r
        · simp only [hge, decide_true, ite_true]
          have hdiff := regSub_val_of_le hN hWF hr hcok hbase (by rw [hcv]; exact hge)
          rw [hcv] at hdiff
          exact hdiff
        · simp [hge]
      have hrm_lt : regVal rm.1 src rm.2 < d * 2 ^ k := by
        rw [hrm_val]
        have hpow : d * 2 ^ (k + 1) = C + C := by
          simp only [C, Nat.pow_succ]; ring
        split <;> omega
      have hlo_val : regVal rd.1 src rd.2 = regVal rm.1 src rm.2 / d :=
        hrd.2.2.2.2 src hbase hrm_lt
      unfold regVal
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, Fin.isLt, dite_true, lt_irrefl, dite_false]
      have hsum_lo :
          ∑ x : Fin k, (evalW rd.1 src (rd.2 ⟨x.val, x.isLt⟩)).toNat * 2 ^ x.val =
            regVal rd.1 src rd.2 := rfl
      rw [hsum_lo, hlo_val, hrm_val, hqbit_rd]
      by_cases hge : C ≤ regVal G src r
      · simp only [hge, ite_true, decide_true, Bool.toNat_true, one_mul]
        have hdiv : (regVal G src r - C) / d + 2 ^ k = regVal G src r / d := by
          have heq : regVal G src r = (regVal G src r - C) + d * 2 ^ k := by omega
          conv_rhs => rw [heq]
          rw [Nat.add_mul_div_left _ _ hd]
        exact hdiv
      · simp only [hge, ite_false, decide_false, Bool.toNat_false, zero_mul, Nat.add_zero]
        rfl

def sumRegs {α : Type} (N B : ℕ) (G : List BGate) (f : α → Fin B → ℕ) :
    List α → List BGate × (Fin B → ℕ)
  | [] => (G, constReg B 0)
  | a :: rest =>
    let r1 := sumRegs N B G f rest
    let r2 := regAdd N r1.1 r1.2 (f a)
    (r2.1, r2.2.1)

lemma sumRegs_spec {α : Type} {N B : ℕ} (hN : 2 ≤ N) {G : List BGate} {f : α → Fin B → ℕ}
    (l : List α) (hWF : WF N G) (hf : ∀ a ∈ l, RegOK N G (f a)) :
    let res := sumRegs N B G f l
    Extends G res.1 ∧ res.1.length ≤ G.length + 5 * B * l.length ∧ WF N res.1 ∧
    RegOK N res.1 res.2 ∧
    ∀ src, HasBase src N → (l.map (fun a => regVal G src (f a))).sum < 2 ^ B →
      regVal res.1 src res.2 = (l.map (fun a => regVal G src (f a))).sum := by
  induction l with
  | nil =>
    refine ⟨extends_rfl G, by simp [sumRegs], hWF, constReg_ok hN G 0, ?_⟩
    intro src hbase _
    simp [sumRegs, constReg_val hbase]
  | cons a rest ih =>
    have hrest := ih (fun b hb => hf b (by simp [hb]))
    dsimp only [sumRegs]
    set r1 := sumRegs N B G f rest
    have ha_ok : RegOK N r1.1 (f a) := regOK_extends hrest.1 (hf a (by simp))
    have hadd := regAdd_spec hN hrest.2.2.1 hrest.2.2.2.1 ha_ok
    refine ⟨extends_trans hrest.1 hadd.1, ?_, hadd.2.2.1, hadd.2.2.2.1, ?_⟩
    · have h1 := hrest.2.1
      have h2 := hadd.2.1
      have hmul : 5 * B * (rest.length + 1) = 5 * B * rest.length + 5 * B := Nat.mul_succ (5 * B) _
      simp only [List.length_cons]
      omega
    · intro src hbase hlt
      simp only [List.map_cons, List.sum_cons] at hlt ⊢
      have hlt_rest : (rest.map (fun x => regVal G src (f x))).sum < 2 ^ B := by omega
      have hv1 := hrest.2.2.2.2 src hbase hlt_rest
      have hva : regVal r1.1 src (f a) = regVal G src (f a) :=
        regVal_extends hrest.1 hbase.1 (hf a (by simp))
      have hsum_lt : regVal r1.1 src r1.2 + regVal r1.1 src (f a) < 2 ^ B := by
        rw [hv1, hva]; omega
      rw [regAdd_val_of_lt hN hrest.2.2.1 hrest.2.2.2.1 ha_ok hbase hsum_lt, hv1, hva, Nat.add_comm]

lemma list_map_toList_sum {α : Type} [Fintype α] (f : α → ℕ) :
    ((Finset.univ : Finset α).toList.map f).sum = ∑ a : α, f a := by
  rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
  rfl

def andList (N : ℕ) (G : List BGate) (init : ℕ) : List ℕ → List BGate × ℕ
  | [] => (G, init)
  | w :: ws =>
    let r1 := andList N G init ws
    let r2 := emitGate N r1.1 and r1.2 w
    (r2.1, r2.2)

lemma andList_spec {N : ℕ} {G : List BGate} {init : ℕ} (l : List ℕ)
    (hWF : WF N G) (hi : init < N + G.length) (hl : ∀ w ∈ l, w < N + G.length) :
    let res := andList N G init l
    Extends G res.1 ∧ res.1.length = G.length + l.length ∧ WF N res.1 ∧
    res.2 < N + res.1.length ∧
    ∀ src, src.length = N →
      (evalW res.1 src res.2 = true ↔
        evalW G src init = true ∧ ∀ w ∈ l, evalW G src w = true) := by
  induction l with
  | nil =>
    exact ⟨extends_rfl G, by simp [andList], hWF, hi, by intro src _; simp [andList]⟩
  | cons w ws ih =>
    have hws := ih (fun u hu => hl u (by simp [hu]))
    dsimp only [andList]
    set r1 := andList N G init ws
    have he1 := hws.1
    have hlen1 := hws.2.1
    have hw1 := hws.2.2.1
    have ho1 := hws.2.2.2.1
    have hev1 := hws.2.2.2.2
    have hwlt : w < N + r1.1.length := by have := hl w (by simp); omega
    set r2 := emitGate N r1.1 and r1.2 w
    have he2 : Extends r1.1 r2.1 := emitGate_extends N r1.1 and r1.2 w
    have hlen2 : r2.1.length = r1.1.length + 1 := emitGate_len N r1.1 and r1.2 w
    have ho2 : r2.2 < N + r2.1.length := emitGate_out_lt N r1.1 and r1.2 w
    have hw2 : WF N r2.1 := emitGate_wf and hw1 (l := r1.2) (r := w) ho1 hwlt
    refine ⟨extends_trans he1 he2, by simp only [List.length_cons]; omega, hw2, ho2, ?_⟩
    intro src hsrc
    rw [emitGate_eval and r1.2 w hsrc]
    have hw_eq : evalW r1.1 src w = evalW G src w :=
      evalW_extends he1 (by rw [hsrc]; exact hl w (by simp))
    rw [hw_eq, Bool.and_eq_true, hev1 src hsrc]
    constructor
    · rintro ⟨⟨hinit, hrest⟩, hwt⟩
      exact ⟨hinit, fun u hu => by rcases List.mem_cons.mp hu with rfl | hmem; exact hwt; exact hrest u hmem⟩
    · rintro ⟨hinit, hall⟩
      exact ⟨⟨hinit, fun u hu => hall u (by simp [hu])⟩, hall w (by simp)⟩

def closedPaths {n q : ℕ} (enabled : (Fin n × Fin q × Bool × Fin q) → Bool)
    (x : Fin n → Bool) : Finset (Fin (n + 1) → Fin q) :=
  Finset.univ.filter (fun p =>
    p 0 = p (Fin.last n) ∧ ∀ i : Fin n, enabled (i, p i.castSucc, x i, p i.succ) = true)

def openPaths {n q : ℕ} (enabled : (Fin n × Fin q × Bool × Fin q) → Bool)
    (k : ℕ) (hk : k ≤ n) (x : Fin k → Bool) (u0 w0 : Fin q) : Finset (Fin (k + 1) → Fin q) :=
  Finset.univ.filter (fun p =>
    p 0 = u0 ∧ p (Fin.last k) = w0 ∧
    ∀ i : Fin k, enabled (⟨i.val, lt_of_lt_of_le i.isLt hk⟩, p i.castSucc, x i, p i.succ) = true)

def maskPref {n : ℕ} (mask : Fin n → Bool → Bool) (k : ℕ) (hk : k ≤ n) :
    Finset (Fin k → Bool) :=
  Finset.univ.filter (fun x => ∀ i : Fin k, mask ⟨i.val, lt_of_lt_of_le i.isLt hk⟩ (x i) = true)

def maskWords {n : ℕ} (mask : Fin n → Bool → Bool) : Finset (Fin n → Bool) :=
  Finset.univ.filter (fun x => ∀ i : Fin n, mask i (x i) = true)

def layerMat {n q : ℕ} (enabled : (Fin n × Fin q × Bool × Fin q) → Bool)
    (mask : Fin n → Bool → Bool) (j : ℕ) :
    (k : ℕ) → k ≤ n → (Fin j → Fin q) → (Fin j → Fin q) → ℕ
  | 0, _, u, w => if u = w then 1 else 0
  | k + 1, hk, u, w =>
    ∑ v : Fin j → Fin q,
      layerMat enabled mask j k (by omega) u v *
        ((if (mask ⟨k, hk⟩ false && decide (∀ r : Fin j, enabled (⟨k, hk⟩, v r, false, w r) = true)) = true then 1 else 0) +
         (if (mask ⟨k, hk⟩ true && decide (∀ r : Fin j, enabled (⟨k, hk⟩, v r, true, w r) = true)) = true then 1 else 0))

lemma openPaths_card_le {n q : ℕ} (enabled : (Fin n × Fin q × Bool × Fin q) → Bool)
    (k : ℕ) (hk : k ≤ n) (x : Fin k → Bool) (u0 w0 : Fin q) :
    (openPaths enabled k hk x u0 w0).card ≤ q ^ k := by
  let tail : (Fin (k + 1) → Fin q) → (Fin k → Fin q) := fun p i => p i.succ
  have hinj : Set.InjOn tail (openPaths enabled k hk x u0 w0 : Set (Fin (k + 1) → Fin q)) := by
    intro p1 hp1 p2 hp2 hEq
    have h1 := (Finset.mem_filter.mp hp1).2.1
    have h2 := (Finset.mem_filter.mp hp2).2.1
    funext i
    refine Fin.cases ?_ ?_ i
    · rw [h1, h2]
    · intro j; exact congrFun hEq j
  calc (openPaths enabled k hk x u0 w0).card
      = ((openPaths enabled k hk x u0 w0).image tail).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.univ : Finset (Fin k → Fin q)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = q ^ k := by simp

lemma openPaths_zero_card {n q : ℕ} (enabled : (Fin n × Fin q × Bool × Fin q) → Bool)
    (x : Fin 0 → Bool) (u0 w0 : Fin q) :
    (openPaths enabled 0 (Nat.zero_le n) x u0 w0).card = if u0 = w0 then 1 else 0 := by
  by_cases h : u0 = w0
  · subst h
    simp only [ite_true]
    have hEq : openPaths enabled 0 (Nat.zero_le n) x u0 u0 = {fun _ => u0} := by
      ext p
      simp only [openPaths, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro ⟨hp0, _, _⟩
        funext i
        have hi : i = 0 := Fin.ext (by omega)
        rw [hi, hp0]
      · intro hp
        subst hp
        refine ⟨rfl, rfl, fun i => Fin.elim0 i⟩
    rw [hEq, Finset.card_singleton]
  · simp only [h, ite_false]
    apply Finset.card_eq_zero.mpr
    rw [Finset.eq_empty_iff_forall_notMem]
    intro p hp
    have hmem := (Finset.mem_filter.mp hp).2
    have hlast : Fin.last 0 = (0 : Fin 1) := rfl
    rw [hlast] at hmem
    exact h (hmem.1.symm.trans hmem.2.1)

def snocFun {k : ℕ} {α : Type} (f : Fin k → α) (x : α) : Fin (k + 1) → α :=
  fun i => if h : i.val < k then f ⟨i.val, h⟩ else x

lemma snocFun_castSucc {k : ℕ} {α : Type} (f : Fin k → α) (x : α) (i : Fin k) :
    snocFun f x i.castSucc = f i := by
  simp [snocFun, i.isLt]

lemma snocFun_last {k : ℕ} {α : Type} (f : Fin k → α) (x : α) :
    snocFun f x (Fin.last k) = x := by
  simp [snocFun]

lemma openPaths_succ_card {n q : ℕ} (enabled : (Fin n × Fin q × Bool × Fin q) → Bool)
    (k : ℕ) (hk : k + 1 ≤ n) (x : Fin (k + 1) → Bool) (u0 w0 : Fin q) :
    (openPaths enabled (k + 1) hk x u0 w0).card =
      ∑ v0 : Fin q,
        (openPaths enabled k (by omega) (fun i => x i.castSucc) u0 v0).card *
          (if enabled (⟨k, hk⟩, v0, x (Fin.last k), w0) = true then 1 else 0) := by
  let S := openPaths enabled (k + 1) hk x u0 w0
  let fiber : Fin q → Finset (Fin (k + 1 + 1) → Fin q) :=
    fun v0 => S.filter (fun p => p (Fin.last k).castSucc = v0)
  have hpart : S.card = ∑ v0 : Fin q, (fiber v0).card := by
    have hbi : S = Finset.univ.biUnion fiber := by
      ext p
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, fiber, Finset.mem_filter]
      exact ⟨fun hp => ⟨p (Fin.last k).castSucc, hp, rfl⟩, fun ⟨_, hp, _⟩ => hp⟩
    conv_lhs => rw [hbi]
    rw [Finset.card_biUnion]
    intro v1 _ v2 _ hne
    change Disjoint (fiber v1) (fiber v2)
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    exact hne ((Finset.mem_filter.mp hp1).2.symm.trans (Finset.mem_filter.mp hp2).2)
  rw [hpart]
  apply Finset.sum_congr rfl
  intro v0 _
  by_cases he : enabled (⟨k, hk⟩, v0, x (Fin.last k), w0) = true
  · simp only [he, ite_true, mul_one]
    apply Finset.card_bij (fun p _ => fun i : Fin (k + 1) => p i.castSucc)
    · intro p hp
      have hpS := (Finset.mem_filter.mp hp).1
      have hpv := (Finset.mem_filter.mp hp).2
      have hcond := (Finset.mem_filter.mp hpS).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hpv, ?_⟩
      · exact hcond.1
      · intro i
        have hi := hcond.2.2 i.castSucc
        have h2 : (i.castSucc : Fin (k + 1)).succ = i.succ.castSucc := by ext; simp
        simpa only [Fin.val_castSucc, h2] using hi
    · intro p1 hp1 p2 hp2 hEq
      have h1w := (Finset.mem_filter.mp (Finset.mem_filter.mp hp1).1).2.2.1
      have h2w := (Finset.mem_filter.mp (Finset.mem_filter.mp hp2).1).2.2.1
      funext i
      refine Fin.lastCases ?_ ?_ i
      · rw [h1w, h2w]
      · intro j; exact congrFun hEq j
    · intro q0 hq0
      have hq := (Finset.mem_filter.mp hq0).2
      let p : Fin (k + 2) → Fin q := snocFun q0 w0
      refine ⟨p, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_⟩, ?_⟩
        · change snocFun q0 w0 (0 : Fin (k + 1)).castSucc = u0
          rw [snocFun_castSucc]; exact hq.1
        · exact snocFun_last q0 w0
        · intro i
          refine Fin.lastCases ?_ ?_ i
          · have hs1 : (Fin.last k).succ = Fin.last (k + 1) := rfl
            dsimp only [p]
            rw [hs1, snocFun_castSucc, snocFun_last, hq.2.1]
            exact he
          · intro j
            have hj2 : j.castSucc.succ = j.succ.castSucc := by ext; simp
            dsimp only [p]
            rw [hj2, snocFun_castSucc, snocFun_castSucc]
            exact hq.2.2 j
        · dsimp only [p]; rw [snocFun_castSucc]; exact hq.2.1
      · funext i; exact snocFun_castSucc q0 w0 i
  · simp only [he, Bool.false_eq_true, ite_false, mul_zero]
    apply Finset.card_eq_zero.mpr
    rw [Finset.eq_empty_iff_forall_notMem]
    intro p hp
    have hpS := (Finset.mem_filter.mp hp).1
    have hpv := (Finset.mem_filter.mp hp).2
    have hcond := (Finset.mem_filter.mp hpS).2
    have hlast := hcond.2.2 (Fin.last k)
    have hs1 : (Fin.last k).succ = Fin.last (k + 1) := rfl
    rw [hs1, hpv, hcond.2.1] at hlast
    exact he hlast

lemma layerMat_eq_sum {n q : ℕ} (enabled : (Fin n × Fin q × Bool × Fin q) → Bool)
    (mask : Fin n → Bool → Bool) (j : ℕ) :
    ∀ (k : ℕ) (hk : k ≤ n) (u w : Fin j → Fin q),
      layerMat enabled mask j k hk u w =
        ∑ x ∈ maskPref mask k hk, ∏ r : Fin j, (openPaths enabled k hk x (u r) (w r)).card
  | 0, hk, u, w => by
    simp only [layerMat]
    have hpref : maskPref mask 0 hk = {Fin.elim0} := by
      ext x
      simp only [maskPref, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun _ => funext (fun i => Fin.elim0 i), fun _ i => Fin.elim0 i⟩
    rw [hpref, Finset.sum_singleton]
    have hprod : ∏ r : Fin j, (openPaths enabled 0 hk Fin.elim0 (u r) (w r)).card =
        ∏ r : Fin j, if u r = w r then 1 else 0 := by
      apply Finset.prod_congr rfl
      intro r _
      exact openPaths_zero_card enabled Fin.elim0 (u r) (w r)
    rw [hprod]
    by_cases huw : u = w
    · subst huw; simp
    · simp only [huw, ite_false]
      have hex : ∃ r : Fin j, u r ≠ w r := by
        by_contra hall; push Not at hall; exact huw (funext hall)
      rcases hex with ⟨r, hr⟩
      exact (Finset.prod_eq_zero (Finset.mem_univ r) (by simp [hr])).symm
  | k + 1, hk, u, w => by
    simp only [layerMat]
    have hstep_edge : ∀ (v : Fin j → Fin q) (b : Bool),
        (if (mask ⟨k, hk⟩ b && decide (∀ r : Fin j, enabled (⟨k, hk⟩, v r, b, w r) = true)) = true then 1 else 0) =
          (if mask ⟨k, hk⟩ b = true then 1 else 0) *
            ∏ r : Fin j, (if enabled (⟨k, hk⟩, v r, b, w r) = true then 1 else 0) := by
      intro v b
      by_cases hm : mask ⟨k, hk⟩ b = true
      · simp only [hm, Bool.true_and, ite_true, one_mul]
        by_cases ha : ∀ r : Fin j, enabled (⟨k, hk⟩, v r, b, w r) = true
        · simp [ha]
        · simp only [ha, decide_false, Bool.false_eq_true, ite_false]
          push Not at ha
          rcases ha with ⟨r, hr⟩
          symm
          exact Finset.prod_eq_zero (Finset.mem_univ r) (by simp [hr])
      · simp [hm]
    have hprod_expand : ∀ (x : Fin (k + 1) → Bool),
        ∏ r : Fin j, (openPaths enabled (k + 1) hk x (u r) (w r)).card =
          ∑ v : Fin j → Fin q,
            (∏ r : Fin j, (openPaths enabled k (by omega) (fun i => x i.castSucc) (u r) (v r)).card) *
              (∏ r : Fin j, if enabled (⟨k, hk⟩, v r, x (Fin.last k), w r) = true then 1 else 0) := by
      intro x
      have h1 :
          ∏ r : Fin j, (openPaths enabled (k + 1) hk x (u r) (w r)).card =
            ∏ r : Fin j, ∑ v0 : Fin q,
              (openPaths enabled k (by omega) (fun i => x i.castSucc) (u r) v0).card *
                (if enabled (⟨k, hk⟩, v0, x (Fin.last k), w r) = true then 1 else 0) := by
        apply Finset.prod_congr rfl
        intro r _
        exact openPaths_succ_card enabled k hk x (u r) (w r)
      rw [h1, Fintype.prod_sum]
      apply Finset.sum_congr rfl
      intro v _
      exact Finset.prod_mul_distrib
    have hrhs_split :
        ∑ x ∈ maskPref mask (k + 1) hk,
          ∏ r : Fin j, (openPaths enabled (k + 1) hk x (u r) (w r)).card =
        ∑ p ∈ (maskPref mask k (by omega)) ×ˢ (Finset.univ : Finset Bool),
          (if mask ⟨k, hk⟩ p.2 = true then 1 else 0) *
            ∏ r : Fin j, (openPaths enabled (k + 1) hk (snocFun p.1 p.2) (u r) (w r)).card := by
      rw [Finset.sum_product]
      symm
      calc ∑ x0 ∈ maskPref mask k (by omega), ∑ b : Bool,
            (if mask ⟨k, hk⟩ b = true then 1 else 0) *
              ∏ r : Fin j, (openPaths enabled (k + 1) hk (snocFun x0 b) (u r) (w r)).card
          = ∑ x0 ∈ maskPref mask k (by omega), ∑ b ∈ Finset.univ.filter (fun b : Bool => mask ⟨k, hk⟩ b = true),
              ∏ r : Fin j, (openPaths enabled (k + 1) hk (snocFun x0 b) (u r) (w r)).card := by
            apply Finset.sum_congr rfl
            intro x0 _
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro b _
            split <;> simp
        _ = ∑ p ∈ (maskPref mask k (by omega)) ×ˢ (Finset.univ.filter (fun b : Bool => mask ⟨k, hk⟩ b = true)),
              ∏ r : Fin j, (openPaths enabled (k + 1) hk (snocFun p.1 p.2) (u r) (w r)).card := by
            rw [Finset.sum_product]
        _ = ∑ x ∈ maskPref mask (k + 1) hk,
              ∏ r : Fin j, (openPaths enabled (k + 1) hk x (u r) (w r)).card := by
            apply Finset.sum_nbij (fun p => snocFun p.1 p.2)
            · intro p hp
              rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
              have h1 := (Finset.mem_filter.mp hp1).2
              have h2 := (Finset.mem_filter.mp hp2).2
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
              intro i
              refine Fin.lastCases ?_ ?_ i
              · rw [snocFun_last]; exact h2
              · intro i0; rw [snocFun_castSucc]; exact h1 i0
            · intro p1 _ p2 _ hEq
              ext i
              · have := congrFun hEq i.castSucc; simpa [snocFun_castSucc] using this
              · have := congrFun hEq (Fin.last k); simpa [snocFun_last] using this
            · intro x hx
              have hcond := (Finset.mem_filter.mp hx).2
              refine ⟨(fun i => x i.castSucc, x (Fin.last k)), ?_, ?_⟩
              · refine Finset.mem_product.mpr ⟨?_, ?_⟩
                · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => hcond i.castSucc⟩
                · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcond (Fin.last k)⟩
              · funext i
                refine Fin.lastCases ?_ ?_ i
                · exact snocFun_last _ _
                · intro i0; exact snocFun_castSucc _ _ i0
            · intro p _; rfl
    rw [hrhs_split, Finset.sum_product]
    have hinner :
        ∑ x0 ∈ maskPref mask k (by omega), ∑ b : Bool,
          (if mask ⟨k, hk⟩ b = true then 1 else 0) *
            ∏ r : Fin j, (openPaths enabled (k + 1) hk (snocFun x0 b) (u r) (w r)).card =
        ∑ v : Fin j → Fin q,
          (∑ x0 ∈ maskPref mask k (by omega), ∏ r : Fin j, (openPaths enabled k (by omega) x0 (u r) (v r)).card) *
            ∑ b : Bool, (if mask ⟨k, hk⟩ b = true then 1 else 0) *
              ∏ r : Fin j, (if enabled (⟨k, hk⟩, v r, b, w r) = true then 1 else 0) := by
      have hrew :
          ∑ x0 ∈ maskPref mask k (by omega), ∑ b : Bool,
            (if mask ⟨k, hk⟩ b = true then 1 else 0) *
              ∏ r : Fin j, (openPaths enabled (k + 1) hk (snocFun x0 b) (u r) (w r)).card =
          ∑ x0 ∈ maskPref mask k (by omega), ∑ v : Fin j → Fin q,
            (∏ r : Fin j, (openPaths enabled k (by omega) x0 (u r) (v r)).card) *
              ∑ b : Bool, (if mask ⟨k, hk⟩ b = true then 1 else 0) *
                ∏ r : Fin j, (if enabled (⟨k, hk⟩, v r, b, w r) = true then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro x0 _
        calc ∑ b : Bool, (if mask ⟨k, hk⟩ b = true then 1 else 0) *
                ∏ r : Fin j, (openPaths enabled (k + 1) hk (snocFun x0 b) (u r) (w r)).card
            = ∑ b : Bool, ∑ v : Fin j → Fin q,
                (if mask ⟨k, hk⟩ b = true then 1 else 0) *
                  ((∏ r : Fin j, (openPaths enabled k (by omega) x0 (u r) (v r)).card) *
                    (∏ r : Fin j, if enabled (⟨k, hk⟩, v r, b, w r) = true then 1 else 0)) := by
              apply Finset.sum_congr rfl
              intro b _
              rw [hprod_expand (snocFun x0 b), Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro v _
              have hsn : (fun i : Fin k => snocFun x0 b i.castSucc) = x0 :=
                funext (fun i => snocFun_castSucc x0 b i)
              rw [hsn, snocFun_last]
          _ = ∑ v : Fin j → Fin q, ∑ b : Bool,
                (if mask ⟨k, hk⟩ b = true then 1 else 0) *
                  ((∏ r : Fin j, (openPaths enabled k (by omega) x0 (u r) (v r)).card) *
                    (∏ r : Fin j, if enabled (⟨k, hk⟩, v r, b, w r) = true then 1 else 0)) :=
              Finset.sum_comm
          _ = ∑ v : Fin j → Fin q,
                (∏ r : Fin j, (openPaths enabled k (by omega) x0 (u r) (v r)).card) *
                  ∑ b : Bool, (if mask ⟨k, hk⟩ b = true then 1 else 0) *
                    ∏ r : Fin j, (if enabled (⟨k, hk⟩, v r, b, w r) = true then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro v _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro b _
              ring
      rw [hrew, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.sum_mul]
    rw [hinner]
    apply Finset.sum_congr rfl
    intro v _
    rw [layerMat_eq_sum enabled mask j k (by omega) u v]
    congr 1
    rw [Fintype.sum_bool, add_comm]
    rw [hstep_edge v false, hstep_edge v true]

lemma layerMat_le {n q : ℕ} (enabled : (Fin n × Fin q × Bool × Fin q) → Bool)
    (mask : Fin n → Bool → Bool) (j k : ℕ) (hk : k ≤ n) (u w : Fin j → Fin q) :
    layerMat enabled mask j k hk u w ≤ 2 ^ k * q ^ (k * j) := by
  rw [layerMat_eq_sum]
  calc ∑ x ∈ maskPref mask k hk, ∏ r : Fin j, (openPaths enabled k hk x (u r) (w r)).card
      ≤ ∑ _x ∈ maskPref mask k hk, q ^ (k * j) := by
        apply Finset.sum_le_sum
        intro x _
        calc ∏ r : Fin j, (openPaths enabled k hk x (u r) (w r)).card
            ≤ ∏ _r : Fin j, q ^ k :=
              Finset.prod_le_prod (fun r _ => openPaths_card_le enabled k hk x (u r) (w r))
          _ = (q ^ k) ^ j := by simp
          _ = q ^ (k * j) := (Nat.pow_mul q k j).symm
    _ = (maskPref mask k hk).card * q ^ (k * j) := by simp
    _ ≤ 2 ^ k * q ^ (k * j) := by
        apply Nat.mul_le_mul_right
        calc (maskPref mask k hk).card
            ≤ (Finset.univ : Finset (Fin k → Bool)).card := Finset.card_le_card (Finset.subset_univ _)
          _ = 2 ^ k := by simp

lemma closedPaths_card_eq_sum_open {n q : ℕ} (enabled : (Fin n × Fin q × Bool × Fin q) → Bool)
    (x : Fin n → Bool) :
    (closedPaths enabled x).card =
      ∑ u0 : Fin q, (openPaths enabled n le_rfl x u0 u0).card := by
  have hbi : closedPaths enabled x =
      Finset.univ.biUnion (fun u0 : Fin q => openPaths enabled n le_rfl x u0 u0) := by
    ext p
    simp only [closedPaths, openPaths, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · intro ⟨hclose, hedges⟩
      exact ⟨p 0, rfl, hclose.symm, hedges⟩
    · rintro ⟨u0, h0, hlast, hedges⟩
      exact ⟨h0.trans hlast.symm, hedges⟩
  rw [hbi, Finset.card_biUnion]
  intro u1 _ u2 _ hne
  change Disjoint _ _
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  exact hne ((Finset.mem_filter.mp hp1).2.1.symm.trans (Finset.mem_filter.mp hp2).2.1)

lemma layerMat_trace_eq {n q : ℕ} (enabled : (Fin n × Fin q × Bool × Fin q) → Bool)
    (mask : Fin n → Bool → Bool) (j : ℕ) :
    ∑ u : Fin j → Fin q, layerMat enabled mask j n le_rfl u u =
      ∑ x ∈ maskWords mask, (closedPaths enabled x).card ^ j := by
  have hmp : maskPref mask n le_rfl = maskWords mask := by
    ext x; simp [maskPref, maskWords]
  have h1 :
      ∑ u : Fin j → Fin q, layerMat enabled mask j n le_rfl u u =
        ∑ x ∈ maskWords mask, ∑ u : Fin j → Fin q,
          ∏ r : Fin j, (openPaths enabled n le_rfl x (u r) (u r)).card := by
    have hcongr :
        ∑ u : Fin j → Fin q, layerMat enabled mask j n le_rfl u u =
          ∑ u : Fin j → Fin q, ∑ x ∈ maskWords mask,
            ∏ r : Fin j, (openPaths enabled n le_rfl x (u r) (u r)).card := by
      apply Finset.sum_congr rfl
      intro u _
      rw [layerMat_eq_sum, hmp]
    rw [hcongr, Finset.sum_comm]
  rw [h1]
  apply Finset.sum_congr rfl
  intro x _
  have hps := (Fintype.prod_sum (fun (_ : Fin j) (u0 : Fin q) => (openPaths enabled n le_rfl x u0 u0).card)).symm
  rw [hps, ← closedPaths_card_eq_sum_open]
  simp

lemma closedPaths_card_le {n q : ℕ} (hn : 0 < n) (enabled : (Fin n × Fin q × Bool × Fin q) → Bool)
    (x : Fin n → Bool) :
    (closedPaths enabled x).card ≤ q ^ n := by
  let proj : (Fin (n + 1) → Fin q) → (Fin n → Fin q) := fun p i => p i.castSucc
  have hinj : Set.InjOn proj (closedPaths enabled x : Set (Fin (n + 1) → Fin q)) := by
    intro p1 hp1 p2 hp2 hEq
    have h1 := (Finset.mem_filter.mp hp1).2.1
    have h2 := (Finset.mem_filter.mp hp2).2.1
    funext i
    refine Fin.lastCases ?_ ?_ i
    · rw [← h1, ← h2]
      have h0 := congrFun hEq ⟨0, hn⟩
      exact h0
    · intro j; exact congrFun hEq j
  calc (closedPaths enabled x).card
      = ((closedPaths enabled x).image proj).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.univ : Finset (Fin n → Fin q)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = q ^ n := by simp

lemma layerMat_trace_le {n q : ℕ} (hn : 0 < n) (enabled : (Fin n × Fin q × Bool × Fin q) → Bool)
    (mask : Fin n → Bool → Bool) (j : ℕ) :
    ∑ u : Fin j → Fin q, layerMat enabled mask j n le_rfl u u ≤ 2 ^ n * q ^ (n * j) := by
  rw [layerMat_trace_eq]
  calc ∑ x ∈ maskWords mask, (closedPaths enabled x).card ^ j
      ≤ ∑ _x ∈ maskWords mask, (q ^ n) ^ j := by
        apply Finset.sum_le_sum
        intro x _
        exact Nat.pow_le_pow_left (closedPaths_card_le hn enabled x) j
    _ = (maskWords mask).card * q ^ (n * j) := by simp [Nat.pow_mul]
    _ ≤ 2 ^ n * q ^ (n * j) := by
        apply Nat.mul_le_mul_right
        calc (maskWords mask).card
            ≤ (Finset.univ : Finset (Fin n → Bool)).card := Finset.card_le_card (Finset.subset_univ _)
          _ = 2 ^ n := by simp

def dotLayer {q j B : ℕ} (N : ℕ) (G : List BGate)
    (M : (Fin j → Fin q) → (Fin j → Fin q) → Fin B → ℕ)
    (e : Bool × (Fin j → Fin q) × (Fin j → Fin q) → ℕ)
    (u w : Fin j → Fin q) : List (Fin j → Fin q) → List BGate × (Fin B → ℕ)
  | [] => (G, constReg B 0)
  | v :: vs =>
    let r1 := dotLayer N G M e u w vs
    let g0 := regGate N r1.1 (e (false, v, w)) (M u v)
    let a0 := regAdd N g0.1 r1.2 g0.2
    let g1 := regGate N a0.1 (e (true, v, w)) (M u v)
    let a1 := regAdd N g1.1 a0.2.1 g1.2
    (a1.1, a1.2.1)

lemma dotLayer_spec {N q j B : ℕ} (hN : 2 ≤ N) (G : List BGate)
    (M : (Fin j → Fin q) → (Fin j → Fin q) → Fin B → ℕ)
    (e : Bool × (Fin j → Fin q) × (Fin j → Fin q) → ℕ)
    (u w : Fin j → Fin q) (l : List (Fin j → Fin q))
    (hWF : WF N G)
    (hM : ∀ v ∈ l, RegOK N G (M u v))
    (he : ∀ v ∈ l, e (false, v, w) < N + G.length ∧ e (true, v, w) < N + G.length) :
    let res := dotLayer N G M e u w l
    Extends G res.1 ∧ res.1.length ≤ G.length + 12 * B * l.length ∧ WF N res.1 ∧
    RegOK N res.1 res.2 ∧
    ∀ src, HasBase src N →
      (l.map (fun v => regVal G src (M u v) *
        ((evalW G src (e (false, v, w))).toNat + (evalW G src (e (true, v, w))).toNat))).sum < 2 ^ B →
      regVal res.1 src res.2 =
        (l.map (fun v => regVal G src (M u v) *
          ((evalW G src (e (false, v, w))).toNat + (evalW G src (e (true, v, w))).toNat))).sum := by
  induction l with
  | nil =>
    refine ⟨extends_rfl G, by simp [dotLayer], hWF, constReg_ok hN G 0, ?_⟩
    intro src hbase _
    simp [dotLayer, constReg_val hbase]
  | cons v vs ih =>
    have hvs := ih (fun x hx => hM x (by simp [hx])) (fun x hx => he x (by simp [hx]))
    dsimp only [dotLayer]
    set r1 := dotLayer N G M e u w vs
    have he1 := hvs.1
    have hl1 := hvs.2.1
    have hw1 := hvs.2.2.1
    have hok1 := hvs.2.2.2.1
    have hev1 := hvs.2.2.2.2
    have hlen_le1 : G.length ≤ r1.1.length := extends_len he1
    have hMv_ok : RegOK N r1.1 (M u v) := regOK_extends he1 (hM v (by simp))
    have he0_lt : e (false, v, w) < N + r1.1.length := by have := (he v (by simp)).1; omega
    have hg0 := regGate_spec hw1 he0_lt hMv_ok
    set g0 := regGate N r1.1 (e (false, v, w)) (M u v)
    have hok1_g0 : RegOK N g0.1 r1.2 := regOK_extends hg0.1 hok1
    have ha0 := regAdd_spec hN hg0.2.2.1 hok1_g0 hg0.2.2.2.1
    set a0 := regAdd N g0.1 r1.2 g0.2
    have he_r1_a0 : Extends r1.1 a0.1 := extends_trans hg0.1 ha0.1
    have hMv_ok2 : RegOK N a0.1 (M u v) := regOK_extends he_r1_a0 hMv_ok
    have he1_lt : e (true, v, w) < N + a0.1.length := by
      have := (he v (by simp)).2; have := extends_len (extends_trans he1 he_r1_a0); omega
    have hg1 := regGate_spec ha0.2.2.1 he1_lt hMv_ok2
    set g1 := regGate N a0.1 (e (true, v, w)) (M u v)
    have hoka0_g1 : RegOK N g1.1 a0.2.1 := regOK_extends hg1.1 ha0.2.2.2.1
    have ha1 := regAdd_spec hN hg1.2.2.1 hoka0_g1 hg1.2.2.2.1
    set a1 := regAdd N g1.1 a0.2.1 g1.2
    refine ⟨extends_trans he1 (extends_trans he_r1_a0 (extends_trans hg1.1 ha1.1)), ?_,
      ha1.2.2.1, ha1.2.2.2.1, ?_⟩
    · have h1 := hg0.2.1
      have h2 := ha0.2.1
      have h3 := hg1.2.1
      have h4 := ha1.2.1
      have hmul : 12 * B * (vs.length + 1) = 12 * B * vs.length + 12 * B := Nat.mul_succ (12 * B) _
      simp only [List.length_cons]
      omega
    · intro src hbase hlt
      simp only [List.map_cons, List.sum_cons] at hlt ⊢
      set restSum := (vs.map (fun x => regVal G src (M u x) *
        ((evalW G src (e (false, x, w))).toNat + (evalW G src (e (true, x, w))).toNat))).sum
      have hrest_lt : restSum < 2 ^ B := by omega
      have hvr1 : regVal r1.1 src r1.2 = restSum := hev1 src hbase hrest_lt
      have hg0_val : regVal g0.1 src g0.2 = regVal G src (M u v) * (evalW G src (e (false, v, w))).toNat := by
        rw [hg0.2.2.2.2 src hbase.1]
        rw [evalW_extends he1 (by rw [hbase.1]; exact (he v (by simp)).1)]
        rw [regVal_extends he1 hbase.1 (hM v (by simp))]
        cases evalW G src (e (false, v, w)) <;> simp
      have hr1_g0 : regVal g0.1 src r1.2 = restSum := by
        rw [regVal_extends hg0.1 hbase.1 hok1, hvr1]
      have hsum0_lt : regVal g0.1 src r1.2 + regVal g0.1 src g0.2 < 2 ^ B := by
        rw [hr1_g0, hg0_val]
        have : regVal G src (M u v) * (evalW G src (e (false, v, w))).toNat ≤
            regVal G src (M u v) * ((evalW G src (e (false, v, w))).toNat + (evalW G src (e (true, v, w))).toNat) :=
          Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
        omega
      have ha0_val : regVal a0.1 src a0.2.1 =
          restSum + regVal G src (M u v) * (evalW G src (e (false, v, w))).toNat := by
        rw [regAdd_val_of_lt hN hg0.2.2.1 hok1_g0 hg0.2.2.2.1 hbase hsum0_lt, hr1_g0, hg0_val]
      have hg1_val : regVal g1.1 src g1.2 = regVal G src (M u v) * (evalW G src (e (true, v, w))).toNat := by
        rw [hg1.2.2.2.2 src hbase.1]
        rw [evalW_extends (extends_trans he1 he_r1_a0) (by rw [hbase.1]; exact (he v (by simp)).2)]
        rw [regVal_extends (extends_trans he1 he_r1_a0) hbase.1 (hM v (by simp))]
        cases evalW G src (e (true, v, w)) <;> simp
      have ha0_g1 : regVal g1.1 src a0.2.1 =
          restSum + regVal G src (M u v) * (evalW G src (e (false, v, w))).toNat := by
        rw [regVal_extends hg1.1 hbase.1 ha0.2.2.2.1, ha0_val]
      have hsum1_eq : regVal g1.1 src a0.2.1 + regVal g1.1 src g1.2 =
          regVal G src (M u v) * ((evalW G src (e (false, v, w))).toNat + (evalW G src (e (true, v, w))).toNat) +
            restSum := by
        rw [ha0_g1, hg1_val, Nat.mul_add]
        omega
      have hsum1_lt : regVal g1.1 src a0.2.1 + regVal g1.1 src g1.2 < 2 ^ B := by
        rw [hsum1_eq]; exact hlt
      rw [regAdd_val_of_lt hN hg1.2.2.1 hoka0_g1 hg1.2.2.2.1 hbase hsum1_lt, hsum1_eq]

noncomputable def buildLayer {n q j B : ℕ} (N : ℕ)
    (edgeW : (Fin n × Fin q × Bool × Fin q) → ℕ)
    (maskW : Fin n → Bool → ℕ) (i : Fin n) (G : List BGate)
    (M : (Fin j → Fin q) → (Fin j → Fin q) → Fin B → ℕ) :
    List BGate × ((Fin j → Fin q) → (Fin j → Fin q) → Fin B → ℕ) :=
  let eList := (Finset.univ : Finset (Bool × (Fin j → Fin q) × (Fin j → Fin q))).toList
  let eRes := buildMap (fun G0 (p : Bool × (Fin j → Fin q) × (Fin j → Fin q)) =>
    andList N G0 (maskW i p.1) ((List.finRange j).map (fun r => edgeW (i, p.2.1 r, p.1, p.2.2 r))))
    0 G eList
  let vList := (Finset.univ : Finset (Fin j → Fin q)).toList
  let pList := (Finset.univ : Finset ((Fin j → Fin q) × (Fin j → Fin q))).toList
  let mRes := buildMap (fun G0 (p : (Fin j → Fin q) × (Fin j → Fin q)) =>
    dotLayer N G0 M eRes.2 p.1 p.2 vList)
    (constReg B 0) eRes.1 pList
  (mRes.1, fun u w => mRes.2 (u, w))

lemma buildLayer_spec {N n q j B k : ℕ} (hN : 2 ≤ N) (hk : k + 1 ≤ n)
    (edgeW : (Fin n × Fin q × Bool × Fin q) → ℕ)
    (maskW : Fin n → Bool → ℕ) (G : List BGate)
    (M : (Fin j → Fin q) → (Fin j → Fin q) → Fin B → ℕ)
    (hWF : WF N G)
    (hedge : ∀ e, edgeW e < N)
    (hmask : ∀ i b, maskW i b < N + G.length)
    (hM : ∀ u v, RegOK N G (M u v)) :
    let res := buildLayer N edgeW maskW ⟨k, hk⟩ G M
    Extends G res.1 ∧
    res.1.length ≤ G.length + 2 * j * q ^ (2 * j) + 12 * B * q ^ (3 * j) ∧
    WF N res.1 ∧
    (∀ u w, RegOK N res.1 (res.2 u w)) ∧
    ∀ src enabled mask, HasBase src N →
      (∀ e, evalW G src (edgeW e) = enabled e) →
      (∀ i b, evalW G src (maskW i b) = mask i b) →
      (∀ u v, regVal G src (M u v) = layerMat enabled mask j k (by omega) u v) →
      2 ^ n * q ^ (n * j) < 2 ^ B →
      ∀ u w, regVal res.1 src (res.2 u w) = layerMat enabled mask j (k + 1) hk u w := by
  dsimp only [buildLayer]
  set eList := (Finset.univ : Finset (Bool × (Fin j → Fin q) × (Fin j → Fin q))).toList
  set eStep : List BGate → (Bool × (Fin j → Fin q) × (Fin j → Fin q)) → List BGate × ℕ :=
    fun G0 p => andList N G0 (maskW ⟨k, hk⟩ p.1)
      ((List.finRange j).map (fun r => edgeW (⟨k, hk⟩, p.2.1 r, p.1, p.2.2 r)))
  set eValid : List BGate → ℕ → Prop := fun G0 w => w < N + G0.length
  set eSpec : List BGate → (Bool × (Fin j → Fin q) × (Fin j → Fin q)) → ℕ → Prop :=
    fun G0 p w => ∀ (src : List Bool) (enabled : (Fin n × Fin q × Bool × Fin q) → Bool)
      (mask : Fin n → Bool → Bool), HasBase src N →
      (∀ e, evalW G src (edgeW e) = enabled e) →
      (∀ i b, evalW G src (maskW i b) = mask i b) →
      (evalW G0 src w = true ↔
        (mask ⟨k, hk⟩ p.1 && decide (∀ r : Fin j, enabled (⟨k, hk⟩, p.2.1 r, p.1, p.2.2 r) = true)) = true)
  have heRes := buildMap_spec (N := N) (cost := j) eStep eValid eSpec
    (fun {G1 G2 t} he hv => by have := extends_len he; omega)
    (fun {G1 G2 p t} he hv hs src enabled mask hbase hed hmk => by
      rw [evalW_extends he (by rw [hbase.1]; exact hv)]
      exact hs src enabled mask hbase hed hmk)
    0 eList (Finset.nodup_toList _) G hWF (by
      intro G0 p _ hExt hWF0
      have hlen_l : ((List.finRange j).map (fun r => edgeW (⟨k, hk⟩, p.2.1 r, p.1, p.2.2 r))).length = j := by
        simp
      have hl_lt : ∀ w ∈ (List.finRange j).map (fun r => edgeW (⟨k, hk⟩, p.2.1 r, p.1, p.2.2 r)),
          w < N + G0.length := by
        intro w hw
        rcases List.mem_map.mp hw with ⟨r, _, rfl⟩
        have := hedge (⟨k, hk⟩, p.2.1 r, p.1, p.2.2 r)
        omega
      have hmlt : maskW ⟨k, hk⟩ p.1 < N + G0.length := by
        have := hmask ⟨k, hk⟩ p.1; have := extends_len hExt; omega
      have hand := andList_spec _ hWF0 hmlt hl_lt
      refine ⟨hand.1, by rw [hand.2.1, hlen_l], hand.2.2.1, hand.2.2.2.1, ?_⟩
      intro src enabled mask hbase hed hmk
      rw [hand.2.2.2.2 src hbase.1]
      rw [evalW_extends hExt (by rw [hbase.1]; exact hmask ⟨k, hk⟩ p.1), hmk]
      rw [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · intro ⟨h1, h2⟩
        refine ⟨h1, fun r => ?_⟩
        have hr := h2 (edgeW (⟨k, hk⟩, p.2.1 r, p.1, p.2.2 r))
          (List.mem_map.mpr ⟨r, List.mem_finRange r, rfl⟩)
        rw [evalW_extends hExt (by rw [hbase.1]; have := hedge (⟨k, hk⟩, p.2.1 r, p.1, p.2.2 r); omega),
          hed] at hr
        exact hr
      · intro ⟨h1, h2⟩
        refine ⟨h1, fun w hw => ?_⟩
        rcases List.mem_map.mp hw with ⟨r, _, rfl⟩
        rw [evalW_extends hExt (by rw [hbase.1]; have := hedge (⟨k, hk⟩, p.2.1 r, p.1, p.2.2 r); omega),
          hed]
        exact h2 r)
  set eRes := buildMap eStep 0 G eList
  set vList := (Finset.univ : Finset (Fin j → Fin q)).toList
  set pList := (Finset.univ : Finset ((Fin j → Fin q) × (Fin j → Fin q))).toList
  set mStep : List BGate → ((Fin j → Fin q) × (Fin j → Fin q)) → List BGate × (Fin B → ℕ) :=
    fun G0 p => dotLayer N G0 M eRes.2 p.1 p.2 vList
  set mValid : List BGate → (Fin B → ℕ) → Prop := fun G0 r => RegOK N G0 r
  set mSpec : List BGate → ((Fin j → Fin q) × (Fin j → Fin q)) → (Fin B → ℕ) → Prop :=
    fun G0 p r => ∀ (src : List Bool) (enabled : (Fin n × Fin q × Bool × Fin q) → Bool)
      (mask : Fin n → Bool → Bool), HasBase src N →
      (∀ e, evalW G src (edgeW e) = enabled e) →
      (∀ i b, evalW G src (maskW i b) = mask i b) →
      (∀ u v, regVal G src (M u v) = layerMat enabled mask j k (by omega) u v) →
      2 ^ n * q ^ (n * j) < 2 ^ B →
      regVal G0 src r = layerMat enabled mask j (k + 1) hk p.1 p.2
  have hmRes := buildMap_spec (N := N) (cost := 12 * B * q ^ j) mStep mValid mSpec
    (fun {G1 G2 t} he hv => regOK_extends he hv)
    (fun {G1 G2 p t} he hv hs src enabled mask hbase hed hmk hMv hlt => by
      rw [regVal_extends he hbase.1 hv]
      exact hs src enabled mask hbase hed hmk hMv hlt)
    (constReg B 0) pList (Finset.nodup_toList _) eRes.1 heRes.2.2.1 (by
      intro G0 p _ hExt0 hWF0
      have heG_G0 : Extends G G0 := extends_trans heRes.1 hExt0
      have hM0 : ∀ v ∈ vList, RegOK N G0 (M p.1 v) := fun v _ => regOK_extends heG_G0 (hM p.1 v)
      have he0 : ∀ v ∈ vList, eRes.2 (false, v, p.2) < N + G0.length ∧ eRes.2 (true, v, p.2) < N + G0.length := by
        intro v _
        have h1 := (heRes.2.2.2 (false, v, p.2) (Finset.mem_toList.mpr (Finset.mem_univ _))).1
        have h2 := (heRes.2.2.2 (true, v, p.2) (Finset.mem_toList.mpr (Finset.mem_univ _))).1
        have hlen := extends_len hExt0
        exact ⟨by omega, by omega⟩
      have hdot := dotLayer_spec hN G0 M eRes.2 p.1 p.2 vList hWF0 hM0 he0
      have hvlen : vList.length = q ^ j := by simp [vList]
      refine ⟨hdot.1, by rw [hvlen] at hdot; exact hdot.2.1, hdot.2.2.1, hdot.2.2.2.1, ?_⟩
      intro src enabled mask hbase hed hmk hMv hlt
      have hsum_eq :
          (vList.map (fun v => regVal G0 src (M p.1 v) *
            ((evalW G0 src (eRes.2 (false, v, p.2))).toNat + (evalW G0 src (eRes.2 (true, v, p.2))).toNat))).sum =
          layerMat enabled mask j (k + 1) hk p.1 p.2 := by
        rw [list_map_toList_sum]
        simp only [layerMat]
        apply Finset.sum_congr rfl
        intro v _
        rw [regVal_extends heG_G0 hbase.1 (hM p.1 v), hMv p.1 v]
        have hbf := (heRes.2.2.2 (false, v, p.2) (Finset.mem_toList.mpr (Finset.mem_univ _)))
        have hbt := (heRes.2.2.2 (true, v, p.2) (Finset.mem_toList.mpr (Finset.mem_univ _)))
        rw [evalW_extends hExt0 (by rw [hbase.1]; exact hbf.1)]
        rw [evalW_extends hExt0 (by rw [hbase.1]; exact hbt.1)]
        have hsf := hbf.2 src enabled mask hbase hed hmk
        have hst := hbt.2 src enabled mask hbase hed hmk
        congr 1
        have hb2n : ∀ (x y : Bool), (x = true ↔ y = true) → x.toNat = if y = true then 1 else 0 := by
          intro x y hiff; cases x <;> cases y <;> simp at hiff ⊢
        rw [hb2n _ _ hsf, hb2n _ _ hst]
      have hsum_lt : (vList.map (fun v => regVal G0 src (M p.1 v) *
            ((evalW G0 src (eRes.2 (false, v, p.2))).toNat + (evalW G0 src (eRes.2 (true, v, p.2))).toNat))).sum < 2 ^ B := by
        rw [hsum_eq]
        have hle := layerMat_le enabled mask j (k + 1) hk p.1 p.2
        have hmon : 2 ^ (k + 1) * q ^ ((k + 1) * j) ≤ 2 ^ n * q ^ (n * j) := by
          apply Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) hk)
          cases q with
          | zero =>
            cases j with
            | zero => simp
            | succ j' =>
              have hpos1 : 0 < (k + 1) * (j' + 1) := Nat.mul_pos (by omega) (by omega)
              have hpos2 : 0 < n * (j' + 1) := Nat.mul_pos (by omega) (by omega)
              rw [Nat.zero_pow hpos1, Nat.zero_pow hpos2]
          | succ q' =>
            exact Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right j hk)
        exact lt_of_le_of_lt (le_trans hle hmon) hlt
      rw [hdot.2.2.2.2 src hbase hsum_lt, hsum_eq])
  set mRes := buildMap mStep (constReg B 0) eRes.1 pList
  have helen : eList.length = 2 * q ^ (2 * j) := by
    simp only [eList, Finset.length_toList, Finset.card_univ, Fintype.card_prod,
      Fintype.card_bool, Fintype.card_fun, Fintype.card_fin]
    rw [← Nat.pow_add, ← two_mul j]
  have hplen : pList.length = q ^ (2 * j) := by
    simp only [pList, Finset.length_toList, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fun, Fintype.card_fin]
    rw [← Nat.pow_add, ← two_mul j]
  refine ⟨extends_trans heRes.1 hmRes.1, ?_, hmRes.2.2.1, ?_, ?_⟩
  · have h1 := heRes.2.1
    have h2 := hmRes.2.1
    rw [helen] at h1
    rw [hplen] at h2
    have hmul1 : j * (2 * q ^ (2 * j)) = 2 * j * q ^ (2 * j) := by ring
    have hmul2 : 12 * B * q ^ j * q ^ (2 * j) = 12 * B * q ^ (3 * j) := by
      rw [Nat.mul_assoc, ← Nat.pow_add]
      congr 2; omega
    omega
  · intro u w
    exact (hmRes.2.2.2 (u, w) (Finset.mem_toList.mpr (Finset.mem_univ _))).1
  · intro src enabled mask hbase hed hmk hMv hlt u w
    exact (hmRes.2.2.2 (u, w) (Finset.mem_toList.mpr (Finset.mem_univ _))).2 src enabled mask hbase hed hmk hMv hlt

noncomputable def buildMatPow {n q j B : ℕ} (N : ℕ)
    (edgeW : (Fin n × Fin q × Bool × Fin q) → ℕ)
    (maskW : Fin n → Bool → ℕ) (G : List BGate) :
    (k : ℕ) → k ≤ n → List BGate × ((Fin j → Fin q) → (Fin j → Fin q) → Fin B → ℕ)
  | 0, _ => (G, fun u w => constReg B (if u = w then 1 else 0))
  | k + 1, hk =>
    let r1 := buildMatPow N edgeW maskW G k (by omega)
    buildLayer N edgeW maskW ⟨k, hk⟩ r1.1 r1.2

lemma buildMatPow_spec {N n q j B : ℕ} (hN : 2 ≤ N) (hq : 0 < q)
    (edgeW : (Fin n × Fin q × Bool × Fin q) → ℕ)
    (maskW : Fin n → Bool → ℕ) (G : List BGate)
    (hWF : WF N G)
    (hedge : ∀ e, edgeW e < N)
    (hmask : ∀ i b, maskW i b < N + G.length) :
    ∀ (k : ℕ) (hk : k ≤ n),
      let res := buildMatPow (j := j) (B := B) N edgeW maskW G k hk
      Extends G res.1 ∧
      res.1.length ≤ G.length + k * (2 * j * q ^ (2 * j) + 12 * B * q ^ (3 * j)) ∧
      WF N res.1 ∧
      (∀ u w, RegOK N res.1 (res.2 u w)) ∧
      ∀ src enabled mask, HasBase src N →
        (∀ e, evalW G src (edgeW e) = enabled e) →
        (∀ i b, evalW G src (maskW i b) = mask i b) →
        2 ^ n * q ^ (n * j) < 2 ^ B →
        ∀ u w, regVal res.1 src (res.2 u w) = layerMat enabled mask j k hk u w := by
  intro k
  induction k with
  | zero =>
    intro hk
    refine ⟨extends_rfl G, by simp [buildMatPow], hWF, fun u w => constReg_ok hN G _, ?_⟩
    intro src enabled mask hbase _ _ hlt u w
    simp only [buildMatPow, layerMat]
    have h1lt : 1 < 2 ^ B := by
      have hpos : 1 ≤ 2 ^ n * q ^ (n * j) :=
        Nat.mul_pos (Nat.two_pow_pos n) (Nat.pow_pos hq)
      omega
    by_cases huw : u = w
    · subst huw; simp only [ite_true]; exact constReg_val_of_lt hbase h1lt
    · simp only [huw, ite_false]; exact constReg_val_of_lt hbase (Nat.two_pow_pos B)
  | succ m ih =>
    intro hk
    have hm := ih (by omega)
    dsimp only [buildMatPow]
    set r1 := buildMatPow (j := j) (B := B) N edgeW maskW G m (by omega)
    have hmask1 : ∀ i b, maskW i b < N + r1.1.length := by
      intro i b; have := hmask i b; have := extends_len hm.1; omega
    have hl := buildLayer_spec hN hk edgeW maskW r1.1 r1.2 hm.2.2.1 hedge hmask1 hm.2.2.2.1
    refine ⟨extends_trans hm.1 hl.1, ?_, hl.2.2.1, hl.2.2.2.1, ?_⟩
    · have h1 := hm.2.1
      have h2 := hl.2.1
      have hmul : (m + 1) * (2 * j * q ^ (2 * j) + 12 * B * q ^ (3 * j)) =
          m * (2 * j * q ^ (2 * j) + 12 * B * q ^ (3 * j)) +
            (2 * j * q ^ (2 * j) + 12 * B * q ^ (3 * j)) := Nat.succ_mul m _
      omega
    · intro src enabled mask hbase hed hmk hlt u w
      have hed1 : ∀ e, evalW r1.1 src (edgeW e) = enabled e := by
        intro e
        rw [evalW_extends hm.1 (by rw [hbase.1]; have := hedge e; omega), hed e]
      have hmk1 : ∀ i b, evalW r1.1 src (maskW i b) = mask i b := by
        intro i b
        rw [evalW_extends hm.1 (by rw [hbase.1]; exact hmask i b), hmk i b]
      exact hl.2.2.2.2 src enabled mask hbase hed1 hmk1
        (hm.2.2.2.2 src enabled mask hbase hed hmk hlt) hlt u w

noncomputable def evalS {n q B : ℕ} (N : ℕ)
    (edgeW : (Fin n × Fin q × Bool × Fin q) → ℕ)
    (maskW : Fin n → Bool → ℕ) (G : List BGate) (j : ℕ) :
    List BGate × (Fin B → ℕ) :=
  let mp := buildMatPow (j := j) (B := B) N edgeW maskW G n le_rfl
  sumRegs N B mp.1 (fun u => mp.2 u u) (Finset.univ : Finset (Fin j → Fin q)).toList

lemma evalS_spec {N n q B : ℕ} (hN : 2 ≤ N) (hn : 0 < n) (hq : 0 < q)
    (edgeW : (Fin n × Fin q × Bool × Fin q) → ℕ)
    (maskW : Fin n → Bool → ℕ) (G : List BGate) (j : ℕ)
    (hWF : WF N G)
    (hedge : ∀ e, edgeW e < N)
    (hmask : ∀ i b, maskW i b < N + G.length) :
    let res := evalS (B := B) N edgeW maskW G j
    Extends G res.1 ∧
    res.1.length ≤ G.length + n * (2 * j * q ^ (2 * j) + 12 * B * q ^ (3 * j)) + 5 * B * q ^ j ∧
    WF N res.1 ∧
    RegOK N res.1 res.2 ∧
    ∀ src enabled mask, HasBase src N →
      (∀ e, evalW G src (edgeW e) = enabled e) →
      (∀ i b, evalW G src (maskW i b) = mask i b) →
      2 ^ n * q ^ (n * j) < 2 ^ B →
      regVal res.1 src res.2 = ∑ x ∈ maskWords mask, (closedPaths enabled x).card ^ j := by
  dsimp only [evalS]
  have hmp := buildMatPow_spec (j := j) (B := B) hN hq edgeW maskW G hWF hedge hmask n le_rfl
  set mp := buildMatPow (j := j) (B := B) N edgeW maskW G n le_rfl
  set uList := (Finset.univ : Finset (Fin j → Fin q)).toList
  have hsr := sumRegs_spec hN uList hmp.2.2.1 (fun u _ => hmp.2.2.2.1 u u)
  refine ⟨extends_trans hmp.1 hsr.1, ?_, hsr.2.2.1, hsr.2.2.2.1, ?_⟩
  · have h1 := hmp.2.1
    have h2 := hsr.2.1
    have hulen : uList.length = q ^ j := by simp [uList]
    rw [hulen] at h2
    omega
  · intro src enabled mask hbase hed hmk hlt
    have hsum_eq :
        (uList.map (fun u => regVal mp.1 src (mp.2 u u))).sum =
          ∑ x ∈ maskWords mask, (closedPaths enabled x).card ^ j := by
      rw [list_map_toList_sum, ← layerMat_trace_eq]
      apply Finset.sum_congr rfl
      intro u _
      exact hmp.2.2.2.2 src enabled mask hbase hed hmk hlt u u
    have hsum_lt : (uList.map (fun u => regVal mp.1 src (mp.2 u u))).sum < 2 ^ B := by
      rw [hsum_eq, ← layerMat_trace_eq]
      exact lt_of_le_of_lt (layerMat_trace_le hn enabled mask j) hlt
    rw [hsr.2.2.2.2 src hbase hsum_lt, hsum_eq]

noncomputable def buildPowList {n q B : ℕ} (N : ℕ)
    (edgeW : (Fin n × Fin q × Bool × Fin q) → ℕ)
    (maskW : Fin n → Bool → ℕ) (G : List BGate) :
    (m : ℕ) → List BGate × (Fin m → Fin B → ℕ)
  | 0 => (G, Fin.elim0)
  | m + 1 =>
    let r1 := buildPowList N edgeW maskW G m
    let r2 := evalS (B := B) N edgeW maskW r1.1 (m + 1)
    (r2.1, fun j : Fin (m + 1) => if h : j.val < m then r1.2 ⟨j.val, h⟩ else r2.2)

lemma buildPowList_spec {N n q B : ℕ} (hN : 2 ≤ N) (hn : 0 < n) (hq : 0 < q)
    (edgeW : (Fin n × Fin q × Bool × Fin q) → ℕ)
    (maskW : Fin n → Bool → ℕ) (G : List BGate)
    (hWF : WF N G)
    (hedge : ∀ e, edgeW e < N)
    (hmask : ∀ i b, maskW i b < N + G.length) :
    ∀ m : ℕ,
      let res := buildPowList (B := B) N edgeW maskW G m
      Extends G res.1 ∧
      res.1.length ≤ G.length + m * (n * (2 * m * q ^ (2 * m) + 12 * B * q ^ (3 * m)) + 5 * B * q ^ m) ∧
      WF N res.1 ∧
      (∀ j : Fin m, RegOK N res.1 (res.2 j)) ∧
      ∀ src enabled mask, HasBase src N →
        (∀ e, evalW G src (edgeW e) = enabled e) →
        (∀ i b, evalW G src (maskW i b) = mask i b) →
        (∀ j : Fin m, 2 ^ n * q ^ (n * (j.val + 1)) < 2 ^ B) →
        ∀ j : Fin m, regVal res.1 src (res.2 j) =
          ∑ x ∈ maskWords mask, (closedPaths enabled x).card ^ (j.val + 1) := by
  intro m
  induction m with
  | zero =>
    exact ⟨extends_rfl G, by simp [buildPowList], hWF, fun j => Fin.elim0 j,
      fun _ _ _ _ _ _ _ j => Fin.elim0 j⟩
  | succ k ih =>
    dsimp only [buildPowList]
    set r1 := buildPowList (B := B) N edgeW maskW G k
    have hmask1 : ∀ i b, maskW i b < N + r1.1.length := by
      intro i b; have := hmask i b; have := extends_len ih.1; omega
    have hs := evalS_spec (B := B) hN hn hq edgeW maskW r1.1 (k + 1) ih.2.2.1 hedge hmask1
    set r2 := evalS (B := B) N edgeW maskW r1.1 (k + 1)
    refine ⟨extends_trans ih.1 hs.1, ?_, hs.2.2.1, ?_, ?_⟩
    · have h1 := ih.2.1
      have h2 := hs.2.1
      have hq1 : q ^ (2 * k) ≤ q ^ (2 * (k + 1)) := Nat.pow_le_pow_right hq (by omega)
      have hq2 : q ^ (3 * k) ≤ q ^ (3 * (k + 1)) := Nat.pow_le_pow_right hq (by omega)
      have hq3 : q ^ k ≤ q ^ (k + 1) := Nat.pow_le_pow_right hq (by omega)
      have hstep_le :
          n * (2 * k * q ^ (2 * k) + 12 * B * q ^ (3 * k)) + 5 * B * q ^ k ≤
          n * (2 * (k + 1) * q ^ (2 * (k + 1)) + 12 * B * q ^ (3 * (k + 1))) + 5 * B * q ^ (k + 1) := by
        apply Nat.add_le_add
        · apply Nat.mul_le_mul_left n
          apply Nat.add_le_add
          · exact Nat.mul_le_mul (by omega) hq1
          · exact Nat.mul_le_mul_left (12 * B) hq2
        · exact Nat.mul_le_mul_left (5 * B) hq3
      have hmul_le :
          k * (n * (2 * k * q ^ (2 * k) + 12 * B * q ^ (3 * k)) + 5 * B * q ^ k) ≤
          k * (n * (2 * (k + 1) * q ^ (2 * (k + 1)) + 12 * B * q ^ (3 * (k + 1))) + 5 * B * q ^ (k + 1)) :=
        Nat.mul_le_mul_left k hstep_le
      have hsucc : (k + 1) * (n * (2 * (k + 1) * q ^ (2 * (k + 1)) + 12 * B * q ^ (3 * (k + 1))) + 5 * B * q ^ (k + 1)) =
          k * (n * (2 * (k + 1) * q ^ (2 * (k + 1)) + 12 * B * q ^ (3 * (k + 1))) + 5 * B * q ^ (k + 1)) +
          (n * (2 * (k + 1) * q ^ (2 * (k + 1)) + 12 * B * q ^ (3 * (k + 1))) + 5 * B * q ^ (k + 1)) :=
        Nat.succ_mul k _
      omega
    · intro j
      by_cases hj : j.val < k
      · simp only [hj, dite_true]; exact regOK_extends hs.1 (ih.2.2.2.1 ⟨j.val, hj⟩)
      · simp only [hj, dite_false]; exact hs.2.2.2.1
    · intro src enabled mask hbase hed hmk hlt j
      by_cases hj : j.val < k
      · simp only [hj, dite_true]
        rw [regVal_extends hs.1 hbase.1 (ih.2.2.2.1 ⟨j.val, hj⟩)]
        exact ih.2.2.2.2 src enabled mask hbase hed hmk (fun j' => hlt ⟨j'.val, by omega⟩) ⟨j.val, hj⟩
      · have hjeq : j.val = k := by omega
        simp only [hj, dite_false]
        have hed1 : ∀ e, evalW r1.1 src (edgeW e) = enabled e := by
          intro e; rw [evalW_extends ih.1 (by rw [hbase.1]; have := hedge e; omega), hed e]
        have hmk1 : ∀ i b, evalW r1.1 src (maskW i b) = mask i b := by
          intro i b; rw [evalW_extends ih.1 (by rw [hbase.1]; exact hmask i b), hmk i b]
        rw [hs.2.2.2.2 src enabled mask hbase hed1 hmk1 (by simpa [hjeq] using hlt j), hjeq]

section Elim
variable {F : Type*} [Field F] [DecidableEq F]

def relStep (A : ℕ → ℕ → F) : ℕ → ℕ → F :=
  fun i j => A (i + 1) (j + 1) - A (i + 1) 0 * (A 0 0)⁻¹ * A 0 (j + 1)

def relE : (ℕ → ℕ → F) → ℕ → ℕ → ℕ → F
  | A, 0 => A
  | A, k + 1 => relE (relStep A) k

def piv (A : ℕ → ℕ → F) (k : ℕ) : F := relE A k 0 0

def absStep (A : ℕ → ℕ → F) (k : ℕ) : ℕ → ℕ → F :=
  fun i j => A i j - A i k * (A k k)⁻¹ * A k j

def absE (A : ℕ → ℕ → F) : ℕ → ℕ → ℕ → F
  | 0 => A
  | k + 1 => absStep (absE A k) k

def sel (k i : ℕ) (s : Fin (k + 1)) : ℕ := if s.val < k then s.val else k + i

omit [DecidableEq F] in
theorem relE_succ' (A : ℕ → ℕ → F) (k : ℕ) : relE A (k + 1) = relStep (relE A k) := by
  induction k generalizing A with
  | zero => rfl
  | succ k ih => exact ih (relStep A)

omit [DecidableEq F] in
theorem det_schur {m : ℕ} (M : Matrix (Fin (m + 1)) (Fin (m + 1)) F) (h : M 0 0 ≠ 0) :
    M.det = M 0 0 * (Matrix.of fun s t : Fin m =>
      M s.succ t.succ - M s.succ 0 * (M 0 0)⁻¹ * M 0 t.succ).det := by
  let N : Matrix (Fin (m + 1)) (Fin (m + 1)) F :=
    Matrix.of fun i j => if i = 0 then M i j else M i j - M i 0 * (M 0 0)⁻¹ * M 0 j
  have hN : N.det = M.det := by
    apply Matrix.det_eq_of_forall_row_eq_smul_add_const
      (fun i => if i = 0 then 0 else -(M i 0 * (M 0 0)⁻¹)) 0 (by simp)
    intro i j
    by_cases hi : i = 0
    · simp [N, hi]
    · simp [N, hi]
      ring
  rw [← hN, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have hz : ∀ i : Fin m, N i.succ 0 = 0 := by
    intro i
    simp [N, h]
  simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
  congr 1

theorem absE_eq_relE (A : ℕ → ℕ → F) (k i j : ℕ) : absE A k (k + i) (k + j) = relE A k i j := by
  induction k generalizing i j with
  | zero => simp [absE, relE]
  | succ k ih =>
    rw [relE_succ']
    show absStep (absE A k) k (k + 1 + i) (k + 1 + j) = _
    have h1 := ih (i + 1) (j + 1)
    have h2 := ih (i + 1) 0
    have h3 := ih 0 0
    have h4 := ih 0 (j + 1)
    simp only [Nat.add_zero] at h2 h3 h4
    simp only [absStep, relStep]
    rw [show k + 1 + i = k + (i + 1) by omega, show k + 1 + j = k + (j + 1) by omega, h1, h2, h3, h4]

theorem det_sel (A : ℕ → ℕ → F) (k : ℕ) (h : ∀ l < k, piv A l ≠ 0) (i j : ℕ) :
    (Matrix.of fun s t : Fin (k + 1) => A (sel k i s) (sel k j t)).det =
      (∏ l ∈ Finset.range k, piv A l) * relE A k i j := by
  induction k generalizing A i j with
  | zero =>
    rw [Matrix.det_fin_one]
    simp [sel, relE]
  | succ k ih =>
    have h0 : piv A 0 ≠ 0 := h 0 (by omega)
    have hs0 : ∀ i, sel (k + 1) i 0 = 0 := fun i => by simp [sel]
    have hss : ∀ i (s : Fin (k + 1)), sel (k + 1) i s.succ = sel k i s + 1 := by
      intro i s
      simp only [sel, Fin.val_succ]
      split_ifs <;> omega
    rw [det_schur _ (by simp only [Matrix.of_apply, hs0]; exact h0)]
    have hm : (Matrix.of fun s t : Fin (k + 1) =>
        (Matrix.of fun s t : Fin (k + 1 + 1) => A (sel (k + 1) i s) (sel (k + 1) j t)) s.succ t.succ -
        (Matrix.of fun s t : Fin (k + 1 + 1) => A (sel (k + 1) i s) (sel (k + 1) j t)) s.succ 0 *
        ((Matrix.of fun s t : Fin (k + 1 + 1) => A (sel (k + 1) i s) (sel (k + 1) j t)) 0 0)⁻¹ *
        (Matrix.of fun s t : Fin (k + 1 + 1) => A (sel (k + 1) i s) (sel (k + 1) j t)) 0 t.succ) =
        Matrix.of fun s t : Fin (k + 1) => relStep A (sel k i s) (sel k j t) := by
      ext s t
      simp [hs0, hss, relStep]
    rw [hm, ih (relStep A) (fun l hl => h (l + 1) (by omega)) i j, Finset.prod_range_succ']
    simp only [Matrix.of_apply, hs0]
    show _ = _ * relE (relStep A) k i j
    have : ∀ l, piv (relStep A) l = piv A (l + 1) := fun l => rfl
    simp only [this]
    rw [show A 0 0 = piv A 0 from rfl]
    ring

theorem det_lead (A : ℕ → ℕ → F) (k : ℕ) (h : ∀ l < k, piv A l ≠ 0) :
    (Matrix.of fun s t : Fin k => A s.val t.val).det = ∏ l ∈ Finset.range k, piv A l := by
  cases k with
  | zero => simp
  | succ k =>
    have hm : (Matrix.of fun s t : Fin (k + 1) => A s.val t.val) =
        Matrix.of fun s t : Fin (k + 1) => A (sel k 0 s) (sel k 0 t) := by
      have hsel : ∀ s : Fin (k + 1), sel k 0 s = s.val := by
        intro s
        have := s.isLt
        simp only [sel]
        split_ifs <;> omega
      ext s t
      simp [hsel]
    rw [hm, det_sel A k (fun l hl => h l (by omega)) 0 0, Finset.prod_range_succ]
    rfl

def stepS (k : ℕ) (st : (ℕ → ℕ → F) × F × Bool) : (ℕ → ℕ → F) × F × Bool :=
  if st.2.2 = false ∧ st.1 k k ≠ 0 then (absStep st.1 k, st.2.1 * st.1 k k, false)
  else (st.1, st.2.1, true)

def runS (A : ℕ → ℕ → F) : ℕ → (ℕ → ℕ → F) × F × Bool
  | 0 => (A, 1, false)
  | k + 1 => stepS k (runS A k)

theorem runS_spec (A : ℕ → ℕ → F) (K : ℕ) :
    ∃ r ≤ K, (∀ l < r, piv A l ≠ 0) ∧ (r < K → piv A r = 0) ∧
      runS A K = (absE A r, ∏ l ∈ Finset.range r, piv A l, decide (r < K)) := by
  induction K with
  | zero => exact ⟨0, le_refl _, by simp, by simp, by simp [runS, absE]⟩
  | succ K ih =>
    obtain ⟨r, hr, hp, hz, hrun⟩ := ih
    rcases Nat.lt_or_ge r K with hlt | hge
    · refine ⟨r, by omega, hp, fun _ => hz hlt, ?_⟩
      show stepS K (runS A K) = _
      rw [hrun]
      simp [stepS, hlt, show r < K + 1 by omega]
    · have hrK : r = K := by omega
      subst hrK
      have hkk : absE A r r r = piv A r := by
        have := absE_eq_relE A r 0 0
        simpa [piv] using this
      by_cases hpz : piv A r = 0
      · refine ⟨r, by omega, hp, fun _ => hpz, ?_⟩
        show stepS r (runS A r) = _
        rw [hrun]
        simp [stepS, hkk, hpz]
      · refine ⟨r + 1, le_refl _, ?_, by omega, ?_⟩
        · intro l hl
          rcases Nat.lt_or_ge l r with h1 | h1
          · exact hp l h1
          · rw [show l = r by omega]; exact hpz
        · show stepS r (runS A r) = _
          rw [hrun]
          simp [stepS, hkk, hpz, Finset.prod_range_succ, absE]

end Elim

section Problem
variable {X : Type*} [Fintype X] [DecidableEq X]

def mom (mult : X → ℕ) (j : ℕ) : ℕ := ∑ x, mult x ^ j

def Ghat (mult : X → ℕ) (d : ℕ) (s t : ℕ) : ℤ :=
  if s < d then (if t < d then (mom mult (s + t + 2) : ℤ) else (mom mult (s + 1) : ℤ))
  else (if t < d then (mom mult (t + 1) : ℤ) else 0)

def Hone (mult : X → ℕ) (s t : ℕ) : ℤ := (mom mult (s + t + 1) : ℤ)

def fitQ (mult : X → ℕ) (d : ℕ) (coeff : Fin d → ℚ) : ℚ :=
  ∑ x, (2 * (∑ t : Fin d, coeff t * (mult x : ℚ) ^ (t.val + 1)) -
    (∑ t : Fin d, coeff t * (mult x : ℚ) ^ (t.val + 1)) ^ 2)

def wordsF (mult : X → ℕ) : Finset X := Finset.univ.filter (fun x => 0 < mult x)

def levelsN (mult : X → ℕ) : ℕ := ((wordsF mult).image mult).card

section OptPart
open Matrix Finset Polynomial

lemma mom_cast (mult : X → ℕ) (j : ℕ) : (mom mult j : ℚ) = ∑ x, (mult x : ℚ) ^ j := by
  simp [mom]

lemma hank_mulVec (mult : X → ℕ) (a k : ℕ) (v : Fin k → ℚ) (s : Fin k) :
    ((Matrix.of fun s t : Fin k => (mom mult (s.val + t.val + a) : ℚ)) *ᵥ v) s =
      ∑ x, (mult x : ℚ) ^ (s.val + a) * ∑ t : Fin k, v t * (mult x : ℚ) ^ t.val := by
  simp only [mulVec, dotProduct, of_apply, mom_cast, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun t _ => ?_
  ring

lemma hank_quad (mult : X → ℕ) (a k : ℕ) (v : Fin k → ℚ) :
    v ⬝ᵥ ((Matrix.of fun s t : Fin k => (mom mult (s.val + t.val + a) : ℚ)) *ᵥ v) =
      ∑ x, (mult x : ℚ) ^ a * (∑ t : Fin k, v t * (mult x : ℚ) ^ t.val) ^ 2 := by
  simp only [dotProduct, hank_mulVec]
  conv_lhs => arg 2; ext s; rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h : ∑ s : Fin k, v s * ((mult x : ℚ) ^ (s.val + a) * ∑ t : Fin k, v t * (mult x : ℚ) ^ t.val)
      = (∑ s : Fin k, v s * (mult x : ℚ) ^ s.val) *
        ((mult x : ℚ) ^ a * ∑ t : Fin k, v t * (mult x : ℚ) ^ t.val) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [h]
  ring

lemma levels_le_natDegree (mult : X → ℕ) (P : ℚ[X]) (hP : P ≠ 0)
    (hroot : ∀ x, 0 < mult x → P.eval (mult x : ℚ) = 0) : levelsN mult ≤ P.natDegree := by
  unfold levelsN
  have h1 : (((wordsF mult).image mult).image (fun n : ℕ => (n : ℚ))).card =
      ((wordsF mult).image mult).card :=
    Finset.card_image_of_injective _ Nat.cast_injective
  have h2 : ((wordsF mult).image mult).image (fun n : ℕ => (n : ℚ)) ⊆ P.roots.toFinset := by
    intro q hq
    simp only [Finset.mem_image, wordsF, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    obtain ⟨n, ⟨x, hx, rfl⟩, rfl⟩ := hq
    simp [Multiset.mem_toFinset, mem_roots hP, hroot x hx]
  rw [← h1]
  exact (Finset.card_le_card h2).trans ((Multiset.toFinset_card_le _).trans (card_roots' P))

lemma pos_of_mem_levels (mult : X → ℕ) {l : ℕ} (hl : l ∈ (wordsF mult).image mult) : 0 < l := by
  simp only [Finset.mem_image, wordsF, Finset.mem_filter, Finset.mem_univ, true_and] at hl
  obtain ⟨x, hx, rfl⟩ := hl
  exact hx

lemma mem_levels (mult : X → ℕ) {x : X} (hx : 0 < mult x) : mult x ∈ (wordsF mult).image mult := by
  simp only [Finset.mem_image, wordsF, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨x, hx, rfl⟩

noncomputable def Qp (mult : X → ℕ) : ℚ[X] := ∏ l ∈ (wordsF mult).image mult, (Polynomial.X - C (l : ℚ))

lemma Qp_monic (mult : X → ℕ) : (Qp mult).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

lemma Qp_natDegree (mult : X → ℕ) : (Qp mult).natDegree = levelsN mult := by
  rw [Qp, natDegree_finsetProd_X_sub_C_eq_card]
  rfl

lemma Qp_eval (mult : X → ℕ) (x : X) (hx : 0 < mult x) : (Qp mult).eval (mult x : ℚ) = 0 := by
  rw [Qp, eval_prod]
  exact Finset.prod_eq_zero (mem_levels mult hx) (by simp)

lemma Qp_eval_zero (mult : X → ℕ) : (Qp mult).eval 0 ≠ 0 := by
  rw [Qp, eval_prod]
  refine Finset.prod_ne_zero_iff.2 fun l hl => ?_
  have := pos_of_mem_levels mult hl
  simp only [eval_sub, eval_X, eval_C, zero_sub, neg_ne_zero]
  exact_mod_cast this.ne'

lemma polyFin_eval (k : ℕ) (v : Fin k → ℚ) (y : ℚ) :
    (∑ t : Fin k, C (v t) * Polynomial.X ^ t.val).eval y = ∑ t : Fin k, v t * y ^ t.val := by
  simp [eval_finsetSum]

lemma polyFin_coeff (k : ℕ) (v : Fin k → ℚ) (t0 : Fin k) :
    (∑ t : Fin k, C (v t) * Polynomial.X ^ t.val).coeff t0.val = v t0 := by
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single t0]
  · simp
  · intro b _ hb
    rw [ite_eq_right_iff]
    intro h
    exact absurd (Fin.ext h.symm) hb
  · simp

lemma polyFin_natDegree (k : ℕ) (v : Fin k → ℚ) :
    (∑ t : Fin k, C (v t) * Polynomial.X ^ t.val).natDegree ≤ k - 1 := by
  refine natDegree_sum_le_of_forall_le _ _ fun t _ => ?_
  exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)

lemma eval_as_fin (P : ℚ[X]) (k : ℕ) (hk : P.natDegree < k) (y : ℚ) :
    ∑ t : Fin k, P.coeff t.val * y ^ t.val = P.eval y := by
  rw [eval_eq_sum_range' hk, Fin.sum_univ_eq_sum_range (fun j => P.coeff j * y ^ j) k]

theorem hankel_det_zero_iff (mult : X → ℕ) (a k : ℕ) (ha : 1 ≤ a) :
    (Matrix.of fun s t : Fin k => (mom mult (s.val + t.val + a) : ℚ)).det = 0 ↔
      levelsN mult < k := by
  rw [← exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨v, hv, hH⟩
    have hq := hank_quad mult a k v
    rw [hH, dotProduct_zero, eq_comm] at hq
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => by positivity)).1 hq
    obtain ⟨t0, ht0⟩ := Function.ne_iff.1 hv
    have hP : (∑ t : Fin k, C (v t) * Polynomial.X ^ t.val) ≠ 0 := by
      intro h0
      have := polyFin_coeff k v t0
      rw [h0, coeff_zero] at this
      exact ht0 this.symm
    have hle := levels_le_natDegree mult _ hP (fun x hx => by
      rw [polyFin_eval]
      have h1 := hterm x (Finset.mem_univ _)
      have h2 : (mult x : ℚ) ^ a ≠ 0 := pow_ne_zero _ (by exact_mod_cast hx.ne')
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ((mul_eq_zero.1 h1).resolve_left h2))
    have := polyFin_natDegree k v
    have := t0.isLt
    omega
  · intro hk
    have hdeg : (Qp mult).natDegree < k := by rw [Qp_natDegree]; exact hk
    refine ⟨fun t => (Qp mult).coeff t.val, ?_, ?_⟩
    · intro h
      have := congrFun h ⟨levelsN mult, hk⟩
      simp only [Pi.zero_apply] at this
      rw [← Qp_natDegree] at this
      exact (Qp_monic mult).ne_zero (leadingCoeff_eq_zero.1 this)
    · funext s
      rw [hank_mulVec]
      simp only [Pi.zero_apply]
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [eval_as_fin _ k hdeg]
      by_cases hx : 0 < mult x
      · rw [Qp_eval mult x hx, mul_zero]
      · have : mult x = 0 := by omega
        rw [this]
        simp
        omega

theorem gram_det_pos (mult : X → ℕ) (r : ℕ)
    (hdet : (Matrix.of fun s t : Fin r => (mom mult (s.val + t.val + 2) : ℚ)).det ≠ 0) :
    0 < (Matrix.of fun s t : Fin r => (mom mult (s.val + t.val + 2) : ℚ)).det := by
  refine PosDef.det_pos (PosDef.of_dotProduct_mulVec_pos ?_ ?_)
  · ext s t
    simp only [conjTranspose_apply, of_apply, star_trivial]
    rw [Nat.add_comm t.val s.val]
  · intro v hv
    rw [star_trivial, hank_quad]
    refine lt_of_le_of_ne (Finset.sum_nonneg fun x _ => by positivity) ?_
    intro hq
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => by positivity)).1 hq.symm
    apply hv
    by_contra hne
    apply hdet
    rw [← exists_mulVec_eq_zero_iff]
    refine ⟨v, hne, ?_⟩
    funext s
    rw [hank_mulVec]
    refine Finset.sum_eq_zero fun x _ => ?_
    have h1 := hterm x (Finset.mem_univ _)
    have h2 : (mult x : ℚ) * ∑ t : Fin r, v t * (mult x : ℚ) ^ t.val = 0 := by
      have : ((mult x : ℚ) * ∑ t : Fin r, v t * (mult x : ℚ) ^ t.val) ^ 2 = 0 := by
        rw [← h1]; ring
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    calc (mult x : ℚ) ^ (s.val + 2) * ∑ t : Fin r, v t * (mult x : ℚ) ^ t.val
        = (mult x : ℚ) ^ (s.val + 1) * ((mult x : ℚ) * ∑ t : Fin r, v t * (mult x : ℚ) ^ t.val) := by
          ring
      _ = 0 := by rw [h2, mul_zero]

def zf (mult : X → ℕ) (x : X) : ℚ := if 0 < mult x then 1 else 0

def Yf (mult : X → ℕ) (u : ℕ → ℚ) (n : ℕ) (x : X) : ℚ :=
  ∑ j ∈ range n, u j * (mult x : ℚ) ^ (j + 1)

def extF {d : ℕ} (c : Fin d → ℚ) (j : ℕ) : ℚ := if h : j < d then c ⟨j, h⟩ else 0

lemma Yf_zero (mult : X → ℕ) (u : ℕ → ℚ) (n : ℕ) (x : X) (h : mult x = 0) : Yf mult u n x = 0 := by
  simp [Yf, h]

lemma fitQ_eq (mult : X → ℕ) (d : ℕ) (u : ℕ → ℚ) :
    fitQ mult d (fun t => u t.val) = ∑ x, (2 * Yf mult u d x - (Yf mult u d x) ^ 2) := by
  unfold fitQ Yf
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fin.sum_univ_eq_sum_range (fun j => u j * (mult x : ℚ) ^ (j + 1)) d]

lemma fitQ_ext (mult : X → ℕ) (d : ℕ) (c : Fin d → ℚ) :
    fitQ mult d c = ∑ x, (2 * Yf mult (extF c) d x - (Yf mult (extF c) d x) ^ 2) := by
  rw [← fitQ_eq]
  congr 1
  funext t
  simp [extF, t.isLt]

lemma card_eq_sum_zf (mult : X → ℕ) : ((wordsF mult).card : ℚ) = ∑ x, zf mult x := by
  simp only [zf, Finset.sum_boole, wordsF]

lemma fit_formula (mult : X → ℕ) (u : ℕ → ℚ) (n : ℕ) :
    ∑ x, (2 * Yf mult u n x - (Yf mult u n x) ^ 2) =
      ((wordsF mult).card : ℚ) - ∑ x, (zf mult x - Yf mult u n x) ^ 2 := by
  rw [card_eq_sum_zf, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : 0 < mult x
  · simp only [zf, if_pos hx]; ring
  · have h0 : mult x = 0 := by omega
    simp only [zf, if_neg hx, Yf_zero mult u n x h0]; ring

lemma Yf_of_poly (mult : X → ℕ) (P : ℚ[X]) (n : ℕ) (hd : P.natDegree ≤ n) (h0 : P.eval 0 = 0)
    (x : X) : Yf mult (fun j => P.coeff (j + 1)) n x = P.eval (mult x : ℚ) := by
  rw [eval_eq_sum_range' (n := n + 1) (by omega), Finset.sum_range_succ',
    coeff_zero_eq_eval_zero, h0]
  simp [Yf]

lemma interp (mult : X → ℕ) (n : ℕ) (hn : levelsN mult ≤ n) :
    ∃ u : ℕ → ℚ, ∀ x, Yf mult u n x = zf mult x := by
  set P : ℚ[X] := 1 - C ((Qp mult).eval 0)⁻¹ * Qp mult with hP
  have hd : P.natDegree ≤ n := by
    refine (natDegree_sub_le _ _).trans ?_
    rw [natDegree_one]
    refine max_le (Nat.zero_le _) ((natDegree_C_mul_le _ _).trans ?_)
    rw [Qp_natDegree]; exact hn
  have h0 : P.eval 0 = 0 := by
    rw [hP, eval_sub, eval_one, eval_mul, eval_C, inv_mul_cancel₀ (Qp_eval_zero mult), sub_self]
  refine ⟨fun j => P.coeff (j + 1), fun x => ?_⟩
  rw [Yf_of_poly mult P n hd h0]
  by_cases hx : 0 < mult x
  · rw [hP, eval_sub, eval_one, eval_mul, Qp_eval mult x hx, mul_zero, sub_zero, zf, if_pos hx]
  · have : mult x = 0 := by omega
    rw [zf, if_neg hx, this, Nat.cast_zero, h0]

lemma Yf_sub (mult : X → ℕ) (u v : ℕ → ℚ) (n : ℕ) (x : X) :
    Yf mult u n x - Yf mult v n x = Yf mult (u - v) n x := by
  simp [Yf, sub_mul, Finset.sum_sub_distrib]

def crN {r : ℕ} (cr : Fin r → ℚ) (j : ℕ) : ℚ := if h : j < r then cr ⟨j, h⟩ else 0

lemma Ys_fin (mult : X → ℕ) {r : ℕ} (cr : Fin r → ℚ) (x : X) :
    Yf mult (crN cr) r x = ∑ t : Fin r, cr t * (mult x : ℚ) ^ (t.val + 1) := by
  rw [Yf, ← Fin.sum_univ_eq_sum_range (fun j => crN cr j * (mult x : ℚ) ^ (j + 1)) r]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp [crN, t.isLt]

lemma Ys_extend (mult : X → ℕ) {r d : ℕ} (hr : r ≤ d) (cr : Fin r → ℚ) (x : X) :
    Yf mult (crN cr) d x = Yf mult (crN cr) r x := by
  unfold Yf
  refine (Finset.sum_subset (Finset.range_subset_range.2 hr) fun j _ hj => ?_).symm
  simp only [Finset.mem_range] at hj
  simp [crN, hj]

lemma normal_eq (mult : X → ℕ) {r : ℕ} (cr : Fin r → ℚ)
    (hcr : (Matrix.of fun s t : Fin r => (mom mult (s.val + t.val + 2) : ℚ)) *ᵥ cr =
      fun s : Fin r => (mom mult (s.val + 1) : ℚ)) (j : ℕ) (hj : j < r) :
    ∑ x, (mult x : ℚ) ^ (j + 1) * (zf mult x - Yf mult (crN cr) r x) = 0 := by
  have h := congrFun hcr ⟨j, hj⟩
  rw [hank_mulVec, mom_cast] at h
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [sub_eq_zero]
  have e1 : ∑ x, (mult x : ℚ) ^ (j + 1) * zf mult x = ∑ x, (mult x : ℚ) ^ (j + 1) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : 0 < mult x
    · simp [zf, hx]
    · have : mult x = 0 := by omega
      simp [zf, this]
  rw [e1, ← h]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Ys_fin, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only
  ring

lemma orth_gen (mult : X → ℕ) (r : ℕ) (w : X → ℚ)
    (hw : ∀ j < r, ∑ x, (mult x : ℚ) ^ (j + 1) * w x = 0) (u : ℕ → ℚ) (n : ℕ) (hn : n ≤ r) :
    ∑ x, Yf mult u n x * w x = 0 := by
  simp only [Yf, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j hj => ?_
  simp only [Finset.mem_range] at hj
  have : ∑ x, u j * (mult x : ℚ) ^ (j + 1) * w x = u j * ∑ x, (mult x : ℚ) ^ (j + 1) * w x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [this, hw j (by omega), mul_zero]

lemma normal_orth (mult : X → ℕ) {r : ℕ} (cr : Fin r → ℚ)
    (hcr : (Matrix.of fun s t : Fin r => (mom mult (s.val + t.val + 2) : ℚ)) *ᵥ cr =
      fun s : Fin r => (mom mult (s.val + 1) : ℚ)) (u : ℕ → ℚ) (n : ℕ) (hn : n ≤ r) :
    ∑ x, Yf mult u n x * (zf mult x - Yf mult (crN cr) r x) = 0 :=
  orth_gen mult r (fun x => zf mult x - Yf mult (crN cr) r x) (normal_eq mult cr hcr) u n hn

lemma V_eq_sumYs (mult : X → ℕ) {r : ℕ} (cr : Fin r → ℚ) :
    (fun s : Fin r => (mom mult (s.val + 1) : ℚ)) ⬝ᵥ cr = ∑ x, Yf mult (crN cr) r x := by
  simp only [dotProduct, mom_cast, Finset.sum_mul, Ys_fin]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun t _ => ?_
  ring

lemma sumYs2 (mult : X → ℕ) {r : ℕ} (cr : Fin r → ℚ)
    (hcr : (Matrix.of fun s t : Fin r => (mom mult (s.val + t.val + 2) : ℚ)) *ᵥ cr =
      fun s : Fin r => (mom mult (s.val + 1) : ℚ)) :
    ∑ x, (Yf mult (crN cr) r x) ^ 2 = (fun s : Fin r => (mom mult (s.val + 1) : ℚ)) ⬝ᵥ cr := by
  have h := normal_orth mult cr hcr (crN cr) r le_rfl
  rw [V_eq_sumYs]
  have e : ∀ x, Yf mult (crN cr) r x * (zf mult x - Yf mult (crN cr) r x) =
      Yf mult (crN cr) r x - (Yf mult (crN cr) r x) ^ 2 := by
    intro x
    by_cases hx : 0 < mult x
    · simp only [zf, hx, if_true]; ring
    · have h0 : mult x = 0 := by omega
      simp [Yf_zero mult _ r x h0]
  simp only [e, Finset.sum_sub_distrib] at h
  linarith

lemma fit_star (mult : X → ℕ) {r d : ℕ} (hr : r ≤ d) (cr : Fin r → ℚ)
    (hcr : (Matrix.of fun s t : Fin r => (mom mult (s.val + t.val + 2) : ℚ)) *ᵥ cr =
      fun s : Fin r => (mom mult (s.val + 1) : ℚ)) :
    fitQ mult d (fun t => crN cr t.val) = (fun s : Fin r => (mom mult (s.val + 1) : ℚ)) ⬝ᵥ cr := by
  rw [fitQ_eq]
  simp only [Ys_extend mult hr cr]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sumYs2 mult cr hcr, ← V_eq_sumYs]
  ring

lemma E_le (mult : X → ℕ) {r d : ℕ} (hr : r ≤ d) (cr : Fin r → ℚ)
    (hcr : (Matrix.of fun s t : Fin r => (mom mult (s.val + t.val + 2) : ℚ)) *ᵥ cr =
      fun s : Fin r => (mom mult (s.val + 1) : ℚ))
    (hstop : r < d → levelsN mult ≤ r) (u : ℕ → ℚ) :
    ∑ x, (zf mult x - Yf mult (crN cr) r x) ^ 2 ≤ ∑ x, (zf mult x - Yf mult u d x) ^ 2 := by
  rcases hr.lt_or_eq with hlt | heq
  · obtain ⟨u0, hu0⟩ := interp mult r (hstop hlt)
    have h1 := normal_orth mult cr hcr u0 r le_rfl
    have h2 := normal_orth mult cr hcr (crN cr) r le_rfl
    have e : ∑ x, (zf mult x - Yf mult (crN cr) r x) ^ 2 = 0 := by
      have : ∀ x, (zf mult x - Yf mult (crN cr) r x) ^ 2 =
          Yf mult u0 r x * (zf mult x - Yf mult (crN cr) r x) -
            Yf mult (crN cr) r x * (zf mult x - Yf mult (crN cr) r x) := by
        intro x; rw [hu0]; ring
      simp only [this, Finset.sum_sub_distrib, h1, h2, sub_zero]
    rw [e]
    exact Finset.sum_nonneg fun x _ => sq_nonneg _
  · subst heq
    have h1 := normal_orth mult cr hcr (crN cr - u) r le_rfl
    have : ∀ x, (zf mult x - Yf mult u r x) ^ 2 = (zf mult x - Yf mult (crN cr) r x) ^ 2 +
        (Yf mult (crN cr - u) r x) ^ 2 +
          2 * (Yf mult (crN cr - u) r x * (zf mult x - Yf mult (crN cr) r x)) := by
      intro x; rw [← Yf_sub]; ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, h1, mul_zero, add_zero]
    have := Finset.sum_nonneg fun x (_ : x ∈ (Finset.univ : Finset X)) =>
      sq_nonneg (Yf mult (crN cr - u) r x)
    linarith

lemma levels_of_exact (mult : X → ℕ) {r : ℕ} (cr : Fin r → ℚ)
    (h : ∀ x, 0 < mult x → Yf mult (crN cr) r x = 1) : levelsN mult ≤ r := by
  set R : ℚ[X] := 1 - ∑ j ∈ range r, C (crN cr j) * Polynomial.X ^ (j + 1) with hR
  have hne : R ≠ 0 := by
    intro h0
    have := congrArg (fun p : ℚ[X] => p.coeff 0) h0
    simp only [hR, coeff_sub, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
    simp at this
  have hdeg : R.natDegree ≤ r := by
    refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
    refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
    simp only [Finset.mem_range] at hj
    exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
  refine (levels_le_natDegree mult R hne fun x hx => ?_).trans hdeg
  have := h x hx
  simp only [hR, eval_sub, eval_one, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  rw [← this, Yf]
  ring

lemma opt_core (mult : X → ℕ) (d r : ℕ) (hr : r ≤ d) (cr : Fin r → ℚ)
    (hcr : (Matrix.of fun s t : Fin r => (mom mult (s.val + t.val + 2) : ℚ)) *ᵥ cr =
      fun s : Fin r => (mom mult (s.val + 1) : ℚ))
    (hstop : r < d → levelsN mult ≤ r) :
    0 ≤ (fun s : Fin r => (mom mult (s.val + 1) : ℚ)) ⬝ᵥ cr ∧
    (∀ coeff, fitQ mult d coeff ≤ (fun s : Fin r => (mom mult (s.val + 1) : ℚ)) ⬝ᵥ cr) ∧
    (∃ coeff, fitQ mult d coeff = (fun s : Fin r => (mom mult (s.val + 1) : ℚ)) ⬝ᵥ cr) ∧
    (fun s : Fin r => (mom mult (s.val + 1) : ℚ)) ⬝ᵥ cr ≤ ((wordsF mult).card : ℚ) ∧
    ((fun s : Fin r => (mom mult (s.val + 1) : ℚ)) ⬝ᵥ cr = ((wordsF mult).card : ℚ) ↔
      levelsN mult ≤ d) := by
  have hfs := fit_star mult hr cr hcr
  have hV : fitQ mult d (fun t => crN cr t.val) =
      ((wordsF mult).card : ℚ) - ∑ x, (zf mult x - Yf mult (crN cr) r x) ^ 2 := by
    rw [fitQ_eq, fit_formula]
    simp only [Ys_extend mult hr cr]
  have hE0 : 0 ≤ ∑ x, (zf mult x - Yf mult (crN cr) r x) ^ 2 :=
    Finset.sum_nonneg fun x _ => sq_nonneg _
  refine ⟨?_, ?_, ⟨_, hfs⟩, ?_, ?_⟩
  · rw [← sumYs2 mult cr hcr]
    exact Finset.sum_nonneg fun x _ => sq_nonneg _
  · intro c
    rw [← hfs, hV, fitQ_ext, fit_formula]
    have := E_le mult hr cr hcr hstop (extF c)
    linarith
  · rw [← hfs, hV]; linarith
  · constructor
    · intro heq
      rw [← hfs, hV] at heq
      have hE : ∑ x, (zf mult x - Yf mult (crN cr) r x) ^ 2 = 0 := by linarith
      have ht := (Finset.sum_eq_zero_iff_of_nonneg fun x _ => sq_nonneg _).1 hE
      refine (levels_of_exact mult cr fun x hx => ?_).trans hr
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (ht x (Finset.mem_univ _))
      rw [zf, if_pos hx] at this
      linarith
    · intro hl
      obtain ⟨u0, hu0⟩ := interp mult d hl
      have h1 := E_le mult hr cr hcr hstop u0
      simp only [hu0, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        Finset.sum_const_zero] at h1
      rw [← hfs, hV]
      linarith

theorem opt_thm (mult : X → ℕ) (d r : ℕ) (hr : r ≤ d)
    (hdet : (Matrix.of fun s t : Fin r => (mom mult (s.val + t.val + 2) : ℚ)).det ≠ 0)
    (hstop : r < d → levelsN mult ≤ r) :
    0 ≤ dotProduct (fun s : Fin r => (mom mult (s.val + 1) : ℚ))
        (Matrix.mulVec (Matrix.of fun s t : Fin r => (mom mult (s.val + t.val + 2) : ℚ))⁻¹
          (fun s : Fin r => (mom mult (s.val + 1) : ℚ))) ∧
    (∀ coeff, fitQ mult d coeff ≤ dotProduct (fun s : Fin r => (mom mult (s.val + 1) : ℚ))
        (Matrix.mulVec (Matrix.of fun s t : Fin r => (mom mult (s.val + t.val + 2) : ℚ))⁻¹
          (fun s : Fin r => (mom mult (s.val + 1) : ℚ)))) ∧
    (∃ coeff, fitQ mult d coeff = dotProduct (fun s : Fin r => (mom mult (s.val + 1) : ℚ))
        (Matrix.mulVec (Matrix.of fun s t : Fin r => (mom mult (s.val + t.val + 2) : ℚ))⁻¹
          (fun s : Fin r => (mom mult (s.val + 1) : ℚ)))) ∧
    dotProduct (fun s : Fin r => (mom mult (s.val + 1) : ℚ))
        (Matrix.mulVec (Matrix.of fun s t : Fin r => (mom mult (s.val + t.val + 2) : ℚ))⁻¹
          (fun s : Fin r => (mom mult (s.val + 1) : ℚ))) ≤ ((wordsF mult).card : ℚ) ∧
    (dotProduct (fun s : Fin r => (mom mult (s.val + 1) : ℚ))
        (Matrix.mulVec (Matrix.of fun s t : Fin r => (mom mult (s.val + t.val + 2) : ℚ))⁻¹
          (fun s : Fin r => (mom mult (s.val + 1) : ℚ))) = ((wordsF mult).card : ℚ) ↔
      levelsN mult ≤ d) := by
  refine opt_core mult d r hr _ ?_ hstop
  rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), one_mulVec]

end OptPart

lemma b_sel_castSucc (k i : ℕ) (s : Fin k) : sel k i (Fin.castSucc s) = s.val := by
  simp [sel]

lemma b_sel_last (k i : ℕ) : sel k i (Fin.last k) = k + i := by
  simp [sel]

lemma b_sel_zero (k : ℕ) (s : Fin (k + 1)) : sel k 0 s = s.val := by
  unfold sel
  split_ifs with h
  · rfl
  · have := s.isLt
    omega

lemma b_sel_le (k i d : ℕ) (h : k + i ≤ d) (s : Fin (k + 1)) : sel k i s ≤ d := by
  unfold sel
  split_ifs with h'
  · omega
  · omega

lemma b_det_cast {R : Type*} [CommRing R] {n : ℕ} (f : Fin n → Fin n → ℤ) :
    (Matrix.of fun s t => ((f s t : ℤ) : R)).det = (((Matrix.of f).det : ℤ) : R) :=
  ((Int.castRingHom R).map_det (Matrix.of f)).symm

lemma b_det_abs {n d w p : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hn : n ≤ d + 1)
    (hM : ∀ s t, |M s t| ≤ 2 ^ w) (hp : (d + 1).factorial * (2 ^ w) ^ (d + 1) < p) :
    |M.det| < p := by
  have h1 := Matrix.det_le (abv := AbsoluteValue.abs) (x := (2 : ℤ) ^ w)
    (fun s t => by rw [AbsoluteValue.abs_apply]; exact hM s t)
  rw [AbsoluteValue.abs_apply] at h1
  simp only [Fintype.card_fin, nsmul_eq_mul] at h1
  have h2 : (n.factorial : ℤ) * ((2 : ℤ) ^ w) ^ n ≤
      ((d + 1).factorial : ℤ) * ((2 : ℤ) ^ w) ^ (d + 1) := by
    apply mul_le_mul
    · exact_mod_cast Nat.factorial_le hn
    · exact pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hn
    · positivity
    · positivity
  have h3 : ((d + 1).factorial : ℤ) * ((2 : ℤ) ^ w) ^ (d + 1) < p := by exact_mod_cast hp
  exact lt_of_le_of_lt (le_trans h1 h2) h3

lemma b_cast_zero_iff {p : ℕ} (D : ℤ) (h : |D| < p) : ((D : ZMod p) = 0 ↔ D = 0) := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · intro hd
    exact Int.eq_zero_of_abs_lt_dvd hd h
  · intro hd
    rw [hd]
    exact dvd_zero _

lemma b_val_cast {p : ℕ} [NeZero p] (D : ℤ) (h0 : 0 ≤ D) (h : D < p) :
    (((D : ZMod p).val : ℕ) : ℚ) = (D : ℚ) := by
  have h1 := ZMod.val_intCast (n := p) D
  rw [Int.emod_eq_of_lt h0 h] at h1
  calc (((D : ZMod p).val : ℕ) : ℚ) = ((((D : ZMod p).val : ℕ) : ℤ) : ℚ) :=
        (Int.cast_natCast _).symm
    _ = (D : ℚ) := by rw [h1]

lemma b_mom_abs (mult : X → ℕ) (d w j : ℕ) (hw : ∀ j ≤ 2 * d + 1, mom mult j < 2 ^ w)
    (hj : j ≤ 2 * d + 1) : |(mom mult j : ℤ)| ≤ 2 ^ w := by
  rw [abs_of_nonneg (by positivity)]
  exact_mod_cast (hw j hj).le

lemma b_ghat_abs (mult : X → ℕ) (d w : ℕ) (hw : ∀ j ≤ 2 * d + 1, mom mult j < 2 ^ w)
    (s t : ℕ) (hs : s ≤ d) (ht : t ≤ d) : |Ghat mult d s t| ≤ 2 ^ w := by
  unfold Ghat
  split_ifs
  · exact b_mom_abs mult d w _ hw (by omega)
  · exact b_mom_abs mult d w _ hw (by omega)
  · exact b_mom_abs mult d w _ hw (by omega)
  · rw [abs_zero]
    positivity

lemma b_hankel_q (mult : X → ℕ) (n a : ℕ) :
    (Matrix.of fun s t : Fin n => (mom mult (s.val + t.val + a) : ℚ)).det =
      (((Matrix.of fun s t : Fin n => (mom mult (s.val + t.val + a) : ℤ)).det : ℤ) : ℚ) := by
  rw [← b_det_cast]
  simp only [Int.cast_natCast]

lemma b_hankel_abs (mult : X → ℕ) (d w p n a : ℕ) (hw : ∀ j ≤ 2 * d + 1, mom mult j < 2 ^ w)
    (hp : (d + 1).factorial * (2 ^ w) ^ (d + 1) < p) (hn : n ≤ d + 1)
    (hb : 2 * n + a ≤ 2 * d + 3) :
    |(Matrix.of fun s t : Fin n => (mom mult (s.val + t.val + a) : ℤ)).det| < p := by
  apply b_det_abs _ hn _ hp
  intro s t
  have := s.isLt
  have := t.isLt
  exact b_mom_abs mult d w _ hw (by omega)

lemma b_hankel_cast (mult : X → ℕ) (d w p n a : ℕ) (hw : ∀ j ≤ 2 * d + 1, mom mult j < 2 ^ w)
    (hp : (d + 1).factorial * (2 ^ w) ^ (d + 1) < p) (hn : n ≤ d + 1)
    (hb : 2 * n + a ≤ 2 * d + 3) :
    ((Matrix.of fun s t : Fin n => (((mom mult (s.val + t.val + a) : ℕ) : ℤ) : ZMod p)).det = 0 ↔
      (Matrix.of fun s t : Fin n => (mom mult (s.val + t.val + a) : ℚ)).det = 0) := by
  rw [b_det_cast, b_cast_zero_iff _ (b_hankel_abs mult d w p n a hw hp hn hb), b_hankel_q,
    Int.cast_eq_zero]

lemma b_border (r : ℕ) (G : Matrix (Fin r) (Fin r) ℚ) (b : Fin r → ℚ) (hG : G.det ≠ 0)
    (M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℚ)
    (h1 : ∀ s t : Fin r, M (Fin.castSucc s) (Fin.castSucc t) = G s t)
    (h2 : ∀ s : Fin r, M (Fin.castSucc s) (Fin.last r) = b s)
    (h3 : ∀ t : Fin r, M (Fin.last r) (Fin.castSucc t) = b t)
    (h4 : M (Fin.last r) (Fin.last r) = 0) :
    M.det = -(dotProduct b (Matrix.mulVec G⁻¹ b)) * G.det := by
  let _ : Invertible G := Matrix.invertibleOfIsUnitDet G (isUnit_iff_ne_zero.mpr hG)
  have hM : M.submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks G (Matrix.of fun i (_ : Fin 1) => b i)
        (Matrix.of fun (_ : Fin 1) j => b j) 0 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · exact h1 i j
    · have : j = 0 := Subsingleton.elim _ _
      subst this
      exact h2 i
    · have : i = 0 := Subsingleton.elim _ _
      subst this
      exact h3 j
    · have : i = 0 := Subsingleton.elim _ _
      subst this
      have : j = 0 := Subsingleton.elim _ _
      subst this
      exact h4
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv M, hM, Matrix.det_fromBlocks₁₁,
    Matrix.invOf_eq_nonsing_inv, Matrix.det_unique (n := Fin 1), mul_comm, Matrix.mul_assoc]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

lemma b_value_core (mult : X → ℕ) (d : ℕ) (p : ℕ) [Fact p.Prime]
    (w : ℕ) (hw : ∀ j ≤ 2 * d + 1, mom mult j < 2 ^ w)
    (hp : (d + 1).factorial * (2 ^ w) ^ (d + 1) < p) (r : ℕ) (hrd : r ≤ d)
    (hpiv : ∀ l < r, piv (fun s t => ((Ghat mult d s t : ℤ) : ZMod p)) l ≠ 0)
    (hstop0 : r < d → piv (fun s t => ((Ghat mult d s t : ℤ) : ZMod p)) r = 0) :
    (Matrix.of fun s t : Fin r => (mom mult (s.val + t.val + 2) : ℚ)).det ≠ 0 ∧
    (r < d → levelsN mult ≤ r) ∧
    0 < (∏ l ∈ Finset.range r, piv (fun s t => ((Ghat mult d s t : ℤ) : ZMod p)) l).val ∧
    (((-((∏ l ∈ Finset.range r, piv (fun s t => ((Ghat mult d s t : ℤ) : ZMod p)) l) *
        absE (fun s t => ((Ghat mult d s t : ℤ) : ZMod p)) r d d)).val : ℚ) /
      ((∏ l ∈ Finset.range r, piv (fun s t => ((Ghat mult d s t : ℤ) : ZMod p)) l).val : ℚ) =
      dotProduct (fun s : Fin r => (mom mult (s.val + 1) : ℚ))
        (Matrix.mulVec (Matrix.of fun s t : Fin r => (mom mult (s.val + t.val + 2) : ℚ))⁻¹
          (fun s : Fin r => (mom mult (s.val + 1) : ℚ)))) := by
  have hNZ : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hden : (∏ l ∈ Finset.range r, piv (fun s t => ((Ghat mult d s t : ℤ) : ZMod p)) l) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun l hl => hpiv l (Finset.mem_range.mp hl))
  have hlead := det_lead (fun s t => ((Ghat mult d s t : ℤ) : ZMod p)) r hpiv
  have hm1 : (Matrix.of fun s t : Fin r => ((Ghat mult d s.val t.val : ℤ) : ZMod p)) =
      Matrix.of fun s t : Fin r => (((mom mult (s.val + t.val + 2) : ℕ) : ℤ) : ZMod p) := by
    ext s t
    have := s.isLt
    have := t.isLt
    simp only [Matrix.of_apply, Ghat, ↓reduceIte, show (s : ℕ) < d from by omega,
      show (t : ℕ) < d from by omega]
  rw [hm1] at hlead
  have hGabs := b_hankel_abs mult d w p r 2 hw hp (by omega) (by omega)
  have hGq : (Matrix.of fun s t : Fin r => (mom mult (s.val + t.val + 2) : ℚ)).det ≠ 0 := by
    intro h0
    rw [← b_hankel_cast mult d w p r 2 hw hp (by omega) (by omega)] at h0
    exact hden (hlead ▸ h0)
  have hpos := gram_det_pos mult r hGq
  rw [b_hankel_q] at hpos hGq
  have hposZ : 0 < (Matrix.of fun s t : Fin r => (mom mult (s.val + t.val + 2) : ℤ)).det := by
    exact_mod_cast hpos
  rw [b_det_cast] at hlead
  have hdenval : (((∏ l ∈ Finset.range r,
      piv (fun s t => ((Ghat mult d s t : ℤ) : ZMod p)) l).val : ℕ) : ℚ) =
      (((Matrix.of fun s t : Fin r => (mom mult (s.val + t.val + 2) : ℤ)).det : ℤ) : ℚ) := by
    rw [← hlead]
    exact b_val_cast _ hposZ.le (lt_of_abs_lt hGabs)

  have hstop : r < d → levelsN mult ≤ r := by
    intro hlt
    have hz := det_sel (fun s t => ((Ghat mult d s t : ℤ) : ZMod p)) r hpiv 0 0
    have hp0 : relE (fun s t => ((Ghat mult d s t : ℤ) : ZMod p)) r 0 0 = 0 := hstop0 hlt
    rw [hp0, mul_zero] at hz
    have hm : (Matrix.of fun s t : Fin (r + 1) =>
        ((Ghat mult d (sel r 0 s) (sel r 0 t) : ℤ) : ZMod p)) =
        Matrix.of fun s t : Fin (r + 1) => (((mom mult (s.val + t.val + 2) : ℕ) : ℤ) : ZMod p) := by
      ext s t
      have := s.isLt
      have := t.isLt
      simp only [Matrix.of_apply, b_sel_zero, Ghat, ↓reduceIte, show (s : ℕ) < d from by omega,
        show (t : ℕ) < d from by omega]
    rw [hm, b_hankel_cast mult d w p (r + 1) 2 hw hp (by omega) (by omega)] at hz
    have := (hankel_det_zero_iff mult 2 (r + 1) (by norm_num)).mp hz
    omega

  have hsel := det_sel (fun s t => ((Ghat mult d s t : ℤ) : ZMod p)) r hpiv (d - r) (d - r)
  have habs := absE_eq_relE (fun s t => ((Ghat mult d s t : ℤ) : ZMod p)) r (d - r) (d - r)
  have e : r + (d - r) = d := by omega
  rw [e] at habs
  rw [← habs, b_det_cast] at hsel
  have hBabs : |(Matrix.of fun s t : Fin (r + 1) =>
      Ghat mult d (sel r (d - r) s) (sel r (d - r) t)).det| < p := by
    apply b_det_abs _ (by omega) _ hp
    intro s t
    exact b_ghat_abs mult d w hw _ _ (b_sel_le r (d - r) d (by omega) s)
      (b_sel_le r (d - r) d (by omega) t)
  have hBq := b_border r (Matrix.of fun s t : Fin r => (mom mult (s.val + t.val + 2) : ℚ))
    (fun s : Fin r => (mom mult (s.val + 1) : ℚ)) (by rw [b_hankel_q]; exact hGq)
    (Matrix.of fun s t : Fin (r + 1) =>
      ((Ghat mult d (sel r (d - r) s) (sel r (d - r) t) : ℤ) : ℚ))
    (by
      intro s t
      have := s.isLt
      have := t.isLt
      simp only [Matrix.of_apply, b_sel_castSucc, Ghat, ↓reduceIte, show (s : ℕ) < d from by omega,
        show (t : ℕ) < d from by omega, Int.cast_natCast])
    (by
      intro s
      have := s.isLt
      simp only [Matrix.of_apply, b_sel_castSucc, b_sel_last, e, Ghat, ↓reduceIte,
        show (s : ℕ) < d from by omega, lt_irrefl, ↓reduceIte, Int.cast_natCast])
    (by
      intro t
      have := t.isLt
      simp only [Matrix.of_apply, b_sel_castSucc, b_sel_last, e, Ghat, ↓reduceIte,
        show (t : ℕ) < d from by omega, lt_irrefl, ↓reduceIte, Int.cast_natCast])
    (by simp only [Matrix.of_apply, b_sel_last, e, Ghat, ↓reduceIte, lt_irrefl, ↓reduceIte, Int.cast_zero])
  rw [b_det_cast, b_hankel_q] at hBq
  obtain ⟨hV, -⟩ := opt_thm mult d r hrd (by rw [b_hankel_q]; exact hGq) hstop
  have hnum : (0 : ℚ) ≤ -(((Matrix.of fun s t : Fin (r + 1) =>
      Ghat mult d (sel r (d - r) s) (sel r (d - r) t)).det : ℤ) : ℚ) := by
    rw [hBq]
    have := hpos
    nlinarith
  have hnumZ : 0 ≤ -(Matrix.of fun s t : Fin (r + 1) =>
      Ghat mult d (sel r (d - r) s) (sel r (d - r) t)).det := by exact_mod_cast hnum
  have hneg : -((∏ l ∈ Finset.range r, piv (fun s t => ((Ghat mult d s t : ℤ) : ZMod p)) l) *
      absE (fun s t => ((Ghat mult d s t : ℤ) : ZMod p)) r d d) =
      ((-(Matrix.of fun s t : Fin (r + 1) =>
        Ghat mult d (sel r (d - r) s) (sel r (d - r) t)).det : ℤ) : ZMod p) := by
    rw [← hsel]
    push_cast
    rfl
  refine ⟨by rw [b_hankel_q]; exact hGq, hstop, ?_, ?_⟩
  · have : (0 : ℚ) < (((∏ l ∈ Finset.range r,
        piv (fun s t => ((Ghat mult d s t : ℤ) : ZMod p)) l).val : ℕ) : ℚ) := by
      rw [hdenval]
      exact hpos
    exact_mod_cast this
  · rw [hdenval, hneg, b_val_cast _ hnumZ (lt_of_abs_lt (by rw [abs_neg]; exact hBabs)),
      Int.cast_neg, hBq]
    field_simp

theorem value_thm (mult : X → ℕ) (d : ℕ) (hd : 0 < d) (p : ℕ) [Fact p.Prime]
    (w : ℕ) (hw : ∀ j ≤ 2 * d + 1, mom mult j < 2 ^ w)
    (hp : (d + 1).factorial * (2 ^ w) ^ (d + 1) < p) :
    0 < (runS (fun s t => ((Ghat mult d s t : ℤ) : ZMod p)) d).2.1.val ∧
    (∀ coeff, fitQ mult d coeff ≤
      ((-((runS (fun s t => ((Ghat mult d s t : ℤ) : ZMod p)) d).2.1 *
          (runS (fun s t => ((Ghat mult d s t : ℤ) : ZMod p)) d).1 d d)).val : ℚ) /
        ((runS (fun s t => ((Ghat mult d s t : ℤ) : ZMod p)) d).2.1.val : ℚ)) ∧
    (∃ coeff, fitQ mult d coeff =
      ((-((runS (fun s t => ((Ghat mult d s t : ℤ) : ZMod p)) d).2.1 *
          (runS (fun s t => ((Ghat mult d s t : ℤ) : ZMod p)) d).1 d d)).val : ℚ) /
        ((runS (fun s t => ((Ghat mult d s t : ℤ) : ZMod p)) d).2.1.val : ℚ)) ∧
    ((-((runS (fun s t => ((Ghat mult d s t : ℤ) : ZMod p)) d).2.1 *
          (runS (fun s t => ((Ghat mult d s t : ℤ) : ZMod p)) d).1 d d)).val : ℚ) /
        ((runS (fun s t => ((Ghat mult d s t : ℤ) : ZMod p)) d).2.1.val : ℚ) ≤
      ((wordsF mult).card : ℚ) ∧
    (((-((runS (fun s t => ((Ghat mult d s t : ℤ) : ZMod p)) d).2.1 *
          (runS (fun s t => ((Ghat mult d s t : ℤ) : ZMod p)) d).1 d d)).val : ℚ) /
        ((runS (fun s t => ((Ghat mult d s t : ℤ) : ZMod p)) d).2.1.val : ℚ) =
      ((wordsF mult).card : ℚ) ↔ levelsN mult ≤ d) := by
  obtain ⟨r, hrd, hpiv, hstop0, hrun⟩ :=
    runS_spec (fun s t => ((Ghat mult d s t : ℤ) : ZMod p)) d
  rw [hrun]
  dsimp only
  obtain ⟨hGq, hstop, hpos, hval⟩ := b_value_core mult d p w hw hp r hrd hpiv hstop0
  obtain ⟨-, h2, h3, h4, h5⟩ := opt_thm mult d r hrd hGq hstop
  rw [hval]
  exact ⟨hpos, h2, h3, h4, h5⟩

theorem flag_thm (mult : X → ℕ) (d : ℕ) (p : ℕ) [Fact p.Prime] (w : ℕ)
    (hw : ∀ j ≤ 2 * d + 1, mom mult j < 2 ^ w)
    (hp : (d + 1).factorial * (2 ^ w) ^ (d + 1) < p) :
    ((runS (fun s t => ((Hone mult s t : ℤ) : ZMod p)) (d + 1)).2.2 = true ↔
      levelsN mult ≤ d) := by
  have hNZ : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨r, hrK, hpiv, hstop0, hrun⟩ :=
    runS_spec (fun s t => ((Hone mult s t : ℤ) : ZMod p)) (d + 1)
  rw [hrun]
  dsimp only
  rw [decide_eq_true_iff]
  rcases Nat.lt_or_ge r (d + 1) with h | h
  · have hz := det_sel (fun s t => ((Hone mult s t : ℤ) : ZMod p)) r hpiv 0 0
    have hp0 : relE (fun s t => ((Hone mult s t : ℤ) : ZMod p)) r 0 0 = 0 := hstop0 h
    rw [hp0, mul_zero] at hz
    have hm : (Matrix.of fun s t : Fin (r + 1) =>
        ((Hone mult (sel r 0 s) (sel r 0 t) : ℤ) : ZMod p)) =
        Matrix.of fun s t : Fin (r + 1) => (((mom mult (s.val + t.val + 1) : ℕ) : ℤ) : ZMod p) := by
      ext s t
      simp only [Matrix.of_apply, b_sel_zero, Hone]
    rw [hm, b_hankel_cast mult d w p (r + 1) 1 hw hp (by omega) (by omega)] at hz
    have := (hankel_det_zero_iff mult 1 (r + 1) le_rfl).mp hz
    exact ⟨fun _ => by omega, fun _ => h⟩
  · have hr : r = d + 1 := by omega
    subst hr
    have hz := det_lead (fun s t => ((Hone mult s t : ℤ) : ZMod p)) (d + 1) hpiv
    have hne : (∏ l ∈ Finset.range (d + 1), piv (fun s t => ((Hone mult s t : ℤ) : ZMod p)) l) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun l hl => hpiv l (Finset.mem_range.mp hl))
    rw [← hz] at hne
    have hne' : (Matrix.of fun s t : Fin (d + 1) =>
        (((mom mult (s.val + t.val + 1) : ℕ) : ℤ) : ZMod p)).det ≠ 0 := hne
    rw [Ne, b_hankel_cast mult d w p (d + 1) 1 hw hp le_rfl (by omega),
      hankel_det_zero_iff mult 1 (d + 1) le_rfl] at hne'
    constructor
    · intro h'
      omega
    · intro h'
      omega

end Problem

def regMulReg (N : ℕ) (G : List BGate) {B : ℕ} (a b : Fin B → ℕ) :
    ℕ → List BGate × (Fin B → ℕ)
  | 0 => (G, constReg B 0)
  | k + 1 =>
    let r1 := regMulReg N G a b k
    if h : k < B then
      let g := regGate N r1.1 (b ⟨k, h⟩) (shiftReg k a)
      let r2 := regAdd N g.1 r1.2 g.2
      (r2.1, r2.2.1)
    else r1

lemma regVal_mod_two_pow_succ {B : ℕ} (G : List BGate) (src : List Bool) (b : Fin B → ℕ) (k : ℕ) :
    regVal G src b % 2 ^ (k + 1) =
      regVal G src b % 2 ^ k + ((regVal G src b).testBit k).toNat * 2 ^ k :=
  mod_two_pow_succ_eq _ k

lemma regMulReg_spec {N B : ℕ} (hN : 2 ≤ N) {G : List BGate} {a b : Fin B → ℕ} (k : ℕ)
    (hWF : WF N G) (ha : RegOK N G a) (hb : RegOK N G b) :
    let res := regMulReg N G a b k
    Extends G res.1 ∧ res.1.length ≤ G.length + 6 * B * k ∧ WF N res.1 ∧
    RegOK N res.1 res.2 ∧
    ∀ src, HasBase src N → (regVal G src b % 2 ^ k) * regVal G src a < 2 ^ B →
      regVal res.1 src res.2 = (regVal G src b % 2 ^ k) * regVal G src a := by
  induction k with
  | zero =>
    refine ⟨extends_rfl G, by simp [regMulReg], hWF, constReg_ok hN G 0, ?_⟩
    intro src hbase _
    simp [regMulReg, constReg_val hbase, Nat.mod_one]
  | succ m ih =>
    dsimp only [regMulReg]
    set r1 := regMulReg N G a b m
    have he1 := ih.1
    have hl1 := ih.2.1
    have hw1 := ih.2.2.1
    have hok1 := ih.2.2.2.1
    have hev1 := ih.2.2.2.2
    by_cases hmB : m < B
    · simp only [hmB, dite_true]
      have haok1 : RegOK N r1.1 a := regOK_extends he1 ha
      have hbok1 : RegOK N r1.1 b := regOK_extends he1 hb
      have hshok : RegOK N r1.1 (shiftReg m a) := shiftReg_ok hN haok1 m
      have hc : b ⟨m, hmB⟩ < N + r1.1.length := hbok1 ⟨m, hmB⟩
      have hg := regGate_spec hw1 hc hshok
      set g := regGate N r1.1 (b ⟨m, hmB⟩) (shiftReg m a)
      have hok1g : RegOK N g.1 r1.2 := regOK_extends hg.1 hok1
      have hadd := regAdd_spec hN hg.2.2.1 hok1g hg.2.2.2.1
      refine ⟨extends_trans he1 (extends_trans hg.1 hadd.1), ?_, hadd.2.2.1, hadd.2.2.2.1, ?_⟩
      · have h1 := hg.2.1
        have h2 := hadd.2.1
        have hmul : 6 * B * (m + 1) = 6 * B * m + 6 * B := Nat.mul_succ (6 * B) m
        omega
      · intro src hbase hlt
        have hmod := regVal_mod_two_pow_succ G src b m
        have hle1 : regVal G src b % 2 ^ m ≤ regVal G src b % 2 ^ (m + 1) := by omega
        have hlt1 : (regVal G src b % 2 ^ m) * regVal G src a < 2 ^ B :=
          lt_of_le_of_lt (Nat.mul_le_mul_right _ hle1) hlt
        have hv1 := hev1 src hbase hlt1
        have hav1 : regVal r1.1 src a = regVal G src a := regVal_extends he1 hbase.1 ha
        have hbit : evalW r1.1 src (b ⟨m, hmB⟩) = (regVal G src b).testBit m := by
          rw [evalW_extends he1 (by rw [hbase.1]; exact hb ⟨m, hmB⟩)]
          exact (regVal_testBit_fin G src b ⟨m, hmB⟩).symm
        have hgv : regVal g.1 src g.2 =
            ((regVal G src b).testBit m).toNat * (regVal G src a * 2 ^ m) := by
          rw [hg.2.2.2.2 src hbase.1, hbit]
          cases hbt : (regVal G src b).testBit m
          · simp
          · simp only [ite_true, Bool.toNat_true, one_mul]
            rw [shiftReg_val hbase, hav1]
            apply Nat.mod_eq_of_lt
            rw [hbt] at hmod
            simp only [Bool.toNat_true, one_mul] at hmod
            have h2le : 2 ^ m ≤ regVal G src b % 2 ^ (m + 1) := by omega
            calc regVal G src a * 2 ^ m = 2 ^ m * regVal G src a := Nat.mul_comm _ _
              _ ≤ (regVal G src b % 2 ^ (m + 1)) * regVal G src a := Nat.mul_le_mul_right _ h2le
              _ < 2 ^ B := hlt
        have hr1g : regVal g.1 src r1.2 = (regVal G src b % 2 ^ m) * regVal G src a := by
          rw [regVal_extends hg.1 hbase.1 hok1, hv1]
        have hsum_eq : regVal g.1 src r1.2 + regVal g.1 src g.2 =
            (regVal G src b % 2 ^ (m + 1)) * regVal G src a := by
          rw [hr1g, hgv, hmod, Nat.add_mul]
          ring
        have hsum_lt : regVal g.1 src r1.2 + regVal g.1 src g.2 < 2 ^ B := by
          rw [hsum_eq]; exact hlt
        rw [regAdd_val_of_lt hN hg.2.2.1 hok1g hg.2.2.2.1 hbase hsum_lt, hsum_eq]
    · simp only [hmB, dite_false]
      refine ⟨he1, ?_, hw1, hok1, ?_⟩
      · have hmul : 6 * B * (m + 1) = 6 * B * m + 6 * B := Nat.mul_succ (6 * B) m
        omega
      · intro src hbase hlt
        have hbl : regVal G src b < 2 ^ B := regVal_lt G src b
        have hpow : 2 ^ B ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) (by omega)
        have hpow1 : 2 ^ B ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by omega) (by omega)
        have e1 : regVal G src b % 2 ^ m = regVal G src b := Nat.mod_eq_of_lt (by omega)
        have e2 : regVal G src b % 2 ^ (m + 1) = regVal G src b := Nat.mod_eq_of_lt (by omega)
        rw [e2] at hlt ⊢
        have := hev1 src hbase (by rw [e1]; exact hlt)
        rw [this, e1]

def regModConst (N : ℕ) (G : List BGate) {B : ℕ} (d : ℕ) :
    ℕ → (Fin B → ℕ) → List BGate × (Fin B → ℕ)
  | 0, r => (G, r)
  | m + 1, r =>
    let C := d * 2 ^ m
    let rs := regSub N G r (constReg B C)
    let rm := regMux N rs.1 rs.2.2 r rs.2.1
    regModConst N rm.1 d m rm.2

lemma regModConst_spec {N B : ℕ} (hN : 2 ≤ N) (d : ℕ) (hd : 0 < d) :
    ∀ (m : ℕ) (G : List BGate) (r : Fin B → ℕ),
      WF N G → RegOK N G r → d * 2 ^ m ≤ 2 ^ B →
      let res := regModConst N G d m r
      Extends G res.1 ∧ res.1.length ≤ G.length + m * (8 * B) ∧ WF N res.1 ∧
      RegOK N res.1 res.2 ∧
      ∀ src, HasBase src N → regVal G src r < d * 2 ^ m →
        regVal res.1 src res.2 = regVal G src r % d := by
  intro m
  induction m with
  | zero =>
    intro G r hWF hr _
    refine ⟨extends_rfl G, by simp [regModConst], hWF, hr, ?_⟩
    intro src _ hlt
    simp only [Nat.pow_zero, Nat.mul_one] at hlt
    simp [regModConst, Nat.mod_eq_of_lt hlt]
  | succ k ih =>
    intro G r hWF hr hdB
    dsimp only [regModConst]
    set C := d * 2 ^ k
    have hCB : C < 2 ^ B := by
      have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
      have hpos : 0 < C := Nat.mul_pos hd (Nat.two_pow_pos k)
      have h2C : 2 * C ≤ 2 ^ B := by
        calc 2 * C = d * (2 * 2 ^ k) := by simp only [C]; ring
          _ = d * 2 ^ (k + 1) := by rw [← hpow]
          _ ≤ 2 ^ B := hdB
      omega
    have hcok := constReg_ok hN G C (B := B)
    have hsub := regSub_spec hN hWF hr hcok
    set rs := regSub N G r (constReg B C)
    have hok_diff : RegOK N rs.1 rs.2.1 := hsub.2.2.2.1
    have hok_r : RegOK N rs.1 r := regOK_extends hsub.1 hr
    have hmux := regMux_spec hsub.2.2.1 hsub.2.2.2.2.1 hok_r hok_diff
    set rm := regMux N rs.1 rs.2.2 r rs.2.1
    have hdBk : d * 2 ^ k ≤ 2 ^ B := le_of_lt hCB
    have hrd := ih rm.1 rm.2 hmux.2.2.1 hmux.2.2.2.1 hdBk
    set rd := regModConst N rm.1 d k rm.2
    refine ⟨extends_trans hsub.1 (extends_trans hmux.1 hrd.1), ?_, hrd.2.2.1, hrd.2.2.2.1, ?_⟩
    · have h1 := hsub.2.1
      have h2 := hmux.2.1
      have h3 := hrd.2.1
      have hmul : (k + 1) * (8 * B) = k * (8 * B) + 8 * B := Nat.succ_mul k _
      omega
    · intro src hbase hlt
      have hcv : regVal G src (constReg B C) = C := constReg_val_of_lt hbase hCB
      have hbor := regSub_borrow_iff hN hWF hr hcok hbase
      rw [hcv] at hbor
      have hrm_val : regVal rm.1 src rm.2 =
          if C ≤ regVal G src r then regVal G src r - C else regVal G src r := by
        rw [hmux.2.2.2.2 src hbase.1]
        rw [regVal_extends hsub.1 hbase.1 hr]
        cases hb' : evalW rs.1 src rs.2.2
        · have hnotlt : ¬ regVal G src r < C := by
            intro hlt'; have := hbor.mpr hlt'; rw [hb'] at this; cases this
          have hge : C ≤ regVal G src r := Nat.le_of_not_lt hnotlt
          simp only [Bool.false_eq_true, ite_false, hge, ite_true]
          have hdiff := regSub_val_of_le hN hWF hr hcok hbase (by rw [hcv]; exact hge)
          rw [hcv] at hdiff
          exact hdiff
        · have hlt' : regVal G src r < C := hbor.mp hb'
          have hnotge : ¬ C ≤ regVal G src r := Nat.not_le.mpr hlt'
          simp [hnotge]
      have hrm_lt : regVal rm.1 src rm.2 < d * 2 ^ k := by
        rw [hrm_val]
        have hpow : d * 2 ^ (k + 1) = C + C := by
          simp only [C, Nat.pow_succ]; ring
        split <;> omega
      rw [hrd.2.2.2.2 src hbase hrm_lt, hrm_val]
      by_cases hge : C ≤ regVal G src r
      · simp only [hge, ite_true]
        have heq : regVal G src r = (regVal G src r - C) + d * 2 ^ k := by omega
        conv_rhs => rw [heq]
        rw [Nat.add_mul_mod_self_left]
      · simp [hge]

def Rep (p : ℕ) (G : List BGate) (src : List Bool) {B : ℕ} (r : Fin B → ℕ) (x : ZMod p) : Prop :=
  regVal G src r < p ∧ ((regVal G src r : ℕ) : ZMod p) = x

lemma rep_extends {N B p : ℕ} {G1 G2 : List BGate} {src : List Bool} {r : Fin B → ℕ} {x : ZMod p}
    (he : Extends G1 G2) (hlen : src.length = N) (hr : RegOK N G1 r) (h : Rep p G1 src r x) :
    Rep p G2 src r x := by
  unfold Rep at h ⊢
  rw [regVal_extends he hlen hr]
  exact h

def modMul (N : ℕ) (G : List BGate) {B : ℕ} (p Bp : ℕ) (a b : Fin B → ℕ) :
    List BGate × (Fin B → ℕ) :=
  let m := regMulReg N G a b B
  regModConst N m.1 p Bp m.2

lemma bp_le_b {p Bp B : ℕ} (hp : 0 < p) (hB : p * 2 ^ Bp ≤ 2 ^ B) : Bp ≤ B := by
  by_contra h
  have h1 : 2 ^ B < 2 ^ Bp := Nat.pow_lt_pow_right (by omega) (by omega)
  have h2 : 2 ^ Bp ≤ p * 2 ^ Bp := Nat.le_mul_of_pos_left _ hp
  omega

lemma modMul_spec {N B p Bp : ℕ} (hN : 2 ≤ N) (hp : 0 < p) (hpB : p ≤ 2 ^ Bp)
    (hB : p * 2 ^ Bp ≤ 2 ^ B) {G : List BGate} {a b : Fin B → ℕ}
    (hWF : WF N G) (ha : RegOK N G a) (hb : RegOK N G b) :
    let res := modMul N G p Bp a b
    Extends G res.1 ∧ res.1.length ≤ G.length + 14 * B * B ∧ WF N res.1 ∧
    RegOK N res.1 res.2 ∧
    ∀ src, HasBase src N → ∀ x y : ZMod p, Rep p G src a x → Rep p G src b y →
      Rep p res.1 src res.2 (x * y) := by
  dsimp only [modMul]
  have hm := regMulReg_spec hN B hWF ha hb
  set m := regMulReg N G a b B
  have hr := regModConst_spec hN p hp Bp m.1 m.2 hm.2.2.1 hm.2.2.2.1 hB
  have hBpB : Bp ≤ B := bp_le_b hp hB
  refine ⟨extends_trans hm.1 hr.1, ?_, hr.2.2.1, hr.2.2.2.1, ?_⟩
  · have h1 := hm.2.1
    have h2 := hr.2.1
    have h3 : Bp * (8 * B) ≤ B * (8 * B) := Nat.mul_le_mul_right _ hBpB
    nlinarith
  · intro src hbase x y hx hy
    have hbl : regVal G src b < 2 ^ B := regVal_lt G src b
    have hbm : regVal G src b % 2 ^ B = regVal G src b := Nat.mod_eq_of_lt hbl
    have hprod : regVal G src a * regVal G src b < p * 2 ^ Bp := by
      calc regVal G src a * regVal G src b < p * p := Nat.mul_lt_mul'' hx.1 hy.1
        _ ≤ p * 2 ^ Bp := Nat.mul_le_mul_left p hpB
    have hmv : regVal m.1 src m.2 = regVal G src a * regVal G src b := by
      rw [hm.2.2.2.2 src hbase (by rw [hbm]; rw [Nat.mul_comm]; omega), hbm, Nat.mul_comm]
    have hres := hr.2.2.2.2 src hbase (by rw [hmv]; exact hprod)
    refine ⟨by rw [hres]; exact Nat.mod_lt _ hp, ?_⟩
    rw [hres, hmv, ZMod.natCast_mod, Nat.cast_mul, hx.2, hy.2]

def modSub (N : ℕ) (G : List BGate) {B : ℕ} (p : ℕ) (a b : Fin B → ℕ) :
    List BGate × (Fin B → ℕ) :=
  let t := regSub N G (constReg B p) b
  let s := regAdd N t.1 a t.2.1
  regModConst N s.1 p 1 s.2.1

lemma modSub_spec {N B p : ℕ} (hN : 2 ≤ N) (hp : 0 < p) (h2p : 2 * p ≤ 2 ^ B)
    {G : List BGate} {a b : Fin B → ℕ}
    (hWF : WF N G) (ha : RegOK N G a) (hb : RegOK N G b) :
    let res := modSub N G p a b
    Extends G res.1 ∧ res.1.length ≤ G.length + 18 * B ∧ WF N res.1 ∧
    RegOK N res.1 res.2 ∧
    ∀ src, HasBase src N → ∀ x y : ZMod p, Rep p G src a x → Rep p G src b y →
      Rep p res.1 src res.2 (x - y) := by
  dsimp only [modSub]
  have hcok := constReg_ok hN G p (B := B)
  have ht := regSub_spec hN hWF hcok hb
  set t := regSub N G (constReg B p) b
  have haok : RegOK N t.1 a := regOK_extends ht.1 ha
  have hs := regAdd_spec hN ht.2.2.1 haok ht.2.2.2.1
  set s := regAdd N t.1 a t.2.1
  have hr := regModConst_spec hN p hp 1 s.1 s.2.1 hs.2.2.1 hs.2.2.2.1 (by omega)
  refine ⟨extends_trans ht.1 (extends_trans hs.1 hr.1), ?_, hr.2.2.1, hr.2.2.2.1, ?_⟩
  · have h1 := ht.2.1
    have h2 := hs.2.1
    have h3 := hr.2.1
    omega
  · intro src hbase x y hx hy
    have hpB : p < 2 ^ B := by omega
    have hcv : regVal G src (constReg B p) = p := constReg_val_of_lt hbase hpB
    have htv : regVal t.1 src t.2.1 = p - regVal G src b := by
      have := regSub_val_of_le hN hWF hcok hb hbase (by rw [hcv]; exact le_of_lt hy.1)
      rw [this, hcv]
    have hav : regVal t.1 src a = regVal G src a := regVal_extends ht.1 hbase.1 ha
    have hsum_lt : regVal t.1 src a + regVal t.1 src t.2.1 < 2 ^ B := by
      rw [hav, htv]; have := hx.1; omega
    have hsv : regVal s.1 src s.2.1 = regVal G src a + (p - regVal G src b) := by
      rw [regAdd_val_of_lt hN ht.2.2.1 haok ht.2.2.2.1 hbase hsum_lt, hav, htv]
    have hres := hr.2.2.2.2 src hbase (by rw [hsv]; have := hx.1; omega)
    refine ⟨by rw [hres]; exact Nat.mod_lt _ hp, ?_⟩
    rw [hres, hsv, ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub (le_of_lt hy.1), ZMod.natCast_self,
      hx.2, hy.2]
    ring

def modPowAux (N : ℕ) (G : List BGate) {B : ℕ} (p Bp e : ℕ) (a : Fin B → ℕ) :
    ℕ → List BGate × (Fin B → ℕ) × (Fin B → ℕ)
  | 0 => (G, constReg B 1, a)
  | k + 1 =>
    let r := modPowAux N G p Bp e a k
    let r1 : List BGate × (Fin B → ℕ) :=
      if e.testBit k then modMul N r.1 p Bp r.2.1 r.2.2 else (r.1, r.2.1)
    let r2 := modMul N r1.1 p Bp r.2.2 r.2.2
    (r2.1, r1.2, r2.2)

lemma modPowAux_spec {N B p Bp : ℕ} (hN : 2 ≤ N) (hp : 1 < p) (hpB : p ≤ 2 ^ Bp)
    (hB : p * 2 ^ Bp ≤ 2 ^ B) (e : ℕ) {G : List BGate} {a : Fin B → ℕ}
    (hWF : WF N G) (ha : RegOK N G a) (k : ℕ) :
    let res := modPowAux N G p Bp e a k
    Extends G res.1 ∧ res.1.length ≤ G.length + k * (28 * B * B) ∧ WF N res.1 ∧
    RegOK N res.1 res.2.1 ∧ RegOK N res.1 res.2.2 ∧
    ∀ src, HasBase src N → ∀ x : ZMod p, Rep p G src a x →
      Rep p res.1 src res.2.1 (x ^ (e % 2 ^ k)) ∧ Rep p res.1 src res.2.2 (x ^ (2 ^ k)) := by
  have hp0 : 0 < p := by omega
  induction k with
  | zero =>
    refine ⟨extends_rfl G, by simp [modPowAux], hWF, constReg_ok hN G 1, ha, ?_⟩
    intro src hbase x hx
    have h1B : 1 < 2 ^ B := by
      have := Nat.le_mul_of_pos_right p (Nat.two_pow_pos Bp)
      omega
    have h1v : regVal G src (constReg B 1) = 1 := constReg_val_of_lt hbase h1B
    refine ⟨⟨by simp only [modPowAux]; rw [h1v]; exact hp, ?_⟩, ?_⟩
    · simp only [modPowAux]; rw [h1v]; simp [Nat.mod_one]
    · simpa [modPowAux] using hx
  | succ k ih =>
    dsimp only [modPowAux]
    set r := modPowAux N G p Bp e a k
    have he := ih.1
    have hl := ih.2.1
    have hw := ih.2.2.1
    have hok1 := ih.2.2.2.1
    have hok2 := ih.2.2.2.2.1
    have hev := ih.2.2.2.2.2
    have hmod := mod_two_pow_succ_eq e k
    by_cases hbit : e.testBit k = true
    · simp only [hbit, ite_true]
      have hm1 := modMul_spec hN hp0 hpB hB hw hok1 hok2
      set m1 := modMul N r.1 p Bp r.2.1 r.2.2
      have hok2' : RegOK N m1.1 r.2.2 := regOK_extends hm1.1 hok2
      have hm2 := modMul_spec hN hp0 hpB hB hm1.2.2.1 hok2' hok2'
      set m2 := modMul N m1.1 p Bp r.2.2 r.2.2
      refine ⟨extends_trans he (extends_trans hm1.1 hm2.1), ?_, hm2.2.2.1,
        regOK_extends hm2.1 hm1.2.2.2.1, hm2.2.2.2.1, ?_⟩
      · have h1 := hm1.2.1
        have h2 := hm2.2.1
        have hmul : (k + 1) * (28 * B * B) = k * (28 * B * B) + 28 * B * B := Nat.succ_mul k _
        have h28 : 28 * B * B = 2 * (14 * B * B) := by ring
        omega
      · intro src hbase x hx
        have hr := hev src hbase x hx
        have hx1 := hm1.2.2.2.2 src hbase _ _ hr.1 hr.2
        have hb2 : Rep p m1.1 src r.2.2 (x ^ 2 ^ k) := rep_extends hm1.1 hbase.1 hok2 hr.2
        have hx2 := hm2.2.2.2.2 src hbase _ _ hb2 hb2
        refine ⟨rep_extends hm2.1 hbase.1 hm1.2.2.2.1 ?_, ?_⟩
        · rw [hbit] at hmod
          simp only [Bool.toNat_true, one_mul] at hmod
          rw [hmod, pow_add]
          exact hx1
        · rw [pow_succ, pow_mul, sq]
          exact hx2
    · have hbf : e.testBit k = false := Bool.eq_false_iff.mpr hbit
      simp only [hbf, Bool.false_eq_true, ite_false]
      have hm2 := modMul_spec hN hp0 hpB hB hw hok2 hok2
      set m2 := modMul N r.1 p Bp r.2.2 r.2.2
      refine ⟨extends_trans he hm2.1, ?_, hm2.2.2.1, regOK_extends hm2.1 hok1, hm2.2.2.2.1, ?_⟩
      · have h2 := hm2.2.1
        have hmul : (k + 1) * (28 * B * B) = k * (28 * B * B) + 28 * B * B := Nat.succ_mul k _
        have h28 : 28 * B * B = 2 * (14 * B * B) := by ring
        omega
      · intro src hbase x hx
        have hr := hev src hbase x hx
        have hx2 := hm2.2.2.2.2 src hbase _ _ hr.2 hr.2
        refine ⟨rep_extends hm2.1 hbase.1 hok1 ?_, ?_⟩
        · rw [hbf] at hmod
          simp only [Bool.toNat_false, zero_mul, Nat.add_zero] at hmod
          rw [hmod]
          exact hr.1
        · rw [pow_succ, pow_mul, sq]
          exact hx2

lemma zmod_pow_sub_two_eq_inv {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p) (x : ZMod p) :
    x ^ (p - 2) = x⁻¹ := by
  by_cases hx : x = 0
  · subst hx
    rw [inv_zero, zero_pow (by omega)]
  · have h1 := ZMod.pow_card_sub_one_eq_one hx
    have h2 : x ^ (p - 2) * x = 1 := by
      rw [← pow_succ]
      have : p - 2 + 1 = p - 1 := by omega
      rw [this, h1]
    exact eq_inv_of_mul_eq_one_left h2

def modInv (N : ℕ) (G : List BGate) {B : ℕ} (p Bp : ℕ) (a : Fin B → ℕ) :
    List BGate × (Fin B → ℕ) :=
  let r := modPowAux N G p Bp (p - 2) a Bp
  (r.1, r.2.1)

lemma modInv_spec {N B p Bp : ℕ} [Fact p.Prime] (hN : 2 ≤ N) (hp : 3 ≤ p) (hpB : p ≤ 2 ^ Bp)
    (hB : p * 2 ^ Bp ≤ 2 ^ B) {G : List BGate} {a : Fin B → ℕ}
    (hWF : WF N G) (ha : RegOK N G a) :
    let res := modInv N G p Bp a
    Extends G res.1 ∧ res.1.length ≤ G.length + 28 * B * B * B ∧ WF N res.1 ∧
    RegOK N res.1 res.2 ∧
    ∀ src, HasBase src N → ∀ x : ZMod p, Rep p G src a x →
      Rep p res.1 src res.2 x⁻¹ := by
  dsimp only [modInv]
  have h := modPowAux_spec hN (by omega) hpB hB (p - 2) hWF ha Bp
  have hBpB : Bp ≤ B := bp_le_b (by omega) hB
  refine ⟨h.1, ?_, h.2.2.1, h.2.2.2.1, ?_⟩
  · have h1 := h.2.1
    have : Bp * (28 * B * B) ≤ B * (28 * B * B) := Nat.mul_le_mul_right _ hBpB
    nlinarith
  · intro src hbase x hx
    have hr := (h.2.2.2.2.2 src hbase x hx).1
    have he : (p - 2) % 2 ^ Bp = p - 2 := Nat.mod_eq_of_lt (by omega)
    rw [he, zmod_pow_sub_two_eq_inv hp] at hr
    exact hr

lemma rep_ne_zero_iff {p B : ℕ} {G : List BGate} {src : List Bool} {r : Fin B → ℕ} {x : ZMod p}
    (h : Rep p G src r x) : regVal G src r ≠ 0 ↔ x ≠ 0 := by
  rw [← h.2]
  constructor
  · intro hne hx
    rw [ZMod.natCast_eq_zero_iff] at hx
    exact hne (Nat.eq_zero_of_dvd_of_lt hx h.1)
  · intro hx hv
    apply hx
    rw [hv]
    simp

lemma two_p_le {p Bp B : ℕ} (hpB : p ≤ 2 ^ Bp) (hp : 3 ≤ p) (hB : p * 2 ^ Bp ≤ 2 ^ B) :
    2 * p ≤ 2 ^ B := by
  have : 2 ≤ 2 ^ Bp := by
    rcases Nat.eq_zero_or_pos Bp with h | h
    · subst h; simp at hpB; omega
    · calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ Bp := Nat.pow_le_pow_right (by omega) h
  calc 2 * p = p * 2 := Nat.mul_comm _ _
    _ ≤ p * 2 ^ Bp := Nat.mul_le_mul_left p this
    _ ≤ 2 ^ B := hB

def headBlock (N : ℕ) {B : ℕ} (p Bp : ℕ) (s : Fin B → ℕ) (stop : ℕ) (G : List BGate) :
    List BGate × ℕ × ℕ × (Fin B → ℕ) :=
  let nz := regNz N G s
  let go := emitGate N nz.1 (fun a b => !a && b) stop nz.2
  let st := emitGate N go.1 (fun a _ => !a) go.2 go.2
  let iv := modInv N st.1 p Bp s
  (iv.1, go.2, st.2, iv.2)

lemma headBlock_spec {N B p Bp : ℕ} [Fact p.Prime] (hN : 2 ≤ N) (hp : 3 ≤ p)
    (hpB : p ≤ 2 ^ Bp) (hB : p * 2 ^ Bp ≤ 2 ^ B) {G : List BGate} {s : Fin B → ℕ} {stop : ℕ}
    (hWF : WF N G) (hs : RegOK N G s) (hstop : stop < N + G.length) :
    let res := headBlock N p Bp s stop G
    Extends G res.1 ∧ res.1.length ≤ G.length + (28 * B * B * B + B + 2) ∧ WF N res.1 ∧
    res.2.1 < N + res.1.length ∧ res.2.2.1 < N + res.1.length ∧ RegOK N res.1 res.2.2.2 ∧
    ∀ src, HasBase src N → ∀ (x : ZMod p) (b : Bool), Rep p G src s x → evalW G src stop = b →
      evalW res.1 src res.2.1 = (!b && decide (x ≠ 0)) ∧
      evalW res.1 src res.2.2.1 = !(!b && decide (x ≠ 0)) ∧
      Rep p res.1 src res.2.2.2 x⁻¹ := by
  dsimp only [headBlock]
  have hnz := regNz_spec hN hWF hs
  set nz := regNz N G s
  set opGo : Bool → Bool → Bool := fun a b => !a && b
  have hstop1 : stop < N + nz.1.length := by have := hnz.2.1; omega
  have hgoW : WF N (emitGate N nz.1 opGo stop nz.2).1 :=
    emitGate_wf opGo hnz.2.2.1 hstop1 hnz.2.2.2.1
  have hgoE : Extends nz.1 (emitGate N nz.1 opGo stop nz.2).1 := emitGate_extends N nz.1 opGo stop nz.2
  have hgoL := emitGate_len N nz.1 opGo stop nz.2
  have hgoO := emitGate_out_lt N nz.1 opGo stop nz.2
  set go := emitGate N nz.1 opGo stop nz.2
  set opNot : Bool → Bool → Bool := fun a _ => !a
  have hstW : WF N (emitGate N go.1 opNot go.2 go.2).1 := emitGate_wf opNot hgoW hgoO hgoO
  have hstE : Extends go.1 (emitGate N go.1 opNot go.2 go.2).1 :=
    emitGate_extends N go.1 opNot go.2 go.2
  have hstL := emitGate_len N go.1 opNot go.2 go.2
  have hstO := emitGate_out_lt N go.1 opNot go.2 go.2
  set st := emitGate N go.1 opNot go.2 go.2
  have heGst : Extends G st.1 := extends_trans hnz.1 (extends_trans hgoE hstE)
  have hiv := modInv_spec hN hp hpB hB hstW (regOK_extends heGst hs)
  set iv := modInv N st.1 p Bp s
  have hlen1 := extends_len hiv.1
  refine ⟨extends_trans heGst hiv.1, ?_, hiv.2.2.1, by omega, by omega, hiv.2.2.2.1, ?_⟩
  · have := hnz.2.1; have := hiv.2.1; omega
  · intro src hbase x b hx hb
    have hgo : evalW go.1 src go.2 = (!b && decide (x ≠ 0)) := by
      rw [emitGate_eval opGo stop nz.2 hbase.1]
      simp only [opGo]
      rw [evalW_extends hnz.1 (by rw [hbase.1]; exact hstop), hb]
      have hz := hnz.2.2.2.2 src hbase
      have hz2 := rep_ne_zero_iff hx
      congr 1
      cases hbv : evalW nz.1 src nz.2
      · have : ¬ x ≠ 0 := fun h => by
          rw [← hz2, ← hz, hbv] at h; cases h
        simp [this]
      · have : x ≠ 0 := hz2.mp (hz.mp hbv)
        simp [this]
    refine ⟨?_, ?_, ?_⟩
    · rw [evalW_extends (extends_trans hstE hiv.1) (by rw [hbase.1]; exact hgoO), hgo]
    · rw [evalW_extends hiv.1 (by rw [hbase.1]; exact hstO)]
      rw [emitGate_eval opNot go.2 go.2 hbase.1]
      simp only [opNot]
      rw [hgo]
    · exact hiv.2.2.2.2 src hbase x (rep_extends heGst hbase.1 hs hx)

def tBlock (N : ℕ) {K B : ℕ} (p Bp : ℕ) (S : Fin K → Fin K → Fin B → ℕ) (k : Fin K)
    (iv : Fin B → ℕ) (G : List BGate) : List BGate × (Fin K → Fin B → ℕ) :=
  buildMap (fun G0 (i : Fin K) => modMul N G0 p Bp (S i k) iv) (constReg B 0) G (List.finRange K)

lemma tBlock_spec {N K B p Bp : ℕ} (hN : 2 ≤ N) (hp : 0 < p)
    (hpB : p ≤ 2 ^ Bp) (hB : p * 2 ^ Bp ≤ 2 ^ B) {G : List BGate}
    {S : Fin K → Fin K → Fin B → ℕ} (k : Fin K) {iv : Fin B → ℕ}
    (hWF : WF N G) (hS : ∀ i j, RegOK N G (S i j)) (hiv : RegOK N G iv) :
    let res := tBlock N p Bp S k iv G
    Extends G res.1 ∧ res.1.length ≤ G.length + K * (14 * B * B) ∧ WF N res.1 ∧
    (∀ i, RegOK N res.1 (res.2 i)) ∧
    ∀ src, HasBase src N → ∀ (Sm : Fin K → ZMod p) (ivx : ZMod p),
      (∀ i, Rep p G src (S i k) (Sm i)) → Rep p G src iv ivx →
      ∀ i, Rep p res.1 src (res.2 i) (Sm i * ivx) := by
  dsimp only [tBlock]
  set tStep : List BGate → Fin K → List BGate × (Fin B → ℕ) :=
    fun G0 i => modMul N G0 p Bp (S i k) iv
  set tValid : List BGate → (Fin B → ℕ) → Prop := fun G0 r => RegOK N G0 r
  set tSpec : List BGate → Fin K → (Fin B → ℕ) → Prop :=
    fun G0 i r => ∀ (src : List Bool), HasBase src N → ∀ (Sm : Fin K → ZMod p) (ivx : ZMod p),
      (∀ i, Rep p G src (S i k) (Sm i)) → Rep p G src iv ivx →
      Rep p G0 src r (Sm i * ivx)
  have htR := buildMap_spec (N := N) (cost := 14 * B * B) tStep tValid tSpec
    (fun {G1 G2 t} he hv => regOK_extends he hv)
    (fun {G1 G2 b t} he hv hs src hbase Sm ivx h1 h2 =>
      rep_extends he hbase.1 hv (hs src hbase Sm ivx h1 h2))
    (constReg B 0) (List.finRange K) (List.nodup_finRange K) G hWF (by
      intro G0 i _ hExt hWF0
      have hm := modMul_spec hN hp hpB hB hWF0 (regOK_extends hExt (hS i k))
        (regOK_extends hExt hiv)
      refine ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, ?_⟩
      intro src hbase Sm ivx h1 h2
      exact hm.2.2.2.2 src hbase _ _ (rep_extends hExt hbase.1 (hS i k) (h1 i))
        (rep_extends hExt hbase.1 hiv h2))
  refine ⟨htR.1, ?_, htR.2.2.1, fun i => (htR.2.2.2 i (List.mem_finRange i)).1, ?_⟩
  · have := htR.2.1
    rw [List.length_finRange] at this
    rw [Nat.mul_comm K]
    exact this
  · intro src hbase Sm ivx h1 h2 i
    exact (htR.2.2.2 i (List.mem_finRange i)).2 src hbase Sm ivx h1 h2

def eCell (N : ℕ) {B : ℕ} (p Bp : ℕ) (go : ℕ) (t sKj sIj : Fin B → ℕ) (G0 : List BGate) :
    List BGate × (Fin B → ℕ) :=
  let m := modMul N G0 p Bp t sKj
  let s := modSub N m.1 p sIj m.2
  regMux N s.1 go s.2 sIj

lemma eCell_spec {N B p Bp : ℕ} (hN : 2 ≤ N) (hp : 3 ≤ p)
    (hpB : p ≤ 2 ^ Bp) (hB : p * 2 ^ Bp ≤ 2 ^ B) {G0 : List BGate} {go : ℕ}
    {t sKj sIj : Fin B → ℕ} (hWF : WF N G0) (ht : RegOK N G0 t) (hk : RegOK N G0 sKj)
    (hi : RegOK N G0 sIj) (hgo : go < N + G0.length) :
    let res := eCell N p Bp go t sKj sIj G0
    Extends G0 res.1 ∧ res.1.length ≤ G0.length + (14 * B * B + 21 * B) ∧ WF N res.1 ∧
    RegOK N res.1 res.2 ∧
    ∀ src, HasBase src N → ∀ (x y z : ZMod p) (b : Bool),
      Rep p G0 src t x → Rep p G0 src sKj y → Rep p G0 src sIj z → evalW G0 src go = b →
      Rep p res.1 src res.2 (if b then z - x * y else z) := by
  have hp0 : 0 < p := by omega
  have h2p := two_p_le hpB hp hB
  dsimp only [eCell]
  have hm := modMul_spec hN hp0 hpB hB hWF ht hk
  set m := modMul N G0 p Bp t sKj
  have hi1 : RegOK N m.1 sIj := regOK_extends hm.1 hi
  have hs := modSub_spec hN hp0 h2p hm.2.2.1 hi1 hm.2.2.2.1
  set s := modSub N m.1 p sIj m.2
  have hgo2 : go < N + s.1.length := by
    have := extends_len (extends_trans hm.1 hs.1); omega
  have hmx := regMux_spec hs.2.2.1 hgo2 hs.2.2.2.1 (regOK_extends hs.1 hi1)
  refine ⟨extends_trans hm.1 (extends_trans hs.1 hmx.1), ?_, hmx.2.2.1, hmx.2.2.2.1, ?_⟩
  · have h1 := hm.2.1
    have h2 := hs.2.1
    have h3 := hmx.2.1
    omega
  · intro src hbase x y z b hx hy hz hb
    have hmr := hm.2.2.2.2 src hbase _ _ hx hy
    have hz1 : Rep p m.1 src sIj z := rep_extends hm.1 hbase.1 hi hz
    have hsr := hs.2.2.2.2 src hbase _ _ hz1 hmr
    have hval := hmx.2.2.2.2 src hbase.1
    rw [evalW_extends (extends_trans hm.1 hs.1) (by rw [hbase.1]; exact hgo), hb] at hval
    unfold Rep
    rw [hval]
    cases b
    · exact rep_extends hs.1 hbase.1 hi1 hz1
    · exact hsr

noncomputable def eBlock (N : ℕ) {K B : ℕ} (p Bp : ℕ) (go : ℕ) (S : Fin K → Fin K → Fin B → ℕ)
    (k : Fin K) (t : Fin K → Fin B → ℕ) (G : List BGate) :
    List BGate × (Fin K × Fin K → Fin B → ℕ) :=
  buildMap (fun G0 (ij : Fin K × Fin K) => eCell N p Bp go (t ij.1) (S k ij.2) (S ij.1 ij.2) G0)
    (constReg B 0) G (Finset.univ : Finset (Fin K × Fin K)).toList

lemma eBlock_spec {N K B p Bp : ℕ} (hN : 2 ≤ N) (hp : 3 ≤ p)
    (hpB : p ≤ 2 ^ Bp) (hB : p * 2 ^ Bp ≤ 2 ^ B) {G : List BGate} {go : ℕ}
    {S : Fin K → Fin K → Fin B → ℕ} (k : Fin K) {t : Fin K → Fin B → ℕ}
    (hWF : WF N G) (hS : ∀ i j, RegOK N G (S i j)) (ht : ∀ i, RegOK N G (t i))
    (hgo : go < N + G.length) :
    let res := eBlock N p Bp go S k t G
    Extends G res.1 ∧ res.1.length ≤ G.length + K * K * (14 * B * B + 21 * B) ∧ WF N res.1 ∧
    (∀ ij, RegOK N res.1 (res.2 ij)) ∧
    ∀ src, HasBase src N → ∀ (Sm : Fin K → Fin K → ZMod p) (tm : Fin K → ZMod p) (b : Bool),
      (∀ i j, Rep p G src (S i j) (Sm i j)) → (∀ i, Rep p G src (t i) (tm i)) →
      evalW G src go = b →
      ∀ i j, Rep p res.1 src (res.2 (i, j)) (if b then Sm i j - tm i * Sm k j else Sm i j) := by
  dsimp only [eBlock]
  set eStep : List BGate → Fin K × Fin K → List BGate × (Fin B → ℕ) :=
    fun G0 ij => eCell N p Bp go (t ij.1) (S k ij.2) (S ij.1 ij.2) G0
  set eValid : List BGate → (Fin B → ℕ) → Prop := fun G0 r => RegOK N G0 r
  set eSpec : List BGate → Fin K × Fin K → (Fin B → ℕ) → Prop :=
    fun G0 ij r => ∀ (src : List Bool), HasBase src N →
      ∀ (Sm : Fin K → Fin K → ZMod p) (tm : Fin K → ZMod p) (b : Bool),
      (∀ i j, Rep p G src (S i j) (Sm i j)) → (∀ i, Rep p G src (t i) (tm i)) →
      evalW G src go = b →
      Rep p G0 src r (if b then Sm ij.1 ij.2 - tm ij.1 * Sm k ij.2 else Sm ij.1 ij.2)
  have heR := buildMap_spec (N := N) (cost := 14 * B * B + 21 * B) eStep eValid eSpec
    (fun {G1 G2 t} he hv => regOK_extends he hv)
    (fun {G1 G2 b t} he hv hs src hbase Sm tm bb h1 h2 h3 =>
      rep_extends he hbase.1 hv (hs src hbase Sm tm bb h1 h2 h3))
    (constReg B 0) (Finset.univ : Finset (Fin K × Fin K)).toList (Finset.nodup_toList _) G hWF (by
      intro G0 ij _ hExt hWF0
      have hgo0 : go < N + G0.length := by have := extends_len hExt; omega
      have hc := eCell_spec hN hp hpB hB hWF0 (regOK_extends hExt (ht ij.1))
        (regOK_extends hExt (hS k ij.2)) (regOK_extends hExt (hS ij.1 ij.2)) hgo0
      refine ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, ?_⟩
      intro src hbase Sm tm bb h1 h2 h3
      apply hc.2.2.2.2 src hbase _ _ _ bb (rep_extends hExt hbase.1 (ht ij.1) (h2 ij.1))
        (rep_extends hExt hbase.1 (hS k ij.2) (h1 k ij.2))
        (rep_extends hExt hbase.1 (hS ij.1 ij.2) (h1 ij.1 ij.2))
      rw [evalW_extends hExt (by rw [hbase.1]; exact hgo), h3])
  have hmem : ∀ ij : Fin K × Fin K, ij ∈ (Finset.univ : Finset (Fin K × Fin K)).toList :=
    fun ij => Finset.mem_toList.mpr (Finset.mem_univ _)
  refine ⟨heR.1, ?_, heR.2.2.1, fun ij => (heR.2.2.2 ij (hmem ij)).1, ?_⟩
  · have := heR.2.1
    have hpairs : ((Finset.univ : Finset (Fin K × Fin K)).toList).length = K * K := by simp
    rw [hpairs] at this
    rw [Nat.mul_comm (K * K)]
    exact this
  · intro src hbase Sm tm b h1 h2 h3 i j
    exact (heR.2.2.2 (i, j) (hmem (i, j))).2 src hbase Sm tm b h1 h2 h3

def tailBlock (N : ℕ) {B : ℕ} (p Bp : ℕ) (go : ℕ) (den s : Fin B → ℕ) (G : List BGate) :
    List BGate × (Fin B → ℕ) :=
  let dm := modMul N G p Bp den s
  regMux N dm.1 go dm.2 den

lemma tailBlock_spec {N B p Bp : ℕ} (hN : 2 ≤ N) (hp : 0 < p)
    (hpB : p ≤ 2 ^ Bp) (hB : p * 2 ^ Bp ≤ 2 ^ B) {G : List BGate} {go : ℕ}
    {den s : Fin B → ℕ} (hWF : WF N G) (hd : RegOK N G den) (hs : RegOK N G s)
    (hgo : go < N + G.length) :
    let res := tailBlock N p Bp go den s G
    Extends G res.1 ∧ res.1.length ≤ G.length + (14 * B * B + 3 * B) ∧ WF N res.1 ∧
    RegOK N res.1 res.2 ∧
    ∀ src, HasBase src N → ∀ (x y : ZMod p) (b : Bool),
      Rep p G src den x → Rep p G src s y → evalW G src go = b →
      Rep p res.1 src res.2 (if b then x * y else x) := by
  dsimp only [tailBlock]
  have hm := modMul_spec hN hp hpB hB hWF hd hs
  set dm := modMul N G p Bp den s
  have hgo2 : go < N + dm.1.length := by have := extends_len hm.1; omega
  have hmx := regMux_spec hm.2.2.1 hgo2 hm.2.2.2.1 (regOK_extends hm.1 hd)
  refine ⟨extends_trans hm.1 hmx.1, ?_, hmx.2.2.1, hmx.2.2.2.1, ?_⟩
  · have := hm.2.1; have := hmx.2.1; omega
  · intro src hbase x y b hx hy hb
    have hval := hmx.2.2.2.2 src hbase.1
    rw [evalW_extends hm.1 (by rw [hbase.1]; exact hgo), hb] at hval
    unfold Rep
    rw [hval]
    cases b
    · exact rep_extends hm.1 hbase.1 hd hx
    · exact hm.2.2.2.2 src hbase _ _ hx hy

noncomputable def elimStepC (N : ℕ) {K B : ℕ} (p Bp : ℕ) (k : Fin K) (G : List BGate)
    (S : Fin K → Fin K → Fin B → ℕ) (den : Fin B → ℕ) (stop : ℕ) :
    List BGate × (Fin K → Fin K → Fin B → ℕ) × (Fin B → ℕ) × ℕ :=
  let h := headBlock N p Bp (S k k) stop G
  let t := tBlock N p Bp S k h.2.2.2 h.1
  let e := eBlock N p Bp h.2.1 S k t.2 t.1
  let d := tailBlock N p Bp h.2.1 den (S k k) e.1
  (d.1, fun i j => e.2 (i, j), d.2, h.2.2.1)

def stepCost (K B : ℕ) : ℕ :=
  28 * B * B * B + (K + 1) * (K + 1) * (14 * B * B + 21 * B) + 4 * B + 2

lemma stepCost_ge (K B : ℕ) :
    (28 * B * B * B + B + 2) + K * (14 * B * B) + K * K * (14 * B * B + 21 * B) +
      (14 * B * B + 3 * B) ≤ stepCost K B := by
  unfold stepCost
  have e1 : (K + 1) * (K + 1) * (14 * B * B + 21 * B) =
      K * K * (14 * B * B + 21 * B) + 2 * (K * (14 * B * B + 21 * B)) +
        (14 * B * B + 21 * B) := by ring
  have e2 : K * (14 * B * B) ≤ K * (14 * B * B + 21 * B) := Nat.mul_le_mul_left K (by omega)
  omega

lemma stepS_eq {F : Type*} [Field F] [DecidableEq F] (k : ℕ) (st : (ℕ → ℕ → F) × F × Bool) :
    stepS k st = if st.2.2 = false ∧ st.1 k k ≠ 0 then
      (fun i j => st.1 i j - st.1 i k * (st.1 k k)⁻¹ * st.1 k j, st.2.1 * st.1 k k, false)
    else (st.1, st.2.1, true) := rfl

lemma elimStepC_spec {N K B p Bp : ℕ} [Fact p.Prime] (hN : 2 ≤ N) (hp : 3 ≤ p)
    (hpB : p ≤ 2 ^ Bp) (hB : p * 2 ^ Bp ≤ 2 ^ B) (k : Fin K) {G : List BGate}
    {S : Fin K → Fin K → Fin B → ℕ} {den : Fin B → ℕ} {stop : ℕ}
    (hWF : WF N G) (hS : ∀ i j, RegOK N G (S i j)) (hden : RegOK N G den)
    (hstop : stop < N + G.length) :
    let res := elimStepC N p Bp k G S den stop
    Extends G res.1 ∧ res.1.length ≤ G.length + stepCost K B ∧ WF N res.1 ∧
    (∀ i j, RegOK N res.1 (res.2.1 i j)) ∧ RegOK N res.1 res.2.2.1 ∧
    res.2.2.2 < N + res.1.length ∧
    ∀ src, HasBase src N → ∀ st : (ℕ → ℕ → ZMod p) × ZMod p × Bool,
      (∀ i j : Fin K, Rep p G src (S i j) (st.1 i.val j.val)) →
      Rep p G src den st.2.1 → evalW G src stop = st.2.2 →
      (∀ i j : Fin K, Rep p res.1 src (res.2.1 i j) ((stepS k.val st).1 i.val j.val)) ∧
      Rep p res.1 src res.2.2.1 (stepS k.val st).2.1 ∧
      evalW res.1 src res.2.2.2 = (stepS k.val st).2.2 := by
  have hp0 : 0 < p := by omega
  dsimp only [elimStepC]
  have hh := headBlock_spec hN hp hpB hB hWF (hS k k) hstop
  set h := headBlock N p Bp (S k k) stop G
  have hS1 : ∀ i j, RegOK N h.1 (S i j) := fun i j => regOK_extends hh.1 (hS i j)
  have ht := tBlock_spec hN hp0 hpB hB k hh.2.2.1 hS1 hh.2.2.2.2.2.1
  set t := tBlock N p Bp S k h.2.2.2 h.1
  have hS2 : ∀ i j, RegOK N t.1 (S i j) := fun i j => regOK_extends ht.1 (hS1 i j)
  have hgo2 : h.2.1 < N + t.1.length := by have := extends_len ht.1; have := hh.2.2.2.1; omega
  have he := eBlock_spec hN hp hpB hB k ht.2.2.1 hS2 ht.2.2.2.1 hgo2
  set e := eBlock N p Bp h.2.1 S k t.2 t.1
  have heGe : Extends G e.1 := extends_trans hh.1 (extends_trans ht.1 he.1)
  have hgo3 : h.2.1 < N + e.1.length := by have := extends_len he.1; omega
  have hd := tailBlock_spec hN hp0 hpB hB he.2.2.1 (regOK_extends heGe hden)
    (regOK_extends heGe (hS k k)) hgo3
  set d := tailBlock N p Bp h.2.1 den (S k k) e.1
  refine ⟨extends_trans heGe hd.1, ?_, hd.2.2.1, fun i j => regOK_extends hd.1 (he.2.2.2.1 (i, j)),
    hd.2.2.2.1, ?_, ?_⟩
  · have l1 := hh.2.1
    have l2 := ht.2.1
    have l3 := he.2.1
    have l4 := hd.2.1
    have := stepCost_ge K B
    omega
  · have := extends_len (extends_trans ht.1 (extends_trans he.1 hd.1))
    have := hh.2.2.2.2.1
    omega
  · intro src hbase stt hSm hdenr hstopv
    have hhr := hh.2.2.2.2.2.2 src hbase _ _ (hSm k k) hstopv
    have hS1r : ∀ i j : Fin K, Rep p h.1 src (S i j) (stt.1 i.val j.val) :=
      fun i j => rep_extends hh.1 hbase.1 (hS i j) (hSm i j)
    have htr := ht.2.2.2.2 src hbase (fun i => stt.1 i.val k.val) _ (fun i => hS1r i k) hhr.2.2
    have hS2r : ∀ i j : Fin K, Rep p t.1 src (S i j) (stt.1 i.val j.val) :=
      fun i j => rep_extends ht.1 hbase.1 (hS1 i j) (hS1r i j)
    have hgo_t : evalW t.1 src h.2.1 = (!stt.2.2 && decide (stt.1 k.val k.val ≠ 0)) := by
      rw [evalW_extends ht.1 (by rw [hbase.1]; exact hh.2.2.2.1), hhr.1]
    have her := he.2.2.2.2 src hbase (fun i j => stt.1 i.val j.val) _ _ hS2r htr hgo_t
    have hgo_e : evalW e.1 src h.2.1 = (!stt.2.2 && decide (stt.1 k.val k.val ≠ 0)) := by
      rw [evalW_extends he.1 (by rw [hbase.1]; exact hgo2), hgo_t]
    have hdr := hd.2.2.2.2 src hbase _ _ _ (rep_extends heGe hbase.1 hden hdenr)
      (rep_extends heGe hbase.1 (hS k k) (hSm k k)) hgo_e
    have hcond : (!stt.2.2 && decide (stt.1 k.val k.val ≠ 0)) = true ↔
        (stt.2.2 = false ∧ stt.1 k.val k.val ≠ 0) := by
      cases stt.2.2 <;> simp
    rw [stepS_eq]
    by_cases hc : stt.2.2 = false ∧ stt.1 k.val k.val ≠ 0
    · have hb : (!stt.2.2 && decide (stt.1 k.val k.val ≠ 0)) = true := hcond.mpr hc
      rw [if_pos hc]
      refine ⟨?_, ?_, ?_⟩
      · intro i j
        have := her i j
        rw [hb] at this
        simp only [ite_true] at this
        exact rep_extends hd.1 hbase.1 (he.2.2.2.1 (i, j)) this
      · rw [hb] at hdr; simpa using hdr
      · rw [evalW_extends (extends_trans ht.1 (extends_trans he.1 hd.1))
          (by rw [hbase.1]; exact hh.2.2.2.2.1), hhr.2.1, hb]
        rfl
    · have hb : (!stt.2.2 && decide (stt.1 k.val k.val ≠ 0)) = false := by
        cases hbb : (!stt.2.2 && decide (stt.1 k.val k.val ≠ 0))
        · rfl
        · exact absurd (hcond.mp hbb) hc
      rw [if_neg hc]
      refine ⟨?_, ?_, ?_⟩
      · intro i j
        have := her i j
        rw [hb] at this
        simp only [Bool.false_eq_true, ite_false] at this
        exact rep_extends hd.1 hbase.1 (he.2.2.2.1 (i, j)) this
      · rw [hb] at hdr; simpa using hdr
      · rw [evalW_extends (extends_trans ht.1 (extends_trans he.1 hd.1))
          (by rw [hbase.1]; exact hh.2.2.2.2.1), hhr.2.1, hb]
        rfl

noncomputable def elimRunC (N : ℕ) {K B : ℕ} (p Bp : ℕ) (G : List BGate)
    (S0 : Fin K → Fin K → Fin B → ℕ) : (s : ℕ) → s ≤ K →
    List BGate × (Fin K → Fin K → Fin B → ℕ) × (Fin B → ℕ) × ℕ
  | 0, _ => (G, S0, constReg B 1, 0)
  | s + 1, h =>
    let r := elimRunC N p Bp G S0 s (by omega)
    elimStepC N p Bp ⟨s, by omega⟩ r.1 r.2.1 r.2.2.1 r.2.2.2

lemma elimRunC_spec {N K B p Bp : ℕ} [Fact p.Prime] (hN : 2 ≤ N) (hp : 3 ≤ p)
    (hpB : p ≤ 2 ^ Bp) (hB : p * 2 ^ Bp ≤ 2 ^ B) {G : List BGate}
    {S0 : Fin K → Fin K → Fin B → ℕ} (hWF : WF N G) (hS0 : ∀ i j, RegOK N G (S0 i j)) :
    ∀ (s : ℕ) (hs : s ≤ K),
    let res := elimRunC N p Bp G S0 s hs
    Extends G res.1 ∧ res.1.length ≤ G.length + s * stepCost K B ∧ WF N res.1 ∧
    (∀ i j, RegOK N res.1 (res.2.1 i j)) ∧ RegOK N res.1 res.2.2.1 ∧
    res.2.2.2 < N + res.1.length ∧
    ∀ src, HasBase src N → ∀ A : ℕ → ℕ → ZMod p,
      (∀ i j : Fin K, Rep p G src (S0 i j) (A i.val j.val)) →
      (∀ i j : Fin K, Rep p res.1 src (res.2.1 i j) ((runS A s).1 i.val j.val)) ∧
      Rep p res.1 src res.2.2.1 (runS A s).2.1 ∧
      evalW res.1 src res.2.2.2 = (runS A s).2.2 := by
  intro s
  induction s with
  | zero =>
    intro hs
    refine ⟨extends_rfl G, by simp [elimRunC], hWF, hS0, constReg_ok hN G 1, by
      simp only [elimRunC]; omega, ?_⟩
    intro src hbase A hA
    have h1B : 1 < 2 ^ B := by
      have := Nat.le_mul_of_pos_right p (Nat.two_pow_pos Bp)
      omega
    have h1v : regVal G src (constReg B 1) = 1 := constReg_val_of_lt hbase h1B
    refine ⟨fun i j => hA i j, ⟨?_, ?_⟩, ?_⟩
    · simp only [elimRunC]; rw [h1v]; omega
    · simp only [elimRunC, runS]; rw [h1v]; simp
    · simp only [elimRunC, runS]; exact evalW_zero hbase
  | succ s ih =>
    intro hs
    have hr := ih (by omega)
    dsimp only [elimRunC]
    set r := elimRunC N p Bp G S0 s (by omega)
    have hst := elimStepC_spec hN hp hpB hB (⟨s, by omega⟩ : Fin K) hr.2.2.1 hr.2.2.2.1
      hr.2.2.2.2.1 hr.2.2.2.2.2.1
    refine ⟨extends_trans hr.1 hst.1, ?_, hst.2.2.1, hst.2.2.2.1, hst.2.2.2.2.1,
      hst.2.2.2.2.2.1, ?_⟩
    · have h1 := hr.2.1
      have h2 := hst.2.1
      have hmul : (s + 1) * stepCost K B = s * stepCost K B + stepCost K B := Nat.succ_mul s _
      omega
    · intro src hbase A hA
      have hrr := hr.2.2.2.2.2.2 src hbase A hA
      have := hst.2.2.2.2.2.2 src hbase (runS A s) hrr.1 hrr.2.1 hrr.2.2
      exact this

noncomputable def inW (d width : ℕ) (i : Fin (2 * d + 1) × Fin width) : ℕ :=
  2 + (Fintype.equivFin (Fin (2 * d + 1) × Fin width) i).val

noncomputable def momRn (d width B : ℕ) (j : ℕ) : Fin B → ℕ :=
  fun k => if h : j < 2 * d + 1 ∧ k.val < width then inW d width (⟨j, h.1⟩, ⟨k.val, h.2⟩) else 0

noncomputable def GR (d width B : ℕ) (s t : Fin (d + 1)) : Fin B → ℕ :=
  if s.val < d then (if t.val < d then momRn d width B (s.val + t.val + 1) else momRn d width B s.val)
  else (if t.val < d then momRn d width B t.val else fun _ => 0)

noncomputable def HR (d width B : ℕ) (s t : Fin (d + 1)) : Fin B → ℕ :=
  momRn d width B (s.val + t.val)

noncomputable def decC (d width p Bp B : ℕ) :
    List BGate × (Fin B → ℕ) × (Fin B → ℕ) × ℕ :=
  let T := 2 + Fintype.card (Fin (2 * d + 1) × Fin width)
  let e1 := elimRunC T p Bp [] (GR d width B) d (Nat.le_succ d)
  let nm := modMul T e1.1 p Bp e1.2.2.1 (e1.2.1 (Fin.last d) (Fin.last d))
  let nn := modSub T nm.1 p (fun _ => 0) nm.2
  let e2 := elimRunC T p Bp nn.1 (HR d width B) (d + 1) le_rfl
  (e2.1, nn.2, e1.2.2.1, e2.2.2.2)

lemma inW_lt (d width : ℕ) (i : Fin (2 * d + 1) × Fin width) :
    inW d width i < 2 + Fintype.card (Fin (2 * d + 1) × Fin width) := by
  unfold inW
  have := (Fintype.equivFin (Fin (2 * d + 1) × Fin width) i).isLt
  omega

lemma momRn_ok (d width B : ℕ) (G : List BGate) (j : ℕ) :
    RegOK (2 + Fintype.card (Fin (2 * d + 1) × Fin width)) G (momRn d width B j) := by
  intro k
  unfold momRn
  split
  · have := inW_lt d width (⟨j, by omega⟩, ⟨k.val, by omega⟩); omega
  · omega

lemma zeroReg_ok (N B : ℕ) (hN : 2 ≤ N) (G : List BGate) : RegOK N G (fun _ : Fin B => 0) := by
  intro k; show 0 < N + G.length; omega

lemma GR_ok (d width B : ℕ) (G : List BGate) (s t : Fin (d + 1)) :
    RegOK (2 + Fintype.card (Fin (2 * d + 1) × Fin width)) G (GR d width B s t) := by
  unfold GR
  split
  · split
    · exact momRn_ok d width B G _
    · exact momRn_ok d width B G _
  · split
    · exact momRn_ok d width B G _
    · exact zeroReg_ok _ B (by omega) G

lemma HR_ok (d width B : ℕ) (G : List BGate) (s t : Fin (d + 1)) :
    RegOK (2 + Fintype.card (Fin (2 * d + 1) × Fin width)) G (HR d width B s t) :=
  momRn_ok d width B G _

lemma zeroReg_val {N B : ℕ} {G : List BGate} {src : List Bool} (hb : HasBase src N) :
    regVal G src (fun _ : Fin B => 0) = 0 := by
  unfold regVal
  apply Finset.sum_eq_zero
  intro i _
  rw [evalW_zero hb]
  simp

lemma momRn_val {d width B : ℕ} (hwB : width ≤ B) {src : List Bool}
    (hb : HasBase src (2 + Fintype.card (Fin (2 * d + 1) × Fin width))) (j v : ℕ)
    (hj : j < 2 * d + 1) (hv : v < 2 ^ width)
    (hbits : ∀ k (hk : k < width), evalW [] src (inW d width (⟨j, hj⟩, ⟨k, hk⟩)) = v.testBit k) :
    regVal [] src (momRn d width B j) = v := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [regVal_testBit]
  by_cases hk : k < width
  · have hkB : k < B := by omega
    simp only [hkB, dite_true, momRn, hj, hk, and_self]
    exact hbits k hk
  · have hv2 : v.testBit k = false := by
      apply Nat.testBit_eq_false_of_lt
      calc v < 2 ^ width := hv
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
    rw [hv2]
    by_cases hkB : k < B
    · simp only [hkB, dite_true, momRn, hk, and_false, dite_false]
      exact evalW_zero hb
    · simp [hkB]

lemma rep_of_val {p B : ℕ} {G : List BGate} {src : List Bool} {r : Fin B → ℕ} {v : ℕ}
    (hv : regVal G src r = v) (hvp : v < p) : Rep p G src r (v : ZMod p) :=
  ⟨by rw [hv]; exact hvp, by rw [hv]⟩

lemma val_of_rep {p B : ℕ} [NeZero p] {G : List BGate} {src : List Bool} {r : Fin B → ℕ}
    {z : ZMod p} (h : Rep p G src r z) : regVal G src r = z.val := by
  rw [← h.2, ZMod.val_natCast_of_lt h.1]

section DecSem
variable {X : Type*} [Fintype X] [DecidableEq X]

lemma GR_rep {d width B p : ℕ} (hwB : width ≤ B) (hwp : 2 ^ width ≤ p) {src : List Bool}
    (hb : HasBase src (2 + Fintype.card (Fin (2 * d + 1) × Fin width))) (mult : X → ℕ)
    (hmom : ∀ j ≤ 2 * d + 1, mom mult j < 2 ^ width)
    (hbits : ∀ j k (hj : j < 2 * d) (hk : k < width),
      evalW [] src (inW d width (⟨j, by omega⟩, ⟨k, hk⟩)) = (mom mult (j + 1)).testBit k)
    (s t : Fin (d + 1)) :
    Rep p [] src (GR d width B s t) (((Ghat mult d s.val t.val : ℤ) : ZMod p)) := by
  have hmv : ∀ j, j < 2 * d → regVal [] src (momRn d width B j) = mom mult (j + 1) := by
    intro j hj
    exact momRn_val hwB hb j _ (by omega) (hmom (j + 1) (by omega)) (fun k hk => hbits j k hj hk)
  have hlt : ∀ j, j < 2 * d → mom mult (j + 1) < p := fun j hj =>
    lt_of_lt_of_le (hmom (j + 1) (by omega)) hwp
  unfold GR Ghat
  by_cases hs : s.val < d
  · by_cases ht : t.val < d
    · simp only [hs, ht, ite_true]
      have e : s.val + t.val + 2 = (s.val + t.val + 1) + 1 := by omega
      rw [e, Int.cast_natCast]
      exact rep_of_val (hmv _ (by omega)) (hlt _ (by omega))
    · simp only [hs, ht, ite_true, ite_false]
      rw [Int.cast_natCast]
      exact rep_of_val (hmv _ (by omega)) (hlt _ (by omega))
  · by_cases ht : t.val < d
    · simp only [hs, ht, ite_true, ite_false]
      rw [Int.cast_natCast]
      exact rep_of_val (hmv _ (by omega)) (hlt _ (by omega))
    · simp only [hs, ht, ite_false]
      have := rep_of_val (p := p) (zeroReg_val (G := []) (B := B) hb) (by
        have : 0 < 2 ^ width := Nat.two_pow_pos width
        omega)
      simpa using this

lemma HR_rep {d width B p : ℕ} (hwB : width ≤ B) (hwp : 2 ^ width ≤ p) {src : List Bool}
    (hb : HasBase src (2 + Fintype.card (Fin (2 * d + 1) × Fin width))) (mult : X → ℕ)
    (hmom : ∀ j ≤ 2 * d + 1, mom mult j < 2 ^ width)
    (hbits : ∀ j k (hj : j < 2 * d + 1) (hk : k < width),
      evalW [] src (inW d width (⟨j, hj⟩, ⟨k, hk⟩)) = (mom mult (j + 1)).testBit k)
    (s t : Fin (d + 1)) :
    Rep p [] src (HR d width B s t) (((Hone mult s.val t.val : ℤ) : ZMod p)) := by
  unfold HR Hone
  rw [Int.cast_natCast]
  have hj : s.val + t.val < 2 * d + 1 := by omega
  exact rep_of_val (momRn_val hwB hb _ _ hj (hmom _ (by omega)) (fun k hk => hbits _ k hj hk))
    (lt_of_lt_of_le (hmom _ (by omega)) hwp)

end DecSem

lemma decC_struct {d width p Bp B : ℕ} [Fact p.Prime] (hp : 3 ≤ p) (hpB : p ≤ 2 ^ Bp)
    (hB : p * 2 ^ Bp ≤ 2 ^ B) :
    let T := 2 + Fintype.card (Fin (2 * d + 1) × Fin width)
    let res := decC d width p Bp B
    res.1.length ≤ (2 * d + 1) * stepCost (d + 1) B + (14 * B * B + 18 * B) ∧ WF T res.1 ∧
    RegOK T res.1 res.2.1 ∧ RegOK T res.1 res.2.2.1 ∧ res.2.2.2 < T + res.1.length := by
  intro T
  have hT : 2 ≤ T := by omega
  have hp0 : 0 < p := by omega
  have h2p := two_p_le hpB hp hB
  dsimp only [decC]
  have hWF0 : WF T [] := fun i => Fin.elim0 i
  have he1 := elimRunC_spec hT hp hpB hB hWF0 (fun s t => GR_ok d width B [] s t) d (Nat.le_succ d)
  set e1 := elimRunC T p Bp [] (GR d width B) d (Nat.le_succ d)
  have hnm := modMul_spec hT hp0 hpB hB he1.2.2.1 he1.2.2.2.2.1 (he1.2.2.2.1 (Fin.last d) (Fin.last d))
  set nm := modMul T e1.1 p Bp e1.2.2.1 (e1.2.1 (Fin.last d) (Fin.last d))
  have hnn := modSub_spec hT hp0 h2p hnm.2.2.1 (zeroReg_ok T B hT _) hnm.2.2.2.1
  set nn := modSub T nm.1 p (fun _ => 0) nm.2
  have he2 := elimRunC_spec hT hp hpB hB hnn.2.2.1 (fun s t => HR_ok d width B nn.1 s t) (d + 1) le_rfl
  set e2 := elimRunC T p Bp nn.1 (HR d width B) (d + 1) le_rfl
  have hext : Extends nn.1 e2.1 := he2.1
  refine ⟨?_, he2.2.2.1, regOK_extends hext hnn.2.2.2.1, ?_, he2.2.2.2.2.2.1⟩
  · have l1 := he1.2.1
    have l2 := hnm.2.1
    have l3 := hnn.2.1
    have l4 := he2.2.1
    simp only [List.length_nil, Nat.zero_add] at l1
    have hmul : (2 * d + 1) * stepCost (d + 1) B = d * stepCost (d + 1) B + (d + 1) * stepCost (d + 1) B := by
      ring
    omega
  · exact regOK_extends (extends_trans hnm.1 (extends_trans hnn.1 hext)) he1.2.2.2.2.1

lemma decC_num {X : Type*} [Fintype X] [DecidableEq X] {d width p Bp B : ℕ} [Fact p.Prime]
    (hp : 3 ≤ p) (hpB : p ≤ 2 ^ Bp) (hB : p * 2 ^ Bp ≤ 2 ^ B) (hwB : width ≤ B)
    (hwp : 2 ^ width ≤ p) {src : List Bool}
    (hb : HasBase src (2 + Fintype.card (Fin (2 * d + 1) × Fin width))) (mult : X → ℕ)
    (hmom : ∀ j ≤ 2 * d + 1, mom mult j < 2 ^ width)
    (hbits : ∀ j k (hj : j < 2 * d) (hk : k < width),
      evalW [] src (inW d width (⟨j, by omega⟩, ⟨k, hk⟩)) = (mom mult (j + 1)).testBit k) :
    let res := decC d width p Bp B
    Rep p res.1 src res.2.1
      (-((runS (fun s t => ((Ghat mult d s t : ℤ) : ZMod p)) d).2.1 *
        (runS (fun s t => ((Ghat mult d s t : ℤ) : ZMod p)) d).1 d d)) ∧
    Rep p res.1 src res.2.2.1 (runS (fun s t => ((Ghat mult d s t : ℤ) : ZMod p)) d).2.1 := by
  set T := 2 + Fintype.card (Fin (2 * d + 1) × Fin width)
  have hT : 2 ≤ T := by omega
  have hp0 : 0 < p := by omega
  have h2p := two_p_le hpB hp hB
  dsimp only [decC]
  have hWF0 : WF T [] := fun i => Fin.elim0 i
  have he1 := elimRunC_spec hT hp hpB hB hWF0 (fun s t => GR_ok d width B [] s t) d (Nat.le_succ d)
  set e1 := elimRunC T p Bp [] (GR d width B) d (Nat.le_succ d)
  have hnm := modMul_spec hT hp0 hpB hB he1.2.2.1 he1.2.2.2.2.1 (he1.2.2.2.1 (Fin.last d) (Fin.last d))
  set nm := modMul T e1.1 p Bp e1.2.2.1 (e1.2.1 (Fin.last d) (Fin.last d))
  have hnn := modSub_spec hT hp0 h2p hnm.2.2.1 (zeroReg_ok T B hT _) hnm.2.2.2.1
  set nn := modSub T nm.1 p (fun _ => 0) nm.2
  have he2 := elimRunC_spec hT hp hpB hB hnn.2.2.1 (fun s t => HR_ok d width B nn.1 s t) (d + 1) le_rfl
  set e2 := elimRunC T p Bp nn.1 (HR d width B) (d + 1) le_rfl
  set A : ℕ → ℕ → ZMod p := fun s t => ((Ghat mult d s t : ℤ) : ZMod p)
  have hA : ∀ s t : Fin (d + 1), Rep p [] src (GR d width B s t) (A s.val t.val) :=
    fun s t => GR_rep hwB hwp hb mult hmom hbits s t
  have hr1 := he1.2.2.2.2.2.2 src hb A hA
  have hm := hnm.2.2.2.2 src hb _ _ hr1.2.1 (hr1.1 (Fin.last d) (Fin.last d))
  have hz := rep_of_val (p := p) (G := nm.1) (B := B) (zeroReg_val hb) hp0
  rw [Nat.cast_zero] at hz
  have hs := hnn.2.2.2.2 src hb _ _ hz hm
  rw [zero_sub] at hs
  refine ⟨rep_extends he2.1 hb.1 hnn.2.2.2.1 hs, ?_⟩
  exact rep_extends (extends_trans hnm.1 (extends_trans hnn.1 he2.1)) hb.1 he1.2.2.2.2.1 hr1.2.1

lemma decC_flag {X : Type*} [Fintype X] [DecidableEq X] {d width p Bp B : ℕ} [Fact p.Prime]
    (hp : 3 ≤ p) (hpB : p ≤ 2 ^ Bp) (hB : p * 2 ^ Bp ≤ 2 ^ B) (hwB : width ≤ B)
    (hwp : 2 ^ width ≤ p) {src : List Bool}
    (hb : HasBase src (2 + Fintype.card (Fin (2 * d + 1) × Fin width))) (mult : X → ℕ)
    (hmom : ∀ j ≤ 2 * d + 1, mom mult j < 2 ^ width)
    (hbits : ∀ j k (hj : j < 2 * d + 1) (hk : k < width),
      evalW [] src (inW d width (⟨j, hj⟩, ⟨k, hk⟩)) = (mom mult (j + 1)).testBit k) :
    let res := decC d width p Bp B
    evalW res.1 src res.2.2.2 = (runS (fun s t => ((Hone mult s t : ℤ) : ZMod p)) (d + 1)).2.2 := by
  set T := 2 + Fintype.card (Fin (2 * d + 1) × Fin width)
  have hT : 2 ≤ T := by omega
  have hp0 : 0 < p := by omega
  have h2p := two_p_le hpB hp hB
  dsimp only [decC]
  have hWF0 : WF T [] := fun i => Fin.elim0 i
  have he1 := elimRunC_spec hT hp hpB hB hWF0 (fun s t => GR_ok d width B [] s t) d (Nat.le_succ d)
  set e1 := elimRunC T p Bp [] (GR d width B) d (Nat.le_succ d)
  have hnm := modMul_spec hT hp0 hpB hB he1.2.2.1 he1.2.2.2.2.1 (he1.2.2.2.1 (Fin.last d) (Fin.last d))
  set nm := modMul T e1.1 p Bp e1.2.2.1 (e1.2.1 (Fin.last d) (Fin.last d))
  have hnn := modSub_spec hT hp0 h2p hnm.2.2.1 (zeroReg_ok T B hT _) hnm.2.2.2.1
  set nn := modSub T nm.1 p (fun _ => 0) nm.2
  have he2 := elimRunC_spec hT hp hpB hB hnn.2.2.1 (fun s t => HR_ok d width B nn.1 s t) (d + 1) le_rfl
  set e2 := elimRunC T p Bp nn.1 (HR d width B) (d + 1) le_rfl
  have heN : Extends [] nn.1 := extends_trans he1.1 (extends_trans hnm.1 hnn.1)
  have hA : ∀ s t : Fin (d + 1), Rep p nn.1 src (HR d width B s t)
      (((Hone mult s.val t.val : ℤ) : ZMod p)) :=
    fun s t => rep_extends heN hb.1 (HR_ok d width B [] s t) (HR_rep hwB hwp hb mult hmom hbits s t)
  exact (he2.2.2.2.2.2.2 src hb _ hA).2.2

lemma factorial_le_two_pow_sq : ∀ k : ℕ, k.factorial ≤ 2 ^ (k * k)
  | 0 => by simp
  | k + 1 => by
    have ih := factorial_le_two_pow_sq k
    have hlin : k + 1 ≤ 2 ^ (k + 1) := Nat.le_of_lt (Nat.lt_two_pow_self)
    calc (k + 1).factorial = (k + 1) * k.factorial := Nat.factorial_succ k
      _ ≤ 2 ^ (k + 1) * 2 ^ (k * k) := Nat.mul_le_mul hlin ih
      _ = 2 ^ (k + 1 + k * k) := (Nat.pow_add 2 _ _).symm
      _ ≤ 2 ^ ((k + 1) * (k + 1)) := Nat.pow_le_pow_right (by omega) (by nlinarith)

lemma src_getD {m : ℕ} (f : Fin m → Bool) (i : Fin m) :
    ([false, true] ++ List.ofFn f).getD (2 + i.val) false = f i := by
  rw [getD_append_right _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

lemma src_hasBase {m : ℕ} (f : Fin m → Bool) : HasBase ([false, true] ++ List.ofFn f) (2 + m) := by
  refine ⟨by simp; omega, by simp, by simp⟩

lemma evalW_nil_src {m : ℕ} (f : Fin m → Bool) (i : Fin m) :
    evalW [] ([false, true] ++ List.ofFn f) (2 + i.val) = f i := by
  unfold evalW runW
  exact src_getD f i

lemma sum_digits_eq {N B D : ℕ} {G : List BGate} {src : List Bool} (hb : HasBase src N)
    (hBD : B ≤ D) (r : Fin B → ℕ) :
    ∑ k : Fin D, (evalW G src (if h : k.val < B then r ⟨k.val, h⟩ else 0)).toNat * 2 ^ k.val =
      regVal G src r := by
  have h1 : ∑ k : Fin D, (evalW G src (if h : k.val < B then r ⟨k.val, h⟩ else 0)).toNat * 2 ^ k.val =
      ∑ k ∈ Finset.range D, (evalW G src (if h : k < B then r ⟨k, h⟩ else 0)).toNat * 2 ^ k :=
    Fin.sum_univ_eq_sum_range (fun k => (evalW G src (if h : k < B then r ⟨k, h⟩ else 0)).toNat * 2 ^ k) D
  have h2 : regVal G src r =
      ∑ k ∈ Finset.range B, (evalW G src (if h : k < B then r ⟨k, h⟩ else 0)).toNat * 2 ^ k := by
    unfold regVal
    rw [← sum_fin_eq_range (fun k => (evalW G src (if h : k < B then r ⟨k, h⟩ else 0)).toNat * 2 ^ k)]
    apply Finset.sum_congr rfl
    intro i _
    simp [i.isLt]
  rw [h1, h2]
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr hBD)
  intro k _ hk
  have hkB : ¬ k < B := by simpa using hk
  simp only [hkB, dite_false, evalW_zero hb, Bool.toNat_false, zero_mul]

def Efun (d width : ℕ) : ℕ := (d + 1) * (d + 1) + width * (d + 1)

def Bfun (d width : ℕ) : ℕ := 2 * (Efun d width + 1)

def decBound (d width : ℕ) : ℕ :=
  (2 * d + 1) * stepCost (d + 1) (Bfun d width) + (14 * Bfun d width * Bfun d width + 18 * Bfun d width)

noncomputable def outF (d width B : ℕ) (num den : Fin B → ℕ) (flag : ℕ) :
    (Bool × Fin (16 * (d + 2) ^ 2 * (width + 1))) ⊕ Unit → ℕ :=
  Sum.elim (fun sk => if h : sk.2.val < B then (if sk.1 then den else num) ⟨sk.2.val, h⟩ else 0)
    (fun _ => flag)

lemma prime_params (d width : ℕ) :
    ∃ p, Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 2 ^ (Efun d width + 1) ∧
      p * 2 ^ (Efun d width + 1) ≤ 2 ^ Bfun d width ∧ width ≤ Bfun d width ∧
      2 ^ width ≤ p ∧ (d + 1).factorial * (2 ^ width) ^ (d + 1) < p ∧
      Bfun d width ≤ 16 * (d + 2) ^ 2 * (width + 1) := by
  have hE1 : 1 ≤ Efun d width := by unfold Efun; nlinarith
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (2 ^ Efun d width)
    (by positivity)
  have h2E : 2 ≤ 2 ^ Efun d width := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ Efun d width := Nat.pow_le_pow_right (by omega) hE1
  have hpB : p ≤ 2 ^ (Efun d width + 1) := by rw [Nat.pow_succ]; omega
  refine ⟨p, hp, by omega, hpB, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Bfun
    calc p * 2 ^ (Efun d width + 1) ≤ 2 ^ (Efun d width + 1) * 2 ^ (Efun d width + 1) :=
          Nat.mul_le_mul_right _ hpB
      _ = 2 ^ (2 * (Efun d width + 1)) := by rw [← Nat.pow_add]; congr 1; ring
  · unfold Bfun Efun; nlinarith
  · have : 2 ^ width ≤ 2 ^ Efun d width := Nat.pow_le_pow_right (by omega) (by unfold Efun; nlinarith)
    omega
  · have hf := factorial_le_two_pow_sq (d + 1)
    calc (d + 1).factorial * (2 ^ width) ^ (d + 1) ≤ 2 ^ ((d + 1) * (d + 1)) * 2 ^ (width * (d + 1)) := by
          rw [← Nat.pow_mul]; exact Nat.mul_le_mul_right _ hf
      _ = 2 ^ Efun d width := by rw [← Nat.pow_add]; rfl
      _ < p := hlt
  · unfold Bfun Efun; nlinarith

noncomputable def decSrc (d width : ℕ) (rd : Fin (2 * d + 1) × Fin width → Bool) (keep : Bool) :
    List Bool :=
  [false, true] ++ List.ofFn (fun j : Fin (Fintype.card (Fin (2 * d + 1) × Fin width)) =>
    (keep || decide (((Fintype.equivFin (Fin (2 * d + 1) × Fin width)).symm j).1.val < 2 * d)) &&
      rd ((Fintype.equivFin (Fin (2 * d + 1) × Fin width)).symm j))

lemma decSrc_hasBase (d width : ℕ) (rd : Fin (2 * d + 1) × Fin width → Bool) (keep : Bool) :
    HasBase (decSrc d width rd keep) (2 + Fintype.card (Fin (2 * d + 1) × Fin width)) :=
  src_hasBase _

lemma decSrc_eval (d width : ℕ) (rd : Fin (2 * d + 1) × Fin width → Bool) (keep : Bool)
    (i : Fin (2 * d + 1) × Fin width) :
    evalW [] (decSrc d width rd keep) (inW d width i) = ((keep || decide (i.1.val < 2 * d)) && rd i) := by
  unfold decSrc inW
  rw [evalW_nil_src]
  simp

lemma dec_ok (d width : ℕ) (hd : 0 < d) :
    ∃ (dec : List BGate) (out : (Bool × Fin (16 * (d + 2) ^ 2 * (width + 1))) ⊕ Unit → ℕ),
      dec.length ≤ decBound d width ∧
      WF (2 + Fintype.card (Fin (2 * d + 1) × Fin width)) dec ∧
      (∀ o, out o < 2 + Fintype.card (Fin (2 * d + 1) × Fin width) + dec.length) ∧
      ∀ {X : Type} [Fintype X] [DecidableEq X] (mult : X → ℕ)
        (rd : Fin (2 * d + 1) × Fin width → Bool),
        (∀ j ≤ 2 * d + 1, mom mult j < 2 ^ width) →
        (∀ i, rd i = (mom mult (i.1.val + 1)).testBit i.2.val) →
        0 < (∑ k : Fin (16 * (d + 2) ^ 2 * (width + 1)),
          ((runW dec (decSrc d width rd false)).getD (out (Sum.inl (true, k))) false).toNat * 2 ^ k.val) ∧
        (∀ coeff, fitQ mult d coeff ≤
          ((∑ k : Fin (16 * (d + 2) ^ 2 * (width + 1)),
            ((runW dec (decSrc d width rd false)).getD (out (Sum.inl (false, k))) false).toNat * 2 ^ k.val : ℕ) : ℚ) /
          ((∑ k : Fin (16 * (d + 2) ^ 2 * (width + 1)),
            ((runW dec (decSrc d width rd false)).getD (out (Sum.inl (true, k))) false).toNat * 2 ^ k.val : ℕ) : ℚ)) ∧
        (∃ coeff, fitQ mult d coeff =
          ((∑ k : Fin (16 * (d + 2) ^ 2 * (width + 1)),
            ((runW dec (decSrc d width rd false)).getD (out (Sum.inl (false, k))) false).toNat * 2 ^ k.val : ℕ) : ℚ) /
          ((∑ k : Fin (16 * (d + 2) ^ 2 * (width + 1)),
            ((runW dec (decSrc d width rd false)).getD (out (Sum.inl (true, k))) false).toNat * 2 ^ k.val : ℕ) : ℚ)) ∧
        ((∑ k : Fin (16 * (d + 2) ^ 2 * (width + 1)),
            ((runW dec (decSrc d width rd false)).getD (out (Sum.inl (false, k))) false).toNat * 2 ^ k.val : ℕ) : ℚ) /
          ((∑ k : Fin (16 * (d + 2) ^ 2 * (width + 1)),
            ((runW dec (decSrc d width rd false)).getD (out (Sum.inl (true, k))) false).toNat * 2 ^ k.val : ℕ) : ℚ)
          ≤ ((wordsF mult).card : ℚ) ∧
        (((∑ k : Fin (16 * (d + 2) ^ 2 * (width + 1)),
            ((runW dec (decSrc d width rd false)).getD (out (Sum.inl (false, k))) false).toNat * 2 ^ k.val : ℕ) : ℚ) /
          ((∑ k : Fin (16 * (d + 2) ^ 2 * (width + 1)),
            ((runW dec (decSrc d width rd false)).getD (out (Sum.inl (true, k))) false).toNat * 2 ^ k.val : ℕ) : ℚ)
          = ((wordsF mult).card : ℚ) ↔
          (runW dec (decSrc d width rd true)).getD (out (Sum.inr ())) false = true) ∧
        ((runW dec (decSrc d width rd true)).getD (out (Sum.inr ())) false = true ↔
          levelsN mult ≤ d) := by
  obtain ⟨p, hpp, hp3, hpB, hB, hwB, hwp, hfact, hBD⟩ := prime_params d width
  haveI : Fact p.Prime := ⟨hpp⟩
  have hs := decC_struct (d := d) (width := width) hp3 hpB hB
  refine ⟨(decC d width p (Efun d width + 1) (Bfun d width)).1,
    outF d width (Bfun d width) (decC d width p (Efun d width + 1) (Bfun d width)).2.1
      (decC d width p (Efun d width + 1) (Bfun d width)).2.2.1
      (decC d width p (Efun d width + 1) (Bfun d width)).2.2.2, hs.1, hs.2.1, ?_, ?_⟩
  · intro o
    rcases o with ⟨side, k⟩ | u
    · simp only [outF, Sum.elim_inl]
      split
      · cases side
        · exact hs.2.2.1 _
        · exact hs.2.2.2.1 _
      · omega
    · simp only [outF, Sum.elim_inr]
      exact hs.2.2.2.2
  · intro X _ _ mult rd hmom hrd
    have hbF := decSrc_hasBase d width rd false
    have hbT := decSrc_hasBase d width rd true
    have hbitsF : ∀ j k (hj : j < 2 * d) (hk : k < width),
        evalW [] (decSrc d width rd false) (inW d width (⟨j, by omega⟩, ⟨k, hk⟩)) =
          (mom mult (j + 1)).testBit k := by
      intro j k hj hk
      rw [decSrc_eval, hrd]
      simp [hj]
    have hbitsT : ∀ j k (hj : j < 2 * d + 1) (hk : k < width),
        evalW [] (decSrc d width rd true) (inW d width (⟨j, hj⟩, ⟨k, hk⟩)) =
          (mom mult (j + 1)).testBit k := by
      intro j k hj hk
      rw [decSrc_eval, hrd]
      simp
    have hnum := decC_num hp3 hpB hB hwB hwp hbF mult hmom hbitsF
    have hflag := decC_flag hp3 hpB hB hwB hwp hbT mult hmom hbitsT
    have hnumF : (∑ k : Fin (16 * (d + 2) ^ 2 * (width + 1)),
        ((runW (decC d width p (Efun d width + 1) (Bfun d width)).1 (decSrc d width rd false)).getD
          (outF d width (Bfun d width) (decC d width p (Efun d width + 1) (Bfun d width)).2.1
            (decC d width p (Efun d width + 1) (Bfun d width)).2.2.1
            (decC d width p (Efun d width + 1) (Bfun d width)).2.2.2 (Sum.inl (false, k)))
          false).toNat * 2 ^ k.val) =
        (-((runS (fun s t => ((Ghat mult d s t : ℤ) : ZMod p)) d).2.1 *
          (runS (fun s t => ((Ghat mult d s t : ℤ) : ZMod p)) d).1 d d)).val := by
      rw [← val_of_rep hnum.1, ← sum_digits_eq hbF hBD]
      rfl
    have hdenT : (∑ k : Fin (16 * (d + 2) ^ 2 * (width + 1)),
        ((runW (decC d width p (Efun d width + 1) (Bfun d width)).1 (decSrc d width rd false)).getD
          (outF d width (Bfun d width) (decC d width p (Efun d width + 1) (Bfun d width)).2.1
            (decC d width p (Efun d width + 1) (Bfun d width)).2.2.1
            (decC d width p (Efun d width + 1) (Bfun d width)).2.2.2 (Sum.inl (true, k)))
          false).toNat * 2 ^ k.val) =
        (runS (fun s t => ((Ghat mult d s t : ℤ) : ZMod p)) d).2.1.val := by
      rw [← val_of_rep hnum.2, ← sum_digits_eq hbF hBD]
      rfl
    have hfl : (runW (decC d width p (Efun d width + 1) (Bfun d width)).1 (decSrc d width rd true)).getD
        (outF d width (Bfun d width) (decC d width p (Efun d width + 1) (Bfun d width)).2.1
          (decC d width p (Efun d width + 1) (Bfun d width)).2.2.1
          (decC d width p (Efun d width + 1) (Bfun d width)).2.2.2 (Sum.inr ())) false =
        (runS (fun s t => ((Hone mult s t : ℤ) : ZMod p)) (d + 1)).2.2 := hflag
    rw [hnumF, hdenT, hfl]
    have hv := value_thm mult d hd p width hmom hfact
    have hf := flag_thm mult d p width hmom hfact
    refine ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, ?_, hf⟩
    rw [hv.2.2.2.2, hf]

lemma maskWords_true (n : ℕ) : maskWords (fun (_ : Fin n) (_ : Bool) => true) = Finset.univ := by
  unfold maskWords
  simp

lemma pow_lt_width (n q d j : ℕ) (hj : j ≤ 2 * d + 1) :
    2 ^ n * q ^ (n * j) < 2 ^ (4 * (n + 1) * (2 * d + 1 + 1) * (Nat.clog 2 (q + 2) + 1)) := by
  have hq : q ≤ 2 ^ Nat.clog 2 (q + 2) := le_trans (by omega) (Nat.le_pow_clog (by decide) (q + 2))
  have hqp : q ^ (n * j) ≤ (2 ^ Nat.clog 2 (q + 2)) ^ (n * j) := Nat.pow_le_pow_left hq _
  rw [← Nat.pow_mul] at hqp
  calc 2 ^ n * q ^ (n * j)
      ≤ 2 ^ n * 2 ^ (Nat.clog 2 (q + 2) * (n * j)) := Nat.mul_le_mul_left _ hqp
    _ = 2 ^ (n + Nat.clog 2 (q + 2) * (n * j)) := (Nat.pow_add 2 _ _).symm
    _ < 2 ^ (4 * (n + 1) * (2 * d + 1 + 1) * (Nat.clog 2 (q + 2) + 1)) := by
        apply Nat.pow_lt_pow_right (by omega)
        set c := Nat.clog 2 (q + 2)
        have h1 : n * j ≤ n * (2 * d + 2) := Nat.mul_le_mul_left n (by omega)
        have h2 : c * (n * j) ≤ c * (n * (2 * d + 2)) := Nat.mul_le_mul_left c h1
        have h3 : 4 * (n + 1) * (2 * d + 1 + 1) * (c + 1) =
            4 * (c * (n * (2 * d + 2))) + 4 * (c * (2 * d + 2)) + 4 * (n * (2 * d + 2)) +
              4 * (2 * d + 2) := by ring
        have h4 : n ≤ n * (2 * d + 2) := Nat.le_mul_of_pos_right n (by omega)
        omega

lemma mom_le (n q j : ℕ) (hn : 0 < n) (enabled : (Fin n × Fin q × Bool × Fin q) → Bool) :
    mom (fun x : Fin n → Bool => (closedPaths enabled x).card) j ≤ 2 ^ n * q ^ (n * j) := by
  unfold mom
  calc ∑ x : Fin n → Bool, (closedPaths enabled x).card ^ j
      ≤ ∑ _x : Fin n → Bool, (q ^ n) ^ j := by
        apply Finset.sum_le_sum
        intro x _
        exact Nat.pow_le_pow_left (closedPaths_card_le hn enabled x) j
    _ = 2 ^ n * q ^ (n * j) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
          smul_eq_mul, ← Nat.pow_mul]

def scanBound (n q d width : ℕ) : ℕ :=
  (2 * d + 1) * (n * (2 * (2 * d + 1) * q ^ (2 * (2 * d + 1)) + 12 * width * q ^ (3 * (2 * d + 1))) +
    5 * width * q ^ (2 * d + 1))

lemma scan_ok (n q d : ℕ) (hn : 0 < n) :
    ∃ (scan : List BGate)
      (tap : Fin (2 * d + 1) × Fin (4 * (n + 1) * (2 * d + 1 + 1) * (Nat.clog 2 (q + 2) + 1)) → ℕ),
      scan.length ≤ scanBound n q d (4 * (n + 1) * (2 * d + 1 + 1) * (Nat.clog 2 (q + 2) + 1)) ∧
      WF (2 + Fintype.card (Fin n × Fin q × Bool × Fin q)) scan ∧
      (∀ i, tap i < 2 + Fintype.card (Fin n × Fin q × Bool × Fin q) + scan.length) ∧
      ∀ (enabled : (Fin n × Fin q × Bool × Fin q) → Bool)
        (j : Fin (2 * d + 1)),
        regVal scan ([false, true] ++ List.ofFn (fun i : Fin (Fintype.card (Fin n × Fin q × Bool × Fin q)) =>
          enabled ((Fintype.equivFin (Fin n × Fin q × Bool × Fin q)).symm i))) (fun k => tap (j, k)) =
        mom (fun x : Fin n → Bool => (closedPaths enabled x).card) (j.val + 1) := by
  set width := 4 * (n + 1) * (2 * d + 1 + 1) * (Nat.clog 2 (q + 2) + 1)
  set N := 2 + Fintype.card (Fin n × Fin q × Bool × Fin q)
  have hN : 2 ≤ N := by omega
  have hWF0 : WF N [] := fun i => Fin.elim0 i
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    refine ⟨[], fun _ => 0, by simp, hWF0, fun _ => by simp; omega, ?_⟩
    intro enabled j
    have hz : ∀ x : Fin n → Bool, (closedPaths enabled x).card = 0 := by
      intro x
      rw [Finset.card_eq_zero]
      apply Finset.eq_empty_of_forall_notMem
      intro p _
      exact (p 0).elim0
    have hb : HasBase ([false, true] ++ List.ofFn (fun i : Fin (Fintype.card (Fin n × Fin 0 × Bool × Fin 0)) =>
        enabled ((Fintype.equivFin (Fin n × Fin 0 × Bool × Fin 0)).symm i))) N := src_hasBase _
    unfold mom regVal
    simp only [hz]
    rw [Finset.sum_eq_zero (fun k _ => by rw [evalW_zero hb]; simp)]
    simp
  · let edgeW : (Fin n × Fin q × Bool × Fin q) → ℕ :=
      fun e => 2 + (Fintype.equivFin (Fin n × Fin q × Bool × Fin q) e).val
    let maskW : Fin n → Bool → ℕ := fun _ _ => 1
    have hedge : ∀ e, edgeW e < N := fun e => by
      simp only [edgeW, N]
      have := (Fintype.equivFin (Fin n × Fin q × Bool × Fin q) e).isLt
      omega
    have hmask : ∀ i b, maskW i b < N + ([] : List BGate).length := fun _ _ => by
      simp only [maskW, List.length_nil]; omega
    have h := buildPowList_spec (B := width) hN hn hq edgeW maskW [] hWF0 hedge hmask (2 * d + 1)
    set res := buildPowList (B := width) N edgeW maskW [] (2 * d + 1)
    refine ⟨res.1, fun i => res.2 i.1 i.2, ?_, h.2.2.1, fun i => h.2.2.2.1 i.1 i.2, ?_⟩
    · have := h.2.1
      simp only [List.length_nil, Nat.zero_add] at this
      exact this
    · intro enabled j
      have hb : HasBase ([false, true] ++ List.ofFn (fun i : Fin (Fintype.card (Fin n × Fin q × Bool × Fin q)) =>
          enabled ((Fintype.equivFin (Fin n × Fin q × Bool × Fin q)).symm i))) N := src_hasBase _
      have hed : ∀ e, evalW [] ([false, true] ++ List.ofFn (fun i : Fin (Fintype.card (Fin n × Fin q × Bool × Fin q)) =>
          enabled ((Fintype.equivFin (Fin n × Fin q × Bool × Fin q)).symm i))) (edgeW e) = enabled e := by
        intro e
        simp only [edgeW]
        rw [evalW_nil_src]
        simp
      have hmk : ∀ i b, evalW [] ([false, true] ++ List.ofFn (fun i : Fin (Fintype.card (Fin n × Fin q × Bool × Fin q)) =>
          enabled ((Fintype.equivFin (Fin n × Fin q × Bool × Fin q)).symm i))) (maskW i b) =
            (fun (_ : Fin n) (_ : Bool) => true) i b := by
        intro i b
        exact evalW_one hb
      have hlt : ∀ j : Fin (2 * d + 1), 2 ^ n * q ^ (n * (j.val + 1)) < 2 ^ width :=
        fun j => pow_lt_width n q d (j.val + 1) (by omega)
      have := h.2.2.2.2 _ enabled _ hb hed hmk hlt j
      rw [maskWords_true] at this
      exact this

lemma scanBound_le (n q d : ℕ) :
    scanBound n q d (4 * (n + 1) * (2 * d + 1 + 1) * (Nat.clog 2 (q + 2) + 1)) ≤
      10000000 * (n + 2) ^ 4 * (d + 2) ^ 10 * (q + 1) ^ (3 * (2 * d + 1)) *
        (Nat.clog 2 (q + 2) + 1) ^ 4 := by
  unfold scanBound
  set L := Nat.clog 2 (q + 2) + 1
  set Q := (q + 1) ^ (3 * (2 * d + 1))
  set o := 2 * d + 1
  set w := 4 * (n + 1) * (o + 1) * L
  have hL : 1 ≤ L := by omega
  have hq1 : ∀ e ≤ 3 * o, q ^ e ≤ Q := fun e he =>
    le_trans (Nat.pow_le_pow_left (by omega) e) (Nat.pow_le_pow_right (by omega) he)
  have e1 := hq1 (2 * o) (by omega)
  have e2 := hq1 (3 * o) le_rfl
  have e3 := hq1 o (by omega)
  have step1 : o * (n * (2 * o * q ^ (2 * o) + 12 * w * q ^ (3 * o)) + 5 * w * q ^ o) ≤
      o * (n * (2 * o * Q + 12 * w * Q) + 5 * w * Q) := by gcongr
  have step2 : o * (n * (2 * o * Q + 12 * w * Q) + 5 * w * Q) =
      Q * (o * (2 * n * o + 12 * n * w + 5 * w)) := by ring
  have hw : w ≤ 8 * (n + 2) * (d + 2) * L := by
    simp only [w, o]
    have : 4 * (n + 1) * (2 * d + 1 + 1) ≤ 8 * (n + 2) * (d + 2) := by nlinarith
    exact Nat.mul_le_mul_right L this
  have ho : o ≤ 2 * (d + 2) := by omega
  have hn2 : n ≤ n + 2 := by omega
  have step3 : o * (2 * n * o + 12 * n * w + 5 * w) ≤
      (2 * (d + 2)) * (2 * (n + 2) * (2 * (d + 2)) * L + 12 * (n + 2) * (8 * (n + 2) * (d + 2) * L) +
        5 * (8 * (n + 2) * (d + 2) * L)) := by
    have hLn : 2 * n * o ≤ 2 * (n + 2) * (2 * (d + 2)) * L := by
      calc 2 * n * o ≤ 2 * (n + 2) * (2 * (d + 2)) := by gcongr
        _ ≤ 2 * (n + 2) * (2 * (d + 2)) * L := Nat.le_mul_of_pos_right _ hL
    gcongr
  have step4 : (2 * (d + 2)) * (2 * (n + 2) * (2 * (d + 2)) * L + 12 * (n + 2) * (8 * (n + 2) * (d + 2) * L) +
        5 * (8 * (n + 2) * (d + 2) * L)) ≤ 300 * (n + 2) ^ 2 * (d + 2) ^ 2 * L := by
    have r1 : (2 * (d + 2)) * (2 * (n + 2) * (2 * (d + 2)) * L + 12 * (n + 2) * (8 * (n + 2) * (d + 2) * L) +
        5 * (8 * (n + 2) * (d + 2) * L)) = ((n + 2) * (d + 2) ^ 2 * L) * (88 + 192 * (n + 2)) := by ring
    have r2 : 300 * (n + 2) ^ 2 * (d + 2) ^ 2 * L = ((n + 2) * (d + 2) ^ 2 * L) * (300 * (n + 2)) := by ring
    rw [r1, r2]
    exact Nat.mul_le_mul_left _ (by omega)
  have step5 : 300 * (n + 2) ^ 2 * (d + 2) ^ 2 * L ≤ 10000000 * (n + 2) ^ 4 * (d + 2) ^ 10 * L ^ 4 := by
    have a1 : (n + 2) ^ 2 ≤ (n + 2) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have a2 : (d + 2) ^ 2 ≤ (d + 2) ^ 10 := Nat.pow_le_pow_right (by omega) (by omega)
    have a3 : L ≤ L ^ 4 := by
      have := Nat.pow_le_pow_right hL (show 1 ≤ 4 by omega)
      simpa using this
    exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) a1) a2) a3
  calc o * (n * (2 * o * q ^ (2 * o) + 12 * w * q ^ (3 * o)) + 5 * w * q ^ o)
      ≤ Q * (o * (2 * n * o + 12 * n * w + 5 * w)) := by rw [← step2]; exact step1
    _ ≤ Q * (10000000 * (n + 2) ^ 4 * (d + 2) ^ 10 * L ^ 4) := by
        apply Nat.mul_le_mul_left
        exact le_trans step3 (le_trans step4 step5)
    _ = 10000000 * (n + 2) ^ 4 * (d + 2) ^ 10 * Q * L ^ 4 := by ring

lemma decBound_le (n q d : ℕ) :
    decBound d (4 * (n + 1) * (2 * d + 1 + 1) * (Nat.clog 2 (q + 2) + 1)) ≤
      10000000 * (n + 2) ^ 4 * (d + 2) ^ 16 * (Nat.clog 2 (q + 2) + 1) ^ 4 := by
  unfold decBound stepCost
  set L := Nat.clog 2 (q + 2) + 1
  set w := 4 * (n + 1) * (2 * d + 1 + 1) * L
  set B := Bfun d w
  have hL : 1 ≤ L := by omega
  have hB1 : 1 ≤ B := by simp only [B, Bfun]; omega
  have hBle : B ≤ 20 * (n + 2) * (d + 2) ^ 2 * L := by
    simp only [B, Bfun, Efun, w]
    have h1 : (d + 1) * (d + 1) ≤ (d + 2) ^ 2 * L := by
      calc (d + 1) * (d + 1) ≤ (d + 2) ^ 2 := by nlinarith
        _ ≤ (d + 2) ^ 2 * L := Nat.le_mul_of_pos_right _ hL
    have h2 : 4 * (n + 1) * (2 * d + 1 + 1) * L * (d + 1) ≤ 8 * (n + 2) * (d + 2) ^ 2 * L := by
      have : 4 * (n + 1) * (2 * d + 1 + 1) * (d + 1) ≤ 8 * (n + 2) * (d + 2) ^ 2 := by nlinarith
      calc 4 * (n + 1) * (2 * d + 1 + 1) * L * (d + 1) = 4 * (n + 1) * (2 * d + 1 + 1) * (d + 1) * L := by ring
        _ ≤ 8 * (n + 2) * (d + 2) ^ 2 * L := Nat.mul_le_mul_right L this
    have h3 : 0 < (n + 2) * (d + 2) ^ 2 * L := by positivity
    have h4 : (d + 2) ^ 2 * L ≤ (n + 2) * (d + 2) ^ 2 * L := by
      have : (d + 2) ^ 2 * L * 1 ≤ (d + 2) ^ 2 * L * (n + 2) := Nat.mul_le_mul_left _ (by omega)
      have e : (d + 2) ^ 2 * L * (n + 2) = (n + 2) * (d + 2) ^ 2 * L := by ring
      omega
    have e1 : 20 * (n + 2) * (d + 2) ^ 2 * L = 20 * ((n + 2) * (d + 2) ^ 2 * L) := by ring
    have e2 : 8 * (n + 2) * (d + 2) ^ 2 * L = 8 * ((n + 2) * (d + 2) ^ 2 * L) := by ring
    omega
  have hB2 : B ≤ B * B := Nat.le_mul_of_pos_left B hB1
  have hB3 : B * B ≤ B * B * B := Nat.le_mul_of_pos_right _ hB1
  have hBB : 1 ≤ B * B * B := le_trans hB1 (le_trans hB2 hB3)
  have hstep : 28 * B * B * B + (d + 1 + 1) * (d + 1 + 1) * (14 * B * B + 21 * B) + 4 * B + 2 ≤
      69 * (d + 2) ^ 2 * (B * B * B) := by
    have a1 : 14 * B * B + 21 * B ≤ 35 * (B * B * B) := by nlinarith
    have a2 : (d + 1 + 1) * (d + 1 + 1) * (14 * B * B + 21 * B) ≤ (d + 2) ^ 2 * (35 * (B * B * B)) := by
      have : (d + 1 + 1) * (d + 1 + 1) = (d + 2) ^ 2 := by ring
      rw [this]; exact Nat.mul_le_mul_left _ a1
    have a3 : 0 < (d + 2) ^ 2 := by positivity
    have a4 : 34 * (B * B * B) ≤ 34 * ((d + 2) ^ 2 * (B * B * B)) := by
      have : B * B * B * 1 ≤ B * B * B * (d + 2) ^ 2 := Nat.mul_le_mul_left _ a3
      linarith
    nlinarith
  have htot : (2 * d + 1) * (28 * B * B * B + (d + 1 + 1) * (d + 1 + 1) * (14 * B * B + 21 * B) + 4 * B + 2) +
      (14 * B * B + 18 * B) ≤ 200 * (d + 2) ^ 3 * (B * B * B) := by
    have a1 : (2 * d + 1) * (28 * B * B * B + (d + 1 + 1) * (d + 1 + 1) * (14 * B * B + 21 * B) + 4 * B + 2) ≤
        (2 * (d + 2)) * (69 * (d + 2) ^ 2 * (B * B * B)) := Nat.mul_le_mul (by omega) hstep
    have a2 : 14 * B * B + 18 * B ≤ 32 * (B * B * B) := by nlinarith
    have a3 : 0 < (d + 2) ^ 3 := by positivity
    have a4 : 32 * (B * B * B) ≤ 32 * ((d + 2) ^ 3 * (B * B * B)) := by
      have : B * B * B * 1 ≤ B * B * B * (d + 2) ^ 3 := Nat.mul_le_mul_left _ a3
      linarith
    have a5 : (2 * (d + 2)) * (69 * (d + 2) ^ 2 * (B * B * B)) = 138 * ((d + 2) ^ 3 * (B * B * B)) := by ring
    have a6 : 200 * (d + 2) ^ 3 * (B * B * B) = 200 * ((d + 2) ^ 3 * (B * B * B)) := by ring
    omega
  have hcube : B * B * B ≤ (20 * (n + 2) * (d + 2) ^ 2 * L) ^ 3 := by
    have := Nat.pow_le_pow_left hBle 3
    simpa [pow_three, Nat.mul_assoc] using this
  calc (2 * d + 1) * (28 * B * B * B + (d + 1 + 1) * (d + 1 + 1) * (14 * B * B + 21 * B) + 4 * B + 2) +
        (14 * B * B + 18 * B)
      ≤ 200 * (d + 2) ^ 3 * (B * B * B) := htot
    _ ≤ 200 * (d + 2) ^ 3 * (20 * (n + 2) * (d + 2) ^ 2 * L) ^ 3 := Nat.mul_le_mul_left _ hcube
    _ = 1600000 * ((n + 2) ^ 3 * (d + 2) ^ 9 * L ^ 3) := by ring
    _ ≤ 1600000 * ((n + 2) ^ 4 * (d + 2) ^ 16 * L ^ 4) := by
        apply Nat.mul_le_mul_left
        have a1 : (n + 2) ^ 3 ≤ (n + 2) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
        have a2 : (d + 2) ^ 9 ≤ (d + 2) ^ 16 := Nat.pow_le_pow_right (by omega) (by omega)
        have a3 : L ^ 3 ≤ L ^ 4 := Nat.pow_le_pow_right hL (by omega)
        gcongr
    _ ≤ 10000000 * (n + 2) ^ 4 * (d + 2) ^ 16 * L ^ 4 := by
        have : 1600000 * ((n + 2) ^ 4 * (d + 2) ^ 16 * L ^ 4) =
            1600000 * (n + 2) ^ 4 * (d + 2) ^ 16 * L ^ 4 := by ring
        rw [this]
        gcongr
        norm_num

end PEqualNP.Outside.L_pcx_331_aux

theorem PEqualNP.Outside.L_pcx_331 : (∃ c : ℕ, 0 < c ∧ ∀ (n q d : ℕ), 0 < n → 0 < d →
  let W := Fin n → Bool
  let Edge := Fin n × Fin q × Bool × Fin q
  let orders := 2*d+1
  let logQ := Nat.clog 2 (q+2)+1
  let width := 4*(n+1)*(orders+1)*logQ
  let digits := 16*(d+2)^2*(width+1)
  let I := Fin orders × Fin width
  let O := (Bool × Fin digits) ⊕ Unit
  let N := 2 + Fintype.card Edge
  let T := 2 + Fintype.card I
  let valid := fun (inputs : ℕ) (gs : List PEqualNP.MetaComplexity.BinaryGate) =>
    ∀ i : Fin gs.length, (gs.get i).left < inputs+i.val ∧ (gs.get i).right < inputs+i.val
  let eval := fun (gs : List PEqualNP.MetaComplexity.BinaryGate) (xs : List Bool) =>
    (PEqualNP.MetaComplexity.BinaryCircuit.mk gs 0).wires ([false,true] ++ xs)
  ∃ (scan dec : List PEqualNP.MetaComplexity.BinaryGate) (tap : I → ℕ) (out : O → ℕ),
    scan.length ≤ c*(n+2)^4*(d+2)^10*(q+1)^(3*orders)*logQ^4 ∧
    dec.length ≤ c*(n+2)^4*(d+2)^16*logQ^4 ∧ valid N scan ∧ valid T dec ∧
    (∀ i, tap i < N+scan.length) ∧ (∀ o, out o < T+dec.length) ∧
    ∀ enabled : Edge → Bool,
      let mult := fun (x : W) => (Finset.univ.filter (fun p : Fin (n+1) → Fin q =>
        p 0 = p (Fin.last n) ∧ ∀ i : Fin n, enabled (i,p i.castSucc,x i,p i.succ) = true)).card
      let words := Finset.univ.filter (fun x : W => 0 < mult x)
      let levels := (words.image mult).card
      let wires := eval scan (List.ofFn (fun j : Fin (Fintype.card Edge) => enabled ((Fintype.equivFin Edge).symm j)))
      let read := fun (i : I) => wires.getD (tap i) false
      let unpack := fun (keep : Bool) => eval dec (List.ofFn (fun j : Fin (Fintype.card I) =>
        let i := (Fintype.equivFin I).symm j
        (keep || decide (i.1.val < 2*d)) && read i))
      let number := fun (side : Bool) => ∑ k : Fin digits,
        ((unpack false).getD (out (Sum.inl (side,k))) false).toNat * 2^k.val
      let flag := (unpack true).getD (out (Sum.inr ())) false
      let value : ℚ := (number false : ℚ) / (number true : ℚ)
      let fit := fun (coeff : Fin d → ℚ) =>
        ∑ x : W, let y := ∑ t : Fin d, coeff t * (mult x : ℚ)^(t.val+1)
                 2*y - y^2
      (∀ j : Fin orders, (∑ k : Fin width, (read (j,k)).toNat * 2^k.val) =
        ∑ x : W, (mult x)^(j.val+1)) ∧
      0 < number true ∧ (∀ coeff, fit coeff ≤ value) ∧ (∃ coeff, fit coeff = value) ∧
      value ≤ (words.card : ℚ) ∧ (value = (words.card : ℚ) ↔ flag = true) ∧
      (flag = true ↔ levels ≤ d)) := by
  refine ⟨10000000, by norm_num, ?_⟩
  intro n q d hn hd
  obtain ⟨scan, tap, hsl, hsw, hst, hsem⟩ := PEqualNP.Outside.L_pcx_331_aux.scan_ok n q d hn
  obtain ⟨dec, out, hdl, hdw, hdo, hdsem⟩ := PEqualNP.Outside.L_pcx_331_aux.dec_ok d
    (4 * (n + 1) * (2 * d + 1 + 1) * (Nat.clog 2 (q + 2) + 1)) hd
  intro W Edge orders logQ width digits I O N T valid eval
  refine ⟨scan, dec, tap, out, le_trans hsl (PEqualNP.Outside.L_pcx_331_aux.scanBound_le n q d),
    le_trans hdl (PEqualNP.Outside.L_pcx_331_aux.decBound_le n q d), hsw, hdw, hst, hdo, ?_⟩
  intro enabled mult words levels wires read unpack number flag value fit
  have hm := hsem enabled
  have hmom : ∀ j ≤ 2 * d + 1, PEqualNP.Outside.L_pcx_331_aux.mom mult j <
      2 ^ (4 * (n + 1) * (2 * d + 1 + 1) * (Nat.clog 2 (q + 2) + 1)) := fun j hj =>
    lt_of_le_of_lt (PEqualNP.Outside.L_pcx_331_aux.mom_le n q j hn enabled)
      (PEqualNP.Outside.L_pcx_331_aux.pow_lt_width n q d j hj)
  have hrd : ∀ i : Fin (2 * d + 1) × Fin (4 * (n + 1) * (2 * d + 1 + 1) * (Nat.clog 2 (q + 2) + 1)),
      read i = (PEqualNP.Outside.L_pcx_331_aux.mom mult (i.1.val + 1)).testBit i.2.val := by
    intro i
    have h1 := hm i.1
    have h2 := PEqualNP.Outside.L_pcx_331_aux.regVal_testBit_fin scan
      ([false, true] ++ List.ofFn (fun j : Fin (Fintype.card (Fin n × Fin q × Bool × Fin q)) =>
        enabled ((Fintype.equivFin (Fin n × Fin q × Bool × Fin q)).symm j)))
      (fun k => tap (i.1, k)) i.2
    rw [h1] at h2
    exact h2.symm
  have hd' := hdsem (X := W) mult read hmom hrd
  exact ⟨hm, hd'.1, hd'.2.1, hd'.2.2.1, hd'.2.2.2.1, hd'.2.2.2.2.1, hd'.2.2.2.2.2⟩
