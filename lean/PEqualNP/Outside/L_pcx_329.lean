import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_329

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

def stirling : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | k + 1, j + 1 => stirling k j + k * stirling k (j + 1)

lemma stirling_gt_zero : ∀ (k j : ℕ), k < j → stirling k j = 0
  | 0, 0, h => by omega
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => by omega
  | k + 1, j + 1, h => by
    simp only [stirling]
    rw [stirling_gt_zero k j (by omega), stirling_gt_zero k (j + 1) (by omega)]
    simp

lemma stirling_succ_one : ∀ a : ℕ, stirling (a + 1) 1 = a.factorial
  | 0 => rfl
  | a + 1 => by
    have hstep : stirling (a + 2) 1 = stirling (a + 1) 0 + (a + 1) * stirling (a + 1) 1 := rfl
    have h0 : stirling (a + 1) 0 = 0 := rfl
    rw [hstep, h0, Nat.zero_add, stirling_succ_one a, Nat.factorial_succ]

lemma stirling_sum : ∀ k : ℕ, ∑ j ∈ Finset.range (k + 1), stirling k j = k.factorial
  | 0 => rfl
  | k + 1 => by
    rw [Finset.sum_range_succ']
    simp only [stirling, Nat.add_zero, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [stirling_sum k]
    cases k with
    | zero => simp [stirling]
    | succ m =>
      have h1 := Finset.sum_range_succ' (fun x => stirling (m + 1) x) (m + 2)
      have h2 := Finset.sum_range_succ (fun x => stirling (m + 1) x) (m + 2)
      have h0 : stirling (m + 1) 0 = 0 := rfl
      have hgt : stirling (m + 1) (m + 2) = 0 := stirling_gt_zero (m + 1) (m + 2) (by omega)
      rw [h0] at h1
      rw [hgt] at h2
      simp only [Nat.add_zero] at h1 h2
      have hshift : ∑ x ∈ Finset.range (m + 2), stirling (m + 1) (x + 1) = (m + 1).factorial := by
        rw [← h1, h2, stirling_sum (m + 1)]
      rw [hshift, Nat.factorial_succ (m + 1)]
      ring

lemma stirling_falling_int : ∀ (k m : ℕ),
    ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ (k - j) * (stirling k j : ℤ) * (m : ℤ) ^ j =
      ∏ i ∈ Finset.range k, ((m : ℤ) - (i : ℤ))
  | 0, m => by simp [stirling]
  | k + 1, m => by
    rw [Finset.prod_range_succ, ← stirling_falling_int k m]
    rw [Finset.sum_range_succ']
    simp only [stirling, Nat.cast_zero, mul_zero, zero_mul, add_zero]
    have hsplit :
        ∑ j ∈ Finset.range (k + 1),
          (-1 : ℤ) ^ (k + 1 - (j + 1)) * ((stirling k j + k * stirling k (j + 1) : ℕ) : ℤ) *
            (m : ℤ) ^ (j + 1) =
        (∑ j ∈ Finset.range (k + 1),
          (-1 : ℤ) ^ (k - j) * (stirling k j : ℤ) * (m : ℤ) ^ (j + 1)) +
        (∑ j ∈ Finset.range (k + 1),
          (-1 : ℤ) ^ (k - j) * ((k : ℤ) * (stirling k (j + 1) : ℤ)) * (m : ℤ) ^ (j + 1)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      ring
    rw [hsplit]
    have hterm1 :
        ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ (k - j) * (stirling k j : ℤ) * (m : ℤ) ^ (j + 1) =
          (∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ (k - j) * (stirling k j : ℤ) * (m : ℤ) ^ j) * (m : ℤ) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_succ]
      ring
    have hterm2 :
        ∑ j ∈ Finset.range (k + 1),
          (-1 : ℤ) ^ (k - j) * ((k : ℤ) * (stirling k (j + 1) : ℤ)) * (m : ℤ) ^ (j + 1) =
        -((∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ (k - j) * (stirling k j : ℤ) * (m : ℤ) ^ j) * (k : ℤ)) := by
      cases k with
      | zero => simp [stirling]
      | succ t =>
        rw [Finset.sum_range_succ, stirling_gt_zero (t + 1) (t + 2) (by omega)]
        simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
        have hrhs :
            ∑ j ∈ Finset.range (t + 2), (-1 : ℤ) ^ (t + 1 - j) * (stirling (t + 1) j : ℤ) * (m : ℤ) ^ j =
              ∑ j ∈ Finset.range (t + 1), (-1 : ℤ) ^ (t + 1 - (j + 1)) * (stirling (t + 1) (j + 1) : ℤ) * (m : ℤ) ^ (j + 1) := by
          rw [Finset.sum_range_succ']
          simp [stirling]
        rw [hrhs, Finset.sum_mul, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        have hjt : j < t + 1 := Finset.mem_range.mp hj
        have hsub1 : t + 1 - j = (t - j) + 1 := by omega
        have hsub2 : t + 1 - (j + 1) = t - j := by omega
        rw [hsub1, hsub2, pow_succ]
        ring
    rw [hterm1, hterm2]
    ring

def capPos (a : ℕ) (j : Fin (a + 1)) : ℕ :=
  if (a - j.val) % 2 = 0 then stirling (a + 1) (j.val + 1) else 0

def capNeg (a : ℕ) (j : Fin (a + 1)) : ℕ :=
  if (a - j.val) % 2 = 1 then stirling (a + 1) (j.val + 1) else 0

def indPos (a : ℕ) (j : Fin a) : ℕ :=
  if j.val % 2 = 0 then stirling (a + 1) (j.val + 2) else 0

def indNeg (a : ℕ) (j : Fin a) : ℕ :=
  if j.val % 2 = 1 then stirling (a + 1) (j.val + 2) else 0

lemma capPos_sub_capNeg (a : ℕ) (j : Fin (a + 1)) :
    (capPos a j : ℤ) - (capNeg a j : ℤ) = (-1 : ℤ) ^ (a - j.val) * (stirling (a + 1) (j.val + 1) : ℤ) := by
  unfold capPos capNeg
  rcases Nat.mod_two_eq_zero_or_one (a - j.val) with h0 | h1
  · simp only [h0, ite_true, show (0 : ℕ) ≠ 1 by decide, ite_false, Nat.cast_zero, sub_zero]
    have heven : Even (a - j.val) := Nat.even_iff.mpr h0
    rw [heven.neg_one_pow, one_mul]
  · simp only [h1, show (1 : ℕ) ≠ 0 by decide, ite_false, ite_true, Nat.cast_zero, zero_sub]
    have hodd : Odd (a - j.val) := Nat.odd_iff.mpr h1
    rw [hodd.neg_one_pow]
    ring

lemma indPos_sub_indNeg (a : ℕ) (j : Fin a) :
    (indPos a j : ℤ) - (indNeg a j : ℤ) = (-1 : ℤ) ^ j.val * (stirling (a + 1) (j.val + 2) : ℤ) := by
  unfold indPos indNeg
  rcases Nat.mod_two_eq_zero_or_one j.val with h0 | h1
  · simp only [h0, ite_true, show (0 : ℕ) ≠ 1 by decide, ite_false, Nat.cast_zero, sub_zero]
    have heven : Even j.val := Nat.even_iff.mpr h0
    rw [heven.neg_one_pow, one_mul]
  · simp only [h1, show (1 : ℕ) ≠ 0 by decide, ite_false, ite_true, Nat.cast_zero, zero_sub]
    have hodd : Odd j.val := Nat.odd_iff.mpr h1
    rw [hodd.neg_one_pow]
    ring

lemma cap_poly_int (a m : ℕ) :
    (∑ j : Fin (a + 1), (capPos a j : ℤ) * (m : ℤ) ^ (j.val + 1)) -
      (∑ j : Fin (a + 1), (capNeg a j : ℤ) * (m : ℤ) ^ (j.val + 1)) =
      ∏ i ∈ Finset.range (a + 1), ((m : ℤ) - (i : ℤ)) := by
  rw [← Finset.sum_sub_distrib]
  have h1 :
      ∑ j : Fin (a + 1), ((capPos a j : ℤ) * (m : ℤ) ^ (j.val + 1) - (capNeg a j : ℤ) * (m : ℤ) ^ (j.val + 1)) =
        ∑ j : Fin (a + 1), (-1 : ℤ) ^ (a - j.val) * (stirling (a + 1) (j.val + 1) : ℤ) * (m : ℤ) ^ (j.val + 1) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [← sub_mul, capPos_sub_capNeg]
  rw [h1, Fin.sum_univ_eq_sum_range (fun j => (-1 : ℤ) ^ (a - j) * (stirling (a + 1) (j + 1) : ℤ) * (m : ℤ) ^ (j + 1))]
  rw [← stirling_falling_int (a + 1) m]
  conv_rhs => rw [Finset.sum_range_succ']
  have h0 : stirling (a + 1) 0 = 0 := rfl
  rw [h0]
  simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro j _
  have hsub : a + 1 - (j + 1) = a - j := by omega
  rw [hsub]

lemma falling_prod_nonneg (a m : ℕ) :
    0 ≤ ∏ i ∈ Finset.range (a + 1), ((m : ℤ) - (i : ℤ)) := by
  by_cases hle : m ≤ a
  · have hmem : m ∈ Finset.range (a + 1) := Finset.mem_range.mpr (by omega)
    have hzero : ∏ i ∈ Finset.range (a + 1), ((m : ℤ) - (i : ℤ)) = 0 :=
      Finset.prod_eq_zero hmem (by omega)
    rw [hzero]
  · apply Finset.prod_nonneg
    intro i hi
    have : i < a + 1 := Finset.mem_range.mp hi
    omega

lemma falling_prod_eq_zero_iff (a m : ℕ) :
    (∏ i ∈ Finset.range (a + 1), ((m : ℤ) - (i : ℤ))) = 0 ↔ m ≤ a := by
  constructor
  · intro h0
    rw [Finset.prod_eq_zero_iff] at h0
    rcases h0 with ⟨i, hi, heq⟩
    have : i < a + 1 := Finset.mem_range.mp hi
    omega
  · intro hle
    exact Finset.prod_eq_zero (i := m) (Finset.mem_range.mpr (by omega)) (by omega)

lemma cap_sum_iff {α : Type} [Fintype α] (a : ℕ) (f : α → ℕ) :
    (∑ j : Fin (a + 1), capPos a j * ∑ x : α, f x ^ (j.val + 1)) =
      (∑ j : Fin (a + 1), capNeg a j * ∑ x : α, f x ^ (j.val + 1)) ↔
      ∀ x : α, f x ≤ a := by
  have hdiff :
      ((∑ j : Fin (a + 1), capPos a j * ∑ x : α, f x ^ (j.val + 1) : ℕ) : ℤ) -
        ((∑ j : Fin (a + 1), capNeg a j * ∑ x : α, f x ^ (j.val + 1) : ℕ) : ℤ) =
        ∑ x : α, ∏ i ∈ Finset.range (a + 1), ((f x : ℤ) - (i : ℤ)) := by
    push_cast
    have hswap1 :
        ∑ j : Fin (a + 1), (capPos a j : ℤ) * ∑ x : α, (f x : ℤ) ^ (j.val + 1) =
          ∑ x : α, ∑ j : Fin (a + 1), (capPos a j : ℤ) * (f x : ℤ) ^ (j.val + 1) := by
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    have hswap2 :
        ∑ j : Fin (a + 1), (capNeg a j : ℤ) * ∑ x : α, (f x : ℤ) ^ (j.val + 1) =
          ∑ x : α, ∑ j : Fin (a + 1), (capNeg a j : ℤ) * (f x : ℤ) ^ (j.val + 1) := by
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    rw [hswap1, hswap2, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    exact cap_poly_int a (f x)
  constructor
  · intro heq x
    have h0 : ∑ y : α, ∏ i ∈ Finset.range (a + 1), ((f y : ℤ) - (i : ℤ)) = 0 := by
      rw [← hdiff, heq, sub_self]
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => falling_prod_nonneg a (f y))).mp h0
    exact (falling_prod_eq_zero_iff a (f x)).mp (hall x (Finset.mem_univ x))
  · intro hall
    have h0 : ∑ y : α, ∏ i ∈ Finset.range (a + 1), ((f y : ℤ) - (i : ℤ)) = 0 := by
      apply Finset.sum_eq_zero
      intro y _
      exact (falling_prod_eq_zero_iff a (f y)).mpr (hall y)
    rw [h0] at hdiff
    omega

lemma prod_range_succ_eq_fact (a : ℕ) :
    ∏ i ∈ Finset.range a, ((i + 1 : ℕ) : ℤ) = (a.factorial : ℤ) := by
  induction a with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
    push_cast
    ring

lemma ind_poly_int (a m : ℕ) :
    (∑ j : Fin a, (indPos a j : ℤ) * (m : ℤ) ^ (j.val + 1)) -
      (∑ j : Fin a, (indNeg a j : ℤ) * (m : ℤ) ^ (j.val + 1)) =
      (a.factorial : ℤ) - ∏ i ∈ Finset.range a, (((i + 1 : ℕ) : ℤ) - (m : ℤ)) := by
  rw [← Finset.sum_sub_distrib]
  have h1 :
      ∑ j : Fin a, ((indPos a j : ℤ) * (m : ℤ) ^ (j.val + 1) - (indNeg a j : ℤ) * (m : ℤ) ^ (j.val + 1)) =
        ∑ j : Fin a, (-1 : ℤ) ^ j.val * (stirling (a + 1) (j.val + 2) : ℤ) * (m : ℤ) ^ (j.val + 1) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [← sub_mul, indPos_sub_indNeg]
  rw [h1]
  by_cases hm0 : m = 0
  · subst hm0
    simp only [Nat.cast_zero, zero_pow (Nat.succ_ne_zero _), mul_zero, Finset.sum_const_zero, sub_zero]
    rw [prod_range_succ_eq_fact a, sub_self]
  · have hmne : (-1 : ℤ) ^ a * (m : ℤ) ≠ 0 := by
      apply mul_ne_zero
      · exact pow_ne_zero a (by decide)
      · exact Int.natCast_ne_zero.mpr hm0
    apply mul_left_cancel₀ hmne
    have hprod_mul :
        (-1 : ℤ) ^ a * (m : ℤ) * ∏ i ∈ Finset.range a, (((i + 1 : ℕ) : ℤ) - (m : ℤ)) =
          ∏ i ∈ Finset.range (a + 1), ((m : ℤ) - (i : ℤ)) := by
      rw [Finset.prod_range_succ']
      simp only [Nat.cast_zero, sub_zero]
      have hflip :
          (-1 : ℤ) ^ a * ∏ i ∈ Finset.range a, (((i + 1 : ℕ) : ℤ) - (m : ℤ)) =
            ∏ i ∈ Finset.range a, ((m : ℤ) - ((i + 1 : ℕ) : ℤ)) := by
        have hconst : (-1 : ℤ) ^ a = ∏ _i ∈ Finset.range a, (-1 : ℤ) := by simp
        rw [hconst, ← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro i _
        ring
      calc (-1 : ℤ) ^ a * (m : ℤ) * ∏ i ∈ Finset.range a, (((i + 1 : ℕ) : ℤ) - (m : ℤ))
          = ((-1 : ℤ) ^ a * ∏ i ∈ Finset.range a, (((i + 1 : ℕ) : ℤ) - (m : ℤ))) * (m : ℤ) := by ring
        _ = (∏ i ∈ Finset.range a, ((m : ℤ) - ((i + 1 : ℕ) : ℤ))) * (m : ℤ) := by rw [hflip]
    rw [mul_sub, hprod_mul, ← stirling_falling_int (a + 1) m]
    conv_rhs => rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have h0 : stirling (a + 1) 0 = 0 := rfl
    have hst1 : stirling (a + 1) 1 = a.factorial := stirling_succ_one a
    have hsub1 : a + 1 - 1 = a := by omega
    rw [h0, Nat.zero_add, hst1, hsub1]
    simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero, pow_one]
    have hsum_eq :
        (-1 : ℤ) ^ a * (m : ℤ) *
          ∑ j : Fin a, (-1 : ℤ) ^ j.val * (stirling (a + 1) (j.val + 2) : ℤ) * (m : ℤ) ^ (j.val + 1) =
        -(∑ j ∈ Finset.range a,
          (-1 : ℤ) ^ (a + 1 - (j + 1 + 1)) * (stirling (a + 1) (j + 1 + 1) : ℤ) * (m : ℤ) ^ (j + 1 + 1)) := by
      rw [Fin.sum_univ_eq_sum_range (fun j => (-1 : ℤ) ^ j * (stirling (a + 1) (j + 2) : ℤ) * (m : ℤ) ^ (j + 1))]
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      have hja : j < a := Finset.mem_range.mp hj
      have hsign : (-1 : ℤ) ^ a * (-1 : ℤ) ^ j = -((-1 : ℤ) ^ (a + 1 - (j + 1 + 1))) := by
        have hsum : a + j = (a - 1 - j) + 2 * j + 1 := by omega
        have hsub' : a + 1 - (j + 1 + 1) = a - 1 - j := by omega
        rw [← pow_add, hsum, hsub', pow_succ, pow_add, pow_mul]
        norm_num
      have hexp : (m : ℤ) * (m : ℤ) ^ (j + 1) = (m : ℤ) ^ (j + 1 + 1) := by
        rw [pow_succ]; ring
      calc (-1 : ℤ) ^ a * (m : ℤ) * ((-1 : ℤ) ^ j * (stirling (a + 1) (j + 2) : ℤ) * (m : ℤ) ^ (j + 1))
          = ((-1 : ℤ) ^ a * (-1 : ℤ) ^ j) * (stirling (a + 1) (j + 2) : ℤ) * ((m : ℤ) * (m : ℤ) ^ (j + 1)) := by ring
        _ = -((-1 : ℤ) ^ (a + 1 - (j + 1 + 1))) * (stirling (a + 1) (j + 2) : ℤ) * (m : ℤ) ^ (j + 1 + 1) := by
            rw [hsign, hexp]
        _ = -((-1 : ℤ) ^ (a + 1 - (j + 1 + 1)) * (stirling (a + 1) (j + 1 + 1) : ℤ) * (m : ℤ) ^ (j + 1 + 1)) := by
            ring
    rw [hsum_eq]
    ring

lemma ind_poly_of_le (a m : ℕ) (hle : m ≤ a) :
    (∑ j : Fin a, (indPos a j : ℤ) * (m : ℤ) ^ (j.val + 1)) -
      (∑ j : Fin a, (indNeg a j : ℤ) * (m : ℤ) ^ (j.val + 1)) =
      if 0 < m then (a.factorial : ℤ) else 0 := by
  rw [ind_poly_int]
  by_cases hm : 0 < m
  · simp only [hm, ite_true]
    have hmem : m - 1 ∈ Finset.range a := Finset.mem_range.mpr (by omega)
    have hzero : ∏ i ∈ Finset.range a, (((i + 1 : ℕ) : ℤ) - (m : ℤ)) = 0 :=
      Finset.prod_eq_zero hmem (by omega)
    rw [hzero, sub_zero]
  · have hm0 : m = 0 := by omega
    subst hm0
    simp only [lt_irrefl, ite_false, Nat.cast_zero, sub_zero]
    rw [prod_range_succ_eq_fact a, sub_self]

lemma ind_sum_count {α : Type} [DecidableEq α] (a : ℕ) (S : Finset α) (f : α → ℕ)
    (hcap : ∀ x ∈ S, f x ≤ a) :
    let Dp := ∑ j : Fin a, indPos a j * ∑ x ∈ S, f x ^ (j.val + 1)
    let Dm := ∑ j : Fin a, indNeg a j * ∑ x ∈ S, f x ^ (j.val + 1)
    Dm ≤ Dp ∧ Dp - Dm = a.factorial * (S.filter (fun x => 0 < f x)).card := by
  dsimp only
  have hdiff :
      ((∑ j : Fin a, indPos a j * ∑ x ∈ S, f x ^ (j.val + 1) : ℕ) : ℤ) -
        ((∑ j : Fin a, indNeg a j * ∑ x ∈ S, f x ^ (j.val + 1) : ℕ) : ℤ) =
        ((a.factorial * (S.filter (fun x => 0 < f x)).card : ℕ) : ℤ) := by
    push_cast
    have hswap1 :
        ∑ j : Fin a, (indPos a j : ℤ) * ∑ x ∈ S, (f x : ℤ) ^ (j.val + 1) =
          ∑ x ∈ S, ∑ j : Fin a, (indPos a j : ℤ) * (f x : ℤ) ^ (j.val + 1) := by
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    have hswap2 :
        ∑ j : Fin a, (indNeg a j : ℤ) * ∑ x ∈ S, (f x : ℤ) ^ (j.val + 1) =
          ∑ x ∈ S, ∑ j : Fin a, (indNeg a j : ℤ) * (f x : ℤ) ^ (j.val + 1) := by
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    rw [hswap1, hswap2, ← Finset.sum_sub_distrib]
    have hcongr :
        ∑ x ∈ S, ((∑ j : Fin a, (indPos a j : ℤ) * (f x : ℤ) ^ (j.val + 1)) -
          (∑ j : Fin a, (indNeg a j : ℤ) * (f x : ℤ) ^ (j.val + 1))) =
        ∑ x ∈ S, if 0 < f x then (a.factorial : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      exact ind_poly_of_le a (f x) (hcap x hx)
    rw [hcongr, Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul, mul_comm]
  omega

lemma factorial_le_two_pow_sq : ∀ k : ℕ, k.factorial ≤ 2 ^ (k * k)
  | 0 => by simp
  | k + 1 => by
    have ih := factorial_le_two_pow_sq k
    have hlin : k + 1 ≤ 2 ^ (k + 1) := Nat.le_of_lt (Nat.lt_two_pow_self)
    calc (k + 1).factorial = (k + 1) * k.factorial := Nat.factorial_succ k
      _ ≤ 2 ^ (k + 1) * 2 ^ (k * k) := Nat.mul_le_mul hlin ih
      _ = 2 ^ (k + 1 + k * k) := (Nat.pow_add 2 _ _).symm
      _ ≤ 2 ^ ((k + 1) * (k + 1)) := Nat.pow_le_pow_right (by omega) (by nlinarith)

lemma capPos_sum_le (a : ℕ) :
    ∑ j : Fin (a + 1), capPos a j ≤ (a + 1).factorial := by
  calc ∑ j : Fin (a + 1), capPos a j
      ≤ ∑ j : Fin (a + 1), stirling (a + 1) (j.val + 1) := by
        apply Finset.sum_le_sum; intro j _; unfold capPos; split <;> omega
    _ = ∑ j ∈ Finset.range (a + 1), stirling (a + 1) (j + 1) :=
        Fin.sum_univ_eq_sum_range (fun j => stirling (a + 1) (j + 1)) (a + 1)
    _ = ∑ j ∈ Finset.range (a + 2), stirling (a + 1) j := by
        symm
        rw [Finset.sum_range_succ']
        have h0 : stirling (a + 1) 0 = 0 := rfl
        rw [h0, Nat.add_zero]
    _ = (a + 1).factorial := stirling_sum (a + 1)

lemma capNeg_sum_le (a : ℕ) :
    ∑ j : Fin (a + 1), capNeg a j ≤ (a + 1).factorial := by
  calc ∑ j : Fin (a + 1), capNeg a j
      ≤ ∑ j : Fin (a + 1), stirling (a + 1) (j.val + 1) := by
        apply Finset.sum_le_sum; intro j _; unfold capNeg; split <;> omega
    _ = ∑ j ∈ Finset.range (a + 1), stirling (a + 1) (j + 1) :=
        Fin.sum_univ_eq_sum_range (fun j => stirling (a + 1) (j + 1)) (a + 1)
    _ = ∑ j ∈ Finset.range (a + 2), stirling (a + 1) j := by
        symm
        rw [Finset.sum_range_succ']
        have h0 : stirling (a + 1) 0 = 0 := rfl
        rw [h0, Nat.add_zero]
    _ = (a + 1).factorial := stirling_sum (a + 1)

lemma indPos_sum_le (a : ℕ) :
    ∑ j : Fin a, indPos a j ≤ (a + 1).factorial := by
  calc ∑ j : Fin a, indPos a j
      ≤ ∑ j : Fin a, stirling (a + 1) (j.val + 2) := by
        apply Finset.sum_le_sum; intro j _; unfold indPos; split <;> omega
    _ = ∑ j ∈ Finset.range a, stirling (a + 1) (j + 2) :=
        Fin.sum_univ_eq_sum_range (fun j => stirling (a + 1) (j + 2)) a
    _ ≤ ∑ j ∈ Finset.range (a + 2), stirling (a + 1) j := by
        conv_rhs => rw [Finset.sum_range_succ', Finset.sum_range_succ']
        have heq : ∑ k ∈ Finset.range a, stirling (a + 1) (k + 1 + 1) =
            ∑ j ∈ Finset.range a, stirling (a + 1) (j + 2) := rfl
        rw [heq]
        omega
    _ = (a + 1).factorial := stirling_sum (a + 1)

lemma indNeg_sum_le (a : ℕ) :
    ∑ j : Fin a, indNeg a j ≤ (a + 1).factorial := by
  calc ∑ j : Fin a, indNeg a j
      ≤ ∑ j : Fin a, stirling (a + 1) (j.val + 2) := by
        apply Finset.sum_le_sum; intro j _; unfold indNeg; split <;> omega
    _ = ∑ j ∈ Finset.range a, stirling (a + 1) (j + 2) :=
        Fin.sum_univ_eq_sum_range (fun j => stirling (a + 1) (j + 2)) a
    _ ≤ ∑ j ∈ Finset.range (a + 2), stirling (a + 1) j := by
        conv_rhs => rw [Finset.sum_range_succ', Finset.sum_range_succ']
        have heq : ∑ k ∈ Finset.range a, stirling (a + 1) (k + 1 + 1) =
            ∑ j ∈ Finset.range a, stirling (a + 1) (j + 2) := rfl
        rw [heq]
        omega
    _ = (a + 1).factorial := stirling_sum (a + 1)

def widthB (n q a : ℕ) : ℕ :=
  (a + 1) * (a + 1) + n * (a + 1) * (Nat.clog 2 (q + 2) + 1) + 2

def kBits (a : ℕ) : ℕ :=
  (a + 1) * (a + 1) + 1

lemma q_le_two_pow_clog (q : ℕ) : q ≤ 2 ^ Nat.clog 2 (q + 2) :=
  le_trans (by omega) (Nat.le_pow_clog (by decide) (q + 2))

lemma two_pow_n_mul_q_pow_le (n q a j : ℕ) (hj : j ≤ a + 1) :
    2 ^ n * q ^ (n * j) ≤ 2 ^ (n * (a + 1) * (Nat.clog 2 (q + 2) + 1)) := by
  have hq : q ≤ 2 ^ Nat.clog 2 (q + 2) := q_le_two_pow_clog q
  have hqp : q ^ (n * j) ≤ (2 ^ Nat.clog 2 (q + 2)) ^ (n * j) := Nat.pow_le_pow_left hq _
  rw [← Nat.pow_mul] at hqp
  calc 2 ^ n * q ^ (n * j)
      ≤ 2 ^ n * 2 ^ (Nat.clog 2 (q + 2) * (n * j)) := Nat.mul_le_mul_left _ hqp
    _ = 2 ^ (n + Nat.clog 2 (q + 2) * (n * j)) := (Nat.pow_add 2 _ _).symm
    _ ≤ 2 ^ (n * (a + 1) * (Nat.clog 2 (q + 2) + 1)) := by
        apply Nat.pow_le_pow_right (by omega)
        have h1 : n * j ≤ n * (a + 1) := Nat.mul_le_mul_left n hj
        have h2 : Nat.clog 2 (q + 2) * (n * j) ≤ Nat.clog 2 (q + 2) * (n * (a + 1)) :=
          Nat.mul_le_mul_left _ h1
        have h3 : n ≤ n * (a + 1) := Nat.le_mul_of_pos_right n (by omega)
        have h4 : n * (a + 1) * (Nat.clog 2 (q + 2) + 1) =
            Nat.clog 2 (q + 2) * (n * (a + 1)) + n * (a + 1) := by ring
        omega

lemma fact_mul_pow_lt_widthB (n q a : ℕ) :
    (a + 1).factorial * (2 ^ n * q ^ (n * (a + 1))) < 2 ^ widthB n q a := by
  have hf := factorial_le_two_pow_sq (a + 1)
  have hp := two_pow_n_mul_q_pow_le n q a (a + 1) le_rfl
  calc (a + 1).factorial * (2 ^ n * q ^ (n * (a + 1)))
      ≤ 2 ^ ((a + 1) * (a + 1)) * 2 ^ (n * (a + 1) * (Nat.clog 2 (q + 2) + 1)) :=
        Nat.mul_le_mul hf hp
    _ = 2 ^ ((a + 1) * (a + 1) + n * (a + 1) * (Nat.clog 2 (q + 2) + 1)) := (Nat.pow_add 2 _ _).symm
    _ < 2 ^ widthB n q a := Nat.pow_lt_pow_right (by omega) (by unfold widthB; omega)

lemma pow_lt_widthB (n q a j : ℕ) (hj : j ≤ a + 1) :
    2 ^ n * q ^ (n * j) < 2 ^ widthB n q a := by
  have hp := two_pow_n_mul_q_pow_le n q a j hj
  calc 2 ^ n * q ^ (n * j)
      ≤ 2 ^ (n * (a + 1) * (Nat.clog 2 (q + 2) + 1)) := hp
    _ < 2 ^ widthB n q a := Nat.pow_lt_pow_right (by omega) (by unfold widthB; omega)

lemma fact_lt_two_pow_kBits (a : ℕ) : (a + 1).factorial < 2 ^ kBits a := by
  calc (a + 1).factorial
      ≤ 2 ^ ((a + 1) * (a + 1)) := factorial_le_two_pow_sq (a + 1)
    _ < 2 ^ kBits a := Nat.pow_lt_pow_right (by omega) (by unfold kBits; omega)

lemma fact_mul_two_pow_le_widthB (n q a : ℕ) :
    a.factorial * 2 ^ (n + 1) ≤ 2 ^ widthB n q a := by
  have hf : a.factorial ≤ (a + 1).factorial := Nat.factorial_le (by omega)
  have hf2 : a.factorial ≤ 2 ^ ((a + 1) * (a + 1)) := le_trans hf (factorial_le_two_pow_sq (a + 1))
  calc a.factorial * 2 ^ (n + 1)
      ≤ 2 ^ ((a + 1) * (a + 1)) * 2 ^ (n + 1) := Nat.mul_le_mul_right _ hf2
    _ = 2 ^ ((a + 1) * (a + 1) + n + 1) := by rw [← Nat.pow_add, Nat.add_assoc]
    _ ≤ 2 ^ widthB n q a := by
        apply Nat.pow_le_pow_right (by omega)
        unfold widthB
        have hpos : 1 ≤ (a + 1) * (Nat.clog 2 (q + 2) + 1) :=
          Nat.mul_pos (by omega) (by omega)
        have hn : n ≤ n * ((a + 1) * (Nat.clog 2 (q + 2) + 1)) :=
          Nat.le_mul_of_pos_right n hpos
        rw [← Nat.mul_assoc] at hn
        omega

lemma widthB_le (n q a : ℕ) :
    widthB n q a ≤ (n + 1) * (a + 2) ^ 2 * (Nat.clog 2 (q + 2) + 1) := by
  unfold widthB
  set L := Nat.clog 2 (q + 2) + 1
  have hL : 1 ≤ L := by omega
  have h1 : (a + 1) * (a + 1) + 2 ≤ (a + 2) ^ 2 := by nlinarith
  have h2 : (a + 2) ^ 2 ≤ (a + 2) ^ 2 * L := Nat.le_mul_of_pos_right _ (by omega)
  have h3 : n * (a + 1) * L ≤ n * (a + 2) ^ 2 * L := by
    have : a + 1 ≤ (a + 2) ^ 2 := by nlinarith
    exact Nat.mul_le_mul_right L (Nat.mul_le_mul_left n this)
  have h4 : (n + 1) * (a + 2) ^ 2 * L = n * (a + 2) ^ 2 * L + (a + 2) ^ 2 * L := by ring
  omega

lemma kBits_le (a : ℕ) : kBits a ≤ (a + 2) ^ 2 := by
  unfold kBits; nlinarith

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

def linComb {B : ℕ} (N Kbits : ℕ) (G : List BGate) :
    (m : ℕ) → (Fin m → ℕ) → (Fin m → Fin B → ℕ) → List BGate × (Fin B → ℕ)
  | 0, _, _ => (G, constReg B 0)
  | m + 1, coeffs, regs =>
    let r1 := linComb N Kbits G m (fun j => coeffs j.castSucc) (fun j => regs j.castSucc)
    let r2 := regMulConst N r1.1 (coeffs (Fin.last m)) (regs (Fin.last m)) Kbits
    let r3 := regAdd N r2.1 r1.2 r2.2
    (r3.1, r3.2.1)

lemma linComb_spec {N B Kbits : ℕ} (hN : 2 ≤ N) :
    ∀ (m : ℕ) (G : List BGate) (coeffs : Fin m → ℕ) (regs : Fin m → Fin B → ℕ),
      WF N G → (∀ j, RegOK N G (regs j)) → (∀ j, coeffs j < 2 ^ Kbits) →
      let res := linComb N Kbits G m coeffs regs
      Extends G res.1 ∧ res.1.length ≤ G.length + m * (5 * B * Kbits + 5 * B) ∧ WF N res.1 ∧
      RegOK N res.1 res.2 ∧
      ∀ src, HasBase src N → (∑ j : Fin m, coeffs j * regVal G src (regs j)) < 2 ^ B →
        regVal res.1 src res.2 = ∑ j : Fin m, coeffs j * regVal G src (regs j) := by
  intro m
  induction m with
  | zero =>
    intro G coeffs regs hWF _ _
    refine ⟨extends_rfl G, by simp [linComb], hWF, constReg_ok hN G 0, ?_⟩
    intro src hbase _
    simp [linComb, constReg_val hbase]
  | succ k ih =>
    intro G coeffs regs hWF hregs hck
    dsimp only [linComb]
    have h1 := ih G (fun j => coeffs j.castSucc) (fun j => regs j.castSucc) hWF
      (fun j => hregs j.castSucc) (fun j => hck j.castSucc)
    set r1 := linComb N Kbits G k (fun j => coeffs j.castSucc) (fun j => regs j.castSucc)
    have hlast_ok : RegOK N r1.1 (regs (Fin.last k)) := regOK_extends h1.1 (hregs (Fin.last k))
    have h2 := regMulConst_spec hN (coeffs (Fin.last k)) Kbits h1.2.2.1 hlast_ok
    set r2 := regMulConst N r1.1 (coeffs (Fin.last k)) (regs (Fin.last k)) Kbits
    have hr1_ok2 : RegOK N r2.1 r1.2 := regOK_extends h2.1 h1.2.2.2.1
    have h3 := regAdd_spec hN h2.2.2.1 hr1_ok2 h2.2.2.2.1
    set r3 := regAdd N r2.1 r1.2 r2.2
    refine ⟨extends_trans h1.1 (extends_trans h2.1 h3.1), ?_, h3.2.2.1, h3.2.2.2.1, ?_⟩
    · have hl1 := h1.2.1
      have hl2 := h2.2.1
      have hl3 := h3.2.1
      have hmul : (k + 1) * (5 * B * Kbits + 5 * B) = k * (5 * B * Kbits + 5 * B) + (5 * B * Kbits + 5 * B) :=
        Nat.succ_mul k _
      omega
    · intro src hbase hlt
      rw [Fin.sum_univ_castSucc] at hlt ⊢
      have hlt1 : (∑ j : Fin k, coeffs j.castSucc * regVal G src (regs j.castSucc)) < 2 ^ B := by omega
      have hv1 := h1.2.2.2.2 src hbase hlt1
      have hmod_eq : coeffs (Fin.last k) % 2 ^ Kbits = coeffs (Fin.last k) :=
        Nat.mod_eq_of_lt (hck (Fin.last k))
      have hlast_val : regVal r1.1 src (regs (Fin.last k)) = regVal G src (regs (Fin.last k)) :=
        regVal_extends h1.1 hbase.1 (hregs (Fin.last k))
      have hlt2 : (coeffs (Fin.last k) % 2 ^ Kbits) * regVal r1.1 src (regs (Fin.last k)) < 2 ^ B := by
        rw [hmod_eq, hlast_val]; omega
      have hv2 := h2.2.2.2.2 src hbase hlt2
      rw [hmod_eq, hlast_val] at hv2
      have hr1_v2 : regVal r2.1 src r1.2 = ∑ j : Fin k, coeffs j.castSucc * regVal G src (regs j.castSucc) := by
        rw [regVal_extends h2.1 hbase.1 h1.2.2.2.1, hv1]
      have hsum_lt : regVal r2.1 src r1.2 + regVal r2.1 src r2.2 < 2 ^ B := by
        rw [hr1_v2, hv2]; exact hlt
      rw [regAdd_val_of_lt hN h2.2.2.1 hr1_ok2 h2.2.2.2.1 hbase hsum_lt, hr1_v2, hv2]

noncomputable def evalCapCheck {n q : ℕ} (N a : ℕ)
    (edgeW : (Fin n × Fin q × Bool × Fin q) → ℕ) (G : List BGate) :
    List BGate × ℕ :=
  let B := widthB n q a
  let Kbits := kBits a
  let allM : Fin n → Bool → ℕ := fun _ _ => 1
  let ps := buildPowList (B := B) N edgeW allM G (a + 1)
  let rp := linComb N Kbits ps.1 (a + 1) (capPos a) ps.2
  let rn := linComb N Kbits rp.1 (a + 1) (capNeg a) ps.2
  regEq N rn.1 rp.2 rn.2

lemma evalCapCheck_spec {N n q a : ℕ} (hN : 2 ≤ N) (hn : 0 < n) (hq : 0 < q)
    (edgeW : (Fin n × Fin q × Bool × Fin q) → ℕ) (G : List BGate)
    (hWF : WF N G) (hedge : ∀ e, edgeW e < N) :
    let B := widthB n q a
    let Kbits := kBits a
    let res := evalCapCheck N a edgeW G
    Extends G res.1 ∧
    res.1.length ≤ G.length +
      (a + 1) * (n * (2 * (a + 1) * q ^ (2 * (a + 1)) + 12 * B * q ^ (3 * (a + 1))) + 5 * B * q ^ (a + 1)) +
      2 * (a + 1) * (5 * B * Kbits + 5 * B) + 2 * B ∧
    WF N res.1 ∧
    res.2 < N + res.1.length ∧
    ∀ src enabled, HasBase src N →
      (∀ e, evalW G src (edgeW e) = enabled e) →
      (evalW res.1 src res.2 = true ↔ ∀ x : Fin n → Bool, (closedPaths enabled x).card ≤ a) := by
  dsimp only [evalCapCheck]
  set B := widthB n q a
  set Kbits := kBits a
  set allM : Fin n → Bool → ℕ := fun _ _ => 1
  have hallM : ∀ i b, allM i b < N + G.length := fun _ _ => by simp only [allM]; omega
  have hps := buildPowList_spec (B := B) hN hn hq edgeW allM G hWF hedge hallM (a + 1)
  set ps := buildPowList (B := B) N edgeW allM G (a + 1)
  have hcp_lt : ∀ j : Fin (a + 1), capPos a j < 2 ^ Kbits := by
    intro j
    have h1 : capPos a j ≤ ∑ i : Fin (a + 1), capPos a i :=
      Finset.single_le_sum (f := capPos a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    exact lt_of_le_of_lt (le_trans h1 (capPos_sum_le a)) (fact_lt_two_pow_kBits a)
  have hcn_lt : ∀ j : Fin (a + 1), capNeg a j < 2 ^ Kbits := by
    intro j
    have h1 : capNeg a j ≤ ∑ i : Fin (a + 1), capNeg a i :=
      Finset.single_le_sum (f := capNeg a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    exact lt_of_le_of_lt (le_trans h1 (capNeg_sum_le a)) (fact_lt_two_pow_kBits a)
  have hrp := linComb_spec (B := B) (Kbits := Kbits) hN (a + 1) ps.1 (capPos a) ps.2
    hps.2.2.1 hps.2.2.2.1 hcp_lt
  set rp := linComb N Kbits ps.1 (a + 1) (capPos a) ps.2
  have hps_ok_rp : ∀ j : Fin (a + 1), RegOK N rp.1 (ps.2 j) := fun j => regOK_extends hrp.1 (hps.2.2.2.1 j)
  have hrn := linComb_spec (B := B) (Kbits := Kbits) hN (a + 1) rp.1 (capNeg a) ps.2
    hrp.2.2.1 hps_ok_rp hcn_lt
  set rn := linComb N Kbits rp.1 (a + 1) (capNeg a) ps.2
  have hrp_ok_rn : RegOK N rn.1 rp.2 := regOK_extends hrn.1 hrp.2.2.2.1
  have heq := regEq_spec hN hrn.2.2.1 hrp_ok_rn hrn.2.2.2.1
  refine ⟨extends_trans hps.1 (extends_trans hrp.1 (extends_trans hrn.1 heq.1)), ?_,
    heq.2.2.1, heq.2.2.2.1, ?_⟩
  · have h1 := hps.2.1; have h2 := hrp.2.1; have h3 := hrn.2.1; have h4 := heq.2.1
    have h2m : 2 * (a + 1) * (5 * B * Kbits + 5 * B) =
        (a + 1) * (5 * B * Kbits + 5 * B) + (a + 1) * (5 * B * Kbits + 5 * B) := by ring
    omega
  · intro src enabled hbase hed
    have hmask_all : ∀ i b, evalW G src (allM i b) = true := fun _ _ => evalW_one hbase
    have hmw_univ : maskWords (fun (_ : Fin n) (_ : Bool) => true) = Finset.univ := by
      ext x; simp [maskWords]
    have hps_val : ∀ j : Fin (a + 1),
        regVal ps.1 src (ps.2 j) = ∑ x : Fin n → Bool, (closedPaths enabled x).card ^ (j.val + 1) := by
      intro j
      have hv := hps.2.2.2.2 src enabled (fun _ _ => true) hbase hed hmask_all
        (fun j' => pow_lt_widthB n q a (j'.val + 1) (by omega)) j
      rw [hmw_univ] at hv
      exact hv
    have hterm_le : ∀ j : Fin (a + 1),
        regVal ps.1 src (ps.2 j) ≤ 2 ^ n * q ^ (n * (a + 1)) := by
      intro j
      rw [hps_val j]
      have h1 := layerMat_trace_le hn enabled (fun _ _ => true) (j.val + 1)
      rw [layerMat_trace_eq, hmw_univ] at h1
      have h2 : 2 ^ n * q ^ (n * (j.val + 1)) ≤ 2 ^ n * q ^ (n * (a + 1)) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hq (Nat.mul_le_mul_left n (by omega)))
      exact le_trans h1 h2
    have hrp_lt : (∑ j : Fin (a + 1), capPos a j * regVal ps.1 src (ps.2 j)) < 2 ^ B := by
      calc ∑ j : Fin (a + 1), capPos a j * regVal ps.1 src (ps.2 j)
          ≤ ∑ j : Fin (a + 1), capPos a j * (2 ^ n * q ^ (n * (a + 1))) :=
            Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_left _ (hterm_le j))
        _ = (∑ j : Fin (a + 1), capPos a j) * (2 ^ n * q ^ (n * (a + 1))) := (Finset.sum_mul _ _ _).symm
        _ ≤ (a + 1).factorial * (2 ^ n * q ^ (n * (a + 1))) := Nat.mul_le_mul_right _ (capPos_sum_le a)
        _ < 2 ^ B := fact_mul_pow_lt_widthB n q a
    have hrp_val : regVal rp.1 src rp.2 = ∑ j : Fin (a + 1), capPos a j * regVal ps.1 src (ps.2 j) :=
      hrp.2.2.2.2 src hbase hrp_lt
    have hrn_lt : (∑ j : Fin (a + 1), capNeg a j * regVal rp.1 src (ps.2 j)) < 2 ^ B := by
      calc ∑ j : Fin (a + 1), capNeg a j * regVal rp.1 src (ps.2 j)
          = ∑ j : Fin (a + 1), capNeg a j * regVal ps.1 src (ps.2 j) := by
            apply Finset.sum_congr rfl; intro j _
            rw [regVal_extends hrp.1 hbase.1 (hps.2.2.2.1 j)]
        _ ≤ ∑ j : Fin (a + 1), capNeg a j * (2 ^ n * q ^ (n * (a + 1))) :=
            Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_left _ (hterm_le j))
        _ = (∑ j : Fin (a + 1), capNeg a j) * (2 ^ n * q ^ (n * (a + 1))) := (Finset.sum_mul _ _ _).symm
        _ ≤ (a + 1).factorial * (2 ^ n * q ^ (n * (a + 1))) := Nat.mul_le_mul_right _ (capNeg_sum_le a)
        _ < 2 ^ B := fact_mul_pow_lt_widthB n q a
    have hrn_val : regVal rn.1 src rn.2 = ∑ j : Fin (a + 1), capNeg a j * regVal ps.1 src (ps.2 j) := by
      rw [hrn.2.2.2.2 src hbase hrn_lt]
      apply Finset.sum_congr rfl; intro j _
      rw [regVal_extends hrp.1 hbase.1 (hps.2.2.2.1 j)]
    rw [heq.2.2.2.2 src hbase, regVal_extends hrn.1 hbase.1 hrp.2.2.2.1, hrp_val, hrn_val]
    simp_rw [hps_val]
    exact cap_sum_iff a (fun x => (closedPaths enabled x).card)

noncomputable def countMask {n q : ℕ} (N a : ℕ)
    (edgeW : (Fin n × Fin q × Bool × Fin q) → ℕ)
    (maskW : Fin n → Bool → ℕ) (G : List BGate) :
    List BGate × (Fin (n + 1) → ℕ) :=
  let B := widthB n q a
  let Kbits := kBits a
  let ps := buildPowList (B := B) N edgeW maskW G a
  let rp := linComb N Kbits ps.1 a (indPos a) ps.2
  let rn := linComb N Kbits rp.1 a (indNeg a) ps.2
  let rs := regSub N rn.1 rp.2 rn.2
  regDivConst N rs.1 a.factorial (n + 1) rs.2.1

lemma countMask_spec {N n q a : ℕ} (hN : 2 ≤ N) (hn : 0 < n) (hq : 0 < q)
    (edgeW : (Fin n × Fin q × Bool × Fin q) → ℕ)
    (maskW : Fin n → Bool → ℕ) (G : List BGate)
    (hWF : WF N G) (hedge : ∀ e, edgeW e < N) (hmask : ∀ i b, maskW i b < N + G.length) :
    let B := widthB n q a
    let Kbits := kBits a
    let res := countMask N a edgeW maskW G
    Extends G res.1 ∧
    res.1.length ≤ G.length +
      a * (n * (2 * a * q ^ (2 * a) + 12 * B * q ^ (3 * a)) + 5 * B * q ^ a) +
      2 * a * (5 * B * Kbits + 5 * B) + 5 * B + (n + 1) * (8 * B + 1) ∧
    WF N res.1 ∧
    RegOK N res.1 res.2 ∧
    ∀ src enabled mask, HasBase src N →
      (∀ e, evalW G src (edgeW e) = enabled e) →
      (∀ i b, evalW G src (maskW i b) = mask i b) →
      (∀ x : Fin n → Bool, (closedPaths enabled x).card ≤ a) →
      regVal res.1 src res.2 =
        ((maskWords mask).filter (fun x => (closedPaths enabled x).Nonempty)).card := by
  dsimp only [countMask]
  set B := widthB n q a
  set Kbits := kBits a
  have hps := buildPowList_spec (B := B) hN hn hq edgeW maskW G hWF hedge hmask a
  set ps := buildPowList (B := B) N edgeW maskW G a
  have hip_lt : ∀ j : Fin a, indPos a j < 2 ^ Kbits := by
    intro j
    have h1 : indPos a j ≤ ∑ i : Fin a, indPos a i :=
      Finset.single_le_sum (f := indPos a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    exact lt_of_le_of_lt (le_trans h1 (indPos_sum_le a)) (fact_lt_two_pow_kBits a)
  have hin_lt : ∀ j : Fin a, indNeg a j < 2 ^ Kbits := by
    intro j
    have h1 : indNeg a j ≤ ∑ i : Fin a, indNeg a i :=
      Finset.single_le_sum (f := indNeg a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    exact lt_of_le_of_lt (le_trans h1 (indNeg_sum_le a)) (fact_lt_two_pow_kBits a)
  have hrp := linComb_spec (B := B) (Kbits := Kbits) hN a ps.1 (indPos a) ps.2
    hps.2.2.1 hps.2.2.2.1 hip_lt
  set rp := linComb N Kbits ps.1 a (indPos a) ps.2
  have hps_ok_rp : ∀ j : Fin a, RegOK N rp.1 (ps.2 j) := fun j => regOK_extends hrp.1 (hps.2.2.2.1 j)
  have hrn := linComb_spec (B := B) (Kbits := Kbits) hN a rp.1 (indNeg a) ps.2
    hrp.2.2.1 hps_ok_rp hin_lt
  set rn := linComb N Kbits rp.1 a (indNeg a) ps.2
  have hrp_ok_rn : RegOK N rn.1 rp.2 := regOK_extends hrn.1 hrp.2.2.2.1
  have hrs := regSub_spec hN hrn.2.2.1 hrp_ok_rn hrn.2.2.2.1
  set rs := regSub N rn.1 rp.2 rn.2
  have hrd := regDivConst_spec hN a.factorial (Nat.factorial_pos a) (n + 1) rs.1 rs.2.1
    hrs.2.2.1 hrs.2.2.2.1 (fact_mul_two_pow_le_widthB n q a)
  refine ⟨extends_trans hps.1 (extends_trans hrp.1 (extends_trans hrn.1 (extends_trans hrs.1 hrd.1))),
    ?_, hrd.2.2.1, hrd.2.2.2.1, ?_⟩
  · have h1 := hps.2.1; have h2 := hrp.2.1; have h3 := hrn.2.1; have h4 := hrs.2.1; have h5 := hrd.2.1
    have h2m : 2 * a * (5 * B * Kbits + 5 * B) =
        a * (5 * B * Kbits + 5 * B) + a * (5 * B * Kbits + 5 * B) := by ring
    omega
  · intro src enabled mask hbase hed hmk hcap
    have hps_val : ∀ j : Fin a,
        regVal ps.1 src (ps.2 j) = ∑ x ∈ maskWords mask, (closedPaths enabled x).card ^ (j.val + 1) :=
      fun j => hps.2.2.2.2 src enabled mask hbase hed hmk
        (fun j' => pow_lt_widthB n q a (j'.val + 1) (by omega)) j
    have hterm_le : ∀ j : Fin a, regVal ps.1 src (ps.2 j) ≤ 2 ^ n * q ^ (n * (a + 1)) := by
      intro j
      rw [hps_val j]
      have h1 := layerMat_trace_le hn enabled mask (j.val + 1)
      rw [layerMat_trace_eq] at h1
      have h2 : 2 ^ n * q ^ (n * (j.val + 1)) ≤ 2 ^ n * q ^ (n * (a + 1)) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hq (Nat.mul_le_mul_left n (by omega)))
      exact le_trans h1 h2
    have hrp_lt : (∑ j : Fin a, indPos a j * regVal ps.1 src (ps.2 j)) < 2 ^ B := by
      calc ∑ j : Fin a, indPos a j * regVal ps.1 src (ps.2 j)
          ≤ ∑ j : Fin a, indPos a j * (2 ^ n * q ^ (n * (a + 1))) :=
            Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_left _ (hterm_le j))
        _ = (∑ j : Fin a, indPos a j) * (2 ^ n * q ^ (n * (a + 1))) := (Finset.sum_mul _ _ _).symm
        _ ≤ (a + 1).factorial * (2 ^ n * q ^ (n * (a + 1))) := Nat.mul_le_mul_right _ (indPos_sum_le a)
        _ < 2 ^ B := fact_mul_pow_lt_widthB n q a
    have hrp_val : regVal rp.1 src rp.2 = ∑ j : Fin a, indPos a j * regVal ps.1 src (ps.2 j) :=
      hrp.2.2.2.2 src hbase hrp_lt
    have hrn_lt : (∑ j : Fin a, indNeg a j * regVal rp.1 src (ps.2 j)) < 2 ^ B := by
      calc ∑ j : Fin a, indNeg a j * regVal rp.1 src (ps.2 j)
          = ∑ j : Fin a, indNeg a j * regVal ps.1 src (ps.2 j) := by
            apply Finset.sum_congr rfl; intro j _
            rw [regVal_extends hrp.1 hbase.1 (hps.2.2.2.1 j)]
        _ ≤ ∑ j : Fin a, indNeg a j * (2 ^ n * q ^ (n * (a + 1))) :=
            Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_left _ (hterm_le j))
        _ = (∑ j : Fin a, indNeg a j) * (2 ^ n * q ^ (n * (a + 1))) := (Finset.sum_mul _ _ _).symm
        _ ≤ (a + 1).factorial * (2 ^ n * q ^ (n * (a + 1))) := Nat.mul_le_mul_right _ (indNeg_sum_le a)
        _ < 2 ^ B := fact_mul_pow_lt_widthB n q a
    have hrn_val : regVal rn.1 src rn.2 = ∑ j : Fin a, indNeg a j * regVal ps.1 src (ps.2 j) := by
      rw [hrn.2.2.2.2 src hbase hrn_lt]
      apply Finset.sum_congr rfl; intro j _
      rw [regVal_extends hrp.1 hbase.1 (hps.2.2.2.1 j)]
    have hind := ind_sum_count a (maskWords mask) (fun x => (closedPaths enabled x).card)
      (fun x _ => hcap x)
    have hrp_eq_rn : regVal rn.1 src rp.2 = ∑ j : Fin a, indPos a j * ∑ x ∈ maskWords mask, (closedPaths enabled x).card ^ (j.val + 1) := by
      rw [regVal_extends hrn.1 hbase.1 hrp.2.2.2.1, hrp_val]
      simp_rw [hps_val]
    have hrn_eq : regVal rn.1 src rn.2 = ∑ j : Fin a, indNeg a j * ∑ x ∈ maskWords mask, (closedPaths enabled x).card ^ (j.val + 1) := by
      rw [hrn_val]; simp_rw [hps_val]
    have hle_sub : regVal rn.1 src rn.2 ≤ regVal rn.1 src rp.2 := by
      rw [hrn_eq, hrp_eq_rn]; exact hind.1
    have hdiff_val : regVal rs.1 src rs.2.1 =
        a.factorial * ((maskWords mask).filter (fun x => 0 < (closedPaths enabled x).card)).card := by
      rw [regSub_val_of_le hN hrn.2.2.1 hrp_ok_rn hrn.2.2.2.1 hbase hle_sub, hrp_eq_rn, hrn_eq]
      exact hind.2
    have hcard_lt : ((maskWords mask).filter (fun x => 0 < (closedPaths enabled x).card)).card < 2 ^ (n + 1) := by
      calc ((maskWords mask).filter (fun x => 0 < (closedPaths enabled x).card)).card
          ≤ (Finset.univ : Finset (Fin n → Bool)).card := Finset.card_le_card (Finset.subset_univ _)
        _ = 2 ^ n := by simp
        _ < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
    have hdiff_lt : regVal rs.1 src rs.2.1 < a.factorial * 2 ^ (n + 1) := by
      rw [hdiff_val]
      exact Nat.mul_lt_mul_of_pos_left hcard_lt (Nat.factorial_pos a)
    rw [hrd.2.2.2.2 src hbase hdiff_lt, hdiff_val, Nat.mul_div_cancel_left _ (Nat.factorial_pos a)]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.card_pos]

def encodeW {n : ℕ} (x : Fin n → Bool) : ℕ :=
  ∑ i : Fin n, (x i).toNat * 2 ^ (n - 1 - i.val)

def langSet {n q : ℕ} (enabled : (Fin n × Fin q × Bool × Fin q) → Bool) :
    Finset (Fin n → Bool) :=
  Finset.univ.filter (fun x => (closedPaths enabled x).Nonempty)

def rankOf {n q : ℕ} (enabled : (Fin n × Fin q × Bool × Fin q) → Bool) (x : Fin n → Bool) : ℕ :=
  ((langSet enabled).filter (fun y => encodeW y < encodeW x)).card

def prefSet {n q : ℕ} (enabled : (Fin n × Fin q × Bool × Fin q) → Bool)
    (p : Fin n → Bool) (k : ℕ) : Finset (Fin n → Bool) :=
  (langSet enabled).filter (fun y => ∀ i : Fin n, i.val < k → y i = p i)

def prefBefore {n q : ℕ} (enabled : (Fin n × Fin q × Bool × Fin q) → Bool)
    (p : Fin n → Bool) (k : ℕ) : ℕ :=
  ((langSet enabled).filter (fun y =>
    ∃ j : Fin n, j.val < k ∧ (∀ i : Fin n, i.val < j.val → y i = p i) ∧ y j = false ∧ p j = true)).card

def zeroChildMask {n : ℕ} (p : Fin n → Bool) (k : Fin n) : Fin n → Bool → Bool :=
  fun i b =>
    if i.val < k.val then (b == p i)
    else if i.val = k.val then !b
    else true

def zeroChildMaskW {n : ℕ} (w nw : Fin n → ℕ) (k : Fin n) : Fin n → Bool → ℕ :=
  fun i b =>
    if i.val < k.val then (if b then w i else nw i)
    else if i.val = k.val then (if b then 0 else 1)
    else 1

def exactMask {n : ℕ} (p : Fin n → Bool) : Fin n → Bool → Bool :=
  fun i b => b == p i

def exactMaskW {n : ℕ} (w nw : Fin n → ℕ) : Fin n → Bool → ℕ :=
  fun i b => if b then w i else nw i

lemma sum_tail_pow_two (n k : ℕ) (hk : k < n) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => k < i.val), 2 ^ (n - 1 - i.val)) < 2 ^ (n - 1 - k) := by
  have hbij :
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => k < i.val), 2 ^ (n - 1 - i.val) =
        ∑ t ∈ Finset.range (n - 1 - k), 2 ^ t := by
    apply Finset.sum_nbij (fun i : Fin n => n - 1 - i.val)
    · intro i hi
      have hlt := (Finset.mem_filter.mp hi).2
      exact Finset.mem_range.mpr (by omega)
    · intro i1 hi1 i2 hi2 hEq
      have h1 := (Finset.mem_filter.mp hi1).2
      have h2 := (Finset.mem_filter.mp hi2).2
      dsimp only at hEq
      exact Fin.ext (by omega)
    · intro t ht
      have htlt := Finset.mem_range.mp ht
      refine ⟨⟨n - 1 - t, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩, by dsimp only; omega⟩
    · intro i _; rfl
  rw [hbij]
  have hs := sum_range_pow_two (n - 1 - k)
  omega

lemma encodeW_lt_of_first_diff {n : ℕ} (y x : Fin n → Bool) (k : Fin n)
    (hpre : ∀ i : Fin n, i.val < k.val → y i = x i) (hy : y k = false) (hx : x k = true) :
    encodeW y < encodeW x := by
  unfold encodeW
  let Slt := Finset.univ.filter (fun i : Fin n => i.val < k.val)
  let Sge := Finset.univ.filter (fun i : Fin n => ¬ i.val < k.val)
  let Sgt := Finset.univ.filter (fun i : Fin n => k.val < i.val)
  have hsplit : ∀ f : Fin n → ℕ,
      ∑ i : Fin n, f i = (∑ i ∈ Slt, f i) + f k + (∑ i ∈ Sgt, f i) := by
    intro f
    have h1 : ∑ i : Fin n, f i = (∑ i ∈ Slt, f i) + ∑ i ∈ Sge, f i :=
      (Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin n => i.val < k.val) f).symm
    have h2 : Sge = insert k Sgt := by
      ext i
      simp only [Sge, Sgt, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      omega
    have hk_not : k ∉ Sgt := by simp [Sgt]
    rw [h1, h2, Finset.sum_insert hk_not]
    omega
  rw [hsplit (fun i => (y i).toNat * 2 ^ (n - 1 - i.val)),
    hsplit (fun i => (x i).toNat * 2 ^ (n - 1 - i.val))]
  have hpre_eq : ∑ i ∈ Slt, (y i).toNat * 2 ^ (n - 1 - i.val) =
      ∑ i ∈ Slt, (x i).toNat * 2 ^ (n - 1 - i.val) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hpre i (Finset.mem_filter.mp hi).2]
  have htail_y : ∑ i ∈ Sgt, (y i).toNat * 2 ^ (n - 1 - i.val) < 2 ^ (n - 1 - k.val) := by
    calc ∑ i ∈ Sgt, (y i).toNat * 2 ^ (n - 1 - i.val)
        ≤ ∑ i ∈ Sgt, 2 ^ (n - 1 - i.val) := by
          apply Finset.sum_le_sum; intro i _; cases y i <;> simp
      _ < 2 ^ (n - 1 - k.val) := sum_tail_pow_two n k.val k.isLt
  rw [hpre_eq, hy, hx]
  simp only [Bool.toNat_false, zero_mul, Bool.toNat_true, one_mul]
  omega

lemma encodeW_lt_iff {n : ℕ} (y x : Fin n → Bool) :
    encodeW y < encodeW x ↔
      ∃ k : Fin n, (∀ i : Fin n, i.val < k.val → y i = x i) ∧ y k = false ∧ x k = true := by
  constructor
  · intro hlt
    have hne : y ≠ x := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
    have hdiff : (Finset.univ.filter (fun i : Fin n => y i ≠ x i)).Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      apply hne
      funext i
      by_contra hneq
      have hmem : i ∈ Finset.univ.filter (fun j : Fin n => y j ≠ x j) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hneq⟩
      rw [hempty] at hmem
      simp at hmem
    let k := (Finset.univ.filter (fun i : Fin n => y i ≠ x i)).min' hdiff
    have hk_mem : k ∈ Finset.univ.filter (fun i : Fin n => y i ≠ x i) := Finset.min'_mem _ hdiff
    have hk_ne : y k ≠ x k := (Finset.mem_filter.mp hk_mem).2
    have hpre : ∀ i : Fin n, i.val < k.val → y i = x i := by
      intro i hi
      by_contra hneq
      have him : i ∈ Finset.univ.filter (fun j : Fin n => y j ≠ x j) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hneq⟩
      have hle : k ≤ i := Finset.min'_le _ i him
      exact not_lt_of_ge hle hi
    cases hyk : y k <;> cases hxk : x k
    · exact absurd (hyk.trans hxk.symm) hk_ne
    · exact ⟨k, hpre, hyk, hxk⟩
    · have hrev := encodeW_lt_of_first_diff x y k (fun i hi => (hpre i hi).symm) hxk hyk
      omega
    · exact absurd (hyk.trans hxk.symm) hk_ne
  · rintro ⟨k, hpre, hy, hx⟩
    exact encodeW_lt_of_first_diff y x k hpre hy hx

lemma prefBefore_zero {n q : ℕ} (enabled : (Fin n × Fin q × Bool × Fin q) → Bool)
    (p : Fin n → Bool) : prefBefore enabled p 0 = 0 := by
  unfold prefBefore
  apply Finset.card_eq_zero.mpr
  rw [Finset.eq_empty_iff_forall_notMem]
  intro y hy
  rcases (Finset.mem_filter.mp hy).2 with ⟨j, hj, _⟩
  omega

lemma prefBefore_n {n q : ℕ} (enabled : (Fin n × Fin q × Bool × Fin q) → Bool)
    (p : Fin n → Bool) : prefBefore enabled p n = rankOf enabled p := by
  unfold prefBefore rankOf
  congr 1
  ext y
  simp only [Finset.mem_filter, encodeW_lt_iff]
  constructor
  · rintro ⟨hlang, j, _, hpre, hy, hp⟩; exact ⟨hlang, j, hpre, hy, hp⟩
  · rintro ⟨hlang, j, hpre, hy, hp⟩; exact ⟨hlang, j, j.isLt, hpre, hy, hp⟩

lemma maskWords_zeroChild {n : ℕ} (p : Fin n → Bool) (k : Fin n) :
    maskWords (zeroChildMask p k) =
      Finset.univ.filter (fun y : Fin n → Bool => (∀ i : Fin n, i.val < k.val → y i = p i) ∧ y k = false) := by
  ext y
  unfold maskWords zeroChildMask
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hall
    refine ⟨fun i hi => ?_, ?_⟩
    · have h := hall i
      simp only [hi, ite_true, beq_iff_eq] at h
      exact h
    · have h := hall k
      simp only [lt_irrefl, ite_false, ite_true, Bool.not_eq_true'] at h
      exact h
  · rintro ⟨hpre, hyk⟩ i
    by_cases hlt : i.val < k.val
    · simp [hlt, hpre i hlt]
    · by_cases heq : i.val = k.val
      · have hik : i = k := Fin.ext heq
        subst hik
        simp [hyk]
      · simp [hlt, heq]

lemma maskWords_exact {n : ℕ} (p : Fin n → Bool) :
    maskWords (exactMask p) = {p} := by
  ext y
  simp only [maskWords, exactMask, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton, beq_iff_eq]
  exact ⟨fun h => funext h, fun h i => by rw [h]⟩

lemma prefBefore_succ {n q : ℕ} (enabled : (Fin n × Fin q × Bool × Fin q) → Bool)
    (p : Fin n → Bool) (k : ℕ) (hk : k < n) :
    prefBefore enabled p (k + 1) =
      prefBefore enabled p k +
        if p ⟨k, hk⟩ = true then
          ((maskWords (zeroChildMask p ⟨k, hk⟩)).filter (fun x => (closedPaths enabled x).Nonempty)).card
        else 0 := by
  unfold prefBefore
  let A := (langSet enabled).filter (fun y =>
    ∃ j : Fin n, j.val < k ∧ (∀ i : Fin n, i.val < j.val → y i = p i) ∧ y j = false ∧ p j = true)
  let B := (langSet enabled).filter (fun y =>
    (∀ i : Fin n, i.val < k → y i = p i) ∧ y ⟨k, hk⟩ = false ∧ p ⟨k, hk⟩ = true)
  have hunion :
      (langSet enabled).filter (fun y =>
        ∃ j : Fin n, j.val < k + 1 ∧ (∀ i : Fin n, i.val < j.val → y i = p i) ∧ y j = false ∧ p j = true) =
      A ∪ B := by
    ext y
    simp only [A, B, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hl, j, hj, hpre, hy, hp⟩
      by_cases hjk : j.val < k
      · exact Or.inl ⟨hl, j, hjk, hpre, hy, hp⟩
      · have hjeq : j = ⟨k, hk⟩ := Fin.ext (by dsimp only; omega)
        subst hjeq
        exact Or.inr ⟨hl, fun i hi => hpre i (by dsimp only; exact hi), hy, hp⟩
    · rintro (⟨hl, j, hj, hpre, hy, hp⟩ | ⟨hl, hpre, hy, hp⟩)
      · exact ⟨hl, j, by omega, hpre, hy, hp⟩
      · exact ⟨hl, ⟨k, hk⟩, by dsimp only; omega, fun i hi => hpre i (by dsimp only at hi; exact hi), hy, hp⟩
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro y hA hB
    rcases (Finset.mem_filter.mp hA).2 with ⟨j, hj, _, hyj, hpj⟩
    have hpreB := (Finset.mem_filter.mp hB).2.1
    have hEq := hpreB j hj
    rw [hyj, hpj] at hEq
    cases hEq
  rw [hunion, Finset.card_union_of_disjoint hdisj]
  congr 1
  by_cases hpk : p ⟨k, hk⟩ = true
  · simp only [hpk, ite_true]
    congr 1
    rw [maskWords_zeroChild]
    ext y
    simp only [B, langSet, Finset.mem_filter, Finset.mem_univ, true_and, hpk, and_true]
    tauto
  · simp only [hpk, Bool.false_eq_true, ite_false]
    apply Finset.card_eq_zero.mpr
    rw [Finset.eq_empty_iff_forall_notMem]
    intro y hy
    exact hpk (Finset.mem_filter.mp hy).2.2.2

lemma prefSet_zero {n q : ℕ} (enabled : (Fin n × Fin q × Bool × Fin q) → Bool)
    (p : Fin n → Bool) : prefSet enabled p 0 = langSet enabled := by
  ext y
  simp [prefSet]

lemma prefSet_succ_split {n q : ℕ} (enabled : (Fin n × Fin q × Bool × Fin q) → Bool)
    (p : Fin n → Bool) (k : ℕ) (hk : k < n) :
    let p0 : Fin n → Bool := fun i => if i.val = k then false else p i
    let p1 : Fin n → Bool := fun i => if i.val = k then true else p i
    (prefSet enabled p k).card = (prefSet enabled p0 (k + 1)).card + (prefSet enabled p1 (k + 1)).card ∧
    (prefSet enabled p0 (k + 1)).card =
      ((maskWords (zeroChildMask p ⟨k, hk⟩)).filter (fun x => (closedPaths enabled x).Nonempty)).card := by
  dsimp only
  set p0 : Fin n → Bool := fun i => if i.val = k then false else p i
  set p1 : Fin n → Bool := fun i => if i.val = k then true else p i
  have hunion : prefSet enabled p k = prefSet enabled p0 (k + 1) ∪ prefSet enabled p1 (k + 1) := by
    ext y
    simp only [prefSet, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro ⟨hl, hpre⟩
      cases hyk : y ⟨k, hk⟩
      · left
        refine ⟨hl, fun i hi => ?_⟩
        by_cases hik : i.val = k
        · have : i = ⟨k, hk⟩ := Fin.ext hik; subst this; simp [p0, hyk]
        · simp [p0, hik, hpre i (by omega)]
      · right
        refine ⟨hl, fun i hi => ?_⟩
        by_cases hik : i.val = k
        · have : i = ⟨k, hk⟩ := Fin.ext hik; subst this; simp [p1, hyk]
        · simp [p1, hik, hpre i (by omega)]
    · rintro (⟨hl, hpre⟩ | ⟨hl, hpre⟩)
      · refine ⟨hl, fun i hi => ?_⟩
        have h := hpre i (by omega)
        have hne : i.val ≠ k := by omega
        simpa [p0, hne] using h
      · refine ⟨hl, fun i hi => ?_⟩
        have h := hpre i (by omega)
        have hne : i.val ≠ k := by omega
        simpa [p1, hne] using h
  have hdisj : Disjoint (prefSet enabled p0 (k + 1)) (prefSet enabled p1 (k + 1)) := by
    rw [Finset.disjoint_left]
    intro y h0 h1
    have hy0 := (Finset.mem_filter.mp h0).2 ⟨k, hk⟩ (by dsimp only; omega)
    have hy1 := (Finset.mem_filter.mp h1).2 ⟨k, hk⟩ (by dsimp only; omega)
    simp only [p0, p1, ite_true] at hy0 hy1
    rw [hy0] at hy1
    cases hy1
  refine ⟨by rw [hunion, Finset.card_union_of_disjoint hdisj], ?_⟩
  congr 1
  rw [maskWords_zeroChild]
  ext y
  simp only [prefSet, langSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hne, hpre⟩
    refine ⟨⟨fun i hi => ?_, ?_⟩, hne⟩
    · have h := hpre i (by omega)
      have hne' : i.val ≠ k := by omega
      simpa [p0, hne'] using h
    · simpa [p0] using hpre ⟨k, hk⟩ (by dsimp only; omega)
  · rintro ⟨⟨hpre, hyk⟩, hne⟩
    refine ⟨hne, fun i hi => ?_⟩
    by_cases hik : i.val = k
    · have : i = ⟨k, hk⟩ := Fin.ext hik; subst this; simp [p0, hyk]
    · simp [p0, hik, hpre i (by omega)]

lemma prefBefore_congr {n q : ℕ} (enabled : (Fin n × Fin q × Bool × Fin q) → Bool)
    (p1 p2 : Fin n → Bool) (k : ℕ) (h : ∀ i : Fin n, i.val < k → p1 i = p2 i) :
    prefBefore enabled p1 k = prefBefore enabled p2 k := by
  unfold prefBefore
  congr 1
  ext y
  simp only [Finset.mem_filter]
  constructor <;> rintro ⟨hl, j, hj, hpre, hy, hp⟩
  · exact ⟨hl, j, hj, fun i hi => by rw [hpre i hi, h i (by omega)], hy, by rw [← h j hj, hp]⟩
  · exact ⟨hl, j, hj, fun i hi => by rw [hpre i hi, ← h i (by omega)], hy, by rw [h j hj, hp]⟩

lemma prefSet_n_card {n q : ℕ} (enabled : (Fin n × Fin q × Bool × Fin q) → Bool)
    (p : Fin n → Bool) :
    (prefSet enabled p n).card = if p ∈ langSet enabled then 1 else 0 := by
  by_cases hp : p ∈ langSet enabled
  · simp only [hp, ite_true]
    have hEq : prefSet enabled p n = {p} := by
      ext y
      simp only [prefSet, Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro ⟨_, hpre⟩; funext i; exact hpre i i.isLt
      · intro hy; subst hy; exact ⟨hp, fun _ _ => rfl⟩
    rw [hEq, Finset.card_singleton]
  · simp only [hp, ite_false]
    apply Finset.card_eq_zero.mpr
    rw [Finset.eq_empty_iff_forall_notMem]
    intro y hy
    have hpre := (Finset.mem_filter.mp hy).2
    have hyeq : y = p := funext (fun i => hpre i i.isLt)
    subst hyeq
    exact hp (Finset.mem_filter.mp hy).1

def notVecAux (N : ℕ) (G : List BGate) (w : ℕ → ℕ) : ℕ → List BGate × (ℕ → ℕ)
  | 0 => (G, fun _ => 0)
  | k + 1 =>
    let r1 := notVecAux N G w k
    let r2 := emitGate N r1.1 (fun x _ => !x) (w k) 0
    (r2.1, fun i => if i = k then r2.2 else r1.2 i)

lemma notVecAux_spec {N : ℕ} (hN : 2 ≤ N) {G : List BGate} {w : ℕ → ℕ} (k : ℕ)
    (hWF : WF N G) (hw : ∀ i < k, w i < N + G.length) :
    let res := notVecAux N G w k
    Extends G res.1 ∧ res.1.length = G.length + k ∧ WF N res.1 ∧
    (∀ i < k, res.2 i < N + res.1.length) ∧
    ∀ src, src.length = N → ∀ i < k, evalW res.1 src (res.2 i) = !evalW G src (w i) := by
  induction k with
  | zero =>
    exact ⟨extends_rfl G, by simp [notVecAux], hWF, by intro i hi; omega, by intro _ _ i hi; omega⟩
  | succ m ih =>
    have hm := ih (fun i hi => hw i (by omega))
    dsimp only [notVecAux]
    set opNot : Bool → Bool → Bool := fun x _ => !x
    set r1 := notVecAux N G w m
    have he1 := hm.1
    have hl1 := hm.2.1
    have hw1 := hm.2.2.1
    have hout1 := hm.2.2.2.1
    have hev1 := hm.2.2.2.2
    set r2 := emitGate N r1.1 opNot (w m) 0
    have he2 : Extends r1.1 r2.1 := emitGate_extends N r1.1 opNot (w m) 0
    have hl2 : r2.1.length = r1.1.length + 1 := emitGate_len N r1.1 opNot (w m) 0
    have ho2 : r2.2 < N + r2.1.length := emitGate_out_lt N r1.1 opNot (w m) 0
    have hw2 : WF N r2.1 := emitGate_wf opNot hw1 (l := w m) (r := 0) (by have := hw m (by omega); omega) (by omega)
    refine ⟨extends_trans he1 he2, by omega, hw2, ?_, ?_⟩
    · intro i hi
      by_cases him : i = m
      · subst him; simp only [ite_true]; exact ho2
      · simp only [him, ite_false]; have := hout1 i (by omega); omega
    · intro src hsrc i hi
      by_cases him : i = m
      · subst him
        simp only [ite_true]
        rw [emitGate_eval opNot (w i) 0 hsrc]
        simp only [opNot]
        rw [evalW_extends he1 (by rw [hsrc]; exact hw i (by omega))]
      · simp only [him, ite_false]
        rw [evalW_extends he2 (by rw [hsrc]; exact hout1 i (by omega))]
        exact hev1 src hsrc i (by omega)

def notVec (N : ℕ) (G : List BGate) {n : ℕ} (w : Fin n → ℕ) : List BGate × (Fin n → ℕ) :=
  let res := notVecAux N G (fun i => if h : i < n then w ⟨i, h⟩ else 0) n
  (res.1, fun i : Fin n => res.2 i.val)

lemma notVec_spec {N n : ℕ} (hN : 2 ≤ N) {G : List BGate} {w : Fin n → ℕ}
    (hWF : WF N G) (hw : RegOK N G w) :
    let res := notVec N G w
    Extends G res.1 ∧ res.1.length = G.length + n ∧ WF N res.1 ∧ RegOK N res.1 res.2 ∧
    ∀ src, src.length = N → ∀ i : Fin n, evalW res.1 src (res.2 i) = !evalW G src (w i) := by
  have h := notVecAux_spec hN n hWF (w := fun i => if h : i < n then w ⟨i, h⟩ else 0)
    (fun i hi => by simp [hi, hw ⟨i, hi⟩])
  refine ⟨h.1, h.2.1, h.2.2.1, fun i => h.2.2.2.1 i.val i.isLt, ?_⟩
  intro src hsrc i
  simpa [notVec, i.isLt] using h.2.2.2.2 src hsrc i.val i.isLt

lemma zeroChildMaskW_ok {N n : ℕ} (hN : 2 ≤ N) {G : List BGate} {w nw : Fin n → ℕ}
    (hw : RegOK N G w) (hnw : RegOK N G nw) (k : Fin n) :
    ∀ i b, zeroChildMaskW w nw k i b < N + G.length := by
  intro i b
  unfold zeroChildMaskW
  split
  · cases b <;> simp [hw i, hnw i]
  · split
    · cases b <;> simp <;> omega
    · omega

lemma zeroChildMaskW_eval {N n : ℕ} {G : List BGate} {src : List Bool}
    {w nw : Fin n → ℕ} {p : Fin n → Bool} (hbase : HasBase src N)
    (hw : ∀ i, evalW G src (w i) = p i) (hnw : ∀ i, evalW G src (nw i) = !p i) (k : Fin n) :
    ∀ i b, evalW G src (zeroChildMaskW w nw k i b) = zeroChildMask p k i b := by
  intro i b
  unfold zeroChildMaskW zeroChildMask
  split
  · cases b <;> simp [hw i, hnw i]
  · split
    · cases b <;> simp [evalW_zero hbase, evalW_one hbase]
    · exact evalW_one hbase

def cmCost (n q a : ℕ) : ℕ :=
  let B := widthB n q a
  let Kbits := kBits a
  a * (n * (2 * a * q ^ (2 * a) + 12 * B * q ^ (3 * a)) + 5 * B * q ^ a) +
    2 * a * (5 * B * Kbits + 5 * B) + 5 * B + (n + 1) * (8 * B + 1)

noncomputable def buildRank {n q : ℕ} (N a : ℕ)
    (edgeW : (Fin n × Fin q × Bool × Fin q) → ℕ)
    (qW nqW : Fin n → ℕ) (G : List BGate) :
    (k : ℕ) → k ≤ n → List BGate × (Fin (n + 1) → ℕ)
  | 0, _ => (G, constReg (n + 1) 0)
  | k + 1, hk =>
    let r1 := buildRank N a edgeW qW nqW G k (by omega)
    let rc := countMask N a edgeW (zeroChildMaskW qW nqW ⟨k, hk⟩) r1.1
    let rg := regGate N rc.1 (qW ⟨k, hk⟩) rc.2
    let ra := regAdd N rg.1 r1.2 rg.2
    (ra.1, ra.2.1)

lemma buildRank_spec {N n q a : ℕ} (hN : 2 ≤ N) (hn : 0 < n) (hq : 0 < q)
    (edgeW : (Fin n × Fin q × Bool × Fin q) → ℕ)
    (qW nqW : Fin n → ℕ) (G : List BGate)
    (hWF : WF N G) (hedge : ∀ e, edgeW e < N)
    (hqW : RegOK N G qW) (hnqW : RegOK N G nqW) :
    ∀ (k : ℕ) (hk : k ≤ n),
      let res := buildRank N a edgeW qW nqW G k hk
      Extends G res.1 ∧
      res.1.length ≤ G.length + k * (cmCost n q a + 6 * (n + 1)) ∧
      WF N res.1 ∧
      RegOK N res.1 res.2 ∧
      ∀ src enabled query, HasBase src N →
        (∀ e, evalW G src (edgeW e) = enabled e) →
        (∀ i, evalW G src (qW i) = query i) →
        (∀ i, evalW G src (nqW i) = !query i) →
        (∀ x : Fin n → Bool, (closedPaths enabled x).card ≤ a) →
        regVal res.1 src res.2 = prefBefore enabled query k := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨extends_rfl G, by simp [buildRank], hWF, constReg_ok hN G 0, ?_⟩
    intro src enabled query hbase _ _ _ _
    simp [buildRank, constReg_val hbase, prefBefore_zero]
  | succ m ih =>
    intro hk
    have hm := ih (by omega)
    dsimp only [buildRank]
    set r1 := buildRank N a edgeW qW nqW G m (by omega)
    have hq1 : RegOK N r1.1 qW := regOK_extends hm.1 hqW
    have hnq1 : RegOK N r1.1 nqW := regOK_extends hm.1 hnqW
    have hcm := countMask_spec (a := a) hN hn hq edgeW (zeroChildMaskW qW nqW ⟨m, hk⟩) r1.1
      hm.2.2.1 hedge (zeroChildMaskW_ok hN hq1 hnq1 ⟨m, hk⟩)
    set rc := countMask N a edgeW (zeroChildMaskW qW nqW ⟨m, hk⟩) r1.1
    have hqm_lt : qW ⟨m, hk⟩ < N + rc.1.length := by
      have := hq1 ⟨m, hk⟩; have := extends_len hcm.1; omega
    have hrg := regGate_spec hcm.2.2.1 hqm_lt hcm.2.2.2.1
    set rg := regGate N rc.1 (qW ⟨m, hk⟩) rc.2
    have hr1_ok_rg : RegOK N rg.1 r1.2 := regOK_extends (extends_trans hcm.1 hrg.1) hm.2.2.2.1
    have hra := regAdd_spec hN hrg.2.2.1 hr1_ok_rg hrg.2.2.2.1
    refine ⟨extends_trans hm.1 (extends_trans hcm.1 (extends_trans hrg.1 hra.1)), ?_,
      hra.2.2.1, hra.2.2.2.1, ?_⟩
    · have h1 := hm.2.1; have h2 := hcm.2.1; have h3 := hrg.2.1; have h4 := hra.2.1
      have hsucc : (m + 1) * (cmCost n q a + 6 * (n + 1)) =
          m * (cmCost n q a + 6 * (n + 1)) + (cmCost n q a + 6 * (n + 1)) := Nat.succ_mul m _
      have h2' : rc.1.length ≤ r1.1.length + cmCost n q a := by
        unfold cmCost; dsimp only; omega
      omega
    · intro src enabled query hbase hed hqv hnqv hcap
      have hed1 : ∀ e, evalW r1.1 src (edgeW e) = enabled e := fun e => by
        rw [evalW_extends hm.1 (by rw [hbase.1]; have := hedge e; omega), hed e]
      have hqv1 : ∀ i, evalW r1.1 src (qW i) = query i := fun i => by
        rw [evalW_extends hm.1 (by rw [hbase.1]; exact hqW i), hqv i]
      have hnqv1 : ∀ i, evalW r1.1 src (nqW i) = !query i := fun i => by
        rw [evalW_extends hm.1 (by rw [hbase.1]; exact hnqW i), hnqv i]
      have hrc_val : regVal rc.1 src rc.2 =
          ((maskWords (zeroChildMask query ⟨m, hk⟩)).filter (fun x => (closedPaths enabled x).Nonempty)).card :=
        hcm.2.2.2.2 src enabled (zeroChildMask query ⟨m, hk⟩) hbase hed1
          (zeroChildMaskW_eval hbase hqv1 hnqv1 ⟨m, hk⟩) hcap
      have hqm_val : evalW rc.1 src (qW ⟨m, hk⟩) = query ⟨m, hk⟩ := by
        rw [evalW_extends hcm.1 (by rw [hbase.1]; exact hq1 ⟨m, hk⟩), hqv1 ⟨m, hk⟩]
      have hrg_val : regVal rg.1 src rg.2 =
          if query ⟨m, hk⟩ = true then
            ((maskWords (zeroChildMask query ⟨m, hk⟩)).filter (fun x => (closedPaths enabled x).Nonempty)).card
          else 0 := by
        rw [hrg.2.2.2.2 src hbase.1, hqm_val, hrc_val]
      have hr1_val : regVal rg.1 src r1.2 = prefBefore enabled query m := by
        rw [regVal_extends (extends_trans hcm.1 hrg.1) hbase.1 hm.2.2.2.1]
        exact hm.2.2.2.2 src enabled query hbase hed hqv hnqv hcap
      have hsum_eq : regVal rg.1 src r1.2 + regVal rg.1 src rg.2 = prefBefore enabled query (m + 1) := by
        rw [hr1_val, hrg_val, prefBefore_succ enabled query m hk]
      have hsum_lt : regVal rg.1 src r1.2 + regVal rg.1 src rg.2 < 2 ^ (n + 1) := by
        rw [hsum_eq]
        unfold prefBefore
        calc ((langSet enabled).filter _).card
            ≤ (Finset.univ : Finset (Fin n → Bool)).card := Finset.card_le_card (Finset.subset_univ _)
          _ = 2 ^ n := by simp
          _ < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
      rw [regAdd_val_of_lt hN hrg.2.2.1 hr1_ok_rg hrg.2.2.2.1 hbase hsum_lt, hsum_eq]

noncomputable def buildUnrank {n q : ℕ} (N a : ℕ)
    (edgeW : (Fin n × Fin q × Bool × Fin q) → ℕ)
    (indexReg : Fin (n + 1) → ℕ) (G : List BGate) :
    (k : ℕ) → k ≤ n → List BGate × (Fin n → ℕ) × (Fin n → ℕ) × (Fin (n + 1) → ℕ)
  | 0, _ => (G, fun _ => 0, fun _ => 1, indexReg)
  | k + 1, hk =>
    let r1 := buildUnrank N a edgeW indexReg G k (by omega)
    let rc := countMask N a edgeW (zeroChildMaskW r1.2.1 r1.2.2.1 ⟨k, hk⟩) r1.1
    let rs := regSub N rc.1 r1.2.2.2 rc.2
    let rbit := emitGate N rs.1 (fun x _ => !x) rs.2.2 0
    let rmux := regMux N rbit.1 rbit.2 rs.2.1 r1.2.2.2
    (rmux.1,
      fun i : Fin n => if i.val = k then rbit.2 else r1.2.1 i,
      fun i : Fin n => if i.val = k then rs.2.2 else r1.2.2.1 i,
      rmux.2)

lemma buildUnrank_spec {N n q a : ℕ} (hN : 2 ≤ N) (hn : 0 < n) (hq : 0 < q)
    (edgeW : (Fin n × Fin q × Bool × Fin q) → ℕ)
    (indexReg : Fin (n + 1) → ℕ) (G : List BGate)
    (hWF : WF N G) (hedge : ∀ e, edgeW e < N) (hidx : RegOK N G indexReg) :
    ∀ (k : ℕ) (hk : k ≤ n),
      let res := buildUnrank N a edgeW indexReg G k hk
      Extends G res.1 ∧
      res.1.length ≤ G.length + k * (cmCost n q a + 8 * (n + 1) + 1) ∧
      WF N res.1 ∧
      RegOK N res.1 res.2.1 ∧ RegOK N res.1 res.2.2.1 ∧ RegOK N res.1 res.2.2.2 ∧
      ∀ src enabled, HasBase src N →
        (∀ e, evalW G src (edgeW e) = enabled e) →
        (∀ x : Fin n → Bool, (closedPaths enabled x).card ≤ a) →
        (∀ i : Fin n, evalW res.1 src (res.2.2.1 i) = !evalW res.1 src (res.2.1 i)) ∧
        (regVal G src indexReg < (langSet enabled).card →
          let p : Fin n → Bool := fun i => evalW res.1 src (res.2.1 i)
          regVal res.1 src res.2.2.2 < (prefSet enabled p k).card ∧
          prefBefore enabled p k + regVal res.1 src res.2.2.2 = regVal G src indexReg) := by
  intro k
  induction k with
  | zero =>
    intro _
    dsimp only [buildUnrank]
    refine ⟨extends_rfl G, by simp, hWF,
      fun _ => by dsimp only; omega, fun _ => by dsimp only; omega, hidx, ?_⟩
    intro src enabled hbase _ _
    refine ⟨fun i => by simp [evalW_zero hbase, evalW_one hbase], ?_⟩
    intro hlt
    rw [prefSet_zero, prefBefore_zero, Nat.zero_add]
    exact ⟨hlt, rfl⟩
  | succ m ih =>
    intro hk
    have hm := ih (by omega)
    dsimp only [buildUnrank]
    set r1 := buildUnrank N a edgeW indexReg G m (by omega)
    have hcm := countMask_spec (a := a) hN hn hq edgeW (zeroChildMaskW r1.2.1 r1.2.2.1 ⟨m, hk⟩) r1.1
      hm.2.2.1 hedge (zeroChildMaskW_ok hN hm.2.2.2.1 hm.2.2.2.2.1 ⟨m, hk⟩)
    set rc := countMask N a edgeW (zeroChildMaskW r1.2.1 r1.2.2.1 ⟨m, hk⟩) r1.1
    have hrem1_rc : RegOK N rc.1 r1.2.2.2 := regOK_extends hcm.1 hm.2.2.2.2.2.1
    have hrs := regSub_spec hN hcm.2.2.1 hrem1_rc hcm.2.2.2.1
    set rs := regSub N rc.1 r1.2.2.2 rc.2
    set opNot : Bool → Bool → Bool := fun x _ => !x
    set rbit := emitGate N rs.1 opNot rs.2.2 0
    have hebit : Extends rs.1 rbit.1 := emitGate_extends N rs.1 opNot rs.2.2 0
    have hlbit : rbit.1.length = rs.1.length + 1 := emitGate_len N rs.1 opNot rs.2.2 0
    have hobit : rbit.2 < N + rbit.1.length := emitGate_out_lt N rs.1 opNot rs.2.2 0
    have hwbit : WF N rbit.1 := emitGate_wf opNot hrs.2.2.1 (l := rs.2.2) (r := 0) hrs.2.2.2.2.1 (by omega)
    have hdiff_ok : RegOK N rbit.1 rs.2.1 := regOK_extends hebit hrs.2.2.2.1
    have hrem1_bit : RegOK N rbit.1 r1.2.2.2 := regOK_extends (extends_trans hrs.1 hebit) hrem1_rc
    have hmux := regMux_spec hwbit hobit hdiff_ok hrem1_bit
    set rmux := regMux N rbit.1 rbit.2 rs.2.1 r1.2.2.2
    have he_r1_rmux : Extends r1.1 rmux.1 :=
      extends_trans hcm.1 (extends_trans hrs.1 (extends_trans hebit hmux.1))
    refine ⟨extends_trans hm.1 he_r1_rmux, ?_, hmux.2.2.1, ?_, ?_, hmux.2.2.2.1, ?_⟩
    · have h1 := hm.2.1; have h2 := hcm.2.1; have h3 := hrs.2.1; have h4 := hmux.2.1
      have h2' : rc.1.length ≤ r1.1.length + cmCost n q a := by
        unfold cmCost; dsimp only; omega
      have hsucc : (m + 1) * (cmCost n q a + 8 * (n + 1) + 1) =
          m * (cmCost n q a + 8 * (n + 1) + 1) + (cmCost n q a + 8 * (n + 1) + 1) := Nat.succ_mul m _
      omega
    · intro i
      by_cases him : i.val = m
      · simp only [him, ite_true]; have := extends_len hmux.1; omega
      · simp only [him, ite_false]; exact regOK_extends he_r1_rmux hm.2.2.2.1 i
    · intro i
      by_cases him : i.val = m
      · simp only [him, ite_true]
        have := hrs.2.2.2.2.1
        have := extends_len (extends_trans hebit hmux.1)
        omega
      · simp only [him, ite_false]; exact regOK_extends he_r1_rmux hm.2.2.2.2.1 i
    · intro src enabled hbase hed hcap
      have hih_ev := hm.2.2.2.2.2.2 src enabled hbase hed hcap
      have hbor_rmux : evalW rmux.1 src rs.2.2 = evalW rs.1 src rs.2.2 :=
        evalW_extends (extends_trans hebit hmux.1) (by rw [hbase.1]; exact hrs.2.2.2.2.1)
      have hbit_rmux : evalW rmux.1 src rbit.2 = !evalW rs.1 src rs.2.2 := by
        rw [evalW_extends hmux.1 (by rw [hbase.1]; exact hobit)]
        rw [emitGate_eval opNot rs.2.2 0 hbase.1]
      refine ⟨?_, ?_⟩
      · intro i
        by_cases him : i.val = m
        · simp only [him, ite_true, hbor_rmux, hbit_rmux, Bool.not_not]
        · simp only [him, ite_false]
          rw [evalW_extends he_r1_rmux (by rw [hbase.1]; exact hm.2.2.2.2.1 i)]
          rw [evalW_extends he_r1_rmux (by rw [hbase.1]; exact hm.2.2.2.1 i)]
          exact hih_ev.1 i
      · intro hidx_lt
        set p1 : Fin n → Bool := fun i => evalW r1.1 src (r1.2.1 i)
        set p2 : Fin n → Bool := fun i => evalW rmux.1 src (if i.val = m then rbit.2 else r1.2.1 i)
        have hinv1 := hih_ev.2 hidx_lt
        have hed1 : ∀ e, evalW r1.1 src (edgeW e) = enabled e := fun e => by
          rw [evalW_extends hm.1 (by rw [hbase.1]; have := hedge e; omega), hed e]
        have hrc_val : regVal rc.1 src rc.2 =
            ((maskWords (zeroChildMask p1 ⟨m, hk⟩)).filter (fun x => (closedPaths enabled x).Nonempty)).card :=
          hcm.2.2.2.2 src enabled (zeroChildMask p1 ⟨m, hk⟩) hbase hed1
            (zeroChildMaskW_eval hbase (fun _ => rfl) hih_ev.1 ⟨m, hk⟩) hcap
        have hrem1_val : regVal rc.1 src r1.2.2.2 = regVal r1.1 src r1.2.2.2 :=
          regVal_extends hcm.1 hbase.1 hm.2.2.2.2.2.1
        have hbor_iff : evalW rs.1 src rs.2.2 = true ↔ regVal r1.1 src r1.2.2.2 < regVal rc.1 src rc.2 := by
          have := regSub_borrow_iff hN hcm.2.2.1 hrem1_rc hcm.2.2.2.1 hbase
          rw [hrem1_val] at this
          exact this
        have hsplit := prefSet_succ_split enabled p1 m hk
        have hp2_lt : ∀ i : Fin n, i.val < m → p2 i = p1 i := by
          intro i hi
          have hne : i.val ≠ m := by omega
          simp only [p2, hne, ite_false]
          exact evalW_extends he_r1_rmux (by rw [hbase.1]; exact hm.2.2.2.1 i)
        have hp2_m : p2 ⟨m, hk⟩ = !evalW rs.1 src rs.2.2 := by
          simp only [p2, ite_true, hbit_rmux]
        have hmux_val : regVal rmux.1 src rmux.2 =
            if !evalW rs.1 src rs.2.2 then regVal rs.1 src rs.2.1 else regVal r1.1 src r1.2.2.2 := by
          rw [hmux.2.2.2.2 src hbase.1]
          rw [emitGate_eval opNot rs.2.2 0 hbase.1]
          simp only [opNot]
          rw [regVal_extends hebit hbase.1 hrs.2.2.2.1]
          rw [regVal_extends (extends_trans hcm.1 (extends_trans hrs.1 hebit)) hbase.1 hm.2.2.2.2.2.1]
        have hp2_agree : ∀ (b : Bool), p2 ⟨m, hk⟩ = b →
            prefSet enabled p2 (m + 1) = prefSet enabled (fun i => if i.val = m then b else p1 i) (m + 1) := by
          intro b hb
          ext y
          simp only [prefSet, Finset.mem_filter]
          constructor <;> rintro ⟨hl, hpre⟩ <;> refine ⟨hl, fun i hi => ?_⟩
          · by_cases him : i.val = m
            · have : i = ⟨m, hk⟩ := Fin.ext him; subst this; simp [hpre ⟨m, hk⟩ hi, hb]
            · simp [him, ← hp2_lt i (by omega), hpre i hi]
          · by_cases him : i.val = m
            · have : i = ⟨m, hk⟩ := Fin.ext him; subst this; simp [hb]; simpa using hpre ⟨m, hk⟩ hi
            · rw [hp2_lt i (by omega)]; simpa [him] using hpre i hi
        have hpb_eq : prefBefore enabled p2 m = prefBefore enabled p1 m :=
          prefBefore_congr enabled p2 p1 m hp2_lt
        have hzc_eq : zeroChildMask p2 ⟨m, hk⟩ = zeroChildMask p1 ⟨m, hk⟩ := by
          funext i b
          unfold zeroChildMask
          split
          · rename_i hlt; rw [hp2_lt i hlt]
          · rfl
        cases hbor : evalW rs.1 src rs.2.2
        · have hge : regVal rc.1 src rc.2 ≤ regVal r1.1 src r1.2.2.2 := by
            by_contra hlt'
            have hlt'' : regVal r1.1 src r1.2.2.2 < regVal rc.1 src rc.2 := by omega
            have := hbor_iff.mpr hlt''
            rw [hbor] at this; cases this
          have hdiff : regVal rs.1 src rs.2.1 = regVal r1.1 src r1.2.2.2 - regVal rc.1 src rc.2 := by
            have := regSub_val_of_le hN hcm.2.2.1 hrem1_rc hcm.2.2.2.1 hbase (by rw [hrem1_val]; exact hge)
            rw [hrem1_val] at this; exact this
          have hrem2 : regVal rmux.1 src rmux.2 = regVal r1.1 src r1.2.2.2 - regVal rc.1 src rc.2 := by
            rw [hmux_val, hbor]; simp [hdiff]
          have hp2m_t : p2 ⟨m, hk⟩ = true := by rw [hp2_m, hbor]; rfl
          have hps_eq := hp2_agree true hp2m_t
          rw [hps_eq, hrem2, prefBefore_succ enabled p2 m hk, hpb_eq, hp2m_t, hzc_eq]
          simp only [ite_true]
          rw [hrc_val] at hge ⊢
          have hinv_lt := hinv1.1
          have hinv_eq := hinv1.2
          rw [hsplit.1, hsplit.2] at hinv_lt
          omega
        · have hlt' : regVal r1.1 src r1.2.2.2 < regVal rc.1 src rc.2 := hbor_iff.mp hbor
          have hrem2 : regVal rmux.1 src rmux.2 = regVal r1.1 src r1.2.2.2 := by
            rw [hmux_val, hbor]; simp
          have hp2m_f : p2 ⟨m, hk⟩ = false := by rw [hp2_m, hbor]; rfl
          have hps_eq := hp2_agree false hp2m_f
          rw [hps_eq, hrem2, prefBefore_succ enabled p2 m hk, hpb_eq, hp2m_f]
          simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
          rw [hrc_val, ← hsplit.2] at hlt'
          exact ⟨hlt', hinv1.2⟩

lemma cmCost_le (n q a : ℕ) (hq : 0 < q) :
    cmCost n q a ≤ 53 * (n + 1) * (a + 2) ^ 3 * widthB n q a * (q + 1) ^ (3 * (a + 1)) := by
  unfold cmCost
  dsimp only
  set B := widthB n q a
  set K := kBits a
  set Q := (q + 1) ^ (3 * (a + 1))
  have hQ1 : 1 ≤ Q := Nat.one_le_pow _ _ (by omega)
  have hq2a : q ^ (2 * a) ≤ Q := by
    calc q ^ (2 * a) ≤ (q + 1) ^ (2 * a) := Nat.pow_le_pow_left (by omega) _
      _ ≤ (q + 1) ^ (3 * (a + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
  have hq3a : q ^ (3 * a) ≤ Q := by
    calc q ^ (3 * a) ≤ (q + 1) ^ (3 * a) := Nat.pow_le_pow_left (by omega) _
      _ ≤ (q + 1) ^ (3 * (a + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
  have hqa : q ^ a ≤ Q := by
    calc q ^ a ≤ (q + 1) ^ a := Nat.pow_le_pow_left (by omega) _
      _ ≤ (q + 1) ^ (3 * (a + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
  have haB : a ≤ B := by
    have h1 : a ≤ (a + 1) * (a + 1) := by nlinarith
    unfold B widthB; omega
  have hB1 : 1 ≤ B := by unfold B widthB; omega
  have hK : K ≤ (a + 2) ^ 2 := kBits_le a
  have hterm1 : a * (n * (2 * a * q ^ (2 * a) + 12 * B * q ^ (3 * a)) + 5 * B * q ^ a) ≤
      19 * (n + 1) * (a + 2) ^ 3 * B * Q := by
    have hinner : 2 * a * q ^ (2 * a) + 12 * B * q ^ (3 * a) ≤ 14 * B * Q := by
      have h1 : 2 * a * q ^ (2 * a) ≤ 2 * B * Q :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 haB) hq2a
      have h2 : 12 * B * q ^ (3 * a) ≤ 12 * B * Q := Nat.mul_le_mul_left (12 * B) hq3a
      have hsum : 2 * B * Q + 12 * B * Q = 14 * B * Q := by ring
      omega
    have h2 : n * (2 * a * q ^ (2 * a) + 12 * B * q ^ (3 * a)) + 5 * B * q ^ a ≤
        19 * (n + 1) * B * Q := by
      have ha1 : n * (2 * a * q ^ (2 * a) + 12 * B * q ^ (3 * a)) ≤ n * (14 * B * Q) :=
        Nat.mul_le_mul_left n hinner
      have ha2 : 5 * B * q ^ a ≤ 5 * B * Q := Nat.mul_le_mul_left (5 * B) hqa
      have h3 : n * (14 * B * Q) + 5 * B * Q ≤ 19 * (n + 1) * B * Q := by
        have hEq : 19 * (n + 1) * B * Q = n * (14 * B * Q) + 5 * B * Q + (5 * n + 14) * B * Q := by ring
        omega
      omega
    have ha3 : a ≤ (a + 2) ^ 3 := by nlinarith
    calc a * (n * (2 * a * q ^ (2 * a) + 12 * B * q ^ (3 * a)) + 5 * B * q ^ a)
        ≤ (a + 2) ^ 3 * (19 * (n + 1) * B * Q) := Nat.mul_le_mul ha3 h2
      _ = 19 * (n + 1) * (a + 2) ^ 3 * B * Q := by ring
  have hterm2 : 2 * a * (5 * B * K + 5 * B) ≤ 20 * (n + 1) * (a + 2) ^ 3 * B * Q := by
    have hK1 : 5 * B * K + 5 * B ≤ 10 * B * (a + 2) ^ 2 := by
      have h1 : 5 * B * K ≤ 5 * B * (a + 2) ^ 2 := Nat.mul_le_mul_left (5 * B) hK
      have h2 : 5 * B ≤ 5 * B * (a + 2) ^ 2 := Nat.le_mul_of_pos_right _ (by nlinarith)
      have hsum : 5 * B * (a + 2) ^ 2 + 5 * B * (a + 2) ^ 2 = 10 * B * (a + 2) ^ 2 := by ring
      omega
    have h1 : 2 * a * (5 * B * K + 5 * B) ≤ 2 * (a + 2) * (10 * B * (a + 2) ^ 2) :=
      Nat.mul_le_mul (by omega) hK1
    have h2 : 2 * (a + 2) * (10 * B * (a + 2) ^ 2) = 20 * (a + 2) ^ 3 * B := by ring
    have h3 : 20 * (a + 2) ^ 3 * B ≤ 20 * (n + 1) * (a + 2) ^ 3 * B * Q := by
      have hn1 : 1 ≤ n + 1 := by omega
      calc 20 * (a + 2) ^ 3 * B = 20 * 1 * (a + 2) ^ 3 * B * 1 := by ring
        _ ≤ 20 * (n + 1) * (a + 2) ^ 3 * B * Q :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 20 hn1))) hQ1
    omega
  have hterm3 : 5 * B + (n + 1) * (8 * B + 1) ≤ 14 * (n + 1) * (a + 2) ^ 3 * B * Q := by
    have h1 : 5 * B + (n + 1) * (8 * B + 1) ≤ 14 * (n + 1) * B := by nlinarith
    have ha1 : 1 ≤ (a + 2) ^ 3 := by nlinarith
    calc 5 * B + (n + 1) * (8 * B + 1)
        ≤ 14 * (n + 1) * B := h1
      _ = 14 * (n + 1) * 1 * B * 1 := by ring
      _ ≤ 14 * (n + 1) * (a + 2) ^ 3 * B * Q :=
        Nat.mul_le_mul (Nat.mul_le_mul_right B (Nat.mul_le_mul_left (14 * (n + 1)) ha1)) hQ1
  have htot : 19 * (n + 1) * (a + 2) ^ 3 * B * Q + 20 * (n + 1) * (a + 2) ^ 3 * B * Q +
      14 * (n + 1) * (a + 2) ^ 3 * B * Q = 53 * (n + 1) * (a + 2) ^ 3 * B * Q := by ring
  omega

lemma capCost_le (n q a : ℕ) (hq : 0 < q) :
    let B := widthB n q a
    let Kbits := kBits a
    (a + 1) * (n * (2 * (a + 1) * q ^ (2 * (a + 1)) + 12 * B * q ^ (3 * (a + 1))) + 5 * B * q ^ (a + 1)) +
      2 * (a + 1) * (5 * B * Kbits + 5 * B) + 2 * B ≤
      41 * (n + 1) * (a + 2) ^ 3 * widthB n q a * (q + 1) ^ (3 * (a + 1)) := by
  dsimp only
  set B := widthB n q a
  set K := kBits a
  set Q := (q + 1) ^ (3 * (a + 1))
  have hQ1 : 1 ≤ Q := Nat.one_le_pow _ _ (by omega)
  have hq2 : q ^ (2 * (a + 1)) ≤ Q := by
    calc q ^ (2 * (a + 1)) ≤ (q + 1) ^ (2 * (a + 1)) := Nat.pow_le_pow_left (by omega) _
      _ ≤ (q + 1) ^ (3 * (a + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
  have hq3 : q ^ (3 * (a + 1)) ≤ Q := Nat.pow_le_pow_left (by omega) _
  have hq1 : q ^ (a + 1) ≤ Q := by
    calc q ^ (a + 1) ≤ (q + 1) ^ (a + 1) := Nat.pow_le_pow_left (by omega) _
      _ ≤ (q + 1) ^ (3 * (a + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
  have ha1B : a + 1 ≤ B := by
    have h1 : a + 1 ≤ (a + 1) * (a + 1) := by nlinarith
    unfold B widthB; omega
  have hK : K ≤ (a + 2) ^ 2 := kBits_le a
  have hterm1 : (a + 1) * (n * (2 * (a + 1) * q ^ (2 * (a + 1)) + 12 * B * q ^ (3 * (a + 1))) + 5 * B * q ^ (a + 1)) ≤
      19 * (n + 1) * (a + 2) ^ 3 * B * Q := by
    have hinner : 2 * (a + 1) * q ^ (2 * (a + 1)) + 12 * B * q ^ (3 * (a + 1)) ≤ 14 * B * Q := by
      have h1 : 2 * (a + 1) * q ^ (2 * (a + 1)) ≤ 2 * B * Q :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 ha1B) hq2
      have h2 : 12 * B * q ^ (3 * (a + 1)) ≤ 12 * B * Q := Nat.mul_le_mul_left (12 * B) hq3
      have hsum : 2 * B * Q + 12 * B * Q = 14 * B * Q := by ring
      omega
    have h2 : n * (2 * (a + 1) * q ^ (2 * (a + 1)) + 12 * B * q ^ (3 * (a + 1))) + 5 * B * q ^ (a + 1) ≤
        19 * (n + 1) * B * Q := by
      have ha1 : n * (2 * (a + 1) * q ^ (2 * (a + 1)) + 12 * B * q ^ (3 * (a + 1))) ≤ n * (14 * B * Q) :=
        Nat.mul_le_mul_left n hinner
      have ha2 : 5 * B * q ^ (a + 1) ≤ 5 * B * Q := Nat.mul_le_mul_left (5 * B) hq1
      have h3 : n * (14 * B * Q) + 5 * B * Q ≤ 19 * (n + 1) * B * Q := by
        have hEq : 19 * (n + 1) * B * Q = n * (14 * B * Q) + 5 * B * Q + (5 * n + 14) * B * Q := by ring
        omega
      omega
    have ha3 : a + 1 ≤ (a + 2) ^ 3 := by nlinarith
    calc (a + 1) * (n * (2 * (a + 1) * q ^ (2 * (a + 1)) + 12 * B * q ^ (3 * (a + 1))) + 5 * B * q ^ (a + 1))
        ≤ (a + 2) ^ 3 * (19 * (n + 1) * B * Q) := Nat.mul_le_mul ha3 h2
      _ = 19 * (n + 1) * (a + 2) ^ 3 * B * Q := by ring
  have hterm2 : 2 * (a + 1) * (5 * B * K + 5 * B) ≤ 20 * (n + 1) * (a + 2) ^ 3 * B * Q := by
    have hK1 : 5 * B * K + 5 * B ≤ 10 * B * (a + 2) ^ 2 := by
      have h1 : 5 * B * K ≤ 5 * B * (a + 2) ^ 2 := Nat.mul_le_mul_left (5 * B) hK
      have h2 : 5 * B ≤ 5 * B * (a + 2) ^ 2 := Nat.le_mul_of_pos_right _ (by nlinarith)
      have hsum : 5 * B * (a + 2) ^ 2 + 5 * B * (a + 2) ^ 2 = 10 * B * (a + 2) ^ 2 := by ring
      omega
    have h1 : 2 * (a + 1) * (5 * B * K + 5 * B) ≤ 2 * (a + 2) * (10 * B * (a + 2) ^ 2) :=
      Nat.mul_le_mul (by omega) hK1
    have h2 : 2 * (a + 2) * (10 * B * (a + 2) ^ 2) = 20 * (a + 2) ^ 3 * B := by ring
    have h3 : 20 * (a + 2) ^ 3 * B ≤ 20 * (n + 1) * (a + 2) ^ 3 * B * Q := by
      have hn1 : 1 ≤ n + 1 := by omega
      calc 20 * (a + 2) ^ 3 * B = 20 * 1 * (a + 2) ^ 3 * B * 1 := by ring
        _ ≤ 20 * (n + 1) * (a + 2) ^ 3 * B * Q :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 20 hn1))) hQ1
    omega
  have hterm3 : 2 * B ≤ 2 * (n + 1) * (a + 2) ^ 3 * B * Q := by
    have h1 : 1 ≤ (n + 1) * (a + 2) ^ 3 := Nat.mul_pos (by omega) (by nlinarith)
    calc 2 * B = 2 * 1 * B * 1 := by ring
      _ ≤ 2 * ((n + 1) * (a + 2) ^ 3) * B * Q :=
        Nat.mul_le_mul (Nat.mul_le_mul_right B (Nat.mul_le_mul_left 2 h1)) hQ1
      _ = 2 * (n + 1) * (a + 2) ^ 3 * B * Q := by ring
  have htot : 19 * (n + 1) * (a + 2) ^ 3 * B * Q + 20 * (n + 1) * (a + 2) ^ 3 * B * Q +
      2 * (n + 1) * (a + 2) ^ 3 * B * Q = 41 * (n + 1) * (a + 2) ^ 3 * B * Q := by ring
  omega

lemma wire_lt_extends {N : ℕ} {G1 G2 : List BGate} {w : ℕ}
    (he : Extends G1 G2) (hw : w < N + G1.length) : w < N + G2.length := by
  have := extends_len he; omega

lemma add5_assoc (x a b c d : ℕ) : x + a + b + c + d = x + (a + b + c + d) := by omega

lemma total_gates_bound (n q a gCap gCard gNQ gQ1 gF1 gRank gUnr gF2 gSel : ℕ)
    (hq : 0 < q)
    (hCap : gCap ≤ 41 * (n + 1) * (a + 2) ^ 3 * widthB n q a * (q + 1) ^ (3 * (a + 1)))
    (hCard : gCard ≤ gCap + cmCost n q a)
    (hNQ : gNQ = gCard + n)
    (hQ1 : gQ1 ≤ gNQ + n * (2 * 1 * q ^ (2 * 1) + 12 * widthB n q a * q ^ (3 * 1)) + 5 * widthB n q a * q ^ 1)
    (hF1 : gF1 = gQ1 + widthB n q a)
    (hRank : gRank ≤ gF1 + n * (cmCost n q a + 6 * (n + 1)))
    (hUnr : gUnr ≤ gRank + n * (cmCost n q a + 8 * (n + 1) + 1))
    (hF2 : gF2 = gUnr + 5 * (n + 1))
    (hSel : gSel = gF2 + n) :
    gSel ≤ 250 * (n + 1) ^ 4 * (a + 2) ^ 6 * (q + 1) ^ (3 * (a + 1)) * (Nat.clog 2 (q + 2) + 1) ^ 2 := by
  set B := widthB n q a
  set L := Nat.clog 2 (q + 2) + 1
  set Q := (q + 1) ^ (3 * (a + 1))
  set U := (n + 1) * (a + 2) ^ 3 * B * Q
  set V := (n + 1) * U
  have hL1 : 1 ≤ L := by omega
  have hQ_one : 1 ≤ Q := Nat.one_le_pow _ _ (by omega)
  have hB_le : B ≤ (n + 1) * (a + 2) ^ 2 * L := widthB_le n q a
  have hB1 : 1 ≤ B := by unfold B widthB; omega
  have hU_le_V : U ≤ V := Nat.le_mul_of_pos_left U (by omega)
  have hCap_V : gCap ≤ 41 * V := by
    have hEq : 41 * (n + 1) * (a + 2) ^ 3 * B * Q = 41 * U := by simp only [U]; ring
    rw [hEq] at hCap
    exact le_trans hCap (Nat.mul_le_mul_left 41 hU_le_V)
  have hCM_U : cmCost n q a ≤ 53 * U := by
    have h1 := cmCost_le n q a hq
    have hEq : 53 * (n + 1) * (a + 2) ^ 3 * B * Q = 53 * U := by simp only [U]; ring
    rw [hEq] at h1
    exact h1
  have hCM_V : cmCost n q a ≤ 53 * V := le_trans hCM_U (Nat.mul_le_mul_left 53 hU_le_V)
  have hCM_nV : n * cmCost n q a ≤ 53 * V := by
    calc n * cmCost n q a ≤ (n + 1) * (53 * U) := Nat.mul_le_mul (by omega) hCM_U
      _ = 53 * V := by simp only [V]; ring
  have hQ1Bound : n * (2 * 1 * q ^ (2 * 1) + 12 * B * q ^ (3 * 1)) + 5 * B * q ^ 1 ≤
      19 * (n + 1) * B * Q := by
    have hq2 : q ^ (2 * 1) ≤ Q := by
      calc q ^ 2 ≤ (q + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ ≤ (q + 1) ^ (3 * (a + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
    have hq3 : q ^ (3 * 1) ≤ Q := by
      calc q ^ 3 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
        _ ≤ (q + 1) ^ (3 * (a + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
    have hq1' : q ^ 1 ≤ Q := by
      calc q ^ 1 ≤ (q + 1) ^ 1 := Nat.pow_le_pow_left (by omega) 1
        _ ≤ (q + 1) ^ (3 * (a + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
    have h1 : 2 * 1 * q ^ (2 * 1) + 12 * B * q ^ (3 * 1) ≤ 14 * B * Q := by
      have ha1 : 2 * 1 * q ^ (2 * 1) ≤ 2 * B * Q := Nat.mul_le_mul (by omega) hq2
      have ha2 : 12 * B * q ^ (3 * 1) ≤ 12 * B * Q := Nat.mul_le_mul_left (12 * B) hq3
      have hsum : 2 * B * Q + 12 * B * Q = 14 * B * Q := by ring
      omega
    have h2 : n * (2 * 1 * q ^ (2 * 1) + 12 * B * q ^ (3 * 1)) ≤ n * (14 * B * Q) :=
      Nat.mul_le_mul_left n h1
    have h3 : 5 * B * q ^ 1 ≤ 5 * B * Q := Nat.mul_le_mul_left (5 * B) hq1'
    have hEq : 19 * (n + 1) * B * Q = n * (14 * B * Q) + 5 * B * Q + (5 * n + 14) * B * Q := by ring
    omega
  have ha3_one : 1 ≤ (a + 2) ^ 3 := Nat.one_le_pow 3 (a + 2) (by omega)
  have hQ1_V : n * (2 * 1 * q ^ (2 * 1) + 12 * B * q ^ (3 * 1)) + 5 * B * q ^ 1 ≤ 19 * V := by
    have h1 : (n + 1) * B * Q ≤ U := by
      calc (n + 1) * B * Q = (n + 1) * 1 * B * Q := by ring
        _ ≤ (n + 1) * (a + 2) ^ 3 * B * Q :=
          Nat.mul_le_mul_right Q (Nat.mul_le_mul_right B (Nat.mul_le_mul_left (n + 1) ha3_one))
    have h2 : 19 * (n + 1) * B * Q = 19 * ((n + 1) * B * Q) := by ring
    calc n * (2 * 1 * q ^ (2 * 1) + 12 * B * q ^ (3 * 1)) + 5 * B * q ^ 1
        ≤ 19 * (n + 1) * B * Q := hQ1Bound
      _ = 19 * ((n + 1) * B * Q) := h2
      _ ≤ 19 * V := Nat.mul_le_mul_left 19 (le_trans h1 hU_le_V)
  have hB_V : B ≤ V := by
    have h1 : B ≤ U := by
      have ha3 : 1 ≤ (n + 1) * (a + 2) ^ 3 := Nat.mul_pos (by omega) ha3_one
      calc B = 1 * B * 1 := by ring
        _ ≤ ((n + 1) * (a + 2) ^ 3) * B * Q :=
          Nat.mul_le_mul (Nat.mul_le_mul_right B ha3) hQ_one
        _ = U := by simp only [U]
    exact le_trans h1 hU_le_V
  have hsq_V : (n + 1) ^ 2 ≤ V := by
    have h1 : n + 1 ≤ U := by
      calc n + 1 = (n + 1) * 1 * 1 * 1 := by ring
        _ ≤ (n + 1) * (a + 2) ^ 3 * B * Q :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left (n + 1) ha3_one) hB1) hQ_one
    calc (n + 1) ^ 2 = (n + 1) * (n + 1) := by ring
      _ ≤ (n + 1) * U := Nat.mul_le_mul_left (n + 1) h1
  have hsmall : n + n * (6 * (n + 1)) + n * (8 * (n + 1) + 1) + 5 * (n + 1) + n ≤ 22 * (n + 1) ^ 2 := by
    have hEq : 22 * (n + 1) ^ 2 =
        n + n * (6 * (n + 1)) + n * (8 * (n + 1) + 1) + 5 * (n + 1) + n + (8 * n ^ 2 + 22 * n + 17) := by
      ring
    omega
  have hrank_exp : n * (cmCost n q a + 6 * (n + 1)) = n * cmCost n q a + n * (6 * (n + 1)) := by ring
  have hunr_exp : n * (cmCost n q a + 8 * (n + 1) + 1) = n * cmCost n q a + n * (8 * (n + 1) + 1) := by ring
  rw [hrank_exp] at hRank
  rw [hunr_exp] at hUnr
  have hTotV : gSel ≤ 250 * V := by omega
  have hV_target : V ≤ (n + 1) ^ 4 * (a + 2) ^ 6 * Q * L ^ 2 := by
    have hstep1 : V ≤ (n + 1) ^ 3 * (a + 2) ^ 5 * Q * L := by
      calc V = (n + 1) ^ 2 * (a + 2) ^ 3 * B * Q := by simp only [V, U]; ring
        _ ≤ (n + 1) ^ 2 * (a + 2) ^ 3 * ((n + 1) * (a + 2) ^ 2 * L) * Q :=
            Nat.mul_le_mul_right Q (Nat.mul_le_mul_left _ hB_le)
        _ = (n + 1) ^ 3 * (a + 2) ^ 5 * Q * L := by ring
    have hstep2 : (n + 1) ^ 3 * (a + 2) ^ 5 * Q * L ≤ (n + 1) ^ 4 * (a + 2) ^ 6 * Q * L ^ 2 := by
      have hmul : 1 ≤ (n + 1) * (a + 2) * L :=
        Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) hL1
      calc (n + 1) ^ 3 * (a + 2) ^ 5 * Q * L
          = ((n + 1) ^ 3 * (a + 2) ^ 5 * Q * L) * 1 := by ring
        _ ≤ ((n + 1) ^ 3 * (a + 2) ^ 5 * Q * L) * ((n + 1) * (a + 2) * L) :=
            Nat.mul_le_mul_left _ hmul
        _ = (n + 1) ^ 4 * (a + 2) ^ 6 * Q * L ^ 2 := by ring
    exact le_trans hstep1 hstep2
  calc gSel ≤ 250 * V := hTotV
    _ ≤ 250 * ((n + 1) ^ 4 * (a + 2) ^ 6 * Q * L ^ 2) := Nat.mul_le_mul_left 250 hV_target
    _ = 250 * (n + 1) ^ 4 * (a + 2) ^ 6 * Q * L ^ 2 := by ring

lemma main_pos_q (n q ambiguity : ℕ) (hn : 0 < n) (ha : 0 < ambiguity) (hq : 0 < q) :
    let W := Fin n → Bool
    let Edge := Fin n × Fin q × Bool × Fin q
    let Pin := Edge ⊕ (Fin n ⊕ Fin n)
    let N := 2 + Fintype.card Pin
    let D := (Fin (n+1) ⊕ Fin (n+1)) ⊕ (Fin n ⊕ Fin 3)
    let encode := fun (x : W) => ∑ i : Fin n, (x i).toNat * 2^(n-1-i.val)
    let source := fun (enabled : Edge → Bool) (query idx : W) =>
      let input : Pin → Bool := Sum.elim enabled (Sum.elim query idx)
      [false,true] ++ List.ofFn (fun j : Fin (Fintype.card Pin) => input ((Fintype.equivFin Pin).symm j))
    ∃ (G : List PEqualNP.MetaComplexity.BinaryGate) (out : D → ℕ),
      G.length ≤ 250*(n+1)^4*(ambiguity+2)^6*(q+1)^(3*(ambiguity+1))*(Nat.clog 2 (q+2)+1)^2 ∧
      (∀ i : Fin G.length, (G.get i).left < N+i.val ∧ (G.get i).right < N+i.val) ∧
      (∀ o, out o < N+G.length) ∧
      ∀ (enabled : Edge → Bool) (query idx : W),
        let paths := fun (x : W) => Finset.univ.filter (fun p : Fin (n+1) → Fin q =>
          p 0 = p (Fin.last n) ∧ ∀ i : Fin n, enabled (i,p i.castSucc,x i,p i.succ) = true)
        let lang := Finset.univ.filter (fun x : W => (paths x).Nonempty)
        let rank := fun (x : W) => (lang.filter (fun y => encode y < encode x)).card
        let index := ∑ i : Fin n, (idx i).toNat * 2^i.val
        let circuit : PEqualNP.MetaComplexity.BinaryCircuit := ⟨G,0⟩
        let bit := fun o => (circuit.wires (source enabled query idx)).getD (out o) false
        let selected : W := fun i => bit (Sum.inr (Sum.inl i))
        let flag := fun (j : Fin 3) => bit (Sum.inr (Sum.inr j))
        (flag 0 = true ↔ ∀ x : W, (paths x).card ≤ ambiguity) ∧
        (flag 0 = true →
          (∀ i : Fin (n+1), bit (Sum.inl (Sum.inl i)) = lang.card.testBit i.val ∧
            bit (Sum.inl (Sum.inr i)) = (rank query).testBit i.val) ∧
          (flag 1 = true ↔ query ∈ lang) ∧ (flag 2 = true ↔ index < lang.card) ∧
          (index < lang.card → selected ∈ lang ∧ rank selected = index) ∧
          (lang.card ≤ index → ∀ i, selected i = false)) := by
  dsimp only
  set W := Fin n → Bool
  set Edge := Fin n × Fin q × Bool × Fin q
  set Pin := Edge ⊕ (Fin n ⊕ Fin n)
  set N := 2 + Fintype.card Pin
  set D := (Fin (n + 1) ⊕ Fin (n + 1)) ⊕ (Fin n ⊕ Fin 3)
  set B := widthB n q ambiguity
  have hN : 2 ≤ N := by omega
  let edgeW : Edge → ℕ := fun e => 2 + (Fintype.equivFin Pin (Sum.inl e)).val
  let queryW : Fin n → ℕ := fun i => 2 + (Fintype.equivFin Pin (Sum.inr (Sum.inl i))).val
  let idxW : Fin n → ℕ := fun i => 2 + (Fintype.equivFin Pin (Sum.inr (Sum.inr i))).val
  let indexReg : Fin (n + 1) → ℕ := fun i => if h : i.val < n then idxW ⟨i.val, h⟩ else 0
  have hedgeW : ∀ e, edgeW e < N := fun e => by
    simp only [edgeW, N]; have := (Fintype.equivFin Pin (Sum.inl e)).isLt; omega
  have hqueryW : RegOK N [] queryW := fun i => by
    simp only [queryW, N, List.length_nil]; have := (Fintype.equivFin Pin (Sum.inr (Sum.inl i))).isLt; omega
  have hidxReg : RegOK N [] indexReg := fun i => by
    simp only [indexReg, List.length_nil]
    by_cases hi : i.val < n
    · simp only [hi, dite_true, idxW, N]
      have := (Fintype.equivFin Pin (Sum.inr (Sum.inr ⟨i.val, hi⟩))).isLt
      omega
    · simp only [hi, dite_false]; omega
  have hWF0 : WF N [] := fun i => Fin.elim0 i
  let rCap := evalCapCheck N ambiguity edgeW []
  have hCap := evalCapCheck_spec (a := ambiguity) hN hn hq edgeW [] hWF0 hedgeW
  let allM : Fin n → Bool → ℕ := fun _ _ => 1
  have hallM : ∀ i b, allM i b < N + rCap.1.length := fun _ _ => by simp only [allM]; omega
  let rCard := countMask N ambiguity edgeW allM rCap.1
  have hCard := countMask_spec (a := ambiguity) hN hn hq edgeW allM rCap.1 hCap.2.2.1 hedgeW hallM
  have hqW_card : RegOK N rCard.1 queryW := regOK_extends (extends_trans hCap.1 hCard.1) hqueryW
  let rNQ := notVec N rCard.1 queryW
  have hNQ := notVec_spec hN hCard.2.2.1 hqW_card
  have hqW_nq : RegOK N rNQ.1 queryW := regOK_extends hNQ.1 hqW_card
  have hexM_ok : ∀ i b, exactMaskW queryW rNQ.2 i b < N + rNQ.1.length := fun i b => by
    cases b
    · exact hNQ.2.2.2.1 i
    · exact hqW_nq i
  let rQ1 := evalS (B := B) N edgeW (exactMaskW queryW rNQ.2) rNQ.1 1
  have hQ1 := evalS_spec (B := B) hN hn hq edgeW (exactMaskW queryW rNQ.2) rNQ.1 1 hNQ.2.2.1 hedgeW hexM_ok
  let rF1 := regNz N rQ1.1 rQ1.2
  have hF1 := regNz_spec hN hQ1.2.2.1 hQ1.2.2.2.1
  have he_nq_f1 : Extends rNQ.1 rF1.1 := extends_trans hQ1.1 hF1.1
  have hqW_f1 : RegOK N rF1.1 queryW := regOK_extends he_nq_f1 hqW_nq
  have hnqW_f1 : RegOK N rF1.1 rNQ.2 := regOK_extends he_nq_f1 hNQ.2.2.2.1
  let rRank := buildRank N ambiguity edgeW queryW rNQ.2 rF1.1 n le_rfl
  have hRank := buildRank_spec (a := ambiguity) hN hn hq edgeW queryW rNQ.2 rF1.1 hF1.2.2.1 hedgeW hqW_f1 hnqW_f1 n le_rfl
  have he0_rank : Extends [] rRank.1 :=
    extends_trans hCap.1 (extends_trans hCard.1 (extends_trans hNQ.1 (extends_trans he_nq_f1 hRank.1)))
  have hidx_rank : RegOK N rRank.1 indexReg := regOK_extends he0_rank hidxReg
  let rUnr := buildUnrank N ambiguity edgeW indexReg rRank.1 n le_rfl
  have hUnr := buildUnrank_spec (a := ambiguity) hN hn hq edgeW indexReg rRank.1 hRank.2.2.1 hedgeW hidx_rank n le_rfl
  have he_card_unr : Extends rCard.1 rUnr.1 :=
    extends_trans hNQ.1 (extends_trans he_nq_f1 (extends_trans hRank.1 hUnr.1))
  have hidx_unr : RegOK N rUnr.1 indexReg := regOK_extends hUnr.1 hidx_rank
  have hcard_unr : RegOK N rUnr.1 rCard.2 := regOK_extends he_card_unr hCard.2.2.2.1
  let rF2 := regSub N rUnr.1 indexReg rCard.2
  have hF2 := regSub_spec hN hUnr.2.2.1 hidx_unr hcard_unr
  have hsel_f2 : RegOK N rF2.1 rUnr.2.1 := regOK_extends hF2.1 hUnr.2.2.2.1
  let rSel := regGate N rF2.1 rF2.2.2 rUnr.2.1
  have hSel := regGate_spec hF2.2.2.1 hF2.2.2.2.2.1 hsel_f2
  let G := rSel.1
  let out : D → ℕ := fun o =>
    match o with
    | Sum.inl (Sum.inl i) => rCard.2 i
    | Sum.inl (Sum.inr i) => rRank.2 i
    | Sum.inr (Sum.inl i) => rSel.2 i
    | Sum.inr (Sum.inr j) =>
      if j.val = 0 then rCap.2
      else if j.val = 1 then rF1.2
      else rF2.2.2
  have he_f2_G : Extends rF2.1 G := hSel.1
  have he_unr_G : Extends rUnr.1 G := extends_trans hF2.1 he_f2_G
  have he_rank_G : Extends rRank.1 G := extends_trans hUnr.1 he_unr_G
  have he_f1_G : Extends rF1.1 G := extends_trans hRank.1 he_rank_G
  have he_card_G : Extends rCard.1 G := extends_trans he_card_unr he_unr_G
  have he_cap_G : Extends rCap.1 G := extends_trans hCard.1 he_card_G
  refine ⟨G, out, ?_, hSel.2.2.1, ?_, ?_⟩
  · have hCapLen : rCap.1.length ≤
        41 * (n + 1) * (ambiguity + 2) ^ 3 * widthB n q ambiguity * (q + 1) ^ (3 * (ambiguity + 1)) := by
      have h1 := hCap.2.1
      simp only [List.length_nil, Nat.zero_add] at h1
      exact le_trans h1 (capCost_le n q ambiguity hq)
    have hCardLen : rCard.1.length ≤ rCap.1.length + cmCost n q ambiguity := by
      have h1 := hCard.2.1
      rw [add5_assoc] at h1
      exact h1
    exact total_gates_bound n q ambiguity rCap.1.length rCard.1.length rNQ.1.length rQ1.1.length
      rF1.1.length rRank.1.length rUnr.1.length rF2.1.length G.length hq
      hCapLen hCardLen hNQ.2.1 hQ1.2.1 hF1.2.1 hRank.2.1 hUnr.2.1 hF2.2.1 hSel.2.1
  · intro o
    rcases o with (i | i) | (i | j)
    · exact regOK_extends he_card_G hCard.2.2.2.1 i
    · exact regOK_extends he_rank_G hRank.2.2.2.1 i
    · exact hSel.2.2.2.1 i
    · simp only [out]
      split
      · exact wire_lt_extends he_cap_G hCap.2.2.2.1
      · split
        · exact wire_lt_extends he_f1_G hF1.2.2.2.1
        · exact wire_lt_extends he_f2_G hF2.2.2.2.2.1
  · intro enabled query idx
    set input : Pin → Bool := Sum.elim enabled (Sum.elim query idx)
    set src := [false, true] ++ List.ofFn (fun j : Fin (Fintype.card Pin) => input ((Fintype.equivFin Pin).symm j))
    have hbase : HasBase src N := by
      refine ⟨by simp [src, N]; omega, by simp [src], by simp [src]⟩
    have hpin_eval : ∀ (G0 : List BGate) (p : Pin),
        evalW G0 src (2 + (Fintype.equivFin Pin p).val) = input p := by
      intro G0 p
      have hlt : 2 + (Fintype.equivFin Pin p).val < src.length := by
        simp only [src, List.length_append, List.length_cons, List.length_nil, List.length_ofFn]
        exact Nat.add_lt_add_left (Fintype.equivFin Pin p).isLt 2
      rw [evalW, runW_getD_lt G0 src _ hlt]
      simp only [src]
      rw [getD_append_right [false, true] _ _ false (by simp)]
      simp only [List.length_cons, List.length_nil, Nat.add_sub_cancel_left]
      simp [List.getD, Equiv.symm_apply_apply]
    have hed0 : ∀ e, evalW [] src (edgeW e) = enabled e := fun e => hpin_eval [] (Sum.inl e)
    have hq0 : ∀ i, evalW [] src (queryW i) = query i := fun i => hpin_eval [] (Sum.inr (Sum.inl i))
    have hidx0 : ∀ i, evalW [] src (idxW i) = idx i := fun i => hpin_eval [] (Sum.inr (Sum.inr i))
    have hidx_val : regVal [] src indexReg = ∑ i : Fin n, (idx i).toNat * 2 ^ i.val := by
      unfold regVal
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, Fin.isLt, dite_true, lt_irrefl, dite_false, indexReg]
      rw [evalW_zero hbase]
      simp only [Bool.toNat_false, zero_mul, Nat.add_zero]
      apply Finset.sum_congr rfl
      intro i _
      rw [hidx0 i]
    have hf0 : evalW G src (out (Sum.inr (Sum.inr 0))) = true ↔
        ∀ x : W, (closedPaths enabled x).card ≤ ambiguity := by
      simp only [out, Fin.val_zero, ite_true]
      rw [evalW_extends he_cap_G (by rw [hbase.1]; exact hCap.2.2.2.1)]
      exact hCap.2.2.2.2 src enabled hbase hed0
    refine ⟨hf0, ?_⟩
    intro hf0_true
    have hcap : ∀ x : W, (closedPaths enabled x).card ≤ ambiguity := hf0.mp hf0_true
    have hed_cap : ∀ e, evalW rCap.1 src (edgeW e) = enabled e := fun e => hpin_eval rCap.1 (Sum.inl e)
    have hcard_val : regVal rCard.1 src rCard.2 = (langSet enabled).card := by
      have h := hCard.2.2.2.2 src enabled (fun _ _ => true) hbase hed_cap
        (fun _ _ => evalW_one hbase) hcap
      have hmw : maskWords (fun (_ : Fin n) (_ : Bool) => true) = Finset.univ := by
        ext x; simp [maskWords]
      rw [hmw] at h
      exact h
    have hcard_G : regVal G src rCard.2 = (langSet enabled).card := by
      rw [regVal_extends he_card_G hbase.1 hCard.2.2.2.1, hcard_val]
    have hq_nq : ∀ i, evalW rNQ.1 src (queryW i) = query i := fun i => hpin_eval rNQ.1 (Sum.inr (Sum.inl i))
    have hnq_nq : ∀ i, evalW rNQ.1 src (rNQ.2 i) = !query i := fun i => by
      rw [hNQ.2.2.2.2 src hbase.1 i, hpin_eval rCard.1 (Sum.inr (Sum.inl i))]; rfl
    have hed_nq : ∀ e, evalW rNQ.1 src (edgeW e) = enabled e := fun e => hpin_eval rNQ.1 (Sum.inl e)
    have hrQ1_val : regVal rQ1.1 src rQ1.2 = (closedPaths enabled query).card := by
      have h := hQ1.2.2.2.2 src enabled (exactMask query) hbase hed_nq
        (fun i b => by cases b <;> simp [exactMaskW, exactMask, hq_nq i, hnq_nq i])
        (pow_lt_widthB n q ambiguity 1 (by omega))
      rw [maskWords_exact, Finset.sum_singleton, pow_one] at h
      exact h
    have hf1_iff : evalW G src (out (Sum.inr (Sum.inr 1))) = true ↔ query ∈ langSet enabled := by
      have hout1 : out (Sum.inr (Sum.inr 1)) = rF1.2 := rfl
      rw [hout1, evalW_extends he_f1_G (by rw [hbase.1]; exact hF1.2.2.2.1)]
      rw [hF1.2.2.2.2 src hbase, hrQ1_val]
      simp only [langSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.nonempty_iff_ne_empty,
        ne_eq, Finset.card_eq_zero]
    have hed_f1 : ∀ e, evalW rF1.1 src (edgeW e) = enabled e := fun e => hpin_eval rF1.1 (Sum.inl e)
    have hq_f1 : ∀ i, evalW rF1.1 src (queryW i) = query i := fun i => hpin_eval rF1.1 (Sum.inr (Sum.inl i))
    have hnq_f1 : ∀ i, evalW rF1.1 src (rNQ.2 i) = !query i := fun i => by
      rw [evalW_extends he_nq_f1 (by rw [hbase.1]; exact hNQ.2.2.2.1 i), hnq_nq i]
    have hrank_G : regVal G src rRank.2 = rankOf enabled query := by
      rw [regVal_extends he_rank_G hbase.1 hRank.2.2.2.1]
      rw [hRank.2.2.2.2 src enabled query hbase hed_f1 hq_f1 hnq_f1 hcap, prefBefore_n]
    have hf2_iff : evalW G src (out (Sum.inr (Sum.inr 2))) = true ↔
        (∑ i : Fin n, (idx i).toNat * 2 ^ i.val) < (langSet enabled).card := by
      have h2ne0 : ((2 : Fin 3).val) ≠ 0 := by decide
      have h2ne1 : ((2 : Fin 3).val) ≠ 1 := by decide
      simp only [out, h2ne0, h2ne1, ite_false]
      rw [evalW_extends he_f2_G (by rw [hbase.1]; exact hF2.2.2.2.2.1)]
      rw [regSub_borrow_iff hN hUnr.2.2.1 hidx_unr hcard_unr hbase]
      rw [regVal_extends (extends_trans he0_rank hUnr.1) hbase.1 hidxReg, hidx_val]
      rw [regVal_extends he_card_unr hbase.1 hCard.2.2.2.1, hcard_val]
    have hed_rank : ∀ e, evalW rRank.1 src (edgeW e) = enabled e := fun e => hpin_eval rRank.1 (Sum.inl e)
    have hunr_ev := hUnr.2.2.2.2.2.2 src enabled hbase hed_rank hcap
    have hidx_rank_val : regVal rRank.1 src indexReg = ∑ i : Fin n, (idx i).toNat * 2 ^ i.val := by
      rw [regVal_extends he0_rank hbase.1 hidxReg, hidx_val]
    refine ⟨?_, hf1_iff, hf2_iff, ?_, ?_⟩
    · intro i
      constructor
      · change evalW G src (rCard.2 i) = (langSet enabled).card.testBit i.val
        rw [← hcard_G, regVal_testBit_fin]
      · change evalW G src (rRank.2 i) = (rankOf enabled query).testBit i.val
        rw [← hrank_G, regVal_testBit_fin]
    · intro hlt
      have hinv := hunr_ev.2 (by rw [hidx_rank_val]; exact hlt)
      set p : W := fun i => evalW rUnr.1 src (rUnr.2.1 i)
      have hcard_p : (prefSet enabled p n).card = if p ∈ langSet enabled then 1 else 0 :=
        prefSet_n_card enabled p
      have hp_mem : p ∈ langSet enabled := by
        by_contra hnot
        have h0 : (prefSet enabled p n).card = 0 := by rw [hcard_p]; simp [hnot]
        have := hinv.1
        omega
      have hrem0 : regVal rUnr.1 src rUnr.2.2.2 = 0 := by
        have h1 : (prefSet enabled p n).card = 1 := by rw [hcard_p]; simp [hp_mem]
        have hlt1 : regVal rUnr.1 src rUnr.2.2.2 < 1 := lt_of_lt_of_eq hinv.1 h1
        exact Nat.lt_one_iff.mp hlt1
      have hrank_p : rankOf enabled p = ∑ i : Fin n, (idx i).toNat * 2 ^ i.val := by
        have h2 := hinv.2
        rw [hrem0, Nat.add_zero, prefBefore_n, hidx_rank_val] at h2
        exact h2
      have hsel_eq_p : (fun i => evalW G src (out (Sum.inr (Sum.inl i)))) = p := by
        funext i
        have hval := hSel.2.2.2.2 src hbase.1
        have hf2_t : evalW rF2.1 src rF2.2.2 = true := by
          have := hf2_iff.mpr hlt
          have hout2 : out (Sum.inr (Sum.inr 2)) = rF2.2.2 := rfl
          rw [hout2, evalW_extends he_f2_G (by rw [hbase.1]; exact hF2.2.2.2.2.1)] at this
          exact this
        rw [hf2_t] at hval
        simp only [ite_true] at hval
        have hbit_eq := (regVal_eq_iff G src rSel.2 rUnr.2.1).mp (by
          rw [regVal_extends he_f2_G hbase.1 hsel_f2]; exact hval) i
        simp only [out, p]
        rw [hbit_eq, evalW_extends he_unr_G (by rw [hbase.1]; exact hUnr.2.2.2.1 i)]
      change (fun i => evalW G src (out (Sum.inr (Sum.inl i)))) ∈ langSet enabled ∧
        rankOf enabled (fun i => evalW G src (out (Sum.inr (Sum.inl i)))) = ∑ i : Fin n, (idx i).toNat * 2 ^ i.val
      rw [hsel_eq_p]
      exact ⟨hp_mem, hrank_p⟩
    · intro hle i
      have hf2_f : evalW rF2.1 src rF2.2.2 = false := by
        cases hf : evalW rF2.1 src rF2.2.2
        · rfl
        · have hout2 : out (Sum.inr (Sum.inr 2)) = rF2.2.2 := rfl
          have ht : evalW G src (out (Sum.inr (Sum.inr 2))) = true := by
            rw [hout2, evalW_extends he_f2_G (by rw [hbase.1]; exact hF2.2.2.2.2.1), hf]
          have hlt' := hf2_iff.mp ht
          exact absurd hlt' (Nat.not_lt.mpr hle)
      have hval := hSel.2.2.2.2 src hbase.1
      rw [hf2_f] at hval
      simp only [Bool.false_eq_true, ite_false] at hval
      change evalW G src (rSel.2 i) = false
      rw [← regVal_testBit_fin, hval, Nat.zero_testBit]

end PEqualNP.Outside.L_pcx_329

theorem PEqualNP.Outside.L_pcx_329 : ∃ c : ℕ, 0 < c ∧ ∀ (n q ambiguity : ℕ), 0 < n → 0 < ambiguity →
  let W := Fin n → Bool
  let Edge := Fin n × Fin q × Bool × Fin q
  let Pin := Edge ⊕ (Fin n ⊕ Fin n)
  let N := 2 + Fintype.card Pin
  let D := (Fin (n+1) ⊕ Fin (n+1)) ⊕ (Fin n ⊕ Fin 3)
  let encode := fun (x : W) => ∑ i : Fin n, (x i).toNat * 2^(n-1-i.val)
  let source := fun (enabled : Edge → Bool) (query idx : W) =>
    let input : Pin → Bool := Sum.elim enabled (Sum.elim query idx)
    [false,true] ++ List.ofFn (fun j : Fin (Fintype.card Pin) => input ((Fintype.equivFin Pin).symm j))
  ∃ (G : List PEqualNP.MetaComplexity.BinaryGate) (out : D → ℕ),
    G.length ≤ c*(n+1)^4*(ambiguity+2)^6*(q+1)^(3*(ambiguity+1))*(Nat.clog 2 (q+2)+1)^2 ∧
    (∀ i : Fin G.length, (G.get i).left < N+i.val ∧ (G.get i).right < N+i.val) ∧
    (∀ o, out o < N+G.length) ∧
    ∀ (enabled : Edge → Bool) (query idx : W),
      let paths := fun (x : W) => Finset.univ.filter (fun p : Fin (n+1) → Fin q =>
        p 0 = p (Fin.last n) ∧ ∀ i : Fin n, enabled (i,p i.castSucc,x i,p i.succ) = true)
      let lang := Finset.univ.filter (fun x : W => (paths x).Nonempty)
      let rank := fun (x : W) => (lang.filter (fun y => encode y < encode x)).card
      let index := ∑ i : Fin n, (idx i).toNat * 2^i.val
      let circuit : PEqualNP.MetaComplexity.BinaryCircuit := ⟨G,0⟩
      let bit := fun o => (circuit.wires (source enabled query idx)).getD (out o) false
      let selected : W := fun i => bit (Sum.inr (Sum.inl i))
      let flag := fun (j : Fin 3) => bit (Sum.inr (Sum.inr j))
      (flag 0 = true ↔ ∀ x : W, (paths x).card ≤ ambiguity) ∧
      (flag 0 = true →
        (∀ i : Fin (n+1), bit (Sum.inl (Sum.inl i)) = lang.card.testBit i.val ∧
          bit (Sum.inl (Sum.inr i)) = (rank query).testBit i.val) ∧
        (flag 1 = true ↔ query ∈ lang) ∧ (flag 2 = true ↔ index < lang.card) ∧
        (index < lang.card → selected ∈ lang ∧ rank selected = index) ∧
        (lang.card ≤ index → ∀ i, selected i = false)) := by
  refine ⟨250, by omega, ?_⟩
  intro n q ambiguity hn ha
  cases q with
  | zero =>
    dsimp only
    let D := (Fin (n + 1) ⊕ Fin (n + 1)) ⊕ (Fin n ⊕ Fin 3)
    let out : D → ℕ := fun o =>
      match o with
      | Sum.inr (Sum.inr j) => if j.val = 0 then 1 else 0
      | _ => 0
    refine ⟨[], out, by simp, fun i => Fin.elim0 i, ?_, ?_⟩
    · intro o
      rcases o with (i | i) | (i | j)
      · simp [out]
      · simp [out]
      · simp [out]
      · simp only [out]; split <;> omega
    · intro enabled query idx
      have hpaths : ∀ x : Fin n → Bool,
          (Finset.univ.filter (fun p : Fin (n + 1) → Fin 0 =>
            p 0 = p (Fin.last n) ∧ ∀ i : Fin n, enabled (i, p i.castSucc, x i, p i.succ) = true)) = ∅ := by
        intro x
        rw [Finset.eq_empty_iff_forall_notMem]
        intro p _
        exact Fin.elim0 (p 0)
      have hlang : (Finset.univ.filter (fun x : Fin n → Bool =>
          (Finset.univ.filter (fun p : Fin (n + 1) → Fin 0 =>
            p 0 = p (Fin.last n) ∧ ∀ i : Fin n, enabled (i, p i.castSucc, x i, p i.succ) = true)).Nonempty)) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro x hx
        have hne := (Finset.mem_filter.mp hx).2
        rw [hpaths x] at hne
        exact Finset.not_nonempty_empty hne
      have hbit0 : (PEqualNP.MetaComplexity.BinaryCircuit.wires ⟨[], 0⟩
          ([false, true] ++ List.ofFn (fun j : Fin (Fintype.card ((Fin n × Fin 0 × Bool × Fin 0) ⊕ (Fin n ⊕ Fin n))) =>
            Sum.elim enabled (Sum.elim query idx) ((Fintype.equivFin _).symm j)))).getD 0 false = false := by
        simp [PEqualNP.MetaComplexity.BinaryCircuit.wires]
      have hbit1 : (PEqualNP.MetaComplexity.BinaryCircuit.wires ⟨[], 0⟩
          ([false, true] ++ List.ofFn (fun j : Fin (Fintype.card ((Fin n × Fin 0 × Bool × Fin 0) ⊕ (Fin n ⊕ Fin n))) =>
            Sum.elim enabled (Sum.elim query idx) ((Fintype.equivFin _).symm j)))).getD 1 false = true := by
        simp [PEqualNP.MetaComplexity.BinaryCircuit.wires]
      refine ⟨?_, ?_⟩
      · simp only [out, Fin.val_zero, ite_true, hbit1, true_iff]
        intro x
        rw [hpaths x, Finset.card_empty]
        omega
      · intro _
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro i
          simp only [out, hbit0, hlang, Finset.card_empty, Finset.filter_empty, Nat.zero_testBit, and_self]
        · have h1ne0 : ((1 : Fin 3).val) ≠ 0 := by decide
          simp only [out, h1ne0, ite_false, hbit0, hlang, Finset.notMem_empty, Bool.false_eq_true]
        · have h2ne0 : ((2 : Fin 3).val) ≠ 0 := by decide
          simp only [out, h2ne0, ite_false, hbit0, hlang, Finset.card_empty, Nat.not_lt_zero, Bool.false_eq_true]
        · intro hlt
          rw [hlang, Finset.card_empty] at hlt
          omega
        · intro _ i
          simp only [out, hbit0]
  | succ q' =>
    exact PEqualNP.Outside.L_pcx_329.main_pos_q n (q' + 1) ambiguity hn ha (by omega)



