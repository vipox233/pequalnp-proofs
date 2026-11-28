import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_328

open PEqualNP.ProofComplexity

inductive Gate (V : Type) where
  | const (out : ℕ) (val : Bool)
  | not (inp : V ⊕ ℕ) (out : ℕ)
  | and (x y : V ⊕ ℕ) (out : ℕ)
  | or (x y : V ⊕ ℕ) (out : ℕ)
  | xor (x y : V ⊕ ℕ) (out : ℕ)

def Gate.out {V : Type} : Gate V → ℕ
  | .const o _ => o
  | .not _ o => o
  | .and _ _ o => o
  | .or _ _ o => o
  | .xor _ _ o => o

def Gate.inputs {V : Type} : Gate V → List (V ⊕ ℕ)
  | .const _ _ => []
  | .not i _ => [i]
  | .and x y _ => [x, y]
  | .or x y _ => [x, y]
  | .xor x y _ => [x, y]

def gateClauses {V : Type} [DecidableEq V] : Gate V → List (Clause (V ⊕ ℕ))
  | .const o val => [{(Sum.inr o, val)}]
  | .not i o => [{(i, true), (Sum.inr o, true)}, {(i, false), (Sum.inr o, false)}]
  | .and x y o =>
    [{(x, true), (Sum.inr o, false)},
     {(y, true), (Sum.inr o, false)},
     {(x, false), (y, false), (Sum.inr o, true)}]
  | .or x y o =>
    [{(x, false), (Sum.inr o, true)},
     {(y, false), (Sum.inr o, true)},
     {(x, true), (y, true), (Sum.inr o, false)}]
  | .xor x y o =>
    [{(x, true), (y, true), (Sum.inr o, false)},
     {(x, false), (y, false), (Sum.inr o, false)},
     {(x, true), (y, false), (Sum.inr o, true)},
     {(x, false), (y, true), (Sum.inr o, true)}]

def gateEval {V : Type} (val : V ⊕ ℕ → Bool) : Gate V → Bool
  | .const _ b => b
  | .not i _ => !(val i)
  | .and x y _ => val x && val y
  | .or x y _ => val x || val y
  | .xor x y _ => Bool.xor (val x) (val y)

lemma card_pair_le {α : Type*} [DecidableEq α] (a b : α) :
    ({a, b} : Finset α).card ≤ 2 :=
  le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ (by simp))

lemma card_triple_le {α : Type*} [DecidableEq α] (a b c : α) :
    ({a, b, c} : Finset α).card ≤ 3 :=
  le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ (card_pair_le b c))

lemma gateClauses_card_le_three {V : Type} [DecidableEq V] (g : Gate V) :
    ∀ c ∈ gateClauses g, c.card ≤ 3 := by
  cases g <;> simp only [gateClauses, List.mem_cons, List.not_mem_nil, or_false] <;>
    rintro c (rfl | rfl | rfl | rfl) <;>
    first
    | exact le_trans (Finset.card_singleton _).le (by omega)
    | exact le_trans (card_pair_le _ _) (by omega)
    | exact card_triple_le _ _ _

lemma gateClauses_length_le_four {V : Type} [DecidableEq V] (g : Gate V) :
    (gateClauses g).length ≤ 4 := by
  cases g <;> simp [gateClauses]

lemma gateClauses_in_gate {V : Type} [DecidableEq V] (g : Gate V) :
    ∀ cl ∈ gateClauses g, ∀ l ∈ cl, l.1 ∈ g.inputs ∨ l.1 = Sum.inr g.out := by
  cases g <;> simp only [gateClauses, Gate.inputs, Gate.out, List.mem_cons, List.not_mem_nil,
    List.mem_singleton, or_false]
  · rintro cl rfl l hl; simp at hl; subst hl; exact Or.inr rfl
  · rintro cl (rfl | rfl) l hl <;> simp at hl <;> rcases hl with rfl | rfl <;> simp
  · rintro cl (rfl | rfl | rfl) l hl <;> simp at hl <;> rcases hl with rfl | rfl | rfl <;> simp
  · rintro cl (rfl | rfl | rfl) l hl <;> simp at hl <;> rcases hl with rfl | rfl | rfl <;> simp
  · rintro cl (rfl | rfl | rfl | rfl) l hl <;> simp at hl <;> rcases hl with rfl | rfl | rfl <;> simp

lemma gateClauses_sat {V : Type} [DecidableEq V] (val : V ⊕ ℕ → Bool) (g : Gate V) :
    (∀ c ∈ gateClauses g, ClauseSat val c) ↔ val (Sum.inr g.out) = gateEval val g := by
  cases g with
  | const o b =>
    simp only [gateClauses, gateEval, Gate.out, ClauseSat, List.mem_singleton, forall_eq,
      Finset.mem_singleton, exists_eq_left]
  | not i o =>
    simp only [gateClauses, gateEval, Gate.out, ClauseSat, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, Finset.mem_insert, Finset.mem_singleton,
      exists_eq_or_imp, exists_eq_left]
    cases val i <;> cases val (Sum.inr o) <;> simp
  | and x y o =>
    simp only [gateClauses, gateEval, Gate.out, ClauseSat, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, Finset.mem_insert, Finset.mem_singleton,
      exists_eq_or_imp, exists_eq_left]
    cases val x <;> cases val y <;> cases val (Sum.inr o) <;> simp
  | or x y o =>
    simp only [gateClauses, gateEval, Gate.out, ClauseSat, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, Finset.mem_insert, Finset.mem_singleton,
      exists_eq_or_imp, exists_eq_left]
    cases val x <;> cases val y <;> cases val (Sum.inr o) <;> simp
  | xor x y o =>
    simp only [gateClauses, gateEval, Gate.out, ClauseSat, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, Finset.mem_insert, Finset.mem_singleton,
      exists_eq_or_imp, exists_eq_left]
    cases val x <;> cases val y <;> cases val (Sum.inr o) <;> simp

structure GEntry (V : Type) where
  gate : Gate V
  node : List Bool

structure CState (V : Type) where
  rev : List (GEntry V)
  len : ℕ

def CState.empty (V : Type) : CState V := ⟨[], 0⟩

def CState.emit {V : Type} (st : CState V) (p : List Bool) (mk : ℕ → Gate V) :
    CState V × (V ⊕ ℕ) :=
  (⟨⟨mk st.len, p⟩ :: st.rev, st.len + 1⟩, Sum.inr st.len)

def WellFormedRev {V : Type} : List (GEntry V) → Prop
  | [] => True
  | e :: rest =>
    e.gate.out = rest.length ∧
    (∀ m, Sum.inr m ∈ e.gate.inputs → m < rest.length) ∧
    WellFormedRev rest

lemma wellFormedRev_out_lt {V : Type} :
    ∀ {rev : List (GEntry V)}, WellFormedRev rev → ∀ e ∈ rev, e.gate.out < rev.length
  | [], _, _, h => by simp at h
  | e :: rest, ⟨ho, _, hr⟩, e', he => by
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · simp [ho]
    · exact Nat.lt_trans (wellFormedRev_out_lt hr e' he) (Nat.lt_succ_self _)

lemma wellFormedRev_in_lt {V : Type} :
    ∀ {rev : List (GEntry V)}, WellFormedRev rev →
      ∀ e ∈ rev, ∀ m, Sum.inr m ∈ e.gate.inputs → m < rev.length
  | [], _, _, h, _, _ => by simp at h
  | e :: rest, ⟨_, hin, hr⟩, e', he, m, hm => by
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · exact Nat.lt_trans (hin m hm) (Nat.lt_succ_self _)
    · exact Nat.lt_trans (wellFormedRev_in_lt hr e' he m hm) (Nat.lt_succ_self _)

lemma wellFormedRev_emit {V : Type} {st : CState V} (hw : WellFormedRev st.rev)
    (hlen : st.rev.length = st.len) (p : List Bool) (mk : ℕ → Gate V)
    (hout : (mk st.len).out = st.len)
    (hin : ∀ m, Sum.inr m ∈ (mk st.len).inputs → m < st.len) :
    WellFormedRev (st.emit p mk).1.rev ∧ (st.emit p mk).1.rev.length = (st.emit p mk).1.len := by
  refine ⟨⟨?_, ?_, hw⟩, ?_⟩
  · simpa [CState.emit, hlen] using hout
  · intro m hm
    simpa [CState.emit, hlen] using hin m hm
  · simp [CState.emit, hlen]

def evalRev {V : Type} (x : V → Bool) : List (GEntry V) → ℕ → Bool
  | [], _ => false
  | e :: rest, k =>
    let prev := evalRev x rest
    if k = e.gate.out then gateEval (Sum.elim x prev) e.gate else prev k

lemma evalRev_lt_eq {V : Type} (x : V → Bool) (e : GEntry V) (rest : List (GEntry V))
    (hw : WellFormedRev (e :: rest)) {k : ℕ} (hk : k < rest.length) :
    evalRev x (e :: rest) k = evalRev x rest k := by
  rcases hw with ⟨ho, _, _⟩
  have hne : k ≠ e.gate.out := by omega
  simp [evalRev, hne]

lemma gateEval_congr {V : Type} {v1 v2 : V ⊕ ℕ → Bool} {g : Gate V}
    (h : ∀ z ∈ g.inputs, v1 z = v2 z) : gateEval v1 g = gateEval v2 g := by
  cases g <;> simp only [Gate.inputs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at h <;> simp [gateEval, h]

lemma evalRev_sat {V : Type} [DecidableEq V] (x : V → Bool) :
    ∀ {rev : List (GEntry V)}, WellFormedRev rev →
      ∀ e ∈ rev, ∀ c ∈ gateClauses e.gate, ClauseSat (Sum.elim x (evalRev x rev)) c
  | [], _, _, h => by simp at h
  | e :: rest, hw, e', he => by
    rcases hw with ⟨ho, hin, hr⟩
    have hcongr : ∀ z ∈ e.gate.inputs,
        Sum.elim x (evalRev x (e :: rest)) z = Sum.elim x (evalRev x rest) z := by
      rintro (v | m) hm
      · rfl
      · exact evalRev_lt_eq x e rest ⟨ho, hin, hr⟩ (hin m hm)
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · rw [gateClauses_sat]
      simp only [Sum.elim_inr, evalRev, ite_true]
      exact (gateEval_congr hcongr).symm
    · have hlt : e'.gate.out < rest.length := wellFormedRev_out_lt hr e' he
      have hsat := evalRev_sat x hr e' he
      rw [gateClauses_sat] at hsat ⊢
      have hcongr' : ∀ z ∈ e'.gate.inputs,
          Sum.elim x (evalRev x (e :: rest)) z = Sum.elim x (evalRev x rest) z := by
        rintro (v | m) hm
        · rfl
        · exact evalRev_lt_eq x e rest ⟨ho, hin, hr⟩ (wellFormedRev_in_lt hr e' he m hm)
      simp only [Sum.elim_inr] at hsat ⊢
      rw [evalRev_lt_eq x e rest ⟨ho, hin, hr⟩ hlt, gateEval_congr hcongr']
      exact hsat

lemma evalRev_unique {V : Type} [DecidableEq V] (x : V → Bool) (y : ℕ → Bool) :
    ∀ {rev : List (GEntry V)}, WellFormedRev rev →
      (∀ e ∈ rev, ∀ c ∈ gateClauses e.gate, ClauseSat (Sum.elim x y) c) →
      ∀ k < rev.length, y k = evalRev x rev k
  | [], _, _, k, hk => by simp at hk
  | e :: rest, ⟨ho, hin, hr⟩, hsat, k, hk => by
    have hrest : ∀ k < rest.length, y k = evalRev x rest k :=
      evalRev_unique x y hr (fun e' he' => hsat e' (List.mem_cons_of_mem _ he'))
    have hy_e := (gateClauses_sat (Sum.elim x y) e.gate).mp (hsat e List.mem_cons_self)
    simp only [Sum.elim_inr] at hy_e
    have hcongr : ∀ z ∈ e.gate.inputs, Sum.elim x y z = Sum.elim x (evalRev x rest) z := by
      rintro (v | m) hm
      · rfl
      · exact hrest m (hin m hm)
    rw [List.length_cons] at hk
    by_cases hke : k = e.gate.out
    · subst hke
      simp only [evalRev, ite_true]
      rw [hy_e, gateEval_congr hcongr]
    · have hk' : k < rest.length := by omega
      simp [evalRev, hke, hrest k hk']

def emitConst {V : Type} (st : CState V) (p : List Bool) (b : Bool) : CState V × (V ⊕ ℕ) :=
  st.emit p (fun o => .const o b)

def emitNot {V : Type} (st : CState V) (p : List Bool) (i : V ⊕ ℕ) : CState V × (V ⊕ ℕ) :=
  st.emit p (fun o => .not i o)

def emitAnd {V : Type} (st : CState V) (p : List Bool) (x y : V ⊕ ℕ) : CState V × (V ⊕ ℕ) :=
  st.emit p (fun o => .and x y o)

def emitOr {V : Type} (st : CState V) (p : List Bool) (x y : V ⊕ ℕ) : CState V × (V ⊕ ℕ) :=
  st.emit p (fun o => .or x y o)

def emitXor {V : Type} (st : CState V) (p : List Bool) (x y : V ⊕ ℕ) : CState V × (V ⊕ ℕ) :=
  st.emit p (fun o => .xor x y o)

def emitHalfAdder {V : Type} (st : CState V) (p : List Bool) (x y : V ⊕ ℕ) :
    CState V × (V ⊕ ℕ) × (V ⊕ ℕ) :=
  let (st1, s) := emitXor st p x y
  let (st2, c) := emitAnd st1 p x y
  (st2, s, c)

def emitFullAdder {V : Type} (st : CState V) (p : List Bool) (x y cin : V ⊕ ℕ) :
    CState V × (V ⊕ ℕ) × (V ⊕ ℕ) :=
  let (st1, t) := emitXor st p x y
  let (st2, s) := emitXor st1 p t cin
  let (st3, a1) := emitAnd st2 p x y
  let (st4, a2) := emitAnd st3 p t cin
  let (st5, cout) := emitOr st4 p a1 a2
  (st5, s, cout)

def compressCol {V : Type} (st : CState V) (p : List Bool) :
    List (V ⊕ ℕ) → List (V ⊕ ℕ) → CState V × Option (V ⊕ ℕ) × List (V ⊕ ℕ)
  | [], carries => (st, none, carries)
  | [a], carries => (st, some a, carries)
  | [a, b], carries =>
    let (st1, s, c) := emitHalfAdder st p a b
    (st1, some s, c :: carries)
  | a :: b :: c :: rest, carries =>
    let (st1, s, cout) := emitFullAdder st p a b c
    compressCol st1 p (s :: rest) (cout :: carries)
termination_by l _ => l.length

def compressAll {V : Type} (st : CState V) (p : List Bool) :
    List (List (V ⊕ ℕ)) → CState V × List (Option (V ⊕ ℕ))
  | [] => (st, [])
  | col :: rest =>
    let (st1, s?, carries) := compressCol st p col []
    let rest' := match rest with
      | [] => []
      | next :: tail => (carries ++ next) :: tail
    let (st2, outs) := compressAll st1 p rest'
    (st2, s? :: outs)
termination_by l => l.length
decreasing_by
  cases rest <;> simp

def WireValid {V : Type} (n : ℕ) : V ⊕ ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr m => m < n

def CInv {V : Type} (st : CState V) : Prop :=
  WellFormedRev st.rev ∧ st.rev.length = st.len

lemma cinv_empty (V : Type) : CInv (CState.empty V) := ⟨trivial, rfl⟩

lemma cinv_emit {V : Type} {st : CState V} (h : CInv st) (p : List Bool) (mk : ℕ → Gate V)
    (hout : (mk st.len).out = st.len)
    (hin : ∀ m, Sum.inr m ∈ (mk st.len).inputs → m < st.len) :
    CInv (st.emit p mk).1 ∧ WireValid (st.emit p mk).1.len (st.emit p mk).2 ∧
    st.len ≤ (st.emit p mk).1.len := by
  have h1 := wellFormedRev_emit h.1 h.2 p mk hout hin
  refine ⟨h1, ?_, ?_⟩
  · simp [CState.emit, WireValid]
  · simp [CState.emit]

lemma wireValid_mono {V : Type} {m n : ℕ} (hmn : m ≤ n) :
    ∀ {w : V ⊕ ℕ}, WireValid m w → WireValid n w
  | Sum.inl _, _ => trivial
  | Sum.inr _, h => lt_of_lt_of_le h hmn

def bitVal {V : Type} (val : V ⊕ ℕ → Bool) (w : V ⊕ ℕ) : ℕ :=
  (val w).toNat

def optBitVal {V : Type} (val : V ⊕ ℕ → Bool) : Option (V ⊕ ℕ) → ℕ
  | none => 0
  | some w => bitVal val w

def sumBits {V : Type} (val : V ⊕ ℕ → Bool) (ws : List (V ⊕ ℕ)) : ℕ :=
  (ws.map (bitVal val)).sum

def sumCols {V : Type} (val : V ⊕ ℕ → Bool) : List (List (V ⊕ ℕ)) → ℕ
  | [] => 0
  | col :: rest => sumBits val col + 2 * sumCols val rest

def sumOptBits {V : Type} (val : V ⊕ ℕ → Bool) : List (Option (V ⊕ ℕ)) → ℕ
  | [] => 0
  | o :: rest => optBitVal val o + 2 * sumOptBits val rest

lemma sumBits_append {V : Type} (val : V ⊕ ℕ → Bool) (xs ys : List (V ⊕ ℕ)) :
    sumBits val (xs ++ ys) = sumBits val xs + sumBits val ys := by
  simp [sumBits, List.map_append, List.sum_append]

lemma evalRev_emit_old {V : Type} (x : V → Bool) {st : CState V} (h : CInv st)
    (p : List Bool) (mk : ℕ → Gate V) (hout : (mk st.len).out = st.len)
    {w : V ⊕ ℕ} (hw : WireValid st.len w) :
    Sum.elim x (evalRev x (st.emit p mk).1.rev) w = Sum.elim x (evalRev x st.rev) w := by
  cases w with
  | inl _ => rfl
  | inr m =>
    have hlen := h.2
    have hlt : m < st.rev.length := by simpa [hlen, WireValid] using hw
    have hne : m ≠ (mk st.len).out := by omega
    simp [CState.emit, evalRev, hne]

lemma evalRev_emit_new {V : Type} (x : V → Bool) {st : CState V} (h : CInv st)
    (p : List Bool) (mk : ℕ → Gate V) (hout : (mk st.len).out = st.len) :
    Sum.elim x (evalRev x (st.emit p mk).1.rev) (st.emit p mk).2 =
      gateEval (Sum.elim x (evalRev x st.rev)) (mk st.len) := by
  simp [CState.emit, evalRev, hout]

def NodesIn {V : Type} (st0 st1 : CState V) (p : List Bool) : Prop :=
  ∃ suf : List (GEntry V), st1.rev = suf ++ st0.rev ∧ ∀ e ∈ suf, e.node = p

lemma nodesIn_refl {V : Type} (st : CState V) (p : List Bool) : NodesIn st st p :=
  ⟨[], rfl, fun _ h => by simp at h⟩

lemma nodesIn_trans {V : Type} {st0 st1 st2 : CState V} {p : List Bool}
    (h1 : NodesIn st0 st1 p) (h2 : NodesIn st1 st2 p) : NodesIn st0 st2 p := by
  rcases h1 with ⟨s1, hs1, hp1⟩
  rcases h2 with ⟨s2, hs2, hp2⟩
  refine ⟨s2 ++ s1, ?_, ?_⟩
  · rw [hs2, hs1, List.append_assoc]
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact hp2 e he
    · exact hp1 e he

lemma nodesIn_emit {V : Type} (st : CState V) (p : List Bool) (mk : ℕ → Gate V) :
    NodesIn st (st.emit p mk).1 p :=
  ⟨[⟨mk st.len, p⟩], rfl, fun e he => by simp only [List.mem_singleton] at he; rw [he]⟩

lemma evalRev_suffix {V : Type} (x : V → Bool) :
    ∀ (suf rev : List (GEntry V)), WellFormedRev (suf ++ rev) →
      ∀ {w : V ⊕ ℕ}, WireValid rev.length w →
        Sum.elim x (evalRev x (suf ++ rev)) w = Sum.elim x (evalRev x rev) w
  | [], rev, _, w, _ => rfl
  | e :: suf, rev, hw, w, hwv => by
    have h1 := evalRev_suffix x suf rev hw.2.2 hwv
    rcases w with v | m
    · rfl
    · have hm : m < (suf ++ rev).length := by
        simp only [WireValid] at hwv
        simp only [List.length_append]
        omega
      have hlt := evalRev_lt_eq x e (suf ++ rev) hw hm
      simpa [Sum.elim_inr] using hlt.trans h1

lemma evalRev_nodesIn {V : Type} (x : V → Bool) {st0 st1 : CState V} {p : List Bool}
    (hc : CInv st1) (h0 : CInv st0) (hn : NodesIn st0 st1 p)
    {w : V ⊕ ℕ} (hw : WireValid st0.len w) :
    Sum.elim x (evalRev x st1.rev) w = Sum.elim x (evalRev x st0.rev) w := by
  rcases hn with ⟨suf, hsuf, _⟩
  have hwf : WellFormedRev (suf ++ st0.rev) := hsuf ▸ hc.1
  have hw' : WireValid st0.rev.length w := h0.2.symm ▸ hw
  simpa [hsuf] using evalRev_suffix x suf st0.rev hwf hw'

lemma sumBits_nodesIn {V : Type} (x : V → Bool) {st0 st1 : CState V} {p : List Bool}
    (hc : CInv st1) (h0 : CInv st0) (hn : NodesIn st0 st1 p)
    {ws : List (V ⊕ ℕ)} (hw : ∀ w ∈ ws, WireValid st0.len w) :
    sumBits (Sum.elim x (evalRev x st1.rev)) ws = sumBits (Sum.elim x (evalRev x st0.rev)) ws := by
  simp only [sumBits]
  congr 1
  exact List.map_congr_left (fun w hmem => by
    simp only [bitVal]; rw [evalRev_nodesIn x hc h0 hn (hw w hmem)])

lemma sumOptBits_nodesIn {V : Type} (x : V → Bool) {st0 st1 : CState V} {p : List Bool}
    (hc : CInv st1) (h0 : CInv st0) (hn : NodesIn st0 st1 p) :
    ∀ {xs : List (Option (V ⊕ ℕ))}, (∀ o ∈ xs, ∀ w, o = some w → WireValid st0.len w) →
      sumOptBits (Sum.elim x (evalRev x st1.rev)) xs =
        sumOptBits (Sum.elim x (evalRev x st0.rev)) xs
  | [], _ => rfl
  | o :: rest, hxs => by
    simp only [sumOptBits]
    have ho : optBitVal (Sum.elim x (evalRev x st1.rev)) o =
        optBitVal (Sum.elim x (evalRev x st0.rev)) o := by
      cases o with
      | none => rfl
      | some w => simp only [optBitVal, bitVal]; rw [evalRev_nodesIn x hc h0 hn (hxs _ (by simp) w rfl)]
    rw [ho, sumOptBits_nodesIn x hc h0 hn (fun o' ho' w hw => hxs o' (by simp [ho']) w hw)]

lemma sumOptBits_suffix {V : Type} (x : V → Bool) {st0 st1 : CState V}
    (hc : CInv st1) (h0 : CInv st0) (suf : List (GEntry V)) (hsuf : st1.rev = suf ++ st0.rev) :
    ∀ {xs : List (Option (V ⊕ ℕ))}, (∀ o ∈ xs, ∀ w, o = some w → WireValid st0.len w) →
      sumOptBits (Sum.elim x (evalRev x st1.rev)) xs =
        sumOptBits (Sum.elim x (evalRev x st0.rev)) xs
  | [], _ => rfl
  | o :: rest, hxs => by
    simp only [sumOptBits]
    have ho : optBitVal (Sum.elim x (evalRev x st1.rev)) o =
        optBitVal (Sum.elim x (evalRev x st0.rev)) o := by
      cases o with
      | none => rfl
      | some w =>
        simp only [optBitVal, bitVal]
        have hwf : WellFormedRev (suf ++ st0.rev) := hsuf ▸ hc.1
        have hw' : WireValid st0.rev.length w := h0.2.symm ▸ hxs _ (by simp) w rfl
        congr 1
        simpa [hsuf] using evalRev_suffix x suf st0.rev hwf hw'
    rw [ho, sumOptBits_suffix x hc h0 suf hsuf (fun o' ho' w hw => hxs o' (by simp [ho']) w hw)]

lemma sumCols_nodesIn {V : Type} (x : V → Bool) {st0 st1 : CState V} {p : List Bool}
    (hc : CInv st1) (h0 : CInv st0) (hn : NodesIn st0 st1 p) :
    ∀ {cols : List (List (V ⊕ ℕ))}, (∀ c ∈ cols, ∀ w ∈ c, WireValid st0.len w) →
      sumCols (Sum.elim x (evalRev x st1.rev)) cols =
        sumCols (Sum.elim x (evalRev x st0.rev)) cols
  | [], _ => rfl
  | c :: rest, hcols => by
    simp only [sumCols]
    rw [sumBits_nodesIn x hc h0 hn (hcols c (by simp)),
      sumCols_nodesIn x hc h0 hn (fun c' hc' w hw => hcols c' (by simp [hc']) w hw)]

lemma emitConst_spec {V : Type} (x : V → Bool) {st : CState V} (h : CInv st)
    (p : List Bool) (b : Bool) :
    let res := emitConst st p b
    CInv res.1 ∧ st.len ≤ res.1.len ∧ res.1.len - st.len = 1 ∧
    WireValid res.1.len res.2 ∧ NodesIn st res.1 p ∧
    Sum.elim x (evalRev x res.1.rev) res.2 = b := by
  have hc := cinv_emit h p (fun o => Gate.const o b) rfl (fun _ hm => by simp [Gate.inputs] at hm)
  refine ⟨hc.1, hc.2.2, by simp [emitConst, CState.emit], hc.2.1, nodesIn_emit _ _ _, ?_⟩
  simpa [emitConst, gateEval] using evalRev_emit_new x h p (fun o => Gate.const o b) rfl

lemma emitNot_spec {V : Type} (x : V → Bool) {st : CState V} (h : CInv st)
    (p : List Bool) {a : V ⊕ ℕ} (ha : WireValid st.len a) :
    let res := emitNot st p a
    CInv res.1 ∧ st.len ≤ res.1.len ∧ res.1.len - st.len = 1 ∧
    WireValid res.1.len res.2 ∧ NodesIn st res.1 p ∧
    Sum.elim x (evalRev x res.1.rev) res.2 = !(Sum.elim x (evalRev x st.rev) a) := by
  have hc := cinv_emit h p (fun o => Gate.not a o) rfl (fun m hm => by
    simp [Gate.inputs] at hm; subst hm; exact ha)
  refine ⟨hc.1, hc.2.2, by simp [emitNot, CState.emit], hc.2.1, nodesIn_emit _ _ _, ?_⟩
  simpa [emitNot, gateEval] using evalRev_emit_new x h p (fun o => Gate.not a o) rfl

lemma emitAnd_spec {V : Type} (x : V → Bool) {st : CState V} (h : CInv st)
    (p : List Bool) {a b : V ⊕ ℕ} (ha : WireValid st.len a) (hb : WireValid st.len b) :
    let res := emitAnd st p a b
    CInv res.1 ∧ st.len ≤ res.1.len ∧ res.1.len - st.len = 1 ∧
    WireValid res.1.len res.2 ∧ NodesIn st res.1 p ∧
    Sum.elim x (evalRev x res.1.rev) res.2 =
      (Sum.elim x (evalRev x st.rev) a && Sum.elim x (evalRev x st.rev) b) := by
  have hc := cinv_emit h p (fun o => Gate.and a b o) rfl (fun m hm => by
    simp [Gate.inputs] at hm; rcases hm with rfl | rfl <;> assumption)
  refine ⟨hc.1, hc.2.2, by simp [emitAnd, CState.emit], hc.2.1, nodesIn_emit _ _ _, ?_⟩
  simpa [emitAnd, gateEval] using evalRev_emit_new x h p (fun o => Gate.and a b o) rfl

lemma emitOr_spec {V : Type} (x : V → Bool) {st : CState V} (h : CInv st)
    (p : List Bool) {a b : V ⊕ ℕ} (ha : WireValid st.len a) (hb : WireValid st.len b) :
    let res := emitOr st p a b
    CInv res.1 ∧ st.len ≤ res.1.len ∧ res.1.len - st.len = 1 ∧
    WireValid res.1.len res.2 ∧ NodesIn st res.1 p ∧
    Sum.elim x (evalRev x res.1.rev) res.2 =
      (Sum.elim x (evalRev x st.rev) a || Sum.elim x (evalRev x st.rev) b) := by
  have hc := cinv_emit h p (fun o => Gate.or a b o) rfl (fun m hm => by
    simp [Gate.inputs] at hm; rcases hm with rfl | rfl <;> assumption)
  refine ⟨hc.1, hc.2.2, by simp [emitOr, CState.emit], hc.2.1, nodesIn_emit _ _ _, ?_⟩
  simpa [emitOr, gateEval] using evalRev_emit_new x h p (fun o => Gate.or a b o) rfl

lemma emitXor_spec {V : Type} (x : V → Bool) {st : CState V} (h : CInv st)
    (p : List Bool) {a b : V ⊕ ℕ} (ha : WireValid st.len a) (hb : WireValid st.len b) :
    let res := emitXor st p a b
    CInv res.1 ∧ st.len ≤ res.1.len ∧ res.1.len - st.len = 1 ∧
    WireValid res.1.len res.2 ∧ NodesIn st res.1 p ∧
    Sum.elim x (evalRev x res.1.rev) res.2 =
      Bool.xor (Sum.elim x (evalRev x st.rev) a) (Sum.elim x (evalRev x st.rev) b) := by
  have hc := cinv_emit h p (fun o => Gate.xor a b o) rfl (fun m hm => by
    simp [Gate.inputs] at hm; rcases hm with rfl | rfl <;> assumption)
  refine ⟨hc.1, hc.2.2, by simp [emitXor, CState.emit], hc.2.1, nodesIn_emit _ _ _, ?_⟩
  simpa [emitXor, gateEval] using evalRev_emit_new x h p (fun o => Gate.xor a b o) rfl

lemma emitHalfAdder_spec {V : Type} (x : V → Bool) {st : CState V} (h : CInv st)
    (p : List Bool) {a b : V ⊕ ℕ} (ha : WireValid st.len a) (hb : WireValid st.len b) :
    let res := emitHalfAdder st p a b
    let st1 := res.1; let s := res.2.1; let c := res.2.2
    CInv st1 ∧ st.len ≤ st1.len ∧ st1.len - st.len = 2 ∧
    WireValid st1.len s ∧ WireValid st1.len c ∧ NodesIn st st1 p ∧
    bitVal (Sum.elim x (evalRev x st1.rev)) s + 2 * bitVal (Sum.elim x (evalRev x st1.rev)) c =
      bitVal (Sum.elim x (evalRev x st.rev)) a + bitVal (Sum.elim x (evalRev x st.rev)) b := by
  dsimp [emitHalfAdder]
  have h1 := emitXor_spec x h p ha hb
  rcases h1 with ⟨h1_inv, h1_le, h1_sub, h1_w, h1_nod, h1_eq⟩
  have h2 := emitAnd_spec x h1_inv p (wireValid_mono h1_le ha) (wireValid_mono h1_le hb)
  rcases h2 with ⟨h2_inv, h2_le, h2_sub, h2_w, h2_nod, h2_eq⟩
  refine ⟨h2_inv, le_trans h1_le h2_le, by omega,
    wireValid_mono h2_le h1_w, h2_w, nodesIn_trans h1_nod h2_nod, ?_⟩
  have hs2 := evalRev_nodesIn x h2_inv h1_inv h2_nod h1_w
  have ha1 := evalRev_nodesIn x h1_inv h h1_nod ha
  have hb1 := evalRev_nodesIn x h1_inv h h1_nod hb
  simp only [bitVal]
  rw [hs2, h1_eq, h2_eq, ha1, hb1]
  cases Sum.elim x (evalRev x st.rev) a <;> cases Sum.elim x (evalRev x st.rev) b <;> rfl

lemma emitFullAdder_spec {V : Type} (x : V → Bool) {st : CState V} (h : CInv st)
    (p : List Bool) {a b cin : V ⊕ ℕ}
    (ha : WireValid st.len a) (hb : WireValid st.len b) (hc : WireValid st.len cin) :
    let res := emitFullAdder st p a b cin
    let st1 := res.1; let s := res.2.1; let cout := res.2.2
    CInv st1 ∧ st.len ≤ st1.len ∧ st1.len - st.len = 5 ∧
    WireValid st1.len s ∧ WireValid st1.len cout ∧ NodesIn st st1 p ∧
    bitVal (Sum.elim x (evalRev x st1.rev)) s + 2 * bitVal (Sum.elim x (evalRev x st1.rev)) cout =
      bitVal (Sum.elim x (evalRev x st.rev)) a + bitVal (Sum.elim x (evalRev x st.rev)) b +
      bitVal (Sum.elim x (evalRev x st.rev)) cin := by
  dsimp [emitFullAdder]
  have h1 := emitXor_spec x h p ha hb
  rcases h1 with ⟨h1_inv, h1_le, h1_sub, h1_w, h1_nod, h1_eq⟩
  have h2 := emitXor_spec x h1_inv p h1_w (wireValid_mono h1_le hc)
  rcases h2 with ⟨h2_inv, h2_le, h2_sub, h2_w, h2_nod, h2_eq⟩
  have h3 := emitAnd_spec x h2_inv p (wireValid_mono (le_trans h1_le h2_le) ha)
    (wireValid_mono (le_trans h1_le h2_le) hb)
  rcases h3 with ⟨h3_inv, h3_le, h3_sub, h3_w, h3_nod, h3_eq⟩
  have h4 := emitAnd_spec x h3_inv p (wireValid_mono (le_trans h2_le h3_le) h1_w)
    (wireValid_mono (le_trans h1_le (le_trans h2_le h3_le)) hc)
  rcases h4 with ⟨h4_inv, h4_le, h4_sub, h4_w, h4_nod, h4_eq⟩
  have h5 := emitOr_spec x h4_inv p (wireValid_mono h4_le h3_w) h4_w
  rcases h5 with ⟨h5_inv, h5_le, h5_sub, h5_w, h5_nod, h5_eq⟩
  refine ⟨h5_inv, le_trans h1_le (le_trans h2_le (le_trans h3_le (le_trans h4_le h5_le))),
    by omega, wireValid_mono (le_trans h3_le (le_trans h4_le h5_le)) h2_w, h5_w,
    nodesIn_trans h1_nod (nodesIn_trans h2_nod (nodesIn_trans h3_nod (nodesIn_trans h4_nod h5_nod))), ?_⟩
  have hs5 := evalRev_nodesIn x h5_inv h2_inv (nodesIn_trans h3_nod (nodesIn_trans h4_nod h5_nod)) h2_w
  have ha1_5 := evalRev_nodesIn x h4_inv h3_inv h4_nod h3_w
  have ht3 := evalRev_nodesIn x h3_inv h1_inv (nodesIn_trans h2_nod h3_nod) h1_w
  have hc3 := evalRev_nodesIn x h3_inv h (nodesIn_trans h1_nod (nodesIn_trans h2_nod h3_nod)) hc
  have hc2 := evalRev_nodesIn x h1_inv h h1_nod hc
  have ha2 := evalRev_nodesIn x h2_inv h (nodesIn_trans h1_nod h2_nod) ha
  have hb2 := evalRev_nodesIn x h2_inv h (nodesIn_trans h1_nod h2_nod) hb
  simp only [bitVal]
  rw [hs5, h2_eq, h5_eq, ha1_5, h3_eq, h4_eq, ht3, h1_eq, hc3, hc2, ha2, hb2]
  cases Sum.elim x (evalRev x st.rev) a <;>
  cases Sum.elim x (evalRev x st.rev) b <;>
  cases Sum.elim x (evalRev x st.rev) cin <;> rfl

lemma compressCol_spec {V : Type} (x : V → Bool) :
    ∀ (col carries : List (V ⊕ ℕ)) {st : CState V} (_h : CInv st) (p : List Bool),
      (∀ w ∈ col, WireValid st.len w) →
      (∀ w ∈ carries, WireValid st.len w) →
      let res := compressCol st p col carries
      let st1 := res.1; let s? := res.2.1; let carries' := res.2.2
      CInv st1 ∧ st.len ≤ st1.len ∧
      (st1.len - st.len) + 5 * (carries'.length - carries.length) ≤ 5 * col.length + 2 ∧
      carries.length ≤ carries'.length ∧
      (∀ w, s? = some w → WireValid st1.len w) ∧
      (∀ w ∈ carries', WireValid st1.len w) ∧
      NodesIn st st1 p ∧
      optBitVal (Sum.elim x (evalRev x st1.rev)) s? +
        2 * sumBits (Sum.elim x (evalRev x st1.rev)) carries' =
      sumBits (Sum.elim x (evalRev x st.rev)) col +
        2 * sumBits (Sum.elim x (evalRev x st.rev)) carries
  | [], carries, st, h, p, _, hcar => by
    rw [compressCol]
    refine ⟨h, le_rfl, by simp, le_rfl, fun _ hw => by simp at hw,
      hcar, nodesIn_refl _ _, by simp [optBitVal, sumBits]⟩
  | [a], carries, st, h, p, hcol, hcar => by
    rw [compressCol]
    refine ⟨h, le_rfl, by simp, le_rfl,
      fun w hw => by simp only [Option.some.injEq] at hw; subst hw; exact hcol a (by simp),
      hcar, nodesIn_refl _ _, by simp [optBitVal, sumBits]⟩
  | [a, b], carries, st, h, p, hcol, hcar => by
    rw [compressCol]
    have ha := hcol a (by simp); have hb := hcol b (by simp)
    have hha := emitHalfAdder_spec x h p ha hb
    rcases hha with ⟨h1_inv, h1_le, h1_sub, hs, hc, h1_nod, h1_sum⟩
    refine ⟨h1_inv, h1_le, by simp; omega, by simp,
      fun w hw => by simp only [Option.some.injEq] at hw; subst hw; exact hs,
      fun w hw => by
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact hc
        · exact wireValid_mono h1_le (hcar w hw),
      h1_nod, ?_⟩
    simp only [optBitVal, sumBits, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
    have hcar_eq := sumBits_nodesIn x h1_inv h h1_nod hcar
    simp only [sumBits] at hcar_eq
    linarith
  | a :: b :: c :: rest, carries, st, h, p, hcol, hcar => by
    have ha := hcol a (by simp); have hb := hcol b (by simp); have hc := hcol c (by simp)
    have hfa := emitFullAdder_spec x h p ha hb hc
    rcases hfa with ⟨h1_inv, h1_le, h1_sub, hs, hcout, h1_nod, h1_sum⟩
    set st1 := (emitFullAdder st p a b c).1
    set s := (emitFullAdder st p a b c).2.1
    set cout := (emitFullAdder st p a b c).2.2
    have hrec := compressCol_spec x (s :: rest) (cout :: carries) h1_inv p
      (fun w hw => by
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact hs
        · exact wireValid_mono h1_le (hcol w (by simp [hw])))
      (fun w hw => by
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact hcout
        · exact wireValid_mono h1_le (hcar w hw))
    rcases hrec with ⟨h2_inv, h2_le, h2_bnd, h2_carle, h2_s, h2_car, h2_nod, h2_sum⟩
    have hdef : compressCol st p (a :: b :: c :: rest) carries =
        compressCol st1 p (s :: rest) (cout :: carries) := by rw [compressCol]
    dsimp only
    rw [hdef]
    refine ⟨h2_inv, le_trans h1_le h2_le, ?_, ?_, h2_s, h2_car, nodesIn_trans h1_nod h2_nod, ?_⟩
    · simp only [List.length_cons] at h2_bnd h2_carle ⊢; omega
    · simp only [List.length_cons] at h2_carle ⊢; omega
    · have hrest_eq := sumBits_nodesIn x h1_inv h h1_nod (fun w hw => hcol w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))))
      have hcar_eq := sumBits_nodesIn x h1_inv h h1_nod hcar
      simp only [sumBits, List.map_cons, List.sum_cons] at h2_sum hrest_eq hcar_eq ⊢
      linarith
termination_by col => col.length

lemma compressAll_spec {V : Type} (x : V → Bool) :
    ∀ (cols : List (List (V ⊕ ℕ))) {st : CState V} (_h : CInv st) (p : List Bool),
      (∀ col ∈ cols, ∀ w ∈ col, WireValid st.len w) →
      let res := compressAll st p cols
      let st1 := res.1; let outs := res.2
      CInv st1 ∧ st.len ≤ st1.len ∧
      st1.len - st.len ≤ 5 * (cols.map List.length).sum + 2 * cols.length ∧
      outs.length = cols.length ∧
      (∀ o ∈ outs, ∀ w, o = some w → WireValid st1.len w) ∧
      NodesIn st st1 p ∧
      ∃ q : ℕ, sumOptBits (Sum.elim x (evalRev x st1.rev)) outs + q * 2 ^ cols.length =
        sumCols (Sum.elim x (evalRev x st.rev)) cols
  | [], st, h, p, _ => by
    rw [compressAll]
    exact ⟨h, le_rfl, by simp, rfl, fun _ ho => by simp at ho, nodesIn_refl _ _, ⟨0, by simp [sumOptBits, sumCols]⟩⟩
  | col :: rest, st, h, p, hcols => by
    have hcc := compressCol_spec x col [] h p (hcols col (by simp)) (fun _ hw => by simp at hw)
    rcases hcc with ⟨h1_inv, h1_le, h1_bnd, _, h1_s, h1_car, h1_nod, h1_sum⟩
    set st1 := (compressCol st p col []).1
    set s? := (compressCol st p col []).2.1
    set carries := (compressCol st p col []).2.2
    let rest' := match rest with | [] => [] | next :: tail => (carries ++ next) :: tail
    have hrest'_len : rest'.length = rest.length := by cases rest <;> rfl
    have hrest'_pot : (rest'.map List.length).sum ≤ carries.length + (rest.map List.length).sum := by
      cases rest with
      | nil => simp [rest']
      | cons next tail => simp [rest', List.length_append]; omega
    have hrest'_w : ∀ c ∈ rest', ∀ w ∈ c, WireValid st1.len w := by
      cases rest with
      | nil => intro c hc; simp [rest'] at hc
      | cons next tail =>
        intro c hc w hw
        simp only [rest', List.mem_cons] at hc
        rcases hc with rfl | hc
        · rcases List.mem_append.mp hw with hw | hw
          · exact h1_car w hw
          · exact wireValid_mono h1_le (hcols next (by simp) w hw)
        · exact wireValid_mono h1_le (hcols c (by simp [hc]) w hw)
    have hrec := compressAll_spec x rest' h1_inv p hrest'_w
    rcases hrec with ⟨h2_inv, h2_le, h2_bnd, h2_len, h2_w, h2_nod, q, hq⟩
    dsimp only
    rw [compressAll]
    dsimp only [st1, s?, carries, rest'] at h1_le h2_le h1_bnd h2_bnd h2_len h2_w h2_nod hq hrest'_len hrest'_pot h1_sum ⊢
    refine ⟨h2_inv, le_trans h1_le h2_le, ?_, ?_, ?_, nodesIn_trans h1_nod h2_nod, ?_⟩
    · simp only [List.map_cons, List.sum_cons, List.length_cons, List.length_nil, Nat.sub_zero] at h1_bnd h2_bnd ⊢
      have h_tri : ∀ a b c : ℕ, a ≤ b → b ≤ c → c - a = (c - b) + (b - a) :=
        fun a b c h1 h2 => by omega
      rw [h_tri _ _ _ h1_le h2_le]
      rw [hrest'_len] at h2_bnd
      linarith [h1_bnd, h2_bnd, hrest'_pot]
    · simp only [List.length_cons]
      rw [h2_len, hrest'_len]
    · intro o ho w hw
      simp only [List.mem_cons] at ho
      rcases ho with rfl | ho
      · exact wireValid_mono h2_le (h1_s w hw)
      · exact h2_w o ho w hw
    · have hs?_eq : optBitVal (Sum.elim x (evalRev x (compressAll st1 p rest').1.rev)) s? =
          optBitVal (Sum.elim x (evalRev x st1.rev)) s? := by
        cases hs : s? with
        | none => rfl
        | some w =>
          simp only [optBitVal, bitVal]
          rw [evalRev_nodesIn x h2_inv h1_inv h2_nod (h1_s w hs)]
      cases rest with
      | nil =>
        refine ⟨sumBits (Sum.elim x (evalRev x st1.rev)) carries, ?_⟩
        simp only [rest', sumOptBits, sumCols, List.length_singleton, pow_one,
          List.length_nil, sumBits, List.map_nil, List.sum_nil, mul_zero, add_zero] at hs?_eq h1_sum hq ⊢
        linarith
      | cons next tail =>
        refine ⟨q, ?_⟩
        have hnext_eq := sumBits_nodesIn x h1_inv h h1_nod (hcols next (by simp))
        have htail_eq := sumCols_nodesIn x h1_inv h h1_nod
          (fun c hc w hw => hcols c (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc)) w hw)
        dsimp only [st1, s?, carries, rest'] at hs?_eq hnext_eq htail_eq h1_sum hq ⊢
        simp only [sumOptBits, sumCols, List.length_cons, pow_succ] at hs?_eq h1_sum hq ⊢
        simp only [sumBits, List.map_nil, List.sum_nil, mul_zero, add_zero] at h1_sum hnext_eq ⊢
        rw [sumBits_append] at hq
        simp only [sumBits] at hq
        rw [hs?_eq, ← hnext_eq, ← htail_eq]
        have h_pow : q * (2 ^ tail.length * 2 * 2) = 2 * (q * (2 ^ tail.length * 2)) := by ring
        rw [h_pow]
        linarith
termination_by cols => cols.length
decreasing_by
  cases rest <;> simp

def emitCmpLeStep {V : Type} (st : CState V) (p : List Bool) (acc : V ⊕ ℕ)
    (o : Option (V ⊕ ℕ)) (kbit : Bool) : CState V × (V ⊕ ℕ) :=
  match o with
  | none => if kbit then emitConst st p true else (st, acc)
  | some w =>
    let (st1, nw) := emitNot st p w
    if kbit then emitOr st1 p nw acc else emitAnd st1 p nw acc

def emitCmpLeLoop {V : Type} (st : CState V) (p : List Bool) (acc : V ⊕ ℕ) :
    List (Option (V ⊕ ℕ)) → ℕ → CState V × (V ⊕ ℕ)
  | [], _ => (st, acc)
  | o :: rest, K =>
    let (st1, acc1) := emitCmpLeStep st p acc o (decide (K % 2 = 1))
    emitCmpLeLoop st1 p acc1 rest (K / 2)

def emitCmpLe {V : Type} (st : CState V) (p : List Bool)
    (xs : List (Option (V ⊕ ℕ))) (K : ℕ) : CState V × (V ⊕ ℕ) :=
  let (st0, acc0) := emitConst st p true
  emitCmpLeLoop st0 p acc0 xs K

def emitCmpGeStep {V : Type} (st : CState V) (p : List Bool) (acc : V ⊕ ℕ)
    (o : Option (V ⊕ ℕ)) (kbit : Bool) : CState V × (V ⊕ ℕ) :=
  match o with
  | none => if kbit then emitConst st p false else (st, acc)
  | some w => if kbit then emitAnd st p w acc else emitOr st p w acc

def emitCmpGeLoop {V : Type} (st : CState V) (p : List Bool) (acc : V ⊕ ℕ) :
    List (Option (V ⊕ ℕ)) → ℕ → CState V × (V ⊕ ℕ)
  | [], _ => (st, acc)
  | o :: rest, K =>
    let (st1, acc1) := emitCmpGeStep st p acc o (decide (K % 2 = 1))
    emitCmpGeLoop st1 p acc1 rest (K / 2)

def emitCmpGe {V : Type} (st : CState V) (p : List Bool)
    (xs : List (Option (V ⊕ ℕ))) (K : ℕ) : CState V × (V ⊕ ℕ) :=
  let (st0, acc0) := emitConst st p true
  emitCmpGeLoop st0 p acc0 xs K

lemma emitCmpLeStep_spec {V : Type} (x : V → Bool) {st : CState V} (h : CInv st)
    (p : List Bool) {acc : V ⊕ ℕ} (hacc : WireValid st.len acc)
    {o : Option (V ⊕ ℕ)} (ho : ∀ w, o = some w → WireValid st.len w) (kbit : Bool)
    {i L K_low : ℕ} (hL : L < 2 ^ i) (hK : K_low < 2 ^ i)
    (heq : Sum.elim x (evalRev x st.rev) acc = decide (L ≤ K_low)) :
    let res := emitCmpLeStep st p acc o kbit
    CInv res.1 ∧ st.len ≤ res.1.len ∧ res.1.len - st.len ≤ 2 ∧
    WireValid res.1.len res.2 ∧ NodesIn st res.1 p ∧
    Sum.elim x (evalRev x res.1.rev) res.2 =
      decide (L + 2 ^ i * optBitVal (Sum.elim x (evalRev x st.rev)) o ≤
        K_low + 2 ^ i * kbit.toNat) := by
  cases o with
  | none =>
    cases kbit with
    | false =>
      refine ⟨h, le_rfl, by simp [emitCmpLeStep], hacc, nodesIn_refl _ _, ?_⟩
      simpa [emitCmpLeStep, optBitVal] using heq
    | true =>
      have hc := emitConst_spec x h p true
      refine ⟨hc.1, hc.2.1, by simp [emitCmpLeStep]; omega, hc.2.2.2.1, hc.2.2.2.2.1, ?_⟩
      dsimp only [emitCmpLeStep]
      simp only [ite_true, optBitVal, Bool.toNat_true, mul_zero, add_zero, mul_one]
      rw [hc.2.2.2.2.2]
      symm; simp; omega
  | some w =>
    have hw := ho w rfl
    have hn := emitNot_spec x h p hw
    rcases hn with ⟨h1_inv, h1_le, h1_sub, h1_w, h1_nod, h1_eq⟩
    set st1 := (emitNot st p w).1; set nw := (emitNot st p w).2
    have hacc1 := evalRev_nodesIn x h1_inv h h1_nod hacc
    cases kbit with
    | false =>
      have ha := emitAnd_spec x h1_inv p h1_w (wireValid_mono h1_le hacc)
      rcases ha with ⟨h2_inv, h2_le, h2_sub, h2_w, h2_nod, h2_eq⟩
      refine ⟨h2_inv, le_trans h1_le h2_le, ?_, h2_w,
        nodesIn_trans h1_nod h2_nod, ?_⟩
      · dsimp only [emitCmpLeStep]; simp only [ite_false, Bool.false_eq_true]; change (emitAnd st1 p nw acc).1.len - st.len ≤ 2; omega
      · dsimp only [emitCmpLeStep]
        simp only [ite_false, Bool.false_eq_true, optBitVal, bitVal, Bool.toNat_false, mul_zero, add_zero]
        rw [h2_eq, h1_eq, hacc1, heq]
        cases Sum.elim x (evalRev x st.rev) w <;> simp <;> omega
    | true =>
      have hor := emitOr_spec x h1_inv p h1_w (wireValid_mono h1_le hacc)
      rcases hor with ⟨h2_inv, h2_le, h2_sub, h2_w, h2_nod, h2_eq⟩
      refine ⟨h2_inv, le_trans h1_le h2_le, ?_, h2_w,
        nodesIn_trans h1_nod h2_nod, ?_⟩
      · dsimp only [emitCmpLeStep]; simp only [ite_true]; change (emitOr st1 p nw acc).1.len - st.len ≤ 2; omega
      · dsimp only [emitCmpLeStep]
        simp only [ite_true, optBitVal, bitVal, Bool.toNat_true, mul_one]
        rw [h2_eq, h1_eq, hacc1, heq]
        cases Sum.elim x (evalRev x st.rev) w <;> simp <;> omega

lemma emitCmpLeLoop_spec {V : Type} (x : V → Bool) :
    ∀ (xs : List (Option (V ⊕ ℕ))) (K i L K_low : ℕ) {st : CState V} (_h : CInv st)
      (p : List Bool) {acc : V ⊕ ℕ},
      WireValid st.len acc → (∀ o ∈ xs, ∀ w, o = some w → WireValid st.len w) →
      L < 2 ^ i → K_low < 2 ^ i → K < 2 ^ xs.length →
      Sum.elim x (evalRev x st.rev) acc = decide (L ≤ K_low) →
      let res := emitCmpLeLoop st p acc xs K
      CInv res.1 ∧ st.len ≤ res.1.len ∧ res.1.len - st.len ≤ 2 * xs.length ∧
      WireValid res.1.len res.2 ∧ NodesIn st res.1 p ∧
      Sum.elim x (evalRev x res.1.rev) res.2 =
        decide (L + 2 ^ i * sumOptBits (Sum.elim x (evalRev x st.rev)) xs ≤ K_low + 2 ^ i * K)
  | [], K, i, L, K_low, st, h, p, acc, hacc, _, hL, hK, hK_lt, heq => by
    have hK0 : K = 0 := by simp at hK_lt; omega
    subst hK0
    refine ⟨h, le_rfl, by simp [emitCmpLeLoop], hacc, nodesIn_refl _ _, ?_⟩
    simp [emitCmpLeLoop, sumOptBits, heq]
  | o :: rest, K, i, L, K_low, st, h, p, acc, hacc, hxs, hL, hK, hK_lt, heq => by
    have hs := emitCmpLeStep_spec x h p hacc (hxs o (by simp)) (decide (K % 2 = 1)) hL hK heq
    rcases hs with ⟨h1_inv, h1_le, h1_sub, h1_w, h1_nod, h1_eq⟩
    set st1 := (emitCmpLeStep st p acc o (decide (K % 2 = 1))).1
    set acc1 := (emitCmpLeStep st p acc o (decide (K % 2 = 1))).2
    have hL' : L + 2 ^ i * optBitVal (Sum.elim x (evalRev x st.rev)) o < 2 ^ (i + 1) := by
      have hb : optBitVal (Sum.elim x (evalRev x st.rev)) o ≤ 1 := by
        cases o with | none => simp [optBitVal] | some w => cases hvw : Sum.elim x (evalRev x st.rev) w <;> simp [optBitVal, bitVal, hvw]
      rw [pow_succ]; nlinarith
    have hK' : K_low + 2 ^ i * (decide (K % 2 = 1)).toNat < 2 ^ (i + 1) := by
      have : (decide (K % 2 = 1)).toNat ≤ 1 := by cases decide (K % 2 = 1) <;> simp
      rw [pow_succ]; nlinarith
    have hK_div : K / 2 < 2 ^ rest.length := by
      simp only [List.length_cons, pow_succ] at hK_lt; omega
    have hrec := emitCmpLeLoop_spec x rest (K / 2) (i + 1)
      (L + 2 ^ i * optBitVal (Sum.elim x (evalRev x st.rev)) o)
      (K_low + 2 ^ i * (decide (K % 2 = 1)).toNat) h1_inv p h1_w
      (fun o' ho' w hw => wireValid_mono h1_le (hxs o' (by simp [ho']) w hw))
      hL' hK' hK_div h1_eq
    rcases hrec with ⟨h2_inv, h2_le, h2_sub, h2_w, h2_nod, h2_eq⟩
    refine ⟨h2_inv, le_trans h1_le h2_le, ?_, h2_w, nodesIn_trans h1_nod h2_nod, ?_⟩
    · dsimp only [emitCmpLeLoop, List.length_cons]
      change (emitCmpLeLoop st1 p acc1 rest (K / 2)).1.len - st.len ≤ 2 * (rest.length + 1)
      omega
    · simp only [emitCmpLeLoop]
      rw [h2_eq]
      have hrest_eq := sumOptBits_nodesIn x h1_inv h h1_nod
        (fun o' ho' w hw => hxs o' (List.mem_cons_of_mem _ ho') w hw)
      rw [hrest_eq]
      simp only [sumOptBits, pow_succ]
      have hmod : (decide (K % 2 = 1)).toNat = K % 2 := by
        rcases Nat.mod_two_eq_zero_or_one K with hk0 | hk1 <;> simp [*]
      rw [hmod]
      congr 1
      have hdiv : K % 2 + 2 * (K / 2) = K := by omega
      have h1 : K_low + 2 ^ i * (K % 2) + 2 ^ i * 2 * (K / 2) = K_low + 2 ^ i * K := by
        calc K_low + 2 ^ i * (K % 2) + 2 ^ i * 2 * (K / 2)
            = K_low + 2 ^ i * (K % 2 + 2 * (K / 2)) := by ring
          _ = K_low + 2 ^ i * K := by rw [hdiv]
      have h2 : L + 2 ^ i * optBitVal (Sum.elim x (evalRev x st.rev)) o +
            2 ^ i * 2 * sumOptBits (Sum.elim x (evalRev x st.rev)) rest =
          L + 2 ^ i * (optBitVal (Sum.elim x (evalRev x st.rev)) o +
            2 * sumOptBits (Sum.elim x (evalRev x st.rev)) rest) := by ring
      simp only [h1, h2]

lemma emitCmpLe_spec {V : Type} (x : V → Bool) {st : CState V} (h : CInv st)
    (p : List Bool) {xs : List (Option (V ⊕ ℕ))}
    (hxs : ∀ o ∈ xs, ∀ w, o = some w → WireValid st.len w) {K : ℕ} (hK_lt : K < 2 ^ xs.length) :
    let res := emitCmpLe st p xs K
    CInv res.1 ∧ st.len ≤ res.1.len ∧ res.1.len - st.len ≤ 2 * xs.length + 1 ∧
    WireValid res.1.len res.2 ∧ NodesIn st res.1 p ∧
    Sum.elim x (evalRev x res.1.rev) res.2 =
      decide (sumOptBits (Sum.elim x (evalRev x st.rev)) xs ≤ K) := by
  dsimp [emitCmpLe]
  have hc := emitConst_spec x h p true
  rcases hc with ⟨h0_inv, h0_le, h0_sub, h0_w, h0_nod, h0_eq⟩
  set st0 := (emitConst st p true).1; set acc0 := (emitConst st p true).2
  have hl := emitCmpLeLoop_spec x xs K 0 0 0 h0_inv p h0_w
    (fun o ho w hw => wireValid_mono h0_le (hxs o ho w hw)) (by simp) (by simp) hK_lt (by simpa using h0_eq)
  rcases hl with ⟨h1_inv, h1_le, h1_sub, h1_w, h1_nod, h1_eq⟩
  refine ⟨h1_inv, le_trans h0_le h1_le, by omega, h1_w, nodesIn_trans h0_nod h1_nod, ?_⟩
  rw [h1_eq]
  have hxs_eq := sumOptBits_nodesIn x h0_inv h h0_nod hxs
  simp [hxs_eq]

lemma emitCmpGeStep_spec {V : Type} (x : V → Bool) {st : CState V} (h : CInv st)
    (p : List Bool) {acc : V ⊕ ℕ} (hacc : WireValid st.len acc)
    {o : Option (V ⊕ ℕ)} (ho : ∀ w, o = some w → WireValid st.len w) (kbit : Bool)
    {i L K_low : ℕ} (hL : L < 2 ^ i) (hK : K_low < 2 ^ i)
    (heq : Sum.elim x (evalRev x st.rev) acc = decide (K_low ≤ L)) :
    let res := emitCmpGeStep st p acc o kbit
    CInv res.1 ∧ st.len ≤ res.1.len ∧ res.1.len - st.len ≤ 1 ∧
    WireValid res.1.len res.2 ∧ NodesIn st res.1 p ∧
    Sum.elim x (evalRev x res.1.rev) res.2 =
      decide (K_low + 2 ^ i * kbit.toNat ≤
        L + 2 ^ i * optBitVal (Sum.elim x (evalRev x st.rev)) o) := by
  cases o with
  | none =>
    cases kbit with
    | false =>
      refine ⟨h, le_rfl, by simp [emitCmpGeStep], hacc, nodesIn_refl _ _, ?_⟩
      simpa [emitCmpGeStep, optBitVal] using heq
    | true =>
      have hc := emitConst_spec x h p false
      refine ⟨hc.1, hc.2.1, by simp [emitCmpGeStep]; omega, hc.2.2.2.1, hc.2.2.2.2.1, ?_⟩
      dsimp only [emitCmpGeStep]
      simp only [ite_true, optBitVal, Bool.toNat_true, mul_zero, add_zero, mul_one]
      rw [hc.2.2.2.2.2]
      symm; simp; omega
  | some w =>
    have hw := ho w rfl
    cases kbit with
    | false =>
      have hor := emitOr_spec x h p hw hacc
      rcases hor with ⟨h1_inv, h1_le, h1_sub, h1_w, h1_nod, h1_eq⟩
      refine ⟨h1_inv, h1_le, by simp [emitCmpGeStep]; omega, h1_w, h1_nod, ?_⟩
      dsimp only [emitCmpGeStep]
      simp only [ite_false, Bool.false_eq_true, optBitVal, bitVal, Bool.toNat_false, mul_zero, add_zero]
      rw [h1_eq, heq]
      cases Sum.elim x (evalRev x st.rev) w <;> simp <;> omega
    | true =>
      have ha := emitAnd_spec x h p hw hacc
      rcases ha with ⟨h1_inv, h1_le, h1_sub, h1_w, h1_nod, h1_eq⟩
      refine ⟨h1_inv, h1_le, by simp [emitCmpGeStep]; omega, h1_w, h1_nod, ?_⟩
      dsimp only [emitCmpGeStep]
      simp only [ite_true, optBitVal, bitVal, Bool.toNat_true, mul_one]
      rw [h1_eq, heq]
      cases Sum.elim x (evalRev x st.rev) w <;> simp <;> omega

lemma emitCmpGeLoop_spec {V : Type} (x : V → Bool) :
    ∀ (xs : List (Option (V ⊕ ℕ))) (K i L K_low : ℕ) {st : CState V} (_h : CInv st)
      (p : List Bool) {acc : V ⊕ ℕ},
      WireValid st.len acc → (∀ o ∈ xs, ∀ w, o = some w → WireValid st.len w) →
      L < 2 ^ i → K_low < 2 ^ i → K < 2 ^ xs.length →
      Sum.elim x (evalRev x st.rev) acc = decide (K_low ≤ L) →
      let res := emitCmpGeLoop st p acc xs K
      CInv res.1 ∧ st.len ≤ res.1.len ∧ res.1.len - st.len ≤ xs.length ∧
      WireValid res.1.len res.2 ∧ NodesIn st res.1 p ∧
      Sum.elim x (evalRev x res.1.rev) res.2 =
        decide (K_low + 2 ^ i * K ≤ L + 2 ^ i * sumOptBits (Sum.elim x (evalRev x st.rev)) xs)
  | [], K, i, L, K_low, st, h, p, acc, hacc, _, hL, hK, hK_lt, heq => by
    have hK0 : K = 0 := by simp at hK_lt; omega
    subst hK0
    refine ⟨h, le_rfl, by simp [emitCmpGeLoop], hacc, nodesIn_refl _ _, ?_⟩
    simp [emitCmpGeLoop, sumOptBits, heq]
  | o :: rest, K, i, L, K_low, st, h, p, acc, hacc, hxs, hL, hK, hK_lt, heq => by
    have hs := emitCmpGeStep_spec x h p hacc (hxs o (by simp)) (decide (K % 2 = 1)) hL hK heq
    rcases hs with ⟨h1_inv, h1_le, h1_sub, h1_w, h1_nod, h1_eq⟩
    set st1 := (emitCmpGeStep st p acc o (decide (K % 2 = 1))).1
    set acc1 := (emitCmpGeStep st p acc o (decide (K % 2 = 1))).2
    have hL' : L + 2 ^ i * optBitVal (Sum.elim x (evalRev x st.rev)) o < 2 ^ (i + 1) := by
      have hb : optBitVal (Sum.elim x (evalRev x st.rev)) o ≤ 1 := by
        cases o with
        | none => simp [optBitVal]
        | some w => cases hvw : Sum.elim x (evalRev x st.rev) w <;> simp [optBitVal, bitVal, hvw]
      rw [pow_succ]; nlinarith
    have hK' : K_low + 2 ^ i * (decide (K % 2 = 1)).toNat < 2 ^ (i + 1) := by
      have : (decide (K % 2 = 1)).toNat ≤ 1 := by cases decide (K % 2 = 1) <;> simp
      rw [pow_succ]; nlinarith
    have hK_div : K / 2 < 2 ^ rest.length := by
      simp only [List.length_cons, pow_succ] at hK_lt; omega
    have hrec := emitCmpGeLoop_spec x rest (K / 2) (i + 1)
      (L + 2 ^ i * optBitVal (Sum.elim x (evalRev x st.rev)) o)
      (K_low + 2 ^ i * (decide (K % 2 = 1)).toNat) h1_inv p h1_w
      (fun o' ho' w hw => wireValid_mono h1_le (hxs o' (by simp [ho']) w hw))
      hL' hK' hK_div h1_eq
    rcases hrec with ⟨h2_inv, h2_le, h2_sub, h2_w, h2_nod, h2_eq⟩
    refine ⟨h2_inv, le_trans h1_le h2_le, ?_,
      h2_w, nodesIn_trans h1_nod h2_nod, ?_⟩
    · dsimp only [emitCmpGeLoop, List.length_cons]
      change (emitCmpGeLoop st1 p acc1 rest (K / 2)).1.len - st.len ≤ rest.length + 1
      omega
    · simp only [emitCmpGeLoop]
      rw [h2_eq]
      have hrest_eq := sumOptBits_nodesIn x h1_inv h h1_nod
        (fun o' ho' w hw => hxs o' (List.mem_cons_of_mem _ ho') w hw)
      rw [hrest_eq]
      simp only [sumOptBits, pow_succ]
      have hmod : (decide (K % 2 = 1)).toNat = K % 2 := by
        rcases Nat.mod_two_eq_zero_or_one K with hk0 | hk1 <;> simp [*]
      rw [hmod]
      have hdiv : K % 2 + 2 * (K / 2) = K := by omega
      have h1 : K_low + 2 ^ i * (K % 2) + 2 ^ i * 2 * (K / 2) = K_low + 2 ^ i * K := by
        calc K_low + 2 ^ i * (K % 2) + 2 ^ i * 2 * (K / 2)
            = K_low + 2 ^ i * (K % 2 + 2 * (K / 2)) := by ring
          _ = K_low + 2 ^ i * K := by rw [hdiv]
      have h2 : L + 2 ^ i * optBitVal (Sum.elim x (evalRev x st.rev)) o +
            2 ^ i * 2 * sumOptBits (Sum.elim x (evalRev x st.rev)) rest =
          L + 2 ^ i * (optBitVal (Sum.elim x (evalRev x st.rev)) o +
            2 * sumOptBits (Sum.elim x (evalRev x st.rev)) rest) := by ring
      simp only [h1, h2]
      rfl

lemma emitCmpGe_spec {V : Type} (x : V → Bool) {st : CState V} (h : CInv st)
    (p : List Bool) {xs : List (Option (V ⊕ ℕ))}
    (hxs : ∀ o ∈ xs, ∀ w, o = some w → WireValid st.len w) {K : ℕ} (hK_lt : K < 2 ^ xs.length) :
    let res := emitCmpGe st p xs K
    CInv res.1 ∧ st.len ≤ res.1.len ∧ res.1.len - st.len ≤ xs.length + 1 ∧
    WireValid res.1.len res.2 ∧ NodesIn st res.1 p ∧
    Sum.elim x (evalRev x res.1.rev) res.2 =
      decide (K ≤ sumOptBits (Sum.elim x (evalRev x st.rev)) xs) := by
  dsimp [emitCmpGe]
  have hc := emitConst_spec x h p true
  rcases hc with ⟨h0_inv, h0_le, h0_sub, h0_w, h0_nod, h0_eq⟩
  set st0 := (emitConst st p true).1; set acc0 := (emitConst st p true).2
  have hl := emitCmpGeLoop_spec x xs K 0 0 0 h0_inv p h0_w
    (fun o ho w hw => wireValid_mono h0_le (hxs o ho w hw)) (by simp) (by simp) hK_lt (by simpa using h0_eq)
  rcases hl with ⟨h1_inv, h1_le, h1_sub, h1_w, h1_nod, h1_eq⟩
  refine ⟨h1_inv, le_trans h0_le h1_le, by omega, h1_w, nodesIn_trans h0_nod h1_nod, ?_⟩
  rw [h1_eq]
  have hxs_eq := sumOptBits_nodesIn x h0_inv h h0_nod hxs
  simp [hxs_eq]

def lcp : List Bool → List Bool → List Bool
  | a :: as, b :: bs => if a = b then a :: lcp as bs else []
  | _, _ => []

lemma lcp_isPrefix_left : ∀ (u v : List Bool), List.IsPrefix (lcp u v) u
  | [], _ => ⟨[], rfl⟩
  | _ :: _, [] => ⟨_, rfl⟩
  | a :: as, b :: bs => by
    dsimp [lcp]
    split_ifs with h
    · subst h; exact List.cons_prefix_cons.mpr ⟨rfl, lcp_isPrefix_left as bs⟩
    · exact ⟨_, rfl⟩

lemma lcp_isPrefix_right : ∀ (u v : List Bool), List.IsPrefix (lcp u v) v
  | [], _ => ⟨_, rfl⟩
  | _ :: _, [] => ⟨_, rfl⟩
  | a :: as, b :: bs => by
    dsimp [lcp]
    split_ifs with h
    · subst h; exact List.cons_prefix_cons.mpr ⟨rfl, lcp_isPrefix_right as bs⟩
    · exact ⟨_, rfl⟩

lemma lcp_isPrefix_iff : ∀ (p u v : List Bool),
    List.IsPrefix p (lcp u v) ↔ (List.IsPrefix p u ∧ List.IsPrefix p v)
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp [lcp]
  | _ :: _, _ :: _, [] => by simp [lcp]
  | c :: cs, a :: as, b :: bs => by
    dsimp [lcp]
    split_ifs with h
    · subst h
      simp only [List.cons_prefix_cons, lcp_isPrefix_iff cs as bs]
      tauto
    · simp only [List.prefix_nil, List.cons_prefix_cons]
      constructor
      · intro hc; simp at hc
      · rintro ⟨⟨rfl, _⟩, ⟨rfl, _⟩⟩; exact absurd rfl h

lemma lcp_lt_of_ne : ∀ {u v : List Bool}, u.length = v.length → u ≠ v →
    (lcp u v).length < u.length ∧
    ∃ d : Bool, List.IsPrefix (lcp u v ++ [d]) u ∧ List.IsPrefix (lcp u v ++ [!d]) v
  | [], [], _, hne => absurd rfl hne
  | a :: as, b :: bs, hlen, hne => by
    simp only [List.length_cons] at hlen
    dsimp [lcp]
    split_ifs with h
    · subst h
      have hne' : as ≠ bs := fun h => hne (congrArg (a :: ·) h)
      rcases lcp_lt_of_ne (by omega) hne' with ⟨hlt, d, hd1, hd2⟩
      refine ⟨by simp [hlt], d, ?_, ?_⟩
      · simp [List.cons_append, hd1]
      · simp [List.cons_append, hd2]
    · refine ⟨by simp, a, ?_, ?_⟩
      · simp
      · have hb : b = !a := by cases a <;> cases b <;> simp_all
        subst hb; simp

def occ {V : Type} [Fintype V] (addr : V → List Bool) (p : List Bool) : Bool :=
  decide (∃ v : V, List.IsPrefix p (addr v))

def isBranch {V : Type} [Fintype V] (addr : V → List Bool) (p : List Bool) : Bool :=
  occ addr (p ++ [false]) && occ addr (p ++ [true])

def ancOf {V : Type} [Fintype V] (addr : V → List Bool) : List Bool → List Bool
  | [] => []
  | a :: as =>
    let q := (a :: as).dropLast
    if isBranch addr q then q else ancOf addr q
termination_by p => p.length
decreasing_by
  simp [q]

def emitDiffs {n : ℕ} (st : CState (Bool × Fin n)) (p : List Bool)
    (addr : (Bool × Fin n) → List Bool) (perm : Equiv.Perm (Fin n)) :
    List (Fin n) → CState (Bool × Fin n) × List ((Bool × Fin n) ⊕ ℕ)
  | [] => (st, [])
  | i :: rest =>
    let (st1, ds) := emitDiffs st p addr perm rest
    if lcp (addr (false, i)) (addr (true, perm i)) = p then
      let (st2, d) := emitXor st1 p (Sum.inl (false, i)) (Sum.inl (true, perm i))
      (st2, d :: ds)
    else (st1, ds)

def optToList {α : Type} : Option α → List α
  | none => []
  | some a => [a]

def mergePairCols {V : Type} : ℕ → List (Option (V ⊕ ℕ)) → List (Option (V ⊕ ℕ)) → List (List (V ⊕ ℕ))
  | 0, _, _ => []
  | k + 1, wL, wR =>
    let hL := match wL with | [] => [] | o :: _ => optToList o
    let hR := match wR with | [] => [] | o :: _ => optToList o
    (hL ++ hR) :: mergePairCols k wL.tail wR.tail

def mergeCols {V : Type} (b : ℕ) (ds : List (V ⊕ ℕ))
    (wL wR : List (Option (V ⊕ ℕ))) : List (List (V ⊕ ℕ)) :=
  match mergePairCols b wL wR with
  | [] => []
  | c0 :: rest => (ds ++ c0) :: rest

def buildBranches {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) (b : ℕ) (p : List Bool)
    (st : CState (Bool × Fin n)) :
    List (Fin r) → List (List (Option ((Bool × Fin n) ⊕ ℕ))) →
      List (List (Option ((Bool × Fin n) ⊕ ℕ))) →
      CState (Bool × Fin n) × List (List (Option ((Bool × Fin n) ⊕ ℕ)))
  | [], _, _ => (st, [])
  | j :: js, wLs, wRs =>
    let wL := wLs.headD []
    let wR := wRs.headD []
    let (st1, ds) := emitDiffs st p addr (M j) (List.finRange n)
    let (st2, outj) := compressAll st1 p (mergeCols b ds wL wR)
    let (st3, outs) := buildBranches M addr b p st2 js wLs.tail wRs.tail
    (st3, outj :: outs)

def buildNode {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) (b : ℕ) :
    ℕ → List Bool → CState (Bool × Fin n) →
      CState (Bool × Fin n) × List (List (Option ((Bool × Fin n) ⊕ ℕ)))
  | 0, _, st => (st, List.replicate r [])
  | d + 1, p, st =>
    let oL := occ addr (p ++ [false])
    let oR := occ addr (p ++ [true])
    if oL && oR then
      let (st1, wL) := buildNode M addr b d (p ++ [false]) st
      let (st2, wR) := buildNode M addr b d (p ++ [true]) st1
      buildBranches M addr b p st2 (List.finRange r) wL wR
    else if oL then
      buildNode M addr b d (p ++ [false]) st
    else if oR then
      buildNode M addr b d (p ++ [true]) st
    else
      (st, List.replicate r [])

lemma emitDiffs_spec {n : ℕ} (x : (Bool × Fin n) → Bool)
    (addr : (Bool × Fin n) → List Bool) (perm : Equiv.Perm (Fin n)) (p : List Bool) :
    ∀ (is : List (Fin n)) {st : CState (Bool × Fin n)}, CInv st →
      let res := emitDiffs st p addr perm is
      CInv res.1 ∧ st.len ≤ res.1.len ∧
      res.1.len - st.len = is.countP (fun i => decide (lcp (addr (false, i)) (addr (true, perm i)) = p)) ∧
      res.2.length = is.countP (fun i => decide (lcp (addr (false, i)) (addr (true, perm i)) = p)) ∧
      (∀ w ∈ res.2, WireValid res.1.len w) ∧
      NodesIn st res.1 p ∧
      sumBits (Sum.elim x (evalRev x res.1.rev)) res.2 =
        (is.map (fun i => if lcp (addr (false, i)) (addr (true, perm i)) = p then
          (decide (x (false, i) ≠ x (true, perm i))).toNat else 0)).sum
  | [], st, h => ⟨h, le_rfl, by simp [emitDiffs], by simp [emitDiffs],
      fun _ hw => by simp [emitDiffs] at hw, nodesIn_refl _ _, by simp [emitDiffs, sumBits]⟩
  | i :: rest, st, h => by
    have hrec := emitDiffs_spec x addr perm p rest h
    rcases hrec with ⟨h1_inv, h1_le, h1_sub, h1_len, h1_w, h1_nod, h1_sum⟩
    dsimp only [emitDiffs]
    split_ifs with hlcp
    · have hxo := emitXor_spec x h1_inv p (a := Sum.inl (false, i)) (b := Sum.inl (true, perm i)) trivial trivial
      rcases hxo with ⟨h2_inv, h2_le, h2_sub, h2_w, h2_nod, h2_eq⟩
      refine ⟨h2_inv, le_trans h1_le h2_le, ?_, ?_, ?_, nodesIn_trans h1_nod h2_nod, ?_⟩
      · simp [hlcp]; omega
      · simp [hlcp]; omega
      · intro w hw
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact h2_w
        · exact wireValid_mono h2_le (h1_w w hw)
      · have hds_eq := sumBits_nodesIn x h2_inv h1_inv h2_nod h1_w
        simp only [sumBits, List.map_cons, List.sum_cons, bitVal] at hds_eq ⊢
        rw [h2_eq]
        simp only [Sum.elim_inl]
        have hsum_eq : (List.map (bitVal (Sum.elim x (evalRev x (emitXor (emitDiffs st p addr perm rest).1 p (Sum.inl (false, i)) (Sum.inl (true, perm i))).1.rev))) (emitDiffs st p addr perm rest).2).sum =
            (List.map (bitVal (Sum.elim x (evalRev x (emitDiffs st p addr perm rest).1.rev))) (emitDiffs st p addr perm rest).2).sum := by
          simpa [sumBits] using hds_eq
        rw [hsum_eq]
        simp only [sumBits] at h1_sum
        rw [h1_sum, hlcp, if_pos rfl]
        cases x (false, i) <;> cases x (true, perm i) <;> simp <;> omega
    · refine ⟨h1_inv, h1_le, by simp [hlcp]; omega,
        by simp [hlcp]; omega, h1_w, h1_nod, ?_⟩
      simp [hlcp, h1_sum]

lemma mergePairCols_spec {V : Type} (val : V ⊕ ℕ → Bool) :
    ∀ (b : ℕ) (wL wR : List (Option (V ⊕ ℕ))),
      wL.length ≤ b → wR.length ≤ b →
      (mergePairCols b wL wR).length = b ∧
      ((mergePairCols b wL wR).map List.length).sum ≤ wL.length + wR.length ∧
      (∀ col ∈ mergePairCols b wL wR, ∀ w ∈ col,
        (∃ o ∈ wL, o = some w) ∨ (∃ o ∈ wR, o = some w)) ∧
      sumCols val (mergePairCols b wL wR) = sumOptBits val wL + sumOptBits val wR
  | 0, wL, wR, hL, hR => by
    have hL0 : wL = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hR0 : wR = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hL0; subst hR0
    simp [mergePairCols, sumCols, sumOptBits]
  | k + 1, wL, wR, hL, hR => by
    have hrec := mergePairCols_spec val k wL.tail wR.tail (by cases wL <;> simp at hL ⊢ <;> omega)
      (by cases wR <;> simp at hR ⊢ <;> omega)
    rcases hrec with ⟨hlen, hpot, hmem, hsum⟩
    refine ⟨by simp [mergePairCols, hlen], ?_, ?_, ?_⟩
    · cases wL with
      | nil => cases wR with
        | nil => simp [mergePairCols] at hpot ⊢; omega
        | cons r rs => cases r <;> simp [mergePairCols, optToList] at hpot ⊢ <;> omega
      | cons l ls => cases wR with
        | nil => cases l <;> simp [mergePairCols, optToList] at hpot ⊢ <;> omega
        | cons r rs => cases l <;> cases r <;> simp [mergePairCols, optToList] at hpot ⊢ <;> omega
    · intro col hcol w hw
      simp only [mergePairCols, List.mem_cons] at hcol
      rcases hcol with rfl | hcol
      · rcases List.mem_append.mp hw with hw | hw
        · cases wL with | nil => simp at hw | cons l ls => cases l <;> simp [optToList] at hw; subst hw; exact Or.inl ⟨some w, by simp, rfl⟩
        · cases wR with | nil => simp at hw | cons r rs => cases r <;> simp [optToList] at hw; subst hw; exact Or.inr ⟨some w, by simp, rfl⟩
      · rcases hmem col hcol w hw with ⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩
        · exact Or.inl ⟨some w, List.mem_of_mem_tail ho, rfl⟩
        · exact Or.inr ⟨some w, List.mem_of_mem_tail ho, rfl⟩
    · cases wL with
      | nil => cases wR with
        | nil => simp [mergePairCols, sumCols, sumOptBits, sumBits] at hsum ⊢; omega
        | cons r rs => cases r <;> simp [mergePairCols, optToList, sumCols, sumOptBits, optBitVal, sumBits] at hsum ⊢ <;> omega
      | cons l ls => cases wR with
        | nil => cases l <;> simp [mergePairCols, optToList, sumCols, sumOptBits, optBitVal, sumBits] at hsum ⊢ <;> omega
        | cons r rs => cases l <;> cases r <;> simp [mergePairCols, optToList, sumCols, sumOptBits, optBitVal, sumBits] at hsum ⊢ <;> omega

lemma mergeCols_spec {V : Type} (val : V ⊕ ℕ → Bool) {b : ℕ} (hb : 0 < b)
    (ds : List (V ⊕ ℕ)) (wL wR : List (Option (V ⊕ ℕ)))
    (hL : wL.length ≤ b) (hR : wR.length ≤ b) :
    (mergeCols b ds wL wR).length = b ∧
    ((mergeCols b ds wL wR).map List.length).sum ≤ ds.length + wL.length + wR.length ∧
    (∀ col ∈ mergeCols b ds wL wR, ∀ w ∈ col,
      w ∈ ds ∨ (∃ o ∈ wL, o = some w) ∨ (∃ o ∈ wR, o = some w)) ∧
    sumCols val (mergeCols b ds wL wR) = sumBits val ds + sumOptBits val wL + sumOptBits val wR := by
  have hm := mergePairCols_spec val b wL wR hL hR
  rcases hm with ⟨hlen, hpot, hmem, hsum⟩
  dsimp [mergeCols]
  cases hmp : mergePairCols b wL wR with
  | nil => simp [hmp] at hlen; omega
  | cons c0 rest =>
    rw [hmp] at hlen hpot hmem hsum
    refine ⟨by simpa using hlen, by simp [List.length_append] at hpot ⊢; omega, ?_, ?_⟩
    · intro col hcol w hw
      simp only [List.mem_cons] at hcol
      rcases hcol with rfl | hcol
      · rcases List.mem_append.mp hw with hw | hw
        · exact Or.inl hw
        · exact Or.inr (hmem c0 (by simp) w hw)
      · exact Or.inr (hmem col (by simp [hcol]) w hw)
    · simp only [sumCols, sumBits_append] at hsum ⊢; omega

def countDiffs {n : ℕ} (addr : (Bool × Fin n) → List Bool) (perm : Equiv.Perm (Fin n)) (p : List Bool) : ℕ :=
  (List.finRange n).countP (fun i => decide (lcp (addr (false, i)) (addr (true, perm i)) = p))

def trueDiffs {n : ℕ} (x : (Bool × Fin n) → Bool) (addr : (Bool × Fin n) → List Bool)
    (perm : Equiv.Perm (Fin n)) (p : List Bool) : ℕ :=
  ((List.finRange n).map (fun i => if lcp (addr (false, i)) (addr (true, perm i)) = p then
    (decide (x (false, i) ≠ x (true, perm i))).toNat else 0)).sum

lemma buildBranches_spec {n r : ℕ} (x : (Bool × Fin n) → Bool) (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) {b : ℕ} (hb : 0 < b) (p : List Bool) :
    ∀ (js : List (Fin r)) (wLs wRs : List (List (Option ((Bool × Fin n) ⊕ ℕ))))
      {st : CState (Bool × Fin n)}, CInv st →
      wLs.length = js.length → wRs.length = js.length →
      (∀ wL ∈ wLs, wL.length ≤ b ∧ ∀ o ∈ wL, ∀ w, o = some w → WireValid st.len w) →
      (∀ wR ∈ wRs, wR.length ≤ b ∧ ∀ o ∈ wR, ∀ w, o = some w → WireValid st.len w) →
      let res := buildBranches M addr b p st js wLs wRs
      CInv res.1 ∧ st.len ≤ res.1.len ∧
      res.1.len - st.len ≤ 12 * js.length * b + 6 * (js.map (fun j => countDiffs addr (M j) p)).sum ∧
      NodesIn st res.1 p ∧
      res.2.length = js.length ∧
      (∀ out ∈ res.2, out.length = b ∧ ∀ o ∈ out, ∀ w, o = some w → WireValid res.1.len w) ∧
      ∀ (k : ℕ) (hk : k < js.length), ∃ q : ℕ,
        sumOptBits (Sum.elim x (evalRev x res.1.rev)) (res.2[k]?.getD []) + q * 2 ^ b =
          sumOptBits (Sum.elim x (evalRev x st.rev)) (wLs[k]?.getD []) +
          sumOptBits (Sum.elim x (evalRev x st.rev)) (wRs[k]?.getD []) +
          trueDiffs x addr (M (js[k])) p
  | [], wLs, wRs, st, h, _, _, _, _ => by
    refine ⟨h, le_rfl, by simp [buildBranches], nodesIn_refl _ _, by simp [buildBranches],
      fun _ ho => by simp [buildBranches] at ho, fun k hk => by simp at hk⟩
  | j :: js, wL :: wLs, wR :: wRs, st, h, hlenL, hlenR, hwL, hwR => by
    have hwL0 := hwL wL (by simp)
    have hwR0 := hwR wR (by simp)
    have hd := emitDiffs_spec x addr (M j) p (List.finRange n) h
    rcases hd with ⟨h1_inv, h1_le, h1_sub, h1_len, h1_w, h1_nod, h1_sum⟩
    set st1 := (emitDiffs st p addr (M j) (List.finRange n)).1
    set ds := (emitDiffs st p addr (M j) (List.finRange n)).2
    have hm := mergeCols_spec (Sum.elim x (evalRev x st1.rev)) hb ds wL wR (by omega) (by omega)
    rcases hm with ⟨hm_len, hm_pot, hm_mem, hm_sum⟩
    have hm_w : ∀ col ∈ mergeCols b ds wL wR, ∀ w ∈ col, WireValid st1.len w := by
      intro col hcol w hw
      rcases hm_mem col hcol w hw with hw | ⟨_, ho, rfl⟩ | ⟨_, ho, rfl⟩
      · exact h1_w w hw
      · exact wireValid_mono h1_le (hwL0.2 (some w) ho w rfl)
      · exact wireValid_mono h1_le (hwR0.2 (some w) ho w rfl)
    have hc := compressAll_spec x (mergeCols b ds wL wR) h1_inv p hm_w
    rcases hc with ⟨h2_inv, h2_le, h2_bnd, h2_len, h2_w, h2_nod, q0, hq0⟩
    set st2 := (compressAll st1 p (mergeCols b ds wL wR)).1
    set outj := (compressAll st1 p (mergeCols b ds wL wR)).2
    have hrec := buildBranches_spec x M addr hb p js wLs wRs h2_inv
      (by simp at hlenL; omega) (by simp at hlenR; omega)
      (fun wL' hwL' => ⟨(hwL wL' (by simp [hwL'])).1,
        fun o ho w hw => wireValid_mono (le_trans h1_le h2_le) ((hwL wL' (by simp [hwL'])).2 o ho w hw)⟩)
      (fun wR' hwR' => ⟨(hwR wR' (by simp [hwR'])).1,
        fun o ho w hw => wireValid_mono (le_trans h1_le h2_le) ((hwR wR' (by simp [hwR'])).2 o ho w hw)⟩)
    rcases hrec with ⟨h3_inv, h3_le, h3_bnd, h3_nod, h3_len, h3_w, h3_val⟩
    refine ⟨h3_inv, le_trans h1_le (le_trans h2_le h3_le), ?_,
      nodesIn_trans h1_nod (nodesIn_trans h2_nod h3_nod), ?_, ?_, ?_⟩
    · simp only [buildBranches, List.headD_cons, List.tail_cons, List.length_cons,
        List.map_cons, List.sum_cons] at h3_bnd ⊢
      have hsub12 : st2.len - st.len ≤ 12 * b + 6 * countDiffs addr (M j) p := by
        dsimp only [countDiffs] at h1_sub h1_len ⊢
        omega
      have h12 : 12 * (js.length + 1) * b = 12 * js.length * b + 12 * b := by ring
      dsimp only [st2, st1, ds] at hsub12 h3_bnd ⊢
      omega
    · simp only [buildBranches, List.headD_cons, List.tail_cons, List.length_cons]
      exact congrArg (· + 1) h3_len
    · intro out hout
      simp only [buildBranches, List.headD_cons, List.tail_cons, List.mem_cons] at hout
      rcases hout with rfl | hout
      · refine ⟨?_, fun o ho w hw => wireValid_mono h3_le (h2_w o ho w hw)⟩
        dsimp only [outj, st2, st1, ds] at h2_len hm_len ⊢; omega
      · exact h3_w out hout
    · intro k hk
      cases k with
      | zero =>
        refine ⟨q0, ?_⟩
        simp only [buildBranches, List.headD_cons, List.tail_cons, List.getElem?_cons_zero, Option.getD_some]
        have houtj_eq := sumOptBits_nodesIn x h3_inv h2_inv h3_nod h2_w
        have hwL_eq := sumOptBits_nodesIn x h1_inv h h1_nod hwL0.2
        have hwR_eq := sumOptBits_nodesIn x h1_inv h h1_nod hwR0.2
        rw [houtj_eq]
        dsimp only [st2, outj] at hq0
        rw [hm_len] at hq0
        rw [hq0, hm_sum, h1_sum, hwL_eq, hwR_eq]
        simp only [List.getElem_cons_zero, trueDiffs]
        omega
      | succ k' =>
        simp only [List.length_cons] at hk
        rcases h3_val k' (by omega) with ⟨qk, hqk⟩
        refine ⟨qk, ?_⟩
        simp only [buildBranches, List.headD_cons, List.tail_cons, List.getElem?_cons_succ]
        have hlenL' : k' < wLs.length := by simp at hlenL; omega
        have hlenR' : k' < wRs.length := by simp at hlenR; omega
        have hwL_eq := sumOptBits_nodesIn x h2_inv h (nodesIn_trans h1_nod h2_nod)
          (hwL (wLs[k']'hlenL') (List.mem_cons_of_mem _ (List.getElem_mem hlenL'))).2
        have hwR_eq := sumOptBits_nodesIn x h2_inv h (nodesIn_trans h1_nod h2_nod)
          (hwR (wRs[k']'hlenR') (List.mem_cons_of_mem _ (List.getElem_mem hlenR'))).2
        simp only [List.getElem?_eq_getElem hlenL', List.getElem?_eq_getElem hlenR', Option.getD_some] at hqk ⊢
        dsimp only [st2, st1, ds, outj] at hqk hwL_eq hwR_eq ⊢
        rw [hqk, hwL_eq, hwR_eq]
        rfl
  | _ :: _, [], _, _, _, hlenL, _, _, _ => by simp at hlenL
  | _ :: _, _, [], _, _, _, hlenR, _, _ => by simp at hlenR

def leavesIn {V : Type} [Fintype V] (addr : V → List Bool) (p : List Bool) : ℕ :=
  (Finset.univ.filter (fun v : V => List.IsPrefix p (addr v))).card

lemma occ_iff_pos_leavesIn {V : Type} [Fintype V] (addr : V → List Bool) (p : List Bool) :
    occ addr p = true ↔ 0 < leavesIn addr p := by
  simp [occ, leavesIn, Finset.card_pos, Finset.Nonempty]

lemma isPrefix_append_bool {p u : List Bool} (hp : List.IsPrefix p u) (hlt : p.length < u.length) :
    List.IsPrefix (p ++ [false]) u ∨ List.IsPrefix (p ++ [true]) u := by
  rcases hp with ⟨t, rfl⟩
  cases t with
  | nil => simp at hlt
  | cons b bs =>
    cases b
    · exact Or.inl ⟨bs, by simp⟩
    · exact Or.inr ⟨bs, by simp⟩

lemma not_isPrefix_both {p u : List Bool} :
    ¬ (List.IsPrefix (p ++ [false]) u ∧ List.IsPrefix (p ++ [true]) u) := by
  rintro ⟨⟨t1, h1⟩, ⟨t2, h2⟩⟩
  have h := h1.trans h2.symm
  simp only [List.append_assoc, List.append_cancel_left_eq, List.cons_append, List.nil_append,
    List.cons.injEq, Bool.false_eq_true, false_and] at h

lemma leavesIn_split {V : Type} [Fintype V] [DecidableEq V] (addr : V → List Bool) {h : ℕ}
    (hlen : ∀ v, (addr v).length = h) {p : List Bool} (hp : p.length < h) :
    leavesIn addr p = leavesIn addr (p ++ [false]) + leavesIn addr (p ++ [true]) := by
  simp only [leavesIn]
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext v
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hpref
      exact isPrefix_append_bool hpref (by rw [hlen v]; exact hp)
    · rintro (h0 | h1)
      · exact List.IsPrefix.trans ⟨[false], rfl⟩ h0
      · exact List.IsPrefix.trans ⟨[true], rfl⟩ h1
  · rw [Finset.disjoint_left]
    intro v h0 h1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h0 h1
    exact not_isPrefix_both ⟨h0, h1⟩

def subtreeCountDiffs {n : ℕ} (addr : (Bool × Fin n) → List Bool)
    (perm : Equiv.Perm (Fin n)) (p : List Bool) : ℕ :=
  (List.finRange n).countP
    (fun i => decide (List.IsPrefix p (lcp (addr (false, i)) (addr (true, perm i)))))

def subtreeTrueDiffs {n : ℕ} (x : (Bool × Fin n) → Bool) (addr : (Bool × Fin n) → List Bool)
    (perm : Equiv.Perm (Fin n)) (p : List Bool) : ℕ :=
  ((List.finRange n).map (fun i =>
    if List.IsPrefix p (lcp (addr (false, i)) (addr (true, perm i))) then
      (decide (x (false, i) ≠ x (true, perm i))).toNat
    else 0)).sum

lemma isPrefix_lcp_cases {u v p : List Bool} (hp : List.IsPrefix p (lcp u v)) :
    lcp u v = p ∨ List.IsPrefix (p ++ [false]) (lcp u v) ∨ List.IsPrefix (p ++ [true]) (lcp u v) := by
  by_cases hlen : p.length < (lcp u v).length
  · exact Or.inr (isPrefix_append_bool hp hlen)
  · left
    rcases hp with ⟨t, ht⟩
    have ht0 : t = [] := List.eq_nil_of_length_eq_zero (by have := congrArg List.length ht; simp at this; omega)
    subst ht0; simpa using ht.symm

lemma occ_false_of_lcp {n : ℕ} (addr : (Bool × Fin n) → List Bool)
    (perm : Equiv.Perm (Fin n)) (i : Fin n) {p : List Bool}
    (h_inj : Function.Injective addr) (h_len : ∀ v, (addr v).length = h) :
    lcp (addr (false, i)) (addr (true, perm i)) = p →
      occ addr (p ++ [false]) = true ∧ occ addr (p ++ [true]) = true := by
  intro hlcp
  have hne : addr (false, i) ≠ addr (true, perm i) := fun h => by
    have := h_inj h; simp at this
  rcases lcp_lt_of_ne (by rw [h_len, h_len]) hne with ⟨_, d, hd1, hd2⟩
  rw [hlcp] at hd1 hd2
  cases d
  · exact ⟨(occ_iff_pos_leavesIn _ _).mpr (Finset.card_pos.mpr ⟨(false, i), by simpa using hd1⟩),
      (occ_iff_pos_leavesIn _ _).mpr (Finset.card_pos.mpr ⟨(true, perm i), by simpa using hd2⟩)⟩
  · exact ⟨(occ_iff_pos_leavesIn _ _).mpr (Finset.card_pos.mpr ⟨(true, perm i), by simpa using hd2⟩),
      (occ_iff_pos_leavesIn _ _).mpr (Finset.card_pos.mpr ⟨(false, i), by simpa using hd1⟩)⟩

lemma subtreeCountDiffs_nil {n h : ℕ} (addr : (Bool × Fin n) → List Bool)
    (perm : Equiv.Perm (Fin n)) {p : List Bool}
    (h_inj : Function.Injective addr) (h_len : ∀ v, (addr v).length = h) (hp : p.length = h) :
    subtreeCountDiffs addr perm p = 0 := by
  simp only [subtreeCountDiffs, List.countP_eq_zero, List.mem_finRange, decide_eq_true_eq]
  intro i _ hpref
  have hne : addr (false, i) ≠ addr (true, perm i) := fun h => by have := h_inj h; simp at this
  have hlt := (lcp_lt_of_ne (by rw [h_len, h_len]) hne).1
  have hle := hpref.length_le
  rw [h_len] at hlt
  omega

lemma subtreeTrueDiffs_nil {n h : ℕ} (x : (Bool × Fin n) → Bool) (addr : (Bool × Fin n) → List Bool)
    (perm : Equiv.Perm (Fin n)) {p : List Bool}
    (h_inj : Function.Injective addr) (h_len : ∀ v, (addr v).length = h) (hp : p.length = h) :
    subtreeTrueDiffs x addr perm p = 0 := by
  simp only [subtreeTrueDiffs, List.sum_eq_zero_iff, List.mem_map, List.mem_finRange, true_and]
  rintro _ ⟨i, rfl⟩
  have hne : addr (false, i) ≠ addr (true, perm i) := fun h => by have := h_inj h; simp at this
  have hlt := (lcp_lt_of_ne (by rw [h_len, h_len]) hne).1
  rw [h_len] at hlt
  rw [if_neg (fun hpref => absurd hlt (not_lt_of_ge (by have := hpref.length_le; omega)))]

lemma countP_split_three {α : Type*} (l : List α) (P Q R : α → Bool)
    (h1 : ∀ a ∈ l, P a = true → Q a = false ∧ R a = false)
    (h2 : ∀ a ∈ l, Q a = true → R a = false) :
    l.countP (fun a => P a || Q a || R a) = l.countP P + l.countP Q + l.countP R := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.countP_cons]
    have ha1 := h1 a (by simp)
    have ha2 := h2 a (by simp)
    have hrec := ih (fun x hx => h1 x (by simp [hx])) (fun x hx => h2 x (by simp [hx]))
    cases hP : P a <;> cases hQ : Q a <;> cases hR : R a <;> simp_all <;> omega

lemma sum_split_three {α : Type*} (l : List α) (f : α → ℕ) (P Q R : α → Prop)
    [DecidablePred P] [DecidablePred Q] [DecidablePred R]
    (hPQ : ∀ a ∈ l, ¬ (P a ∧ Q a)) (hPR : ∀ a ∈ l, ¬ (P a ∧ R a)) (hQR : ∀ a ∈ l, ¬ (Q a ∧ R a)) :
    (l.map (fun a => if (P a ∨ Q a ∨ R a) then f a else 0)).sum =
      (l.map (fun a => if P a then f a else 0)).sum +
      (l.map (fun a => if Q a then f a else 0)).sum +
      (l.map (fun a => if R a then f a else 0)).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    have hrec := ih (fun x hx => hPQ x (by simp [hx])) (fun x hx => hPR x (by simp [hx]))
      (fun x hx => hQR x (by simp [hx]))
    rcases em (P a) with hP | hP <;> rcases em (Q a) with hQ | hQ <;> rcases em (R a) with hR | hR <;>
      simp_all <;> omega

lemma subtreeCountDiffs_split {n : ℕ} (addr : (Bool × Fin n) → List Bool)
    (perm : Equiv.Perm (Fin n)) (p : List Bool) :
    subtreeCountDiffs addr perm p =
      countDiffs addr perm p + subtreeCountDiffs addr perm (p ++ [false]) +
      subtreeCountDiffs addr perm (p ++ [true]) := by
  simp only [subtreeCountDiffs, countDiffs]
  have h_eq : (fun i : Fin n => decide (List.IsPrefix p (lcp (addr (false, i)) (addr (true, perm i))))) =
      (fun i : Fin n =>
        decide (lcp (addr (false, i)) (addr (true, perm i)) = p) ||
        decide (List.IsPrefix (p ++ [false]) (lcp (addr (false, i)) (addr (true, perm i)))) ||
        decide (List.IsPrefix (p ++ [true]) (lcp (addr (false, i)) (addr (true, perm i))))) := by
    ext i
    by_cases h0 : lcp (addr (false, i)) (addr (true, perm i)) = p <;>
    by_cases h1 : List.IsPrefix (p ++ [false]) (lcp (addr (false, i)) (addr (true, perm i))) <;>
    by_cases h2 : List.IsPrefix (p ++ [true]) (lcp (addr (false, i)) (addr (true, perm i))) <;>
    simp [h0, h1, h2]
    all_goals
      first
      | exact List.IsPrefix.trans ⟨[false], rfl⟩ h1
      | exact List.IsPrefix.trans ⟨[true], rfl⟩ h2
      | (intro hp; rcases isPrefix_lcp_cases hp with ha | hb | hc <;> contradiction)
  rw [h_eq]
  apply countP_split_three
  · intro i _ h0
    simp only [decide_eq_true_eq] at h0
    simp only [decide_eq_false_iff_not, h0]
    exact ⟨fun h1 => by have := h1.length_le; simp at this, fun h2 => by have := h2.length_le; simp at this⟩
  · intro i _ h0
    simp only [decide_eq_true_eq] at h0
    simp only [decide_eq_false_iff_not]
    intro h1; exact not_isPrefix_both ⟨h0, h1⟩

lemma subtreeTrueDiffs_split {n : ℕ} (x : (Bool × Fin n) → Bool) (addr : (Bool × Fin n) → List Bool)
    (perm : Equiv.Perm (Fin n)) (p : List Bool) :
    subtreeTrueDiffs x addr perm p =
      trueDiffs x addr perm p + subtreeTrueDiffs x addr perm (p ++ [false]) +
      subtreeTrueDiffs x addr perm (p ++ [true]) := by
  simp only [subtreeTrueDiffs, trueDiffs]
  have h_eq : (fun i : Fin n =>
      if List.IsPrefix p (lcp (addr (false, i)) (addr (true, perm i))) then
        (decide (x (false, i) ≠ x (true, perm i))).toNat
      else 0) =
      (fun i : Fin n =>
      if (lcp (addr (false, i)) (addr (true, perm i)) = p ∨
          List.IsPrefix (p ++ [false]) (lcp (addr (false, i)) (addr (true, perm i))) ∨
          List.IsPrefix (p ++ [true]) (lcp (addr (false, i)) (addr (true, perm i)))) then
        (decide (x (false, i) ≠ x (true, perm i))).toNat
      else 0) := by
    ext i; congr 1; apply propext
    constructor
    · intro hp; rcases isPrefix_lcp_cases hp with h0 | h1 | h2 <;> simp [*]
    · rintro (h0 | h1 | h2)
      · simp [h0]
      · exact List.IsPrefix.trans ⟨[false], rfl⟩ h1
      · exact List.IsPrefix.trans ⟨[true], rfl⟩ h2
  rw [h_eq]
  apply sum_split_three
  · rintro i _ ⟨h0, h1⟩; have := h1.length_le; rw [h0] at this; simp at this
  · rintro i _ ⟨h0, h1⟩; have := h1.length_le; rw [h0] at this; simp at this
  · rintro i _ ⟨h0, h1⟩; exact not_isPrefix_both ⟨h0, h1⟩

lemma countDiffs_zero_of_occ_false {n h : ℕ} (addr : (Bool × Fin n) → List Bool)
    (perm : Equiv.Perm (Fin n)) {p : List Bool}
    (h_inj : Function.Injective addr) (h_len : ∀ v, (addr v).length = h)
    (hocc : occ addr (p ++ [false]) = false ∨ occ addr (p ++ [true]) = false) :
    countDiffs addr perm p = 0 ∧
    (∀ x, trueDiffs x addr perm p = 0) := by
  have hno : ∀ i : Fin n, lcp (addr (false, i)) (addr (true, perm i)) ≠ p := by
    intro i hlcp
    have hboth := occ_false_of_lcp addr perm i h_inj h_len hlcp
    rcases hocc with hf | ht <;> simp_all
  refine ⟨?_, fun x => ?_⟩
  · simp [countDiffs, hno]
  · simp [trueDiffs, hno]

lemma subtree_zero_of_occ_false {n : ℕ} (addr : (Bool × Fin n) → List Bool)
    (perm : Equiv.Perm (Fin n)) {q : List Bool} (hq : occ addr q = false) :
    subtreeCountDiffs addr perm q = 0 ∧ (∀ x, subtreeTrueDiffs x addr perm q = 0) := by
  have hno : ∀ i : Fin n, ¬ List.IsPrefix q (lcp (addr (false, i)) (addr (true, perm i))) := by
    intro i hpref
    have hq' := List.IsPrefix.trans hpref (lcp_isPrefix_left _ _)
    have : occ addr q = true := (occ_iff_pos_leavesIn _ _).mpr (Finset.card_pos.mpr ⟨(false, i), by simpa using hq'⟩)
    simp_all
  refine ⟨?_, fun x => ?_⟩
  · simp [subtreeCountDiffs, hno]
  · simp [subtreeTrueDiffs, hno]

lemma list_sum_map_add {α : Type*} (l : List α) (f g : α → ℕ) :
    (l.map (fun a => f a + g a)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]; omega

lemma buildNode_spec {n r h : ℕ} (x : (Bool × Fin n) → Bool) (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) (h_inj : Function.Injective addr)
    (h_len : ∀ v, (addr v).length = h) {b : ℕ} (hb : 0 < b) :
    ∀ (d : ℕ) (p : List Bool), p.length + d = h →
      ∀ {st : CState (Bool × Fin n)}, CInv st →
      let res := buildNode M addr b d p st
      CInv res.1 ∧ st.len ≤ res.1.len ∧
      res.1.len - st.len ≤
        12 * r * b * (leavesIn addr p - 1) +
        6 * ((List.finRange r).map (fun j => subtreeCountDiffs addr (M j) p)).sum ∧
      res.2.length = r ∧
      (∀ out ∈ res.2, out.length ≤ b ∧ ∀ o ∈ out, ∀ w, o = some w → WireValid res.1.len w) ∧
      (2 ≤ leavesIn addr p → ∀ out ∈ res.2, out.length = b) ∧
      (∃ suf, res.1.rev = suf ++ st.rev ∧
        ∀ e ∈ suf, List.IsPrefix p e.node ∧ e.node.length < h ∧ isBranch addr e.node = true) ∧
      (∀ (j : Fin r), ∃ q : ℕ,
        sumOptBits (Sum.elim x (evalRev x res.1.rev)) (res.2[j.1]?.getD []) + q * 2 ^ b =
          subtreeTrueDiffs x addr (M j) p)
  | 0, p, hp, st, hst => by
    have hp_len : p.length = h := by omega
    refine ⟨hst, le_rfl, by simp [buildNode], by simp [buildNode],
      fun out hout => by simp [buildNode, List.mem_replicate] at hout; rcases hout with ⟨_, rfl⟩; simp,
      fun h2 => by
        exfalso
        have hle1 : leavesIn addr p ≤ 1 := by
          rw [leavesIn, Finset.card_le_one]
          intro v1 hv1 v2 hv2
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv1 hv2
          have e1 : addr v1 = p := by
            rcases hv1 with ⟨t, ht⟩
            have : t = [] := List.eq_nil_of_length_eq_zero (by have := congrArg List.length ht; rw [h_len] at this; simp at this; omega)
            subst this; simpa using ht.symm
          have e2 : addr v2 = p := by
            rcases hv2 with ⟨t, ht⟩
            have : t = [] := List.eq_nil_of_length_eq_zero (by have := congrArg List.length ht; rw [h_len] at this; simp at this; omega)
            subst this; simpa using ht.symm
          exact h_inj (e1.trans e2.symm)
        omega,
      ⟨[], rfl, fun _ hmem => by simp at hmem⟩,
      fun j => ⟨0, by
        simp [buildNode, sumOptBits, subtreeTrueDiffs_nil x addr (M j) h_inj h_len hp_len]⟩⟩
  | d + 1, p, hp, st, hst => by
    have hp_lt : p.length < h := by omega
    dsimp only [buildNode]
    by_cases hoL : occ addr (p ++ [false]) = true <;> by_cases hoR : occ addr (p ++ [true]) = true
    · simp only [hoL, hoR, Bool.and_self, ite_true]
      have hL := buildNode_spec x M addr h_inj h_len hb d (p ++ [false]) (by simp; omega) hst
      rcases hL with ⟨h1_inv, h1_le, h1_bnd, h1_len, h1_w, _, ⟨suf1, hsuf1, hnod1⟩, h1_val⟩
      set st1 := (buildNode M addr b d (p ++ [false]) st).1
      set wL := (buildNode M addr b d (p ++ [false]) st).2
      have hR := buildNode_spec x M addr h_inj h_len hb d (p ++ [true]) (by simp; omega) h1_inv
      rcases hR with ⟨h2_inv, h2_le, h2_bnd, h2_len, h2_w, _, ⟨suf2, hsuf2, hnod2⟩, h2_val⟩
      set st2 := (buildNode M addr b d (p ++ [true]) st1).1
      set wR := (buildNode M addr b d (p ++ [true]) st1).2
      have hb_res := buildBranches_spec x M addr hb p (List.finRange r) wL wR h2_inv
        (by simp [h1_len]) (by simp [h2_len])
        (fun wL' hwL' => ⟨(h1_w wL' hwL').1, fun o ho w hw => wireValid_mono h2_le ((h1_w wL' hwL').2 o ho w hw)⟩)
        h2_w
      rcases hb_res with ⟨h3_inv, h3_le, h3_bnd, ⟨suf3, hsuf3, hnod3⟩, h3_len, h3_w, h3_val⟩
      refine ⟨h3_inv, le_trans h1_le (le_trans h2_le h3_le), ?_, by simpa using h3_len,
        fun out hout => ⟨le_of_eq (h3_w out hout).1, (h3_w out hout).2⟩,
        fun _ out hout => (h3_w out hout).1, ?_, ?_⟩
      · have hl_split := leavesIn_split addr h_len hp_lt
        have hposL := (occ_iff_pos_leavesIn addr (p ++ [false])).mp hoL
        have hposR := (occ_iff_pos_leavesIn addr (p ++ [true])).mp hoR
        have hl_eq : (leavesIn addr (p ++ [false]) - 1) + (leavesIn addr (p ++ [true]) - 1) + 1 =
            leavesIn addr p - 1 := by omega
        have hs_split : ((List.finRange r).map (fun j => subtreeCountDiffs addr (M j) p)).sum =
            ((List.finRange r).map (fun j => countDiffs addr (M j) p)).sum +
            ((List.finRange r).map (fun j => subtreeCountDiffs addr (M j) (p ++ [false]))).sum +
            ((List.finRange r).map (fun j => subtreeCountDiffs addr (M j) (p ++ [true]))).sum := by
          simp only [subtreeCountDiffs_split addr _ p]
          rw [list_sum_map_add, list_sum_map_add]
        simp only [List.length_finRange] at h3_bnd
        have h12 : 12 * r * b * (leavesIn addr p - 1) =
            12 * r * b * (leavesIn addr (p ++ [false]) - 1) +
            12 * r * b * (leavesIn addr (p ++ [true]) - 1) + 12 * r * b := by
          rw [← hl_eq]; ring
        dsimp only [st2, st1, wL, wR] at h1_bnd h2_bnd h3_bnd ⊢
        omega
      · refine ⟨suf3 ++ suf2 ++ suf1, by rw [hsuf3, hsuf2, hsuf1, List.append_assoc, List.append_assoc], ?_⟩
        intro e he
        rcases List.mem_append.mp he with he | he
        · rcases List.mem_append.mp he with he | he
          · have heq := hnod3 e he; subst heq
            exact ⟨List.prefix_refl _, hp_lt, by simp [isBranch, hoL, hoR]⟩
          · rcases hnod2 e he with ⟨hp2, hlt2, hb2⟩
            exact ⟨List.IsPrefix.trans ⟨[true], rfl⟩ hp2, hlt2, hb2⟩
        · rcases hnod1 e he with ⟨hp1, hlt1, hb1⟩
          exact ⟨List.IsPrefix.trans ⟨[false], rfl⟩ hp1, hlt1, hb1⟩
      · intro j
        have hj : j.1 < (List.finRange r).length := by simp
        rcases h3_val j.1 hj with ⟨q3, hq3⟩
        rcases h1_val j with ⟨q1, hq1⟩
        rcases h2_val j with ⟨q2, hq2⟩
        have hwL_mem : wL[j.1]?.getD [] ∈ wL ∨ wL[j.1]?.getD [] = [] := by
          by_cases hlt : j.1 < wL.length
          · left; rw [List.getElem?_eq_getElem hlt, Option.getD_some]; exact List.getElem_mem hlt
          · right; rw [List.getElem?_eq_none (by omega), Option.getD_none]
        have hwL_w : ∀ o ∈ wL[j.1]?.getD [], ∀ w, o = some w → WireValid st1.len w := by
          rcases hwL_mem with hmem | heq
          · exact (h1_w _ hmem).2
          · simp [heq]
        have hwL_eq : sumOptBits (Sum.elim x (evalRev x st2.rev)) (wL[j.1]?.getD []) =
            sumOptBits (Sum.elim x (evalRev x st1.rev)) (wL[j.1]?.getD []) := by
          rcases hwL_mem with hmem | heq
          · exact sumOptBits_suffix x h2_inv h1_inv suf2 hsuf2 hwL_w
          · simp [heq, sumOptBits]
        simp only [List.getElem_finRange, Fin.cast_mk, Fin.eta] at hq3
        refine ⟨q3 + q1 + q2, ?_⟩
        rw [subtreeTrueDiffs_split x addr (M j) p]
        dsimp only [st2, st1, wL, wR] at hq3 hq1 hq2 hwL_eq ⊢
        rw [hwL_eq] at hq3
        have h_mul : (q3 + q1 + q2) * 2 ^ b = q3 * 2 ^ b + q1 * 2 ^ b + q2 * 2 ^ b := by ring
        omega
    · have hoR' : occ addr (p ++ [true]) = false := Bool.eq_false_iff.mpr hoR
      simp only [hoL, hoR', Bool.and_false, Bool.false_eq_true, ite_false, ite_true]
      have hL := buildNode_spec x M addr h_inj h_len hb d (p ++ [false]) (by simp; omega) hst
      rcases hL with ⟨h1_inv, h1_le, h1_bnd, h1_len, h1_w, h1_full, ⟨suf1, hsuf1, hnod1⟩, h1_val⟩
      have hl_zero : leavesIn addr (p ++ [true]) = 0 := by
        by_contra hne
        have : occ addr (p ++ [true]) = true := (occ_iff_pos_leavesIn _ _).mpr (Nat.pos_of_ne_zero hne)
        simp_all
      have hl_eq : leavesIn addr p = leavesIn addr (p ++ [false]) := by
        rw [leavesIn_split addr h_len hp_lt, hl_zero, add_zero]
      have hs_eq : ((List.finRange r).map (fun j => subtreeCountDiffs addr (M j) p)).sum =
          ((List.finRange r).map (fun j => subtreeCountDiffs addr (M j) (p ++ [false]))).sum := by
        congr 1; apply List.map_congr_left; intro j _
        rw [subtreeCountDiffs_split addr (M j) p,
          (countDiffs_zero_of_occ_false addr (M j) h_inj h_len (Or.inr hoR')).1,
          (subtree_zero_of_occ_false addr (M j) hoR').1]
        omega
      refine ⟨h1_inv, h1_le, by rw [hl_eq, hs_eq]; exact h1_bnd, h1_len, h1_w,
        fun h2 => h1_full (by rw [← hl_eq]; exact h2),
        ⟨suf1, hsuf1, fun e he => let ⟨hp1, hlt1, hb1⟩ := hnod1 e he;
          ⟨List.IsPrefix.trans ⟨[false], rfl⟩ hp1, hlt1, hb1⟩⟩,
        fun j => by
          rcases h1_val j with ⟨q1, hq1⟩
          refine ⟨q1, ?_⟩
          rw [subtreeTrueDiffs_split x addr (M j) p,
            (countDiffs_zero_of_occ_false addr (M j) h_inj h_len (Or.inr hoR')).2 x,
            (subtree_zero_of_occ_false addr (M j) hoR').2 x]
          omega⟩
    · have hoL' : occ addr (p ++ [false]) = false := Bool.eq_false_iff.mpr hoL
      simp only [hoL', hoR, Bool.false_and, Bool.false_eq_true, ite_false, ite_true]
      have hR := buildNode_spec x M addr h_inj h_len hb d (p ++ [true]) (by simp; omega) hst
      rcases hR with ⟨h1_inv, h1_le, h1_bnd, h1_len, h1_w, h1_full, ⟨suf1, hsuf1, hnod1⟩, h1_val⟩
      have hl_zero : leavesIn addr (p ++ [false]) = 0 := by
        by_contra hne
        have : occ addr (p ++ [false]) = true := (occ_iff_pos_leavesIn _ _).mpr (Nat.pos_of_ne_zero hne)
        simp_all
      have hl_eq : leavesIn addr p = leavesIn addr (p ++ [true]) := by
        rw [leavesIn_split addr h_len hp_lt, hl_zero, zero_add]
      have hs_eq : ((List.finRange r).map (fun j => subtreeCountDiffs addr (M j) p)).sum =
          ((List.finRange r).map (fun j => subtreeCountDiffs addr (M j) (p ++ [true]))).sum := by
        congr 1; apply List.map_congr_left; intro j _
        rw [subtreeCountDiffs_split addr (M j) p,
          (countDiffs_zero_of_occ_false addr (M j) h_inj h_len (Or.inl hoL')).1,
          (subtree_zero_of_occ_false addr (M j) hoL').1]
        omega
      refine ⟨h1_inv, h1_le, by rw [hl_eq, hs_eq]; exact h1_bnd, h1_len, h1_w,
        fun h2 => h1_full (by rw [← hl_eq]; exact h2),
        ⟨suf1, hsuf1, fun e he => let ⟨hp1, hlt1, hb1⟩ := hnod1 e he;
          ⟨List.IsPrefix.trans ⟨[true], rfl⟩ hp1, hlt1, hb1⟩⟩,
        fun j => by
          rcases h1_val j with ⟨q1, hq1⟩
          refine ⟨q1, ?_⟩
          rw [subtreeTrueDiffs_split x addr (M j) p,
            (countDiffs_zero_of_occ_false addr (M j) h_inj h_len (Or.inl hoL')).2 x,
            (subtree_zero_of_occ_false addr (M j) hoL').2 x]
          omega⟩
    · have hoL' : occ addr (p ++ [false]) = false := Bool.eq_false_iff.mpr hoL
      have hoR' : occ addr (p ++ [true]) = false := Bool.eq_false_iff.mpr hoR
      simp only [hoL', hoR', Bool.and_self, Bool.false_eq_true, ite_false]
      have hl_zero : leavesIn addr p = 0 := by
        rw [leavesIn_split addr h_len hp_lt]
        have h0 : leavesIn addr (p ++ [false]) = 0 := by
          by_contra hne; have : occ addr (p ++ [false]) = true := (occ_iff_pos_leavesIn _ _).mpr (Nat.pos_of_ne_zero hne); simp_all
        have h1 : leavesIn addr (p ++ [true]) = 0 := by
          by_contra hne; have : occ addr (p ++ [true]) = true := (occ_iff_pos_leavesIn _ _).mpr (Nat.pos_of_ne_zero hne); simp_all
        omega
      refine ⟨hst, le_rfl, by simp, by simp,
        fun out hout => by simp [List.mem_replicate] at hout; rcases hout with ⟨_, rfl⟩; simp,
        fun h2 => by omega, ⟨[], rfl, fun _ hmem => by simp at hmem⟩,
        fun j => ⟨0, by
          simp only [List.getElem?_eq_getElem (by simp : j.1 < (List.replicate r ([] : List (Option (Bool × Fin n ⊕ ℕ)))).length),
            Option.getD_some, List.getElem_replicate, sumOptBits]
          rw [subtreeTrueDiffs_split x addr (M j) p,
            (countDiffs_zero_of_occ_false addr (M j) h_inj h_len (Or.inl hoL')).2 x,
            (subtree_zero_of_occ_false addr (M j) hoL').2 x,
            (subtree_zero_of_occ_false addr (M j) hoR').2 x]
          simp⟩⟩

def emitRootCmps {V : Type} (st : CState V) (lo hi : ℕ) :
    List (List (Option (V ⊕ ℕ))) → CState V × List (V ⊕ ℕ)
  | [] => (st, [])
  | xs :: rest =>
    let (st1, wge) := emitCmpGe st [] xs lo
    let (st2, wle) := emitCmpLe st1 [] xs hi
    let (st3, ws) := emitRootCmps st2 lo hi rest
    (st3, wge :: wle :: ws)

lemma emitRootCmps_spec {V : Type} (x : V → Bool) (lo hi b : ℕ)
    (hlo : lo < 2 ^ b) (hhi : hi < 2 ^ b) :
    ∀ (xss : List (List (Option (V ⊕ ℕ)))) {st : CState V}, CInv st →
      (∀ xs ∈ xss, xs.length = b ∧ ∀ o ∈ xs, ∀ w, o = some w → WireValid st.len w) →
      let res := emitRootCmps st lo hi xss
      CInv res.1 ∧ st.len ≤ res.1.len ∧
      res.1.len - st.len ≤ xss.length * (3 * b + 2) ∧
      (∀ w ∈ res.2, WireValid res.1.len w) ∧
      NodesIn st res.1 [] ∧
      ((∀ w ∈ res.2, Sum.elim x (evalRev x res.1.rev) w = true) ↔
        (∀ xs ∈ xss, lo ≤ sumOptBits (Sum.elim x (evalRev x st.rev)) xs ∧
          sumOptBits (Sum.elim x (evalRev x st.rev)) xs ≤ hi))
  | [], st, h, _ => ⟨h, le_rfl, by simp [emitRootCmps], fun _ hw => by simp [emitRootCmps] at hw,
      nodesIn_refl _ _, by simp [emitRootCmps]⟩
  | xs :: rest, st, h, hxss => by
    have hxs0 := hxss xs (by simp)
    have hge := emitCmpGe_spec x h [] hxs0.2 (hxs0.1 ▸ hlo)
    rcases hge with ⟨h1_inv, h1_le, h1_sub, h1_w, h1_nod, h1_eq⟩
    set st1 := (emitCmpGe st [] xs lo).1
    set wge := (emitCmpGe st [] xs lo).2
    have hle := emitCmpLe_spec x h1_inv []
      (fun o ho w hw => wireValid_mono h1_le (hxs0.2 o ho w hw)) (hxs0.1 ▸ hhi)
    rcases hle with ⟨h2_inv, h2_le, h2_sub, h2_w, h2_nod, h2_eq⟩
    set st2 := (emitCmpLe st1 [] xs hi).1
    set wle := (emitCmpLe st1 [] xs hi).2
    have hrec := emitRootCmps_spec x lo hi b hlo hhi rest h2_inv
      (fun xs' hxs' => ⟨(hxss xs' (by simp [hxs'])).1,
        fun o ho w hw => wireValid_mono (le_trans h1_le h2_le) ((hxss xs' (by simp [hxs'])).2 o ho w hw)⟩)
    rcases hrec with ⟨h3_inv, h3_le, h3_bnd, h3_w, h3_nod, h3_iff⟩
    refine ⟨h3_inv, le_trans h1_le (le_trans h2_le h3_le), ?_, ?_,
      nodesIn_trans h1_nod (nodesIn_trans h2_nod h3_nod), ?_⟩
    · simp only [emitRootCmps, List.length_cons] at h3_bnd ⊢
      dsimp only [st2, st1] at h1_le h2_le h3_le h1_sub h2_sub h3_bnd ⊢
      rw [hxs0.1] at h1_sub h2_sub
      have h_mul : (rest.length + 1) * (3 * b + 2) = rest.length * (3 * b + 2) + (3 * b + 2) := by ring
      omega
    · intro w hw
      simp only [emitRootCmps, List.mem_cons] at hw
      rcases hw with rfl | rfl | hw
      · exact wireValid_mono (le_trans h2_le h3_le) h1_w
      · exact wireValid_mono h3_le h2_w
      · exact h3_w w hw
    · have hwge_eq := evalRev_nodesIn x h3_inv h1_inv (nodesIn_trans h2_nod h3_nod) h1_w
      have hwle_eq := evalRev_nodesIn x h3_inv h2_inv h3_nod h2_w
      have hxs_eq1 := sumOptBits_nodesIn x h1_inv h h1_nod hxs0.2
      have hxs_eq2 := sumOptBits_nodesIn x h2_inv h (nodesIn_trans h1_nod h2_nod) hxs0.2
      have hrest_eq : ∀ xs' ∈ rest,
          sumOptBits (Sum.elim x (evalRev x st2.rev)) xs' =
            sumOptBits (Sum.elim x (evalRev x st.rev)) xs' :=
        fun xs' hxs' => sumOptBits_nodesIn x h2_inv h (nodesIn_trans h1_nod h2_nod)
          (hxss xs' (by simp [hxs'])).2
      simp only [emitRootCmps, List.mem_cons, forall_eq_or_imp]
      rw [hwge_eq, hwle_eq, h1_eq, h2_eq, hxs_eq1, h3_iff]
      simp only [decide_eq_true_eq]
      constructor
      · rintro ⟨hge_val, hle_val, hrest_val⟩
        refine ⟨⟨hge_val, hle_val⟩, fun xs' hxs' => ?_⟩
        have := hrest_val xs' hxs'; rwa [hrest_eq xs' hxs'] at this
      · rintro ⟨hxs_val, hrest_val⟩
        refine ⟨hxs_val.1, hxs_val.2, fun xs' hxs' => ?_⟩
        rw [hrest_eq xs' hxs']
        exact hrest_val xs' hxs'

lemma dist_iff_bounds (D n : ℕ) :
    16 * Nat.dist (2 * D) n ≤ n ↔ (15 * n + 31) / 32 ≤ D ∧ D ≤ (17 * n) / 32 := by
  simp only [Nat.dist]
  omega

lemma subtreeTrueDiffs_root {n : ℕ} (x : (Bool × Fin n) → Bool)
    (addr : (Bool × Fin n) → List Bool) (perm : Equiv.Perm (Fin n)) :
    subtreeTrueDiffs x addr perm [] =
      (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, perm i))).card := by
  simp only [subtreeTrueDiffs, List.nil_prefix, ite_true]
  have h1 : ∀ (l : List (Fin n)) (hl : l.Nodup),
      (l.map (fun i => (decide (x (false, i) ≠ x (true, perm i))).toNat)).sum =
      (l.toFinset.filter (fun i => x (false, i) ≠ x (true, perm i))).card := by
    intro l hl
    induction l with
    | nil => simp
    | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, List.nodup_cons] at hl ⊢
      have ha : a ∉ t.toFinset := by simpa using hl.1
      rw [ih hl.2]
      by_cases hx : x (false, a) ≠ x (true, perm a)
      · have hfilt : (List.toFinset (a :: t)).filter (fun i => x (false, i) ≠ x (true, perm i)) =
            insert a (t.toFinset.filter (fun i => x (false, i) ≠ x (true, perm i))) := by
          ext i; simp only [Finset.mem_filter, List.mem_toFinset, List.mem_cons, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | hi, hxi⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨hi, hxi⟩
          · rintro (rfl | ⟨hi, hxi⟩)
            · exact ⟨Or.inl rfl, hx⟩
            · exact ⟨Or.inr hi, hxi⟩
        rw [hfilt, Finset.card_insert_of_notMem (by simp [ha])]
        simp [hx]; omega
      · have hfilt : (List.toFinset (a :: t)).filter (fun i => x (false, i) ≠ x (true, perm i)) =
            t.toFinset.filter (fun i => x (false, i) ≠ x (true, perm i)) := by
          ext i; simp only [Finset.mem_filter, List.mem_toFinset, List.mem_cons]
          constructor
          · rintro ⟨rfl | hi, hxi⟩
            · exact absurd hxi hx
            · exact ⟨hi, hxi⟩
          · rintro ⟨hi, hxi⟩; exact ⟨Or.inr hi, hxi⟩
        rw [hfilt]
        simp [hx]
  rw [h1 (List.finRange n) (List.nodup_finRange n)]
  congr 1; ext i; simp

def castWire {V : Type} (a : ℕ) (ha : 0 < a) : V ⊕ ℕ → V ⊕ Fin a
  | Sum.inl v => Sum.inl v
  | Sum.inr m => Sum.inr ⟨m % a, Nat.mod_lt m ha⟩

lemma clauseSat_image_castWire {V : Type} [DecidableEq V] (x : V → Bool) {a : ℕ} (ha : 0 < a)
    (y : Fin a → Bool) (c : Clause (V ⊕ ℕ))
    (hc : ∀ l ∈ c, WireValid a l.1) :
    ClauseSat (Sum.elim x y) (c.image (fun l => (castWire a ha l.1, l.2))) ↔
      ClauseSat (Sum.elim x (fun m => if hm : m < a then y ⟨m, hm⟩ else false)) c := by
  simp only [ClauseSat, Finset.mem_image, exists_exists_and_eq_and]
  constructor
  · rintro ⟨l, hl, hsat⟩
    refine ⟨l, hl, ?_⟩
    have hw := hc l hl
    rcases l with ⟨v | m, b⟩
    · simpa [castWire] using hsat
    · have hm : m < a := hw
      simpa [castWire, Nat.mod_eq_of_lt hm, hm] using hsat
  · rintro ⟨l, hl, hsat⟩
    refine ⟨l, hl, ?_⟩
    have hw := hc l hl
    rcases l with ⟨v | m, b⟩
    · simpa [castWire] using hsat
    · have hm : m < a := hw
      simpa [castWire, Nat.mod_eq_of_lt hm, hm] using hsat

lemma ancOf_isPrefix {V : Type} [Fintype V] (addr : V → List Bool) :
    ∀ p : List Bool, List.IsPrefix (ancOf addr p) p
  | [] => by rw [ancOf]
  | a :: as => by
    rw [ancOf]
    split_ifs
    · exact List.dropLast_prefix _
    · exact List.IsPrefix.trans (ancOf_isPrefix addr (a :: as).dropLast) (List.dropLast_prefix _)
termination_by p => p.length
decreasing_by simp

lemma ancOf_isBranch_or_nil {V : Type} [Fintype V] (addr : V → List Bool) :
    ∀ p : List Bool, ancOf addr p = [] ∨ isBranch addr (ancOf addr p) = true
  | [] => by rw [ancOf]; exact Or.inl rfl
  | a :: as => by
    rw [ancOf]
    split_ifs with h
    · exact Or.inr h
    · exact ancOf_isBranch_or_nil addr (a :: as).dropLast
termination_by p => p.length
decreasing_by simp

lemma ancOf_strict_isPrefix {V : Type} [Fintype V] (addr : V → List Bool) :
    ∀ p q : List Bool, List.IsPrefix q p → q ≠ p → isBranch addr q = true →
      List.IsPrefix q (ancOf addr p)
  | [], q, hqp, hne, _ => by
    have : q = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hqp.length_le)
    exact absurd this hne
  | a :: as, q, hqp, hne, hbr => by
    have hq_dl : List.IsPrefix q (a :: as).dropLast := by
      rcases hqp with ⟨t, ht⟩
      cases t with
      | nil => simp at ht; exact absurd ht hne
      | cons b bs =>
        rw [← ht]
        rw [List.dropLast_append_of_ne_nil (by simp)]
        exact List.prefix_append _ _
    rw [ancOf]
    split_ifs with h
    · exact hq_dl
    · by_cases hqeq : q = (a :: as).dropLast
      · subst hqeq; exact absurd hbr (by simp [h])
      · exact ancOf_strict_isPrefix addr (a :: as).dropLast q hq_dl hqeq hbr
termination_by p => p.length
decreasing_by simp

lemma prefix_trichotomy (u p : List Bool) (h : List.IsPrefix u p) :
    p = u ∨ List.IsPrefix (u ++ [false]) p ∨ List.IsPrefix (u ++ [true]) p := by
  rcases h with ⟨t, rfl⟩
  cases t with
  | nil => exact Or.inl (by simp)
  | cons b bs =>
    cases b
    · exact Or.inr (Or.inl ⟨bs, by simp [List.append_assoc]⟩)
    · exact Or.inr (Or.inr ⟨bs, by simp [List.append_assoc]⟩)

lemma lcp_symm : ∀ a b : List Bool, lcp a b = lcp b a
  | [], _ => by simp [lcp]
  | _ :: _, [] => by simp [lcp]
  | a :: as, b :: bs => by
    dsimp [lcp]
    by_cases h : a = b
    · subst h; simp [lcp_symm as bs]
    · have h' : b ≠ a := Ne.symm h
      simp [h, h']

lemma lcp_isPrefix_both : ∀ a b : List Bool, List.IsPrefix (lcp a b) a ∧ List.IsPrefix (lcp a b) b
  | [], _ => by simp [lcp]
  | _ :: _, [] => by simp [lcp]
  | a :: as, b :: bs => by
    dsimp [lcp]
    split_ifs with h
    · subst h
      have ih := lcp_isPrefix_both as bs
      exact ⟨List.cons_prefix_cons.mpr ⟨rfl, ih.1⟩, List.cons_prefix_cons.mpr ⟨rfl, ih.2⟩⟩
    · exact ⟨List.nil_prefix, List.nil_prefix⟩

lemma isPrefix_lcp_iff : ∀ a b c : List Bool,
    List.IsPrefix c (lcp a b) ↔ List.IsPrefix c a ∧ List.IsPrefix c b
  | _, _, [] => by simp
  | [], _, _ :: _ => by simp [lcp]
  | _ :: _, [], _ :: _ => by simp [lcp]
  | a :: as, b :: bs, c :: cs => by
    dsimp [lcp]
    split_ifs with h
    · subst h
      simp only [List.cons_prefix_cons, isPrefix_lcp_iff]
      tauto
    · simp only [List.prefix_nil, List.cons_prefix_cons]
      constructor
      · intro h0; simp at h0
      · rintro ⟨⟨rfl, _⟩, ⟨rfl, _⟩⟩; exact absurd rfl h

lemma lcp_strict_not_prefix {a b z : List Bool} (_hne : a ≠ b)
    (hza : List.IsPrefix z a) (hlcp : List.IsPrefix (lcp a b) z) (hneq : z ≠ lcp a b) :
    ¬ List.IsPrefix z b := by
  intro hzb
  have hle : (lcp a b).length < z.length := by
    have h1 := hlcp.length_le
    rcases hlcp with ⟨t, ht⟩
    cases t with
    | nil => simp at ht; exact absurd ht.symm hneq
    | cons _ _ =>
      have := congrArg List.length ht
      simp only [List.length_append, List.length_cons] at this
      omega
  have h2 := ((isPrefix_lcp_iff a b z).mpr ⟨hza, hzb⟩).length_le
  omega

lemma isBranch_mono_occ {V : Type} [Fintype V] (addr : V → List Bool) {p : List Bool}
    (hbr : isBranch addr p = true) : occ addr p = true := by
  simp only [isBranch, Bool.and_eq_true] at hbr
  simp only [occ, decide_eq_true_eq] at hbr ⊢
  rcases hbr.1 with ⟨v, hv⟩
  exact ⟨v, List.IsPrefix.trans (List.prefix_append _ _) hv⟩

lemma ancOf_pair_eq {V : Type} [Fintype V] (addr : V → List Bool) (u : List Bool) (d : Bool)
    {p1 p2 : List Bool}
    (hp1 : List.IsPrefix (u ++ [d]) p1) (hp2 : List.IsPrefix (u ++ [d]) p2)
    (hbr1 : isBranch addr p1 = true) (hbr2 : isBranch addr p2 = true)
    (ha1 : List.IsPrefix (ancOf addr p1) u) (ha2 : List.IsPrefix (ancOf addr p2) u) :
    p1 = p2 := by
  by_contra hne
  by_cases h12 : List.IsPrefix p1 p2
  · have hanc := ancOf_strict_isPrefix addr p2 p1 h12 hne hbr1
    have hlen := (List.IsPrefix.trans hanc ha2).length_le
    have hlen2 := hp1.length_le
    simp only [List.length_append, List.length_singleton] at hlen2
    omega
  · by_cases h21 : List.IsPrefix p2 p1
    · have hanc := ancOf_strict_isPrefix addr p1 p2 h21 (Ne.symm hne) hbr2
      have hlen := (List.IsPrefix.trans hanc ha1).length_le
      have hlen2 := hp2.length_le
      simp only [List.length_append, List.length_singleton] at hlen2
      omega
    · have hcp : ∀ a b : List Bool, ¬ List.IsPrefix a b → ¬ List.IsPrefix b a →
          ∃ c : List Bool, List.IsPrefix c a ∧ List.IsPrefix c b ∧
          c ≠ a ∧ ∃ e : Bool, List.IsPrefix (c ++ [e]) a ∧ List.IsPrefix (c ++ [!e]) b := by
        intro a b hab hba
        induction a generalizing b with
        | nil => exact absurd List.nil_prefix hab
        | cons x xs ih =>
          cases b with
          | nil => exact absurd List.nil_prefix hba
          | cons y ys =>
            by_cases hxy : x = y
            · subst hxy
              have hab' : ¬ List.IsPrefix xs ys := fun h => hab (List.cons_prefix_cons.mpr ⟨rfl, h⟩)
              have hba' : ¬ List.IsPrefix ys xs := fun h => hba (List.cons_prefix_cons.mpr ⟨rfl, h⟩)
              rcases ih ys hab' hba' with ⟨c, hc1, hc2, hcne, e, he1, he2⟩
              exact ⟨x :: c, List.cons_prefix_cons.mpr ⟨rfl, hc1⟩,
                List.cons_prefix_cons.mpr ⟨rfl, hc2⟩, fun h => hcne (List.cons.inj h).2,
                e, List.cons_prefix_cons.mpr ⟨rfl, he1⟩, List.cons_prefix_cons.mpr ⟨rfl, he2⟩⟩
            · have hy : y = !x := by cases x <;> cases y <;> simp_all
              subst hy
              exact ⟨[], List.nil_prefix, List.nil_prefix, by simp, x,
                List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩,
                List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩⟩
      rcases hcp p1 p2 h12 h21 with ⟨c, hc1, hc2, hcne, e, he1, he2⟩
      have hoc1 : occ addr (c ++ [e]) = true := by
        have ho := isBranch_mono_occ addr hbr1
        simp only [occ, decide_eq_true_eq] at ho ⊢
        rcases ho with ⟨v, hv⟩
        exact ⟨v, List.IsPrefix.trans he1 hv⟩
      have hoc2 : occ addr (c ++ [!e]) = true := by
        have ho := isBranch_mono_occ addr hbr2
        simp only [occ, decide_eq_true_eq] at ho ⊢
        rcases ho with ⟨v, hv⟩
        exact ⟨v, List.IsPrefix.trans he2 hv⟩
      have hbr_c : isBranch addr c = true := by
        simp only [isBranch, Bool.and_eq_true]
        cases e <;> simp_all
      have hanc := ancOf_strict_isPrefix addr p1 c hc1 hcne hbr_c
      have huc : List.IsPrefix (u ++ [d]) c := by
        have hlcp := (isPrefix_lcp_iff p1 p2 (u ++ [d])).mpr ⟨hp1, hp2⟩
        have hc_lcp : List.IsPrefix c (lcp p1 p2) := (isPrefix_lcp_iff p1 p2 c).mpr ⟨hc1, hc2⟩
        have heq_len : (lcp p1 p2).length ≤ c.length := by
          have : ¬ List.IsPrefix (c ++ [e]) (lcp p1 p2) := by
            intro h
            have h' := ((isPrefix_lcp_iff p1 p2 (c ++ [e])).mp h).2
            have : (c ++ [e]).length ≤ p2.length := h'.length_le
            rcases he2 with ⟨t2, ht2⟩
            rcases h' with ⟨t1, ht1⟩
            have hcon : (c ++ [e]) ++ t1 = (c ++ [!e]) ++ t2 := ht1.trans ht2.symm
            simp only [List.append_assoc, List.cons_append, List.nil_append] at hcon
            have hcon' := List.append_cancel_left hcon
            cases e <;> simp at hcon'
          have h1 := (isPrefix_lcp_iff p1 p2 c).mpr ⟨hc1, hc2⟩
          rcases h1 with ⟨t, ht⟩
          cases t with
          | nil => simp at ht; rw [ht]
          | cons b bs =>
            exfalso
            have hbe : b = e := by
              have hle1 : List.IsPrefix (c ++ [b]) (lcp p1 p2) := ⟨bs, by simpa [List.append_assoc] using ht⟩
              have hp1' := List.IsPrefix.trans hle1 (lcp_isPrefix_both p1 p2).1
              rcases he1 with ⟨t1, ht1⟩
              rcases hp1' with ⟨t2, ht2⟩
              have hcon := ht1.trans ht2.symm
              simp only [List.append_assoc, List.cons_append, List.nil_append] at hcon
              exact (List.cons.inj (List.append_cancel_left hcon)).1.symm
            subst hbe
            exact absurd ⟨bs, by simpa [List.append_assoc] using ht⟩ this
        have hsub : ∀ x y z : List Bool, List.IsPrefix x z → List.IsPrefix y z → x.length ≤ y.length →
            List.IsPrefix x y := by
          intro x y z hx hy hxy
          rcases hx with ⟨tx, htx⟩
          rcases hy with ⟨ty, hty⟩
          rw [← htx] at hty
          have := List.append_eq_append_iff.mp hty.symm
          rcases this with ⟨s, hs1, _⟩ | ⟨s, hs1, _⟩
          · exact ⟨s, hs1.symm⟩
          · have h1 := congrArg List.length hs1
            simp only [List.length_append] at h1
            have : s = [] := List.eq_nil_of_length_eq_zero (by omega)
            subst this; simp at hs1; rw [hs1]
        exact hsub (u ++ [d]) c (lcp p1 p2) hlcp hc_lcp (by
          have := hc_lcp.length_le; have := hlcp.length_le; omega)
      have hlen1 := (List.IsPrefix.trans hanc ha1).length_le
      have hlen2 := huc.length_le
      simp only [List.length_append, List.length_singleton] at hlen2
      omega

lemma ancOf_card_le_three {V : Type} [Fintype V] (addr : V → List Bool) (u : List Bool)
    (S : Finset (List Bool))
    (hS_br : ∀ p ∈ S, p = [] ∨ isBranch addr p = true)
    (hS_anc : ∀ p ∈ S, List.IsPrefix (ancOf addr p) u ∧ List.IsPrefix u p) :
    S.card ≤ 3 := by
  let SF := S.filter (fun p => List.IsPrefix (u ++ [false]) p)
  let ST := S.filter (fun p => List.IsPrefix (u ++ [true]) p)
  have hSF : SF.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro p1 hp1 p2 hp2
    simp only [SF, Finset.mem_filter] at hp1 hp2
    have hbr1 : isBranch addr p1 = true := by
      rcases hS_br p1 hp1.1 with rfl | h
      · have := hp1.2.length_le; simp at this
      · exact h
    have hbr2 : isBranch addr p2 = true := by
      rcases hS_br p2 hp2.1 with rfl | h
      · have := hp2.2.length_le; simp at this
      · exact h
    exact ancOf_pair_eq addr u false hp1.2 hp2.2 hbr1 hbr2 (hS_anc p1 hp1.1).1 (hS_anc p2 hp2.1).1
  have hST : ST.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro p1 hp1 p2 hp2
    simp only [ST, Finset.mem_filter] at hp1 hp2
    have hbr1 : isBranch addr p1 = true := by
      rcases hS_br p1 hp1.1 with rfl | h
      · have := hp1.2.length_le; simp at this
      · exact h
    have hbr2 : isBranch addr p2 = true := by
      rcases hS_br p2 hp2.1 with rfl | h
      · have := hp2.2.length_le; simp at this
      · exact h
    exact ancOf_pair_eq addr u true hp1.2 hp2.2 hbr1 hbr2 (hS_anc p1 hp1.1).1 (hS_anc p2 hp2.1).1
  have hsub : S ⊆ insert u (SF ∪ ST) := by
    intro p hp
    rcases prefix_trichotomy u p (hS_anc p hp).2 with rfl | h | h
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, h⟩))
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, h⟩))
  calc S.card ≤ (insert u (SF ∪ ST)).card := Finset.card_le_card hsub
    _ ≤ (SF ∪ ST).card + 1 := Finset.card_insert_le _ _
    _ ≤ SF.card + ST.card + 1 := by grw [Finset.card_union_le]
    _ ≤ 3 := by omega

def partner {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n)) (j : Fin r) : (Bool × Fin n) → (Bool × Fin n)
  | (false, i) => (true, M j i)
  | (true, i) => (false, (M j).symm i)

lemma partner_ne {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n)) (j : Fin r) (v : Bool × Fin n) :
    v ≠ partner M j v := by
  rcases v with ⟨_ | _, i⟩ <;> simp [partner]

def inBagV {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) (u : List Bool) (v : Bool × Fin n) : Bool :=
  decide (List.IsPrefix u (addr v) ∧
    (u = addr v ∨ ∃ j : Fin r, ¬ List.IsPrefix u (addr (partner M j v)) ∨
      u = lcp (addr v) (addr (partner M j v))))

lemma inBagV_running {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) (h_inj : Function.Injective addr)
    (u1 u2 : List Bool) (v : Bool × Fin n)
    (h1 : inBagV M addr u1 v = true) (h2 : inBagV M addr u2 v = true) :
    ∃ b : List Bool, List.IsPrefix b u1 ∧ List.IsPrefix b u2 ∧
      ∀ z : List Bool, List.IsPrefix b z → (List.IsPrefix z u1 ∨ List.IsPrefix z u2) →
        inBagV M addr z v = true := by
  simp only [inBagV, decide_eq_true_eq] at h1 h2 ⊢
  have hprefix_ord : ∀ a b c : List Bool, List.IsPrefix a c → List.IsPrefix b c →
      List.IsPrefix a b ∨ List.IsPrefix b a := by
    intro a b c ha hb
    rcases ha with ⟨ta, hta⟩
    rcases hb with ⟨tb, htb⟩
    rw [← hta] at htb
    rcases List.append_eq_append_iff.mp htb.symm with ⟨s, hs, _⟩ | ⟨s, hs, _⟩
    · exact Or.inl ⟨s, hs.symm⟩
    · exact Or.inr ⟨s, hs.symm⟩
  have prop : ∀ u z : List Bool, List.IsPrefix u z → List.IsPrefix z (addr v) →
      (u = addr v ∨ ∃ j : Fin r, ¬ List.IsPrefix u (addr (partner M j v)) ∨
        u = lcp (addr v) (addr (partner M j v))) →
      (z = addr v ∨ ∃ j : Fin r, ¬ List.IsPrefix z (addr (partner M j v)) ∨
        z = lcp (addr v) (addr (partner M j v))) := by
    intro u z huz hzv hu
    rcases hu with rfl | ⟨j, hj | hj⟩
    · exact Or.inl (List.IsPrefix.eq_of_length hzv (Nat.le_antisymm hzv.length_le huz.length_le))
    · exact Or.inr ⟨j, Or.inl (fun hzp => hj (List.IsPrefix.trans huz hzp))⟩
    · by_cases hzeq : z = lcp (addr v) (addr (partner M j v))
      · exact Or.inr ⟨j, Or.inr hzeq⟩
      · have hne : addr v ≠ addr (partner M j v) :=
          fun h => partner_ne M j v (h_inj h)
        exact Or.inr ⟨j, Or.inl (lcp_strict_not_prefix hne hzv (hj ▸ huz) hzeq)⟩
  rcases hprefix_ord u1 u2 (addr v) h1.1 h2.1 with h12 | h21
  · refine ⟨u1, List.prefix_refl _, h12, fun z hbz hz => ?_⟩
    have hzv : List.IsPrefix z (addr v) := by
      rcases hz with hz | hz
      · exact List.IsPrefix.trans hz h1.1
      · exact List.IsPrefix.trans hz h2.1
    exact ⟨hzv, prop u1 z hbz hzv h1.2⟩
  · refine ⟨u2, h21, List.prefix_refl _, fun z hbz hz => ?_⟩
    have hzv : List.IsPrefix z (addr v) := by
      rcases hz with hz | hz
      · exact List.IsPrefix.trans hz h1.1
      · exact List.IsPrefix.trans hz h2.1
    exact ⟨hzv, prop u2 z hbz hzv h2.2⟩

lemma inBagV_card_le {n r t h : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) (h_inj : Function.Injective addr)
    (h_len : ∀ v, (addr v).length = h)
    (ht : ∀ (p : List Bool) (j : Fin r),
      (Finset.univ.filter (fun i : Fin n =>
        ¬ (List.IsPrefix p (addr (false, i)) ↔ List.IsPrefix p (addr (true, M j i))))).card ≤ t)
    (u : List Bool) :
    (Finset.univ.filter (fun v : Bool × Fin n => inBagV M addr u v = true)).card ≤ 1 + 4 * r * t := by
  let S0 := Finset.univ.filter (fun v : Bool × Fin n => u = addr v)
  let S1 (j : Fin r) := Finset.univ.filter (fun v : Bool × Fin n =>
    List.IsPrefix u (addr v) ∧ ¬ List.IsPrefix u (addr (partner M j v)))
  let S2 (j : Fin r) := Finset.univ.filter (fun v : Bool × Fin n =>
    u = lcp (addr v) (addr (partner M j v)))
  have hS0 : S0.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro v1 hv1 v2 hv2
    simp only [S0, Finset.mem_filter, Finset.mem_univ, true_and] at hv1 hv2
    exact h_inj (hv1.symm.trans hv2)
  have hS1 : ∀ j : Fin r, (S1 j).card ≤ 2 * t := by
    intro j
    let SF := (S1 j).filter (fun v => v.1 = false)
    let ST := (S1 j).filter (fun v => v.1 = true)
    have hSF : SF.card ≤ t := by
      have hinj : Set.InjOn (fun v : Bool × Fin n => v.2) SF := by
        intro ⟨b1, i1⟩ h1 ⟨b2, i2⟩ h2 heq
        simp only [SF, Finset.mem_coe, Finset.mem_filter] at h1 h2
        subst heq; simp only at h1 h2; rw [h1.2, h2.2]
      calc SF.card ≤ (SF.image Prod.snd).card := (Finset.card_image_of_injOn hinj).ge
        _ ≤ (Finset.univ.filter (fun i : Fin n =>
            ¬ (List.IsPrefix u (addr (false, i)) ↔ List.IsPrefix u (addr (true, M j i))))).card := by
          apply Finset.card_le_card
          intro i hi
          simp only [Finset.mem_image, SF, S1, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          rcases hi with ⟨⟨_ | _, i'⟩, ⟨⟨hp1, hp2⟩, hfl⟩, rfl⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            simp only [partner] at hp2
            tauto
          · simp at hfl
        _ ≤ t := ht u j
    have hST : ST.card ≤ t := by
      have hinj : Set.InjOn (fun v : Bool × Fin n => (M j).symm v.2) ST := by
        intro ⟨b1, i1⟩ h1 ⟨b2, i2⟩ h2 heq
        simp only [ST, Finset.mem_coe, Finset.mem_filter] at h1 h2
        have hi := (M j).symm.injective heq
        simp only at hi h1 h2; rw [h1.2, h2.2, hi]
      calc ST.card ≤ (ST.image (fun v => (M j).symm v.2)).card := (Finset.card_image_of_injOn hinj).ge
        _ ≤ (Finset.univ.filter (fun i : Fin n =>
            ¬ (List.IsPrefix u (addr (false, i)) ↔ List.IsPrefix u (addr (true, M j i))))).card := by
          apply Finset.card_le_card
          intro i hi
          simp only [Finset.mem_image, ST, S1, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          rcases hi with ⟨⟨_ | _, i'⟩, ⟨⟨hp1, hp2⟩, htr⟩, rfl⟩
          · simp at htr
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            simp only [partner] at hp1 hp2
            simp only [Equiv.apply_symm_apply]
            tauto
        _ ≤ t := ht u j
    have hun : S1 j ⊆ SF ∪ ST := by
      intro ⟨b, i⟩ hv
      cases b
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hv, rfl⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hv, rfl⟩)
    calc (S1 j).card ≤ (SF ∪ ST).card := Finset.card_le_card hun
      _ ≤ SF.card + ST.card := Finset.card_union_le _ _
      _ ≤ 2 * t := by omega
  have hS2 : ∀ j : Fin r, (S2 j).card ≤ 2 * t := by
    intro j
    let SF := (S2 j).filter (fun v => v.1 = false)
    let ST := (S2 j).filter (fun v => v.1 = true)
    have hlcp_cross : ∀ v : Bool × Fin n, u = lcp (addr v) (addr (partner M j v)) →
        ¬ (List.IsPrefix (u ++ [false]) (addr v) ↔ List.IsPrefix (u ++ [false]) (addr (partner M j v))) := by
      intro v hu
      have hne : addr v ≠ addr (partner M j v) := fun heq => partner_ne M j v (h_inj heq)
      have hlen : (addr v).length = (addr (partner M j v)).length := by rw [h_len, h_len]
      rcases lcp_lt_of_ne hlen hne with ⟨_, d, hd1, hd2⟩
      rw [← hu] at hd1 hd2
      have hdisj : ∀ (a : List Bool), List.IsPrefix (u ++ [true]) a → List.IsPrefix (u ++ [false]) a → False := by
        intro a h1 h2
        rcases h1 with ⟨t1, ht1⟩; rcases h2 with ⟨t2, ht2⟩
        have hcon := ht1.trans ht2.symm
        simp only [List.append_assoc, List.cons_append, List.nil_append] at hcon
        have hcon' := List.append_cancel_left hcon
        simp at hcon'
      cases d
      · intro hiff; exact hdisj (addr (partner M j v)) hd2 (hiff.mp hd1)
      · intro hiff; exact hdisj (addr v) hd1 (hiff.mpr hd2)
    have hSF : SF.card ≤ t := by
      have hinj : Set.InjOn (fun v : Bool × Fin n => v.2) SF := by
        intro ⟨b1, i1⟩ h1 ⟨b2, i2⟩ h2 heq
        simp only [SF, Finset.mem_coe, Finset.mem_filter] at h1 h2
        subst heq; simp only at h1 h2; rw [h1.2, h2.2]
      calc SF.card ≤ (SF.image Prod.snd).card := (Finset.card_image_of_injOn hinj).ge
        _ ≤ (Finset.univ.filter (fun i : Fin n =>
            ¬ (List.IsPrefix (u ++ [false]) (addr (false, i)) ↔
               List.IsPrefix (u ++ [false]) (addr (true, M j i))))).card := by
          apply Finset.card_le_card
          intro i hi
          simp only [Finset.mem_image, SF, S2, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          rcases hi with ⟨⟨_ | _, i'⟩, ⟨hu, hfl⟩, rfl⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlcp_cross (false, i') hu⟩
          · simp at hfl
        _ ≤ t := ht (u ++ [false]) j
    have hST : ST.card ≤ t := by
      have hinj : Set.InjOn (fun v : Bool × Fin n => (M j).symm v.2) ST := by
        intro ⟨b1, i1⟩ h1 ⟨b2, i2⟩ h2 heq
        simp only [ST, Finset.mem_coe, Finset.mem_filter] at h1 h2
        have hi := (M j).symm.injective heq
        simp only at hi h1 h2; rw [h1.2, h2.2, hi]
      calc ST.card ≤ (ST.image (fun v => (M j).symm v.2)).card := (Finset.card_image_of_injOn hinj).ge
        _ ≤ (Finset.univ.filter (fun i : Fin n =>
            ¬ (List.IsPrefix (u ++ [false]) (addr (false, i)) ↔
               List.IsPrefix (u ++ [false]) (addr (true, M j i))))).card := by
          apply Finset.card_le_card
          intro i hi
          simp only [Finset.mem_image, ST, S2, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          rcases hi with ⟨⟨_ | _, i'⟩, ⟨hu, htr⟩, rfl⟩
          · simp at htr
          · have hcr := hlcp_cross (true, i') hu
            simp only [partner] at hcr
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp only [Equiv.apply_symm_apply]; tauto⟩
        _ ≤ t := ht (u ++ [false]) j
    have hun : S2 j ⊆ SF ∪ ST := by
      intro ⟨b, i⟩ hv
      cases b
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hv, rfl⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hv, rfl⟩)
    calc (S2 j).card ≤ (SF ∪ ST).card := Finset.card_le_card hun
      _ ≤ SF.card + ST.card := Finset.card_union_le _ _
      _ ≤ 2 * t := by omega
  have hsub : Finset.univ.filter (fun v : Bool × Fin n => inBagV M addr u v = true) ⊆
      S0 ∪ (Finset.univ.biUnion (fun j : Fin r => S1 j ∪ S2 j)) := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, inBagV, decide_eq_true_eq] at hv
    rcases hv with ⟨huv, rfl | ⟨j, hj | hj⟩⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
        Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, hj⟩)⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
        Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)⟩)
  calc (Finset.univ.filter (fun v : Bool × Fin n => inBagV M addr u v = true)).card
      ≤ (S0 ∪ (Finset.univ.biUnion (fun j : Fin r => S1 j ∪ S2 j))).card := Finset.card_le_card hsub
    _ ≤ S0.card + (Finset.univ.biUnion (fun j : Fin r => S1 j ∪ S2 j)).card := Finset.card_union_le _ _
    _ ≤ 1 + ∑ j : Fin r, (S1 j ∪ S2 j).card := by grw [hS0, Finset.card_biUnion_le]
    _ ≤ 1 + ∑ _j : Fin r, (2 * t + 2 * t) := by
        gcongr with j _
        calc (S1 j ∪ S2 j).card ≤ (S1 j).card + (S2 j).card := Finset.card_union_le _ _
          _ ≤ 2 * t + 2 * t := Nat.add_le_add (hS1 j) (hS2 j)
    _ = 1 + 4 * r * t := by simp [Finset.sum_const, Finset.card_univ]; ring

def countNode {V : Type} (rev : List (GEntry V)) (p : List Bool) : ℕ :=
  (rev.filter (fun e => decide (e.node = p))).length

lemma countNode_empty {V : Type} (p : List Bool) :
    countNode (CState.empty V).rev p = 0 := by
  simp [countNode, CState.empty]

lemma countNode_nodesIn_ne {V : Type} {st1 st2 : CState V} {p q : List Bool}
    (hn : NodesIn st1 st2 p) (hne : p ≠ q) :
    countNode st2.rev q = countNode st1.rev q := by
  rcases hn with ⟨pref, hrev, hnod⟩
  have hnil : pref.filter (fun e => decide (e.node = q)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro e he; simp [hnod e he, hne]
  simp only [countNode, hrev, List.filter_append, hnil, List.length_append, List.length_nil, zero_add]

lemma countNode_nodesIn_le {V : Type} {st1 st2 : CState V} {p : List Bool}
    (hn : NodesIn st1 st2 p) :
    countNode st2.rev p ≤ countNode st1.rev p + (st2.rev.length - st1.rev.length) := by
  rcases hn with ⟨pref, hrev, _⟩
  have hlen : st2.rev.length = pref.length + st1.rev.length := by rw [hrev, List.length_append]
  have hfl : (pref.filter (fun e => decide (e.node = p))).length ≤ pref.length := List.length_filter_le _ _
  simp only [countNode, hrev, List.filter_append, List.length_append]
  omega

lemma nodesIn_node_prop {V : Type} {st1 st2 : CState V} {p : List Bool}
    (hn : NodesIn st1 st2 p) (P : List Bool → Prop)
    (h1 : ∀ e ∈ st1.rev, P e.node) (hp : P p) :
    ∀ e ∈ st2.rev, P e.node := by
  rcases hn with ⟨pref, hrev, hnod⟩
  intro e he
  rw [hrev] at he
  rcases List.mem_append.mp he with h | h
  · rw [hnod e h]; exact hp
  · exact h1 e h

def diffAt {n : ℕ} (addr : (Bool × Fin n) → List Bool) (perm : Equiv.Perm (Fin n))
    (p : List Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => lcp (addr (false, i)) (addr (true, perm i)) = p)).card

lemma diffAt_le_t {n t : ℕ} (addr : (Bool × Fin n) → List Bool)
    (perm : Equiv.Perm (Fin n)) (h_inj : Function.Injective addr)
    (h_len : ∀ v, (addr v).length = h)
    (ht : ∀ p : List Bool, (Finset.univ.filter (fun i : Fin n =>
      ¬ (List.IsPrefix p (addr (false, i)) ↔ List.IsPrefix p (addr (true, perm i))))).card ≤ t)
    (p : List Bool) : diffAt addr perm p ≤ t := by
  calc diffAt addr perm p
      ≤ (Finset.univ.filter (fun i : Fin n =>
          ¬ (List.IsPrefix (p ++ [false]) (addr (false, i)) ↔
             List.IsPrefix (p ++ [false]) (addr (true, perm i))))).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        have hne : addr (false, i) ≠ addr (true, perm i) := fun h => by
          have := h_inj h; simp at this
        have hlen : (addr (false, i)).length = (addr (true, perm i)).length := by
          rw [h_len, h_len]
        rcases lcp_lt_of_ne hlen hne with ⟨_, d, hd1, hd2⟩
        rw [hi] at hd1 hd2
        have hdisj : ∀ a : List Bool, List.IsPrefix (p ++ [true]) a →
            List.IsPrefix (p ++ [false]) a → False := by
          intro a h1 h2
          rcases h1 with ⟨t1, ht1⟩; rcases h2 with ⟨t2, ht2⟩
          have hcon := ht1.trans ht2.symm
          simp only [List.append_assoc, List.cons_append, List.nil_append] at hcon
          have hcon' := List.append_cancel_left hcon
          simp at hcon'
        cases d
        · intro hiff; exact hdisj (addr (true, perm i)) hd2 (hiff.mp hd1)
        · intro hiff; exact hdisj (addr (false, i)) hd1 (hiff.mpr hd2)
    _ ≤ t := ht (p ++ [false])

def sumDiffsIn {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) (p : List Bool) : ℕ :=
  ∑ j : Fin r, (Finset.univ.filter (fun i : Fin n =>
    List.IsPrefix p (lcp (addr (false, i)) (addr (true, M j i))))).card

lemma sumDiffsIn_split {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) (p : List Bool) :
    (∑ j : Fin r, diffAt addr (M j) p) +
      sumDiffsIn M addr (p ++ [false]) + sumDiffsIn M addr (p ++ [true]) ≤
    sumDiffsIn M addr p := by
  simp only [sumDiffsIn, diffAt]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  let A := Finset.univ.filter (fun i : Fin n => lcp (addr (false, i)) (addr (true, M j i)) = p)
  let B := Finset.univ.filter (fun i : Fin n => List.IsPrefix (p ++ [false]) (lcp (addr (false, i)) (addr (true, M j i))))
  let C := Finset.univ.filter (fun i : Fin n => List.IsPrefix (p ++ [true]) (lcp (addr (false, i)) (addr (true, M j i))))
  let U := Finset.univ.filter (fun i : Fin n => List.IsPrefix p (lcp (addr (false, i)) (addr (true, M j i))))
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro i hiA hiB
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hiA hiB
    rw [hiA] at hiB; have := hiB.length_le; simp at this
  have hAC : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro i hiA hiC
    simp only [A, C, Finset.mem_filter, Finset.mem_univ, true_and] at hiA hiC
    rw [hiA] at hiC; have := hiC.length_le; simp at this
  have hBC : Disjoint B C := by
    rw [Finset.disjoint_left]
    intro i hiB hiC
    simp only [B, C, Finset.mem_filter, Finset.mem_univ, true_and] at hiB hiC
    rcases hiB with ⟨t1, ht1⟩; rcases hiC with ⟨t2, ht2⟩
    have hcon := ht1.trans ht2.symm
    simp only [List.append_assoc, List.cons_append, List.nil_append] at hcon
    have hcon' := List.append_cancel_left hcon
    simp at hcon'
  have hsub : A ∪ B ∪ C ⊆ U := by
    intro i hi
    simp only [A, B, C, U, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rcases hi with (rfl | h) | h
    · exact List.prefix_refl _
    · exact List.IsPrefix.trans (List.prefix_append _ _) h
    · exact List.IsPrefix.trans (List.prefix_append _ _) h
  calc A.card + B.card + C.card = (A ∪ B).card + C.card := by rw [Finset.card_union_of_disjoint hAB]
    _ = (A ∪ B ∪ C).card := by rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩)]
    _ ≤ U.card := Finset.card_le_card hsub

lemma emitDiffs_len_le {n : ℕ} (addr : (Bool × Fin n) → List Bool)
    (perm : Equiv.Perm (Fin n)) (p : List Bool) (st : CState (Bool × Fin n)) :
    ∀ l : List (Fin n), st.len ≤ (emitDiffs st p addr perm l).1.len
  | [] => by simp [emitDiffs]
  | i :: rest => by
    have ih := emitDiffs_len_le addr perm p st rest
    dsimp [emitDiffs]
    split_ifs
    · have h1 : (emitDiffs st p addr perm rest).1.len ≤
          (emitXor (emitDiffs st p addr perm rest).1 p (Sum.inl (false, i)) (Sum.inl (true, perm i))).1.len := by
        simp [emitXor, CState.emit]
      exact le_trans ih h1
    · exact ih

lemma emitDiffs_len_eq {n : ℕ} (addr : (Bool × Fin n) → List Bool)
    (perm : Equiv.Perm (Fin n)) (p : List Bool) (st : CState (Bool × Fin n)) :
    ∀ l : List (Fin n),
      (emitDiffs st p addr perm l).1.len - st.len =
        (l.filter (fun i => decide (lcp (addr (false, i)) (addr (true, perm i)) = p))).length ∧
      (emitDiffs st p addr perm l).2.length =
        (l.filter (fun i => decide (lcp (addr (false, i)) (addr (true, perm i)) = p))).length
  | [] => by simp [emitDiffs]
  | i :: rest => by
    have ih := emitDiffs_len_eq addr perm p st rest
    have hle := emitDiffs_len_le addr perm p st rest
    dsimp [emitDiffs]
    rw [List.filter_cons]
    by_cases h : lcp (addr (false, i)) (addr (true, perm i)) = p
    · simp only [h, decide_true, ↓reduceIte, List.length_cons]
      have hxor : (emitXor (emitDiffs st p addr perm rest).1 p (Sum.inl (false, i)) (Sum.inl (true, perm i))).1.len =
          (emitDiffs st p addr perm rest).1.len + 1 := by
        simp [emitXor, CState.emit]
      omega
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact ih

lemma mergePairCols_len_le {V : Type} :
    ∀ (k : ℕ) (wL wR : List (Option (V ⊕ ℕ))),
      (mergePairCols k wL wR).length = k ∧
      ((mergePairCols k wL wR).map List.length).sum ≤ wL.length + wR.length
  | 0, _, _ => by simp [mergePairCols]
  | k + 1, wL, wR => by
    have ih := mergePairCols_len_le k wL.tail wR.tail
    simp only [mergePairCols, List.length_cons, List.map_cons, List.sum_cons, List.length_append]
    have hL : (match wL with | [] => ([] : List (V ⊕ ℕ)) | o :: _ => optToList o).length + wL.tail.length ≤ wL.length := by
      cases wL with
      | nil => simp
      | cons o t => cases o <;> simp [optToList] <;> omega
    have hR : (match wR with | [] => ([] : List (V ⊕ ℕ)) | o :: _ => optToList o).length + wR.tail.length ≤ wR.length := by
      cases wR with
      | nil => simp
      | cons o t => cases o <;> simp [optToList] <;> omega
    omega

lemma mergeCols_len_le {V : Type} (b : ℕ) (ds : List (V ⊕ ℕ))
    (wL wR : List (Option (V ⊕ ℕ))) :
    (mergeCols b ds wL wR).length ≤ b ∧
    ((mergeCols b ds wL wR).map List.length).sum ≤ ds.length + wL.length + wR.length := by
  have hm := mergePairCols_len_le b wL wR
  dsimp [mergeCols]
  cases h : mergePairCols b wL wR with
  | nil => simp
  | cons c0 rest =>
    rw [h] at hm
    simp only [List.length_cons, List.map_cons, List.sum_cons, List.length_append] at hm ⊢
    omega

lemma compressCol_len_le {V : Type} :
    ∀ (col carries : List (V ⊕ ℕ)) (st : CState V) (p : List Bool),
      st.len ≤ (compressCol st p col carries).1.len ∧
      (compressCol st p col carries).1.len - st.len +
        5 * ((compressCol st p col carries).2.2.length - carries.length) ≤
        5 * col.length + 2 ∧
      carries.length ≤ (compressCol st p col carries).2.2.length
  | [], carries, st, p => by rw [compressCol]; simp
  | [a], carries, st, p => by rw [compressCol]; simp
  | [a, b], carries, st, p => by
    rw [compressCol]
    have h1 : (emitHalfAdder st p a b).1.len = st.len + 2 := by
      simp [emitHalfAdder, emitXor, emitAnd, CState.emit]
    dsimp only
    rw [h1]
    simp
  | a :: b :: c :: rest, carries, st, p => by
    have h1 : (emitFullAdder st p a b c).1.len = st.len + 5 := by
      simp [emitFullAdder, emitXor, emitAnd, emitOr, CState.emit]
    have ih := compressCol_len_le ((emitFullAdder st p a b c).2.1 :: rest)
      ((emitFullAdder st p a b c).2.2 :: carries) (emitFullAdder st p a b c).1 p
    rw [compressCol]
    simp only [List.length_cons, h1] at ih ⊢
    set L1 := (compressCol (emitFullAdder st p a b c).1 p ((emitFullAdder st p a b c).2.1 :: rest)
      ((emitFullAdder st p a b c).2.2 :: carries)).1.len
    set C1 := (compressCol (emitFullAdder st p a b c).1 p ((emitFullAdder st p a b c).2.1 :: rest)
      ((emitFullAdder st p a b c).2.2 :: carries)).2.2.length
    have hle1 : st.len ≤ st.len + 5 := by omega
    have h_tri : ∀ x y z : ℕ, x ≤ y → y ≤ z → z - x = (z - y) + (y - x) := fun x y z h1 h2 => by omega
    rw [h_tri st.len (st.len + 5) L1 hle1 ih.1]
    have hsub : C1 - carries.length = (C1 - (carries.length + 1)) + 1 := by omega
    rw [hsub]
    simp only [Nat.mul_add, Nat.mul_one] at ih ⊢
    omega
termination_by col => col.length

lemma compressAll_len_le {V : Type} :
    ∀ (cols : List (List (V ⊕ ℕ))) (st : CState V) (p : List Bool),
      st.len ≤ (compressAll st p cols).1.len ∧
      (compressAll st p cols).1.len - st.len ≤
        5 * (cols.map List.length).sum + 2 * cols.length ∧
      (compressAll st p cols).2.length = cols.length
  | [], st, p => by rw [compressAll]; simp
  | col :: rest, st, p => by
    have hcc := compressCol_len_le col [] st p
    set st1 := (compressCol st p col []).1
    set carries := (compressCol st p col []).2.2
    let rest' := match rest with | [] => [] | next :: tail => (carries ++ next) :: tail
    have hrest'_len : rest'.length = rest.length := by cases rest <;> rfl
    have hrest'_pot : (rest'.map List.length).sum ≤ carries.length + (rest.map List.length).sum := by
      cases rest with
      | nil => simp [rest']
      | cons next tail => simp [rest', List.length_append]; omega
    have ih := compressAll_len_le rest' st1 p
    rw [compressAll]
    dsimp only [st1, carries, rest'] at ih hrest'_len hrest'_pot hcc ⊢
    refine ⟨le_trans hcc.1 ih.1, ?_, ?_⟩
    · simp only [List.map_cons, List.sum_cons, List.length_cons, List.length_nil, Nat.sub_zero] at hcc ih ⊢
      have h_tri : ∀ x y z : ℕ, x ≤ y → y ≤ z → z - x = (z - y) + (y - x) :=
        fun x y z h1 h2 => by omega
      rw [h_tri _ _ _ hcc.1 ih.1]
      rw [hrest'_len] at ih
      linarith [hcc.2.1, ih.2.1, hrest'_pot]
    · simp only [List.length_cons]; rw [ih.2.2, hrest'_len]
termination_by cols => cols.length
decreasing_by
  cases rest <;> simp

lemma buildBranches_len_le {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) (b : ℕ) (p : List Bool) :
    ∀ (js : List (Fin r)) (wLs wRs : List (List (Option ((Bool × Fin n) ⊕ ℕ))))
      (st : CState (Bool × Fin n)),
      (∀ wL ∈ wLs, wL.length ≤ b) → (∀ wR ∈ wRs, wR.length ≤ b) → js.Nodup →
      st.len ≤ (buildBranches M addr b p st js wLs wRs).1.len ∧
      (buildBranches M addr b p st js wLs wRs).1.len - st.len ≤
        6 * (∑ j ∈ js.toFinset, diffAt addr (M j) p) + 12 * js.length * b
  | [], _, _, st, _, _, _ => by simp [buildBranches]
  | j :: js, wLs, wRs, st, hwL, hwR, hnd => by
    have hnd' := List.nodup_cons.mp hnd
    have h1_le := emitDiffs_len_le addr (M j) p st (List.finRange n)
    have h1_len := emitDiffs_len_eq addr (M j) p st (List.finRange n)
    set st1 := (emitDiffs st p addr (M j) (List.finRange n)).1
    set ds := (emitDiffs st p addr (M j) (List.finRange n)).2
    have hds_eq : ds.length = diffAt addr (M j) p := by
      rw [h1_len.2]
      rw [← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]
      congr 1; ext i; simp [diffAt]
    have hwL0 : (wLs.headD []).length ≤ b := by
      cases wLs with | nil => simp | cons a as => exact hwL a (by simp)
    have hwR0 : (wRs.headD []).length ≤ b := by
      cases wRs with | nil => simp | cons a as => exact hwR a (by simp)
    have hm := mergeCols_len_le b ds (wLs.headD []) (wRs.headD [])
    have hca := compressAll_len_le (mergeCols b ds (wLs.headD []) (wRs.headD [])) st1 p
    set st2 := (compressAll st1 p (mergeCols b ds (wLs.headD []) (wRs.headD []))).1
    have hwL_tail : ∀ wL ∈ wLs.tail, wL.length ≤ b := by
      cases wLs with | nil => simp | cons _ _ => intro w hw; exact hwL w (List.mem_cons_of_mem _ hw)
    have hwR_tail : ∀ wR ∈ wRs.tail, wR.length ≤ b := by
      cases wRs with | nil => simp | cons _ _ => intro w hw; exact hwR w (List.mem_cons_of_mem _ hw)
    have ih := buildBranches_len_le M addr b p js wLs.tail wRs.tail st2 hwL_tail hwR_tail hnd'.2
    have h_sum_insert : ∑ x ∈ (j :: js).toFinset, diffAt addr (M x) p =
        diffAt addr (M j) p + ∑ x ∈ js.toFinset, diffAt addr (M x) p := by
      rw [List.toFinset_cons, Finset.sum_insert (by simpa using hnd'.1)]
    have h_mul : 12 * (js.length + 1) * b = 12 * js.length * b + 12 * b := by ring
    have h_goal : (buildBranches M addr b p st2 js wLs.tail wRs.tail).1.len - st.len ≤
        6 * (∑ j ∈ (j :: js).toFinset, diffAt addr (M j) p) + 12 * (j :: js).length * b := by
      rw [h_sum_insert, List.length_cons, h_mul]
      have h_tri : (buildBranches M addr b p st2 js wLs.tail wRs.tail).1.len - st.len =
          ((buildBranches M addr b p st2 js wLs.tail wRs.tail).1.len - st2.len) +
          (st2.len - st1.len) + (st1.len - st.len) := by
        have := h1_le; have := hca.1; have := ih.1; omega
      rw [h_tri]
      linarith [h1_len.1, h1_len.2, hds_eq, hm.1, hm.2, hwL0, hwR0, hca.2.1, ih.2]
    dsimp [buildBranches]
    exact ⟨le_trans h1_le (le_trans hca.1 ih.1), h_goal⟩

lemma buildNode_outs_len_le {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) (b : ℕ) :
    ∀ (d : ℕ) (p : List Bool) (st : CState (Bool × Fin n))
      (out : List (Option ((Bool × Fin n) ⊕ ℕ))),
      out ∈ (buildNode M addr b d p st).2 → out.length ≤ b
  | 0, _, _, out, hout => by
    simp [buildNode, List.mem_replicate] at hout; rcases hout with ⟨_, rfl⟩; simp
  | d + 1, p, st, out, hout => by
    dsimp [buildNode] at hout
    split_ifs at hout with h1 h2 h3
    · have hbb : ∀ (js : List (Fin r)) (wLs wRs : List (List (Option ((Bool × Fin n) ⊕ ℕ))))
          (st0 : CState (Bool × Fin n)) (out0 : List (Option ((Bool × Fin n) ⊕ ℕ))),
          out0 ∈ (buildBranches M addr b p st0 js wLs wRs).2 → out0.length ≤ b := by
        intro js wLs wRs st0 out0 hout0
        induction js generalizing wLs wRs st0 with
        | nil => simp [buildBranches] at hout0
        | cons j js' ihj =>
          dsimp [buildBranches] at hout0
          simp only [List.mem_cons] at hout0
          rcases hout0 with rfl | hout0
          · have hca := compressAll_len_le (mergeCols b (emitDiffs st0 p addr (M j) (List.finRange n)).2
              (wLs.headD []) (wRs.headD [])) (emitDiffs st0 p addr (M j) (List.finRange n)).1 p
            have hm := mergeCols_len_le b (emitDiffs st0 p addr (M j) (List.finRange n)).2
              (wLs.headD []) (wRs.headD [])
            omega
          · exact ihj wLs.tail wRs.tail _ hout0
      exact hbb _ _ _ _ out hout
    · exact buildNode_outs_len_le M addr b d (p ++ [false]) st out hout
    · exact buildNode_outs_len_le M addr b d (p ++ [true]) st out hout
    · simp [List.mem_replicate] at hout; rcases hout with ⟨_, rfl⟩; simp

lemma buildNode_len_le {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) (b : ℕ) :
    ∀ (d : ℕ) (p : List Bool) (st : CState (Bool × Fin n)),
      st.len ≤ (buildNode M addr b d p st).1.len ∧
      (buildNode M addr b d p st).1.len - st.len ≤
        6 * sumDiffsIn M addr p + 12 * r * b * (leavesIn addr p - 1)
  | 0, _, st => by simp [buildNode]
  | d + 1, p, st => by
    dsimp [buildNode]
    split_ifs with h1 h2 h3
    · simp only [Bool.and_eq_true] at h1
      have hL := buildNode_len_le M addr b d (p ++ [false]) st
      set st1 := (buildNode M addr b d (p ++ [false]) st).1
      set wL := (buildNode M addr b d (p ++ [false]) st).2
      have hR := buildNode_len_le M addr b d (p ++ [true]) st1
      set st2 := (buildNode M addr b d (p ++ [true]) st1).1
      set wR := (buildNode M addr b d (p ++ [true]) st1).2
      have hbb := buildBranches_len_le M addr b p (List.finRange r) wL wR st2
        (fun w hw => buildNode_outs_len_le M addr b d (p ++ [false]) st w hw)
        (fun w hw => buildNode_outs_len_le M addr b d (p ++ [true]) st1 w hw)
        (List.nodup_finRange r)
      refine ⟨le_trans hL.1 (le_trans hR.1 hbb.1), ?_⟩
      have h_tri : ∀ x y z w : ℕ, x ≤ y → y ≤ z → z ≤ w → w - x = (w - z) + (z - y) + (y - x) :=
        fun x y z w ha hb hc => by omega
      rw [h_tri st.len st1.len st2.len _ hL.1 hR.1 hbb.1]
      have hposL : 1 ≤ leavesIn addr (p ++ [false]) := by
        simp only [occ, decide_eq_true_eq] at h1
        rcases h1.1 with ⟨v, hv⟩
        exact Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩
      have hposR : 1 ≤ leavesIn addr (p ++ [true]) := by
        simp only [occ, decide_eq_true_eq] at h1
        rcases h1.2 with ⟨v, hv⟩
        exact Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩
      have hdisj : leavesIn addr (p ++ [false]) + leavesIn addr (p ++ [true]) ≤ leavesIn addr p := by
        have hAB : Disjoint
            (Finset.univ.filter (fun v => List.IsPrefix (p ++ [false]) (addr v)))
            (Finset.univ.filter (fun v => List.IsPrefix (p ++ [true]) (addr v))) := by
          rw [Finset.disjoint_left]
          intro v hv1 hv2
          simp only [Finset.mem_filter] at hv1 hv2
          rcases hv1.2 with ⟨t1, ht1⟩; rcases hv2.2 with ⟨t2, ht2⟩
          have hcon := ht1.trans ht2.symm
          simp only [List.append_assoc, List.cons_append, List.nil_append] at hcon
          have hcon' := List.append_cancel_left hcon
          simp at hcon'
        simp only [leavesIn]
        rw [← Finset.card_union_of_disjoint hAB]
        apply Finset.card_le_card
        intro v hv
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        rcases hv with h | h <;> exact List.IsPrefix.trans (List.prefix_append _ _) h
      have h_leaves : (leavesIn addr (p ++ [false]) - 1) + (leavesIn addr (p ++ [true]) - 1) + 1 ≤
          leavesIn addr p - 1 := by omega
      have h_sum_r : (∑ j ∈ (List.finRange r).toFinset, diffAt addr (M j) p) =
          ∑ j : Fin r, diffAt addr (M j) p := by
        congr 1; ext j; simp
      rw [h_sum_r, List.length_finRange] at hbb
      have h_sdiff := sumDiffsIn_split M addr p
      have h_rb : 12 * r * b * ((leavesIn addr (p ++ [false]) - 1) + (leavesIn addr (p ++ [true]) - 1) + 1) ≤
          12 * r * b * (leavesIn addr p - 1) := Nat.mul_le_mul_left _ h_leaves
      nlinarith
    · have ih := buildNode_len_le M addr b d (p ++ [false]) st
      refine ⟨ih.1, ?_⟩
      have hsd : sumDiffsIn M addr (p ++ [false]) ≤ sumDiffsIn M addr p := by
        have := sumDiffsIn_split M addr p; omega
      have hlv : leavesIn addr (p ++ [false]) ≤ leavesIn addr p := by
        apply Finset.card_le_card
        intro v hv; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        exact List.IsPrefix.trans (List.prefix_append _ _) hv
      have h_rb : 12 * r * b * (leavesIn addr (p ++ [false]) - 1) ≤ 12 * r * b * (leavesIn addr p - 1) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    · have ih := buildNode_len_le M addr b d (p ++ [true]) st
      refine ⟨ih.1, ?_⟩
      have hsd : sumDiffsIn M addr (p ++ [true]) ≤ sumDiffsIn M addr p := by
        have := sumDiffsIn_split M addr p; omega
      have hlv : leavesIn addr (p ++ [true]) ≤ leavesIn addr p := by
        apply Finset.card_le_card
        intro v hv; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        exact List.IsPrefix.trans (List.prefix_append _ _) hv
      have h_rb : 12 * r * b * (leavesIn addr (p ++ [true]) - 1) ≤ 12 * r * b * (leavesIn addr p - 1) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    · simp

lemma emitGate_nodesIn {V : Type} (st : CState V) (p : List Bool) (g : ℕ → Gate V) :
    NodesIn st (st.emit p g).1 p := by
  refine ⟨[⟨g st.len, p⟩], rfl, ?_⟩
  simp

lemma emitXor_nodesIn {V : Type} (st : CState V) (p : List Bool) (a b : V ⊕ ℕ) :
    NodesIn st (emitXor st p a b).1 p := emitGate_nodesIn st p _

lemma emitAnd_nodesIn {V : Type} (st : CState V) (p : List Bool) (a b : V ⊕ ℕ) :
    NodesIn st (emitAnd st p a b).1 p := emitGate_nodesIn st p _

lemma emitOr_nodesIn {V : Type} (st : CState V) (p : List Bool) (a b : V ⊕ ℕ) :
    NodesIn st (emitOr st p a b).1 p := emitGate_nodesIn st p _

lemma emitConst_nodesIn {V : Type} (st : CState V) (p : List Bool) (b : Bool) :
    NodesIn st (emitConst st p b).1 p := emitGate_nodesIn st p _

lemma emitHalfAdder_nodesIn {V : Type} (st : CState V) (p : List Bool) (a b : V ⊕ ℕ) :
    NodesIn st (emitHalfAdder st p a b).1 p :=
  nodesIn_trans (emitXor_nodesIn st p a b) (emitAnd_nodesIn _ p a b)

lemma emitFullAdder_nodesIn {V : Type} (st : CState V) (p : List Bool) (a b c : V ⊕ ℕ) :
    NodesIn st (emitFullAdder st p a b c).1 p :=
  nodesIn_trans (emitXor_nodesIn st p a b)
    (nodesIn_trans (emitXor_nodesIn _ p _ c)
      (nodesIn_trans (emitAnd_nodesIn _ p a b)
        (nodesIn_trans (emitAnd_nodesIn _ p _ c) (emitOr_nodesIn _ p _ _))))

lemma compressCol_nodesIn {V : Type} :
    ∀ (col carries : List (V ⊕ ℕ)) (st : CState V) (p : List Bool),
      NodesIn st (compressCol st p col carries).1 p
  | [], _, st, p => by rw [compressCol]; exact nodesIn_refl _ _
  | [_], _, st, p => by rw [compressCol]; exact nodesIn_refl _ _
  | [a, b], _, st, p => by rw [compressCol]; exact emitHalfAdder_nodesIn st p a b
  | a :: b :: c :: rest, carries, st, p => by
    rw [compressCol]
    exact nodesIn_trans (emitFullAdder_nodesIn st p a b c)
      (compressCol_nodesIn ((emitFullAdder st p a b c).2.1 :: rest)
        ((emitFullAdder st p a b c).2.2 :: carries) (emitFullAdder st p a b c).1 p)
termination_by col => col.length

lemma compressAll_nodesIn {V : Type} :
    ∀ (cols : List (List (V ⊕ ℕ))) (st : CState V) (p : List Bool),
      NodesIn st (compressAll st p cols).1 p
  | [], st, p => by rw [compressAll]; exact nodesIn_refl _ _
  | col :: rest, st, p => by
    rw [compressAll]
    exact nodesIn_trans (compressCol_nodesIn col [] st p) (compressAll_nodesIn _ _ p)
termination_by cols => cols.length
decreasing_by
  cases rest <;> simp

lemma emitDiffs_nodesIn {n : ℕ} (addr : (Bool × Fin n) → List Bool)
    (perm : Equiv.Perm (Fin n)) (p : List Bool) (st : CState (Bool × Fin n)) :
    ∀ l : List (Fin n), NodesIn st (emitDiffs st p addr perm l).1 p
  | [] => by simp [emitDiffs]; exact nodesIn_refl _ _
  | i :: rest => by
    dsimp [emitDiffs]
    split_ifs
    · exact nodesIn_trans (emitDiffs_nodesIn addr perm p st rest) (emitXor_nodesIn _ p _ _)
    · exact emitDiffs_nodesIn addr perm p st rest

lemma buildBranches_nodesIn {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) (b : ℕ) (p : List Bool) :
    ∀ (js : List (Fin r)) (wLs wRs : List (List (Option ((Bool × Fin n) ⊕ ℕ))))
      (st : CState (Bool × Fin n)),
      NodesIn st (buildBranches M addr b p st js wLs wRs).1 p
  | [], _, _, st => by simp [buildBranches]; exact nodesIn_refl _ _
  | j :: js, wLs, wRs, st => by
    dsimp [buildBranches]
    exact nodesIn_trans (emitDiffs_nodesIn addr (M j) p st (List.finRange n))
      (nodesIn_trans (compressAll_nodesIn _ _ p)
        (buildBranches_nodesIn M addr b p js wLs.tail wRs.tail _))

lemma buildNode_node_prop {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) (b : ℕ)
    (P : List Bool → Prop) :
    ∀ (d : ℕ) (q : List Bool) (st : CState (Bool × Fin n)),
      (∀ e ∈ st.rev, P e.node) →
      (∀ p, List.IsPrefix q p → p.length ≤ q.length + d → isBranch addr p = true → P p) →
      ∀ e ∈ (buildNode M addr b d q st).1.rev, P e.node
  | 0, _, st, hst, _ => by simpa [buildNode] using hst
  | d + 1, q, st, hst, hP => by
    dsimp [buildNode]
    split_ifs with h1 h2 h3
    · have hbr : isBranch addr q = true := h1
      have hPq : P q := hP q (List.prefix_refl _) (by omega) hbr
      have h1' := buildNode_node_prop M addr b P d (q ++ [false]) st hst
        (fun p hp hlen => hP p (List.IsPrefix.trans (List.prefix_append _ _) hp) (by simp at hlen; omega))
      have h2' := buildNode_node_prop M addr b P d (q ++ [true]) _ h1'
        (fun p hp hlen => hP p (List.IsPrefix.trans (List.prefix_append _ _) hp) (by simp at hlen; omega))
      exact nodesIn_node_prop (buildBranches_nodesIn M addr b q (List.finRange r) _ _ _) P h2' hPq
    · exact buildNode_node_prop M addr b P d (q ++ [false]) st hst
        (fun p hp hlen => hP p (List.IsPrefix.trans (List.prefix_append _ _) hp) (by simp at hlen; omega))
    · exact buildNode_node_prop M addr b P d (q ++ [true]) st hst
        (fun p hp hlen => hP p (List.IsPrefix.trans (List.prefix_append _ _) hp) (by simp at hlen; omega))
    · exact hst

lemma nodesIn_rev_length_eq {V : Type} {st1 st2 : CState V} {p : List Bool}
    (hn : NodesIn st1 st2 p) (h1 : st1.len = st1.rev.length) (h2 : st2.len = st2.rev.length) :
    st2.rev.length - st1.rev.length = st2.len - st1.len := by omega

lemma emitGate_len_eq_rev {V : Type} (st : CState V) (p : List Bool) (g : ℕ → Gate V)
    (h : st.len = st.rev.length) : (st.emit p g).1.len = (st.emit p g).1.rev.length := by
  simp [CState.emit, h]

lemma compressCol_len_eq_rev {V : Type} :
    ∀ (col carries : List (V ⊕ ℕ)) (st : CState V) (p : List Bool),
      st.len = st.rev.length →
      (compressCol st p col carries).1.len = (compressCol st p col carries).1.rev.length
  | [], _, st, _, h => by rw [compressCol]; exact h
  | [_], _, st, _, h => by rw [compressCol]; exact h
  | [a, b], _, st, _, h => by
    rw [compressCol]; simp [emitHalfAdder, emitXor, emitAnd, CState.emit, h]
  | a :: b :: c :: rest, carries, st, p, h => by
    rw [compressCol]
    apply compressCol_len_eq_rev
    simp [emitFullAdder, emitXor, emitAnd, emitOr, CState.emit, h]
termination_by col => col.length

lemma compressAll_len_eq_rev {V : Type} :
    ∀ (cols : List (List (V ⊕ ℕ))) (st : CState V) (p : List Bool),
      st.len = st.rev.length →
      (compressAll st p cols).1.len = (compressAll st p cols).1.rev.length
  | [], st, _, h => by rw [compressAll]; exact h
  | col :: rest, st, p, h => by
    rw [compressAll]
    exact compressAll_len_eq_rev _ _ p (compressCol_len_eq_rev col [] st p h)
termination_by cols => cols.length
decreasing_by
  cases rest <;> simp

lemma emitDiffs_len_eq_rev {n : ℕ} (addr : (Bool × Fin n) → List Bool)
    (perm : Equiv.Perm (Fin n)) (p : List Bool) (st : CState (Bool × Fin n)) :
    ∀ l : List (Fin n), st.len = st.rev.length →
      (emitDiffs st p addr perm l).1.len = (emitDiffs st p addr perm l).1.rev.length
  | [], h => by simp [emitDiffs, h]
  | i :: rest, h => by
    dsimp [emitDiffs]
    split_ifs
    · exact emitGate_len_eq_rev _ _ _ (emitDiffs_len_eq_rev addr perm p st rest h)
    · exact emitDiffs_len_eq_rev addr perm p st rest h

lemma buildBranches_len_eq_rev {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) (b : ℕ) (p : List Bool) :
    ∀ (js : List (Fin r)) (wLs wRs : List (List (Option ((Bool × Fin n) ⊕ ℕ))))
      (st : CState (Bool × Fin n)), st.len = st.rev.length →
      (buildBranches M addr b p st js wLs wRs).1.len =
      (buildBranches M addr b p st js wLs wRs).1.rev.length
  | [], _, _, st, h => by simp [buildBranches, h]
  | j :: js, wLs, wRs, st, h => by
    dsimp [buildBranches]
    exact buildBranches_len_eq_rev M addr b p js wLs.tail wRs.tail _
      (compressAll_len_eq_rev _ _ p (emitDiffs_len_eq_rev addr (M j) p st _ h))

lemma buildNode_len_eq_rev {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) (b : ℕ) :
    ∀ (d : ℕ) (p : List Bool) (st : CState (Bool × Fin n)), st.len = st.rev.length →
      (buildNode M addr b d p st).1.len = (buildNode M addr b d p st).1.rev.length
  | 0, _, st, h => by simp [buildNode, h]
  | d + 1, p, st, h => by
    dsimp [buildNode]
    split_ifs
    · exact buildBranches_len_eq_rev M addr b p _ _ _ _
        (buildNode_len_eq_rev M addr b d (p ++ [true]) _
          (buildNode_len_eq_rev M addr b d (p ++ [false]) st h))
    · exact buildNode_len_eq_rev M addr b d (p ++ [false]) st h
    · exact buildNode_len_eq_rev M addr b d (p ++ [true]) st h
    · exact h

lemma buildNode_countNode_le {n r t h : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) (b : ℕ)
    (h_inj : Function.Injective addr) (h_len : ∀ v, (addr v).length = h)
    (ht : ∀ (p : List Bool) (j : Fin r),
      (Finset.univ.filter (fun i : Fin n =>
        ¬ (List.IsPrefix p (addr (false, i)) ↔ List.IsPrefix p (addr (true, M j i))))).card ≤ t) :
    ∀ (d : ℕ) (q : List Bool) (st : CState (Bool × Fin n)) (p : List Bool),
      st.len = st.rev.length →
      (¬ List.IsPrefix q p → countNode (buildNode M addr b d q st).1.rev p = countNode st.rev p) ∧
      (List.IsPrefix q p → countNode (buildNode M addr b d q st).1.rev p ≤
        countNode st.rev p + r * (6 * t + 12 * b))
  | 0, q, st, p, _ => by simp [buildNode]
  | d + 1, q, st, p, hst => by
    dsimp [buildNode]
    split_ifs with h1 h2 h3
    · have hst1 := buildNode_len_eq_rev M addr b d (q ++ [false]) st hst
      have hst2 := buildNode_len_eq_rev M addr b d (q ++ [true]) _ hst1
      have ihL := buildNode_countNode_le M addr b h_inj h_len ht d (q ++ [false]) st p hst
      have ihR := buildNode_countNode_le M addr b h_inj h_len ht d (q ++ [true]) _ p hst1
      set st1 := (buildNode M addr b d (q ++ [false]) st).1
      set wL := (buildNode M addr b d (q ++ [false]) st).2
      set st2 := (buildNode M addr b d (q ++ [true]) st1).1
      set wR := (buildNode M addr b d (q ++ [true]) st1).2
      have hbb_nod := buildBranches_nodesIn M addr b q (List.finRange r) wL wR st2
      have hbb_len := buildBranches_len_le M addr b q (List.finRange r) wL wR st2
        (fun w hw => buildNode_outs_len_le M addr b d (q ++ [false]) st w hw)
        (fun w hw => buildNode_outs_len_le M addr b d (q ++ [true]) st1 w hw)
        (List.nodup_finRange r)
      have hbb_rev := buildBranches_len_eq_rev M addr b q (List.finRange r) wL wR st2 hst2
      have hbb_bnd : (buildBranches M addr b q st2 (List.finRange r) wL wR).1.len - st2.len ≤
          r * (6 * t + 12 * b) := by
        have hsum : (∑ j ∈ (List.finRange r).toFinset, diffAt addr (M j) q) ≤ r * t := by
          calc (∑ j ∈ (List.finRange r).toFinset, diffAt addr (M j) q)
              ≤ ∑ _j ∈ (List.finRange r).toFinset, t := Finset.sum_le_sum (fun j _ =>
                diffAt_le_t addr (M j) h_inj h_len (fun p' => ht p' j) q)
            _ = (List.finRange r).toFinset.card * t := by simp [Finset.sum_const]
            _ ≤ r * t := by rw [List.toFinset_card_of_nodup (List.nodup_finRange r), List.length_finRange]
        rw [List.length_finRange] at hbb_len
        nlinarith
      constructor
      · intro hnot
        have hnotL : ¬ List.IsPrefix (q ++ [false]) p :=
          fun hp => hnot (List.IsPrefix.trans (List.prefix_append _ _) hp)
        have hnotR : ¬ List.IsPrefix (q ++ [true]) p :=
          fun hp => hnot (List.IsPrefix.trans (List.prefix_append _ _) hp)
        have hne : q ≠ p := fun heq => hnot (heq ▸ List.prefix_refl _)
        rw [countNode_nodesIn_ne hbb_nod hne, ihR.1 hnotR, ihL.1 hnotL]
      · intro hqp
        rcases prefix_trichotomy q p hqp with rfl | hL | hR
        · have hnotL : ¬ List.IsPrefix (p ++ [false]) p := fun h => by have := h.length_le; simp at this
          have hnotR : ¬ List.IsPrefix (p ++ [true]) p := fun h => by have := h.length_le; simp at this
          have hcn := countNode_nodesIn_le hbb_nod
          rw [nodesIn_rev_length_eq hbb_nod hst2 hbb_rev] at hcn
          rw [ihR.1 hnotR, ihL.1 hnotL] at hcn
          omega
        · have hne : q ≠ p := fun heq => by subst heq; have := hL.length_le; simp at this
          have hnotR : ¬ List.IsPrefix (q ++ [true]) p := by
            intro hR
            rcases hL with ⟨t1, ht1⟩; rcases hR with ⟨t2, ht2⟩
            have hcon := ht1.trans ht2.symm
            simp only [List.append_assoc, List.cons_append, List.nil_append] at hcon
            have hcon' := List.append_cancel_left hcon
            simp at hcon'
          rw [countNode_nodesIn_ne hbb_nod hne, ihR.1 hnotR]
          exact ihL.2 hL
        · have hne : q ≠ p := fun heq => by subst heq; have := hR.length_le; simp at this
          have hnotL : ¬ List.IsPrefix (q ++ [false]) p := by
            intro hL
            rcases hL with ⟨t1, ht1⟩; rcases hR with ⟨t2, ht2⟩
            have hcon := ht1.trans ht2.symm
            simp only [List.append_assoc, List.cons_append, List.nil_append] at hcon
            have hcon' := List.append_cancel_left hcon
            simp at hcon'
          rw [countNode_nodesIn_ne hbb_nod hne]
          calc countNode st2.rev p ≤ countNode st1.rev p + r * (6 * t + 12 * b) := ihR.2 hR
            _ = countNode st.rev p + r * (6 * t + 12 * b) := by rw [ihL.1 hnotL]
    · have ih := buildNode_countNode_le M addr b h_inj h_len ht d (q ++ [false]) st p hst
      constructor
      · intro hnot; exact ih.1 (fun hp => hnot (List.IsPrefix.trans (List.prefix_append _ _) hp))
      · intro hqp
        rcases prefix_trichotomy q p hqp with rfl | hL | hR
        · have hnotL : ¬ List.IsPrefix (p ++ [false]) p := fun h => by have := h.length_le; simp at this
          rw [ih.1 hnotL]; omega
        · exact ih.2 hL
        · have hnotL : ¬ List.IsPrefix (q ++ [false]) p := by
            intro hL
            rcases hL with ⟨t1, ht1⟩; rcases hR with ⟨t2, ht2⟩
            have hcon := ht1.trans ht2.symm
            simp only [List.append_assoc, List.cons_append, List.nil_append] at hcon
            have hcon' := List.append_cancel_left hcon
            simp at hcon'
          rw [ih.1 hnotL]; omega
    · have ih := buildNode_countNode_le M addr b h_inj h_len ht d (q ++ [true]) st p hst
      constructor
      · intro hnot; exact ih.1 (fun hp => hnot (List.IsPrefix.trans (List.prefix_append _ _) hp))
      · intro hqp
        rcases prefix_trichotomy q p hqp with rfl | hL | hR
        · have hnotR : ¬ List.IsPrefix (p ++ [true]) p := fun h => by have := h.length_le; simp at this
          rw [ih.1 hnotR]; omega
        · have hnotR : ¬ List.IsPrefix (q ++ [true]) p := by
            intro hR
            rcases hL with ⟨t1, ht1⟩; rcases hR with ⟨t2, ht2⟩
            have hcon := ht1.trans ht2.symm
            simp only [List.append_assoc, List.cons_append, List.nil_append] at hcon
            have hcon' := List.append_cancel_left hcon
            simp at hcon'
          rw [ih.1 hnotR]; omega
        · exact ih.2 hR
    · simp

def nodeOf {V : Type} (st : CState V) (m : ℕ) : List Bool :=
  (st.rev.getD (st.len - 1 - m) { gate := Gate.const 0 false, node := [] }).node

lemma nodeOf_nodesIn_lt {V : Type} {st1 st2 : CState V} {q : List Bool}
    (hn : NodesIn st1 st2 q) (h1 : st1.len = st1.rev.length) (h2 : st2.len = st2.rev.length)
    {m : ℕ} (hm : m < st1.len) :
    nodeOf st2 m = nodeOf st1 m := by
  rcases hn with ⟨pref, hrev, _⟩
  have hlen : st2.len = pref.length + st1.len := by
    have := congrArg List.length hrev
    simp only [List.length_append] at this
    omega
  simp only [nodeOf, hrev, List.getD_eq_getElem?_getD]
  have hsub : st2.len - 1 - m = pref.length + (st1.len - 1 - m) := by omega
  rw [hsub, List.getElem?_append_right (by omega)]
  simp

lemma nodeOf_nodesIn_ge {V : Type} {st1 st2 : CState V} {q : List Bool}
    (hn : NodesIn st1 st2 q) (h1 : st1.len = st1.rev.length) (h2 : st2.len = st2.rev.length)
    {m : ℕ} (hm1 : st1.len ≤ m) (hm2 : m < st2.len) :
    nodeOf st2 m = q := by
  rcases hn with ⟨pref, hrev, hnod⟩
  have hlen : st2.len = pref.length + st1.len := by
    have := congrArg List.length hrev
    simp only [List.length_append] at this
    omega
  simp only [nodeOf, hrev, List.getD_eq_getElem?_getD]
  have hidx : st2.len - 1 - m < pref.length := by omega
  rw [List.getElem?_append_left hidx, List.getElem?_eq_getElem hidx, Option.getD_some]
  exact hnod _ (List.getElem_mem hidx)

def AllEntriesOk {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) (st : CState (Bool × Fin n)) : Prop :=
  st.len = st.rev.length ∧
  ∀ e ∈ st.rev,
    (∀ v, Sum.inl v ∈ e.gate.inputs → inBagV M addr e.node v = true) ∧
    (∀ m, Sum.inr m ∈ e.gate.inputs → m < st.len ∧ List.IsPrefix e.node (nodeOf st m))

lemma allEntriesOk_emit {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) {st : CState (Bool × Fin n)} (p : List Bool)
    (g : ℕ → Gate (Bool × Fin n)) (hok : AllEntriesOk M addr st)
    (hg_v : ∀ v, Sum.inl v ∈ (g st.len).inputs → inBagV M addr p v = true)
    (hg_m : ∀ m, Sum.inr m ∈ (g st.len).inputs → m < st.len ∧ List.IsPrefix p (nodeOf st m)) :
    AllEntriesOk M addr (st.emit p g).1 := by
  have hnod := emitGate_nodesIn st p g
  have hrev := emitGate_len_eq_rev st p g hok.1
  refine ⟨hrev, fun e he => ?_⟩
  simp only [CState.emit, List.mem_cons] at he
  rcases he with rfl | he
  · exact ⟨hg_v, fun m hm => ⟨Nat.lt_succ_of_lt (hg_m m hm).1,
      (nodeOf_nodesIn_lt hnod hok.1 hrev (hg_m m hm).1) ▸ (hg_m m hm).2⟩⟩
  · refine ⟨(hok.2 e he).1, fun m hm => ⟨Nat.lt_succ_of_lt ((hok.2 e he).2 m hm).1, ?_⟩⟩
    rw [nodeOf_nodesIn_lt hnod hok.1 hrev ((hok.2 e he).2 m hm).1]
    exact ((hok.2 e he).2 m hm).2

lemma allEntriesOk_mono_wire {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) {st1 st2 : CState (Bool × Fin n)} {q : List Bool}
    (hn : NodesIn st1 st2 q) (h1 : st1.len = st1.rev.length) (h2 : st2.len = st2.rev.length)
    (hle : st1.len ≤ st2.len) {p : List Bool}
    {w : (Bool × Fin n) ⊕ ℕ}
    (hw : (∀ v, w = Sum.inl v → inBagV M addr p v = true) ∧
      (∀ m, w = Sum.inr m → m < st1.len ∧ List.IsPrefix p (nodeOf st1 m))) :
    (∀ v, w = Sum.inl v → inBagV M addr p v = true) ∧
    (∀ m, w = Sum.inr m → m < st2.len ∧ List.IsPrefix p (nodeOf st2 m)) := by
  refine ⟨hw.1, fun m hm => ?_⟩
  rcases hw.2 m hm with ⟨hm1, hpm⟩
  exact ⟨lt_of_lt_of_le hm1 hle, (nodeOf_nodesIn_lt hn h1 h2 hm1) ▸ hpm⟩

def WireOk {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) (st : CState (Bool × Fin n)) (p : List Bool)
    (w : (Bool × Fin n) ⊕ ℕ) : Prop :=
  (∀ v, w = Sum.inl v → inBagV M addr p v = true) ∧
  (∀ m, w = Sum.inr m → m < st.len ∧ List.IsPrefix p (nodeOf st m))

lemma wireOk_mono_prefix {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) {st : CState (Bool × Fin n)} {p q : List Bool}
    (hpq : List.IsPrefix p q) {w : (Bool × Fin n) ⊕ ℕ}
    (hw : WireOk M addr st q w) (hw_no_inl : ∀ v, w = Sum.inl v → False) :
    WireOk M addr st p w :=
  ⟨fun v hv => absurd hv (hw_no_inl v),
   fun m hm => ⟨(hw.2 m hm).1, List.IsPrefix.trans hpq (hw.2 m hm).2⟩⟩

lemma allEntriesOk_emitConst {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) {st : CState (Bool × Fin n)} (p : List Bool) (b : Bool)
    (hok : AllEntriesOk M addr st) :
    let res := emitConst st p b
    AllEntriesOk M addr res.1 ∧ st.len ≤ res.1.len ∧ NodesIn st res.1 p ∧
    WireOk M addr res.1 p res.2 ∧ (∀ v, res.2 = Sum.inl v → False) := by
  refine ⟨allEntriesOk_emit M addr p _ hok (by simp [Gate.inputs]) (by simp [Gate.inputs]),
    by simp [emitConst, CState.emit], emitConst_nodesIn st p b, ?_, by simp [emitConst, CState.emit]⟩
  refine ⟨by simp [emitConst, CState.emit], fun m hm => ?_⟩
  simp only [emitConst, CState.emit, Sum.inr.injEq] at hm
  subst hm
  refine ⟨by simp [emitConst, CState.emit], ?_⟩
  rw [nodeOf_nodesIn_ge (emitConst_nodesIn st p b) hok.1
    (emitGate_len_eq_rev st p _ hok.1) le_rfl (by dsimp [emitConst, CState.emit]; omega)]

lemma allEntriesOk_emitNot {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) {st : CState (Bool × Fin n)} (p : List Bool)
    {a : (Bool × Fin n) ⊕ ℕ} (hok : AllEntriesOk M addr st) (ha : WireOk M addr st p a) :
    let res := emitNot st p a
    AllEntriesOk M addr res.1 ∧ st.len ≤ res.1.len ∧ NodesIn st res.1 p ∧
    WireOk M addr res.1 p res.2 ∧ (∀ v, res.2 = Sum.inl v → False) := by
  refine ⟨allEntriesOk_emit M addr p _ hok
      (fun v hv => by simp [Gate.inputs] at hv; exact ha.1 v hv.symm)
      (fun m hm => by simp [Gate.inputs] at hm; exact ha.2 m hm.symm),
    by simp [emitNot, CState.emit], emitGate_nodesIn st p _, ?_, by simp [emitNot, CState.emit]⟩
  refine ⟨by simp [emitNot, CState.emit], fun m hm => ?_⟩
  simp only [emitNot, CState.emit, Sum.inr.injEq] at hm
  subst hm
  dsimp only [emitNot]
  refine ⟨by simp [CState.emit], ?_⟩
  rw [nodeOf_nodesIn_ge (emitGate_nodesIn st p _) hok.1
    (emitGate_len_eq_rev st p _ hok.1) le_rfl (by simp [CState.emit])]

lemma allEntriesOk_emitBin {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) {st : CState (Bool × Fin n)} (p : List Bool)
    (mk : (Bool × Fin n) ⊕ ℕ → (Bool × Fin n) ⊕ ℕ → ℕ → Gate (Bool × Fin n))
    (hmk_in : ∀ a b o, (mk a b o).inputs = [a, b])
    {a b : (Bool × Fin n) ⊕ ℕ} (hok : AllEntriesOk M addr st)
    (ha : WireOk M addr st p a) (hb : WireOk M addr st p b) :
    let res := st.emit p (mk a b)
    AllEntriesOk M addr res.1 ∧ st.len ≤ res.1.len ∧ NodesIn st res.1 p ∧
    WireOk M addr res.1 p res.2 ∧ (∀ v, res.2 = Sum.inl v → False) := by
  refine ⟨allEntriesOk_emit M addr p _ hok
      (fun v hv => by
        rw [hmk_in] at hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with hv | hv
        · exact ha.1 v hv.symm
        · exact hb.1 v hv.symm)
      (fun m hm => by
        rw [hmk_in] at hm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with hm | hm
        · exact ha.2 m hm.symm
        · exact hb.2 m hm.symm),
    by simp [CState.emit], emitGate_nodesIn st p _, ?_, by simp [CState.emit]⟩
  refine ⟨by simp [CState.emit], fun m hm => ?_⟩
  simp only [CState.emit, Sum.inr.injEq] at hm
  subst hm
  refine ⟨by simp [CState.emit], ?_⟩
  rw [nodeOf_nodesIn_ge (emitGate_nodesIn st p _) hok.1
    (emitGate_len_eq_rev st p _ hok.1) le_rfl (by simp [CState.emit])]

lemma allEntriesOk_emitHalfAdder {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) {st : CState (Bool × Fin n)} (p : List Bool)
    {a b : (Bool × Fin n) ⊕ ℕ} (hok : AllEntriesOk M addr st)
    (ha : WireOk M addr st p a) (hb : WireOk M addr st p b) :
    let res := emitHalfAdder st p a b
    AllEntriesOk M addr res.1 ∧ st.len ≤ res.1.len ∧ NodesIn st res.1 p ∧
    WireOk M addr res.1 p res.2.1 ∧ WireOk M addr res.1 p res.2.2 ∧
    (∀ v, res.2.1 = Sum.inl v → False) ∧ (∀ v, res.2.2 = Sum.inl v → False) := by
  have h1 := allEntriesOk_emitBin M addr p Gate.xor (fun _ _ _ => rfl) hok ha hb
  rcases h1 with ⟨h1_ok, h1_le, h1_nod, h1_w, h1_no⟩
  have ha1 := allEntriesOk_mono_wire M addr h1_nod hok.1 h1_ok.1 h1_le ha
  have hb1 := allEntriesOk_mono_wire M addr h1_nod hok.1 h1_ok.1 h1_le hb
  have h2 := allEntriesOk_emitBin M addr p Gate.and (fun _ _ _ => rfl) h1_ok ha1 hb1
  rcases h2 with ⟨h2_ok, h2_le, h2_nod, h2_w, h2_no⟩
  exact ⟨h2_ok, le_trans h1_le h2_le, nodesIn_trans h1_nod h2_nod,
    allEntriesOk_mono_wire M addr h2_nod h1_ok.1 h2_ok.1 h2_le h1_w, h2_w, h1_no, h2_no⟩

lemma allEntriesOk_emitFullAdder {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) {st : CState (Bool × Fin n)} (p : List Bool)
    {a b c : (Bool × Fin n) ⊕ ℕ} (hok : AllEntriesOk M addr st)
    (ha : WireOk M addr st p a) (hb : WireOk M addr st p b) (hc : WireOk M addr st p c) :
    let res := emitFullAdder st p a b c
    AllEntriesOk M addr res.1 ∧ st.len ≤ res.1.len ∧ NodesIn st res.1 p ∧
    WireOk M addr res.1 p res.2.1 ∧ WireOk M addr res.1 p res.2.2 ∧
    (∀ v, res.2.1 = Sum.inl v → False) ∧ (∀ v, res.2.2 = Sum.inl v → False) := by
  have h1 := allEntriesOk_emitBin M addr p Gate.xor (fun _ _ _ => rfl) hok ha hb
  rcases h1 with ⟨h1_ok, h1_le, h1_nod, h1_w, h1_no⟩
  have h2 := allEntriesOk_emitBin M addr p Gate.xor (fun _ _ _ => rfl) h1_ok h1_w
    (allEntriesOk_mono_wire M addr h1_nod hok.1 h1_ok.1 h1_le hc)
  rcases h2 with ⟨h2_ok, h2_le, h2_nod, h2_w, h2_no⟩
  have h3 := allEntriesOk_emitBin M addr p Gate.and (fun _ _ _ => rfl) h2_ok
    (allEntriesOk_mono_wire M addr (nodesIn_trans h1_nod h2_nod) hok.1 h2_ok.1 (le_trans h1_le h2_le) ha)
    (allEntriesOk_mono_wire M addr (nodesIn_trans h1_nod h2_nod) hok.1 h2_ok.1 (le_trans h1_le h2_le) hb)
  rcases h3 with ⟨h3_ok, h3_le, h3_nod, h3_w, h3_no⟩
  have h4 := allEntriesOk_emitBin M addr p Gate.and (fun _ _ _ => rfl) h3_ok
    (allEntriesOk_mono_wire M addr (nodesIn_trans h2_nod h3_nod) h1_ok.1 h3_ok.1 (le_trans h2_le h3_le) h1_w)
    (allEntriesOk_mono_wire M addr (nodesIn_trans h1_nod (nodesIn_trans h2_nod h3_nod)) hok.1 h3_ok.1
      (le_trans h1_le (le_trans h2_le h3_le)) hc)
  rcases h4 with ⟨h4_ok, h4_le, h4_nod, h4_w, h4_no⟩
  have h5 := allEntriesOk_emitBin M addr p Gate.or (fun _ _ _ => rfl) h4_ok
    (allEntriesOk_mono_wire M addr h4_nod h3_ok.1 h4_ok.1 h4_le h3_w) h4_w
  rcases h5 with ⟨h5_ok, h5_le, h5_nod, h5_w, h5_no⟩
  exact ⟨h5_ok, le_trans h1_le (le_trans h2_le (le_trans h3_le (le_trans h4_le h5_le))),
    nodesIn_trans h1_nod (nodesIn_trans h2_nod (nodesIn_trans h3_nod (nodesIn_trans h4_nod h5_nod))),
    allEntriesOk_mono_wire M addr (nodesIn_trans h3_nod (nodesIn_trans h4_nod h5_nod)) h2_ok.1 h5_ok.1
      (le_trans h3_le (le_trans h4_le h5_le)) h2_w,
    h5_w, h2_no, h5_no⟩

lemma allEntriesOk_compressCol {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) :
    ∀ (col carries : List ((Bool × Fin n) ⊕ ℕ)) {st : CState (Bool × Fin n)} (p : List Bool),
      AllEntriesOk M addr st →
      (∀ w ∈ col, WireOk M addr st p w ∧ (∀ v, w = Sum.inl v → False)) →
      (∀ w ∈ carries, WireOk M addr st p w ∧ (∀ v, w = Sum.inl v → False)) →
      let res := compressCol st p col carries
      AllEntriesOk M addr res.1 ∧ st.len ≤ res.1.len ∧ NodesIn st res.1 p ∧
      (∀ w, res.2.1 = some w → WireOk M addr res.1 p w ∧ (∀ v, w = Sum.inl v → False)) ∧
      (∀ w ∈ res.2.2, WireOk M addr res.1 p w ∧ (∀ v, w = Sum.inl v → False))
  | [], carries, st, p, hok, _, hcar => by
    rw [compressCol]
    exact ⟨hok, le_rfl, nodesIn_refl _ _, fun _ h => by simp at h, hcar⟩
  | [a], carries, st, p, hok, hcol, hcar => by
    rw [compressCol]
    exact ⟨hok, le_rfl, nodesIn_refl _ _,
      fun w hw => by simp only [Option.some.injEq] at hw; subst hw; exact hcol a (by simp), hcar⟩
  | [a, b], carries, st, p, hok, hcol, hcar => by
    rw [compressCol]
    have hha := allEntriesOk_emitHalfAdder M addr p hok (hcol a (by simp)).1 (hcol b (by simp)).1
    rcases hha with ⟨h1_ok, h1_le, h1_nod, hs, hc, hs_no, hc_no⟩
    refine ⟨h1_ok, h1_le, h1_nod,
      fun w hw => by simp only [Option.some.injEq] at hw; subst hw; exact ⟨hs, hs_no⟩,
      fun w hw => ?_⟩
    simp only [List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact ⟨hc, hc_no⟩
    · exact ⟨allEntriesOk_mono_wire M addr h1_nod hok.1 h1_ok.1 h1_le (hcar w hw).1, (hcar w hw).2⟩
  | a :: b :: c :: rest, carries, st, p, hok, hcol, hcar => by
    have hfa := allEntriesOk_emitFullAdder M addr p hok
      (hcol a (by simp)).1 (hcol b (by simp)).1 (hcol c (by simp)).1
    rcases hfa with ⟨h1_ok, h1_le, h1_nod, hs, hcout, hs_no, hcout_no⟩
    have hrec := allEntriesOk_compressCol M addr ((emitFullAdder st p a b c).2.1 :: rest)
      ((emitFullAdder st p a b c).2.2 :: carries) p h1_ok
      (fun w hw => by
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact ⟨hs, hs_no⟩
        · exact ⟨allEntriesOk_mono_wire M addr h1_nod hok.1 h1_ok.1 h1_le (hcol w (by simp [hw])).1,
            (hcol w (by simp [hw])).2⟩)
      (fun w hw => by
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact ⟨hcout, hcout_no⟩
        · exact ⟨allEntriesOk_mono_wire M addr h1_nod hok.1 h1_ok.1 h1_le (hcar w hw).1, (hcar w hw).2⟩)
    rcases hrec with ⟨h2_ok, h2_le, h2_nod, h2_s, h2_car⟩
    rw [compressCol]
    exact ⟨h2_ok, le_trans h1_le h2_le, nodesIn_trans h1_nod h2_nod, h2_s, h2_car⟩
termination_by col => col.length

lemma allEntriesOk_compressAll {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) :
    ∀ (cols : List (List ((Bool × Fin n) ⊕ ℕ))) {st : CState (Bool × Fin n)} (p : List Bool),
      AllEntriesOk M addr st →
      (∀ col ∈ cols, ∀ w ∈ col, WireOk M addr st p w ∧ (∀ v, w = Sum.inl v → False)) →
      let res := compressAll st p cols
      AllEntriesOk M addr res.1 ∧ st.len ≤ res.1.len ∧ NodesIn st res.1 p ∧
      (∀ o ∈ res.2, ∀ w, o = some w → WireOk M addr res.1 p w ∧ (∀ v, w = Sum.inl v → False))
  | [], st, p, hok, _ => by
    rw [compressAll]
    exact ⟨hok, le_rfl, nodesIn_refl _ _, fun _ h => by simp at h⟩
  | col :: rest, st, p, hok, hcols => by
    have hcc := allEntriesOk_compressCol M addr col [] p hok (hcols col (by simp)) (fun _ h => by simp at h)
    rcases hcc with ⟨h1_ok, h1_le, h1_nod, h1_s, h1_car⟩
    set st1 := (compressCol st p col []).1
    set s? := (compressCol st p col []).2.1
    set carries := (compressCol st p col []).2.2
    let rest' := match rest with | [] => [] | next :: tail => (carries ++ next) :: tail
    have hrest'_w : ∀ c ∈ rest', ∀ w ∈ c, WireOk M addr st1 p w ∧ (∀ v, w = Sum.inl v → False) := by
      cases rest with
      | nil => intro c hc; simp [rest'] at hc
      | cons next tail =>
        intro c hc w hw
        simp only [rest', List.mem_cons] at hc
        rcases hc with rfl | hc
        · rcases List.mem_append.mp hw with hw | hw
          · exact h1_car w hw
          · exact ⟨allEntriesOk_mono_wire M addr h1_nod hok.1 h1_ok.1 h1_le (hcols next (by simp) w hw).1,
              (hcols next (by simp) w hw).2⟩
        · exact ⟨allEntriesOk_mono_wire M addr h1_nod hok.1 h1_ok.1 h1_le (hcols c (by simp [hc]) w hw).1,
            (hcols c (by simp [hc]) w hw).2⟩
    have hrec := allEntriesOk_compressAll M addr rest' p h1_ok hrest'_w
    rcases hrec with ⟨h2_ok, h2_le, h2_nod, h2_w⟩
    cases rest with
    | nil =>
      rw [compressAll]
      dsimp only [st1, s?, carries, rest'] at h1_ok h1_le h1_nod h1_s h2_ok h2_le h2_nod h2_w ⊢
      refine ⟨h2_ok, le_trans h1_le h2_le, nodesIn_trans h1_nod h2_nod, fun o ho w hw => ?_⟩
      simp only [List.mem_cons] at ho
      rcases ho with rfl | ho
      · exact ⟨allEntriesOk_mono_wire M addr h2_nod h1_ok.1 h2_ok.1 h2_le (h1_s w hw).1, (h1_s w hw).2⟩
      · exact h2_w o ho w hw
    | cons next tail =>
      rw [compressAll]
      dsimp only [st1, s?, carries, rest'] at h1_ok h1_le h1_nod h1_s h2_ok h2_le h2_nod h2_w ⊢
      refine ⟨h2_ok, le_trans h1_le h2_le, nodesIn_trans h1_nod h2_nod, fun o ho w hw => ?_⟩
      simp only [List.mem_cons] at ho
      rcases ho with rfl | ho
      · exact ⟨allEntriesOk_mono_wire M addr h2_nod h1_ok.1 h2_ok.1 h2_le (h1_s w hw).1, (h1_s w hw).2⟩
      · exact h2_w o ho w hw
termination_by cols => cols.length
decreasing_by
  cases rest <;> simp

lemma allEntriesOk_emitCmpLeStep {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) {st : CState (Bool × Fin n)} (p : List Bool)
    {acc : (Bool × Fin n) ⊕ ℕ} {o : Option ((Bool × Fin n) ⊕ ℕ)} (kbit : Bool)
    (hok : AllEntriesOk M addr st) (hacc : WireOk M addr st p acc)
    (ho : ∀ w, o = some w → WireOk M addr st p w) :
    let res := emitCmpLeStep st p acc o kbit
    AllEntriesOk M addr res.1 ∧ st.len ≤ res.1.len ∧ NodesIn st res.1 p ∧
    WireOk M addr res.1 p res.2 := by
  cases o with
  | none =>
    cases kbit with
    | false => exact ⟨hok, le_rfl, nodesIn_refl _ _, hacc⟩
    | true =>
      have hc := allEntriesOk_emitConst M addr p true hok
      exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1⟩
  | some w =>
    have hn := allEntriesOk_emitNot M addr p hok (ho w rfl)
    rcases hn with ⟨h1_ok, h1_le, h1_nod, h1_w, _⟩
    have hacc1 := allEntriesOk_mono_wire M addr h1_nod hok.1 h1_ok.1 h1_le hacc
    cases kbit with
    | false =>
      have ha := allEntriesOk_emitBin M addr p Gate.and (fun _ _ _ => rfl) h1_ok h1_w hacc1
      exact ⟨ha.1, le_trans h1_le ha.2.1, nodesIn_trans h1_nod ha.2.2.1, ha.2.2.2.1⟩
    | true =>
      have hor := allEntriesOk_emitBin M addr p Gate.or (fun _ _ _ => rfl) h1_ok h1_w hacc1
      exact ⟨hor.1, le_trans h1_le hor.2.1, nodesIn_trans h1_nod hor.2.2.1, hor.2.2.2.1⟩

lemma allEntriesOk_emitCmpLeLoop {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) :
    ∀ (xs : List (Option ((Bool × Fin n) ⊕ ℕ))) (K : ℕ) {st : CState (Bool × Fin n)}
      (p : List Bool) {acc : (Bool × Fin n) ⊕ ℕ},
      AllEntriesOk M addr st → WireOk M addr st p acc →
      (∀ o ∈ xs, ∀ w, o = some w → WireOk M addr st p w) →
      let res := emitCmpLeLoop st p acc xs K
      AllEntriesOk M addr res.1 ∧ st.len ≤ res.1.len ∧ NodesIn st res.1 p ∧
      WireOk M addr res.1 p res.2
  | [], _, st, p, acc, hok, hacc, _ => ⟨hok, le_rfl, nodesIn_refl _ _, hacc⟩
  | o :: rest, K, st, p, acc, hok, hacc, hxs => by
    have hs := allEntriesOk_emitCmpLeStep M addr p (decide (K % 2 = 1)) hok hacc (hxs o (by simp))
    rcases hs with ⟨h1_ok, h1_le, h1_nod, h1_w⟩
    have hrec := allEntriesOk_emitCmpLeLoop M addr rest (K / 2) p h1_ok h1_w
      (fun o' ho' w hw => allEntriesOk_mono_wire M addr h1_nod hok.1 h1_ok.1 h1_le
        (hxs o' (by simp [ho']) w hw))
    rcases hrec with ⟨h2_ok, h2_le, h2_nod, h2_w⟩
    exact ⟨h2_ok, le_trans h1_le h2_le, nodesIn_trans h1_nod h2_nod, h2_w⟩

lemma allEntriesOk_emitCmpLe {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) {st : CState (Bool × Fin n)} (p : List Bool)
    {xs : List (Option ((Bool × Fin n) ⊕ ℕ))} (K : ℕ)
    (hok : AllEntriesOk M addr st)
    (hxs : ∀ o ∈ xs, ∀ w, o = some w → WireOk M addr st p w) :
    let res := emitCmpLe st p xs K
    AllEntriesOk M addr res.1 ∧ st.len ≤ res.1.len ∧ NodesIn st res.1 p ∧
    WireOk M addr res.1 p res.2 := by
  have hc := allEntriesOk_emitConst M addr p true hok
  rcases hc with ⟨h0_ok, h0_le, h0_nod, h0_w, _⟩
  have hl := allEntriesOk_emitCmpLeLoop M addr xs K p h0_ok h0_w
    (fun o ho w hw => allEntriesOk_mono_wire M addr h0_nod hok.1 h0_ok.1 h0_le (hxs o ho w hw))
  exact ⟨hl.1, le_trans h0_le hl.2.1, nodesIn_trans h0_nod hl.2.2.1, hl.2.2.2⟩

lemma allEntriesOk_emitCmpGeStep {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) {st : CState (Bool × Fin n)} (p : List Bool)
    {acc : (Bool × Fin n) ⊕ ℕ} {o : Option ((Bool × Fin n) ⊕ ℕ)} (kbit : Bool)
    (hok : AllEntriesOk M addr st) (hacc : WireOk M addr st p acc)
    (ho : ∀ w, o = some w → WireOk M addr st p w) :
    let res := emitCmpGeStep st p acc o kbit
    AllEntriesOk M addr res.1 ∧ st.len ≤ res.1.len ∧ NodesIn st res.1 p ∧
    WireOk M addr res.1 p res.2 := by
  cases o with
  | none =>
    cases kbit with
    | false => exact ⟨hok, le_rfl, nodesIn_refl _ _, hacc⟩
    | true =>
      have hc := allEntriesOk_emitConst M addr p false hok
      exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1⟩
  | some w =>
    cases kbit with
    | false =>
      have hor := allEntriesOk_emitBin M addr p Gate.or (fun _ _ _ => rfl) hok (ho w rfl) hacc
      exact ⟨hor.1, hor.2.1, hor.2.2.1, hor.2.2.2.1⟩
    | true =>
      have ha := allEntriesOk_emitBin M addr p Gate.and (fun _ _ _ => rfl) hok (ho w rfl) hacc
      exact ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1⟩

lemma allEntriesOk_emitCmpGeLoop {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) :
    ∀ (xs : List (Option ((Bool × Fin n) ⊕ ℕ))) (K : ℕ) {st : CState (Bool × Fin n)}
      (p : List Bool) {acc : (Bool × Fin n) ⊕ ℕ},
      AllEntriesOk M addr st → WireOk M addr st p acc →
      (∀ o ∈ xs, ∀ w, o = some w → WireOk M addr st p w) →
      let res := emitCmpGeLoop st p acc xs K
      AllEntriesOk M addr res.1 ∧ st.len ≤ res.1.len ∧ NodesIn st res.1 p ∧
      WireOk M addr res.1 p res.2
  | [], _, st, p, acc, hok, hacc, _ => ⟨hok, le_rfl, nodesIn_refl _ _, hacc⟩
  | o :: rest, K, st, p, acc, hok, hacc, hxs => by
    have hs := allEntriesOk_emitCmpGeStep M addr p (decide (K % 2 = 1)) hok hacc (hxs o (by simp))
    rcases hs with ⟨h1_ok, h1_le, h1_nod, h1_w⟩
    have hrec := allEntriesOk_emitCmpGeLoop M addr rest (K / 2) p h1_ok h1_w
      (fun o' ho' w hw => allEntriesOk_mono_wire M addr h1_nod hok.1 h1_ok.1 h1_le
        (hxs o' (by simp [ho']) w hw))
    rcases hrec with ⟨h2_ok, h2_le, h2_nod, h2_w⟩
    exact ⟨h2_ok, le_trans h1_le h2_le, nodesIn_trans h1_nod h2_nod, h2_w⟩

lemma allEntriesOk_emitCmpGe {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) {st : CState (Bool × Fin n)} (p : List Bool)
    {xs : List (Option ((Bool × Fin n) ⊕ ℕ))} (K : ℕ)
    (hok : AllEntriesOk M addr st)
    (hxs : ∀ o ∈ xs, ∀ w, o = some w → WireOk M addr st p w) :
    let res := emitCmpGe st p xs K
    AllEntriesOk M addr res.1 ∧ st.len ≤ res.1.len ∧ NodesIn st res.1 p ∧
    WireOk M addr res.1 p res.2 := by
  have hc := allEntriesOk_emitConst M addr p true hok
  rcases hc with ⟨h0_ok, h0_le, h0_nod, h0_w, _⟩
  have hl := allEntriesOk_emitCmpGeLoop M addr xs K p h0_ok h0_w
    (fun o ho w hw => allEntriesOk_mono_wire M addr h0_nod hok.1 h0_ok.1 h0_le (hxs o ho w hw))
  exact ⟨hl.1, le_trans h0_le hl.2.1, nodesIn_trans h0_nod hl.2.2.1, hl.2.2.2⟩

lemma allEntriesOk_emitRootCmps {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) (lo hi : ℕ) :
    ∀ (xss : List (List (Option ((Bool × Fin n) ⊕ ℕ)))) {st : CState (Bool × Fin n)},
      AllEntriesOk M addr st →
      (∀ xs ∈ xss, ∀ o ∈ xs, ∀ w, o = some w → WireOk M addr st [] w) →
      let res := emitRootCmps st lo hi xss
      AllEntriesOk M addr res.1 ∧ st.len ≤ res.1.len ∧ NodesIn st res.1 [] ∧
      (∀ w ∈ res.2, WireOk M addr res.1 [] w)
  | [], st, hok, _ => ⟨hok, le_rfl, nodesIn_refl _ _, fun _ h => by simp [emitRootCmps] at h⟩
  | xs :: rest, st, hok, hxs => by
    have h1 := allEntriesOk_emitCmpGe M addr [] lo hok (hxs xs (by simp))
    rcases h1 with ⟨h1_ok, h1_le, h1_nod, h1_w⟩
    have h2 := allEntriesOk_emitCmpLe M addr [] hi h1_ok
      (fun o ho w hw => allEntriesOk_mono_wire M addr h1_nod hok.1 h1_ok.1 h1_le (hxs xs (by simp) o ho w hw))
    rcases h2 with ⟨h2_ok, h2_le, h2_nod, h2_w⟩
    have hrest := allEntriesOk_emitRootCmps M addr lo hi rest h2_ok
      (fun xs' hxs' o ho w hw => allEntriesOk_mono_wire M addr (nodesIn_trans h1_nod h2_nod) hok.1 h2_ok.1
        (le_trans h1_le h2_le) (hxs xs' (by simp [hxs']) o ho w hw))
    rcases hrest with ⟨h3_ok, h3_le, h3_nod, h3_w⟩
    refine ⟨h3_ok, le_trans h1_le (le_trans h2_le h3_le),
      nodesIn_trans h1_nod (nodesIn_trans h2_nod h3_nod), fun w hw => ?_⟩
    simp only [emitRootCmps, List.mem_cons] at hw
    rcases hw with rfl | rfl | hw
    · exact allEntriesOk_mono_wire M addr (nodesIn_trans h2_nod h3_nod) h1_ok.1 h3_ok.1 (le_trans h2_le h3_le) h1_w
    · exact allEntriesOk_mono_wire M addr h3_nod h2_ok.1 h3_ok.1 h3_le h2_w
    · exact h3_w w hw

lemma allEntriesOk_emitDiffs {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) (j : Fin r) (p : List Bool) :
    ∀ (l : List (Fin n)) {st : CState (Bool × Fin n)},
      AllEntriesOk M addr st →
      let res := emitDiffs st p addr (M j) l
      AllEntriesOk M addr res.1 ∧ st.len ≤ res.1.len ∧ NodesIn st res.1 p ∧
      (∀ w ∈ res.2, WireOk M addr res.1 p w ∧ (∀ v, w = Sum.inl v → False))
  | [], st, hok => by dsimp [emitDiffs]; exact ⟨hok, le_rfl, nodesIn_refl _ _, fun _ h => by simp at h⟩
  | i :: rest, st, hok => by
    have ih := allEntriesOk_emitDiffs M addr j p rest hok
    rcases ih with ⟨h1_ok, h1_le, h1_nod, h1_w⟩
    dsimp [emitDiffs]
    split_ifs with heq
    · have hlcp := lcp_isPrefix_both (addr (false, i)) (addr (true, M j i))
      rw [heq] at hlcp
      have hw1 : WireOk M addr (emitDiffs st p addr (M j) rest).1 p (Sum.inl (false, i)) := by
        refine ⟨fun v hv => ?_, fun _ h => by simp at h⟩
        simp only [Sum.inl.injEq] at hv; subst hv
        simp only [inBagV, decide_eq_true_eq]
        exact ⟨hlcp.1, Or.inr ⟨j, Or.inr heq.symm⟩⟩
      have hw2 : WireOk M addr (emitDiffs st p addr (M j) rest).1 p (Sum.inl (true, M j i)) := by
        refine ⟨fun v hv => ?_, fun _ h => by simp at h⟩
        simp only [Sum.inl.injEq] at hv; subst hv
        simp only [inBagV, decide_eq_true_eq]
        refine ⟨hlcp.2, Or.inr ⟨j, Or.inr ?_⟩⟩
        simp only [partner, Equiv.symm_apply_apply]
        rw [lcp_symm, heq]
      have hx := allEntriesOk_emitBin M addr p Gate.xor (fun _ _ _ => rfl) h1_ok hw1 hw2
      rcases hx with ⟨h2_ok, h2_le, h2_nod, h2_w, h2_no⟩
      refine ⟨h2_ok, le_trans h1_le h2_le, nodesIn_trans h1_nod h2_nod, fun w hw => ?_⟩
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact ⟨h2_w, h2_no⟩
      · exact ⟨allEntriesOk_mono_wire M addr h2_nod h1_ok.1 h2_ok.1 h2_le (h1_w w hw).1, (h1_w w hw).2⟩
    · exact ⟨h1_ok, h1_le, h1_nod, h1_w⟩

lemma allEntriesOk_buildBranches {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) (b : ℕ) (p : List Bool) :
    ∀ (js : List (Fin r)) (wLs wRs : List (List (Option ((Bool × Fin n) ⊕ ℕ))))
      {st : CState (Bool × Fin n)},
      AllEntriesOk M addr st →
      (∀ wL ∈ wLs, ∀ o ∈ wL, ∀ w, o = some w → WireOk M addr st p w ∧ (∀ v, w = Sum.inl v → False)) →
      (∀ wR ∈ wRs, ∀ o ∈ wR, ∀ w, o = some w → WireOk M addr st p w ∧ (∀ v, w = Sum.inl v → False)) →
      let res := buildBranches M addr b p st js wLs wRs
      AllEntriesOk M addr res.1 ∧ st.len ≤ res.1.len ∧ NodesIn st res.1 p ∧
      (∀ out ∈ res.2, ∀ o ∈ out, ∀ w, o = some w → WireOk M addr res.1 p w ∧ (∀ v, w = Sum.inl v → False))
  | [], _, _, st, hok, _, _ => by
    dsimp [buildBranches]; exact ⟨hok, le_rfl, nodesIn_refl _ _, fun _ h => by simp at h⟩
  | j :: js, wLs, wRs, st, hok, hwL, hwR => by
    have h1 := allEntriesOk_emitDiffs M addr j p (List.finRange n) hok
    rcases h1 with ⟨h1_ok, h1_le, h1_nod, h1_w⟩
    set st1 := (emitDiffs st p addr (M j) (List.finRange n)).1
    set ds := (emitDiffs st p addr (M j) (List.finRange n)).2
    have hm_w : ∀ col ∈ mergeCols b ds (wLs.headD []) (wRs.headD []),
        ∀ w ∈ col, WireOk M addr st1 p w ∧ (∀ v, w = Sum.inl v → False) := by
      have h_pair : ∀ k wL wR,
          (∀ o ∈ wL, ∀ w, o = some w → WireOk M addr st1 p w ∧ (∀ v, w = Sum.inl v → False)) →
          (∀ o ∈ wR, ∀ w, o = some w → WireOk M addr st1 p w ∧ (∀ v, w = Sum.inl v → False)) →
          ∀ col ∈ mergePairCols k wL wR, ∀ w ∈ col, WireOk M addr st1 p w ∧ (∀ v, w = Sum.inl v → False) := by
        intro k
        induction k with
        | zero => intro _ _ _ _ col hcol; simp [mergePairCols] at hcol
        | succ k ihk =>
          intro wL wR hwL1 hwR1 col hcol w hw
          simp only [mergePairCols, List.mem_cons] at hcol
          rcases hcol with rfl | hcol
          · rcases List.mem_append.mp hw with hw | hw
            · cases wL with
              | nil => simp at hw
              | cons o t => cases o with | none => simp [optToList] at hw | some u => simp [optToList] at hw; subst hw; exact hwL1 _ (by simp) _ rfl
            · cases wR with
              | nil => simp at hw
              | cons o t => cases o with | none => simp [optToList] at hw | some u => simp [optToList] at hw; subst hw; exact hwR1 _ (by simp) _ rfl
          · exact ihk wL.tail wR.tail
              (fun o ho => hwL1 o (by cases wL with | nil => simp at ho | cons _ _ => exact List.mem_cons_of_mem _ ho))
              (fun o ho => hwR1 o (by cases wR with | nil => simp at ho | cons _ _ => exact List.mem_cons_of_mem _ ho)) col hcol w hw
      have hwL0 : ∀ o ∈ wLs.headD [], ∀ w, o = some w → WireOk M addr st1 p w ∧ (∀ v, w = Sum.inl v → False) := by
        cases wLs with
        | nil => intro o ho; simp at ho
        | cons a as => intro o ho w hw; exact ⟨allEntriesOk_mono_wire M addr h1_nod hok.1 h1_ok.1 h1_le (hwL a (by simp) o ho w hw).1, (hwL a (by simp) o ho w hw).2⟩
      have hwR0 : ∀ o ∈ wRs.headD [], ∀ w, o = some w → WireOk M addr st1 p w ∧ (∀ v, w = Sum.inl v → False) := by
        cases wRs with
        | nil => intro o ho; simp at ho
        | cons a as => intro o ho w hw; exact ⟨allEntriesOk_mono_wire M addr h1_nod hok.1 h1_ok.1 h1_le (hwR a (by simp) o ho w hw).1, (hwR a (by simp) o ho w hw).2⟩
      have hp := h_pair b (wLs.headD []) (wRs.headD []) hwL0 hwR0
      dsimp [mergeCols]
      cases hmp : mergePairCols b (wLs.headD []) (wRs.headD []) with
      | nil => intro col hcol; simp at hcol
      | cons c0 rest =>
        intro col hcol w hw
        simp only [List.mem_cons] at hcol
        rcases hcol with rfl | hcol
        · rcases List.mem_append.mp hw with hw | hw
          · exact h1_w w hw
          · rw [hmp] at hp; exact hp c0 (by simp) w hw
        · rw [hmp] at hp; exact hp col (by simp [hcol]) w hw
    have h2 := allEntriesOk_compressAll M addr (mergeCols b ds (wLs.headD []) (wRs.headD [])) p h1_ok hm_w
    rcases h2 with ⟨h2_ok, h2_le, h2_nod, h2_w⟩
    set st2 := (compressAll st1 p (mergeCols b ds (wLs.headD []) (wRs.headD []))).1
    have hrec := allEntriesOk_buildBranches M addr b p js wLs.tail wRs.tail h2_ok
      (fun wL hwL' o ho w hw => by
        have hwL'' : wL ∈ wLs := by cases wLs with | nil => simp at hwL' | cons _ _ => exact List.mem_cons_of_mem _ hwL'
        exact ⟨allEntriesOk_mono_wire M addr (nodesIn_trans h1_nod h2_nod) hok.1 h2_ok.1
          (le_trans h1_le h2_le) (hwL wL hwL'' o ho w hw).1, (hwL wL hwL'' o ho w hw).2⟩)
      (fun wR hwR' o ho w hw => by
        have hwR'' : wR ∈ wRs := by cases wRs with | nil => simp at hwR' | cons _ _ => exact List.mem_cons_of_mem _ hwR'
        exact ⟨allEntriesOk_mono_wire M addr (nodesIn_trans h1_nod h2_nod) hok.1 h2_ok.1
          (le_trans h1_le h2_le) (hwR wR hwR'' o ho w hw).1, (hwR wR hwR'' o ho w hw).2⟩)
    rcases hrec with ⟨h3_ok, h3_le, h3_nod, h3_w⟩
    dsimp [buildBranches]
    refine ⟨h3_ok, le_trans h1_le (le_trans h2_le h3_le),
      nodesIn_trans h1_nod (nodesIn_trans h2_nod h3_nod), fun out hout o ho w hw => ?_⟩
    simp only [List.mem_cons] at hout
    rcases hout with rfl | hout
    · exact ⟨allEntriesOk_mono_wire M addr h3_nod h2_ok.1 h3_ok.1 h3_le (h2_w o ho w hw).1, (h2_w o ho w hw).2⟩
    · exact h3_w out hout o ho w hw

lemma allEntriesOk_buildNode {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) (b : ℕ) :
    ∀ (d : ℕ) (p : List Bool) {st : CState (Bool × Fin n)},
      AllEntriesOk M addr st →
      let res := buildNode M addr b d p st
      AllEntriesOk M addr res.1 ∧ st.len ≤ res.1.len ∧
      (∃ pref, res.1.rev = pref ++ st.rev) ∧
      (∀ out ∈ res.2, ∀ o ∈ out, ∀ w, o = some w →
        WireOk M addr res.1 p w ∧ (∀ v, w = Sum.inl v → False)) := by
  intro d
  induction d with
  | zero =>
    intro p st hok
    simp only [buildNode]
    refine ⟨hok, le_rfl, ⟨[], rfl⟩, fun out hout o ho => ?_⟩
    simp [List.mem_replicate] at hout
    rcases hout with ⟨_, rfl⟩
    simp at ho
  | succ d ih =>
    intro p st hok
    dsimp [buildNode]
    split_ifs with h1 h2 h3
    · have hL := ih (p ++ [false]) hok
      rcases hL with ⟨h1_ok, h1_le, ⟨pref1, hrev1⟩, h1_w⟩
      set st1 := (buildNode M addr b d (p ++ [false]) st).1
      set wL := (buildNode M addr b d (p ++ [false]) st).2
      have hR := ih (p ++ [true]) h1_ok
      rcases hR with ⟨h2_ok, h2_le, ⟨pref2, hrev2⟩, h2_w⟩
      set st2 := (buildNode M addr b d (p ++ [true]) st1).1
      set wR := (buildNode M addr b d (p ++ [true]) st1).2
      have h1_w' : ∀ out ∈ wL, ∀ o ∈ out, ∀ w, o = some w →
          WireOk M addr st2 p w ∧ (∀ v, w = Sum.inl v → False) := by
        intro out hout o ho w hw
        rcases h1_w out hout o ho w hw with ⟨hwok, hno⟩
        refine ⟨⟨fun v hv => absurd hv (hno v), fun m hm => ?_⟩, hno⟩
        rcases hwok.2 m hm with ⟨hm1, hpm⟩
        refine ⟨lt_of_lt_of_le hm1 h2_le, ?_⟩
        have hnode : nodeOf st2 m = nodeOf st1 m := by
          simp only [nodeOf, hrev2, List.getD_eq_getElem?_getD]
          have hlen2 : st2.len = pref2.length + st1.len := by
            have hlen_rev2 := congrArg List.length hrev2
            have := h1_ok.1; have := h2_ok.1
            simp only [List.length_append] at hlen_rev2
            omega
          have hsub : st2.len - 1 - m = pref2.length + (st1.len - 1 - m) := by omega
          rw [hsub, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
        rw [hnode]
        exact List.IsPrefix.trans (List.prefix_append _ _) hpm
      have h2_w' : ∀ out ∈ wR, ∀ o ∈ out, ∀ w, o = some w →
          WireOk M addr st2 p w ∧ (∀ v, w = Sum.inl v → False) := by
        intro out hout o ho w hw
        rcases h2_w out hout o ho w hw with ⟨hwok, hno⟩
        exact ⟨wireOk_mono_prefix M addr (List.prefix_append _ _) hwok hno, hno⟩
      have hbb := allEntriesOk_buildBranches M addr b p (List.finRange r) wL wR h2_ok h1_w' h2_w'
      rcases hbb with ⟨h3_ok, h3_le, h3_nod, h3_w⟩
      rcases h3_nod with ⟨pref3, hrev3, _⟩
      exact ⟨h3_ok, le_trans h1_le (le_trans h2_le h3_le),
        ⟨pref3 ++ pref2 ++ pref1, by rw [hrev3, hrev2, hrev1, List.append_assoc, List.append_assoc]⟩, h3_w⟩
    · have hL := ih (p ++ [false]) hok
      rcases hL with ⟨h1_ok, h1_le, h1_rev, h1_w⟩
      exact ⟨h1_ok, h1_le, h1_rev, fun out hout o ho w hw =>
        ⟨wireOk_mono_prefix M addr (List.prefix_append _ _) (h1_w out hout o ho w hw).1
          (h1_w out hout o ho w hw).2, (h1_w out hout o ho w hw).2⟩⟩
    · have hR := ih (p ++ [true]) hok
      rcases hR with ⟨h1_ok, h1_le, h1_rev, h1_w⟩
      exact ⟨h1_ok, h1_le, h1_rev, fun out hout o ho w hw =>
        ⟨wireOk_mono_prefix M addr (List.prefix_append _ _) (h1_w out hout o ho w hw).1
          (h1_w out hout o ho w hw).2, (h1_w out hout o ho w hw).2⟩⟩
    · simp only [List.mem_replicate]
      exact ⟨hok, le_rfl, ⟨[], rfl⟩, fun out hout o ho => by rcases hout with ⟨_, rfl⟩; simp at ho⟩

def outsWires {V : Type} (outs : List (List (Option (V ⊕ ℕ)))) : Finset ℕ :=
  (outs.flatten.filterMap (fun o => match o with | some (Sum.inr m) => some m | _ => none)).toFinset

lemma mem_outsWires {V : Type} {outs : List (List (Option (V ⊕ ℕ)))} {m : ℕ} :
    m ∈ outsWires outs ↔ ∃ out ∈ outs, some (Sum.inr m) ∈ out := by
  simp only [outsWires, List.mem_toFinset, List.mem_filterMap, List.mem_flatten]
  constructor
  · rintro ⟨o, ⟨out, hout, ho⟩, hmatch⟩
    rcases o with _ | (v | m') <;> simp at hmatch
    subst hmatch
    exact ⟨out, hout, ho⟩
  · rintro ⟨out, hout, hm⟩
    exact ⟨some (Sum.inr m), ⟨out, hout, hm⟩, rfl⟩

lemma outsWires_card_le {V : Type} (outs : List (List (Option (V ⊕ ℕ)))) (r b : ℕ)
    (hlen : outs.length ≤ r) (hout : ∀ out ∈ outs, out.length ≤ b) :
    (outsWires outs).card ≤ r * b := by
  have h1 : (outs.map List.length).sum ≤ outs.length * b := by
    clear hlen
    induction outs with
    | nil => simp
    | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have h_ih := ih (fun x hx => hout x (List.mem_cons_of_mem _ hx))
      have h_a := hout a List.mem_cons_self
      nlinarith
  calc (outsWires outs).card
      ≤ (outs.flatten.filterMap (fun o => match o with | some (Sum.inr m) => some m | _ => none)).length :=
        List.toFinset_card_le _
    _ ≤ outs.flatten.length := List.length_filterMap_le _ _
    _ = (outs.map List.length).sum := List.length_flatten
    _ ≤ outs.length * b := h1
    _ ≤ r * b := Nat.mul_le_mul_right b hlen

def cutWires {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) (b : ℕ) (u : List Bool) :
    ℕ → List Bool → CState (Bool × Fin n) → Finset ℕ
  | 0, _, _ => ∅
  | d + 1, q, st =>
    if occ addr (q ++ [false]) && occ addr (q ++ [true]) then
      let r1 := buildNode M addr b d (q ++ [false]) st
      let r2 := buildNode M addr b d (q ++ [true]) r1.1
      (if q = u then outsWires r1.2 else cutWires M addr b u d (q ++ [false]) st) ∪
      (if q = u then outsWires r2.2 else cutWires M addr b u d (q ++ [true]) r1.1)
    else if occ addr (q ++ [false]) then
      let r1 := buildNode M addr b d (q ++ [false]) st
      if q = u then outsWires r1.2 else cutWires M addr b u d (q ++ [false]) st
    else if occ addr (q ++ [true]) then
      let r2 := buildNode M addr b d (q ++ [true]) st
      if q = u then outsWires r2.2 else cutWires M addr b u d (q ++ [true]) st
    else ∅

lemma buildBranches_outs_length {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) (b : ℕ) (p : List Bool) :
    ∀ (js : List (Fin r)) (wLs wRs : List (List (Option ((Bool × Fin n) ⊕ ℕ))))
      (st : CState (Bool × Fin n)),
      (buildBranches M addr b p st js wLs wRs).2.length = js.length
  | [], _, _, _ => by simp [buildBranches]
  | j :: js, wLs, wRs, st => by
    dsimp [buildBranches]
    rw [buildBranches_outs_length M addr b p js wLs.tail wRs.tail _]

lemma buildNode_outs_length {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) (b : ℕ) :
    ∀ (d : ℕ) (q : List Bool) (st : CState (Bool × Fin n)),
      (buildNode M addr b d q st).2.length = r
  | 0, _, _ => by simp [buildNode]
  | d + 1, q, st => by
    dsimp [buildNode]
    split_ifs
    · rw [buildBranches_outs_length, List.length_finRange]
    · exact buildNode_outs_length M addr b d (q ++ [false]) st
    · exact buildNode_outs_length M addr b d (q ++ [true]) st
    · simp

lemma cutWires_card_le {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) (b : ℕ) (u : List Bool) :
    ∀ (d : ℕ) (q : List Bool) (st : CState (Bool × Fin n)),
      (¬ List.IsPrefix q u → cutWires M addr b u d q st = ∅) ∧
      (List.IsPrefix q u → (cutWires M addr b u d q st).card ≤ 2 * r * b)
  | 0, _, _ => by simp [cutWires]
  | d + 1, q, st => by
    dsimp [cutWires]
    by_cases h1 : (occ addr (q ++ [false]) && occ addr (q ++ [true])) = true
    · simp only [h1, ↓reduceIte]
      have ihL := cutWires_card_le M addr b u d (q ++ [false]) st
      have ihR := cutWires_card_le M addr b u d (q ++ [true]) (buildNode M addr b d (q ++ [false]) st).1
      have hlen1 : (outsWires (buildNode M addr b d (q ++ [false]) st).2).card ≤ r * b :=
        outsWires_card_le _ r b (le_of_eq (buildNode_outs_length M addr b d (q ++ [false]) st))
          (buildNode_outs_len_le M addr b d (q ++ [false]) st)
      have hlen2 : (outsWires (buildNode M addr b d (q ++ [true])
          (buildNode M addr b d (q ++ [false]) st).1).2).card ≤ r * b :=
        outsWires_card_le _ r b (le_of_eq (buildNode_outs_length M addr b d (q ++ [true]) _))
          (buildNode_outs_len_le M addr b d (q ++ [true]) _)
      constructor
      · intro hnot
        have hne : q ≠ u := fun heq => hnot (heq ▸ List.prefix_refl _)
        have hnotL : ¬ List.IsPrefix (q ++ [false]) u :=
          fun hp => hnot (List.IsPrefix.trans (List.prefix_append _ _) hp)
        have hnotR : ¬ List.IsPrefix (q ++ [true]) u :=
          fun hp => hnot (List.IsPrefix.trans (List.prefix_append _ _) hp)
        simp only [hne, ↓reduceIte, ihL.1 hnotL, ihR.1 hnotR, Finset.union_empty]
      · intro hqu
        rcases prefix_trichotomy q u hqu with rfl | hL | hR
        · simp only [↓reduceIte]
          calc (outsWires (buildNode M addr b d (u ++ [false]) st).2 ∪
                  outsWires (buildNode M addr b d (u ++ [true]) (buildNode M addr b d (u ++ [false]) st).1).2).card
              ≤ (outsWires _).card + (outsWires _).card := Finset.card_union_le _ _
            _ ≤ r * b + r * b := Nat.add_le_add hlen1 hlen2
            _ = 2 * r * b := by ring
        · have hne : q ≠ u := fun heq => by subst heq; have := hL.length_le; simp at this
          have hnotR : ¬ List.IsPrefix (q ++ [true]) u := by
            intro hR
            rcases hL with ⟨t1, ht1⟩; rcases hR with ⟨t2, ht2⟩
            have hcon := ht1.trans ht2.symm
            simp only [List.append_assoc, List.cons_append, List.nil_append] at hcon
            have hcon' := List.append_cancel_left hcon
            simp at hcon'
          simp only [hne, ↓reduceIte, ihR.1 hnotR, Finset.union_empty]
          exact ihL.2 hL
        · have hne : q ≠ u := fun heq => by subst heq; have := hR.length_le; simp at this
          have hnotL : ¬ List.IsPrefix (q ++ [false]) u := by
            intro hL
            rcases hL with ⟨t1, ht1⟩; rcases hR with ⟨t2, ht2⟩
            have hcon := ht1.trans ht2.symm
            simp only [List.append_assoc, List.cons_append, List.nil_append] at hcon
            have hcon' := List.append_cancel_left hcon
            simp at hcon'
          simp only [hne, ↓reduceIte, ihL.1 hnotL, Finset.empty_union]
          exact ihR.2 hR
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      by_cases h2 : occ addr (q ++ [false]) = true
      · simp only [h2, ↓reduceIte]
        have ihL := cutWires_card_le M addr b u d (q ++ [false]) st
        have hlen1 : (outsWires (buildNode M addr b d (q ++ [false]) st).2).card ≤ r * b :=
          outsWires_card_le _ r b (le_of_eq (buildNode_outs_length M addr b d (q ++ [false]) st))
            (buildNode_outs_len_le M addr b d (q ++ [false]) st)
        constructor
        · intro hnot
          have hne : q ≠ u := fun heq => hnot (heq ▸ List.prefix_refl _)
          have hnotL : ¬ List.IsPrefix (q ++ [false]) u :=
            fun hp => hnot (List.IsPrefix.trans (List.prefix_append _ _) hp)
          simp only [hne, ↓reduceIte, ihL.1 hnotL]
        · intro hqu
          rcases prefix_trichotomy q u hqu with rfl | hL | hR
          · simp only [↓reduceIte]; nlinarith
          · have hne : q ≠ u := fun heq => by subst heq; have := hL.length_le; simp at this
            simp only [hne, ↓reduceIte]; exact ihL.2 hL
          · have hne : q ≠ u := fun heq => by subst heq; have := hR.length_le; simp at this
            have hnotL : ¬ List.IsPrefix (q ++ [false]) u := by
              intro hL
              rcases hL with ⟨t1, ht1⟩; rcases hR with ⟨t2, ht2⟩
              have hcon := ht1.trans ht2.symm
              simp only [List.append_assoc, List.cons_append, List.nil_append] at hcon
              have hcon' := List.append_cancel_left hcon
              simp at hcon'
            simp only [hne, ↓reduceIte, ihL.1 hnotL]; simp
      · simp only [h2, Bool.false_eq_true, ↓reduceIte]
        by_cases h3 : occ addr (q ++ [true]) = true
        · simp only [h3, ↓reduceIte]
          have ihR := cutWires_card_le M addr b u d (q ++ [true]) st
          have hlen2 : (outsWires (buildNode M addr b d (q ++ [true]) st).2).card ≤ r * b :=
            outsWires_card_le _ r b (le_of_eq (buildNode_outs_length M addr b d (q ++ [true]) st))
              (buildNode_outs_len_le M addr b d (q ++ [true]) st)
          constructor
          · intro hnot
            have hne : q ≠ u := fun heq => hnot (heq ▸ List.prefix_refl _)
            have hnotR : ¬ List.IsPrefix (q ++ [true]) u :=
              fun hp => hnot (List.IsPrefix.trans (List.prefix_append _ _) hp)
            simp only [hne, ↓reduceIte, ihR.1 hnotR]
          · intro hqu
            rcases prefix_trichotomy q u hqu with rfl | hL | hR
            · simp only [↓reduceIte]; nlinarith
            · have hne : q ≠ u := fun heq => by subst heq; have := hL.length_le; simp at this
              have hnotR : ¬ List.IsPrefix (q ++ [true]) u := by
                intro hR
                rcases hL with ⟨t1, ht1⟩; rcases hR with ⟨t2, ht2⟩
                have hcon := ht1.trans ht2.symm
                simp only [List.append_assoc, List.cons_append, List.nil_append] at hcon
                have hcon' := List.append_cancel_left hcon
                simp at hcon'
              simp only [hne, ↓reduceIte, ihR.1 hnotR]; simp
            · have hne : q ≠ u := fun heq => by subst heq; have := hR.length_le; simp at this
              simp only [hne, ↓reduceIte]; exact ihR.2 hR
        · simp [h3]

def InputsIn {V : Type} (st1 st2 : CState V) (S : Set ℕ) : Prop :=
  ∀ e ∈ st2.rev, e ∈ st1.rev ∨ ∀ m, Sum.inr m ∈ e.gate.inputs → m < st1.len → m ∈ S

lemma inputsIn_refl {V : Type} (st : CState V) (S : Set ℕ) : InputsIn st st S :=
  fun _ h => Or.inl h

lemma inputsIn_trans {V : Type} {st1 st2 st3 : CState V} {S1 S2 : Set ℕ}
    (hle : st1.len ≤ st2.len) (h12 : InputsIn st1 st2 S1) (h23 : InputsIn st2 st3 S2)
    (hS : ∀ m ∈ S2, m ∈ S1 ∨ st1.len ≤ m) :
    InputsIn st1 st3 S1 := by
  intro e he
  rcases h23 e he with he2 | he2
  · exact h12 e he2
  · right
    intro m hm hm1
    rcases hS m (he2 m hm (lt_of_lt_of_le hm1 hle)) with h | h
    · exact h
    · omega

lemma inputsIn_emit {V : Type} (st : CState V) (p : List Bool) (g : ℕ → Gate V) (S : Set ℕ)
    (hg : ∀ m, Sum.inr m ∈ (g st.len).inputs → m < st.len → m ∈ S) :
    InputsIn st (st.emit p g).1 S := by
  intro e he
  simp only [CState.emit, List.mem_cons] at he
  rcases he with rfl | he
  · exact Or.inr hg
  · exact Or.inl he

lemma inputsIn_emit_wire {V : Type} (st : CState V) (p : List Bool) (g : ℕ → Gate V) (S : Set ℕ)
    (hg : ∀ m, Sum.inr m ∈ (g st.len).inputs → m < st.len → m ∈ S) :
    InputsIn st (st.emit p g).1 S ∧ st.len ≤ (st.emit p g).1.len ∧
    (∀ m, (st.emit p g).2 = Sum.inr m → m < st.len → m ∈ S) := by
  refine ⟨inputsIn_emit st p g S hg, by simp [CState.emit], fun m hm hm1 => ?_⟩
  simp only [CState.emit, Sum.inr.injEq] at hm
  omega

lemma inputsIn_emitBin {V : Type} (st : CState V) (p : List Bool)
    (mk : V ⊕ ℕ → V ⊕ ℕ → ℕ → Gate V) (hmk : ∀ a b o, (mk a b o).inputs = [a, b])
    {a b : V ⊕ ℕ} (S : Set ℕ)
    (ha : ∀ m, a = Sum.inr m → m < st.len → m ∈ S)
    (hb : ∀ m, b = Sum.inr m → m < st.len → m ∈ S) :
    InputsIn st (st.emit p (mk a b)).1 S ∧ st.len ≤ (st.emit p (mk a b)).1.len ∧
    (∀ m, (st.emit p (mk a b)).2 = Sum.inr m → m < st.len → m ∈ S) :=
  inputsIn_emit_wire st p (mk a b) S (fun m hm hm1 => by
    rw [hmk] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hm | hm
    · exact ha m hm.symm hm1
    · exact hb m hm.symm hm1)

def WIn {V : Type} (st : CState V) (S : Set ℕ) (w : V ⊕ ℕ) : Prop :=
  ∀ m, w = Sum.inr m → m < st.len ∧ m ∈ S

def liftS (n : ℕ) (S : Set ℕ) : Set ℕ := S ∪ {m | n ≤ m}

lemma wIn_lift {V : Type} {st1 st2 : CState V} {S : Set ℕ} {w : V ⊕ ℕ}
    (hle : st1.len ≤ st2.len) (hw : WIn st1 S w) : WIn st2 (liftS st1.len S) w := by
  intro m hm
  rcases hw m hm with ⟨hm1, hmS⟩
  exact ⟨lt_of_lt_of_le hm1 hle, Or.inl hmS⟩

lemma liftS_liftS {a b : ℕ} (hab : a ≤ b) (S : Set ℕ) :
    ∀ m ∈ liftS b (liftS a S), m ∈ liftS a S := by
  intro m hm
  rcases hm with (h | h) | h
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inr (le_trans hab h)

lemma inputsIn_lift {V : Type} {st1 st2 st3 : CState V} {S : Set ℕ}
    (hle : st1.len ≤ st2.len) (h12 : InputsIn st1 st2 S) (h23 : InputsIn st2 st3 (liftS st1.len S)) :
    InputsIn st1 st3 S :=
  inputsIn_trans hle h12 h23 (fun _ h => h)

lemma inputsIn_emitHalfAdder {V : Type} (st : CState V) (p : List Bool) {a b : V ⊕ ℕ} (S : Set ℕ)
    (ha : WIn st S a) (hb : WIn st S b) :
    let res := emitHalfAdder st p a b
    InputsIn st res.1 S ∧ st.len ≤ res.1.len ∧
    WIn res.1 (liftS st.len S) res.2.1 ∧ WIn res.1 (liftS st.len S) res.2.2 := by
  have h1 := inputsIn_emitBin st p Gate.xor (fun _ _ _ => rfl) S
    (fun m hm _ => (ha m hm).2) (fun m hm _ => (hb m hm).2)
  have h2 := inputsIn_emitBin (emitXor st p a b).1 p Gate.and (fun _ _ _ => rfl) (liftS st.len S)
    (fun m hm _ => (wIn_lift h1.2.1 ha m hm).2) (fun m hm _ => (wIn_lift h1.2.1 hb m hm).2)
  refine ⟨inputsIn_lift h1.2.1 h1.1 h2.1, le_trans h1.2.1 h2.2.1, ?_, ?_⟩
  · intro m hm
    dsimp only [emitHalfAdder, emitXor, emitAnd, CState.emit] at hm ⊢
    simp only [Sum.inr.injEq] at hm; subst hm
    exact ⟨by omega, Or.inr (Set.mem_setOf.mpr le_rfl)⟩
  · intro m hm
    dsimp only [emitHalfAdder, emitXor, emitAnd, CState.emit] at hm ⊢
    simp only [Sum.inr.injEq] at hm; subst hm
    exact ⟨by omega, Or.inr (Set.mem_setOf.mpr (by omega))⟩

lemma inputsIn_emitFullAdder {V : Type} (st : CState V) (p : List Bool) {a b c : V ⊕ ℕ} (S : Set ℕ)
    (ha : WIn st S a) (hb : WIn st S b) (hc : WIn st S c) :
    let res := emitFullAdder st p a b c
    InputsIn st res.1 S ∧ st.len ≤ res.1.len ∧
    WIn res.1 (liftS st.len S) res.2.1 ∧ WIn res.1 (liftS st.len S) res.2.2 := by
  have h1 := inputsIn_emitBin st p Gate.xor (fun _ _ _ => rfl) S
    (fun m hm _ => (ha m hm).2) (fun m hm _ => (hb m hm).2)
  have h2 := inputsIn_emitBin (emitXor st p a b).1 p Gate.xor (fun _ _ _ => rfl) (liftS st.len S)
    (a := (emitXor st p a b).2) (b := c)
    (fun m hm _ => by simp only [emitXor, CState.emit, Sum.inr.injEq] at hm; subst hm; exact Or.inr (Set.mem_ofPred.mpr le_rfl))
    (fun m hm _ => (wIn_lift h1.2.1 hc m hm).2)
  have h12 := inputsIn_lift h1.2.1 h1.1 h2.1
  have hle12 : st.len ≤ (emitXor (emitXor st p a b).1 p (emitXor st p a b).2 c).1.len :=
    le_trans h1.2.1 h2.2.1
  have h3 := inputsIn_emitBin (emitXor (emitXor st p a b).1 p (emitXor st p a b).2 c).1 p Gate.and (fun _ _ _ => rfl) (liftS st.len S)
    (a := a) (b := b)
    (fun m hm _ => (wIn_lift hle12 ha m hm).2) (fun m hm _ => (wIn_lift hle12 hb m hm).2)
  have h13 := inputsIn_lift hle12 h12 h3.1
  have hle13 := le_trans hle12 h3.2.1
  have h4 := inputsIn_emitBin (emitAnd (emitXor (emitXor st p a b).1 p (emitXor st p a b).2 c).1 p a b).1 p Gate.and (fun _ _ _ => rfl) (liftS st.len S)
    (a := (emitXor st p a b).2) (b := c)
    (fun m hm _ => by simp only [emitXor, CState.emit, Sum.inr.injEq] at hm; subst hm; exact Or.inr (Set.mem_setOf.mpr le_rfl))
    (fun m hm _ => (wIn_lift hle13 hc m hm).2)
  have h14 := inputsIn_lift hle13 h13 h4.1
  have hle14 := le_trans hle13 h4.2.1
  have h5 := inputsIn_emitBin (emitAnd (emitAnd (emitXor (emitXor st p a b).1 p (emitXor st p a b).2 c).1 p a b).1 p (emitXor st p a b).2 c).1 p Gate.or (fun _ _ _ => rfl) (liftS st.len S)
    (a := (emitAnd (emitXor (emitXor st p a b).1 p (emitXor st p a b).2 c).1 p a b).2)
    (b := (emitAnd (emitAnd (emitXor (emitXor st p a b).1 p (emitXor st p a b).2 c).1 p a b).1 p (emitXor st p a b).2 c).2)
    (fun m hm _ => by simp only [emitAnd, emitXor, CState.emit, Sum.inr.injEq] at hm; subst hm; exact Or.inr (Set.mem_setOf.mpr (by omega)))
    (fun m hm _ => by simp only [emitAnd, emitXor, CState.emit, Sum.inr.injEq] at hm; subst hm; exact Or.inr (Set.mem_setOf.mpr (by omega)))
  refine ⟨inputsIn_lift hle14 h14 h5.1, le_trans hle14 h5.2.1, ?_, ?_⟩
  · intro m hm
    dsimp only [emitFullAdder, emitXor, emitAnd, emitOr, CState.emit] at hm ⊢
    simp only [Sum.inr.injEq] at hm; subst hm
    exact ⟨by omega, Or.inr (Set.mem_setOf.mpr (by omega))⟩
  · intro m hm
    dsimp only [emitFullAdder, emitXor, emitAnd, emitOr, CState.emit] at hm ⊢
    simp only [Sum.inr.injEq] at hm; subst hm
    exact ⟨by omega, Or.inr (Set.mem_setOf.mpr (by omega))⟩

lemma inputsIn_compressCol {V : Type} :
    ∀ (col carries : List (V ⊕ ℕ)) (st : CState V) (p : List Bool) (S : Set ℕ),
      (∀ w ∈ col, WIn st S w) → (∀ w ∈ carries, WIn st S w) →
      let res := compressCol st p col carries
      InputsIn st res.1 S ∧ st.len ≤ res.1.len ∧
      (∀ w, res.2.1 = some w → WIn res.1 (liftS st.len S) w) ∧
      (∀ w ∈ res.2.2, WIn res.1 (liftS st.len S) w)
  | [], carries, st, p, S, _, hcar => by
    rw [compressCol]
    exact ⟨inputsIn_refl _ _, le_rfl, fun _ h => by simp at h, fun w hw => wIn_lift le_rfl (hcar w hw)⟩
  | [a], carries, st, p, S, hcol, hcar => by
    rw [compressCol]
    exact ⟨inputsIn_refl _ _, le_rfl,
      fun w hw => by simp only [Option.some.injEq] at hw; subst hw; exact wIn_lift le_rfl (hcol a (by simp)),
      fun w hw => wIn_lift le_rfl (hcar w hw)⟩
  | [a, b], carries, st, p, S, hcol, hcar => by
    rw [compressCol]
    have hha := inputsIn_emitHalfAdder st p S (hcol a (by simp)) (hcol b (by simp))
    refine ⟨hha.1, hha.2.1,
      fun w hw => by simp only [Option.some.injEq] at hw; subst hw; exact hha.2.2.1,
      fun w hw => ?_⟩
    simp only [List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact hha.2.2.2
    · exact wIn_lift hha.2.1 (hcar w hw)
  | a :: b :: c :: rest, carries, st, p, S, hcol, hcar => by
    have hfa := inputsIn_emitFullAdder st p S (hcol a (by simp)) (hcol b (by simp)) (hcol c (by simp))
    have hrec := inputsIn_compressCol ((emitFullAdder st p a b c).2.1 :: rest)
      ((emitFullAdder st p a b c).2.2 :: carries) (emitFullAdder st p a b c).1 p (liftS st.len S)
      (fun w hw => by
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact hfa.2.2.1
        · exact wIn_lift hfa.2.1 (hcol w (by simp [hw])))
      (fun w hw => by
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact hfa.2.2.2
        · exact wIn_lift hfa.2.1 (hcar w hw))
    rw [compressCol]
    refine ⟨inputsIn_lift hfa.2.1 hfa.1 hrec.1, le_trans hfa.2.1 hrec.2.1, ?_, ?_⟩
    · intro w hw m hm
      rcases hrec.2.2.1 w hw m hm with ⟨hlt, hmem⟩
      exact ⟨hlt, liftS_liftS hfa.2.1 S m hmem⟩
    · intro w hw m hm
      rcases hrec.2.2.2 w hw m hm with ⟨hlt, hmem⟩
      exact ⟨hlt, liftS_liftS hfa.2.1 S m hmem⟩
termination_by col => col.length

lemma inputsIn_compressAll {V : Type} :
    ∀ (cols : List (List (V ⊕ ℕ))) (st : CState V) (p : List Bool) (S : Set ℕ),
      (∀ col ∈ cols, ∀ w ∈ col, WIn st S w) →
      let res := compressAll st p cols
      InputsIn st res.1 S ∧ st.len ≤ res.1.len ∧
      (∀ o ∈ res.2, ∀ w, o = some w → WIn res.1 (liftS st.len S) w)
  | [], st, p, S, _ => by
    rw [compressAll]; exact ⟨inputsIn_refl _ _, le_rfl, fun _ h => by simp at h⟩
  | col :: rest, st, p, S, hcols => by
    have hcc := inputsIn_compressCol col [] st p S (hcols col (by simp)) (fun _ h => by simp at h)
    set st1 := (compressCol st p col []).1
    set s? := (compressCol st p col []).2.1
    set carries := (compressCol st p col []).2.2
    let rest' := match rest with | [] => [] | next :: tail => (carries ++ next) :: tail
    have hrest'_w : ∀ c ∈ rest', ∀ w ∈ c, WIn st1 (liftS st.len S) w := by
      cases rest with
      | nil => intro c hc; simp [rest'] at hc
      | cons next tail =>
        intro c hc w hw
        simp only [rest', List.mem_cons] at hc
        rcases hc with rfl | hc
        · rcases List.mem_append.mp hw with hw | hw
          · exact hcc.2.2.2 w hw
          · exact wIn_lift hcc.2.1 (hcols next (by simp) w hw)
        · exact wIn_lift hcc.2.1 (hcols c (by simp [hc]) w hw)
    have hrec := inputsIn_compressAll rest' st1 p (liftS st.len S) hrest'_w
    cases rest with
    | nil =>
      rw [compressAll]
      dsimp only [st1, s?, carries, rest'] at hcc hrec ⊢
      refine ⟨inputsIn_lift hcc.2.1 hcc.1 hrec.1, le_trans hcc.2.1 hrec.2.1, fun o ho w hw => ?_⟩
      simp only [List.mem_cons] at ho
      rcases ho with rfl | ho
      · intro m hm
        rcases hcc.2.2.1 w hw m hm with ⟨hlt, hmem⟩
        exact ⟨lt_of_lt_of_le hlt hrec.2.1, hmem⟩
      · intro m hm
        rcases hrec.2.2 o ho w hw m hm with ⟨hlt, hmem⟩
        exact ⟨hlt, liftS_liftS hcc.2.1 S m hmem⟩
    | cons next tail =>
      rw [compressAll]
      dsimp only [st1, s?, carries, rest'] at hcc hrec ⊢
      refine ⟨inputsIn_lift hcc.2.1 hcc.1 hrec.1, le_trans hcc.2.1 hrec.2.1, fun o ho w hw => ?_⟩
      simp only [List.mem_cons] at ho
      rcases ho with rfl | ho
      · intro m hm
        rcases hcc.2.2.1 w hw m hm with ⟨hlt, hmem⟩
        exact ⟨lt_of_lt_of_le hlt hrec.2.1, hmem⟩
      · intro m hm
        rcases hrec.2.2 o ho w hw m hm with ⟨hlt, hmem⟩
        exact ⟨hlt, liftS_liftS hcc.2.1 S m hmem⟩
termination_by cols => cols.length
decreasing_by
  cases rest <;> simp

lemma inputsIn_emitConst {V : Type} (st : CState V) (p : List Bool) (b : Bool) (S : Set ℕ) :
    InputsIn st (emitConst st p b).1 S ∧ st.len ≤ (emitConst st p b).1.len ∧
    WIn (emitConst st p b).1 (liftS st.len S) (emitConst st p b).2 := by
  refine ⟨inputsIn_emit st p _ S (by simp [Gate.inputs]), by simp [emitConst, CState.emit], fun m hm => ?_⟩
  simp only [emitConst, CState.emit, Sum.inr.injEq] at hm; subst hm
  exact ⟨by simp [emitConst, CState.emit], Or.inr (Set.mem_ofPred.mpr le_rfl)⟩

lemma inputsIn_emitNot {V : Type} (st : CState V) (p : List Bool) {a : V ⊕ ℕ} (S : Set ℕ)
    (ha : WIn st S a) :
    InputsIn st (emitNot st p a).1 S ∧ st.len ≤ (emitNot st p a).1.len ∧
    WIn (emitNot st p a).1 (liftS st.len S) (emitNot st p a).2 := by
  refine ⟨inputsIn_emit st p _ S (fun m hm _ => by simp [Gate.inputs] at hm; exact (ha m hm.symm).2),
    by simp [emitNot, CState.emit], fun m hm => ?_⟩
  simp only [emitNot, CState.emit, Sum.inr.injEq] at hm; subst hm
  exact ⟨by simp [emitNot, CState.emit], Or.inr (Set.mem_ofPred.mpr le_rfl)⟩

lemma inputsIn_emitCmpLeStep {V : Type} (st : CState V) (p : List Bool) {acc : V ⊕ ℕ}
    {o : Option (V ⊕ ℕ)} (kbit : Bool) (S : Set ℕ)
    (hacc : WIn st S acc) (ho : ∀ w, o = some w → WIn st S w) :
    let res := emitCmpLeStep st p acc o kbit
    InputsIn st res.1 S ∧ st.len ≤ res.1.len ∧ WIn res.1 (liftS st.len S) res.2 := by
  cases o with
  | none =>
    cases kbit with
    | false => exact ⟨inputsIn_refl _ _, le_rfl, wIn_lift le_rfl hacc⟩
    | true => exact inputsIn_emitConst st p true S
  | some w =>
    have hn := inputsIn_emitNot st p S (ho w rfl)
    have hacc1 := wIn_lift hn.2.1 hacc
    cases kbit with
    | false =>
      have ha := inputsIn_emitBin (emitNot st p w).1 p Gate.and (fun _ _ _ => rfl) (liftS st.len S)
        (fun m hm _ => (hn.2.2 m hm).2) (fun m hm _ => (hacc1 m hm).2)
      exact ⟨inputsIn_lift hn.2.1 hn.1 ha.1, le_trans hn.2.1 ha.2.1, fun m hm => by
        simp only [emitCmpLeStep, ite_false, Bool.false_eq_true, emitAnd, CState.emit, Sum.inr.injEq] at hm; subst hm
        exact ⟨by simp [emitCmpLeStep, emitNot, emitAnd, CState.emit], Or.inr (Set.mem_ofPred.mpr hn.2.1)⟩⟩
    | true =>
      have hor := inputsIn_emitBin (emitNot st p w).1 p Gate.or (fun _ _ _ => rfl) (liftS st.len S)
        (fun m hm _ => (hn.2.2 m hm).2) (fun m hm _ => (hacc1 m hm).2)
      exact ⟨inputsIn_lift hn.2.1 hn.1 hor.1, le_trans hn.2.1 hor.2.1, fun m hm => by
        simp only [emitCmpLeStep, ite_true, emitOr, CState.emit, Sum.inr.injEq] at hm; subst hm
        exact ⟨by simp [emitCmpLeStep, emitNot, emitOr, CState.emit], Or.inr (Set.mem_ofPred.mpr hn.2.1)⟩⟩

lemma inputsIn_emitCmpLeLoop {V : Type} :
    ∀ (xs : List (Option (V ⊕ ℕ))) (K : ℕ) (st : CState V) (p : List Bool) (acc : V ⊕ ℕ) (S : Set ℕ),
      WIn st S acc → (∀ o ∈ xs, ∀ w, o = some w → WIn st S w) →
      let res := emitCmpLeLoop st p acc xs K
      InputsIn st res.1 S ∧ st.len ≤ res.1.len ∧ WIn res.1 (liftS st.len S) res.2
  | [], _, st, _, acc, S, hacc, _ => ⟨inputsIn_refl _ _, le_rfl, wIn_lift le_rfl hacc⟩
  | o :: rest, K, st, p, acc, S, hacc, hxs => by
    have hs := inputsIn_emitCmpLeStep st p (decide (K % 2 = 1)) S hacc (hxs o (by simp))
    have hrec := inputsIn_emitCmpLeLoop rest (K / 2) _ p _ (liftS st.len S) hs.2.2
      (fun o' ho' w hw => wIn_lift hs.2.1 (hxs o' (by simp [ho']) w hw))
    refine ⟨inputsIn_lift hs.2.1 hs.1 hrec.1, le_trans hs.2.1 hrec.2.1, fun m hm => ?_⟩
    rcases hrec.2.2 m hm with ⟨hlt, hmem⟩
    exact ⟨hlt, liftS_liftS hs.2.1 S m hmem⟩

lemma inputsIn_emitCmpLe {V : Type} (st : CState V) (p : List Bool) (xs : List (Option (V ⊕ ℕ)))
    (K : ℕ) (S : Set ℕ) (hxs : ∀ o ∈ xs, ∀ w, o = some w → WIn st S w) :
    InputsIn st (emitCmpLe st p xs K).1 S ∧ st.len ≤ (emitCmpLe st p xs K).1.len ∧
    WIn (emitCmpLe st p xs K).1 (liftS st.len S) (emitCmpLe st p xs K).2 := by
  have hc := inputsIn_emitConst st p true S
  have hl := inputsIn_emitCmpLeLoop xs K (emitConst st p true).1 p (emitConst st p true).2 (liftS st.len S)
    hc.2.2 (fun o ho w hw => wIn_lift hc.2.1 (hxs o ho w hw))
  refine ⟨inputsIn_lift hc.2.1 hc.1 hl.1, le_trans hc.2.1 hl.2.1, fun m hm => ?_⟩
  rcases hl.2.2 m hm with ⟨hlt, hmem⟩
  exact ⟨hlt, liftS_liftS hc.2.1 S m hmem⟩

lemma inputsIn_emitCmpGeStep {V : Type} (st : CState V) (p : List Bool) {acc : V ⊕ ℕ}
    {o : Option (V ⊕ ℕ)} (kbit : Bool) (S : Set ℕ)
    (hacc : WIn st S acc) (ho : ∀ w, o = some w → WIn st S w) :
    let res := emitCmpGeStep st p acc o kbit
    InputsIn st res.1 S ∧ st.len ≤ res.1.len ∧ WIn res.1 (liftS st.len S) res.2 := by
  cases o with
  | none =>
    cases kbit with
    | false => exact ⟨inputsIn_refl _ _, le_rfl, wIn_lift le_rfl hacc⟩
    | true => exact inputsIn_emitConst st p false S
  | some w =>
    cases kbit with
    | false =>
      have hor := inputsIn_emitBin st p Gate.or (fun _ _ _ => rfl) S
        (fun m hm _ => (ho w rfl m hm).2) (fun m hm _ => (hacc m hm).2)
      exact ⟨hor.1, hor.2.1, fun m hm => by
        simp only [emitCmpGeStep, ite_false, Bool.false_eq_true, emitOr, CState.emit, Sum.inr.injEq] at hm; subst hm
        exact ⟨by simp [emitCmpGeStep, emitOr, CState.emit], Or.inr (Set.mem_ofPred.mpr le_rfl)⟩⟩
    | true =>
      have ha := inputsIn_emitBin st p Gate.and (fun _ _ _ => rfl) S
        (fun m hm _ => (ho w rfl m hm).2) (fun m hm _ => (hacc m hm).2)
      exact ⟨ha.1, ha.2.1, fun m hm => by
        simp only [emitCmpGeStep, ite_true, emitAnd, CState.emit, Sum.inr.injEq] at hm; subst hm
        exact ⟨by simp [emitCmpGeStep, emitAnd, CState.emit], Or.inr (Set.mem_ofPred.mpr le_rfl)⟩⟩

lemma inputsIn_emitCmpGeLoop {V : Type} :
    ∀ (xs : List (Option (V ⊕ ℕ))) (K : ℕ) (st : CState V) (p : List Bool) (acc : V ⊕ ℕ) (S : Set ℕ),
      WIn st S acc → (∀ o ∈ xs, ∀ w, o = some w → WIn st S w) →
      let res := emitCmpGeLoop st p acc xs K
      InputsIn st res.1 S ∧ st.len ≤ res.1.len ∧ WIn res.1 (liftS st.len S) res.2
  | [], _, st, _, acc, S, hacc, _ => ⟨inputsIn_refl _ _, le_rfl, wIn_lift le_rfl hacc⟩
  | o :: rest, K, st, p, acc, S, hacc, hxs => by
    have hs := inputsIn_emitCmpGeStep st p (decide (K % 2 = 1)) S hacc (hxs o (by simp))
    have hrec := inputsIn_emitCmpGeLoop rest (K / 2) _ p _ (liftS st.len S) hs.2.2
      (fun o' ho' w hw => wIn_lift hs.2.1 (hxs o' (by simp [ho']) w hw))
    refine ⟨inputsIn_lift hs.2.1 hs.1 hrec.1, le_trans hs.2.1 hrec.2.1, fun m hm => ?_⟩
    rcases hrec.2.2 m hm with ⟨hlt, hmem⟩
    exact ⟨hlt, liftS_liftS hs.2.1 S m hmem⟩

lemma inputsIn_emitCmpGe {V : Type} (st : CState V) (p : List Bool) (xs : List (Option (V ⊕ ℕ)))
    (K : ℕ) (S : Set ℕ) (hxs : ∀ o ∈ xs, ∀ w, o = some w → WIn st S w) :
    InputsIn st (emitCmpGe st p xs K).1 S ∧ st.len ≤ (emitCmpGe st p xs K).1.len ∧
    WIn (emitCmpGe st p xs K).1 (liftS st.len S) (emitCmpGe st p xs K).2 := by
  have hc := inputsIn_emitConst st p true S
  have hl := inputsIn_emitCmpGeLoop xs K (emitConst st p true).1 p (emitConst st p true).2 (liftS st.len S)
    hc.2.2 (fun o ho w hw => wIn_lift hc.2.1 (hxs o ho w hw))
  refine ⟨inputsIn_lift hc.2.1 hc.1 hl.1, le_trans hc.2.1 hl.2.1, fun m hm => ?_⟩
  rcases hl.2.2 m hm with ⟨hlt, hmem⟩
  exact ⟨hlt, liftS_liftS hc.2.1 S m hmem⟩

lemma inputsIn_emitRootCmps {V : Type} (lo hi : ℕ) :
    ∀ (xss : List (List (Option (V ⊕ ℕ)))) (st : CState V) (S : Set ℕ),
      (∀ xs ∈ xss, ∀ o ∈ xs, ∀ w, o = some w → WIn st S w) →
      InputsIn st (emitRootCmps st lo hi xss).1 S ∧ st.len ≤ (emitRootCmps st lo hi xss).1.len
  | [], st, S, _ => ⟨inputsIn_refl _ _, le_rfl⟩
  | xs :: rest, st, S, hxs => by
    have h1 := inputsIn_emitCmpGe st [] xs lo S (hxs xs (by simp))
    have h2 := inputsIn_emitCmpLe (emitCmpGe st [] xs lo).1 [] xs hi (liftS st.len S)
      (fun o ho w hw => wIn_lift h1.2.1 (hxs xs (by simp) o ho w hw))
    have h12 := inputsIn_lift h1.2.1 h1.1 h2.1
    have hle12 := le_trans h1.2.1 h2.2.1
    have hrest := inputsIn_emitRootCmps lo hi rest _ (liftS st.len S)
      (fun xs' hxs' o ho w hw => wIn_lift hle12 (hxs xs' (by simp [hxs']) o ho w hw))
    exact ⟨inputsIn_lift hle12 h12 hrest.1, le_trans hle12 hrest.2⟩

lemma inputsIn_emitDiffs {n : ℕ} (addr : (Bool × Fin n) → List Bool)
    (perm : Equiv.Perm (Fin n)) (p : List Bool) (st : CState (Bool × Fin n)) (S : Set ℕ) :
    ∀ l : List (Fin n),
      InputsIn st (emitDiffs st p addr perm l).1 S ∧
      st.len ≤ (emitDiffs st p addr perm l).1.len ∧
      (∀ w ∈ (emitDiffs st p addr perm l).2, WIn (emitDiffs st p addr perm l).1 (liftS st.len S) w)
  | [] => by dsimp [emitDiffs]; exact ⟨inputsIn_refl _ _, le_rfl, fun _ h => by simp at h⟩
  | i :: rest => by
    have ih := inputsIn_emitDiffs addr perm p st S rest
    dsimp [emitDiffs]
    split_ifs
    · have hx := inputsIn_emitBin (emitDiffs st p addr perm rest).1 p Gate.xor (fun _ _ _ => rfl)
        (liftS st.len S) (a := Sum.inl (false, i)) (b := Sum.inl (true, perm i))
        (fun _ h => by simp at h) (fun _ h => by simp at h)
      refine ⟨inputsIn_lift ih.2.1 ih.1 hx.1, le_trans ih.2.1 hx.2.1, fun w hw => ?_⟩
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · intro m hm
        simp only [emitXor, CState.emit, Sum.inr.injEq] at hm; subst hm
        exact ⟨by simp [emitXor, CState.emit], Or.inr (Set.mem_ofPred.mpr ih.2.1)⟩
      · intro m hm
        rcases ih.2.2 w hw m hm with ⟨hlt, hmem⟩
        exact ⟨lt_of_lt_of_le hlt hx.2.1, hmem⟩
    · exact ih

lemma inputsIn_buildBranches {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) (b : ℕ) (p : List Bool) :
    ∀ (js : List (Fin r)) (wLs wRs : List (List (Option ((Bool × Fin n) ⊕ ℕ))))
      (st : CState (Bool × Fin n)) (S : Set ℕ),
      (∀ wL ∈ wLs, ∀ o ∈ wL, ∀ w, o = some w → WIn st S w) →
      (∀ wR ∈ wRs, ∀ o ∈ wR, ∀ w, o = some w → WIn st S w) →
      InputsIn st (buildBranches M addr b p st js wLs wRs).1 S ∧
      st.len ≤ (buildBranches M addr b p st js wLs wRs).1.len ∧
      (∀ out ∈ (buildBranches M addr b p st js wLs wRs).2,
        ∀ o ∈ out, ∀ w, o = some w → WIn (buildBranches M addr b p st js wLs wRs).1 (liftS st.len S) w)
  | [], _, _, st, S, _, _ => by
    dsimp [buildBranches]; exact ⟨inputsIn_refl _ _, le_rfl, fun _ h => by simp at h⟩
  | j :: js, wLs, wRs, st, S, hwL, hwR => by
    have h1 := inputsIn_emitDiffs addr (M j) p st S (List.finRange n)
    set st1 := (emitDiffs st p addr (M j) (List.finRange n)).1
    set ds := (emitDiffs st p addr (M j) (List.finRange n)).2
    have hm_w : ∀ col ∈ mergeCols b ds (wLs.headD []) (wRs.headD []),
        ∀ w ∈ col, WIn st1 (liftS st.len S) w := by
      have h_pair : ∀ k wL wR,
          (∀ o ∈ wL, ∀ w, o = some w → WIn st1 (liftS st.len S) w) →
          (∀ o ∈ wR, ∀ w, o = some w → WIn st1 (liftS st.len S) w) →
          ∀ col ∈ mergePairCols k wL wR, ∀ w ∈ col, WIn st1 (liftS st.len S) w := by
        intro k
        induction k with
        | zero => intro _ _ _ _ col hcol; simp [mergePairCols] at hcol
        | succ k ihk =>
          intro wL wR hwL1 hwR1 col hcol w hw
          simp only [mergePairCols, List.mem_cons] at hcol
          rcases hcol with rfl | hcol
          · rcases List.mem_append.mp hw with hw | hw
            · cases wL with
              | nil => simp at hw
              | cons o t => cases o with | none => simp [optToList] at hw | some u => simp [optToList] at hw; subst hw; exact hwL1 _ (by simp) _ rfl
            · cases wR with
              | nil => simp at hw
              | cons o t => cases o with | none => simp [optToList] at hw | some u => simp [optToList] at hw; subst hw; exact hwR1 _ (by simp) _ rfl
          · exact ihk wL.tail wR.tail
              (fun o ho => hwL1 o (by cases wL with | nil => simp at ho | cons _ _ => exact List.mem_cons_of_mem _ ho))
              (fun o ho => hwR1 o (by cases wR with | nil => simp at ho | cons _ _ => exact List.mem_cons_of_mem _ ho)) col hcol w hw
      have hwL0 : ∀ o ∈ wLs.headD [], ∀ w, o = some w → WIn st1 (liftS st.len S) w := by
        cases wLs with
        | nil => intro o ho; simp at ho
        | cons a as => intro o ho w hw; exact wIn_lift h1.2.1 (hwL a (by simp) o ho w hw)
      have hwR0 : ∀ o ∈ wRs.headD [], ∀ w, o = some w → WIn st1 (liftS st.len S) w := by
        cases wRs with
        | nil => intro o ho; simp at ho
        | cons a as => intro o ho w hw; exact wIn_lift h1.2.1 (hwR a (by simp) o ho w hw)
      have hp := h_pair b (wLs.headD []) (wRs.headD []) hwL0 hwR0
      dsimp [mergeCols]
      cases hmp : mergePairCols b (wLs.headD []) (wRs.headD []) with
      | nil => intro col hcol; simp at hcol
      | cons c0 rest =>
        intro col hcol w hw
        simp only [List.mem_cons] at hcol
        rcases hcol with rfl | hcol
        · rcases List.mem_append.mp hw with hw | hw
          · exact h1.2.2 w hw
          · rw [hmp] at hp; exact hp c0 (by simp) w hw
        · rw [hmp] at hp; exact hp col (by simp [hcol]) w hw
    have h2 := inputsIn_compressAll (mergeCols b ds (wLs.headD []) (wRs.headD [])) st1 p (liftS st.len S) hm_w
    have h12 := inputsIn_lift h1.2.1 h1.1 h2.1
    have hle12 := le_trans h1.2.1 h2.2.1
    have hrec := inputsIn_buildBranches M addr b p js wLs.tail wRs.tail _ (liftS st.len S)
      (fun wL hwL' o ho w hw => wIn_lift hle12 (hwL wL (by cases wLs with | nil => simp at hwL' | cons _ _ => exact List.mem_cons_of_mem _ hwL') o ho w hw))
      (fun wR hwR' o ho w hw => wIn_lift hle12 (hwR wR (by cases wRs with | nil => simp at hwR' | cons _ _ => exact List.mem_cons_of_mem _ hwR') o ho w hw))
    dsimp [buildBranches]
    refine ⟨inputsIn_lift hle12 h12 hrec.1, le_trans hle12 hrec.2.1, fun out hout o ho w hw => ?_⟩
    simp only [List.mem_cons] at hout
    rcases hout with rfl | hout
    · intro m hm
      rcases h2.2.2 o ho w hw m hm with ⟨hlt, hmem⟩
      exact ⟨lt_of_lt_of_le hlt hrec.2.1, liftS_liftS h1.2.1 S m hmem⟩
    · intro m hm
      rcases hrec.2.2 out hout o ho w hw m hm with ⟨hlt, hmem⟩
      exact ⟨hlt, liftS_liftS hle12 S m hmem⟩

lemma entries_nodesIn {V : Type} {st1 st2 : CState V} {p : List Bool}
    (hn : NodesIn st1 st2 p) : ∀ e ∈ st2.rev, e ∈ st1.rev ∨ e.node = p := by
  rcases hn with ⟨pref, hrev, hnod⟩
  intro e he
  rw [hrev] at he
  rcases List.mem_append.mp he with h | h
  · exact Or.inr (hnod e h)
  · exact Or.inl h

lemma buildNode_node_prefix {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) (b : ℕ) :
    ∀ (d : ℕ) (q : List Bool) (st : CState (Bool × Fin n)),
      ∀ e ∈ (buildNode M addr b d q st).1.rev, e ∈ st.rev ∨ List.IsPrefix q e.node
  | 0, _, st, e, he => by simp [buildNode] at he; exact Or.inl he
  | d + 1, q, st, e, he => by
    dsimp [buildNode] at he
    split_ifs at he with h1 h2 h3
    · rcases entries_nodesIn (buildBranches_nodesIn M addr b q (List.finRange r) _ _ _) e he with he2 | hq
      · rcases buildNode_node_prefix M addr b d (q ++ [true]) _ e he2 with he1 | hqR
        · rcases buildNode_node_prefix M addr b d (q ++ [false]) st e he1 with he0 | hqL
          · exact Or.inl he0
          · exact Or.inr (List.IsPrefix.trans (List.prefix_append _ _) hqL)
        · exact Or.inr (List.IsPrefix.trans (List.prefix_append _ _) hqR)
      · exact Or.inr (hq ▸ List.prefix_refl _)
    · rcases buildNode_node_prefix M addr b d (q ++ [false]) st e he with he0 | hqL
      · exact Or.inl he0
      · exact Or.inr (List.IsPrefix.trans (List.prefix_append _ _) hqL)
    · rcases buildNode_node_prefix M addr b d (q ++ [true]) st e he with he0 | hqR
      · exact Or.inl he0
      · exact Or.inr (List.IsPrefix.trans (List.prefix_append _ _) hqR)
    · exact Or.inl he

lemma buildNode_cutWires_used {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (addr : (Bool × Fin n) → List Bool) (b : ℕ) (u : List Bool) :
    ∀ (d : ℕ) (q : List Bool) (st : CState (Bool × Fin n)),
      AllEntriesOk M addr st →
      let res := buildNode M addr b d q st
      (∀ m ∈ outsWires res.2, List.IsPrefix q u →
        (∃ b', List.IsPrefix (u ++ [b']) (nodeOf res.1 m)) → m ∈ cutWires M addr b u d q st) ∧
      (∀ e ∈ res.1.rev, e ∈ st.rev ∨
        (List.IsPrefix e.node u → ∀ m, Sum.inr m ∈ e.gate.inputs →
          (∃ b', List.IsPrefix (u ++ [b']) (nodeOf res.1 m)) → m ∈ cutWires M addr b u d q st))
  | 0, q, st, _ => by
    simp only [buildNode]
    refine ⟨fun m hm => ?_, fun e he => Or.inl he⟩
    simp [mem_outsWires, List.mem_replicate] at hm
  | d + 1, q, st, hok => by
    dsimp [buildNode, cutWires]
    by_cases h1 : (occ addr (q ++ [false]) && occ addr (q ++ [true])) = true
    · simp only [h1, ↓reduceIte]
      have ihL := buildNode_cutWires_used M addr b u d (q ++ [false]) st hok
      have hokL := allEntriesOk_buildNode M addr b d (q ++ [false]) hok
      set r1 := buildNode M addr b d (q ++ [false]) st
      have ihR := buildNode_cutWires_used M addr b u d (q ++ [true]) r1.1 hokL.1
      have hokR := allEntriesOk_buildNode M addr b d (q ++ [true]) hokL.1
      set r2 := buildNode M addr b d (q ++ [true]) r1.1
      have hbb_ok := allEntriesOk_buildBranches M addr b q (List.finRange r) r1.2 r2.2 hokR.1
        (fun out hout o ho w hw => by
          rcases hokL.2.2.2 out hout o ho w hw with ⟨hwok, hno⟩
          have h_rev : ∃ pref, r2.1.rev = pref ++ r1.1.rev := hokR.2.2.1
          rcases h_rev with ⟨pref2, hrev2⟩
          refine ⟨⟨fun v hv => absurd hv (hno v), fun m hm => ?_⟩, hno⟩
          rcases hwok.2 m hm with ⟨hm1, hpm⟩
          refine ⟨lt_of_lt_of_le hm1 hokR.2.1, ?_⟩
          have hnode : nodeOf r2.1 m = nodeOf r1.1 m := by
            simp only [nodeOf, hrev2, List.getD_eq_getElem?_getD]
            have hlen2 : r2.1.len = pref2.length + r1.1.len := by
              have hlen_rev2 := congrArg List.length hrev2
              have := hokL.1.1; have := hokR.1.1
              simp only [List.length_append] at hlen_rev2; omega
            have hsub : r2.1.len - 1 - m = pref2.length + (r1.1.len - 1 - m) := by omega
            rw [hsub, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
          rw [hnode]
          exact List.IsPrefix.trans (List.prefix_append _ _) hpm)
        (fun out hout o ho w hw =>
          ⟨wireOk_mono_prefix M addr (List.prefix_append _ _)
            (hokR.2.2.2 out hout o ho w hw).1 (hokR.2.2.2 out hout o ho w hw).2,
           (hokR.2.2.2 out hout o ho w hw).2⟩)
      have hbb_in := inputsIn_buildBranches M addr b q (List.finRange r) r1.2 r2.2 r2.1
        {m | m ∈ outsWires r1.2 ∨ m ∈ outsWires r2.2}
        (fun out hout o ho w hw m hm => by
          subst hm; subst hw
          have hwok := (hokL.2.2.2 out hout _ ho _ rfl).1
          refine ⟨lt_of_lt_of_le (hwok.2 m rfl).1 hokR.2.1, Or.inl (mem_outsWires.mpr ⟨out, hout, ho⟩)⟩)
        (fun out hout o ho w hw m hm => by
          subst hm; subst hw
          have hwok := (hokR.2.2.2 out hout _ ho _ rfl).1
          refine ⟨(hwok.2 m rfl).1, Or.inr (mem_outsWires.mpr ⟨out, hout, ho⟩)⟩)
      set r3 := buildBranches M addr b q r2.1 (List.finRange r) r1.2 r2.2
      have h_node_r1 : ∀ m, m < r1.1.len → nodeOf r3.1 m = nodeOf r1.1 m := by
        intro m hm
        rw [nodeOf_nodesIn_lt hbb_ok.2.2.1 hokR.1.1 hbb_ok.1.1 (lt_of_lt_of_le hm hokR.2.1)]
        rcases hokR.2.2.1 with ⟨pref2, hrev2⟩
        simp only [nodeOf, hrev2, List.getD_eq_getElem?_getD]
        have hlen2 : r2.1.len = pref2.length + r1.1.len := by
          have hlen_rev2 := congrArg List.length hrev2
          have := hokL.1.1; have := hokR.1.1
          simp only [List.length_append] at hlen_rev2; omega
        have hsub : r2.1.len - 1 - m = pref2.length + (r1.1.len - 1 - m) := by omega
        rw [hsub, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
      have h_node_r2 : ∀ m, m < r2.1.len → nodeOf r3.1 m = nodeOf r2.1 m :=
        fun m hm => nodeOf_nodesIn_lt hbb_ok.2.2.1 hokR.1.1 hbb_ok.1.1 hm
      have h_m_in_cut : ∀ m, (m ∈ outsWires r1.2 ∨ m ∈ outsWires r2.2) →
          List.IsPrefix q u → (∃ b', List.IsPrefix (u ++ [b']) (nodeOf r3.1 m)) →
          m ∈ (if q = u then outsWires r1.2 else cutWires M addr b u d (q ++ [false]) st) ∪
              (if q = u then outsWires r2.2 else cutWires M addr b u d (q ++ [true]) r1.1) := by
        intro m hm hqu ⟨b', hb'⟩
        rcases prefix_trichotomy q u hqu with rfl | hL | hR
        · simp only [↓reduceIte, Finset.mem_union]; exact hm
        · have hne : q ≠ u := fun heq => by subst heq; have := hL.length_le; simp at this
          simp only [hne, ↓reduceIte, Finset.mem_union]
          rcases hm with hmL | hmR
          · left
            rcases mem_outsWires.mp hmL with ⟨out, hout, ho⟩
            have hm_lt := ((hokL.2.2.2 out hout _ ho _ rfl).1.2 m rfl).1
            rw [h_node_r1 m hm_lt] at hb'
            exact ihL.1 m hmL hL ⟨b', hb'⟩
          · exfalso
            rcases mem_outsWires.mp hmR with ⟨out, hout, ho⟩
            have hqm := (hokR.2.2.2 out hout _ ho _ rfl).1.2 m rfl
            rw [h_node_r2 m hqm.1] at hb'
            have hnot : ¬ List.IsPrefix (q ++ [true]) (u ++ [b']) := by
              intro hcon
              rcases hcon with ⟨t2, ht2⟩
              have h1' := List.IsPrefix.trans hL (List.prefix_append u [b'])
              rcases h1' with ⟨t1', ht1'⟩
              have hcon2 := ht1'.trans ht2.symm
              simp only [List.append_assoc, List.cons_append, List.nil_append] at hcon2
              have hcon3 := List.append_cancel_left hcon2
              simp at hcon3
            have hsub : List.IsPrefix (q ++ [true]) (u ++ [b']) ∨ List.IsPrefix (u ++ [b']) (q ++ [true]) := by
              rcases hqm.2 with ⟨ta, hta⟩; rcases hb' with ⟨tb, htb⟩
              rw [← hta] at htb
              rcases List.append_eq_append_iff.mp htb.symm with ⟨s, hs, _⟩ | ⟨s, hs, _⟩
              · exact Or.inl ⟨s, hs.symm⟩
              · exact Or.inr ⟨s, hs.symm⟩
            rcases hsub with h | h
            · exact hnot h
            · have h1' := h.length_le; have h2' := hL.length_le; simp at h1' h2'; omega
        · have hne : q ≠ u := fun heq => by subst heq; have := hR.length_le; simp at this
          simp only [hne, ↓reduceIte, Finset.mem_union]
          rcases hm with hmL | hmR
          · exfalso
            rcases mem_outsWires.mp hmL with ⟨out, hout, ho⟩
            have hqm := (hokL.2.2.2 out hout _ ho _ rfl).1.2 m rfl
            rw [h_node_r1 m hqm.1] at hb'
            have hnot : ¬ List.IsPrefix (q ++ [false]) (u ++ [b']) := by
              intro hcon
              have h1' := List.IsPrefix.trans hR (List.prefix_append u [b'])
              rcases h1' with ⟨t1', ht1'⟩; rcases hcon with ⟨t2, ht2⟩
              have hcon2 := ht1'.trans ht2.symm
              simp only [List.append_assoc, List.cons_append, List.nil_append] at hcon2
              have hcon3 := List.append_cancel_left hcon2
              simp at hcon3
            have hsub : List.IsPrefix (q ++ [false]) (u ++ [b']) ∨ List.IsPrefix (u ++ [b']) (q ++ [false]) := by
              rcases hqm.2 with ⟨ta, hta⟩; rcases hb' with ⟨tb, htb⟩
              rw [← hta] at htb
              rcases List.append_eq_append_iff.mp htb.symm with ⟨s, hs, _⟩ | ⟨s, hs, _⟩
              · exact Or.inl ⟨s, hs.symm⟩
              · exact Or.inr ⟨s, hs.symm⟩
            rcases hsub with h | h
            · exact hnot h
            · have h1' := h.length_le; have h2' := hR.length_le; simp at h1' h2'; omega
          · right
            rcases mem_outsWires.mp hmR with ⟨out, hout, ho⟩
            have hm_lt := ((hokR.2.2.2 out hout _ ho _ rfl).1.2 m rfl).1
            rw [h_node_r2 m hm_lt] at hb'
            exact ihR.1 m hmR hR ⟨b', hb'⟩
      constructor
      · intro m hm hqu ⟨b', hb'⟩
        rcases mem_outsWires.mp hm with ⟨out, hout, ho⟩
        have hm_lt := ((hbb_ok.2.2.2 out hout _ ho _ rfl).1.2 m rfl).1
        by_cases hm2 : m < r2.1.len
        · have hmem := (hbb_in.2.2 out hout _ ho _ rfl m rfl).2
          simp only [liftS, Set.mem_union, Set.mem_setOf_eq, Set.mem_ofPred] at hmem
          rcases hmem with hmem | hle
          · exact h_m_in_cut m hmem hqu ⟨b', hb'⟩
          · omega
        · have hnode : nodeOf r3.1 m = q :=
            nodeOf_nodesIn_ge hbb_ok.2.2.1 hokR.1.1 hbb_ok.1.1 (Nat.le_of_not_lt hm2) hm_lt
          rw [hnode] at hb'
          have h1' := hb'.length_le; have h2' := hqu.length_le; simp at h1'; omega
      · intro e he
        by_cases he0 : e ∈ st.rev
        · exact Or.inl he0
        · by_cases he2 : e ∈ r2.1.rev
          · by_cases he1 : e ∈ r1.1.rev
            · rcases ihL.2 e he1 with he0' | heL
              · exact absurd he0' he0
              · right
                intro heu m hm ⟨b', hb'⟩
                have hm_lt := ((hokL.1.2 e he1).2 m hm).1
                rw [h_node_r1 m hm_lt] at hb'
                have hmem := heL heu m hm ⟨b', hb'⟩
                rcases buildNode_node_prefix M addr b d (q ++ [false]) st e he1 with h_st | h_qL
                · exact absurd h_st he0
                · have hquL : List.IsPrefix (q ++ [false]) u := List.IsPrefix.trans h_qL heu
                  have hne : q ≠ u := fun heq => by subst heq; have := hquL.length_le; simp at this
                  simp only [hne, ↓reduceIte, Finset.mem_union]; exact Or.inl hmem
            · rcases ihR.2 e he2 with he1' | heR
              · exact absurd he1' he1
              · right
                intro heu m hm ⟨b', hb'⟩
                have hm_lt := ((hokR.1.2 e he2).2 m hm).1
                rw [h_node_r2 m hm_lt] at hb'
                have hmem := heR heu m hm ⟨b', hb'⟩
                rcases buildNode_node_prefix M addr b d (q ++ [true]) r1.1 e he2 with h_r1 | h_qR
                · exact absurd h_r1 he1
                · have hquR : List.IsPrefix (q ++ [true]) u := List.IsPrefix.trans h_qR heu
                  have hne : q ≠ u := fun heq => by subst heq; have := hquR.length_le; simp at this
                  simp only [hne, ↓reduceIte, Finset.mem_union]; exact Or.inr hmem
          · right
            intro heu m hm ⟨b', hb'⟩
            have he_node : e.node = q := by
              rcases entries_nodesIn hbb_ok.2.2.1 e he with h | h
              · exact absurd h he2
              · exact h
            have he_new : ∀ m, Sum.inr m ∈ e.gate.inputs → m < r2.1.len →
                m ∈ outsWires r1.2 ∨ m ∈ outsWires r2.2 := by
              rcases hbb_in.1 e he with h | h
              · exact absurd h he2
              · exact h
            rw [he_node] at heu
            have hm_lt := (hbb_ok.1.2 e he).2 m hm |>.1
            by_cases hm2 : m < r2.1.len
            · exact h_m_in_cut m (he_new m hm hm2) heu ⟨b', hb'⟩
            · have hnode := nodeOf_nodesIn_ge hbb_ok.2.2.1 hokR.1.1 hbb_ok.1.1 (Nat.le_of_not_lt hm2) hm_lt
              rw [hnode] at hb'
              have h1' := hb'.length_le; have h2' := heu.length_le; simp at h1'; omega
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      by_cases h2 : occ addr (q ++ [false]) = true
      · simp only [h2, ↓reduceIte]
        have ihL := buildNode_cutWires_used M addr b u d (q ++ [false]) st hok
        have hokL := allEntriesOk_buildNode M addr b d (q ++ [false]) hok
        refine ⟨fun m hm hqu ⟨b', hb'⟩ => ?_, fun e he => ?_⟩
        · rcases prefix_trichotomy q u hqu with rfl | hL | hR
          · simp only [↓reduceIte]; exact hm
          · have hne : q ≠ u := fun heq => by subst heq; have := hL.length_le; simp at this
            simp only [hne, ↓reduceIte]; exact ihL.1 m hm hL ⟨b', hb'⟩
          · exfalso
            rcases mem_outsWires.mp hm with ⟨out, hout, ho⟩
            have hqm := (hokL.2.2.2 out hout _ ho _ rfl).1.2 m rfl
            have hnot : ¬ List.IsPrefix (q ++ [false]) (u ++ [b']) := by
              intro hcon
              have h1' := List.IsPrefix.trans hR (List.prefix_append u [b'])
              rcases h1' with ⟨t1', ht1'⟩; rcases hcon with ⟨t2, ht2⟩
              have hcon2 := ht1'.trans ht2.symm
              simp only [List.append_assoc, List.cons_append, List.nil_append] at hcon2
              have hcon3 := List.append_cancel_left hcon2
              simp at hcon3
            have hsub : List.IsPrefix (q ++ [false]) (u ++ [b']) ∨ List.IsPrefix (u ++ [b']) (q ++ [false]) := by
              rcases hqm.2 with ⟨ta, hta⟩; rcases hb' with ⟨tb, htb⟩
              rw [← hta] at htb
              rcases List.append_eq_append_iff.mp htb.symm with ⟨s, hs, _⟩ | ⟨s, hs, _⟩
              · exact Or.inl ⟨s, hs.symm⟩
              · exact Or.inr ⟨s, hs.symm⟩
            rcases hsub with h | h
            · exact hnot h
            · have h1' := h.length_le; have h2' := hR.length_le; simp at h1' h2'; omega
        · by_cases he0 : e ∈ st.rev
          · exact Or.inl he0
          · rcases ihL.2 e he with he0' | heL
            · exact absurd he0' he0
            · right
              intro heu m hm ⟨b', hb'⟩
              have hmem := heL heu m hm ⟨b', hb'⟩
              rcases buildNode_node_prefix M addr b d (q ++ [false]) st e he with h_st | h_qL
              · exact absurd h_st he0
              · have hquL : List.IsPrefix (q ++ [false]) u := List.IsPrefix.trans h_qL heu
                have hne : q ≠ u := fun heq => by subst heq; have := hquL.length_le; simp at this
                simp only [hne, ↓reduceIte]; exact hmem
      · simp only [h2, Bool.false_eq_true, ↓reduceIte]
        by_cases h3 : occ addr (q ++ [true]) = true
        · simp only [h3, ↓reduceIte]
          have ihR := buildNode_cutWires_used M addr b u d (q ++ [true]) st hok
          have hokR := allEntriesOk_buildNode M addr b d (q ++ [true]) hok
          refine ⟨fun m hm hqu ⟨b', hb'⟩ => ?_, fun e he => ?_⟩
          · rcases prefix_trichotomy q u hqu with rfl | hL | hR
            · simp only [↓reduceIte]; exact hm
            · exfalso
              rcases mem_outsWires.mp hm with ⟨out, hout, ho⟩
              have hqm := (hokR.2.2.2 out hout _ ho _ rfl).1.2 m rfl
              have hnot : ¬ List.IsPrefix (q ++ [true]) (u ++ [b']) := by
                intro hcon
                have h1' := List.IsPrefix.trans hL (List.prefix_append u [b'])
                rcases h1' with ⟨t1', ht1'⟩; rcases hcon with ⟨t2, ht2⟩
                have hcon2 := ht1'.trans ht2.symm
                simp only [List.append_assoc, List.cons_append, List.nil_append] at hcon2
                have hcon3 := List.append_cancel_left hcon2
                simp at hcon3
              have hsub : List.IsPrefix (q ++ [true]) (u ++ [b']) ∨ List.IsPrefix (u ++ [b']) (q ++ [true]) := by
                rcases hqm.2 with ⟨ta, hta⟩; rcases hb' with ⟨tb, htb⟩
                rw [← hta] at htb
                rcases List.append_eq_append_iff.mp htb.symm with ⟨s, hs, _⟩ | ⟨s, hs, _⟩
                · exact Or.inl ⟨s, hs.symm⟩
                · exact Or.inr ⟨s, hs.symm⟩
              rcases hsub with h | h
              · exact hnot h
              · have h1' := h.length_le; have h2' := hL.length_le; simp at h1' h2'; omega
            · have hne : q ≠ u := fun heq => by subst heq; have := hR.length_le; simp at this
              simp only [hne, ↓reduceIte]; exact ihR.1 m hm hR ⟨b', hb'⟩
          · by_cases he0 : e ∈ st.rev
            · exact Or.inl he0
            · rcases ihR.2 e he with he0' | heR
              · exact absurd he0' he0
              · right
                intro heu m hm ⟨b', hb'⟩
                have hmem := heR heu m hm ⟨b', hb'⟩
                rcases buildNode_node_prefix M addr b d (q ++ [true]) st e he with h_st | h_qR
                · exact absurd h_st he0
                · have hquR : List.IsPrefix (q ++ [true]) u := List.IsPrefix.trans h_qR heu
                  have hne : q ≠ u := fun heq => by subst heq; have := hquR.length_le; simp at this
                  simp only [hne, ↓reduceIte]; exact hmem
        · simp only [h3, Bool.false_eq_true, ↓reduceIte]; exact ⟨fun m hm => by
            simp [mem_outsWires, List.mem_replicate] at hm, fun e he => Or.inl he⟩

lemma emitCmpLeLoop_out_ge {V : Type} :
    ∀ (xs : List (Option (V ⊕ ℕ))) (L : ℕ) (st : CState V) (p : List Bool) (acc : V ⊕ ℕ) (K : ℕ),
      L ≤ st.len → (∀ m, acc = Sum.inr m → L ≤ m) →
      ∀ m, (emitCmpLeLoop st p acc xs K).2 = Sum.inr m → L ≤ m
  | [], L, st, p, acc, K, _, hacc, m, hm => hacc m hm
  | o :: rest, L, st, p, acc, K, hL, hacc, m, hm => by
    dsimp only [emitCmpLeLoop] at hm
    have hstep_le : st.len ≤ (emitCmpLeStep st p acc o (decide (K % 2 = 1))).1.len := by
      cases o <;> simp [emitCmpLeStep] <;> split_ifs <;> simp [emitConst, emitNot, emitOr, emitAnd, CState.emit] <;> omega
    have hstep_acc : ∀ m', (emitCmpLeStep st p acc o (decide (K % 2 = 1))).2 = Sum.inr m' → L ≤ m' := by
      intro m' hm'
      cases o with
      | none =>
        dsimp only [emitCmpLeStep] at hm'
        split_ifs at hm'
        · simp [emitConst, CState.emit] at hm'; omega
        · exact hacc m' hm'
      | some w =>
        dsimp only [emitCmpLeStep] at hm'
        split_ifs at hm' <;>
        · simp [emitNot, emitOr, emitAnd, CState.emit] at hm'; omega
    exact emitCmpLeLoop_out_ge rest L (emitCmpLeStep st p acc o (decide (K % 2 = 1))).1 p
      (emitCmpLeStep st p acc o (decide (K % 2 = 1))).2 (K / 2) (le_trans hL hstep_le) hstep_acc m hm

lemma emitCmpGeLoop_out_ge {V : Type} :
    ∀ (xs : List (Option (V ⊕ ℕ))) (L : ℕ) (st : CState V) (p : List Bool) (acc : V ⊕ ℕ) (K : ℕ),
      L ≤ st.len → (∀ m, acc = Sum.inr m → L ≤ m) →
      ∀ m, (emitCmpGeLoop st p acc xs K).2 = Sum.inr m → L ≤ m
  | [], L, st, p, acc, K, _, hacc, m, hm => hacc m hm
  | o :: rest, L, st, p, acc, K, hL, hacc, m, hm => by
    dsimp only [emitCmpGeLoop] at hm
    have hstep_le : st.len ≤ (emitCmpGeStep st p acc o (decide (K % 2 = 1))).1.len := by
      cases o <;> simp [emitCmpGeStep] <;> split_ifs <;> simp [emitConst, emitOr, emitAnd, CState.emit] <;> omega
    have hstep_acc : ∀ m', (emitCmpGeStep st p acc o (decide (K % 2 = 1))).2 = Sum.inr m' → L ≤ m' := by
      intro m' hm'
      cases o with
      | none =>
        dsimp only [emitCmpGeStep] at hm'
        split_ifs at hm'
        · simp [emitConst, CState.emit] at hm'; omega
        · exact hacc m' hm'
      | some w =>
        dsimp only [emitCmpGeStep] at hm'
        split_ifs at hm' <;>
        · simp [emitOr, emitAnd, CState.emit] at hm'; omega
    exact emitCmpGeLoop_out_ge rest L (emitCmpGeStep st p acc o (decide (K % 2 = 1))).1 p
      (emitCmpGeStep st p acc o (decide (K % 2 = 1))).2 (K / 2) (le_trans hL hstep_le) hstep_acc m hm

lemma emitRootCmps_out_ge {V : Type} (lo hi : ℕ) :
    ∀ (xss : List (List (Option (V ⊕ ℕ)))) (st : CState V),
      ∀ w ∈ (emitRootCmps st lo hi xss).2, ∀ m, w = Sum.inr m → st.len ≤ m
  | [], st, w, hw, m, _ => by simp [emitRootCmps] at hw
  | xs :: rest, st, w, hw, m, hm => by
    simp only [emitRootCmps, List.mem_cons] at hw
    have hge_le : st.len ≤ (emitCmpGe st [] xs lo).1.len := by
      have h0 : st.len ≤ (emitConst st [] true).1.len := by simp [emitConst, CState.emit]
      have h1 : ∀ (ys : List (Option (V ⊕ ℕ))) (s : CState V) (a : V ⊕ ℕ) (K : ℕ),
          s.len ≤ (emitCmpGeLoop s [] a ys K).1.len := by
        intro ys; induction ys with
        | nil => intro s a K; simp [emitCmpGeLoop]
        | cons y yt ih =>
          intro s a K; simp only [emitCmpGeLoop]
          have hs : s.len ≤ (emitCmpGeStep s [] a y (decide (K % 2 = 1))).1.len := by
            cases y <;> simp [emitCmpGeStep] <;> split_ifs <;> simp [emitConst, emitOr, emitAnd, CState.emit] <;> omega
          exact le_trans hs (ih _ _ _)
      exact le_trans h0 (h1 xs _ _ _)
    have hle_le : (emitCmpGe st [] xs lo).1.len ≤ (emitCmpLe (emitCmpGe st [] xs lo).1 [] xs hi).1.len := by
      have h0 : (emitCmpGe st [] xs lo).1.len ≤ (emitConst (emitCmpGe st [] xs lo).1 [] true).1.len := by
        simp [emitConst, CState.emit]
      have h1 : ∀ (ys : List (Option (V ⊕ ℕ))) (s : CState V) (a : V ⊕ ℕ) (K : ℕ),
          s.len ≤ (emitCmpLeLoop s [] a ys K).1.len := by
        intro ys; induction ys with
        | nil => intro s a K; simp [emitCmpLeLoop]
        | cons y yt ih =>
          intro s a K; simp only [emitCmpLeLoop]
          have hs : s.len ≤ (emitCmpLeStep s [] a y (decide (K % 2 = 1))).1.len := by
            cases y <;> simp [emitCmpLeStep] <;> split_ifs <;> simp [emitConst, emitNot, emitOr, emitAnd, CState.emit] <;> omega
          exact le_trans hs (ih _ _ _)
      exact le_trans h0 (h1 xs _ _ _)
    rcases hw with rfl | rfl | hw
    · exact emitCmpGeLoop_out_ge xs st.len (emitConst st [] true).1 [] (emitConst st [] true).2 lo
        (by simp [emitConst, CState.emit])
        (fun m' hm' => by simp [emitConst, CState.emit] at hm'; omega) m hm
    · exact le_trans hge_le (emitCmpLeLoop_out_ge xs (emitCmpGe st [] xs lo).1.len
        (emitConst (emitCmpGe st [] xs lo).1 [] true).1 []
        (emitConst (emitCmpGe st [] xs lo).1 [] true).2 hi
        (by simp [emitConst, CState.emit])
        (fun m' hm' => by simp [emitConst, CState.emit] at hm'; omega) m hm)
    · exact le_trans (le_trans hge_le hle_le) (emitRootCmps_out_ge lo hi rest _ w hw m hm)

end PEqualNP.Outside.L_pcx_328

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.L_pcx_328 : (∃ C : ℕ, 0 < C ∧ ∀ (n r : ℕ) (M : Fin r → Equiv.Perm (Fin n)),
    let V := Bool × Fin n
    let X := V → Bool
    let accept := fun x : X => ∀ j : Fin r,
      let D := (Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true,M j i))).card
      16 * Nat.dist (2*D) n ≤ n
    ∀ (h : ℕ) (addr : V → List Bool), Function.Injective addr →
      (∀ v : V, (addr v).length = h) →
      let crosses := fun (p : List Bool) (j : Fin r) =>
        (Finset.univ.filter (fun i : Fin n =>
          ¬ (List.IsPrefix p (addr (false,i)) ↔ List.IsPrefix p (addr (true,M j i))))).card
      ∀ t : ℕ, (∀ (p : List Bool) (j : Fin r), crosses p j ≤ t) →
        ∃ a c : ℕ,
        let Q := V ⊕ Fin a
        let G := Q ⊕ Fin c
        ∃ (clauses : Fin c → PEqualNP.ProofComplexity.Clause Q) (bag : List Bool → Finset G),
          let valid := (∀ v : G, ∃ u : List Bool, u.length ≤ h ∧ v ∈ bag u) ∧
            (∀ v : V, Sum.inl (Sum.inl v) ∈ bag (addr v)) ∧
            (∀ j : Fin c, ∀ lit ∈ clauses j, ∃ u : List Bool, u.length ≤ h ∧
              Sum.inl lit.1 ∈ bag u ∧ Sum.inr j ∈ bag u) ∧
            (∀ (u v : List Bool) (x : G), u.length ≤ h → v.length ≤ h →
              x ∈ bag u → x ∈ bag v → ∃ b : List Bool,
                List.IsPrefix b u ∧ List.IsPrefix b v ∧
                ∀ z : List Bool, List.IsPrefix b z →
                  (List.IsPrefix z u ∨ List.IsPrefix z v) → x ∈ bag z)
          let sat := fun (x : X) (y : Fin a → Bool) =>
            ∀ j : Fin c, PEqualNP.ProofComplexity.ClauseSat (Sum.elim x y) (clauses j)
          let b := Nat.clog 2 (n+1) + 1
          valid ∧ (∀ u : List Bool, u.length ≤ h → (bag u).card ≤ C*(r+1)*(t+b)) ∧
          a+c ≤ C*(r+1)*(n+1)*b ∧ (∀ j : Fin c, (clauses j).card ≤ 3) ∧
          (∀ x : X, accept x ↔ ∃ y : Fin a → Bool, sat x y) ∧
          (∀ (x : X) (y z : Fin a → Bool), sat x y → sat x z → y = z)) := by
  refine ⟨1000, by omega, fun n r M => ?_⟩
  intro V X accept h addr h_inj h_len crosses t ht
  by_cases hn : n = 0
  · subst hn
    refine ⟨0, 0, fun j => Fin.elim0 j, fun _ => ∅, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨fun v => ?_, fun v => Fin.elim0 v.2, fun j => Fin.elim0 j, fun u v x _ _ hx => by simp at hx⟩
      rcases v with (v | a') | j
      · exact Fin.elim0 v.2
      · exact Fin.elim0 a'
      · exact Fin.elim0 j
    · intro u _; simp
    · simp
    · intro j; exact Fin.elim0 j
    · intro x
      constructor
      · intro _
        exact ⟨Fin.elim0, fun j => Fin.elim0 j⟩
      · intro _ j
        have hD : (Finset.univ.filter (fun i : Fin 0 => x (false, i) ≠ x (true, M j i))).card = 0 := by
          simp
        rw [hD]; simp [Nat.dist]
    · intro x y z _ _
      funext i; exact Fin.elim0 i
  · by_cases hr : r = 0
    · subst hr
      refine ⟨0, 0, fun j => Fin.elim0 j,
        fun u => (Finset.univ.filter (fun v : V => addr v = u)).image (fun v => Sum.inl (Sum.inl v)),
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      · refine ⟨fun v => ?_, fun v => ?_, fun j => Fin.elim0 j, fun u w x _ _ hxu hxw => ?_⟩
        · rcases v with (v | a') | j
          · exact ⟨addr v, le_of_eq (h_len v), Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩⟩
          · exact Fin.elim0 a'
          · exact Fin.elim0 j
        · exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩
        · simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hxu hxw
          rcases hxu with ⟨v1, rfl, rfl⟩
          rcases hxw with ⟨v2, heq, hveq⟩
          have hv : v1 = v2 := by simpa using hveq.symm
          subst hv
          refine ⟨addr v1, List.prefix_refl _, by rw [heq], fun z hbz hzu => ?_⟩
          have hzlen : z.length = (addr v1).length := by
            rcases hzu with hzu | hzw
            · exact Nat.le_antisymm hzu.length_le hbz.length_le
            · rw [← heq] at hzw; exact Nat.le_antisymm hzw.length_le hbz.length_le
          have hzeq : z = addr v1 := List.IsPrefix.eq_of_length (by
            rcases hzu with hzu | hzw
            · exact hzu
            · rw [← heq] at hzw; exact hzw) hzlen
          rw [hzeq]
          exact Finset.mem_image.mpr ⟨v1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩
      · intro u _
        calc ((Finset.univ.filter (fun v : V => addr v = u)).image (fun v => Sum.inl (Sum.inl v))).card
            ≤ (Finset.univ.filter (fun v : V => addr v = u)).card := Finset.card_image_le
          _ ≤ 1 := Finset.card_le_one.mpr (fun v1 hv1 v2 hv2 => by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv1 hv2
              exact h_inj (hv1.trans hv2.symm))
          _ ≤ 1000 * (0 + 1) * (t + (Nat.clog 2 (n + 1) + 1)) := by nlinarith
      · simp
      · intro j; exact Fin.elim0 j
      · intro x
        constructor
        · intro _
          exact ⟨Fin.elim0, fun j => Fin.elim0 j⟩
        · intro _ j; exact Fin.elim0 j
      · intro x y z _ _; funext i; exact Fin.elim0 i
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
      have hr_pos : 0 < r := Nat.pos_of_ne_zero hr
      let b := Nat.clog 2 (n + 1) + 1
      have hb_pos : 0 < b := by omega
      have hn_lt_pow : n < 2 ^ b := by
        have h1 : n + 1 ≤ 2 ^ Nat.clog 2 (n + 1) := Nat.le_pow_clog (by omega) (n + 1)
        have h2 : 2 ^ b = 2 ^ Nat.clog 2 (n + 1) * 2 := by simp [b, pow_succ]
        omega
      let lo := (15 * n + 31) / 32
      let hi := (17 * n) / 32
      have hlo_lt : lo < 2 ^ b := by omega
      have hhi_lt : hi < 2 ^ b := by omega
      let res1 := PEqualNP.Outside.L_pcx_328.buildNode M addr b h [] (PEqualNP.Outside.L_pcx_328.CState.empty V)
      let st1 := res1.1
      let w_root := res1.2
      let res2 := PEqualNP.Outside.L_pcx_328.emitRootCmps st1 lo hi w_root
      let st2 := res2.1
      let w_cmps := res2.2
      have h_empty_inv : PEqualNP.Outside.L_pcx_328.CInv (PEqualNP.Outside.L_pcx_328.CState.empty V) := by
        simp [PEqualNP.Outside.L_pcx_328.CInv, PEqualNP.Outside.L_pcx_328.CState.empty,
          PEqualNP.Outside.L_pcx_328.WellFormedRev]
      have h_empty_ok : PEqualNP.Outside.L_pcx_328.AllEntriesOk M addr (PEqualNP.Outside.L_pcx_328.CState.empty V) := by
        simp [PEqualNP.Outside.L_pcx_328.AllEntriesOk, PEqualNP.Outside.L_pcx_328.CState.empty]
      have h_bn : ∀ x : X,
          PEqualNP.Outside.L_pcx_328.CInv st1 ∧ 0 ≤ st1.len ∧
          st1.len ≤ 12 * r * b * (PEqualNP.Outside.L_pcx_328.leavesIn addr [] - 1) +
            6 * ((List.finRange r).map (fun j => PEqualNP.Outside.L_pcx_328.subtreeCountDiffs addr (M j) [])).sum ∧
          w_root.length = r ∧
          (∀ out ∈ w_root, out.length = b ∧ ∀ o ∈ out, ∀ w, o = some w → PEqualNP.Outside.L_pcx_328.WireValid st1.len w) ∧
          (∃ suf, st1.rev = suf ++ [] ∧
            ∀ e ∈ suf, e.node.length < h ∧ PEqualNP.Outside.L_pcx_328.isBranch addr e.node = true) ∧
          (∀ j : Fin r, PEqualNP.Outside.L_pcx_328.sumOptBits (Sum.elim x (PEqualNP.Outside.L_pcx_328.evalRev x st1.rev)) (w_root[j.1]?.getD []) =
            (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, M j i))).card) := by
        intro x
        have hbs := PEqualNP.Outside.L_pcx_328.buildNode_spec x M addr h_inj h_len hb_pos h [] (by simp) h_empty_inv
        rcases hbs with ⟨h1_inv, h1_le, h1_bnd, h1_len, h1_w, h1_blen, ⟨suf, hsuf, hbr⟩, h1_val⟩
        have hleaves : PEqualNP.Outside.L_pcx_328.leavesIn addr [] = 2 * n := by
          dsimp only [V]
          simp [PEqualNP.Outside.L_pcx_328.leavesIn]
        have h2leaves : 2 ≤ PEqualNP.Outside.L_pcx_328.leavesIn addr [] := by omega
        refine ⟨h1_inv, h1_le, by simpa [st1, res1, PEqualNP.Outside.L_pcx_328.CState.empty] using h1_bnd,
          h1_len, fun out hout => ⟨h1_blen h2leaves out hout, (h1_w out hout).2⟩,
          ⟨suf, by simpa [st1, res1, PEqualNP.Outside.L_pcx_328.CState.empty] using hsuf,
            fun e he => ⟨(hbr e he).2.1, (hbr e he).2.2⟩⟩, fun j => ?_⟩
        rcases h1_val j with ⟨q, hq⟩
        rw [PEqualNP.Outside.L_pcx_328.subtreeTrueDiffs_root] at hq
        have hcard_le : (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, M j i))).card ≤ n := by
          calc (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, M j i))).card
              ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
            _ = n := Finset.card_fin n
        have hq0 : q = 0 := by
          by_contra hq_ne
          have hq1 : 1 ≤ q := Nat.pos_of_ne_zero hq_ne
          have hmul : 2 ^ b ≤ q * 2 ^ b := Nat.le_mul_of_pos_left (2 ^ b) hq1
          omega
        subst hq0; simp at hq; exact hq
      have h_bn0 := h_bn (fun _ => false)
      have h_rc : ∀ x : X,
          PEqualNP.Outside.L_pcx_328.CInv st2 ∧ st1.len ≤ st2.len ∧
          st2.len - st1.len ≤ r * (3 * b + 2) ∧
          (∀ w ∈ w_cmps, PEqualNP.Outside.L_pcx_328.WireValid st2.len w) ∧
          PEqualNP.Outside.L_pcx_328.NodesIn st1 st2 [] ∧
          ((∀ w ∈ w_cmps, Sum.elim x (PEqualNP.Outside.L_pcx_328.evalRev x st2.rev) w = true) ↔
            accept x) := by
        intro x
        have hbnx := h_bn x
        have hrc := PEqualNP.Outside.L_pcx_328.emitRootCmps_spec x lo hi b hlo_lt hhi_lt w_root hbnx.1
          (fun xs hxs => hbnx.2.2.2.2.1 xs hxs)
        rcases hrc with ⟨h2_inv, h2_le, h2_bnd, h2_w, h2_nod, h2_iff⟩
        rw [hbnx.2.2.2.1] at h2_bnd
        refine ⟨h2_inv, h2_le, h2_bnd, h2_w, h2_nod, ?_⟩
        rw [h2_iff]
        constructor
        · intro hacc j
          have hmem : w_root[j.1]?.getD [] ∈ w_root := by
            have hj : j.1 < w_root.length := by rw [hbnx.2.2.2.1]; exact j.2
            simp [List.getElem?_eq_getElem hj]
          have hbounds := hacc _ hmem
          rw [hbnx.2.2.2.2.2.2 j] at hbounds
          exact (PEqualNP.Outside.L_pcx_328.dist_iff_bounds _ n).mpr hbounds
        · intro hacc xs hxs
          rcases List.mem_iff_getElem.mp hxs with ⟨idx, hidx, rfl⟩
          have hidx' : idx < r := by rw [hbnx.2.2.2.1] at hidx; exact hidx
          have hget : w_root[idx] = w_root[(⟨idx, hidx'⟩ : Fin r).1]?.getD [] := by
            simp [List.getElem?_eq_getElem hidx]
          rw [hget, hbnx.2.2.2.2.2.2 ⟨idx, hidx'⟩]
          exact (PEqualNP.Outside.L_pcx_328.dist_iff_bounds _ n).mp (hacc ⟨idx, hidx'⟩)
      have h_rc0 := h_rc (fun _ => false)
      have ha_pos : 0 < st2.len := by
        have h0 : w_root ≠ [] := by
          intro heq
          have := h_bn0.2.2.2.1
          rw [heq] at this; simp at this; omega
        cases hwr : w_root with
        | nil => exact absurd hwr h0
        | cons xs rest =>
          have hxs_mem : xs ∈ w_root := by rw [hwr]; exact List.mem_cons_self
          have hok1 := PEqualNP.Outside.L_pcx_328.allEntriesOk_buildNode M addr b h [] h_empty_ok
          have hxs_ok : ∀ o ∈ xs, ∀ w, o = some w → PEqualNP.Outside.L_pcx_328.WireOk M addr st1 [] w :=
            fun o ho w hw => (hok1.2.2.2 xs hxs_mem o ho w hw).1
          have hc0 := PEqualNP.Outside.L_pcx_328.allEntriesOk_emitConst M addr [] true hok1.1
          have hl := PEqualNP.Outside.L_pcx_328.allEntriesOk_emitCmpGeLoop M addr xs lo [] hc0.1 hc0.2.2.2.1
            (fun o ho w hw => PEqualNP.Outside.L_pcx_328.allEntriesOk_mono_wire M addr hc0.2.2.1 hok1.1.1 hc0.1.1 hc0.2.1 (hxs_ok o ho w hw))
          have hge_ok := PEqualNP.Outside.L_pcx_328.allEntriesOk_emitCmpGe M addr [] lo hok1.1 hxs_ok
          have h2 := PEqualNP.Outside.L_pcx_328.allEntriesOk_emitCmpLe M addr [] hi hge_ok.1
            (fun o ho w hw => PEqualNP.Outside.L_pcx_328.allEntriesOk_mono_wire M addr
              hge_ok.2.2.1 hok1.1.1 hge_ok.1.1 hge_ok.2.1 (hxs_ok o ho w hw))
          have hrest := PEqualNP.Outside.L_pcx_328.allEntriesOk_emitRootCmps M addr lo hi rest h2.1
            (fun xs' hxs' o ho w hw => PEqualNP.Outside.L_pcx_328.allEntriesOk_mono_wire M addr
              (PEqualNP.Outside.L_pcx_328.nodesIn_trans hge_ok.2.2.1 h2.2.2.1)
              hok1.1.1 h2.1.1
              (le_trans hge_ok.2.1 h2.2.1)
              (hok1.2.2.2 xs' (by
                change xs' ∈ (PEqualNP.Outside.L_pcx_328.buildNode M addr b h [] (PEqualNP.Outside.L_pcx_328.CState.empty V)).2
                have hwr' : (PEqualNP.Outside.L_pcx_328.buildNode M addr b h [] (PEqualNP.Outside.L_pcx_328.CState.empty V)).2 = xs :: rest := hwr
                rw [hwr']; exact List.mem_cons_of_mem _ hxs') o ho w hw).1)
          have h_c_lt : st1.len < (PEqualNP.Outside.L_pcx_328.emitConst st1 [] true).1.len := by
            simp [PEqualNP.Outside.L_pcx_328.emitConst, PEqualNP.Outside.L_pcx_328.CState.emit]
          have h_ge_le : (PEqualNP.Outside.L_pcx_328.emitConst st1 [] true).1.len ≤
              (PEqualNP.Outside.L_pcx_328.emitCmpGe st1 [] xs lo).1.len := hl.2.1
          have h_st2 : (PEqualNP.Outside.L_pcx_328.emitCmpGe st1 [] xs lo).1.len ≤ st2.len := by
            change (PEqualNP.Outside.L_pcx_328.emitCmpGe st1 [] xs lo).1.len ≤
              (PEqualNP.Outside.L_pcx_328.emitRootCmps st1 lo hi w_root).1.len
            rw [hwr]
            dsimp [PEqualNP.Outside.L_pcx_328.emitRootCmps]
            exact le_trans h2.2.1 hrest.2.1
          omega
      have hok_bn := PEqualNP.Outside.L_pcx_328.allEntriesOk_buildNode M addr b h [] h_empty_ok
      have hok_rc := PEqualNP.Outside.L_pcx_328.allEntriesOk_emitRootCmps M addr lo hi w_root hok_bn.1
        (fun xs hxs o ho w hw => (hok_bn.2.2.2 xs hxs o ho w hw).1)
      let gateClsList : List (List Bool × PEqualNP.ProofComplexity.Clause (V ⊕ ℕ)) :=
        st2.rev.flatMap (fun e => (PEqualNP.Outside.L_pcx_328.gateClauses e.gate).map (fun cl => (e.node, cl)))
      let unitClsList : List (List Bool × PEqualNP.ProofComplexity.Clause (V ⊕ ℕ)) :=
        w_cmps.map (fun w => ([], ({(w, true)} : PEqualNP.ProofComplexity.Clause (V ⊕ ℕ))))
      let allClsList := gateClsList ++ unitClsList
      let a := st2.len
      let c := allClsList.length
      let clauses : Fin c → PEqualNP.ProofComplexity.Clause (V ⊕ Fin a) :=
        fun j => (allClsList[j.1]).2.image (fun l => (PEqualNP.Outside.L_pcx_328.castWire a ha_pos l.1, l.2))
      let bag : List Bool → Finset ((V ⊕ Fin a) ⊕ Fin c) := fun u =>
        (Finset.univ.filter (fun v : V => PEqualNP.Outside.L_pcx_328.inBagV M addr u v = true)).image (fun v => Sum.inl (Sum.inl v)) ∪
        (Finset.univ.filter (fun m : Fin a => decide (List.IsPrefix u (PEqualNP.Outside.L_pcx_328.nodeOf st2 m.1) ∧
          ∃ e ∈ st2.rev, (e.node = PEqualNP.Outside.L_pcx_328.nodeOf st2 m.1 ∨ Sum.inr m.1 ∈ e.gate.inputs) ∧
            List.IsPrefix e.node u))).image (fun m => Sum.inl (Sum.inr m)) ∪
        (Finset.univ.filter (fun j : Fin c => decide ((allClsList[j.1]).1 = u))).image Sum.inr
      have h_st2_node_prop : ∀ e ∈ st2.rev, e.node.length ≤ h ∧ (e.node = [] ∨ PEqualNP.Outside.L_pcx_328.isBranch addr e.node = true) := by
        intro e he
        rcases PEqualNP.Outside.L_pcx_328.entries_nodesIn h_rc0.2.2.2.2.1 e he with he1 | he_nil
        · rcases h_bn0.2.2.2.2.2.1 with ⟨suf, hsuf, hbr⟩
          rw [hsuf, List.append_nil] at he1
          exact ⟨le_of_lt (hbr e he1).1, Or.inr (hbr e he1).2⟩
        · rw [he_nil]; exact ⟨Nat.zero_le _, Or.inl rfl⟩
      have h_nodeOf_prop : ∀ m : Fin a,
          let p := PEqualNP.Outside.L_pcx_328.nodeOf st2 m.1
          p.length ≤ h ∧ (p = [] ∨ PEqualNP.Outside.L_pcx_328.isBranch addr p = true) ∧
          ∃ e ∈ st2.rev, e.node = p := by
        intro m
        have hidx : a - 1 - m.1 < st2.rev.length := by rw [h_rc0.1.2]; change a - 1 - m.1 < a; omega
        have hmem := List.getElem_mem hidx
        have hget : st2.rev.getD (a - 1 - m.1) { gate := PEqualNP.Outside.L_pcx_328.Gate.const 0 false, node := [] } =
            st2.rev[a - 1 - m.1] := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx]
        have hnode_eq : PEqualNP.Outside.L_pcx_328.nodeOf st2 m.1 = st2.rev[a - 1 - m.1].node := by
          simp only [PEqualNP.Outside.L_pcx_328.nodeOf]
          rw [hget]
        refine ⟨hnode_eq ▸ (h_st2_node_prop _ hmem).1, hnode_eq ▸ (h_st2_node_prop _ hmem).2,
          st2.rev[a - 1 - m.1], hmem, hnode_eq.symm⟩
      refine ⟨a, c, clauses, bag, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · refine ⟨fun v => ?_, fun v => ?_, fun j lit hlit => ?_, fun u w x hu hw hxu hxw => ?_⟩
        · rcases v with (v | m) | j
          · refine ⟨addr v, le_of_eq (h_len v), Finset.mem_union_left _ (Finset.mem_union_left _ ?_)⟩
            exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
              simp [PEqualNP.Outside.L_pcx_328.inBagV]⟩, rfl⟩
          · refine ⟨PEqualNP.Outside.L_pcx_328.nodeOf st2 m.1, (h_nodeOf_prop m).1,
              Finset.mem_union_left _ (Finset.mem_union_right _ ?_)⟩
            rcases (h_nodeOf_prop m).2.2 with ⟨e, he, hen⟩
            exact Finset.mem_image.mpr ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              decide_eq_true ⟨List.prefix_refl _, e, he, Or.inl hen, hen ▸ List.prefix_refl _⟩⟩, rfl⟩
          · have hmem : allClsList[j.1] ∈ allClsList := List.getElem_mem j.2
            have hlen_node : (allClsList[j.1]).1.length ≤ h := by
              rcases List.mem_append.mp hmem with hg | hu'
              · simp only [gateClsList, List.mem_flatMap, List.mem_map] at hg
                rcases hg with ⟨e, he, _, _, heq⟩
                rw [← heq]
                exact (h_st2_node_prop e he).1
              · simp only [unitClsList, List.mem_map] at hu'
                rcases hu' with ⟨_, _, heq⟩
                rw [← heq]
                simp
            refine ⟨(allClsList[j.1]).1, hlen_node, Finset.mem_union_right _ ?_⟩
            exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, decide_eq_true rfl⟩, rfl⟩
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr
            ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [PEqualNP.Outside.L_pcx_328.inBagV]⟩, rfl⟩))
        · simp only [clauses, Finset.mem_image] at hlit
          rcases hlit with ⟨l, hl, rfl⟩
          have hmem : allClsList[j.1] ∈ allClsList := List.getElem_mem j.2
          rcases List.mem_append.mp hmem with hg | hu'
          · simp only [gateClsList, List.mem_flatMap, List.mem_map] at hg
            rcases hg with ⟨e, he, cl, hcl, heq⟩
            have hnode_eq : (allClsList[j.1]).1 = e.node := by rw [← heq]
            have hcl_eq : (allClsList[j.1]).2 = cl := by rw [← heq]
            rw [hcl_eq] at hl
            refine ⟨e.node, (h_st2_node_prop e he).1, ?_, Finset.mem_union_right _ (Finset.mem_image.mpr
              ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, decide_eq_true hnode_eq⟩, rfl⟩)⟩
            have hin : l.1 ∈ e.gate.inputs ∨ l.1 = Sum.inr e.gate.out := by
              have := PEqualNP.Outside.L_pcx_328.gateClauses_in_gate e.gate cl hcl l hl
              exact this
            rcases l with ⟨v | m, lb⟩
            · rcases hin with hin | hin
              · have hv_bag := (hok_rc.1.2 e he).1 v hin
                simp only [PEqualNP.Outside.L_pcx_328.castWire]
                exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr
                  ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv_bag⟩, rfl⟩))
              · simp at hin
            · have hm_lt : m < a := by
                rcases hin with hin | hin
                · exact ((hok_rc.1.2 e he).2 m hin).1
                · simp only [Sum.inr.injEq] at hin; subst hin
                  change e.gate.out < st2.len
                  rw [← h_rc0.1.2]
                  exact PEqualNP.Outside.L_pcx_328.wellFormedRev_out_lt h_rc0.1.1 e he
              simp only [PEqualNP.Outside.L_pcx_328.castWire, Nat.mod_eq_of_lt hm_lt]
              refine Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr
                ⟨⟨m, hm_lt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, decide_eq_true ?_⟩, rfl⟩))
              rcases hin with hin | hin
              · exact ⟨((hok_rc.1.2 e he).2 m hin).2, e, he, Or.inr hin, List.prefix_refl _⟩
              · simp only [Sum.inr.injEq] at hin; subst hin
                have h_e_node : PEqualNP.Outside.L_pcx_328.nodeOf st2 e.gate.out = e.node := by
                  have hwf := h_rc0.1.1
                  have : ∀ (rev : List (PEqualNP.Outside.L_pcx_328.GEntry V)),
                      PEqualNP.Outside.L_pcx_328.WellFormedRev rev →
                      ∀ e' ∈ rev, (rev.getD (rev.length - 1 - e'.gate.out)
                        { gate := PEqualNP.Outside.L_pcx_328.Gate.const 0 false, node := [] }).node = e'.node := by
                    intro rev hwf_r
                    induction rev with
                    | nil => intro _ h; simp at h
                    | cons hd tl ih_r =>
                      intro e' he'
                      rcases hwf_r with ⟨ho, hin_r, htl⟩
                      simp only [List.mem_cons] at he'
                      rcases he' with rfl | he'
                      · simp [ho]
                      · have hlt' := PEqualNP.Outside.L_pcx_328.wellFormedRev_out_lt htl e' he'
                        have hne' : e'.gate.out ≠ hd.gate.out := by omega
                        have hsub' : tl.length + 1 - 1 - e'.gate.out = (tl.length - 1 - e'.gate.out) + 1 := by omega
                        simp only [List.length_cons, hsub', List.getD_cons_succ]
                        exact ih_r htl e' he'
                  simpa [PEqualNP.Outside.L_pcx_328.nodeOf, h_rc0.1.2] using this st2.rev hwf e he
                rw [h_e_node]
                exact ⟨List.prefix_refl _, e, he, Or.inl rfl, List.prefix_refl _⟩
          · simp only [unitClsList, List.mem_map] at hu'
            rcases hu' with ⟨w_u, hw_u, heq⟩
            have hnode_eq : (allClsList[j.1]).1 = [] := by rw [← heq]
            have hcl_eq : (allClsList[j.1]).2 = {(w_u, true)} := by rw [← heq]
            rw [hcl_eq] at hl
            simp only [Finset.mem_singleton] at hl
            subst hl
            have hw_ok := hok_rc.2.2.2 w_u hw_u
            have hw_lt : ∀ m, w_u = Sum.inr m → m < a ∧ PEqualNP.Outside.L_pcx_328.nodeOf st2 m = [] := by
              intro m hm
              have hm1 := (hw_ok.2 m hm).1
              have hm_ge := PEqualNP.Outside.L_pcx_328.emitRootCmps_out_ge lo hi w_root st1 w_u hw_u m hm
              exact ⟨hm1, PEqualNP.Outside.L_pcx_328.nodeOf_nodesIn_ge h_rc0.2.2.2.2.1 h_bn0.1.2.symm h_rc0.1.2.symm hm_ge hm1⟩
            rcases w_u with v | m
            · refine ⟨[], by simp, ?_, Finset.mem_union_right _ (Finset.mem_image.mpr
                ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, decide_eq_true hnode_eq⟩, rfl⟩)⟩
              simp only [PEqualNP.Outside.L_pcx_328.castWire]
              exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr
                ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw_ok.1 v rfl⟩, rfl⟩))
            · rcases hw_lt m rfl with ⟨hm_lt, hm_nil⟩
              refine ⟨[], by simp, ?_, Finset.mem_union_right _ (Finset.mem_image.mpr
                ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, decide_eq_true hnode_eq⟩, rfl⟩)⟩
              simp only [PEqualNP.Outside.L_pcx_328.castWire, Nat.mod_eq_of_lt hm_lt]
              refine Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr
                ⟨⟨m, hm_lt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, decide_eq_true ?_⟩, rfl⟩))
              rcases (h_nodeOf_prop ⟨m, hm_lt⟩).2.2 with ⟨e, he, hen⟩
              exact ⟨hm_nil ▸ List.nil_prefix, e, he, Or.inl hen, hm_nil ▸ hen ▸ List.prefix_refl _⟩
        · simp only [bag, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
            true_and, decide_eq_true_eq] at hxu hxw
          rcases hxu with (⟨v1, hv1, rfl⟩ | ⟨m1, hm1, rfl⟩) | ⟨j1, hj1, rfl⟩
          · rcases hxw with (⟨v2, hv2, hveq⟩ | ⟨m2, _, hveq⟩) | ⟨j2, _, hveq⟩
            · have hv : v1 = v2 := by simpa using hveq.symm
              subst hv
              rcases PEqualNP.Outside.L_pcx_328.inBagV_running M addr h_inj u w v1 hv1 hv2 with
                ⟨b0, hb0u, hb0w, hb0z⟩
              refine ⟨b0, hb0u, hb0w, fun z hbz hzw => ?_⟩
              exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr
                ⟨v1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb0z z hbz hzw⟩, rfl⟩))
            · simp at hveq
            · simp at hveq
          · rcases hxw with (⟨v2, _, hveq⟩ | ⟨m2, hm2, hveq⟩) | ⟨j2, _, hveq⟩
            · simp at hveq
            · have hm : m1 = m2 := by simpa using hveq.symm
              subst hm
              have hord : List.IsPrefix u w ∨ List.IsPrefix w u := by
                rcases hm1.1 with ⟨tu, htu⟩; rcases hm2.1 with ⟨tw, htw⟩
                rw [← htu] at htw
                rcases List.append_eq_append_iff.mp htw.symm with ⟨s, hs, _⟩ | ⟨s, hs, _⟩
                · exact Or.inl ⟨s, hs.symm⟩
                · exact Or.inr ⟨s, hs.symm⟩
              rcases hord with huw | hwu
              · refine ⟨u, List.prefix_refl _, huw, fun z hbz hzw => ?_⟩
                refine Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr
                  ⟨m1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, decide_eq_true ?_⟩, rfl⟩))
                have hzp : List.IsPrefix z (PEqualNP.Outside.L_pcx_328.nodeOf st2 m1.1) := by
                  rcases hzw with hz | hz
                  · exact List.IsPrefix.trans hz hm1.1
                  · exact List.IsPrefix.trans hz hm2.1
                rcases hm1.2 with ⟨e, he, hem, heu⟩
                exact ⟨hzp, e, he, hem, List.IsPrefix.trans heu hbz⟩
              · refine ⟨w, hwu, List.prefix_refl _, fun z hbz hzw => ?_⟩
                refine Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr
                  ⟨m1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, decide_eq_true ?_⟩, rfl⟩))
                have hzp : List.IsPrefix z (PEqualNP.Outside.L_pcx_328.nodeOf st2 m1.1) := by
                  rcases hzw with hz | hz
                  · exact List.IsPrefix.trans hz hm1.1
                  · exact List.IsPrefix.trans hz hm2.1
                rcases hm2.2 with ⟨e, he, hem, hew⟩
                exact ⟨hzp, e, he, hem, List.IsPrefix.trans hew hbz⟩
            · simp at hveq
          · rcases hxw with (⟨v2, _, hveq⟩ | ⟨m2, _, hveq⟩) | ⟨j2, hj2, hveq⟩
            · simp at hveq
            · simp at hveq
            · have hj : j1 = j2 := by simpa using hveq.symm
              subst hj
              have huw : u = w := hj1.symm.trans hj2
              subst huw
              refine ⟨u, List.prefix_refl _, List.prefix_refl _, fun z hbz hzw => ?_⟩
              have hzlen : z.length = u.length := by
                rcases hzw with hz | hz <;> exact Nat.le_antisymm hz.length_le hbz.length_le
              have hzeq : z = u := List.IsPrefix.eq_of_length (by rcases hzw with hz | hz <;> exact hz) hzlen
              exact Finset.mem_union_right _ (Finset.mem_image.mpr
                ⟨j1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, decide_eq_true (hj1.trans hzeq.symm)⟩, rfl⟩)
      · intro u hu
        have h_bagV_le : (Finset.univ.filter (fun v : V => PEqualNP.Outside.L_pcx_328.inBagV M addr u v = true)).card ≤
            1 + 4 * r * t :=
          PEqualNP.Outside.L_pcx_328.inBagV_card_le M addr h_inj h_len ht u
        have h_cnt_le : ∀ p : List Bool,
            PEqualNP.Outside.L_pcx_328.countNode st2.rev p ≤ r * (6 * t + 15 * b + 2) := by
          intro p
          have h1 := PEqualNP.Outside.L_pcx_328.buildNode_countNode_le M addr b h_inj h_len ht h []
            (PEqualNP.Outside.L_pcx_328.CState.empty V) p rfl
          have h1' : PEqualNP.Outside.L_pcx_328.countNode st1.rev p ≤ r * (6 * t + 12 * b) := by
            have h1_2 := h1.2 List.nil_prefix
            dsimp only [PEqualNP.Outside.L_pcx_328.CState.empty] at h1_2
            simp only [PEqualNP.Outside.L_pcx_328.countNode, List.filter_nil, List.length_nil, zero_add] at h1_2
            exact h1_2
          by_cases hp : p = []
          · subst hp
            have h2 := PEqualNP.Outside.L_pcx_328.countNode_nodesIn_le h_rc0.2.2.2.2.1
            rw [PEqualNP.Outside.L_pcx_328.nodesIn_rev_length_eq h_rc0.2.2.2.2.1 h_bn0.1.2.symm h_rc0.1.2.symm] at h2
            have h3 := h_rc0.2.2.1
            nlinarith
          · rw [PEqualNP.Outside.L_pcx_328.countNode_nodesIn_ne h_rc0.2.2.2.2.1 (Ne.symm hp)]
            nlinarith
        let Mset := Finset.univ.filter (fun m : Fin a =>
          List.IsPrefix u (PEqualNP.Outside.L_pcx_328.nodeOf st2 m.1) ∧
          ∃ e ∈ st2.rev, (e.node = PEqualNP.Outside.L_pcx_328.nodeOf st2 m.1 ∨ Sum.inr m.1 ∈ e.gate.inputs) ∧
            List.IsPrefix e.node u)
        let M1 := Mset.filter (fun m : Fin a => List.IsPrefix (PEqualNP.Outside.L_pcx_328.ancOf addr (PEqualNP.Outside.L_pcx_328.nodeOf st2 m.1)) u)
        let M2 := Mset.filter (fun m : Fin a => ¬ List.IsPrefix (PEqualNP.Outside.L_pcx_328.ancOf addr (PEqualNP.Outside.L_pcx_328.nodeOf st2 m.1)) u)
        have hM1 : M1.card ≤ 3 * (r * (6 * t + 15 * b + 2)) := by
          let S_nodes := M1.image (fun m : Fin a => PEqualNP.Outside.L_pcx_328.nodeOf st2 m.1)
          have hS_le : S_nodes.card ≤ 3 := by
            apply PEqualNP.Outside.L_pcx_328.ancOf_card_le_three addr u S_nodes
            · intro p hp
              simp only [S_nodes, Finset.mem_image] at hp
              rcases hp with ⟨m, _, rfl⟩
              exact (h_nodeOf_prop m).2.1
            · intro p hp
              simp only [S_nodes, M1, Mset, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hp
              rcases hp with ⟨m, ⟨⟨hum, _⟩, hanc⟩, rfl⟩
              exact ⟨hanc, hum⟩
          have h_each : ∀ p ∈ S_nodes, (M1.filter (fun m : Fin a => PEqualNP.Outside.L_pcx_328.nodeOf st2 m.1 = p)).card ≤
              r * (6 * t + 15 * b + 2) := by
            intro p _
            let F := M1.filter (fun m : Fin a => PEqualNP.Outside.L_pcx_328.nodeOf st2 m.1 = p)
            have hinj : Set.InjOn (fun m : Fin a => (⟨a - 1 - m.1, by rw [h_rc0.1.2]; change a - 1 - m.1 < a; omega⟩ : Fin st2.rev.length)) F := by
              intro m1 _ m2 _ heq
              have hval := congrArg Fin.val heq
              simp only at hval
              ext; omega
            have hle_cnt : (F.image (fun m : Fin a => (⟨a - 1 - m.1, by rw [h_rc0.1.2]; change a - 1 - m.1 < a; omega⟩ : Fin st2.rev.length))).card ≤
                PEqualNP.Outside.L_pcx_328.countNode st2.rev p := by
              have hsub : F.image (fun m : Fin a => (⟨a - 1 - m.1, by rw [h_rc0.1.2]; change a - 1 - m.1 < a; omega⟩ : Fin st2.rev.length)) ⊆
                  Finset.univ.filter (fun idx : Fin st2.rev.length => st2.rev[idx.1].node = p) := by
                intro idx hidx
                simp only [Finset.mem_image, F, Finset.mem_filter, Finset.mem_univ, true_and] at hidx ⊢
                rcases hidx with ⟨m, ⟨_, hmp⟩, rfl⟩
                have hidx' : a - 1 - m.1 < st2.rev.length := by rw [h_rc0.1.2]; change a - 1 - m.1 < a; omega
                have hget : st2.rev[a - 1 - m.1] = st2.rev.getD (a - 1 - m.1)
                    { gate := PEqualNP.Outside.L_pcx_328.Gate.const 0 false, node := [] } := by
                  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx', Option.getD_some]
                rw [hget]; exact hmp
              have hcard_eq : (Finset.univ.filter (fun idx : Fin st2.rev.length => st2.rev[idx.1].node = p)).card =
                  PEqualNP.Outside.L_pcx_328.countNode st2.rev p := by
                simp only [PEqualNP.Outside.L_pcx_328.countNode]
                have h_aux : ∀ {α : Type} (l : List α) (P : α → Bool),
                    (Finset.univ.filter (fun idx : Fin l.length => P l[idx.1] = true)).card = (l.filter P).length := by
                  intro α l P
                  induction l with
                  | nil => simp
                  | cons hd tl ihtl =>
                    rw [List.filter_cons]
                    have hbij : (Finset.univ.filter (fun idx : Fin (hd :: tl).length => P (hd :: tl)[idx.1] = true)).card =
                        (if P hd = true then 1 else 0) +
                        (Finset.univ.filter (fun idx : Fin tl.length => P tl[idx.1] = true)).card := by
                      have h_split : Finset.univ.filter (fun idx : Fin (hd :: tl).length => P (hd :: tl)[idx.1] = true) =
                          (if P hd = true then {0} else ∅) ∪
                          (Finset.univ.filter (fun idx : Fin tl.length => P tl[idx.1] = true)).image Fin.succ := by
                        ext ⟨i, hi⟩
                        cases i with
                        | zero => by_cases hP : P hd = true <;> simp [hP, Fin.ext_iff]
                        | succ k =>
                          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
                            Finset.mem_image, Fin.ext_iff]
                          by_cases hP : P hd = true <;> simp [hP, Fin.succ] <;>
                            exact ⟨fun h => ⟨⟨k, Nat.lt_of_succ_lt_succ hi⟩, h, rfl⟩, fun ⟨a, ha, h_eq⟩ => h_eq ▸ ha⟩
                      rw [h_split, Finset.card_union_of_disjoint]
                      · rw [Finset.card_image_of_injective _ (fun a b h => Fin.succ_injective _ h)]
                        split_ifs <;> simp
                      · split_ifs <;> simp [Finset.disjoint_left, Fin.succ]
                    rw [hbij, ihtl]
                    split_ifs <;> simp <;> omega
                exact h_aux st2.rev (fun e => decide (e.node = p))
              exact (Finset.card_le_card hsub).trans (le_of_eq hcard_eq)
            calc F.card = (F.image _).card := (Finset.card_image_of_injOn hinj).symm
              _ ≤ PEqualNP.Outside.L_pcx_328.countNode st2.rev p := hle_cnt
              _ ≤ r * (6 * t + 15 * b + 2) := h_cnt_le p
          have hpart : M1 = S_nodes.biUnion (fun p => M1.filter (fun m : Fin a => PEqualNP.Outside.L_pcx_328.nodeOf st2 m.1 = p)) := by
            ext m; simp only [Finset.mem_biUnion, Finset.mem_filter, S_nodes, Finset.mem_image]
            exact ⟨fun h => ⟨_, ⟨m, h, rfl⟩, h, rfl⟩, fun ⟨_, _, h, _⟩ => h⟩
          calc M1.card = (S_nodes.biUnion (fun p => M1.filter (fun m : Fin a => PEqualNP.Outside.L_pcx_328.nodeOf st2 m.1 = p))).card := by
                rw [← hpart]
            _ ≤ ∑ p ∈ S_nodes, (M1.filter (fun m : Fin a => PEqualNP.Outside.L_pcx_328.nodeOf st2 m.1 = p)).card :=
                Finset.card_biUnion_le
            _ ≤ ∑ _p ∈ S_nodes, r * (6 * t + 15 * b + 2) := Finset.sum_le_sum h_each
            _ = S_nodes.card * (r * (6 * t + 15 * b + 2)) := by simp [Finset.sum_const]
            _ ≤ 3 * (r * (6 * t + 15 * b + 2)) := Nat.mul_le_mul_right _ hS_le
        have hM2 : M2.card ≤ 2 * r * b := by
          have hcut := (PEqualNP.Outside.L_pcx_328.cutWires_card_le M addr b u h [] (PEqualNP.Outside.L_pcx_328.CState.empty V)).2 List.nil_prefix
          have hinj : Set.InjOn (fun m : Fin a => m.1) M2 := fun _ _ _ _ h => Fin.ext h
          have hsub : M2.image Fin.val ⊆ PEqualNP.Outside.L_pcx_328.cutWires M addr b u h [] (PEqualNP.Outside.L_pcx_328.CState.empty V) := by
            intro m hm
            simp only [Finset.mem_image, M2, Mset, Finset.mem_filter, Finset.mem_univ, true_and] at hm
            rcases hm with ⟨m', ⟨⟨⟨hum, e, he, hem, heu⟩, hnot_anc⟩, rfl⟩⟩
            have hanc_p := PEqualNP.Outside.L_pcx_328.ancOf_isPrefix addr (PEqualNP.Outside.L_pcx_328.nodeOf st2 m'.1)
            have hord : List.IsPrefix u (PEqualNP.Outside.L_pcx_328.ancOf addr (PEqualNP.Outside.L_pcx_328.nodeOf st2 m'.1)) := by
              rcases hanc_p with ⟨ta, hta⟩; rcases hum with ⟨tu, htu⟩
              rw [← hta] at htu
              rcases List.append_eq_append_iff.mp htu.symm with ⟨s, hs, _⟩ | ⟨s, hs, _⟩
              · exact absurd ⟨s, hs.symm⟩ hnot_anc
              · exact ⟨s, hs.symm⟩
            have hne_anc : u ≠ PEqualNP.Outside.L_pcx_328.ancOf addr (PEqualNP.Outside.L_pcx_328.nodeOf st2 m'.1) :=
              fun heq => hnot_anc (heq ▸ List.prefix_refl _)
            have hex_b : ∃ b', List.IsPrefix (u ++ [b']) (PEqualNP.Outside.L_pcx_328.nodeOf st2 m'.1) := by
              rcases PEqualNP.Outside.L_pcx_328.prefix_trichotomy u (PEqualNP.Outside.L_pcx_328.ancOf addr (PEqualNP.Outside.L_pcx_328.nodeOf st2 m'.1)) hord with h0 | h0 | h0
              · exact absurd h0.symm hne_anc
              · exact ⟨false, List.IsPrefix.trans h0 hanc_p⟩
              · exact ⟨true, List.IsPrefix.trans h0 hanc_p⟩
            have hm1 : m'.1 < st1.len := by
              by_contra hnot
              have hnode := PEqualNP.Outside.L_pcx_328.nodeOf_nodesIn_ge h_rc0.2.2.2.2.1 h_bn0.1.2.symm h_rc0.1.2.symm (Nat.le_of_not_lt hnot) m'.2
              rcases hex_b with ⟨b', hb'⟩
              rw [hnode] at hb'; simp at hb'
            have hnode_eq : PEqualNP.Outside.L_pcx_328.nodeOf st2 m'.1 = PEqualNP.Outside.L_pcx_328.nodeOf st1 m'.1 :=
              PEqualNP.Outside.L_pcx_328.nodeOf_nodesIn_lt h_rc0.2.2.2.2.1 h_bn0.1.2.symm h_rc0.1.2.symm hm1
            rcases hex_b with ⟨b', hb'⟩
            rw [hnode_eq] at hb'
            have h_in_st1 : m'.1 ∈ PEqualNP.Outside.L_pcx_328.outsWires w_root ∨
                ∃ e1 ∈ st1.rev, List.IsPrefix e1.node u ∧ Sum.inr m'.1 ∈ e1.gate.inputs := by
              by_cases he1 : e ∈ st1.rev
              · right; refine ⟨e, he1, heu, ?_⟩
                rcases hem with hen | hin
                · exfalso
                  have hle1 : e.node.length ≤ u.length := heu.length_le
                  have hle2 : u.length < (PEqualNP.Outside.L_pcx_328.nodeOf st1 m'.1).length := by
                    have := hb'.length_le; simp at this; omega
                  rw [← hnode_eq, ← hen] at hle2; omega
                · exact hin
              · left
                have hrc_in := PEqualNP.Outside.L_pcx_328.inputsIn_emitRootCmps lo hi w_root st1
                  (PEqualNP.Outside.L_pcx_328.outsWires w_root)
                  (fun xs hxs o ho w hw m0 hm0 => by
                    subst hm0
                    exact ⟨(h_bn0.2.2.2.2.1 xs hxs).2 o ho _ hw,
                      PEqualNP.Outside.L_pcx_328.mem_outsWires.mpr ⟨xs, hxs, hw ▸ ho⟩⟩)
                rcases hrc_in.1 e he with h | h
                · exact absurd h he1
                · rcases hem with hen | hin
                  · exfalso
                    have he_nil : e.node = [] := by
                      rcases PEqualNP.Outside.L_pcx_328.entries_nodesIn h_rc0.2.2.2.2.1 e he with h' | h'
                      · exact absurd h' he1
                      · exact h'
                    rw [← hnode_eq, ← hen, he_nil] at hb'; simp at hb'
                  · exact h m'.1 hin hm1
            have hcw := PEqualNP.Outside.L_pcx_328.buildNode_cutWires_used M addr b u h []
              (PEqualNP.Outside.L_pcx_328.CState.empty V) h_empty_ok
            rcases h_in_st1 with hm_out | ⟨e1, he1, he1u, he1in⟩
            · exact hcw.1 m'.1 hm_out List.nil_prefix ⟨b', hb'⟩
            · rcases hcw.2 e1 he1 with h_emp | h_used
              · simp [PEqualNP.Outside.L_pcx_328.CState.empty] at h_emp
              · exact h_used he1u m'.1 he1in ⟨b', hb'⟩
          calc M2.card = (M2.image Fin.val).card := (Finset.card_image_of_injOn hinj).symm
            _ ≤ (PEqualNP.Outside.L_pcx_328.cutWires M addr b u h [] (PEqualNP.Outside.L_pcx_328.CState.empty V)).card :=
              Finset.card_le_card hsub
            _ ≤ 2 * r * b := hcut
        have h_bagM_le : Mset.card ≤ 3 * (r * (6 * t + 15 * b + 2)) + 2 * r * b := by
          have hun : Mset ⊆ M1 ∪ M2 := fun m hm => by
            by_cases hanc : List.IsPrefix (PEqualNP.Outside.L_pcx_328.ancOf addr (PEqualNP.Outside.L_pcx_328.nodeOf st2 m.1)) u
            · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hm, hanc⟩)
            · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hm, hanc⟩)
          calc Mset.card ≤ (M1 ∪ M2).card := Finset.card_le_card hun
            _ ≤ M1.card + M2.card := Finset.card_union_le _ _
            _ ≤ 3 * (r * (6 * t + 15 * b + 2)) + 2 * r * b := Nat.add_le_add hM1 hM2
        have h_bagC_le : (Finset.univ.filter (fun j : Fin c => decide ((allClsList[j.1]).1 = u))).card ≤
            4 * (r * (6 * t + 15 * b + 2)) + 2 * r := by
          have h_aux : ∀ {α : Type} (l : List α) (P : α → Bool),
              (Finset.univ.filter (fun idx : Fin l.length => P l[idx.1] = true)).card = (l.filter P).length := by
            intro α l P
            induction l with
            | nil => simp
            | cons hd tl ihtl =>
              rw [List.filter_cons]
              have hbij : (Finset.univ.filter (fun idx : Fin (hd :: tl).length => P (hd :: tl)[idx.1] = true)).card =
                  (if P hd = true then 1 else 0) +
                  (Finset.univ.filter (fun idx : Fin tl.length => P tl[idx.1] = true)).card := by
                have h_split : Finset.univ.filter (fun idx : Fin (hd :: tl).length => P (hd :: tl)[idx.1] = true) =
                    (if P hd = true then {0} else ∅) ∪
                    (Finset.univ.filter (fun idx : Fin tl.length => P tl[idx.1] = true)).image Fin.succ := by
                  ext ⟨i, hi⟩
                  cases i with
                  | zero => by_cases hP : P hd = true <;> simp [hP, Fin.ext_iff]
                  | succ k =>
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
                      Finset.mem_image, Fin.ext_iff]
                    by_cases hP : P hd = true <;> simp [hP, Fin.succ] <;>
                      exact ⟨fun h => ⟨⟨k, Nat.lt_of_succ_lt_succ hi⟩, h, rfl⟩, fun ⟨a, ha, h_eq⟩ => h_eq ▸ ha⟩
                rw [h_split, Finset.card_union_of_disjoint]
                · rw [Finset.card_image_of_injective _ (fun a b h => Fin.succ_injective _ h)]
                  split_ifs <;> simp
                · split_ifs <;> simp [Finset.disjoint_left, Fin.succ]
              rw [hbij, ihtl]
              split_ifs <;> simp <;> omega
          have h_eq := h_aux allClsList (fun x => decide (x.1 = u))
          simp only [decide_eq_true_eq] at h_eq ⊢
          rw [h_eq]
          rw [show allClsList = gateClsList ++ unitClsList from rfl, List.filter_append, List.length_append]
          have h_gate : (gateClsList.filter (fun x => decide (x.1 = u))).length ≤
              4 * PEqualNP.Outside.L_pcx_328.countNode st2.rev u := by
            simp only [gateClsList, PEqualNP.Outside.L_pcx_328.countNode]
            induction st2.rev with
            | nil => simp
            | cons e rest ih =>
              simp only [List.flatMap_cons, List.filter_append, List.length_append, List.filter_cons]
              by_cases he : e.node = u
              · have hlen_g : ((PEqualNP.Outside.L_pcx_328.gateClauses e.gate).map (fun cl => (e.node, cl))).length ≤ 4 := by
                  rw [List.length_map]
                  exact PEqualNP.Outside.L_pcx_328.gateClauses_length_le_four e.gate
                have hfl : ((PEqualNP.Outside.L_pcx_328.gateClauses e.gate).map (fun cl => (e.node, cl)) |>.filter
                    (fun x => decide (x.1 = u))).length ≤ 4 :=
                  (List.length_filter_le _ _).trans hlen_g
                simp only [he, decide_true, ite_true, List.length_cons] at hfl ⊢
                linarith [ih, hfl]
              · have hfl0 : ((PEqualNP.Outside.L_pcx_328.gateClauses e.gate).map (fun cl => (e.node, cl))).filter
                    (fun x => decide (x.1 = u)) = [] := by
                  rw [List.filter_eq_nil_iff]
                  intro x hx
                  simp only [List.mem_map] at hx
                  rcases hx with ⟨cl, _, rfl⟩
                  simp [he]
                rw [hfl0]; simp only [List.length_nil, zero_add, he, decide_false, Bool.false_eq_true, ↓reduceIte]
                exact ih
          have h_unit_len : w_cmps.length = 2 * r := by
            have h_rc_len : ∀ (xss : List (List (Option (V ⊕ ℕ)))) (st : PEqualNP.Outside.L_pcx_328.CState V),
                (PEqualNP.Outside.L_pcx_328.emitRootCmps st lo hi xss).2.length = 2 * xss.length := by
              intro xss
              induction xss with
              | nil => intro st; simp [PEqualNP.Outside.L_pcx_328.emitRootCmps]
              | cons xs rest ih => intro st; simp [PEqualNP.Outside.L_pcx_328.emitRootCmps, ih]; omega
            rw [show w_cmps = (PEqualNP.Outside.L_pcx_328.emitRootCmps st1 lo hi w_root).2 from rfl, h_rc_len, h_bn0.2.2.2.1]
          have h_unit : (unitClsList.filter (fun x => decide (x.1 = u))).length ≤ 2 * r :=
            (List.length_filter_le _ _).trans (by simp [unitClsList, h_unit_len])
          have hcu := h_cnt_le u
          omega
        calc (bag u).card
            ≤ (Finset.univ.filter (fun v : V => PEqualNP.Outside.L_pcx_328.inBagV M addr u v = true)).card +
              Mset.card +
              (Finset.univ.filter (fun j : Fin c => decide ((allClsList[j.1]).1 = u))).card := by
                refine (Finset.card_union_le _ _).trans ?_
                refine (Nat.add_le_add_right (Finset.card_union_le _ _) _).trans ?_
                refine Nat.add_le_add (Nat.add_le_add Finset.card_image_le ?_) Finset.card_image_le
                simpa [Mset, decide_eq_true_eq] using
                  (Finset.card_image_le (f := fun m : Fin a => (Sum.inl (Sum.inr m) : (V ⊕ Fin a) ⊕ Fin c)))
          _ ≤ (1 + 4 * r * t) + (3 * (r * (6 * t + 15 * b + 2)) + 2 * r * b) +
              (4 * (r * (6 * t + 15 * b + 2)) + 2 * r) := by omega
          _ ≤ 1000 * (r + 1) * (t + b) := by nlinarith
      · have h_sd : ((List.finRange r).map (fun j => PEqualNP.Outside.L_pcx_328.subtreeCountDiffs addr (M j) [])).sum ≤ r * n := by
          have h_sum_le : ∀ {α : Type} (l : List α) (f : α → ℕ) (K : ℕ),
              (∀ x ∈ l, f x ≤ K) → (l.map f).sum ≤ l.length * K := by
            intro α l f K hf
            induction l with
            | nil => simp
            | cons hd tl ih =>
              simp only [List.map_cons, List.sum_cons, List.length_cons]
              have := ih (fun x hx => hf x (List.mem_cons_of_mem _ hx))
              have := hf hd List.mem_cons_self
              nlinarith
          have h1 := h_sum_le (List.finRange r) (fun j => PEqualNP.Outside.L_pcx_328.subtreeCountDiffs addr (M j) []) n
            (fun j _ => by
              simp only [PEqualNP.Outside.L_pcx_328.subtreeCountDiffs]
              exact (List.countP_le_length).trans (by simp))
          simpa using h1
        have ha_bnd : a ≤ 12 * r * b * (2 * n) + 6 * (r * n) + r * (3 * b + 2) := by
          have h1 := h_bn0.2.2.1
          have h2 := h_rc0.2.2.1
          have hle := h_rc0.2.1
          have hlv : PEqualNP.Outside.L_pcx_328.leavesIn addr [] = 2 * n := by
            dsimp only [V]
            simp [PEqualNP.Outside.L_pcx_328.leavesIn]
          rw [hlv] at h1
          have hmul : 12 * r * b * (2 * n - 1) ≤ 12 * r * b * (2 * n) := Nat.mul_le_mul_left _ (by omega)
          change a ≤ _
          omega
        have hc_bnd : c ≤ 4 * a + 2 * r := by
          have h_gate_len : gateClsList.length ≤ 4 * st2.rev.length := by
            simp only [gateClsList]
            induction st2.rev with
            | nil => simp
            | cons e rest ih =>
              simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons]
              have := PEqualNP.Outside.L_pcx_328.gateClauses_length_le_four e.gate
              omega
          have h_unit_len : unitClsList.length = 2 * r := by
            have h_rc_len : ∀ (xss : List (List (Option (V ⊕ ℕ)))) (st : PEqualNP.Outside.L_pcx_328.CState V),
                (PEqualNP.Outside.L_pcx_328.emitRootCmps st lo hi xss).2.length = 2 * xss.length := by
              intro xss
              induction xss with
              | nil => intro st; simp [PEqualNP.Outside.L_pcx_328.emitRootCmps]
              | cons xs rest ih => intro st; simp [PEqualNP.Outside.L_pcx_328.emitRootCmps, ih]; omega
            simp only [unitClsList, List.length_map]
            rw [show w_cmps = (PEqualNP.Outside.L_pcx_328.emitRootCmps st1 lo hi w_root).2 from rfl, h_rc_len, h_bn0.2.2.2.1]
          have hrev_len : st2.rev.length = a := h_rc0.1.2
          simp only [c, allClsList, List.length_append]
          omega
        change a + c ≤ 1000 * (r + 1) * (n + 1) * b
        have hrn_le : r * n ≤ r * n * b := Nat.le_mul_of_pos_right _ hb_pos
        have hr_le : r ≤ r * b := Nat.le_mul_of_pos_right _ hb_pos
        nlinarith [ha_bnd, hc_bnd, hrn_le, hr_le]
      · intro j
        have hmem : allClsList[j.1] ∈ allClsList := List.getElem_mem j.2
        calc (clauses j).card ≤ (allClsList[j.1]).2.card := Finset.card_image_le
          _ ≤ 3 := by
            rcases List.mem_append.mp hmem with hg | hu'
            · simp only [gateClsList, List.mem_flatMap, List.mem_map] at hg
              rcases hg with ⟨e, _, cl, hcl, heq⟩
              rw [← heq]
              exact PEqualNP.Outside.L_pcx_328.gateClauses_card_le_three e.gate cl hcl
            · simp only [unitClsList, List.mem_map] at hu'
              rcases hu' with ⟨w, _, heq⟩
              rw [← heq]; simp
      · have h_sat_congr : ∀ {y1 y2 : ℕ → Bool} {x : X} {cl : PEqualNP.ProofComplexity.Clause (V ⊕ ℕ)},
            (∀ l ∈ cl, PEqualNP.Outside.L_pcx_328.WireValid a l.1) →
            (∀ m < a, y1 m = y2 m) →
            (PEqualNP.ProofComplexity.ClauseSat (Sum.elim x y1) cl ↔
             PEqualNP.ProofComplexity.ClauseSat (Sum.elim x y2) cl) := by
          intro y1 y2 x cl hcl hy
          simp only [PEqualNP.ProofComplexity.ClauseSat]
          constructor
          · rintro ⟨⟨v | m, b0⟩, hl, hsat⟩
            · exact ⟨(Sum.inl v, b0), hl, hsat⟩
            · exact ⟨(Sum.inr m, b0), hl, by simpa [hy m (hcl _ hl)] using hsat⟩
          · rintro ⟨⟨v | m, b0⟩, hl, hsat⟩
            · exact ⟨(Sum.inl v, b0), hl, hsat⟩
            · exact ⟨(Sum.inr m, b0), hl, by simpa [hy m (hcl _ hl)] using hsat⟩
        have h_cl_wv : ∀ j : Fin c, ∀ l ∈ (allClsList[j.1]).2, PEqualNP.Outside.L_pcx_328.WireValid a l.1 := by
          intro j l hl
          have hmem : allClsList[j.1] ∈ allClsList := List.getElem_mem j.2
          rcases List.mem_append.mp hmem with hg | hu'
          · simp only [gateClsList, List.mem_flatMap, List.mem_map] at hg
            rcases hg with ⟨e, he, cl, hcl, heq⟩
            rw [← heq] at hl
            rcases PEqualNP.Outside.L_pcx_328.gateClauses_in_gate e.gate cl hcl l hl with hin | hout
            · rcases l with ⟨v | m, lb⟩
              · trivial
              · exact ((hok_rc.1.2 e he).2 m hin).1
            · rcases l with ⟨v | m, lb⟩
              · simp at hout
              · simp only [Sum.inr.injEq] at hout; subst hout
                change e.gate.out < st2.len
                rw [← h_rc0.1.2]
                exact PEqualNP.Outside.L_pcx_328.wellFormedRev_out_lt h_rc0.1.1 e he
          · simp only [unitClsList, List.mem_map] at hu'
            rcases hu' with ⟨w_u, hw_u, heq⟩
            rw [← heq] at hl; simp only [Finset.mem_singleton] at hl; subst hl
            exact h_rc0.2.2.2.1 w_u hw_u
        have h_sat_uniq : ∀ (x : X) (y : Fin a → Bool),
            (∀ j : Fin c, PEqualNP.ProofComplexity.ClauseSat (Sum.elim x y) (clauses j)) →
            ∀ m : Fin a, y m = PEqualNP.Outside.L_pcx_328.evalRev x st2.rev m.1 := by
          intro x y hsat m
          let y' : ℕ → Bool := fun k => if hk : k < a then y ⟨k, hk⟩ else false
          have h_gates : ∀ e ∈ st2.rev, ∀ cl ∈ PEqualNP.Outside.L_pcx_328.gateClauses e.gate,
              PEqualNP.ProofComplexity.ClauseSat (Sum.elim x y') cl := by
            intro e he cl hcl
            have hmem : (e.node, cl) ∈ allClsList :=
              List.mem_append_left _ (List.mem_flatMap.mpr ⟨e, he, List.mem_map.mpr ⟨cl, hcl, rfl⟩⟩)
            rcases List.mem_iff_getElem.mp hmem with ⟨idx, hidx, h_eq⟩
            have hsat_j := hsat ⟨idx, hidx⟩
            dsimp only [clauses] at hsat_j
            rw [PEqualNP.Outside.L_pcx_328.clauseSat_image_castWire x ha_pos y _ (h_cl_wv ⟨idx, hidx⟩)] at hsat_j
            rw [h_eq] at hsat_j
            exact hsat_j
          have heq := PEqualNP.Outside.L_pcx_328.evalRev_unique x y' (h_rc x).1.1 h_gates m.1
            (by rw [h_rc0.1.2]; exact m.2)
          simpa [y', m.2] using heq
        intro x
        constructor
        · intro hacc
          refine ⟨fun m => PEqualNP.Outside.L_pcx_328.evalRev x st2.rev m.1, fun j => ?_⟩
          dsimp only [clauses]
          rw [PEqualNP.Outside.L_pcx_328.clauseSat_image_castWire x ha_pos _ _ (h_cl_wv j)]
          rw [h_sat_congr (y2 := PEqualNP.Outside.L_pcx_328.evalRev x st2.rev) (h_cl_wv j)
            (fun m hm => by change m < st2.len at hm; simp [hm])]
          have hmem : allClsList[j.1] ∈ allClsList := List.getElem_mem j.2
          rcases List.mem_append.mp hmem with hg | hu'
          · simp only [gateClsList, List.mem_flatMap, List.mem_map] at hg
            rcases hg with ⟨e, he, cl, hcl, heq⟩
            rw [← heq]
            exact PEqualNP.Outside.L_pcx_328.evalRev_sat x (h_rc x).1.1 e he cl hcl
          · simp only [unitClsList, List.mem_map] at hu'
            rcases hu' with ⟨w_u, hw_u, heq⟩
            rw [← heq]
            refine ⟨(w_u, true), Finset.mem_singleton_self _, ?_⟩
            exact (h_rc x).2.2.2.2.2.mpr hacc w_u hw_u
        · rintro ⟨y, hsat⟩
          rw [← (h_rc x).2.2.2.2.2]
          intro w_u hw_u
          have hmem : ([], ({(w_u, true)} : PEqualNP.ProofComplexity.Clause (V ⊕ ℕ))) ∈ allClsList :=
            List.mem_append_right _ (List.mem_map.mpr ⟨w_u, hw_u, rfl⟩)
          rcases List.mem_iff_getElem.mp hmem with ⟨idx, hidx, h_eq⟩
          have hsat_j := hsat ⟨idx, hidx⟩
          dsimp only [clauses] at hsat_j
          rw [PEqualNP.Outside.L_pcx_328.clauseSat_image_castWire x ha_pos y _ (h_cl_wv ⟨idx, hidx⟩)] at hsat_j
          rw [h_sat_congr (y2 := PEqualNP.Outside.L_pcx_328.evalRev x st2.rev) (h_cl_wv ⟨idx, hidx⟩)
            (fun m hm => by change m < st2.len at hm; simp [hm, h_sat_uniq x y hsat ⟨m, hm⟩])] at hsat_j
          rw [h_eq] at hsat_j
          simp only [PEqualNP.ProofComplexity.ClauseSat, Finset.mem_singleton, exists_eq_left] at hsat_j
          exact hsat_j
      · intro x y z hsy hsz
        funext m
        have h_sat_uniq : ∀ (w : Fin a → Bool),
            (∀ j : Fin c, PEqualNP.ProofComplexity.ClauseSat (Sum.elim x w) (clauses j)) →
            w m = PEqualNP.Outside.L_pcx_328.evalRev x st2.rev m.1 := by
          intro w hsat
          let w' : ℕ → Bool := fun k => if hk : k < a then w ⟨k, hk⟩ else false
          have h_cl_wv : ∀ j : Fin c, ∀ l ∈ (allClsList[j.1]).2, PEqualNP.Outside.L_pcx_328.WireValid a l.1 := by
            intro j l hl
            have hmem : allClsList[j.1] ∈ allClsList := List.getElem_mem j.2
            rcases List.mem_append.mp hmem with hg | hu'
            · simp only [gateClsList, List.mem_flatMap, List.mem_map] at hg
              rcases hg with ⟨e, he, cl, hcl, heq⟩
              rw [← heq] at hl
              rcases PEqualNP.Outside.L_pcx_328.gateClauses_in_gate e.gate cl hcl l hl with hin | hout
              · rcases l with ⟨v | k, lb⟩
                · trivial
                · exact ((hok_rc.1.2 e he).2 k hin).1
              · rcases l with ⟨v | k, lb⟩
                · simp at hout
                · simp only [Sum.inr.injEq] at hout; subst hout
                  change e.gate.out < st2.len
                  rw [← h_rc0.1.2]
                  exact PEqualNP.Outside.L_pcx_328.wellFormedRev_out_lt h_rc0.1.1 e he
            · simp only [unitClsList, List.mem_map] at hu'
              rcases hu' with ⟨w_u, hw_u, heq⟩
              rw [← heq] at hl; simp only [Finset.mem_singleton] at hl; subst hl
              exact h_rc0.2.2.2.1 w_u hw_u
          have h_gates : ∀ e ∈ st2.rev, ∀ cl ∈ PEqualNP.Outside.L_pcx_328.gateClauses e.gate,
              PEqualNP.ProofComplexity.ClauseSat (Sum.elim x w') cl := by
            intro e he cl hcl
            have hmem : (e.node, cl) ∈ allClsList :=
              List.mem_append_left _ (List.mem_flatMap.mpr ⟨e, he, List.mem_map.mpr ⟨cl, hcl, rfl⟩⟩)
            rcases List.mem_iff_getElem.mp hmem with ⟨idx, hidx, h_eq⟩
            have hsat_j := hsat ⟨idx, hidx⟩
            dsimp only [clauses] at hsat_j
            rw [PEqualNP.Outside.L_pcx_328.clauseSat_image_castWire x ha_pos w _ (h_cl_wv ⟨idx, hidx⟩)] at hsat_j
            rw [h_eq] at hsat_j
            exact hsat_j
          have heq := PEqualNP.Outside.L_pcx_328.evalRev_unique x w' (h_rc x).1.1 h_gates m.1
            (by rw [h_rc0.1.2]; exact m.2)
          simpa [w', m.2] using heq
        rw [h_sat_uniq y hsy, h_sat_uniq z hsz]
