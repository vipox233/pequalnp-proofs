import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29826_aux

open PEqualNP.CircuitLowerBounds
abbrev W := BitVec 128

def xbit : Nat → W
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000
  | 6 => 0xffffffffffffffff0000000000000000
  | _ => 0

def target : W :=
  (xbit 0 &&& xbit 1) ||| (xbit 1 &&& xbit 2) ||| (xbit 2 &&& xbit 3) |||
  (xbit 3 &&& xbit 4) ||| (xbit 4 &&& xbit 5) ||| (xbit 5 &&& xbit 6) ||| (xbit 6 &&& xbit 0)

def seed : List W := [xbit 1, xbit 2, xbit 3, xbit 4, xbit 5, xbit 6]
def choices (vs : List W) : List W :=
  [0, -1] ++ vs ++ vs.map (~~~·) ++ vs.flatMap (fun a => vs.flatMap (fun b => [a &&& b, a ||| b]))
def corePool (a b c : W) : List W := seed ++ [a, b, c, xbit 0 ||| c]
def Suffix : Nat → List W → Prop
  | 0, vs => target ∈ vs ∨ target = 0 ∨ target = -1
  | k+1, vs => ∃ z ∈ choices vs, Suffix k (z :: vs)
def Good (c : W) : Prop :=
  (∀ j : Fin 64, target.getLsbD (2*j.val) ≠ target.getLsbD (2*j.val+1) →
    c.getLsbD (2*j.val) = false) ∧
  (∃ r : Fin 128, (xbit 0).getLsbD r.val = false ∧ (xbit 1).getLsbD r.val = false ∧
    (xbit 6).getLsbD r.val = false ∧ c.getLsbD r.val = true)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem mem_choices {v : W} {vs : List W} : v ∈ choices vs ↔
  v = 0 ∨ v = -1 ∨ v ∈ vs ∨ (∃ a ∈ vs, v = ~~~a) ∨
    (∃ a ∈ vs, ∃ b ∈ vs, v = a &&& b ∨ v = a ||| b) := by
  simp only [choices, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map, List.mem_flatMap]
  aesop

def row (r : Fin 128) (w : W) := w.getLsbD r.val

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] theorem row_one (r : Fin 128) : row r (-1) = true := by
  change (BitVec.allOnes 128).getLsbD r.val = true
  rw [BitVec.getLsbD_allOnes]; exact decide_eq_true r.isLt

def pack (f : Fin 128 → Bool) : W :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn (f := f))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] theorem row_pack (r : Fin 128) (f : Fin 128 → Bool) : row r (pack f) = f r := by
  simp only [row, pack, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left r.isLt, Option.getD_some]

def wordGate (op : GateOp) (args : List W) : W :=
  pack (fun r => op.eval (args.map (row r)))

def wstep (ws : List W) (g : Gate) : List W :=
  ws ++ [wordGate g.op (g.inputs.map (fun n => ws.getD n 0))]
def bstep (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [g.op.eval (g.inputs.map (fun n => ws.getD n false))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem map_getD (r : Fin 128) (ws : List W) (n : Nat) :
    (ws.map (row r)).getD n false = row r (ws.getD n 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ws[n]? <;> simp [row]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem map_sim (r : Fin 128) (gs : List Gate) (ws : List W) :
    (gs.foldl wstep ws).map (row r) = gs.foldl bstep (ws.map (row r)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, List.foldl_cons, ih]
    congr 1
    simp only [wstep, bstep, List.map_append, List.map_cons, List.map_nil, wordGate, row_pack, map_getD, List.map_map, Function.comp_def]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem wext {w v : W} (h : ∀ r : Fin 128, row r w = row r v) : w = v :=
  BitVec.eq_of_getLsbD_eq (fun n hn => h ⟨n,hn⟩)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem gate_choice (vs : List W) (op : GateOp) (as : List W)
    (hop : op = .and ∨ op = .or ∨ op = .not) (hlen : as.length ≤ 2)
    (hmem : ∀ u ∈ as, u = 0 ∨ u ∈ vs) : wordGate op as ∈ choices vs := by
  have h0 : (0 : W) ∈ choices vs := mem_choices.mpr (by tauto)
  have h1 : (-1 : W) ∈ choices vs := mem_choices.mpr (by tauto)
  have hu (u : W) (h : u = 0 ∨ u ∈ vs) : u ∈ choices vs := mem_choices.mpr (by tauto)
  have hn (u : W) (h : u = 0 ∨ u ∈ vs) : ~~~u ∈ choices vs := by
    rcases h with rfl | h
    · simpa using h1
    · exact mem_choices.mpr (by aesop)
  have hand (u v : W) (h : u = 0 ∨ u ∈ vs) (h' : v = 0 ∨ v ∈ vs) : u &&& v ∈ choices vs := by
    rcases h with rfl | h <;> rcases h' with rfl | h'
    all_goals first | simpa using h0 | exact mem_choices.mpr (by aesop)
  have hor (u v : W) (h : u = 0 ∨ u ∈ vs) (h' : v = 0 ∨ v ∈ vs) : u ||| v ∈ choices vs := by
    rcases h with rfl | h <;> rcases h' with rfl | h'
    all_goals first | simpa using h0 | simpa using hu _ (Or.inr ‹_›) | exact mem_choices.mpr (by aesop)
  cases as with
  | nil =>
    rcases hop with rfl | rfl | rfl
    · convert h1 using 1
      apply wext; intro r; rw [wordGate, row_pack, row_one]; rfl
    · convert h0 using 1
      apply wext; intro r; rw [wordGate, row_pack]; simp [GateOp.eval, row]
    · convert h1 using 1
      apply wext; intro r; rw [wordGate, row_pack, row_one]; rfl
  | cons a l =>
    have ha := hmem a (by simp)
    cases l with
    | nil =>
      rcases hop with rfl | rfl | rfl
      all_goals first
        | convert hu a ha using 1; apply wext; intro r; rw [wordGate, row_pack]; solve | simp [GateOp.eval, row, r.isLt]
        | convert hn a ha using 1; apply wext; intro r; rw [wordGate, row_pack]; solve | simp [GateOp.eval, row, r.isLt]
    | cons b rest =>
      have hb := hmem b (by simp)
      cases rest with
      | nil =>
        rcases hop with rfl | rfl | rfl
        all_goals first
          | convert hand a b ha hb using 1; apply wext; intro r; rw [wordGate, row_pack]; solve | simp [GateOp.eval, row, r.isLt]
          | convert hor a b ha hb using 1; apply wext; intro r; rw [wordGate, row_pack]; solve | simp [GateOp.eval, row, r.isLt]
          | convert hn a ha using 1; apply wext; intro r; rw [wordGate, row_pack]; solve | simp [GateOp.eval, row, r.isLt]
      | cons _ _ => simp at hlen

def legal (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem read_sub (ws vs : List W) (hs : ∀ w ∈ ws, w ∈ vs) (n : Nat) :
    ws.getD n 0 = 0 ∨ ws.getD n 0 ∈ vs := by
  rw [List.getD_eq_getElem?_getD]
  cases h : ws[n]? with
  | none => simp
  | some v => exact Or.inr (hs _ (List.mem_of_getElem? h))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem next_choice (g : Gate) (ws vs : List W) (hsub : ∀ w ∈ ws, w ∈ vs)
    (hlegal : legal g) (hzero : 0 ∉ g.inputs) :
    wordGate g.op (g.inputs.map (fun n => (xbit 0 :: ws).getD n 0)) ∈ choices vs := by
  apply gate_choice vs _ _ hlegal.1 (by simpa using hlegal.2)
  intro v hv
  obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hv
  cases n with
  | zero => contradiction
  | succ n => simpa [List.getD_cons_succ] using read_sub ws vs hsub n

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem finish (gs : List Gate) (ws vs : List W) (out : Nat)
    (hleg : ∀ g ∈ gs, legal g ∧ 0 ∉ g.inputs) (hsub : ∀ w ∈ ws, w ∈ vs)
    (he : (gs.foldl wstep (xbit 0 :: ws)).getD out 0 = target) : Suffix gs.length vs := by
  induction gs generalizing ws vs with
  | nil =>
    cases out with
    | zero =>
      have h : xbit 0 = target := he
      exact False.elim ((by decide : xbit 0 ≠ target) h)
    | succ n =>
      have h : ws.getD n 0 = target := he
      rcases read_sub ws vs hsub n with h0 | hm
      · exact Or.inr (Or.inl (h.symm.trans h0))
      · exact Or.inl (h ▸ hm)
  | cons g gs ih =>
    obtain ⟨hl,hz⟩ := hleg g (by simp)
    let z := wordGate g.op (g.inputs.map (fun n => (xbit 0 :: ws).getD n 0))
    exact ⟨z,next_choice g ws vs hsub hl hz,
      ih (ws ++ [z]) (z :: vs) (fun g hg => hleg _ (by simp [hg]))
        (by intro w hw; simp only [List.mem_append, List.mem_singleton] at hw; rcases hw with hw | rfl
            · exact List.mem_cons_of_mem _ (hsub _ hw)
            · simp)
        he⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem row_closed (r s : Fin 128) (vs : List W) (hs : ∀ v ∈ vs, row r v = row s v)
    (z : W) (hz : z ∈ choices vs) : row r z = row s z := by
  rcases mem_choices.mp hz with rfl | rfl | h | ⟨a, ha, rfl⟩ | ⟨a,ha,b,hb,h | h⟩
  · simp [row]
  · rw [row_one, row_one]
  · exact hs _ h
  · simpa [row, r.isLt, s.isLt] using congrArg Bool.not (hs _ ha)
  · subst z; simp only [row, BitVec.getLsbD_and]; change (row r a && row r b) = _; rw [hs a ha, hs b hb]; rfl
  · subst z; simp only [row, BitVec.getLsbD_or]; change (row r a || row r b) = _; rw [hs a ha, hs b hb]; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem suffix_closed (r s : Fin 128) (n : Nat) (vs : List W)
    (hs : ∀ v ∈ vs, row r v = row s v) (hf : Suffix n vs) : row r target = row s target := by
  induction n generalizing vs with
  | zero =>
    rcases hf with hm | h | h
    · exact hs _ hm
    · simp [h, row]
    · rw [h, row_one, row_one]
  | succ n ih =>
    obtain ⟨z,hz,hh⟩ := hf
    apply ih (z::vs) _ hh
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hm
    · exact row_closed _ _ _ hs _ hz
    · exact hs _ hm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem good_sensitive (a b c : W) (ha : a ∈ choices seed) (hb : b ∈ choices (a::seed))
    (hc : c ∈ choices (b::a::seed)) (hf : Suffix 6 (corePool a b c)) (j : Fin 64)
    (hd : target.getLsbD (2*j.val) ≠ target.getLsbD (2*j.val+1)) : c.getLsbD (2*j.val) = false := by
  let r : Fin 128 := ⟨2*j.val, by omega⟩
  let s : Fin 128 := ⟨2*j.val+1, by omega⟩
  have hbase : ∀ v ∈ seed, row r v = row s v := by
    have h : ∀ j : Fin 64, ∀ v ∈ seed, v.getLsbD (2*j.val) = v.getLsbD (2*j.val+1) := by
      simp [seed]; decide +kernel
    exact h j
  have ha' := row_closed r s seed hbase a ha
  have ha'' : ∀ v ∈ a::seed, row r v = row s v := by simpa [ha'] using And.intro ha' hbase
  have hb' := row_closed r s _ ha'' b hb
  have hb'' : ∀ v ∈ b::a::seed, row r v = row s v := by simpa [hb'] using And.intro hb' ha''
  have hc' := row_closed r s _ hb'' c hc
  cases hdigit : c.getLsbD (2*j.val) with
  | false => rfl
  | true =>
    exfalso; apply hd
    apply suffix_closed r s 6 _ _ hf
    intro v hv
    rcases List.mem_append.mp hv with h | h
    · exact hbase _ h
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl
      · exact ha'
      · exact hb'
      · exact hc'
      · have h1 : row r c = true := hdigit
        have h2 : row s c = true := hc'.symm.trans h1
        change ((xbit 0 ||| c).getLsbD r.val) = ((xbit 0 ||| c).getLsbD s.val)
        simp only [BitVec.getLsbD_or]
        change (row r (xbit 0) || row r c) = (row s (xbit 0) || row s c)
        simp [h1, h2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem four_of_len {α : Type} (gs : List α) (hl : 4 ≤ gs.length) :
    ∃ a b c d tl, gs = a::b::c::d::tl := by
  cases gs with | nil => simp at hl | cons a gs =>
  cases gs with | nil => simp at hl | cons b gs =>
  cases gs with | nil => simp at hl | cons c gs =>
  cases gs with | nil => simp at hl | cons d gs => exact ⟨a,b,c,d,gs,rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem forced_args (ns : List Nat) (hh : ns.length ≤ 2) (h0 : 0 ∈ ns) (h9 : 9 ∈ ns) :
    ns = [0,9] ∨ ns = [9,0] := by
  cases ns with
  | nil => simp at h0
  | cons a ns =>
    cases ns with
    | nil => simp at h0 h9; omega
    | cons b ns =>
      cases ns with
      | nil => simp at h0 h9; simp; omega
      | cons _ _ => simp at hh

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem prefix_sim (gs : List Gate) (ws : List W) :
    ∃ tl, gs.foldl wstep ws = ws ++ tl := by
  induction gs generalizing ws with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨tl,h⟩ := ih (wstep ws g)
    exact ⟨_ :: tl, by simpa [wstep] using h⟩

def IX (r : Fin 128) (i : Fin 7) := row r (xbit i.val)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem start_rows (r : Fin 128) : (xbit 0 :: seed).map (row r) = List.ofFn (IX r) := by rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem row_inputs (x : Fin 7 → Bool) : ∃ r : Fin 128, IX r = x := by
  let v := BitVec.ofBoolListLE (List.ofFn x)
  have hb : v.toNat < 128 := by
    have hv := v.isLt
    simpa [v] using hv
  let r : Fin 128 := ⟨v.toNat, hb⟩
  refine ⟨r, ?_⟩
  funext i
  have spec : ∀ (i : Fin 7) (r : Fin 128), (xbit i.val).getLsbD r.val = r.val.testBit i.val := by decide +kernel
  rw [IX, row, spec]
  change v.getLsbD i.val = _
  simp only [v, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left i.isLt, Option.getD_some]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem bridge (C : Circuit) (i : Fin C.gates.length) (hi : i.val = 3)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C) (hlen : C.size = 10)
    (hgraph : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
      ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0)))
    (hzi : 0 ∈ (C.gates.get i).inputs)
    (hunique : ∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i)
    (hop : (C.gates.get i).op = .or) (h9 : 9 ∈ (C.gates.get i).inputs)
    (hwit : ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧
       (C.wires (List.ofFn x)).getD 9 false = true) :
    ∃ a ∈ choices seed, ∃ b ∈ choices (a::seed), ∃ c ∈ choices (b::a::seed),
      Good c ∧ Suffix 6 (corePool a b c) := by
  change C.gates.length = 10 at hlen
  obtain ⟨p,q,t,g,tl,hgs⟩ := four_of_len C.gates (by omega)
  have hg : C.gates.get i = g := by
    change C.gates[i.val] = g
    simp [hgs, hi]
  have hl (x : Gate) (hx : x ∈ C.gates) : legal x := by
    obtain ⟨h1,h2⟩ := hfan x hx
    exact ⟨by simpa using h1,h2⟩
  have index0 (n : Nat) (hn : n < C.gates.length) (hz : 0 ∈ C.gates[n].inputs) : n = 3 :=
    (congrArg Fin.val (hunique ⟨n,hn⟩ hz)).trans hi
  have hlegal : legal p ∧ legal q ∧ legal t ∧ legal g :=
    ⟨hl p (by simp [hgs]), hl q (by simp [hgs]), hl t (by simp [hgs]), hl g (by simp [hgs])⟩
  have hzp : 0 ∉ p.inputs := by
    intro h; have := index0 0 (by omega) (by simpa [hgs] using h); omega
  have hzq : 0 ∉ q.inputs := by
    intro h; have := index0 1 (by omega) (by simpa [hgs] using h); omega
  have hzt : 0 ∉ t.inputs := by
    intro h; have := index0 2 (by omega) (by simpa [hgs] using h); omega
  have htail : ∀ d ∈ tl, legal d ∧ 0 ∉ d.inputs := by
    intro d hd
    refine ⟨hl d (by simp [hgs,hd]), ?_⟩
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp hd
    intro h
    have hn : j.val+4 < C.gates.length := by simp [hgs]
    have he : C.gates[j.val+4] = d := by simpa [hgs, Nat.add_assoc] using hj
    have := index0 _ hn (he.symm ▸ h)
    omega
  let d (g : Gate) (ws : List W) := wordGate g.op (g.inputs.map (fun n => (xbit 0 :: ws).getD n 0))
  let a := d p seed
  let b := d q (seed ++ [a])
  let c := d t (seed ++ [a,b])
  have ha : a ∈ choices seed := next_choice p seed seed (by simp) hlegal.1 hzp
  have hb : b ∈ choices (a::seed) := next_choice q (seed++[a]) (a::seed) (by
    intro w hw; simp only [List.mem_append, List.mem_singleton] at hw
    exact List.mem_cons.mpr hw.symm) hlegal.2.1 hzq
  have hc : c ∈ choices (b::a::seed) := next_choice t (seed++[a,b]) (b::a::seed) (by
    intro w hw; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢; tauto) hlegal.2.2.1 hzt
  have hgword : d g (seed++[a,b,c]) = xbit 0 ||| c := by
    have gop : g.op = .or := hg ▸ hop
    obtain h | h := forced_args g.inputs hlegal.2.2.2.2 (hg ▸ hzi) (hg ▸ h9)
    all_goals
      unfold d
      rw [gop, h]
      apply wext
      intro r
      rw [wordGate, row_pack]
      simp [seed, GateOp.eval, row, Bool.or_comm]
  let finalWords := C.gates.foldl wstep (xbit 0::seed)
  have sim (r : Fin 128) : finalWords.map (row r) = C.wires (List.ofFn (IX r)) := by
    exact (map_sim r C.gates _).trans (congrArg (C.gates.foldl bstep) (start_rows r))
  have hout : finalWords.getD C.output 0 = target := by
    apply wext
    intro r
    rw [←map_getD, sim]
    have h := hgraph (IX r)
    simpa [Circuit.eval, IX, row, target] using h
  have shape : finalWords = tl.foldl wstep (xbit 0 :: corePool a b c) := by
    unfold finalWords
    rw [hgs]
    change tl.foldl wstep (xbit 0 :: seed ++ [a,b,c,d g (seed++[a,b,c])]) = _
    rw [hgword]; rfl
  have htlen : tl.length = 6 := by
    simp only [hgs, List.length_cons] at hlen
    omega
  have hs := finish tl (corePool a b c) (corePool a b c) C.output htail (by simp) (shape ▸ hout)
  rw [htlen] at hs
  refine ⟨a,ha,b,hb,c,hc,⟨good_sensitive _ _ _ ha hb hc hs,?_⟩,hs⟩
  obtain ⟨x,h0,h1,h6,hw⟩ := hwit
  obtain ⟨r,rfl⟩ := row_inputs x
  refine ⟨r,h0,h1,h6,?_⟩
  rw [←sim, map_getD] at hw
  obtain ⟨tailWord, ht⟩ := prefix_sim tl (xbit 0 :: corePool a b c)
  rw [shape, ht] at hw
  exact hw

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem goodMask {c : W} (hc : Good c) :
    ((c &&& 0x1505150000040400040404) == 0 && (c &&& 0x1111111111111111) != 0) = true := by
  have k (r : Fin 128) : (0x1505150000040400040404 : W).getLsbD r.val = true →
      ∃ j : Fin 64, r.val = 2*j.val ∧ target.getLsbD (2*j.val) ≠ target.getLsbD (2*j.val+1) := by
    revert r; decide +kernel
  have o (r : Fin 128) : (xbit 0).getLsbD r.val = false → (xbit 1).getLsbD r.val = false →
      (xbit 6).getLsbD r.val = false → (0x1111111111111111 : W).getLsbD r.val = true := by
    revert r; decide +kernel
  have left : c &&& 0x1505150000040400040404 = 0 := by
    apply wext; intro r
    change (c &&& _).getLsbD r.val = (0:W).getLsbD r.val
    rw [BitVec.getLsbD_and]
    cases h : (0x1505150000040400040404 : W).getLsbD r.val with
    | false => simp
    | true =>
      obtain ⟨j,hj,hk⟩ := k r h
      rw [hj, hc.1 j hk]; simp
  obtain ⟨r, h0,h1,h6,hh⟩ := hc.2
  have right : c &&& 0x1111111111111111 ≠ 0 := by
    intro h
    have he := congrArg (fun x : W => x.getLsbD r.val) h
    simp only [BitVec.getLsbD_and, o r h0 h1 h6, hh, Bool.and_self, BitVec.getLsbD_zero] at he
    simpa using he
  exact Bool.and_eq_true_iff.mpr ⟨beq_iff_eq.mpr left, bne_iff_ne.mpr right⟩

namespace Signed

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 440

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 220 := ((x >>> 220) ^^^ x).setWidth 220
def cuts (ws : List W) : BitVec 220 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 220) ++ (0 : BitVec 220)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 220) (w : W) : Prop :=
  w.getLsbD (220+i.val) ≠ w.getLsbD i.val

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem ops_differs (i : Fin 220) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 220+i.val < 440 := by omega
  have hi' : i.val < 440 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem cuts_spec (ws : List W) (i : Fin 220) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 220)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) ws

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', optimized_complete hg n ws _ hnd (by omega : n+1-ws.length+ws.length=n+1) hl']⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 440 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 440)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

abbrev Raw := BitVec 128
abbrev Cell := Raw × W
def cellNot (a : Cell) : Cell := (~~~a.1, ~~~a.2)
def cellAnd (a b : Cell) : Cell := (a.1 &&& b.1, a.2 &&& b.2)
def cellOr (a b : Cell) : Cell := (a.1 ||| b.1, a.2 ||| b.2)
def selections (vs : List Cell) : List Cell :=
  [(0,0),(-1,-1)] ++ vs ++ vs.map cellNot ++
  vs.flatMap (fun a => vs.flatMap (fun b => [cellAnd a b,cellOr a b]))
def raw (j : Nat) : Raw := ([0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000] : List Raw).getD j 0
def paired (j : Nat) : W := ([0x2af86986ea4c194bed1b79ebb5925c25ad6174264f18af423d920d4a894a900c2081043c911698331907460046164260618ad022d82084,0x9cd746aebcf9705d18c5944b8f7c8e065dd701f378544ee59004238144316220df0608c00a010080c440b16598601d1780442659000218,0xdf1dcb7862038514b69a8c47337e31023436604512f109b9066ece7c914c148220781023e0b8060333130002430600400f10888064ece5,0x4280be77c5fa491d27f00a9f3b82cbae42820cf80a2cb572c23bf9602021424c1e8283d4170389f4806c12642820cf80a00b5728031012,0xb1eb041993fecdc403ceaedc7390f8c1d0c8dd1de09c108e7c8e74191a8001110140140128a044033000cc090485101e09c00885c8e740,0x557338ac9c33f6bc8a3e600a5c4bf27f4e288ba6a0a3c17fa5c10a9445339cc840344948904211a400ab01b4c208aa60021817721010a9,0x7e3875025f55ab63c662c5e428211abea2a472c1e547f2888b5155a1328400319d4a9200662846400010a0422841041e14652888250552] : List W).getD j 0
def prim (j : Nat) : Cell := (raw j, paired j)
def basis : List Cell := [prim 1, prim 2, prim 3, prim 4, prim 5, prim 6]
def maskOK (c : Cell) : Bool := (c.1 &&& 0x1505150000040400040404) == 0 && (c.1 &&& 0x1111111111111111) != 0
def pool (a b c : Cell) : List W :=
  ((basis.map Prod.snd ++ [a.2,b.2,c.2,(prim 0).2 ||| c.2]).filter
     (fun z => z != 0 && z != -1)).dedup
def walk (n : Nat) (chosen : List W) (cs : BitVec 220) : List W → Bool
  | [] => decide (chosen.length ≤ n+1) && (cs == -1) && optimized n (n+1-chosen.length) chosen
  | w :: ws => ((cs ||| sep w ||| cuts ws) == -1) &&
      (walk n chosen cs ws || (decide (chosen.length < n+1) && walk n (w::chosen) (cs ||| sep w) ws))
def goC (a b c : Cell) : Bool := maskOK c && walk 6 [] 0 (pool a b c)
def goB (a b : Cell) : Bool := ((selections (b :: a :: basis)).filter maskOK).eraseDups.any (goC a b)
def goA (a : Cell) : Bool := (selections (a :: basis)).eraseDups.any (goB a)
def checkAll : Bool := (selections basis).eraseDups.any goA

def sampleRows : List Nat := [36,72,5,34,74,36,84,37,80,18,84,4,40,21,20,20,72,8,68,17,33,68,21,17,18,33,16,74,34,41,34,84,40,42,42,84,41,66,9,5,72,9,66,41,36,64,82,17,21,36,68,20,64,9,1,10,2,82,82,80,82,33,37,8,10,41,74,42,18,32,9,40,80,5,21,32,1,10,66,16,4,37,17,74,2,72,37,34,18,68,42,16,32,42,74,32,34,9,17,16,10,66,17,82,37,37,9,40,68,40,10,32,5,4,2,1,21,20,2,10,21,21,40,0,9,41,72,42,40,68,84,9,33,0,80,9,10,41,1,68,5,84,32,20,9,74,72,18,41,84,68,37,20,4,9,33,9,5,42,10,40,72,17,34,84,0,32,72,1,74,34,68,36,36,84,9,82,10,74,74,74,5,34,66,80,4,9,41,80,66,40,36,16,10,36,32,37,2,10,33,42,33,68,5,34,42,5,80,37,80,34,17,84,72,34,5,82,1,36,21,52,76,13,98,75,38,85,45,88,26,92,12,104,29,22,28,73,12,100,49,97,76,53,81,19,49,24,106,38,57,50,116,44,46,43,86,45,67,11,7,88,73,98,105,100,96,90,25,23,44,70,52,65,13,65,11,6,114,83,112,86,35,53,24,26,43,78,106,50,96,25,56,81,69,85,48,3,14,70,48,6,101,19,90,3,104,39,35,22,69,58,81,49,110,107,104,96,105,48,88,12,106,3,91,117,52,57,58,96,45,6,38,23,70,38,25,31,30,35,106,61,93,48,3,15,47,92,59,24,65,87,89,65,24,86,29,3,49,97,86,3,117,50,53,45,104,90,30,25,124,77,35,6,13,65,101,75,65,62,43,46,96,83,48,93,96,52,89,35,98,58,116,102,60,81,27,122,58,91,26,88,85,106,99,114,7,77,59,24,75,43,54,28,46,12,35,69,14,90,45,104,105,71,12,54,50,6,85,103,113,51,27,52,77,102,71,118,81,108,22]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem cuts_append (a b : List W) : cuts (a++b) = (cuts a ||| cuts b) := by
  induction a with
  | nil => simp [cuts]
  | cons x xs ih => simpa only [List.cons_append, cuts, List.foldr_cons, BitVec.or_assoc] using congrArg (sep x ||| ·) ih

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem cuts_of_sub {g : W} (hg : g = goal ∨ g = ~~~goal) {k : Nat} {s : Finset W}
    (h : live basicOps g k s) (ls : List W) (hm : ∀ w ∈ s, w ∈ ls) : cuts ls = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl|rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro i hi
  obtain ⟨w,hw,d⟩ := live_separates (differs ⟨i,hi⟩) (hd ⟨i,hi⟩) (ops_differs ⟨i,hi⟩) h
  have hh := (cuts_spec ls ⟨i,hi⟩).mpr ⟨w,hm w hw,d⟩
  change (cuts ls)[i] = (BitVec.allOnes 220)[i]
  simpa only [BitVec.getElem_allOnes, BitVec.getLsbD_eq_getElem hi] using hh

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem walk_complete {g : W} (hg : g = goal ∨ g = ~~~goal) {k : Nat} {s : Finset W}
    (hl : live basicOps g k s) (cs ws : List W)
    (cn : cs.Nodup) (wn : ws.Nodup) (dis : ∀ w ∈ cs, w ∉ ws)
    (cin : ∀ w ∈ cs, w ∈ s) (sin : ∀ w ∈ s, w ∈ cs ∨ w ∈ ws) :
    walk k cs (cuts cs) ws = true := by
  induction ws generalizing cs with
  | nil =>
    have eq : cs.toFinset = s := by ext v; simp only [List.mem_toFinset]; exact ⟨cin v,fun h => (sin v h).resolve_right (List.not_mem_nil)⟩
    have h' : live basicOps g k cs.toFinset := eq.symm ▸ hl
    have card := live_card h'
    rw [List.toFinset_card_of_nodup cn] at card
    simp only [walk, decide_eq_true card, cuts_full hg h', beq_self_eq_true, Bool.true_and,
      optimized_complete hg k cs _ cn (by omega : k+1-cs.length+cs.length=k+1) h']
  | cons w ws ih =>
    have sub : ∀ v ∈ s, v ∈ cs ++ (w :: ws) := by simpa only [List.mem_append] using sin
    have full := cuts_of_sub hg hl (cs ++ (w :: ws)) sub
    rw [cuts_append] at full
    change (cuts cs ||| (sep w ||| cuts ws)) = -1 at full
    rw [walk, BitVec.or_assoc, full, beq_self_eq_true, Bool.true_and, Bool.or_eq_true]
    obtain ⟨nw,nws⟩ := List.nodup_cons.mp wn
    by_cases hit : w ∈ s
    · right
      have wc : w ∉ cs := fun m => dis w m List.mem_cons_self
      have includeSet : insert w cs.toFinset ⊆ s := by
        exact Finset.insert_subset hit (fun z hz => cin _ (List.mem_toFinset.mp hz))
      have hc := Finset.card_le_card includeSet
      have wc' : w ∉ cs.toFinset := by simpa using wc
      rw [Finset.card_insert_of_notMem wc',List.toFinset_card_of_nodup cn] at hc
      have bound := live_card hl
      have len : cs.length < k+1 := by omega
      rw [decide_eq_true len, Bool.true_and]
      have run := ih (w::cs) (List.nodup_cons.mpr ⟨wc,cn⟩) nws (by
        intro z hz; rcases List.mem_cons.mp hz with rfl|hz
        · exact nw
        · exact fun m => dis z hz (List.mem_cons_of_mem _ m)) (by
        intro z hz; rcases List.mem_cons.mp hz with rfl|hz
        · exact hit
        · exact cin z hz) (by
        intro z hz; rcases sin z hz with hm|hm
        · exact .inl (List.mem_cons_of_mem _ hm)
        · rcases List.mem_cons.mp hm with rfl|hm
          · exact .inl List.mem_cons_self
          · exact .inr hm)
      simpa only [cuts, List.foldr_cons, BitVec.or_comm (sep w)] using run
    · left
      apply ih cs cn nws (fun z hz m => dis z hz (List.mem_cons_of_mem _ m)) cin
      intro z hz
      rcases sin z hz with hm|hm
      · exact .inl hm
      · rcases List.mem_cons.mp hm with rfl|hm
        · exact False.elim (hit hz)
        · exact .inr hm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem walk_root {g : W} (hg : g = goal ∨ g = ~~~goal) {k : Nat} {xs : List W} (hn : xs.Nodup)
    (h : build basicOps g k xs.toFinset) : walk k [] 0 xs = true := by
  obtain ⟨s,ss,hl⟩ := compress h
  apply walk_complete hg hl [] xs (by simp) hn (by simp) (by simp)
  intro w hw
  exact .inr (List.mem_toFinset.mp (ss hw))

open PEqualNP.Outside.L_meta_29826_aux

def image (x : Raw) : W :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 440 => x.getLsbD (sampleRows.getD j.val 0)))).cast List.length_ofFn

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem sample_bound : ∀ i : Fin 440, sampleRows.getD i.val 0 < 128 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] theorem image_get (x : Raw) (j : Nat) (hj : j < 440) :
    (image x).getLsbD j = x.getLsbD (sampleRows.getD j 0) := by
  simp only [image, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
    List.getElem?_ofFn, dif_pos hj, Option.getD_some]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem image_eq {a b : W} (h : ∀ i : Nat, i < 440 → a.getLsbD i = b.getLsbD i) : a = b := by
  apply BitVec.eq_of_getElem_eq
  exact h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] theorem image_and (a b : Raw) : image (a &&& b) = image a &&& image b := by
  apply image_eq; intro i hi; simp only [BitVec.getLsbD_and, image_get _ i hi]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] theorem image_or (a b : Raw) : image (a ||| b) = image a ||| image b := by
  apply image_eq; intro i hi; simp only [BitVec.getLsbD_or, image_get _ i hi]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] theorem image_not (a : Raw) : image (~~~a) = ~~~image a := by
  apply image_eq; intro i hi; simp only [BitVec.getLsbD_not, image_get _ i hi,
    decide_eq_true hi, decide_eq_true (sample_bound ⟨i,hi⟩),Bool.true_and]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] theorem image_zero : image 0 = 0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
@[local simp] theorem image_one : image (-1) = -1 := by
  change image (~~~(0 : Raw)) = ~~~(0 : W)
  rw [image_not,image_zero]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem image_target : image target = goal := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem prims : ∀ j : Fin 7, prim j.val = (xbit j.val, image (xbit j.val)) := by decide +kernel

def together (a : Raw) : Cell := (a,image a)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem basis_eq : basis = seed.map together := by
  simp only [basis, seed, List.map_cons, List.map_nil, together]
  rw [prims ⟨1,by decide⟩,prims ⟨2,by decide⟩,prims ⟨3,by decide⟩,
    prims ⟨4,by decide⟩,prims ⟨5,by decide⟩,prims ⟨6,by decide⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem select_sound {vs : List Raw} {a : Raw} (h : a ∈ choices vs) :
    together a ∈ selections (vs.map together) := by
  simp only [selections, List.mem_append, List.mem_cons, List.mem_singleton, List.mem_map,
    List.mem_flatMap, List.mem_nil_iff, or_false]
  rcases mem_choices.mp h with rfl | rfl | ha | ⟨b,hb,rfl⟩ | ⟨b,hb,c,hc,he⟩
  · exact .inl (.inl (.inl (.inl (Prod.ext rfl image_zero))))
  · exact .inl (.inl (.inl (.inr (Prod.ext rfl image_one))))
  · exact .inl (.inl (.inr ⟨a,ha,rfl⟩))
  · exact .inl (.inr ⟨together b,⟨b,hb,rfl⟩,by simp [together,cellNot]⟩)
  · right
    refine ⟨together b, ⟨b,hb,rfl⟩, together c, ⟨c,hc,rfl⟩, ?_⟩
    rcases he with rfl | rfl
    · left; simp [together,cellAnd]
    · right; simp [together,cellOr]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem choose_reach {vs : List Raw} {av : Finset W} {x : Raw}
    (ha : ∀ v ∈ vs, holds av (image v)) (h : x ∈ choices vs) : reachable av (image x) := by
  rcases mem_choices.mp h with rfl | rfl | hv | ⟨y,hy,rfl⟩ | ⟨a,hm,b,hn,he⟩
  · rw [image_zero]; exact .inl (.inl rfl)
  · rw [image_one]; exact .inl (.inr (.inl rfl))
  · exact .inl (ha _ hv)
  · rw [image_not]; exact .inl (holds_not (ha _ hy))
  · rcases he with rfl | rfl
    · rw [image_and]; exact and_reach (ha _ hm) (ha _ hn)
    · rw [image_or]; exact or_reach (ha _ hm) (ha _ hn)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem signed_suffix (k : Nat) (vs : List Raw) (h : Suffix k vs) (av : Finset W)
    (ha : ∀ v ∈ vs, holds av (image v)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t k av := by
  induction k generalizing vs av with
  | zero =>
    rcases h with ht | ht | ht
    · have hh := ha _ ht
      rw [image_target] at hh
      rcases hh with hz | ho | ⟨t,hm,eq|eq⟩
      · exact False.elim ((by decide : goal ≠ 0) hz)
      · exact False.elim ((by decide : goal ≠ ~~~0) ho)
      · exact ⟨t,.inl eq.symm,hm⟩
      · exact ⟨t,.inr (by simpa using congrArg (fun v : W => ~~~v) eq.symm),hm⟩
    · exact False.elim ((by decide : target ≠ 0) ht)
    · exact False.elim ((by decide : target ≠ -1) ht)
  | succ k ih =>
    obtain ⟨z,hz,hs⟩ := h
    rcases choose_reach ha hz with ok | ⟨a,ha',b,hb,hn,w,hw,hold⟩
    · obtain ⟨t,e,run⟩ := ih _ hs av (by simpa [ok] using ha)
      exact ⟨t,e,.inl run⟩
    · obtain ⟨t,e,run⟩ := ih _ hs (insert w av) (by
        intro x hx; rcases List.mem_cons.mp hx with rfl|hx
        · exact hold
        · exact holds_insert (ha _ hx))
      exact ⟨t,e,.inr ⟨a,ha',b,hb,hn,w,hw,run⟩⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem pool_holds (a b c : Raw) (v : Raw) (hv : v ∈ corePool a b c) :
    holds (pool (together a) (together b) (together c)).toFinset (image v) := by
  by_cases hz : image v = 0
  · exact .inl hz
  by_cases ho : image v = -1
  · exact .inr (.inl ho)
  refine .inr (.inr ⟨image v,?_,.inl rfl⟩)
  apply List.mem_toFinset.mpr
  unfold pool
  apply List.mem_dedup.mpr
  apply List.mem_filter.mpr
  constructor
  · have hm : image v ∈ (corePool a b c).map image := List.mem_map.mpr ⟨v,hv,rfl⟩
    simpa only [basis_eq, corePool, List.map_append, List.map_cons, List.map_nil, List.map_map,
      prims ⟨0,by decide⟩, together, Function.comp_def, image_or] using hm
  · rw [Bool.and_eq_true]
    exact ⟨bne_iff_ne.mpr hz,bne_iff_ne.mpr ho⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem sound {a b c : Raw} (h1 : a ∈ choices seed) (h2 : b ∈ choices (a::seed))
    (h3 : c ∈ choices (b::a::seed)) (hc : maskOK (together c) = true)
    (h : Suffix 6 (corePool a b c)) : checkAll = true := by
  obtain ⟨t,ht,hb⟩ := signed_suffix _ _ h _ (pool_holds a b c)
  have nodup : (pool (together a) (together b) (together c)).Nodup := List.nodup_dedup _
  have w := walk_root ht nodup hb
  apply List.any_eq_true.mpr
  refine ⟨together a, List.mem_eraseDups.mpr ?_, ?_⟩
  · simpa only [basis_eq] using select_sound h1
  · apply List.any_eq_true.mpr
    refine ⟨together b, List.mem_eraseDups.mpr ?_, ?_⟩
    · simpa only [basis_eq, List.map_cons] using select_sound h2
    · apply List.any_eq_true.mpr
      refine ⟨together c, List.mem_eraseDups.mpr (List.mem_filter.mpr ⟨?_,hc⟩), ?_⟩
      · simpa only [basis_eq, List.map_cons] using select_sound h3
      · change (maskOK (together c) && walk 6 [] 0 _) = true
        rw [hc, Bool.true_and]
        exact w

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA0 : goA (0x0,0x0) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA1 : goA (0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA2 : goA (0xcccccccccccccccccccccccccccccccc,0x9cd746aebcf9705d18c5944b8f7c8e065dd701f378544ee59004238144316220df0608c00a010080c440b16598601d1780442659000218) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA3 : goA (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xdf1dcb7862038514b69a8c47337e31023436604512f109b9066ece7c914c148220781023e0b8060333130002430600400f10888064ece5) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA4 : goA (0xff00ff00ff00ff00ff00ff00ff00ff00,0x4280be77c5fa491d27f00a9f3b82cbae42820cf80a2cb572c23bf9602021424c1e8283d4170389f4806c12642820cf80a00b5728031012) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA5 : goA (0xffff0000ffff0000ffff0000ffff0000,0xb1eb041993fecdc403ceaedc7390f8c1d0c8dd1de09c108e7c8e74191a8001110140140128a044033000cc090485101e09c00885c8e740) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA6 : goA (0xffffffff00000000ffffffff00000000,0x557338ac9c33f6bc8a3e600a5c4bf27f4e288ba6a0a3c17fa5c10a9445339cc840344948904211a400ab01b4c208aa60021817721010a9) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA7 : goA (0xffffffffffffffff0000000000000000,0x7e3875025f55ab63c662c5e428211abea2a472c1e547f2888b5155a1328400319d4a9200662846400010a0422841041e14652888250552) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA8 : goA (0x33333333333333333333333333333333,0x6328b95143068fa2e73a6bb4708371f9a228fe0c87abb11a6ffbdc7ebbce9ddf20f9f73ff5feff7f3bbf4e9a679fe2e87fbbd9a6fffde7) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA9 : goA (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,0x20e234879dfc7aeb496573b8cc81cefdcbc99fbaed0ef646f99131836eb3eb7ddf87efdc1f47f9fcccecfffdbcf9ffbff0ef777f9b131a) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA10 : goA (0xff00ff00ff00ff00ff00ff00ff00ff,0xbd7f41883a05b6e2d80ff560c47d3451bd7df307f5d34a8d3dc4069fdfdebdb3e17d7c2be8fc760b7f93ed9bd7df307f5ff4a8d7fcefed) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA11 : goA (0xffff0000ffff0000ffff0000ffff,0x4e14fbe66c01323bfc3151238c6f073e2f3722e21f63ef7183718be6e57ffeeefebfebfed75fbbfccfff33f6fb7aefe1f63ff77a3718bf) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA12 : goA (0xffffffff00000000ffffffff,0xaa8cc75363cc094375c19ff5a3b40d80b1d774595f5c3e805a3ef56bbacc6337bfcbb6b76fbdee5bff54fe4b3df7559ffde7e88defef56) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA13 : goA (0xffffffffffffffff,0x81c78afda0aa549c399d3a1bd7dee5415d5b8d3e1ab80d7774aeaa5ecd7bffce62b56dff99d7b9bfffef5fbdd7befbe1eb9ad777dafaad) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA14 : goA (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0,0x9c1542282001001410808443037c000214160041105008a100040200000000000000000000000000000000000000000000000000000000) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA15 : goA (0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,0xdfdfcffefefbf55dbedf9c4fbf7ebf067df761f77af54ffd966eeffdd57d76a2ff7e18e3eab90683f753b167db661d578f54aed964eefd) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA16 : goA (0xcc00cc00cc00cc00cc00cc00cc00cc00,0x80062684f8401d00c0000b0b008a06408200f00804046080002100002142001e0200c0020100808040106408200d0080000608000010) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA17 : goA (0xffccffccffccffccffccffccffccffcc,0xded7fefffdfb795d3ff59edfbffecfae5fd70dfb7a7cfff7d23ffbe16431626cdf868bd41f0389f4c46cb365b860df97a04f777903121a) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA18 : goA (0xcccc0000cccc0000cccc0000cccc0000,0x90c3040890f8404400c484480310880050c001116014008410042001000000000100000008000000000080010000101600400001000200) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA19 : goA (0xffffccccffffccccffffccccffffcccc,0xbdff46bfbffffddd1bcfbedffffcfec7dddfddfff8dc5eeffc8e77995eb16331df461cc12aa14483f440fd6d9ce51d1f89c42eddc8e758) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA20 : goA (0xcccccccc00000000cccccccc00000000,0x145300ac9c31701c0804000a0c4882064c0001a22000406580000280443100004004084000000080000001248000080000000650000008) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA21 : goA (0xffffffffccccccccffffffffcccccccc,0xddf77eaebcfbf6fd9afff44bdf7ffe7f5fff8bf7f8f7cfffb5c52b954533fee8df3649c89a4311a4c4ebb1f5da68bf77825c377b1012b9) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA22 : goA (0xcccccccccccccccc0000000000000000,0x1c1044021c5120410040844008200a06008400c16044428080000181000000209d020000020000000000a0400840041600442008000010) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA23 : goA (0xffffffffffffffffcccccccccccccccc,0xfeff77aefffdfb7fdee7d5efaf7d9ebefff773f3fd57feed9b5577a176b56231df4e9ac06e2946c0c450b167b8611d1f94652ed925075a) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA24 : goA (0xf000f000f000f000f000f000f000f000,0x42008a704002011426900807330201020002004002200130022ac860000000000000000000000000000000000000000000000000000000) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA25 : goA (0xfff0fff0fff0fff0fff0fff0fff0fff0,0xdf9dff7fe7fbcd1db7fa8edf3bfefbae76b66cfd1afdbdfbc67fff7cb16d56ce3efa93f7f7bb8ff7b37f12666b26cfc0af1bdfa867fcf7) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA26 : goA (0xf0f00000f0f00000f0f00000f0f00000,0x9109001802028504028a8c44331030001000400500900088040e4418100000000040100120a0040330000000000400000900088040e440) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA27 : goA (0xfffff0f0fffff0f0fffff0f0fffff0f0,0xffffcf79f3ffcdd4b7deaedf73fef9c3f4fefd5df2fd19bf7eeefe7d9bcc159321781423e8b846033313cc0b4787105e0fd08885ecefe5) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA28 : goA (0xf0f0f0f000000000f0f0f0f000000000,0x5511082800038414821a0002104a30020420000400a1013904400a140100148000300000800000000003000042000040021000000000a1) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA29 : goA (0xfffffffff0f0f0f0fffffffff0f0f0f0,0xdf7ffbfcfe33f7bcbebeec4f7f7ff37f7e3eebe7b2f3c9ffa7efcefcd57f9cca607c596bf0fa17a733bb01b6c30eaa600f189ff274fced) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA30 : goA (0xf0f0f0f0f0f0f0f00000000000000000,0x5e184100420181008602844420201002202460410041008802404420100400000048100060280600001000020000000004000880240440) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA31 : goA (0xfffffffffffffffff0f0f0f0f0f0f0f0,0xff3dff7a7f57af77f6facde73b7f3bbeb6b672c5f7f7fbb98f7fdffdb3cc14b3bd7a9223e6b846433313a0426b47045e1f75a88865edf7) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA32 : goA (0xff000000ff000000ff000000ff000000,0x80041181fa490403c00a9c3380c88040800c18000c1002400a7000000000000000000000000000000000000000000000000000000000) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA33 : goA (0xffffff00ffffff00ffffff00ffffff00,0xf3ebbe7fd7fecddd27feaedf7b92fbefd2caddfdeabcb5fefebffd793aa1435d1fc297d53fa3cdf7b06cde6d2ca5df9ea9cb5fadcbf752) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA34 : goA (0xff00ff0000000000ff00ff0000000000,0x400038248432401c0230000a1802c22e420008a000208172800108000021004800000140100201a40028002400008a0000081720001000) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA35 : goA (0xffffffffff00ff00ffffffffff00ff00,0x57f3beffddfbffbdaffe6a9f7fcbfbff4eaa8ffeaaaff57fe7fbfbf46533decc5eb6cbdc974399f480ef13f4ea28efe0a21b577a1310bb) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA36 : goA (0xff00ff00ff00ff000000000000000000,0x42003402455009010660008428000aae028000c00004b00082115120200000001c02820006000040000000402800040000010008010012) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA37 : goA (0xffffffffffffffffff00ff00ff00ff00,0x7eb8ff77dfffeb7fe7f2cfff3ba3dbbee2a67ef9ef6ff7facb7bfde132a5427d9fca93d4772bcff4807cb2662861cf9eb46f7fa8271552) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA38 : goA (0xffff000000000000ffff000000000000,0x116300089032c484020e20085000f04140088904a080000e24800010000000000000000000000000000000000000000000000000000000) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA39 : goA (0xffffffffffff0000ffffffffffff0000,0xf5fb3cbd9ffffffc8bfeeede7fdbfaffdee8dfbfe0bfd1fffdcf7e9d5fb39dd941745d49b8e255a730abcdbdc68dba7e0bd81ff7d8f7e9) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA40 : goA (0xffff0000ffff00000000000000000000,0x3028040013548940024284c42000188080805001e004108808005401128000110140100020204400000080000001001e00400880000540) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA41 : goA (0xffffffffffffffffffff0000ffff0000,0xfffb751bdfffefe7c7eeeffc7bb1fafff2ecffdde5dff28effdf75b93a8401319d4a96016ea846433010ec4b2cc5141e1de5288dede752) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA42 : goA (0xffffffff000000000000000000000000,0x543030001c11a220822240000801123e02200280a003c00881410080000000000000000000000000000000000000000000000000000000) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certA43 : goA (0xffffffffffffffffffffffff00000000,0x7f7b7daedf77ffffce7ee5ee7c6bfaffeeacfbe7e5e7f3ffafd15fb577b79cf9dd7edb48f66a57e400bba1f6ea49ae7e167d3ffa3515fb) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem certRoots : (selections basis).eraseDups = [
(0x0,0x0),
(0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff),
(0xcccccccccccccccccccccccccccccccc,0x9cd746aebcf9705d18c5944b8f7c8e065dd701f378544ee59004238144316220df0608c00a010080c440b16598601d1780442659000218),
(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xdf1dcb7862038514b69a8c47337e31023436604512f109b9066ece7c914c148220781023e0b8060333130002430600400f10888064ece5),
(0xff00ff00ff00ff00ff00ff00ff00ff00,0x4280be77c5fa491d27f00a9f3b82cbae42820cf80a2cb572c23bf9602021424c1e8283d4170389f4806c12642820cf80a00b5728031012),
(0xffff0000ffff0000ffff0000ffff0000,0xb1eb041993fecdc403ceaedc7390f8c1d0c8dd1de09c108e7c8e74191a8001110140140128a044033000cc090485101e09c00885c8e740),
(0xffffffff00000000ffffffff00000000,0x557338ac9c33f6bc8a3e600a5c4bf27f4e288ba6a0a3c17fa5c10a9445339cc840344948904211a400ab01b4c208aa60021817721010a9),
(0xffffffffffffffff0000000000000000,0x7e3875025f55ab63c662c5e428211abea2a472c1e547f2888b5155a1328400319d4a9200662846400010a0422841041e14652888250552),
(0x33333333333333333333333333333333,0x6328b95143068fa2e73a6bb4708371f9a228fe0c87abb11a6ffbdc7ebbce9ddf20f9f73ff5feff7f3bbf4e9a679fe2e87fbbd9a6fffde7),
(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,0x20e234879dfc7aeb496573b8cc81cefdcbc99fbaed0ef646f99131836eb3eb7ddf87efdc1f47f9fcccecfffdbcf9ffbff0ef777f9b131a),
(0xff00ff00ff00ff00ff00ff00ff00ff,0xbd7f41883a05b6e2d80ff560c47d3451bd7df307f5d34a8d3dc4069fdfdebdb3e17d7c2be8fc760b7f93ed9bd7df307f5ff4a8d7fcefed),
(0xffff0000ffff0000ffff0000ffff,0x4e14fbe66c01323bfc3151238c6f073e2f3722e21f63ef7183718be6e57ffeeefebfebfed75fbbfccfff33f6fb7aefe1f63ff77a3718bf),
(0xffffffff00000000ffffffff,0xaa8cc75363cc094375c19ff5a3b40d80b1d774595f5c3e805a3ef56bbacc6337bfcbb6b76fbdee5bff54fe4b3df7559ffde7e88defef56),
(0xffffffffffffffff,0x81c78afda0aa549c399d3a1bd7dee5415d5b8d3e1ab80d7774aeaa5ecd7bffce62b56dff99d7b9bfffef5fbdd7befbe1eb9ad777dafaad),
(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0,0x9c1542282001001410808443037c000214160041105008a100040200000000000000000000000000000000000000000000000000000000),
(0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,0xdfdfcffefefbf55dbedf9c4fbf7ebf067df761f77af54ffd966eeffdd57d76a2ff7e18e3eab90683f753b167db661d578f54aed964eefd),
(0xcc00cc00cc00cc00cc00cc00cc00cc00,0x80062684f8401d00c0000b0b008a06408200f00804046080002100002142001e0200c0020100808040106408200d0080000608000010),
(0xffccffccffccffccffccffccffccffcc,0xded7fefffdfb795d3ff59edfbffecfae5fd70dfb7a7cfff7d23ffbe16431626cdf868bd41f0389f4c46cb365b860df97a04f777903121a),
(0xcccc0000cccc0000cccc0000cccc0000,0x90c3040890f8404400c484480310880050c001116014008410042001000000000100000008000000000080010000101600400001000200),
(0xffffccccffffccccffffccccffffcccc,0xbdff46bfbffffddd1bcfbedffffcfec7dddfddfff8dc5eeffc8e77995eb16331df461cc12aa14483f440fd6d9ce51d1f89c42eddc8e758),
(0xcccccccc00000000cccccccc00000000,0x145300ac9c31701c0804000a0c4882064c0001a22000406580000280443100004004084000000080000001248000080000000650000008),
(0xffffffffccccccccffffffffcccccccc,0xddf77eaebcfbf6fd9afff44bdf7ffe7f5fff8bf7f8f7cfffb5c52b954533fee8df3649c89a4311a4c4ebb1f5da68bf77825c377b1012b9),
(0xcccccccccccccccc0000000000000000,0x1c1044021c5120410040844008200a06008400c16044428080000181000000209d020000020000000000a0400840041600442008000010),
(0xffffffffffffffffcccccccccccccccc,0xfeff77aefffdfb7fdee7d5efaf7d9ebefff773f3fd57feed9b5577a176b56231df4e9ac06e2946c0c450b167b8611d1f94652ed925075a),
(0xf000f000f000f000f000f000f000f000,0x42008a704002011426900807330201020002004002200130022ac860000000000000000000000000000000000000000000000000000000),
(0xfff0fff0fff0fff0fff0fff0fff0fff0,0xdf9dff7fe7fbcd1db7fa8edf3bfefbae76b66cfd1afdbdfbc67fff7cb16d56ce3efa93f7f7bb8ff7b37f12666b26cfc0af1bdfa867fcf7),
(0xf0f00000f0f00000f0f00000f0f00000,0x9109001802028504028a8c44331030001000400500900088040e4418100000000040100120a0040330000000000400000900088040e440),
(0xfffff0f0fffff0f0fffff0f0fffff0f0,0xffffcf79f3ffcdd4b7deaedf73fef9c3f4fefd5df2fd19bf7eeefe7d9bcc159321781423e8b846033313cc0b4787105e0fd08885ecefe5),
(0xf0f0f0f000000000f0f0f0f000000000,0x5511082800038414821a0002104a30020420000400a1013904400a140100148000300000800000000003000042000040021000000000a1),
(0xfffffffff0f0f0f0fffffffff0f0f0f0,0xdf7ffbfcfe33f7bcbebeec4f7f7ff37f7e3eebe7b2f3c9ffa7efcefcd57f9cca607c596bf0fa17a733bb01b6c30eaa600f189ff274fced),
(0xf0f0f0f0f0f0f0f00000000000000000,0x5e184100420181008602844420201002202460410041008802404420100400000048100060280600001000020000000004000880240440),
(0xfffffffffffffffff0f0f0f0f0f0f0f0,0xff3dff7a7f57af77f6facde73b7f3bbeb6b672c5f7f7fbb98f7fdffdb3cc14b3bd7a9223e6b846433313a0426b47045e1f75a88865edf7),
(0xff000000ff000000ff000000ff000000,0x80041181fa490403c00a9c3380c88040800c18000c1002400a7000000000000000000000000000000000000000000000000000000000),
(0xffffff00ffffff00ffffff00ffffff00,0xf3ebbe7fd7fecddd27feaedf7b92fbefd2caddfdeabcb5fefebffd793aa1435d1fc297d53fa3cdf7b06cde6d2ca5df9ea9cb5fadcbf752),
(0xff00ff0000000000ff00ff0000000000,0x400038248432401c0230000a1802c22e420008a000208172800108000021004800000140100201a40028002400008a0000081720001000),
(0xffffffffff00ff00ffffffffff00ff00,0x57f3beffddfbffbdaffe6a9f7fcbfbff4eaa8ffeaaaff57fe7fbfbf46533decc5eb6cbdc974399f480ef13f4ea28efe0a21b577a1310bb),
(0xff00ff00ff00ff000000000000000000,0x42003402455009010660008428000aae028000c00004b00082115120200000001c02820006000040000000402800040000010008010012),
(0xffffffffffffffffff00ff00ff00ff00,0x7eb8ff77dfffeb7fe7f2cfff3ba3dbbee2a67ef9ef6ff7facb7bfde132a5427d9fca93d4772bcff4807cb2662861cf9eb46f7fa8271552),
(0xffff000000000000ffff000000000000,0x116300089032c484020e20085000f04140088904a080000e24800010000000000000000000000000000000000000000000000000000000),
(0xffffffffffff0000ffffffffffff0000,0xf5fb3cbd9ffffffc8bfeeede7fdbfaffdee8dfbfe0bfd1fffdcf7e9d5fb39dd941745d49b8e255a730abcdbdc68dba7e0bd81ff7d8f7e9),
(0xffff0000ffff00000000000000000000,0x3028040013548940024284c42000188080805001e004108808005401128000110140100020204400000080000001001e00400880000540),
(0xffffffffffffffffffff0000ffff0000,0xfffb751bdfffefe7c7eeeffc7bb1fafff2ecffdde5dff28effdf75b93a8401319d4a96016ea846433010ec4b2cc5141e1de5288dede752),
(0xffffffff000000000000000000000000,0x543030001c11a220822240000801123e02200280a003c00881410080000000000000000000000000000000000000000000000000000000),
(0xffffffffffffffffffffffff00000000,0x7f7b7daedf77ffffce7ee5ee7c6bfaffeeacfbe7e5e7f3ffafd15fb577b79cf9dd7edb48f66a57e400bba1f6ea49ae7e167d3ffa3515fb)] := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem checkFailed : checkAll = false := by
  unfold checkAll
  rw [certRoots]
  simp only [List.any_cons, List.any_nil, Bool.false_or, certA0, certA1, certA2, certA3, certA4, certA5, certA6, certA7, certA8, certA9, certA10, certA11, certA12, certA13, certA14, certA15, certA16, certA17, certA18, certA19, certA20, certA21, certA22, certA23, certA24, certA25, certA26, certA27, certA28, certA29, certA30, certA31, certA32, certA33, certA34, certA35, certA36, certA37, certA38, certA39, certA40, certA41, certA42, certA43]

end Signed
end PEqualNP.Outside.L_meta_29826_aux

theorem PEqualNP.Outside.L_meta_29826 : (¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 3 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 9 ∈ (C.gates.get i).inputs ∧ 9 ≠ 0 ∧ 9 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 9 false = true)) := by
  have reject := PEqualNP.Outside.L_meta_29826_aux.Signed.checkFailed
  rintro ⟨C,i,k,hi,hf,hn,hg,hi0,hu,hop,hkop,hik,hkread,h9,h9ne,h9lt,hw⟩
  obtain ⟨a,ha,b,hb,c,hc,good,suf⟩ := PEqualNP.Outside.L_meta_29826_aux.bridge C i hi hf hn hg hi0 hu hop h9 hw
  have pos := PEqualNP.Outside.L_meta_29826_aux.Signed.sound ha hb hc
    (PEqualNP.Outside.L_meta_29826_aux.goodMask good) suf
  exact Bool.noConfusion (reject.symm.trans pos)
