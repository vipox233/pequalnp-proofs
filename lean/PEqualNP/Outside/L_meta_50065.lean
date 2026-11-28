import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket
namespace PEqualNP.Outside.L_meta_50065_aux
open PEqualNP.CircuitLowerBounds
abbrev W := BitVec 5
def raw : List W := [30,28,24,16,0,31]
def rows (t : Fin 5) := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
theorem rawRows : ∀ t : Fin 5, raw.map (fun w => w.getLsbD t.val) = rows t := by decide
def val (w : List W) (g : Gate) : W :=
  let a := w.getD (g.inputs.getD 0 0) 0
  let b := w.getD (g.inputs.getD 1 0) 0
  match g.op, g.inputs with
  | .and, [] => 31
  | .or, [] => 0
  | .not, [] => 31
  | .not, _::_ => ~~~a
  | .and, [_] | .or, [_] => a
  | .and, _::_::_ => a &&& b
  | .or, _::_::_ => a ||| b
  | _, _ => 0
def run (gs : List Gate) (w : List W) := gs.foldl (fun w g => w ++ [val w g]) w
def fee (gs : List Gate) := PEqualNP.NotBracket.notCount ⟨gs,0⟩
def OK (g : Gate) := (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2
theorem rowGet (w : List W) (t : Fin 5) (i : Nat) :
    (w.map (fun a => a.getLsbD t.val)).getD i false = (w.getD i 0).getLsbD t.val := by
  induction w generalizing i with
  | nil => simp
  | cons a l ih => cases i with
    | zero => rfl
    | succ i => exact ih i
theorem valRow (w : List W) (g : Gate) (h : OK g) (t : Fin 5) :
    (val w g).getLsbD t.val = g.op.eval (g.inputs.map fun i => (w.getD i 0).getLsbD t.val) := by
  obtain ⟨op,ins⟩ := g
  rcases h with ⟨h,len⟩
  change op = .and ∨ op = .or ∨ op = .not at h
  change ins.length ≤ 2 at len
  have full : (31 : W).getLsbD t.val = true := by fin_cases t <;> decide
  rcases h with rfl | rfl | rfl <;>
    match ins,len with
    | [], _ => first | exact full | simp [val,GateOp.eval]
    | [i], _ => simp [val,GateOp.eval,t.isLt]
    | [i,j], _ => simp [val,GateOp.eval,t.isLt]
theorem replay (gs : List Gate) (w : List W) (h : ∀ g ∈ gs, OK g) (t : Fin 5) :
    (run gs w).map (fun a => a.getLsbD t.val) =
      gs.foldl (fun b g => b ++ [g.op.eval (g.inputs.map fun i => b.getD i false)]) (w.map (fun a => a.getLsbD t.val)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (w ++ [val w g])).map _ = _
    rw [ih _ (fun a ha => h a (List.mem_cons_of_mem _ ha))]
    simp only [List.foldl_cons,List.map_append,List.map_cons,List.map_nil,valRow w g (h g List.mem_cons_self),rowGet]
def bins (s : List W) : List W :=
  (s.flatMap fun a => s.flatMap fun b => [a &&& b,a ||| b]).eraseDups
def invs (s : List W) : List W := s.map fun a => ~~~a
def fresh (xs s : List W) := xs.filter fun x => !(s.contains x)
def missing (T s : List W) := (T.filter fun x => !(s.contains x)).length
theorem extension (gs : List Gate) (w : List W) :
    ∃ extra, run gs w = w ++ extra ∧ extra.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[],by simp [run]⟩
  | cons g gs ih =>
    obtain ⟨xs,eqn,len⟩ := ih (w ++ [val w g])
    exact ⟨val w g :: xs,by simpa [run,List.foldl_cons,List.append_assoc] using eqn,by simp [len]⟩
theorem remaining (T s w : List W) (gs : List Gate) (hd : T.Nodup)
    (hw : ∀ x ∈ w, x ∈ s) (hit : ∀ x ∈ T, x ∈ run gs w) : missing T s ≤ gs.length := by
  obtain ⟨extra,eqn,len⟩ := extension gs w
  let m := T.filter fun x => !(s.contains x)
  have sub : m.toFinset ⊆ extra.toFinset := by
    intro x hx
    obtain ⟨inT,absent⟩ := List.mem_filter.mp (List.mem_toFinset.mp hx : x ∈ m)
    have he := hit x inT
    rw [eqn] at he
    rcases List.mem_append.mp he with old | fresh
    · simp [hw x old] at absent
    · exact List.mem_toFinset.mpr fresh
  have le := Finset.card_le_card sub
  rw [List.toFinset_card_of_nodup (l := m) (hd.filter _)] at le
  exact le.trans (len ▸ List.toFinset_card_le (l := extra))
def walk (T : List W) : Nat → Nat → List W → Bool
  | 0, _, s => T.all fun a => s.contains a
  | k+1, n, s =>
    if missing T s ≤ k+1 then
      walk T k n s || (fresh (bins s) s).any (fun z => walk T k n (z::s)) ||
    (decide (0 < n) && (fresh (invs s) s).any (fun z => walk T k (n-1) (z::s)))
    else false
theorem mem_get (w : List W) (s : List W) (hw : ∀ a ∈ w, a ∈ s) (hz : (0 : W) ∈ s) (i : Nat) : w.getD i 0 ∈ s := by
  induction w generalizing i with
  | nil => simpa using hz
  | cons a w ih => cases i with
    | zero => exact hw a List.mem_cons_self
    | succ i => exact ih (fun b hb => hw b (List.mem_cons_of_mem _ hb)) i
theorem possible (w s : List W) (hw : ∀ a ∈ w, a ∈ s) (hz : (0 : W) ∈ s) (ho : (31 : W) ∈ s) (g : Gate) (hg : OK g) :
    val w g ∈ s ∨ val w g ∈ bins s ∨ (g.op = .not ∧ val w g ∈ invs s) := by
  have hb (a b : W) (ha : a ∈ s) (hh : b ∈ s) : (a &&& b) ∈ bins s ∧ (a ||| b) ∈ bins s := by
    constructor <;> simp only [bins,List.mem_eraseDups,List.mem_flatMap] <;>
      exact ⟨a,ha,b,hh,by simp⟩
  have hn (a : W) (h : a ∈ s) : (~~~a) ∈ invs s := List.mem_map.mpr ⟨a,h,rfl⟩
  obtain ⟨op,ins⟩ := g
  rcases hg with ⟨h,len⟩
  change op = .and ∨ op = .or ∨ op = .not at h
  change ins.length ≤ 2 at len
  rcases h with rfl | rfl | rfl <;>
    match ins,len with
    | [], _ => first | exact Or.inl hz | exact Or.inl ho
    | [i], _ => first | exact Or.inl (mem_get w s hw hz i) | exact Or.inr (Or.inr ⟨rfl,hn _ (mem_get w s hw hz i)⟩)
    | [i,j], _ => first
      | exact Or.inr (Or.inl (hb _ _ (mem_get w s hw hz i) (mem_get w s hw hz j)).1)
      | exact Or.inr (Or.inl (hb _ _ (mem_get w s hw hz i) (mem_get w s hw hz j)).2)
      | exact Or.inr (Or.inr ⟨rfl,hn _ (mem_get w s hw hz i)⟩)
theorem sound (T : List W) (hd : T.Nodup) (k n : Nat) (s w : List W) (gs : List Gate)
    (hw : ∀ a ∈ w, a ∈ s) (hz : (0 : W) ∈ s) (ho : (31 : W) ∈ s)
    (hg : ∀ g ∈ gs, OK g) (hl : gs.length ≤ k) (hn : fee gs ≤ n)
    (hit : ∀ a ∈ T, a ∈ run gs w) : walk T k n s = true := by
  induction k generalizing n s w gs with
  | zero =>
    have e : gs = [] := List.length_eq_zero_iff.mp (by omega)
    subst gs
    exact List.all_eq_true.mpr (fun a ha => List.contains_iff_mem.mpr (hw a (hit a ha)))
  | succ k ih =>
    have enough : missing T s ≤ k+1 := (remaining T s w gs hd hw hit).trans hl
    simp only [walk,if_pos enough,Bool.or_eq_true,Bool.and_eq_true,List.any_eq_true,decide_eq_true_eq]
    cases gs with
    | nil =>
      exact Or.inl (Or.inl (ih n s w [] hw hz ho hg (by simp) hn hit))
    | cons g gs =>
      let v := val w g
      have tailOK := fun a ha => hg a (List.mem_cons_of_mem g ha)
      have lk : gs.length ≤ k := by simpa using hl
      have lf : fee gs ≤ n := by
        letI : DecidableEq GateOp := lineDegreeGateOpDecEq
        change ((g::gs).filter (fun x : Gate => decide (x.op = .not))).length ≤ n at hn
        change (gs.filter (fun x : Gate => decide (x.op = .not))).length ≤ n
        rw [List.filter_cons] at hn
        split at hn <;> simp_all <;> omega
      have hits : ∀ a ∈ T, a ∈ run gs (w ++ [v]) := hit
      by_cases held : v ∈ s
      · apply Or.inl ∘ Or.inl
        apply ih n s (w ++ [v]) gs _ hz ho tailOK lk lf hits
        intro a ha
        rcases List.mem_append.mp ha with h | h
        · exact hw a h
        · simpa only [List.mem_singleton.mp h] using held
      have inc : ∀ a ∈ w ++ [v], a ∈ v::s := by
        intro a ha
        rcases List.mem_append.mp ha with h | h
        · exact List.mem_cons_of_mem _ (hw a h)
        · exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp h))
      have good (xs : List W) (hm : v ∈ xs) : v ∈ fresh xs s := by simp [fresh,hm,held]
      rcases possible w s hw hz ho g (hg g List.mem_cons_self) with h | h | ⟨neg,h⟩
      · exact (held h).elim
      · exact Or.inl (Or.inr ⟨v,good _ h,ih n (v::s) (w++[v]) gs inc (List.mem_cons_of_mem _ hz) (List.mem_cons_of_mem _ ho) tailOK lk lf hits⟩)
      · have paid : fee gs + 1 ≤ n := by simpa [fee,PEqualNP.NotBracket.notCount,List.filter_cons,neg] using hn
        exact Or.inr ⟨by omega,v,good _ h,ih (n-1) (v::s) (w++[v]) gs inc (List.mem_cons_of_mem _ hz) (List.mem_cons_of_mem _ ho) tailOK lk (by omega) hits⟩

def targets : List W := [5, 6, 21]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem exhausted : walk targets 5 2 raw = false := by decide +kernel
end PEqualNP.Outside.L_meta_50065_aux
open PEqualNP.Outside.L_meta_50065_aux in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_50065 : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 5,
    let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (5 : Nat).testBit t.val ∧
    w.getD q.val false = (6 : Nat).testBit t.val ∧
    w.getD r.val false = (21 : Nat).testBit t.val) := by
  rintro ⟨D,p,q,r,fit,_,notLim,sizeLim,reported⟩
  have legal : ∀ g ∈ D.gates, OK g := by
    intro g hg
    simpa only [OK,Set.mem_insert_iff,Set.mem_singleton_iff] using fit g hg
  let w := run D.gates raw
  have wire (i : Nat) (t : Fin 5) : (w.getD i 0).getLsbD t.val = (D.wires (rows t)).getD i false := by
    rw [← rowGet, replay D.gates raw legal t,rawRows]
    rfl
  have atMask (i j : Nat) (h : ∀ t : Fin 5, (D.wires (rows t)).getD i false = j.testBit t.val) :
      w.getD i 0 = BitVec.ofNat 5 j := by
    apply BitVec.eq_of_getLsbD_eq
    intro t ht
    rw [wire i ⟨t,ht⟩,h ⟨t,ht⟩]
    change j.testBit t = (BitVec.ofNat 5 j).getLsbD t
    rw [BitVec.getLsbD_ofNat]
    simp [ht]
  have w0 : w.getD p.val 0 = (5 : W) := atMask _ 5 (fun t => (reported t).1)
  have w1 : w.getD q.val 0 = (6 : W) := atMask _ 6 (fun t => (reported t).2.1)
  have w2 : w.getD r.val 0 = (21 : W) := atMask _ 21 (fun t => (reported t).2.2)
  have hz : (0 : W) ∈ w := by
    have aux (gs : List PEqualNP.CircuitLowerBounds.Gate) (l : List W) (h : (0 : W) ∈ l) : (0 : W) ∈ run gs l := by
      induction gs generalizing l with
      | nil => exact h
      | cons a b ih => exact ih _ (List.mem_append_left _ h)
    exact aux _ _ (by decide : (0 : W) ∈ raw)
  have hits : ∀ a ∈ targets, a ∈ w := by
    intro a ha
    simp only [targets,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl
    · rw [← w0]
      exact mem_get w w (fun _ h => h) hz p.val
    · rw [← w1]
      exact mem_get w w (fun _ h => h) hz q.val
    · rw [← w2]
      exact mem_get w w (fun _ h => h) hz r.val
  have result := sound targets (by decide) 5 2 raw raw D.gates (fun _ h => h) (by decide) (by decide) legal sizeLim notLim hits
  exact Bool.noConfusion (exhausted.symm.trans result)
