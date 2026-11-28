import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_49985
open PEqualNP.CircuitLowerBounds
abbrev W := BitVec 5
private def bit (k : Fin 5) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 5) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 5) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#5)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def base : List W := [30,28,24,16,0,31]
def choices (s : List W) : List W :=
  (s.flatMap fun a => (~~~a) :: s.flatMap (fun b => [a &&& b, a ||| b])).eraseDups
def won (s : List W) : Bool := s.contains 4 && s.contains 17 && s.contains 22
def missing (s : List W) := ([4,17,22] : List W).filter (fun x => !(s.contains x))
def scan : Nat → List W → Bool
  | 0, s => won s
  | k+1, s => decide ((missing s).length ≤ k+1) && (scan k s || (choices s).any (fun v => !(s.contains v) && scan k (v::s)))

theorem next_ok {k : Nat} {v : W} {s : List W} (bound : (missing s).length ≤ k+1) (hv : v ∈ choices s) (hn : v ∉ s)
    (h : scan k (v::s) = true) : scan (k+1) s = true := by
  simp only [scan,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq]
  refine ⟨bound, ?_⟩
  right
  exact List.any_eq_true.mpr ⟨v,hv,by simp [hn,h]⟩

theorem ops_mem {s : List W} {a b : W} (ha : a ∈ s) (hb : b ∈ s) :
    (~~~a) ∈ choices s ∧ (a &&& b) ∈ choices s ∧ (a ||| b) ∈ choices s := by
  simp only [choices,List.mem_eraseDups,List.mem_flatMap,List.mem_cons,List.mem_nil_iff,or_false]
  exact ⟨⟨a,ha,Or.inl rfl⟩,⟨a,ha,Or.inr ⟨b,hb,Or.inl rfl⟩⟩,⟨a,ha,Or.inr ⟨b,hb,Or.inr rfl⟩⟩⟩

theorem canRead {s w : List W} (hz : (0 : W) ∈ s) (hw : ∀ a ∈ w, a ∈ s) (i : Nat) :
    w.getD i 0 ∈ s := by
  by_cases h : i < w.length
  · rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h]
    exact hw _ (List.getElem_mem h)
  · simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_none (Nat.le_of_not_gt h)] using hz

theorem action_mem (w s : List W) (g : Gate) (hg : legal g) (hz : (0 : W) ∈ s)
    (ht : (~~~(0 : W)) ∈ s) (hw : ∀ a ∈ w, a ∈ s) : action w g ∈ s ∨ action w g ∈ choices s := by
  have topAnd : ∀ x : W, x &&& 31#5 = x := by decide
  rcases g with ⟨op,args⟩
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp [action,topAnd] <;> first
    | exact Or.inl ht
    | exact Or.inl hz
    | exact Or.inl (canRead hz hw _)
    | exact Or.inr (ops_mem (canRead hz hw _) hz).1
    | exact Or.inr (ops_mem (canRead hz hw _) (canRead hz hw _)).2.1
    | exact Or.inr (ops_mem (canRead hz hw _) (canRead hz hw _)).2.2

def run (gs : List Gate) (w : List W) := gs.foldl (fun l g => l ++ [action l g]) w

theorem simulate (gs : List Gate) (w : List W) (hg : ∀ g ∈ gs, legal g) (t : Fin 5) :
    gs.foldl step (w.map (bit t)) = (run gs w).map (bit t) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons,action_spec w g (hg g (by simp)) t]
    exact ih _ (fun a ha => hg a (by simp [ha]))

theorem run_tail (gs : List Gate) (w : List W) :
    ∃ u, run gs w = w ++ u ∧ u.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[],by simp [run],rfl⟩
  | cons g gs ih =>
    obtain ⟨u,e,sz⟩ := ih (w ++ [action w g])
    refine ⟨action w g :: u,?_,by simp [sz]⟩
    change run gs (w ++ [action w g]) = _
    simpa using e

theorem missing_le (gs : List Gate) (w s : List W)
    (hw : ∀ a ∈ w, a ∈ s) (hwin : ∀ a ∈ ([4,17,22] : List W), a ∈ run gs w) :
    (missing s).length ≤ gs.length := by
  obtain ⟨u,e,sz⟩ := run_tail gs w
  have nd : (missing s).Nodup := (show ([4,17,22] : List W).Nodup by decide).filter _
  have sub : (missing s).toFinset ⊆ u.toFinset := by
    intro a ha
    have h := List.mem_filter.mp (List.mem_toFinset.mp ha)
    have h' := hwin a h.1
    rw [e] at h'
    apply List.mem_toFinset.mpr
    apply (List.mem_append.mp h').resolve_left
    intro ha
    simpa [hw a ha] using h.2
  have h := Finset.card_le_card sub
  rw [List.toFinset_card_of_nodup nd] at h
  exact (h.trans (List.toFinset_card_le _)).trans_eq sz

theorem winning (k : Nat) (gs : List Gate) (w s : List W) (hl : gs.length ≤ k)
    (hg : ∀ g ∈ gs, legal g) (hz : (0 : W) ∈ s) (ht : (~~~(0 : W)) ∈ s)
    (hw : ∀ a ∈ w, a ∈ s) (hwin : ∀ a ∈ ([4,17,22] : List W), a ∈ run gs w) : scan k s = true := by
  induction k generalizing gs w s with
  | zero =>
    have : gs = [] := List.length_eq_zero_iff.mp (by omega)
    subst gs
    change won s = true
    simp only [won,Bool.and_eq_true,List.contains_iff_mem]
    exact ⟨⟨hw _ (hwin _ (by simp)),hw _ (hwin _ (by simp))⟩,hw _ (hwin _ (by simp))⟩
  | succ k ih =>
    have bound := (missing_le gs w s hw hwin).trans hl
    cases gs with
    | nil =>
      simp only [scan,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq]
      exact ⟨bound, .inl (ih [] w s (by simp) hg hz ht hw hwin)⟩
    | cons g gs =>
      let z := action w g
      have hs : gs.length ≤ k := by simpa using hl
      have hgs : ∀ a ∈ gs, legal a := fun a ha => hg a (by simp [ha])
      have htail : ∀ a ∈ ([4,17,22] : List W), a ∈ run gs (w++[z]) := hwin
      by_cases h : z ∈ s
      · simp only [scan,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq]
        refine ⟨bound,?_⟩
        exact .inl (ih gs (w++[z]) s hs hgs hz ht (by
          intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · exact hw a ha
          · simpa only [List.mem_singleton.mp ha] using h) htail)
      · apply next_ok bound ((action_mem _ _ _ (hg g (by simp)) hz ht hw).resolve_left h) h
        apply ih gs (w++[z]) (z::s) hs hgs (List.mem_cons_of_mem _ hz) (List.mem_cons_of_mem _ ht) _ htail
        intro a ha
        rcases List.mem_append.mp ha with h1|h1
        · exact List.mem_cons_of_mem _ (hw a h1)
        · exact List.mem_cons.mpr (.inl (by simpa using h1))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem exhausted : scan 5 base = false := by decide +kernel

theorem eqMask {w : W} {n : Nat} (h : ∀ t : Fin 5, bit t w = n.testBit t.val) :
    w = BitVec.ofNat 5 n := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_ofNat]
  simpa [hj,bit] using h ⟨j,hj⟩

theorem finish (D : Circuit) (p q r : Fin (6+D.size)) (hf : PEqualNP.MetaComplexity.FanInTwo D)
    (hs : D.size ≤ 5) (he : ∀ t : Fin 5,
      let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
      let w := D.wires xs
      w.getD p.val false = (4 : Nat).testBit t.val ∧
      w.getD q.val false = (17 : Nat).testBit t.val ∧
      w.getD r.val false = (22 : Nat).testBit t.val) : False := by
  have hg : ∀ g ∈ D.gates, legal g := fun g h => ⟨(hf g h).1,(hf g h).2⟩
  have sample : ∀ t : Fin 5, base.map (bit t) =
      List.ofFn (fun i : Fin 4 => decide (i.val < t.val)) ++ [false,true] := by decide +kernel
  let l := run D.gates base
  have out (i : Nat) (t : Fin 5) :
      (D.wires (List.ofFn (fun j : Fin 4 => decide (j.val < t.val)) ++ [false,true])).getD i false =
      bit t (l.getD i 0) := by
    rw [← sample t]
    change (D.gates.foldl step _).getD i false = _
    rw [simulate D.gates base hg t,read_bit]
  have a : l.getD p.val 0 = 4 := eqMask (n:=4) (fun t => (out p t).symm.trans (he t).1)
  have b : l.getD q.val 0 = 17 := eqMask (n:=17) (fun t => (out q t).symm.trans (he t).2.1)
  have c : l.getD r.val 0 = 22 := eqMask (n:=22) (fun t => (out r t).symm.trans (he t).2.2)
  have mem (i : Nat) (hn : l.getD i 0 ≠ 0) : l.getD i 0 ∈ l := by
    by_cases hi : i < l.length
    · simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
    · simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (Nat.le_of_not_gt hi)] at hn
  have win := winning 5 D.gates base base hs hg (by decide) (by decide) (fun _ h => h) (by
    intro j hj
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hj
    rcases hj with rfl|rfl|rfl
    · exact a ▸ mem p (by rw [a]; decide)
    · exact b ▸ mem q (by rw [b]; decide)
    · exact c ▸ mem r (by rw [c]; decide))
  exact Bool.noConfusion (exhausted.symm.trans win)
end PEqualNP.Outside.L_meta_49985
theorem PEqualNP.Outside.L_meta_49985 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 5,
    let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (4 : Nat).testBit t.val ∧
    w.getD q.val false = (17 : Nat).testBit t.val ∧
    w.getD r.val false = (22 : Nat).testBit t.val)) := by
  rintro ⟨D,p,q,r,hf,_,_,hs,he⟩
  exact PEqualNP.Outside.L_meta_49985.finish D p q r hf hs he
