import PEqualNP.Defs
import Mathlib.Tactic.IntervalCases

namespace PEqualNP.Outside.L_meta_50810
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def hcsGateVal {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    BitVec rows :=
  let args := g.inputs.map fun i => bank.getD i 0
  match g.op with
  | PEqualNP.CircuitLowerBounds.GateOp.and => args.foldr (· &&& ·) (BitVec.allOnes rows)
  | PEqualNP.CircuitLowerBounds.GateOp.or => args.foldr (· ||| ·) 0
  | PEqualNP.CircuitLowerBounds.GateOp.not => ~~~(args.headD 0)
  | _ => 0
def hcsStep {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    List (BitVec rows) :=
  bank ++ [hcsGateVal bank g]
theorem hcsGetDBit {rows : Nat} (bank : List (BitVec rows)) (i : Nat) (k : Nat) :
    (bank.getD k 0).getLsbD i = (bank.map fun w => w.getLsbD i).getD k false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases bank[k]? <;> simp
theorem hcsAndBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· &&& ·) (BitVec.allOnes rows)).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).all id := by
  induction xs with
  | nil => simp [i.isLt]
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_and, List.map_cons, List.all_cons, id_eq, ih]
theorem hcsOrBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· ||| ·) 0).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).any id := by
  induction xs with
  | nil => simp
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_or, List.map_cons, List.any_cons, id_eq, ih]
theorem hcsGateBit {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp)) :
    (hcsGateVal bank g).getLsbD i.val =
      g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsAndBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsOrBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, BitVec.getLsbD_not, i.isLt,
      decide_true, Bool.true_and]
    cases ins with
    | nil => simp
    | cons k _ => simp only [List.map_cons, List.headD_cons, hcsGetDBit]
theorem hcsFoldBits {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    (gs.foldl hcsStep bank).map (fun w => w.getLsbD i.val) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
        (bank.map fun w => w.getLsbD i.val) := by
  induction gs generalizing bank with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hstep : (hcsStep bank g).map (fun w => w.getLsbD i.val) =
        (bank.map fun w => w.getLsbD i.val) ++
          [g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false)] := by
      simp only [hcsStep, List.map_append, List.map_cons, List.map_nil,
        hcsGateBit bank i g (hfan g List.mem_cons_self).1]
    rw [ih (hcsStep bank g) (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')), hstep]

private def initial : List (BitVec 6) := [62,60,56,48,32,0,63]

private def inv (g : Gate) : Bool := match g.op with | .not => true | _ => false

private def possible (b : List (BitVec 6)) (n : Bool) (v : BitVec 6) : Prop :=
  ∃ x y, x ∈ b ∧ y ∈ b ∧ (v = x &&& y ∨ v = x ||| y ∨ (n = true ∧ v = ~~~x))

private theorem getMem (b : List (BitVec 6)) (hz : 0 ∈ b) (i : Nat) : b.getD i 0 ∈ b := by
  by_cases h : i < b.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  · simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)] using hz

private theorem stepPossible (b : List (BitVec 6)) (hz : 0 ∈ b) (hm : 63 ∈ b)
    (g : Gate) (hf : FanInTwo ⟨[g],0⟩) : possible b (inv g) (hcsGateVal b g) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop,hlen⟩ := hf ⟨op,ins⟩ (by simp)
  change ins.length ≤ 2 at hlen
  change op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) at hop
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  all_goals cases ins with
  | nil => first
            | exact ⟨63,63,hm,hm,Or.inl rfl⟩
            | exact ⟨0,0,hz,hz,Or.inl rfl⟩
            | exact ⟨0,0,hz,hz,Or.inr (Or.inr ⟨rfl,rfl⟩)⟩
  | cons a tail =>
    cases tail with
    | nil => first
              | exact ⟨b.getD a 0,63,getMem _ hz _,hm,Or.inl rfl⟩
              | exact ⟨b.getD a 0,0,getMem _ hz _,hz,Or.inr (Or.inl rfl)⟩
              | exact ⟨b.getD a 0,0,getMem _ hz _,hz,Or.inr (Or.inr ⟨rfl,rfl⟩)⟩
    | cons c tail =>
      cases tail with
      | nil =>
        refine ⟨b.getD a 0,b.getD c 0,getMem _ hz _,getMem _ hz _,?_⟩
        simp [inv,hcsGateVal]
        all_goals
          left
          have neutral : ∀ w : BitVec 6, w &&& 63#6 = w := by decide
          rw [neutral]
      | cons d ds => simp at hlen

private def path (targets : List (BitVec 6)) : Nat → Nat → List (BitVec 6) → Prop
  | 0, _, b => ∀ v ∈ targets, v ∈ b
  | k+1, cash, b => ∃ v n, possible b n v ∧ (n = true → cash ≠ 0) ∧
      path targets k (if n then cash - 1 else cash) (b ++ [v])

private theorem sound (ts : List (BitVec 6)) (k : Nat) (gs : List Gate) (b : List (BitVec 6))
    (c : Nat) (hc : c ≤ 2) (hz : 0 ∈ b) (hm : 63 ∈ b) (hl : gs.length ≤ k)
    (hf : FanInTwo ⟨gs,0⟩) (hn : (gs.filter inv).length ≤ c)
    (done_ : ∀ v ∈ ts, v ∈ gs.foldl hcsStep b) : path ts k c b := by
  induction k generalizing gs b c with
  | zero =>
    have emp : gs = [] := List.length_eq_zero_iff.mp (by omega)
    simpa [path, emp] using done_
  | succ k ih =>
    cases gs with
    | nil =>
      refine ⟨0,false,⟨0,0,hz,hz,Or.inl rfl⟩,by simp,?_⟩
      exact ih [] _ c hc (List.mem_append_left _ hz) (List.mem_append_left _ hm) (by simp) (by simp [FanInTwo]) (by simp)
        (fun v hv => List.mem_append_left _ (done_ v hv))
    | cons g gs =>
      let v := hcsGateVal b g
      have hg : FanInTwo ⟨[g],0⟩ := by
        intro h mem; simp only [List.mem_singleton] at mem; subst h; exact hf _ (by simp)
      have ht : FanInTwo ⟨gs,0⟩ := fun h mem => hf h (List.mem_cons_of_mem _ mem)
      refine ⟨v,inv g,stepPossible _ hz hm g hg,?_,?_⟩
      · intro yes
        simp [yes] at hn
        omega
      · cases eq : inv g <;> simp [eq] at hn ⊢
        · exact ih gs _ c hc (List.mem_append_left _ hz) (List.mem_append_left _ hm) (by simpa using hl) ht hn done_
        · exact ih gs _ (c-1) (by omega) (List.mem_append_left _ hz) (List.mem_append_left _ hm) (by simpa using hl) ht (by omega) done_

private theorem tap {D : Circuit} (hf : FanInTwo D) (p : Nat) (a : Nat)
    (out : ∀ t : Fin 6, (D.wires ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true])).getD p false = a.testBit t.val) :
    BitVec.ofNat 6 a ∈ D.gates.foldl hcsStep initial := by
  let final_ := D.gates.foldl hcsStep initial
  have eq : final_.getD p 0 = BitVec.ofNat 6 a := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    let t : Fin 6 := ⟨i,hi⟩
    have input : ∀ t : Fin 6, initial.map (fun w => w.getLsbD t.val) =
        (List.ofFn (fun j : Fin 5 => decide (j.val < t.val))) ++ [false,true] := by decide
    rw [hcsGetDBit]
    change ((D.gates.foldl hcsStep initial).map _).getD p false = _
    rw [hcsFoldBits initial t D.gates hf,input t,BitVec.getLsbD_ofNat]
    simp only [decide_eq_true hi, Bool.true_and]
    simpa only [Circuit.wires,t] using out ⟨i,hi⟩
  rw [← eq]
  apply getMem
  have keep (gs : List Gate) (b : List (BitVec 6)) (hz : 0 ∈ b) : 0 ∈ gs.foldl hcsStep b := by
    induction gs generalizing b with
    | nil => exact hz
    | cons g gs ih => exact ih _ (List.mem_append_left _ hz)
  exact keep _ _ (by decide)


private def missing (ts b : List (BitVec 6)) : Nat := (ts.toFinset \ b.toFinset).card

private theorem missed {ts b b' : List (BitVec 6)} {cash k} (h : path ts k cash b) (sub : b ⊆ b') : missing ts b' ≤ k := by
  induction k generalizing cash b b' with
  | zero =>
    have ss : ts.toFinset ⊆ b'.toFinset := fun v hv => List.mem_toFinset.mpr (sub (h v (List.mem_toFinset.mp hv)))
    simp [missing, Finset.sdiff_eq_empty_iff_subset.mpr ss]
  | succ k ih =>
    obtain ⟨v,n,_,_,tail⟩ := h
    have ht := ih tail (b' := v::b') (by intro w hw; simp at hw ⊢; exact hw.elim (fun mem => Or.inr (sub mem)) Or.inl)
    have cover : ts.toFinset \ b'.toFinset ⊆ insert v (ts.toFinset \ (v::b').toFinset) := by
      intro w hw; simp at hw ⊢; by_cases eq : w = v <;> simp [eq,hw]
    exact (Finset.card_le_card cover).trans ((Finset.card_insert_le ..).trans (Nat.succ_le_succ ht))

private def bins (b : List (BitVec 6)) := (b.flatMap (fun x => b.flatMap (fun y => [x &&& y,x ||| y]))).eraseDups

private def search_ (ts : List (BitVec 6)) : Nat → Nat → List (BitVec 6) → Bool
  | 0, _, b => ts.all (fun v => b.contains v)
  | k+1, cash, b => decide (missing ts b ≤ k+1) && (search_ ts k cash b ||
      (bins b).any (fun v => !b.contains v && search_ ts k cash (v::b)) ||
      (decide (0 < cash) && b.any (fun x => !b.contains (~~~x) && search_ ts k (cash-1) ((~~~x)::b))))

private theorem searchSound {ts b b' : List (BitVec 6)} {k c c'} (h : path ts k c b)
    (sub : b ⊆ b') (budget : c ≤ c') : search_ ts k c' b' = true := by
  induction k generalizing c c' b b' with
  | zero => exact List.all_eq_true.mpr (fun v hv => List.contains_iff_mem.mpr (sub (h v hv)))
  | succ k ih =>
    have bound := missed h sub
    obtain ⟨v,n,⟨x,y,hx,hy,op⟩,lim,tail⟩ := h
    simp only [search_, decide_eq_true bound, Bool.true_and,Bool.or_eq_true,Bool.and_eq_true,List.any_eq_true]
    have cost : (if n then c-1 else c) ≤ c' := by cases n <;> simp <;> omega
    by_cases hv : v ∈ b'
    · left; left; apply ih tail _ cost
      intro w hw; simp at hw; exact hw.elim (fun z => sub z) (fun e => e ▸ hv)
    have next : b ++ [v] ⊆ v::b' := by
      intro w hw; simp at hw ⊢; exact hw.elim (fun z => Or.inr (sub z)) Or.inl
    have bn (hv' : v = x &&& y ∨ v = x ||| y) : v ∈ bins b' := by
      apply List.mem_eraseDups.mpr; apply List.mem_flatMap.mpr
      refine ⟨x,sub hx,List.mem_flatMap.mpr ⟨y,sub hy,?_⟩⟩
      simpa using hv'
    rcases op with eq | eq | ⟨yes,eq⟩
    · left; right; exact ⟨v,bn (Or.inl eq),by simpa using hv,ih tail next cost⟩
    · left; right; exact ⟨v,bn (Or.inr eq),by simpa using hv,ih tail next cost⟩
    · right; subst n; subst v
      exact ⟨by simp; have := lim rfl; omega, x,sub hx,by simpa using hv,ih tail next (by simpa using Nat.sub_le_sub_right budget 1)⟩

set_option maxHeartbeats 2400000 in
set_option maxRecDepth 16000 in
private theorem exclude : ¬ path [20,28,54] 5 2 initial := by
  intro h
  have no : search_ [20,28,54] 5 2 initial = false := by decide +kernel
  have yes := searchSound h (List.Subset.refl _) (Nat.le_refl _)
  rw [no] at yes; contradiction

end PEqualNP.Outside.L_meta_50810

open PEqualNP.Outside.L_meta_50810 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_50810 : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (20 : Nat).testBit t.val ∧
    w.getD q.val false = (28 : Nat).testBit t.val ∧
    w.getD r.val false = (54 : Nat).testBit t.val) := by
  rintro ⟨D,p,q,r,hf,_,hn,hl,outs⟩
  apply exclude
  apply sound _ _ D.gates initial 2 (by decide) (by decide) (by decide) hl hf
  · have ident : (D.gates.filter inv) = (D.gates.filter fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq _ _)) := by
      apply List.filter_congr; intro g _; cases g with | mk op ins => cases op <;> rfl
    rw [ident]; exact hn
  · intro v hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact tap hf p.val 20 (fun t => (outs t).1)
    · exact tap hf q.val 28 (fun t => (outs t).2.1)
    · exact tap hf r.val 54 (fun t => (outs t).2.2)
