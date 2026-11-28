import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_51084_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

abbrev Mask := BitVec 6

def roots : List Mask := [62, 60, 56, 48, 32, 0, 63]

def binary (w : List Mask) : List Mask :=
  (w.flatMap fun a => w.flatMap fun b => [a &&& b, a ||| b]).eraseDups

def moves (w : List Mask) : List (Mask × Nat) :=
  (binary w).map (fun a => (a,0)) ++ w.map (fun a => (~~~a,1))

lemma binary_mem (a b : Mask) (w : List Mask) (ha : a ∈ w) (hb : b ∈ w) :
    (a &&& b,0) ∈ moves w ∧ (a ||| b,0) ∈ moves w := by
  have one (v : Mask) (hv : v ∈ [a &&& b, a ||| b]) : (v,0) ∈ moves w := by
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨v,?_,rfl⟩
    unfold binary
    apply List.mem_eraseDups.mpr
    exact List.mem_flatMap.mpr ⟨a,ha,List.mem_flatMap.mpr ⟨b,hb,hv⟩⟩
  exact ⟨one _ (by simp),one _ (by simp)⟩

lemma inv_mem {a : Mask} {w : List Mask} (ha : a ∈ w) : (~~~a,1) ∈ moves w :=
  List.mem_append_right _ (List.mem_map.mpr ⟨a,ha,rfl⟩)

inductive Path : List Mask → List Mask → Nat → Nat → Prop
  | done {w} : Path [] w 0 0
  | next {need w v q d i} : (v,q) ∈ moves w → v ∉ w →
      Path (need.erase v) (v::w) d i → Path need w (d+1) (q+i)

lemma path_length {need w d i} (h : Path need w d i) : need.length ≤ d := by
  induction h with
  | done => simp
  | @next need w v q d i _ _ _ ih =>
    by_cases hx : v ∈ need
    · rw [List.length_erase_of_mem hx] at ih
      omega
    · rw [List.erase_of_not_mem hx] at ih
      omega

def scan : Nat → Nat → List Mask → List Mask → Bool
  | 0, _, _, need => need.isEmpty
  | k+1, n, w, need => need.isEmpty || (decide (need.length ≤ k+1) &&
      (moves w).any (fun z => !(w.contains z.1) && decide (z.2 ≤ n) &&
        scan k (n-z.2) (z.1::w) (need.erase z.1)))

lemma scan_complete {need w d i} (h : Path need w d i) (k n : Nat) (hd : d ≤ k) (hi : i ≤ n) :
    scan k n w need = true := by
  induction h generalizing k n with
  | done => cases k <;> simp [scan]
  | @next need w v q d i hm hn hp ih =>
    cases k with
    | zero => omega
    | succ k =>
      apply Bool.or_eq_true_iff.mpr
      right
      apply Bool.and_eq_true_iff.mpr
      refine ⟨decide_eq_true ((path_length (Path.next hm hn hp)).trans hd),?_⟩
      apply List.any_eq_true.mpr
      refine ⟨(v,q),hm,?_⟩
      have hn' : q ≤ n := by omega
      simpa [hn,hn'] using ih k (n-q) (by omega) (by omega)

def val (w : List Mask) (g : Gate) : Mask :=
  match g.op, g.inputs with
  | .and, [] => 63
  | .or, [] => 0
  | .not, [] => 63
  | .not, a :: _ => ~~~(w.getD a 0)
  | .and, [a] | .or, [a] => w.getD a 0
  | .and, a::b::_ => w.getD a 0 &&& w.getD b 0
  | .or, a::b::_ => w.getD a 0 ||| w.getD b 0
  | _, _ => 0

def run : List Gate → List Mask → List Mask
  | [], w => w
  | g::gs, w => run gs (w ++ [val w g])

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def price (g : Gate) : Nat := match g.op with | .not => 1 | _ => 0

def negs (gs : List Gate) : Nat := notCount ⟨gs,0⟩

lemma negs_cons (g : Gate) (gs : List Gate) : negs (g::gs) = price g + negs gs := by
  obtain ⟨op,l⟩ := g
  cases op <;> simp [negs,notCount,price,Nat.add_comm]

lemma get_mem {w bank : List Mask} (hz : (0 : Mask) ∈ bank) (hw : ∀ x ∈ w, x ∈ bank) (j : Nat) :
    w.getD j 0 ∈ bank := by
  by_cases hj : j < w.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact hw _ (List.getElem_mem hj)
  · rwa [List.getD_eq_default _ _ (by omega)]

lemma new_value {w bank : List Mask} (hz : (0 : Mask) ∈ bank) (hu : (63 : Mask) ∈ bank)
    (hw : ∀ x ∈ w, x ∈ bank) (g : Gate) (hg : legal g) (fresh : val w g ∉ bank) :
    (val w g,price g) ∈ moves bank := by
  have rd := get_mem hz hw
  obtain ⟨op,l⟩ := g
  rcases hg.1 with h | h | h <;> change op = _ at h <;> subst op
  · match l with
    | [] => exact (fresh hu).elim
    | [a] => exact (fresh (rd a)).elim
    | a::b::_ => exact (binary_mem _ _ _ (rd a) (rd b)).1
  · match l with
    | [] => exact (fresh hz).elim
    | [a] => exact (fresh (rd a)).elim
    | a::b::_ => exact (binary_mem _ _ _ (rd a) (rd b)).2
  · match l with
    | [] => exact (fresh hu).elim
    | a::_ => exact inv_mem (rd a)

lemma build (gs : List Gate) (w bank need : List Mask)
    (hz : (0 : Mask) ∈ bank) (hu : (63 : Mask) ∈ bank) (hw : ∀ x ∈ w, x ∈ bank)
    (hg : ∀ g ∈ gs, legal g) (nd : need.Nodup) (unseen : ∀ x ∈ need, x ∉ bank)
    (covering : ∀ x ∈ need, x ∈ run gs w) :
    ∃ d i, d ≤ gs.length ∧ i ≤ negs gs ∧ Path need bank d i := by
  induction gs generalizing w bank need with
  | nil =>
    have hnil : need = [] := by
      cases need with
      | nil => rfl
      | cons a rest => exact (unseen a (by simp) (hw a (covering a (by simp)))).elim
    subst need
    exact ⟨0,0,by simp,Nat.zero_le _,Path.done⟩
  | cons g gs ih =>
    let v := val w g
    have ht (e) (he : e ∈ gs) := hg e (List.mem_cons_of_mem _ he)
    change ∀ x ∈ need, x ∈ run gs (w ++ [v]) at covering
    by_cases old : v ∈ bank
    · have all : ∀ x ∈ w ++ [v], x ∈ bank := by
        intro x hx
        rcases List.mem_append.mp hx with h|h
        · exact hw x h
        · exact (List.mem_singleton.mp h) ▸ old
      obtain ⟨d,i,hd,hi,hp⟩ := ih (w++[v]) bank need hz hu all ht nd unseen covering
      exact ⟨d,i,by simp; omega,by rw [negs_cons]; omega,hp⟩
    · have all : ∀ x ∈ w ++ [v], x ∈ v::bank := by
        intro x h
        rcases List.mem_append.mp h with hx|hx
        · exact List.mem_cons_of_mem _ (hw _ hx)
        · exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hx))
      have new_unseen (x) (hx : x ∈ need.erase v) : x ∉ v::bank := by
        rcases eq_or_ne x v with rfl | h
        · exact (nd.not_mem_erase hx).elim
        · exact fun e => unseen _ (List.mem_of_mem_erase hx) ((List.mem_cons.mp e).resolve_left h)
      obtain ⟨d,i,hd,hi,hp⟩ := ih (w++[v]) (v::bank) (need.erase v)
        (List.mem_cons_of_mem _ hz) (List.mem_cons_of_mem _ hu) all ht (nd.erase _) new_unseen
        (fun x hx => covering _ (List.mem_of_mem_erase hx))
      exact ⟨d+1,price g+i,by simp; omega,by rw [negs_cons]; omega,
        Path.next (new_value hz hu hw g (hg _ List.mem_cons_self) old) old hp⟩

def bit (t : Fin 6) (a : Mask) := a.getLsbD t.val

lemma read_bit (t : Fin 6) (w : List Mask) (i : Nat) :
    (w.map (bit t)).getD i false = bit t (w.getD i 0) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[i]? <;> simp [bit]

lemma bit_zero (t : Fin 6) : bit t 0 = false := by simp [bit]
lemma bit_full : ∀ t : Fin 6, bit t 63 = true := by decide +kernel
lemma bit_inv (t : Fin 6) (x : Mask) : bit t (~~~x) = !(bit t x) := by simp [bit,t.isLt]
lemma bit_and (t : Fin 6) (x y : Mask) : bit t (x &&& y) = (bit t x && bit t y) := by simp [bit]
lemma bit_or (t : Fin 6) (x y : Mask) : bit t (x ||| y) = (bit t x || bit t y) := by simp [bit]

lemma val_bit (t : Fin 6) (w : List Mask) (g : Gate) (hg : legal g) :
    bit t (val w g) = g.op.eval (g.inputs.map fun i => (w.map (bit t)).getD i false) := by
  obtain ⟨op,l⟩ := g
  have len : l.length ≤ 2 := hg.2
  simp only [read_bit]
  rcases hg.1 with h|h|h <;> change op = _ at h <;> subst op <;>
    (match l with
    | [] => first | exact bit_full t | exact bit_zero t
    | [a] => simp [val,GateOp.eval,bit_inv]
    | [a,b] => simp [val,GateOp.eval,bit_and,bit_or,bit_inv]
    | a::b::c::r => simp at len)

lemma eval_run (t : Fin 6) (gs : List Gate) (w : List Mask) (hg : ∀ g ∈ gs, legal g) :
    (run gs w).map (bit t) =
    gs.foldl (fun (s : List Bool) (g : Gate) =>
        s ++ [g.op.eval (g.inputs.map fun i => s.getD i false)]) (w.map (bit t)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [run, List.foldl_cons, ih (w ++ [val w g]) (fun x hx => hg x (List.mem_cons_of_mem _ hx))]
    rw [List.map_append]
    simp only [List.map_singleton,val_bit t w g (hg g List.mem_cons_self)]

def row (t : Fin 6) : List Bool := (List.ofFn fun i : Fin 5 => decide (i.val < t.val)) ++ [false,true]

lemma roots_row : ∀ t : Fin 6, roots.map (bit t) = row t := by decide +kernel

lemma output_mem (D : Circuit) (fit : FanInTwo D) (p : Nat) (a : Mask)
    (h : ∀ t : Fin 6, (D.wires (row t)).getD p false = bit t a) : a ∈ run D.gates roots := by
  have ok (g) (hg : g ∈ D.gates) : legal g := by
    exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (fit g hg).1,(fit g hg).2⟩
  have eq : (run D.gates roots).getD p 0 = a := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    let t : Fin 6 := ⟨i,hi⟩
    change bit t ((run D.gates roots).getD p 0) = bit t a
    rw [← read_bit,eval_run t D.gates roots ok, roots_row]
    exact h t
  have rz : (0 : Mask) ∈ run D.gates roots := by
    have keep (gs : List Gate) (w : List Mask) (hw : (0 : Mask) ∈ w) : (0 : Mask) ∈ run gs w := by
      induction gs generalizing w with
      | nil => exact hw
      | cons g gs ih => exact ih _ (List.mem_append_left _ hw)
    exact keep _ _ (by decide)
  rw [← eq]
  exact get_mem rz (fun _ h => h) p

lemma exclude (k : Nat) (goals : List Mask) (unique : goals.Nodup)
    (fresh : ∀ x ∈ goals, x ∉ roots) (test : scan k 2 roots goals = false)
    (D : Circuit) (fan : FanInTwo D) (nb : notCount D ≤ 2) (sz : D.size ≤ k)
    (hits : ∀ a ∈ goals, a ∈ run D.gates roots) : False := by
  obtain ⟨d,i,hd,hi,h⟩ := build D.gates roots roots goals (by decide) (by decide)
    (fun _ h => h) (fun g hg => ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using (fan g hg).1,(fan g hg).2⟩)
    unique fresh hits
  have yes := scan_complete h k 2 (hd.trans sz) (hi.trans nb)
  rw [test] at yes
  contradiction


set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem exhausted : scan 5 2 roots [8,45,61] = false := by decide +kernel

end PEqualNP.Outside.L_meta_51084_aux

open PEqualNP.Outside.L_meta_51084_aux in
theorem PEqualNP.Outside.L_meta_51084 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (8 : Nat).testBit t.val ∧
    w.getD q.val false = (45 : Nat).testBit t.val ∧
    w.getD r.val false = (61 : Nat).testBit t.val)) := by
  rintro ⟨D,z0,z1,z2,fan,_,nb,sz,h⟩
  have hout0 : (8 : Mask) ∈ run D.gates roots :=
    output_mem D fan z0.val 8 (fun t => (h t).1)
  have hout1 : (45 : Mask) ∈ run D.gates roots :=
    output_mem D fan z1.val 45 (fun t => (h t).2.1)
  have hout2 : (61 : Mask) ∈ run D.gates roots :=
    output_mem D fan z2.val 61 (fun t => (h t).2.2)
  exact exclude 5 [8,45,61] (by decide) (by decide) exhausted D fan nb sz (by intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; rcases hx with rfl | rfl | rfl <;> assumption)
