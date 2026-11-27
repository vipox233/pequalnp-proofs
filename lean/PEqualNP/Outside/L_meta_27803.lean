import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27803_aux

namespace Meta27803Delete
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def readRef (w : List Bool) : Option Nat → Bool
  | none => false
  | some i => w.getD i false

private def reduce : GateOp → List (Option Nat) → Sum (Option Nat) Gate
  | .and, [] => .inr ⟨.and, []⟩
  | .and, [some x] => .inl (some x)
  | .and, [some x, some y] => .inr ⟨.and, [x,y]⟩
  | .or, [some x, some y] => .inr ⟨.or, [x,y]⟩
  | .or, [some x] | .or, [some x, none] | .or, [none, some x] => .inl (some x)
  | _, _ => .inl none

private theorem reduce_spec (op : GateOp) (r : List (Option Nat)) (w : List Bool)
    (kind : op = .and ∨ op = .or) (small : r.length ≤ 2) :
    match reduce op r with
    | .inl a => readRef w a = op.eval (r.map (readRef w)) ∧ ∀ i, a = some i → some i ∈ r
    | .inr g => g.op = op ∧ g.inputs.length ≤ 2 ∧ (∀ i ∈ g.inputs, some i ∈ r) ∧
        none ∉ r ∧ g.op.eval (g.inputs.map (fun i => w.getD i false)) = op.eval (r.map (readRef w)) := by
  rcases kind with rfl|rfl <;>
    rcases r with _|⟨a,_|⟨b,_|⟨c,tail⟩⟩⟩
  all_goals simp only [List.length_cons,List.length_nil] at small
  all_goals try omega
  all_goals try cases a
  all_goals try cases b
  all_goals simp [reduce, readRef, GateOp.eval, or_comm]

private def State := List Gate × List (Option Nat)

private def step (m : Nat) (s : State) (g : Gate) : State :=
  let r := g.inputs.map (fun i => s.2.getD i none)
  match reduce g.op r with
  | .inl a => (s.1, s.2 ++ [a])
  | .inr h => (s.1 ++ [h], s.2 ++ [some (m + s.1.length)])

private def init (n m : Nat) : State :=
  ([], (List.range n).map some ++ [none] ++ (List.range m).map (fun i => some (n+i)))

private def run (s : List Gate) (xs : List Bool) : List Bool := (Circuit.mk s 0).wires xs

private theorem run_snoc (s : List Gate) (g : Gate) (xs : List Bool) :
    run (s ++ [g]) xs = run s xs ++ [g.op.eval (g.inputs.map (fun i => (run s xs).getD i false))] := by
  simp [run, Circuit.wires, List.foldl_append]

private theorem run_length (s : List Gate) (xs : List Bool) : (run s xs).length=xs.length+s.length := by
  induction s using List.reverseRecOn with
  | nil => simp [run, Circuit.wires]
  | append_singleton s g ih => simp [run_snoc, ih, Nat.add_assoc]

private theorem getD_map_ref (r : List (Option Nat)) (w : List Bool) (i : Nat) :
    (r.map (readRef w)).getD i false = readRef w (r.getD i none) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases r[i]? <;> rfl

private theorem read_before_append (w : List Bool) (b : Bool) (a : Option Nat)
    (below : ∀ i, a=some i → i<w.length) : readRef (w++[b]) a=readRef w a := by
  cases a with
  | none => rfl
  | some i =>
    simp only [readRef, List.getD_eq_getElem?_getD, List.getElem?_append_left (below i rfl)]

private def WireBound (m : Nat) (s : State) : Prop :=
  ∀ a ∈ s.2, ∀ i, a = some i → i < m+s.1.length

private def GateBound (s : State) : Prop :=
  ∀ g∈s.1, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2

private theorem bound_input (m : Nat) (s : State) (bound : WireBound m s)
    (j i : Nat) (same : s.2.getD j none = some i) : i < m + s.1.length := by
  have below : j < s.2.length := by
    by_contra not
    rw [List.getD_eq_default _ _ (by omega)] at same
    cases same
  exact bound _ (by simpa only [List.getD_eq_getElem _ _ below] using List.getElem_mem (l:=s.2) below) i same

private theorem step_spec (m : Nat) (s : State) (g : Gate) (xs : List Bool) (hx : xs.length=m)
    (bounded : WireBound m s) (normal : GateBound s) (kind : g.op=.and ∨ g.op=.or) (small : g.inputs.length≤2) :
    WireBound m (step m s g) ∧ GateBound (step m s g) ∧
    s.1.length ≤ (step m s g).1.length ∧ (step m s g).1.length ≤ s.1.length + 1 ∧
    (none ∈ g.inputs.map (fun i=>s.2.getD i none) → (step m s g).1.length=s.1.length) ∧
    (step m s g).2.map (readRef (run (step m s g).1 xs)) =
      (s.2.map (readRef (run s.1 xs))) ++
        [g.op.eval (g.inputs.map (fun i => (s.2.map (readRef (run s.1 xs))).getD i false))] := by
  let r := g.inputs.map (fun i=>s.2.getD i none)
  let w := run s.1 xs
  have spec := reduce_spec g.op r w kind (by simpa [r] using small)
  have rhs : g.op.eval (g.inputs.map (fun i => (s.2.map (readRef w)).getD i false)) =
      g.op.eval (r.map (readRef w)) := by
    simp only [r, List.map_map, Function.comp_def, getD_map_ref]
  have rBelow (i : Nat) (mem : some i ∈ r) : i < m + s.1.length := by
    obtain ⟨j,_,same⟩ := List.mem_map.mp mem
    exact bound_input m s bounded j i same
  cases h : reduce g.op r with
  | inl a =>
    change reduce g.op r = .inl a at h
    rw [h] at spec
    change (readRef w a = g.op.eval (r.map (readRef w))) ∧ (∀ i,a=some i → some i∈r) at spec
    have byStep : step m s g=(s.1,s.2++[a]) := by unfold step; change (match reduce g.op r with | .inl a => _ | .inr k => _) = _; rw [h]
    rw [byStep]
    refine ⟨?_,normal,le_rfl,Nat.le_succ _,fun _=>rfl,?_⟩
    · intro b bm i same
      rcases List.mem_append.mp bm with old|new
      · exact bounded b old i same
      · have ba : b=a := by simpa using new
        exact rBelow i (spec.2 i (ba.symm ▸ same))
    · simp only [List.map_append,List.map_cons,List.map_nil]
      rw [rhs, spec.1]
  | inr k =>
    rw [h] at spec
    change k.op=g.op ∧ k.inputs.length≤2 ∧ (∀ i∈k.inputs,some i∈r) ∧ none∉r ∧
      k.op.eval (k.inputs.map (fun i=>w.getD i false))=g.op.eval (r.map (readRef w)) at spec
    have byStep : step m s g=(s.1++[k],s.2++[some (m+s.1.length)]) := by unfold step; change (match reduce g.op r with | .inl a => _ | .inr k => _) = _; rw [h]
    rw [byStep]
    simp only [List.length_append,List.length_singleton]
    refine ⟨?_,?_,by omega,by omega,fun mem=>False.elim (spec.2.2.2.1 mem),?_⟩
    · intro a am i same
      change i < m + (s.1++[k]).length
      simp only [List.length_append,List.length_singleton]
      rcases List.mem_append.mp am with old|new
      · have lt := bounded a old i same
        omega
      · simp at new
        rw [new] at same
        injection same with eq
        omega
    · intro l lm
      rcases List.mem_append.mp lm with old|new
      · exact normal l old
      · have lk : l=k := by simpa using new
        exact lk.symm ▸ ⟨spec.1.symm ▸ kind,spec.2.1⟩
    · let b := k.op.eval (k.inputs.map (fun i=>w.getD i false))
      have len : w.length=m+s.1.length := by simp [w, run_length, hx]
      have newW : run (s.1++[k]) xs = w++[b] := run_snoc s.1 k xs
      rw [newW]
      simp only [List.map_append,List.map_cons,List.map_nil]
      have older : s.2.map (readRef (w++[b])) = s.2.map (readRef w) := by
        apply List.map_congr_left
        intro a am
        exact read_before_append w b a (fun i ai=>by rw [len]; exact bounded a am i ai)
      have last : readRef (w++[b]) (some (m+s.1.length)) = b := by
        rw [readRef, ←len, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
        simp
      rw [older,last,rhs]
      exact congrArg (fun t => s.2.map (readRef w) ++ [t]) spec.2.2.2.2

private theorem step_ref_prefix (m : Nat) (s : State) (g : Gate) :
    s.2 <+: (step m s g).2 := by
  cases h : reduce g.op (g.inputs.map (fun i=>s.2.getD i none)) <;>
    simp only [step,h] <;> exact List.prefix_append _ _

private theorem ref_prefix_getD {r t : List (Option Nat)} (hpre : r <+: t) (p : Nat)
    (hp : p < r.length) : t.getD p none = r.getD p none := by
  obtain ⟨suffix,rfl⟩ := hpre
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left hp]

private def oldStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (fun i=>w.getD i false))]

private theorem process_spec (m p : Nat) (gs : List Gate) (s : State) (xs : List Bool)
    (hx : xs.length=m) (bounded : WireBound m s) (normal : GateBound s)
    (primary : p < s.2.length) (missing : s.2.getD p none=none)
    (legal : ∀g∈gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2) :
    let t := gs.foldl (step m) s
    WireBound m t ∧ GateBound t ∧ t.1.length ≤ s.1.length+gs.length ∧
      ((∃g∈gs,p∈g.inputs) → t.1.length+1 ≤ s.1.length+gs.length) ∧
      t.2.map (readRef (run t.1 xs)) = gs.foldl oldStep (s.2.map (readRef (run s.1 xs))) := by
  induction gs generalizing s with
  | nil => simp [bounded,normal]
  | cons g gs ih =>
    have head := legal g (by simp)
    obtain ⟨bnd,norm,_,size,drop,sem⟩ := step_spec m s g xs hx bounded normal head.1 head.2
    let u := step m s g
    have hpre : s.2 <+: u.2 := step_ref_prefix m s g
    have prime : p < u.2.length := lt_of_lt_of_le primary hpre.length_le
    have miss' : u.2.getD p none=none := (ref_prefix_getD hpre p primary).trans missing
    obtain ⟨finB,finN,cap,saved,finalSem⟩ := ih u bnd norm prime miss'
      (fun g' gm=>legal g' (List.mem_cons_of_mem _ gm))
    let t := gs.foldl (step m) u
    change WireBound m t ∧ GateBound t ∧ t.1.length ≤ s.1.length+(g::gs).length ∧
      ((∃g'∈g::gs,p∈g'.inputs) → t.1.length+1 ≤ s.1.length+(g::gs).length) ∧ _
    change t.1.length ≤ u.1.length+gs.length at cap
    change u.1.length ≤ s.1.length+1 at size
    refine ⟨finB,finN,by simp only [List.length_cons];omega,?_,?_⟩
    · rintro ⟨v,vm,use⟩
      simp only [List.length_cons]
      rcases List.mem_cons.mp vm with rfl|tail
      · have erased : u.1.length=s.1.length := drop (List.mem_map.mpr ⟨p,use,missing⟩)
        omega
      · have cut : t.1.length+1 ≤ u.1.length+gs.length := saved ⟨v,tail,use⟩
        omega
    · change t.2.map (readRef (run t.1 xs)) = gs.foldl oldStep (oldStep _ g)
      rw [finalSem,show u.2.map (readRef (run u.1 xs))=oldStep (s.2.map (readRef (run s.1 xs))) g from sem]

private theorem init_bounds (n m : Nat) : WireBound (n+m) (init n m) := by
  intro a am i eq
  change a ∈ ((List.range n).map some ++ [none]) ++ (List.range m).map (fun i=>some (n+i)) at am
  rcases List.mem_append.mp am with prev|right
  · rcases List.mem_append.mp prev with left|middle
    · obtain ⟨j,jm,js⟩ := List.mem_map.mp left
      have hj := List.mem_range.mp jm
      have e : j=i := Option.some.inj (js.trans eq)
      change i < n+m+0
      omega
    · have emp : a=none := List.mem_singleton.mp middle
      rw [emp] at eq
      cases eq
  · obtain ⟨j,jm,js⟩ := List.mem_map.mp right
    have hj := List.mem_range.mp jm
    have e : n+j=i := Option.some.inj (js.trans eq)
    change i < n+m+0
    omega

private theorem init_getD_none (n m : Nat) : (init n m).2.getD n none=none := by
  unfold init
  change (((List.range n).map some ++ [none]) ++ (List.range m).map (fun i=>some (n+i))).getD n none=none
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp),List.getElem?_append_right (by simp)]
  simp

private theorem init_sem (n m : Nat) (xs : List Bool) (hx : xs.length=n+m) :
    (init n m).2.map (readRef (run (init n m).1 xs)) = xs.take n ++ [false] ++ xs.drop n := by
  have left : (List.range n).map (fun i=>xs.getD i false)=xs.take n := by
    apply List.ext_getElem
    · simp [List.length_take, hx]
    · intro i il ir
      rw [List.getElem_map,List.getElem_range,List.getElem_take]
      exact List.getD_eq_getElem _ _ (by simp at il; omega)
  have right : (List.range m).map (fun i=>xs.getD (n+i) false)=xs.drop n := by
    apply List.ext_getElem
    · simp [hx]
    · intro i il ir
      rw [List.getElem_map,List.getElem_range,List.getElem_drop]
      have hi : i < m := by simpa using il
      rw [List.getD_eq_getElem _ _ (by omega)]
  change (((List.range n).map some ++ [none]) ++ (List.range m).map (fun i=>some (n+i))).map
    (readRef xs) = _
  simp only [List.map_append,List.map_cons,List.map_nil,List.map_map,Function.comp_def,readRef,left,right]

private theorem inserted_agree (n m : Nat) (xs : List Bool) (hx : xs.length=n+m) :
    ∀ i, i≠n → (xs.take n++[true]++xs.drop n).getD i false =
      (xs.take n++[false]++xs.drop n).getD i false := by
  intro i different
  have takeLen : (xs.take n).length=n := by simp [List.length_take,hx]
  simp only [List.getD_eq_getElem?_getD]
  by_cases lt : i<n
  · have pre : i<(xs.take n).length := by omega
    rw [List.getElem?_append_left (by simp [takeLen]; omega),List.getElem?_append_left pre,
      List.getElem?_append_left (by simp [takeLen]; omega),List.getElem?_append_left pre]
  · have ge : n + 1 ≤ i := by omega
    rw [List.getElem?_append_right (by simpa [takeLen]),List.getElem?_append_right (by simpa [takeLen])]
    simp [takeLen]

private theorem append_agree (p : Nat) (w v : List Bool) (size : w.length=v.length)
    (agree : ∀ i,i≠p → w.getD i false=v.getD i false) (bit : Bool) :
    ∀ i,i≠p → (w++[bit]).getD i false=(v++[bit]).getD i false := by
  intro i different
  by_cases left : i<w.length
  · have right : i<v.length := by omega
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_append_left left,List.getElem?_append_left right] using
      agree i different
  · simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega),List.getElem?_append_right (by omega),size]

private theorem unread_fold (p : Nat) (gs : List Gate) (w v : List Bool)
    (size : w.length=v.length) (agree : ∀ i,i≠p → w.getD i false=v.getD i false)
    (unread : ∀ g∈gs, p∉g.inputs) :
    ∀ i,i≠p → (gs.foldl oldStep w).getD i false=(gs.foldl oldStep v).getD i false := by
  induction gs generalizing w v with
  | nil => exact agree
  | cons g tail ih =>
    have same : g.inputs.map (fun i=>w.getD i false)=g.inputs.map (fun i=>v.getD i false) := by
      apply List.map_congr_left
      intro i im
      exact agree i (fun ip=>unread g (by simp) (ip ▸ im))
    have oldSize : (oldStep w g).length=(oldStep v g).length := by simp [oldStep,size]
    have oldAgree : ∀ i,i≠p → (oldStep w g).getD i false=(oldStep v g).getD i false := by
      unfold oldStep
      rw [same]
      exact append_agree p w v size agree _
    exact ih (oldStep w g) (oldStep v g) oldSize oldAgree
      (fun g' gm=>unread g' (List.mem_cons_of_mem _ gm))

theorem remove_last_row (n m : Nat) (C : Circuit) (mono : Monotone2 C) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧
      (∀ xs : List Bool, xs.length=n+m → D.eval xs=C.eval (xs.take n++[false]++xs.drop n)) ∧
      (D.size+1≤C.size ∨
        (∀ xs : List Bool, xs.length=n+m →
          C.eval (xs.take n++[true]++xs.drop n)=C.eval (xs.take n++[false]++xs.drop n)) ∨ C.output=n) := by
  classical
  let t := C.gates.foldl (step (n+m)) (init n m)
  let r := t.2.getD C.output none
  let D : Circuit := ⟨t.1,r.getD (n+m+t.1.length)⟩
  have pInit : n < (init n m).2.length := by simp [init]
  have gInit : GateBound (init n m) := by simp [GateBound,init]
  have good (xs : List Bool) (hx : xs.length=n+m) :=
    process_spec (n+m) n C.gates (init n m) xs hx (init_bounds n m) gInit pInit (init_getD_none n m) mono
  obtain ⟨_,normal,cap,saving,_⟩ := good (List.replicate (n+m) false) (by simp)
  change t.1.length ≤ (init n m).1.length + C.gates.length at cap
  change (∃g∈C.gates,n∈g.inputs) → t.1.length + 1 ≤ (init n m).1.length + C.gates.length at saving
  refine ⟨D,normal,by simpa only [D,Circuit.size,init,Prod.fst,List.length_nil,Nat.zero_add] using cap,?_,?_⟩
  · intro xs hx
    have mapped : t.2.map (readRef (run t.1 xs))=C.wires (xs.take n++[false]++xs.drop n) := by
      have sem := (good xs hx).2.2.2.2
      rw [init_sem n m xs hx] at sem
      exact sem
    have eq : readRef (run t.1 xs) r = C.eval (xs.take n++[false]++xs.drop n) := by
      unfold Circuit.eval
      rw [←mapped,getD_map_ref]
    rw [←eq]
    change (run t.1 xs).getD (r.getD (n+m+t.1.length)) false=readRef (run t.1 xs) r
    cases h : r with
    | none =>
      exact List.getD_eq_default _ _ (by simp [run_length,hx])
    | some i => rfl
  · by_cases read : ∃g∈C.gates,n∈g.inputs
    · exact .inl (by simpa only [D,Circuit.size,init,Prod.fst,List.length_nil,Nat.zero_add] using saving read)
    right
    by_cases out : C.output=n
    · exact .inr out
    left
    intro xs hx
    exact unread_fold n C.gates (xs.take n++[true]++xs.drop n) (xs.take n++[false]++xs.drop n)
      (by simp) (inserted_agree n m xs hx) (fun g gm readInput=>read ⟨g,gm,readInput⟩) C.output out

end Meta27803Delete

namespace Meta27803Lower
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents



def RemoveLast : Prop :=
  ∀ (n m : Nat) (C : Circuit), Monotone2 C →
    ∃ D : Circuit, Monotone2 D ∧ D.size  ≤  C.size ∧
      (∀ xs : List Bool, xs.length=n+m →
        D.eval xs=C.eval (xs.take n ++ [false] ++ xs.drop n)) ∧
      (D.size+1 ≤ C.size ∨
        (∀ xs : List Bool, xs.length=n+m →
          C.eval (xs.take n ++ [true] ++ xs.drop n)=
            C.eval (xs.take n ++ [false] ++ xs.drop n)) ∨ C.output=n)

def expanded {n m : Nat} (A : Fin n→Fin m→Bool) (u : Fin n) (t : Nat) :
    Fin (n+t)→Fin m→Bool :=
  fun i j=>if h : i.val<n then A ⟨i.val,h⟩ j else A u j

def Silent {n m : Nat} (A : Fin n→Fin m→Bool) (u : Fin n) (s : Nat) : Prop :=
  ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ Represents A C ∧
    ∀j : Fin m,C.eval (List.replicate n false ++ List.ofFn (fun v : Fin m=>decide (v=j)))=A u j


def rowHot (N i : Nat) : List Bool := List.ofFn (fun v : Fin N=>decide (v.val=i))
def colHot {m : Nat} (j : Fin m) : List Bool := List.ofFn (fun v : Fin m=>decide (v=j))
def emptyRows (N : Nat) {m : Nat} (j : Fin m) : List Bool := List.replicate N false ++ colHot j
def insertBit (N : Nat) (b : Bool) (xs : List Bool) : List Bool := xs.take N ++ [b] ++ xs.drop N

@[simp] theorem length_rowHot (N i : Nat) : (rowHot N i).length=N := by simp [rowHot]
@[simp] theorem length_colHot {m : Nat} (j : Fin m) : (colHot j).length=m := by simp [colHot]
@[simp] theorem length_emptyRows (N : Nat) {m : Nat} (j : Fin m) : (emptyRows N j).length=N+m := by simp [emptyRows]

lemma oneEach_eq {N m : Nat} (i : Fin N) (j : Fin m) :
    oneEach i j=rowHot N i.val ++ colHot j := by
  simp only [oneEach,rowHot,colHot,Fin.ext_iff]

lemma rowHot_succ (N i : Nat) : rowHot (N+1) i=rowHot N i ++ [decide (N=i)] := by
  unfold rowHot
  rw [List.ofFn_succ']
  simp only [Fin.val_castSucc,Fin.val_last,List.concat_eq_append]

lemma rowHot_outside (N i : Nat) (outside : N ≤ i) : rowHot N i=List.replicate N false := by
  unfold rowHot
  have pointwise : (fun v : Fin N=>decide (v.val=i))=(fun _ : Fin N=>false) := by
    funext v
    have different : v.val≠i := by omega
    simp [different]
  rw [pointwise,List.ofFn_const]

lemma insertBit_append (N : Nat) (b : Bool) (xs ys : List Bool) (length : xs.length=N) :
    insertBit N b (xs++ys)=xs++[b]++ys := by
  subst N
  simp [insertBit]

lemma insert_oneEach_false {N m : Nat} (i : Fin N) (j : Fin m) :
    insertBit N false (oneEach i j)=
      rowHot (N+1) i.val ++ colHot j := by
  rw [oneEach_eq,insertBit_append N false (rowHot N i.val) (colHot j) (length_rowHot N i.val)]
  rw [rowHot_succ]
  have different : N≠i.val:=by omega
  simp [different]

lemma insert_emptyRows (N : Nat) {m : Nat} (j : Fin m) (b : Bool) :
    insertBit N b (emptyRows N j)=List.replicate N false ++ [b] ++ colHot j := by
  exact insertBit_append N b _ _ (by simp)

lemma insert_emptyRows_false (N : Nat) {m : Nat} (j : Fin m) :
    insertBit N false (emptyRows N j)=emptyRows (N+1) j := by
  rw [insert_emptyRows]
  simp [emptyRows,List.replicate_add,List.append_assoc]

lemma insert_emptyRows_true (N : Nat) {m : Nat} (j : Fin m) :
    insertBit N true (emptyRows N j)=rowHot (N+1) N ++ colHot j := by
  rw [insert_emptyRows,rowHot_succ,rowHot_outside N N (by omega)]
  simp

private def run (gs : List Gate) (xs : List Bool) : List Bool :=
  gs.foldl (fun w g=>w++[g.op.eval (g.inputs.map (fun i=>w.getD i false))]) xs

private lemma run_preserves_input (gs : List Gate) (xs : List Bool) (i : Nat) (inside : i<xs.length) :
    (run gs xs).getD i false=xs.getD i false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (xs++[g.op.eval (g.inputs.map (fun k=>xs.getD k false))])).getD i false=xs.getD i false
    rw [ih _ (by simp;omega)]
    exact List.getD_append _ _ _ _ inside

lemma eval_input_output (C : Circuit) (xs : List Bool) (inside : C.output<xs.length) :
    C.eval xs=xs.getD C.output false := by
  exact run_preserves_input C.gates xs C.output inside

lemma last_row_bit (N i : Nat) {m : Nat} (j : Fin m) :
    (rowHot (N+1) i ++ colHot j).getD N false=decide (N=i) := by
  rw [rowHot_succ,List.append_assoc]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp


theorem restriction_represents {n m t : Nat} (A : Fin n→Fin m→Bool) (u : Fin n)
    (C D : Circuit)
    (restricted : ∀xs : List Bool,xs.length=(n+t)+m →
      D.eval xs=C.eval (insertBit (n+t) false xs))
    (rep : Represents (expanded A u (t+1)) C) : Represents (expanded A u t) D := by
  intro i j
  rw [restricted (oneEach i j) (by simp [oneEach]),insert_oneEach_false]
  let i' : Fin (n+(t+1)):=⟨i.val,by omega⟩
  have represented:=rep i' j
  rw [oneEach_eq] at represented
  simpa [expanded,i',Nat.add_assoc] using represented


theorem restriction_preserves_silence {n m t : Nat} (A : Fin n→Fin m→Bool) (u : Fin n)
    (C D : Circuit)
    (restricted : ∀xs : List Bool,xs.length=(n+t)+m →
      D.eval xs=C.eval (insertBit (n+t) false xs))
    (silent : ∀j : Fin m,C.eval (emptyRows (n+(t+1)) j)=A u j) :
    ∀j : Fin m,D.eval (emptyRows (n+t) j)=A u j := by
  intro j
  rw [restricted _ (length_emptyRows _ j),insert_emptyRows_false]
  simpa [Nat.add_assoc] using silent j


theorem independence_gives_silence {n m t : Nat} (A : Fin n→Fin m→Bool) (u : Fin n)
    (C D : Circuit)
    (restricted : ∀xs : List Bool,xs.length=(n+t)+m →
      D.eval xs=C.eval (insertBit (n+t) false xs))
    (independent : ∀xs : List Bool,xs.length=(n+t)+m →
      C.eval (insertBit (n+t) true xs)=C.eval (insertBit (n+t) false xs))
    (rep : Represents (expanded A u (t+1)) C) :
    ∀j : Fin m,D.eval (emptyRows (n+t) j)=A u j := by
  intro j
  rw [restricted _ (length_emptyRows _ j),←independent _ (length_emptyRows _ j),insert_emptyRows_true]
  let last : Fin (n+(t+1)):=⟨n+t,by omega⟩
  have represented:=rep last j
  rw [oneEach_eq] at represented
  simpa [expanded,last,Nat.add_assoc] using represented


theorem expanded_output_ne_last {n m t : Nat} (A : Fin n→Fin m→Bool) (u : Fin n)
    (column : Fin m) (C : Circuit) (rep : Represents (expanded A u (t+1)) C) : C.output≠n+t := by
  intro output
  let original : Fin (n+(t+1)):=⟨u.val,by omega⟩
  let last : Fin (n+(t+1)):=⟨n+t,by omega⟩
  have originalRep:=rep original column
  have lastRep:=rep last column
  rw [oneEach_eq] at originalRep lastRep
  have originalEval : C.eval (rowHot (n+(t+1)) u.val ++ colHot column)=false := by
    rw [eval_input_output C _ (by simp [output];omega),output]
    have rowBit:=last_row_bit (n+t) u.val column
    have different : n+t≠u.val:=by omega
    simpa [Nat.add_assoc,different] using rowBit
  have lastEval : C.eval (rowHot (n+(t+1)) (n+t) ++ colHot column)=true := by
    rw [eval_input_output C _ (by simp [output];omega),output]
    simpa [Nat.add_assoc] using last_row_bit (n+t) (n+t) column
  have originalValue : A u column=false := by
    simpa [expanded,original,u.isLt] using originalRep.symm.trans originalEval
  have lastValue : A u column=true := by
    simpa [expanded,last] using lastRep.symm.trans lastEval
  rw [originalValue] at lastValue
  cases lastValue


theorem erase_copies_preserving_silence (removeLast : RemoveLast)
    {n m : Nat} (A : Fin n→Fin m→Bool) (u : Fin n) :
    ∀t : Nat,∀C : Circuit,Monotone2 C → Represents (expanded A u t) C →
      (∀j : Fin m,C.eval (emptyRows (n+t) j)=A u j) →
      ∃D : Circuit,Monotone2 D ∧ D.size ≤ C.size ∧ Represents A D ∧
        ∀j : Fin m,D.eval (emptyRows n j)=A u j := by
  intro t
  induction t with
  | zero =>
    intro C mono rep silent
    refine ⟨C,mono,le_rfl,?_,?_⟩
    · intro i j
      simpa [expanded,i.isLt] using rep ⟨i.val,by omega⟩ j
    · simpa using silent
  | succ t ih =>
    intro C mono rep silent
    obtain ⟨D,monoD,sizeD,restriction,_⟩:=removeLast (n+t) m C mono
    have restriction' : ∀xs : List Bool,xs.length=(n+t)+m → D.eval xs=C.eval (insertBit (n+t) false xs):=restriction
    obtain ⟨E,monoE,sizeE,repE,silentE⟩:=ih D monoD
      (restriction_represents A u C D restriction' rep)
      (restriction_preserves_silence A u C D restriction' silent)
    exact ⟨E,monoE,sizeE.trans sizeD,repE,silentE⟩


theorem lower_from_removeLast (removeLast : RemoveLast) :
    ∀ (n m : Nat) (A : Fin n→Fin m→Bool) (u : Fin n),
      (∃i j,A i j=false) → ∀t s : Nat,
      let expanded := fun (i : Fin (n+t)) (j : Fin m)=>
        if h : i.val<n then A ⟨i.val,h⟩ j else A u j
      let silent := ∃C : Circuit,Monotone2 C ∧ C.size ≤ s ∧ Represents A C ∧
        ∀j : Fin m,C.eval (List.replicate n false ++ List.ofFn (fun v : Fin m=>decide (v=j)))=A u j
      RepSizeAtMost expanded s → (∃b : Nat,b+t ≤ s ∧ RepSizeAtMost A b) ∨ silent := by
  intro n m A u zero t
  induction t with
  | zero =>
    intro s
    dsimp only
    intro hypothesis
    obtain ⟨C,mono,size,rep⟩:=hypothesis
    left
    refine ⟨C.size,by omega,C,mono,le_rfl,?_⟩
    intro i j
    simpa [i.isLt] using rep ⟨i.val,by omega⟩ j
  | succ t ih =>
    intro s
    dsimp only
    intro hypothesis
    obtain ⟨C,mono,size,rep⟩:=hypothesis
    change Represents (Meta27803Lower.expanded A u (t+1)) C at rep
    obtain ⟨D,monoD,sizeD,restriction,casesD⟩:=removeLast (n+t) m C mono
    have restriction' : ∀xs : List Bool,xs.length=(n+t)+m → D.eval xs=C.eval (insertBit (n+t) false xs):=restriction
    have repD:=restriction_represents A u C D restriction' rep
    rcases casesD with saves|independent|output
    · have reduced : RepSizeAtMost (Meta27803Lower.expanded A u t) D.size:=⟨D,monoD,le_rfl,repD⟩
      rcases ih D.size reduced with ⟨b,budget,base⟩|⟨E,monoE,sizeE,base,silentE⟩
      · exact .inl ⟨b,by omega,base⟩
      · exact .inr ⟨E,monoE,sizeE.trans (sizeD.trans size),base,silentE⟩
    · have silentD:=independence_gives_silence A u C D restriction' independent rep
      obtain ⟨E,monoE,sizeE,base,silentE⟩:=erase_copies_preserving_silence removeLast A u t D monoD repD silentD
      exact .inr ⟨E,monoE,sizeE.trans (sizeD.trans size),base,silentE⟩
    · obtain ⟨i,j,_⟩:=zero
      exact False.elim (expanded_output_ne_last A u j C rep output)

end Meta27803Lower

namespace Meta27803Upper
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents


def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def relabel (r : Nat → Nat) (g : Gate) : Gate := ⟨g.op,g.inputs.map r⟩

lemma run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g::gs) w = run gs (w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]) := rfl

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : Nat) (h : j ≠ L.length) :
    (L++[S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) :
    (L++[S]).getD L.length d = S := by simp

theorem relabel_sim_all (r : ℕ → ℕ) (gs : List Gate) : ∀ (v w : List Bool),
    (∀ i, v.getD (r i) false = w.getD i false) →
    (∀ i < w.length, r i < v.length ∨ v.length + gs.length ≤ r i) →
    (∀ k < gs.length, r (w.length + k) = v.length + k) →
    (∀ i, w.length + gs.length ≤ i → v.length + gs.length ≤ r i) →
    ∀ i, (run (gs.map (relabel r)) v).getD (r i) false
      = (run gs w).getD i false := by
  induction gs with
  | nil => intro v w h1 _ _ _ i; exact h1 i
  | cons g gs ih =>
    intro v w h1 h2 h3 h4
    simp only [List.length_cons] at h2 h3 h4
    have hval : (relabel r g).op.eval
          ((relabel r g).inputs.map fun i => v.getD i false)
        = g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [relabel, List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact h1 j
    have hr0 : r w.length = v.length := by simpa using h3 0 (by omega)
    have hne : ∀ i, i ≠ w.length → r i ≠ v.length := by
      intro i hi
      by_cases hlt : i < w.length
      · rcases h2 i hlt with h | h <;> omega
      · by_cases hk : i < w.length + (gs.length + 1)
        · have := h3 (i - w.length) (by omega)
          rw [show w.length + (i - w.length) = i by omega] at this
          omega
        · have := h4 i (by omega); omega
    rw [List.map_cons, run_cons, run_cons, hval]
    apply ih
    · intro i
      by_cases hi : i = w.length
      · subst hi
        rw [hr0, getD_snoc_eq, getD_snoc_eq]
      · rw [getD_snoc_ne _ _ _ _ (hne i hi), getD_snoc_ne _ _ _ _ hi]
        exact h1 i
    · intro i hi
      simp only [List.length_append, List.length_singleton] at hi ⊢
      by_cases hlt : i < w.length
      · rcases h2 i hlt with h | h
        · left; omega
        · right; omega
      · left; have : i = w.length := by omega
        subst this; omega
    · intro k hk
      simp only [List.length_append, List.length_singleton]
      have := h3 (k + 1) (by omega)
      rw [show w.length + 1 + k = w.length + (k + 1) by omega, this]; omega
    · intro i hi
      simp only [List.length_append, List.length_singleton] at hi ⊢
      have := h4 i (by omega); omega


theorem relabel_sim (r : ℕ → ℕ) (gs : List Gate) (v w : List Bool)
    (h1 : ∀ i < w.length, v.getD (r i) false = w.getD i false)
    (h2 : ∀ i < w.length, r i < v.length ∨ v.length + gs.length ≤ r i)
    (h3 : ∀ k < gs.length, r (w.length + k) = v.length + k)
    (h4 : ∀ i, w.length + gs.length ≤ i → v.length + gs.length ≤ r i) (i : ℕ) :
    (run (gs.map (relabel r)) v).getD (r i) false
      = (run gs w).getD i false := by
  apply relabel_sim_all r gs v w _ h2 h3 h4
  intro j
  by_cases hj : j < w.length
  · exact h1 j hj
  · have hge : v.length ≤ r j := by
      by_cases hk : j < w.length + gs.length
      · have := h3 (j - w.length) (by omega)
        rw [show w.length + (j - w.length) = j by omega] at this
        omega
      · have := h4 j (by omega); omega
    rw [List.getD_eq_default _ _ hge, List.getD_eq_default _ _ (by omega)]


lemma relabel_monotone (r : Nat→Nat) (C : Circuit) (h : Monotone2 C) :
    Monotone2 ⟨C.gates.map (relabel r),r C.output⟩ := by
  rintro g hg
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
  obtain ⟨ho,hl⟩ := h a ha
  exact ⟨ho,by simpa [relabel] using hl⟩


def rowInput (n : Nat) {m : Nat} (r : Nat) (j : Fin m) : List Bool :=
  List.ofFn (fun i : Fin n=>decide (i.val=r)) ++
    List.ofFn (fun i : Fin m=>decide (i=j))

lemma rowInput_length (n r : Nat) {m : Nat} (j : Fin m) :
    (rowInput n r j).length=n+m := by simp [rowInput]

lemma getD_ofFn {n : Nat} (x : Fin n→Bool) (i : Nat) (hi : i<n) :
    (List.ofFn x).getD i false=x ⟨i,hi⟩ := by
  simp [List.getD_eq_getElem?_getD,hi]

lemma rowInput_getD (n r i : Nat) {m : Nat} (j : Fin m) :
    (rowInput n r j).getD i false=
      if i<n then decide (i=r) else decide (i=n+j.val) := by
  by_cases hi : i<n
  · rw [if_pos hi]
    unfold rowInput
    rw [List.getD_append _ _ _ _ (by simpa using hi),getD_ofFn _ _ hi]
  · rw [if_neg hi]
    by_cases him : i<n+m
    · unfold rowInput
      rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hi)]
      simp only [List.length_ofFn]
      rw [getD_ofFn _ _ (by omega)]
      simp only [Fin.ext_iff]
      apply decide_eq_decide.mpr
      omega
    · rw [List.getD_eq_default _ _ (by rw [rowInput_length];omega)]
      simp [show i≠n+j.val by have := j.isLt;omega]

lemma rowInput_oneEach {n m : Nat} (i : Fin n) (j : Fin m) :
    rowInput n i.val j=oneEach i j := by
  unfold rowInput oneEach
  congr 1

lemma rowInput_silent {n m r : Nat} (j : Fin m) (hr : n≤r) :
    rowInput n r j=List.replicate n false++List.ofFn (fun v : Fin m=>decide (v=j)) := by
  unfold rowInput
  have h : (fun i : Fin n=>decide (i.val=r))=(fun _ : Fin n=>false) := by
    funext i
    simp [show i.val≠r by have := i.isLt;omega]
  rw [h]
  simp


def padMap (n t i : Nat) : Nat := if i<n then i else i+t

def padCircuit (n t : Nat) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relabel (padMap n t)),padMap n t C.output⟩

lemma pad_eval {n m : Nat} (C : Circuit) (t r : Nat) (j : Fin m) :
    (padCircuit n t C).eval (rowInput (n+t) r j)=C.eval (rowInput n r j) := by
  change (run (C.gates.map (relabel (padMap n t))) (rowInput (n+t) r j)).getD
      (padMap n t C.output) false=(run C.gates (rowInput n r j)).getD C.output false
  apply relabel_sim
  · intro i hi
    rw [rowInput_length] at hi
    rw [rowInput_getD,rowInput_getD]
    by_cases hin : i<n
    · simp [padMap,hin,show i<n+t by omega]
    · simp only [padMap,hin,if_false]
      rw [if_neg (by omega)]
      apply decide_eq_decide.mpr
      omega
  · intro i hi
    simp only [rowInput_length] at hi ⊢
    left
    by_cases hin : i<n <;> simp [padMap,hin] <;> omega
  · intro k hk
    simp only [rowInput_length]
    simp [padMap,show ¬n+m+k<n by omega]
    omega
  · intro i hi
    simp only [rowInput_length] at hi ⊢
    simp [padMap,show ¬i<n by omega]
    omega


theorem silent_upper {n m : Nat} (A : Fin n→Fin m→Bool) (u : Fin n) (t s : Nat)
    (silent : ∃C : Circuit,Monotone2 C ∧ C.size≤ s ∧ Represents A C ∧
      ∀j : Fin m,C.eval (List.replicate n false++List.ofFn (fun v : Fin m=>decide (v=j)))=A u j) :
    RepSizeAtMost (fun i : Fin (n+t)=>fun j=>if h : i.val<n then A ⟨i.val,h⟩ j else A u j) s := by
  obtain ⟨C,hmono,hsize,hrep,hsilent⟩ := silent
  refine ⟨padCircuit n t C,relabel_monotone _ C hmono,?_,?_⟩
  · simpa [padCircuit,Circuit.size] using hsize
  · intro i j
    rw [←rowInput_oneEach,pad_eval]
    change C.eval (rowInput n i.val j)=(if h : i.val<n then A ⟨i.val,h⟩ j else A u j)
    by_cases hi : i.val<n
    · rw [dif_pos hi]
      rw [rowInput_oneEach (⟨i.val,hi⟩ : Fin n) j]
      exact hrep _ _
    · rw [dif_neg hi,rowInput_silent j (by omega)]
      exact hsilent j



def mergeMap (n m : Nat) (u : Fin n) (i : Nat) : Nat :=
  if i<n then (if i=u.val then (n+1)+m else i)
  else if i<n+m then i+1 else i+2

def mergeGate {n : Nat} (u : Fin n) : Gate := ⟨GateOp.or,[u.val,n]⟩

def mergeCircuit {n : Nat} (m : Nat) (u : Fin n) (C : Circuit) : Circuit :=
  ⟨mergeGate u::C.gates.map (relabel (mergeMap n m u)),mergeMap n m u C.output⟩

def mergeStart {n m : Nat} (u : Fin n) (r : Nat) (j : Fin m) : List Bool :=
  rowInput (n+1) r j++[decide (u.val=r)||decide (n=r)]

lemma mergeStart_length {n m : Nat} (u : Fin n) (r : Nat) (j : Fin m) :
    (mergeStart u r j).length=n+m+2 := by simp [mergeStart,rowInput_length];omega

lemma mergeStart_lookup {n m : Nat} (u : Fin n) (r : Nat) (hr : r<n+1) (j : Fin m)
    (i : Nat) (hi : i<n+m) :
    (mergeStart u r j).getD (mergeMap n m u i) false=
      (rowInput n (if r<n then r else u.val) j).getD i false := by
  by_cases hin : i<n
  · by_cases hiu : i=u.val
    · subst i
      have start : (mergeStart u r j).getD ((n+1)+m) false=
          (decide (u.val=r)||decide (n=r)) := by
        simpa only [mergeStart,rowInput_length] using
          (getD_snoc_eq (rowInput (n+1) r j) (decide (u.val=r)||decide (n=r)) false)
      rw [mergeMap,if_pos u.isLt,if_pos rfl,start,rowInput_getD,if_pos u.isLt]
      by_cases hrn : r<n
      · simp [hrn,show n≠r by omega]
      · have re : r=n := by omega
        simp [hrn,re]
    · rw [mergeMap,if_pos hin,if_neg hiu]
      unfold mergeStart
      rw [List.getD_append _ _ _ _ (by rw [rowInput_length];omega),
        rowInput_getD,rowInput_getD,if_pos (by omega),if_pos hin]
      by_cases hrn : r<n
      · simp [hrn]
      · simp [hrn,show i≠r by omega,hiu]
  · rw [mergeMap,if_neg hin,if_pos hi]
    unfold mergeStart
    rw [List.getD_append _ _ _ _ (by rw [rowInput_length];omega),
      rowInput_getD,rowInput_getD,if_neg (by omega),if_neg hin]
    apply decide_eq_decide.mpr
    omega

lemma merge_eval {n m : Nat} (C : Circuit) (u : Fin n) (r : Nat) (hr : r<n+1) (j : Fin m) :
    (mergeCircuit m u C).eval (rowInput (n+1) r j)=
      C.eval (rowInput n (if r<n then r else u.val) j) := by
  change (run (mergeGate u::C.gates.map (relabel (mergeMap n m u)))
      (rowInput (n+1) r j)).getD (mergeMap n m u C.output) false=
    (run C.gates (rowInput n (if r<n then r else u.val) j)).getD C.output false
  rw [run_cons]
  have gateval : (mergeGate u).op.eval
      ((mergeGate u).inputs.map (fun i=>(rowInput (n+1) r j).getD i false))=
        (decide (u.val=r)||decide (n=r)) := by
    simp only [mergeGate,GateOp.eval,List.map_cons,List.map_nil,
      List.any_cons,List.any_nil,id_eq,Bool.or_false]
    rw [rowInput_getD,rowInput_getD]
    simp [show u.val<n+1 by omega]
  rw [gateval]
  change (run (C.gates.map (relabel (mergeMap n m u))) (mergeStart u r j)).getD
      (mergeMap n m u C.output) false=_
  apply relabel_sim
  · intro i hi
    apply mergeStart_lookup u r hr j i
    simpa only [rowInput_length] using hi
  · intro i hi
    simp only [rowInput_length,mergeStart_length] at hi ⊢
    left
    by_cases hin : i<n
    · by_cases hiu : i=u.val <;> simp [mergeMap,hin,hiu] <;> omega
    · simp [mergeMap,hin,hi];omega
  · intro k hk
    simp only [rowInput_length,mergeStart_length]
    rw [mergeMap,if_neg (by omega),if_neg (by omega)]
    omega
  · intro i hi
    simp only [rowInput_length,mergeStart_length] at hi ⊢
    rw [mergeMap,if_neg (by omega),if_neg (by omega)]
    omega

lemma merge_monotone {n m : Nat} (C : Circuit) (u : Fin n) (mono : Monotone2 C) :
    Monotone2 (mergeCircuit m u C) := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl|hg
  · simp [mergeGate]
  · exact relabel_monotone (mergeMap n m u) C mono g hg


theorem one_copy_upper {n m b : Nat} (A : Fin n→Fin m→Bool) (u : Fin n)
    (rep : RepSizeAtMost A b) :
    RepSizeAtMost
      (fun i : Fin (n+1)=>fun j=>if h : i.val<n then A ⟨i.val,h⟩ j else A u j) (b+1) := by
  obtain ⟨C,mono,size,repC⟩ := rep
  refine ⟨mergeCircuit m u C,merge_monotone C u mono,?_,?_⟩
  · simpa [mergeCircuit,Circuit.size] using Nat.add_le_add_right size 1
  · intro i j
    rw [←rowInput_oneEach,merge_eval C u i.val i.isLt j]
    change C.eval (rowInput n (if i.val<n then i.val else u.val) j)=
      (if h : i.val<n then A ⟨i.val,h⟩ j else A u j)
    by_cases hin : i.val<n
    · rw [if_pos hin,dif_pos hin,rowInput_oneEach (⟨i.val,hin⟩ : Fin n) j]
      exact repC _ _
    · rw [if_neg hin,dif_neg hin,rowInput_oneEach u j]
      exact repC _ _

def expanded {n m : Nat} (A : Fin n→Fin m→Bool) (u : Fin n) (t : Nat) :
    Fin (n+t)→Fin m→Bool :=
  fun i j=>if h : i.val<n then A ⟨i.val,h⟩ j else A u j

lemma expanded_zero {n m : Nat} (A : Fin n→Fin m→Bool) (u : Fin n) :
    expanded A u 0=A := by
  funext i j
  simp [expanded,i.isLt]

lemma expanded_step {n m : Nat} (A : Fin n→Fin m→Bool) (u : Fin n) (t : Nat) :
    (fun i : Fin ((n+t)+1)=>fun j=>if h : i.val<n+t then
      expanded A u t ⟨i.val,h⟩ j else expanded A u t ⟨u.val,by omega⟩ j)=
      expanded A u (t+1) := by
  funext i j
  by_cases hin : i.val<n
  · simp [expanded,hin,show i.val<n+t by omega]
  · by_cases hit : i.val<n+t
    · simp [expanded,hit,hin]
    · simp [expanded,hit,hin,u.isLt]


theorem copies_upper {n m b : Nat} (A : Fin n→Fin m→Bool) (u : Fin n)
    (rep : RepSizeAtMost A b) (t : Nat) :
    RepSizeAtMost (expanded A u t) (b+t) := by
  induction t with
  | zero => simpa only [expanded_zero,Nat.add_zero] using rep
  | succ t ih =>
    have next := one_copy_upper (expanded A u t) (⟨u.val,by omega⟩ : Fin (n+t)) ih
    rw [expanded_step] at next
    simpa only [Nat.add_assoc] using next


theorem upper {n m : Nat} (A : Fin n→Fin m→Bool) (u : Fin n) (t s : Nat)
    (bound : (∃b : Nat,b+t≤ s ∧ RepSizeAtMost A b) ∨
      (∃C : Circuit,Monotone2 C ∧ C.size≤ s ∧ Represents A C ∧
        ∀j : Fin m,C.eval (List.replicate n false++List.ofFn (fun v : Fin m=>decide (v=j)))=A u j)) :
    RepSizeAtMost (expanded A u t) s := by
  rcases bound with ⟨b,size,rep⟩|silent
  · obtain ⟨C,mono,hsize,hrep⟩ := copies_upper A u rep t
    exact ⟨C,mono,hsize.trans size,hrep⟩
  · exact silent_upper A u t s silent

end Meta27803Upper

end PEqualNP.Outside.L_meta_27803_aux

set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.L_meta_27803 : (∀ (n m : Nat) (A : Fin n → Fin m → Bool) (u : Fin n),
  (∃ i j, A i j = false) →
  ∀ (t s : Nat),
    let expanded := fun (i : Fin (n + t)) (j : Fin m) =>
      if h : i.val < n then A ⟨i.val, h⟩ j else A u j
    let silent := ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ PEqualNP.Represents.Represents A C ∧
      ∀ j : Fin m,
        C.eval (List.replicate n false ++ List.ofFn (fun v : Fin m => decide (v = j))) = A u j
    PEqualNP.Represents.RepSizeAtMost expanded s ↔
      (∃ b : Nat, b + t ≤ s ∧ PEqualNP.Represents.RepSizeAtMost A b) ∨ silent) := by
  intro n m A u hasZero t s
  exact ⟨PEqualNP.Outside.L_meta_27803_aux.Meta27803Lower.lower_from_removeLast
    PEqualNP.Outside.L_meta_27803_aux.Meta27803Delete.remove_last_row n m A u hasZero t s,
    PEqualNP.Outside.L_meta_27803_aux.Meta27803Upper.upper A u t s⟩
