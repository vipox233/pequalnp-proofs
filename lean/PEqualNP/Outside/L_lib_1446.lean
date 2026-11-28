import PEqualNP.Defs
import Mathlib.Data.Fintype.Fin

namespace PEqualNP.Outside.L_lib_1446

def band (r a b : Nat) : Finset (Fin r) := Finset.univ.filter fun i => a ≤ i.val ∧ i.val < b

def seg (r B u v : Nat) : Finset (Fin r) := band r 0 u ∪ band r B (B+v)

lemma band_card {r a b : Nat} (hab : a ≤ b) (hbr : b ≤ r) : (band r a b).card = b-a := by
  let pref := fun t : Nat => Finset.univ.filter (fun i : Fin r => i.val < t)
  have sub : pref a ⊆ pref b := by intro i hi; simpa [pref] using (show i.val < b from lt_of_lt_of_le (by simpa [pref] using hi) hab)
  have eq : band r a b = pref b \ pref a := by ext i; simp [band,pref]; omega
  rw [eq,Finset.card_sdiff_of_subset sub]
  simp only [pref,Fin.card_filter_val_lt]
  omega

lemma seg_form (r B u v : Nat) : seg r B u v = Finset.univ.filter (fun i : Fin r => i.val < u ∨ B ≤ i.val ∧ i.val < B+v) := by
  ext i; simp [seg,band]

lemma seg_mono {r B u v u' v' : Nat} (h : u ≤ u') (h' : v ≤ v') : seg r B u v ⊆ seg r B u' v' := by
  intro i hi
  simp [seg,band] at hi ⊢
  omega

lemma seg_diff {r B u v u' v' : Nat} (hu : u ≤ B) (hu' : u' ≤ B) (hv : B+v ≤ r) :
    (seg r B u v \ seg r B u' v').card = (u-u')+(v-v') := by
  have eq : seg r B u v \ seg r B u' v' = band r (min u u') u ∪ band r (B+min v v') (B+v) := by
    ext i; simp [seg,band]; omega
  have dis : Disjoint (band r (min u u') u) (band r (B+min v v') (B+v)) := by
    rw [Finset.disjoint_left]; intro i h1 h2; simp [band] at h1 h2; omega
  rw [eq, Finset.card_union_of_disjoint dis, band_card (by omega) (by omega),band_card (by omega) hv]
  omega

lemma pert_low {r B u v A F a f : Nat} (hB : u ≤ B) (hr : B+v+F ≤ r)
    (hA : A ≤ a) (hF : F ≤ f) :
    let X := seg r B u v
    let Y := seg r B (u-A) (v+F)
    (X \ Y).card ≤ a ∧ (Y \ X).card ≤ f := by
  dsimp only
  rw [seg_diff hB (by omega) (by omega),seg_diff (by omega) hB (by omega)]
  omega

lemma pert_high {r B u v A F a f : Nat} (hB : u+F ≤ B) (hr : B+v ≤ r)
    (hA : A ≤ a) (hF : F ≤ f) :
    let X := seg r B u v
    let Y := seg r B (u+F) (v-A)
    (X \ Y).card ≤ a ∧ (Y \ X).card ≤ f := by
  dsimp only
  rw [seg_diff (by omega) hB hr,seg_diff hB (by omega) (by omega)]
  omega

lemma bridge_low_high {r B i q d t A F : Nat} (hs : A+F=q) (hd : q+d=t) :
    seg r B ((i+1)*q-A) ((i+1)*d+F) ⊆ seg r B (i*q+F) ((i+1)*d+t-A) := by
  apply seg_mono <;> simp only [Nat.add_mul,Nat.one_mul] <;> omega

lemma bridge_high_low {r B i q d t A F : Nat} (hs : A+F=q) (hd : q+d=t) :
    seg r B (i*q+F) ((i+1)*d+t-A) ⊆ seg r B ((i+2)*q-A) ((i+2)*d+F) := by
  apply seg_mono <;> simp only [Nat.add_mul,Nat.one_mul,Nat.two_mul] <;> omega

lemma split_noise {a f t d : Nat} (ht : t=a+f+1) (hd : 0<d) (hd' : d ≤ t) :
    ∃ A F : Nat, A ≤ a ∧ F ≤ f ∧ A+F=t-d := by
  refine ⟨min a (t-d), (t-d)-min a (t-d), ?_, ?_, ?_⟩ <;> omega

end PEqualNP.Outside.L_lib_1446

namespace PEqualNP.Outside.L_lib_1446.Driver

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.NotBracket (notCount)

private abbrev Allowed (g : Gate) : Prop :=
  g.op = .and ∨ g.op = .or ∨ g.op = .not

private def bitOrder (x y : List Bool) : Prop :=
  x.length = y.length ∧ ∀ i, x.getD i false ≤ y.getD i false

private theorem bool_order (a b : Bool) : a ≤ b ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

private theorem bool_digit (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide

private theorem digit_order {a b : Bool} (ab : a ≤ b) : a.toNat ≤ b.toNat := by
  cases a <;> cases b <;> simp_all [bool_order]

private theorem digit_inj {a b : Bool} (eq : a.toNat = b.toNat) : a = b := by
  cases a <;> cases b <;> simp_all

private theorem order_append {x y : List Bool} (ordered : bitOrder x y) {a b : Bool} (ab : a ≤ b) :
    bitOrder (x ++ [a]) (y ++ [b]) := by
  refine ⟨by simp [ordered.1],?_⟩
  intro i
  rcases lt_trichotomy i x.length with lt | eq | gt
  · have ly : i < y.length := ordered.1 ▸ lt
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_append_left lt,
      List.getElem?_append_left ly] using ordered.2 i
  · subst i
    simpa [List.getD_eq_getElem?_getD,ordered.1] using ab
  · have noneX : (x ++ [a]).length ≤ i := by simp; omega
    have noneY : (y ++ [b]).length ≤ i := by simp [← ordered.1]; omega
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none noneX,List.getElem?_eq_none noneY]

private def incoming (g : Gate) (w : List Bool) : List Bool :=
  g.inputs.map (fun i => w.getD i false)

private def outputBit (g : Gate) (w : List Bool) : Bool := g.op.eval (incoming g w)

private def firstBit (g : Gate) (w : List Bool) : Bool := (incoming g w).headD false

private theorem first_order (g : Gate) {x y : List Bool} (ordered : bitOrder x y) :
    firstBit g x ≤ firstBit g y := by
  unfold firstBit incoming
  cases h : g.inputs with
  | nil => simp
  | cons i rest => exact ordered.2 i

private theorem and_order {g : Gate} (op : g.op = .and) {x y : List Bool} (ordered : bitOrder x y) :
    outputBit g x ≤ outputBit g y := by
  apply (bool_order _ _).mpr
  intro on
  simp only [outputBit,op,GateOp.eval,List.all_eq_true] at on ⊢
  intro v hm
  obtain ⟨i,here,rfl⟩ := List.mem_map.mp hm
  exact (bool_order _ _).mp (ordered.2 i) (on _ (List.mem_map.mpr ⟨i,here,rfl⟩))

private theorem or_order {g : Gate} (op : g.op = .or) {x y : List Bool} (ordered : bitOrder x y) :
    outputBit g x ≤ outputBit g y := by
  apply (bool_order _ _).mpr
  intro on
  simp only [outputBit,op,GateOp.eval,List.any_eq_true] at on ⊢
  obtain ⟨v,hm,active⟩ := on
  obtain ⟨i,here,rfl⟩ := List.mem_map.mp hm
  exact ⟨_,List.mem_map.mpr ⟨i,here,rfl⟩,(bool_order _ _).mp (ordered.2 i) active⟩

private def inverting (g : Gate) : Bool :=
  match g.op with | .not => true | _ => false

private def advance (s : List Bool × ℕ) (g : Gate) : List Bool × ℕ :=
  (s.1 ++ [outputBit g s.1],if inverting g then 2*s.2+(firstBit g s.1).toNat else s.2)

private def consistent (s t : List Bool × ℕ) : Prop :=
  s.2 ≤ t.2 ∧ (s.2 = t.2 → bitOrder s.1 t.1)

private theorem advance_consistent {s t : List Bool × ℕ} {g : Gate} (allowed : Allowed g)
    (before : consistent s t) : consistent (advance s g) (advance t g) := by
  by_cases strict : s.2 < t.2
  · have increase : (advance s g).2 < (advance t g).2 := by
      by_cases neg : inverting g = true
      · simp only [advance,neg,ite_true]
        have bit := bool_digit (firstBit g s.1)
        omega
      · simpa [advance,neg] using strict
    exact ⟨increase.le,fun eq => (increase.ne eq).elim⟩
  have eq : s.2 = t.2 := Nat.le_antisymm before.1 (Nat.le_of_not_gt strict)
  have ordered := before.2 eq
  rcases allowed with op | op | op
  · simp only [consistent,advance,inverting,op,Bool.false_eq_true,ite_false]
    exact ⟨before.1,fun _ => order_append ordered (and_order op ordered)⟩
  · simp only [consistent,advance,inverting,op,Bool.false_eq_true,ite_false]
    exact ⟨before.1,fun _ => order_append ordered (or_order op ordered)⟩
  · simp only [consistent,advance,inverting,op,ite_true]
    have order := digit_order (first_order g ordered)
    refine ⟨by omega,?_⟩
    intro next
    have sameDigit : (firstBit g s.1).toNat = (firstBit g t.1).toNat := by omega
    have sameBit := digit_inj sameDigit
    apply order_append ordered
    simp only [outputBit,op,GateOp.eval]
    change (!firstBit g s.1) ≤ (!firstBit g t.1)
    rw [sameBit]

private def negCount (gates : List Gate) : ℕ := (gates.filter inverting).length

private theorem negCount_spec (C : Circuit) : negCount C.gates = notCount C := by
  classical
  unfold negCount notCount
  congr 2
  funext g
  cases h : g.op <;> simp [inverting,h]

private theorem run_consistent (gates : List Gate) (allowed : ∀ g ∈ gates, Allowed g)
    {s t : List Bool × ℕ} (before : consistent s t) :
    consistent (gates.foldl advance s) (gates.foldl advance t) := by
  induction gates generalizing s t with
  | nil => exact before
  | cons g rest ih =>
    exact ih (fun k hm => allowed k (List.mem_cons_of_mem _ hm))
      (advance_consistent (allowed g (List.mem_cons_self ..)) before)

private theorem run_bounded (gates : List Gate) (s : List Bool × ℕ) (d : ℕ) (bound : s.2 < 2^d) :
    (gates.foldl advance s).2 < 2^(d+negCount gates) := by
  induction gates generalizing s d with
  | nil => simpa [negCount] using bound
  | cons g rest ih =>
    by_cases neg : inverting g = true
    · have raises : (advance s g).2 < 2^(d+1) := by
        simp only [advance,neg,ite_true,Nat.pow_succ]
        have digit := bool_digit (firstBit g s.1)
        omega
      have next := ih (advance s g) (d+1) raises
      simpa [negCount,neg,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using next
    · have same : (advance s g).2 < 2^d := by simpa [advance,neg] using bound
      simpa [negCount,neg] using ih (advance s g) d same

private theorem run_wires (gates : List Gate) (s : List Bool × ℕ) :
    (gates.foldl advance s).1 =
      gates.foldl (fun w g => w ++ [outputBit g w]) s.1 := by
  induction gates generalizing s with
  | nil => rfl
  | cons g rest ih => exact ih (advance s g)

private theorem inputs_order {n : ℕ} {x y : Fin n → Bool} (xy : x ≤ y) :
    bitOrder (List.ofFn x ++ [false,true]) (List.ofFn y ++ [false,true]) := by
  have first : bitOrder (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp,?_⟩
    intro i
    by_cases inside : i < n
    · simpa [List.getD_eq_getElem?_getD,List.getElem?_ofFn,inside] using xy ⟨i,inside⟩
    · simp [List.getD_eq_getElem?_getD,List.getElem?_ofFn,inside]
  simpa only [List.append_assoc,List.singleton_append] using
    order_append (order_append first (a := false) (b := false) le_rfl)
      (a := true) (b := true) le_rfl

def grade {n : ℕ} (C : Circuit) (x : Fin n → Bool) : ℕ :=
  (C.gates.foldl advance (List.ofFn x ++ [false,true],0)).2

theorem grade_bound {n : ℕ} (C : Circuit) (x : Fin n → Bool) : grade C x < 2^(notCount C) := by
  simpa [grade,negCount_spec] using
    run_bounded C.gates (List.ofFn x ++ [false,true],0) 0 (by change 0 < 1; decide)

theorem grade_order {n : ℕ} {C : Circuit} (basis : FanInTwo C) {x y : Fin n → Bool} (xy : x ≤ y) :
    grade C x ≤ grade C y ∧ (grade C x = grade C y → ∀ i,
      (C.wires (List.ofFn x ++ [false,true])).getD i false ≤
        (C.wires (List.ofFn y ++ [false,true])).getD i false) := by
  have allowed (g) (mem : g ∈ C.gates) : Allowed g := by
    simpa [Allowed] using (basis g mem).1
  have initial : consistent (List.ofFn x ++ [false,true],0) (List.ofFn y ++ [false,true],0) :=
    ⟨le_rfl,fun _ => inputs_order xy⟩
  have result := run_consistent C.gates allowed initial
  refine ⟨result.1,?_⟩
  intro eq
  have order := (result.2 eq).2
  rw [run_wires,run_wires] at order
  exact order

theorem grade_fall {n : ℕ} {C : Circuit} (basis : FanInTwo C) {x y : Fin n → Bool}
    (xy : x ≤ y) (i : ℕ)
    (before : (C.wires (List.ofFn x ++ [false,true])).getD i false = true)
    (after : (C.wires (List.ofFn y ++ [false,true])).getD i false = false) :
    grade C x < grade C y := by
  obtain ⟨order,read⟩ := grade_order basis xy
  refine lt_of_le_of_ne order ?_
  intro eq
  have impossible := read eq i
  rw [before,after] at impossible
  exact (by decide : ¬ (true ≤ false)) impossible

end PEqualNP.Outside.L_lib_1446.Driver

namespace PEqualNP.Outside.L_lib_1446.Tape
open PEqualNP.CircuitLowerBounds
def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = run C.gates x := rfl

theorem run_append (a b : List Gate) (w : List Bool) : run (a ++ b) w = run b (run a w) := by
  unfold run; rw [List.foldl_append]

theorem run_nil (w : List Bool) : run [] w = w := rfl

theorem run_singleton (g : Gate) (w : List Bool) :
    run [g] w = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := rfl

theorem run_prefix (gs : List Gate) :
    ∀ w : List Bool, ∃ t, run gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [run]⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, ?_⟩
    · rw [show g :: gs = [g] ++ gs from rfl, run_append, run_singleton, ht]; simp
    · simp [hl]

theorem run_length (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := run_prefix gs w
  rw [ht, List.length_append, hl]

theorem getD_run (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := run_prefix gs w
  rw [ht]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_snoc_length (l : List Bool) (a : Bool) : (l ++ [a]).getD l.length false = a := by
  simp

theorem eval_or2 (a b : Bool) : GateOp.eval GateOp.or [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

theorem eval_and2 (a b : Bool) : GateOp.eval GateOp.and [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

end PEqualNP.Outside.L_lib_1446.Tape

namespace PEqualNP.Outside.L_lib_1446.Bank

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_lib_1446.Tape (run run_length run_append run_singleton)

open Classical

variable {X J : Type} {n : Nat}

structure Net (n : Nat) where
  gates : List Gate
  fan : FanInTwo ⟨gates,0⟩
  back : ∀ j (hj : j < gates.length), ∀ i ∈ gates[j].inputs, i < n+j

def empty (n : Nat) : Net n := ⟨[],by simp [FanInTwo],by simp⟩

def Net.cost (p : Net n) := NotBracket.notCount ⟨p.gates,0⟩

def Net.has (p : Net n) (raw : X → List Bool) (f : X → Bool) :=
  ∃ i, i < n+p.gates.length ∧ ∀ x, (run p.gates (raw x)).getD i false = f x

def Grow (raw : X → List Bool) (p q : Net n) (size neg : Nat) : Prop :=
  (∀ f, p.has raw f → q.has raw f) ∧ q.gates.length ≤ p.gates.length+size ∧ q.cost=p.cost+neg

theorem start (raw : X → List Bool) (p : Net n) : Grow raw p p 0 0 := by simp [Grow]

theorem chain {raw : X → List Bool} {p q r : Net n} {a b c d : Nat}
    (pq : Grow raw p q a b) (qr : Grow raw q r c d) : Grow raw p r (a+c) (b+d) :=
  ⟨fun f h => qr.1 f (pq.1 f h),by have := pq.2.1; have := qr.2.1; omega,
    by rw [qr.2.2,pq.2.2,Nat.add_assoc]⟩

theorem allowance {raw : X → List Bool} {p q : Net n} {a b c : Nat}
    (grow : Grow raw p q a b) (le : a≤c) : Grow raw p q c b :=
  ⟨grow.1,grow.2.1.trans (Nat.add_le_add_left le _),grow.2.2⟩

private def extend (p : Net n) (g : Gate)
    (ops : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (ok : ∀ i ∈ g.inputs, i < n+p.gates.length) : Net n where
  gates := p.gates++[g]
  fan := by
    intro v hv
    rcases List.mem_append.mp hv with old | last
    · exact p.fan v old
    · exact (List.mem_singleton.mp last) ▸ ops
  back := by
    intro j hj i hi
    by_cases h : j < p.gates.length
    · rw [List.getElem_append_left h] at hi
      exact p.back j h i hi
    · have len : j=p.gates.length := by simp at hj; omega
      subst j
      simp at hi
      exact ok i hi

private theorem emit {raw : X → List Bool} (width : ∀ x, (raw x).length=n)
    (p : Net n) (g : Gate)
    (ops : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (ok : ∀ i ∈ g.inputs, i < n+p.gates.length) :
    ∃ q, Grow raw p q 1 (if g.op=.not then 1 else 0) ∧
      q.has raw (fun x => g.op.eval (g.inputs.map (fun i => (run p.gates (raw x)).getD i false))) := by
  let q := extend p g ops ok
  have len (x : X) : (run p.gates (raw x)).length=n+p.gates.length := by rw [run_length,width]
  refine ⟨q,⟨?_,by simp [q,extend],?_⟩,n+p.gates.length,by simp [q,extend],?_⟩
  · rintro f ⟨i,hi,read⟩
    refine ⟨i,by simp [q,extend]; omega,?_⟩
    intro x
    change (run (p.gates++[g]) (raw x)).getD i false = _
    rw [run_append,run_singleton,List.getD_append _ _ _ _ ((len x).symm ▸ hi),read]
  · unfold Net.cost NotBracket.notCount
    simp only [q,extend,List.filter_append,List.length_append]
    split <;> simp_all
  · intro x
    change (run (p.gates++[g]) (raw x)).getD (n+p.gates.length) false = _
    rw [run_append,run_singleton,←len x]; simp

theorem binary {raw : X → List Bool} (width : ∀ x, (raw x).length=n)
    (p : Net n) (a b : X → Bool) (ha : p.has raw a) (hb : p.has raw b) (isAnd : Bool) :
    ∃ q, Grow raw p q 1 0 ∧ q.has raw (fun x => if isAnd then a x && b x else a x || b x) := by
  obtain ⟨i,hi,readI⟩ := ha
  obtain ⟨j,hj,readJ⟩ := hb
  let g : Gate := ⟨if isAnd then .and else .or,[i,j]⟩
  obtain ⟨q,grow,w⟩ := emit width p g (by cases isAnd <;> simp [g]) (by simp [g,hi,hj])
  refine ⟨q,by cases isAnd <;> simpa [g] using grow,?_⟩
  convert w using 2 with x
  cases isAnd <;> simp only [g,Bool.false_eq_true,ite_false,ite_true,List.map_cons,List.map_nil,
    PEqualNP.Outside.L_lib_1446.Tape.eval_and2,PEqualNP.Outside.L_lib_1446.Tape.eval_or2, readI,readJ] <;> rfl

theorem invert {raw : X → List Bool} (width : ∀ x, (raw x).length=n)
    (p : Net n) (a : X → Bool) (ha : p.has raw a) :
    ∃ q, Grow raw p q 1 1 ∧ q.has raw (fun x => !(a x)) := by
  obtain ⟨i,hi,readI⟩ := ha
  let g : Gate := ⟨.not,[i]⟩
  obtain ⟨q,grow,w⟩ := emit width p g (by simp [g]) (by simp [g,hi])
  refine ⟨q,by simpa [g] using grow,?_⟩
  convert w using 2 with x
  change (!(a x)) = (!((run p.gates (raw x)).getD i false))
  rw [readI]

theorem anyList {raw : X → List Bool} (width : ∀ x, (raw x).length=n) (p : Net n)
    (zero : p.has raw (fun _ => false)) (l : List J) (f : J → X → Bool)
    (known : ∀ i ∈ l, p.has raw (f i)) :
    ∃ q, Grow raw p q l.length 0 ∧ q.has raw (fun x => l.any (fun j => f j x)) := by
  induction l with
  | nil => exact ⟨p,start _ _,zero⟩
  | cons j l ih =>
    obtain ⟨q,gq,old⟩ := ih (fun i hi => known i (by simp [hi]))
    obtain ⟨r,gr,ans⟩ := binary width q _ _ (gq.1 _ (known j (by simp))) old false
    exact ⟨r,chain gq gr,by simpa [List.any_cons] using ans⟩

theorem batch {raw : X → List Bool} (p : Net n) (l : List J) (f : J → X → Bool) (s z : Nat)
    (build : ∀ j ∈ l, ∀ q : Net n, (∀ a, p.has raw a → q.has raw a) →
      ∃ r, Grow raw q r s z ∧ r.has raw (f j)) :
    ∃ r, Grow raw p r (l.length*s) (l.length*z) ∧ ∀ j ∈ l, r.has raw (f j) := by
  induction l with
  | nil => exact ⟨p,by simpa using start raw p,by simp⟩
  | cons j l ih =>
    obtain ⟨q,gq,old⟩ := ih (fun i hi => build i (by simp [hi]))
    obtain ⟨r,gr,ans⟩ := build j (by simp) q gq.1
    refine ⟨r,by simpa [Nat.succ_mul] using chain gq gr,?_⟩
    intro i mem
    rcases List.mem_cons.mp mem with rfl | h
    · exact ans
    · exact gr.1 _ (old i h)

theorem Net.readsBack (p : Net n) : ReadsBack n ⟨p.gates,0⟩ := by
  intro j hj i hi
  exact p.back j hj i (by simpa [gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj] using hi)

end PEqualNP.Outside.L_lib_1446.Bank

namespace PEqualNP.Outside.L_lib_1446.Sorted

open PEqualNP.Outside.L_lib_1446.Bank

variable {X : Type} {n : Nat}

def high (r : X → Nat) (i : Nat) (x : X) := decide (i ≤ r x)
def low (r : X → Nat) (i : Nat) (x : X) := decide (r x < i)

theorem decode (raw : X → List Bool) (width : ∀ x, (raw x).length=n) (b k : Nat)
    (room : k < 2^b) (r : X → Nat) (bound : ∀ x, r x≤k) (p : Net n)
    (zero : p.has raw (fun _ => false)) (known : ∀ i : Nat, 0 < i → i ≤ k → p.has raw (high r i)) :
    ∃ q, Grow raw p q (4*k+b) b ∧ ∀ i : Nat, 0 < i → i ≤ k → q.has raw (low r i) := by
  induction b generalizing k r p with
  | zero =>
    have : k=0 := by simpa using room
    subst k
    exact ⟨p,by simpa using start raw p,by omega⟩
  | succ b ih =>
    let a := k/2
    let m := a+1
    let rem (x : X) := if r x < m then r x else r x-m
    have small : k < 2*m := by dsimp [m,a]; omega
    have rem_le (x) : rem x≤a := by
      have := bound x
      dsimp [rem,m,a] at *
      split <;> omega
    have limited : a < 2^b := by dsimp [a]; rw [pow_succ] at room; omega
    have avail (i) (pos : 0 < i) : p.has raw (high r i) := by
      by_cases le : i≤k
      · exact known i pos le
      · convert zero using 2 with x
        simp [high,show ¬i≤r x by have := bound x; omega]
    obtain ⟨p₁,g₁,hneg⟩ := invert width p (high r m) (avail m (by dsimp [m]; omega))
    let ids := List.range a
    obtain ⟨p₂,g₂,hrem⟩ := batch (raw:=raw) p₁ ids (fun j => high rem (j+1)) 2 0 (by
      intro j hj q keep
      have index : j < a := List.mem_range.mp hj
      obtain ⟨u,gu,band⟩ := binary width q _ _ (keep _ hneg) (keep _ (g₁.1 _ (avail (j+1) (by omega)))) true
      obtain ⟨v,gv,bor⟩ := binary width u _ _ band (gu.1 _ (keep _ (g₁.1 _ (avail (m+(j+1)) (by omega))))) false
      refine ⟨v,chain gu gv,?_⟩
      convert bor using 2 with x
      have := bound x
      apply Bool.eq_iff_iff.mpr
      simp only [high,rem,Bool.or_eq_true,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq,
        decide_eq_false_iff_not,ite_true,ite_false,Bool.false_eq_true]
      dsimp [m] at *
      split <;> omega)
    have residual (i) (pos : 0 < i) (le : i≤a) : p₂.has raw (high rem i) := by
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i≠0)
      exact hrem j (List.mem_range.mpr (by omega))
    obtain ⟨p₃,g₃,remneg⟩ := ih a limited rem rem_le p₂ (g₂.1 _ (g₁.1 _ zero)) residual
    have g123 := chain (chain g₁ g₂) g₃
    have mid := g₃.1 _ (g₂.1 _ hneg)
    obtain ⟨q,g₄,outs⟩ := batch (raw:=raw) p₃ (List.range k) (fun j => low r (j+1)) 1 0 (by
      intro j hj u keep
      have jk : j < k := List.mem_range.mp hj
      by_cases below : j+1 < m
      · have le : j+1≤a := by dsimp [m] at below; omega
        obtain ⟨v,g,h⟩ := binary width u _ _ (keep _ mid) (keep _ (remneg (j+1) (by omega) le)) true
        refine ⟨v,g,?_⟩
        convert h using 2 with x
        apply Bool.eq_iff_iff.mpr
        simp only [low,high,rem,ite_true,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq,decide_eq_false_iff_not]
        split <;> omega
      · by_cases eq : j+1=m
        · refine ⟨u,allowance (start raw u) (by decide : 0≤1),?_⟩
          convert keep _ mid using 2 with x
          apply Bool.eq_iff_iff.mpr
          simp only [high,low,Bool.not_eq_true',decide_eq_true_eq,decide_eq_false_iff_not]
          omega
        · have above : m < j+1 := by omega
          have ix : j+1-m≤a := by dsimp [m,a] at *; omega
          obtain ⟨v,g,h⟩ := binary width u _ _ (keep _ mid) (keep _ (remneg (j+1-m) (by omega) ix)) false
          refine ⟨v,g,?_⟩
          convert h using 2 with x
          apply Bool.eq_iff_iff.mpr
          simp only [low,high,rem,Bool.false_eq_true,ite_false,Bool.or_eq_true,Bool.not_eq_true',decide_eq_true_eq,decide_eq_false_iff_not]
          split <;> omega)
    have gr := chain g123 g₄
    simp only [ids,List.length_range,Nat.mul_zero,Nat.add_zero,Nat.mul_one] at gr
    refine ⟨q,?_,?_⟩
    · have gr' := allowance gr (show 1 + a*2 + (4*a+b) + k ≤ 4*k+(b+1) by dsimp [a]; omega)
      simpa [Nat.add_comm 1 b] using gr'
    · intro i pos le
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i≠0)
      exact outs j (List.mem_range.mpr (by omega))

end PEqualNP.Outside.L_lib_1446.Sorted

namespace PEqualNP.Outside.L_lib_1446

structure Grid where
  L : Nat
  t : Nat
  d : Nat
  q : Nat
  A : Nat
  F : Nat
  pos : 0 < L
  sumq : q+d=t
  half : d≤q
  split : A+F=q

namespace Grid

variable (G : Grid)

def B := G.L*G.q
def width := (G.L+1)*G.t+G.d
def K := 2*G.L+1

def height (s : Nat) := if s=0 then 0 else if s=G.K then G.L else if s%2=1 then (s+1)/2 else (s-2)/2
def upper (s : Nat) := s≠0 ∧ (s%2=0 ∨ s=G.K)
instance (s : Nat) : Decidable (G.upper s) := by unfold upper; infer_instance

def raw (s : Nat) := Finset.univ.filter (fun i : Fin (G.L+1) => i.val<G.height s ∨ i.val=G.L ∧ G.upper s)
def W (s : Nat) := seg G.width G.B (G.height s*G.q) (G.height s*G.d+(if G.upper s then G.t+G.d else 0))
def Y (s : Nat) := if s=0 ∨ s=G.K then G.W s else if G.upper s then
    seg G.width G.B (G.height s*G.q+G.F) (G.height s*G.d+G.t+G.d-G.A)
  else seg G.width G.B (G.height s*G.q-G.A) (G.height s*G.d+G.F)

lemma width_eq : G.width=G.B+G.L*G.d+G.t+G.d := by
  unfold width B; rw [←G.sumq]; ring

lemma height_zero : G.height 0=0 := by simp [height]
lemma upper_zero : ¬G.upper 0 := by simp [upper]
lemma height_end : G.height G.K=G.L := by simp [height,K]
lemma upper_end : G.upper G.K := by simp [upper,K]
lemma height_low {i : Nat} (hi : i<G.L) : G.height (2*i+1)=i+1 := by
  unfold height K; split_ifs <;> omega
lemma height_high {i : Nat} (_hi : i<G.L) : G.height (2*i+2)=i := by
  rw [height,if_neg (by omega),if_neg (by unfold K; omega),if_neg (by omega),Nat.add_sub_cancel]
  exact Nat.mul_div_cancel_left i (by decide : 0 < 2)
lemma upper_low {i : Nat} (hi : i<G.L) : ¬G.upper (2*i+1) := by unfold upper K; omega
lemma upper_high {i : Nat} : G.upper (2*i+2) := by unfold upper K; omega

lemma w_zero : G.W 0=seg G.width G.B 0 0 := by simp [W,G.height_zero,G.upper_zero]
lemma w_end : G.W G.K=seg G.width G.B G.B (G.L*G.d+G.t+G.d) := by
  simp [W,B,G.height_end,G.upper_end,Nat.add_assoc]
lemma w_low {i : Nat} (hi : i<G.L) : G.W (2*i+1)=seg G.width G.B ((i+1)*G.q) ((i+1)*G.d) := by
  simp [W,G.height_low hi,G.upper_low hi]
lemma w_high {i : Nat} (hi : i<G.L) : G.W (2*i+2)=seg G.width G.B (i*G.q) ((i+1)*G.d+G.t) := by
  rw [W,G.height_high hi,if_pos G.upper_high,Nat.add_mul,Nat.one_mul]
  congr 1 <;> omega
lemma y_zero : G.Y 0=G.W 0 := by simp [Y]
lemma y_end : G.Y G.K=G.W G.K := by simp [Y]
lemma y_low {i : Nat} (hi : i<G.L) : G.Y (2*i+1)=seg G.width G.B ((i+1)*G.q-G.A) ((i+1)*G.d+G.F) := by
  have hn : 2*i+1≠G.K := by unfold K; omega
  simp [Y,G.height_low hi,G.upper_low hi,hn]
lemma y_high {i : Nat} (hi : i<G.L) : G.Y (2*i+2)=seg G.width G.B (i*G.q+G.F) ((i+1)*G.d+G.t-G.A) := by
  have hn : 2*i+2≠G.K := by unfold K; omega
  rw [Y,if_neg (by omega),if_pos G.upper_high,G.height_high hi,Nat.add_mul,Nat.one_mul]
  congr 1 <;> omega

lemma stages (s : Nat) (hs : s≤G.K) : s=0 ∨ s=G.K ∨ (∃ i<G.L,s=2*i+1) ∨ ∃ i<G.L,s=2*i+2 := by
  unfold K at *
  by_cases z : s=0
  · exact Or.inl z
  by_cases e : s=2*G.L+1
  · exact Or.inr (Or.inl e)
  by_cases h : s%2=1
  · exact Or.inr (Or.inr (Or.inl ⟨s/2, by omega, by omega⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨(s-2)/2, by omega, by omega⟩))

lemma near_Y {s : Nat} (hs : s≤G.K) : (G.W s \ G.Y s).card ≤ G.A ∧ (G.Y s \ G.W s).card ≤ G.F := by
  rcases G.stages s hs with rfl | rfl | ⟨i,hi,rfl⟩ | ⟨i,hi,rfl⟩
  · simp [G.y_zero]
  · simp [G.y_end]
  · rw [G.w_low hi,G.y_low hi]; apply pert_low _ _ le_rfl le_rfl
    · exact Nat.mul_le_mul_right _ hi
    · rw [G.width_eq]; have h : (i+1)*G.d ≤ G.L*G.d := Nat.mul_le_mul_right G.d hi; have := G.split; have := G.sumq; omega
  · rw [G.w_high hi,G.y_high hi]; apply pert_high _ _ le_rfl le_rfl
    · unfold B; have h := Nat.mul_le_mul_right G.q hi; rw [Nat.succ_mul] at h; have := G.split; omega
    · rw [G.width_eq]; have h : (i+1)*G.d ≤ G.L*G.d := Nat.mul_le_mul_right G.d hi; omega

lemma y_step {s : Nat} (hs : s<G.K) : G.Y s ⊆ G.Y (s+1) := by
  rcases G.stages s hs.le with rfl | rfl | ⟨i,hi,rfl⟩ | ⟨i,hi,rfl⟩
  · rw [G.y_zero,G.w_zero]; simp [seg,band]
  · exact (Nat.lt_irrefl _ hs).elim
  · rw [G.y_low hi,G.y_high hi]; exact bridge_low_high G.split G.sumq
  · rw [G.y_high hi]
    by_cases h : i+1=G.L
    · rw [show 2*i+2+1=G.K by unfold K; omega,G.y_end,G.w_end]
      apply seg_mono
      · have hb := Nat.mul_le_mul_right G.q hi; unfold B; rw [Nat.succ_mul] at hb; have := G.split; omega
      · have hb : (i+1)*G.d ≤ G.L*G.d := Nat.mul_le_mul_right G.d hi; omega
    · have hlt : i+1<G.L := by omega
      rw [show 2*i+2+1=2*(i+1)+1 by omega,G.y_low hlt]
      exact bridge_high_low G.split G.sumq

end Grid
end PEqualNP.Outside.L_lib_1446

namespace PEqualNP.Outside.L_lib_1446.Grid

variable (G : Grid)

lemma height_le {s : Nat} (h : s≤G.K) : G.height s ≤ G.L := by
  rcases G.stages s h with rfl | rfl | ⟨i,hi,rfl⟩ | ⟨i,hi,rfl⟩
  · rw [G.height_zero]; omega
  · rw [G.height_end]
  · rw [G.height_low hi]; omega
  · rw [G.height_high hi]; omega

lemma step_heights {s u : Nat} (h : s<u) (hK : u≤G.K) :
    (G.upper s → G.upper u → G.height s+1 ≤ G.height u) ∧
    (¬G.upper s → ¬G.upper u → G.height s+1 ≤ G.height u) ∧
    (¬G.upper s → G.upper u → G.height s ≤ G.height u+1) ∧
    (G.upper s → ¬G.upper u → G.height s+2 ≤ G.height u) := by
  unfold upper height K at *
  split_ifs <;> omega

lemma diff_W {s u : Nat} (hu : u≤G.K) (hs : s≤G.K) :
    (G.W u \ G.W s).card =
      (G.height u*G.q-G.height s*G.q)+
      ((G.height u*G.d+(if G.upper u then G.t+G.d else 0))-(G.height s*G.d+(if G.upper s then G.t+G.d else 0))) := by
  apply seg_diff (Nat.mul_le_mul_right _ (G.height_le hu)) (Nat.mul_le_mul_right _ (G.height_le hs))
  rw [G.width_eq]; unfold B; have hd := Nat.mul_le_mul_right G.d (G.height_le hu); split <;> omega

lemma separated {s u : Nat} (h : s<u) (hu : u≤G.K) : G.t ≤ (G.W u \ G.W s).card := by
  rw [G.diff_W hu (by omega)]
  obtain ⟨aa,bb,ba,ab⟩ := G.step_heights h hu
  have same (h : G.height s+1 ≤ G.height u) :
      G.height s*G.q + G.q ≤ G.height u*G.q ∧ G.height s*G.d + G.d ≤ G.height u*G.d := by
    constructor <;> simpa only [Nat.add_mul,Nat.one_mul] using Nat.mul_le_mul_right _ h
  have ht := G.sumq
  by_cases a : G.upper s <;> by_cases b : G.upper u <;> simp only [a,b,ite_true,ite_false,Nat.add_zero]
  · have := same (aa a b); omega
  · have hz := Nat.mul_le_mul_right G.q (ab a b); simp only [Nat.add_mul,Nat.two_mul] at hz; have := G.half; omega
  · have hz := Nat.mul_le_mul_right G.d (ba a b); simp only [Nat.add_mul,Nat.one_mul] at hz; omega
  · have := same (bb a b); omega

lemma triangle {α : Type} [DecidableEq α] (A B C : Finset α) : (A \ C).card ≤ (A \ B).card + (B \ C).card := by
  apply (Finset.card_le_card (t:=(A \ B) ∪ (B \ C)) ?_).trans (Finset.card_union_le _ _)
  intro z hz; simp only [Finset.mem_sdiff,Finset.mem_union] at hz ⊢; by_cases q : z∈B <;> simp [q,hz]

lemma center_test {s u a f : Nat} {Y : Finset (Fin G.width)} (sK : s≤G.K) (uK : u≤G.K) (ht : G.t=a+f+1)
    (gain : (Y \ G.W s).card ≤ f) (test : (G.W u \ Y).card ≤ a) : u≤s := by
  by_contra! h
  have := G.separated h uK
  have := triangle (G.W u) Y (G.W s)
  omega

end PEqualNP.Outside.L_lib_1446.Grid

namespace PEqualNP.Outside.L_lib_1446
namespace Bank
variable {X J : Type} {n : Nat}

def countAt (l : List J) (tag : J → X → Bool) (x : X) := (l.filter (fun i => tag i x)).length

theorem countBank (raw : X → List Bool) (width : ∀ x, (raw x).length=n) (p : Net n)
    (z : p.has raw (fun _ => false)) (one : p.has raw (fun _ => true))
    (l : List J) (tag : J → X → Bool) (get : ∀ j ∈ l, p.has raw (tag j)) :
    ∃ q, Grow raw p q (2*l.length*(l.length+1)) 0 ∧
      ∀ k : Nat, q.has raw (fun x => decide (k≤countAt l tag x)) := by
  induction l with
  | nil =>
    refine ⟨p,by simpa using start raw p,?_⟩
    intro k
    by_cases h : k=0
    · simpa [h,countAt] using one
    · simpa [countAt,h] using z
  | cons j l ih =>
    obtain ⟨q,g,old⟩ := ih (fun i hi => get i (List.mem_cons_of_mem j hi))
    let target := fun (k : Nat) (x : X) => decide (k+1 ≤ countAt (j::l) tag x)
    obtain ⟨v,g',outputs⟩ := batch (raw:=raw) q (List.range (l.length+1)) target 2 0 (by
      intro k _ u keep
      obtain ⟨p₁,g₁,a⟩ := binary width u _ _ (keep _ (g.1 _ (get j (by simp)))) (keep _ (old k)) true
      obtain ⟨p₂,g₂,c⟩ := binary width p₁ _ _ (g₁.1 _ (keep _ (old (k+1)))) a false
      refine ⟨p₂,chain g₁ g₂,?_⟩
      convert c using 2 with x
      change decide (k+1 ≤ countAt (j::l) tag x) = (decide (k+1 ≤ countAt l tag x) || (tag j x && decide (k ≤ countAt l tag x)))
      have eq : countAt (j::l) tag x = (if tag j x then 1 else 0)+countAt l tag x := by
        cases h : tag j x <;> simp [countAt,List.filter_cons,h,Nat.add_comm]
      have bump (v : Bool) (x k : Nat) : decide (k+1 ≤ (if v then 1 else 0)+x) =
          (decide (k+1≤x) || (v && decide (k≤x))) := by
        apply Bool.eq_iff_iff.mpr
        cases v <;> simp <;> omega
      rw [eq]; exact bump _ _ _)
    have growth := chain g g'
    refine ⟨v,allowance growth ?_,?_⟩
    · simp only [List.length_range,List.length_cons]; nlinarith
    · intro k
      rcases k with _ | k
      · simpa using (growth.1 _ one)
      · by_cases inside : k<l.length+1
        · exact outputs k (List.mem_range.mpr inside)
        · have empty (x : X) : ¬ k+1 ≤ countAt (j::l) tag x := by
            have := List.length_filter_le (fun i => tag i x) (j::l)
            simp only [List.length_cons] at this
            dsimp [countAt]; omega
          simpa only [empty,decide_false] using growth.1 _ z

end Bank
end PEqualNP.Outside.L_lib_1446

namespace PEqualNP.Outside.L_lib_1446.Grid

variable (G : Grid)

def chosen (V : Finset (Fin (G.L+1))) := V.filter (fun i => i.val<G.L)
def cutsA (V : Finset (Fin (G.L+1))) := (G.chosen V).image (fun i => 2*i.val+2)
def cutsB (V : Finset (Fin (G.L+1))) : Finset Nat :=
  if ∃ i∈V, i.val=G.L then (Finset.range (G.L-1)).image (fun i => 2*i+3) else ∅
def cuts (V : Finset (Fin (G.L+1))) := G.cutsA V ∪ G.cutsB V

lemma cuts_card (V : Finset (Fin (G.L+1))) :
    (G.cuts V).card = (G.chosen V).card + if ∃ i∈V,i.val=G.L then G.L-1 else 0 := by
  have d : Disjoint (G.cutsA V) (G.cutsB V) := by
    rw [Finset.disjoint_left]; intro z h1 h2
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h1
    unfold cutsB at h2; split at h2
    · obtain ⟨k,_,he⟩ := Finset.mem_image.mp h2; omega
    · simpa using h2
  rw [cuts,Finset.card_union_of_disjoint d,cutsA,Finset.card_image_of_injective _ (fun i j he => Fin.ext (by omega))]
  unfold cutsB; split
  · rw [Finset.card_image_of_injective _ (fun i j he => by omega),Finset.card_range]
  · simp

lemma cut_bounds {V : Finset (Fin (G.L+1))} {e : Nat} (h : e∈G.cuts V) : 0<e ∧ e≤G.K := by
  rcases Finset.mem_union.mp h with ha | hb
  · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha; have hi' := (Finset.mem_filter.mp hi).2; unfold K; omega
  · unfold cutsB at hb; split at hb
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hb; have := Finset.mem_range.mp hi; unfold K; omega
    · simp at hb

lemma cut_falls {V : Finset (Fin (G.L+1))} {e : Nat} (h : e∈G.cuts V) : ∃ j∈V, j ∈ G.raw (e-1) ∧ j ∉ G.raw e := by
  rcases Finset.mem_union.mp h with a|b
  · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp a
    obtain ⟨jj,hj⟩ := Finset.mem_filter.mp hj
    refine ⟨j,jj,?_⟩
    rw [show 2*j.val+2-1=2*j.val+1 by omega]
    simp [raw,G.height_low hj,G.height_high hj,G.upper_low hj,G.upper_high,show j.val≠G.L by omega]
  · unfold cutsB at b; split at b
    · rename_i htop; obtain ⟨j,hj,ej⟩ := htop
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp b; have h := Finset.mem_range.mp hk
      have hk1 : k+1<G.L := by omega
      have hk0 : k<G.L := by omega
      refine ⟨j,hj,?_⟩
      rw [show 2*k+3-1=2*k+2 by omega,show 2*k+3=2*(k+1)+1 by omega]
      simp [raw,G.height_high hk0,G.upper_high,G.height_low hk1,G.upper_low hk1,ej]; omega
    · simp at b

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

def asBits {r : Nat} (x : Finset (Fin r)) := fun i : Fin r => decide (i∈x)

theorem falls_lower (V : Finset (Fin (G.L+1))) (D : Circuit) (tap : Fin (G.L+1) → Nat)
    (fan : FanInTwo D) (fit : ∀ s≤G.K, ∀ i∈V, (D.wires (List.ofFn (asBits (G.Y s)) ++ [false,true])).getD (tap i) false=true ↔ i∈G.raw s) :
    (G.cuts V).card < 2^(notCount D) := by
  let r := fun s => Driver.grade D (asBits (G.Y s))
  have mono {s : Nat} (hs : s<G.K) : asBits (G.Y s) ≤ asBits (G.Y (s+1)) := by
    intro j; change decide (j∈G.Y s) ≤ decide (j∈G.Y (s+1)); by_cases h : j∈G.Y s
    · simp [h,G.y_step hs h]
    · simp [h]
  have below (s : Nat) (hs : s ≤ G.K) : ((G.cuts V).filter (·≤s)).card ≤ r s := by
    induction s with
    | zero =>
      have hn : (G.cuts V).filter (·≤0)=∅ := by
        ext e; simp only [Finset.mem_filter,Finset.notMem_empty,iff_false]; rintro ⟨he,hz⟩; have := (G.cut_bounds he).1; omega
      rw [hn]; simp
    | succ s ih =>
      have hlt : s<G.K := by omega
      have prev := ih hlt.le
      by_cases hit : s+1 ∈ G.cuts V
      · have eq : (G.cuts V).filter (·≤s+1) = insert (s+1) ((G.cuts V).filter (·≤s)) := by
          ext e; simp only [Finset.mem_filter,Finset.mem_insert]; constructor
          · rintro ⟨h1,h2⟩; by_cases eq : e=s+1; exact Or.inl eq; exact Or.inr ⟨h1,by omega⟩
          · rintro (rfl|⟨h1,h2⟩); exact ⟨hit,le_rfl⟩; exact ⟨h1,by omega⟩
        obtain ⟨j,hj,h1,h2⟩ := G.cut_falls hit
        have a := (fit s hlt.le j hj).2 (by simpa using h1)
        have b := Bool.eq_false_iff.mpr (fun z => h2 ((fit _ hs j hj).1 z))
        have step : r s < r (s+1) := Driver.grade_fall fan (mono hlt) _ a b
        rw [eq,Finset.card_insert_of_notMem (by simp)]; omega
      · have eq : (G.cuts V).filter (·≤s+1) = (G.cuts V).filter (·≤s) := by
          ext e; simp only [Finset.mem_filter]; constructor
          · rintro ⟨he,hle⟩; exact ⟨he, by by_contra! h; exact hit ((show e=s+1 by omega) ▸ he)⟩
          · rintro ⟨he,hle⟩; exact ⟨he,by omega⟩
        rw [eq]; exact prev.trans (Driver.grade_order fan (mono hlt)).1
  have eq : (G.cuts V).filter (·≤G.K) = G.cuts V := Finset.filter_eq_self.mpr fun e he => (G.cut_bounds he).2
  have h := below G.K le_rfl; rw [eq] at h
  exact lt_of_le_of_lt h (Driver.grade_bound ..)

end PEqualNP.Outside.L_lib_1446.Grid

namespace PEqualNP.Outside.L_lib_1446.Run
variable {m : Nat}

def cuts (k : Nat) (f : Nat → Fin m → Bool) : Finset Nat :=
  (Finset.range (k+1)).filter (fun e => 0 < e ∧ ∃ j, f (e-1) j=true ∧ f e j=false)

def starts (k : Nat) (f : Nat → Fin m → Bool) (j : Fin m) : Finset Nat :=
  (Finset.range (k+1)).filter (fun a => f a j=true ∧ (a=0 ∨ f (a-1) j=false))

def stop (k : Nat) (f : Nat → Fin m → Bool) (j : Fin m) (a : Nat) : Nat :=
  Nat.find (show ∃ e, e=k+1 ∨ a < e ∧ f e j=false from ⟨k+1,Or.inl rfl⟩)

theorem stop_spec {k a} {f : Nat → Fin m → Bool} {j : Fin m} :
    stop k f j a=k+1 ∨ a < stop k f j a ∧ f (stop k f j a) j=false := by
  unfold stop
  exact Nat.find_spec (p:=fun e => e=k+1 ∨ a < e ∧ f e j=false) _

theorem stop_le {k a e} {f : Nat → Fin m → Bool} {j : Fin m}
    (h : e=k+1 ∨ a < e ∧ f e j=false) : stop k f j a ≤ e := Nat.find_min' _ h

theorem interior {k a u} {f : Nat → Fin m → Bool} {j : Fin m}
    (one : f a j=true) (lo : a ≤ u) (hi : u < stop k f j a) : f u j=true := by
  by_contra! h
  have zero : f u j=false := Bool.eq_false_iff.mpr h
  by_cases eq : a=u
  · simp_all
  · have b := stop_le (k:=k) (Or.inr ⟨show a < u by omega,zero⟩)
    omega

theorem ends {k a} {f : Nat → Fin m → Bool} {j : Fin m} (ha : a∈starts k f j) :
    stop k f j a=k+1 ∨ stop k f j a ∈ cuts k f := by
  rcases stop_spec (k:=k) (f:=f) (j:=j) (a:=a) with last | ⟨lt,zero⟩
  · exact Or.inl last
  · have upper := stop_le (a:=a) (f:=f) (j:=j) (Or.inl rfl : k+1=k+1 ∨ _)
    by_cases last : stop k f j a=k+1
    · exact Or.inl last
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by omega,j,
        interior (k:=k) (Finset.mem_filter.mp ha).2.1 (by omega) (by omega),zero⟩)

theorem represent (k : Nat) (f : Nat → Fin m → Bool) (j : Fin m) (u : Nat)
    (ku : u ≤ k) : f u j=true ↔ ∃ a ∈ starts k f j, a ≤ u ∧ u < stop k f j a := by
  constructor
  · intro one
    let P (a : Nat) := a ≤ u ∧ ∀ v, a ≤ v → v ≤ u → f v j=true
    have hp : ∃ a, P a := ⟨u,le_rfl,fun v lo hi => le_antisymm hi lo ▸ one⟩
    let a := Nat.find hp
    have prop : P a := Nat.find_spec hp
    have start : a=0 ∨ f (a-1) j=false := by
      by_cases za : a=0
      · exact Or.inl za
      · right
        apply Bool.eq_false_iff.mpr
        intro yes
        have prev : P (a-1) := by
          refine ⟨by have := prop.1; omega,?_⟩
          intro v lo hi
          by_cases eq : v=a-1
          · simpa [eq] using yes
          · exact prop.2 _ (by omega) hi
        have minimal := Nat.find_min' hp prev
        change a ≤ a-1 at minimal
        omega
    have au := prop.1
    refine ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),prop.2 _ le_rfl au,start⟩,au,?_⟩
    rcases stop_spec (k:=k) (f:=f) (j:=j) (a:=a) with last | ⟨lt,zero⟩
    · omega
    · by_contra! h
      have o := prop.2 _ lt.le h
      simp_all
  · rintro ⟨a,ha,lo,hi⟩
    exact interior (Finset.mem_filter.mp ha).2.1 lo hi

def place (s : Finset Nat) (x : Nat) :=
  Finset.univ.sup (fun i : Fin s.card => if s.orderEmbOfFin rfl i ≤ x then i.val+1 else 0)

theorem place_le (s : Finset Nat) (x : Nat) : place s x ≤ s.card := by
  apply Finset.sup_le
  intro i _
  split <;> have := i.isLt <;> omega

theorem place_at (s : Finset Nat) (i : Fin s.card) (x : Nat) :
    i.val+1 ≤ place s x ↔ s.orderEmbOfFin rfl i ≤ x := by
  classical
  constructor
  · intro large
    by_contra! bad
    have upper : place s x ≤ i.val := by
      apply Finset.sup_le
      intro j _
      split
      · rename_i yes
        have lt : s.orderEmbOfFin rfl j < s.orderEmbOfFin rfl i := lt_of_le_of_lt yes bad
        have jj : j < i := (s.orderEmbOfFin rfl).lt_iff_lt.mp lt
        omega
      · omega
    omega
  · intro le
    have z := Finset.le_sup (s:=Finset.univ)
      (f:=fun j : Fin s.card => if s.orderEmbOfFin rfl j ≤ x then j.val+1 else 0) (Finset.mem_univ i)
    simpa only [place,if_pos le] using z

end PEqualNP.Outside.L_lib_1446.Run

namespace PEqualNP.Outside.L_lib_1446.Run
open Bank Sorted

theorem realize {X : Type} {n m k b : Nat} (raw : X → List Bool) (width : ∀ x,(raw x).length=n)
    (stage : X → Nat) (bounded : ∀ x,stage x≤k) (f : Nat → Fin m → Bool) (room : (cuts k f).card<2^b)
    (p : Net n) (zero : p.has raw (fun _ => false)) (basic : ∀ j : Nat, p.has raw (fun x => decide (j≤stage x))) :
    ∃ z, Grow raw p z (4*(cuts k f).card+b+m*(2*(k+1))) b ∧ ∀ j, z.has raw (fun x => f (stage x) j) := by
  classical
  let S := cuts k f
  let r := fun x => place S (stage x)
  have known (i : Nat) (pos : 0 < i) (le : i ≤ S.card) : p.has raw (high r i) := by
    let j : Fin S.card := ⟨i-1,by omega⟩
    convert basic (S.orderEmbOfFin rfl j) using 2 with x
    apply Bool.eq_iff_iff.mpr
    simp only [high,r,decide_eq_true_eq]
    have he : i=j.val+1 := by dsimp [j]; omega
    have hh := place_at S j (stage x)
    rwa [←he] at hh
  obtain ⟨q,g,lows⟩ := decode raw width b S.card room r (fun x => place_le S (stage x)) p zero known
  have ending (j : Fin m) (a : Nat) (ha : a∈starts k f j) : q.has raw (fun x => decide (stage x < stop k f j a)) := by
    rcases ends ha with last|mem
    · convert g.1 _ (basic 0) using 2 with x
      simp [last,Nat.lt_succ_of_le (bounded x)]
    · obtain ⟨i,hi'⟩ : ∃ i : Fin S.card, S.orderEmbOfFin rfl i=stop k f j a := by
        exact (show stop k f j a ∈ Set.range (S.orderEmbOfFin rfl) by simpa [S] using mem)
      have h := lows (i.val+1) (by omega) i.isLt
      convert h using 2 with x
      apply Bool.eq_iff_iff.mpr
      simp only [low,r,decide_eq_true_eq]
      have key := place_at S i (stage x); rw [hi'] at key; omega
  obtain ⟨z,gz,labels⟩ := batch (raw:=raw) q (List.finRange m) (fun j x => f (stage x) j) (2*(k+1)) 0 (by
    intro j _ u keep
    let l := (starts k f j).toList
    let ok := fun (a : Nat) (x : X) => decide (a ≤ stage x) && decide (stage x < stop k f j a)
    obtain ⟨w,gw,okW⟩ := batch (raw:=raw) u l ok 1 0 (by
      intro a ha v pv
      have ha' : a∈starts k f j := by simpa [l] using ha
      obtain ⟨w,gg,ww⟩ := binary width v _ _ (pv _ (keep _ (g.1 _ (basic a)))) (pv _ (keep _ (ending j a ha'))) true
      exact ⟨w,gg,by simpa [ok] using ww⟩)
    obtain ⟨v,gv,h⟩ := anyList width w (gw.1 _ (keep _ (g.1 _ zero))) l ok okW
    refine ⟨v,?_,?_⟩
    · have bound : l.length ≤ k+1 := by
        simpa [l,starts] using Finset.card_filter_le (Finset.range (k+1)) (fun a => f a j=true ∧ (a=0 ∨ f (a-1) j=false))
      simpa only [Nat.mul_zero,Nat.add_zero] using allowance (chain gw gv) (show l.length*1+l.length ≤ 2*(k+1) by omega)
    · convert h using 2 with x
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true,ok,Bool.and_eq_true,decide_eq_true_eq,l,Finset.mem_toList]
      exact represent _ _ _ _ (bounded x))
  refine ⟨z,by simpa [S] using chain g gz,fun j => labels j (by simp)⟩

end PEqualNP.Outside.L_lib_1446.Run

namespace PEqualNP.Outside.L_lib_1446.Grid

variable (G : Grid)
def answer (V : Finset (Fin (G.L+1))) (s : Nat) (i : Fin (G.L+1)) := decide (i∈V ∧ i∈G.raw s)

lemma actual_cuts (V : Finset (Fin (G.L+1))) : Run.cuts G.K (G.answer V) ⊆ G.cuts V := by
  intro e he
  obtain ⟨heK,hp,j,one,zero⟩ := Finset.mem_filter.mp he
  have hK := Finset.mem_range.mp heK
  have h1 : j∈V ∧ j∈G.raw (e-1) := of_decide_eq_true one
  have h0 : j∉G.raw e := fun h => (of_decide_eq_false zero) ⟨h1.1,h⟩
  rcases G.stages (e-1) (by omega) with hz | hz | ⟨i,hi,hs⟩ | ⟨i,hi,hs⟩
  · have := h1.2; simp [hz,raw,G.height_zero,G.upper_zero] at this
  · omega
  · have heq : e=2*i+2 := by omega
    have hb := h1.2; simp [hs,raw,G.height_low hi,G.upper_low hi] at hb
    simp [heq,raw,G.height_high hi,G.upper_high] at h0
    apply Finset.mem_union.mpr; left
    exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨h1.1,by omega⟩,by omega⟩
  · by_cases eq : i+1=G.L
    · have heq : e=G.K := by unfold K; omega
      have jle := j.isLt; simp [heq,raw,G.height_end,G.upper_end] at h0; omega
    · have hi1 : i+1<G.L := by omega
      have heq : e=2*(i+1)+1 := by omega
      have hb := h1.2; simp [hs,raw,G.height_high hi,G.upper_high] at hb
      simp [heq,raw,G.height_low hi1,G.upper_low hi1] at h0
      have htop : ∃ j∈V,j.val=G.L := ⟨j,h1.1,by omega⟩
      apply Finset.mem_union.mpr; right
      rw [cutsB,if_pos htop]; exact Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr (by omega),by omega⟩

end PEqualNP.Outside.L_lib_1446.Grid

namespace PEqualNP.Outside.L_lib_1446.Grid
open Bank

variable (G : Grid)
structure Sample (a f : Nat) where
  stage : Fin (G.K+1)
  recv : Finset (Fin G.width)
  loss : (G.W stage.val \ recv).card ≤ a
  gain : (recv \ G.W stage.val).card ≤ f

variable {a f : Nat}
def input (v : Sample G a f) := List.ofFn (asBits v.recv) ++ [false,true]
def pin (j : Fin G.width) (v : Sample G a f) := asBits v.recv j
def test (s : Fin (G.K+1)) (v : Sample G a f) := decide ((G.W s.val \ v.recv).card ≤ a)

lemma in_len (v : Sample G a f) : (G.input v).length=G.width+2 := by simp [input]
lemma emptyPin (j : Fin G.width) : (empty (G.width+2)).has (G.input (a:=a) (f:=f)) (G.pin j) := by
  refine ⟨j.val,by simp [empty]; omega,?_⟩
  intro x; change (List.ofFn (asBits x.recv) ++ [false,true]).getD j.val false = asBits x.recv j
  rw [List.getD_append _ _ _ _ (by simpa using j.isLt)]
  simp [List.getD_eq_getElem?_getD,j.isLt]
lemma emptyZero : (empty (G.width+2)).has (G.input (a:=a) (f:=f)) (fun _ => false) := by
  refine ⟨G.width,by simp [empty],?_⟩
  intro x; change (List.ofFn (asBits x.recv) ++ [false,true]).getD G.width false=false
  rw [List.getD_append_right _ _ _ _ (by simp)]; simp
lemma emptyOne : (empty (G.width+2)).has (G.input (a:=a) (f:=f)) (fun _ => true) := by
  refine ⟨G.width+1,by simp [empty],?_⟩
  intro x; change (List.ofFn (asBits x.recv) ++ [false,true]).getD (G.width+1) false=true
  rw [List.getD_append_right _ _ _ _ (by simp)]; simp

lemma count_eq (w : Finset (Fin G.width)) (x : Sample G a f) : countAt w.toList G.pin x = (w ∩ x.recv).card := by
  let l := w.toList.filter (fun j => G.pin j x)
  have dis : l.Nodup := w.nodup_toList.filter _
  have eq : l.toFinset = w ∩ x.recv := by ext j; simp [l,pin,asBits]
  change l.length = _
  rw [← List.toFinset_card_of_nodup dis,eq]

def detectCost := (G.K+1)*(2*G.width*(G.width+1))+(G.K+1)*(G.K+1)

theorem detect (ht : G.t=a+f+1) : ∃ p : Net (G.width+2),
    Grow (G.input (a:=a) (f:=f)) (empty _) p G.detectCost 0 ∧
    ∀ e : Nat, p.has G.input (fun x : Sample G a f => decide (e ≤ x.stage.val)) := by
  let raw := G.input (a:=a) (f:=f)
  let init := empty (G.width+2)
  let K := G.K+1
  let stepCost := 2*G.width*(G.width+1)
  obtain ⟨q,g,tested⟩ := batch (raw:=raw) init (List.finRange K) G.test stepCost 0 (by
    intro j _ u keep
    let w := G.W j.val
    let l := w.toList
    obtain ⟨v,g,nums⟩ := countBank raw G.in_len u (keep _ G.emptyZero) (keep _ G.emptyOne) l G.pin
      (fun i _ => keep _ (G.emptyPin i))
    have len : l.length ≤ G.width := by simpa [l] using card_finset_fin_le w
    refine ⟨v,allowance g (by dsimp [stepCost]; nlinarith [Nat.mul_le_mul len (Nat.add_le_add_right len 1)]),?_⟩
    convert nums (w.card-a) using 2 with x
    rw [G.count_eq]; apply Bool.eq_iff_iff.mpr
    simp only [test,decide_eq_true_eq]
    have h := Finset.card_sdiff_add_card_inter w x.recv
    change (w \ x.recv).card ≤ a ↔ w.card-a ≤ (w ∩ x.recv).card
    omega)
  have tq (j : Fin K) := tested j (by simp)
  let pref := fun (e : Fin K) (x : Sample G a f) => decide (e.val≤x.stage.val)
  obtain ⟨p,h,prefs⟩ := batch (raw:=raw) q (List.finRange K) pref K 0 (by
    intro e _ u keep
    let l := (List.finRange K).filter (fun j => decide (e.val ≤ j.val))
    obtain ⟨v,gu,truth⟩ := anyList G.in_len u (keep _ (g.1 _ G.emptyZero)) l G.test (fun i _ => keep _ (tq i))
    refine ⟨v,allowance gu (by simpa [l] using List.length_filter_le (fun j : Fin K => decide (e.val≤j.val)) (List.finRange K)),?_⟩
    convert truth using 2 with x
    apply Bool.eq_iff_iff.mpr
    simp only [pref,List.any_eq_true,l,List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq,test]
    constructor
    · intro he; exact ⟨x.stage,he,x.loss⟩
    · rintro ⟨j,hj,hpass⟩; exact hj.trans (G.center_test (by have := x.stage.isLt; omega) (by have := j.isLt; dsimp [K] at *; omega) ht x.gain hpass))
  have both := chain g h
  refine ⟨p,by simpa [raw,init,K,stepCost,detectCost] using both,?_⟩
  intro e
  by_cases le : e<K
  · exact prefs ⟨e,le⟩ (by simp)
  · convert both.1 _ G.emptyZero using 2 with x
    have bound := x.stage.isLt; simp [show ¬e≤x.stage.val by dsimp [K] at le; omega]

end PEqualNP.Outside.L_lib_1446.Grid

namespace PEqualNP.Outside.L_lib_1446.Grid
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket
open Bank

variable (G : Grid)
def fits (a f b size : Nat) (V : Finset (Fin (G.L+1))) :=
  ∃ (C : Circuit) (out : Fin (G.L+1) → Nat), FanInTwo C ∧ ReadsBack (G.width+2) C ∧
    C.output<G.width+2+C.size ∧ C.size≤size ∧ notCount C≤b ∧ (∀ j,out j<G.width+2+C.size) ∧
    ∀ s : Fin (G.K+1), ∀ Y : Finset (Fin G.width),
      (G.W s.val \ Y).card≤a ∧ (Y \ G.W s.val).card≤f → ∀ i∈V,
      (C.wires (List.ofFn (asBits Y) ++ [false,true])).getD (out i) false=true ↔ i∈G.raw s.val

def cap := 64*(G.L+1)*((G.width+1)^2+G.L+2)

theorem lower {a f b size : Nat} {V : Finset (Fin (G.L+1))} (ha : G.A≤a) (hf : G.F≤f) (ok : G.fits a f b size V) : (G.cuts V).card<2^b := by
  obtain ⟨C,out,fan,_,_,_,hn,_,labels⟩ := ok
  apply lt_of_lt_of_le (G.falls_lower V C out fan ?_) (Nat.pow_le_pow_right (by decide : 0<2) hn)
  intro s hs i hi
  have near := G.near_Y hs
  exact labels ⟨s,by omega⟩ (G.Y s) ⟨near.1.trans ha,near.2.trans hf⟩ i hi

theorem upper_fit {a f b : Nat} {V : Finset (Fin (G.L+1))} (ht : G.t=a+f+1) (room : (G.cuts V).card<2^b) : G.fits a f b G.cap V := by
  classical
  let card := (Run.cuts G.K (G.answer V)).card
  let c := min b card
  have cmp : card ≤ (G.cuts V).card := Finset.card_le_card (G.actual_cuts V)
  have capCard : card ≤ G.K+1 := by
    simpa [card,Run.cuts] using Finset.card_filter_le (Finset.range (G.K+1)) (fun e => 0 < e ∧ ∃ j,G.answer V (e-1) j=true ∧ G.answer V e j=false)
  have enough : card<2^c := by
    dsimp [c]; rcases le_total b card with u|u
    · rw [min_eq_left u]; exact lt_of_le_of_lt cmp room
    · rw [min_eq_right u]; exact card.lt_two_pow_self
  let raw := G.input (a:=a) (f:=f)
  obtain ⟨p,g,basic⟩ := G.detect ht
  obtain ⟨z,gz,labels⟩ := Run.realize raw G.in_len (fun x => x.stage.val) (by intro x; have := x.stage.isLt; omega)
    (G.answer V) enough p (g.1 _ G.emptyZero) basic
  have total := chain g gz
  let C : Circuit := ⟨z.gates,0⟩
  let out := fun j => (labels j).choose
  refine ⟨C,out,z.fan,z.readsBack,by simp [C],?_,?_,fun j => (labels j).choose_spec.1,?_⟩
  · have budget : z.gates.length ≤ G.detectCost+(4*card+c+(G.L+1)*(2*(G.K+1))) := by simpa [empty,card] using total.2.1
    have bound : c≤card := min_le_right ..
    change z.gates.length ≤ G.cap
    apply budget.trans
    dsimp [detectCost,cap,K] at *
    have z1 := G.pos
    nlinarith [Nat.zero_le (G.L*G.width*G.width),Nat.zero_le (G.L*G.width),Nat.zero_le (G.width*G.width)]
  · change z.cost ≤ b
    have eq : z.cost=c := by simpa [empty,Net.cost,NotBracket.notCount] using total.2.2
    exact eq.le.trans (min_le_left ..)
  · intro s Y near i hi
    let x : Sample G a f := ⟨s,Y,near.1,near.2⟩
    have h := (labels i).choose_spec.2 x
    change (C.wires (List.ofFn (asBits Y) ++ [false,true])).getD (out i) false = G.answer V s.val i at h
    rw [h]; simp [answer,hi]

end PEqualNP.Outside.L_lib_1446.Grid

namespace PEqualNP.Outside.L_lib_1446

theorem result (L a f d : Nat) (hp : 0<L) (hd : 0<d) (h : 2*d≤a+f+1) (V : Finset (Fin (L+1))) (b : Nat) :
  let t := a+f+1
  let q := t-d
  let r := (L+1)*t+d
  let height := fun (s : Fin (2*L+2)) => if s.val=0 then 0 else if s.val=2*L+1 then L else
    if s.val % 2=1 then (s.val+1)/2 else (s.val-2)/2
  let upper := fun (s : Fin (2*L+2)) => s.val≠0 ∧ (s.val % 2=0 ∨ s.val=2*L+1)
  let raw := fun (s : Fin (2*L+2)) => Finset.univ.filter (fun i : Fin (L+1) => i.val < height s ∨ (i.val=L ∧ upper s))
  let word := fun (s : Fin (2*L+2)) => Finset.univ.filter (fun i : Fin r =>
    i.val < height s*q ∨ (L*q ≤ i.val ∧ i.val < L*q+height s*d+(if upper s then t+d else 0)))
  let near := fun (s : Fin (2*L+2)) (Y : Finset (Fin r)) => (word s \ Y).card ≤ a ∧ (Y \ word s).card ≤ f
  let bits := fun {k : Nat} (X : Finset (Fin k)) => List.ofFn (fun j : Fin k => decide (j ∈ X)) ++ [false,true]
  let falls := (V.filter (fun i => i.val<L)).card + (if ∃ i ∈ V, i.val=L then L-1 else 0)
  let fit := fun (size : Nat) => ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin (L+1) → Nat),
    PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (r+2) D ∧
    D.output < r+2+D.size ∧ D.size ≤ size ∧ PEqualNP.NotBracket.notCount D ≤ b ∧
    (∀ i, out i < r+2+D.size) ∧ ∀ s Y, near s Y → ∀ i ∈ V,
      ((D.wires (bits Y)).getD (out i) false = true ↔ i ∈ raw s)
  ((∃ size, fit size) ↔ falls < 2^b) ∧ (falls < 2^b → fit (64*(L+1)*((r+1)^2+L+2))) := by
  obtain ⟨A,F,hA,hF,hAF⟩ := split_noise (a:=a) (f:=f) rfl hd (by omega : d ≤ a+f+1)
  let G : Grid := ⟨L,a+f+1,d,a+f+1-d,A,F,hp,by omega,by omega,hAF⟩
  let N := (G.cuts V).card
  have ans : ((∃ size, G.fits a f b size V) ↔ N<2^b) ∧ (N<2^b → G.fits a f b G.cap V) := by
    have upper := G.upper_fit (V:=V) (b:=b) (a:=a) (f:=f) rfl
    exact ⟨⟨fun ⟨s,hs⟩ => G.lower hA hF hs,fun hr => ⟨_,upper hr⟩⟩,upper⟩
  have wform (s : Nat) : G.W s = Finset.univ.filter (fun i : Fin G.width => i.val < G.height s*G.q ∨ G.B ≤ i.val ∧
      i.val < G.B+G.height s*G.d+(if G.upper s then G.t+G.d else 0)) := by
    rw [Grid.W,seg_form]; simp only [Nat.add_assoc]
  simp only [N,G.cuts_card,Grid.fits,Grid.chosen,wform,Grid.raw,Grid.cap,Grid.height,Grid.upper,Grid.K,
    Grid.width,Grid.B,Grid.asBits,G] at ans
  dsimp only
  convert! ans using 1 <;> congr! 80

end PEqualNP.Outside.L_lib_1446

theorem PEqualNP.Outside.L_lib_1446 : (letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
∀ (L a f d : Nat), 0<L → 0<d →
  let t := a+f+1
  2*d ≤ t →
  let q := t-d
  let r := (L+1)*t+d
  let height := fun (s : Fin (2*L+2)) => if s.val=0 then 0 else if s.val=2*L+1 then L else
    if s.val % 2=1 then (s.val+1)/2 else (s.val-2)/2
  let upper := fun (s : Fin (2*L+2)) => s.val≠0 ∧ (s.val % 2=0 ∨ s.val=2*L+1)
  let raw := fun (s : Fin (2*L+2)) => Finset.univ.filter (fun i : Fin (L+1) => i.val < height s ∨ (i.val=L ∧ upper s))
  let word := fun (s : Fin (2*L+2)) => Finset.univ.filter (fun i : Fin r =>
    i.val < height s*q ∨ (L*q ≤ i.val ∧ i.val < L*q+height s*d+(if upper s then t+d else 0)))
  let near := fun (s : Fin (2*L+2)) (Y : Finset (Fin r)) => (word s \ Y).card ≤ a ∧ (Y \ word s).card ≤ f
  let bits := fun {k : Nat} (X : Finset (Fin k)) => List.ofFn (fun j : Fin k => decide (j ∈ X)) ++ [false,true]
  ∀ (V : Finset (Fin (L+1))) (b : Nat),
    let falls := (V.filter (fun i => i.val<L)).card + (if ∃ i ∈ V, i.val=L then L-1 else 0)
    let fit := fun (size : Nat) => ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin (L+1) → Nat),
      PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (r+2) D ∧
      D.output < r+2+D.size ∧ D.size ≤ size ∧ PEqualNP.NotBracket.notCount D ≤ b ∧
      (∀ i, out i < r+2+D.size) ∧ ∀ s Y, near s Y → ∀ i ∈ V,
        ((D.wires (bits Y)).getD (out i) false = true ↔ i ∈ raw s)
    ((∃ size, fit size) ↔ falls < 2^b) ∧ (falls < 2^b → fit (64*(L+1)*((r+1)^2+L+2)))) := by
  dsimp only
  intro L a f d hp hd hh V b
  have h := PEqualNP.Outside.L_lib_1446.result L a f d hp hd hh V b
  dsimp only at h
  convert! h using 1 <;> congr! 80
