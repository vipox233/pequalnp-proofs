import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Sublists
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27189_aux

open PEqualNP.CircuitLowerBounds
namespace CircuitSatBridge

def source (n i : Nat) : Nat := if i < n then i+1 else 0

def read (w : List Bool) : Nat → Bool
  | 0 => false
  | i+1 => w.getD i false

theorem read_source (w : List Bool) (i : Nat) :
    read w (source w.length i) = w.getD i false := by
  by_cases h : i < w.length
  · simp [source, h, read]
  · simp [source, h, read]

abbrev Op := Ordering
abbrev Choice := Ordering × Nat × Nat
abbrev Choice.mk (op : Op) (l r : Nat) : Choice := (op,l,r)

def Choice.eval (c : Choice) (w : List Bool) : Bool :=
  match c.1 with
  | .lt => read w c.2.1 && read w c.2.2
  | .eq => read w c.2.1 || read w c.2.2
  | .gt => !read w c.2.1

def binary (op : Op) (a b : Nat) : Choice := ⟨op, min a b, max a b⟩

def normalize (n : Nat) (g : Gate) : Choice :=
  match g.op, g.inputs with
  | .and, [] => ⟨.gt, 0, 0⟩
  | .and, a :: xs => binary .lt (source n a) (source n (xs.headD a))
  | .or, [] => ⟨.eq, 0, 0⟩
  | .or, a :: xs => binary .eq (source n a) (source n (xs.headD a))
  | .not, [] => ⟨.gt, 0, 0⟩
  | .not, a :: _ => ⟨.gt, source n a, 0⟩
  | _, _ => ⟨.eq, 0, 0⟩

def Supported (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

private theorem binary_and (a b : Nat) (w : List Bool) :
    (binary .lt a b).eval w = (read w a && read w b) := by
  rcases le_total a b with h|h <;>
    simp [binary, Choice.eval, h, Bool.and_comm]

private theorem binary_or (a b : Nat) (w : List Bool) :
    (binary .eq a b).eval w = (read w a || read w b) := by
  rcases le_total a b with h|h <;>
    simp [binary, Choice.eval, h, Bool.or_comm]

private theorem neg_eval (l r : Nat) (w : List Bool) :
    (Choice.mk .gt l r).eval w = !read w l := rfl

theorem normalize_correct (w : List Bool) (g : Gate) (h : Supported g) :
    (normalize w.length g).eval w = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  obtain ⟨op, xs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  change xs.length ≤ 2 at hlen
  change op = _ ∨ op = _ ∨ op = _ at hop
  cases xs with
  | nil => rcases hop with rfl|rfl|rfl <;> rfl
  | cons a xs =>
    cases xs with
    | nil => rcases hop with rfl|rfl|rfl <;>
               simp [normalize, binary_and, binary_or, neg_eval, GateOp.eval, read_source]
    | cons b xs =>
      have : xs = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst xs
      rcases hop with rfl|rfl|rfl <;>
        simp [normalize, binary_and, binary_or, neg_eval, GateOp.eval, read_source]

def compile (n : Nat) : List Gate → List Choice
  | [] => []
  | g :: gs => normalize n g :: compile (n+1) gs

theorem compile_wires (gs : List Gate) (w : List Bool) (h : ∀ g ∈ gs, Supported g) :
    (compile w.length gs).foldl (fun v c => v ++ [c.eval v]) w =
      gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [compile, List.foldl_cons, normalize_correct w g (h g List.mem_cons_self)]
    apply Eq.trans _ (ih _ (fun a ha => h a (List.mem_cons_of_mem _ ha)))
    simp

def Choice.Legal (n : Nat) (c : Choice) : Prop :=
  c.2.1 ≤ n ∧ c.2.2 ≤ n ∧
    match c.1 with
    | .gt => c.2.2 = 0
    | _ => c.2.1 ≤ c.2.2

private theorem source_le (n i : Nat) : source n i ≤ n := by
  unfold source
  split <;> omega

theorem normalize_legal (n : Nat) (g : Gate) : (normalize n g).Legal n := by
  obtain ⟨op, xs⟩ := g
  cases op <;> cases xs <;>
    simp [normalize, Choice.Legal, binary, source_le]

theorem compile_length (gs : List Gate) (n : Nat) : (compile n gs).length = gs.length := by
  induction gs generalizing n with
  | nil => rfl
  | cons g gs ih => simp [compile, ih]

def operatorClauses (sa so sn a b y : Bool) : List Bool :=
  [!sa || !a || !b || y, !sa || a || !y, !sa || b || !y,
   !so || a || b || !y, !so || !a || y, !so || !b || y,
   !sn || a || y, !sn || !a || !y]

def selectors : Op → Bool × Bool × Bool
  | .lt => (true, false, false)
  | .eq => (false, true, false)
  | .gt => (false, false, true)

theorem operatorClauses_iff (c : Choice) (w : List Bool) (y : Bool) :
    (operatorClauses (selectors c.1).1 (selectors c.1).2.1 (selectors c.1).2.2
      (read w c.2.1) (read w c.2.2) y).all id = true ↔ y = c.eval w := by
  obtain ⟨op, l, r⟩ := c
  cases op <;> simp only [Choice.eval, selectors] <;>
    cases read w l <;> cases read w r <;> cases y <;> decide

def muxClauses (pick operand upstream : Bool) : List Bool :=
  [!pick || operand || !upstream, !pick || !operand || upstream]

theorem muxClauses_correct (w : List Bool) (selected candidate : Nat) :
    (muxClauses (decide (selected = candidate)) (read w selected) (read w candidate)).all id =
      true := by
  by_cases h : selected = candidate
  · subst candidate
    cases read w selected <;> simp [muxClauses, *]
  · simp [muxClauses, h]

theorem gate_rows (n : Nat) (g : Gate) (hg : Supported g) :
    ∃ c : Choice, c.Legal n ∧ ∀ w : List Bool, w.length = n →
      (∀ i, (muxClauses (decide (c.2.1 = i)) (read w c.2.1) (read w i)).all id = true ∧
            (muxClauses (decide (c.2.2 = i)) (read w c.2.2) (read w i)).all id = true) ∧
      (operatorClauses (selectors c.1).1 (selectors c.1).2.1 (selectors c.1).2.2
        (read w c.2.1) (read w c.2.2)
        (g.op.eval (g.inputs.map fun i => w.getD i false))).all id = true := by
  refine ⟨normalize n g, normalize_legal n g, ?_⟩
  intro w hw
  subst n
  exact ⟨fun i => ⟨muxClauses_correct _ _ _, muxClauses_correct _ _ _⟩,
    (operatorClauses_iff _ _ _).2 (normalize_correct w g hg).symm⟩

theorem compile_circuit (c : Circuit) (hc : PEqualNP.MetaComplexity.FanInTwo c) (n : Nat) :
    ∃ cs : List Choice, cs.length = c.size ∧ ∀ w : List Bool, w.length = n →
      (cs.foldl (fun v gate => v ++ [gate.eval v]) w).getD c.output false = c.eval w := by
  refine ⟨compile n c.gates, compile_length _ _, ?_⟩
  intro w hw
  subst n
  rw [compile_wires _ _ hc]
  rfl

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) w

def runChoices (gs : List Choice) (w : List Bool) : List Bool :=
  gs.foldl (fun v g => v ++ [g.eval v]) w

def Valid : Nat → List Choice → Prop
  | _, [] => True
  | n, c :: cs => c.Legal n ∧ Valid (n+1) cs

def copyWire (n i : Nat) : Choice := ⟨.eq, source n i, source n i⟩

private theorem copy_legal (n i : Nat) : (copyWire n i).Legal n := by
  simp [copyWire, Choice.Legal, source_le]

private theorem copy_eval (w : List Bool) (i : Nat) :
    (copyWire w.length i).eval w = w.getD i false := by
  simp [copyWire, Choice.eval, read_source]

private theorem append_at_end (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by simp

private theorem append_elsewhere (w : List Bool) (b : Bool) (i : Nat) (hne : i ≠ w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  by_cases hi : i < w.length
  · exact List.getD_append _ _ _ _ hi
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    have hi' : w.length ≤ i := by omega
    rw [List.getD_eq_default _ _ hi', List.getD_eq_default _ _ (by simp; omega)]

theorem fixed_slots (k n output : Nat) (gs : List Gate) (hs : ∀ g ∈ gs, Supported g)
    (hlen : gs.length ≤ k+1) :
    ∃ cs : List Choice, cs.length = k+1 ∧ Valid n cs ∧
      ∀ w : List Bool, w.length = n →
        (runChoices cs w).getD (n+k) false = (run gs w).getD output false := by
  induction k generalizing n output gs with
  | zero =>
    cases gs with
    | nil =>
      refine ⟨[copyWire n output], rfl, ⟨copy_legal _ _, trivial⟩, ?_⟩
      intro w hw
      subst n
      exact (append_at_end _ _).trans (copy_eval _ _)
    | cons g gs =>
      have : gs = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst gs
      by_cases hout : output = n
      · refine ⟨[normalize n g], rfl, ⟨normalize_legal _ _, trivial⟩, ?_⟩
        intro w hw
        subst n
        subst output
        change (_ ++ [_]).getD _ _ = (_ ++ [_]).getD _ _
        rw [normalize_correct w g (hs _ List.mem_cons_self)]
        rfl
      · refine ⟨[copyWire n output], rfl, ⟨copy_legal _ _, trivial⟩, ?_⟩
        intro w hw
        subst n
        exact (append_at_end _ _).trans ((copy_eval _ _).trans
          (append_elsewhere w _ output hout).symm)
  | succ k ih =>
    cases gs with
    | cons g gs =>
      obtain ⟨cs, hsize, hvalid, heval⟩ := ih (n+1) output gs
        (fun a ha => hs a (List.mem_cons_of_mem _ ha)) (by simpa using hlen)
      refine ⟨normalize n g :: cs, by simp [hsize], ⟨normalize_legal _ _, hvalid⟩, ?_⟩
      intro w hw
      subst n
      change (runChoices cs (w ++ [_])).getD _ _ = (run gs (w ++ [_])).getD _ _
      rw [normalize_correct w g (hs _ List.mem_cons_self)]
      simpa only [Nat.add_right_comm, Nat.add_assoc, Nat.add_comm 1 k] using
        heval (w ++ [_]) (by simp)
    | nil =>
      obtain ⟨cs, hsize, hvalid, heval⟩ := ih (output := n) (n+1) [] (by simp) (by simp)
      refine ⟨copyWire n output :: cs, by simp [hsize], ⟨copy_legal _ _, hvalid⟩, ?_⟩
      intro w hw
      subst n
      change (runChoices cs (w ++ [_])).getD _ _ = w.getD output false
      have h := heval (w ++ [(copyWire w.length output).eval w]) (by simp)
      simpa [run, copy_eval, Nat.add_assoc, Nat.add_comm 1 k] using h

end CircuitSatBridge

namespace CircuitSatBridge

def before (cs : List Choice) (w : List Bool) (j : Nat) : List Bool :=
  runChoices (cs.take j) w

private theorem runChoices_append (xs ys : List Choice) (w : List Bool) :
    runChoices (xs ++ ys) w = runChoices ys (runChoices xs w) := by
  simp [runChoices, List.foldl_append]

theorem before_length (cs : List Choice) (w : List Bool) (j : Nat) :
    (before cs w j).length = w.length + min j cs.length := by
  have len : ∀ (gs : List Choice) (x : List Bool), (runChoices gs x).length = x.length + gs.length := by
    intro gs
    induction gs with
    | nil => simp [runChoices]
    | cons g gs ih =>
      intro x
      change (runChoices gs (x ++ [g.eval x])).length = _
      rw [ih]
      simp
      omega
  simp [before, len]

theorem before_step (cs : List Choice) (w : List Bool) (j : Nat) (hj : j < cs.length) :
    before cs w (j+1) = before cs w j ++ [cs[j].eval (before cs w j)] := by
  rw [before, List.take_add_one, List.getElem?_eq_getElem hj]
  exact runChoices_append _ _ _

private theorem keeps_prefix (cs : List Choice) (w : List Bool) (i : Nat) (hi : i < w.length) :
    (runChoices cs w).getD i false = w.getD i false := by
  induction cs generalizing w with
  | nil => rfl
  | cons c cs ih =>
    change (runChoices cs (w ++ [_])).getD i false = _
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

theorem before_keeps (cs : List Choice) (w : List Bool) {a b i : Nat} (hab : a ≤ b)
    (hi : i < (before cs w a).length) :
    (before cs w b).getD i false = (before cs w a).getD i false := by
  have h : cs.take b = cs.take a ++ (cs.take b).drop a := by
    have ht : (cs.take b).take a = cs.take a := by simp [List.take_take, hab]
    rw [← ht]
    simp
  unfold before at *
  rw [h, runChoices_append, keeps_prefix _ _ _ hi]

def gateValue (cs : List Choice) (w : List Bool) (j : Nat) : Bool :=
  (before cs w (j+1)).getD (w.length+j) false

theorem gateValue_eq (cs : List Choice) (w : List Bool) (j : Nat) (hj : j < cs.length) :
    gateValue cs w j = cs[j].eval (before cs w j) := by
  rw [gateValue, before_step _ _ _ hj]
  have h := before_length cs w j
  rw [Nat.min_eq_left (by omega)] at h
  rw [← h, append_at_end]

theorem read_earlier_gate (cs : List Choice) (w : List Bool) {a b : Nat}
    (hab : a < b) (hb : b ≤ cs.length) :
    read (before cs w b) (w.length+a+1) = gateValue cs w a := by
  apply before_keeps _ _ (Nat.succ_le_of_lt hab)
  rw [before_length, Nat.min_eq_left (by omega)]
  omega

theorem read_input (cs : List Choice) (w : List Bool) (j i : Nat) (hi : i < w.length) :
    read (before cs w j) (i+1) = w.getD i false :=
  keeps_prefix _ _ _ hi

end CircuitSatBridge

namespace CircuitSatBridge

def agrees (s : Finset Nat) (x y : List Bool) := ∀ i ∈ s, x.getD i false = y.getD i false

theorem bounded_support (cs : List Choice) (n out : Nat) :
    ∃ s : Finset Nat, s ⊆ Finset.range n ∧ s.card ≤ cs.length+1 ∧
      ∀ x y : List Bool, x.length = n → y.length = n → agrees s x y →
        (runChoices cs x).getD out false = (runChoices cs y).getD out false := by
  induction cs generalizing n with
  | nil =>
    by_cases h : out < n
    · exact ⟨{out}, by simpa, by simp, fun x y _ _ ha => ha out (by simp)⟩
    · refine ⟨∅, by simp, by simp, ?_⟩
      intro x y hx hy _
      change x.getD out false = y.getD out false
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  | cons c cs ih =>
    obtain ⟨s, hs, hcard, he⟩ := ih (n+1)
    by_cases h : n ∈ s
    · let t := ({c.2.1-1, c.2.2-1} : Finset Nat).filter (· < n)
      refine ⟨s.erase n ∪ t, ?_, ?_, ?_⟩
      · intro i hi
        rcases Finset.mem_union.mp hi with h₁|h₂
        · obtain ⟨hne,his⟩ := Finset.mem_erase.mp h₁
          have hh := Finset.mem_range.mp (hs his)
          exact Finset.mem_range.mpr (by omega)
        · exact Finset.mem_range.mpr (Finset.mem_filter.mp h₂).2
      · have ht : t.card ≤ 2 := (Finset.card_filter_le _ _).trans
            ((Finset.card_insert_le _ _).trans (by simp))
        have hb := Finset.card_union_le (s.erase n) t
        rw [Finset.card_erase_of_mem h] at hb
        have hp := Finset.card_pos.mpr ⟨n,h⟩
        simp only [List.length_cons]
        omega
      · intro x y hx hy ha
        apply he _ _ (by simp [hx]) (by simp [hy])
        intro i hi
        have readEq (q : Nat) (hq : q = c.2.1 ∨ q = c.2.2) : read x q = read y q := by
          cases q with
          | zero => rfl
          | succ q =>
            change x.getD q false = y.getD q false
            by_cases hq' : q < n
            · apply ha
              apply Finset.mem_union_right
              apply Finset.mem_filter.mpr
              refine ⟨?_, hq'⟩
              rcases hq with hq|hq <;> simp [← hq]
            · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
        by_cases hi' : i = n
        · subst i
          have ev : c.eval x = c.eval y := by
            unfold Choice.eval
            rw [readEq _ (Or.inl rfl), readEq _ (Or.inr rfl)]
          convert ev using 1
          · rw [← hx]; simp
          · rw [← hy]; simp
        · have hh := Finset.mem_range.mp (hs hi)
          rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
          exact ha _ (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hi',hi⟩))
    · refine ⟨s, ?_, by simp; omega, ?_⟩
      · intro i hi
        have hh := Finset.mem_range.mp (hs hi)
        have hn : i ≠ n := fun e => h (e ▸ hi)
        exact Finset.mem_range.mpr (by omega)
      · intro x y hx hy ha
        apply he _ _ (by simp [hx]) (by simp [hy])
        intro i hi
        have hh := Finset.mem_range.mp (hs hi)
        have hn : i ≠ n := fun e => h (e ▸ hi)
        rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact ha _ hi

end CircuitSatBridge

namespace CircuitSatBridge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def IsMonotone (c : Choice) : Prop := c.1 = .gt → c.2.1 = 0

private theorem normalization_mono (n : Nat) (g : Gate) (h : g.op = .and ∨ g.op = .or) :
    IsMonotone (normalize n g) := by
  obtain ⟨op,xs⟩ := g
  rcases h with h|h <;> dsimp at h <;> subst op <;> cases xs <;> simp [normalize,binary,IsMonotone]

private theorem compile_mono (gs : List Gate) (n : Nat)
    (h : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
    Valid n (compile n gs) ∧ ∀ c ∈ compile n gs, IsMonotone c := by
  induction gs generalizing n with
  | nil => exact ⟨trivial, by simp [compile]⟩
  | cons g gs ih =>
    obtain ⟨hv,hm⟩ := ih (n+1) (fun a ha => h a (List.mem_cons_of_mem _ ha))
    refine ⟨⟨normalize_legal _ _,hv⟩, ?_⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl|hc
    · exact normalization_mono _ _ (h g List.mem_cons_self)
    · exact hm _ hc

def falseGate : Choice := ⟨.eq,0,0⟩

private theorem pad_eval (k : Nat) (x : List Bool) (o : Nat) :
    (runChoices (List.replicate k falseGate) x).getD o false = x.getD o false := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ]
    change (runChoices _ (x ++ [false])).getD o false = _
    rw [ih]
    by_cases ho : o < x.length
    · exact List.getD_append _ _ _ _ ho
    · have hh : x.length ≤ o := by omega
      rw [List.getD_append_right _ _ _ _ hh, List.getD_eq_default _ _ hh]
      cases o - x.length <;> rfl

private theorem pad_valid (cs : List Choice) (n k : Nat) (h : Valid n cs) :
    Valid n (cs ++ List.replicate k falseGate) := by
  induction cs generalizing n with
  | nil =>
    induction k generalizing n with
    | zero => trivial
    | succ k ih => exact ⟨by simp [falseGate,Choice.Legal], ih (n+1) trivial⟩
  | cons c cs ih => exact ⟨h.1, ih _ h.2⟩

theorem monotone_slots (n k : Nat) {c : Circuit} (hm : Monotone2 c) (hs : c.size ≤ k) :
    ∃ cs : List Choice, cs.length = k ∧ Valid n cs ∧ (∀ g ∈ cs, IsMonotone g) ∧
    ∀ w : List Bool, w.length = n → (runChoices cs w).getD c.output false = c.eval w := by
  obtain ⟨hv, hmono⟩ := compile_mono c.gates n (fun g hg => (hm g hg).1)
  let padded := List.replicate (k-c.size) falseGate
  refine ⟨compile n c.gates ++ padded, ?_, pad_valid _ _ _ hv, ?_, ?_⟩
  · simp [padded, compile_length, Circuit.size] at *
    omega
  · intro g hg
    rcases List.mem_append.mp hg with h|h
    · exact hmono _ h
    · have he := (List.mem_replicate.mp h).2
      subst g
      simp [falseGate, IsMonotone]
  · intro w hw
    subst n
    change (List.foldl _ w (_ ++ _)).getD _ _ = _
    rw [List.foldl_append]
    change (runChoices padded (runChoices _ w)).getD _ _ = _
    rw [pad_eval]
    unfold runChoices
    rw [compile_wires]
    · rfl
    · intro g hg
      obtain ⟨hop, hb⟩ := hm g hg
      rcases hop with hop|hop
      · exact ⟨Or.inl hop,hb⟩
      · exact ⟨Or.inr (Or.inl hop),hb⟩

end CircuitSatBridge

namespace CircuitSatBridge

def remapGate (f : Nat → Nat) (c : Choice) : Choice :=
  match c.1 with
  | .lt => binary .lt (f c.2.1) (f c.2.2)
  | .eq => binary .eq (f c.2.1) (f c.2.2)
  | .gt => ⟨.gt,f c.2.1,0⟩

def liftMap (f : Nat → Nat) (n m q : Nat) := if q = n+1 then m+1 else f q

def transfer (f : Nat → Nat) (n m : Nat) (cs : List Choice) : List Choice × (Nat → Nat) :=
  match cs with
  | [] => ([],f)
  | c :: rest =>
    let (gs,last) := transfer (liftMap f n m) (n+1) (m+1) rest
    (remapGate f c :: gs,last)

def BoundedMap (m : Nat) (f : Nat → Nat) := f 0 = 0 ∧ ∀ q, f q ≤ m

private theorem lift_bounded {f : Nat → Nat} {n m : Nat} (h : BoundedMap m f) :
    BoundedMap (m+1) (liftMap f n m) := by
  refine ⟨by simp [liftMap, h.1], ?_⟩
  intro q
  have := h.2 q
  unfold liftMap; split <;> omega

private theorem remap_legal (c : Choice) {f : Nat → Nat} {m : Nat} (h : BoundedMap m f) :
    (remapGate f c).Legal m := by
  obtain ⟨op,l,r⟩ := c
  cases op <;> simp [remapGate, Choice.Legal, binary, h.2]

private theorem remap_mono {c : Choice} {f : Nat → Nat} {m : Nat} (h : BoundedMap m f)
    (hc : IsMonotone c) : IsMonotone (remapGate f c) := by
  obtain ⟨op,l,r⟩ := c
  cases op <;> simp_all [IsMonotone, remapGate, binary, h.1]

theorem transfer_valid (cs : List Choice) (f : Nat → Nat) (n m : Nat) (h : BoundedMap m f) :
    Valid m (transfer f n m cs).1 ∧ (transfer f n m cs).1.length = cs.length := by
  induction cs generalizing n m f with
  | nil => exact ⟨trivial,rfl⟩
  | cons c cs ih =>
    obtain ⟨hv,hl⟩ := ih _ _ _ (lift_bounded (n := n) h)
    exact ⟨⟨remap_legal _ h,hv⟩, congrArg Nat.succ hl⟩

theorem transfer_mono (cs : List Choice) (f : Nat → Nat) (n m : Nat) (h : BoundedMap m f)
    (hc : ∀ c ∈ cs, IsMonotone c) : ∀ g ∈ (transfer f n m cs).1, IsMonotone g := by
  induction cs generalizing n m f with
  | nil => simp [transfer]
  | cons c cs ih =>
    intro g hg
    rcases List.mem_cons.mp hg with rfl|hm
    · exact remap_mono h (hc _ List.mem_cons_self)
    · exact ih _ _ _ (lift_bounded (n := n) h) (fun a ha => hc _ (List.mem_cons_of_mem _ ha)) _ hm

def ReadsAs (f : Nat → Nat) (x y : List Bool) : Prop := ∀ q, read x q = read y (f q)

private theorem remap_eval {f : Nat → Nat} {x y : List Bool} (hr : ReadsAs f x y) (c : Choice) :
    (remapGate f c).eval y = c.eval x := by
  obtain ⟨op,l,r⟩ := c
  cases op <;> simp only [remapGate, Choice.eval, binary] <;>
    rcases le_total (f l) (f r) with h|h <;> simp [h, hr l, hr r, Bool.and_comm, Bool.or_comm]

private theorem read_append (x : List Bool) (q : Nat) (b : Bool) :
    read (x ++ [b]) q = if q = x.length+1 then b else read x q := by
  cases q with
  | zero => simp [CircuitSatBridge.read]
  | succ i =>
    simp only [CircuitSatBridge.read, Nat.add_right_cancel_iff]
    split
    · next h => subst i; simp
    · next h =>
      by_cases hi : i < x.length
      · exact List.getD_append _ _ _ _ hi
      · have he : x.length ≤ i := by omega
        rw [List.getD_append_right _ _ _ _ he, List.getD_eq_default _ _ he,
          List.getD_eq_default _ _ (by simp; omega)]

private theorem extend_reads {f : Nat → Nat} {x y : List Bool} (h : BoundedMap y.length f)
    (hr : ReadsAs f x y) (c : Choice) :
    ReadsAs (liftMap f x.length y.length) (x ++ [c.eval x]) (y ++ [(remapGate f c).eval y]) := by
  intro q
  have hq := h.2 q
  by_cases he : q = x.length+1
  · simp [read_append, liftMap, he, remap_eval hr]
  · simp [read_append, liftMap, he, show f q ≠ y.length+1 by omega, hr q]

theorem transfer_eval (cs : List Choice) (f : Nat → Nat) (x y : List Bool)
    (h : BoundedMap y.length f) (hr : ReadsAs f x y) :
    ReadsAs (transfer f x.length y.length cs).2 (runChoices cs x)
      (runChoices (transfer f x.length y.length cs).1 y) := by
  induction cs generalizing x y f with
  | nil => exact hr
  | cons c cs ih =>
    have hd := ih _ _ _ (show BoundedMap (y ++ [(remapGate f c).eval y]).length
        (liftMap f x.length y.length) by simpa using lift_bounded (n := x.length) h) (extend_reads h hr c)
    simpa [transfer, runChoices] using hd

end CircuitSatBridge

namespace CircuitSatBridge

def pull (f : Nat → Nat) (n : Nat) (y : List Bool) :=
  List.ofFn fun i : Fin n => read y (f (i.val+1))

theorem pull_len (f : Nat → Nat) (n : Nat) (y : List Bool) : (pull f n y).length = n := by
  simp [pull]

theorem pull_at (f : Nat → Nat) (n : Nat) (y : List Bool) (i : Nat) (hi : i < n) :
    (pull f n y).getD i false = read y (f (i+1)) := by
  simp [pull, List.getElem?_eq_getElem, hi]

def SourceMap (n m : Nat) (f : Nat → Nat) := BoundedMap m f ∧ ∀ i, n ≤ i → f (i+1) = 0

theorem pull_reads {n m : Nat} {f : Nat → Nat} (h : SourceMap n m f) (y : List Bool) :
    ReadsAs f (pull f n y) y := by
  intro q
  cases q with
  | zero => rw [h.1.1]; rfl
  | succ i =>
    by_cases hi : i < n
    · exact pull_at _ _ _ _ hi
    · rw [h.2 i (by omega)]
      change (pull f n y).getD i false = false
      exact List.getD_eq_default _ _ (by rw [pull_len]; omega)

theorem transfer_pull (cs : List Choice) {f : Nat → Nat} {n m : Nat} (h : SourceMap n m f)
    (y : List Bool) (hy : y.length = m) (out : Nat) :
    read (runChoices (transfer f n m cs).1 y) ((transfer f n m cs).2 (out+1)) =
      (runChoices cs (pull f n y)).getD out false := by
  have he := transfer_eval cs f (pull f n y) y (hy ▸ h.1) (pull_reads h y) (out+1)
  rw [pull_len,hy] at he
  exact he.symm

end CircuitSatBridge

namespace FreeSupport
open CircuitSatBridge

abbrev Word := BitVec 110
abbrev Wire := Word × Word

def sample (ws : List Wire) (t : Fin 110) (side : Bool) : List Bool :=
  ws.map fun (l,r) => (if side then r else l).getLsbD t.val

def wire (ws : List Wire) : Nat → Wire
  | 0 => (0,0)
  | i+1 => ws.getD i (0,0)

def evalW (c : Choice) (ws : List Wire) : Wire :=
  let (l,r) := wire ws c.2.1
  let (l',r') := wire ws c.2.2
  match c.1 with
  | .lt => (l &&& l',r &&& r')
  | .eq => (l ||| l',r ||| r')
  | .gt => (~~~l,~~~r)

def extend (c : Choice) (ws : List Wire) := ws ++ [evalW c ws]

private theorem sample_read (ws : List Wire) (t : Fin 110) (s : Bool) (q : Nat) :
    read (sample ws t s) q = (if s then (wire ws q).2 else (wire ws q).1).getLsbD t := by
  cases q with
  | zero => cases s <;> simp [CircuitSatBridge.read, wire]
  | succ i =>
    cases s <;> simp [CircuitSatBridge.read, sample, wire, List.getElem?_map] <;>
      cases ws[i]? <;> simp

theorem sample_extend (ws : List Wire) (t : Fin 110) (s : Bool) (c : Choice) :
    sample (extend c ws) t s = sample ws t s ++ [c.eval (sample ws t s)] := by
  obtain ⟨op,l,r⟩ := c
  have hl := sample_read ws t s l
  have hr := sample_read ws t s r
  cases op <;> cases s <;> simp_all [extend, sample, evalW, Choice.eval, Fin.is_lt]

def delta (ws : List Wire) (i : Nat) : Word :=
  let w := ws.getD i (0,0)
  w.1 ^^^ w.2

def unionD (ws : List Wire) (ix : List Nat) : Word :=
  (ix.map (delta ws)).foldr (· ||| ·) 0

theorem bit_union (ws : List Wire) (ix : List Nat) (t : Fin 110) :
    (unionD ws ix).getLsbD t = true ↔ ∃ i ∈ ix, (delta ws i).getLsbD t = true := by
  induction ix with
  | nil => simp [unionD]
  | cons i ix ih =>
    change ((delta ws i ||| unionD ws ix).getLsbD t = true) ↔ _
    simp only [BitVec.getLsbD_or, Bool.or_eq_true, ih, List.mem_cons, exists_eq_or_imp]

def cover (ws : List Wire) (k : Nat) : Bool :=
  decide (∃ s ∈ (Finset.range ws.length).powerset,
    s.card ≤ k ∧ unionD ws ((List.range ws.length).filter (fun i => i ∈ s)) = BitVec.allOnes 110)

def distinguished (cs : List Choice) (ws : List Wire) (out : Nat) : Prop :=
  ∀ t : Fin 110, (runChoices cs (sample ws t false)).getD out false ≠
                  (runChoices cs (sample ws t true)).getD out false

theorem suffix_cover (cs : List Choice) (ws : List Wire) (out : Nat)
    (h : distinguished cs ws out) : cover ws (cs.length+1) = true := by
  obtain ⟨s, hs, hcard, determ⟩ := bounded_support cs ws.length out
  have hbits (t : Fin 110) : ∃ i ∈ s, (delta ws i).getLsbD t = true := by
    by_contra! hn
    apply h t
    apply determ _ _ (by simp [sample]) (by simp [sample])
    intro i hi
    have hb := hn i hi
    have hii := Finset.mem_range.mp (hs hi)
    simp [delta, List.getElem?_eq_getElem hii] at hb
    simpa [sample, List.getElem?_eq_getElem hii] using hb
  have hu : unionD ws ((List.range ws.length).filter (fun i => i ∈ s)) = BitVec.allOnes 110 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain ⟨x,hx,hd⟩ := hbits ⟨i,hi⟩
    simpa only [BitVec.getLsbD_allOnes, decide_eq_true hi] using (bit_union ws ((List.range ws.length).filter (fun i => i ∈ s)) ⟨i,hi⟩).mpr
      ⟨x, by simp [hx, Finset.mem_range.mp (hs hx)], hd⟩
  exact decide_eq_true ⟨s, Finset.mem_powerset.mpr hs, hcard, hu⟩

end FreeSupport

namespace FreeSupport
open CircuitSatBridge

def scan (k : Nat) (acc : Word) (xs : List Word) : Bool :=
  match k, xs with
  | 0, _ | _, [] => acc == BitVec.allOnes 110
  | k+1, x :: rest => scan (k+1) acc rest || scan k (acc ||| x) rest

private theorem scan_complete (ws : List Wire) (s : Finset Nat) (ix : List Nat)
    (k : Nat) (acc : Word) (hk : (ix.filter (· ∈ s)).length ≤ k)
    (hu : acc ||| unionD ws (ix.filter (· ∈ s)) = BitVec.allOnes 110) :
    scan k acc (ix.map (delta ws)) = true := by
  induction ix generalizing acc k with
  | nil => cases k <;> simpa [scan, unionD] using hu
  | cons i ix ih =>
    cases k with
    | zero =>
      have hnil : ((i :: ix).filter (· ∈ s)) = [] := List.length_eq_zero_iff.mp (by omega)
      simpa [scan, hnil, unionD] using hu
    | succ k =>
      simp only [List.map_cons, scan, Bool.or_eq_true]
      by_cases h : i ∈ s
      · right
        apply ih k _ (by simpa [h] using hk)
        simpa only [List.filter_cons_of_pos (p := fun a => decide (a ∈ s)) (by simpa using h),
          unionD, List.map_cons, List.foldr_cons, BitVec.or_assoc] using hu
      · exact Or.inl (ih _ _ (by simpa [h] using hk) (by simpa [h] using hu))

def fastCover (ws : List Wire) (k : Nat) : Bool :=
  scan k 0 ((List.range ws.length).map (delta ws))

theorem fast_of_cover {ws : List Wire} {k : Nat} (h : cover ws k) : fastCover ws k := by
  obtain ⟨s, hs, hk, hu⟩ := of_decide_eq_true h
  apply scan_complete ws s
  · have hl : ((List.range ws.length).filter (· ∈ s)).toFinset = s := by
      ext i
      simp only [List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact and_iff_right_of_imp (fun hi => Finset.mem_range.mp (Finset.mem_powerset.mp hs hi))
    have hn := (List.nodup_range (n := ws.length)).filter (p := fun i => decide (i ∈ s))
    rwa [← List.toFinset_card_of_nodup hn, hl]
  · simpa using hu

def candidates (n : Nat) : List Choice :=
  (List.range (n+1)).flatMap fun l =>
    [(Choice.mk .gt l 0)] ++ ((List.range (n+1)).filter (l ≤ ·)).flatMap fun r =>
       [⟨.lt,l,r⟩,⟨.eq,l,r⟩]

theorem candidate_mem {c : Choice} {n : Nat} (h : c.Legal n) : c ∈ candidates n := by
  obtain ⟨op,l,r⟩ := c
  obtain ⟨hl, hr, ho⟩ := h
  change l ≤ n at hl
  change r ≤ n at hr
  apply List.mem_flatMap.mpr
  refine ⟨l,List.mem_range.mpr (by omega),?_⟩
  cases op <;> simp_all [List.mem_flatMap, List.mem_filter] <;> omega

def pass (ws : List Wire) (k : Nat) : List (List Wire) :=
  ((candidates ws.length).map (extend · ws)).filter (fastCover · k)

theorem extend_mem {c : Choice} {ws : List Wire} {cs : List Choice} {out : Nat}
    (hc : c.Legal ws.length) (h : distinguished (c :: cs) ws out) :
    extend c ws ∈ pass ws (cs.length+1) := by
  apply List.mem_filter.mpr
  refine ⟨List.mem_map.mpr ⟨c,candidate_mem hc,rfl⟩, fast_of_cover (suffix_cover cs _ out ?_)⟩
  intro t
  simpa only [sample_extend, runChoices, List.foldl_cons] using h t

end FreeSupport

namespace FreeSupport
open CircuitSatBridge

def residuals (k : Nat) (xs : List Word) (need : Word) : List Word :=
  match k, xs with
  | 0, _ | _, [] => [need]
  | k+1, x :: rest => residuals (k+1) rest need ++ residuals k rest (need &&& ~~~x)

private theorem scan_as_residual (xs : List Word) (k : Nat) (acc : Word) :
    scan k acc xs = ((residuals k xs (~~~acc)).any (· == 0)) := by
  have he (a : Word) : (a == BitVec.allOnes 110) = (~~~a == 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    constructor
    · rintro rfl; decide
    · intro h
      have hh := congrArg (fun x : Word => ~~~x) h
      simpa [BitVec.not_not] using hh
  induction xs generalizing k acc with
  | nil => cases k <;> simp only [scan,residuals,List.any_cons,List.any_nil,Bool.or_false,he]
  | cons x xs ih =>
    cases k with
    | zero => simp only [scan,residuals,List.any_cons,List.any_nil,Bool.or_false,he]
    | succ k =>
      simp [scan,residuals, ih, BitVec.not_or]

private theorem resid_append (xs : List Word) (x : Word) (k : Nat) (need : Word) :
    (residuals (k+1) (xs ++ [x]) need).any (· == 0) =
    ((residuals (k+1) xs need).any (· == 0) ||
      (residuals k xs need).any (fun m => m &&& ~~~x == 0)) := by
  induction xs generalizing k need with
  | nil => cases k <;> simp [residuals]
  | cons y ys ih =>
    cases k with
    | zero => simp only [List.cons_append, residuals, List.any_append, ih, List.any_cons, List.any_nil, Bool.or_false]; ac_rfl
    | succ k => simp only [List.cons_append, residuals, List.any_append, ih, List.any_cons, List.any_nil, Bool.or_false]; ac_rfl

def oldCols (ws : List Wire) : List Word := ws.map fun w => w.1 ^^^ w.2

private theorem cols_eq (ws : List Wire) :
    (List.range ws.length).map (delta ws) = oldCols ws := by
  apply List.ext_getElem
  · simp [oldCols]
  · intro i h₁ h₂
    have hi : i < ws.length := by simpa [oldCols] using h₂
    simp [oldCols, delta, List.getElem?_eq_getElem hi]

def next (ws : List Wire) (k : Nat) : List (List Wire) :=
  let cols := oldCols ws
  let already := (residuals (k+1) cols (BitVec.allOnes 110)).any (· == 0)
  let rest := (residuals k cols (BitVec.allOnes 110)).eraseDups
  (((candidates ws.length).map (evalW · ws)).eraseDups.filter fun w =>
    already || rest.any (fun m => m &&& ~~~(w.1 ^^^ w.2) == 0)).map (ws ++ [·])

theorem next_mem {c : Choice} {ws : List Wire} {k : Nat} (hc : c.Legal ws.length)
    (h : fastCover (extend c ws) (k+1)) : extend c ws ∈ next ws k := by
  let w := evalW c ws
  apply List.mem_map.mpr
  refine ⟨w,List.mem_filter.mpr ⟨?_,?_⟩,rfl⟩
  · apply List.mem_eraseDups.mpr
    exact List.mem_map.mpr ⟨c,candidate_mem hc,rfl⟩
  · unfold fastCover at h
    rw [cols_eq, scan_as_residual] at h
    change (residuals (k+1) (oldCols (ws ++ [w])) (~~~(0 : Word))).any (· == 0) = true at h
    have he : oldCols (ws ++ [w]) = oldCols ws ++ [w.1 ^^^ w.2] := by simp [oldCols]
    rw [he,resid_append] at h
    have hz : ~~~(0 : Word) = BitVec.allOnes 110 := rfl
    rw [hz] at h
    simpa only [Bool.or_eq_true, List.any_eq_true, List.mem_eraseDups, BitVec.not_zero] using h

end FreeSupport

namespace FreeSupport
open CircuitSatBridge

def Oriented (cs : List Choice) (ws : List Wire) (out : Nat) : Prop :=
  ∀ t : Fin 110, (runChoices cs (sample ws t false)).getD out false = true ∧
    (runChoices cs (sample ws t true)).getD out false = false

theorem distinguished_of_oriented {cs : List Choice} {ws : List Wire} {out : Nat}
    (h : Oriented cs ws out) : distinguished cs ws out := by
  intro t
  rw [(h t).1,(h t).2]
  decide

def attainable (k : Nat) (ws : List Wire) := ∃ cs : List Choice, ∃ o : Nat,
  cs.length = k ∧ Valid ws.length cs ∧ Oriented cs ws o

def wireMap (old new : List Wire) : Nat → Nat
  | 0 => 0
  | i+1 =>
    if hi : i < old.length then
      if old[i] ∈ new then new.idxOf old[i] + 1 else 0
    else 0

private theorem wireMap_ok (old new : List Wire) : SourceMap old.length new.length (wireMap old new) := by
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · intro q
    cases q with
    | zero => simp [wireMap]
    | succ i =>
      simp only [wireMap]
      split
      · split
        · next h => have := List.idxOf_lt_length_iff.mpr h; omega
        · omega
      · omega
  · intro i hi
    simp [wireMap, Nat.not_lt.mpr hi]

private theorem pull_sample {old new : List Wire} {i : Nat} (hi : i < old.length)
    (hm : old[i] ∈ new ∨ old[i] = (0,0)) (t : Fin 110) (s : Bool) :
    (pull (wireMap old new) old.length (sample new t s)).getD i false =
      (sample old t s).getD i false := by
  rw [pull_at _ _ _ _ hi]
  by_cases hin : old[i] ∈ new
  · cases s <;> simp [wireMap, hi, hin, CircuitSatBridge.read, sample,
      List.getElem?_idxOf hin]
  · have hz := hm.resolve_left hin
    have hmap : wireMap old new (i+1) = 0 := by simp only [wireMap, dif_pos hi, if_neg hin]
    rw [hmap]
    cases s <;> simp [CircuitSatBridge.read, sample, hi, hz]

theorem project_suffix {cs : List Choice} {old new : List Wire} {out : Nat} {s : Finset Nat}
    (hs : s ⊆ Finset.range old.length) (hd : Oriented cs old out)
    (det : ∀ x y : List Bool, x.length = old.length → y.length = old.length → agrees s x y →
      (runChoices cs x).getD out false = (runChoices cs y).getD out false)
    (hnew : ∀ i, (hi : i ∈ s) → old[i]'(Finset.mem_range.mp (hs hi)) ∈ new ∨
      old[i]'(Finset.mem_range.mp (hs hi)) = (0,0)) : attainable cs.length new := by
  let f := wireMap old new
  let moved := transfer f old.length new.length cs
  let q := moved.2 (out+1)
  have hf := wireMap_ok old new
  have he (t : Fin 110) (b : Bool) :
      read (runChoices moved.1 (sample new t b)) q =
      (runChoices cs (sample old t b)).getD out false := by
    rw [show read (runChoices moved.1 (sample new t b)) q =
      (runChoices cs (pull f old.length (sample new t b))).getD out false from
      transfer_pull cs hf _ (by simp [sample]) out]
    have hcol (i : Nat) (hi : i ∈ s) := pull_sample (Finset.mem_range.mp (hs hi)) (hnew i hi) t b
    exact det _ _ (pull_len ..) (by simp [sample]) hcol
  have hn : q ≠ 0 := by
    intro hz
    apply distinguished_of_oriented hd 0
    rw [← he, ← he, hz]
    rfl
  obtain ⟨hv,hl⟩ := transfer_valid cs f old.length new.length hf.1
  refine ⟨moved.1,q-1,hl,hv,?_⟩
  intro t
  have hq (x : List Bool) : x.getD (q-1) false = read x q := by
    cases h : q with
    | zero => contradiction
    | succ i => rfl
  change _ = true ∧ _ = false
  rw [hq, hq, he, he]
  exact hd t

end FreeSupport

namespace FreeSupport
open CircuitSatBridge

def key (w : Wire) : Nat := (w.1.toNat <<< 110) + w.2.toNat

def live (ws : List Wire) : List Wire :=
  ((ws.filter (· != (0,0))).dedup).insertionSort (fun a b => key a ≤ key b)

theorem mem_live (ws : List Wire) (w : Wire) :
    w ∈ live ws ↔ w ∈ ws ∧ w ≠ (0,0) := by simp [live]

theorem live_nodup (ws : List Wire) : (live ws).Nodup :=
  (List.perm_insertionSort _ _).nodup_iff.mpr (List.nodup_dedup _)

def coversAll (ws : List Wire) : Bool := ((oldCols ws).foldr (· ||| ·) 0) == BitVec.allOnes 110

theorem covers_of_attainable {k : Nat} {ws : List Wire} (h : attainable k ws) :
    coversAll ws = true := by
  obtain ⟨cs,out,_,_,hd⟩ := h
  obtain ⟨s, _, _, hu⟩ := of_decide_eq_true (suffix_cover cs ws out (distinguished_of_oriented hd))
  apply beq_iff_eq.mpr
  have he : (List.range ws.length).map (delta ws) = oldCols ws := by
    apply List.ext_getElem
    · simp [oldCols]
    · intro i _ hi
      have hj : i < ws.length := by simpa [oldCols] using hi
      simp [oldCols,delta,hj]
  rw [← he]
  change unionD ws (List.range ws.length) = _
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_allOnes, decide_eq_true hi]
  apply (bit_union _ _ ⟨i,hi⟩).mpr
  have hb := congrArg (fun (v : Word) => v.getLsbD i) hu
  simp only [BitVec.getLsbD_allOnes, decide_eq_true hi] at hb
  obtain ⟨j,hj,hd⟩ := (bit_union _ _ ⟨i,hi⟩).mp hb
  exact ⟨j,(List.mem_filter.mp hj).1,hd⟩

end FreeSupport

namespace FreeSupport
open CircuitSatBridge

def choose (n : Nat) (ws : List Wire) := List.sublistsLen (min n (live ws).length) (live ws)

private theorem pick_support {ws : List Wire} {indices : Finset Nat} {k : Nat}
    (hi : indices ⊆ Finset.range ws.length) (hk : indices.card ≤ k) :
    ∃ ys ∈ choose k ws, ∀ i, (h : i ∈ indices) →
      ws[i]'(Finset.mem_range.mp (hi h)) ∈ ys ∨ ws[i]'(Finset.mem_range.mp (hi h)) = (0,0) := by
  let pool := live ws
  let need := (indices.image (fun i => ws.getD i (0,0))).erase (0,0)
  have hh : need ⊆ pool.toFinset := by
    intro v hv
    obtain ⟨hn,hv⟩ := Finset.mem_erase.mp hv
    obtain ⟨i,h,rfl⟩ := Finset.mem_image.mp hv
    have hl := Finset.mem_range.mp (hi h)
    apply List.mem_toFinset.mpr
    apply (mem_live ..).mpr
    exact ⟨by simp [hl],hn⟩
  have hn : need.card ≤ k := (Finset.card_erase_le ..).trans (Finset.card_image_le.trans hk)
  have hp : pool.toFinset.card = pool.length := List.toFinset_card_of_nodup (live_nodup ws)
  obtain ⟨big,ha,hb,hc⟩ := Finset.exists_subsuperset_card_eq hh
    (le_min hn (hp ▸ Finset.card_le_card hh)) (by rw [hp]; exact min_le_right _ _)
  let ys := pool.filter (fun v => v ∈ big)
  have hy : ys.toFinset = big := by
    ext v
    simp only [ys, List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact and_iff_right_of_imp (fun h => List.mem_toFinset.mp (hb h))
  refine ⟨ys, List.mem_sublistsLen.mpr ⟨List.filter_sublist,?_⟩, ?_⟩
  · rw [← List.toFinset_card_of_nodup ((live_nodup ws).filter _),hy,hc]
  · intro i h
    by_cases hz : ws[i]'(Finset.mem_range.mp (hi h)) = (0,0)
    · exact Or.inr hz
    · left
      apply List.mem_toFinset.mp
      rw [hy]
      exact ha (Finset.mem_erase.mpr ⟨hz,Finset.mem_image.mpr
        ⟨i,h,by simp [Finset.mem_range.mp (hi h)]⟩⟩)

def wordDelta (w : Wire) := w.1 ^^^ w.2
def covered (ys : List Wire) : Word := (ys.map wordDelta).foldr (· ||| ·) 0

private theorem covered_live (ws : List Wire) : covered (live ws) = covered ws := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have mem (ys : List Wire) :
      (covered ys).getLsbD i = true ↔ ∃ w ∈ ys, (wordDelta w).getLsbD i = true := by
    induction ys with
    | nil => simp [covered]
    | cons w ys ih =>
      change (wordDelta w ||| covered ys).getLsbD i = true ↔ _
      simp only [BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]
  apply Bool.eq_iff_iff.mpr
  rw [mem,mem]
  constructor
  · rintro ⟨w,hw,hd⟩
    exact ⟨w,((mem_live ..).mp hw).1,hd⟩
  · rintro ⟨w,hw,hd⟩
    refine ⟨w, (mem_live ..).mpr ⟨hw,?_⟩,hd⟩
    rintro rfl
    simp [wordDelta] at hd

def gateValues (ws : List Wire) := ((candidates ws.length).map (evalW · ws)).eraseDups

def fastChildren (ws : List Wire) (k : Nat) : List (List Wire) :=
  let gs := gateValues ws
  let keep := (choose (k+1) ws).filter coversAll
  let added := (choose k ws).flatMap fun ys =>
    let old := covered ys
    (gs.filter (fun w => (wordDelta w ||| old) == BitVec.allOnes 110)).map
      (fun w => live (w :: ys))
  (keep ++ added).eraseDups

end FreeSupport

namespace FreeSupport
open CircuitSatBridge

theorem fast_complete {ws : List Wire} {k : Nat} (h : attainable (k+1) ws) :
    ∃ zs ∈ fastChildren ws k, attainable k zs := by
  obtain ⟨all,out,hl,hv,hd⟩ := h
  cases all with
  | nil => simp at hl
  | cons c cs =>
    have hk : cs.length = k := by simpa using hl
    let v := evalW c ws
    let old := ws ++ [v]
    have hd' : Oriented cs old out := by
      intro t
      simpa only [show old = extend c ws from rfl,sample_extend,runChoices,List.foldl_cons] using hd t
    obtain ⟨s,hs,hcard,det⟩ := bounded_support cs old.length out
    have hlen : old.length = ws.length + 1 := by simp [old]
    have hs' : s.erase ws.length ⊆ Finset.range ws.length := by
      intro i hi
      obtain ⟨hn,hi⟩ := Finset.mem_erase.mp hi
      have hb := Finset.mem_range.mp (hs hi)
      exact Finset.mem_range.mpr (by omega)
    have hval : v ∈ gateValues ws := by
      apply List.mem_eraseDups.mpr
      exact List.mem_map.mpr ⟨c,candidate_mem hv.1,rfl⟩
    have hread (i : Nat) (hi : i < ws.length) :
        old[i]'(by omega) = ws[i] := List.getElem_append_left hi
    have last : old[ws.length]'(by omega) = v := by simp [old]
    by_cases use : ws.length ∈ s
    · have small : (s.erase ws.length).card ≤ k := by
        rw [Finset.card_erase_of_mem use]; omega
      obtain ⟨ys,hys,hy⟩ := pick_support hs' small
      let zs := live (v :: ys)
      have hat : attainable k zs := by
        rw [← hk]
        apply project_suffix hs hd' det
        intro i hi
        by_cases hz : old[i]'(Finset.mem_range.mp (hs hi)) = (0,0)
        · exact Or.inr hz
        · left
          apply (mem_live ..).mpr
          refine ⟨?_,hz⟩
          by_cases eq : i = ws.length
          · subst i; simp [last]
          · have ins := Finset.mem_erase.mpr ⟨eq,hi⟩
            rw [hread i (Finset.mem_range.mp (hs' ins))] at hz ⊢
            exact List.mem_cons_of_mem _ ((hy _ ins).resolve_right hz)
      have covered' : covered zs = BitVec.allOnes 110 := eq_of_beq (covers_of_attainable hat)
      rw [show zs = live (v :: ys) from rfl, covered_live] at covered'
      refine ⟨zs,List.mem_eraseDups.mpr (List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨ys,hys,List.mem_map.mpr ⟨v,List.mem_filter.mpr ⟨hval,?_⟩,rfl⟩⟩)),hat⟩
      exact beq_iff_eq.mpr covered'
    · have small : (s.erase ws.length).card ≤ k+1 :=
        (Finset.card_erase_le ..).trans (hk ▸ hcard)
      obtain ⟨ys,hys,hy⟩ := pick_support hs' small
      have hat : attainable k ys := by
        rw [← hk]
        apply project_suffix hs hd' det
        intro i hi
        have neq : i ≠ ws.length := fun e => use (e ▸ hi)
        have ins := Finset.mem_erase.mpr ⟨neq,hi⟩
        rw [hread i (Finset.mem_range.mp (hs' ins))]
        exact hy _ ins
      exact ⟨ys,List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_filter.mpr
        ⟨hys,covers_of_attainable hat⟩)),hat⟩

end FreeSupport

namespace FreeSupport
def advance (states : List (List Wire)) (k : Nat) := (states.flatMap (fastChildren · k)).eraseDups
theorem advance_complete {states : List (List Wire)} {k : Nat}
    (h : ∃ ws ∈ states, attainable (k+1) ws) : ∃ ys ∈ advance states k, attainable k ys := by
  obtain ⟨ws,hw,ha⟩ := h
  obtain ⟨ys,hy,hb⟩ := fast_complete ha
  exact ⟨ys,List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨ws,hw,hy⟩),hb⟩

def fastExplore (k : Nat) (states : List (List Wire)) : Nat → List (List Wire)
  | 0 => states
  | d+1 => fastExplore (k-1) (advance states (k-1)) d

theorem fastExplore_complete (d k : Nat) (states : List (List Wire)) (hd : d ≤ k)
    (h : ∃ ws ∈ states, attainable k ws) :
    ∃ ws ∈ fastExplore k states d, attainable (k-d) ws := by
  induction d generalizing k states with
  | zero => exact h
  | succ d ih =>
    cases k with
    | zero => omega
    | succ k => simpa [fastExplore] using ih k (advance states k) (by omega) (advance_complete h)

theorem fast_exclude {k d : Nat} {ws : List Wire} (hd : d ≤ k)
    (h : fastExplore k [ws] d = []) : ¬ attainable k ws := by
  intro a
  obtain ⟨y,hy,_⟩ := fastExplore_complete d k [ws] hd ⟨ws,by simp,a⟩
  rw [h] at hy
  exact List.not_mem_nil hy
end FreeSupport

namespace CircuitSatBridge

private theorem and_le (a b c d : Bool) (ha : a ≤ c) (hb : b ≤ d) : (a && b) ≤ (c && d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all
private theorem or_le (a b c d : Bool) (ha : a ≤ c) (hb : b ≤ d) : (a || b) ≤ (c || d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

def belowOn (s : Finset Nat) (x y : List Bool) := ∀ i ∈ s, x.getD i false ≤ y.getD i false

theorem bounded_monotone_support (cs : List Choice) (n out : Nat) (hm : ∀ c ∈ cs, IsMonotone c) :
    ∃ s : Finset Nat, s ⊆ Finset.range n ∧ s.card ≤ cs.length+1 ∧
      ∀ x y : List Bool, x.length = n → y.length = n → belowOn s x y →
        (runChoices cs x).getD out false ≤ (runChoices cs y).getD out false := by
  induction cs generalizing n with
  | nil =>
    by_cases h : out < n
    · exact ⟨{out}, by simpa, by simp, fun x y _ _ ha => ha out (by simp)⟩
    · refine ⟨∅, by simp, by simp, ?_⟩
      intro x y hx hy _
      change x.getD out false ≤ y.getD out false
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  | cons c cs ih =>
    obtain ⟨s, hs, hcard, he⟩ := ih (n+1) (fun g hg => hm _ (List.mem_cons_of_mem _ hg))
    by_cases h : n ∈ s
    · let t := ({c.2.1-1, c.2.2-1} : Finset Nat).filter (· < n)
      refine ⟨s.erase n ∪ t, ?_, ?_, ?_⟩
      · intro i hi
        rcases Finset.mem_union.mp hi with h₁|h₂
        · obtain ⟨hne,his⟩ := Finset.mem_erase.mp h₁
          have hh := Finset.mem_range.mp (hs his)
          exact Finset.mem_range.mpr (by omega)
        · exact Finset.mem_range.mpr (Finset.mem_filter.mp h₂).2
      · have ht : t.card ≤ 2 := (Finset.card_filter_le _ _).trans
            ((Finset.card_insert_le _ _).trans (by simp))
        have hb := Finset.card_union_le (s.erase n) t
        rw [Finset.card_erase_of_mem h] at hb
        have hp := Finset.card_pos.mpr ⟨n,h⟩
        simp only [List.length_cons]
        omega
      · intro x y hx hy ha
        apply he _ _ (by simp [hx]) (by simp [hy])
        intro i hi
        have readEq (q : Nat) (hq : q = c.2.1 ∨ q = c.2.2) : read x q ≤ read y q := by
          cases q with
          | zero => exact le_rfl
          | succ q =>
            change x.getD q false ≤ y.getD q false
            by_cases hq' : q < n
            · apply ha
              apply Finset.mem_union_right
              apply Finset.mem_filter.mpr
              refine ⟨?_, hq'⟩
              rcases hq with hq|hq <;> simp [← hq]
            · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
        by_cases hi' : i = n
        · subst i
          have hl := readEq c.2.1 (Or.inl rfl)
          have hr := readEq c.2.2 (Or.inr rfl)
          have hmono := hm c List.mem_cons_self
          have ev : c.eval x ≤ c.eval y := by
            unfold Choice.eval
            cases he : c.1 with
            | lt => exact and_le _ _ _ _ hl hr
            | eq => exact or_le _ _ _ _ hl hr
            | gt => rw [hmono he]; exact le_rfl
          convert ev using 1
          · rw [← hx]; simp
          · rw [← hy]; simp
        · have hh := Finset.mem_range.mp (hs hi)
          rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
          exact ha _ (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hi',hi⟩))
    · refine ⟨s, ?_, by simp; omega, ?_⟩
      · intro i hi
        have hh := Finset.mem_range.mp (hs hi)
        have hn : i ≠ n := fun e => h (e ▸ hi)
        exact Finset.mem_range.mpr (by omega)
      · intro x y hx hy ha
        apply he _ _ (by simp [hx]) (by simp [hy])
        intro i hi
        have hh := Finset.mem_range.mp (hs hi)
        have hn : i ≠ n := fun e => h (e ▸ hi)
        rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact ha _ hi

end CircuitSatBridge

namespace CircuitSatBridge
def effectiveRight (c : Choice) := match c.1 with
  | .gt => c.2.1
  | _ => c.2.2

def gateCost (c : Choice) := match c.1 with
  | .gt => 0
  | _ => 1

def binaryCount : List Choice → Nat
  | [] => 0
  | c :: cs => gateCost c + binaryCount cs

theorem count_le_length (cs : List Choice) : binaryCount cs ≤ cs.length := by
  induction cs with
  | nil => decide
  | cons c cs ih => cases h : c.1 <;> simp [binaryCount,gateCost,h] <;> omega

theorem count_lt_of_nonmono {cs : List Choice} (hn : ¬ ∀ c ∈ cs, IsMonotone c) :
    binaryCount cs < cs.length := by
  induction cs with
  | nil => simp at hn
  | cons c cs ih =>
    by_cases h : IsMonotone c
    · have h' := ih (fun hm => hn (by simpa using And.intro h hm))
      cases he : c.1 <;> simp [binaryCount,gateCost,he] <;> omega
    · have hh := count_le_length cs
      cases he : c.1 <;> simp_all [IsMonotone,gateCost,binaryCount]

theorem bounded_unary_support (cs : List Choice) (n out : Nat) :
    ∃ s : Finset Nat, s ⊆ Finset.range n ∧ s.card ≤ binaryCount cs+1 ∧
      ∀ x y : List Bool, x.length = n → y.length = n → agrees s x y →
        (runChoices cs x).getD out false = (runChoices cs y).getD out false := by
  induction cs generalizing n with
  | nil =>
    by_cases h : out < n
    · exact ⟨{out}, by simpa, by simp [binaryCount], fun x y _ _ ha => ha out (by simp)⟩
    · refine ⟨∅, by simp, by simp [binaryCount], ?_⟩
      intro x y hx hy _
      change x.getD out false = y.getD out false
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  | cons c cs ih =>
    obtain ⟨s, hs, hcard, he⟩ := ih (n+1)
    by_cases h : n ∈ s
    · let t := ({c.2.1-1, effectiveRight c-1} : Finset Nat).filter (· < n)
      refine ⟨s.erase n ∪ t, ?_, ?_, ?_⟩
      · intro i hi
        rcases Finset.mem_union.mp hi with h₁|h₂
        · obtain ⟨hne,his⟩ := Finset.mem_erase.mp h₁
          have hh := Finset.mem_range.mp (hs his)
          exact Finset.mem_range.mpr (by omega)
        · exact Finset.mem_range.mpr (Finset.mem_filter.mp h₂).2
      · have ht : t.card ≤ gateCost c + 1 := by
          apply (Finset.card_filter_le _ _).trans
          cases hop : c.1 <;> simp [effectiveRight, gateCost, hop] <;>
            exact (Finset.card_insert_le _ _).trans (by simp)
        have hb := Finset.card_union_le (s.erase n) t
        rw [Finset.card_erase_of_mem h] at hb
        have hp := Finset.card_pos.mpr ⟨n,h⟩
        simp only [binaryCount]
        omega
      · intro x y hx hy ha
        apply he _ _ (by simp [hx]) (by simp [hy])
        intro i hi
        have readEq (q : Nat) (hq : q = c.2.1 ∨ q = effectiveRight c) : read x q = read y q := by
          cases q with
          | zero => rfl
          | succ q =>
            change x.getD q false = y.getD q false
            by_cases hq' : q < n
            · apply ha
              apply Finset.mem_union_right
              apply Finset.mem_filter.mpr
              refine ⟨?_, hq'⟩
              rcases hq with hq|hq <;> simp [← hq]
            · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
        by_cases hi' : i = n
        · subst i
          have ev : c.eval x = c.eval y := by
            unfold Choice.eval
            have hl := readEq _ (Or.inl rfl)
            have hr := readEq _ (Or.inr rfl)
            cases hop : c.1 <;> simp_all [effectiveRight]
          convert ev using 1
          · rw [← hx]; simp
          · rw [← hy]; simp
        · have hh := Finset.mem_range.mp (hs hi)
          rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
          exact ha _ (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hi',hi⟩))
    · refine ⟨s, ?_, by simp only [binaryCount]; omega, ?_⟩
      · intro i hi
        have hh := Finset.mem_range.mp (hs hi)
        have hn : i ≠ n := fun e => h (e ▸ hi)
        exact Finset.mem_range.mpr (by omega)
      · intro x y hx hy ha
        apply he _ _ (by simp [hx]) (by simp [hy])
        intro i hi
        have hh := Finset.mem_range.mp (hs hi)
        have hn : i ≠ n := fun e => h (e ▸ hi)
        rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact ha _ hi

end CircuitSatBridge

namespace SharpSupport
open FreeSupport CircuitSatBridge
private theorem pick_support {ws : List Wire} {indices : Finset Nat} {k : Nat}
    (hi : indices ⊆ Finset.range ws.length) (hk : indices.card ≤ k) :
    ∃ ys ∈ choose k ws, ∀ i, (h : i ∈ indices) →
      ws[i]'(Finset.mem_range.mp (hi h)) ∈ ys ∨ ws[i]'(Finset.mem_range.mp (hi h)) = (0,0) := by
  let pool := live ws
  let need := (indices.image (fun i => ws.getD i (0,0))).erase (0,0)
  have hh : need ⊆ pool.toFinset := by
    intro v hv
    obtain ⟨hn,hv⟩ := Finset.mem_erase.mp hv
    obtain ⟨i,h,rfl⟩ := Finset.mem_image.mp hv
    have hl := Finset.mem_range.mp (hi h)
    apply List.mem_toFinset.mpr
    apply (mem_live ..).mpr
    exact ⟨by simp [hl],hn⟩
  have hn : need.card ≤ k := (Finset.card_erase_le ..).trans (Finset.card_image_le.trans hk)
  have hp : pool.toFinset.card = pool.length := List.toFinset_card_of_nodup (live_nodup ws)
  obtain ⟨big,ha,hb,hc⟩ := Finset.exists_subsuperset_card_eq hh
    (le_min hn (hp ▸ Finset.card_le_card hh)) (by rw [hp]; exact min_le_right _ _)
  let ys := pool.filter (fun v => v ∈ big)
  have hy : ys.toFinset = big := by
    ext v
    simp only [ys, List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact and_iff_right_of_imp (fun h => List.mem_toFinset.mp (hb h))
  refine ⟨ys, List.mem_sublistsLen.mpr ⟨List.filter_sublist,?_⟩, ?_⟩
  · rw [← List.toFinset_card_of_nodup ((live_nodup ws).filter _),hy,hc]
  · intro i h
    by_cases hz : ws[i]'(Finset.mem_range.mp (hi h)) = (0,0)
    · exact Or.inr hz
    · left
      apply List.mem_toFinset.mp
      rw [hy]
      exact ha (Finset.mem_erase.mpr ⟨hz,Finset.mem_image.mpr
        ⟨i,h,by simp [Finset.mem_range.mp (hi h)]⟩⟩)

def diff (ord : Bool) (w : Wire) : Word :=
  if ord then w.1 &&& ~~~w.2 else w.1 ^^^ w.2

def coverage (ord : Bool) (ws : List Wire) : Word := (ws.map (diff ord)).foldr (· ||| ·) 0

private theorem bit_cover (ord : Bool) (ws : List Wire) (t : Fin 110) :
    (coverage ord ws).getLsbD t = true ↔ ∃ w ∈ ws, (diff ord w).getLsbD t = true := by
  induction ws with
  | nil => simp [coverage]
  | cons w ws ih =>
    change (diff ord w ||| coverage ord ws).getLsbD t = true ↔ _
    simp only [BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

def childrenUsing (ws : List Wire) (slots : Nat) (ord : Bool) : List (List Wire) :=
  let keep := (choose slots ws).filter (fun ys => coverage ord ys == BitVec.allOnes 110)
  let add := if slots = 0 then [] else (choose (slots-1) ws).flatMap fun ys =>
    let old := coverage ord ys
    ((gateValues ws).filter (fun w => (diff ord w ||| old) == BitVec.allOnes 110)).map
      (fun w => live (w :: ys))
  keep ++ add

private theorem select_support {ws : List Wire} {c : Choice} {cs : List Choice} {out slots : Nat}
    {ord : Bool} (hleg : c.Legal ws.length)
    (hd : Oriented cs (extend c ws) out) {s : Finset Nat}
    (hs : s ⊆ Finset.range (extend c ws).length) (bound : s.card ≤ slots)
    (det : ∀ x y : List Bool, x.length = (extend c ws).length → y.length = (extend c ws).length →
      agrees s x y → (runChoices cs x).getD out false = (runChoices cs y).getD out false)
    (bits : ∀ t : Fin 110, ∃ i, ∃ hi : i ∈ s,
      (diff ord ((extend c ws)[i]'(Finset.mem_range.mp (hs hi)))).getLsbD t = true) :
    ∃ zs ∈ childrenUsing ws slots ord, attainable cs.length zs := by
  let v := evalW c ws
  let old := extend c ws
  have hlen : old.length = ws.length+1 := by simp [old,extend]
  change s ⊆ Finset.range old.length at hs
  have hs' : s.erase ws.length ⊆ Finset.range ws.length := by
    intro i hi
    obtain ⟨hn,hi⟩ := Finset.mem_erase.mp hi
    have hb := Finset.mem_range.mp (hs hi)
    exact Finset.mem_range.mpr (by omega)
  have hval : v ∈ gateValues ws := List.mem_eraseDups.mpr (List.mem_map.mpr ⟨c,candidate_mem hleg,rfl⟩)
  have hread (i : Nat) (hi : i < ws.length) :
      old[i]'(by omega) = ws[i] := List.getElem_append_left hi
  have last : old[ws.length]'(by omega) = v := by simp [old,extend,v]
  have cov (ys : List Wire)
      (hc : ∀ i, (hi : i ∈ s) → old[i]'(Finset.mem_range.mp (hs hi)) ∈ ys ∨
        old[i]'(Finset.mem_range.mp (hs hi)) = (0,0)) : coverage ord ys = BitVec.allOnes 110 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [BitVec.getLsbD_allOnes,decide_eq_true hj]
    obtain ⟨i,hi,hbit⟩ := bits ⟨j,hj⟩
    change (diff ord (old[i]'(Finset.mem_range.mp (hs hi)))).getLsbD j = true at hbit
    rcases hc i hi with hm|hz
    · exact (bit_cover _ _ ⟨j,hj⟩).mpr ⟨_,hm,hbit⟩
    · rw [hz] at hbit
      cases ord <;> simp [diff] at hbit
  by_cases use : ws.length ∈ s
  · have pos := Finset.card_pos.mpr ⟨_,use⟩
    have small : (s.erase ws.length).card ≤ slots-1 := by rw [Finset.card_erase_of_mem use]; omega
    obtain ⟨ys,hys,hy⟩ := pick_support hs' small
    have hc (i : Nat) (hi : i ∈ s) :
        old[i]'(Finset.mem_range.mp (hs hi)) ∈ v :: ys ∨ old[i]'(Finset.mem_range.mp (hs hi)) = (0,0) := by
      by_cases eq : i = ws.length
      · subst i; simp [last]
      · have ins := Finset.mem_erase.mpr ⟨eq,hi⟩
        rw [hread i (Finset.mem_range.mp (hs' ins))]
        exact (hy i ins).imp (List.mem_cons_of_mem _) id
    refine ⟨live (v :: ys), ?_, project_suffix hs hd det ?_⟩
    · apply List.mem_append_right
      simp only [if_neg (show slots ≠ 0 by omega)]
      exact List.mem_flatMap.mpr ⟨ys,hys,List.mem_map.mpr
        ⟨v,List.mem_filter.mpr ⟨hval,beq_iff_eq.mpr (cov _ hc)⟩,rfl⟩⟩
    · intro i hi
      by_cases hz : old[i]'(Finset.mem_range.mp (hs hi)) = (0,0)
      · exact Or.inr hz
      · exact Or.inl ((mem_live ..).mpr ⟨(hc _ hi).resolve_right hz,hz⟩)
  · obtain ⟨ys,hys,hy⟩ := pick_support hs' ((Finset.card_erase_le ..).trans bound)
    have hc (i : Nat) (hi : i ∈ s) : old[i]'(Finset.mem_range.mp (hs hi)) ∈ ys ∨
        old[i]'(Finset.mem_range.mp (hs hi)) = (0,0) := by
      have neq : i ≠ ws.length := fun e => use (e ▸ hi)
      have ins := Finset.mem_erase.mpr ⟨neq,hi⟩
      rw [hread i (Finset.mem_range.mp (hs' ins))]
      exact hy _ ins
    exact ⟨ys,List.mem_append_left _ (List.mem_filter.mpr ⟨hys,beq_iff_eq.mpr (cov _ hc)⟩),
      project_suffix hs hd det hc⟩

def children (ws : List Wire) (k : Nat) :=
  childrenUsing ws k false ++ childrenUsing ws (k+1) true

theorem complete {ws : List Wire} {k : Nat} (ha : attainable (k+1) ws) :
    ∃ zs ∈ children ws k, attainable k zs := by
  obtain ⟨all,out,hlen,hv,hd⟩ := ha
  cases all with
  | nil => simp at hlen
  | cons c cs =>
    have hk : cs.length = k := by simpa using hlen
    subst k
    let old := extend c ws
    have ho : Oriented cs old out := by
      intro t
      simpa only [old,sample_extend,runChoices,List.foldl_cons] using hd t
    by_cases hm : ∀ g ∈ cs, IsMonotone g
    · obtain ⟨s,hs,hb,mono⟩ := bounded_monotone_support cs old.length out hm
      have eqdet (x y : List Bool) (hx : x.length = old.length) (hy : y.length = old.length)
          (h : agrees s x y) := le_antisymm (mono x y hx hy (fun i hi => (h i hi).le))
            (mono y x hy hx (fun i hi => (h i hi).ge))
      obtain ⟨zs,hz,hatt⟩ := select_support (ord := true) hv.1 ho hs hb eqdet (by
        intro t
        by_contra! hn
        have bad := mono (sample old t false) (sample old t true) (by simp [sample]) (by simp [sample]) (by
          intro i hi
          have hh := hn i hi
          have hin := Finset.mem_range.mp (hs hi)
          simp [sample,List.getElem?_eq_getElem hin]
          simpa [diff, t.isLt, Bool.le_iff_imp] using hh)
        rw [(ho t).1,(ho t).2] at bad
        contradiction)
      exact ⟨zs,List.mem_append_right _ hz,hatt⟩
    · obtain ⟨s,hs,hc,det⟩ := bounded_unary_support cs old.length out
      have hlt := count_lt_of_nonmono hm
      obtain ⟨zs,hz,hatt⟩ := select_support (ord := false) hv.1 ho hs (show s.card ≤ cs.length by omega) det (by
        intro t
        by_contra! hn
        apply distinguished_of_oriented ho t
        apply det _ _ (by simp [sample]) (by simp [sample])
        intro i hi
        have hh := hn i hi
        have hin := Finset.mem_range.mp (hs hi)
        simpa [sample,List.getElem?_eq_getElem hin,diff] using hh)
      exact ⟨zs,List.mem_append_left _ hz,hatt⟩
end SharpSupport

namespace FreeSupport
open CircuitSatBridge

theorem zero_wire {ws : List Wire} (ha : attainable 0 ws) :
    (BitVec.allOnes 110, (0 : Word)) ∈ ws := by
  obtain ⟨cs,out,hlen,_,h⟩ := ha
  have hnil := List.length_eq_zero_iff.mp hlen
  subst cs
  have hout : out < ws.length := by
    by_contra! hbad
    have hh := (h 0).1
    change (sample ws 0 false).getD out false = true at hh
    rw [List.getD_eq_default _ _ (by simpa [sample] using hbad)] at hh
    contradiction
  have hl : ws[out].1 = BitVec.allOnes 110 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_allOnes,decide_eq_true hi]
    have hh := (h ⟨i,hi⟩).1
    simpa [runChoices,sample,List.getElem?_eq_getElem hout] using hh
  have hr : ws[out].2 = (0 : Word) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hh := (h ⟨i,hi⟩).2
    simpa [runChoices,sample,List.getElem?_eq_getElem hout] using hh
  have he : ws[out] = (BitVec.allOnes 110, (0 : Word)) := Prod.ext hl hr
  exact he ▸ List.getElem_mem hout

end FreeSupport

namespace FourCheck
open FreeSupport CircuitSatBridge PEqualNP.Represents PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def excluded : Nat → List Wire → Bool
  | 0, ws => !(ws.contains (BitVec.allOnes 110, (0 : Word)))
  | k+1, ws => (SharpSupport.children ws k).eraseDups.all (excluded k)

theorem excluded_sound (k : Nat) (ws : List Wire) (h : excluded k ws) : ¬ attainable k ws := by
  induction k generalizing ws with
  | zero =>
    intro ha
    have hw := List.contains_iff_mem.mpr (zero_wire ha)
    change (!(ws.contains (BitVec.allOnes 110, (0 : Word)))) = true at h
    rw [hw] at h
    contradiction
  | succ k ih =>
    intro ha
    obtain ⟨zs, hz, hza⟩ := SharpSupport.complete ha
    exact ih zs (List.all_eq_true.mp h zs (List.mem_eraseDups.mpr hz)) hza

def graph (m : Nat) (i j : Fin 4) := m.testBit (4*i.val+j.val)

def Samples (ws : List Wire) (m : Nat) :=
  ∀ t : Fin 110, ∀ b : Bool, ∃ i j : Fin 4, sample ws t b = oneEach i j ∧ graph m i j = !b

theorem attainable_of_circuit (k : Nat) (m : Nat) (ws : List Wire) (hw : ws.length = 8)
    (hp : Samples ws m) (c : Circuit) (hc : FanInTwo c) (hs : c.size ≤ k)
    (hr : Represents (graph m) c) : attainable k ws := by
  cases k with
  | zero =>
    have hn : c.gates = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hs)
    refine ⟨[],c.output,rfl,trivial,?_⟩
    intro t
    have side (b : Bool) : (runChoices [] (sample ws t b)).getD c.output false = !b := by
      obtain ⟨i,j,he,hg⟩ := hp t b
      rw [he]
      have hh := (hr i j).trans hg
      simpa [Circuit.eval, Circuit.wires, hn, runChoices] using hh
    exact ⟨side false,side true⟩
  | succ k =>
    obtain ⟨cs,hl,hv,he⟩ := fixed_slots k 8 c.output c.gates hc hs
    refine ⟨cs,8+k,hl,hw ▸ hv,?_⟩
    intro t
    have side (b : Bool) : (runChoices cs (sample ws t b)).getD (8+k) false = !b := by
      obtain ⟨i,j,ha,hb⟩ := hp t b
      rw [ha]
      exact (he _ (by simp [oneEach])).trans ((hr i j).trans hb)
    exact ⟨side false,side true⟩

theorem refute (k m : Nat) (ws : List Wire) (hw : ws.length = 8) (hp : Samples ws m)
    (hx : excluded k ws) :
    ¬ ∃ c : Circuit, FanInTwo c ∧ c.size ≤ k ∧ Represents (graph m) c := by
  rintro ⟨c,hc,hs,hr⟩
  exact excluded_sound k ws hx (attainable_of_circuit k m ws hw hp c hc hs hr)
end FourCheck
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitSatBridge FreeSupport

def target (x : Fin 9 → Bool) : Bool := ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
def test (t : Fin 110) (b : Bool) : Fin 9 → Bool :=
  let pts : List Nat := if b then [219, 20, 438, 295, 186, 457, 17, 151, 151, 365, 160, 12, 63, 504, 455, 121, 219, 316, 484, 258, 68, 129, 186, 316, 151, 264, 295, 80, 455, 484, 63, 121, 438, 63, 257, 79, 186, 365, 484, 148, 79, 457, 66, 136, 457, 438, 101, 151, 219, 466, 316, 455, 365, 484, 504, 295, 96, 79, 504, 79, 121, 316, 438, 457, 33, 466, 132, 186, 295, 484, 121, 34, 47, 224, 217, 209, 418, 291, 484, 388, 63, 268, 323, 450, 63, 297, 466, 137, 198, 29, 391, 365, 151, 440, 147, 196, 74, 365, 164, 284, 504, 391, 30, 203, 338, 184, 284, 105, 78, 121] else [251, 84, 502, 359, 442, 473, 273, 159, 183, 493, 161, 140, 319, 505, 463, 123, 475, 317, 486, 266, 84, 161, 250, 444, 407, 266, 303, 84, 487, 500, 191, 125, 161, 127, 273, 111, 190, 367, 161, 212, 335, 459, 98, 140, 461, 446, 103, 215, 223, 498, 84, 471, 381, 492, 506, 311, 98, 95, 508, 207, 377, 318, 439, 489, 161, 467, 140, 187, 423, 485, 249, 98, 303, 225, 249, 465, 419, 307, 98, 396, 266, 396, 355, 458, 84, 299, 84, 141, 214, 157, 423, 273, 266, 441, 179, 212, 330, 140, 165, 348, 273, 407, 94, 235, 346, 185, 285, 107, 110, 98]
  fun i => (pts.getD t.val 0).testBit i.val
def wires : List FreeSupport.Wire := [((480317274089 <<< 0) + (272660863443 <<< 40) + (246705828 <<< 80), (201144259561 <<< 0) + (194642614739 <<< 40) + (681729717 <<< 80)), ((250572820893 <<< 0) + (487922060263 <<< 40) + (971068717 <<< 80), (117394985373 <<< 0) + (213041974181 <<< 40) + (299980125 <<< 80)), ((803118406542 <<< 0) + (554930454009 <<< 40) + (342788050 <<< 80), (1011290102670 <<< 0) + (829808098529 <<< 40) + (342794003 <<< 80)), ((252443359921 <<< 0) + (572518199611 <<< 40) + (533410475 <<< 80), (252375710257 <<< 0) + (22695269659 <<< 40) + (1054550707 <<< 80)), ((648168059383 <<< 0) + (190227865504 <<< 40) + (125365072 <<< 80), (634745237975 <<< 0) + (52788742048 <<< 40) + (660107857 <<< 80)), ((532389738269 <<< 0) + (515294753380 <<< 40) + (981754916 <<< 80), (497759467036 <<< 0) + (498106496096 <<< 40) + (706095153 <<< 80)), ((733237076527 <<< 0) + (338809552855 <<< 40) + (969507164 <<< 80), (449765040673 <<< 0) + (336662068055 <<< 40) + (965970252 <<< 80)), ((899559026613 <<< 0) + (680748936122 <<< 40) + (44492682 <<< 80), (898476893621 <<< 0) + (954267364282 <<< 40) + (45413832 <<< 80)), ((155550970492 <<< 0) + (795423865395 <<< 40) + (87637039 <<< 80), (434706997804 <<< 0) + (1031646019122 <<< 40) + (87698542 <<< 80)), ((29008048609 <<< 0) + (190225488256 <<< 40) + (103836160 <<< 80), (11828040129 <<< 0) + (52614398336 <<< 40) + (536891921 <<< 80)), ((296393221233 <<< 0) + (544581173766 <<< 40) + (730953773 <<< 80), (88221525105 <<< 0) + (269703529246 <<< 40) + (730947820 <<< 80))]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem samples : ∀ t : Fin 110, ∀ b : Bool,
    sample wires t b = run [⟨.and, [0, 4]⟩, ⟨.not, [2]⟩] (List.ofFn (test t b)) ∧ target (test t b) = !b := by decide +kernel

theorem attainable_suffix (rest : List Gate) (o : Nat)
    (hs : ∀ g ∈ rest, Supported g) (hlen : rest.length ≤ 9)
    (hfun : ∀ x : Fin 9 → Bool, (run ([⟨.and, [0, 4]⟩, ⟨.not, [2]⟩] ++ rest) (List.ofFn x)).getD o false = target x) :
    attainable 9 wires := by
  obtain ⟨cs,hl,hv,he⟩ := fixed_slots 8 11 o rest hs hlen
  refine ⟨cs,19,hl,?_,?_⟩
  · exact hv
  intro t
  have h (b : Bool) :
      (runChoices cs (sample wires t b)).getD 19 false = !b := by
    rw [(samples t b).1, he]
    · exact (hfun (test t b)).trans (samples t b).2
    · simp [run]
  exact ⟨h false, h true⟩

theorem stepCover {k : Nat} {ws : List FreeSupport.Wire} (dst : List (List FreeSupport.Wire))
    (hn : (SharpSupport.children ws k).all (fun t => dst.contains t) = true)
    (he : ∀ t ∈ dst, ¬ FreeSupport.attainable k t) : ¬ FreeSupport.attainable (k+1) ws := by
  intro h
  obtain ⟨t, ht, ha⟩ := SharpSupport.complete h
  exact he t (List.contains_iff_mem.mp (List.all_eq_true.mp hn t ht)) ha
def wire0 : FreeSupport.Wire := ((899559026613 <<< 0) + (680748936122 <<< 40) + (44492682 <<< 80), (898476893621 <<< 0) + (954267364282 <<< 40) + (45413832 <<< 80))
def wire1 : FreeSupport.Wire := ((155550970492 <<< 0) + (795423865395 <<< 40) + (87637039 <<< 80), (434706997804 <<< 0) + (1031646019122 <<< 40) + (87698542 <<< 80))
def wire2 : FreeSupport.Wire := ((250572820893 <<< 0) + (487922060263 <<< 40) + (971068717 <<< 80), (117394985373 <<< 0) + (213041974181 <<< 40) + (299980125 <<< 80))
def wire3 : FreeSupport.Wire := ((803118406542 <<< 0) + (554930454009 <<< 40) + (342788050 <<< 80), (1011290102670 <<< 0) + (829808098529 <<< 40) + (342794003 <<< 80))
def wire4 : FreeSupport.Wire := ((29008048609 <<< 0) + (190225488256 <<< 40) + (103836160 <<< 80), (11828040129 <<< 0) + (52614398336 <<< 40) + (536891921 <<< 80))
def wire5 : FreeSupport.Wire := ((648168059383 <<< 0) + (190227865504 <<< 40) + (125365072 <<< 80), (634745237975 <<< 0) + (52788742048 <<< 40) + (660107857 <<< 80))
def wire6 : FreeSupport.Wire := ((480317274089 <<< 0) + (272660863443 <<< 40) + (246705828 <<< 80), (201144259561 <<< 0) + (194642614739 <<< 40) + (681729717 <<< 80))
def wire7 : FreeSupport.Wire := ((532389738269 <<< 0) + (515294753380 <<< 40) + (981754916 <<< 80), (497759467036 <<< 0) + (498106496096 <<< 40) + (706095153 <<< 80))
def wire8 : FreeSupport.Wire := ((296393221233 <<< 0) + (544581173766 <<< 40) + (730953773 <<< 80), (88221525105 <<< 0) + (269703529246 <<< 40) + (730947820 <<< 80))
def wire9 : FreeSupport.Wire := ((733237076527 <<< 0) + (338809552855 <<< 40) + (969507164 <<< 80), (449765040673 <<< 0) + (336662068055 <<< 40) + (965970252 <<< 80))
def wire10 : FreeSupport.Wire := ((252443359921 <<< 0) + (572518199611 <<< 40) + (533410475 <<< 80), (252375710257 <<< 0) + (22695269659 <<< 40) + (1054550707 <<< 80))
def node1_0 : List FreeSupport.Wire := [wire0, wire1, wire5, wire6, wire3, wire10, wire9, wire2, wire7]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_0 : ¬ FreeSupport.attainable 8 node1_0 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject0_wires : ¬ FreeSupport.attainable 9 wires := by
  apply stepCover [node1_0] (by decide +kernel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl
  · exact reject1_node1_0

end PEqualNP.Outside.L_meta_27189_aux

theorem PEqualNP.Outside.L_meta_27189 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [2]⟩) := by
  rintro ⟨⟨gs,o⟩,hf,hs,hr,_,_,_,_,hfirst,hsecond⟩
  cases gs with
  | nil => contradiction
  | cons g gs =>
    cases gs with
    | nil => contradiction
    | cons h rest =>
      change some g = some ⟨.and, [0, 4]⟩ at hfirst
      change some h = some ⟨.not, [2]⟩ at hsecond
      obtain rfl := Option.some.inj hfirst
      obtain rfl := Option.some.inj hsecond
      apply PEqualNP.Outside.L_meta_27189_aux.reject0_wires
      apply PEqualNP.Outside.L_meta_27189_aux.attainable_suffix rest o
      · intro g hg
        apply hf
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hg)
      · change (rest.length + 1 + 1) ≤ 11 at hs
        omega
      · exact hr
