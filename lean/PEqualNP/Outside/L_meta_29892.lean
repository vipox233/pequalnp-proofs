import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Sublists
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29892_aux

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

open PEqualNP.CircuitLowerBounds

def bank (a b : Nat) (x : Fin 128) : List Bool :=
  [false, x.val.testBit 1, x.val.testBit 2, x.val.testBit 3, x.val.testBit 4, x.val.testBit 5, x.val.testBit 6,
   x.val.testBit a && x.val.testBit b, x.val.testBit 0 || (x.val.testBit a && x.val.testBit b)]

def target (x : Fin 128) : Bool :=
  ((x.val.testBit 0 && x.val.testBit 1) || (x.val.testBit 1 && x.val.testBit 2) ||
   (x.val.testBit 2 && x.val.testBit 3) || (x.val.testBit 3 && x.val.testBit 4) ||
   (x.val.testBit 4 && x.val.testBit 5) || (x.val.testBit 5 && x.val.testBit 6) ||
   (x.val.testBit 6 && x.val.testBit 0))

def mkSampleWire (a b c d e f : FreeSupport.Word) : FreeSupport.Wire :=
  (a + (b <<< 40) + (c <<< 80), d + (e <<< 40) + (f <<< 80))

theorem rejectNil (k : Nat) : ∀ t ∈ ([] : List (List FreeSupport.Wire)), ¬ FreeSupport.attainable k t := by simp

theorem rejectCons {k : Nat} {w : List FreeSupport.Wire} {ws : List (List FreeSupport.Wire)}
    (hw : ¬ FreeSupport.attainable k w) (hs : ∀ t ∈ ws, ¬ FreeSupport.attainable k t) :
    ∀ t ∈ w :: ws, ¬ FreeSupport.attainable k t := by
  intro t ht
  rcases List.mem_cons.mp ht with rfl | hh
  · exact hw
  · exact hs t hh

theorem stepCover {k : Nat} {ws : List FreeSupport.Wire} (dst : List (List FreeSupport.Wire))
    (hn : (SharpSupport.children ws k).all (fun t => dst.contains t) = true)
    (he : ∀ t ∈ dst, ¬ FreeSupport.attainable k t) : ¬ FreeSupport.attainable (k+1) ws := by
  intro h
  obtain ⟨t, ht, ha⟩ := SharpSupport.complete h
  exact he t (List.contains_iff_mem.mp (List.all_eq_true.mp hn t ht)) ha

namespace Case23
open CircuitSatBridge FreeSupport PEqualNP.CircuitLowerBounds
def w0 := mkSampleWire 0 0 0 0 0 0
def w1 := mkSampleWire 201588736 401 0 0 0 0
def w2 := mkSampleWire 854699671552 137908748288 25493578 0 0 0
def w3 := mkSampleWire 854901260288 137908748689 25493578 0 0 0
def w4 := mkSampleWire 137438987457 68721119264 68157476 0 0 0
def w5 := mkSampleWire 137640576193 68721119665 68157476 0 0 0
def w6 := mkSampleWire 2189492242 45105615876 134750465 0 0 0
def w7 := mkSampleWire 139628479699 113826665508 202907941 0 0 0
def w8 := mkSampleWire 139830068435 113826665909 202907941 0 0 0
def w9 := mkSampleWire 2650116 585191793728 408978944 0 0 0
def w10 := mkSampleWire 2192142358 595937670212 409511681 0 0 0
def w11 := mkSampleWire 104689827880 567495641096 536893568 0 0 0
def w12 := mkSampleWire 289409792 279294542338 570556432 0 0 0
def w13 := mkSampleWire 104979237672 846769211914 570579088 0 0 0
def w14 := mkSampleWire 854989081344 417136148994 596050010 0 0 0
def w15 := mkSampleWire 855190670080 417136149395 596050010 0 0 0
def w16 := mkSampleWire 104692477996 602929523784 945872512 0 0 0
def w17 := mkSampleWire 0 1125913088 100663296 18128841796 1125388316 0
def w18 := mkSampleWire 0 11140123648 589888 457414132256 8858422467 64
def w19 := mkSampleWire 0 560596058624 139520 619671589008 551972569632 256
def w20 := mkSampleWire 0 550848167936 2099744 17985176580 18087956 2560
def w21 := mkSampleWire 0 10806675456 20480 449915519504 10806673505 16384
def w22 := mkSampleWire 0 10741729280 1057168 448824082944 8589983809 1056912
def w23 := mkSampleWire 201588736 550863442833 2097664 618723817664 550863180296 2097152
def w24 := mkSampleWire 137640576193 619584492465 70255140 618723817664 550863180296 2097152
def w25 := mkSampleWire 0 404769792 8442888 8590049312 268438658 8393728
def w26 := mkSampleWire 201588736 10806625681 17597440 1091436560 2216689696 17334272
def w27 := mkSampleWire 854901260288 148648265105 26051658 1091436560 2216689696 17334272
def w28 := mkSampleWire 854901260288 137841608081 26051658 8590049312 137707392130 25728064
def w29 := mkSampleWire 854901260288 148648283537 26072138 458505568816 148514065635 25744448
def w30 := mkSampleWire 992340247745 217369402801 94229614 458505568816 148514065635 25744448
def w31 := mkSampleWire 857090752530 183016480149 160298315 458505568816 148514065635 25744448
def w32 := mkSampleWire 854903910404 733837979089 435017290 458505568816 148514065635 25744448
def w33 := mkSampleWire 959591088168 716141809049 562945226 458505568816 148514065635 25744448
def w34 := mkSampleWire 855190670080 427875684243 596628570 458505568816 148514065635 25744448
def w35 := mkSampleWire 854901260288 148652543377 27129306 458505568816 148514065635 26801360
def w36 := mkSampleWire 0 549806211584 34605056 618580152448 549755879936 33554432
def w37 := mkSampleWire 104979237672 857506695690 571636112 1068495671952 852620329569 34627984
def w38 := mkSampleWire 105180826408 857506696091 571636112 1068495671952 852620329569 34627984
def w39 := mkSampleWire 959678909224 995348302346 597129690 1068495671952 852620329569 34627984
def w40 := mkSampleWire 959880497960 995348302747 597129690 1068495671952 852620329569 34627984
def w41 := mkSampleWire 242418225129 926227749418 638745012 1068495671952 852620329569 34627984
def w42 := mkSampleWire 107168729914 891874827790 706378129 1068495671952 852620329569 34627984
def w43 := mkSampleWire 104981887788 892940578378 980615056 1068495671952 852620329569 34627984
def w44 := mkSampleWire 137640576193 619601269681 103811620 636708994244 619600744988 35654144
def w45 := mkSampleWire 992340247745 757510017969 129305198 636708994244 619600744988 35654144
def w46 := mkSampleWire 139830068435 664706815925 238562085 636708994244 619600744988 35654144
def w47 := mkSampleWire 137643226309 653963245553 510692900 636708994244 619600744988 35654144
def w48 := mkSampleWire 242330404073 637324319673 640703140 636708994244 619600744988 35654144
def w49 := mkSampleWire 137929985985 898845479859 640813620 636708994244 619600744988 35654144
def w50 := mkSampleWire 242619813865 927301753787 640842676 1086624513748 922465194621 36727696
def w51 := mkSampleWire 105180826408 857506697115 589233552 1068495671952 852620329569 51962256
def w52 := mkSampleWire 959880497960 995348303771 597687770 1077085721264 990327721699 60356048
def w53 := mkSampleWire 992340247745 768249552817 129883758 1095214563060 768114810623 61398592
def w54 := mkSampleWire 0 34768195584 67174480 4297064715 34498674944 67174400
def w55 := mkSampleWire 0 34768178176 134217888 12887114027 34767113602 134217760
def w56 := mkSampleWire 244522546431 646940159485 137953189 1077085721264 1059592597219 196673525
def w57 := mkSampleWire 139628479699 114233564196 202973685 461711196971 43357097411 202449141
def w58 := mkSampleWire 139830068435 114233564597 202973685 461711196971 43357097411 202449141
def w59 := mkSampleWire 994328151251 251739626532 228401663 461711196971 43357097411 202449141
def w60 := mkSampleWire 139631129815 665065618532 477734901 461711196971 43357097411 202449141
def w61 := mkSampleWire 244318307579 681724992556 739867125 461711196971 43357097411 202449141
def w62 := mkSampleWire 139917889491 393523879462 773530101 461711196971 43357097411 202449141
def w63 := mkSampleWire 139628479699 114235661348 211416573 461711196971 43357097411 210842869
def w64 := mkSampleWire 994529739987 251741724085 228455935 462802633531 183012740579 228193525
def w65 := mkSampleWire 244607717371 960998530606 773552629 1081382785979 887387443171 236020213
def w66 := mkSampleWire 139830068435 665113714613 238627829 1098420191215 662957842399 238103285
def w67 := mkSampleWire 0 35534410240 289800192 143665216 1107300360 268828672
def w68 := mkSampleWire 2192142358 596038334020 426682113 619815254224 553088266792 288260352
def w69 := mkSampleWire 2393731094 596038334421 426682113 619815254224 553088266792 288260352
def w70 := mkSampleWire 857093402646 733879973845 435136331 619815254224 553088266792 288260352
def w71 := mkSampleWire 139832718551 664759384053 494839589 619815254224 553088266792 288260352
def w72 := mkSampleWire 107083558974 613776064477 963575681 619815254224 553088266792 288260352
def w73 := mkSampleWire 2683140886 875232212951 997107473 619815254224 553088266792 288260352
def w74 := mkSampleWire 857093402646 733879992277 435156811 1077229386480 699385642731 296670528
def w75 := mkSampleWire 137640576193 654028116913 393611812 636708994244 619600744988 304482816
def w76 := mkSampleWire 2393731094 596055111637 461287169 619815254224 553088266792 321814784
def w77 := mkSampleWire 139832718551 664776161269 528396069 637800430804 621825831484 321817344
def w78 := mkSampleWire 107372968766 892948971487 998178705 1068639337168 853736026729 322888080
def w79 := mkSampleWire 994819149779 496177877943 119480663 1068639337168 1064189424233 390062551
def w80 := mkSampleWire 139832718551 665166282741 494905333 1081526451195 596445364203 490709493
def w81 := mkSampleWire 0 35858939904 817889288 22282241295 34516762900 541065224
def w82 := mkSampleWire 104692477996 603333749832 954261160 30872290607 35322203542 683679272
def w83 := mkSampleWire 104894066732 603333750233 954261160 30872290607 35322203542 683679272
def w84 := mkSampleWire 106881970238 614079626316 954793897 30872290607 35322203542 683679272
def w85 := mkSampleWire 959392149548 740839844936 971366122 30872290607 35322203542 683679272
def w86 := mkSampleWire 104981887788 882607320650 987946680 30872290607 35322203542 683679272
def w87 := mkSampleWire 242131465453 672053296232 1022418604 30872290607 35322203542 683679272
def w88 := mkSampleWire 959593738284 751577263577 971890410 480787810111 183567830519 701029992
def w89 := mkSampleWire 104981887788 893344804426 989003704 1099367962559 887942533111 718307256
def w90 := mkSampleWire 242333054189 672086851577 1055973036 649596108271 654904860574 719330856
def w91 := mkSampleWire 104692477996 603333786696 1021435640 30872290607 35322203542 750853672
def w92 := mkSampleWire 244320957695 682799135852 1023016957 479696373551 43912187351 751910653
def w93 := mkSampleWire 1097117896681 503473293354 647059710 479696373551 546423360983 785481471
def w94 := mkSampleWire 959883148076 985278063579 870768138 637800430804 1056154530364 871292682
def w95 := mkSampleWire 854989081344 452571468290 935788634 22425906511 39919030556 877068298
def w96 := mkSampleWire 855190670080 452571468691 935788634 22425906511 39919030556 877068298
def w97 := mkSampleWire 959678909224 1020046137866 935811290 22425906511 39919030556 877068298
def w98 := mkSampleWire 992428068801 521291010594 936837246 22425906511 39919030556 877068298
def w99 := mkSampleWire 857178573586 463317341702 1070539099 22425906511 39919030556 877068298
def w100 := mkSampleWire 854991731460 1002329519682 1072137818 22425906511 39919030556 877068298
def w101 := mkSampleWire 854989081344 1002327282178 937888378 22425906511 39919030556 877070858
def w102 := mkSampleWire 857382812438 1013075392471 1072670555 642097495519 591899996988 896499978
def w103 := mkSampleWire 855190670080 463311003539 936367194 480931475327 188433096191 902812746
def w104 := mkSampleWire 959678909224 1030783621642 936868314 1090921578463 892539360125 911696282
def w105 := mkSampleWire 992629657537 1071046824883 938936958 641006058959 658394387228 912722442
def w106 := mkSampleWire 107083558974 614180290525 971964329 650687544831 588410470334 971939624
def w107 := mkSampleWire 994617561043 532036836902 1071587839 479840038767 48777453023 1012343039
def w108 := mkSampleWire 107171380030 331262074958 943858065 4297064715 331396817152 1012343231
def w109 := mkSampleWire 959681559340 1020046278218 1072160506 31015955823 40724471198 1019682346
def w110 := mkSampleWire 961871051582 479910358094 969930203 462802633531 479910882787 1038087679
def w111 := mkSampleWire 994532390103 242004932085 502105711 31015955823 246891298206 1039113839
def w112 := mkSampleWire 244610367487 950863344238 1047669685 641006058959 950997562140 1047997375
def w113 := mkSampleWire 1099310039039 1099511627374 1073741823 1099511627775 1099511627775 1073741823
def w114 := mkSampleWire 1099511627775 1099511627775 1073741823 1099511627775 1099511627775 1073741823
def wires : List Wire := [w0, w57, w44, w29, w95, w37, w82, w1, w69]
def n1_0 : List Wire := [w1, w2, w44, w57, w69, w37, w95, w82]
def n1_1 : List Wire := [w1, w29, w4, w57, w69, w37, w95, w82]
def n1_2 : List Wire := [w1, w29, w44, w57, w69, w37, w95, w82]
def n1_3 : List Wire := [w1, w29, w44, w57, w69, w37, w95, w83]
def n1_4 : List Wire := [w1, w29, w44, w57, w69, w37, w96, w82]
def n1_5 : List Wire := [w1, w29, w44, w57, w69, w38, w95, w82]
def n1_6 : List Wire := [w1, w29, w44, w58, w69, w37, w95, w82]
def n1_7 : List Wire := [w1, w29, w57, w69, w77, w37, w95, w82]
def n1_8 : List Wire := [w1, w44, w57, w69, w37, w52, w95, w82]
def n1_9 : List Wire := [w1, w53, w57, w69, w37, w95, w82]
def n1_10 : List Wire := [w2, w29, w44, w57, w69, w37, w95, w82]
def n1_11 : List Wire := [w2, w44, w57, w69, w37, w95, w82]
def n1_12 : List Wire := [w18, w29, w44, w57, w69, w37, w95, w82]
def n1_13 : List Wire := [w19, w29, w44, w57, w69, w37, w95, w82]
def n1_14 : List Wire := [w20, w29, w44, w57, w69, w37, w95, w82]
def n1_15 : List Wire := [w21, w29, w44, w57, w69, w37, w95, w82]
def n1_16 : List Wire := [w22, w29, w44, w57, w69, w37, w95, w82]
def n1_17 : List Wire := [w23, w29, w44, w57, w69, w37, w95, w82]
def n1_18 : List Wire := [w25, w29, w44, w57, w69, w37, w95, w82]
def n1_19 : List Wire := [w26, w29, w44, w57, w69, w37, w95, w82]
def n1_20 : List Wire := [w29, w4, w44, w57, w69, w37, w95, w82]
def n1_21 : List Wire := [w29, w4, w57, w69, w37, w95, w82]
def n1_22 : List Wire := [w29, w17, w44, w57, w69, w37, w95, w82]
def n1_23 : List Wire := [w29, w36, w44, w57, w69, w37, w95, w82]
def n1_24 : List Wire := [w29, w44, w6, w57, w69, w37, w95, w82]
def n1_25 : List Wire := [w29, w44, w53, w57, w69, w37, w95, w82]
def n1_26 : List Wire := [w29, w44, w55, w57, w69, w37, w95, w82]
def n1_27 : List Wire := [w29, w44, w56, w57, w69, w37, w82]
def n1_28 : List Wire := [w29, w44, w56, w57, w69, w37, w95, w82]
def n1_29 : List Wire := [w29, w44, w57, w9, w69, w37, w95, w82]
def n1_30 : List Wire := [w29, w44, w57, w37, w93, w95, w82]
def n1_31 : List Wire := [w29, w44, w57, w58, w69, w37, w95, w82]
def n1_32 : List Wire := [w29, w44, w57, w64, w69, w37, w95, w82]
def n1_33 : List Wire := [w29, w44, w57, w66, w69, w37, w95, w82]
def n1_34 : List Wire := [w29, w44, w57, w67, w69, w37, w95, w82]
def n1_35 : List Wire := [w29, w44, w57, w69, w11, w37, w95, w82]
def n1_36 : List Wire := [w29, w44, w57, w69, w12, w37, w95, w82]
def n1_37 : List Wire := [w29, w44, w57, w69, w37, w38, w95, w82]
def n1_38 : List Wire := [w29, w44, w57, w69, w37, w50, w95, w82]
def n1_39 : List Wire := [w29, w44, w57, w69, w37, w52, w95, w82]
def n1_40 : List Wire := [w29, w44, w57, w69, w37, w65, w95, w82]
def n1_41 : List Wire := [w29, w44, w57, w69, w37, w81, w95, w82]
def n1_42 : List Wire := [w29, w44, w57, w69, w37, w93, w95, w82]
def n1_43 : List Wire := [w29, w44, w57, w69, w37, w94, w95, w82]
def n2_27 : List Wire := [w29, w44, w57, w69, w37, w95, w82]
def n1_45 : List Wire := [w29, w44, w57, w69, w37, w95, w82, w78]
def n1_46 : List Wire := [w29, w44, w57, w69, w37, w95, w82, w83]
def n1_47 : List Wire := [w29, w44, w57, w69, w37, w95, w82, w88]
def n1_48 : List Wire := [w29, w44, w57, w69, w37, w95, w82, w89]
def n1_49 : List Wire := [w29, w44, w57, w69, w37, w95, w82, w90]
def n1_50 : List Wire := [w29, w44, w57, w69, w37, w95, w82, w92]
def n1_51 : List Wire := [w29, w44, w57, w69, w37, w95, w82, w102]
def n1_52 : List Wire := [w29, w44, w57, w69, w37, w95, w82, w106]
def n1_53 : List Wire := [w29, w44, w57, w69, w37, w95, w82, w107]
def n1_54 : List Wire := [w29, w44, w57, w69, w37, w95, w82, w109]
def n1_55 : List Wire := [w29, w44, w57, w69, w37, w95, w82, w110]
def n1_56 : List Wire := [w29, w44, w57, w69, w37, w95, w82, w112]
def n1_57 : List Wire := [w29, w44, w57, w69, w37, w95, w82, w113]
def n1_58 : List Wire := [w29, w44, w57, w69, w37, w95, w82, w114]
def n2_28 : List Wire := [w29, w44, w57, w69, w37, w95, w83]
def n1_60 : List Wire := [w29, w44, w57, w69, w37, w95, w96, w82]
def n1_61 : List Wire := [w29, w44, w57, w69, w37, w95, w103, w82]
def n1_62 : List Wire := [w29, w44, w57, w69, w37, w95, w104, w82]
def n1_63 : List Wire := [w29, w44, w57, w69, w37, w95, w105, w82]
def n2_34 : List Wire := [w29, w44, w57, w69, w37, w96, w82]
def n2_39 : List Wire := [w29, w44, w57, w69, w38, w95, w82]
def n1_66 : List Wire := [w29, w44, w57, w69, w74, w37, w95, w82]
def n1_67 : List Wire := [w29, w44, w57, w69, w77, w37, w95, w82]
def n1_68 : List Wire := [w29, w44, w57, w69, w80, w37, w95, w82]
def n1_69 : List Wire := [w29, w44, w57, w69, w111, w37, w95, w82]
def n1_70 : List Wire := [w29, w44, w57, w69, w111, w95, w82]
def n2_50 : List Wire := [w29, w44, w58, w69, w37, w95, w82]
def n1_72 : List Wire := [w29, w44, w69, w37, w94, w95, w82]
def n1_73 : List Wire := [w29, w44, w79, w57, w69, w37, w95]
def n1_74 : List Wire := [w29, w44, w79, w57, w69, w37, w95, w82]
def n1_75 : List Wire := [w29, w53, w57, w69, w37, w95, w82]
def n1_76 : List Wire := [w29, w54, w44, w57, w69, w37, w95, w82]
def n1_77 : List Wire := [w29, w57, w69, w37, w95, w82, w110]
def n1_78 : List Wire := [w29, w57, w69, w77, w37, w95, w82]
def n1_79 : List Wire := [w44, w53, w57, w69, w37, w95, w82]
def n1_80 : List Wire := [w44, w57, w69, w37, w52, w95, w82]
def n1_81 : List Wire := [w44, w57, w69, w37, w95, w82, w112]
def n2_0 : List Wire := [w1, w29, w7, w69, w37, w95, w82]
def n2_1 : List Wire := [w1, w29, w57, w71, w37, w95, w82]
def n2_2 : List Wire := [w1, w44, w57, w69, w37, w14, w82]
def n2_3 : List Wire := [w1, w44, w57, w69, w39, w95, w82]
def n2_4 : List Wire := [w2, w44, w57, w69, w37, w95, w83]
def n2_5 : List Wire := [w2, w44, w58, w69, w37, w95, w82]
def n2_6 : List Wire := [w3, w44, w57, w69, w37, w95, w82]
def n2_7 : List Wire := [w3, w44, w57, w69, w37, w96, w82]
def n2_8 : List Wire := [w27, w44, w57, w69, w37, w95, w82]
def n2_9 : List Wire := [w28, w44, w57, w69, w37, w95, w82]
def n2_10 : List Wire := [w29, w4, w57, w69, w37, w95, w83]
def n2_11 : List Wire := [w29, w4, w57, w69, w37, w96, w82]
def n2_12 : List Wire := [w29, w4, w58, w69, w37, w95, w82]
def n2_13 : List Wire := [w29, w5, w57, w69, w37, w95, w82]
def n2_14 : List Wire := [w29, w5, w58, w69, w37, w95, w82]
def n2_15 : List Wire := [w29, w7, w69, w37, w95, w82]
def n2_16 : List Wire := [w29, w24, w57, w69, w37, w95, w82]
def n2_17 : List Wire := [w29, w44, w7, w69, w37, w95, w82]
def n2_18 : List Wire := [w29, w44, w57, w10, w37, w95, w82]
def n2_19 : List Wire := [w29, w44, w57, w37, w95, w82, w72]
def n2_20 : List Wire := [w29, w44, w57, w37, w95, w82, w73]
def n2_21 : List Wire := [w29, w44, w57, w68, w37, w95, w82]
def n2_22 : List Wire := [w29, w44, w57, w69, w13, w95, w82]
def n2_23 : List Wire := [w29, w44, w57, w69, w37, w14, w82]
def n2_24 : List Wire := [w29, w44, w57, w69, w37, w82, w99]
def n2_25 : List Wire := [w29, w44, w57, w69, w37, w82, w100]
def n2_26 : List Wire := [w29, w44, w57, w69, w37, w95, w16]
def n2_29 : List Wire := [w29, w44, w57, w69, w37, w95, w84]
def n2_30 : List Wire := [w29, w44, w57, w69, w37, w95, w85]
def n2_31 : List Wire := [w29, w44, w57, w69, w37, w95, w86]
def n2_32 : List Wire := [w29, w44, w57, w69, w37, w95, w87]
def n2_33 : List Wire := [w29, w44, w57, w69, w37, w95, w91]
def n2_35 : List Wire := [w29, w44, w57, w69, w37, w96, w83]
def n2_36 : List Wire := [w29, w44, w57, w69, w37, w97, w82]
def n2_37 : List Wire := [w29, w44, w57, w69, w37, w98, w82]
def n2_38 : List Wire := [w29, w44, w57, w69, w37, w101, w82]
def n2_40 : List Wire := [w29, w44, w57, w69, w38, w95, w83]
def n2_41 : List Wire := [w29, w44, w57, w69, w38, w96, w82]
def n2_42 : List Wire := [w29, w44, w57, w69, w39, w95, w82]
def n2_43 : List Wire := [w29, w44, w57, w69, w41, w95, w82]
def n2_44 : List Wire := [w29, w44, w57, w69, w42, w95, w82]
def n2_45 : List Wire := [w29, w44, w57, w69, w51, w95, w82]
def n2_46 : List Wire := [w29, w44, w57, w69, w95, w82, w43]
def n2_47 : List Wire := [w29, w44, w57, w70, w37, w95, w82]
def n2_48 : List Wire := [w29, w44, w57, w71, w37, w95, w82]
def n2_49 : List Wire := [w29, w44, w57, w76, w37, w95, w82]
def n2_51 : List Wire := [w29, w44, w58, w69, w37, w95, w83]
def n2_52 : List Wire := [w29, w44, w58, w69, w37, w96, w82]
def n2_53 : List Wire := [w29, w44, w58, w69, w38, w95, w82]
def n2_54 : List Wire := [w29, w44, w59, w69, w37, w95, w82]
def n2_55 : List Wire := [w29, w44, w63, w69, w37, w95, w82]
def n2_56 : List Wire := [w29, w44, w69, w37, w61, w95, w82]
def n2_57 : List Wire := [w29, w44, w69, w37, w62, w95, w82]
def n2_58 : List Wire := [w29, w44, w69, w60, w37, w95, w82]
def n2_59 : List Wire := [w29, w45, w57, w69, w37, w95, w82]
def n2_60 : List Wire := [w29, w57, w46, w69, w37, w95, w82]
def n2_61 : List Wire := [w29, w57, w69, w37, w48, w95, w82]
def n2_62 : List Wire := [w29, w57, w69, w37, w49, w95, w82]
def n2_63 : List Wire := [w29, w57, w69, w47, w37, w95, w82]
def n2_64 : List Wire := [w29, w57, w69, w77, w37, w95, w83]
def n2_65 : List Wire := [w29, w57, w69, w77, w37, w96, w82]
def n2_66 : List Wire := [w29, w57, w71, w37, w95, w82]
def n2_67 : List Wire := [w29, w57, w75, w69, w37, w95, w82]
def n2_68 : List Wire := [w29, w58, w69, w77, w37, w95, w82]
def n2_69 : List Wire := [w30, w44, w57, w69, w37, w95, w82]
def n2_70 : List Wire := [w30, w57, w69, w37, w95, w82]
def n2_71 : List Wire := [w35, w44, w57, w69, w37, w95, w82]
def n2_72 : List Wire := [w44, w31, w57, w69, w37, w95, w82]
def n2_73 : List Wire := [w44, w57, w69, w32, w37, w95, w82]
def n2_74 : List Wire := [w44, w57, w69, w33, w37, w95, w82]
def n2_75 : List Wire := [w44, w57, w69, w37, w34, w95, w82]
def n2_76 : List Wire := [w44, w57, w69, w37, w52, w95, w83]
def n2_77 : List Wire := [w44, w57, w69, w37, w52, w96, w82]
def n2_78 : List Wire := [w44, w57, w69, w39, w95, w82]
def n2_79 : List Wire := [w44, w58, w69, w37, w52, w95, w82]
def n2_80 : List Wire := [w45, w57, w69, w37, w95, w82]
def n2_81 : List Wire := [w53, w56, w57, w69, w37, w82]
def n2_82 : List Wire := [w53, w57, w37, w93, w95, w82]
def n2_83 : List Wire := [w53, w57, w69, w37, w95, w82]
def n2_84 : List Wire := [w53, w57, w69, w37, w95, w83]
def n2_85 : List Wire := [w53, w57, w69, w111, w95, w82]
def n2_86 : List Wire := [w53, w58, w69, w37, w95, w82]
def n2_87 : List Wire := [w53, w69, w37, w94, w95, w82]
def n2_88 : List Wire := [w57, w69, w37, w95, w108, w82]
def n2_89 : List Wire := [w79, w53, w57, w69, w37, w95]
def n3_0 : List Wire := [w29, w7, w69, w37, w95, w83]
def n3_1 : List Wire := [w29, w7, w69, w37, w96, w82]
def n3_2 : List Wire := [w29, w8, w69, w37, w95, w82]
def n3_3 : List Wire := [w29, w57, w71, w37, w95, w83]
def n3_4 : List Wire := [w29, w57, w71, w37, w96, w82]
def n3_5 : List Wire := [w29, w58, w71, w37, w95, w82]
def n3_6 : List Wire := [w44, w57, w69, w37, w14, w83]
def n3_7 : List Wire := [w44, w57, w69, w37, w15, w82]
def n3_8 : List Wire := [w44, w57, w69, w39, w95, w83]
def n3_9 : List Wire := [w44, w57, w69, w40, w96, w82]
def n3_10 : List Wire := [w44, w58, w69, w37, w14, w82]
def n3_11 : List Wire := [w44, w58, w69, w39, w95, w82]
def test (t : Fin 110) (b : Bool) : Fin 128 :=
  let pts : List (Fin 128) := if b then [82, 82, 84, 82, 41, 74, 21, 37, 82, 42, 84, 21, 37, 21, 74, 74, 74, 41, 41, 41, 21, 82, 37, 21, 41, 37, 37, 21, 84, 84, 41, 42, 82, 74, 84, 42, 37, 42, 42, 37, 42, 74, 84, 21, 84, 41, 42, 74, 82, 37, 74, 74, 21, 1, 42, 42, 37, 64, 84, 82, 84, 41, 82, 1, 84, 21, 41, 82, 74, 64, 21, 41, 16, 42, 32, 82, 4, 8, 32, 37, 2, 16, 2, 80, 34, 66, 10, 34, 33, 68, 72, 68, 72, 34, 40, 9, 18, 17, 17, 9, 34, 5, 80, 72, 9, 36, 18, 66, 17, 80] else [6, 3, 65, 96, 3, 96, 6, 6, 48, 48, 6, 48, 65, 65, 65, 6, 3, 24, 12, 65, 24, 65, 48, 3, 48, 3, 12, 12, 48, 96, 96, 3, 24, 24, 24, 96, 96, 6, 24, 24, 12, 48, 3, 96, 12, 6, 65, 12, 12, 53, 75, 106, 23, 65, 106, 58, 39, 65, 85, 86, 86, 105, 114, 3, 116, 53, 57, 90, 90, 96, 85, 43, 48, 43, 96, 83, 6, 24, 48, 101, 3, 24, 6, 88, 50, 70, 26, 98, 35, 69, 73, 100, 104, 35, 104, 73, 26, 49, 25, 11, 38, 69, 81, 88, 25, 52, 22, 67, 81, 112]
  pts.getD t.val 0

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem samples : ∀ t : Fin 110, ∀ b : Bool,
    sample wires t b = bank 2 3 (test t b) ∧ target (test t b) = !b := by decide +kernel

theorem suffix (rest : List Gate) (o : Nat) (hs : ∀ g ∈ rest, Supported g) (hlen : rest.length ≤ 8)
    (hr : ∀ x : Fin 128, (run rest (bank 2 3 x)).getD o false = target x) :
    attainable 8 wires := by
  obtain ⟨cs,hl,hv,he⟩ := fixed_slots 7 9 o rest hs hlen
  refine ⟨cs,16,hl,hv,?_⟩
  intro t
  have h (b : Bool) : (runChoices cs (sample wires t b)).getD 16 false = !b := by
    rw [(samples t b).1, he]
    · exact (hr _).trans (samples t b).2
    · simp [bank]
  exact ⟨h false, h true⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_0 : ¬ attainable 5 n3_0 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_1 : ¬ attainable 5 n3_1 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_2 : ¬ attainable 5 n3_2 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_3 : ¬ attainable 5 n3_3 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_4 : ¬ attainable 5 n3_4 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_5 : ¬ attainable 5 n3_5 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_6 : ¬ attainable 5 n3_6 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_7 : ¬ attainable 5 n3_7 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_8 : ¬ attainable 5 n3_8 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_9 : ¬ attainable 5 n3_9 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_10 : ¬ attainable 5 n3_10 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_11 : ¬ attainable 5 n3_11 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_0 : ¬ attainable 6 n2_0 := by
  exact stepCover [n3_0, n3_1, n3_2] (by decide +kernel) (rejectCons r3_n3_0 (rejectCons r3_n3_1 (rejectCons r3_n3_2 (rejectNil 5))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_1 : ¬ attainable 6 n2_1 := by
  exact stepCover [n3_3, n3_4, n3_5] (by decide +kernel) (rejectCons r3_n3_3 (rejectCons r3_n3_4 (rejectCons r3_n3_5 (rejectNil 5))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_2 : ¬ attainable 6 n2_2 := by
  exact stepCover [n3_6, n3_7, n3_10] (by decide +kernel) (rejectCons r3_n3_6 (rejectCons r3_n3_7 (rejectCons r3_n3_10 (rejectNil 5))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_3 : ¬ attainable 6 n2_3 := by
  exact stepCover [n3_8, n3_11] (by decide +kernel) (rejectCons r3_n3_8 (rejectCons r3_n3_11 (rejectNil 5)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_4 : ¬ attainable 6 n2_4 := by
  exact stepCover [n3_8] (by decide +kernel) (rejectCons r3_n3_8 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_5 : ¬ attainable 6 n2_5 := by
  exact stepCover [n3_11] (by decide +kernel) (rejectCons r3_n3_11 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_6 : ¬ attainable 6 n2_6 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_7 : ¬ attainable 6 n2_7 := by
  exact stepCover [n3_9] (by decide +kernel) (rejectCons r3_n3_9 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_8 : ¬ attainable 6 n2_8 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_9 : ¬ attainable 6 n2_9 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_10 : ¬ attainable 6 n2_10 := by
  exact stepCover [n3_3] (by decide +kernel) (rejectCons r3_n3_3 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_11 : ¬ attainable 6 n2_11 := by
  exact stepCover [n3_4] (by decide +kernel) (rejectCons r3_n3_4 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_12 : ¬ attainable 6 n2_12 := by
  exact stepCover [n3_5] (by decide +kernel) (rejectCons r3_n3_5 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_13 : ¬ attainable 6 n2_13 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_14 : ¬ attainable 6 n2_14 := by
  exact stepCover [n3_5] (by decide +kernel) (rejectCons r3_n3_5 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_15 : ¬ attainable 6 n2_15 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_16 : ¬ attainable 6 n2_16 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_17 : ¬ attainable 6 n2_17 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_18 : ¬ attainable 6 n2_18 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_19 : ¬ attainable 6 n2_19 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_20 : ¬ attainable 6 n2_20 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_21 : ¬ attainable 6 n2_21 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_22 : ¬ attainable 6 n2_22 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_23 : ¬ attainable 6 n2_23 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_24 : ¬ attainable 6 n2_24 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_25 : ¬ attainable 6 n2_25 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_26 : ¬ attainable 6 n2_26 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_27 : ¬ attainable 6 n2_27 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_28 : ¬ attainable 6 n2_28 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_29 : ¬ attainable 6 n2_29 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_30 : ¬ attainable 6 n2_30 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_31 : ¬ attainable 6 n2_31 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_32 : ¬ attainable 6 n2_32 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_33 : ¬ attainable 6 n2_33 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_34 : ¬ attainable 6 n2_34 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_35 : ¬ attainable 6 n2_35 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_36 : ¬ attainable 6 n2_36 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_37 : ¬ attainable 6 n2_37 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_38 : ¬ attainable 6 n2_38 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_39 : ¬ attainable 6 n2_39 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_40 : ¬ attainable 6 n2_40 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_41 : ¬ attainable 6 n2_41 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_42 : ¬ attainable 6 n2_42 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_43 : ¬ attainable 6 n2_43 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_44 : ¬ attainable 6 n2_44 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_45 : ¬ attainable 6 n2_45 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_46 : ¬ attainable 6 n2_46 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_47 : ¬ attainable 6 n2_47 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_48 : ¬ attainable 6 n2_48 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_49 : ¬ attainable 6 n2_49 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_50 : ¬ attainable 6 n2_50 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_51 : ¬ attainable 6 n2_51 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_52 : ¬ attainable 6 n2_52 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_53 : ¬ attainable 6 n2_53 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_54 : ¬ attainable 6 n2_54 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_55 : ¬ attainable 6 n2_55 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_56 : ¬ attainable 6 n2_56 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_57 : ¬ attainable 6 n2_57 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_58 : ¬ attainable 6 n2_58 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_59 : ¬ attainable 6 n2_59 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_60 : ¬ attainable 6 n2_60 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_61 : ¬ attainable 6 n2_61 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_62 : ¬ attainable 6 n2_62 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_63 : ¬ attainable 6 n2_63 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_64 : ¬ attainable 6 n2_64 := by
  exact stepCover [n3_0] (by decide +kernel) (rejectCons r3_n3_0 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_65 : ¬ attainable 6 n2_65 := by
  exact stepCover [n3_1] (by decide +kernel) (rejectCons r3_n3_1 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_66 : ¬ attainable 6 n2_66 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_67 : ¬ attainable 6 n2_67 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_68 : ¬ attainable 6 n2_68 := by
  exact stepCover [n3_2] (by decide +kernel) (rejectCons r3_n3_2 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_69 : ¬ attainable 6 n2_69 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_70 : ¬ attainable 6 n2_70 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_71 : ¬ attainable 6 n2_71 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_72 : ¬ attainable 6 n2_72 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_73 : ¬ attainable 6 n2_73 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_74 : ¬ attainable 6 n2_74 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_75 : ¬ attainable 6 n2_75 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_76 : ¬ attainable 6 n2_76 := by
  exact stepCover [n3_6] (by decide +kernel) (rejectCons r3_n3_6 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_77 : ¬ attainable 6 n2_77 := by
  exact stepCover [n3_7] (by decide +kernel) (rejectCons r3_n3_7 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_78 : ¬ attainable 6 n2_78 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_79 : ¬ attainable 6 n2_79 := by
  exact stepCover [n3_10] (by decide +kernel) (rejectCons r3_n3_10 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_80 : ¬ attainable 6 n2_80 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_81 : ¬ attainable 6 n2_81 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_82 : ¬ attainable 6 n2_82 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_83 : ¬ attainable 6 n2_83 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_84 : ¬ attainable 6 n2_84 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_85 : ¬ attainable 6 n2_85 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_86 : ¬ attainable 6 n2_86 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_87 : ¬ attainable 6 n2_87 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_88 : ¬ attainable 6 n2_88 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_89 : ¬ attainable 6 n2_89 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_0 : ¬ attainable 7 n1_0 := by
  exact stepCover [n2_3, n2_4, n2_5, n2_6, n2_78, n2_80] (by decide +kernel) (rejectCons r2_n2_3 (rejectCons r2_n2_4 (rejectCons r2_n2_5 (rejectCons r2_n2_6 (rejectCons r2_n2_78 (rejectCons r2_n2_80 (rejectNil 6)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_1 : ¬ attainable 7 n1_1 := by
  exact stepCover [n2_1, n2_10, n2_11, n2_12, n2_13, n2_66, n2_70] (by decide +kernel) (rejectCons r2_n2_1 (rejectCons r2_n2_10 (rejectCons r2_n2_11 (rejectCons r2_n2_12 (rejectCons r2_n2_13 (rejectCons r2_n2_66 (rejectCons r2_n2_70 (rejectNil 6))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_2 : ¬ attainable 7 n1_2 := by
  exact stepCover [n2_27, n2_28, n2_34, n2_39, n2_50, n2_83] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_28 (rejectCons r2_n2_34 (rejectCons r2_n2_39 (rejectCons r2_n2_50 (rejectCons r2_n2_83 (rejectNil 6)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_3 : ¬ attainable 7 n1_3 := by
  exact stepCover [n2_4, n2_10, n2_28, n2_35, n2_40, n2_51, n2_64, n2_76, n2_84] (by decide +kernel) (rejectCons r2_n2_4 (rejectCons r2_n2_10 (rejectCons r2_n2_28 (rejectCons r2_n2_35 (rejectCons r2_n2_40 (rejectCons r2_n2_51 (rejectCons r2_n2_64 (rejectCons r2_n2_76 (rejectCons r2_n2_84 (rejectNil 6))))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_4 : ¬ attainable 7 n1_4 := by
  exact stepCover [n2_7, n2_11, n2_34, n2_35, n2_41, n2_52, n2_65, n2_77] (by decide +kernel) (rejectCons r2_n2_7 (rejectCons r2_n2_11 (rejectCons r2_n2_34 (rejectCons r2_n2_35 (rejectCons r2_n2_41 (rejectCons r2_n2_52 (rejectCons r2_n2_65 (rejectCons r2_n2_77 (rejectNil 6)))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_5 : ¬ attainable 7 n1_5 := by
  exact stepCover [n2_39, n2_40, n2_41, n2_53] (by decide +kernel) (rejectCons r2_n2_39 (rejectCons r2_n2_40 (rejectCons r2_n2_41 (rejectCons r2_n2_53 (rejectNil 6)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_6 : ¬ attainable 7 n1_6 := by
  exact stepCover [n2_5, n2_14, n2_50, n2_51, n2_52, n2_53, n2_68, n2_79, n2_86] (by decide +kernel) (rejectCons r2_n2_5 (rejectCons r2_n2_14 (rejectCons r2_n2_50 (rejectCons r2_n2_51 (rejectCons r2_n2_52 (rejectCons r2_n2_53 (rejectCons r2_n2_68 (rejectCons r2_n2_79 (rejectCons r2_n2_86 (rejectNil 6))))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_7 : ¬ attainable 7 n1_7 := by
  exact stepCover [n2_0, n2_15, n2_64, n2_65, n2_68] (by decide +kernel) (rejectCons r2_n2_0 (rejectCons r2_n2_15 (rejectCons r2_n2_64 (rejectCons r2_n2_65 (rejectCons r2_n2_68 (rejectNil 6))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_8 : ¬ attainable 7 n1_8 := by
  exact stepCover [n2_2, n2_76, n2_77, n2_79] (by decide +kernel) (rejectCons r2_n2_2 (rejectCons r2_n2_76 (rejectCons r2_n2_77 (rejectCons r2_n2_79 (rejectNil 6)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_9 : ¬ attainable 7 n1_9 := by
  exact stepCover [n2_81, n2_82, n2_83, n2_84, n2_85, n2_86, n2_87, n2_88, n2_89] (by decide +kernel) (rejectCons r2_n2_81 (rejectCons r2_n2_82 (rejectCons r2_n2_83 (rejectCons r2_n2_84 (rejectCons r2_n2_85 (rejectCons r2_n2_86 (rejectCons r2_n2_87 (rejectCons r2_n2_88 (rejectCons r2_n2_89 (rejectNil 6))))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_10 : ¬ attainable 7 n1_10 := by
  exact stepCover [n2_27, n2_30, n2_42, n2_47, n2_54, n2_59, n2_78, n2_80, n2_83] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_30 (rejectCons r2_n2_42 (rejectCons r2_n2_47 (rejectCons r2_n2_54 (rejectCons r2_n2_59 (rejectCons r2_n2_78 (rejectCons r2_n2_80 (rejectCons r2_n2_83 (rejectNil 6))))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_11 : ¬ attainable 7 n1_11 := by
  exact stepCover [n2_78, n2_80] (by decide +kernel) (rejectCons r2_n2_78 (rejectCons r2_n2_80 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_12 : ¬ attainable 7 n1_12 := by
  exact stepCover [n2_27, n2_83] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_83 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_13 : ¬ attainable 7 n1_13 := by
  exact stepCover [n2_27, n2_83] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_83 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_14 : ¬ attainable 7 n1_14 := by
  exact stepCover [n2_27, n2_38, n2_83] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_38 (rejectCons r2_n2_83 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_15 : ¬ attainable 7 n1_15 := by
  exact stepCover [n2_27, n2_83] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_83 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_16 : ¬ attainable 7 n1_16 := by
  exact stepCover [n2_27, n2_71, n2_83] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_71 (rejectCons r2_n2_83 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_17 : ¬ attainable 7 n1_17 := by
  exact stepCover [n2_27, n2_83] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_83 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_18 : ¬ attainable 7 n1_18 := by
  exact stepCover [n2_27, n2_55, n2_83] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_55 (rejectCons r2_n2_83 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_19 : ¬ attainable 7 n1_19 := by
  exact stepCover [n2_27, n2_45, n2_83] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_45 (rejectCons r2_n2_83 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_20 : ¬ attainable 7 n1_20 := by
  exact stepCover [n2_27, n2_32, n2_37, n2_43, n2_48, n2_66, n2_69, n2_70, n2_83] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_32 (rejectCons r2_n2_37 (rejectCons r2_n2_43 (rejectCons r2_n2_48 (rejectCons r2_n2_66 (rejectCons r2_n2_69 (rejectCons r2_n2_70 (rejectCons r2_n2_83 (rejectNil 6))))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_21 : ¬ attainable 7 n1_21 := by
  exact stepCover [n2_66, n2_70] (by decide +kernel) (rejectCons r2_n2_66 (rejectCons r2_n2_70 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_22 : ¬ attainable 7 n1_22 := by
  exact stepCover [n2_27, n2_83] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_83 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_23 : ¬ attainable 7 n1_23 := by
  exact stepCover [n2_27, n2_49, n2_83] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_49 (rejectCons r2_n2_83 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_24 : ¬ attainable 7 n1_24 := by
  exact stepCover [n2_24, n2_27, n2_29, n2_44, n2_60, n2_72, n2_83] (by decide +kernel) (rejectCons r2_n2_24 (rejectCons r2_n2_27 (rejectCons r2_n2_29 (rejectCons r2_n2_44 (rejectCons r2_n2_60 (rejectCons r2_n2_72 (rejectCons r2_n2_83 (rejectNil 6))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_25 : ¬ attainable 7 n1_25 := by
  exact stepCover [n2_27, n2_81, n2_82, n2_83, n2_85, n2_87, n2_88, n2_89] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_81 (rejectCons r2_n2_82 (rejectCons r2_n2_83 (rejectCons r2_n2_85 (rejectCons r2_n2_87 (rejectCons r2_n2_88 (rejectCons r2_n2_89 (rejectNil 6)))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_26 : ¬ attainable 7 n1_26 := by
  exact stepCover [n2_27, n2_83] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_83 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_27 : ¬ attainable 7 n1_27 := by
  exact stepCover [n2_27, n2_81] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_81 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_28 : ¬ attainable 7 n1_28 := by
  exact stepCover [n2_27, n2_81, n2_83] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_81 (rejectCons r2_n2_83 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_29 : ¬ attainable 7 n1_29 := by
  exact stepCover [n2_25, n2_27, n2_46, n2_58, n2_63, n2_73, n2_83] (by decide +kernel) (rejectCons r2_n2_25 (rejectCons r2_n2_27 (rejectCons r2_n2_46 (rejectCons r2_n2_58 (rejectCons r2_n2_63 (rejectCons r2_n2_73 (rejectCons r2_n2_83 (rejectNil 6))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_30 : ¬ attainable 7 n1_30 := by
  exact stepCover [n2_27, n2_82] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_82 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_31 : ¬ attainable 7 n1_31 := by
  exact stepCover [n2_5, n2_12, n2_13, n2_14, n2_27, n2_50, n2_68, n2_79, n2_83, n2_86] (by decide +kernel) (rejectCons r2_n2_5 (rejectCons r2_n2_12 (rejectCons r2_n2_13 (rejectCons r2_n2_14 (rejectCons r2_n2_27 (rejectCons r2_n2_50 (rejectCons r2_n2_68 (rejectCons r2_n2_79 (rejectCons r2_n2_83 (rejectCons r2_n2_86 (rejectNil 6)))))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_32 : ¬ attainable 7 n1_32 := by
  exact stepCover [n2_13, n2_27, n2_83] (by decide +kernel) (rejectCons r2_n2_13 (rejectCons r2_n2_27 (rejectCons r2_n2_83 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_33 : ¬ attainable 7 n1_33 := by
  exact stepCover [n2_27, n2_83] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_83 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_34 : ¬ attainable 7 n1_34 := by
  exact stepCover [n2_27, n2_67, n2_83] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_67 (rejectCons r2_n2_83 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_35 : ¬ attainable 7 n1_35 := by
  exact stepCover [n2_19, n2_27, n2_36, n2_56, n2_61, n2_74, n2_83] (by decide +kernel) (rejectCons r2_n2_19 (rejectCons r2_n2_27 (rejectCons r2_n2_36 (rejectCons r2_n2_56 (rejectCons r2_n2_61 (rejectCons r2_n2_74 (rejectCons r2_n2_83 (rejectNil 6))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_36 : ¬ attainable 7 n1_36 := by
  exact stepCover [n2_20, n2_27, n2_31, n2_57, n2_62, n2_75, n2_83] (by decide +kernel) (rejectCons r2_n2_20 (rejectCons r2_n2_27 (rejectCons r2_n2_31 (rejectCons r2_n2_57 (rejectCons r2_n2_62 (rejectCons r2_n2_75 (rejectCons r2_n2_83 (rejectNil 6))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_37 : ¬ attainable 7 n1_37 := by
  exact stepCover [n2_27, n2_39, n2_83] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_39 (rejectCons r2_n2_83 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_38 : ¬ attainable 7 n1_38 := by
  exact stepCover [n2_27, n2_83] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_83 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_39 : ¬ attainable 7 n1_39 := by
  exact stepCover [n2_23, n2_27, n2_83] (by decide +kernel) (rejectCons r2_n2_23 (rejectCons r2_n2_27 (rejectCons r2_n2_83 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_40 : ¬ attainable 7 n1_40 := by
  exact stepCover [n2_27, n2_83] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_83 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_41 : ¬ attainable 7 n1_41 := by
  exact stepCover [n2_27, n2_83] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_83 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_42 : ¬ attainable 7 n1_42 := by
  exact stepCover [n2_27, n2_82, n2_83] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_82 (rejectCons r2_n2_83 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_43 : ¬ attainable 7 n1_43 := by
  exact stepCover [n2_27, n2_83, n2_87] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_83 (rejectCons r2_n2_87 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n2_27 : ¬ attainable 7 n2_27 := by
  exact stepCover [n2_27, n2_83] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_83 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_45 : ¬ attainable 7 n1_45 := by
  exact stepCover [n2_26, n2_27, n2_83] (by decide +kernel) (rejectCons r2_n2_26 (rejectCons r2_n2_27 (rejectCons r2_n2_83 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_46 : ¬ attainable 7 n1_46 := by
  exact stepCover [n2_4, n2_10, n2_27, n2_28, n2_64, n2_76, n2_83, n2_84] (by decide +kernel) (rejectCons r2_n2_4 (rejectCons r2_n2_10 (rejectCons r2_n2_27 (rejectCons r2_n2_28 (rejectCons r2_n2_64 (rejectCons r2_n2_76 (rejectCons r2_n2_83 (rejectCons r2_n2_84 (rejectNil 6)))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_47 : ¬ attainable 7 n1_47 := by
  exact stepCover [n2_27, n2_83] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_83 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_48 : ¬ attainable 7 n1_48 := by
  exact stepCover [n2_27, n2_83] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_83 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_49 : ¬ attainable 7 n1_49 := by
  exact stepCover [n2_27, n2_83] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_83 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_50 : ¬ attainable 7 n1_50 := by
  exact stepCover [n2_18, n2_27, n2_83] (by decide +kernel) (rejectCons r2_n2_18 (rejectCons r2_n2_27 (rejectCons r2_n2_83 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_51 : ¬ attainable 7 n1_51 := by
  exact stepCover [n2_8, n2_27, n2_83] (by decide +kernel) (rejectCons r2_n2_8 (rejectCons r2_n2_27 (rejectCons r2_n2_83 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_52 : ¬ attainable 7 n1_52 := by
  exact stepCover [n2_27, n2_83] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_83 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_53 : ¬ attainable 7 n1_53 := by
  exact stepCover [n2_27, n2_83] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_83 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_54 : ¬ attainable 7 n1_54 := by
  exact stepCover [n2_22, n2_27, n2_83] (by decide +kernel) (rejectCons r2_n2_22 (rejectCons r2_n2_27 (rejectCons r2_n2_83 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_55 : ¬ attainable 7 n1_55 := by
  exact stepCover [n2_27, n2_83] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_83 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_56 : ¬ attainable 7 n1_56 := by
  exact stepCover [n2_27, n2_83] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_83 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_57 : ¬ attainable 7 n1_57 := by
  exact stepCover [n2_21, n2_27, n2_83] (by decide +kernel) (rejectCons r2_n2_21 (rejectCons r2_n2_27 (rejectCons r2_n2_83 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_58 : ¬ attainable 7 n1_58 := by
  exact stepCover [n2_27, n2_83] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_83 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n2_28 : ¬ attainable 7 n2_28 := by
  exact stepCover [n2_4, n2_10, n2_28, n2_64, n2_76, n2_84] (by decide +kernel) (rejectCons r2_n2_4 (rejectCons r2_n2_10 (rejectCons r2_n2_28 (rejectCons r2_n2_64 (rejectCons r2_n2_76 (rejectCons r2_n2_84 (rejectNil 6)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_60 : ¬ attainable 7 n1_60 := by
  exact stepCover [n2_6, n2_7, n2_11, n2_27, n2_34, n2_65, n2_77, n2_83] (by decide +kernel) (rejectCons r2_n2_6 (rejectCons r2_n2_7 (rejectCons r2_n2_11 (rejectCons r2_n2_27 (rejectCons r2_n2_34 (rejectCons r2_n2_65 (rejectCons r2_n2_77 (rejectCons r2_n2_83 (rejectNil 6)))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_61 : ¬ attainable 7 n1_61 := by
  exact stepCover [n2_27, n2_83] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_83 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_62 : ¬ attainable 7 n1_62 := by
  exact stepCover [n2_27, n2_83] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_83 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_63 : ¬ attainable 7 n1_63 := by
  exact stepCover [n2_6, n2_27, n2_83] (by decide +kernel) (rejectCons r2_n2_6 (rejectCons r2_n2_27 (rejectCons r2_n2_83 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n2_34 : ¬ attainable 7 n2_34 := by
  exact stepCover [n2_7, n2_11, n2_34, n2_65, n2_77] (by decide +kernel) (rejectCons r2_n2_7 (rejectCons r2_n2_11 (rejectCons r2_n2_34 (rejectCons r2_n2_65 (rejectCons r2_n2_77 (rejectNil 6))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n2_39 : ¬ attainable 7 n2_39 := by
  exact stepCover [n2_39] (by decide +kernel) (rejectCons r2_n2_39 (rejectNil 6))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_66 : ¬ attainable 7 n1_66 := by
  exact stepCover [n2_27, n2_83] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_83 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_67 : ¬ attainable 7 n1_67 := by
  exact stepCover [n2_15, n2_17, n2_27, n2_83] (by decide +kernel) (rejectCons r2_n2_15 (rejectCons r2_n2_17 (rejectCons r2_n2_27 (rejectCons r2_n2_83 (rejectNil 6)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_68 : ¬ attainable 7 n1_68 := by
  exact stepCover [n2_16, n2_27, n2_83] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_27 (rejectCons r2_n2_83 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_69 : ¬ attainable 7 n1_69 := by
  exact stepCover [n2_9, n2_27, n2_83, n2_85] (by decide +kernel) (rejectCons r2_n2_9 (rejectCons r2_n2_27 (rejectCons r2_n2_83 (rejectCons r2_n2_85 (rejectNil 6)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_70 : ¬ attainable 7 n1_70 := by
  exact stepCover [n2_27, n2_85] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_85 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n2_50 : ¬ attainable 7 n2_50 := by
  exact stepCover [n2_5, n2_14, n2_50, n2_68, n2_79, n2_86] (by decide +kernel) (rejectCons r2_n2_5 (rejectCons r2_n2_14 (rejectCons r2_n2_50 (rejectCons r2_n2_68 (rejectCons r2_n2_79 (rejectCons r2_n2_86 (rejectNil 6)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_72 : ¬ attainable 7 n1_72 := by
  exact stepCover [n2_27, n2_87] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_87 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_73 : ¬ attainable 7 n1_73 := by
  exact stepCover [n2_27, n2_89] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_89 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_74 : ¬ attainable 7 n1_74 := by
  exact stepCover [n2_27, n2_83, n2_89] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_83 (rejectCons r2_n2_89 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_75 : ¬ attainable 7 n1_75 := by
  exact stepCover [n2_81, n2_82, n2_83, n2_85, n2_87, n2_88, n2_89] (by decide +kernel) (rejectCons r2_n2_81 (rejectCons r2_n2_82 (rejectCons r2_n2_83 (rejectCons r2_n2_85 (rejectCons r2_n2_87 (rejectCons r2_n2_88 (rejectCons r2_n2_89 (rejectNil 6))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_76 : ¬ attainable 7 n1_76 := by
  exact stepCover [n2_27, n2_33, n2_83] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_33 (rejectCons r2_n2_83 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_77 : ¬ attainable 7 n1_77 := by
  exact stepCover [n2_27] (by decide +kernel) (rejectCons r2_n2_27 (rejectNil 6))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_78 : ¬ attainable 7 n1_78 := by
  exact stepCover [n2_15] (by decide +kernel) (rejectCons r2_n2_15 (rejectNil 6))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_79 : ¬ attainable 7 n1_79 := by
  exact stepCover [n2_81, n2_82, n2_83, n2_85, n2_87, n2_88, n2_89] (by decide +kernel) (rejectCons r2_n2_81 (rejectCons r2_n2_82 (rejectCons r2_n2_83 (rejectCons r2_n2_85 (rejectCons r2_n2_87 (rejectCons r2_n2_88 (rejectCons r2_n2_89 (rejectNil 6))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_80 : ¬ attainable 7 n1_80 := by
  exact stepCover [] (by decide +kernel) (rejectNil 6)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_81 : ¬ attainable 7 n1_81 := by
  exact stepCover [n2_27] (by decide +kernel) (rejectCons r2_n2_27 (rejectNil 6))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r0_wires : ¬ attainable 8 wires := by
  exact stepCover [n1_0, n1_1, n1_2, n1_3, n1_4, n1_5, n1_6, n1_7, n1_8, n1_9, n1_10, n1_11, n1_12, n1_13, n1_14, n1_15, n1_16, n1_17, n1_18, n1_19, n1_20, n1_21, n1_22, n1_23, n1_24, n1_25, n1_26, n1_27, n1_28, n1_29, n1_30, n1_31, n1_32, n1_33, n1_34, n1_35, n1_36, n1_37, n1_38, n1_39, n1_40, n1_41, n1_42, n1_43, n2_27, n1_45, n1_46, n1_47, n1_48, n1_49, n1_50, n1_51, n1_52, n1_53, n1_54, n1_55, n1_56, n1_57, n1_58, n2_28, n1_60, n1_61, n1_62, n1_63, n2_34, n2_39, n1_66, n1_67, n1_68, n1_69, n1_70, n2_50, n1_72, n1_73, n1_74, n1_75, n1_76, n1_77, n1_78, n1_79, n1_80, n1_81] (by decide +kernel) (rejectCons r1_n1_0 (rejectCons r1_n1_1 (rejectCons r1_n1_2 (rejectCons r1_n1_3 (rejectCons r1_n1_4 (rejectCons r1_n1_5 (rejectCons r1_n1_6 (rejectCons r1_n1_7 (rejectCons r1_n1_8 (rejectCons r1_n1_9 (rejectCons r1_n1_10 (rejectCons r1_n1_11 (rejectCons r1_n1_12 (rejectCons r1_n1_13 (rejectCons r1_n1_14 (rejectCons r1_n1_15 (rejectCons r1_n1_16 (rejectCons r1_n1_17 (rejectCons r1_n1_18 (rejectCons r1_n1_19 (rejectCons r1_n1_20 (rejectCons r1_n1_21 (rejectCons r1_n1_22 (rejectCons r1_n1_23 (rejectCons r1_n1_24 (rejectCons r1_n1_25 (rejectCons r1_n1_26 (rejectCons r1_n1_27 (rejectCons r1_n1_28 (rejectCons r1_n1_29 (rejectCons r1_n1_30 (rejectCons r1_n1_31 (rejectCons r1_n1_32 (rejectCons r1_n1_33 (rejectCons r1_n1_34 (rejectCons r1_n1_35 (rejectCons r1_n1_36 (rejectCons r1_n1_37 (rejectCons r1_n1_38 (rejectCons r1_n1_39 (rejectCons r1_n1_40 (rejectCons r1_n1_41 (rejectCons r1_n1_42 (rejectCons r1_n1_43 (rejectCons r1_n2_27 (rejectCons r1_n1_45 (rejectCons r1_n1_46 (rejectCons r1_n1_47 (rejectCons r1_n1_48 (rejectCons r1_n1_49 (rejectCons r1_n1_50 (rejectCons r1_n1_51 (rejectCons r1_n1_52 (rejectCons r1_n1_53 (rejectCons r1_n1_54 (rejectCons r1_n1_55 (rejectCons r1_n1_56 (rejectCons r1_n1_57 (rejectCons r1_n1_58 (rejectCons r1_n2_28 (rejectCons r1_n1_60 (rejectCons r1_n1_61 (rejectCons r1_n1_62 (rejectCons r1_n1_63 (rejectCons r1_n2_34 (rejectCons r1_n2_39 (rejectCons r1_n1_66 (rejectCons r1_n1_67 (rejectCons r1_n1_68 (rejectCons r1_n1_69 (rejectCons r1_n1_70 (rejectCons r1_n2_50 (rejectCons r1_n1_72 (rejectCons r1_n1_73 (rejectCons r1_n1_74 (rejectCons r1_n1_75 (rejectCons r1_n1_76 (rejectCons r1_n1_77 (rejectCons r1_n1_78 (rejectCons r1_n1_79 (rejectCons r1_n1_80 (rejectCons r1_n1_81 (rejectNil 7)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Case23

theorem no23 (rest : List PEqualNP.CircuitLowerBounds.Gate) (o : Nat) (hs : ∀ g ∈ rest, CircuitSatBridge.Supported g) (hlen : rest.length ≤ 8) (hr : ∀ x : Fin 128, (CircuitSatBridge.run rest (bank 2 3 x)).getD o false = target x) : False :=
  Case23.r0_wires (Case23.suffix rest o hs hlen hr)

namespace Case25
open CircuitSatBridge FreeSupport PEqualNP.CircuitLowerBounds
def w0 := mkSampleWire 0 0 0 0 0 0
def w1 := mkSampleWire 34087504 537452800 525472 0 0 0
def w2 := mkSampleWire 0 512 2097154 0 0 0
def w3 := mkSampleWire 275498664193 69023564292 2097682 0 0 0
def w4 := mkSampleWire 0 3221225472 16793600 0 0 0
def w5 := mkSampleWire 17586847744 292091462154 40042826 0 0 0
def w6 := mkSampleWire 293085511937 361081471502 40043354 0 0 0
def w7 := mkSampleWire 115964182530 29004793920 50384896 0 0 0
def w8 := mkSampleWire 133551030274 303916255818 56873290 0 0 0
def w9 := mkSampleWire 0 67371008 67108864 0 0 0
def w10 := mkSampleWire 549756885024 84238464 68419600 0 0 0
def w11 := mkSampleWire 549790972528 621666688 68945072 0 0 0
def w12 := mkSampleWire 825255549217 69107802756 70517266 0 0 0
def w13 := mkSampleWire 0 34359738368 268435460 0 0 0
def w14 := mkSampleWire 138523213832 699005932560 562055169 0 0 0
def w15 := mkSampleWire 254487396362 716199566416 595646465 0 0 0
def w16 := mkSampleWire 2147746948 39325795361 939533316 0 0 0
def w17 := mkSampleWire 2181834452 39326377249 940057764 0 0 0
def w18 := mkSampleWire 140670960780 738331726897 964717573 0 0 0
def w19 := mkSampleWire 0 430033633280 65593 52901712708 155155726432 25
def w20 := mkSampleWire 0 103121184768 268435972 2248370315 41969688 512
def w21 := mkSampleWire 0 163208798208 8654897 51559530560 154618855456 4112
def w22 := mkSampleWire 0 412853732864 6301707 1342182148 536870976 10249
def w23 := mkSampleWire 0 69290066944 139808 4975230976 68719608960 131104
def w24 := mkSampleWire 0 71949101056 17089040 2214682632 8396808 295424
def w25 := mkSampleWire 825255549217 69048821892 1344016 2248370315 60844056 295424
def w26 := mkSampleWire 0 300715098112 68752392 8594162736 283467841540 1639424
def w27 := mkSampleWire 0 421511036928 75498505 9936344884 284004712516 8389641
def w28 := mkSampleWire 549790972528 438708330880 77403321 61495875444 438623633508 10032281
def w29 := mkSampleWire 549790972528 438708331392 79500475 61495875444 438623633508 10032281
def w30 := mkSampleWire 825289636721 507731895172 79500987 61495875444 438623633508 10032281
def w31 := mkSampleWire 549790972528 441929556352 94196921 61495875444 438623633508 10032281
def w32 := mkSampleWire 567377820272 438742016906 117380603 61495875444 438623633508 10032281
def w33 := mkSampleWire 665755155058 441943321024 127784121 61495875444 438623633508 10032281
def w34 := mkSampleWire 549790972528 473068069248 345838781 61495875444 438623633508 10032281
def w35 := mkSampleWire 688314186360 991685375376 631069881 61495875444 438623633508 10032281
def w36 := mkSampleWire 551938719476 477497255329 1016935613 61495875444 438623633508 10032281
def w37 := mkSampleWire 549790972528 438708332416 83705019 61495875444 438623633508 10042521
def w38 := mkSampleWire 140670960780 975628670001 683682825 9936344884 833894744132 12594185
def w39 := mkSampleWire 0 223338464256 33557041 56534761536 223338464416 33554480
def w40 := mkSampleWire 293085511937 499057329678 40053627 57876943684 224143770848 33696057
def w41 := mkSampleWire 293119599441 499057878798 40579067 57876943684 224143770848 33696057
def w42 := mkSampleWire 293085511937 502278555150 56847227 57876943684 224143770848 33696057
def w43 := mkSampleWire 409049694467 510882123342 56884091 57876943684 224143770848 33696057
def w44 := mkSampleWire 293085511937 499124700686 107162491 57876943684 224143770848 33696057
def w45 := mkSampleWire 842842396961 499141568142 108473211 57876943684 224143770848 33696057
def w46 := mkSampleWire 293085511937 533417068046 308489087 57876943684 224143770848 33696057
def w47 := mkSampleWire 431608725769 1060624307742 602106747 57876943684 224143770848 33696057
def w48 := mkSampleWire 295233258885 537846253103 979578751 57876943684 224143770848 33696057
def w49 := mkSampleWire 293085511937 507647272462 48708475 57876943684 224143770848 33700153
def w50 := mkSampleWire 842876484465 507732027278 117391355 66471106420 507611677924 43728313
def w51 := mkSampleWire 0 34401830912 403309572 33687683 33572880 134217728
def w52 := mkSampleWire 133551030274 300695046218 173774152 8627850419 283505608724 140051520
def w53 := mkSampleWire 0 37648335360 354435078 1030792151040 37648335619 354435078
def w54 := mkSampleWire 0 37690296832 355516422 1030825838723 37681908499 354435078
def w55 := mkSampleWire 825255549217 106697157252 355779094 1033040521355 37709179675 354730502
def w56 := mkSampleWire 825289636721 107234585476 356304566 1033040521355 37709179675 354730502
def w57 := mkSampleWire 941219731747 132472335044 389337622 1033040521355 37709179675 354730502
def w58 := mkSampleWire 842842396961 398755064462 393724766 1033040521355 37709179675 354730502
def w59 := mkSampleWire 963778763049 802481864340 901040663 1033040521355 37709179675 354730502
def w60 := mkSampleWire 827403296165 111663214245 1026876950 1033040521355 37709179675 354730502
def w61 := mkSampleWire 0 321116176896 492848142 1039386313776 321116177159 358630406
def w62 := mkSampleWire 549790972528 476289295232 364729535 1092288026484 476271969127 364467359
def w63 := mkSampleWire 825289636721 545321249668 364762815 1094536396799 476332813183 364762783
def w64 := mkSampleWire 140670960780 1013277005361 1038117903 1040728495924 871543079751 367029263
def w65 := mkSampleWire 416169624973 1082300569141 1038118431 1040728495924 871543079751 367029263
def w66 := mkSampleWire 140705048284 1013277587249 1038642351 1040728495924 871543079751 367029263
def w67 := mkSampleWire 690427845804 1013293872817 1039428639 1040728495924 871543079751 367029263
def w68 := mkSampleWire 256635143310 1030470639217 1071709199 1040728495924 871543079751 367029263
def w69 := mkSampleWire 158257808524 1030490560059 1071869263 1040728495924 871543079751 367029263
def w70 := mkSampleWire 965926509997 1082325827253 1039461919 1042976866239 871603923807 367324687
def w71 := mkSampleWire 140670960780 1030456890929 1039760399 1040728495924 871543079751 368667663
def w72 := mkSampleWire 690461933308 1030474299313 1040022719 1092288026484 1026162000743 368671903
def w73 := mkSampleWire 293085511937 536705664526 392391551 1088669094724 261792106467 388131135
def w74 := mkSampleWire 842842396961 536730922638 393735039 1090917465039 261852950523 388426559
def w75 := mkSampleWire 433756472717 1099480602175 1071869823 1097263257460 1095149979623 400715071
def w76 := mkSampleWire 1097329793323 991423697630 133552475 1092288026484 1026454557543 402521567
def w77 := mkSampleWire 825255549217 106697288324 490653206 1033040521355 37709179675 488948230
def w78 := mkSampleWire 133551030274 338343381578 528209230 1039420001459 321153944343 494486598
def w79 := mkSampleWire 133585117778 338880817994 528209390 1039420001459 321153944343 494486598
def w80 := mkSampleWire 409049694467 407333390926 528209758 1039420001459 321153944343 494486598
def w81 := mkSampleWire 683307915298 338360232650 528471390 1039420001459 321153944343 494486598
def w82 := mkSampleWire 135698777222 343309438571 1065088334 1039420001459 321153944343 494486598
def w83 := mkSampleWire 272074244106 1025538154074 1073470799 1039420001459 321153944343 494486598
def w84 := mkSampleWire 958806579491 407350241998 528471902 1041634684091 321181215519 494782022
def w85 := mkSampleWire 683342002802 476336614346 536860159 1092321714167 476309736311 502879455
def w86 := mkSampleWire 274221991054 1030504210043 1073478991 1040762183607 871580846935 502885455
def w87 := mkSampleWire 845024231413 314592543663 477832654 1040762183607 876163713879 503016911
def w88 := mkSampleWire 409049694467 545309249102 528220031 1097296945143 545297715191 528182655
def w89 := mkSampleWire 0 68728040448 536871456 7189913608 68728005768 536871456
def w90 := mkSampleWire 254487396362 784919084112 595909169 58749444168 223347913896 570724912
def w91 := mkSampleWire 254521483866 785456495952 596434609 58749444168 223347913896 570724912
def w92 := mkSampleWire 254487396362 784919084624 598006323 58749444168 223347913896 570724912
def w93 := mkSampleWire 529986060555 785223171668 598006323 58749444168 223347913896 570724912
def w94 := mkSampleWire 272074244106 1059830546010 602397563 58749444168 223347913896 570724912
def w95 := mkSampleWire 254487396362 784986455120 663018033 58749444168 223347913896 570724912
def w96 := mkSampleWire 804244281386 785003314384 664066609 58749444168 223347913896 570724912
def w97 := mkSampleWire 254487396362 819278822480 864344629 58749444168 223347913896 570724912
def w98 := mkSampleWire 256635143310 824244878449 998571573 58749444168 223347913896 570724912
def w99 := mkSampleWire 254487396362 785489509456 596048433 58749444168 223347913896 570855984
def w100 := mkSampleWire 547572908299 1060637949534 602405755 60091626316 224153220328 570866489
def w101 := mkSampleWire 965960597501 761168246197 545532593 60091626316 778357683432 579255225
def w102 := mkSampleWire 804278368890 1060418616784 664657593 68685789052 507352691948 580753081
def w103 := mkSampleWire 2181834452 108087930145 940189348 7223601291 73057070232 671220256
def w104 := mkSampleWire 2181834452 108087930657 942286502 7223601291 73057070232 671220256
def w105 := mkSampleWire 277680498645 108358463269 942286518 7223601291 73057070232 671220256
def w106 := mkSampleWire 2181834452 111309155617 956982948 7223601291 73057070232 671220256
def w107 := mkSampleWire 140705048284 807093861681 965373605 7223601291 73057070232 671220256
def w108 := mkSampleWire 19768682196 400145706795 980101102 7223601291 73057070232 671220256
def w109 := mkSampleWire 118146016982 137084202337 990574244 7223601291 73057070232 671220256
def w110 := mkSampleWire 2181834452 108155301153 1007298212 7223601291 73057070232 671220256
def w111 := mkSampleWire 551938719476 108172144033 1008608948 7223601291 73057070232 671220256
def w112 := mkSampleWire 2181834452 111309155617 957277876 7223601291 73057070232 671515168
def w113 := mkSampleWire 551938719476 546258808225 1017067197 68719476735 511680703740 681252537
def w114 := mkSampleWire 295267346389 537855192879 980103167 60125313999 228481232120 704785209
def w115 := mkSampleWire 256669230814 824278973809 999227061 58783131851 227676978360 705073712
def w116 := mkSampleWire 133585117778 17185800522 34279904 56534761536 227907703968 706417136
def w117 := mkSampleWire 958840666995 86234622414 35623920 58783131851 227968548024 706712560
def w118 := mkSampleWire 274256078558 992814470523 717962729 66471106420 1061802448100 719011321
def w119 := mkSampleWire 1099511627775 1061863292415 719306745 68719476735 1061863292156 719306745
def w120 := mkSampleWire 254487396362 819346194000 933550647 1089541595208 260996249515 925159990
def w121 := mkSampleWire 1079742945579 819667140308 934599223 1089575282891 261048696763 925159990
def w122 := mkSampleWire 256635143310 1099190156913 1071971903 1099477940092 1094890993647 937754175
def w123 := mkSampleWire 2181834452 111376527137 1026188966 1038015752331 110705405851 1025655334
def w124 := mkSampleWire 827437383669 111663902629 1027532470 1038015752331 110724280219 1025950246
def w125 := mkSampleWire 135732864726 412029480811 1065089006 1046609915067 394177441695 1031489126
def w126 := mkSampleWire 140705048284 1082039140145 1038773935 1047952097215 944600149983 1038249519
def w127 := mkSampleWire 806426115838 600454298097 1033688196 1041634684091 875367856927 1040045766
def w128 := mkSampleWire 549720655247 660803296895 996338502 1038015752331 660887994267 1063709542
def w129 := mkSampleWire 272074244106 1094257671770 1073733503 1098169445627 544501858239 1065211510
def w130 := mkSampleWire 1099511627775 1099511627775 1073741823 1099511627775 1099511627775 1073741823
def wires : List Wire := [w0, w40, w55, w28, w103, w64, w90, w53, w78]
def n1_0 : List Wire := [w1, w40, w28, w55, w78, w90, w103, w64]
def n1_1 : List Wire := [w2, w40, w28, w55, w78, w90, w103, w64]
def n1_2 : List Wire := [w3, w40, w28, w55, w78, w90, w103, w64]
def n1_3 : List Wire := [w4, w40, w28, w55, w78, w90, w103, w64]
def n1_4 : List Wire := [w5, w40, w28, w55, w78, w90, w103, w64]
def n1_5 : List Wire := [w19, w40, w28, w55, w78, w90, w103, w64]
def n1_6 : List Wire := [w21, w40, w28, w55, w78, w90, w103, w64]
def n1_7 : List Wire := [w22, w40, w28, w55, w78, w90, w103, w64]
def n1_8 : List Wire := [w23, w40, w28, w55, w78, w90, w103, w64]
def n1_9 : List Wire := [w24, w40, w28, w55, w78, w90, w103, w64]
def n1_10 : List Wire := [w28, w55, w78, w90, w103, w127, w64]
def n1_11 : List Wire := [w39, w40, w28, w55, w78, w90, w103, w64]
def n1_12 : List Wire := [w40, w7, w28, w55, w78, w90, w103, w64]
def n1_13 : List Wire := [w40, w9, w28, w55, w78, w90, w103, w64]
def n1_14 : List Wire := [w40, w10, w28, w55, w78, w90, w103, w64]
def n1_15 : List Wire := [w40, w26, w28, w55, w78, w90, w103, w64]
def n1_16 : List Wire := [w40, w27, w28, w55, w78, w90, w103, w64]
def n1_17 : List Wire := [w40, w28, w13, w55, w78, w90, w103, w64]
def n1_18 : List Wire := [w40, w28, w20, w55, w78, w90, w103, w64]
def n1_19 : List Wire := [w40, w28, w50, w55, w78, w90, w103, w64]
def n1_20 : List Wire := [w40, w28, w53, w55, w78, w90, w103, w64]
def n1_21 : List Wire := [w40, w28, w53, w78, w90, w103, w70]
def n1_22 : List Wire := [w40, w28, w54, w55, w78, w90, w103, w64]
def n1_23 : List Wire := [w40, w28, w55, w51, w78, w90, w103, w64]
def n1_24 : List Wire := [w40, w28, w55, w61, w78, w90, w103, w64]
def n1_25 : List Wire := [w40, w28, w55, w62, w78, w90, w103, w64]
def n1_26 : List Wire := [w40, w28, w55, w63, w78, w90, w103, w64]
def n1_27 : List Wire := [w40, w28, w55, w73, w78, w90, w103, w64]
def n1_28 : List Wire := [w40, w28, w55, w74, w78, w90, w103, w64]
def n1_29 : List Wire := [w40, w28, w55, w78, w14, w90, w103, w64]
def n1_30 : List Wire := [w40, w28, w55, w78, w84, w90, w103, w64]
def n1_31 : List Wire := [w40, w28, w55, w78, w85, w90, w103, w64]
def n1_32 : List Wire := [w40, w28, w55, w78, w88, w90, w103, w64]
def n1_33 : List Wire := [w40, w28, w55, w78, w89, w90, w103, w64]
def n1_34 : List Wire := [w40, w28, w55, w78, w90, w16, w103, w64]
def n1_35 : List Wire := [w40, w28, w55, w78, w90, w100, w103, w64]
def n1_36 : List Wire := [w40, w28, w55, w78, w90, w102, w103, w64]
def n2_16 : List Wire := [w40, w28, w55, w78, w90, w103, w64]
def n1_38 : List Wire := [w40, w28, w55, w78, w90, w103, w64, w70]
def n1_39 : List Wire := [w40, w28, w55, w78, w90, w103, w64, w72]
def n1_40 : List Wire := [w40, w28, w55, w78, w90, w103, w64, w75]
def n1_41 : List Wire := [w40, w28, w55, w78, w90, w103, w64, w86]
def n1_42 : List Wire := [w40, w28, w55, w78, w90, w103, w64, w122]
def n1_43 : List Wire := [w40, w28, w55, w78, w90, w103, w64, w125]
def n1_44 : List Wire := [w40, w28, w55, w78, w90, w103, w64, w126]
def n1_45 : List Wire := [w40, w28, w55, w78, w90, w103, w64, w129]
def n1_46 : List Wire := [w40, w28, w55, w78, w90, w103, w64, w130]
def n1_47 : List Wire := [w40, w28, w55, w78, w90, w103, w70]
def n1_48 : List Wire := [w40, w28, w55, w78, w90, w103, w113, w64]
def n1_49 : List Wire := [w40, w28, w55, w78, w90, w103, w114, w64]
def n1_50 : List Wire := [w40, w28, w55, w78, w90, w103, w115, w64]
def n1_51 : List Wire := [w40, w28, w55, w78, w90, w103, w123, w64]
def n1_52 : List Wire := [w40, w28, w55, w78, w90, w103, w124, w64]
def n1_53 : List Wire := [w40, w28, w55, w78, w90, w103, w127, w64]
def n1_54 : List Wire := [w40, w28, w55, w78, w90, w103, w128, w64]
def n1_55 : List Wire := [w40, w28, w55, w78, w90, w118, w103, w64]
def n1_56 : List Wire := [w40, w28, w55, w78, w90, w119, w103, w64]
def n1_57 : List Wire := [w40, w28, w55, w78, w90, w120, w103, w64]
def n1_58 : List Wire := [w40, w28, w55, w78, w90, w121, w103, w64]
def n1_59 : List Wire := [w40, w28, w55, w78, w101, w90, w103, w64]
def n1_60 : List Wire := [w40, w28, w55, w87, w78, w90, w103, w64]
def n1_61 : List Wire := [w40, w28, w55, w87, w78, w103, w64]
def n1_62 : List Wire := [w40, w28, w55, w101, w90, w103, w64]
def n1_63 : List Wire := [w40, w28, w76, w55, w78, w90, w64]
def n1_64 : List Wire := [w40, w28, w76, w55, w78, w90, w103, w64]
def n1_65 : List Wire := [w40, w28, w78, w90, w103, w64, w70]
def n1_66 : List Wire := [w40, w28, w78, w90, w118, w103, w64]
def n1_67 : List Wire := [w40, w55, w78, w90, w103, w128, w64]
def n1_68 : List Wire := [w117, w40, w28, w55, w78, w90, w103]
def n1_69 : List Wire := [w117, w40, w28, w55, w78, w90, w103, w64]
def n2_0 : List Wire := [w6, w28, w55, w78, w90, w103, w64]
def n2_1 : List Wire := [w25, w40, w28, w78, w90, w103, w64]
def n2_2 : List Wire := [w28, w44, w55, w78, w90, w103, w64]
def n2_3 : List Wire := [w28, w45, w55, w78, w90, w103, w64]
def n2_4 : List Wire := [w28, w46, w55, w78, w90, w103, w64]
def n2_5 : List Wire := [w28, w55, w78, w90, w47, w103, w64]
def n2_6 : List Wire := [w28, w55, w78, w90, w103, w48, w64]
def n2_7 : List Wire := [w28, w78, w90, w103, w127, w70]
def n2_8 : List Wire := [w40, w8, w28, w55, w90, w103, w64]
def n2_9 : List Wire := [w40, w11, w55, w78, w90, w103, w64]
def n2_10 : List Wire := [w40, w12, w28, w78, w90, w103, w64]
def n2_11 : List Wire := [w40, w28, w52, w55, w90, w103, w64]
def n2_12 : List Wire := [w40, w28, w55, w78, w15, w103, w64]
def n2_13 : List Wire := [w40, w28, w55, w78, w90, w17, w64]
def n2_14 : List Wire := [w40, w28, w55, w78, w90, w38, w103]
def n2_15 : List Wire := [w40, w28, w55, w78, w90, w103, w18]
def n2_17 : List Wire := [w40, w28, w55, w78, w90, w103, w65]
def n2_18 : List Wire := [w40, w28, w55, w78, w90, w103, w66]
def n2_19 : List Wire := [w40, w28, w55, w78, w90, w103, w67]
def n2_20 : List Wire := [w40, w28, w55, w78, w90, w103, w68]
def n2_21 : List Wire := [w40, w28, w55, w78, w90, w103, w69]
def n2_22 : List Wire := [w40, w28, w55, w78, w90, w103, w71]
def n2_23 : List Wire := [w40, w28, w55, w78, w90, w104, w64]
def n2_24 : List Wire := [w40, w28, w55, w78, w90, w105, w64]
def n2_25 : List Wire := [w40, w28, w55, w78, w90, w106, w64]
def n2_26 : List Wire := [w40, w28, w55, w78, w90, w107, w64]
def n2_27 : List Wire := [w40, w28, w55, w78, w90, w108, w64]
def n2_28 : List Wire := [w40, w28, w55, w78, w90, w109, w64]
def n2_29 : List Wire := [w40, w28, w55, w78, w90, w110, w64]
def n2_30 : List Wire := [w40, w28, w55, w78, w90, w111, w64]
def n2_31 : List Wire := [w40, w28, w55, w78, w90, w112, w64]
def n2_32 : List Wire := [w40, w28, w55, w78, w91, w103, w64]
def n2_33 : List Wire := [w40, w28, w55, w78, w92, w103, w64]
def n2_34 : List Wire := [w40, w28, w55, w78, w93, w103, w64]
def n2_35 : List Wire := [w40, w28, w55, w78, w94, w103, w64]
def n2_36 : List Wire := [w40, w28, w55, w78, w95, w103, w64]
def n2_37 : List Wire := [w40, w28, w55, w78, w96, w103, w64]
def n2_38 : List Wire := [w40, w28, w55, w78, w97, w103, w64]
def n2_39 : List Wire := [w40, w28, w55, w78, w99, w103, w64]
def n2_40 : List Wire := [w40, w28, w55, w78, w103, w98, w64]
def n2_41 : List Wire := [w40, w28, w55, w79, w90, w103, w64]
def n2_42 : List Wire := [w40, w28, w55, w80, w90, w103, w64]
def n2_43 : List Wire := [w40, w28, w55, w81, w90, w103, w64]
def n2_44 : List Wire := [w40, w28, w55, w90, w103, w64, w82]
def n2_45 : List Wire := [w40, w28, w55, w90, w103, w64, w83]
def n2_46 : List Wire := [w40, w28, w56, w78, w90, w103, w64]
def n2_47 : List Wire := [w40, w28, w57, w78, w90, w103, w64]
def n2_48 : List Wire := [w40, w28, w58, w78, w90, w103, w64]
def n2_49 : List Wire := [w40, w28, w76, w78, w90, w70]
def n2_50 : List Wire := [w40, w28, w77, w78, w90, w103, w64]
def n2_51 : List Wire := [w40, w28, w78, w90, w59, w103, w64]
def n2_52 : List Wire := [w40, w28, w78, w90, w103, w60, w64]
def n2_53 : List Wire := [w40, w28, w78, w90, w103, w70]
def n2_54 : List Wire := [w40, w28, w87, w78, w103, w70]
def n2_55 : List Wire := [w40, w28, w101, w90, w103, w70]
def n2_56 : List Wire := [w40, w29, w55, w78, w90, w103, w64]
def n2_57 : List Wire := [w40, w30, w55, w78, w90, w103, w64]
def n2_58 : List Wire := [w40, w31, w55, w78, w90, w103, w64]
def n2_59 : List Wire := [w40, w32, w55, w78, w90, w103, w64]
def n2_60 : List Wire := [w40, w33, w55, w78, w90, w103, w64]
def n2_61 : List Wire := [w40, w34, w55, w78, w90, w103, w64]
def n2_62 : List Wire := [w40, w37, w55, w78, w90, w103, w64]
def n2_63 : List Wire := [w40, w55, w78, w90, w35, w103, w64]
def n2_64 : List Wire := [w40, w55, w78, w90, w103, w36, w64]
def n2_65 : List Wire := [w40, w78, w90, w103, w128, w70]
def n2_66 : List Wire := [w41, w28, w55, w78, w90, w103, w64]
def n2_67 : List Wire := [w42, w28, w55, w78, w90, w103, w64]
def n2_68 : List Wire := [w43, w28, w55, w78, w90, w103, w64]
def n2_69 : List Wire := [w49, w28, w55, w78, w90, w103, w64]
def n2_70 : List Wire := [w116, w40, w28, w78, w90, w103]
def test (t : Fin 110) (b : Bool) : Fin 128 :=
  let pts : List (Fin 128) := if b then [21, 21, 42, 84, 41, 41, 74, 21, 42, 42, 41, 21, 42, 84, 84, 41, 84, 21, 82, 82, 74, 74, 41, 82, 74, 21, 84, 82, 42, 82, 42, 84, 82, 41, 74, 74, 37, 37, 37, 37, 37, 37, 41, 84, 21, 74, 42, 82, 37, 37, 82, 21, 64, 84, 21, 74, 8, 82, 37, 16, 64, 4, 1, 84, 4, 21, 37, 32, 2, 42, 37, 37, 16, 41, 74, 37, 82, 74, 41, 32, 42, 37, 37, 42, 74, 82, 1, 8, 2, 84, 41, 34, 72, 34, 36, 68, 9, 18, 68, 9, 9, 36, 33, 40, 36, 66, 36, 17, 36, 80] else [6, 65, 48, 96, 24, 12, 24, 48, 6, 24, 48, 12, 12, 24, 12, 96, 65, 3, 48, 24, 12, 96, 3, 96, 6, 24, 6, 3, 3, 6, 96, 48, 65, 65, 3, 65, 65, 96, 6, 12, 48, 3, 6, 3, 96, 48, 65, 12, 24, 39, 114, 85, 96, 92, 29, 90, 12, 83, 44, 24, 65, 6, 65, 85, 12, 23, 45, 48, 6, 58, 101, 100, 48, 105, 75, 53, 86, 106, 43, 96, 106, 38, 52, 43, 78, 90, 3, 24, 3, 86, 57, 98, 73, 50, 100, 69, 11, 19, 76, 25, 13, 39, 35, 104, 101, 67, 44, 49, 52, 112]
  pts.getD t.val 0

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem samples : ∀ t : Fin 110, ∀ b : Bool,
    sample wires t b = bank 2 5 (test t b) ∧ target (test t b) = !b := by decide +kernel

theorem suffix (rest : List Gate) (o : Nat) (hs : ∀ g ∈ rest, Supported g) (hlen : rest.length ≤ 8)
    (hr : ∀ x : Fin 128, (run rest (bank 2 5 x)).getD o false = target x) :
    attainable 8 wires := by
  obtain ⟨cs,hl,hv,he⟩ := fixed_slots 7 9 o rest hs hlen
  refine ⟨cs,16,hl,hv,?_⟩
  intro t
  have h (b : Bool) : (runChoices cs (sample wires t b)).getD 16 false = !b := by
    rw [(samples t b).1, he]
    · exact (hr _).trans (samples t b).2
    · simp [bank]
  exact ⟨h false, h true⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_0 : ¬ attainable 6 n2_0 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_1 : ¬ attainable 6 n2_1 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_2 : ¬ attainable 6 n2_2 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_3 : ¬ attainable 6 n2_3 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_4 : ¬ attainable 6 n2_4 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_5 : ¬ attainable 6 n2_5 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_6 : ¬ attainable 6 n2_6 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_7 : ¬ attainable 6 n2_7 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_8 : ¬ attainable 6 n2_8 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_9 : ¬ attainable 6 n2_9 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_10 : ¬ attainable 6 n2_10 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_11 : ¬ attainable 6 n2_11 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_12 : ¬ attainable 6 n2_12 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_13 : ¬ attainable 6 n2_13 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_14 : ¬ attainable 6 n2_14 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_15 : ¬ attainable 6 n2_15 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_16 : ¬ attainable 6 n2_16 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_17 : ¬ attainable 6 n2_17 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_18 : ¬ attainable 6 n2_18 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_19 : ¬ attainable 6 n2_19 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_20 : ¬ attainable 6 n2_20 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_21 : ¬ attainable 6 n2_21 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_22 : ¬ attainable 6 n2_22 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_23 : ¬ attainable 6 n2_23 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_24 : ¬ attainable 6 n2_24 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_25 : ¬ attainable 6 n2_25 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_26 : ¬ attainable 6 n2_26 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_27 : ¬ attainable 6 n2_27 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_28 : ¬ attainable 6 n2_28 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_29 : ¬ attainable 6 n2_29 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_30 : ¬ attainable 6 n2_30 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_31 : ¬ attainable 6 n2_31 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_32 : ¬ attainable 6 n2_32 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_33 : ¬ attainable 6 n2_33 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_34 : ¬ attainable 6 n2_34 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_35 : ¬ attainable 6 n2_35 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_36 : ¬ attainable 6 n2_36 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_37 : ¬ attainable 6 n2_37 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_38 : ¬ attainable 6 n2_38 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_39 : ¬ attainable 6 n2_39 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_40 : ¬ attainable 6 n2_40 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_41 : ¬ attainable 6 n2_41 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_42 : ¬ attainable 6 n2_42 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_43 : ¬ attainable 6 n2_43 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_44 : ¬ attainable 6 n2_44 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_45 : ¬ attainable 6 n2_45 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_46 : ¬ attainable 6 n2_46 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_47 : ¬ attainable 6 n2_47 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_48 : ¬ attainable 6 n2_48 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_49 : ¬ attainable 6 n2_49 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_50 : ¬ attainable 6 n2_50 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_51 : ¬ attainable 6 n2_51 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_52 : ¬ attainable 6 n2_52 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_53 : ¬ attainable 6 n2_53 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_54 : ¬ attainable 6 n2_54 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_55 : ¬ attainable 6 n2_55 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_56 : ¬ attainable 6 n2_56 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_57 : ¬ attainable 6 n2_57 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_58 : ¬ attainable 6 n2_58 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_59 : ¬ attainable 6 n2_59 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_60 : ¬ attainable 6 n2_60 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_61 : ¬ attainable 6 n2_61 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_62 : ¬ attainable 6 n2_62 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_63 : ¬ attainable 6 n2_63 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_64 : ¬ attainable 6 n2_64 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_65 : ¬ attainable 6 n2_65 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_66 : ¬ attainable 6 n2_66 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_67 : ¬ attainable 6 n2_67 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_68 : ¬ attainable 6 n2_68 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_69 : ¬ attainable 6 n2_69 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_70 : ¬ attainable 6 n2_70 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_0 : ¬ attainable 7 n1_0 := by
  exact stepCover [n2_16, n2_18, n2_32, n2_41, n2_46, n2_53, n2_66] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_18 (rejectCons r2_n2_32 (rejectCons r2_n2_41 (rejectCons r2_n2_46 (rejectCons r2_n2_53 (rejectCons r2_n2_66 (rejectNil 6))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_1 : ¬ attainable 7 n1_1 := by
  exact stepCover [n2_16, n2_23, n2_33, n2_53, n2_56] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_23 (rejectCons r2_n2_33 (rejectCons r2_n2_53 (rejectCons r2_n2_56 (rejectNil 6))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_2 : ¬ attainable 7 n1_2 := by
  exact stepCover [n2_16, n2_17, n2_24, n2_34, n2_42, n2_53, n2_57] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_17 (rejectCons r2_n2_24 (rejectCons r2_n2_34 (rejectCons r2_n2_42 (rejectCons r2_n2_53 (rejectCons r2_n2_57 (rejectNil 6))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_3 : ¬ attainable 7 n1_3 := by
  exact stepCover [n2_16, n2_25, n2_53, n2_58, n2_67] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_25 (rejectCons r2_n2_53 (rejectCons r2_n2_58 (rejectCons r2_n2_67 (rejectNil 6))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_4 : ¬ attainable 7 n1_4 := by
  exact stepCover [n2_16, n2_21, n2_27, n2_35, n2_48, n2_53, n2_59] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_21 (rejectCons r2_n2_27 (rejectCons r2_n2_35 (rejectCons r2_n2_48 (rejectCons r2_n2_53 (rejectCons r2_n2_59 (rejectNil 6))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_5 : ¬ attainable 7 n1_5 := by
  exact stepCover [n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_6 : ¬ attainable 7 n1_6 := by
  exact stepCover [n2_16, n2_53, n2_69] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectCons r2_n2_69 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_7 : ¬ attainable 7 n1_7 := by
  exact stepCover [n2_16, n2_53, n2_62] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectCons r2_n2_62 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_8 : ¬ attainable 7 n1_8 := by
  exact stepCover [n2_16, n2_39, n2_53] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_39 (rejectCons r2_n2_53 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_9 : ¬ attainable 7 n1_9 := by
  exact stepCover [n2_16, n2_31, n2_53] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_31 (rejectCons r2_n2_53 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_10 : ¬ attainable 7 n1_10 := by
  exact stepCover [n2_7, n2_16] (by decide +kernel) (rejectCons r2_n2_7 (rejectCons r2_n2_16 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_11 : ¬ attainable 7 n1_11 := by
  exact stepCover [n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_12 : ¬ attainable 7 n1_12 := by
  exact stepCover [n2_16, n2_20, n2_28, n2_47, n2_53, n2_60, n2_68] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_20 (rejectCons r2_n2_28 (rejectCons r2_n2_47 (rejectCons r2_n2_53 (rejectCons r2_n2_60 (rejectCons r2_n2_68 (rejectNil 6))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_13 : ¬ attainable 7 n1_13 := by
  exact stepCover [n2_2, n2_16, n2_29, n2_36, n2_53] (by decide +kernel) (rejectCons r2_n2_2 (rejectCons r2_n2_16 (rejectCons r2_n2_29 (rejectCons r2_n2_36 (rejectCons r2_n2_53 (rejectNil 6))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_14 : ¬ attainable 7 n1_14 := by
  exact stepCover [n2_3, n2_16, n2_19, n2_30, n2_37, n2_43, n2_53] (by decide +kernel) (rejectCons r2_n2_3 (rejectCons r2_n2_16 (rejectCons r2_n2_19 (rejectCons r2_n2_30 (rejectCons r2_n2_37 (rejectCons r2_n2_43 (rejectCons r2_n2_53 (rejectNil 6))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_15 : ¬ attainable 7 n1_15 := by
  exact stepCover [n2_16, n2_22, n2_53] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_22 (rejectCons r2_n2_53 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_16 : ¬ attainable 7 n1_16 := by
  exact stepCover [n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_17 : ¬ attainable 7 n1_17 := by
  exact stepCover [n2_4, n2_16, n2_38, n2_53, n2_61] (by decide +kernel) (rejectCons r2_n2_4 (rejectCons r2_n2_16 (rejectCons r2_n2_38 (rejectCons r2_n2_53 (rejectCons r2_n2_61 (rejectNil 6))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_18 : ¬ attainable 7 n1_18 := by
  exact stepCover [n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_19 : ¬ attainable 7 n1_19 := by
  exact stepCover [n2_10, n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_10 (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_20 : ¬ attainable 7 n1_20 := by
  exact stepCover [n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_21 : ¬ attainable 7 n1_21 := by
  exact stepCover [n2_7, n2_49, n2_53, n2_54, n2_55, n2_65, n2_70] (by decide +kernel) (rejectCons r2_n2_7 (rejectCons r2_n2_49 (rejectCons r2_n2_53 (rejectCons r2_n2_54 (rejectCons r2_n2_55 (rejectCons r2_n2_65 (rejectCons r2_n2_70 (rejectNil 6))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_22 : ¬ attainable 7 n1_22 := by
  exact stepCover [n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_23 : ¬ attainable 7 n1_23 := by
  exact stepCover [n2_16, n2_50, n2_53] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_50 (rejectCons r2_n2_53 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_24 : ¬ attainable 7 n1_24 := by
  exact stepCover [n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_25 : ¬ attainable 7 n1_25 := by
  exact stepCover [n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_26 : ¬ attainable 7 n1_26 := by
  exact stepCover [n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_27 : ¬ attainable 7 n1_27 := by
  exact stepCover [n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_28 : ¬ attainable 7 n1_28 := by
  exact stepCover [n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_29 : ¬ attainable 7 n1_29 := by
  exact stepCover [n2_5, n2_16, n2_26, n2_45, n2_51, n2_53, n2_63] (by decide +kernel) (rejectCons r2_n2_5 (rejectCons r2_n2_16 (rejectCons r2_n2_26 (rejectCons r2_n2_45 (rejectCons r2_n2_51 (rejectCons r2_n2_53 (rejectCons r2_n2_63 (rejectNil 6))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_30 : ¬ attainable 7 n1_30 := by
  exact stepCover [n2_0, n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_0 (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_31 : ¬ attainable 7 n1_31 := by
  exact stepCover [n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_32 : ¬ attainable 7 n1_32 := by
  exact stepCover [n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_33 : ¬ attainable 7 n1_33 := by
  exact stepCover [n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_34 : ¬ attainable 7 n1_34 := by
  exact stepCover [n2_6, n2_16, n2_40, n2_44, n2_52, n2_53, n2_64] (by decide +kernel) (rejectCons r2_n2_6 (rejectCons r2_n2_16 (rejectCons r2_n2_40 (rejectCons r2_n2_44 (rejectCons r2_n2_52 (rejectCons r2_n2_53 (rejectCons r2_n2_64 (rejectNil 6))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_35 : ¬ attainable 7 n1_35 := by
  exact stepCover [n2_8, n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_8 (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_36 : ¬ attainable 7 n1_36 := by
  exact stepCover [n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n2_16 : ¬ attainable 7 n2_16 := by
  exact stepCover [n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_38 : ¬ attainable 7 n1_38 := by
  exact stepCover [n2_7, n2_16, n2_49, n2_53, n2_54, n2_55, n2_65, n2_70] (by decide +kernel) (rejectCons r2_n2_7 (rejectCons r2_n2_16 (rejectCons r2_n2_49 (rejectCons r2_n2_53 (rejectCons r2_n2_54 (rejectCons r2_n2_55 (rejectCons r2_n2_65 (rejectCons r2_n2_70 (rejectNil 6)))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_39 : ¬ attainable 7 n1_39 := by
  exact stepCover [n2_13, n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_13 (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_40 : ¬ attainable 7 n1_40 := by
  exact stepCover [n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_41 : ¬ attainable 7 n1_41 := by
  exact stepCover [n2_12, n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_12 (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_42 : ¬ attainable 7 n1_42 := by
  exact stepCover [n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_43 : ¬ attainable 7 n1_43 := by
  exact stepCover [n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_44 : ¬ attainable 7 n1_44 := by
  exact stepCover [n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_45 : ¬ attainable 7 n1_45 := by
  exact stepCover [n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_46 : ¬ attainable 7 n1_46 := by
  exact stepCover [n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_47 : ¬ attainable 7 n1_47 := by
  exact stepCover [n2_7, n2_49, n2_53, n2_54, n2_55, n2_65, n2_70] (by decide +kernel) (rejectCons r2_n2_7 (rejectCons r2_n2_49 (rejectCons r2_n2_53 (rejectCons r2_n2_54 (rejectCons r2_n2_55 (rejectCons r2_n2_65 (rejectCons r2_n2_70 (rejectNil 6))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_48 : ¬ attainable 7 n1_48 := by
  exact stepCover [n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_49 : ¬ attainable 7 n1_49 := by
  exact stepCover [n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_50 : ¬ attainable 7 n1_50 := by
  exact stepCover [n2_15, n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_15 (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_51 : ¬ attainable 7 n1_51 := by
  exact stepCover [n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_52 : ¬ attainable 7 n1_52 := by
  exact stepCover [n2_9, n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_9 (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_53 : ¬ attainable 7 n1_53 := by
  exact stepCover [n2_7, n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_7 (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_54 : ¬ attainable 7 n1_54 := by
  exact stepCover [n2_16, n2_53, n2_65] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectCons r2_n2_65 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_55 : ¬ attainable 7 n1_55 := by
  exact stepCover [n2_14, n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_14 (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_56 : ¬ attainable 7 n1_56 := by
  exact stepCover [n2_1, n2_11, n2_14, n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_1 (rejectCons r2_n2_11 (rejectCons r2_n2_14 (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_57 : ¬ attainable 7 n1_57 := by
  exact stepCover [n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_58 : ¬ attainable 7 n1_58 := by
  exact stepCover [n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_59 : ¬ attainable 7 n1_59 := by
  exact stepCover [n2_16, n2_53, n2_55] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectCons r2_n2_55 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_60 : ¬ attainable 7 n1_60 := by
  exact stepCover [n2_16, n2_53, n2_54] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectCons r2_n2_54 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_61 : ¬ attainable 7 n1_61 := by
  exact stepCover [n2_16, n2_54] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_54 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_62 : ¬ attainable 7 n1_62 := by
  exact stepCover [n2_16, n2_55] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_55 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_63 : ¬ attainable 7 n1_63 := by
  exact stepCover [n2_16, n2_49] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_49 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_64 : ¬ attainable 7 n1_64 := by
  exact stepCover [n2_16, n2_49, n2_53] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_49 (rejectCons r2_n2_53 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_65 : ¬ attainable 7 n1_65 := by
  exact stepCover [n2_7, n2_49, n2_53, n2_54, n2_55, n2_65, n2_70] (by decide +kernel) (rejectCons r2_n2_7 (rejectCons r2_n2_49 (rejectCons r2_n2_53 (rejectCons r2_n2_54 (rejectCons r2_n2_55 (rejectCons r2_n2_65 (rejectCons r2_n2_70 (rejectNil 6))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_66 : ¬ attainable 7 n1_66 := by
  exact stepCover [n2_16] (by decide +kernel) (rejectCons r2_n2_16 (rejectNil 6))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_67 : ¬ attainable 7 n1_67 := by
  exact stepCover [n2_16, n2_65] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_65 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_68 : ¬ attainable 7 n1_68 := by
  exact stepCover [n2_16] (by decide +kernel) (rejectCons r2_n2_16 (rejectNil 6))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_69 : ¬ attainable 7 n1_69 := by
  exact stepCover [n2_1, n2_16, n2_53] (by decide +kernel) (rejectCons r2_n2_1 (rejectCons r2_n2_16 (rejectCons r2_n2_53 (rejectNil 6))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r0_wires : ¬ attainable 8 wires := by
  exact stepCover [n1_0, n1_1, n1_2, n1_3, n1_4, n1_5, n1_6, n1_7, n1_8, n1_9, n1_10, n1_11, n1_12, n1_13, n1_14, n1_15, n1_16, n1_17, n1_18, n1_19, n1_20, n1_21, n1_22, n1_23, n1_24, n1_25, n1_26, n1_27, n1_28, n1_29, n1_30, n1_31, n1_32, n1_33, n1_34, n1_35, n1_36, n2_16, n1_38, n1_39, n1_40, n1_41, n1_42, n1_43, n1_44, n1_45, n1_46, n1_47, n1_48, n1_49, n1_50, n1_51, n1_52, n1_53, n1_54, n1_55, n1_56, n1_57, n1_58, n1_59, n1_60, n1_61, n1_62, n1_63, n1_64, n1_65, n1_66, n1_67, n1_68, n1_69] (by decide +kernel) (rejectCons r1_n1_0 (rejectCons r1_n1_1 (rejectCons r1_n1_2 (rejectCons r1_n1_3 (rejectCons r1_n1_4 (rejectCons r1_n1_5 (rejectCons r1_n1_6 (rejectCons r1_n1_7 (rejectCons r1_n1_8 (rejectCons r1_n1_9 (rejectCons r1_n1_10 (rejectCons r1_n1_11 (rejectCons r1_n1_12 (rejectCons r1_n1_13 (rejectCons r1_n1_14 (rejectCons r1_n1_15 (rejectCons r1_n1_16 (rejectCons r1_n1_17 (rejectCons r1_n1_18 (rejectCons r1_n1_19 (rejectCons r1_n1_20 (rejectCons r1_n1_21 (rejectCons r1_n1_22 (rejectCons r1_n1_23 (rejectCons r1_n1_24 (rejectCons r1_n1_25 (rejectCons r1_n1_26 (rejectCons r1_n1_27 (rejectCons r1_n1_28 (rejectCons r1_n1_29 (rejectCons r1_n1_30 (rejectCons r1_n1_31 (rejectCons r1_n1_32 (rejectCons r1_n1_33 (rejectCons r1_n1_34 (rejectCons r1_n1_35 (rejectCons r1_n1_36 (rejectCons r1_n2_16 (rejectCons r1_n1_38 (rejectCons r1_n1_39 (rejectCons r1_n1_40 (rejectCons r1_n1_41 (rejectCons r1_n1_42 (rejectCons r1_n1_43 (rejectCons r1_n1_44 (rejectCons r1_n1_45 (rejectCons r1_n1_46 (rejectCons r1_n1_47 (rejectCons r1_n1_48 (rejectCons r1_n1_49 (rejectCons r1_n1_50 (rejectCons r1_n1_51 (rejectCons r1_n1_52 (rejectCons r1_n1_53 (rejectCons r1_n1_54 (rejectCons r1_n1_55 (rejectCons r1_n1_56 (rejectCons r1_n1_57 (rejectCons r1_n1_58 (rejectCons r1_n1_59 (rejectCons r1_n1_60 (rejectCons r1_n1_61 (rejectCons r1_n1_62 (rejectCons r1_n1_63 (rejectCons r1_n1_64 (rejectCons r1_n1_65 (rejectCons r1_n1_66 (rejectCons r1_n1_67 (rejectCons r1_n1_68 (rejectCons r1_n1_69 (rejectNil 7)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Case25

theorem no25 (rest : List PEqualNP.CircuitLowerBounds.Gate) (o : Nat) (hs : ∀ g ∈ rest, CircuitSatBridge.Supported g) (hlen : rest.length ≤ 8) (hr : ∀ x : Fin 128, (CircuitSatBridge.run rest (bank 2 5 x)).getD o false = target x) : False :=
  Case25.r0_wires (Case25.suffix rest o hs hlen hr)

namespace Case34
open CircuitSatBridge FreeSupport PEqualNP.CircuitLowerBounds
def w0 := mkSampleWire 0 0 0 0 0 0
def w1 := mkSampleWire 270532608 87 0 0 0 0
def w2 := mkSampleWire 33570902 277293832200 328967 0 0 0
def w3 := mkSampleWire 687748940544 618713350144 34210304 0 0 0
def w4 := mkSampleWire 10804530304 12848160 68157713 0 0 0
def w5 := mkSampleWire 11075062912 12848247 68157713 0 0 0
def w6 := mkSampleWire 10838101206 277306678312 68486423 0 0 0
def w7 := mkSampleWire 11108633814 277306678399 68486423 0 0 0
def w8 := mkSampleWire 395137257473 138648490496 276826308 0 0 0
def w9 := mkSampleWire 395170828375 415942318600 277155271 0 0 0
def w10 := mkSampleWire 1082886198017 757226574336 311036612 0 0 0
def w11 := mkSampleWire 5369921544 77896704128 538985000 0 0 0
def w12 := mkSampleWire 693118862088 627857023104 573194792 0 0 0
def w13 := mkSampleWire 146874400 55834779904 692105216 0 0 0
def w14 := mkSampleWire 417407008 55834779991 692105216 0 0 0
def w15 := mkSampleWire 5516795944 133731410304 694219304 0 0 0
def w16 := mkSampleWire 5787328552 133731410391 694219304 0 0 0
def w17 := mkSampleWire 0 91314720768 402657792 540424612 85946011658 4608
def w18 := mkSampleWire 0 275147399168 16788612 17188291136 269492320 8320
def w19 := mkSampleWire 0 846377091072 4228100 417131987985 828928786576 33796
def w20 := mkSampleWire 0 893621731328 852017 279323870224 824633786384 65552
def w21 := mkSampleWire 0 184565760 2228249 44023955456 150995204 131081
def w22 := mkSampleWire 0 275298410496 344065 61212246592 420487524 262145
def w23 := mkSampleWire 0 639962746880 1572868 138345132165 90198544514 524292
def w24 := mkSampleWire 270532608 1254621271 9568320 3410208 42467336 1048640
def w25 := mkSampleWire 11075062912 1254886519 76677457 3410208 42467336 1048640
def w26 := mkSampleWire 0 1137199104 69206024 620630378794 1116227593 2097152
def w27 := mkSampleWire 11075062912 46400631 70385688 3410208 42468360 3276872
def w28 := mkSampleWire 0 1225279488 8388929 664650924042 1224755461 8388865
def w29 := mkSampleWire 11075062912 1271680119 78774617 664654334250 1267223821 11665737
def w30 := mkSampleWire 11108633814 278565510271 79103327 664654334250 1267223821 11665737
def w31 := mkSampleWire 698824003456 619817258103 112853849 664654334250 1267223821 11665737
def w32 := mkSampleWire 406212320385 138711686775 347212253 664654334250 1267223821 11665737
def w33 := mkSampleWire 16444984456 79118036215 615662457 664654334250 1267223821 11665737
def w34 := mkSampleWire 11221937312 57106460023 770879833 664654334250 1267223821 11665737
def w35 := mkSampleWire 11075062912 276419079287 95563229 681842625386 1536716141 11674057
def w36 := mkSampleWire 11075062912 276419079287 79118681 681842625386 1536716141 11927881
def w37 := mkSampleWire 0 90206967808 71335968 537014404 85903544322 71303200
def w38 := mkSampleWire 10838101206 917256903720 73237815 417669002389 914832593042 71926838
def w39 := mkSampleWire 11108633814 917256903807 73237815 417669002389 914832593042 71926838
def w40 := mkSampleWire 698587041750 917494930472 106923831 417669002389 914832593042 71926838
def w41 := mkSampleWire 405975358679 1055905390120 350064119 417669002389 914832593042 71926838
def w42 := mkSampleWire 16208022750 926434065576 612222783 417669002389 914832593042 71926838
def w43 := mkSampleWire 10984975606 951616781608 761115959 417669002389 914832593042 71926838
def w44 := mkSampleWire 11108633814 918515735679 83854719 1082323336639 916099816863 83592575
def w45 := mkSampleWire 270532608 571231731799 167778436 137808117761 4295000192 167774212
def w46 := mkSampleWire 417407008 605591675223 725661828 137808117761 4295000192 167774212
def w47 := mkSampleWire 417407008 55834706263 155237508 137808117761 4295131264 167816324
def w48 := mkSampleWire 1082886198017 778713993728 446307012 138348542373 227747074186 169351748
def w49 := mkSampleWire 1083156730625 778713993815 446307012 138348542373 227747074186 169351748
def w50 := mkSampleWire 1083190301527 1056007821919 446635975 138348542373 227747074186 169351748
def w51 := mkSampleWire 1093961260929 778714259063 513416149 138348542373 227747074186 169351748
def w52 := mkSampleWire 1088526652169 787857666775 985291500 138348542373 227747074186 169351748
def w53 := mkSampleWire 1083303605025 813073937239 1004190404 138348542373 227747074186 169351748
def w54 := mkSampleWire 1093961260929 778731052663 515513309 802999466415 228971830671 179968845
def w55 := mkSampleWire 11108633814 917257952383 241016247 417669002389 914832593042 239701046
def w56 := mkSampleWire 1083156730625 778714061399 517642980 138348542373 227747074186 240654948
def w57 := mkSampleWire 1093994831831 1056008150655 517971959 417672412597 1052381122714 240754294
def w58 := mkSampleWire 0 1091074048 285237248 620626968586 1073760257 285229056
def w59 := mkSampleWire 395170828375 415959120392 293957063 681839215178 3641731941 293888385
def w60 := mkSampleWire 395441360983 415959120479 293957063 681839215178 3641731941 293888385
def w61 := mkSampleWire 1082919768919 1034537204232 328167367 681839215178 3641731941 293888385
def w62 := mkSampleWire 405975358679 415971966504 362114519 681839215178 3641731941 293888385
def w63 := mkSampleWire 406245891287 415971966591 362114519 681839215178 3641731941 293888385
def w64 := mkSampleWire 400540749919 493839022728 832925679 681839215178 3641731941 293888385
def w65 := mkSampleWire 395317702775 471793892104 969276871 681839215178 3641731941 293888385
def w66 := mkSampleWire 395170828375 415992674824 296185311 681839215178 3641731941 294019465
def w67 := mkSampleWire 11075062912 1271692407 364011865 664654334250 1267223821 296894793
def w68 := mkSampleWire 406245891287 416005521023 364342751 681842625386 3684200301 297165257
def w69 := mkSampleWire 1088289690463 217501930120 269304354 537014404 269045993986 357388850
def w70 := mkSampleWire 5516795944 134818265472 1029763624 621167393198 121916381195 358634016
def w71 := mkSampleWire 5787328552 134818265559 1029763624 621167393198 121916381195 358634016
def w72 := mkSampleWire 5550366846 412112091528 1030092591 621167393198 121916381195 358634016
def w73 := mkSampleWire 16321326248 134818528672 1030812473 621167393198 121916381195 358634016
def w74 := mkSampleWire 400654053417 272392485760 1038154476 621167393198 121916381195 358634016
def w75 := mkSampleWire 693265736488 684778584448 1063973416 621167393198 121916381195 358634016
def w76 := mkSampleWire 16354897150 961868201384 1031665471 1038299381183 950845429915 359257654
def w77 := mkSampleWire 5787328552 134952483287 1039331944 621167393198 121916381195 359682656
def w78 := mkSampleWire 405975358679 1055922191912 366865911 1099508217567 918474324983 365815223
def w79 := mkSampleWire 400687624319 549686311816 1038483439 682379639790 124484352879 367293345
def w80 := mkSampleWire 16591858856 134952746487 1039332217 665191348654 122067377423 368202601
def w81 := mkSampleWire 1099094220767 218773610152 348078971 665191348654 270313217807 369054587
def w82 := mkSampleWire 1083190301527 1056024623711 463437767 820187757551 231388806127 463240133
def w83 := mkSampleWire 1088673526569 822217538519 1073412844 758975510959 263717443723 527981156
def w84 := mkSampleWire 406392765687 196508262271 500219334 758975510959 265865322123 536412134
def w85 := mkSampleWire 0 824903311360 570425344 296512161360 824903278704 536870912
def w86 := mkSampleWire 693118862088 903003365504 573522489 340536116816 833646305652 537329689
def w87 := mkSampleWire 693389394696 903003365591 573522489 340536116816 833646305652 537329689
def w88 := mkSampleWire 693152432990 905150855304 573523775 340536116816 833646305652 537329689
def w89 := mkSampleWire 703923392392 903016213664 641680185 340536116816 833646305652 537329689
def w90 := mkSampleWire 693265736488 958838071680 728756793 340536116816 833646305652 537329689
def w91 := mkSampleWire 693536269096 958838071767 728756793 340536116816 833646305652 537329689
def w92 := mkSampleWire 1088256119561 1041516589696 850348797 340536116816 833646305652 537329689
def w93 := mkSampleWire 693118862088 903003365504 590311101 340536116816 833646305652 537338009
def w94 := mkSampleWire 704193925000 904090479863 650068857 961166495610 834762534269 548864345
def w95 := mkSampleWire 703956963294 926638537896 645908287 478881248981 923845112310 609190975
def w96 := mkSampleWire 417407008 880738017623 725662852 434320279121 829198409968 704687236
def w97 := mkSampleWire 450977910 882885507423 725990791 434320279121 829198409968 704687236
def w98 := mkSampleWire 688166347552 949694472535 726318724 434320279121 829198409968 704687236
def w99 := mkSampleWire 5787328552 958634648023 727776940 434320279121 829198409968 704687236
def w100 := mkSampleWire 11221937312 880750865783 793820565 434320279121 829198409968 704687236
def w101 := mkSampleWire 395554664481 1019385459543 1002486980 434320279121 829198409968 704687236
def w102 := mkSampleWire 417407008 949457494359 726514869 434320279121 829198409968 704752788
def w103 := mkSampleWire 417407008 880922583383 727891101 478344234577 829349405172 704818317
def w104 := mkSampleWire 417407008 880889028951 726006917 478344234577 829349405172 704949381
def w105 := mkSampleWire 693536269096 958838071767 728759997 478344234577 837941436916 705146013
def w106 := mkSampleWire 1083303605025 1088220279639 1004191428 434860703733 1052650483962 706264772
def w107 := mkSampleWire 1088526652169 1063004009175 985619197 478884659189 1061393379838 706681437
def w108 := mkSampleWire 1093994831831 964693362303 43978199 478344234577 977595246580 715107807
def w109 := mkSampleWire 1094141706231 1020528142207 736083415 478344234577 977595246580 715107807
def w110 := mkSampleWire 11221937312 882009697655 804437469 1098974613371 830465633789 716352973
def w111 := mkSampleWire 11255508214 951617830271 794672567 434857293525 915102216434 776580278
def w112 := mkSampleWire 704340799400 683552507383 779784760 417672412597 1095869895834 779853438
def w113 := mkSampleWire 1088289690463 1043664075400 867135487 961163085402 836867550069 830955929
def w114 := mkSampleWire 693265736488 959924926848 1064301113 961703510014 955562686847 895963705
def w115 := mkSampleWire 16354897150 320797633960 627434811 961163085402 871764553589 904390075
def w116 := mkSampleWire 395588235383 1021549738847 1002831303 1098971203163 832570649589 998567301
def w117 := mkSampleWire 1088673526569 182254724055 1000504008 681842625386 184679034733 1001814985
def w118 := mkSampleWire 1099478056873 182267572215 1068661721 681842625386 184679034733 1001814985
def w119 := mkSampleWire 1088436564863 1098239947656 994967206 434857293525 1098244403954 1062076086
def w120 := mkSampleWire 5787328552 959721503191 1063321260 1055487672319 951114791163 1063321252
def w121 := mkSampleWire 1099241095167 1099511627688 1073741823 1099511627775 1099511627775 1073741823
def w122 := mkSampleWire 1099511627775 1099511627775 1073741823 1099511627775 1099511627775 1073741823
def wires : List Wire := [w0, w86, w70, w96, w29, w38, w59, w1, w49]
def n1_0 : List Wire := [w1, w4, w38, w59, w49, w86, w96, w70]
def n1_1 : List Wire := [w1, w38, w29, w59, w49, w86, w13, w70]
def n1_2 : List Wire := [w1, w38, w29, w59, w49, w86, w96, w70]
def n1_3 : List Wire := [w1, w38, w29, w59, w49, w86, w96, w71]
def n1_4 : List Wire := [w1, w38, w29, w59, w49, w86, w105, w70]
def n1_5 : List Wire := [w1, w38, w29, w59, w49, w87, w96, w70]
def n1_6 : List Wire := [w1, w38, w29, w60, w49, w86, w96, w70]
def n1_7 : List Wire := [w1, w38, w59, w49, w86, w110, w70]
def n1_8 : List Wire := [w1, w38, w59, w68, w49, w86, w96, w70]
def n1_9 : List Wire := [w1, w39, w29, w59, w49, w86, w96, w70]
def n1_10 : List Wire := [w2, w38, w29, w59, w49, w86, w96, w70]
def n1_11 : List Wire := [w3, w38, w29, w59, w49, w86, w96, w70]
def n1_12 : List Wire := [w4, w38, w29, w59, w49, w86, w96, w70]
def n1_13 : List Wire := [w4, w38, w59, w49, w86, w96, w70]
def n1_14 : List Wire := [w18, w38, w29, w59, w49, w86, w96, w70]
def n1_15 : List Wire := [w19, w38, w29, w59, w49, w86, w96, w70]
def n1_16 : List Wire := [w20, w38, w29, w59, w49, w86, w96, w70]
def n1_17 : List Wire := [w21, w38, w29, w59, w49, w86, w96, w70]
def n1_18 : List Wire := [w22, w38, w29, w59, w49, w86, w96, w70]
def n1_19 : List Wire := [w23, w38, w29, w59, w49, w86, w96, w70]
def n1_20 : List Wire := [w24, w38, w29, w59, w49, w86, w96, w70]
def n1_21 : List Wire := [w26, w38, w29, w59, w49, w86, w96, w70]
def n1_22 : List Wire := [w28, w38, w29, w59, w49, w86, w96, w70]
def n1_23 : List Wire := [w29, w59, w49, w86, w96, w117, w70]
def n1_24 : List Wire := [w37, w38, w29, w59, w49, w86, w96, w70]
def n1_25 : List Wire := [w38, w29, w8, w59, w49, w86, w96, w70]
def n1_26 : List Wire := [w38, w29, w44, w59, w49, w86, w96, w70]
def n1_27 : List Wire := [w38, w29, w45, w59, w49, w86, w96, w70]
def n1_28 : List Wire := [w38, w29, w49, w86, w96, w112, w70]
def n1_29 : List Wire := [w38, w29, w58, w59, w49, w86, w96, w70]
def n1_30 : List Wire := [w38, w29, w59, w17, w49, w86, w96, w70]
def n1_31 : List Wire := [w38, w29, w59, w49, w11, w86, w96, w70]
def n1_32 : List Wire := [w38, w29, w59, w49, w54, w86, w96, w70]
def n1_33 : List Wire := [w38, w29, w59, w49, w57, w86, w96, w70]
def n1_34 : List Wire := [w38, w29, w59, w49, w82, w86, w96, w70]
def n1_35 : List Wire := [w38, w29, w59, w49, w84, w86, w96, w70]
def n1_36 : List Wire := [w38, w29, w59, w49, w84, w96, w70]
def n1_37 : List Wire := [w38, w29, w59, w49, w85, w86, w96, w70]
def n1_38 : List Wire := [w38, w29, w59, w49, w86, w13, w70]
def n1_39 : List Wire := [w38, w29, w59, w49, w86, w13, w96, w70]
def n1_40 : List Wire := [w38, w29, w59, w49, w86, w87, w96, w70]
def n1_41 : List Wire := [w38, w29, w59, w49, w86, w94, w96, w70]
def n1_42 : List Wire := [w38, w29, w59, w49, w86, w95, w96, w70]
def n2_32 : List Wire := [w38, w29, w59, w49, w86, w96, w70]
def n1_44 : List Wire := [w38, w29, w59, w49, w86, w96, w70, w71]
def n1_45 : List Wire := [w38, w29, w59, w49, w86, w96, w70, w76]
def n1_46 : List Wire := [w38, w29, w59, w49, w86, w96, w70, w79]
def n1_47 : List Wire := [w38, w29, w59, w49, w86, w96, w70, w80]
def n1_48 : List Wire := [w38, w29, w59, w49, w86, w96, w70, w83]
def n1_49 : List Wire := [w38, w29, w59, w49, w86, w96, w70, w114]
def n1_50 : List Wire := [w38, w29, w59, w49, w86, w96, w70, w120]
def n1_51 : List Wire := [w38, w29, w59, w49, w86, w96, w70, w121]
def n1_52 : List Wire := [w38, w29, w59, w49, w86, w96, w70, w122]
def n2_33 : List Wire := [w38, w29, w59, w49, w86, w96, w71]
def n1_54 : List Wire := [w38, w29, w59, w49, w86, w96, w105, w70]
def n1_55 : List Wire := [w38, w29, w59, w49, w86, w96, w106, w70]
def n1_56 : List Wire := [w38, w29, w59, w49, w86, w96, w107, w70]
def n1_57 : List Wire := [w38, w29, w59, w49, w86, w96, w110, w70]
def n1_58 : List Wire := [w38, w29, w59, w49, w86, w96, w111, w70]
def n1_59 : List Wire := [w38, w29, w59, w49, w86, w96, w112, w70]
def n1_60 : List Wire := [w38, w29, w59, w49, w86, w96, w113, w70]
def n1_61 : List Wire := [w38, w29, w59, w49, w86, w96, w116, w70]
def n1_62 : List Wire := [w38, w29, w59, w49, w86, w96, w117, w70]
def n1_63 : List Wire := [w38, w29, w59, w49, w86, w96, w119, w70]
def n2_47 : List Wire := [w38, w29, w59, w49, w86, w105, w70]
def n1_65 : List Wire := [w38, w29, w59, w49, w86, w110, w70]
def n1_66 : List Wire := [w38, w29, w59, w49, w86, w115, w96, w70]
def n2_51 : List Wire := [w38, w29, w59, w49, w87, w96, w70]
def n1_68 : List Wire := [w38, w29, w59, w60, w49, w86, w96, w70]
def n1_69 : List Wire := [w38, w29, w59, w68, w49, w86, w96, w70]
def n1_70 : List Wire := [w38, w29, w59, w78, w49, w86, w96, w70]
def n1_71 : List Wire := [w38, w29, w59, w81, w49, w86, w70]
def n1_72 : List Wire := [w38, w29, w59, w81, w49, w86, w96, w70]
def n1_73 : List Wire := [w38, w29, w59, w86, w115, w96, w70]
def n2_69 : List Wire := [w38, w29, w60, w49, w86, w96, w70]
def n1_75 : List Wire := [w38, w39, w29, w59, w49, w86, w96, w70]
def n1_76 : List Wire := [w38, w59, w49, w86, w96, w110, w70]
def n1_77 : List Wire := [w38, w59, w49, w86, w96, w119, w70]
def n2_91 : List Wire := [w38, w59, w68, w49, w86, w96, w70]
def n2_104 : List Wire := [w39, w29, w59, w49, w86, w96, w70]
def n1_80 : List Wire := [w108, w38, w29, w59, w49, w86, w96]
def n1_81 : List Wire := [w108, w38, w29, w59, w49, w86, w96, w70]
def n2_0 : List Wire := [w1, w6, w59, w49, w86, w96, w70]
def n2_1 : List Wire := [w1, w38, w29, w59, w49, w86, w15]
def n2_2 : List Wire := [w1, w38, w29, w59, w49, w90, w70]
def n2_3 : List Wire := [w1, w38, w62, w49, w86, w96, w70]
def n2_4 : List Wire := [w3, w38, w29, w59, w49, w105, w70]
def n2_5 : List Wire := [w4, w38, w59, w49, w86, w96, w71]
def n2_6 : List Wire := [w4, w38, w59, w49, w87, w96, w70]
def n2_7 : List Wire := [w4, w38, w60, w49, w86, w96, w70]
def n2_8 : List Wire := [w5, w38, w59, w49, w86, w96, w70]
def n2_9 : List Wire := [w5, w39, w59, w49, w86, w96, w70]
def n2_10 : List Wire := [w6, w29, w59, w49, w86, w96, w70]
def n2_11 : List Wire := [w6, w59, w68, w49, w86, w96, w70]
def n2_12 : List Wire := [w27, w38, w59, w49, w86, w96, w70]
def n2_13 : List Wire := [w29, w40, w59, w49, w86, w96, w70]
def n2_14 : List Wire := [w29, w55, w59, w49, w86, w96, w70]
def n2_15 : List Wire := [w29, w59, w41, w49, w86, w96, w70]
def n2_16 : List Wire := [w29, w59, w49, w86, w42, w96, w70]
def n2_17 : List Wire := [w29, w59, w49, w86, w96, w43, w70]
def n2_18 : List Wire := [w38, w8, w68, w49, w86, w96, w70]
def n2_19 : List Wire := [w38, w25, w59, w49, w86, w96, w70]
def n2_20 : List Wire := [w38, w29, w9, w49, w86, w96, w70]
def n2_21 : List Wire := [w38, w29, w47, w59, w49, w86, w70]
def n2_22 : List Wire := [w38, w29, w49, w86, w96, w64, w70]
def n2_23 : List Wire := [w38, w29, w49, w86, w96, w65, w70]
def n2_24 : List Wire := [w38, w29, w59, w10, w86, w96, w70]
def n2_25 : List Wire := [w38, w29, w59, w48, w86, w96, w70]
def n2_26 : List Wire := [w38, w29, w59, w49, w12, w96, w70]
def n2_27 : List Wire := [w38, w29, w59, w49, w86, w14, w70]
def n2_28 : List Wire := [w38, w29, w59, w49, w86, w14, w71]
def n2_29 : List Wire := [w38, w29, w59, w49, w86, w15, w96]
def n2_30 : List Wire := [w38, w29, w59, w49, w86, w15, w105]
def n2_31 : List Wire := [w38, w29, w59, w49, w86, w46, w70]
def n2_34 : List Wire := [w38, w29, w59, w49, w86, w96, w72]
def n2_35 : List Wire := [w38, w29, w59, w49, w86, w96, w73]
def n2_36 : List Wire := [w38, w29, w59, w49, w86, w96, w74]
def n2_37 : List Wire := [w38, w29, w59, w49, w86, w96, w75]
def n2_38 : List Wire := [w38, w29, w59, w49, w86, w96, w77]
def n2_39 : List Wire := [w38, w29, w59, w49, w86, w97, w70]
def n2_40 : List Wire := [w38, w29, w59, w49, w86, w98, w70]
def n2_41 : List Wire := [w38, w29, w59, w49, w86, w99, w70]
def n2_42 : List Wire := [w38, w29, w59, w49, w86, w100, w70]
def n2_43 : List Wire := [w38, w29, w59, w49, w86, w101, w70]
def n2_44 : List Wire := [w38, w29, w59, w49, w86, w102, w70]
def n2_45 : List Wire := [w38, w29, w59, w49, w86, w103, w70]
def n2_46 : List Wire := [w38, w29, w59, w49, w86, w104, w70]
def n2_48 : List Wire := [w38, w29, w59, w49, w86, w105, w71]
def n2_49 : List Wire := [w38, w29, w59, w49, w86, w109, w70]
def n2_50 : List Wire := [w38, w29, w59, w49, w87, w13, w70]
def n2_52 : List Wire := [w38, w29, w59, w49, w87, w96, w71]
def n2_53 : List Wire := [w38, w29, w59, w49, w87, w105, w70]
def n2_54 : List Wire := [w38, w29, w59, w49, w88, w96, w70]
def n2_55 : List Wire := [w38, w29, w59, w49, w89, w96, w70]
def n2_56 : List Wire := [w38, w29, w59, w49, w90, w70]
def n2_57 : List Wire := [w38, w29, w59, w49, w93, w96, w70]
def n2_58 : List Wire := [w38, w29, w59, w49, w94, w105, w70]
def n2_59 : List Wire := [w38, w29, w59, w49, w96, w90, w70]
def n2_60 : List Wire := [w38, w29, w59, w49, w96, w92, w70]
def n2_61 : List Wire := [w38, w29, w59, w49, w105, w70, w114]
def n2_62 : List Wire := [w38, w29, w59, w49, w105, w113, w70]
def n2_63 : List Wire := [w38, w29, w59, w50, w86, w96, w70]
def n2_64 : List Wire := [w38, w29, w59, w51, w86, w96, w70]
def n2_65 : List Wire := [w38, w29, w59, w56, w86, w96, w70]
def n2_66 : List Wire := [w38, w29, w59, w86, w96, w52, w70]
def n2_67 : List Wire := [w38, w29, w59, w86, w96, w53, w70]
def n2_68 : List Wire := [w38, w29, w60, w49, w86, w13, w70]
def n2_70 : List Wire := [w38, w29, w60, w49, w86, w96, w71]
def n2_71 : List Wire := [w38, w29, w60, w49, w86, w105, w70]
def n2_72 : List Wire := [w38, w29, w60, w49, w87, w96, w70]
def n2_73 : List Wire := [w38, w29, w61, w49, w86, w96, w70]
def n2_74 : List Wire := [w38, w29, w62, w49, w86, w96, w70]
def n2_75 : List Wire := [w38, w29, w66, w49, w86, w96, w70]
def n2_76 : List Wire := [w38, w30, w59, w49, w86, w96, w70]
def n2_77 : List Wire := [w38, w31, w59, w49, w86, w96, w70]
def n2_78 : List Wire := [w38, w35, w59, w49, w86, w96, w70]
def n2_79 : List Wire := [w38, w36, w59, w49, w86, w96, w70]
def n2_80 : List Wire := [w38, w49, w86, w112, w110, w70]
def n2_81 : List Wire := [w38, w59, w32, w49, w86, w96, w70]
def n2_82 : List Wire := [w38, w59, w49, w84, w110, w70]
def n2_83 : List Wire := [w38, w59, w49, w86, w33, w96, w70]
def n2_84 : List Wire := [w38, w59, w49, w86, w34, w70]
def n2_85 : List Wire := [w38, w59, w49, w86, w96, w34, w70]
def n2_86 : List Wire := [w38, w59, w49, w86, w96, w70, w118]
def n2_87 : List Wire := [w38, w59, w49, w86, w100, w70]
def n2_88 : List Wire := [w38, w59, w49, w86, w110, w70]
def n2_89 : List Wire := [w38, w59, w49, w87, w110, w70]
def n2_90 : List Wire := [w38, w59, w67, w49, w86, w96, w70]
def n2_92 : List Wire := [w38, w59, w68, w49, w86, w96, w71]
def n2_93 : List Wire := [w38, w59, w68, w49, w86, w105, w70]
def n2_94 : List Wire := [w38, w59, w68, w49, w87, w96, w70]
def n2_95 : List Wire := [w38, w59, w86, w115, w110, w70]
def n2_96 : List Wire := [w38, w60, w49, w86, w110, w70]
def n2_97 : List Wire := [w38, w60, w68, w49, w86, w96, w70]
def n2_98 : List Wire := [w38, w62, w49, w86, w96, w70]
def n2_99 : List Wire := [w38, w68, w49, w86, w96, w113, w70]
def n2_100 : List Wire := [w38, w68, w49, w86, w96, w116, w70]
def n2_101 : List Wire := [w38, w68, w78, w49, w86, w96, w70]
def n2_102 : List Wire := [w38, w69, w59, w49, w86, w70]
def n2_103 : List Wire := [w39, w29, w59, w49, w86, w13, w70]
def n2_105 : List Wire := [w39, w29, w59, w49, w86, w96, w71]
def n2_106 : List Wire := [w39, w29, w59, w49, w86, w105, w70]
def n2_107 : List Wire := [w39, w29, w59, w49, w87, w96, w70]
def n2_108 : List Wire := [w39, w29, w60, w49, w86, w96, w70]
def n2_109 : List Wire := [w39, w59, w68, w49, w86, w96, w70]
def n2_110 : List Wire := [w59, w49, w86, w110, w117, w70]
def n2_111 : List Wire := [w108, w38, w59, w49, w86, w110]
def n3_0 : List Wire := [w6, w59, w49, w86, w96, w71]
def n3_1 : List Wire := [w6, w59, w49, w87, w96, w70]
def n3_2 : List Wire := [w6, w60, w49, w86, w96, w70]
def n3_3 : List Wire := [w7, w59, w49, w86, w96, w70]
def n3_4 : List Wire := [w38, w29, w59, w49, w86, w16]
def n3_5 : List Wire := [w38, w29, w59, w49, w87, w15]
def n3_6 : List Wire := [w38, w29, w59, w49, w91, w70]
def n3_7 : List Wire := [w38, w29, w59, w49, w91, w71]
def n3_8 : List Wire := [w38, w29, w59, w49, w105, w75]
def n3_9 : List Wire := [w38, w29, w60, w49, w86, w15]
def n3_10 : List Wire := [w38, w29, w60, w49, w90, w70]
def n3_11 : List Wire := [w38, w29, w61, w49, w105, w70]
def n3_12 : List Wire := [w38, w31, w59, w49, w105, w70]
def n3_13 : List Wire := [w38, w62, w49, w86, w96, w71]
def n3_14 : List Wire := [w38, w62, w49, w87, w96, w70]
def n3_15 : List Wire := [w38, w63, w49, w86, w96, w70]
def n3_16 : List Wire := [w38, w68, w49, w86, w101, w70]
def n3_17 : List Wire := [w38, w68, w49, w96, w92, w70]
def n3_18 : List Wire := [w38, w68, w49, w105, w113, w70]
def n3_19 : List Wire := [w39, w29, w59, w49, w86, w15]
def n3_20 : List Wire := [w39, w29, w59, w49, w90, w70]
def n3_21 : List Wire := [w39, w63, w49, w86, w96, w70]
def n3_22 : List Wire := [w41, w68, w49, w86, w96, w70]
def test (t : Fin 110) (b : Bool) : Fin 128 :=
  let pts : List (Fin 128) := if b then [41, 84, 37, 84, 42, 21, 74, 37, 21, 74, 42, 21, 37, 37, 82, 74, 41, 37, 21, 82, 21, 21, 84, 74, 42, 41, 41, 42, 41, 37, 82, 84, 42, 82, 74, 82, 84, 41, 42, 84, 84, 37, 82, 21, 42, 74, 74, 41, 82, 64, 16, 84, 37, 74, 84, 41, 42, 8, 32, 21, 74, 2, 37, 21, 82, 21, 1, 82, 74, 4, 84, 64, 41, 2, 37, 4, 37, 1, 42, 42, 82, 32, 41, 18, 34, 36, 17, 72, 80, 5, 40, 9, 5, 72, 68, 40, 34, 18, 66, 33, 17, 20, 36, 80, 68, 9, 36, 9, 68, 10] else [65, 96, 96, 6, 96, 12, 96, 48, 3, 3, 48, 48, 65, 12, 96, 6, 12, 6, 65, 3, 6, 24, 12, 12, 3, 96, 48, 12, 24, 3, 6, 48, 6, 48, 65, 65, 65, 3, 65, 3, 24, 24, 24, 96, 24, 48, 24, 6, 12, 65, 48, 116, 101, 78, 86, 43, 46, 12, 48, 85, 75, 3, 53, 53, 86, 23, 3, 83, 106, 6, 85, 96, 45, 6, 45, 12, 39, 65, 106, 43, 114, 96, 105, 22, 50, 38, 81, 73, 112, 7, 104, 73, 13, 76, 70, 44, 98, 19, 98, 35, 49, 22, 44, 81, 76, 11, 52, 13, 69, 14]
  pts.getD t.val 0

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem samples : ∀ t : Fin 110, ∀ b : Bool,
    sample wires t b = bank 3 4 (test t b) ∧ target (test t b) = !b := by decide +kernel

theorem suffix (rest : List Gate) (o : Nat) (hs : ∀ g ∈ rest, Supported g) (hlen : rest.length ≤ 8)
    (hr : ∀ x : Fin 128, (run rest (bank 3 4 x)).getD o false = target x) :
    attainable 8 wires := by
  obtain ⟨cs,hl,hv,he⟩ := fixed_slots 7 9 o rest hs hlen
  refine ⟨cs,16,hl,hv,?_⟩
  intro t
  have h (b : Bool) : (runChoices cs (sample wires t b)).getD 16 false = !b := by
    rw [(samples t b).1, he]
    · exact (hr _).trans (samples t b).2
    · simp [bank]
  exact ⟨h false, h true⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_0 : ¬ attainable 5 n3_0 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_1 : ¬ attainable 5 n3_1 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_2 : ¬ attainable 5 n3_2 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_3 : ¬ attainable 5 n3_3 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_4 : ¬ attainable 5 n3_4 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_5 : ¬ attainable 5 n3_5 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_6 : ¬ attainable 5 n3_6 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_7 : ¬ attainable 5 n3_7 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_8 : ¬ attainable 5 n3_8 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_9 : ¬ attainable 5 n3_9 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_10 : ¬ attainable 5 n3_10 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_11 : ¬ attainable 5 n3_11 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_12 : ¬ attainable 5 n3_12 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_13 : ¬ attainable 5 n3_13 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_14 : ¬ attainable 5 n3_14 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_15 : ¬ attainable 5 n3_15 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_16 : ¬ attainable 5 n3_16 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_17 : ¬ attainable 5 n3_17 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_18 : ¬ attainable 5 n3_18 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_19 : ¬ attainable 5 n3_19 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_20 : ¬ attainable 5 n3_20 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_21 : ¬ attainable 5 n3_21 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_22 : ¬ attainable 5 n3_22 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_0 : ¬ attainable 6 n2_0 := by
  exact stepCover [n3_0, n3_1, n3_2, n3_3] (by decide +kernel) (rejectCons r3_n3_0 (rejectCons r3_n3_1 (rejectCons r3_n3_2 (rejectCons r3_n3_3 (rejectNil 5)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_1 : ¬ attainable 6 n2_1 := by
  exact stepCover [n3_4, n3_5, n3_9, n3_19] (by decide +kernel) (rejectCons r3_n3_4 (rejectCons r3_n3_5 (rejectCons r3_n3_9 (rejectCons r3_n3_19 (rejectNil 5)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_2 : ¬ attainable 6 n2_2 := by
  exact stepCover [n3_6, n3_10, n3_20] (by decide +kernel) (rejectCons r3_n3_6 (rejectCons r3_n3_10 (rejectCons r3_n3_20 (rejectNil 5))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_3 : ¬ attainable 6 n2_3 := by
  exact stepCover [n3_13, n3_14, n3_15] (by decide +kernel) (rejectCons r3_n3_13 (rejectCons r3_n3_14 (rejectCons r3_n3_15 (rejectNil 5))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_4 : ¬ attainable 6 n2_4 := by
  exact stepCover [n3_8, n3_11, n3_12] (by decide +kernel) (rejectCons r3_n3_8 (rejectCons r3_n3_11 (rejectCons r3_n3_12 (rejectNil 5))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_5 : ¬ attainable 6 n2_5 := by
  exact stepCover [n3_13] (by decide +kernel) (rejectCons r3_n3_13 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_6 : ¬ attainable 6 n2_6 := by
  exact stepCover [n3_14] (by decide +kernel) (rejectCons r3_n3_14 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_7 : ¬ attainable 6 n2_7 := by
  exact stepCover [n3_15] (by decide +kernel) (rejectCons r3_n3_15 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_8 : ¬ attainable 6 n2_8 := by
  exact stepCover [n3_15] (by decide +kernel) (rejectCons r3_n3_15 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_9 : ¬ attainable 6 n2_9 := by
  exact stepCover [n3_21] (by decide +kernel) (rejectCons r3_n3_21 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_10 : ¬ attainable 6 n2_10 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_11 : ¬ attainable 6 n2_11 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_12 : ¬ attainable 6 n2_12 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_13 : ¬ attainable 6 n2_13 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_14 : ¬ attainable 6 n2_14 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_15 : ¬ attainable 6 n2_15 := by
  exact stepCover [n3_22] (by decide +kernel) (rejectCons r3_n3_22 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_16 : ¬ attainable 6 n2_16 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_17 : ¬ attainable 6 n2_17 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_18 : ¬ attainable 6 n2_18 := by
  exact stepCover [n3_16, n3_17, n3_22] (by decide +kernel) (rejectCons r3_n3_16 (rejectCons r3_n3_17 (rejectCons r3_n3_22 (rejectNil 5))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_19 : ¬ attainable 6 n2_19 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_20 : ¬ attainable 6 n2_20 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_21 : ¬ attainable 6 n2_21 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_22 : ¬ attainable 6 n2_22 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_23 : ¬ attainable 6 n2_23 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_24 : ¬ attainable 6 n2_24 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_25 : ¬ attainable 6 n2_25 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_26 : ¬ attainable 6 n2_26 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_27 : ¬ attainable 6 n2_27 := by
  exact stepCover [n3_6] (by decide +kernel) (rejectCons r3_n3_6 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_28 : ¬ attainable 6 n2_28 := by
  exact stepCover [n3_7] (by decide +kernel) (rejectCons r3_n3_7 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_29 : ¬ attainable 6 n2_29 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_30 : ¬ attainable 6 n2_30 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_31 : ¬ attainable 6 n2_31 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_32 : ¬ attainable 6 n2_32 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_33 : ¬ attainable 6 n2_33 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_34 : ¬ attainable 6 n2_34 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_35 : ¬ attainable 6 n2_35 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_36 : ¬ attainable 6 n2_36 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_37 : ¬ attainable 6 n2_37 := by
  exact stepCover [n3_8] (by decide +kernel) (rejectCons r3_n3_8 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_38 : ¬ attainable 6 n2_38 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_39 : ¬ attainable 6 n2_39 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_40 : ¬ attainable 6 n2_40 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_41 : ¬ attainable 6 n2_41 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_42 : ¬ attainable 6 n2_42 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_43 : ¬ attainable 6 n2_43 := by
  exact stepCover [n3_16] (by decide +kernel) (rejectCons r3_n3_16 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_44 : ¬ attainable 6 n2_44 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_45 : ¬ attainable 6 n2_45 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_46 : ¬ attainable 6 n2_46 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_47 : ¬ attainable 6 n2_47 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_48 : ¬ attainable 6 n2_48 := by
  exact stepCover [n3_4] (by decide +kernel) (rejectCons r3_n3_4 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_49 : ¬ attainable 6 n2_49 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_50 : ¬ attainable 6 n2_50 := by
  exact stepCover [n3_6] (by decide +kernel) (rejectCons r3_n3_6 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_51 : ¬ attainable 6 n2_51 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_52 : ¬ attainable 6 n2_52 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_53 : ¬ attainable 6 n2_53 := by
  exact stepCover [n3_5] (by decide +kernel) (rejectCons r3_n3_5 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_54 : ¬ attainable 6 n2_54 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_55 : ¬ attainable 6 n2_55 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_56 : ¬ attainable 6 n2_56 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_57 : ¬ attainable 6 n2_57 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_58 : ¬ attainable 6 n2_58 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_59 : ¬ attainable 6 n2_59 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_60 : ¬ attainable 6 n2_60 := by
  exact stepCover [n3_17] (by decide +kernel) (rejectCons r3_n3_17 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_61 : ¬ attainable 6 n2_61 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_62 : ¬ attainable 6 n2_62 := by
  exact stepCover [n3_18] (by decide +kernel) (rejectCons r3_n3_18 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_63 : ¬ attainable 6 n2_63 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_64 : ¬ attainable 6 n2_64 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_65 : ¬ attainable 6 n2_65 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_66 : ¬ attainable 6 n2_66 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_67 : ¬ attainable 6 n2_67 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_68 : ¬ attainable 6 n2_68 := by
  exact stepCover [n3_10] (by decide +kernel) (rejectCons r3_n3_10 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_69 : ¬ attainable 6 n2_69 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_70 : ¬ attainable 6 n2_70 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_71 : ¬ attainable 6 n2_71 := by
  exact stepCover [n3_9] (by decide +kernel) (rejectCons r3_n3_9 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_72 : ¬ attainable 6 n2_72 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_73 : ¬ attainable 6 n2_73 := by
  exact stepCover [n3_11] (by decide +kernel) (rejectCons r3_n3_11 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_74 : ¬ attainable 6 n2_74 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_75 : ¬ attainable 6 n2_75 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_76 : ¬ attainable 6 n2_76 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_77 : ¬ attainable 6 n2_77 := by
  exact stepCover [n3_12] (by decide +kernel) (rejectCons r3_n3_12 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_78 : ¬ attainable 6 n2_78 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_79 : ¬ attainable 6 n2_79 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_80 : ¬ attainable 6 n2_80 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_81 : ¬ attainable 6 n2_81 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_82 : ¬ attainable 6 n2_82 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_83 : ¬ attainable 6 n2_83 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_84 : ¬ attainable 6 n2_84 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_85 : ¬ attainable 6 n2_85 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_86 : ¬ attainable 6 n2_86 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_87 : ¬ attainable 6 n2_87 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_88 : ¬ attainable 6 n2_88 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_89 : ¬ attainable 6 n2_89 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_90 : ¬ attainable 6 n2_90 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_91 : ¬ attainable 6 n2_91 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_92 : ¬ attainable 6 n2_92 := by
  exact stepCover [n3_0] (by decide +kernel) (rejectCons r3_n3_0 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_93 : ¬ attainable 6 n2_93 := by
  exact stepCover [n3_18] (by decide +kernel) (rejectCons r3_n3_18 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_94 : ¬ attainable 6 n2_94 := by
  exact stepCover [n3_1] (by decide +kernel) (rejectCons r3_n3_1 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_95 : ¬ attainable 6 n2_95 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_96 : ¬ attainable 6 n2_96 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_97 : ¬ attainable 6 n2_97 := by
  exact stepCover [n3_2] (by decide +kernel) (rejectCons r3_n3_2 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_98 : ¬ attainable 6 n2_98 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_99 : ¬ attainable 6 n2_99 := by
  exact stepCover [n3_18] (by decide +kernel) (rejectCons r3_n3_18 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_100 : ¬ attainable 6 n2_100 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_101 : ¬ attainable 6 n2_101 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_102 : ¬ attainable 6 n2_102 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_103 : ¬ attainable 6 n2_103 := by
  exact stepCover [n3_20] (by decide +kernel) (rejectCons r3_n3_20 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_104 : ¬ attainable 6 n2_104 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_105 : ¬ attainable 6 n2_105 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_106 : ¬ attainable 6 n2_106 := by
  exact stepCover [n3_19] (by decide +kernel) (rejectCons r3_n3_19 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_107 : ¬ attainable 6 n2_107 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_108 : ¬ attainable 6 n2_108 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_109 : ¬ attainable 6 n2_109 := by
  exact stepCover [n3_3] (by decide +kernel) (rejectCons r3_n3_3 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_110 : ¬ attainable 6 n2_110 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_111 : ¬ attainable 6 n2_111 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_0 : ¬ attainable 7 n1_0 := by
  exact stepCover [n2_3, n2_5, n2_6, n2_7, n2_8, n2_87, n2_98] (by decide +kernel) (rejectCons r2_n2_3 (rejectCons r2_n2_5 (rejectCons r2_n2_6 (rejectCons r2_n2_7 (rejectCons r2_n2_8 (rejectCons r2_n2_87 (rejectCons r2_n2_98 (rejectNil 6))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_1 : ¬ attainable 7 n1_1 := by
  exact stepCover [n2_2, n2_27, n2_50, n2_56, n2_68, n2_84, n2_103] (by decide +kernel) (rejectCons r2_n2_2 (rejectCons r2_n2_27 (rejectCons r2_n2_50 (rejectCons r2_n2_56 (rejectCons r2_n2_68 (rejectCons r2_n2_84 (rejectCons r2_n2_103 (rejectNil 6))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_2 : ¬ attainable 7 n1_2 := by
  exact stepCover [n2_32, n2_33, n2_47, n2_51, n2_69, n2_88, n2_91, n2_104] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_33 (rejectCons r2_n2_47 (rejectCons r2_n2_51 (rejectCons r2_n2_69 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectCons r2_n2_104 (rejectNil 6)))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_3 : ¬ attainable 7 n1_3 := by
  exact stepCover [n2_5, n2_28, n2_33, n2_48, n2_52, n2_70, n2_92, n2_105] (by decide +kernel) (rejectCons r2_n2_5 (rejectCons r2_n2_28 (rejectCons r2_n2_33 (rejectCons r2_n2_48 (rejectCons r2_n2_52 (rejectCons r2_n2_70 (rejectCons r2_n2_92 (rejectCons r2_n2_105 (rejectNil 6)))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_4 : ¬ attainable 7 n1_4 := by
  exact stepCover [n2_1, n2_4, n2_30, n2_47, n2_48, n2_53, n2_58, n2_61, n2_62, n2_71, n2_93, n2_106] (by decide +kernel) (rejectCons r2_n2_1 (rejectCons r2_n2_4 (rejectCons r2_n2_30 (rejectCons r2_n2_47 (rejectCons r2_n2_48 (rejectCons r2_n2_53 (rejectCons r2_n2_58 (rejectCons r2_n2_61 (rejectCons r2_n2_62 (rejectCons r2_n2_71 (rejectCons r2_n2_93 (rejectCons r2_n2_106 (rejectNil 6)))))))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_5 : ¬ attainable 7 n1_5 := by
  exact stepCover [n2_6, n2_50, n2_51, n2_52, n2_53, n2_72, n2_89, n2_94, n2_107] (by decide +kernel) (rejectCons r2_n2_6 (rejectCons r2_n2_50 (rejectCons r2_n2_51 (rejectCons r2_n2_52 (rejectCons r2_n2_53 (rejectCons r2_n2_72 (rejectCons r2_n2_89 (rejectCons r2_n2_94 (rejectCons r2_n2_107 (rejectNil 6))))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_6 : ¬ attainable 7 n1_6 := by
  exact stepCover [n2_7, n2_68, n2_69, n2_70, n2_71, n2_72, n2_96, n2_97, n2_108] (by decide +kernel) (rejectCons r2_n2_7 (rejectCons r2_n2_68 (rejectCons r2_n2_69 (rejectCons r2_n2_70 (rejectCons r2_n2_71 (rejectCons r2_n2_72 (rejectCons r2_n2_96 (rejectCons r2_n2_97 (rejectCons r2_n2_108 (rejectNil 6))))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_7 : ¬ attainable 7 n1_7 := by
  exact stepCover [n2_80, n2_82, n2_88, n2_89, n2_95, n2_96, n2_102, n2_110, n2_111] (by decide +kernel) (rejectCons r2_n2_80 (rejectCons r2_n2_82 (rejectCons r2_n2_88 (rejectCons r2_n2_89 (rejectCons r2_n2_95 (rejectCons r2_n2_96 (rejectCons r2_n2_102 (rejectCons r2_n2_110 (rejectCons r2_n2_111 (rejectNil 6))))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_8 : ¬ attainable 7 n1_8 := by
  exact stepCover [n2_0, n2_11, n2_18, n2_91, n2_92, n2_93, n2_94, n2_97, n2_99, n2_100, n2_101, n2_109] (by decide +kernel) (rejectCons r2_n2_0 (rejectCons r2_n2_11 (rejectCons r2_n2_18 (rejectCons r2_n2_91 (rejectCons r2_n2_92 (rejectCons r2_n2_93 (rejectCons r2_n2_94 (rejectCons r2_n2_97 (rejectCons r2_n2_99 (rejectCons r2_n2_100 (rejectCons r2_n2_101 (rejectCons r2_n2_109 (rejectNil 6)))))))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_9 : ¬ attainable 7 n1_9 := by
  exact stepCover [n2_9, n2_103, n2_104, n2_105, n2_106, n2_107, n2_108, n2_109] (by decide +kernel) (rejectCons r2_n2_9 (rejectCons r2_n2_103 (rejectCons r2_n2_104 (rejectCons r2_n2_105 (rejectCons r2_n2_106 (rejectCons r2_n2_107 (rejectCons r2_n2_108 (rejectCons r2_n2_109 (rejectNil 6)))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_10 : ¬ attainable 7 n1_10 := by
  exact stepCover [n2_32, n2_34, n2_39, n2_47, n2_54, n2_63, n2_76, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_34 (rejectCons r2_n2_39 (rejectCons r2_n2_47 (rejectCons r2_n2_54 (rejectCons r2_n2_63 (rejectCons r2_n2_76 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6))))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_11 : ¬ attainable 7 n1_11 := by
  exact stepCover [n2_4, n2_13, n2_32, n2_37, n2_40, n2_47, n2_73, n2_77, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_4 (rejectCons r2_n2_13 (rejectCons r2_n2_32 (rejectCons r2_n2_37 (rejectCons r2_n2_40 (rejectCons r2_n2_47 (rejectCons r2_n2_73 (rejectCons r2_n2_77 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6)))))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_12 : ¬ attainable 7 n1_12 := by
  exact stepCover [n2_32, n2_35, n2_42, n2_47, n2_55, n2_64, n2_74, n2_87, n2_88, n2_91, n2_98] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_35 (rejectCons r2_n2_42 (rejectCons r2_n2_47 (rejectCons r2_n2_55 (rejectCons r2_n2_64 (rejectCons r2_n2_74 (rejectCons r2_n2_87 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectCons r2_n2_98 (rejectNil 6))))))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_13 : ¬ attainable 7 n1_13 := by
  exact stepCover [n2_87, n2_98] (by decide +kernel) (rejectCons r2_n2_87 (rejectCons r2_n2_98 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_14 : ¬ attainable 7 n1_14 := by
  exact stepCover [n2_32, n2_47, n2_57, n2_78, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_57 (rejectCons r2_n2_78 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_15 : ¬ attainable 7 n1_15 := by
  exact stepCover [n2_32, n2_47, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_16 : ¬ attainable 7 n1_16 := by
  exact stepCover [n2_32, n2_44, n2_47, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_44 (rejectCons r2_n2_47 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_17 : ¬ attainable 7 n1_17 := by
  exact stepCover [n2_32, n2_45, n2_47, n2_75, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_45 (rejectCons r2_n2_47 (rejectCons r2_n2_75 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_18 : ¬ attainable 7 n1_18 := by
  exact stepCover [n2_32, n2_46, n2_47, n2_79, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_46 (rejectCons r2_n2_47 (rejectCons r2_n2_79 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_19 : ¬ attainable 7 n1_19 := by
  exact stepCover [n2_32, n2_47, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_20 : ¬ attainable 7 n1_20 := by
  exact stepCover [n2_32, n2_38, n2_47, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_38 (rejectCons r2_n2_47 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_21 : ¬ attainable 7 n1_21 := by
  exact stepCover [n2_32, n2_47, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_22 : ¬ attainable 7 n1_22 := by
  exact stepCover [n2_32, n2_47, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_23 : ¬ attainable 7 n1_23 := by
  exact stepCover [n2_32, n2_110] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_110 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_24 : ¬ attainable 7 n1_24 := by
  exact stepCover [n2_32, n2_47, n2_65, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_65 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_25 : ¬ attainable 7 n1_25 := by
  exact stepCover [n2_15, n2_18, n2_32, n2_36, n2_43, n2_47, n2_60, n2_81, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_15 (rejectCons r2_n2_18 (rejectCons r2_n2_32 (rejectCons r2_n2_36 (rejectCons r2_n2_43 (rejectCons r2_n2_47 (rejectCons r2_n2_60 (rejectCons r2_n2_81 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6)))))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_26 : ¬ attainable 7 n1_26 := by
  exact stepCover [n2_32, n2_47, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_27 : ¬ attainable 7 n1_27 := by
  exact stepCover [n2_14, n2_32, n2_47, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_14 (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_28 : ¬ attainable 7 n1_28 := by
  exact stepCover [n2_32, n2_80] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_80 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_29 : ¬ attainable 7 n1_29 := by
  exact stepCover [n2_32, n2_47, n2_88, n2_90, n2_91] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_88 (rejectCons r2_n2_90 (rejectCons r2_n2_91 (rejectNil 6))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_30 : ¬ attainable 7 n1_30 := by
  exact stepCover [n2_32, n2_47, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_31 : ¬ attainable 7 n1_31 := by
  exact stepCover [n2_16, n2_22, n2_32, n2_41, n2_47, n2_66, n2_83, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_16 (rejectCons r2_n2_22 (rejectCons r2_n2_32 (rejectCons r2_n2_41 (rejectCons r2_n2_47 (rejectCons r2_n2_66 (rejectCons r2_n2_83 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6))))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_32 : ¬ attainable 7 n1_32 := by
  exact stepCover [n2_32, n2_47, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_33 : ¬ attainable 7 n1_33 := by
  exact stepCover [n2_19, n2_20, n2_32, n2_47, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_19 (rejectCons r2_n2_20 (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_34 : ¬ attainable 7 n1_34 := by
  exact stepCover [n2_32, n2_47, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_35 : ¬ attainable 7 n1_35 := by
  exact stepCover [n2_21, n2_32, n2_47, n2_82, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_21 (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_82 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_36 : ¬ attainable 7 n1_36 := by
  exact stepCover [n2_32, n2_82] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_82 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_37 : ¬ attainable 7 n1_37 := by
  exact stepCover [n2_32, n2_47, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_38 : ¬ attainable 7 n1_38 := by
  exact stepCover [n2_56, n2_84] (by decide +kernel) (rejectCons r2_n2_56 (rejectCons r2_n2_84 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_39 : ¬ attainable 7 n1_39 := by
  exact stepCover [n2_17, n2_23, n2_32, n2_47, n2_56, n2_59, n2_67, n2_84, n2_85, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_17 (rejectCons r2_n2_23 (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_56 (rejectCons r2_n2_59 (rejectCons r2_n2_67 (rejectCons r2_n2_84 (rejectCons r2_n2_85 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6))))))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_40 : ¬ attainable 7 n1_40 := by
  exact stepCover [n2_6, n2_32, n2_47, n2_50, n2_51, n2_53, n2_88, n2_89, n2_91, n2_94] (by decide +kernel) (rejectCons r2_n2_6 (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_50 (rejectCons r2_n2_51 (rejectCons r2_n2_53 (rejectCons r2_n2_88 (rejectCons r2_n2_89 (rejectCons r2_n2_91 (rejectCons r2_n2_94 (rejectNil 6)))))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_41 : ¬ attainable 7 n1_41 := by
  exact stepCover [n2_32, n2_47, n2_58, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_58 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_42 : ¬ attainable 7 n1_42 := by
  exact stepCover [n2_32, n2_47, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n2_32 : ¬ attainable 7 n2_32 := by
  exact stepCover [n2_32, n2_47, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_44 : ¬ attainable 7 n1_44 := by
  exact stepCover [n2_5, n2_27, n2_28, n2_32, n2_33, n2_47, n2_48, n2_88, n2_91, n2_92] (by decide +kernel) (rejectCons r2_n2_5 (rejectCons r2_n2_27 (rejectCons r2_n2_28 (rejectCons r2_n2_32 (rejectCons r2_n2_33 (rejectCons r2_n2_47 (rejectCons r2_n2_48 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectCons r2_n2_92 (rejectNil 6)))))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_45 : ¬ attainable 7 n1_45 := by
  exact stepCover [n2_32, n2_47, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_46 : ¬ attainable 7 n1_46 := by
  exact stepCover [n2_32, n2_47, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_47 : ¬ attainable 7 n1_47 := by
  exact stepCover [n2_27, n2_32, n2_47, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_27 (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_48 : ¬ attainable 7 n1_48 := by
  exact stepCover [n2_26, n2_31, n2_32, n2_47, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_26 (rejectCons r2_n2_31 (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_49 : ¬ attainable 7 n1_49 := by
  exact stepCover [n2_32, n2_47, n2_61, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_61 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_50 : ¬ attainable 7 n1_50 := by
  exact stepCover [n2_32, n2_47, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_51 : ¬ attainable 7 n1_51 := by
  exact stepCover [n2_25, n2_32, n2_47, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_25 (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_52 : ¬ attainable 7 n1_52 := by
  exact stepCover [n2_32, n2_47, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n2_33 : ¬ attainable 7 n2_33 := by
  exact stepCover [n2_5, n2_28, n2_33, n2_48, n2_92] (by decide +kernel) (rejectCons r2_n2_5 (rejectCons r2_n2_28 (rejectCons r2_n2_33 (rejectCons r2_n2_48 (rejectCons r2_n2_92 (rejectNil 6))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_54 : ¬ attainable 7 n1_54 := by
  exact stepCover [n2_4, n2_29, n2_30, n2_32, n2_47, n2_58, n2_61, n2_62, n2_88, n2_91, n2_93] (by decide +kernel) (rejectCons r2_n2_4 (rejectCons r2_n2_29 (rejectCons r2_n2_30 (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_58 (rejectCons r2_n2_61 (rejectCons r2_n2_62 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectCons r2_n2_93 (rejectNil 6))))))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_55 : ¬ attainable 7 n1_55 := by
  exact stepCover [n2_32, n2_47, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_56 : ¬ attainable 7 n1_56 := by
  exact stepCover [n2_32, n2_47, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_57 : ¬ attainable 7 n1_57 := by
  exact stepCover [n2_32, n2_47, n2_80, n2_82, n2_88, n2_91, n2_95, n2_102, n2_110, n2_111] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_80 (rejectCons r2_n2_82 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectCons r2_n2_95 (rejectCons r2_n2_102 (rejectCons r2_n2_110 (rejectCons r2_n2_111 (rejectNil 6)))))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_58 : ¬ attainable 7 n1_58 := by
  exact stepCover [n2_8, n2_32, n2_47, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_8 (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_59 : ¬ attainable 7 n1_59 := by
  exact stepCover [n2_12, n2_32, n2_47, n2_80, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_12 (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_80 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_60 : ¬ attainable 7 n1_60 := by
  exact stepCover [n2_24, n2_32, n2_47, n2_62, n2_88, n2_91, n2_99] (by decide +kernel) (rejectCons r2_n2_24 (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_62 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectCons r2_n2_99 (rejectNil 6))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_61 : ¬ attainable 7 n1_61 := by
  exact stepCover [n2_32, n2_47, n2_88, n2_91, n2_100] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectCons r2_n2_100 (rejectNil 6))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_62 : ¬ attainable 7 n1_62 := by
  exact stepCover [n2_32, n2_47, n2_86, n2_88, n2_91, n2_110] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_86 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectCons r2_n2_110 (rejectNil 6)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_63 : ¬ attainable 7 n1_63 := by
  exact stepCover [n2_32, n2_47, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n2_47 : ¬ attainable 7 n2_47 := by
  exact stepCover [n2_4, n2_30, n2_47, n2_58, n2_61, n2_62, n2_93] (by decide +kernel) (rejectCons r2_n2_4 (rejectCons r2_n2_30 (rejectCons r2_n2_47 (rejectCons r2_n2_58 (rejectCons r2_n2_61 (rejectCons r2_n2_62 (rejectCons r2_n2_93 (rejectNil 6))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_65 : ¬ attainable 7 n1_65 := by
  exact stepCover [n2_80, n2_82, n2_88, n2_95, n2_102, n2_110, n2_111] (by decide +kernel) (rejectCons r2_n2_80 (rejectCons r2_n2_82 (rejectCons r2_n2_88 (rejectCons r2_n2_95 (rejectCons r2_n2_102 (rejectCons r2_n2_110 (rejectCons r2_n2_111 (rejectNil 6))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_66 : ¬ attainable 7 n1_66 := by
  exact stepCover [n2_32, n2_47, n2_88, n2_91, n2_95] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectCons r2_n2_95 (rejectNil 6))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n2_51 : ¬ attainable 7 n2_51 := by
  exact stepCover [n2_6, n2_50, n2_51, n2_53, n2_89, n2_94] (by decide +kernel) (rejectCons r2_n2_6 (rejectCons r2_n2_50 (rejectCons r2_n2_51 (rejectCons r2_n2_53 (rejectCons r2_n2_89 (rejectCons r2_n2_94 (rejectNil 6)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_68 : ¬ attainable 7 n1_68 := by
  exact stepCover [n2_7, n2_32, n2_47, n2_68, n2_69, n2_71, n2_88, n2_91, n2_96, n2_97] (by decide +kernel) (rejectCons r2_n2_7 (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_68 (rejectCons r2_n2_69 (rejectCons r2_n2_71 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectCons r2_n2_96 (rejectCons r2_n2_97 (rejectNil 6)))))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_69 : ¬ attainable 7 n1_69 := by
  exact stepCover [n2_10, n2_11, n2_18, n2_32, n2_47, n2_88, n2_91, n2_93, n2_99, n2_100, n2_101] (by decide +kernel) (rejectCons r2_n2_10 (rejectCons r2_n2_11 (rejectCons r2_n2_18 (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectCons r2_n2_93 (rejectCons r2_n2_99 (rejectCons r2_n2_100 (rejectCons r2_n2_101 (rejectNil 6))))))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_70 : ¬ attainable 7 n1_70 := by
  exact stepCover [n2_32, n2_47, n2_88, n2_91, n2_101] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectCons r2_n2_101 (rejectNil 6))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_71 : ¬ attainable 7 n1_71 := by
  exact stepCover [n2_32] (by decide +kernel) (rejectCons r2_n2_32 (rejectNil 6))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_72 : ¬ attainable 7 n1_72 := by
  exact stepCover [n2_32, n2_47, n2_88, n2_91] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectNil 6)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_73 : ¬ attainable 7 n1_73 := by
  exact stepCover [n2_32, n2_95] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_95 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n2_69 : ¬ attainable 7 n2_69 := by
  exact stepCover [n2_7, n2_68, n2_69, n2_71, n2_96, n2_97] (by decide +kernel) (rejectCons r2_n2_7 (rejectCons r2_n2_68 (rejectCons r2_n2_69 (rejectCons r2_n2_71 (rejectCons r2_n2_96 (rejectCons r2_n2_97 (rejectNil 6)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_75 : ¬ attainable 7 n1_75 := by
  exact stepCover [n2_8, n2_9, n2_32, n2_47, n2_88, n2_91, n2_103, n2_104, n2_106, n2_109] (by decide +kernel) (rejectCons r2_n2_8 (rejectCons r2_n2_9 (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectCons r2_n2_103 (rejectCons r2_n2_104 (rejectCons r2_n2_106 (rejectCons r2_n2_109 (rejectNil 6)))))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_76 : ¬ attainable 7 n1_76 := by
  exact stepCover [n2_80, n2_82, n2_88, n2_95, n2_102, n2_110, n2_111] (by decide +kernel) (rejectCons r2_n2_80 (rejectCons r2_n2_82 (rejectCons r2_n2_88 (rejectCons r2_n2_95 (rejectCons r2_n2_102 (rejectCons r2_n2_110 (rejectCons r2_n2_111 (rejectNil 6))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_77 : ¬ attainable 7 n1_77 := by
  exact stepCover [n2_32] (by decide +kernel) (rejectCons r2_n2_32 (rejectNil 6))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n2_91 : ¬ attainable 7 n2_91 := by
  exact stepCover [n2_11, n2_18, n2_91, n2_93, n2_99, n2_100, n2_101] (by decide +kernel) (rejectCons r2_n2_11 (rejectCons r2_n2_18 (rejectCons r2_n2_91 (rejectCons r2_n2_93 (rejectCons r2_n2_99 (rejectCons r2_n2_100 (rejectCons r2_n2_101 (rejectNil 6))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n2_104 : ¬ attainable 7 n2_104 := by
  exact stepCover [n2_9, n2_103, n2_104, n2_106, n2_109] (by decide +kernel) (rejectCons r2_n2_9 (rejectCons r2_n2_103 (rejectCons r2_n2_104 (rejectCons r2_n2_106 (rejectCons r2_n2_109 (rejectNil 6))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_80 : ¬ attainable 7 n1_80 := by
  exact stepCover [n2_32, n2_111] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_111 (rejectNil 6)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_81 : ¬ attainable 7 n1_81 := by
  exact stepCover [n2_32, n2_47, n2_49, n2_88, n2_91, n2_111] (by decide +kernel) (rejectCons r2_n2_32 (rejectCons r2_n2_47 (rejectCons r2_n2_49 (rejectCons r2_n2_88 (rejectCons r2_n2_91 (rejectCons r2_n2_111 (rejectNil 6)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r0_wires : ¬ attainable 8 wires := by
  exact stepCover [n1_0, n1_1, n1_2, n1_3, n1_4, n1_5, n1_6, n1_7, n1_8, n1_9, n1_10, n1_11, n1_12, n1_13, n1_14, n1_15, n1_16, n1_17, n1_18, n1_19, n1_20, n1_21, n1_22, n1_23, n1_24, n1_25, n1_26, n1_27, n1_28, n1_29, n1_30, n1_31, n1_32, n1_33, n1_34, n1_35, n1_36, n1_37, n1_38, n1_39, n1_40, n1_41, n1_42, n2_32, n1_44, n1_45, n1_46, n1_47, n1_48, n1_49, n1_50, n1_51, n1_52, n2_33, n1_54, n1_55, n1_56, n1_57, n1_58, n1_59, n1_60, n1_61, n1_62, n1_63, n2_47, n1_65, n1_66, n2_51, n1_68, n1_69, n1_70, n1_71, n1_72, n1_73, n2_69, n1_75, n1_76, n1_77, n2_91, n2_104, n1_80, n1_81] (by decide +kernel) (rejectCons r1_n1_0 (rejectCons r1_n1_1 (rejectCons r1_n1_2 (rejectCons r1_n1_3 (rejectCons r1_n1_4 (rejectCons r1_n1_5 (rejectCons r1_n1_6 (rejectCons r1_n1_7 (rejectCons r1_n1_8 (rejectCons r1_n1_9 (rejectCons r1_n1_10 (rejectCons r1_n1_11 (rejectCons r1_n1_12 (rejectCons r1_n1_13 (rejectCons r1_n1_14 (rejectCons r1_n1_15 (rejectCons r1_n1_16 (rejectCons r1_n1_17 (rejectCons r1_n1_18 (rejectCons r1_n1_19 (rejectCons r1_n1_20 (rejectCons r1_n1_21 (rejectCons r1_n1_22 (rejectCons r1_n1_23 (rejectCons r1_n1_24 (rejectCons r1_n1_25 (rejectCons r1_n1_26 (rejectCons r1_n1_27 (rejectCons r1_n1_28 (rejectCons r1_n1_29 (rejectCons r1_n1_30 (rejectCons r1_n1_31 (rejectCons r1_n1_32 (rejectCons r1_n1_33 (rejectCons r1_n1_34 (rejectCons r1_n1_35 (rejectCons r1_n1_36 (rejectCons r1_n1_37 (rejectCons r1_n1_38 (rejectCons r1_n1_39 (rejectCons r1_n1_40 (rejectCons r1_n1_41 (rejectCons r1_n1_42 (rejectCons r1_n2_32 (rejectCons r1_n1_44 (rejectCons r1_n1_45 (rejectCons r1_n1_46 (rejectCons r1_n1_47 (rejectCons r1_n1_48 (rejectCons r1_n1_49 (rejectCons r1_n1_50 (rejectCons r1_n1_51 (rejectCons r1_n1_52 (rejectCons r1_n2_33 (rejectCons r1_n1_54 (rejectCons r1_n1_55 (rejectCons r1_n1_56 (rejectCons r1_n1_57 (rejectCons r1_n1_58 (rejectCons r1_n1_59 (rejectCons r1_n1_60 (rejectCons r1_n1_61 (rejectCons r1_n1_62 (rejectCons r1_n1_63 (rejectCons r1_n2_47 (rejectCons r1_n1_65 (rejectCons r1_n1_66 (rejectCons r1_n2_51 (rejectCons r1_n1_68 (rejectCons r1_n1_69 (rejectCons r1_n1_70 (rejectCons r1_n1_71 (rejectCons r1_n1_72 (rejectCons r1_n1_73 (rejectCons r1_n2_69 (rejectCons r1_n1_75 (rejectCons r1_n1_76 (rejectCons r1_n1_77 (rejectCons r1_n2_91 (rejectCons r1_n2_104 (rejectCons r1_n1_80 (rejectCons r1_n1_81 (rejectNil 7)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Case34

theorem no34 (rest : List PEqualNP.CircuitLowerBounds.Gate) (o : Nat) (hs : ∀ g ∈ rest, CircuitSatBridge.Supported g) (hlen : rest.length ≤ 8) (hr : ∀ x : Fin 128, (CircuitSatBridge.run rest (bank 3 4 x)).getD o false = target x) : False :=
  Case34.r0_wires (Case34.suffix rest o hs hlen hr)

namespace Mirror45
open FreeSupport CircuitSatBridge PEqualNP.CircuitLowerBounds
def wires : List Wire := [Case23.w0, Case23.w82, Case23.w37, Case23.w95, Case23.w29, Case23.w44, Case23.w57, Case23.w1, Case23.w69]
def test (t : Fin 110) (b : Bool) : Fin 128 :=
  let pts : List (Fin 128) := if b then [74, 74, 42, 74, 21, 82, 41, 37, 74, 84, 42, 41, 37, 41, 82, 82, 82, 21, 21, 21, 41, 74, 37, 41, 21, 37, 37, 41, 42, 42, 21, 84, 74, 82, 42, 84, 37, 84, 84, 37, 84, 82, 42, 41, 42, 21, 84, 82, 74, 37, 82, 82, 41, 1, 84, 84, 37, 2, 42, 74, 42, 21, 74, 1, 42, 41, 21, 74, 82, 2, 41, 21, 8, 84, 4, 74, 32, 16, 4, 37, 64, 8, 64, 10, 68, 66, 80, 68, 5, 34, 18, 34, 18, 68, 20, 17, 72, 9, 9, 17, 68, 33, 10, 18, 17, 36, 72, 66, 9, 10] else [96, 65, 3, 6, 65, 6, 96, 96, 12, 12, 96, 12, 3, 3, 3, 96, 65, 24, 48, 3, 24, 3, 12, 65, 12, 65, 48, 48, 12, 6, 6, 65, 24, 24, 24, 6, 6, 96, 24, 24, 48, 12, 65, 6, 48, 96, 3, 48, 48, 45, 83, 86, 105, 3, 86, 92, 101, 3, 43, 106, 106, 23, 78, 65, 46, 45, 29, 90, 90, 6, 43, 85, 12, 85, 6, 75, 96, 24, 12, 39, 65, 24, 96, 26, 76, 98, 88, 70, 69, 35, 19, 38, 22, 69, 22, 19, 88, 13, 25, 81, 100, 35, 11, 26, 25, 44, 104, 67, 11, 14]
  pts.getD t.val 0
set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem samples : ∀ t : Fin 110, ∀ b : Bool,
    sample wires t b = bank 4 5 (test t b) ∧ target (test t b) = !b := by decide +kernel

theorem suffix (rest : List Gate) (o : Nat) (hs : ∀ g ∈ rest, Supported g) (hlen : rest.length ≤ 8)
    (hr : ∀ x : Fin 128, (run rest (bank 4 5 x)).getD o false = target x) :
    attainable 8 wires := by
  obtain ⟨cs,hl,hv,he⟩ := fixed_slots 7 9 o rest hs hlen
  refine ⟨cs,16,hl,hv,?_⟩
  intro t
  have h (b : Bool) : (runChoices cs (sample wires t b)).getD 16 false = !b := by
    rw [(samples t b).1, he]
    · exact (hr _).trans (samples t b).2
    · simp [bank]
  exact ⟨h false, h true⟩

theorem project (k : Nat) (hs : attainable k wires) : attainable k Case23.wires := by
  have hm : wires.all (fun w => Case23.wires.contains w) = true := by decide +kernel
  obtain ⟨cs, o, rfl, _, orient⟩ := hs
  obtain ⟨support, sub, _, det⟩ := bounded_support cs wires.length o
  apply project_suffix sub orient det
  intro i hi
  exact Or.inl (List.contains_iff_mem.mp ((List.all_eq_true.mp hm) _ (List.getElem_mem _)))

end Mirror45

theorem no45 (rest : List PEqualNP.CircuitLowerBounds.Gate) (o : Nat) (hs : ∀ g ∈ rest, CircuitSatBridge.Supported g) (hlen : rest.length ≤ 8) (hr : ∀ x : Fin 128, (CircuitSatBridge.run rest (bank 4 5 x)).getD o false = target x) : False :=
  Case23.r0_wires (Mirror45.project 8 (Mirror45.suffix rest o hs hlen hr))
open PEqualNP.CircuitLowerBounds CircuitSatBridge

def bitfn (x : Fin 128) (j : Fin 7) : Bool := x.val.testBit j.val

def otherInputs (x : Fin 128) : List Bool :=
  [x.val.testBit 1,x.val.testBit 2,x.val.testBit 3,x.val.testBit 4,x.val.testBit 5,x.val.testBit 6]

def andfn (a b : Nat) (x : Fin 128) : Bool := x.val.testBit a && x.val.testBit b

theorem ofFn_bits : ∀ x : Fin 128, List.ofFn (bitfn x) = x.val.testBit 0 :: otherInputs x := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem bits_cover : ∀ f : Fin 7 → Bool, ∃ x : Fin 128, f = bitfn x := by decide +kernel

def gval (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun j => w.getD j false)

theorem skipZero (g : Gate) (t : List Bool) (b : Bool) (hz : 0 ∉ g.inputs) :
    gval g (b :: t) = gval g (false :: t) := by
  unfold gval
  congr 1
  apply List.map_congr_left
  intro v hv
  cases v with
  | zero => exact False.elim (hz hv)
  | succ j => rfl

theorem maskRun (gs : List Gate) (hn : ∀ g ∈ gs, 0 ∉ g.inputs)
    (t : List Bool) (b : Bool) (o : Nat) (ho : o ≠ 0) :
    (run gs (b :: t)).getD o false = (run gs (false :: t)).getD o false := by
  induction gs generalizing t with
  | nil => cases o <;> simp_all [run]
  | cons g gs ih =>
    change (run gs (b :: (t ++ [gval g (b :: t)]))).getD o false =
      (run gs (false :: (t ++ [gval g (false :: t)]))).getD o false
    rw [skipZero g t b (hn g (by simp))]
    exact ih (fun a ha => hn a (by simp [ha])) _

theorem keepWire (gs : List Gate) (w : List Bool) (o : Nat) (ho : o < w.length) :
    (run gs w).getD o false = w.getD o false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (w ++ [gval g w])).getD _ _ = _
    rw [ih _ (by simp; omega),List.getD_append _ _ _ _ ho]

namespace MoveOr
open PEqualNP.CircuitLowerBounds CircuitSatBridge

def value (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)

def agrees (f : Nat → Nat) (w v : List Bool) : Prop :=
  ∀ i, i < w.length → i ≠ 0 → f i < v.length ∧ v.getD (f i) false = w.getD i false

def ext (n m : Nat) (f : Nat → Nat) (i : Nat) := if i = n then m else f i

def move (n m : Nat) (f : Nat → Nat) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map fun i => if i < n then f i else m⟩

theorem move_value {w v : List Bool} {f : Nat → Nat} {g : Gate}
    (h : agrees f w v) (nz : 0 ∉ g.inputs) :
    value (move w.length v.length f g) v = value g w := by
  unfold value move
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro i hi
  by_cases hit : i < w.length
  · have ne : i ≠ 0 := fun e => nz (e ▸ hi)
    simpa [Function.comp_def,hit] using (h i hit ne).2
  · simp [Function.comp_def,hit,List.getD_eq_default _ _ (Nat.le_of_not_lt hit),List.getD_eq_default _ _ (Nat.le_refl _)]

theorem after {w v : List Bool} {f : Nat → Nat} (h : agrees f w v) (b : Bool) :
    agrees (ext w.length v.length f) (w ++ [b]) (v ++ [b]) := by
  intro i hi nz
  by_cases old : i < w.length
  · obtain ⟨lt,e⟩ := h i old nz
    simp only [ext,if_neg (Nat.ne_of_lt old),List.getD_append _ _ _ _ old,
      List.getD_append _ _ _ _ lt,List.length_append,List.length_singleton]
    exact ⟨by omega,e⟩
  · have eq : i = w.length := by simp at hi; omega
    subst i
    simp [ext,List.getD_append_right]

theorem skipped {w v : List Bool} {f : Nat → Nat} (h : agrees f w v) (j : Nat) (hj : j < v.length) :
    agrees (ext w.length j f) (w ++ [v.getD j false]) v := by
  intro i hi nz
  by_cases old : i < w.length
  · rw [List.getD_append _ _ _ _ old]
    simpa only [ext,if_neg (Nat.ne_of_lt old)] using h i old nz
  · have eq : i = w.length := by simp at hi; omega
    subst i
    simp [ext,List.getD_append_right,hj]

def transform (gs : List Gate) (n m : Nat) (f : Nat → Nat) : List Gate × (Nat → Nat) :=
  match gs with
  | [] => ([],f)
  | g :: rest =>
    let tail := transform rest (n+1) (m+1) (ext n m f)
    (move n m f g :: tail.1, tail.2)

theorem transform_length (gs : List Gate) (n m : Nat) (f : Nat → Nat) :
    (transform gs n m f).1.length = gs.length := by
  induction gs generalizing n m f with
  | nil => rfl
  | cons g gs ih => simp [transform,ih]

theorem transform_supported (gs : List Gate) (n m : Nat) (f : Nat → Nat)
    (hs : ∀ g ∈ gs, Supported g) : ∀ g ∈ (transform gs n m f).1, Supported g := by
  induction gs generalizing n m f with
  | nil => simp [transform]
  | cons g gs ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | hmem
    · simpa [move,Supported] using hs g (by simp)
    · exact ih _ _ _ (fun h hh => hs h (by simp [hh])) _ hmem

theorem transform_values (gs : List Gate) (w v : List Bool) (f : Nat → Nat)
    (h : agrees f w v) (nz : ∀ g ∈ gs, 0 ∉ g.inputs) :
    agrees (transform gs w.length v.length f).2 (run gs w)
      (run (transform gs w.length v.length f).1 v) := by
  induction gs generalizing w v f with
  | nil => exact h
  | cons g gs ih =>
    have hg := move_value h (nz g (by simp))
    change agrees _ (run gs (w ++ [value g w])) (run _ (v ++ [value (move _ _ _ g) v]))
    rw [hg]
    have e := ih (w ++ [value g w]) (v ++ [value g w]) (ext w.length v.length f)
      (after h _) (fun h hh => nz h (by simp [hh]))
    simpa [transform] using e

theorem run_len (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (w ++ [value g w])).length = _
    rw [ih]
    simp; omega

theorem run_cat (gs hs : List Gate) (w : List Bool) : run (gs ++ hs) w = run hs (run gs w) := by
  simp [run,List.foldl_append]

theorem initial (b q : Bool) (xs : List Bool) : agrees id (b :: xs) (false :: (xs ++ [q])) := by
  intro i hi nz
  cases i with
  | zero => contradiction
  | succ j =>
    have hj : j < xs.length := by simpa using hi
    constructor
    · simp;omega
    · simpa using List.getD_append xs [q] false j hj

def pick (n m : Nat) (f : Nat → Nat) (i : Nat) := if i < n then f i else m

theorem pick_ok {w v : List Bool} {f : Nat → Nat} (h : agrees f w v) (o : Nat) (nz : o ≠ 0) :
    v.getD (pick w.length v.length f o) false = w.getD o false := by
  by_cases valid : o < w.length
  · simpa [pick,valid] using (h o valid nz).2
  · simp [pick,valid,List.getD_eq_default _ _ (Nat.le_of_not_lt valid),List.getD_eq_default _ _ (Nat.le_refl _)]

theorem const_wire (gs : List Gate) (w : List Bool) (o : Nat) (ho : o < w.length) :
    (run gs w).getD o false = w.getD o false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (w ++ [value g w])).getD _ _ = _
    rw [ih _ (by simp; omega),List.getD_append _ _ _ _ ho]

end MoveOr
end PEqualNP.Outside.L_meta_29892_aux
namespace PEqualNP.Outside.L_meta_29892_aux
namespace MoveOr
open PEqualNP.CircuitLowerBounds CircuitSatBridge
theorem accelerateEight (pre post : List Gate) (o : Nat) (hn : o ≠ 0)
    (npre : ∀ g ∈ pre, 0 ∉ g.inputs) (npost : ∀ g ∈ post, 0 ∉ g.inputs)
    (spre : ∀ g ∈ pre, Supported g) (spost : ∀ g ∈ post, Supported g) :
    ∃ (rest : List Gate) (out : Nat), rest.length = pre.length + post.length ∧
      (∀ g ∈ rest, Supported g) ∧ ∀ (x0 q : Bool) (xs : List Bool), xs.length = 8 →
      (run rest (false :: (xs ++ [q]))).getD out false =
      (run post ((run pre (x0 :: xs)) ++ [q])).getD o false := by
  let P := transform pre 9 10 id
  let f := ext (9+pre.length) 9 P.2
  let S := transform post (9+pre.length+1) (10+pre.length) f
  let size := 10 + pre.length + post.length
  refine ⟨P.1 ++ S.1, pick size size S.2 o, ?_, ?_, ?_⟩
  · simp [P,S,transform_length]
  · intro g hg
    rcases List.mem_append.mp hg with h|h
    · exact transform_supported _ _ _ _ spre g h
    · exact transform_supported _ _ _ _ spost g h
  intro x0 q xs hlen
  let w := run pre (x0 :: xs)
  let v := run P.1 (false :: (xs ++ [q]))
  have lw : w.length = 9 + pre.length := by simp [w,run_len,hlen]
  have lv : v.length = 10 + pre.length := by simp [v,run_len,hlen,P,transform_length]
  have r : agrees P.2 w v := by
    have z := transform_values pre _ _ _ (initial x0 q xs) npre
    simpa [P,w,v,hlen] using z
  have oldQ : (false :: (xs ++ [q])).getD 9 false = q := by
    change (xs ++ [q]).getD 8 false = q
    rw [List.getD_append_right _ _ _ _ (by omega), hlen]
    rfl
  have vq : v.getD 9 false = q := by
    exact (const_wire _ _ _ (by simp [hlen])).trans oldQ
  have s : agrees f (w ++ [q]) v := by
    have z := skipped r 9 (by omega)
    simpa only [f,lw,vq] using z
  have rr : agrees S.2 (run post (w ++ [q])) (run S.1 v) := by
    have z := transform_values post _ _ _ s npost
    simpa [S,lw,lv] using z
  have h := pick_ok rr o hn
  simpa [size,run_cat,run_len,lw,lv,S,P,transform_length,v,w,Nat.add_assoc,
    Nat.add_comm,Nat.add_left_comm] using h

end MoveOr
end PEqualNP.Outside.L_meta_29892_aux

namespace PEqualNP.Outside.L_meta_29892_aux.DepthBridge
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_29892_aux PEqualNP.Outside.L_meta_29892_aux.CircuitSatBridge
def initial : List Nat := [0, 0, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320]
def firstMasks : List Nat := [0, 4294967295, 281470681808895, 71777214294589695, 1085102592571150095, 3689348814741910323, 6148914691236517205, 9838263505978427528, 11574427654092267680, 12249977906276641280, 12297641735351828480, 12297829379609722880, 12297829382473034410, 13889313184910721216, 14699973487531969536, 14757170082422194176, 14757395255531667456, 14757395258967641292, 17216961135462248174, 17294086455919964160, 17361376567555522560, 17361641477096079360, 17361641481138401520, 18085043209519168250, 18229723555195321596, 18374686483949813760, 18374966855136706560, 18374966859414961920, 18422818335611355050, 18432388630850633676, 18442521884633399280, 18446462598732840960, 18446462603027742720, 18446650250148948650, 18446687779573189836, 18446727516610621680, 18446742978492890880, 18446744069414584320, 18446744072277895850, 18446744072850558156, 18446744073456906480, 18446744073692839680, 18446744073709486080, 18446744073709551615]
def simpleMasks : List Nat := [13889313184910721216, 14757170082422194176, 17294086455919964160, 18374686483949813760]
def specialMasks : List (Nat × Nat) := [(4294967295, 3435973836), (6148914691236517205, 6148820867675914240), (13889313184910721216, 13835269164735971328), (13889313184910721216, 13889101254044418048), (14699973487531969536, 13835269164735971328), (14699973487531969536, 14699749187159851008), (14757170082422194176, 13889101254044418048), (14757170082422194176, 14699749187159851008), (17294086455919964160, 13835269164735971328), (17294086455919964160, 17293822573129236480), (17361376567555522560, 13889101254044418048), (17361376567555522560, 17293822573129236480), (18085043209519168250, 14468034567615334600), (18374686483949813760, 14699749187159851008), (18374686483949813760, 17293822573129236480), (18432388630850633676, 17348130476094714048), (18432388630850633676, 18432107379212156928), (18446650250148948650, 14757320200119158920), (18446727516610621680, 14757382013288497344), (18446727516610621680, 18374950366740541440), (18446744072277895850, 1431655765), (18446744072850558156, 18446462602168762368), (18446744073692839680, 18446462603011031040)]
def sourceMask (f : Nat) (j : Nat) : Nat := if j = 8 then f else initial.getD j 0
def gateMask (op : Ordering) (p q : Nat) : Nat :=
  match op with
  | .lt => p &&& q
  | .eq => p ||| q
  | .gt => p ^^^ 18446744073709551615
def nextMask (f : Nat) (op : Ordering) (l r : Nat) := gateMask op (sourceMask f l) (sourceMask f r)
def allowed (f h : Nat) : Bool := (h &&& 1431655765 == 0) || (h &&& 7932806824482 != 0) || simpleMasks.contains h || specialMasks.contains (f,h)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 15000000 in
theorem computedFirst : ∀ (op : Ordering) (l r : Fin 8), nextMask 0 op l r ∈ firstMasks := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 15000000 in
theorem computedSecond : ∀ (i : Fin 44) (op : Ordering) (l r : Fin 9),
    allowed (firstMasks.getD i.val 0) (nextMask (firstMasks.getD i.val 0) op l r) = true := by decide +kernel
theorem evalZero (x : Fin 128) : Nat.testBit 18446744073709551615 (x.val/2) = true := by revert x; decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 15000000 in
theorem evalInput : ∀ (x : Fin 128) (j : Fin 8),
    (initial.getD j.val 0).testBit (x.val/2) = read (false :: otherInputs x) j.val := by decide +kernel
theorem evalGate (op : Ordering) (p q : Nat) (x : Fin 128) :
    (gateMask op p q).testBit (x.val/2) =
      (match op with
      | .lt => p.testBit (x.val/2) && q.testBit (x.val/2)
      | .eq => p.testBit (x.val/2) || q.testBit (x.val/2)
      | .gt => !p.testBit (x.val/2)) := by
  cases op <;> simp [gateMask,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,evalZero]
end PEqualNP.Outside.L_meta_29892_aux.DepthBridge

namespace PEqualNP.Outside.L_meta_29892_aux.DepthBridge
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_29892_aux PEqualNP.Outside.L_meta_29892_aux.CircuitSatBridge
def val (m : Nat) (x : Fin 128) : Bool := m.testBit (x.val/2)

theorem readBase (x : Fin 128) (j : Fin 8) :
    val (sourceMask 0 j.val) x = read (false :: otherInputs x) j.val := by
  simp only [val,sourceMask,ite_eq_right (by omega : j.val ≠ 8),evalInput]

theorem readExtra (x : Fin 128) (f : Nat) (j : Fin 9) :
    val (sourceMask f j.val) x = read ((false :: otherInputs x) ++ [val f x]) j.val := by
  by_cases eq : j.val = 8
  · rw [eq]; rfl
  · let k : Fin 8 := ⟨j.val,by omega⟩
    have h := evalInput x k
    change val (initial.getD j.val 0) x = read (false :: otherInputs x) j.val at h
    simp only [sourceMask,ite_eq_right eq]
    rw [h]
    cases e : j.val with
    | zero => rfl
    | succ i =>
      have lt : i < (false :: otherInputs x).length := by simp [otherInputs]; omega
      exact (List.getD_append _ _ _ _ lt).symm

theorem firstValue (x : Fin 128) (op : Ordering) (l r : Fin 8) :
    val (nextMask 0 op l r) x = (Choice.mk op l r).eval (false :: otherInputs x) := by
  unfold val nextMask
  rw [evalGate]
  cases op <;> simp only [Choice.eval,← readBase x, val]

theorem secondValue (x : Fin 128) (f : Nat) (op : Ordering) (l r : Fin 9) :
    val (nextMask f op l r) x = (Choice.mk op l r).eval ((false :: otherInputs x) ++ [val f x]) := by
  unfold val nextMask
  rw [evalGate]
  have hl := readExtra x f l
  have hr := readExtra x f r
  unfold val at hl hr
  cases op <;> simp only [Choice.eval,hl,hr]

theorem covered (a : Ordering) (l r : Fin 8) (b : Ordering) (s t : Fin 9) :
    allowed (nextMask 0 a l r) (nextMask (nextMask 0 a l r) b s t) = true := by
  obtain ⟨i,hi⟩ := List.get_of_mem (computedFirst a l r)
  have hz := computedSecond i b s t
  have eq : firstMasks.getD i.val 0 = nextMask 0 a l r := by simpa using hi
  rw [eq] at hz; exact hz
end PEqualNP.Outside.L_meta_29892_aux.DepthBridge

namespace PEqualNP.Outside.L_meta_29892_aux.DepthBridge
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_29892_aux PEqualNP.Outside.L_meta_29892_aux.CircuitSatBridge
def deepBank (f h : Nat) (x : Fin 128) : List Bool :=
  false :: (otherInputs x ++ [val f x, val h x, x.val.testBit 0 || val h x])
def NoSuffix (f h : Nat) : Prop := ∀ (rest : List Gate) (o : Nat),
  (∀ g ∈ rest, Supported g) → rest.length ≤ 7 →
  (∀ x : Fin 128, (run rest (deepBank f h x)).getD o false = target x) → False
end PEqualNP.Outside.L_meta_29892_aux.DepthBridge

namespace PEqualNP.Outside.L_meta_29892_aux.DepthBridge
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_29892_aux PEqualNP.Outside.L_meta_29892_aux.CircuitSatBridge

def lcase (k : Fin 64) : Fin 128 := ⟨k.val*2,by omega⟩
def hcase (k : Fin 64) : Fin 128 := ⟨k.val*2+1,by omega⟩

theorem zerosHit (h : Nat) (x : Fin 128) (ha : x.val.testBit 0 = false)
    (hb : x.val.testBit 1 = false) (hc : x.val.testBit 6 = false) (hh : val h x = true) :
    h &&& 1431655765 ≠ 0 := by
  intro eq
  have z := congrArg (fun n : Nat => n.testBit (x.val/2)) eq
  have s : ∀ y : Fin 128, y.val.testBit 0 = false → y.val.testBit 1 = false → y.val.testBit 6 = false →
      Nat.testBit 1431655765 (y.val/2) = true := by decide +kernel
  have hh' := s x ha hb hc
  simp only [Nat.testBit_and,hh',Bool.and_true,Nat.zero_testBit] at z
  exact Bool.noConfusion (hh.symm.trans z)

theorem stable (f h : Nat) (k : Fin 64) (ht : h.testBit k.val = true) :
    deepBank f h (lcase k) = deepBank f h (hcase k) := by
  have same : ∀ i : Fin 64, otherInputs (lcase i) = otherInputs (hcase i) := by decide +kernel
  have low : (lcase k).val / 2 = k.val := by unfold lcase; dsimp; omega
  have high : (hcase k).val / 2 = k.val := by unfold hcase; dsimp; omega
  simp only [deepBank,val,same k,low,high,ht,Bool.or_true]

theorem cannotSeparate (f h : Nat) (rest : List Gate) (o : Nat)
    (hr : ∀ x : Fin 128, (run rest (deepBank f h x)).getD o false = target x) :
    h &&& 7932806824482 = 0 := by
  apply Nat.zero_of_testBit_eq_false
  intro i
  rw [Nat.testBit_and]
  by_cases lo : i < 64
  · let k : Fin 64 := ⟨i,lo⟩
    by_cases hc : Nat.testBit 7932806824482 i = true
    · cases hv : h.testBit i with
      | false => rfl
      | true =>
        have sep : ∀ j : Fin 64, Nat.testBit 7932806824482 j.val = true →
            target (lcase j) ≠ target (hcase j) := by decide +kernel
        exact False.elim (sep k hc ((hr _).symm.trans ((congrArg (fun w => (run rest w).getD o false) (stable f h k hv)).trans (hr _))))
    · simp_all
  · have bound : 7932806824482 < 2^i := lt_of_lt_of_le (by decide : 7932806824482 < 2^64) (Nat.pow_le_pow_right (by decide) (by omega))
    simp [Nat.testBit_lt_two_pow bound]

end PEqualNP.Outside.L_meta_29892_aux.DepthBridge

namespace PEqualNP.Outside.L_meta_29892_aux.DepthBridge
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_29892_aux PEqualNP.Outside.L_meta_29892_aux.CircuitSatBridge

def reindex (i : Nat) := if i=7 then 9 else if i=8 then 7 else if i=9 then 8 else i

theorem admitFirst (a b : Nat) (x : Fin 128) :
    MoveOr.agrees id (false :: otherInputs x) (bank a b x) := by
  intro i hi nz
  simp [otherInputs] at hi
  interval_cases i <;> simp [bank,otherInputs] at *

theorem admitRot (a b f h : Nat) (x : Fin 128) (he : val h x = andfn a b x) :
    MoveOr.agrees reindex (deepBank f h x) (bank a b x ++ [val f x]) := by
  intro i hi nz
  simp [deepBank,otherInputs] at hi
  interval_cases i <;> simp [reindex,deepBank,bank,otherInputs,he,andfn] at *

def OneExclusion (a b : Nat) : Prop := ∀ (rest : List Gate) (o : Nat), (∀ g ∈ rest, Supported g) →
  rest.length ≤ 8 → (∀ x : Fin 128, (run rest (bank a b x)).getD o false = target x) → False

theorem replay (a b f h : Nat) (g : Gate) (gn : 0 ∉ g.inputs) (gs : Supported g)
    (gv : ∀ x : Fin 128, gval g (false :: otherInputs x) = val f x)
    (he : ∀ x, val h x = andfn a b x) (no : OneExclusion a b)
    (rest : List Gate) (o : Nat) (on : o ≠ 0) (ns : ∀ u ∈ rest, 0 ∉ u.inputs)
    (hs : ∀ u ∈ rest, Supported u) (hl : rest.length ≤ 7)
    (hr : ∀ x : Fin 128, (run rest (deepBank f h x)).getD o false = target x) : False := by
  let orig := MoveOr.move 7 9 id g
  let trans := MoveOr.transform rest 10 10 reindex
  let idx := MoveOr.pick (10+rest.length) (10+rest.length) trans.2 o
  refine no (orig :: trans.1) idx ?_ ?_ ?_
  · intro u hu
    rcases List.mem_cons.mp hu with rfl|hm
    · simpa [orig,MoveOr.move,Supported] using gs
    · exact MoveOr.transform_supported _ _ _ _ hs _ hm
  · simp [trans,MoveOr.transform_length]; omega
  intro x
  have val1 : gval orig (bank a b x) = val f x := by
    have hh := MoveOr.move_value (g := g) (admitFirst a b x) gn
    exact hh.trans (gv x)
  change (run trans.1 (bank a b x ++ [gval orig (bank a b x)])).getD idx false = _
  rw [val1]
  have conn : MoveOr.agrees trans.2 (run rest (deepBank f h x))
      (run trans.1 (bank a b x ++ [val f x])) := by
    exact MoveOr.transform_values rest _ _ _ (admitRot a b f h x (he x)) ns
  have pick := MoveOr.pick_ok conn o on
  simpa [idx,trans,MoveOr.run_len,MoveOr.transform_length,bank,deepBank,otherInputs] using pick.trans (hr x)

end PEqualNP.Outside.L_meta_29892_aux.DepthBridge

namespace PEqualNP.Outside.L_meta_29892_aux.DepthBridge
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_29892_aux PEqualNP.Outside.L_meta_29892_aux.CircuitSatBridge

def cleared (n : Nat) (g : Gate) : Gate := ⟨g.op,g.inputs.map (fun i => if i=0 then n else i)⟩

def clearZero (n : Nat) : List Gate → List Gate
  | [] => []
  | g :: gs => cleared n g :: clearZero (n+1) gs

theorem clearLength (n : Nat) (gs : List Gate) : (clearZero n gs).length = gs.length := by
  induction gs generalizing n with
  | nil => rfl
  | cons g gs ih => simp [clearZero,ih]

theorem clearProps (n : Nat) (hn : 0 < n) (gs : List Gate) (hs : ∀ g ∈ gs, Supported g) :
    ∀ g ∈ clearZero n gs, Supported g ∧ 0 ∉ g.inputs := by
  induction gs generalizing n with
  | nil => simp [clearZero]
  | cons g gs ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl|hh
    · constructor
      · simpa [cleared,Supported] using hs g (by simp)
      · simp only [cleared,List.mem_map]
        rintro ⟨i,_,e⟩
        split at e <;> omega
    · exact ih (n+1) (by omega) (fun v hv => hs v (by simp [hv])) _ hh

theorem clearPreserve (gs : List Gate) (t : List Bool) :
    run (clearZero (false::t).length gs) (false::t) = run gs (false::t) := by
  induction gs generalizing t with
  | nil => rfl
  | cons g gs ih =>
    have v : gval (cleared (false::t).length g) (false::t) = gval g (false::t) := by
      unfold gval cleared
      congr 1
      rw [List.map_map]
      apply List.map_congr_left
      intro i _
      by_cases e : i=0
      · simp [e]
      · simp [e]
    change run (clearZero ((false::t).length+1) gs) (false::(t++[gval (cleared _ g) (false::t)])) =
      run gs (false::(t++[gval g (false::t)]))
    rw [v]
    simpa using ih (t++[gval g (false::t)])

theorem replayMasked (a b f h : Nat) (g : Gate) (gn : 0 ∉ g.inputs) (gs : Supported g)
    (gv : ∀ x : Fin 128, gval g (false :: otherInputs x) = val f x)
    (he : ∀ x, val h x = andfn a b x) (no : OneExclusion a b)
    (rest : List Gate) (o : Nat) (hs : ∀ u ∈ rest, Supported u) (hl : rest.length ≤ 7)
    (hr : ∀ x : Fin 128, (run rest (deepBank f h x)).getD o false = target x) : False := by
  let c := clearZero 10 rest
  have cp := clearProps 10 (by decide) rest hs
  have on : o ≠ 0 := by
    intro e
    have u := hr 3
    rw [e,keepWire _ _ _ (by simp [deepBank])] at u
    contradiction
  apply replay a b f h g gn gs gv he no c o on (fun u hu => (cp u hu).2) (fun u hu => (cp u hu).1) (by simpa [c,clearLength] using hl)
  intro x
  have hh := clearPreserve rest (otherInputs x ++ [val f x,val h x,x.val.testBit 0 || val h x])
  change run c (deepBank f h x) = run rest (deepBank f h x) at hh
  rw [hh]
  exact hr x

end PEqualNP.Outside.L_meta_29892_aux.DepthBridge

namespace PEqualNP.Outside.L_meta_29892_aux.DepthBridge
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_29892_aux PEqualNP.Outside.L_meta_29892_aux.CircuitSatBridge
theorem onlyTwoEight (l : List Nat) (hn : l.length ≤ 2) (ha : 0 ∈ l) (hb : 8 ∈ l) :
    l = [0,8] ∨ l = [8,0] := by
  rcases l with _ | ⟨a,l⟩
  · simp at ha
  rcases l with _ | ⟨b,l⟩
  · simp_all; omega
  have e : l = [] := List.length_eq_zero_iff.mp (by simpa using hn)
  subst l
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha hb
  rcases ha with h|h <;> rcases hb with k|k <;> simp_all <;> omega

theorem simpleTo (h : Nat) (hs : h ∈ simpleMasks) : ∃ a b, (∀ x, val h x = andfn a b x) ∧ OneExclusion a b := by
  simp only [simpleMasks,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl|rfl|rfl|rfl
  · exact ⟨2,3,by decide +kernel,no23⟩
  · exact ⟨2,5,by decide +kernel,no25⟩
  · exact ⟨3,4,by decide +kernel,no34⟩
  · exact ⟨4,5,by decide +kernel,no45⟩
theorem orEight (g : Gate) (w : List Bool) (ho : g.op = .or) (hi : g.inputs = [0,8] ∨ g.inputs = [8,0]) :
    gval g w = (w.getD 0 false || w.getD 8 false) := by
  rcases hi with e|e <;> simp [gval,ho,e,GateOp.eval,Bool.or_comm]

end PEqualNP.Outside.L_meta_29892_aux.DepthBridge

namespace PEqualNP.Outside.L_meta_29892_aux.DepthBridge
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_29892_aux PEqualNP.Outside.L_meta_29892_aux.CircuitSatBridge

namespace Depth0
open CircuitSatBridge FreeSupport PEqualNP.CircuitLowerBounds
def w0 := mkSampleWire 0 0 0 0 0 0
def w1 := mkSampleWire 721554505731 592980541445 84412424 0 0 0
def w2 := mkSampleWire 721606049859 593048174605 86526031 0 0 0
def w3 := mkSampleWire 0 34629305344 362496 1140867088 34360804377 360448
def w4 := mkSampleWire 281056185356 417863375696 416486294 178915487680 274912057446 1183766
def w5 := mkSampleWire 96773100208 449110985888 1542720 551703433904 449110986079 1542720
def w6 := mkSampleWire 71077487008 636246747778 582772022 530606828870 550330573344 44582166
def w7 := mkSampleWire 792631992739 679467281031 666660158 530606828870 550330573344 44582166
def w8 := mkSampleWire 822674119423 564877134845 167758215 531144748998 840325610086 201317783
def w9 := mkSampleWire 725849475087 633111708501 264774056 369430626319 633111708288 264774056
def w10 := mkSampleWire 725849475087 667741013845 265136552 370571493407 667472512665 265134504
def w11 := mkSampleWire 796926962095 684971257815 805170622 548949060959 667506075321 267249086
def w12 := mkSampleWire 721606049859 593081204749 354966543 143881502976 33554464 270537731
def w13 := mkSampleWire 721606049859 1005398624269 354966607 694444069792 412619475302 270539843
def w14 := mkSampleWire 347838703008 464184801410 269819392 695584936880 466332810623 272080451
def w15 := mkSampleWire 751672924767 635326826365 803922431 403926690895 633178817152 801661372
def w16 := mkSampleWire 751672924767 669955065725 803924479 403926690895 633178817152 801661372
def w17 := mkSampleWire 751672924767 669956130685 804252159 405067557983 667539621529 802021820
def w18 := mkSampleWire 377905577916 94113003506 718775216 405067557983 686892152473 803201980
def w19 := mkSampleWire 373662152688 431770613930 808605271 728940134368 432039115110 808607319
def w20 := mkSampleWire 276837508352 534634492930 905983608 568366878777 259186017689 872424040
def w21 := mkSampleWire 1028434140767 463264879997 490969801 568904798905 549181054431 1029159657
def w22 := mkSampleWire 1002738527567 650400641887 1072199103 547808193871 650400641696 1072199103
def w23 := mkSampleWire 818455442419 681648252079 657255529 920596140095 824599570329 1072558057
def w24 := mkSampleWire 1002738527567 685029947231 1072561599 548949060959 684761446073 1072559551
def wires : List Wire := [w0, w13, w10, w4, w20, w6, w5, w22, w9, w15]
def n1_0 : List Wire := [w1, w13, w4, w6, w15, w20]
def n1_1 : List Wire := [w3, w13, w4, w6, w15, w20]
def n1_2 : List Wire := [w5, w10, w13, w4, w6, w15, w20]
def n1_3 : List Wire := [w8, w10, w13, w4, w6, w15]
def n1_4 : List Wire := [w10, w4, w6, w18, w15, w20]
def n1_5 : List Wire := [w10, w13, w4, w6, w15, w20]
def n1_6 : List Wire := [w10, w13, w4, w21, w15, w20]
def n1_7 : List Wire := [w10, w13, w6, w23, w15, w20]
def n1_8 : List Wire := [w10, w14, w13, w4, w6, w20]
def n1_9 : List Wire := [w13, w4, w6, w15, w11, w20]
def n1_10 : List Wire := [w13, w4, w6, w15, w17, w20]
def n1_11 : List Wire := [w13, w4, w6, w15, w19, w20]
def n1_12 : List Wire := [w13, w4, w6, w15, w20, w24]
def n2_0 : List Wire := [w2, w4, w6, w15, w20]
def n2_1 : List Wire := [w12, w4, w6, w15, w20]
def n2_2 : List Wire := [w13, w4, w6, w16, w20]
def n2_3 : List Wire := [w13, w4, w7, w15, w20]
def test (t : Fin 110) (b : Bool) : Fin 128 :=
  let pts : List (Fin 128) := if b then [21, 37, 37, 21, 84, 82, 41, 74, 42, 74, 41, 41, 82, 41, 84, 42, 42, 82, 82, 21, 74, 41, 21, 37, 21, 37, 84, 41, 82, 74, 84, 42, 42, 37, 21, 41, 37, 42, 37, 82, 84, 74, 74, 84, 84, 42, 74, 21, 82, 37, 84, 74, 8, 32, 84, 82, 74, 37, 4, 74, 84, 21, 37, 16, 64, 42, 1, 21, 82, 37, 21, 64, 5, 5, 16, 84, 21, 82, 74, 37, 2, 42, 41, 21, 41, 21, 82, 4, 37, 80, 34, 66, 10, 20, 33, 68, 68, 72, 68, 36, 72, 34, 4, 36, 4, 36, 20, 5, 18, 17] else [6, 6, 12, 12, 65, 96, 3, 96, 48, 65, 24, 12, 65, 48, 96, 3, 24, 3, 48, 48, 3, 65, 24, 48, 3, 3, 48, 96, 24, 24, 24, 96, 12, 65, 65, 6, 96, 6, 24, 6, 6, 48, 6, 3, 12, 65, 12, 96, 12, 44, 85, 106, 24, 48, 116, 114, 78, 52, 6, 75, 92, 23, 38, 24, 96, 58, 3, 28, 86, 53, 29, 65, 12, 6, 48, 86, 52, 90, 90, 39, 3, 43, 43, 22, 57, 53, 83, 12, 45, 88, 50, 70, 26, 53, 35, 69, 76, 73, 100, 39, 104, 35, 13, 44, 7, 53, 23, 13, 26, 49]
  pts.getD t.val 0

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem samples : ∀ t : Fin 110, ∀ b : Bool,
   sample wires t b = deepBank 4294967295 3435973836 (test t b) ∧ target (test t b) = !b := by decide +kernel

theorem suffix (rest : List Gate) (o : Nat) (hs : ∀ g ∈ rest, Supported g) (hlen : rest.length ≤ 7)
   (hr : ∀ x : Fin 128, (run rest (deepBank 4294967295 3435973836 x)).getD o false = target x) :
   attainable 7 wires := by
 obtain ⟨cs,hl,hv,he⟩ := fixed_slots 6 10 o rest hs hlen
 refine ⟨cs,16,hl,hv,?_⟩
 intro t
 have h (b : Bool) : (runChoices cs (sample wires t b)).getD 16 false = !b := by
   rw [(samples t b).1, he]
   · exact (hr _).trans (samples t b).2
   · simp [deepBank, otherInputs]
 exact ⟨h false, h true⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_0 : ¬ attainable 5 n2_0 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_1 : ¬ attainable 5 n2_1 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_2 : ¬ attainable 5 n2_2 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_3 : ¬ attainable 5 n2_3 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_0 : ¬ attainable 6 n1_0 := by
  exact stepCover [n2_2, n2_3] (by decide +kernel) (rejectCons r2_n2_2 (rejectCons r2_n2_3 (rejectNil 5)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_1 : ¬ attainable 6 n1_1 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_2 : ¬ attainable 6 n1_2 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_3 : ¬ attainable 6 n1_3 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_4 : ¬ attainable 6 n1_4 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_5 : ¬ attainable 6 n1_5 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_6 : ¬ attainable 6 n1_6 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_7 : ¬ attainable 6 n1_7 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_8 : ¬ attainable 6 n1_8 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_9 : ¬ attainable 6 n1_9 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_10 : ¬ attainable 6 n1_10 := by
  exact stepCover [n2_0] (by decide +kernel) (rejectCons r2_n2_0 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_11 : ¬ attainable 6 n1_11 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_12 : ¬ attainable 6 n1_12 := by
  exact stepCover [n2_1] (by decide +kernel) (rejectCons r2_n2_1 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r0_wires : ¬ attainable 7 wires := by
  exact stepCover [n1_0, n1_1, n1_2, n1_3, n1_4, n1_5, n1_6, n1_7, n1_8, n1_9, n1_10, n1_11, n1_12] (by decide +kernel) (rejectCons r1_n1_0 (rejectCons r1_n1_1 (rejectCons r1_n1_2 (rejectCons r1_n1_3 (rejectCons r1_n1_4 (rejectCons r1_n1_5 (rejectCons r1_n1_6 (rejectCons r1_n1_7 (rejectCons r1_n1_8 (rejectCons r1_n1_9 (rejectCons r1_n1_10 (rejectCons r1_n1_11 (rejectCons r1_n1_12 (rejectNil 6))))))))))))))

end Depth0

theorem noDepth0 : NoSuffix 4294967295 3435973836 := fun rest o hs hl hr => Depth0.r0_wires (Depth0.suffix rest o hs hl hr)

namespace Reverse0
open CircuitSatBridge FreeSupport
def wires : List Wire := [Depth0.w0, Depth0.w5, Depth0.w6, Depth0.w20, Depth0.w4, Depth0.w10, Depth0.w13, Depth0.w22, Depth0.w9, Depth0.w15]
def test (t : Fin 110) (b : Bool) : Fin 128 :=
  let pts : List (Fin 128) := if b then [41, 37, 37, 41, 42, 74, 21, 82, 84, 82, 21, 21, 74, 21, 42, 84, 84, 74, 74, 41, 82, 21, 41, 37, 41, 37, 42, 21, 74, 82, 42, 84, 84, 37, 41, 21, 37, 84, 37, 74, 42, 82, 82, 42, 42, 84, 82, 41, 74, 37, 42, 82, 16, 4, 42, 74, 82, 37, 32, 82, 42, 41, 37, 8, 2, 84, 1, 41, 74, 37, 41, 2, 33, 33, 8, 42, 41, 74, 82, 37, 64, 84, 21, 41, 21, 41, 74, 32, 37, 10, 68, 66, 80, 40, 5, 34, 34, 18, 34, 36, 18, 68, 32, 36, 32, 36, 40, 33, 72, 9] else [96, 96, 48, 48, 3, 6, 65, 6, 12, 3, 24, 48, 3, 12, 6, 65, 24, 65, 12, 12, 65, 3, 24, 12, 65, 65, 12, 6, 24, 24, 24, 6, 48, 3, 3, 96, 6, 96, 24, 96, 96, 12, 96, 65, 48, 3, 48, 6, 48, 52, 43, 86, 24, 12, 46, 78, 114, 44, 96, 83, 58, 105, 100, 24, 6, 92, 65, 56, 106, 45, 57, 3, 48, 96, 12, 106, 44, 90, 90, 101, 65, 85, 85, 104, 29, 45, 75, 48, 53, 26, 76, 98, 88, 45, 69, 35, 50, 19, 38, 101, 22, 69, 49, 52, 97, 45, 105, 49, 88, 13]
  pts.getD t.val 0
set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem samples : ∀ t : Fin 110, ∀ b : Bool,
   sample wires t b = deepBank 6148914691236517205 6148820867675914240 (test t b) ∧ target (test t b) = !b := by decide +kernel

theorem suffix (rest : List Gate) (o : Nat) (hs : ∀ g ∈ rest, Supported g) (hlen : rest.length ≤ 7)
   (hr : ∀ x : Fin 128, (run rest (deepBank 6148914691236517205 6148820867675914240 x)).getD o false = target x) :
   attainable 7 wires := by
 obtain ⟨cs,hl,hv,he⟩ := fixed_slots 6 10 o rest hs hlen
 refine ⟨cs,16,hl,hv,?_⟩
 intro t
 have h (b : Bool) : (runChoices cs (sample wires t b)).getD 16 false = !b := by
   rw [(samples t b).1, he]
   · exact (hr _).trans (samples t b).2
   · simp [deepBank, otherInputs]
 exact ⟨h false, h true⟩
theorem project (k : Nat) (hs : attainable k wires) : attainable k Depth0.wires := by
  have hm : wires.all (fun w => Depth0.wires.contains w) = true := by decide +kernel
  obtain ⟨cs, o, rfl, _, orient⟩ := hs
  obtain ⟨support, sub, _, det⟩ := bounded_support cs wires.length o
  apply project_suffix sub orient det
  intro i hi
  exact Or.inl (List.contains_iff_mem.mp ((List.all_eq_true.mp hm) _ (List.getElem_mem _)))

end Reverse0

theorem revDepth0 : NoSuffix 6148914691236517205 6148820867675914240 := fun rest o hs hl hr => Depth0.r0_wires (Reverse0.project 7 (Reverse0.suffix rest o hs hl hr))

namespace Depth1
open CircuitSatBridge FreeSupport PEqualNP.CircuitLowerBounds
def w0 := mkSampleWire 0 0 0 0 0 0
def w1 := mkSampleWire 1030792151040 259 0 0 0 0
def w2 := mkSampleWire 1068910641152 148648283399 26072138 263478297136 148514065610 25744448
def w3 := mkSampleWire 13130271528 857506695720 571636112 545891160720 852620329668 34627984
def w4 := mkSampleWire 1043922422568 857506695979 571636112 545891160720 852620329668 34627984
def w5 := mkSampleWire 1047972054209 619601269571 103811620 835495410884 619600745013 35654144
def w6 := mkSampleWire 1086090544321 768249552711 129883758 1098973708020 768114810623 61398592
def w7 := mkSampleWire 17469375699 114233564240 202973685 126434263851 43357097354 202449141
def w8 := mkSampleWire 1048261526739 114233564499 202973685 126434263851 43357097354 202449141
def w9 := mkSampleWire 290811926 596038334096 426682113 970829215952 553088266852 288260352
def w10 := mkSampleWire 1031082962966 596038334355 426682113 970829215952 553088266852 288260352
def w11 := mkSampleWire 13087567916 603333749920 954261160 3859924271 35322203419 683679272
def w12 := mkSampleWire 1043879718956 603333750179 954261160 3859924271 35322203419 683679272
def w13 := mkSampleWire 38162533120 452571468300 935788634 552546610511 39919030577 877068298
def w14 := mkSampleWire 1068954684160 452571468559 935788634 552546610511 39919030577 877068298
def wires : List Wire := [w0, w7, w5, w2, w13, w3, w11, w1, w0, w9]
def n1_0 : List Wire := [w2, w5, w7, w9, w3, w13, w11]
def n1_1 : List Wire := [w2, w5, w7, w9, w3, w13, w12]
def n1_2 : List Wire := [w2, w5, w7, w9, w3, w14, w11]
def n1_3 : List Wire := [w2, w5, w7, w9, w4, w13, w11]
def n1_4 : List Wire := [w2, w5, w7, w10, w3, w13, w11]
def n1_5 : List Wire := [w2, w5, w8, w9, w3, w13, w11]
def n1_6 : List Wire := [w6, w7, w9, w3, w13, w11]
def test (t : Fin 110) (b : Bool) : Fin 128 :=
  let pts : List (Fin 128) := if b then [82, 82, 84, 82, 41, 74, 21, 37, 82, 42, 84, 21, 37, 21, 74, 74, 74, 41, 41, 21, 82, 37, 21, 41, 37, 84, 84, 41, 42, 82, 74, 84, 42, 37, 42, 42, 42, 41, 37, 21, 84, 74, 37, 74, 84, 21, 41, 42, 82, 37, 74, 74, 21, 1, 42, 42, 37, 64, 84, 82, 84, 41, 82, 1, 84, 21, 41, 82, 74, 64, 21, 41, 16, 42, 32, 82, 4, 8, 32, 37, 2, 16, 2, 80, 34, 66, 10, 34, 33, 68, 72, 68, 72, 34, 40, 9, 18, 17, 17, 9, 34, 5, 80, 72, 9, 36, 18, 66, 17, 80] else [6, 3, 65, 96, 3, 96, 6, 6, 48, 48, 6, 48, 65, 65, 65, 6, 3, 24, 65, 24, 65, 48, 3, 48, 3, 48, 96, 96, 3, 24, 24, 24, 96, 96, 6, 24, 12, 12, 12, 12, 12, 12, 24, 48, 3, 96, 6, 65, 12, 53, 75, 106, 23, 65, 106, 58, 39, 65, 85, 86, 86, 105, 114, 3, 116, 53, 57, 90, 90, 96, 85, 43, 48, 43, 96, 83, 6, 24, 48, 101, 3, 24, 6, 88, 50, 70, 26, 98, 35, 69, 73, 100, 104, 35, 104, 73, 26, 49, 25, 11, 38, 69, 81, 88, 25, 52, 22, 67, 81, 112]
  pts.getD t.val 0

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem samples : ∀ t : Fin 110, ∀ b : Bool,
   sample wires t b = deepBank 13889313184910721216 13835269164735971328 (test t b) ∧ target (test t b) = !b := by decide +kernel

theorem suffix (rest : List Gate) (o : Nat) (hs : ∀ g ∈ rest, Supported g) (hlen : rest.length ≤ 7)
   (hr : ∀ x : Fin 128, (run rest (deepBank 13889313184910721216 13835269164735971328 x)).getD o false = target x) :
   attainable 7 wires := by
 obtain ⟨cs,hl,hv,he⟩ := fixed_slots 6 10 o rest hs hlen
 refine ⟨cs,16,hl,hv,?_⟩
 intro t
 have h (b : Bool) : (runChoices cs (sample wires t b)).getD 16 false = !b := by
   rw [(samples t b).1, he]
   · exact (hr _).trans (samples t b).2
   · simp [deepBank, otherInputs]
 exact ⟨h false, h true⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_0 : ¬ attainable 6 n1_0 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_1 : ¬ attainable 6 n1_1 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_2 : ¬ attainable 6 n1_2 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_3 : ¬ attainable 6 n1_3 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_4 : ¬ attainable 6 n1_4 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_5 : ¬ attainable 6 n1_5 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_6 : ¬ attainable 6 n1_6 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r0_wires : ¬ attainable 7 wires := by
  exact stepCover [n1_0, n1_1, n1_2, n1_3, n1_4, n1_5, n1_6] (by decide +kernel) (rejectCons r1_n1_0 (rejectCons r1_n1_1 (rejectCons r1_n1_2 (rejectCons r1_n1_3 (rejectCons r1_n1_4 (rejectCons r1_n1_5 (rejectCons r1_n1_6 (rejectNil 6))))))))

end Depth1

theorem noDepth1 : NoSuffix 13889313184910721216 13835269164735971328 := fun rest o hs hl hr => Depth1.r0_wires (Depth1.suffix rest o hs hl hr)

namespace Reverse1
open CircuitSatBridge FreeSupport
def wires : List Wire := [Depth1.w0, Depth1.w11, Depth1.w3, Depth1.w13, Depth1.w2, Depth1.w5, Depth1.w7, Depth1.w1, Depth1.w0, Depth1.w9]
def test (t : Fin 110) (b : Bool) : Fin 128 :=
  let pts : List (Fin 128) := if b then [74, 74, 42, 74, 21, 82, 41, 37, 74, 84, 42, 41, 37, 41, 82, 82, 82, 21, 21, 41, 74, 37, 41, 21, 37, 42, 42, 21, 84, 74, 82, 42, 84, 37, 84, 84, 84, 21, 37, 41, 42, 82, 37, 82, 42, 41, 21, 84, 74, 37, 82, 82, 41, 1, 84, 84, 37, 2, 42, 74, 42, 21, 74, 1, 42, 41, 21, 74, 82, 2, 41, 21, 8, 84, 4, 74, 32, 16, 4, 37, 64, 8, 64, 10, 68, 66, 80, 68, 5, 34, 18, 34, 18, 68, 20, 17, 72, 9, 9, 17, 68, 33, 10, 18, 17, 36, 72, 66, 9, 10] else [96, 65, 3, 6, 65, 6, 96, 96, 12, 12, 96, 12, 3, 3, 3, 96, 65, 24, 3, 24, 3, 12, 65, 12, 65, 12, 6, 6, 65, 24, 24, 24, 6, 6, 96, 24, 48, 48, 48, 48, 48, 48, 24, 12, 65, 6, 96, 3, 48, 45, 83, 86, 105, 3, 86, 92, 101, 3, 43, 106, 106, 23, 78, 65, 46, 45, 29, 90, 90, 6, 43, 85, 12, 85, 6, 75, 96, 24, 12, 39, 65, 24, 96, 26, 76, 98, 88, 70, 69, 35, 19, 38, 22, 69, 22, 19, 88, 13, 25, 81, 100, 35, 11, 26, 25, 44, 104, 67, 11, 14]
  pts.getD t.val 0
set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem samples : ∀ t : Fin 110, ∀ b : Bool,
   sample wires t b = deepBank 18374686483949813760 17293822573129236480 (test t b) ∧ target (test t b) = !b := by decide +kernel

theorem suffix (rest : List Gate) (o : Nat) (hs : ∀ g ∈ rest, Supported g) (hlen : rest.length ≤ 7)
   (hr : ∀ x : Fin 128, (run rest (deepBank 18374686483949813760 17293822573129236480 x)).getD o false = target x) :
   attainable 7 wires := by
 obtain ⟨cs,hl,hv,he⟩ := fixed_slots 6 10 o rest hs hlen
 refine ⟨cs,16,hl,hv,?_⟩
 intro t
 have h (b : Bool) : (runChoices cs (sample wires t b)).getD 16 false = !b := by
   rw [(samples t b).1, he]
   · exact (hr _).trans (samples t b).2
   · simp [deepBank, otherInputs]
 exact ⟨h false, h true⟩
theorem project (k : Nat) (hs : attainable k wires) : attainable k Depth1.wires := by
  have hm : wires.all (fun w => Depth1.wires.contains w) = true := by decide +kernel
  obtain ⟨cs, o, rfl, _, orient⟩ := hs
  obtain ⟨support, sub, _, det⟩ := bounded_support cs wires.length o
  apply project_suffix sub orient det
  intro i hi
  exact Or.inl (List.contains_iff_mem.mp ((List.all_eq_true.mp hm) _ (List.getElem_mem _)))

end Reverse1

theorem revDepth1 : NoSuffix 18374686483949813760 17293822573129236480 := fun rest o hs hl hr => Depth1.r0_wires (Reverse1.project 7 (Reverse1.suffix rest o hs hl hr))

namespace Depth2
open CircuitSatBridge FreeSupport PEqualNP.CircuitLowerBounds
def w0 := mkSampleWire 0 0 0 0 0 0
def w1 := mkSampleWire 1030792151040 259 0 0 0 0
def w2 := mkSampleWire 1068910641152 148648283399 26072138 263478297136 148514065610 25744448
def w3 := mkSampleWire 13130271528 857506695720 571636112 545891160720 852620329668 34627984
def w4 := mkSampleWire 1043922422568 857506695979 571636112 545891160720 852620329668 34627984
def w5 := mkSampleWire 1047972054209 619601269571 103811620 835495410884 619600745013 35654144
def w6 := mkSampleWire 1086090544321 768249552711 129883758 1098973708020 768114810623 61398592
def w7 := mkSampleWire 17469375699 114233564240 202973685 126434263851 43357097354 202449141
def w8 := mkSampleWire 1048261526739 114233564499 202973685 126434263851 43357097354 202449141
def w9 := mkSampleWire 290811926 596038334096 426682113 970829215952 553088266852 288260352
def w10 := mkSampleWire 1031082962966 596038334355 426682113 970829215952 553088266852 288260352
def w11 := mkSampleWire 13087567916 603333749920 954261160 3859924271 35322203419 683679272
def w12 := mkSampleWire 1043879718956 603333750179 954261160 3859924271 35322203419 683679272
def w13 := mkSampleWire 38162533120 452571468300 935788634 552546610511 39919030577 877068298
def w14 := mkSampleWire 1068954684160 452571468559 935788634 552546610511 39919030577 877068298
def wires : List Wire := [w0, w7, w5, w2, w13, w3, w11, w1, w0, w9]
def n1_0 : List Wire := [w2, w5, w7, w9, w3, w13, w11]
def n1_1 : List Wire := [w2, w5, w7, w9, w3, w13, w12]
def n1_2 : List Wire := [w2, w5, w7, w9, w3, w14, w11]
def n1_3 : List Wire := [w2, w5, w7, w9, w4, w13, w11]
def n1_4 : List Wire := [w2, w5, w7, w10, w3, w13, w11]
def n1_5 : List Wire := [w2, w5, w8, w9, w3, w13, w11]
def n1_6 : List Wire := [w6, w7, w9, w3, w13, w11]
def test (t : Fin 110) (b : Bool) : Fin 128 :=
  let pts : List (Fin 128) := if b then [82, 82, 84, 82, 41, 74, 21, 37, 82, 42, 84, 21, 37, 21, 74, 74, 74, 41, 41, 21, 82, 37, 21, 41, 37, 84, 84, 41, 42, 82, 74, 84, 42, 37, 42, 42, 42, 41, 37, 21, 84, 74, 37, 74, 84, 21, 41, 42, 82, 37, 74, 74, 21, 1, 42, 42, 37, 64, 84, 82, 84, 41, 82, 1, 84, 21, 41, 82, 74, 64, 21, 41, 16, 42, 32, 82, 4, 8, 32, 37, 2, 16, 2, 80, 34, 66, 10, 34, 33, 68, 72, 68, 72, 34, 40, 9, 18, 17, 17, 9, 34, 5, 80, 72, 9, 36, 18, 66, 17, 80] else [6, 3, 65, 96, 3, 96, 6, 6, 48, 48, 6, 48, 65, 65, 65, 6, 3, 24, 65, 24, 65, 48, 3, 48, 3, 48, 96, 96, 3, 24, 24, 24, 96, 96, 6, 24, 12, 12, 12, 12, 12, 12, 24, 48, 3, 96, 6, 65, 12, 53, 75, 106, 23, 65, 106, 58, 39, 65, 85, 86, 86, 105, 114, 3, 116, 53, 57, 90, 90, 96, 85, 43, 48, 43, 96, 83, 6, 24, 48, 101, 3, 24, 6, 88, 50, 70, 26, 98, 35, 69, 73, 100, 104, 35, 104, 73, 26, 49, 25, 11, 38, 69, 81, 88, 25, 52, 22, 67, 81, 112]
  pts.getD t.val 0

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem samples : ∀ t : Fin 110, ∀ b : Bool,
   sample wires t b = deepBank 13889313184910721216 13889101254044418048 (test t b) ∧ target (test t b) = !b := by decide +kernel

theorem suffix (rest : List Gate) (o : Nat) (hs : ∀ g ∈ rest, Supported g) (hlen : rest.length ≤ 7)
   (hr : ∀ x : Fin 128, (run rest (deepBank 13889313184910721216 13889101254044418048 x)).getD o false = target x) :
   attainable 7 wires := by
 obtain ⟨cs,hl,hv,he⟩ := fixed_slots 6 10 o rest hs hlen
 refine ⟨cs,16,hl,hv,?_⟩
 intro t
 have h (b : Bool) : (runChoices cs (sample wires t b)).getD 16 false = !b := by
   rw [(samples t b).1, he]
   · exact (hr _).trans (samples t b).2
   · simp [deepBank, otherInputs]
 exact ⟨h false, h true⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_0 : ¬ attainable 6 n1_0 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_1 : ¬ attainable 6 n1_1 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_2 : ¬ attainable 6 n1_2 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_3 : ¬ attainable 6 n1_3 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_4 : ¬ attainable 6 n1_4 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_5 : ¬ attainable 6 n1_5 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_6 : ¬ attainable 6 n1_6 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r0_wires : ¬ attainable 7 wires := by
  exact stepCover [n1_0, n1_1, n1_2, n1_3, n1_4, n1_5, n1_6] (by decide +kernel) (rejectCons r1_n1_0 (rejectCons r1_n1_1 (rejectCons r1_n1_2 (rejectCons r1_n1_3 (rejectCons r1_n1_4 (rejectCons r1_n1_5 (rejectCons r1_n1_6 (rejectNil 6))))))))

end Depth2

theorem noDepth2 : NoSuffix 13889313184910721216 13889101254044418048 := fun rest o hs hl hr => Depth2.r0_wires (Depth2.suffix rest o hs hl hr)

namespace Reverse2
open CircuitSatBridge FreeSupport
def wires : List Wire := [Depth2.w0, Depth2.w11, Depth2.w3, Depth2.w13, Depth2.w2, Depth2.w5, Depth2.w7, Depth2.w1, Depth2.w0, Depth2.w9]
def test (t : Fin 110) (b : Bool) : Fin 128 :=
  let pts : List (Fin 128) := if b then [74, 74, 42, 74, 21, 82, 41, 37, 74, 84, 42, 41, 37, 41, 82, 82, 82, 21, 21, 41, 74, 37, 41, 21, 37, 42, 42, 21, 84, 74, 82, 42, 84, 37, 84, 84, 84, 21, 37, 41, 42, 82, 37, 82, 42, 41, 21, 84, 74, 37, 82, 82, 41, 1, 84, 84, 37, 2, 42, 74, 42, 21, 74, 1, 42, 41, 21, 74, 82, 2, 41, 21, 8, 84, 4, 74, 32, 16, 4, 37, 64, 8, 64, 10, 68, 66, 80, 68, 5, 34, 18, 34, 18, 68, 20, 17, 72, 9, 9, 17, 68, 33, 10, 18, 17, 36, 72, 66, 9, 10] else [96, 65, 3, 6, 65, 6, 96, 96, 12, 12, 96, 12, 3, 3, 3, 96, 65, 24, 3, 24, 3, 12, 65, 12, 65, 12, 6, 6, 65, 24, 24, 24, 6, 6, 96, 24, 48, 48, 48, 48, 48, 48, 24, 12, 65, 6, 96, 3, 48, 45, 83, 86, 105, 3, 86, 92, 101, 3, 43, 106, 106, 23, 78, 65, 46, 45, 29, 90, 90, 6, 43, 85, 12, 85, 6, 75, 96, 24, 12, 39, 65, 24, 96, 26, 76, 98, 88, 70, 69, 35, 19, 38, 22, 69, 22, 19, 88, 13, 25, 81, 100, 35, 11, 26, 25, 44, 104, 67, 11, 14]
  pts.getD t.val 0
set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem samples : ∀ t : Fin 110, ∀ b : Bool,
   sample wires t b = deepBank 18374686483949813760 14699749187159851008 (test t b) ∧ target (test t b) = !b := by decide +kernel

theorem suffix (rest : List Gate) (o : Nat) (hs : ∀ g ∈ rest, Supported g) (hlen : rest.length ≤ 7)
   (hr : ∀ x : Fin 128, (run rest (deepBank 18374686483949813760 14699749187159851008 x)).getD o false = target x) :
   attainable 7 wires := by
 obtain ⟨cs,hl,hv,he⟩ := fixed_slots 6 10 o rest hs hlen
 refine ⟨cs,16,hl,hv,?_⟩
 intro t
 have h (b : Bool) : (runChoices cs (sample wires t b)).getD 16 false = !b := by
   rw [(samples t b).1, he]
   · exact (hr _).trans (samples t b).2
   · simp [deepBank, otherInputs]
 exact ⟨h false, h true⟩
theorem project (k : Nat) (hs : attainable k wires) : attainable k Depth2.wires := by
  have hm : wires.all (fun w => Depth2.wires.contains w) = true := by decide +kernel
  obtain ⟨cs, o, rfl, _, orient⟩ := hs
  obtain ⟨support, sub, _, det⟩ := bounded_support cs wires.length o
  apply project_suffix sub orient det
  intro i hi
  exact Or.inl (List.contains_iff_mem.mp ((List.all_eq_true.mp hm) _ (List.getElem_mem _)))

end Reverse2

theorem revDepth2 : NoSuffix 18374686483949813760 14699749187159851008 := fun rest o hs hl hr => Depth2.r0_wires (Reverse2.project 7 (Reverse2.suffix rest o hs hl hr))

namespace Depth3
open CircuitSatBridge FreeSupport PEqualNP.CircuitLowerBounds
def w0 := mkSampleWire 0 0 0 0 0 0
def w1 := mkSampleWire 0 17197172224 8 1098437885952 17197172611 8
def w2 := mkSampleWire 693915109445 232250803752 681755978 1098573808192 86219687815 10666056
def w3 := mkSampleWire 318415184256 843517005334 117443260 1098454728843 842434873227 117440664
def w4 := mkSampleWire 1012330293701 1058570636862 799199230 1098590651083 911457388431 128106712
def w5 := mkSampleWire 18457134632 876845465409 139973824 830061223083 842485423259 134726784
def w6 := mkSampleWire 86977910290 385664255680 382296137 268573794896 110647870244 381689928
def w7 := mkSampleWire 722151170052 218510104590 502630837 920976692 149252708464 408226085
def w8 := mkSampleWire 283671658920 759247466769 574501453 1014948692 209423999076 540553797
def w9 := mkSampleWire 75435087955 986555291808 822624007 935402927 962614204504 554180359
def wires : List Wire := [w0, w9, w2, w7, w3, w8, w5, w1, w0, w6]
def n1_0 : List Wire := [w3, w5, w6, w7, w8, w2, w9]
def n1_1 : List Wire := [w5, w6, w7, w8, w4, w9]
def test (t : Fin 110) (b : Bool) : Fin 128 :=
  let pts : List (Fin 128) := if b then [82, 82, 42, 82, 41, 74, 37, 82, 42, 37, 74, 74, 74, 41, 41, 41, 82, 37, 41, 37, 37, 41, 42, 74, 82, 74, 42, 37, 42, 42, 84, 21, 84, 21, 21, 21, 21, 21, 84, 84, 84, 84, 37, 82, 74, 41, 42, 84, 21, 21, 84, 74, 74, 32, 64, 41, 74, 74, 42, 84, 4, 41, 2, 32, 21, 37, 16, 64, 4, 82, 41, 41, 1, 8, 84, 1, 37, 42, 82, 82, 42, 2, 42, 21, 16, 8, 37, 80, 10, 34, 66, 10, 34, 33, 68, 68, 72, 68, 72, 34, 40, 36, 9, 5, 18, 17, 17, 72, 9, 34] else [6, 3, 12, 96, 3, 96, 6, 48, 48, 65, 65, 6, 3, 24, 12, 65, 65, 48, 48, 3, 12, 96, 3, 12, 24, 24, 96, 96, 6, 24, 65, 6, 6, 48, 65, 24, 3, 12, 48, 12, 96, 24, 24, 12, 48, 6, 65, 3, 96, 85, 85, 90, 106, 96, 96, 105, 75, 78, 106, 116, 12, 45, 3, 48, 23, 39, 48, 65, 6, 90, 57, 43, 3, 12, 86, 65, 45, 46, 83, 114, 43, 6, 58, 53, 24, 24, 101, 88, 14, 50, 70, 26, 98, 35, 69, 76, 73, 100, 104, 35, 104, 44, 73, 13, 26, 49, 25, 76, 11, 38]
  pts.getD t.val 0

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem samples : ∀ t : Fin 110, ∀ b : Bool,
   sample wires t b = deepBank 14699973487531969536 13835269164735971328 (test t b) ∧ target (test t b) = !b := by decide +kernel

theorem suffix (rest : List Gate) (o : Nat) (hs : ∀ g ∈ rest, Supported g) (hlen : rest.length ≤ 7)
   (hr : ∀ x : Fin 128, (run rest (deepBank 14699973487531969536 13835269164735971328 x)).getD o false = target x) :
   attainable 7 wires := by
 obtain ⟨cs,hl,hv,he⟩ := fixed_slots 6 10 o rest hs hlen
 refine ⟨cs,16,hl,hv,?_⟩
 intro t
 have h (b : Bool) : (runChoices cs (sample wires t b)).getD 16 false = !b := by
   rw [(samples t b).1, he]
   · exact (hr _).trans (samples t b).2
   · simp [deepBank, otherInputs]
 exact ⟨h false, h true⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_0 : ¬ attainable 6 n1_0 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_1 : ¬ attainable 6 n1_1 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r0_wires : ¬ attainable 7 wires := by
  exact stepCover [n1_0, n1_1] (by decide +kernel) (rejectCons r1_n1_0 (rejectCons r1_n1_1 (rejectNil 6)))

end Depth3

theorem noDepth3 : NoSuffix 14699973487531969536 13835269164735971328 := fun rest o hs hl hr => Depth3.r0_wires (Depth3.suffix rest o hs hl hr)

namespace Reverse3
open CircuitSatBridge FreeSupport
def wires : List Wire := [Depth3.w0, Depth3.w5, Depth3.w8, Depth3.w3, Depth3.w7, Depth3.w2, Depth3.w9, Depth3.w1, Depth3.w0, Depth3.w6]
def test (t : Fin 110) (b : Bool) : Fin 128 :=
  let pts : List (Fin 128) := if b then [74, 74, 84, 74, 21, 82, 37, 74, 84, 37, 82, 82, 82, 21, 21, 21, 74, 37, 21, 37, 37, 21, 84, 82, 74, 82, 84, 37, 84, 84, 42, 41, 42, 41, 41, 41, 41, 41, 42, 42, 42, 42, 37, 74, 82, 21, 84, 42, 41, 41, 42, 82, 82, 4, 2, 21, 82, 82, 84, 42, 32, 21, 64, 4, 41, 37, 8, 2, 32, 74, 21, 21, 1, 16, 42, 1, 37, 84, 74, 74, 84, 64, 84, 41, 8, 16, 37, 10, 80, 68, 66, 80, 68, 5, 34, 34, 18, 34, 18, 68, 20, 36, 17, 33, 72, 9, 9, 18, 17, 68] else [96, 65, 48, 6, 65, 6, 96, 12, 12, 3, 3, 96, 65, 24, 48, 3, 3, 12, 12, 65, 48, 6, 65, 48, 24, 24, 6, 6, 96, 24, 3, 96, 96, 12, 3, 24, 65, 48, 12, 48, 6, 24, 24, 48, 12, 96, 3, 65, 6, 43, 43, 90, 86, 6, 6, 23, 83, 114, 86, 46, 48, 53, 65, 12, 105, 101, 12, 3, 96, 90, 29, 85, 65, 48, 106, 3, 53, 116, 75, 78, 85, 96, 92, 45, 24, 24, 39, 26, 112, 76, 98, 88, 70, 69, 35, 50, 19, 38, 22, 69, 22, 52, 19, 49, 88, 13, 25, 50, 81, 100]
  pts.getD t.val 0
set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem samples : ∀ t : Fin 110, ∀ b : Bool,
   sample wires t b = deepBank 17361376567555522560 17293822573129236480 (test t b) ∧ target (test t b) = !b := by decide +kernel

theorem suffix (rest : List Gate) (o : Nat) (hs : ∀ g ∈ rest, Supported g) (hlen : rest.length ≤ 7)
   (hr : ∀ x : Fin 128, (run rest (deepBank 17361376567555522560 17293822573129236480 x)).getD o false = target x) :
   attainable 7 wires := by
 obtain ⟨cs,hl,hv,he⟩ := fixed_slots 6 10 o rest hs hlen
 refine ⟨cs,16,hl,hv,?_⟩
 intro t
 have h (b : Bool) : (runChoices cs (sample wires t b)).getD 16 false = !b := by
   rw [(samples t b).1, he]
   · exact (hr _).trans (samples t b).2
   · simp [deepBank, otherInputs]
 exact ⟨h false, h true⟩
theorem project (k : Nat) (hs : attainable k wires) : attainable k Depth3.wires := by
  have hm : wires.all (fun w => Depth3.wires.contains w) = true := by decide +kernel
  obtain ⟨cs, o, rfl, _, orient⟩ := hs
  obtain ⟨support, sub, _, det⟩ := bounded_support cs wires.length o
  apply project_suffix sub orient det
  intro i hi
  exact Or.inl (List.contains_iff_mem.mp ((List.all_eq_true.mp hm) _ (List.getElem_mem _)))

end Reverse3

theorem revDepth3 : NoSuffix 17361376567555522560 17293822573129236480 := fun rest o hs hl hr => Depth3.r0_wires (Reverse3.project 7 (Reverse3.suffix rest o hs hl hr))

namespace Depth4
open CircuitSatBridge FreeSupport PEqualNP.CircuitLowerBounds
def w0 := mkSampleWire 0 0 0 0 0 0
def w1 := mkSampleWire 0 285250560 8 1098437885952 285250947 8
def w2 := mkSampleWire 693915109445 62639938600 681755914 1098573808192 53972407687 10665994
def w3 := mkSampleWire 318415184256 826027840534 117443324 1098454728843 550041589131 117440700
def w4 := mkSampleWire 1012330293701 888382528574 799199230 1098590651083 603728745871 128106686
def w5 := mkSampleWire 18457134632 771383797569 139973800 830061223083 769235911835 134726816
def w6 := mkSampleWire 86977910290 25390315200 382296105 268573794896 20956934948 381689864
def w7 := mkSampleWire 722151170052 443560024590 502630791 920976692 426379594352 408226049
def w8 := mkSampleWire 283671658920 1051262927633 574501457 1014948692 295348683364 540553793
def w9 := mkSampleWire 75435087955 1010253512864 822624033 935402927 975071608920 554180385
def wires : List Wire := [w0, w9, w2, w7, w3, w8, w5, w1, w0, w6]
def n1_0 : List Wire := [w3, w5, w6, w7, w8, w2, w9]
def n1_1 : List Wire := [w5, w6, w7, w8, w4, w9]
def test (t : Fin 110) (b : Bool) : Fin 128 :=
  let pts : List (Fin 128) := if b then [82, 82, 42, 82, 41, 74, 37, 82, 42, 37, 74, 74, 74, 41, 41, 41, 82, 37, 41, 37, 37, 41, 42, 74, 82, 74, 42, 37, 42, 42, 84, 21, 84, 21, 21, 21, 21, 21, 84, 84, 84, 84, 37, 82, 74, 41, 42, 84, 21, 41, 84, 8, 21, 1, 41, 84, 37, 32, 42, 82, 8, 41, 2, 2, 21, 74, 42, 64, 84, 1, 41, 37, 74, 74, 37, 4, 64, 74, 42, 82, 42, 4, 16, 21, 16, 82, 32, 80, 10, 34, 66, 10, 34, 33, 68, 68, 72, 68, 72, 34, 40, 36, 9, 5, 18, 17, 17, 72, 9, 34] else [6, 3, 12, 96, 3, 96, 6, 48, 48, 65, 65, 6, 3, 24, 12, 65, 65, 48, 48, 3, 12, 96, 3, 12, 24, 24, 96, 96, 6, 24, 65, 6, 6, 48, 65, 24, 3, 12, 48, 12, 96, 24, 24, 12, 48, 6, 65, 3, 96, 105, 85, 12, 29, 65, 43, 92, 39, 96, 106, 90, 24, 45, 3, 6, 23, 90, 46, 65, 86, 3, 57, 101, 75, 78, 45, 6, 96, 106, 58, 114, 43, 12, 24, 85, 48, 83, 48, 88, 14, 50, 70, 26, 98, 35, 69, 76, 73, 100, 104, 35, 104, 44, 73, 13, 26, 49, 25, 76, 11, 38]
  pts.getD t.val 0

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem samples : ∀ t : Fin 110, ∀ b : Bool,
   sample wires t b = deepBank 14699973487531969536 14699749187159851008 (test t b) ∧ target (test t b) = !b := by decide +kernel

theorem suffix (rest : List Gate) (o : Nat) (hs : ∀ g ∈ rest, Supported g) (hlen : rest.length ≤ 7)
   (hr : ∀ x : Fin 128, (run rest (deepBank 14699973487531969536 14699749187159851008 x)).getD o false = target x) :
   attainable 7 wires := by
 obtain ⟨cs,hl,hv,he⟩ := fixed_slots 6 10 o rest hs hlen
 refine ⟨cs,16,hl,hv,?_⟩
 intro t
 have h (b : Bool) : (runChoices cs (sample wires t b)).getD 16 false = !b := by
   rw [(samples t b).1, he]
   · exact (hr _).trans (samples t b).2
   · simp [deepBank, otherInputs]
 exact ⟨h false, h true⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_0 : ¬ attainable 6 n1_0 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_1 : ¬ attainable 6 n1_1 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r0_wires : ¬ attainable 7 wires := by
  exact stepCover [n1_0, n1_1] (by decide +kernel) (rejectCons r1_n1_0 (rejectCons r1_n1_1 (rejectNil 6)))

end Depth4

theorem noDepth4 : NoSuffix 14699973487531969536 14699749187159851008 := fun rest o hs hl hr => Depth4.r0_wires (Depth4.suffix rest o hs hl hr)

namespace Reverse4
open CircuitSatBridge FreeSupport
def wires : List Wire := [Depth4.w0, Depth4.w5, Depth4.w8, Depth4.w3, Depth4.w7, Depth4.w2, Depth4.w9, Depth4.w1, Depth4.w0, Depth4.w6]
def test (t : Fin 110) (b : Bool) : Fin 128 :=
  let pts : List (Fin 128) := if b then [74, 74, 84, 74, 21, 82, 37, 74, 84, 37, 82, 82, 82, 21, 21, 21, 74, 37, 21, 37, 37, 21, 84, 82, 74, 82, 84, 37, 84, 84, 42, 41, 42, 41, 41, 41, 41, 41, 42, 42, 42, 42, 37, 74, 82, 21, 84, 42, 41, 21, 42, 16, 41, 1, 21, 42, 37, 4, 84, 74, 16, 21, 64, 64, 41, 82, 84, 2, 42, 1, 21, 37, 82, 82, 37, 32, 2, 82, 84, 74, 84, 32, 8, 41, 8, 74, 4, 10, 80, 68, 66, 80, 68, 5, 34, 34, 18, 34, 18, 68, 20, 36, 17, 33, 72, 9, 9, 18, 17, 68] else [96, 65, 48, 6, 65, 6, 96, 12, 12, 3, 3, 96, 65, 24, 48, 3, 3, 12, 12, 65, 48, 6, 65, 48, 24, 24, 6, 6, 96, 24, 3, 96, 96, 12, 3, 24, 65, 48, 12, 48, 6, 24, 24, 48, 12, 96, 3, 65, 6, 23, 43, 48, 57, 3, 85, 58, 101, 6, 86, 90, 24, 53, 65, 96, 105, 90, 116, 3, 106, 65, 29, 39, 83, 114, 53, 96, 6, 86, 92, 78, 85, 48, 24, 43, 12, 75, 12, 26, 112, 76, 98, 88, 70, 69, 35, 50, 19, 38, 22, 69, 22, 52, 19, 49, 88, 13, 25, 50, 81, 100]
  pts.getD t.val 0
set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem samples : ∀ t : Fin 110, ∀ b : Bool,
   sample wires t b = deepBank 17361376567555522560 13889101254044418048 (test t b) ∧ target (test t b) = !b := by decide +kernel

theorem suffix (rest : List Gate) (o : Nat) (hs : ∀ g ∈ rest, Supported g) (hlen : rest.length ≤ 7)
   (hr : ∀ x : Fin 128, (run rest (deepBank 17361376567555522560 13889101254044418048 x)).getD o false = target x) :
   attainable 7 wires := by
 obtain ⟨cs,hl,hv,he⟩ := fixed_slots 6 10 o rest hs hlen
 refine ⟨cs,16,hl,hv,?_⟩
 intro t
 have h (b : Bool) : (runChoices cs (sample wires t b)).getD 16 false = !b := by
   rw [(samples t b).1, he]
   · exact (hr _).trans (samples t b).2
   · simp [deepBank, otherInputs]
 exact ⟨h false, h true⟩
theorem project (k : Nat) (hs : attainable k wires) : attainable k Depth4.wires := by
  have hm : wires.all (fun w => Depth4.wires.contains w) = true := by decide +kernel
  obtain ⟨cs, o, rfl, _, orient⟩ := hs
  obtain ⟨support, sub, _, det⟩ := bounded_support cs wires.length o
  apply project_suffix sub orient det
  intro i hi
  exact Or.inl (List.contains_iff_mem.mp ((List.all_eq_true.mp hm) _ (List.getElem_mem _)))

end Reverse4

theorem revDepth4 : NoSuffix 17361376567555522560 13889101254044418048 := fun rest o hs hl hr => Depth4.r0_wires (Reverse4.project 7 (Reverse4.suffix rest o hs hl hr))

namespace Depth5
open CircuitSatBridge FreeSupport PEqualNP.CircuitLowerBounds
def w0 := mkSampleWire 0 0 0 0 0 0
def w1 := mkSampleWire 0 275985203200 0 1030792151040 275985203459 0
def w2 := mkSampleWire 283690142544 997546061866 4659500 1091328999976 963186319811 399648
def w3 := mkSampleWire 635925742755 698926979664 35790740 64157180763 688004995724 2232212
def w4 := mkSampleWire 86478308489 357809391173 84959873 1035215576196 353513768243 68182017
def w5 := mkSampleWire 370168451033 1079370249839 89619373 1095752425132 1040714884595 68581665
def w6 := mkSampleWire 316775402240 489982528776 954205566 5498215831 77663306804 148897886
def w7 := mkSampleWire 146231537748 61553228962 487451220 8171611479 43294333980 419553876
def w8 := mkSampleWire 687466655782 914353144976 786083856 1030942038176 364052005219 651694080
def w9 := mkSampleWire 42455465992 760551561477 868074691 63221260904 691496540360 856523904
def wires : List Wire := [w0, w3, w4, w9, w6, w2, w7, w1, w0, w8]
def n1_0 : List Wire := [w2, w3, w4, w7, w8, w9, w6]
def n1_1 : List Wire := [w3, w5, w7, w8, w9, w6]
def test (t : Fin 110) (b : Bool) : Fin 128 :=
  let pts : List (Fin 128) := if b then [82, 82, 84, 42, 82, 41, 74, 21, 82, 42, 84, 21, 21, 74, 74, 74, 41, 41, 41, 21, 82, 21, 41, 21, 84, 84, 84, 41, 42, 74, 82, 74, 84, 42, 42, 42, 37, 37, 37, 37, 37, 37, 82, 74, 84, 21, 41, 42, 37, 2, 84, 74, 74, 32, 41, 41, 74, 74, 8, 82, 21, 41, 42, 64, 21, 37, 84, 4, 82, 2, 37, 1, 8, 84, 1, 64, 21, 42, 37, 42, 4, 16, 82, 16, 82, 32, 80, 10, 34, 66, 10, 34, 33, 68, 68, 72, 72, 34, 40, 9, 5, 18, 17, 17, 72, 9, 5, 80, 72, 9] else [6, 3, 65, 12, 96, 3, 96, 6, 48, 48, 6, 48, 65, 65, 6, 3, 24, 12, 65, 24, 65, 3, 48, 12, 48, 12, 96, 96, 3, 12, 24, 24, 24, 96, 6, 24, 6, 65, 48, 3, 12, 96, 12, 48, 3, 96, 6, 65, 24, 6, 85, 90, 106, 96, 43, 105, 75, 78, 24, 86, 85, 57, 106, 65, 23, 39, 92, 6, 90, 3, 101, 3, 12, 86, 65, 96, 29, 58, 53, 43, 12, 24, 114, 48, 83, 48, 88, 14, 50, 70, 26, 98, 35, 69, 76, 73, 104, 35, 104, 73, 13, 26, 49, 25, 76, 11, 69, 81, 88, 25]
  pts.getD t.val 0

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem samples : ∀ t : Fin 110, ∀ b : Bool,
   sample wires t b = deepBank 14757170082422194176 13889101254044418048 (test t b) ∧ target (test t b) = !b := by decide +kernel

theorem suffix (rest : List Gate) (o : Nat) (hs : ∀ g ∈ rest, Supported g) (hlen : rest.length ≤ 7)
   (hr : ∀ x : Fin 128, (run rest (deepBank 14757170082422194176 13889101254044418048 x)).getD o false = target x) :
   attainable 7 wires := by
 obtain ⟨cs,hl,hv,he⟩ := fixed_slots 6 10 o rest hs hlen
 refine ⟨cs,16,hl,hv,?_⟩
 intro t
 have h (b : Bool) : (runChoices cs (sample wires t b)).getD 16 false = !b := by
   rw [(samples t b).1, he]
   · exact (hr _).trans (samples t b).2
   · simp [deepBank, otherInputs]
 exact ⟨h false, h true⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_0 : ¬ attainable 6 n1_0 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_1 : ¬ attainable 6 n1_1 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r0_wires : ¬ attainable 7 wires := by
  exact stepCover [n1_0, n1_1] (by decide +kernel) (rejectCons r1_n1_0 (rejectCons r1_n1_1 (rejectNil 6)))

end Depth5

theorem noDepth5 : NoSuffix 14757170082422194176 13889101254044418048 := fun rest o hs hl hr => Depth5.r0_wires (Depth5.suffix rest o hs hl hr)

namespace Reverse5
open CircuitSatBridge FreeSupport
def wires : List Wire := [Depth5.w0, Depth5.w7, Depth5.w2, Depth5.w6, Depth5.w9, Depth5.w4, Depth5.w3, Depth5.w1, Depth5.w0, Depth5.w8]
def test (t : Fin 110) (b : Bool) : Fin 128 :=
  let pts : List (Fin 128) := if b then [74, 74, 42, 84, 74, 21, 82, 41, 74, 84, 42, 41, 41, 82, 82, 82, 21, 21, 21, 41, 74, 41, 21, 41, 42, 42, 42, 21, 84, 82, 74, 82, 42, 84, 84, 84, 37, 37, 37, 37, 37, 37, 74, 82, 42, 41, 21, 84, 37, 64, 42, 82, 82, 4, 21, 21, 82, 82, 16, 74, 41, 21, 84, 2, 41, 37, 42, 32, 74, 64, 37, 1, 16, 42, 1, 2, 41, 84, 37, 84, 32, 8, 74, 8, 74, 4, 10, 80, 68, 66, 80, 68, 5, 34, 34, 18, 18, 68, 20, 17, 33, 72, 9, 9, 18, 17, 33, 10, 18, 17] else [96, 65, 3, 48, 6, 65, 6, 96, 12, 12, 96, 12, 3, 3, 96, 65, 24, 48, 3, 24, 3, 65, 12, 48, 12, 48, 6, 6, 65, 48, 24, 24, 24, 6, 96, 24, 96, 3, 12, 65, 48, 6, 48, 12, 65, 6, 96, 3, 24, 96, 43, 90, 86, 6, 85, 23, 83, 114, 24, 106, 43, 29, 86, 3, 105, 101, 58, 96, 90, 65, 39, 65, 48, 106, 3, 6, 57, 92, 45, 85, 48, 24, 78, 12, 75, 12, 26, 112, 76, 98, 88, 70, 69, 35, 50, 19, 22, 69, 22, 19, 49, 88, 13, 25, 50, 81, 35, 11, 26, 25]
  pts.getD t.val 0
set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem samples : ∀ t : Fin 110, ∀ b : Bool,
   sample wires t b = deepBank 14757170082422194176 14699749187159851008 (test t b) ∧ target (test t b) = !b := by decide +kernel

theorem suffix (rest : List Gate) (o : Nat) (hs : ∀ g ∈ rest, Supported g) (hlen : rest.length ≤ 7)
   (hr : ∀ x : Fin 128, (run rest (deepBank 14757170082422194176 14699749187159851008 x)).getD o false = target x) :
   attainable 7 wires := by
 obtain ⟨cs,hl,hv,he⟩ := fixed_slots 6 10 o rest hs hlen
 refine ⟨cs,16,hl,hv,?_⟩
 intro t
 have h (b : Bool) : (runChoices cs (sample wires t b)).getD 16 false = !b := by
   rw [(samples t b).1, he]
   · exact (hr _).trans (samples t b).2
   · simp [deepBank, otherInputs]
 exact ⟨h false, h true⟩
theorem project (k : Nat) (hs : attainable k wires) : attainable k Depth5.wires := by
  have hm : wires.all (fun w => Depth5.wires.contains w) = true := by decide +kernel
  obtain ⟨cs, o, rfl, _, orient⟩ := hs
  obtain ⟨support, sub, _, det⟩ := bounded_support cs wires.length o
  apply project_suffix sub orient det
  intro i hi
  exact Or.inl (List.contains_iff_mem.mp ((List.all_eq_true.mp hm) _ (List.getElem_mem _)))

end Reverse5

theorem revDepth5 : NoSuffix 14757170082422194176 14699749187159851008 := fun rest o hs hl hr => Depth5.r0_wires (Reverse5.project 7 (Reverse5.suffix rest o hs hl hr))

namespace Depth6
open CircuitSatBridge FreeSupport PEqualNP.CircuitLowerBounds
def w0 := mkSampleWire 0 0 0 0 0 0
def w1 := mkSampleWire 1030792151040 259 0 0 0 0
def w2 := mkSampleWire 39024134537 520617793092 325749544 155682109828 378612750129 21138176
def w3 := mkSampleWire 1069816285577 520617793351 325749544 155682109828 378612750129 21138176
def w4 := mkSampleWire 36528392611 769216011344 103817465 874027124315 150605449358 102768761
def w5 := mkSampleWire 1067320543651 769216011603 103817465 874027124315 150605449358 102768761
def w6 := mkSampleWire 2170216486 835080074896 215426433 224544977312 826481325920 139919488
def w7 := mkSampleWire 1032962367526 835080075155 215426433 224544977312 826481325920 139919488
def w8 := mkSampleWire 1035456479240 598890072327 270259720 668950561896 563993462986 270095368
def w9 := mkSampleWire 27525125712 858546785832 824506582 132131857704 856311220162 287367380
def w10 := mkSampleWire 1058317276752 858546786091 824506582 132131857704 856311220162 287367380
def w11 := mkSampleWire 27382046804 295612377248 751394656 829869492823 2447280157 612900640
def w12 := mkSampleWire 1058174197844 295612377507 751394656 829869492823 2447280157 612900640
def w13 := mkSampleWire 1030936860160 123507467 730071062 413328759447 123506741 713293826
def w14 := mkSampleWire 1035601188360 599013579535 1000330782 1082279321343 564116969727 983389194
def wires : List Wire := [w0, w4, w2, w8, w13, w9, w11, w1, w0, w6]
def n1_0 : List Wire := [w4, w6, w2, w11, w9, w14]
def n1_1 : List Wire := [w4, w6, w8, w2, w13, w11, w9]
def n1_2 : List Wire := [w4, w6, w8, w2, w13, w11, w10]
def n1_3 : List Wire := [w4, w6, w8, w2, w13, w12, w9]
def n1_4 : List Wire := [w4, w6, w8, w3, w13, w11, w9]
def n1_5 : List Wire := [w4, w7, w8, w2, w13, w11, w9]
def n1_6 : List Wire := [w5, w6, w8, w2, w13, w11, w9]
def test (t : Fin 110) (b : Bool) : Fin 128 :=
  let pts : List (Fin 128) := if b then [82, 82, 84, 42, 82, 41, 74, 21, 37, 82, 42, 84, 21, 37, 21, 74, 74, 74, 41, 41, 82, 37, 21, 41, 37, 37, 21, 84, 84, 84, 41, 42, 74, 42, 37, 42, 41, 21, 82, 74, 84, 42, 82, 74, 84, 21, 41, 42, 37, 37, 37, 74, 21, 1, 42, 82, 8, 64, 84, 82, 84, 41, 82, 74, 84, 21, 21, 1, 74, 37, 41, 64, 42, 42, 32, 4, 4, 2, 37, 41, 2, 16, 32, 10, 34, 66, 34, 33, 68, 68, 72, 68, 72, 34, 40, 36, 9, 5, 17, 72, 9, 34, 5, 80, 36, 18, 66, 17, 40, 80] else [6, 3, 65, 12, 96, 3, 96, 6, 6, 48, 48, 6, 48, 65, 65, 65, 6, 3, 12, 65, 65, 48, 3, 48, 3, 12, 12, 48, 12, 96, 96, 3, 12, 96, 96, 6, 24, 24, 24, 24, 24, 24, 12, 48, 3, 96, 6, 65, 24, 53, 39, 106, 23, 65, 106, 83, 12, 65, 85, 86, 86, 45, 114, 75, 116, 85, 53, 3, 78, 45, 105, 96, 46, 43, 96, 12, 6, 6, 101, 43, 3, 48, 48, 14, 50, 70, 98, 35, 69, 76, 73, 100, 104, 35, 104, 44, 73, 13, 49, 76, 11, 38, 69, 81, 52, 22, 67, 81, 44, 112]
  pts.getD t.val 0

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem samples : ∀ t : Fin 110, ∀ b : Bool,
   sample wires t b = deepBank 17294086455919964160 13835269164735971328 (test t b) ∧ target (test t b) = !b := by decide +kernel

theorem suffix (rest : List Gate) (o : Nat) (hs : ∀ g ∈ rest, Supported g) (hlen : rest.length ≤ 7)
   (hr : ∀ x : Fin 128, (run rest (deepBank 17294086455919964160 13835269164735971328 x)).getD o false = target x) :
   attainable 7 wires := by
 obtain ⟨cs,hl,hv,he⟩ := fixed_slots 6 10 o rest hs hlen
 refine ⟨cs,16,hl,hv,?_⟩
 intro t
 have h (b : Bool) : (runChoices cs (sample wires t b)).getD 16 false = !b := by
   rw [(samples t b).1, he]
   · exact (hr _).trans (samples t b).2
   · simp [deepBank, otherInputs]
 exact ⟨h false, h true⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_0 : ¬ attainable 6 n1_0 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_1 : ¬ attainable 6 n1_1 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_2 : ¬ attainable 6 n1_2 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_3 : ¬ attainable 6 n1_3 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_4 : ¬ attainable 6 n1_4 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_5 : ¬ attainable 6 n1_5 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_6 : ¬ attainable 6 n1_6 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r0_wires : ¬ attainable 7 wires := by
  exact stepCover [n1_0, n1_1, n1_2, n1_3, n1_4, n1_5, n1_6] (by decide +kernel) (rejectCons r1_n1_0 (rejectCons r1_n1_1 (rejectCons r1_n1_2 (rejectCons r1_n1_3 (rejectCons r1_n1_4 (rejectCons r1_n1_5 (rejectCons r1_n1_6 (rejectNil 6))))))))

end Depth6

theorem noDepth6 : NoSuffix 17294086455919964160 13835269164735971328 := fun rest o hs hl hr => Depth6.r0_wires (Depth6.suffix rest o hs hl hr)

namespace Reverse6
open CircuitSatBridge FreeSupport
def wires : List Wire := [Depth6.w0, Depth6.w11, Depth6.w9, Depth6.w13, Depth6.w8, Depth6.w2, Depth6.w4, Depth6.w1, Depth6.w0, Depth6.w6]
def test (t : Fin 110) (b : Bool) : Fin 128 :=
  let pts : List (Fin 128) := if b then [74, 74, 42, 84, 74, 21, 82, 41, 37, 74, 84, 42, 41, 37, 41, 82, 82, 82, 21, 21, 74, 37, 41, 21, 37, 37, 41, 42, 42, 42, 21, 84, 82, 84, 37, 84, 21, 41, 74, 82, 42, 84, 74, 82, 42, 41, 21, 84, 37, 37, 37, 82, 41, 1, 84, 74, 16, 2, 42, 74, 42, 21, 74, 82, 42, 41, 41, 1, 82, 37, 21, 2, 84, 84, 4, 32, 32, 64, 37, 21, 64, 8, 4, 80, 68, 66, 68, 5, 34, 34, 18, 34, 18, 68, 20, 36, 17, 33, 9, 18, 17, 68, 33, 10, 36, 72, 66, 9, 20, 10] else [96, 65, 3, 48, 6, 65, 6, 96, 96, 12, 12, 96, 12, 3, 3, 3, 96, 65, 48, 3, 3, 12, 65, 12, 65, 48, 48, 12, 48, 6, 6, 65, 48, 6, 6, 96, 24, 24, 24, 24, 24, 24, 48, 12, 65, 6, 96, 3, 24, 45, 101, 86, 105, 3, 86, 75, 48, 3, 43, 106, 106, 53, 78, 83, 46, 43, 45, 65, 114, 53, 23, 6, 116, 85, 6, 48, 96, 96, 39, 85, 65, 12, 12, 112, 76, 98, 70, 69, 35, 50, 19, 38, 22, 69, 22, 52, 19, 49, 13, 50, 81, 100, 35, 11, 44, 104, 67, 11, 52, 14]
  pts.getD t.val 0
set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem samples : ∀ t : Fin 110, ∀ b : Bool,
   sample wires t b = deepBank 17294086455919964160 17293822573129236480 (test t b) ∧ target (test t b) = !b := by decide +kernel

theorem suffix (rest : List Gate) (o : Nat) (hs : ∀ g ∈ rest, Supported g) (hlen : rest.length ≤ 7)
   (hr : ∀ x : Fin 128, (run rest (deepBank 17294086455919964160 17293822573129236480 x)).getD o false = target x) :
   attainable 7 wires := by
 obtain ⟨cs,hl,hv,he⟩ := fixed_slots 6 10 o rest hs hlen
 refine ⟨cs,16,hl,hv,?_⟩
 intro t
 have h (b : Bool) : (runChoices cs (sample wires t b)).getD 16 false = !b := by
   rw [(samples t b).1, he]
   · exact (hr _).trans (samples t b).2
   · simp [deepBank, otherInputs]
 exact ⟨h false, h true⟩
theorem project (k : Nat) (hs : attainable k wires) : attainable k Depth6.wires := by
  have hm : wires.all (fun w => Depth6.wires.contains w) = true := by decide +kernel
  obtain ⟨cs, o, rfl, _, orient⟩ := hs
  obtain ⟨support, sub, _, det⟩ := bounded_support cs wires.length o
  apply project_suffix sub orient det
  intro i hi
  exact Or.inl (List.contains_iff_mem.mp ((List.all_eq_true.mp hm) _ (List.getElem_mem _)))

end Reverse6

theorem revDepth6 : NoSuffix 17294086455919964160 17293822573129236480 := fun rest o hs hl hr => Depth6.r0_wires (Reverse6.project 7 (Reverse6.suffix rest o hs hl hr))

namespace Depth7
open CircuitSatBridge FreeSupport PEqualNP.CircuitLowerBounds
def w0 := mkSampleWire 0 0 0 0 0 0
def w1 := mkSampleWire 71940702464 321 0 0 0 0
def w2 := mkSampleWire 793496781056 331 0 0 0 0
def w3 := mkSampleWire 722227171397 18325438506 17834116 0 0 0
def w4 := mkSampleWire 794167873861 18325438827 17834116 0 0 0
def w5 := mkSampleWire 8623579264 73014455812 136317984 0 0 0
def w6 := mkSampleWire 80564281728 73014456133 136317984 0 0 0
def w7 := mkSampleWire 802120360320 73014456143 136317984 0 0 0
def w8 := mkSampleWire 8898307720 116285255188 174890080 0 0 0
def w9 := mkSampleWire 80839010184 116285255509 174890080 0 0 0
def w10 := mkSampleWire 802395088776 116285255519 174890080 0 0 0
def w11 := mkSampleWire 722319446135 843638689962 898655124 0 0 0
def w12 := mkSampleWire 794260148599 843638690283 898655124 0 0 0
def w13 := mkSampleWire 296445446194 964908014208 914614043 180466641987 826789354361 108035
def w14 := mkSampleWire 368386148658 964908014529 914614043 180466641987 826789354361 108035
def w15 := mkSampleWire 1089942227250 964908014539 914614043 180466641987 826789354361 108035
def w16 := mkSampleWire 1018672617591 983228734122 932439967 180466641987 826789354361 108035
def w17 := mkSampleWire 1090613320055 983228734443 932439967 180466641987 826789354361 108035
def w18 := mkSampleWire 0 88118201856 135266464 223351230528 70938332307 1048576
def w19 := mkSampleWire 721556078592 88118201866 135266464 223351230528 70938332307 1048576
def w20 := mkSampleWire 71940702464 88118202177 135266464 223351230528 70938332307 1048576
def w21 := mkSampleWire 793496781056 88118202187 135266464 223351230528 70938332307 1048576
def w22 := mkSampleWire 8623579264 92413177348 137366688 223351230528 70938332307 1048576
def w23 := mkSampleWire 722227171397 89192468010 152051876 223351230528 70938332307 1048576
def w24 := mkSampleWire 0 259917155840 139526308 223351230528 242737024147 1048580
def w25 := mkSampleWire 0 637874048512 135267514 223351230528 620694146195 1049602
def w26 := mkSampleWire 80564281728 622774455109 1051824 137447620672 624921937937 1051794
def w27 := mkSampleWire 722227171397 260991421994 156311716 257780314177 243811553171 22093860
def w28 := mkSampleWire 794167873861 260991422315 156311716 257780314177 243811553171 22093860
def w29 := mkSampleWire 1018672617591 1086307950250 1070852031 266370251843 1068448440315 22128167
def w30 := mkSampleWire 1090613320055 1086307950571 1070852031 266370251843 1068448440315 22128167
def w31 := mkSampleWire 80564281728 642169024325 137366714 777687224772 642169023635 137366682
def w32 := mkSampleWire 802120360320 642169024335 137366714 777687224772 642169023635 137366682
def w33 := mkSampleWire 296627899912 200239719440 183472207 641851298708 198038496390 145100812
def w34 := mkSampleWire 1090124680968 200239719771 183472207 641851298708 198038496390 145100812
def w35 := mkSampleWire 305251479176 273254166036 183475311 641851298708 198038496390 145100812
def w36 := mkSampleWire 377192181640 273254166357 183475311 641851298708 198038496390 145100812
def w37 := mkSampleWire 377192181640 823014174549 184524031 779298919380 822960434327 146152606
def w38 := mkSampleWire 802791453125 815042244463 158411966 812116308421 815042244499 158411966
def w39 := mkSampleWire 1090613320055 982688961003 882057631 779298919380 1098921524375 481770911
def w40 := mkSampleWire 305251479176 255587716628 174822443 266370251843 1081367027707 528201263
def w41 := mkSampleWire 793496781056 275834224971 603980032 278805381688 956301316 536871168
def w42 := mkSampleWire 794260148599 843923911147 898919380 833141375932 18144600068 545540560
def w43 := mkSampleWire 8898307720 116822666772 191684192 320212708395 590103400 591970912
def w44 := mkSampleWire 80839010184 116822667093 191684192 320212708395 590103400 591970912
def w45 := mkSampleWire 802395088776 116822667103 191684192 320212708395 590103400 591970912
def w46 := mkSampleWire 731125479117 274734083646 192806628 543563938923 244400869371 593093220
def w47 := mkSampleWire 793496781056 275836322123 604639489 287395319354 275836321900 604639489
def w48 := mkSampleWire 1089942227250 965193227211 915142427 459272023675 827745655677 604747523
def w49 := mkSampleWire 793496781056 363954523979 739905953 510746549882 346774654207 605688065
def w50 := mkSampleWire 794167873861 536827744107 760951205 545175633531 519647875071 626733349
def w51 := mkSampleWire 802395088776 391834791775 795795297 321824403003 275870663532 659215201
def w52 := mkSampleWire 802883727863 919085907951 1035235326 1056492606460 643133713559 682905050
def w53 := mkSampleWire 802120360320 918005346127 742006203 1065082544126 918005345535 742006171
def w54 := mkSampleWire 802883727863 899271908335 890269616 457660329067 901473131385 928641011
def w55 := mkSampleWire 1018947346047 457342603450 936375109 321824403003 457342604140 936375141
def w56 := mkSampleWire 377284456378 838520205781 917430107 841731313598 855700074604 1051647963
def w57 := mkSampleWire 1099511627775 1011393425919 938475359 876160397247 1028573295468 1072693247
def w58 := mkSampleWire 803066181581 134603613567 159127780 919044985788 272722273414 1073633788
def wires : List Wire := [w0, w27, w47, w31, w43, w33, w13, w38, w2, w42]
def n1_0 : List Wire := [w1, w31, w27, w33, w43, w42, w13]
def n1_1 : List Wire := [w2, w3, w31, w33, w43, w42, w13]
def n1_2 : List Wire := [w2, w5, w27, w33, w43, w42, w13]
def n1_3 : List Wire := [w2, w18, w33, w43, w42, w13]
def n1_4 : List Wire := [w2, w27, w33, w37, w43, w42, w13]
def n1_5 : List Wire := [w2, w31, w27, w33, w43, w42, w13]
def n1_6 : List Wire := [w2, w31, w27, w33, w43, w42, w15]
def n1_7 : List Wire := [w2, w31, w27, w33, w45, w42, w13]
def n1_8 : List Wire := [w2, w31, w27, w34, w43, w42, w13]
def n1_9 : List Wire := [w2, w31, w28, w33, w43, w42, w13]
def n1_10 : List Wire := [w2, w31, w33, w43, w42, w13, w29]
def n1_11 : List Wire := [w2, w32, w27, w33, w43, w42, w13]
def n1_12 : List Wire := [w3, w31, w33, w43, w42, w13]
def n1_13 : List Wire := [w3, w31, w33, w43, w47, w42, w13]
def n1_14 : List Wire := [w5, w27, w33, w43, w42, w13]
def n1_15 : List Wire := [w18, w27, w33, w43, w42, w13]
def n1_16 : List Wire := [w18, w31, w33, w43, w42, w13]
def n1_17 : List Wire := [w18, w33, w43, w47, w42, w13]
def n1_18 : List Wire := [w18, w38, w33, w43, w42, w13]
def n1_19 : List Wire := [w27, w33, w37, w43, w42, w13]
def n1_20 : List Wire := [w27, w33, w43, w42, w13, w52]
def n1_21 : List Wire := [w27, w33, w43, w42, w13, w55]
def n1_22 : List Wire := [w27, w33, w43, w53, w42, w13]
def n1_23 : List Wire := [w31, w27, w28, w33, w43, w42, w13]
def n1_24 : List Wire := [w31, w27, w33, w39, w42, w13]
def n1_25 : List Wire := [w31, w27, w33, w43, w41, w42, w13]
def n1_26 : List Wire := [w31, w27, w33, w43, w42, w13]
def n1_27 : List Wire := [w31, w27, w33, w43, w42, w13, w15]
def n1_28 : List Wire := [w31, w27, w33, w43, w42, w13, w48]
def n2_31 : List Wire := [w31, w27, w33, w43, w42, w15]
def n1_30 : List Wire := [w31, w27, w33, w43, w45, w42, w13]
def n1_31 : List Wire := [w31, w27, w33, w43, w47, w42, w13]
def n1_32 : List Wire := [w31, w27, w33, w43, w47, w42, w15]
def n1_33 : List Wire := [w31, w27, w33, w43, w50, w42, w13]
def n1_34 : List Wire := [w31, w27, w33, w43, w51, w42, w13]
def n1_35 : List Wire := [w31, w27, w33, w43, w54, w42, w13]
def n2_33 : List Wire := [w31, w27, w33, w45, w42, w13]
def n1_37 : List Wire := [w31, w27, w33, w45, w47, w42, w13]
def n1_38 : List Wire := [w31, w27, w34, w43, w47, w42, w13]
def n1_39 : List Wire := [w31, w27, w38, w33, w43, w42, w15]
def n1_40 : List Wire := [w31, w27, w38, w33, w45, w42, w13]
def n1_41 : List Wire := [w31, w27, w40, w33, w43, w13]
def n1_42 : List Wire := [w31, w27, w43, w54, w42, w13]
def n1_43 : List Wire := [w31, w27, w58, w33, w43, w42]
def n2_37 : List Wire := [w31, w28, w33, w43, w42, w13]
def n1_45 : List Wire := [w31, w28, w33, w43, w47, w42, w13]
def n1_46 : List Wire := [w31, w28, w38, w33, w43, w42, w13]
def n1_47 : List Wire := [w31, w33, w43, w42, w13, w29]
def n1_48 : List Wire := [w31, w33, w43, w42, w13, w56]
def n1_49 : List Wire := [w31, w33, w43, w46, w42, w13]
def n1_50 : List Wire := [w31, w33, w43, w47, w42, w13, w29]
def n1_51 : List Wire := [w31, w33, w43, w50, w42, w13]
def n1_52 : List Wire := [w31, w38, w33, w43, w50, w42, w13]
def n1_53 : List Wire := [w32, w27, w33, w43, w42, w13]
def n1_54 : List Wire := [w32, w27, w33, w43, w47, w42, w13]
def n2_0 : List Wire := [w2, w27, w8, w33, w42, w13]
def n2_1 : List Wire := [w2, w27, w35, w43, w42, w13]
def n2_2 : List Wire := [w2, w31, w33, w43, w11, w13]
def n2_3 : List Wire := [w2, w31, w33, w43, w42, w16]
def n2_4 : List Wire := [w3, w31, w33, w43, w42, w15]
def n2_5 : List Wire := [w3, w31, w33, w45, w42, w13]
def n2_6 : List Wire := [w4, w31, w33, w43, w42, w13]
def n2_7 : List Wire := [w5, w27, w33, w43, w42, w15]
def n2_8 : List Wire := [w5, w28, w33, w43, w42, w13]
def n2_9 : List Wire := [w6, w27, w33, w43, w42, w13]
def n2_10 : List Wire := [w6, w27, w33, w45, w42, w13]
def n2_11 : List Wire := [w7, w27, w33, w43, w42, w13]
def n2_12 : List Wire := [w18, w33, w39, w42, w13]
def n2_13 : List Wire := [w18, w33, w43, w42, w13]
def n2_14 : List Wire := [w18, w33, w43, w42, w15]
def n2_15 : List Wire := [w18, w40, w33, w43, w13]
def n2_16 : List Wire := [w18, w43, w54, w42, w13]
def n2_17 : List Wire := [w18, w58, w33, w43, w42]
def n2_18 : List Wire := [w19, w33, w43, w42, w13]
def n2_19 : List Wire := [w20, w33, w43, w42, w13]
def n2_20 : List Wire := [w21, w33, w43, w42, w13]
def n2_21 : List Wire := [w22, w33, w43, w42, w13]
def n2_22 : List Wire := [w23, w33, w43, w42, w13]
def n2_23 : List Wire := [w24, w33, w43, w42, w13]
def n2_24 : List Wire := [w25, w33, w43, w42, w13]
def n2_25 : List Wire := [w26, w27, w33, w43, w42, w13]
def n2_26 : List Wire := [w27, w33, w37, w43, w42, w15]
def n2_27 : List Wire := [w27, w33, w37, w45, w42, w13]
def n2_28 : List Wire := [w27, w35, w43, w42, w13]
def n2_29 : List Wire := [w28, w33, w37, w43, w42, w13]
def n2_30 : List Wire := [w31, w27, w33, w43, w42, w14]
def n2_32 : List Wire := [w31, w27, w33, w44, w42, w13]
def n2_34 : List Wire := [w31, w27, w33, w45, w42, w15]
def n2_35 : List Wire := [w31, w27, w34, w43, w42, w15]
def n2_36 : List Wire := [w31, w27, w34, w45, w42, w13]
def n2_38 : List Wire := [w31, w28, w33, w43, w42, w15]
def n2_39 : List Wire := [w31, w28, w33, w45, w42, w13]
def n2_40 : List Wire := [w31, w28, w34, w43, w42, w13]
def n2_41 : List Wire := [w31, w33, w43, w11, w13]
def n2_42 : List Wire := [w31, w33, w43, w42, w13, w30]
def n2_43 : List Wire := [w31, w33, w43, w42, w15, w29]
def n2_44 : List Wire := [w31, w33, w43, w42, w15, w30]
def n2_45 : List Wire := [w31, w33, w43, w42, w16]
def n2_46 : List Wire := [w31, w33, w43, w42, w48, w29]
def n2_47 : List Wire := [w31, w33, w43, w47, w11, w13]
def n2_48 : List Wire := [w31, w33, w43, w47, w42, w16]
def n2_49 : List Wire := [w31, w33, w45, w42, w13, w29]
def n2_50 : List Wire := [w32, w27, w33, w43, w42, w15]
def n2_51 : List Wire := [w32, w27, w33, w45, w42, w13]
def n2_52 : List Wire := [w32, w28, w33, w43, w42, w13]
def n2_53 : List Wire := [w33, w43, w42, w13, w57]
def n2_54 : List Wire := [w33, w43, w49, w42, w13]
def n3_0 : List Wire := [w27, w8, w33, w42, w15]
def n3_1 : List Wire := [w27, w9, w33, w42, w13]
def n3_2 : List Wire := [w27, w10, w33, w42, w13]
def n3_3 : List Wire := [w27, w35, w43, w42, w15]
def n3_4 : List Wire := [w27, w36, w45, w42, w13]
def n3_5 : List Wire := [w28, w8, w33, w42, w13]
def n3_6 : List Wire := [w28, w35, w43, w42, w13]
def n3_7 : List Wire := [w31, w33, w43, w12, w13]
def n3_8 : List Wire := [w31, w33, w43, w12, w15]
def n3_9 : List Wire := [w31, w33, w43, w42, w17]
def n3_10 : List Wire := [w31, w33, w45, w11, w13]
def n3_11 : List Wire := [w31, w33, w45, w42, w16]
def test (t : Fin 110) (b : Bool) : Fin 128 :=
  let pts : List (Fin 128) := if b then [82, 84, 41, 21, 37, 21, 74, 41, 41, 37, 84, 84, 42, 82, 74, 37, 42, 82, 74, 21, 37, 82, 42, 74, 41, 21, 82, 21, 41, 37, 37, 21, 41, 84, 42, 82, 42, 74, 21, 41, 74, 42, 37, 84, 74, 84, 84, 42, 82, 82, 42, 74, 64, 41, 84, 41, 42, 32, 82, 82, 64, 84, 74, 1, 21, 16, 42, 37, 37, 21, 2, 74, 8, 32, 41, 34, 10, 34, 68, 72, 68, 72, 34, 40, 9, 18, 17, 9, 5, 80, 72, 9, 36, 66, 17, 80, 66, 36, 33, 20, 10, 40, 18, 33, 18, 16, 4, 40, 0, 21] else [3, 65, 3, 48, 65, 65, 3, 24, 12, 48, 48, 96, 3, 24, 24, 96, 24, 96, 96, 6, 6, 48, 48, 65, 65, 24, 65, 3, 48, 3, 12, 12, 96, 24, 96, 6, 12, 6, 96, 6, 12, 6, 24, 6, 48, 3, 12, 65, 12, 90, 58, 90, 65, 57, 85, 105, 106, 96, 114, 83, 96, 116, 75, 65, 53, 48, 43, 101, 53, 85, 3, 106, 24, 48, 43, 50, 26, 98, 69, 73, 100, 104, 35, 104, 73, 26, 49, 11, 69, 81, 88, 25, 52, 67, 81, 112, 98, 100, 49, 52, 11, 56, 50, 97, 19, 112, 69, 58, 65, 69]
  pts.getD t.val 0

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem samples : ∀ t : Fin 110, ∀ b : Bool,
   sample wires t b = deepBank 18085043209519168250 14468034567615334600 (test t b) ∧ target (test t b) = !b := by decide +kernel

theorem suffix (rest : List Gate) (o : Nat) (hs : ∀ g ∈ rest, Supported g) (hlen : rest.length ≤ 7)
   (hr : ∀ x : Fin 128, (run rest (deepBank 18085043209519168250 14468034567615334600 x)).getD o false = target x) :
   attainable 7 wires := by
 obtain ⟨cs,hl,hv,he⟩ := fixed_slots 6 10 o rest hs hlen
 refine ⟨cs,16,hl,hv,?_⟩
 intro t
 have h (b : Bool) : (runChoices cs (sample wires t b)).getD 16 false = !b := by
   rw [(samples t b).1, he]
   · exact (hr _).trans (samples t b).2
   · simp [deepBank, otherInputs]
 exact ⟨h false, h true⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_0 : ¬ attainable 4 n3_0 := by
  exact stepCover [] (by decide +kernel) (rejectNil 3)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_1 : ¬ attainable 4 n3_1 := by
  exact stepCover [] (by decide +kernel) (rejectNil 3)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_2 : ¬ attainable 4 n3_2 := by
  exact stepCover [] (by decide +kernel) (rejectNil 3)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_3 : ¬ attainable 4 n3_3 := by
  exact stepCover [] (by decide +kernel) (rejectNil 3)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_4 : ¬ attainable 4 n3_4 := by
  exact stepCover [] (by decide +kernel) (rejectNil 3)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_5 : ¬ attainable 4 n3_5 := by
  exact stepCover [] (by decide +kernel) (rejectNil 3)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_6 : ¬ attainable 4 n3_6 := by
  exact stepCover [] (by decide +kernel) (rejectNil 3)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_7 : ¬ attainable 4 n3_7 := by
  exact stepCover [] (by decide +kernel) (rejectNil 3)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_8 : ¬ attainable 4 n3_8 := by
  exact stepCover [] (by decide +kernel) (rejectNil 3)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_9 : ¬ attainable 4 n3_9 := by
  exact stepCover [] (by decide +kernel) (rejectNil 3)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_10 : ¬ attainable 4 n3_10 := by
  exact stepCover [] (by decide +kernel) (rejectNil 3)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_11 : ¬ attainable 4 n3_11 := by
  exact stepCover [] (by decide +kernel) (rejectNil 3)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_0 : ¬ attainable 5 n2_0 := by
  exact stepCover [n3_0, n3_2, n3_5] (by decide +kernel) (rejectCons r3_n3_0 (rejectCons r3_n3_2 (rejectCons r3_n3_5 (rejectNil 4))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_1 : ¬ attainable 5 n2_1 := by
  exact stepCover [n3_3, n3_6] (by decide +kernel) (rejectCons r3_n3_3 (rejectCons r3_n3_6 (rejectNil 4)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_2 : ¬ attainable 5 n2_2 := by
  exact stepCover [n3_7, n3_10] (by decide +kernel) (rejectCons r3_n3_7 (rejectCons r3_n3_10 (rejectNil 4)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_3 : ¬ attainable 5 n2_3 := by
  exact stepCover [n3_9, n3_11] (by decide +kernel) (rejectCons r3_n3_9 (rejectCons r3_n3_11 (rejectNil 4)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_4 : ¬ attainable 5 n2_4 := by
  exact stepCover [n3_9] (by decide +kernel) (rejectCons r3_n3_9 (rejectNil 4))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_5 : ¬ attainable 5 n2_5 := by
  exact stepCover [n3_11] (by decide +kernel) (rejectCons r3_n3_11 (rejectNil 4))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_6 : ¬ attainable 5 n2_6 := by
  exact stepCover [n3_9] (by decide +kernel) (rejectCons r3_n3_9 (rejectNil 4))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_7 : ¬ attainable 5 n2_7 := by
  exact stepCover [n3_3] (by decide +kernel) (rejectCons r3_n3_3 (rejectNil 4))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_8 : ¬ attainable 5 n2_8 := by
  exact stepCover [n3_6] (by decide +kernel) (rejectCons r3_n3_6 (rejectNil 4))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_9 : ¬ attainable 5 n2_9 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_10 : ¬ attainable 5 n2_10 := by
  exact stepCover [n3_4] (by decide +kernel) (rejectCons r3_n3_4 (rejectNil 4))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_11 : ¬ attainable 5 n2_11 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_12 : ¬ attainable 5 n2_12 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_13 : ¬ attainable 5 n2_13 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_14 : ¬ attainable 5 n2_14 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_15 : ¬ attainable 5 n2_15 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_16 : ¬ attainable 5 n2_16 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_17 : ¬ attainable 5 n2_17 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_18 : ¬ attainable 5 n2_18 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_19 : ¬ attainable 5 n2_19 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_20 : ¬ attainable 5 n2_20 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_21 : ¬ attainable 5 n2_21 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_22 : ¬ attainable 5 n2_22 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_23 : ¬ attainable 5 n2_23 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_24 : ¬ attainable 5 n2_24 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_25 : ¬ attainable 5 n2_25 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_26 : ¬ attainable 5 n2_26 := by
  exact stepCover [n3_0] (by decide +kernel) (rejectCons r3_n3_0 (rejectNil 4))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_27 : ¬ attainable 5 n2_27 := by
  exact stepCover [n3_1] (by decide +kernel) (rejectCons r3_n3_1 (rejectNil 4))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_28 : ¬ attainable 5 n2_28 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_29 : ¬ attainable 5 n2_29 := by
  exact stepCover [n3_5] (by decide +kernel) (rejectCons r3_n3_5 (rejectNil 4))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_30 : ¬ attainable 5 n2_30 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_31 : ¬ attainable 5 n2_31 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_32 : ¬ attainable 5 n2_32 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_33 : ¬ attainable 5 n2_33 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_34 : ¬ attainable 5 n2_34 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_35 : ¬ attainable 5 n2_35 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_36 : ¬ attainable 5 n2_36 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_37 : ¬ attainable 5 n2_37 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_38 : ¬ attainable 5 n2_38 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_39 : ¬ attainable 5 n2_39 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_40 : ¬ attainable 5 n2_40 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_41 : ¬ attainable 5 n2_41 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_42 : ¬ attainable 5 n2_42 := by
  exact stepCover [n3_7] (by decide +kernel) (rejectCons r3_n3_7 (rejectNil 4))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_43 : ¬ attainable 5 n2_43 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_44 : ¬ attainable 5 n2_44 := by
  exact stepCover [n3_8] (by decide +kernel) (rejectCons r3_n3_8 (rejectNil 4))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_45 : ¬ attainable 5 n2_45 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_46 : ¬ attainable 5 n2_46 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_47 : ¬ attainable 5 n2_47 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_48 : ¬ attainable 5 n2_48 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_49 : ¬ attainable 5 n2_49 := by
  exact stepCover [n3_10] (by decide +kernel) (rejectCons r3_n3_10 (rejectNil 4))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_50 : ¬ attainable 5 n2_50 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_51 : ¬ attainable 5 n2_51 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_52 : ¬ attainable 5 n2_52 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_53 : ¬ attainable 5 n2_53 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_54 : ¬ attainable 5 n2_54 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_0 : ¬ attainable 6 n1_0 := by
  exact stepCover [n2_13, n2_30, n2_32, n2_37] (by decide +kernel) (rejectCons r2_n2_13 (rejectCons r2_n2_30 (rejectCons r2_n2_32 (rejectCons r2_n2_37 (rejectNil 5)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_1 : ¬ attainable 6 n1_1 := by
  exact stepCover [n2_3, n2_4, n2_5, n2_6, n2_45] (by decide +kernel) (rejectCons r2_n2_3 (rejectCons r2_n2_4 (rejectCons r2_n2_5 (rejectCons r2_n2_6 (rejectCons r2_n2_45 (rejectNil 5))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_2 : ¬ attainable 6 n1_2 := by
  exact stepCover [n2_1, n2_7, n2_8, n2_11, n2_28] (by decide +kernel) (rejectCons r2_n2_1 (rejectCons r2_n2_7 (rejectCons r2_n2_8 (rejectCons r2_n2_11 (rejectCons r2_n2_28 (rejectNil 5))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_3 : ¬ attainable 6 n1_3 := by
  exact stepCover [n2_12, n2_13, n2_14, n2_15, n2_16, n2_17, n2_20, n2_53] (by decide +kernel) (rejectCons r2_n2_12 (rejectCons r2_n2_13 (rejectCons r2_n2_14 (rejectCons r2_n2_15 (rejectCons r2_n2_16 (rejectCons r2_n2_17 (rejectCons r2_n2_20 (rejectCons r2_n2_53 (rejectNil 5)))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_4 : ¬ attainable 6 n1_4 := by
  exact stepCover [n2_0, n2_23, n2_26, n2_27, n2_29] (by decide +kernel) (rejectCons r2_n2_0 (rejectCons r2_n2_23 (rejectCons r2_n2_26 (rejectCons r2_n2_27 (rejectCons r2_n2_29 (rejectNil 5))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_5 : ¬ attainable 6 n1_5 := by
  exact stepCover [n2_13, n2_31, n2_33, n2_37] (by decide +kernel) (rejectCons r2_n2_13 (rejectCons r2_n2_31 (rejectCons r2_n2_33 (rejectCons r2_n2_37 (rejectNil 5)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_6 : ¬ attainable 6 n1_6 := by
  exact stepCover [n2_4, n2_7, n2_14, n2_26, n2_31, n2_34, n2_35, n2_38, n2_44, n2_50] (by decide +kernel) (rejectCons r2_n2_4 (rejectCons r2_n2_7 (rejectCons r2_n2_14 (rejectCons r2_n2_26 (rejectCons r2_n2_31 (rejectCons r2_n2_34 (rejectCons r2_n2_35 (rejectCons r2_n2_38 (rejectCons r2_n2_44 (rejectCons r2_n2_50 (rejectNil 5)))))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_7 : ¬ attainable 6 n1_7 := by
  exact stepCover [n2_5, n2_10, n2_27, n2_33, n2_34, n2_36, n2_39, n2_49, n2_51] (by decide +kernel) (rejectCons r2_n2_5 (rejectCons r2_n2_10 (rejectCons r2_n2_27 (rejectCons r2_n2_33 (rejectCons r2_n2_34 (rejectCons r2_n2_36 (rejectCons r2_n2_39 (rejectCons r2_n2_49 (rejectCons r2_n2_51 (rejectNil 5))))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_8 : ¬ attainable 6 n1_8 := by
  exact stepCover [n2_35, n2_36, n2_40] (by decide +kernel) (rejectCons r2_n2_35 (rejectCons r2_n2_36 (rejectCons r2_n2_40 (rejectNil 5))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_9 : ¬ attainable 6 n1_9 := by
  exact stepCover [n2_6, n2_8, n2_19, n2_29, n2_37, n2_38, n2_39, n2_40, n2_42, n2_52] (by decide +kernel) (rejectCons r2_n2_6 (rejectCons r2_n2_8 (rejectCons r2_n2_19 (rejectCons r2_n2_29 (rejectCons r2_n2_37 (rejectCons r2_n2_38 (rejectCons r2_n2_39 (rejectCons r2_n2_40 (rejectCons r2_n2_42 (rejectCons r2_n2_52 (rejectNil 5)))))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_10 : ¬ attainable 6 n1_10 := by
  exact stepCover [n2_2, n2_24, n2_41, n2_42, n2_43, n2_49] (by decide +kernel) (rejectCons r2_n2_2 (rejectCons r2_n2_24 (rejectCons r2_n2_41 (rejectCons r2_n2_42 (rejectCons r2_n2_43 (rejectCons r2_n2_49 (rejectNil 5)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_11 : ¬ attainable 6 n1_11 := by
  exact stepCover [n2_18, n2_50, n2_51, n2_52] (by decide +kernel) (rejectCons r2_n2_18 (rejectCons r2_n2_50 (rejectCons r2_n2_51 (rejectCons r2_n2_52 (rejectNil 5)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_12 : ¬ attainable 6 n1_12 := by
  exact stepCover [n2_45] (by decide +kernel) (rejectCons r2_n2_45 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_13 : ¬ attainable 6 n1_13 := by
  exact stepCover [n2_45, n2_48] (by decide +kernel) (rejectCons r2_n2_45 (rejectCons r2_n2_48 (rejectNil 5)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_14 : ¬ attainable 6 n1_14 := by
  exact stepCover [n2_28] (by decide +kernel) (rejectCons r2_n2_28 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_15 : ¬ attainable 6 n1_15 := by
  exact stepCover [n2_12, n2_13, n2_15, n2_16, n2_17, n2_53] (by decide +kernel) (rejectCons r2_n2_12 (rejectCons r2_n2_13 (rejectCons r2_n2_15 (rejectCons r2_n2_16 (rejectCons r2_n2_17 (rejectCons r2_n2_53 (rejectNil 5)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_16 : ¬ attainable 6 n1_16 := by
  exact stepCover [n2_12, n2_13, n2_15, n2_16, n2_17, n2_53] (by decide +kernel) (rejectCons r2_n2_12 (rejectCons r2_n2_13 (rejectCons r2_n2_15 (rejectCons r2_n2_16 (rejectCons r2_n2_17 (rejectCons r2_n2_53 (rejectNil 5)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_17 : ¬ attainable 6 n1_17 := by
  exact stepCover [n2_12, n2_13, n2_15, n2_16, n2_17, n2_53, n2_54] (by decide +kernel) (rejectCons r2_n2_12 (rejectCons r2_n2_13 (rejectCons r2_n2_15 (rejectCons r2_n2_16 (rejectCons r2_n2_17 (rejectCons r2_n2_53 (rejectCons r2_n2_54 (rejectNil 5))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_18 : ¬ attainable 6 n1_18 := by
  exact stepCover [n2_12, n2_13, n2_15, n2_16, n2_17, n2_53] (by decide +kernel) (rejectCons r2_n2_12 (rejectCons r2_n2_13 (rejectCons r2_n2_15 (rejectCons r2_n2_16 (rejectCons r2_n2_17 (rejectCons r2_n2_53 (rejectNil 5)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_19 : ¬ attainable 6 n1_19 := by
  exact stepCover [n2_23] (by decide +kernel) (rejectCons r2_n2_23 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_20 : ¬ attainable 6 n1_20 := by
  exact stepCover [n2_22] (by decide +kernel) (rejectCons r2_n2_22 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_21 : ¬ attainable 6 n1_21 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_22 : ¬ attainable 6 n1_22 := by
  exact stepCover [n2_18] (by decide +kernel) (rejectCons r2_n2_18 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_23 : ¬ attainable 6 n1_23 := by
  exact stepCover [n2_6, n2_8, n2_13, n2_19, n2_29, n2_37, n2_42] (by decide +kernel) (rejectCons r2_n2_6 (rejectCons r2_n2_8 (rejectCons r2_n2_13 (rejectCons r2_n2_19 (rejectCons r2_n2_29 (rejectCons r2_n2_37 (rejectCons r2_n2_42 (rejectNil 5))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_24 : ¬ attainable 6 n1_24 := by
  exact stepCover [n2_12] (by decide +kernel) (rejectCons r2_n2_12 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_25 : ¬ attainable 6 n1_25 := by
  exact stepCover [n2_13] (by decide +kernel) (rejectCons r2_n2_13 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_26 : ¬ attainable 6 n1_26 := by
  exact stepCover [n2_13] (by decide +kernel) (rejectCons r2_n2_13 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_27 : ¬ attainable 6 n1_27 := by
  exact stepCover [n2_4, n2_7, n2_13, n2_14, n2_26, n2_31, n2_42, n2_43, n2_44] (by decide +kernel) (rejectCons r2_n2_4 (rejectCons r2_n2_7 (rejectCons r2_n2_13 (rejectCons r2_n2_14 (rejectCons r2_n2_26 (rejectCons r2_n2_31 (rejectCons r2_n2_42 (rejectCons r2_n2_43 (rejectCons r2_n2_44 (rejectNil 5))))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_28 : ¬ attainable 6 n1_28 := by
  exact stepCover [n2_13, n2_46] (by decide +kernel) (rejectCons r2_n2_13 (rejectCons r2_n2_46 (rejectNil 5)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n2_31 : ¬ attainable 6 n2_31 := by
  exact stepCover [n2_4, n2_7, n2_14, n2_26, n2_31, n2_44] (by decide +kernel) (rejectCons r2_n2_4 (rejectCons r2_n2_7 (rejectCons r2_n2_14 (rejectCons r2_n2_26 (rejectCons r2_n2_31 (rejectCons r2_n2_44 (rejectNil 5)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_30 : ¬ attainable 6 n1_30 := by
  exact stepCover [n2_5, n2_9, n2_10, n2_13, n2_27, n2_33, n2_49] (by decide +kernel) (rejectCons r2_n2_5 (rejectCons r2_n2_9 (rejectCons r2_n2_10 (rejectCons r2_n2_13 (rejectCons r2_n2_27 (rejectCons r2_n2_33 (rejectCons r2_n2_49 (rejectNil 5))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_31 : ¬ attainable 6 n1_31 := by
  exact stepCover [n2_13] (by decide +kernel) (rejectCons r2_n2_13 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_32 : ¬ attainable 6 n1_32 := by
  exact stepCover [n2_4, n2_7, n2_14, n2_26, n2_31, n2_44] (by decide +kernel) (rejectCons r2_n2_4 (rejectCons r2_n2_7 (rejectCons r2_n2_14 (rejectCons r2_n2_26 (rejectCons r2_n2_31 (rejectCons r2_n2_44 (rejectNil 5)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_33 : ¬ attainable 6 n1_33 := by
  exact stepCover [n2_13, n2_19] (by decide +kernel) (rejectCons r2_n2_13 (rejectCons r2_n2_19 (rejectNil 5)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_34 : ¬ attainable 6 n1_34 := by
  exact stepCover [n2_9, n2_13] (by decide +kernel) (rejectCons r2_n2_9 (rejectCons r2_n2_13 (rejectNil 5)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_35 : ¬ attainable 6 n1_35 := by
  exact stepCover [n2_13, n2_16, n2_25] (by decide +kernel) (rejectCons r2_n2_13 (rejectCons r2_n2_16 (rejectCons r2_n2_25 (rejectNil 5))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n2_33 : ¬ attainable 6 n2_33 := by
  exact stepCover [n2_5, n2_10, n2_27, n2_33, n2_49] (by decide +kernel) (rejectCons r2_n2_5 (rejectCons r2_n2_10 (rejectCons r2_n2_27 (rejectCons r2_n2_33 (rejectCons r2_n2_49 (rejectNil 5))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_37 : ¬ attainable 6 n1_37 := by
  exact stepCover [n2_5, n2_10, n2_27, n2_33, n2_49] (by decide +kernel) (rejectCons r2_n2_5 (rejectCons r2_n2_10 (rejectCons r2_n2_27 (rejectCons r2_n2_33 (rejectCons r2_n2_49 (rejectNil 5))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_38 : ¬ attainable 6 n1_38 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_39 : ¬ attainable 6 n1_39 := by
  exact stepCover [n2_4, n2_7, n2_14, n2_26, n2_31, n2_44] (by decide +kernel) (rejectCons r2_n2_4 (rejectCons r2_n2_7 (rejectCons r2_n2_14 (rejectCons r2_n2_26 (rejectCons r2_n2_31 (rejectCons r2_n2_44 (rejectNil 5)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_40 : ¬ attainable 6 n1_40 := by
  exact stepCover [n2_5, n2_10, n2_27, n2_33, n2_49] (by decide +kernel) (rejectCons r2_n2_5 (rejectCons r2_n2_10 (rejectCons r2_n2_27 (rejectCons r2_n2_33 (rejectCons r2_n2_49 (rejectNil 5))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_41 : ¬ attainable 6 n1_41 := by
  exact stepCover [n2_15] (by decide +kernel) (rejectCons r2_n2_15 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_42 : ¬ attainable 6 n1_42 := by
  exact stepCover [n2_16] (by decide +kernel) (rejectCons r2_n2_16 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_43 : ¬ attainable 6 n1_43 := by
  exact stepCover [n2_17] (by decide +kernel) (rejectCons r2_n2_17 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n2_37 : ¬ attainable 6 n2_37 := by
  exact stepCover [n2_6, n2_8, n2_19, n2_29, n2_37, n2_42] (by decide +kernel) (rejectCons r2_n2_6 (rejectCons r2_n2_8 (rejectCons r2_n2_19 (rejectCons r2_n2_29 (rejectCons r2_n2_37 (rejectCons r2_n2_42 (rejectNil 5)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_45 : ¬ attainable 6 n1_45 := by
  exact stepCover [n2_6, n2_8, n2_19, n2_29, n2_37, n2_42] (by decide +kernel) (rejectCons r2_n2_6 (rejectCons r2_n2_8 (rejectCons r2_n2_19 (rejectCons r2_n2_29 (rejectCons r2_n2_37 (rejectCons r2_n2_42 (rejectNil 5)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_46 : ¬ attainable 6 n1_46 := by
  exact stepCover [n2_6, n2_8, n2_19, n2_29, n2_37, n2_42] (by decide +kernel) (rejectCons r2_n2_6 (rejectCons r2_n2_8 (rejectCons r2_n2_19 (rejectCons r2_n2_29 (rejectCons r2_n2_37 (rejectCons r2_n2_42 (rejectNil 5)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_47 : ¬ attainable 6 n1_47 := by
  exact stepCover [n2_24, n2_41] (by decide +kernel) (rejectCons r2_n2_24 (rejectCons r2_n2_41 (rejectNil 5)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_48 : ¬ attainable 6 n1_48 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_49 : ¬ attainable 6 n1_49 := by
  exact stepCover [n2_21] (by decide +kernel) (rejectCons r2_n2_21 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_50 : ¬ attainable 6 n1_50 := by
  exact stepCover [n2_24, n2_41, n2_46, n2_47] (by decide +kernel) (rejectCons r2_n2_24 (rejectCons r2_n2_41 (rejectCons r2_n2_46 (rejectCons r2_n2_47 (rejectNil 5)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_51 : ¬ attainable 6 n1_51 := by
  exact stepCover [n2_19] (by decide +kernel) (rejectCons r2_n2_19 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_52 : ¬ attainable 6 n1_52 := by
  exact stepCover [n2_19, n2_37] (by decide +kernel) (rejectCons r2_n2_19 (rejectCons r2_n2_37 (rejectNil 5)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_53 : ¬ attainable 6 n1_53 := by
  exact stepCover [n2_18] (by decide +kernel) (rejectCons r2_n2_18 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_54 : ¬ attainable 6 n1_54 := by
  exact stepCover [n2_18] (by decide +kernel) (rejectCons r2_n2_18 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r0_wires : ¬ attainable 7 wires := by
  exact stepCover [n1_0, n1_1, n1_2, n1_3, n1_4, n1_5, n1_6, n1_7, n1_8, n1_9, n1_10, n1_11, n1_12, n1_13, n1_14, n1_15, n1_16, n1_17, n1_18, n1_19, n1_20, n1_21, n1_22, n1_23, n1_24, n1_25, n1_26, n1_27, n1_28, n2_31, n1_30, n1_31, n1_32, n1_33, n1_34, n1_35, n2_33, n1_37, n1_38, n1_39, n1_40, n1_41, n1_42, n1_43, n2_37, n1_45, n1_46, n1_47, n1_48, n1_49, n1_50, n1_51, n1_52, n1_53, n1_54] (by decide +kernel) (rejectCons r1_n1_0 (rejectCons r1_n1_1 (rejectCons r1_n1_2 (rejectCons r1_n1_3 (rejectCons r1_n1_4 (rejectCons r1_n1_5 (rejectCons r1_n1_6 (rejectCons r1_n1_7 (rejectCons r1_n1_8 (rejectCons r1_n1_9 (rejectCons r1_n1_10 (rejectCons r1_n1_11 (rejectCons r1_n1_12 (rejectCons r1_n1_13 (rejectCons r1_n1_14 (rejectCons r1_n1_15 (rejectCons r1_n1_16 (rejectCons r1_n1_17 (rejectCons r1_n1_18 (rejectCons r1_n1_19 (rejectCons r1_n1_20 (rejectCons r1_n1_21 (rejectCons r1_n1_22 (rejectCons r1_n1_23 (rejectCons r1_n1_24 (rejectCons r1_n1_25 (rejectCons r1_n1_26 (rejectCons r1_n1_27 (rejectCons r1_n1_28 (rejectCons r1_n2_31 (rejectCons r1_n1_30 (rejectCons r1_n1_31 (rejectCons r1_n1_32 (rejectCons r1_n1_33 (rejectCons r1_n1_34 (rejectCons r1_n1_35 (rejectCons r1_n2_33 (rejectCons r1_n1_37 (rejectCons r1_n1_38 (rejectCons r1_n1_39 (rejectCons r1_n1_40 (rejectCons r1_n1_41 (rejectCons r1_n1_42 (rejectCons r1_n1_43 (rejectCons r1_n2_37 (rejectCons r1_n1_45 (rejectCons r1_n1_46 (rejectCons r1_n1_47 (rejectCons r1_n1_48 (rejectCons r1_n1_49 (rejectCons r1_n1_50 (rejectCons r1_n1_51 (rejectCons r1_n1_52 (rejectCons r1_n1_53 (rejectCons r1_n1_54 (rejectNil 6))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Depth7

theorem noDepth7 : NoSuffix 18085043209519168250 14468034567615334600 := fun rest o hs hl hr => Depth7.r0_wires (Depth7.suffix rest o hs hl hr)

namespace Reverse7
open CircuitSatBridge FreeSupport
def wires : List Wire := [Depth7.w0, Depth7.w13, Depth7.w33, Depth7.w43, Depth7.w31, Depth7.w47, Depth7.w27, Depth7.w38, Depth7.w2, Depth7.w42]
def test (t : Fin 110) (b : Bool) : Fin 128 :=
  let pts : List (Fin 128) := if b then [74, 42, 21, 41, 37, 41, 82, 21, 21, 37, 42, 42, 84, 74, 82, 37, 84, 74, 82, 41, 37, 74, 84, 82, 21, 41, 74, 41, 21, 37, 37, 41, 21, 42, 84, 74, 84, 82, 41, 21, 82, 84, 37, 42, 82, 42, 42, 84, 74, 74, 84, 82, 2, 21, 42, 21, 84, 4, 74, 74, 2, 42, 82, 1, 41, 8, 84, 37, 37, 41, 64, 82, 16, 4, 21, 68, 80, 68, 34, 18, 34, 18, 68, 20, 17, 72, 9, 17, 33, 10, 18, 17, 36, 66, 9, 10, 66, 36, 5, 40, 80, 20, 72, 5, 72, 8, 32, 20, 0, 41] else [65, 3, 65, 12, 3, 3, 65, 24, 48, 12, 12, 6, 65, 24, 24, 6, 24, 6, 6, 96, 96, 12, 12, 3, 3, 24, 3, 65, 12, 65, 48, 48, 6, 24, 6, 96, 48, 96, 6, 96, 48, 96, 24, 96, 12, 65, 48, 3, 48, 90, 92, 90, 3, 29, 43, 23, 86, 6, 78, 75, 6, 46, 83, 3, 45, 12, 85, 39, 45, 43, 65, 86, 24, 12, 85, 76, 88, 70, 35, 19, 38, 22, 69, 22, 19, 88, 13, 81, 35, 11, 26, 25, 44, 67, 11, 14, 70, 38, 13, 44, 81, 28, 76, 7, 73, 14, 35, 92, 3, 35]
  pts.getD t.val 0
set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem samples : ∀ t : Fin 110, ∀ b : Bool,
   sample wires t b = deepBank 18446744073692839680 18446462603011031040 (test t b) ∧ target (test t b) = !b := by decide +kernel

theorem suffix (rest : List Gate) (o : Nat) (hs : ∀ g ∈ rest, Supported g) (hlen : rest.length ≤ 7)
   (hr : ∀ x : Fin 128, (run rest (deepBank 18446744073692839680 18446462603011031040 x)).getD o false = target x) :
   attainable 7 wires := by
 obtain ⟨cs,hl,hv,he⟩ := fixed_slots 6 10 o rest hs hlen
 refine ⟨cs,16,hl,hv,?_⟩
 intro t
 have h (b : Bool) : (runChoices cs (sample wires t b)).getD 16 false = !b := by
   rw [(samples t b).1, he]
   · exact (hr _).trans (samples t b).2
   · simp [deepBank, otherInputs]
 exact ⟨h false, h true⟩
theorem project (k : Nat) (hs : attainable k wires) : attainable k Depth7.wires := by
  have hm : wires.all (fun w => Depth7.wires.contains w) = true := by decide +kernel
  obtain ⟨cs, o, rfl, _, orient⟩ := hs
  obtain ⟨support, sub, _, det⟩ := bounded_support cs wires.length o
  apply project_suffix sub orient det
  intro i hi
  exact Or.inl (List.contains_iff_mem.mp ((List.all_eq_true.mp hm) _ (List.getElem_mem _)))

end Reverse7

theorem revDepth7 : NoSuffix 18446744073692839680 18446462603011031040 := fun rest o hs hl hr => Depth7.r0_wires (Reverse7.project 7 (Reverse7.suffix rest o hs hl hr))

namespace Depth8
open CircuitSatBridge FreeSupport PEqualNP.CircuitLowerBounds
def w0 := mkSampleWire 0 0 0 0 0 0
def w1 := mkSampleWire 927914289152 481 0 0 0 0
def w2 := mkSampleWire 1077973152 2420383746 34738448 0 0 0
def w3 := mkSampleWire 928992262304 2420384227 34738448 0 0 0
def w4 := mkSampleWire 13965299876 592442631178 38957333 0 0 0
def w5 := mkSampleWire 941879589028 592442631659 38957333 0 0 0
def w6 := mkSampleWire 17213423705 8734638608 539329024 0 0 0
def w7 := mkSampleWire 86067142745 8734638897 539329024 0 0 0
def w8 := mkSampleWire 945127712857 8734639089 539329024 0 0 0
def w9 := mkSampleWire 19898434139 77555468820 565020194 0 0 0
def w10 := mkSampleWire 947812723291 77555469301 565020194 0 0 0
def w11 := mkSampleWire 927914289152 275482542561 524328 1275134978 537395216 40
def w12 := mkSampleWire 150620931332 1028163851784 507804877 897953858405 976069481318 275585
def w13 := mkSampleWire 1078535220484 1028163852265 507804877 897953858405 976069481318 275585
def w14 := mkSampleWire 151698904484 1030579779082 508984797 897953858405 976069481318 275585
def w15 := mkSampleWire 1079613193636 1030579779563 508984797 897953858405 976069481318 275585
def w16 := mkSampleWire 927914289152 276556349921 524333 155932100358 276556349683 524333
def w17 := mkSampleWire 1078535220484 1028231485417 508329197 1053852403559 976674051063 799917
def w18 := mkSampleWire 13965299876 661238129674 577925399 201004102674 103961658513 6308102
def w19 := mkSampleWire 941879589028 661238130155 577925399 201004102674 103961658513 6308102
def w20 := mkSampleWire 19898434139 112989276692 566076962 429805929253 35534636003 18359810
def w21 := mkSampleWire 947812723291 112989277173 566076962 429805929253 35534636003 18359810
def w22 := mkSampleWire 947812723291 388404055029 566076975 431081064231 310949938163 18359855
def w23 := mkSampleWire 1013444485030 403292788942 198720703 431081064231 403292789747 198721215
def w24 := mkSampleWire 0 8881463808 197376 623325006024 8613027852 268632064
def w25 := mkSampleWire 1077973152 11029209602 34804496 623325006024 8613027852 268632064
def w26 := mkSampleWire 17213423705 9024070160 539460352 623325006024 8613027852 268632064
def w27 := mkSampleWire 0 696076232192 336020288 623325006024 695807795212 268894208
def w28 := mkSampleWire 1068332904194 499150159333 499682554 46934359194 86732450840 281053304
def w29 := mkSampleWire 1085546327899 507874312181 1038978810 46934359194 86732450840 281053304
def w30 := mkSampleWire 860138543264 11062764226 59972496 898473969897 10794328844 328407696
def w31 := mkSampleWire 928992262304 11062764515 59972496 898473969897 10794328844 328407696
def w32 := mkSampleWire 1010759474596 1030581876426 534216669 898507525101 978235847534 328679057
def w33 := mkSampleWire 1079613193636 1030581876715 534216669 898507525101 978235847534 328679057
def w34 := mkSampleWire 880036977403 115426192086 599769010 1053130935277 46295147503 328941202
def w35 := mkSampleWire 239373084511 1088448863549 1013769327 201037657878 1088717298931 745334127
def w36 := mkSampleWire 31178723581 600361468442 574059269 1052577268581 1012779176935 792688519
def w37 := mkSampleWire 1099511627775 1090630163967 1073544447 476186621751 1090898599923 805109759
def w38 := mkSampleWire 86067142745 696218838833 875021120 668430563544 696218838028 875020608
def w39 := mkSampleWire 945127712857 696218839025 875021120 668430563544 696218838028 875020608
def w40 := mkSampleWire 100032442621 807420127035 913830743 824329108698 799903671453 879214918
def w41 := mkSampleWire 1085546327899 1057634320373 1039126522 669705698522 782655581212 887605624
def w42 := mkSampleWire 946205686009 698400139251 934796240 943579527417 698400139020 934796240
def w43 := mkSampleWire 1079613193636 986522351083 507664861 669705698522 1063976991772 1055382013
def w44 := mkSampleWire 1085546327899 438273498101 495816424 898507525101 995549969262 1067433721
def w45 := mkSampleWire 948890696443 71347775991 565936946 201557769370 123442146457 1073466238
def wires : List Wire := [w0, w20, w38, w16, w30, w18, w12, w42, w1, w28]
def n1_0 : List Wire := [w1, w2, w28, w12, w20, w18, w38]
def n1_1 : List Wire := [w1, w24, w28, w12, w20, w18]
def n1_2 : List Wire := [w1, w28, w12, w32, w20, w18, w38]
def n1_3 : List Wire := [w1, w30, w28, w12, w6, w20, w18]
def n1_4 : List Wire := [w1, w30, w28, w12, w20, w18, w38]
def n1_5 : List Wire := [w1, w30, w28, w12, w20, w18, w39]
def n1_6 : List Wire := [w1, w30, w28, w12, w20, w18, w41]
def n1_7 : List Wire := [w1, w30, w28, w12, w20, w19, w38]
def n1_8 : List Wire := [w1, w30, w28, w12, w21, w18, w38]
def n1_9 : List Wire := [w1, w30, w28, w13, w20, w18, w38]
def n1_10 : List Wire := [w1, w31, w28, w12, w20, w18, w38]
def n1_11 : List Wire := [w11, w30, w28, w12, w20, w18, w38]
def n1_12 : List Wire := [w16, w28, w12, w32, w20, w18, w38]
def n1_13 : List Wire := [w16, w30, w28, w12, w20, w18, w38]
def n1_14 : List Wire := [w16, w30, w28, w12, w20, w18, w39]
def n1_15 : List Wire := [w16, w30, w28, w12, w20, w19, w38]
def n1_16 : List Wire := [w16, w30, w28, w12, w21, w18, w38]
def n1_17 : List Wire := [w16, w30, w28, w13, w20, w18, w38]
def n1_18 : List Wire := [w16, w31, w28, w12, w20, w18, w38]
def n1_19 : List Wire := [w24, w16, w28, w12, w20, w18]
def n1_20 : List Wire := [w24, w28, w12, w20, w18, w38]
def n1_21 : List Wire := [w24, w28, w12, w20, w18, w42]
def n1_22 : List Wire := [w24, w30, w28, w12, w20, w18]
def n1_23 : List Wire := [w28, w12, w20, w18, w34, w38]
def n1_24 : List Wire := [w28, w12, w20, w18, w38, w35]
def n1_25 : List Wire := [w28, w12, w32, w20, w18, w38]
def n1_26 : List Wire := [w30, w12, w20, w36, w18, w38]
def n1_27 : List Wire := [w30, w23, w28, w12, w20, w18]
def n1_28 : List Wire := [w30, w28, w12, w13, w20, w18, w38]
def n1_29 : List Wire := [w30, w28, w12, w17, w20, w18, w38]
def n1_30 : List Wire := [w30, w28, w12, w20, w18, w38]
def n1_31 : List Wire := [w30, w28, w12, w20, w18, w40]
def n1_32 : List Wire := [w30, w28, w12, w20, w21, w18, w38]
def n1_33 : List Wire := [w30, w28, w12, w20, w22, w18, w38]
def n2_25 : List Wire := [w30, w28, w12, w21, w18, w38]
def n1_35 : List Wire := [w30, w28, w12, w21, w18, w38, w42]
def n2_30 : List Wire := [w30, w28, w13, w20, w18, w38]
def n1_37 : List Wire := [w30, w28, w13, w20, w18, w38, w42]
def n1_38 : List Wire := [w30, w28, w43, w12, w18, w38]
def n1_39 : List Wire := [w30, w28, w45, w20, w18, w38]
def n1_40 : List Wire := [w30, w44, w28, w12, w20, w38]
def n2_0 : List Wire := [w1, w4, w28, w12, w20, w38]
def n2_1 : List Wire := [w1, w28, w14, w20, w18, w38]
def n2_2 : List Wire := [w1, w30, w12, w20, w18, w29]
def n2_3 : List Wire := [w1, w30, w28, w12, w9, w18]
def n2_4 : List Wire := [w2, w28, w12, w21, w18, w38]
def n2_5 : List Wire := [w2, w28, w13, w20, w18, w38]
def n2_6 : List Wire := [w3, w28, w12, w20, w18, w38]
def n2_7 : List Wire := [w24, w12, w20, w36, w18]
def n2_8 : List Wire := [w24, w28, w12, w20, w18]
def n2_9 : List Wire := [w24, w28, w12, w21, w18]
def n2_10 : List Wire := [w24, w28, w13, w20, w18]
def n2_11 : List Wire := [w24, w28, w43, w12, w18]
def n2_12 : List Wire := [w24, w28, w45, w20, w18]
def n2_13 : List Wire := [w24, w44, w28, w12, w20]
def n2_14 : List Wire := [w25, w28, w12, w20, w18]
def n2_15 : List Wire := [w27, w28, w12, w20, w18]
def n2_16 : List Wire := [w28, w12, w20, w18, w37]
def n2_17 : List Wire := [w28, w12, w26, w20, w18]
def n2_18 : List Wire := [w28, w12, w32, w21, w18, w38]
def n2_19 : List Wire := [w28, w13, w32, w20, w18, w38]
def n2_20 : List Wire := [w28, w13, w33, w20, w18, w38]
def n2_21 : List Wire := [w28, w17, w32, w20, w18, w38]
def n2_22 : List Wire := [w30, w28, w12, w6, w21, w18]
def n2_23 : List Wire := [w30, w28, w12, w7, w21, w18]
def n2_24 : List Wire := [w30, w28, w12, w8, w20, w18]
def n2_26 : List Wire := [w30, w28, w12, w21, w18, w39]
def n2_27 : List Wire := [w30, w28, w12, w21, w18, w41]
def n2_28 : List Wire := [w30, w28, w12, w21, w19, w38]
def n2_29 : List Wire := [w30, w28, w13, w6, w20, w18]
def n2_31 : List Wire := [w30, w28, w13, w20, w18, w39]
def n2_32 : List Wire := [w30, w28, w13, w20, w18, w41]
def n2_33 : List Wire := [w30, w28, w13, w20, w19, w38]
def n2_34 : List Wire := [w30, w28, w13, w21, w18, w38]
def n2_35 : List Wire := [w31, w28, w12, w20, w19, w38]
def n2_36 : List Wire := [w31, w28, w12, w21, w18, w38]
def n2_37 : List Wire := [w31, w28, w13, w20, w18, w38]
def n3_0 : List Wire := [w4, w28, w12, w21, w38]
def n3_1 : List Wire := [w4, w28, w13, w20, w38]
def n3_2 : List Wire := [w5, w28, w12, w20, w38]
def n3_3 : List Wire := [w28, w14, w21, w18, w38]
def n3_4 : List Wire := [w28, w15, w20, w18, w38]
def n3_5 : List Wire := [w30, w12, w21, w18, w29]
def n3_6 : List Wire := [w30, w13, w20, w18, w29]
def n3_7 : List Wire := [w30, w28, w12, w10, w18]
def n3_8 : List Wire := [w30, w28, w13, w9, w18]
def test (t : Fin 110) (b : Bool) : Fin 128 :=
  let pts : List (Fin 128) := if b then [82, 41, 74, 21, 37, 82, 84, 21, 74, 74, 41, 21, 37, 37, 21, 84, 41, 42, 42, 82, 84, 82, 42, 37, 21, 74, 41, 41, 82, 21, 41, 37, 84, 37, 42, 37, 84, 42, 82, 84, 42, 74, 84, 21, 41, 74, 74, 42, 82, 82, 37, 1, 64, 21, 84, 2, 42, 74, 82, 41, 32, 21, 84, 37, 21, 82, 42, 4, 37, 41, 74, 16, 64, 84, 1, 34, 33, 68, 72, 68, 72, 34, 40, 9, 17, 9, 5, 80, 36, 18, 66, 17, 80, 66, 36, 5, 20, 20, 68, 10, 18, 36, 33, 17, 18, 16, 4, 0, 21, 4] else [6, 3, 96, 6, 6, 48, 6, 48, 65, 3, 65, 24, 48, 12, 12, 48, 96, 3, 96, 3, 65, 96, 48, 65, 65, 6, 24, 12, 65, 3, 48, 3, 96, 96, 6, 24, 12, 65, 24, 24, 12, 48, 3, 96, 6, 12, 24, 24, 12, 86, 101, 3, 65, 53, 85, 3, 106, 75, 114, 43, 96, 23, 116, 39, 85, 83, 43, 6, 53, 105, 106, 48, 96, 86, 65, 98, 35, 69, 73, 100, 104, 35, 104, 73, 49, 11, 69, 81, 52, 22, 67, 81, 112, 98, 100, 7, 22, 52, 70, 11, 50, 38, 97, 19, 19, 112, 69, 65, 69, 38]
  pts.getD t.val 0

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem samples : ∀ t : Fin 110, ∀ b : Bool,
   sample wires t b = deepBank 18432388630850633676 17348130476094714048 (test t b) ∧ target (test t b) = !b := by decide +kernel

theorem suffix (rest : List Gate) (o : Nat) (hs : ∀ g ∈ rest, Supported g) (hlen : rest.length ≤ 7)
   (hr : ∀ x : Fin 128, (run rest (deepBank 18432388630850633676 17348130476094714048 x)).getD o false = target x) :
   attainable 7 wires := by
 obtain ⟨cs,hl,hv,he⟩ := fixed_slots 6 10 o rest hs hlen
 refine ⟨cs,16,hl,hv,?_⟩
 intro t
 have h (b : Bool) : (runChoices cs (sample wires t b)).getD 16 false = !b := by
   rw [(samples t b).1, he]
   · exact (hr _).trans (samples t b).2
   · simp [deepBank, otherInputs]
 exact ⟨h false, h true⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_0 : ¬ attainable 4 n3_0 := by
  exact stepCover [] (by decide +kernel) (rejectNil 3)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_1 : ¬ attainable 4 n3_1 := by
  exact stepCover [] (by decide +kernel) (rejectNil 3)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_2 : ¬ attainable 4 n3_2 := by
  exact stepCover [] (by decide +kernel) (rejectNil 3)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_3 : ¬ attainable 4 n3_3 := by
  exact stepCover [] (by decide +kernel) (rejectNil 3)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_4 : ¬ attainable 4 n3_4 := by
  exact stepCover [] (by decide +kernel) (rejectNil 3)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_5 : ¬ attainable 4 n3_5 := by
  exact stepCover [] (by decide +kernel) (rejectNil 3)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_6 : ¬ attainable 4 n3_6 := by
  exact stepCover [] (by decide +kernel) (rejectNil 3)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_7 : ¬ attainable 4 n3_7 := by
  exact stepCover [] (by decide +kernel) (rejectNil 3)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r3_n3_8 : ¬ attainable 4 n3_8 := by
  exact stepCover [] (by decide +kernel) (rejectNil 3)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_0 : ¬ attainable 5 n2_0 := by
  exact stepCover [n3_0, n3_1, n3_2] (by decide +kernel) (rejectCons r3_n3_0 (rejectCons r3_n3_1 (rejectCons r3_n3_2 (rejectNil 4))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_1 : ¬ attainable 5 n2_1 := by
  exact stepCover [n3_3, n3_4] (by decide +kernel) (rejectCons r3_n3_3 (rejectCons r3_n3_4 (rejectNil 4)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_2 : ¬ attainable 5 n2_2 := by
  exact stepCover [n3_5, n3_6] (by decide +kernel) (rejectCons r3_n3_5 (rejectCons r3_n3_6 (rejectNil 4)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_3 : ¬ attainable 5 n2_3 := by
  exact stepCover [n3_7, n3_8] (by decide +kernel) (rejectCons r3_n3_7 (rejectCons r3_n3_8 (rejectNil 4)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_4 : ¬ attainable 5 n2_4 := by
  exact stepCover [n3_3] (by decide +kernel) (rejectCons r3_n3_3 (rejectNil 4))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_5 : ¬ attainable 5 n2_5 := by
  exact stepCover [n3_4] (by decide +kernel) (rejectCons r3_n3_4 (rejectNil 4))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_6 : ¬ attainable 5 n2_6 := by
  exact stepCover [n3_4] (by decide +kernel) (rejectCons r3_n3_4 (rejectNil 4))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_7 : ¬ attainable 5 n2_7 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_8 : ¬ attainable 5 n2_8 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_9 : ¬ attainable 5 n2_9 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_10 : ¬ attainable 5 n2_10 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_11 : ¬ attainable 5 n2_11 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_12 : ¬ attainable 5 n2_12 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_13 : ¬ attainable 5 n2_13 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_14 : ¬ attainable 5 n2_14 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_15 : ¬ attainable 5 n2_15 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_16 : ¬ attainable 5 n2_16 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_17 : ¬ attainable 5 n2_17 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_18 : ¬ attainable 5 n2_18 := by
  exact stepCover [n3_0] (by decide +kernel) (rejectCons r3_n3_0 (rejectNil 4))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_19 : ¬ attainable 5 n2_19 := by
  exact stepCover [n3_1] (by decide +kernel) (rejectCons r3_n3_1 (rejectNil 4))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_20 : ¬ attainable 5 n2_20 := by
  exact stepCover [n3_1] (by decide +kernel) (rejectCons r3_n3_1 (rejectNil 4))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_21 : ¬ attainable 5 n2_21 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_22 : ¬ attainable 5 n2_22 := by
  exact stepCover [n3_5] (by decide +kernel) (rejectCons r3_n3_5 (rejectNil 4))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_23 : ¬ attainable 5 n2_23 := by
  exact stepCover [n3_5] (by decide +kernel) (rejectCons r3_n3_5 (rejectNil 4))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_24 : ¬ attainable 5 n2_24 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_25 : ¬ attainable 5 n2_25 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_26 : ¬ attainable 5 n2_26 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_27 : ¬ attainable 5 n2_27 := by
  exact stepCover [n3_7] (by decide +kernel) (rejectCons r3_n3_7 (rejectNil 4))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_28 : ¬ attainable 5 n2_28 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_29 : ¬ attainable 5 n2_29 := by
  exact stepCover [n3_6] (by decide +kernel) (rejectCons r3_n3_6 (rejectNil 4))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_30 : ¬ attainable 5 n2_30 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_31 : ¬ attainable 5 n2_31 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_32 : ¬ attainable 5 n2_32 := by
  exact stepCover [n3_8] (by decide +kernel) (rejectCons r3_n3_8 (rejectNil 4))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_33 : ¬ attainable 5 n2_33 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_34 : ¬ attainable 5 n2_34 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_35 : ¬ attainable 5 n2_35 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_36 : ¬ attainable 5 n2_36 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_37 : ¬ attainable 5 n2_37 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_0 : ¬ attainable 6 n1_0 := by
  exact stepCover [n2_1, n2_4, n2_5, n2_6] (by decide +kernel) (rejectCons r2_n2_1 (rejectCons r2_n2_4 (rejectCons r2_n2_5 (rejectCons r2_n2_6 (rejectNil 5)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_1 : ¬ attainable 6 n1_1 := by
  exact stepCover [n2_7, n2_8, n2_9, n2_10, n2_11, n2_12, n2_13, n2_16] (by decide +kernel) (rejectCons r2_n2_7 (rejectCons r2_n2_8 (rejectCons r2_n2_9 (rejectCons r2_n2_10 (rejectCons r2_n2_11 (rejectCons r2_n2_12 (rejectCons r2_n2_13 (rejectCons r2_n2_16 (rejectNil 5)))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_2 : ¬ attainable 6 n1_2 := by
  exact stepCover [n2_0, n2_15, n2_18, n2_19] (by decide +kernel) (rejectCons r2_n2_0 (rejectCons r2_n2_15 (rejectCons r2_n2_18 (rejectCons r2_n2_19 (rejectNil 5)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_3 : ¬ attainable 6 n1_3 := by
  exact stepCover [n2_2, n2_22, n2_24, n2_29] (by decide +kernel) (rejectCons r2_n2_2 (rejectCons r2_n2_22 (rejectCons r2_n2_24 (rejectCons r2_n2_29 (rejectNil 5)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_4 : ¬ attainable 6 n1_4 := by
  exact stepCover [n2_8, n2_25, n2_30] (by decide +kernel) (rejectCons r2_n2_8 (rejectCons r2_n2_25 (rejectCons r2_n2_30 (rejectNil 5))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_5 : ¬ attainable 6 n1_5 := by
  exact stepCover [n2_26, n2_31] (by decide +kernel) (rejectCons r2_n2_26 (rejectCons r2_n2_31 (rejectNil 5)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_6 : ¬ attainable 6 n1_6 := by
  exact stepCover [n2_3, n2_27, n2_32] (by decide +kernel) (rejectCons r2_n2_3 (rejectCons r2_n2_27 (rejectCons r2_n2_32 (rejectNil 5))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_7 : ¬ attainable 6 n1_7 := by
  exact stepCover [n2_28, n2_33, n2_35] (by decide +kernel) (rejectCons r2_n2_28 (rejectCons r2_n2_33 (rejectCons r2_n2_35 (rejectNil 5))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_8 : ¬ attainable 6 n1_8 := by
  exact stepCover [n2_4, n2_9, n2_18, n2_23, n2_25, n2_26, n2_27, n2_28, n2_34, n2_36] (by decide +kernel) (rejectCons r2_n2_4 (rejectCons r2_n2_9 (rejectCons r2_n2_18 (rejectCons r2_n2_23 (rejectCons r2_n2_25 (rejectCons r2_n2_26 (rejectCons r2_n2_27 (rejectCons r2_n2_28 (rejectCons r2_n2_34 (rejectCons r2_n2_36 (rejectNil 5)))))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_9 : ¬ attainable 6 n1_9 := by
  exact stepCover [n2_5, n2_10, n2_20, n2_29, n2_30, n2_31, n2_32, n2_33, n2_34, n2_37] (by decide +kernel) (rejectCons r2_n2_5 (rejectCons r2_n2_10 (rejectCons r2_n2_20 (rejectCons r2_n2_29 (rejectCons r2_n2_30 (rejectCons r2_n2_31 (rejectCons r2_n2_32 (rejectCons r2_n2_33 (rejectCons r2_n2_34 (rejectCons r2_n2_37 (rejectNil 5)))))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_10 : ¬ attainable 6 n1_10 := by
  exact stepCover [n2_35, n2_36, n2_37] (by decide +kernel) (rejectCons r2_n2_35 (rejectCons r2_n2_36 (rejectCons r2_n2_37 (rejectNil 5))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_11 : ¬ attainable 6 n1_11 := by
  exact stepCover [n2_8] (by decide +kernel) (rejectCons r2_n2_8 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_12 : ¬ attainable 6 n1_12 := by
  exact stepCover [n2_15, n2_21] (by decide +kernel) (rejectCons r2_n2_15 (rejectCons r2_n2_21 (rejectNil 5)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_13 : ¬ attainable 6 n1_13 := by
  exact stepCover [n2_8] (by decide +kernel) (rejectCons r2_n2_8 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_14 : ¬ attainable 6 n1_14 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_15 : ¬ attainable 6 n1_15 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_16 : ¬ attainable 6 n1_16 := by
  exact stepCover [n2_4, n2_9, n2_18, n2_23, n2_25, n2_27] (by decide +kernel) (rejectCons r2_n2_4 (rejectCons r2_n2_9 (rejectCons r2_n2_18 (rejectCons r2_n2_23 (rejectCons r2_n2_25 (rejectCons r2_n2_27 (rejectNil 5)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_17 : ¬ attainable 6 n1_17 := by
  exact stepCover [n2_5, n2_10, n2_20, n2_29, n2_30, n2_32] (by decide +kernel) (rejectCons r2_n2_5 (rejectCons r2_n2_10 (rejectCons r2_n2_20 (rejectCons r2_n2_29 (rejectCons r2_n2_30 (rejectCons r2_n2_32 (rejectNil 5)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_18 : ¬ attainable 6 n1_18 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_19 : ¬ attainable 6 n1_19 := by
  exact stepCover [n2_7, n2_8, n2_11, n2_12, n2_13, n2_16] (by decide +kernel) (rejectCons r2_n2_7 (rejectCons r2_n2_8 (rejectCons r2_n2_11 (rejectCons r2_n2_12 (rejectCons r2_n2_13 (rejectCons r2_n2_16 (rejectNil 5)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_20 : ¬ attainable 6 n1_20 := by
  exact stepCover [n2_7, n2_8, n2_11, n2_12, n2_13, n2_16] (by decide +kernel) (rejectCons r2_n2_7 (rejectCons r2_n2_8 (rejectCons r2_n2_11 (rejectCons r2_n2_12 (rejectCons r2_n2_13 (rejectCons r2_n2_16 (rejectNil 5)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_21 : ¬ attainable 6 n1_21 := by
  exact stepCover [n2_7, n2_8, n2_11, n2_12, n2_13, n2_16] (by decide +kernel) (rejectCons r2_n2_7 (rejectCons r2_n2_8 (rejectCons r2_n2_11 (rejectCons r2_n2_12 (rejectCons r2_n2_13 (rejectCons r2_n2_16 (rejectNil 5)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_22 : ¬ attainable 6 n1_22 := by
  exact stepCover [n2_7, n2_8, n2_11, n2_12, n2_13, n2_16] (by decide +kernel) (rejectCons r2_n2_7 (rejectCons r2_n2_8 (rejectCons r2_n2_11 (rejectCons r2_n2_12 (rejectCons r2_n2_13 (rejectCons r2_n2_16 (rejectNil 5)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_23 : ¬ attainable 6 n1_23 := by
  exact stepCover [n2_17] (by decide +kernel) (rejectCons r2_n2_17 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_24 : ¬ attainable 6 n1_24 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_25 : ¬ attainable 6 n1_25 := by
  exact stepCover [n2_15] (by decide +kernel) (rejectCons r2_n2_15 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_26 : ¬ attainable 6 n1_26 := by
  exact stepCover [n2_7] (by decide +kernel) (rejectCons r2_n2_7 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_27 : ¬ attainable 6 n1_27 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_28 : ¬ attainable 6 n1_28 := by
  exact stepCover [n2_5, n2_8, n2_10, n2_19, n2_20, n2_29, n2_30, n2_32] (by decide +kernel) (rejectCons r2_n2_5 (rejectCons r2_n2_8 (rejectCons r2_n2_10 (rejectCons r2_n2_19 (rejectCons r2_n2_20 (rejectCons r2_n2_29 (rejectCons r2_n2_30 (rejectCons r2_n2_32 (rejectNil 5)))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_29 : ¬ attainable 6 n1_29 := by
  exact stepCover [n2_8, n2_21] (by decide +kernel) (rejectCons r2_n2_8 (rejectCons r2_n2_21 (rejectNil 5)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_30 : ¬ attainable 6 n1_30 := by
  exact stepCover [n2_8] (by decide +kernel) (rejectCons r2_n2_8 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_31 : ¬ attainable 6 n1_31 := by
  exact stepCover [n2_14] (by decide +kernel) (rejectCons r2_n2_14 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_32 : ¬ attainable 6 n1_32 := by
  exact stepCover [n2_4, n2_8, n2_9, n2_18, n2_22, n2_23, n2_25, n2_27] (by decide +kernel) (rejectCons r2_n2_4 (rejectCons r2_n2_8 (rejectCons r2_n2_9 (rejectCons r2_n2_18 (rejectCons r2_n2_22 (rejectCons r2_n2_23 (rejectCons r2_n2_25 (rejectCons r2_n2_27 (rejectNil 5)))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_33 : ¬ attainable 6 n1_33 := by
  exact stepCover [n2_8] (by decide +kernel) (rejectCons r2_n2_8 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n2_25 : ¬ attainable 6 n2_25 := by
  exact stepCover [n2_4, n2_9, n2_18, n2_23, n2_25, n2_27] (by decide +kernel) (rejectCons r2_n2_4 (rejectCons r2_n2_9 (rejectCons r2_n2_18 (rejectCons r2_n2_23 (rejectCons r2_n2_25 (rejectCons r2_n2_27 (rejectNil 5)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_35 : ¬ attainable 6 n1_35 := by
  exact stepCover [n2_4, n2_9, n2_18, n2_23, n2_25, n2_27] (by decide +kernel) (rejectCons r2_n2_4 (rejectCons r2_n2_9 (rejectCons r2_n2_18 (rejectCons r2_n2_23 (rejectCons r2_n2_25 (rejectCons r2_n2_27 (rejectNil 5)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n2_30 : ¬ attainable 6 n2_30 := by
  exact stepCover [n2_5, n2_10, n2_20, n2_29, n2_30, n2_32] (by decide +kernel) (rejectCons r2_n2_5 (rejectCons r2_n2_10 (rejectCons r2_n2_20 (rejectCons r2_n2_29 (rejectCons r2_n2_30 (rejectCons r2_n2_32 (rejectNil 5)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_37 : ¬ attainable 6 n1_37 := by
  exact stepCover [n2_5, n2_10, n2_20, n2_29, n2_30, n2_32] (by decide +kernel) (rejectCons r2_n2_5 (rejectCons r2_n2_10 (rejectCons r2_n2_20 (rejectCons r2_n2_29 (rejectCons r2_n2_30 (rejectCons r2_n2_32 (rejectNil 5)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_38 : ¬ attainable 6 n1_38 := by
  exact stepCover [n2_11] (by decide +kernel) (rejectCons r2_n2_11 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_39 : ¬ attainable 6 n1_39 := by
  exact stepCover [n2_12] (by decide +kernel) (rejectCons r2_n2_12 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_40 : ¬ attainable 6 n1_40 := by
  exact stepCover [n2_13] (by decide +kernel) (rejectCons r2_n2_13 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r0_wires : ¬ attainable 7 wires := by
  exact stepCover [n1_0, n1_1, n1_2, n1_3, n1_4, n1_5, n1_6, n1_7, n1_8, n1_9, n1_10, n1_11, n1_12, n1_13, n1_14, n1_15, n1_16, n1_17, n1_18, n1_19, n1_20, n1_21, n1_22, n1_23, n1_24, n1_25, n1_26, n1_27, n1_28, n1_29, n1_30, n1_31, n1_32, n1_33, n2_25, n1_35, n2_30, n1_37, n1_38, n1_39, n1_40] (by decide +kernel) (rejectCons r1_n1_0 (rejectCons r1_n1_1 (rejectCons r1_n1_2 (rejectCons r1_n1_3 (rejectCons r1_n1_4 (rejectCons r1_n1_5 (rejectCons r1_n1_6 (rejectCons r1_n1_7 (rejectCons r1_n1_8 (rejectCons r1_n1_9 (rejectCons r1_n1_10 (rejectCons r1_n1_11 (rejectCons r1_n1_12 (rejectCons r1_n1_13 (rejectCons r1_n1_14 (rejectCons r1_n1_15 (rejectCons r1_n1_16 (rejectCons r1_n1_17 (rejectCons r1_n1_18 (rejectCons r1_n1_19 (rejectCons r1_n1_20 (rejectCons r1_n1_21 (rejectCons r1_n1_22 (rejectCons r1_n1_23 (rejectCons r1_n1_24 (rejectCons r1_n1_25 (rejectCons r1_n1_26 (rejectCons r1_n1_27 (rejectCons r1_n1_28 (rejectCons r1_n1_29 (rejectCons r1_n1_30 (rejectCons r1_n1_31 (rejectCons r1_n1_32 (rejectCons r1_n1_33 (rejectCons r1_n2_25 (rejectCons r1_n1_35 (rejectCons r1_n2_30 (rejectCons r1_n1_37 (rejectCons r1_n1_38 (rejectCons r1_n1_39 (rejectCons r1_n1_40 (rejectNil 6))))))))))))))))))))))))))))))))))))))))))

end Depth8

theorem noDepth8 : NoSuffix 18432388630850633676 17348130476094714048 := fun rest o hs hl hr => Depth8.r0_wires (Depth8.suffix rest o hs hl hr)

namespace Reverse8
open CircuitSatBridge FreeSupport
def wires : List Wire := [Depth8.w0, Depth8.w12, Depth8.w18, Depth8.w30, Depth8.w16, Depth8.w38, Depth8.w20, Depth8.w42, Depth8.w1, Depth8.w28]
def test (t : Fin 110) (b : Bool) : Fin 128 :=
  let pts : List (Fin 128) := if b then [74, 21, 82, 41, 37, 74, 42, 41, 82, 82, 21, 41, 37, 37, 41, 42, 21, 84, 84, 74, 42, 74, 84, 37, 41, 82, 21, 21, 74, 41, 21, 37, 42, 37, 84, 37, 42, 84, 74, 42, 84, 82, 42, 41, 21, 82, 82, 84, 74, 74, 37, 1, 2, 41, 42, 64, 84, 82, 74, 21, 4, 41, 42, 37, 41, 74, 84, 32, 37, 21, 82, 8, 2, 42, 1, 68, 5, 34, 18, 34, 18, 68, 20, 17, 9, 17, 33, 10, 36, 72, 66, 9, 10, 66, 36, 33, 40, 40, 34, 80, 72, 36, 5, 9, 72, 8, 32, 0, 41, 32] else [96, 65, 6, 96, 96, 12, 96, 12, 3, 65, 3, 24, 12, 48, 48, 12, 6, 65, 6, 65, 3, 6, 12, 3, 3, 96, 24, 48, 3, 65, 12, 65, 6, 6, 96, 24, 48, 3, 24, 24, 48, 12, 65, 6, 96, 48, 24, 24, 48, 106, 39, 65, 3, 45, 43, 65, 86, 83, 78, 85, 6, 105, 46, 101, 43, 75, 85, 96, 45, 23, 86, 12, 6, 106, 3, 70, 69, 35, 19, 38, 22, 69, 22, 19, 13, 81, 35, 11, 44, 104, 67, 11, 14, 70, 38, 97, 104, 44, 98, 81, 76, 100, 7, 73, 73, 14, 35, 3, 35, 100]
  pts.getD t.val 0
set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem samples : ∀ t : Fin 110, ∀ b : Bool,
   sample wires t b = deepBank 18446727516610621680 18374950366740541440 (test t b) ∧ target (test t b) = !b := by decide +kernel

theorem suffix (rest : List Gate) (o : Nat) (hs : ∀ g ∈ rest, Supported g) (hlen : rest.length ≤ 7)
   (hr : ∀ x : Fin 128, (run rest (deepBank 18446727516610621680 18374950366740541440 x)).getD o false = target x) :
   attainable 7 wires := by
 obtain ⟨cs,hl,hv,he⟩ := fixed_slots 6 10 o rest hs hlen
 refine ⟨cs,16,hl,hv,?_⟩
 intro t
 have h (b : Bool) : (runChoices cs (sample wires t b)).getD 16 false = !b := by
   rw [(samples t b).1, he]
   · exact (hr _).trans (samples t b).2
   · simp [deepBank, otherInputs]
 exact ⟨h false, h true⟩
theorem project (k : Nat) (hs : attainable k wires) : attainable k Depth8.wires := by
  have hm : wires.all (fun w => Depth8.wires.contains w) = true := by decide +kernel
  obtain ⟨cs, o, rfl, _, orient⟩ := hs
  obtain ⟨support, sub, _, det⟩ := bounded_support cs wires.length o
  apply project_suffix sub orient det
  intro i hi
  exact Or.inl (List.contains_iff_mem.mp ((List.all_eq_true.mp hm) _ (List.getElem_mem _)))

end Reverse8

theorem revDepth8 : NoSuffix 18446727516610621680 18374950366740541440 := fun rest o hs hl hr => Depth8.r0_wires (Reverse8.project 7 (Reverse8.suffix rest o hs hl hr))

namespace Depth9
open CircuitSatBridge FreeSupport PEqualNP.CircuitLowerBounds
def w0 := mkSampleWire 0 0 0 0 0 0
def w1 := mkSampleWire 185859152896 77381797896 34293794 0 0 0
def w2 := mkSampleWire 185859152896 81139919880 34565474 65080025996 3758122386 271680
def w3 := mkSampleWire 112239674433 335094384921 115544066 208719944818 317914384481 111345666
def w4 := mkSampleWire 277170758280 452030948422 489727351 221344797098 309623833889 153092466
def w5 := mkSampleWire 567225368886 862307579552 696582796 270737523082 36591134482 159449604
def w6 := mkSampleWire 69256347713 154624266513 273193089 825711656961 154624266252 273193089
def w7 := mkSampleWire 71406067785 158785040725 407412621 877890003461 158516588702 273194637
def w8 := mkSampleWire 160076666930 1047997159552 853072049 828136561777 1047980382317 844683441
def w9 := mkSampleWire 229333014643 1047997159825 853072049 828136561777 1047980382317 844683441
def w10 := mkSampleWire 894301914053 197081898803 897514201 826626027093 160540858572 878639241
def w11 := mkSampleWire 272316341363 1091013941657 922474675 1034431601779 1091013941357 922474675
def wires : List Wire := [w0, w5, w8, w2, w3, w7, w4, w11, w6, w10]
def n1_0 : List Wire := [w1, w3, w7, w4, w5, w8, w10]
def n1_1 : List Wire := [w2, w3, w7, w4, w5, w8, w10]
def n1_2 : List Wire := [w2, w3, w7, w4, w5, w9, w10]
def test (t : Fin 110) (b : Bool) : Fin 128 :=
  let pts : List (Fin 128) := if b then [37, 82, 41, 74, 21, 84, 21, 74, 74, 41, 21, 21, 84, 41, 42, 82, 84, 42, 82, 84, 42, 82, 37, 21, 74, 41, 41, 82, 21, 41, 37, 84, 74, 74, 42, 42, 82, 82, 37, 37, 84, 42, 37, 37, 42, 84, 21, 41, 74, 2, 74, 21, 37, 42, 74, 84, 37, 37, 84, 21, 37, 21, 37, 1, 82, 64, 82, 32, 64, 41, 41, 42, 1, 16, 37, 82, 4, 37, 84, 4, 37, 80, 34, 33, 68, 68, 72, 36, 72, 34, 40, 36, 36, 9, 5, 36, 18, 17, 9, 36, 5, 80, 36, 18, 66, 20, 17, 66, 36, 5] else [48, 6, 3, 96, 6, 6, 48, 65, 3, 65, 24, 12, 12, 96, 3, 24, 24, 96, 3, 65, 12, 96, 6, 65, 6, 24, 12, 65, 3, 48, 12, 96, 12, 24, 6, 24, 48, 12, 65, 3, 48, 65, 96, 24, 48, 3, 96, 6, 48, 3, 75, 29, 38, 106, 106, 92, 39, 52, 85, 23, 45, 85, 44, 3, 86, 65, 90, 96, 96, 105, 43, 43, 65, 24, 53, 83, 12, 101, 86, 6, 100, 88, 98, 35, 69, 76, 73, 39, 104, 35, 104, 44, 53, 73, 13, 101, 26, 25, 11, 45, 69, 81, 52, 22, 67, 28, 81, 98, 100, 7]
  pts.getD t.val 0

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem samples : ∀ t : Fin 110, ∀ b : Bool,
   sample wires t b = deepBank 18432388630850633676 18432107379212156928 (test t b) ∧ target (test t b) = !b := by decide +kernel

theorem suffix (rest : List Gate) (o : Nat) (hs : ∀ g ∈ rest, Supported g) (hlen : rest.length ≤ 7)
   (hr : ∀ x : Fin 128, (run rest (deepBank 18432388630850633676 18432107379212156928 x)).getD o false = target x) :
   attainable 7 wires := by
 obtain ⟨cs,hl,hv,he⟩ := fixed_slots 6 10 o rest hs hlen
 refine ⟨cs,16,hl,hv,?_⟩
 intro t
 have h (b : Bool) : (runChoices cs (sample wires t b)).getD 16 false = !b := by
   rw [(samples t b).1, he]
   · exact (hr _).trans (samples t b).2
   · simp [deepBank, otherInputs]
 exact ⟨h false, h true⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_0 : ¬ attainable 6 n1_0 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_1 : ¬ attainable 6 n1_1 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_2 : ¬ attainable 6 n1_2 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r0_wires : ¬ attainable 7 wires := by
  exact stepCover [n1_0, n1_1, n1_2] (by decide +kernel) (rejectCons r1_n1_0 (rejectCons r1_n1_1 (rejectCons r1_n1_2 (rejectNil 6))))

end Depth9

theorem noDepth9 : NoSuffix 18432388630850633676 18432107379212156928 := fun rest o hs hl hr => Depth9.r0_wires (Depth9.suffix rest o hs hl hr)

namespace Reverse9
open CircuitSatBridge FreeSupport
def wires : List Wire := [Depth9.w0, Depth9.w4, Depth9.w7, Depth9.w3, Depth9.w2, Depth9.w8, Depth9.w5, Depth9.w11, Depth9.w6, Depth9.w10]
def test (t : Fin 110) (b : Bool) : Fin 128 :=
  let pts : List (Fin 128) := if b then [37, 74, 21, 82, 41, 42, 41, 82, 82, 21, 41, 41, 42, 21, 84, 74, 42, 84, 74, 42, 84, 74, 37, 41, 82, 21, 21, 74, 41, 21, 37, 42, 82, 82, 84, 84, 74, 74, 37, 37, 42, 84, 37, 37, 84, 42, 41, 21, 82, 64, 82, 41, 37, 84, 82, 42, 37, 37, 42, 41, 37, 41, 37, 1, 74, 2, 74, 4, 2, 21, 21, 84, 1, 8, 37, 74, 32, 37, 42, 32, 37, 10, 68, 5, 34, 34, 18, 36, 18, 68, 20, 36, 36, 17, 33, 36, 72, 9, 17, 36, 33, 10, 36, 72, 66, 40, 9, 66, 36, 33] else [12, 96, 65, 6, 96, 96, 12, 3, 65, 3, 24, 48, 48, 6, 65, 24, 24, 6, 65, 3, 48, 6, 96, 3, 96, 24, 48, 3, 65, 12, 48, 6, 48, 24, 96, 24, 12, 48, 3, 65, 12, 3, 6, 24, 12, 65, 6, 96, 12, 65, 83, 57, 100, 86, 86, 58, 101, 44, 43, 105, 53, 43, 52, 65, 106, 3, 90, 6, 6, 23, 85, 85, 3, 24, 45, 75, 48, 39, 106, 96, 38, 26, 70, 69, 35, 50, 19, 101, 22, 69, 22, 52, 45, 19, 49, 39, 88, 25, 81, 53, 35, 11, 44, 104, 67, 56, 11, 70, 38, 97]
  pts.getD t.val 0
set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem samples : ∀ t : Fin 110, ∀ b : Bool,
   sample wires t b = deepBank 18446727516610621680 14757382013288497344 (test t b) ∧ target (test t b) = !b := by decide +kernel

theorem suffix (rest : List Gate) (o : Nat) (hs : ∀ g ∈ rest, Supported g) (hlen : rest.length ≤ 7)
   (hr : ∀ x : Fin 128, (run rest (deepBank 18446727516610621680 14757382013288497344 x)).getD o false = target x) :
   attainable 7 wires := by
 obtain ⟨cs,hl,hv,he⟩ := fixed_slots 6 10 o rest hs hlen
 refine ⟨cs,16,hl,hv,?_⟩
 intro t
 have h (b : Bool) : (runChoices cs (sample wires t b)).getD 16 false = !b := by
   rw [(samples t b).1, he]
   · exact (hr _).trans (samples t b).2
   · simp [deepBank, otherInputs]
 exact ⟨h false, h true⟩
theorem project (k : Nat) (hs : attainable k wires) : attainable k Depth9.wires := by
  have hm : wires.all (fun w => Depth9.wires.contains w) = true := by decide +kernel
  obtain ⟨cs, o, rfl, _, orient⟩ := hs
  obtain ⟨support, sub, _, det⟩ := bounded_support cs wires.length o
  apply project_suffix sub orient det
  intro i hi
  exact Or.inl (List.contains_iff_mem.mp ((List.all_eq_true.mp hm) _ (List.getElem_mem _)))

end Reverse9

theorem revDepth9 : NoSuffix 18446727516610621680 14757382013288497344 := fun rest o hs hl hr => Depth9.r0_wires (Reverse9.project 7 (Reverse9.suffix rest o hs hl hr))

namespace Depth10
open CircuitSatBridge FreeSupport PEqualNP.CircuitLowerBounds
def w0 := mkSampleWire 0 0 0 0 0 0
def w1 := mkSampleWire 618878501395 141884928054 134220865 0 0 0
def w2 := mkSampleWire 2156146688 9131035657 271655168 0 0 0
def w3 := mkSampleWire 49405047808 352770886921 322773270 0 0 0
def w4 := mkSampleWire 756369883927 694059152054 683839169 0 0 0
def w5 := mkSampleWire 49405047808 374262525705 322810646 869762779824 296411489926 51417618
def w6 := mkSampleWire 618475814913 596065128470 69362688 154954366977 596065128705 69362688
def w7 := mkSampleWire 293736696040 617641767488 69368938 189343910033 600394789767 69368938
def w8 := mkSampleWire 912212510953 617641767510 69368938 189343910033 600394789767 69368938
def w9 := mkSampleWire 618878501395 159140835382 134483067 942781399786 159006605452 134481979
def w10 := mkSampleWire 155745141036 706885929664 701666212 910031921774 154712016952 160433028
def w11 := mkSampleWire 774623642431 711315127030 701669349 910031921774 154712016952 160433028
def w12 := mkSampleWire 774623642431 711315127030 701931519 944392086254 159007000764 160697279
def w13 := mkSampleWire 912615197435 755106411126 203848827 1097765145339 755106411407 203848827
def w14 := mkSampleWire 620631961601 596604394527 343106944 156700849413 596604393841 342058368
def w15 := mkSampleWire 914368657641 618181033567 343113194 191090392469 600934054903 342064618
def w16 := mkSampleWire 756369883927 738120348342 787214017 155119541521 596369257283 644604992
def w17 := mkSampleWire 322731838656 516582836480 931938334 74794480974 206228457592 814481412
def w18 := mkSampleWire 324887985344 525713837321 935158046 74794480974 206228457592 814481412
def w19 := mkSampleWire 943363800257 1077751356703 939484574 229748847951 802830457209 888104324
def wires : List Wire := [w0, w9, w14, w5, w17, w7, w10, w13, w6, w16]
def n1_0 : List Wire := [w7, w1, w5, w14, w10, w16, w17]
def n1_1 : List Wire := [w7, w5, w14, w10, w12, w16, w17]
def n1_2 : List Wire := [w7, w9, w2, w5, w10, w16, w17]
def n1_3 : List Wire := [w7, w9, w5, w10, w16, w17, w19]
def n1_4 : List Wire := [w7, w9, w5, w14, w10, w16, w17]
def n1_5 : List Wire := [w8, w9, w5, w14, w10, w16, w17]
def n1_6 : List Wire := [w9, w5, w15, w10, w16, w17]
def n2_0 : List Wire := [w7, w5, w14, w4, w10, w17]
def n2_1 : List Wire := [w7, w5, w14, w11, w16, w17]
def n2_2 : List Wire := [w7, w9, w3, w10, w16, w17]
def n2_3 : List Wire := [w7, w9, w5, w10, w16, w18]
def test (t : Fin 110) (b : Bool) : Fin 128 :=
  let pts : List (Fin 128) := if b then [37, 82, 84, 82, 41, 74, 82, 42, 21, 74, 21, 41, 21, 84, 41, 42, 84, 42, 42, 21, 21, 74, 41, 41, 41, 82, 37, 21, 37, 84, 84, 74, 82, 74, 37, 42, 82, 37, 74, 74, 37, 41, 42, 82, 84, 84, 21, 42, 37, 41, 8, 84, 37, 41, 42, 21, 32, 64, 84, 82, 32, 21, 37, 74, 74, 41, 82, 37, 1, 4, 37, 37, 42, 37, 74, 37, 16, 82, 8, 37, 2, 42, 80, 34, 10, 34, 33, 68, 68, 72, 36, 34, 40, 36, 36, 9, 5, 36, 18, 17, 72, 36, 5, 80, 72, 9, 36, 66, 20, 17] else [6, 3, 65, 96, 3, 96, 48, 48, 65, 3, 24, 48, 12, 12, 96, 3, 24, 96, 12, 6, 48, 65, 24, 12, 65, 65, 48, 3, 3, 48, 96, 12, 24, 24, 96, 24, 6, 65, 48, 6, 12, 6, 6, 12, 6, 3, 96, 65, 24, 105, 12, 92, 38, 43, 106, 29, 96, 65, 85, 90, 48, 85, 44, 90, 75, 57, 114, 39, 65, 12, 52, 100, 43, 45, 106, 53, 24, 83, 24, 101, 3, 58, 88, 50, 26, 98, 35, 69, 76, 73, 39, 35, 104, 44, 53, 73, 13, 101, 26, 25, 76, 45, 69, 81, 88, 25, 52, 67, 28, 81]
  pts.getD t.val 0

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem samples : ∀ t : Fin 110, ∀ b : Bool,
   sample wires t b = deepBank 18446650250148948650 14757320200119158920 (test t b) ∧ target (test t b) = !b := by decide +kernel

theorem suffix (rest : List Gate) (o : Nat) (hs : ∀ g ∈ rest, Supported g) (hlen : rest.length ≤ 7)
   (hr : ∀ x : Fin 128, (run rest (deepBank 18446650250148948650 14757320200119158920 x)).getD o false = target x) :
   attainable 7 wires := by
 obtain ⟨cs,hl,hv,he⟩ := fixed_slots 6 10 o rest hs hlen
 refine ⟨cs,16,hl,hv,?_⟩
 intro t
 have h (b : Bool) : (runChoices cs (sample wires t b)).getD 16 false = !b := by
   rw [(samples t b).1, he]
   · exact (hr _).trans (samples t b).2
   · simp [deepBank, otherInputs]
 exact ⟨h false, h true⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_0 : ¬ attainable 5 n2_0 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_1 : ¬ attainable 5 n2_1 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_2 : ¬ attainable 5 n2_2 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r2_n2_3 : ¬ attainable 5 n2_3 := by
  exact stepCover [] (by decide +kernel) (rejectNil 4)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_0 : ¬ attainable 6 n1_0 := by
  exact stepCover [n2_1] (by decide +kernel) (rejectCons r2_n2_1 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_1 : ¬ attainable 6 n1_1 := by
  exact stepCover [n2_0] (by decide +kernel) (rejectCons r2_n2_0 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_2 : ¬ attainable 6 n1_2 := by
  exact stepCover [n2_3] (by decide +kernel) (rejectCons r2_n2_3 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_3 : ¬ attainable 6 n1_3 := by
  exact stepCover [n2_2] (by decide +kernel) (rejectCons r2_n2_2 (rejectNil 5))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_4 : ¬ attainable 6 n1_4 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_5 : ¬ attainable 6 n1_5 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_6 : ¬ attainable 6 n1_6 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r0_wires : ¬ attainable 7 wires := by
  exact stepCover [n1_0, n1_1, n1_2, n1_3, n1_4, n1_5, n1_6] (by decide +kernel) (rejectCons r1_n1_0 (rejectCons r1_n1_1 (rejectCons r1_n1_2 (rejectCons r1_n1_3 (rejectCons r1_n1_4 (rejectCons r1_n1_5 (rejectCons r1_n1_6 (rejectNil 6))))))))

end Depth10

theorem noDepth10 : NoSuffix 18446650250148948650 14757320200119158920 := fun rest o hs hl hr => Depth10.r0_wires (Depth10.suffix rest o hs hl hr)

namespace Reverse10
open CircuitSatBridge FreeSupport
def wires : List Wire := [Depth10.w0, Depth10.w10, Depth10.w7, Depth10.w17, Depth10.w5, Depth10.w14, Depth10.w9, Depth10.w13, Depth10.w6, Depth10.w16]
def test (t : Fin 110) (b : Bool) : Fin 128 :=
  let pts : List (Fin 128) := if b then [37, 74, 42, 74, 21, 82, 74, 84, 41, 82, 41, 21, 41, 42, 21, 84, 42, 84, 84, 41, 41, 82, 21, 21, 21, 74, 37, 41, 37, 42, 42, 82, 74, 82, 37, 84, 74, 37, 82, 82, 37, 21, 84, 74, 42, 42, 41, 84, 37, 21, 16, 42, 37, 21, 84, 41, 4, 2, 42, 74, 4, 41, 37, 82, 82, 21, 74, 37, 1, 32, 37, 37, 84, 37, 82, 37, 8, 74, 16, 37, 64, 84, 10, 68, 80, 68, 5, 34, 34, 18, 36, 68, 20, 36, 36, 17, 33, 36, 72, 9, 18, 36, 33, 10, 18, 17, 36, 66, 40, 9] else [96, 65, 3, 6, 65, 6, 12, 12, 3, 65, 24, 12, 48, 48, 6, 65, 24, 6, 48, 96, 12, 3, 24, 48, 3, 3, 12, 65, 65, 12, 6, 48, 24, 24, 6, 24, 96, 3, 12, 96, 48, 96, 96, 48, 96, 65, 6, 3, 24, 23, 48, 58, 100, 85, 86, 57, 6, 3, 43, 90, 12, 43, 52, 90, 83, 29, 78, 101, 3, 48, 44, 38, 85, 53, 86, 45, 24, 75, 24, 39, 65, 92, 26, 76, 88, 70, 69, 35, 50, 19, 101, 69, 22, 52, 45, 19, 49, 39, 88, 25, 50, 53, 35, 11, 26, 25, 44, 67, 56, 11]
  pts.getD t.val 0
set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem samples : ∀ t : Fin 110, ∀ b : Bool,
   sample wires t b = deepBank 18446744072850558156 18446462602168762368 (test t b) ∧ target (test t b) = !b := by decide +kernel

theorem suffix (rest : List Gate) (o : Nat) (hs : ∀ g ∈ rest, Supported g) (hlen : rest.length ≤ 7)
   (hr : ∀ x : Fin 128, (run rest (deepBank 18446744072850558156 18446462602168762368 x)).getD o false = target x) :
   attainable 7 wires := by
 obtain ⟨cs,hl,hv,he⟩ := fixed_slots 6 10 o rest hs hlen
 refine ⟨cs,16,hl,hv,?_⟩
 intro t
 have h (b : Bool) : (runChoices cs (sample wires t b)).getD 16 false = !b := by
   rw [(samples t b).1, he]
   · exact (hr _).trans (samples t b).2
   · simp [deepBank, otherInputs]
 exact ⟨h false, h true⟩
theorem project (k : Nat) (hs : attainable k wires) : attainable k Depth10.wires := by
  have hm : wires.all (fun w => Depth10.wires.contains w) = true := by decide +kernel
  obtain ⟨cs, o, rfl, _, orient⟩ := hs
  obtain ⟨support, sub, _, det⟩ := bounded_support cs wires.length o
  apply project_suffix sub orient det
  intro i hi
  exact Or.inl (List.contains_iff_mem.mp ((List.all_eq_true.mp hm) _ (List.getElem_mem _)))

end Reverse10

theorem revDepth10 : NoSuffix 18446744072850558156 18446462602168762368 := fun rest o hs hl hr => Depth10.r0_wires (Reverse10.project 7 (Reverse10.suffix rest o hs hl hr))

namespace Depth11
open CircuitSatBridge FreeSupport PEqualNP.CircuitLowerBounds
def w0 := mkSampleWire 0 0 0 0 0 0
def w1 := mkSampleWire 12826920448 146029151232 77596688 0 0 0
def w2 := mkSampleWire 0 154677578240 1116288 68719729408 154635635591 67712
def w3 := mkSampleWire 481040531515 104924247838 135183820 894846775177 36132394154 666056
def w4 := mkSampleWire 30804433920 439353380384 66136192 893622157056 439319826319 65087616
def w5 := mkSampleWire 3551109888 154677971520 68537489 249112025856 154669583255 68537489
def w6 := mkSampleWire 34355543808 439353773664 133557393 1074014453504 439353773983 133557393
def w7 := mkSampleWire 584168022468 677959128257 828982059 845559375065 106711569448 292028712
def w8 := mkSampleWire 584119746766 711322221215 851863166 185232642086 708771457877 579094038
def w9 := mkSampleWire 502512490545 381755287840 790140822 204664733814 70904930384 739284502
def w10 := mkSampleWire 1065156083967 660157854111 940184430 25497174271 660157853792 940184430
def w11 := mkSampleWire 1077983004415 806187005343 1017781118 25497174271 660157853792 940184430
def wires : List Wire := [w0, w5, w7, w8, w3, w9, w4, w6, w10, w11]
def n1_0 : List Wire := [w2, w3, w9, w7, w8, w11]
def n1_1 : List Wire := [w4, w5, w1, w3, w9, w7, w8]
def n1_2 : List Wire := [w4, w5, w3, w9, w7, w8, w11]
def test (t : Fin 110) (b : Bool) : Fin 128 :=
  let pts : List (Fin 128) := if b then [21, 41, 41, 21, 37, 41, 37, 21, 82, 82, 84, 82, 74, 84, 74, 74, 74, 82, 84, 42, 42, 42, 37, 41, 21, 37, 37, 21, 84, 41, 21, 37, 41, 42, 37, 42, 82, 42, 84, 84, 74, 82, 74, 84, 42, 21, 41, 82, 74, 74, 84, 74, 21, 41, 37, 82, 37, 42, 2, 16, 9, 16, 33, 84, 82, 42, 8, 84, 5, 17, 84, 37, 8, 64, 74, 21, 37, 74, 64, 9, 2, 41, 41, 21, 42, 4, 17, 82, 21, 41, 42, 82, 32, 80, 10, 34, 66, 16, 10, 20, 34, 68, 68, 72, 68, 72, 34, 32, 4, 40] else [48, 24, 12, 24, 48, 48, 12, 12, 6, 3, 65, 96, 96, 6, 65, 6, 3, 65, 96, 3, 96, 6, 24, 3, 6, 6, 65, 65, 3, 65, 3, 3, 96, 65, 96, 12, 48, 48, 48, 12, 12, 24, 24, 24, 24, 96, 6, 12, 48, 90, 85, 106, 28, 56, 52, 90, 45, 46, 3, 24, 24, 48, 48, 86, 86, 106, 24, 92, 12, 48, 116, 44, 12, 65, 78, 52, 53, 75, 96, 12, 6, 44, 57, 29, 43, 12, 24, 114, 53, 45, 58, 83, 48, 88, 14, 50, 70, 25, 26, 53, 98, 69, 76, 73, 100, 104, 35, 49, 13, 45]
  pts.getD t.val 0

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem samples : ∀ t : Fin 110, ∀ b : Bool,
   sample wires t b = deepBank 18446744072277895850 1431655765 (test t b) ∧ target (test t b) = !b := by decide +kernel

theorem suffix (rest : List Gate) (o : Nat) (hs : ∀ g ∈ rest, Supported g) (hlen : rest.length ≤ 7)
   (hr : ∀ x : Fin 128, (run rest (deepBank 18446744072277895850 1431655765 x)).getD o false = target x) :
   attainable 7 wires := by
 obtain ⟨cs,hl,hv,he⟩ := fixed_slots 6 10 o rest hs hlen
 refine ⟨cs,16,hl,hv,?_⟩
 intro t
 have h (b : Bool) : (runChoices cs (sample wires t b)).getD 16 false = !b := by
   rw [(samples t b).1, he]
   · exact (hr _).trans (samples t b).2
   · simp [deepBank, otherInputs]
 exact ⟨h false, h true⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_0 : ¬ attainable 6 n1_0 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_1 : ¬ attainable 6 n1_1 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r1_n1_2 : ¬ attainable 6 n1_2 := by
  exact stepCover [] (by decide +kernel) (rejectNil 5)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem r0_wires : ¬ attainable 7 wires := by
  exact stepCover [n1_0, n1_1, n1_2] (by decide +kernel) (rejectCons r1_n1_0 (rejectCons r1_n1_1 (rejectCons r1_n1_2 (rejectNil 6))))

end Depth11

theorem noDepth11 : NoSuffix 18446744072277895850 1431655765 := fun rest o hs hl hr => Depth11.r0_wires (Depth11.suffix rest o hs hl hr)
end PEqualNP.Outside.L_meta_29892_aux.DepthBridge
namespace PEqualNP.Outside.L_meta_29892_aux.DepthBridge
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_29892_aux PEqualNP.Outside.L_meta_29892_aux.CircuitSatBridge
theorem specialReady (f h : Nat) (hs : (f,h) ∈ specialMasks) : NoSuffix f h := by
  simp only [specialMasks,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hs
  rcases hs with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact noDepth0
  · exact revDepth0
  · exact noDepth1
  · exact noDepth2
  · exact noDepth3
  · exact noDepth4
  · exact noDepth5
  · exact revDepth5
  · exact noDepth6
  · exact revDepth6
  · exact revDepth4
  · exact revDepth3
  · exact noDepth7
  · exact revDepth2
  · exact revDepth1
  · exact noDepth8
  · exact noDepth9
  · exact noDepth10
  · exact revDepth9
  · exact revDepth8
  · exact noDepth11
  · exact revDepth10
  · exact revDepth7
end PEqualNP.Outside.L_meta_29892_aux.DepthBridge
set_option maxHeartbeats 12000000 in
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_29892_aux.DepthBridge PEqualNP.Outside.L_meta_29892_aux PEqualNP.Outside.L_meta_29892_aux.CircuitSatBridge in
theorem PEqualNP.Outside.L_meta_29892 : ¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 7 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 8 ∈ (C.gates.get i).inputs ∧ 8 ≠ 0 ∧ 8 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 8 false = true) := by
  rintro ⟨⟨gs,o⟩,i,k,hi,hf,sz,hrep,hm0,hu,hor,_,_,_,hm8,_,_,hw⟩
  change gs.length = 10 at sz
  rcases gs with _ | ⟨g0,gs⟩
  · simp at sz
  rcases gs with _ | ⟨g1,gs⟩
  · simp at sz
  rcases gs with _ | ⟨g2,gs⟩
  · simp at sz
  rcases gs with _ | ⟨g3,gs⟩
  · simp at sz
  rcases gs with _ | ⟨g4,gs⟩
  · simp at sz
  rcases gs with _ | ⟨g5,gs⟩
  · simp at sz
  rcases gs with _ | ⟨g6,gs⟩
  · simp at sz
  rcases gs with _ | ⟨g7,rest⟩
  · simp at sz
  have hs (g : Gate) (hg : g ∈ g0 :: g1 :: g2 :: g3 :: g4 :: g5 :: g6 :: g7 :: rest) : Supported g := hf g hg
  have hi' : i = ⟨7,by simp⟩ := Fin.ext hi
  subst i
  change 0 ∈ g7.inputs at hm0
  change 8 ∈ g7.inputs at hm8
  change g7.op = .or at hor
  have nz0 : 0 ∉ g0.inputs := by
    intro hz
    have bad := congrArg Fin.val (hu ⟨0,by simp⟩ hz)
    change 0 = 7 at bad
    omega
  have nz1 : 0 ∉ g1.inputs := by
    intro hz
    have bad := congrArg Fin.val (hu ⟨1,by simp⟩ hz)
    change 1 = 7 at bad
    omega
  have nz2 : 0 ∉ g2.inputs := by
    intro hz
    have bad := congrArg Fin.val (hu ⟨2,by simp⟩ hz)
    change 2 = 7 at bad
    omega
  have nz3 : 0 ∉ g3.inputs := by
    intro hz
    have bad := congrArg Fin.val (hu ⟨3,by simp⟩ hz)
    change 3 = 7 at bad
    omega
  have nz4 : 0 ∉ g4.inputs := by
    intro hz
    have bad := congrArg Fin.val (hu ⟨4,by simp⟩ hz)
    change 4 = 7 at bad
    omega
  have nz5 : 0 ∉ g5.inputs := by
    intro hz
    have bad := congrArg Fin.val (hu ⟨5,by simp⟩ hz)
    change 5 = 7 at bad
    omega
  have nz6 : 0 ∉ g6.inputs := by
    intro hz
    have bad := congrArg Fin.val (hu ⟨6,by simp⟩ hz)
    change 6 = 7 at bad
    omega
  have npre (g : Gate) (hg : g ∈ [g2,g3,g4,g5,g6]) : 0 ∉ g.inputs := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl|rfl|rfl|rfl|rfl
    · exact nz2
    · exact nz3
    · exact nz4
    · exact nz5
    · exact nz6
  have spre (g : Gate) (hg : g ∈ [g2,g3,g4,g5,g6]) : Supported g := by
    apply hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hg ⊢
    tauto
  have ns (g : Gate) (hg : g ∈ rest) : 0 ∉ g.inputs := by
    intro hz
    obtain ⟨j,he⟩ := List.get_of_mem hg
    have bad := congrArg Fin.val (hu j.succ.succ.succ.succ.succ.succ.succ.succ (he ▸ hz))
    change j.val+1+1+1+1+1+1+1+1 = 7 at bad
    omega
  have ss (g : Gate) (hg : g ∈ rest) : Supported g := hs _ (by simp [hg])
  let c0 := normalize 7 g0
  let c1 := normalize 8 g1
  have leg0 := normalize_legal 7 g0
  have leg1 := normalize_legal 8 g1
  let l : Fin 8 := ⟨c0.2.1,lt_of_le_of_lt leg0.1 (by decide : 7 < 8)⟩
  let r : Fin 8 := ⟨c0.2.2,lt_of_le_of_lt leg0.2.1 (by decide : 7 < 8)⟩
  let s : Fin 9 := ⟨c1.2.1,lt_of_le_of_lt leg1.1 (by decide : 8 < 9)⟩
  let t : Fin 9 := ⟨c1.2.2,lt_of_le_of_lt leg1.2.1 (by decide : 8 < 9)⟩
  let f := nextMask 0 c0.1 l r
  let h := nextMask f c1.1 s t
  have fit (x : Fin 128) : gval g0 (false :: otherInputs x) = val f x :=
    (normalize_correct _ g0 (hs _ (by simp))).symm.trans (firstValue x c0.1 l r).symm
  have first (x : Fin 128) : gval g0 (x.val.testBit 0 :: otherInputs x) = val f x :=
    (skipZero _ _ _ nz0).trans (fit x)
  have second (x : Fin 128) : gval g1 ((x.val.testBit 0 :: otherInputs x) ++ [val f x]) = val h x := by
    change gval g1 (x.val.testBit 0 :: (otherInputs x ++ [val f x])) = _
    rw [skipZero _ _ _ nz1]
    exact (normalize_correct _ g1 (hs _ (by simp))).symm.trans (secondValue x f c1.1 s t).symm
  have on : o ≠ 0 := by
    intro hz
    have eq := hrep (bitfn 1)
    change (run _ _).getD o false = false at eq
    rw [hz,ofFn_bits,keepWire _ _ _ (by simp)] at eq
    contradiction
  obtain ⟨tail,out,tl,supp,trans⟩ := MoveOr.accelerateEight [g2,g3,g4,g5,g6] rest o on npre ns spre ss
  have tlen : tail.length ≤ 7 := by simp at sz tl; omega
  have preRuns (x : Fin 128) : (run (g0 :: g1 :: g2 :: g3 :: g4 :: g5 :: g6 :: g7 :: rest) (List.ofFn (bitfn x))).getD o false =
      (run rest ((run [g2,g3,g4,g5,g6] (x.val.testBit 0 :: (otherInputs x ++ [val f x,val h x]))) ++ [x.val.testBit 0 || val h x])).getD o false := by
    let w := x.val.testBit 0 :: (otherInputs x ++ [val f x,val h x])
    have out0 : (run [g2,g3,g4,g5,g6] w).getD 0 false = x.val.testBit 0 := by rw [keepWire _ _ _ (by simp [w])]; rfl
    have out8 : (run [g2,g3,g4,g5,g6] w).getD 8 false = val h x := by rw [keepWire _ _ _ (by simp [w,otherInputs])]; rfl
    have gg : gval g7 (run [g2,g3,g4,g5,g6] w) = (x.val.testBit 0 || val h x) := by
      rw [orEight _ _ hor (onlyTwoEight _ (hs _ (by simp)).2 hm0 hm8), out0, out8]
    rw [ofFn_bits]
    let w0 := x.val.testBit 0 :: otherInputs x
    let w1 := w0 ++ [gval g0 w0]
    change (run ([g2,g3,g4,g5,g6] ++ (g7 :: rest)) (w1 ++ [gval g1 w1])).getD o false = _
    dsimp only [w1,w0]
    rw [first,second,MoveOr.run_cat]
    change (run rest ((run [g2,g3,g4,g5,g6] w) ++ [gval g7 (run [g2,g3,g4,g5,g6] w)])).getD o false = _
    rw [gg]
  have hr (x : Fin 128) : (run tail (deepBank f h x)).getD out false = target x := by
    have hh := hrep (bitfn x)
    change (run _ _).getD o false = target x at hh
    change (run tail (false :: ((otherInputs x ++ [val f x,val h x]) ++ [x.val.testBit 0 || val h x]))).getD out false = _
    rw [trans _ _ _ (by simp [otherInputs]), ← preRuns]
    exact hh
  obtain ⟨z,hz0,hz1,hz6,hz8⟩ := hw
  obtain ⟨x,rfl⟩ := bits_cover z
  change (run (g0 :: g1 :: g2 :: g3 :: g4 :: g5 :: g6 :: g7 :: rest) _).getD 8 false = true at hz8
  rw [ofFn_bits] at hz8
  let w0 := x.val.testBit 0 :: otherInputs x
  let w1 := w0 ++ [gval g0 w0]
  change (run (g2 :: g3 :: g4 :: g5 :: g6 :: g7 :: rest) (w1 ++ [gval g1 w1])).getD 8 false = true at hz8
  dsimp only [w1,w0] at hz8
  rw [first,second,keepWire _ _ _ (by simp [otherInputs])] at hz8
  have side := zerosHit h x hz0 hz1 hz6 hz8
  have sep := cannotSeparate f h tail out hr
  have check : allowed f h = true := covered c0.1 l r c1.1 s t
  have options : h ∈ simpleMasks ∨ (f,h) ∈ specialMasks := by
    simpa [allowed,side,sep,List.contains_iff_mem] using check
  rcases options with sh|pair
  · obtain ⟨a,b,he,no⟩ := simpleTo h sh
    exact replayMasked a b f h g0 nz0 (hs _ (by simp)) fit he no tail out supp tlen hr
  · exact specialReady f h pair tail out supp tlen hr
