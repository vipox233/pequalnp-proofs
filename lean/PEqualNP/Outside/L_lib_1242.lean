import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1242_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wireVal (gs : List Gate) (x : List Bool) (i : ℕ) : Bool :=
  (gs.foldl stepWire x).getD i false

def isNotGate (g : Gate) : Bool :=
  match g.op with
  | GateOp.not => true
  | _ => false

def nonNotCount (gs : List Gate) : ℕ :=
  (gs.filter fun g => !isNotGate g).length

lemma foldl_stepWire_length (gs : List Gate) (x : List Bool) :
    (gs.foldl stepWire x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
      simp [List.foldl_cons, ih, stepWire]
      omega

lemma foldl_stepWire_append_exists (gs ext : List Gate) (x : List Bool) :
    ∃ suf, (gs ++ ext).foldl stepWire x = gs.foldl stepWire x ++ suf := by
  rw [List.foldl_append]
  generalize gs.foldl stepWire x = w
  induction ext generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g ext ih =>
      obtain ⟨suf, hsuf⟩ := ih (stepWire w g)
      exact ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ suf, by
        simpa [List.foldl_cons, stepWire, List.append_assoc] using hsuf⟩

lemma wireVal_append_of_lt (gs ext : List Gate) (x : List Bool) (w : ℕ)
    (hw : w < x.length + gs.length) :
    wireVal (gs ++ ext) x w = wireVal gs x w := by
  unfold wireVal
  obtain ⟨suf, hsuf⟩ := foldl_stepWire_append_exists gs ext x
  rw [hsuf]
  have hlen : w < (gs.foldl stepWire x).length := by
    rw [foldl_stepWire_length]
    exact hw
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlen]

lemma wireVal_snoc_self (gs : List Gate) (g : Gate) (x : List Bool) :
    wireVal (gs ++ [g]) x (x.length + gs.length) =
      g.op.eval (g.inputs.map fun i => wireVal gs x i) := by
  unfold wireVal
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil, stepWire]
  have hlen : (gs.foldl stepWire x).length = x.length + gs.length := foldl_stepWire_length gs x
  simp [List.getD_eq_getElem?_getD, hlen]

lemma notCount_cons_of_eq (g : Gate) (gs : List Gate) (h : g.op = GateOp.not) (o : ℕ) :
    notCount (Circuit.mk (g :: gs) o) = notCount (Circuit.mk gs o) + 1 := by
  have hdec : ∀ inst : Decidable (g.op = GateOp.not), @decide (g.op = GateOp.not) inst = true :=
    fun inst => @decide_eq_true (g.op = GateOp.not) inst h
  simp only [notCount, List.filter_cons]
  rw [hdec]
  simp

lemma notCount_cons_of_ne (g : Gate) (gs : List Gate) (h : g.op ≠ GateOp.not) (o : ℕ) :
    notCount (Circuit.mk (g :: gs) o) = notCount (Circuit.mk gs o) := by
  have hdec : ∀ inst : Decidable (g.op = GateOp.not), @decide (g.op = GateOp.not) inst = false :=
    fun inst => @decide_eq_false (g.op = GateOp.not) inst h
  simp only [notCount, List.filter_cons]
  rw [hdec]
  simp

lemma size_sub_notCount (gs : List Gate) (o : ℕ) :
    (Circuit.mk gs o).size - notCount (Circuit.mk gs o) = nonNotCount gs := by
  induction gs with
  | nil => simp [Circuit.size, notCount, nonNotCount]
  | cons g gs ih =>
      by_cases h : g.op = GateOp.not
      · have his : isNotGate g = true := by cases h' : g.op <;> simp_all [isNotGate]
        rw [notCount_cons_of_eq g gs h o]
        simp only [Circuit.size, List.length_cons, nonNotCount, List.filter_cons, his,
          Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        have hle : notCount (Circuit.mk gs o) ≤ gs.length := by
          unfold notCount
          exact List.length_filter_le _ _
        change gs.length - notCount (Circuit.mk gs o) = nonNotCount gs at ih
        change gs.length + 1 - (notCount (Circuit.mk gs o) + 1) = nonNotCount gs
        omega
      · have his : isNotGate g = false := by cases h' : g.op <;> simp_all [isNotGate]
        rw [notCount_cons_of_ne g gs h o]
        simp only [Circuit.size, List.length_cons, nonNotCount, List.filter_cons, his,
          Bool.not_false, ↓reduceIte]
        have hle : notCount (Circuit.mk gs o) ≤ gs.length := by
          unfold notCount
          exact List.length_filter_le _ _
        change gs.length - notCount (Circuit.mk gs o) = nonNotCount gs at ih
        change gs.length + 1 - notCount (Circuit.mk gs o) = nonNotCount gs + 1
        omega

lemma notCount_append (gs ext : List Gate) (o₁ o₂ o₃ : ℕ) :
    notCount (Circuit.mk (gs ++ ext) o₁) =
      notCount (Circuit.mk gs o₂) + notCount (Circuit.mk ext o₃) := by
  simp [notCount, List.filter_append]

lemma nonNotCount_append (gs ext : List Gate) :
    nonNotCount (gs ++ ext) = nonNotCount gs + nonNotCount ext := by
  simp [nonNotCount, List.filter_append]

lemma fanInTwo_append {gs ext : List Gate} {o : ℕ}
    (h1 : FanInTwo (Circuit.mk gs o)) (h2 : FanInTwo (Circuit.mk ext o)) :
    FanInTwo (Circuit.mk (gs ++ ext) o) := by
  intro g hg
  simp only [List.mem_append] at hg
  rcases hg with hg | hg
  · exact h1 g hg
  · exact h2 g hg

lemma readsBack_snoc {N : ℕ} {gs : List Gate} {o : ℕ} {g : Gate}
    (h1 : ReadsBack N (Circuit.mk gs o))
    (h2 : ∀ i ∈ g.inputs, i < N + gs.length) :
    ReadsBack N (Circuit.mk (gs ++ [g]) o) := by
  intro j hj i hi
  simp only [List.length_append, List.length_singleton] at hj
  by_cases hlt : j < gs.length
  · have hgate : gateAt (Circuit.mk (gs ++ [g]) o) j = gateAt (Circuit.mk gs o) j := by
      simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
    rw [hgate] at hi
    exact h1 j hlt i hi
  · have hj_eq : j = gs.length := by omega
    subst hj_eq
    have hgate : gateAt (Circuit.mk (gs ++ [g]) o) gs.length = g := by
      simp [gateAt, List.getD_eq_getElem?_getD]
    rw [hgate] at hi
    exact h2 i hi

lemma eval_and (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

lemma eval_or (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

lemma eval_not (a : Bool) : GateOp.not.eval [a] = !a := by
  cases a <;> rfl

def addAnd (N : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨GateOp.and, [a, b]⟩], N + gs.length)

def addOr (N : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨GateOp.or, [a, b]⟩], N + gs.length)

def addNot (N : ℕ) (gs : List Gate) (a : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨GateOp.not, [a]⟩], N + gs.length)

def foldAux (op : GateOp) (N : ℕ) : List Gate → ℕ → List ℕ → List Gate × ℕ
  | gs, acc, [] => (gs, acc)
  | gs, acc, w :: ws =>
      let gs' := gs ++ [⟨op, [acc, w]⟩]
      foldAux op N gs' (N + gs.length) ws

def foldAnd (N : ℕ) (gs : List Gate) (defWire : ℕ) : List ℕ → List Gate × ℕ
  | [] => (gs, defWire)
  | w :: ws => foldAux GateOp.and N gs w ws

def foldOr (N : ℕ) (gs : List Gate) (defWire : ℕ) : List ℕ → List Gate × ℕ
  | [] => (gs, defWire)
  | w :: ws => foldAux GateOp.or N gs w ws

lemma foldAux_ext (op : GateOp) (N : ℕ) (gs : List Gate) (acc : ℕ) (ws : List ℕ) :
    ∃ ext, (foldAux op N gs acc ws).1 = gs ++ ext ∧ ext.length = ws.length := by
  induction ws generalizing gs acc with
  | nil => exact ⟨[], by simp [foldAux]⟩
  | cons w ws ih =>
      obtain ⟨ext, hext, hlen⟩ := ih (gs ++ [⟨op, [acc, w]⟩]) (N + gs.length)
      exact ⟨⟨op, [acc, w]⟩ :: ext, by simpa [foldAux, List.append_assoc] using hext, by simp [hlen]⟩

lemma foldAux_out_lt (op : GateOp) (N : ℕ) (gs : List Gate) (acc : ℕ) (ws : List ℕ)
    (hacc : acc < N + gs.length) :
    (foldAux op N gs acc ws).2 < N + (foldAux op N gs acc ws).1.length := by
  induction ws generalizing gs acc with
  | nil => simpa [foldAux] using hacc
  | cons w ws ih =>
      simp only [foldAux]
      apply ih
      simp only [List.length_append, List.length_singleton]
      omega

lemma foldAux_fanInTwo (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (N : ℕ) (gs : List Gate) (acc : ℕ) (ws : List ℕ)
    (hgs : FanInTwo (Circuit.mk gs 0)) :
    FanInTwo (Circuit.mk (foldAux op N gs acc ws).1 0) := by
  induction ws generalizing gs acc with
  | nil => simpa [foldAux] using hgs
  | cons w ws ih =>
      simp only [foldAux]
      apply ih
      apply fanInTwo_append hgs
      intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      refine ⟨?_, by simp⟩
      rcases hop with rfl | rfl <;> simp

lemma foldAux_readsBack (op : GateOp) (N : ℕ) (gs : List Gate) (acc : ℕ) (ws : List ℕ)
    (hgs : ReadsBack N (Circuit.mk gs 0))
    (hacc : acc < N + gs.length)
    (hws : ∀ w ∈ ws, w < N + gs.length) :
    ReadsBack N (Circuit.mk (foldAux op N gs acc ws).1 0) := by
  induction ws generalizing gs acc with
  | nil => simpa [foldAux] using hgs
  | cons w ws ih =>
      simp only [foldAux]
      apply ih
      · apply readsBack_snoc hgs
        intro u hu
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
        rcases hu with rfl | rfl
        · exact hacc
        · exact hws _ (by simp)
      · simp only [List.length_append, List.length_singleton]
        omega
      · intro u hu
        have hu' : u < N + gs.length := hws u (by simp [hu])
        simp only [List.length_append, List.length_singleton]
        omega

lemma foldAux_counts (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (N : ℕ) (gs : List Gate) (acc : ℕ) (ws : List ℕ) :
    notCount (Circuit.mk (foldAux op N gs acc ws).1 0) = notCount (Circuit.mk gs 0) ∧
      nonNotCount (foldAux op N gs acc ws).1 = nonNotCount gs + ws.length := by
  induction ws generalizing gs acc with
  | nil => simp [foldAux]
  | cons w ws ih =>
      simp only [foldAux]
      have hsub := ih (gs ++ [⟨op, [acc, w]⟩]) (N + gs.length)
      have hne : op ≠ GateOp.not := by
        rcases hop with rfl | rfl <;> intro heq <;> cases heq
      have his : isNotGate ⟨op, [acc, w]⟩ = false := by
        rcases hop with rfl | rfl <;> rfl
      have hnc : notCount (Circuit.mk (gs ++ [⟨op, [acc, w]⟩]) 0) = notCount (Circuit.mk gs 0) := by
        rw [notCount_append (gs := gs) (ext := [⟨op, [acc, w]⟩]) (o₁ := 0) (o₂ := 0) (o₃ := 0)]
        rw [notCount_cons_of_ne ⟨op, [acc, w]⟩ [] hne 0]
        simp [notCount]
      have hnnc : nonNotCount (gs ++ [⟨op, [acc, w]⟩]) = nonNotCount gs + 1 := by
        rw [nonNotCount_append]
        simp [nonNotCount, his]
      rw [hnc, hnnc] at hsub
      exact ⟨hsub.1, by simp [hsub.2]; omega⟩

lemma foldAux_eval_and (N : ℕ) (gs : List Gate) (acc : ℕ) (ws : List ℕ)
    (x : List Bool) (hx : x.length = N)
    (hacc : acc < N + gs.length)
    (hws : ∀ w ∈ ws, w < N + gs.length) :
    wireVal (foldAux GateOp.and N gs acc ws).1 x (foldAux GateOp.and N gs acc ws).2 = true ↔
      wireVal gs x acc = true ∧ ∀ w ∈ ws, wireVal gs x w = true := by
  induction ws generalizing gs acc with
  | nil => simp [foldAux]
  | cons w ws ih =>
      simp only [foldAux]
      let gs' := gs ++ [⟨GateOp.and, [acc, w]⟩]
      have hacc' : N + gs.length < N + gs'.length := by
        simp [gs']
      have hws' : ∀ u ∈ ws, u < N + gs'.length := by
        intro u hu
        have hu' := hws u (by simp [hu])
        simp [gs']
        omega
      have hih := ih gs' (N + gs.length) hacc' hws'
      rw [hih]
      have hnew : wireVal gs' x (N + gs.length) = (wireVal gs x acc && wireVal gs x w) := by
        have hsnoc := wireVal_snoc_self gs ⟨GateOp.and, [acc, w]⟩ x
        rw [hx] at hsnoc
        simpa [gs', eval_and] using hsnoc
      have hpres : ∀ u ∈ ws, wireVal gs' x u = wireVal gs x u := by
        intro u hu
        exact wireVal_append_of_lt gs [⟨GateOp.and, [acc, w]⟩] x u (by rw [hx]; exact hws u (by simp [hu]))
      constructor
      · rintro ⟨h1, h2⟩
        rw [hnew, Bool.and_eq_true] at h1
        refine ⟨h1.1, ?_⟩
        intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | hu
        · exact h1.2
        · rw [← hpres u hu]
          exact h2 u hu
      · rintro ⟨h1, h2⟩
        refine ⟨?_, ?_⟩
        · rw [hnew, Bool.and_eq_true]
          exact ⟨h1, h2 w (by simp)⟩
        · intro u hu
          rw [hpres u hu]
          exact h2 u (by simp [hu])

lemma foldAux_eval_or (N : ℕ) (gs : List Gate) (acc : ℕ) (ws : List ℕ)
    (x : List Bool) (hx : x.length = N)
    (hacc : acc < N + gs.length)
    (hws : ∀ w ∈ ws, w < N + gs.length) :
    wireVal (foldAux GateOp.or N gs acc ws).1 x (foldAux GateOp.or N gs acc ws).2 = true ↔
      wireVal gs x acc = true ∨ ∃ w ∈ ws, wireVal gs x w = true := by
  induction ws generalizing gs acc with
  | nil => simp [foldAux]
  | cons w ws ih =>
      simp only [foldAux]
      let gs' := gs ++ [⟨GateOp.or, [acc, w]⟩]
      have hacc' : N + gs.length < N + gs'.length := by
        simp [gs']
      have hws' : ∀ u ∈ ws, u < N + gs'.length := by
        intro u hu
        have hu' := hws u (by simp [hu])
        simp [gs']
        omega
      have hih := ih gs' (N + gs.length) hacc' hws'
      rw [hih]
      have hnew : wireVal gs' x (N + gs.length) = (wireVal gs x acc || wireVal gs x w) := by
        have hsnoc := wireVal_snoc_self gs ⟨GateOp.or, [acc, w]⟩ x
        rw [hx] at hsnoc
        simpa [gs', eval_or] using hsnoc
      have hpres : ∀ u ∈ ws, wireVal gs' x u = wireVal gs x u := by
        intro u hu
        exact wireVal_append_of_lt gs [⟨GateOp.or, [acc, w]⟩] x u (by rw [hx]; exact hws u (by simp [hu]))
      constructor
      · rintro (h1 | ⟨u, hu, h2⟩)
        · rw [hnew, Bool.or_eq_true] at h1
          rcases h1 with h1 | h1
          · exact Or.inl h1
          · exact Or.inr ⟨w, by simp, h1⟩
        · rw [hpres u hu] at h2
          exact Or.inr ⟨u, by simp [hu], h2⟩
      · rintro (h1 | ⟨u, hu, h2⟩)
        · left
          rw [hnew, Bool.or_eq_true]
          exact Or.inl h1
        · simp only [List.mem_cons] at hu
          rcases hu with rfl | hu
          · left
            rw [hnew, Bool.or_eq_true]
            exact Or.inr h2
          · right
            exact ⟨u, hu, by rw [hpres u hu]; exact h2⟩

lemma foldAnd_ext (N : ℕ) (gs : List Gate) (defW : ℕ) (ws : List ℕ) :
    ∃ ext, (foldAnd N gs defW ws).1 = gs ++ ext ∧ ext.length ≤ ws.length := by
  cases ws with
  | nil => exact ⟨[], by simp [foldAnd]⟩
  | cons w ws =>
      obtain ⟨ext, hext, hlen⟩ := foldAux_ext GateOp.and N gs w ws
      exact ⟨ext, hext, by simp [hlen]⟩

lemma foldOr_ext (N : ℕ) (gs : List Gate) (defW : ℕ) (ws : List ℕ) :
    ∃ ext, (foldOr N gs defW ws).1 = gs ++ ext ∧ ext.length ≤ ws.length := by
  cases ws with
  | nil => exact ⟨[], by simp [foldOr]⟩
  | cons w ws =>
      obtain ⟨ext, hext, hlen⟩ := foldAux_ext GateOp.or N gs w ws
      exact ⟨ext, hext, by simp [hlen]⟩

lemma foldAnd_out_lt (N : ℕ) (gs : List Gate) (defW : ℕ) (ws : List ℕ)
    (hdef : defW < N + gs.length) (hws : ∀ w ∈ ws, w < N + gs.length) :
    (foldAnd N gs defW ws).2 < N + (foldAnd N gs defW ws).1.length := by
  cases ws with
  | nil => simpa [foldAnd] using hdef
  | cons w ws => exact foldAux_out_lt GateOp.and N gs w ws (hws w (by simp))

lemma foldOr_out_lt (N : ℕ) (gs : List Gate) (defW : ℕ) (ws : List ℕ)
    (hdef : defW < N + gs.length) (hws : ∀ w ∈ ws, w < N + gs.length) :
    (foldOr N gs defW ws).2 < N + (foldOr N gs defW ws).1.length := by
  cases ws with
  | nil => simpa [foldOr] using hdef
  | cons w ws => exact foldAux_out_lt GateOp.or N gs w ws (hws w (by simp))

lemma foldAnd_fanInTwo (N : ℕ) (gs : List Gate) (defW : ℕ) (ws : List ℕ)
    (hgs : FanInTwo (Circuit.mk gs 0)) :
    FanInTwo (Circuit.mk (foldAnd N gs defW ws).1 0) := by
  cases ws with
  | nil => simpa [foldAnd] using hgs
  | cons w ws => exact foldAux_fanInTwo GateOp.and (Or.inl rfl) N gs w ws hgs

lemma foldOr_fanInTwo (N : ℕ) (gs : List Gate) (defW : ℕ) (ws : List ℕ)
    (hgs : FanInTwo (Circuit.mk gs 0)) :
    FanInTwo (Circuit.mk (foldOr N gs defW ws).1 0) := by
  cases ws with
  | nil => simpa [foldOr] using hgs
  | cons w ws => exact foldAux_fanInTwo GateOp.or (Or.inr rfl) N gs w ws hgs

lemma foldAnd_readsBack (N : ℕ) (gs : List Gate) (defW : ℕ) (ws : List ℕ)
    (hgs : ReadsBack N (Circuit.mk gs 0)) (hws : ∀ w ∈ ws, w < N + gs.length) :
    ReadsBack N (Circuit.mk (foldAnd N gs defW ws).1 0) := by
  cases ws with
  | nil => simpa [foldAnd] using hgs
  | cons w ws =>
      exact foldAux_readsBack GateOp.and N gs w ws hgs (hws w (by simp))
        (fun u hu => hws u (by simp [hu]))

lemma foldOr_readsBack (N : ℕ) (gs : List Gate) (defW : ℕ) (ws : List ℕ)
    (hgs : ReadsBack N (Circuit.mk gs 0)) (hws : ∀ w ∈ ws, w < N + gs.length) :
    ReadsBack N (Circuit.mk (foldOr N gs defW ws).1 0) := by
  cases ws with
  | nil => simpa [foldOr] using hgs
  | cons w ws =>
      exact foldAux_readsBack GateOp.or N gs w ws hgs (hws w (by simp))
        (fun u hu => hws u (by simp [hu]))

lemma foldAnd_counts (N : ℕ) (gs : List Gate) (defW : ℕ) (ws : List ℕ) :
    notCount (Circuit.mk (foldAnd N gs defW ws).1 0) = notCount (Circuit.mk gs 0) ∧
      nonNotCount (foldAnd N gs defW ws).1 ≤ nonNotCount gs + ws.length := by
  cases ws with
  | nil => simp [foldAnd]
  | cons w ws =>
      have h := foldAux_counts GateOp.and (Or.inl rfl) N gs w ws
      refine ⟨h.1, ?_⟩
      simp only [foldAnd, h.2, List.length_cons]
      omega

lemma foldOr_counts (N : ℕ) (gs : List Gate) (defW : ℕ) (ws : List ℕ) :
    notCount (Circuit.mk (foldOr N gs defW ws).1 0) = notCount (Circuit.mk gs 0) ∧
      nonNotCount (foldOr N gs defW ws).1 ≤ nonNotCount gs + ws.length := by
  cases ws with
  | nil => simp [foldOr]
  | cons w ws =>
      have h := foldAux_counts GateOp.or (Or.inr rfl) N gs w ws
      refine ⟨h.1, ?_⟩
      simp only [foldOr, h.2, List.length_cons]
      omega

lemma foldAnd_eval (N : ℕ) (gs : List Gate) (defW : ℕ) (ws : List ℕ)
    (x : List Bool) (hx : x.length = N) (hdef : wireVal gs x defW = true)
    (hws : ∀ w ∈ ws, w < N + gs.length) :
    wireVal (foldAnd N gs defW ws).1 x (foldAnd N gs defW ws).2 = true ↔
      ∀ w ∈ ws, wireVal gs x w = true := by
  cases ws with
  | nil => simp [foldAnd, hdef]
  | cons w ws =>
      have h := foldAux_eval_and N gs w ws x hx (hws w (by simp)) (fun u hu => hws u (by simp [hu]))
      simpa [foldAnd] using h

lemma foldOr_eval (N : ℕ) (gs : List Gate) (defW : ℕ) (ws : List ℕ)
    (x : List Bool) (hx : x.length = N) (hdef : wireVal gs x defW = false)
    (hws : ∀ w ∈ ws, w < N + gs.length) :
    wireVal (foldOr N gs defW ws).1 x (foldOr N gs defW ws).2 = true ↔
      ∃ w ∈ ws, wireVal gs x w = true := by
  cases ws with
  | nil => simp [foldOr, hdef]
  | cons w ws =>
      have h := foldAux_eval_or N gs w ws x hx (hws w (by simp)) (fun u hu => hws u (by simp [hu]))
      simpa [foldOr] using h

def buildMap {α : Type*} [DecidableEq α] (f : List Gate → α → List Gate × ℕ) (defW : ℕ) :
    List Gate → List α → List Gate × (α → ℕ)
  | gs, [] => (gs, fun _ => defW)
  | gs, k :: ks =>
      let r1 := f gs k
      let r2 := buildMap f defW r1.1 ks
      (r2.1, fun a => if a = k then r1.2 else r2.2 a)

lemma buildMap_ext {α : Type*} [DecidableEq α] (f : List Gate → α → List Gate × ℕ) (defW : ℕ)
    (Inv : List Gate → Prop)
    (hf : ∀ gs k, Inv gs → ∃ ext, (f gs k).1 = gs ++ ext ∧ Inv (f gs k).1)
    (gs : List Gate) (ks : List α) (hgs : Inv gs) :
    ∃ ext, (buildMap f defW gs ks).1 = gs ++ ext ∧ Inv (buildMap f defW gs ks).1 := by
  induction ks generalizing gs with
  | nil => exact ⟨[], by simp [buildMap], hgs⟩
  | cons k ks ih =>
      obtain ⟨e1, he1, hinv1⟩ := hf gs k hgs
      obtain ⟨e2, he2, hinv2⟩ := ih (f gs k).1 hinv1
      exact ⟨e1 ++ e2, by simp only [buildMap]; rw [he2, he1, List.append_assoc], hinv2⟩

lemma buildMap_counts {α : Type*} [DecidableEq α] (f : List Gate → α → List Gate × ℕ)
    (defW : ℕ) (c : α → ℕ) (Inv : List Gate → Prop)
    (hf_inv : ∀ gs k, Inv gs → Inv (f gs k).1)
    (hf : ∀ gs k, Inv gs →
      notCount (Circuit.mk (f gs k).1 0) = notCount (Circuit.mk gs 0) ∧
      nonNotCount (f gs k).1 ≤ nonNotCount gs + c k)
    (gs : List Gate) (ks : List α) (hgs : Inv gs) :
    notCount (Circuit.mk (buildMap f defW gs ks).1 0) = notCount (Circuit.mk gs 0) ∧
      nonNotCount (buildMap f defW gs ks).1 ≤ nonNotCount gs + (ks.map c).sum := by
  induction ks generalizing gs with
  | nil => simp [buildMap]
  | cons k ks ih =>
      simp only [buildMap, List.map_cons, List.sum_cons]
      have h1 := hf gs k hgs
      have h2 := ih (f gs k).1 (hf_inv gs k hgs)
      refine ⟨h2.1.trans h1.1, ?_⟩
      omega

lemma buildMap_out_lt {α : Type*} [DecidableEq α] (N : ℕ)
    (f : List Gate → α → List Gate × ℕ) (defW : ℕ) (Inv : List Gate → Prop)
    (hf_ext : ∀ gs k, Inv gs → ∃ ext, (f gs k).1 = gs ++ ext ∧ Inv (f gs k).1)
    (hf_out : ∀ gs k, Inv gs → (f gs k).2 < N + (f gs k).1.length)
    (gs : List Gate) (ks : List α) (hgs : Inv gs) (hdef : defW < N + gs.length) :
    ∀ a, (buildMap f defW gs ks).2 a < N + (buildMap f defW gs ks).1.length := by
  induction ks generalizing gs with
  | nil =>
      intro a
      simpa [buildMap] using hdef
  | cons k ks ih =>
      intro a
      simp only [buildMap]
      obtain ⟨e1, he1, hinv1⟩ := hf_ext gs k hgs
      split_ifs with ha
      · obtain ⟨e2, he2, _⟩ := buildMap_ext f defW Inv hf_ext (f gs k).1 ks hinv1
        rw [he2]
        have hlt := hf_out gs k hgs
        simp only [List.length_append]
        omega
      · apply ih (f gs k).1 hinv1
        rw [he1]
        simp only [List.length_append]
        omega

lemma buildMap_eval {α : Type*} [DecidableEq α] (N : ℕ)
    (f : List Gate → α → List Gate × ℕ) (defW : ℕ) (Inv : List Gate → Prop)
    (x : List Bool) (hx : x.length = N) (P : α → Prop)
    (hf_ext : ∀ gs k, Inv gs → ∃ ext, (f gs k).1 = gs ++ ext ∧ Inv (f gs k).1)
    (hf_out : ∀ gs k, Inv gs → (f gs k).2 < N + (f gs k).1.length)
    (hf_eval : ∀ gs k, Inv gs → (wireVal (f gs k).1 x (f gs k).2 = true ↔ P k))
    (gs : List Gate) (ks : List α) (hnodup : ks.Nodup) (hgs : Inv gs) :
    ∀ a ∈ ks, wireVal (buildMap f defW gs ks).1 x ((buildMap f defW gs ks).2 a) = true ↔ P a := by
  induction ks generalizing gs with
  | nil => intro a ha; simp at ha
  | cons k ks ih =>
      intro a ha
      simp only [List.nodup_cons] at hnodup
      obtain ⟨hk_not, hnodup'⟩ := hnodup
      obtain ⟨e1, he1, hinv1⟩ := hf_ext gs k hgs
      simp only [buildMap]
      by_cases hak : a = k
      · subst hak
        simp only [↓reduceIte]
        obtain ⟨e2, he2, _⟩ := buildMap_ext f defW Inv hf_ext (f gs a).1 ks hinv1
        rw [he2, wireVal_append_of_lt _ _ _ _ (by rw [hx]; exact hf_out gs a hgs)]
        exact hf_eval gs a hgs
      · simp only [hak, ↓reduceIte]
        have ha' : a ∈ ks := by
          simp only [List.mem_cons] at ha
          exact ha.resolve_left hak
        exact ih (f gs k).1 hnodup' hinv1 a ha'

lemma buildMap_eval_mem {α : Type*} [DecidableEq α] (N : ℕ)
    (f : List Gate → α → List Gate × ℕ) (defW : ℕ) (Inv : List Gate → Prop)
    (x : List Bool) (hx : x.length = N) (P : α → Prop)
    (hf_ext : ∀ gs k, Inv gs → ∃ ext, (f gs k).1 = gs ++ ext ∧ Inv (f gs k).1)
    (hf_out : ∀ gs k, Inv gs → (f gs k).2 < N + (f gs k).1.length)
    (gs : List Gate) (ks : List α) (hnodup : ks.Nodup) (hgs : Inv gs)
    (hf_eval : ∀ gs' k, k ∈ ks → Inv gs' → (wireVal (f gs' k).1 x (f gs' k).2 = true ↔ P k)) :
    ∀ a ∈ ks, wireVal (buildMap f defW gs ks).1 x ((buildMap f defW gs ks).2 a) = true ↔ P a := by
  induction ks generalizing gs with
  | nil => intro a ha; simp at ha
  | cons k ks ih =>
      intro a ha
      simp only [List.nodup_cons] at hnodup
      obtain ⟨hk_not, hnodup'⟩ := hnodup
      obtain ⟨e1, he1, hinv1⟩ := hf_ext gs k hgs
      simp only [buildMap]
      by_cases hak : a = k
      · subst hak
        simp only [↓reduceIte]
        obtain ⟨e2, he2, _⟩ := buildMap_ext f defW Inv hf_ext (f gs a).1 ks hinv1
        rw [he2, wireVal_append_of_lt _ _ _ _ (by rw [hx]; exact hf_out gs a hgs)]
        exact hf_eval gs a (by simp) hgs
      · simp only [hak, ↓reduceIte]
        have ha' : a ∈ ks := by
          simp only [List.mem_cons] at ha
          exact ha.resolve_left hak
        exact ih (f gs k).1 hnodup' hinv1 (fun gs' k' hk' => hf_eval gs' k' (by simp [hk'])) a ha'

lemma addAnd_props (N : ℕ) (gs : List Gate) (a b : ℕ) :
    (addAnd N gs a b).1 = gs ++ [⟨GateOp.and, [a, b]⟩] ∧
      (addAnd N gs a b).2 = N + gs.length ∧
      (addAnd N gs a b).2 < N + (addAnd N gs a b).1.length ∧
      notCount (Circuit.mk (addAnd N gs a b).1 0) = notCount (Circuit.mk gs 0) ∧
      nonNotCount (addAnd N gs a b).1 = nonNotCount gs + 1 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · simp [addAnd]
  · rw [addAnd, notCount_append (gs := gs) (ext := [⟨GateOp.and, [a, b]⟩]) (o₁ := 0) (o₂ := 0) (o₃ := 0)]
    have hne : GateOp.and ≠ GateOp.not := by intro h; cases h
    rw [notCount_cons_of_ne ⟨GateOp.and, [a, b]⟩ [] hne 0]
    simp [notCount]
  · rw [addAnd, nonNotCount_append]
    simp [nonNotCount, isNotGate]

lemma addAnd_wf (N : ℕ) (gs : List Gate) (a b : ℕ)
    (hf : FanInTwo (Circuit.mk gs 0)) (hr : ReadsBack N (Circuit.mk gs 0))
    (ha : a < N + gs.length) (hb : b < N + gs.length) :
    FanInTwo (Circuit.mk (addAnd N gs a b).1 0) ∧
      ReadsBack N (Circuit.mk (addAnd N gs a b).1 0) := by
  refine ⟨?_, ?_⟩
  · apply fanInTwo_append hf
    intro g hg
    simp only [List.mem_singleton] at hg
    subst hg
    simp
  · apply readsBack_snoc hr
    intro i hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl <;> assumption

lemma addAnd_eval (N : ℕ) (gs : List Gate) (a b : ℕ) (x : List Bool) (hx : x.length = N) :
    wireVal (addAnd N gs a b).1 x (addAnd N gs a b).2 = true ↔
      wireVal gs x a = true ∧ wireVal gs x b = true := by
  simp only [addAnd]
  have h := wireVal_snoc_self gs ⟨GateOp.and, [a, b]⟩ x
  rw [hx] at h
  rw [h]
  simp [eval_and]

lemma addNot_props (N : ℕ) (gs : List Gate) (a : ℕ) :
    (addNot N gs a).1 = gs ++ [⟨GateOp.not, [a]⟩] ∧
      (addNot N gs a).2 = N + gs.length ∧
      (addNot N gs a).2 < N + (addNot N gs a).1.length ∧
      notCount (Circuit.mk (addNot N gs a).1 0) = notCount (Circuit.mk gs 0) + 1 ∧
      nonNotCount (addNot N gs a).1 = nonNotCount gs := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · simp [addNot]
  · rw [addNot, notCount_append (gs := gs) (ext := [⟨GateOp.not, [a]⟩]) (o₁ := 0) (o₂ := 0) (o₃ := 0)]
    simp [notCount]
  · rw [addNot, nonNotCount_append]
    simp [nonNotCount, isNotGate]

lemma addNot_wf (N : ℕ) (gs : List Gate) (a : ℕ)
    (hf : FanInTwo (Circuit.mk gs 0)) (hr : ReadsBack N (Circuit.mk gs 0))
    (ha : a < N + gs.length) :
    FanInTwo (Circuit.mk (addNot N gs a).1 0) ∧
      ReadsBack N (Circuit.mk (addNot N gs a).1 0) := by
  refine ⟨?_, ?_⟩
  · apply fanInTwo_append hf
    intro g hg
    simp only [List.mem_singleton] at hg
    subst hg
    simp
  · apply readsBack_snoc hr
    intro i hi
    simp only [List.mem_singleton] at hi
    subst hi
    exact ha

lemma addNot_eval (N : ℕ) (gs : List Gate) (a : ℕ) (x : List Bool) (hx : x.length = N) :
    wireVal (addNot N gs a).1 x (addNot N gs a).2 = true ↔
      wireVal gs x a = false := by
  simp only [addNot]
  have h := wireVal_snoc_self gs ⟨GateOp.not, [a]⟩ x
  rw [hx] at h
  rw [h]
  simp [eval_not]

def addHits (N step : ℕ) (B : ℕ → ℕ) : List Gate → List (ℕ × ℕ) → List Gate × List ℕ
  | gs, [] => (gs, [])
  | gs, (L, w) :: ps =>
      let r1 := addAnd N gs w (B (L + step))
      let r2 := addHits N step B r1.1 ps
      (r2.1, r1.2 :: r2.2)

def addBranches (N step bit nbit : ℕ) : List Gate → List (ℕ × ℕ) → List Gate × List (ℕ × ℕ)
  | gs, [] => (gs, [])
  | gs, (L, w) :: ps =>
      let rL := addAnd N gs w nbit
      let rR := addAnd N rL.1 w bit
      let rRest := addBranches N step bit nbit rR.1 ps
      (rRest.1, (L, rL.2) :: (L + step, rR.2) :: rRest.2)

def buildTrie (N nF h : ℕ) (B : ℕ → ℕ) : ℕ → List Gate → List (ℕ × ℕ) → List Gate × List (ℕ × ℕ)
  | 0, gs, nodes => (gs, nodes)
  | d + 1, gs, nodes =>
      let step := 2 ^ d
      let split := nodes.filter (fun p => p.1 + step ≤ h)
      let nosplit := nodes.filter (fun p => h < p.1 + step)
      if split.isEmpty then
        buildTrie N nF h B d gs nodes
      else
        let rHits := addHits N step B gs split
        let rBit := foldOr N rHits.1 nF rHits.2
        let rNBit := addNot N rBit.1 rBit.2
        let rBr := addBranches N step rBit.2 rNBit.2 rNBit.1 split
        buildTrie N nF h B d rBr.1 (nosplit ++ rBr.2)

lemma addHits_props (N step : ℕ) (B : ℕ → ℕ) (gs : List Gate) (split : List (ℕ × ℕ)) :
    (∃ ext, (addHits N step B gs split).1 = gs ++ ext) ∧
      (addHits N step B gs split).2.length = split.length ∧
      notCount (Circuit.mk (addHits N step B gs split).1 0) = notCount (Circuit.mk gs 0) ∧
      nonNotCount (addHits N step B gs split).1 = nonNotCount gs + split.length := by
  induction split generalizing gs with
  | nil => exact ⟨⟨[], by simp [addHits]⟩, by simp [addHits], rfl, by simp [addHits]⟩
  | cons p ps ih =>
      obtain ⟨L, w⟩ := p
      simp only [addHits]
      have h1 := addAnd_props N gs w (B (L + step))
      obtain ⟨⟨e2, he2⟩, hlen2, hnc2, hnnc2⟩ := ih (addAnd N gs w (B (L + step))).1
      refine ⟨⟨[⟨GateOp.and, [w, B (L + step)]⟩] ++ e2, ?_⟩, ?_, ?_, ?_⟩
      · rw [he2, h1.1, List.append_assoc]
      · simp [hlen2]
      · rw [hnc2, h1.2.2.2.1]
      · rw [hnnc2, h1.2.2.2.2]; simp; omega

lemma addHits_out_lt (N step : ℕ) (B : ℕ → ℕ) (gs : List Gate) (split : List (ℕ × ℕ)) :
    ∀ w ∈ (addHits N step B gs split).2, w < N + (addHits N step B gs split).1.length := by
  induction split generalizing gs with
  | nil => intro w hw; simp [addHits] at hw
  | cons p ps ih =>
      obtain ⟨L, w0⟩ := p
      intro w hw
      simp only [addHits, List.mem_cons] at hw
      rcases hw with rfl | hw
      · simp only [addHits]
        obtain ⟨e2, he2⟩ := (addHits_props N step B (addAnd N gs w0 (B (L + step))).1 ps).1
        rw [he2]
        have hlt := (addAnd_props N gs w0 (B (L + step))).2.2.1
        simp only [List.length_append]
        omega
      · exact ih _ w hw

lemma addHits_wf (N step : ℕ) (B : ℕ → ℕ) (gs : List Gate) (split : List (ℕ × ℕ))
    (hf : FanInTwo (Circuit.mk gs 0)) (hr : ReadsBack N (Circuit.mk gs 0))
    (hw : ∀ p ∈ split, p.2 < N + gs.length ∧ B (p.1 + step) < N + gs.length) :
    FanInTwo (Circuit.mk (addHits N step B gs split).1 0) ∧
      ReadsBack N (Circuit.mk (addHits N step B gs split).1 0) := by
  induction split generalizing gs with
  | nil => exact ⟨hf, hr⟩
  | cons p ps ih =>
      obtain ⟨L, w⟩ := p
      simp only [addHits]
      have h0 := hw (L, w) (by simp)
      obtain ⟨hf1, hr1⟩ := addAnd_wf N gs w (B (L + step)) hf hr h0.1 h0.2
      apply ih _ hf1 hr1
      intro q hq
      have hq' := hw q (by simp [hq])
      have hlen : (addAnd N gs w (B (L + step))).1.length = gs.length + 1 := by
        rw [(addAnd_props N gs w (B (L + step))).1]; simp
      omega

lemma addHits_eval (N step : ℕ) (B : ℕ → ℕ) (gs : List Gate) (split : List (ℕ × ℕ))
    (x : List Bool) (hx : x.length = N)
    (hw : ∀ p ∈ split, p.2 < N + gs.length ∧ B (p.1 + step) < N + gs.length) :
    (∃ w ∈ (addHits N step B gs split).2, wireVal (addHits N step B gs split).1 x w = true) ↔
      ∃ p ∈ split, wireVal gs x p.2 = true ∧ wireVal gs x (B (p.1 + step)) = true := by
  induction split generalizing gs with
  | nil => simp [addHits]
  | cons p ps ih =>
      obtain ⟨L, w0⟩ := p
      simp only [addHits]
      let r1 := addAnd N gs w0 (B (L + step))
      have h0 := hw (L, w0) (by simp)
      have hw1 : ∀ q ∈ ps, q.2 < N + r1.1.length ∧ B (q.1 + step) < N + r1.1.length := by
        intro q hq
        have hq' := hw q (by simp [hq])
        have hlen : r1.1.length = gs.length + 1 := by
          rw [(addAnd_props N gs w0 (B (L + step))).1]; simp
        omega
      have hih := ih r1.1 hw1
      obtain ⟨e2, he2⟩ := (addHits_props N step B r1.1 ps).1
      have hpres_r1 : wireVal (addHits N step B r1.1 ps).1 x r1.2 = wireVal r1.1 x r1.2 := by
        rw [he2]
        exact wireVal_append_of_lt _ _ _ _ (by rw [hx]; exact (addAnd_props N gs w0 (B (L + step))).2.2.1)
      have hpres_ps : ∀ q ∈ ps,
          wireVal r1.1 x q.2 = wireVal gs x q.2 ∧
          wireVal r1.1 x (B (q.1 + step)) = wireVal gs x (B (q.1 + step)) := by
        intro q hq
        have hq' := hw q (by simp [hq])
        have hr1_eq : r1.1 = gs ++ [⟨GateOp.and, [w0, B (L + step)]⟩] := rfl
        rw [hr1_eq]
        exact ⟨wireVal_append_of_lt _ _ _ _ (by rw [hx]; exact hq'.1),
               wireVal_append_of_lt _ _ _ _ (by rw [hx]; exact hq'.2)⟩
      constructor
      · rintro ⟨w, hwmem, hwt⟩
        simp only [List.mem_cons] at hwmem
        rcases hwmem with rfl | hwmem
        · rw [hpres_r1, addAnd_eval N gs w0 (B (L + step)) x hx] at hwt
          exact ⟨(L, w0), by simp, hwt⟩
        · obtain ⟨q, hq, hqt⟩ := hih.mp ⟨w, hwmem, hwt⟩
          rw [(hpres_ps q hq).1, (hpres_ps q hq).2] at hqt
          exact ⟨q, by simp [hq], hqt⟩
      · rintro ⟨q, hqmem, hqt⟩
        simp only [List.mem_cons] at hqmem
        rcases hqmem with rfl | hqmem
        · refine ⟨r1.2, by simp [r1], ?_⟩
          rw [hpres_r1, addAnd_eval N gs w0 (B (L + step)) x hx]
          exact hqt
        · have hqt' : wireVal r1.1 x q.2 = true ∧ wireVal r1.1 x (B (q.1 + step)) = true := by
            rw [(hpres_ps q hqmem).1, (hpres_ps q hqmem).2]; exact hqt
          obtain ⟨w, hwmem, hwt⟩ := hih.mpr ⟨q, hqmem, hqt'⟩
          exact ⟨w, by simp [r1, hwmem], hwt⟩

lemma addBranches_props (N step bit nbit : ℕ) (gs : List Gate) (split : List (ℕ × ℕ)) :
    (∃ ext, (addBranches N step bit nbit gs split).1 = gs ++ ext) ∧
      notCount (Circuit.mk (addBranches N step bit nbit gs split).1 0) = notCount (Circuit.mk gs 0) ∧
      nonNotCount (addBranches N step bit nbit gs split).1 = nonNotCount gs + 2 * split.length ∧
      ((addBranches N step bit nbit gs split).2.map Prod.fst) =
        split.flatMap (fun p => [p.1, p.1 + step]) := by
  induction split generalizing gs with
  | nil => exact ⟨⟨[], by simp [addBranches]⟩, rfl, by simp [addBranches], by simp [addBranches]⟩
  | cons p ps ih =>
      obtain ⟨L, w⟩ := p
      simp only [addBranches]
      let rL := addAnd N gs w nbit
      let rR := addAnd N rL.1 w bit
      have hL := addAnd_props N gs w nbit
      have hR := addAnd_props N rL.1 w bit
      obtain ⟨⟨e, he⟩, hnc, hnnc, hfst⟩ := ih rR.1
      refine ⟨⟨[⟨GateOp.and, [w, nbit]⟩, ⟨GateOp.and, [w, bit]⟩] ++ e, ?_⟩, ?_, ?_, ?_⟩
      · rw [he, hR.1, hL.1, List.append_assoc, List.append_assoc]; rfl
      · rw [hnc, hR.2.2.2.1, hL.2.2.2.1]
      · rw [hnnc, hR.2.2.2.2, hL.2.2.2.2]; simp; omega
      · simp only [List.map_cons, List.flatMap_cons]
        rw [hfst]
        simp

lemma addBranches_out_lt (N step bit nbit : ℕ) (gs : List Gate) (split : List (ℕ × ℕ)) :
    ∀ q ∈ (addBranches N step bit nbit gs split).2,
      q.2 < N + (addBranches N step bit nbit gs split).1.length := by
  induction split generalizing gs with
  | nil => intro q hq; simp [addBranches] at hq
  | cons p ps ih =>
      obtain ⟨L, w⟩ := p
      intro q hq
      simp only [addBranches, List.mem_cons] at hq
      let rL := addAnd N gs w nbit
      let rR := addAnd N rL.1 w bit
      obtain ⟨e, he⟩ := (addBranches_props N step bit nbit rR.1 ps).1
      rcases hq with rfl | rfl | hq
      · simp only [addBranches]
        have hlt := (addAnd_props N gs w nbit).2.2.1
        have hlenL : rL.1.length = gs.length + 1 := by
          dsimp only [rL]; rw [(addAnd_props N gs w nbit).1]; simp
        have hlenR : rR.1.length = gs.length + 2 := by
          dsimp only [rR]; rw [(addAnd_props N rL.1 w bit).1]; simp [hlenL]
        rw [he]
        simp only [List.length_append]
        change (addAnd N gs w nbit).2 < N + (rR.1.length + e.length)
        have hlt' : (addAnd N gs w nbit).2 < N + (gs.length + 1) := by
          dsimp only [rL] at hlenL
          rw [← hlenL]
          exact hlt
        omega
      · simp only [addBranches]
        have hlt := (addAnd_props N rL.1 w bit).2.2.1
        rw [he]
        simp only [List.length_append]
        change (addAnd N rL.1 w bit).2 < N + (rR.1.length + e.length)
        have hlt' : (addAnd N rL.1 w bit).2 < N + rR.1.length := hlt
        omega
      · exact ih rR.1 q hq

lemma addBranches_wf (N step bit nbit : ℕ) (gs : List Gate) (split : List (ℕ × ℕ))
    (hf : FanInTwo (Circuit.mk gs 0)) (hr : ReadsBack N (Circuit.mk gs 0))
    (hbit : bit < N + gs.length) (hnbit : nbit < N + gs.length)
    (hw : ∀ p ∈ split, p.2 < N + gs.length) :
    FanInTwo (Circuit.mk (addBranches N step bit nbit gs split).1 0) ∧
      ReadsBack N (Circuit.mk (addBranches N step bit nbit gs split).1 0) := by
  induction split generalizing gs with
  | nil => exact ⟨hf, hr⟩
  | cons p ps ih =>
      obtain ⟨L, w⟩ := p
      simp only [addBranches]
      have h0 := hw (L, w) (by simp)
      let rL := addAnd N gs w nbit
      obtain ⟨hfL, hrL⟩ := addAnd_wf N gs w nbit hf hr h0 hnbit
      have hlenL : rL.1.length = gs.length + 1 := by dsimp only [rL]; rw [(addAnd_props N gs w nbit).1]; simp
      let rR := addAnd N rL.1 w bit
      obtain ⟨hfR, hrR⟩ := addAnd_wf N rL.1 w bit hfL hrL (by omega) (by omega)
      have hlenR : rR.1.length = gs.length + 2 := by
        dsimp only [rR]; rw [(addAnd_props N rL.1 w bit).1]; simp [hlenL]
      apply ih rR.1 hfR hrR (by omega) (by omega)
      intro q hq
      have hq' := hw q (by simp [hq])
      omega

lemma addBranches_eval (N step bit nbit : ℕ) (gs : List Gate) (split : List (ℕ × ℕ))
    (x : List Bool) (hx : x.length = N)
    (hbit : bit < N + gs.length) (hnbit : nbit < N + gs.length)
    (hw : ∀ p ∈ split, p.2 < N + gs.length) :
    ∀ q ∈ (addBranches N step bit nbit gs split).2,
      ∃ p ∈ split,
        (q.1 = p.1 ∧ (wireVal (addBranches N step bit nbit gs split).1 x q.2 = true ↔
          wireVal gs x p.2 = true ∧ wireVal gs x nbit = true)) ∨
        (q.1 = p.1 + step ∧ (wireVal (addBranches N step bit nbit gs split).1 x q.2 = true ↔
          wireVal gs x p.2 = true ∧ wireVal gs x bit = true)) := by
  induction split generalizing gs with
  | nil => intro q hq; simp [addBranches] at hq
  | cons p ps ih =>
      obtain ⟨L, w⟩ := p
      intro q hq
      simp only [addBranches, List.mem_cons] at hq
      let rL := addAnd N gs w nbit
      let rR := addAnd N rL.1 w bit
      have h0 := hw (L, w) (by simp)
      have hlenL : rL.1.length = gs.length + 1 := by dsimp only [rL]; rw [(addAnd_props N gs w nbit).1]; simp
      have hlenR : rR.1.length = gs.length + 2 := by dsimp only [rR]; rw [(addAnd_props N rL.1 w bit).1]; simp [hlenL]
      obtain ⟨e, he⟩ := (addBranches_props N step bit nbit rR.1 ps).1
      rcases hq with rfl | rfl | hq
      · simp only [addBranches]
        refine ⟨(L, w), by simp, Or.inl ⟨rfl, ?_⟩⟩
        have he' : (addBranches N step bit nbit rR.1 ps).1 = rL.1 ++ ([⟨GateOp.and, [w, bit]⟩] ++ e) := by
          rw [he, (addAnd_props N rL.1 w bit).1, List.append_assoc]
        rw [he', wireVal_append_of_lt _ _ _ _ (by rw [hx]; exact (addAnd_props N gs w nbit).2.2.1)]
        exact addAnd_eval N gs w nbit x hx
      · simp only [addBranches]
        refine ⟨(L, w), by simp, Or.inr ⟨rfl, ?_⟩⟩
        rw [he, wireVal_append_of_lt _ _ _ _ (by rw [hx]; exact (addAnd_props N rL.1 w bit).2.2.1)]
        rw [addAnd_eval N rL.1 w bit x hx]
        have hrL_eq : rL.1 = gs ++ [⟨GateOp.and, [w, nbit]⟩] := rfl
        rw [hrL_eq, wireVal_append_of_lt _ _ _ _ (by rw [hx]; exact h0),
          wireVal_append_of_lt _ _ _ _ (by rw [hx]; exact hbit)]
      · simp only [addBranches]
        have hw' : ∀ p' ∈ ps, p'.2 < N + rR.1.length := by
          intro p' hp'; have := hw p' (by simp [hp']); omega
        obtain ⟨p', hp', hcase⟩ := ih rR.1 (by omega) (by omega) hw' q hq
        have hp'w := hw p' (by simp [hp'])
        have hrL_eq : rL.1 = gs ++ [⟨GateOp.and, [w, nbit]⟩] := rfl
        have hrR_eq : rR.1 = gs ++ [⟨GateOp.and, [w, nbit]⟩, ⟨GateOp.and, [w, bit]⟩] := by
          simp [rR, rL, addAnd, List.append_assoc]
        refine ⟨p', by simp [hp'], ?_⟩
        rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left
          refine ⟨h1, ?_⟩
          rw [h2, hrR_eq, wireVal_append_of_lt _ _ _ _ (by rw [hx]; exact hp'w),
            wireVal_append_of_lt _ _ _ _ (by rw [hx]; exact hnbit)]
        · right
          refine ⟨h1, ?_⟩
          rw [h2, hrR_eq, wireVal_append_of_lt _ _ _ _ (by rw [hx]; exact hp'w),
            wireVal_append_of_lt _ _ _ _ (by rw [hx]; exact hbit)]

def remSet (d h : ℕ) : Finset ℕ :=
  (Finset.Icc 1 h).filter (fun m => m % 2 ^ d ≠ 0)

lemma remSet_zero (h : ℕ) : remSet 0 h = ∅ := by
  ext m
  simp [remSet, Nat.mod_one]

lemma mul_pow_ne_add_pow (step a b : ℕ) (hstep : 0 < step) :
    2 * step * a ≠ 2 * step * b + step := by
  intro heq
  have hmod := congrArg (· % (2 * step)) heq
  have hlt : step < 2 * step := by omega
  rw [Nat.mul_mod_right, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod,
    Nat.mod_eq_of_lt hlt] at hmod
  omega

lemma remSet_card_le (d h : ℕ) : (remSet d h).card ≤ h := by
  calc (remSet d h).card ≤ (Finset.Icc 1 h).card := Finset.card_filter_le _ _
    _ = h := by simp

lemma remSet_step_le (d h : ℕ) (split : List (ℕ × ℕ))
    (hnodup : (split.map Prod.fst).Nodup)
    (hdiv : ∀ p ∈ split, 2 ^ (d + 1) ∣ p.1 ∧ p.1 + 2 ^ d ≤ h) :
    split.length + (remSet d h).card ≤ (remSet (d + 1) h).card := by
  let S := split.map (fun p => p.1 + 2 ^ d)
  have hS_nodup : S.Nodup := by
    have hinj : Function.Injective (fun x : ℕ => x + 2 ^ d) := fun a b hab => Nat.add_right_cancel hab
    have hS_eq : S = (split.map Prod.fst).map (fun x => x + 2 ^ d) := by simp [S]
    rw [hS_eq]
    exact hnodup.map hinj
  have hsub : remSet d h ⊆ remSet (d + 1) h := by
    intro m hm
    simp only [remSet, Finset.mem_filter] at hm ⊢
    refine ⟨hm.1, ?_⟩
    intro h0
    apply hm.2
    have hd : 2 ^ d ∣ 2 ^ (d + 1) := ⟨2, by ring⟩
    exact Nat.dvd_iff_mod_eq_zero.mp (dvd_trans hd (Nat.dvd_iff_mod_eq_zero.mpr h0))
  have hS_sub : S.toFinset ⊆ remSet (d + 1) h \ remSet d h := by
    intro m hm
    simp only [S, List.mem_toFinset, List.mem_map] at hm
    obtain ⟨p, hp, rfl⟩ := hm
    obtain ⟨hdvd, hle⟩ := hdiv p hp
    have hpos : 1 ≤ 2 ^ d := Nat.one_le_pow _ _ (by omega)
    have hm1 : p.1 + 2 ^ d ∈ Finset.Icc 1 h := Finset.mem_Icc.mpr ⟨by omega, hle⟩
    have hm_d0 : (p.1 + 2 ^ d) % 2 ^ d = 0 := by
      apply Nat.dvd_iff_mod_eq_zero.mp
      exact dvd_add (dvd_trans ⟨2, by ring⟩ hdvd) dvd_rfl
    have hm_d1 : (p.1 + 2 ^ d) % 2 ^ (d + 1) ≠ 0 := by
      obtain ⟨q, hq⟩ := hdvd
      rw [hq, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod]
      have hlt : 2 ^ d < 2 ^ (d + 1) := by
        have : 0 < 2 ^ d := Nat.pow_pos (by omega)
        rw [pow_succ]; omega
      rw [Nat.mod_eq_of_lt hlt]
      omega
    simp only [Finset.mem_sdiff, remSet, Finset.mem_filter]
    exact ⟨⟨hm1, hm_d1⟩, fun h => absurd hm_d0 h.2⟩
  have hcard_S : S.toFinset.card = split.length := by
    rw [List.toFinset_card_of_nodup hS_nodup, List.length_map]
  have hle_union : (S.toFinset ∪ remSet d h).card ≤ (remSet (d + 1) h).card := by
    apply Finset.card_le_card
    intro m hm
    rcases Finset.mem_union.mp hm with hm | hm
    · exact (Finset.mem_sdiff.mp (hS_sub hm)).1
    · exact hsub hm
  have hdisj : Disjoint S.toFinset (remSet d h) := by
    rw [Finset.disjoint_left]
    intro m hm1 hm2
    exact (Finset.mem_sdiff.mp (hS_sub hm1)).2 hm2
  rw [Finset.card_union_of_disjoint hdisj, hcard_S] at hle_union
  exact hle_union

lemma buildTrie_inv (N nF h : ℕ) (B : ℕ → ℕ) (d : ℕ) (gs : List Gate) (nodes : List (ℕ × ℕ))
    (hf : FanInTwo (Circuit.mk gs 0)) (hr : ReadsBack N (Circuit.mk gs 0))
    (hnF : nF < N + gs.length)
    (hB : ∀ k ≤ h, B k < N + gs.length)
    (hnodes : ∀ p ∈ nodes, p.1 ≤ h ∧ 2 ^ d ∣ p.1 ∧ p.2 < N + gs.length)
    (hnodup : (nodes.map Prod.fst).Nodup)
    (hcomp : ∀ L ≤ h, 2 ^ d ∣ L → ∃ p ∈ nodes, p.1 = L) :
    let res := buildTrie N nF h B d gs nodes
    (∃ ext, res.1 = gs ++ ext) ∧
      FanInTwo (Circuit.mk res.1 0) ∧
      ReadsBack N (Circuit.mk res.1 0) ∧
      notCount (Circuit.mk res.1 0) ≤ notCount (Circuit.mk gs 0) + d ∧
      nonNotCount res.1 ≤ nonNotCount gs + 4 * (remSet d h).card ∧
      (∀ p ∈ res.2, p.1 ≤ h ∧ p.2 < N + res.1.length) ∧
      (res.2.map Prod.fst).Nodup ∧
      (∀ L ≤ h, ∃ p ∈ res.2, p.1 = L) := by
  induction d generalizing gs nodes with
  | zero =>
      simp only [buildTrie]
      refine ⟨⟨[], by simp⟩, hf, hr, Nat.le_add_right _ _, Nat.le_add_right _ _, ?_, hnodup, ?_⟩
      · intro p hp; exact ⟨(hnodes p hp).1, (hnodes p hp).2.2⟩
      · intro L hL; exact hcomp L hL (by simp)
  | succ d ih =>
      simp only [buildTrie]
      set step := 2 ^ d
      set split := nodes.filter (fun p => p.1 + step ≤ h)
      set nosplit := nodes.filter (fun p => h < p.1 + step)
      have hsplit_sub : ∀ p ∈ split, p ∈ nodes := fun p hp => (List.mem_filter.mp hp).1
      have hnosplit_sub : ∀ p ∈ nosplit, p ∈ nodes := fun p hp => (List.mem_filter.mp hp).1
      by_cases hemp : split.isEmpty = true
      · rw [if_pos hemp]
        have hsplit_nil : split = [] := List.isEmpty_iff.mp hemp
        have hnodes' : ∀ p ∈ nodes, p.1 ≤ h ∧ 2 ^ d ∣ p.1 ∧ p.2 < N + gs.length := by
          intro p hp
          have h0 := hnodes p hp
          exact ⟨h0.1, dvd_trans ⟨2, by rw [pow_succ]⟩ h0.2.1, h0.2.2⟩
        have hcomp' : ∀ L ≤ h, 2 ^ d ∣ L → ∃ p ∈ nodes, p.1 = L := by
          intro L hL hdvd
          by_cases hdvd1 : 2 ^ (d + 1) ∣ L
          · exact hcomp L hL hdvd1
          · obtain ⟨q, hq⟩ := hdvd
            have hq_odd : q % 2 = 1 := by
              by_contra hne
              have h2q : 2 ∣ q := Nat.dvd_of_mod_eq_zero (by omega)
              obtain ⟨r, hrq⟩ := h2q
              apply hdvd1
              exact ⟨r, by rw [hq, hrq, pow_succ]; ring⟩
            have hLge : step ≤ L := by
              have : 1 ≤ q := by omega
              calc step = step * 1 := (Nat.mul_one _).symm
                _ ≤ step * q := Nat.mul_le_mul_left _ this
                _ = L := hq.symm
            let L0 := L - step
            have hL0_le : L0 ≤ h := by omega
            have hL0_dvd : 2 ^ (d + 1) ∣ L0 := by
              have hq1 : L0 = step * (q - 1) := by
                dsimp only [L0]
                rw [Nat.mul_sub_left_distrib, Nat.mul_one, ← hq]
              have h2q1 : 2 ∣ q - 1 := Nat.dvd_of_mod_eq_zero (by omega)
              obtain ⟨r, hrq⟩ := h2q1
              exact ⟨r, by rw [hq1, hrq, pow_succ]; ring⟩
            obtain ⟨p, hp, hpL⟩ := hcomp L0 hL0_le hL0_dvd
            have hp_in : p ∈ split := by
              simp only [split, List.mem_filter, decide_eq_true_eq]
              exact ⟨hp, by omega⟩
            rw [hsplit_nil] at hp_in
            simp at hp_in
        obtain ⟨⟨e, he⟩, hf', hr', hnc, hnnc, hres, hnd, hc⟩ := ih gs nodes hf hr hnF hB hnodes' hnodup hcomp'
        refine ⟨⟨e, he⟩, hf', hr', ?_, ?_, hres, hnd, hc⟩
        · omega
        · have hsub_rem : (remSet d h).card ≤ (remSet (d + 1) h).card := by
            apply Finset.card_le_card
            intro m hm
            simp only [remSet, Finset.mem_filter] at hm ⊢
            refine ⟨hm.1, ?_⟩
            intro h0
            apply hm.2
            exact Nat.dvd_iff_mod_eq_zero.mp (dvd_trans ⟨2, by rw [pow_succ]⟩ (Nat.dvd_iff_mod_eq_zero.mpr h0))
          omega
      · rw [if_neg hemp]
        set rHits := addHits N step B gs split
        set rBit := foldOr N rHits.1 nF rHits.2
        set rNBit := addNot N rBit.1 rBit.2
        set rBr := addBranches N step rBit.2 rNBit.2 rNBit.1 split
        have hw_hits : ∀ p ∈ split, p.2 < N + gs.length ∧ B (p.1 + step) < N + gs.length := by
          intro p hp
          have hp0 := hnodes p (hsplit_sub p hp)
          have hle : p.1 + step ≤ h := by
            have := (List.mem_filter.mp hp).2
            simpa using this
          exact ⟨hp0.2.2, hB _ hle⟩
        have hHitsP := addHits_props N step B gs split
        have hHitsWF := addHits_wf N step B gs split hf hr hw_hits
        have hHitsOut := addHits_out_lt N step B gs split
        obtain ⟨eH, heH⟩ := hHitsP.1
        have hlenH : gs.length ≤ rHits.1.length := by rw [heH]; simp
        have hBitExt := foldOr_ext N rHits.1 nF rHits.2
        obtain ⟨eB, heB, _⟩ := hBitExt
        have hlenB : rHits.1.length ≤ rBit.1.length := by rw [heB]; simp
        have hBitWF : FanInTwo (Circuit.mk rBit.1 0) ∧ ReadsBack N (Circuit.mk rBit.1 0) :=
          ⟨foldOr_fanInTwo N rHits.1 nF rHits.2 hHitsWF.1,
           foldOr_readsBack N rHits.1 nF rHits.2 hHitsWF.2 (fun w hw => hHitsOut w hw)⟩
        have hBitOut : rBit.2 < N + rBit.1.length :=
          foldOr_out_lt N rHits.1 nF rHits.2 (by omega) (fun w hw => hHitsOut w hw)
        have hBitC := foldOr_counts N rHits.1 nF rHits.2
        have hNBitP := addNot_props N rBit.1 rBit.2
        have hNBitWF := addNot_wf N rBit.1 rBit.2 hBitWF.1 hBitWF.2 hBitOut
        have hlenN : rBit.1.length ≤ rNBit.1.length := by rw [hNBitP.1]; simp
        have hw_br : ∀ p ∈ split, p.2 < N + rNBit.1.length := by
          intro p hp; have := (hnodes p (hsplit_sub p hp)).2.2; omega
        have hBrP := addBranches_props N step rBit.2 rNBit.2 rNBit.1 split
        have hBrWF := addBranches_wf N step rBit.2 rNBit.2 rNBit.1 split hNBitWF.1 hNBitWF.2
          (by omega) hNBitP.2.2.1 hw_br
        have hBrOut := addBranches_out_lt N step rBit.2 rNBit.2 rNBit.1 split
        obtain ⟨eBr, heBr⟩ := hBrP.1
        have hlenBr : rNBit.1.length ≤ rBr.1.length := by rw [heBr]; simp
        have hfull_ext : ∃ ext, rBr.1 = gs ++ ext :=
          ⟨eH ++ eB ++ [⟨GateOp.not, [rBit.2]⟩] ++ eBr, by
            rw [heBr, hNBitP.1, heB, heH]; simp [List.append_assoc]⟩
        obtain ⟨eAll, heAll⟩ := hfull_ext
        have hlenAll : gs.length ≤ rBr.1.length := by rw [heAll]; simp
        have hnF' : nF < N + rBr.1.length := by omega
        have hB' : ∀ k ≤ h, B k < N + rBr.1.length := fun k hk => by have := hB k hk; omega
        have hnodes' : ∀ p ∈ nosplit ++ rBr.2, p.1 ≤ h ∧ 2 ^ d ∣ p.1 ∧ p.2 < N + rBr.1.length := by
          intro p hp
          simp only [List.mem_append] at hp
          rcases hp with hp | hp
          · have h0 := hnodes p (hnosplit_sub p hp)
            exact ⟨h0.1, dvd_trans ⟨2, by rw [pow_succ]⟩ h0.2.1, by omega⟩
          · have hlt := hBrOut p hp
            have hmem : p.1 ∈ rBr.2.map Prod.fst := List.mem_map.mpr ⟨p, hp, rfl⟩
            rw [hBrP.2.2.2, List.mem_flatMap] at hmem
            obtain ⟨q, hq, hqm⟩ := hmem
            have hq0 := hnodes q (hsplit_sub q hq)
            have hqle : q.1 + step ≤ h := by simpa using (List.mem_filter.mp hq).2
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hqm
            rcases hqm with hEq | hEq
            · rw [hEq]
              exact ⟨by omega, dvd_trans ⟨2, by rw [pow_succ]⟩ hq0.2.1, hlt⟩
            · rw [hEq]
              exact ⟨hqle, dvd_add (dvd_trans ⟨2, by rw [pow_succ]⟩ hq0.2.1) dvd_rfl, hlt⟩
        have hsplit_nodup : (split.map Prod.fst).Nodup :=
          hnodup.sublist (List.filter_sublist.map Prod.fst)
        have hnosplit_nodup : (nosplit.map Prod.fst).Nodup :=
          hnodup.sublist (List.filter_sublist.map Prod.fst)
        have hbr_nodup : (rBr.2.map Prod.fst).Nodup := by
          rw [hBrP.2.2.2]
          have hsub_s : ∀ p ∈ split, 2 ^ (d + 1) ∣ p.1 := fun p hp => (hnodes p (hsplit_sub p hp)).2.1
          revert hsplit_nodup hsub_s
          generalize split = s
          intro hs_nodup hs_dvd
          induction s with
          | nil => simp
          | cons q qs ihs =>
              simp only [List.map_cons, List.nodup_cons] at hs_nodup
              simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons]
              have hq0 : 2 ^ (d + 1) ∣ q.1 := hs_dvd q (by simp)
              have hstep_pos : 0 < step := Nat.pow_pos (by omega)
              have hne : q.1 ≠ q.1 + step := by omega
              have hnot1 : q.1 ∉ qs.flatMap (fun p => [p.1, p.1 + step]) := by
                intro hm
                rw [List.mem_flatMap] at hm
                obtain ⟨p, hp, hpm⟩ := hm
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpm
                rcases hpm with hp1 | hp2
                · exact hs_nodup.1 (List.mem_map.mpr ⟨p, hp, hp1.symm⟩)
                · have hp0 := hs_dvd p (by simp [hp])
                  obtain ⟨a, ha⟩ := hq0
                  obtain ⟨b, hb⟩ := hp0
                  have heq : 2 * step * a = 2 * step * b + step := by
                    calc 2 * step * a = 2 ^ (d + 1) * a := by rw [pow_succ]; ring
                      _ = q.1 := ha.symm
                      _ = p.1 + step := hp2
                      _ = 2 ^ (d + 1) * b + step := by rw [hb]
                      _ = 2 * step * b + step := by rw [pow_succ]; ring
                  exact mul_pow_ne_add_pow step a b hstep_pos heq
              have hnot2 : q.1 + step ∉ qs.flatMap (fun p => [p.1, p.1 + step]) := by
                intro hm
                rw [List.mem_flatMap] at hm
                obtain ⟨p, hp, hpm⟩ := hm
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpm
                have hp0 := hs_dvd p (by simp [hp])
                rcases hpm with hp1 | hp2
                · obtain ⟨a, ha⟩ := hq0
                  obtain ⟨b, hb⟩ := hp0
                  have heq : 2 * step * b = 2 * step * a + step := by
                    calc 2 * step * b = 2 ^ (d + 1) * b := by rw [pow_succ]; ring
                      _ = p.1 := hb.symm
                      _ = q.1 + step := hp1.symm
                      _ = 2 ^ (d + 1) * a + step := by rw [ha]
                      _ = 2 * step * a + step := by rw [pow_succ]; ring
                  exact mul_pow_ne_add_pow step b a hstep_pos heq
                · exact hs_nodup.1 (List.mem_map.mpr ⟨p, hp, by omega⟩)
              refine ⟨?_, hnot2, ihs hs_nodup.2 (fun p hp => hs_dvd p (by simp [hp]))⟩
              intro hm
              rcases List.mem_cons.mp hm with h1 | h1
              · exact hne h1
              · exact hnot1 h1
        have hnodup' : ((nosplit ++ rBr.2).map Prod.fst).Nodup := by
          rw [List.map_append, List.nodup_append]
          refine ⟨hnosplit_nodup, hbr_nodup, ?_⟩
          intro a ha1 b hb2 hab
          subst hab
          rw [List.mem_map] at ha1
          obtain ⟨p, hp, rfl⟩ := ha1
          have hpn : h < p.1 + step := by simpa using (List.mem_filter.mp hp).2
          have hp0 := (hnodes p (hnosplit_sub p hp)).2.1
          rw [hBrP.2.2.2, List.mem_flatMap] at hb2
          obtain ⟨q, hq, hqm⟩ := hb2
          have hqs : q.1 + step ≤ h := by simpa using (List.mem_filter.mp hq).2
          have hq0 := (hnodes q (hsplit_sub q hq)).2.1
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hqm
          rcases hqm with hEq | hEq
          · omega
          · obtain ⟨a, ha⟩ := hp0
            obtain ⟨b, hb⟩ := hq0
            have hstep_pos : 0 < step := Nat.pow_pos (by omega)
            have heq : 2 * step * a = 2 * step * b + step := by
              calc 2 * step * a = 2 ^ (d + 1) * a := by rw [pow_succ]; ring
                _ = p.1 := ha.symm
                _ = q.1 + step := hEq
                _ = 2 ^ (d + 1) * b + step := by rw [hb]
                _ = 2 * step * b + step := by rw [pow_succ]; ring
            exact mul_pow_ne_add_pow step a b hstep_pos heq
        have hcomp' : ∀ L ≤ h, 2 ^ d ∣ L → ∃ p ∈ nosplit ++ rBr.2, p.1 = L := by
          intro L hL hdvd
          by_cases hdvd1 : 2 ^ (d + 1) ∣ L
          · obtain ⟨p, hp, rfl⟩ := hcomp L hL hdvd1
            by_cases hle : p.1 + step ≤ h
            · have hp_s : p ∈ split := List.mem_filter.mpr ⟨hp, by simpa using hle⟩
              have hmem : p.1 ∈ rBr.2.map Prod.fst := by
                rw [hBrP.2.2.2, List.mem_flatMap]
                exact ⟨p, hp_s, by simp⟩
              obtain ⟨q, hq, hq1⟩ := List.mem_map.mp hmem
              exact ⟨q, List.mem_append_right _ hq, hq1⟩
            · have hp_ns : p ∈ nosplit := List.mem_filter.mpr ⟨hp, by simpa using (by omega : h < p.1 + step)⟩
              exact ⟨p, List.mem_append_left _ hp_ns, rfl⟩
          · obtain ⟨q, hq⟩ := hdvd
            have hq_odd : q % 2 = 1 := by
              by_contra hne
              have h2q : 2 ∣ q := Nat.dvd_of_mod_eq_zero (by omega)
              obtain ⟨r, hrq⟩ := h2q
              apply hdvd1
              exact ⟨r, by rw [hq, hrq, pow_succ]; ring⟩
            have hLge : step ≤ L := by
              have : 1 ≤ q := by omega
              calc step = step * 1 := (Nat.mul_one _).symm
                _ ≤ step * q := Nat.mul_le_mul_left _ this
                _ = L := hq.symm
            let L0 := L - step
            have hL0_le : L0 ≤ h := by omega
            have hL0_dvd : 2 ^ (d + 1) ∣ L0 := by
              have hq1 : L0 = step * (q - 1) := by
                dsimp only [L0]
                calc L - step = step * q - step * 1 := by rw [hq, Nat.mul_one]
                  _ = step * (q - 1) := by rw [← Nat.mul_sub_left_distrib]
              have h2q1 : 2 ∣ q - 1 := Nat.dvd_of_mod_eq_zero (by omega)
              obtain ⟨r, hrq⟩ := h2q1
              exact ⟨r, by rw [hq1, hrq, pow_succ]; ring⟩
            obtain ⟨p, hp, hpL⟩ := hcomp L0 hL0_le hL0_dvd
            have hp_s : p ∈ split := List.mem_filter.mpr ⟨hp, by simpa using (by omega : p.1 + step ≤ h)⟩
            have hmem : L ∈ rBr.2.map Prod.fst := by
              rw [hBrP.2.2.2, List.mem_flatMap]
              exact ⟨p, hp_s, by simp [hpL, L0]; omega⟩
            obtain ⟨q', hq', hq'1⟩ := List.mem_map.mp hmem
            exact ⟨q', List.mem_append_right _ hq', hq'1⟩
        obtain ⟨⟨e_rec, he_rec⟩, hf_rec, hr_rec, hnc_rec, hnnc_rec, hres_rec, hnd_rec, hc_rec⟩ :=
          ih rBr.1 (nosplit ++ rBr.2) hBrWF.1 hBrWF.2 hnF' hB' hnodes' hnodup' hcomp'
        have hnc_step : notCount (Circuit.mk rBr.1 0) = notCount (Circuit.mk gs 0) + 1 := by
          rw [hBrP.2.1, hNBitP.2.2.2.1, hBitC.1, hHitsP.2.2.1]
        have hnnc_step : nonNotCount rBr.1 ≤ nonNotCount gs + 4 * split.length := by
          calc nonNotCount rBr.1
              = nonNotCount rNBit.1 + 2 * split.length := hBrP.2.2.1
            _ = nonNotCount rBit.1 + 2 * split.length := by rw [hNBitP.2.2.2.2]
            _ ≤ (nonNotCount rHits.1 + rHits.2.length) + 2 * split.length := Nat.add_le_add_right hBitC.2 _
            _ = (nonNotCount gs + split.length + split.length) + 2 * split.length := by
                rw [hHitsP.2.2.2, hHitsP.2.1]
            _ = nonNotCount gs + 4 * split.length := by ring
        have hrem_step : split.length + (remSet d h).card ≤ (remSet (d + 1) h).card := by
          apply remSet_step_le d h split hsplit_nodup
          intro p hp
          exact ⟨(hnodes p (hsplit_sub p hp)).2.1, by simpa using (List.mem_filter.mp hp).2⟩
        refine ⟨⟨eAll ++ e_rec, by rw [he_rec, heAll, List.append_assoc]⟩, hf_rec, hr_rec, ?_, ?_, hres_rec, hnd_rec, hc_rec⟩
        · exact Nat.le_trans hnc_rec (by rw [hnc_step]; omega)
        · calc nonNotCount (buildTrie N nF h B d rBr.1 (nosplit ++ rBr.2)).1
              ≤ nonNotCount rBr.1 + 4 * (remSet d h).card := hnnc_rec
            _ ≤ (nonNotCount gs + 4 * split.length) + 4 * (remSet d h).card := Nat.add_le_add_right hnnc_step _
            _ = nonNotCount gs + 4 * (split.length + (remSet d h).card) := by ring
            _ ≤ nonNotCount gs + 4 * (remSet (d + 1) h).card := Nat.add_le_add_left (Nat.mul_le_mul_left 4 hrem_step) _

lemma mod_pow_eq_sub {L M W : ℕ} (hW : 0 < W) (hdvd : W ∣ L) (h1 : L ≤ M) (h2 : M < L + W) :
    M % W = M - L := by
  obtain ⟨q, rfl⟩ := hdvd
  have hM : M = W * q + (M - W * q) := (Nat.add_sub_cancel' h1).symm
  rw [hM, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  omega

lemma buildTrie_eval (N nF h : ℕ) (B : ℕ → ℕ) (d : ℕ) (gs : List Gate) (nodes : List (ℕ × ℕ))
    (x : List Bool) (hx : x.length = N)
    (M : ℕ) (hM : M ≤ h)
    (hnF : nF < N + gs.length)
    (hnF_val : wireVal gs x nF = false)
    (hB : ∀ k ≤ h, B k < N + gs.length)
    (hB_val : ∀ k ≤ h, wireVal gs x (B k) = true ↔ k ≤ M)
    (hnodes : ∀ p ∈ nodes, p.1 ≤ h ∧ 2 ^ d ∣ p.1 ∧ p.2 < N + gs.length)
    (hcomp : ∀ L ≤ h, 2 ^ d ∣ L → ∃ p ∈ nodes, p.1 = L)
    (hnodes_val : ∀ p ∈ nodes, wireVal gs x p.2 = true ↔ p.1 ≤ M ∧ M < p.1 + 2 ^ d) :
    ∀ p ∈ (buildTrie N nF h B d gs nodes).2,
      wireVal (buildTrie N nF h B d gs nodes).1 x p.2 = true ↔ p.1 = M := by
  induction d generalizing gs nodes with
  | zero =>
      intro p hp
      simp only [buildTrie] at hp ⊢
      rw [hnodes_val p hp]
      simp only [pow_zero]
      omega
  | succ d ih =>
      simp only [buildTrie]
      set step := 2 ^ d
      set split := nodes.filter (fun p => p.1 + step ≤ h)
      set nosplit := nodes.filter (fun p => h < p.1 + step)
      have hsplit_sub : ∀ p ∈ split, p ∈ nodes := fun p hp => (List.mem_filter.mp hp).1
      have hnosplit_sub : ∀ p ∈ nosplit, p ∈ nodes := fun p hp => (List.mem_filter.mp hp).1
      by_cases hemp : split.isEmpty = true
      · rw [if_pos hemp]
        have hsplit_nil : split = [] := List.isEmpty_iff.mp hemp
        have hnodes' : ∀ p ∈ nodes, p.1 ≤ h ∧ 2 ^ d ∣ p.1 ∧ p.2 < N + gs.length := by
          intro p hp
          have h0 := hnodes p hp
          exact ⟨h0.1, dvd_trans ⟨2, by rw [pow_succ]⟩ h0.2.1, h0.2.2⟩
        have hcomp' : ∀ L ≤ h, 2 ^ d ∣ L → ∃ p ∈ nodes, p.1 = L := by
          intro L hL hdvd
          by_cases hdvd1 : 2 ^ (d + 1) ∣ L
          · exact hcomp L hL hdvd1
          · obtain ⟨q, hq⟩ := hdvd
            have hq_odd : q % 2 = 1 := by
              by_contra hne
              obtain ⟨r, hrq⟩ := Nat.dvd_of_mod_eq_zero (by omega : q % 2 = 0)
              apply hdvd1
              exact ⟨r, by rw [hq, hrq, pow_succ]; ring⟩
            have hLge : step ≤ L := by
              have : 1 ≤ q := by omega
              calc step = step * 1 := (Nat.mul_one _).symm
                _ ≤ step * q := Nat.mul_le_mul_left _ this
                _ = L := hq.symm
            let L0 := L - step
            have hL0_dvd : 2 ^ (d + 1) ∣ L0 := by
              have hq1 : L0 = step * (q - 1) := by
                dsimp only [L0]
                rw [Nat.mul_sub_left_distrib, Nat.mul_one, ← hq]
              obtain ⟨r, hrq⟩ := Nat.dvd_of_mod_eq_zero (by omega : (q - 1) % 2 = 0)
              exact ⟨r, by rw [hq1, hrq, pow_succ]; ring⟩
            obtain ⟨p, hp, hpL⟩ := hcomp L0 (by omega) hL0_dvd
            have hp_in : p ∈ split := by
              simp only [split, List.mem_filter, decide_eq_true_eq]
              exact ⟨hp, by omega⟩
            rw [hsplit_nil] at hp_in
            simp at hp_in
        have hnodes_val' : ∀ p ∈ nodes, wireVal gs x p.2 = true ↔ p.1 ≤ M ∧ M < p.1 + step := by
          intro p hp
          rw [hnodes_val p hp]
          have hnos : p ∉ split := by rw [hsplit_nil]; simp
          have hlt : h < p.1 + step := by
            by_contra hle
            apply hnos
            exact List.mem_filter.mpr ⟨hp, by simpa using (by omega : p.1 + step ≤ h)⟩
          have hpow : 2 ^ (d + 1) = step + step := by rw [pow_succ]; ring
          omega
        exact ih gs nodes hnF hnF_val hB hB_val hnodes' hcomp' hnodes_val'
      · rw [if_neg hemp]
        set rHits := addHits N step B gs split
        set rBit := foldOr N rHits.1 nF rHits.2
        set rNBit := addNot N rBit.1 rBit.2
        set rBr := addBranches N step rBit.2 rNBit.2 rNBit.1 split
        have hw_hits : ∀ p ∈ split, p.2 < N + gs.length ∧ B (p.1 + step) < N + gs.length := by
          intro p hp
          have hp0 := hnodes p (hsplit_sub p hp)
          have hle : p.1 + step ≤ h := by simpa using (List.mem_filter.mp hp).2
          exact ⟨hp0.2.2, hB _ hle⟩
        have hHitsP := addHits_props N step B gs split
        have hHitsOut := addHits_out_lt N step B gs split
        obtain ⟨eH, heH⟩ := hHitsP.1
        have hlenH : gs.length ≤ rHits.1.length := by rw [heH]; simp
        obtain ⟨eB, heB, _⟩ := foldOr_ext N rHits.1 nF rHits.2
        have hlenB : rHits.1.length ≤ rBit.1.length := by rw [heB]; simp
        have hBitOut : rBit.2 < N + rBit.1.length :=
          foldOr_out_lt N rHits.1 nF rHits.2 (by omega) (fun w hw => hHitsOut w hw)
        have hNBitP := addNot_props N rBit.1 rBit.2
        have hlenN : rBit.1.length ≤ rNBit.1.length := by rw [hNBitP.1]; simp
        have hw_br : ∀ p ∈ split, p.2 < N + rNBit.1.length := by
          intro p hp; have := (hnodes p (hsplit_sub p hp)).2.2; omega
        have hBrP := addBranches_props N step rBit.2 rNBit.2 rNBit.1 split
        have hBrOut := addBranches_out_lt N step rBit.2 rNBit.2 rNBit.1 split
        obtain ⟨eBr, heBr⟩ := hBrP.1
        have hfull_ext : ∃ ext, rBr.1 = gs ++ ext :=
          ⟨eH ++ eB ++ [⟨GateOp.not, [rBit.2]⟩] ++ eBr, by
            rw [heBr, hNBitP.1, heB, heH]; simp [List.append_assoc]⟩
        obtain ⟨eAll, heAll⟩ := hfull_ext
        have hlenAll : gs.length ≤ rBr.1.length := by rw [heAll]; simp
        have hExt_Bit_to_NBit : ∃ ext, rNBit.1 = rBit.1 ++ ext := ⟨[⟨GateOp.not, [rBit.2]⟩], hNBitP.1⟩
        have hnF_hits : wireVal rHits.1 x nF = false := by
          rw [heH, wireVal_append_of_lt _ _ _ _ (by rw [hx]; exact hnF)]
          exact hnF_val
        have hbit_eval : wireVal rBit.1 x rBit.2 = true ↔ step ≤ M % 2 ^ (d + 1) := by
          rw [foldOr_eval N rHits.1 nF rHits.2 x hx hnF_hits (fun w hw => hHitsOut w hw)]
          rw [addHits_eval N step B gs split x hx hw_hits]
          constructor
          · rintro ⟨p, hp, hp_val, hB_p⟩
            have hp0 := hnodes p (hsplit_sub p hp)
            have hp_le : p.1 + step ≤ h := by simpa using (List.mem_filter.mp hp).2
            rw [hnodes_val p (hsplit_sub p hp)] at hp_val
            rw [hB_val _ hp_le] at hB_p
            have hpow : 0 < 2 ^ (d + 1) := Nat.pow_pos (by omega)
            rw [mod_pow_eq_sub hpow hp0.2.1 hp_val.1 hp_val.2]
            omega
          · intro hmod
            have hpow : 0 < 2 ^ (d + 1) := Nat.pow_pos (by omega)
            let L := 2 ^ (d + 1) * (M / 2 ^ (d + 1))
            have hLM : L + M % 2 ^ (d + 1) = M := Nat.div_add_mod M (2 ^ (d + 1))
            have hmod_lt : M % 2 ^ (d + 1) < 2 ^ (d + 1) := Nat.mod_lt M hpow
            have hL_dvd : 2 ^ (d + 1) ∣ L := ⟨M / 2 ^ (d + 1), rfl⟩
            obtain ⟨p, hp, hp1⟩ := hcomp L (by omega) hL_dvd
            have hp_s : p ∈ split := by
              exact List.mem_filter.mpr ⟨hp, by simpa using (by omega : p.1 + step ≤ h)⟩
            refine ⟨p, hp_s, ?_, ?_⟩
            · rw [hnodes_val p hp]
              omega
            · rw [hB_val _ (by omega)]
              omega
        have hbit_at_nbit : wireVal rNBit.1 x rBit.2 = true ↔ step ≤ M % 2 ^ (d + 1) := by
          rw [hNBitP.1, wireVal_append_of_lt _ _ _ _ (by rw [hx]; exact hBitOut)]
          exact hbit_eval
        have hnbit_at_nbit : wireVal rNBit.1 x rNBit.2 = true ↔ M % 2 ^ (d + 1) < step := by
          rw [addNot_eval N rBit.1 rBit.2 x hx]
          have hiff := not_congr hbit_eval
          simp only [Bool.not_eq_true, not_le] at hiff
          exact hiff
        have hnF' : nF < N + rBr.1.length := by omega
        have hnF_val' : wireVal rBr.1 x nF = false := by
          rw [heAll, wireVal_append_of_lt _ _ _ _ (by rw [hx]; exact hnF)]
          exact hnF_val
        have hB' : ∀ k ≤ h, B k < N + rBr.1.length := fun k hk => by have := hB k hk; omega
        have hB_val' : ∀ k ≤ h, wireVal rBr.1 x (B k) = true ↔ k ≤ M := by
          intro k hk
          rw [heAll, wireVal_append_of_lt _ _ _ _ (by rw [hx]; exact hB k hk)]
          exact hB_val k hk
        have hnodes' : ∀ p ∈ nosplit ++ rBr.2, p.1 ≤ h ∧ 2 ^ d ∣ p.1 ∧ p.2 < N + rBr.1.length := by
          intro p hp
          simp only [List.mem_append] at hp
          rcases hp with hp | hp
          · have h0 := hnodes p (hnosplit_sub p hp)
            exact ⟨h0.1, dvd_trans ⟨2, by rw [pow_succ]⟩ h0.2.1, by omega⟩
          · have hlt := hBrOut p hp
            have hmem : p.1 ∈ rBr.2.map Prod.fst := List.mem_map.mpr ⟨p, hp, rfl⟩
            rw [hBrP.2.2.2, List.mem_flatMap] at hmem
            obtain ⟨q, hq, hqm⟩ := hmem
            have hq0 := hnodes q (hsplit_sub q hq)
            have hqle : q.1 + step ≤ h := by simpa using (List.mem_filter.mp hq).2
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hqm
            rcases hqm with hEq | hEq
            · rw [hEq]
              exact ⟨by omega, dvd_trans ⟨2, by rw [pow_succ]⟩ hq0.2.1, hlt⟩
            · rw [hEq]
              exact ⟨hqle, dvd_add (dvd_trans ⟨2, by rw [pow_succ]⟩ hq0.2.1) dvd_rfl, hlt⟩
        have hcomp' : ∀ L ≤ h, 2 ^ d ∣ L → ∃ p ∈ nosplit ++ rBr.2, p.1 = L := by
          intro L hL hdvd
          by_cases hdvd1 : 2 ^ (d + 1) ∣ L
          · obtain ⟨p, hp, rfl⟩ := hcomp L hL hdvd1
            by_cases hle : p.1 + step ≤ h
            · have hp_s : p ∈ split := List.mem_filter.mpr ⟨hp, by simpa using hle⟩
              have hmem : p.1 ∈ rBr.2.map Prod.fst := by
                rw [hBrP.2.2.2, List.mem_flatMap]
                exact ⟨p, hp_s, by simp⟩
              obtain ⟨q, hq, hq1⟩ := List.mem_map.mp hmem
              exact ⟨q, List.mem_append_right _ hq, hq1⟩
            · have hp_ns : p ∈ nosplit := List.mem_filter.mpr ⟨hp, by simpa using (by omega : h < p.1 + step)⟩
              exact ⟨p, List.mem_append_left _ hp_ns, rfl⟩
          · obtain ⟨q, hq⟩ := hdvd
            have hq_odd : q % 2 = 1 := by
              by_contra hne
              obtain ⟨r, hrq⟩ := Nat.dvd_of_mod_eq_zero (by omega : q % 2 = 0)
              apply hdvd1
              exact ⟨r, by rw [hq, hrq, pow_succ]; ring⟩
            have hLge : step ≤ L := by
              have : 1 ≤ q := by omega
              calc step = step * 1 := (Nat.mul_one _).symm
                _ ≤ step * q := Nat.mul_le_mul_left _ this
                _ = L := hq.symm
            let L0 := L - step
            have hL0_dvd : 2 ^ (d + 1) ∣ L0 := by
              have hq1 : L0 = step * (q - 1) := by
                dsimp only [L0]
                rw [Nat.mul_sub_left_distrib, Nat.mul_one, ← hq]
              obtain ⟨r, hrq⟩ := Nat.dvd_of_mod_eq_zero (by omega : (q - 1) % 2 = 0)
              exact ⟨r, by rw [hq1, hrq, pow_succ]; ring⟩
            obtain ⟨p, hp, hpL⟩ := hcomp L0 (by omega) hL0_dvd
            have hp_s : p ∈ split := List.mem_filter.mpr ⟨hp, by simpa using (by omega : p.1 + step ≤ h)⟩
            have hmem : L ∈ rBr.2.map Prod.fst := by
              rw [hBrP.2.2.2, List.mem_flatMap]
              exact ⟨p, hp_s, by simp [hpL, L0]; omega⟩
            obtain ⟨q', hq', hq'1⟩ := List.mem_map.mp hmem
            exact ⟨q', List.mem_append_right _ hq', hq'1⟩
        have hnodes_val' : ∀ p ∈ nosplit ++ rBr.2, wireVal rBr.1 x p.2 = true ↔ p.1 ≤ M ∧ M < p.1 + step := by
          intro p hp
          simp only [List.mem_append] at hp
          rcases hp with hp | hp
          · have h0 := hnodes p (hnosplit_sub p hp)
            have hgt : h < p.1 + step := by simpa using (List.mem_filter.mp hp).2
            rw [heAll, wireVal_append_of_lt _ _ _ _ (by rw [hx]; exact h0.2.2)]
            rw [hnodes_val p (hnosplit_sub p hp)]
            have hpow : 2 ^ (d + 1) = step + step := by rw [pow_succ]; ring
            omega
          · have hev := addBranches_eval N step rBit.2 rNBit.2 rNBit.1 split x hx
              (by omega) hNBitP.2.2.1 hw_br p hp
            obtain ⟨q, hq, hcase⟩ := hev
            have hq0 := hnodes q (hsplit_sub q hq)
            have hq_ext : ∃ ext, rNBit.1 = gs ++ ext :=
              ⟨eH ++ eB ++ [⟨GateOp.not, [rBit.2]⟩], by rw [hNBitP.1, heB, heH]; simp [List.append_assoc]⟩
            obtain ⟨eN, heN⟩ := hq_ext
            have hq_pres : wireVal rNBit.1 x q.2 = wireVal gs x q.2 := by
              rw [heN, wireVal_append_of_lt _ _ _ _ (by rw [hx]; exact hq0.2.2)]
            have hpow : 0 < 2 ^ (d + 1) := Nat.pow_pos (by omega)
            have hpow2 : 2 ^ (d + 1) = step + step := by rw [pow_succ]; ring
            rcases hcase with ⟨hq1, hiff⟩ | ⟨hq1, hiff⟩
            · rw [hiff, hq_pres, hnodes_val q (hsplit_sub q hq), hnbit_at_nbit, hq1]
              constructor
              · rintro ⟨⟨h1, h2⟩, hmod⟩
                have := mod_pow_eq_sub hpow hq0.2.1 h1 h2
                omega
              · intro ⟨h1, h2⟩
                have h2' : M < q.1 + 2 ^ (d + 1) := by omega
                have := mod_pow_eq_sub hpow hq0.2.1 h1 h2'
                exact ⟨⟨h1, h2'⟩, by omega⟩
            · rw [hiff, hq_pres, hnodes_val q (hsplit_sub q hq), hbit_at_nbit, hq1]
              constructor
              · rintro ⟨⟨h1, h2⟩, hmod⟩
                have := mod_pow_eq_sub hpow hq0.2.1 h1 h2
                omega
              · intro ⟨h1, h2⟩
                have h1' : q.1 ≤ M := by omega
                have h2' : M < q.1 + 2 ^ (d + 1) := by omega
                have := mod_pow_eq_sub hpow hq0.2.1 h1' h2'
                exact ⟨⟨h1', h2'⟩, by omega⟩
        exact ih rBr.1 (nosplit ++ rBr.2) hnF' hnF_val' hB' hB_val' hnodes' hcomp' hnodes_val'

def namedAt {n m : ℕ} (a b c d : Fin m → Finset (Fin n)) :
    List (Fin m) → Finset (Fin n) → Prop
  | [], _ => True
  | j :: js, x =>
      ∃ u v, namedAt a b c d js u ∧ u ⊆ v ∧ v ⊆ x ∧
        a j ⊆ u ∧ u ⊆ b j ∧ c j ⊆ v ∧ v ⊆ d j

lemma namedAt_iff_rec {n m : ℕ} (a b c d : Fin m → Finset (Fin n))
    (js : List (Fin m)) (x : Finset (Fin n)) :
    namedAt a b c d js x ↔
      List.rec (motive := fun _ => Finset (Fin n) → Prop) (fun _ => True)
        (fun j _ prev y => ∃ u v, prev u ∧ u ⊆ v ∧ v ⊆ y ∧
          a j ⊆ u ∧ u ⊆ b j ∧ c j ⊆ v ∧ v ⊆ d j) js x := by
  induction js generalizing x with
  | nil => simp [namedAt]
  | cons j js ih =>
      simp only [namedAt]
      constructor
      · rintro ⟨u, v, h1, h2⟩
        exact ⟨u, v, (ih u).mp h1, h2⟩
      · rintro ⟨u, v, h1, h2⟩
        exact ⟨u, v, (ih u).mpr h1, h2⟩

lemma namedAt_mono {n m : ℕ} (a b c d : Fin m → Finset (Fin n))
    {js : List (Fin m)} {x y : Finset (Fin n)} (hxy : x ⊆ y)
    (h : namedAt a b c d js x) : namedAt a b c d js y := by
  cases js with
  | nil => trivial
  | cons j js' =>
      obtain ⟨u, v, h1, huv, hvx, hrest⟩ := h
      exact ⟨u, v, h1, huv, hvx.trans hxy, hrest⟩

lemma namedAt_tail {n m : ℕ} (a b c d : Fin m → Finset (Fin n))
    {j : Fin m} {js : List (Fin m)}
    (h : namedAt a b c d (j :: js) Finset.univ) :
    namedAt a b c d js Finset.univ := by
  obtain ⟨u, _, h1, _⟩ := h
  exact namedAt_mono a b c d (Finset.subset_univ u) h1

lemma namedAt_length_le {n m h : ℕ} (a b c d : Fin m → Finset (Fin n))
    (Hlen : ∀ js : List (Fin m), js.length = h + 1 → ¬namedAt a b c d js Finset.univ) :
    ∀ js : List (Fin m), namedAt a b c d js Finset.univ → js.length ≤ h := by
  intro js hjs
  induction js with
  | nil => simp
  | cons j js' ih =>
      by_cases hle : (j :: js').length ≤ h
      · exact hle
      · have hgt : h + 1 ≤ (j :: js').length := by omega
        by_cases heq : (j :: js').length = h + 1
        · exact False.elim (Hlen (j :: js') heq hjs)
        · have ih' := ih (namedAt_tail a b c d hjs)
          simp only [List.length_cons] at heq hle ih' ⊢
          omega

lemma namedAt_replicate {n m : ℕ} (a b c d : Fin m → Finset (Fin n))
    (j : Fin m) (U : Finset (Fin n))
    (ha : a j ⊆ U) (hb : U ⊆ b j) (hc : c j ⊆ U) (hd : U ⊆ d j)
    (k : ℕ) : namedAt a b c d (List.replicate k j) Finset.univ := by
  have hk : ∀ t, namedAt a b c d (List.replicate t j) U := by
    intro t
    induction t with
    | zero => simp [namedAt]
    | succ t iht =>
        simp only [List.replicate_succ, namedAt]
        exact ⟨U, U, iht, Finset.Subset.rfl, Finset.Subset.rfl, ha, hb, hc, hd⟩
  exact namedAt_mono a b c d (Finset.subset_univ U) (hk k)

lemma namedAt_restrict {n m : ℕ} (a b c d : Fin m → Finset (Fin n))
    (W : Finset (Fin n)) :
    ∀ (js : List (Fin m)) (z : Finset (Fin n)),
      namedAt a b c d js z → (∀ i ∈ js, a i ∪ c i ⊆ W) →
      namedAt a b c d js (z ∩ W) := by
  intro js
  induction js with
  | nil => intro z _ _; simp [namedAt]
  | cons i js ih =>
      intro z hz hW
      obtain ⟨u, v, hprev, huv, hvz, hai, hbi, hci, hdi⟩ := hz
      have hiW : a i ∪ c i ⊆ W := hW i (by simp)
      refine ⟨u ∩ W, v ∩ W, ih u hprev (fun k hk => hW k (by simp [hk])), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact Finset.inter_subset_inter_right huv
      · exact Finset.inter_subset_inter_right hvz
      · exact Finset.subset_inter hai (Finset.subset_union_left.trans hiW)
      · exact Finset.inter_subset_left.trans hbi
      · exact Finset.subset_inter hci (Finset.subset_union_right.trans hiW)
      · exact Finset.inter_subset_left.trans hdi

noncomputable def buildStage2 {m : ℕ} (n : ℕ) (ℱ : Finset (Finset (Fin m)))
    (stepE : ℕ → (Finset (Fin m) → ℕ) → List Gate → Finset (Fin m) → List Gate × ℕ)
    (gs2 : List Gate) : ℕ → List Gate × (Finset (Fin m) → ℕ)
  | 0 => (gs2, fun _ => n + 1)
  | k + 1 =>
      let prev := buildStage2 n ℱ stepE gs2 k
      let bucket := (ℱ.filter (fun S => S.card = k + 1)).toList
      let r := buildMap (stepE k prev.2) (n + 1) prev.1 bucket
      (r.1, fun S => if S ∈ ℱ ∧ S.card = k + 1 then r.2 S else prev.2 S)

end PEqualNP.Outside.L_lib_1242_aux

theorem PEqualNP.Outside.L_lib_1242 : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (n m r h : Nat) (a b c d : Fin m → Finset (Fin n)),
  let X := Finset (Fin n)
  let named := fun (js : List (Fin m)) =>
    List.rec (motive := fun _ => X → Prop) (fun _ => True)
      (fun j _ prev x => ∃ u v, prev u ∧ u ⊆ v ∧ v ⊆ x ∧
        a j ⊆ u ∧ u ⊆ b j ∧ c j ⊆ v ∧ v ⊆ d j) js Finset.univ
  let F := ((Finset.univ : Finset (Finset (Fin m))).filter (fun S =>
    ∃ js : List (Fin m), js.Nodup ∧ js.toFinset=S ∧ named js)).card
  h < 2^r → (∀ js : List (Fin m), js.length=h+1 → ¬named js) →
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin m → Fin (n+2+C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    C.output < n+2+C.size ∧ PEqualNP.NotBracket.notCount C ≤ r ∧
    C.size-PEqualNP.NotBracket.notCount C ≤ 2*n*m+m+(m+3)*F+5*h ∧
    ∀ (x : X) (j : Fin m),
      let input := List.ofFn (fun i : Fin n => decide (i∈x)) ++ [false,true]
      let output := (C.wires input).getD (tap j).val false
      (a j ⊆ x ∧ x ⊆ b j → output=true) ∧ (c j ⊆ x ∧ x ⊆ d j → output=false)) := by
  intro n m r h a b c d _X named F hr hlen
  let N := n + 2
  let inp : Finset (Fin n) → List Bool := fun x =>
    List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]
  have hinp_len : ∀ x, (inp x).length = N := by
    intro x
    simp [inp, N]
  have hinp_bit : ∀ x (i : Fin n),
      PEqualNP.Outside.L_lib_1242_aux.wireVal [] (inp x) i.val = decide (i ∈ x) := by
    intro x i
    unfold PEqualNP.Outside.L_lib_1242_aux.wireVal
    simp [inp, List.getD_eq_getElem?_getD, List.getElem?_append_left, i.isLt]
  have hinp_false : ∀ x, PEqualNP.Outside.L_lib_1242_aux.wireVal [] (inp x) n = false := by
    intro x
    unfold PEqualNP.Outside.L_lib_1242_aux.wireVal
    simp [inp, List.getD_eq_getElem?_getD]
  have hinp_true : ∀ x, PEqualNP.Outside.L_lib_1242_aux.wireVal [] (inp x) (n + 1) = true := by
    intro x
    unfold PEqualNP.Outside.L_lib_1242_aux.wireVal
    simp [inp, List.getD_eq_getElem?_getD]
  let ℱ : Finset (Finset (Fin m)) := @Finset.filter (Finset (Fin m)) (fun S =>
    ∃ js : List (Fin m), js.Nodup ∧ js.toFinset = S ∧
      PEqualNP.Outside.L_lib_1242_aux.namedAt a b c d js Finset.univ)
    (fun _ => Classical.propDecidable _) (Finset.univ : Finset (Finset (Fin m)))
  have hF_eq : F = ℱ.card := by
    dsimp only [F, named]
    apply Finset.card_bij (fun S _ => S)
    · intro S hS
      simp only [ℱ, Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
      obtain ⟨js, hnd, hts, hnm⟩ := hS
      refine ⟨js, hnd, ?_, (PEqualNP.Outside.L_lib_1242_aux.namedAt_iff_rec a b c d js Finset.univ).mpr hnm⟩
      rw [← hts]; ext i; simp
    · intro _ _ _ _ heq; exact heq
    · intro S hS
      simp only [ℱ, Finset.mem_filter, Finset.mem_univ, true_and] at hS
      obtain ⟨js, hnd, hts, hnm⟩ := hS
      refine ⟨S, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨js, hnd, ?_, (PEqualNP.Outside.L_lib_1242_aux.namedAt_iff_rec a b c d js Finset.univ).mp hnm⟩
      rw [← hts]; ext i; simp
  have hlen_at : ∀ js : List (Fin m), js.length = h + 1 →
      ¬PEqualNP.Outside.L_lib_1242_aux.namedAt a b c d js Finset.univ := by
    intro js hjs hnm
    exact hlen js hjs ((PEqualNP.Outside.L_lib_1242_aux.namedAt_iff_rec a b c d js Finset.univ).mp hnm)
  have hℱ_empty : ∅ ∈ ℱ := by
    simp only [ℱ, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨[], List.nodup_nil, by simp, trivial⟩
  have hℱ_card_le : ∀ S ∈ ℱ, S.card ≤ h := by
    intro S hS
    simp only [ℱ, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    obtain ⟨js, hnd, rfl, hnm⟩ := hS
    rw [List.toFinset_card_of_nodup hnd]
    exact PEqualNP.Outside.L_lib_1242_aux.namedAt_length_le a b c d hlen_at js hnm
  have hℱ_pred : ∀ S ∈ ℱ, S.Nonempty → ∃ j ∈ S, S.erase j ∈ ℱ := by
    intro S hS hne
    simp only [ℱ, Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    obtain ⟨js, hnd, rfl, hnm⟩ := hS
    cases js with
    | nil => simp at hne
    | cons j js' =>
        simp only [List.nodup_cons] at hnd
        refine ⟨j, by simp, js', hnd.2, ?_, PEqualNP.Outside.L_lib_1242_aux.namedAt_tail a b c d hnm⟩
        ext i
        simp only [Finset.mem_erase, List.mem_toFinset, List.mem_cons]
        constructor
        · intro hi; exact ⟨fun heq => hnd.1 (heq ▸ hi), Or.inr hi⟩
        · rintro ⟨hne', rfl | hi⟩
          · exact False.elim (hne' rfl)
          · exact hi
  let stepP : List PEqualNP.CircuitLowerBounds.Gate → Fin m → List PEqualNP.CircuitLowerBounds.Gate × ℕ :=
    fun gs j => PEqualNP.Outside.L_lib_1242_aux.foldAnd N gs (n + 1) ((a j).toList.map Fin.val)
  let rP := PEqualNP.Outside.L_lib_1242_aux.buildMap stepP (n + 1) [] (List.finRange m)
  let gs1 := rP.1
  let P := rP.2
  let Inv1 : List PEqualNP.CircuitLowerBounds.Gate → Prop := fun gs =>
    PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack N ⟨gs, 0⟩
  have hP_wf : Inv1 gs1 := by
    have h0 : Inv1 [] := ⟨fun g hg => by simp at hg, fun j hj => by simp at hj⟩
    have hext := PEqualNP.Outside.L_lib_1242_aux.buildMap_ext stepP (n + 1) Inv1
      (fun gs j ⟨hf, hr⟩ => by
        obtain ⟨e, he, _⟩ := PEqualNP.Outside.L_lib_1242_aux.foldAnd_ext N gs (n + 1) ((a j).toList.map Fin.val)
        refine ⟨e, he, PEqualNP.Outside.L_lib_1242_aux.foldAnd_fanInTwo N gs (n + 1) _ hf, ?_⟩
        apply PEqualNP.Outside.L_lib_1242_aux.foldAnd_readsBack N gs (n + 1) _ hr
        intro w hw; simp only [List.mem_map] at hw; obtain ⟨i, _, rfl⟩ := hw; omega)
      [] (List.finRange m) h0
    obtain ⟨_, _, hwf⟩ := hext
    exact hwf
  have hP_counts : PEqualNP.NotBracket.notCount ⟨gs1, 0⟩ = 0 ∧
      PEqualNP.Outside.L_lib_1242_aux.nonNotCount gs1 ≤ n * m := by
    have hc := PEqualNP.Outside.L_lib_1242_aux.buildMap_counts stepP (n + 1)
      (fun _ => n) (fun _ => True) (fun _ _ _ => trivial)
      (fun gs j _ => by
        have hfc := PEqualNP.Outside.L_lib_1242_aux.foldAnd_counts N gs (n + 1) ((a j).toList.map Fin.val)
        have hlen_a : ((a j).toList.map Fin.val).length ≤ n := by
          rw [List.length_map, Finset.length_toList]
          calc (a j).card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
            _ = n := Finset.card_fin n
        exact ⟨hfc.1, hfc.2.trans (Nat.add_le_add_left hlen_a _)⟩) [] (List.finRange m) trivial
    have hsum : ((List.finRange m).map (fun _ : Fin m => n)).sum = n * m := by
      simp [List.sum_replicate, List.length_finRange, Nat.mul_comm]
    refine ⟨?_, ?_⟩
    · simpa [PEqualNP.NotBracket.notCount] using hc.1
    · have h0 : PEqualNP.Outside.L_lib_1242_aux.nonNotCount [] = 0 := rfl
      calc PEqualNP.Outside.L_lib_1242_aux.nonNotCount gs1
          ≤ PEqualNP.Outside.L_lib_1242_aux.nonNotCount [] + ((List.finRange m).map (fun _ : Fin m => n)).sum := hc.2
        _ = n * m := by rw [h0, zero_add, hsum]
  have hP_out : ∀ j, P j < N + gs1.length := by
    apply PEqualNP.Outside.L_lib_1242_aux.buildMap_out_lt N stepP (n + 1) (fun _ => True)
    · intro gs j _
      obtain ⟨e, he, _⟩ := PEqualNP.Outside.L_lib_1242_aux.foldAnd_ext N gs (n + 1) ((a j).toList.map Fin.val)
      exact ⟨e, he, trivial⟩
    · intro gs j _
      apply PEqualNP.Outside.L_lib_1242_aux.foldAnd_out_lt N gs (n + 1) _ (by omega)
      intro w hw
      simp only [List.mem_map] at hw
      obtain ⟨i, _, rfl⟩ := hw
      omega
    · trivial
    · dsimp only [N]; omega
  have hP_eval : ∀ x j, PEqualNP.Outside.L_lib_1242_aux.wireVal gs1 (inp x) (P j) = true ↔ a j ⊆ x := by
    intro x j
    have hev := PEqualNP.Outside.L_lib_1242_aux.buildMap_eval N stepP (n + 1)
      (fun _ => True) (inp x) (hinp_len x) (fun j => a j ⊆ x)
      (fun gs j _ => by
        obtain ⟨e, he, _⟩ := PEqualNP.Outside.L_lib_1242_aux.foldAnd_ext N gs (n + 1) ((a j).toList.map Fin.val)
        exact ⟨e, he, trivial⟩)
      (fun gs j _ => by
        apply PEqualNP.Outside.L_lib_1242_aux.foldAnd_out_lt N gs (n + 1) _ (by dsimp only [N]; omega)
        intro w hw
        simp only [List.mem_map] at hw
        obtain ⟨i, _, rfl⟩ := hw
        omega)
      (fun gs j _ => by
        have hgs0 : gs = [] ++ gs := rfl
        have htrue : PEqualNP.Outside.L_lib_1242_aux.wireVal gs (inp x) (n + 1) = true := by
          rw [hgs0, PEqualNP.Outside.L_lib_1242_aux.wireVal_append_of_lt [] _ _ _ (by rw [hinp_len]; omega)]
          exact hinp_true x
        have hws : ∀ w ∈ (a j).toList.map Fin.val, w < N + gs.length := by
          intro w hw
          simp only [List.mem_map] at hw
          obtain ⟨i, _, rfl⟩ := hw
          omega
        rw [PEqualNP.Outside.L_lib_1242_aux.foldAnd_eval N gs (n + 1) _ (inp x) (hinp_len x) htrue hws]
        constructor
        · intro hall i hi
          have hw : i.val ∈ (a j).toList.map Fin.val := List.mem_map.mpr ⟨i, Finset.mem_toList.mpr hi, rfl⟩
          have hval := hall i.val hw
          rw [hgs0, PEqualNP.Outside.L_lib_1242_aux.wireVal_append_of_lt [] _ _ _
            (by rw [hinp_len]; omega), hinp_bit] at hval
          exact of_decide_eq_true hval
        · intro hsub w hw
          simp only [List.mem_map, Finset.mem_toList] at hw
          obtain ⟨i, hi, rfl⟩ := hw
          rw [hgs0, PEqualNP.Outside.L_lib_1242_aux.wireVal_append_of_lt [] _ _ _
            (by rw [hinp_len]; omega), hinp_bit]
          exact decide_eq_true (hsub hi))
      [] (List.finRange m) (List.nodup_finRange m) trivial j (List.mem_finRange j)
    exact hev
  let stepQ : List PEqualNP.CircuitLowerBounds.Gate → Fin m → List PEqualNP.CircuitLowerBounds.Gate × ℕ :=
    fun gs j => PEqualNP.Outside.L_lib_1242_aux.foldAnd N gs (n + 1) ((a j ∪ c j).toList.map Fin.val)
  let rQ := PEqualNP.Outside.L_lib_1242_aux.buildMap stepQ (n + 1) gs1 (List.finRange m)
  let gs2 := rQ.1
  let Q := rQ.2
  have hQ_ext : ∃ e, gs2 = gs1 ++ e := by
    obtain ⟨e, he, _⟩ := PEqualNP.Outside.L_lib_1242_aux.buildMap_ext stepQ (n + 1) (fun _ => True)
      (fun gs j _ => by
        obtain ⟨e1, he1, _⟩ := PEqualNP.Outside.L_lib_1242_aux.foldAnd_ext N gs (n + 1) _
        exact ⟨e1, he1, trivial⟩) gs1 (List.finRange m) trivial
    exact ⟨e, he⟩
  have hQ_wf : Inv1 gs2 := by
    have hext := PEqualNP.Outside.L_lib_1242_aux.buildMap_ext stepQ (n + 1) Inv1
      (fun gs j ⟨hf, hr⟩ => by
        obtain ⟨e, he, _⟩ := PEqualNP.Outside.L_lib_1242_aux.foldAnd_ext N gs (n + 1) _
        refine ⟨e, he, PEqualNP.Outside.L_lib_1242_aux.foldAnd_fanInTwo N gs (n + 1) _ hf, ?_⟩
        apply PEqualNP.Outside.L_lib_1242_aux.foldAnd_readsBack N gs (n + 1) _ hr
        intro w hw; simp only [List.mem_map] at hw; obtain ⟨i, _, rfl⟩ := hw; omega)
      gs1 (List.finRange m) hP_wf
    obtain ⟨_, _, hwf⟩ := hext
    exact hwf
  have hQ_counts : PEqualNP.NotBracket.notCount ⟨gs2, 0⟩ = 0 ∧
      PEqualNP.Outside.L_lib_1242_aux.nonNotCount gs2 ≤ 2 * n * m := by
    have hc := PEqualNP.Outside.L_lib_1242_aux.buildMap_counts stepQ (n + 1)
      (fun _ => n) (fun _ => True) (fun _ _ _ => trivial)
      (fun gs j _ => by
        have hfc := PEqualNP.Outside.L_lib_1242_aux.foldAnd_counts N gs (n + 1) ((a j ∪ c j).toList.map Fin.val)
        have hlen_ac : ((a j ∪ c j).toList.map Fin.val).length ≤ n := by
          rw [List.length_map, Finset.length_toList]
          calc (a j ∪ c j).card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
            _ = n := Finset.card_fin n
        exact ⟨hfc.1, hfc.2.trans (Nat.add_le_add_left hlen_ac _)⟩) gs1 (List.finRange m) trivial
    have hsum : ((List.finRange m).map (fun _ : Fin m => n)).sum = n * m := by
      simp [List.sum_replicate, List.length_finRange, Nat.mul_comm]
    refine ⟨?_, ?_⟩
    · rw [hc.1, hP_counts.1]
    · calc PEqualNP.Outside.L_lib_1242_aux.nonNotCount gs2
          ≤ PEqualNP.Outside.L_lib_1242_aux.nonNotCount gs1 + ((List.finRange m).map (fun _ : Fin m => n)).sum := hc.2
        _ ≤ n * m + n * m := Nat.add_le_add hP_counts.2 (by rw [hsum])
        _ = 2 * n * m := by ring
  have hQ_out : ∀ j, Q j < N + gs2.length := by
    apply PEqualNP.Outside.L_lib_1242_aux.buildMap_out_lt N stepQ (n + 1) (fun _ => True)
    · intro gs j _
      obtain ⟨e, he, _⟩ := PEqualNP.Outside.L_lib_1242_aux.foldAnd_ext N gs (n + 1) _
      exact ⟨e, he, trivial⟩
    · intro gs j _
      apply PEqualNP.Outside.L_lib_1242_aux.foldAnd_out_lt N gs (n + 1) _ (by omega)
      intro w hw
      simp only [List.mem_map] at hw
      obtain ⟨i, _, rfl⟩ := hw
      omega
    · trivial
    · dsimp only [N]; omega
  have hP_out2 : ∀ j, P j < N + gs2.length := by
    intro j
    obtain ⟨e, he⟩ := hQ_ext
    rw [he]; simp only [List.length_append]; have := hP_out j; omega
  have hP_eval2 : ∀ x j, PEqualNP.Outside.L_lib_1242_aux.wireVal gs2 (inp x) (P j) = true ↔ a j ⊆ x := by
    intro x j
    obtain ⟨e, he⟩ := hQ_ext
    rw [he, PEqualNP.Outside.L_lib_1242_aux.wireVal_append_of_lt _ _ _ _ (by rw [hinp_len]; exact hP_out j)]
    exact hP_eval x j
  have hQ_eval : ∀ x j, PEqualNP.Outside.L_lib_1242_aux.wireVal gs2 (inp x) (Q j) = true ↔ a j ∪ c j ⊆ x := by
    intro x j
    have hev := PEqualNP.Outside.L_lib_1242_aux.buildMap_eval N stepQ (n + 1)
      (fun gs => ∃ e, gs = gs1 ++ e) (inp x) (hinp_len x) (fun j => a j ∪ c j ⊆ x)
      (fun gs j hgs_ex => by
        rcases hgs_ex with ⟨e0, rfl⟩
        obtain ⟨e, he, _⟩ := PEqualNP.Outside.L_lib_1242_aux.foldAnd_ext N (gs1 ++ e0) (n + 1) _
        exact ⟨e, he, ⟨e0 ++ e, by rw [he, List.append_assoc]⟩⟩)
      (fun gs j _ => by
        apply PEqualNP.Outside.L_lib_1242_aux.foldAnd_out_lt N gs (n + 1) _ (by omega)
        intro w hw
        simp only [List.mem_map] at hw
        obtain ⟨i, _, rfl⟩ := hw
        omega)
      (fun gs j ⟨e0, hgs_eq⟩ => by
        have htrue : PEqualNP.Outside.L_lib_1242_aux.wireVal gs (inp x) (n + 1) = true := by
          have hgs0 : gs = [] ++ gs := rfl
          rw [hgs0, PEqualNP.Outside.L_lib_1242_aux.wireVal_append_of_lt [] _ _ _ (by rw [hinp_len]; omega)]
          exact hinp_true x
        have hws : ∀ w ∈ (a j ∪ c j).toList.map Fin.val, w < N + gs.length := by
          intro w hw
          simp only [List.mem_map] at hw
          obtain ⟨i, _, rfl⟩ := hw
          omega
        rw [PEqualNP.Outside.L_lib_1242_aux.foldAnd_eval N gs (n + 1) _ (inp x) (hinp_len x) htrue hws]
        constructor
        · intro hall i hi
          have hw : i.val ∈ (a j ∪ c j).toList.map Fin.val := List.mem_map.mpr ⟨i, Finset.mem_toList.mpr hi, rfl⟩
          have hval := hall i.val hw
          have hgs0 : gs = [] ++ gs := rfl
          rw [hgs0, PEqualNP.Outside.L_lib_1242_aux.wireVal_append_of_lt [] _ _ _
            (by rw [hinp_len]; omega), hinp_bit] at hval
          exact of_decide_eq_true hval
        · intro hsub w hw
          simp only [List.mem_map, Finset.mem_toList] at hw
          obtain ⟨i, hi, rfl⟩ := hw
          have hgs0 : gs = [] ++ gs := rfl
          rw [hgs0, PEqualNP.Outside.L_lib_1242_aux.wireVal_append_of_lt [] _ _ _
            (by rw [hinp_len]; omega), hinp_bit]
          exact decide_eq_true (hsub hi))
      gs1 (List.finRange m) (List.nodup_finRange m) ⟨[], by simp⟩ j (List.mem_finRange j)
    exact hev
  let stepE : ℕ → (Finset (Fin m) → ℕ) → List PEqualNP.CircuitLowerBounds.Gate → Finset (Fin m) → List PEqualNP.CircuitLowerBounds.Gate × ℕ :=
    fun k prevE gs S =>
      if hS : S ∈ ℱ ∧ S.Nonempty ∧ S.card = k + 1 then
        let j := Classical.choose (hℱ_pred S hS.1 hS.2.1)
        PEqualNP.Outside.L_lib_1242_aux.addAnd N gs (prevE (S.erase j)) (Q j)
      else (gs, n + 1)
  have hStage2 : ∀ k : ℕ,
      let st := PEqualNP.Outside.L_lib_1242_aux.buildStage2 n ℱ stepE gs2 k
      (∃ e, st.1 = gs2 ++ e) ∧
      PEqualNP.MetaComplexity.FanInTwo ⟨st.1, 0⟩ ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack N ⟨st.1, 0⟩ ∧
      PEqualNP.NotBracket.notCount ⟨st.1, 0⟩ = 0 ∧
      PEqualNP.Outside.L_lib_1242_aux.nonNotCount st.1 ≤
        PEqualNP.Outside.L_lib_1242_aux.nonNotCount gs2 +
          (ℱ.filter (fun S => 1 ≤ S.card ∧ S.card ≤ k)).card ∧
      (∀ S ∈ ℱ, S.card ≤ k → st.2 S < N + st.1.length) ∧
      (∀ x S, S ∈ ℱ → S.card ≤ k →
        (PEqualNP.Outside.L_lib_1242_aux.wireVal st.1 (inp x) (st.2 S) = true ↔
          ∀ i ∈ S, a i ∪ c i ⊆ x)) := by
    intro k
    induction k with
    | zero =>
        simp only [PEqualNP.Outside.L_lib_1242_aux.buildStage2]
        refine ⟨⟨[], by simp⟩, hQ_wf.1, hQ_wf.2, hQ_counts.1, ?_, ?_, ?_⟩
        · simp
        · intro S _ _; dsimp only [N]; omega
        · intro x S _ hS0
          have hSe : S = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hS0)
          subst hSe
          have hgs2_eq : gs2 = [] ++ gs2 := rfl
          rw [hgs2_eq, PEqualNP.Outside.L_lib_1242_aux.wireVal_append_of_lt [] _ _ _ (by rw [hinp_len]; omega), hinp_true]
          simp
    | succ k ih =>
        obtain ⟨⟨ep, hep⟩, hpf, hpr, hpnc, hpnnc, hpout, hpeval⟩ := ih
        set prev := PEqualNP.Outside.L_lib_1242_aux.buildStage2 n ℱ stepE gs2 k
        set bucket := (ℱ.filter (fun S => S.card = k + 1)).toList
        let Inv : List PEqualNP.CircuitLowerBounds.Gate → Prop := fun gs =>
          (∃ e, gs = prev.1 ++ e) ∧
          PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ ∧
          PEqualNP.MetaComplexity.NestedCover.ReadsBack N ⟨gs, 0⟩
        have hstep_ext : ∀ gs S, Inv gs →
            ∃ e, (stepE k prev.2 gs S).1 = gs ++ e ∧ Inv (stepE k prev.2 gs S).1 := by
          intro gs S ⟨⟨eg, heg⟩, hgf, hgr⟩
          dsimp only [stepE]
          split_ifs with hS
          · set j := Classical.choose (hℱ_pred S hS.1 hS.2.1)
            have hj := Classical.choose_spec (hℱ_pred S hS.1 hS.2.1)
            have hS'_card : (S.erase j).card ≤ k := by
              rw [Finset.card_erase_of_mem hj.1, hS.2.2]; omega
            have hE_lt : prev.2 (S.erase j) < N + gs.length := by
              have := hpout (S.erase j) hj.2 hS'_card
              rw [heg]; simp only [List.length_append]; omega
            have hQ_lt : Q j < N + gs.length := by
              have := hQ_out j
              rw [heg, hep]; simp only [List.length_append]; omega
            have hwf := PEqualNP.Outside.L_lib_1242_aux.addAnd_wf N gs (prev.2 (S.erase j)) (Q j) hgf hgr hE_lt hQ_lt
            exact ⟨_, (PEqualNP.Outside.L_lib_1242_aux.addAnd_props N gs _ _).1,
              ⟨⟨eg ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [prev.2 (S.erase j), Q j]⟩],
                by rw [(PEqualNP.Outside.L_lib_1242_aux.addAnd_props N gs _ _).1, heg, List.append_assoc]⟩, hwf.1, hwf.2⟩⟩
          · exact ⟨[], by simp, ⟨⟨eg, heg⟩, hgf, hgr⟩⟩
        have hstep_out : ∀ gs S, Inv gs → (stepE k prev.2 gs S).2 < N + (stepE k prev.2 gs S).1.length := by
          intro gs S _
          dsimp only [stepE]
          split_ifs with hS
          · exact (PEqualNP.Outside.L_lib_1242_aux.addAnd_props N gs _ _).2.2.1
          · dsimp only [N]; omega
        have hInv0 : Inv prev.1 := ⟨⟨[], by simp⟩, hpf, hpr⟩
        have hr_ext := PEqualNP.Outside.L_lib_1242_aux.buildMap_ext (stepE k prev.2) (n + 1) Inv hstep_ext prev.1 bucket hInv0
        obtain ⟨eb, heb, hInv_r⟩ := hr_ext
        have hr_cnt := PEqualNP.Outside.L_lib_1242_aux.buildMap_counts (stepE k prev.2) (n + 1) (fun _ => 1) Inv
          (fun gs S hI => by obtain ⟨_, _, h⟩ := hstep_ext gs S hI; exact h)
          (fun gs S _ => by
            dsimp only [stepE]
            split_ifs with hS
            · have hp := PEqualNP.Outside.L_lib_1242_aux.addAnd_props N gs
                (prev.2 (S.erase (Classical.choose (hℱ_pred S hS.1 hS.2.1))))
                (Q (Classical.choose (hℱ_pred S hS.1 hS.2.1)))
              exact ⟨hp.2.2.2.1, by rw [hp.2.2.2.2]⟩
            · exact ⟨rfl, Nat.le_add_right _ _⟩) prev.1 bucket hInv0
        have hr_out := PEqualNP.Outside.L_lib_1242_aux.buildMap_out_lt N (stepE k prev.2) (n + 1) Inv
          hstep_ext hstep_out prev.1 bucket hInv0 (by dsimp only [N]; omega)
        have hsum_b : (bucket.map (fun _ : Finset (Fin m) => 1)).sum =
            (ℱ.filter (fun S => S.card = k + 1)).card := by
          simp [bucket, List.sum_replicate, Finset.length_toList]
        have hpart : (ℱ.filter (fun S => 1 ≤ S.card ∧ S.card ≤ k)).card +
            (ℱ.filter (fun S => S.card = k + 1)).card =
            (ℱ.filter (fun S => 1 ≤ S.card ∧ S.card ≤ k + 1)).card := by
          rw [← Finset.card_union_of_disjoint]
          · congr 1; ext S; simp only [Finset.mem_union, Finset.mem_filter]
            constructor
            · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2⟩) <;> exact ⟨h1, by omega, by omega⟩
            · rintro ⟨h1, h2, h3⟩
              by_cases hck : S.card = k + 1
              · exact Or.inr ⟨h1, hck⟩
              · exact Or.inl ⟨h1, h2, by omega⟩
          · rw [Finset.disjoint_left]; intro S h1 h2; simp only [Finset.mem_filter] at h1 h2; omega
        simp only [PEqualNP.Outside.L_lib_1242_aux.buildStage2]
        refine ⟨⟨ep ++ eb, by rw [heb, hep, List.append_assoc]⟩, hInv_r.2.1, hInv_r.2.2, ?_, ?_, ?_, ?_⟩
        · rw [hr_cnt.1, hpnc]
        · dsimp only [prev, bucket] at hpnnc hr_cnt hsum_b
          exact hr_cnt.2.trans (by rw [hsum_b, ← hpart, ← Nat.add_assoc]; exact Nat.add_le_add_right hpnnc _)
        · intro S hS hSc
          by_cases hck : S.card = k + 1
          · simp only [hS, hck, and_self, ↓reduceIte]
            exact hr_out S
          · simp only [hS, hck, and_false, ↓reduceIte]
            have hlt := hpout S hS (by omega)
            dsimp only [prev] at heb hlt
            rw [heb]; simp only [List.length_append]; omega
        · intro x S hS hSc
          by_cases hck : S.card = k + 1
          · simp only [hS, hck, and_self, ↓reduceIte]
            have hSin : S ∈ bucket := by simp [bucket, hS, hck]
            have hev := PEqualNP.Outside.L_lib_1242_aux.buildMap_eval_mem N (stepE k prev.2) (n + 1) Inv
              (inp x) (hinp_len x) (fun T => ∀ i ∈ T, a i ∪ c i ⊆ x) hstep_ext hstep_out
              prev.1 bucket (Finset.nodup_toList _) hInv0
              (fun gs T hTmem ⟨⟨eg, heg⟩, _, _⟩ => by
                have hTmem' : T ∈ ℱ ∧ T.card = k + 1 := by
                  simpa [bucket] using hTmem
                have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
                have hTcond : T ∈ ℱ ∧ T.Nonempty ∧ T.card = k + 1 := ⟨hTmem'.1, hTne, hTmem'.2⟩
                dsimp only [stepE]
                rw [dif_pos hTcond]
                set j := Classical.choose (hℱ_pred T hTcond.1 hTcond.2.1)
                have hj := Classical.choose_spec (hℱ_pred T hTcond.1 hTcond.2.1)
                have hT'_card : (T.erase j).card ≤ k := by
                  rw [Finset.card_erase_of_mem hj.1, hTcond.2.2]; omega
                rw [PEqualNP.Outside.L_lib_1242_aux.addAnd_eval N gs _ _ (inp x) (hinp_len x)]
                rw [heg, PEqualNP.Outside.L_lib_1242_aux.wireVal_append_of_lt _ _ _ _
                  (by rw [hinp_len]; exact hpout _ hj.2 hT'_card)]
                have hgs_q : prev.1 ++ eg = gs2 ++ (ep ++ eg) := by rw [hep, List.append_assoc]
                rw [hgs_q, PEqualNP.Outside.L_lib_1242_aux.wireVal_append_of_lt _ _ _ _
                  (by rw [hinp_len]; exact hQ_out j)]
                rw [hpeval x (T.erase j) hj.2 hT'_card, hQ_eval x j]
                constructor
                · intro ⟨hsub1, hsub2⟩ i hi
                  by_cases hij : i = j
                  · subst hij; exact hsub2
                  · exact hsub1 i (Finset.mem_erase.mpr ⟨hij, hi⟩)
                · intro hall
                  exact ⟨fun i hi => hall i (Finset.mem_erase.mp hi).2, hall j hj.1⟩)
              S hSin
            exact hev
          · simp only [hS, hck, and_false, ↓reduceIte]
            rw [heb, PEqualNP.Outside.L_lib_1242_aux.wireVal_append_of_lt _ _ _ _
              (by rw [hinp_len]; exact hpout S hS (by omega))]
            exact hpeval x S hS (by omega)
  obtain ⟨⟨e3, he3⟩, hE_f, hE_r, hE_nc, hE_nnc, hE_out_all, hE_eval_all⟩ := hStage2 h
  let stE := PEqualNP.Outside.L_lib_1242_aux.buildStage2 n ℱ stepE gs2 h
  let gs3 := stE.1
  let E := stE.2
  have hE_out : ∀ S ∈ ℱ, E S < N + gs3.length := fun S hS => hE_out_all S hS (hℱ_card_le S hS)
  have hE_eval : ∀ x S, S ∈ ℱ →
      (PEqualNP.Outside.L_lib_1242_aux.wireVal gs3 (inp x) (E S) = true ↔ ∀ i ∈ S, a i ∪ c i ⊆ x) :=
    fun x S hS => hE_eval_all x S hS (hℱ_card_le S hS)
  have hE_nnc' : PEqualNP.Outside.L_lib_1242_aux.nonNotCount gs3 ≤ 2 * n * m + ℱ.card := by
    dsimp only [gs3, stE]
    calc PEqualNP.Outside.L_lib_1242_aux.nonNotCount (PEqualNP.Outside.L_lib_1242_aux.buildStage2 n ℱ stepE gs2 h).1
        ≤ PEqualNP.Outside.L_lib_1242_aux.nonNotCount gs2 + (ℱ.filter (fun S => 1 ≤ S.card ∧ S.card ≤ h)).card := hE_nnc
      _ ≤ 2 * n * m + ℱ.card := Nat.add_le_add hQ_counts.2 (Finset.card_filter_le _ _)
  let stepB : List PEqualNP.CircuitLowerBounds.Gate → ℕ → List PEqualNP.CircuitLowerBounds.Gate × ℕ := fun gs k =>
    PEqualNP.Outside.L_lib_1242_aux.foldOr N gs n (((ℱ.filter (fun S => S.card = k)).toList).map E)
  let Inv3 : List PEqualNP.CircuitLowerBounds.Gate → Prop := fun gs =>
    (∃ e, gs = gs3 ++ e) ∧
    PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack N ⟨gs, 0⟩
  have hstepB_ext : ∀ gs k, Inv3 gs →
      ∃ e, (stepB gs k).1 = gs ++ e ∧ Inv3 (stepB gs k).1 := by
    intro gs k ⟨⟨eg, heg⟩, hgf, hgr⟩
    obtain ⟨e1, he1, _⟩ := PEqualNP.Outside.L_lib_1242_aux.foldOr_ext N gs n _
    have hws : ∀ w ∈ ((ℱ.filter (fun S => S.card = k)).toList).map E, w < N + gs.length := by
      intro w hw
      simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter] at hw
      obtain ⟨S, ⟨hS, _⟩, rfl⟩ := hw
      have := hE_out S hS
      rw [heg]; simp only [List.length_append]; omega
    exact ⟨e1, he1, ⟨⟨eg ++ e1, by rw [he1, heg, List.append_assoc]⟩,
      PEqualNP.Outside.L_lib_1242_aux.foldOr_fanInTwo N gs n _ hgf,
      PEqualNP.Outside.L_lib_1242_aux.foldOr_readsBack N gs n _ hgr hws⟩⟩
  have hstepB_out : ∀ gs k, Inv3 gs → (stepB gs k).2 < N + (stepB gs k).1.length := by
    intro gs k ⟨⟨eg, heg⟩, _, _⟩
    apply PEqualNP.Outside.L_lib_1242_aux.foldOr_out_lt N gs n _ (by omega)
    intro w hw
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter] at hw
    obtain ⟨S, ⟨hS, _⟩, rfl⟩ := hw
    have := hE_out S hS
    rw [heg]; simp only [List.length_append]; omega
  let rB := PEqualNP.Outside.L_lib_1242_aux.buildMap stepB n gs3 (List.range (h + 1))
  let gs4 := rB.1
  let B := rB.2
  have hInv3_0 : Inv3 gs3 := ⟨⟨[], by simp⟩, hE_f, hE_r⟩
  have hB_inv := PEqualNP.Outside.L_lib_1242_aux.buildMap_ext stepB n Inv3 hstepB_ext gs3 (List.range (h + 1)) hInv3_0
  obtain ⟨e4, he4, hInv4⟩ := hB_inv
  have hB_counts : PEqualNP.NotBracket.notCount ⟨gs4, 0⟩ = 0 ∧
      PEqualNP.Outside.L_lib_1242_aux.nonNotCount gs4 ≤ 2 * n * m + 2 * ℱ.card := by
    have hc := PEqualNP.Outside.L_lib_1242_aux.buildMap_counts stepB n
      (fun k => (ℱ.filter (fun S => S.card = k)).card) Inv3
      (fun gs k hI => by obtain ⟨_, _, h⟩ := hstepB_ext gs k hI; exact h)
      (fun gs k _ => by
        have hfc := PEqualNP.Outside.L_lib_1242_aux.foldOr_counts N gs n (((ℱ.filter (fun S => S.card = k)).toList).map E)
        have hlen : (((ℱ.filter (fun S => S.card = k)).toList).map E).length =
            (ℱ.filter (fun S => S.card = k)).card := by
          simp
        exact ⟨hfc.1, hlen ▸ hfc.2⟩) gs3 (List.range (h + 1)) hInv3_0
    have hsum_part : ((List.range (h + 1)).map (fun k => (ℱ.filter (fun S => S.card = k)).card)).sum = ℱ.card := by
      rw [← List.sum_toFinset _ (List.nodup_range)]
      simp only [List.toFinset_range]
      symm
      exact Finset.card_eq_sum_card_fiberwise (fun S hS => Finset.mem_range.mpr (Nat.lt_succ_of_le (hℱ_card_le S hS)))
    refine ⟨?_, ?_⟩
    · rw [hc.1, hE_nc]
    · dsimp only [gs4]
      calc PEqualNP.Outside.L_lib_1242_aux.nonNotCount rB.1
          ≤ PEqualNP.Outside.L_lib_1242_aux.nonNotCount gs3 +
              ((List.range (h + 1)).map (fun k => (ℱ.filter (fun S => S.card = k)).card)).sum := hc.2
        _ ≤ (2 * n * m + ℱ.card) + ℱ.card := by rw [hsum_part]; exact Nat.add_le_add_right hE_nnc' _
        _ = 2 * n * m + 2 * ℱ.card := by ring
  have hB_out : ∀ k, B k < N + gs4.length :=
    PEqualNP.Outside.L_lib_1242_aux.buildMap_out_lt N stepB n Inv3 hstepB_ext hstepB_out gs3 (List.range (h + 1)) hInv3_0 (by dsimp only [N]; omega)
  have hB_eval : ∀ x k, k ≤ h →
      (PEqualNP.Outside.L_lib_1242_aux.wireVal gs4 (inp x) (B k) = true ↔
        ∃ S ∈ ℱ, S.card = k ∧ ∀ i ∈ S, a i ∪ c i ⊆ x) := by
    intro x k hk
    apply PEqualNP.Outside.L_lib_1242_aux.buildMap_eval N stepB n Inv3 (inp x) (hinp_len x)
      (fun k => ∃ S ∈ ℱ, S.card = k ∧ ∀ i ∈ S, a i ∪ c i ⊆ x) hstepB_ext hstepB_out
      (fun gs k ⟨⟨eg, heg⟩, _, _⟩ => by
        have hfalse : PEqualNP.Outside.L_lib_1242_aux.wireVal gs (inp x) n = false := by
          have hgs0 : gs = [] ++ gs := rfl
          rw [hgs0, PEqualNP.Outside.L_lib_1242_aux.wireVal_append_of_lt [] _ _ _ (by rw [hinp_len]; omega)]
          exact hinp_false x
        have hws : ∀ w ∈ ((ℱ.filter (fun S => S.card = k)).toList).map E, w < N + gs.length := by
          intro w hw
          simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter] at hw
          obtain ⟨S, ⟨hS, _⟩, rfl⟩ := hw
          have := hE_out S hS
          rw [heg]; simp only [List.length_append]; omega
        dsimp only [stepB]
        rw [PEqualNP.Outside.L_lib_1242_aux.foldOr_eval N gs n _ (inp x) (hinp_len x) hfalse hws]
        constructor
        · rintro ⟨w, hw, hwt⟩
          simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter] at hw
          obtain ⟨S, ⟨hS, hSc⟩, rfl⟩ := hw
          rw [heg, PEqualNP.Outside.L_lib_1242_aux.wireVal_append_of_lt _ _ _ _ (by rw [hinp_len]; exact hE_out S hS),
            hE_eval x S hS] at hwt
          exact ⟨S, hS, hSc, hwt⟩
        · rintro ⟨S, hS, hSc, hsub⟩
          refine ⟨E S, List.mem_map.mpr ⟨S, Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨hS, hSc⟩), rfl⟩, ?_⟩
          rw [heg, PEqualNP.Outside.L_lib_1242_aux.wireVal_append_of_lt _ _ _ _ (by rw [hinp_len]; exact hE_out S hS),
            hE_eval x S hS]
          exact hsub)
      gs3 (List.range (h + 1)) List.nodup_range hInv3_0 k (List.mem_range.mpr (by omega))
  let goodKs : Finset (Fin n) → Finset ℕ := fun x =>
    (Finset.range (h + 1)).filter (fun k => PEqualNP.Outside.L_lib_1242_aux.wireVal gs4 (inp x) (B k) = true)
  have hgood0 : ∀ x, 0 ∈ goodKs x := by
    intro x
    simp only [goodKs, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, (hB_eval x 0 (by omega)).mpr ⟨∅, hℱ_empty, Finset.card_empty, fun i hi => by simp at hi⟩⟩
  let M : Finset (Fin n) → ℕ := fun x => (goodKs x).max' ⟨0, hgood0 x⟩
  have hM_le : ∀ x, M x ≤ h := by
    intro x
    have hmem : M x ∈ goodKs x := Finset.max'_mem (goodKs x) ⟨0, hgood0 x⟩
    simp only [goodKs, Finset.mem_filter, Finset.mem_range] at hmem
    omega
  have hB_monotone : ∀ x k, k ≤ h →
      (PEqualNP.Outside.L_lib_1242_aux.wireVal gs4 (inp x) (B k) = true ↔ k ≤ M x) := by
    intro x k hk
    constructor
    · intro hval
      apply Finset.le_max'
      simp only [goodKs, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hval⟩
    · intro hle
      have hMmem : M x ∈ goodKs x := Finset.max'_mem (goodKs x) ⟨0, hgood0 x⟩
      simp only [goodKs, Finset.mem_filter, Finset.mem_range] at hMmem
      obtain ⟨S, hS, hSc, hsub⟩ := (hB_eval x (M x) (hM_le x)).mp hMmem.2
      have hdown : ∀ d : ℕ, d ≤ M x → ∃ S' ∈ ℱ, S'.card = M x - d ∧ ∀ i ∈ S', a i ∪ c i ⊆ x := by
        intro d hd
        induction d with
        | zero => exact ⟨S, hS, by omega, hsub⟩
        | succ d ihd =>
            obtain ⟨S', hS', hS'c, hsub'⟩ := ihd (by omega)
            have hne' : S'.Nonempty := Finset.card_pos.mp (by omega)
            obtain ⟨j, hjS, hjℱ⟩ := hℱ_pred S' hS' hne'
            refine ⟨S'.erase j, hjℱ, ?_, fun i hi => hsub' i (Finset.mem_erase.mp hi).2⟩
            rw [Finset.card_erase_of_mem hjS, hS'c]
            omega
      obtain ⟨S', hS', hS'c, hsub'⟩ := hdown (M x - k) (Nat.sub_le _ _)
      rw [Nat.sub_sub_self hle] at hS'c
      exact (hB_eval x k hk).mpr ⟨S', hS', hS'c, hsub'⟩
  let rT := PEqualNP.Outside.L_lib_1242_aux.buildTrie N n h B r gs4 [(0, n + 1)]
  let gs5 := rT.1
  let nodes := rT.2
  let eqW : ℕ → ℕ := fun k => ((nodes.find? (fun p => p.1 == k)).map Prod.snd).getD n
  have hT_inv := PEqualNP.Outside.L_lib_1242_aux.buildTrie_inv N n h B r gs4 [(0, n + 1)]
    hInv4.2.1 hInv4.2.2 (by dsimp only [N]; omega) (fun k _ => hB_out k)
    (by intro p hp; simp only [List.mem_singleton] at hp; subst hp; simp only [N]; exact ⟨Nat.zero_le _, Nat.dvd_zero _, by omega⟩)
    (by simp) (by
      intro L hL hdvd
      have hL0 : L = 0 := by
        by_contra hne
        obtain ⟨q, hq⟩ := hdvd
        have hq0 : 1 ≤ q := by
          cases q with
          | zero => simp at hq; exact False.elim (hne hq)
          | succ _ => omega
        have : 2 ^ r ≤ L := by
          calc 2 ^ r = 2 ^ r * 1 := (Nat.mul_one _).symm
            _ ≤ 2 ^ r * q := Nat.mul_le_mul_left _ hq0
            _ = L := hq.symm
        omega
      subst hL0
      exact ⟨(0, n + 1), by simp, rfl⟩)
  obtain ⟨⟨e5, he5⟩, hT_f, hT_r, hT_nc, hT_nnc, hT_nodes, hT_nodup, hT_comp⟩ := hT_inv
  have hT_nc' : PEqualNP.NotBracket.notCount ⟨gs5, 0⟩ ≤ r := by
    exact Nat.le_trans hT_nc (by rw [hB_counts.1]; simp)
  have hT_nnc' : PEqualNP.Outside.L_lib_1242_aux.nonNotCount gs5 ≤ 2 * n * m + 2 * ℱ.card + 4 * h := by
    have hrem := PEqualNP.Outside.L_lib_1242_aux.remSet_card_le r h
    dsimp only [gs5]
    calc PEqualNP.Outside.L_lib_1242_aux.nonNotCount rT.1
        ≤ PEqualNP.Outside.L_lib_1242_aux.nonNotCount gs4 + 4 * (PEqualNP.Outside.L_lib_1242_aux.remSet r h).card := hT_nnc
      _ ≤ (2 * n * m + 2 * ℱ.card) + 4 * h := Nat.add_le_add hB_counts.2 (Nat.mul_le_mul_left 4 hrem)
      _ = 2 * n * m + 2 * ℱ.card + 4 * h := by ring
  have heq_out : ∀ k ≤ h, eqW k < N + gs5.length := by
    intro k hk
    obtain ⟨p, hp, hp1⟩ := hT_comp k hk
    have hfind : ∃ q ∈ nodes, nodes.find? (fun p => p.1 == k) = some q ∧ q.1 = k := by
      have hsome : (nodes.find? (fun p => p.1 == k)).isSome :=
        List.find?_isSome.mpr ⟨p, hp, by simp [hp1]⟩
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hsome
      exact ⟨q, List.mem_of_find?_eq_some hq, hq, by simpa using List.find?_some hq⟩
    obtain ⟨q, hq_mem, hq_find, _⟩ := hfind
    dsimp only [eqW]
    rw [hq_find]
    exact (hT_nodes q hq_mem).2
  have heq_eval : ∀ x k, k ≤ h →
      (PEqualNP.Outside.L_lib_1242_aux.wireVal gs5 (inp x) (eqW k) = true ↔ k = M x) := by
    intro x k hk
    have hnF_val : PEqualNP.Outside.L_lib_1242_aux.wireVal gs4 (inp x) n = false := by
      have hgs4_eq : gs4 = [] ++ gs4 := rfl
      rw [hgs4_eq, PEqualNP.Outside.L_lib_1242_aux.wireVal_append_of_lt [] _ _ _ (by rw [hinp_len]; omega)]
      exact hinp_false x
    have hev_trie := PEqualNP.Outside.L_lib_1242_aux.buildTrie_eval N n h B r gs4 [(0, n + 1)]
      (inp x) (hinp_len x) (M x) (hM_le x) (by dsimp only [N]; omega) hnF_val (fun k _ => hB_out k) (hB_monotone x)
      (by intro p hp; simp only [List.mem_singleton] at hp; subst hp; simp only [N]; exact ⟨Nat.zero_le _, Nat.dvd_zero _, by omega⟩)
      (by
        intro L hL hdvd
        have hL0 : L = 0 := by
          by_contra hne
          obtain ⟨q, hq⟩ := hdvd
          have hq0 : 1 ≤ q := by
            cases q with
            | zero => simp at hq; exact False.elim (hne hq)
            | succ _ => omega
          have : 2 ^ r ≤ L := by
            calc 2 ^ r = 2 ^ r * 1 := (Nat.mul_one _).symm
              _ ≤ 2 ^ r * q := Nat.mul_le_mul_left _ hq0
              _ = L := hq.symm
          omega
        subst hL0
        exact ⟨(0, n + 1), by simp, rfl⟩)
      (by
        intro p hp
        simp only [List.mem_singleton] at hp
        subst hp
        have hgs4_eq : gs4 = [] ++ gs4 := rfl
        rw [hgs4_eq, PEqualNP.Outside.L_lib_1242_aux.wireVal_append_of_lt [] _ _ _ (by rw [hinp_len]; omega), hinp_true]
        constructor
        · intro _; exact ⟨Nat.zero_le _, by have := hM_le x; omega⟩
        · intro _; rfl)
    obtain ⟨p, hp, hp1⟩ := hT_comp k hk
    have hfind : ∃ q ∈ nodes, nodes.find? (fun p => p.1 == k) = some q ∧ q.1 = k := by
      have hsome : (nodes.find? (fun p => p.1 == k)).isSome :=
        List.find?_isSome.mpr ⟨p, hp, by simp [hp1]⟩
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hsome
      exact ⟨q, List.mem_of_find?_eq_some hq, hq, by simpa using List.find?_some hq⟩
    obtain ⟨q, hq_mem, hq_find, hq1⟩ := hfind
    dsimp only [eqW]
    rw [hq_find]
    simpa [hq1] using hev_trie q hq_mem
  let stepSel : List PEqualNP.CircuitLowerBounds.Gate → Finset (Fin m) → List PEqualNP.CircuitLowerBounds.Gate × ℕ :=
    fun gs S => PEqualNP.Outside.L_lib_1242_aux.addAnd N gs (E S) (eqW S.card)
  let Inv5 : List PEqualNP.CircuitLowerBounds.Gate → Prop := fun gs =>
    (∃ e, gs = gs5 ++ e) ∧
    PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack N ⟨gs, 0⟩
  have hE_out5 : ∀ S ∈ ℱ, E S < N + gs5.length := by
    intro S hS
    have h1 := hE_out S hS
    dsimp only [gs5]
    rw [he5]
    dsimp only [gs4]
    rw [he4]
    simp only [List.length_append]
    omega
  have hstepSel_ext : ∀ gs S, S ∈ ℱ → Inv5 gs →
      ∃ e, (stepSel gs S).1 = gs ++ e ∧ Inv5 (stepSel gs S).1 := by
    intro gs S hS ⟨⟨eg, heg⟩, hgf, hgr⟩
    have h1 : E S < N + gs.length := by
      have := hE_out5 S hS; rw [heg]; simp only [List.length_append]; omega
    have h2 : eqW S.card < N + gs.length := by
      have := heq_out S.card (hℱ_card_le S hS); rw [heg]; simp only [List.length_append]; omega
    have hwf := PEqualNP.Outside.L_lib_1242_aux.addAnd_wf N gs (E S) (eqW S.card) hgf hgr h1 h2
    exact ⟨_, (PEqualNP.Outside.L_lib_1242_aux.addAnd_props N gs _ _).1,
      ⟨⟨eg ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [E S, eqW S.card]⟩],
        by rw [(PEqualNP.Outside.L_lib_1242_aux.addAnd_props N gs _ _).1, heg, List.append_assoc]⟩, hwf.1, hwf.2⟩⟩
  let stepSelSafe : List PEqualNP.CircuitLowerBounds.Gate → Finset (Fin m) → List PEqualNP.CircuitLowerBounds.Gate × ℕ :=
    fun gs S => if S ∈ ℱ then PEqualNP.Outside.L_lib_1242_aux.addAnd N gs (E S) (eqW S.card) else (gs, n)
  have hstepSel_ext' : ∀ gs S, Inv5 gs →
      ∃ e, (stepSelSafe gs S).1 = gs ++ e ∧ Inv5 (stepSelSafe gs S).1 := by
    intro gs S hI
    dsimp only [stepSelSafe]
    split_ifs with hS
    · exact hstepSel_ext gs S hS hI
    · exact ⟨[], by simp, hI⟩
  have hstepSel_out' : ∀ gs S, Inv5 gs →
      (stepSelSafe gs S).2 < N + (stepSelSafe gs S).1.length := by
    intro gs S ⟨⟨eg, heg⟩, _, _⟩
    dsimp only [stepSelSafe]
    split_ifs with hS
    · exact (PEqualNP.Outside.L_lib_1242_aux.addAnd_props N gs _ _).2.2.1
    · dsimp only [N]; omega
  let rSel := PEqualNP.Outside.L_lib_1242_aux.buildMap stepSelSafe n gs5 ℱ.toList
  let gs6 := rSel.1
  let sel := rSel.2
  have hInv5_0 : Inv5 gs5 := ⟨⟨[], by simp⟩, hT_f, hT_r⟩
  have hSel_inv := PEqualNP.Outside.L_lib_1242_aux.buildMap_ext stepSelSafe n Inv5 hstepSel_ext' gs5 ℱ.toList hInv5_0
  obtain ⟨e6, he6, hInv6⟩ := hSel_inv
  have hSel_counts : PEqualNP.NotBracket.notCount ⟨gs6, 0⟩ ≤ r ∧
      PEqualNP.Outside.L_lib_1242_aux.nonNotCount gs6 ≤ 2 * n * m + 3 * ℱ.card + 4 * h := by
    have hc := PEqualNP.Outside.L_lib_1242_aux.buildMap_counts stepSelSafe n (fun _ => 1) Inv5
      (fun gs S hI => by obtain ⟨_, _, h⟩ := hstepSel_ext' gs S hI; exact h)
      (fun gs S _ => by
        dsimp only [stepSelSafe]
        split_ifs
        · have hp := PEqualNP.Outside.L_lib_1242_aux.addAnd_props N gs (E S) (eqW S.card)
          exact ⟨hp.2.2.2.1, by rw [hp.2.2.2.2]⟩
        · exact ⟨rfl, Nat.le_add_right _ _⟩) gs5 ℱ.toList hInv5_0
    have hsum : (ℱ.toList.map (fun _ : Finset (Fin m) => 1)).sum = ℱ.card := by
      simp [List.sum_replicate, Finset.length_toList]
    refine ⟨?_, ?_⟩
    · rw [hc.1]; exact hT_nc'
    · dsimp only [gs6]
      calc PEqualNP.Outside.L_lib_1242_aux.nonNotCount rSel.1
          ≤ PEqualNP.Outside.L_lib_1242_aux.nonNotCount gs5 + (ℱ.toList.map (fun _ : Finset (Fin m) => 1)).sum := hc.2
        _ ≤ (2 * n * m + 2 * ℱ.card + 4 * h) + ℱ.card := by rw [hsum]; exact Nat.add_le_add_right hT_nnc' _
        _ = 2 * n * m + 3 * ℱ.card + 4 * h := by ring
  have hSel_out : ∀ S, sel S < N + gs6.length :=
    PEqualNP.Outside.L_lib_1242_aux.buildMap_out_lt N stepSelSafe n Inv5 hstepSel_ext' hstepSel_out' gs5 ℱ.toList hInv5_0 (by dsimp only [N]; omega)
  have hSel_eval : ∀ x S, S ∈ ℱ →
      (PEqualNP.Outside.L_lib_1242_aux.wireVal gs6 (inp x) (sel S) = true ↔
        (∀ i ∈ S, a i ∪ c i ⊆ x) ∧ S.card = M x) := by
    intro x S hS
    apply PEqualNP.Outside.L_lib_1242_aux.buildMap_eval_mem N stepSelSafe n Inv5 (inp x) (hinp_len x)
      (fun S => (∀ i ∈ S, a i ∪ c i ⊆ x) ∧ S.card = M x) hstepSel_ext' hstepSel_out'
      gs5 ℱ.toList (Finset.nodup_toList _) hInv5_0
      (fun gs S' hS'mem ⟨⟨eg, heg⟩, _, _⟩ => by
        have hS' : S' ∈ ℱ := Finset.mem_toList.mp hS'mem
        dsimp only [stepSelSafe]
        rw [if_pos hS', PEqualNP.Outside.L_lib_1242_aux.addAnd_eval N gs _ _ (inp x) (hinp_len x)]
        have hgs5_eq : gs5 = gs3 ++ (e4 ++ e5) := by
          dsimp only [gs5]; rw [he5]; dsimp only [gs4]; rw [he4, List.append_assoc]
        have hgs_e : gs = gs3 ++ (e4 ++ e5 ++ eg) := by
          rw [heg, hgs5_eq, List.append_assoc]
        have hW1 : PEqualNP.Outside.L_lib_1242_aux.wireVal gs (inp x) (E S') =
            PEqualNP.Outside.L_lib_1242_aux.wireVal gs3 (inp x) (E S') := by
          rw [hgs_e, PEqualNP.Outside.L_lib_1242_aux.wireVal_append_of_lt _ _ _ _ (by rw [hinp_len]; exact hE_out S' hS')]
        have hW2 : PEqualNP.Outside.L_lib_1242_aux.wireVal gs (inp x) (eqW S'.card) =
            PEqualNP.Outside.L_lib_1242_aux.wireVal gs5 (inp x) (eqW S'.card) := by
          rw [heg, PEqualNP.Outside.L_lib_1242_aux.wireVal_append_of_lt _ _ _ _
            (by rw [hinp_len]; exact heq_out S'.card (hℱ_card_le S' hS'))]
        rw [hW1, hW2, hE_eval x S' hS', heq_eval x S'.card (hℱ_card_le S' hS')])
      S (Finset.mem_toList.mpr hS)
  let stepTap : List PEqualNP.CircuitLowerBounds.Gate → Fin m → List PEqualNP.CircuitLowerBounds.Gate × ℕ := fun gs j =>
    if a j ⊆ b j then
      let r1 := PEqualNP.Outside.L_lib_1242_aux.foldOr N gs n
        (((ℱ.filter (fun S => ∀ i ∈ S, a i ∪ c i ⊆ b j)).toList).map sel)
      PEqualNP.Outside.L_lib_1242_aux.addAnd N r1.1 (P j) r1.2
    else (gs, n)
  let Inv6 : List PEqualNP.CircuitLowerBounds.Gate → Prop := fun gs =>
    (∃ e, gs = gs6 ++ e) ∧
    PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack N ⟨gs, 0⟩
  have hP_out6 : ∀ j, P j < N + gs6.length := by
    intro j
    have := hP_out2 j
    dsimp only [gs6]
    rw [he6]
    dsimp only [gs5]
    rw [he5]
    dsimp only [gs4]
    rw [he4]
    dsimp only [gs3]
    rw [he3]
    simp only [List.length_append]
    omega
  have hstepTap_ext : ∀ gs j, Inv6 gs →
      ∃ e, (stepTap gs j).1 = gs ++ e ∧ Inv6 (stepTap gs j).1 := by
    intro gs j ⟨⟨eg, heg⟩, hgf, hgr⟩
    dsimp only [stepTap]
    split_ifs
    · let ws := ((ℱ.filter (fun S => ∀ i ∈ S, a i ∪ c i ⊆ b j)).toList).map sel
      have hws : ∀ w ∈ ws, w < N + gs.length := by
        intro w hw
        simp only [ws, List.mem_map, Finset.mem_toList] at hw
        obtain ⟨S, _, rfl⟩ := hw
        have := hSel_out S; rw [heg]; simp only [List.length_append]; omega
      obtain ⟨e1, he1, _⟩ := PEqualNP.Outside.L_lib_1242_aux.foldOr_ext N gs n ws
      have hf1 := PEqualNP.Outside.L_lib_1242_aux.foldOr_fanInTwo N gs n ws hgf
      have hr1 := PEqualNP.Outside.L_lib_1242_aux.foldOr_readsBack N gs n ws hgr hws
      have hout1 := PEqualNP.Outside.L_lib_1242_aux.foldOr_out_lt N gs n ws (by omega) hws
      have hPj_lt : P j < N + (PEqualNP.Outside.L_lib_1242_aux.foldOr N gs n ws).1.length := by
        have := hP_out6 j; rw [he1, heg]; simp only [List.length_append]; omega
      have hwf2 := PEqualNP.Outside.L_lib_1242_aux.addAnd_wf N _ (P j) _ hf1 hr1 hPj_lt hout1
      exact ⟨e1 ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [P j, (PEqualNP.Outside.L_lib_1242_aux.foldOr N gs n ws).2]⟩],
        by rw [(PEqualNP.Outside.L_lib_1242_aux.addAnd_props N _ _ _).1, he1, List.append_assoc],
        ⟨⟨eg ++ (e1 ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [P j, (PEqualNP.Outside.L_lib_1242_aux.foldOr N gs n ws).2]⟩]),
          by rw [(PEqualNP.Outside.L_lib_1242_aux.addAnd_props N _ _ _).1, he1, heg, List.append_assoc, List.append_assoc]⟩,
          hwf2.1, hwf2.2⟩⟩
    · exact ⟨[], by simp, ⟨⟨eg, heg⟩, hgf, hgr⟩⟩
  have hstepTap_out : ∀ gs j, Inv6 gs → (stepTap gs j).2 < N + (stepTap gs j).1.length := by
    intro gs j _
    dsimp only [stepTap]
    split_ifs
    · exact (PEqualNP.Outside.L_lib_1242_aux.addAnd_props N _ _ _).2.2.1
    · dsimp only [N]; omega
  let rTap := PEqualNP.Outside.L_lib_1242_aux.buildMap stepTap n gs6 (List.finRange m)
  let gs7 := rTap.1
  let tapRaw := rTap.2
  have hInv6_0 : Inv6 gs6 := ⟨⟨[], by simp⟩, hInv6.2.1, hInv6.2.2⟩
  have hTap_inv := PEqualNP.Outside.L_lib_1242_aux.buildMap_ext stepTap n Inv6 hstepTap_ext gs6 (List.finRange m) hInv6_0
  obtain ⟨e7, he7, hInv7⟩ := hTap_inv
  have hTap_counts : PEqualNP.NotBracket.notCount ⟨gs7, 0⟩ ≤ r ∧
      PEqualNP.Outside.L_lib_1242_aux.nonNotCount gs7 ≤ 2 * n * m + m + (m + 3) * ℱ.card + 4 * h := by
    have hc := PEqualNP.Outside.L_lib_1242_aux.buildMap_counts stepTap n (fun _ => ℱ.card + 1) Inv6
      (fun gs j hI => by obtain ⟨_, _, h⟩ := hstepTap_ext gs j hI; exact h)
      (fun gs j _ => by
        dsimp only [stepTap]
        split_ifs
        · let ws := ((ℱ.filter (fun S => ∀ i ∈ S, a i ∪ c i ⊆ b j)).toList).map sel
          have hfc := PEqualNP.Outside.L_lib_1242_aux.foldOr_counts N gs n ws
          have hap := PEqualNP.Outside.L_lib_1242_aux.addAnd_props N (PEqualNP.Outside.L_lib_1242_aux.foldOr N gs n ws).1
            (P j) (PEqualNP.Outside.L_lib_1242_aux.foldOr N gs n ws).2
          have hws_len : ws.length ≤ ℱ.card := by
            simp only [ws, List.length_map, Finset.length_toList]
            exact Finset.card_filter_le _ _
          exact ⟨by rw [hap.2.2.2.1, hfc.1], by rw [hap.2.2.2.2]; omega⟩
        · exact ⟨rfl, Nat.le_add_right _ _⟩) gs6 (List.finRange m) hInv6_0
    have hsum : ((List.finRange m).map (fun _ : Fin m => ℱ.card + 1)).sum = m * (ℱ.card + 1) := by
      simp [List.sum_replicate, List.length_finRange]
    refine ⟨?_, ?_⟩
    · rw [hc.1]; exact hSel_counts.1
    · have hmul : m * (ℱ.card + 1) = m * ℱ.card + m := by ring
      dsimp only [gs7]
      calc PEqualNP.Outside.L_lib_1242_aux.nonNotCount rTap.1
          ≤ PEqualNP.Outside.L_lib_1242_aux.nonNotCount gs6 + ((List.finRange m).map (fun _ : Fin m => ℱ.card + 1)).sum := hc.2
        _ ≤ (2 * n * m + 3 * ℱ.card + 4 * h) + (m * ℱ.card + m) := by
            rw [hsum, hmul]; exact Nat.add_le_add_right hSel_counts.2 _
        _ = 2 * n * m + m + (m + 3) * ℱ.card + 4 * h := by ring
  have hTap_out : ∀ j, tapRaw j < N + gs7.length :=
    PEqualNP.Outside.L_lib_1242_aux.buildMap_out_lt N stepTap n Inv6 hstepTap_ext hstepTap_out gs6 (List.finRange m) hInv6_0 (by dsimp only [N]; omega)
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gs7, 0⟩
  let tap : Fin m → Fin (n + 2 + C.size) := fun j => ⟨tapRaw j, hTap_out j⟩
  refine ⟨C, tap, hInv7.2.1, hInv7.2.2, ?_, hTap_counts.1, ?_, ?_⟩
  · simp [C]
  · dsimp only [C]
    rw [PEqualNP.Outside.L_lib_1242_aux.size_sub_notCount gs7 0, hF_eq]
    exact Nat.le_trans hTap_counts.2 (by omega)
  · intro x j
    have hev := PEqualNP.Outside.L_lib_1242_aux.buildMap_eval N stepTap n Inv6 (inp x) (hinp_len x)
      (fun j => a j ⊆ b j ∧ a j ⊆ x ∧
        ∃ S ∈ ℱ, (∀ i ∈ S, a i ∪ c i ⊆ b j) ∧ (∀ i ∈ S, a i ∪ c i ⊆ x) ∧ S.card = M x)
      hstepTap_ext hstepTap_out
      (fun gs j ⟨⟨eg, heg⟩, _, _⟩ => by
        dsimp only [stepTap]
        split_ifs with hab
        · let ws := ((ℱ.filter (fun S => ∀ i ∈ S, a i ∪ c i ⊆ b j)).toList).map sel
          have hfalse : PEqualNP.Outside.L_lib_1242_aux.wireVal (PEqualNP.Outside.L_lib_1242_aux.foldOr N gs n ws).1 (inp x) n = false := by
            obtain ⟨e', he', _⟩ := PEqualNP.Outside.L_lib_1242_aux.foldOr_ext N gs n ws
            have hgs0 : (PEqualNP.Outside.L_lib_1242_aux.foldOr N gs n ws).1 = [] ++ (gs ++ e') := by
              rw [he']; simp
            rw [hgs0, PEqualNP.Outside.L_lib_1242_aux.wireVal_append_of_lt [] _ _ _ (by rw [hinp_len]; omega)]
            exact hinp_false x
          have hfalse0 : PEqualNP.Outside.L_lib_1242_aux.wireVal gs (inp x) n = false := by
            have hgs0 : gs = [] ++ gs := rfl
            rw [hgs0, PEqualNP.Outside.L_lib_1242_aux.wireVal_append_of_lt [] _ _ _ (by rw [hinp_len]; omega)]
            exact hinp_false x
          have hws : ∀ w ∈ ws, w < N + gs.length := by
            intro w hw
            simp only [ws, List.mem_map, Finset.mem_toList] at hw
            obtain ⟨S, _, rfl⟩ := hw
            have := hSel_out S; rw [heg]; simp only [List.length_append]; omega
          rw [PEqualNP.Outside.L_lib_1242_aux.addAnd_eval N _ (P j) _ (inp x) (hinp_len x)]
          obtain ⟨e1, he1, _⟩ := PEqualNP.Outside.L_lib_1242_aux.foldOr_ext N gs n ws
          have hgs6_eq : gs6 = gs2 ++ (e3 ++ e4 ++ e5 ++ e6) := by
            dsimp only [gs6]; rw [he6]; dsimp only [gs5]; rw [he5]; dsimp only [gs4]; rw [he4]; dsimp only [gs3]; rw [he3]
            simp [List.append_assoc]
          have hgs_p : (PEqualNP.Outside.L_lib_1242_aux.foldOr N gs n ws).1 = gs2 ++ (e3 ++ e4 ++ e5 ++ e6 ++ eg ++ e1) := by
            rw [he1, heg, hgs6_eq]; simp [List.append_assoc]
          have hWP : PEqualNP.Outside.L_lib_1242_aux.wireVal (PEqualNP.Outside.L_lib_1242_aux.foldOr N gs n ws).1 (inp x) (P j) =
              PEqualNP.Outside.L_lib_1242_aux.wireVal gs2 (inp x) (P j) := by
            rw [hgs_p, PEqualNP.Outside.L_lib_1242_aux.wireVal_append_of_lt _ _ _ _ (by rw [hinp_len]; exact hP_out2 j)]
          rw [hWP, hP_eval2 x j, PEqualNP.Outside.L_lib_1242_aux.foldOr_eval N gs n ws (inp x) (hinp_len x) hfalse0 hws]
          constructor
          · rintro ⟨hpj, ⟨w, hw, hwt⟩⟩
            simp only [ws, List.mem_map, Finset.mem_toList, Finset.mem_filter] at hw
            obtain ⟨S, ⟨hS, hSb⟩, rfl⟩ := hw
            rw [heg, PEqualNP.Outside.L_lib_1242_aux.wireVal_append_of_lt _ _ _ _ (by rw [hinp_len]; exact hSel_out S),
              hSel_eval x S hS] at hwt
            exact ⟨hab, hpj, S, hS, hSb, hwt.1, hwt.2⟩
          · rintro ⟨_, hpj, S, hS, hSb, hSx, hSc⟩
            refine ⟨hpj, sel S, List.mem_map.mpr ⟨S, Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨hS, hSb⟩), rfl⟩, ?_⟩
            rw [heg, PEqualNP.Outside.L_lib_1242_aux.wireVal_append_of_lt _ _ _ _ (by rw [hinp_len]; exact hSel_out S),
              hSel_eval x S hS]
            exact ⟨hSx, hSc⟩
        · have hgs_f : gs = [] ++ gs := rfl
          rw [hgs_f, PEqualNP.Outside.L_lib_1242_aux.wireVal_append_of_lt [] _ _ _ (by rw [hinp_len]; omega), hinp_false]
          simp [hab])
      gs6 (List.finRange m) (List.nodup_finRange m) hInv6_0 j (List.mem_finRange j)
    have hwire_eq : ∀ {l : List Bool} {k : ℕ}, l = inp x → k = tapRaw j →
        (C.wires l).getD k false = PEqualNP.Outside.L_lib_1242_aux.wireVal gs7 (inp x) (tapRaw j) := by
      intro l k hl hk; subst hl; subst hk; rfl
    dsimp only
    rw [hwire_eq (by dsimp only [inp]; congr 1; congr 1; funext i; congr 1) rfl]
    constructor
    · intro ⟨hax, hxb⟩
      rw [hev]
      refine ⟨hax.trans hxb, hax, ?_⟩
      have hMmem : M x ∈ goodKs x := Finset.max'_mem (goodKs x) ⟨0, hgood0 x⟩
      simp only [goodKs, Finset.mem_filter, Finset.mem_range] at hMmem
      obtain ⟨S, hS, hSc, hSx⟩ := (hB_eval x (M x) (hM_le x)).mp hMmem.2
      exact ⟨S, hS, fun i hi => (hSx i hi).trans hxb, hSx, hSc⟩
    · intro ⟨hcx, hxd⟩
      by_contra hne
      have htrue : PEqualNP.Outside.L_lib_1242_aux.wireVal gs7 (inp x) (tapRaw j) = true := by
        cases hval : PEqualNP.Outside.L_lib_1242_aux.wireVal gs7 (inp x) (tapRaw j)
        · exact False.elim (hne hval)
        · rfl
      rw [hev] at htrue
      obtain ⟨hab, hax, S, hS, hSb, hSx, hSc⟩ := htrue
      have hj_not : j ∉ S := by
        intro hjS
        have hjb : a j ∪ c j ⊆ b j := hSb j hjS
        let U := a j ∪ c j
        have hUd : U ⊆ d j := Finset.union_subset (hax.trans hxd) (hcx.trans hxd)
        have hnm := PEqualNP.Outside.L_lib_1242_aux.namedAt_replicate a b c d j U
          Finset.subset_union_left hjb Finset.subset_union_right hUd (h + 1)
        exact hlen_at (List.replicate (h + 1) j) (List.length_replicate) hnm
      have hS_copy := hS
      simp only [ℱ, Finset.mem_filter, Finset.mem_univ, true_and] at hS_copy
      obtain ⟨js, hnd, hts, hnm⟩ := hS_copy
      let W := S.biUnion (fun i => a i ∪ c i)
      have hWx : W ⊆ x := Finset.biUnion_subset.mpr (fun i hi => hSx i hi)
      have hWb : W ⊆ b j := Finset.biUnion_subset.mpr (fun i hi => hSb i hi)
      have hnmW : PEqualNP.Outside.L_lib_1242_aux.namedAt a b c d js W := by
        have h1 := PEqualNP.Outside.L_lib_1242_aux.namedAt_restrict a b c d W js Finset.univ hnm
          (fun i hi => Finset.subset_biUnion_of_mem (fun i => a i ∪ c i) (hts ▸ List.mem_toFinset.mpr hi))
        simpa using h1
      have hnm_ext : PEqualNP.Outside.L_lib_1242_aux.namedAt a b c d (j :: js) Finset.univ := by
        refine ⟨W ∪ a j, x, PEqualNP.Outside.L_lib_1242_aux.namedAt_mono a b c d Finset.subset_union_left hnmW,
          Finset.union_subset hWx hax, Finset.subset_univ x, Finset.subset_union_right,
          Finset.union_subset hWb hab, hcx, hxd⟩
      have hins_mem : insert j S ∈ ℱ := by
        simp only [ℱ, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨j :: js, List.nodup_cons.mpr ⟨fun hj => hj_not (hts ▸ List.mem_toFinset.mpr hj), hnd⟩,
          by simp [hts], hnm_ext⟩
      have hins_card : (insert j S).card = M x + 1 := by
        rw [Finset.card_insert_of_notMem hj_not, hSc]
      have hins_le : M x + 1 ≤ h := by
        rw [← hins_card]
        exact hℱ_card_le (insert j S) hins_mem
      have hins_B : PEqualNP.Outside.L_lib_1242_aux.wireVal gs4 (inp x) (B (M x + 1)) = true := by
        rw [hB_eval x (M x + 1) hins_le]
        refine ⟨insert j S, hins_mem, hins_card, ?_⟩
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hiS
        · exact Finset.union_subset hax hcx
        · exact hSx i hiS
      have hcontra := (hB_monotone x (M x + 1) hins_le).mp hins_B
      omega


