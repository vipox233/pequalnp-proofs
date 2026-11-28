import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_50274

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (a : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) a

theorem run_nil (a : List Bool) : run [] a = a := rfl

theorem run_cons (g : Gate) (gs : List Gate) (a : List Bool) :
    run (g :: gs) a = run gs (a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]) := rfl

theorem run_append (g1 g2 : List Gate) (a : List Bool) :
    run (g1 ++ g2) a = run g2 (run g1 a) := by
  unfold run; rw [List.foldl_append]

theorem run_single (g : Gate) (a : List Bool) :
    run [g] a = a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)] := rfl

theorem length_run : ∀ (gs : List Gate) (a : List Bool), (run gs a).length = a.length + gs.length
  | [], a => by simp [run_nil]
  | g :: gs, a => by rw [run_cons, length_run gs]; simp; omega

theorem prefix_run : ∀ (gs : List Gate) (a : List Bool), a <+: run gs a
  | [], a => by simp [run_nil]
  | g :: gs, a => by
      rw [run_cons]
      exact (List.prefix_append a _).trans (prefix_run gs _)

theorem getD_prefix {a b : List Bool} (h : a <+: b) {i : ℕ} (hi : i < a.length) :
    b.getD i false = a.getD i false := by
  obtain ⟨t, rfl⟩ := h
  exact List.getD_append _ _ _ _ hi

theorem getD_ofFn {n : ℕ} (g : Fin n → Bool) (w : ℕ) :
    (List.ofFn g).getD w false = if h : w < n then g ⟨w, h⟩ else false := by
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]; simp
  · rw [List.getD_eq_default _ _ (by simp; omega)]

inductive Ex where
  | var : ℕ → Ex
  | neg : Ex → Ex
  | conj : Ex → Ex → Ex
  | disj : Ex → Ex → Ex
  | tt : Ex
  | ff : Ex

def Ex.ev : Ex → List Bool → Bool
  | .var i, a => a.getD i false
  | .neg e, a => !(e.ev a)
  | .conj e1 e2, a => e1.ev a && e2.ev a
  | .disj e1 e2, a => e1.ev a || e2.ev a
  | .tt, _ => true
  | .ff, _ => false

def Ex.ok (n : ℕ) : Ex → Prop
  | .var i => i < n
  | .neg e => e.ok n
  | .conj e1 e2 => e1.ok n ∧ e2.ok n
  | .disj e1 e2 => e1.ok n ∧ e2.ok n
  | .tt => True
  | .ff => True

def comp : ℕ → Ex → List Gate × ℕ
  | _, .var i => ([], i)
  | c, .neg e => ((comp c e).1 ++ [⟨GateOp.not, [(comp c e).2]⟩], c + (comp c e).1.length)
  | c, .conj e1 e2 =>
      ((comp c e1).1 ++ (comp (c + (comp c e1).1.length) e2).1 ++
        [⟨GateOp.and, [(comp c e1).2, (comp (c + (comp c e1).1.length) e2).2]⟩],
        c + (comp c e1).1.length + (comp (c + (comp c e1).1.length) e2).1.length)
  | c, .disj e1 e2 =>
      ((comp c e1).1 ++ (comp (c + (comp c e1).1.length) e2).1 ++
        [⟨GateOp.or, [(comp c e1).2, (comp (c + (comp c e1).1.length) e2).2]⟩],
        c + (comp c e1).1.length + (comp (c + (comp c e1).1.length) e2).1.length)
  | c, .tt => ([⟨GateOp.and, []⟩], c)
  | c, .ff => ([⟨GateOp.or, []⟩], c)

theorem ev_prefix {n : ℕ} : ∀ (e : Ex), e.ok n → ∀ (a b : List Bool), n ≤ a.length → a <+: b →
    e.ev b = e.ev a
  | .var i, h, a, b, hn, hp => by
      simp only [Ex.ev]; exact getD_prefix hp (by simp only [Ex.ok] at h; omega)
  | .neg e, h, a, b, hn, hp => by simp only [Ex.ev]; rw [ev_prefix e h a b hn hp]
  | .conj e1 e2, h, a, b, hn, hp => by
      simp only [Ex.ev]; rw [ev_prefix e1 h.1 a b hn hp, ev_prefix e2 h.2 a b hn hp]
  | .disj e1 e2, h, a, b, hn, hp => by
      simp only [Ex.ev]; rw [ev_prefix e1 h.1 a b hn hp, ev_prefix e2 h.2 a b hn hp]
  | .tt, _, _, _, _, _ => rfl
  | .ff, _, _, _, _, _ => rfl

theorem comp_out {n : ℕ} : ∀ (e : Ex) (c : ℕ), e.ok n → n ≤ c →
    (comp c e).2 < c + (comp c e).1.length
  | .var i, c, h, hn => by simp only [comp, Ex.ok] at *; omega
  | .neg e, c, h, hn => by simp [comp]
  | .conj e1 e2, c, h, hn => by simp [comp]; omega
  | .disj e1 e2, c, h, hn => by simp [comp]; omega
  | .tt, c, h, hn => by simp [comp]
  | .ff, c, h, hn => by simp [comp]

theorem comp_ev {n : ℕ} : ∀ (e : Ex) (a : List Bool), e.ok n → n ≤ a.length →
    (run (comp a.length e).1 a).getD (comp a.length e).2 false = e.ev a
  | .var i, a, h, hn => by simp [comp, run_nil, Ex.ev]
  | .neg e, a, h, hn => by
      have ih := comp_ev e a h hn
      simp only [comp, Ex.ev]
      rw [run_append, run_single, List.getD_append_right _ _ _ _ (by rw [length_run])]
      simp only [List.map_cons, List.map_nil, GateOp.eval, ih]
      simp [length_run]
  | .conj e1 e2, a, h, hn => by
      have ih1 := comp_ev e1 a h.1 hn
      have ho1 := comp_out e1 a.length h.1 hn
      set a1 := run (comp a.length e1).1 a with ha1
      have hl1 : a1.length = a.length + (comp a.length e1).1.length := length_run _ _
      have ih2 := comp_ev e2 a1 h.2 (by omega)
      rw [hl1] at ih2
      have ho2 := comp_out e2 (a.length + (comp a.length e1).1.length) h.2 (by omega)
      simp only [comp, Ex.ev]
      rw [run_append, run_append, ← ha1, run_single,
        List.getD_append_right _ _ _ _ (by rw [length_run]; omega)]
      have hl2 := length_run (comp (a.length + (comp a.length e1).1.length) e2).1 a1
      have e1p : (run (comp (a.length + (comp a.length e1).1.length) e2).1 a1).getD
          (comp a.length e1).2 false = a1.getD (comp a.length e1).2 false :=
        getD_prefix (prefix_run _ _) (by omega)
      have e2p : e2.ev a1 = e2.ev a := ev_prefix e2 h.2 a a1 hn (prefix_run _ _)
      simp only [List.map_cons, List.map_nil, GateOp.eval, e1p, ih1, ih2, e2p]
      simp [hl2, hl1]
  | .disj e1 e2, a, h, hn => by
      have ih1 := comp_ev e1 a h.1 hn
      have ho1 := comp_out e1 a.length h.1 hn
      set a1 := run (comp a.length e1).1 a with ha1
      have hl1 : a1.length = a.length + (comp a.length e1).1.length := length_run _ _
      have ih2 := comp_ev e2 a1 h.2 (by omega)
      rw [hl1] at ih2
      have ho2 := comp_out e2 (a.length + (comp a.length e1).1.length) h.2 (by omega)
      simp only [comp, Ex.ev]
      rw [run_append, run_append, ← ha1, run_single,
        List.getD_append_right _ _ _ _ (by rw [length_run]; omega)]
      have hl2 := length_run (comp (a.length + (comp a.length e1).1.length) e2).1 a1
      have e1p : (run (comp (a.length + (comp a.length e1).1.length) e2).1 a1).getD
          (comp a.length e1).2 false = a1.getD (comp a.length e1).2 false :=
        getD_prefix (prefix_run _ _) (by omega)
      have e2p : e2.ev a1 = e2.ev a := ev_prefix e2 h.2 a a1 hn (prefix_run _ _)
      simp only [List.map_cons, List.map_nil, GateOp.eval, e1p, ih1, ih2, e2p]
      simp [hl2, hl1]
  | .tt, a, h, hn => by simp [comp, run_single, Ex.ev, GateOp.eval]
  | .ff, a, h, hn => by simp [comp, run_single, Ex.ev, GateOp.eval]

def RB (c : ℕ) (gs : List Gate) : Prop :=
  ∀ j (h : j < gs.length), ∀ i ∈ (gs[j]).inputs, i < c + j

def Fan (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem RB_append {c : ℕ} {g1 g2 : List Gate} (h1 : RB c g1) (h2 : RB (c + g1.length) g2) :
    RB c (g1 ++ g2) := by
  intro j hj i hi
  by_cases hj1 : j < g1.length
  · rw [List.getElem_append_left hj1] at hi
    exact h1 j hj1 i hi
  · rw [List.getElem_append_right (by omega)] at hi
    have := h2 (j - g1.length) (by simp at hj; omega) i hi
    omega

theorem RB_single {c : ℕ} {g : Gate} (h : ∀ i ∈ g.inputs, i < c) : RB c [g] := by
  intro j hj i hi
  simp at hj; subst hj
  have := h i (by simpa using hi)
  omega

theorem comp_rb {n : ℕ} : ∀ (e : Ex) (c : ℕ), e.ok n → n ≤ c → RB c (comp c e).1 ∧ Fan (comp c e).1
  | .var i, c, h, hn => by
      simp only [comp]; exact ⟨fun j hj => by simp at hj, fun g hg => by simp at hg⟩
  | .neg e, c, h, hn => by
      have ih := comp_rb e c h hn
      have ho := comp_out e c h hn
      simp only [comp]
      refine ⟨RB_append ih.1 (RB_single ?_), ?_⟩
      · intro i hi; simp at hi; omega
      · intro g hg
        rcases List.mem_append.1 hg with hg | hg
        · exact ih.2 g hg
        · simp at hg; subst hg; simp
  | .conj e1 e2, c, h, hn => by
      have ih1 := comp_rb e1 c h.1 hn
      have ho1 := comp_out e1 c h.1 hn
      have ih2 := comp_rb e2 (c + (comp c e1).1.length) h.2 (by omega)
      have ho2 := comp_out e2 (c + (comp c e1).1.length) h.2 (by omega)
      simp only [comp]
      refine ⟨RB_append (RB_append ih1.1 ih2.1) (RB_single ?_), ?_⟩
      · intro i hi; simp at hi; rcases hi with hi | hi <;> subst hi <;> simp <;> omega
      · intro g hg
        rcases List.mem_append.1 hg with hg | hg
        · rcases List.mem_append.1 hg with hg | hg
          · exact ih1.2 g hg
          · exact ih2.2 g hg
        · simp at hg; subst hg; simp
  | .disj e1 e2, c, h, hn => by
      have ih1 := comp_rb e1 c h.1 hn
      have ho1 := comp_out e1 c h.1 hn
      have ih2 := comp_rb e2 (c + (comp c e1).1.length) h.2 (by omega)
      have ho2 := comp_out e2 (c + (comp c e1).1.length) h.2 (by omega)
      simp only [comp]
      refine ⟨RB_append (RB_append ih1.1 ih2.1) (RB_single ?_), ?_⟩
      · intro i hi; simp at hi; rcases hi with hi | hi <;> subst hi <;> simp <;> omega
      · intro g hg
        rcases List.mem_append.1 hg with hg | hg
        · rcases List.mem_append.1 hg with hg | hg
          · exact ih1.2 g hg
          · exact ih2.2 g hg
        · simp at hg; subst hg; simp
  | .tt, c, h, hn => by
      simp only [comp]
      exact ⟨RB_single (by simp), fun g hg => by simp at hg; subst hg; simp⟩
  | .ff, c, h, hn => by
      simp only [comp]
      exact ⟨RB_single (by simp), fun g hg => by simp at hg; subst hg; simp⟩

theorem readsBack_of_RB {n : ℕ} {gs : List Gate} (h : RB n gs) (o : ℕ) :
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n ⟨gs, o⟩ := by
  intro j hj i hi
  simp only [PEqualNP.MetaComplexity.NestedCover.gateAt] at hi
  rw [List.getD_eq_getElem _ _ hj] at hi
  exact h j hj i hi

def bigOr (es : List Ex) : Ex := es.foldr Ex.disj Ex.ff
def bigAnd (es : List Ex) : Ex := es.foldr Ex.conj Ex.tt

theorem bigOr_ev (a : List Bool) : ∀ es : List Ex, (bigOr es).ev a = es.any (fun e => e.ev a)
  | [] => rfl
  | e :: es => by simp only [bigOr, List.foldr_cons, Ex.ev, List.any_cons]; rw [← bigOr, bigOr_ev a es]

theorem bigAnd_ev (a : List Bool) : ∀ es : List Ex, (bigAnd es).ev a = es.all (fun e => e.ev a)
  | [] => rfl
  | e :: es => by simp only [bigAnd, List.foldr_cons, Ex.ev, List.all_cons]; rw [← bigAnd, bigAnd_ev a es]

theorem bigOr_ok {n : ℕ} : ∀ es : List Ex, (∀ e ∈ es, e.ok n) → (bigOr es).ok n
  | [], _ => trivial
  | e :: es, h => by
      simp only [bigOr, List.foldr_cons]
      exact ⟨h e (by simp), bigOr_ok es (fun e' he' => h e' (by simp [he']))⟩

theorem bigAnd_ok {n : ℕ} : ∀ es : List Ex, (∀ e ∈ es, e.ok n) → (bigAnd es).ok n
  | [], _ => trivial
  | e :: es, h => by
      simp only [bigAnd, List.foldr_cons]
      exact ⟨h e (by simp), bigAnd_ok es (fun e' he' => h e' (by simp [he']))⟩

def lit (w : List Bool) (i : ℕ) : Ex := if w.getD i false then Ex.var i else Ex.neg (Ex.var i)

def wordTest (w : List Bool) : Ex := bigAnd ((List.range w.length).map (lit w))

theorem wordTest_ok (w : List Bool) : (wordTest w).ok w.length := by
  apply bigAnd_ok
  intro e he
  simp only [List.mem_map, List.mem_range] at he
  obtain ⟨i, hi, rfl⟩ := he
  unfold lit; split_ifs <;> simp [Ex.ok, hi]

theorem wordTest_ev (w x : List Bool) (hl : x.length = w.length) :
    (wordTest w).ev x = true ↔ x = w := by
  constructor
  · intro h
    rw [wordTest, bigAnd_ev, List.all_eq_true] at h
    apply List.ext_getElem hl
    intro i h1 h2
    have := h (lit w i) (by simp only [List.mem_map, List.mem_range]; exact ⟨i, h2, rfl⟩)
    rw [← List.getD_eq_getElem _ false h1, ← List.getD_eq_getElem _ false h2]
    unfold lit at this
    split_ifs at this with hw
    · simp only [Ex.ev] at this; rw [this, hw]
    · simp only [Ex.ev, Bool.not_eq_true'] at this; rw [this]; simpa using hw
  · rintro rfl
    rw [wordTest, bigAnd_ev, List.all_eq_true]
    intro e he
    simp only [List.mem_map, List.mem_range] at he
    obtain ⟨i, hi, rfl⟩ := he
    unfold lit; split_ifs with hw
    · simp only [Ex.ev]; exact hw
    · simp only [Ex.ev]; simpa using hw

theorem key (k p q u v u' v' : ℕ) (hu : u < k+p) (hv : v < k+q) (hu' : u' < k+p) (hv' : v' < k+q)
  (H : ∀ w, ((w<k ∧ (u=w ∨ v=w)) ∨ (k ≤ w ∧ w < k+p ∧ u = w) ∨ (k+p ≤ w ∧ w < k+p+q ∧ v+p = w)) ↔
     ((w<k ∧ (u'=w ∨ v'=w)) ∨ (k ≤ w ∧ w < k+p ∧ u' = w) ∨ (k+p ≤ w ∧ w < k+p+q ∧ v'+p = w))) :
  (u'=u ∧ v'=v) ∨ (u<k ∧ v<k ∧ u'=v ∧ v'=u) := by
  by_cases hku : k ≤ u
  · have e1 : u' = u := by have := (H u).1 (by omega); omega
    by_cases hkv : k ≤ v
    · have e2 : v' = v := by have := (H (v+p)).1 (by omega); omega
      omega
    · have e2 : u' = v ∨ v' = v := by have := (H v).1 (by omega); omega
      omega
  · have hu'k : u' < k := by
      by_contra hc
      have := (H u').2 (by omega); omega
    by_cases hkv : k ≤ v
    · have e2 : v' = v := by have := (H (v+p)).1 (by omega); omega
      have e1 : u' = u ∨ v' = u := by have := (H u).1 (by omega); omega
      omega
    · have hv'k : v' < k := by
        by_contra hc
        have := (H (v'+p)).2 (by omega); omega
      have a1 : u' = u ∨ v' = u := by have := (H u).1 (by omega); omega
      have a2 : u' = v ∨ v' = v := by have := (H v).1 (by omega); omega
      have a3 : u = u' ∨ v = u' := by have := (H u').2 (by omega); omega
      have a4 : u = v' ∨ v = v' := by have := (H v').2 (by omega); omega
      omega

def mg (k p q : ℕ) (u : Fin (k+p)) (v : Fin (k+q)) : List Bool :=
  List.ofFn (fun i : Fin k => decide (u.val=i.val ∨ v.val=i.val)) ++
    List.ofFn (fun i : Fin p => decide (u.val=k+i.val)) ++
    List.ofFn (fun j : Fin q => decide (v.val=k+j.val))

theorem mg_length (k p q : ℕ) (u : Fin (k+p)) (v : Fin (k+q)) : (mg k p q u v).length = k+p+q := by
  simp [mg]; omega

theorem mg_getD (k p q : ℕ) (u : Fin (k+p)) (v : Fin (k+q)) (w : ℕ) :
    (mg k p q u v).getD w false = decide ((w<k ∧ (u.val=w ∨ v.val=w)) ∨
      (k ≤ w ∧ w < k+p ∧ u.val = w) ∨ (k+p ≤ w ∧ w < k+p+q ∧ v.val+p = w)) := by
  unfold mg
  by_cases h1 : w < k
  · rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simp; omega),
      getD_ofFn]
    split_ifs
    exact decide_eq_decide.2 (by simp; omega)
  · by_cases h2 : w < k + p
    · rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by simp; omega),
        getD_ofFn]
      split_ifs with h4
      · exact decide_eq_decide.2 (by simp; omega)
      · simp at h4; omega
    · rw [List.getD_append_right _ _ _ _ (by simp; omega), getD_ofFn]
      split_ifs with h3
      · exact decide_eq_decide.2 (by simp; omega)
      · simp at h3; symm; simp; omega

theorem list_ext_getD (a b : List Bool) (hl : a.length = b.length)
    (h : ∀ w, a.getD w false = b.getD w false) : a = b := by
  apply List.ext_getElem hl
  intro i h1 h2
  rw [← List.getD_eq_getElem _ false h1, ← List.getD_eq_getElem _ false h2]
  exact h i

theorem mg_wd (k p q : ℕ) (A : Fin (k+p) → Fin (k+q) → Bool)
    (hs : ∀ i j : Fin k, A (Fin.castAdd p i) (Fin.castAdd q j) = A (Fin.castAdd p j) (Fin.castAdd q i))
    (u u' : Fin (k+p)) (v v' : Fin (k+q)) (he : mg k p q u v = mg k p q u' v') :
    A u v = A u' v' := by
  have H : ∀ w, ((w<k ∧ (u.val=w ∨ v.val=w)) ∨ (k ≤ w ∧ w < k+p ∧ u.val = w) ∨
      (k+p ≤ w ∧ w < k+p+q ∧ v.val+p = w)) ↔ ((w<k ∧ (u'.val=w ∨ v'.val=w)) ∨
      (k ≤ w ∧ w < k+p ∧ u'.val = w) ∨ (k+p ≤ w ∧ w < k+p+q ∧ v'.val+p = w)) := by
    intro w
    have := congrArg (fun l => l.getD w false) he
    simp only [mg_getD] at this
    exact decide_eq_decide.1 this
  rcases key k p q u.val v.val u'.val v'.val u.isLt v.isLt u'.isLt v'.isLt H with
    ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
  · rw [Fin.ext h1, Fin.ext h2]
  · have := hs ⟨u.val, h1⟩ ⟨v.val, h2⟩
    have eu : Fin.castAdd p (⟨u.val, h1⟩ : Fin k) = u := Fin.ext rfl
    have ev : Fin.castAdd q (⟨v.val, h2⟩ : Fin k) = v := Fin.ext rfl
    have eu' : Fin.castAdd p (⟨v.val, h2⟩ : Fin k) = u' := Fin.ext (by simp; omega)
    have ev' : Fin.castAdd q (⟨u.val, h1⟩ : Fin k) = v' := Fin.ext (by simp; omega)
    rw [eu, ev, eu', ev'] at this
    exact this

def pairs (k p q : ℕ) : List (Fin (k+p) × Fin (k+q)) :=
  (List.finRange (k+p)).flatMap (fun u => (List.finRange (k+q)).map (fun v => (u, v)))

def bigE (k p q : ℕ) (A : Fin (k+p) → Fin (k+q) → Bool) : Ex :=
  bigOr (((pairs k p q).filter (fun uv => A uv.1 uv.2)).map (fun uv => wordTest (mg k p q uv.1 uv.2)))

theorem bigE_ok (k p q : ℕ) (A : Fin (k+p) → Fin (k+q) → Bool) : (bigE k p q A).ok (k+p+q) := by
  apply bigOr_ok
  intro e he
  simp only [List.mem_map] at he
  obtain ⟨uv, _, rfl⟩ := he
  have := wordTest_ok (mg k p q uv.1 uv.2)
  rwa [mg_length] at this

theorem bigE_ev (k p q : ℕ) (A : Fin (k+p) → Fin (k+q) → Bool)
    (hs : ∀ i j : Fin k, A (Fin.castAdd p i) (Fin.castAdd q j) = A (Fin.castAdd p j) (Fin.castAdd q i))
    (u : Fin (k+p)) (v : Fin (k+q)) : (bigE k p q A).ev (mg k p q u v) = A u v := by
  rw [bigE, bigOr_ev]
  apply Bool.eq_iff_iff.2
  rw [List.any_eq_true]
  constructor
  · rintro ⟨e, he, hev⟩
    simp only [List.mem_map, List.mem_filter] at he
    obtain ⟨uv, ⟨_, hA⟩, rfl⟩ := he
    rw [wordTest_ev _ _ (by rw [mg_length, mg_length])] at hev
    rw [mg_wd k p q A hs u uv.1 v uv.2 hev]; exact hA
  · intro hA
    refine ⟨wordTest (mg k p q u v), ?_, ?_⟩
    · simp only [List.mem_map, List.mem_filter]
      exact ⟨(u, v), ⟨by simp [pairs], hA⟩, rfl⟩
    · rw [wordTest_ev _ _ rfl]

theorem part1 (k p q : ℕ) (A : Fin (k+p) → Fin (k+q) → Bool) :
    (∀ i j : Fin k,
      A (Fin.castAdd p i) (Fin.castAdd q j) = A (Fin.castAdd p j) (Fin.castAdd q i)) ↔
    ∃ D : Circuit, (PEqualNP.MetaComplexity.FanInTwo D ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+p+q) D) ∧
      ∀ u v, D.eval (mg k p q u v) = A u v := by
  constructor
  · intro hs
    have hrb := comp_rb (bigE k p q A) (k+p+q) (bigE_ok k p q A) le_rfl
    refine ⟨⟨(comp (k+p+q) (bigE k p q A)).1, (comp (k+p+q) (bigE k p q A)).2⟩,
      ⟨hrb.2, readsBack_of_RB hrb.1 _⟩, ?_⟩
    intro u v
    have := comp_ev (bigE k p q A) (mg k p q u v) (bigE_ok k p q A) (by rw [mg_length])
    rw [mg_length, bigE_ev k p q A hs] at this
    exact this
  · rintro ⟨D, _, hD⟩ i j
    rw [← hD, ← hD]
    congr 1
    apply list_ext_getD _ _ (by rw [mg_length, mg_length])
    intro w
    simp only [mg_getD, Fin.val_castAdd]
    exact decide_eq_decide.2 (by omega)

def rl (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

theorem relabel (f : ℕ → ℕ) : ∀ (gs : List Gate) (a b : List Bool), RB a.length gs →
    (∀ w, a.length ≤ w → f w = b.length + (w - a.length)) →
    (∀ w < a.length, f w < b.length ∧ b.getD (f w) false = a.getD w false) →
    ∀ w, (run (gs.map (rl f)) b).getD (f w) false = (run gs a).getD w false
  | [], a, b, _, hf, hab => by
      intro w
      simp only [List.map_nil, run_nil]
      by_cases hw : w < a.length
      · exact (hab w hw).2
      · rw [List.getD_eq_default _ _ (by rw [hf w (by omega)]; omega),
          List.getD_eq_default _ _ (by omega)]
  | g :: gs, a, b, hrb, hf, hab => by
      have hval : (rl f g).op.eval ((rl f g).inputs.map fun i => b.getD i false) =
          g.op.eval (g.inputs.map fun i => a.getD i false) := by
        simp only [rl, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i hi
        have := hrb 0 (by simp) i (by simpa using hi)
        exact (hab i (by omega)).2
      simp only [List.map_cons, run_cons]
      rw [hval]
      apply relabel f gs
      · intro j hj i hi
        have := hrb (j+1) (by simp; omega) i (by simpa using hi)
        simp; omega
      · intro w hw
        simp at hw ⊢
        rw [hf w (by omega)]; omega
      · intro w hw
        simp at hw
        by_cases hw' : w < a.length
        · have := hab w hw'
          refine ⟨by simp; omega, ?_⟩
          rw [List.getD_append _ _ _ _ this.1, List.getD_append _ _ _ _ hw', this.2]
        · have hwe : w = a.length := by omega
          subst hwe
          rw [hf _ le_rfl]
          refine ⟨by simp, ?_⟩
          rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
          simp

theorem run_shallow (y : List Bool) : ∀ (gs : List Gate) (acc : List Bool),
    (∀ g ∈ gs, ∀ i ∈ g.inputs, i < y.length) →
    run gs (y ++ acc) = y ++ acc ++ gs.map (fun g => g.op.eval (g.inputs.map fun i => y.getD i false))
  | [], acc, _ => by simp [run_nil]
  | g :: gs, acc, h => by
      rw [run_cons]
      have hv : (g.inputs.map fun i => (y ++ acc).getD i false) =
          g.inputs.map fun i => y.getD i false := by
        apply List.map_congr_left
        intro i hi
        exact List.getD_append _ _ _ _ (h g (by simp) i hi)
      rw [hv, List.append_assoc y acc, run_shallow y gs _ (fun g' hg' => h g' (by simp [hg']))]
      simp

theorem oneEach_getD (k p q : ℕ) (u : Fin (k+p)) (v : Fin (k+q)) (w : ℕ) :
    (PEqualNP.Represents.oneEach u v).getD w false = decide ((w < k+p ∧ u.val = w) ∨
      (k+p ≤ w ∧ w < k+p+(k+q) ∧ v.val + (k+p) = w)) := by
  unfold PEqualNP.Represents.oneEach
  by_cases h1 : w < k + p
  · rw [List.getD_append _ _ _ _ (by simp; omega), getD_ofFn]
    split_ifs
    exact decide_eq_decide.2 (by rw [Fin.ext_iff]; simp; omega)
  · rw [List.getD_append_right _ _ _ _ (by simp; omega), getD_ofFn]
    split_ifs with h3
    · exact decide_eq_decide.2 (by rw [Fin.ext_iff]; simp; omega)
    · simp at h3; symm; simp; omega

def preG (k p : ℕ) : List Gate :=
  List.ofFn (fun i : Fin k => (⟨GateOp.or, [i.val, (k+p)+i.val]⟩ : Gate))

def fm (k p q : ℕ) (w : ℕ) : ℕ :=
  if w < k then (k+p)+(k+q) + w else if w < k+p then w else if w < k+p+q then w + k else w + 2*k

theorem part2 (k p q : ℕ) (D : Circuit) (hD : PEqualNP.MetaComplexity.FanInTwo D ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+p+q) D) :
    ∃ E : Circuit, (PEqualNP.MetaComplexity.FanInTwo E ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack ((k+p)+(k+q)) E) ∧
      E.gates.take k = preG k p ∧
      E.size = k+D.size ∧
      ∀ u v, E.eval (PEqualNP.Represents.oneEach u v) = D.eval (mg k p q u v) := by
  have hPl : (preG k p).length = k := by simp [preG]
  refine ⟨⟨preG k p ++ D.gates.map (rl (fm k p q)), fm k p q D.output⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · simp only [preG, List.mem_ofFn] at hg
      obtain ⟨i, rfl⟩ := hg
      simp
    · simp only [List.mem_map] at hg
      obtain ⟨g', hg', rfl⟩ := hg
      have := hD.1 g' hg'
      simpa [rl] using this
  · intro j hj i hi
    simp only [PEqualNP.MetaComplexity.NestedCover.gateAt] at hi
    rw [List.getD_eq_getElem _ _ hj] at hi
    simp only [List.length_append, List.length_map, hPl] at hj
    by_cases hjk : j < k
    · rw [List.getElem_append_left (by omega)] at hi
      simp [preG] at hi
      omega
    · rw [List.getElem_append_right (by omega)] at hi
      simp only [List.getElem_map, rl, List.mem_map] at hi
      obtain ⟨i', hi', rfl⟩ := hi
      have h1 := hD.2 (j - (preG k p).length) (by omega) i'
      simp only [PEqualNP.MetaComplexity.NestedCover.gateAt] at h1
      rw [List.getD_eq_getElem _ _ (by omega)] at h1
      have h2 := h1 hi'
      rw [hPl] at h2
      unfold fm; split_ifs <;> omega
  · simp only
    rw [List.take_left' hPl]
  · simp [Circuit.size, hPl]
  · intro u v
    set y := PEqualNP.Represents.oneEach u v with hy
    have hyD : ∀ w, y.getD w false = decide ((w < k+p ∧ u.val = w) ∨
        (k+p ≤ w ∧ w < k+p+(k+q) ∧ v.val + (k+p) = w)) := fun w => oneEach_getD k p q u v w
    have hyl : y.length = (k+p)+(k+q) := by simp [hy, PEqualNP.Represents.oneEach]
    have hb := run_shallow y (preG k p) [] (by
      intro g hg i hi
      simp only [preG, List.mem_ofFn] at hg
      obtain ⟨j, rfl⟩ := hg
      simp at hi; omega)
    simp only [List.append_nil] at hb
    have hbl : (run (preG k p) y).length = (k+p)+(k+q)+k := by rw [length_run, hyl, hPl]
    show (run (preG k p ++ D.gates.map (rl (fm k p q))) y).getD (fm k p q D.output) false =
      (run D.gates (mg k p q u v)).getD D.output false
    rw [run_append]
    apply relabel
    · intro j hj i hi
      have h1 := hD.2 j hj i
      simp only [PEqualNP.MetaComplexity.NestedCover.gateAt] at h1
      rw [List.getD_eq_getElem _ _ hj] at h1
      rw [mg_length]; exact h1 hi
    · intro w hw
      rw [mg_length] at hw
      rw [mg_length, hbl]
      unfold fm; split_ifs <;> omega
    · intro w hw
      rw [mg_length] at hw
      refine ⟨by rw [hbl]; unfold fm; split_ifs <;> omega, ?_⟩
      rw [mg_getD, hb]
      by_cases h1 : w < k
      · have : fm k p q w = (k+p)+(k+q) + w := by simp [fm, h1]
        rw [this, List.getD_append_right _ _ _ _ (by omega), hyl, show (k+p)+(k+q)+w-((k+p)+(k+q)) = w by omega,
          List.getD_eq_getElem _ _ (by simp [preG]; omega)]
        simp only [preG, List.map_ofFn, List.getElem_ofFn, Function.comp_apply, List.map_cons,
          List.map_nil, GateOp.eval, hyD]
        simp only [List.any_cons, List.any_nil, id, Bool.or_false]
        rw [Bool.eq_iff_iff]; simp; omega
      · have hlt : fm k p q w < (k+p)+(k+q) := by unfold fm; split_ifs <;> omega
        rw [List.getD_append _ _ _ _ (by omega), hyD]
        apply decide_eq_decide.2
        unfold fm
        split_ifs <;> omega

end PEqualNP.Outside.L_meta_50274

theorem PEqualNP.Outside.L_meta_50274 : ∀ (k p q : Nat) (A : Fin (k+p) → Fin (k+q) → Bool),
  let merged := fun (u : Fin (k+p)) (v : Fin (k+q)) =>
    List.ofFn (fun i : Fin k => decide (u.val=i.val ∨ v.val=i.val)) ++
    List.ofFn (fun i : Fin p => decide (u.val=k+i.val)) ++
    List.ofFn (fun j : Fin q => decide (v.val=k+j.val))
  let legal := fun n (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C
  ((∀ i j : Fin k,
      A (Fin.castAdd p i) (Fin.castAdd q j) = A (Fin.castAdd p j) (Fin.castAdd q i)) ↔
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, legal (k+p+q) D ∧
      ∀ u v, D.eval (merged u v) = A u v) ∧
  (∀ D : PEqualNP.CircuitLowerBounds.Circuit, legal (k+p+q) D →
    ∃ E : PEqualNP.CircuitLowerBounds.Circuit, legal ((k+p)+(k+q)) E ∧
      E.gates.take k = List.ofFn (fun i : Fin k =>
        (⟨PEqualNP.CircuitLowerBounds.GateOp.or, [i.val, (k+p)+i.val]⟩ :
          PEqualNP.CircuitLowerBounds.Gate)) ∧
      E.size = k+D.size ∧
      ∀ u v, E.eval (PEqualNP.Represents.oneEach u v) = D.eval (merged u v)) := by
  intro k p q A merged legal
  exact ⟨PEqualNP.Outside.L_meta_50274.part1 k p q A, PEqualNP.Outside.L_meta_50274.part2 k p q⟩
