import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

namespace PEqualNP.Outside.L_meta_25000

abbrev Ref := Bool ⊕ ℕ
abbrev zero : Ref := Sum.inl false

def value (w : List Bool) : Ref → Bool
  | .inl b => b
  | .inr i => w.getD i false

def ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def readGate (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)
def step (w : List Bool) (g : Gate) := w ++ [readGate w g]

def kept (g : Gate) : Ref ⊕ Gate := .inr g

def bin (op : GateOp) (neutral : Bool) (a b : Ref) : Ref ⊕ Gate :=
  match a, b with
  | .inl x, _ => .inl (if x = neutral then b else .inl x)
  | _, .inl x => .inl (if x = neutral then a else .inl x)
  | .inr i, .inr j => kept ⟨op, [i,j]⟩

def lower (op : GateOp) (xs : List Ref) : Ref ⊕ Gate :=
  match op, xs with
  | .and, [] => .inl (.inl true)
  | .and, [a] => .inl a
  | .and, [a,b] => bin .and true a b
  | .or, [] => .inl zero
  | .or, [a] => .inl a
  | .or, [a,b] => bin .or false a b
  | .not, .inl b :: _ => .inl (.inl (!b))
  | .not, .inr i :: _ => kept ⟨.not, [i]⟩
  | .not, [] => .inl (.inl true)
  | _, _ => .inl zero

def meaning (w : List Bool) : Ref ⊕ Gate → Bool
  | .inl r => value w r
  | .inr g => readGate w g

def effective (g : Gate) : List ℕ :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

lemma gate_effective (g : Gate) (f : ℕ → Bool) :
    g.op.eval (g.inputs.map f) = g.op.eval ((effective g).map f) := by
  rcases g with ⟨op, is⟩
  cases op <;> cases is <;> rfl

lemma cases_short {α : Type} (xs : List α) (h : xs.length ≤ 2) :
    xs = [] ∨ (∃ a, xs = [a]) ∨ ∃ a b, xs = [a,b] := by
  rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨a,rfl⟩)
  · exact Or.inr (Or.inr ⟨a,b,rfl⟩)
  · simp at h

def valid (k p : ℕ) : Ref → Prop
  | .inl _ => True
  | .inr i => i < k ∧ i ≠ p

def validGate (k p : ℕ) (g : Gate) := ok g ∧ ∀ i ∈ g.inputs, i < k ∧ i ≠ p

def good (k p : ℕ) : Ref ⊕ Gate → Prop
  | .inl r => valid k p r
  | .inr g => validGate k p g

lemma lower_properties (g : Gate) (hg : ok g) (f : ℕ → Ref) (w : List Bool) (k p : ℕ)
    (hv : ∀ i, valid k p (f i)) :
    meaning w (lower g.op ((effective g).map f)) =
      g.op.eval (g.inputs.map fun i => value w (f i)) ∧
    good k p (lower g.op ((effective g).map f)) ∧
    (∀ i ∈ effective g, ∀ b : Bool, f i = .inl b →
      ∃ r, lower g.op ((effective g).map f) = .inl r) := by
  rcases g with ⟨op, is⟩
  have hl := hg.2
  have ho := hg.1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho
  rcases ho with h | h | h <;> subst op <;>
    rcases cases_short is hl with rfl | ⟨a,rfl⟩ | ⟨a,b,rfl⟩ <;>
    simp [lower, effective, meaning, GateOp.eval, valid, good, zero, value]
  all_goals try solve | exact hv _ | grind
  all_goals try
    have ha := hv a
    cases ea : f a with
    | inl x => cases x <;> simp_all [bin, value, good, valid, validGate, ok, meaning, kept, readGate, GateOp.eval]
    | inr x => simp_all [bin, value, good, valid, validGate, ok, meaning, kept, readGate, GateOp.eval]
  all_goals try
    have ha := hv a
    have hb := hv b
    cases ea : f a <;> cases eb : f b <;> rename_i x y <;>
      try cases x <;> try cases y <;>
      simp_all [bin, value, good, valid, validGate, ok, meaning, kept, readGate, GateOp.eval]

lemma get_append_at {α : Type} (l : List α) (a d : α) (i : ℕ) :
    (l ++ [a]).getD i d = if i = l.length then a else l.getD i d := by
  by_cases h : i < l.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h, show i ≠ l.length by omega]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    by_cases e : i = l.length
    · simp [e]
    · have hi : 1 ≤ i - l.length := by omega
      have hn : l[i]? = none := List.getElem?_eq_none (by omega)
      simp [e, List.getD_eq_getElem?_getD, hn, List.getElem?_eq_none (l := [a]) (by simpa using hi)]

lemma grow (k p : ℕ) (w : List Bool) (b : Bool) (r : Ref) (h : valid k p r)
    (hw : w.length = k) : valid (k+1) p r ∧ value (w ++ [b]) r = value w r := by
  cases r with
  | inl x => exact ⟨trivial,rfl⟩
  | inr i =>
    obtain ⟨hi,hp⟩ := h
    exact ⟨⟨by omega,hp⟩, by simp only [value, get_append_at, if_neg (show i ≠ w.length by omega)]⟩

lemma wires_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, step]; omega

def owns (p : ℕ) (g : Gate) : Prop := ok g ∧ p ∉ g.inputs

set_option maxHeartbeats 500000 in
lemma sweep {α : Type} (p : ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, ok g) :
    ∀ (k t : ℕ) (rs : List Ref) (x y : α → List Bool),
      p < k → p < t →
      rs.length = k →
      rs.getD p zero = zero →
      (∀ i, valid t p (rs.getD i zero)) →
      (∀ a, (x a).length = k ∧ (y a).length = t ∧
        ∀ i, value (y a) (rs.getD i zero) = (x a).getD i false) →
      ∃ (ds : List Gate) (refs : List Ref), (∀ g ∈ ds, owns p g) ∧
        ds.length ≤ gs.length ∧
        ((∃ g ∈ gs, p ∈ effective g) → ds.length < gs.length) ∧
        (∀ i, valid (t + ds.length) p (refs.getD i zero)) ∧
        ∀ a i, value (ds.foldl step (y a)) (refs.getD i zero) =
          (gs.foldl step (x a)).getD i false := by
  induction gs with
  | nil =>
    intro k t rs x y hpk hpt hk hp hv hh
    exact ⟨[], rs, by simp, by simp, by simp, by simpa using hv, fun a => (hh a).2.2⟩
  | cons g gs ih =>
    intro k t rs x y hpk hpt hk hp hv hh
    have hg0 := hg g (by simp)
    have hgs : ∀ d ∈ gs, ok d := fun d hd => hg d (by simp [hd])
    let z := lower g.op ((effective g).map fun i => rs.getD i zero)
    have sound (a : α) : meaning (y a) z = readGate (x a) g := by
      simpa only [z, readGate, (hh a).2.2] using
        (lower_properties g hg0 (fun i => rs.getD i zero) (y a) t p hv).1
    have hgood : good t p z :=
      (lower_properties g hg0 (fun i => rs.getD i zero) [] t p hv).2.1
    have skipGate (h : p ∈ effective g) : ∃ r, z = .inl r :=
      (lower_properties g hg0 (fun i => rs.getD i zero) [] t p hv).2.2 p h false hp
    have hpne : p ≠ k := by omega
    cases hz : z with
    | inl r =>
      have hr : valid t p r := by simpa [hz, good] using hgood
      have inv (a : α) : (step (x a) g).length = k+1 ∧ (y a).length = t ∧
          ∀ i, value (y a) ((rs ++ [r]).getD i zero) = (step (x a) g).getD i false := by
        obtain ⟨hx,hy,he⟩ := hh a
        refine ⟨by simp [step,hx],hy,?_⟩
        intro i
        rw [hz] at sound
        simp only [meaning] at sound
        simp only [step, get_append_at, hk, hx]
        split <;> simp only [sound a, he]
      obtain ⟨ds,refs,hds,hn,_,hvr,he⟩ :=
        ih hgs (k+1) t (rs ++ [r]) (fun a => step (x a) g) y
          (by omega) hpt (by simp [hk]) (by simpa only [get_append_at,hk,if_neg hpne] using hp)
          (fun i => by by_cases e : i = k <;> simp only [get_append_at,hk,e,if_true,if_false,hr,hv]) inv
      exact ⟨ds,refs,hds,by simp; omega,fun _ => by simp; omega,hvr,he⟩
    | inr d =>
      have hd : validGate t p d := by simpa [hz, good] using hgood
      have hno : p ∉ effective g := by
        intro he
        obtain ⟨r, hr⟩ := skipGate he
        simp [hz] at hr
      have inv (a : α) : (step (x a) g).length = k+1 ∧ (step (y a) d).length = t+1 ∧
          ∀ i, value (step (y a) d) ((rs ++ [(.inr t : Ref)]).getD i zero) =
            (step (x a) g).getD i false := by
        obtain ⟨hx,hy,he⟩ := hh a
        refine ⟨by simp [step,hx],by simp [step,hy],?_⟩
        intro i
        by_cases e : i = k
        · have hsa := sound a
          rw [hz] at hsa
          simpa only [meaning, step, get_append_at, hk, hx,hy,e,value,if_true] using hsa
        · simpa only [step,get_append_at,hk,hx,e,if_false,he] using
            (grow t p (y a) (readGate (y a) d) (rs.getD i zero) (hv i) hy).2
      have htne : t ≠ p := by omega
      obtain ⟨ds,refs,hds,hn,hs,hvr,he⟩ :=
        ih hgs (k+1) (t+1) (rs ++ [(.inr t : Ref)]) (fun a => step (x a) g)
          (fun a => step (y a) d) (by omega) (by omega) (by simp [hk])
          (by simpa only [get_append_at,hk,if_neg hpne] using hp)
          (fun i => by
            by_cases e : i = k
            · simpa only [get_append_at,hk,e,if_true,valid] using
                And.intro (Nat.lt_succ_self t) htne
            · simp only [get_append_at,hk,e,if_false]
              exact (grow t p (List.replicate t false) false _ (hv i) (by simp)).1) inv
      refine ⟨d :: ds,refs,?_,by simp; omega,?_,?_,he⟩
      · simp only [List.mem_cons]
        rintro j (rfl | hj)
        · exact ⟨hd.1, fun h => (hd.2 p h).2 rfl⟩
        · exact hds j hj
      · rintro ⟨j,hj,hj'⟩
        rcases List.mem_cons.mp hj with rfl | hj
        · exact (hno hj').elim
        · have := hs ⟨j,hj,hj'⟩
          simp; omega
      · simpa [Nat.add_assoc, Nat.add_comm 1 ds.length] using hvr

def initial (n p : ℕ) : List Ref :=
  List.ofFn (fun i : Fin n => if i.val = p then zero else .inr i.val)

lemma get_initial (n p i : ℕ) :
    (initial n p).getD i zero = if i < n ∧ i ≠ p then .inr i else zero := by
  by_cases hi : i < n
  · simp [initial, hi, List.getD_eq_getElem?_getD, List.getElem?_ofFn, eq_comm]
  · simp [initial, hi, List.getD_eq_getElem?_getD, List.getElem?_ofFn]

def erase (n p : ℕ) (w : List Bool) : List Bool :=
  List.ofFn (fun i : Fin n => if i.val = p then false else w.getD i false)

lemma get_erase (n p : ℕ) (w : List Bool) (hw : w.length = n) (i : ℕ) :
    (erase n p w).getD i false = if i = p then false else w.getD i false := by
  by_cases hi : i < n
  · simp [erase, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi]
  · have hnone : w[i]? = none := List.getElem?_eq_none (by omega)
    simp [erase, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, hnone]

def avoids (p : ℕ) (C : Circuit) : Prop :=
  C.output ≠ p ∧ ∀ g ∈ C.gates, p ∉ g.inputs

lemma fold_agree (gs : List Gate) (x y : List Bool) (p : ℕ) (hl : x.length = y.length)
    (hp : p < x.length) (hg : ∀ g ∈ gs, p ∉ effective g)
    (he : ∀ i ≠ p, x.getD i false = y.getD i false) :
    ∀ i ≠ p, (gs.foldl step x).getD i false = (gs.foldl step y).getD i false := by
  induction gs generalizing x y with
  | nil => exact he
  | cons g gs ih =>
    have hr : readGate x g = readGate y g := by
      unfold readGate
      rw [gate_effective g, gate_effective g (fun i => y.getD i false)]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact he i (fun e => hg g (by simp) (e ▸ hi))
    apply ih (step x g) (step y g)
    · simp [step,hl]
    · simp [step]; omega
    · exact fun d hd => hg d (by simp [hd])
    · intro i hi
      rw [step, step, get_append_at, get_append_at, hl, hr, he i hi]

lemma reduce {α : Type} (C : Circuit) (hC : FanInTwo C) (N p : ℕ) (hp : p < N)
    (y : α → List Bool) (hy : ∀ a, (y a).length = N) (hs : 1 ≤ C.size ∨ C.output ≠ p) :
    ∃ D : Circuit, FanInTwo D ∧ avoids p D ∧ D.size ≤ C.size ∧
      (∀ a, D.eval (y a) = C.eval (erase N p (y a))) ∧
      ((∃ g ∈ C.gates, p ∈ effective g) →
        D.size < C.size ∨ (∀ g ∈ D.gates, g.inputs = []) ∧ N ≤ D.output) := by
  classical
  by_cases hz : C.gates = []
  · have hno : C.output ≠ p := hs.resolve_left (by simp [Circuit.size,hz])
    refine ⟨C,hC,⟨hno,by simp [hz]⟩,le_rfl,?_,by simp [hz]⟩
    intro a
    change (C.gates.foldl step (y a)).getD C.output false =
      (C.gates.foldl step (erase N p (y a))).getD C.output false
    simp only [hz,List.foldl_nil,get_erase N p _ (hy a),if_neg hno]
  have hpos : 0 < C.size := by simpa [Circuit.size,List.length_pos_iff] using hz
  obtain ⟨ds,rs,hds,hn,hh,hv,he⟩ :=
    sweep p C.gates hC N N (initial N p) (fun a => erase N p (y a)) y hp hp
      (by simp [initial]) (by rw [get_initial]; simp)
      (fun i => by rw [get_initial]; by_cases hi : i < N ∧ i ≠ p <;> simp [hi,valid,zero])
      (fun a => by
        refine ⟨by simp [erase],hy a,?_⟩
        intro i
        rw [get_initial, get_erase N p _ (hy a)]
        by_cases hi : i < N
        · by_cases h : i = p <;> simp [hi,h,value,zero]
        · have he : (y a)[i]? = none := List.getElem?_eq_none (by have := hy a; omega)
          simp [hi,value,zero,List.getD_eq_getElem?_getD,he])
  cases h : rs.getD C.output zero with
  | inr i =>
    have hv' : valid (N+ds.length) p (.inr i) := by rw [← h]; exact hv _
    have hne : i ≠ p := hv'.2
    refine ⟨⟨ds,i⟩,fun g hg => (hds g hg).1,⟨hne,fun g hg => (hds g hg).2⟩,hn,?_,fun H => Or.inl (hh H)⟩
    intro a
    have ha := he a C.output
    rw [h] at ha
    exact ha
  | inl b =>
    have eq (a : α) : b = C.eval (erase N p (y a)) := by
      have ha := he a C.output
      rw [h] at ha
      exact ha
    cases b
    · refine ⟨⟨[],N⟩,by simp [FanInTwo],⟨Nat.ne_of_gt hp,by simp⟩,by simp [Circuit.size],?_,fun _ => Or.inl hpos⟩
      intro a
      have hnone : (y a)[N]? = none := List.getElem?_eq_none (by rw [hy a])
      simpa [Circuit.eval,Circuit.wires,List.getD_eq_getElem?_getD,hnone] using eq a
    · refine ⟨⟨[⟨.and,[]⟩],N⟩,by simp [FanInTwo],⟨Nat.ne_of_gt hp,by simp⟩,hpos,?_,fun _ => Or.inr ⟨by simp,le_rfl⟩⟩
      intro a
      change (step (y a) ⟨.and,[]⟩).getD N false = _
      simpa only [step,get_append_at,hy a,if_true,readGate,List.map_nil,GateOp.eval,List.all_nil] using eq a

lemma one_len {n m} (u : Fin n) (v : Fin m) : (oneEach u v).length = n+m := by
  simp [oneEach]

lemma one_left {n m} (u : Fin n) (v : Fin m) (i : ℕ) (h : i < n) :
    (oneEach u v).getD i false = decide (i = u.val) := by
  simp [oneEach,List.getD_eq_getElem?_getD,List.getElem?_append_left, List.getElem?_ofFn,h,Fin.ext_iff]

lemma one_right {n m} (u w : Fin n) (v : Fin m) (i : ℕ) (h : n ≤ i) :
    (oneEach u v).getD i false = (oneEach w v).getD i false := by
  simp [oneEach,List.getD_eq_getElem?_getD,List.getElem?_append_right,h]

lemma avoid_cone {N p : ℕ} {D : Circuit} (h : avoids p D) :
    D.output ≠ p ∧ ∀ g < D.gates.length,
      (D.output = N + g ∨ (N ≤ D.output ∧ PEqualNP.EdgeOwnership.InCone N D g (D.output-N))) →
      p ∉ (D.gates.getD g ⟨GateOp.and, []⟩).inputs := by
  refine ⟨h.1,?_⟩
  intro g hg _
  apply h.2
  simpa [List.getD_eq_getElem?_getD,hg] using List.getElem_mem (l := D.gates) hg

lemma constantFalse {n m} (w : Fin n) (v : Fin m) :
    (Circuit.mk [] (n+m)).eval (oneEach w v) = false := by
  change (oneEach w v).getD (n+m) false = false
  have hnone : (oneEach w v)[n+m]? = none := List.getElem?_eq_none (by rw [one_len])
  simp [List.getD_eq_getElem?_getD,hnone]

end PEqualNP.Outside.L_meta_25000

open PEqualNP.Outside.L_meta_25000

set_option maxHeartbeats 500000 in
theorem PEqualNP.Outside.L_meta_25000 : ∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (u u2 : Fin n), (∀ v : Fin m, A u v = A u2 v) → (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧ PEqualNP.Represents.Represents A C) → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ (∀ (w : Fin n) (v : Fin m), w ≠ u2 → C2.eval (PEqualNP.Represents.oneEach w v) = A w v) ∧ (C2.size + 1 ≤ s ∨ (C2.size ≤ s ∧ (C2.output ≠ u.val ∧ ∀ g < C2.gates.length, (C2.output = n + m + g ∨ (n + m ≤ C2.output ∧ PEqualNP.EdgeOwnership.InCone (n + m) C2 g (C2.output - (n + m)))) → u.val ∉ (C2.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs))) := by
  classical
  intro n m s A u u2 hrow ⟨C,hC,hsize,hrep⟩
  let y : {w : Fin n // w ≠ u2} × Fin m → List Bool := fun a => oneEach a.1.val a.2
  have hy (a) : (y a).length = n+m := one_len _ _
  have hu : u.val < n+m := by have := u.isLt; omega
  have h2 : u2.val < n+m := by have := u2.isLt; omega
  have leftNe {w z : Fin n} (h : w ≠ z) : z.val ≠ w.val :=
    fun he => h (Fin.ext he.symm)
  have unchanged (w : Fin n) (v : Fin m) (p : ℕ) (hf : (oneEach w v).getD p false = false) :
      erase (n+m) p (oneEach w v) = oneEach w v := by
    apply List.ext_getElem?
    intro i
    have hl : (erase (n+m) p (oneEach w v)).length = (oneEach w v).length := by simp [erase,one_len]
    by_cases hi : i < (oneEach w v).length
    · have eq := get_erase (n+m) p (oneEach w v) (one_len _ _) i
      have hix : i < (erase (n+m) p (oneEach w v)).length := by omega
      simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hix,Option.getD_some] at eq ⊢
      congr 1
      by_cases e : i=p
      · subst i
        simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some] at hf
        simpa [hf] using eq
      · simpa only [if_neg e] using eq
    · rw [List.getElem?_eq_none (by omega),List.getElem?_eq_none (by omega)]
  have emptyCase (h : ∀ w v, w ≠ u2 → A w v = false) :
      ∃ D : Circuit, FanInTwo D ∧ (∀ w v, w ≠ u2 → D.eval (oneEach w v) = A w v) ∧
        (D.size + 1 ≤ s ∨ D.size ≤ s ∧
         D.output ≠ u.val ∧ ∀ g < D.gates.length,
          (D.output = n + m + g ∨ (n + m ≤ D.output ∧ PEqualNP.EdgeOwnership.InCone (n + m) D g (D.output - (n + m)))) →
          u.val ∉ (D.gates.getD g ⟨GateOp.and, []⟩).inputs) := by
    exact ⟨⟨[],n+m⟩,by simp [FanInTwo],fun w v hw => (constantFalse w v).trans (h w v hw).symm,
      Or.inr ⟨Nat.zero_le _, avoid_cone ⟨Nat.ne_of_gt hu,by simp⟩⟩⟩
  by_cases hg : C.gates = []
  · have hn : avoids u.val C ∨ C.output = u.val := by
      by_cases h : C.output = u.val
      · exact Or.inr h
      · exact Or.inl ⟨h,by simp [hg]⟩
    rcases hn with hn | hn
    · exact ⟨C,hC,fun w v _ => hrep w v,Or.inr ⟨hsize,avoid_cone hn⟩⟩
    · have ev (w : Fin n) (v : Fin m) : A w v = decide (u.val = w.val) := by
        rw [← hrep w v]
        simpa [Circuit.eval,Circuit.wires,hg,hn] using one_left w v u.val u.isLt
      apply emptyCase
      intro w v hw
      by_cases e : u = u2
      · rw [ev,decide_eq_false (by simpa [e] using leftNe hw)]
      · have hf := hrow v
        rw [ev,ev] at hf
        simp [leftNe (Ne.symm e)] at hf
  have hpos : 1 ≤ C.size := by
    have h := List.length_pos_iff.mpr hg
    exact h
  by_cases hread : ∃ g ∈ C.gates, u2.val ∈ effective g
  · obtain ⟨D,hD,ha,hn,he,hh⟩ := reduce C hC (n+m) u2.val h2 y hy (Or.inl hpos)
    refine ⟨D,hD,?_,?_⟩
    · intro w v hw
      have hx := he (⟨w,hw⟩,v)
      change D.eval (oneEach w v) = C.eval (erase (n+m) u2.val (oneEach w v)) at hx
      rw [unchanged w v _ (by rw [one_left w v _ u2.isLt]; simp [leftNe hw]), hrep w v] at hx
      exact hx
    · rcases hh hread with hs | ⟨hs,ho⟩
      · exact Or.inl (by omega)
      · exact Or.inr ⟨hn.trans hsize, avoid_cone ⟨by omega,fun g hg => by simp [hs g hg]⟩⟩
  · have hnread : ∀ g ∈ C.gates, u2.val ∉ effective g :=
      fun g hg hm => hread ⟨g,hg,hm⟩
    by_cases ho : C.output = u2.val
    · apply emptyCase
      intro w v hw
      rw [← hrep w v]
      have hkeep (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
          (gs.foldl step x).getD i false = x.getD i false := by
        induction gs generalizing x with
        | nil => rfl
        | cons g gs ih =>
          rw [List.foldl_cons, ih _ (by simp [step]; omega)]
          simp only [step,get_append_at,if_neg (show i ≠ x.length by omega)]
      change (C.gates.foldl step (oneEach w v)).getD C.output false = false
      rw [ho, hkeep _ _ _ (by rw [one_len]; exact h2), one_left w v _ u2.isLt]
      simp [leftNe hw]
    · obtain ⟨D,hD,ha,hn,he,_⟩ := reduce C hC (n+m) u.val hu y hy (Or.inl hpos)
      refine ⟨D,hD,?_,Or.inr ⟨hn.trans hsize,avoid_cone ha⟩⟩
      intro w v hw
      have hx := he (⟨w,hw⟩,v)
      change D.eval (oneEach w v) = C.eval (erase (n+m) u.val (oneEach w v)) at hx
      rw [hx]
      by_cases ew : w = u
      · subst w
        have hne : u.val ≠ u2.val := (leftNe hw).symm
        have hdiff (i : ℕ) (hi : i ≠ u2.val) :
            (erase (n+m) u.val (oneEach u v)).getD i false = (oneEach u2 v).getD i false := by
          rw [get_erase _ _ _ (one_len _ _) i]
          by_cases hil : i < n
          · rw [one_left u v i hil,one_left u2 v i hil]
            simp [hi]
          · rw [if_neg (show i ≠ u.val by have := u.isLt; omega),one_right u u2 v i (by omega)]
        have hsame := fold_agree C.gates (erase (n+m) u.val (oneEach u v)) (oneEach u2 v) u2.val
          (by simp [erase,one_len]) (by simpa [erase] using h2) hnread hdiff C.output ho
        exact hsame.trans ((hrep u2 v).trans (hrow v).symm)
      · rw [unchanged w v _ (by rw [one_left w v _ u.isLt]; simp [leftNe ew]),hrep w v]
