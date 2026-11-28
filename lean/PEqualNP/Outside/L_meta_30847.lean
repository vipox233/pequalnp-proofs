import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_30847

open PEqualNP.CircuitLowerBounds

abbrev Sig := BitVec 256
abbrev Row := Fin 256
abbrev Bits := BitVec 192
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def zero : Sig := 0
def one : Sig := BitVec.allOnes 256
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one

private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin, BitVec.and_comm, BitVec.or_comm]

inductive Live (target : Sig) : Nat → Nat → Finset Sig → Prop
  | stop (hp : proper target) : Live target 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) :
      Live target (k + 1) (t + 1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) :
      Live target (k + 1) t (insert a (insert b U))

private lemma live_proper {target k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop hp => simpa using hp
  | unary ha _ _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb _ _ _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha, hb, fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {target k t S} (h : Live target k t S) : t ≤ k ∧ S.card + t ≤ k + 1 := by
  induction h with
  | stop _ => simp
  | @unary k t U a _ hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega, by omega⟩
  | @binary k t U a b d _ _ _ hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega, by omega⟩

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  simp only [bin, one, zero, Bool.false_eq_true, ite_false, ite_true,
    BitVec.and_allOnes, BitVec.or_allOnes, BitVec.and_self, BitVec.or_self, and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg, zero, one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz, ho⟩), hz, ho⟩)

def witnessBin (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

def witnessNeg (w : List Sig) (z : Sig) : Prop :=
  ∃ a ∈ w, proper a ∧ z = neg a

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witnessBin w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1, a0, az, ao, aa, aa'⟩ := bin_laws a
  obtain ⟨b1, b0, bz, bo, bb, bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham, hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm, hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a = b
  · subst b; cases d <;> simp_all
  exact Or.inr ⟨d, a, b, ham, hbm, hap, hbp, he, rfl⟩

private lemma inv_rep {w a} (ha : represented w a) :
    represented w (neg a) ∨ witnessNeg w (neg a) := by
  rcases operand_cases ha with rfl | rfl | ⟨hm, hp⟩
  · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
  · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
  · exact Or.inr ⟨a, hm, hp, rfl⟩

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
    represented w (gv w g) ∨
    (g.op = .not ∧ witnessNeg w (gv w g)) ∨
    witnessBin w (gv w g) := by
  obtain ⟨o, l⟩ := g
  obtain ⟨ho, hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) :
      represented w (neg a) ∨ (GateOp.not = .not ∧ witnessNeg w (neg a)) ∨ witnessBin w (neg a) :=
    (inv_rep ha).elim Or.inl (fun hw => Or.inr (Or.inl ⟨rfl, hw⟩))
  have bx (d : Bool) (a b : Sig) (ha : represented w a) (hb : represented w b) :
      represented w (bin d a b) ∨ (o = .not ∧ witnessNeg w (bin d a b)) ∨ witnessBin w (bin d a b) :=
    (bin_rep d ha hb).elim Or.inl (fun hw => Or.inr (Or.inr hw))
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, (bin_laws _).1]
          using Or.inl (get_rep w i)
      · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, (bin_laws _).2.1]
          using Or.inl (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons _ _ => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, (bin_laws _).1]
            using bx false _ _ (get_rep w i) (get_rep w j)
        · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, (bin_laws _).2.1]
            using bx true _ _ (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

private lemma pull_gate_bin {target} {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z ∨ witnessBin w z) (sub : ∀ a ∈ S, a ∈ w ++ [z]) :
    ∃ k' S', k' ≤ k + 1 ∧ Live target k' t S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k, S, by omega, h, ?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a ∈ w ∨ a = z) with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨d, a, b, ha, hb, pa, pb, hab, eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live target k t (insert (bin d a b) U) := by simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_, _, Nat.le_refl _, Live.binary pa pb hab hf ht, by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k, S, by omega, h, ?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma pull_gate_neg {target} {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z ∨ witnessNeg w z) (sub : ∀ a ∈ S, a ∈ w ++ [z]) :
    ∃ k' t' S', k' + (t + 1 - t') ≤ k + 1 ∧ t' ≤ t + 1 ∧ Live target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k, t, S, by omega, by omega, h, ?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a ∈ w ∨ a = z) with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨a, ha, hp', eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live target k t (insert (neg a) U) := by simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_, _, _, by omega, Nat.le_refl _, Live.unary hp' hf ht, by simpa using And.intro ha hu⟩
  · refine ⟨k, t, S, by omega, by omega, h, ?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

def isNotOp : GateOp → Bool
  | .not => true
  | _ => false

private lemma extract1 {target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ t ≤ gs.countP (fun g => isNotOp g.op) ∧
      Live target k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0, 0, {target}, by simp, by simp, Live.stop hp, by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k, t, S, hk, ht, run, hs⟩ := ih (w ++ [gv w g]) (fun a ha => legal a (by simp [ha])) hout
    rcases gate_rep w g (legal g (by simp)) with hr | ⟨hn, hwn⟩ | hwb
    · obtain ⟨k', S', hk', run', hS'⟩ := pull_gate_bin run (Or.inl hr) hs
      exact ⟨k', t, S', by simp; omega, by simp [List.countP_cons]; omega, run', hS'⟩
    · obtain ⟨k', t', S', hk', ht', run', hS'⟩ := pull_gate_neg run (Or.inr hwn) hs
      refine ⟨k', t', S', by simp; omega, ?_, run', hS'⟩
      have hnt : isNotOp g.op = true := by rw [hn]; rfl
      rw [List.countP_cons, hnt]; simp only [ite_true]; omega
    · obtain ⟨k', S', hk', run', hS'⟩ := pull_gate_bin run (Or.inr hwb) hs
      exact ⟨k', t, S', by simp; omega, by simp [List.countP_cons]; omega, run', hS'⟩

def bit (i : Row) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit, zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit, neg, i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit, bin]

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op = .and ∨ g.op = .or ∨ g.op = .not) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o, l⟩ := g
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg, bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op = .and ∨ g.op = .or ∨ g.op = .not) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l ++ [g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w ++ [gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons, List.map_append, List.map_singleton, run_bit i g w (hg g (by simp))]

private lemma live_zero_to_gates {target k S} (h : Live target k 0 S) (w : List Sig)
    (sub : ∀ a ∈ S, a ∈ w) :
    ∃ gs : List Gate, (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs.length = k ∧ target ∈ execute gs w := by
  generalize ht : (0 : Nat) = t at h
  induction h generalizing w with
  | stop _ =>
    exact ⟨[], by simp, rfl, by simpa [execute] using sub target (Finset.mem_singleton_self _)⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab hf tail ih =>
    have ha' : a ∈ w := sub a (Finset.mem_insert_self _ _)
    have hb' : b ∈ w := sub b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    obtain ⟨ia, hia, ha_eq⟩ := List.getElem_of_mem ha'
    obtain ⟨ib, hib, hb_eq⟩ := List.getElem_of_mem hb'
    let g : Gate := ⟨if d then .or else .and, [ia, ib]⟩
    have hgv : gv w g = bin d a b := by
      have ga : w.getD ia zero = a := by simp [List.getD_eq_getElem?_getD, hia, ha_eq]
      have gb : w.getD ib zero = b := by simp [List.getD_eq_getElem?_getD, hib, hb_eq]
      cases d
      · simp only [g, gv, Bool.false_eq_true, ite_false, List.map_cons, List.map_nil,
          List.foldr_cons, List.foldr_nil, (bin_laws _).1, ga, gb]
      · simp only [g, gv, ite_true, List.map_cons, List.map_nil,
          List.foldr_cons, List.foldr_nil, (bin_laws _).2.1, ga, gb]
    have sub' : ∀ v ∈ insert (bin d a b) U, v ∈ w ++ [gv w g] := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hu
      · rw [hgv]; simp
      · exact List.mem_append_left _ (sub v (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)))
    obtain ⟨gs, hmono, hlen, hout⟩ := ih (w ++ [gv w g]) sub' ht
    refine ⟨g :: gs, ?_, by simp [hlen], hout⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hm
    · cases d <;> simp [g]
    · exact hmono x hm

abbrev Wire (R : Type) := R → Bool
def inv {R} (a : Wire R) : Wire R := fun r => !(a r)
def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b
noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0
noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum
def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop := v ∈ pool ∨ Constant v
def supply {R} (pool xs : List (Wire R)) := ∀ a ∈ xs, Available pool a

inductive Reach {R} (roots : List (Wire R)) : Nat → Nat → List (Wire R) → Prop
  | start : Reach roots 0 0 roots
  | one {p t bank a} : Reach roots p t bank → Available bank a →
      Reach roots (p + 1) (t + 1) (inv a :: bank)
  | two {p t bank a b} (op : Bool) : Reach roots p t bank → Available bank a →
      Available bank b → Reach roots (p + 1) t (combine op a b :: bank)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x :: xs else xs

inductive Run {R} (goal : Wire R) : Nat → Nat → List (Wire R) → Prop
  | stop : Run goal 0 0 [goal]
  | perm {s t xs zs} : xs.Perm zs → Run goal s t xs → Run goal s t zs
  | one {s t a rest} (save : Bool) : Run goal s t (inv a :: kept save a rest) →
      Run goal (s + 1) (t + 1) (a :: rest)
  | two {s t a b rest} (op ka kb : Bool) :
      Run goal s t (combine op a b :: kept ka a (kept kb b rest)) →
      Run goal (s + 1) t (a :: b :: rest)

theorem mass_cons {R} (a : Wire R) (xs) : mass (a :: xs) = cost a + mass xs := by simp [mass]
theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept, mass_cons]
theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v, rfl⟩ := h; exact ⟨!v, rfl⟩
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v, rfl⟩ := h; obtain ⟨w, rfl⟩ := g; cases op <;> exact ⟨_, rfl⟩

theorem from_constant {R} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b) := by
  rcases h with ⟨v, rfl⟩ | ⟨v, rfl⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩

theorem available_cons {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w :: bank) v :=
  h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr

theorem extend_one {R} (roots : List (Wire R)) {p t bank a} (hp : Reach roots p t bank)
    (ha : Available bank a) :
    ∃ q u next, Reach roots q u next ∧ u ≤ t + 1 ∧ Available next (inv a) ∧
        (∀ v, Available bank v → Available next v) ∧ q + cost a + (t + 1 - u) ≤ p + 1 + cost (inv a) := by
  classical
  by_cases c : Constant a
  · exact ⟨p, t, bank, hp, by omega, Or.inr (inv_constant c), fun _ h => h,
      by simp [cost, c, inv_constant c]⟩
  · exact ⟨p + 1, t + 1, _, Reach.one hp ha, Nat.le_refl _, Or.inl (by simp),
      fun _ h => available_cons _ h, by simp [cost, c]⟩

theorem extend_two {R} (roots : List (Wire R)) {p t bank a b} (op) (hp : Reach roots p t bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q t next ∧ Available next (combine op a b) ∧
        (∀ v, Available bank v → Available next v) ∧
        q + cost a + cost b ≤ p + 1 + cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p, bank, hp, from_constant op c ha hb, fun _ h => h, ?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost, ca, cb, both_constant op ca cb]
    · simp [cost, ca, cb]
    · simp [cost, ca, cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p + 1, _, Reach.two op hp ha hb, Or.inl (by simp), fun _ h => available_cons _ h,
      by simp [cost, ca, cb]⟩

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x = a ∨ x ∈ xs := by cases k <;> simp_all [kept]

theorem contraction {R} {goal : Wire R} (nc : ¬Constant goal) {s t2 ws}
    (h : Run goal s t2 ws) (roots : List (Wire R)) {p t1 bank}
    (hp : Reach roots p t1 bank) (hs : supply bank ws) :
    ∃ q u next, Reach roots q u next ∧ u ≤ t1 + t2 ∧ Available next goal ∧ q + mass ws + (t1 + t2 - u) ≤ p + s := by
  classical
  induction h generalizing p t1 bank with
  | stop =>
    exact ⟨p, t1, bank, hp, by omega, hs _ (by simp), by simp [mass, cost, nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q, u, W, hW, hu, hv, hl⟩ := ih hp hsub
    exact ⟨q, u, W, hW, hu, hv, by simpa only [mass, ← (eq.map cost).sum_eq] using hl⟩
  | @one s t2 a rest save _ ih =>
    obtain ⟨r, u1, T, hT, hu1, hz, inc, le⟩ := extend_one roots hp (hs a (by simp))
    have ht : supply T (inv a :: kept save a rest) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · exact inc v (hs v (List.mem_cons.mpr (mem_kept hh)))
    obtain ⟨q, u, W, hW, hu, hv, hl⟩ := ih hT ht
    have hlen := mass_kept a rest save
    rw [mass_cons] at hl ⊢
    exact ⟨q, u, W, hW, by omega, hv, by omega⟩
  | @two s t2 a b rest op ka kb _ ih =>
    obtain ⟨r, T, hT, hz, inc, le⟩ := extend_two roots op hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (combine op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q, u, W, hW, hu, hv, hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q, u, W, hW, by omega, hv, ?_⟩
    rw [mass_cons, mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S := fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_run {R S : Type} (rows : S → R) {goal s t ws} (h : Run goal s t ws) :
    Run (restrictRows rows goal) s t (ws.map (restrictRows rows)) := by
  induction h with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | one save _ ih =>
    simp only [List.map_cons, restrict_kept] at ih ⊢
    exact Run.one save ih
  | two op ka kb _ ih =>
    simp only [List.map_cons, restrict_kept] at ih ⊢
    cases op
    · exact Run.two false ka kb ih
    · exact Run.two true ka kb ih

theorem projected_bound {R S : Type} (rows : S → R) {goal s t2 ws} (h : Run goal s t2 ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p t1 bank L}
    (hp : Reach roots p t1 bank) (hs : supply bank (ws.map (restrictRows rows)))
    (ht : t1 + t2 ≤ 1)
    (hl : ∀ q u bs, u ≤ 1 → Reach roots q u bs → Available bs (restrictRows rows goal) → L + u ≤ q) :
    L + (t1 + t2) + mass (ws.map (restrictRows rows)) ≤ p + s := by
  obtain ⟨q, u, bs, hq, hu, hit, hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q u bs (by omega) hq hit
  omega

def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit, table, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j, hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r; exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r; exact bit_neg _ _

theorem obs_bin (d : Bool) (a b : Sig) :
    observe (bin d a b) = combine d (observe a) (observe b) := by
  funext r; cases d <;> exact bit_bin _ _ _ _

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl
theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept, hn, ha]
theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {T : Sig} {k u S} (h : Live T k u S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run (observe T) k u (v.map observe) := by
  classical
  induction h generalizing v with
  | stop _ =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @unary k u U a ha fresh _ ih =>
    let rest := (U.erase a).toList
    let save := decide (a ∈ U)
    let tail := kept save a rest
    have er : rest.toFinset = U.erase a := by simp [rest]
    have hm : a ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have ht : tail.toFinset = U := by
      rw [show tail = kept save a rest by rfl, kept_fin, er]
      by_cases hh : a ∈ U <;> simp [save, hh]
    have nd := kept_nd save a rest hr hm
    have hf : neg a ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress := ih (neg a :: tail) (List.nodup_cons.mpr ⟨hf, nd⟩) (by simp [ht])
    rw [List.map_cons, map_kept, obs_neg] at progress
    have perm : (a :: rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm, hr⟩) hv
      simp [er, eqv]
    exact Run.perm (perm.map _) (Run.one save progress)
  | @binary k u U a b d ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid, kept, h, hab, ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin, kept_fin, er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j = a <;>
        by_cases bj : j = b <;> simp_all [ka, kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b :: tail) (List.nodup_cons.mpr ⟨hf, nd⟩) (by simp [ht])
    change Run _ _ _ ((bin d a b :: kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons, map_kept, map_kept, obs_bin] at progress
    have perm : (a :: b :: rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab, ar, br, hr]) hv
      ext j
      by_cases ja : j = a <;> by_cases jb : j = b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d ka kb progress)

theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [← table_observe (neg (table f)), obs_neg, observe_table]
theorem table_bin (d : Bool) (f g : Wire Row) :
    table (combine d f g) = bin d (table f) (table g) := by
  rw [← table_observe (bin d (table f) (table g)), obs_bin, observe_table, observe_table]

theorem available_rep {bank : List (Wire Row)} {a} (h : Available bank a) :
    represented (bank.map table) (table a) := by
  rcases h with hm | ⟨b, rfl⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply Or.inr
    cases b
    · have z : table (fun _ => false) = zero := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj; exact (bit_table _ ⟨j, hj⟩).trans (bit_zero ⟨j, hj⟩).symm
      exact fun hp => hp.1 z
    · have z : table (fun _ => true) = one := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj; exact (bit_table _ ⟨j, hj⟩).trans (bit_one ⟨j, hj⟩).symm
      exact fun hp => hp.2 z

theorem pull_cons_bin {w : List Sig} {z : Sig} {T k t S} (h : Live T k t S)
    (hz : represented w z ∨ witnessBin w z) (hs : ∀ a ∈ S, a ∈ z :: w) :
    ∃ k' S', k' ≤ k + 1 ∧ Live T k' t S' ∧ ∀ a ∈ S', a ∈ w :=
  pull_gate_bin h hz (fun a hm => by simpa [or_comm] using hs a hm)

theorem pull_cons_neg {w : List Sig} {z : Sig} {T k t S} (h : Live T k t S)
    (hz : represented w z ∨ witnessNeg w z) (hs : ∀ a ∈ S, a ∈ z :: w) :
    ∃ k' t' S', k' + (t + 1 - t') ≤ k + 1 ∧ t' ≤ t + 1 ∧ Live T k' t' S' ∧ ∀ a ∈ S', a ∈ w :=
  pull_gate_neg h hz (fun a hm => by simpa [or_comm] using hs a hm)

theorem reach_live_sub {roots : List (Wire Row)} {p t0 bank}
    (h : Reach roots p t0 bank) {T k t S} (run : Live T k t S)
    (sub : ∀ a ∈ S, a ∈ bank.map table) :
    ∃ l v U, l + (t0 + t - v) ≤ p + k ∧ v ≤ t0 + t ∧ Live T l v U ∧ ∀ a ∈ U, a ∈ roots.map table := by
  induction h generalizing k t S with
  | start => exact ⟨k, t, S, by omega, by omega, run, sub⟩
  | @one p t0 bank a h ha ih =>
    rw [List.map_cons, table_inv] at sub
    obtain ⟨k', t', S', hk, ht, run', sub'⟩ := pull_cons_neg run (inv_rep (available_rep ha)) sub
    obtain ⟨l, v, U, hl, hv, hr, hs⟩ := ih run' sub'
    exact ⟨l, v, U, by omega, by omega, hr, hs⟩
  | @two p t0 bank a b d h ha hb ih =>
    rw [List.map_cons, table_bin] at sub
    obtain ⟨k', S', hk, run', sub'⟩ := pull_cons_bin run (bin_rep d (available_rep ha) (available_rep hb)) sub
    obtain ⟨l, v, U, hl, hv, hr, hs⟩ := ih run' sub'
    exact ⟨l, v, U, by omega, by omega, hr, hs⟩

theorem reach_live {roots : List Sig} {p t0 bank T} (hp : proper T)
    (h : Reach (roots.map observe) p t0 bank) (hit : Available bank (observe T)) :
    ∃ k t S, k + (t0 - t) ≤ p ∧ t ≤ t0 ∧ Live T k t S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l, v, U, hl, hv, hr, hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l, v, U, by omega, by omega, hr, ?_⟩
  simpa [List.map_map, Function.comp_def, table_observe] using hs

theorem live_row_difference {T k t S} (h : Live T k t S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h with
  | stop _ => exact ⟨_, by simp, diff⟩
  | @unary k t U a _ _ _ ih =>
    obtain ⟨v, hv, hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · exact ⟨a, by simp, fun he => hd (by rw [bit_neg, bit_neg, he])⟩
    · exact ⟨v, Finset.mem_insert_of_mem hu, hd⟩
  | @binary k t U a b d _ _ _ _ _ ih =>
    obtain ⟨v, hv, hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · exact ⟨b, by simp, fun beq => hd (by rw [bit_bin, bit_bin, aeq, beq])⟩
      · exact ⟨a, by simp, aeq⟩
    · exact ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu), hd⟩

theorem raw_required {T k t S} (h : Live T k t S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v, hv, hd⟩ := live_row_difference h diff
  by_cases veq : v = a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig :=
  [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
   0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
   0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
   0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
   0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
   0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
   0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]

def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 8).filterMap fun i => if m.testBit i then some (i, inputs.getD i zero) else none
def vars (m : Nat) : List Sig := (selected m).map Prod.snd
def vertex (m j : Nat) : Sig := if m.testBit j then inputs.getD j zero else zero

def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) |||
  (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 3 &&& x 6) |||
  (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) |||
  (x 5 &&& x 7) ||| (x 6 &&& x 7)

def rename (f : Row → Row) (a : Sig) : Sig := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_neg (f : Row → Row) (a : Sig) : rename f (neg a) = neg (rename f a) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  change bit ⟨j, hj⟩ (rename f (neg a)) = bit ⟨j, hj⟩ (neg (rename f a))
  rw [bit_rename, bit_neg, bit_neg, bit_rename]
theorem rename_bin (f : Row → Row) (d : Bool) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  change bit ⟨j, hj⟩ (rename f (bin d a b)) = bit ⟨j, hj⟩ (bin d (rename f a) (rename f b))
  rw [bit_rename, bit_bin, bit_bin, bit_rename, bit_rename]
theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  obtain ⟨r, hr⟩ := onto ⟨j, hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j, hj⟩ a = bit ⟨j, hj⟩ b
  rw [bit_rename, bit_rename, hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j, hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j, hj⟩).symm)
  · exact (bit_rename f one ⟨j, hj⟩).trans ((bit_one _).trans (bit_one ⟨j, hj⟩).symm)

theorem live_rename {T k t S} (h : Live T k t S) (f : Row → Row) (onto : Function.Surjective f) :
    Live (rename f T) k t (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz, fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)), fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @unary k t U a hp hf _ ih =>
    have fresh : rename f (neg a) ∉ (insert a U).image (rename f) := by
      intro hm; obtain ⟨v, hv, eq⟩ := Finset.mem_image.mp hm; exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert, rename_neg] at fresh ih ⊢
    exact Live.unary (pp _ hp) fresh ih
  | @binary k t U a b d ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm; obtain ⟨v, hv, eq⟩ := Finset.mem_image.mp hm; exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert, rename_bin] at fresh ih ⊢
    exact Live.binary (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {T k t S} (h : Live T k t S) (none : t = 0) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h with
  | stop _ => exact ⟨_, by simp, pos, negRow⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d _ _ _ _ _ ih =>
    obtain ⟨v, hv, hp, hn⟩ := ih none
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      cases d <;> cases p : bit r a <;> cases q : bit s a <;>
        cases u : bit r b <;> cases z : bit s b <;> simp_all
    · exact ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu), hp, hn⟩

def Lower1 (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p t bank, t ≤ 1 → Reach (roots.map observe) p t bank → Available bank (observe T) → L + t ≤ p

def Impossible1 (T : Sig) (cap remNot : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live T k remNot S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower1_impossible {roots T L} (hp : proper T)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (no0 : Impossible1 T L 0 roots.toFinset)
    (no1 : Impossible1 T (L + 1) 1 roots.toFinset) : Lower1 roots T (L + 1) := by
  intro p t0 bank ht0 h ha
  obtain ⟨k, t, S, hk, ht, run, hs⟩ := reach_live hp h ha
  have he : roots.toFinset = S := by
    ext a; rw [List.mem_toFinset]
    refine ⟨fun hm => ?_, hs a⟩
    obtain ⟨r, s, hd, iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  have ht1 : t = 0 ∨ t = 1 := by omega
  rcases ht1 with rfl | rfl
  · exact no0 k (by omega) (he.symm ▸ run)
  · exact no1 k (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b, h⟩
  have hr : represented ([] : List Sig) v := by
    have avail : Available ([] : List (Wire Row)) (observe v) := Or.inr ⟨b, h⟩
    simpa only [List.map_nil, table_observe] using available_rep avail
  exact (hr.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a ++ b) = mass a + mass b := by simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons, List.length_cons, cost, if_pos ha, ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower1_slice {roots other : List Sig} {T G : Sig} (pT : proper T) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower1 other G L) : Lower1 roots T (L + singles.card) := by
  classical
  intro p t0 bank ht0 hh ha
  obtain ⟨k, t, S, hk, ht, run, sub⟩ := reach_live pT hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i, j, hd, hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front, List.nodup_append]
    refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, ?_⟩
    intro a ha b hb he; subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset = S := by ext a; simp [front, Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, hmem, rfl⟩ := List.mem_map.mp hm
    rw [← observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (by omega) (L := L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front, List.map_append, mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, hmem, rfl⟩ := List.mem_map.mp hm
      rw [← observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs, List.length_map, Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]; omega
  omega

def childOne (ws : List Sig) (a : Sig) (keep : Bool) : List Sig :=
  neg a :: kept keep a (ws.erase a)
def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) :
    (l.erase a).toFinset = l.toFinset.erase a := by
  ext x; simp [h.mem_erase_iff]

theorem enum_step1 {T : Sig} {cap remNot : Nat} {ws : List Sig} (hrem1 : remNot ≤ 1)
    (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : remNot = 1 → ∀ a ∈ ws, ∀ keep, neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      Impossible1 T (cap - 1) 0 (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length + remNot ≤ cap →
      Impossible1 T (cap - 1) remNot (childTwo ws a b d ka kb).toFinset) :
    Impossible1 T cap remNot ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  cases h with
  | stop _ =>
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  | @unary k t U a ha hf tail =>
    have ht0 : t = 0 := by omega
    subst ht0
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let keep := decide (a ∈ U)
    have er := erase_fin hn a
    have rest : (kept keep a (ws.erase a)).toFinset = U := by
      rw [kept_fin, er, he]; by_cases hm : a ∈ U <;> simp [keep, hm]
    have nd : (childOne ws a keep).Nodup := by
      have na : a ∉ ws.erase a := hn.not_mem_erase
      have nk := kept_nd keep a (ws.erase a) (hn.erase _) na
      refine List.nodup_cons.mpr ⟨?_, nk⟩
      intro h; exact hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h))
    have eq : (childOne ws a keep).toFinset = insert (neg a) U := by simp [childOne, rest]
    have sc := (live_size tail).2
    have len : (childOne ws a keep).length ≤ cap := by
      rw [← List.toFinset_card_of_nodup nd, eq]; omega
    exact oneStep rfl a am keep fresh hz len k (by omega) (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest = (ws.erase a).erase b by rfl, erase_fin (hn.erase _) b, erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin, kept_fin, er, he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j = a <;>
        by_cases jb : j = b <;> simp_all [ka, kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => hn.not_mem_erase (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept, ar, hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_, kept_nd ka a _ nk ax⟩
      intro h; exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b :: kept ka a (kept kb b rest)).toFinset = _; simp [ke]
    have sc := (live_size tail).2
    have len : (childTwo ws a b d ka kb).length + remNot ≤ cap := by
      rw [← List.toFinset_card_of_nodup nd, eq]; omega
    exact twoStep a am b bm d ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a :: ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered, BitVec.getLsbD_or, Bool.or_eq_true, ih, List.mem_cons, exists_eq_or_imp]

theorem cover_sound {T k t S} (h : Live T k t S) {ws : List Sig} (he : ws.toFinset = S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented = true → t = 0) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j, hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj, decide_true]
  apply (covered_bit (i := i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a, ha, hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes, no])
    refine ⟨a, List.mem_toFinset.mp (he.symm ▸ ha), ?_⟩
    simp only [column, Bool.false_eq_true, ite_false, BitVec.getLsbD_xor, (correct.2 a i).1, (correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a, ha, hp, hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a, List.mem_toFinset.mp (he.symm ▸ ha), ?_⟩
    simp only [column, ite_true, BitVec.getLsbD_and, BitVec.getLsbD_not, i.isLt, decide_true,
      Bool.true_and, (correct.2 a i).1, (correct.2 a i).2, hp, hn, Bool.not_false, Bool.and_self]

def Slice1 (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p t bank, t ≤ 1 → Reach (roots.map observe) p t bank →
      Available bank (restrictRows f (observe T)) → L + t ≤ p

def masked (d a : Sig) : Sig := a &&& d
def availableM (d : Sig) (mpool : List Sig) (a : Sig) : Bool :=
  let m := masked d a
  m == zero || m == d || mpool.any (fun v => v == m)

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit, masked, BitVec.getLsbD_and, show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit, masked, BitVec.getLsbD_and, show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit, masked, BitVec.getLsbD_and, show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupplyM (f : Row → Row) (d : Sig) (bank : List (Wire Row)) (mpool : List Sig) : Prop :=
  ∀ m ∈ mpool, ∃ a : Sig, masked d a = m ∧ Available bank (restrictRows f (observe a))

theorem availableM_sound {f : Row → Row} {d a : Sig} {bank mpool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupplyM f d bank mpool)
    (check : availableM d mpool a = true) : Available bank (restrictRows f (observe a)) := by
  simp only [availableM, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at check
  rcases check with (hz | ho) | ⟨m, hm, he⟩
  · exact Or.inr ⟨false, masked_zero dom hz⟩
  · exact Or.inr ⟨true, masked_one dom ho⟩
  · obtain ⟨v, hvm, hav⟩ := supplyB m hm
    exact masked_eq dom (hvm.trans he) ▸ hav

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) : Sig :=
  if c.1 = 2 then neg c.2.1 else bin (c.1 == 1) c.2.1 c.2.2
def choiceOK (d : Sig) (mpool : List Sig) (c : Choice) : Bool :=
  availableM d mpool c.2.1 && (c.1 == 2 || availableM d mpool c.2.2)
def choiceNot (c : Choice) : Nat := if c.1 == 2 then 1 else 0

theorem pay_choice {f : Row → Row} {d : Sig} {roots bank mpool q t}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach roots q t bank) (hs : poolSupplyM f d bank mpool)
    (c : Choice) (valid : choiceOK d mpool c = true) :
    ∃ next, Reach roots (q + 1) (t + choiceNot c) next ∧
      poolSupplyM f d next (masked d (choiceVal c) :: mpool) := by
  have ok : availableM d mpool c.2.1 = true ∧ (c.1 == 2 || availableM d mpool c.2.2) = true := by
    simpa only [choiceOK, Bool.and_eq_true] using valid
  have ha := availableM_sound dom hs ok.1
  let z := restrictRows f (observe (choiceVal c))
  have hz : Reach roots (q + 1) (t + choiceNot c) (z :: bank) := by
    by_cases unary : c.1 = 2
    · change Reach _ _ (t + choiceNot c) (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal, if_pos unary, obs_neg, choiceNot, show (c.1 == 2) = true by simp [unary], if_pos rfl]
      exact Reach.one hp ha
    · have hb : availableM d mpool c.2.2 = true := by simpa [unary] using ok.2
      have hz' := Reach.two (c.1 == 1) hp ha (availableM_sound dom hs hb)
      change Reach _ _ (t + choiceNot c) (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal, if_neg unary, obs_bin, choiceNot, show (c.1 == 2) = false by simp [unary], if_neg Bool.false_ne_true, Nat.add_zero]
      have comm (b : Bool) (v w : Wire Row) :
          restrictRows f (combine b v w) = combine b (restrictRows f v) (restrictRows f w) := by
        cases b <;> rfl
      rw [comm]
      exact hz'
  refine ⟨_, hz, ?_⟩
  intro m hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact ⟨choiceVal c, rfl, Or.inl (by simp [z])⟩
  · obtain ⟨v, hv, hav⟩ := hs m hm
    exact ⟨v, hv, available_cons _ hav⟩

def makePool (d : Sig) (mpool : List Sig) (nots : Nat) : List Choice → Option (List Sig × Nat)
  | [] => some (mpool, nots)
  | c :: cs => if choiceOK d mpool c then makePool d (masked d (choiceVal c) :: mpool) (nots + choiceNot c) cs else none

theorem makePool_sound {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q t mpool} (hp : Reach roots q t bank) (hs : poolSupplyM f d bank mpool)
    (cs : List Choice) {resM resN} (ok : makePool d mpool t cs = some (resM, resN)) :
    ∃ next, Reach roots (q + cs.length) resN next ∧ poolSupplyM f d next resM := by
  induction cs generalizing bank q t mpool with
  | nil => cases ok; exact ⟨_, hp, hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next, hr, sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out, hr', sh'⟩ := ih hr sh ok
      exact ⟨out, by simpa [Nat.add_assoc, Nat.add_comm 1] using hr', sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) : Bool := masked d a == zero || masked d a == d

theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons, List.map_cons, mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by
          simpa only [isMaskedConstant, Bool.or_eq_true, beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false, masked_zero dom hz⟩
        · exact ⟨true, masked_one dom ho⟩
      simpa [cost, hc, Nat.add_comm] using Nat.succ_le_succ ih

theorem raw_supplyM {f : Row → Row} {d : Sig} {roots raw : List Sig}
    (base : ∀ a ∈ raw, Available (roots.map observe) (restrictRows f (observe a))) :
    poolSupplyM f d (roots.map observe) (raw.map (masked d)) := by
  intro m hm
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
  exact ⟨a, rfl, base a ha⟩

def poolCut (d : Sig) (L cap paid nots : Nat) (raw ws : List Sig) : Bool :=
  decide (cap + paid < L + ws.countP (isMaskedConstant d)) &&
  decide (nots + 1 ≤ 1) &&
  ws.all (availableM d (raw.map (masked d)))

theorem poolCut_sound {raw T d L} (slice : Slice1 raw T d L)
    {ws cap remNot} (hrem : remNot ≤ 1) (nd : ws.Nodup)
    (cut : poolCut d L cap 0 0 raw ws = true) :
    Impossible1 T (cap + remNot) remNot ws.toFinset := by
  intro k hk h
  obtain ⟨f, roots, dom, base, nc, lo⟩ := slice
  simp only [poolCut, Bool.and_eq_true, decide_eq_true_eq] at cut
  obtain ⟨⟨ineq, _⟩, all⟩ := cut
  have hs := raw_supplyM (d := d) base
  have coveredS : supply (roots.map observe) ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
    exact availableM_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc Reach.start coveredS (by omega) lo
  have massLo := count_constants dom ws
  omega

abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 256 - d.val then ⟨d.val + r.val, by omega⟩ else ⟨r.val - (256 - d.val), by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 256 (256 - d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) : Sig := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) : Sig :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 256 - d.val <;> simp [shifted, h, r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit, mux, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, r.isLt,
    decide_true, Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove, bit_mux, bit_shift, rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) : Row := ms.foldr rowMove r
def movedWord (ms : List Move) (a : Sig) : Sig := ms.foldl (fun w m => wordMove m w) a

theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing a with
  | nil => rfl
  | cons m ms ih => exact (ih (wordMove m a)).trans (bit_move _ m a)

theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  exact (bit_moved ms a ⟨j, hj⟩).trans (bit_rename _ _ ⟨j, hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) : Bool := w == zero || w == one || roots.contains w
theorem freeWord_ok {roots w} (ok : freeWord roots w = true) :
    Available (roots.map observe) (observe w) := by
  simp only [freeWord, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr ⟨false, funext bit_zero⟩
  · exact Or.inr ⟨true, funext bit_one⟩
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) : Bool :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, moved_eq_rename] at ok
  exact ⟨ok.1, fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower1_map {ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (pG : proper G) (hL : Lower1 base G L) : Lower1 raw T L := by
  obtain ⟨eq, supp⟩ := map_correct ok
  simpa using lower1_slice pT pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice1_correct {ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower1 base G L) :
    Slice1 raw T d L := by
  obtain ⟨eq, supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms, base, ?_, ?_, ?_, ?_⟩
  · intro r; rw [← bit_moved, all, bit_one]
  · intro a ha; rw [← observe_rename]; exact supp a ha
  · rw [obs]; exact observe_proper properG
  · rw [obs]; exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) : Bool :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB, Bool.and_eq_true, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at ok
  exact ⟨rs.1, rs.2, ok.1, fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) : Bool :=
  xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  intro a ha
  obtain ⟨⟨a, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok _ hm)

theorem lower1_count {raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower1 raw T ((xs.map Prod.fst).toFinset.card - 1) := by
  intro p t0 bank ht0 hr hit
  obtain ⟨k, t, S, hk, ht, run, sub⟩ := reach_live properT hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r, s, hd, iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have ⟨htk, bound⟩ := live_size run
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) : Bool :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift1_ok {ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower1 base G L) :
    Lower1 raw T (L + (xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift, Bool.and_eq_true] at ok
  obtain ⟨eq, supp⟩ := map_correct ok.1.1
  apply lower1_slice properT properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true, beq_iff_eq, moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]; exact ⟨false, funext bit_zero⟩
  · rw [h]; exact ⟨true, funext bit_one⟩

def subcube (z o : Nat) : Sig :=
  if z &&& o != 0 then zero
  else (List.range 8).foldl (fun acc j =>
    if z.testBit j then acc &&& ~~~(inputs.getD j zero)
    else if o.testBit j then acc &&& inputs.getD j zero
    else acc) one

def fixRows (z o : Nat) : List Move :=
  (List.range 8).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 256 (1 <<< j)
    if z.testBit j then some (zero, x, step)
    else if o.testBit j then some (~~~x, zero, step) else none

def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j) - (1 <<< i)
  (a &&& ~~~b, b &&& ~~~a, Fin.ofNat 256 d)

def supportPairs (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i, a) => (a, 0, Fin.ofNat 256 (1 <<< i))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i, a) =>
    let r := 1 <<< ((hints >>> (4 * i)) &&& 15)
    (a, Fin.ofNat 256 r, Fin.ofNat 256 (r ||| (1 <<< i)))

def properB (T : Sig) : Bool := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB, proper, Bool.and_eq_true, bne_iff_ne] using h

def assertSize (m hints L : Nat) : Bool :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card - 1)
theorem size_of {m hints L} (h : assertSize m hints L = true) :
    Lower1 (vars m) (graphGoal m) L := by
  simp only [assertSize, Bool.and_eq_true, decide_eq_true_eq] at h
  intro p t bank ht hr ha
  have := lower1_count (proper_of _ h.1.1) _ h.1.2 p t bank ht hr ha
  omega

abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) : Nat := m ^^^ (m &&& (z ||| o))

def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z, o, q, s, L) := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (graphGoal m)
  let xs := supportPairs s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (vars m) (graphGoal m) (vars free) G &&
    (movedWord ms (subcube z o) == one) &&
    (if q = 0 then checkEssential G (vars free) xs && decide (L ≤ count - 1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q + count))

theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower1 (vars q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice1 (vars m) (graphGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  obtain ⟨z, o, q, s, L⟩ := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (graphGoal m)
  let xs := supportPairs s
  change (((properB G && checkMap ms (vars m) (graphGoal m) (vars free) G) &&
    (movedWord ms (subcube z o) == one)) && _) = true at ok
  simp only [Bool.and_eq_true, beq_iff_eq] at ok
  apply slice1_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p t bank ht hr ha
  have hh := ok.2
  by_cases hq : q = 0
  · simp only [colCheck, hq, if_true, Bool.and_eq_true, decide_eq_true_eq] at hh
    have := lower1_count (proper_of _ ok.1.1.1) xs hh.1 p t bank ht hr ha
    dsimp only [xs] at this ⊢; omega
  · simp only [colCheck, hq, if_false, Bool.and_eq_true, decide_eq_true_eq] at hh
    have := lift1_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p t bank ht hr ha
    dsimp only at this ⊢; omega

def relabelOK (old rep : Nat) (swaps : List Nat) : Bool :=
  properB (graphGoal old) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (vars old) (graphGoal old) (vars rep) (graphGoal rep)
theorem relabel_of {old rep L swaps} (ok : relabelOK old rep swaps = true)
    (h : Lower1 (vars rep) (graphGoal rep) L) : Lower1 (vars old) (graphGoal old) L := by
  simp only [relabelOK, Bool.and_eq_true] at ok
  exact lower1_map ok.2 (proper_of _ ok.1.1) (proper_of _ ok.1.2) h

private lemma reach_not_le {R} {roots : List (Wire R)} {p t bank} (h : Reach roots p t bank) : t ≤ p := by
  induction h with
  | start => omega
  | one _ _ ih => omega
  | two _ _ _ _ ih => omega

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) : Nat :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower1 (vars e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower1 (vars q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ hr _ => by simpa using reach_not_le hr
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true :=
      List.find?_some (p := fun a : Nat × Nat => a.1 == q) (a := e) h
    have eq : e.1 = q := beq_iff_eq.mp hit
    simpa only [Option.map_some, Option.getD_some, eq] using sound e he

structure BoundPool where
  domain : Sig
  bound : Nat
  paid : Nat
  nots : Nat
  mwires : List Sig

def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q u ws, u ≤ 1 → Reach (roots.map observe) q u ws →
      Available ws (restrictRows f (observe T)) → c.bound + u ≤ q) ∧
    Reach (roots.map observe) c.paid c.nots bank ∧ poolSupplyM f c.domain bank c.mwires

theorem build_valid {raw T d lb} (h : Slice1 raw T d lb) (cs : List Choice) {ms nots}
    (build : makePool d (raw.map (masked d)) 0 cs = some (ms, nots)) :
    ValidPool raw T ⟨d, lb, cs.length, nots, ms⟩ := by
  obtain ⟨f, roots, dom, sup, nc, prior⟩ := h
  obtain ⟨bank, hr, hs⟩ := makePool_sound dom (Reach.start (roots := roots.map observe))
    (raw_supplyM (d := d) sup) cs build
  exact ⟨f, roots, bank, dom, nc, prior, by simpa using hr, hs⟩

theorem valid_exclude {raw T c} (valid : ValidPool raw T c) (k remNot : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableM c.domain c.mwires a = true)
    (buy : if paid then choiceOK c.domain c.mwires choice = true
       else availableM c.domain c.mwires (choiceVal choice) = true)
    (notsOK : c.nots + (if paid then choiceNot choice else 0) + remNot ≤ 1)
    (bound : k + c.paid + paid.toNat <
      c.bound + (c.nots + (if paid then choiceNot choice else 0) + remNot) +
        (choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible1 T k remNot (choiceVal choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f, roots, bank, dom, nc, lo, hp, hs⟩ := valid
  let ws := choiceVal choice :: rest
  have done (n u : Nat) (out : List (Wire Row)) (reach : Reach (roots.map observe) n u out)
      (zs : ∀ a ∈ choiceVal choice :: rest, Available out (restrictRows f (observe a)))
      (le : n = c.paid + paid.toNat)
      (eu : u = c.nots + (if paid then choiceNot choice else 0)) (lu : u + remNot ≤ 1) : False := by
    have covered : supply out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lu lo
    have cm := count_constants dom ws
    change k + c.paid + paid.toNat <
      c.bound + (c.nots + (if paid then choiceNot choice else 0) + remNot) + ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ _ hp _ rfl (by simp) (by simpa using notsOK)
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableM_sound dom hs buy
    · exact availableM_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out, hr, hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ _ hr _ rfl (by simp) (by simpa using notsOK)
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · obtain ⟨v, hv, hav⟩ := hc (masked c.domain (choiceVal choice)) (by simp)
      exact masked_eq dom hv ▸ hav
    · have avail := availableM_sound dom hs (known _ hm)
      rcases avail with mem | con
      · have point : poolSupplyM f c.domain out c.mwires :=
          fun u hu => hc u (List.mem_cons_of_mem _ hu)
        exact availableM_sound dom point (known _ hm)
      · exact Or.inr con

def scalarPoolCut (c : BoundPool) (k remNot : Nat) (rest : List Sig) (op : Choice) : Bool :=
  if c.nots + remNot > 1 then false else
  if k + c.paid >= c.bound + 1 + rest.length + 1 then false else
  let z := choiceVal op
  let extra := !(availableM c.domain c.mwires z)
  let totNot := c.nots + (if extra then choiceNot op else 0) + remNot
  decide (totNot ≤ 1) &&
  decide (k + c.paid + extra.toNat < c.bound + totNot + (z :: rest).countP (isMaskedConstant c.domain)) &&
  rest.all (availableM c.domain c.mwires) &&
  (!extra || choiceOK c.domain c.mwires op)

theorem scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k remNot rest op}
    (nd : (choiceVal op :: rest).Nodup) (cut : scalarPoolCut c k remNot rest op = true) :
    Impossible1 T k remNot (choiceVal op :: rest).toFinset := by
  let extra := !(availableM c.domain c.mwires (choiceVal op))
  unfold scalarPoolCut at cut
  split at cut; · contradiction
  split at cut; · contradiction
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at cut
  apply valid_exclude valid k remNot rest op extra cut.1.2 _ cut.1.1.1 cut.1.1.2 nd
  cases he : availableM c.domain c.mwires (choiceVal op) <;> simp_all [extra]

def materialize (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool d (raw.map (masked d)) 0 cs).map (fun (ms, nots) => ⟨d, lb, cs.length, nots, ms⟩)

theorem materialize_sound {raw T d L cs c} (slice : Slice1 raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  cases he : makePool d (raw.map (masked d)) 0 cs with
  | none => simp [he] at h
  | some p =>
    simp only [he, Option.map_some, Option.some.injEq] at h
    subst c
    exact build_valid slice cs he

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 192 → Row) (a : Sig) : Signals := (ofRows r a, ofRows s a)
def properPairs (T : Sig) (r s : Fin 192 → Row) : Prop :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 192 r s (pairSig r s) :=
  ⟨h, fun a i => ⟨ofRows_bit _ _ _, ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 192 → Row) (x : Decor) : Prop := x.2 = pairSig r s x.1
def dneg (x : Decor) : Decor := (neg x.1, ~~~x.2.1, ~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1, x.2.1 ||| y.2.1, x.2.2 ||| y.2.2)
  else (bin d x.1 y.1, x.2.1 &&& y.2.1, x.2.2 &&& y.2.2)

theorem ofRows_neg (r : Fin 192 → Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have h := ofRows_bit r (neg a) ⟨j, hj⟩
  rw [bit_neg, ← ofRows_bit r a ⟨j, hj⟩] at h
  simpa only [BitVec.getLsbD_not, hj, decide_true, Bool.true_and] using h

theorem ofRows_bin (r : Fin 192 → Row) (d : Bool) (a b : Sig) :
    ofRows r (bin d a b) = if d then ofRows r a ||| ofRows r b else ofRows r a &&& ofRows r b := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j, hj⟩
  rw [bit_bin, ← ofRows_bit r a ⟨j, hj⟩, ← ofRows_bit r b ⟨j, hj⟩] at h
  cases d <;> simpa only [Bool.false_eq_true, ite_false, ite_true, BitVec.getLsbD_and, BitVec.getLsbD_or] using h

theorem faithful_neg {r s x} (h : faithful r s x) : faithful r s (dneg x) := by
  change x.2 = _ at h; simp only [faithful, dneg, pairSig, ofRows_neg, h]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx; change y.2 = _ at hy
  cases d <;> simp only [faithful, dbin, Bool.false_eq_true, ite_false, ite_true, pairSig, ofRows_bin, hx, hy]

def codeDecor (op : Nat) (x y : Decor) : Decor := if op = 2 then dneg x else dbin (op == 1) x y
def defaultDecor : Decor := (zero, 0, 0)
theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j, hj⟩) zero from ofRows_bit _ _ ⟨j, hj⟩, bit_zero]; simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j, hj⟩) zero from ofRows_bit _ _ ⟨j, hj⟩, bit_zero]; simp

theorem faithful_get {r s} {ws : List Decor} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (ws.getD i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)

def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k + 1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws ++ [codeDecor ((bits >>> 8) &&& 3) a b])

def codeSig (op : Nat) (x y : Sig) : Sig := if op = 2 then neg x else bin (op == 1) x y
def decodeSig (n : Nat) (bits : Nat) (ws : List Sig) : List Sig :=
  match n with
  | 0 => ws
  | k + 1 =>
    let a := ws.getD (bits &&& 15) zero
    let b := ws.getD ((bits >>> 4) &&& 15) zero
    decodeSig k (bits >>> 10) (ws ++ [codeSig ((bits >>> 8) &&& 3) a b])

theorem decodeBank_fst (n bits : Nat) (ws : List Decor) :
    (decodeBank n bits ws).map Prod.fst = decodeSig n bits (ws.map Prod.fst) := by
  induction n generalizing ws bits with
  | zero => rfl
  | succ k ih =>
    simp only [decodeBank, decodeSig, ih, List.map_append, List.map_cons, List.map_nil]
    have hg (i : Nat) : (ws.getD i defaultDecor).1 = (ws.map Prod.fst).getD i zero := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_map]; cases ws[i]? <;> rfl
    have hc (op : Nat) (a b : Decor) : (codeDecor op a b).1 = codeSig op a.1 b.1 := by
      unfold codeDecor codeSig; split
      · rfl
      · cases (op == 1) <;> rfl
    rw [hc, hg, hg]

theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ decodeBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih; intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      unfold codeDecor; split
      · exact faithful_neg (faithful_get base _)
      · exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 192) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 8 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])

theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel

theorem input_coords : ∀ (j : Fin 8) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r; fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r

theorem asRow_bit (cols : Nat → Bits) (i : Fin 192) (j : Fin 8) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 8 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [j.isLt]

def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j, a) => (a, p j, q j))

theorem selected_entry {m j a} (h : (j, a) ∈ selected m) : j < 8 ∧ a = inputs.getD j zero := by
  obtain ⟨v, hv, hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next => cases hh; exact ⟨hv, rfl⟩
  next => contradiction

theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j, v⟩, hv, rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj, rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i, hi⟩ ⟨j, hj⟩).symm.trans (ofRows_bit _ _ ⟨i, hi⟩).symm
  · exact (asRow_bit q ⟨i, hi⟩ ⟨j, hj⟩).symm.trans (ofRows_bit _ _ ⟨i, hi⟩).symm

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) |||
  (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 3 &&& x 6) |||
  (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) |||
  (x 5 &&& x 7) ||| (x 6 &&& x 7)

theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 192) (j : Fin 8) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex, hh] using asRow_bit v i j
  · simp [vertex, hh, bit_zero]

theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 192) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j < 8) :
      (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val :=
    bit_vertex m v i ⟨j, hj⟩
  simp only [bit, graphGoal, liftGoal, BitVec.getLsbD_and, BitVec.getLsbD_or]
  simp only [pos 0 (by decide), pos 1 (by decide), pos 2 (by decide), pos 3 (by decide),
    pos 4 (by decide), pos 5 (by decide), pos 6 (by decide), pos 7 (by decide)]

theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : liftGoal m p = BitVec.allOnes 192) (hq : liftGoal m q = 0) :
    properPairs (graphGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [bit_liftGoal, hp, hq, BitVec.getLsbD_allOnes, i.isLt, decide_true, BitVec.getLsbD_zero]
  simp

abbrev Cov := Bits × Bits × Bits
def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z), (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))
def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0, 0, 0)
def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a = c.1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [takeOne, addCov, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b = c.1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [takeTwo, addCov, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c) = addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [addCov, BitVec.getLsbD_or]; cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l = coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b _ => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2

theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2 = pairSig r s a.1 from good _ (by simp), ih (fun a ha => good a (by simp [ha]))]

def delOne (ws : List Decor) (a : Decor) (keep : Bool) : List Decor := if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) : List Decor := delOne (delOne ws a ka) b kb
theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) : ws.Perm (a :: ws.erase a) :=
  List.perm_cons_erase ha
theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]; exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ws.Perm (a :: b :: (ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))
theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]; exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl

def sameWords (a b : List Sig) : Bool := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset = ys.toFinset := by
  simp only [sameWords, Bool.and_eq_true, List.all_eq_true, List.contains_eq_mem, decide_eq_true_eq] at h
  ext a; simp only [List.mem_toFinset]; exact ⟨h.1 a, h.2 a⟩

def sameWords1 (a b : List Sig) : Bool := a.length == b.length && a.all (fun x => b.contains x)
theorem sameWords1_sound {xs ys} (nd : xs.Nodup) (h : sameWords1 xs ys = true) : xs.toFinset = ys.toFinset := by
  simp only [sameWords1, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_eq_mem, decide_eq_true_eq] at h
  have hsub : xs.toFinset ⊆ ys.toFinset := fun a ha => List.mem_toFinset.mpr (h.2 a (List.mem_toFinset.mp ha))
  have hcard : ys.toFinset.card ≤ xs.toFinset.card := by
    rw [List.toFinset_card_of_nodup nd, h.1]; exact List.toFinset_card_le ys
  exact Finset.eq_of_subset_of_card_le hsub hcard

def keyWord (v : Sig) : Nat :=
  let n := v.toNat % 2305843009213693951
  (n * (n + 971)) % 2305843009213693951
def keySet (xs : List Sig) : Nat := xs.foldl (fun v x => v + keyWord x) 0
def sumKeys (xs : List Nat) : Nat := xs.foldl (· + ·) 0

theorem sumKeys_map (ws : List Decor) : sumKeys (ws.map (fun w => keyWord w.1)) = keySet (ws.map Prod.fst) := by
  simp [sumKeys, keySet, List.foldl_map]
theorem keySet_aux (xs : List Sig) (acc : Nat) :
    xs.foldl (fun v x => v + keyWord x) acc = acc + keySet xs := by
  induction xs generalizing acc with
  | nil => simp [keySet]
  | cons x xs ih =>
    simp only [List.foldl_cons, keySet, Nat.zero_add]
    rw [ih (acc + keyWord x), ih (keyWord x), Nat.add_assoc]
theorem keySet_cons (x : Sig) (xs : List Sig) : keySet (x :: xs) = keyWord x + keySet xs := by
  simpa [keySet] using keySet_aux xs (keyWord x)
theorem keySet_perm {xs ys : List Sig} (h : xs.Perm ys) : keySet xs = keySet ys := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [keySet_cons, ih]
  | swap x y l => simp only [keySet_cons]; omega
  | trans _ _ h1 h2 => exact h1.trans h2
theorem keySet_delOne {ws : List Decor} {a : Decor} (ha : a ∈ ws) (k : Bool) :
    keySet ((delOne ws a k).map Prod.fst) = keySet (ws.map Prod.fst) - (if k then 0 else keyWord a.1) := by
  cases k
  · have hp : (ws.map Prod.fst).Perm (a.1 :: (ws.erase a).map Prod.fst) := (delOne_perm a ha).map Prod.fst
    rw [keySet_perm hp, keySet_cons]; simp [delOne]
  · simp [delOne]

def closeChild (pools : List BoundPool) (links : Nat → List (List Sig)) (k remNot : Nat)
    (rest : List Sig) (op : Choice) : Bool :=
  let ws := choiceVal op :: rest
  pools.any (fun p => scalarPoolCut p k remNot rest op) || (links (keySet ws)).any (sameWords1 ws)

theorem closeChild_sound {raw T pools links k remNot rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible1 T k remNot xs.toFinset)
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k remNot rest op = true) :
    Impossible1 T k remNot (choiceVal op :: rest).toFinset := by
  simp only [closeChild, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with ⟨p, hp, ok⟩ | ⟨xs, hx, ok⟩
  · exact scalarPoolCut_sound (pValid _ hp) nd ok
  · rw [sameWords1_sound nd ok]; exact lValid _ _ hx

abbrev CovPair := Cov × Cov
def preCov (ws : List Decor) : CovPair := (coverage false ws, coverage true ws)
def getCov (c : CovPair) (d : Bool) : Cov := if d then c.2 else c.1
theorem get_preCov (ws) (d : Bool) : getCov (preCov ws) d = coverage d ws := by cases d <;> rfl
def restCov (v : Cov) (a b : Bits) (un ka kb : Bool) : Bits :=
  if un then (if ka then v.1 else takeOne v a)
  else if ka then (if kb then v.1 else takeOne v b)
  else if kb then takeOne v a else takeTwo v a b
def opKeep (un ka kb : Bool) (a b : Decor) (ws : List Decor) : List Decor :=
  if un then delOne ws a ka else delTwo ws a b ka kb

theorem rest_coverage {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (un ka kb d : Bool) (ne : un = false → a ≠ b) :
    (coverage d (opKeep un ka kb a b ws)).1 =
      restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) un ka kb := by
  rw [get_preCov]; cases un
  · exact cover_two d a b ha hb (ne rfl) ka kb
  · exact cover_one d a ha ka

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    (opKeep un ka kb a b ws).Sublist ws := by
  cases un
  · exact (delOne_sub _ _ _).trans (delOne_sub _ _ _)
  · exact delOne_sub _ _ _
theorem len_keep (ws : List Decor) (a b : Decor) (un ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : un = false → a ≠ b) :
    (opKeep un ka kb a b ws).length =
      ws.length - (if ka then 0 else 1) - (if un || kb then 0 else 1) := by
  cases un
  · have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm (ne rfl))).mpr hb
    cases ka <;> cases kb <;> simp [opKeep, delTwo, delOne, List.length_erase_of_mem ha, List.length_erase_of_mem hb, List.length_erase_of_mem hm]
  · cases ka <;> cases kb <;> simp [opKeep, delOne, List.length_erase_of_mem ha]

def movedDecor (op : Nat) (a b : Decor) : Decor := codeDecor op a b
def movedChoice (op : Nat) (a b : Decor) : Choice := (op, a.1, b.1)
theorem moved_full (op) (a b : Decor) : (movedDecor op a b).1 = choiceVal (movedChoice op a b) := by
  by_cases h : op = 2
  · simp [movedDecor, codeDecor, h, dneg, choiceVal, movedChoice]
  · cases hh : op == 1 <;> simp [movedDecor, codeDecor, h, hh, dbin, choiceVal, movedChoice]
theorem moved_faithful {r s a b} (ha : faithful r s a) (hb : faithful r s b) (op : Nat) :
    faithful r s (movedDecor op a b) := by
  unfold movedDecor codeDecor; split
  · exact faithful_neg ha
  · exact faithful_bin _ ha hb

def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) : Nat :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne, Bool.false_eq_true, ite_false, constantLoss, List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne, constantLoss]
theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b (un || kb) ≤
    (opKeep un ka kb a b ws).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  cases un <;> simp only [opKeep, delTwo, Bool.false_eq_true, ite_false, ite_true,
    Bool.false_or, Bool.true_or] <;> first | omega | simp [constantLoss]; omega

abbrev QuickPool := BoundPool × Nat × Bool
def summarizePool (ws : List Decor) (p : BoundPool) : QuickPool :=
  (p, ws.countP (fun w => isMaskedConstant p.domain w.1),
      ws.all (fun w => availableM p.domain p.mwires w.1))

def fastCost (s : QuickPool) (k remNot : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) : Bool :=
  if !s.2.2 then false else
  let p := s.1
  if k + p.paid >= p.bound + 1 + s.2.1 + 1 then false else
  if p.nots + remNot > 1 then false else
  let un := op == 2
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := codeSig op a.1 b.1
  let zm := masked p.domain z
  let zc := isMaskedConstant p.domain z
  let cm := s.2.1 - constantLoss const a ka - constantLoss const b (un || kb) + zc.toNat
  let free := zc || zm == masked p.domain a.1 || zm == masked p.domain b.1
  let totNot := p.nots + (if !free && un then 1 else 0) + remNot
  decide (totNot ≤ 1) && decide (k + p.paid + (!free).toNat < p.bound + totNot + cm)

theorem fastCost_good {p k remNot ws a b op ka kb} (ha : a ∈ ws) (hb : b ∈ ws)
    (h : fastCost (summarizePool ws p) k remNot a b op ka kb = true) :
    scalarPoolCut p k remNot ((opKeep (op == 2) ka kb a b ws).map Prod.fst) (movedChoice op a b) = true := by
  have hz : codeSig op a.1 b.1 = choiceVal (movedChoice op a b) := by
    unfold codeSig choiceVal movedChoice
    by_cases h2 : op = 2
    · simp [h2]
    · cases h1 : (op == 1) <;> simp [h2, h1]
  let z := choiceVal (movedChoice op a b)
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let free := isMaskedConstant p.domain z || masked p.domain z == masked p.domain a.1 ||
      masked p.domain z == masked p.domain b.1
  let rest := opKeep (op == 2) ka kb a b ws
  have ck : ws.countP const - constantLoss const a ka - constantLoss const b ((op == 2) || kb) ≤ rest.countP const :=
    keptCount const ws a b (op == 2) ka kb
  by_cases all : ws.all (fun w => availableM p.domain p.mwires w.1) = true
  · have hav := List.all_eq_true.mp all
    have ready : free = true → availableM p.domain p.mwires z = true := by
      intro f
      simp only [free, Bool.or_eq_true, beq_iff_eq] at f
      rcases f with (zc | za) | zb
      · simp only [availableM, isMaskedConstant, Bool.or_eq_true] at zc ⊢; exact Or.inl zc
      · have := hav _ ha; simp only [availableM] at this ⊢; rwa [za]
      · have := hav _ hb; simp only [availableM] at this ⊢; rwa [zb]
    have extra : (!availableM p.domain p.mwires z).toNat ≤ (!free).toNat := by
      cases hf : free <;> cases he : availableM p.domain p.mwires z <;> simp_all
    have notLe : (if !availableM p.domain p.mwires z then choiceNot (movedChoice op a b) else 0) ≤
        (if !free && (op == 2) then 1 else 0) := by
      cases hf : free <;> cases he : availableM p.domain p.mwires z <;>
        cases hu : (op == 2) <;> simp_all [choiceNot, movedChoice]
    have diffLe : (if !free && (op == 2) then 1 else 0) + (!availableM p.domain p.mwires z).toNat ≤
        (if !availableM p.domain p.mwires z then choiceNot (movedChoice op a b) else 0) + (!free).toNat := by
      cases hf : free <;> cases he : availableM p.domain p.mwires z <;>
        cases hu : (op == 2) <;> simp_all [choiceNot, movedChoice]
    have hs : (rest.map Prod.fst).all (availableM p.domain p.mwires) = true := by
      apply List.all_eq_true.mpr
      intro _ hm; obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hm
      exact hav w ((keep_sub ws a b (op == 2) ka kb).subset hw)
    have opOK : choiceOK p.domain p.mwires (movedChoice op a b) = true := by
      simp [choiceOK, movedChoice, hav _ ha, hav _ hb]
    simp only [fastCost, summarizePool, all, Bool.not_true, Bool.false_eq_true, ite_false, hz] at h
    split at h
    · contradiction
    split at h
    · contradiction
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    change p.nots + (if !free && (op == 2) then 1 else 0) + remNot ≤ 1 at h1
    change k + p.paid + (!free).toNat < p.bound + (p.nots + (if !free && (op == 2) then 1 else 0) + remNot) +
        (ws.countP const - constantLoss const a ka -
        constantLoss const b ((op == 2) || kb) + (isMaskedConstant p.domain z).toNat) at h2
    dsimp only [rest] at hs
    have hnot_le : ¬(p.nots + remNot > 1) := by omega
    have hcnt_le : rest.countP const ≤ rest.length := List.countP_le_length
    have hzc : (isMaskedConstant p.domain z).toNat = if isMaskedConstant p.domain z then 1 else 0 := by
      cases isMaskedConstant p.domain z <;> rfl
    have hzc1 : (isMaskedConstant p.domain z).toNat ≤ 1 := by
      cases isMaskedConstant p.domain z <;> decide
    have hbd_lt : ¬(k + p.paid ≥ p.bound + 1 + (rest.map Prod.fst).length + 1) := by
      rw [List.length_map]; omega
    unfold scalarPoolCut
    rw [if_neg hnot_le, if_neg hbd_lt]
    simp only [hs, opOK, Bool.or_true, Bool.and_true, Bool.and_eq_true,
      decide_eq_true_eq, List.countP_cons, List.countP_map, Function.comp_def]
    refine ⟨by change p.nots + (if !availableM p.domain p.mwires z then choiceNot (movedChoice op a b) else 0) + remNot ≤ 1; omega, ?_⟩
    change k + p.paid + (!availableM p.domain p.mwires z).toNat <
      p.bound + (p.nots + (if !availableM p.domain p.mwires z then choiceNot (movedChoice op a b) else 0) + remNot) +
      (rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
    omega
  · simp [fastCost, summarizePool, all] at h

theorem keySet_keep {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (un ka kb : Bool) (hne : un = false → a ≠ b) :
    keySet ((opKeep un ka kb a b ws).map Prod.fst) =
      keySet (ws.map Prod.fst) - (if ka then 0 else keyWord a.1) - (if un || kb then 0 else keyWord b.1) := by
  cases un
  · have hb' : b ∈ delOne ws a ka := by
      cases ka
      · exact (List.mem_erase_of_ne (Ne.symm (hne rfl))).mpr hb
      · exact hb
    simp only [opKeep, Bool.false_eq_true, ite_false, delTwo, Bool.false_or]
    rw [keySet_delOne hb' kb, keySet_delOne ha ka]
  · simp only [opKeep, ite_true, Bool.true_or, Nat.sub_zero]
    exact keySet_delOne ha ka

structure NodeContext where
  target : Sig
  lv : Nat
  arity : Nat
  ws : List Decor
  cov : CovPair
  pools : List BoundPool
  qpools : List QuickPool
  ksum : Nat
  wkeys : List Nat
  linksBin : Nat → List (List Sig)
  linksUn : Nat → List (List Sig)

def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let cap := c.lv / 2
  let remNot := c.lv % 2
  let un := op == 2
  if un && remNot == 0 then true else
  let nrem := if un then 0 else remNot
  let len := 1 + (c.arity - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len + nrem > cap then true else
  let d := nrem == 0
  let rs := restCov (getCov c.cov d) (column d a.2) (column d b.2) un ka kb
  if (rs ||| column d z.2) != BitVec.allOnes 192 then true else
  if !properB z.1 || c.ws.any (fun v => v.1 == z.1) then true else
  if cap == 1 then (nrem == 1) || (z.1 != c.target) else
    let rest := (opKeep un ka kb a b c.ws).map Prod.fst
    let ls := if un then c.linksUn else c.linksBin
    closeChild c.pools ls (cap - 1) nrem rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) : List Sig :=
  (movedDecor op a b).1 :: (opKeep (op == 2) ka kb a b ws).map Prod.fst

theorem evalMove_sound {raw T r s ws pools linksBin linksUn lv a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op == 2) = false → a ≠ b) (hcap : 0 < lv / 2)
    (hrem : (op == 2) = true → lv % 2 = 1)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lvBin : ∀ tag xs, xs ∈ linksBin tag → Impossible1 T (lv / 2 - 1) (lv % 2) xs.toFinset)
    (lvUn : lv % 2 = 1 → ∀ tag xs, xs ∈ linksUn tag → Impossible1 T (lv / 2 - 1) 0 xs.toFinset)
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove ⟨T, lv, ws.length, ws, preCov ws, pools, pools.map (summarizePool ws),
        sumKeys (ws.map (fun w => keyWord w.1)), ws.map (fun w => keyWord w.1), linksBin, linksUn⟩
      op a b (movedDecor op a b) ka kb = true) :
    Impossible1 T (lv / 2 - 1) (if op == 2 then 0 else lv % 2) (moveFront ws op a b ka kb).toFinset := by
  let cap := lv / 2
  let remNot := lv % 2
  let un := op == 2
  let nrem := if un then 0 else remNot
  let z := movedDecor op a b
  let rest := opKeep un ka kb a b ws
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm), nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1 == z.1) = false := by
    apply Bool.eq_false_iff.mpr; intro hh
    obtain ⟨x, hx, he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB, proper] using pro
  have leq : 1 + (ws.length - (if ka then 0 else 1) - (if un || kb then 0 else 1)) = child.length := by
    change _ = (z.1 :: rest.map Prod.fst).length
    rw [List.length_cons, List.length_map, len_keep _ _ _ _ _ _ ha hb ne, Nat.add_comm 1]
  have hun : (un && (remNot == 0)) = false := by
    cases hu : un
    · rfl
    · have := hrem hu; simp [remNot, this]
  intro k hk h
  have hsz := (live_size h).2
  change child.toFinset.card + nrem ≤ k + 1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length + nrem ≤ cap := by omega
  unfold evalMove at test
  dsimp only at test
  change (if un && (remNot == 0) then true else
    if 1 + (ws.length - (if ka then 0 else 1) - (if un || kb then 0 else 1)) + nrem > cap then true else _) = true at test
  rw [hun, if_neg Bool.false_ne_true, leq, if_neg (by omega)] at test
  let d := nrem == 0
  have sep := cover_sound h rfl (pair_sep pairs) d (fun hd => beq_iff_eq.mp hd)
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz := rest_coverage ha hb un ka kb d ne
  have hf := moved_faithful (faith _ ha) (faith _ hb) op
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [← hf, ← g, rz, BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) un ka kb ||| column d z.2) != BitVec.allOnes 192) = false := by simp [sep]
  change (if (_ != _) then true else if !properB z.1 || ws.any (fun v => v.1 == z.1) then true else _) = true at test
  rw [be, pp, fr] at test
  simp only [Bool.false_eq_true, ite_false, Bool.not_true, Bool.or_self] at test
  by_cases h1 : cap = 1
  · dsimp only [cap] at h1
    have h1t : (lv / 2 == 1) = true := beq_iff_eq.mpr h1
    rw [h1t] at test
    simp only [ite_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at test
    have hk0 : k = 0 := by omega
    subst hk0
    have ht0 : nrem = 0 := by have := (live_size h).1; omega
    have hne : z.1 ≠ T := test.resolve_left (by simp only [nrem, un, remNot, beq_iff_eq] at ht0; omega)
    have hclen : child.length = 1 := by
      have : 1 ≤ child.length := by simp [child]
      omega
    have h' : Live T 0 0 child.toFinset := by
      change Live T 0 nrem child.toFinset at h
      rwa [ht0] at h
    generalize heq : child.toFinset = S at h'
    cases h'
    have hmem : T ∈ child := List.mem_toFinset.mp (heq.symm ▸ Finset.mem_singleton_self _)
    cases hrest : rest.map Prod.fst with
    | nil => simp [child, hrest] at hmem; exact hne hmem.symm
    | cons _ _ => simp [child, hrest] at hclen
  · dsimp only [cap] at h1
    have h1f : (lv / 2 == 1) = false := beq_false_of_ne h1
    rw [h1f] at test
    simp only [Bool.false_eq_true, ite_false] at test
    have val := moved_full op a b
    change z.1 = _ at val
    change Live T k nrem (z.1 :: rest.map Prod.fst).toFinset at h
    have nd' := ndc
    change (z.1 :: rest.map Prod.fst).Nodup at nd'
    rw [val] at nd' h
    have hls : ∀ tag xs, xs ∈ (if un then linksUn else linksBin) tag → Impossible1 T (cap - 1) nrem xs.toFinset := by
      cases hu : un
      · simpa [nrem, hu, cap, remNot] using lvBin
      · simpa [nrem, hu, cap] using lvUn (hrem hu)
    exact closeChild_sound pv hls nd' test k hk h

def testPair (ctx : NodeContext) (a b : Decor) (d : Bool) : Bool :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true

def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) : Bool :=
  let z := movedDecor 2 a a
  (if ctx.lv % 2 == 0 then true else evalMove ctx 2 a a z false false && evalMove ctx 2 a a z true true) &&
    bs.all (fun b => testPair ctx a b false && testPair ctx a b true)

def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a :: bs => testRow ctx a bs && testAll ctx bs

theorem all_unary {ctx ws} (h : testAll ctx ws = true) (h1 : ctx.lv % 2 = 1)
    {a : Decor} (ha : a ∈ ws) (keep : Bool) :
    evalMove ctx 2 a a (movedDecor 2 a a) keep keep = true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll, Bool.and_eq_true, testRow, h1, Nat.reduceBEq, Bool.false_eq_true, ite_false] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · cases keep
      · exact h.1.1.1
      · exact h.1.1.2
    · exact ih h.2 hm

theorem all_binary {ctx ws} (h : testAll ctx ws = true) {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (d : Bool) : testPair ctx a b d = true ∨ testPair ctx b a d = true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll, Bool.and_eq_true, testRow, List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left; cases d <;> first | exact (h.1.2 b bm).1 | exact (h.1.2 b bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right; cases d <;> first | exact (h.1.2 a haTail).1 | exact (h.1.2 a haTail).2
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true := by
  simp only [testPair, Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w = a ∧ k = true) ∨ w ∈ v := by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w ∈ v ∧ (w ≠ a ∨ k = true) := by cases k <;> simp [delOne, nd.mem_erase_iff, and_comm]
theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (eq : a.1 = b.1) : a = b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn, ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail

theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (un ka kb : Bool) (v : Sig) :
    v ∈ (opKeep un ka kb a b ws).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v ≠ a.1 ∨ ka = true) ∧ (un = true ∨ v ≠ b.1 ∨ kb = true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  cases un <;> simp only [opKeep, Bool.false_eq_true, ite_false, ite_true, delTwo, List.mem_map,
    mem_delone wn, mem_delone dn, or_false, false_or, true_or, and_true] <;> constructor
  all_goals
    first
    | rintro ⟨w, hw, rfl⟩
      first
      | exact ⟨⟨_, hw.1.1, rfl⟩, hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
      | exact ⟨⟨_, hw.1, rfl⟩, hw.2.imp (fun ne eq => ne (unique_value nd hw.1 ha eq)) id⟩
    | rintro ⟨⟨w, hm, rfl⟩, h1, h2⟩
      exact ⟨w, ⟨⟨hm, h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩, rfl⟩
    | rintro ⟨⟨w, hm, rfl⟩, h1⟩
      exact ⟨w, ⟨hm, h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩, rfl⟩

theorem unary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a : Decor} (ha : a ∈ ws)
    (keep : Bool) :
    (moveFront ws 2 a a keep keep).toFinset = (childOne (ws.map Prod.fst) a.1 keep).toFinset := by
  ext v
  simp only [moveFront, childOne, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset,
    kept_value nd ha ha, keep_mem, nd.mem_erase_iff, movedDecor, codeDecor, dneg, ite_true,
    Nat.reduceBEq, true_or, and_true]
  have av := List.mem_map_of_mem (f := Prod.fst) ha
  by_cases e : v = a.1 <;> cases keep <;> simp_all

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a.1 ≠ b.1) (d ka kb : Bool) :
    (moveFront ws (if d then 1 else 0) a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f := Prod.fst) ha
  have bv := List.mem_map_of_mem (f := Prod.fst) hb
  cases d <;> simp only [moveFront, childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset,
    kept_value nd ha hb, keep_mem, (nd.erase _).mem_erase_iff, nd.mem_erase_iff, movedDecor, codeDecor, dbin,
    Bool.false_eq_true, Nat.reduceBEq, ite_true, ite_false, false_or]
  all_goals by_cases va : v = a.1 <;> by_cases vb : v = b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap (v : List Sig) (nd : v.Nodup) (a b : Sig) (d ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a d kb ka).toFinset := by
  ext x
  simp only [childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset,
    keep_mem, (nd.erase _).mem_erase_iff, nd.mem_erase_iff, bin_comm d b a]
  tauto

theorem node_sound {raw T r s ws pools linksBin linksUn lv}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lvBin : 0 < lv / 2 → ∀ tag xs, xs ∈ linksBin tag → Impossible1 T (lv / 2 - 1) (lv % 2) xs.toFinset)
    (lvUn : 0 < lv / 2 → lv % 2 = 1 → ∀ tag xs, xs ∈ linksUn tag → Impossible1 T (lv / 2 - 1) 0 xs.toFinset)
    (checks : lv / 2 = 0 ∨ testAll ⟨T, lv, ws.length, ws, preCov ws, pools, pools.map (summarizePool ws),
        sumKeys (ws.map (fun w => keyWord w.1)), ws.map (fun w => keyWord w.1), linksBin, linksUn⟩ ws = true) :
    Impossible1 T (lv / 2) (lv % 2) (ws.map Prod.fst).toFinset := by
  by_cases hc : lv / 2 = 0
  · intro k hk h
    have ke : k = 0 := by omega
    subst k
    have ht0 : lv % 2 = 0 := by have := (live_size h).1; omega
    rw [ht0] at h
    generalize he : (ws.map Prod.fst).toFinset = S at h
    cases h
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  have hc' : 0 < lv / 2 := by omega
  have htest := checks.resolve_left hc
  apply enum_step1 (by omega) nd out
  · intro hrem1 v hv keep fresh pro len
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    have hf := unary_front nd ha keep
    rw [← hf]
    simpa using evalMove_sound (op := 2) pairs faith nd ha ha (by simp) hc' (fun _ => hrem1)
      pv (lvBin hc') (lvUn hc') pro fresh (all_unary htest hrem1 ha keep)
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a, haW, rfl⟩ := List.mem_map.mp ha
    obtain ⟨b, hbW, rfl⟩ := List.mem_map.mp hb
    have ab : a ≠ b := fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a ∈ ws) (bb : b ∈ ws) (ne' : a.1 ≠ b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPair ⟨T, lv, ws.length, ws, preCov ws, pools, pools.map (summarizePool ws),
          sumKeys (ws.map (fun w => keyWord w.1)), ws.map (fun w => keyWord w.1), linksBin, linksUn⟩ a b d = true) :
        Impossible1 T (lv / 2 - 1) (lv % 2) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      rw [← binary_front nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
      have hne2 : ((if d then 1 else 0) == 2) = false := by cases d <;> decide
      have res := evalMove_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc'
        (fun h => by rw [hne2] at h; contradiction) pv (lvBin hc') (lvUn hc')
        (eq ▸ pr) (eq ▸ fr) (testPair_at test ka kb)
      simpa [hne2] using res
    rcases all_binary htest haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [childTwo_swap _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro)
        (bin_comm d a.1 b.1 ▸ fresh) hh

theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r = s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 8
  · let i : Fin 8 := ⟨j, hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      have : List.ofFn (fun k : Fin 8 => inputs.getD k.val zero) = inputs := rfl
      rw [← this]; exact List.mem_ofFn.mpr ⟨i, rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 256 ≤ 2 ^ j := by
      change 2 ^ 8 ≤ 2 ^ j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def composedOK (p q : List Move) : Bool := inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [← bit_moved, ← bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def autoOK (T : Sig) (p : List Move) : Bool :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p

theorem rotate_excluded {T cap remNot} {ws : List Sig} (hi : Impossible1 T cap remNot ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) :
    Impossible1 T cap remNot (ws.map (movedWord p)).toFinset := by
  simp only [autoOK, Bool.and_eq_true, beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p.reverse) :=
    fun r => ⟨movedRow p r, composed_id ok.1.2 r⟩
  intro k hk h
  have run := live_rename h (movedRow p.reverse) onto
  have inv (x : Sig) : rename (movedRow p.reverse) (movedWord p x) = x := by
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    change bit ⟨j, hj⟩ _ = bit ⟨j, hj⟩ _
    rw [bit_rename, bit_moved, composed_id ok.2]
  have goal : rename (movedRow p.reverse) T = T := by
    have h1 := inv T
    rwa [ok.1.1] at h1
  have back : (ws.map (movedWord p)).toFinset.image (rename (movedRow p.reverse)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨v, ⟨w, hw, rfl⟩, rfl⟩; simpa only [inv] using hw
    · intro ha; exact ⟨_, ⟨a, ha, rfl⟩, inv a⟩
  rw [goal, back] at run
  exact hi k hk run

abbrev Packing := Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0, 0, 0, 0, fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) : Nat :=
  let i := pos / 8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift + len ≤ 8192 then lo &&& ((1 <<< len) - 1)
  else (lo ||| (word (i + 1) <<< (8192 - shift))) &&& ((1 <<< len) - 1)

def lookupWord (nb slots sw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a * sw) sw
  let row := (h / nb + sh) % slots
  let word := packedAt data (nb * sw + row * (iw + pw)) (iw + pw)
  some (word &&& ((1 <<< iw) - 1), (word >>> iw) &&& ((1 <<< pw) - 1))

inductive IndexTree (α : Type) where
  | leaf (items : List α)
  | fork (pivot : Nat) (left right : IndexTree α)
def IndexTree.read {α} : IndexTree α → Nat → Option α
  | .leaf xs, i => xs[i]?
  | .fork pivot a b, i => if i < pivot then a.read i else b.read (i - pivot)
def IndexTree.values {α} : IndexTree α → List α
  | .leaf xs => xs
  | .fork _ a b => a.values ++ b.values
theorem IndexTree.read_mem {α} (tree : IndexTree α) {i x} (e : tree.read i = some x) :
    x ∈ tree.values := by
  induction tree generalizing i with
  | leaf xs => exact List.mem_of_getElem? e
  | fork pivot a b ia ib =>
    simp only [IndexTree.read] at e; split at e
    · exact List.mem_append_left _ (ia e)
    · exact List.mem_append_right _ (ib e)

structure Forest where
  mask : Nat
  topCap : Nat
  samples : Nat → Bits × Bits
  cols : IndexTree ColumnInfo
  autos : Array (List Nat)
  levels : Nat → Packing
  index : Nat → Nat → Option (Nat × Nat)

def wiresOf (g : Forest) : List Decor :=
  rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a :=
  raw_faithful g.mask _ _

def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w :: ws => if bits &&& 1 == 1 then w :: selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons _ _ ih => unfold selectLive; split; exact List.Sublist.cons₂ _ (ih _); exact List.Sublist.cons _ (ih _)

def readNode (g : Forest) (lv i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_, depth, _, _, data) := g.levels lv
  let len := 10 * depth
  let width := len + raw.length + depth
  let recp := packedAt data (i * width) width
  let ops := recp &&& ((1 <<< len) - 1)
  let bank := decodeBank depth ops raw
  (ops, bank, selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) : Nat := (x >>> pos) &&& ((1 <<< width) - 1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n + 1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2, (bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols.read idx).bind fun ci =>
    materialize (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols.values, Slice1 (vars g.mask) (graphGoal g.mask) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (graphGoal g.mask) c := by
  unfold buildRule at h
  cases e : g.cols.read i with
  | none => simp [e] at h
  | some ci =>
    simp only [e, Option.bind_some] at h
    exact materialize_sound (cols ci (g.cols.read_mem e)) h

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0, _ => []
  | n + 1, pos =>
    let x := packedAt data pos (w + v)
    (x &&& ((1 <<< w) - 1), x >>> w) :: getPairs data w v n (pos + w + v)

theorem selectLive_map {α β} (f : α → β) (bits : Nat) (ws : List α) :
    (selectLive bits ws).map f = selectLive bits (ws.map f) := by
  induction ws generalizing bits with
  | nil => rfl
  | cons w ws ih =>
    unfold selectLive; split
    · simp only [List.map_cons, ih]
    · exact ih _

def stateSet (g : Forest) (lv i : Nat) : List Sig :=
  let raw := vars g.mask
  let (_, depth, _, _, data) := g.levels lv
  let len := 10 * depth
  let width := len + raw.length + depth
  let recp := packedAt data (i * width) width
  selectLive (recp >>> len) (decodeSig depth (recp &&& ((1 <<< len) - 1)) raw)

theorem readNode_fst (g : Forest) (lv i : Nat) :
    (readNode g lv i).2.2.map Prod.fst = stateSet g lv i := by
  have hraw : (wiresOf g).map Prod.fst = vars g.mask := by
    simp [wiresOf, rawDecor, vars, List.map_map, Function.comp_def]
  have hlen : (wiresOf g).length = (vars g.mask).length := by rw [← hraw, List.length_map]
  unfold readNode stateSet
  dsimp only
  rw [hlen, selectLive_map, decodeBank_fst, hraw]
def linkedSet (g : Forest) (lv : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels lv).1 then none else
    (g.autos[pair.2]?).map fun perm =>
      let st := stateSet g lv pair.1
      if perm.isEmpty then st else
        let ms := perm.map swapRows
        st.map (movedWord ms)

theorem linkedSet_sound (g : Forest) (lv : Nat)
    (names : ∀ x ∈ g.autos.toList, autoOK (graphGoal g.mask) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels lv).1, Impossible1 (graphGoal g.mask) (lv / 2) (lv % 2) (stateSet g lv i).toFinset)
    {pair out} (h : linkedSet g lv pair = some out) :
    Impossible1 (graphGoal g.mask) (lv / 2) (lv % 2) out.toFinset := by
  unfold linkedSet at h; split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e, Option.map_some, Option.some.injEq] at h
      subst out
      split
      · exact earlier _ (by omega)
      · exact rotate_excluded (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))

def contextOf (g : Forest) (lv i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num, depth, cw, offw, data) := g.levels lv
  let (ops, bank, ws) := readNode g lv i
  let start := num * (10 * depth + raw.length + depth)
  let pos := start + num * offw + packedAt data (start + i * offw) offw
  let nr := packedAt data pos 5
  let rules := (getPairs data cw depth nr (pos + 5)).filterMap (fun (a, b) => buildRule g ops depth bank a b)
  let wkeys := ws.map (fun w => keyWord w.1)
  let lsBin := fun tag => ((g.index (lv - 2) tag).bind (linkedSet g (lv - 2))).toList
  let lsUn := fun tag => ((g.index (lv - 3) tag).bind (linkedSet g (lv - 3))).toList
  ⟨graphGoal g.mask, lv, ws.length, ws, preCov ws, rules, rules.map (summarizePool ws), sumKeys wkeys, wkeys, lsBin, lsUn⟩

def prelim (T : Sig) (c : NodeContext) : Bool :=
  let ws := c.ws.map Prod.fst
  decide ws.Nodup && !(ws.contains T)

def nodeVerified (g : Forest) (lv i : Nat) : Bool :=
  let c := contextOf g lv i
  prelim (graphGoal g.mask) c && (if lv / 2 = 0 then true else testAll c c.ws)

theorem nodeVerified_sound (g : Forest) (lv i : Nat)
    (samples : properPairs (graphGoal g.mask) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols.values, Slice1 (vars g.mask) (graphGoal g.mask) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos.toList, autoOK (graphGoal g.mask) (x.map swapRows) = true)
    (prior : ∀ lv' < lv, ∀ j < (g.levels lv').1,
      Impossible1 (graphGoal g.mask) (lv' / 2) (lv' % 2) (stateSet g lv' j).toFinset)
    (checked : nodeVerified g lv i = true) :
    Impossible1 (graphGoal g.mask) (lv / 2) (lv % 2) (stateSet g lv i).toFinset := by
  simp only [nodeVerified, prelim, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : graphGoal g.mask ∉ (readNode g lv i).2.2.map Prod.fst := by simpa [contextOf] using checked.1.2
  rw [← readNode_fst]
  apply node_sound (raw := vars g.mask) (pools := (contextOf g lv i).pools)
    (linksBin := (contextOf g lv i).linksBin) (linksUn := (contextOf g lv i).linksUn)
    samples _ hN hT _ _ _ _
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a, b⟩, _, h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro hcap tag xs hx
    dsimp only [contextOf] at hx
    have e : ((g.index (lv - 2) tag).bind (linkedSet g (lv - 2))) = some xs := by simpa using hx
    obtain ⟨pair, _, h⟩ := Option.bind_eq_some_iff.mp e
    have hlt : lv - 2 < lv := by omega
    have hdiv : (lv - 2) / 2 = lv / 2 - 1 := by omega
    have hmod : (lv - 2) % 2 = lv % 2 := by omega
    rw [← hdiv, ← hmod]
    exact linkedSet_sound g (lv - 2) names (prior (lv - 2) hlt) h
  · intro hcap hrem1 tag xs hx
    dsimp only [contextOf] at hx
    have e : ((g.index (lv - 3) tag).bind (linkedSet g (lv - 3))) = some xs := by simpa using hx
    obtain ⟨pair, _, h⟩ := Option.bind_eq_some_iff.mp e
    have hlt : lv - 3 < lv := by omega
    have hdiv : (lv - 3) / 2 = lv / 2 - 1 := by omega
    have hmod : (lv - 3) % 2 = 0 := by omega
    rw [← hdiv, ← hmod]
    exact linkedSet_sound g (lv - 3) names (prior (lv - 3) hlt) h
  · by_cases h0 : lv / 2 = 0
    · exact Or.inl h0
    · exact Or.inr (by
        have hc := checked.2
        rw [if_neg h0] at hc
        simpa only [contextOf] using hc)

def block (g : Forest) (lv start : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => nodeVerified g lv (start + n) && block g lv start n

theorem block_at {g lv start n} (h : block g lv start n = true) (j : Nat) (lo : start ≤ j) (hi : j < start + n) :
    nodeVerified g lv j = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block, Bool.and_eq_true] at h
    by_cases eq : j = start + n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)

theorem block_merge {g lv start a b} (h : block g lv start a = true)
    (h' : block g lv (start + a) b = true) : block g lv start (a + b) = true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block, Bool.and_eq_true] at h'
    simp only [Nat.add_succ, block, Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1, ih h'.2⟩

def checkedTables (g : Forest) (topLv : Nat) : Prop :=
  ∀ lv ≤ topLv, block g lv 0 (g.levels lv).1 = true

def graphValid (g : Forest) (prior : Nat → Nat) : Bool :=
  (liftGoal g.mask (fun j => (g.samples j).1) == BitVec.allOnes 192) &&
  (liftGoal g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.values.all (fun c => colCheck g.mask c prior) &&
  g.autos.toList.all (fun p => autoOK (graphGoal g.mask) (p.map swapRows))

theorem forest_all (g : Forest) (topLv : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower1 (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g topLv) :
    ∀ lv ≤ topLv, ∀ i < (g.levels lv).1,
      Impossible1 (graphGoal g.mask) (lv / 2) (lv % 2) (stateSet g lv i).toFinset := by
  simp only [graphValid, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at geometry
  intro lv
  induction lv using Nat.strong_induction_on with
  | ind lv ih =>
    intro hlv i hi
    apply nodeVerified_sound g lv i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun lv' hlt => ih lv' hlt (by omega))
    exact block_at (rows lv hlv) i (by omega) (by omega)

def indexedRoot (g : Forest) (lv i : Nat) (ws : List Sig) : Bool :=
  decide (i < (g.levels lv).1) && sameWords (stateSet g lv i) ws

theorem root_index {g topLv prior lv i ws} (low : ∀ q, Lower1 (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g topLv) (le : lv ≤ topLv)
    (idx : indexedRoot g lv i ws = true) :
    Impossible1 (graphGoal g.mask) (lv / 2) (lv % 2) ws.toFinset := by
  simp only [indexedRoot, Bool.and_eq_true, decide_eq_true_eq] at idx
  rw [← sameWords_sound idx.2]
  exact forest_all g topLv prior low geom blocks lv le i idx.1

theorem lower_forest2 {g0 g1 prior hints} (low : ∀ q, Lower1 (vars q) (graphGoal q) (prior q))
    (hmatch : g1.mask = g0.mask ∧ g1.topCap = g0.topCap + 1)
    (geom0 : graphValid g0 prior = true) (geom1 : graphValid g1 prior = true)
    (blocks0 : checkedTables g0 (2 * g0.topCap))
    (blocks1 : checkedTables g1 (2 * g1.topCap + 1))
    (idx0 : indexedRoot g0 (2 * g0.topCap) 0 (vars g0.mask) = true)
    (idx1 : indexedRoot g1 (2 * g1.topCap + 1) 0 (vars g1.mask) = true)
    (hp : properB (graphGoal g0.mask) = true)
    (ess : checkEssential (graphGoal g0.mask) (vars g0.mask) (graphPairs g0.mask hints) = true)
    (all : (graphPairs g0.mask hints).map Prod.fst = vars g0.mask) :
    Lower1 (vars g0.mask) (graphGoal g0.mask) (g0.topCap + 1) := by
  have no0 := root_index low geom0 blocks0 (Nat.le_refl _) idx0
  have no1 := root_index low geom1 blocks1 (Nat.le_refl _) idx1
  have d0 : (2 * g0.topCap) / 2 = g0.topCap := by omega
  have m0 : (2 * g0.topCap) % 2 = 0 := by omega
  have d1 : (2 * g1.topCap + 1) / 2 = g1.topCap := by omega
  have m1 : (2 * g1.topCap + 1) % 2 = 1 := by omega
  rw [d0, m0] at no0
  rw [d1, m1, hmatch.1, hmatch.2] at no1
  apply lower1_impossible (proper_of _ hp) _ no0 no1
  intro a ha; apply essential_ok ess a; rw [all]; exact List.mem_toFinset.mpr ha

theorem impossible_forest_t1 {g prior m cap} (low : ∀ q, Lower1 (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g (2 * g.topCap + 1))
    (idx1 : indexedRoot g (2 * g.topCap + 1) 0 (vars g.mask) = true)
    (hmc : g.mask = m ∧ g.topCap = cap) :
    Impossible1 (graphGoal m) cap 1 (vars m).toFinset := by
  obtain ⟨rfl, rfl⟩ := hmc
  have no1 := root_index low geom blocks (Nat.le_refl _) idx1
  have d1 : (2 * g.topCap + 1) / 2 = g.topCap := by omega
  have m1 : (2 * g.topCap + 1) % 2 = 1 := by omega
  rwa [d1, m1] at no1

theorem lower_discard {m prior ci hints} (low : ∀ q, Lower1 (vars q) (graphGoal q) (prior q))
    (ok : colCheck m ci prior = true)
    (hp : properB (graphGoal m) = true)
    (ess : checkEssential (graphGoal m) (vars m) (graphPairs m hints) = true)
    (all : (graphPairs m hints).map Prod.fst = vars m)
    (cut : decide (vars m).Nodup && poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 ci.2.2.2.2 0 0 (vars m) (vars m) = true) :
    Lower1 (vars m) (graphGoal m) (ci.2.2.2.2 + 1) := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at cut
  have sl := col_sound ci prior low ok
  apply lower1_impossible (proper_of _ hp) _
    (by simpa using poolCut_sound sl (remNot := 0) (by decide) cut.1 cut.2)
    (poolCut_sound sl (remNot := 1) (by decide) cut.1 cut.2)
  intro a ha; apply essential_ok ess a; rw [all]; exact List.mem_toFinset.mpr ha

def Known (entries : List (Nat × Nat)) : Prop :=
  ∀ e ∈ entries, Lower1 (vars e.1) (graphGoal e.1) e.2
def baseKnown : List (Nat × Nat) := []
theorem baseValid : Known baseKnown := by simp [Known, baseKnown]
def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) : List (Nat × Nat) :=
  relabels.map (fun v => (v.1, L)) ++ old
theorem extendKnown_ok {old L m relabels} (previous : Known old)
    (main : Lower1 (vars m) (graphGoal m) L)
    (ok : relabels.all (fun v => relabelOK v.1 m v.2) = true) :
    Known (extendKnown old L relabels) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
    exact relabel_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h

def lanePlace (v : Nat) (upper : Nat) : Nat := 2 ^ 193 * upper + v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x :: xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n + 1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2 ^ 193 := lt_trans x.isLt (by decide +kernel)

theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [lanePlace, Nat.testBit_and, Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i < 193 <;> simp only [h, ite_true, ite_false, BitVec.toNat_and, Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [lanePlace, Nat.testBit_or, Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i < 193 <;> simp only [h, ite_true, ite_false, BitVec.toNat_or, Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [lanePlace, Nat.testBit_xor, Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i < 193 <;> simp only [h, ite_true, ite_false, BitVec.toNat_xor, Nat.testBit_xor]

theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with | nil => simp [combineLanes] | cons a xs ih => simp only [combineLanes, place_and, ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with | nil => simp [combineLanes] | cons a xs ih => simp only [combineLanes, place_or, ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with | nil => simp [combineLanes] | cons a xs ih => simp only [combineLanes, place_xor, ih]
theorem broadcast {α} (a : Bits) (xs : List α) :
    units xs.length * a.toNat = combineLanes (fun _ => a) xs := by
  induction xs with
  | nil => simp [units, combineLanes]
  | cons _ xs ih => simp only [List.length_cons, units, combineLanes, lanePlace, Nat.add_mul, Nat.mul_assoc, ih, Nat.one_mul]

def fullMarks (r packed : Nat) : Nat := ((packed + r) >>> 192) &&& r
theorem unit_bit (n i : Nat) (hi : i < n) : (units n).testBit (193 * i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units, lanePlace, Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2 ^ 193)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 193 * (i + 1) - 193 = 193 * i := by omega
      have ge : ¬193 * (i + 1) < 193 := by omega
      simp only [ge, ite_false, di]; exact ih _ (by omega)

set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat + 1).testBit 192 = (a == BitVec.allOnes 192) := by
  by_cases h : a = BitVec.allOnes 192
  · subst a; decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2 ^ 192 - 1 := by
      intro eq; apply h; apply BitVec.eq_of_toNat_eq; simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat + 1 < 2 ^ 192 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i < xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (193 * i) =
      (f xs[i] == BitVec.allOnes 192) := by
  simp only [fullMarks, Nat.testBit_and, Nat.testBit_shiftRight, unit_bit _ _ hi, Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes, List.length_cons, units, lanePlace]
    have sum (u v x : Nat) : 2 ^ 193 * u + x + (2 ^ 193 * v + 1) = 2 ^ 193 * (u + v) + (x + 1) := by omega
    rw [sum, Nat.testBit_two_pow_mul_add _ (show (f a).toNat + 1 < 2 ^ 193 from by have := (f a).isLt; omega)]
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have hi' : i < xs.length := by simpa using hi
      have ge : ¬193 * (i + 1) + 192 < 193 := by omega
      have di : 193 * (i + 1) + 192 - 193 = 193 * i + 192 := by omega
      simp only [ge, ite_false, di, List.getElem_cons_succ]; exact ih i hi'

abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat
def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs, combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs, combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) : Nat :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn, packedSig, column, Bool.false_eq_true, ite_false, ite_true, lanes_and, lanes_xor, xor_meet]

def packedOp (full : Nat) (op : Nat) (a b : PackedSig) : PackedSig :=
  if op = 2 then (full ^^^ a.1, full ^^^ a.2) else if op = 1 then (a.1 ||| b.1, a.2 ||| b.2)
  else (a.1 &&& b.1, a.2 &&& b.2)
theorem top_xor (a : Bits) : BitVec.allOnes 192 ^^^ a = ~~~a := BitVec.allOnes_xor
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length * (BitVec.allOnes 192).toNat) op
      (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (movedDecor op (a x) (b x)).2) xs := by
  by_cases un : op = 2
  · simp only [packedOp, un, ite_true, packedSig, broadcast, lanes_xor, top_xor, movedDecor, codeDecor, dneg]
  · by_cases one : op = 1 <;> simp [packedOp, un, one, packedSig, lanes_or, lanes_and, movedDecor, codeDecor, dbin]

def takePacked (c : PackedCov) (a b : Nat) (un ka kb : Bool) : Nat :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if un then (if ka then c.1 else without1 a)
  else if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (un ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) un ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) un ka kb) xs := by
  cases un <;> cases ka <;> cases kb <;>
    simp only [takePacked, packedCov, lanes_and, lanes_or, lanes_xor, xor_meet, restCov, takeOne, takeTwo,
      Bool.false_eq_true, ite_false, ite_true]

def contextWire (c : NodeContext) (i : Nat) : Decor := c.ws.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) : Bool :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (movedDecor op a b) ka kb
def combField (c : NodeContext) (d un ka kb : Bool) (op i j : Nat) : Bits :=
  let a := contextWire c i
  let b := contextWire c j
  restCov (getCov c.cov d) (column d a.2) (column d b.2) un ka kb |||
    column d (movedDecor op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x :: xs => if mask = 0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 193) xs

theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i < xs.length)
    (bitOn : mask.testBit (193 * i) = true) (ok : onMarks f mask xs = true) : f xs[i] = true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask ≠ 0 := by intro e; simp [e] at bitOn
    simp only [onMarks, ne, ite_false, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0 = true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask := mask >>> 193) (i := i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight, Nat.mul_succ, Nat.add_comm] using bitOn

def fallbackFast (c : NodeContext) (i j op : Nat) (ka kb : Bool) : Bool :=
  let a := contextWire c i
  let b := contextWire c j
  let z := codeSig op a.1 b.1
  if !properB z || c.ws.any (fun v => v.1 == z) then true else
  let cap := c.lv / 2
  let un := op == 2
  let nrem := if un then 0 else c.lv % 2
  if cap == 1 then (nrem == 1) || (z != c.target) else
  if i < c.ws.length ∧ j < c.ws.length then
    if c.qpools.any (fun s => fastCost s (cap - 1) nrem a b op ka kb) then true else
    let rest := (opKeep un ka kb a b c.ws).map Prod.fst
    if c.qpools.any (fun s => decide (cap - 1 + s.1.paid < s.1.bound + 1 + s.2.1 + 1) &&
        scalarPoolCut s.1 (cap - 1) nrem rest (movedChoice op a b)) then true else
    let tag := if un || (a.1 != b.1) then
        keyWord z + (c.ksum - (if ka then 0 else c.wkeys.getD i 0) - (if un || kb then 0 else c.wkeys.getD j 0))
      else keySet (z :: rest)
    let ls := if un then c.linksUn else c.linksBin
    (ls tag).any (sameWords1 (z :: rest))
  else
    let rest := (opKeep un ka kb a b c.ws).map Prod.fst
    let ls := if un then c.linksUn else c.linksBin
    closeChild c.pools ls (cap - 1) nrem rest (movedChoice op a b)

theorem fallbackFast_sound {c i j op ka kb}
    (hq : c.qpools = c.pools.map (summarizePool c.ws))
    (hwk : c.wkeys = c.ws.map (fun w => keyWord w.1))
    (hks : c.ksum = keySet (c.ws.map Prod.fst))
    (h : fallbackFast c i j op ka kb = true) :
    (if !properB (movedDecor op (contextWire c i) (contextWire c j)).1 ||
        c.ws.any (fun v => v.1 == (movedDecor op (contextWire c i) (contextWire c j)).1)
      then true else
      if c.lv / 2 == 1 then ((if op == 2 then 0 else c.lv % 2) == 1) ||
        ((movedDecor op (contextWire c i) (contextWire c j)).1 != c.target) else
      closeChild c.pools (if op == 2 then c.linksUn else c.linksBin) (c.lv / 2 - 1)
        (if op == 2 then 0 else c.lv % 2)
        ((opKeep (op == 2) ka kb (contextWire c i) (contextWire c j) c.ws).map Prod.fst)
        (movedChoice op (contextWire c i) (contextWire c j))) = true := by
  have hz : (movedDecor op (contextWire c i) (contextWire c j)).1 =
      codeSig op (contextWire c i).1 (contextWire c j).1 := by
    unfold movedDecor codeDecor codeSig; split
    · rfl
    · cases (op == 1) <;> rfl
  have hzc : choiceVal (movedChoice op (contextWire c i) (contextWire c j)) =
      codeSig op (contextWire c i).1 (contextWire c j).1 := by
    rw [← moved_full, hz]
  rw [hz]
  let a := contextWire c i
  let b := contextWire c j
  let z := codeSig op a.1 b.1
  let cap := c.lv / 2
  let un := op == 2
  let nrem := if un then 0 else c.lv % 2
  let rest := (opKeep un ka kb a b c.ws).map Prod.fst
  let ls := if un then c.linksUn else c.linksBin
  by_cases hpd : (!properB z || c.ws.any (fun v => v.1 == z)) = true
  · change (if (!properB z || c.ws.any (fun v => v.1 == z)) = true then true else _) = true
    rw [if_pos hpd]
  · change (if (!properB z || c.ws.any (fun v => v.1 == z)) = true then true else _) = true
    rw [if_neg hpd]
    by_cases h1 : (cap == 1) = true
    · change (if (cap == 1) = true then _ else _) = true
      rw [if_pos h1]
      unfold fallbackFast at h
      change (if (!properB z || c.ws.any (fun v => v.1 == z)) = true then true else
        if (cap == 1) = true then _ else _) = true at h
      rw [if_neg hpd, if_pos h1] at h
      exact h
    · change (if (cap == 1) = true then _ else _) = true
      rw [if_neg h1]
      unfold fallbackFast at h
      change (if (!properB z || c.ws.any (fun v => v.1 == z)) = true then true else
        if (cap == 1) = true then _ else _) = true at h
      rw [if_neg hpd, if_neg h1] at h
      by_cases hij : i < c.ws.length ∧ j < c.ws.length
      · rw [if_pos hij] at h
        by_cases hq1 : c.qpools.any (fun s => fastCost s (cap - 1) nrem a b op ka kb) = true
        · rw [hq] at hq1
          obtain ⟨_, hm, ok⟩ := List.any_eq_true.mp hq1
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
          have mem (t) (ht : t < c.ws.length) : contextWire c t ∈ c.ws := by
            simp [contextWire, List.getD_eq_getElem?_getD, ht]
          have closed := fastCost_good (mem _ hij.1) (mem _ hij.2) ok
          have cut : c.pools.any (fun p => scalarPoolCut p (cap - 1) nrem rest (movedChoice op a b)) = true :=
            List.any_eq_true.mpr ⟨p, hp, closed⟩
          change closeChild c.pools ls (cap - 1) nrem rest (movedChoice op a b) = true
          simp only [closeChild, cut, Bool.true_or]
        · rw [if_neg hq1] at h
          by_cases hsc : c.qpools.any (fun s => decide (cap - 1 + s.1.paid < s.1.bound + 1 + s.2.1 + 1) &&
              scalarPoolCut s.1 (cap - 1) nrem rest (movedChoice op a b)) = true
          · rw [hq] at hsc
            obtain ⟨_, hm, ok⟩ := List.any_eq_true.mp hsc
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
            simp only [Bool.and_eq_true] at ok
            have cut : c.pools.any (fun p => scalarPoolCut p (cap - 1) nrem rest (movedChoice op a b)) = true :=
              List.any_eq_true.mpr ⟨p, hp, ok.2⟩
            change closeChild c.pools ls (cap - 1) nrem rest (movedChoice op a b) = true
            simp only [closeChild, cut, Bool.true_or]
          · rw [if_neg hsc] at h
            have htag : (if un || (a.1 != b.1) then
                keyWord z + (c.ksum - (if ka then 0 else c.wkeys.getD i 0) -
                  (if un || kb then 0 else c.wkeys.getD j 0))
              else keySet (z :: rest)) = keySet (z :: rest) := by
              split
              · next hcond =>
                simp only [Bool.or_eq_true, bne_iff_ne] at hcond
                have mem (t) (ht : t < c.ws.length) : contextWire c t ∈ c.ws := by
                  simp [contextWire, List.getD_eq_getElem?_getD, ht]
                have wk (t) (ht : t < c.ws.length) : c.wkeys.getD t 0 = keyWord (contextWire c t).1 := by
                  rw [hwk]; simp [contextWire, List.getD_eq_getElem?_getD, ht]
                have hne : un = false → a ≠ b := by
                  intro huf eq
                  rcases hcond with hu | hne1
                  · rw [hu] at huf; contradiction
                  · exact hne1 (congrArg Prod.fst eq)
                dsimp only [a, b, z, un, rest]
                rw [wk i hij.1, wk j hij.2, hks, keySet_cons, keySet_keep (mem i hij.1) (mem j hij.2) (op == 2) ka kb hne]
              · rfl
            change (ls (if un || (a.1 != b.1) then
                keyWord z + (c.ksum - (if ka then 0 else c.wkeys.getD i 0) -
                  (if un || kb then 0 else c.wkeys.getD j 0))
              else keySet (z :: rest))).any (sameWords1 (z :: rest)) = true at h
            rw [htag] at h
            have hzc' : choiceVal (movedChoice op a b) = z := hzc
            change closeChild c.pools ls (cap - 1) nrem rest (movedChoice op a b) = true
            simp only [closeChild, hzc', h, Bool.or_true]
      · rw [if_neg hij] at h; exact h

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov × PackedCov
def makeBatch (lv n : Nat) (xs : List NodeContext) : Batch :=
  (lv, n, units xs.length, (List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.cov.1) xs, packedCov (fun c => c.cov.2) xs)
def laneWire (b : Batch) (i : Nat) : PackedSig := b.2.2.2.1.getD i (0, 0)
theorem laneWire_at (lv n) (xs) {i : Nat} (h : i < n) :
    laneWire (makeBatch lv n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire, makeBatch, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, h]

def batchMove (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) : Bool :=
  let (lv, n, r, _, u, v) := b
  let cap := lv / 2
  let remNot := lv % 2
  let un := op == 2
  if un && remNot == 0 then true else
  let nrem := if un then 0 else remNot
  let len := 1 + (n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len + nrem > cap then true else
    let d := nrem == 0
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp (r * (BitVec.allOnes 192).toNat) op a b'
    let cov := if d then v else u
    let mask := fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fallbackFast c i j op ka kb) mask xs

theorem batchMove_at (lv n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i < n) (hj : j < n) {q : Nat} (hq : q < xs.length)
    (hlv : xs[q].lv = lv) (har : xs[q].arity = n)
    (hqp : xs[q].qpools = xs[q].pools.map (summarizePool xs[q].ws))
    (hwk : xs[q].wkeys = xs[q].ws.map (fun w => keyWord w.1))
    (hks : xs[q].ksum = keySet (xs[q].ws.map Prod.fst))
    (pass : batchMove (makeBatch lv n xs) xs i j op ka kb = true) :
    checkAt xs[q] i j op ka kb = true := by
  let cap := lv / 2
  let remNot := lv % 2
  let un := op == 2
  let nrem := if un then 0 else remNot
  let len := 1 + (n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  let d := nrem == 0
  have eval : checkAt xs[q] i j op ka kb =
      if un && remNot == 0 then true else
      if len + nrem > cap then true else
      if combField xs[q] d un ka kb op i j != BitVec.allOnes 192 then true else
      if !properB (movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].ws.any (fun v => v.1 == (movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else
      if cap == 1 then (nrem == 1) || ((movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1 != xs[q].target) else
      closeChild xs[q].pools (if un then xs[q].linksUn else xs[q].linksBin) (cap - 1) nrem
        ((opKeep un ka kb (contextWire xs[q] i) (contextWire xs[q] j) xs[q].ws).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt, evalMove, hlv, har, cap, remNot, un, nrem, len, d, combField]
  by_cases hun : (un && (remNot == 0)) = true
  · simp [eval, hun]
  · by_cases small : len + nrem > cap
    · simp [eval, hun, small]
    · let r := units xs.length
      let a := laneWire (makeBatch lv n xs) i
      let b := laneWire (makeBatch lv n xs) j
      let cov := if d then packedCov (fun c : NodeContext => c.cov.2) xs
                 else packedCov (fun c : NodeContext => c.cov.1) xs
      change (if un && remNot == 0 then true else if len + nrem > cap then true else
        onMarks _ (fullMarks r
          (takePacked cov (packedColumn d a) (packedColumn d b) un ka kb |||
           packedColumn d (packedOp (r * (BitVec.allOnes 192).toNat) op a b))) xs) = true at pass
      rw [if_neg hun, if_neg small] at pass
      have chosen : cov = packedCov (fun c => getCov c.cov d) xs := by dsimp only [cov]; cases d <;> rfl
      have ca : a = _ := laneWire_at lv n xs hi
      have cb : b = _ := laneWire_at lv n xs hj
      dsimp only [r] at pass
      rw [ca, cb, packed_op, packed_column, packed_column, packed_column, chosen, takePacked_ok, lanes_or] at pass
      by_cases hit : combField xs[q] d un ka kb op i j = BitVec.allOnes 192
      · have hfb : fallbackFast xs[q] i j op ka kb = true := by
          apply marked_ok _ _ _ q hq _ pass
          rw [mark_at _ _ _ hq]
          exact beq_iff_eq.mpr hit
        have hbn : (combField xs[q] d un ka kb op i j != BitVec.allOnes 192) = false := by simp [hit]
        rw [eval, if_neg hun, if_neg small, hbn, if_neg Bool.false_ne_true]
        simpa only [hlv, cap, remNot, un, nrem] using fallbackFast_sound hqp hwk hks hfb
      · rw [eval, if_neg hun, if_neg small, if_pos (bne_iff_ne.mpr hit)]

def batchPair (b : Batch) (xs : List NodeContext) (i j op : Nat) : Bool :=
  let f := batchMove b xs i j op
  f false false && f true false && f false true && f true true
def batchRow (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) : Bool :=
  (if b.1 % 2 == 0 then true else batchMove b xs i i 2 false false && batchMove b xs i i 2 true true) &&
    js.all (fun j => batchPair b xs i j 0 && batchPair b xs i j 1)
def batchRows (b : Batch) (xs : List NodeContext) : List Nat → Bool
  | [] => true
  | i :: js => batchRow b xs i js && batchRows b xs js

theorem batchRows_at (lv n) (xs : List NodeContext) {q : Nat} (hq : q < xs.length)
    (hlv : xs[q].lv = lv) (har : xs[q].arity = n)
    (hqp : xs[q].qpools = xs[q].pools.map (summarizePool xs[q].ws))
    (hwk : xs[q].wkeys = xs[q].ws.map (fun w => keyWord w.1))
    (hks : xs[q].ksum = keySet (xs[q].ws.map Prod.fst))
    (js : List Nat) (bounds : ∀ j ∈ js, j < n)
    (allRows : batchRows (makeBatch lv n xs) xs js = true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows, Bool.and_eq_true, batchRow, List.all_eq_true] at allRows
    simp only [List.map_cons, testAll, testRow, Bool.and_eq_true, List.all_eq_true, List.mem_map]
    have hi := bounds i List.mem_cons_self
    have check := @batchMove_at lv n xs
    refine ⟨⟨?_, ?_⟩, ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    · rw [hlv]
      cases h0 : (lv % 2 == 0)
      · have h1 := allRows.1.1; change (if (lv % 2 == 0) then true else _) = true at h1
        rw [h0] at h1; simp only [Bool.false_eq_true, ite_false, Bool.and_eq_true] at h1 ⊢
        exact ⟨check hi hi hq hlv har hqp hwk hks h1.1, check hi hi hq hlv har hqp hwk hks h1.2⟩
      · simp
    · rintro _ ⟨j, hj, rfl⟩
      have hj' := bounds j (List.mem_cons_of_mem _ hj)
      have both := allRows.1.2 j hj
      have opCheck (d : Bool) (pass : batchPair (makeBatch lv n xs) xs i j (if d then 1 else 0) = true) :
          testPair xs[q] (contextWire xs[q] i) (contextWire xs[q] j) d = true := by
        simp only [batchPair, Bool.and_eq_true] at pass
        simp only [testPair, Bool.and_eq_true]
        exact ⟨⟨⟨check hi hj' hq hlv har hqp hwk hks pass.1.1.1, check hi hj' hq hlv har hqp hwk hks pass.1.1.2⟩,
          check hi hj' hq hlv har hqp hwk hks pass.1.2⟩, check hi hj' hq hlv har hqp hwk hks pass.2⟩
      exact ⟨opCheck false both.1, opCheck true both.2⟩

def runBatch (lv n : Nat) (xs : List NodeContext) : Bool :=
  batchRows (makeBatch lv n xs) xs (List.range n)
theorem runBatch_at {lv n} {xs : List NodeContext} {q} (hq : q < xs.length)
    (hlv : xs[q].lv = lv) (har : xs[q].arity = n) (hn : xs[q].ws.length = n)
    (hqp : xs[q].qpools = xs[q].pools.map (summarizePool xs[q].ws))
    (hwk : xs[q].wkeys = xs[q].ws.map (fun w => keyWord w.1))
    (hks : xs[q].ksum = keySet (xs[q].ws.map Prod.fst))
    (pass : runBatch lv n xs = true) : testAll xs[q] xs[q].ws = true := by
  have all := batchRows_at lv n xs hq hlv har hqp hwk hks (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].ws := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2; simp [contextWire, List.getD_eq_getElem?_getD, h2]
  rwa [eq] at all

theorem makeBlock {g lv start n} (h : ∀ i, start ≤ i → i < start + n → nodeVerified g lv i = true) :
    block g lv start n = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block, Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega), ih (fun i le lt => h i le (by omega))⟩

def contexts (g : Forest) (lv start n : Nat) : List NodeContext :=
  ((List.range n).map (start + ·)).map (contextOf g lv)
def header (g : Forest) (lv start n ar : Nat) : Bool :=
  (contexts g lv start n).all (fun c => c.arity == ar && prelim (graphGoal g.mask) c)
def rowCut (g : Forest) (lv start n ar lo len : Nat) : Bool :=
  let xs := contexts g lv start n
  let b := makeBatch lv ar xs
  (List.range len).all (fun d =>
    let i := lo + d
    batchRow b xs i (List.range' (i + 1) (ar - (i + 1))))

theorem rowCut_at {g lv start n ar lo len} (h : rowCut g lv start n ar lo len = true)
    (i : Nat) (l : lo ≤ i) (r : i < lo + len) :
    batchRow (makeBatch lv ar (contexts g lv start n)) (contexts g lv start n)
      i (List.range' (i + 1) (ar - (i + 1))) = true := by
  have ha := List.all_eq_true.mp h (i - lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem cutsRun {g lv start n ar} (h : rowCut g lv start n ar 0 ar = true) :
    runBatch lv ar (contexts g lv start n) = true := by
  let xs := contexts g lv start n
  have go (lo num : Nat) (eq : lo + num = ar) :
      batchRows (makeBatch lv ar xs) xs (List.range' lo num) = true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ, batchRows, Bool.and_eq_true]
      refine ⟨?_, ih (lo + 1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar - (lo + 1) = num by omega] using ok
  unfold runBatch; rw [List.range_eq_range']; exact go 0 ar (by omega)

theorem cutsBlock {g lv start n ar} (hd : header g lv start n ar = true)
    (h : rowCut g lv start n ar 0 ar = true) : block g lv start n = true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g lv start n
  have hm : contextOf g lv i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i, List.mem_map.mpr ⟨i - start, List.mem_range.mpr (by omega), by omega⟩, rfl⟩
  obtain ⟨q, hq, e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true, beq_iff_eq] at one
  have hlv : xs[q].lv = lv := by rw [e]; rfl
  have har : xs[q].arity = ar := e ▸ one.1
  have hn : xs[q].ws.length = ar := by rw [e]; exact one.1
  have hqp : xs[q].qpools = xs[q].pools.map (summarizePool xs[q].ws) := by rw [e]; rfl
  have hwk : xs[q].wkeys = xs[q].ws.map (fun w => keyWord w.1) := by rw [e]; rfl
  have hks : xs[q].ksum = keySet (xs[q].ws.map Prod.fst) := by rw [e]; exact sumKeys_map _
  simp only [nodeVerified, Bool.and_eq_true]
  refine ⟨one.2, ?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hlv har hn hqp hwk hks (cutsRun h)

def checkLeaf (g : Forest) (lv start n ar : Nat) : Bool :=
  let xs := contexts g lv start n
  xs.all (fun c => c.arity == ar && prelim (graphGoal g.mask) c) &&
  let b := makeBatch lv ar xs
  (List.range ar).all (fun i => batchRow b xs i (List.range' (i + 1) (ar - (i + 1))))

theorem checkLeaf_sound {g lv start n ar} (h : checkLeaf g lv start n ar = true) :
    block g lv start n = true := by
  simp only [checkLeaf, Bool.and_eq_true] at h
  exact cutsBlock h.1 (by simpa [rowCut] using h.2)

def cells (g : Forest) (lv start n ar : Nat) : Nat → Prop
  | 0 => checkLeaf g lv start n ar = true
  | d + 1 => cells g lv start (n / 2) ar d ∧ cells g lv (start + n / 2) (n - n / 2) ar d

theorem cellsBlock {g lv start n ar d} (h : cells g lv start n ar d) :
    block g lv start n = true := by
  induction d generalizing start n with
  | zero => exact checkLeaf_sound h
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

theorem cl {g lv start n} (ar : Nat) (h : checkLeaf g lv start n ar = true) :
    block g lv start n = true := checkLeaf_sound h

theorem cb {g lv start n} (ar d : Nat) (h : cells g lv start n ar d) :
    block g lv start n = true := cellsBlock h

def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f = true
  | d + 1 => listPieces f (xs.take (xs.length / 2)) d ∧ listPieces f (xs.drop (xs.length / 2)) d

theorem listPieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f = true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length / 2)) ++ (xs.drop (xs.length / 2))).all f = true := by
      simp only [List.all_append, ih h.1, ih h.2, Bool.and_self]
    simpa only [List.take_append_drop] using ap

def edgeList : List ℕ :=
  [0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7]

def edgeFn (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edgeList.length / 2,
    (List.ofFn x).getD (edgeList.getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (edgeList.getD (2 * i + 1) 0) false = true)

def hand14Gates : List Gate :=
  [⟨.or, [5, 6]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [0, 7]⟩, ⟨.and, [9, 10]⟩,
   ⟨.or, [7, 8]⟩, ⟨.or, [4, 12]⟩, ⟨.and, [1, 13]⟩, ⟨.or, [0, 2]⟩,
   ⟨.or, [5, 7]⟩, ⟨.and, [15, 16]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [11, 14]⟩,
   ⟨.or, [17, 18]⟩, ⟨.or, [19, 20]⟩]

def sample8 (r : Row) (j : Fin 8) : Bool := bit r (inputs.getD j.val zero)

def rowOfVec (x : Fin 8 → Bool) : Row :=
  (BitVec.ofBoolListLE (List.ofFn x)).toFin.cast (by simp)

theorem sample8_rowOfVec (x : Fin 8 → Bool) : sample8 (rowOfVec x) = x := by
  funext j
  simp only [sample8, input_coords, rowOfVec]
  change (BitVec.ofBoolListLE (List.ofFn x)).getLsbD j.val = x j
  simp only [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn, j.isLt,
    ↓reduceDIte, Option.getD_some]

theorem sampled8 (r : Row) : List.ofFn (sample8 r) = inputs.map (bit r) := by
  have hi : List.ofFn (fun j : Fin 8 => inputs.getD j.val zero) = inputs := rfl
  rw [← hi, List.map_ofFn]; rfl

theorem table_eval (gates : List Gate)
    (h : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (i : Nat) (r : Row) :
    bit r ((execute gates inputs).getD i zero) =
      (Circuit.wires ⟨gates, 0⟩ (List.ofFn (sample8 r))).getD i false := by
  rw [← b_read, execute_bits _ _ _ (fun g hg => (h g hg).1), sampled8]
  rfl

theorem graph255_table : ∀ r : Row, bit r (graphGoal 255) = edgeFn (sample8 r) := by decide +kernel
theorem graph255_proper : proper (graphGoal 255) := by unfold proper; decide +kernel
theorem hand14_mono : ∀ g ∈ hand14Gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [hand14Gates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem hand14_len : hand14Gates.length = 14 := rfl
theorem hand14_eval_row : ∀ r : Row, Circuit.eval ⟨hand14Gates, 21⟩ (List.ofFn (sample8 r)) = edgeFn (sample8 r) := by
  decide +kernel

theorem hand14_eval (x : Fin 8 → Bool) : Circuit.eval ⟨hand14Gates, 21⟩ (List.ofFn x) = edgeFn x := by
  simpa only [sample8_rowOfVec] using hand14_eval_row (rowOfVec x)

theorem countP_not_le_one (gates : List Gate)
    (hnot1 : ∀ i j : Fin gates.length, (gates.get i).op = .not → (gates.get j).op = .not → i = j) :
    gates.countP (fun g => isNotOp g.op) ≤ 1 := by
  induction gates with
  | nil => simp
  | cons g gs ih =>
    rw [List.countP_cons]
    cases hg : g.op with
    | not =>
      have hzero : gs.countP (fun g => isNotOp g.op) = 0 := by
        rw [List.countP_eq_zero]
        intro x hx
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
        cases hxop : gs[k].op with
        | not =>
          have h0 : ((g :: gs).get ⟨0, by simp⟩).op = .not := hg
          have h1 : ((g :: gs).get ⟨k + 1, by simp; omega⟩).op = .not := hxop
          have heq := hnot1 ⟨0, by simp⟩ ⟨k + 1, by simp; omega⟩ h0 h1
          simp at heq
        | and | or | mod _ | maj => simp [isNotOp]
      rw [hzero]; simp [isNotOp]
    | and | or | mod _ | maj =>
      simp only [isNotOp, Bool.false_eq_true, ite_false, Nat.add_zero]
      apply ih
      intro i j hi hj
      have heq := hnot1 i.succ j.succ hi hj
      exact Fin.ext (Nat.succ.inj (congrArg Fin.val heq))

theorem all_roots_255 {k t S} (h : Live (graphGoal 255) k t S) (sub : ∀ v ∈ S, v ∈ inputs) :
    S = (vars 255).toFinset := by
  have ess : checkEssential (graphGoal 255) (vars 255) (graphPairs 255 66883) = true := by decide +kernel
  have all : (graphPairs 255 66883).map Prod.fst = vars 255 := by decide +kernel
  have vin : vars 255 = inputs := rfl
  ext a
  constructor
  · intro ha; exact List.mem_toFinset.mpr (vin.symm ▸ sub a ha)
  · intro ha
    have hmem : a ∈ ((graphPairs 255 66883).map Prod.fst).toFinset := by
      rw [all]; exact ha
    obtain ⟨r, s, hd, iso⟩ := essential_ok ess a hmem
    exact raw_required h (vars 255) a (fun v hv => vin.symm ▸ sub v hv) r s hd iso

theorem main_from_imp255 (imp : Impossible1 (graphGoal 255) 13 1 (vars 255).toFinset)
    (gates : List Gate) (o : ℕ)
    (hlegal : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hnot1 : ∀ i j : Fin gates.length, (gates.get i).op = .not → (gates.get j).op = .not → i = j)
    (heval : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = edgeFn x) :
    ∃ (gates' : List Gate) (o' : ℕ),
      (∀ g ∈ gates', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = edgeFn x := by
  by_cases h14 : 14 ≤ gates.length
  · exact ⟨hand14Gates, 21, hand14_mono, by rw [hand14_len]; exact h14, hand14_eval⟩
  · have hlt : gates.length ≤ 13 := by omega
    have goalEq : (execute gates inputs).getD o zero = graphGoal 255 := by
      apply BitVec.eq_of_getLsbD_eq; intro j hj
      let r : Row := ⟨j, hj⟩
      exact (table_eval gates hlegal o r).trans ((heval (sample8 r)).trans (graph255_table r).symm)
    have out := get_rep (execute gates inputs) o
    rw [goalEq] at out
    have targetIn : graphGoal 255 ∈ execute gates inputs := out.resolve_right (fun hn => hn graph255_proper)
    obtain ⟨k, t, S, hk, ht, run, hs⟩ := extract1 gates inputs hlegal graph255_proper targetIn
    have hcnt := countP_not_le_one gates hnot1
    have ht1 : t = 0 ∨ t = 1 := by omega
    rcases ht1 with rfl | rfl
    · obtain ⟨gs', hmono', hlen', hout'⟩ := live_zero_to_gates run inputs hs
      obtain ⟨o', ho', hget'⟩ := List.getElem_of_mem hout'
      refine ⟨gs', o', hmono', by omega, ?_⟩
      intro x
      have hleg' : ∀ g ∈ gs', (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
        intro g hg; obtain ⟨ho, hl⟩ := hmono' g hg
        exact ⟨ho.elim Or.inl (fun h => Or.inr (Or.inl h)), hl⟩
      have hev := table_eval gs' hleg' o' (rowOfVec x)
      have hgD : (execute gs' inputs).getD o' zero = graphGoal 255 := by
        simp [List.getD_eq_getElem?_getD, ho', hget']
      rw [hgD, graph255_table, sample8_rowOfVec] at hev
      exact hev.symm
    · have hS := all_roots_255 run hs
      exact False.elim (imp k (by omega) (hS ▸ run))

def g73s : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffe3f3f5,0x1242b0),(0x0,0x0),(0x0,0x0),(0x1c7cde,0x9284c),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffff8f2b,0xffffffffffffffffffffffffffffffffffffffffffe49503),(0x0,0x0)]
def g73c : IndexTree ColumnInfo := (.leaf [])
def g73a : Array (List Nat) := #[[],[99],[48],[48,96],[96,48],[96]]
def da73_6 (_ : Nat) := 0x7
def la73 : Nat -> Packing
| 6 => (1,0,0,0,da73_6)
| _ => emptyPacking
def ia73 : Nat -> Nat -> Option (Nat × Nat)
| _ => fun _ => none
def fa73 : Forest := ⟨73,3,fun j => g73s[j]?.getD (0,0),g73c,g73a,la73,ia73⟩
lemma ba73_6 : block fa73 6 0 1 = true := cl 3 (by decide +kernel)
lemma ta73 : checkedTables fa73 6 := by
 intro lv hlv;interval_cases lv
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . exact ba73_6
set_option maxHeartbeats 0 in
theorem gm73 : graphValid fa73 (boundsBefore baseKnown) = true := by decide +kernel
def kb73_6 (_ : Nat) := 0x440
def db73_6 (_ : Nat) := 0x3e00
def db73_9 (_ : Nat) := 0x7
def lb73 : Nat -> Packing
| 6 => (1,1,0,0,db73_6)
| 9 => (1,0,0,0,db73_9)
| _ => emptyPacking
def ib73 : Nat -> Nat -> Option (Nat × Nat)
| 6 => lookupWord 1 3 2 0 3 kb73_6
| _ => fun _ => none
def fb73 : Forest := ⟨73,4,fun j => g73s[j]?.getD (0,0),g73c,g73a,lb73,ib73⟩
lemma bb73_6 : block fb73 6 0 1 = true := cl 4 (by decide +kernel)
lemma bb73_9 : block fb73 9 0 1 = true := cl 3 (by decide +kernel)
lemma tb73 : checkedTables fb73 9 := by
 intro lv hlv;interval_cases lv
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . exact bb73_6
 . rfl
 . rfl
 . exact bb73_9
theorem l73 : Lower1 (vars 73) (graphGoal 73) 4 := lower_forest2 (g0:=fa73) (g1:=fb73) (hints:=3) (before_sound baseKnown baseValid) ⟨rfl,rfl⟩ gm73 gm73 ta73 tb73 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def k73 := extendKnown baseKnown 4 [(73,[]),(137,[118]),(161,[67,83,118]),(162,[16,67,83,118]),(164,[16,32,67,83,118]),(193,[67,83,115,99]),(194,[16,67,83,115,99]),(200,[16,32,64,48,83,115,99])]
theorem v73 : Known k73 := extendKnown_ok baseValid l73 (by decide +kernel)
def g43s : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffe3f3f5,0x1242b0),(0x1c0c3e,0x1b683c),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffe070df,0xffffffffffffffffffffffffffffffffffffffffffedb04f),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffff8f2b,0xffffffffffffffffffffffffffffffffffffffffffe49503),(0x0,0x0),(0x0,0x0)]
def g43c : IndexTree ColumnInfo := (.leaf [])
def g43a : Array (List Nat) := #[[],[80,49]]
def da43_6 (_ : Nat) := 0xf
def la43 : Nat -> Packing
| 6 => (1,0,0,0,da43_6)
| _ => emptyPacking
def ia43 : Nat -> Nat -> Option (Nat × Nat)
| _ => fun _ => none
def fa43 : Forest := ⟨43,3,fun j => g43s[j]?.getD (0,0),g43c,g43a,la43,ia43⟩
lemma ba43_6 : block fa43 6 0 1 = true := cl 4 (by decide +kernel)
lemma ta43 : checkedTables fa43 6 := by
 intro lv hlv;interval_cases lv
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . exact ba43_6
set_option maxHeartbeats 0 in
theorem gm43 : graphValid fa43 (boundsBefore k73) = true := by decide +kernel
def db43_9 (_ : Nat) := 0xf
def lb43 : Nat -> Packing
| 9 => (1,0,0,0,db43_9)
| _ => emptyPacking
def ib43 : Nat -> Nat -> Option (Nat × Nat)
| _ => fun _ => none
def fb43 : Forest := ⟨43,4,fun j => g43s[j]?.getD (0,0),g43c,g43a,lb43,ib43⟩
lemma bb43_9 : block fb43 9 0 1 = true := cl 4 (by decide +kernel)
lemma tb43 : checkedTables fb43 9 := by
 intro lv hlv;interval_cases lv
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . exact bb43_9
theorem l43 : Lower1 (vars 43) (graphGoal 43) 4 := lower_forest2 (g0:=fa43) (g1:=fb43) (hints:=83) (before_sound k73 v73) ⟨rfl,rfl⟩ gm43 gm43 ta43 tb43 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def k43 := extendKnown k73 4 [(43,[]),(45,[33]),(51,[16,67]),(54,[32,16,67]),(83,[16,67,101]),(90,[32,16,65,49,101]),(101,[33,67,99]),(102,[32,16,67,99]),(106,[32,16,65,49,99,83]),(147,[16,67,101,117]),(150,[32,16,67,101,117]),(154,[32,16,65,49,101,117])]
theorem v43 : Known k43 := extendKnown_ok v73 l43 (by decide +kernel)
theorem l75 : Lower1 (vars 75) (graphGoal 75) 5 := lower_discard (m:=75) (ci:=(2,0,73,0,4)) (hints:=99) (before_sound k43 v43) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def k75 := extendKnown k43 5 [(75,[]),(105,[96,33,65,48,81]),(139,[118]),(170,[32,16,65,49,83,118]),(172,[32,65,49,83,118]),(178,[32,97,64,83,16,48,115]),(198,[32,16,67,83,115,99]),(204,[32,65,16,48,83,115,99]),(210,[32,97,64,83,16,115]),(228,[32,65,83,113,97]),(232,[32,65,80,48,113,49,99])]
theorem v75 : Known k75 := extendKnown_ok v43 l75 (by decide +kernel)
theorem l163 : Lower1 (vars 163) (graphGoal 163) 5 := lower_discard (m:=163) (ci:=(1,0,162,0,4)) (hints:=85) (before_sound k75 v75) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def k163 := extendKnown k75 5 [(163,[]),(165,[33]),(166,[32,16]),(169,[80,33,49,16]),(202,[32,16,49,101]),(225,[80,33,49,65,97]),(226,[32,81,48,64,96,16])]
theorem v163 : Known k163 := extendKnown_ok v75 l163 (by decide +kernel)
def g201s : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffff00f0ff0cfe49,0x88888808ae00),(0x0,0x0),(0x0,0x0),(0xf0f0f3333d2,0x4444442211c0),(0x0,0x0),(0x0,0x0),(0xf00ff0c3c4bc,0x222222814038),(0xfffffffffffffffffffffffffffffffffffffff000fc0927,0xffffffffffffffffffffffffffffffffffff111111540007)]
def g201c : IndexTree ColumnInfo := (.leaf [(1,0,200,0,4),(8,0,193,0,4),(64,0,137,0,4),(128,0,73,0,4)])
def g201a : Array (List Nat) := #[[],[118],[99],[99,115],[115,99],[115],[48],[48,118],[48,96],[48,96,112],[48,112,96],[48,112],[96,48],[96,48,115],[96],[96,112],[96,115],[96,115,48],[112,48,99],[112,48],[112,96],[112],[112,99,48],[112,99]]
def ka201_6 (_ : Nat) := 0
def da201_6 (_ : Nat) := 0x45e12148110
def ka201_8 (_ : Nat) := 0xc0010c23a0
def da201_8 (_ : Nat) := 0xc2422d0bd42443e48110
def ka201_10 (_ : Nat) := 0x10a20a00000
def da201_10 (_ : Nat) := 0xd01fd10
def da201_12 (_ : Nat) := 0x483f
def la201 : Nat -> Packing
| 6 => (1,3,2,0,da201_6)
| 8 => (2,2,2,4,da201_8)
| 10 => (1,1,2,0,da201_10)
| 12 => (1,0,2,0,da201_12)
| _ => emptyPacking
def ia201 : Nat -> Nat -> Option (Nat × Nat)
| 6 => lookupWord 1 1 0 0 5 ka201_6
| 8 => lookupWord 2 6 3 1 5 ka201_8
| 10 => lookupWord 4 8 3 0 5 ka201_10
| _ => fun _ => none
def fa201 : Forest := ⟨201,6,fun j => g201s[j]?.getD (0,0),g201c,g201a,la201,ia201⟩
lemma ba201_6 : block fa201 6 0 1 = true := cl 4 (by decide +kernel)
lemma ba201_8 : block fa201 8 0 2 = true := cl 5 (by decide +kernel)
lemma ba201_10 : block fa201 10 0 1 = true := cl 5 (by decide +kernel)
lemma ba201_12 : block fa201 12 0 1 = true := cl 4 (by decide +kernel)
lemma ta201 : checkedTables fa201 12 := by
 intro lv hlv;interval_cases lv
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . exact ba201_6
 . rfl
 . exact ba201_8
 . rfl
 . exact ba201_10
 . rfl
 . exact ba201_12
set_option maxHeartbeats 0 in
theorem gm201 : graphValid fa201 (boundsBefore k163) = true := by
 simp only [graphValid,Bool.and_eq_true]
 refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=2) ?_⟩
 all_goals simp only [listPieces]
 all_goals repeat' apply And.intro
 all_goals decide +kernel
def kb201_6 (_ : Nat) := 0
def db201_6 (_ : Nat) := 0x8758e5550910
def kb201_8 (_ : Nat) := 0x80850002
def db201_8 (_ : Nat) := 0x5284f955424427aa5222213c5448600
def kb201_9 (_ : Nat) := 0
def db201_9 (_ : Nat) := 0x45e12148110
def kb201_10 (_ : Nat) := 0x501240001ac408200402
def db201_10 (_ : Nat) := 0xc080946650389103f91110fd21802f91110
def kb201_11 (_ : Nat) := 0xc0010c23a0
def db201_11 (_ : Nat) := 0xc2422d0bd42443e48110
def kb201_12 (_ : Nat) := 0x6602400
def db201_12 (_ : Nat) := 0x7a827e00
def kb201_13 (_ : Nat) := 0x10a20a00000
def db201_13 (_ : Nat) := 0x68827d10
def db201_15 (_ : Nat) := 0x483f
def lb201 : Nat -> Packing
| 6 => (1,4,2,0,db201_6)
| 8 => (3,3,2,4,db201_8)
| 9 => (1,3,2,0,db201_9)
| 10 => (3,2,2,6,db201_10)
| 11 => (2,2,2,4,db201_11)
| 12 => (1,1,2,0,db201_12)
| 13 => (1,1,2,0,db201_13)
| 15 => (1,0,2,0,db201_15)
| _ => emptyPacking
def ib201 : Nat -> Nat -> Option (Nat × Nat)
| 6 => lookupWord 1 1 0 0 5 kb201_6
| 8 => lookupWord 3 5 3 2 5 kb201_8
| 9 => lookupWord 1 1 0 0 5 kb201_9
| 10 => lookupWord 5 9 4 2 5 kb201_10
| 11 => lookupWord 2 6 3 1 5 kb201_11
| 12 => lookupWord 3 5 3 0 5 kb201_12
| 13 => lookupWord 4 8 3 0 5 kb201_13
| _ => fun _ => none
def fb201 : Forest := ⟨201,7,fun j => g201s[j]?.getD (0,0),g201c,g201a,lb201,ib201⟩
lemma bb201_6 : block fb201 6 0 1 = true := cl 4 (by decide +kernel)
lemma bb201_8 : block fb201 8 0 3 = true := cl 5 (by decide +kernel)
lemma bb201_9 : block fb201 9 0 1 = true := cl 4 (by decide +kernel)
lemma sb201_10_0 : block fb201 10 0 1 = true := cl 5 (by decide +kernel)
lemma sb201_10_1 : block fb201 10 1 2 = true := cl 6 (by decide +kernel)
lemma bb201_10 : block fb201 10 0 3 = true := (@block_merge fb201 10 0 1 2 (sb201_10_0) sb201_10_1)
lemma bb201_11 : block fb201 11 0 2 = true := cl 5 (by decide +kernel)
lemma bb201_12 : block fb201 12 0 1 = true := cl 5 (by decide +kernel)
lemma bb201_13 : block fb201 13 0 1 = true := cl 5 (by decide +kernel)
lemma bb201_15 : block fb201 15 0 1 = true := cl 4 (by decide +kernel)
lemma tb201 : checkedTables fb201 15 := by
 intro lv hlv;interval_cases lv
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . exact bb201_6
 . rfl
 . exact bb201_8
 . exact bb201_9
 . exact bb201_10
 . exact bb201_11
 . exact bb201_12
 . exact bb201_13
 . rfl
 . exact bb201_15
theorem l201 : Lower1 (vars 201) (graphGoal 201) 7 := lower_forest2 (g0:=fa201) (g1:=fb201) (hints:=3) (before_sound k163 v163) ⟨rfl,rfl⟩ gm201 gm201 ta201 tb201 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def k201 := extendKnown k163 7 [(201,[])]
theorem v201 : Known k201 := extendKnown_ok v163 l201 (by decide +kernel)
theorem l47 : Lower1 (vars 47) (graphGoal 47) 5 := lower_discard (m:=47) (ci:=(2,0,45,0,4)) (hints:=1363) (before_sound k201 v201) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def k47 := extendKnown k201 5 [(47,[]),(55,[16,67]),(118,[64,81,50,98,16])]
theorem v47 : Known k47 := extendKnown_ok v201 l47 (by decide +kernel)
theorem l59 : Lower1 (vars 59) (graphGoal 59) 5 := lower_discard (m:=59) (ci:=(8,0,51,0,4)) (hints:=65603) (before_sound k47 v47) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def k59 := extendKnown k47 5 [(59,[]),(110,[32,81,48,64,96,16])]
theorem v59 : Known k59 := extendKnown_ok v47 l59 (by decide +kernel)
def g91s : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffc00f83e19f3c9,0x294a5281171c0),(0x1f07c0667e52,0x318c630447e00),(0x0,0x0),(0x3e0003f819ebc,0x14a5295008e38),(0xfffffffffffffffffffffffffffffffffffc0007c00625ff,0xfffffffffffffffffffffffffffffffffffce739ce0201ff),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffff801f84927,0xfffffffffffffffffffffffffffffffffffc210842a80007),(0x0,0x0)]
def g91c : IndexTree ColumnInfo := (.fork 3 (.leaf [(16,0,75,0,5),(0,16,73,2,5),(8,0,83,0,4)]) (.leaf [(1,0,90,0,4),(2,0,73,0,4),(18,0,73,0,4)]))
def g91a : Array (List Nat) := #[[],[48]]
def ka91_10 (_ : Nat) := 0x10c0000000
def da91_10 (_ : Nat) := 0x824190fd40fd20
def da91_12 (_ : Nat) := 0xaac9f
def la91 : Nat -> Packing
| 10 => (2,1,3,4,da91_10)
| 12 => (1,0,3,0,da91_12)
| _ => emptyPacking
def ia91 : Nat -> Nat -> Option (Nat × Nat)
| 10 => lookupWord 7 9 4 1 1 ka91_10
| _ => fun _ => none
def fa91 : Forest := ⟨91,6,fun j => g91s[j]?.getD (0,0),g91c,g91a,la91,ia91⟩
lemma ba91_10 : block fa91 10 0 2 = true := cl 6 (by decide +kernel)
lemma ba91_12 : block fa91 12 0 1 = true := cl 5 (by decide +kernel)
lemma ta91 : checkedTables fa91 12 := by
 intro lv hlv;interval_cases lv
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . exact ba91_10
 . rfl
 . exact ba91_12
set_option maxHeartbeats 0 in
theorem gm91 : graphValid fa91 (boundsBefore k59) = true := by decide +kernel
def kb91_8 (_ : Nat) := 0
def db91_8 (_ : Nat) := 0x26d6295540
def kb91_10 (_ : Nat) := 0x1085658
def db91_10 (_ : Nat) := 0x421cd140bf2aa817e55482faa1225f15200
def kb91_12 (_ : Nat) := 0x60
def db91_12 (_ : Nat) := 0x923d2491a41720fe44fe00
def kb91_13 (_ : Nat) := 0x10c0000000
def db91_13 (_ : Nat) := 0x824190fd40fd20
def db91_15 (_ : Nat) := 0xb549f
def lb91 : Nat -> Packing
| 8 => (1,3,3,0,db91_8)
| 10 => (4,2,3,5,db91_10)
| 12 => (2,1,3,5,db91_12)
| 13 => (2,1,3,4,db91_13)
| 15 => (1,0,3,0,db91_15)
| _ => emptyPacking
def ib91 : Nat -> Nat -> Option (Nat × Nat)
| 8 => lookupWord 1 1 0 0 1 kb91_8
| 10 => lookupWord 3 6 3 2 1 kb91_10
| 12 => lookupWord 1 3 2 1 1 kb91_12
| 13 => lookupWord 7 9 4 1 1 kb91_13
| _ => fun _ => none
def fb91 : Forest := ⟨91,7,fun j => g91s[j]?.getD (0,0),g91c,g91a,lb91,ib91⟩
lemma bb91_8 : block fb91 8 0 1 = true := cl 5 (by decide +kernel)
lemma bb91_10 : block fb91 10 0 4 = true := cl 6 (by decide +kernel)
lemma bb91_12 : block fb91 12 0 2 = true := cl 6 (by decide +kernel)
lemma bb91_13 : block fb91 13 0 2 = true := cl 6 (by decide +kernel)
lemma bb91_15 : block fb91 15 0 1 = true := cl 5 (by decide +kernel)
lemma tb91 : checkedTables fb91 15 := by
 intro lv hlv;interval_cases lv
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . exact bb91_8
 . rfl
 . exact bb91_10
 . rfl
 . exact bb91_12
 . exact bb91_13
 . rfl
 . exact bb91_15
theorem l91 : Lower1 (vars 91) (graphGoal 91) 7 := lower_forest2 (g0:=fa91) (g1:=fb91) (hints:=65603) (before_sound k59 v59) ⟨rfl,rfl⟩ gm91 gm91 ta91 tb91 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def k91 := extendKnown k59 7 [(91,[]),(109,[96,33,65,48,81]),(155,[118])]
theorem v91 : Known k91 := extendKnown_ok v59 l91 (by decide +kernel)
theorem l107 : Lower1 (vars 107) (graphGoal 107) 6 := lower_discard (m:=107) (ci:=(2,0,105,0,5)) (hints:=83) (before_sound k91 v91) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def k107 := extendKnown k91 6 [(107,[])]
theorem v107 : Known k107 := extendKnown_ok v91 l107 (by decide +kernel)
def g171s : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffff800787f819fc91,0x44444440115c00),(0x787800661fa2,0x66666660441f80),(0x0,0x0),(0x78000798067f4,0x333333310023f0),(0x0,0x0),(0x78007f86078978,0x11111114028070),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffff8007f8124f,0xffffffffffffffffffffffffffffffffff8888888aa8000f)]
def g171c : IndexTree ColumnInfo := (.leaf [(1,0,170,0,5),(2,0,169,0,5),(8,0,163,0,5),(32,0,139,0,5)])
def g171a : Array (List Nat) := #[[],[80,49]]
def da171_12 (_ : Nat) := 0x3909f
def la171 : Nat -> Packing
| 12 => (1,0,2,0,da171_12)
| _ => emptyPacking
def ia171 : Nat -> Nat -> Option (Nat × Nat)
| _ => fun _ => none
def fa171 : Forest := ⟨171,6,fun j => g171s[j]?.getD (0,0),g171c,g171a,la171,ia171⟩
lemma ba171_12 : block fa171 12 0 1 = true := cl 5 (by decide +kernel)
lemma ta171 : checkedTables fa171 12 := by
 intro lv hlv;interval_cases lv
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . exact ba171_12
set_option maxHeartbeats 0 in
theorem gm171 : graphValid fa171 (boundsBefore k107) = true := by decide +kernel
def kb171_12 (_ : Nat) := 0
def db171_12 (_ : Nat) := 0x1af84fe44
def db171_15 (_ : Nat) := 0x3909f
def lb171 : Nat -> Packing
| 12 => (1,1,2,0,db171_12)
| 15 => (1,0,2,0,db171_15)
| _ => emptyPacking
def ib171 : Nat -> Nat -> Option (Nat × Nat)
| 12 => lookupWord 1 1 0 0 1 kb171_12
| _ => fun _ => none
def fb171 : Forest := ⟨171,7,fun j => g171s[j]?.getD (0,0),g171c,g171a,lb171,ib171⟩
lemma bb171_12 : block fb171 12 0 1 = true := cl 6 (by decide +kernel)
lemma bb171_15 : block fb171 15 0 1 = true := cl 5 (by decide +kernel)
lemma tb171 : checkedTables fb171 15 := by
 intro lv hlv;interval_cases lv
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . exact bb171_12
 . rfl
 . rfl
 . exact bb171_15
theorem l171 : Lower1 (vars 171) (graphGoal 171) 7 := lower_forest2 (g0:=fa171) (g1:=fb171) (hints:=83) (before_sound k107 v107) ⟨rfl,rfl⟩ gm171 gm171 ta171 tb171 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def k171 := extendKnown k107 7 [(171,[]),(173,[33]),(229,[33,67,99]),(230,[32,16,67,99]),(234,[32,16,65,49,99,83])]
theorem v171 : Known k171 := extendKnown_ok v107 l171 (by decide +kernel)
theorem l174 : Lower1 (vars 174) (graphGoal 174) 6 := lower_discard (m:=174) (ci:=(2,0,172,0,5)) (hints:=269514064) (before_sound k171 v171) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def k174 := extendKnown k171 6 [(174,[]),(206,[50,101]),(242,[113,66,99,50,81])]
theorem v174 : Known k174 := extendKnown_ok v171 l174 (by decide +kernel)
def g179s : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffff00f0f00ccfc9,0xcccccc088fc0),(0xf0f0f333e52,0x888888222e00),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffff00000f0033ff,0xffffffffffffffffffffffffffffffffffff7777770011ff),(0xf00ff0c3c4bc,0x222222814038),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffff000fc0927,0xffffffffffffffffffffffffffffffffffff111111540007)]
def g179c : IndexTree ColumnInfo := (.fork 3 (.leaf [(1,0,178,0,5),(16,0,163,0,5),(0,16,161,2,5)]) (.leaf [(32,0,147,0,4),(128,0,51,0,4),(18,0,161,0,4)]))
def g179a : Array (List Nat) := #[[],[117]]
def ka179_10 (_ : Nat) := 0
def da179_10 (_ : Nat) := 0x6403fd43
def da179_12 (_ : Nat) := 0x1aa09f
def la179 : Nat -> Packing
| 10 => (1,1,3,0,da179_10)
| 12 => (1,0,3,0,da179_12)
| _ => emptyPacking
def ia179 : Nat -> Nat -> Option (Nat × Nat)
| 10 => lookupWord 1 1 0 0 1 ka179_10
| _ => fun _ => none
def fa179 : Forest := ⟨179,6,fun j => g179s[j]?.getD (0,0),g179c,g179a,la179,ia179⟩
lemma ba179_10 : block fa179 10 0 1 = true := cl 6 (by decide +kernel)
lemma ba179_12 : block fa179 12 0 1 = true := cl 5 (by decide +kernel)
lemma ta179 : checkedTables fa179 12 := by
 intro lv hlv;interval_cases lv
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . exact ba179_10
 . rfl
 . exact ba179_12
set_option maxHeartbeats 0 in
theorem gm179 : graphValid fa179 (boundsBefore k174) = true := by decide +kernel
def kb179_8 (_ : Nat) := 0
def db179_8 (_ : Nat) := 0x2796095543
def kb179_10 (_ : Nat) := 0
def db179_10 (_ : Nat) := 0x10df95543
def kb179_12 (_ : Nat) := 0x4
def db179_12 (_ : Nat) := 0x9407a5fe33
def kb179_13 (_ : Nat) := 0
def db179_13 (_ : Nat) := 0x6403fd43
def db179_15 (_ : Nat) := 0x1aa09f
def lb179 : Nat -> Packing
| 8 => (1,3,3,0,db179_8)
| 10 => (1,2,3,0,db179_10)
| 12 => (1,1,3,0,db179_12)
| 13 => (1,1,3,0,db179_13)
| 15 => (1,0,3,0,db179_15)
| _ => emptyPacking
def ib179 : Nat -> Nat -> Option (Nat × Nat)
| 8 => lookupWord 1 1 0 0 1 kb179_8
| 10 => lookupWord 1 1 0 0 1 kb179_10
| 12 => lookupWord 1 2 1 0 1 kb179_12
| 13 => lookupWord 1 1 0 0 1 kb179_13
| _ => fun _ => none
def fb179 : Forest := ⟨179,7,fun j => g179s[j]?.getD (0,0),g179c,g179a,lb179,ib179⟩
lemma bb179_8 : block fb179 8 0 1 = true := cl 5 (by decide +kernel)
lemma bb179_10 : block fb179 10 0 1 = true := cl 6 (by decide +kernel)
lemma bb179_12 : block fb179 12 0 1 = true := cl 6 (by decide +kernel)
lemma bb179_13 : block fb179 13 0 1 = true := cl 6 (by decide +kernel)
lemma bb179_15 : block fb179 15 0 1 = true := cl 5 (by decide +kernel)
lemma tb179 : checkedTables fb179 15 := by
 intro lv hlv;interval_cases lv
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . exact bb179_8
 . rfl
 . exact bb179_10
 . rfl
 . exact bb179_12
 . exact bb179_13
 . rfl
 . exact bb179_15
theorem l179 : Lower1 (vars 179) (graphGoal 179) 7 := lower_forest2 (g0:=fa179) (g1:=fb179) (hints:=65605) (before_sound k174 v174) ⟨rfl,rfl⟩ gm179 gm179 ta179 tb179 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def k179 := extendKnown k174 7 [(179,[]),(182,[32]),(211,[101]),(218,[32,48,101])]
theorem v179 : Known k179 := extendKnown_ok v174 l179 (by decide +kernel)
theorem l186 : Lower1 (vars 186) (graphGoal 186) 6 := lower_discard (m:=186) (ci:=(8,0,178,0,5)) (hints:=269578304) (before_sound k179 v179) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def k186 := extendKnown k179 6 [(186,[]),(214,[50,101])]
theorem v186 : Known k186 := extendKnown_ok v179 l186 (by decide +kernel)
theorem l203 : Lower1 (vars 203) (graphGoal 203) 8 := lower_discard (m:=203) (ci:=(2,0,201,0,7)) (hints:=99) (before_sound k186 v186) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def k203 := extendKnown k186 8 [(203,[]),(233,[96,33,65,48,81])]
theorem v203 : Known k203 := extendKnown_ok v186 l203 (by decide +kernel)
theorem l205 : Lower1 (vars 205) (graphGoal 205) 8 := lower_discard (m:=205) (ci:=(4,0,201,0,7)) (hints:=1795) (before_sound k203 v203) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def k205 := extendKnown k203 8 [(205,[])]
theorem v205 : Known k205 := extendKnown_ok v203 l205 (by decide +kernel)
theorem l227 : Lower1 (vars 227) (graphGoal 227) 6 := lower_discard (m:=227) (ci:=(1,0,226,0,5)) (hints:=85) (before_sound k205 v205) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def k227 := extendKnown k205 6 [(227,[])]
theorem v227 : Known k227 := extendKnown_ok v205 l227 (by decide +kernel)
def g236s : Array (Bits × Bits) := #[(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffc0007c1f033e791,0x294a5294022e380),(0xf83e00ccfca2,0x318c6318088fc00),(0x0,0x0),(0x1f0001f3033d74,0x14a5294a2011c70),(0x3e0003e0c0c4bf8,0xc6318c680403f0),(0xffffffffffffffffffffffffffffffffffffffc00ff0924f,0xfffffffffffffffffffffffffffffffffc2108421550000f)]
def g236c : IndexTree ColumnInfo := (.fork 3 (.leaf [(4,0,232,0,5),(8,0,228,0,5),(32,0,204,0,5)]) (.leaf [(64,0,172,0,5),(36,0,200,0,4),(72,0,164,0,4)]))
def g236a : Array (List Nat) := #[[],[99],[50,101],[50,82,98],[82],[82,99],[98,50,83],[98,83]]
def ka236_8 (_ : Nat) := 0x100
def da236_8 (_ : Nat) := 0x26d6215110
def ka236_10 (_ : Nat) := 0x980040082200
def da236_10 (_ : Nat) := 0x31080110542f3c17d54442f8a8887e50110
def ka236_12 (_ : Nat) := 0x201a9506d005440
def da236_12 (_ : Nat) := 0xc5068a2d0fd40fd10
def da236_14 (_ : Nat) := 0xb05f
def la236 : Nat -> Packing
| 8 => (1,3,3,0,da236_8)
| 10 => (3,2,3,5,da236_10)
| 12 => (2,1,3,4,da236_12)
| 14 => (1,0,3,0,da236_14)
| _ => emptyPacking
def ia236 : Nat -> Nat -> Option (Nat × Nat)
| 8 => lookupWord 2 3 2 0 3 ka236_8
| 10 => lookupWord 4 8 3 2 3 ka236_10
| 12 => lookupWord 5 10 4 1 3 ka236_12
| _ => fun _ => none
def fa236 : Forest := ⟨236,7,fun j => g236s[j]?.getD (0,0),g236c,g236a,la236,ia236⟩
lemma ba236_8 : block fa236 8 0 1 = true := cl 5 (by decide +kernel)
lemma ba236_10 : block fa236 10 0 3 = true := cl 6 (by decide +kernel)
lemma ba236_12 : block fa236 12 0 2 = true := cl 6 (by decide +kernel)
lemma ba236_14 : block fa236 14 0 1 = true := cl 5 (by decide +kernel)
lemma ta236 : checkedTables fa236 14 := by
 intro lv hlv;interval_cases lv
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . exact ba236_8
 . rfl
 . exact ba236_10
 . rfl
 . exact ba236_12
 . rfl
 . exact ba236_14
set_option maxHeartbeats 0 in
theorem gm236 : graphValid fa236 (boundsBefore k227) = true := by decide +kernel
def kb236_8 (_ : Nat) := 0x20
def db236_8 (_ : Nat) := 0x11b5ca6655110
def kb236_10 (_ : Nat) := 0x1090e000010648d0b002050c0010a050c00080000822
def db236_10 (_ : Nat) := 0x82000030840054100030801527ca8ad17aa3e68a8a0a02ed6295540db58a555027d61955409f999544427e66151109f592554427c6495510de541409127d65442449f195109127d61152009f195418026d6295540
def kb236_11 (_ : Nat) := 0x100
def db236_11 (_ : Nat) := 0x26d6215110
def kb236_12 (_ : Nat) := 0x7c2053000a03327011a380088526482240020c504350754ae7200200000008860
def db236_12 (_ : Nat) := 0x281004480814208040584630d075a086160c6120e5a1df5b97d2cdca05003fcaaa07f95510fea8489fd40913fa21227f50600bf2aa817e55442faa1225f15200
def kb236_13 (_ : Nat) := 0x980040082200
def db236_13 (_ : Nat) := 0x31080110542f3c17d54442f8a8887e50110
def kb236_14 (_ : Nat) := 0x189002084
def db236_14 (_ : Nat) := 0x3705a82d0fe44fe00
def kb236_15 (_ : Nat) := 0x201a9506d005440
def db236_15 (_ : Nat) := 0xc506a82d0fd40fd10
def db236_17 (_ : Nat) := 0xb05f
def lb236 : Nat -> Packing
| 8 => (1,4,3,0,db236_8)
| 10 => (13,3,3,7,db236_10)
| 11 => (1,3,3,0,db236_11)
| 12 => (10,2,3,8,db236_12)
| 13 => (3,2,3,5,db236_13)
| 14 => (2,1,3,4,db236_14)
| 15 => (2,1,3,4,db236_15)
| 17 => (1,0,3,0,db236_17)
| _ => emptyPacking
def ib236 : Nat -> Nat -> Option (Nat × Nat)
| 8 => lookupWord 2 3 2 0 3 kb236_8
| 10 => lookupWord 9 19 5 4 3 kb236_10
| 11 => lookupWord 2 3 2 0 3 kb236_11
| 12 => lookupWord 12 29 5 4 3 kb236_12
| 13 => lookupWord 4 8 3 2 3 kb236_13
| 14 => lookupWord 3 6 3 1 3 kb236_14
| 15 => lookupWord 5 10 4 1 3 kb236_15
| _ => fun _ => none
def fb236 : Forest := ⟨236,8,fun j => g236s[j]?.getD (0,0),g236c,g236a,lb236,ib236⟩
lemma bb236_8 : block fb236 8 0 1 = true := cl 5 (by decide +kernel)
lemma sb236_10_0 : block fb236 10 0 1 = true := cl 5 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sb236_10_1 : block fb236 10 1 12 = true := cl 6 (by decide +kernel)
lemma bb236_10 : block fb236 10 0 13 = true := (@block_merge fb236 10 0 1 12 (sb236_10_0) sb236_10_1)
lemma bb236_11 : block fb236 11 0 1 = true := cl 5 (by decide +kernel)
lemma sb236_12_0 : block fb236 12 0 4 = true := cl 6 (by decide +kernel)
lemma sb236_12_1 : block fb236 12 4 6 = true := cl 7 (by decide +kernel)
lemma bb236_12 : block fb236 12 0 10 = true := (@block_merge fb236 12 0 4 6 (sb236_12_0) sb236_12_1)
lemma bb236_13 : block fb236 13 0 3 = true := cl 6 (by decide +kernel)
lemma bb236_14 : block fb236 14 0 2 = true := cl 6 (by decide +kernel)
lemma bb236_15 : block fb236 15 0 2 = true := cl 6 (by decide +kernel)
lemma bb236_17 : block fb236 17 0 1 = true := cl 5 (by decide +kernel)
lemma tb236 : checkedTables fb236 17 := by
 intro lv hlv;interval_cases lv
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . exact bb236_8
 . rfl
 . exact bb236_10
 . exact bb236_11
 . exact bb236_12
 . exact bb236_13
 . exact bb236_14
 . exact bb236_15
 . rfl
 . exact bb236_17
theorem l236 : Lower1 (vars 236) (graphGoal 236) 8 := lower_forest2 (g0:=fa236) (g1:=fb236) (hints:=589325568) (before_sound k227 v227) ⟨rfl,rfl⟩ gm236 gm236 ta236 tb236 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def k236 := extendKnown k227 8 [(236,[])]
theorem v236 : Known k236 := extendKnown_ok v227 l236 (by decide +kernel)
def g63s : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffc00f83e19f3c9,0x294a5281171c0),(0x1f07c0667e52,0x318c630447e00),(0x3e00001807ffc,0x3def7bd007ff8),(0xfffffffffffffffffffffffffffffffffffc00003e019ebf,0xfffffffffffffffffffffffffffffffffffd6b5ad6008e3f),(0xfffffffffffffffffffffffffffffffffffc0007c00625ff,0xfffffffffffffffffffffffffffffffffffce739ce0201ff),(0xfffffffffffffffffffffffffffffffffffffff801f84927,0xfffffffffffffffffffffffffffffffffffc210842a80007),(0x0,0x0),(0x0,0x0)]
def g63c : IndexTree ColumnInfo := (.fork 3 (.leaf [(4,0,59,0,5),(8,0,55,0,5),(0,8,54,1,5)]) (.leaf [(16,0,47,0,5),(0,16,45,2,5),(9,0,54,0,4),(18,0,45,0,4)]))
def g63a : Array (List Nat) := #[[],[16,67]]
def da63_12 (_ : Nat) := 0x221a97f
def la63 : Nat -> Packing
| 12 => (1,0,3,0,da63_12)
| _ => emptyPacking
def ia63 : Nat -> Nat -> Option (Nat × Nat)
| _ => fun _ => none
def fa63 : Forest := ⟨63,6,fun j => g63s[j]?.getD (0,0),g63c,g63a,la63,ia63⟩
lemma ba63_12 : block fa63 12 0 1 = true := cl 6 (by decide +kernel)
lemma ta63 : checkedTables fa63 12 := by
 intro lv hlv;interval_cases lv
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . exact ba63_12
set_option maxHeartbeats 0 in
theorem gm63 : graphValid fa63 (boundsBefore k236) = true := by decide +kernel
def kb63_10 (_ : Nat) := 0
def db63_10 (_ : Nat) := 0xbb58a55
def kb63_12 (_ : Nat) := 0
def db63_12 (_ : Nat) := 0xc45fe55
def db63_15 (_ : Nat) := 0x221a97f
def lb63 : Nat -> Packing
| 10 => (1,2,3,0,db63_10)
| 12 => (1,1,3,0,db63_12)
| 15 => (1,0,3,0,db63_15)
| _ => emptyPacking
def ib63 : Nat -> Nat -> Option (Nat × Nat)
| 10 => lookupWord 1 1 0 0 1 kb63_10
| 12 => lookupWord 1 1 0 0 1 kb63_12
| _ => fun _ => none
def fb63 : Forest := ⟨63,7,fun j => g63s[j]?.getD (0,0),g63c,g63a,lb63,ib63⟩
lemma bb63_10 : block fb63 10 0 1 = true := cl 6 (by decide +kernel)
lemma bb63_12 : block fb63 12 0 1 = true := cl 7 (by decide +kernel)
lemma bb63_15 : block fb63 15 0 1 = true := cl 6 (by decide +kernel)
lemma tb63 : checkedTables fb63 15 := by
 intro lv hlv;interval_cases lv
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . exact bb63_10
 . rfl
 . exact bb63_12
 . rfl
 . rfl
 . exact bb63_15
theorem l63 : Lower1 (vars 63) (graphGoal 63) 7 := lower_forest2 (g0:=fa63) (g1:=fb63) (hints:=66883) (before_sound k236 v236) ⟨rfl,rfl⟩ gm63 gm63 ta63 tb63 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def k63 := extendKnown k236 7 [(63,[]),(126,[96,81,50,66,16])]
theorem v63 : Known k63 := extendKnown_ok v236 l63 (by decide +kernel)
theorem l111 : Lower1 (vars 111) (graphGoal 111) 8 := lower_discard (m:=111) (ci:=(2,0,109,0,7)) (hints:=1363) (before_sound k63 v63) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def k111 := extendKnown k63 8 [(111,[]),(123,[96,81,66])]
theorem v111 : Known k111 := extendKnown_ok v63 l111 (by decide +kernel)
def g119s : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffff0f00f030cfc9,0xcccccc208fc0),(0xf00f0fc33e52,0x888888822e00),(0xf0000c0ffc,0xeeeeee080ff8),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffff00000f0033ff,0xffffffffffffffffffffffffffffffffffff7777770011ff),(0xffffffffffffffffffffffffffffffffffff00fff00fc4a7,0xffffffffffffffffffffffffffffffffffff111111054007),(0xffffffffffffffffffffffffffffffffffffff0000f0093f,0xffffffffffffffffffffffffffffffffffff33333350003f),(0x0,0x0)]
def g119c : IndexTree ColumnInfo := (.fork 2 (.leaf [(1,0,118,0,5),(0,16,101,2,5)]) (.leaf [(64,0,55,0,5),(18,0,101,0,4),(36,0,83,0,4)]))
def g119a : Array (List Nat) := #[[],[96,81,66]]
def da119_12 (_ : Nat) := 0x11193f
def la119 : Nat -> Packing
| 12 => (1,0,3,0,da119_12)
| _ => emptyPacking
def ia119 : Nat -> Nat -> Option (Nat × Nat)
| _ => fun _ => none
def fa119 : Forest := ⟨119,6,fun j => g119s[j]?.getD (0,0),g119c,g119a,la119,ia119⟩
lemma ba119_12 : block fa119 12 0 1 = true := cl 6 (by decide +kernel)
lemma ta119 : checkedTables fa119 12 := by
 intro lv hlv;interval_cases lv
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . exact ba119_12
set_option maxHeartbeats 0 in
theorem gm119 : graphValid fa119 (boundsBefore k111) = true := by decide +kernel
def db119_15 (_ : Nat) := 0x21193f
def lb119 : Nat -> Packing
| 15 => (1,0,3,0,db119_15)
| _ => emptyPacking
def ib119 : Nat -> Nat -> Option (Nat × Nat)
| _ => fun _ => none
def fb119 : Forest := ⟨119,7,fun j => g119s[j]?.getD (0,0),g119c,g119a,lb119,ib119⟩
lemma bb119_15 : block fb119 15 0 1 = true := cl 6 (by decide +kernel)
lemma tb119 : checkedTables fb119 15 := by
 intro lv hlv;interval_cases lv
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . exact bb119_15
theorem l119 : Lower1 (vars 119) (graphGoal 119) 7 := lower_forest2 (g0:=fa119) (g1:=fb119) (hints:=66885) (before_sound k111 v111) ⟨rfl,rfl⟩ gm119 gm119 ta119 tb119 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def k119 := extendKnown k111 7 [(119,[])]
theorem v119 : Known k119 := extendKnown_ok v111 l119 (by decide +kernel)
theorem l183 : Lower1 (vars 183) (graphGoal 183) 8 := lower_discard (m:=183) (ci:=(1,0,182,0,7)) (hints:=66885) (before_sound k119 v119) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def k183 := extendKnown k119 8 [(183,[])]
theorem v183 : Known k183 := extendKnown_ok v119 l183 (by decide +kernel)
def g187s : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffff8000f83e0f8199f8f91,0x5294a5294a011178780),(0x1f07c1f006667f8a2,0x6318c6318c04447f800),(0x0,0x0),(0x3e000000f98018f974,0x294a5294a5100087870),(0xfffffffffffffffffffffffffffff80000001f00006117ff,0xfffffffffffffffffffffffffffff9ce739ce738002007ff),(0x7c0007fe00607822278,0x842108421402800070),(0x0,0x0),(0xffffffffffffffffffffffffffffffffff800007f804444f,0xfffffffffffffffffffffffffffff8421084210aa800000f)]
def g187c : IndexTree ColumnInfo := (.fork 4 (.leaf [(8,0,179,0,7),(16,0,171,0,7),(32,0,155,0,7),(0,16,169,2,6)]) (.fork 2 (.leaf [(1,0,186,0,6),(2,0,169,0,5)]) (.leaf [(128,0,59,0,5),(18,0,169,0,5),(2,16,169,0,5)])))
def g187a : Array (List Nat) := #[[]]
def ka187_12 (_ : Nat) := 0x46200
def da187_12 (_ : Nat) := 0x2090410200c444818c86238ab8b80f754d50bf59510fd54510fe54110
def ka187_14 (_ : Nat) := 0x2d4
def da187_14 (_ : Nat) := 0x2251810a589250299128c0b282284aadcc80fea8ff543fa21dd53
def da187_16 (_ : Nat) := 0x3908217f
def la187 : Nat -> Packing
| 12 => (4,2,4,7,da187_12)
| 14 => (4,1,4,7,da187_14)
| 16 => (1,0,4,0,da187_16)
| _ => emptyPacking
def ia187 : Nat -> Nat -> Option (Nat × Nat)
| 12 => lookupWord 3 5 3 2 0 ka187_12
| 14 => lookupWord 2 4 2 2 0 ka187_14
| _ => fun _ => none
def fa187 : Forest := ⟨187,8,fun j => g187s[j]?.getD (0,0),g187c,g187a,la187,ia187⟩
lemma ba187_12 : block fa187 12 0 4 = true := cl 7 (by decide +kernel)
lemma sa187_14_0 : block fa187 14 0 1 = true := cl 6 (by decide +kernel)
lemma sa187_14_1 : block fa187 14 1 3 = true := cl 7 (by decide +kernel)
lemma ba187_14 : block fa187 14 0 4 = true := (@block_merge fa187 14 0 1 3 (sa187_14_0) sa187_14_1)
lemma ba187_16 : block fa187 16 0 1 = true := cl 6 (by decide +kernel)
lemma ta187 : checkedTables fa187 16 := by
 intro lv hlv;interval_cases lv
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . exact ba187_12
 . rfl
 . exact ba187_14
 . rfl
 . exact ba187_16
set_option maxHeartbeats 0 in
theorem gm187 : graphValid fa187 (boundsBefore k183) = true := by
 simp only [graphValid,Bool.and_eq_true]
 refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=0) ?_⟩
 all_goals simp only [listPieces]
 all_goals repeat' apply And.intro
 all_goals decide +kernel
def kb187_10 (_ : Nat) := 0x211
def db187_10 (_ : Nat) := 0x29433354d72999508bd849dd654423b60a7759510
def kb187_12 (_ : Nat) := 0xe800173a74c59020a020842000000
def db187_12 (_ : Nat) := 0x10000841841840840041868040841cb88a3a09f5e1b1815120f0c090604c027eb84cca8ded7299950dbaa7332a1bb5ca665427eb8ccca84fe77595109faeb332213f1d9109567eb80cb08cfc7654211dbac6a84233f5c4658027e3b2a3004ed7299950
def kb187_14 (_ : Nat) := 0x3a408245c208d4503160819af241c110040
def db187_14 (_ : Nat) := 0xc6818626030c42311a30b0310485018830f8884150106222c0c4c32a082e12639146c32a080c19303486032c4610a0642e23144c3220818986390c6906c3260b9602e84815ee75dba675805a5524d5123d4cc2a4861a44007400ff99951ff99950ff99910ff54655ff54255ff44255ff54211ff54600bf99951bf99950bf99910f754e55bf58655bf58255bf19611bf19600f754e00b758e11
def kb187_15 (_ : Nat) := 0x46200
def db187_15 (_ : Nat) := 0x2090410200c444818c86238ab8b80f754d50bf59510fd54510fe54110
def kb187_16 (_ : Nat) := 0x120
def db187_16 (_ : Nat) := 0x5cd484a26a424825e51810bbbc07f957fc23fe00
def kb187_17 (_ : Nat) := 0x2d4
def db187_17 (_ : Nat) := 0x824a0729651810a644650390f494104bf04c80fea8ff543fa21dd53
def db187_19 (_ : Nat) := 0x3a10817f
def lb187 : Nat -> Packing
| 10 => (3,4,4,4,db187_10)
| 12 => (14,3,4,8,db187_12)
| 14 => (18,2,4,10,db187_14)
| 15 => (4,2,4,7,db187_15)
| 16 => (3,1,4,6,db187_16)
| 17 => (4,1,4,7,db187_17)
| 19 => (1,0,4,0,db187_19)
| _ => emptyPacking
def ib187 : Nat -> Nat -> Option (Nat × Nat)
| 10 => lookupWord 2 4 2 2 0 kb187_10
| 12 => lookupWord 9 18 5 4 0 kb187_12
| 14 => lookupWord 8 20 5 5 0 kb187_14
| 15 => lookupWord 3 5 3 2 0 kb187_15
| 16 => lookupWord 2 4 2 2 0 kb187_16
| 17 => lookupWord 2 4 2 2 0 kb187_17
| _ => fun _ => none
def fb187 : Forest := ⟨187,9,fun j => g187s[j]?.getD (0,0),g187c,g187a,lb187,ib187⟩
lemma bb187_10 : block fb187 10 0 3 = true := cl 6 (by decide +kernel)
lemma sb187_12_0 : block fb187 12 0 1 = true := cl 6 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sb187_12_1 : block fb187 12 1 13 = true := cl 7 (by decide +kernel)
lemma bb187_12 : block fb187 12 0 14 = true := (@block_merge fb187 12 0 1 13 (sb187_12_0) sb187_12_1)
lemma sb187_14_0 : block fb187 14 0 1 = true := cl 6 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sb187_14_1 : block fb187 14 1 9 = true := cl 7 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sb187_14_2 : block fb187 14 10 8 = true := cl 8 (by decide +kernel)
lemma bb187_14 : block fb187 14 0 18 = true := (@block_merge fb187 14 0 10 8 ((@block_merge fb187 14 0 1 9 (sb187_14_0) sb187_14_1)) sb187_14_2)
lemma bb187_15 : block fb187 15 0 4 = true := cl 7 (by decide +kernel)
lemma bb187_16 : block fb187 16 0 3 = true := cl 7 (by decide +kernel)
lemma sb187_17_0 : block fb187 17 0 1 = true := cl 6 (by decide +kernel)
lemma sb187_17_1 : block fb187 17 1 3 = true := cl 7 (by decide +kernel)
lemma bb187_17 : block fb187 17 0 4 = true := (@block_merge fb187 17 0 1 3 (sb187_17_0) sb187_17_1)
lemma bb187_19 : block fb187 19 0 1 = true := cl 6 (by decide +kernel)
lemma tb187 : checkedTables fb187 19 := by
 intro lv hlv;interval_cases lv
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . exact bb187_10
 . rfl
 . exact bb187_12
 . rfl
 . exact bb187_14
 . exact bb187_15
 . exact bb187_16
 . exact bb187_17
 . rfl
 . exact bb187_19
theorem l187 : Lower1 (vars 187) (graphGoal 187) 9 := lower_forest2 (g0:=fa187) (g1:=fb187) (hints:=65603) (before_sound k183 v183) ⟨rfl,rfl⟩ gm187 gm187 ta187 tb187 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def k187 := extendKnown k183 9 [(187,[])]
theorem v187 : Known k187 := extendKnown_ok v183 l187 (by decide +kernel)
def g219s : Array (Bits × Bits) := #[(0xffffffffffffffffffffffff00003f000fc0fc0c33f1f111,0xa28a28a28a28a00822f0f000),(0xfc003f03f0030ccff1222,0xc30c30c30c30c02088ff0000),(0x0,0x0),(0x3f000fc0000fcc3031f2f44,0x5145145145145082010f0f00),(0xffffffffffffffffffffffff00000000003f00000c22ffff,0xffffffffffffffffffffffff3cf3cf3cf3cf3c000400ffff),(0x0,0x0),(0xfc0000ffffc00303f04444f8,0x820820820820a01500000f0),(0xffffffffffffffffffffffffffffff00000003fc0088888f,0xffffffffffffffffffffffff04104104104105540000000f)]
def g219c : IndexTree ColumnInfo := (.fork 6 (.fork 3 (.leaf [(16,0,203,0,8),(0,16,201,2,8),(8,0,211,0,7)]) (.leaf [(1,0,218,0,7),(64,0,155,0,7),(128,0,91,0,7)])) (.fork 3 (.leaf [(18,0,201,0,7),(9,0,210,0,5),(72,0,147,0,4)]) (.leaf [(136,0,83,0,4),(65,0,154,0,4),(129,0,90,0,4)])))
def g219a : Array (List Nat) := #[[],[118],[48],[48,118]]
def ka219_10 (_ : Nat) := 0xb484001c77501404100000000100c2000003
def da219_10 (_ : Nat) := 0x4084840820c6c7d2140b398550950503ca5494254140e396555140483ca5515250120da97550940483aa5954250120
def ka219_12 (_ : Nat) := 0x86019233594a40009023a03d000012ca0000254d81471000084220080000000
def da219_12 (_ : Nat) := 0x24208200050820840804861f1ec9090f8f6444998d817c776b5f534e422100dd8e4b2a81cf551525035eb2a84a07b942541409faecaa241af59154482fcbaa80906f96550120f72a8a0241fa549404839caa2a0a07a94250120
def ka219_14 (_ : Nat) := 0x714602a000210949900d000400042948304420ce00004130848
def da219_14 (_ : Nat) := 0x498a499120a412423a88c44c42d878c6aec4c634b6249b2a3171d878eca444dacfc4b99c85684b341d00ff58154ff59540ff58940ff54940ff55120bf59540ef55140ef50940fe54140bf59120fe50120
def ka219_16 (_ : Nat) := 0x5102009d040
def da219_16 (_ : Nat) := 0x8ca65258d1ac864b1a838d8e5827807f553fa81fd20
def da219_18 (_ : Nat) := 0x2093197f
def la219 : Nat -> Packing
| 10 => (6,4,4,6,da219_10)
| 12 => (12,3,4,8,da219_12)
| 14 => (11,2,4,8,da219_14)
| 16 => (3,1,4,7,da219_16)
| 18 => (1,0,4,0,da219_18)
| _ => emptyPacking
def ia219 : Nat -> Nat -> Option (Nat × Nat)
| 10 => lookupWord 12 18 5 3 2 ka219_10
| 12 => lookupWord 14 31 5 4 2 ka219_12
| 14 => lookupWord 10 26 5 4 2 ka219_14
| 16 => lookupWord 4 8 3 2 2 ka219_16
| _ => fun _ => none
def fa219 : Forest := ⟨219,9,fun j => g219s[j]?.getD (0,0),g219c,g219a,la219,ia219⟩
lemma ba219_10 : block fa219 10 0 6 = true := cl 6 (by decide +kernel)
lemma sa219_12_0 : block fa219 12 0 2 = true := cl 6 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sa219_12_1 : block fa219 12 2 10 = true := cl 7 (by decide +kernel)
lemma ba219_12 : block fa219 12 0 12 = true := (@block_merge fa219 12 0 2 10 (sa219_12_0) sa219_12_1)
lemma sa219_14_0 : block fa219 14 0 6 = true := cl 7 (by decide +kernel)
lemma sa219_14_1 : block fa219 14 6 5 = true := cl 8 (by decide +kernel)
lemma ba219_14 : block fa219 14 0 11 = true := (@block_merge fa219 14 0 6 5 (sa219_14_0) sa219_14_1)
lemma ba219_16 : block fa219 16 0 3 = true := cl 7 (by decide +kernel)
lemma ba219_18 : block fa219 18 0 1 = true := cl 6 (by decide +kernel)
lemma ta219 : checkedTables fa219 18 := by
 intro lv hlv;interval_cases lv
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . exact ba219_10
 . rfl
 . exact ba219_12
 . rfl
 . exact ba219_14
 . rfl
 . exact ba219_16
 . rfl
 . exact ba219_18
set_option maxHeartbeats 0 in
theorem gm219 : graphValid fa219 (boundsBefore k187) = true := by
 simp only [graphValid,Bool.and_eq_true]
 refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=0) ?_⟩
 all_goals simp only [listPieces]
 all_goals repeat' apply And.intro
 all_goals decide +kernel
def kb219_10 (_ : Nat) := 0x134101210c203
def db219_10 (_ : Nat) := 0x28f51418e872602775954087cc8510bb2a89069a2195254120912c592caa2a4a1401c2c765515250a00
def kb219_12 (_ : Nat) := 0x14047140a37386920a1049806400151e88c80030400e0c2194b6844d131690b8c0e58701c009007080000009241
def db219_12 (_ : Nat) := 0xe4f1100002041000040004082c2380c8c905e2100071080d8810602100000411207e018000002840281f1f015328f3a96ca2371688c11ced262b01568e409f0ee7232920863e1c8d04e220a8027b60a77581549ed829dd655027e6027759540aed829dd655033b1ca7759540af9809dd655023f60a7759540ced829dd65502ee6027755140f3a8855150503ce55150999408fd859dd644823fa2176551208fd869dd54483ea50a77501208fc87552664823f6087654244c7c76549509123f2197548244af88654120913da54950482448fd821d9548023f6147650a008fc865d542802af2195450a00cbc76551428033b1d95250a00f2d54549428023b60a7759540
def kb219_13 (_ : Nat) := 0xb484001c77501404100000000100c2000003
def db219_13 (_ : Nat) := 0x4084840820c6c7d2140b398550950503ca5494254140e396555140483ca5515250120da97550940483aa5954250120
def kb219_14 (_ : Nat) := 0x15000001c066a540000600002240051336934387449386800002400580080734e7e78404d262866201168021c5418007828143c20000c0000006c44005e747c002c08340002303018d060c0000004000000000300000020010011020000000040800200103
def db219_14 (_ : Nat) := 0x285e4e240617210e25074190f83310b08a162091580c38810514c861050810a10a082062842848838a103218838c18a1070ad1890960450c8112e0850ca97007244a9c44962420642a9610ca25883e597276255c80b1f1ec6e20bb0a205e2cbb0a285a98b1f1ec6e209276202ec8f8902f1ec8c9bfeaf9ee558f61778dbd625634f5173c4cb25c630f3faee368c9b00afa8a95a146d974490c621042005fe7758154bfae1332a9bf582665537eb84ccaa5fe7759540dfceeb2a81ef9dd54502ff3bac4a06fd6599940f7aa933281bf58a66503dea14cca07f95099940dfaa533281bf9dd64482ff3baa8907fa7750120dfaa933241df54950912febaa41227f95048244df8ecaa4017f5d542803deaa285007ed5250a009fae1332a93f9dd655027ebaccca04fd72999409fceeb22413f1d9509127e3b2a9004fc7650a00
def kb219_15 (_ : Nat) := 0x86019233594a40009023a03d000012ca0000254d81471000084220080000000
def db219_15 (_ : Nat) := 0x484104000a10410810090f18693b13887ec392867a757064584c473b1a00dd8e4b2a81cf551525035eb2a84a07b942541409faecaa241af59154482fcbaa80906f96550120f72a8a0241fa549404839caa2a0a07a94250120
def kb219_16 (_ : Nat) := 0x438d326b2a2911c81880800358018020
def db219_16 (_ : Nat) := 0x25cb3c64d8cae39091ec51cb1714a24e4d90acb8a43ed21d2885c54da3390aca26296d1a32ce59362e3a9594726c7174c761cb6c9ec21b2aa3a9484600ff99954ff99940ff54244ff48244ff55200ff50a00bf99954bf99940bf99920
def kb219_17 (_ : Nat) := 0x714602a000210949900d000400042948304420ce00004130848
def db219_17 (_ : Nat) := 0x498a49915484904908ea231102564da32e2aed19314b68c8ac9b0c5c548b68cd8a9b0e4feede2d7ba977a5d461d00ff58154ff59540ff58940ff54940ff55120bf59540ef55140ef50940fe54140bf59120fe50120
def kb219_18 (_ : Nat) := 0xc4200
def db219_18 (_ : Nat) := 0x2c644b4cc5a46d219a303fc89fe00
def kb219_19 (_ : Nat) := 0x5102009d040
def db219_19 (_ : Nat) := 0x8ce45258d1ac864b1a838d8e5827807f553fa81fd20
def db219_21 (_ : Nat) := 0x2099317f
def lb219 : Nat -> Packing
| 10 => (5,5,4,5,db219_10)
| 12 => (29,4,4,9,db219_12)
| 13 => (6,4,4,6,db219_13)
| 14 => (33,3,4,10,db219_14)
| 15 => (12,3,4,8,db219_15)
| 16 => (9,2,4,9,db219_16)
| 17 => (11,2,4,8,db219_17)
| 18 => (2,1,4,6,db219_18)
| 19 => (3,1,4,7,db219_19)
| 21 => (1,0,4,0,db219_21)
| _ => emptyPacking
def ib219 : Nat -> Nat -> Option (Nat × Nat)
| 10 => lookupWord 3 8 3 3 2 kb219_10
| 12 => lookupWord 15 39 6 5 2 kb219_12
| 13 => lookupWord 12 18 5 3 2 kb219_13
| 14 => lookupWord 34 72 7 6 2 kb219_14
| 15 => lookupWord 14 31 5 4 2 kb219_15
| 16 => lookupWord 7 17 5 4 2 kb219_16
| 17 => lookupWord 10 26 5 4 2 kb219_17
| 18 => lookupWord 3 5 3 1 2 kb219_18
| 19 => lookupWord 4 8 3 2 2 kb219_19
| _ => fun _ => none
def fb219 : Forest := ⟨219,10,fun j => g219s[j]?.getD (0,0),g219c,g219a,lb219,ib219⟩
lemma bb219_10 : block fb219 10 0 5 = true := cl 6 (by decide +kernel)
lemma sb219_12_0 : block fb219 12 0 1 = true := cl 6 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sb219_12_1 : block fb219 12 1 28 = true := cl 7 (by decide +kernel)
lemma bb219_12 : block fb219 12 0 29 = true := (@block_merge fb219 12 0 1 28 (sb219_12_0) sb219_12_1)
lemma bb219_13 : block fb219 13 0 6 = true := cl 6 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sb219_14_0 : block fb219 14 0 8 = true := cl 7 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sb219_14_1 : block fb219 14 8 25 = true := cl 8 (by decide +kernel)
lemma bb219_14 : block fb219 14 0 33 = true := (@block_merge fb219 14 0 8 25 (sb219_14_0) sb219_14_1)
lemma sb219_15_0 : block fb219 15 0 2 = true := cl 6 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sb219_15_1 : block fb219 15 2 10 = true := cl 7 (by decide +kernel)
lemma bb219_15 : block fb219 15 0 12 = true := (@block_merge fb219 15 0 2 10 (sb219_15_0) sb219_15_1)
lemma sb219_16_0 : block fb219 16 0 3 = true := cl 7 (by decide +kernel)
lemma sb219_16_1 : block fb219 16 3 6 = true := cl 8 (by decide +kernel)
lemma bb219_16 : block fb219 16 0 9 = true := (@block_merge fb219 16 0 3 6 (sb219_16_0) sb219_16_1)
lemma sb219_17_0 : block fb219 17 0 6 = true := cl 7 (by decide +kernel)
lemma sb219_17_1 : block fb219 17 6 5 = true := cl 8 (by decide +kernel)
lemma bb219_17 : block fb219 17 0 11 = true := (@block_merge fb219 17 0 6 5 (sb219_17_0) sb219_17_1)
lemma bb219_18 : block fb219 18 0 2 = true := cl 7 (by decide +kernel)
lemma bb219_19 : block fb219 19 0 3 = true := cl 7 (by decide +kernel)
lemma bb219_21 : block fb219 21 0 1 = true := cl 6 (by decide +kernel)
lemma tb219 : checkedTables fb219 21 := by
 intro lv hlv;interval_cases lv
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . exact bb219_10
 . rfl
 . exact bb219_12
 . exact bb219_13
 . exact bb219_14
 . exact bb219_15
 . exact bb219_16
 . exact bb219_17
 . exact bb219_18
 . exact bb219_19
 . rfl
 . exact bb219_21
theorem l219 : Lower1 (vars 219) (graphGoal 219) 10 := lower_forest2 (g0:=fa219) (g1:=fb219) (hints:=65603) (before_sound k187 v187) ⟨rfl,rfl⟩ gm219 gm219 ta219 tb219 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def k219 := extendKnown k187 10 [(219,[])]
theorem v219 : Known k219 := extendKnown_ok v187 l219 (by decide +kernel)
def g235s : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffc00003e007c1ff80619fe2221,0x21084210842108004115e0000),(0x7c00f83e00018661fe442,0x318c6318c6318c010441fe000),(0x0,0x0),(0xf801f00000f8618063fe84,0x18c6318c6318c60410021fe00),(0x0,0x0),(0x1f00000003ff018007845fe8,0xc6318c6318c6310002801fe0),(0x3e00001fffc000601f80889f0,0x4210842108421400a80001e0),(0xfffffffffffffffffffffffffffffe00000007fe0011111f,0xfffffffffffffffffffffffc2108421084210aaa0000001f)]
def g235c : IndexTree ColumnInfo := (.fork 10 (.fork 5 (.fork 2 (.leaf [(2,0,233,0,8),(32,0,203,0,8)]) (.leaf [(1,0,234,0,7),(64,0,171,0,7),(34,0,201,0,7)])) (.fork 2 (.leaf [(128,0,107,0,6),(8,0,227,0,6)]) (.leaf [(9,0,226,0,5),(33,0,202,0,5),(65,0,170,0,5)]))) (.fork 5 (.fork 2 (.leaf [(10,0,225,0,5),(3,0,232,0,5)]) (.leaf [(66,0,169,0,5),(130,0,105,0,5),(72,0,163,0,5)])) (.fork 3 (.leaf [(96,0,139,0,5),(129,0,106,0,4),(192,0,43,0,4)]) (.leaf [(35,0,200,0,4),(73,0,162,0,4),(98,0,137,0,4)]))))
def g235a : Array (List Nat) := #[[],[96,81]]
def ka235_10 (_ : Nat) := 0x101c000ac980048cb2b004c3ec97580201008010c80
def da235_10 (_ : Nat) := 0x128500a6122c28708304112c0842308bc2009867e6a31d59d655118bc844c38038d5956455110dd1755c143443cc5915454110dd18750d50443d46154354110f917450d50443e45914354110f915450d50443d85895254110f316555140443e45954350110f115450d50443645d54350110
def ka235_12 (_ : Nat) := 0x5c02c0018911014b400000652136c633540a38988303348d59501a0050070213c00000000800006661000420801c0003000000001041001000000000000000
def da235_12 (_ : Nat) := 0x203102868c2424c22309284b82970822f092b0e10c8c8444b04207092858c20e1252611312888d845c227c03e113e01a5c2098c2f844c7162620b13e118070898c2f844c6885f162648de2a876087edee785cc6fda2635785ad5e545444bd1a414e832cae2447c17c4209400f72a8a8281fa549504837ab2ac8885f57655110eeacaaa221ed59154443f8b82a8887d57650d10faacaa1a21bd59562442fabb2a4887e56254910fe2e8a8221fc59150443f8aa2a0887f17254110fe2c4a8221fc54950443f8b2a80887395454140ed2a4a8241f45c143443b8aa2a0887d14354110ee2a4a82217c5d540443d8aa280887914350110
def ka235_14 (_ : Nat) := 0x14cc4f44900002d527bc754d4c394a42348682b08804ed6c1242c001305231004834a0c2
def da235_14 (_ : Nat) := 0xe1470841c2182c21e1c04c7830931e1c04c7849e01e0c24c783093193c3806951a681861192e1263178498d293c30882f0931e11c1439300e0a1c8be5931c0164f0905e12638c224846057add16dd9d60d6953d35418ec348b125c761543b06800ff58152ff59150ff55150ff58950ff54950df55150df54950bf59540fe54140bf59520fb54920fe54120fd59510fd59110fd55110fd58910fd54910bd58452be58052f550d10fc54110fc50110
def ka235_16 (_ : Nat) := 0x95100b3480200000200
def da235_16 (_ : Nat) := 0x58604c874228f01428214c90c098e08531961429922da12cd07403faa5fc52fea87f503fa41f510
def da235_18 (_ : Nat) := 0xc22013f
def la235 : Nat -> Packing
| 10 => (13,4,5,8,da235_10)
| 12 => (28,3,5,10,da235_12)
| 14 => (22,2,5,10,da235_14)
| 16 => (6,1,5,8,da235_16)
| 18 => (1,0,5,0,da235_18)
| _ => emptyPacking
def ia235 : Nat -> Nat -> Option (Nat × Nat)
| 10 => lookupWord 10 24 5 4 1 ka235_10
| 12 => lookupWord 29 55 6 5 1 ka235_12
| 14 => lookupWord 13 35 6 5 1 ka235_14
| 16 => lookupWord 7 13 4 3 1 ka235_16
| _ => fun _ => none
def fa235 : Forest := ⟨235,9,fun j => g235s[j]?.getD (0,0),g235c,g235a,la235,ia235⟩
lemma sa235_10_0 : block fa235 10 0 2 = true := cl 5 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sa235_10_1 : block fa235 10 2 11 = true := cl 6 (by decide +kernel)
lemma ba235_10 : block fa235 10 0 13 = true := (@block_merge fa235 10 0 2 11 (sa235_10_0) sa235_10_1)
lemma sa235_12_0 : block fa235 12 0 1 = true := cl 5 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sa235_12_1 : block fa235 12 1 8 = true := cl 6 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sa235_12_2 : block fa235 12 9 19 = true := cl 7 (by decide +kernel)
lemma ba235_12 : block fa235 12 0 28 = true := (@block_merge fa235 12 0 9 19 ((@block_merge fa235 12 0 1 8 (sa235_12_0) sa235_12_1)) sa235_12_2)
lemma sa235_14_0 : block fa235 14 0 5 = true := cl 6 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sa235_14_1 : block fa235 14 5 12 = true := cl 7 (by decide +kernel)
lemma sa235_14_2 : block fa235 14 17 5 = true := cl 8 (by decide +kernel)
lemma ba235_14 : block fa235 14 0 22 = true := (@block_merge fa235 14 0 17 5 ((@block_merge fa235 14 0 5 12 (sa235_14_0) sa235_14_1)) sa235_14_2)
lemma sa235_16_0 : block fa235 16 0 1 = true := cl 6 (by decide +kernel)
lemma sa235_16_1 : block fa235 16 1 5 = true := cl 7 (by decide +kernel)
lemma ba235_16 : block fa235 16 0 6 = true := (@block_merge fa235 16 0 1 5 (sa235_16_0) sa235_16_1)
lemma ba235_18 : block fa235 18 0 1 = true := cl 6 (by decide +kernel)
lemma ta235 : checkedTables fa235 18 := by
 intro lv hlv;interval_cases lv
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . exact ba235_10
 . rfl
 . exact ba235_12
 . rfl
 . exact ba235_14
 . rfl
 . exact ba235_16
 . rfl
 . exact ba235_18
set_option maxHeartbeats 0 in
theorem gm235 : graphValid fa235 (boundsBefore k219) = true := by
 simp only [graphValid,Bool.and_eq_true]
 refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,listPieces_all (d:=0) ?_⟩
 all_goals simp only [listPieces]
 all_goals repeat' apply And.intro
 all_goals decide +kernel
def kb235_8 (_ : Nat) := 0x180008120000
def db235_8 (_ : Nat) := 0x14c100a60809306a955400b6068a995d543501108e46a2995954350110964680975514399910b44680755514399910a646a07550d4099910
def kb235_10 (_ : Nat) := 0x363401c12843860114f57403cbd5042088014689003a14018322c713023000020540490852b163e0e1c10400881000400093cb082000080041
def db235_10 (_ : Nat) := 0x61c200982004261004c10000000001004c1001660800010c204acc284c11fefa7abc1d6e670b719ac85cad15ea04da310e823e9e0e6642f94096461b8c85a280c8023ab27442ecaa2211e592a2176551108f8c8510bb2a88847565e885954344236b29442eca92211d593a2176549108f8c8510bb2a4884f864a885d1504426e32b442c8a822137195a216254110ec8ba2873baa0887c4551439dd50442bc325442eaa02213b194a2165501109e8c9d10b2a8088764a657550d40442f2532b2a86a02211f19021d5499910ab8c80eaaa4cc885656507550e66442ba3203aa8733221594975514399910e8a3aaa8a1ccc8847c6408754a66443e22a8a1aa1332211f1981d54099910ad8ca0eaa04cc8874c1d554502664437230aa1a8133221d907550d4099910b684b300a1a212afc45514354110957d22eca1a80884abb918550d4044255
def kb235_12 (_ : Nat) := 0x79200390f3e000000000000ce17004f000a44000024278626a54eab534a002e4120000b095137281849362d4222912b2f1aad1c4614b61b3b290d98100e453021990006230050003a004d1d52b7013c1513430596162c4b00af474c003203003f00112a000000343dbf31040008c3191f0000250000004095021e0c0012330038354800000101110c07180300000000000400000007000700070107000400000c08000003040008000803000001030001000a000000030100040c0004
def db235_12 (_ : Nat) := 0x205081820010144000818206c1014602028842106871a1010418100095c200482984188c9a2040414100084c2000121060404112840e105044c1136084a30821c4100c08c620804211310342230800410001800a2e462002d46285a8c40b0388006610016102840a101048612784041228604c310888a221841266110c20d09042e106888440110020e1f0858de0708600f0a4c625f0898766838be16427c2c6630078426322f8426300f802630478026322f80263b67696cbd89b095b6afd51a6346a864fe9e138a6a4cf9712ce49c7c8dd1822dc4487f0ea1641e821009fa3e67b0ee1d0b936f8db9abb49676cd99432363cc6585af45deb6160aaa526a39402724c89592423a458879039f03c472cde9af342628b99652c0524949091d2300500800c0100100009ed829dd645427e6027754950b79809dd52542bb60a7759540ced829dd65503ce5527754140af9809dd65482fa6027754920f6a8854950483da54a7754120bd5839dd654427d6127759510dd5839dd654427d60a77595109f5859dd644427da217655110df1709dd544427d61a7755110bd6885d943442f5a216550d10fd2885c1434427d61677589109f6885d952442fc60277549109f5869dd524437c6027754910bf2885d150442fca216454110bf28855150443dca215454110bf2885c950442fca216254110bf28854950443dca215254110df1749dd50443dc5527754110fd1439dd50443dc54a7754110df2885d540442fca216550110fb288551404427d61075999109f5821d6664427d21d5499910d747555266443751d54399910f955450e66443f460143999109f48754a66443dc5515099910fd14354266443dc5495099910bf185502664437c1d54099910fb15450266443ce5515050255f695254120956bd2197444255ed57650d10957f46014344255af4865c910957dc5515044255fd14354110957dc5495044255ef17650110956fc6154044255fb15450110956bd2197544222af5871951088bbc5d56044222adc865d543802b761c6550e00e5d75195438023b60a77595409d5839dd654427c60277549109f1801d666443e450d4099910f914350110956bc6006544222e70655411088aa76106550e00a9c8655143803871955450e00
def kb235_13 (_ : Nat) := 0x101c000ac980048cb2b004c3ec97580201008010c80
def db235_13 (_ : Nat) := 0x250a014c245850e10608225810846117842610986a28e55f9c189753ce0a87038038d5956455110dd1755c143443cc5915454110dd18750d50443d46154354110f917450d50443e45914354110f915450d50443d85895254110f316555140443e45954350110f115450d50443645d54350110
def kb235_14 (_ : Nat) := 0x4e03d2a30025a2001f8058089bd7d4871406842609e59f1d9cc68f0487a10da69c199705a46695a4880058801ee400000000000acce10055855982de90db80dc8f801e018c9a9049e6060923a1a0a0010213184a950e0c62a51483000b539891e3929617991a1d1b0a4f4611138ea29692270bc7c28d488b004588630655920e1008300040002204400000018336006930654502045000100080090020108
def db235_14 (_ : Nat) := 0x71010103028c082c41091110384180840d840a3031047188028818404200a203101030808424c44604202071010283610c0840417c21a30b0c11192a10c2c2b0864c4b8430b2380183c0058c88144440a2092610102c18c1c20c0b0430507122b0858d150c2c6868b043450b07a222322914111182d84684c1801e4420f0f0298c058c180040a03c0a6204e1e0931f0f0498c2c8c9b030b8634e4b19c32640be193192c570c9902f864c680c7c2210e50be125197c3c031c594968f85982c1cc17c2a63434645e1a2285a322b1f0d1193e2ccc617c28a6640bc3e1664507305f0998c3b87801c9c3c0263e1e0131f070898f85144c62057c2264e1e0131f0f0098f83844c7c3c0263e0451318897f00993838608389c1c2263e0e1131f087702110af8538722d1f31d91bf19517b1511170dd0b308905f03500afd0fa6f7cf42f18edeeb4e7ae40e06dccd92d68d3ed14cdacc0c86c5cc22be8baeb64b1aae0a96a7ca429e899e96492a8b086682c7e27a874e7146ba6506165bc5525184ce46442a3e03a636c3322f82ae27423a2001c618c1420f80be08403a0017f9dd6054afeb84cca96fd6099952dfae1332a57f9dd64542ff3bac4a85fe7754950efceea92a1bf59266543beaa4cca86fd6299950efaa5332a1bf552665437ea94cca86fe7759540ff4eea8281bf9dd65483f73baa4907fa7754120feceeb2a21fd9dd64443fb3baa8887f67758910feceea9221fd55266443faa94cc8877d5454255efaa4a84ab7f5d540957fca82812adfd7548255fdaa4904abfe54120957fabaa212aff57444255feaa8884abfd5c910957faa92212aff57544222fbaeaa1c01bf1d9528027eb84cca94fd74999509fae5332a13f9dd655027f3baca905f67759510beceeb22217d9dd54442fb3bac4885f67754910fe4eea82217d1d666443eaa1ccc887f15099910fe28133221bd5d9109577ab22212afd54344255deac4884abfc54110957f8a02212acfd72196229fae032c453f1d95088b3e32aa1116f46544222fe2a0884453f5d0658027eb90cb004fc7655200cf8caaa401b719543803ceaa287004fd7518a009f8eca94019f1955280376312a5006f16044222
def kb235_15 (_ : Nat) := 0x5c02c0018911014b400000652136c633540a38988303348d59501a0050070213c00000000800006661000420801c0003000000001041001000000000000000
def db235_15 (_ : Nat) := 0x203102868c2424c22309284b82970822f092b0e10c8c8444b04207092858c20e1252611312888d845c227c0313e1e01c217898c2f844c7162620be11318070898c2f844c6885f162648de2a876087edee785cc6fda2635785ad5e545444bd1a414e832cae2447c17c4209400f72a8a8281fa549504837ab2ac8885f57655110eeacaaa221ed59154443f8b82a8887d57650d10faacaa1a21bd59562442fabb2a4887e56254910fe2e8a8221fc59150443f8aa2a0887f17254110fe2c4a8221fc54950443f8b2a80887395454140ed2a4a8241f45c143443b8aa2a0887d14354110ee2a4a82217c5d540443d8aa280887914350110
def kb235_16 (_ : Nat) := 0xcdb68058d0920032402f112154017640cc8f90a5236461dc9e84576013b82130001005400441800005830c500d
def db235_16 (_ : Nat) := 0x18f1468b870191858f830903055d870272a3861b0e044161211c34c1c2e145810170e06640b830b32611d8039028ec380395110c184994191c3809942e1c04c9170e0a640a0c761041f01c842c3829942e1c04c8170e0264014f08b261c0cc2907610f8088b0e06614aae2a2c2cca3b087c04c380985205c28b00e2abc24c60b0612614a8d7e0264c18410e242f800f61cdb5e67ac717dad3556a0d3124141678ce11a130057c9f1161dc334560840d410810800ff99952ff99950ff18a55ff54a55ff54255ff50255ff48255ff19622ff54a22ff54222ff55200ff54a00bf99952bf99852bf99950bf99940bf99920fd99910bf58a55bf18a55bf58255fd44255bf59622bf19622bf58222fd44222bf19600f750e00bf18a00
def kb235_17 (_ : Nat) := 0x14cc4f44900002d527bc754d4c394a42348682b08804ed6c1242c001305231004834a0c2
def db235_17 (_ : Nat) := 0x8828c3891c21070860b087870131e0c24c7870131e127807830931e0c24c7830931a34d005e12a517849905e12634a2f09320bc24c62828ec21cb870070a38abe5931c0164f0905e12639163287e137e5df715ab645775754346cfa380bf2947d1543b06800ff58152ff59150ff55150ff58950ff54950df55150df54950bf59540fe54140bf59520fb54920fe54120fd59510fd59110fd55110fd58910fd54910bd58452be58052f550d10fc54110fc50110
def kb235_18 (_ : Nat) := 0x460040
def db235_18 (_ : Nat) := 0x118b0c501438a18132a71c214058c8c07f957fc45fe00
def kb235_19 (_ : Nat) := 0x95100b3480200000200
def db235_19 (_ : Nat) := 0x58604c829d0c039428214c90c098e08531961429922da12cd07403faa5fc52fea87f503fa41f510
def db235_21 (_ : Nat) := 0xc41013f
def lb235 : Nat -> Packing
| 8 => (5,6,5,6,db235_8)
| 10 => (34,5,5,9,db235_10)
| 12 => (84,4,5,11,db235_12)
| 13 => (13,4,5,8,db235_13)
| 14 => (79,3,5,12,db235_14)
| 15 => (28,3,5,10,db235_15)
| 16 => (29,2,5,11,db235_16)
| 17 => (22,2,5,10,db235_17)
| 18 => (3,1,5,7,db235_18)
| 19 => (6,1,5,8,db235_19)
| 21 => (1,0,5,0,db235_21)
| _ => emptyPacking
def ib235 : Nat -> Nat -> Option (Nat × Nat)
| 8 => lookupWord 5 8 3 3 1 kb235_8
| 10 => lookupWord 20 50 6 6 1 kb235_10
| 12 => lookupWord 58 131 8 7 1 kb235_12
| 13 => lookupWord 10 24 5 4 1 kb235_13
| 14 => lookupWord 45 119 7 7 1 kb235_14
| 15 => lookupWord 29 55 6 5 1 kb235_15
| 16 => lookupWord 17 44 6 5 1 kb235_16
| 17 => lookupWord 13 35 6 5 1 kb235_17
| 18 => lookupWord 3 5 3 2 1 kb235_18
| 19 => lookupWord 7 13 4 3 1 kb235_19
| _ => fun _ => none
def fb235 : Forest := ⟨235,10,fun j => g235s[j]?.getD (0,0),g235c,g235a,lb235,ib235⟩
lemma bb235_8 : block fb235 8 0 5 = true := cl 5 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma bb235_10 : block fb235 10 0 34 = true := by apply cb 6 1;simp only [cells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
set_option maxHeartbeats 0 in
lemma sb235_12_0 : block fb235 12 0 11 = true := cl 6 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sb235_12_1 : block fb235 12 11 73 = true := by apply cb 7 2;simp only [cells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma bb235_12 : block fb235 12 0 84 = true := (@block_merge fb235 12 0 11 73 (sb235_12_0) sb235_12_1)
lemma sb235_13_0 : block fb235 13 0 2 = true := cl 5 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sb235_13_1 : block fb235 13 2 11 = true := cl 6 (by decide +kernel)
lemma bb235_13 : block fb235 13 0 13 = true := (@block_merge fb235 13 0 2 11 (sb235_13_0) sb235_13_1)
lemma sb235_14_0 : block fb235 14 0 1 = true := cl 6 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sb235_14_1 : block fb235 14 1 37 = true := by apply cb 7 1;simp only [cells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
set_option maxHeartbeats 0 in
lemma sb235_14_2 : block fb235 14 38 41 = true := by apply cb 8 1;simp only [cells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma bb235_14 : block fb235 14 0 79 = true := (@block_merge fb235 14 0 38 41 ((@block_merge fb235 14 0 1 37 (sb235_14_0) sb235_14_1)) sb235_14_2)
lemma sb235_15_0 : block fb235 15 0 1 = true := cl 5 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sb235_15_1 : block fb235 15 1 8 = true := cl 6 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sb235_15_2 : block fb235 15 9 19 = true := cl 7 (by decide +kernel)
lemma bb235_15 : block fb235 15 0 28 = true := (@block_merge fb235 15 0 9 19 ((@block_merge fb235 15 0 1 8 (sb235_15_0) sb235_15_1)) sb235_15_2)
set_option maxHeartbeats 0 in
lemma sb235_16_0 : block fb235 16 0 17 = true := cl 7 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sb235_16_1 : block fb235 16 17 12 = true := cl 8 (by decide +kernel)
lemma bb235_16 : block fb235 16 0 29 = true := (@block_merge fb235 16 0 17 12 (sb235_16_0) sb235_16_1)
lemma sb235_17_0 : block fb235 17 0 5 = true := cl 6 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sb235_17_1 : block fb235 17 5 12 = true := cl 7 (by decide +kernel)
lemma sb235_17_2 : block fb235 17 17 5 = true := cl 8 (by decide +kernel)
lemma bb235_17 : block fb235 17 0 22 = true := (@block_merge fb235 17 0 17 5 ((@block_merge fb235 17 0 5 12 (sb235_17_0) sb235_17_1)) sb235_17_2)
lemma bb235_18 : block fb235 18 0 3 = true := cl 7 (by decide +kernel)
lemma sb235_19_0 : block fb235 19 0 1 = true := cl 6 (by decide +kernel)
lemma sb235_19_1 : block fb235 19 1 5 = true := cl 7 (by decide +kernel)
lemma bb235_19 : block fb235 19 0 6 = true := (@block_merge fb235 19 0 1 5 (sb235_19_0) sb235_19_1)
lemma bb235_21 : block fb235 21 0 1 = true := cl 6 (by decide +kernel)
lemma tb235 : checkedTables fb235 21 := by
 intro lv hlv;interval_cases lv
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . exact bb235_8
 . rfl
 . exact bb235_10
 . rfl
 . exact bb235_12
 . exact bb235_13
 . exact bb235_14
 . exact bb235_15
 . exact bb235_16
 . exact bb235_17
 . exact bb235_18
 . exact bb235_19
 . rfl
 . exact bb235_21
theorem l235 : Lower1 (vars 235) (graphGoal 235) 10 := lower_forest2 (g0:=fa235) (g1:=fb235) (hints:=83) (before_sound k219 v219) ⟨rfl,rfl⟩ gm235 gm235 ta235 tb235 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def k235 := extendKnown k219 10 [(235,[])]
theorem v235 : Known k235 := extendKnown_ok v219 l235 (by decide +kernel)
def g237s : Array (Bits × Bits) := #[(0xfffffffffffffffffffffe000001f81f81ffe0199fe22221,0x104104104104104001115e00000),(0x0,0x0),(0x7e00007e00006061fe5e42,0x1a69a69a69a69a6804041fe1e00),(0x1f8007e00007e186063fe484,0xc30c30c30c30c30104021fe000),(0x0,0x0),(0x7e00000007ff806007845e9e8,0x5145145145145144002801e1e0),(0x1f8000007ff8000180780889ff0,0x30c30c30c30c30d00280001fe0),(0xfffffffffffffffffffffffffffff80000001ff80111111f,0xfffffffffffffffffffffe082082082082082aa80000001f)]
def g237c : IndexTree ColumnInfo := (.fork 4 (.leaf [(1,0,236,0,8),(4,0,233,0,8),(32,0,205,0,8),(8,0,229,0,7)]) (.fork 2 (.leaf [(64,0,173,0,7),(128,0,109,0,7)]) (.leaf [(72,0,165,0,5),(136,0,101,0,4),(192,0,45,0,4)])))
def g237a : Array (List Nat) := #[[],[99]]
def ka237_12 (_ : Nat) := 0
def da237_12 (_ : Nat) := 0x4349cb8f02f2d5454942
def ka237_14 (_ : Nat) := 0x42708
def da237_14 (_ : Nat) := 0x5031a99638172c701c8ae58e05bae9180ff59152df55152bf59542fb54942
def ka237_16 (_ : Nat) := 0x314
def da237_16 (_ : Nat) := 0x5a0e51818728c0c5f03faa5fd42
def da237_18 (_ : Nat) := 0x2190817f
def la237 : Nat -> Packing
| 12 => (1,3,4,0,da237_12)
| 14 => (4,2,4,7,da237_14)
| 16 => (2,1,4,5,da237_16)
| 18 => (1,0,4,0,da237_18)
| _ => emptyPacking
def ia237 : Nat -> Nat -> Option (Nat × Nat)
| 12 => lookupWord 1 1 0 0 1 ka237_12
| 14 => lookupWord 2 5 3 2 1 ka237_14
| 16 => lookupWord 2 4 2 1 1 ka237_16
| _ => fun _ => none
def fa237 : Forest := ⟨237,9,fun j => g237s[j]?.getD (0,0),g237c,g237a,la237,ia237⟩
lemma ba237_12 : block fa237 12 0 1 = true := cl 6 (by decide +kernel)
lemma sa237_14_0 : block fa237 14 0 3 = true := cl 7 (by decide +kernel)
lemma sa237_14_1 : block fa237 14 3 1 = true := cl 8 (by decide +kernel)
lemma ba237_14 : block fa237 14 0 4 = true := (@block_merge fa237 14 0 3 1 (sa237_14_0) sa237_14_1)
lemma ba237_16 : block fa237 16 0 2 = true := cl 7 (by decide +kernel)
lemma ba237_18 : block fa237 18 0 1 = true := cl 6 (by decide +kernel)
lemma ta237 : checkedTables fa237 18 := by
 intro lv hlv;interval_cases lv
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . exact ba237_12
 . rfl
 . exact ba237_14
 . rfl
 . exact ba237_16
 . rfl
 . exact ba237_18
set_option maxHeartbeats 0 in
theorem gm237 : graphValid fa237 (boundsBefore k235) = true := by
 simp only [graphValid,Bool.and_eq_true]
 refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=0) ?_⟩
 all_goals simp only [listPieces]
 all_goals repeat' apply And.intro
 all_goals decide +kernel
def kb237_12 (_ : Nat) := 0x2
def db237_12 (_ : Nat) := 0x21828bcb5527754942
def kb237_14 (_ : Nat) := 0xd7126430052200
def db237_14 (_ : Nat) := 0x3081040e20e144183881830e2cbc7963e05ab931f2e3c0dcb8a3e04cbb8a58b78502100bfceeb22a5bf5926654bbeaa4cca96fe7759542fdceea92853f5d26654a7f3bacaa14fc7655222
def kb237_15 (_ : Nat) := 0
def db237_15 (_ : Nat) := 0xdcb8f0272d5454942
def kb237_16 (_ : Nat) := 0x874400258
def db237_16 (_ : Nat) := 0x1a0b1e58e039f24f11b094c40aa651e381c79748f2c7038b96380c5aa81522300ff99952ff50a55ff55222bf99952bf99942
def kb237_17 (_ : Nat) := 0x42708
def db237_17 (_ : Nat) := 0x140a99478e05564ca3c7032b96380c5df31180ff59152df55152bf59542fb54942
def kb237_18 (_ : Nat) := 0x84
def db237_18 (_ : Nat) := 0x216728c0c5a0e5181a303fcabfe22
def kb237_19 (_ : Nat) := 0x314
def db237_19 (_ : Nat) := 0x1428e51818728c0c5f03faa5fd42
def db237_21 (_ : Nat) := 0x2190817f
def lb237 : Nat -> Packing
| 12 => (1,4,4,0,db237_12)
| 14 => (8,3,4,8,db237_14)
| 15 => (1,3,4,0,db237_15)
| 16 => (5,2,4,8,db237_16)
| 17 => (4,2,4,7,db237_17)
| 18 => (2,1,4,6,db237_18)
| 19 => (2,1,4,5,db237_19)
| 21 => (1,0,4,0,db237_21)
| _ => emptyPacking
def ib237 : Nat -> Nat -> Option (Nat × Nat)
| 12 => lookupWord 1 2 1 0 1 kb237_12
| 14 => lookupWord 4 10 4 3 1 kb237_14
| 15 => lookupWord 1 1 0 0 1 kb237_15
| 16 => lookupWord 3 7 3 3 1 kb237_16
| 17 => lookupWord 2 5 3 2 1 kb237_17
| 18 => lookupWord 1 3 2 1 1 kb237_18
| 19 => lookupWord 2 4 2 1 1 kb237_19
| _ => fun _ => none
def fb237 : Forest := ⟨237,10,fun j => g237s[j]?.getD (0,0),g237c,g237a,lb237,ib237⟩
lemma bb237_12 : block fb237 12 0 1 = true := cl 7 (by decide +kernel)
lemma sb237_14_0 : block fb237 14 0 3 = true := cl 7 (by decide +kernel)
lemma sb237_14_1 : block fb237 14 3 5 = true := cl 8 (by decide +kernel)
lemma bb237_14 : block fb237 14 0 8 = true := (@block_merge fb237 14 0 3 5 (sb237_14_0) sb237_14_1)
lemma bb237_15 : block fb237 15 0 1 = true := cl 6 (by decide +kernel)
lemma sb237_16_0 : block fb237 16 0 2 = true := cl 7 (by decide +kernel)
lemma sb237_16_1 : block fb237 16 2 3 = true := cl 8 (by decide +kernel)
lemma bb237_16 : block fb237 16 0 5 = true := (@block_merge fb237 16 0 2 3 (sb237_16_0) sb237_16_1)
lemma sb237_17_0 : block fb237 17 0 3 = true := cl 7 (by decide +kernel)
lemma sb237_17_1 : block fb237 17 3 1 = true := cl 8 (by decide +kernel)
lemma bb237_17 : block fb237 17 0 4 = true := (@block_merge fb237 17 0 3 1 (sb237_17_0) sb237_17_1)
lemma bb237_18 : block fb237 18 0 2 = true := cl 7 (by decide +kernel)
lemma bb237_19 : block fb237 19 0 2 = true := cl 7 (by decide +kernel)
lemma bb237_21 : block fb237 21 0 1 = true := cl 6 (by decide +kernel)
lemma tb237 : checkedTables fb237 21 := by
 intro lv hlv;interval_cases lv
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . exact bb237_12
 . rfl
 . exact bb237_14
 . exact bb237_15
 . exact bb237_16
 . exact bb237_17
 . exact bb237_18
 . exact bb237_19
 . rfl
 . exact bb237_21
theorem l237 : Lower1 (vars 237) (graphGoal 237) 10 := lower_forest2 (g0:=fa237) (g1:=fb237) (hints:=1283) (before_sound k235 v235) ⟨rfl,rfl⟩ gm237 gm237 ta237 tb237 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def k237 := extendKnown k235 10 [(237,[])]
theorem v237 : Known k237 := extendKnown_ok v235 l237 (by decide +kernel)
def g238s : Array (Bits × Bits) := #[(0x0,0x0),(0xfffffffffffffffffffffffffff800007c1f07c0333e2221,0x4210842108400222e0000),(0xf8000f800c0ce5e42,0x5294a5294a500808e1e00),(0x1f003e000030c0fe484,0x6318c6318c602080fe000),(0x0,0x0),(0x3e000000ffcc00f3e9e8,0x294a5294a52880051e1e0),(0x7c00003ff00300f049ff0,0x18c6318c631a005001fe0),(0xfffffffffffffffffffffffffffffffffc00003ff009111f,0xfffffffffffffffffffffffffff84210842108555000001f)]
def g238c : IndexTree ColumnInfo := (.fork 9 (.fork 4 (.leaf [(2,0,236,0,8),(4,0,234,0,7),(8,0,230,0,7),(32,0,206,0,6)]) (.fork 2 (.leaf [(64,0,174,0,6),(128,0,110,0,5)]) (.leaf [(34,0,204,0,5),(66,0,172,0,5),(12,0,226,0,5)]))) (.fork 4 (.leaf [(36,0,202,0,5),(68,0,170,0,5),(40,0,198,0,5),(72,0,166,0,5)]) (.fork 2 (.leaf [(132,0,106,0,4),(136,0,102,0,4)]) (.leaf [(38,0,200,0,4),(44,0,194,0,4),(76,0,162,0,4)]))))
def g238a : Array (List Nat) := #[[],[50,101]]
def ka238_8 (_ : Nat) := 0
def da238_8 (_ : Nat) := 0x18e1826057019543
def ka238_10 (_ : Nat) := 0x401b302000010
def da238_10 (_ : Nat) := 0x160710800a0a04209a14c5033c5917018553cf1815c06550ef46007154d43f155350d51507955915354531
def ka238_12 (_ : Nat) := 0xab93b56c005386004220000533210acd14004811748f1b2e806880c30012063c707000088000680143a7c04c005800022430812010001000030060c0000000
def da238_12 (_ : Nat) := 0x1898040220b10588211c0200008040061410562a1185050420210342120841420212308100081420a105080818804084141e20309e0104f008278040c12205e0102844380508416ff3e2f239ee538ad4336bf2e2b22aea126a94236871f2761be6917a541163b0c22606e1102a006f56418553dbac8a98a7bb5516214f7aaa2c229ef95458053de8e2b2a877d5c46550efcb80caa1cfd7654d43db8eca9a87e75515350fea38aa6a1f5d5350d51b7aeaa1a83af59543507cea9a86a0fb55454541eeaa6a8a83ed50d515067ebb2a898ebd6455131dbac8a9a63bd591514c7eaa9aa298fe55254521be2e030aa7a75915314f66a9ac429ed55358453db2a6b00a73d5c46550e7cb80caa1f555354531
def ka238_14 (_ : Nat) := 0x32028275174d8e282cd000016588c06068008544cc4c326822c8c317887481f42048d69088920c6903933d6818a397d28f38d2c74010ca0c02000401c1080180
def da238_14 (_ : Nat) := 0x2242806282101a2824201421441448500c184104422421441088a08c02423418800a0885044a210ac04061028bc024a2f0091820380638184c034a102e24380a10589c04218040c8e0191c02824300d191c03084300c290c03c040443008811c03224300c28bc0248145e01240a2700b20516243138bdff5ed4b46ceb20c36fabbae2b22c3adea4a7e8ca026d94e2b845f773da761973565464b1123e0de32cb82788418c4208400ff59153ff19153ff55153ff58953ff58553ff55053ff59543ff19543ff54d43ff58543ff59151ff55151ff58d51ff54d51ff50d51ff58951ff54951ff54d41ff55131fd18553bf59053f754c53bf59543bf19543f754d43bf59443df54d51bf59541ef55141ef50d41fd54541bf59531bf59131f754d31fd54531bf59521fd54521af59053bb58853bd58453be58053
def ka238_16 (_ : Nat) := 0x9f020b5410073ae622103300
def da238_16 (_ : Nat) := 0x4060408297012430a8102085c049014604084c088ca8101a10223b99c7f62452e1700fea9ff14ffa87fc43fea8ff507fa63fd21
def da238_18 (_ : Nat) := 0x4100ff
def la238 : Nat -> Packing
| 8 => (1,5,5,0,da238_8)
| 10 => (5,4,5,6,da238_10)
| 12 => (33,3,5,10,da238_12)
| 14 => (41,2,5,10,da238_14)
| 16 => (8,1,5,8,da238_16)
| 18 => (1,0,5,0,da238_18)
| _ => emptyPacking
def ia238 : Nat -> Nat -> Option (Nat × Nat)
| 8 => lookupWord 1 1 0 0 1 ka238_8
| 10 => lookupWord 5 9 4 3 1 ka238_10
| 12 => lookupWord 23 53 6 6 1 ka238_12
| 14 => lookupWord 20 56 6 6 1 ka238_14
| 16 => lookupWord 8 16 4 3 1 ka238_16
| _ => fun _ => none
def fa238 : Forest := ⟨238,9,fun j => g238s[j]?.getD (0,0),g238c,g238a,la238,ia238⟩
lemma ba238_8 : block fa238 8 0 1 = true := cl 5 (by decide +kernel)
lemma ba238_10 : block fa238 10 0 5 = true := cl 6 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sa238_12_0 : block fa238 12 0 8 = true := cl 6 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sa238_12_1 : block fa238 12 8 25 = true := cl 7 (by decide +kernel)
lemma ba238_12 : block fa238 12 0 33 = true := (@block_merge fa238 12 0 8 25 (sa238_12_0) sa238_12_1)
lemma sa238_14_0 : block fa238 14 0 4 = true := cl 6 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sa238_14_1 : block fa238 14 4 18 = true := cl 7 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sa238_14_2 : block fa238 14 22 19 = true := cl 8 (by decide +kernel)
lemma ba238_14 : block fa238 14 0 41 = true := (@block_merge fa238 14 0 22 19 ((@block_merge fa238 14 0 4 18 (sa238_14_0) sa238_14_1)) sa238_14_2)
set_option maxHeartbeats 0 in
lemma ba238_16 : block fa238 16 0 8 = true := cl 7 (by decide +kernel)
lemma ba238_18 : block fa238 18 0 1 = true := cl 6 (by decide +kernel)
lemma ta238 : checkedTables fa238 18 := by
 intro lv hlv;interval_cases lv
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . exact ba238_8
 . rfl
 . exact ba238_10
 . rfl
 . exact ba238_12
 . rfl
 . exact ba238_14
 . rfl
 . exact ba238_16
 . rfl
 . exact ba238_18
set_option maxHeartbeats 0 in
theorem gm238 : graphValid fa238 (boundsBefore k237) = true := by
 simp only [graphValid,Bool.and_eq_true]
 refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,listPieces_all (d:=0) ?_⟩
 all_goals simp only [listPieces]
 all_goals repeat' apply And.intro
 all_goals decide +kernel
def kb238_8 (_ : Nat) := 0x2c2080
def db238_8 (_ : Nat) := 0xfa5083c6a299591701855393868a995917018553c38649916027759543c64611901c67754d43
def kb238_10 (_ : Nat) := 0x1208547000044000167010a0000393a81658d2000016000c41ba27cc9802746529278a009e18d0f01550174224100208008804d0820002440c0144105000
def db238_10 (_ : Nat) := 0x18408000002beaa96826e5a46321e09f5e1cdb9a5917d6955412d1904f0dcc8b4a064503c2814021eb2f442c830aa72e592a216418553978c8510b20c2a9d3ca65645c06154f1e2e8c00c3332a7a95646067754c53876cbd10aa2c429db16468854d6214e5cb25442a8b08a74d597a215358453974c9510aa2c029db46468854d6014f1cb0438ceeb2a878f0716027759543c72c13033bacaa1e3c605809dd6550f1e322c04eeb2a870f990a217654d43c6a3b3033baa6a1e65610719dd5350eba32038ceea9a87655911955399943b2cc80caa9ccca1c3b64a885d9544c61eb23442ecaa2630f990a217655131a74c8104ba0cb19d2d650655c4648cf1d0ecc00e4aa467555911d55350e33aacc80eaa9a8719d33648855cc648469ab2242ae6324234d9902157319211
def kb238_11 (_ : Nat) := 0
def db238_11 (_ : Nat) := 0x18e1826057019543
def kb238_12 (_ : Nat) := 0x1763a28800240f0ee6d4d0d204008a021815339ad9f400893d9581426b7ac02c364393c6a9e5091e0b8fbca5d4069049bce47955a4f03874c000f9310001ce63cbf0f45a001c16c5e009f5696e12312444f7f432b088413f100408d5c98571414a00d5e00000005c7f000fc7cbb2d5f0002553accda00ca8011c6b4fad864595ea3c107811a64e2aa420000000000b278000028c000025801356232d4c0000000000000001d4004c5a9b80400000af12ad354cc224d001c0921bd62a31c923b1095c45bd299182a000a03a9b2b830d80600a2ca80f2714c000b2f272dd8d19d600010c9864bb42028726ba1072080052418002a0028a22c2000a00000000011800b2938dcf4a42c0872200000000068401901a770012086000007d3a661114260632e500ce312a8a50a9058d4275724b0c02e4a0c29574952f8e868b409e4872bc00000420c0481c000c0280004170301c000d000140601130000000010040c000780000000000c10000000402060780802000001c00040680c00000000400040380800000180402010400806020401c0e0101828080700810020000824040200800060c0000400010000802000280002010380828020080c0400000140000048000200
def db238_12 (i : Nat) : Nat := (if i<1 then 0x5825c66654e3f61a77550539ed829dd5414fa7a216454c53add869dd5314fa75927754c53bd5819dd5314ebba215458853ece8854d6214ebda215458453ed68854d6114ebea215458053eda8854d6014e3f21d54998539f5819dd6550e7e6027759543add839dd6550ebd6067759543cf4719dd6550ebe60277595438fd839dd6550e3f6067759543cf5819dd6550f3e6027759543cfa885c06550e3fa217654d439bd849dd5350e7d6067754d43cdc769dd5350ee76127754d43bd5819dd5350f751c67754d43c7d755966650e3f61c6599943af5811966650ebe6006599943d5d7554e6650f971955399943c7d751d66650f1f5d553999439ed829dd645467b60a77551519f5819dd545467d6067754d51b75819dd535463f61a7750d518fc8750e66547375cd4399951aed829dd65506bd60677595418fd839dd655073b60a7759541bad829dd54506ed60677551418fd869dd535067d6067754d41bb5819dd435063f60c75999418fc8754e66506bd60677595318fd849dd654c73d6067759531af5819dd644c63f61677591318fe885d9544c63f61a77551319ed829dd544c6f56067754d31f568854d514c7d554e77545318fd841d6664c63f21d5499931add8319063956b760c6454e55bf1801c5539563f61c6414e55cbd74190539573b1917214e55cf4645c4539573e1917014e558fd811d9439563f2197550e55e9c6418d43957a71915350e558fc8750d619579d54d6154655abc8650d419563f219744c655f5553545319573b2097419633c7d75194648ceaf6106519233cf4655c4648ce3f60876552338fd811d9548ceed6046455233cec761c9548cefa6007255233cdd655cc548cf675517315233ced655c8548cf6b5517215233cf5655c4548cf6d5517115233cf9655c0548cf6e55170152338fd841d9538ce9f6146454e33af581191538ce3f2197550e339ed821d5438ce7d6047550e339f9801d5438ce3f61c6550e33abd84195438ceb760c6550e33d5c7554d438ce3f6107558a338fc87551628ce3f6107654a338fc865d5428ce3f61c6550a33abd84195428cebb6086550a33f2d54549428ce3f61075586338fc87551618ce3f61076546338fc865d5418ce3f61c6550633abd84195418cebd6046550633abc86551418cfad5516150633e7465545418cf376157319211cdc855cc648463f60c7655211abd83191548463f61d5418e11cbd74550638463f6107654e118fd8719153846b760c6454e11add8418d538463f6147650e118fc865d5438463f61c6550e11abd8419543846b760c6550e11abd85191438472f5d46450e11abc86551438472f1d95450e11cdc7654d43847971955350e11e9c6454d43846bc60061999538f5819dd6550e3e60277595438ed829dd655063d6067759531ab581191548cea760c6455211 else 0x108002100042e00829c4e0180c2c310203e00e0c1a20000610800200000003882000000000c20000c200184003080c04200000100f80400004000001c0d1000010000210800010000a100000008000008002c1028800408102020800200704200010241080000080000080000304062018144810288041003421c18344030800000000025844010814400014200188200184004204160c1000000000000820008282000142050808020019082042088002080c04201040001040810604041000820010402102040210208081082420d1040400100ec42010004010812022808400010004032108081028802a018183621104241090420a2813c7e0083c01f00419e01033c0283182381e81080b7fd7ef7cf7ca7b37a579778077b77677176375575074b74674173c73772972471f71a71571070b6fd6f86f36e56e06d26cd6bf6a86a369e69067967466666165c65765263b63662862361e61960b6065f85f35ee5e05db5d65d15c35be5b95ab59d58658157356555754954453f53152c52751950b5065014f34ee4e94db4d64d14cc4c74b049948247446f46a45c44543743242d42842341e4194143fd3f83e13dc3d73c93c43bf3b13ac39e39939438636f36a36536035b35635134c34733932b31d3183133052f72d72c92b22ad29f28827a2752702622542462382332252202122041f61f11da1d51c71b91b41a618f17816115313c12e12912410d0f60e80e30c30be0a709908b07d05d04f04a03c02e0170009ed829dd6454e7d60677591539f9809dd6454e7d6067758953af6885906154e7d6047499953dd5735c66654f3d5917199953cf4645c66654f7560d7199953cf5625c66654e7d61c6199953bf1801866654ebd61c6199953cf5741866654f2f5d07499953af5811d26654f2f5d15499953cf5745c66654f3d1d17199953cf5735c66654f3d5c97199953cf5845c66654f3d2117199953cf5545c66654f3d60d7199953cf)
def kb238_13 (_ : Nat) := 0x260002e91801509d00300000148200001000000000008000
def db238_13 (_ : Nat) := 0x2c0e21000000000a0a04205808a8cc8f09eb86694b80cf1645c06154f1e5957019543cf1815c06550e9d6046554d43a79801955350ed56046554d43b59801955350ef46007154d43f155350d51507955915354531
def kb238_14 (_ : Nat) := 0xa800230000000de206c54cd8424ac358f000180ec5258700000001440000002e0fa520000000352532174ea35acc8e6e300016ec30000000a4c03196a006600000a96a80000000006014bde31ed9ca01bb840000122bb3ebe261a8b66700350d2c258b7c52212d170003e42b40000053af1465f02000720033648e2e5344b8ae0873924003a41aa80046007650479001f9827352b5f086f00000016ddd0038e95b280116c909f043a4e6eb99ad932a23d596404800eaa116800ee27000010cda269d0009857a04fe643d2ac4c02ce8598ee20000000971604b7d671e854000067a88b0362298dc9ad0888878b6a2a70285e6d93f229ecc2fd287256a011438e2ba5203b062751a0118800009f001b0005666984016e3c381d15544800840558177a91b498d01e910000000256580000b43b62c00000000000871710da699495af111e000ad50006e1945e000025aa6882080000000000001710023b0a0000301346d019c00000e1634640e06dcb50000000016bb0811066000cdd13600656735f1d0fa31a2d2622c860001f80090620f000511c10003147c0006c00000b94000532cb8ed0b92a80000d90000000000002000000180c0605000000401018203e090180000000080404000300400000001800070001406050080804000200406030080000000000412010100000040801400010000002010080000050080404020280000040082c06030100c060200800000100034000e0700004000000000020080c0400000040400008000600010000000028000001010000000000080a00000040401020040200010000004000002202018040600018000200000000203010000201000000000018040404
def db238_14 (i : Nat) : Nat := (if i<1 then 0xeff3bacaa1efe7759543bfcee32a877f9dd5350fef3baa6a1dfe7758543bfaeb332877f1d66650f7eb2ccca1efc6599943fbaa7332877f5c66650f7eb0ccca1efd7599943df8eb33287bf54e6650f7eb8ccca1efe7759443bfceeb22a37f9dd54546ff3bac6a8dfe7754d51efceea9aa37f9dd43546ff3bac4a8efd6499951dfac7332a3df54e665477eb14cca8efd5499951dfaa7332a3bf50e665477ea94cca8efe7759541f7ceeaa2837f9dd53507df3ba86a0ff67754541dfaa733283bf9dd654c77f3bac898dfe7755131fbceea9a63fd9dd514c77eaa4cc98efe7759521feceea8a43bf1d163956feba8c72adfd7418e55dfac831cabbf190639577eb22a72aefc6454e55dfac6a9cabfd1c553956feba0a72aefc6414e55dfaeca1cab7f1d9439577e3b2872adfd7550e55dfac6a1cabf718d43957eea9a872adfd7510e55dfaa8b0cabbf54d619577ea1ac32af7d5354655bfaeaa0cabef551419577eb1a832afbd4350655feaa2a0cab7f5d531956feba2632aefd644c655fbaa698cabfd54531956febaa432aff55148655bfae832c67bf5d0658cefeba8c919efc6519233dfaecaa4677f1d9548cf7e3b2a919efd6555233df8caaa467bf591548cfde322a919fec7255233dfaca2a467ef550548cefeb98a919efc6554e33df8c8a9c677f5d5438cefe3aa8719efc6550e33f7aa8a1c67f754d438cf7eaa2c519f7d5454a33bfaeaa1467bf195428cfdeaa28519fed5250a33dfaa8b0c677f5d5418cf7e32a8319fbd5450633feaa2a0c67bf5d0658477eb98cb08efc7655211df8caaa423bf550638477e3b2a708efc6554e11df8c8a9c23bf1d943846febaa8708efc6550e11f7aa8a1c23f754d43846fab8ccca9ef461999539fae9332a73f5ca6654e7eb8ccca9ef571999539fceeb20a7af9dd6414e7f3bacaa1cfe77195439faeb332873f1d66650e7eb8ccca1cfe77594439f8eb330873f5d2665467eb9ccca8cfd72999519fceeb2a833f1d6665067f3baca98cfe77591319f8eb332633f9dd654867e3accc90edd6318e559fae831cabb758d539567ebb0a72adbd7414e55bdae429cab7d5c453956fcb80a72acfd7650e559f8eca1cabb718d439567ebb0872aef561546559faeca0cab3f5d9319567ebb2432acfd74196339fae632c673f5c8658ce7eb88cb19cfc7559233beae2324673f5d4648ce7eb98c919cfc7655233d78c8aa467775cc548cef6b90a919df57115233bf2e02a4673f1d9538ce7e3aac519cfc7654a339f8eab0c673f1d9518cf3e32aa319ef561506339fae832c233f5cc658467eb90cb08cfd75192119fae6324233f1d9548475e322a908cfd7518e119fae831c233f1d9538473e32aa708edc6354e119f8eca1c23af191438467e3b2a508cf57199953978e9330a73d5c4648ce5e3a2c519cdd7319211 else (if i<2 then 0x908c14100e8481a10a2210202c08c142841413423050a1048414282460a1220305811828488202020b0430322102b1080c2081420b100102060944304a2101a1510c0e88416182002041020742204a111110900c140c9060a103046219201b08c0c1088644182030828488304481820304622120185110c1424214224430a182b10a0414422104a2101b1090420a02204011208488048060a123c162192208b0f898780815c0a0305030201e028270280c138140787c5c0304058be089282c5c4f01008078060806040a03c0604030201e028706f00c1529438090917c1124040b09e0201817006901037814080806c5c01a503e09118507700c13824060bc1203090ee01c8f0480c44438060bc02040b09e0206f0081008140780a07840b83c05420305c1e02a08182e17017089817048040a03c0404030201e02828485f010100c08140780d460bc03030205a1e02820102d0f014100e88168780c080a060403c06040b09e020208700c10438060817c01240a83e2e02018605701014242f80808060403c05030c0ae02029670151014b0ab8080a5459c04052c2a272020584f010128b802480821c0304a10be020270080c438045497c0303e01118270080c4780406061903c04050ce009201f0088d0780306081703c04050be08120270080f804041683c030541e01020620f00c4780406c397c03040be0092458570061288138024903c0183ba95cf6e5170bb7b5ba6d896b7b555a56d01663b275906c59627b115816c015f3af35766ba95c7acd5636b01553a9f54a6a294f7a75531695148ba3b51a68c945fa2150d685141ba034fe67c93c79dd4e967113739b34d4666931f9854bd65c12c395b4a6650926f92d491647121b90347a63991b78d546363011738b3454627912f88d43f61f10f387743661790a784d41f60e105381b4046008fef7e93ef5f40f8b7bf3d85e98f2f78d3c35de0edb7633ae5d58e977493a15cd0e5371b3885c18e076fd37b5bb0dc36d33625af8d5f6a13495a20d0367b3385998ca764531f58d0c4b61b3085828bff5f52f75790bb35d32e256f8b5f5a52c95610adb55f2a85508a5751928553c09b34cb25c5298927481237516089343b216507881f4011f94fa07ab3cb1da4e7870f3711af4d3066b3231844be85c72cd1594a6050b277134495848723110f48203eb1e30e846f83571990c345e02cb1570a644f825f12108944001db0df06842f815709d04942100e306302a411806702100740017f9dd6454eff3b8c8a9dfe7758953bfceeb0aa77f5d26654efe3a4cca9efd6499953df8c9332a7f75ce6654efeb94cca9efd6299953bfae3332a7fd5c66654f7eb0ccca9ff46199953dfae9332a7bf1d26654f7eaa4cca9efd7399953dfae5332a7bf5c66654f7f3bac829dfe7755053fbceea98a7bf5526614 else 0x2040c2841d202090da1182028828208c4c2c04040a1841540404c220305611b0e188043061a20000c118860620b0840c2003082314140c014143c0104032221202828208140c412142050304182841589858080a868834403611819088042000202b08d8420610a08200882420602203c10d1868420384081ac43030d1068408344081ac43030d1068208083441b22205c104185040c13046021a2030a10486882428412105c103186c4882411886101a1c3010d10287801484648105081841684409422a10c1868810140c60000100c444424030504102840c158460610a056218482))
def kb238_15 (_ : Nat) := 0x403802374d153c0a90c4b4c34c9a00189006cc0b423cb81445afc2b4749591a651940028e242638fd8101500400044708624008504a00d0ca00f
def db238_15 (_ : Nat) := 0x3130080441620b104238040000080400600a08000ac54230a0a08488048060684241082b1082821a4620200102d1608c160440b06201031008108283c4060a1613c040b0509e02048285f01018142c2481a1dc030e0d108700ac9ad2afa8a95a22739ba699924790a358c22b83a017d1d7709b5681935f969531374890d3e0db2d8911b0470a8150035eb20c8a9ef56418553dbac8a98a7bb5516214f7aaa2c229ef95458053de8e2b2a879f5946550efab88caa1df970195439faeca9a879f1955350f6e3b2a6a1f5c6554d43f38e8a9a87e75515350fea38aa6a1f5d5350d51b7aeaa1a83af59543507cea9a86a0fb55454541eeaa6a8a83ed50d515067ebb2a898ebd6455131dbac8a9a63bd591514c7eaa9aa298fe55254521be2e030aa7a75915314f66a9ac429ed55358453db2a6b00a73d5c46550e7cb80caa1f555354531
def kb238_16 (_ : Nat) := 0x4400e284a680af1d5068bbe9f184ab6d6113d7836ab43cb4925a5723cc4c50c3e50ed70e848199400000539135c2a265add6ad50037b1218ca201000a80003005c0166c040000220000040400128bc1802a0440550100072618082
def db238_16 (_ : Nat) := 0xc5861e0243898b0e028a442700d2a447882e1c060aad4e0224450a085428f0215a9c014814203c5870182a45781495529c4150e030a842700d28512c701028ac0c0815860624482f00920b498049020345090c1c070a0d660545482c4e02041380590724180886032cc04063520a024301b02a203478088d2602031a10841c050438860225098280c20504045e0127992b05020b098049208da382816860223958080c8e020308386e0605178048d08e638181420bc02481070dc040a9010bc024a2c66014444b300922a16870107012380814481c0308280e0164d6fa3f33e38c2f76adcd8aac54ce85cea9932a243c66861021f3bc672edf5a7334634c016c2b052c9811fa1e3ec770e11a83005989f11d1ea3345608b0d410810800ff99953ff99943ff99951ff58e55ff18e55ff54e55ff14e55ff50e55ff10e55ff58655ff54655ff50655ff4c655ff48655ff19633ff19233ff55233ff15233ff54e33ff50e33ff54a33ff50a33ff54633ff50633ff55211ff54e11ff50e11ff54a11bf99953bf99853bf99943bf99843bf99951bf99941bf99931bf99921bf58e55bf18e55bf58655bf59633bf19633bf59233bf19233bf58a33bf58633bf19611bf19211bf18e11
def kb238_17 (_ : Nat) := 0x32028275174d8e282cd000016588c06068008544cc4c326822c8c317887481f42048d69088920c6903933d6818a397d28f38d2c74010ca0c02000401c1080180
def db238_17 (_ : Nat) := 0x448500c50420345048402842882890a0183082080d08d084522104450462422423418910514110a08945046288601840a2c4e02851627010101c03061070dc050a13121c05082c4e0260202078088f01110ac04068c8e01842180614560204c0404430088e0203238080c28b1380814589c040a245e02050c2c493bcec38fe0f77daf51cfb24c6305baedfb4ec0ad2a1a567b98639861fe759ae6357a5814d4cd193fcde32cb82788418c4208400ff59153ff19153ff55153ff58953ff58553ff55053ff59543ff19543ff54d43ff58543ff59151ff55151ff58d51ff54d51ff50d51ff58951ff54951ff54d41ff55131fd18553bf59053f754c53bf59543bf19543f754d43bf59443df54d51bf59541ef55141ef50d41fd54541bf59531bf59131f754d31fd54531bf59521fd54521af59053bb58853bd58453be58053
def kb238_18 (_ : Nat) := 0x5842084
def db238_18 (_ : Nat) := 0x450c030908602228440c05808c07f957fc67fe11
def kb238_19 (_ : Nat) := 0x9f020b5410073ae622103300
def db238_19 (_ : Nat) := 0x10181020a593010c2a04082164c0405181021302232900602230203bfa285684b341700fea9ff14ffa87fc43fea8ff507fa63fd21
def db238_21 (_ : Nat) := 0x4100ff
def lb238 : Nat -> Packing
| 8 => (4,6,5,4,db238_8)
| 10 => (34,5,5,8,db238_10)
| 11 => (1,5,5,0,db238_11)
| 12 => (190,4,5,12,db238_12)
| 13 => (10,4,5,7,db238_13)
| 14 => (235,3,5,13,db238_14)
| 15 => (38,3,5,10,db238_15)
| 16 => (48,2,5,11,db238_16)
| 17 => (41,2,5,10,db238_17)
| 18 => (3,1,5,7,db238_18)
| 19 => (8,1,5,8,db238_19)
| 21 => (1,0,5,0,db238_21)
| _ => emptyPacking
def ib238 : Nat -> Nat -> Option (Nat × Nat)
| 8 => lookupWord 3 5 3 2 1 kb238_8
| 10 => lookupWord 23 53 6 6 1 kb238_10
| 11 => lookupWord 1 1 0 0 1 kb238_11
| 12 => lookupWord 116 285 9 8 1 kb238_12
| 13 => lookupWord 16 22 5 4 1 kb238_13
| 14 => lookupWord 171 382 9 8 1 kb238_14
| 15 => lookupWord 18 51 6 6 1 kb238_15
| 16 => lookupWord 29 75 7 6 1 kb238_16
| 17 => lookupWord 20 56 6 6 1 kb238_17
| 18 => lookupWord 3 6 3 2 1 kb238_18
| 19 => lookupWord 8 16 4 3 1 kb238_19
| _ => fun _ => none
def fb238 : Forest := ⟨238,10,fun j => g238s[j]?.getD (0,0),g238c,g238a,lb238,ib238⟩
lemma bb238_8 : block fb238 8 0 4 = true := cl 5 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma bb238_10 : block fb238 10 0 34 = true := by apply cb 6 1;simp only [cells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma bb238_11 : block fb238 11 0 1 = true := cl 5 (by decide +kernel)
lemma sb238_12_0 : block fb238 12 0 7 = true := cl 6 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sb238_12_1 : block fb238 12 7 183 = true := by apply cb 7 3;simp only [cells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma bb238_12 : block fb238 12 0 190 = true := (@block_merge fb238 12 0 7 183 (sb238_12_0) sb238_12_1)
set_option maxHeartbeats 0 in
lemma bb238_13 : block fb238 13 0 10 = true := cl 6 (by decide +kernel)
lemma sb238_14_0 : block fb238 14 0 5 = true := cl 6 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sb238_14_1 : block fb238 14 5 77 = true := by apply cb 7 2;simp only [cells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
set_option maxHeartbeats 0 in
lemma sb238_14_2 : block fb238 14 82 153 = true := by apply cb 8 3;simp only [cells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma bb238_14 : block fb238 14 0 235 = true := (@block_merge fb238 14 0 82 153 ((@block_merge fb238 14 0 5 77 (sb238_14_0) sb238_14_1)) sb238_14_2)
set_option maxHeartbeats 0 in
lemma sb238_15_0 : block fb238 15 0 8 = true := cl 6 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sb238_15_1 : block fb238 15 8 30 = true := by apply cb 7 1;simp only [cells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma bb238_15 : block fb238 15 0 38 = true := (@block_merge fb238 15 0 8 30 (sb238_15_0) sb238_15_1)
set_option maxHeartbeats 0 in
lemma sb238_16_0 : block fb238 16 0 20 = true := cl 7 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sb238_16_1 : block fb238 16 20 28 = true := cl 8 (by decide +kernel)
lemma bb238_16 : block fb238 16 0 48 = true := (@block_merge fb238 16 0 20 28 (sb238_16_0) sb238_16_1)
lemma sb238_17_0 : block fb238 17 0 4 = true := cl 6 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sb238_17_1 : block fb238 17 4 18 = true := cl 7 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sb238_17_2 : block fb238 17 22 19 = true := cl 8 (by decide +kernel)
lemma bb238_17 : block fb238 17 0 41 = true := (@block_merge fb238 17 0 22 19 ((@block_merge fb238 17 0 4 18 (sb238_17_0) sb238_17_1)) sb238_17_2)
lemma bb238_18 : block fb238 18 0 3 = true := cl 7 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma bb238_19 : block fb238 19 0 8 = true := cl 7 (by decide +kernel)
lemma bb238_21 : block fb238 21 0 1 = true := cl 6 (by decide +kernel)
lemma tb238 : checkedTables fb238 21 := by
 intro lv hlv;interval_cases lv
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . exact bb238_8
 . rfl
 . exact bb238_10
 . exact bb238_11
 . exact bb238_12
 . exact bb238_13
 . exact bb238_14
 . exact bb238_15
 . exact bb238_16
 . exact bb238_17
 . exact bb238_18
 . exact bb238_19
 . rfl
 . exact bb238_21
theorem l238 : Lower1 (vars 238) (graphGoal 238) 10 := lower_forest2 (g0:=fa238) (g1:=fb238) (hints:=286287184) (before_sound k237 v237) ⟨rfl,rfl⟩ gm238 gm238 ta238 tb238 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def k238 := extendKnown k237 10 [(238,[])]
theorem v238 : Known k238 := extendKnown_ok v237 l238 (by decide +kernel)
def g246s : Array (Bits × Bits) := #[(0x0,0x0),(0xffffffffffffffffffffffffffffffffc003fc3fc0f3fc91,0x2222222200a2bc00),(0x3c03c0030c3fa2,0x3333333302083f80),(0x0,0x0),(0xffffffffffffffffffffffffffffffffc0000003c000c7ff,0xffffffffffffffffffffffffffffffffddddddddc00043ff),(0x3c003fc0c0f0974,0x888888888050070),(0x3c003c00303013f8,0x19999999a01003f0),(0xffffffffffffffffffffffffffffffffffffc0003fc0224f,0xffffffffffffffffffffffffffffffffc44444445540000f)]
def g246c : IndexTree ColumnInfo := (.fork 8 (.fork 4 (.leaf [(16,0,230,0,7),(64,0,182,0,7),(0,16,228,2,6),(32,0,214,0,6)]) (.leaf [(4,0,242,0,6),(2,0,228,0,5),(128,0,118,0,5),(18,0,228,0,5)])) (.fork 4 (.leaf [(2,16,228,0,5),(20,0,226,0,5),(36,0,210,0,5),(48,0,198,0,5)]) (.leaf [(64,16,164,2,5),(66,0,164,0,4),(96,0,150,0,4),(192,0,54,0,4)])))
def g246a : Array (List Nat) := #[[]]
def ka246_8 (_ : Nat) := 0x8c618
def da246_8 (_ : Nat) := 0x2408000440f2f2682a52195350d10b318419550442d460c6554110f115350d50443645d5434c110
def ka246_10 (_ : Nat) := 0x62c0020002000a00000d33a0a41c617a409290001000000020
def da246_10 (_ : Nat) := 0x250473413408e0814826419010002040c82c83202102c824f8481e3da544e44beb8b633adab251f19130d0078d7254d43f1aa6b1287e354d4354b8ea9a86a869d6550d30eb2a6a8261e650d504c2daba0ca885d573195109e8eca9a21e554d43443b832aa0887715354110f6286a82217c5d530443e8a9a6088791434c110
def ka246_12 (_ : Nat) := 0x100999eb00154001854cad015db1238e11d6d32890000081
def da246_12 (_ : Nat) := 0x2a0a4a0906050282006908e828182008315210640810c018a11081229a03484126809209c56033aa6069d02a2728782740c4c702089e38104dbe9b2b84bfdbaaf4097c7a0efc75b5186b253a40f268288e83a00fb58953ef59543ef58143fb54d52fb54951df54d50ef50d50bf59530f754d30fe54130bf59510fd54510fe54110fd59510fd19510fd58d10fd54d10e754d43eb58943eb50d52e750d30ed50d10fc54110fc4c110
def ka246_14 (_ : Nat) := 0x51072603480442
def da246_14 (_ : Nat) := 0x145458162a2c0834122729a283a8a64460a2baf05123a40e2a40e138a099b692cf0b4825a3201fd53fea8ff543fa61fd10dea1fb54bda65f510
def da246_16 (_ : Nat) := 0x3d0813f
def la246 : Nat -> Packing
| 8 => (5,4,4,5,da246_8)
| 10 => (17,3,4,8,da246_10)
| 12 => (24,2,4,9,da246_12)
| 14 => (9,1,4,8,da246_14)
| 16 => (1,0,4,0,da246_16)
| _ => emptyPacking
def ia246 : Nat -> Nat -> Option (Nat × Nat)
| 8 => lookupWord 2 5 3 3 0 ka246_8
| 10 => lookupWord 14 26 5 5 0 ka246_10
| 12 => lookupWord 10 28 5 5 0 ka246_12
| 14 => lookupWord 4 10 4 4 0 ka246_14
| _ => fun _ => none
def fa246 : Forest := ⟨246,8,fun j => g246s[j]?.getD (0,0),g246c,g246a,la246,ia246⟩
lemma ba246_8 : block fa246 8 0 5 = true := cl 5 (by decide +kernel)
lemma sa246_10_0 : block fa246 10 0 1 = true := cl 5 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sa246_10_1 : block fa246 10 1 16 = true := cl 6 (by decide +kernel)
lemma ba246_10 : block fa246 10 0 17 = true := (@block_merge fa246 10 0 1 16 (sa246_10_0) sa246_10_1)
lemma sa246_12_0 : block fa246 12 0 7 = true := cl 6 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sa246_12_1 : block fa246 12 7 17 = true := cl 7 (by decide +kernel)
lemma ba246_12 : block fa246 12 0 24 = true := (@block_merge fa246 12 0 7 17 (sa246_12_0) sa246_12_1)
lemma sa246_14_0 : block fa246 14 0 4 = true := cl 6 (by decide +kernel)
lemma sa246_14_1 : block fa246 14 4 5 = true := cl 7 (by decide +kernel)
lemma ba246_14 : block fa246 14 0 9 = true := (@block_merge fa246 14 0 4 5 (sa246_14_0) sa246_14_1)
lemma ba246_16 : block fa246 16 0 1 = true := cl 6 (by decide +kernel)
lemma ta246 : checkedTables fa246 16 := by
 intro lv hlv;interval_cases lv
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . exact ba246_8
 . rfl
 . exact ba246_10
 . rfl
 . exact ba246_12
 . rfl
 . exact ba246_14
 . rfl
 . exact ba246_16
set_option maxHeartbeats 0 in
theorem gm246 : graphValid fa246 (boundsBefore k238) = true := by
 simp only [graphValid,Bool.and_eq_true]
 refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=0) ?_⟩
 all_goals simp only [listPieces]
 all_goals repeat' apply And.intro
 all_goals decide +kernel
def kb246_8 (_ : Nat) := 0
def db246_8 (_ : Nat) := 0x1a908650d3044255
def kb246_10 (_ : Nat) := 0x73d34806c82400146800003440007c001114100b00c66270000a60000e01776155e1825838100000020000000400001800010c0000000001000100001
def db246_10 (_ : Nat) := 0x9080502281010060800000000001901117014405102a41520c2440ac03601003802003104048124081d034aa2ce2572688c320f027ebe1e6ee74b91aec25aaa1368e3c9b0be5a2a920863e188b03e12068033958971999539b5819dd6550ee56067754d4399d831d66650e796067754d52aac869dd4354a2f61d43999508bd849dd654c23d60677595308bd849dd654423760e77595109b5849dd654427560e77595109f1809dd654423d61a7754d10bb1849dd50443e4a21434c110f91439dd30443655cd4399910d717554266443745cd3099910f91434c266442ab2197250e55cad765c943957271d9434c255af0864c110957e450d3044255af180195108cebc2195044233e7065541108cebc6006544211a9d8319543802a72195350e00e1c6554d43803a354d4358a00
def kb246_11 (_ : Nat) := 0x10183941001000
def db246_11 (_ : Nat) := 0x90200000881ba171748d03155957319510a948654d43442cc6106554110b518319550443c454d4354110ad08654d30443645d5434c110
def kb246_12 (_ : Nat) := 0x143c9d626000c01a8a0010b8021b898e88e3e301089f2e1402a42d09906ad9e425e558461ca1d8f7a6c02d0cc65009281c1288cc3ba6494cc8010468072911c31800e9602014ae14fd5cb0008020080c90012044b118000031a0808d100c00100206030c00000
def db246_12 (_ : Nat) := 0x840f008008f20261284349089047506830013c444000103c340f4041041c210010580e148062041041e01041241224c805212142201444581e1c80c809208224124105222082281045024010781a0e1860231038020018e100144802890050051200a2471c580c091e030302004040091050231220e1c0606040080882118b030404104004105482a02d0508134102082071c7c07a03c51981b38a29b733e61cb79492463f4728b11321cc3485103a013f67c6f79e93bf758e81ca3886f8dc1a7b3c652c3d81af75c8b6162ab253ea31402664b491d1a228438824fb1ea3ae710d899e3085c4af15227e4cc8c9062023d46a0c11782a44e8910fc1ac2c0530720b409800ddac5332a77d5c66654f7ab8ccca9cfd7099953b7ceeb2a87e79dd5350edf3bac0a1dbc7599943f3aa7332877b9dd5354bd73ba86a96ed52999519fae1332a36f5d2665435eba4cca84fd7399950d7a87332a13f5c6665427f3baca9879e7750d30f3a87332613f5d6664c27f3baca885f677545109faeb332217d9dd65442fb3b8ca885f67758d10beceea9a21ed9dd43443f93baa0887f2774c110beaeb332217d1d666442fab9ccc887b54399910fe2a133221fc4c2664435ebb2872af9d5350e55f5ae4a1cabeb50d529575ea1ac12acfc764c255f3a86984ab3f1d9109577ab0a212aef57644255de8ec884abbd58d10957daa1a212aff15044255fe260884ab3f5c0658ce7e3b2a119e7c6554233de8ec88467bd195108cff8a822119cfd70196119f8eca8423bd19510847f8a822108cfd73196009fae232c013f1d9538033e32aa7006bc6550e00f3aa6a1c01bb54d628027e3b2a3006ed62546009eae3332a72f5d266542763b2a519ead4358a00
def kb246_13 (_ : Nat) := 0x61301a2224f052c08795cc8a484200c2
def db246_13 (_ : Nat) := 0x128239a09a047040a410364290100001020641641901081641272380f4f02d2a25609d9c5b19d6d5928f8c8986803c6b92a6a1f8d5358943f1aa6a1aa5c754d435434eb2a86987595354130f3286a82619d59465442daba0ca885d573195109e8eca9a21e554d43443b832aa0887715354110f6286a82217c5d530443e8a9a6088791434c110
def kb246_14 (_ : Nat) := 0xa79c6800040004003000007c00011d36489460a35214917645c36d539626014b00f622344005480000000003001100040100001
def db246_14 (_ : Nat) := 0x642a18830b1c2818985018f010818632502851201868a103031460d060728c80839034614181cc222830415250a20a2085c70a880a872f8145c70a881898d041b1aa820d8d54113c319282e298830b818e9f068804318d23066f169820b8e0d0c50436041973478b0b902c7018a28d0c72305c706232058e031451a1a9826383051031312087265504c7a14789440e30c5086707202be2796ea1c2b6867ec8982af45aead14ba7a4ba9010e9f43ae6b8c896e28a4a0828e218a288428680960b80b800ff99953ff99951ff99950ff99930ff99910ff54e55ff54655ff54255ff4c255ff44255ff54233ff54211ff54e00ff54600bf99953ef99943bf99951bf99950bf99930bf99910fd99910bf58e55ef50e55fb54a55fb4ca55bf58655bf58255fd44255bf19633fb54a33fd44233bf19611fb54a11fd44211bf19600ef50e00bb58a00bd18600
def kb246_15 (_ : Nat) := 0x100999eb00154001854cad015db1238e11d6d32890000081
def db246_15 (_ : Nat) := 0xa82724a0d85c50282006908e828182008319210640810c018c2e034502042229a03484126809348476050cea981bcd503a0a9c742738c4231c084629e04f0f2b73a8d1e4af764a9d0a57147bb819ebe56a58fe68288e83a00fb58953ef59543ef58143fb54d52fb54951df54d50ef50d50bf59530f754d30fe54130bf59510fd54510fe54110fd59510fd19510fd58d10fd54d10e754d43eb58943eb50d52e750d30ed50d10fc54110fc4c110
def kb246_16 (_ : Nat) := 0x630c8
def db246_16 (_ : Nat) := 0xb9b51816f1828978c1448e9038cb4a00ff2aff8cffc23fe00
def kb246_17 (_ : Nat) := 0x51072603480442
def db246_17 (_ : Nat) := 0x22c60a2961151068244e53222a394c8844ea33af05135140e2a40e6889c9a57336fab4825a3201fd53fea8ff543fa61fd10dea1fb54bda65f510
def db246_19 (_ : Nat) := 0x3d0813f
def lb246 : Nat -> Packing
| 8 => (1,5,4,0,db246_8)
| 10 => (35,4,4,9,db246_10)
| 11 => (7,4,4,6,db246_11)
| 12 => (76,3,4,11,db246_12)
| 13 => (18,3,4,8,db246_13)
| 14 => (38,2,4,11,db246_14)
| 15 => (24,2,4,9,db246_15)
| 16 => (4,1,4,7,db246_16)
| 17 => (9,1,4,8,db246_17)
| 19 => (1,0,4,0,db246_19)
| _ => emptyPacking
def ib246 : Nat -> Nat -> Option (Nat × Nat)
| 8 => lookupWord 1 1 0 0 0 kb246_8
| 10 => lookupWord 29 53 6 6 0 kb246_10
| 11 => lookupWord 6 10 4 3 0 kb246_11
| 12 => lookupWord 32 85 7 7 0 kb246_12
| 13 => lookupWord 7 19 5 5 0 kb246_13
| 14 => lookupWord 21 49 6 6 0 kb246_14
| 15 => lookupWord 10 28 5 5 0 kb246_15
| 16 => lookupWord 3 5 3 2 0 kb246_16
| 17 => lookupWord 4 10 4 4 0 kb246_17
| _ => fun _ => none
def fb246 : Forest := ⟨246,9,fun j => g246s[j]?.getD (0,0),g246c,g246a,lb246,ib246⟩
lemma bb246_8 : block fb246 8 0 1 = true := cl 5 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma bb246_10 : block fb246 10 0 35 = true := by apply cb 6 1;simp only [cells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma bb246_11 : block fb246 11 0 7 = true := cl 5 (by decide +kernel)
lemma sb246_12_0 : block fb246 12 0 4 = true := cl 6 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sb246_12_1 : block fb246 12 4 72 = true := by apply cb 7 2;simp only [cells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma bb246_12 : block fb246 12 0 76 = true := (@block_merge fb246 12 0 4 72 (sb246_12_0) sb246_12_1)
lemma sb246_13_0 : block fb246 13 0 1 = true := cl 5 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sb246_13_1 : block fb246 13 1 17 = true := cl 6 (by decide +kernel)
lemma bb246_13 : block fb246 13 0 18 = true := (@block_merge fb246 13 0 1 17 (sb246_13_0) sb246_13_1)
lemma sb246_14_0 : block fb246 14 0 2 = true := cl 6 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sb246_14_1 : block fb246 14 2 22 = true := cl 7 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sb246_14_2 : block fb246 14 24 14 = true := cl 8 (by decide +kernel)
lemma bb246_14 : block fb246 14 0 38 = true := (@block_merge fb246 14 0 24 14 ((@block_merge fb246 14 0 2 22 (sb246_14_0) sb246_14_1)) sb246_14_2)
lemma sb246_15_0 : block fb246 15 0 7 = true := cl 6 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sb246_15_1 : block fb246 15 7 17 = true := cl 7 (by decide +kernel)
lemma bb246_15 : block fb246 15 0 24 = true := (@block_merge fb246 15 0 7 17 (sb246_15_0) sb246_15_1)
lemma bb246_16 : block fb246 16 0 4 = true := cl 7 (by decide +kernel)
lemma sb246_17_0 : block fb246 17 0 4 = true := cl 6 (by decide +kernel)
lemma sb246_17_1 : block fb246 17 4 5 = true := cl 7 (by decide +kernel)
lemma bb246_17 : block fb246 17 0 9 = true := (@block_merge fb246 17 0 4 5 (sb246_17_0) sb246_17_1)
lemma bb246_19 : block fb246 19 0 1 = true := cl 6 (by decide +kernel)
lemma tb246 : checkedTables fb246 19 := by
 intro lv hlv;interval_cases lv
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . exact bb246_8
 . rfl
 . exact bb246_10
 . exact bb246_11
 . exact bb246_12
 . exact bb246_13
 . exact bb246_14
 . exact bb246_15
 . exact bb246_16
 . exact bb246_17
 . rfl
 . exact bb246_19
theorem l246 : Lower1 (vars 246) (graphGoal 246) 9 := lower_forest2 (g0:=fa246) (g1:=fb246) (hints:=286328128) (before_sound k238 v238) ⟨rfl,rfl⟩ gm246 gm246 ta246 tb246 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def k246 := extendKnown k238 9 [(246,[])]
theorem v246 : Known k246 := extendKnown_ok v238 l246 (by decide +kernel)
def g127s : Array (Bits × Bits) := #[(0xfffffffffffffffffffffff0003f8001fc07f0c33f1f1111,0xa142850a1428500822f0f0000),(0x1fc000fe03f8030ccff12222,0xc183060c1830602088ff00000),(0x7f00000000300ffff4f4,0xf5ebd7af5ebd7a0200ffff0f0),(0xfe00000000007fc0031f2ff48,0x58b162c58b162c80010f0ff00),(0xfffffffffffffffffffffff00000000003f80000c22fffff,0xfffffffffffffffffffffff3e7cf9f3e7cf9f000400fffff),(0xfffffffffffffffffffffff000007ffffc00003f04444f8f,0xfffffffffffffffffffffff0a142850a1428501500000f0f),(0xffffffffffffffffffffffffffff800000000fc0088888ff,0xfffffffffffffffffffffff060c183060c183540000000ff),(0x0,0x0)]
def g127c : IndexTree ColumnInfo := (.fork 7 (.fork 3 (.leaf [(4,0,123,0,8),(0,4,91,32,8),(16,0,111,0,8)]) (.leaf [(0,16,109,2,8),(8,0,119,0,7),(1,0,126,0,7),(2,0,109,0,7)])) (.fork 4 (.leaf [(32,0,91,0,7),(64,0,63,0,7),(18,0,109,0,7),(36,0,91,0,7)]) (.leaf [(9,0,118,0,5),(1,8,54,64,5),(64,8,54,1,5),(73,0,54,0,4)])))
def g127a : Array (List Nat) := #[[],[96,81,66]]
def ka127_16 (_ : Nat) := 0x200100000000
def da127_16 (_ : Nat) := 0x9acb8879c0d269228b40ff583fd30
def da127_18 (_ : Nat) := 0x34a19537f
def la127 : Nat -> Packing
| 16 => (2,1,4,6,da127_16)
| 18 => (1,0,4,0,da127_18)
| _ => emptyPacking
def ia127 : Nat -> Nat -> Option (Nat × Nat)
| 16 => lookupWord 7 9 4 1 1 ka127_16
| _ => fun _ => none
def fa127 : Forest := ⟨127,9,fun j => g127s[j]?.getD (0,0),g127c,g127a,la127,ia127⟩
lemma ba127_16 : block fa127 16 0 2 = true := cl 8 (by decide +kernel)
lemma ba127_18 : block fa127 18 0 1 = true := cl 7 (by decide +kernel)
lemma ta127 : checkedTables fa127 18 := by
 intro lv hlv;interval_cases lv
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . exact ba127_16
 . rfl
 . exact ba127_18
set_option maxHeartbeats 0 in
theorem gm127 : graphValid fa127 (boundsBefore k246) = true := by
 simp only [graphValid,Bool.and_eq_true]
 refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=0) ?_⟩
 all_goals simp only [listPieces]
 all_goals repeat' apply And.intro
 all_goals decide +kernel
def kb127_14 (_ : Nat) := 0
def db127_14 (_ : Nat) := 0x1cf872e249dd839dd60
def kb127_16 (_ : Nat) := 0x100
def db127_16 (_ : Nat) := 0x1f3c3938a467d72596302ff3bac17f9dd30
def kb127_18 (_ : Nat) := 0x90
def db127_18 (_ : Nat) := 0x89bb448e6a844d942e747a00ff8cffe00
def kb127_19 (_ : Nat) := 0x200100000000
def db127_19 (_ : Nat) := 0x42eb2e2975969320ff583fd30
def db127_21 (_ : Nat) := 0x3514a937f
def lb127 : Nat -> Packing
| 14 => (1,3,4,0,db127_14)
| 16 => (2,2,4,6,db127_16)
| 18 => (2,1,4,6,db127_18)
| 19 => (2,1,4,5,db127_19)
| 21 => (1,0,4,0,db127_21)
| _ => emptyPacking
def ib127 : Nat -> Nat -> Option (Nat × Nat)
| 14 => lookupWord 1 1 0 0 1 kb127_14
| 16 => lookupWord 2 3 2 1 1 kb127_16
| 18 => lookupWord 1 3 2 1 1 kb127_18
| 19 => lookupWord 7 9 4 1 1 kb127_19
| _ => fun _ => none
def fb127 : Forest := ⟨127,10,fun j => g127s[j]?.getD (0,0),g127c,g127a,lb127,ib127⟩
lemma bb127_14 : block fb127 14 0 1 = true := cl 7 (by decide +kernel)
lemma bb127_16 : block fb127 16 0 2 = true := cl 8 (by decide +kernel)
lemma bb127_18 : block fb127 18 0 2 = true := cl 8 (by decide +kernel)
lemma bb127_19 : block fb127 19 0 2 = true := cl 8 (by decide +kernel)
lemma bb127_21 : block fb127 21 0 1 = true := cl 7 (by decide +kernel)
lemma tb127 : checkedTables fb127 21 := by
 intro lv hlv;interval_cases lv
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . exact bb127_14
 . rfl
 . exact bb127_16
 . rfl
 . exact bb127_18
 . exact bb127_19
 . rfl
 . exact bb127_21
theorem l127 : Lower1 (vars 127) (graphGoal 127) 10 := lower_forest2 (g0:=fa127) (g1:=fb127) (hints:=66883) (before_sound k246 v246) ⟨rfl,rfl⟩ gm127 gm127 ta127 tb127 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def k127 := extendKnown k246 10 [(127,[])]
theorem v127 : Known k127 := extendKnown_ok v246 l127 (by decide +kernel)
theorem l191 : Lower1 (vars 191) (graphGoal 191) 10 := lower_discard (m:=191) (ci:=(4,0,187,0,9)) (hints:=66883) (before_sound k127 v127) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def k191 := extendKnown k127 10 [(191,[])]
theorem v191 : Known k191 := extendKnown_ok v127 l191 (by decide +kernel)
theorem l223 : Lower1 (vars 223) (graphGoal 223) 11 := lower_discard (m:=223) (ci:=(4,0,219,0,10)) (hints:=67395) (before_sound k191 v191) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def k223 := extendKnown k191 11 [(223,[])]
theorem v223 : Known k223 := extendKnown_ok v191 l223 (by decide +kernel)
theorem l247 : Lower1 (vars 247) (graphGoal 247) 10 := lower_discard (m:=247) (ci:=(1,0,246,0,9)) (hints:=66885) (before_sound k223 v223) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def k247 := extendKnown k223 10 [(247,[])]
theorem v247 : Known k247 := extendKnown_ok v223 l247 (by decide +kernel)
theorem l251 : Lower1 (vars 251) (graphGoal 251) 11 := lower_discard (m:=251) (ci:=(16,0,235,0,10)) (hints:=65603) (before_sound k247 v247) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def k251 := extendKnown k247 11 [(251,[])]
theorem v251 : Known k251 := extendKnown_ok v247 l251 (by decide +kernel)
theorem l254 : Lower1 (vars 254) (graphGoal 254) 11 := lower_discard (m:=254) (ci:=(16,0,238,0,10)) (hints:=286352704) (before_sound k251 v251) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def k254 := extendKnown k251 11 [(254,[])]
theorem v254 : Known k254 := extendKnown_ok v251 l254 (by decide +kernel)
def g255s : Array (Bits × Bits) := #[(0xffe0000000001fe0001fe0001fe01fe0061867f0fc210841,0x141414141414141414141414141400041045f07c000000),(0x1fe0001fe0001fe01fe000186199ff84421082,0x181818181818181818181818181800104111ff80000000),(0x1fe0000000001fe000000000600601ffffe4f904,0x1e9e9e9e9e9e9e9e9e9e9e9e9e9e80400401ffffe0f800),(0x1fe000001fe000000000001fe18180061f8bff2208,0xb0b0b0b0b0b0b0b0b0b0b0b0b0b010100020f83ff0000),(0xffe000000000000000000000001fe000000018217fffffff,0xffe7e7e7e7e7e7e7e7e7e7e7e7e7e7e0000008007fffffff),(0x1fe00000000000001fffffe000060007e042109f47d0,0x141414141414141414141414141440002a000001f07c0),(0x1fe0000000001fffffe0000000001801f800842108ffe0,0xc0c0c0c0c0c0c0c0c0c0c0c0c0d000a800000000ffc0),(0xffffffffffffffe0000000000000001ffe0001084210843f,0xffe0202020202020202020202020202aaa0000000000003f)]
def g255c : IndexTree ColumnInfo := (.fork 6 (.fork 3 (.leaf [(1,0,254,0,11),(4,0,251,0,11),(0,16,237,2,11)]) (.leaf [(32,0,223,0,11),(8,0,247,0,10),(64,0,191,0,10)])) (.fork 3 (.leaf [(128,0,127,0,10),(18,0,237,0,10),(72,0,183,0,8)]) (.leaf [(192,0,63,0,7),(136,0,119,0,7),(0,8,54,193,7),(200,0,55,0,5)])))
def g255a : Array (List Nat) := #[[]]
def kb255_18 (_ : Nat) := 0x2
def db255_18 (_ : Nat) := 0x16f286c4f1f3a5f0f74a20b79422378f9b2f87baaa80f37aa9765cd63f375da995cd63
def kb255_20 (_ : Nat) := 0xa923508471db06c800840
def db255_20 (_ : Nat) := 0x2572e3cf87790729c79f0ee24dca4f1e7c3bc8386c9c79f0ee24fc8af1e7c3b8a3f20dc5af3e1dc52394a93c79c8e1dd0178f3c9c3b89384e3cf2f7e028f9b8f3e197b9b964e3c39e6ee7c95b2f1e7c3b9d2f2a9cfbf1e07abc9273efc781ebea3e5988ded6c1734f507360a21b036002ffd32c1aedbfd83a2176bff4cb0cb9f7fa65765cf7fb0d442e7dfd76a2173dff4cb0eb1fbfa657658ffbd32b9ac73fd93a21769fecb510b9cffa658758e7f930b9ccd3fc985da33
def kb255_21 (_ : Nat) := 0
def db255_21 (_ : Nat) := 0xe4239f1efc0dcdd765cd63
def kb255_22 (_ : Nat) := 0x10345dd03013
def db255_22 (_ : Nat) := 0xc899a5d33df1c13ae43498e786e5272508c73c3799050d94aa67be38249195ca4cf7c7049334ba67be3820a9b5ca4cf7c7048d9639e1b907c2d2a2ada4f9a85e00ffe885dbffa2173ffd639dfff5ce66ffd768ceffa2176bfe885ceffa2163
def kb255_23 (_ : Nat) := 0xa10644600
def db255_23 (_ : Nat) := 0xca5531cf0dcc4498ab9e1b945a32573931df03ad2e7263be07c96c73c3720eb639e1b906ebb687582900ffd835dbff61973dfd765ceff61d63efd7658ff75cd63
def kb255_24 (_ : Nat) := 0x48
def db255_24 (_ : Nat) := 0x591a93bc608348b49de3041ab224ef1822d2d01ff9dfff337fe33
def kb255_25 (_ : Nat) := 0x484
def db255_25 (_ : Nat) := 0x950c58ce1744aa434670ba2448ce1741eaa801ff5dbfeb9ffd63
def db255_27 (_ : Nat) := 0xa4862e07ff
def lb255 : Nat -> Packing
| 18 => (2,4,4,7,db255_18)
| 20 => (14,3,4,10,db255_20)
| 21 => (1,3,4,0,db255_21)
| 22 => (8,2,4,9,db255_22)
| 23 => (6,2,4,8,db255_23)
| 24 => (3,1,4,7,db255_24)
| 25 => (3,1,4,7,db255_25)
| 27 => (1,0,4,0,db255_27)
| _ => emptyPacking
def ib255 : Nat -> Nat -> Option (Nat × Nat)
| 18 => lookupWord 1 2 1 1 0 kb255_18
| 20 => lookupWord 6 15 4 4 0 kb255_20
| 21 => lookupWord 1 1 0 0 0 kb255_21
| 22 => lookupWord 5 10 4 3 0 kb255_22
| 23 => lookupWord 4 8 3 3 0 kb255_23
| 24 => lookupWord 1 3 2 2 0 kb255_24
| 25 => lookupWord 2 4 2 2 0 kb255_25
| _ => fun _ => none
def fb255 : Forest := ⟨255,13,fun j => g255s[j]?.getD (0,0),g255c,g255a,lb255,ib255⟩
lemma bb255_18 : block fb255 18 0 2 = true := cl 9 (by decide +kernel)
lemma sb255_20_0 : block fb255 20 0 5 = true := cl 9 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma sb255_20_1 : block fb255 20 5 9 = true := cl 10 (by decide +kernel)
lemma bb255_20 : block fb255 20 0 14 = true := (@block_merge fb255 20 0 5 9 (sb255_20_0) sb255_20_1)
lemma bb255_21 : block fb255 21 0 1 = true := cl 8 (by decide +kernel)
lemma sb255_22_0 : block fb255 22 0 3 = true := cl 9 (by decide +kernel)
lemma sb255_22_1 : block fb255 22 3 5 = true := cl 10 (by decide +kernel)
lemma bb255_22 : block fb255 22 0 8 = true := (@block_merge fb255 22 0 3 5 (sb255_22_0) sb255_22_1)
lemma sb255_23_0 : block fb255 23 0 4 = true := cl 9 (by decide +kernel)
lemma sb255_23_1 : block fb255 23 4 2 = true := cl 10 (by decide +kernel)
lemma bb255_23 : block fb255 23 0 6 = true := (@block_merge fb255 23 0 4 2 (sb255_23_0) sb255_23_1)
lemma bb255_24 : block fb255 24 0 3 = true := cl 9 (by decide +kernel)
lemma bb255_25 : block fb255 25 0 3 = true := cl 9 (by decide +kernel)
lemma bb255_27 : block fb255 27 0 1 = true := cl 8 (by decide +kernel)
lemma tb255 : checkedTables fb255 27 := by
 intro lv hlv;interval_cases lv
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . rfl
 . exact bb255_18
 . rfl
 . exact bb255_20
 . exact bb255_21
 . exact bb255_22
 . exact bb255_23
 . exact bb255_24
 . exact bb255_25
 . rfl
 . exact bb255_27
set_option maxHeartbeats 0 in
theorem gm255 : graphValid fb255 (boundsBefore k254) = true := by
 simp only [graphValid,Bool.and_eq_true]
 refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=0) ?_⟩
 all_goals simp only [listPieces]
 all_goals repeat' apply And.intro
 all_goals decide +kernel
theorem imp255 : Impossible1 (graphGoal 255) 13 1 (vars 255).toFinset := impossible_forest_t1 (g:=fb255) (before_sound k254 v254) gm255 tb255 (by decide +kernel) ⟨rfl,rfl⟩
end PEqualNP.Outside.L_meta_30847
theorem PEqualNP.Outside.L_meta_30847 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  exact PEqualNP.Outside.L_meta_30847.main_from_imp255 PEqualNP.Outside.L_meta_30847.imp255
