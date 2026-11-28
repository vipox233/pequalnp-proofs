import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_52624.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_52624
open PEqualNP.CircuitLowerBounds
private def word80 (xs : List Nat) : Nat :=
  xs.foldl (fun a b => (a <<< 80) ||| b) 0

abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩ 
  all_goals simp_all [flipOp,allowed]

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem nrm_false (a : Sig) : nrm false a = a := rfl
theorem nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply bit_ext
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,bit_prime,ha,hb,bit_bin,bit_neg,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,bit_neg,bit_prime]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)

private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
theorem prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := bin_rep (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [nrm_false] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := nrm_prime d a b
    unfold Repr
    rw [eq]
    exact bin_rep e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨norm_ne_one a,norm_ne_one b⟩)
theorem repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
private lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]

abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)

def supply {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, Available u pool a

def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
theorem Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach u roots p bank) (ha : Available u bank a)
      (hb : Available u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : allowed u op) (ka kb : Bool) (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
theorem avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R u} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)

theorem available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))

theorem extend_two {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (combine op a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩
theorem comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩
theorem extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R u} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run u goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach u roots p bank) (hs : supply u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply u T (comb op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl
theorem restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

theorem projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega


abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,bit_bin,comb]
  split_ifs <;> rfl

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih =>
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
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext
  intro r
  rw [bit_table,bit_prime,bit_table,bit_table]
  cases d <;> rfl

theorem available_rep {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (bit_table _ i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (bit_table _ i).trans (bit_one i).symm)
  · have := table_inv a
    refine Or.inl ?_
    rw [←nrm_neg,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

theorem reach_live_sub {u} {roots : List (Wire Row)} {p bank}
    (h : Reach u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,table_prime] at sub
    have rep := prime_rep d (available_rep ha) (available_rep hb)
    obtain ⟨k',S',hk,run',sub'⟩ := pull_gate (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩

def plainWord (a : Sig) : Bool := !(bit 0 a)
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem reach_live {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (h : Reach u (roots.map observe) p bank) (hit : Available u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  unfold Repr at hm
  rw [nrm_id (by simpa [plainWord] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,table_observe]
  rw [e,nrm_map nR] at hs
  exact hs

theorem live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [(BitVec.ofNat 512 (word80 [0xaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa])),(BitVec.ofNat 512 (word80 [0xcccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc])),(BitVec.ofNat 512 (word80 [0xf0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0])),(BitVec.ofNat 512 (word80 [0xff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00])),(BitVec.ofNat 512 (word80 [0xffff0000,0xffff0000ffff0000ffff,0xffff0000ffff0000,0xffff0000ffff0000ffff,0xffff0000ffff0000,0xffff0000ffff0000ffff,0xffff0000ffff0000])),(BitVec.ofNat 512 (word80 [0xffffffff,0xffffffff0000,0xffffffff00000000,0xffffffff00000000ffff,0xffff00000000ffffffff,0xffffffff0000,0xffffffff00000000])),(BitVec.ofNat 512 (word80 [0xffffffff,0xffffffff000000000000,0xffffffffffffffff,0xffff,0xffffffffffff00000000,0xffffffffffff,0xffff0000000000000000])),(BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xffff0000000000000000,0xffff,0xffffffffffffffffffff,0xffffffff000000000000,0])),(BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xffffffffffffffffffff,0xffffffffffffffff0000,0,0,0]))]
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xfefefffffffefffffefe,0xfffeffeefefaeca0ffff,0xffffffffffffffffffff,0xfffffefefffffffeffff,0xfefefffeffeefefaeca0]))
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply bit_ext
  intro r
  simp only [bit_rename,bit_bin]

theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {u T k S} (h : Live u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live u (rename f T) k (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {u T k S} (h : Live u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      subst none
      rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {u roots T L} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible u T L roots.toFinset) : Lower u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower u other G L) : Lower u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := reach_live pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply u (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega



def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := live_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {u T k S} (h : Live u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  simp

def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available u bank (restrictRows f (observe a))

theorem availableB_sound {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply u f bank pool)
    (check : availableB u d pool a = true) : Available u bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,masked_one dom ho⟩)
  · exact masked_eq dom he ▸ supplyB v hv
  · have h := avail_inv hu (masked_eq dom he ▸ supplyB v hv)
    rw [obs_neg] at h
    have e : inv (restrictRows f (inv (observe a))) = restrictRows f (observe a) := by
      funext r
      simp [inv,restrictRows]
    rwa [e] at h

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) := bin c.1 c.2.1 c.2.2
def allowedB (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
theorem allowedB_ok {u d} (h : allowedB u d=true) : allowed u d := by
  simpa [allowedB,allowed] using h
def choiceOK (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  allowedB u c.1 && (availableB u d pool c.2.1 && availableB u d pool c.2.2)

theorem pay_choice {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (c : Choice) (valid : choiceOK u d pool c = true) :
    ∃ next, Reach u roots (q+1) next ∧ poolSupply u f next (choiceVal c :: pool) := by
  simp only [choiceOK,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := comb_prime (allowedB_ok valid.1) (availableB_sound dom hs valid.2.1)
    (availableB_sound dom hs valid.2.2)
  refine ⟨_,Reach.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [choiceVal,obs_bin,restrict_comb,e]
    exact Or.inl (by simp)
  · exact available_cons _ (hs _ hm)

def makePool (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK u d pool c then makePool u d (choiceVal c::pool) cs else none

theorem makePool_sound {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (cs : List Choice) {result} (ok : makePool u d pool cs = some result) :
    ∃ next, Reach u roots (q+cs.length) next ∧ poolSupply u f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {u roots w} (ok : freeWord roots w = true) :
    Available u (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true,funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {u ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available u (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {u ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (nT : plainWord T=true) (nR : raw.all plainWord=true) (pG : proper G)
    (hL : Lower u base G L) : Lower u raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT nT nR pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {u ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower u base G L) :
    Slice u raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  plainWord T && raw.all plainWord && xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok.2 _ hm)

theorem essential_plain {T raw xs} (ok : checkEssential T raw xs = true) :
    plainWord T=true ∧ raw.all plainWord=true := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  exact ok.1
theorem lower_count {u raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower u raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩ := reach_live properT (essential_plain ok).1 (essential_plain ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := live_size run
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {u ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower u base G L) :
    Lower u raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩



def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def typeWord (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def varsX (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [typeWord (m/512-1)]
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 2) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => (word80 [0x1000000000000,0x10000000000000001,0x10000,0x100000000,0x1000000000000,0x10000000000000001])
  | 1 => (word80 [0x10000000000000000,0x10000,0,0x1000000000000,1])
  | 2 => (word80 [1,0x10000,0,0,0x10000000000000001])
  | 3 => (word80 [0x10000,0,0,1])
  | 4 => (word80 [0x100000000,0x1000000000000,0x10000000000000001])
  | 5 => (word80 [0x1000000000000,1])
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def supportPairs (t : Nat) (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) =>
    let r := if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 512+512*(c.1/512)
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (varsX free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (varsX free) (varsX q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {u} {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice u (varsX (rawMask m c)) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := fixRows z o
  let raw := rawMask m (z,o,q,s,L)
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  change (((properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def carryOK (old rep : Nat) (swaps : List Nat) :=
  (properB (graphGoal old) && plainWord (graphGoal old) && (varsX old).all plainWord) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (varsX old) (graphGoal old) (varsX rep) (graphGoal rep)
theorem carry_of {u old rep L swaps} (ok : carryOK old rep swaps = true)
    (h : Lower u (varsX rep) (graphGoal rep) L) : Lower u (varsX old) (graphGoal old) L := by
  simp only [carryOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound {u} (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower u (varsX q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he


abbrev BoundPool := Sig × Nat × Nat × List Sig
def BoundPool.domain (c : BoundPool) : Sig := c.1
def BoundPool.bound (c : BoundPool) : Nat := c.2.1
def BoundPool.paid (c : BoundPool) : Nat := c.2.2.1
def BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2

def ValidPool (u : Bool) (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach u (roots.map observe) q ws → Available u ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach u (roots.map observe) c.paid bank ∧ poolSupply u f bank c.wires ∧ True

theorem build_valid {u raw T d lb} (h : Slice u raw T d lb) (cs : List Choice) {ws}
    (build : makePool u d raw cs = some ws) : ValidPool u raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩

theorem valid_exclude {u raw T c} (valid : ValidPool u raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB u c.domain c.wires a = true)
    (buy : if paid then choiceOK u c.domain c.wires choice = true
       else availableB u c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible u T k (choiceVal choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach u (roots.map observe) n out)
      (zs : poolSupply u f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply u out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have point : ∀ v ∈ c.wires, Available u out (restrictRows f (observe v)) :=
        fun v hu => hc v (List.mem_cons_of_mem _ hu)
      exact availableB_sound dom point (known _ hm)

def scalarPoolCut (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB u c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB u c.domain c.wires)) && (!extra || choiceOK u c.domain c.wires op)

theorem scalarPoolCut_sound {u raw T c} (valid : ValidPool u raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut u c k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB u c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB u c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (u : Bool) (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {u raw T d L cs c} (slice : Slice u raw T d L)
    (h : materialize u raw cs d L = some c) : ValidPool u raw T c := by
  unfold materialize at h
  cases he : makePool u d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he


abbrev Bits := BitVec 152
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 152 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 152 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 152 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 152 → Row) (x : Decor) := x.2 = pairSig r s x.1
def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)

theorem ofRows_bin {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    ofRows r (bin d a b) = bv d (ofRows r a) (ofRows r b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  simp only [faithful,dbin,pairSig,ofRows_bin,hx,hy]

def defaultDecor : Decor := (zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[dbin ((bits >>> 8) &&& 3) a b])
theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ decodeBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 152) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem coordinate8 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 2) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov := Bits × Bits × Bits

def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)

def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2



theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb

theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
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
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl

def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩


def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List Sig → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws) ws).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag query xs, xs ∈ links tag query → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Bool
def preCov (u : Bool) (ws : List Decor) : CovPair := (coverage (!u) ws,u)
def restCov (v : Cov) (a b : Bits) (ka kb : Bool) :=
  if ka then (if kb then v.1 else takeOne v b) else if kb then takeOne v a else takeTwo v a b

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    (delTwo ws a b ka kb).Sublist ws := (delOne_sub _ _ _).trans (delOne_sub _ _ _)
theorem len_keep (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) :
    (delTwo ws a b ka kb).length =
      ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]

def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List Sig → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 152 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild cov.2 pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem evalMove_sound {u raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag query xs, xs ∈ links tag query → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov u ws,pools,links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := dbin op a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h (pair_sep pairs)
  let d := !u
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : (coverage d rest).1 = restCov (coverage d ws) (column d a.2) (column d b.2) ka kb :=
    cover_two d a b ha hb ne ka kb
  have hf := faithful_bin op (faith _ ha) (faith _ hb)
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact closeChild_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h

def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem opsOf_mem {u d} (h : allowed u d) : d ∈ opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [opsOf]
  · cases u <;> simp [opsOf]
  · simp [opsOf]
  · simp [opsOf]
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair ctx a b))
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (opsOf_mem hd)
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx d a b (dbin d a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail

theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,mem_delone wn,mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (moveFront ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto

theorem node_sound {u raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag query xs, xs ∈ links tag query → Impossible u T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov u ws,pools,links) ws = true) :
    Impossible u T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
  have ab : a≠b := fun e => ne (congrArg Prod.fst e)
  have one (a b : Decor) (d : Nat) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : testPair (cap,ws.length,ws,preCov u ws,pools,links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←binary_front nd aa bb ne']
    exact evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (testPair_at test ka kb)
  rcases all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)


theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
theorem rotate_excluded {u T n} {ws : List Sig} (hi : Impossible u T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible u T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k hk run

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
private def limbs80 (pages : Array (Array Nat)) (i : Nat) : Nat :=
  ((pages[i/32]?).getD #[])[i%32]?.getD 0

def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/80
  let shift := pos % 80
  let lo := word i >>> shift
  if shift+len ≤ 80 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (80-shift))) &&& ((1 <<< len)-1)


def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


def lookupShort (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 4 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.mode (g : Forest) : Bool := !(g.1.testBit 10)
def Forest.cap (g : Forest) : Nat := g.2.1
def Forest.samples (g : Forest) : Nat → Bits × Bits := g.2.2.1
def Forest.cols (g : Forest) : List ColumnInfo := g.2.2.2.1
def Forest.autos (g : Forest) : List (List Nat) := g.2.2.2.2.1
def Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1
def Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  exact raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 152) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

def prefixWidth (d : Nat) := 10*(d-1)
def denseRowWidth (d flags : Nat) := flags % 16 + (if d=0 then 0 else 10) + flags/16
def denseRowStart (d raw dict : Nat) :=
  (dict % 65536)*prefixWidth d + (dict/65536)*(raw+d)

def forestRecord (tab : Packing) (raw i : Nat) : Nat :=
  let (_,d,_,dict,flags,_,marker,word) := tab
  let width := 10*d+raw+d
  if marker<1024 then packedAt word (i*width) width else
    let off := denseRowStart d raw dict+i*denseRowWidth d flags
    let pre := packedAt word off (flags % 16)
    let lastBits := if d=0 then 0 else 10
    let last := packedAt word (off+flags % 16) lastBits
    let mask := packedAt word (off+flags % 16+lastBits) (flags/16)
    let base := (dict % 65536)*prefixWidth d
    packedAt word (pre*prefixWidth d) (prefixWidth d) |||
      (last <<< prefixWidth d) ||| (packedAt word (base+mask*(raw+d)) (raw+d) <<< (10*d))


def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := forestRecord (g.levels k) raw.length i
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols[idx]?).bind fun ci =>
    materialize g.mode (varsX (rawMask g.mask ci)) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool g.mode (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (List.mem_of_getElem? e)

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def forceDatum {α : Type} : Nat → (Nat → α) → α
  | 0, next => next 0
  | n+1, next => next (n+1)

def readSortedHints (data : Nat → Nat) (dict cw d gapBits : Nat) :
    Nat → Nat → Nat → List (Nat × Nat)
  | 0,_,_ => []
  | left+1,st,first =>
    forceDatum st fun pos => forceDatum first fun base =>
    forceDatum (packedAt data pos 32) fun head =>
    forceDatum (Nat.log2 (head ^^^ (head+1))) fun ones =>
    forceDatum (base+(ones <<< gapBits)+packedAt data (pos+ones+1) gapBits) fun key =>
    forceDatum (packedAt data (dict+key*(cw+d)) (cw+d)) fun pair =>
      (pair &&& ((1 <<< cw)-1),pair >>> cw) ::
        readSortedHints data dict cw d gapBits left (pos+ones+1+gapBits) (key+1)

def promoteHints {α : Type} (a b : Nat) (xs : List α) : List α :=
  let rec collect : List α → Nat → List α → List α → List α → List α
    | [],_,first,second,other => first ++ second ++ other.reverse
    | x::tail,i,first,second,other =>
      if i=a then collect tail (i+1) [x] second other
      else if i=b then collect tail (i+1) first [x] other
      else collect tail (i+1) first second (x::other)
  collect xs 0 [] [] []

def forestHints (tab : Packing) (raw i : Nat) : List (Nat × Nat) :=
  let (num,d,cw,dict,flags,ow,marker,data) := tab
  if marker<1024 then
    let start := num*(10*d+raw+d)
    let pos := start+num*ow+packedAt data (start+i*ow) ow
    getPairs data cw d (packedAt data pos 6) (pos+6+marker)
  else
    let off := denseRowStart d raw dict + num*denseRowWidth d flags
    let pairs := off+num*ow
    let priority := decide (4096≤marker)
    let pos := pairs+(marker-(if priority then 4096 else 1024))*(cw+d)+packedAt data (off+i*ow) ow
    let n := packedAt data pos 5
    let gap := packedAt data (pos+5) 3
    if !priority || decide (n≤1) then readSortedHints data pairs cw d gap n (pos+8) 0 else
      let width := (n-1).log2+1
      let a := packedAt data (pos+8) width
      let b := if n=2 then 1-a else packedAt data (pos+8+width) width
      let extra := if n=2 then width else 2*width
      let xs := readSortedHints data pairs cw d gap n (pos+8+extra) 0
      promoteHints a b xs

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible g.mode (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))

abbrev SixBits := Bool × Bool × Bool × Bool × Bool × Bool
abbrev SixRows := Fin 512 × Fin 512 × Fin 512 × Fin 512 × Fin 512 × Fin 512
def readSix (r : SixRows) (v : Sig) : SixBits := ⟨bit r.1 v,bit r.2.1 v,bit r.2.2.1 v,bit r.2.2.2.1 v,bit r.2.2.2.2.1 v,bit r.2.2.2.2.2 v⟩
def sixCost (x : SixBits) : Nat := (#[0,2,1,1,1,1,2,0,2,2,2,2,2,2,3,2,1,2,1,2,2,1,2,1,1,2,2,1,1,2,2,1,1,2,2,1,1,2,2,1,1,2,1,2,2,1,2,1,2,3,2,2,2,2,2,2,0,2,1,1,1,1,2,0] : Array Nat)[1 * x.1.toNat+2 * x.2.1.toNat+4 * x.2.2.1.toNat+8 * x.2.2.2.1.toNat+16 * x.2.2.2.2.1.toNat+32 * x.2.2.2.2.2.toNat]?.getD 3
def crossOp (d : Nat) (a b : Bool) :=
  if d=0 then a && b else if d=1 then a || b else if d=2 then a && !b else !a && b
def applySix (d : Nat) (a b : SixBits) : SixBits := ⟨crossOp d a.1 b.1,crossOp d a.2.1 b.2.1,crossOp d a.2.2.1 b.2.2.1,crossOp d a.2.2.2.1 b.2.2.2.1,crossOp d a.2.2.2.2.1 b.2.2.2.2.1,crossOp d a.2.2.2.2.2 b.2.2.2.2.2⟩
theorem readSix_bin (r : SixRows) (d) (a b : Sig) :
    readSix r (bin d a b) = applySix d (readSix r a) (readSix r b) := by
  simp only [readSix,applySix,bit_bin,crossOp]

private def flipSix (v : SixBits) : SixBits :=
  ⟨!v.1,!v.2.1,!v.2.2.1,!v.2.2.2.1,!v.2.2.2.2.1,!v.2.2.2.2.2⟩

private theorem flipSix_cost : ∀ v : SixBits, sixCost (flipSix v) = sixCost v := by decide +kernel
private theorem capSix_cost : ∀ v : SixBits, sixCost v ≤ 3 := by decide +kernel

private theorem orSix_eq (x y : SixBits) :
    applySix 1 x y = flipSix (applySix 0 (flipSix x) (flipSix y)) := by
  obtain ⟨a,b,c,d,e,f⟩ := x
  obtain ⟨g,h,i,j,k,l⟩ := y
  have dm (v w : Bool) : (v || w) = (!((!v) && (!w))) := by cases v <;> cases w <;> rfl
  change (a||g,b||h,c||i,d||j,e||k,f||l) =
    (!(!a && !g),!(!b && !h),!(!c && !i),!(!d && !j),!(!e && !k),!(!f && !l))
  exact Prod.ext (dm a g) (Prod.ext (dm b h) (Prod.ext (dm c i)
    (Prod.ext (dm d j) (Prod.ext (dm e k) (dm f l)))))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem sixAnd000 : ∀ (x y z : Bool) (b : SixBits),
    sixCost ⟨false,false,false,x,y,z⟩ + sixCost b < 3 →
    sixCost (applySix 0 ⟨false,false,false,x,y,z⟩ b) ≤ sixCost ⟨false,false,false,x,y,z⟩ + sixCost b := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem sixAnd001 : ∀ (x y z : Bool) (b : SixBits),
    sixCost ⟨false,false,true,x,y,z⟩ + sixCost b < 3 →
    sixCost (applySix 0 ⟨false,false,true,x,y,z⟩ b) ≤ sixCost ⟨false,false,true,x,y,z⟩ + sixCost b := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem sixAnd010 : ∀ (x y z : Bool) (b : SixBits),
    sixCost ⟨false,true,false,x,y,z⟩ + sixCost b < 3 →
    sixCost (applySix 0 ⟨false,true,false,x,y,z⟩ b) ≤ sixCost ⟨false,true,false,x,y,z⟩ + sixCost b := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem sixAnd011 : ∀ (x y z : Bool) (b : SixBits),
    sixCost ⟨false,true,true,x,y,z⟩ + sixCost b < 3 →
    sixCost (applySix 0 ⟨false,true,true,x,y,z⟩ b) ≤ sixCost ⟨false,true,true,x,y,z⟩ + sixCost b := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem sixAnd100 : ∀ (x y z : Bool) (b : SixBits),
    sixCost ⟨true,false,false,x,y,z⟩ + sixCost b < 3 →
    sixCost (applySix 0 ⟨true,false,false,x,y,z⟩ b) ≤ sixCost ⟨true,false,false,x,y,z⟩ + sixCost b := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem sixAnd101 : ∀ (x y z : Bool) (b : SixBits),
    sixCost ⟨true,false,true,x,y,z⟩ + sixCost b < 3 →
    sixCost (applySix 0 ⟨true,false,true,x,y,z⟩ b) ≤ sixCost ⟨true,false,true,x,y,z⟩ + sixCost b := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem sixAnd110 : ∀ (x y z : Bool) (b : SixBits),
    sixCost ⟨true,true,false,x,y,z⟩ + sixCost b < 3 →
    sixCost (applySix 0 ⟨true,true,false,x,y,z⟩ b) ≤ sixCost ⟨true,true,false,x,y,z⟩ + sixCost b := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem sixAnd111 : ∀ (x y z : Bool) (b : SixBits),
    sixCost ⟨true,true,true,x,y,z⟩ + sixCost b < 3 →
    sixCost (applySix 0 ⟨true,true,true,x,y,z⟩ b) ≤ sixCost ⟨true,true,true,x,y,z⟩ + sixCost b := by decide +kernel

private theorem sixAnd_all (a b : SixBits) : sixCost (applySix 0 a b) ≤ sixCost a + sixCost b := by
  by_cases h : 3 ≤ sixCost a + sixCost b
  · exact (capSix_cost _).trans h
  · obtain ⟨p,q,r,x,y,z⟩ := a
    cases p <;> cases q <;> cases r
    · exact sixAnd000 _ _ _ _ (by omega)
    · exact sixAnd001 _ _ _ _ (by omega)
    · exact sixAnd010 _ _ _ _ (by omega)
    · exact sixAnd011 _ _ _ _ (by omega)
    · exact sixAnd100 _ _ _ _ (by omega)
    · exact sixAnd101 _ _ _ _ (by omega)
    · exact sixAnd110 _ _ _ _ (by omega)
    · exact sixAnd111 _ _ _ _ (by omega)
theorem six_cost_binary (d : Fin 4) (a b : SixBits) :
    sixCost (applySix d a b) ≤ sixCost a + sixCost b := by
  have lim := d.isLt
  have h : d.val=0 ∨ d.val=1 ∨ d.val=2 ∨ d.val=3 := by omega
  rcases h with h | h | h | h <;> rw [h]
  · exact sixAnd_all a b
  · rw [orSix_eq,flipSix_cost]
    simpa only [flipSix_cost] using sixAnd_all (flipSix a) (flipSix b)
  · change sixCost (applySix 0 a (flipSix b)) ≤ _
    simpa only [flipSix_cost] using sixAnd_all a (flipSix b)
  · change sixCost (applySix 0 (flipSix a) b) ≤ _
    simpa only [flipSix_cost] using sixAnd_all (flipSix a) b

theorem measure_live_tree (w : Sig → Nat) (hb : ∀ {d u} (a b), allowed u d →
    w (bin d a b) ≤ w a + w b) {u T k S} (h : Live u T k S) :
    S.card = k+1 → w T ≤ ∑ s ∈ S, w s := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb' ab fr tail ih =>
    intro saturated
    have zU : bin d a b ∉ U := fun m => fr (by simp [m])
    have bound := live_size tail
    rw [Finset.card_insert_of_notMem zU] at bound
    have bc := Finset.card_insert_le (a:=b) (s:=U)
    have ac := Finset.card_insert_le (a:=a) (s:=insert b U)
    have aU : a ∉ insert b U := by
      intro p
      rw [Finset.insert_eq_of_mem p] at saturated
      omega
    have bU : b ∉ U := by
      intro p
      rw [Finset.insert_eq_of_mem p] at saturated ac
      omega
    rw [Finset.card_insert_of_notMem aU,Finset.card_insert_of_notMem bU] at saturated
    have tp : (insert (bin d a b) U).card = k+1 := by rw [Finset.card_insert_of_notMem zU]; omega
    have step := ih tp
    rw [Finset.sum_insert zU] at step
    rw [Finset.sum_insert aU,Finset.sum_insert bU]
    have price := hb a b hd
    omega

theorem six_cut {u T k S} (r : SixRows) (size : S.card = k+1)
    (cost : (∑ s ∈ S, sixCost (readSix r s)) < sixCost (readSix r T)) :
    ∀ t, t ≤ k → ¬ Live u T t S := by
  intro t ht live
  have wid := live_size live
  have eq : S.card=t+1 := by omega
  apply Nat.not_lt_of_ge (measure_live_tree (fun a => sixCost (readSix r a)) (by
    intro d v a b h
    rw [readSix_bin]
    obtain h|h|⟨_,h⟩|⟨_,h⟩ := allowed_four h
    all_goals subst d
    · exact six_cost_binary 0 _ _
    · exact six_cost_binary 1 _ _
    · exact six_cost_binary 2 _ _
    · exact six_cost_binary 3 _ _) live eq) cost

def cubRows (word : Nat) : SixRows := ⟨Fin.ofNat 512 ((word >>> 0) % 256),Fin.ofNat 512 ((word >>> 8) % 256),Fin.ofNat 512 ((word >>> 16) % 256),Fin.ofNat 512 ((word >>> 24) % 256),Fin.ofNat 512 ((word >>> 32) % 256),Fin.ofNat 512 ((word >>> 40) % 256)⟩

def inlineSix (T : Sig) (k : Nat) (ws : List Sig) (word : Nat) : Bool :=
  let S := ws.toFinset
  let r := cubRows word
  decide (S.card = k+1) && decide ((∑ v ∈ S, sixCost (readSix r v)) < sixCost (readSix r T))

theorem inlineSix_sound {T k ws word} (ok : inlineSix T k ws word=true) (u : Bool) :
    Impossible u T k ws.toFinset := by
  simp only [inlineSix,Bool.and_eq_true,decide_eq_true_eq] at ok
  exact six_cut (cubRows word) ok.1 ok.2

def closeSix (T : Sig) (k : Nat) (marks : List Nat) (ws : List Sig) : List (List Sig) :=
  if marks.any (inlineSix T k ws) then [ws] else []

theorem closeSix_sound {T k marks ws xs} (h : xs ∈ closeSix T k marks ws) (u : Bool) :
    Impossible u T k xs.toFinset := by
  unfold closeSix at h
  split at h
  next e =>
    obtain ⟨word,_,hw⟩ := List.any_eq_true.mp e
    have same : xs=ws := by simpa only [List.mem_singleton] using h
    subst xs
    exact inlineSix_sound hw u
  next => simp at h

private def sixWordsP0 : Array Nat := #[44127031068939,18713189552148,158898757832724,22063515501573,44127031001098,44127031003146,145691733197829,158898759938100,45127372513314,18713191657524,57385863414789,41811607363617,176482353815586,147364723654785,145157076910209,158885872734225,158415842476164,141858491891844,141910032253972,150680488804482,141910032285840,176094196531722,55057487831073,18713189548052,145221502402704,143082576183456,18777865715973,37555731497739,6118181962001,6118181962772,142457623806996,176482354078758,57385863546375,22011774570513,158898757828628,6116310253953,142457625912372,141978752811168,143625855959586,176094196597515,145691733329415,20985512591879,41811607388289,6064569319809,6116310254724,5583525642513,54100213629189,22546430886917,145756160795700,57334122483729,22608984671364,147497869672608,45127372776486,48542324492298,176482354868274,158402957377665,5570590409748,22546430890001,176478058782753,176068426367106,22011774566417,193738190389380,41386917233025,37426379104296]
private def sixWordsP1 : Array Nat := #[45127373566002,61788204959754,20920836296724,6051634087044,39045606416544,20920836292628,45127372537986,57390158413953,158402957377541,158415842476037,55070372757633,7859892912417,18777865715717,19310449787265,19245773619344,15449207087264,143018167370772,158490735939604,158885872865811,141858491891732,142526344331553,5570592515124,38071135371906,142406083412229,145756158690324,142406083543815,8272216064385,167237839388802,160610604122241,12683197809282,160743750140064,7791172518419,158898757832709,144083318743080,54100213760775,147364723654689,36852967277319,7791172419728,54445153194004,36844377351206,40905873555729,24219421442579,150680488804386,141910032285716,20985512592135,44127031266318,153991958921346,176064131334273,57334122615315,11141180819496,38530202476584,55602957000864,48542324755470,57338417479809,158885872734213,14353984159904,22063515500549,38564562763920,145691733196805,21105773379873,160610604122145,36904507671315,30898397610114,54100213661828]
private def sixWordsP2 : Array Nat := #[36844378140722,36356916019344,176542484267281,55057487855745,55199733383553,24352573620609,24404314554753,28695087554720,180543850283281,36456220067342,36456220856858,180543850315920,54632797700481,142457623806225,142457623937811,21518096531841,57248424592903,18713189683734,42357076533408,61788206012442,20920836428310]
private def sixWords : Array (Array Nat) := #[sixWordsP0,sixWordsP1,sixWordsP2]
private def sixMenuStartsP0 : Array Nat := #[0,1,17,35,81,97,113,129,145,162,193,209,225,241,257,273,289,305,321,337,353,369,385,401,417,433,449,465,481,497,513,529,545,562,596,659,705,721,737,754,786,818,851,898,929,947,999,1106,1138,1174,1271,1382,1473,1489,1505,1521,1538,1572,1633,1649,1665,1682,1715,1764]
private def sixMenuStartsP1 : Array Nat := #[1826,1859,1906,1938,1969,1986,2018,2050,2086,2181,2258,2290,2322,2354,2385,2402,2434,2465,2483,2532,2594,2625,2642,2673,2693,2775,2883,2933,3015,3121,3138,3170,3201,3222,3314,3347,3394,3426,3458,3490,3523,3570,3602,3636,3699,3747,3795,3842,3874,3907,3955,4001,4018,4049,4067,4114,4149,4229,4307,4355,4402,4433,4449,4465]
private def sixMenuStartsP2 : Array Nat := #[4482,4513,4529,4545,4561,4579,4625,4641,4657,4673,4689,4705,4721,4737,4753,4769,4785,4801,4818,4849,4865,4882,4913,4931,4978,5009,5025,5042,5073,5089,5105,5121,5138,5170,5202,5234,5265,5286,5381,5463,5572,5635,5683,5730,5763,5810,5845,5923,5970,6003,6050,6085,6165,6246,6338,6370,6404,6467,6514,6548,6613,6692,6756,6818]
private def sixMenuStartsP3 : Array Nat := #[6850,6885,6961,6980,7042,7074,7107,7156,7220,7283,7330,7362,7394,7426,7459,7507,7555,7601,7618,7652,7721,7858,7894,7987,8034,8066,8099,8148,8210,8242,8274,8307,8354,8386,8418,8449,8467,8514,8547,8596,8658,8693,8772,8834,8866,8897,8915,8965,9046,9139,9188,9253,9332,9394,9430,9525,9602,9636,9700,9764,9827,9874,9906,9938]
private def sixMenuStartsP4 : Array Nat := #[9972,10036,10099,10146,10179,10226,10259,10309,10385,10404,10467,10517,10594,10629,10709,10788,10851,10899,10949,11027,11077,11155,11208,11331,11380,11442,11476,11539,11590,11682,11713,11732,11796,11858,11892,11958,12054,12146,12181,12263,12372,12437,12515,12562,12598,12692,12757,12834,12868,12933,13011,13061,13138,13171,13225,13365,13446,13538,13571,13620,13681,13697,13714,13746]
private def sixMenuStartsP5 : Array Nat := #[13783]
private def sixMenuStarts : Array (Array Nat) := #[sixMenuStartsP0,sixMenuStartsP1,sixMenuStartsP2,sixMenuStartsP3,sixMenuStartsP4,sixMenuStartsP5]
private def sixMenuWordsP0 : Array Nat := #[1,4,23,34,69,23,41,69,39,70,0,8,42,27,43,6,44,96,28,29,36,45,3,72,73,46,47,120,122,11,0,127,81,5,106,22,83,2,16,18,71,0,8,71,2,18,16,8,18,0,18,23,34,1,41,95,1,41,56,35,43,44,6,12]
private def sixMenuWordsP1 : Array Nat := #[35,43,44,96,118,12,59,12,25,3,28,29,45,72,73,3,8,28,29,45,72,73,1,26,30,36,74,79,74,8,30,26,31,36,3,7,10,48,21,60,121,0,98,75,80,123,99,100,124,125,8,126,0,11,70,18,80,9,98,101,34,69,0,100]
private def sixMenuWordsP2 : Array Nat := #[0,99,46,81,102,103,104,128,7,46,81,102,104,7,103,27,32,2,21,0,11,34,5,129,5,101,130,23,34,105,40,42,82,131,79,135,97,5,18,136,3,11,22,47,57,1,2,3,7,27,42,106,7,10,49,2,7,9,10,48,0,1,3,47]
private def sixMenuWordsP3 : Array Nat := #[57,83,107,15,15,21,1,21,76,1,3,47,57,83,107,39,70,2,71,117,0,23,71,95,41,42,28,44,4,28,44,29,35,26,29,4,29,35,74,4,26,29,31,36,46,36,46,79,35,47,3,28,4,35,47,3,4,28,119,21,36,80,27,39]
private def sixMenuWordsP4 : Array Nat := #[70,45,57,4,8,45,57,132,0,1,42,133,134,0,23,40,0,30,42,36,46,137,9,19,7,37,84,13,25,86,1,41,63,37,17,87,77,14,24,88,33,50,10,78,75,7,9,58,20,0,111,61,5,53,65,1,66,7,55,0,58,93,38,113]
private def sixMenuWordsP5 : Array Nat := #[114,22,67,91,145,17,22,2,22,12,1,2,9,19,37,84,2,9,16,61,85,1,7,9,61,85,108,138,2,9,61,139,0,8,37,0,8,62,62,140,2,13,25,2,16,11,25,27,39,86,0,8,11,0,27,0,13,19,17,20,12,17,20,87]
private def sixMenuWordsP6 : Array Nat := #[141,1,20,26,30,77,1,12,20,26,30,77,0,12,14,24,3,24,33,50,1,3,33,3,26,3,6,14,17,6,12,14,24,88,1,3,6,33,3,6,7,48,6,87,12,38,3,7,10,21,48,59,7,10,25,38,48,51,6,10,6,9,10,0]
private def sixMenuWordsP7 : Array Nat := #[2,52,64,89,90,142,143,8,19,75,9,52,8,89,8,90,0,53,0,9,109,11,22,27,0,19,27,109,0,19,0,19,20,27,0,1,11,17,19,32,52,64,144,0,32,0,2,17,20,52,64,11,22,75,11,22,0,22,0,5,11,0,5,11]
private def sixMenuWordsP8 : Array Nat := #[37,0,84,1,9,0,110,0,5,19,0,85,17,61,7,17,91,9,91,110,64,108,5,9,32,5,9,19,32,7,32,2,10,31,49,54,2,7,10,49,7,31,32,112,52,2,5,66,0,1,32,52,64,11,22,32,66,111,112,5,7,32,11,37]
private def sixMenuWordsP9 : Array Nat := #[52,53,2,15,16,18,55,6,14,15,43,13,92,2,8,15,16,18,55,6,8,14,15,43,8,12,8,13,40,89,0,8,13,90,13,40,82,92,0,1,40,5,13,5,8,5,40,5,8,40,62,5,8,13,62,0,8,14,8,14,1,31,54,1]
private def sixMenuWordsP10 : Array Nat := #[7,14,22,33,1,2,3,16,24,22,6,11,15,22,6,16,50,1,3,11,13,93,1,56,0,14,33,56,67,0,1,2,3,7,0,12,25,38,2,3,88,2,17,67,0,6,15,17,20,6,7,15,2,6,7,9,48,0,19,93,1,2,3,7]
private def sixMenuWordsP11 : Array Nat := #[13,19,21,39,59,86,114,1,7,10,49,1,76,14,33,56,67,5,12,37,2,7,25,37,38,58,2,7,68,10,15,54,68,10,15,68,115,54,115,6,15,17,20,1,10,31,49,54,68,1,10,49,51,68,94,31,51,2,10,31,51,54,2,7]
private def sixMenuWordsP12 : Array Nat := #[9,10,51,94,146,7,10,25,49,2,7,9,10,25,5,9,31,54,94,0,13,25,37,39,41,3,6,20,24,3,4,6,20,24,4,78,10,12,38,51,7,10,21,38,51,0,11,19,1,2,3,14,55,6,23,6,18,30,0,1,2,3,4,8]
private def sixMenuWordsP13 : Array Nat := #[13,14,55,4,6,8,13,23,4,6,8,13,18,30,4,60,2,12,38,2,7,21,38,63,116,0,5,9,147,2,5,53,65,66,116,148]
private def sixMenuWords : Array (Array Nat) := #[sixMenuWordsP0,sixMenuWordsP1,sixMenuWordsP2,sixMenuWordsP3,sixMenuWordsP4,sixMenuWordsP5,sixMenuWordsP6,sixMenuWordsP7,sixMenuWordsP8,sixMenuWordsP9,sixMenuWordsP10,sixMenuWordsP11,sixMenuWordsP12,sixMenuWordsP13]
private def sixMenuAtP0 : Array Nat := #[0,0,0,0,1,2,0,0,2,0,0,0,3,0,0,0,0,2,0,0,0,4,0,5,0,0,0,0,2,0,0,0,0,0,2,0,0,0,0,6,0,0,0,0,7,8,0,0,0,9,10,0,0,11,0,0,0,0,0,12,13,14,15,0]
private def sixMenuAtP1 : Array Nat := #[0,16,0,0,17,18,0,19,20,21,22,0,0,0,23,24,0,20,0,0,25,0,26,27,0,28,29,30,0,0,31,0,0,0,0,0,0,0,0,0,0,32,0,1,0,33,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def sixMenuAtP2 : Array Nat := #[0,0,0,0,0,0,34,35,36,0,0,0,37,38,39,40,0,0,0,41,0,42,43,0,0,0,0,0,44,0,0,1,28,0,1,0,0,0,0,0,45,46,2,47,0,45,0,48,0,49,50,2,51,9,52,49,0,53,54,0,1,55,56,0]
private def sixMenuAtP3 : Array Nat := #[0,0,57,2,2,2,2,2,2,2,0,0,58,0,0,58,0,0,0,0,0,0,0,0,59,60,13,0,0,0,0,28,28,61,62,63,0,28,0,64,65,36,28,66,38,67,68,69,70,71,72,73,74,0,11,0,0,75,36,0,0,76,0,0]
private def sixMenuAtP4 : Array Nat := #[0,0,77,31,1,0,0,0,0,0,0,0,78,0,31,79,80,0,0,0,81,0,0,0,0,82,0,0,83,2,2,84,41,0,85,0,0,0,0,0,0,0,0,86,0,0,41,82,0,0,0,87,0,0,0,0,0,0,0,0,0,0,0,88]
private def sixMenuAtP5 : Array Nat := #[89,90,91,2,2,92,2,2,2,2,2,2,0,0,0,0,0,0,58,93,93,94,0,0,0,95,0,0,96,96,97,0,0,96,10,36,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,31,0,0,0,0,0,7,0,98]
private def sixMenuAtP6 : Array Nat := #[0,0,0,0,0,99,78,37,28,0,100,28,37,101,102,0,0,103,0,104,0,0,103,105,106,0,107,108,85,0,105,106,109,110,0,111,112,0,0,113,52,114,115,2,0,0,111,18,116,112,0,6,117,28,118,0,119,0,120,121,122,123,0,119]
private def sixMenuAtP7 : Array Nat := #[124,124,0,0,0,2,0,0,0,0,0,0,0,0,58,58,0,0,0,0,0,0,0,0,0,0,0,0,125,126,0,126,127,0,128,129,0,0,0,0,0,0,0,53,28,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,130,0,131]
private def sixMenuAtP8 : Array Nat := #[0,0,0,7,27,11,132,133,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,28,130,28,134,0,28,0,28,0,0,0,28,0,28,0,0,0,0,135,136,0,0,0,54,0,1,55,137,0,0,0,0,2,0,0,0,0,0,0,0,0]
private def sixMenuAtP9 : Array Nat := #[0,0,0,0,0,138,13,139,140,0,0,0,0,0,0,0,0,0,0,141,20,142,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,13,20,0,0,13,0,0,20,143,0,0,0,0,0,0,0,0,0,144,0,13,13,13,20,0,0,13]
private def sixMenuAtP10 : Array Nat := #[0,145,0,28,28,0,36,0,146,0,27,147,28,28,0,0,0,148,149,0,150,148,0,0,0,0,36,0,31,0,31,0,151,147,0,152,28,0,0,0,2,153,0,0,0,0,0,0,0,0,36,138,0,0,0,0,37,154,38,0,4,0,93,155]
private def sixMenuAtP11 : Array Nat := #[31,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def sixMenuAtP12 : Array Nat := #[0,0,0,0,0,156,2,2,0,28,157,0,0,158,0,127,28,158,0,0,0,0,0,58,0,159,0,0,0,0,0,0,0,0,44,0,0,0,1,0,0,0,0,0,0,160,0,0,31,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0]
private def sixMenuAtP13 : Array Nat := #[0,20,0,0,0,0,0,0,0,0,93,0,161,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,93,0,0,0,0,0,0,0,0,0,0,0,0,0,59,0,162,163,0,0,0,0,13,0,0,0,0,0,0,0,0,0,0]
private def sixMenuAtP14 : Array Nat := #[0,0,151,31,31,0,0,164,0,147,0,0,0,0,165,166,167,168,169,0,170,170,171,0,0,172,173,174,0,28,0,0,175,176,0,0,177,28,36,36,0,0,0,0,0,0,0,0,0,0,28,38,28,28,0,0,0,0,0,178,179,47,178,0]
private def sixMenuAtP15 : Array Nat := #[48,180,181,182,180,0,164,183,184,185,186,187,0,0,0,0,20,188,184,189,186,190,187,191,192,47,0,20,20,193,0,0,194,0,183,0,48,184,185,186,187,0,0,0,0,20,20,195,196,197,198,0,0,0,0,0,0,126,199,200,0,201,202,203]
private def sixMenuAtP16 : Array Nat := #[204,0,126,28,28,0,28,0,28,205,0,28,0,0,206,207,208,0,209,127,210,211,212,213,214,215,216,31,217,0,0,218,219,220,36,36,1,221,222,223,31,224,77,38,225,226,227,0,0,228,229,230,231,232,233,234,235,0,151,236,237,238,239,240]
private def sixMenuAtP17 : Array Nat := #[241,242,0,0,243,244,245,246,247,248,9,249,250,251,0,0,252,0,0,0,253,0,243,0,254,0,255,256,0,0,253,257,253,258,244,0,259,260,261,235,0,31,251,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,262,263,264,265,266,267]
private def sixMenuAtP18 : Array Nat := #[268,269,270,271,263,272,273,274,266,275,276,0,277,0,1,278,279,0,0,0,0,0,0,0,0,280,91,268,0,281,282,263,0,0,0,283,284,36,285,0,0,0,0,0,286,0,287,288,289,0,0,0,273,0,290,266,0,291,292,153,0,293,1,0]
private def sixMenuAtP19 : Array Nat := #[0,0,294,261,295,0,296,297,298,153,0,299,0,0,300,5,301,144,302,2,303,0,301,144,304,305,306,307,308,309,310,311,312,307,308,309,59,2,2,313,2,0,0,314,315,59,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def sixMenuAtP20 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def sixMenuAtP21 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,316,0,0,0,0,0,316,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,317,126,28,318,28,319,320,0,0,0,1,0,0,0,0,0,0,0,0,0,152,0,0]
private def sixMenuAtP22 : Array Nat := #[0,0,0,0,0,0,0,264,0,0,316,316,0,0,0,0,0,0,0,0,0,31,0,0,0,0,0,0,0,0,0,0,0,147,0,151,31,0,0,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def sixMenuAtP23 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def sixMenuAt : Array (Array Nat) := #[sixMenuAtP0,sixMenuAtP1,sixMenuAtP2,sixMenuAtP3,sixMenuAtP4,sixMenuAtP5,sixMenuAtP6,sixMenuAtP7,sixMenuAtP8,sixMenuAtP9,sixMenuAtP10,sixMenuAtP11,sixMenuAtP12,sixMenuAtP13,sixMenuAtP14,sixMenuAtP15,sixMenuAtP16,sixMenuAtP17,sixMenuAtP18,sixMenuAtP19,sixMenuAtP20,sixMenuAtP21,sixMenuAtP22,sixMenuAtP23]
private def atSix (v : Array (Array Nat)) (i : Nat) : Nat := ((v[i/64]?).getD #[])[i%64]?.getD 0
private def sixOffset : Nat → Nat → Nat
  | 191, 6 => 0
  | 191, 7 => 1
  | 191, 8 => 43
  | 191, 9 => 465
  | 191, 10 => 1263
  | 191, 11 => 1449
  | 191, 12 => 1467
  | 255, 10 => 1468
  | 255, 11 => 1478
  | 255, 12 => 1509
  | 255, 13 => 1529
  | 255, 14 => 1535
  | _, _ => 1536
private def inlineMenu (m k i : Nat) : List Nat :=
  let off := sixOffset m k
  if off < 1536 then
    let mnum := atSix sixMenuAt (off+i)
    let offsetCode := atSix sixMenuStarts mnum
    (List.range (offsetCode % 16)).map (fun j => atSix sixWords (atSix sixMenuWords (offsetCode / 16 + j)))
  else []

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag query => ((g.index k tag).bind (linkedSet g (k-1))).toList ++ closeSix (targetOf g) (k-1) (inlineMenu g.mask k i) query
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov g.mode ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible g.mode (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag query xs hx
    rcases List.mem_append.mp hx with old | extra
    · have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using old
      obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
      exact linkedSet_sound g _ names (prior (by omega)) h
    · exact closeSix_sound extra g.mode



def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 152) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain ess).1 (essential_plain ess).2 _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (carries : List (Nat × List Nat)) :=
  carries.map (fun v => (v.1,L)) ++ old
theorem extend_ok {u old L m carries} (previous : Known u old)
    (main : Lower u (varsX m) (graphGoal m) L)
    (ok : carries.all (fun v => carryOK v.1 m v.2) = true) :
    Known u (extendKnown old L carries) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact carry_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known true [] := by simp [Known]
def lanePlace (v : Nat) (upper : Nat) := 2^153*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^153 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
def fullMarks (r packed : Nat) := ((packed+r) >>> 152) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (153*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^153)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 153*(i+1)-153=153*i := by omega
      have ge : ¬153*(i+1)<153 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 152 = (a==BitVec.allOnes 152) := by
  by_cases h : a=BitVec.allOnes 152
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^152-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^152 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (153*i) =
      (f xs[i]==BitVec.allOnes 152) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^153*u+x+(2^153*v+1)=2^153*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^153 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬153*(i+1)+152<153 := by omega
      have di : 153*(i+1)+152-153=153*i+152 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)


abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat

def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]

def packedOp (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=0 then (a.1 &&& b.1,a.2 &&& b.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else if op=2 then (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
  else (b.1 ^^^ (b.1 &&& a.1),b.2 ^^^ (b.2 &&& a.2))
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp op (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (dbin op (a x) (b x)).2) xs := by
  by_cases h0 : op=0
  · simp only [packedOp,h0,ite_true,packedSig,lanes_and,dbin,bv]
  by_cases h1 : op=1
  · simp [packedOp,h1,packedSig,lanes_or,dbin,bv]
  by_cases h2 : op=2
  · simp [packedOp,h2,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv]
  · have e (x y : Bits) : ~~~x &&& y = y &&& ~~~x := BitVec.and_comm _ _
    simp only [packedOp,h0,h1,h2,ite_false,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv,e]

def takePacked (c : PackedCov) (a b : Nat) (ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) ka kb) xs := by
  cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (dbin op a b) ka kb
def combField (c : NodeContext) (d ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov c.2.2.2.1.1 (column d a.2) (column d b.2) ka kb |||
    column d (dbin op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 153) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (153*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 153) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

theorem masked_comp (d x : Sig) : masked d (neg x) = d ^^^ masked d x := by
  apply bit_ext
  intro r
  simp only [masked,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl
def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b kb ≤
    (delTwo ws a b ka kb).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  simp only [delTwo]
  omega

noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem force_eq {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl
noncomputable def forceMap {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => force (f a) fun x => ih fun xs => k (x::xs)) l
theorem forceMap_eq {α β : Type} (f : α → Nat) (l : List α) (k : List Nat → β) : forceMap f l k = k (l.map f) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    change force (f a) (fun x => forceMap f l fun xs => k (x::xs)) = _
    rw [force_eq,ih]
    rfl
def nmask (d : Nat) (a : Sig) : Nat := Nat.land a.toNat d
noncomputable def anyEq (m : Nat) (l : List Nat) : Bool := List.rec false (fun v _ ih => or (Nat.beq m v) ih) l
def nconst (d m : Nat) : Bool := or (Nat.beq m 0) (Nat.beq m d)
noncomputable def navail (u : Bool) (d : Nat) (pm : List Nat) (m : Nat) : Bool :=
  or (or (nconst d m) (anyEq m pm)) (and u (anyEq (Nat.xor d m) pm))
theorem nmask_eq (d a : Sig) : nmask d.toNat a = (masked d a).toNat := (BitVec.toNat_and _ _).symm
theorem beq_toNat (a b : Sig) : Nat.beq a.toNat b.toNat = (a==b) := by
  rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]
  exact BitVec.toNat_inj
theorem nconst_eq (d a : Sig) : nconst d.toNat (nmask d.toNat a) = isMaskedConstant d a := by
  rw [nmask_eq]
  have e : Nat.beq (masked d a).toNat 0 = (masked d a == zero) := by
    have z0 : zero.toNat=0 := by simp [zero]
    rw [←beq_toNat,z0]
  rw [nconst,e,beq_toNat]
  rfl
theorem anyEq_eq (x d : Sig) (pool : List Sig) : anyEq x.toNat (pool.map (nmask d.toNat)) = (pool.map (masked d)).any (fun v => v==x) := by
  induction pool with
  | nil => rfl
  | cons a l ih =>
    change or (Nat.beq x.toNat (nmask d.toNat a)) (anyEq x.toNat (l.map (nmask d.toNat))) = _
    rw [ih,nmask_eq,beq_toNat,List.map_cons,List.any_cons,Bool.beq_comm]
theorem navail_eq (u : Bool) (d a : Sig) (pool : List Sig) :
    navail u d.toNat (pool.map (nmask d.toNat)) (nmask d.toNat a) = availableB u d pool a := by
  have x : Nat.xor d.toNat (masked d a).toNat = (masked d (neg a)).toNat := by
    rw [masked_comp]
    exact (BitVec.toNat_xor _ _).symm
  rw [navail,nconst_eq,nmask_eq,x,anyEq_eq,anyEq_eq]
  simp only [availableB,isMaskedConstant]
def unav (u : Bool) (p : BoundPool) (w : Decor) : Nat := cond (availableB u p.domain p.wires w.1) 0 1
def slowCost (u : Bool) (p : BoundPool) (ws : List Decor) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) : Bool :=
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let cm := ws.countP const - constantLoss const a ka - constantLoss const b kb + (isMaskedConstant p.domain z).toNat
  (((ws.map (unav u p)).sum == cond ka 0 (unav u p a) + cond kb 0 (unav u p b)) &&
    decide (k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+cm)) &&
    (availableB u p.domain p.wires z || (availableB u p.domain p.wires a.1 && availableB u p.domain p.wires b.1))
def zN (op x y : Nat) : Nat := cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
  (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))
theorem zN_eq (op : Nat) (d a b : Sig) : zN op (nmask d.toNat a) (nmask d.toNat b) = nmask d.toNat (bin op a b) := by
  have tn (x y : Sig) : Nat.land x.toNat y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm
  have tx (x y : Sig) : Nat.xor x.toNat y.toNat = (x ^^^ y).toNat := (BitVec.toNat_xor x y).symm
  have tor (x y : Sig) : Nat.lor x.toNat y.toNat = (x ||| y).toNat := (BitVec.toNat_or x y).symm
  simp only [nmask_eq]
  unfold zN
  by_cases h0 : op=0
  · subst h0
    change Nat.land _ _ = _
    rw [tn]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,ite_true,BitVec.getLsbD_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  by_cases h1 : op=1
  · subst h1
    change Nat.lor _ _ = _
    rw [tor]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,Nat.one_ne_zero,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e0 : Nat.beq op 0=false := Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  have e1 : Nat.beq op 1=false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2 : op=2
  · subst h2
    change Nat.xor _ (Nat.land _ _) = _
    rw [tn,tx]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e2 : Nat.beq op 2=false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  rw [e0,e1,e2]
  change Nat.xor _ (Nat.land _ _) = _
  rw [tn,tx]
  congr 1
  apply bit_ext
  intro r
  simp only [masked,bin,bit,h0,h1,h2,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
  cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
def nloss (d x : Nat) (keep : Bool) : Nat := cond keep 0 (cond (nconst d x) 1 0)
theorem nloss_eq (d : Sig) (a : Decor) (keep : Bool) :
    nloss d.toNat (nmask d.toNat a.1) keep = constantLoss (fun w : Decor => isMaskedConstant d w.1) a keep := by
  rw [nloss,nconst_eq,constantLoss]
  cases keep
  · cases isMaskedConstant d a.1 <;> rfl
  · rfl
abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × Bool
noncomputable def quickSpec (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) : QS :=
  let d := p.domain.toNat
  let ms := ws.map (fun w : Decor => nmask d w.1)
  (d,ms.countP (nconst d),p.bound,Nat.add k p.paid,(ms.map fun m => cond (navail u d (p.wires.map (nmask d)) m) 0 1).sum,ms,p.wires.map (nmask d),u)
noncomputable def forceBool {β : Type} (b : Bool) (f : Bool → β) : β := Bool.rec (f false) (f true) b
noncomputable def forcePool {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) (f : QS → β) : β :=
  force p.domain.toNat fun d => forceMap (nmask d) p.wires fun pm => forceMap (fun w : Decor => nmask d w.1) ws fun ms =>
  force (ms.countP (nconst d)) fun c => force p.bound fun l => force (Nat.add k p.paid) fun t =>
  force (ms.map fun m => cond (navail u d pm m) 0 1).sum fun v => forceBool u fun u => f (d,c,l,t,v,ms,pm,u)
theorem forcePool_eq {β : Type} (u k ws p) (f : QS → β) : forcePool u k ws p f = f (quickSpec u k ws p) := by
  have e (b : Bool) (f : Bool → β) : forceBool b f = f b := by cases b <;> rfl
  simp only [forcePool,force_eq,forceMap_eq,e]
  rfl
noncomputable def forcePools {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (ps : List BoundPool) : (List QS → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f => forcePool u k ws p fun q => ih fun qs => f (q::qs)) ps
theorem forcePools_eq {β : Type} (u k ws ps) (f : List QS → β) : forcePools u k ws ps f = f (ps.map (quickSpec u k ws)) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change forcePool u k ws p (fun q => forcePools u k ws ps fun qs => f (q::qs)) = _
    rw [forcePool_eq,ih]
    rfl
def kwN (v : Nat) : Nat :=
  let n := v % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
abbrev Lane := NodeContext × Nat × Nat × List QS × List Nat × Nat
noncomputable def laneOf (c : NodeContext) : Lane :=
  let ws := c.2.2.1.map (fun w : Decor => w.1.toNat)
  (c,c.2.2.1.length,cond c.2.2.2.1.2 4 2,c.2.2.2.2.1.map (quickSpec c.2.2.2.1.2 (c.1-1) c.2.2.1),ws,(ws.map kwN).sum)
noncomputable def forceLanes {β : Type} (cs : List NodeContext) : (List Lane → β) → β :=
  List.rec (fun f => f []) (fun c _ ih f => force c.2.2.1.length fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
    forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
    forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => ih fun ys => f ((c,n,l,qs,ws,t)::ys)) cs
theorem forceLanes_eq {β : Type} (cs) (f : List Lane → β) : forceLanes cs f = f (cs.map laneOf) := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
    change force c.2.2.1.length (fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
      forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
      forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => forceLanes cs fun ys => f ((c,n,l,qs,ws,t)::ys)) = _
    rw [force_eq,force_eq,forceMap_eq,force_eq,forcePools_eq,ih]
    rfl
noncomputable def fastCost (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (s.2.2.2.2.2.1.getD i 0) fun x => force (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (nloss s.1 x ka)) (nloss s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (force (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (nconst s.1 (zN op x y)) false))
theorem spec_get {d : Nat} (ws : List Decor) (i : Nat) (hd : nmask d zero=0) :
    (ws.map (fun w : Decor => nmask d w.1)).getD i 0 = nmask d (ws.getD i defaultDecor).1 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none => exact hd.symm
  | some v => rfl
theorem fast_slow {u k p ws i j op ka kb} (h : fastCost (quickSpec u k ws p) i j op ka kb=true) :
    slowCost u p ws k (ws.getD i defaultDecor) (ws.getD j defaultDecor) op ka kb=true := by
  have z0 : nmask p.domain.toNat zero=0 := by
    have : zero.toNat=0 := by simp [zero]
    simp [nmask,this]
  have su : (((ws.map (fun w : Decor => nmask p.domain.toNat w.1)).map fun m => cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) m) 0 1).sum) =
      (ws.map (unav u p)).sum := by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro w _
    change cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) (nmask p.domain.toNat w.1)) 0 1 = _
    rw [navail_eq]
    rfl
  simp only [fastCost,quickSpec,force_eq,spec_get _ _ z0,su,List.countP_map,Function.comp_def,nconst_eq] at h
  generalize ws.getD i defaultDecor=a at h ⊢
  generalize ws.getD j defaultDecor=b at h ⊢
  replace h : and (Nat.beq (ws.map (unav u p)).sum (Nat.add (cond ka 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) 0 1)) (cond kb 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)) 0 1))))
   (cond (Nat.ble (Nat.succ (Nat.add k p.paid)) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb))))
    (or ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) (and (Nat.ble (Nat.add (Nat.add k p.paid) 2) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (and ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)))))
    (cond (Nat.ble (Nat.add k p.paid) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (nconst p.domain.toNat (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) false)) = true := h
  rw [zN_eq,nconst_eq,navail_eq,navail_eq,navail_eq,nloss_eq,nloss_eq] at h
  have ca : isMaskedConstant p.domain (bin op a.1 b.1)=true → availableB u p.domain p.wires (bin op a.1 b.1)=true := by
    intro zc
    simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
    exact Or.inl (Or.inl zc)
  simp only [Nat.add_eq,Nat.sub_eq,Nat.succ_eq_add_one,Bool.and_eq_true,Nat.beq_eq] at h
  obtain ⟨hu,h⟩ := h
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
  refine ⟨⟨hu,?_⟩,?_⟩
  all_goals
    generalize ws.countP (fun w => isMaskedConstant p.domain w.1) - constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) a ka -
      constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) b kb = c at h ⊢
    generalize isMaskedConstant p.domain (bin op a.1 b.1)=r at h ca ⊢
    generalize availableB u p.domain p.wires (bin op a.1 b.1)=q at h ca ⊢
    cases h1 : Nat.ble (k+p.paid+1) (p.bound+c)
    · rw [h1] at h
      cases h2 : Nat.ble (k+p.paid) (p.bound+c)
      · simp [h2] at h
      · have := Nat.ble_eq.mp h2
        simp only [h2,cond_true,cond_false] at h
        subst h
        rw [ca rfl]
        simp <;> omega
    · rw [h1] at h
      have l1 := Nat.ble_eq.mp h1
      simp only [cond_true,Bool.or_eq_true,Bool.and_eq_true,Nat.ble_eq] at h
      rcases h with rfl | ⟨l2,ha,hb⟩
      · simp <;> omega
      · first
        | (have : (!q).toNat ≤ 1 := Bool.toNat_le _
           omega)
        | simp [ha,hb]

theorem anyEq_iff (m : Nat) (l : List Nat) : anyEq m l=true ↔ m ∈ l := by
  induction l with
  | nil => simp [anyEq]
  | cons a l ih =>
    change or (Nat.beq m a) (anyEq m l)=true ↔ _
    rw [Bool.or_eq_true,ih,Nat.beq_eq,List.mem_cons]
noncomputable def linkAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (l.2.2.2.2.1.getD i 0) fun x => force (l.2.2.2.2.1.getD j 0) fun y => force (zN op x y) fun z =>
  Option.rec false (fun ys => forceMap (fun v => v) ys fun ys =>
    and (anyEq z ys) (and (l.2.2.2.2.1.all fun v => or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (anyEq v ys)))
      (ys.all fun v => or (Nat.beq v z) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (anyEq v l.2.2.2.2.1)))))
    (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2.2 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))
theorem keySet_sum (xs : List Sig) : keySet xs = (xs.map keyWord).sum := by
  have go (a : Nat) : xs.foldl (fun v x => v+keyWord x) a = a+(xs.map keyWord).sum := by
    induction xs generalizing a with
    | nil => rfl
    | cons x xs ih => rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,Nat.add_assoc]
  exact (go 0).trans (Nat.zero_add _)
theorem delTwo_sum (f : Decor → Nat) {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map f).sum = (ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)) := by
  have er {l : List Decor} {x : Decor} (hx : x ∈ l) : (l.map f).sum = f x + ((l.erase x).map f).sum := by
    have := ((List.perm_cons_erase hx).map f).sum_eq
    rwa [List.map_cons,List.sum_cons] at this
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e1 := er ha
  have e2 := er hb
  have e3 := er hm
  cases ka <;> cases kb <;> simp only [delTwo,delOne,Bool.false_eq_true,ite_true,ite_false,cond_true,cond_false] <;> omega
theorem fastCost_good {u p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws) (ne : a≠b) (al : allowedB u op=true)
    (h : slowCost u p ws k a b op ka kb=true) :
    scalarPoolCut u p k ((delTwo ws a b ka kb).map Prod.fst) (movedChoice op a b)=true := by
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let rest := delTwo ws a b ka kb
  have ck := keptCount const ws a b ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b kb ≤ rest.countP const at ck
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  obtain ⟨⟨hu,hc⟩,hz⟩ := h
  have sum := delTwo_sum (unav u p) ha hb ne ka kb
  rw [hu] at sum
  have zs : ((delTwo ws a b ka kb).map (unav u p)).sum=0 := by omega
  have hs : (rest.map Prod.fst).all (availableB u p.domain p.wires)=true := by
    apply List.all_eq_true.mpr
    intro _ hm
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    have v := List.sum_eq_zero_iff.mp zs _ (List.mem_map_of_mem hw)
    cases e : availableB u p.domain p.wires w.1
    · simp [unav,e] at v
    · rfl
  have opOK : (!(!availableB u p.domain p.wires z) || choiceOK u p.domain p.wires (movedChoice op a b))=true := by
    simp only [Bool.or_eq_true,Bool.and_eq_true] at hz
    rcases hz with hz | ⟨x,y⟩
    · simp [z,hz]
    · simp [choiceOK,movedChoice,x,y,al]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b kb+(isMaskedConstant p.domain z).toNat) at hc
  dsimp only [rest] at hs
  have ez : choiceVal (movedChoice op a b)=z := rfl
  simp only [scalarPoolCut,ez,hs,opOK,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
  cases hc' : isMaskedConstant p.domain z <;> simp [hc'] at hc ⊢ <;> omega

theorem zN_full (op : Nat) (a b : Sig) : zN op a.toNat b.toNat = (bin op a b).toNat := by
  have e (v : Sig) : nmask one.toNat v = v.toNat := by
    rw [nmask_eq]
    congr 1
    exact BitVec.and_allOnes
  have := zN_eq op one a b
  rwa [e,e,e] at this
theorem getW (ws : List Decor) (i : Nat) :
    (ws.map (fun w : Decor => w.1.toNat)).getD i 0 = (ws.getD i defaultDecor).1.toNat := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none =>
    have z0 : zero.toNat=0 := by simp [zero]
    exact z0.symm
  | some v => rfl
theorem wire_ne {c : NodeContext} {i j} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) : (contextWire c i).1 ≠ (contextWire c j).1 := by
  have gi : contextWire c i = c.2.2.1[i] := by simp [contextWire,List.getD_eq_getElem?_getD,hi]
  have gj : contextWire c j = c.2.2.1[j] := by simp [contextWire,List.getD_eq_getElem?_getD,hj]
  rw [gi,gj]
  intro e
  apply hij
  apply (List.Nodup.getElem_inj_iff nd (hi:=by simpa using hi) (hj:=by simpa using hj)).mp
  simpa using e
theorem link_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∀ query, ∃ xs ∈ c.2.2.2.2.2 tag query, ys=xs.map BitVec.toNat)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) (h : linkAt fl (laneOf c) i j op ka kb=true) :
    (c.2.2.2.2.2 (keySet (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst)) (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst)).any (sameWords
      (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  have hne := wire_ne nd hi hj hij
  have ha := mem i hi
  have hb := mem j hj
  have hab : contextWire c i ≠ contextWire c j := fun e => hne (congrArg Prod.fst e)
  have kv (v : Sig) := kept_value nd ha hb ka kb v
  have sum := delTwo_sum (fun w : Decor => keyWord w.1) ha hb hab ka kb
  have wi : contextWire c i = c.2.2.1.getD i defaultDecor := rfl
  have wj : contextWire c j = c.2.2.1.getD j defaultDecor := rfl
  simp only [linkAt,laneOf,force_eq,getW,←wi,←wj,zN_full] at h
  generalize contextWire c i=a at *
  generalize contextWire c j=b at *
  change Option.rec false _ (fl (keyWord (bin op a.1 b.1)+(((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum -
    (cond ka 0 (keyWord a.1)) - (cond kb 0 (keyWord b.1)))))=true at h
  have tot : ((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum = (c.2.2.1.map (fun w : Decor => keyWord w.1)).sum := by
    rw [List.map_map]
    rfl
  rw [tot,←sum] at h
  have tag : keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst) =
      keyWord (bin op a.1 b.1)+((delTwo c.2.2.1 a b ka kb).map (fun w : Decor => keyWord w.1)).sum := by
    rw [keySet_sum,List.map_cons,List.sum_cons,List.map_map]
    rfl
  rw [←tag] at h
  generalize keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst)=t at h ⊢
  cases hf : fl t with
  | none => simp [hf] at h
  | some ys =>
    obtain ⟨xs,hx,rfl⟩ := hfl t ys hf (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst)
    rw [hf] at h
    simp only [forceMap_eq,List.map_id',Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,anyEq_iff,Nat.beq_eq,Bool.not_eq_true'] at h
    obtain ⟨h1,h2,h3⟩ := h
    have back {v : Sig} (hv : v.toNat ∈ xs.map BitVec.toNat) : v ∈ xs := by
      obtain ⟨w,hw,e⟩ := List.mem_map.mp hv
      exact BitVec.toNat_inj.mp e ▸ hw
    apply List.any_eq_true.mpr
    refine ⟨xs,hx,?_⟩
    simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
    constructor
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact back h1
      · obtain ⟨hw,va,vb⟩ := (kv v).mp hv
        obtain ⟨w,hm,rfl⟩ := List.mem_map.mp hw
        rcases h2 _ (List.mem_map_of_mem hm) with ⟨x,y⟩ | ⟨x,y⟩ | x
        · rcases va with va | va
          · exact absurd (BitVec.toNat_inj.mp y) va
          · simp [va] at x
        · rcases vb with vb | vb
          · exact absurd (BitVec.toNat_inj.mp y) vb
          · simp [vb] at x
        · exact back x
    · intro v hv
      rcases h3 _ (List.mem_map_of_mem hv) with x | ⟨⟨x,y⟩,m⟩
      · exact List.mem_cons.mpr (Or.inl (BitVec.toNat_inj.mp x))
      · refine List.mem_cons_of_mem _ ((kv v).mpr ⟨?_,?_,?_⟩)
        · obtain ⟨w,hw,e⟩ := List.mem_map.mp m
          exact BitVec.toNat_inj.mp e ▸ List.mem_map_of_mem hw
        · rcases x with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
        · rcases y with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
noncomputable def fallbackAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  or (and (and (Nat.ble (Nat.succ i) l.2.1) (and (Nat.ble (Nat.succ j) l.2.1) (and (Nat.ble (Nat.succ op) l.2.2.1) (not (Nat.beq i j)))))
    (or (l.2.2.2.1.any fun s => fastCost s i j op ka kb) (linkAt fl l i j op ka kb))) (checkAt l.1 i j op ka kb)
theorem fallback_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∀ query, ∃ xs ∈ c.2.2.2.2.2 tag query, ys=xs.map BitVec.toNat)
    (h : fallbackAt fl (laneOf c) i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with ⟨⟨hi,hj,ho,hn⟩,h | h⟩ | h
  · have hi := Nat.ble_eq.mp hi
    have hj := Nat.ble_eq.mp hj
    have ho := Nat.ble_eq.mp ho
    change Nat.succ i ≤ c.2.2.1.length at hi
    change Nat.succ j ≤ c.2.2.1.length at hj
    change Nat.succ op ≤ cond c.2.2.2.1.2 4 2 at ho
    have al : allowedB c.2.2.2.1.2 op=true := by
      cases hu : c.2.2.2.1.2 <;> simp [hu] at ho <;> simp [allowedB] <;> omega
    have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
      simp [contextWire,List.getD_eq_getElem?_getD,ht]
    obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    have hne := wire_ne nd hi hj (fun e => by simp [e] at hn)
    have closed := fastCost_good (mem i hi) (mem j hj) (fun e => hne (congrArg Prod.fst e)) al (fast_slow ok)
    have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut c.2.2.2.1.2 p (c.1-1)
        ((delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst)
        (movedChoice op (contextWire c i) (contextWire c j)))=true :=
      List.any_eq_true.mpr ⟨p,hp,closed⟩
    simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
    repeat' split
    all_goals rfl
  · have cut := link_sound nd hfl (Nat.ble_eq.mp hi) (Nat.ble_eq.mp hj) (fun e => by simp [e] at hn) h
    simp only [checkAt,evalMove,closeChild,cut,Bool.true_or]
    repeat' split
    all_goals rfl
  · exact h
def swapIdx (v t : Nat) : Nat := cond (Nat.beq t (v &&& 15)) (v >>> 4) (cond (Nat.beq t (v >>> 4)) (v &&& 15) t)
def validSwap (v : Nat) : Bool := and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 9)
set_option maxRecDepth 8192 in
theorem swap_table : ∀ v : Fin 144, validSwap v.val=true → ∀ t : Fin 9, swapIdx v.val t.val<9 ∧
    wordMove (swapRows v.val) (inputs.getD t.val zero) = inputs.getD (swapIdx v.val t.val) zero := by decide +kernel
theorem swap_input {v t : Nat} (hv : validSwap v=true) (ht : t<9) : swapIdx v t<9 ∧
    wordMove (swapRows v) (inputs.getD t zero) = inputs.getD (swapIdx v t) zero := by
  have lt : v<144 := by
    simp only [validSwap,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv
    omega
  exact swap_table ⟨v,lt⟩ hv ⟨t,ht⟩
def idxOf (perm : List Nat) (t : Nat) : Nat := perm.foldl (fun t v => swapIdx v t) t
theorem idx_move {perm : List Nat} (ok : perm.all validSwap=true) {t : Nat} (ht : t<9) :
    movedWord (perm.map swapRows).reverse (inputs.getD t zero) = inputs.getD (idxOf perm t) zero := by
  rw [movedWord,List.foldr_reverse,List.foldl_map]
  induction perm generalizing t with
  | nil => rfl
  | cons v perm ih =>
    simp only [List.all_cons,Bool.and_eq_true] at ok
    obtain ⟨lt,e⟩ := swap_input ok.1 ht
    rw [List.foldl_cons,e,ih ok.2 lt]
    rfl
noncomputable def decodeN : Nat → Nat → List Nat → List Nat
  | 0,_,ws => ws
  | n+1,bits,ws => force (zN ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) 0) (ws.getD ((bits >>> 4) &&& 15) 0))
      fun z => decodeN n (bits >>> 10) (ws++[z])
theorem decodeN_eq (F : Sig → Nat) (F0 : F zero=0) (Fb : ∀ op a b, F (bin op a b)=zN op (F a) (F b))
    (n bits : Nat) (ds : List Decor) :
    (decodeBank n bits ds).map (fun w => F w.1) = decodeN n bits (ds.map fun w => F w.1) := by
  have gd (ds : List Decor) (i : Nat) : (ds.map fun w => F w.1).getD i 0 = F (ds.getD i defaultDecor).1 := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases ds[i]? with
    | none => exact F0.symm
    | some v => rfl
  induction n generalizing bits ds with
  | zero => rfl
  | succ n ih =>
    rw [decodeN,force_eq,decodeBank,ih,gd,gd,←Fb,List.map_append]
    rfl
theorem selectLive_map {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    (selectLive bits ws).map f = selectLive bits (ws.map f) := by
  induction ws generalizing bits with
  | nil => rfl
  | cons w ws ih =>
    rw [List.map_cons,selectLive,selectLive]
    split
    · rw [List.map_cons,ih]
    · exact ih _
noncomputable def fastState (g : Forest) (k i : Nat) (perm : List Nat) : List Nat :=
  let raw := (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*depth
  force (forestRecord (g.levels k) (selected g.mask).length i) fun rec =>
  selectLive (rec >>> len) (decodeN depth (rec &&& ((1 <<< len)-1)) raw)
theorem fastState_eq (g : Forest) (k i : Nat) {perm : List Nat} (ok : perm.all validSwap=true) :
    fastState g k i perm = ((stateSet g k i).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat := by
  let ms := (perm.map swapRows).reverse
  let F (a : Sig) : Nat := (movedWord ms a).toNat
  have F0 : F zero=0 := by
    change (movedWord ms zero).toNat=0
    rw [moved_eq_rename,(rename_constants _).1]
    simp [zero]
  have Fb (op a b) : F (bin op a b)=zN op (F a) (F b) := by
    change (movedWord ms (bin op a b)).toNat = zN op (movedWord ms a).toNat (movedWord ms b).toNat
    rw [zN_full,moved_eq_rename,rename_bin,moved_eq_rename,moved_eq_rename]
  have raw : (wiresOf g).map (fun w => F w.1) = (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat := by
    simp only [wiresOf,rawDecor,List.map_map]
    apply List.map_congr_left
    rintro ⟨j,a⟩ hm
    obtain ⟨hj,rfl⟩ := selected_entry hm
    exact congrArg BitVec.toNat (idx_move ok hj)
  have len : (wiresOf g).length = (selected g.mask).length := by simp [wiresOf,rawDecor]
  unfold fastState stateSet readNode
  rcases g.levels k with ⟨a,depth,b,c,d,e,f,data⟩
  simp only [force_eq,storedDepth,len]
  rw [List.map_map,List.map_map,selectLive_map,←raw,←decodeN_eq F F0 Fb]
  rfl
noncomputable def linkedFast (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Nat) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).bind fun perm => cond (perm.all validSwap) (some (fastState g k pair.1 perm)) none
noncomputable def flOf (g : Forest) (k : Nat) : Nat → Option (List Nat) := fun tag => (g.index k tag).bind (linkedFast g (k-1))
noncomputable def batchMove (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp op a b'
    let mask := fullMarks r (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b') ka kb ||| packedColumn (!u) z)
    onMarks (fun c => fallbackAt fl c i j op ka kb) mask xs

theorem batchMove_at {fl u} (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∀ query, ∃ zs ∈ xs[q].2.2.2.2.2 tag query, ys=zs.map BitVec.toNat)
    (pass : batchMove fl u (makeBatch k n xs) (xs.map laneOf) i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 152 then true
      else if !properB (dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((delTwo xs[q].2.2.1 (contextWire xs[q] i) (contextWire xs[q] j) ka kb).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,mode,len,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b) ka kb |||
        packedColumn (!u) (packedOp op a b))) (xs.map laneOf)) = true at pass
    rw [if_neg small] at pass
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 152
    · apply fallback_sound nd hfl
      have m := marked_ok _ _ _ q (by simpa using hq) (by
        rw [mark_at _ _ _ hq]
        exact beq_iff_eq.mpr hit) pass
      simpa only [List.getElem_map] using m
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]


noncomputable def batchPair (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) :=
  let f := batchMove fl u b xs i j op
  f false false && f true false && f false true && f true true
noncomputable def batchRow (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i : Nat) (js : List Nat) :=
    js.all (fun j => (opsOf u).all (batchPair fl u b xs i j))
noncomputable def batchRows (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) : List Nat → Bool
  | [] => true
  | i::js => batchRow fl u b xs i js && batchRows fl u b xs js

theorem batchRows_at {fl u} (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∀ query, ∃ zs ∈ xs[q].2.2.2.2.2 tag query, ys=zs.map BitVec.toNat)
    (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows fl u (makeBatch k n xs) (xs.map laneOf) js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    refine ⟨?_,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩ op hop
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    rw [mode] at hop
    have pass := allRows.1 j hj op hop
    have check := @batchMove_at fl u k n xs i j op
    simp only [batchPair,Bool.and_eq_true] at pass
    simp only [testPair,Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode nd hfl pass.1.1.1,check hi hj' hq budget arity mode nd hfl pass.1.1.2⟩,
      check hi hj' hq budget arity mode nd hfl pass.1.2⟩,check hi hj' hq budget arity mode nd hfl pass.2⟩

noncomputable def runBatch (fl : Nat → Option (List Nat)) (u : Bool) (k n : Nat) (xs : List NodeContext) :=
    batchRows fl u (makeBatch k n xs) (xs.map laneOf) (List.range n)
theorem runBatch_at {fl u k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hm : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∀ query, ∃ zs ∈ xs[q].2.2.2.2.2 tag query, ys=zs.map BitVec.toNat)
    (hn : xs[q].2.2.1.length=n)
    (pass : runBatch fl u k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha hm nd hfl (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag query => ((g.index k tag).bind (linkedSet g (k-1))).toList ++ closeSix (targetOf g) (k-1) (inlineMenu g.mask k i) query
  (k,ws.length,ws,preCov g.mode ws,rules,ls)


theorem flOf_ok (g : Forest) (k i tag : Nat) (ys) (h : flOf g k tag=some ys) (query : List Sig) :
    ∃ xs ∈ (contextOf g k i).2.2.2.2.2 tag query, ys=xs.map BitVec.toNat := by
  suffices old : ∃ xs ∈ ((g.index k tag).bind (linkedSet g (k-1))).toList, ys=xs.map BitVec.toNat by
    obtain ⟨xs,mem,eq⟩ := old
    exact ⟨xs,List.mem_append_left _ mem,eq⟩
  unfold flOf at h
  cases hp : g.index k tag with
  | none => simp [hp] at h
  | some pair =>
    simp only [hp,Option.bind_some,linkedFast] at h
    simp only [Option.bind_some,linkedSet]
    split at h
    · contradiction
    next v =>
      cases ha : g.autos[pair.2]? with
      | none => simp [ha] at h
      | some perm =>
        simp only [ha,Option.bind_some] at h
        cases hv : perm.all validSwap with
        | false => simp [hv] at h
        | true =>
          simp only [hv,cond_true,Option.some.injEq] at h
          refine ⟨(stateSet g (k-1) pair.1).map (movedWord (perm.map swapRows).reverse),?_,?_⟩
          · simp [v]
          · exact h.symm.trans (fastState_eq g _ _ hv)

def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl

theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
noncomputable def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  forceLanes xs fun ys => (List.range len).all (fun d =>
    let i := lo+d
    batchRow (flOf g k) g.mode b ys i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (flOf g k) g.mode (makeBatch k ar (contexts g k start n)) ((contexts g k start n).map laneOf)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  simp only [rowCut,forceLanes_eq] at h
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  simp only [rowCut,forceLanes_eq]
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch (flOf g k) g.mode k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (flOf g k) g.mode (makeBatch k ar xs) (xs.map laneOf) (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have nd : (xs[q].2.2.1.map Prod.fst).Nodup := by
    have p := one.2
    simp only [prelim,Bool.and_eq_true,decide_eq_true_eq] at p
    rw [e]
    exact p.1
  have hfl : ∀ tag ys, flOf g k tag=some ys → ∀ query, ∃ zs ∈ xs[q].2.2.2.2.2 tag query, ys=zs.map BitVec.toNat := by
    rw [e]
    exact fun tag ys h => flOf_ok g k i tag ys h
  have hm : xs[q].2.2.2.1.2=g.mode := by rw [e]; rfl
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hm nd hfl hn (cutsRun h)

def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[0,7]⟩,⟨.or,[0,4]⟩,⟨.or,[2,4]⟩,⟨.or,[1,5]⟩,⟨.or,[5,6]⟩,⟨.or,[1,8]⟩,⟨.or,[2,7]⟩,⟨.or,[3,7]⟩,⟨.or,[6,8]⟩,⟨.and,[15,11]⟩,⟨.and,[13,12]⟩,⟨.and,[14,9]⟩,⟨.and,[16,10]⟩,⟨.or,[17,18]⟩,⟨.or,[21,19]⟩,⟨.or,[22,20]⟩], 23⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : smallCircuit.gates.length = 16 := rfl

theorem noNotReuse {gates : List Gate} (fit : ∀ g ∈ gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (h : ∀ g ∈ gates, g.op ≠ GateOp.not) :
    ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨ops,arity⟩ := fit g hg
  refine ⟨?_,arity⟩
  rcases ops with a | b | c
  · exact Or.inl a
  · exact Or.inr b
  · exact (h g hg c).elim


def sevenInputs : List Sig := vars 255
def sampleSeven (r : Row) (i : Fin 8) : Bool := bit r (sevenInputs.getD i.val zero)
theorem sevenList : List.ofFn (fun i : Fin 8 => sevenInputs.getD i.val zero) = sevenInputs := rfl
theorem sevenSampled (r : Row) : List.ofFn (sampleSeven r) = sevenInputs.map (bit r) := by
  rw [←sevenList,List.map_ofFn]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem sevenTable : ∀ r : Row, bit r graph = target (sampleSeven r) := by decide +kernel

theorem sevenEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates sevenInputs).getD i zero) =
      (C.wires (List.ofFn (sampleSeven r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sevenSampled]
  rfl

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([2, 3, 0, 1, 0, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([2, 3, 0, 1, 0, 0, 0, 0] : List Nat).getD i.val 0))

set_option maxHeartbeats 1000000 in
theorem allSevenRequired :
    (∀ i : Fin 8, bit (lowRow i) graph ≠ bit (highRow i) graph) ∧
    (∀ i j : Fin 8, i ≠ j →
      bit (lowRow i) (sevenInputs.getD j.val zero) =
      bit (highRow i) (sevenInputs.getD j.val zero)) := by decide +kernel

theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k sevenInputs.toFinset := by
  have goalEq : (execute C.gates sevenInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (sevenEval C legal C.output r).trans ((computes (sampleSeven r)).trans (sevenTable r).symm)
  have out := get_rep (u:=true) (execute C.gates sevenInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates sevenInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : sevenInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ sevenInputs) : ∃ i : Fin 8, sevenInputs.getD i.val zero = a := by
    rw [←sevenList] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = sevenInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run sevenInputs (sevenInputs.getD i.val zero) sub (lowRow i) (highRow i)
        (allSevenRequired.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply allSevenRequired.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k,hk,eq ▸ run⟩

theorem replaceShort 
    (lower : Impossible true graph 14 sevenInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 8 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 8 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 16 ≤ gates.length
  · exact ⟨smallCircuit.gates,smallCircuit.output,witnessMonotone,witnessSize.symm ▸ big,witnessCorrect⟩
  by_cases mono : ∀ g ∈ gates, g.op ≠ GateOp.not
  · exact ⟨gates,o,noNotReuse fit mono,Nat.le_refl _,correct⟩
  push Not at mono
  obtain ⟨g,hg,hop⟩ := mono
  have lt : gates.countP (fun q => !isNot q) < gates.length := by
    rcases Nat.lt_or_ge (gates.countP (fun q => !isNot q)) gates.length with h | h
    · exact h
    · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
      simp [isNot,hop] at eq
  have legal : PEqualNP.MetaComplexity.FanInTwo (Circuit.mk gates o) := by
    intro g hg
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using fit g hg
  obtain ⟨k,hk,run⟩ := physicalSigned (Circuit.mk gates o) legal correct
  change k ≤ gates.countP (fun q => !isNot q) at hk
  exact (lower k (by omega) run).elim
def g21Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ff63ff63ff63ff63f,0xf63ff63ff63ff63ff63f])),(BitVec.ofNat 152 (word80 [0x492049204920492049,0x20492049204920492049]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc7fbc7fbc7fbc7fbc7,0xfbc7fbc7fbc7fbc7fbc7])),(BitVec.ofNat 152 (word80 [0x924092409240924092,0x40924092409240924092]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf8fdf8fdf8fdf8fdf8,0xfdf8fdf8fdf8fdf8fdf8])),(BitVec.ofNat 152 (word80 [0x248124812481248124,0x81248124812481248124]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g21C : List ColumnInfo := []
def g21A : List (List Nat) := [[],[66],[32],[32,64],[64,32],[64]]
def g21D3 (j : Nat) := if j=0 then 0x7 else 0
def g21L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g21D3)
  | _ => emptyPacking
def g21I (_ _ : Nat) : Option (Nat × Nat) := none
def g21 : Forest := ⟨21,3,fun i => g21Y[i]?.getD (0,0),g21C,g21A,g21L,g21I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g21P3_0 : block g21 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g21B3 : block g21 3 0 1=true := g21P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g21T : checkedTables g21 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g21 0 0 0 = true)
  · exact (rfl : block g21 1 0 0 = true)
  · exact (rfl : block g21 2 0 0 = true)
  · exact g21B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g21G : graphValid g21 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low21 : Lower true (varsX 21) (graphGoal 21) 4 := lower_forest (g:=g21) (i:=0) (hints:=2) (before_sound [] baseKnown) g21G g21T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K21 := extendKnown [] 4 [(21,[]),(42,[16,50,84]),(69,[100,84]),(81,[66,50,99,83]),(84,[32,16,65,49,99,83]),(133,[116,84,101]),(145,[66,50,115,83,101]),(148,[32,16,65,49,115,83,101]),(161,[82,50,116,100]),(162,[16,82,50,116,100]),(193,[98,50,116,83,84]),(196,[32,16,97,49,116,83,84]),(208,[64,16,98,49,115,82,83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V21 : Known true K21 := extend_ok (m:=21) baseKnown low21 (by decide +kernel)
def g39Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe6de3fff03fff1ffe6,0xde3fff03fff1ffe6de3f])),(BitVec.ofNat 152 (word80 [0x648490a2850240206,0x48490a28502402064849]))),((BitVec.ofNat 152 (word80 [0x19e9c0fffc07fe3f19,0xe9c0fffc07fe3f19e9c0])),(BitVec.ofNat 152 (word80 [0x50e8db2c3161408450,0xe8db2c3161408450e8db]))),((BitVec.ofNat 152 (word80 [0xece607fffff8003fec,0xe607fffff8003fece607])),(BitVec.ofNat 152 (word80 [0x8a7b6b04185892808,0xa7b6b04185892808a7b6]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1b3df8ffffffffc01b,0x3df8ffffffffc01b3df8])),(BitVec.ofNat 152 (word80 [0x891524c08206003089,0x1524c082060030891524]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g39C : List ColumnInfo := []
def g39A : List (List Nat) := [[],[80,33]]
def g39D3 (j : Nat) := if j=0 then 0xf else 0
def g39L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g39D3)
  | _ => emptyPacking
def g39I (_ _ : Nat) : Option (Nat × Nat) := none
def g39 : Forest := ⟨39,3,fun i => g39Y[i]?.getD (0,0),g39C,g39A,g39L,g39I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g39P3_0 : block g39 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g39B3 : block g39 3 0 1=true := g39P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g39T : checkedTables g39 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g39 0 0 0 = true)
  · exact (rfl : block g39 1 0 0 = true)
  · exact (rfl : block g39 2 0 0 = true)
  · exact g39B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g39G : graphValid g39 (boundsBefore K21) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low39 : Lower true (varsX 39) (graphGoal 39) 4 := lower_forest (g:=g39) (i:=0) (hints:=82) (before_sound K21 V21) g39G g39T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K39 := extendKnown K21 4 [(39,[]),(45,[80,33,49]),(51,[66,50]),(57,[49,66]),(75,[16,50,101]),(78,[16,32,48,101]),(90,[96,49,66,16,81]),(102,[16,32,80,48,67,100]),(139,[16,50,117,101]),(142,[16,32,48,117,101]),(154,[112,49,66,16,81,101]),(172,[80,33,49,16,65,116,100]),(184,[112,49,66,16,33,98])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V39 : Known true K39 := extend_ok (m:=39) V21 low39 (by decide +kernel)
def g43Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe6e00e3f80fc7e3fcd,0xc01c7f01f8fc7f9b8038])),(BitVec.ofNat 152 (word80 [0x56e1b6d52a292480ad,0xc36daa545249015b86db]))),((BitVec.ofNat 152 (word80 [0xfdb871ffff007fc7fb,0x70e3fffe00ff8ff6e1c7])),(BitVec.ofNat 152 (word80 [0x858892460c3208110b,0x11248c18641022162249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfbb781ffffff8007f7,0x6f03ffffff000feede07])),(BitVec.ofNat 152 (word80 [0x23524983040312204,0x6a49306080624408d492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x64ffe3ffffffff80c,0x9ffc7ffffffff0193ff8])),(BitVec.ofNat 152 (word80 [0x249204080400400,0x4924081008008000924]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g43C : List ColumnInfo := [(1,0,42,0,4)]
def g43A : List (List Nat) := [[],[49]]
def g43D4 (j : Nat) := if j=0 then 0x1f else 0
def g43L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g43D4)
  | _ => emptyPacking
def g43I (_ _ : Nat) : Option (Nat × Nat) := none
def g43 : Forest := ⟨43,4,fun i => g43Y[i]?.getD (0,0),g43C,g43A,g43L,g43I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43P4_0 : block g43 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g43B4 : block g43 4 0 1=true := g43P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43T : checkedTables g43 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g43 0 0 0 = true)
  · exact (rfl : block g43 1 0 0 = true)
  · exact (rfl : block g43 2 0 0 = true)
  · exact (rfl : block g43 3 0 0 = true)
  · exact g43B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43G : graphValid g43 (boundsBefore K39) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low43 : Lower true (varsX 43) (graphGoal 43) 5 := lower_forest (g:=g43) (i:=0) (hints:=4149) (before_sound K39 V39) g43G g43T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K43 := extendKnown K39 5 [(43,[]),(53,[80,33,67]),(71,[16,50,101]),(101,[80,33,99,67]),(106,[96,49,32,81,66]),(135,[16,50,117,101]),(150,[16,32,67,117,101]),(166,[32,83,67,116,100]),(169,[48,16,33,114,66,100]),(178,[64,32,83,115,99]),(180,[80,33,16,67,49,115,99]),(228,[80,33,16,99,65,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V43 : Known true K43 := extend_ok (m:=43) V39 low43 (by decide +kernel)
def g85Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xdf7ec03c3ffe0fbefd,0x80787ffc1f7dfb00f0ff])),(BitVec.ofNat 152 (word80 [0x820404444444210408,0x8888888420810111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fbf43c3c3fff03f7e,0x878787ffe07efd0f0f0f])),(BitVec.ofNat 152 (word80 [0x40808888888420810,0x11111110841020222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe03fbc03fc3fffc07f,0x7807f87fff80fef00ff0])),(BitVec.ofNat 152 (word80 [0x81011111110841020,0x22222221082040444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffc03ffc003fffff80,0x7ff8007fffff00fff000])),(BitVec.ofNat 152 (word80 [0x102022222221082040,0x44444442104080888888]))),(0x0,0x0),(0x0,0x0)]
def g85C : List ColumnInfo := [(1,0,84,0,4),(4,0,81,0,4),(16,0,69,0,4),(64,0,21,0,4)]
def g85A : List (List Nat) := [[],[100],[66],[66,98],[98,66],[98],[32],[32,100],[32,64],[32,64,96],[32,96,64],[32,96],[64,32],[64,32,98],[64],[64,96],[64,98],[64,98,32],[96,32,66],[96,32],[96,64],[96],[96,66,32],[96,66]]
def g85D3 := limbs80 #[#[0x23ea6a1221e12148110,0x8028]]
def g85D4 := limbs80 #[#[0x2fd0910bd42443e48110,0x609085870]]
def g85H4 (j : Nat) := if j=0 then 0xe8 else 0
def g85D5 (j : Nat) := if j=0 then 0xd1027d10 else 0
def g85H5 := limbs80 #[#[0x2e0000046b0c004,0x69584007236]]
def g85D6 (j : Nat) := if j=0 then 0x3904f else 0
def g85H6 := limbs80 #[#[0x681d00082002442a,0x3c000]]
def g85L : Nat → Packing
  | 3 => (2,3,2,0,0,5,0,g85D3)
  | 4 => (3,2,2,0,0,5,0,g85D4)
  | 5 => (1,1,2,0,0,0,0,g85D5)
  | 6 => (1,0,2,0,0,0,0,g85D6)
  | _ => emptyPacking
def g85I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 2 0 5 1 0 g85H4
  | 5 => lookupWord 2 13 3 9 2 3 g85H5
  | 6 => lookupWord 1 11 0 9 0 5 g85H6
  | _ => fun _ => none
def g85 : Forest := ⟨85,6,fun i => g85Y[i]?.getD (0,0),g85C,g85A,g85L,g85I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g85P3_0 : block g85 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g85B3 : block g85 3 0 2=true := g85P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g85P4_0 : block g85 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g85B4 : block g85 4 0 3=true := g85P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g85P5_0 : block g85 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g85B5 : block g85 5 0 1=true := g85P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g85P6_0 : block g85 6 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g85B6 : block g85 6 0 1=true := g85P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g85T : checkedTables g85 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g85 0 0 0 = true)
  · exact (rfl : block g85 1 0 0 = true)
  · exact (rfl : block g85 2 0 0 = true)
  · exact g85B3
  · exact g85B4
  · exact g85B5
  · exact g85B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g85G : graphValid g85 (boundsBefore K43) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low85 : Lower true (varsX 85) (graphGoal 85) 7 := lower_forest (g:=g85) (i:=0) (hints:=2) (before_sound K43 V43) g85G g85T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K85 := extendKnown K43 7 [(85,[]),(149,[118]),(197,[100,84,117]),(209,[66,50,99,83,117]),(212,[32,16,65,49,99,83,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V85 : Known true K85 := extend_ok (m:=85) V43 low85 (by decide +kernel)
def g163Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe7d01c7fc0fc7cfe7,0xd01c7fc0fc7cfe7d01c7])),(BitVec.ofNat 152 (word80 [0x51d124928a290a051,0xd124928a290a051d1249]))),((BitVec.ofNat 152 (word80 [0x3f8b8e38fff007f3f8,0xb8e38fff007f3f8b8e38])),(BitVec.ofNat 152 (word80 [0x884b924930c3210884,0xb924930c3210884b9249]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fe7703ffffff803fe,0x7703ffffff803fe7703f])),(BitVec.ofNat 152 (word80 [0x100024924104020100,0x2492410402010002492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc018ffc0fffffffc01,0x8ffc0fffffffc018ffc0])),(BitVec.ofNat 152 (word80 [0x200049248208040200,0x4924820804020004924]))),(0x0,0x0)]
def g163C : List ColumnInfo := [(1,0,162,0,4)]
def g163A : List (List Nat) := [[],[117],[16],[16,117]]
def g163D4 (j : Nat) := if j=0 then 0x1f else 0
def g163L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g163D4)
  | _ => emptyPacking
def g163I (_ _ : Nat) : Option (Nat × Nat) := none
def g163 : Forest := ⟨163,4,fun i => g163Y[i]?.getD (0,0),g163C,g163A,g163L,g163I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g163P4_0 : block g163 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g163B4 : block g163 4 0 1=true := g163P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g163T : checkedTables g163 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g163 0 0 0 = true)
  · exact (rfl : block g163 1 0 0 = true)
  · exact (rfl : block g163 2 0 0 = true)
  · exact (rfl : block g163 3 0 0 = true)
  · exact g163B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g163G : graphValid g163 (boundsBefore K85) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low163 : Lower true (varsX 163) (graphGoal 163) 5 := lower_forest (g:=g163) (i:=0) (hints:=85) (before_sound K85 V85) g163G g163T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K163 := extendKnown K85 5 [(163,[]),(165,[32,81,16]),(170,[48,113,32,81]),(198,[16,32,101]),(225,[80,97,33,50,67]),(226,[80,97,32,50,67,65])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V163 : Known true K163 := extend_ok (m:=163) V85 low163 (by decide +kernel)
def g31Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc00fff0ffffffc00ff,0xfff0fffeea3a5303f03f])),(BitVec.ofNat 152 (word80 [0x84a08a210802284a02,0x80220882200a53145145]))),((BitVec.ofNat 152 (word80 [0xfff0000ffc3fffff00,0x3fffffc009adfd000fc0])),(BitVec.ofNat 152 (word80 [0xc42c405090b10c4b,0x11404108092d994d34d3]))),((BitVec.ofNat 152 (word80 [0xfffffff0003fffffff,0xc000fffd77e88afc003f])),(BitVec.ofNat 152 (word80 [0x90130026104c0100c,0x584120152a08828a28a]))),((BitVec.ofNat 152 (word80 [0x3fffffff,0xffff00012697f4000fc0])),(BitVec.ofNat 152 (word80 [0x2e09c08b8227026090,0x26009c11269264b2cb2c]))),((BitVec.ofNat 152 (word80 [0xffffffffffc0000000,0x39d530dfff000])),(BitVec.ofNat 152 (word80 [0x300e000c00380380e0,0x3808e0208d5104c30c30]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g31C : List ColumnInfo := [(0,2,21,8,5)]
def g31A : List (List Nat) := [[],[66],[49],[49,66],[32],[32,64],[32,49],[32,49,64],[64,32],[64],[64,49,32],[64,49]]
def g31D5 (j : Nat) := if j=0 then 0x3f else 0
def g31L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g31D5)
  | _ => emptyPacking
def g31I (_ _ : Nat) : Option (Nat × Nat) := none
def g31 : Forest := ⟨31,5,fun i => g31Y[i]?.getD (0,0),g31C,g31A,g31L,g31I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P5_0 : block g31 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B5 : block g31 5 0 1=true := g31P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31T : checkedTables g31 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact (rfl : block g31 4 0 0 = true)
  · exact g31B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31G : graphValid g31 (boundsBefore K163) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low31 : Lower true (varsX 31) (graphGoal 31) 6 := lower_forest (g:=g31) (i:=0) (hints:=4146) (before_sound K163 V163) g31G g31T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K31 := extendKnown K163 6 [(31,[]),(62,[16,32,48,64,80])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V31 : Known true K31 := extend_ok (m:=31) V163 low31 (by decide +kernel)
def g47Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc01ffffe1fffc01f,0xfff87fffe4d2a4007c1f])),(BitVec.ofNat 152 (word80 [0x228944508440228940,0xa01108826012a45294a5]))),((BitVec.ofNat 152 (word80 [0xffffe007ffe1ffffe0,0xfffffc03359f20f83e0])),(BitVec.ofNat 152 (word80 [0xb01816028040b0182,0xc0a00108205932318c63]))),((BitVec.ofNat 152 (word80 [0xfffffff80001ffffff,0xf0007ffccfd11c00001f])),(BitVec.ofNat 152 (word80 [0x4c12098530894c2213,0xac252008fc119ad6b5a]))),((BitVec.ofNat 152 (word80 [0x1ffffff,0xffff80004d2fe9f003e0])),(BitVec.ofNat 152 (word80 [0x701c0e01c110700c04,0x3001c104506c8c6318c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffe000000,0x33aa61bfffc00])),(BitVec.ofNat 152 (word80 [0x802010060001803018,0xc0460211aa001084210]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g47C : List ColumnInfo := [(0,4,42,1,5),(4,0,43,0,5),(1,4,42,0,4),(2,0,45,0,4),(8,0,39,0,4)]
def g47A : List (List Nat) := [[],[49]]
def g47D4 (j : Nat) := if j=0 then 0x57d4d41 else 0
def g47D5 := limbs80 #[#[0x260d140ff41fd41fd31,0x2012]]
def g47H5 (j : Nat) := if j=0 then 0x0 else 0
def g47D6 (j : Nat) := if j=0 then 0x18d09f else 0
def g47H6 := limbs80 #[#[0x8c000000000500,0x1880000000000000000,0x1000000003d000000000]]
def g47L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g47D4)
  | 5 => (3,1,3,0,0,5,0,g47D5)
  | 6 => (1,0,3,0,0,0,0,g47D6)
  | _ => emptyPacking
def g47I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g47H5
  | 6 => lookupWord 1 43 0 7 2 1 g47H6
  | _ => fun _ => none
def g47 : Forest := ⟨47,6,fun i => g47Y[i]?.getD (0,0),g47C,g47A,g47L,g47I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P4_0 : block g47 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g47B4 : block g47 4 0 1=true := g47P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P5_0 : block g47 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g47B5 : block g47 5 0 3=true := g47P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P6_0 : block g47 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g47B6 : block g47 6 0 1=true := g47P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47T : checkedTables g47 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g47 0 0 0 = true)
  · exact (rfl : block g47 1 0 0 = true)
  · exact (rfl : block g47 2 0 0 = true)
  · exact (rfl : block g47 3 0 0 = true)
  · exact g47B4
  · exact g47B5
  · exact g47B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47G : graphValid g47 (boundsBefore K31) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low47 : Lower true (varsX 47) (graphGoal 47) 7 := lower_forest (g:=g47) (i:=0) (hints:=4146) (before_sound K31 V31) g47G g47T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K47 := extendKnown K31 7 [(47,[]),(55,[80,33,67]),(59,[66]),(61,[80,33,49,65]),(79,[16,50,101]),(91,[16,50,66,101]),(94,[16,32,48,64,101]),(109,[80,33,49,97,65]),(110,[96,49,81,64]),(121,[80,65,50,98]),(143,[16,50,117,101]),(155,[16,50,66,117,101]),(158,[16,32,48,64,117,101]),(188,[80,33,49,65,16,113,97])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V47 : Known true K47 := extend_ok (m:=47) V31 low47 (by decide +kernel)
def g87Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff00ff87f87ffc0,0x7fc7ffffd3b94000f0ff])),(BitVec.ofNat 152 (word80 [0x1440a0a05101100285,0x2902008418941111111]))),((BitVec.ofNat 152 (word80 [0x1ffff0007ff87fff,0x8007f1fc231ee00f0000])),(BitVec.ofNat 152 (word80 [0x588ac4c5622a012b06,0x2b214491231ee7777777]))),((BitVec.ofNat 152 (word80 [0x1fffffff80007fff,0xfff801ff9c1f30f00f0f])),(BitVec.ofNat 152 (word80 [0x61030101800c220c08,0xc0188201c1602222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06060430443010,0x300200c20260b4444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008080040004020,0x40040100000008888888]))),(0x0,0x0),(0x0,0x0)]
def g87C : List ColumnInfo := [(2,0,85,0,7)]
def g87A : List (List Nat) := [[],[66],[32],[32,64],[64,32],[64]]
def g87D7 (j : Nat) := if j=0 then 0x3f else 0
def g87L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g87D7)
  | _ => emptyPacking
def g87I (_ _ : Nat) : Option (Nat × Nat) := none
def g87 : Forest := ⟨87,7,fun i => g87Y[i]?.getD (0,0),g87C,g87A,g87L,g87I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g87P7_0 : block g87 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g87B7 : block g87 7 0 1=true := g87P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g87T : checkedTables g87 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g87 0 0 0 = true)
  · exact (rfl : block g87 1 0 0 = true)
  · exact (rfl : block g87 2 0 0 = true)
  · exact (rfl : block g87 3 0 0 = true)
  · exact (rfl : block g87 4 0 0 = true)
  · exact (rfl : block g87 5 0 0 = true)
  · exact (rfl : block g87 6 0 0 = true)
  · exact g87B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g87G : graphValid g87 (boundsBefore K47) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low87 : Lower true (varsX 87) (graphGoal 87) 8 := lower_forest (g:=g87) (i:=0) (hints:=98) (before_sound K47 V47) g87G g87T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K87 := extendKnown K47 8 [(87,[]),(117,[32,81,64,49,96]),(151,[118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V87 : Known true K87 := extend_ok (m:=87) V47 low87 (by decide +kernel)
def g103Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff007fe1ff0fffc03f,0xfff0fffff95e0200f0ff])),(BitVec.ofNat 152 (word80 [0xa0501440220028281,0x40220020980602111111]))),((BitVec.ofNat 152 (word80 [0xffff8001fff0ffffc0,0x1fff0ff01c35b90f0f00])),(BitVec.ofNat 152 (word80 [0x2c06058814020b0305,0x81402042183511333333]))),((BitVec.ofNat 152 (word80 [0xfffffffe0000ffffff,0xe0000fff23b566f0000f])),(BitVec.ofNat 152 (word80 [0xb028160058442c0406,0x5844280213164666666]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff,0xfffff000134bf8000ff0])),(BitVec.ofNat 152 (word80 [0xc0b058116088b02828,0x16000b040348e8cccccc]))),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc060018000c03030,0x18088c08468880888888]))),(0x0,0x0),(0x0,0x0)]
def g103C : List ColumnInfo := [(2,0,101,0,5)]
def g103A : List (List Nat) := [[],[96,81]]
def g103D5 (j : Nat) := if j=0 then 0x3f else 0
def g103L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g103D5)
  | _ => emptyPacking
def g103I (_ _ : Nat) : Option (Nat × Nat) := none
def g103 : Forest := ⟨103,5,fun i => g103Y[i]?.getD (0,0),g103C,g103A,g103L,g103I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103P5_0 : block g103 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g103B5 : block g103 5 0 1=true := g103P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103T : checkedTables g103 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g103 0 0 0 = true)
  · exact (rfl : block g103 1 0 0 = true)
  · exact (rfl : block g103 2 0 0 = true)
  · exact (rfl : block g103 3 0 0 = true)
  · exact (rfl : block g103 4 0 0 = true)
  · exact g103B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103G : graphValid g103 (boundsBefore K87) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low103 : Lower true (varsX 103) (graphGoal 103) 6 := lower_forest (g:=g103) (i:=0) (hints:=82) (before_sound K87 V87) g103G g103T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K103 := extendKnown K87 6 [(103,[]),(107,[16,50,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V103 : Known true K103 := extend_ok (m:=103) V87 low103 (by decide +kernel)
def g167Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff00ff87f87ffc0,0x7fff8fffd8b95000f0ff])),(BitVec.ofNat 152 (word80 [0x1440a0a05101100285,0x5012008488941111111]))),((BitVec.ofNat 152 (word80 [0x1ffff0007ff87fff,0x807ff1fc2b1e600f0f00])),(BitVec.ofNat 152 (word80 [0x5882c0c1620a010b06,0x160a0411291e43333333]))),((BitVec.ofNat 152 (word80 [0x1fffffff80007fff,0xff8001ff941fb0f0000f])),(BitVec.ofNat 152 (word80 [0x610b0505802c222c08,0x182c48a01416b6666666]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06060430443010,0x203000c20260b4444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008080040004020,0x40400100000008888888]))),(0x0,0x0)]
def g167C : List ColumnInfo := [(1,0,166,0,5),(2,0,165,0,5),(4,0,163,0,5),(32,0,135,0,5)]
def g167A : List (List Nat) := [[],[80,33]]
def g167D6 (j : Nat) := if j=0 then 0x4e09f else 0
def g167L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g167D6)
  | _ => emptyPacking
def g167I (_ _ : Nat) : Option (Nat × Nat) := none
def g167 : Forest := ⟨167,6,fun i => g167Y[i]?.getD (0,0),g167C,g167A,g167L,g167I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g167P6_0 : block g167 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g167B6 : block g167 6 0 1=true := g167P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g167T : checkedTables g167 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g167 0 0 0 = true)
  · exact (rfl : block g167 1 0 0 = true)
  · exact (rfl : block g167 2 0 0 = true)
  · exact (rfl : block g167 3 0 0 = true)
  · exact (rfl : block g167 4 0 0 = true)
  · exact (rfl : block g167 5 0 0 = true)
  · exact g167B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g167G : graphValid g167 (boundsBefore K103) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low167 : Lower true (varsX 167) (graphGoal 167) 7 := lower_forest (g:=g167) (i:=0) (hints:=82) (before_sound K103 V103) g167G g167T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K167 := extendKnown K103 7 [(167,[]),(171,[16,50,117]),(179,[66,50]),(230,[16,32,80,48,67,100]),(234,[112,49,98,16,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V167 : Known true K167 := extend_ok (m:=167) V103 low167 (by decide +kernel)
def g173Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc03ffff0fffc03f,0xe1ffffffe9561600f0ff])),(BitVec.ofNat 152 (word80 [0x204848081220048480,0x44120020890602111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc03fff0ffffc0,0x1ff0fff24b5730f000f])),(BitVec.ofNat 152 (word80 [0x42911150a40229010a,0x88242240209171666666]))),((BitVec.ofNat 152 (word80 [0xffffffc0000ffffff,0xfe000ff01bb52c000f00])),(BitVec.ofNat 152 (word80 [0x88e0606238448e2623,0x13848820bb50cbbbbbb]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf00000000000ffffff,0xfffff000134bf8f00ff0])),(BitVec.ofNat 152 (word80 [0x3018180c08830080c,0x400304104870444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc0202030000c03030,0x11808c08462084888888]))),(0x0,0x0)]
def g173C : List ColumnInfo := [(0,8,133,32,5),(4,0,169,0,5),(8,0,165,0,5),(1,0,172,0,4),(32,8,133,0,4),(128,0,45,0,4)]
def g173A : List (List Nat) := [[],[112]]
def g173D4 (j : Nat) := if j=0 then 0x5dd4540 else 0
def g173D5 (j : Nat) := if j=0 then 0xc8404fd40 else 0
def g173H5 (j : Nat) := if j=0 then 0xc0 else 0
def g173D6 (j : Nat) := if j=0 then 0x2b460bf else 0
def g173H6 (j : Nat) := if j=0 then 0x6 else 0
def g173L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g173D4)
  | 5 => (1,1,3,0,0,0,0,g173D5)
  | 6 => (1,0,3,0,0,0,0,g173D6)
  | _ => emptyPacking
def g173I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g173H5
  | 6 => lookupWord 1 2 0 4 0 0 g173H6
  | _ => fun _ => none
def g173 : Forest := ⟨173,6,fun i => g173Y[i]?.getD (0,0),g173C,g173A,g173L,g173I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173P4_0 : block g173 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g173B4 : block g173 4 0 1=true := g173P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173P5_0 : block g173 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g173B5 : block g173 5 0 1=true := g173P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173P6_0 : block g173 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g173B6 : block g173 6 0 1=true := g173P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173T : checkedTables g173 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g173 0 0 0 = true)
  · exact (rfl : block g173 1 0 0 = true)
  · exact (rfl : block g173 2 0 0 = true)
  · exact (rfl : block g173 3 0 0 = true)
  · exact g173B4
  · exact g173B5
  · exact g173B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173G : graphValid g173 (boundsBefore K167) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low173 : Lower true (varsX 173) (graphGoal 173) 7 := lower_forest (g:=g173) (i:=0) (hints:=20482) (before_sound K167 V167) g173G g173T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K173 := extendKnown K167 7 [(173,[]),(174,[16,50,117]),(185,[66]),(186,[16,50,66,117]),(203,[96,33,16,81]),(233,[98,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V173 : Known true K173 := extend_ok (m:=173) V167 low173 (by decide +kernel)
def g181Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fc7f807f8ff1ffe0,0x7fffffcfd609000ff0ff])),(BitVec.ofNat 152 (word80 [0x80801010100200041,0x2040080000011111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfc007fff800ffe1fff,0x80fe3ff1cdec00f00f0f])),(BitVec.ofNat 152 (word80 [0x109112121222404482,0x240889040cac22222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7ffffff0001fff,0xff003ffe31e30f000ff0])),(BitVec.ofNat 152 (word80 [0xa12224242404848904,0x8511200b14344444444]))),((BitVec.ofNat 152 (word80 [0xffff80000000001fff,0xffffc0003b98f000f000])),(BitVec.ofNat 152 (word80 [0xc1c038383847090e08,0x30601c293b9866666666]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffe000,0x2816ffff0000])),(BitVec.ofNat 152 (word80 [0x20040404008001010,0x40802000000088888888]))),(0x0,0x0)]
def g181C : List ColumnInfo := [(32,0,149,0,7)]
def g181A : List (List Nat) := [[],[66],[112],[112,66]]
def g181D7 (j : Nat) := if j=0 then 0x3f else 0
def g181L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g181D7)
  | _ => emptyPacking
def g181I (_ _ : Nat) : Option (Nat × Nat) := none
def g181 : Forest := ⟨181,7,fun i => g181Y[i]?.getD (0,0),g181C,g181A,g181L,g181I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P7_0 : block g181 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g181B7 : block g181 7 0 1=true := g181P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181T : checkedTables g181 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g181 0 0 0 = true)
  · exact (rfl : block g181 1 0 0 = true)
  · exact (rfl : block g181 2 0 0 = true)
  · exact (rfl : block g181 3 0 0 = true)
  · exact (rfl : block g181 4 0 0 = true)
  · exact (rfl : block g181 5 0 0 = true)
  · exact (rfl : block g181 6 0 0 = true)
  · exact g181B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181G : graphValid g181 (boundsBefore K173) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low181 : Lower true (varsX 181) (graphGoal 181) 8 := lower_forest (g:=g181) (i:=0) (hints:=2) (before_sound K173 V173) g181G g181T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K181 := extendKnown K173 8 [(181,[]),(199,[96,49,32,65,33,81]),(229,[100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V181 : Known true K181 := extend_ok (m:=181) V173 low181 (by decide +kernel)
def g182Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffc00ff87fc3fff00,0xffffffe257e300007fe0])),(BitVec.ofNat 152 (word80 [0x20a82a051048802a2a,0xa12004a546306318c63]))),((BitVec.ofNat 152 (word80 [0xfffff0007ffc3ffff,0xff1ffd9276c00f801f])),(BitVec.ofNat 152 (word80 [0x42308c262110088c0c,0x4c0444811226ca5294a5]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffff80003ffff,0xff001ffce8f541f0001f])),(BitVec.ofNat 152 (word80 [0x84c130480261113030,0x10588900e8d114a5294a]))),((BitVec.ofNat 152 (word80 [0xf0000000000003ffff,0xffffe0005f98fe0003e0])),(BitVec.ofNat 152 (word80 [0x701c070438221c040,0x60600e100b98d8c6318c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x3280bbffffc00])),(BitVec.ofNat 152 (word80 [0x80200800400020080,0x80801000000021084210]))),(0x0,0x0)]
def g182C : List ColumnInfo := [(2,0,180,0,5),(4,0,178,0,5),(16,0,166,0,5),(32,0,150,0,5),(20,0,162,0,4),(34,0,148,0,4)]
def g182A : List (List Nat) := [[],[66],[33,84],[33,81,65],[65,33,82],[65,82],[81],[81,66]]
def g182D4 := limbs80 #[#[0x9bd89544426d6215110,0x31826f625474]]
def g182D5 := limbs80 #[#[0x7c54443f2808857d4d40,0xfea8885f95110beaa221,0x7d4d40bfa8a81fb40502,0xcc8d018160c02faa3a07,0x882188201161080d176b,0x8118204c10001]]
def g182H5 (j : Nat) := if j=0 then 0x3921f000827800 else 0
def g182D6 := limbs80 #[#[0x540a0380ff40fd40fd10,0x2150c8543]]
def g182H6 := limbs80 #[#[0x2d30000000000001b,0x700191c6554002e15200,0x42278361b02001810018,0x285f5c0000180000c]]
def g182D7 (j : Nat) := if j=0 then 0x1605f else 0
def g182H7 := limbs80 #[#[0x58a5001c4b0e,0x158ba0062400000,0x12400ec800040,0x850000]]
def g182L : Nat → Packing
  | 4 => (3,3,3,0,0,4,0,g182D4)
  | 5 => (10,2,3,0,0,7,0,g182D5)
  | 6 => (3,1,3,0,0,6,0,g182D6)
  | 7 => (1,0,3,0,0,0,0,g182D7)
  | _ => emptyPacking
def g182I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 7 0 8 2 2 g182H5
  | 6 => lookupWord 4 29 4 10 4 2 g182H6
  | 7 => lookupWord 3 31 1 9 2 3 g182H7
  | _ => fun _ => none
def g182 : Forest := ⟨182,7,fun i => g182Y[i]?.getD (0,0),g182C,g182A,g182L,g182I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g182P4_0 : block g182 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g182B4 : block g182 4 0 3=true := g182P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g182P5_0 : block g182 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g182P5_1 : block g182 5 1 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g182B5 : block g182 5 0 10=true := (@block_merge g182 5 0 1 9 g182P5_0 g182P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g182P6_0 : block g182 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g182B6 : block g182 6 0 3=true := g182P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g182P7_0 : block g182 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g182B7 : block g182 7 0 1=true := g182P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g182T : checkedTables g182 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g182 0 0 0 = true)
  · exact (rfl : block g182 1 0 0 = true)
  · exact (rfl : block g182 2 0 0 = true)
  · exact (rfl : block g182 3 0 0 = true)
  · exact g182B4
  · exact g182B5
  · exact g182B6
  · exact g182B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g182G : graphValid g182 (boundsBefore K181) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low182 : Lower true (varsX 182) (graphGoal 182) 8 := lower_forest (g:=g182) (i:=0) (hints:=269616208) (before_sound K181 V181) g182G g182T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K182 := extendKnown K181 8 [(182,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V182 : Known true K182 := extend_ok (m:=182) V181 low182 (by decide +kernel)
def g213Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc0fc0fc0fdf81fbf7f,0x3f7efec0007c00f83ff])),(BitVec.ofNat 152 (word80 [0x820820820810410202,0x8204040210842108421]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff000fff01ffe03fbf,0xfc07f7f400f801f07c1f])),(BitVec.ofNat 152 (word80 [0x41041041020820404,0x10408080421084210842]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffff00001ffffc03f,0xfff807f81f003e007fe0])),(BitVec.ofNat 152 (word80 [0x82082082041040808,0x20810100842108421084]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffe0000003f,0xfffff803e0003fff8000])),(BitVec.ofNat 152 (word80 [0x104104104082081010,0x41020201084210842108]))),((BitVec.ofNat 152 (word80 [0xffffffffffffffffc0,0x3ffffc0000000])),(BitVec.ofNat 152 (word80 [0x208208208104102020,0x82040402108421084210]))),(0x0,0x0)]
def g213C : List ColumnInfo := [(1,0,212,0,7),(4,0,209,0,7),(16,0,197,0,7),(64,0,149,0,7),(128,0,85,0,7),(5,0,208,0,4),(17,0,196,0,4),(20,0,193,0,4),(65,0,148,0,4),(68,0,145,0,4),(80,0,133,0,4)]
def g213A : List (List Nat) := [[],[118],[100],[100,116],[116,100],[116],[66],[66,118],[66,98],[66,98,114],[66,114,98],[66,114],[98,66],[98,66,116],[98],[98,114],[98,116],[98,116,66],[114,66,100],[114,66],[114,98],[114],[114,100,66],[114,100],[32],[32,118],[32,100],[32,100,116],[32,116,100],[32,116],[32,64],[32,64,118],[32,64,96],[32,64,96,112],[32,64,112,96],[32,64,112],[32,96,64],[32,96,64,116],[32,96],[32,96,112],[32,96,116],[32,96,116,64],[32,112,64,100],[32,112,64],[32,112,96],[32,112],[32,112,100,64],[32,112,100],[64,32],[64,32,118],[64,32,98],[64,32,98,114],[64,32,114,98],[64,32,114],[64],[64,118],[64,96],[64,96,112],[64,112,96],[64,112],[64,98],[64,98,114],[64,98,32],[64,98,32,112],[64,98,112,32],[64,98,112],[64,114,98],[64,114],[64,114,32,96],[64,114,32],[64,114,96],[64,114,96,32],[96,32,66],[96,32,66,116],[96,32],[96,32,114],[96,32,116],[96,32,116,66],[96,64],[96,64,116],[96],[96,112],[96,116],[96,116,64],[96,66,32],[96,66,32,114],[96,66],[96,66,112],[96,66,114],[96,66,114,32],[96,114,64,66],[96,114,64],[96,114,66],[96,114,66,64],[96,114],[96,114,32],[112,32,66,100],[112,32,66],[112,32,98],[112,32],[112,32,100,66],[112,32,100],[112,64,100],[112,64],[112,96],[112],[112,100,64],[112,100],[112,66,32,98],[112,66,32],[112,66,96],[112,66],[112,66,98,32],[112,66,98],[112,98,64],[112,98,64,66],[112,98,66,64],[112,98,66],[112,98,32],[112,98]]
def g213D3 := limbs80 #[#[0x887805915350d2148110,0x4180360709aa26498a40,0x2]]
def g213D4 := limbs80 #[#[0x48110f415350d2148110,0x54d2148110b618550d21,0xe636454d2148110e6164,0x48110b638454d2148110,0xd4d2148110e6364d4d21,0xf41544c93148110b6184,0x48110f43544c93148110,0xd913148110f814350931,0xcb374d913148110ad183,0x4c91087b805d9544c910,0x82a4854300c3874dc165,0x808103df5df82d4b78d9,0x4002820a04000000120,0x1]]
def g213H4 := limbs80 #[#[0x0,0x0,0xfc4c0d00000010,0x30000000201000000000,0x7]]
def g213D5 := limbs80 #[#[0xa4290221d854d2148110,0x4887c1324c520443b1a9,0x850d214811087ee8b2a6,0xc520443f0a9a4290221f,0x10fc2e498a40887e1424,0xaa26290221dc55131481,0xa40886f1644c520443b9,0x15e5d54348110de6c898,0x254d20442f5b92a69022,0x8110cf2c8a9a408876b7,0xbdba2a6902219ed91534,0xa9a408867b64d4d20442,0x221bc585604c910af2e9,0xf76551324423ebb2a899,0x44c910adae5aa2648847,0x423ebb6a8992218fd935,0xe8b2a648856f72595324,0x992219edc1654c910a7e,0x63f74595324431e3a2ca,0xa654c9108fee8b2a6488,0x24423ebb4ca992215b5c,0x7ee8b1aa48856f7254d5,0xc7a92211f5d36354910a,0xb62007a1502e0023fba2,0x364a11a43106400e2370,0xbe681926317e5e16a531,0x16821fa7b1e6781d2711,0x669825a9323e8c22a872,0xc19cc144090805739216,0x7381801800a090605101,0x300242048144070605,0x8202041810904000241d],#[0x3481002410805020c200,0xc1d2040d221200c0810,0x404000074810204000,0x41010204]]
def g213H5 := limbs80 #[#[0x8000482242d520012002,0xc14f040e33182f831c33,0x14e0079e3c86b500da1,0x38920000c30355380000,0xcc0002992826fac32019,0x3c25237de40000301a47,0x58e100000001c8111823,0xc0004c8ca0a50614000,0x19787c3d868000101706,0x80000000000000060ca8,0x4941000000021b1,0x3d7030c7011a4b70f400,0xa01c8063b128,0x29e3a0200000000,0x31860240001804749400,0x180555c00002cc68000a,0x1c7218030001a920000,0xd00000ca0724720e600,0xe18480100008,0x606050100000000]]
def g213D6 := limbs80 #[#[0xfc4c520443e12148110,0x10ded4d2044379534811,0x9109fd8d524427d654c9,0x8110fe50d204427d63d4,0x4c910fe58132443f9534,0x54c910dfd51324437d54,0x5354910df995324437d6,0xd6354910bfd8d524437d,0x40600dc00dfd8d524437,0xf1935a94847d0436cb22,0x414795e43886067e5de6,0x12199d20a2870d03a732,0x333a414412202b3c3486,0x5d30e0662d3a58700414,0x4467083058228466143a,0x14288a42836114488241,0x2520ca5214144294a0c0,0x7c019989809920e90215,0x1c305662346610]]
def g213H6 := limbs80 #[#[0xe0080000a00220428a8a,0x6000a1836c06199004,0x400364127ccd051000,0x1200000321f808a0000a,0x800002343d8034000180,0xcf8a20a033c0082364e1,0xc2cc09f001c1389b732a,0x561e8a4f0ae185a01010,0xa001f322a4c9e0000d0c,0x1c1e0002005c499103c8,0x560184005d044d1e288,0x401de30ab0889800640,0x8717c044410cd007f8c0,0x11520000041a21011e,0x1b00c80001c303c34800,0x1002800014d0cc02,0x1440006c3c82b232190c,0x4c83a0000000001007d0,0x1860000000000e024480,0x4851ca31da230097e686,0x1aa02011c1800002016e,0x2068d53c599a380001e0,0x160d7648380000402,0x23dcd14730c13e0a0238,0xebb418000000001485e6,0x3801c00012004b00,0x7c030249872bc1ac0000,0x10f02a,0x9c020478a90e006d2800,0x72c0001e00cc1c04802,0xad9a2e8318001466474,0xe30e51e1c41356c1c30],#[0xa01e100de81044e22c19,0x317a024c012ec8734013]]
def g213D7 := limbs80 #[#[0x7f52442faa4887e48110,0x3015007f54910fe99221,0x94301030ba6694235a3f,0xa5011a6690a20e30ba66,0x38da6690a3c8a142a70,0x4]]
def g213H7 := limbs80 #[#[0x1061708a080,0x80800000000000000000,0x82470134006181200007,0x6400000000000000007,0x9e080001001f81878003,0x80080002005901180000,0x549c1800051a440710,0x101130c0f041d8172,0x12e3210000000008028,0xbc5800000000bc680000,0xa408000000000006018b,0x3c650350000000068088,0x6100000000000000006,0x6426780480005,0x80300000000000008218,0x0,0x7198618000000000000,0x1a180004006d81400000,0x6080000000000000006,0x80100005007abc480006,0x69c10000600748179,0x10410,0x50038,0x73410000000000000,0x3c500000000000000000,0x1ca14,0x9e100000000000000000,0x5583c184a8211,0x0,0x0,0x1a100000000000000000,0x31c479c3e810e0040],#[0x584420438,0x28358000000000000,0x707098740,0x403bc2480000,0x100265448]]
def g213D8 (j : Nat) := if j=0 then 0x2d2720806fd10 else 0
def g213H8 := limbs80 #[#[0x50403,0xc0000000000210f00000,0x20008140000000003129,0xe2,0xd01000000321,0xb0000000000000000000,0x60,0x206e0e030000006d0000,0xc1b000f11a,0xf02000000b2400]]
def g213D9 (j : Nat) := if j=0 then 0x219080bf else 0
def g213H9 := limbs80 #[#[0x9000000318003895808,0xb8f40600000000000785,0x1da5790a]]
def g213L : Nat → Packing
  | 3 => (2,6,4,0,0,5,0,g213D3)
  | 4 => (14,5,4,0,0,7,0,g213D4)
  | 5 => (38,4,4,0,0,10,0,g213D5)
  | 6 => (18,3,4,0,0,10,0,g213D6)
  | 7 => (5,2,4,0,0,8,0,g213D7)
  | 8 => (1,1,4,0,0,0,0,g213D8)
  | 9 => (1,0,4,0,0,0,0,g213D9)
  | _ => emptyPacking
def g213I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 29 0 12 1 7 g213H4
  | 5 => lookupWord 16 101 4 15 4 7 g213H5
  | 6 => lookupWord 30 149 7 17 6 7 g213H6
  | 7 => lookupWord 17 179 3 16 5 7 g213H7
  | 8 => lookupWord 4 67 2 12 3 5 g213H8
  | 9 => lookupWord 2 17 2 11 0 7 g213H9
  | _ => fun _ => none
def g213 : Forest := ⟨213,9,fun i => g213Y[i]?.getD (0,0),g213C,g213A,g213L,g213I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P3_0 : block g213 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g213B3 : block g213 3 0 2=true := g213P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P4_0 : block g213 4 0 14=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g213B4 : block g213 4 0 14=true := g213P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P5_0 : block g213 5 0 4=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P5_4 : block g213 5 4 34=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g213B5 : block g213 5 0 38=true := (@block_merge g213 5 0 4 34 g213P5_0 g213P5_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P6_0 : block g213 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P6_1 : block g213 6 1 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P6_7 : block g213 6 7 11=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g213B6 : block g213 6 0 18=true := (@block_merge g213 6 0 1 17 g213P6_0 (@block_merge g213 6 1 6 11 g213P6_1 g213P6_7))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P7_0 : block g213 7 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P7_3 : block g213 7 3 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g213B7 : block g213 7 0 5=true := (@block_merge g213 7 0 3 2 g213P7_0 g213P7_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P8_0 : block g213 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g213B8 : block g213 8 0 1=true := g213P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P9_0 : block g213 9 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g213B9 : block g213 9 0 1=true := g213P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213T : checkedTables g213 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g213 0 0 0 = true)
  · exact (rfl : block g213 1 0 0 = true)
  · exact (rfl : block g213 2 0 0 = true)
  · exact g213B3
  · exact g213B4
  · exact g213B5
  · exact g213B6
  · exact g213B7
  · exact g213B8
  · exact g213B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213G : graphValid g213 (boundsBefore K182) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low213 : Lower true (varsX 213) (graphGoal 213) 10 := lower_forest (g:=g213) (i:=0) (hints:=2) (before_sound K182 V182) g213G g213T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K213 := extendKnown K182 10 [(213,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V213 : Known true K213 := extend_ok (m:=213) V182 low213 (by decide +kernel)
def g227Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1fe1fe01fe1fc3ffc,0x7ffe3ff1ecd460071c7])),(BitVec.ofNat 152 (word80 [0x141441414144088028,0x50a04802424506249249]))),((BitVec.ofNat 152 (word80 [0xfe001fffe001ffc3ff,0xf80ffc7fe17493038e38])),(BitVec.ofNat 152 (word80 [0x181881818188100830,0x60c08104095412249249]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffffffe0003ff,0xfff0007ffcc2f51c003f])),(BitVec.ofNat 152 (word80 [0xa0a10a0a0a00a11140,0x810512280082e1492492]))),((BitVec.ofNat 152 (word80 [0xffffe00000000003ff,0xffffff80003b4be00fc0])),(BitVec.ofNat 152 (word80 [0xc0c00c0c0c10c22181,0x2060030902a49492492]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffffc00,0x30628fff000])),(BitVec.ofNat 152 (word80 [0x10010101001000202,0x4080040000000924924]))),(0x0,0x0)]
def g227C : List ColumnInfo := [(1,0,226,0,5)]
def g227A : List (List Nat) := [[],[101],[16],[16,101],[80,97],[80,97,16],[96,81,16],[96,81]]
def g227D5 (j : Nat) := if j=0 then 0x3f else 0
def g227L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g227D5)
  | _ => emptyPacking
def g227I (_ _ : Nat) : Option (Nat × Nat) := none
def g227 : Forest := ⟨227,5,fun i => g227Y[i]?.getD (0,0),g227C,g227A,g227L,g227I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227P5_0 : block g227 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g227B5 : block g227 5 0 1=true := g227P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227T : checkedTables g227 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g227 0 0 0 = true)
  · exact (rfl : block g227 1 0 0 = true)
  · exact (rfl : block g227 2 0 0 = true)
  · exact (rfl : block g227 3 0 0 = true)
  · exact (rfl : block g227 4 0 0 = true)
  · exact g227B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227G : graphValid g227 (boundsBefore K213) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low227 : Lower true (varsX 227) (graphGoal 227) 6 := lower_forest (g:=g227) (i:=0) (hints:=85) (before_sound K213 V213) g227G g227T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K227 := extendKnown K213 6 [(227,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V227 : Known true K227 := extend_ok (m:=227) V213 low227 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7fffffe0ffffd92a29,0x2351cb0000ff00ff00ff])),(BitVec.ofNat 152 (word80 [0x2800420110182201,0x141c805050505050505]))),((BitVec.ofNat 152 (word80 [0x8003fffffff80a75a4,0xd6e15000ff000000ff00])),(BitVec.ofNat 152 (word80 [0x4b0228008208a7124,0xc6404013131313131313]))),((BitVec.ofNat 152 (word80 [0xfffc0000ffffefc3b2,0x2c8429000000ff0000ff])),(BitVec.ofNat 152 (word80 [0x20c10b0442402701b0,0x2484214a4a4a4a4a4a4a]))),((BitVec.ofNat 152 (word80 [0xffffffff0000209251,0x65fb34ff00000000ff00])),(BitVec.ofNat 152 (word80 [0x9004c001381208201,0x21bb302c2c2c2c2c2c2c]))),((BitVec.ofNat 152 (word80 [0x24dd4e,0xb16d0000000ffff0000])),(BitVec.ofNat 152 (word80 [0x4e0270089c0200dc4e,0xa1210b0b0b0b0b0b0b0]))),((BitVec.ofNat 152 (word80 [0x1324dd,0x980e26ffffff00000000])),(BitVec.ofNat 152 (word80 [0x70038010e0040104d8,0x180406c0c0c0c0c0c0c0]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(2,0,61,0,7),(4,0,59,0,7),(8,0,55,0,7),(16,0,47,0,7),(0,2,21,40,6),(0,4,42,17,6),(0,8,21,34,6),(0,16,42,5,6),(32,0,31,0,6),(1,4,42,16,5),(1,16,42,4,5),(2,8,21,32,5),(4,16,42,1,5),(10,0,53,0,5),(32,2,21,8,5),(32,8,21,2,5),(5,0,42,0,4),(5,16,42,0,4)]
def g63A : List (List Nat) := [[],[66],[49],[49,66],[80,33,67],[80,33,49,65],[80,65,33,50],[80,65,50]]
def g63D5 (j : Nat) := if j=0 then 0x327d937354520 else 0
def g63D6 := limbs80 #[#[0x2efb9aa2906bf644c520,0x9faeda8c41afd935148,0x2801c306801a9c38]]
def g63H6 (j : Nat) := if j=0 then 0xc0 else 0
def g63D7 := limbs80 #[#[0xd58450afd9120b758e10,0x59650bf59620ded4250b,0x4520ff54520ff4c520bf,0x931ffd4620ff4c620ffd,0x331547a2f8f43600ff50,0x220612383b7d52731777,0xe1218a08204898b0071,0x2870910304040208a185,0xb0d104161a01a1041e,0x10340342070d0100a21,0x8600d082054]]
def g63H7 := limbs80 #[#[0x6a000000600d100001b5,0x78000,0x0,0xcc40000000000000000,0x2]]
def g63D8 := limbs80 #[#[0xc50ff107f483fc21fd10,0x1fd31fe90ff943faa1f,0x1ed13e8a37950782a0c0,0x4b08a38914384a88b24e,0x81848a004a1c38a01511,0x28e24818304008a38920,0x460a03ca3891a38a180f,0x8e134e1433222ce2]]
def g63H8 := limbs80 #[#[0xa000388b1206781ca18,0x2c29a270f38843000f04,0xd8400025b2100000000,0xc8300c9e95000e163624,0x450]]
def g63D9 (j : Nat) := if j=0 then 0x1882013f else 0
def g63H9 := limbs80 #[#[0x11e18000000004a01,0x24c00000000c04000000,0x80000000038400000000,0x4c600000000000001a1,0x1a1cc1c480,0xda600041603a4e000a08,0x1a21cb84216e001c3800,0x2a0001a140000000,0x1f48004800000,0x448480000]]
def g63L : Nat → Packing
  | 5 => (1,4,5,0,0,0,0,g63D5)
  | 6 => (4,3,5,0,0,6,0,g63D6)
  | 7 => (12,2,5,0,0,9,0,g63D7)
  | 8 => (9,1,5,0,0,9,0,g63D8)
  | 9 => (1,0,5,0,0,0,0,g63D9)
  | _ => emptyPacking
def g63I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g63H6
  | 7 => lookupWord 1 37 0 9 2 3 g63H7
  | 8 => lookupWord 5 29 3 11 4 3 g63H8
  | 9 => lookupWord 6 67 3 11 4 3 g63H9
  | _ => fun _ => none
def g63 : Forest := ⟨63,9,fun i => g63Y[i]?.getD (0,0),g63C,g63A,g63L,g63I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P5_0 : block g63 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B5 : block g63 5 0 1=true := g63P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_0 : block g63 6 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B6 : block g63 6 0 4=true := g63P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_0 : block g63 7 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_4 : block g63 7 4 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_6 : block g63 7 6 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B7 : block g63 7 0 12=true := (@block_merge g63 7 0 4 8 g63P7_0 (@block_merge g63 7 4 2 6 g63P7_4 g63P7_6))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_0 : block g63 8 0 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B8 : block g63 8 0 9=true := g63P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P9_0 : block g63 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B9 : block g63 9 0 1=true := g63P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63T : checkedTables g63 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g63 0 0 0 = true)
  · exact (rfl : block g63 1 0 0 = true)
  · exact (rfl : block g63 2 0 0 = true)
  · exact (rfl : block g63 3 0 0 = true)
  · exact (rfl : block g63 4 0 0 = true)
  · exact g63B5
  · exact g63B6
  · exact g63B7
  · exact g63B8
  · exact g63B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K227) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 10 := lower_forest (g:=g63) (i:=0) (hints:=4146) (before_sound K227 V227) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K227 10 [(63,[]),(126,[16,32,48,64,80,96])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V227 low63 (by decide +kernel)
def g95Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffc1ffff60ac8,0x4caee8000007f01fc07f])),(BitVec.ofNat 152 (word80 [0x280280084044060880,0x400ce80a142850a14285]))),((BitVec.ofNat 152 (word80 [0xfc003ffffffe021c2c,0x13d9d30003f800003f80])),(BitVec.ofNat 152 (word80 [0x304b04500208221c28,0x3c941264c993264c993]))),((BitVec.ofNat 152 (word80 [0xffffc0001ffffbf0cb,0x81210b01fc000fe0007f])),(BitVec.ofNat 152 (word80 [0x400c0160809009404a,0x12103142850a142850a]))),((BitVec.ofNat 152 (word80 [0xffffffffe0000824f7,0x691ab200000000003f80])),(BitVec.ofNat 152 (word80 [0x8290298014e04820d7,0x6812b2d9b366cd9b366c]))),((BitVec.ofNat 152 (word80 [0x93710,0xa28774fe00000fffc000])),(BitVec.ofNat 152 (word80 [0xe00e010700803700,0xa2821060c183060c1830]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x4c917,0x7e4005fffffff0000000])),(BitVec.ofNat 152 (word80 [0x30030021801008015,0x1c000481020408102040]))),(0x0,0x0),(0x0,0x0)]
def g95C : List ColumnInfo := [(0,8,85,2,8),(8,0,87,0,8),(1,0,94,0,7),(2,8,85,0,7),(4,0,91,0,7),(16,0,79,0,7),(64,0,31,0,6),(5,0,90,0,4),(17,0,78,0,4),(20,0,75,0,4)]
def g95A : List (List Nat) := [[],[66],[32],[32,64],[64,32],[64]]
def g95D4 (j : Nat) := if j=0 then 0x1a2b6460b5454120 else 0
def g95D5 := limbs80 #[#[0x50940483aa5954250120,0x483ca5515250120eab65,0x5915254120d697554940,0x54120e6b64549504839a,0xb6982d51504835add152,0x5d9544838ed935454120,0x4832ed9170d51208fb80,0x1d37059520a3d85d9354,0x8d01d345ca0d141c032e,0x8080002836294c]]
def g95H5 (j : Nat) := if j=0 then 0xe16 else 0
def g95D6 := limbs80 #[#[0x3b4a92a0907a94250120,0xfd2a4a02412fdd16548,0x837db2a80906f9655012,0x20fd6e4a8241fa549504,0x483bdaa2a09077954541,0x120df6c8a8241be59150,0x44833eb2aa8905fb7454,0x51209feecaa2413f5d95,0x544835fb26a8905f970d,0x591209faedaa2419f597,0x1654827ebaec8904ff75,0x59520b7ee8b2a417edc,0xd1654835e3a2ca906fb7,0x70995209fee8b2a41afd,0x5d3654827ebb4ca905f9,0xb7054950bf6e0a92a13f,0xfd93525433fb22a4a877,0xbf7458950afae9a92a19,0x3fdd162d427eba6c4a85,0x78a8431e4d85f258a401,0x5610fb7aba1b6d564309,0x75a2b74ea0cee5d288dc,0xee46ef5da1cde3b037bb,0x8178f049085f3f6ba9c,0x82141100f1e010649ce1,0x810000808205c7806102,0x80101c4080141c80801,0x400e0e2043820700400a,0x8604002005041020050,0x35040000a8]]
def g95H6 := limbs80 #[#[0x6200032492902e13f0,0x20c9094c0000,0x542000727d1784c00000,0x8bc022c00185fd330921,0xd8800a2800000405d672,0x3827220000000065461d,0x20f83000746e0654]]
def g95D7 := limbs80 #[#[0xf59120fe54120fe50120,0xd9520bf59520bfd9120b,0x8950dfd4950df54950bf,0x120ff55120bf58b50bfd,0x20ff59520ff59120ffd5,0xff58950ff54950ff995,0x90ba2585a0c000ffd895,0xc9ce691865a144481023,0xb1c159079aa528ba107,0x648b3242c461f3906207,0x3186c55cc7149207c465,0x522105c731c4c4792217,0x54d62cc51e2cd41851b3,0x51c6185887105506cc4c,0x88710920789516245019,0xf1c065221624501c4195,0x60940c75540]]
def g95H7 := limbs80 #[#[0xa008,0x0,0x0,0x0,0x345000000,0x50821f00,0x0,0x1c8b00041140000000,0x0,0x0,0x30000000000000000000,0x73151130054c,0x0,0x0,0x68200000000000,0xe1a0000000000,0x0,0x1246000000000000,0x0,0x4b1204400000000000,0xd0200000000000,0x1c480000000000,0xc0000004418000000000,0x588,0xc38000000000000000,0x5b4000000000000,0x7604200076998198860,0x4,0x4500000000,0x0,0x0,0x0],#[0x66d25800000000028440,0xb,0x0,0x0,0x2110000000000,0x0,0x0,0x28400000000039480000,0x1,0x0,0xa100000000000000000,0x0,0x0,0x1900000000,0x1c9a0000,0x0,0x184c0000000000000000,0x0,0x28c2000000000000000,0x11000,0x0,0x850000,0x0,0x70b0001824000000,0x0,0x2c8000000000000000,0x0,0xb01d8940000000,0x0,0x0,0x767827c000000000000,0xf000000000],#[0x0,0x349200000000000000,0x0,0x0,0x6014001b0a000,0x0,0x120f0000000001e1500,0x0,0x4900009048000001a170,0x6980000003,0x1a4c,0x0,0xd48000000000,0x106c00000000000,0x2c0200000000000000,0x70500000000000000,0x0,0x60e0000000000000000,0x0,0x40b00,0x0,0x0,0x14000000000000,0x0,0x5030000000000000,0x0,0x180e00000000,0x282600000000000000,0x60a0,0x0,0x9068001112000000,0x0],#[0x69c000000003000000]]
def g95D8 := limbs80 #[#[0xc79aa407fd43faa1fd20,0x98d13568298d131ea414,0x1ad046]]
def g95H8 := limbs80 #[#[0x3000f40000050a002e62,0x90854120968700020,0x470bb6bc31000a28b11,0x7006a2fd2900cf10000d,0x60a805c6a000f4,0x50110220f000827f21,0x6030107e24000b0d0000,0x60e000b0072]]
def g95D9 (j : Nat) := if j=0 then 0x1542317f else 0
def g95H9 := limbs80 #[#[0x92000000000000040000,0x54000000352,0x82000000098880,0x6003c400000000000000,0x7]]
def g95L : Nat → Packing
  | 4 => (1,5,4,0,0,0,0,g95D4)
  | 5 => (13,4,4,0,0,7,0,g95D5)
  | 6 => (39,3,4,0,0,9,0,g95D6)
  | 7 => (18,2,4,0,0,10,0,g95D7)
  | 8 => (3,1,4,0,0,7,0,g95D8)
  | 9 => (1,0,4,0,0,0,0,g95D9)
  | _ => emptyPacking
def g95I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 6 0 2 g95H5
  | 6 => lookupWord 7 47 4 11 4 3 g95H6
  | 7 => lookupWord 18 599 1 13 6 3 g95H7
  | 8 => lookupWord 8 47 5 12 5 3 g95H8
  | 9 => lookupWord 2 37 0 9 2 3 g95H9
  | _ => fun _ => none
def g95 : Forest := ⟨95,9,fun i => g95Y[i]?.getD (0,0),g95C,g95A,g95L,g95I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P4_0 : block g95 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B4 : block g95 4 0 1=true := g95P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P5_0 : block g95 5 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B5 : block g95 5 0 13=true := g95P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6_0 : block g95 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6_3 : block g95 6 3 36=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B6 : block g95 6 0 39=true := (@block_merge g95 6 0 3 36 g95P6_0 g95P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P7_0 : block g95 7 0 10=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P7_10 : block g95 7 10 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B7 : block g95 7 0 18=true := (@block_merge g95 7 0 10 8 g95P7_0 g95P7_10)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P8_0 : block g95 8 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B8 : block g95 8 0 3=true := g95P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P9_0 : block g95 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B9 : block g95 9 0 1=true := g95P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95T : checkedTables g95 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g95 0 0 0 = true)
  · exact (rfl : block g95 1 0 0 = true)
  · exact (rfl : block g95 2 0 0 = true)
  · exact (rfl : block g95 3 0 0 = true)
  · exact g95B4
  · exact g95B5
  · exact g95B6
  · exact g95B7
  · exact g95B8
  · exact g95B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95G : graphValid g95 (boundsBefore K63) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low95 : Lower true (varsX 95) (graphGoal 95) 10 := lower_forest (g:=g95) (i:=0) (hints:=4146) (before_sound K63 V63) g95G g95T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K95 := extendKnown K63 10 [(95,[]),(125,[32,81,64,96]),(159,[118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V95 : Known true K95 := extend_ok (m:=95) V63 low95 (by decide +kernel)
def g111Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffc1ffff726c9,0xd02c890003f8001fc07f])),(BitVec.ofNat 152 (word80 [0x280280084044032480,0x100c890a142850a14285]))),((BitVec.ofNat 152 (word80 [0xfc003ffffffe039128,0x1dd9c201fc000fe03f80])),(BitVec.ofNat 152 (word80 [0x300b00500008238028,0x150940060c183060c183]))),((BitVec.ofNat 152 (word80 [0xffffc0001ffffad8ce,0x83211efe00000000007f])),(BitVec.ofNat 152 (word80 [0x404c0560829008984c,0x8121163468d1a3468d1a]))),((BitVec.ofNat 152 (word80 [0xffffffffe0000804f6,0x691ab3000007f0003f80])),(BitVec.ofNat 152 (word80 [0x8110118008e04004c6,0x6810b358b162c58b162c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x91711,0xa28774000007ffffc000])),(BitVec.ofNat 152 (word80 [0x26026011300881311,0x828204a142850a142850]))),((BitVec.ofNat 152 (word80 [0x4e917,0x7e4005fffff800000000])),(BitVec.ofNat 152 (word80 [0x38038021c01044113,0x6a4000c183060c183060]))),(0x0,0x0),(0x0,0x0)]
def g111C : List ColumnInfo := [(1,0,110,0,7),(2,0,109,0,7),(32,0,79,0,7),(64,0,47,0,7),(0,4,42,65,6),(4,0,107,0,6)]
def g111A : List (List Nat) := [[],[16,50,101],[80,97,50],[96,81]]
def g111D8 (j : Nat) := if j=0 then 0x2c6881bf else 0
def g111L : Nat → Packing
  | 8 => (1,0,3,0,0,0,0,g111D8)
  | _ => emptyPacking
def g111I (_ _ : Nat) : Option (Nat × Nat) := none
def g111 : Forest := ⟨111,8,fun i => g111Y[i]?.getD (0,0),g111C,g111A,g111L,g111I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P8_0 : block g111 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B8 : block g111 8 0 1=true := g111P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111T : checkedTables g111 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact (rfl : block g111 4 0 0 = true)
  · exact (rfl : block g111 5 0 0 = true)
  · exact (rfl : block g111 6 0 0 = true)
  · exact (rfl : block g111 7 0 0 = true)
  · exact g111B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111G : graphValid g111 (boundsBefore K95) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low111 : Lower true (varsX 111) (graphGoal 111) 9 := lower_forest (g:=g111) (i:=0) (hints:=4146) (before_sound K95 V95) g111G g111T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K111 := extendKnown K95 9 [(111,[]),(123,[16,50,66,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V111 : Known true K111 := extend_ok (m:=111) V95 low111 (by decide +kernel)
def g119Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ffe0ffffffff722a,0x900f2a40000fc0fc0fff])),(BitVec.ofNat 152 (word80 [0x28014200400040320a,0x30201041041041041]))),((BitVec.ofNat 152 (word80 [0xfc0000ffe0ffe03942,0x8762f48003f03f000000])),(BitVec.ofNat 152 (word80 [0x301584028204823802,0x8542f0871c71c71c71c7]))),((BitVec.ofNat 152 (word80 [0xffffff0000ffffad94,0xb0d84280fc000003f03f])),(BitVec.ofNat 152 (word80 [0x404600130411000990,0xb058400a28a28a28a28a]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffff0000804d,0x6956a9bf00000003ffc0])),(BitVec.ofNat 152 (word80 [0x809800240026048044,0x904a994514514514514]))),((BitVec.ofNat 152 (word80 [0x9171,0x18b1dc4000003ffc0000])),(BitVec.ofNat 152 (word80 [0x2e008b808b8088171,0x18b00c78e38e38e38e38]))),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x30010c010c0104401,0x42800460820820820820]))),(0x0,0x0),(0x0,0x0)]
def g119C : List ColumnInfo := [(2,0,117,0,8)]
def g119A : List (List Nat) := [[],[66],[96,81],[96,81,66]]
def g119D8 (j : Nat) := if j=0 then 0x7f else 0
def g119L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g119D8)
  | _ => emptyPacking
def g119I (_ _ : Nat) : Option (Nat × Nat) := none
def g119 : Forest := ⟨119,8,fun i => g119Y[i]?.getD (0,0),g119C,g119A,g119L,g119I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P8_0 : block g119 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B8 : block g119 8 0 1=true := g119P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119T : checkedTables g119 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g119 0 0 0 = true)
  · exact (rfl : block g119 1 0 0 = true)
  · exact (rfl : block g119 2 0 0 = true)
  · exact (rfl : block g119 3 0 0 = true)
  · exact (rfl : block g119 4 0 0 = true)
  · exact (rfl : block g119 5 0 0 = true)
  · exact (rfl : block g119 6 0 0 = true)
  · exact (rfl : block g119 7 0 0 = true)
  · exact g119B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119G : graphValid g119 (boundsBefore K111) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low119 : Lower true (varsX 119) (graphGoal 119) 9 := lower_forest (g:=g119) (i:=0) (hints:=82) (before_sound K111 V111) g119G g119T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K119 := extendKnown K111 9 [(119,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V119 : Known true K119 := extend_ok (m:=119) V111 low119 (by decide +kernel)
def g175Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc007ffffe0ffff7266,0xf00b2300000fc003f03f])),(BitVec.ofNat 152 (word80 [0x82500a004204403242,0x20032305145145145145]))),((BitVec.ofNat 152 (word80 [0xfff800ffffffe0390a,0x8766708003f000fc0fc0])),(BitVec.ofNat 152 (word80 [0x602c02800082380a,0x844250030c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xffffff0000ffffad84,0xb85846c0fc000000003f])),(BitVec.ofNat 152 (word80 [0x881302b0429008984,0x985840da69a69a69a69a]))),((BitVec.ofNat 152 (word80 [0xffffffffff0000804d,0x6156adc000003f000fc0])),(BitVec.ofNat 152 (word80 [0x2304408c008e040045,0x61142decb2cb2cb2cb2c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x9171,0x18b1d83f00003ffff000])),(BitVec.ofNat 152 (word80 [0xc0180300830088130,0x18208010410410410410]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x300600c010c0104401,0x43800420820820820820]))),(0x0,0x0)]
def g175C : List ColumnInfo := [(1,0,174,0,7),(2,0,173,0,7),(4,0,171,0,7),(8,0,167,0,7),(32,0,143,0,7),(128,0,47,0,7),(0,4,42,129,6),(0,8,133,34,6),(1,4,42,128,5),(2,8,133,32,5),(5,0,170,0,5),(9,0,166,0,5),(12,0,163,0,5),(32,8,133,2,5),(40,0,135,0,5),(128,4,42,1,5),(132,0,43,0,5),(3,0,172,0,4),(13,0,162,0,4),(14,0,161,0,4),(33,0,142,0,4),(34,0,133,0,4),(34,8,133,0,4),(42,0,133,0,4),(129,0,42,0,4),(129,4,42,0,4),(130,0,45,0,4),(133,0,42,0,4)]
def g175A : List (List Nat) := [[],[16,50,117]]
def g175D5 := limbs80 #[#[0x55140443cc5515150110,0x443cc5514154110e3965,0x5536154140e396455150,0x50550f1b80551535038e,0xb678523060333dcf62,0x50400]]
def g175D6 := limbs80 #[#[0x3d4a12808870d5454d42,0xe3aa8a9a81ce5515050,0x43f8a8a80884ed74d895,0x10df2caa0221ee551404,0x442fcbaa80886fb65501,0x110fe282a82217edd540,0x4437cb22a0887795454,0x5110d7ac8aa221bed915,0x644427fbb2a8884fd765,0x505209faebb22213fdd5,0x1515037db0aa0a05df73,0x4d8540f5a84b0a81cf55,0xc1545027ebaec2a06bd5,0x7059540bf6e0b2a81eed,0x5c7655027fb8acaa06fb,0xd5450550ddec4a0aa13f,0xedc15454376a1ec4a873,0xaf7155142f5ae2aa285d,0x520d0160027eb8ec0aa7,0x23d0d6320b22908e1e0,0xa2631865814a4f12e461,0x12811fe7c1ca711be6e1,0x8a9f2769c262932468a2,0xc505864319160aaea82,0x6c508171b00584a70419,0x31904641021604645820,0x911098e8821904648804,0x60302105814205041411,0x180820703080070,0x204040160454368e844,0xc107030801b14190c645,0xc216058c58219040028],#[0x1c]]
def g175H6 := limbs80 #[#[0x29002b55000000c10080,0xb39614602d000052]]
def g175D7 := limbs80 #[#[0x354d42bbd8950eb50940,0x94e42eb55142f394d42f,0x910fe54110fe50110f3,0x110bf59110fb90910fb5,0x40bfd8540fe54140bfd9,0xef55140f794d40f754d,0xdf55150bfd9540bf5954,0xfd8154fbd8542bfd8542,0x50520ff59110ff55110b,0x9540ff58540ff54540ff,0xd52ff50d50ff50550ff5,0xffd8154ff58154ff50,0x1dc2f8518810da164148,0x2834ee9bb3165349c925,0xc984ad957ca5532a3544,0x174137c6f05d33766b6c,0xc38c6991650c868d7142,0x1192c164c7860068a314,0x64b109078718d3221732,0xf1a2826472e508a21058,0x172c416361163211b229,0x305045888c508c00c141,0xc14116283144f10c885c,0x86c04a317321192c1170,0x282940e0c09b323148c9,0x4421e347486430e0c099,0x264546a44441e2870710,0x89469063258887103830,0x68c9628223141832a508,0x42888c8654a111a8d08c,0xc1c307087070d1c23054,0x432114446431]]
def g175H7 := limbs80 #[#[0xcc5800060400000210c8,0x9258340029d19046cd06,0xac3144947b0ea8808800,0x1e4e061174126fd9a70,0x4f195a1c28c006130200,0x20212fe6000080a3f350,0xc000000002a100122800,0x20c0000044a00221a1,0x207ca04f71f090000000,0x18c8008c791ae6800000,0x59000416001c2]]
def g175D8 := limbs80 #[#[0xd30fe907f443dc85ed42,0xa5fd42fe997f543fa81f,0xd257240a82a007f553fa,0xd8e11191b558cae4fa1c,0x22324024d8c28446c608,0x4b3459213d2111065922,0x75009628633481092222,0x1cc3492046c70a48e164,0x891340810d8e108420f,0x218223e33451]]
def g175H8 := limbs80 #[#[0x7d8e6389a38b00131811,0x9e0000b2d6b37c660e70,0x9242240319ce696c185c,0x747e02d3a002903c32a7,0x61005bce8730800001f4,0x9064f45a04e24837c,0x9200004736020c000e30,0x1080000010fe89,0x668c0006140000061e00,0x59592e00000111b281,0x72c00281194b40]]
def g175D9 (j : Nat) := if j=0 then 0xa4188201bf else 0
def g175H9 := limbs80 #[#[0x10250002d001a42,0x20000000000000000000,0xbec00410000000718002,0x638000000005a,0x66648000000b4,0x640000000000178,0x7a80000000000000,0xb05cf0a0000000]]
def g175L : Nat → Packing
  | 5 => (7,4,5,0,0,6,0,g175D5)
  | 6 => (38,3,5,0,0,10,0,g175D6)
  | 7 => (34,2,5,0,0,11,0,g175D7)
  | 8 => (11,1,5,0,0,9,0,g175D8)
  | 9 => (1,0,5,0,0,0,0,g175D9)
  | _ => emptyPacking
def g175I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 17 4 8 3 1 g175H6
  | 7 => lookupWord 12 71 6 11 6 1 g175H7
  | 8 => lookupWord 13 73 5 11 6 1 g175H8
  | 9 => lookupWord 4 71 1 9 4 1 g175H9
  | _ => fun _ => none
def g175 : Forest := ⟨175,9,fun i => g175Y[i]?.getD (0,0),g175C,g175A,g175L,g175I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P5_0 : block g175 5 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B5 : block g175 5 0 7=true := g175P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P6_0 : block g175 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P6_1 : block g175 6 1 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P6_5 : block g175 6 5 33=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B6 : block g175 6 0 38=true := (@block_merge g175 6 0 1 37 g175P6_0 (@block_merge g175 6 1 4 33 g175P6_1 g175P6_5))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P7_0 : block g175 7 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P7_6 : block g175 7 6 17=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P7_23 : block g175 7 23 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B7 : block g175 7 0 34=true := (@block_merge g175 7 0 6 28 g175P7_0 (@block_merge g175 7 6 17 11 g175P7_6 g175P7_23))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P8_0 : block g175 8 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P8_2 : block g175 8 2 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B8 : block g175 8 0 11=true := (@block_merge g175 8 0 2 9 g175P8_0 g175P8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P9_0 : block g175 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B9 : block g175 9 0 1=true := g175P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175T : checkedTables g175 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g175 0 0 0 = true)
  · exact (rfl : block g175 1 0 0 = true)
  · exact (rfl : block g175 2 0 0 = true)
  · exact (rfl : block g175 3 0 0 = true)
  · exact (rfl : block g175 4 0 0 = true)
  · exact g175B5
  · exact g175B6
  · exact g175B7
  · exact g175B8
  · exact g175B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175G : graphValid g175 (boundsBefore K119) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low175 : Lower true (varsX 175) (graphGoal 175) 10 := lower_forest (g:=g175) (i:=0) (hints:=4146) (before_sound K119 V119) g175G g175T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K175 := extendKnown K119 10 [(175,[]),(187,[16,50,66,117]),(238,[96,81,64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V175 : Known true K175 := extend_ok (m:=175) V119 low175 (by decide +kernel)
def g183Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe007ff87ffffff98c2,0x903af000000fc0fc0fff])),(BitVec.ofNat 152 (word80 [0x4050051004001018c2,0x80006041041041041041]))),((BitVec.ofNat 152 (word80 [0xfff80007fe1ff83b0f,0x3485500003f03f000000])),(BitVec.ofNat 152 (word80 [0x806056202841213a0f,0x140551c71c71c71c71c7]))),((BitVec.ofNat 152 (word80 [0xfffffff8001fffd03d,0x79312000fc000003f03f])),(BitVec.ofNat 152 (word80 [0x48118013084400015,0x7931028a28a28a28a28a]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffe000462a,0x8b87903f00000003ffc0])),(BitVec.ofNat 152 (word80 [0x90260024009824628,0x2869514514514514514]))),((BitVec.ofNat 152 (word80 [0x4984,0x67ec8fc000003ffc0000])),(BitVec.ofNat 152 (word80 [0xe038043810e044100,0x63e88618618618618618]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x2651,0x42404fffffffc0000000])),(BitVec.ofNat 152 (word80 [0x100400040010000000,0x820820820820820]))),(0x0,0x0)]
def g183C : List ColumnInfo := [(1,0,182,0,8),(2,0,181,0,8),(32,0,151,0,8),(4,0,179,0,7),(16,0,167,0,7),(128,0,55,0,7),(20,0,163,0,5),(132,0,51,0,4),(144,0,39,0,4)]
def g183A : List (List Nat) := [[],[66]]
def g183D6 := limbs80 #[#[0xe5c5243e0374d5354932,0x5]]
def g183D7 := limbs80 #[#[0xf54d52bf59532fb54932,0x42a00ff58d52bfd8d52d,0xc70187cb1570186ae8a5,0x481c5cb15308c82071b2,0x81c60d4c72c071]]
def g183H7 (j : Nat) := if j=0 then 0x7 else 0
def g183D8 := limbs80 #[#[0xa3946061a403faa5fd32,0x1e851ca301c]]
def g183H8 := limbs80 #[#[0x30000a8b400d100,0x82000000500000]]
def g183D9 (j : Nat) := if j=0 then 0x5432101bf else 0
def g183H9 (j : Nat) := if j=0 then 0x3500000000070002f else 0
def g183L : Nat → Packing
  | 6 => (1,3,4,0,0,0,0,g183D6)
  | 7 => (5,2,4,0,0,8,0,g183D7)
  | 8 => (2,1,4,0,0,6,0,g183D8)
  | 9 => (1,0,4,0,0,0,0,g183D9)
  | _ => emptyPacking
def g183I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 4 0 0 g183H7
  | 8 => lookupWord 1 17 0 8 3 1 g183H8
  | 9 => lookupWord 1 11 0 6 1 1 g183H9
  | _ => fun _ => none
def g183 : Forest := ⟨183,9,fun i => g183Y[i]?.getD (0,0),g183C,g183A,g183L,g183I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P6_0 : block g183 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B6 : block g183 6 0 1=true := g183P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P7_0 : block g183 7 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P7_4 : block g183 7 4 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B7 : block g183 7 0 5=true := (@block_merge g183 7 0 4 1 g183P7_0 g183P7_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P8_0 : block g183 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B8 : block g183 8 0 2=true := g183P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P9_0 : block g183 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B9 : block g183 9 0 1=true := g183P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183T : checkedTables g183 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g183 0 0 0 = true)
  · exact (rfl : block g183 1 0 0 = true)
  · exact (rfl : block g183 2 0 0 = true)
  · exact (rfl : block g183 3 0 0 = true)
  · exact (rfl : block g183 4 0 0 = true)
  · exact (rfl : block g183 5 0 0 = true)
  · exact g183B6
  · exact g183B7
  · exact g183B8
  · exact g183B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183G : graphValid g183 (boundsBefore K175) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low183 : Lower true (varsX 183) (graphGoal 183) 10 := lower_forest (g:=g183) (i:=0) (hints:=82) (before_sound K175 V175) g183G g183T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K183 := extendKnown K175 10 [(183,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V183 : Known true K183 := extend_ok (m:=183) V175 low183 (by decide +kernel)
def g189Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffc1fffff62ae,0xb00d1a00000fc0fc0fff])),(BitVec.ofNat 152 (word80 [0x48010048400040220a,0x30010201041041041041]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfc007fffe0ffff2d40,0x86caf28003f00003f03f])),(BitVec.ofNat 152 (word80 [0x104a08900210800500,0x84cad00a28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0xffff800000ffe0bd86,0xb97040c000003f000000])),(BitVec.ofNat 152 (word80 [0x620c42e08485022c86,0xb97040e79e79e79e79e7]))),((BitVec.ofNat 152 (word80 [0xffffffffff0000804d,0x6156a9c0fc000003ffc0])),(BitVec.ofNat 152 (word80 [0x809013000026048045,0x1142994514514514514]))),((BitVec.ofNat 152 (word80 [0x9171,0x18b1dc3f00003ffc0000])),(BitVec.ofNat 152 (word80 [0xe01c010838089161,0x809c18618618618618]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x300600210c0104890,0x4a000060820820820820]))),(0x0,0x0)]
def g189C : List ColumnInfo := [(0,8,149,32,8),(8,0,181,0,8),(1,0,188,0,7),(4,0,185,0,7),(16,0,173,0,7),(32,8,149,0,7),(128,0,61,0,7),(20,0,169,0,5),(5,0,184,0,4),(17,0,172,0,4),(132,0,57,0,4),(144,0,45,0,4)]
def g189A : List (List Nat) := [[],[66],[112],[112,66]]
def g189D5 := limbs80 #[#[0x4c530443b4595314c110,0x442f4615314c110ed365,0x5d5514c110f515354530,0x54110f51534c5504435c,0xe736354550442dc61531,0x5d9534435cdcd5154110,0xc03351cf71595108f781,0x80d49d221344c80d141,0x408402000000]]
def g189D6 := limbs80 #[#[0x3b8a8aa0887d1314c110,0xfe2a29822137dcd6544,0x437db2a60886f9654c11,0x10fe6e2a8221fc4c5504,0x4437cb1aa08877953541,0x510bf6e6a8221bed8d50,0x14437ab2a62887d5534c,0x4510beaea98a21bdd953,0x634427ebb2a6886f7635,0x595109faebb1a213fdd5,0x565442efb9aca885f771,0x359510db8e6b2a21bddc,0xcf654427fb9aca886df7,0x73585509fcec98aa13f5,0xe4b110027eb9ec2a85df,0xd64a54c22cfc7839194b,0xc822706803cdccd9662f,0xcadeabf59a9d1a813396,0x1710c8fac217882ea1c4,0x811008204000202071e0,0x204202101100e306b021,0x100802016c0f0040ac08,0xb8f00e98100180004040,0x18]]
def g189H6 := limbs80 #[#[0x2a0700000e0000b2000a,0x141000005,0x23600000b9800d9c000,0x44000000000000510000,0x6400419890000030f600,0x1c50000000114b41827]]
def g189D7 := limbs80 #[#[0xd4c510fe54110fe4c110,0xd8d10bf58d10fd54510f,0x8550bfd9510bf59510bf,0x510ff58d10ff54d10bfd,0x50ff58550ff4c550ff59,0x360a81f85a0c000ffd85,0x799bc679865d14a4b0fc,0x58d61892310b55231e16,0xd56886231d621c52310b,0x481492221b11f51ca203,0x810a2235848b51d4c76d,0x2c8093c748a6d46116d4,0x6088718a2145842481c3,0x885288522c704c71938,0x193c7]]
def g189H7 := limbs80 #[#[0xc0000060271040430860,0x386dc7813a0fc330fd1,0x4980000000092b230018,0xc3ba5084746000845,0x9160004b80000005462,0x1a9982b02000e100071,0x38c00000181ecb31a0,0xb06049000140003e6000,0x589c925e938ce4f5df22,0x430000000000045ba6c7,0xeac00b]]
def g189D8 := limbs80 #[#[0x479aa407f4c7faa1fd10,0x38d1a4cc2a8d145a8315,0x3b4655]]
def g189H8 := limbs80 #[#[0x149,0x0,0x529de0000000,0x84200000000000000000,0x57400204006180033,0x1240024023,0xc8800000000000000,0x2c7a8400e2c0000,0x38584400000000000000,0x183f6,0xd58001274d04800b2,0xf10000000,0xc13b200]]
def g189D9 (j : Nat) := if j=0 then 0x1643251bf else 0
def g189H9 := limbs80 #[#[0xe2002400000070,0xe100fc00002800]]
def g189L : Nat → Packing
  | 5 => (11,4,4,0,0,7,0,g189D5)
  | 6 => (30,3,4,0,0,9,0,g189D6)
  | 7 => (15,2,4,0,0,10,0,g189D7)
  | 8 => (3,1,4,0,0,7,0,g189D8)
  | 9 => (1,0,4,0,0,0,0,g189D9)
  | _ => emptyPacking
def g189I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 4 53 1 10 4 2 g189H6
  | 7 => lookupWord 11 71 5 11 5 2 g189H7
  | 8 => lookupWord 6 97 3 10 4 2 g189H8
  | 9 => lookupWord 1 17 0 8 2 2 g189H9
  | _ => fun _ => none
def g189 : Forest := ⟨189,9,fun i => g189Y[i]?.getD (0,0),g189C,g189A,g189L,g189I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P5_0 : block g189 5 0 11=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B5 : block g189 5 0 11=true := g189P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P6_0 : block g189 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P6_3 : block g189 6 3 27=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B6 : block g189 6 0 30=true := (@block_merge g189 6 0 3 27 g189P6_0 g189P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P7_0 : block g189 7 0 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P7_9 : block g189 7 9 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B7 : block g189 7 0 15=true := (@block_merge g189 7 0 9 6 g189P7_0 g189P7_9)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P8_0 : block g189 8 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B8 : block g189 8 0 3=true := g189P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P9_0 : block g189 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B9 : block g189 9 0 1=true := g189P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189T : checkedTables g189 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0 = true)
  · exact (rfl : block g189 1 0 0 = true)
  · exact (rfl : block g189 2 0 0 = true)
  · exact (rfl : block g189 3 0 0 = true)
  · exact (rfl : block g189 4 0 0 = true)
  · exact g189B5
  · exact g189B6
  · exact g189B7
  · exact g189B8
  · exact g189B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189G : graphValid g189 (boundsBefore K183) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low189 : Lower true (varsX 189) (graphGoal 189) 10 := lower_forest (g:=g189) (i:=0) (hints:=20482) (before_sound K183 V183) g189G g189T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K189 := extendKnown K183 10 [(189,[]),(207,[96,65,32,33,81]),(237,[100]),(249,[66,98])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V189 : Known true K189 := extend_ok (m:=189) V183 low189 (by decide +kernel)
def g190Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fffffc1ffff64acc,0x4aee8000007f01fc07f])),(BitVec.ofNat 152 (word80 [0x280280084044060884,0xce80a142850a14285]))),((BitVec.ofNat 152 (word80 [0xfc003ffffffe029c28,0x13d9d30003f800003f80])),(BitVec.ofNat 152 (word80 [0x304b04500208229c28,0x3c940264c993264c993]))),((BitVec.ofNat 152 (word80 [0xffffc0001ffffbf0cb,0xa1210b0000000fe0007f])),(BitVec.ofNat 152 (word80 [0x420c2160909009c04b,0x212103952a54a952a54a]))),((BitVec.ofNat 152 (word80 [0xffffffffe0000824f7,0x491ab201fc0000003f80])),(BitVec.ofNat 152 (word80 [0x8090098004e04820d6,0x4012b258b162c58b162c]))),((BitVec.ofNat 152 (word80 [0x93710,0xa28774fe00000fffc000])),(BitVec.ofNat 152 (word80 [0xe00e010700803710,0x82821060c183060c1830]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x4c917,0x7e4005fffffff0000000])),(BitVec.ofNat 152 (word80 [0x30030021801004001,0x3c000581020408102040]))),(0x0,0x0)]
def g190C : List ColumnInfo := [(8,0,182,0,8),(2,0,188,0,7),(4,0,186,0,7),(16,0,174,0,7),(32,0,158,0,7),(0,4,42,144,6),(0,8,148,34,6),(0,16,42,132,6),(128,0,62,0,6),(2,8,148,32,5),(4,16,42,128,5),(20,0,170,0,5),(32,8,148,2,5),(128,4,42,16,5),(128,16,42,4,5),(34,0,148,0,4),(34,8,148,0,4),(132,0,42,0,4),(132,16,42,0,4)]
def g190A : List (List Nat) := [[],[66],[81],[81,66]]
def g190D5 := limbs80 #[#[0xd8b5150333dcf6254540,0x1832edd370595408ed87,0x1004003]]
def g190D6 := limbs80 #[#[0x276baec4a07395454140,0xf76e8a8281ee5515050,0x377b12a2a06ef624c54,0x40bf2e1a8a8177dcd515,0x5027ebb6a2a06ef62d45,0x150bf6e0aa2a1bedc165,0xb0027fba2c1a8f7b7055,0xc632c1448c3f1c0c4441,0xf142207803c687401e4d,0x68811004238040306071,0x81a882040707002a30,0x201100780402060]]
def g190H6 (j : Nat) := if j=0 then 0xa011700 else 0
def g190D7 := limbs80 #[#[0xb54b50db54950bbd8940,0x58b51b7d8d51bb58b50d,0x9540fe54140bfd9110bb,0x150df55150fb54950bf5,0x51bf59350bfd9150dfd5,0xff54540ff4c540bf583,0xff59150ff55150ffd454,0x881198520a400ffd9150,0x1d066570555253f0d32a,0x70abdadba927b94a1b80,0xc63b10d202e3c5103411,0x843e01a2c11a3031a402,0x3c10468b2b1c210245c9,0xc160203478b80410143e,0x1b812411470d201870a0,0x1101878e13070241a38e,0x10840e386900f0070a0c,0x8a8a0c01614542131cac,0x2a2830100f1d1c180442,0x1040240402c02080624]]
def g190H7 := limbs80 #[#[0x3a02000000a800304c23,0x64d0e00001b,0x6d0901c57a6300f678a0,0x10dcc1146165485a900]]
def g190D8 := limbs80 #[#[0xf50fea87f503fa21ed52,0x685400ffa8ff547fa63f,0x2238d4069c439c8c0481,0x389020408a8c180d1e30,0x92388e04d80720714182,0xa40a180b34610e060345,0x12a38022079038458121,0x92]]
def g190H8 := limbs80 #[#[0x21fe0448012b410020,0xec40034b000002c18,0x550684193001c31ca385,0x3ba3800900a24003b028,0x7c9a05a100018bb146,0x72200306e0680fd38]]
def g190D9 (j : Nat) := if j=0 then 0x41882017f else 0
def g190H9 := limbs80 #[#[0xc000000001cc00000020,0x8000000278008a00003c,0x8c016200001dc0034,0x67000000000000000000,0xe2005c8000000ca00000,0x2100001880000581]]
def g190L : Nat → Packing
  | 5 => (3,4,5,0,0,4,0,g190D5)
  | 6 => (14,3,5,0,0,9,0,g190D6)
  | 7 => (21,2,5,0,0,10,0,g190D7)
  | 8 => (8,1,5,0,0,9,0,g190D8)
  | 9 => (1,0,5,0,0,0,0,g190D9)
  | _ => emptyPacking
def g190I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 5 0 6 2 0 g190H6
  | 7 => lookupWord 5 29 5 10 4 2 g190H7
  | 8 => lookupWord 7 41 4 11 5 2 g190H8
  | 9 => lookupWord 3 59 2 9 3 2 g190H9
  | _ => fun _ => none
def g190 : Forest := ⟨190,9,fun i => g190Y[i]?.getD (0,0),g190C,g190A,g190L,g190I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190P5_0 : block g190 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g190B5 : block g190 5 0 3=true := g190P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190P6_0 : block g190 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190P6_2 : block g190 6 2 12=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g190B6 : block g190 6 0 14=true := (@block_merge g190 6 0 2 12 g190P6_0 g190P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190P7_0 : block g190 7 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190P7_6 : block g190 7 6 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190P7_15 : block g190 7 15 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g190B7 : block g190 7 0 21=true := (@block_merge g190 7 0 6 15 g190P7_0 (@block_merge g190 7 6 9 6 g190P7_6 g190P7_15))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190P8_0 : block g190 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190P8_1 : block g190 8 1 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g190B8 : block g190 8 0 8=true := (@block_merge g190 8 0 1 7 g190P8_0 g190P8_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190P9_0 : block g190 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g190B9 : block g190 9 0 1=true := g190P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190T : checkedTables g190 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g190 0 0 0 = true)
  · exact (rfl : block g190 1 0 0 = true)
  · exact (rfl : block g190 2 0 0 = true)
  · exact (rfl : block g190 3 0 0 = true)
  · exact (rfl : block g190 4 0 0 = true)
  · exact g190B5
  · exact g190B6
  · exact g190B7
  · exact g190B8
  · exact g190B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190G : graphValid g190 (boundsBefore K189) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low190 : Lower true (varsX 190) (graphGoal 190) 10 := lower_forest (g:=g190) (i:=0) (hints:=269620272) (before_sound K189 V189) g190G g190T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K190 := extendKnown K189 10 [(190,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V190 : Known true K190 := extend_ok (m:=190) V189 low190 (by decide +kernel)
def g215Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf87ffe01ff8fffffe4,0x13c7300000f8000f83ff])),(BitVec.ofNat 152 (word80 [0x110014140520200420,0x11c13084210842108421]))),((BitVec.ofNat 152 (word80 [0xff87fffe000ff1fe09,0x4badd0001f0001f00000])),(BitVec.ofNat 152 (word80 [0xa01158185641444889,0x4badd39ce739ce739ce7]))),((BitVec.ofNat 152 (word80 [0x7fffffff001ffc7,0xaa986003e0003e007c1f])),(BitVec.ofNat 152 (word80 [0xc22060201801881007,0x82184108421084210842]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fffffffffe0012,0x6c4f807c0007c0007fe0])),(BitVec.ofNat 152 (word80 [0x44180406002006110,0x6c068210842108421084]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff800000000000029,0x84009f800007ffff8000])),(BitVec.ofNat 152 (word80 [0x200808004008000,0x421084210842108]))),((BitVec.ofNat 152 (word80 [0x10,0x51304ffffff800000000])),(BitVec.ofNat 152 (word80 [0x401010008010000,0x842108421084210]))),(0x0,0x0)]
def g215C : List ColumnInfo := [(2,0,213,0,10)]
def g215A : List (List Nat) := [[],[118],[66],[66,118],[32],[32,118],[32,64],[32,64,118],[64,32],[64,32,118],[64],[64,118]]
def g215D10 (j : Nat) := if j=0 then 0x7f else 0
def g215L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g215D10)
  | _ => emptyPacking
def g215I (_ _ : Nat) : Option (Nat × Nat) := none
def g215 : Forest := ⟨215,10,fun i => g215Y[i]?.getD (0,0),g215C,g215A,g215L,g215I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P10_0 : block g215 10 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B10 : block g215 10 0 1=true := g215P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215T : checkedTables g215 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g215 0 0 0 = true)
  · exact (rfl : block g215 1 0 0 = true)
  · exact (rfl : block g215 2 0 0 = true)
  · exact (rfl : block g215 3 0 0 = true)
  · exact (rfl : block g215 4 0 0 = true)
  · exact (rfl : block g215 5 0 0 = true)
  · exact (rfl : block g215 6 0 0 = true)
  · exact (rfl : block g215 7 0 0 = true)
  · exact (rfl : block g215 8 0 0 = true)
  · exact (rfl : block g215 9 0 0 = true)
  · exact g215B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215G : graphValid g215 (boundsBefore K190) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low215 : Lower true (varsX 215) (graphGoal 215) 11 := lower_forest (g:=g215) (i:=0) (hints:=98) (before_sound K190 V190) g215G g215T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K215 := extendKnown K190 11 [(245,[32,81,64,49,96])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V215 : Known true K215 := extend_ok (m:=215) V190 low215 (by decide +kernel)
def g231Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffc01ffffe1fffffa,0x8241b1000007c00f83ff])),(BitVec.ofNat 152 (word80 [0x28140500440020da,0x2011004210842108421]))),((BitVec.ofNat 152 (word80 [0x1ffffe007ffe1ff05d,0x2ccb088000f801f07c00])),(BitVec.ofNat 152 (word80 [0x40b018160280404259,0xc4b080c6318c6318c63]))),((BitVec.ofNat 152 (word80 [0x1fffffff80001fff20,0xf4695e001f003e00001f])),(BitVec.ofNat 152 (word80 [0x82c020180b08828020,0xe4684a18c6318c6318c6]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffffffffe00010,0xab846f83e00000007fe0])),(BitVec.ofNat 152 (word80 [0xb0140a02c000b0400,0xa18467b18c6318c6318c]))),((BitVec.ofNat 152 (word80 [0xe0000000000000000e,0x11ba877c00003fff8000])),(BitVec.ofNat 152 (word80 [0xc0180c030110c0804,0x11908521084210842108]))),((BitVec.ofNat 152 (word80 [0xc1,0x4514407fffffc0000000])),(BitVec.ofNat 152 (word80 [0x100201004000100000,0x42108421084210]))),(0x0,0x0)]
def g231C : List ColumnInfo := [(2,0,229,0,8),(32,0,199,0,8),(1,0,230,0,7),(34,0,197,0,7),(64,0,167,0,7),(4,0,227,0,6),(128,0,103,0,6),(3,0,228,0,5),(5,0,226,0,5),(6,0,225,0,5),(33,0,198,0,5),(65,0,166,0,5),(66,0,165,0,5),(68,0,163,0,5),(96,0,135,0,5),(130,0,101,0,5),(160,0,71,0,5),(35,0,196,0,4),(69,0,162,0,4),(98,0,133,0,4),(129,0,102,0,4),(192,0,39,0,4)]
def g231A : List (List Nat) := [[],[96,81]]
def g231D4 := limbs80 #[#[0xa0221393985954350110,0x7550d40442b232f32a86,0x89caac8a1aa088760e49,0x822171194a154354110b,0x750d50442b2728c3a86a,0x81c6564cb0c05646528,0x5282000014a094a]]
def g231D5 := limbs80 #[#[0x50d50443645d54350110,0x442f8e0965c8110f1154,0x60a65c8110bd38359720,0x501109f18799720442f8,0xf926550d40443e459543,0x55140443cc5955450110,0x442f4e0d6550110f3265,0x6126550110bb38459540,0x501109f18799540442ec,0xf61625495044378e0975,0x50d50442dce156254110,0x443e45914354110f9154,0x6154354110f917450d50,0x54110f528550d50443d4,0xdd28750d504437461d43,0x59150443cc5915454110,0x442f8e097454110b7385,0xe0d76549109f3805d952,0x549109b7845d95244275,0x9d7835db524427c60376,0x5c143443745d57050d10,0x44275e1d6550d10bd385,0x6126550d10bd18099543,0x55110e356559154442e5,0x9f3805d954442dc60265,0x5d95444279e097655110,0x4427c60376551109d783,0x61373595109d7835db54,0x782d1388436150780275,0xc5328a3d9d4de6931950,0xcca5914873d9bcc65ba,0x9bd5d2dd5facd4e9b47a],#[0x1b9d9eb74fa1cde571f8,0x10b8100000000240f3b9,0x822504000000480a1c48,0x40c43858204013408212,0x295001003043840b440,0x2000000400000001302,0x94100000000000005]]
def g231H5 := limbs80 #[#[0x28000000002d0cd,0x398000000000000,0x0,0x374000038,0x800036c00,0x1c4b00000019400]]
def g231D6 := limbs80 #[#[0x3f0a9640887914350110,0xf62a8a02217c5d72044,0x43b8a92a0885f1755011,0x10fa286a8221dcd49504,0x443b9aa2a08877154541,0x910be6e0a92217cdd150,0x4443e8b8286885f170d4,0x9510baee6b2a217c5c35,0x50503b4a92a0905f1709,0xc81109dee4b2a81ce551,0x540443f932e40887f165,0x254110fe4caa0221fc59,0xc950443f8b12a0887f15,0x6454110fe2a8a8221fc5,0xdc152443f8ba2a0887f1,0x57654910fcac4a9221fc,0xd5db52442fbbb2a4885f,0xf77558910deacab12217,0xf599543443eab2a86885,0x7f17055110faaeca1a21,0x1dd59554443dab22a888,0x85f57655110eeccaaa22,0x21dd59754442fbbb2a88,0x886f56559110beaedaa2,0xa217ddc965442fbbaac8,0xa885f77459510faee6b2,0x82417d5d265442fab94c,0xca907eb7054920fd2a4a,0xb2a81ee551505037db82,0x2a4a85fb7054950ddee4,0x260017bdc964543bdb8,0xe2303e86a0ae1101a826],#[0x80888fe1ce350628b213,0xca9822ee590ac9462664,0x9ea3b6730e09ba356680,0x246e8b10ea1241e810fa,0x1ea1140a764d697126a4,0xb3160ab6556a914ca925,0x182afe5eebc174ae25b6,0xb44432e8712131a626c3,0xf8448307e12d0c501f84,0x501f844841400e112101,0x211861c48307e1261210,0x12101f84984841407e11,0x1001210038448307e114,0x1210b8291e0c48526e,0x507e114123f0308326e1,0x6e1e01213801b844842,0x1c9420725610f1313082,0x625081c9020f07612410,0x60e0850208041c982432,0x83254208502c2030c072,0x830f21080242108249a0,0x24093cb8209020b09849,0x982142d0b0c4e0c44347,0xf04025210800f240830,0xf02083008224043c842,0x2040810f02210e3c842,0x414106042010504181,0x1810]]
def g231H6 := limbs80 #[#[0xa2000a200000010a5512,0x183800000000000002,0xc0fc280000000000000,0x5e422a96262580000000,0x8b800000000000000017,0x290001580,0xd580000029c00,0xe27ccc0003460000000,0xe280000000000000353f,0xab00000000000000001,0x10c00000147d3c00,0x316000308000000000,0xc480000071a001518000,0xa000000007420000032c,0x29dd51e3dca8000a,0x40f9400008229000d4a0,0x70c00000386800000000,0x739e480032600055000,0x1044000000040008480,0x5ce000e6dcc8000,0x2d5000000]]
def g231D7 := limbs80 #[#[0xc54110fc50110fcc8110,0x58452be58052f550d10f,0x4910fd54910dbd4a52bd,0x110fd55110fd58910fdd,0x10fd59510fd59110fdd5,0xfb54920fe54120fd995,0xbf59720fb54b20bf5952,0xf54950bf59540fe54140,0x55150bfd8950dfd4950d,0x4b50bfd9150dfd5150df,0x152bf59350bf58b50df5,0x50bf58352bf59652bfd8,0xff55150ff58950ff549,0xffd8152ff58152ff5915,0xc330550880be0d80d800,0x50f21bb3245a4a01171d,0x882ee598a8d40a5f47a8,0x41a7f0f59d33846c4ce5,0xca1139a6249b90117a1e,0x24187c2b43adb5669bd1,0x747242c0281c961143e1,0x218688130061a2044301,0xc00e9b092170061a204c,0x25307c24850f030a6242,0x78185312160074d8490a,0x520fc21c618983e12428,0x2984908952610e985809,0x294c1849098036124260,0x2130e08434429830c21a,0x490a54a61c0485298309,0x28484c18431210a06c18,0x31210a940d870121b0e0],#[0x1b092130e028484c380,0x830d8701210361c0484c,0xc04840d8700d102e1c04,0x503282020c1611410361,0x1065040454a08162422a,0xc15]]
def g231H7 := limbs80 #[#[0x955a9fd98001000d44a3,0x4003f300032200000000,0x4280033026,0x49c0000,0x1c6d4eabd000608,0xbfd000042000d1224000,0x880480000035f6540045,0x69400021b,0x0,0x1810000000000000000,0xa40002f8000000000000,0x3,0xd2761400000,0x2a199700,0xf9a00000000b680,0x0,0x34180012380000000000,0x5b7a0d650170a,0x39e000000000002190,0x8ca0005c000a58,0xa500000000000000,0xce000000000000000000,0x21d000000002189,0x2659800000000000079f,0xd5,0x72000000000000,0x6bbb4000000000000a20,0x7c885600000,0x183e9b10e000000cc00,0x2858000,0x127800000000,0xa8000000000000000000],#[0x3c3800a340015,0x2444980000031a001018,0x2ad00000000000]]
def g231D8 := limbs80 #[#[0xd50fea07fc83fa41f510,0xa5fe52fea97f14bfea1f,0x4d257210cc4212003fe,0x8214840070a1485a2482,0x861a18121060a180d146,0x81c28214861540868214,0x2051a181210408636084,0x218121841a180d]]
def g231H8 := limbs80 #[#[0xec71400008c20411a4,0x9882a080029b7b481410,0xac0000000001657c0d39,0xf512ba9d000999c54224,0xc002a190d43800189001,0xa5950940000000014032,0x938a1b1c000000000014,0xc4e0036e6c8838230006,0xd149310a528aa36493a4,0xc039772ce1d7380093,0x5300083eb8400388c460,0xf0600028c84b30512,0x58f402c4408]]
def g231D9 (j : Nat) := if j=0 then 0x2082013f else 0
def g231H9 := limbs80 #[#[0xc0000004a001f5280038,0x14153e4948000068,0x580000000000000000,0x22200007d10dc2,0x0,0x24a0000000000014800]]
def g231L : Nat → Packing
  | 4 => (7,5,5,0,0,6,0,g231D4)
  | 5 => (45,4,5,0,0,9,0,g231D5)
  | 6 => (63,3,5,0,0,11,0,g231D6)
  | 7 => (40,2,5,0,0,11,0,g231D7)
  | 8 => (10,1,5,0,0,9,0,g231D8)
  | 9 => (1,0,5,0,0,0,0,g231D9)
  | _ => emptyPacking
def g231I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 2 59 1 8 3 1 g231H5
  | 6 => lookupWord 14 149 2 11 6 1 g231H6
  | 7 => lookupWord 18 271 2 11 6 1 g231H7
  | 8 => lookupWord 15 83 6 11 6 1 g231H8
  | 9 => lookupWord 3 59 2 9 4 1 g231H9
  | _ => fun _ => none
def g231 : Forest := ⟨231,9,fun i => g231Y[i]?.getD (0,0),g231C,g231A,g231L,g231I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P4_0 : block g231 4 0 7=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B4 : block g231 4 0 7=true := g231P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P5_0 : block g231 5 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P5_2 : block g231 5 2 43=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B5 : block g231 5 0 45=true := (@block_merge g231 5 0 2 43 g231P5_0 g231P5_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P6_0 : block g231 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P6_1 : block g231 6 1 19=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P6_20 : block g231 6 20 43=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B6 : block g231 6 0 63=true := (@block_merge g231 6 0 1 62 g231P6_0 (@block_merge g231 6 1 19 43 g231P6_1 g231P6_20))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P7_0 : block g231 7 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P7_7 : block g231 7 7 27=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P7_34 : block g231 7 34 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B7 : block g231 7 0 40=true := (@block_merge g231 7 0 7 33 g231P7_0 (@block_merge g231 7 7 27 6 g231P7_7 g231P7_34))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P8_0 : block g231 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P8_1 : block g231 8 1 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B8 : block g231 8 0 10=true := (@block_merge g231 8 0 1 9 g231P8_0 g231P8_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P9_0 : block g231 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B9 : block g231 9 0 1=true := g231P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231T : checkedTables g231 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g231 0 0 0 = true)
  · exact (rfl : block g231 1 0 0 = true)
  · exact (rfl : block g231 2 0 0 = true)
  · exact (rfl : block g231 3 0 0 = true)
  · exact g231B4
  · exact g231B5
  · exact g231B6
  · exact g231B7
  · exact g231B8
  · exact g231B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231G : graphValid g231 (boundsBefore K215) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low231 : Lower true (varsX 231) (graphGoal 231) 10 := lower_forest (g:=g231) (i:=0) (hints:=82) (before_sound K215 V215) g231G g231T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K231 := extendKnown K215 10 [(231,[]),(243,[66,50])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V231 : Known true K231 := extend_ok (m:=231) V215 low231 (by decide +kernel)
def g235Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ff83ff83fff82cb,0xc960a8500007c1f003e0])),(BitVec.ofNat 152 (word80 [0xa8050809080010ac1,0x496000506318c6318c63]))),((BitVec.ofNat 152 (word80 [0xffc0003fffc1fffdd4,0x614114ac00f83e007c1f])),(BitVec.ofNat 152 (word80 [0x300610020040201c0,0x60410004210842108421]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffc00001fffc97,0x853647440000000f801f])),(BitVec.ofNat 152 (word80 [0x4c248024c109240017,0x85260742d6b5ad6b5ad6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffe000021,0x2e5c7a201f00000fffe0])),(BitVec.ofNat 152 (word80 [0x900900090000481020,0x187821084210842108]))),((BitVec.ofNat 152 (word80 [0x44,0x90bf89b3e0003ff00000])),(BitVec.ofNat 152 (word80 [0xe00e020e0210702004,0x809e88a18c6318c6318c]))),((BitVec.ofNat 152 (word80 [0x33a,0x528a034bffffc0000000])),(BitVec.ofNat 152 (word80 [0x300430042180401a,0x1200030a108421084210]))),(0x0,0x0)]
def g235C : List ColumnInfo := [(1,0,234,0,7),(2,0,233,0,7),(32,0,203,0,7),(64,0,171,0,7),(0,8,193,34,6),(8,0,227,0,6)]
def g235A : List (List Nat) := [[],[96,81]]
def g235D7 := limbs80 #[#[0x9156e2a45d03dca5ed52,0x4b8a]]
def g235D8 (j : Nat) := if j=0 then 0x2c6111bf else 0
def g235H8 (j : Nat) := if j=0 then 0x64 else 0
def g235L : Nat → Packing
  | 7 => (2,1,3,0,0,5,0,g235D7)
  | 8 => (1,0,3,0,0,0,0,g235D8)
  | _ => emptyPacking
def g235I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 2 0 5 1 0 g235H8
  | _ => fun _ => none
def g235 : Forest := ⟨235,8,fun i => g235Y[i]?.getD (0,0),g235C,g235A,g235L,g235I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_0 : block g235 7 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B7 : block g235 7 0 2=true := g235P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P8_0 : block g235 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B8 : block g235 8 0 1=true := g235P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235T : checkedTables g235 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g235 0 0 0 = true)
  · exact (rfl : block g235 1 0 0 = true)
  · exact (rfl : block g235 2 0 0 = true)
  · exact (rfl : block g235 3 0 0 = true)
  · exact (rfl : block g235 4 0 0 = true)
  · exact (rfl : block g235 5 0 0 = true)
  · exact (rfl : block g235 6 0 0 = true)
  · exact g235B7
  · exact g235B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235G : graphValid g235 (boundsBefore K231) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low235 : Lower true (varsX 235) (graphGoal 235) 9 := lower_forest (g:=g235) (i:=0) (hints:=4149) (before_sound K231 V231) g235G g235T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K235 := extendKnown K231 9 [(235,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V235 : Known true K235 := extend_ok (m:=235) V231 low235 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x8c636947e400000000,0xffc00003ff003ff003ff])),(BitVec.ofNat 152 (word80 [0x84434841a400501405,0x1405014050140501405]))),((BitVec.ofNat 152 (word80 [0x81e981d880000003ff,0xffc0000000ffc00])),(BitVec.ofNat 152 (word80 [0x80e101888001304c13,0x4c1304c1304c1304c13]))),((BitVec.ofNat 152 (word80 [0x1037109618800ffc00,0xffc00003ff])),(BitVec.ofNat 152 (word80 [0x102010960084a1284a,0x1284a1284a1284a1284a]))),((BitVec.ofNat 152 (word80 [0x64108cf04580000000,0x3ff0000000000ffc00])),(BitVec.ofNat 152 (word80 [0x24108c704492c4b12c,0x4b12c4b12c4b12c4b12c]))),((BitVec.ofNat 152 (word80 [0x2714d7088afff00000,0xfffff00000])),(BitVec.ofNat 152 (word80 [0x23148308080b02c0b0,0x2c0b02c0b02c0b02c0b0]))),((BitVec.ofNat 152 (word80 [0xf9881a2a3b00000000,0x3fffffff0000000000])),(BitVec.ofNat 152 (word80 [0x590812021b2c0b02c0,0xb02c0b02c0b02c0b02c0]))),((BitVec.ofNat 152 (word80 [0x12402621577fffffff,0xffc00000000000000000])),(BitVec.ofNat 152 (word80 [0x242053700c0300,0xc0300c0300c0300c0300]))),(0x0,0x0),(0x0,0x0)]
def g127C : List ColumnInfo := [(1,0,126,0,10),(2,0,125,0,10),(32,0,95,0,10),(64,0,63,0,10),(0,8,85,34,9),(4,0,123,0,9),(8,0,119,0,9),(16,0,111,0,9),(0,4,42,81,7),(36,0,91,0,7)]
def g127A : List (List Nat) := [[],[66],[96,81],[96,81,66]]
def g127D9 := limbs80 #[#[0x1f003af21aa5d750d52,0x8975b1cf01c9897531cf,0x9]]
def g127D10 := limbs80 #[#[0xff50bde43f750f7d52,0x701ad4121319c08ed497,0xc67020e68ca7018e48ca,0xb50f22]]
def g127H10 (j : Nat) := if j=0 then 0x270 else 0
def g127D11 (j : Nat) := if j=0 then 0xeac8246047f else 0
def g127H11 (j : Nat) := if j=0 then 0xab3004001000000 else 0
def g127L : Nat → Packing
  | 9 => (2,2,4,0,0,6,0,g127D9)
  | 10 => (4,1,4,0,0,7,0,g127D10)
  | 11 => (1,0,4,0,0,0,0,g127D11)
  | _ => emptyPacking
def g127I : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 1 2 0 5 1 0 g127H10
  | 11 => lookupWord 1 11 0 6 2 0 g127H11
  | _ => fun _ => none
def g127 : Forest := ⟨127,11,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_0 : block g127 9 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B9 : block g127 9 0 2=true := g127P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P10_0 : block g127 10 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P10_3 : block g127 10 3 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B10 : block g127 10 0 4=true := (@block_merge g127 10 0 3 1 g127P10_0 g127P10_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P11_0 : block g127 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B11 : block g127 11 0 1=true := g127P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127T : checkedTables g127 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g127 0 0 0 = true)
  · exact (rfl : block g127 1 0 0 = true)
  · exact (rfl : block g127 2 0 0 = true)
  · exact (rfl : block g127 3 0 0 = true)
  · exact (rfl : block g127 4 0 0 = true)
  · exact (rfl : block g127 5 0 0 = true)
  · exact (rfl : block g127 6 0 0 = true)
  · exact (rfl : block g127 7 0 0 = true)
  · exact (rfl : block g127 8 0 0 = true)
  · exact g127B9
  · exact g127B10
  · exact g127B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K235) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 12 := lower_forest (g:=g127) (i:=0) (hints:=4146) (before_sound K235 V235) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K235 12 [(127,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V127 : Known true K127 := extend_ok (m:=127) V235 low127 (by decide +kernel)
def g191Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1ff00003fe00,0xff803fe003482466337e])),(BitVec.ofNat 152 (word80 [0x28140a05028140a05,0x28140a001400420113a]))),((BitVec.ofNat 152 (word80 [0x3fe00007fc0000,0x7fc00044f0c1b84f9f])),(BitVec.ofNat 152 (word80 [0x984c26130984c2613,0x984c26040d040a80f0f]))),((BitVec.ofNat 152 (word80 [0x7fc00000000001ff,0x3fe4188319c18ce6])),(BitVec.ofNat 152 (word80 [0x25128944a25128944a,0x25128944088119c084c4]))),((BitVec.ofNat 152 (word80 [0xff8000000,0x7fc0099f041e01f0f9])),(BitVec.ofNat 152 (word80 [0x964b2592c964b2592c,0x964b25899f040c01f0f0]))),((BitVec.ofNat 152 (word80 [0xff80000000000001ff,0xff800011e007e001ff01])),(BitVec.ofNat 152 (word80 [0x582c160b0582c160b0,0x582c1610c006e0016a01]))),((BitVec.ofNat 152 (word80 [0xffffffe00,0x1e0007fffe0000])),(BitVec.ofNat 152 (word80 [0x6030180c06030180c0,0x603018160003b3540000]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffff000000000,0x1ffff800000000])),(BitVec.ofNat 152 (word80 [0x804020100804020100,0x80402009362800000000]))),(0x0,0x0)]
def g191C : List ColumnInfo := [(1,0,190,0,10),(2,0,189,0,10),(4,0,187,0,10),(8,0,183,0,10),(16,0,175,0,10),(32,0,159,0,10),(128,0,63,0,10),(0,8,149,34,9),(2,8,149,32,8),(9,0,182,0,8),(10,0,181,0,8),(32,8,149,2,8),(40,0,151,0,8),(0,2,21,168,7),(0,4,42,145,7),(0,16,42,133,7),(3,0,188,0,7),(5,0,186,0,7),(6,0,185,0,7),(12,0,179,0,7),(17,0,174,0,7),(18,0,173,0,7),(20,0,171,0,7),(24,0,167,0,7),(33,0,158,0,7),(34,0,149,0,7),(34,8,149,0,7),(36,0,155,0,7),(42,0,149,0,7),(48,0,143,0,7),(130,0,61,0,7),(132,0,59,0,7),(136,0,55,0,7),(144,0,47,0,7),(1,4,42,144,6),(1,8,148,34,6),(1,16,42,132,6),(4,16,42,129,6),(8,2,21,160,6),(16,4,42,129,6),(32,2,21,136,6),(128,2,21,40,6),(128,4,42,17,6),(128,8,21,34,6),(128,16,42,5,6),(129,0,62,0,6),(160,0,31,0,6),(3,8,148,32,5),(5,16,42,128,5),(11,0,180,0,5),(13,0,178,0,5),(17,4,42,128,5),(21,0,170,0,5),(22,0,169,0,5),(28,0,163,0,5),(40,2,21,128,5),(41,0,150,0,5),(129,4,42,16,5),(129,16,42,4,5),(132,16,42,1,5),(136,2,21,32,5),(138,0,53,0,5),(144,4,42,1,5),(148,0,43,0,5),(160,2,21,8,5),(29,0,162,0,4),(30,0,161,0,4),(35,0,148,0,4),(35,8,148,0,4),(37,0,154,0,4),(38,8,145,0,4),(43,0,148,0,4),(46,0,145,0,4),(50,8,133,0,4),(52,0,139,0,4),(133,0,42,0,4),(133,16,42,0,4),(134,0,57,0,4),(145,4,42,0,4),(149,0,42,0,4),(162,0,21,0,4),(162,8,21,0,4),(168,2,21,0,4)]
def g191A : List (List Nat) := [[],[66]]
def g191D6 := limbs80 #[#[0x3f88595425855150120,0xb01]]
def g191D7 := limbs80 #[#[0x61443479955977258110,0x977258510db458f90509,0xa59162e0142443475955,0x48378b935095150120ea,0x4250120fa258d4258540,0x4d6254560483e896558d,0x299fa45db8354520db2e,0x5d920b27e91975956348,0x94609605431ad9521382,0x5992e416558d50d8e597,0x960b96e8192595635436,0xe05525832e9626438154,0x64dcd6250951c9e59590,0xb36e81975956350bc8d,0x560443ea964589425411,0x6095158110f9c5954254,0x9c5978254560443e7165,0x483ea5645894254510f,0x55150120faa591624c54,0x5956154540483fa14258,0x83f29655095150120f9c,0x150120faa59162545404,0x15358940483ea9655096,0xea9645093158120faa59,0x8120fb85898154560483,0x254560483e7165605515,0x9855898158120faa5914,0x20faa5915350960483ae,0x8551482eeba161562581,0x560b7158150f99595425,0xf1e59782dc560543c796,0x61546e77a26416558551],#[0xc15015000b9de9192595,0x60bd1682643f06909c0f,0x4d264474870f91c83546,0x3d878ce41ad3185c4ae1,0x490d1d237444865021fb,0x75472854f89e5352614a,0x68350f0390440eb5558a,0x82d8203b0440c07a6598,0x3a0458be00b021013010,0xc0239a04c12809668130,0x860681ac0b801664404f,0xc2c12c203e041332682b,0x3068138330004c0400d,0x223fa08100303304008c,0x1332682f05484c8203c1,0xee0a08841820358220c,0x10b84d83b8204b150436,0x2e051104360ee0a08844,0x60299a0b6281c0de8318,0xf60c1d83a0259a0f8081,0x6142d8a04012aa025810,0x1120b60c1185f0209802,0x8404b0ac10130d040902,0x804c3c230e06e0a4382b,0x3]]
def g191H7 (j : Nat) := if j=0 then 0x50 else 0
set_option maxRecDepth 16000 in
def g191D8 := limbs80 #[#[0xb0aa0887d85492154110,0x21c797659550443ce2ca,0x955158110f70b1242b02,0x4439d2e4b12c08879c5,0xabb2caa8a21c79755956,0x2c28873558d7258510e3,0xc7575595614439aac7b9,0x42501208dfca30eb1221,0x83f14c6a1280907e258d,0xaa84a02417a995509404,0x9076a5d94250120bd5c,0x99650940483b56eca128,0x50120bd5cb284a02417a,0xd52c8b1280907ca55152,0xe2b0241ae98658940483,0x7aa5914258120e74b16,0x554960482dd32ca12c09,0x120b74cb2a4b0241e696,0x6e8b12c09073a5d16258,0xb0241aeb84589604839d,0x3a5d56258120b75ca2c4,0x89604839d6eab12c0907,0xe3cbaacab02416eb955,0xab1aa49072b5d9645092,0xa41cad7459162483c9ac,0x5d56558d20a6fcb2e8b1,0x654823df24c3ac890717,0xd642704bb2411bf9461d,0xac0a871e5977158150c,0x1e6962549605434f2cbc,0x77258150b3ccb2a4b02a,0x542cf724b2ac0a871e59],#[0xc82cab1aa1c5d6558f72,0xeab053765a83dc560f2d,0xd5635877048637f28c16,0x250521f92aa2a4a0a43c,0x7ccacaa92c290fa95916,0x2c6b0a43cd57458d6148,0x90f1d5d56558521e6bba,0x65e016154795ae8b22c4,0xc142d6ab1f02b82c3a75,0x5ac8b16e2a172b59162d,0x8b1285aad64e016250b9,0x72bdd56458942e56baac,0x61d6550b8baeab2ac6a1,0x52e2eb2ac7b82a51fb90,0xcbba2c6a978b59154589,0x2ac7e4f925956354b8ba,0xc5512154110b2fcab00b,0x550442fe72890aa0887d,0xbf9c92c2a8221f715258,0xa92a0885de6554254110,0x2177b9454950443ed2c4,0xd95254110ebcbb2a4a82,0x4436f30ca92a08875ed,0xccb2a4a8221b7b865495,0x2a0885dee595254110bb,0xb7b9561950442ef72ac3,0x4258110f78b12a2b0221,0x42df32ca12c0887ba589,0x2aa4b0221ee962549604,0x885be6595258110f3cb,0xb9458960443dd704b12c,0x58110e7cbaac4b02216f],#[0xdf72ab12c08873edd562,0xe4b0221cf965dc960442,0x85eee518258110afccae,0x50951443cf70ab2ac08,0x510bf9c8284b0a217f39,0xacaa92c2887b558d4258,0xb0a21cf565dc961443ce,0xfd6578258510afacaee4,0x1424437d2c5c0284884,0x9fccaf00a1221bd963e,0x8b1284884fe65b805091,0x2213fb9061542443d5ac,0x5d965549109fdc830ca1,0x724432fb0ab2ee48871f,0xfecc2cbb92218fd86597,0x8a809047f657825d9108,0x1fa94254540483f52849,0x96150120bedc9aa2a024,0x483db2c6b0a80907ea50,0xb1a84a0241fa95350940,0x80907ea5954250120fd4,0xe9624c560483db2cab1a,0x158120f74b12a2b0241e,0x3cf2caa8ac0905f6e4d5,0xa84b0241ee9626056048,0x907ba54d6258120f74b2,0x8558960483dd306b12c0,0x8120f74b2f04b0241ee9,0xf2caba2c0905fa657825,0xab0241cf965dd1604839,0x56fe51764c520f74c92c,0xdd14148337f0bba28290],#[0x20f3ab2ac2a8a415bd95,0x6b12a2906f3e0d42545,0x8a419dd74e0d5148379f,0x75db8354520cefba706a,0xd514833beedc1aa29067,0xadfca2eca8a413dd96e0,0xa92c2907b358d4258520,0x41cdd7458d61483cdaca,0xd56558520e6fba2c6b0a,0x3483d9acab1a849071f5,0xeb2ae8b1a415bf945d95,0xac6907375977458d20e6,0xcdd9759563483d9b24b2,0x8155120e6f4bacab1a41,0x82b7f28c3aca9066fdd3,0xb50eb2a414ff9661d654,0xc904fb657825d920a7ec,0xd64589424c2bdb2bc12e,0x581509fdc830ca1261ea,0xcf2ca90ac0a87ba58921,0xe2b02a1e79655c560543,0x879e5958158150e7cb16,0x5605605436f70ac0ac0a,0x150f3cb2f02b02a177b9,0x2caa12c0a87ba5894258,0xb02a16f99650960543cf,0xbae096258150f74b92c4,0xc960542df728b12c0a87,0xb7dcb2e4b02a1e79655,0xac12c0a85eee51825815,0x2a1e7965e0960543cf2c,0xe456558150f3cc8acab0],#[0x60543cf324b2ac0a879e,0x3ab2ac290aa1e7b92595,0x3a42a847fe5d8648550f,0x1e75655c5615426ff2ac,0x38258550e3eb2ee4b0aa,0x5423fb2fc12c2a84fe64,0xcab0eb0aa1e779159561,0x84a84df65787585509bf,0xfd97e05425426fb2bc0a,0x350950f56b22c4a12a11,0x27f720c3a84a87975956,0xac4a92a13f990e1d4254,0xa85dee417654950bb7c8,0x95e0562543af720bb2a4,0x89508fecbf02b12a137d,0x7f28c3ac4a84fee41875,0x6b92a13f990e1d625427,0x69fe19655c950f2eb2ac,0x595635431ff0cbb2e4a8,0x50f2fc92cab1aa1e5d92,0x20c12caa86de60b80595,0xb2a1b7b85e0176542ef7,0xfe55815d950ebdc2f00b,0x976542bf720c12eca855,0xd77c2ac490ac15bf9460,0xb8aa2b05bbe556248560,0xc1adf8358951583ceaca,0x456554560cefc1ee4a8a,0x1582b7f28b92e2b079de,0xfc2acab8ac1c7f755957,0xaa4b047f6568750960d3,0xaed62e05525827f321c0],#[0x8154960d3eb2f02a92c1,0x823fb2fc0aa4b04bf65b,0x8ee4b12c1e7b90595525,0x4b05bb6577258960b76c,0xf845cd72582df720baac,0x5c960d5eb2f08b92c19b,0x5f305c02cab066f5d784,0xb2ac16f992e0165583,0x5bee418259560f3dbaf,0x558770486cfb23baacab,0x121af7caac5b8243cf56,0xacbc02c290c7fe5586dc,0xb0a439f775e01614875e,0x3d5977458521f3ab2aa8,0x9162487d5ac8aa2c490f,0x18ffc830dbaa43cef755,0xaa12c2a8fab591625093,0xaa3e759059561547ceac,0xdcf8050951f3ac92cab0,0x42547b9ee6b1284a8e77,0xeec36e6a12a3ead64589,0x9a84a8e77e1b7350951c,0x39df73e0162546bbb2db,0x37358951e6eb26e6b12a,0x546eeb21c0acaa8e77e1,0xb1f04b82c35f590e0576,0xe0b0f1f59552dc161d6e,0xdd63e01425863ff2ac16,0x54961d3ec2acaa12c3a,0x74facbc22a4b0e9f5978,0xf00b92c3e77915955258,0xb0eb7e11635c961d6eb1],#[0x90e0565586cff2ac02ca,0xd561b7ac9702b2ac36f5,0xbacab1ee0a14fd643815,0x6b12855fb905977050b9,0x73765d6558d42f56b22a,0x61d6550b9bd2eb2ac6a1,0x42a7fcb30eb2a855fb90,0x21c0aeaa153f65a87595,0x8aa59ed626037154a3fb,0xfe5980dc552cbeb2b01b,0x56254b9dac8b16e2a947,0xf2ec82cab1aa53ed90e0,0xb2ac6a9797e416558d52,0xa5e5f945956354bcbb28,0x57825c1628fec8702bb2,0x558e3ff20c0eeab14fb6,0xfc1300b2ac7add826016,0x2cab1db7e498059563d6,0xadd82e016558fcbf2ac0,0x8259563b6ec9700b2ac7,0x8f5bb08c12cab1db7e41,0xa304b2ac7adf84609655,0xab1db76438259563b6fc,0x14258550442dbb29c12c,0x54110ff4b1284a8221ff,0xbf6eca12a0887de59542,0xa4a8221f798454950443,0x87be5916254110fbcc32,0x254560442ff724c32a08,0x110ff8c12a2b0221ff14,0x2caa12c0887fce095158,0xb0221ef98558960443df],#[0xbe5978258110f7cb2b04,0x951442ff32bc12c0887,0xfbab2a84a8a21fe5625,0x8b12a28877ddd9425451,0x241fe9624c540483deac,0x5895150120ff8b0aa2a0,0x40483ef2caa8a80907fa,0xf4a9ac4a0241ef965585,0x8ac0907fa5093158120f,0x1ff18154560483df2c89,0x15158120ff4a12a2b024,0x483df2cac0ac0907be59,0xa9a84b0241bf98560560,0xc0907be5915358120ff4,0xfb9159560483df322b2a,0x24c520bfdc8b0ab0241e,0x3ddac8b1262907eb5914,0x2c2a8a417ef925d93148,0x907eb5914254520ff2a1,0x6458951483edacaa12a2,0x4520fbbc8acaa8a41eed,0xdacaa12c2905fbe49765,0x6a12417f79161561483d,0x7db6456554920fd6b22a,0x54d62483edf22b2aa490,0x50bf7c92eca9a41eed64,0x5b8ac0a877e60b71581,0xaa1ef96260560543bf7,0xfe457654950f3eb2a84b,0x551583ddac4a1262b05d,0xf76b1284a8ac1ef5625c,0xb92a2b079f5954254560],#[0xc1e7d65dc951583cfaca,0x4d6250960e7ebaac4b8a,0x2583cfb22b2aa4b07bb5,0xfc8aeab12c1e7f915955,0xa84a8dfbe498058931b7,0x7ef9260162547eef22b2,0x8259551bbfc9300b2aa3,0x86fef22baa84b0ddfe51,0xa2caa92c3e7d90595525,0xab0dbfe498059561f3ec,0xd756056550adff28c12c,0x59552ebebaf02b2a85d7,0x7daa7c12e0b15df64381,0xe029c045804e00380003,0xde036e066c0af011601d,0x17702b104fe090811301,0x610241eb839a06d00c80,0x400a061318255046d087,0x32d86290bd816bc2b905,0x1d8039706fc0d941a60,0x8c10b420cc40607cf0f5,0x4bd8949122e236845408,0x229d45218a1c13d426e0,0x2816182bc05648aad152,0x5f58ba316f82d805a20b,0x8333c6490c551872301c,0xda1b5035d86ad0d3e1a1,0x7490e601c7238486fb0d,0x3e307b28f281dec3ae4,0x6b209e40a08008fe51f5,0x8b291492218436884e90,0xa48f890611da23504604],#[0x1225ec4ae494e928124c,0x9f593c427504d8099c93,0x85234a38945528725048,0x982ae25554a8c14fc296,0xb4916342c04576cada15,0xa5eb4bbd97492e445b68,0x5231fe6308c3798272fe,0xd3c1a3b34126730ccd19,0x86e20d9a9b0335a26aa8,0xca390470e8dee1bc0374,0xf191ddf3b5a7568e941c,0x7c84f7d1ed33d587a14,0x213fc87ef4fcb1f7a3e9,0x77a0c8412c81e9029a0,0xa86450baa14e427a84b1,0xd3456e896510e21d4435,0x1d0a38546a68cdd182a2,0xc92f124aa43748368fa5,0x404bc496952b4252049d,0x38ca6dc4d809a6533ea6,0x29fc93e5a78e4ece9d2d,0xe75180a239428a835503,0x4d5298e52b8a4d548728,0xaa0d5232a1f53daa719,0xc55710ad855922adc558,0x65a2c8258a0b04d5f62b,0xb6b96b8ad3459d8b341,0xe55d7cba057222e285bc,0x7be2f605e72bc75780ae,0xcc0d18012fe65f94be8d,0x296204c315854b08260c,0x8eb31ba6326c5b18a831],#[0x6ca9193eb2566448c7c9,0x1d67aace8d9adb31e659,0xac8355e6a16d365a3db4,0x6d9fdb31b63c6c14d761,0x5e6e6edc6db74b6c26d3,0xc1637fa6fbcdf09bcdb7,0xee415c6438ac710ae14d,0x1073e8e6ddcc8395e726,0xd643aac750ae979d163a,0xeee2ddb7bb48762cebe9,0x8078b2f0c9e05bbce774,0xeacbd3279eaf30de4e3c,0x6f871efabdc37b38f601,0x1c7deafb0df48be5f7c8,0x163fef7f90fe59facbf,0x704f207a40c2812101a6,0xfa83a7070a0d3419582c,0x13dc254848708ca11641,0x10c4a18642e585670a32,0xaf873d0e0a1b8c34a863,0x228c42a88070f9e1e5c3,0xf13a226bc4b0891311b6,0x9b8ae9153629e452b8a1,0x329c6218c2117a62e6c5,0x11cde38846de8d4319be,0xf58f9d1eca3cb477a8e9,0x467489c90d5210e40e47,0x326464b5493892392402,0x7824301484088138293b,0xc1784e03e0a0c05217c2,0xb0646bc27820a4305209,0x3c1052180304009c1810],#[0x6b80052141602a00de1,0x3e088184e0a41784f05,0x1602af09e0b80052180f,0x707009cd04c141b83908,0x8260b00820b9c098204f,0x9cd04f11c2c02000e6,0x9e013c2f83f02130670b,0xc084c17c2f8108213040,0x17c0841098204ff0be0f,0x81098240233409c2609e,0x2785f07e04260be17c1f,0xbe0fc084c142004c0b4,0x409fe17c1f81098284ff,0x2cd04e1420783334138,0xfe17c1f810982840b0a0,0x609e17c1927f02130509,0x7c1f810982f85f07e042,0xc1014b85734138424fe1,0x3857341304052e15cd04,0x21306081e0ccd04e1020,0x134138309e013c2f83f0,0x309fe17c1f81098282e,0xc100309a09c182ad344d,0x2c4d341302f0be0fc084,0x3e13c105217c2f83f021,0x7080682704c0a4202c07,0xa0c51a09c2f838314682,0xe10207836341384f0760,0x1f07c110302214a8d04,0x40e42205e13c11180a22,0x9c26061382305a68258,0x30208013820781302804],#[0x30a2138209c11820a41,0xe13c15800a2300608013,0x842098204c0a4103a073,0x7e04260a100278405bc2,0x70b009cd04c141ff85f0,0x4052e160139a09e2829,0x60b4d04c080370213413,0x3044054681384c102704,0x4c082884e0810d844341,0xc0290611c1984c0c290,0x8520c0d21809c1484030,0xc582020868260a06019,0x834130561b0620d04e11,0x828300dc2706041c2418,0x62c17010a4138508813,0x3838300cc29061102704,0x1a0982044098141808c1,0x1a00a34e08290a1000c2,0x213c5f07c042784c12c,0x2704148270408bc1810e,0xe0213040201482706148,0x84f07c041984c1043783,0x609080520e0003bb0414,0x10270414827041482605,0x520b08708f07c04258a1,0x10826068402161a0c260,0x3d60a8004f4341306420,0x8184007c110309c14824,0x6040c4198510c0f03e08,0x6c682604c6826041082,0x27f83e34130617e10826,0xe341305a341302105c04],#[0x8220614827042ffc1f01,0xc07c110307c11024060f,0x6c5842118e31a09c1d1,0x38002621460566883141,0xc0062f427021ace10e08,0x2b0360ecd04c1b0a611,0xe682089808cd04c0c27a,0xd009c339a0822402718,0x2608e160104ff06e6826,0xb00587b38360207c668,0x13814a11b343d8a40cc,0xc01c08cce8616c183bc0,0x83c000b81cf023343e11,0xa00b060e6cd04c1a185,0x18e68509fe0dc284c12c,0xea04e68260901a816007,0x304a04e0c1cb9a098290,0x8e150c04c0fc1c0070a1,0x183e0982783080e14260,0xf840b35e0c270ee17c,0x25341302d15a682b0a80,0x7820702e002688534138,0x4a2f805841b1860ee082,0xa05c014cd861a8b511a0,0x6709c0b80499228fd11,0x2786932c44462cc5188b,0xd88f02e00e19824991dc,0x1323b0470d2658888c7,0x69a1c15826e09c09c370,0x260609c07e83e05c02c3,0x9818401341383a08a68,0x827060b24d04e0c27c9a],#[0xa0827e04334130403c26,0x68270613d4d04c0f4669,0x8c000f82e9341385058a,0x549a0981b04099268270,0xbe0f4d04c124d04c081,0xc1e850982f8307c1143d,0xd0410c2602130121a41f,0x74682704c278d0421b8,0xc111a080110603014827,0x390004c7041485f0960f,0xde13c104e23413029104,0xc8440a42044098101013,0x981028b0646826080901,0x26056090584f098204f0,0x8f0be38860270c13c,0x330981086e0a14826081,0xdc11f062198d01809c40,0xa12c402306027061000,0x6b08c2c1c84c130c70be,0x44510d6080c052634130,0x4840288a42dc1e000801,0x40014a8d04e202704c23,0x8209c1445036e0bc189f,0xcc26861382904844433,0x78208011050661482c34,0xc101e0800f82208067c2,0x51170e0330a21e1a09,0xc478220a4183a07221b8,0x29040d0290423c110510,0x104170309fc68260a0d0,0x180941303d0413c8d04c,0x601b84e0c4680b09e19],#[0x18d0413840301442706,0x4e0c1b84c08260520820,0x1d18f07c682608234058,0x2221827044144680b098,0x203742fc184e08a2a1bc,0x7dc13008341386d04138,0x6c444338209c144505c2,0xc040c161385830138288,0xa21303030144260606d0,0x42484890c5810a428180,0xf8d04c1094218b04138,0x8608013020a41382c31e,0xc00503de13c170013414,0x1c194c8b47e83582533,0x610ba0f8005112c1784e,0x302c3d84340e83d1612c,0xa8900f039e0014850a41,0x4e0f41026011c001d8,0x4138290414827041142,0x2138208a138290613820,0x2852098181e0a413030a,0x84b1025d9a082884e09c,0x8c38371012c4717e0dc2,0x60407c2884e0c2884e09,0xc0ff83081a14270a1442,0x223c13823060782904c0,0xa41b1a0661343080130,0x2904c0909052080f04e,0xfa341384058878270461,0xdc2686100270420d0910,0x824343886e16108309c0,0x51140f580b08100165],#[0x1c10400a23384704e002,0x21ac030b86a2601708e0,0x1127e4b482633a12c30d,0xee060594204c14320b8d,0xa96d09a0940386a32440,0x23a8070d42d1a88a854f,0x1015826d01a11c368223,0x19709a0869096018cc9f,0x2780a32a7c4542a7d435,0x341443e070690c05111c,0xa185109c105209c141c8,0x608c681c8420d8d03309,0x9c184609c168203c4682,0xb20de134105116c20460,0x8260520a4004e0a4183,0x437000b01c8511026052,0x23c47026834201f09c14,0x685c2c1302c2c6682606,0xf268260881982602b196,0xd04c101549a09e1b0007,0x9e2f830941303d0be0f4,0x2060148221a41fc1e850,0xc22a1a09c1484066148,0x241e14827061381e045,0x108177028341384a3413,0x44305dc0a0d04e102705,0xa609810330a4130209c1,0xe0b0d04e142603709a18,0x4e0cc884e0a2182e300,0xc144205c8682606e0b0d,0x161a09c201f09c144309,0xc17182709868260a07ec],#[0x270986826066582884c0,0x722021098144309c144,0x4306a088c207069c1296,0x308c2582072121ab040e,0x280724480c09c041b83,0x2e08110660b008330602,0x58aa1ac1b82044a585e0,0x8116001108b84b06e082,0x20722a10b040e43b06e0,0x584b0413058200a580d8,0x80b4442160816860e508,0x81ba0f0298412c110d08,0x8342103741d82a008686,0xa0cc1029c0a2205b0508,0x3341d83070119a0ac503,0x4007c0ef0118112c1e02,0x6081030bc083b140d8a0,0x2f0207221270481043b0,0x4040000734088906040c,0x2845c082a0c4f18b7061,0x1d14168a0488e8a08148,0xa081911d06149a608111,0xc4d04892070410f41a9a,0x3054a068207a0c8885a0,0xa02683422089e134438,0x864441a1808281341383,0x2210e7050603422e1025,0x4076081c840790011b07,0x3cc024289a281c00e041,0xc1500844208e08212220,0x108fd84d07608258ba0e,0x8207226c3d0760822029],#[0xe082008b706144451809,0xc4ff0a0b0002909c082,0x8313fc0c8687c0f4111a,0xe1086f03c34190de0786,0x82a424100423c46b4108,0x20a82e020a9090401380,0x1f0203c2684e020b02e0,0x1dc0a0d0dc090309a0ec,0x107c46040b80c1122]]
def g191H8 := limbs80 #[#[0x1ebc70c400104090331b,0x648782fea092ee8d01f8,0xc250314421ed397522,0xf15e81c48,0x21080043558711627,0x4dcb0000aa001f2d9100,0x8a800807414000000004,0x69843fe530dd6755208c,0xed1ba3f922e6c2126683,0xc702d0210194c43b8135,0x21d2]]
set_option maxRecDepth 16000 in
def g191D9 := limbs80 #[#[0xfa94250120ed56358510,0x9bf845d920ee96258120,0xe5d6558d50e796558150,0xe756558551ed56358521,0xead64589429dd86dcd51,0xff12154110e5d6558d52,0xf795254110ff16154110,0xdf97654110f796554110,0xbf98654110dfb7654110,0xff12158110bfb8654110,0xff38158110ff15158110,0xdf97258110ef96258110,0xef96558110dfb7258110,0xdfb7558110df97558110,0xfe55248510bfb8558110,0xfd56348510fe56248510,0xdf57448510fd66348510,0xbf58448510df77448510,0xbf58548510bf78448510,0xdf57648510bf78548510,0xbf58648510df77648510,0xf756554510bf78648510,0xdf77654510df57654510,0xdf57258510bf58654510,0xbf78258510df77258510,0xdf57558510ef56558510,0xbf78558510df77558510,0x9fd8750910bfb8050910,0x9fd8754910ded7254910,0x9fd8758910ded7258910,0xdde635c910ddd635c910,0x9ff855c9109ff845c910],#[0xddd63dc9109ff865c910,0x9fd84dc910dde63dc910,0x9fd86dc9109fd85dc910,0xcfd7659510d7d7559510,0x9ff87595109fd8759510,0x9ff865d5109ff825d510,0x9fd86dd5109fd82dd510,0xdf7815d910bf7815d910,0x9ff855d9109ff825d910,0x9fd85dd9109fd82dd910,0xfe96250120fe95250120,0xfda6350120fd96350120,0xdfb7650120df97650120,0xfe94258120dfb7158120,0xfeb8258120fe95258120,0xdf97458120ef96458120,0xbfb8458120dfb7458120,0xdf97558120ef96558120,0xdbf7450520dfb7558120,0xedd6358520bdf8354520,0xded62dc520ded52dc520,0xdde63dc520ddd63dc520,0x9fd85dc5209fd84dc520,0xfcd63509209fd86dc520,0xfad6450920fce6350920,0xbef8550920bed8550920,0xdef7650920ded7650920,0xbef8650920bed8650920,0xfce6354920fcd6354920,0xbef8454920f6d5454920,0xded7654920f6d6554920,0xbed8654920def7654920],#[0xeed6458920bef8654920,0xdef7458920ded7458920,0xded7558920bef8458920,0xbef8558920def7558920,0xddf7458d20ddd7458d20,0xddd7558d20edd6558d20,0xddd7498d20ddf7558d20,0xddd7598d20ddf7498d20,0xdbf7455120ddf7598d20,0x9fd8755120d7d7555120,0x9fd8759120cfd7659120,0x9ff855d1209ff815d120,0x9fd81dd1209ff865d120,0x9fd86dd1209fd85dd120,0x9fd8759520d7d7559520,0x9ff815d5209ff8759520,0x9ff865d5209ff845d520,0x9fd84dd5209fd81dd520,0xbef825d9209fd86dd520,0x9ff815d920bbf845d920,0xdbc845d920def825d920,0x9ff845d920dbf845d920,0x9fd81dd9209ff855d920,0x9fd85dd9209fd84dd920,0xbfb8158150dfb7158150,0xef96258150f795258150,0xf7b8558150dfb7258150,0xe7d6558550f6d5248550,0xd7d65dc5509fd82dc550,0xb7d85509509fd86dc550,0xf5d6354950f6d6254950,0xd7f7454950f5e6354950],#[0xd7d7654950b7f8454950,0xb7d8654950d7f7654950,0x9fd81dc950b7f8654950,0xdde63dc950ddd63dc950,0xd7d65dc9509fd84dc950,0xf7b80595509fd86dc950,0xbfb805d950b7f8259550,0xdfb805d950b7f855d950,0x9ff825d9509ff815d950,0x9fd81dd950d7f855d950,0xeed62485609fd82dd950,0xbdf83545609fe8748560,0x9fe8754560e7d6554560,0x9fd82dc560bdd83dc560,0xdde83dc560ddd83dc560,0x9fd85dc560cfd65dc560,0xafd8650960eed6250960,0xeed62549609fe8750960,0xafd8654960e7d6554960,0xeef72589609fe8754960,0xaff8458960cff7458960,0xbbf845c960aff8558960,0x9fd84dc9609fd81dc960,0xefb80595609fd85dc960,0xe7f7559560aff8259560,0x9fd81dd560bfb805d560,0xdf541dc1219fd82dd560,0xded52dc121df561dc121,0xddd63dc121ded62dc121,0x9fd84dc121dde63dc121,0x9fd86dc1219fd85dc121,0xfe56250521fe55250521],#[0xfd66350521fd56350521,0xdf77650521df57650521,0xfe55258521bf78058521,0xdf77458521df57458521,0xef56558521bf78458521,0xdf77558521df57558521,0xf6d6554921f6d5454921,0xdef7654921ded7654921,0xbef8654921bed8654921,0xded7458921eed6458921,0xded7558921def7458921,0xbef8558921def7558921,0xddf7458d21ddd7458d21,0xddf7498d21ddd7498d21,0x9fd8755121dbf7455121,0x9ff805d1219fd8759121,0x9ff865d1219ff855d121,0x9fd85dd1219fd80dd121,0xd7d75595219fd86dd121,0x9ff87595219fd8759521,0x9ff845d5219ff805d521,0x9fd80dd5219ff865d521,0x9fd86dd5219fd84dd521,0x9ff845d9219ff805d921,0x9fd80dd9219ff855d921,0x9fd85dd9219fd84dd921,0xddf7350951bf78058551,0xf778159551ddf7358951,0xdf7815d9519ff805d951,0xbf7815c1619ff825d951,0x9fd82dc161edd635c161,0x9fd85dc161cfd65dc161],#[0xe7d6554961edd6350961,0x9fd80dc961edd635c961,0x9fd85dc9619fd84dc961,0xbf7815d561ef78159561,0x9fd82dd5619fd80dd561,0x9fd86dc1329fd84dc132,0x9fd86dd1329fd80dd132,0x9fd84dd9329fd80dd932,0xded62dc1429fd81dc142,0xdde63dc142ddd63dc142,0x9fd86dc1429fd85dc142,0xded62dc5429fd80dc542,0xdde63dc542ddd63dc542,0x9fd86dc5429fd85dc542,0xded7558942bef8058942,0xedd6558d42def7558942,0xddf7558d42ddd7558d42,0xddf7598d42ddd7598d42,0x9fd8759542d7d7559542,0x9ff805d5429ff8759542,0x9ff865d5429ff815d542,0x9fd81dd5429fd80dd542,0x9ff805d9429fd86dd542,0x9ff855d9429ff815d942,0x9fd81dd9429fd80dd942,0x9fd81dc1529fd85dd942,0xddd63dc152ded62dc152,0xd7d54dc152dde63dc152,0xd7d65dc1529fd84dc152,0x9fd80dc5529fd86dc152,0x9fd84dc552ded62dc552,0x9fd86dc552d7d65dc552],#[0xbef8158952bef8058952,0xeed6458952f6d5458952,0xf5d5458d52def7458952,0xf5d5498d52ddf7458d52,0xd7d7655152ddf7498d52,0xbef8259152d7f7655152,0x9fd81dd1529fd80dd152,0x9fd86dd152d7d65dd152,0xf6f8259552b7f8059552,0xbef825d952b7f8459552,0x9ff815d9529ff805d952,0x9ff845d952def825d952,0x9fd81dd9529fd80dd952,0xbef825c1629fd84dd952,0x9fd81dc162bbf845c162,0x9fd84dc162cfd64dc162,0x9fd80dc5629fd85dc162,0x9fd85dc5629fd84dc562,0x9fd81dd1629fd80dd162,0xbef825d5629fd85dd162,0x9fd81dd5629fd80dd562,0x9fd82dc1639fd84dd562,0x9fd84dc9639fd80dc963,0xbdd80dc963bdd82dc163,0xedd8059563bdd84dc963,0xedd8259563edf8059563,0xb7f855c165edf8259563,0x9fd82dc1659fd81dc165,0x9fd82dc5659fd80dc565,0x9fd81dc9659fd80dc965,0xff942541109fd84dc965,0xff98254110ff96254110],#[0xff94258110ff98654110,0xff98258110ff95258110,0xff98558110ffb8258110,0xff55448510ffb8558110,0xff56254510ff54254510,0xff55258510ff54258510,0xfdd6350910fed6250910,0xdfd7550910fde6350910,0xbfd8550910dff7550910,0xdfd7650910bff8550910,0xbfd8650910dff7650910,0xfed6254910bff8650910,0xdfd7454910f7d5454910,0xbff8454910dff7454910,0xdfd7654910f7d6554910,0xbfd8654910dff7654910,0xefd6458910bff8654910,0xdfd7558910bff8458910,0xbff8558910dff7558910,0xdfd65dc910bff845c910,0xdff825d910bff825d910,0xff95150120ff93150120,0xff95350120ff96150120,0xff96550120ff96350120,0xff95158120ff93158120,0xff95358120ff98158120,0xff98558120ff98358120,0xfed624c520fed424c520,0xdff744c520dfd744c520,0xdff764c520dfd764c520,0xdfd7550520fed5250520,0xff56154520bff8550520],#[0xfed6254520fed4254520,0xdff7454520dfd7454520,0xdfd7654520f7d6554520,0xbfd8654520dff7654520,0xfed5258520fed4258520,0xdff7458520dfd7458520,0xdfd7558520efd6558520,0xbff8558520dff7558520,0xfed5350920bff855c520,0xfed6550920fed6350920,0xdfd7454d20fed5358920,0xdfd7654d20dff7454d20,0xdfd7458d20dff7654d20,0xbff8155120dff7458d20,0xdfd65dd120dfd655d120,0xfed8259520bff8159520,0xdfe8759520dfd8759520,0xdff815d520bff815d520,0xbfd8650930fed6250930,0xbff8458930efd6458930,0xff97158150ff92158150,0xffb8158150ff98158150,0xff97258150ff94258150,0xffb8258150ff98258150,0xff56148550ff54148550,0xf7d5448550fed6248550,0xbfd8448550dff7448550,0xf7d6548550bff8448550,0xdff7648550dfd7648550,0xbff8648550bfd8648550,0xbff8748550bfd8748550,0xf7d5258550ff57158550],#[0xbff8258550dff7258550,0xbff8758550bfd8758550,0xdfd725c550f7d525c550,0xdfd765c550f7d655c550,0xdfd62dc550dfd42dc550,0xfed6250950bff8150950,0xfde6350950fdd6350950,0xdfd7650950f7d6550950,0xbfd8650950dff7650950,0xbfd8750950bff8650950,0xf7d7454950bff8750950,0xbff8158950f7d7654950,0xefd6458950fed7258950,0xbfd8758950bff8458950,0xbff815c950bff8758950,0xfde635c950fdd635c950,0xbff845c950dfd745c950,0xdfd765c950f7d655c950,0xf7d8159550bff865c950,0xf7d8259550f7f8159550,0xffb805d950f7f8259550,0xbff825d950bff815d950,0xdfd815d950f7f855d950,0xdfd825d950dff815d950,0xefd6548560dff825d950,0xefd624c560bff8548560,0xff57154560dff724c560,0xdff7254560efd6254560,0xefd625c560bfd8754560,0xdff725c560dfd725c560,0xdfd755c560efd655c560,0xbff855c560dff755c560],#[0xdfd75dc560efd65dc560,0xefd6550960bfd85dc560,0xefd5358960bff8154960,0xefd7558960efd7358960,0xefd655c960dfd735c960,0xbfd81dc960dfd755c960,0xefd65dc960dfd73dc960,0xbfd85dc960dfd75dc960,0xdfd53dc960dfd81dc960,0xdfd85dc960dfd83dc960,0xeff8159560efd8159560,0xeff8259560efd8259560,0xbff815d560ffb805d560,0xdfd81dd560bfd81dd560,0xdfd65dc121dfd54dc121,0xfed5458921ff55458521,0xfbd6455121bff8055121,0xdfd7655121f7d6555121,0xbfd8655121dff7655121,0xdff7559121bff8655121,0xfed6250931dfd65dd121,0xbff8058931bfd8650931,0xbff8458931efd6458931,0xbff8050951ff54258551,0xf7d6550951fed6250951,0xbfd8650951dfd7650951,0xbff8058951bff8650951,0xbff8458951efd6458951,0xf7d8259551f7d8059551,0xdfd42dc161bff825c161,0xbff8050961dfd52dc161,0xdff7550961efd6550961],#[0xbff8550961bfd8550961,0xf7d5454961bff8054961,0xbff8454961dff7454961,0xbff845c961bff805c961,0xefd8259561efd8059561,0xdfd63dc142dfd53dc142,0xfed5358942dfd65dc142,0xdff7654d42dfd7654d42,0xfdf8058d42bff8058d42,0xbff8159542bff8059542,0xdfe8759542dfd8759542,0xdff815d542bff815d542,0xdfd64dc552bff815c152,0xf7d8059552bff815d152,0xf7d8159552f7f8059552,0xf7d8459552f7f8159552,0xbff815d952f7f8459552,0xdfd53dc162dff815d952,0xefd6454d62bff855c562,0xbff815d562dff7454d62,0xdff715c165dfd715c165,0xdff725c165dfd725c165,0xf7f855c165bff825c165,0xbfd82dc165dfd72dc165,0xdfd725c565dfd82dc165,0xdfd72dc565bfd80dc565,0xdfd80dc565bfd82dc565,0xbff805c965dfd82dc565,0xdff745c965dfd745c965,0xbfd80dc965bff845c965,0xffd6550910bfd84dc965,0xffd644c520ffd7550910],#[0xffd6454520ffd764c520,0xffd7654520ffd7454520,0xffd6454d20ffd8558520,0xffd8159520ffd7654d20,0xffd4258550fff8159520,0xffd724c560ffd424c560,0xffd4254560fff724c560,0xfff7254560ffd7254560,0xffd535c960ffd5350960,0xffd8058931ffd53dc960,0xffd8650951ffd8050951,0xffd8458951ffd8058951,0xffd7654d42ffd7550961,0xfff8159542ffd8159542,0xffd7454d62ffd535c162,0x13a00ee00a2004c0000,0x284023801f601c80186,0x3e203820340031202da,0x4f004c2048a045c041a,0x5ea05c60570054c050a,0x6e406c006920646060e,0x7840760073c071806fe,0x842081e07fa07cc07a8,0x90a08be08a408800866,0xa2209f409d0097a0942,0xb4e0b0c0ad40a7e0a50,0xc020bde0bba0ba00b86,0xcac0c7e0c5a0c400c26,0xd560d1e0cfa0ce00cc6,0xea00e5e0e080dd00d7a,0xf860f580f160efc0eba,0x10761034101a0fd80fb4],#[0x11981156111e10e610ae,0x1288125a122211ea11d0,0x13d213861344130212c0,0x14f4149e145c1438140a,0x159e157a15601546152c,0x168e164c161e15e615cc,0x17b0176e173616f416c6,0x187818541826180217de,0x1968193a190218de18a6,0x1a9e1a661a2419e219a0,0x1bac1b601b321afa1acc,0x1c4c1c321c041be01bc6,0x1d461d041cc21c941c66,0x1e0e1df41dc61d981d7e,0x1f081eee1eb61e7e1e3c,0x1fe41fb61f881f5a1f36,0x20de209c2082204a2012,0x21d821be219021582116,0x22dc22a4227622342206,0x240823b2238e23602332,0x252024f224b0246e2422,0x260625ce259625682544,0x26ec26d226ae26762634,0x27b427862758272a2706,0x28ae286c283e281027e2,0x29a8297a294c290a28dc,0x2aa22a882a642a0e29d6,0x2b742b462b0e2aea2ac6,0x2c8c2c5e2c3a2bee2bac,0x2dae2d6c2d2a2cf22cc4,0x2ec62e702e2e2e002dd2,0x2fac2f7e2f502f222efe],#[0x306a3046302c2ffe2fda,0x310030d230b8309e3084,0x31aa31863162313e3124,0x3268323a321631f231c4,0x3330330c32de32b0328c,0x33bc33a23388336e3354,0x34843460343c340e33ea,0x351a350034e634cc34b2,0x35a6358c357235583534,0x3650362235fe35e435c0,0x36f036c236a8368e3674,0x37b8379437663738371e,0x3880383e381a380037e6,0x39d439883946390438c2,0x3aa63a783a4a3a1239ee,0x3bf03bcc3b8a3b3e3ae8,0x3d1c3cda3c843c4c3c14,0x3d9e3d843d6a3d503d36,0x3e5c3e2e3e003de63dc2,0x3f103ef63ed23ea43e76,0x3fc43f823f683f443f2a,0x40c840a4408040343ffc,0x41a4418a4152411040ec,0x426c4252422441f641d2,0x4348431a42ec42d2429a,0x43f243d843b443904362,0x44ba448c445e4430440c,0x45a0457c454e45344506,0x4672464e462045f245c4,0x4730470246de46ba4696,0x480247ca47a647824754,0x48b648924864484a4826],#[0x4988495a4936490848e4,0x4a6e4a544a1c49da49ac,0x4b544b304b0c4ade4aa6,0x4c264c024bd44bba4b78,0x4ce44cca4cb04c824c54,0x4d8e4d4c4d324d184cfe,0x4eba4e6e4e4a4e124dc6,0x4faa4f864f584f3e4ee8,0x511250da508450384fce,0x5298524251ec518c5172,0x53e2538c534a52e052bc,0x552c54b8548a54525406,0x5694565255fc55ba5582,0x57705742571456fa56d6,0x5824580057dc57b85794,0x593c58e658ae586c5848,0x59fa59d659b2598e596a,0x5b1c5aee5aac5a4c5a1e,0x5c7a5c2e5bd85b8c5b4a,0x5dc45d6e5d405cf45cbc,0x5edc5eae5e805e205df2,0x604e5fee5f985f385f0a,0x622e61e26178611860c2,0x638c6354631c62ee62ac,0x64a4648a643e641063e2,0x65bc658e6542650064d2,0x66ca669c666e664065ea,0x681467be6768673066f8,0x690468d668bc68a26860,0x69e069946970694c6928,0x6b5c6b106aba6a6e6a36,0x6c7e6c466c0e6bd66ba8],#[0x6d506d226cf46cd06ca2,0x6e2c6df46dc66da26d7e,0x6f4e6ef86ed46ea66e6e,0x70de709c705a6fe66f9a,0x720071d2719a71767134,0x732272f472b27270722e,0x746c743473d473927346,0x758e7542751474dc7490,0x76ce7678764a761c75e4,0x783677f477a8775c7706,0x79947948791a78e27882,0x7b067ab07a647a0479d6,0x7c147bd27b867b627b48,0x7dc27d767d0c7cb67c60,0x7f2a7f067ec47e647e18,0x806080147ff07fb87f8a,0x8150812280ea80bc807a,0x8290823a821681e881a6,0x83bc83988356832882dc,0x84de84ba845a842283e0,0x85d885b4859a856c8520,0x869686688644862085f2,0x8772874e872086fc86ce,0x8880883e87fc87c48796,0x89de8988895088fa88c2,0x8ba08b548b1c8aa88a34,0x8cf48cd08c7a8c388bf6,0x8e168dca8d7e8d5a8d36,0x8ef28ece8ea08e868e4e,0x8fe28f968f5e8f3a8f16,0x912290cc90809048901a,0x924e91f891ac917e9150],#[0x933e9324930092dc929a,0x942e93e293be937c9362,0x9528950e94f494c6947a,0x961895fe95c6957a9560,0x97769734970696b09664,0x98849824980097d297ae,0x99e299aa9972993a98da,0x9b0e9aea9ab29a849a2e,0x9c269bf89bc09b749b32,0x9d489d1a9ce29ca09c5e,0x9e6a9e329df09db89d76,0x9fc89f869f309ee49eac,0xa11ca0d0a08ea056a014,0xa270a224a1e2a1a0a15e,0x37000687a32ca2eaa2b2,0x4084c1048e13828401e8,0x949c4c1d0e0138580381,0x8609c4b1f8521b8140a0,0x8868251a1f85e0f81c02,0x1382c001a181880384e0,0xa1a0d0784e068446086e,0x860647e1382e001e1001,0x81613080ac26e1382e01,0x381a1406e178380b810f,0xce18608521006e13021,0x1a241a80384e0a181486,0x1c0638406c2860844138,0x60521b8406b820605214,0xe084414848038486b828,0x521018e1382c04521784,0x852184e1482e1382110,0x60c4c148360e0046b84e],#[0x8e0d82c04100cc521308,0x4061484e0c061004e0f0,0xe08521c10e1382c04521,0x204052102c0aa0001b84,0x8371382c044c1483e138,0xe14838004e14830cc520,0x44413830083014838004,0xcc37130400030148309,0x120cc520c090cc520e08,0x14831484e0802138520c,0x1ac00521c4e148200033,0xa1ac00521410e1283e08,0x2005e1382110521784e0,0x902206b8420f82c0052,0x1e8203713840184e1483,0xb001484042080dc4e10,0x6806e1382c00522384e,0x606b84e081014850b02a,0x42141ae101ee0b00148,0x13820c0520801e143944,0x61484e0c038684e0e1a,0x14821385208040cc520c,0x120cc5210270dc4c0c4e,0x13820f8440852138203c,0x1c0f8441427c684c0d1c,0x5220081484e0c0f01d,0x14850b02a06b8408382c,0x4e0b001488e138286b00,0x82c0051180f0380700f8,0xa447183e110203c0ee13,0x21833148201f8400f820,0x4c148403c0ee1382c005],#[0x3830781013052101020c,0x3b84e0b001486020371,0x3e084414861484e080f,0x414615026684e1407e10,0x6684c1427e1783e044c1,0xe60e846704c143e60e84,0x509f85a1383e044c183,0x144013020fb85e044113,0x56684e144fe1783e044c,0x5e17818244c104006d8,0xf811306e1783e043e13,0xe0c3ee044c180613f85e,0x9c0b85e0f811306a1b85,0x2102096159a0f84c1c3,0x684c1029019856684e17,0x2646a069a13030a5856,0x1389a2311e1b84c0b0,0x433148507a0dc1302133,0x13052085213020c01904,0x45210340dc4c0c9c1302,0x6684c145213020103004,0x6106046704c104f60e04,0x84c144f04785e0f81130,0x16046684f11858100066,0xc144fe1404e0f8113066,0x83e044c1b85013811044,0xf85e0441130413c00e17,0xe12002704e0e002684e0,0x8406e9a13034109a0c04,0x1285a684e1440e0c9a13,0xa684e1411a684e0c284,0x51001ba684e1040a140],#[0x7831306e178109f8313,0xe0427e0c4c180613f85e,0x9f85e0f811306a1b85,0x4c1029019856704e170,0x14406159a13040a58567,0xea684c1006a0c4fa684c,0x4c084cc004e2687a0c3,0x13032684c089a13820bb,0x4e0a830fa9c13041069c,0xa285a684c109c1302270,0x3a684c18042683013840,0x84e0f81130603407a140,0xb85e0f8113c4c1427e16,0x111850999a13c40dc4f0,0x84e10371382e17810a84,0x1783e042713066142666,0xe142901b832684e1586e,0x840cc51080da1417a684,0x1027a684c0c0f6043314,0x40c0111484a1426a684e,0xa9a130400834a684c100,0x1411e1783e044c168509,0x60dc4c0b85e0f810384b,0x84b141f04785e0f81130,0xf810384b1b85e0f8103,0xe1783e0427130501385e,0x40dc4e09850999a1304,0x14266684e1385e044113,0x2102c80039e138214866,0x820611a13850684e1305,0xe18c15820cf1c1308e0d,0x13040a705c684e1086c2],#[0x1a20180684e0f830611a,0x8221b84e082846051c00,0xa81ae1382c00521e1a13,0x3c0ee1382c0052182c0,0x4e1383a08004611a1306,0x383a081a1383e0e18868,0xc1402868331304a081c1,0x828684e1783612188684,0x386062821104e1018e0e,0x8684e1783a08008621a1,0x4408440cc520f83a0a18,0x1027c684c0d1c13820f8,0x6a0b1a1384103834684e,0xa1a1384e138206051102,0x1304e138206051101114,0x6e1018e0851101842c44,0x84e100f03b84e0b00148,0x1818e0d1a130409982c6,0xa138401f8400f8211052,0x404a81a704e130509b1,0xb00c1899140700c3713,0xe440e1382c009a2384e,0x9a130200c9a13030ea83,0xc032684c0c0e0dc4c0c,0x981f0013052140713052,0x7831305c004e13052103,0x385e0f81130613f85e0,0x1f85e0f81a10391c4f0,0x822684e1285a704e0c0d,0x304a0800a169a1385e0e,0xe1781e0c4c168509a9a1,0x6a0833e1781e0c4c1806],#[0x84c0f000cf85e0f81130,0x1484e1783e044b118566,0x5e0f8109c4c1b0013033,0xc1b84a099a13086138,0xc0640384e0851140de0f,0x1b832684c12851484e0,0x4e1305210394004c1444,0x84c0c0403a9a1304c00,0xa1382420120dc4e10331,0x821384608121484e0d1,0x4e111a13821084c08391,0x382008371383c0808148,0x2108520e02130520c521,0x3841484c08040dc4e0e0,0x20c1e0684e0c0dc08511,0x838203e0dc4c10061305,0x14848044e14830945113,0x30681213852101a0184e,0x3820b81a13830741a138,0x4e0a1a13828684e0a1a1,0x484c0c12c071c1384868,0xa1383018271484c10061,0x84c14840483314830191,0x2083a118213052080e46,0x3038684c083a12021085,0x21084c0837130200e1a1,0x9f1a13030e4420835148,0x5210271484c0d1a13820,0x38200e1a138306820138,0x48121a13028684e0a1a1,0x80f04833148401c030e4,0xe100f0484e14848684c0],#[0x8409c371303c08080dc4,0x13021484e080f4683314,0x826005118034684e0c42,0xb80a128246460e839e13,0x7f84e0282a19191a96e1,0x11b0306b84e0b801446a,0x80144703c0ee13826005,0xc3314420781ce101ae0b,0xe081ea0052141e130520,0x80144460826c684e1384,0xc0ee1382a00511b84e0a,0x368047a84a084c468803,0xa091e26c401381a1e968,0x307e84a001e138521b84,0x44509f1a130309b1a138,0xe0b80144503c0302c331,0xe06b84e0b80144801b84,0xee138260052182c0a81,0x13828684c0833148203c,0x84e0e1a13020c8490a1a,0xdc4c08038684c0c0386,0x166684c1385058421304,0x14266684c1039108260e,0x80dc4f0f850fc4213046,0x704f089a13c21484f080,0x4c185213c20001614832,0x59c13050fc04e1783e04,0xa5858119c13c50a58507,0xbb16c0304c084c26870,0x3c089a13c3c089a1303,0x1306c089c13c3c089c13,0x9a684c1429c0806e0c9a],#[0xa9a13041444c080da140,0xa684c11810c0520e8509,0x520a8509a9a13c4a1426,0x144c168509a9a13c40d4,0xa13c40dc4f0b83e043fe,0x2e17811044c11850999,0x1383614266684c103713,0x4e118206f1c138300d1a,0x13040cc4613034704e08,0x406f834684e130509b1a,0xc1b13a1a1c26c171a138,0x83b0cc52121c6004503,0x30b01a13852121a13024,0x48407f1a13830944e148,0x2111a0ec4e10190ec331,0x27c704c0f0580b1c1384,0xd848684c0d840684c0c,0x4e11848704c0d840704c,0x3840f84613030121a0ec,0xe0c27c684c0c28c171a1,0x3ea13834684c14034684,0xb021444e0c27c684c0c,0x4e0c028683e13041444e,0x483c1426c684e101b144,0xc0c1f06c401384094331,0x8309b05c684e1027c684,0x1b0509b1a130400d1a13,0xe12c50a41fe1781e0c4c,0x44c14371382e1783e040,0xf810fc4c17850cf83e0,0x71303614266684e1385e,0xc4c14830fc3713030203],#[0x980e1783e0427130609,0x4e0d850999a13840dc4e,0x484a1426a684c101f144,0x83fa684c118109c4c1,0x83a118213846083e1102,0x60e846084e11820f8440,0x5116060bb84e0980868,0xb98213a1a1c06e138260,0x844e60851141f611800,0xda00511d0b1484c0d80,0x4081484e1007e1003e08,0x3c0ee1382603068688c1,0x8a085213848684e080d0,0x8271484c0c0d0cc510c0,0x4096610441002460a1a2,0x618460b011487872188,0xb0458410182110813022,0x1e13821004414458701,0xc86e0d8225b0113c4c27,0xc043913091484e0a10a1,0x1130804610c2184e0d82,0x522210c23836083c1130,0x381b84e081813b01130,0x868a0cc3713030005213,0x6588ea0e106102960b00,0x8a0d8460a1ac00521a1c,0x1e84182402838204f130,0xa783c684c1c1a0dc4e0e,0x8004f4684c144f213010,0x82468ba08424704c1282,0x1010d1ca10290d82cc02,0x82a10284a091a4408461],#[0x1a82034104684c151c05,0xf130825a820400d4684f,0x4c191e44282c050342c4,0xf1a130640e8242c4f440,0xb051084c0f010038313,0x4c12820683313041484e,0x38306c44138306c330dc,0x713830684e1483610461,0x52138304052138306c3,0xc683313060404e148304,0x1e0f1a0904e1482c0783,0x3a103b09e82c0052230,0x30520e84a0910148441d,0xf8440c040c0520c2f1,0x2138520c020cc520c4,0xa130266896284162c421,0xa13066708f60d2a85211,0x8c66841103e6068460d9,0x684c19838099a1304809,0xa1b02670761602e0c3e6,0xcc0a8666888458a80187,0x396684c1e1160e000f84,0x98ca199a198104183c08,0x242ac099a130584600c0,0xc0a00061831319a13870,0x61a9c208a1068b1084,0x68b108447d11a2902a1f,0xa709e1911a2c42110610,0x47d864128ac0b0010687,0x9a09c4c1186a2a9a1044,0x84c101509c9a1304854,0x3702c01862689039851],#[0x161300a6888c20ec109e,0x61a9a269ca0c2a4591,0x69a2d1f446834084c09f,0x91444506c09840ab0010,0x3683e19844469a229c45,0x10302c01862689a700f0,0x2c0186a68a8c20ea0f04,0x9a1d1f44683130274130,0x9a3030412830f986446,0x2403704c080e61841c0,0x504a0e9a13062789c14,0xa1305400282684e104fa,0x83a682c1385a068313e9,0x2a27840c0b002688a06,0x13040780d2684e104cc1,0x7c0b002689e1c1e0349a,0x19a10442684e0b040c02,0x130660e046684c118c81,0x6c019c1d858104fe0d9a,0x8ca6841121f8460261e8,0x329a228ce1a9a104441a,0x104447d8641302c0041a,0x400c2aa6841100c61a9a,0x89d2684c12830fa9a130,0x13856178313d9a130503,0x60cf022688617836682c,0x83a684e200dc13000c28,0xe9a138706e854004007f,0xe9a13060a2854104ce0,0xa13822684e0828a142ae,0x71a130382439c6841109,0xc271a1383a0b1a138302],#[0x82468401107860521383,0x4e4684c14880438460f,0x61834684c149ee138211,0xa1c8660b0513c4c1c288,0xb04486e0f1a0604e2218,0x11c2d84c143913071001,0x852c1582c6a181307860,0x13852143320837130421,0x48868684e141a04882,0x4e0c182101a0c04e144,0x13030d4180c052101211,0x4e101a4604e14840ce1a,0xc4004844138446012148,0xe10401184e0c180dc4e0,0x2411c4e118520c461104,0x419e13820404011060a0,0xf8441028061820684e1,0x4414880621a13830780d,0x511c240888314784e08,0x8441c2408828e138246,0x608442d1b02c4ce101c6,0xc11b4460b0fa1c61029,0x6e1283e081a100441845,0xa18220ba0d8460844148,0x486870166182a6118286,0x4684f0d840ec2760b001,0x4c1084c0c4fc684c1418,0xa821051c1304a084f468,0x130646282c0d0b13c4c1,0xf4604c1918a09034204f,0x313f1a130440e824204,0xc41c684c1f1a1044c0f],#[0xe0d18c684f1828460872,0x320b838683313090a022,0x828681813850741802d8,0x691813870611a1303e0e,0xc683313051001b04783c,0x4e1f03c6824138420b03,0x84c20282104ce0d18c68,0x4850a087e0c2220d18c6,0x8444e110409384604451,0x33130886e1111c4e121b,0xc4c150b2128360c82c68,0x191a0604e2218e0f1a0c,0xa0b1a13871001b847832,0xa21845138710086c1438,0x1a11040144606f830471,0x84cc001a860511d83c00,0xc9f4021a1484e248613,0x60a1813851141b86182e,0x181487e1382060511086,0xa18138609022e1382606,0xc184684c1028e0d82c6,0x60c5111384e091a1489e,0x986384e098114870e839,0x841338360b1a13880e83,0x218e0f1a6084e1840861,0xc1c12138520c52138210,0x9a191fa2906a1f0060a9,0x9a1487c1b84c0182a2a,0xb00a68807810e1382c0,0xc1a9a203041a8347c4e6,0x148aa0c0d6084ce1300,0x1110240888326b84e0b0],#[0x4c07a83a069a6084e1c5,0xa1061281a0e8b0e44c20,0x7a1024a81a2a9a130787,0xe138213b002684c14898,0x8c004e1309a148607810,0x89ac005224191484c0d1,0x484c10240881e04384e0,0x462831009a1305a0c9a1,0x6144f1307a04521303,0x19c18521382c1f83a0a,0xa099a138487e06a0987c,0x4c118560d9aa084e1420,0xe820e5851308a100e668,0xd880e44c181f62e84e0,0xc0c1e040521304462846,0x82824516144c20136684,0x89b6319a13071018be0e,0x60526159a130710118a0,0xa1981e0d9a1304e0e824,0x9a1303c1b84c02826319,0x3001446e0d9a130300d,0x2684cc0051141e22d831,0x240285e0c52a684e244e,0x511982138510c1f06d8,0x1811487e13820604e13,0x4052130409022e1382c,0x820cc4613032684c081e,0x13030f81a0dc4c104613,0x52138404849138309c52,0x1a8103b1484e1512094,0xf84613030743b0dc4e1,0x3b1244e0c3e048521304],#[0x683e13052100f1484e0c,0xb108627e0a61b0b10854,0x727f1c18a127d862030,0xc86c2b0b108621180c2b,0x230ae009fc2c4214a127,0x439808780d61182a1a1a,0x86c688c18296031a1085,0x91a2016c0c9f25822a11,0x68b83b03a0040a128261,0x400da028403d86106824,0xa12820c186c68b4791c1,0xa10852849f25b030fc80,0x336009fc6872003961b1,0x44c61282c6880c084c0c,0x138027f1a1b0309c9f28,0x611820621a1486037036,0x2611808681b100512303,0xe1e1306008371383c0d8,0xc1b1444e0e0360a0b13,0x41002ca091a1f051084c,0x22a12824691e1e8047a8,0x6820780d4684c1416a00,0x1184e0a820780d4684f1,0x1b1444e0e820683e1304,0xc80138520d841184e0c,0x460980c0452140413052,0x5107d8460182c04521d8,0xe4421206a018c62c4214,0x6178366a16130500d8b0,0x887e1680987a1b046707,0x2147d86c13021068ca68,0x49a130403186a684111],#[0xf1307c084f2684c13021,0x22688a1702400832204,0x84c1c0dc001608a86c13,0x684f1828a15000ff83a6,0xc089a13030a2850ab83a,0x84e0d1a1382c089a1303,0x8685213864684e080f14,0x511c05138510c18e0f02,0x8511e1be118306b02100,0xf84c1c3be121b4cc1ac0,0x13851101d10102e0e1a0,0x854684e091a138209502,0x1c9a1382812806321f66,0xa152147d06c0a876129c,0x472684e0984e028c47e9,0x4478618346a84a084014,0x13881384c46a84a08441,0x11218e0c80c1582c6852,0x8360b1a1386860911385,0xc18e0c524684c1428c17,0x7c1b138511011138510,0x846004014490084e1443,0x180144847d1ba0d82869,0x18512784e0a1a4603e13,0x143b47e1a60984600331,0x260051141f8681b13851,0x1ae138060851161ae138,0x1bc141fe0c52c684e1e,0x148410082e0f1a0f84c2,0xa0f84c143b0584e1444c,0x510e82138510f05e0f1,0xa004691013c39182113],#[0x8918a08414680d4407a,0x87a28481c8748441a285,0xa83485110f830151f106,0x3864591444584038411,0x349a1584a0c4b47d11,0x444c1210f841109e60c5,0x8501009a184b47c0e10,0xc082e4442a268527983c,0xc2161a861828784f0e46,0x182a1e8a198281c3d08c,0x1900a1d82a28547d1161,0x8650660900104390d474,0x947d116128360839a688,0x470b68360b000a69a182,0x1c643206a0a0041c3910,0x63187161f84684a098c6,0x161180c1f0a1a0680282,0x94246826000e104727c9,0x8a1a083f27c0e1086258,0x3866130312c9127c0e1,0x351a18a1c0c3f2589f,0x261a8ca1c747983a085,0xf021404026864851f45b,0x1916c082a0b89a149e60,0x7a30687e11a128061d8c,0x12147d166128]]
set_option maxRecDepth 16000 in
def g191H9 := limbs80 #[#[0x400010403422400021c0,0xd0021010c50c00830,0x1031430800400450410c,0x508c00914100724b001,0x1060007440080442030,0xc01870c23c2a4110308,0x500010e44d1c0080280,0x20400451871800041440,0x8514408144920204d18,0xc017218900b18300a0c5,0xfbe0833c0040216f0470,0x711b293204c9e454ac14,0xb600000576ee3c000e22,0xa30002cd20000000b3df,0x60a5c1164dbc210000c,0xd9300c1f7fd41400,0x3d4b9998f19cd98783,0xf800095b944571b778d0,0x30e100014c100000001d,0xd5e000,0x31000000098440003860,0xb632e23c0de4477468a4,0x360e86c51538193aded2,0x89c6bd034f708663128,0xea59a42c40000000000a,0xe4da0000000000075b24,0x88150600000002c1d098,0x730000b6d40e0000d4dc,0x532880005dd70ba834d5,0x81380001390cd,0x425000000055c318e,0x780008054000000295f0],#[0x4000fa618200000000ee,0x8880001b95454f75745b,0x13000016500001840000,0x4a400085ae42600025,0x3d2e484e583a16aa7000,0x10fc52f4e6d2e99084c0,0xee0db000245b4299d20e,0x7ce986514f474cc0004d,0x822dc6c1c726c000915,0x34bc000f1e649dc454,0x70380005d2000000000,0x3b742781a97596a47400,0x31c00076000000590000,0x20000a00e54700000004,0x14f265eb51fe4,0x3d10ec25f3684000000,0x402a41fc1134bb5c5c,0x9a0b7c5d0002c65d4fc0,0x61fc000632800092a3cd,0x3586130ed6700024aa,0x925e4d40,0x1a5c0000000503c00000,0xc42d67c00062326b5000,0x72780003c90000726a,0xb000000049b8d8112e00,0x9e23b77e008000000181,0x65300000000003c70,0xae999e33083c13d8f0d0,0xf3400003d09b38000043,0x11eb52208541938d0f19,0x22c00000000009362,0xe6487ec6e690469e95c0],#[0x929c4f,0x0,0xcb99c0003d1788401340,0xc19b66021,0xee00034ff0000903000,0x7633,0x2b9800012dc00000000,0xa51000000000002c8c00,0x8e280000003471,0xfc8b9000351100035320,0x13ba0cf6c27c4797d75,0xfd048fd7542862000,0xf970003d2d0000,0x83b3cd648a1ca400000,0xe146e24e18e057000000,0x1ec000640b8dce164000,0x10b9d2b0588864000f,0x2cc500000000b9c00000,0x22af392c158000adf,0x71808d7408f45e0000,0x9543310000e1f00,0x55d40000000000000000,0xc04000fdce81713e0c93,0xa778b9b652af319a32a,0xa8e3712b87315750bcce,0xc399405014083a82d,0x350002d3c000317c0000,0xb5e180ca09f0b464491,0x2106c240000e3bc00,0x135ce5bc00000020b0,0x4b2c52700000000,0x80000000000000314d00],#[0x8d25c40f99953496205,0x7040353d5b00000002,0x4dad832352800000000,0x2191958b02a15a000,0xd394000,0x6b5f0488000d2840000,0x166a1bf24ec4f400090,0x618411a00010fa000,0x349ffdc80001428,0x17873d00a53bc744e500,0x163c000f453192dbcf55,0x1f9c6e000281a0003da3,0xd8000000309400000a09,0x18d0001919000000041,0xced00000001824000000,0x47b48fc3f1e8015b7e1a,0x50d64000de0451652ffc,0xd954000000207d0003da,0x1526cc18376da25c13,0x10379dd000000039770,0xc090000000000000,0x4573a2f1654796000,0x2b0000000967800065f8,0x500000008dba15700004,0x201400018f1aa2ed8,0x5d15791cfc000fd0b561,0x640000001408c347ce2b,0x1393f21d98ab10000032,0xc489270835f13f886c43,0xc49301f,0x85cbd35e22480005aa80,0xce245970000c0492b695],#[0x530000c8c4ccec47385a,0x116ab4c2c78e3774f34,0xd1a8000f321da000,0x339b562c4b2000,0xf6770e78df4,0x4b17c000426382e65640,0x60f800080bfd0,0x68800e758795ed8de,0x16fe000000000029550,0x778e653c9492e92671f0,0x8bd83d4e4f0000000840,0x18a4e000000000000000,0x40000891cd38000a2d65,0xed1a8830000000000392,0x2be0460000000be31c75,0x6d8a5d558034737e0683,0xc0008d58000d548000a9,0xf9f00031820000141c14,0xc991702a444340008622,0xe4b000000008950002e,0x758c0000000000000000,0x24be266c525f5a6943,0xdad310000000e5140000,0x2ec50001d40cd1f189e0,0xd100000adc23ed9073ba,0x2300000008dbc2bc0000,0x2297e509af200036,0x288a0000256000000,0x480007db26ca2b3c84d,0x21460001a9e2c17d906,0x8000dca80000000ee300,0x220048ea2b],#[0x2c000000000000000000,0xe330bd7240240000002c,0x532400000000000001d0,0xd8880bf8c3e29d336c7a,0x3768000000000008fc5,0x14410000000000000000,0x5078000212c000a0a,0xe8233c0008018ceaaa80,0x4843e4a9c23dd5a2c3f4,0xa2cd66]]
set_option maxRecDepth 16000 in
def g191D10 := limbs80 #[#[0xd6558f6eb1ac377dcd51,0xa21fe58110ff2a0886d,0x10feac2887f551443fa9,0x7dd63442ffb92217f5c9,0xfbaa217f5d510fbcc688,0x120bfeec885fd76442f,0x905ff71483fcb0241fe5,0x3f6b1241fb54920fda84,0xf5d120fbcc6907dd6348,0xea905fd75482ffba2417,0x542ffbb2417f5d920bfe,0x1df54950bfee2a87f960,0xbcc6a87dd63542ffb92a,0x76542febb2a1df59550f,0x2c1bf58960bfee2b05ff,0x1bfeeab06fd65582ffb9,0xf561487faa0a437fdc12,0xb1a43fb58921fdaa490f,0x121bfae890fde63487ee,0xdff75486febaa437fdd,0xfab0aa37fdd921bfaec9,0xdc161bfaeca8f7d65547,0xab0efd65586ffb92c37f,0xcaffba2657fdc132bfee,0x7fdc542bfee0a15ff764,0xcc6a17dd6350bf6b1285,0x650affbaa857f5d542fb,0xa57fdc152bfeeca15fd7,0xfbac6a97ed6254affb8a,0xf7454bbeaa2a5f798d52,0xb2a57f5d952efacaa95f,0x62bfee2b15ff7058affb],#[0xdff7558affba2c5bf591,0xfb82c77fdc963bfee0b1,0xc565bfee0b2fdf7258fe,0x887fd42442ffb92cb7fd,0x3feb9221ff58910ffaa4,0xf5d910ffaea887fd6544,0xa2907fd41483fe98a41f,0x483feb8a41ff58520ffa,0x1ff58d20ffaa6907fd43,0xfac8907fd54483feb9a4,0x75483feb2a41ff5d120f,0x261ff50930ffaec907fd,0xffac2a87fd21543feb1,0xfd62543fea12a1ff5c55,0x90ac1ff5d950ffae4a87,0x560ffaa2b07fd31583fe,0x7fd32583ffb8ac1ff5c,0xfeb92c1ff54960ffa84b,0x5cd60ffaa6b07ff72583,0xab07fd75583ffb9ac1ff,0x87feaa243ff5c121ffee,0xff59521ffae890ffd644,0xa8498ffd76487febaa43,0x2547fea12a3ff58931ff,0xc3ff50961ffae0b0ffd6,0xffaeab0ffd72587fea92,0xd7150bfeb8285ff59132,0x9a85ff58d42ffaa6a17f,0x42ffaeaa17fd6550bfeb,0x7fd7154bfeb82a5ff5d9,0xebb2a5ff5d152ffac8a9,0x4d62ffae2b17fd7058bf],#[0xb17fd7458bfeb9ac5ff5,0x7ffb82cbff5c165ffaea,0xf5c965ffee2b2ffd7159,0x201bc0330003ffb92cbf,0x8e81e3065414703e40a,0x143c90da43240b7c2a3,0xf459d156050a12a84651,0xc7c21d407021aac64b17,0x9b125b091e22b0867201,0x342bbcab329dca3b27b4,0x33378c7e309cbbe2e08b,0x39f0e3737c8dad35c4d2,0xf8ff03eacf423c18eca,0x11a9459111f438d07a4,0x531a4bc12bd49e123c48,0x4b8518540a4f153804d3,0xcb5a3d64156f556f5419,0x606d7cd5e457555c1d6,0x672d98664e18fc629586,0xd39b1b6bc5abe69c1a2b,0xf5cdd71adc146f61b816,0xdeb179f9e3077addaf74,0x8581920287eb5f447bf,0x2c8756190850a118832a,0x98e5e35b8ca22d18a562,0x97ee59b94a64b791a640,0xef67819c3e6c199f2637,0x92928a38e88ca0fa7de9,0x6aa2a99aa33a74e9b2a5,0xc25afa6bb6adeab3eabe,0x1db6aed6fb43ecafb186,0xdbe22f31bc42ec2b9f6e],#[0xc573117c2bb069c04afc,0xb7f2acc9c3222c7bf1b3,0xd3441cf873aecda732dc,0x75fad647555d41f4cbd1,0x5800d0d86c260b00191,0x361305800d0a060f613,0x3010006130444200689,0x908613050184218a4407,0x4820830420a004e29100,0x1c41e13041014c003440,0x8782184c10210d002912,0xd018005d051a27148b41,0x160e343e080c12088400,0x5310c260a00860d0e214,0x4509a2184c14010c1c1c,0x2044030730982800a43,0xa450730d84c104034306,0x78200380e1304868d400,0x4a01e13051a431482038,0x444e00c2e0509022610,0x385c0826043e4313080a,0x52046020c2268a4111c2,0x220e0161702848013082,0xd8470685802689c4058,0x40581c1c004e86261504,0xe804090c9a26121f08e1,0x8129c43104841882083,0xc2e04984130982a824,0x4470b05022074208205,0xa9a271407c2e0f038642,0x88e1b0c046050010e0d0,0x4e4c300c85c1e10989a0],#[0x440e0481617078180218,0x300be1702414304480f8,0x630982828250d1a1c0e,0x689c40730d84c1068303,0x3e0c0d840d8630700410,0x60a00860d0c214160e34,0xf18c260a00860e0d18c2,0x1a203184c1402121a430,0x6060c4170784c14010d,0xf064d130bc260f051a43,0x612390380d03848004c6,0xa0f81b0b81c18ce00822,0x1f0900c2e044f0983130,0x6c260b0685802687410,0x13a0016834250a9a2610,0x30a4388501838d138243,0x22913870a8481084811,0x410044e0d0e120f0210d,0x21f84218a44e20381b09,0x240a00862706860940e0,0x148b8240a00862707068,0xa8480c8481404131a26,0xc004260e343a090e16,0x60d84a04060e0509c1a2,0x29138b0e61b098009068,0x1f0f048088681404131a,0x60d0e14c1a1a344e090c,0x10c1a1f0982c00343c8,0x82c0218344c0c8184c16,0x202341e183c1c2883709,0x882c1c68661e1b0983c1,0x281b0982c0078801a1c2],#[0x9383413130982c007834,0x4c342818003a09868510,0x86c290900161c0809270,0xa0441804d1482c380c11,0xd8582607061643130927,0x45a09024326898487c1,0x704812710c412106208,0xc1a1605044d130b15401,0xc9e9a0b101d0d8580c00,0x14309c98701a040042e0,0xe1603c1204001fe17078,0x38270b8120a182c40843,0xc214060e344e0d8c420,0xd1a27101cc3613001b0d,0x31383432103e1bc1c150,0x9024313838340309024,0xde0c9d0242068984403,0xc0c00c1a12343a0d8e1d,0x9c4e10378343408344e1,0x183e1b0a4090d8382c68,0x5001f202983434689c1b,0xc4d07c7038ef0b84c1e0,0x12043e261400c1a07084,0x840f8e210f81b0b81c1a,0x131341f200f85c1e0700,0x48010068503e0d0a09c2,0x200d0a14198803426130,0xa11004e100685c260900,0x7834163984c1200a24,0x51241b84c16020c1a188,0x18820390029068e4149c,0x42042023c80208851a26],#[0x200404113834505b0710,0xc8d138a46072201bc204,0xc1f80a130610414010c4,0x290e1208a110410290,0x688852200c10c260835,0x9820814850c0430883c1,0x261a00878110538407b0,0x2284c1a042a9a260e8a8,0x720e2386c240a009a2c,0xd0d00262689c68c13811,0xe193c1140c101b020f60,0x5d344c0c241041845344,0x88826191902049053438,0xe101c20c24090c092626,0xc22854d130809825344,0x8308e047c4c1c3b02426,0xe15098107104984e1443,0x68680131344e2c2c1408,0x8a689c3046084042c0b0,0xb83c083898486c30830,0x410263441143e114221b,0xd188219a1883098d0c86,0x241219081280460224e0,0xa3098243400345070309,0x1cc260888407a30184f0,0x208831a2618180802f0c,0xc605a308641a10310580,0x20a188020a1286264689,0x408e0e344e0c141f8c21,0x90d1a0c0c454106d0c8,0x960d029a270f84c1e,0x22b098243c020c9c1d04],#[0x83a418e7098280419344,0x1e09030627401344c291,0x68340a6898307821844,0xb83c0930a09a689c181b,0xd13888381904002785b0,0x724c240c820060c36854,0x260e1f08a110585c1e04,0x8129a190e06c2a0b0309,0x483024989a2309824641,0x2614834d13031c883058,0x1842e1305838013a0c9a,0x199486034250a9a260a,0x76244e26068909044208,0x2180c689c38702502420,0x5424841994860940b06,0x38582400241a2714860b,0x12430dc9c306c24830d1,0x2081586c042c84307c3c,0x49f8561301074320a384,0xb03a0696c360108828d1,0x69fc260104868d151c0,0xc26083c80290c3b0f83a,0x9130183208851a261810,0x4113834505a3c0d4207,0x38a4387901840dc7a0c4,0x1a0694480fa1100120f1,0x84e344e0c3c83c260b00,0xc1408e16058140104984,0x38582a1281204844c1c2,0x26898061a048c8210534,0x238802d008220d0d0226,0xd130b0b84e0483152688],#[0x6804108085c1a1a2d024,0x2436830ec082c9a260e1,0x210f85a0486c29087e4c,0xa270a1808a26341b270c,0xc37058d13880d849061,0x830b468364e184302426,0xe2610830fc68364e143a,0x709c3045081fc2e05120,0x878141938387824870fa,0x8026834d13858fe1300,0xe16c2a1307811f838985,0x522436870fa709c28843,0x8c18c1c1709828320234,0x4028900602e13048028,0xd600a230790784c106b0,0xa1f8d1489c581b09820,0x2714450da110480c1c1a,0x2004282]]
set_option maxRecDepth 16000 in
def g191H10 := limbs80 #[#[0x608810621c000582000,0x20080804040f80c04,0xe1100800380005800,0x443000028d00023000,0x6400090000012030,0x21a078000401000040c0,0xc0200050f40a0b000280,0x97402000701802000e80,0x301c0004020183e1100,0x8000003040000007,0x261a070000a200281800,0x926d00828320202008,0x7054200b188000806098,0x701810560d0381006012,0xc03090081e0700000900,0x4e0040402000000202c0,0xb384e4f0080c522d0102,0x2080028000003404000b,0x40706016041700c3a1c,0x16142d80808050d26824,0x1c40530588002311d920,0xf8652e180185c0017000,0x40201442024500c04330,0x80c0400dba024882c000,0x802010d82c172b000680,0x2d05c0404a8034081780,0x278940724010f42e3902,0x100f81056380c824963c,0x2711181806100199804,0x213008140a2a0080c,0x45162380000000f14185,0x2dc2d91f70e5d43427c4],#[0x3e163000000000001853,0xcab6bcbf03965e731406,0x8919040864c28b3fee09,0x24af1bf0e0000e17d779,0xd0d067e302043d80ca5b,0x143b000198228a94d51e,0x7e52074b456000000000,0x469db700000000438923,0xfe637bf9c76558e0000d,0xcc01770c871989148419,0xbedc3688326adee06086,0x515ac829039096b6,0xe1e20d0c9b440cc74000,0x1ee60f1d7d489953a0d8,0x211a0000039800003070,0x3400001fa0240000014e,0xdd600014c36cf08d409b,0x18d28e0e00016ee0000b,0xdf81ae21498140000000,0x9c804b04130000b0f488,0xdacaa625dc324ad484c3,0x2d8da862e42f4624080,0x1c86272f8000c4da00,0x624115cc13a3d67668d0,0x942a35c4d111f7c266b,0x925d730020398330a392,0xf123c3370a0013d22604,0x2b4588000d8c5e73784b,0x324c692cfe8edba4c2f1,0x1b095f1938257b00000,0xb3c50a198bd42d8f3546,0x9926216cf1312f7cec8b],#[0xdd49a0c334eb94b72bae,0xc16260a76c47cc38be7a,0x2a6abc000049d591d2e7,0x8b6600000006ae30,0x58a3788f5d885e32d16c,0x18d250fcb238e100005a,0x7b106516a53a41eb007f,0x200b7218ccd13dc2cc79,0x43d30194b67215037566,0x220c33cd676914500007,0x2411254584009679f23b,0x1dc55372072c0cc1964,0x8852f4cad70d80d769e6,0xca4bde8d0e4d8a45c0ed,0x31fc1000066ecd93a89,0x49397237e55c0007e1e3,0xa800002bcd03d60a4000,0x5fd89715618000e28e02,0xc0146576d04c98349796,0x557530000c4966234f08,0x39d0b08925710f5473e9,0x8a0e0000000000000005,0x1c9610ad,0xc6749900000000000000,0x398da79000076de6,0xdc000000000000000000,0xe233ce30000d0d2c9,0x1de40,0xc38938000c44709cc000,0x18a62dfc7f000055bf11,0x8000518f89539523046a,0x2a38b1d1211d4a6],#[0x2c00000000956000000,0x4d4284d5811258760d70,0x317c821b7d4ac43385e,0xaba0002015c8a5000000,0x80000000ec1000021603,0x32f988b07025a8a9409,0x3d3031083edc1fd35800,0xc1fca1159140570ddb47,0xb9a0b0ebc0ce3196cca7,0xfc0003b398000000162,0xa290000c7c8000148a2,0x4b478f9e8b346033eac1,0xbe57c4800000000000c9,0x492100000ba00002e97e,0x540000000b0c76617b46,0xb5709d80000001e3,0x80002dbea4aa01c29e50,0x2e4a21f3f4d1e40e663,0x1206ac0000183e000000,0xdaede2eb9904000616ad,0xa9c0888b90000000016c,0x154280000000000063,0x50c30b6fe4fc4c05f110,0x200306f68bb3e6e4000,0x3ea00005480000000000,0x50ab000000028400000a,0x18000000000012a98000,0x14ff6b800068312bea29,0xc75627000000001,0x203a41a600000000281,0x4e80a6bce8ea8f21fa00,0x50dd1841483595718a8d],#[0xd40000000ed100000000,0x1d7458a4029504808301,0x10ce000000000001,0x99116000000000000000,0x8cff71e1705a69407f68,0x830be512c2c841a78a29,0x4c00031d801ecc37055f,0x45f8423d3a9472000143,0xf090aa15f3b8000f,0x1c49be07f3d444154000,0x2ede9bd076c928c06426,0x6d0c85f6816000041c34,0xe0000322d0001aad142d,0x12ae570000795ef611a3,0x7e11e2fc3384c216,0x6727300000292e9e4000,0x5a26ac80004c7a91f881,0x9a1000043c000000005,0xf1d2cae20c26a0124000,0x146a2900007999331b65,0x9ab519502e08e000003,0x1d30d127,0x6c2403bd31580b800,0x7a71a5520000000501f0,0x3821000005d60000000,0x1327bc25aa3fc8e800,0x3e05e256c98b17aee790,0xf4d1ad2a09352ab5e509,0x37f6774000000099b6a6,0xc0838298e034045c2707,0x1c00008ceb50fe084cb7,0x252fa7c0006994a23cab],#[0xf105a1b0000000002004,0xd000000000001427ecdb,0x44e06d800015e284,0x7d2655c4a13c923de850,0xe4fa0000cd5,0x4770a0b54ef266b53e00,0xc2b81d0ff4940002911e,0x7aeaba06c00000002877,0x2b0641a03e684e53dd03,0xd2a574120000c4f0981c,0x7b95b529401f7709448a,0x3d6000210830b66427ca,0xcc49f0bd8db0000c,0x8096938c20001c16c000,0x2092174000622b54a000,0x78afc97e2065d21fa301,0x45adcc90e852783ffb3a,0x2caf2ca513e94813a74a,0xb01bd622c8cd4e7a9463,0x2d0b68000c2e218bf13d,0xc3729304408ccc744b19,0xb9109629c64fb808000f,0xcc8f7cadaa35b6ac5847,0x27bf6784ceb236322981,0xb3ae0001d22da1a3,0x440a5412ea485c47552d,0x4cfb0c4901c97f739185,0xa94b312869470115d3d2,0x8c89269de4320bbc552e,0x17a05ebe2ce13a00012a,0x33a98c040006454b,0x1d7a44d40000c3b1085],#[0x1d40d049aa4f154e00,0xb9f6d5ba30a40006a080,0x8e10eb9845074e98ff18,0x4fe00001477222000123,0x91590001d7e9883da5e2,0x208cf3acd0c5cd8ffac1,0x635cb9e4000c0bbd7409,0x8000732a00001440000b,0x8910000e36b41a888f,0x1b76b43c394428c600,0xa9e090860002206e5dd0,0x7c000000000011bbdc60,0x379eba6822ea3d407288,0x90012489e2080300000f,0x3714cc02f93d867aa0c5,0x12aab06fe8000c591e9,0xf05000000000c9b08be4,0xa40da109114be000120b,0x1c0000000032c1b263a5,0x7a5300d600000000000f,0xe0cbf00002371439ff58,0x62cd64baef5297c861a5,0x3d27000186fa69b02ee0,0x3c0e89ccf3642c5c000,0x61a814d77f88ac000000,0xde918984ac3dd00f0cda,0xeb15bd102a16600038e5,0x9b2ae4a4e4898c06fe2,0x8e0d940d43e50b821ca4,0x540412d3d84fa03c8a2,0x2aa61be4fcca05321a25,0xdc5e5b2041c6959f9c7d],#[0xa0c3cee7bf4167345d03,0xd8938d00d17197bb146a,0x90c0d1ac026f08928e5b,0x314ff2af7dc5a42748d7,0x3fed3f9011f8840bfd8b,0x59772bfebbe5ceff422a,0xa02598000b4646bbf43b,0x41e000325e8acf35d5f0,0x914235fe98a215a9aa25,0x7892b08b5f57c4c61238,0x24bb83ed6a7a3c94dd21,0xa8a9f02000008d8a6ee9,0xa903dde172b7dea6398c,0xb17e15b46a4a022433e0,0x488682cda471108ea81c,0xe8ab757bafa,0x462268273780006cce00,0xd8d1e8ee670860c0e8ee,0x59d89e1a5edbac7d3ee5,0x11307b7a59d6dcf446,0xee62bbbf8b7340acdab0,0xe78e480fac2c2c0ee6f3,0x438f8498e280000017ba,0x48d900cc0000079a93cf,0x718aef600c3c74b1349f,0xbd22bf4401e81788cd06,0xa5c97916295c94226374,0x280f680005113d6fdb54,0x9ca7913d41f6a3297ce0,0xd28dcbd1944f581f82c9,0xabb35b27e52beaa6c972,0x4b6677348c684ad124fb],#[0xb824655f94227343aa1d,0xeb8fb82f3d3042aa80fd,0x2e595dc4720e8a597128,0x1abd987848b82309aad2,0xc3c3468ee9382800b08b,0x3344887c0e7ad69de121,0x817489e9eb6d412ba490,0x5f0f0a096b34fcb17564,0xe1f4b93cf8b9730018a1,0x6e494c2724cf22dca956,0xc744d39d222c722d0000,0x4f1ac08aa08b0a506cf7,0xdd09f5a1809cf2b082de,0xe5436e30c2e0beaaecdd,0x3cc71d120000b8,0x326bcb120c17d65b9500,0xc8000686e01e8c859d7e,0x525d91445d800089fe04,0x5473635dc6440fc7138a,0xa18d4212d0001e42c493,0x90225f400048879201c0,0x7968f]]
def g191D11 := limbs80 #[#[0x30ff483fd10f798fdd63,0xfd31ff487fd60ff543fd,0x4bfd42ff4cbfd61ff547,0xf597fd63ff54ffd62ff5,0x5d0971001641b01b000f,0x19f2f05749d11b200374,0x8280061a1a1f4087a4e1,0xa200e120824187060384,0x8449100001868482091,0x91a141c021a16120424,0x4021a120824688868482,0x78584838281000620601,0x1848060e1a1200086880,0x20a00687868482800a1a,0x1848280061a20700e1a1,0x26180e1200086861e830,0x88078685838180040216,0x602246c160e1a0210086,0x30686071f85848180830,0x828003061a1a1a120a00,0x16120a020c1868784]]
def g191H11 := limbs80 #[#[0xc6399c0400001380e1,0x380c1084622b83068401,0x8021790637c822001ab,0x16b85015241842900040,0x63580870878410000000,0xe0c61224f06f120498e7,0xb90002a6000000001c7e,0xadd0d767f2060000000f,0x7502700b996d5373206,0x92040000006b78003651,0x8b4babf4ac000a5c,0x2c66000b21000000,0x87c350006a25e1080a00,0xa980028dd573190b96f0,0x8989ed00da00000ea6d,0xe44000000112e1339a65,0xb8b84637b0800000165a,0x94574ab40014a56b2814,0x252c42f0007db301750,0x58d305607ea928692500,0xf491963a50ab0ee16a8,0xb20,0x1240001461516c06c000,0x996a000587c001e06000,0xd0000000000fd839c440,0x31516000000111a84588,0x457800113500020fc7,0x8551721cf00010e80000,0x1c900018de2b4a4e8003,0x246273d0000824000627,0x44e0d2000000000,0x2a5248798e145d8c400],#[0xb200018848f3788fb180,0x86a0be6a13b700004536,0xc7e0005904c29c85f498,0x293c92aaa30000000001,0xe2c00019b4000e39e56,0x3a5fcd89895c508c800,0x14266549000000000000,0x12c974663f7033d80031,0x506000a1f0000000f111,0x6a7f4a10b873b96ae,0x5560000000178001f91,0x21b00000f5caa000000,0x0,0xe4e0000000f9da0b00,0x28001f88efc3488268a0,0xa029990000801a0eb3e6,0x384c0000000000000000,0x4a7825f089122000000,0x704813400000060d000,0x93d7992321a90aa00000,0xbb08e80ec732a780014,0xed6a59515c1534a317a2,0x84255fb830da0c343dd4,0x3d4400000000a000104d,0x381400000082b800,0x45929e0320e800000000,0x70000554048e00000038,0x94c11e0000000002c3de,0x41900020dc5520000007,0x5a2e9620000000000001,0x0,0x6a08001a08d5434810f],#[0xfe0000000000000a7200,0x5201f400000000000006,0x44dfc14001d94e,0xb1352cc0018653320000,0x199a]]
def g191D12 (j : Nat) := if j=0 then 0x305080c101003ff else 0
def g191H12 := limbs80 #[#[0x2801c4c06a32cf010000,0x71967800004172,0xb1800c411a0,0x5a200714158000045c0,0x71c00000008000058e0,0xf68008,0x101000000000,0x108000820000]]
def g191L : Nat → Packing
  | 6 => (1,6,7,0,0,0,0,g191D6)
  | 7 => (42,5,7,0,0,11,0,g191D7)
  | 8 => (422,4,7,0,0,15,0,g191D8)
  | 9 => (798,3,7,0,0,16,0,g191D9)
  | 10 => (186,2,7,0,0,14,0,g191D10)
  | 11 => (18,1,7,0,0,11,0,g191D11)
  | 12 => (1,0,7,0,0,0,0,g191D12)
  | _ => emptyPacking
def g191I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 4 0 0 g191H7
  | 8 => lookupWord 13 67 6 11 6 1 g191H8
  | 9 => lookupWord 141 907 6 14 9 1 g191H9
  | 10 => lookupWord 266 1319 9 15 10 1 g191H10
  | 11 => lookupWord 61 397 5 13 8 1 g191H11
  | 12 => lookupWord 5 59 5 10 5 1 g191H12
  | _ => fun _ => none
def g191 : Forest := ⟨191,12,fun i => g191Y[i]?.getD (0,0),g191C,g191A,g191L,g191I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P6_0 : block g191 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B6 : block g191 6 0 1=true := g191P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P7_0 : block g191 7 0 18=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P7_18 : block g191 7 18 24=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B7 : block g191 7 0 42=true := (@block_merge g191 7 0 18 24 g191P7_0 g191P7_18)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P8_0 : block g191 8 0 76=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P8_76 : block g191 8 76 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P8_172 : block g191 8 172 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P8_268 : block g191 8 268 70=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P8_338 : block g191 8 338 84=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B8 : block g191 8 0 422=true := (@block_merge g191 8 0 172 250 (@block_merge g191 8 0 76 96 g191P8_0 g191P8_76) (@block_merge g191 8 172 96 154 g191P8_172 (@block_merge g191 8 268 70 84 g191P8_268 g191P8_338)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P9_0 : block g191 9 0 11=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P9_11 : block g191 9 11 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P9_107 : block g191 9 107 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P9_203 : block g191 9 203 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P9_299 : block g191 9 299 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P9_395 : block g191 9 395 50=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P9_445 : block g191 9 445 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P9_541 : block g191 9 541 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P9_637 : block g191 9 637 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P9_733 : block g191 9 733 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P9_765 : block g191 9 765 33=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B9 : block g191 9 0 798=true := (@block_merge g191 9 0 395 403 (@block_merge g191 9 0 107 288 (@block_merge g191 9 0 11 96 g191P9_0 g191P9_11) (@block_merge g191 9 107 96 192 g191P9_107 (@block_merge g191 9 203 96 96 g191P9_203 g191P9_299))) (@block_merge g191 9 395 242 161 (@block_merge g191 9 395 50 192 g191P9_395 (@block_merge g191 9 445 96 96 g191P9_445 g191P9_541)) (@block_merge g191 9 637 96 65 g191P9_637 (@block_merge g191 9 733 32 33 g191P9_733 g191P9_765))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P10_0 : block g191 10 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P10_3 : block g191 10 3 95=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P10_98 : block g191 10 98 88=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B10 : block g191 10 0 186=true := (@block_merge g191 10 0 3 183 g191P10_0 (@block_merge g191 10 3 95 88 g191P10_3 g191P10_98))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P11_0 : block g191 11 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P11_2 : block g191 11 2 16=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B11 : block g191 11 0 18=true := (@block_merge g191 11 0 2 16 g191P11_0 g191P11_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P12_0 : block g191 12 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B12 : block g191 12 0 1=true := g191P12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191T : checkedTables g191 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0 = true)
  · exact (rfl : block g191 1 0 0 = true)
  · exact (rfl : block g191 2 0 0 = true)
  · exact (rfl : block g191 3 0 0 = true)
  · exact (rfl : block g191 4 0 0 = true)
  · exact (rfl : block g191 5 0 0 = true)
  · exact g191B6
  · exact g191B7
  · exact g191B8
  · exact g191B9
  · exact g191B10
  · exact g191B11
  · exact g191B12
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191G : graphValid g191 (boundsBefore K127) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low191 : Lower true (varsX 191) (graphGoal 191) 13 := lower_forest (g:=g191) (i:=0) (hints:=4146) (before_sound K127 V127) g191G g191T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K191 := extendKnown K127 13 [(191,[]),(254,[96,81])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V191 : Known true K191 := extend_ok (m:=191) V127 low191 (by decide +kernel)
def g239Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x4e04095f440d000000,0xff0000ff0000ff00ff])),(BitVec.ofNat 152 (word80 [0x4000011e040d050505,0x5050505050505050505]))),((BitVec.ofNat 152 (word80 [0x60d9068ae849000000,0xff0000ff0000ff00ff00])),(BitVec.ofNat 152 (word80 [0x40c1020ac801030303,0x3030303030303030303]))),((BitVec.ofNat 152 (word80 [0x3026858e9a20000ff,0xff000000000000ff])),(BitVec.ofNat 152 (word80 [0x3006840e8a21a1a1a,0x1a1a1a1a1a1a1a1a1a1a]))),((BitVec.ofNat 152 (word80 [0x4b7a9000b4be000000,0xff0000ff00])),(BitVec.ofNat 152 (word80 [0xb1a8000349eacacac,0xacacacacacacacacacac]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xa420fe2403b000ff00,0xffffff0000])),(BitVec.ofNat 152 (word80 [0xa4207c200120505050,0x50505050505050505050]))),((BitVec.ofNat 152 (word80 [0xbc0950031552ff0000,0xffffff0000000000])),(BitVec.ofNat 152 (word80 [0xac0810011150606060,0x60606060606060606060]))),((BitVec.ofNat 152 (word80 [0x919621a01a05ffffff,0xffff0000000000000000])),(BitVec.ofNat 152 (word80 [0x101600800200808080,0x80808080808080808080]))),(0x0,0x0)]
def g239C : List ColumnInfo := [(1,0,238,0,10),(2,0,237,0,10),(8,0,231,0,10),(32,0,207,0,10),(64,0,175,0,10),(0,8,197,34,9),(4,0,235,0,9),(128,0,111,0,9)]
def g239A : List (List Nat) := [[],[96,81]]
def g239D10 := limbs80 #[#[0x775c8b91bc0ff58bdd63,0x19ee6b20]]
def g239D11 (j : Nat) := if j=0 then 0x3e8c843ff else 0
def g239H11 (j : Nat) := if j=0 then 0x45 else 0
def g239L : Nat → Packing
  | 10 => (2,1,3,0,0,5,0,g239D10)
  | 11 => (1,0,3,0,0,0,0,g239D11)
  | _ => emptyPacking
def g239I : Nat → Nat → Option (Nat × Nat)
  | 11 => lookupWord 1 2 0 5 1 0 g239H11
  | _ => fun _ => none
def g239 : Forest := ⟨239,11,fun i => g239Y[i]?.getD (0,0),g239C,g239A,g239L,g239I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P10_0 : block g239 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P10_1 : block g239 10 1 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B10 : block g239 10 0 2=true := (@block_merge g239 10 0 1 1 g239P10_0 g239P10_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P11_0 : block g239 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B11 : block g239 11 0 1=true := g239P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239T : checkedTables g239 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g239 0 0 0 = true)
  · exact (rfl : block g239 1 0 0 = true)
  · exact (rfl : block g239 2 0 0 = true)
  · exact (rfl : block g239 3 0 0 = true)
  · exact (rfl : block g239 4 0 0 = true)
  · exact (rfl : block g239 5 0 0 = true)
  · exact (rfl : block g239 6 0 0 = true)
  · exact (rfl : block g239 7 0 0 = true)
  · exact (rfl : block g239 8 0 0 = true)
  · exact (rfl : block g239 9 0 0 = true)
  · exact g239B10
  · exact g239B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239G : graphValid g239 (boundsBefore K191) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low239 : Lower true (varsX 239) (graphGoal 239) 12 := lower_forest (g:=g239) (i:=0) (hints:=4146) (before_sound K191 V191) g239G g239T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K239 := extendKnown K191 12 [(239,[]),(251,[66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V239 : Known true K239 := extend_ok (m:=239) V191 low239 (by decide +kernel)
def g247Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x84210184f2c6000000,0x3f800003f80fe03fff])),(BitVec.ofNat 152 (word80 [0x802000047006040810,0x20408102040810204081]))),((BitVec.ofNat 152 (word80 [0x58a03ed50852000000,0x1fc00001fc07f0000000])),(BitVec.ofNat 152 (word80 [0xa01cd508521c3870,0xe1c3870e1c3870e1c387]))),((BitVec.ofNat 152 (word80 [0x61c6c5d0130000000f,0xe00000fe0000001fc07f])),(BitVec.ofNat 152 (word80 [0x6182c59003002850a1,0x42850a142850a142850a]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x112c8c68ace80007f0,0x7f000000001fff80])),(BitVec.ofNat 152 (word80 [0x100408488ce850a142,0x850a142850a142850a14]))),((BitVec.ofNat 152 (word80 [0x5cd1cb23850c03f800,0x7ffe00000])),(BitVec.ofNat 152 (word80 [0x5c51c3228508e1c387,0xe1c3870e1c3870e1c38]))),((BitVec.ofNat 152 (word80 [0xaa493022092bfc0000,0x7ffffff800000000])),(BitVec.ofNat 152 (word80 [0xa4920220000810204,0x8102040810204081020]))),((BitVec.ofNat 152 (word80 [0x212401e4411ffffff,0xffff8000000000000000])),(BitVec.ofNat 152 (word80 [0x1020408,0x10204081020408102040]))),(0x0,0x0)]
def g247C : List ColumnInfo := [(2,0,245,0,11)]
def g247A : List (List Nat) := [[],[66],[96,81],[96,81,66]]
def g247D11 (j : Nat) := if j=0 then 0xff else 0
def g247L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g247D11)
  | _ => emptyPacking
def g247I (_ _ : Nat) : Option (Nat × Nat) := none
def g247 : Forest := ⟨247,11,fun i => g247Y[i]?.getD (0,0),g247C,g247A,g247L,g247I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P11_0 : block g247 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B11 : block g247 11 0 1=true := g247P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247T : checkedTables g247 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g247 0 0 0 = true)
  · exact (rfl : block g247 1 0 0 = true)
  · exact (rfl : block g247 2 0 0 = true)
  · exact (rfl : block g247 3 0 0 = true)
  · exact (rfl : block g247 4 0 0 = true)
  · exact (rfl : block g247 5 0 0 = true)
  · exact (rfl : block g247 6 0 0 = true)
  · exact (rfl : block g247 7 0 0 = true)
  · exact (rfl : block g247 8 0 0 = true)
  · exact (rfl : block g247 9 0 0 = true)
  · exact (rfl : block g247 10 0 0 = true)
  · exact g247B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247G : graphValid g247 (boundsBefore K239) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low247 : Lower true (varsX 247) (graphGoal 247) 12 := lower_forest (g:=g247) (i:=0) (hints:=82) (before_sound K239 V239) g247G g247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K247 := extendKnown K239 12 [(247,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V247 : Known true K247 := extend_ok (m:=247) V239 low247 (by decide +kernel)
def g255Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1ffc00000ffe,0x3ff800ffe000c61507])),(BitVec.ofNat 152 (word80 [0x280500a0140280500a,0x140280500a000421501]))),((BitVec.ofNat 152 (word80 [0xffe000007ff000,0x7ff00009301fc9d])),(BitVec.ofNat 152 (word80 [0x981302604c09813026,0x4c0981302609100f495]))),((BitVec.ofNat 152 (word80 [0x7ff00000000000001,0xffc00000ffe41c186cb2])),(BitVec.ofNat 152 (word80 [0x504a0941282504a094,0x1282504a0944140828b2]))),((BitVec.ofNat 152 (word80 [0x3ff800000,0x7ff000000018961])),(BitVec.ofNat 152 (word80 [0x652ca594b29652ca59,0x4b29652ca58024410940]))),((BitVec.ofNat 152 (word80 [0xf80000000000000001,0xfffff8000008e039f244])),(BitVec.ofNat 152 (word80 [0x80b01602c0580b0160,0x2c0580b01608a011c244]))),((BitVec.ofNat 152 (word80 [0x3fffffffe,0xf003e027a])),(BitVec.ofNat 152 (word80 [0x2c0580b01602c0580,0xb01602c0580d003c022a]))),((BitVec.ofNat 152 (word80 [0xfffffffffc00000000,0x1000200380])),(BitVec.ofNat 152 (word80 [0x300600c0180300600,0xc0180300600000200000]))),(0x1fffc00000,(BitVec.ofNat 152 (word80 [0x40080100200400801,0x20040080124a800000]))),(0x0,0x0)]
def g255C : List ColumnInfo := [(1,0,254,0,13),(64,0,191,0,13),(0,8,213,34,12),(4,0,251,0,12),(8,0,247,0,12),(16,0,239,0,12),(128,0,127,0,12),(2,8,213,32,11),(10,0,245,0,11),(6,0,249,0,10),(12,0,243,0,10),(18,0,237,0,10),(24,0,231,0,10),(34,8,213,0,10),(42,0,213,0,10),(130,0,125,0,10),(20,0,235,0,9),(132,0,123,0,9),(144,0,111,0,9),(0,4,42,209,8),(22,0,233,0,7),(128,16,42,69,7),(134,0,121,0,7),(146,0,109,0,7),(65,4,42,144,6),(129,4,42,80,6),(144,4,42,65,6),(148,0,107,0,6),(69,16,42,128,5),(81,4,42,128,5),(104,2,21,128,5),(133,16,42,64,5),(145,4,42,64,5),(149,0,106,0,5),(193,4,42,16,5),(212,0,43,0,5)]
def g255A : List (List Nat) := [[],[66],[96,81],[96,81,66]]
def g255D10 := limbs80 #[#[0x745c921f695d17250521,0x1e6b5d172e0542e6b611,0x5945c921f79685745c92,0x21cfde85985d121bf9e8,0x859461d21afde8597611,0x942f6b5d17260542afde,0xc772b0ac00f6b5d1915c,0x10730d23f1cad360a811,0x18e34804811f010b827c,0x74d1810c0c14f0246f05,0x258d0704043c003fc108,0x60641e1ac5634220c164,0x8305019078305c1461c1,0xc100534d86040582007,0x16b3618]]
def g255D11 := limbs80 #[#[0xfcae4a0a43dad745c942,0xfac22e290efd61d41487,0xdb08b9243ded745c921d,0xfcbb0890cff661744877,0xae5c0a853ff9461d219f,0xc8b0ea14ff65f8150b7d,0x29c0ae53fd91e1d429ff,0xa2e490cff647845ca7fb,0xba243ff5915d121ff6c,0x30e90eff65d844877fb3,0xa12e3ff59150971dfeca,0x2a17fb5c98150b7fb30,0x3a85fed915c942dfec3b,0xea16ff6458750afff22c,0xae5dfd7460572dffc8b0,0x5ffe45845cb7fb08c0,0xa343ba6189c0ea13815c,0x7768e05a730959aa6933,0x3b56292ce093715a0d3e,0xbc3636a5cc18b701dd0b,0x85e204a07c0e0f349e35,0xb1813c0e0c2e1a384420,0x216e003f830b0ec38808,0x585013c00ff061f0d201,0x24c508f0383090ee3480,0x4b1429c0e0d183b8d24,0xb1017a3703821dc69210,0x2c2b1b81c1c685050a05,0xe0704214d158bc0e0e34,0x68ec6087038221a68c4f,0x9a14170b83a370382216,0xe0704221ca68b46e0705],#[0x2e34442d1781c1668585,0x1e0b09234341c1820126,0xc385c2c840a51b1a1c1c,0x7870bb1184160a0643,0xa08d110a176230828161,0x4250c2c15c6860705824,0x68605080269a14110a17,0x8a09668583a260d8c14a,0x8156686070360f80cd11,0x1d1380cd1186170b0518,0x3140a16a687440785a9a,0x183097019a2]]
def g255H11 := limbs80 #[#[0x965c65040001d40028,0x1290000000000000,0x28000132880001400000,0x7200000009b0c00ee4,0xe840000000710,0x2c200000000]]
def g255D12 := limbs80 #[#[0x5c921ff571487fd50521,0x50aff61d21bfd84487fb,0xfdd7350bfb5c942bff81,0xe1d42bfd8750bf79cd42,0x5cb7f5d172bff815caff,0xffd425c7ff5d121bff84,0x60572ffd8750bff60542,0x441901b000ffd845cbff,0x9f1131f03745d09f0f01,0x2133d8734d71932e0564,0x141f03042c2438699521,0x7011b06347c0c1090f0d,0x80bc609c0c18d2714442,0x2027143f030634914108,0x484806c0c1104d185846,0x14d1844402a1703051b3,0xd1b0305386858346c0c,0x1083858a46c0c1cd2a16,0xd14111b0307344061211,0x1703060f34805c0c1114,0x445c0c1cd111b104845,0xf8d1c49151b030636247,0x30534509104543c0c18,0xc0c1cd102c402d20271b,0x534588831b131211c446,0xc1cd112c443c2717030,0x831b131210454cc]]
def g255H12 := limbs80 #[#[0x9801211d100d04387040,0x963931558e81f3b91850,0x281c5cc613d98adb0909,0x3000000001f38004156,0x2d480072c55624cdd001,0xd689001490fe00000000,0xd1c000007970000006,0x1190007cf220003e58,0xc000e23d7d1f646c5d0a,0xc0ed88400641986800fa,0xcd800810217d280020e4,0xd21001c082e05817857b,0x4a2e3cc692c]]
def g255D13 := limbs80 #[#[0x2ffae3ff487ef39fdd73,0xb1d2e6018003feb97fd4,0x823868b0c3408234682,0x88d16041123478b0c34,0xe0419a445870208f1a3,0x9143038106690402c618,0x118]]
def g255H13 := limbs80 #[#[0x78f000000037c4,0x5180000000000,0x343000000000000000,0xd1c00000000000000,0x49600000000704002a9,0x6870a00000000,0x0,0x610,0x0,0x0,0x1403e1000000000000,0x0,0x0,0x0,0xe28,0x11b80070511a00000,0x120000000000000,0x1004000000,0x203001c1000000c12,0x15c00,0xc4400000d43c2c0,0xe20000000,0x4f924a98e2b93]]
def g255D14 (j : Nat) := if j=0 then 0x106143001347ff else 0
def g255H14 := limbs80 #[#[0x25007e800000000000c1,0x66000000000002940000,0x2440000000,0x2d350000000000,0x6000000000000,0x92000000000000000]]
def g255L : Nat → Packing
  | 10 => (10,4,6,0,0,9,0,g255D10)
  | 11 => (31,3,6,0,0,11,0,g255D11)
  | 12 => (20,2,6,0,0,11,0,g255D12)
  | 13 => (6,1,6,0,0,9,0,g255D13)
  | 14 => (1,0,6,0,0,0,0,g255D14)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 11 => lookupWord 4 43 3 10 4 2 g255H11
  | 12 => lookupWord 15 83 6 11 5 2 g255H12
  | 13 => lookupWord 8 173 0 11 5 2 g255H13
  | 14 => lookupWord 2 59 0 9 3 2 g255H14
  | _ => fun _ => none
def g255 : Forest := ⟨255,14,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_0 : block g255 10 0 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_3 : block g255 10 3 7=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B10 : block g255 10 0 10=true := (@block_merge g255 10 0 3 7 g255P10_0 g255P10_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_0 : block g255 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_1 : block g255 11 1 14=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_15 : block g255 11 15 16=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B11 : block g255 11 0 31=true := (@block_merge g255 11 0 1 30 g255P11_0 (@block_merge g255 11 1 14 16 g255P11_1 g255P11_15))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_0 : block g255 12 0 14=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_14 : block g255 12 14 6=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B12 : block g255 12 0 20=true := (@block_merge g255 12 0 14 6 g255P12_0 g255P12_14)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P13_0 : block g255 13 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P13_2 : block g255 13 2 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B13 : block g255 13 0 6=true := (@block_merge g255 13 0 2 4 g255P13_0 g255P13_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P14_0 : block g255 14 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B14 : block g255 14 0 1=true := g255P14_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255T : checkedTables g255 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g255 0 0 0 = true)
  · exact (rfl : block g255 1 0 0 = true)
  · exact (rfl : block g255 2 0 0 = true)
  · exact (rfl : block g255 3 0 0 = true)
  · exact (rfl : block g255 4 0 0 = true)
  · exact (rfl : block g255 5 0 0 = true)
  · exact (rfl : block g255 6 0 0 = true)
  · exact (rfl : block g255 7 0 0 = true)
  · exact (rfl : block g255 8 0 0 = true)
  · exact (rfl : block g255 9 0 0 = true)
  · exact g255B10
  · exact g255B11
  · exact g255B12
  · exact g255B13
  · exact g255B14
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255G : graphValid g255 (boundsBefore K247) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 14 sevenInputs.toFinset := by
  rw [show graph = targetOf g255 by decide +kernel]
  exact root_index (g:=g255) (top:=14) (i:=0) (before_sound K247 V247) g255G g255T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_52624

open PEqualNP.Outside.L_meta_52624 in
theorem PEqualNP.Outside.L_meta_52624 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort g255R gates o fit correct
