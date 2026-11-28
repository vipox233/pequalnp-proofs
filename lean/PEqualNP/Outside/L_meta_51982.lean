import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_51982.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_51982
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xfffffffeffffffffffff,0xffeefffffffefffffffa,0xffffffeefefeaa00ffff,0xfffffffffffeffffffff,0xffffffeefffffffeffff,0xfffaffffffeefefeaa00]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) || (x 4 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 5 && x 7)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

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
theorem reach_up {R u} {roots : List (Wire R)} {p bank} (h : Reach false roots p bank) : Reach u roots p bank := by
  have up {bank : List (Wire R)} {a} (h : Available false bank a) : Available u bank a :=
    h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
  induction h using Reach.ind with
  | start => exact Reach.start
  | two op h ha hb ih => exact Reach.two op ih (up ha) (up hb)
theorem lower_down {u roots T L} (h : Lower true roots T L) : Lower u roots T L := by
  cases u
  · exact fun p bank hr ha => h p bank (reach_up hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
  · exact h

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

def poolCut (u : Bool) (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB u d pool)

theorem poolCut_sound {u raw T d L} (slice : Slice u raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool u d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut u d L cap cs.length pool ws = true) :
    Impossible u T cap ws.toFinset := by
  intro k hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply u bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega



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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 4 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7)
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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 4 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7)
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

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
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

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
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
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
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
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
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

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
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
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h


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
theorem known_down {u es} (h : Known true es) : Known u es := fun e he => lower_down (h e he)
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
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) (h : linkAt fl (laneOf c) i j op ka kb=true) :
    (c.2.2.2.2.2 (keySet (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))).any (sameWords
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
    obtain ⟨xs,hx,rfl⟩ := hfl t ys hf
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
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
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
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
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
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
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
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
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
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov g.mode ws,rules,ls)


theorem flOf_ok (g : Forest) (k i tag : Nat) (ys) (h : flOf g k tag=some ys) :
    ∃ xs ∈ (contextOf g k i).2.2.2.2.2 tag, ys=xs.map BitVec.toNat := by
  change ∃ xs ∈ ((g.index k tag).bind (linkedSet g (k-1))).toList, _
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
  have hfl : ∀ tag ys, flOf g k tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat := by
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

def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d ∧ listPieces f (xs.drop (xs.length/2)) d
theorem pieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
theorem slice_self {u} {raw : List Sig} {T : Sig} {L : Nat} (pT : proper T) (h : Lower u raw T L) :
    Slice u raw T one L := by
  refine ⟨id,raw,fun r => bit_one r,fun a ha => ?_,observe_proper pT,h⟩
  exact Or.inl (List.mem_map_of_mem ha)

theorem plainA {u} {m q cap : Nat} {prior : Nat → Nat} (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (e : (graphGoal q == graphGoal m && (varsX q == vars m) && (prior q == cap+1) && properB (graphGoal m) &&
      decide (vars m).Nodup && poolCut u one (cap+1) cap 0 (vars m) (vars m)) = true) :
    Impossible u (graphGoal m) cap (vars m).toFinset := by
  simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at e
  obtain ⟨⟨⟨⟨⟨e1,e2⟩,e3⟩,e4⟩,e5⟩,e6⟩ := e
  have h := low q
  rw [e1,e2,e3] at h
  exact poolCut_sound (slice_self (proper_of _ e4) h) [] rfl e5 e6

theorem cut_root {u} {m cap : Nat} {prior : Nat → Nat} {ws : List Sig}
    (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q)) (ci : ColumnInfo)
    (ok : colCheck m ci prior = true)
    (cut : (decide ws.Nodup && poolCut u (subcube ci.1 ci.2.1) ci.2.2.2.2 cap 0 (varsX (rawMask m ci)) ws)=true) :
    Impossible u (graphGoal m) cap ws.toFinset := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  exact poolCut_sound (col_sound ci prior low ok) [] rfl cut.1 cut.2

theorem index_root {u} {g : Forest} {m cap i : Nat} {prior : Nat → Nat} {ws : List Sig}
    (hm : g.mask=m) (hu : g.mode=u) (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g cap)
    (idx : indexedRoot g cap i ws = true) : Impossible u (graphGoal m) cap ws.toFinset := by
  subst hm
  subst hu
  exact root_index low geom blocks (Nat.le_refl _) idx

def essOK (m hints : Nat) : Bool :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs && (xs.map Prod.fst == vars m)
theorem plain_low {u} {m hints cap : Nat} (ok : essOK m hints = true)
    (a : Impossible u (graphGoal m) cap (vars m).toFinset) : Lower u (vars m) (graphGoal m) (cap+1) := by
  simp only [essOK,Bool.and_eq_true,beq_iff_eq] at ok
  apply lower_impossible (proper_of _ ok.1.1) (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 _ a
  intro v hv
  apply essential_ok ok.1.2 v
  rw [ok.2]
  exact List.mem_toFinset.mpr hv



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[3,4]⟩,⟨.or,[0,8]⟩,⟨.or,[1,2]⟩,⟨.or,[1,9]⟩,⟨.or,[2,9]⟩,⟨.or,[5,8]⟩,⟨.or,[0,7]⟩,⟨.or,[5,7]⟩,⟨.and,[6,12]⟩,⟨.and,[15,11]⟩,⟨.and,[14,13]⟩,⟨.and,[4,10]⟩,⟨.or,[16,17]⟩,⟨.or,[20,18]⟩,⟨.or,[21,19]⟩], 22⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : smallCircuit.gates.length = 15 := rfl

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

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([3, 4, 4, 0, 0, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([3, 4, 4, 0, 0, 0, 0, 0] : List Nat).getD i.val 0))

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
    (lower : Impossible true graph 13 sevenInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 8 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 8 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 15 ≤ gates.length
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
def g41Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ff63ff63ff63ff63f,0xf63ff63ff63ff63ff63f])),(BitVec.ofNat 152 (word80 [0x492049204920492049,0x20492049204920492049]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc7fbc7fbc7fbc7fbc7,0xfbc7fbc7fbc7fbc7fbc7])),(BitVec.ofNat 152 (word80 [0x924092409240924092,0x40924092409240924092]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf8fdf8fdf8fdf8fdf8,0xfdf8fdf8fdf8fdf8fdf8])),(BitVec.ofNat 152 (word80 [0x248124812481248124,0x81248124812481248124]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g41C : List ColumnInfo := []
def g41A : List (List Nat) := [[],[83],[48],[48,80],[80,48],[80]]
def g41D3 (j : Nat) := if j=0 then 0x7 else 0
def g41L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g41D3)
  | _ => emptyPacking
def g41I (_ _ : Nat) : Option (Nat × Nat) := none
def g41 : Forest := ⟨41,3,fun i => g41Y[i]?.getD (0,0),g41C,g41A,g41L,g41I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g41P3_0 : block g41 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g41B3 : block g41 3 0 1=true := g41P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g41T : checkedTables g41 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g41 0 0 0 = true)
  · exact (rfl : block g41 1 0 0 = true)
  · exact (rfl : block g41 2 0 0 = true)
  · exact g41B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g41G : graphValid g41 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low41 : Lower true (varsX 41) (graphGoal 41) 4 := lower_forest (g:=g41) (i:=0) (hints:=3) (before_sound [] baseKnown) g41G g41T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K41 := extendKnown [] 4 [(41,[]),(49,[67]),(50,[16,67]),(73,[101]),(81,[67,101]),(84,[32,16,67,101]),(137,[117,101]),(161,[83,67,116,100]),(162,[16,83,67,116,100]),(168,[48,16,33,82,66,116,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V41 : Known true K41 := extend_ok (m:=41) baseKnown low41 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low23 : Lower true (varsX 23) (graphGoal 23) 3 := by
  have q := @lower_count true (vars 23) (graphGoal 23) (proper_of _ (by decide +kernel)) (graphPairs 23 1092) (by decide +kernel)
  exact q
def K23 := extendKnown K41 3 [(23,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V23 : Known true K23 := extend_ok (m:=23) V41 low23 (by decide +kernel)
def g27Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe6de3fff03fff1ffe6,0xde3fff03fff1ffe6de3f])),(BitVec.ofNat 152 (word80 [0x648490a2850240206,0x48490a28502402064849]))),((BitVec.ofNat 152 (word80 [0x19e9c0fffc07fe3f19,0xe9c0fffc07fe3f19e9c0])),(BitVec.ofNat 152 (word80 [0x50e8db2c3161408450,0xe8db2c3161408450e8db]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xece607fffff8003fec,0xe607fffff8003fece607])),(BitVec.ofNat 152 (word80 [0x8a7b6b04185892808,0xa7b6b04185892808a7b6]))),((BitVec.ofNat 152 (word80 [0x1b3df8ffffffffc01b,0x3df8ffffffffc01b3df8])),(BitVec.ofNat 152 (word80 [0x891524c08206003089,0x1524c082060030891524]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g27C : List ColumnInfo := []
def g27A : List (List Nat) := [[],[64,49]]
def g27D3 (j : Nat) := if j=0 then 0xf else 0
def g27L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g27D3)
  | _ => emptyPacking
def g27I (_ _ : Nat) : Option (Nat × Nat) := none
def g27 : Forest := ⟨27,3,fun i => g27Y[i]?.getD (0,0),g27C,g27A,g27L,g27I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27P3_0 : block g27 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g27B3 : block g27 3 0 1=true := g27P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27T : checkedTables g27 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g27 0 0 0 = true)
  · exact (rfl : block g27 1 0 0 = true)
  · exact (rfl : block g27 2 0 0 = true)
  · exact g27B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27G : graphValid g27 (boundsBefore K23) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low27 : Lower true (varsX 27) (graphGoal 27) 4 := lower_forest (g:=g27) (i:=0) (hints:=67) (before_sound K23 V23) g27G g27T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K27 := extendKnown K23 4 [(27,[]),(29,[33]),(60,[80,33,16]),(99,[99,84,67]),(101,[33,83,100]),(106,[48,32,98,84,66]),(108,[48,33,16,81,100]),(156,[112,33,16,81,101]),(195,[99,116,83,84]),(197,[33,115,100,83]),(202,[48,32,98,116,82,84]),(204,[48,33,16,113,100,81])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V27 : Known true K27 := extend_ok (m:=27) V23 low27 (by decide +kernel)
def g43Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfdf00fff81fc7e3ffb,0xe01fff03f8fc7ff7c03f])),(BitVec.ofNat 152 (word80 [0x45c09245142904808b,0x81248a28520901170249]))),((BitVec.ofNat 152 (word80 [0xe6a8703ffe007fc7cd,0x50e07ffc00ff8f9aa1c0])),(BitVec.ofNat 152 (word80 [0x96a9b6d618b228112d,0x536dac316450225aa6db]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfbb781ffffff8007f7,0x6f03ffffff000feede07])),(BitVec.ofNat 152 (word80 [0x235249820c0312204,0x6a49304180624408d492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x64ffe3ffffffff80c,0x9ffc7ffffffff0193ff8])),(BitVec.ofNat 152 (word80 [0x249204100400400,0x4924082008008000924]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g43C : List ColumnInfo := [(2,0,41,0,4)]
def g43A : List (List Nat) := [[],[48]]
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
theorem g43G : graphValid g43 (boundsBefore K27) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low43 : Lower true (varsX 43) (graphGoal 43) 5 := lower_forest (g:=g43) (i:=0) (hints:=83) (before_sound K27 V27) g43G g43T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K43 := extendKnown K27 5 [(43,[]),(53,[33,83,67]),(54,[16,32,83,67]),(58,[16,48,32,66]),(77,[33,101]),(83,[99,67,84]),(86,[32,99,67,84]),(92,[32,49,65,101]),(114,[16,96,32,83,66,67]),(116,[32,81,99,65]),(139,[117,101]),(154,[16,48,32,66,117,101]),(210,[16,96,32,115,66,84,83]),(212,[32,113,99,65,84]),(225,[80,97,33,115,66,67]),(232,[80,97,32,115,65,50,66]),(240,[80,97,32,115,65,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V43 : Known true K43 := extend_ok (m:=43) V27 low43 (by decide +kernel)
def g51Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe7d01c7fc0fc7cfe7,0xd01c7fc0fc7cfe7d01c7])),(BitVec.ofNat 152 (word80 [0x51d124928a290a051,0xd124928a290a051d1249]))),((BitVec.ofNat 152 (word80 [0x3f8b8e38fff007f3f8,0xb8e38fff007f3f8b8e38])),(BitVec.ofNat 152 (word80 [0x884b924930c3210884,0xb924930c3210884b9249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fe7703ffffff803fe,0x7703ffffff803fe7703f])),(BitVec.ofNat 152 (word80 [0x100024924104020100,0x2492410402010002492]))),((BitVec.ofNat 152 (word80 [0xc018ffc0fffffffc01,0x8ffc0fffffffc018ffc0])),(BitVec.ofNat 152 (word80 [0x200049248208040200,0x4924820804020004924]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g51C : List ColumnInfo := [(1,0,50,0,4)]
def g51A : List (List Nat) := [[],[84],[16],[16,84]]
def g51D4 (j : Nat) := if j=0 then 0x1f else 0
def g51L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g51D4)
  | _ => emptyPacking
def g51I (_ _ : Nat) : Option (Nat × Nat) := none
def g51 : Forest := ⟨51,4,fun i => g51Y[i]?.getD (0,0),g51C,g51A,g51L,g51I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g51P4_0 : block g51 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g51B4 : block g51 4 0 1=true := g51P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g51T : checkedTables g51 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g51 0 0 0 = true)
  · exact (rfl : block g51 1 0 0 = true)
  · exact (rfl : block g51 2 0 0 = true)
  · exact (rfl : block g51 3 0 0 = true)
  · exact g51B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g51G : graphValid g51 (boundsBefore K43) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low51 : Lower true (varsX 51) (graphGoal 51) 5 := lower_forest (g:=g51) (i:=0) (hints:=68) (before_sound K43 V43) g51G g51T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K51 := extendKnown K43 5 [(51,[]),(57,[48,65,33,32]),(85,[33,101]),(89,[48,65,33,32,101]),(113,[80,97,33,50,64]),(147,[117,101]),(153,[48,65,33,32,117,101]),(163,[84,116,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V51 : Known true K51 := extend_ok (m:=51) V43 low51 (by decide +kernel)
def g169Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xdf7ec03c3ffe0fbefd,0x80787ffc1f7dfb00f0ff])),(BitVec.ofNat 152 (word80 [0x820404444444210408,0x8888888420810111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fbf43c3c3fff03f7e,0x878787ffe07efd0f0f0f])),(BitVec.ofNat 152 (word80 [0x40808888888420810,0x11111110841020222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe03fbc03fc3fffc07f,0x7807f87fff80fef00ff0])),(BitVec.ofNat 152 (word80 [0x81011111110841020,0x22222221082040444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffc03ffc003fffff80,0x7ff8007fffff00fff000])),(BitVec.ofNat 152 (word80 [0x102022222221082040,0x44444442104080888888]))),(0x0,0x0)]
def g169C : List ColumnInfo := [(1,0,168,0,4),(8,0,161,0,4),(32,0,137,0,4),(128,0,41,0,4)]
def g169A : List (List Nat) := [[],[117],[83],[83,115],[115,83],[115],[48],[48,117],[48,80],[48,80,112],[48,112,80],[48,112],[80,48],[80,48,115],[80],[80,112],[80,115],[80,115,48],[112,48,83],[112,48],[112,80],[112],[112,83,48],[112,83]]
def g169D3 := limbs80 #[#[0x23ea6a1221e12148110,0x8028]]
def g169D4 := limbs80 #[#[0x2fd0910bd42443e48110,0x609085870]]
def g169H4 (j : Nat) := if j=0 then 0x22e else 0
def g169D5 (j : Nat) := if j=0 then 0xd1027d10 else 0
def g169H5 := limbs80 #[#[0xa00716920c004c5720,0x241410000]]
def g169D6 (j : Nat) := if j=0 then 0x3904f else 0
def g169H6 := limbs80 #[#[0x0,0x88274228000000002a0,0x281]]
def g169L : Nat → Packing
  | 3 => (2,3,2,0,0,5,0,g169D3)
  | 4 => (3,2,2,0,0,5,0,g169D4)
  | 5 => (1,1,2,0,0,0,0,g169D5)
  | 6 => (1,0,2,0,0,0,0,g169D6)
  | _ => emptyPacking
def g169I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 2 0 5 1 0 g169H4
  | 5 => lookupWord 2 13 3 9 2 3 g169H5
  | 6 => lookupWord 1 23 0 9 0 5 g169H6
  | _ => fun _ => none
def g169 : Forest := ⟨169,6,fun i => g169Y[i]?.getD (0,0),g169C,g169A,g169L,g169I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g169P3_0 : block g169 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g169B3 : block g169 3 0 2=true := g169P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g169P4_0 : block g169 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g169B4 : block g169 4 0 3=true := g169P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g169P5_0 : block g169 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g169B5 : block g169 5 0 1=true := g169P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g169P6_0 : block g169 6 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g169B6 : block g169 6 0 1=true := g169P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g169T : checkedTables g169 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g169 0 0 0 = true)
  · exact (rfl : block g169 1 0 0 = true)
  · exact (rfl : block g169 2 0 0 = true)
  · exact g169B3
  · exact g169B4
  · exact g169B5
  · exact g169B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g169G : graphValid g169 (boundsBefore K51) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low169 : Lower true (varsX 169) (graphGoal 169) 7 := lower_forest (g:=g169) (i:=0) (hints:=3) (before_sound K51 V51) g169G g169T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K169 := extendKnown K51 7 [(169,[]),(177,[67]),(178,[16,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V169 : Known true K169 := extend_ok (m:=169) V51 low169 (by decide +kernel)
def g31Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf8003ffe00fff803ff,0xfffffffffffb5d61e03f])),(BitVec.ofNat 152 (word80 [0x501a80941a02905828,0x540940a414940616249]))),((BitVec.ofNat 152 (word80 [0xffffc00000fffffc01,0xffe001ffe008a3d3c1c0])),(BitVec.ofNat 152 (word80 [0x61530ad8ac2b22914c,0x2986d84c8668a351c6db]))),((BitVec.ofNat 152 (word80 [0xffffffffff00000001,0xfffffe000004e42dde00])),(BitVec.ofNat 152 (word80 [0x819c0ce13033c4e270,0x4e04e06f0b84e429c6db]))),((BitVec.ofNat 152 (word80 [1,0xfffffffffff22feda007])),(BitVec.ofNat 152 (word80 [0x5e02f01c0bc070381,0x701701700c022f8c8db6]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffffffe,0xdfa9e5ff8])),(BitVec.ofNat 152 (word80 [0x600300000c0000001,0x80180180100018861924]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g31C : List ColumnInfo := [(2,0,29,0,4)]
def g31A : List (List Nat) := [[],[33]]
def g31D4 (j : Nat) := if j=0 then 0x3f else 0
def g31L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g31D4)
  | _ => emptyPacking
def g31I (_ _ : Nat) : Option (Nat × Nat) := none
def g31 : Forest := ⟨31,4,fun i => g31Y[i]?.getD (0,0),g31C,g31A,g31L,g31I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P4_0 : block g31 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B4 : block g31 4 0 1=true := g31P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31T : checkedTables g31 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact g31B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31G : graphValid g31 (boundsBefore K169) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low31 : Lower true (varsX 31) (graphGoal 31) 5 := lower_forest (g:=g31) (i:=0) (hints:=1091) (before_sound K169 V169) g31G g31T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K31 := extendKnown K169 5 [(31,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V31 : Known true K31 := extend_ok (m:=31) V169 low31 (by decide +kernel)
def g55Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc01ffffc0ffff00,0x3ff01ff80ffae2c80e07])),(BitVec.ofNat 152 (word80 [0xa0a8d44a1496502a1a,0x84a342916290e2c89249]))),((BitVec.ofNat 152 (word80 [0xffffe00ffff03ffff,0xc0001ffff0054b9c7038])),(BitVec.ofNat 152 (word80 [0xc130986c1924984c13,0x6c5832244c44a9c9249]))),((BitVec.ofNat 152 (word80 [0xfffffff000003ffff,0xffffe00000196cb001c0])),(BitVec.ofNat 152 (word80 [0x9c0e0709e38e2709c,0x270613c387196cb2db6d]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf0000000000003ffff,0xffffffffffe47e6381ff])),(BitVec.ofNat 152 (word80 [0x20100802000008020,0x8000400000000012492]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x1b91bffe00])),(BitVec.ofNat 152 (word80 [0xc020100c0000300c0,0x30081804080b11224924]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g55C : List ColumnInfo := [(1,0,54,0,5)]
def g55A : List (List Nat) := [[],[16]]
def g55D5 (j : Nat) := if j=0 then 0x3f else 0
def g55L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g55D5)
  | _ => emptyPacking
def g55I (_ _ : Nat) : Option (Nat × Nat) := none
def g55 : Forest := ⟨55,5,fun i => g55Y[i]?.getD (0,0),g55C,g55A,g55L,g55I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55P5_0 : block g55 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g55B5 : block g55 5 0 1=true := g55P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55T : checkedTables g55 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g55 0 0 0 = true)
  · exact (rfl : block g55 1 0 0 = true)
  · exact (rfl : block g55 2 0 0 = true)
  · exact (rfl : block g55 3 0 0 = true)
  · exact (rfl : block g55 4 0 0 = true)
  · exact g55B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55G : graphValid g55 (boundsBefore K31) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (varsX 55) (graphGoal 55) 6 := lower_forest (g:=g55) (i:=0) (hints:=1092) (before_sound K31 V31) g55G g55T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K55 := extendKnown K31 6 [(55,[]),(87,[33,101]),(151,[117,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V55 : Known true K55 := extend_ok (m:=55) V31 low55 (by decide +kernel)
def g59Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff00ff87f87ffc0,0x7fff8fffd8b95000f0ff])),(BitVec.ofNat 152 (word80 [0x1440a0a05101100285,0x5012008488941111111]))),((BitVec.ofNat 152 (word80 [0x1ffff0007ff87fff,0x807ff1fc2b1e600f0f00])),(BitVec.ofNat 152 (word80 [0x5882c0c1620a010b06,0x160a0411291e43333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffff80007fff,0xff8001ff941fb0f0000f])),(BitVec.ofNat 152 (word80 [0x610b0505802c222c08,0x182c48a01416b6666666]))),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06060430443010,0x203000c20260b4444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008080040004020,0x40400100000008888888]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g59C : List ColumnInfo := [(1,0,58,0,5),(2,0,57,0,5),(8,0,51,0,5),(16,0,43,0,5)]
def g59A : List (List Nat) := [[],[64,49]]
def g59D6 (j : Nat) := if j=0 then 0x4e09f else 0
def g59L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g59D6)
  | _ => emptyPacking
def g59I (_ _ : Nat) : Option (Nat × Nat) := none
def g59 : Forest := ⟨59,6,fun i => g59Y[i]?.getD (0,0),g59C,g59A,g59L,g59I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P6_0 : block g59 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B6 : block g59 6 0 1=true := g59P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59T : checkedTables g59 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g59 0 0 0 = true)
  · exact (rfl : block g59 1 0 0 = true)
  · exact (rfl : block g59 2 0 0 = true)
  · exact (rfl : block g59 3 0 0 = true)
  · exact (rfl : block g59 4 0 0 = true)
  · exact (rfl : block g59 5 0 0 = true)
  · exact g59B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59G : graphValid g59 (boundsBefore K55) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low59 : Lower true (varsX 59) (graphGoal 59) 7 := lower_forest (g:=g59) (i:=0) (hints:=67) (before_sound K55 V55) g59G g59T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K59 := extendKnown K55 7 [(59,[]),(93,[33,101]),(115,[99,84]),(117,[33,83,100,67]),(155,[117,101]),(211,[99,116,84]),(213,[33,115,100,84,83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V59 : Known true K59 := extend_ok (m:=59) V55 low59 (by decide +kernel)
def g61Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc03ff0fffffc03f,0xfff0fffff5560300f0ff])),(BitVec.ofNat 152 (word80 [0x2028280a2020028281,0x40220020900603111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc000ff0ffffc0,0x1fff0ff014b579000f00])),(BitVec.ofNat 152 (word80 [0x48b0322c41428b2325,0x9140284214b551bbbbbb]))),((BitVec.ofNat 152 (word80 [0xffffffff000ffffff,0xe0000fff2bb5260f000f])),(BitVec.ofNat 152 (word80 [0x82c140b005842c0406,0x58442802b9120666666]))),((BitVec.ofNat 152 (word80 [0xf00000000000ffffff,0xfffff000134bf8f00ff0])),(BitVec.ofNat 152 (word80 [0x30180c08608300808,0x6000304034828444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc0203000800c03030,0x18088c084420c4888888]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g61C : List ColumnInfo := [(0,4,41,16,5),(4,0,57,0,5),(8,0,53,0,5),(1,0,60,0,4),(16,4,41,0,4),(32,0,29,0,4)]
def g61A : List (List Nat) := [[],[80]]
def g61D4 (j : Nat) := if j=0 then 0x5bd4940 else 0
def g61D5 (j : Nat) := if j=0 then 0xc8404fd40 else 0
def g61H5 (j : Nat) := if j=0 then 0x70 else 0
def g61D6 (j : Nat) := if j=0 then 0x2b2a0bf else 0
def g61H6 (j : Nat) := if j=0 then 0xe else 0
def g61L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g61D4)
  | 5 => (1,1,3,0,0,0,0,g61D5)
  | 6 => (1,0,3,0,0,0,0,g61D6)
  | _ => emptyPacking
def g61I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g61H5
  | 6 => lookupWord 1 2 0 4 0 0 g61H6
  | _ => fun _ => none
def g61 : Forest := ⟨61,6,fun i => g61Y[i]?.getD (0,0),g61C,g61A,g61L,g61I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P4_0 : block g61 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g61B4 : block g61 4 0 1=true := g61P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P5_0 : block g61 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g61B5 : block g61 5 0 1=true := g61P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P6_0 : block g61 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g61B6 : block g61 6 0 1=true := g61P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61T : checkedTables g61 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g61 0 0 0 = true)
  · exact (rfl : block g61 1 0 0 = true)
  · exact (rfl : block g61 2 0 0 = true)
  · exact (rfl : block g61 3 0 0 = true)
  · exact g61B4
  · exact g61B5
  · exact g61B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61G : graphValid g61 (boundsBefore K59) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low61 : Lower true (varsX 61) (graphGoal 61) 7 := lower_forest (g:=g61) (i:=0) (hints:=1027) (before_sound K59 V59) g61G g61T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K61 := extendKnown K59 7 [(61,[]),(91,[33,101]),(107,[33,99,84,67]),(109,[83,100]),(157,[117,101]),(188,[80,16,113,97]),(203,[33,99,116,83,84]),(205,[115,100,83]),(227,[80,33,97,49,64,116]),(234,[80,16,98,49,67,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V61 : Known true K61 := extend_ok (m:=61) V59 low61 (by decide +kernel)
def g62Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7ff003ff80fffffff0,0x3ffffe03ff4b19901c7])),(BitVec.ofNat 152 (word80 [0x2a1a8251a148a02a1,0xa84a0a458a44b1811249]))),((BitVec.ofNat 152 (word80 [0x7ffffc0000ffc07fff,0xfc00ffffc068db260038])),(BitVec.ofNat 152 (word80 [0x44c132362c191344c9,0x326c8c891360d3265b6d]))),((BitVec.ofNat 152 (word80 [0x7fffffffff00007fff,0xffff0000000ff00e8e00])),(BitVec.ofNat 152 (word80 [0x1705c0b8305e1c1701,0xc0702f0e1c0db00eb6db]))),((BitVec.ofNat 152 (word80 [0x800000000000007fff,0xffffffffff99af6d703f])),(BitVec.ofNat 152 (word80 [0x180600c04060201802,0x80300000190c082492]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6754f2ffc0])),(BitVec.ofNat 152 (word80 [0x60080300008000600c,0x300c010202240704924]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g62C : List ColumnInfo := [(4,0,58,0,5)]
def g62A : List (List Nat) := [[],[50,84]]
def g62D5 (j : Nat) := if j=0 then 0x3f else 0
def g62L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g62D5)
  | _ => emptyPacking
def g62I (_ _ : Nat) : Option (Nat × Nat) := none
def g62 : Forest := ⟨62,5,fun i => g62Y[i]?.getD (0,0),g62C,g62A,g62L,g62I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62P5_0 : block g62 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g62B5 : block g62 5 0 1=true := g62P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62T : checkedTables g62 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g62 0 0 0 = true)
  · exact (rfl : block g62 1 0 0 = true)
  · exact (rfl : block g62 2 0 0 = true)
  · exact (rfl : block g62 3 0 0 = true)
  · exact (rfl : block g62 4 0 0 = true)
  · exact g62B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62G : graphValid g62 (boundsBefore K61) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low62 : Lower true (varsX 62) (graphGoal 62) 6 := lower_forest (g:=g62) (i:=0) (hints:=1135680) (before_sound K61 V61) g62G g62T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K62 := extendKnown K61 6 [(62,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V62 : Known true K62 := extend_ok (m:=62) V61 low62 (by decide +kernel)
def g103Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe003ffc07ffffffe00,0x3fffff80ffd386b20f0f])),(BitVec.ofNat 152 (word80 [0x41a8128d052280541a,0x82502916291304a21111]))),((BitVec.ofNat 152 (word80 [0xfffc00007ff01fffff,0xc007ffff01a37d4800f0])),(BitVec.ofNat 152 (word80 [0x81311b160644c89893,0x136232244d835c485555]))),((BitVec.ofNat 152 (word80 [0xffffffff80001fffff,0xfff80000003f407df000])),(BitVec.ofNat 152 (word80 [0x5c05c18178702e01c,0x380bc38703340753333]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffff,0xfffffffffe663f7600ff])),(BitVec.ofNat 152 (word80 [0x160260205808130120,0x2404c00000642314aaaa]))),((BitVec.ofNat 152 (word80 [0xffffffffffffe00000,0x19dd38dff00])),(BitVec.ofNat 152 (word80 [0x1803800060001c01c0,0x38070040808c9308cccc]))),(0x0,0x0),(0x0,0x0)]
def g103C : List ColumnInfo := []
def g103A : List (List Nat) := [[],[33,101]]
def g103D4 (j : Nat) := if j=0 then 0x1f else 0
def g103L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g103D4)
  | _ => emptyPacking
def g103I (_ _ : Nat) : Option (Nat × Nat) := none
def g103 : Forest := ⟨103,4,fun i => g103Y[i]?.getD (0,0),g103C,g103A,g103L,g103I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103P4_0 : block g103 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g103B4 : block g103 4 0 1=true := g103P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103T : checkedTables g103 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g103 0 0 0 = true)
  · exact (rfl : block g103 1 0 0 = true)
  · exact (rfl : block g103 2 0 0 = true)
  · exact (rfl : block g103 3 0 0 = true)
  · exact g103B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103G : graphValid g103 (boundsBefore K62) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low103 : Lower true (varsX 103) (graphGoal 103) 5 := lower_forest (g:=g103) (i:=0) (hints:=1621) (before_sound K62 V62) g103G g103T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K103 := extendKnown K62 5 [(103,[]),(199,[117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V103 : Known true K103 := extend_ok (m:=103) V62 low103 (by decide +kernel)
def g118Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfe007fc3fc7fe00ffc,0x3ffffc3e357700007c1f])),(BitVec.ofNat 152 (word80 [0x14850288092148a428,0x9082088221761294a529]))),((BitVec.ofNat 152 (word80 [0xffff8003fffffff000,0x3fc7ffc2d1b8c1f003e0])),(BitVec.ofNat 152 (word80 [0x98261310900980c131,0x1109008d1b80a5294a5]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffc007fffffff,0xc007fffdca263e0f83ff])),(BitVec.ofNat 152 (word80 [0x200804002002010040,0x2002000000004210842]))),((BitVec.ofNat 152 (word80 [0x7fffffff,0xfff800007f49800ffc00])),(BitVec.ofNat 152 (word80 [0xc1305822c24c120980,0x2404c1105e09a94a5294]))),((BitVec.ofNat 152 (word80 [0xffffffffff80000000,0x3289bfff00000])),(BitVec.ofNat 152 (word80 [0x1c0600300701c0e02,0x382702232803f18c6318]))),(0x0,0x0),(0x0,0x0)]
def g118C : List ColumnInfo := [(2,0,116,0,5),(4,0,114,0,5),(32,0,86,0,5),(64,0,54,0,5),(34,0,84,0,4),(68,0,50,0,4)]
def g118A : List (List Nat) := [[],[98],[33,101],[33,81,97],[81],[81,98],[97,33,82],[97,82]]
def g118D4 := limbs80 #[#[0x97d8d524425d6314910,0x31823f645472]]
def g118D5 := limbs80 #[#[0x7c52443f2408857d4d20,0xfea4885f94910bea9221,0x7d4d20bfa8a41fb20482,0xcc8d018160c02faa3907,0x882188201141080d176b,0xc110204810001]]
def g118H5 := limbs80 #[#[0xc10099d20000f8,0x400000]]
def g118D6 := limbs80 #[#[0x540a0380ff20fd20fd10,0x3140cc503]]
def g118H6 := limbs80 #[#[0x6640000000,0x1230900000,0x111,0x0,0x386000000000000000,0x4080000000,0xa0e9400000002e100204,0xb4c00002400000000000,0x6140000000000c7,0xc04d7]]
def g118D7 (j : Nat) := if j=0 then 0x1605f else 0
def g118H7 := limbs80 #[#[0x38ac800948b000f24ca,0x0,0x7c642009d600000,0xaa4a0000]]
def g118L : Nat → Packing
  | 4 => (3,3,3,0,0,4,0,g118D4)
  | 5 => (10,2,3,0,0,7,0,g118D5)
  | 6 => (3,1,3,0,0,6,0,g118D6)
  | 7 => (1,0,3,0,0,0,0,g118D7)
  | _ => emptyPacking
def g118I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 19 0 8 2 2 g118H5
  | 6 => lookupWord 4 83 0 10 4 2 g118H6
  | 7 => lookupWord 3 31 1 9 2 3 g118H7
  | _ => fun _ => none
def g118 : Forest := ⟨118,7,fun i => g118Y[i]?.getD (0,0),g118C,g118A,g118L,g118I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118P4_0 : block g118 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g118B4 : block g118 4 0 3=true := g118P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118P5_0 : block g118 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118P5_1 : block g118 5 1 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g118B5 : block g118 5 0 10=true := (@block_merge g118 5 0 1 9 g118P5_0 g118P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118P6_0 : block g118 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g118B6 : block g118 6 0 3=true := g118P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118P7_0 : block g118 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g118B7 : block g118 7 0 1=true := g118P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118T : checkedTables g118 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g118 0 0 0 = true)
  · exact (rfl : block g118 1 0 0 = true)
  · exact (rfl : block g118 2 0 0 = true)
  · exact (rfl : block g118 3 0 0 = true)
  · exact g118B4
  · exact g118B5
  · exact g118B6
  · exact g118B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118G : graphValid g118 (boundsBefore K103) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low118 : Lower true (varsX 118) (graphGoal 118) 8 := lower_forest (g:=g118) (i:=0) (hints:=34669632) (before_sound K103 V103) g118G g118T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K118 := extendKnown K103 8 [(118,[]),(214,[117]),(244,[33,81,49,99,115])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V118 : Known true K118 := extend_ok (m:=118) V103 low118 (by decide +kernel)
def g121Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fff80ff1fe3ffc07,0xf8ff1ffffc80b60381ff])),(BitVec.ofNat 152 (word80 [0x81010202004000810,0x10020008000000249249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfc07fff001ffc3fff8,0xffe1fc3c655d1c0e07])),(BitVec.ofNat 152 (word80 [0x50a0a0414428085020,0xa2140410806454492492]))),((BitVec.ofNat 152 (word80 [0x7fffffe0003ffff,0xff0001ffc3be10e07038])),(BitVec.ofNat 152 (word80 [0x60c0c0818030906040,0xc01848200aac10492492]))),((BitVec.ofNat 152 (word80 [0xfff80000000003ffff,0xfffffe00007ba8007fc0])),(BitVec.ofNat 152 (word80 [0x8105050a0941228285,0xa001411013a8924924]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x3066bff8000])),(BitVec.ofNat 152 (word80 [0x206060c0180030306,0x4c0918221022b924924]))),(0x0,0x0),(0x0,0x0)]
def g121C : List ColumnInfo := [(8,0,113,0,5)]
def g121A : List (List Nat) := [[],[101],[67],[67,101],[83,100],[83,100,67],[99,84,67],[99,84]]
def g121D5 (j : Nat) := if j=0 then 0x3f else 0
def g121L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g121D5)
  | _ => emptyPacking
def g121I (_ _ : Nat) : Option (Nat × Nat) := none
def g121 : Forest := ⟨121,5,fun i => g121Y[i]?.getD (0,0),g121C,g121A,g121L,g121I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g121P5_0 : block g121 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g121B5 : block g121 5 0 1=true := g121P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g121T : checkedTables g121 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g121 0 0 0 = true)
  · exact (rfl : block g121 1 0 0 = true)
  · exact (rfl : block g121 2 0 0 = true)
  · exact (rfl : block g121 3 0 0 = true)
  · exact (rfl : block g121 4 0 0 = true)
  · exact g121B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g121G : graphValid g121 (boundsBefore K118) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low121 : Lower true (varsX 121) (graphGoal 121) 6 := lower_forest (g:=g121) (i:=0) (hints:=3) (before_sound K118 V118) g121G g121T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K121 := extendKnown K118 6 [(121,[]),(217,[101,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V121 : Known true K121 := extend_ok (m:=121) V118 low121 (by decide +kernel)
def g122Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff007fc3fc3ff007fe,0x1ff0ffff34de830000ff])),(BitVec.ofNat 152 (word80 [0xa4502880890a45214,0x48220420148e03555555]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff8003fffffff800,0x1fff0ff0d434790f0f00])),(BitVec.ofNat 152 (word80 [0x2c060b105002c06058,0x81402042903431333333]))),((BitVec.ofNat 152 (word80 [0xfffffffc003fffffff,0xe0000fff2bb526f0f00f])),(BitVec.ofNat 152 (word80 [0x30080c006103008060,0x1844080293020222222]))),((BitVec.ofNat 152 (word80 [0x3fffffff,0xfffff000134bf800fff0])),(BitVec.ofNat 152 (word80 [0x409050228224090480,0x120009040241c8888888]))),((BitVec.ofNat 152 (word80 [0xffffffffffc0000000,0xcea8c5ff0000])),(BitVec.ofNat 152 (word80 [0x80e0600300380e0701,0x1c088e084688c4cccccc]))),(0x0,0x0),(0x0,0x0)]
def g122C : List ColumnInfo := [(8,0,114,0,5)]
def g122A : List (List Nat) := [[],[99,84]]
def g122D5 (j : Nat) := if j=0 then 0x3f else 0
def g122L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g122D5)
  | _ => emptyPacking
def g122I (_ _ : Nat) : Option (Nat × Nat) := none
def g122 : Forest := ⟨122,5,fun i => g122Y[i]?.getD (0,0),g122C,g122A,g122L,g122I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g122P5_0 : block g122 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g122B5 : block g122 5 0 1=true := g122P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g122T : checkedTables g122 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g122 0 0 0 = true)
  · exact (rfl : block g122 1 0 0 = true)
  · exact (rfl : block g122 2 0 0 = true)
  · exact (rfl : block g122 3 0 0 = true)
  · exact (rfl : block g122 4 0 0 = true)
  · exact g122B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g122G : graphValid g122 (boundsBefore K121) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low122 : Lower true (varsX 122) (graphGoal 122) 6 := lower_forest (g:=g122) (i:=0) (hints:=51466304) (before_sound K121 V121) g122G g122T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K122 := extendKnown K121 6 [(122,[]),(124,[33,101]),(218,[117]),(220,[33,101,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V122 : Known true K122 := extend_ok (m:=122) V121 low122 (by decide +kernel)
def g171Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff0ff01fe3f8ffe0,0x3fc7f1ffd675000f00ff])),(BitVec.ofNat 152 (word80 [0xa0a20a14148120142,0x82902402163411111111]))),((BitVec.ofNat 152 (word80 [0xff000fffe003ff1fff,0xc007fe3f317a00f00f00])),(BitVec.ofNat 152 (word80 [0x2c2c42c18590a04583,0xb214084b17a33333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffc001fff,0xfff8003fede10f00f00f])),(BitVec.ofNat 152 (word80 [0x303083020600c48604,0xc01890829c122222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffff0000000001fff,0xffffffc01388f000fff0])),(BitVec.ofNat 152 (word80 [0x404004040801000808,0x10020010000044444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffe000,0x2816ffff0000])),(BitVec.ofNat 152 (word80 [0x808008081002001010,0x20040020000088888888]))),(0x0,0x0)]
def g171C : List ColumnInfo := [(2,0,169,0,7)]
def g171A : List (List Nat) := [[],[117],[48],[48,117]]
def g171D7 (j : Nat) := if j=0 then 0x3f else 0
def g171L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g171D7)
  | _ => emptyPacking
def g171I (_ _ : Nat) : Option (Nat × Nat) := none
def g171 : Forest := ⟨171,7,fun i => g171Y[i]?.getD (0,0),g171C,g171A,g171L,g171I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171P7_0 : block g171 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g171B7 : block g171 7 0 1=true := g171P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171T : checkedTables g171 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g171 0 0 0 = true)
  · exact (rfl : block g171 1 0 0 = true)
  · exact (rfl : block g171 2 0 0 = true)
  · exact (rfl : block g171 3 0 0 = true)
  · exact (rfl : block g171 4 0 0 = true)
  · exact (rfl : block g171 5 0 0 = true)
  · exact (rfl : block g171 6 0 0 = true)
  · exact g171B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171G : graphValid g171 (boundsBefore K122) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low171 : Lower true (varsX 171) (graphGoal 171) 8 := lower_forest (g:=g171) (i:=0) (hints:=83) (before_sound K122 V122) g171G g171T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K171 := extendKnown K122 8 [(171,[]),(186,[16,48,32,66]),(233,[80,97,33,115,66]),(241,[80,97,33,115,66,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V171 : Known true K171 := extend_ok (m:=171) V122 low171 (by decide +kernel)
def g179Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7f01fc7f01fc7e7fc,0x7f1f9fe7ea000f00f0f])),(BitVec.ofNat 152 (word80 [0x50a14290a142905028,0x50a414051ea111111111]))),((BitVec.ofNat 152 (word80 [0x7ffe007ffe007f9ff,0xf801fe7f8b700f00f0f0])),(BitVec.ofNat 152 (word80 [0x60c18320c183208430,0x60c821084b7111111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf8000007fffff801ff,0xfffe007fe640f00f00ff])),(BitVec.ofNat 152 (word80 [0x810204010204010040,0x81004010000222222222]))),((BitVec.ofNat 152 (word80 [0xfffffff800000001ff,0xffffff8001af000fff00])),(BitVec.ofNat 152 (word80 [0x20408020408020081,0x2008020000444444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffffe00,0x181ffff00000])),(BitVec.ofNat 152 (word80 [0x40810040810040102,0x4010040000888888888]))),(0x0,0x0)]
def g179C : List ColumnInfo := [(1,0,178,0,7)]
def g179A : List (List Nat) := [[],[117],[84],[84,116],[116,84],[116],[16],[16,117],[16,84],[16,84,116],[16,116,84],[16,116]]
def g179D7 (j : Nat) := if j=0 then 0x3f else 0
def g179L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g179D7)
  | _ => emptyPacking
def g179I (_ _ : Nat) : Option (Nat × Nat) := none
def g179 : Forest := ⟨179,7,fun i => g179Y[i]?.getD (0,0),g179C,g179A,g179L,g179I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179P7_0 : block g179 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g179B7 : block g179 7 0 1=true := g179P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179T : checkedTables g179 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g179 0 0 0 = true)
  · exact (rfl : block g179 1 0 0 = true)
  · exact (rfl : block g179 2 0 0 = true)
  · exact (rfl : block g179 3 0 0 = true)
  · exact (rfl : block g179 4 0 0 = true)
  · exact (rfl : block g179 5 0 0 = true)
  · exact (rfl : block g179 6 0 0 = true)
  · exact g179B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179G : graphValid g179 (boundsBefore K171) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low179 : Lower true (varsX 179) (graphGoal 179) 8 := lower_forest (g:=g179) (i:=0) (hints:=68) (before_sound K171 V171) g179G g179T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K179 := extendKnown K171 8 [(179,[]),(185,[48,65,33,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V179 : Known true K179 := extend_ok (m:=179) V171 low179 (by decide +kernel)
def g181Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfc7fc03fe1ffffc03f,0xe1ffff87c1bd300f0f0f])),(BitVec.ofNat 152 (word80 [0x290282814408028281,0x44080110003931111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fffc001fc7fffc0,0x1fc7ff85968e00000f0])),(BitVec.ofNat 152 (word80 [0x325313298891532329,0x891152015968eddddddd]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7ffffffe007fffff,0xfe007fffba0940f0f0ff])),(BitVec.ofNat 152 (word80 [0x400404020020040402,0x200400000002222222]))),((BitVec.ofNat 152 (word80 [0xff80000000007fffff,0xffff80000ff28f00ff00])),(BitVec.ofNat 152 (word80 [0x8018180c10c218080c,0x4018220fc004444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffff800000,0x6446ffff0000])),(BitVec.ofNat 152 (word80 [0x6020300100603030,0x118260446006c8888888]))),(0x0,0x0)]
def g181C : List ColumnInfo := [(4,0,177,0,7)]
def g181A : List (List Nat) := [[],[117],[80],[80,112],[112,80],[112]]
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
theorem g181G : graphValid g181 (boundsBefore K179) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low181 : Lower true (varsX 181) (graphGoal 181) 8 := lower_forest (g:=g181) (i:=0) (hints:=1028) (before_sound K179 V179) g181G g181T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K181 := extendKnown K179 8 [(181,[]),(182,[16]),(242,[16,98,50])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V181 : Known true K181 := extend_ok (m:=181) V179 low181 (by decide +kernel)
def g229Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf007ff0ffffff007ff,0xff87ffffd45c460f83ff])),(BitVec.ofNat 152 (word80 [0xa0500a201000a05014,0x1100082401806108421]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff8000ff87ffff801,0xfff87fc05373b2007c00])),(BitVec.ofNat 152 (word80 [0xc0622c40a122c46258,0x8a012108527132b5ad6b]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff0007ffffffe,0x7ffcafd11df0001f])),(BitVec.ofNat 152 (word80 [0x280b002c20b008060,0x2c220a00a541186318c6]))),((BitVec.ofNat 152 (word80 [0x7fffffff,0xffff80004d2fe8007fe0])),(BitVec.ofNat 152 (word80 [0xb04c08b044c090481,0x30004c100d06c94a5294]))),((BitVec.ofNat 152 (word80 [0xffffffffff80000000,0x33aa61bff8000])),(BitVec.ofNat 152 (word80 [0xc07000c00700e0701,0xc04470211aa6018c6318]))),(0x0,0x0)]
def g229C : List ColumnInfo := [(0,4,161,64,5),(4,0,225,0,5),(32,0,197,0,4),(64,4,161,0,4),(128,0,101,0,4)]
def g229A : List (List Nat) := [[],[117]]
def g229D4 (j : Nat) := if j=0 then 0x4fd5120 else 0
def g229D5 := limbs80 #[#[0x480e140fd42fe20fd20,0x4088]]
def g229H5 (j : Nat) := if j=0 then 0xb0 else 0
def g229D6 (j : Nat) := if j=0 then 0x18989f else 0
def g229H6 := limbs80 #[#[0x406a0000000,0x3400000000d0,0x2a0000]]
def g229L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g229D4)
  | 5 => (3,1,3,0,0,5,0,g229D5)
  | 6 => (1,0,3,0,0,0,0,g229D6)
  | _ => emptyPacking
def g229I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g229H5
  | 6 => lookupWord 1 29 0 7 2 1 g229H6
  | _ => fun _ => none
def g229 : Forest := ⟨229,6,fun i => g229Y[i]?.getD (0,0),g229C,g229A,g229L,g229I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g229P4_0 : block g229 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g229B4 : block g229 4 0 1=true := g229P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g229P5_0 : block g229 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g229B5 : block g229 5 0 3=true := g229P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g229P6_0 : block g229 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g229B6 : block g229 6 0 1=true := g229P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g229T : checkedTables g229 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g229 0 0 0 = true)
  · exact (rfl : block g229 1 0 0 = true)
  · exact (rfl : block g229 2 0 0 = true)
  · exact (rfl : block g229 3 0 0 = true)
  · exact g229B4
  · exact g229B5
  · exact g229B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g229G : graphValid g229 (boundsBefore K181) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low229 : Lower true (varsX 229) (graphGoal 229) 7 := lower_forest (g:=g229) (i:=0) (hints:=1541) (before_sound K181 V181) g229G g229T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K229 := extendKnown K181 7 [(229,[]),(236,[48,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V229 : Known true K229 := extend_ok (m:=229) V181 low229 (by decide +kernel)
def g230Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc00fff0ffffffc00ff,0xfff0fffeea3a5303f03f])),(BitVec.ofNat 152 (word80 [0x84a08a210802284a02,0x80220882200a53145145]))),((BitVec.ofNat 152 (word80 [0xfff0000ffc3fffff00,0x3fffffc009adfd000fc0])),(BitVec.ofNat 152 (word80 [0xc42c405090b10c4b,0x11404108092d994d34d3]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff0003fffffff,0xc000fffd77e88afc003f])),(BitVec.ofNat 152 (word80 [0x90130026104c0100c,0x584120152a08828a28a]))),((BitVec.ofNat 152 (word80 [0x3fffffff,0xffff00012697f4000fc0])),(BitVec.ofNat 152 (word80 [0x2e09c08b8227026090,0x26009c11269264b2cb2c]))),((BitVec.ofNat 152 (word80 [0xffffffffffc0000000,0x39d530dfff000])),(BitVec.ofNat 152 (word80 [0x300e000c00380380e0,0x3808e0208d5104c30c30]))),(0x0,0x0)]
def g230C : List ColumnInfo := [(0,4,162,64,5)]
def g230A : List (List Nat) := [[],[117],[98],[98,117],[81],[81,113],[81,98],[81,98,113],[113,81],[113],[113,98,81],[113,98]]
def g230D5 (j : Nat) := if j=0 then 0x3f else 0
def g230L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g230D5)
  | _ => emptyPacking
def g230I (_ _ : Nat) : Option (Nat × Nat) := none
def g230 : Forest := ⟨230,5,fun i => g230Y[i]?.getD (0,0),g230C,g230A,g230L,g230I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g230P5_0 : block g230 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g230B5 : block g230 5 0 1=true := g230P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g230T : checkedTables g230 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g230 0 0 0 = true)
  · exact (rfl : block g230 1 0 0 = true)
  · exact (rfl : block g230 2 0 0 = true)
  · exact (rfl : block g230 3 0 0 = true)
  · exact (rfl : block g230 4 0 0 = true)
  · exact g230B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g230G : graphValid g230 (boundsBefore K229) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low230 : Lower true (varsX 230) (graphGoal 230) 6 := lower_forest (g:=g230) (i:=0) (hints:=303040080) (before_sound K229 V229) g230G g230T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K230 := extendKnown K229 6 [(230,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V230 : Known true K230 := extend_ok (m:=230) V229 low230 (by decide +kernel)
def g248Y : Array (Bits × Bits) := #[(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff803fe1fe1fff00f,0xfff0fff0fe94ae0071c7])),(BitVec.ofNat 152 (word80 [0xa0502814404400a0a0,0xa0220022089424049249]))),((BitVec.ofNat 152 (word80 [0xffffc001ffe1ffff0,0xfff0fff01d961a38e38])),(BitVec.ofNat 152 (word80 [0xc0603018808040c0c0,0xc0402040209861049249]))),((BitVec.ofNat 152 (word80 [0xfffffffe0001fffff,0xf0000ffff22376dc003f])),(BitVec.ofNat 152 (word80 [0x28140a00508850101,0x2844280020302c92492]))),((BitVec.ofNat 152 (word80 [0xf000000000001fffff,0xfffff000013c8ae00fc0])),(BitVec.ofNat 152 (word80 [0xb0582c11611160a0a,0xb000b0441208afb6db6]))),((BitVec.ofNat 152 (word80 [0xffffffffffffe00000,0xce2917ff000])),(BitVec.ofNat 152 (word80 [0xc0603001800180c0c,0xc088c08846090324924]))),(0x0,0x0)]
def g248C : List ColumnInfo := [(8,0,240,0,5)]
def g248A : List (List Nat) := [[],[117],[67],[67,117]]
def g248D5 (j : Nat) := if j=0 then 0x3f else 0
def g248L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g248D5)
  | _ => emptyPacking
def g248I (_ _ : Nat) : Option (Nat × Nat) := none
def g248 : Forest := ⟨248,5,fun i => g248Y[i]?.getD (0,0),g248C,g248A,g248L,g248I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g248P5_0 : block g248 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g248B5 : block g248 5 0 1=true := g248P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g248T : checkedTables g248 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g248 0 0 0 = true)
  · exact (rfl : block g248 1 0 0 = true)
  · exact (rfl : block g248 2 0 0 = true)
  · exact (rfl : block g248 3 0 0 = true)
  · exact (rfl : block g248 4 0 0 = true)
  · exact g248B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g248G : graphValid g248 (boundsBefore K230) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low248 : Lower true (varsX 248) (graphGoal 248) 6 := lower_forest (g:=g248) (i:=0) (hints:=859131904) (before_sound K230 V230) g248G g248T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K248 := extendKnown K230 6 [(248,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V248 : Known true K248 := extend_ok (m:=248) V230 low248 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf003ffffffffffffff,0xfa28e890fd89000f00ff])),(BitVec.ofNat 152 (word80 [0x20581400a804a01481,0x4a00a090cc0911111111]))),((BitVec.ofNat 152 (word80 [0xfffc00fffc000fffc0,0x7d10c854cb300f00f00])),(BitVec.ofNat 152 (word80 [0x4290a6053036c09906,0x67510c814c9133333333]))),((BitVec.ofNat 152 (word80 [0xfffffff00000,0x1cf23b09ad10000f000])),(BitVec.ofNat 152 (word80 [0x84e13889c22708de0b,0x81cb23b09a91bbbbbbbb]))),((BitVec.ofNat 152 (word80 [0xffffffffffff,0xf2153f483bb80f00000f])),(BitVec.ofNat 152 (word80 [0x701c02e00b802e00c,0x151e4033b066666666]))),((BitVec.ofNat 152 (word80 [0xffffff000000000000,0x116d0a38776f000fff0])),(BitVec.ofNat 152 (word80 [0x3000c0030010,0x45000016644444444]))),(0xce9177e4005ffff0000,(BitVec.ofNat 152 (word80 [0x80200c003000c0020,0xa8012e000088888888]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(2,0,61,0,7),(4,0,59,0,7),(0,4,43,16,6),(1,0,62,0,6),(8,0,55,0,6),(2,4,41,16,5),(5,0,58,0,5),(6,0,57,0,5),(9,0,54,0,5),(12,0,51,0,5),(16,0,43,0,5),(16,4,43,0,5),(32,0,31,0,5),(3,0,60,0,4),(18,0,41,0,4),(34,0,29,0,4),(36,0,27,0,4)]
def g63A : List (List Nat) := [[]]
def g63D4 := limbs80 #[#[0x50d40443645d54350110,0x442d86174254110d9375,0xe1562541109e187d0950,0x54110f115450d50442d8,0x9e3855c3424427421d43,0x9956244239e1975d0910,0x5423361f63d0950c6775,0xe0576d0b508e7815db42,0x597428e7815db53d0a39,0xb19801955450e3960371,0x5c06550ec56046555143,0xe0217e1d6519543c5965,0x6aa4e9109e2d4e84d951,0x480fef1cb666c1,0x90100]]
def g63D5 := limbs80 #[#[0xaf0b8684887914350110,0xf62a8a022139dc565d0,0x42f9baa80885f1755011,0x10fc2a4a8221f8d09504,0x443f0b92a0887e162541,0x110fa6e6a8221f450d50,0x443b9aa2a0887715454,0x910bcaeba12217cdd15,0x62442f3bb2a4885e576d,0x50d10bceeab1221b9995,0x954443caaa286887d370,0x359510be2e1aa2213ddd,0xd50502f8b84ca885d77,0x7050d40e72a8a8281e65,0xd95435034eb2a86a079b,0xf73595409eee2b2a81a7,0x3d8f42542f4b8684a84d,0xed76d0950adaeba12a1b,0xb3d8d6254367b1aa4a84,0x4dc7650d50e3aa8a1aa1,0x1b35cb635426f3b286a8,0x856d75d0b509bae9b1aa,0xa1c755143d4276bb685a,0xa14f77159350d3ac8a1e,0xe853b5db53d0a77baac1,0x6a1ee771597429dee0b2,0x9a87675d35350ecfba2a,0xcaa1cfb7059543cbecba,0xaa28767dc15450e7bb8a,0xaa8a1f1c6555143f2ee2,0x232a87765c06550f8fb2,0x82caa1e5d6519543baae],#[0xcb32a8775dc56550eedb,0xb86c2aa4f77159353cbe,0x580f00137dcd60d527a,0x1684f100390c82f0901d,0x2187f1e0751b86b1905d,0x2d8af2b0a52889b2508d,0x388df370d9358cf320bd,0x419033f0f53b8eb3a0e5,0x4891f471194490f43109,0x4e9374d1314b92b4a125,0x5795b561555494b5113d,0x5024857c21da96759161,0x3480804800115831409,0x920204403041b480e1d2,0x42082820a080480801a0,0x20201202015824808382,0x202c4081d1054409,0x80e102120800000000,0x18408000000,0x3102c40c58200000000]]
def g63H5 := limbs80 #[#[0x10020c00000000000e10,0x67a0001908,0xa00003b8003200003ce0,0x6620064820da00620030,0x118000052d95830050]]
def g63D6 := limbs80 #[#[0x9d0910fc54110fc50110,0x50d10f958910f954910f,0x8342b7d8d50e750d40f5,0x143bbd8152bb59742bb5,0x10fd55110bdd8554e755,0xfd59510fd59110fdd51,0xef55140fe54140fd9951,0xbd0950bfd9540bf59540,0x50d50fb58950fb54950f,0x5150df55150f7d8d50f7,0xf50fbd0b50bfd9150dfd,0x42bf59350df55350f750,0x3fb54d52fbd4f42fb54f,0xef55143f7d4d43f754d4,0x758143bfd9543bf59543,0x59543f719543f7d8143f,0x9153f7d9543f799543f7,0x554bfd8154bf59353bfd,0x54bf58354bfd8d54fdd8,0xe07a0b00f411000bf58f,0x7c2b44e0921091dc3144,0x472895051e138c6acc81,0x4bbd66ab252ea0d37a4d,0xadc83836c2d359931e61,0x14c077e6f61e5bc5762e,0x5099cf34e58c818bf112,0x1589676c157cac351a92,0x890242a0c6e11018dc22,0xd58a1e40d5622181215,0x3c2184c1845c315240c3,0x4058980505805280f04,0x558786584130e016223c],#[0x21147215618342ac3423,0x910c086a24218f1a911,0x820404208080801018b,0x141108480c1908884388,0x3841420610487843150e,0x50e14112182082020218,0x10120208004040070811,0x20200416102448450630,0x48444484406281010c18,0xa01050446890a0182234,0xc504448444484246890,0x10100184040400810101,0x202021818404b0c]]
def g63H6 := limbs80 #[#[0x4052242220201,0x102800000000002920,0x19380000000000000000,0x167c0008700000,0x0,0x2e30000000035c8,0x64400081,0x0,0x16f8000000000,0x1650,0xac00202a5800000,0x5b634000000000000000,0xd,0x14e800000,0x38e0000000000000000,0xf4c0000,0x0,0x2ba,0x0,0xa34000000000000,0x80010762c00000000000,0x432003a0,0x40000000000000000000,0x108c000007,0x300000000014e96e2a,0xa3c0039a000d2e00,0x45660002d88000000000,0x1c3000003d29,0x7a1,0xf180000021c00,0x3bb0000,0x0],#[0x0,0x66000000000004d80000,0x9,0x0,0x6c000000,0x6e0000000000000,0x0,0x1c40007180008a0003c2,0xdd9f80057aeb86270400,0x526000000000008,0x12000,0x0,0xf0000000000,0x63555fe90000000,0x0,0x3d900000000,0x14f2047220016000,0x1400000000000000000,0x40000000000106c00000,0xf5]]
def g63D7 := limbs80 #[#[0xd43f6a97bd0bda41f510,0x87ff50fea87f503bc87d,0x3fea9fd54ffa9ff54ffa,0x439c8c0511f8b4421200,0xdae1205ea6ab015c9c,0x2880b16880a0c68082c4,0x58602c810486380b1413,0x18230a8212063218082c,0x532180b20528282120c,0xb18a0a084c20630a8602,0x40e180c2c63040e180]]
def g63H7 := limbs80 #[#[0x13f0030150210,0x46e24000019100000000,0x2750000000063001,0xd4c,0xc5d8300000001327d0,0x872d400182000,0x4a9a50018bc5800738,0xf09af1ef000054800784,0x9d000000100000000822,0xca00000000007b2a6003,0x2470000000000ba4,0x2b8,0x90002eff161b00159000,0x1cd0000000000ba3,0x410004f0000000000930,0xac62057c6705400002,0x3220000000324bb4,0x98000000029a000738d8,0x1]]
def g63D8 (j : Nat) := if j=0 then 0x5a00113f else 0
def g63H8 := limbs80 #[#[0x80088000000000074020,0x1600103dd86e654002,0x17258000000000,0x32c00000290018c0]]
def g63L : Nat → Packing
  | 4 => (19,4,5,0,0,7,0,g63D4)
  | 5 => (71,3,5,0,0,10,0,g63D5)
  | 6 => (55,2,5,0,0,11,0,g63D6)
  | 7 => (14,1,5,0,0,9,0,g63D7)
  | 8 => (1,0,5,0,0,0,0,g63D8)
  | _ => emptyPacking
def g63I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 4 53 3 9 5 0 g63H5
  | 6 => lookupWord 17 367 3 11 7 0 g63H6
  | 7 => lookupWord 13 139 4 10 6 0 g63H7
  | 8 => lookupWord 3 37 2 8 4 0 g63H8
  | _ => fun _ => none
def g63 : Forest := ⟨63,8,fun i => g63Y[i]?.getD (0,0),g63C,g63A,g63L,g63I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P4_0 : block g63 4 0 19=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B4 : block g63 4 0 19=true := g63P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P5_0 : block g63 5 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P5_3 : block g63 5 3 68=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B5 : block g63 5 0 71=true := (@block_merge g63 5 0 3 68 g63P5_0 g63P5_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_0 : block g63 6 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_13 : block g63 6 13 42=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B6 : block g63 6 0 55=true := (@block_merge g63 6 0 13 42 g63P6_0 g63P6_13)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_0 : block g63 7 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_6 : block g63 7 6 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B7 : block g63 7 0 14=true := (@block_merge g63 7 0 6 8 g63P7_0 g63P7_6)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_0 : block g63 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B8 : block g63 8 0 1=true := g63P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63T : checkedTables g63 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g63 0 0 0 = true)
  · exact (rfl : block g63 1 0 0 = true)
  · exact (rfl : block g63 2 0 0 = true)
  · exact (rfl : block g63 3 0 0 = true)
  · exact g63B4
  · exact g63B5
  · exact g63B6
  · exact g63B7
  · exact g63B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K248) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 9 := lower_forest (g:=g63) (i:=0) (hints:=1091) (before_sound K248 V248) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K248 9 [(63,[]),(95,[33,101]),(159,[117,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V248 low63 (by decide +kernel)
def g111Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ffffffffffffffff,0xc55533030e5801f003ff])),(BitVec.ofNat 152 (word80 [0x581400540128029029,0xc1541202044042108421]))),((BitVec.ofNat 152 (word80 [0xfc00fffe0003fff800,0xf825583e2d9000007c00])),(BitVec.ofNat 152 (word80 [0x90a642988db11320cc,0xd825583a0d92d6b5ad6b]))),((BitVec.ofNat 152 (word80 [0xfffffffc000000,0x39c4d6d39a803e000000])),(BitVec.ofNat 152 (word80 [0xe13814e029c05bc170,0x29c4d6538a81ce739ce7]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffe,0x428bca0bc9efc00f801f])),(BitVec.ofNat 152 (word80 [0x1c007000e001c0180,0x9c809c88884210842]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff00000000000000,0x22fa317cb680000fffe0])),(BitVec.ofNat 152 (word80 [0x98013002600200,0x228221443205294a5294]))),((BitVec.ofNat 152 (word80 [1,0x9d26ecc07137fff00000])),(BitVec.ofNat 152 (word80 [0x200e001c003800400,0x142220803136318c6318]))),(0x0,0x0),(0x0,0x0)]
def g111C : List ColumnInfo := [(2,0,109,0,7)]
def g111A : List (List Nat) := [[],[33,101],[48],[48,33,101]]
def g111D7 (j : Nat) := if j=0 then 0x7f else 0
def g111L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g111D7)
  | _ => emptyPacking
def g111I (_ _ : Nat) : Option (Nat × Nat) := none
def g111 : Forest := ⟨111,7,fun i => g111Y[i]?.getD (0,0),g111C,g111A,g111L,g111I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7_0 : block g111 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B7 : block g111 7 0 1=true := g111P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111T : checkedTables g111 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact (rfl : block g111 4 0 0 = true)
  · exact (rfl : block g111 5 0 0 = true)
  · exact (rfl : block g111 6 0 0 = true)
  · exact g111B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111G : graphValid g111 (boundsBefore K63) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low111 : Lower true (varsX 111) (graphGoal 111) 8 := lower_forest (g:=g111) (i:=0) (hints:=1619) (before_sound K63 V63) g111G g111T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K111 := extendKnown K63 8 [(111,[]),(207,[117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V111 : Known true K111 := extend_ok (m:=111) V63 low111 (by decide +kernel)
def g119Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe000fff807ffc03fc,0xda2aa9236007c00f801f])),(BitVec.ofNat 152 (word80 [0x5406a0250d01485850,0xca2a0821610842108421]))),((BitVec.ofNat 152 (word80 [0xfffff000007ffffc01,0xe0ed0cd3800001f003e0])),(BitVec.ofNat 152 (word80 [0x9884c4361621909099,0xe0a90c53894a5294a529]))),((BitVec.ofNat 152 (word80 [0xffffffffff80000003,0x4b5b594880f800007c00])),(BitVec.ofNat 152 (word80 [0xe02701381809e0e0e1,0x4a5a594885294a5294a5]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffffffc,0x841a46543f003e007fff])),(BitVec.ofNat 152 (word80 [0x800400002000000,0x21084210842]))),(0x79f423ac80003fff8000,(BitVec.ofNat 152 (word80 [0x1300980204c010100,0x1154238c14a5294a5294]))),((BitVec.ofNat 152 (word80 [3,0x37059a1b5fffc0000000])),(BitVec.ofNat 152 (word80 [0x1c00e004070020202,0x3505821218c6318c6318]))),(0x0,0x0),(0x0,0x0)]
def g119C : List ColumnInfo := [(1,0,118,0,8),(2,0,117,0,7),(4,0,115,0,7),(32,0,87,0,6),(64,0,55,0,6),(6,0,113,0,5),(16,0,103,0,5),(33,0,86,0,5),(34,0,85,0,5),(36,0,83,0,5),(66,0,53,0,5),(68,0,51,0,5),(18,0,101,0,4),(20,0,99,0,4),(35,0,84,0,4),(38,0,81,0,4),(70,0,49,0,4)]
def g119A : List (List Nat) := [[],[33,101]]
def g119D4 := limbs80 #[#[0x30a87c33655517018543,0x655c06150e9c724b2ae0,0x79c830faa6c2a1c3ce61,0x1aa98e382e0770595438,0xf624c3031c304c0ae03]]
def g119D5 := limbs80 #[#[0x50d414c679e0975cc531,0x4c7c55514354531d9575,0xe0576551318fb805d954,0xd91318ef825d9544c63d,0x8f7815d3654c63be0975,0xd9741cc6b9e0965d0731,0xcc6e5e055450f31ab584,0x59371553319d583dc554,0x55331c7565dc554cc72d,0x8ef825d954cc63ee0176,0xdc553d063be0975d9331,0xd071d5977154f419b584,0xe097654f418fb805d953,0x90d518ef825d663d063b,0xcb564dc543d463be0976,0x55143d465d6177150f51,0xd46a7e0d6490f51c3f76,0x5937254f51c3d7559243,0x59351ab9801cd64d478b,0xaad821cd64d46ad60473,0x9cd64d46ade057359351,0x10face054358043c9f73,0xe1d4358443aeb8254d60,0x58843ae78254d6110f2d,0x8ef8754d6210fa9e0543,0xdc54310f8d5977150c43,0x10f2de077650c43cb776,0x5517018543c6d65dc953,0x18543cf1655c06150f6c,0xe37655506150f3cd9570,0x5946150ebce016518543,0x50e3de1d6518543ae782],#[0xe0165d8543ba58295361,0xd8543ae7825976150ebc,0x8ef825d76150e3ee0175,0x94f6150eb9e0953d8543,0x50e3d61f54d8543e5753,0x5d475d8543ab5841d761,0xd8543af3805d76150f1d,0x9af825d64350eb9e0975,0x5d95350f0fd977454d43,0x50e7660073551438fb80,0xd9773551439d5811cd54,0x55143b99801cd5450f17,0x87f875946550ee560473,0xdc16550f3c1c77059543,0x50f3c2077059543cf371,0xdc87159543cf381dc165,0xd0e43ce772dc56550f39,0xb8f825974390eabe0965,0x5c75490f65e0576d0e43,0x552ba6007259643c7565,0xe1d6318d54cd9635c063,0x1800cf1815c06355237,0x120420f0360c02a09015,0x1e0721b0661805a1504e,0x2a0a2270962408a2107e,0x360d2330c6300ba2d0ae,0x421023f0f63c0ea390de,0x57156541414a51a4510e,0x631866017a5d16e5a162,0x6f1b66c1aa6919e66192,0x7b1e6781da751ce721c2,0x872168420a811fe7e1f2],#[0x8083010408d22e8a222,0x0,0x0,0x0,0x6182e230040a04]]
def g119H5 := limbs80 #[#[0xe8000000530000500,0x6c20040000]]
set_option maxRecDepth 16000 in
def g119D6 := limbs80 #[#[0x67bb8ac898f954350531,0x1f2a87a0e633bdc9654c,0xc75ab268398dd573d073,0x43c7ac8a9ea33bdc965c,0x10f5aa1ac221eb943580,0xc43c7acaa1887ab50d62,0x450ef8b80c2a1cbf7650,0x95439f6e0b2a876b5ca5,0x6590ecebb68721cf7715,0x18d549f2e031aa93bdc9,0xf314c7f29926290cf571,0x5cc531beae998a63f550,0xd5414c7daa1a8298df57,0x4354531faa86a8a637d5,0x551514c7baa9aa298fd6,0x77150d31beee2a1a63dd,0xddc5534c7ceaa28698fd,0xbf6455131bdee4a9a637,0x3f5d9544c73eb2aa898e,0xef771591319feecaa263,0x33f5d7644c67fbaac898,0x8ef77159531bdee4b2a6,0x633fdd1654c777b92ca9,0x98fb543d07319fae9b2a,0xe63ed59341cc6fab9e83,0x398ef765d0731deacba0,0x1e63f5dc543cc6fabb68,0xa998def7254f31f3aa8a,0xaa663af59154cc6fbb8a,0x2a998cfd7655331cfaca,0xab2663bddc564cc67fbb,0x92cb98cfd75d93319fee],#[0xe8b2e63bbdc965cc6f7b,0xb8a86a0cfd74d97319fe,0xee4a9a83af59543507db,0xfbb2a6a0e7d6554d41bd,0x7ae929a837d5c6535067,0x7bb8acaa0cfd7694d41b,0xf6a86a8e833fdcd65507,0x77ab1aa3a0f755354741,0x1d7acaa1e83eddc543d0,0x6f7b92a7a0df77154f4,0x419faeca9e839f59553d,0xd06deba4a7a0cff7654f,0xf41deee2b1e833f5da53,0x5d067ebacc7a0cff7558,0xd51beee2a1aa33fdcd6,0x43546bebaa86a8f3d545,0x90d51beae321aa33fdd9,0x5535467ebb486a8d7d75,0x454d51edee4a9aa3dddc,0xcd54547bbb8aa8a8d7f7,0x5450f51beee2a1ea35fd,0x5d543d475eb2287a8f3d,0xf7650f519faeca1ea35f,0xf5d643d475eb2487a8cf,0x6f7254f519faed21ea35,0x5fdd153d473eb22a7a8f,0xcff7458f51cfaa8b1ea3,0x35fdcd54d467eba4c7a8,0x8ebc73593519fee6b26a,0xa3af9cd64d475eb9ac9a,0x21ef95358043d7ee6b26,0x887bd54d6110f7da9ac0],#[0x421eed5358843deea6b0,0x1887eddc54310f77a9ac,0xa621ebf7650c43d7acaa,0xa98879f5955310ef7b92,0x6a621e7d65d4c439feec,0x830a873f5d66310e7ebb,0x28c2a1ef56518543f6aa,0xc5b0a877d9d86150f7bb,0x21ec2a1ef762d8543dea,0xca9b0a87ed5536150fdb,0xbba6c2a1ef764d8543f6,0xeacbb0a87bd1976150fd,0x7bb2ec2a1ef665d8543d,0xdeae5b0a873f5d76150f,0xf7aa9ec2a1ef772d8543,0x3deea7b0a87bd94f6150,0xf7baa6c2a1ef554d854,0x43de8ebb0a87bddd3615,0x50f7b3aec2a1ef575d85,0x943beee2b1287bddd761,0x350e7ebaec4a1ebd54d8,0x4d43e7aa8a9a876f5d64,0x5350e7ebb2a6a1dbf745,0xd4d43e7aa9a9a87d7d4e,0xd5450f3fb2ea6a1dbd74,0x555143bbee6aa287771c,0xc95450edfb8aa8a1e7f6,0x7355143f38e6aa2876fd,0xd955450f9e32aa8a1f9f,0xe7695143b7aeb2a287cf,0x75cf5450efab8ea8a1db,0x7f65d5143bbce7aa2877],#[0x3f9d86550f3eb28caa1e,0xdf77159543bf6e0b2a87,0x79fd956550ef7b92caa1,0x1ef47159543df6e0b2a8,0x873fdc56550f7bb8acaa,0xa1cff7359543dbee6b2a,0xa879fd966550efab8cca,0x721cfd72d95439fae3b2,0x1c87af5974390fcfa9e8,0xa921f9e65d0e43f3acba,0xaa4879f5955490eefb9a,0xea921ddd73d5243beae3,0x2b2c877bdc96590f3eb2,0x92cb21eec72596439fee,0xa9a9e873fdc96590f77b,0xbb2a9a1dbd74d4f43e7a,0x2e031aa93f5cf615535f,0xeb18c6aa5f57118d54bf,0xeee2b1aa97edc1635536,0x7eb8ec6aa6df6398d54b,0x101b81600e80b0078002,0x84203c83703182c02682,0x6486105b858056851047,0x708188007a87506f86a0,0x89e09a89509189008c88,0xba8b50af8ac0aa8a70a3,0xf0cb8c80c68c30c18be0,0x8e00de8db0d78d40d08c,0xf28ef0ed8ec0e88e50e1,0xb1099061049010ff8fa0,0x92011e91911391210e90,0x3693512f92e12a927125],#[0xd14994814493f13d93a1,0x96215e95d15995815294,0x7497316f96c168967163,0xb18798418097f17b9781,0x9a219e99b19599218e98,0xb49b31b19b01ac9ab1a7,0xf1cb9c21be9bd1b99b81,0x9e21de9db1d79d41d29c,0xfc9f91ef9ec1ea9e91e5,0x7213a0e20aa07203a021,0xa2a226a2321fa1e21aa1,0x44a3f23da3c234a3322d,0x324fa4e24ca4b247a462,0xa66262a6125fa5a256a5,0x84a81279a7626ea6d26b,0xd299a96292a9128da8a2,0xaac2a6aa52a3aa22a0a9,0xbeabd2bbab82b6ab32af,0x72d1acc2c8ac52c3ac02,0xae62e2ae12ddadc2d8ad,0xfcaf92f5af22eeaeb2e7,0x5311b1030cb0b305b022,0xb28324b2331db1a316b1,0xe00f0f2fb2e32cb2b329,0xe0083023803e00780106,0x82f802c1e0083380208,0x2380208e008238020807,0x8e00830283c38408e008,0x34302e00423802e00400,0xc206010808042e00608,0x41068308041820019,0x410641083010c4308181],#[0x200080d082040400c060,0x810c040020400c041010,0x81042010804041000,0x4304040020410806041,0x2040410400200080d0b,0x681080d0420004102040,0x20004103040c1060800,0x10c410800a0428100282,0x800203a20b0410204,0x4101000810104100041,0x10008101041010004181,0x81060c10105041010704,0x1030108041010412042,0x41000c1000000c1001,0x10504104626008101010,0x22041816204181620404,0x6110b070040804000181,0x28102040c1000c082a20,0xc10014160050c1626008,0x3010c842430604181050,0x81000020008000298980,0x60090c108050c1000018,0x18300004a20884100062,0x2c104080400300068b04,0x400100101c1041304,0x4130420000006205041,0x4000003040000428103,0x780205e0080010004021,0x81000c10084100001000,0x242040c1060588103041,0xc1000d0820304120c,0x1000d042030418100081],#[0x18]]
def g119H6 := limbs80 #[#[0x210d040c040030a20006,0x4ea10036400001c0000,0xb4c34685111e81c45508,0x2800200000072f043633,0x81fdcbc23000f27612c,0x914000bc891500000,0x436100d3e000000e4b,0xdab0009443370,0x2cc23c00052c510e3d00,0xc9000000849816b3fd2d,0xd92944a000018f0a0014,0xa30b2aa1340600070ed1,0x50dc2000000c38000547,0x51b5d500cb4d000d459,0xa410000009425ca5c4e4,0x250001c5434705524a2e,0x3000e20587411000d319,0x152c54000632d0,0x53d8463ba2b104a1a207,0x603a735a91d220000005,0x32100094e748f39000a2,0x4f000a1720900091940d,0x10f10840b0007]]
set_option maxRecDepth 16000 in
def g119D7 := limbs80 #[#[0xe58043af99351af59351,0x59443bb58843bd58443b,0xe43bdd85439f994439f,0x521cfd5254bb58a54e7d,0x31bf98d21bf58d21fd4c,0x1fd54531fd50531fdcc5,0xf790d31f750d31bfd893,0xf59531bfd9131bf59131,0x58b31fdd0731bfd9531b,0x9331f790f31f750f31bf,0x731bf59731bfd9331bf5,0x41bf59541ef50d41bfd9,0x1bf58f41ef50f41fd547,0xdf54d51bf59741bf98f4,0xf58f51df54f51df55151,0x59351df55351bf98f51b,0x9443bf98c43ef50c43bf,0x543fdd8543fd18543bf5,0x43ef90d43bfd8943bfd8,0x3bf59543ef95143ef551,0xbf58a43bf58643bfd954,0xf59643bf59243efd0e43,0x59743ef55343bfd9643b,0x8554bf98c54bf58c54bf,0xe54bfd8d54bf18d54bfd,0x31bf59654bf98e54bf58,0x1ff50d31ff58931ff4c9,0xff59131ff55131ff54d3,0xf54f31ff50f31ff59531,0x59731ff59331ff55331f,0x4f41ff94d41ff54d41ff,0xd51ff50d51ff94f41ff5],#[0x43ff90f51ff50f51ff90,0x3ff58543ffd4c43ff54c,0xffd8943ff58943ffd854,0xf94d43ff54d43ff90d43,0xd5143ff55143ffd4d43f,0x9543ff59543ff19543ff,0x243ffd4e43ffd9543ff9,0x43ff59643ffd5243ff55,0x4ff58554ffd4f43ff996,0xff58d54ff18d54ffd855,0x1b000ffd8d54ff98d54,0x20e70c50a308105f03d,0x71d51b318a1681461241,0x2ae28c2712562342121f,0x8736c35132f3142f22d0,0x744c42a40f3ed3cb3a93,0x52c5114f64d44ab48946,0x215f85d65b459957054e,0x66e66c46a968e66c64a6,0x7e97c77a578375a73f71,0xe58bc89a87884f83480b,0x69db9b298996793e9078,0xa98a7da69a47a25a119f,0x5cb41b1fb04ae9ac7aac,0x7bfebe3bc8badb99b7eb,0xcbbca7c93c7fc64c50c2,0x86d64d50d2ed0ccf1cdd,0x7e1adffddddc2db5d9ad,0xec2eb5e93e63e4fe3be2,0x203890426012241c02c3,0x61380408184e01020612,0x1890980408184e01020],#[0x9c02040c27008110c9c,0x14610c03c41213008122,0x688430061e20d184300f,0x633010106601e1818780,0x7863300f0c78cc04048,0x83f00c10604c03c4198,0xa43064300c10603c0404,0x30d807864300d1e201c0,0x180688182601e206c020,0x831580688181e0202041,0x152430c2b00f103601e1,0x284c1044883304112260,0xc3601424409070090c,0x208cc02c4c0287861b01,0x60e0e016185070700b1,0x1b0081036016204c02c4,0x6138040a10488c018512,0xf12187804182b00f1020,0x83c030409807861300f0,0x2700817106820c260186,0x202181e014101c018608,0xc204c03c6881300f1820,0x6c02841380408244600,0x184e01028dc030302082,0x5121300810208c024408,0x8386158078824208c018,0x2101e01468104101e01,0x209c02030a104e010202,0x50e08d18186082700814,0x82044504608304043460,0x2188850630404101c11,0x61018682206442830c2],#[0x11141102044418307043,0x5030c222070440c28406,0x38210310185060c50418,0x284848a0c0143080818,0x606843182020c121418,0x8406241061061e10d1e1,0x80c48210187043048a0,0x80406282070508410341,0x302182030d08a0822242,0x20c1a10c0c2080c3040c,0x34210814104061060422,0x91214020644850040630,0x182030c3021]]
set_option maxRecDepth 16000 in
def g119H7 := limbs80 #[#[0x41a00048040643000413,0x800d0512004024006431,0x4e86480004c008,0x0,0x1ac80000,0x15ba0000,0x1894,0x2d0800000031c4001a41,0x40000000000000126336,0x1ce,0x0,0xa800000000028003c8a0,0x4,0x16040000000000,0x6bf0000002c4e000000,0x559c000000000000000,0x31580015a600000,0x6da9180000005f400000,0xfbb78800003d5a,0x146e0000000000,0x0,0x0,0x1ed7067320b000000000,0x3a40000000007d,0x1b400000000000000000,0x7,0x0,0x1ec5000,0x31bad942000000000000,0x87a7b557800251a00089,0x28e00000000004974f,0x359e0000],#[0x34780000000000,0x1ec30000000000000,0x13040008ce000000,0x0,0x0,0x0,0x3db80000220,0x0,0x20000000000000000000,0x97,0x28c3552b51a400000000,0x2477006e43001e2,0x128e00000000000000,0x0,0x69bc000000,0x0,0x7a6000000000,0x4c8c00000000000,0x199000000033a00000,0x0,0x0,0xeaa000252c001ca4000,0xc0000000000608000000,0x84000a5a8000000000e9,0x2380000000000000001d,0x38be5300005,0x34ca0000004298,0x449c000000,0x1250000000,0x0,0xa1000000000000000000,0x13b4760694a4e01],#[0x24280000000000000,0x0,0x6058000000f89000,0x3aa000000001820cc00,0x0,0x87080000,0x29b80000000,0x4f38,0x34a2000f2a00000018d6,0x63317d84000a7a000000,0x7052400000000ab05c6e,0x90a000000048a5564f,0x3ed400000000000000,0x0,0x800040200000038b0000,0xfeb0000000c6c0adc53,0x26f68000000000000000,0x830b76704c000b1,0xeca00000000,0x36d00e40000000,0xbaa00031770790000000,0xddc000000106a,0xd51800,0x6800069ecdfb76f16600,0xe2444fb3400000000062,0x8200000000000002d7b6,0x7e0004128001c480004,0x13cc00000005ae,0x12bc0000000000000000,0x0,0x653eda2b800000000000,0x26800000000006a0002b],#[0xa4b00022e8000e97a,0x1cea0000000000,0x38120000000000000a80,0x0,0xc1d93e000000000,0xed71d000000000000000,0x237a992a,0xe789b400018ec6b40000,0x205c00121c0000000000,0xa880000910000000,0xc6b48000000175000000,0xd0182c000148210,0x11980000000003cb00,0x869f7400000008186550,0x29200000000003,0x0,0xfa4db2c9cef822000000,0x80000000000000000c3,0x9340001e92000bdd10,0x7ecc0000,0x6764c940000000000,0x0,0x47280034537b6000,0x10000000000000000000,0x1e40000000000000be,0xd800000000000000000,0x18c400000000000001,0x60480000000000000,0x2c7a000000000301dc1e,0xe31800,0x26cc00000046dc00000,0x0],#[0x2484e11463800053e0,0x0,0x80000000000000000000,0xf1c11360000000000235,0xcb1524ca3101,0x33a686400000000,0x0,0x4b06940,0x6680000,0x2104e7b9c000000,0x0,0xf9a00000069fc00000,0x91000000000000000000,0x8,0x40a800000000052f8,0x1af913a000aa42180000,0xc670000000000ccc000,0x4f28000000000000000,0x0,0x0,0x4665900000028b60000,0x50a2ca764e0000000,0x0,0x0,0x54000000d188b5400000,0x7a940000000005d,0x41900033140,0xa7d46fdb671020000000,0x80000000000000000001,0x5dd,0x0,0x0],#[0x43ef8e89100000,0xa3e73900000000000,0x20980030bc000d168000,0xa069a8ac800c6,0x28365b000,0x7e316f000000,0x6ea558002d17acb15700,0x1e4f00000000009,0x0,0x0,0x97a000,0x0,0x1ece3d2e1adc00000000,0x5000001ed100051919,0x32580000000,0x1f1a0000000000,0xee940007218000000000,0x70680000002d83a4,0x52a000e05000000000,0x6aa400000004c80,0x2dc000000000000000,0x5a000421c0000000000]]
def g119D8 := limbs80 #[#[0xf41fea0ffcc7fa63fd21,0x87fd43fe21ffd47faa3f,0x3fca9fd54fe2a7fd0ffc,0x409a4b44e1f8c03c0c00,0x3c54203c3cf602c54490,0xa03c404d4203c504c420,0x2c42204032a00491012,0x80f1040811898081c806,0x42602043443203c5044,0x980814b2a03c42448081,0x210]]
def g119H8 := limbs80 #[#[0xb200040250040200003,0x23c0000000843107c2,0x2da0000000,0x17640000000000000,0xa9edbc00000000210800,0x29800f0,0xd610e48c0,0x35a800000000000,0x6b0000000000000,0x2d510240007014cc1180,0x0,0x2034000000000000000,0x41c0000000000,0x3cd3474000000001c2,0x70000000000d34000000,0x9040018640028,0x34e0002d4cfbc00,0x339c,0x3195d2c0000000000,0x38a800,0x99560000000c840014b4,0x29240000033,0x3168000002687c4000,0x30000000002452511054,0x35,0x316c00000,0x0,0x35e00000000000,0xb4c0000013d7e2c00000,0x880000488000000,0x1990000001c140,0x0],#[0x480008c4000001048000,0x31c40000000000000031,0x4c0032a400000000000,0x26da97c000000000001,0x0,0x970000001db000000000,0x3140002,0x333bd880024a00000000,0x3bba97400,0x30000002438000000000,0x3999946008090003c,0x0,0x3959115d64,0x18b80000000000000,0xdc800000000000000000,0x614f40000019b4000003,0x15e64dc002096c,0x14bc00000000000000,0xac00346acf8000000,0x0,0x46c000001c0400000000,0x3fc2af7c00000000191f,0x1cb0000000002c,0x289c00000374800,0x9def78,0x0,0x3a58c1000,0x21d0000000000000000,0xd1009780000000000000,0xbd39d505800080c00245,0xa40000000010d800392b,0x1aa00000000000000017],#[0x192000000000,0x1f3400235b818000000,0x14e40000000,0x35c15c00000000000000,0xec000000000002,0x0,0xa400000000000000000,0xd578c0000000000002,0x1cfc0000000000,0x0,0x1584003b10,0xda40000000000000,0x878000000000000dcc00,0xe7c000d9c3a0000,0xdc04c80,0xc2cdb8000003d8c00000,0x9b800000000002,0xc0000000000000000000,0x53800000187f5a,0x25d8000000000000000,0x800000013c8440000000,0x1360000000000002ce]]
def g119D9 (j : Nat) := if j=0 then 0x8200ff else 0
def g119H9 := limbs80 #[#[0x3940055d4e48b290c80,0xc640049fd6692c006a0,0x6c67bb46aca22d14c000,0x17860f640f28005d2c]]
def g119L : Nat → Packing
  | 4 => (6,5,5,0,0,5,0,g119D4)
  | 5 => (86,4,5,0,0,10,0,g119D5)
  | 6 => (238,3,5,0,0,12,0,g119D6)
  | 7 => (122,2,5,0,0,12,0,g119D7)
  | 8 => (14,1,5,0,0,9,0,g119D8)
  | 9 => (1,0,5,0,0,0,0,g119D9)
  | _ => emptyPacking
def g119I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 23 0 7 3 0 g119H5
  | 6 => lookupWord 24 137 7 12 7 1 g119H6
  | 7 => lookupWord 74 1103 3 13 8 1 g119H7
  | 8 => lookupWord 38 563 3 12 7 1 g119H8
  | 9 => lookupWord 6 31 5 9 4 1 g119H9
  | _ => fun _ => none
def g119 : Forest := ⟨119,9,fun i => g119Y[i]?.getD (0,0),g119C,g119A,g119L,g119I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P4_0 : block g119 4 0 6=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B4 : block g119 4 0 6=true := g119P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P5_0 : block g119 5 0 86=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B5 : block g119 5 0 86=true := g119P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6_0 : block g119 6 0 21=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6_21 : block g119 6 21 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6_117 : block g119 6 117 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6_213 : block g119 6 213 25=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B6 : block g119 6 0 238=true := (@block_merge g119 6 0 117 121 (@block_merge g119 6 0 21 96 g119P6_0 g119P6_21) (@block_merge g119 6 117 96 25 g119P6_117 g119P6_213))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P7_0 : block g119 7 0 11=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P7_11 : block g119 7 11 63=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P7_74 : block g119 7 74 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B7 : block g119 7 0 122=true := (@block_merge g119 7 0 11 111 g119P7_0 (@block_merge g119 7 11 63 48 g119P7_11 g119P7_74))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P8_0 : block g119 8 0 14=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B8 : block g119 8 0 14=true := g119P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P9_0 : block g119 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B9 : block g119 9 0 1=true := g119P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119T : checkedTables g119 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g119 0 0 0 = true)
  · exact (rfl : block g119 1 0 0 = true)
  · exact (rfl : block g119 2 0 0 = true)
  · exact (rfl : block g119 3 0 0 = true)
  · exact g119B4
  · exact g119B5
  · exact g119B6
  · exact g119B7
  · exact g119B8
  · exact g119B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119G : graphValid g119 (boundsBefore K111) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low119 : Lower true (varsX 119) (graphGoal 119) 10 := lower_forest (g:=g119) (i:=0) (hints:=1092) (before_sound K111 V111) g119G g119T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K119 := extendKnown K111 10 [(119,[]),(215,[117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V119 : Known true K119 := extend_ok (m:=119) V111 low119 (by decide +kernel)
def g123Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf801fffff83fffffc8,0xdd0a41400f8000f83ff])),(BitVec.ofNat 152 (word80 [0x5014028010800100c8,0x8500014210842108421]))),((BitVec.ofNat 152 (word80 [0xfffe003fffc1ff81cf,0x334350c0000001f07c00])),(BitVec.ofNat 152 (word80 [0x62188b10a0048209ce,0x334140416b5ad6b5ad6b]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffc00001fffc87,0xc524474c1f003e00001f])),(BitVec.ofNat 152 (word80 [0x80200c02c108140005,0x5244648c6318c6318c6]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000031,0x2e4c7a23e007c0007fe0])),(BitVec.ofNat 152 (word80 [0x4010030000181011,0x4043a00842108421084]))),((BitVec.ofNat 152 (word80 [0x44,0x90af89b00007ffff8000])),(BitVec.ofNat 152 (word80 [0x48120240211202000,0x808a81a2108421084210]))),((BitVec.ofNat 152 (word80 [0x33a,0x529a034bfff800000000])),(BitVec.ofNat 152 (word80 [0x701c0380421c04322,0x528a010318c6318c6318]))),(0x0,0x0),(0x0,0x0)]
def g123C : List ColumnInfo := [(8,0,115,0,7),(16,0,107,0,7),(32,0,91,0,7),(64,0,59,0,7),(0,2,73,48,6),(1,0,122,0,6),(2,0,121,0,6)]
def g123A : List (List Nat) := [[],[99,84]]
def g123D7 := limbs80 #[#[0x1552e2a46f03ee21f510,0x4b8a9]]
def g123D8 (j : Nat) := if j=0 then 0x346111bf else 0
def g123H8 (j : Nat) := if j=0 then 0x1b4 else 0
def g123L : Nat → Packing
  | 7 => (2,1,3,0,0,5,0,g123D7)
  | 8 => (1,0,3,0,0,0,0,g123D8)
  | _ => emptyPacking
def g123I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 2 0 5 1 0 g123H8
  | _ => fun _ => none
def g123 : Forest := ⟨123,8,fun i => g123Y[i]?.getD (0,0),g123C,g123A,g123L,g123I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_0 : block g123 7 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B7 : block g123 7 0 2=true := g123P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P8_0 : block g123 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B8 : block g123 8 0 1=true := g123P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123T : checkedTables g123 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g123 0 0 0 = true)
  · exact (rfl : block g123 1 0 0 = true)
  · exact (rfl : block g123 2 0 0 = true)
  · exact (rfl : block g123 3 0 0 = true)
  · exact (rfl : block g123 4 0 0 = true)
  · exact (rfl : block g123 5 0 0 = true)
  · exact (rfl : block g123 6 0 0 = true)
  · exact g123B7
  · exact g123B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123G : graphValid g123 (boundsBefore K119) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low123 : Lower true (varsX 123) (graphGoal 123) 9 := lower_forest (g:=g123) (i:=0) (hints:=67) (before_sound K119 V119) g123G g123T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K123 := extendKnown K119 9 [(123,[]),(125,[33,101]),(219,[117]),(221,[33,101,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V123 : Known true K123 := extend_ok (m:=123) V119 low123 (by decide +kernel)
def g183Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffff8007ff807ff807,0xfd8daa908b000f00f00f])),(BitVec.ofNat 152 (word80 [0xa0150350250d0290b0,0xa589aa10031111111111]))),((BitVec.ofNat 152 (word80 [0x7fffff800007ffff8,0x393a0597400f00f00f0])),(BitVec.ofNat 152 (word80 [0x302602603616032121,0x3383a051601111111111]))),((BitVec.ofNat 152 (word80 [0x7ffffffffff800000,0x6dd6d60a40000000f00])),(BitVec.ofNat 152 (word80 [0xc5385385381853c1c1,0xc6dd6d60a4dddddddddd]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7ffffffffffffffff,0xf9407903220f00f00fff])),(BitVec.ofNat 152 (word80 [0x4004004000040000,0x2222222222]))),((BitVec.ofNat 152 (word80 [0xf80000000000000000,0xbac4e691f000fff000])),(BitVec.ofNat 152 (word80 [0x18018018020180202,0x304482904444444444]))),(0x0,0x0),(0x665163c4cffff000000,(BitVec.ofNat 152 (word80 [0x60060060040600404,0x44102c0c8888888888]))),(0x0,0x0)]
def g183C : List ColumnInfo := [(1,0,182,0,8)]
def g183A : List (List Nat) := [[],[117],[16],[16,117]]
def g183D8 (j : Nat) := if j=0 then 0x7f else 0
def g183L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g183D8)
  | _ => emptyPacking
def g183I (_ _ : Nat) : Option (Nat × Nat) := none
def g183 : Forest := ⟨183,8,fun i => g183Y[i]?.getD (0,0),g183C,g183A,g183L,g183I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P8_0 : block g183 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B8 : block g183 8 0 1=true := g183P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183T : checkedTables g183 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g183 0 0 0 = true)
  · exact (rfl : block g183 1 0 0 = true)
  · exact (rfl : block g183 2 0 0 = true)
  · exact (rfl : block g183 3 0 0 = true)
  · exact (rfl : block g183 4 0 0 = true)
  · exact (rfl : block g183 5 0 0 = true)
  · exact (rfl : block g183 6 0 0 = true)
  · exact (rfl : block g183 7 0 0 = true)
  · exact g183B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183G : graphValid g183 (boundsBefore K123) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low183 : Lower true (varsX 183) (graphGoal 183) 9 := lower_forest (g:=g183) (i:=0) (hints:=1092) (before_sound K123 V123) g183G g183T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K183 := extendKnown K123 9 [(183,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V183 : Known true K183 := extend_ok (m:=183) V123 low183 (by decide +kernel)
def g187Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf87ffe01ffff8fffe6,0x33c2300000f8000f83ff])),(BitVec.ofNat 152 (word80 [0x110014140a01200422,0x11c03084210842108421]))),((BitVec.ofNat 152 (word80 [0xff87fffe00fff1fe0b,0xbad50001f0001f07c00])),(BitVec.ofNat 152 (word80 [0xa01058182c0a04088b,0x3a9518c6318c6318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7ffffff0001ffc5,0xea98e003e0003e00001f])),(BitVec.ofNat 152 (word80 [0xc2216020302c485005,0xea18c318c6318c6318c6]))),((BitVec.ofNat 152 (word80 [0x7fffffffffe0012,0x6c4f807c0007c0007fe0])),(BitVec.ofNat 152 (word80 [0x44180404030006110,0x6c068210842108421084]))),((BitVec.ofNat 152 (word80 [0xfff800000000000029,0x84009f800007ffff8000])),(BitVec.ofNat 152 (word80 [0x200808040008000,0x421084210842108]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x10,0x51304ffffff800000000])),(BitVec.ofNat 152 (word80 [0x401010080010000,0x842108421084210]))),(0x0,0x0)]
def g187C : List ColumnInfo := [(1,0,186,0,8),(2,0,185,0,8),(8,0,179,0,8),(16,0,171,0,8),(32,0,155,0,7),(128,0,59,0,7)]
def g187A : List (List Nat) := [[],[117],[64,49],[64,49,117]]
def g187D8 (j : Nat) := if j=0 then 0x2a54dc0dfd54 else 0
def g187D9 (j : Nat) := if j=0 then 0x2c4581bf else 0
def g187H9 (j : Nat) := if j=0 then 0xe else 0
def g187L : Nat → Packing
  | 8 => (1,1,3,0,0,0,0,g187D8)
  | 9 => (1,0,3,0,0,0,0,g187D9)
  | _ => emptyPacking
def g187I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 1 2 0 4 0 0 g187H9
  | _ => fun _ => none
def g187 : Forest := ⟨187,9,fun i => g187Y[i]?.getD (0,0),g187C,g187A,g187L,g187I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P8_0 : block g187 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B8 : block g187 8 0 1=true := g187P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P9_0 : block g187 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B9 : block g187 9 0 1=true := g187P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187T : checkedTables g187 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g187 0 0 0 = true)
  · exact (rfl : block g187 1 0 0 = true)
  · exact (rfl : block g187 2 0 0 = true)
  · exact (rfl : block g187 3 0 0 = true)
  · exact (rfl : block g187 4 0 0 = true)
  · exact (rfl : block g187 5 0 0 = true)
  · exact (rfl : block g187 6 0 0 = true)
  · exact (rfl : block g187 7 0 0 = true)
  · exact g187B8
  · exact g187B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187G : graphValid g187 (boundsBefore K183) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low187 : Lower true (varsX 187) (graphGoal 187) 10 := lower_forest (g:=g187) (i:=0) (hints:=67) (before_sound K183 V183) g187G g187T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K187 := extendKnown K183 10 [(187,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V187 : Known true K187 := extend_ok (m:=187) V183 low187 (by decide +kernel)
def g189Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf801fffff83fffff88,0xd41a49c0007c00f83ff])),(BitVec.ofNat 152 (word80 [0x501402801080010380,0x8410014210842108421]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffe003fffc1ff8197,0xa14d5388000000007c00])),(BitVec.ofNat 152 (word80 [0x65194b28a005420996,0xa14d438b7bdef7bdef7b]))),((BitVec.ofNat 152 (word80 [0xffffffc00001fffcd7,0xc5b0444400f801f0001f])),(BitVec.ofNat 152 (word80 [0x80200c02c108140043,0xc5904400c6318c6318c6]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000021,0x2ed47a201f003e007fe0])),(BitVec.ofNat 152 (word80 [0x4010030000181021,0x4903800842108421084]))),((BitVec.ofNat 152 (word80 [0x44,0x903f89b3e0003fff8000])),(BitVec.ofNat 152 (word80 [0x180600c0210602004,0x102481a1084210842108]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x33a,0x528a034bffffc0000000])),(BitVec.ofNat 152 (word80 [0x60180300421804018,0x20a024a108421084210]))),(0x0,0x0)]
def g189C : List ColumnInfo := [(0,4,169,16,8),(4,0,185,0,8),(8,0,181,0,8),(1,0,188,0,7),(16,4,169,0,7),(32,0,157,0,7),(128,0,61,0,7),(33,0,156,0,4),(129,0,60,0,4),(160,0,29,0,4)]
def g189A : List (List Nat) := [[],[117],[80],[80,112],[112,80],[112]]
def g189D6 := limbs80 #[#[0x277b92caa07395454140,0xddee4b2a817bdc96550,0x20dc52f287d06bf1180,0x171e01e3e3c03e3d]]
def g189D7 := limbs80 #[#[0xfd9540bf59540fe54140,0x5d0884603600ff59540b,0x2481f1cb41881c3c725a,0x78d25b1c085b1cb41c5,0x92]]
def g189H7 (j : Nat) := if j=0 then 0x28070000503b000 else 0
def g189D8 (j : Nat) := if j=0 then 0xf1b1472a0ffd40 else 0
def g189H8 := limbs80 #[#[0x93008281b800,0x3000]]
def g189D9 (j : Nat) := if j=0 then 0x6513241bf else 0
def g189H9 (j : Nat) := if j=0 then 0x9200003 else 0
def g189L : Nat → Packing
  | 6 => (4,3,4,0,0,7,0,g189D6)
  | 7 => (4,2,4,0,0,8,0,g189D7)
  | 8 => (1,1,4,0,0,0,0,g189D8)
  | 9 => (1,0,4,0,0,0,0,g189D9)
  | _ => emptyPacking
def g189I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 11 0 6 2 0 g189H7
  | 8 => lookupWord 1 13 0 8 2 2 g189H8
  | 9 => lookupWord 1 5 0 6 0 2 g189H9
  | _ => fun _ => none
def g189 : Forest := ⟨189,9,fun i => g189Y[i]?.getD (0,0),g189C,g189A,g189L,g189I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P6_0 : block g189 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P6_2 : block g189 6 2 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B6 : block g189 6 0 4=true := (@block_merge g189 6 0 2 2 g189P6_0 g189P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P7_0 : block g189 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P7_3 : block g189 7 3 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B7 : block g189 7 0 4=true := (@block_merge g189 7 0 3 1 g189P7_0 g189P7_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P8_0 : block g189 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B8 : block g189 8 0 1=true := g189P8_0
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
  · exact (rfl : block g189 5 0 0 = true)
  · exact g189B6
  · exact g189B7
  · exact g189B8
  · exact g189B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189G : graphValid g189 (boundsBefore K187) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low189 : Lower true (varsX 189) (graphGoal 189) 10 := lower_forest (g:=g189) (i:=0) (hints:=1027) (before_sound K187 V187) g189G g189T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K189 := extendKnown K187 10 [(189,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V189 : Known true K189 := extend_ok (m:=189) V187 low189 (by decide +kernel)
def g231Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf8001fffffff00ff57,0xa021d7a224003f03f03f])),(BitVec.ofNat 152 (word80 [0x500d40250052161413,0x8001d0a2201041041041]))),((BitVec.ofNat 152 (word80 [0xffffe0007fffff0029,0x7e9bc066080fc0000fc0])),(BitVec.ofNat 152 (word80 [0x604981360464242629,0x2419c066085145145145]))),((BitVec.ofNat 152 (word80 [0xffffffff800000009d,0x8e48a9b5c00000fc0000])),(BitVec.ofNat 152 (word80 [0x820e0838217838381d,0x8a4881b5c134d34d34d3]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffffa0,0x49c585ccf7f000000fff])),(BitVec.ofNat 152 (word80 [0x9002400980000080,0x48800508d4a28a28a28a]))),((BitVec.ofNat 152 (word80 [0x91,0x75383e5b400000fff000])),(BitVec.ofNat 152 (word80 [0x4e013804e00404080,0x75302e4802cb2cb2cb2c]))),((BitVec.ofNat 152 (word80 [0x4e,0x937660389bffff000000])),(BitVec.ofNat 152 (word80 [0x7001c007000808044,0x13662010030c30c30c30]))),(0x0,0x0)]
def g231C : List ColumnInfo := [(2,0,229,0,7)]
def g231A : List (List Nat) := [[],[117]]
def g231D7 (j : Nat) := if j=0 then 0x7f else 0
def g231L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g231D7)
  | _ => emptyPacking
def g231I (_ _ : Nat) : Option (Nat × Nat) := none
def g231 : Forest := ⟨231,7,fun i => g231Y[i]?.getD (0,0),g231C,g231A,g231L,g231I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P7_0 : block g231 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B7 : block g231 7 0 1=true := g231P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231T : checkedTables g231 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g231 0 0 0 = true)
  · exact (rfl : block g231 1 0 0 = true)
  · exact (rfl : block g231 2 0 0 = true)
  · exact (rfl : block g231 3 0 0 = true)
  · exact (rfl : block g231 4 0 0 = true)
  · exact (rfl : block g231 5 0 0 = true)
  · exact (rfl : block g231 6 0 0 = true)
  · exact g231B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231G : graphValid g231 (boundsBefore K189) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low231 : Lower true (varsX 231) (graphGoal 231) 8 := lower_forest (g:=g231) (i:=0) (hints:=1621) (before_sound K189 V189) g231G g231T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K231 := extendKnown K189 8 [(231,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V231 : Known true K231 := extend_ok (m:=231) V189 low231 (by decide +kernel)
def g235Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7ff83ff83ffffe88,0x4941ae940007c1f003ff])),(BitVec.ofNat 152 (word80 [0x50050801080010280,0x48410014210842108421]))),((BitVec.ofNat 152 (word80 [0xff80003fffc1ff8195,0xf1c510a800f800007c00])),(BitVec.ofNat 152 (word80 [0x46096104a004220995,0xe1c100a0e739ce739ce7]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffc00001fffcd7,0x853244441f003e0f801f])),(BitVec.ofNat 152 (word80 [0x8018000c108040051,0x85000440421084210842]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffe000021,0x2e5c7923e000000fffe0])),(BitVec.ofNat 152 (word80 [0x901200090000481020,0x147901084210842108]))),((BitVec.ofNat 152 (word80 [0x44,0x90bf8bb000003ff00000])),(BitVec.ofNat 152 (word80 [0xe05c022e0211702004,0x10be8ba39ce739ce739c]))),((BitVec.ofNat 152 (word80 [0x33a,0x528a034bffffc0000000])),(BitVec.ofNat 152 (word80 [0x600430042180400a,0x120a020a108421084210]))),(0x0,0x0)]
def g235C : List ColumnInfo := [(2,0,233,0,8),(64,0,171,0,8),(1,0,234,0,7),(8,0,227,0,7),(32,0,203,0,7),(128,0,107,0,7),(0,2,73,160,6),(0,64,162,9,6),(1,64,162,8,5),(3,0,232,0,5),(32,2,73,128,5),(128,2,73,32,5),(9,0,162,0,4),(9,64,162,0,4),(33,0,202,0,4),(40,0,195,0,4),(129,0,106,0,4),(136,0,99,0,4),(160,0,73,0,4),(160,2,73,0,4)]
def g235A : List (List Nat) := [[],[117],[48],[48,117],[80,97,115],[80,97,115,48],[112,97,83,48],[112,97,83]]
def g235D4 (j : Nat) := if j=0 then 0x10b598d937154d20 else 0
def g235D5 := limbs80 #[#[0x4c930483b2595324c120,0x48372dd5324c120dc975,0x6037154d20f495354930,0x54d20cb764dc5534827c,0x8bf855cf644823d61b71,0xdb271e03d25493254130,0x818500c20683bf4e3bb5,0x7229101c2]]
def g235H5 (j : Nat) := if j=0 then 0x5 else 0
def g235D6 := limbs80 #[#[0x3e89926088791434c110,0xf926498241bcd893044,0x83f8b9260884bd73d912,0x20fb2a698241fa549304,0x482fcbaa60906f9654c1,0xd20beee2a9a417edd530,0x4c27fbaac6904fd7654,0x8930df6c4a8261f64c95,0x89e381486816004fd75d,0xb096ea44aa28fe743496,0x4c30e0d130c4c342d466,0xf0993805e10a0d0c2434,0x8083a28343610d081f0,0xe280c28a0308103420a,0x701081c180400406c2c1,0x180020d044c3420]]
def g235H6 := limbs80 #[#[0x5,0x24200000000000000000,0x4180090d00,0xa1c0,0xd0800000000000c08,0x2a4001c8800000,0x1f08910000000000000,0xf11014000000000,0x64000000001721001710,0x191800]]
def g235D7 := limbs80 #[#[0xdd8910bd58910fc4c110,0x4c910afd9120ed50d10b,0x4130bf58d20fe4c120fd,0x930ff54d20bfd8930fe5,0x3692c5200ff58930ff54,0xece55faab25773156281,0x4470858a10702c78498b,0x61f0421898d0b0931234,0x8ec22920d146930b2e48,0xb0931878e48170e01a3,0x218505c38070d1480ec0,0x131a20a1092141430101,0xf1c84688447]]
def g235H7 := limbs80 #[#[0x8b506b0b00060b403060,0x680d48372200000078a3,0x70c00058800000000038,0xa8120200074e62ee07,0x30e96860a0009052c90,0x501000c00c67524c0400,0x3100007e8528000e49,0xc2f2090000002890,0x9c1203000a0882700,0x94790f]]
def g235D8 := limbs80 #[#[0xc6a8a807f4c3fa41f510,0x70a592180d1890230a14,0x3a58c40a180]]
def g235H8 := limbs80 #[#[0x172000000904002041,0x2a480012a00000696,0x103800d0600289c0400,0xc500000131e807880000,0xf0a00000000000002,0xb0c0000000000000000,0x1b9400000a6c0010580,0x18bac60,0x30c60364220000000,0x84cc26e61a500000]]
def g235D9 (j : Nat) := if j=0 then 0xa4188201bf else 0
def g235H9 := limbs80 #[#[0x26200000020c00000028,0xf8001c000172a,0x1e00000a0800002200,0x19400]]
def g235L : Nat → Packing
  | 4 => (1,5,5,0,0,0,0,g235D4)
  | 5 => (9,4,5,0,0,7,0,g235D5)
  | 6 => (17,3,5,0,0,9,0,g235D6)
  | 7 => (13,2,5,0,0,9,0,g235D7)
  | 8 => (3,1,5,0,0,7,0,g235D8)
  | 9 => (1,0,5,0,0,0,0,g235D9)
  | _ => emptyPacking
def g235I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g235H5
  | 6 => lookupWord 4 67 1 11 4 3 g235H6
  | 7 => lookupWord 9 59 4 12 5 3 g235H7
  | 8 => lookupWord 7 71 2 11 4 3 g235H8
  | 9 => lookupWord 2 29 3 9 2 3 g235H9
  | _ => fun _ => none
def g235 : Forest := ⟨235,9,fun i => g235Y[i]?.getD (0,0),g235C,g235A,g235L,g235I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P4_0 : block g235 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B4 : block g235 4 0 1=true := g235P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P5_0 : block g235 5 0 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B5 : block g235 5 0 9=true := g235P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_0 : block g235 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_1 : block g235 6 1 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_5 : block g235 6 5 12=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B6 : block g235 6 0 17=true := (@block_merge g235 6 0 1 16 g235P6_0 (@block_merge g235 6 1 4 12 g235P6_1 g235P6_5))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_0 : block g235 7 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_5 : block g235 7 5 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_10 : block g235 7 10 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B7 : block g235 7 0 13=true := (@block_merge g235 7 0 5 8 g235P7_0 (@block_merge g235 7 5 5 3 g235P7_5 g235P7_10))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P8_0 : block g235 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P8_1 : block g235 8 1 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B8 : block g235 8 0 3=true := (@block_merge g235 8 0 1 2 g235P8_0 g235P8_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P9_0 : block g235 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B9 : block g235 9 0 1=true := g235P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235T : checkedTables g235 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g235 0 0 0 = true)
  · exact (rfl : block g235 1 0 0 = true)
  · exact (rfl : block g235 2 0 0 = true)
  · exact (rfl : block g235 3 0 0 = true)
  · exact g235B4
  · exact g235B5
  · exact g235B6
  · exact g235B7
  · exact g235B8
  · exact g235B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235G : graphValid g235 (boundsBefore K231) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low235 : Lower true (varsX 235) (graphGoal 235) 10 := lower_forest (g:=g235) (i:=0) (hints:=83) (before_sound K231 V231) g235G g235T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K235 := extendKnown K231 10 [(235,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V235 : Known true K235 := extend_ok (m:=235) V231 low235 (by decide +kernel)
def g237Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ffe0fffffffff228,0x840f2a4003f000fc0fff])),(BitVec.ofNat 152 (word80 [0x28014200400040f008,0x30201041041041041]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfc0000ffe0ffe075d0,0xc562b48000003f000000])),(BitVec.ofNat 152 (word80 [0x311584428244827580,0xc542b4975d75d75d75d7]))),((BitVec.ofNat 152 (word80 [0xffffff0000ffff2586,0xb2d84280fc0fc003f03f])),(BitVec.ofNat 152 (word80 [0x400600030401000180,0xb2480002082082082082]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffff0000084d,0x6956a9bf00000003ffc0])),(BitVec.ofNat 152 (word80 [0x805800140016040844,0x4814a88c30c30c30c30c]))),((BitVec.ofNat 152 (word80 [0x1171,0x18b1dc40000ffffc0000])),(BitVec.ofNat 152 (word80 [0x26008980898080071,0x8b04868a28a28a28a28]))),((BitVec.ofNat 152 (word80 [0xce93,0x4f80057ffff000000000])),(BitVec.ofNat 152 (word80 [0x38010e010e0100613,0x5800570c30c30c30c30]))),(0x0,0x0)]
def g237C : List ColumnInfo := [(0,4,169,64,8),(4,0,233,0,8),(1,0,236,0,7),(8,0,229,0,7),(32,0,205,0,7),(64,4,169,0,7),(128,0,109,0,7),(160,0,77,0,5),(33,0,204,0,4),(40,0,197,0,4),(129,0,108,0,4),(136,0,101,0,4)]
def g237A : List (List Nat) := [[],[117],[48],[48,117]]
def g237D5 := limbs80 #[#[0x4c930483b2595324c120,0x483725d5324c120ecb65,0x54d524c120dcb754c930,0x54d20e596554d30483d2,0xc5f731d56348237e0d76,0x4c9504c3d25493254130,0xc039654f6254130b5985,0x800549d2213c5c80d0c0,0x20210080060]]
def g237D6 := limbs80 #[#[0x23fbaac6907c9324c120,0xfd2a498241d654d504c,0x83edb1a60907d9534c12,0x20df6ca98241be595304,0x482fdbaa60905f9754c1,0xd209faeca9a41b758d53,0x34836fb1ac6904fe7654,0x8d20cf8eab1a415fdd56,0x634827fbaac69067f755,0x54130fb264a82613f5d7,0x5324c36eb2a64986fb62,0x358930ebaa6a9261b7d9,0x4f624c2bfbaac4985df7,0x72595309faebb1261b75,0xe3d148027eb96ca984ff,0x980b353265187f391b0b,0xcd65f228e43e12ee70b1,0xcae230575b7d8aab489d,0xd4389c7805c4223eb085,0x8350108082040100f105,0xc003500800c00c0e3041,0x800360400c0818b8f00,0x100302000044034c106,0x1983c]]
def g237H6 := limbs80 #[#[0xd1000d4bb5a58008,0x2080,0x200000,0x24000038300000000000,0x2,0x8c0000000c6800000000,0xd,0xb88000,0x0,0x1a900000000000,0x5400d140040787000000,0x30600202728006]]
def g237D7 := limbs80 #[#[0xfd8d20bf58d20fe4c120,0xd8930f74c930fe54130b,0x9530bf59530f754d30bf,0xd20ff58d20ff54d20bfd,0x30ff58930ff54930ffd8,0x378b42105a0a800ff595,0x811f27399e5d150480fc,0x68e2d472310b55231a22,0x5a41d4c768a3d4624850,0x42481354e218a2310b5,0x11f51c8c758871464f52,0x887196c73d4814a2220f,0x852485a2c70507503860,0x324859310b2020d4c708,0x2881c]]
def g237H7 := limbs80 #[#[0xf403340000141050e2c1,0x4aa2b8a70de2eb271724,0xc860500159cda4877136,0x311b2600015000391b9b,0x358cc535e3b8cc8e,0x4926238e0000024680,0x2540058491854e810000,0x28a18f54c46e4ce1a001,0x36aa00000496002e2]]
def g237D8 := limbs80 #[#[0x469a9007f54ffa61fd20,0x38d145a6415478da8315,0x49c655]]
def g237H8 := limbs80 #[#[0x1f1b00349120cd04da40,0xd81aa32842820679800a,0x807420010384b509,0xc0005380019c00000000,0x31600180b4400000005,0x245c284b0]]
def g237D9 (j : Nat) := if j=0 then 0x1643251bf else 0
def g237H9 := limbs80 #[#[0xc99d00000000f2000000,0xa09591]]
def g237L : Nat → Packing
  | 5 => (11,4,4,0,0,7,0,g237D5)
  | 6 => (30,3,4,0,0,9,0,g237D6)
  | 7 => (15,2,4,0,0,10,0,g237D7)
  | 8 => (3,1,4,0,0,7,0,g237D8)
  | 9 => (1,0,4,0,0,0,0,g237D9)
  | _ => emptyPacking
def g237I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 4 97 1 10 4 2 g237H6
  | 7 => lookupWord 11 59 6 11 5 2 g237H7
  | 8 => lookupWord 6 41 4 10 4 2 g237H8
  | 9 => lookupWord 1 23 0 8 2 2 g237H9
  | _ => fun _ => none
def g237 : Forest := ⟨237,9,fun i => g237Y[i]?.getD (0,0),g237C,g237A,g237L,g237I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P5_0 : block g237 5 0 11=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B5 : block g237 5 0 11=true := g237P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_0 : block g237 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_3 : block g237 6 3 27=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B6 : block g237 6 0 30=true := (@block_merge g237 6 0 3 27 g237P6_0 g237P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_0 : block g237 7 0 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_9 : block g237 7 9 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B7 : block g237 7 0 15=true := (@block_merge g237 7 0 9 6 g237P7_0 g237P7_9)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P8_0 : block g237 8 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B8 : block g237 8 0 3=true := g237P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P9_0 : block g237 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B9 : block g237 9 0 1=true := g237P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237T : checkedTables g237 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g237 0 0 0 = true)
  · exact (rfl : block g237 1 0 0 = true)
  · exact (rfl : block g237 2 0 0 = true)
  · exact (rfl : block g237 3 0 0 = true)
  · exact (rfl : block g237 4 0 0 = true)
  · exact g237B5
  · exact g237B6
  · exact g237B7
  · exact g237B8
  · exact g237B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237G : graphValid g237 (boundsBefore K235) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low237 : Lower true (varsX 237) (graphGoal 237) 10 := lower_forest (g:=g237) (i:=0) (hints:=1539) (before_sound K235 V235) g237G g237T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K237 := extendKnown K235 10 [(237,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V237 : Known true K237 := extend_ok (m:=237) V235 low237 (by decide +kernel)
def g243Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ff83ff0fffc1f06,0xe2491d8000f83e007c1f])),(BitVec.ofNat 152 (word80 [0x28050802200084000,0xa0491484210842108421]))),((BitVec.ofNat 152 (word80 [0xffc0003fff0fffe02a,0x2ca726801f00000f83e0])),(BitVec.ofNat 152 (word80 [0x23046104402110022a,0x24832494a5294a5294a5]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffc0000fffffb0,0x1003d003e007c1f003ff])),(BitVec.ofNat 152 (word80 [0x40080008000200000,0x8421084210842]))),((BitVec.ofNat 152 (word80 [0xfffffffffff000005d,0x1b7020fc000001fffc00])),(BitVec.ofNat 152 (word80 [0x480900090002408415,0x1a300021084210842108]))),((BitVec.ofNat 152 (word80 [0xe,0xf536c8000007fe000000])),(BitVec.ofNat 152 (word80 [0x702e022e044b81080e,0x5536c8739ce739ce739c]))),((BitVec.ofNat 152 (word80 [0xc1,0x459c477ffff800000000])),(BitVec.ofNat 152 (word80 [0x80300430088c0210c0,0x41044342108421084210]))),(0x0,0x0)]
def g243C : List ColumnInfo := [(1,0,242,0,8),(2,0,241,0,8),(64,0,179,0,8),(16,0,227,0,7),(32,0,211,0,7),(128,0,115,0,7),(16,64,162,1,5),(96,0,147,0,5),(160,0,83,0,5),(48,0,195,0,4),(144,0,99,0,4)]
def g243A : List (List Nat) := [[],[117]]
def g243D5 (j : Nat) := if j=0 then 0x2e5e056550d32 else 0
def g243D6 := limbs80 #[#[0xba6a9aa49978d4354932,0x29eee2b2a6567dd5434c,0xcafbb8aca9979d6550d3,0x471eda965201bddc5654,0xdc780812a89e21b80b53,0x2ab93970138b50fc040,0x1040622]]
def g243H6 (j : Nat) := if j=0 then 0xb else 0
def g243D7 := limbs80 #[#[0xfd9543af59543e750d32,0x55132f754d32fb54932a,0x9532bfd9532bf59532ef,0xa3a98c9c331205400ff5,0xc980c21226b8e030d388,0x21e58e0ac8462ae0388a,0x8ab80c29318d8e040c51,0xe58e048a513911862349,0x144a2408a]]
def g243H7 := limbs80 #[#[0x44100008200508553008,0x9618a]]
def g243D8 := limbs80 #[#[0x7a4a407f54ffa65bd43,0x19351925180e7154c48c,0x8394608]]
def g243H8 := limbs80 #[#[0x30200d000000e400001,0x2e8220061400c81a8,0x41800000000000000,0x49f460]]
def g243D9 (j : Nat) := if j=0 then 0x5431201bf else 0
def g243H9 (j : Nat) := if j=0 then 0x1c400a3a03c3c else 0
def g243L : Nat → Packing
  | 5 => (1,4,4,0,0,0,0,g243D5)
  | 6 => (7,3,4,0,0,8,0,g243D6)
  | 7 => (9,2,4,0,0,9,0,g243D7)
  | 8 => (3,1,4,0,0,7,0,g243D8)
  | 9 => (1,0,4,0,0,0,0,g243D9)
  | _ => emptyPacking
def g243I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g243H6
  | 7 => lookupWord 2 13 2 8 3 1 g243H7
  | 8 => lookupWord 2 29 1 9 4 1 g243H8
  | 9 => lookupWord 1 7 0 7 2 1 g243H9
  | _ => fun _ => none
def g243 : Forest := ⟨243,9,fun i => g243Y[i]?.getD (0,0),g243C,g243A,g243L,g243I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P5_0 : block g243 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B5 : block g243 5 0 1=true := g243P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_0 : block g243 6 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_4 : block g243 6 4 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B6 : block g243 6 0 7=true := (@block_merge g243 6 0 4 3 g243P6_0 g243P6_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_0 : block g243 7 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_3 : block g243 7 3 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_8 : block g243 7 8 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B7 : block g243 7 0 9=true := (@block_merge g243 7 0 3 6 g243P7_0 (@block_merge g243 7 3 5 1 g243P7_3 g243P7_8))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P8_0 : block g243 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P8_1 : block g243 8 1 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B8 : block g243 8 0 3=true := (@block_merge g243 8 0 1 2 g243P8_0 g243P8_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P9_0 : block g243 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B9 : block g243 9 0 1=true := g243P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243T : checkedTables g243 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g243 0 0 0 = true)
  · exact (rfl : block g243 1 0 0 = true)
  · exact (rfl : block g243 2 0 0 = true)
  · exact (rfl : block g243 3 0 0 = true)
  · exact (rfl : block g243 4 0 0 = true)
  · exact g243B5
  · exact g243B6
  · exact g243B7
  · exact g243B8
  · exact g243B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243G : graphValid g243 (boundsBefore K237) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low243 : Lower true (varsX 243) (graphGoal 243) 10 := lower_forest (g:=g243) (i:=0) (hints:=68) (before_sound K237 V237) g243G g243T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K243 := extendKnown K237 10 [(243,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V243 : Known true K243 := extend_ok (m:=243) V237 low243 (by decide +kernel)
def g245Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7ff83fffffe0f9123,0xb08fa000fc003f03f03f])),(BitVec.ofNat 152 (word80 [0x500508020004201020,0x300e2041041041041041]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf80003ff0ffff05e9a,0x8be4000000fc0000fc0])),(BitVec.ofNat 152 (word80 [0x622611042448015c1a,0x89e4555555555555555]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffc000fffffd004,0xd50303f03f000fc0fff])),(BitVec.ofNat 152 (word80 [0x800800080010000000,0x82082082082082]))),((BitVec.ofNat 152 (word80 [0xfffffffff000002956,0xda225fc0000000fff000])),(BitVec.ofNat 152 (word80 [0xb000500160420946,0xc820530c30c30c30c30c]))),((BitVec.ofNat 152 (word80 [0xfad,0x4669000003ffff000000])),(BitVec.ofNat 152 (word80 [0x4c022604980840385,0x46610a28a28a28a28a28]))),((BitVec.ofNat 152 (word80 [0x6651,0x63c4cffffc0000000000])),(BitVec.ofNat 152 (word80 [0x70043808e01086611,0x3c08c30c30c30c30c30]))),(0x0,0x0)]
def g245C : List ColumnInfo := [(1,0,244,0,8),(4,0,241,0,8),(64,0,181,0,8),(16,0,229,0,7),(32,0,213,0,7),(128,0,117,0,7),(160,0,85,0,5),(48,0,197,0,4),(144,0,101,0,4)]
def g245A : List (List Nat) := [[],[117]]
def g245D6 := limbs80 #[#[0xe5c61a4e0374d5354932,0x5]]
def g245D7 := limbs80 #[#[0xf59532f754d32fb54932,0x3600ff59532bfd9532b,0x1881c3cb1570908ae8a6,0x481c6cb1c061f2c63c06,0x81c60d5c72c071]]
def g245H7 (j : Nat) := if j=0 then 0x6 else 0
def g245D8 := limbs80 #[#[0xa41ca301e903faa7fd32,0x10728c0c31e]]
def g245H8 := limbs80 #[#[0xf90000000034506300d1,0x12]]
def g245D9 (j : Nat) := if j=0 then 0x5432101bf else 0
def g245H9 (j : Nat) := if j=0 then 0xe40038180 else 0
def g245L : Nat → Packing
  | 6 => (1,3,4,0,0,0,0,g245D6)
  | 7 => (5,2,4,0,0,8,0,g245D7)
  | 8 => (2,1,4,0,0,6,0,g245D8)
  | 9 => (1,0,4,0,0,0,0,g245D9)
  | _ => emptyPacking
def g245I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 4 0 0 g245H7
  | 8 => lookupWord 1 11 0 8 3 1 g245H8
  | 9 => lookupWord 1 11 0 6 1 1 g245H9
  | _ => fun _ => none
def g245 : Forest := ⟨245,9,fun i => g245Y[i]?.getD (0,0),g245C,g245A,g245L,g245I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P6_0 : block g245 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g245B6 : block g245 6 0 1=true := g245P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P7_0 : block g245 7 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P7_4 : block g245 7 4 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g245B7 : block g245 7 0 5=true := (@block_merge g245 7 0 4 1 g245P7_0 g245P7_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P8_0 : block g245 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g245B8 : block g245 8 0 2=true := g245P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P9_0 : block g245 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g245B9 : block g245 9 0 1=true := g245P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245T : checkedTables g245 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g245 0 0 0 = true)
  · exact (rfl : block g245 1 0 0 = true)
  · exact (rfl : block g245 2 0 0 = true)
  · exact (rfl : block g245 3 0 0 = true)
  · exact (rfl : block g245 4 0 0 = true)
  · exact (rfl : block g245 5 0 0 = true)
  · exact g245B6
  · exact g245B7
  · exact g245B8
  · exact g245B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245G : graphValid g245 (boundsBefore K243) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low245 : Lower true (varsX 245) (graphGoal 245) 10 := lower_forest (g:=g245) (i:=0) (hints:=1028) (before_sound K243 V243) g245G g245T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K245 := extendKnown K243 10 [(245,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V245 : Known true K245 := extend_ok (m:=245) V243 low245 (by decide +kernel)
def g246Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffc1ffffffc1f361ab,0x414e8001fc00001fc07f])),(BitVec.ofNat 152 (word80 [0x428410802084022183,0x14a8912244891224489]))),((BitVec.ofNat 152 (word80 [0x1ffc3fffe02baf0,0xf31800000007f0003f80])),(BitVec.ofNat 152 (word80 [0x130881090900229aa0,0xf118254a952a54a952a5]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffe0003fffffa0800,0x94a380fe03f80fe03fff])),(BitVec.ofNat 152 (word80 [0x40002000200000000,0x204081020408102]))),((BitVec.ofNat 152 (word80 [0xfffffffc000005156d,0xa9917f0000000fffc000])),(BitVec.ofNat 152 (word80 [0x980024004c08450468,0xa091142850a142850a14]))),((BitVec.ofNat 152 (word80 [0x1e7d0,0xe73000003fff0000000])),(BitVec.ofNat 152 (word80 [0xe01138127010816550,0xe6358b162c58b162c58]))),((BitVec.ofNat 152 (word80 [0xcdc16,0x686c7ffffc0000000000])),(BitVec.ofNat 152 (word80 [0x21c023802108d814,0x482460c183060c183060]))),(0x0,0x0)]
def g246C : List ColumnInfo := [(2,0,244,0,8),(4,0,242,0,8),(32,0,214,0,8),(64,0,182,0,8),(128,0,118,0,8),(68,0,178,0,7),(0,4,162,80,6),(0,64,162,20,6),(16,0,230,0,6),(6,0,240,0,5),(16,4,162,64,5),(16,64,162,4,5),(34,0,212,0,5),(36,0,210,0,5),(64,4,162,16,5),(130,0,116,0,5),(132,0,114,0,5),(160,0,86,0,5),(20,0,162,0,4),(20,64,162,0,4),(162,0,84,0,4)]
def g246A : List (List Nat) := [[],[117],[98],[98,117],[81],[81,113],[81,98],[81,98,113],[113,81],[113],[113,98,81],[113,98]]
def g246D4 := limbs80 #[#[0x20c92e1593d953248110,0x30c52e17935d532c81]]
def g246D5 := limbs80 #[#[0x9022194b7560e524c120,0x654c920442d9327b2a64,0xa5c82a6a92648869ae17,0x122185f7560f654c910b,0x54c624431b2e7c02a63,0xccbf00a98c48862e5d38,0x2214db90615731891087,0x54e624430f2ebc02a731,0xbaaa6996409043e65f80,0x415cb935d532c8120ea4,0x85304832d70abaa65902,0x2264b0a60906e2e11324,0x136995209714c120dc5c,0x930483c96caa92649824,0xaa499260907525d5524c,0xd4b75949324c120ae5cb,0x304834b70bb2a6498241,0xca9926090792d95654c9,0x4b75d95324c120e65cba,0x4836970bb2a6498241d,0x6a926090572a5b754c93,0xb65d8d524c120ba54b2a,0x4832b6eac1ca498241e4,0xa9a6090752dd58394930,0x85d97634c120d2d432ca,0x8307f0bba2c690a41a59,0x82649060fe177458d614,0xd95654c920cb4c2eebb,0x28f720baecb19241a6b8,0xc649069ae03655963248,0xe017654d20b35c82ebb2,0xbb0ac1ceca9a4187b85],#[0xc690716dd763dc163483,0x117158d20c1e3af08b8a,0xf7003aae2b1a4183f75e,0x69041fa60755c5634830,0x77558d20d2dc1f01baac,0x6e9c02a6b0e4143f9460,0x9071659563dc153c8317,0x2154130c2fc2f06bb2a7,0xca9e42a8261b1b8454d,0x849de5586c85214c34b3,0x6c853083fcab0fb16429,0xa392c4b0a6187885e017,0x656e0f80dd5624c28db2,0x541203c0c0240600c00,0xc82a09c240841e06c18,0x18c5b1384b10c400f43a,0x2007d1e8771d0711b86b,0x2889f270992589324088,0x2fcbc2e4b62ccb02a0a5,0x3e8f23a8dd368d233ccc,0x103400fd,0x14003400200000000,0x440c440a454004060008,0x783110200000000006,0x510200000000000,0x101a002001322c81000,0x80100001d18202034150,0x611]]
def g246H5 (j : Nat) := if j=0 then 0x29007051000000 else 0
set_option maxRecDepth 16000 in
def g246D6 := limbs80 #[#[0x4c930483b2595324c120,0x483725d5324c120ecb65,0x54d524c120dcb754c930,0x4c120bc98394930483d2,0xe596554d304835add652,0x1d5634823ee017654d20,0x4c31e5977054f20c7b70,0x94972d953087f855db21,0x48110fc9534c9204431b,0xeeb654c920443f2dcd32,0x4c920442fa6153248110,0x443ba2193248110beb85,0xa1f6348110af985d8d20,0x48510b7b855cd20442be,0xcf775d8d21442fce0153,0xdcd21442bd6176348510,0x443d354d524c9109f585,0x60f654c910bdb8054d32,0x4c910c7f75d9532442b7,0x8fe87d95324423f61f65,0x9d9324427ee01754c910,0x442bee015318910aed82,0x5d15318910cdd7354c62,0x189108fd8754c624432f,0xcdd855cc624423fe1573,0x54d6244337e157318910,0x4423fa1d5358910cbf74,0xe0153989108fd85dcd62,0x98910cdd7354e62442be,0x8ff855ce624423f61d53,0x5cb634427e60b7054d10,0x4823fe0975d8d108ff85],#[0xd8d32c8120fc9534cb20,0xc8120de9754cb20483f2,0xbeb854cb20482fa61532,0x54f20483765cd53c8120,0x482dee1563c81209f987,0xe1573c8120dd973d8f20,0x4c120fc932485304827e,0xfc932c8530482eee1121,0x58530482f660f214c120,0x482f6e0d614c120fc932,0x4cb614c120bbb8458530,0x4c120fc9325c530483f2,0xbeb825c530482fa20971,0x4c930483f2549324c120,0x483f29c9324c120fca52,0xd95324c120ed9654c930,0x4c120dd9754c930483b6,0xfc9654c93048376dd532,0x54930483f2d95324c120,0x4839ed95524c120f5953,0xd8d524c1209fb8754930,0x4c120fc98354930483f2,0xdeb8754930483dad9552,0x94930482f660e524c120,0x483f2d8e524c120d7b75,0x60e724c120fc98394930,0x4c120f596554d30482f6,0xed965d8d30482f6a1953,0xd8d30483b6d97634c120,0x482f6e0d654c120bd985,0xe0d654c120e7b6559530,0x4c120cfb8759530483b6],#[0xedb83d95304835edd765,0x4c9214827ea1b754c120,0x4832fdd16348520daf74,0xdd36348520a7f8558d21,0xc8520a7f8558f214832f,0xcdd73d8f214823fe1d63,0x4c9614827ee0173c8520,0x4836bdd13258520dcf73,0xdd16358520cdf7358d61,0x58520a7f8558d614832f,0xa7f8558f614832fdd363,0x54f61483375cf63d8520,0x4823f61d53d8520cdd73,0xd8f704c9208ff855cf61,0x4c920de952dc132483b6,0x9f985dc1324837a94b70,0xd9532482b7e0d654c920,0x483f2d8f704c920c7f75,0x5d7704c920fcb83dc132,0x4c920deb75dc1324837a,0xbcf8359532482fa61770,0x595324839bd95654c920,0x4835bdd7654c920ecf83,0xe0d658c920ecf83d9532,0x8c920c7d75d9632482b7,0xbcf83596324827ee0175,0x596324839bd95658c920,0x4835b5d7658c920ecf83,0xe01758c920e6d75d9632,0x54d20deb805d632482fa,0x9df835d9534839759563,0x9d9534833ee017654d20],#[0x483b6d8f7058d20cdd83,0xdd77058d20d7875dc163,0x58d20e5c75d8d634835e,0xadd85d8d6348397dd763,0x1d563482b7e0d6558d20,0x4835ee037558d20d5f73,0xe117158d20aef825c563,0x58d20c7c755c563482af,0xa7f855c5634831fdd571,0xdc5634831f1d77158d20,0x4829fa1c7558d20c7f75,0x6077558d20e7b80dd563,0x58d20c7f81dd5634831f,0xadd83d97634831f60b75,0x54d61c82afe1171d8d20,0xc832fdd15358720afb80,0x58f7054f209f982dc153,0x54f20e5d6558d53c8376,0xcfb805d953c8397e1563,0x59563c8337e0d7654f20,0x4c2bee017558f20adf83,0xe112154130f595348550,0x54130f5953c85504c2ee,0xaf986c85504c2f660f21,0xc85214c2fc6032148530,0x4c32fdd36248530af586,0xd977448530cbd65dd121,0x48530c7f75d95214c32f,0x9fb805d9214c23f61b75,0x5d9214c26fe117648530,0x4c27e603764853097f85,0xe0d70c8530dd9735c321],#[0xc8530cf9655c3214c376,0x9fb855c3214c33ed9570,0x597214c23f61f62c8530,0x4c23f61f65c85308fd87,0xe1576c85308ff865d721,0xc85309fb805db214c29f,0xcfb805db214c25fe1576,0x5db214c31f21576c8530,0x4c23fe1576c8530c7f85,0x60376c85308fd879db21,0x58530cec72589614c27e,0x9bd841c9614c29fe1562,0xdc1624c25f6147258530,0x4c35edd77058930ddb73,0xe037558930c7f7598962,0x98930c7f86dd5624c35e,0x9bf845c6624c3765cd70,0x5c3214863fe1573d8121,0xc86bee0163583219f783,0x6177358321a7f855cd60,0x2dc2a01f81080840023f,0x584f84bc4804684083a8,0x869c68464860c5d05945,0x81c7e07c87447086f06d,0xc09609248e88ac894834,0xb94b34ad4a74a389fc9,0xd38d20ce4ca8c6cc30bd,0x28decdd4dbcda4d8cd74,0x8f6cf30ed0eb8e7ce64e,0x1c51410e10a4ffcfe4fa,0x8944d4113693092cd26d,0x56a56455e55a95494e94],#[0x98d9519158d985578970,0x9db61b25ac5a41a059c9,0x5d95d35cf9c99c39bfdb,0xf81f69f2def1eb5e55df,0xba07e06604e035ff9fbd,0xa2221e61aa16e1320f60,0x33631e3062ca28e25223,0xb647a43e3de3a238a372,0x25d659a55e52250a4f24,0x70e6d26ba67e64262a61,0x8e8768167da79e78674a,0x29d299695a91e9068ca8,0xbbeba6b6aae6aaaa6ea3,0xaad26ceacd2cbac5abfa,0xaecaeb2e9ae5ee22e0ad,0xb707b063026fa2f66f2,0x332f72bb1ef18f10b0f3,0xb42f3f33db3c33ab36f3,0x5f75bb55b51f4e34a746,0x537176ff6e768764b633,0xb87383781f7e37a776b7,0x9cf96f93391b9038c788,0x73b37afbabfa5fa47a0b,0xdc9220fc1bc03bc7b8bb,0x18a753020608b9218183,0xa14054ea60639040883c,0x8207e8824602c1f64050,0x1f1e842d1036404007c8,0x2000010502c6058c0850,0x40d1805001f041000050,0x8181040200898c101a30,0x1000201040200080c0],#[0xd8800158a8015000812,0xd881b102e405c8c009c8,0x4020000000010101c80,0x4a208080000206001,0x84a4d63400806001c002,0x2258400820e4c800b040,0x82d10209010412b18881,0x8209064d610682444049,0x81400280020291600204,0x1c81390101401c810081,0x10e491400507b9244182,0x7040c30108833001830,0xac8080c1008201400200,0x2c00408041e083f44120,0x810888820880020a028,0x103e44103d44103c0410,0x400103800744083d44,0x410002000068c1a2034,0x3460d901030340042408,0x80080000010202000400,0x1a002a2a0040004000,0xa881910380040008009,0x2140400102000400280,0x9044102010102002010a,0xd001d10202881000200,0xa8819202a405490c0a80,0x8c2b1820000146590c81,0xc81b001000025842085,0x26404071b8424659,0x80e8008501b1500200,0x300000f0010008088b8,0x1882400b84c105634120],#[0xd183a30408083c10883c,0x78008001030206040000,0xc080812110020003c00,0x3800800010021708100,0x1000808000078008001,0x208e005c00400000081,0x10a036461040430120,0x390100000f0c1038009]]
def g246H6 := limbs80 #[#[0x781252f8903914350803,0x2193855c080bc412002,0x5cae00000014ba800,0x12f42e0a06037e141028,0x1f25a000784921b80706,0x60678056a500007cb671,0x38e01303c20b803a000,0xf200dc06a1c80000004,0x620bd06e86701b604b0,0xc8810194160235c08800,0x8c0000e1780016180000,0xf301e00068634034aba2,0x689800c9852811282412,0x8a76ae000110590eae07,0x10102843888e,0x1c0d50c0000405c00000,0x422d809815f85a000783,0xa8e826602b011c9c0001,0xa822e000004c0001a46a,0x884f411d82c801f874c0,0x8680002896c00281652f,0x1a850000000783e0007,0xaa1b686a905000000000,0x1a32000621]]
set_option maxRecDepth 16000 in
def g246D7 := limbs80 #[#[0x25eba0c4884dd7318910,0xf9264982412fdd16244,0xc25fba2c39047f7558d2,0x3097ae9b0a61d654d504,0x4423eba8c4984f571189,0x510df6c690221fa4c920,0x1442fbb9a42886f76348,0x89109fae631221bdd953,0x534427eb9cc4884ff735,0xd8d109feeab1a217edc1,0xb204827ebaec6884fd72,0x24c120bf2e790241fa4c,0x4930483f4a9260907d93,0x634c120fb2a698241fa9,0xd95304837cb2a60907db,0xb754c120bf2ea98241be,0xfdd161482dfba242905f,0xfb704c9209fae7b0a416,0xbb59532483f5b8264905,0x6ed658c920ddeca99241,0x17b5d63248377b2c6490,0x4fd7654d20bdeeb1924,0x41b7d8d634827f3b2a69,0x9067c7558d20afeeab1a,0xa413fdd5634833fbaac6,0x7906ed658cb209faebb1,0x9e41b758d53c82fdb82a,0xc7904ff7558f209faeca,0x90a616fdd1214c27ebae,0x2c4984fd76c8530bf2e1,0x1312615fdd5624c2fdb8,0x96ca984fd7698930bf2e],#[0xe190a433f5cf604867eb,0xa9a40884ff7358321bea,0x6e690221fe5cd20443fc,0x6a9264887f55348510ff,0xfeca99221f754d32443f,0xffbaa64885fd754c910d,0xdfcec99221bf1d932442,0x37ea9ac4886fd5318910,0xdfaa7b1221bf54e6244,0x83fcb1e40907f953c812,0x20ff24298241fed8f204,0x483fcb0a60907fb214c1,0x120ff2e298241fed8530,0x483fd29260907f9524c,0xc120ff2ca98241fe9c93,0x21483f699242907fb654,0xc8520dfec690a41bf58d,0xf214837eb1e42907ed32,0x258520bfae790a41bfd8,0x8d614837eb1ac2907ed3,0x32d8520bfee6b0a41bfd,0xd8f614837eb1ec2907ed,0xd53d8520bfae7b0a41bf,0xb54932483fdb8264906f,0xfd654c920fdca499241f,0xfb595324837fb2a64906,0x6fd658c920fdeca99241,0x17f5d6324837fb2c6490,0x7ef658c920fdacb1924,0x41f758d53483f6bac649,0x905fe7654d20bfaeca9a,0xa41f7d8d63483fdb82c6],#[0x6906ff6558d20dfacab1,0x1a41dfdd563483be3aac,0xc6906fd7158d20bfeeab,0xb1a41bf5d5634837fb8a,0xec6907fb70d8d20dfeea,0x3b1a417f5d7634837fb2,0xaec6906ff71d8d20dfae,0xa6b0e41bfdd7634837eb,0xbb2a7907dd6354f20dfa,0xeeab1e41bf59563c82fe,0xfbaac7906fd7558f20bf,0xf642a8261fe485504c37,0xfab0a42987f72148530f,0xf7ee890a61bfd89214c3,0x37fb2a42986fd6548530,0xbfaec90a617fdd5214c,0xc3fcb8642985ff764853,0x30dfacb90a61bfd8b214,0x4c2febae42986ff65c85,0x530bfaed90a61bf5db21,0x14c2ffbb642986fe76c8,0x8530bf8e4b0a61bf5896,0x624c3fdb82c4985ff725,0x58930dfcc4b12617fdc5,0x6624c3fcb84c49877f75,0x358321dfac6b06437f5c,0xcd60c877eb9ac190dff7,0x818008a02e0098001bfd,0xa0da06382d014208e03b,0xd852026211e08784001d,0xa21be0d386502fa16e0a,0x1f88d045a21210187903],#[0x5822a214589d04c224e1,0x1978ca062a3021778b60,0x76a3a61c18db06ba342,0xa22f91308524061f58f4,0x50a024e226592a090a46,0x9a2bf9580a9a53629594,0x850c025ea2e996f0b525,0x6723319960c8a63a3179,0x9b70d9a6ba3519a10cfa,0xa73a3939c50e026fa375,0x59e50f0a77e3b59d50e8,0x27f23f59f80fa27be3d,0x39a1910aa842415a0510,0x19a8ba455a27111a87e4,0x493a4812128fa473a371,0x12da9664aba521282932,0x64dda6a133a9964c5a5d,0x8141aa064fda7a13aa9c,0x6a531a961492a3a515a8,0xb21572aa654daa214e2a,0xb26587ac015daade569a,0xae51702b6a5abad2166a,0xabda5e5aef1762bae5cf,0x3b0c1822bfe5fbafd17c,0x2ac8263db1b18bac4e62,0x930023144cb6655b2819,0xf00285e4e2c00708451b,0x5220b0a80e5141b93881,0xe207c00a15928b039630,0x7c2c00a10080394504e4,0xbc2c00a101b0b002c40,0x3c5620a0910018b14284],#[0x6142840006130c261428,0x28462e4c008c514082,0x314c430408c562139317,0x1428244a2c0c5640a150,0xd882846408c5a2091413,0x28307800b620a10302,0x28860b0a140c2f938f86,0xe0030214042c3e30299,0x81412023192884640fa2,0xa14209c999030527260,0xf938a8700287c4c2c00b,0x288562c0040aa5149d8,0x28840b0a40a2109c9b11,0x105011164c0a2103d930,0x2e8829930060cc064a2,0x1c180c045050b0a140c3,0x30807060301a4a2c020,0x68c64e3e1a2c01832930,0xc08c641a8b02338f8590,0xc1b8e8b8701908e3a2e1,0xf07060301c064a220301,0x29064031082f02882840,0x7060301c020c42c882b0,0x19900c070288811a4a20,0x7007a2c00b640a14201c,0x8a5c2103a201f130a8,0x5401408330b00129454,0x70b0a4014138f0b87023,0xca41b0b001c180c0450,0x851012804c307060301,0xa14218b931680508066,0x3191891b04562813109],#[0x8d8a0024186c18046091,0x20a091091182220a084e,0x42824409060c18242240,0x220d8a0601004470a070,0x98900444118362410614,0x620d8821443620a090c1,0x8426638212120010c64,0xa882120963a21024889a,0x31902202885090d0c0c9,0xf64a20c3010f64a20810,0x400a1310302192028850,0x2a30d060d128c1a844a3,0x92210250888344050020,0xa1144c2a8c8824508420,0x20c341a8c8440664a322,0x430d640a850028312096,0x19884430a62a10c188a8,0xd10928b00408a2400c,0x1164a2c0103e8828208c,0x108648040a2143d92883,0x3140430219030c640850,0x404501640c080c302190,0x10ca2084422928b0051,0xa20844930288424a2083,0x40cc0a2641230928838c,0x41050106610819918d84,0x24c0a20c890020ca2c06,0x198420663610c3d92883,0x48362401206159016404,0x9288411c0080b029020,0x6409019020864a20f002,0x3840f0c8212118e08308],#[0x430da3c0090c141a8f00,0x4818323c01206128c1a8,0x9130048524a31206128c,0xc1b002122423c010301,0x189030306140800006c2,0x624c00c3110244c00c0c,0x90c1d93001a844c00400,0x34282450d082423c00,0x4c00c0f0019843140687,0xf00198440c049302303a,0x82646208018822220088,0x198]]
set_option maxRecDepth 16000 in
def g246H7 := limbs80 #[#[0x6201f05000008010401,0xd00220c00020c010205,0x1500250f2a0400000600,0x5003713070900031406,0x200051c0118044d00a7,0x9166c12112602110200,0x33010506000e17070903,0x45011401000003720300,0x151b172b0a5701110811,0x151234100007244c1b05,0x67124c24090020150516,0xb600000000d0c0000b71,0x1e00001162e82c007c30,0xb0ebb5bfe0,0x1700008051f4abe08a00,0xb0bd00007013508ed0,0x617d0000f1b9807b00,0x61a0b180310000000000,0x630000b07e0000788480,0xe02600000000c0,0x4dc04dc043e0a4000000,0x22d5550000604511,0xc00001158840e000000,0x6579590000615d906990,0xe10f381612410000c5,0x42bb2559a0e6000000,0x2ad4470000d437a09500,0xe648ab0e0d900c486f0,0x9ee01a00be0000209356,0xcd6473413ed08ba059f0,0xad0000287e6107b13384,0xbd50bca4c7b07d9172b0],#[0x33d0c380a7044c44bc52,0x1b80a160190000308260,0xdee2a6311bd165000068,0x9c1c030845a200076d2,0x5210420000649d000084,0x1b0000a07065c62035a0,0x4cb004000000000000e0,0x464400a9b0d550,0xa8c0dd00000000402800,0xb5480000000002,0xa0a6f4e4106d504e00,0x60f0a20000710df07200,0xd1b424d5401690,0x91996540d24105200d00,0x4130370190f002815f40,0xea80b8602ff088c148b4,0x65101225d3d0aa80cd40,0x3655064102e61120a080,0x646444a90600e460c594,0x8c3498809914119470c0,0x32d006000000000000d0,0x89604780e330cc407100,0xcee990c4eab26df1a021,0x2db57d219102acf4be14,0xb91079340160c4b45010,0xf05bc0ecb552897d00,0x3a0000802c7138d18c00,0x6ca45c805051be000090,0x3b205ed0c8d87d505f51,0x20bb72ad45be80,0x98000094460000188500,0xe9aa1a509222450277e8],#[0xcd506881170000c485f0,0x23b021707f0000a143d8,0x301888123a0582077d0,0x20c0dc603f8001309680,0xb0240000d05cf0c198,0xd4f06a0000255352a900,0xb0615ab176a075d18060,0xe280b7a26bb153302990,0x5350c7d819501c20b3e4,0x8f50c6a4a0116a208d79,0x9e209f40d9409bb02e00,0x1510cea610e039600ab4,0xc931af5215b0db000050,0xf041f23db00fd05670,0xd0018f2046f44b000000,0xe990d300002564909a50,0x980000f089c01480e8d1,0x1140554053111e00bab0,0x97706e61b870af4641f0,0x6b023fe0308062301f00,0x33104b8484605a000080,0x9057b1973164a8b778,0x6011638483404fa17e00,0x80a957195b0025204921,0x7179d4100000040880,0x87f4ca5074618b655600,0x95d0055244e0b2c43e01,0x86f48cda300000b80838,0xcf82a5102b401d555720,0x960277044647ed04a10,0xc2e1c17174fa0d203440,0x1a203640ac7958d4c010],#[0xd0000000011cf0000e8,0x6157605438,0x311cb0202894400000,0x35d0df00000000e0d800,0x8100000000888e0000b1,0x909d10b400003085a0,0x73a435647d60caa44f00,0xde30d1b27500002400a0,0x5d000004bf2048000000,0x409988212d21bf90,0x2c58b38199503e000000,0xa8308360e7f066115462,0xe495540947440406fa0,0x34d0d7e010b0874018e0,0xe20000f0a30000000034,0x10bfb03800009007a0,0x9c994b0000906c183000,0xe5848010d6d03d44d790,0x6992b1d0b50000906710,0x8015bc07ab15ef40721,0xcb3090847ff0da24dc80,0x7840a5a90580e160aea0,0x3c00001a1b747c00abd0,0xc0]]
def g246D8 := limbs80 #[#[0xd48510fe48110afd9121,0x58910bf18910fd4c510f,0x8d10bfd8910bf98910bf,0x120fec8120bfd8d10bf5,0x20fb4c920bfd8520fe4c,0xbfd8d20bf58d20fb8c9,0xbf58f20fb8cb20bf5872,0xfd8530fe54130bfd8f20,0x59530bfd8930bf18930b,0x8521bfd8121bfd9530bf,0x910bf58321efd9121fdc,0x20ff48520ff54d10ff4c,0xffd8520ff58520ffc85,0xff54d20ff8c920ff4c92,0xf54f20ffd8d20ff58d20,0xc8530ff48530ff58f20f,0x8930ff58930ff58530ff,0x9060037000ff58321ff9,0x18615d13410b0e20ab08,0xc828a2532312081d81af,0x3c53a337a34a3282f82,0x4eb4bb49946944041e3e,0x496125d45a457b54451b,0xf79a76371e6d96a96726,0x90d8dd8ad87d8468087d,0x1451428e0e2b262c1047,0x14509931400a2850193,0x8a17202098a0088a3a28,0x245c98a0088a2e4c5022,0x914222811450b9314514,0x6c80310b1428ac88a28,0x931404a285002c565445],#[0x41794522803e4ca8a009,0x6081c30cc88a0652066,0xf106804c60e1b222cb0,0xb802b2a2185a280284c8,0x16528204450058a1720,0x404003145084a28a061,0x386ca5050e1b29410384,0x48098820386ca9060c20,0x624364c5804050c364c,0x28711931208a283c98b0,0x424545282c412911408a,0x404a2084712140144c64,0x4e4c50128a1d22213121,0x2291401f262809450a4c,0x130320c168850c2f263c,0x22245a3448400a8704a,0x7222803a41628664c786,0x8908087045142458ac78,0x280948c9005a21428b46,0xc110a0251c64448189c,0x84a0c2a00d1294a0d112,0xa2c540c784a0c22140c7,0x3262402228]]
set_option maxRecDepth 16000 in
def g246H8 := limbs80 #[#[0x2543b7120c082000d293,0x5c3002a3420e0c040170,0x40c1833200e430304,0x4003030a1aa89801a2,0xb256040240428a880604,0x12e3a806020cfae42240,0x9204180085239d420818,0xf283382204580056f407,0xa02a705400005e545d40,0x7247613a5008843f2421,0x513bd100e29e0000f0a6,0xe16ee071701ab087d016,0x4426f0736477,0x80bad1567058c09f0000,0x80ada025f093484da09a,0x610b0000e0944174b164,0xd011953a00000000,0xb2b2f01500004166d08a,0xbd07ae05044200000,0x126e0af,0x2082c088a15a00000000,0xb55c981f0000345b0821,0xb01800004048441f,0x201b0000a43bb116,0x706df2590000c0760000,0x7519c919311a70030000,0x715d,0xd2660000000000002032,0xc28f545e107f00007443,0xe0ac7009d0208a12,0x95c504b705f4041d40a,0xa468000080855293c1aa],#[0x31b70000a84a0000,0xf849a0532a4c70014268,0x74b1902eb0670000a0b0,0xe01d604c126ee66c513c,0x4169d15fc1ba50a3,0x30b9404754570000a06b,0x30976134f0069136f158,0xa07b508031620146f10e,0x903f417b708d70743026,0x411d212362519037806a,0xe177c49a505500002081,0x7042b16f706362b6802c,0x32580000f06fc06544b5,0x70078089b05be0525835,0xd2a85099917500000000,0x920ae4168264a262,0xd05e0000f030,0x70a14476f17800003039,0x4245c01f0000310dd10f,0x11b1010409b887d0000,0xe16b640e0000e14ab2a6,0x229aa09ca021910c1036,0x70b1008690b8e0597031,0x725a5127c02db25be5a2,0xb128e08ef07e3068942e,0xc14bd0570000d0600000,0x816d60a05040a00ec06e,0x1200000000243d6023,0x2077a2adf85221600000,0x206100000000908c880d,0x12906092000040a51028,0xc26c94750000000050b4],#[0xf05cc2a72005904a5078,0x10b2319f200cb08f0000,0x51107a4d802b0000b083,0xd5a9b02f104e4072a1b9,0x5051284311683117,0x559f20443269b019e270,0x48125033a16a00006467,0x300010452017651d,0x13917cf03a6155401e,0x161d2521246741bc81b,0x1014d1b862880000b022,0xe43450b5c0b68428f458,0x304f9163e84c509e911e,0xc8489027717ed024d165,0xc47820045851706c807d,0x500da0566147205af090,0x3e203d40aa600af091,0x1066,0xe11100001142d03b4867,0xd4714179da4a21730000,0x5427b079f55d,0xf2a100000000495d6095,0x649b00000000401c782b,0xb0a9000070b72a49,0x7029007cb51ad075c40d,0x7265119ce91de46c091a,0x6194f0ae9070516c2002,0x51599425359c0129a668,0xd09d704d8098410a0000,0x10a8d03cf60a60351289,0xb0ab00006167f2636144,0x10b3e87a5038f29b0000],#[0xb1a5204900a7009604a5,0xb0340000608b00004157,0xc06452572069a82a0000,0x60a4b26d10a28176,0xa05d4119e2a00000,0xa0437474e0460000f2ae,0x184f2a34424815ca261,0x1062826a900fe2081084]]
def g246D9 := limbs80 #[#[0xd21fe987fc83fa41fd10,0x51b0259c920a803fe43f,0xa1a48a500426488a00,0xa1461020255052e48a5,0x248a02051539228]]
def g246H9 := limbs80 #[#[0x40100041000600080040,0x9c000000000000000000,0xd12404f0000000e8,0x1813000,0x202300000009004,0x0,0x3000000000000,0x0,0x304ec08400010900000,0x0,0x0,0x0,0xc1400ae000000000000,0xb120000000000,0x0,0x0,0x2019209800000,0x0,0x0,0x0,0x1c2c907800,0x0,0xb00980b00000000,0x142b0000000a88800000,0x53100000000000000000,0x0,0x141d000000000000,0xb287e1e7488000a0a000,0x0,0xa21400000000000,0x10b800000,0x2a00000000000000f5b],#[0x3,0x0,0x8290000000000000,0x0,0x151f000000000000000,0xc0000000000000000000,0x42fd408000a198000386,0x18ac00000000001,0x51b00,0x104bb1a0000000000,0x0,0x18200,0x220e000000000,0x41400000000000000000,0x3,0x3053000000000000,0x150e0000000000000,0x9c00000000000000000,0x100358a800000015158,0x71a4000701800000,0x2417000,0xf0540000000,0x0,0x2288000e478000000000,0x0,0x0,0x18540000000000000000,0x0,0xc08800000000000044,0x0,0x413708c0000000000000,0x680000000000d24501c],#[0x58000922000000000001,0xa9f02,0x0,0xb1af4ad00000001034,0x14a3920700500000,0x38180000000000000,0x1c120000000,0x30000000000000000000,0x70b400050,0x0,0x689800000026210000,0x601c00000000,0xda800000000000000000,0x41400000000000000000,0x64840000,0xd26000000000,0x0,0x0,0xd0000000000280800000,0x32050003d6,0x0,0x0,0x787c05f000000000,0x51b0003d06367c000000,0xe0000000f8080000000,0x6000000000000000000c,0xe03c000d07c000000308,0x51b40000000000,0xf1480000002c310,0x865f06c00000,0x0,0x380a0000],#[0x6000000030c000000000,0xf09710b000020,0x3c0900000002880000,0x631000000000018100,0x610c000000000000,0x72900000000000000,0x3c1600000000000,0x80400000]]
def g246D10 (j : Nat) := if j=0 then 0x2080513f else 0
def g246H10 := limbs80 #[#[0x0,0x2c58000000000000000,0x0,0x740000000,0x1c0800,0x1c10000000000000000,0x1850,0x21059400000000015000,0x10000000000000000000,0x21a200000073000160c9,0x3e0d,0x0,0x0,0xc840,0x0,0x85600000,0x65,0x0,0x0,0x0,0xe02000000000000030]]
def g246L : Nat → Packing
  | 4 => (2,6,5,0,0,3,0,g246D4)
  | 5 => (59,5,5,0,0,10,0,g246D5)
  | 6 => (237,4,5,0,0,12,0,g246D6)
  | 7 => (187,3,5,0,0,13,0,g246D7)
  | 8 => (50,2,5,0,0,12,0,g246D8)
  | 9 => (6,1,5,0,0,8,0,g246D9)
  | 10 => (1,0,5,0,0,0,0,g246D10)
  | _ => emptyPacking
def g246I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 11 0 8 1 3 g246H5
  | 6 => lookupWord 23 127 5 14 6 4 g246H6
  | 7 => lookupWord 109 541 8 16 8 4 g246H7
  | 8 => lookupWord 96 479 7 16 8 4 g246H8
  | 9 => lookupWord 28 587 3 14 6 4 g246H9
  | 10 => lookupWord 4 163 0 11 3 4 g246H10
  | _ => fun _ => none
def g246 : Forest := ⟨246,10,fun i => g246Y[i]?.getD (0,0),g246C,g246A,g246L,g246I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P4_0 : block g246 4 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B4 : block g246 4 0 2=true := g246P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P5_0 : block g246 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P5_1 : block g246 5 1 58=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B5 : block g246 5 0 59=true := (@block_merge g246 5 0 1 58 g246P5_0 g246P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P6_0 : block g246 6 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P6_13 : block g246 6 13 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P6_109 : block g246 6 109 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P6_205 : block g246 6 205 32=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B6 : block g246 6 0 237=true := (@block_merge g246 6 0 109 128 (@block_merge g246 6 0 13 96 g246P6_0 g246P6_13) (@block_merge g246 6 109 96 32 g246P6_109 g246P6_205))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P7_0 : block g246 7 0 10=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P7_10 : block g246 7 10 59=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P7_69 : block g246 7 69 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P7_165 : block g246 7 165 22=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B7 : block g246 7 0 187=true := (@block_merge g246 7 0 69 118 (@block_merge g246 7 0 10 59 g246P7_0 g246P7_10) (@block_merge g246 7 69 96 22 g246P7_69 g246P7_165))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P8_0 : block g246 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P8_1 : block g246 8 1 30=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P8_31 : block g246 8 31 19=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B8 : block g246 8 0 50=true := (@block_merge g246 8 0 1 49 g246P8_0 (@block_merge g246 8 1 30 19 g246P8_1 g246P8_31))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P9_0 : block g246 9 0 6=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B9 : block g246 9 0 6=true := g246P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P10_0 : block g246 10 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B10 : block g246 10 0 1=true := g246P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246T : checkedTables g246 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g246 0 0 0 = true)
  · exact (rfl : block g246 1 0 0 = true)
  · exact (rfl : block g246 2 0 0 = true)
  · exact (rfl : block g246 3 0 0 = true)
  · exact g246B4
  · exact g246B5
  · exact g246B6
  · exact g246B7
  · exact g246B8
  · exact g246B9
  · exact g246B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246G : graphValid g246 (boundsBefore K245) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low246 : Lower true (varsX 246) (graphGoal 246) 11 := lower_forest (g:=g246) (i:=0) (hints:=303105088) (before_sound K245 V245) g246G g246T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K246 := extendKnown K245 11 [(246,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V246 : Known true K246 := extend_ok (m:=246) V245 low246 (by decide +kernel)
def g249Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff007fe1ff87fffff,0x84a42821000f00f00fff])),(BitVec.ofNat 152 (word80 [0x2010040010000400,0x111111111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3ffff8001fff83fe0f,0xc318e23600f00f00f00f])),(BitVec.ofNat 152 (word80 [0x8140202840a0080820,0x210a226222222222222]))),((BitVec.ofNat 152 (word80 [0x3fffffffe00003fff0,0x2e1336480f00f00f00f0])),(BitVec.ofNat 152 (word80 [0x180403000c1101001,0x26122600222222222222]))),((BitVec.ofNat 152 (word80 [0x3ffffffffffffc0000,0x13c281d9f000000fff00])),(BitVec.ofNat 152 (word80 [0xa028140050000a042,0x11c00059444444444444]))),((BitVec.ofNat 152 (word80 [0xc00000000000000000,0x69e90a8a0000fff00000])),(BitVec.ofNat 152 (word80 [0x2c0b0580960222c084,0x49e90888cccccccccccc]))),(0x50555d84ffff00000000,(BitVec.ofNat 152 (word80 [0x300c06011804430108,0x40055980888888888888]))),(0x0,0x0)]
def g249C : List ColumnInfo := [(8,0,241,0,8)]
def g249A : List (List Nat) := [[],[117],[67],[67,117]]
def g249D8 (j : Nat) := if j=0 then 0x7f else 0
def g249L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g249D8)
  | _ => emptyPacking
def g249I (_ _ : Nat) : Option (Nat × Nat) := none
def g249 : Forest := ⟨249,8,fun i => g249Y[i]?.getD (0,0),g249C,g249A,g249L,g249I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P8_0 : block g249 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g249B8 : block g249 8 0 1=true := g249P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249T : checkedTables g249 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g249 0 0 0 = true)
  · exact (rfl : block g249 1 0 0 = true)
  · exact (rfl : block g249 2 0 0 = true)
  · exact (rfl : block g249 3 0 0 = true)
  · exact (rfl : block g249 4 0 0 = true)
  · exact (rfl : block g249 5 0 0 = true)
  · exact (rfl : block g249 6 0 0 = true)
  · exact (rfl : block g249 7 0 0 = true)
  · exact g249B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249G : graphValid g249 (boundsBefore K246) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low249 : Lower true (varsX 249) (graphGoal 249) 9 := lower_forest (g:=g249) (i:=0) (hints:=3) (before_sound K246 V246) g249G g249T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K249 := extendKnown K246 9 [(249,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V249 : Known true K249 := extend_ok (m:=249) V246 low249 (by decide +kernel)
def g250Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7ff83ff83ffffe88,0xc9c12ea40007c00003ff])),(BitVec.ofNat 152 (word80 [0x450850841080210280,0xc8410a84a5294a5294a5]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff80003fffc1ff8195,0x7145909800f801f07c00])),(BitVec.ofNat 152 (word80 [0x6016100a004020995,0x614100106318c6318c63]))),((BitVec.ofNat 152 (word80 [0xffffffc00001fffcd7,0x853244441f003e0f801f])),(BitVec.ofNat 152 (word80 [0x8018000c108040055,0x5000440421084210842]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000021,0x2e5c7923e000000fffe0])),(BitVec.ofNat 152 (word80 [0x901200090000481020,0x147121084210842108]))),((BitVec.ofNat 152 (word80 [0x44,0x90bf8bb000003ff00000])),(BitVec.ofNat 152 (word80 [0xe05c022e0211702000,0x90be8ba39ce739ce739c]))),((BitVec.ofNat 152 (word80 [0x33a,0x528a034bffffc0000000])),(BitVec.ofNat 152 (word80 [0x600430042180400a,0x128a000a108421084210]))),(0x0,0x0)]
def g250C : List ColumnInfo := [(8,0,242,0,8)]
def g250A : List (List Nat) := [[],[117]]
def g250D8 (j : Nat) := if j=0 then 0x7f else 0
def g250L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g250D8)
  | _ => emptyPacking
def g250I (_ _ : Nat) : Option (Nat × Nat) := none
def g250 : Forest := ⟨250,8,fun i => g250Y[i]?.getD (0,0),g250C,g250A,g250L,g250I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P8_0 : block g250 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g250B8 : block g250 8 0 1=true := g250P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250T : checkedTables g250 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g250 0 0 0 = true)
  · exact (rfl : block g250 1 0 0 = true)
  · exact (rfl : block g250 2 0 0 = true)
  · exact (rfl : block g250 3 0 0 = true)
  · exact (rfl : block g250 4 0 0 = true)
  · exact (rfl : block g250 5 0 0 = true)
  · exact (rfl : block g250 6 0 0 = true)
  · exact (rfl : block g250 7 0 0 = true)
  · exact g250B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250G : graphValid g250 (boundsBefore K249) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low250 : Lower true (varsX 250) (graphGoal 250) 9 := lower_forest (g:=g250) (i:=0) (hints:=319901760) (before_sound K249 V249) g250G g250T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K250 := extendKnown K249 9 [(250,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V250 : Known true K250 := extend_ok (m:=250) V249 low250 (by decide +kernel)
def g252Y : Array (Bits × Bits) := #[(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffe0ffe0ffff70a0,0xc54bae40000000fc003f])),(BitVec.ofNat 152 (word80 [0x948142404244407080,0x45432a55555555555555]))),((BitVec.ofNat 152 (word80 [0xfe0000ffffffe0f758,0x8426308003f03f000fc0])),(BitVec.ofNat 152 (word80 [0x18058402800082f508,0x800210830c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xffffff0000ffff2586,0xb2d84280fc0fc003f03f])),(BitVec.ofNat 152 (word80 [0x200600030401000500,0xb2080082082082082082]))),((BitVec.ofNat 152 (word80 [0xffffffffff0000084d,0x6956a9bf00000003ffc0])),(BitVec.ofNat 152 (word80 [0xc02800140016040844,0x4854a80c30c30c30c30c]))),((BitVec.ofNat 152 (word80 [0x1171,0x18b1dc40000ffffc0000])),(BitVec.ofNat 152 (word80 [0x13008980898080071,0x8b0c428a28a28a28a28]))),((BitVec.ofNat 152 (word80 [0xce93,0x4f80057ffff000000000])),(BitVec.ofNat 152 (word80 [0x1c010e010e0100293,0x5800570c30c30c30c30]))),(0x0,0x0)]
def g252C : List ColumnInfo := [(8,0,244,0,8)]
def g252A : List (List Nat) := [[],[117]]
def g252D8 (j : Nat) := if j=0 then 0x7f else 0
def g252L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g252D8)
  | _ => emptyPacking
def g252I (_ _ : Nat) : Option (Nat × Nat) := none
def g252 : Forest := ⟨252,8,fun i => g252Y[i]?.getD (0,0),g252C,g252A,g252L,g252I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g252P8_0 : block g252 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g252B8 : block g252 8 0 1=true := g252P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g252T : checkedTables g252 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g252 0 0 0 = true)
  · exact (rfl : block g252 1 0 0 = true)
  · exact (rfl : block g252 2 0 0 = true)
  · exact (rfl : block g252 3 0 0 = true)
  · exact (rfl : block g252 4 0 0 = true)
  · exact (rfl : block g252 5 0 0 = true)
  · exact (rfl : block g252 6 0 0 = true)
  · exact (rfl : block g252 7 0 0 = true)
  · exact g252B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g252G : graphValid g252 (boundsBefore K250) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low252 : Lower true (varsX 252) (graphGoal 252) 9 := lower_forest (g:=g252) (i:=0) (hints:=842159104) (before_sound K250 V250) g252G g252T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K252 := extendKnown K250 9 [(252,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V252 : Known true K252 := extend_ok (m:=252) V250 low252 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffb820c8ac017d2d0c,0x4a00003f00003f000fff])),(BitVec.ofNat 152 (word80 [0xa28008804011d2c00,0x4a041041041041041041]))),((BitVec.ofNat 152 (word80 [0x2f050e11191793ec,0xc1000000000fc003f000])),(BitVec.ofNat 152 (word80 [0x332f040e10011793ac,0xc14d34d34d34d34d34d3]))),((BitVec.ofNat 152 (word80 [0x79bb1e060412a532,0x2d000fc0000000fc0000])),(BitVec.ofNat 152 (word80 [0x5c39ab1e060412a510,0x292cb2cb2cb2cb2cb2cb]))),((BitVec.ofNat 152 (word80 [0xff909c6d56cc4e9189,0x1003f00003f00000003f])),(BitVec.ofNat 152 (word80 [0x60101845524c429189,0x186186186186186186]))),((BitVec.ofNat 152 (word80 [0x252c2726a934642,0x20fc0000fc0000ffffc0])),(BitVec.ofNat 152 (word80 [0x80001040606a000042,0x104104104104104104]))),((BitVec.ofNat 152 (word80 [0xca90509d3a05010,0xbf000000ffffff000000])),(BitVec.ofNat 152 (word80 [0xa1000990a04010,0x34a28a28a28a28a28a28]))),((BitVec.ofNat 152 (word80 [0x674430c92480a8b5,0x54ffffff000000000000])),(BitVec.ofNat 152 (word80 [0x4644208900800024,0x14c30c30c30c30c30c30]))),(0x0,0x0),(0x0,0x0)]
def g127C : List ColumnInfo := [(8,0,119,0,10)]
def g127A : List (List Nat) := [[],[33,101]]
def g127D10 (j : Nat) := if j=0 then 0xff else 0
def g127L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g127D10)
  | _ => emptyPacking
def g127I (_ _ : Nat) : Option (Nat × Nat) := none
def g127 : Forest := ⟨127,10,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P10_0 : block g127 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B10 : block g127 10 0 1=true := g127P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127T : checkedTables g127 10 := by
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
  · exact (rfl : block g127 9 0 0 = true)
  · exact g127B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K252) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 11 := lower_forest (g:=g127) (i:=0) (hints:=1091) (before_sound K252 V252) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K252 11 [(127,[]),(223,[117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V127 : Known true K127 := extend_ok (m:=127) V252 low127 (by decide +kernel)
def g191Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffffea43612014bcb,0x102200001f0001f003ff])),(BitVec.ofNat 152 (word80 [0x52029a0026020103c9,0x221084210842108421]))),((BitVec.ofNat 152 (word80 [0xff000a084f801c22d6,0xf6860003e0003e007c00])),(BitVec.ofNat 152 (word80 [0x640cca0807801022d6,0x7682318c6318c6318c63]))),((BitVec.ofNat 152 (word80 [0x1f77cba780821a,0x463000000000000f8000])),(BitVec.ofNat 152 (word80 [0x78171f75cba780021a,0x4631bdef7bdef7bdef7b]))),((BitVec.ofNat 152 (word80 [0xffffe44b1363d60d92,0x5980007c0007c000001f])),(BitVec.ofNat 152 (word80 [0x8018040b1141960c12,0x58806318c6318c6318c6]))),((BitVec.ofNat 152 (word80 [0x10ab09924965c,0x88500f8000f8000fffe0])),(BitVec.ofNat 152 (word80 [0x2000021010049400,0x88404210842108421084]))),((BitVec.ofNat 152 (word80 [0x2954164680021,0x2cfbf00000fffff00000])),(BitVec.ofNat 152 (word80 [0x4000944020680020,0x108421084210842108]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x19700c0c937420,0x430dffffff0000000000])),(BitVec.ofNat 152 (word80 [0x800160080c004000,0x10d0842108421084210]))),(0x0,0x0)]
def g191C : List ColumnInfo := [(2,0,189,0,10)]
def g191A : List (List Nat) := [[],[117]]
def g191D10 (j : Nat) := if j=0 then 0xff else 0
def g191L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g191D10)
  | _ => emptyPacking
def g191I (_ _ : Nat) : Option (Nat × Nat) := none
def g191 : Forest := ⟨191,10,fun i => g191Y[i]?.getD (0,0),g191C,g191A,g191L,g191I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P10_0 : block g191 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B10 : block g191 10 0 1=true := g191P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191T : checkedTables g191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0 = true)
  · exact (rfl : block g191 1 0 0 = true)
  · exact (rfl : block g191 2 0 0 = true)
  · exact (rfl : block g191 3 0 0 = true)
  · exact (rfl : block g191 4 0 0 = true)
  · exact (rfl : block g191 5 0 0 = true)
  · exact (rfl : block g191 6 0 0 = true)
  · exact (rfl : block g191 7 0 0 = true)
  · exact (rfl : block g191 8 0 0 = true)
  · exact (rfl : block g191 9 0 0 = true)
  · exact g191B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191G : graphValid g191 (boundsBefore K127) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low191 : Lower true (varsX 191) (graphGoal 191) 11 := lower_forest (g:=g191) (i:=0) (hints:=1091) (before_sound K127 V127) g191G g191T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K191 := extendKnown K127 11 [(191,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V191 : Known true K191 := extend_ok (m:=191) V127 low191 (by decide +kernel)
def g239Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x991441cca21ba2225c,0x400000fe0007f0003fff])),(BitVec.ofNat 152 (word80 [0x904410c8203a20010,0x40408102040810204081]))),((BitVec.ofNat 152 (word80 [0x6858f90005b2e7ed10,0x20007f000000001fc000])),(BitVec.ofNat 152 (word80 [0x2858f1000512e7e510,0x2c58b162c58b162c58b]))),((BitVec.ofNat 152 (word80 [0x3dc96b07926648b166,0x3f800000000])),(BitVec.ofNat 152 (word80 [0x3dc16b07926240a166,0x9d3a74e9d3a74e9d3a7]))),((BitVec.ofNat 152 (word80 [0x90e264355411d52622,0x803f8001fc000fe0007f])),(BitVec.ofNat 152 (word80 [0x10c224010410512602,0x810204081020408102]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x6260a631f8268c8c9,0x1fc0000000000fffff80])),(BitVec.ofNat 152 (word80 [0x2200a621080080849,0x50a142850a142850a14]))),((BitVec.ofNat 152 (word80 [0x8b93482c1cc0c1599,0xe0000001fffff0000000])),(BitVec.ofNat 152 (word80 [0x381080418c0c1089,0xb62c58b162c58b162c58]))),((BitVec.ofNat 152 (word80 [0x6741939828201310a7,0xbffffffe000000000000])),(BitVec.ofNat 152 (word80 [0x4401009028200010a4,0xb83060c183060c183060]))),(0x0,0x0)]
def g239C : List ColumnInfo := [(2,0,237,0,10)]
def g239A : List (List Nat) := [[],[117],[48],[48,117]]
def g239D10 (j : Nat) := if j=0 then 0xff else 0
def g239L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g239D10)
  | _ => emptyPacking
def g239I (_ _ : Nat) : Option (Nat × Nat) := none
def g239 : Forest := ⟨239,10,fun i => g239Y[i]?.getD (0,0),g239C,g239A,g239L,g239I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P10_0 : block g239 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B10 : block g239 10 0 1=true := g239P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239T : checkedTables g239 10 := by
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239G : graphValid g239 (boundsBefore K191) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low239 : Lower true (varsX 239) (graphGoal 239) 11 := lower_forest (g:=g239) (i:=0) (hints:=1619) (before_sound K191 V191) g239G g239T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K239 := extendKnown K191 11 [(239,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V239 : Known true K239 := extend_ok (m:=239) V191 low239 (by decide +kernel)
def g247Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x6d7d8188c6a090800,0x3f8001fc000fe0007f])),(BitVec.ofNat 152 (word80 [0x6520818842a090810,0x20408102040810204081]))),((BitVec.ofNat 152 (word80 [0x8f0c0ca8e5b7049000,0x1fc000000007f0003f80])),(BitVec.ofNat 152 (word80 [0x8f0c0c8884b3048091,0x22448912244891224489]))),((BitVec.ofNat 152 (word80 [0x7a4139115783b58800,0xfe0000001fc000])),(BitVec.ofNat 152 (word80 [0x3a4139114782958a54,0xa952a54a952a54a952a5]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x24082817001806600f,0xe0007f0003f8001fffff])),(BitVec.ofNat 152 (word80 [0x20,0x40810204081020408102]))),((BitVec.ofNat 152 (word80 [0x3a163c2b380585ff0,0x3ffffe00000])),(BitVec.ofNat 152 (word80 [0x8161423100505142,0x850a142850a142850a14]))),((BitVec.ofNat 152 (word80 [0xd9dc830c1807e07000,0x7ffffc0000000000])),(BitVec.ofNat 152 (word80 [0xc18c8204180560758b,0x162c58b162c58b162c58]))),((BitVec.ofNat 152 (word80 [0xb022966446647387ff,0xffff8000000000000000])),(BitVec.ofNat 152 (word80 [0x30209224424422060c,0x183060c183060c183060]))),(0x0,0x0)]
def g247C : List ColumnInfo := [(1,0,246,0,11)]
def g247A : List (List Nat) := [[],[117]]
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
theorem low247 : Lower true (varsX 247) (graphGoal 247) 12 := lower_forest (g:=g247) (i:=0) (hints:=1092) (before_sound K239 V239) g247G g247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K247 := extendKnown K239 12 [(247,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V247 : Known true K247 := extend_ok (m:=247) V239 low247 (by decide +kernel)
def g251Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xd390a158881c424400,0x3f000fc0000fc0fff])),(BitVec.ofNat 152 (word80 [0x19020180004404410,0x41041041041041041041]))),((BitVec.ofNat 152 (word80 [0x239d2c00d0c015f800,0xfc000000003f03f000])),(BitVec.ofNat 152 (word80 [0xa39c2400904001f8b2,0xcb2cb2cb2cb2cb2cb2cb]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc50e10c1f22d891000,0x3f00003f000fc000003f])),(BitVec.ofNat 152 (word80 [0xa00c1f008891061,0x86186186186186186186]))),((BitVec.ofNat 152 (word80 [0x86226ee54000e080f,0xc0000fc003f00003ffc0])),(BitVec.ofNat 152 (word80 [0x82200c044000e0041,0x4104104104104104104]))),((BitVec.ofNat 152 (word80 [0x8bd2050de22027f0,0x3fffffc0000])),(BitVec.ofNat 152 (word80 [0x1920409a0200104,0x10410410410410410410]))),((BitVec.ofNat 152 (word80 [0x367503820823f03800,0xffffc0000000000])),(BitVec.ofNat 152 (word80 [0x364503020823302b8e,0x38e38e38e38e38e38e38]))),((BitVec.ofNat 152 (word80 [0x2c004932231239c3ff,0xfffff000000000000000])),(BitVec.ofNat 152 (word80 [0x40049220212100208,0x20820820820820820820]))),(0x0,0x0)]
def g251C : List ColumnInfo := [(8,0,243,0,10),(16,0,235,0,10),(64,0,187,0,10),(1,0,250,0,9),(2,0,249,0,9),(32,0,219,0,9),(128,0,123,0,9),(65,0,186,0,8),(66,0,185,0,8),(0,2,73,176,7),(0,64,162,25,7),(96,0,155,0,7),(160,0,91,0,7),(192,0,59,0,7),(1,64,162,24,6),(3,0,248,0,6),(32,2,73,144,6),(33,0,218,0,6),(34,0,217,0,6),(128,2,73,48,6),(129,0,122,0,6),(97,0,154,0,5),(98,0,153,0,5),(160,2,73,16,5),(162,0,89,0,5)]
def g251A : List (List Nat) := [[],[117]]
def g251D7 := limbs80 #[#[0xaa280885cc6595450110,0x216399655160502e672c,0xd98059541f98c32a8a02,0x7846812acde3c0071fd,0xc0e615f845e24941ce6f,0x24d17c81707783c23713,0x4d52564b102362f039bc,0x70]]
def g251D8 := limbs80 #[#[0xf395450110f315450110,0xfb16450110bf38050510,0xf716550110fb37450110,0xbf38650110bf18650110,0xb778655110b758655110,0xb778655310b758655310,0xeb96458140f395458140,0xb3f8655140b3d8655140,0xc7f7659541eb56458541,0xf3d5458540ff18650110,0xf3d545c540ebd6458540,0xf7d8059541f3d7655140,0x4510870e01341d01f000,0x716f2984c4890f71b830,0x47450844fb1db3806a4c,0x4438ac5f83847a152f2,0x4c4840b8348e0e1171b1,0x10c40fe2e0e12c238384,0xe11718978b83845c511,0x47138b8384b07626d0ee,0x43860fe2e066e1111850,0x3e066e12b1b119a97838,0x18b4ae97130f83847c4c,0xf829b848c4c366e0e12b,0x7e2e0e10c1c47905c392,0x17905d9b838438603e41,0x78b83846061766e0e115,0x5c6e3132de0e15218162,0xe0e110181450478b8384,0x71690470f8033844074b,0x885f838444912e0e1151,0x27865249122ca9919a]]
def g251H8 := limbs80 #[#[0x73a2,0x900000000000,0x0,0x0,0x78000000000000000000,0x0,0xa1a400]]
def g251D9 := limbs80 #[#[0x554c43baaa221fc50110,0xb2a95f5d954e7aa8a077,0x10fea82887f940442bfb,0x5ff74442feba221df551,0xbba221fd5d110feac888,0xc540ff2c0a07f564c43f,0xa077d65503deb22817fd,0x6ffb82837fdd940bfaec,0xf59541f7ac8a0ff56150,0xe0aa5ff76506febb283d,0x503bebb2a9df5c554efa,0x1ff5d940ffae2a07fd61,0xc8c114b20c3204183e00,0x92af558a9e5282203c46,0x4d794116e07bd1742d71,0xc4f7c2e3d9eac14c280,0x97062c25c8debafb4765,0x8395a2c10f0972488388,0x1cad1664b121e0c24a58,0x972488ecd905e0c30c8,0xb0611638d17913451d83,0x181c4c58309718be4c69,0x4878309723143c097093,0xc5878b025c24c6162914,0x421e2c185614970611e5,0xd0f1604b8498c4c7a588,0xe2c18560e112e0c23cb8,0x3642317160c25c94b121,0x1846110f1608b8498c51,0x4c3b0612e511c85f143c,0x42f8b061184a28b0d6e4,0x842e9b160c244728461e],#[0x27160c2606c48f061302,0xc2608261b160c26060a,0x89c58309815686458c9e,0x90560c2547c18b093242,0x116388118308e2c287cd,0xe2c1848181880d489b06,0x84890487e2c1848971e1,0x14c85f10cc1]]
def g251H9 := limbs80 #[#[0x1c7f5a52d50d000,0xcc9040014da30000000,0x3400000000314bd00000,0x7c3000001b8006108800,0x377000003cdace364a71,0x4004268ec545085ecb00,0x51aa50000060b0fb4]]
def g251D10 := limbs80 #[#[0x40ff4437d54fdc43f510,0x2c6018003fd64ff507fd,0xe24d28704508f3e81331,0x2462c109134a20704508,0x9134a2070450ae4045cd,0xa2450424a33482871410,0xb8b2471410984244cd18]]
def g251H10 := limbs80 #[#[0xa1c000000306b9300030,0x1e4c00000001,0x11c0000000080c00,0x0,0xc8715000000000,0x386800e820028d000,0x48000008380000000800,0xa04000000000004,0x71800000000000000000,0x40000000041600022800,0x9b23c00000000000c891,0x920ccf97da2f5d600008,0x21b01600000000000,0x4ce8ec104000000000,0x31a5763a1785b944780,0x97800000619e828fe,0x34edc6,0x913204e480000]]
def g251D11 (j : Nat) := if j=0 then 0x3148300823ff else 0
def g251H11 := limbs80 #[#[0x4c798000003700000020,0x190000001cd0803017,0x228000001140]]
def g251L : Nat → Packing
  | 7 => (5,4,5,0,0,9,0,g251D7)
  | 8 => (24,3,5,0,0,11,0,g251D8)
  | 9 => (33,2,5,0,0,11,0,g251D9)
  | 10 => (7,1,5,0,0,9,0,g251D10)
  | 11 => (1,0,5,0,0,0,0,g251D11)
  | _ => emptyPacking
def g251I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 97 0 8 3 1 g251H8
  | 9 => lookupWord 7 53 4 10 5 1 g251H9
  | 10 => lookupWord 12 127 4 11 6 1 g251H10
  | 11 => lookupWord 2 29 3 8 3 1 g251H11
  | _ => fun _ => none
def g251 : Forest := ⟨251,11,fun i => g251Y[i]?.getD (0,0),g251C,g251A,g251L,g251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_0 : block g251 7 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_3 : block g251 7 3 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_4 : block g251 7 4 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B7 : block g251 7 0 5=true := (@block_merge g251 7 0 3 2 g251P7_0 (@block_merge g251 7 3 1 1 g251P7_3 g251P7_4))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_0 : block g251 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_1 : block g251 8 1 17=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_18 : block g251 8 18 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_23 : block g251 8 23 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B8 : block g251 8 0 24=true := (@block_merge g251 8 0 18 6 (@block_merge g251 8 0 1 17 g251P8_0 g251P8_1) (@block_merge g251 8 18 5 1 g251P8_18 g251P8_23))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_0 : block g251 9 0 6=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_6 : block g251 9 6 24=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_30 : block g251 9 30 3=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B9 : block g251 9 0 33=true := (@block_merge g251 9 0 6 27 g251P9_0 (@block_merge g251 9 6 24 3 g251P9_6 g251P9_30))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_0 : block g251 10 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_3 : block g251 10 3 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B10 : block g251 10 0 7=true := (@block_merge g251 10 0 3 4 g251P10_0 g251P10_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P11_0 : block g251 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B11 : block g251 11 0 1=true := g251P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251T : checkedTables g251 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g251 0 0 0 = true)
  · exact (rfl : block g251 1 0 0 = true)
  · exact (rfl : block g251 2 0 0 = true)
  · exact (rfl : block g251 3 0 0 = true)
  · exact (rfl : block g251 4 0 0 = true)
  · exact (rfl : block g251 5 0 0 = true)
  · exact (rfl : block g251 6 0 0 = true)
  · exact g251B7
  · exact g251B8
  · exact g251B9
  · exact g251B10
  · exact g251B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251G : graphValid g251 (boundsBefore K247) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low251 : Lower true (varsX 251) (graphGoal 251) 12 := lower_forest (g:=g251) (i:=0) (hints:=67) (before_sound K247 V247) g251G g251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K251 := extendKnown K247 12 [(251,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V251 : Known true K251 := extend_ok (m:=251) V247 low251 (by decide +kernel)
def g253Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x8280b203ea22180000,0x1fc00001fc000fe03fff])),(BitVec.ofNat 152 (word80 [0x8030018a20000810,0x20408102040810204081]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x6dd021e34525900000,0xfe0000001fc000])),(BitVec.ofNat 152 (word80 [0x69d020e34520115ab5,0x6ad5ab56ad5ab56ad5ab]))),((BitVec.ofNat 152 (word80 [0x3067c1c429c810000f,0xe0007f000007f000007f])),(BitVec.ofNat 152 (word80 [0x42c14021c8103060,0xc183060c183060c18306]))),((BitVec.ofNat 152 (word80 [0x489ad95000566007f0,0x3f800003f8001fff80])),(BitVec.ofNat 152 (word80 [0x2c1100046002040,0x81020408102040810204]))),((BitVec.ofNat 152 (word80 [0x2f490e3f124007f800,0x3ffffe00000])),(BitVec.ofNat 152 (word80 [0x2e090e26100000c183,0x60c183060c183060c18]))),((BitVec.ofNat 152 (word80 [0x940f022814a1e00000,0x3ffffffc0000000000])),(BitVec.ofNat 152 (word80 [0x940d02081001e2850a,0x142850a142850a142850]))),((BitVec.ofNat 152 (word80 [0x41246488d518afffff,0xffc00000000000000000])),(BitVec.ofNat 152 (word80 [0x412400884410af060c,0x183060c183060c183060]))),(0x0,0x0)]
def g253C : List ColumnInfo := [(8,0,245,0,10),(16,0,237,0,10),(64,0,189,0,10),(0,4,169,80,9),(1,0,252,0,9),(4,0,249,0,9),(32,0,221,0,9),(128,0,125,0,9),(160,0,93,0,7),(33,0,220,0,6),(129,0,124,0,6),(161,0,92,0,5)]
def g253A : List (List Nat) := [[],[117]]
def g253D8 := limbs80 #[#[0x11372e1c48eb96458140,0xbf5e7]]
def g253D9 := limbs80 #[#[0x960503fab2621fd59110,0xb2817f5d940f7ac8a07f,0xc478a361446018002ffb,0xd6ca5930c475d6ca3930,0x820a244d735f2c3198a5,0xcf2c31209275ce4cb0c4,0x1435f2c70247289935]]
def g253H9 (j : Nat) := if j=0 then 0x9 else 0
def g253D10 := limbs80 #[#[0xff593fd40fdc43f510,0x88f7b10709447855229,0x7356649422b26f62925,0x18959ca1141]]
def g253H10 := limbs80 #[#[0x656400eb727100a3,0xd0]]
def g253D11 (j : Nat) := if j=0 then 0xec8a640247f else 0
def g253H11 (j : Nat) := if j=0 then 0x50f658961 else 0
def g253L : Nat → Packing
  | 8 => (1,3,4,0,0,0,0,g253D8)
  | 9 => (6,2,4,0,0,9,0,g253D9)
  | 10 => (4,1,4,0,0,8,0,g253D10)
  | 11 => (1,0,4,0,0,0,0,g253D11)
  | _ => emptyPacking
def g253I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 1 2 0 4 0 0 g253H9
  | 10 => lookupWord 1 11 0 8 3 1 g253H10
  | 11 => lookupWord 1 5 0 7 2 1 g253H11
  | _ => fun _ => none
def g253 : Forest := ⟨253,11,fun i => g253Y[i]?.getD (0,0),g253C,g253A,g253L,g253I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_0 : block g253 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B8 : block g253 8 0 1=true := g253P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_0 : block g253 9 0 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B9 : block g253 9 0 6=true := g253P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P10_0 : block g253 10 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P10_2 : block g253 10 2 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B10 : block g253 10 0 4=true := (@block_merge g253 10 0 2 2 g253P10_0 g253P10_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P11_0 : block g253 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B11 : block g253 11 0 1=true := g253P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253T : checkedTables g253 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g253 0 0 0 = true)
  · exact (rfl : block g253 1 0 0 = true)
  · exact (rfl : block g253 2 0 0 = true)
  · exact (rfl : block g253 3 0 0 = true)
  · exact (rfl : block g253 4 0 0 = true)
  · exact (rfl : block g253 5 0 0 = true)
  · exact (rfl : block g253 6 0 0 = true)
  · exact (rfl : block g253 7 0 0 = true)
  · exact g253B8
  · exact g253B9
  · exact g253B10
  · exact g253B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253G : graphValid g253 (boundsBefore K251) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low253 : Lower true (varsX 253) (graphGoal 253) 12 := lower_forest (g:=g253) (i:=0) (hints:=1027) (before_sound K251 V251) g253G g253T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K253 := extendKnown K251 12 [(253,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V253 : Known true K253 := extend_ok (m:=253) V251 low253 (by decide +kernel)
def g254Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xd2c83b904bca252400,0x7f000000001fc07f])),(BitVec.ofNat 152 (word80 [0xd2c009904a0a212401,0x22448912244891224489]))),((BitVec.ofNat 152 (word80 [0x68af80954336199a20,0x3f800003f80])),(BitVec.ofNat 152 (word80 [0x48ad80940316191a24,0xa952a54a952a54a952a5]))),((BitVec.ofNat 152 (word80 [0xcad768808411d03190,0x3f8001fc000fe00000])),(BitVec.ofNat 152 (word80 [0xcad668808410900010,0x60c183060c183060c183]))),((BitVec.ofNat 152 (word80 [0x8032249ab04c92cc40,0x1fc000fe0007f0003fff])),(BitVec.ofNat 152 (word80 [0x122400a040828000,0x40810204081020408102]))),((BitVec.ofNat 152 (word80 [0x5a999692412e442af,0xe00000000007ffffc000])),(BitVec.ofNat 152 (word80 [0x52990090000444282,0x850a142850a142850a14]))),((BitVec.ofNat 152 (word80 [0x7154152740a10967d0,0xfffff800000000])),(BitVec.ofNat 152 (word80 [0x3100112340a10065cb,0x162c58b162c58b162c58]))),((BitVec.ofNat 152 (word80 [0x3f00c2649b8102186f,0xffffff00000000000000])),(BitVec.ofNat 152 (word80 [0x20000264118100186c,0x183060c183060c183060]))),(0x0,0x0)]
def g254C : List ColumnInfo := [(8,0,246,0,11)]
def g254A : List (List Nat) := [[],[117]]
def g254D11 (j : Nat) := if j=0 then 0xff else 0
def g254L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g254D11)
  | _ => emptyPacking
def g254I (_ _ : Nat) : Option (Nat × Nat) := none
def g254 : Forest := ⟨254,11,fun i => g254Y[i]?.getD (0,0),g254C,g254A,g254L,g254I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254P11_0 : block g254 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g254B11 : block g254 11 0 1=true := g254P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254T : checkedTables g254 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g254 0 0 0 = true)
  · exact (rfl : block g254 1 0 0 = true)
  · exact (rfl : block g254 2 0 0 = true)
  · exact (rfl : block g254 3 0 0 = true)
  · exact (rfl : block g254 4 0 0 = true)
  · exact (rfl : block g254 5 0 0 = true)
  · exact (rfl : block g254 6 0 0 = true)
  · exact (rfl : block g254 7 0 0 = true)
  · exact (rfl : block g254 8 0 0 = true)
  · exact (rfl : block g254 9 0 0 = true)
  · exact (rfl : block g254 10 0 0 = true)
  · exact g254B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254G : graphValid g254 (boundsBefore K253) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low254 : Lower true (varsX 254) (graphGoal 254) 12 := lower_forest (g:=g254) (i:=0) (hints:=303125568) (before_sound K253 V253) g254G g254T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K254 := extendKnown K253 12 [(254,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V254 : Known true K254 := extend_ok (m:=254) V253 low254 (by decide +kernel)
def g255Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff000000ff00000,0xff0000ffff000806246])),(BitVec.ofNat 152 (word80 [0x101010101010101010,0x10101010101000002002]))),((BitVec.ofNat 152 (word80 [0xff00000000000000f,0xf0000ff00000210604bf])),(BitVec.ofNat 152 (word80 [0x313131313131313131,0x3131313131302002003f]))),((BitVec.ofNat 152 (word80 [0xff0000000,0xff0000000c018010f])),(BitVec.ofNat 152 (word80 [0xb4b4b4b4b4b4b4b4b4,0xb4b4b4b4b4b040080007]))),((BitVec.ofNat 152 (word80 [0xf000000ff000000ff0,0xff102208807])),(BitVec.ofNat 152 (word80 [0x606060606060606060,0x60606060606002008005]))),((BitVec.ofNat 152 (word80 [0xff000000ff000,0xffffff002044111c1])),(BitVec.ofNat 152 (word80 [0x404040404040404040,0x404040404040040111c0]))),((BitVec.ofNat 152 (word80 [0xfffff,0xfff00000000c187e1e20])),(BitVec.ofNat 152 (word80 [0x828282828282828282,0x828282828284087c0a00]))),((BitVec.ofNat 152 (word80 [0xffffffff00000,0xfe07fe008])),(BitVec.ofNat 152 (word80 [0xb0b0b0b0b0b0b0b0b,0xb0b0b0b0b0fa0764008]))),((BitVec.ofNat 152 (word80 [0xfffff0000000000000,0xfff800030])),(BitVec.ofNat 152 (word80 [0xc0c0c0c0c0c0c0c0c,0xc0c0c0c0c0bd1800000]))),(0x0,0x0)]
def g255C : List ColumnInfo := [(1,0,254,0,12),(2,0,253,0,12),(4,0,251,0,12),(8,0,247,0,12),(16,0,239,0,11),(32,0,223,0,11),(64,0,191,0,11),(128,0,127,0,11),(0,4,171,80,10),(40,0,215,0,10),(66,0,189,0,10),(136,0,119,0,10),(16,4,171,64,9),(72,0,183,0,9),(96,0,159,0,9),(160,0,95,0,9),(192,0,63,0,9),(0,2,77,176,8),(0,64,162,29,8),(24,0,231,0,8),(48,0,207,0,8),(80,0,171,0,8),(80,4,171,0,8),(144,0,111,0,8),(16,2,77,160,7),(16,64,162,13,7),(24,64,162,5,6),(48,2,77,128,6),(104,0,151,0,6),(144,2,77,32,6),(168,0,87,0,6),(200,0,55,0,6),(56,0,199,0,5),(88,0,163,0,5),(88,4,163,0,5),(112,4,139,0,5),(152,0,103,0,5),(176,0,77,0,5),(176,2,77,0,5),(208,4,43,0,5),(232,0,23,0,3)]
def g255A : List (List Nat) := [[],[117]]
def g255D7 := limbs80 #[#[0xef85f05976196555143,0x143af17c165da6e15545,0x6450ebc5f0597e958655,0x559143f81fb761d85595,0x5d56450ef85f05b76156,0x197559143f81d87ed985,0x5a85d56450f3a5f05bae,0xa7e998559143ce97b6ec,0x16dda5e196450eba5f05,0x61fb4699855d543ae97c,0x97b4ec5a9e197550f647,0x9c5e97a4e85985d543c7,0x3a795c6e93a16617550f,0x50e9f4f01a6e85985d54,0xd543a797c469ba166175,0x17550f947e9fa5e91985,0x985d543a79bc069ba466,0x46598550e9c7f15a6e91,0x5436301e00a797c165fa,0xd8c6c0baa8a2908a8466,0x8071177082f6f0eae4de,0x4c50b1381652e46080cc,0x40019141034581000a52,0x3840]]
set_option maxRecDepth 16000 in
def g255D8 := limbs80 #[#[0xa8a1de1fb76196555143,0x65d55450ef8bd8b2eb2a,0xf62cbf0aaa2877476df8,0x1de1fb56197655143be2,0x95450e78fdab50bb2a8a,0xd3f0caa2873c76dfa561,0x97b165d96551439e3f6a,0x50f3cad3742cbaa8a1d7,0xeab2287e8761d8559564,0x5e197559143f23b0ec2a,0x74edd70cbaac8a1de1db,0x22873e5ec5a85d56450e,0x786591439d3b6fd330ab,0xd2742cc2eaa1ce9fb769,0x79c7e97a46617550f3cb,0x55143fc3b2ec32caaa28,0x2cbaaa8a1fd1d8761975,0x76d9875d55450fe8ec3b,0x43fa3f6cc3aeaaa287f4,0xb2a8a1ef1d9769b85551,0x5a85d95450fe8fdab0eb,0xe3b2fd2b0caa2873e7ee,0x8a1df1fb561d8655143d,0x6195450efcbd8b2ec32a,0x62cbf0caa287de5ec597,0xf797b165f8655143bf2f,0x5450ef8fdab0ecb2a8a1,0x2b0eaa287bc769ba561d,0xfb56998755143de3b6dd,0xebcfdc34ccbaa8a1df1,0xab2287f876dd85595645,0x6157559143fc3f6ec2ac],#[0x8ec3b0abaac8a1fe1fb6,0x287f47edd855d56450fe,0x7559143df2f62d42eab2,0xb350baac8a1ef1fb56a1,0xea761fa66156450f74fd,0x9143dd3b4fd330ab2287,0xec2ac8a1de9db7e99855,0xed5876156450ef8fdab0,0x3bf2f62d3b0ab2287ec7,0xacaa1ee9db7697865914,0xa76156550fcafd3b0ec2,0x3f68d3b0ab2a877d5ec5,0xa1e79fb4e9d9859543be,0x157550fcaec3b0cc2aea,0xed330abaa877c7ed1a66,0xd5fb7699855d543f2bb0,0x550fcaec3f4cc2aeaa1d,0x30cbaa875f5ec5986197,0xb16a7865d543af3f68cc,0xf3cfda353c32eaa1e7d7,0xbaa87de5e93a16617550,0x85985d543eeaf4bd0b30,0xbd3742cc2eaa1e7d5a6e,0x87dc7e97a46617550f3e,0x85d543cf3b4dd2330baa,0x748cc2eaa1e79fa6e919,0x57e9fa56617550ebcedb,0x543afb760d3330baa87d,0xcc2eaa1d79fb4699985d,0xe1a66617550ebafdab4c,0xd73b0fd232cc2a874f7e,0xaa1e79d97e919661543],#[0x76598550f3cfcbf48cb3,0xf62cbb2cc2a87a77e9d8,0x1d79fb465d9661543afa,0x98550ebebd8b2fcb30aa,0xd3f2cc2a875e7ed197e5,0x5f97e958761543cf3f68,0x50f7cbd2742cbb0aa1f9,0x2ec2a87bd5e97a165d85,0x469b9761543de3f4bd23,0x3cfda34fcab0ca1d79fb,0x32875f5ec5a76578650f,0xb9161d54af3f68d3b2bc,0x3b812003d00073b7b465,0x2b412b083837615d0900,0x93748fe4211e70d68624,0x666c31217c8b6a56d292,0xe9d84ea07343869bc4d2,0xfa85641d2078fd87ba3b,0xcf25b127492948123150,0x4e4a4b51227f53c29ba4,0x5ae2d01632af2565aa65,0xd8b8c14601af7176ab8e,0xe6b9352da48ce7660320,0xb5ca2e35701b79db96d8,0x6d79dbca9e1ced176039,0x18a08d01f7f6bf19f3ef,0x10a87cc3761990b083f4,0x46ca32d17a8a9c4de24d,0xe13fe0fc2f8006858e7,0x882984ee3918f85f0327,0x84e51771be17c1f8044c,0x3f005c27f0be044f1127],#[0xf83f0be0113180d7c2f8,0xc2f803f04e07b1f63345,0xfc0190fec6043517e0f,0xfe061623635c7f8504fe,0xc588231051657c2d0771,0x913a23395f09c1825f80,0xf29e3fc189df0be001a1,0x13c100d746f83f0be00c,0x3f83f0be02cf1f8aa0b8,0xfc1f85f0167900828a91,0xa57c2f8040240400628a,0xbe00dc5468d13d8fb15,0x5f00100c11b62852f83f,0xf85f010f0cf1f0afc1f8,0x83f85f07e00a4748d9c1,0x84689d709e0a4f13a3f,0x85138383343122dc2b8c,0xf618f09e08d0c8a450cb,0x5278604d27040981081,0x4a78406414333402990f,0x5106960cd8413b068af0,0xe8dc19b084d1b8336164,0x4e0f637830b636130a27,0x73c27820998b0d833612,0xc130d2784f058b0a3482,0x67c4e13c18208705b450,0x9293c78131384782948,0xc6284068629130d296c7,0xff83d18383c307a30631,0x140d5160e67846f8218c,0x160401d160a0b3de088b,0x6b230654a85e460c125],#[0x2078273c4c13c582a16,0x3c132707c118cf460c12,0x8460320952b8f9383c1,0x8e0703a33636c6245b84,0x3043630a3dc209c298de,0x3e04a45b8c2e0908e070,0xc201a1e8dd19b0830261,0xe0fe0ec617c204109466,0x24fb821783b821024041,0x4879c204e30253c27802,0x6046784f05e00fe0fe08,0x7f04c20a1481050098c,0xc27c10427fc108293c6f,0x49f71be08814b27fc1b8,0x9a281a0c14052f821852,0x69081852782d3d6309b1,0x13466c20810f8408292c,0x1c13a102519b0b274c7,0x63b840aa283148020461,0x95c63081ec7b08130907,0x200b44f840810dc7082,0x12704a48e657c215c2]]
def g255H8 := limbs80 #[#[0x94400022c00213d21101,0x5140000091e3c008,0x1c0092272001430020c0,0x90ea480062c007114a9,0x240000046001d0003237,0xf058d5]]
set_option maxRecDepth 16000 in
def g255D9 := limbs80 #[#[0x6555143f875d96555143,0x3bc769d6555143f87619,0xb8555143f4761d755514,0x43ec761f8555143bc769,0x597655143bc769f85551,0x1439e76a57655143da76,0xe9d9655143bc7e958655,0x51439e769f96551439e7,0x5e859755143bc7e95875,0x55143de5e859755143be,0xe769b97551439e7e9997,0x559143f8761565591439,0xba7e998559143ba769d6,0x9859543ba76978659143,0x3e5761d855d5439e7e91,0x1985d5439f5e85985d54,0x54f0f5d9655d1549e7e9,0x85985d954b4f69d655d1,0x143fc761d65551438fde,0x6197555143fc765d6555,0x5143fc7e197555143fc7,0x765f8555143fc7659755,0x55143fa76197655143fc,0x6761d7655143fa765976,0x655143be76a17655143f,0xde765d8655143be76a57,0x8655143de7e5d8655143,0x3de765f8655143be7e9d,0xf8655143de7e5f865514,0x43de765d9655143be769,0x1f9655143de761d96551,0x143fc7e958755143de76],#[0x69b8755143be7e998755,0x9143de76999755143be7,0x76157559143fa761d655,0x59143fa7e197559143fc,0xa7e998559143be76a175,0x559143ee761d8559143f,0xbe7e9d8559143ee7e1d8,0x8559543be769f8559143,0x3bb7e9d8659543ed761d,0xd855d5439f7e9d985954,0x43f57e9d855d543f5761,0xa7865d543bd7697865d5,0x543df5e85985d5439f76,0xe95985d543de7e91985d,0x1543be7e919661543dd7,0x7e9587615439f769f966,0x61543ed7e958761543bd,0xe7e919761543bf5e8597,0x5e19439f769f9561943b,0xf8f659655d1549f7e9d9,0x8759554f4f619755d154,0x49efe91985d954bdde85,0xb9161d54afde85876195,0x54cfd69b9161d54cfd65,0x1d8655143aefe919661d,0x143fe765d8655143fe76,0x61d9655143fe765f8655,0x5143fe76998755143fe7,0x761d8559143fe7e99875,0x59143fe769d8559143fe,0xd769d8559543fe7e9d85,0x55d543fd7e9d8559543f],#[0xfd7699855d543fd76198,0x865d543fd7e99855d543,0x3df7699985d543df7661,0xd8661543df7e99985d54,0x43df7e5d8661543ef761,0x5d9661543ef761d96615,0x543df7e5d9661543df76,0x61f9661543bf7e9d9661,0x1543df765f9661543ef7,0x5e859761543bf769f966,0x61543fe7e919761543ff,0xf769b9761543fd7e9597,0x661d54df769d95e1943d,0x2f008400e0000eefe919,0x3823808001b405a011c0,0x83f60ed03540c202c60a,0x56414b04f412c847010b,0x4a1bd06a819705fc1710,0xe240889820b87ec1e807,0x2b78a922940a04269094,0x428ca03150bfe2e78b48,0x10eb83988e2036d8d563,0x10b241210063ec0f643c,0x29848e120046a9168442,0x7450c93d24e1933a4b91,0xa58615cc565153453294,0x61397da5de971a5ae965,0x8319c065d191e6371890,0x41bc46de1b186b09a6c6,0x1d6474b1d0872a1c6670,0xee67a69e4e7859dd4767,0x8681120027f29f747ca1],#[0xe871a1988582114834a0,0x8c822de8ac2278892a1f,0xa1fc1343c2f001a16362,0x1a1614f1c4ef07c2f001,0xbc1f004f27c1343c2f00,0x221c1a8511322fc6f0,0xf004f1cc8f1c19853c1f,0x1f018b1d8bf181af0bc1,0xc2f001a1645f181af0bc,0xf45f07c2f005223c113b,0x53c7f07c0088509c03b1,0xf1c5262fc1f0bc093864,0xc02452a36c6f0bc1f014,0x14067c6516c7f0824f07,0x945e0fc6b1fc2f001b19,0xf005293c6e0fc6f0bc00,0xbf07c2f014e180df07c2,0xc713bc1f0216068614a8,0x581a17c1f0bc033c1a17,0xf07c2f018926c5f07c04,0x2f001a142014a15f1c13,0x84f0bc1f004f27c1073c,0xbc00624f1d0b8241af1b,0xbc1f001e1e93e0fc6f0,0xf0bc3f008e209314bc6f,0xef0bc3f00805c14143c1,0xc2f0fc01c0f14304f048,0xbc09381a1b46e1784047,0x84ff07c0938a62fc1f0,0x45a4f2a1360c1905025f,0x661463422f0913f07c0,0x88504ef0bc1f024f44c7],#[0x13431c2e0fc1f024f08c,0xc147181af0bc0f044f26,0x37c1343c2f001a1c2584,0x70bc1343c00581a1b452,0xa02f45f07c2f00d00687,0xc244cd0d17c1f0216064,0xcd0f07c08581a201f06c,0x37c1f014f858906cc209,0xf0114858845d1484fc2a,0x1f00221c1ff0a1371fc1,0xc0f0613284f2374571fc,0xc70951745283b194ff0b,0x2c9451c7f07c2f024e84,0x904e04f45b1bc2f07c06,0xb0825e0d4ff07c008ca0,0x162fc08581a191714a0c,0xc7b1bc2f07c08508d17c,0x945f0bc1f00241d1307d,0x17c1f0a8bf0019241af1,0xf07c0064221e13139c6d,0x1e0fc04582620c830ac7,0xc2f024e068609c23f0bc,0x913f07c2f00cf29c7f07,0x113b3c806b1502615d1,0xf03462452b1515f07c2f,0x181ec5513148cff0bc1,0xc5c58804fc7f07c04582,0xb16150b8241371fc1f02,0x7c2f028927c133fc006,0xf001a1c52c542071f46f,0x9381a234662ec5f07c2,0xc006878270462fc1f0bc],#[0xbc0068771e0dd17c1f0b,0x4f24c9071c7d17c1f0,0x13c606bc642e09f0bc1f,0x53c932384827c2f07c0,0xc124ca08109b1bc2f07c,0x240801e062c653fc2f03,0xf83f1b847064ff0bc024,0x1fc6f0bc0f041e151d46,0xa1bc6e104fc2fc2f03c1,0xc00649f1fc1f0bc00701,0xc971f4507b83b1bc1f0b,0x38426746427c2f07c0a2,0x1a13427c1f0bc0a2c908,0xc2784f0bc093c9e101ad,0x2f07c0b1cb26313f19c1,0x60838306913f1984d17c,0x201c1fb17c171fc0088,0x58261a8971f46f0bc1f0,0xf020f458870819f0fc00,0x8530e1c14f088ef07c3,0xc2f0fc01c9883fc2f0fc,0xfc3f03162746d1fc1613,0x19620988530e52bc2a3,0x658849d2332bc2097c3f,0x12747e17c2046c1f0fc0,0x209517452c6f0bc3f03c,0xc42ec2b1945068221c1,0x1174520cb09c1a354f1e,0x95174521353dc193b832,0x526158318bb081a93860,0x60890c709c107c1a3434,0xec5c581a14247181a0c2],#[0x16097041a33f16141331,0x913e4e1b1604cc571c20,0x4466099385827047051,0x58d6320991dc2084771f,0x858c827047084ed1c746,0x61c1313dc6c134782460,0xc12052a368cb094153ec,0x850985293d8c709c071b,0x81a08860785293fc171,0xa32c2424501a8da3145b,0xc31ec206ac6138714a8d,0x52a32c27054f938608a8,0x4521428c42584b0a4e1c,0xb181a1021c2784071c71,0x71414f82684704582545,0xc40902007b0971c1ab18,0x1383f06c71709e10c193,0x4538608109f044f10206,0xc1e10cf18526330970b8,0xc96f0bc1098609020a25,0x2708]]
def g255H9 := limbs80 #[#[0x140869fa571a3e78184,0x4848c0a3d7e4000021f0,0xb6ad5411680ce000b70c,0x2900000001610928001c,0xa8800161d0ee144c6a07,0x550c4133449ab34b193d,0x22bbc038938f00fd9,0x40800382348a89c00000,0xdc0004db4b9a488f7558,0x45403c42757388e2ca4,0x42da8c91512725cc0c63,0x30002c511767180590cd,0x117a43920841c00016bc,0x16fe650e5d100360fba9,0xdca4066cc34280028be,0xa6ef6f514811908210c7,0x415904d400954d58d08a,0x8553905fa51a70e17078,0x3d5d49ac1bd510638,0x52d8a3cc800006e92116,0x758e284dd4ea2a183047,0x7ce8003c430adc7c737c,0xd1d137d0b65bec417f40,0x1d67]]
set_option maxRecDepth 16000 in
def g255D10 := limbs80 #[#[0xe3aeaaa287f1d6555143,0xcecb2a8a1fc7e155450f,0x3b2eaa28779f9655143b,0xeb2ac8a1de7e5d5450ef,0xaeaba2a9e9f8659143f4,0xbb2a8a1cfde4587553a7,0xcaa287f9d8655143fce,0x3aa8a1fe76595450ff3f,0xeaa287f9f8755143fcec,0xac8a1fe75d56450ff3b2,0xb2a87f9f8559143fcec2,0xcaa1fb75d96550febb0a,0x2a877dd9759543f6ec32,0xaa1fd76157550efbb30b,0xa877df9661543beecc2e,0xa1ef7e1d8550f7bb0ec2,0x877dd96e1543befcbb0a,0x1df7e558650efbb2fc2a,0x9f3d655d154beecaf0ca,0x5df65d65553cfaecb2aa,0x3fd985d954d7ec32ecaa,0xff65f865527ff2ec32a9,0xf79161d54bfbc8b0eaa4,0xf65b875527ff2cc3aa9b,0xd9759564df6baf04b24f,0x61d6550e7ff28c3acb6f,0x865d543feec32eaa1ff7,0x598550ffbb0cc2a87fdf,0x761543fefcb30aa1ff76,0xd8550ffbb2ec2a87fdd8,0x59554fdec32e8aa7f7e5,0x76553efb0cbaaa9f7d87],#[0x1954bfecc2ecaa7bf619,0x37fb2cc3aa9bfd876,0x61ef0cc05281d409c027,0x88ea06b430c15f09c045,0x58e2a013ec95a45620,0xc19d1ce166cf34098f0c,0x29c90045921d903e7c83,0x58cab2d4faa414f9a695,0x99ecca8628afe9758b67,0xd7533985c26dbc6b734c,0xb213d0477f83e89e84ef,0xf695449464071ac8a643,0x3c2e01388a06ce926892,0x1707804f20261a0a71f8,0x83c2e004c809e0c29c6e,0x2770780162b8e1ae3053,0xb801420461401f0b8e1a,0xe093c90d0378ec6e0f0,0x2830982e14c1f1b85c,0xc1e01382c3f1917c1e17,0x5783c2e004c80d04f8f,0xdc2e1f03820f238fc529,0x3e1709c2e1f0080b8538,0x35c1a2f0b80d02023c6a,0xe388b83c0a2858b09850,0xb8013270e198a04d1bc2,0x7c1f0780232629c7e0f0,0xb83c0459014610682dc,0xc1e004c9e3c5027c6a2f,0xf1b07c2e00988e306b85,0x746e0f0b80cf302e1460,0x45868a84ca4c5820570],#[0x83c08b068709f1d13c1e,0x2770785c00d10c709b17,0xf824ee170034341013c7,0x343037824ee170034331,0xe045834381383c2e013c,0x385c1e013c92390a8bc1,0x2e07049e48692609e361,0xb801a1927830cf1b09c,0x8be17078109208fc184f,0x70b83c00993c809e138c,0xcc7e1707810926121ae3,0xcd1783c01110200ce138,0x8bc1e170026403490420,0xe3b1783c0110dc60d22e,0x38e89a370785c009900d,0x70a51f83c2e1f011c408,0x53080ee0f0b81c328101,0x882f0785c3e01403238,0x22708120770781c3e114,0x208a3e1385c1e070c4e1,0x96168d84e0f0b87c0639,0x2585c270785c0e1d1880,0x251b8d47e170f801b18,0x70f84122003c6e170f8,0x87c0e12389c2b1b09c1e,0xc270f8040202584a3f07,0xf8412278ec7846198bc1,0x1e170386c4278384e070,0xb814e0d0e12c2d1f0dc,0x8de0f012d4f2a088be0f,0xf029e93228a22e106526,0x3c00d0889a2a0d8dc2e0],#[0x258344a3518c2a3c278,0x802020444e6171e13c1e,0x9c24a84f1d8dc10d70b,0xca120838c1a45f0b83c0,0x6a2709e361385c0e093,0x5c684f0b83c063880910,0x105a8fc1e1f004646103,0x1fc2e1f0382148713176,0x770787c08788c80c894,0xb83c3e0058a0192118c2,0x50c94383c3e0458a6103,0x3f87c0e088cb1386c858,0x961312970943a194212a,0x8789c47c2e0f0f80]]
def g255H10 := limbs80 #[#[0x36c303c0082c6000219,0x8fc00370800000299444,0x3d6000001c180000c66,0x4ac62d51b40030467b80,0x337043400101,0xac0000000faa230,0x2544d6b0ec0000,0x197c00000000000,0x2ca98e4000000000000,0x4001431f5d2880000000,0x113,0x1000333c000002d00000,0x12e906a2fb4,0x247800000000,0xa761c0034a00002b8000,0xc0000000000012f70b66,0x28c4000003d3,0x48ad0000000000000000,0x1094000000002d,0x21400050800000000000,0x51ccc000001678000000,0x10e80000000008004,0x1b000000000,0xc000295c000000000000,0x1c4c5900029aadbd0,0x419d0400000071800000,0x980003430861251384e1,0x2587a00001c5804a4395,0x11800000085c0024f4c2,0x318a9cc000001994000,0x2c8cc0800257000312c0,0xdd],#[0xdb9c4000000001110d6c,0x38754f0000c9c0031,0x940000000000000002cb,0xb8000000003b24003004,0x4000000000000003695c,0x3e08000c55f6d96,0x0,0x2d2000000120f51c0,0x8dd5c0425a90000d5800,0x90002ca400317a0d4000,0x319c0000000010,0x386c00000000000,0x34d8000000,0xc00194c0012c80000000,0x83,0x0,0x7d0ac8880000000000,0x9b800000000000000000,0x2f88000000000003,0x3c2a5753280,0x5500018d,0x35d7da4001c0c000a50,0x8003c6247048327e42c0,0xbc0025a2530000000d2,0x19af898000,0x250c002cfb18c0000000,0x4c8000516eb315400000,0xc40002dc8002]]
def g255D11 := limbs80 #[#[0xe0964f9d6450fe755143,0x50ff75d543fdd6550efb,0xfdd8650ff7e1543fdd85,0x59554fbd74553f7e1943,0x552ff61954f7d75553df,0xbff87552ff61d54bff86,0x61d65efd76597bf59564,0x553ff61954ffd76552ff,0x8409c003ff5d564ffd87,0x52c940fd1ac2cc460650,0xd2622d40478cdc1952e4,0x5804e34bcd662a950499,0xb0c0829078f8c8b838,0xd83098780401e3e2e0e,0xe3c260e16027138f8a11,0x78d098583809e48d09c1,0x3e34260e1600490268b0,0x78f8c8b83858026489e,0xe10689e3e2e0e00b1434,0x78f8a8d838580264110c,0xb8a6323e161e060c2920,0x918e2909838785801c40,0x2c50a6342616061e087,0xa0e462825841d8f83878,0x81864c503a360e1e1600,0x600a0e2e29081f8d8385,0x387801c2c36323e1e0e1,0x1c4e0e161e008070d058,0xa81020321f8983858780,0x7804648a42c260e16061,0x1e01312281c858e2d838,0x87849e58b8a2087e3616],#[0x12a248a2b0d098381]]
def g255H11 := limbs80 #[#[0x40af180010aca038020,0x4bc001224ac47,0xcb4000000a400030ac00,0x76318ee480003c00001,0x101146a2,0x1c940000034a800,0x480000000008b000088c,0x4e246640acf40024c8c,0x8d0001288e8c00124e65,0xa0000000000a91a99034,0x20600028166efc,0x102e85706c001071c9,0x7a41a6680004c000140c,0x502b49fc318d94f2877c,0x201c0034cd69447fad,0x821c24000000,0xa1e40484404c0000000,0x20c00000000000327800,0x580014b9a9fec84dc002,0xc0c68a743a4e4001cfdc,0x85fe3c003265c88851e2,0x5dc9b8e8000000001084,0x40028d4636d0143e8432,0x14fb10]]
def g255D12 := limbs80 #[#[0x5ffacbff593feaa7dd43,0xc280478dd419f007fd7,0x4241870a0120e3c68a12,0xa3c5830e0161ca478c1,0x3803c88f120c3850070e,0x2c6890a0c]]
def g255H12 := limbs80 #[#[0x5ec000000000000d0120,0x370000000000095b8f65,0x5ab00363000000000000,0x15050410000015310,0x400c1800000030000000,0xce85b0800c800014,0x25f98ce0000001c0000,0x10042400000000000000,0x14b62000000008371200,0x128000038c0000000]]
def g255D13 (j : Nat) := if j=0 then 0x71851010c2008ff else 0
def g255H13 := limbs80 #[#[0x39a2001b0000,0xe10000,0x0,0x240000000050,0x7300]]
def g255L : Nat → Packing
  | 7 => (20,6,6,0,0,8,0,g255D7)
  | 8 => (97,5,6,0,0,13,0,g255D8)
  | 9 => (119,4,6,0,0,14,0,g255D9)
  | 10 => (66,3,6,0,0,13,0,g255D10)
  | 11 => (23,2,6,0,0,11,0,g255D11)
  | 12 => (5,1,6,0,0,8,0,g255D12)
  | 13 => (1,0,6,0,0,0,0,g255D13)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 6 41 4 10 5 1 g255H8
  | 9 => lookupWord 30 137 7 12 7 1 g255H9
  | 10 => lookupWord 38 389 3 12 7 1 g255H10
  | 11 => lookupWord 22 149 5 12 7 1 g255H11
  | 12 => lookupWord 7 79 4 10 5 1 g255H12
  | 13 => lookupWord 1 59 0 8 3 1 g255H13
  | _ => fun _ => none
def g255 : Forest := ⟨255,13,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P7_0 : block g255 7 0 20=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B7 : block g255 7 0 20=true := g255P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_0 : block g255 8 0 19=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_19 : block g255 8 19 78=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B8 : block g255 8 0 97=true := (@block_merge g255 8 0 19 78 g255P8_0 g255P8_19)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_0 : block g255 9 0 28=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_28 : block g255 9 28 59=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_87 : block g255 9 87 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B9 : block g255 9 0 119=true := (@block_merge g255 9 0 28 91 g255P9_0 (@block_merge g255 9 28 59 32 g255P9_28 g255P9_87))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_0 : block g255 10 0 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_11 : block g255 10 11 39=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_50 : block g255 10 50 16=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B10 : block g255 10 0 66=true := (@block_merge g255 10 0 11 55 g255P10_0 (@block_merge g255 10 11 39 16 g255P10_11 g255P10_50))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_0 : block g255 11 0 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_3 : block g255 11 3 16=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_19 : block g255 11 19 4=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B11 : block g255 11 0 23=true := (@block_merge g255 11 0 3 20 g255P11_0 (@block_merge g255 11 3 16 4 g255P11_3 g255P11_19))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_0 : block g255 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_1 : block g255 12 1 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B12 : block g255 12 0 5=true := (@block_merge g255 12 0 1 4 g255P12_0 g255P12_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P13_0 : block g255 13 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B13 : block g255 13 0 1=true := g255P13_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255T : checkedTables g255 13 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g255 0 0 0 = true)
  · exact (rfl : block g255 1 0 0 = true)
  · exact (rfl : block g255 2 0 0 = true)
  · exact (rfl : block g255 3 0 0 = true)
  · exact (rfl : block g255 4 0 0 = true)
  · exact (rfl : block g255 5 0 0 = true)
  · exact (rfl : block g255 6 0 0 = true)
  · exact g255B7
  · exact g255B8
  · exact g255B9
  · exact g255B10
  · exact g255B11
  · exact g255B12
  · exact g255B13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255G : graphValid g255 (boundsBefore K254) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 13 sevenInputs.toFinset := by
  rw [show graph = targetOf g255 by decide +kernel]
  exact root_index (g:=g255) (top:=13) (i:=0) (before_sound K254 V254) g255G g255T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_51982

open PEqualNP.Outside.L_meta_51982 in
theorem PEqualNP.Outside.L_meta_51982 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort g255R gates o fit correct
